-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0161
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:11:52.186745+00:00
-- url     : https://prove2.me/submissions/12165012-ae1d-433e-af50-c3e3fe67e0d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 28776984 ≤ n < 28956840 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 28778234 1250 28776984 28776997
    0x41a1c150603151e200409050402010801090b010801090c1e030e070f0b0405040c120e060f01060507020306011404090510020702040c050705030301031101030e010507180510090509040302030f 84
    0x2a5903859004004100c0c0f034080600c004400004100140c840140c10f800d031070107906a1000c090b9541c1d0480362400f00b01c034142802d200c502d50300e0098a940d201c58a85c0003c11081d01e0036030100d480d540c00010b103004640242040c030306e07060303452408507440c2c017116001800d5041e140106100341c0250741c01c0300a5a841c100d515140050f40c000c10b442071000642403c24640f03402540c51545440824400c50526400b210215441034030002024510540100e030301c1e2405413003081301c0604001e0381c00000300d40002c000e40600d0410a1089031070b60382d080d05403500c0c4103140000350180c0004e0010004a41040022100000e02400c00b0403a24590f44d105402d103035840c031002821039804198542541072034494580c0100080c10603e18004458541c1552070105100061006441e8540100b041c6d100b80c010480290b00c0d02c000344a5424681009030480789860b900b04009400f81ca8000f4007032500c0c014030980342d04a0303100c240c4140c3c10315081c0061084003c1003035055200803c4552003070208040203045 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 28779484 1250 28778234 28778273
    0x1d03180f1c03090914150109030507030b160504030f0f030e03030c07080d0f09030b190609020a080901020a0f0e0d0503040303050a0201050c04030b0a1e060902090f041a1c 75
    0x261107546009444072010350841a081803800004003c0007500c1c584c0b00781c0004414a44c1126550f0740401240c00300c81580004220340641c800000401c00284110b600440e052035207102c103020152070446040c007482c413024003456503d0000201140e41d5120155107a030003450442003c490302d4000c680b441d40015160902c0d030b8010f650411801c181801074080701511442c1640d8035101040d4000d086002900010b00101018008104110860181100781c0101e060003445290b0746c03070b0840d00007134000c105a40c0100d1109070000b03a01080c103100311000190a41c8401c0c0c0b14084041048035030815000b00b003a00214000172400100c3c1d02003001d00011442035503420b56506145100a00b90783d0054482104540c040c0024000030707060034841e690281811000107450703400c140036080c82603e03900e03070000c4c420b2802d103020401001a40040c40d1001e000d07280300071420240c0301400105c2d038011100c1c04030400c0007805a0171900d80b002d00007180d0310141510300b45000d6503445440442549055641 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 28780734 1250 28779484 28779529
    0xd0803070c050f0606010e0108071206060e010219170a03060902030a02070c0e06010c080d0b0a0f15050405090612100e07030b0105060c10051305010603080901031d03180f 75
    0x400300b207000c0225450801c10740c00901142c0c01d01c100040d0500d41440c2c211814420003800203510907105100000c000c4682e01800e10405945210103846d5940442865006019501d46507100c0c0d06540b880380301d90740c6e21844030201c42c15140c03440e01150b0800e80701c080402d074445000151280c15400510301a640384400180d0380d401c00d182690210520b60b014204045110b0200402a1303000700c11131040f10303080043d05940c0c2c04210807039030050441d48182580400c5144003c108510940c80c0f0505035041d54100c440d203c0480c07001521a03010310b20660fa44271040c400002c1d03050038018400250500c1d00d4048032051720a04184100b038035406820800160700004040040c002c0990300540100020755601d441d1440000e81a074850f4581450405003a444001003031103660700070900246560000300801c10355072a4a00444036520a850590001c0e0520314450384080c55404545014001540110324180702c2c07944603642c00005240c010340c800c88100a681007038a4555010740040350141544 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 28781984 1250 28780734 28780757
    0xb030705091e090a0812040c030210110105010b0403080405120102120c0304030206070e01050a03090c15230a020a0b04020f0d080d1401120206030907031a0907080102030f150d080307 80
    0x202c90903401003007104254412100500418107250498100c80703038400c030304003040c1d03600e09010350329540c0e030707403000703400c40030391640001001d07800b0301230b1070760010240001d1110f42d07030310304100c541801240006021107404100811440c5003851560182171312501c0054101401d9a641e4141c000c0115200403090b08000100410168180001a8003040a040030045000710400007000760050145003c1856034a0351100c0c00d1000e000c80f244003e00070106034110241d03d00000411400034210443c282c141d14400d02c948100c42038059a071900c449600510090303001e51107102180c100500141c0e04241c0d4445c0d411416125a944000124043d0380001d9884050506540c216200b900c8400540d00c150750040c00022032450301e91400e0307034040700c00030f03280d8031800001400c200c2a980000c1100c0300d100c120040c0f0340313603c403051032081d2881002d9a01290f0350b04103080c20303031204491030002c2401c0400090220148176601c0884680080e102e0b0034007480a0791340d13008130362050391020003045842140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 28783234 1250 28781984 28782031
    0x60d06092901091d09010b100201060603060b030609070f0e030a030801050108060103090206040b1c050702010e070e090d0309030203090406030c05040e0c0906210d08010303200a060b03070509 84
    0x40034042031804503407036450001404840e5030618644c501c4082c2102c0418280002500b286003402c1000704800e000303617030326003020707000300890300c00e0b00302080c24250009050403800c401d0700d00c10000035000941c603680e24a401c4520701401c25403802072080d901125885518100081a80b140c425180c03104154140700024103000c02c0100003c2c1058240325030100161a80c4e03003034804803949500096102c49500b001001c1c810403280001e201c3d50310b02401c00c080d039581500400c40d550411002e4680e41034441c403001514a00460391035003a941714000200701944241c0c4240c007852301910503a42090404000902510f0301540b0a89023103000701ca060003146424440c220040c00ca0f0300040009844410100d001684020121842010000c203802e1500e03040d03a08416040c407220059810b4141c0003800600248804c1c0015800141b0702d507584d050460f140f10070f11050342c400074000c0c03260a903180c0d2805c020740403900e00760f80c250186080c00280d98460f03031040350040501d54014168408136200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 28784484 1250 28783234 28783301
    0xf030501021e0a140d06030219050a080609030a1404080a030809010c03020705060a0c03060305071206050609010e15040f15080d020c01051204020406050909010207120306080309060d0609 82
    0x2a074100c0303100304540f00c1d100c3d412200800400d9000c10300d46445940481ca0140200016031010350401346d031400040c0d04002c152002c0c02a12030403034a100d152360f180c03010941d44440407a4030034640e500810060064074050400700601c040c00103c00d6103010f440700c149a0501d280e6200480100703011000b4030841d241c0c20f015a80c10151b00749421428120152038540d03680c0b10140c40810708036962850710a41030300c6504010007550704641102c0480f0398420f00c85c3c0004040010940c0c82c18908004100e840c075041a180d8100c0340c030002d001d070090b280c01c566804180c2030007512550056031090340d04200c03042e6000340c401410b980400301c0182840c0c1311810b820111080440b03804c40d005442c02010980e0060280c1e00d022046400d01801640c80307101140007004c4075007100703600c21911804c001850005400600c0c03c1c62181c8a2507120310310a40c03044d000e03901c080c05450701c2c60704144001601401e288000d800442880b5002040c1c09548281400c110340f01c42c410720f184240c1100b034807004500c1003030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 28785734 1250 28784484 28784527
    0x1090501050310031b0f060f02060a0203060f0618040e0d0813050607120e0102042c04051e03040e0903040807060504120201050c010e120309010e0a111002070f03050102 74
    0x2407282c55480c0026100c0405141030000900041407500c8403000014000f08040162640e440708609181c0c450002070b061561003000080140700c2d00300000e690101c0d500aa9000d280090529488c4100d8102005296042a40c01500c0144441017200040d43d45000c0c2e11710101c03160028100c00c03100f50718000d000361001007003014500d01d07501c114000210001b4080d41d01c020710745401101d0003002800d00b006445140c10314a1250700204001c1040c10000000311908032000e029440a20b00070100c2105044085501500a400140b0210781d0004010101d0307a18415180540b490b19441c0c40d85100b5044090320348c5449135001190510107000704020342c601800903800c00c40d060030301e041900003164030300c1c06000f81000404140d6124003a4250000c14540c0d1043e410390f83d004208032803210087c1c00c00c9456507115824465800303513104e400300702e000c030b0341c0c1d0866101c040390800e030404d2003441040850080f04500c2100c0002031502804480080550f104000160f50313074410702400ca050038003c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 28786984 1250 28785734 28785737
    0x170403210506030d0302160609030c050601030c050f040b01080a050705070c030b04020922030c03140313031b0c090921020c04051501021e030912010902190609090e0102070609080901090501 83
    0x4101000c40700ba01ea612046100d41d0005000c0364400d0279180848000f00c0c0c0c224005c1c0248180e0b030010007000056401c40381581c10075104142c42103000d00420050312054440c0074045440c1c403010589a020542140343c0c004205c0c203015150215642c0c60900d00501a0700a641d20409070062004516080c280c1d40e400c01c400c28510304a0f607480c00002450750503180700c01018000c80214000406000f90050044030440010240d201e180602120070000c03107150003100042d400d1004a01e00c020000145590260000d40d00ca510300c3c104140343c1c004025141d0300b5100d810001000300305492048500c00c16003011075010341441915081840140c07035010380040501000150901400d982c0001c400e98615058010540c01401d00710546045102c0c1e0100941c01078411440d00421420541010300e481e4402d54010580c403101940d0301e1404c0c8858060a00090b414060801031810301da0001c55010b2203000005141080e669140c80c00c8980000003100c81c09404030b45101ca940c0c000c0e5500d00201020b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 28788234 1250 28786984 28786987
    0x3130902040503120c0a0212010b010e060f090603061302030103050d030b060f0a03050a0608061612050c0901051305040203040b060f150d020a09170304030c080a03170403210506030d0302 82
    0x41c000000d0311361510b40202c040707805000c10320b100000810440c80039040e401416203503403800341034a550b000c0d11a05101d5408140010048121814102c007164034118401700054184a010800c0000320351001e4051070303002e0140c1c1c08281c10f4024a1005500940c40b0780001d04160b25001e0005d01078504141d40144100c100340030707035142c0364a510120381e284101c9140010b9a80d80710100700c001000030360041c01c02d034800c0c10100710455503a58a1600000c519441e401b541e80c0c5524407940580b4030407145011085820b01808080754043c1020707000b07000200e181c2091141e11364021901300d03001101e041c0c0309900c1d40c500780425402c1078034214810407020355224070f0100818400c803000e40700e0540c4000003190b001815044491150001c0e07405040131a000c441800903040815549400c140425500900c0030000081e44000c0058598401d9a00d515000c54040c1c4202944c40900d500a00960038000e90310841040e01503101d0f40703404a030790351040000715410a40103040c981841401c3c1502850310 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 28789484 1250 28788234 28788239
    0x60a090308010603020702120709020d18050a12020f0f0705011205040201020d050c0109022106100806040201140c16080708070303120b01050906030a02120f040b04030f020c030a050313090204 84
    0x51003510a0b06403201ca080240c2e48503024404201c01c5411742c8062080350043c02c0000c6031b0410326400030300d0f10b02080c200138170129019000c101c4550680c050004c040354400141031f4000303144041804895115401901e810006c000030b07003810691035003040c000036044002c0c240503075178120031466485c40101d101000b2600c0d0617400130f580c80680b00c0c800d40a0000208002c2c0c0e117802e003508040251135029080d0b481b02024080c04104281030840454482e02841e000101619511080d001c100c4034000d0080140c2c1e1640d800540752141400f400210303403101040903541104081101d08004051001c4900010b45000501811b015031500316a68941200e8810004680e0024000c01c0c413810010002691007640d00040e40c9522494080340e80100b0b001c401c2010345101940a0724106441c5282c40c0401d43d213105038030820030741c1190002c000c1c55041c1c0209020912402c0101c2034000075004032000680c410000034688550504102c810b1307440014403481072403544110500804501d0f02c203506050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 28790734 1250 28789484 28789487
    0x115090609030b24060c0610080102160f060b04050415052203030b040b0901030b090d0507020d0303050a06050303041214010e0705010507030315090504050f060f1501050904020d020c060a0903 84
    0x114050b00c40c0310303040c0c22940030b0007204581048a4500340d0004205c1551150f0401925444050885020100034102d401c0065501418000c580940300e0480d400c0d4548842d990700c0c43c4514018180944002d0381d200c2c5451001d03101c074031816010f980540f0001d401d80121020b00016a10028080c4441580d41582e0222400b0115821119292315007800305641c0f14420104001b44039080c0d2643d07101040100000034024400c1e10540525030b1070382a42e2904952400503500e030304c039222000350001c1016281c0c0b004a80b02380d0019801110050011803d65601d0340000c3c40c582294000c4880001d54500c4d54041150407a04008502c0300c08009002041e01d2140107034440d007480c4101342c144403000584c079080620a0780701c1e04169010b980c075100f001c0c0d1200288001490120340031200762007015414a440302001035620710841881502040f95500d02da4031041a000640c0400c2c1480000d11404005030b0340c50003c1c14042d9580d81d00181c840e0461300d05c0c0c03454a030000c0c2040c51401d00e0200402c000c20b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 28791984 1250 28790734 28790753
    0xb1201080c0a03030e0f010203070602131511120705010906050106030c020c01082517040507090b01050909010b0a090803030c030901050c0a021b010504050310060e060105040e060d0203030f03011509060903 90
    0x45c64201c030100d1035048800e00503803c500c40e00400811031480010385c4070340b80120041d10020f1720a610100d0b600e240100741d00783c0c0e030800c804482e13a01981c8500005c00b00c000080340104105032281002282d10802030b5030710720560b4006e1300568003281c1c4510352001d40c56410849a031281300709182400007407c00400100714003100c0c1485c071402400144010408034065a21250140300000d8203480a140078103100f52a5115802065661820401260203640c452800d4803812840141400002d902e07000070041c1ea54000c191500500050b45800100250144041c40c42140e101200c56070f249807080d40d01d0f00312440100242103014052004002c030550009020241d650f844c1d00501d00c03034110b6001a20940296404198103106a080e03d050103012508948201e44c041480103000d519400010354460045000c0e4500a4400d10001742c551315103912403203180b80c006401c0e0707450500810646000ca6109810040b60416038040c0c078140158800b11100040619150008640b41185e1312000780 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 28793234 1250 28791984 28792007
    0x603060509030a0801030f1110080103030909020a080a0c03110d02070506010806010b07081602090a140601030b0303120c07170304030f0c0b040b07090816050a0f0b0901180b1201080c0a0303 83
    0x2e1640d011a440308104445620f81d01c1510700409c45402503101c034400420b0321900740002c81c000749441d0340006a06130301d40251101890241c8904940e07035607a1012000500350102408101a00d2710000700c43c005420000b442801c0110402581c0c0f1000d5003003080c40d110040c0e01948484d800a0010040c00740f0315001c1d103082c0d6504c02c215913030f82c80d00000c0c0d0440c034506000700a584144000140001070701554442040345200d8403590210713036512001541101e684c28803041e0075410030010010360740d80b00900036601400884040342082050b4580390108002407907a260015000000d001c01d150700014016200070395880e00d041004410394602320300c844082c000034190301c0100c011640b130501030300c4450045c20519044420b8100f81c2110102e414078584a51f60042c0083c480218022001200724400c0c0c45047c14100d180001e55001118a00c00b200d0140c0303000a404c110100c1d11080d04002020141984400d01c1019410124060b0030f000c2c44003812032003081c030740008100094000240001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 28794484 1250 28793234 28793243
    0x3090501050c01020d11071101081006031508031306020601090b060403140102090409060f0b060906041a07120e0406270e1002030406051b0403050304050904021302030a0603060509030a080103 84
    0x1100c200203216240603000f000310019405c1e0504250700c000680d10800341052070701401c200c065003121103005682c0588140d440780b10403402c800090214078001d4200e402440d46144280202582d5551024216085200c441c9904585150104442503041107203034003400384904100822022500000e1440c440c5103c02444841c0c81c400e003103540a001c2d81504c1210030040c00a1002c20f40501d094802000c41071045500e86142c201100498100501512015a805400c030303032410b81400c2d18161010200080f00d41e07505070400107000011000c403190b2002c551543c40d4040d07000459020402502c249400607100e4010006035000a0040803407442156070b03e000340005d4082c9203d0415082c0100605a060560700000621040001907800248a544c0384016408081d92855403000d41d0301c074031321000c0c209520900051010780f038000c0c04140c1141c401450031034640d000a4140042c1d030402c40d0741c00001750741c400081040c00914000c03194401032000156180465496001e024040180400f50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 28795734 1250 28794484 28794487
    0x203040302011805030a03030608120a020303040b131202030a0f0302090609100212040b0d0605030105040201080412051303030f021b0a0905040c0305120715020405101107030813090605030a0309050105 88
    0x501403560b03d0f0301001819003e016504000d01c2400d018000d010681b145000c0c911412003ca101001c0d04410b0302d07401c1c0180d030301561a588468640b6182d003040134049400c01400000107500250b456052900607042a8024540341c801480c0301038030303103440035001c4403e0500403c6005165a03c030011102103081c201c030750800e50004040f040b4540054281c0359a64520000f4010035081c050710050000040e144000744600c1341c80d80f0a05003602c1060354020b0225074804041400501d43d134029a460001c14a080e07420240030300c480c0384007071005a00641c041207003070000420705036040c80302414480280d0b030034200c0b481c5100b0210340c00b00014803c0c2e0301050340d80c40c040390410425080910085800c04226080c52001c01c4030b8141f45d5000c800f084070000c1c40040c0c8081a00d10a00a071002c8603802064120b0f410745448040d42d9840a0860342401800380401c0800050915809004d06d14800c1501090450802c001d43e0101c032015001070744030343d1050380084002680b103400b8000b615005e00c0e099 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 28796984 1250 28795734 28795757
    0xb04090f060f06050310020405030105090c0f10020109021008060306090a0206030c0a0216031a07170708040201050d0c030501080c030105190b0319050c1507020f040203100e04050304060816020304030201 89
    0x200b00600050b080968103000c0c01c410001021140c3d0050020b5a408600070000d41d02c42c0c2c040140d44161002d04943c1103502c0c3c1c0e1000c00140380c99210145042028000481c140000d5800a0540da2030810365034081454142488010305041040d1580400c00b1030003441200c0d020740008244e030100601d4411860400074048010710301c28455000d4080001d0b00700b844668076480d00c10491001001241d0100300300c0d8000071003c1d442002460611010019088400c2e280c85038101d40000b0300910603818860708120300c24030080c0520440c80c1c04030711580d00154550504204c0d600304402c920038035200345c0c10541030003002e00c03e0442e003415000d4103603000135503000740341c0100f81095560710813095260b483c01c501005210b40826196100c20301183c003240413140d003000e20b43e170b14044c940e0003940200d800c15458910307040603802160007001c0501201c254541c0d90090cca2491002c680454107a000410104115600603505c0c40d00451001c558a80040d41030000035624001da1001904016400010303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 28798234 1250 28796984 28797011
    0x20a0806041a0306010801020d14041101030903090509160e04020903100b03071206020d05010609030f020d0201030e03040305030c0c0a1208030402150c1e031317010e030301180b04090f06 82
    0x2e003103544801070155035440d81d503021918000c1d004401d100d0403082c2400e1002c80c1c40703444407220610849c0d020250381d404401305401100148000c000c11000d10001e2107000c1000c0d80c504401502c075201d0300b83c4801009201d0f850040840150710140d86c01180180100009658041043d210141a00c0800680750780e504c00040c1c58600c041d400724005118198400c0306104468009003c014a201d00600a990303880e01e040b1001440d61001904206102c0242d40040c0340c0030844211190052501284441c81521040e041d94040e620032950782d0310004021000080c1803001e0320f24928221030008845203040784507208145045002082c01c03500200040455a0382c091140c0c81c4068419420b0300c940294985079600e54440030300e000703912403c1c1c00062142900008035100c5002c0c1c2d9203101100382c80c0c50b03005040c107080c3c1e003481c14407552194418091540200003440c024004001c0c00300c004030075000060f0441d02150750317441c099428001a10301040701e0743c2070340500f603601c2070002070b42d92070400c070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 28799484 1250 28798234 28798271
    0x507020f15030709060801050f0d0b130c06090e010e0103020a0302060309100c0f1e1b02030a020306040b041505070512040206130303020c1314070c0305040b13090b04020a080604 78
    0x407140c81c19000801800290399001050000341c44407502d0f8240166210800c0100c107000d9400c849a200308003030601d0000580c1143c480c2c0c6c100200014104000d000c56485504080c0c881c2c01081c0020b000050402c21900080a070301d005000d882440355080d4119004078460186034000640141c1001020400841007080035061007051200304015034204070800400340301e525903041c800591000c50031040c80e00010030b108449520354803034007142c0340000324003007486502c1a8148da240c00b078480c02c540540c170203011551059205506160203460245014020486141490101b0710f203800d041120300c5802c6030449004c400e01c2d4a01039803607600c0340300184040c450303840f01e51100088030100004040c1c00181d0b0f203c040740100c40c050713410b240704503c880407a0340c1030803106040151a004264203a0092144a40c410300914240346000c0d12080304003d00d43c083c8000c5008005028001c20000101e84240c900401084400b0b51401614501c02801c040700a40040d110b82c0d43d88202c01001042080d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 28800734 1250 28799484 28799509
    0x20c031204020a0e0109020d06060e1e060f070809030118050d080c07050a0501090b060d021f031b020706020c04020313060519060602030c06070e090c030a0f0612120f0507020f 77
    0x4000362207561b1242c401c5070107900042030902c03a07141482004500940280b504203102400075014200c0d08980c00b60320440c07010780094554004204110305240c0c280743c00010180f15000340710107a034408440040c1421141600c0302d10224000b5040044001440405c81e601c0c400400e03e010350041d101c886100d80b242c850300078018010f20814110008004040d000440c1040c0281e45899840d6907030803c0c00041c1c0b07481c6030025031101000074201d9a001243c400141402410311700005c21300ac110209001e00c80c0840221000341e84241780401081e0b60403c041ca030b0070b0740c06540a604600701781039449070b00801440000d0003192180c000840c1070740c80003080c00b105e0404880910001d40d840201035101e5028000403544d078001c400000302a00c1c002c1800844004001e00101d503159038070072202501c3d80024158410035501c0b0791040c400d54000b40200700c090304186000c2904d881a13858a80c201c03540310803c8000b4021400c03a441c0d50703c3d8001068441301a0140d40a5030307001101c4000820825208 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 28801984 1250 28800734 28800749
    0x703082e03050615010915050304050f25080106030c0b07051c030911030102030705042705100620030322050d051b01020301050310020a170103050f010b04020c031204020a 75
    0x140c000280b11001640500030700455019450140100300111403050b12400f5100940d05480b1024440e5407181c3d00441e03110b4003410980701c02010542c260360a00e0082600805c4c00740c1120f014140342c2211401c401e005041c884002c003d858510350794550003c050b84605201000c01040c03860a00800b0322152051083c031126043d40c0e0005000c001e0014240d42c001591044660074003000241170501c00ca078018840c40e25045e0602c2d180c80c81900e1740d4258a11401000c20000345c0d880c80480340c60180501079030600d41c50301010f5003012340c01403020100c2c001d41c0001424000603202d248102108076500098424160300c540c0d8010010740c04114a4244002e10a21031003076100d40050740b00c00580f0106502402d0080c11034413014180b402c5c0e00085c0101581500900490384090100c0d0307004003040c540c1e50900e2810341000c0000001d10740826801510b040d0454500340407008800c1c4910950880115821414a00c07100215640c0307014403000b5074410d41860012400b5035840da2030b000010982c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 28803234 1250 28801984 28802071
    0x1c080117160b03090c010306080c0603100803040905060f0907080601080705040810150f03030503010b0306150c010b011b0305030408071103030309150106030507050304122003040515070308 83
    0x982c030421200703610456050300e49015190200304598840c2c050704040390a400000e0038178180c151b0030003500d41d00103808013500c02c900380300000e00100188058401001d218400059500d03201041c01503940c9440c480c0344c4904030b00810481442c0d041006103030003803420300e403803201a620080c0c1600e05201d241c1214010781704929200600020b40c1e00400e455140780410480c0d8160380f4454840703040e06a00000380820410b00040c0f000300b546e1005194003100040c40c6c1c108203420018000c030300f6401003030384803c00e13510341c0e80c2c0744103d50700070b0744413021010801c5048040060f140c900400d0f5001c0900000d06900d0002111810f00021400885501200500f5aa524100041c0782940da4454500c42184e642e141000006c14074040d01c1038610500da9625a07501c0d542c0c0760f0fa078601002c0c0701d16261200380030a03440029000c4503514a860034007038031040155a59401c100405c405216000c10100b11044200300b0b0800080c0c2c00040b407904072100c100900010034414040c0200714580506202d942c402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 28804484 1250 28803234 28803239
    0x30509030d0c211a03010e060c0c0a080a0e0a0b04080d030b061207080405011a0a0501030c02010e03041205060f0106170a111c0b0411270910081c08011716 68
    0x315448543c4c8080446030b24101040024181400d03520701c9103200c0310769085903001036040d00a14004051043c481810b40c0e0b1540519510501c40c0c1d0410f84a2070300080381d40c00242c0d900e060400220001e0f0500082e0035042c1817a088150740ea40c4500311400301019150842161036417a400107070f0b07e003980d00c15111016803520034401402c0741070440b0151180e609119410708070461005030015840170141100795880e00300801074024104401a00c011596100c21742c54801200f48043c00c0980a1208213610401041c00d00e246080c0c4060f04100e104020080100f00b19500300001104c0003883c500211006da07501f0311104014034a6104011280d4000200c04100d0201b40b50700c0021f40c0c8042c002003100c0c0c0710000c2400b08a03075151203200816030040014009002e900750031542e00300b05007840c3d1140403c14901049a330001620310240800806105020304902480b15142d02d04100c40320f240301c0a15004000c10b04901849003030003010781d000e80181444000c1c00710300700070b0b031040001102503503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 28805734 1250 28804484 28804547
    0x906120a021e130605030702030d1103010f09020f03040209060307080a0807020405070e221d0a0b0108060c0702040c030608030c0c031e0304090e01060f08010605090106030509030d0c 80
    0x62000018144503502c035102e80b410361400c141550990b00146690b03142076414088241c800394009807201c0305502c001e10998451100b107000702c242040d07102c1b01840e00c9524200003140084140d4106828480c01404114a0b4444a80c1034070740c4150121a0f0b02060340750580801d0800807950810f405a00440304038409000308180200106842503c0030030030b036510984121105030305124138075444070340541d8900c002458804911200d448041c00003500d402182901c040f44501441400c100c0e8020107050801d0083d150402401803291f800541010b10b040180402944618003000344610b503110301130030b0142e110f5030108014013000740860b6074072040c10154542c0d40c9011600a8460f1055000d07070906c249008460012200c03001c0010f60810b410b004030480581520100314072950750740c400028000c250703540050010150100002401c1341171105208407504141c0015090505213814004070110010403903500c04980d010004c0c84a00c1c8200c1124420844042c0c501681205d50007040c424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 28806984 1250 28805734 28805737
    0x4020f0d050105011e03021810050415090c020d050d0216080f03040507080d1b0215040303082208040308070c050a08030a030e0c0a031b05040f02091201110f0906120a02 74
    0x300d1211049210700c4580444002e2691517500000350030180141c40c0b410710980260307505402c40500690000002d407224013040480b5544481040710b191714610410007020140b01d00d4403202ca09101500c0d926500d444060000c1c824078401d1a501035002605802c2c0c40c05240d5616000c03a800100e941c0d490082c00c00751019a0000d84061307503c0d01a09000107a540e000180f80d00b07900e40c503500c0b0001c10003140d92030800110010305c41a07800c556040e914101c4010a54014009075100c1d44030242ca82c20000a608001503041828454003807400046001041e242710a49045a90100405948032000d18106103244c0c41c03540590f03001501c0314800f0814407008030180c40038641d2503800b0032150a0b00c0c8100c0ba40d6401c841510360300101004005e1001c20210191409041d00a264058105503220082012200d03108008204954080784551070b924000c400c41d240180203a000348006a03218041c41035510500380c819680c2d850004041c040790315088143c88004000c140410b4207803504a101c18041e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 28808234 1250 28806984 28806989
    0xc0607201006031b06090b130308030a1407020604020904020d031803060e010e0a110d020303040b0a0302030a0b030d0914010311161106070c050f12010903111002041d04020f0d05010501 81
    0x20186518136a80038000540ca08115091a900c44078907074503080c0c180801e544100c00782001c08003020f80110218510340019802000c0c003500001e44c81c0c0e9030010b0070540c0e00002d4480401c541040c4103000c050707035a02c16074030b41040d0110303941e01035a0018035040e502a400c285007803841440e90100002440443e60100c0c0450503400d0080c0f1080041c03907000c0c1d84071600000b0041c008a001c401c4c41c080d904011510800e01d038800f4003144d2416480700350040c440d07004601c914000a800004100300030010303002e0100001d8060300142449100c0907400350100402e405142c1540c45d14190115182c0e01c06c2c1c1007949a040d21018181e42c0710b100d8015220701c9082a4019900740059091500d81070901204407407131543c02603800c01150303050030100604d40100300040c0d13a2201c0e0f491018800310600b0b118406010384603444003a2900740030010b850614400b07002c0d074080c5500c144401c1000e59018688603ca6008000344020310703949a20010743d210050301c07112904a880c2000003000c204055000c01d05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 28809484 1250 28808234 28808243
    0x6041a0106030b010203040315020405131a090105031005091c080109060b07080703080702031201080d2c0f0a0801060e07030e1c03090201090e0702030702010305060301020c060720100603 82
    0x46a07889200036002d883d00701d18401d0040e0700070402040410302800c50201c80c59134440300585040d550742c00140c01c403000d0b00c0309043d00580e81c0760404044000510654080320040e00c034a0081c0d03152a000a807905000140b11046c00d443e400090311034907007406003829504560b4910f400d10b610219008000d46424011108941d241c9100410348094581c2074441c141d9010705038a00c0c04100d40d9080312107500103132100d001e52000b0300041461144040300b041c0038120103401054090b1140ea002040090207400e1000251030381003080c18607690340c03d500c0500300c000759030700c000044080000c640301c0445503000c0f03c16546030883c0420b40384000c1c2c150a0045641d6601403240b0043c4445072600d40c0b081100c1c494040c2010b46600c0003003402a00492030250050410001c0b013603940020f0044980225105001a000003618804542c6c00d48100c03600b222055000b1810304052104556580e003000d8880c3c0300748842071300c0614111041304400e035a034a10710310a031010014039040c814003410480c0001c64 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 28810734 1250 28809484 28809533
    0x4060e010315080d0507030e1518100e0621090307030206010602030a050a140d09030906020d03050903041a070804030605010e071706061303050f03030a050c0304120f0e030604 77
    0xc2c200041e8030203802a6805840500303640410300d03206840350b510070b00c0100c0a00c0325060070104240c4e41e00c003180810780c10303003014290348507050110f55109002c0b02c900c55100300c8000a151116503170081a04d4801c09040c1d4030103075a011a1002100911500000c1031a94030040c0100940c081c0e010000d02a05440380c1c003100c4c0709136210b0700160303100d00904801c900000c00501011040c5882005140150114141c480303140c610b4002420054815104007130b00410001a010130180e03030b04200401c1307840d1480ca000c004ca8100120034a49a02c940d20903000031030b0240c5c080820b01c10b500750442d80d0b11640307c0d80d00c0d42d88580d2890b10b20050042441074104040724440050aa00e0041d2205280030801c81840c07078007a6103e0b810040583c000c20124000901d4404001c00010005c004031120818140000c6450b40b13040e0f80960140d59000f001503105150620610000034180031300f400c06a180c41c10210503190807480c00301c4824414400c496850b2244800380010710000103142c02c4008400790501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 28811984 1250 28810734 28810751
    0x1050a091407080a0204020306040b0904061a0a0503100c030605120106032303070209090f01141510050d020306010513030b09120903070e0a09050f0618070501090302060d1104060e0103 81
    0x158031001c1e10f10070b400f455001503992a00614280d40115481080248005a0b40317048401054808070100c501310f070201d589004a040c00b41c05001c54948401e401c503a00030401d420301c40031130748034042c0180d111111511251030750112402038000801900c005010101c0c66051404980c1c040c000d14482551641c5d281001e00310b1016a002070f0148020410004514102d115828001c000030014401503242c0030300128400801420f015030403081240341c0c150710f0709042250007102520101d00000d84140c4a16181c400e925130040b003603454280064500588a541d07600050310540308500010408019a41011041114800081d8007070740e0ba44044402030b611703c00c08101103101d084c0c805981a80482c03003c000d0848110030050744140a40c001042200e06070765221b24066807100000110342150303042141d1001c011007107604040c0c442005004640c07074000040d044c80f2160001034015140012072600180258001c11710f100440078541d42e03240d03960f4000901c100c0d0300455080c002824440c05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 28813234 1250 28811984 28812023
    0x30a0305120a090c05100c021507060617071503020f0f1c0b0303090d06020f030907050112060608061201020721030605030a050c0d26130e0907061202070501050a09 72
    0x1519072190703002c5a00320015052008201c11120341b0821001089561100900142c43c2d0107400c00c4000c054980113600d982991401005848c0640c210704900b8150803440707a814403000035a00200c40782d14209100c82444040c044020b0301c100c2d1014035400c1c000182d042d2001c10500001c000c403603025900010260306118005050350001117004d5419441880003a000d45010480032030020322840d00145415003140803041c2c5134004546005c82da0300040010405945c1000388040843c00048040142908024015260f204090045801081c240d01905c0310450f0940c11201d405822800410715402c081c105040007100d11124000041d09242000989040004100605650000180248480a60904c020380300700c410182d804075a410070500b0028000350002c0c05180a0340d5003259200d0381280a1070540703245500c0f91001c1036030783c000c1007003c0c02e010030b016054407480e141c8882c2409052503064060301032000040c0c0503510b84000e11681c1000c5500c10b190691003045d8203480203100800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 28814484 1250 28813234 28813241
    0x103030f0801090519020903280b010503030310150c0515011a07020109050d060605060d0605041b170a0f0e30030c091c0302010b1906020a060f0b030a0305120a 70
    0x1c103907a148044110b83e82030300145da00a02040900641111200703c0c2d03081c584515003c10030342d84101841c64082c0da0040c880703040403017409410107030000d600e5410182c00302070390341640b480749088030070b0301030065074080c0d00c1401040c5100d5005411281104d0f00c0c09420040c00b0428400c5a50850440c4902c1c1c600000301001e542c20560141c50382d940c3d0925040a2081e10700c40124200d45a42d40d0b444081419a220f0000c2c20410807000310004485040c4030500084400f50740f054480c1111408400d60a5680085c0381e4403a070a10941c051341070313222511000081c00c0314184005030513040c44003070064850006541120045004d011005608a01606500244a81c1c00d140c0d14440c0400000e0760351a00203008229104018000050326641c040b8603030b140c1100c0715011070050751101d40b441e034140391022003411107001600c026481285407000195030741100f9100100601c1c0c03103c90140c00e0f0076039a41702070130745a4040d0565402400034a0000c00590000c0d6428920b20305000109003001d02912 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 28815734 1250 28814484 28814491
    0x60907060f020a170c0f060709090b0d060b030a12020c01021e0d11030403050d080411030c01080612071e0501020d03150506070602090a0306020c150402150307170103030f08010905 79
    0x200500405440c3c1d0300c540684d1190000d07104a5041c0400010311529010418110706555010281900d800c01c480000d040440c954400306105c5d00303007030080c0358555410a181c0f1859922400008104030404082030510074a00c50281c982d0310b031412110b900540124842240c05000d90a40b614122820b02050010240c40003a00d000e621412031100b030103010385150040315612004890030680d07642d964070718080b0050b001c400003607a03000500040110704503119180c0311045018100096068000030082c00c00108400c0c0b040c02e819200c403414210a02100010300740e8514200022905005603014078034003846818018400c55500005041c403912400c50780d40c11300c03140e42003481d2a01c002c101d041d42103036506445995082201102030b1b40c540040500552051034090b8840318190300c8141091101403a80290390103800c10000147d58601d2400e110031240d403000750301c0c1d07200c0c00d000f15889070b00004040c8005400e40d0011040c1a0411070102c454512642e601d0f0842e0b0700c0d4007802d404d0754000e8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 28816984 1250 28815734 28815737
    0x9020421050706030903050f0403030905010f0c0b061c0510091109010e060d0204110a11010606090308041e12030c050106090902010f1d0604032402090901030f0204060314060907060f 80
    0x69003d1000b540710790805c1c2010381c001e252103401d14a209110502a6000f81e0040300031400b80c03401002256002016502c2c07540301c07410445034100311502c0c0c60500b160001d0460307101e00d419600104900032403130000203840740c01104a514400c0b446c0503034001040103c2c000d60300a0300c2c2401704940c92412400a9042c0d030301e81c42e4110740d20344401081c060072081004003284d005464103442403034901240e015140d030f03401030341e01c040319a0f10b03042c001800c658041d0000000c0024540303080c400b145003142203600300c0f0400444001d501c200212a45003007036550b0015500c3c03042c03500005080c50741c0551b00c240210700520081045503900c1e40c01d481200c180c0980280800e4130744003207500c0b5501550721941842c1c92250080d00003d1070200055840d8403d030802c8500007070820310342540b4030010040c084d40f10b841d10001c42c680b12201e000950032080500c0f005101c201c40e030301d00c0301c00c64585402c410300940c1e03c091881000300e51400e201d0b4441c101129011403622486200040041c0709045000d10308107103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 28818234 1250 28816984 28816993
    0x8010207231203070512130b01091104060c060605060408031b0a030e0105090109030c0602150901020301120f080f030a02040503100c080a02090d05030a050714010b030c0126010902042105 82
    0x391002d00655000140900c0034841d0a01035840884c800c808124812480c0d0072100002d101c9901d4407840d0b40d001a000205114a07211403181206010400c46003a24550700f4142d8042a840c80c1180280c00c29030084c1340c102802150000d0f8903000040a0403c025822032203441032242c109a8580d6400b1000c000340c00204107205546d0694015001040c4914061403e0380303003940c40c1d85490001803641c0e403288006a03c0401c90300d2084010610054001d03180d07400a40c07455250641a101d6101c02c4200903000c54035034001320082051000440341c010b46c001660075140d01d444038501d0b0082d0043d1007414000c3c020200d2030010038909201c1d006c4900e490307466581c1d10f5182c45017890001c0d00200303034064002c0004e09461000c035104201030f1812a02ea561450b81d900744614183d121403007141c000805070382c18044940707207940d00030801010b415001e11384020201d01e0215801820001600d0891140e0084d00c008220041c641e0000d006480f545c810300950200345042d0140440020380010300140c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 28819484 1250 28818234 28818253
    0x307030809120f062d01030b060d0b1003030e03060405100f020408030403050d090501020d020a030302070305190306080c030d090911040506030f0a050f0c1912060801020723 76
    0xc140098411450080c0859500b0400c1661451514965401c000c0859000004010310f25180c01c9801d00890500b801c004100352003080390344070326201800300a0440322001b000a0a50300c8002554840b2034000b1002402820700254500d0b804450b40400d40010304d070041111715a04000030000e02565100b8010000010b80c56068001030590100c0381c600c080e02004001143c030310803c060000fa5010380050985000103c0b0094152212940142d045d504242240e010b482d8010a48004060f0503080141ea1804586400c982500c15845001d442c1c00d01d1403d00781c03d0310380c16413100080d11b015008a400c0100020704055032b42045600d40c00001d9843c1c2014001800030360000403070640314258460806446000143c0c860b0000c0704c10055118207501080b403e0790042c0141074102c07042700e4507141daa05185140c106a449a017043c048401e9004c1f0240c10105c0c032910b20030041d420002d40030070030b580e04c405203517000c4d500a01c4107a4807051000c0b10b85c10042d40000e900c0e40a8010b600040540d0203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 28820734 1250 28819484 28819493
    0x306010309020307081006051e1302070510090506090105070201060b1c0b03151506090f1c0c080709110301060905240412051504030806010e06090d050c011d030703 72
    0x252400c41243c060051840010322924200203078402100c00080110760310781044207000c4000e00c048828003a806000c0800c001c16220f12010301c0c45c02050540c056510290390030224640005000050305444c5005140001d00c60041041030040e4801d40007804291039140d022400d172101c900039411611000c008000c0c0b1010b100e01510f50705081080d01142031041040060705144803801c14038a8030480c00304001c18400700c4c0104541c0c40e40103d650038244117210f004510bc404100380683d01506001100b0700640b403201a1004d0f0140d4007011381d00e0483d44840300305803118058032588d5900d41c18420303500701c0c2103000ca081d24141c90066031080120f074034001c104142c2d25200c0c0c02201044000060b80d00041d00100001c1018000c0030900162804662400900c0c10510076040c0d0301040d841400d11000070b91119006401c13082c2480c02000b120f01090000f42e40340301c0c040345913a0103080410707132004114010a4600040c4c000b40c030b03800d02c544682c80601c1740700010b03941d6155042d0003402c02400001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 28821984 1250 28820734 28820741
    0x10501090519090203160207150f03050408070b0a0e0f070b0304060510120c0e01050102030a0c06021308010524060307080a0f0b10030b1c0f0b071106040c03020307060305040803060103 81
    0x840304048001031a5403444014100e85c01540d0100c0840003030068103211580401c07000c8024140031b00440014214200001c0003a119500701d501059110000300d0180300f900c4050700c0c1c0ca107402480e41029410036a540d28004e107280e1a815072030740120300f6940480320010a28004503014400020300e150740d075640e00c200410005001824070501007501240685c0c40d05080c10040d4814081c4031180c80c02c06070850100c603016481b540c1194820454082d155034003030401d403030869000702c2c05616404c09030035a03d82c00e0312941000f10658030700307410071a074181700820605d192041c880010154a03408810301806103c00c44890300481d8038100415804101540451202d01344070500088920700b81c0002091911900c40e0a40000c0d1200721903021407500030703180181c15084400d160b200d642565507046882c0503085004e84113410020008400c0c0b4081c808080042200c5030994840d45001d191803a007000031400b05038000d00c10060007148403406840b403070380a960021443d80c11562180700440c0134 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 28823234 1250 28821984 28822009
    0x30408040e0112030305101202040f06050301020f03010e0106020a020d0f02010e0d030c030305090102090a03030c05070308040b0d0501090b0105190e060414010806040b09010b16020306040b0103021201050105010905 94
    0x50080000003401071228107a2400307050302400705610302420f070030010140c1d280502040d00382800310004011015040c4034001c040b0768181ca02040c9007030300d0310307102c401400e56501140c0c1550001070b46503800c00800e401035040c0c0b1200351010300c1503601c5540482c1d07603108500c8002d4004091911800c08104a04041d80c0c0c0b040c4149032054460900e4000300d120640b02000031400301d078081c1c03c54010103800d805030a40c48250301c0d00031801c1030545800a400121944800741c18002422501000d000d014030003034029503080306050341da442d41c808422955603c1405946c20907480c2c040046079055450080d14082c0b00165901810b142c514410f0003802c0c181014010305100030b6280e02001602d0b0000076000501100c2284060031002a00150204000800d018859403409030208041c1e070340c7c0e8084074151020850880d8a400395039607018034145541c40c01960500c80c1008000400c440c035101541624400da8684814600c0e09a0081c26a071080c003d041c00300380154810b01090034213000e00d140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 28824484 1250 28823234 28823243
    0x8100f0902010c02150f0a0f02101103010b0f1b0312010e0103020609090a0905060411030d020a0c060807020703080412120e030a02040519020301090b03121201090f0e010509060a050c09010e04020304 87
    0x19011070a15403d01c0747d0f01c021408800f00c0c08458614003069014480e4003071403a4100c03414403081030403002074151444140070b00c403500d00000c100107890090517025900d0000b5a2600c2e8140300300d101c03075a15903a40000048803485c28070a0004640c030f00591404034101ca40c06000a03042407044002c00c220900010007207036960340d84998031004107604110f0706000768007583c0c0803040341c00c4107000e05040512907480300c429540903001c0e8800190078400054101d0b0b80c0e0b40b0b00086d0989076613604904051950703101030400c0c5008070f0041010095020b2241000344103100015200000840c161210300e2988503030366043e00182d8034100903007055000f05130300c1400b155800c00c0314442d04042d48200d820a8001614a550740c80343c6140d981010040314040c000401555410a04e800180a80f23415050103190030450702d030480d840e03c205c0c00d600310080d07a0301460300a202030700c0c20084007a6521400c507000881745040c08081010501124112040701e003041e5241c1e42a0541102800003a5202520846 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 28825734 1250 28824484 28824487
    0x50106021506210d0c02030115060519020c03070609150806011d060904020c0a020a0803070b0714270427020d0c030203060708070e0103020306090f04020a0306050108100f0902010c0215 81
    0x4445a05100380e929001c95034507401c81c80c501c5c50061608560700ca040f20003040d04400c00603c01c5a40140944503d2040040410b60740c0c01c10031001c070300b048030003c40d45406105915020591a410000310001c1d1b800540d0203400034000c4403012110508140e5515000c0f40d000e94021004552507a00111008405801c080ca46000c40d07010030226802003a0340041c80d08010941011403401900181c02099808025030030035019231a2200c070054080c0020060207125540c1011b00381e003d00981d050b800f55540e140c40c00c260302c03262044800020b1540544900c0c03410001e240208811114080c0d8130050038000183e10415600340110742d8603131002500c50498180000005075001c00119101d00320340c0d6140e8259040828001e0301c440c690070b0f0540c0c103040c01801008800d49074051402d5200300802403400d490744407400800e41c03401890f0000303044942030400104100e81e0019401e503a1201c40b0304c0402906610400c05000c0b0342d00030400900054254034054003624011900b4440740341d9a40b4500e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 28826984 1250 28825734 28825789
    0x10050306041a0a140405090304030b0f09010b04050a0902011707021b03070503010c0207030c14030307030c152a020f0309010309020109080102070f02040608030307091703040e090a0501050106021506 87
    0x50070451072640000101004078244144e9410f16014503900304450f2001181414215500c42c0f00070070006041c00d09520345400064000710003500705417070f0800c024104211728182001e89001800700000c2c2640071881403005950401d80c40c01d8080d216901c00d90282c1100001409007540d0001c0e140b10301c0740e051141e0740021450399001e2140c0c201440e825001408214903503c2c2c005e181c01d9407680003028044d0041110303102510003104171090181e05240c040c4001c07407a072811001c82140d160012410301e2400640d1107009048080c1c444001038100c066910144802c10101d035240c80c001031090090300306025001c07403035020390084110f8a2050400200c110380341c00030350f0b00b240c0106509860050503901c50805500b0548030307210150210901862651401d0440900391b082c051242000e80a8500143c0020840c140141e40290101200700d85150811043e40c03642c68000000954081d440d00000107034560000450176039a424100c15a1080d030b81c3c400401c20440301c401000f02a0b500300b984213 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 28828234 1250 28826984 28826989
    0x604020f03070e0907090b03030712050307050d050907030221030706050603070803120f060f030a020f010302040906080105091203060d080a0909020d0c140406050706090c03050a120e10050306041a 86
    0x3a0f42c46042140c00415400d850290894252001d040d50f441c000d800411244000c03c10f0f0f078016440c840e0381814221741d030b602c030070100710303124803400301460300b0145400284141c005010402e842242e000701c0c0e030468102e40321a001d403d080c8404d40300d100a0b510421104001034201d4200aa00c07100040990340115030f03e0806c42c1c1103501c52201100f14008a0003084103580c0100c40350350b08a001980c40b90714852045020a40d07460308508007920520701e088031084107070300c03a8045901802c1d52840901000c0d42d00e60040b4040c01081c0c4c0c80c1b080c58014a440c0041d00c030072800640f0b22501009245100960107526400910b602900c0740d1030401c10303680c0000c910040e0500080c1071900c1c040390002a64000613100500c1c0e46014810310360341440c00c000c10011a90b1100969510369004074000a03400458a00300c40d062141e03900081c40ba0041e004107109110584696940b1102d06448002118640c14100714890042009500c0070a40520200b031071414540d1180880310300d11484440ea8480e000c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 28829484 1250 28828234 28828259
    0xe0604021603080103030206010803191d040c050406030b060c03070b04050c060403030c0209071e12140705040509011d0a32061003050c0901030209030a0f060501051008090604020f0307 81
    0x9080d000700f0980c6004000709541000024014980e0354051420001c207a00340b60003e0341410340300c904006800c400d4084244800b003000300c680030000e000700300088004002520710b410911610b4040391500328851010305069003154030102511003d1480c2410b283d135661a03405002c0c0058030306102e41e020b8005562503010050001c6d40c06034a40c0f4070b02ca05603104102060f58000c0c0448100700f203034620f0502c4043c03141500607801d941400e05000100315015800020700324418020405803140d0203011100da00000244280c60341510b07c40780681e290f00107030301001d0111003107601d903402c00400200c4002140d8031100403000c07032040c20301c0250b00080d41c80b5622130310a080741031040240c00a000c1c640c901f800c280030401340141400e20042c50b16142d2400306000b403002e828149030b00000d02c90a0369030107004c2d1441c2541c1c0070252088038452070030002c00910b404d011382c50103203484e205014500781c080c0120328465200403004002950b61542403100a0504030401c82d05840b030b090010907800140b00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 28830734 1250 28829484 28829527
    0xb0a0810020313060f0605040f09020315090a0c0f08160b160303020c100c03051302010801140a0e01080105040302011a06091201020c0102070602070c05010309020907050a09050a06050c06010501050906040e060402 93
    0x5c1000c5840c80c104010041106e0305551008400e41c90040740500503103021965000c074000303c001b0b0600583c0c41401c400e041c480b04890007048141c40900114502104a658a058490880448041d0301303003c001002c18140368000c01c81c00c5e003400c1c0041c094035103003e40c074014990322074a000f41c10b040c40845a1880d00441c2091010042d0300e07441482c124680c1807045507880000d42d02d007021800059000a45410710600072207000f90400c0d8041c4160f0348039080032500500d81d0601e451403039a99001c0503802080c094500f10015420704948020030315030710390942c0d101100144a5441c1a45210400801c1c0c5074480c00301c6c406540130302100c0c810031001e01c040c03c4001d0140002503950102c0b4508284034608540009051626200d00e42001d600c8400c4070641c090003d0500f00d594074a16a425a94901c2560200c1e1703200b02402e0010070010b1307010000e002201701c42800c5401a903284c80043d20b1a01606c2e0700e40f6040a414001008aa01ca03100c1240d0450009040140340207610080c5112945c141c1c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 28831984 1250 28830734 28830761
    0xc0405100e030c040213090207020f121e0a030503061309141f050907120309080d090e0a060b030705090105070c0e01080d08010321110a050d030b0a081002031306 71
    0x1050716180d98101881006409542118214540000c50100e00ca03926124040d9a91060340031600004549960903802c444900080c09030044018a4280304d0303840459000184a007410a103d280040034001038041c0c540742e26840d42401c2d55a0041407182004c05041c69600a80e1140004008200e00903a07419400b0402d0028085562099550034007403a07010b040000001c1c940f4042080c4800c0c007203101800c0d030312081080780610030f880c20100c4402ca02d54004803228080c1200751240f080c1c10841c00b00483d450b004500380702c1d80e43c80ca284c40440d28903200c1e00c0001c801c1000090340d03140c821002011400c1e4141001c9040c1419511403540c40c8071035400029021071400014441001c04000c8200081034074540600301d5030441c2d82e103054070212030346041e11035040780d00040e250500410190800c0030028045801100b2103007001d541e90101c0c81101c02c0800c3c5841d6100f041424001c902105480400c40204480303075850b00b03604000d5100a04041c942c03015102040001001e43c0110a082c400c10f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 28833234 1250 28831984 28831997
    0x6080705030d171506070503030a050403030c0203030708070f1103030c0408010b1207090f06051008150a06080f2205101103130b040201091d010e060603010308120c040510 75
    0x105400c0c54603250100702c01c0018081101480840d1050760f9030a554403804699a2210300410032021071150301070302030024410b000210070010344a0340c81d4842c82c0700f0781c000d940c20b000c4843d0450050762030307101c117a840301c000130070040008204900a2401122511040c94900031014240038054156003040d1006140400300140c10000f2000901412200361000c40382455aa1501080565a090640305205003070703454241c45a010300c4103510040080c040902001680c10b8a010018071480c001c6412688000c0003801207519805c0807036458058036960744400e204c1d030311044068001001c0040c00074000040c0810b1102c84e40000c411351540c894400c90040c84000162040d00c000c0e608806100d40c440d007000d108200015a500490091194100310508920f4445000494007a4815000310010051b2201104814100c140940e41260f40c031304898240d0303465403000c20040b44401c1c80050451801802149902102c60101c29013102520a07286e00d86595000800c0c6200011000000481ea4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 28834484 1250 28833234 28833239
    0xc021c050604050606090f011e0b0403080307030e0609070504090c030c0e0103200603181005190608030901020606062d0703081003081909090207050105180111070b0c0706060807 78
    0x7001c021365078121908507601e000302d150044565400c0c0c501442491004141541090b100003e00140c0c030000c0c120004c403003a607460b103a007000d403440d0380181c4100d030001e4500031400d4890040481c2c05401265890050800d491034401000083d0000203c181c80c540c0c04224004006001c10210a00500c00c90700d0f011410b40c9036080841c81032850140c171000740541280e015425540360800c50b5805060354090494a42d46120054a890714100d04013111501e0841402003034400c58102d0a41d81414030014800203846103c0032b6124041d00304501e0143c0c1c0903a0104d20743d0314010029000c00c40c07030700400d403041c40031801241e0002e1000200c250000700000541c1340c14103900c04c0d03019500036000c40c1808045491a5610074251103104a248001d0300e40d180300c80c103040c1c8a98420002056141c2056441d202c0c5410418020441521441c1464024ac00c6004011006000e130084007004000790034286810350702c1740b005c0076100501d1140550010048507001548034841e040181c681400104480750 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 28835734 1250 28834484 28834493
    0x90b0103050d09031a0711070602010b12010204080c0103020325030212070e0102151b0f09010809060c07020d020109080a030215060a030b270d05130603050f070c021c050604 76
    0x110b003503078800400440c56818800718a100e15900b00284040218251070303516080102c81c1d00700010109a454000c1c260002443c40e415001060201d80868600180b201103007000d900300c0c8140e208060454014a0020100c0d40c0283d0140da07105010024100d084c580442004d00070b03030245522100801d5010504840304008845126405003150400030302d00281344001030364405081c91445048440100000e011034012046012240d10031408141c81d4801070304411180d8000f0349440380003421610014042081c0001c002e03000720b080d04200c81c509849602841003058000e0710682c1845016140003d61110401c814481603001c0c0e40941041503007682044080040035200358401c0b14503079800d0000c9080702003415048080c041101c0003020607095110000c08451241541e14026213501026454000d4003d00018112142c0c51041c9611002c00381c1c00c0303500950b540031051200e000018503d50007034080344403e50000300200c071401c2d5000000080001c0303e81e03017103d064103c04240300412 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 28836984 1250 28835734 28835743
    0x109150606140f0d050403020102090d14010f02031b0c0114150a060e0609010c05010603021c0b0606040605040509090c120a050601051c031b081206120a02060301060302130504090b010305 82
    0x522034803410b5881c0500300d41c41085180102c003490030400d95280d001c00d007050f000354119022460041e100f070010030150300b4050b900b014180b07881c00665003000c1d20b07032059102070320031288a040c1e4038101d03801e40031404100030890342249444101e02c1d90b0700c0c03226200d23140211020034442c0f00201003103044203440ba800e20030f903105203034000400e00584000940c00f90f42e980c015511407400a00c0c01283d0003401d07041031400340a0580c0082d40020720760000203040019240407040b0580a010421059107a02e0180b01c1c40d0b00ca9803080d680021000d100601c060325050b61403d030070481c4103007200c072500101c030000354501083c1c0c1e5440405510406813403080180c2480007500400d41142c094114151041034040950200100141084004804450701c07880051116407526009590b09494002c00e0a080d07d02610540e50684201c110501c001d00d8a140095291035603580680b1042c2540d18149042e4040e4000000074440380c00c10b900003082c0c50701c5504c01c030301403103019014002c0c00d5451740c1405400d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 28838234 1250 28836984 28837007
    0xf0204080d08100b22060507030207060206010b030606030403050d0e0705040c020705090a18050d020604170304020d030e0604080f0606090c04030b011211120106140102030403051504050109150606 86
    0x207020a4400300a000c00e2400c283c0c8044440d4940015642c07100c00008034590020200ca40c54220700c25000820880d82c07240182c1300c2540300c0d8003100c0285803600c0c0d040c3e03130315142482007444090040000580701e0a00d240916040b5209051641c1000a41c0d603258040c0d82d2014201c1070290b104c0b107020805481c19024003081c032400c074000360454508010124100400c0186501030864607100008d040c455244068011244c01405a4070b40c240d4417603000713444020070b039400d407000081219006640b03a451011240919070003002012281421b0740c0036146113659101142d802503050100081e819014080c800520542c100906039500c2c05c170041100300e100184c85491141c20a101c1031001414007450641580c00340e221002c0c8411aa2038840c0c092003203550011341145814254000f450015003700c070950b80001c40c0141d50b081c40790300490b030340c0c0220b100c0900340d648003007000b4801174400e061040c0c1090060300049001c008030348450821180c484d209030a01742d502c00c010454a0b902c400300008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 28839484 1250 28838234 28838237
    0xa0c0906050105030411010c050d0c02030c1c110a0f030506010810020703021b04020d0e1f1505011b0812010608090c09070e13050a0209090c0a0903080a02030c010f0204080d 76
    0xc5401c120000b403007400000c000400c15144040001c140d07038007034485582496440000c0b2180148000c1006004518090049010b0301c0344003c131420900c1c1813086400403400404a41e0031444807519441000380f1250004c941041414002180c0c00030401c01080142d802131006002c1949048200c0b032500980e4102420210301c184403040010381d001c99071500d5201c01c00307007101c1b0201c002d0300050020300c98044408a102e140445040748050082a02e15000c00010a964031482001d2022800c0d9405007030420700490342000c042c0095801150a62280c5400f43c0c0000341d000080d5489940076030150180001c6001c441d001003110640c003801180d8081d41810180c11061a0000811101000604003000303010aa004908646c1c444401007103d030040c03441c0038000c5041c035040c0c1c070b0f0080d4000641540104440b500140368404100e089030810040c035540d1688051031601d40e0807441d00180c0c2400d086000c1000440800d881c00d00654910425000e8010381d2a840c00b19000e04d01181000042c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 28840734 1250 28839484 28839491
    0x207260a09230907030f0f090b0603010504150207170307050c0708070609060e030118140d03020906070b0603030d0510060806040905070b1b030403080a081003050d050d0b030d020a0c09 81
    0x503074818142a501000d220590350f44410f030b100d24500390003030010050b0aa501030301e000c080490f19407964000c404024002e00c082c551548541c030515003a034100f03c4000d04111113900124501c0c4220ba80109102801010300c00300e4050840c007a51080d5209a0342a00001c0c004a40a0704404c01840602c00510307516000303001091621802034000c01c0c062154105005a20081c071a0b151029040520b0061260010016214041c5014011480d20f440e02c0d0005101c0c00d0000c1c0c41650080c0300325118110300400090130600541c0c0d80d00c4030501c00070030203030b00350006000030f00c030340c0005000d09401240080c200b84c20315420180c0040400d140100007078459401c1ca0382080100b0804580c010950302c52640043c0e07290703400e44507942c81d0035090701c2c0c0c0c890600c030014001003403203900c10207425100702d281c2d982c081035140c54aa80c1c0c100d9180d8000609a03400445c80e440b28035000302d000b062445120750010405d41a800d0001c0d0410032050428400f60300302c241460b00f000005561400500030303005040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 28841984 1250 28840734 28840769
    0x31507080c0304020a0b130e13020303120405011404080903100507080604090c080f0102190c1502070c03140c030c0102010e0c150f130f060306060807030207260a09 72
    0x303202050140400c070311070358008081003d5446100c1050064403d071004a03070303030703855420403100f40135114800c0308002d00c40c601c0424401c00c2c0501036201e015800500450505407004a030039480900a00211190741d81c079000c405510468030130a622450140e400c0c2515000c100040c5030402244900c0307100c0542c942010031040b1604100c149808c0b400c15640050032009910344031a8003921070300b00703003c1c40c8144400e60140490540040c04e10148400c410751a2489203602a80d100140c1c040044c48091031001500c6c100100354040c00245001d2140345240750703901d84520040f18810b10104000c1e03040380d038907a10310b418100300d50240703030754217100030050703011446402611802010807261140c65480c00b440b00110050054420001c100003005981344407400040e1002c2c1c1e981e21840000101c03d0400040392802880f42ca001c444070394035000c506a4a030b0344114020b41c4105005c4915220b03458401e01010319142c01c0013940102508a0303070b0ba85807a914094242da21035448817010701a500481c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 28843234 1250 28841984 28841987
    0x706080f0f010306020306131109030c030c0a0b0307090b04140103050601080103120e0607060c030c0219080307050c0a060906050106030b06091528170a0c08070f030608011a031507 79
    0xc0381104c0e000300005891f03440301d800107070b88901d40c0e15890304c200707083c00900c0141c0341d103e10003010703018001c90440d201224010b0901d03480c0d01036145016408807005008004205001000b141e110405103440610203440710491012500107409c0780c08009181555a070031540c0502c6019000708003424040810b40c03540e0380f070361aa424844595010062500c403441020345510050315280f56109500b4841000f00380c03c010000c0c404182d00c03000604c90398400f107030305180c1c0d01101032030240c001c11418510340e01d058080d00d503035102c81003020300c502c1201181c40108406128841b16140b0070200810341d0b525044c0010309403100101903174030a820400c1441015596038161040e180148014652900045860004401c1e4000c11521203859505105400d459203d4014806840c035082c0d0250140c031121020002c8070035640c40300c00842c83c4130010030745160081616144a20583c40d002c80c1d000c1c1c56600003800c1d51849004100343c181b0003070000d01145414007801c1070007550b8071114116071900000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 28844484 1250 28843234 28843261
    0xa02030a080901030f0e031305010c03020604020910080607080108010506040b030c040c030e16050102010f05070f200f0f01060503150106050304060213030b060112060605040611010615020706080f 86
    0x9005050303610004180401c0d034041d4000001d4450b05d044100855096804540c0e2640d00c88803014018080950303000c282e542c0129500d1003c190598010b11042e521039090122030000502075201d0321f0000340000505410402c60b07684544074a5403011095450100c5050a585c0c2c050000c2d03110f00c0c00d100060000d6140002c03a201c402004940114840c4407008080c0c00078040c4017a1805580a82c592030050300a2003080d00048a6007030340204005c202c641e5174501112419502480000c9071038183d00d0007148a00812030000b4800505c000c042008040e41e01e00e4100a420309086582101c0c500c84e52412081c45004014201500500801d900c00d01902038034000501a00e014417502001140602180394184c0c0c5a00d4000f0002241d580d0312410060f11200b03040341c4003400281180303105002c1c0000b1b80200000c039040c43d02d4181c209030818805840030703007024000007160340d40c2e1a00007803e02e904903218004209190050110203040a01c0148511802441d240094141e030092060100249a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 28845734 1250 28844484 28844503
    0x11406030c18060d020d050f06060409020f0409060e030d0e060a0504030e0105030a060504092d0305030105040b0414010308270105090112090c0b03011401080c07060209120304090203010e0106020a0203 88
    0xc80400e065543d035400902603000c40c0a001e074000009807982c104204000816841c818441402c0701c00590392403081009540300707904029049503202e01c1c0034505003001d400103888180b0402c0040781103040c1c060014510341003179045001c02510b5408c1991040b0062102c16005821904103006628150f14042c11707000005e0711280c104000080002d1a40f40a6030060000c0e2800a00c140f0800b80c0d84e0030101400404130404800c45000da0410400540c2446041e07e4141c5c0e040d00c0381c41c11603203003908000017410300b80c14054100d42c5403032034840f0b405046500c05010354481c140d8141c4038080107545c40381101d400109003944104120013580542e8000302501c1105001340780c40040d0640840002014015404009200a289001c0406d041c0140409036059403000c00204600c07501190045491402c2035a010701d10880c20081c0e4030102c1c400e074000700716900c00581b00c000307403051015850f45558030903484a9081980840144103460504a03410300410051000f8030110b00940c0001b5100c81415 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 28846984 1250 28845734 28845769
    0x507050a0f0b01140306060d11240a090503030705060a0c1101110a0206060922080d0c020109050f0a0f020d05030c0d050c010506010f080f0a0f0c030e010c0203040b19020703060e011406030c 83
    0x580030908075a1003c64880a40721400a66108c0e5003141c0740200e030074bc001541e41800f1422514001c40c0311308000099807603842c1c1010043c8800d407030b4524070b000282250a900410481c111f40d002548500901503c0900130000c060f055032074001001c001d08118000c1d22580c49140003d05004041940886e00d8584020580012550410506c0c240f00c091013131207000c5041da8142600d040e60300b82c041d03000a1980d80614160f460140300380301a0350312511000f1000302480b02500c458005403c000c1000e20780340d4450710850346011007440c40c61b450008c000300e284001400c0010000c1d080d40081c0100354100c0401c3c282200f00841544001e00b4800000705542e00c050300582c006482c281c0690071260080181c14030400c2841c1d12b4600050181c28541c240703044640c20f015030450780f03500c0001150200c1e64550f000509081c8202e604001d0101040f26200845c8503110000c004107420f84580e070b44809184c400000d030040308205000d400070004001e60703c42c1d00103644c04619074690141c90791881251 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 28848234 1250 28846984 28847003
    0x2040b0f0f0d0603060506090106210209030708010203160e0405070c0209130611130b19050703020106030b0c1c110a0c020a08150709120c03030507050a0f0b01140306060d 75
    0x101c54100c154020710300e01055281c1068800010b0040540c0b0032401a403050340c40c11a1071781c0310341050f60704015035400b005d03404043e0f00e80d082d412240341e4054882c06000074180c070340070703a62401181d09a070015140084c0c21703044a001c100c8000c0d085000303400303805415242880302d40360000015066205109000e0b0046a084001690300382040800000050388560100710003001200860030503088040d12101d19a2022404210b004601058620112112280c2d010002040d94200c032540c011101c02c50666485a101000241146031070b03074071402100c0c0f10580c4a441c1c100d074031400640310000e00d0300100c0c90220020080c03c10001250340b24115800c000c08611403600c0881c082035070756486a216801544407400c103180c0341c2c2c4d40141c0190b6881d512400c078903886003107084079041d661000074020f00c84030104100081c0528041e0145a0044064a065030080e4035400b84082c03031010f040f9481480740005022401c45070206031080c48054008281d60700d811004610303480540b0348042d01c007110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 28849484 1250 28848234 28848247
    0x10b0105030a02210420010801030209060607080c011e060b0909060405091002120601030606080f2d040f03030513080306091b0a05070303180b0708150402040e0402090a02040b0f 78
    0x40d02d40180c49026041365511071030385042c1c00c140022000d04416403e050701c409040220302d41c40381d01210b058980013020003900d6201c81c020044990320594080310581420b11542000d141c00303200b0700052240310314000c180ca003507010402040745c82a41050881c10f60a00a00070341d9102c81140e103500c2181900c00160b00d84034075414600d007410303050041100da0300000d40380c511502c07d518450300980c2c00381c0702482840c0c0c131041c0c1038680308800c68401d041582520b0000e0344040384024000803c1030b1071a0507030380c000f01c00340340801d0a500845080d690341c60b60000e50010140c0c1885860f0740300c1c4900701005600f641c1566003462a1001500e058414859480840e042da00310030a07100e8106080340303001d035481b02504800361103900a0301e81640402d1520304160b8210001a90a50701c0b1a8000c40040d4903684804050b590110080c1100e0f207000e409610025040d00c07070344000c0c0040c202144e01c142080ca031503c1040f20405d002011441c20700d005000801030303600300d0402e6586042c000b00d4801e8907000b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 28850734 1250 28849484 28849507
    0x171312030b0a090606031d0606011209110406030803060316080a0f050111040e0a0509010c12020304030c05030d060801060b040b09090903071b030302060601020c01020c010e0a052709010b0105030a02 87
    0x194280c21800c40140342400000b0340e650580e101c02d00c0c40c2002d0828100c40002c0e10202508d4102c02ca4145010032032584d155070708068150300c0078103001c1c072820103a10113a403403502180445110380c0040725612800800e10441c0c1c602000809010200003807030045d100e041c603c00c1c0380c8a03031507030300014207480103898400b0030424290002c18900345040603094980d50350f401c800d030310410b00786e82060b05070b8503080c0803c0c0728a0042c052201511050740301e501001d00e454074040c00941c8010401e82c20020f035101d02c900082d00610051007251180540898021705200b4560700b104d80c1540204146032042200700041502c03001959100c00c4112108485030b03071502c48127403d61240340c500034045a40208642c4000320280e50360320076a8001c2e42182c18941e02c60b401a030344e910303e6440707242c09039114801c0c0d0902580706000c09146000003811240c038503565280800c1c540d2441c04160070241d0841d244400f01003420f00311f02507000300480001c1c0240d4244000181c104c0c44003401148425800141d000d81c3da0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 28851984 1250 28850734 28850749
    0x30c05100507080a0e12010203060303090904020414041203060608041104090c0f0909030e0301020a170a0b0310020304020102060c0f0a03020904060b0a02070503061008070b0901030e0706171312030b 87
    0x2d540110885130786007514000282104210b0388001e115400c40c004410300141c051003564415240a0001c524240800c001c005203000010000c0781d0040d1900c006010501e18103d419000d0740c41190404981d441114001d0140c0b0003507000001002144003c11000c524030050401d49000b00760b500050303d02082c20042013a4845030400760101c0366600000800241c290300c400d2003580280c0da0000000d06040c10907081c6e105680c0140c0c0000d2903a00001060109006026001042040d000900181107800f1a09040901001d50815607010040000f596010300004e5840400b400a0302d1034403810680c400c5003400b0380c9100702c1c10564081507a594039100c036440030000d44160043e1070b844a0076008000d5868400c1e0090310301901410001c10340444518042070b06030748a580103807110b075040081205550b0407540c40c880c1015140d54084d00c04440034041d0030050311813580c4d520441940081d8801c04c15002401401c4601c800c0b455900100c7c403841040c0150f0842c910f00070648100040000d400c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 28853234 1250 28851984 28851997
    0x50d0e1504080913020f07030e130f0203010f060c0302031c1413050c01030e0a11040f110d06060c030f0e010e04021803010b060c07030b041a01170c0a030c051005 71
    0x80180c01090009100448015220740c01048800c013440c0780010350400300303a0140e0210400419402d0040c0c0700040d02450400711501c3c00646007501c4000c070010b00710286e40c0c4d580d458800c035980c0040140305158035030b082c00c400307007501c0e0805250b42d2105580080d85c80c844c0340c0f064808c07902c501c1600740b11480d003504080003030840540d525400381072000050b0290042581c0c1103456100718402d4013295402401420402c00800001d030000b0881515180407001d010f280c2c4941c1302c5c2d03983d12100d00129551064a0301140d104118641303030003075009804200c800035000038007441449007060b40003da00c0001c40005095507d8024840c144901c0180c550041001e042d0b80e01900109402c1c24402d01810b5514101034105e00a102c03007000c40c024801540700d01800f08105400101050000c5110300da0b00c60b802c01d00c5030420040030b907100510001a540203070456402e10aa05910001c6100208405000c03c1e0040b070745180740e9841e5a80d01c0030341d102940704190050340550107080304180110103540c00d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 28854484 1250 28853234 28853263
    0x5070f080403020a0324090201051c270302070e060f040902120d0807020d05030603070306020a02030f0408030403020103060b090a050f0103090204060306050f0708040804050105090d02030a0302010501030b090d050d0e 95
    0x10440e200d00d0301286e14035179840d03400c4407448551644035117040d040c002c4004468040e182d0502e010060b142c00212810340420710082d998480c00110110075140a02c100c1803001540c01d0201071066190090421040343d21140c2d1864202082c0004ca076140d0840403540001180c00117004041480410200c040016144150340030b50848000d220f60800c034494030604055098802080104405035000d0005880e001d4042d031125100340f00203030f41e030340c01040b800c9458011642015019003601c02c055100e60880e241c40d800104042045503018084c0c03178081c00382244114100b100040102d800da00b40751144a10482c114481c4c0c03162a400381d403001c0959500a00180259030722070030005d02600043d07030003404070512100050011031042102d24000c550210400349041e103042c00440c2d00e070b00050100341d40628681ca108005a4040004500c168840e400100e4550300d142080300b03000c20000c1214400750860310754818a41d40c071004072202c3d02d1800302c0000710384022000e0245031000518181a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 28855734 1250 28854484 28854499
    0x90b040608010527070e162d02010b010503090a06052a0304110108040201021908040e07020d080106050a090e0a02071205040e070306050d030804050f060c04050f060a05070f08040302 80
    0x560b1410710250402c00004251004807403013441240d10b0383e030314081c03084080c24414100400e50f0401031420000c0e411801c0d19061180c4600c103a046c0051010090780e060328003c40309401902e554081c040c00820601c242015811850050103042e10340702580001002c1541d03850002d001c6c05810b0064210344090802c0d00b03074200c035400c140007035142d00580d03080d0750001260080588640c490369a0900c00c55041e40900820044500741518204100000301c4600d402804046100d086144031944103040550081200c440180400b8150000680140041040400405094540118203401203400404d80145169100501d8000900400500a0494281d001c40040450b4000c0291080c3c07940004040056290100140c003101d405115190700070550013214804a07000c0c1c0034103507000b4007840554000c0b24101c40507078180081203440403035072800800c0c1444581000702240d030300480c041e80c61500d40060020060030901990701d0061016152110280403c10000c0c01d0b503006680c0500101d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 28856984 1250 28855734 28855741
    0x20105040b01030f0320010606140703050403150605060703050301050f030c03032a01020f0c060a05010e0a0c02151008070906032006120103060b090c07020a060e0102010e0a050a03030c020609030301090b0406080105 94
    0x8074082c14161003001d0010703070580502c65014001c680bc40d20045c0c0d050300d80c1ca19042c95555010780c415921040f104805039900320005041d00c03101c00400d2650b00c65035030079680350f0400b02041840003031810300c580242c0c04005614042d0f14000100c841e2044a102078449101035840c2491740510708086400f0254004658050000c10b64801b070000b0801c03080640b400f607507403c0d10040458809101703421500c1d4560010944403a00c0d80d00600901e02a032040e030780000c00c1010990001e01c8152409440c0c55100c2d1810031058000784040c0e40030308040d00701405418a16200d031101401a0b00701e80f60b99000a048400c542e03510300086401160010b0500380700396961b420500300a008141045010b0152440000c04004140048602c4113034000c202403800360401d541207814600c5542460b05542d62600401c800c90f0f820072032003150900c00c00c000d02c40441140f50090a90300700c0d143d58819584200144118240080701792419208a09030001e0070900100000d4017030901d590120310389518003401d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 28858234 1250 28856984 28857047
    0x2c030408010605060a0c0b0c0702060714060a0b01050702040b03030c0604110108011403101d070308070215090a0b0702010c0b010e040c0b09101404171b01020105040b01030f03 77
    0x18108440325003000300009a030312400d1002501c0385112240c002001e440282d400504d070700f5085608000417a07025410400e59601003416079006810a54200120300c0719a000e1441c00c01407250321914805060102c901104006402c9010b2824024421034a84143c0b03080703900d0400070303240e03541c00c80380c01c986107800c017810002d00c60f488040b039490004000c4400442d00400e650104a443c01003d0700402c10341c1046004d41c0c0040000c00340001d40c105842c00380c10a0360000f0400b0300c01840c041c0c1c0900307940f0780c005e1040160308640c00703c0405102c4020300c00040c2965441c141c1d40e0460b2040cbd015180e6510140c030040706d02c48011500185041c50030340010074100088910248207601c00d944207030b2441d84aa115a00a000c0c0095941d0701c29102e00116000d03512920b1440f40360550000454107050f110804440402e40c00f1913007558690150f501064030f44014413494010754000c1c0000c201d1400d0680310500210014080941040da03641c040d1010544180c0b00d41d40c1c01800900040c107400c615030310 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 28859484 1250 28858234 28858237
    0x50918120a030606020d0c060b0a0305030f1305040b100c0501020708130501020c0a030510150503010603081e03060306060402071118160203120a090804090c0909050c0c0a062c03 78
    0x1c1c20001a141200100e10b01e400002d103540048480d4031204030344642565000040c02a81c0040ea400412070b500c00000140100050b019206502c45234030349036100217101101e16091a48070512403820601f00021a48800404c3c031030380c0c201894202d45d0250142001c5000e40300b0002e0050480800248000614030090408020340e8400d80c2aa01101d842d1002c200b542c3c412404090b0030303500500568440c1da0301550010312952510702000003550fa407000042e003101d106074000d481000d000940000b902c2d90306c1445101082c404103042e400c6041c00d4000c00c0d0b035240010302450046600103040d00074400100b04103111030034020500012a1644480c01141801c1510340b0114443e28a0070350700c1a034008429500001000150004113641d038101d101c0242680c040c080d600d00310108801300c0c118540b0301901c0c0d405803154846603046854240a030003107483c000c02c80300a5074410b00044402d400042042c40344e541e006280405c0c9400342c620464903982c081d0020f0310303400d40034a030710030b00c1140c0200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 28860734 1250 28859484 28859497
    0xf030a14040b070e0a0302030709050603010e0d0203070b04060603080a0309060b120a120c080d020903070e0114090a0e01060e040204050f01050d0305070c05060703030e061501050405091812 83
    0x4000303100240180d402540c2a42058a000308444800d5001074000c502c2000c80c1c241c0386100800c184100c55594022a00b0301d051500250103043c2c8031420840c041c2800d002d0300820a1145000f802c40d14180c03d8001e460b03015011008042c42c07600780c08502401446d80299000c0d54004041c3c07503441248000240c010314040d08203e401c10308001d40e030300c0745161066101300c0d020b000c0800341010001d2982c0d240340e12060b0140d500300b401102e10340c5002003602c131000780403a44028031006940d110004205403074800154442c3c40f00c901100018010403a030075106040b41203040c0c03900b8041e41c55800c48030b0060310304207449101645c60074400280300030500c0f21180c00307a8003d580410064403101d1720120729410074080c1c1a00102c1d1440900c0001e03101d0402803e40c9800340044e115443e40b5400000d9440e800101c05030f002923221540018805002d215141d0414444044140b4422045001034100d000d00d00c1a5803050b490680012030540d0a0021905070a801409841d00500341c2235525140d43c1115 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 28861984 1250 28860734 28860751
    0x71e03050405070b040812030c07050601120c05030d09060f1e020c0a050618010c050102041d0403020f01060807060509040209040501120b0c04031a040f0c03030906030b0901050d030f0507080f03 85
    0x10000842e130240c102110251110000a00051417031036021071419800904030200d0988104100008618144607a034040c3c20101c00d841901035040c1414404640075400c8180304e82c006e2000012456048440501100e00f00c0c18400c8002d50138841c00e0396215402d5406100789609a1440041d0315804a110b0050b1901201e40038689503c82c0d0a0190502594803440100074a1107600c4510707602600042107041e01c59400545015205c8038000165500c0341d00d54221030040e481403004158040c04165900e03441240204030f110b00d0b0156440d96817101e40f04080501400040134905070300c69404881800b400640b041c44156984d502c01049101414002e84842180c070012408a845100844041325040f03a007501756148a542e41c4295104060001c4590040d107126070380c00a04080c5a0800850181d111141207900d8442d014055031040c1c00c0151059148500601c107a42d00e59588602031500761134000c41e5100c01e1042541d03188034100018144000200b034103030744c03007500000540c4103000d00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 28863234 1250 28861984 28861993
    0x3060f14090103020603100b07150509010207020108040b07230c010b0105030405070b030a0b09041b05010306080a06020703091e0f050f0f0d0203100f02070b09030306030304030605071e03050405 85
    0x803502450111801000303055400300074240100050b00d0020042c1d500008044101d5600e90760f1010303606541d500901044034101103440c680d101c6280507116217a404041030000358a000210750008051060040c001003030039000601203510244203400d400036195624600c0905504414400a01d035000f030300c0400040c1d070805409620342d510035415603002c2c81e44034004010715410300c01d0340540d43c0c00c010612520f155031503641305c40030750f2801285401240a13801c2d4106614603040b5142458172180c000d00e05040c2403403410002d1302400a00c440c21542c0103c0016110301c00f500d012111a00c0f280e1112045100080c004454180030b034a17140110f982186025000696540901121200c1502c03120780c000600b01e540c0c5020304100c014040014401400d0320f1160340030340401c1c000c641045e000756070b40c5540801c1000411504910740c98000920400440c1103107410400240d0f40c1c800c50100609950300c8401140d201400340b1080b0034440c0c00401300c010400036404009006100454040d4ac05115 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 28864484 1250 28863234 28863239
    0x30d0e0a020a271e060308030708010b040b090105030c0c0601030c080115060509040f09060213030b18030912070305030301120506070e130908090402040902030402030d05030702060402042a03060f 86
    0x10451401c8491000035040380b031103d04681c40006000241c40160801310030064942ca0424920031100510300c14500180c9900b0564801801520160058890f1410410007402110301101c00d0703503401c890900c1c0060b80ca81e1a1041600f05029407502100a80b080800210400ca0300601d090190b40c0e001c00200000040001025040da000b84258008140104010340c0b80d070078070741c01c01100e481c0c920901003584509139075100201c0c0e00165804140c0c134143e5405004100030b00c8400c40d007050542c20f040d0502d1a0080d0520744910464007140d1084036003160414a90070280b00c200011034026003035a850350380d110700035240c1c0320441c0c0d01141e19004031000a443c3d24040e0505502c904405001c03416100c0703450404000038082180b055079070303035400d0043c480180d480d0b00040000e085400000340e12802c0c20300c10b15140c552654000ca003030203010f10400c01d40950024070380d60712070340444010820001c1007480c0108103107015001c264010001090ba2203058040d04000125290b05410b4840305a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 28865734 1250 28864484 28864499
    0x203090d0327140d0305090d0206011406070f080304030302191e140c03160b07020d120507030f0504060b121207060c0e060406020a0203190203100e030d0e0a020a 71
    0xc40003044800c1c0c401e00c0a5001560070076408080540703e100b0200700c080c000403810290b14203503203000d60f14006621841000a20201804280e0042a10340000e10655040c0807051200c60f06110b644c1d030140b0800700395542132204100c4021050350700020741965a042c5030500601940c06682c00b1051541d80354008000c0c82d100304000e07640c00107980b00002c480400c003001240c005c28003a440614545040c0700060640f0018001441c4d204088003030984010401d15040394003480042c580e006642101031030b03000340768100400c5265038449040c0003406940f209400c3c2c00800301c1b000c000213600e207803204100c10070000303500605480320120751442c000281e0001c0e2642d941d4890900e20a0300c070003070045c0c9001400682080180070034074102400244c0007000400d00603000b40d0b10900042e07014940600a40c2028030940b090841119803030001e00300d0f160003003507460541003403102c40580c1d50400800c0596080c03043d64412400c0d407074148051801e08000c20307603a010844040e4484d1480200009a00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 28866984 1250 28865734 28865741
    0x40605060306090a050405030d0e160f120305070c1a130510020a0b060d0f0503130504150b1c02031602011103150d14100606260c0d090b09010203090d03 67
    0x24030004000410765540c0c204c40601a0001920840f00d502c02800302d504580c5850080c0c003080b6041c60002c240e050703000c101000d01c040d0150701c0082245081107040c000f50750218075800010f03030135081580c0d54040a10382107072680d00f20341c80741c0c4288400010201582c91860000c0400f51203031b015103c03c0070f8481e001c1010029014490a01592007454104001107210a03801c0e0f00c03403401018450481c0050b1100354450340c00e0320049586800000e0060748203840604500c1c042d050940b020041c222800010010305450b80c000e0741c080d85000f05444040d64400c40d490100000b03030000030b54980c141504601d00c20710b8400d020002550030480c0c060308580300e13081600d102e482c11100341070f1803915080a01c0340c081c0705442c0035581060703910b10b00010004204100b1490a41c803510016115182c82d03402858a407100c01544000d09015400780841640e00c00043d070030490702c015039540c8441c0308102500500380c0000080c0380c2030101c03042000365041940910301c11181a03068640459916600b00d045 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 28868234 1250 28866984 28866991
    0x7030b0f0a060801061103070210050c060906070e1e12010c020c04050f01030f02030f010509070e09060402090a0513020d080315190306020a110a0501050412030c05090f061204050c0406050603 84
    0x740f050001044032034420804900311307a40402c04e49203800d0340c5801003005410009048404135000250441401d0820001d0319440035030f01c0050844c905125100038083c0056003080c1d03100340d030001c8011005985480350001e0030f9000a041c601f40c54114400b1034040c210010321030015016001d8202c840741081c0c002d403072041002881d04502c0741e085a413481d01c0c2042025042c0d03054820381070500b0060000340301e0380380104281c1008015041c5000e060f051040002042c80c680c40d0840b405100058456a0105030455540d810110386962240a814041c0c0c1e0001750180d40300c828410100b090055600042d800307002406d107061f4500c200f0000b4840c0c00c2042050350b401c0d81e50b00c4001000810003940c050503036038000740b80040c03052190700a0681b80034400b54058400340d6407401488200042101c103080e192000d801d050000258081c0041e100d07025078040c3c01c0c010114103140b00002e070f07140001c40d580ba80809291034401c0c1080d0608a968603140c001941c0114646540880c413803070100142c078803 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 28869484 1250 28868234 28868237
    0x103110901080a0c020f03040b12010b070b0414010b060708120105010201060807030f03020109020d1209060e10030e0c03061906061d0105070201090801020a12151202060c031207030b0f0a06 83
    0x4281d21000f401c0c00c001c02030960a18214002c2c000f003071080320410300090000701000b050740da0300c500445400c90341c1c64006031b0001c200b02e101001034500007400c80b402d807036000d0340240c2c0000d84000029285405400303c4025103a00043c00941c03802000500c4010f0840144601500b183c280c0e00e490069088034640d02072584298040b1508000003102d0301c102c42c1030f55100e44004642c030002d507400b03d41082c07600d060444132245500d0f0a010140d50181c1100020419460324900541b1300b003000c03a040a54505001d8105900d40c05107208029003044110301646001c0c00b250503a151810781c0486030b0142000c0d502d02582809030004089110b00140d118907640181040c0b1410303900c80041d9016400034804905003c03507580e00081c030341c00c00e10280c020100780d0f03150000303034204412281c011030b160880c0091048000131002e002c1100300c000815041541699500d58410b58155030603e1405110031640f0000d00d11010401400e9064000b02900001580c040c075070b1071000c03010020031810308c1c000d010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 28870734 1250 28869484 28869497
    0x30903200301060b0c0d090315090804030f0302070f080705010206070509130606030b030c0d0803041112160302010f0203030702100c03090821100e070f0e030604110103110901 77
    0x411000c8208018440a020800500e140c1860110b801d4a030b03641d226582c1c0c82e101141c0044604410f10030961501c5940c9444034500341540c0e1100740c444c00e14141c403101e2594403030101c420040740c3e41c1158051500a804001d010000d450b000795a0750b0207004040b80c412091800040c8903900060140903110141c0140031195142c240858064001d02d6143d80d102c04010600d41c4c0c00c1d891031142c0390291500740d40216800801805252800001c000c0c0c150160307040c810908041021003056940180d8815048601c0d001020000381403248040503020b00f40c01441d5504100410100354581124400c3c0c80d104e01798448040240d03100c1c0401c403203107000b40c0c0180e000000d0a0081c1c0c0c0c0203404c0e4018505001072440f285481e0b0030140e40000070494101000484005611400c4100700d9501c00b070b4031070480c043c41d0b00346a0100600c14028042c01c0600403409000b2a42c42d0040c070802e14400d801030102c810301d00c1c1900b002d10541c49006152400729140503507582007035408104941c955103040e1100c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 28871984 1250 28870734 28870739
    0x1110c0a02060a090509070c05010507020a020a050607030201021b01050106031404030e01030c090b0d060f08010204120305090a03021012110903070e0a14010608010801060501030903090b220b1c05040309 89
    0x780c1c0d03500c680c07401c40800424800c0460360381e80c6c2c1c100803400360100d0364544007910020b2800301c1c210366020b0220419580310420b600010390380c0d001c0704015100144c981a4440320380d881e043e03000e8090840d500014440e014030200c1c5001c01544098100d4080f41c3d4180000a64114007460b000c0342510007400249010110301e1565010b07811409102209180c500c6600b0394480410301342e500403c00708004951220420040300e842e43c5150b5001d00b0101d0003c5240c549040d50360700e0b051002990040c04c0c007501080422441d921200000d00075600a0101c0b00c41405450000380b00c4008400c100302d0880c9404403002c0d541c3c49480907599400b1014004001690404088000b003500080030100041e890700c00d81992117205046840c004e0259071140300c2a941450205800d64100350801d80c105454605001c002c82d9211001904840d12007012a644000074410b030102560b1019800c4400c064542001a6011100b1b00401040540c500700e6520011344003592800e40780182c5015000134002c1406 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 28873234 1250 28871984 28871989
    0x40605090d050a02130204290406110109050319180b0a030f020c10050402010917031602011101061401120509030708090a0e070c020103050a1404080a031107060204030501110c0a02 79
    0x2030700040d005000315102ca020b00d900003410360340c0b40e044525503550041400c00000c1900e0307091040e11408203140c4000b100c82e170620501d4a0045126072802c11924078002d1003442c80039841901c0803604241038a50351140d240580c0c0c1d041c040460170f000084e404160480344111500c5105041d165058846c0380f810701c68880c11000f17001a000c1d059440da17420000c1079007050342002002620950b0000104062415000141c25001140d00c4500802e480308034650668201004442403404000d40c14030071200140012240042d012520307207581c1d071a107840800c403600340320100035940109a0300c81d01414407111810040c0c44065400d036040742d2051128400003134009005c0e01510002612614085a4801ca404483d940a86414000c50341807040041076580c18052150b02004d5100c05002c002d00442d40d42c4408a0000d0015103454004224018081c1c80f80d00a5048000d18086098858a250811000035401807008440644ca4103118421120b19003041d00c682e200c1c8003000d8103213080342e60203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 28874484 1250 28873234 28873249
    0xf0e1305060112020301260a030516031101090c0e06010314060607080f0406090612050403020d0804021311030603010b04111e070204050901050603010605090c0a050705120307020a0b010b04060509 86
    0x1440d041c01103207503d1240390384452002c0c6009200301030100d11031310705034580e03a42d14180320650007059801007486c500109400c402150108180180e07410b000100b541401c880e403020520055006500384280002846000b8581c081a5034080b03840c80002d444807001034084900f100f1210980c040e20f040040c5461070000c01a220613806005420300d0402070203071040965000c1e40000000c542c07040310034013000758018064180601444001c100f941000e44000c1e50f142c2e401c000c02070810a501c0c2c0040c007103403184114505d0040e0620000e01511250fa0405030481d001102d0640c007a40c6001c82240701481c0070300070f030314030160b03164081450803145c1c41c80f555102d46c00c8071207050411800c101110040c4c070b0700d205241c0304a00170400090f0500380f010401d82500c140e544080d1281409400b031000c80d859140442da1013182c1418102d81d11002c07468803034203224070404c5110b91481c0110422035403036004a2031855883c41001030040f2a80c0b0fa00700800c250185016880001c3d5040c880c0b00081d0608a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 28875734 1250 28874484 28874491
    0x18030605090c030102070c030303151a070510060602011a0a060806010503090a02150403031d1c03020a05120304020a060f080a0c0e0d060605031509060402061608030c0304030f0e1305 80
    0x1c1555141c502040109003641e21074036049622117808401042416410310803805540040800c0502c298a4042070110441c0400d680c61404c120000c1c81408100e820001e400c40d80c02417940c1400841d0307039004068002c18a0381560000750b9a507180003c002d103044003095058800945480c080c0b43c0b58000111540d0b080280b46440b00e101364a440d40150742d8280841140180b0003421a03511030552134011301700c8540d484c4510150305070781540c0800c0e54842903050300403003080f620144400510f044c1245410100c0002410b14055800c2601c00c0303180b00303401544070301c0c029580000000c0e84c030181150710015001e00c0d140080d1003c0c003c40d09031a81c07a04400001c4045281142741c80d040c810010740c0c80341c018041150407507030b51b5408015a05091007a0305980c420558144110710700121026251180144001d100e00d0700000d0036600303811482088140345400142d281d4603803502c041c5c9200d007a4000c0d242038001c5114850340c0c0001c3c030700c05c014a03400340714090712494600d000c141c0a140070f400c01a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 28876984 1250 28875734 28875751
    0x209090a1d1615020c090402060d110301030b01030209070503010e0c070f050d080108100c05120c0f0a02010e0105100b0a0f030f0e030d060906050121061203020607020c0118030605 79
    0x780c0c0090151904000410841440c000524061850441d942e4012560072076241c00b503420001e404809651002e46c050380c0303d50180e074040c0d624580080408000c25950680502c1100b001c0000700500c850f800c2500e041e24825540307407507940ca0308441a17071140070900c00c4810b0042c42c1000204220341c4500031340b01c228890840d9401000c001d80d01d2030300b441a550b041300f000804400040145010411010031002404241040b40100b10000142144682110280e1860302c000103c0c10302031a4000702c0c1d0001141803003140d00c450403c80000c4c060584403990540d1503003000042180750443c402280102c402c0c00080e540341c850b0010307007940e000c90b44084100515503102c2030309101c0d501e240900345072003000d0400346540b200f100c19850300715502d94209101e0039103444400c0c00720b079030030600803910700d10641403220341c030020b00095034045d0282c1e80021004040c2090fa5100300f580002c3c2d118010480c0c0d07001e689900559400440705413811242030844101e032580200013041c010b601c07942e0400c080c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 28878234 1250 28876984 28877021
    0x140a0905060a0f11040603140c1905091c0803011d0c07020409111c050601090605060901200a0303020d0c0f0f230403080a080106020a02060d1a0a0312020f010209090a 73
    0x4080d44c400c0d19082070740b100020945681d084074140d41d5007204242d00c414090142c5003440078140003500740c250100180824820000740b020702e5591100301c84407580503101e0200011105501e4070302c1040c1c0013072013001d258400032240804824241c0403d0741c481d14003c11003034101000c58082001030310b007103903090390458542e00407800c0d1034460400120702c40c1f204d9421910307003912510340305184c124140e014211407490420103100c0783e03458404465200d4802d2034450b0401030440008a200700546c5201c48180c4035031607070a410941c00d034018113440498410100100041150140d614410303000e40b010008004500c46042203002d6085281c1400b06052a41c583d441450400350659010350010354014034003140c01038046038881c0049026140300d1020300b8800c030b6150f000c6a0b06004008446940640b03941c1d901c102010960800c2c0d018460040c800407145603241016050521003084203030060203502c10b01c881007003050003143c0c8590b03000b800102d520780e180ea001000501c18100b610a400c0391 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 28879484 1250 28878234 28878251
    0x16030902030f0106080f0309030c060c120a09061202030402030718151206050112030804020d0602090301020a0f0305060406210503040305150f13080a0f1110140a0905060a0f 76
    0x504004030b000501c0b1110001401d40d0501c541d091070003404200c64000340c1e00030000224161070200d1680c4003d4004d5501075121070911201030b0600e51500b10b040240301020881125040d03002c0c01100807100d0304c0d182c0e482000c0d1818443c8040e07101c02c641c042d416501a6808010200c51214040281d0301032180000e00c121070603841c11941c07503080d07000300400b01e08481d40d0b00c00e000c10362191138010701d42140d000c4c800d40801d80c0e000c2e04000004002a101d2801071081c01c003444542c0d0121460000010000c56444003c2c44c0d0141c440b408080c51440003d2030940010210b0401d40b24800640715036204000748109500c01c0d01d06640b00604080351240418800000000c40c00c12810012a1000940c041c040ca800401c03190360800c001d11000041a00b5001300f4041070340c01c02180d00c01c00c90b83c5049149296003882c1500c216048942e07542c543d20880300c002040d10000d0f40213440c03c8446020b08070803a100c00c41e0034420340b1b0041d0b401809540006c001308602d9981c6038020b80a02210003001715040c1e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 28880734 1250 28879484 28879489
    0x51603090b040f030c09050105090c0708070c0b07060608120d0e0c0a03080d0c05070f0807030c02060f0403060b0a0501050406120902060712020618030910020709020d061e0b0316030902 81
    0x4000354080911545610424810002d1507071703645016140100c0200881c1d850000018050381004c0d20003150040006490800d0141d40000c4540c01c0e5000b803815402d0303176680c40030f46016511502c8141c1384a07142c00b1011a60758004034100700007007401c0c44007606180031041e04030300400314880403e80503c1642c00d2042103881d00002e01d80154001c3c1000c1d5182c0f9070707683c014401c0d182040075000400c08100405c800040b080601e5032601600802965101c84207032800b07543c0e51030000000780d0f2020000c01c00d140401d00e101c00410a4910525003400300220780020303c00e9a0b00d00e401283c0c0826414030040c0005446000b00346c00c8802d46c014003041441032a00452641d5021803070071341d90b1500c034a00c0560b605404100c4c031600700400440260103884a4070819489020703280409205a00048150050510030040e00c409050005401c40d03643c1600f4104000800081c4501d142d03108041c80d8895950982c0f004400c00c44040038032051840e624040a203584050701410101410783e60124100580c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 28881984 1250 28880734 28880737
    0x60d110f060c0607030504140706090e040f060912020d020c0307051018090c0e030a1505070507021c02030705010503010b040620010903020c0301060b040b12060d020603090615060703051603090b 85
    0x2c0684d07440c0050941494240078240c1c500030107003a1400d030f1103030604110792640040071508441c10500351500c207488516140881c10308010010300031a0401013400248401c00000030000c00b165021200310310040301c01131707031030341c0c0e02c0c3c820030f42c0c1500607031020081070414058500400c02ea903d400321488000d4507140b40c80c3c00e22078100f000600c0c1d0300d00030061b10381d030407110041000740124010305009125039144155900c0c100c85c1135261546a0020540017401182507e050340c0d4010244584480c1100e280c400507000580d041e8864801e034600010700b9401207045906803061551030515003070800c04150344950030400c040103410242c5441c440802e400b842100743d918440d5004e4407002c0c24800400d820340d01c0540110071800c1c03040008211b06024101118291503049602108643e9040c00080e004030401c60b002e500000000308201006801095076845034000443c0150f85100300301c00c0c08000d001b2498000c01042041000a184014000c5910201031081c54a255519215180304203203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 28883234 1250 28881984 28881991
    0xf061203020a02040515060304030c02060f0a0c05010506010c031b0201020703080f0a0201050601080112020409050312040b04030908030901080109051b0d0608010605040c0e01050a090b120a05060d110f060c06 91
    0x140c208005000031031030301740a0030750045400310040c46854107200016019120280000303050004d521050700c01c5440e00c60548851001202e141c82d10341120f1680580030311513844c4100d90715403070000003844035805200091606501507540c0002008061000c0c107004054486c1a810340c410f125002002600d148014100951032144030381d15086007100c06401d460014040e141407001c01e60051117030840702100e10040e00d404540100300c804240c10518298800c161656040002c1c0c04104400d11082c001054000c0b442a40c2d10401603540e1034940b81c883c050451800d002410304401081b0b00c401ea600080e4005c1402c2044e000d0011b2641c142408990080030f900c045142c65907030401130035400f84166001044195414071601d1803218004280c5060704010f0f5051043c08034070b0f1a54240b084600c400a050004c900d1655588881c10300e00c0c82940490b0f5990000b4204000a0301e0385c24800c21072210194480c2a22800c2c0701c000007044400c1c02030500c03070f6812100a0207400003841040090710300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 28884484 1250 28883234 28883237
    0x5090604020105280c02190602100f11040b0702010f030c1707021e1c1b0308090a060f05010302090711070302040f0902091e07050c1009110d050106090e0f0601090f061203 75
    0xd03105c030f5a1060050319004240220360303141d4103841c100241500441e450075401c400c07040000d5090703542c100c2500288030351008511220700c0030a0100321043c12100400c1a907000740c07585a04480160400c8050300c4c20b0b4600103000500c5540c46403c6281010022a0855070b40e005880c035403c1040c4100d4566200700d0341140b096800030448074000c001c280040500302d02149898540d00000006038000b9500c10350009040250b620006a0504000d00004c0100b69010100344900c81e00da500c4036000d00802e0209a2140b1101004110050300071814520070040040c080c014640ca141c00700f20042207502c4070100729a490340401001680d81d001d00318416802c0010705d0503061550341c5000302c0030100828203800e001d400c008441e17034807100042c1510044a4084089007810241c9409107151010000c0c05411801082c80b4200700081900010142e0314001c9041148148221169541d810085017000e440c2d0400c01c0180410841d0f40c01c100c00081c408035011901c40c2d070350b114241c10042c28090a50 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 28885734 1250 28884484 28884497
    0x207051501090b03010204060203030c03091c0201050a050f130f1b03050a0519020d140a0b04030509010206090118020d020d0807030c0605071706120708070603020d0f0509060402010528 81
    0x3141d0311441014045030f400e500071402d2504040c0c0c060b41d207200c0030740a103400200220010b8601d81c8100a2055084e0314601c0d0101040c0007100080c0c080e000c1941c4260550b8104000181038620704840f50741300d0078800d03400e00c20580b883d0310340036101d2890038000c0d10042c1c002c10101d000515003c68403002544104010980400d45091242c100480980c0e031040c0c6c44a0486420301580d11400c00c80e00c10350b04202840514203680340f4852400320b08d02c0008100783c60500c200700905800c1806856401d00c00e0b0250382e46503840e801c0f0a030803200d00030780c02c012001c640310340f030b02c00b41c1400d008030f440796407028009102200e150f440307020094108000880014451016003002c001c0e623401060b4001145090840045101e00c1c5a001c5000009043c02d0003400c0540803071100041c100a0341000f40a1241551400e03500c03980f0003400307580403088075100345041c0004508148254402c240c400c40034180502255103890707004607842e44c80541810b14241c650103480c00e10517035144050400d899a6141c22 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 28886984 1250 28885734 28885739
    0x120e10020f12010801060b0f030711010c0917060610030e0109081305011403240609090412020708030319110f0406030c0818060103031b05070806010503070b0414130207051501 77
    0x510b060a050b001080640d050442c108442d80843c41910700c11000003100b543c40ea03850380003c0360301c803c000961200e25070901d03820950580c0c10081d8101555601c010780c0d4805020320306203035600d00d000e0b100e42e40c0001340c048001000510951207802d0780a60800081403429107a10740074030315040030402400e510400041005036680101c0c290b1554410521300c9030544c503011108080381c603542002d20b8105080400c60080d00d0350f40070125040130304001e04407486070a103818040d0030002d02070160300140c4905c0c40701080b42c2200109a034800e034022002e903083c550024181d84060881001195540308007402616003041108000c0c01c098007040e540041c0c1403034078000082000b44081d00803c03156094841454801c103002c10039606607901410003c03615070081c1d1295449810b601c0001d0031038000e0703030404a29510082101e03030403910100d0032220000e45501d00308240b0710803885031010440e043c050900c0d59090243d038908174141c04040042c10607a107910b6450030400d151080562800d4040d005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 28888234 1250 28886984 28887007
    0x40605011d01031109060a030206120412020c130c0509090103050c030d0c02011e051905070501050903090306040b07090b04150306080706050f0c0f0f0609060609040201120e10020f 79
    0x120103401c07002052070815545140c0b00c2000d4051151221070040b4556400241a80c580c411400000c5a0203040c89a503280248c041002401096401300e6001078400303841c0d01b015200141207601e4000007400402251f101d18480002468440d0010080c0700c0c017800101101ea495054950085001d003020702070540c481400c241c280482d1a4080003840070000d201405030b68440104044070f05100c3c504a5642c1c92040260345038020380f503034500a00c42c034842076030f07603107500c440a000310601c9034009008503199000826241d000d810302e0750f0380590141c000200404e0000a14680090960815160303003500c980909246900c15080b0041c04030380407031100611039151040e50014003510000d40350860800c800140107208403010300c0d1256502003640308540d8003d114105d0103a90b00d10460304050024510a03403180c100704c0d04500c850185d40c00241d10b80c140f082c0010701c0765505a541a81a8201c660321030f0082024440c407005c0e41c403c095040c0c449410130710041c10103400b031000705902c07040603204 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 28889484 1250 28888234 28888259
    0x12060405010b030a1502090301090501060b040e18030702011b060623010807080106110c1206010303122309032109070f15030b030a06020307030605040c0f0e0103050901110304060501 80
    0x10840c000d038411801c28001c43c5c41c40d65030800c00d10f00928050ba07101a0f42d00003d0140000c010040d1065181600018280c3c031103200910480310b6140321402c2c82d0b6a8441c070340c068804020711080c0359800c104280001584034809030f429001c1d031a0860407409181e911000100c6521740c00c480c80c0b00c000c004030035076999104001626200400d00e401681d510304001d000780700c40700c184101320601104980409000905000c11100d0020190162080e4024115019500ca070300788000e0f40850600b03019020b4022603405418581008203000d1900d80c41441184c2810100041036041140018010036040010520840c80e2890381c076014050182011180c1c1030a0150a9016400d0308180c15410000910305105606c0103581c0c41c14005412180800840c0c01d0400c084801031040b4400810019490780680c41a010b4542c10354041106000c3d81d03a041d2a078580340c0c140c01010030f009045200c115031007604900e40c8481c3c2c1c0b03000481c3c80e00b88100600b40c103400a0700d048411544490040c0509a4540c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 28890734 1250 28889484 28889501
    0xb030a0506040209030a0b0601021009150513050304030809010c050f07051302162603070c03020111030606070b150d060f1505060f0c0c060c0c09010503160b090d021206040501 77
    0x4400314582444d0400090b40c0f03144103180100103d0a00d000540306a00901c903200066038520024080c816441c4ac200032198400007201f440585000082060003440003080a5680c1c0d02c00001c525040c255100c600711904000c1040e4100402c0700810310000390103018906403030000c00001c02085050204212041c01d02c3da0340610490710504c030856030103071420752124105412001880b298400590302c0f0790b4015030a40c041c104480000b09221202e54424814042ca82c06a8001c100034141c1280000c045e01c07042d80c00b680d1148041c09000081403458100c183c1103d09200d958020301e88c3c9c000816006080700d041075031600c2c0c1d2002d0340e05d00100580a401d04408010061580c0f4605101c001842402a43c42512048402040d041d416010400402030341950040c58151103003194180d0aa80d0080200341d14091441080002103508002aaa2805105500c42400b042e81131031407513402500b003020140e500c0380d402c1321030501680303034070000f002101445409040d29180a040081c00c0d6000d20 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 28891984 1250 28890734 28890739
    0x105060f09060c0307060507110d05030c040b030901060512010c0e03070b03010b070602040504090c0312021605120709050c0405090c040503060606030402180c13090b06070f020114040b030a0506 85
    0x20003500284805400031600011011141d05480d000b1045400d0700d54000ca09001300342528110030301144d036411054400d01090311004031141c410342c1038000c070f8040c0000e079000c014a480a010500111180b000a1039219910304000034541d65642d000aa14425980d0364213200e954602c0044501e03548038854aa450784190000e004251500302d004140b8441442451064900400d03018200705864041f0340082800910900c4092414203150701c000a8070b10044484100b22901d0250203800402d00300511944041c00c01c4d241481c140c284011510043e07213189090080c44d0700424010b80310320803a030050b0740300c80d045500c450a100501c0100e08026280d804454000c1c40100030b00ea4000030303c1540860180c84040d00c03030300c9a10110300f00d03c101d42d503008251544034041008580c0300801504800920b801101360b51540e80000c0d0040340c20444101e03800000406c030410104824180ca0301c40c90384185400c03003074481e026203c1f8000e0303000f903002484404400401e2007a80a02409400c2c0c216004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 28893234 1250 28891984 28891987
    0x80a022e0902060c0604030306090e0d08012105071202210712080702130c02060615160507050a120c0f050121020d020a051308060417030a020d06060215010506 70
    0x9600c0340d1184811080080a416070301e0741d44040864460030140d80d00309445000f00c842604080c6000307000b42100b400388450b01d40c03030520414407443c40043ca0b185441199100c2c41f40303d0b42031030260540111b0036802c00d600403002c04460341c00102c0400c41000285543c9101c410510501c2c030420624034642c1840800b01c42d08042080390001c00031564804440f0020b800d0309100780070b443c00c0c1400b0300858030040c2d0302c0120380d030051000c0c424940220765404620b82c2550007070b0703840404110181010f240e612001e110700f0301101000018082580d80d02600481c100d411031039070b170400182546005d0300114842c90b000e481c054100b003001c1100c90041c10300c9580451405080500082c481c03000400d4503511280311981c0320007100d0303c4d07504441c5225812002595241c0314198090005c4c0c0c88100c90f1081070500e20400204000302047c1d86000d5507002c1500024404e504034800ca80f45c0010308012521503003000100f1500600303119280c0201615009424200314a405c4403c05640503407110f03006040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 28894484 1250 28893234 28893283
    0x501050a08060f0a0c020c0406090507091703090415050d050a1502030f06010302090a08060c070c090b010507030807090509040c03050105060103150b0a05041a070b070315032004050103080a02 84
    0x50f15250158040c0d00c0b540005404000440224501460300c82c0f42d40d0414513207400440c440304240c20440c410551034a441485030364403a80001032014681101003d5042405400303414542a045000c00d00041949515600e40300e4002923810180458101c90360791002c486001084000c40c40c045504005034011811403400504511414000400071070400da400030304184a0740d02d0700325240180600c017080f91040d143c00b80c825012640900c1c02962042e40c22030b4000303146000c074061446101d4043e580e03641801c03200d540c190b9080303c0140c0501c081c04032445d40800c0c036864100c522441b0358050049140124698181142150b401806260406040c0700d0046625010800584100c8107040211682e88062580440395801250030103041c0140300c0c50303144844048100544412381c040c511801d40758807034500650440301650f06003088288902c0f010404030320880130951250a580031503006c2039010900207021076109800072280c40102007000001194100840860043c0e100c0c0115958034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 28895734 1250 28894484 28894501
    0x109020307060503091e03040f0f030c06110a05030703030203070f08070c02010f0e0d0503090a0f0e010b03060402070f030f0e010e060d0e0a0f0503040e0604090b04060b010315090501050a0806 84
    0x450300d0003150b052010000c0480c602203400c005540e0a1001d03001e1201c180d00b070789001141c81e58818403542035400110180852141041c0c58080704583e800007550310400c1c51300c40251803120103001203203001c5c00f6923484100403e100b40014443d40e4030940c0c0041c2e80303103061480505510b06404c1c500d0200654401040b840750742010403d591282c09080022181e8455007003203c401300c0b82e200f065049814136408900300b000000c0901041e9404403003103038038151a202c1d032411101c00740c850640e280d280b002c01000303200000380085070044000f500140c81c00c80310b522100d1511a00c00411000981c2d444034451425604c0342d5604810f030000d18090b040f1002c082c0008065001b085070700c40c0710715030300c55411030340d00c01c2080140000359110300e0180448003d414069202d400a10440a8500b450380004d44145043d204a45607980d1000518007140c80b00d458410081c10001602814960b42e50b00d05002d00140030b1030000104880540810340350b040c4810320140030504e0b0300420740d55000c10140300206 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 28896984 1250 28895734 28895743
    0x10b0a020a0609050c030f1c0806010207090e030f041205011a061c061505070b060406060f05070201090e13060f020304030f08100302040906020405041802061e120901061701090203 79
    0x720782026001c00d1181d02404c102c0d0a055680c0381c01030b4180b1a80202002d0400f011429490100c041c40001420f801c81d01c0341582c100008940c1c4500580005200780003603004d072780c440008040341c04101d81c103010140210f207940d64080d401003100c0400d0b2141c01c0302080300034040c504c01c8551020107402c2400c0c1200200780300e4014031101281908c0071003813100c58040240c4c8000e00038140701c240e08161801c1280091300d40da002c1e1030191540202c07140024400c0c2414000c2d84225005992210124003034000304484030303048502c0c12810407680c240f0014500c03480711045030140321003040104e60700240d468604112000e000d00e102c03d030f038018401c1002180c0c00900403030800082d428181c4250b0784440d10303440091540c1d00004c0d07125142222007400e001540e800717481070320402d460801548201d003407241c5280741c91038002075202e4410403100003000d800322600020340322010611400c0050b500c3d111000381ea000c030765030b8840d0381d9a00c90403c40d420020704000b180700394900081015440300c1c0c012035100e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 28898234 1250 28896984 28897003
    0x103021c0203030a0e0f030102030c0a09090902060306131b020715022404020a09050a06050406080f0d121e23010b0307030908070f030206010311060a0503130c030c060309020108010b0a02 82
    0xa014064070845c0003500c8182c1040c034000c1e0018008c43d81c92504040040b100e412050744400082d03254200458000004c0c828111104d40007405242191349050400c80003841005024400b02e407110302c08c40741c00c141c0c0460b4151001ca00e401800fa03d03070402545034031001c0002110030031544203059000d15108400581003070300d280100040080d566900100300d0b220f07400d6020005e25850401044584209548410b094590031101402155502c0021669541c50500c01340540e41000d40c18609040c000c07a0042c1040b1046103010540600040102c5051215500303000c09107a214a180d1031006510104482a5480014001c41c59410f00030100c03401c0c00700510300e809165807181c00100f4070100c141a2450207600c1145461a082589802921600284012030b104061001c01c11071500e01081929181240c0b95542c0e4115521500c8a21009500160544054801400100200d0303000c082220240ca0151404107140030148001400706c20143d0107224070800c24020000065804101a2003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 28899484 1250 28898234 28898237
    0x509010306020a0216030605010503070f05010e01080402041b0801030c15050403240203090d02011a030c0f12010207031110090314090a051c020f030102040303020601061b060c080103021c0203030a 86
    0x3183c40080c0402d80c940044510008500300e06503000004024264101905039403003030341a5402c1c1991502070507424031650140398080780c120a040d4100d5486499805d600500041c80403c011381d100c41c070081040c188845920010b108400140240035950760608001d10085400c407440480c03036100100f89001e41d0000820350242c00e03150703c100d40d0041245a40c50443d65004560f41d080c640c51003030f03966100507481e00140d400d09d40c41802c4004c0c0705809100c1c60b00c01074040c1030b03410003081c00c001e5100c0a00707280c00e9001ccc400c0032841442040902c0600715288c842c2d1200001d409541c4400c13803400301c25102c9851102d043c000004c2c0069400300e000d0300702944c003510645c2c403141c0c0000091601055504016045450280d07800390003645460490307550390007620703006041d411420a150a0303200d07501002d405030340302c58010000d4520070300740c800d0485808075901481c4103581e543c038810764528145d0040001d50b198018410340c030340b0f400c5d0b0030307008000d0b840e02042c6400d056010170303100c1c0150300c170120 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 28900734 1250 28899484 28899487
    0x90601050d0605030601090905010c1d0607080408030f0403030809060405150601030f140714130302060319022a0d0207060809070e0103150e07030b0606070606050d0302060718050901030602 83
    0x10a20700240c01800141c00014103440640da1a03405a038020640c540e802d0f1000c2d806e010f036001c401da000303600d00e02101c80740a44409091560900b806010b82c000a82110800030401c0002000341050002d03001c980600d0340055a698a1424014848800a0100d0545400c0542800001040010811001800c0b0722100302e003996503d006030020b140c4040c0075810f0b10b041c000c006a440ba4410241c5104202c6d03600c0741500419440d1a01e4003502400c40d2021a502c4101e0050000d803030300001450307002c54200400081d042c600925101640c01c40894414011940c0c60450711045200d071a99001c005c038200142621581d84c24000c0d0340d5100351103004188803d05002c5500804140300c241c000c0c06041c440120103503541d26010142445000e03100700024608070072040e0140740840c0780303000c503030f088071301344450b070711a10100442540045821202e0130f5440343c4c0091a6280c50034424201c40c081d40186c1414034100c00041c01e21003a84403000000f110fa05002e21445d42c402d08800d054030740044005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 28901984 1250 28900734 28900747
    0xa08040303060503030c060f16020c0603101a1309020a0e04090c090c052701090626090d110105160c0203010e060c0403030e01050a0503010e04020d0c18060e040209060105 75
    0x740c0052640c1c1d0845900342c000022580c1080c80c0000e0300b1800340d0b03421000b4010598811100415402e5a101c0c0c140c01078103d0321000a41d454200040e64010103842101d0110a0791410000381c050881003112078005030224581507a01c01c0f5820407001807154a40552925040d03000c001c00440113022030364405c0c0c0c0ea0b04441002d10003441c48005c05807060340000c2015100d4410041d0141d0084044085074600b1180e004407843d01800f50364041c0101a181d401840f0b00b4001c06841e00c07240340309500b0341c10012051001c075100ca20303000c1d00e000e584d0450117414808195080140039102924074542241c0c142003c0c003208250fa98800c011041d4030b4500041580b0591001a015001d41608030b000c510a500501c403c015009009100b2684207444d0f8190455000e03006613407500916002d01e0101d40c0601c010840c03800c08411155009100030003441082c91160b0321b030782c10000d440e00015142c5028a26080b03140d440741c400d61019180364100c2c46058586a400210501e4000301f40c14104000400d40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 28903234 1250 28901984 28901987
    0xf0f0e13090204051305060c07020307150210060303080412090f05040209121605090106090303021b0103020c0a03080615120112050a0501060303230a09090c0905061209010c080702030a080403 84
    0x18a000d0b42e0092080c003150a00001c101181100d030203054640f40180c4000c59012001c0100b102e0100d13a01030007411001d4980001615003051001307141303055000d00c4900b200740140e6482040042e44c17084d15581e4240c200b0b81840302250080c45004002e00040203c10320105244400d0007080368411a00565210202c40c08103910300d4420800d401c9921520010f810443c000307055400644800351040c1c016a07994030f41c2100c0108840c0300103070150700a8003100c5c007001003100501809070700605015280c042d690344070a241500c500c0c400d80005007084240900e03868414440b414445050405d607007841c8150460089028042c8034940708610031b50b0a610822500f80407a910903600301008004181d5681400340407001e900240c0074001200c441120044030100c8241c0300b445646560300c0511038102701e584001844174100c001300313000c04c40200240c01e030307130f144020201100d50803140c140d90f0400300006800d4800c3c0031120030a0207a050108200b443c0e001040d90030151445c6040519a101e0703040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 28904484 1250 28903234 28903241
    0xe030c152707050301140c031b04030b040c0501020706020d090e0402010306080f01050109110301080c130e0106061d0301050c030f04080d020403030302070506010e0903040905090c030601080d0f0f0e13 88
    0x1010020288800984007400841d00b242203c1080e03000744002e42440d801307051128800c55a0034607101c030501c08030f500c007100703a1201c1e851145440142481c182d165101c0541401040310f08030b0300b0995000c020700c010350b4180702c42c9005080e140010403c140f0f8200c405003017044030b4000d200207608087c000030300b56882900b040008246103800c1c0c409074946400850301803e82406240d015900b002d9007500125203020072a412640100003a0610f65040002c01500f049082106803140d80c0341e0b4001503146200303100703038802071005071034003441c0c84108440300421424046103c0d2090b458841000724bc0c10240c1c0c11031707600907142c0010b8070b49540d562030503101c540121000d175100284085800710415800d40c0c0140155030040d404c03905a81ea1341c051003e1407510448108440380c00600040200d1845500704503004103000303050301c5c00d02c0b541000bca8a0410f09030300194181d8000344401b984542c00900c41600c48120f450240001e402c1504040e241c403d0512482d40907261140e50315003102d0082d031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 28905734 1250 28904484 28904521
    0x21b062a0d0204030b040309050604030c06050a2c031504030503060d050a0501140103020906030604080405010c0525032604031401020c011505040b0d050d050304032304090e030c15 79
    0x7601107450303e880b03051035044141c2c111001c40100e06d0381d000c04500e82c5805816a0300f10f0381e01003032a04c1c0715402c100048803507400900c001c0c1c052090f824041e143e8441d0300208400c0f5070003006c0e00d00c00c014546a0405251580b0140044d841c000c4500c18800401d078450f00f141c0d4031400541d10110140c5091521a140c0668200082c00315441d00b20b8215900d82001c0d0090704a0b4000c841004ac3ea858030810180c4604007550000c0000408103c200311550285218840990181c408d580788142207a803020702610101c0e1aa00e1110900e020a00070801c0d01c55482c5492162405505183d106080c408800c6201c0c0303010252400c55560418001900b00350104c0c1c0402d0b9600c40240074096504070780b410242c4031401241d1040d8204203264032542807030000000c81940200050100c0c545011090b1280d0b48007601c1a0108440402d40482861481d055074070031140c001092680c0d54600043e5030100c0350614004280e070340080010f403407841d400041d07010141c1402c90070701c0116183c00c0100107528526a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 28906984 1250 28905734 28905757
    0x40201080402030312090303190c170606130b0903010509030703080c1e13031401090f06090f0804120203150105060901030c0201020408010e01020c010609020f071203060513021b062a 80
    0x9200300702e120355007c006103000c2d001000343c0300c00e05000c00c04003601381c0d60004c1820002071445040e00f100c0c83c003282c81450b0040c802500f41d6140140018a00c05040100c0c0c01c8580d00c0b00000403c041c540c02c013440388a9010803407030041d504180c06940d00801d4a00b000d440c00140c0c141c08140c10310480c4510300404540010112072959419036002c0c0c1900256080c8025070340c2e004ca05042c0841e0070018021030f82d106510206403124840a071b0f0740c14001307028415054444025210201000551303800007000681100da010b010443c9191040614044c141c1004212020b4440d0040045031149401c3e01c01404003401c000c504200810741c200d0080c0130350740c000c1140d0740c24683c4000c0f01100640c010414101890000c2c072000d900c840200081e841035012290109004201c0713035002c1014200541c03e070201074034001c20a195120001225000c1d05612a00ca00d45d000620f1080c0c04098140080e2060380301d80580400d203080240c901107a5403036600d5600a10074090800f4821050030f0483d500900003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 28908234 1250 28906984 28907017
    0x30c030f050a0b03331e0103051f020712030f0f06060906031406100c0602090301090305120f0601020d1b0c0801050405250b070201020109060911100c08030402010804020303 76
    0x840100c00c0a411010301c01ca010740941c500c0d80301c45503d140301d10f034070301700f10700e40d25009042588410101c0c030407000b065242c1510301d0341c0d903038641d40d9025040b040c029030080c2c1c01001200340341003281c850a8210101c43c903001344100401c00015015541c1d00d024003645081c0001e410742104409005080491420f011041c5465004905107402c00d2100e019100550f4041001410300718a0003900e00307041d18403a60044072a0340c0c40704000e1060a038104114420030000d401d109003080441d0175903c00ea03400300c0c08500c0c00f1429070545080000019400813030f44a890743c29003032050010f074503100001c2103481040404241000071851445550700c0c0c1c42e17485111264007980d2005000c2c002c00095030100c64902544100070321400c014258009a03085c02c00050300d01c0381c54051003041550290004038195500c0b0280040840c22911591440030701850302400401c0c418010403401030a900c0d040c006010340b00c12030b00301182680302134070380c8030340e083c2070040c025111800000c9c03841c0515078250543c0003030f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 28909484 1250 28908234 28908241
    0x13090203070b030a15050901051012020c0c0f06120a020c0304030c0803070204050906090607082e050109090603111207030b0a0c0206100503060a0b0609180402210d030c030f05 77
    0x284402944502e03004c420402004030f0346201e00100c0400b600c507040d40070369814018020f81ca01170290401540250401c030201d418030368441e200360f030005000d80c80150490518007105050200340c0740700303101c8101e40b000d1500c17500c0e000c2d04c41100c0c3c02801900925a001c101100454010801ca601442d0400010b44015a5030404590f40b0f9000c2c800883c01103041c0404103030a0031000640314090000140074241559403003404403950300c0000c280b4001d104042030b200040402141c25a41c0c00e01c141c6100340e80d024200b4001403c003500f554000507105190442c20400318005542016401000300c40e41e1b80000c4090320803628000442e000070304041104805d00c4606004d9a01805800b50f403a02070310941e54a41100100b0185544a650b4150304040b001454031200d950102515640080c822401e00d038890b40070429030100c121034500181026024041580345c80301400040140e001c001101a81c1d41c800c0094032003003107503080c0d07050545400c8140c0703006000342c00c40c40044c410900100003514 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 28910734 1250 28909484 28909499
    0x6080102090f060406080106030c0c2003010e060105010912080702040c050c010f02070206030a0e071a07031101051e0411090f0f07080601080601180504050408030f1509061309020307 80
    0x184040300d0380e4030400040003800c0c1c643c145038040d10201c03442601d40200c1d5a02e480c1d8181c0141c028442c2d240c00b000000c0100500080300c0981001d40d140310306034911484030400c000c0c14212502c26003000c0701c40c0c2c030680041205030b0340003008501303440075043c008102c585d0034a0480c5c8980516100254418100440300110301d81c800094000c80301c41c0d800a000850ba580c02e0300b4100d01c548180a5045502040018120540c0740c0001d90341450030812a00050396a40d540c56030100500031318640742d10300180e84001c0c140c0c444a00074034441200020003a03404c2c10741c0041780110490780000c00d001d00c1040020300f449004590000e0051002c1d114484514028031070074880c010131241c2500d104102c401240656100d0606640b0884041c0c40e181d24a842d21350054442408d00141603105c0d450600d40030445441e10b0161034042c80c0b14210103030311b034100003540d10408000242001175427400c0e005044450398a4038a116000102034031421010b258043c145800b9068007040a501403254602c0019401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 28911984 1250 28910734 28910737
    0x19090c030905100b0a0501051605010903020c01030e010e10050405070f150906170604020c0f0313030c0e07020a2006190306060908070902030618090c0102070506030f0a0908090406080102 82
    0x1c5125005a80e800d00c1d018400e0b8045a070801c056540009116600744440d50045004142c11440c1c5405204107015582c1c800d030035504042421001a00880d10514583d609400b844c0030409000009200404000562550303e411200007288026120f80105061140510990380504001003000c140d0315210100141070601401c40c0b500010203440d00020858400c4198865290300748640c08019107481c000c00029411004840170035004a0440b9a5080c030104020702001d02c1d280704819a2900c0d40c202078180c95902d030b11281c40481c240041141d1180d021a0941c1c01135441900340032898803140b6640d0200c5007002040d90040000110141246c009013141041440c2641e0144251600d4071406c42c0c90302014414581d0640c001581441580350030740155038460005006e0071944818480d0512086d0303401c0d1600511a00f1014600200d542d05105c0d801c0a0241552401d246041c103014280d04000f00410b6858403681c0c0300540c000300300c0c2010444200c040010300500a50791280030580c000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 28913234 1250 28911984 28912001
    0x12020a09080703050c090f0105010507020d1e03110c01080f220803010602100b041a0411090d0b0702010b03011404030c030c291b0313030e1c030807031a19090c03 71
    0x307a010400040c0c7d9600e81148000d0690380180d40f0360703090000f40d5080c03010301250f10b1011104100000c428410a2010480c03444540d0b0003a95a03590141c032040c443c608110f035500c0307014100b080010401802207220400284c1003080c040b841d21007004070080344580c81c289044001d1240600000000e18140c0c000781001d016250401d003040041d01c00d404110171118202603881403600001420b1001d46080d42c44041007290608507140360010340340026501c5950b035030040f1032031a130650034000d00b280d0903c10316455000a40081100440c808480710f030034074000b0401020030250128500c20140b24060b041550340d40f1022003640b11010942000786410940241e40030040c4040001c0c54a071403842104245207401d41c2d2051541d2181000c00030a44190356041d0103102d030000c01c411480c1ca40d0010720203801014654504100300a140040540300090304c1d60342014107061b407645052203410a036501c4c0010803180148807540149002950b21001d40c0208a40d5190020115040c2d4254000900 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 28914484 1250 28913234 28913239
    0x50708090411030f100303090b070309050301020a03090302070e04110409020303090904230303100e06061605010b10030b0915010201090602030405010c0906021501091112090109060b040204030312020a09080703050c 94
    0x1381c0d92541a054040140ca00c80580040c201200c10418200c411300201201030191600d1445c071601d50000c242664481c004d010002070369080c91304103050f8107003d19000b6050050a911b03141c24a40c4401d5482202c520780e4520499407410858110b540070001ca501190010f0203040c014605802d2003000b003c145100d00110800380e504552001d1000310407688600f24018441c45014146024000e100d00000c0403250040c40030400441d074404c01c2c03c90040201d1180b000400e000c5612818851042c8075040c0c0c07c4c0500d41800718020240e0307a4625065480b603502400005070502500040707024082851000e070a16100206210602074190000b504510031510b8410b0301c60399800c0220b0b912103030111100a01c501c00d03c0180061400c40d0003141508840328944d03401c18414040850440506903040c610b540e5448101408201031401340da80325030004c80c1c3c1182490b00d142c5015040245102c260907000b0380c0064100840c601401c480800f07400c060085079211910303032411a680e00a40c00d140c52 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 28915734 1250 28914484 28914511
    0x909190b010309020319030212070605011505090f09070203090a080115051801120302120309160501110a02040908070b0403090e130201170421030204050109080304060801030305070809041103 84
    0xc00e95009008080368154058010062030324219403c060b0940da580e4100d085010f00c0b0542c42200e284040506100c901480002805501d80101e4400f001c011124070420701c902444101d43c140d035414842140000d00b918480840d0395880d074202d0441c800e072000d80364070030705004020804440540c080c600401c41180d2500c1e482c2e40324400c114244c0c00c0354240c4d600309000500180f00c01402c0f1700c604400740e031081c01152006028000151681e400403107000f1540c0d480301070a1281103c0b03000203440100f42c2801c014154404802d50180c4404600744082d0003661a01002403c000104088440e1107030081008040ca040a150007810180d09108600c2060b15120204501081545c4255a5181d050b155100103103017001ca00c291040008209440f03101c48091013078001c0c00b0441c400c0c000f460050342d0042e9140d00b41400907042140c1504a209250b1050006001e61604610614103403501410010388990652030002c1d0544641c12000c3d42050030040000780e4150f00070007441c083e0b00c1c03862030707007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 28916984 1250 28915734 28915751
    0x60201020418020301031110050c060412031406060a18030203070603020c060a02090303041202040e0f0706091208031810090b040311010905060609070207030f0507030c0602070b040b0906090919 85
    0x400f80d01080c0400b4120342450b0241c08154540480c100ca6202a1800c1040c00c0c1a0501d280741c2c141001141c0580707201c41000b00d070301f203080e0f0700d031155816407085103061000d00d0414001142c0b1501644011009200d41d03444810420b0380c54609240041d5801802c0300c0441c0d0325908014082d412040040006110301d01c0854a5460303503000795420307840098001c2d42410314004211003240100381b000c0e41c04c60f5403140e000409640a102614010030b17120300400700d0340c0c64110b0082c080207183d40034808802440340e8160009140f20b080302c3d001106c10589003000648018244c1c180907212460240207840c03c44110100700444445030300c01c81c0070b80c5440301c407113041c94034090030382c1d198510041c00b81c0c004000180440c44c101035648c1c5c01090794411102201d840f583c4100b20420200829101c5a102c1d84e0200208038141c1c981601400d03061009d409882d1500c91000e4540c0614040c0030705508000c22001c07003030f8880303e06076801210000c20b50581810a00511007040e20301c407110014807804c19418 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 28918234 1250 28916984 28917029
    0xf1c02010615020a0609020f040207050607020601050427020a050d050f010501090c0f0c0c081009060b01050717070501090b070c020406081c050f0403060608060f070305010e190e0303010602010204 86
    0x70b1007110720300c0d03009802c80c03d80d80c0e41ca0030005e180850f001ca0344071443e1203038a01d003a10b0750303c06440024840c100a08441c10705040191400b003059100d14811400d0215400481743c0c00d03468500454042d80083c20b0001441c400034140c07000700d41001b41c1007840302c010b40090010001d80e866514841000801039640c0328210360003640d000700c1d983d030003003000c00d000e05806c2403082101608190082d190704040507190b0101070301b0b04113440c2942c14642d072114a0901800903922410700c0e110b209003089860002180e60710422107000c00c0344040c01c8232000c141881800400e401c108842944030140c03040e140340c5408007500d0540569410790040d40350442c040b03000d10000491210b1400340c5000f0410400c0940400c503100d038841e0000b0150302c08107200001c0041ea003030041001814000010346810300c0d1821094042040040c060300806092100401100b1035503000c054202c203000d00c6104401c680c2c0c00008001e0240d008901c4541e00c000400014020fa06502070019119017400001c20841303a50007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 28919484 1250 28918234 28918259
    0x703060b0a050d031805060c07091406090f09010902030105040b010305060f0c040b0c031207020d0809010b0d120e0a03030206060315060a050f031203010905040c050103050412050c0f1c020106 84
    0x180319004610f0304034420109014407160203500441103503215030315886501107280c41e0441005801194042c40c0c003072040a0b2140900803188400183d00d1481c3c0c9440400580e5020001d0300321700c1400000c00c0400c005000a4221844254002d0000d1006080031b15200007001c1c0244000c0da0980100c8010949a4501070300c01c0f4043c0007103040c0310707007840e00304000130003a0707804a1420201803200f00407c40b500c81071000158418031450f000b600c08481c080e100030b407a92100074551030305c9074941025000070b6919103540284003508030403510441c00529005841014800c1c0e10715610407843c0c5800410980d00240ca0382c4244415425035102c5481c1c102c1000c2c0e5500140d0700030750700c6120028188814102400610b880c82401800c50740f01c0c54054950f100e081e4400c4c0c0100441c69224002c120900c400d2602101c024102071804112616044e11503d440040e890f40550030000d000403e04003400e0100b0a510f1000c44c56010398980b2420721300104441690900600e0165082402c0090003140f50030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 28920734 1250 28919484 28919489
    0x3070f0c030b01060315060f051e0405090c0705030406030207020f040e0106050102010e010903080c070303091e020109120803060f04060503030a0e1807020d03050703062408090613020616060203090703060b0a 91
    0x110854142d0703042500a5810500024000381080003d01441032000e0280ac0303100b04035048031405550b598188000c1c8600c001c001001c0c01c42c808010030a00300000c5d4004101c0b0100c6840d45001a00e5008504c0007d4100c84080300040c0e102d410720001e90640c86040d4070800440e10260000c216460920f5051401c1c3e80b410040074000c81c0d101d00005420140342c0c0e0040c61610700c2440d000036400c181c0e565090340014214466101c40e00c51003188000c55800c07840213409801100ca089800080640e6006242e1200405007170040303040d2035506840da1116001000035090040541c1e071602c640b0b0384020a003400d4840540d12032000303407041e8802003c4071541c035401070402c0e034050300c031800c036400c002c3e406440007500080c00c15959003000a01d0b16200f042d030b0360200711080386042105090705001000c10350042c04100c000e070401c509100321502d590ba03c6504850b8150f0728503482e16601c04000402141130b04014140c24000000c001000e00c0100d101e20a43e0300c01c00e000c00c11031080005101c1060b4450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 28921984 1250 28920734 28920761
    0x6040b06090f060906030403080f010602031216020a0203060a02091302040623092e1805010f0207030501050c07020907020c060304020607020d120f09060c050c040b0303070f0c030b010603 82
    0x8000e030303a6260405034190382c95100d0240c0300c0c41c40c024010f00820566030040700d082d400502814280040018240e03240c600600651005606210b0540d03814441050064070b2a9504001510034000c01402030220040c00f58004080d20818589000180c0207075224a91062085400709460300003480d50388245c0b000e8032060b40e11070b00c2010f82075071469070884d28103580c008041c0302440f0100303040e0360300544203580b011048003c034207003038006080c1803040c460b84e65803005114003103c074140c81c0da00300b059440c1150400d1030140c103c40d0502d20240d0404507141c00141c141c0d401e1404001003069000b0007080c03807510940300c1c02c0712660f0301034040345c40303c58002c841c950080007040800d000d0f01d08440074040c00ca000a04080e40e40185680d40c4042850f07243c00100400d080070b0152480c15002540c60300145007504007004904a203540d20b40c0c0301d884120b09903114a075662428042610208240c0b00741641c07184641c0381034900c504043c0c0d0152200d2101300c8000d800030b4000b19809100340101c10170540031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 28923234 1250 28921984 28921987
    0x100501031407030915090804030b06010305090a021005070b09061006050c030315040204050301020c0607030e07030203070905100e0103060213060311120411130b120c03060103030509031006030b06030606040b06 92
    0x501c08201e0160100007005d45000080c004500048510b61060029035403040c00041e9542c1c1c9189407000d02e40d4001403401d4141450102040503002005c540002c481d581100e6609d00c50488040548850185000103008214807000300300220b0000156240660b0404020400d20b655030f8004941c81c1c811250102200e40041c0b01080440c035201050000c410f400038000750070f2503241c4010070308903001a00008500c0c0c2c808028080442d80511844a0300da9280e0041d00b6154110340219035182d007039205142089581e2800904180c400e10f401e240901b1050240018a5a4a040c030070084c0d00060949a0f20001a180028005001c1d03c40c4403100350048401900b0501803228408120300000c0083d41e850f82e48030036004469640c12054400d003c103031003001070414080341c00d002020780c0120210509520070203540e04a0b030340c0040d010307044950505d4119903907110600442c0c108050352035060b90f46410400d0200420040c0790348640f0425055045039110381e110801c0100380c48081d04460f800040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 28924484 1250 28923234 28923241
    0x91502040f1406211e0c07030806030321040b1015050912030d060e0a0903050910020a020303030123010806061905040e010b0c0d020a11010804030c0203010c081005010314 75
    0x142c907a0380b07821008000e0050707003818840f42c01c0c0c03030200094041c65042001080c040060142e0b400403030303c1594205d081c1000c02c0303241c10300001050380324021000d410b10200b41d0000f0441d9504204171410482c8040b03680690307589946801a0698040d58111039030480040042c01110101070b0040071901180381c4030404155600d0295248c0e800460b0b22500040c0865901e0b000035010002080e885441c00303000209a45004400c4030458005801c031000c03e401d040c00680403985c09401e8036075a02c2d08446a05011400c0c040c180d160502000e0029010b00002c000000d49140c0d94103502e0f1060031100448010140d160011243d191049826685c8110309201c12003205502c565540101c0d100b90900c03070b2400da01d4034481105000c007603000d011808400640b206054105101044d1207403030500007040c81c1c850b55034814202900240307456040003800b40003d400d05200305403218440b5000f40007040042c3c01c1d142c0082414008440e5050008044d07403002078254440d200781180d2114040b0385040d56103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 28925734 1250 28924484 28924499
    0x313080d0c12050702190f05040c09080706030b12060903090f180c0d020d06031209050604030c030b1302040c0f090503030a020634030504060c03020306091803160501091502040f 78
    0x2c002003130590b00b28070b030b141108a820a4a0352407102810b40050460f8903c2d01e80700800c025161880d00f640100101c002080060400005220b01600c0365410085910800d03607020070140b00744681da00d03070f00b8426072091000304a400300040c0702101068601c1c0811000764014000481c1280481c0c200440f0b114000492040300280070300b034611080c0354054a00b41c604020181035506039001943c0300e600c88190940e501c5e400030181da004120558200742054590385903040c10360228800941401504000a107a9141032a49a2000c80d801801006008094031008000f40c41d0309001d400840c1c00c4070000714003480c00200343d40c4a190107034014281e41e6504400b800022508290b225100701d02140e003450303600110054080c60101b90b50f0001964030342428504242d682c1f0b202d03d0341c245131042042c84100d4030b94190b001d41c0a190454047d8032602485042d0740f651003012000141d44402040e4902000320640098a030b00340500113036410030f51b0404001d4120320407442000600daa01e04010082030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 28926984 1250 28925734 28925737
    0x6090b0901210e010608060108012d18020607110f090105030c01050903070b0301060809060703060b04140114030a09020a0803090607300509040f2d020405030313080d0c1205 76
    0x14110942c2c04190b11a10000c4a401c0d255070350800c10103500254010300400000348107507983c5008a404000840c42952440e03051000b4044c1140d00d40754071800b00341080503440f40500342030b56001d040c007613841d02141015000b03048400070f8280700320b0042507052403500c3c1c0085620f06944005011344a611080e00041d51664000e80000d5054021a4800142a0880c802031402820982c580d42800e240c00c020044c203041e0010165014145440c8007403048100c50410799003561100d600f00301c1032409940040e00d022113009054283c1138000005c020044c0340b150848140e4a209030303001450681c40340346c05500c9008002c22582c00c00414440c41c400b05040304100801c3d060420316842041c0c14000f800400c003060100c071280450400920640c42d130030544100c40304202c2d4124204842100b40c110800f142e00c8403801e43c1902d405c0381d90b5902101e400c583c100c60041400400300da65421140404400d402014410031415000e00250607000c140503809284d1f441d544803480c19600100c820069805 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 28928234 1250 28926984 28927037
    0x71401050c070f14010207090903090302060c011808091309021f0c060c020109020906010e18060a0506070515070c0c0b0a0c0204141501030204180b010c02030d05030106090b0901 78
    0x1c1e885080000500458041000380c0688203c5110440e403e054100281c5003241560110307144605d030200031702c0400d5102000205480d4110352140e55045a003075030394090241402c545e0913200340c031a80c030310030402c10030000d2a00c00d00a481c2c0030b40f804001c4003124120f500da40030194101d40b030000d1040302000e06400d000070500083c10170042c02059030311303170304112450440030b080580e548103008001c5d40340665034143d1100e024a441a410440343d00801c0742404066500c00c2088a03600106441781d8840000c10040c0c20003400150300d80c0c1003410030941d03407114001c5c1228440024004104058070908010b6420b54000b0070f000c40961802c00042d803968050400c2d4020032802074090801680d880c000d9143c0c0802c0700d00701c1203090405410301c144001044281c0c9041c50f204000030040c0d940e0108000085a060120006040c8800d00c01650b040e0340c1c100000754140074071701112030f04603001005141a00c0007962000040754903012945c05a1041202403800b140481e010484d10400555a8240 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 28929484 1250 28928234 28928257
    0x30f07020301090b070c0b06060703050702010e03010b1302040f06030207030903150f060321020303160318050a0302071403070612020d0908040602010c0e0301060f03020907020a1a09010c0207140105 87
    0x543c1011602d4039a031000b0180c03607180c0000e9004004906001d01d0701c800f00d030071807000c90304a40b800c2603643e40a801841441002414414000d070410942d650039408150402409000050028510364540c0b00a41c0503002d681034266841002040f92031003407094a22565064580581e114195115020b180c40e0034050341d0041901c0c2d040c921422800b600581d001903100d06100c02d58103e90402d02c040110781c400042046510a000b0008540ca00724000721041400741000134180d0141a6840c0016114140203052441036240d00c104060340003c1d0341d801c6075400c2c401011260415010151206141d100388000a240c0424800c0150242d60080c0b51a000c1c0041c0020140d01c030341d41d1010075800c281c1c07040c00540d41d90746190482d590031641ea0648400100c00800c03d503803c00e80e8140c850140c902010740074080c840c000a030041e00802007512019040000c80130301c200c82c031300b404100040444808485500b003101038403c0e1400010380e9000d540b0140c034550190f460200c0110b0f1180c100203150b08 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 28930734 1250 28929484 28929491
    0xb0414010c0504080c010305041502210408070330050c0904060f0501090f030c090c02030c0102040906170604032c060c0304030209010f0b031f080f0a02041b02030f07020301 76
    0x95218003407041040e01802501c0350781c1c441e494110841c0c1885c041ea440c0505042c144001c010004540c07800707214031460038400058841c4101080040011485001c103108001500148424001c600000d000303000d12a80d00c0c41420349568810031003240310510300008a8ac00600c1c5080352141a80081d0361080c150101241400d50800005d002d83d44582d01c05c01041d50440701c140704c0c80d60f0090340c940140500012003082e00d032441e9514004611640b0a180519503a031614008071417090080f22038101402e4000c1d034030b643d2540f5124005120714428000400764049896022041c00300310603118a8050300ca000f003450364640c80796017060354290841e826206082140380640d03241d0019150700020b00e170017191130b1303411441481a441d8040c0c1002070040f81c56001081200110000c40c2d5201d41d0070305501c107000142c00c05204005050b6040605c4030b00035250720004c45d280000c0c1e0181e00d07a000716407e010707000c80e004c0840d4188800d00b070300d40016002000a495500407100c002c0c40024400350000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 28931984 1250 28930734 28930763
    0x12060105070f0203060403080901051501020309060d0605060427090201080a0509120406090e070c0b0406020d060b0309060a0c0503060d03082e0602011103070516021201020315130504030207030b04 86
    0x1390800c002220b0032408214508180b10386480c0034440d041d8020004c0b20b0901a924480c030003c0c0d0741b07008081c0c5044c850000001e0700345159200b034004200400010340095111600c60701314200c00951082042c0090034444a904041290b40c029801010b406841306401602c54902c1c2c44090702c002018003081d485811034098146461307000400040c415942c070008600d003010080d612180015045000700301040e03110001056401c00d02c980c0003035016100594804500b030340c00010342080e9004103030540000c420069096008103a091046d80301010400098040e55000d507124002590410f0700000c2d1000000002030061003130542007542027520002c4001e041581e00e42680403000541340b0326030110710030081985c09029070040c1203901a080c0d42145058880180740340a07018607448000c219500400039900c0d582c01c4080e504184200179036407490710341d494030010040b0041040c09800c0303210340220045014802c003401154507501520f00c40c2d143d42c4175048640406401030f5001803001c0d000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 28933234 1250 28931984 28931989
    0x30a0e07150e03071403031c060b04060c03020607080906132f0108070201110f0f0c12040f08070302030a0b0402060c0d0c060e010513081c0f05010801050c12060105070f02 75
    0x6000d5541c031242e40d0400d01ca1100c00a0500b0002c25511103280d40904405440240d50080140d814400c8001703617411286101c207a6200103403005511030590b1f1b500c00200450304a81c03140744400c646000342c084800c0d070b8940181c1200c54407412070f10201c41c0d41119003c03c0c1002106600d0143c0240151604030502d41010850030030000c800c1e080141500700313403880b0811545c0224003282d025540e40002c20141c4c022a05214440c41540d001d01451000040c0e900c844480c00f406030380b8580044403c50307104141c0604290f0403a485400b913034051483c01300001840c010001211015a03a0250240804a086940e0a842644050000c991140041c814030004039800c00c0100c03004106a40c2d5200c050f11b0504008040f80c00480043d8003a034144002c00a480a40d0301061280e15846055190b41c6d45209003900c28031060720800c00241410405045071700c41898102c2c42c1614807180080001d91660706060640d441072880402d03051a06a000031015805403000e0503686010344040200c0f4242ea500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 28934484 1250 28933234 28933259
    0x3110d02060313140a0302060f0606040902070303050a1104050f06070809090405100524240c011506020c030a140a0206040e0405060907060215090712030c0303110301030206030a0e07 80
    0x3c40800210039200c945041c00311004907800d4014500380038200b9514103890082d21507800404800d506107007030001c40c0042c1c0b90f120450b8000d01034960b08549030092442d0040180c842a100da120103030038844050078501c604401c5604580703004090380c0042070003d0921a060304407003012741c2c0b4210213008101980c1c0360008054442c4ec0301c0c002611010180d540c940013121030281603280e00c0c007264941039011602200903454256411505201018000c0d0404440074280e4a02c00307004c03c00214080e55021415007050300c0c0294141c0c0c1c00070507184c8915049036600000701d14940d05504c00c04c1c118001c103807494180201c0c2454281940e5900c40d464000c0754483c0c0c010b5201c003e41200031001c0009015080c499550080c454101410400c4d2030200025074070744c250804112285514004a02854010000b41c801000381e1641c0520415540c14041d02154580e40280e0200741010104e00b180c40ca83c0048038143e13075000308802d0035900e42c08101402021400302c0758555210380c9001284c40c0c1c50041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 28935734 1250 28934484 28934491
    0x4140d0609050a0501140408030402040515040623090702030301060507060b06030103230d09050f040f09030203030f1501050706020d02071a06130e0312070c08040306020301090c05031003110d020603 87
    0x2402480b00c4100c500d04036003106c040c015118100b403e13100a05c00018841011130390065011180421103484440480380c00710340981d80941d110b4645400001d840c00c40c0b6090400110079040581d0440d41b1200600081041c00c0f00c40c0030050f0801c000500a13540240040d20000b4090f010001d91480c1c00b00208040f68020b0300281c405540490400044607114806040c01284120203032240d081440381c0a01580c0349030050780d2040d5804041c0d505d070b940b695032007130140c031016101c144515555428060348903841611401315403104200003d22016110350b80340c6882906948a0b23162614546600f0025000390002e009071030340070001e0002007880e40404064409500140320303603501f06081000355410f05030740203c01036420b00e10540d1503100c01000391001805074011449130303039452003c01c81c3c0c0c841e0700c11002481204081030201c184040c980c040e6058070781016007000210741c052026105800b0031221220802c0780003006000251305500000d0074144050081e406916040d40026420f40085 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 28936984 1250 28935734 28935743
    0x8040b0d02120a0e0a2301050c070b0907210c0324180203150a060e011502060a0e0a06090302120a030902030d05071e02010210020705010209030c0603060604140d0609 73
    0x314a02a03482c0e0304030540c54100c00071a1082001003100c0b0010b90300e034464400040e107510302d0520001d164440321013104201314902070003040a480e100100c0f1081d900401c2088e00e81485120000e078103030340d000581c00c0690780388856026800019a0742030003144025040bc07a00040080800000604102203241c03000d40c1900f004022200e0b0108031340201c645521211402d0032070194140c01585002c00c0380c040d15450809030b11616074070803640402405407540040100e882103c00000c214000000d401c140d6021507003640d2650319110a1031040e1500d01082d160250003405a400c0020364990000400c54030a00544403c5018103142000395040780489401080c0ca801d008401c514050242c04000300d25428030714180001a11103062070141c6001c40a580c0e00102d59030004e5a000300300442c1600705509042d541e620440c90254080d40040380d03403602070700c5007030691891450f0104c00d0301c0c030400c00545594203151030802444110001950007a800030031004c08900451403901030a0311030b6008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 28938234 1250 28936984 28936987
    0x92303160b0f100605090111010b030d1701050910051e040e070503010e03030f070c0606050306010f031203090b0c07060605030a050307120507030c0201050903010b04050a0c110a050307020d08040b0d02 88
    0x702101807211807000708541c0b22143c84100c14000303142c000059410031082842d001a06d100990446401001503403249a03042c0301b03444205080702d901c00d10b0300300c0d030013503198501603142d13600c0f418003044003c00c3c0c4029444881c0d142d814805828414901c9003100643c410040501444001060807101d40080038a5180c005010a02a50a09000d25038003807034070b900114550316120000d00284040581207100300400035008500340803c6402032005003c1c001d083d1809940e50f40000c80742c00c8003e01c0f040769190b480354008000b0b41c0c003d2040700301e91078002d40002e00ca0b40c0c4803468180e035035202810841c0d400b59074060100312510100880c400c81c5100d000103640d200010706100b0781141e0580880820444200300580000e6845040c80784065820300344540c5800700480024003400380042c2c00d0307412525010801070300c03820760380000070810762a45440c036000d404181004d48072403413683c01500315441000789c0c0c030041c10444462640320b4040c2405604103034650340310040701c1c0d10407801840503640 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 28939484 1250 28938234 28938241
    0x31710140d0f0b060d05010c180e10091805010509010509160819080d09110f0a05060919080a0507050a050a121106210406050604092303160b 62
    0x5585440024550480701c038140d0100655400d280000314000c01400401c0c0075021442030345940d55070085895102000340650b42d410368000300f0950034001d404000407549040040d4940701c8001700b40c000c1815440b48501c0da400c21001c0d501a10144031108886802e0512181c08603800303100d102e00645c0140300100b01801d00d5044645031030040040c9e03030b00c800c010700002c1054050000300c10784100c1c10100009900032950a2115641c003c04200613000340c2400442170400180c1911701000407005c031036040b4507015107020f21543d61482d00415410a800700800001031610f01541c2c544211005c1c0040354054503142180d0034120f10b03c0c01100c50f50b0080c5414071040c60812182c0000e48019035004104030325098840703d240000b000d0281200642d80708480d41a04d41c54100c0c0c0c42d11580da8044660028083c214a10446d0100d6081c1c074040c2c81e1001040c0300f49024000d0001c00740d004140d0504010a8500000d90f181c139400215403548020004204e0610101c03159105c4a4010040340b0030368603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 28940734 1250 28939484 28939499
    0xa142a041d010503030a0c1209030b0403050903010c0e0a0902070c030c180501051804080904060b190201050105030303041101080718240f020304090b01020c0306010905071e0207060804031710 84
    0x1c8107030481c3d071083e0000e01601000039070146c00e44504980107440e0000120318000e0a0310190040d41020300b0b518890b00822044c1608000180b9103404160000c00840c24071080c00c8461402d00c944156000c942c44104210340f03913054016144c0207000d1110b032840a0b6603070b0b840445003009a801220f011034030101d460098511482160b0040030140c0b100c00d0400801e01d0381d41241080104020542c90000c11026450f4413298851005040710b12162a41c61903003242c42458000c02200c1a0015800c10380085054180441a43c0c001d5900460320000001c404006549020008141204100305501d0407815500c0c400c60580c000c00b417901000400749803880c120b64500302006a0702c0c00b0b12501d004c52000f4039032f00100f12401c8488a11000a01111250040b81003600c11800035506104406c00400c4480265008502444494441185001c0c0c91701002d07406006404800000d81c111003c01c0048602400010307900600c00d00d0001c44000648019408000c1e0540300e542280241040a0100c071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 28941984 1250 28940734 28940789
    0xf01050402100f090e130b0103051606090b070b310210020a020f06090f0301050a0209040615050301091505180105211f110301080a02090a142a04 64
    0x2181145060f4000e840075010260109000d07104400c0040743c2d4034001507101c041c0c00c0038010802d91180403211a56900e09240b40d840c1c80803503192541402100b0300286c964003c0c1c0c0f003072045424602d500343c2001c0554803813080901d401440205141c841800d0005001050280c0c22185229030745020888041401031000c2c40301d00680150540d4070105488000d03a44044030800d00303480403104299142000004a45043d10302c00d0045e8140d802c21080c064400d03040e03000380541c528143c400700050399544c002d1540c0c1019054051000c038100f00010f003c400026040b0380041c0050b5076000f041540d590000c118880314004411001346031410052009152034103102544000035000d516030141c8469610343c6035038104001711000e503039240101100320385d160002801400c95240741d5072250b0750354103044d0702e44402c00401c92003a01c1000014005640d180310300323840d00e20700d005545001c1d82d42501503022441c014242c10290342c41e08205000d2412204000c0c03019111300d03040300500c140701314094801c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 28943234 1250 28941984 28942009
    0x1e020a0c06110615011e090305060a020304080706050a180503130801020301060518030c120d02010f05190504050c09070302040512030403050a08160c03060507020610051e01110f01050402 82
    0x10401e90800c40b2260040002d106500901d001900304030301110500143d900c6000080c49031101c401c8141c022010301c0e080303409081141d0181c000c0c0c8505a50725460036049100403940145255000e114003808641c1a501140d13000648020004810340c01480c01e844006c81a0790484c1c095200203141e0303001c01414080800142002c1c0000d500395410710074080c025000308180d40d290340040600300080c65604002c1d140c4c07600400b50542004420305c40402c2e4990030740641d101e026608240c1c103034850349901d1007440e210300111210003100851f0314000740050b002c050015280d522a03c0307619559903481c680310b50302a240903140181e035680380c54144550900b101c224440f00c0d800030b04c0200040396000c02d81418040d805103890350768421221100713802907810400a040c40d222181d0200c00c00c44103900c4180100f4003a000c81d1142d51703038111421107400c00f07402050b4000da0001078009441e12442d14000405205061005240c1d030441403880c1351200b0700d00c400d00702d80e444409000560400050340d03441d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 28944484 1250 28943234 28943237
    0x1506030a05180604122102031f0807030206030609060f1906020d0c08040314121602130e071a0702180114090f13020402070807060903030b031b09071e020a0c06 70
    0x11301d0991954a070384030110403007005000c42c1c1958084600315480c113800d0041785c1c0507001c40d101e00304000c3c20050000e13200342c519420090141c006c0748120f40011424212903000706024990740c0d070501030281c50a0060543c5402200a403000130301560341c0c5042d100303142d5100240221440c40d107403009250440c0711a08609020340c2000706c0b004103500c5001ca5090700d4104080c007040c1c8c140c8020700c074508400725800c019210000300f0102494140c02e20950038150088600c982d1800f21000c650040312224503190942e5030040404100d0a01e642000c10400400100598180107160b004149580f01d000030035072414200c00014040d9508040c580f08d00c00c0c82c01d5074104514942802009040f01c0041c1c000a100c2e1215210041196991380455007016030240c4010b481da0420300d01a0090300d24002e00310040b9080426403051814006140312034600341c10180c80f01e4821041c20301006000c040c142c0010000c0702c041410b20b42c2005605160f801741540d000b4058036500742403180d0403800c141c02140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 28945734 1250 28944484 28944493
    0x90b15100906050f0c0705090a020403051e0d0c03020304050409080d06090209010503040f021903060b0310020a1209060204080109120e040203151018080c0f040501050d08031506030a0518 82
    0x45110fa00c0400d584400c61010f200c070b950761041d6080140303024490740c0300341d40c084034290400501c3c0005401034000c5a11030b40880d842c250304043c400c00b0004100081074038980c480fa401c2002d00348103607a4146900d0090069030b140c02d490341e000c039058481201081c0d40b2041c00150f540c120031400d126510013030402d20300071402c0070300600008059100281c000380c0364640c0a4080c40540d61120200c030b44081ca040b02011511f562403a04501400004400c2c522038000d24030008080c074114022240c1c0104a9070f9200031000140d51090010160b071101650303180d43c24400425011800d10503510400e000e0401c40460880b031100040061100c0c0040a0165006106100540319040d02c01d411181c81151500b80b150500740c2e0840701c500b030070010141d008000b02400502c1600100f4030401c140010703202100c0b000907030300170300007580c400313100d03180c0c121140c40d1000c804035070f01c03102443d000150400c00081582c511000030b00c654105880e4000700943e59818081c94100302c3c03200500c1511200301a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 28946984 1250 28945734 28945739
    0x130203070f0b12040303020c0a0c140108010806011502030c0a0b100b04030b15010513060306060f02010207080a0c0f0605010602010c03050f09060703020c0c04060803030906011d0415090b151009 85
    0x4450500655448030840303909000413508141c02178041e1100c2c100507400b2120282690301f00f0002d01c16032441550201110511840c000394031806459060700e8565005000e180d2034031541000071100052110304501083c42440c219820a01180da58140194034010803828370341c0410003080d1956002658042041108100251004031002d6101c0c0c6041e8100c00c1c5c00c05840010f1300c092169160700310310040300c0304000c500b45800d40d0103680ad54007555110b10380c8464511081e0b080b031055040c041c000150500c00800454130901010828610612001140c400c19640390010740c0c10a03040038000d40d44404250034105d034148100c9601c4900b0501c05088c1c1d08200c40d42a8454201034410010507400244038002460208582c0e84010340150080000d2580c0d400100d450790000da03040001030040b03500000e1030700100032400b54100b03501e080540c2c498032183d4500801080e40600d50040540b60001c65001c01c082825480c4074440402c07040000d0040c11341001040d00c0034140c02014400c01a005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 28948234 1250 28946984 28946999
    0xc020d020c01030b0406030f0c0311010507030503150307081e010507091202041a180a0c050306090c0702031c1206060206090a06050a0b030a1203230c030406060806130203070f 77
    0x500340c0741e1100b0b0070000b408041c0f020106015060340d40019194052101684041000500151085901a001002c903244071a001102e1a1140c3caa0290005000b0f0021035040f0a075140302c00c84001004040762001e81c0d882c0c1d14107003008800d201c01841841a02500b00100e00e081c0a000c0e841071403880d00e180d00724104040340ca4100c9003801c02a008a0303607044150400c00c07022030000120200100100032051032101a840600b4044441c07031980e60404d48100c07041070041040c0c80c0503035001440881582c0d00c642010403103401810082c0d03803500c00c0c1e040114800581076a51203081c021035594141011078000944241e500380d0b07000304110340c411401c02c40025404111800f015520400110340d40c2c88524243c0064000810305a505004652054082000c4d20700c00140716042500c05000706010350100c514800c5183c1d0080c50729424601c001b80422845500841d070040c80340c800010f105803640021841d09004440d17403d00000c03102015000d5103000c10201e00102090544030320594201440c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 28949484 1250 28948234 28948243
    0x403080a0503130c0803180a03020607120201090c12020315040309090b0d080301140108130206030103021309050106080d1202090f0402071a0408031008030711090a151502010c020d02 80
    0x11814204440880032400c0d01d6405103c075070480340c01c01d156240e015114860340e5125400418080d0503980c032503d4691042c00d0001000c0d048980060416041248a45402e450280707080380305c0c1c003155039072141180001c0c0d4850444002d048403100f8a0025800f40c03051514141c0c041c030718a86015501d0081000113980a6a00e1041d120000b10100b4042141800300e10400880c079001407c0c1c01000c4004074800c4e41d50742800004503005d980d100d0190704c0d00b00b0264030b812481c0e40e01940140c000c200500260070402d4180348402030002c0001034030760302c54403550708592040d0410301d0141c000c1e484011107590300078160340350390790003510441c40e0035100800104d42d20040c4440394000c0d50040740c90703024801c03440c01942580021140e2101036281c146001c0ca110fa2045440642601900d00f01080030a000401d542d038040e40003849038a4180d01c1d808001054a005000d114015100c00c044854045040d10807402040b100383d180362604c64543c1c000e0f0035551544081c3d407c540c800710700700c0d851075400113 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 28950734 1250 28949484 28949497
    0xf0105042711061c050a05100810020310090c08150105040602060f04020102030712030203010302040f020702060702150c0106080312010501020d080109020f270301050c04060903060203060a170604110303040308 92
    0x2032180304038094070101e01c190044030350300c2440b0034440000a503e1396041c1c000c1c0784210407420041007030303548100d0701c5415a4480e0040144550000301c4a6015103c140e000f5504003603c02e0095582941d62030300881600e403e4403d1500280c00101441000c0701010004440340209080040c10182040e0000f961800d004010801034810070010070251790085c01100c07840c035081018000c174100c2d903000142c042e50080c030049025502e040702d0b0900455003407003542c0d200d0341c1c001c001030b25001c803540810581c0c00c0c28407109004a03004000f6a80400403d210b803000400e0303150059074035240c18560402500030140d0109041d0340080c1090104c90b60310500d6241942c9007807000584131500c1041009680c007401c255000200311a01c64030940d680200507011031302404500034801035950303030291502401180700354000300308100001e100090340e03034014540c401d80c003429041c0d020381d650300504e2212761201c8540c005900680c0030310040c400d0650890400449c260300540c0f81518503030b03c1c2c40d01c620441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 28951984 1250 28950734 28950743
    0xc020c01030e03121801050106021b0d21020c0a090b01030509010209010203030c0a020309180103140c01120b060f030705040305070603060b0a0e0117040c080c0103050105030304090e150f01050427 86
    0x381c0011781980d00011802100080c0d0400800c0b0f40d40e15960082e680300448281c001001105103200d41d0f540c5042300882142c546d009816100030982c822110420342e8502082c20158001e2041610503522013400c2d480007400071640204101d1401000036080300c81c050800e6400e0f0b401084000c020740d80000131240c01c10103680c102c03a5201c0d0110070403810350042c030143c2d541c0b010300884506580c21004c58241d0503203010340000d40030036400e0b036040d580d6a4801d46071304d404078075041c01700d04110030035510110f100000a4811032800880000441035940300f100c0203000700d0300225080c01031081c200303d0b52002e050399080c2001510f04200c648082e034010030418404001c050204249582d1264842d48400c0089076aa02c596007170920707020f0241c00c05405150f50620451104551079071103030040e2030482e0000b8001e50320303081c2481100c42c0640724140040109100b141c4110b0401e21400503007910480f0800040031030395051004220076145000c885405d03101c040307042c00c0720010b001200c3c801c006030321 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 28953234 1250 28951984 28952017
    0xb090f06060d05040c06110a03020706050c03070b100609050109030f020405130501090b06041514060a050c030c010e12121303120c11070608042a0302060c010c020c01030e03 76
    0x101400141c035442060321103070380c540c00c00c002d1008002242c0c40c60000c1c3d441e035442d140c01000b03d80c11810f990705410796001c0c0c01a0300c6680100251401107000f03000b8500c20900303880c0f0340307160703900d5402e4031160039203c984c5c03a260002d81c01c1003000d9000c45010042e240c00d207409000d031440c6444044e002d0144c000e020784140d40e62404182440108404131034a81d030300c0f400900c4081c1d4039081078030103048100c44d654019410300200c000603894004d205015038500b403100e5281011b070340d424000b0a81005c6007240c1405420082030400f6082040941500c84000001050350f40c10f03003c00c1420034540c42840c201c440c03000c1c0401d104242c218810250320030002d9154003002c2d207c3e410211003d803071381900c02d01c8544c034102d08941c019922454605040001004880d001d50395204125501901241d02520000000c003d40900284910840344400c888445000381e9544a170001542e603480858190544e0f950317061401c6106406002d1100e440703009003010010075003200107040e01d034842c4010302c0c28010032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 28954484 1250 28953234 28953241
    0x3010609090b061c14010902090303040e04050a05060f04050106080601050a1401030b0a09060e130b06010f11030301090e010e0a030905040b03011503050c01020708010c02031905090d05010c030f0b090f 88
    0xc07200c00340d68080b6100c926800031541e907000391030300030074100f03919812210b0564004207c1c0c103880e000700c90b500400500110300c0c05240210400317144001500848650280d1111800450002c2001502034146032442e9070312820a45080c07400c40700c045c1e221304034541084004000c0380da00c0607040c0084622401242c68058848001200244050300030503500c001d22050219810225900c6a009e03564041c41c042c5803901c80d025020941c001ca64070040c001d0b85504000b80031944214220041210725007440e00c0f600c00d5250203542543c000341c00551010759a00c04951602d0002d02424419980c0d60303001e4186817201d40c0b0010303c0400b9a00a0030301454403109950f009840942c002c03801030345280703e80c498098036860015100c3d00000007a50048c40780c010041001d03a4180f0401045803886d40056140551000350130402d44095000701060100038070003541541c440c100040400c0f4414400041c5010158601804481006d00c4c0100080c3c0361090503c0c3c182c40f40103c0c02d42249000d50304440b96035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 28955734 1250 28954484 28954489
    0xa05012912070305070f02010902030c1c05010507050d0c0c0f0201050a090b0408010617120d15030602121014010c1401060305160302010314040503030f090c040204030c0e090303010609090b 83
    0x1040e00005110380708a41c0400440541c103512282c01111681e641c0d00400320f8500701207090724040b0380007030b5054003c0b61607403c0c24030b400310308920300c00d0302203407091086005500c9543c21560111400c13000b1400003c1e101440d030a0324843c0c581d00c0e80960600c5001c40c8000d80b941b030200051141c2c02810300c8800528141e81500400080004202d1003881e10b0b521034507852154045c2c041d03840384c0d4106c9401c46c03d0307100b940e890124289210300d40b1418540d041006001d059000307003011000d1448420f05244010002c101140014040201c45e001c0d003210742c0c107214103200e00c00c0026910105030080c2c20b41c1040a0360307a11030300e03181c4000d0700501c5240c0104d440a00450050030290720040151080b10220380c07013551150801000c0300c2c000d8038100182c4401c102100644030086400074041d0308100b000681000300c4269a0307401144810440e00204d0035900070070220703486a001134a0300e049241e0100805007103262000c1d80104035102850940d458071901030200d9500740252544103841d20403828458 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 28956840 1106 28955734 28955737
    0x708010501050a2303040803151005070308180d0917060411100e060309070503060a0b01020a121205010b1902010c020715030b0409030509090a050129 66
    0x80340f006046030b640404c201080741400071344490708940710012016600c21403048050990701e0070705480042e02c4070500030480d07201304003400c0200e000300c1d480303800d0b160000d6243c20300b40c03855110f000314050000d02c480242c07040361152442240b03440e50321103008001c0350107240815240c040c2c40440f558480900300d8001c0d185100c01c0e0803c2044d070500034540c845465091400c03001c00d015000000d241c65000341e460343e800c2d03400082d040c0420700e418006035402c185c1d03040041001c0c2e580000041d48078a95a04040c0883c2091000210741c039009481d5041940f45c0848108082c1d83c640540148940010080b0600c0106142c4082602801440744c0ca058150720b40040c41c5041c07918a03c010341900c1044021300701a01c1e00c4003c6034949030f41c012064214800d490b2a9210030581d01030090703000008101a650f40d0804004201100310201c2040c0940410b09458020824051848145 = true := by decide +kernel

theorem cover : BRFrame.Cov 28776984 28956840 := by
  have h0 := BRFrame.cov_init 28776984
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 28776984 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 28776984 ≤ n) (h2 : n < 28956840) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
