-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4392
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:28:22.905951+00:00
-- url     : https://prove2.me/submissions/6519c5cd-bda9-4215-b760-7409a2d7c6c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 789748201 ≤ n < 789928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 789749451 1250 789748201 789748231
    0x1201080d0216090506040f0f0e0118051b01140c0c011214062101092a06090515090405070c151a040506030a02060304080a0e010912110a1703031f05100c02040b280e 72
    0x40d00509200dc00c640760701414180c58821184c818003201e070700031407201c805544c0000903102096030045881340e0a803004d4201032041f90310040900d140707403101425541c00340c042c1800101c0980030480c8003001c1c0c603420344001c0000c0745042c14200c60350440000592501d000b4481d8009506402070203050640f46180c030b6480c961440d00c004e108241c60101242c044684d03086c0003079850341e83c860103990300a01e0b2a039100c50400b4103d08010041c07a00c0f480300c890803107240c10740c0000b25090781441000c102d00d0840c1c001403a1350f165400300e42041c0369008001d5105400104010800c420070002d080c0c0107030507585608100b1030301030040d101030201c1d00030942001c0c3c610120000050441c01501a0100042c5c00a48050340d2010310b80840900003100c0e0111340c001008101000559000d850125440e02e1b0315120040d00c1c000105801c1070441c0407000811002e06030041c103548850b00041c2c2c400c24090800014031130f50300541c950606046030b45440c5001d08050000d96544040c0c0141d003d03004d44103840d44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 789750701 1250 789749451 789749473
    0x31b0f060a1e1e0f020607020102041202010c080408012c06010b0715110f0423210a0f0f02010e03010b062a031201080d0216090506040f0f0e011805 65
    0x3400c07480b070000812104900740284800400212043d0780301d140c45408081e444404042d0800000400e01780031a8414001040ba4682001c6204180381e02070a10701d400c02000d040c44846841b0f5030300f2000c40c1d90308040700c02d20501220030005d5180920b071581d46001c0307904a40d4060304d0f110300f84078030003490300d06000f10350100e42d40c01c81c07800c1403071022200021041c03c1d651070103c658021a8070b410801002281c1040b16050098846072030420b8140c10020914903400010f0500b0007a000341c284ca808a0160031028a100300311743c4000316000144000306442ca898401c0d001310300784008078000b841102d81c41460b41014090400c0380c0c2c40c020320040c1000316006060140090300d40c000f1a03521200c142c3d414403408144014000b00300007a405484c1e541c12305440500e00283c0c0e40c802c0045500011540a00307610445104090701d1a101c40450180c480700006400342c61040d0030f0b000c84c0e51528031810203e4440c0c3e4041d491508648009006002d549124a121500410000342468000002d000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 789751951 1250 789750701 789750737
    0x180103020d061d100b0f010c0b131a0109020406090806040c21080c060603071e092c010c02010c0c050303060409080c0d0c03080c1c05070905031b0f060a 67
    0x80704007840c8602d5411190141050f50f203010400d043c0d407440d10355610940b883c1c1d400c007510000e099000078205040103a20343ea413034804a800080080014228a98213007007048881c44400c01c3c0c035446199070207415610744e542c42000358032a2080301c000c0748140c4000100c011011420912854014418903450b0b490210f074000001d024008a40c0500081c810000000307015901032301d000203003e0f0041846103844028036180001c20707004240c800000e9a10f000080d42c1d07448030842039909490020900c42c40f441440045403940e4514890401100080c004110b40154440c0c42c690086a009109003500702d8400e51b0060001d81010b401c0b03820400024440e820316411110b605072140d509a860300f01c411100506140f034214501001840d15410001859400070f881034000035030f10081e07484e10242c041c03011013101c040c902441100303446400080b80d150040641c03400404018050740c91036502410300c00100d18528040c68400c44104034161403e01b0310350705a0b04165110b840310103d804030403c040c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 789753201 1250 789751951 789751961
    0xb010503071502032a030f030612030313060b0d0f030f0206150d0b0619030804090516120507090509070e0102120909010b07260a020c010309050717030c0609030405180103020d06 78
    0x10041076401c580b486078170070130b0400040040d11a000391f0b40e9240c1c1000410030042c020075264a80381c9905c180144801034065004000206900c01c3c40001c60380502e02c00700f0216100b1130701c0500b908668803071034003d050b084900140d00d02d00c075500750f50281c1e644025408000441402e81303030300000b0042001d00060305a100d00303900108018090f0007200e03410004039036080c0b00b6400c12104007801040401c481000c07801070a4000c08100e032489200030007000003c0c1100040070b45030a0103074035000855400e5002c1c8000001400d405040284171340350200002e4100c03410301e8001c07401403140c0442d00300000c1c03c000681c2e02058000301a45103e9180000e0380c3c0041d00640c006440d2076520040c9070a00191300c038146903010903010007090f107c425805019091480c00c01c1d004e8141402d10501400249000c02c3c980d080e80c000c42075000c090f0b0703c00d503d81841c5000e030021555180c40740005020868030004060001c954041b1190510340f40913041c00784540b842884000d40044081c0c005100041c015004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 789754451 1250 789753201 789753247
    0x20c1005031f09020403120f03060e060409061d1617061602030d09030201150501030902030c06030a1104030c030b060619050304061112061e06030a0e0c0a030b01050307150203 77
    0x14a030403280c48107855412a41719a00071542e01032004078450303025401c02c48000b540741040c14208030f143d00e0894500290304c8000c0000c0d120b1b5a607038100c0002c00140398003c0e0316100031050500400012031b9a050390f00d610a2060050480510800082c800b5500c01a142c200c42d240740988000d0f242c40d0221040c400c190f1750450290b002c180701507070010000f407154052160099001181d030340086003203980000d0032504541c3c101401e00303400f000583c40006100c1d100f081d094991583d607940c3c41e8a40b000070100b040c4a40c2c80610300140020a00000c00329440a5902640806100342c5462041168501c42c0c005066016042e49407608041d1340a00003541d84940580d402054091a0081c0756103643d0201c2d031a0001c1c0c20305102800010700381070810808107100d900080d8a4641c0540010340a03010080100450580301c442840103184244980004244042d1a17030b20a00c0c1c59242c281c01d6804240100c500900c00d10600060545654031010240c803400d4018602e4003800440e103052441c0300d651 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 789755701 1250 789754451 789754501
    0x708071a0a0915181205031605160305010209030c04050601021009170a080a060902311a0714031303230709090c0503030f0f031e011401020c100503 65
    0x4800a103190300c3c02110110580301c1e40d1009007110f4940d264852810081d0401d0107010b2501c1e06150001c1d00000c1160701c1c0900031405a91150424030f80581b074142d0b140140120180d202c5400000c200f8150050701174880210b00303031000b0040d41014070045540403640e050059014181c0c00c0f91920040e070004003503900800c861010682d4004020641d50f000310748030340004242c00100b0101014602c01c0f240a0040140290718009041961200d1112451070391044400000c081ea0b4404810f070010704020450390403141c0340719584d42c202d200103801400099450205002c40080403001c0801211300700034541400c03109403410354440100e006000c4071102c00352038141034070128004081000e08006e100110011482c1710141c5001e054901003a801a402030380140608a035806600701928005c007129980141c5980c0d8403154542c24002c2d4410355440401480c0011520461403442030903202802c0c0c00b15040c2c1484101400210688610040e00248003030001c68800180090020f054000c46c00b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 789756951 1250 789755701 789755717
    0x24061807052104060b09040201050f1c0c03020a0906180603020304050f010501080106051201050c04060e01020a080c0c041b0905090603070f1401030e07060c0809131401080708071a0a 80
    0x120051036485800002460003005600f00b108000da240074502c540748040da0780400b40d040981c000784c960300a890700d8101540010441164004a00e00c00c8902c090600c04244160402c2080c00740003940701a031030301d0015600790b2010a905001e000501882004c0702142c0b81407516081048000b50005001110f40340182110f01c1e100700e50034003426020f001c080e030000075214646000c000b280c0340f218921a41603410542040205078407041a18211601401c1c1003d8000003500101d0400c24860b10003171114070045201a10300000040d0420308041c10707513040103401940f400e4220806294818803000800300320040c00207091841e0f146e6000040542206c1e0820303200c10314211100d02070341009480d4806928440c246681c180207a42c540e404072000350011500341840201040500341018007012000100307103aa41e1680380e102d00303011846083c01c00c080034034107103c05104102842411407900c01c221002c40c00d200d012444204542c1440c1036866544080180b071592508520f440c0000c0c84089 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 789758201 1250 789756951 789756967
    0x61401110c040f0b0904121b020f040506010e0603040510060902040509040312060b0406080a15210c0314030a17010b0a1b06020a050726030103031805122406180705 72
    0x171030906010354412442a4080c6220840c01002d40c9041408060b54850300c210300b4026864069000384640015039001c40da82d500c034801a13912501d1081029005000002084180039011031031052020b80c04600340141e541ea2080e4800b607025600405a0000200700820b0003e4060307045441c0f11a124000414100c1c2d40319000402c6404c03a03881100801c5850082009401103403050b2900c5000c90801d107980d19080c0426103c18015410003da072411400e4210340074080d40e0b01c0010010356100ea0b846001e82c079215070960301c94000d410b410b40800c0400d0003142161030516240784c140c404082e9002c1c1000104181190116000c4100c411000305030380803a0041902c4d4001060b00d01d6544c0c0710325944407602e107170403819980098101c202d00b0404105455440e1150b40c1101e044a4141c500100d00000d4542024200800c5030700c480d40c802d03c20100310108800100d0030900c011302c5483d08404440724042c40b1440c42d04101c0300e05a002c00d00030100c0d0401241c401e0440c0d0070080c1c17860414245480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 789759451 1250 789758201 789758209
    0x6030a02040c0320130302220f090b070807020c01030b0d0803070306032a050108150a2601060803091c05060a05060a0b21070e06030a061401110c040f0b 67
    0x45011980001e0b03c07000b10000900040c80700138440d414281d0724a00c2d040c030002610740b80c991280402403080200103086200101069501d80800902081c204010602100d10400502c00b8100c115070903005034002a440d40e0060134214460062a00a0409490084d00450041040342525980715140013084e4005ca441c0c100034520a81300f50b100010980d0860901c1c82c0d290b541084203911142c00940b0327509161001c441510b08582081c00c1c60f01651300e8000740203840d0449a507c181e040501182d0015000da4095840021540107110003450300c1c0000b42541c2c280c64240c06401d42d10361080041c02810f081c0f450500354a1030307400d481c031220341030b66a4440d070270860150340040c240d684401c01d014403490681e04040041c600361890038601043c2821645007010201e41440030b544541000940c510700504400d8641000108159520714103000e28900030003050040c000c000480e07054040e0a940111114402250020010900c1800da2070801000d0290310400e030000a80b16a0000c00c542c03a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 789760701 1250 789759451 789759461
    0x216060c0323061c0c06020c0d0f060c0302040518010311010e0f0d020a0803030c19091401080a0219050d1401030305030414011104090b030c1c020915090705070b0f04030906050306030a0204 83
    0x310400b03514280030b140100003481c01c0301441b02113220b9500132720040000b44e000441603292a81c09800400d00c5990190160300038050340d4441e6421001d6603540c0c0c06941210740d1941e040c1da21a03050740350b0803c2100011038440c0c0d00100e0158011018070016a200c1ca0610259400140300410084da02a110142036066400a07100c01c0c03a44000410518800c0c0107e0b031b80a04015072034035060501c545405c403070302c40350420484040c0c103000f00c24000c00c840c1c1085804440690200c420f441100700c404040080c8950302107509a10b01625180303900c01014003014095040341e404d139403070314111346a40e141e60101c0e08959032182c7c419982c4010480c90101403c01800080c4140c1c1c500041035420b89040c541000003070070910740314605c1046281c088a40c0340481811564040c0e40603501503449014503050074240c0b101c1140d0140c004c508024403140d207d001414424480c202a10158807200180c1491082c25140200420310802d0300380417480c072500c06994402001800c0b28807400d45600417500f164 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 789761951 1250 789760701 789760703
    0x40305061801110f071a01080c01090e0412050c0a06110403140d0f32072d030806030a02090405010f0b190e0c0d0216060c0323061c 58
    0x2400440810038201c101c0080307a452030840c0402480f100c80e440f52084030a102c2d1200001841402242d00e20a00c0074041c440b61001003a000c403c40c00e96141c107030389a922442100d007036000800c01100482c42100b40c612181c0100d6000320303150014010004181c4454201c240d60100700c1c404e9040c214045a170364043c0d62410524510a15511403c41c2801e0782d007100741000300f03402540f081d90100002e0340d2215604183e00502d1030305205061421034560811200800c102c0f10001203081e00d28000c990000c000c0c03541034810300c840c070040c1c94259103202203201d007440005401d4864a01c928046030160000030390215004040c0e0320209456800501d8524082d14282c425a54400358881c4074041031160100e005002c0b900d20440346020350002007418568094084130a0320700f000700e4040d80b48070050780c11141c003503030065403182d03122440caa002200582069410307500700a8a0010640240308442461541485846140565450300550090054022034000d000b6060002840ca0582542d0340340e5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 789763201 1250 789761951 789761953
    0xc031119060513261c02030601021603030c08090a120b040228150207270b010503073207111f090608090c13201c0b04090602040305 58
    0x500e6207042420403290014000703186400b40f46518008544d081c0b200d10a0002c00c0c1c1c1c04805000c02d03079441c04405000f20801102441846210250150543d4020318460107080c0d080760344452644108a42d8001c0910010700400c04018005020402d400010311401a0203001c07820001e540d002d5040f0100301c3d42c0025900564a0418042103240c02c0b4842a10024044400c9081c9030700e000c101c2e000d061041c80b65a030700901d40c00a071080d05000b030110b18014240c41036041c420321041d80d015120811440c1000011600c0c00d01d06810075801a0140d80c090304607550307041c020043c5280307581d403c5a80302c902030a03500c210340c440c082c804015038010300b0460300c42c1d02e2070124401c00906125441c108a00b502d144d5a0890790307003400d4036a10030301c02e20445a440c81c00d14099194010f089052411441031260800300c1020030f9903042c4801d070814030310141c1c82500343c400280c0c00880384019000701d498001a01c55001003803506144140c00000081d031000b000081c00205560381d04049911990040b901 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 789764451 1250 789763201 789763243
    0x150f1602160602030901030f0c0f050702030109051c020d0305100909050f06010609031104020309030735040608091605040f020909010f0503071e0e0403050c150a06050613060c0311 79
    0x15a503410702070303208002c40400f2305200368000400050001000130b8031040c1001404600345040d95025000b6403c5540c10009580400d4506845500c0c403807516130800015205002c1ca14580900c40e100740b620401c0240051900d03142403081c40d07000b40065100544091140c050f440030041400d00c07619000b05850780392846914914a8059920541c0c003071018465403040c41080000300b008030031200d00c203500000c4440a054000604c1c0c0d035507101c9280600c01c0c103170380980f8000c400390f26000400a451058544425965954980d40c0d998106001a1584038011120400c6107042c10340005440290452000d03080245070400b0805c0344000764001116414004400c101c541030a00140000d000a440c0700385d000d44c00072408040401c07441c801c090010f107555001406051141e81038582522a8005860007141800301d40c42600d142034400c110046d141600000300f61918000b22000b03500c2079402e142e0264030701001515014140070060f018040c5103400c041890341c080c04031400141454091501e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 789765701 1250 789764451 789764467
    0x70b2107020d0e0306010305031e040902040801051005030d02100e100e100c020a03050906161514060a050a0308160212010e010b121506150705070305150f160216060203 74
    0x10410b5040f4500600036084580107001280001c4219907081d40f4030789409184510303120b800100c611456121500807440400c0201b20140190490380c0107140a81000c0a0a074440701010f072916454803220000d130b07014030418207a44489402c0420007c0040d410354a000c05800342c2e0350141e0720050400d44e2160821407070116904080d20419040c00001d1000308280582681e0240803031003200301c8240b0030744000c5002c03511035800c40c81410b81590311000126899884c840168042c10502007500c000d103c42c1c00015000b0b00b03104039038000303c4400406080105107180c460791354543c403110300903203032010140d10200940c4405144003500c000013000003d80c9100003c4050031900c64161251091410302403000059034005000108140501c40c13140d09074036800c0014403d2920810f01845030b0101103140810303c4030106800003105d004409803038454040e12080c101c1e4220032101181480e0002000c02d00c01d0030064503071a0180c0755401143e00e00d01121050b80c0c030854480c0d0120006900c0010b24503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 789766951 1250 789765701 789765707
    0x6190503090d02030a020604030e0310090b040506150f0f0a050a0b0c070909020a0311042418110403030c11030102030411031e0c040f020f0a02010209100809070b2107020d 75
    0x20b0104241c0e02c059400c005840030025103c06018201a00300001c603900c190250b90140442059041c848001708030100451a080c10f40c00001c0318180c40718040c40c00094041d030a400403e451a41b0001c210f00c42c400000420040325003d442006a0448003045010506d615081e1000c80584015101a13444414080500c1d2a046c01504840040f5040558000068840c2039245007941c1d0301c0b0020140c800100c0c40824010024502c103041d040b000d0300d50880d5900c052480b281c3c207032544c0b800c000c1a491445004041621098a408481c0300f03070402c41000400e02c2201c0080c0140d10074150031100100610010b426600240d8081e07030300d4400c200b03605040380b4040010302c5031000f840d2a5070308042c0300640c29a80720000404201e000c0e47d11500c000c82a41c80a60407a0011129400019280c0d011882c00a00035080f80c40c0704d0780203124000300c0c0c40103540140200c2e481840550000c140b80d41c281031040781c00c2d400c0804809560490004001d244d20280b104540c4256110ba0080280306c008403801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 789768201 1250 789766951 789766963
    0xa06090c06030e06060103112703010b01031e05041e12080f04030f030b0307180603170c0a0f03050c061302030c0a0f05240a210209100e0619050309 65
    0x803105052900c1c840c03e040c603501140c0d4940c004030901300040c09841e08031407582a072042c541e0710b03001c80800e007100d1010091074606240148000b034008112800e030788001541103401132889840c0c8406408005c8007002c000e90015540a1720440c41c41c0e01d42c0d42c050007440031041d09481304841400080c01c09004007a07103c01d00c2035000c0e80c1c0320003200f40e41c242620b014000c49804030307142c000c16880d40c940213210b807001c1003120002c00740c001e282e2030208800003400004000500040752100a0728031402011091130059034204601d80c00503103084101d940c0d518007125000581181442414040c141c0000018800320303214a40940a140011000f8810142000700c0c208001d4032a401c450b00034801d80c80350307078900400d0b41e0081d290420501803c2c0340300f4010541c0b84d008030601c071000060581508c1d500c03003100c440c000348102c5200c624845e21802a416402001e0353700390001e141c0c1d90741082280c422020199040405000e20f8075180040040340c41109419603c18040f03030b0300000344000e0300e8041000f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 789769451 1250 789768201 789768209
    0x6041e1a09090a1122120305130509010303090b0711041a03010b0108072a06060303020d0e180c070c051c110303030403020a030c050102040e0a0623030601170106080a06090c 76
    0x8100006001c07804d07104d40d001d030740340da00e42c00c181d08801c041c00c2019800100c0003900c070f200544403203030503207180081c000c1e4070a04800210740c19550780055141070505550f03069991540b42d0710112801c1890ba1842c0750401581982c6406030f8400c0d69005468030701c9010003c049421012100240550601d030039075803c12581c40c10000d075982040801079010300c964110000188480290021069801001450b4014080c189500d040303130000415800045416a0421503160410a518800704212480f26445480c1401e90030220000b280300054000602c200c5d0301c280c043701c6019440e0008540c40c00b20b0f814284242c02c150041c90002e11040f08031042d0504400c400540c918074050758000e440d41707240c0b2001024001c0562915081281c20b40554024083d102d50405441ca8241601e5001d41901d02c40c403446101020900400d2120010034500041e5025000340342030391030080d5200c0b688100061043c00c5560345e65001c2441c100c1480307094982401050003003413810003401e2802e0008940c0e88 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 789770701 1250 789769451 789769471
    0x7050c0a05090112020109090f0e0607021501090b060705010903030b0f06040302030a020402160b040303090b090d020c011121090f120c0d0f02030607021c03060506041e1a0909 77
    0x34040205540741c0d502c10b41034550034650109425250320058803501031a40011107941c3c1001040040012640e00031403c08044808070761a5441d001c20030781e2610080f10124100f0054a0018051031015800812070b039000544210310b4800702e500d506007120441903049000030340742c1e40c41c2800303480c0144200741242003c44546152502d10b60000f90b44d81000b40d07000740116004120740462440302c1d100100440d412040700012445c081c94018000c00d0354200464102c569200401c1003c64005890610400203800030444008200c005513801103071090801c0d524801d8040030403003d410320a41c1f03100064040055034070b684a82d820410020b02402d1414010035940c40300c9040761100148a20400c0e5080d28a070501581d0f0f0300f09090201c00006000c1c1d01841004188140c40383d00090365060200c0d46446030b038040c01c02c801c2c01c070160f854600c1041e0341701500b4002444500110030882400c0b90300341c00103a940076034483c42e08114004180c01d448040c5004141d051181c108405c50341c0e441100c0c15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 789771951 1250 789770701 789770719
    0x120f0117030d09110d0b090d171305160b1804021201090203070507140a051b0d020f041416110115030308060a0e190e0d0806090a020d050a0207050c 65
    0x5100a907603008200003808040d860744541e03402c2c049140401c03441000d000d0f1401541604038107146103581ea00b50f5981d42c40d446060200c154103441151100d03440c01285501501e00d80714070b208004c5c00d8102650a0b2403070f0240c006040c01c41c0c1c0083c03003124001c01c18501403a80b0f0b01c21080d9240320210016154500540c010407404c1090405e841034035041d6a982c000058030f9450b142c4044034203020350000148820700751085004040c8000942440c594810b104494401c00380c4104020844443e81200d900928008800c0c0c0041c07800c001038034020f03003020344001240d6007511503040400e42d050f6002840741c1c408520107181554080d03030300b80344400a1030080c8080c10309403c0040c4100c2c4107100140400c1014000724126513200b141c0d0b04002d040e12820b40e8034900b00344224410300c0b10f0030307003d1101480c9081701d00300d00400c2c045089401344032035890303c941d07650302c46c400d20449800c020460701d5031a07030070080b295501213107200c4c4c240900e030440f900503210400c030301e080740c60800b40740d02d045d101e41101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 789773201 1250 789771951 789771989
    0x9011208030402182d01030c271406040c1d10140403030f0f09080318041b03020315030a02061b0a140303011505180f030c060d0f050c310b120f01 64
    0x902c0b4880c08039520801c01c0b2aa4402204c0d0750300c484040800c60302c027120b003408a0300002c400700007030b42405007800b11030801a203c210f0800352214003048905030900340302418401810b181c004200000e0b510a4103000108014040741e5542641c0141c2044001c078442d6050130b09015030002500c19026a54100120594100606a80c2e68026004102e4a82c84d0030850340b0b0a5450300d800c2101106460703602040e050840036000360194004903400040940b502e8045a003900c0e000410100c541d0300540010300c2d04014042415002c10b040c241c041c070b180300b214031400000b00500e501c210442b2194000d03603142e506280f014003981e0b40029000b000c02c00305110541c3b05004d11080110b03104402c4540503603600301640440d08080324a410300368000303804682c10744072002c2030300906890a6042420812a9036242801c2014011141010700313007030b2044210386080c60100800c3e1006142d003240613110075a6030798000703050b0340401002e0b00c2124406050003c50300001c290302e03004d4105020078644880034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 789774451 1250 789773201 789773213
    0x5010b01080708041101050c0a0b0105090a02130e040f080f1e1810120c020718200c1f140105120a02191a120609011208030402182d0103 60
    0x4e003001c2c0c060b080c040d40d0841541e02440440707550342c8903503081d52402007a605007001d003d1401d00c62940103001180000303801160902c03ca50030200542440d2000c2400e1005800da074200c0184100c50100b1120740b07c00214030f141024103c0b6140c002005503550303001042c0b0440304668040001008481403000c9100140d030701b0310002c1d40c02000c0c1e4449440d0b250303111040b02c1c89031116982c01155481c244403039021585c0490f03481c2c1a03c1d1104408098801412001e8040b22942030030a00d03200161151400020300400c0240344040b1070501720385a4110300f4107002d030740314410403c018009588494817501154010340250040000311040004012032400994a800d42004000d04c5281110181100c003024060790310054420300c120406190041780c0f50f1216035101c2038151030b00d80307155800100b403440d01001d413a0586002c0c102650380411f081e80d804090f07400252040f031380101107808012035640e41c2042940300d0020560944988200d80300102854011404103101c0000890018400304030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 789775701 1250 789774451 789774467
    0x90b0103180f022b030e060a020319050c03030f010306050a0b0f060f120106050a02060c03060a0311010c20101106041101180b04060e0111070b090103020d0e010905010b010807 77
    0x3800501c60b92040085100142c501a0fa14001d1020b9240c128841e414100700c09000c3c14031035200307448020000381035004100e82c86c040c8003100b10040e4000c000c041c2c60700521600c1e40902c030380070b0706149003025800c0b040709045400445600c1c5200f0508030041041c84079501410b500444402810008013001d080801e0606001700700160081100003908410700031036804442e40ba507180c07400100e00b9611110024240c0d40070010307000051181d80041422040094211390148400400403c1964950b50f6840c0d0b0b82e007900480c450510142c000114003003501940b0000221200043c070000440403041005071388144142c00710108480c1058100e400000043c28503041904160180c1b4104501e40040b5002881c482822040c0861800001601c3e06040050300503201140c135024052907102004403180514406412020343c0400000c0003100394900042ca100300040c540540340c1295020a802540d0700d212890030581e55403e800301c14810203108031003400e42c007460101990305040e074008203585 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 789776951 1250 789775701 789775703
    0x6011e050906040b030f01031a070903030804020d051f06080c0609060d090f030f0e011103030619080d0e1504050a1a190e1e060d05090304031b090b010318 68
    0x20006a01d4105507503040a56004007291680c0590300d03d170100800a0b094000c1c4400c80d40c0f1080c0080042d417555151215070302c100c00e26542c103280c00f0315545003110182d070040d01c2680c1010082c0007110100b2420711880344800d02d58803a10040345050000c03c0b0490b501d5a12080480d0000301d208030907580c0d5007080b03c440e00000c48900e0745441401100200034085143c0c010701308610989035008040c1c1101511900c2040c60311601c02e5001000d0064038011031400f2444c0d295001007000071240d162a090b8100e440d03003100180c110351602d07228a9483d241c01480000b0110b00c241b502490b0600c1e0001168642502c2c881070b040c102880c101c00b06030302d03100b18003c2000a07402125003100030706441c404e60ba000c5e070149010030b00d41c0102c1d22019080c2c40880364054001c44214100d1441c805043ca00c4407800030010301103d01d070817413425179500200006804400c40d400200400004948100048001e60104055103007075035280060303500484440b814103038181030a010308002010041c41400c244d203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 789778201 1250 789776951 789776957
    0x6051503030310090207050c030a150509030a0e0405090c0a0b09091b1b0a0503070609050105064c03020a081501120b0f12070f05031501060e0d06090302060f06011e 72
    0x31b08540e1601e6410000d01c0c000c4581c051060740b003042c042c8840781068080341c4448601c10001038454081e03458680c13003000c164801141c0380044409040c20140d111950100005042c0c078203010300c1c600000c01201c0a544050104000802d201c2c0091038132081040d0450220031548144200001d1025614080e001480a58018045070000d054809210000d42549d001c4250b80e80c4000f80d1400c10000d02155901341c1d03071586080005002400e0200c4e403000d220f00004038464041800d1006500e44508800e0901c0d441080745202861200c1515030290524a1603203002d81c5030b65504000410480c0000c080c0e09420a10b05c14000450740c000c00d0f0103c002c0c0701d40740c001c03a9080c0c42c1c00116482c2080602000e400000c105983d003020000860142e050711115079440300f0f190f03518020180c0d200101400400005c1e841030040084074041e014051042e20042c00d00034401249444420032201c10480940150700a44100120342c1001600b01e81e00c4036090a1200341503241c040e207460803c6000103d4824 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 789779451 1250 789778201 789778207
    0xe0115050114031614070812150904051f11030c3402040c030608030c0f071a0316020c0d0809091605120a02042c1b0a0305061903060515030303100902 66
    0x3d5809102203904061f00007041c55a20910080403484210341190822098038901181d00c05900e4040364487c001c81e0441c5c01001504885a0340500303400c2c1c650359403109560f640c6800640ca0b0075480c0914800c481c0340500644400501c004080f806081c194500c5070700f4442078842c100c034814002508107850301a980040d5802c102d19058000305078a80000c01c491001241071511101d0000300000d103036145a068071101c6559481009803a000302402241c007070003e10001d0b0200c022484000f001400d1441210805810200810301c81d00400d00180d42c0c012000441c18803c3c03c21080407500a10180f0540e05003981000c03004206000c1e00175241024111000459401d200540655010300138000b0416a0503032140941954007403908210b00226818400051580700c81440c07420342851114146e0340f80c80510a0200c00610009001d03940c004074009080c1341c0030b20b204203c2d201a52103480b00159904240c1500041c01081e404d41e24840e9204000308242c400c044640701c8101d446140b405030f1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 789780701 1250 789779451 789779477
    0x1512030509040609060b03041b0501020304031b15051e0909040f0f150e01050c090612130c1d0a05150d0309090905011506030c0f050703030e01150501140316 69
    0x101412060380049440d0b405c0c0203000c41c2030f513a141d004601561040441a00641c80c9101c40e98403d0b481d44500350158006100410100b1414600d42d600c407542028510041600c45900f815801c290300c5100c0f0014a0105040720021480d481c00785664840a09107400c28030008001400c640c0024001403000e12205032100c10401c120b60052061507120300c0b00c1c081003070780181d440b0003007a6025071040302d90f09040108407042aa10101e9600c40b802501c05403420240b0904070001c05005013031000c0f52600c000c3d419001c40c0816840101801449a48060303001c6404452106104003a25031b14140c1e15100c180140480020300c00401080241c0c0d0584a40e007040c2015150180035a00815a01d82030a159500300541076100303080c0b0001480e20845055140d100807401c5600c0c2c1c1d110390307011402d103c01d6404442c0c02040507080d1180f080c40c0203d0704442020480342501d400c60035089280c06500414007666803c5038040f51b135400451042800d41c90281704400d0418a001c0c940c50620010740300c00c1c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 789781951 1250 789780701 789780709
    0x140a120b1909050d080703150f060c03090b0304032c0901150203121305070e0403080a02090d021f030b010311030402060a0c140c130c05180a120b0a1512030509 70
    0x18002d180c01001351102d40c2e01c00301014208020440d140c0e4006803600310301360a4100c601848001f52190000300d6000107080c0702c03060300c02c4c0101640a409001d0024070001d0390b001e0440045228620030b03a1500c80b4000e070301c1c0c09101c4081841d2005480440d5031440100d271502d0f0700c800641119240c4c0c075440d122840510701a82184525803000701940c0c0c440d82000002b41e141100c103c0b50512130300c01c480c1d0181e618a60741040c1ca500340c8005001078004030100d080043c0540140500070801042e0038240707545680024001c0b00001c1c82c1100c14a250040080407035010312440007142001e007018840080d1800b1529528440180028401d40c4049010b00b52544903071140460b09071303c0010728070040f0070200015941c0d80081c0440d482144084e81c540c41d000c2d41805145414805902e826051040c211094448644a0800c150f0419002c00e000151111040c10b450025802071003c0449400c1c1300881009403210320100c440324010300b40b820480003400c004442400f0380c140c40e242d0b8a070300c1d9110000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 789783201 1250 789781951 789781961
    0x1503010503061f0f030f150c0203071203110403050d1206050105070f0c05091905070c2f03060a020a0912020a060f090b0327010507020d0c02041104140a120b19 70
    0x200358100d030313500d0700071040060410300000d91a0041e80300b891f113000c15144d070a090382d0200c001840160800c1c000c080000741e00841c0f8841c8a410740c00c0100d0000510030b2940050f410a03031069455601070f58008110b180c2020503121585401301c3d080c0000c50071300f40003800e54418904010306000780b81e03141100703219011a000d000341000404010480c2405d4440448401d017940e24414002d14003c00b2a903054041c00e00080001e80c0b201d040140c60003400c200b103003403107089412585851205120b0700c5480d40c050240500c159032082c00140c8417025a540101010640d400a040149038454040d0250703803904601c4084480351315100b05000e64810086807915680c3d4000b410b02c5501106000c0c445020400d109000d03024403090100340128050140d0980b01c040d1201c201681100b220441382c90711800c22038141500140010501050342c1c0c01016443d03005501c0718402c0c00008045185c2450001c1d4400020803440c0c5d004d0404040c02d0b04c90031110135014191801107403031210407031282e000c583c1003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 789784451 1250 789783201 789783209
    0x1515030803060d2d050f01140c030621010c1b0c030605060114131a1806030703021629090601060e040e0303071d03010e0307121106040f021503010503061f 68
    0x1130210319006848a50030982d41690201c03200d00440c00c0f0306030b1144051107111100407800580081c20b0b00d80c01403c0c04982d001600c030a400541100180d00e032030184a042084803080c03400000b07800034400c03800903c400300851003045082c020394202e0010410202d0102c058a4001c01e0015841e100d44c030040e28a540012040c2030381440100d14604140200d015090803521941d00c404c01c903c50502460f8030328441e807014098880000c64401d100303420b00d074024686c490300c5030400619004a000c40d07040210500003003211460a4110142c008503041e981e40120303110403059079101d6040030b80d5010b0316403805002d110100710800100104965880d045104100b030040c0c241c1e6542c0c10b00c510020000746001d514005c1000c100c60180800342014807a4488001d880301c00b031420140e50f540c8004d051400529280c2c108110200c124690035818410340e40600d03c18180050940014410300c614080580c181000d41502031004008030340300840d0303c0c0d0f0702c030420814485071110004c44130200011f49400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 789785701 1250 789784451 789784493
    0x513020c0f150f0a0b1e040222080f0606180603031c14010501091203080c07062d020405010e09071206060306060e09011202010507051005041515030803060d 69
    0x18010106400b40002600503190184800800e03503910f1410707829100c0716a00c25030010780c08541040c0142548041000300b1600400151274016402040c3c924080e024800e81050000002d0400c410342c01000b10550502040f0040d10940c50130780000f441031101041012881c8459000061459170700b80200c0304854101c413007200c5105443d002d54001015800c46c8a8004003802c000803030550300520361301084030314501800c105020349076070446050340090081c110000c42400180c00144080c040d48500008461480c2c01c0801d45200380e8800e02c80007601c4111141c81040240040d99000041d4040c86000740c8440e246074558803022207400e405661481082031401601045860345604104201c4103150360350140d07281104100046440b0a00c00c1904c03801c80e60b110300006500900c0505021401501034411103409010140c0565038115022504003032106101c0c1d0410116125881100c82c8400590b1507180c00c60361111403c0c44041d01c0e003131107648503211300d00070401c254a408180301c08100b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 789786951 1250 789785701 789785713
    0x80d0908120108010e070b0a122025110609061201030615050108150d0c090608032104022803050f0d030e2e02070f0c090c02070513020c0f 61
    0x201401140782401e0050041c1542022000440b2034000183c040170f40d201900707000d2038040140010795100941000c0403245e9034880c1e204210810f020007000075144092314405980300b1034141400c5020032455003c2c030164185d1f0444201040054001c8c41e00c4071000c0d12116076070f4981d100050818050540a40010045000040104103803904034058510305105a005000e84500040d10103110488081290601100c05a001883d01d6140d0034907443c0140100c030300b00c5440b056880240c1e03e07982c11450300ca134800210a1040300c0b0561001403440700180700c40480742000d5000079140e270302c10307404448003040d0855986401e40c0b0311460305c4000c580c000300300c64040700c494101c1902c0f50707070b210340c844023191400c03a00021008010954128005650480d1182102c1482414800d03000349030000e0051942407180b4000541940348200d030700ca00400b081080c403454500348005070354541400e80c0864001007410416515407480b0380c040d8400b103090140c1c5034506400036603e056100e003541141742c4100c1d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 789788201 1250 789786951 789786967
    0x62405090a120c091107020d060917030c040509070c03082701020a0815030a0201020a150621050111040501050d0203060f0d03080a0609090803061908070902090301050a1404080d0908 80
    0x1401c0703d408a0300403190078091509000300044440c0602440030f0f400200da801321800141702d651051522a208400907604000741c50fa1036007281d001103400c0041b4920000d0300340714030310b00030a4641e4051506e1501c81e82c03451143e030300140000c8001d44500044200968010780e090880186941d01c1c802e032070004c54a1b402283e80c001d204200a0f142d0a80c040004615120b41d400c003c0b4503400c0e41034042e0003d1121000079622054102400c50500c1e05040d42c40a02040404c4c40005401c51004036101c11588140241080c5084445080180c81d12110800041010741d0b0400c085d1114082002001a102c0c3d50300381c049442080466142503000c11031910010400d90440c0703200f8000c041ca80c2d800c000361034491366280102c5912041c040d203105070510024140340350031018900d503402696810f65a4580d2a2100341c507002464120306a8182c010606035000d040034814554415403204003402121039110064090310030140005e00f00410002e09807840e41503603044108a00e40c009440755803803003a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 789789451 1250 789788201 789788213
    0x913020a020c0a090b0d0b040302012a021504031b06140705030414030f070b1906062006060901051c15061a0a080c0a020705030f0a0501062405090a12 66
    0x40382e0305881201d0401002c10046884e1243d403206141c0074080841c20b10190305c84020301c210080003102190740b03c001002d13220003c03241801c16528540304541440c004000e020342401a05c21401c041520301c00c0810010079400166400e250b195011128045042802c0c1700d0041c1c880400300300844000a814051483e500400951046004000c00250140d45140107500c038842c0c007500c030b410100b003444120042060501c40a420402c6050070743c41c0b040313000c103080c0e00b42e0720180e0000f03020030220480349440e800959a0081030002140203070880e40741140000e1107039681801250b0043d520002600350041c401500b81c4400e54001c01c16944034408007000d00090701140c007407c001c03202d40e014a0f9182964490554103081030316200c103041641c1f021184031305600f140300b0103c11880b80c0b080001d400d40301404111342c00c81003403010740f0341707103140f41041405c0d2440c0e94845071f01c920500314010300004409104c107942448034a005d581d41c0005000180c0c0448890300030b2410b90490b00c0081007000a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 789790701 1250 789789451 789789463
    0x3210315061d270c130b13050d03030506010210020901081329010303020d0504081f18081210050904060e0c060409092d0605040507030b0c0a03060503031e0913020a02 73
    0x914507288403084d0354424400c5418000c080070f44810b1801c100d0140403901c441c4003c2c090002c40040b001259603a0f610000d4002042020706030082507580c07062046950781800308200030040001c0c10b500e40301c00000002c00c0c00500801704508420195203480c00c00c46219045500440d0000c1403004141c4102c45003483d0321800c0c401100940b15064000080c50300401c2500c0444202402030307c1c12250582d83d107074002c00d6182a0001165980b01b90201e202d0140ca180d52040b401840c40c00d88807148030362000c1d95000701411020804600d140100519556410901d62043e8051030105003881c1d4100d8051424280f4050141d00c090702003008110340341b160b404944403a009420b99801140742c90112905c048007503034034140040854682002103907036600044d4100c1c0c4100c0449903995a13985940f94216400d84140c07210060000e00c01c00420350602510000d400128083c40c03815640340403002141845943c143c001b0040030400c0399081d5a1042100c0c1e0401c1092005d6648114080c002501c0305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 789791951 1250 789790701 789790759
    0x30e12070e07020601080106031a0601020a050d0203091e0901030f05070905040f0b07030e100e030705100203041a0105010f0e01110f0610060c02060703032403210315061d 75
    0x4c8210000012a40305c14018803040320380001da61050301c1ca0518415047e4400204224194401c00b400741c0009002003280f440e01c42e100742c2c0030b5629000d691042010b48071040070004c2401d0f061084030074090791504070107070459611030340348140441249045810300c04150b0040201c40e280500f04001e200d00c2c460001445445910b40b0400359848600070b40440346c80c1c501540d4658440ca1601e039100c50b0302d5006460559941003100c2c140742c119503c0f04d01c1c4c072084110b21400f0341c1d000700c11303c4200414142c0c0111214205814060658100b800081401d000402a0740c10031817149942e4000764043c1d0500b03404401c048090320f0f95403094180c09075580405480114619800e200b0001d036240c0700c1e040d5110721030f600130f108910f4041c00c1c0e04c0450140803140d15807010f103069010f00c40103140c86002e6041c010b5100c2d200b203249544141030f21030a008020007040080c1030401b5001183d40a0f80700150060b00e19034100500c902d40d0000002c10b6401040d010345820900e926000c1144075a8074000754032035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 789793201 1250 789791951 789791953
    0x90304090518060402060a0302070b010b07120908030a0509152b090c12080c034515090d3f080a180f0627030e12070e0702 54
    0x1d4980b80c0c2c444941504a085034807058000802143c010325107007000f046900340c140383c09401c000e825114411507401c00e034072054030900700003450700070000c140700009030480007428088291494041216141c0c0f1450124404010001442e030040340d5941c0d0f0132410205415448035160800e02c900b1005d40718a140c0701c0415040984003041e0884054040c0036086903220903c0d50001d0700d030a0b401700602d02d40c030300c0840d042d54040c40381c1080b10202b0405809071020480000803500000b0f20032820b2510f480c240b001a4002440c0548115030128145841c440026540c00300c0100c14039004d0042c60189082c100d5002d80b0150b912802d0007802d101005a400040030194424604000d5040404068803241e00100408203205035040340200030066000b8041c0c0c1000c035809200c0142c204594003001812907403419a03000c840b0910000303214081d614204101900c148103204c1c0c8080003480c22400303005040000c00c035003001e041d032950340c9007000e00c080840403940d94548400c04211249030480d102001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 789794451 1250 789793201 789793211
    0x1140903041505030a061d18010b0a0519030b19060b12070f3c021209120c0a0305010606080f040c120813090510140315061809030409 59
    0x40402004440403103031a1002d40d00c00c01c142980c2550036401c014484200c0b10b80d501000030f000071680341110950b25080b090481107103482c8441d80508203000603600200d078941040c1581c5034a80c18210b00039213030b0032102c07100c04191b40380840448060070b07000181001c0d40300042c40705611040c1c0c0f1460303c42010080c240044c51703c504d40c1c07007420b0040300b080200000560000c94180d900412140106161030302d072400c0130303201600309000ea00d514240c0c042125003090084000b851020800c1003d620036610141510140030342d9008894040c0c40c0314640f040a07504840e244000003005000390042c0040c01c002d440310f55a0400301d00811580c82901c001c6a2a0307400a1031401d458105248a241d204010303621070340c100350001c038122030300b403408956400b01045503448650804540c00018039070700700003107014502a1800981c514040d404848500645035800d40d1943c0c010404801c801d00022445c00c0b0303036581000084401768110030001c030180480051014114000c0000e01c140d440800081c44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 789795701 1250 789794451 789794461
    0x3070503030304200616030e0f100c081c1803020f0d09090b060d0e07060306051203190c080d39030e0f15090c190b03040c1203020114 59
    0x3860780b004407402003400300300302d800d1001c441d07086500c510020304c090411410000100355001c1300c121401e05c1035000c03880c424400c244a103050b148010590505541c822100f0300500c6024041900d090001494110003003101030702480a11245c14007454101c0c401d12850183c44400d490f0749041503015001401a43c003010842000001c00c54240d070205c2d6220000645450840c0c002881d00c03a0304a98040750411181823a80d1440c028034103002c003045c0203044164501707400607003200c00300e0388060f0040c040d0510500850307070080285c48180401e580d50707226100050000f15912000200e004140300404680e02c1e031440c8180e84842e564642050300c1028404051110003442c135801a004268001d0249400e0b043c02e10940002804900354011602c1c01100040d411741489481502c0340704101003d020040e03000e00402420210704025203410a0303400c2400c41c0041e28091500400d01c41620000120302042800302c0020002c00f030014040c1209103151174000d002e844c90031902c82c0b4144060012030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 789796951 1250 789795701 789795703
    0x706050f0403060c0207050409210201110d050a060e040f12050310031101020703021c17090603162105090606013f18020909060103110f03100606020c03070503 70
    0x185003040000140303041c40e20b96901d21000d400040032080440c0036464001455440e94091402c4540c0700e08000700000035201441c880a00b070041c83c15045a04081103680103005c0032044580d480c0d105640440d0701c0c1c2c0c46c41e0516025100075400b083e842e03801c60007004248108024055841407140110344456413101c04202c4003804191500e070b00d4484003540400c00602149031a011004060040e00c0003c0d07503d4000402031680c0c0b000212010f2100c0d0011004c1260a005689100032100744003410070070244003003155400000c10507100800d040d050403108902403d02c81040c03801045040070841c0072545000040e2800743c5003034410f072140e8800300d0165070040440c02c00291185403402101c070a8880d1583c2c4d502d00180f003400414901152010b036880c943c0c01010382d01c030440024100c0c3c0d038103d88144048031308000c00c092065081031005000052000c841c030b80080100300c440c0a075900401000034202201010400282d502d05200000c241e074000c5a51014108100d050b1080c1070f5440d8185 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 789798201 1250 789796951 789796957
    0x1201050f070f0f0c051608280c03111f05190c0b0406021303020a150e120303010b03070e04050f07121a190b0c060402040b0604080a02010e0105090411030405070605 72
    0x181d0702180400107508100c1d8810b252110713a032405001210350707202502d400d81024484540001ca20340d0041181c5c00884020014080804506011042c80b00f00541e02e8440400304a4007004000c00d031080d441d900c0320b96440c0d0011400c9421000d00c8017090000c89805042c42c2d010324001000903443c040345005580c006d0500785402e0382c114801032244e40c2c0395030f41c00c00258816514a030110000d494044050f84400304198081c2400d0121200d0705511150301604142c3c82c400002e03c40d0403011a45175004c0b6020059070704460001c5400340e203a031114201a03031400510100240c1041c9400d04002c04c8942100d01e072401109180c46440141078000c05110640380602d80c40c0c43c0c0a240707140f42d211203042003214004007212108441c80b0050311070071070008607070111403c0e2a02d07900c41d80070320007507162511560402c038108807805850f01b89016541074480040780b1000e4140110f45811302000d0340100c045410b503040c02001084203004600010643c0c0d00b083e00e040e0f4440c85650004a4514000c0d411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 789799451 1250 789798201 789798227
    0x180f0a08190212070f030501060f0609030312021611010305060405071704151103072c01122a1101020717031e01120516050f0d0f021201050f07 63
    0x9080a4601e0080901d038089003104100e0b0070040214058000440030700081002d05100b22101d108a031440c249242507440581100c01d500d01c425204010203904080540c2c100c2e030f4541001c0000e0a01c0180300c9000340181d201c117580074030710704940c0406c2154030242440620800d8070104650b4442c4020f02c012100e0494007032001c90414201c100450885225860f0301900c90042c40b08440300c8511490140c40400b1035040b044200031041c0144d072134010301240c0301e40340c81071080f01240c1100982202c20302c640203104d40c1070200c020320620840c002030b0042400408011043d2140c4405d0340303145180f800c041e4950741e000a90303404840903071540600844120540000041e002403401040490095102a141d030071218070202240b00d046030200c030403d0003000c2c20040c7c00c41c4014641009070801c4084407030150000710003d014003480d0b0716030007007502a00c000e135180110300b070aa103012402010400700103540542107010100c0c5611054020510401c503e051055164580100c1903a4451030780d82 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 789800701 1250 789799451 789799453
    0x106030308150a030812010303020613021806060d0c0807090b1806031806040606030201090e090d0521160e0303070506220f300c060213050303180f0a08 67
    0x10114542ca07982011151104400401c20303441c05941e035039040802d42c410000410005981001041410740620030582d00c840c1007415021280d025a000a030801141c404240240c030b100c00c08665251104000d403250200c000c1d1040054032602e45010741200300031202c20000404a48000c541c40c003807441030b84e03441a0a9004031813066912010130069420003060403020860b40c1c040e10410643c02c11a00380154042c41c400103419003503000042c018192030b0000c141001c100024008107001c002040e850701c83c03040c0b501549032441e2001d01c7e55800041d5000140c0d465610b81409007003c1e1091920103104030310384032a1604540d00c0b080c141c032402504005802500005d0029168481c1c0c40c4004605034500814410285202c1d6990410042c20480c1502c2c03a402104415030b03030101500303c9460703d80410344001c142140700d20b401094441500401071071240c000c074941301c0002e207a40d41240549402410b482d101d0a054088050410000051500c6001003442107446400c00320351070700544013224 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 789801951 1250 789800701 789800717
    0xa090b0916092c1f090b010614090904111203040504060918121206060804030807091202060d0204030605011715040812040f0206180910080c01080a0b030a0c03120201060303 76
    0xb600030841448072109a001d010b206510713400d9500c030540c0360a44100901c400075924050f801c00c200440740c141c10010034454038020030030136541204140c5200c540210b0b490720071342d5101e1926001c0c071074405917a150000c0a000b0b140d401d010020025005550b026a004c000305a0b03941d0000c015100e09080401070940a43e420001113040790f9a0f04d01c0344903040c2400303922842c03044009400c69200c2d921020024140c0703800d0108041c0d1100c10b050f0420072034900002000d083c404650008100160f001344a00000112070019510b140c056074025030700180704202941c1e4450188010944d1070408040354040d0045403101440b072104203e0280c6d800042d2141000000059510400c001030300950fa01954003001c100181c2d034400c001d0446c2c010300f4441e403039040300c2c01003400040070380940125140000710070306000e100d000141c401200c0c0400d18210085860b0809918020a1502101c9400d4050b4100300000c1c40042c0b0447e0701240d10596a40042e0f400c1e0041c102e0884020380801030000d00300b9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 789803201 1250 789801951 789802001
    0x1020a030614090c1c0209061b06070c0b07230301031101090803030103150507020f071401140f0307050a09171c02060613200d091202240a090b091609 66
    0x102651081842e85d00c801840d120615001400a80003078054202c8102030140407646105c052251a400c1146401c0c5200207442c250703202104010014036030001c00000c03d40e05202400c1d00c40c1c00000181480035580e0390ba5849080420310507001c41291030210311000d000140e07070748001080300c0c1200e07000a40041c81c4070b144903c0b48003820b0058040c204610821800d041070100501104005107d20b2801085101e1a400054a6078110300801011410b080c40700300f615848510845e5400821490003a40c2d034a08500c090b110156250040302c42d00140a6895001e6100021407110243c48500d02c10813151105004996401044411580041d0700b580c18001081c91034110075842a14080c59881c0142a100140001d80160034006440d58540100c2e03001d001c840507181500e900180302810b2081607040300152040c0c0121110580e1840c604005600700a1507808500703184d40c851118203086c10030f890007542c1c50804201107492100d10394800110111140314001c3c44a0350352010840d64004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 789804451 1250 789803201 789803227
    0x42303090108070c021207090b03010c09180905030309010c020111040303020a02010c080d0e1014040b190216200f01020a030503100806041203050702030702010c060203040201020a0501020a030614090c 88
    0x25100d4000e00c2079485413a4016038980409050845080009021003440d081c900825101c10041081c003d92504038200000c2ea4000318000555909032403250b00c0c0c0e045582c05030010700c50000040c0c91400048140141000706400000360104203074004c0c0b0809000380a4540544640d1000a0244e400406200010350107074510090603070154140d182450103252490054500c10a210000ca40250840018420740b0f4410809540801d907030400c3c0507d000c0e614640d5941002d045180d404070303102d5210441040540455542e26881152501c84101318640f55600500c40001c28a1145c000c5104183c50308288100060392201603004080304080798806880301d9101604060b005503800c000030541c00e2007004428010f0344611f80d4002c04480e06540102100c42c05041441190400c018003030260384e0020000001c41d03045400140c1d01d845620042c0e151400d0000c00400303075400441c2c07d841c1603030940d10401c201c5401c0344c600e11074442d000080100200040fa03c44001d12403d001108954038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 789805701 1250 789804451 789804467
    0x16050f030a2414030f060108030417101503150509030f0a02010f0501081f0203070f0e030f06010e1f0815060d05031c0c030b030c131d060423030901 65
    0x1d041400041c100002482080c02e29815070411004115680c0b00800c1d1420f003080500081807801014005650424107801d4a03446640710701d101c00455540001914941889090b03008442c0c20410049003216030711040500c4a40d10003500d4440c1c007120740001808280c014248501440c601461601c0054880303001aa0060300200f0119940d907008103803003000910846001e020210010041b2280704010480814000d0b04083c04560050060040880c0c00000e10703088001ca81c1401058581c2d1000400d251103011080d2003143d10a81c00001012091450801d00440742c0d800c9042210400001c1140b41c2d02c0c0b2403140700010b41c85011620b181402402c0c0941e000403009120701d106030041e407519480c54020380080f4650b000440f6203100781094070b02c41c0c40c600109a060610821030210300190f00c42944100e404e00440c40055141c15403101c0c0d078809d494030510030030310203403110381401c0540e0380d090300300c0d0200c88a03002030071018034001d034030b14180a1401c0c442d0001c520b402c402c0001100c0140c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 789806951 1250 789805701 789805721
    0x10b0a15052203060c05040303021b220906060b0403020109120807140d020601120f0b042a030b01050607080d090c050405070f08070f02070e06031006080616050f030a 73
    0x71205110301020740350b414002d016000c15084001c00490f00f5820940200c604c004580c1c014032900b00401c00001350041010342620720b989420020007036900700860403005242e581310075500f4460544164032855980700c850a43d000f00802c01050b902e0300c100c40414401c6000c06400b0848116041198a0762484640403842c41802d00605124bc15a2100c034042422151a00550040c4000d4034842d41d04104190050901d0007000c5103227205907e0300404011050b001610048800000400340000c14905000c00c240d0710741c070b001c1078185042200d808248076010407507010b900c080c0000398903e000300c1920461a0401c4690346000704011381800105610300080390a00304040c4000741c1591a40b045074400d030038940310281d01d15404000100364402c0240b03002c0c2070210410903588101e50000c1e150094420115160119841760710020380382103000461594024105040801c01210200b074040c001c043c420040c050480300c2d8403050f40c0601454401aa5501701813002544d01242c94210310201c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 789808201 1250 789806951 789806957
    0x70905090a0f020a0207090b0a03080f070201090f08070504140714071104021c0f090b13060912031407030e030a03020304030c0611040f050919111b060109050603010b0a15 75
    0x203078501140d0b00140d0b001916140050307040300c0402c010034407044c019059400c8044034610390310342c11581c90501901036100344820411010407180c003164041d0200d007010f4814001d002400694449007166591814054035000340d0404106031011101c042946000320b50581714003185560400045c2c0480e0042c0401ba240c2d07000e00702d56909585c4440c070080800e42c02035403210021102841d86003040d51400e070640103801d45442c40c11804a50024186a08140111060ac00415842c03c10f20701a20742c80d030000d808050901c401d6461142c0591080d8209403005aa03050705a82c3c00b102a002c45010f0245468550410004000c40034070940c02180c1c030a12908040c10840d10589610044803141881c44c030446d02c0015003482210250301900e4020f183c125074501140c5402c41e1070f40c007990005262801e00503148c89146510141e0f80058503e50850500c504640b00c22000150740c0c1e808003881040000c52a10300400c90302e0074103000e111030498001d01051400e17483c2c0364148030407a05a0303c2d40c100b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 789809451 1250 789808201 789808211
    0x2030a080c0a063801081f0306060806060f010206040803010509180615030111090a0e060a0503030307270b120709080d05120c040e041217070c0c0e070905090a 70
    0x1881620444909450002c10f1a0304d0043c000d94000302800b005154001c00c146001100131660f82c17080001d0b500c9040d07051355900f540103d26044c443c02a023074000a20103400c010b00840c0c20314000401e01d01c100c90455501781e41c0002500166103401040d140503060b503400308018007403814070640315a007210012900c4a44441c0d40030700705003030000503107070306443c44000b05c00a007080c030f802d0150701480d072130b6400107d06d0400c495001824803042480b807a100742818400054541c0d4400350b00800411014081c3d0740d03a85841c07500102034a10800040403400300b0399400101c101c200c4110b400998905404c7c140c03810424813210030301684010520010440008400306050406210750380d050101a2915603c0c1e107a0313000c1c4504040c000902e010312001080c441084141401c584281e0416040f8840b180110000d42080b40c00551200444480c86006024082e43c0c2d980441c03903100d070501420607004070a403140c0c3d035a004021b0640709400050016001409070f0b14040c145e0030b030003031603451000279 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 789810701 1250 789809451 789809453
    0x14030c09010e070329010c0c050414040b0a110f131505040e01080c0a052202030103080a0210090201050a0f050c0a08040f0f3023010b0102070302030a080c0a 69
    0x80d40240c010340381c00b079408024000101d816000368520b0410300202143d0600549420500340500035031000e040054006185c82842590360031807014007009030080c13000180075101c00b1f1410509071001c0f98090502d4000130b03a103160611803100c4881114007031a2420314008101c1001c5e0f0401c2d5040c410b85d1601d03950001c2c460086001180742c170701f1582c0f2200c1d03c8500d0038050151a0805a004103140e4118150144c000c2c0d458031500302c207440c400c64581181e16000344016120204040034441c1d814400000801413080b030381c0181c144501c49900302c3d0981800034010005417440c0000080c0072641c10f01051003264081c48001900c0340347ea01d051030608052040462900e044d00c1020390310365500040600c0a1140c2036510409402010071a003181c910301100200100c0081c01c0c1c40c43d68a540c100c0c6035a420407800040300d116900450107010002c2002d0300d642421001c0302c411b0130710f5881d241d0320440b59400420740e081100d40003800740008802940310201144d2022420340c510380155190a8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 789811951 1250 789810701 789810709
    0x11040f090506180601081203090f010c05040e07030b0f1302070602030a02040e0f0f04170903030d06090f09020a1401110d09060e01141e1b01020715020c030414030c 72
    0x5103006000380020501030802080020824032000d039207501c190800b60046c4600300000a400303200718805c3e14600d81d0f965501d01e540381044810814050b4550814104c2201158824050416145604942d42c03042d22120020380803904a400802d8101d009050003000a1601d540c040003030843c2c00ca03000d490007102c0c3e940c040480e8002c50701c480c1d00a40c01308041c08034003c514100c41c2d01000400783d55003903061601251590320001000100500c0301400d0360192980d0044c2a00c2c48140d018041300e888642020a0780c020345160700604490350320f419100c002125107800341c030031525009018804102d0410f05140c0358040050f40c06814803114030001c80c0100800c01034080604042e41d21300780b40a08016008180003645003299041141d403e00000c000c04000080b0780d20030006c11011808240041030034440b50080c5008411040101020b000400d0010340080807000c4c07280e85442038982201040808902404400c41d45680c0148000d01140c85e010b4008003580300c008007100e5440074224001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 789813201 1250 789811951 789811961
    0xc150908180a260715021b06040b0d0b04020403080c1f050709050d021908031e040b0301060c031404060e19060806010507150516020d030e0a11040f 65
    0x1103400050000c1e81618070079007011400c1c041001151030030403507880e01081142d8242d2400c820490841464041d0b0210081002110010425000043e455501112020b5141c20072421184000050903865510303914115084070195218641014103188811102c3c4001b401104c0a0036005036080001002140e81480030741814031004000704420580b0807644411100c2c445950309825007028240300083c0e030000c524400b44c07001034600e150f840c1d45a00004a070181e14a03140000e64070b00388030129000e40c000c002802200c51072043c0040b5079040e402c0c0102d00c0e1140e8407503040c141105000500c41a40300ea541807003d10302070b150483c03503601c1c00401c000540e070255100002240c40c0790182e00041c100301400040071b03103007102d900304c48910b04040034001400007000c440c100680050160b080204080c940242c44c44185c404006034070b4400f10780c0f642ca41013403a01b0000341c40303480d007210300d60b40c468000c41d242210383d100580740d0700b03000760703624260301d220002080c1d0301030b07107514000003441c0c014420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 789814451 1250 789813201 789813203
    0x1d06070518041d120f07060c030b131a0303070f17071b03030f031503060e1009060b09060901061b030e0d0317010503030403021f0302091005030403030f0c020d0c1509 73
    0x81c10440c8184403401c14a845010b407501c04400c40180291104400751740140c6e01e0441d000b942c0401c24010001084000304112045242d1003404050801c00000041e44405030801d00d640500421030b15000070141d6900807440010020b03410540703504000741c1c4d040c18100d01520075a940c141403120554079405d41440f03880c0c51242d210000314040050680c454840303800003895040c20443c040590b00c0543d5001020702001c1d02d141d4480604004622080207609030035210350700708000e03448080c0341541c05000400c500901c107100c1500030502c1c0d8900381c41064102c0307444d616400b17440c40044040010400c147e031410380600c001585c3c80a03554070364000e01344510f4031035610f881c86070600c1034513005001e406802c590f010b40c1c028402440187c440c810440080000e56003902594407405500320041d1003040c003003d402400d50625104002c1d0030801843c0500d10a85050000c2016094502d0444140c003544d0340040c2c4c0880001600140600c2c07458048a001d60070380d00d0068640e11213a0b06484031908 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 789815701 1250 789814451 789814481
    0x90c03030513090c0c0b0c09040f05150103150e150a080f101107060b040f02190807020307020a03030c03090e01060207180506030303060108090a23011d0607051804 72
    0x540c0c40d80c4154021581c5001c1e02442c3d104000030440c080000f000318102040c01044088440081071450364418290350b62000010300622810014117008400b0381015524070717000b800000300e081801d43c080d024034180b0b600300c0908174012031302c1c00c2c11020341050054140d80d00b0000c5000540001d4a175124104080c1c403640006008902c819030529140c01c0c104c0d4540c880462030b2503002d50291511000b00c075070b281d40084021a08040030701c0054018807450310b217600341520000d032015442101c1045082c4c0c015294840c40501da59408041c0d8491140c0c040c000d43c82003909030b052002a00a142d0308189a01078074140740342c0c036102c01e020414240c082e0011000350348030250070007142259203901d03940940042c1050005040c981e020a0341d90201405042c11301407482c4c00103403010010805001529005000c01d01440d00145801c19100641c0105c440d441d42043c01c00400030b0703604c40740100d100440000070844d550315240200c03810780020300110b5440007a9018003006a84a0003001401d41c0341c19 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 789816951 1250 789815701 789815707
    0xa0f08160807081b06012916030306053303090c0405043e04020a020a0b0403090609090b030715020a05060f0a051e1b040305010203040c080706090e0c0d090c030305 72
    0x1901c00358251134002c000d4075036203c14010b0060410040c0c0300b11b513050f4060a075030b403103802c0d0421044160040202603038040800c440c189040c540d151f0450400c45130155009508015444060311410080003208803502c5800c06443c040c00c0b400100a561160402c415070300001c0800e00058240c5078251400d641036060f00041d034180312003100032083d40d00d01c00d100e603c400c141c1100082e82003c0e00080c43c00c0c843e9270302003030400d6600c0c0280000a03001d607020410184078a45403801400c414010301600001442010000c5a0b201b090f00c2901c07000c550042c009d080051410b610b41041b003850b95490310440c00341c0051180003803410400c01d80102c2c1d411a40d6a51482d040c1d051314211131004064101010141000d0b08941280c4203990750000d40d04451a01c29440001680200c0c4c891a03000805540c0300004010500042501d2601605c01d002c042e00c0340240c0d50f00e000c40b1003109a000360201440b1681c041400e14907003900070454800020030115070841207886006d80c8040c2c41d803003600854000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 789818201 1250 789816951 789816967
    0x1104020913200705150903040503030a0906081e040609140712020405060117010b341a06031e070f081b0a06140c0129040e0a0f0816080708 61
    0x80d00c440101c00700c401ea4443c00c100054442507612002003056030310090b0148003250390110180101e41c003414020b82120354903c0c1540009040740058860b01c1c0024221034003040036a640c00c5038885000c0126a002486502d541e219030008146d100d0086a1030700d540004201002014040c01c8000c0c108a007000b41d91607658014081030328030040483c0c0c10412201120410884140003031815200c51030a602e03161010981d000d40c19118282c004224400074500006202d0311110351481d410b4455030451481c001c20300074100c503101c000d580e4945d040d08200c442c104400c1ca4520b141301c442e05e842c011a0b003032964038081070205520740d402a40380c681006407541d181440e00100402001c5d8103948804045152600042c055994584400000c072030001c0c4041804509401480c0300036103e0038003035000b02c074240034240d40643c1406114081c0b8182a0340401e00361020681003149070300501c225048003413542e41c104030b69000392401645c94072110b1402c0c3c0411180320140c40c6040c0300300d00c526070756108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 789819451 1250 789818201 789818231
    0xe0a0f18090b010e190f0c0e04050c0301141302070b04021206150423190614060a05070c0317070b0c07021315080f0105070315060c1104020913 63
    0xd161100c040e15824070002000060140700e00504440886405950302e0b1500b4001072030103a0100304080300305040c40c41850100d1300710742c0a107084140d15100d42c03158000d00d40901c81130b10000c1320380100c9190140010090112643c00c40c03050a43c00428111655021702c00c00c030100d8008007004d484603e02e02c0100720440c10010001e5144e80302c440003c1010345805010103e042ca102100c4601994641e80710000341c55610081c0c0140c407402e4003e00c201407501900011469040c19032402c9801d081c07a600040480c0281c0d04402c2024028141c0b524100c031000083c0c42681c0400022280304046d042c000000c906050504170310b40150004160b038910b0541007070200f0603000f80c2003461101e07040022200580c2d650041008955030080302156482c6031070016101103640d913001c0c0b14140a13036000d1030a08181135002c14414a102e440401024100d941403402040c1c09001d4240820341986092010500001c110354040d800140050700d44020107000c0380010000c04042d0200c00e032194078841c0d0000d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 789820701 1250 789819451 789819479
    0xe0a0c0815060d0f200d03080f0718050607030c170d0c03020a050703030f0b10082203170912040618091104090902040204080a1401150e07050a0e0a0f 66
    0x1220356440741d8449460301c044880341080000d02d060300d9010046045d030008502c2c0811081d004000d06100c074085d04001d00f81210444d802010869005e000071803d5004440540180010201007441c19040000340300d8031380d11060081d005e00c23303c40c2810000401880c0c0d54141001c0400580d0303125400b510f0b42409461184580c0410316006008403680c0c00d034840d058031003142c1c0518002c00d0b2035180c1c2aa0700010040612a6504032000302e1401a1181d048400a80104d02803403c91000440c01e0300140c49440712590010b00207000c02c910100c9003c28510103d4010800c80103450b683c05a00030030f0319166206600c0380011502c184108250300c440c1d05c032000018081d00905100c4036442210200040c032030380c0103010311583c3d188069000d41d00c56a041d036020740844000c4070140c1d16103080a40c00e0b0002414500d00755030a0101c46c0030340f82e2080d004c801c104c0314102d600422a80b103e0380d081e40c540d0000c080030010040c2c80594201d80e0b650300384c031040040c001642e00003016400d103003828034010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 789821951 1250 789820701 789820711
    0x912010615141207080a1d03040e15063403120e01060f09090305040f0e160e0607060f0b09012612070201050a05040f03050601050901170d030e0a0c0815 67
    0x82488800c40d00a824505144c1c020000d18004032255141d0305440d00510700000c00c00c4440402603400300040400000920950704801c06482d0941d541e04183c110604261035011f410103414003d003240e85e0740c10240c4403000c0c1d40071031552000340d5004a103018109445501540050200d011042d00d584e00d9120352061491820020b000302c60508a4a0805400c64031803101d08030366900b4000141481b4006540c061300002044280c200c1c0d0b10401a185840192111900321b400041096201c0d4041e00c1f4000b000c01e0301401c6641403592a89401c13000b8004a0a1500800c0d200e00f03000030350b50f44c0d90441c21b02070480700301306050306580007601645001d5040c0210740c2d00e41c005040c1e40c1800d0071a4050710181070b030900c0e10700c3e81c800078070008441c0350040c1d9020600310040f442022040143c04504203040e504203035a0b0095603a0396050500c0003079881410140c1c43c0c2c111845203072005100381c204601041d43c010845511134000c5e52103165040d00c3d40d001038030641043d481e2044003048268095040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 789823201 1250 789821951 789821987
    0x109030f0f11041401062006010e01050103061509050f0f09040615060c02010801090c0e090c04082109120708150411030a02012001330603020c03040b0912010615 71
    0xc4844d001c56124200d2040c0200014840d40e2400c05803002001036000000d22621401c0e02c002e565075200c16000320380280500c902207420a0800304840c2c0b100c04280107091110ba45204c41c6c01e1800081c005800107480e98660000a41404548185c45415145006610483c0f002440c8244180c5a414501203504010b04000c01d0950440250382d21003d40c030b064420354100000e81c8040610203507144201840119007207064102000039094640c40908111144201682c12003a580ca02000110324580c01e80f0076290b50078009004103007403040c240c001040081084030426903c85540b5880e0101d1611080e424145030b800300020441a5130a95240300e07000e400a084020031a400a030809540b180340b2101c007810368100c2c85031380d0360942040940c2011105242e4107441035902244654a4600801c079036500c0079900040e401d4401c0c401c0b41c0e84883e8510107103003440d00340b900715504c66200c007111b20741c442c108068100c2da05d0b1085c8944802800300c144c040d614812403440240549032085d00440c84 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 789824451 1250 789823201 789823211
    0x60302031e0c0a090b161e0507031211070e040f0302011e0e07121703131703150114220906090501081c09030b1305100203191104090b0109030f0f1104 66
    0xc48100035410180079405004140d403030a064007403500051400c7e50203051031090001c000300740a4005503c40080040d907032800803051180700300c59a1442940302d0b40b401e5212100000b0045030001c1d42a51030184a803002041031381d10140703007401810412010450390b581c0c80d403c544992108009000050800400c2802c01c6100d54560843d05488100031002e420400000585654000741e00c0307034049903000380c02c00c40c0c042e0009120000c607002115440823110080e40c4950b2158010761050140904580105140c01c420412540c090540e0140590151909140c046409503250150750054004d14100240e10340c0741c068850b180c5002c40d03080c000704030305a4400003185a40024500140d86e0002c40c10b104940311820800c3e6403080c10300000d400d5014202418405041c1600154041c54410400c1a801800010b005048404452104200300001c01040282c04001d8021103c4030710705050840c50310f80d5a413141003400c040080700300c5680c4010100c000800442e1802004000c4081d201000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 789825701 1250 789824451 789824467
    0x11e0f050903040504151d0a140f07030c020f011a030d0912020d0c0e0702100e030406081501020304170601030b070c050c0f06130f03230304060302031e0c0a090b 71
    0x5100e11450041e45e028030340318250400c01c4202c450080c40100800410109101c1580c82c00c560031180c1940c4400429050010300c070142907507a050f20703000700b01130721010119071150310302503000303152202d1001d040d8010b00c0c524464140081c402d200795001d60b41c01c00c104050380d21040506081c02400c1031814009501030600c05010100172190304254141d0b0340840b900c00a00340202402c9155010701380031041001008101e5a01082d55070310141c60407418000a6000079040b5148d000340d00451001440450000e03044420403004801580818019286800e8540c0c0070a540950302c03a00350045640803e00410811002060056000d0f08502e0007144c108565a68942c41784440550715200d10000c2c00c8501d21540d5010840c3e0b0f01e41d1400182c09001690b540f88189071036030034802603c0142081c00b405880c010885800741c0c01004280286240030300b080307001e800a40000e4945080b4082620800b00401190000c03240101019540c0316203600c00924000c01d21511604100202402440002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 789826951 1250 789825701 789825703
    0x109050c070305090f0402040b09040c0e010e010c02040b0d050f0607050702010f1d09180c040908030f1003020316080c041413080904020a0c050d020604050607080601050705011e0f0509 81
    0x24075919030525003070365144c000070001204203404c0d940640d80b00748000b0300000c5003103000c0010f040800b02540c0910540c140014280c507070100511150380402d0120f51040a2503200364203c190892004200182e84808000801c20070504d1040440f8603030f00181680c20a180e00b003000c5640100c3d1494050b1412030070b540000e04000074002030030180315034114000c44040c00d0b401002411140940f69026501c0c1ca00c0d001890405200d260f00c406002c0d0201365011390905002c1c0300150b0382c00c05115072441c1c81d00100c0f48c88010006040c840c075080145004801a40c0c1400006411071201d101d03500d4041c240943d450420300b208a0417031240e032034640c42e03000c040941c0b1019980310701c1410b0165414031443c1000003207882800d000c15809440002c0000c040e80d0000d54817a443c0c0d010b20200d980070203404500341d9449005843c05003ea0f4440400034041d40e104034809548680d06152150410b403003aa078042c02c1d80c20000304111aa08840528401414075106d070407042480002c0a10440c01c0400c1c1d51 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 789828201 1250 789826951 789826957
    0x60403030c060b0405240607211112090a050919020c030702030304080d0201060e0f0a0b01110d0306030b070212030f0411090a020301090f11090f030106091508060109050c 75
    0x203080c00444803a007400d11225078020040304801410a02180c81d00101050032881c1444c41d10004941c02d00014100c0c0c2030600a95114692140501d180c20010703000143d000d81c025240501080901c1134030104400c014001260b0310300d81d50503182e8440841d0001c2042010b007a8000c02d0041c1914030800001c551000102400c20034085401a50340c8114601c0b24154403880401035090b10001a0008941d00e0009107449640c94948c005c10400e926500340130690320303042d43c001032210481c0c004100a4400d981c0b0000b07464a050510000b1240d10f0301c0e2035800c042803401c0718070109560f10010405c0c1304114180d5544001248081c1c80002c2c82c01030460003600002d480406107000140004040022003c46610811f5001781001194035003414610041e41c000d0007040040b034142500c4080c03c402c1406860726682c0014000f50038180d00c2000d00840e160440c01c60b590564888900080c1c0708058890346d980c040360810348440450070800a6803a00d0010383c040c4d1251841e103410450444520425 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 789829451 1250 789828201 789828203
    0xd0c0f0201030b031e060a050105040c020d0315050901120c050103110417101e0b06070c0b18120c010215070c140a0b070818060601080a2a11100506060403 68
    0xc0c0d0301081d0f408685810700700c03a0200b07181d802d440d1100c01810400a501807180204030020320143ea203403c01d00007030310b50100007034015038008058042d1940c020f40100d00380711000b1584848007581d940010300029001c0e40102c55411152154000380121481608044c000a080c1800130001d91454865184224410055040050012405002000c0c02508030014010f0400d000900c814440c9444c40c0041c41420781c040d9203494449000e81c00c201e415101c440d03400031000c10041c2d18010701e00c100d591000c00343c0c0c02c0602c90b422804407141d4500700030308056480500240f901283c0400064a84041c1d191b0b581c0c0c184000d8402c014000e64407042e4586010f511100408280031121120762400700162001410070b0082800c00031415404065075105282002c11802c00f80030340c1c0c1d144d03a21038405880040c000340422002540490075500404144000310247c0000c80d44d422680b40c1c1404114080e02001449101070384081c1d00d0304200340346004201d5401001181403c0c00020300700c0c8502e03c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 789830701 1250 789829451 789829457
    0x90a090b06040213030f060b01020d09080d050903190302101a060901050c1912120504030e120a06021c0506100504090c03020c060412030c02070608060402070f051e0d0c0f0201 77
    0x360111284c0c03c41c400070340103603848414800e01c10341900c1d01601809600010300d00620030000c1012440c0e04c104070303134070848140d0006024420459802103030ba680c45040d0540c0c0600c030b400a0b00380303500c60400c80c41c1603036800380e4007508544000003104410307907403400f1061041000d0724200c2c2c05280d4404d000c440408209080041e0340f485038114090034482c648010b0320009540b00b40003004d100000403a003d80d00710b141c0d180301600540348940740c00c6074026100600000c030507003403074440b0b401c2022250314420581c00403030f400714803140d03210350907644800043d91521581441c012282030302e42c0113840e00b0060490b44402c1c0c0030304154006040d070059200c3c8010f450380317034200d0400460080d4102c510030604103043d40d05e05d161908110060080f259401c03070009240c080c07000d00c00740c0302044200541d000e547e114059500c46004100280d000488140d510100e4411201c00241040022242c0c103095410b68040c0040a140e10394200449030320468280015a4603a10005881070090861658242 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 789831951 1250 789830701 789830707
    0x60e1c030216030b0906011208090906120a1109011d0a0504080d05181006060914030f03131e0e010924081e0c01020604080d0b0d06020702090a090b060402 68
    0x1040c124079000d0000480d40e86581014404000e1180e1149502e1081183d002243c403030380d036241e504580e00101c0c2c210180002c075040c09501d00d40d141c450310740b039000075005104000010340b0078445800d140d41054100c7d090301d1212101c04d00c40c141100007500600580d400400c18400ba40d080b54940e4200401200205a5800005040080c5201079030041c4100b0003003042103140c041c00b81c4903c0c503011001301c401d510410a1192034001240600da06407600c0d5603840c901c3c07600d00801d04120310401885164103002d60340340d650070000b0800180c080c10390b41c40c03119802e441c5028510800c00070145c00510404550050a01101c004c045a80d4116280c0c00000905d003424071aa04030444461001180b401903404000954441e0000e0040300680b2030141c101c44808040250a94401c1023050450140c1c100d58001004900d1800c06084041e20780c3d01c021400c0700d560000140c400d440c4c0401120701c981e01040f20380a5041c46242140d00c030200540c10040000191103089e0604030040c9020311850b000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 789833201 1250 789831951 789831953
    0x70f02010f09030c050115080d0c02010210020c0c1002030406090605090d06050a061a0c07050d03021009030206012c190207150b030f190b0714031003060501060e1c 72
    0xd501610212140c01c104001445403841c0003000191051400c1d103081d070030031900201850112210b03034115401e40c0010000441e45841c1074410b401120010390643c001c1e010020104c1c0040d0004000c94480080905692480c000820240e04120382c00b41e011507005000611040d908004041c2c01d031941800d1040c0c0b51035100e0005010780c04809001040c05081c0010b00038800040d4001c1c1c8152840959001101c2503420350005d1035005801108080707600004040080742031170901030300414081d106854451b080300c81e0030b500390b9003440c4c0100c005034401e50040103800d00d4041c0c000f039142c1420000701c0c259130001c1103050740c002c0040c01806690b01c0d1040112040703852603040b248016484804982d001d808407007680001e1003881c3d103550181c050b4540e100b40740e8002048446100d040501c182c1810340254850700c4043c2c10080002042c8645402c039040d491110300082d40c49001340b00140d026490652400805459040e03021f0005c0c41800f6183c0d0403140d0352000c00302d01c07454210300010105605 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 789834451 1250 789833201 789833203
    0x8030c012d05150d030210061a0909060409050d0f1805030604150617071401080105060a080606090402191d01020a02010809070e0103031106100b0d050a11030a0f14040209070f02 78
    0x103c80c2030a921000341080d4104164020440c1c060b00521608100803103503907901462004c000390000e030b1308580400c001e880a2442c1c02d500c200d40102c00035100103518081d6654107441d00c001c0e40340400202d040b500c800b00e01180d21928034200081140c03203105101c0d1503c4042a510500680010f0410080e040a0040c841055010030020041c0109500250791000070054681c0c0980c0100140058503081903541c0b94000c2d581d090407901c1c054041440c02803102001c81e10820080c05c400c0d401601007240403003540e143e00140000031001e9005840f0000e040c1e030701500d10360b0048001700000003400c141780b6040e81c01054059113580c083c03c00c0d410035a901990141003401c0c98200000300c20080300088249036026200150640d00d00d41100c01503150060042d004102920a40444400800200741e500585400c0580c00000c0c5590120341c20341030048080b150f40017111840452070759940ca5074102070650141400034100301c203112405040c0381d00414072305880181003405200d11300d0040414944 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 789835701 1250 789834451 789834481
    0x12180e0a090516060e09160c05070806190e0c03190503041706010e011e090209030c030a0605060a2c07090f062607091401120608030c012d05 62
    0x240c001c0540d50300f44521103400d0401c5a8901541c00003901012040c00305051100049000d04403820803843c1081c50f500084031014580382003160b2030301407100c000a1000c42000080c1c0100411403c000600c6403041029040390900e03240403080354080c5181f07601c1c5450200f543ca010120b002c155404180326806c0c90b928501c600c0d403248581c024808800e00500c01c01085080c1614070250381001145da81c2c02e00b5901c8401d83d100d01c03616480030b1040c02c02526000b83c3c010010b469015082c3c820003400b800c0044c0c00c020281105031195a26041000482c0ca452400f902c05404141c20307203002e0b40c40307e0111100d12080b0341d18690701d00d0f000d04082081a230041000d0310080c145a00c0001e14a07440b170304003c12622241641c8010000e640b51112011540c41c00414805e00c85641c6841e140c5e40380180b9010b4400d80310001c0c50610299089070815030790140106406850300800540d41c80103038108540c21201810368130000c030100c4246010011011080c4100390107011400030500d500c2d41d1240c00e200038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 789836951 1250 789835701 789835703
    0x606090f15030405150103120f0c061a0f030f031c020705030f2701020a150605030304080304031704060c110102190f0b061909110705010e0a12180e0a09 67
    0x1d481c04441100740420401980300380d01c14019100c120b030107010640d540d00340c280401498503114814a4002c1d5204e4240012448003e1600c08070520003501c0e00070485262100d048004400303142c0340d81c40f43c2410609400e564030150002c05124109000003616401119070001e4000b0711666681c404079580d4060741d8400342c0150070740b551108125491102a8080006d00c800d1008200a0800000c2000d485030401c3c0c5040c0c02a10380c0195659812440b04524040e021001c1da683c1d0001c6525201040038201070850b0740c00842e916410350600c02a043c84810400380c07000300c1008140540340d030000ba26181c0d194007140581403040004d005034242085200002d070300d0b101c024508410b210800a030140e00b039000d0940d12040e500c80d01c00b40710100918132181100400d15080030400010343d58030001d12003902403541400c20a0b07039690503095855204024031168441101074091043d03e61a2140201840c18218000c2d851244210020392103842048400c0c1c0325640051036481d03503904400c45003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 789838201 1250 789836951 789836959
    0x206040b24150c011803120506100e030114010b1201170c01200102030a02030609090604080f0d240f0e011805191b111513020109030c090b010f0203120606090f 70
    0x200244081010341721000000550000314a9030300030781c001d18a4031540307004800140811000c0207a0107070179a5405641c10942d0b40541da50b50080400b6202e5034000e038060005006043ea80700002000c50740400c00c10780220b03040200314031803420b02013000515055480002e0034010304a441d04685500c42513040401c0c095554000020000042403650003540309400817560001c403519800c2240b42d807050202c600130107040040042e03881da900118007034503039000070000100f21500d40e240003121b101e900e100710389282c0a10300c0b8180b040e0140701000c040035081d01c500c91441903245c507249520f840c2c0400001e090f9180e8540c0460401d00c000c1c000008014511182031040c42c5540741400010b082c95401c2c40c0018031081c1e1701c1d0140500100303440c020386c3d0100c01440d10701e407541d07101ca155484602034128140f01811030000009203000b1000d40003021003038800601140e046c03001400c2d080d40d000e0014219041080800313000000f146030241c007c041038030b0454031681490040780c20388519448507540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 789839451 1250 789838201 789838211
    0x915050423031612140d0f0302090a0b1801090e041205180d030f02010507050a05090f0109080a030f0206010b070210120b060f0301050f0d0c0b22060206040b24150c01 73
    0x800c200400748004d8084c030442d501c07000e140c0380e41e000c9600e4041d6150a10000342d400c40b81040464402e802070186900d008020b00019595505d21200d02d030f00043e158188200d13104000f1000d5038100b2910001071884210200d03480c9820ba40f10120340c050001d9a000b0b020021940ca0085004c0034441d00c0a00700c058017034400c0450300d08000d006010241d11080c0158285800a101c051290090784c46860042d00c0f00d0f400c00c0d652100b00800c0c8815003800a040007044c4800051103007081219101c014000e40b00c10341d0411074160000e0601405030032007900e0070810054000141c440d9040000b000b0864030b80041c0300c40707546024102601034401480d604c55004600f03e1050f80985c0003c50484390201d400e00c00b5115031310140304c003441e54100040d024180f00c4000704415040c010040c8460500c0317100794850806030400040c030403000e54216100581c0f00308100010000c0301504030780c224035145502070600c007155003d031004c4484802c0450040d100c5041a00b1054100307415200083d820300000c1c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 789840701 1250 789839451 789839459
    0x6071401230612030901020c0d060f050f010f05010f08070f020c031e0c030f0d050c070b030c0306012c0f030f01060b1321020f060d0c09150504230316 66
    0x403001001d58409225407091a810011070f41c2c00000c880703091006801a11008020b01c0c100611003480e600261041034945480300e1501516200f103500c2004c0250003008594103100e5100204400c1341c000905000c56130307084170700c6a5006143caa5120312640381003804100b40020890030f018600b42141d8061144c88071400b1b441003d1f50403009a0498001101c100203a80c004140d40e56070226444152030300b00f0810214034910031002403801510041c01c642c0442e5070b45040f90b00650040741c07032115081000c8284200c56134008007201c240c1019507103000602c5110341e00c000500340c484c0d180c94803c01d0352001440242d1402d11a03d60304201e201d00802515554000e02140c650001031440e481d0303d00c0500200e003481412100b0296019481c4924240341c407146e00b4400b10282041d0800d5000d1024031080c829024203000d4002c5090703569892029a5181c21000c1c40c82e10b0205141d00d0a0110510050195030341c400e000303c540000301140c03540d0080700280802d00f4a00028400010301d441054049 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 789841951 1250 789840701 789840761
    0x603080a2304090c02150106091a03070e091315020a030b1c0303110f0c0c130b1507080714010506090109060608280f0f0e0c06071401 59
    0x480900e05840381c0344040030059201004903140340301001545001d0000b030102ca0b0322644140c414503400d00441700c001444010010500300e09070b1008000134041030060040c2c12501140344034160183c40c00f07600f103052115001c0d100d2a0b640d00a5802a52075100203000c01100c0c000031517603982c0000d028086e1a00800e071358000b943c005c2e06007101081c10305805210a0521070102c008110014841e0240b1000382d5804a0241480010140e400e0320305009450b0318007508001048007070350a2008082c40074002040c01818a81c450119003041c0c0341c00303000c1c0c01035103510740c0c07034071080e1403800025035a030502e40342141c4c0c0e0303001d000d10203800e69642181c10007007160150712690144404072030820b001ea030381b070748500250354141c0105400210108080740d40c500c0c80c03d00e225031400c5900e16183d244d1084091910880d141030349103a8049032a89803021401d5520310440c0080c01045c070250042207800d00106080d031103001d9000780303034880701010f02c40040c500394070920038014401c0142d52140000c041c41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 789843201 1250 789841951 789841957
    0xe060d02120603120301030807080d060f09021321080d09080c0703030305012301031802040515041104030314070c12080a0e0306061011100c0503100801050c0405040e0f01060308 78
    0x14038041e101e11041034107243c1c84c810949040b00e5000101504d08000c565aa108540000400707200b0103031103190208200000707003141800762284950041c0c071000081043d000000e041e600c030307106940d511004041010542180724a450760000d03d281e945904030790002c4000c11446030003406407180400d110003111408070f070354001c40740079590a0080c0e907242c0001d140c401a43d0350190007a64110880740c55030354081c2e000042c10300550705075a079010006801040c01d0f902c1c121440076604807080c0d00844c01c0d00c0c1a12400c07003080e00401e8410f0803d811a07801034007102014a0046220b1400b142d010204a803000c00359025010110401e01100d0300c0e0b10f080d0b4070030f801900124010403240b00b400361180c2400120303030740311740c10080c01405da0030500e10301511181056103010b4242d02031a37940d49071070f494a0042c481e0000c01a0b81c1c0c1e0f583d80c546407000d10056951078001c2550b84c2d0501d005d010070844114182d6059500031100040c685c14151441c920b414010140c040b029428007000200380328de06405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 789844451 1250 789843201 789843211
    0x8040510090b0726010b040825181803030209010216050d0b19111e03060f090c070602120403170108061501110f0106180902031b030a02151c0501060f0e060d0212 71
    0x1220300070b01c1e20300310241080040660b00305c160609e2040c10080542451004e901c440140640055400c400041d14840e20301c040000380c020a800040030f0709256410404688405110984c05400905042c0041e503a8590100041e001044060100701c0501130102103c130711080c843c008001c1010000300f0725030300d908070724140d40c8074406030b55400d0607000034401120300c994001840c0d804611881c00800c41c801d9409030a2505c400c6051120000040c440c1c401810040006a00c88070383e440d00c0c1c54010041e480c0c02c1e0320090105003440042080c00340c0010701e02d40017451104107460b2a40d118004a0f140444c000100f2418440c95248100041d419805501030702c0b0408030000c2500a025201000d44a00c240001d405603c18036804003070095000c0c1510380d495000382660013080050300014690702c1d906128035148100000c440d024a14800c403146030040d0020000e2106c1e42c5041409441e5004c0e85a0502c02e02c400021140c5c3e2690301c0004982c1140c00c07050085469180120f0b140d1441c1c501165 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 789845701 1250 789844451 789844453
    0x2041a0306070206071706010c0308040c05062b090807060b180c0a080601110d03091e1a0916050f0406030803012c060a0b0d02040e0708040510090b0726010b0408 71
    0x40310310416546d60780c140c0c803c0318182c582c61400b600c1030741c0841e410000104203031803240d00301c0800f103290341c1c13003e00914240541900503a034106501118101c15a0340d0307210020620b2801c003a20000070001c0c4d00f5218007a41006001a81601c01070201d031144d038036140700003060b140300000c001c0101040406085000442ea480c40c02c0c07940c0c0d41c0019a22042c103024096942d50200c8000c0c00784c144241c00410074140302c0c0402100001c0c1c0b007428649071140760f01d82215030083c46445960815402080345500c4900e0b040188024121245180c11019040c06030350700030800000e10030307110b8a541c1c229900a5511405880d030300d60b0345250389104082c0700800c0c0b9401d0382c1140d80c080742c160240c4644e40c0c0200d03002021381c41d04526000200c5070640c824101902640d409020010340b000640c4407213032090340141c443d1040b1385040e10703103241448440350b00d4402c61484c1c41d1515000c2400c01551035801110703030610000340d0800c2c0d080c0305140701110041d0f0803c85425000490f1480c032041c0079100301c0389004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 789846951 1250 789845701 789845717
    0x80c0711033310180b060705060105010210090209010311030c0d0c0510180902070f0b190b1e04021b011803020d0504062f0610032102060402041a030607020607 70
    0x1c0c038600c0044007a07542d4600c02481c0302c02404101c004c8403400003400441d9000044202c001804211035800c025026207468020074010811542c0601c01c0048404084004224184a603400200703552410f0102034070310701c19880c0c00005a1010032200d16000340c0100306694080d000e107444aa2142c1c18000c29008084078500b24103914060081200b00c4038481e00c0341e010700707418090010029080600c094036001643d00078100842c13201d100306400340302d41e0540d050b00c1c03040000d0070405480c07204400c180224040c01c9280c2d92075860031000d04146100729400359841d00340d0000c200c0e281007a0650220154a000038441e400c6440c0a160000b043c429000d0702c81d18070340c000c001e4900b80147d1003184046100c420141d080d001d42d81e6086180c4d10100d00a08408000811716a840d010040722066211000700c01e007031040c800103404004c1280126441c3c5c0b1820403107200c1c02900c42d500500b0007400b0704d8803807410200191812900e205010750283c02c8030350300d1070203403002951408241c80a01c0811303010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 789848201 1250 789846951 789847033
    0x42a0c05060423160e062d0a0b0c060109150308030408030a060b0a020c0904020a0b040617060d17090607121d090118022116090e041a090c04020409020913090201080c071103 76
    0x27072007640c1c0d42889880280101c0d80ca0906010003801c099540c8003102b009120000c1f00103540c034009540178078010451750b40c0300e02d010001d01086525076048060351041c2070099181d56a4001210b41c1c001e241030700e03188010784071803000c030b090320300290000160020003080c04610103071300880001003200c1c080085c2000c2d480b80ca007880011142d000d805408403211413404141e07800c00303e008200031507014141600c1c1444540702e101032501840d6000700012401d1004800d034041c40d424a60b03010303008441c40480303549000303c41c2c001e8903140352000c1e060a070042042d41400c4400c11070031344840138100c0c10490702d2400301110742c2c0081540300c0d00c5000c1030384040080f07000000060914402c60340705000103190600700c07010150441000341101c000340f03d11b03450101c46407142d0002e44001c044403032015840700010400c000800d80c00621510005180401c4080543e82c0803548581000d0b0400416941d140340d130505800005210341056014441d100b074800402d416001d98190305000701d45040007e07400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 789849451 1250 789848201 789848219
    0xd0c020c13091e020a12030e060a030c2c010e0301090c03051510030f0b0408070f0510110c0705060c160e0a0b042a0c05060423160e062d0a 61
    0x40c0c1d0304043d4001d00c185a046c4214a005020301e00198040d0810302200d6581800090040c0c0c042202c0000180d22080540001e0f0f8206481c04072080181218070954503120100724040303015441c1460401204000300c4000b91004c0d40701d6041030780c00c1400c100c5000d40ba421301c0c96a401c1e4100e590350f01c1084000004400000c0c0e4032402c1c040e00e41c02621842d40c0d507126190300540d001c0142050b110b041c010454000014004102200700e02d03ca140940144451844000c1c1150042d4051018106d000c128100d0184e501281c294203607801201d4098651022482c0d05251101080451103400a6400c020414030910b4060500c520b178954414006003420406110036540c403400780303050310400001d032042c06010b08480f0700310080d002c0c030b0242910b12594a40c585070090554090718044080e2460003a00080020480040c024103c02080ca6a11415024003081218400c4080d00385824001c04c80300d5540c50310a119000c1c9045160351000000c078500d021507002c20380ca403445410154000190804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 789850701 1250 789849451 789849503
    0x3040515090d0f0f12020d0c020d0e0a050909030c191506030b150609030a030c02090106020115060c2102010b030c03010b011704080c0607120b0102060c0d0c020c1309 73
    0xc0e902c3c4012050203000980f1100342501c03020080c00942886090b0461581c400b502400c00c070b03000d020030351503241c0310040d060100c0c0a080e0410081006403500f10381d11075900722b03011900181e80e642c54950340c2c4c3c3c0d501410f40c003410a42c00c016026026000b8003200c9003110610201d40601c2c514001200c840703c001c000c031041c0d80700c01000524403a00140c09807a155001c6c805a0750080c0505250110000c0043e0034125407200890100d050084ca800035410305082a0340901240d00081103002034280200394101464410074003000003c013040c1080010014511400200b00502c001644550110280c06400051041ea00a10442241c0c480920b0b05005070800384006855022040910503200b00c4450070080081e101c0a40400404002800420030a4410900c550310b009106001c28034440076500180845411940b0400c28400070390f0555044038040e16000700c0004078003c0c1d60006074103084000700c0700384c2c0c000124201d420300010160050842544034003611600e1101441084518076 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 789851951 1250 789850701 789850723
    0x405060a050106171f08070e011a16050709060e0610081513110a0e0a080601030b0a092603101a0901030903090b0403050309010e0d030c020f0112020304051509 70
    0x101c0c10865401d0a2803010001504580301c0458040c003050100e04000302c045c800d511000c0140c0c081c0004012101c5070f02c0300e090142c403003c46100410b0310203507001c0510780164440e02c9485401d400c00c9008110040124100400c2503e109021341a5540085903031090100d62250051400c1000241d11070321070210b1074444c0b45400310480d00000814140003c182404000196840e5600b14003903c0c0110300010307209101460380d0b4240305100070018019813a40583c800c003070590003000180001645d84454941c050072101000030600001c2c101400401000620301600500100c0c0d144c503883c10b154000d5110301c0d0001c215842c00e0381d0701d850b80b040060314640807104a13401803110b00d140d0743c40390b000b444901740a441c108003c04c0d212000206180c0c0309900c02ca07441d5000140d00030782560007806032080319400702c3d84c080059039203032000703054a44100c80003446455070485003221071380901145280d1030341d50081191a481d003460700981e141c0c10002074525100c0ca0a00280d003000c4002200d40e811 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 789853201 1250 789851951 789851957
    0x21050d120e0d140a050d060905070e010f020c130906050403031a0d030e040c0e030f0c0301050a05040b040210051909031103070b04090f060510050d0b0f210a0f0b0405060a050106 78
    0x3920f0700409165003101c6410001c00004000300310695040340201170203024500300001d0356050508000c1c0c68110000000c905021068401621440c8c011641e42c441e01d90070380741d4041c06540708900400400000300024082843d0800340700525505a00c06482d0440e0940c400c0c18216511041001114112800800250000355042c245013059001700a00382c880341041403264000303200086c20486280150345042e4041000a0503078a404d0180d65004003019500304401c1c106501d42d074590707030002071019024001090105112500c100f0448035509104072011003400d039400d2009100440b1440309654607200400d9040141c50007069140c1100c2d10184001d00c0c040c030f44a0794801070305002ca504006680d80b240b0029050f1140fa00c20070392051143e07600c603a0703200700200c5a02104c80d840c0c00c0c0c1d4002e256140307c41c4c0c01500c40c8001039001c503086502840380003000f2500d00d80b5003580d422000b00f000c15001e03084802c100c4000340b0719000714031030001d445665403404540c204a4000b44110000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 789854451 1250 789853201 789853217
    0x319020c0c01081803250b010b0a030c050406090b0705100f14090102040e06011b050d03020c01051f0504090510090f2009071d1009050a080309030721050d120e0d 71
    0x2030b841c030000c07540c1407140100046d0381d8803000075154000d2260090380329038003003900000e40a142c81c2c0d00d4426207121a005086c814103060a0681c000c0c4800c0c0c95000702c1416620020b880301c14840c0070480c0c0361240c4d11082040c40002c10320382c41e020141000306810456002c0c1d00340410024881802505d050303445050300b00b212a035070320340111894800031120002688189074041d0100b4414814820110403685000d80d070b9280300344408d802c4941c0100254082260400325003030208072000e900382100c000300c0d00412040036509010f8104041441c100d040c0f50b1034100c8481c20840d5001403c2d148a002d50140d00e540f690005030740511180b8140825840105180006c244500413aa0003a0415450f030301d041c0e02c80750701c10116481f108114100c001264050304100824500301d690000640118005103061401081c080b03a46ca9205001c2c20810480f036070841011100480c03400902a5008070807600000003100d00034212040100c840c840d102e0400c42d0400b0b0381540083c4503044400f07543d4565032 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 789855701 1250 789854451 789854467
    0xc130f030f020f15190f030903020c060a021005181212010e0c090603040b1b0705060c220311010206060d110d02060c0d0206061002070803040b0319020c0c01081803 72
    0x22078068883c041ca54800300c81c04009003548031041c00740c0492990000741c0814100e4042000d400a0b40d10b91810b030801d428480c00b0b50009501058140c5000400d462054441181007001d0782045e40704001003021038941010800c120070642d05c000c08040d03030700701610060003180301680d0052150803007500d1103601881c01000241030100302140d02041015905045c802c84a0006007940d00540303046c0c49200c2e0220034060f061079411141095204220303001441c00035a03540d0540c1b503600041525503020000b04080d000c080c61041260040c10041207100582505e07840d0519040102490aa006206500000d500c50404e644000328142d0060420301c40015041c0070032a074004010350890304090244616071381c20004000c8170840c810f480d0041e000030f1901380d061050400b10200b808086600c00d4204014400010003224142c80f01d070a0855505e0751052507040002c456a0808880d561002802c450081808911010307141e500344e0703800001d515500507a40950326a5a05070741981c000300010a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 789856951 1250 789855701 789855709
    0x1908070305040905011e0503030a020d05090a0e0f04060c020c0f09040f140a0614060603070c0c1d01090b10050901051308120406080f0103030206010b0c150c130f030f02 74
    0x919244245080391a007920342801000b07440f002c3c1d00140c2590480700803403409150304410707040a031800341e0041d41000101c03000290b80c2c400040d04030046c001c0014004880343c171100c403d440548031040225945c1e04140600e13003645c007411601503030901d00e0301e4030790385c2c14038800305551500c0c6400400c00782e64031589204000c1d01c00710280c8100c0708410a1240070000403035145035219400702045c090400040319050040944103051544a0910300300030030040c160307072a03505a07500650b2a01d09030704228000d10307262044c1881c03030b0031600e00100600f2401075440c05801406040c0d904840051003084801418030408145114460780411030621810b0420352040000c0c05007800c0c10040540e09560707072103409040040c00b181c0c0e43c082d0100081e09000c0c072500525843d405c442419482c032036640c03440d00d009450318018001c000303a044000a8007185242c0c01c101d02a04034001d940001240e050009907820030781d2180020620440b201c81c80021001c9048580c1c070200c941089451000d41100e030300308 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 789858201 1250 789856951 789856957
    0xe010f03020d0e060702030a1b02240f0c010912051204110d06180b0c03041a1b0d06030203070602010618020904020f0a0f1d010f1128060e1908 63
    0xe00ca5951003ca071419000700000c0d0b01a0003e40c02030741d5201d98042c0020815408000b02900103040340c2c1c24100180c8a2501070021031841d0f10b42c42111914404004d89644682d45803071007181c0c004180d90801c414190b02403900c4502c50790345040800e00a0509880ca030183d00340525048400400042c082002000c0c840c001220007414146624441da6512007201c001d040d104040310410400709040041100c1c0380d5420000d80b690352411468a83d8400000840181e56401003080039408100200c0195000e07a2080c0b107808000b075211099181240c00810607448281d200303110700000003d01900610941013030300c01c1c554440540c242c008009002a600240215070413035402c0241c070040c07003403520142a4a020307aa0b217129180441c0003004054079540054100c01c19038090390620b0b240c0c1c004d007000c0302000540c185554104802d020481c01d140141541d1b8031051003150000c0642810400d41ca200f55126090400031100850f502c00d6850240640307040707480c20720301c000101040e020405 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 789859451 1250 789858201 789858217
    0xf0605041b0608010e0a020415050f07060203090a03020601170706031a03030a050d0605100e040f0f11040501170106020a08071b0e04060f0e0601140a030611070507060e010f0302 78
    0x141c00c84018000786010411806900c803900141150005002e18000705034074542150400c3c000b5401c050508a16820f1a58250a21818040b0002c0d000105a1340c80c01940c1d0042d0700108115100d00d040d45403941c5854504030110018040d0100214149041404007804010340500519017213040540540003064120b651070271009001c4a040401d550400040c019007645a03546905c03000303040d40400503200c9070b40000e0701c00d1aa0004d6a81201d50000320001c00c1e102c2250046401024440b1202c0140144080342002030304101da1500c1c039040e800010001c0b50801e0f0317645044951f0800340301c1c80e04440cc2c0506801a000107021001054020000c0c00c4514050040084001e070700303242090605001c1c1c2c0c403103581c8002003400c1000740050f910851002140c00c4406200c00c0555408480d00d50105002c0c0402c20041c09501e581c4d05e840c1c404056002d160f2000b02084030303407a46911068641c0001204445501c148000802e0a40c0700d0282950203d0b0181c43d8882e00c001844d2051b8069009124 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 789860701 1250 789859451 789859463
    0x141903020403081b060708040209150f041104210c05040e280201090b1c05090c09040507052805090402040e01090b0f092b0507020d200901030f060504 66
    0x30010036400d800400004c03140040025400804003620b5042040041c4200f003407020380d000300400340e05d800704540e07030141420010f07941e80144540050040d9012010349a023291410716400c1c01d06a42e14020402c2e070740ca584c10081c801e0318070498007174a8030342500e00602c01c01c0d82100400060910b5000303030000885003000e46444186003608110f00080c02c03060080d403602c440d00c010081d03582040307100300604044040c451520040d0703c03502c3c2c00c000e101510350009540c3c45000811603803003801030080618000704512614203090074030f980d589032180100c6100b83d24681c158810103044003d0080c0740f0340149070308a2600d00c4c00041000d4050000e100340d03045a03e540101940407802c0c807036a04841c3c450007545480e41080c00e40c034001410018038183c40d6510500740c01300c01781038086161a41080981142800e6041e5150454490003003400082d0080c1c05100c15030100100000322003d036021501c04c00d61680300c00001c000c905072007840082c00d006840324003000400c1d01c54000c03c0d030182c0140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 789861951 1250 789860701 789860707
    0xd3b191b05060c03090103061a03161214011a0421030302300c0301230d17070302010b0102060f06040f060312030c02010b04150b130504020f0c0c0114190302 69
    0x11000c50020752001203c84416000020350390020b42e01485148054005901c0002c01d80900c2038451003c0d00c8042d00050310515070f035262004551203020751616204c809001400f10302c03540728803106d0b501800e000b20704014100000c8100030400e40c0098804032008913441494209501c000c4140384005505c0039410140c003000006a0f401990303100c01a251540005030b01d00e184134a80340d0090003006001c941e5003544c108010001c034200ca04554000450300305581142c40b0800700021444a80c00c82c1c000c0042c0000413000c0800800b0001130001030b80246c00034001c01c8a000c004a0302c40030103c48003a00701c440d4002054444c2030035403082c034071103440c03501c0007505640300e46803803100c001c01c90140d030002a1140341c441411582801019034214041d5030501003820200502c00d680021030182e900b40d40310100307603001001e029554901c024800078004541e070300322203884070003254041d024070080b40c4149181154a94461940f5141070002882d00074146000c01d0750001c80d555021103a1403c0580034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 789863201 1250 789861951 789861959
    0x903080c0705030d0f031a21190303140a0207080d0b040906050c0a1805090105040e0316080403020907181a04080601090b040606090e0402060d3b191b 66
    0x812240d881c0060946170f0100c0740280880c02407d443d01803c100300110500300480c03007140c880c00d480c00c40c1c203090740031869070903468504001c1c40e00c00f03c2c07240000d091203044c050703d00307041c0c250b408003092010009400c5466620001c000d0103078071400c03d0080c060041003105412007030352540103c4803544010400720741e1484c1e035100d18050364426104a400c1c52000141d0510b51908a010403045d044902d5008103403501c1c0200240603807405110302402541c0f07c1c10700d003280d500c00b07108644c0f010391010740140c0240384c0c2d0300b0801415000382c00120f005803c0040461900f03400b403000001d1650550140402a070304007402e481c101c9038460840f201c244000d000114224809020b03031406880c404d140001c41c9001c08007000142c030359a0b445201445034028040c403082d20710b1604503500c1a0140c4600399501c5541490340b00400e280c2c12203181c48a51f00a02c90802d045403060642529000e00c3c8101a03d00b4288445444500e5408024114a008a01c04000481b0900c1c50102c2c2d0030341c0c0903140c0c1290b6407 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 789864451 1250 789863201 789863203
    0x307030806010504032a0f050303160309150c0501110c06060d0201020708120c0d1e03091505010e0402010324170c1216080303040b010506030612010c0903020103110a0903080c070503 80
    0x49088581e04103100640c01040320446c040c64030011300101c1400c440851514011a46070b1007065903a2041c01c4e440b801807001d05015860210007404003a40b41031041d80f480c08020000010184111007550030030203640c0c00d41b0000e40584403044140409880d80741c582c1310402500e0400104100e065003d00741002408400502c00382c08881700f1031810b25030f14152041064184941003c0c0401400007010341c015046807500039250601d07045050004c1c01442c01e05044020580c820030a1709820305201c00400c0c01e01041300000d015501c00c2e00c2c14400c50302030004c0e100030f034002d90595101080449404200c10748040e0504103418030a10284c400103554000271960068071062980c00b141d005007010000d0394142c50f810002001210701850540c00c0a80c2c41c40d0840d0018410780b07100790b40c080040346141e40c50b40407100044020900800049004040242c142c00c1d1911059005c2403401d808050310100301c0080303807030f00c0d9140d80c1d6813812541560390b40c51540c0c200b100c1c04a9544240c03440403405440c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 789865701 1250 789864451 789864473
    0x4150c050613020906190b0706020c0a060617011e1a031603030207140904030c02060d090b150904050d0c051c0903060506060a0f030b06220602010b12030703080601050403 75
    0x80e010b00007851414040c010300c0780d4084041d101e2402083c98010200322002030749185015109120125a9680c21a003845400b81c0502202200c840c0680081c1c0d504100c400e40c400c00c00c4842c1b0020a4483d82300740c0c11410700720f940035019020202c1194840101c1c500c050352103100c3c19010300f5040d14000d000700703010030314004c0314400e600c003031518604061060540400028008000d00a5180d502000f00f00c0844c0c100300d0301800003024009944415000c6561303580c15548033b400080c0b0704004a03845400c1070661a0030a80322002c11008600e500241820507044151049401c50001c0418090218048680d050000c2043d965801640b090880c0c2da14103206c81e030300000c0d9030764070100c050b802d506200c000c40d50043d2006224a00c00c10004c4460794000351045040c802d1400d0008400ad0090f0108810f449011a001608082500c9540304900090005000d60b0090780c001c1203c1c034000d0080c0308100c0b9013401e60242a52050040c20000792090103451390009d4107140880c10316649036070b18a5000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 789866951 1250 789865701 789865711
    0x32001110315031605060702130e0c040c0e010c0b0408070f061505010906080f090102160305070b0f0705030f0604090b0406051e0601050414030c2e1404150c0506 71
    0x1100c00414031000003901e00008004102c00c602030014505060704003a40790140f03100d0940142c6000c43c52600f9580d803107418031100300550724140701c080780034655a40c031442c0c42008036116524002c54045d0f802c0c40b035175510301c0080d8180c69030312654001d91160b445400c0024070841d103d060400101002070924401088603074131841000c2132032100062608110106900b1a40c1080b03005041080a154040803080e0401925100040d4903250300d03c005000e48542c010048041d40c5810b0300a08244c0e20a00510b80340303000d481340328890740b44c01140000301e517801c0c2d5450300040e205101061404442140e0f1070b40003a4024000140034503141e441917024a41190282ea035550b40d1410080f040c07411036907110321145010368031065481c00c600068064007039070281203000c8682c120001c0e0161030800c0140400c1384020500350010f160b202c4c558401c01e5a091303075100c03030701494001e54519074062098100c1c81225030400d01c0c1440c2c1820302000044883c03074050010030881202c3e001c041002072020074060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 789868201 1250 789866951 789866981
    0x5a010c05030a1a06030703050604060521060c030105031c091203120e0606091504110d0c120b030c0d0615090e0c030f07032406081e030a0903032001 65
    0x24541600c032042120003051840304211641450b040f00740e90740d03c0c1281d911080d942000641525200042802029140c0180d900312a1021034000c041c0348200d540c064001248003100c01c59620419021001d01081c4900c90701a40503a00c9805048003030b80e102e40003c801d1741342c4040d00b907540340458290020614001d4001c2114040680300c42d2280d4065414000c88480080129041070b030041503001c60000c0420005035120318600000e607842d50805052903244054507520f520720b05125000901491500c0400310b030aa00002107140c0140c0a9004510f00040203007491030010710074030090340d9100c00700b159003d1703440088104c00040c01401c10043e00740c54800140040e040d0385aa440c0c0040c2d00c01c1a4800da200107440c81c80880005040d00903a43d0111181b00c3c3e0751010718141000c0d500c198090383c80c0d241407030030100340c0840c00a80c41c1200600e030b181c40b0800104105125480b841101c0c07200000071064402440400e010f13441c0c80340e6100d441154941c2c080402c0d000b460031101ca000d010f40907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 789869451 1250 789868201 789868207
    0x8040b21090601050906040608120c070e01060804080a09050d0c03050d03022503030e030f030a0605091312020c030a05010f0b0f060418021b5a010c05 66
    0x1082661010403450300311800180e00080c140004800e03500c1105214803072061070450002000c3d0f4035107401c403400804039101200c81074601440c5003040754124002780c4045105625001402461542d1450304071034040d190f9004079200d03600c2d242c1c89a03000061038000e000700081e0000305500d840c42103e09240c003d42c203a40499056103405030030a011600c0130307030416006000000054640d20000040c410305036552492807440e80c5002d40c060b164116940020740804210034059004034030055204181252003000b1550300e41003003001c2000241e03400e102055000c008100010201240d0000200d00c80c012030b2001c0b10010300191034010348a1041b112039442d0713520405002458041e00d600a0001c17a141001c2d4150302c0301048513401284078440580c3c2e03283d000c91045e4640c90341102c42011203480380300440d2081110440c1d4418011001036000858041400011200710fa0302d405002042060188100c84c01101c001e82d401170199407004440c013500b2140c40d8034600340702d070807000e114503161151 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 789870701 1250 789869451 789869467
    0xc0c0303020f060a050c04051c05010204030c03050106081209210f0d030f061422060e01081b01050405120f1b010f0201060609030204050c09180a0b04021201060c0f08040b 75
    0xf05011015251003002d13400c110901000031006d0040c1c40545030300b5101c1d203080030304a00c901c411210b901000501103500c00680402880107520160050b80e001c1c074000e2284607500c43da00d9a803044c1014a0711645c0c0d20610aa450038600f151a080c4030304130007100314005500110f549400c00c40c4800030134010798085000c0200080d01070042c01c54402d130f10a000c001640c038101040740415442e10529108240151b085c46d1600c400c2004888800c0f01d40c6020845261581c01c14480080d0038040c9100d6481a0358040c0d8510a1003c1c1d4480040f006a5a4074203081ca04400e0003484050098814030500541d4040381c1004420820740c81156690440282c0001c0c4000002d0a0f0a0342d0460f06011a4181030703080c0300e1650040454811170398141d40008a90351a009810803130700031311510030b0744286900e20000490421101d85400303043e550004014000403201007108921030a51000001001c000040003181c1c00b405aaaa6242c025500c1c00d08090103603030362400e1640076401c00007002c1c1e80070881d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 789871951 1250 789870701 789870703
    0x10e100219030e07030f0819090914060d0206030603070810020405040e06090d050a0e0d120212070b15030a050a03110c040507200102040b0a020a110f130b010c0c0303020f 75
    0x2071410407403800c04120715480b10364015126407041c003018002a00700c901000420548404444100c03640d60008511448100707401448442c1c0f610071000224100280c50503a0101e180c0c44138001c0c82c0c001c005042e4403010780c1c280b00c882c0c0c000400300da5150040200029403850b05010000c1610049480103035100d040904005c12200c2c000c441c0c5481ea40f0100400c83d00c0d07200051000c41e00c07510b50520719107421070300314101c41e14096103010a0f0000d1052465408202c0c005100034030300701150302621041c00c6000080400740c000d0301000340590000502154414000e1159500300c110050181d400718881910380d035181c07803403c0c6411400500601d15140c10000244990030041000720360612950400c403100a000792030a003042088982c502e51010720102003541114010401925065111109520069114080144141d0310628403103182c128900c3c00080c002007200009116400109003904040700400d45104460b040c08550a480c8c0c007c0340e120700320540214841d034014503000c81544921 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 789873201 1250 789871951 789871987
    0x20904060b07051b030d0509031f0c020721030509030c180f010b0307090311010c06051810090209010b0a0c0615080c10020606010c0c030b1314030405060d0e010e1002 73
    0x14161035140f0402a42a540824506c405d10b04910301141c0350b440c1a800a41880741000d0300343c161310040b0706816800c080c1030300540f18110283d000d403622140c1c0c45405603891213103188405580a0140c101030300007030241002d4003a0482c00340490f2122102c1e0800318610400011102d41c2a45c4502c0c1006541c0309072103085d40c058a000d440d800c0c11410204009028041c26010083c008014800c3c0764400da481100306421198011400f4032450400c1043c00011455038442c0f41c034280610001203581e10784601440300c050781c0c043c0c06c41000368681107041081c3d42104400400b0400c0c4014044007190b445d000704001c060302c030700740b070900c01c2d140c110002d03c2c10f5002c0503214020440c8440365075141e50003044427a4005020b090150b00c02d0a01e141502000d0507640006207220540700c11f00c50f07100052081c00758414401c07140115581079141e03884e03940340a41c2c0700311390740004200f00008070703030120343c0014160a807214000f14080480d10a002e00700841172000f6400543e0204015036035040e45051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 789874451 1250 789873201 789873223
    0x6090212031206040b30010e190b0705070602040303020105101e03061a1c1101090f061d040203070810090216020909031603080609100e04030f0201020904060b0705 72
    0xd51402c2e01d0b002e80070400e500d0062400380304a40d50300d0001da20f40c44d008a0084404016103440d24020284030081d000d10034450400d00803503290008101c0281000641e11121a0704518030302c0492413507588040d000710f0000d1501c41048010b2108000148250002e0030165210f600003007118034100200c4103840616912112185556940a4840c08590300000c02660b400a6021a010080c0403c1042500f40f4183c0307143c000c510416400c0680d4110600702e0003051049000001124210004480303003801340c060724410b00e007030000030481715000e8210503800c060b8128030a03a403604041c00107412a0800c69046001c41c01d07040802158041c80001c1101034a80343c00214185407048155400303c2840440c000c0c040d0000202142d0140f40c100207484542c0d0401c0000003104015150040401d00d0a88030540900c0d42003010442d01c1488075544130580c6c290454000c807030f90b500e460440758241d01c0020642555401c2000c903000d619180a00b8020b480e15240103581c40e40c16141c40ba02d04096100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 789875701 1250 789874451 789874453
    0x14010903030e1306051816020d0801140a1802030709080f07060810030209180f0316290720060c0f0d1104091b020604020a0504020c0c04050406090212 66
    0x8024000a074002c1ea681d150b50606841d200240d09200d0845001030220342c015541c050404c0390390342083d10700c03044054400da02c0c1a90002c1614025003081e40c1c0d807800d4449140c04244c040006111003800308002d000f03001b20003840c0c2c07820550399640c16644000c203040c502031041e80000030090a282c0080d0104001c000242c001c20030030503202509a1241900e0251204000c08800854008000c00032050f0145070010403041c464180009404040c0080c590411380303a028046103140c5008012042d42c1c0c00c0b1003880c441203c0d00026030350740000018000c4020512989591764404030742c0840101e0b9100b100992a6031aa0744905020000e07054400d8401c24881c0d030140041100c2c102051040c2c0d2289903010301d416071100d9002c9641005400c10b903124607a0210041030025071801c041d080600300f02441c032200c007001c541c070074402c0362610001c840194010039494010807840c142540200244600201610221451903001030142d0307400303540507142e00c0d455001250551401c0d40d082d0720001c00c008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 789876951 1250 789875701 789875717
    0x9090308070e010c0309170f0d0c050601170c010e0102010e0105040c081005041709030703060f02030a061203092102090f060307061d01030f09021809010c0c080f0309160b03011401 79
    0x2540041c10002c03d402100b188000701c03002e044060b1020031094031480603413026600c0e080b40002c0010522b8a11980c180c4151107940c00000c0e41400c40076400c00c400000030007510300614101c0064039196280c5175441d04643d42e50400c2e80d01c0c14000e20415016030310510910340007502e0507541c1c0d80b402c0504640f000d400d40c5403a007403000098003a030480070590980b4030020f8030b075a10303040080e0810345117a102030000c0f403c0c8611240751035050342c000c500c50000d01804004031a25404800d1036520000001004640e50300720a02001401c403640380081c500c030301a01300c3c035180350340c1c0420032180c01170755500c040a00060910080340740c280180300c064800c911703080c1034608103180380100441200101d02d040c15038418544d8030010664000c0d900711a000362411100011014194048010440300800607501c0c10382e0982c41c9500c01c7c5140b821094010b01900c1c1011000224681d03294009403400100307129804401c0c01e440290b80c0600014110008040d44940c03401c01035045821078101c109041025507 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 789878201 1250 789876951 789876953
    0x3080c0a05090f0a0b03070503102103140910090e0a0b09040f06090c0e070e10020c120319021b15030a021809091e012c030409090308070e010c 63
    0x848156250701c10103c2d00c03808450312410101d50410120341003209031080001c2000030540d000802580220300914018040e641d40f403189004181c41203800d40281164042c00034042442500e40813a50700c0d000d00c460f40f40406407000102d080a0131001c51003c1800c0780740c20003100301640da58a901030000071052000c520b50000082c20400002c00083c00081c60714804d00501180b64091004540d01c00321604840703481d42e25100103070300115025400a0a84480c43c21035050071910800800155002841d6004072803041008409014031012094030007404444074013484506e80c2d8403800e201760080c000c444e003030766030042c402d9a40c0109540941c82200804081c02d00701000ca0740e00085c104d40058a40904c4200b50f02e200d00300d8605030b0790090b100d005004080b400410b80d000a420031010021043c401071001e1803c0c0c0741100d8107045000700703e0034443c80380c80c0540e520646e80c0001c0416a40761a88071440c00040f10075040041e070008035103204004906401c04200c4964007405d0074410008041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 789879451 1250 789878201 789878207
    0x6361814060d030f0507050106030c14120709021c0f051f080a020d050f2b030b030606060f0f0703090509010b0903121308030309012c190c0e0a050403080c0a 69
    0x441c10020104200302056000d55403045c41901d0241d030f44a0000e010803940c0381008a22540c650280c68400c1c41141100d800d40e1410203000540d40f901200540999844e0440401c02500301e00241f031419500b0740c1081c0380c02c4c400b07441000d104048020000070725040100c608034032101c3c40360101442c50740882040c00148000149502d586604541e8403008a0b400e15107182080401858032056109a6010014201100741c88a02030100820780c11110080c40c10224281e40b0038428060b0990800c1c400300d141801c14900800d040c40d040ca0500d85054070203071001d880c1d41e106420030b600080e03070b44805110ba40b408001c0d20f0b0040442001e240d00302100c4074002500c400900c01c8031045c8601c001034494444240352030720380081c94180140c03a00d80c9090200103010740040c1030b0015090803450b0340d546014048e510884221503482c0d004181500c000c040c3e95242541e03025055502c0c2480d4030700055600048a046c0340b00341c110300d0011401c1e0409103405490303010040c1c011440503c040c040f12038000c1d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 789880701 1250 789879451 789879469
    0x20304031703060406181a040902090402090c0f0c0708071502061819111207060504151b05030702041a01050702040906140f0405160636181406 63
    0x8401460b94a403100e0001a0003800c072903204e04881c002191031071001c400e055000350000c05440d224105c04100a40411045070000301000f0b500411900108025040c80012144c0c0015040711041c076280c00f048030000e083c0c001406410a5a03c442014001c0300e5040c480340c070081c8220003003405141c0c809030010b5204c0c20300501c0c0e0256807465028042d4948420844083d1310342c0100324030040f00d0304e0742c104a807144050202460040b811580a0b043d00c2c04000382140c110b5040d65691821301d82401900d01d642c00c10141e43c4800c00401c0c070022407030b0301c411700c070005400b6110340011a40c4112a1052005031160b00da114000600301212008181c0d030450101d600007036040318002003103200c500d07209000f0865407044030030340d000007001c01c8400c9099907000b50083d406142251142d102c22800d041c85040729004250001d140003507900010f038400480c610040840c003151100303521041b5900c44002c4007079403081081294022000101c5580d0380b2500c2c44991541c48003041c22320b48800400c071500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 789881951 1250 789880701 789880733
    0xf0b012d09150e0109061a0304020d03080403110714310e01110a0504030b2a03040201020a0210180905160f0210050a0504110d030c020906031f020d0c02030403 70
    0xd5190700b101100a00740840d9040a49402c0036002120350311065190010041406040310482182900f0320020005400b43c9100c0c41d030007070640c18400d03150f54040302c514038040c000310300307020000340880d4507500c080c800003010b0400403030103d0352240d0510400c1015440303d5440c4101041701012507050700b00d07000c1f210308101000400410740f1903c0804050041c03000d1651480c0d080c40102e694960a40d1100040007103a00900031a400c9856088922501800941c0045440e58404556214242d09240615031007030050043d144400c0345600410203c0805140d0030b40000c05403100801c62604013401c080140c4226003041000f4070b0480d00d41d10101c041d1107500424410a00c0059814920030404119a1b1900b03a1040c4610300385a4030b504040c20080d907040702c00003911005812241012547c558000307030103544d044445c3c1001d400b84031305507401400183d094000c080c0341486810229a640e92070241c1c50f031006076285d0540e0799220466000301002421034004200400110390008440307103001d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 789883201 1250 789881951 789881969
    0x90507060809030424140f0711060c01021224060429040609060f210504020402041a03180307020a06080a0b040603060b150f070b0903070f0b012d 64
    0x1d034a800038590b145005517072028005c2075032840b80b0610746020f03d01c0c01920440c0b6407101e008401030a61454070701e001d4900b001d0703c400001d2001001141c294404011390560103000c551030079030740000c0582680d2000054152005003441400104a40f00350144044407001c1c410074003410301d2000140e000d110740d00c00c140040440c03441d01c50307480c00d00301840740c1020a8000c8a95549035241d002030480c7c0ca146c0301d03680109a9414482003800c1c00b80502c400c0c4040c01010700c12424103c0650840203050241040c1d0b04649c4c284000b0030301400d034118a4204500340f0346030302c1e124903003030700081a041c2504955042c1c40d0424800400140c40f116400c10544146d401c000201e0341e901c4003018020000982d04c1613101d4200348000007402103550000110030350680f8248540c1800b0001d001d218415240a694180300c10007a0740701041c00900c00325040264031081da0300e0980251280b40c031040f5401c500b035540a10074001000203d08000b40c80b404011410003c0300c82c0400d00d0746102d12811350b40f04010381 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 789884451 1250 789883201 789883217
    0x30a05030c0d0513050d050a09030204020c0f0106230a051005070302190303020d0b09040203030904200315130c0207050f190303020303060a050607020319030c0b0f1909050706 77
    0x595020701510852a4404020482850300c000c010f038a201e2000020798180c001c0f05d140c40f511a11980072501c0e440480d4031480103541c9143d092000a5115401e03400ea0350050007400d40f1208400e0148500408180208852032002149400c040da003422003228468003020b0001c119645070301907420391100740c1c0d04040f4ac4031016824240d081156030440660300c00c0044c400c070410540c165020b4070300400007050410960880400f030088985c81958007a40c564424007040c0755516141d0031042184409070750500144042d20300300e000580041d101c0d0555011014885841c5081900f10b503445248600c0d002e00c02a0480350020b134450b001409044e0003640104265035268481503584481e251901e1108090b080c1d8034107009444e90003d58041d403081d54640c000240034503018055448440e00200640f005a1134020011080c0142106c11002d0080401888001c11401011140300d0b007503c0d0b40c040ea1500d0070001c807100c0c001c07042140c245480e1514280d14040758000034103605803805c505182d40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 789885701 1250 789884451 789884461
    0x30106050306400614070305101502070b071101020f0304270e0607030f0612051b041d030403020103060906031a0c0c0304030c05091006020318011b06091a09030a0503 73
    0x2e500350100f0b0b1082071821142401c402002074692240c95540520340c0f2001503a11054000c40c141e507425207841c2c0c0e40310300000c0c1c01c0c0102e2108900450b021034550044501041e0b03981c0060126400640d0141c8001021400c07900c0e5031758051141210000440c40550f1410741080c030101d5040f210462000100c20640185000004060b80040100b541c0d18007121418604130b500180a00b4102c01c0549116090800014a8182a0b5602102d15601801070111400e12070000e030460b00c05101c0180e071081d1680c1810300214800034048004101d00d0340a19510350443c00007409a68259000200c02d500c0e1810400120b80940c050b034440f0301840114000d00c1d21a035804134854040c90340040c0321760000090000c204501c1c0e41840003215820340b41900c1560b070f0300901107480c00302d5224100151708100a0100d0401a8900e00c400c0c003241410a880b030400c995a0201842800550486032950f40c4e294400030b01509840f400703070f1090820002601481d19803d515164001e10207090305209010005c15 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 789886951 1250 789885701 789885781
    0xc0c030712020c0a120b100e1306020f0f07050c0909100207320f030f070219090e0705040501120b0112080d050f1503070303050d0b040912020307030f0306081b040207120905030106050306 82
    0x8a903300701d86841c980b200c2001c421800743ea032240e482140c86115400c8500a28104824180e100d084800d000e400746103500303003511019501040301222541e00384240545c8580e0310030440401806910454a0145509515145070410900344010207501c28010360036000210030460342400c1d4140d035070302e1425180040c81d8118030000d401691515040c90140405030100141c003a04640048505000a9994080241000ca001072010300f00c6800300005000c802001310071120860300c12456075162074074010050302281c01c25280a1004400c0805003c1402c80810150040090440242805d80e00d1660003900a104100b40040602d0301d411554225540307692145001d103800946211208106820084d00c1340d00141007200402c0d11040e4100e4001e10a20800b01942c04a40c001c20004a420b202c8e0310803440c44080085e40250204000030010741c40c60b541902960702c90700c41d0540e49040104150a44100340c0040340030340d0041c401c100d000020440000f4105108030840d0840001d441e04174 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 789888201 1250 789886951 789886957
    0x30c03050d0f0c030c090506030f0910020319110901170c070807050d090f181e0c090f050d0507050402030709030b040c0e0c0c030712020c0a120b100e130602 69
    0x140e40145060036500b10b80c00c19030000350403000980c0c1c00b0404240501d40a840070102406103d402c280e0500019200c00c090040484c1c1103801c20080b607407003801e018010401e0b030384121403100e40c1c050310301000f418015440c0130301174101c3c0741c1180312401c11b440100020502500000000c19029504000c22422501c0004407484281c10051b2140c1d00c501038208681d84280c14061180040c07001000080d070581124000800d50301802401c8144c5a4a00100c0024102c0da4100d00442800c13442d40303880d0b459103481111166101074a5480b2110700e002000d58043c0c131f203507102602031305001c113880c40094400700d0340301d0a41e842110016202c2d140e80070111420f05c0702c1c0d000144020182c2d8184800c0c4030000762402d04865003010a068141d0f20004011618081c800c46180f00703034030511540707001944035042864200340501c1100d03d03041a440c002120101154443c000c0c110345034400c1c000744020581d9041d0320a00780d002600c90140fa19950b801c0c08c1000a1034003110201111452007041415011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 789889451 1250 789888201 789888217
    0x50606040c11030f120f1b0306060f1611090903091504050a260d050712030b0a0605041a1602101202030109060801180201050d0f0209031504050d020a0c03030c0305 72
    0x40f00d8660f89450410803440d0302441400d2020300394007002640b00c1c0a21036080d0711034001c03804151741c1c92815503c2e0403e15000a402581c1c4282d00344280894182010060042103070442c0c25070160f0010b03420a40030010f105140d05000d84194020006900000411208108800e4403550b80c0c9002d4071074103040c5400341c0d4000c20390003c2030b54800203400c038803140095540700d00e2040107102c40b071180a00c0703035550075a190024040b4a0510910020805036503004454034000c1c00c000c20a0403a00000030790501d40c980109001c0380011600780400202c00c00804070b001201114146882c030349002e030f60001c00d6101c400900c20802c40303054810071f51240c508280114000841951070796101c03202c50020380541d0081008035860b180e1505c0c00210b001080710031150701078488074542000d00c68050040c0081c0301e6107000c0917808100003c85603c0c2042031007c07610502042341041c0c2050701d46941080d02c6c80c4d440200310751000009001180403082980304803035050400400a441c5840c00b07492a000e1554 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 789890701 1250 789889451 789889453
    0x3050f19170f0c0d200927010b09041805010e0c040e03122d07260a0b010203130b04030b01050a06050d1d19060c05040e1801090b100e070804050606040c11 68
    0x260444d0781c21125015103111001100d03c4403400402d0343c00b05c1c0303040d02025070214020047c40010419054584000d00c10b02801400200f01340040314014603030419039001c210f809a544040c075081001d010301480d0102c40049078244207103003940072403c1e81d0307010300404040c1054010020032101140c002c5580040103850301030316078055480c8000c4130310000407940e002c041510382c80e8407491000344074480b680c0304403001c400c4c00c01c80d00c9100088009000d60030000e41940f00c1041944000324500d0860002040f11540066a0b10300b1441e001203960810790041c1e010302d540e90414000141c00c403042e43e50601c510103000a038403108580e500380b04964104002050b001e03802400615a1020703141c20080760146005000b0031100f40340c00c482d284524814807224040a60100703441a0840a14083c5601881d00205421400d9100e070400080c050300c5048820300782000803c003c130400c40e4200d62001a908007420a81f405803641510f0f1100142039600c21f0f59a9030200e0185800f5100c00c0c1510714500c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 789891951 1250 789890701 789890741
    0xf0f09031e0601090609090302061b042303100212013503030702060c0a020c090c0c0312190b090c03100f06032f04060c03050f19170f0c0d 61
    0x81650342c07a5002800741c540c00c14100400858183c1142c0181494190300d0b030300800b026a14608a0080c1001c0b0600305001d81208010025908140912440c0506003840d2172000c800078000805140409070405048518014052512040d10031803480341103c003810000e100014a13210716030764040c00030141ca52136051a01800036803070000405103100c3d800680844255484690101e400c5009007444000107a00c139001d0000c060030b01646464000f40780c3c1026905114040300340d203080d5042013814480c40307000384082201d0303841c2c03034041c181103201c0c01e0004004403c00340000c2070003410001c0c14003141160000205080301015915140189000d180310708065840d4107006000c1e041e000006098500240d040c0343c030113102110b203134600102c1d41803024600b40c0f900c2d000f41c40d2002c000006800b800018040b49003d03140700e100a0142202c010240201001d1081000e8492100b03101d04a41580188003008019921f5040082d080084544a151a0100c0c8511070019149446150180c04d080c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 789893201 1250 789891951 789892003
    0xb07021f05040b060f0609120307020a06031e0c08070804030e09040302010506040614030d03052203080103230d11010b0d0803010e091b010f030b09040c030c05060f0f0903 75
    0xd40c4420b000e01d20030a441d81c0207499140c1013140d0319541c10320715640300404008031501c5140400b4003072495400281034a060040c160000784210345154001e40200c0d41700c80c24420f9100b94045806025200d601c8200160300700702000904c0d058004002d00103004600006c6410300d0b01403c02c201d14200007e0040081d4541782c60001d0103400151180c0d80101c0c204200801c0b014619804003103400c602800810868154100440103003102610031100d0410300203018030040310348200c1d1652240213480d020b92a515619064800070103116003070180790912000c3c050001404580024103400900d80b12a20031500c10440c0c0c01080881507403a0701002e81c0c1d10308020003000c03030059030413100c42010003511603407103da41944946a82004c21314020310410303030814644c0103012800d10f2429a2030300003000703508403000c0b0341110000d48050b20311010a110030010400c485031300c10007914007514014240320b17034000c404042d13010756194241c034107001282c0d600590304c08028161751074012482058010307103d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 789894451 1250 789893201 789893263
    0x9120305070f0c0e09010b0f060904090f051c08220201030608070f0812040f0e090703060e03070b100602190519150b010207060905190506030711010501120b040b0702 73
    0x151007510108442000040c0c18a072041c4140c0d107c2c0d0a0103000042d12060070000c0242d80d9209000c01c03580540d031900600041400103081c990001d2245009000348002e11398034109600e50342040104000c18041044030f0f02101349402c0d42c0823280c0d0003280580700940e00c0143c001e000f10380c000e0103540c420740d0740001e00075007080c0c1510f0840301003e081e07c95088030614032100030300c01c07801882d9508890705020802c07140c0390a4010791200c0660305503201d25499a0700d04055403089400c0001b1540040385000c180003429412580240008181e075059038503204029458109202d03100c205e504a41010109000051143e9070005c041e4441e40706004196207440310700c0c001c5400e00912001d1421f060002c445d400040e80509030348042c2c840b040205d10b130004001000000310100381200030948800106030301d500010310700500b40c58a40d0310703c0245880d006403c640c016800880d881c0148040034010420541c085270300039400c06071810050f070f80d101e0140e24149800789415a4a002546143c0759100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 789895701 1250 789894451 789894473
    0x901110c0a020a0803070b0613092f030105070909020901050d060e0108060c09360109020309010f020f09100908070605030103030905030d14030a0b0402130e130309120305070f 77
    0x3108030b81004442d0b072100a04ea03074074000e101c0c0007005d022045012038103070b107840b8901406512a8100105003e40b46640c0d081c004d0404403903a054017040240a0507107280b808d800e0709214002940200100e280600c401003010a061040d880074550006e500c4456900c0303413003240c1e0355106c00d0b07105100c03041d902c081c9803040c40024413503d1828010903020801c562054401c991400f0401424080a107912611040000b26208110171440c40760303060032a41400e5170030045000701103400d00140c90389443e507044d0342901c070a44004140d0600c100b0420710021248015613510403825902401948404030040c0c0743d0700a690404d03c0188120640014282d81c410000c5042e64869541e8030300c15640c640c00d0580d21010358001c5800304200034079400b00100103901541d8420981078022618003100004501268014484800135071294a004d000e0b10318550305468028510100001554040d82c600a0504402d03020b510310703141070702c10700d00c0a1520a40950f00c450f9040001d82004200b1403428140d413039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 789896951 1250 789895701 789895703
    0x70c0b070b060d0b34020601230607150b03030301150f03050c0706090302010b220c1404030803060d080316090f050a090b03012003010e010e061005030901110c0a 71
    0x40d450070004419090074409030030169407108000d240c50b254076564401400075a11824510000e000388025600403550b00c070320580c80c5540142c05a54140360085884580c40c0459052403184924190308a1700d40c2011205e9050300640e2440c00c1c0703c1244030b184003030000000da95074188000301c008a0340d50004800d0b4040032101d501c1340d00c03040003800b80980070760380115030700c140d0054144104c038042005600104051807103440002240c1e00a000084c0310340c4141035064012001d030380101034420306a40b1a0805250090800400c409640c4141035424411760000604c42c01c8040003103000b58584280940c1302540c0200e03259240e103480081040c1003101da1011400003400500d00240c3d1140c210034100c20b50f07001a0032580041d0070108000c0c098801c041116803d90341c2c9028080941e00007810300d854240990b8076140d5603502d0481920b1444a045c0c100c3c4110807220400e015459803900c4c005403014007542083ea807a507650643e0680103140c0e078a1503044192000490160030440860340304416 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 789898201 1250 789896951 789896963
    0x1b0609200906010c02010c022d090a0e0c240a170609060306220b0408040f0801020a0210091115130b0c0a0b041b090209131a1005070c0b07 61
    0x128000c081000745105090311502e000c00c1041404001652103048080e41d0f00b800503202100c00c1140c18030010313004075400c080101007080c2010704803062500d040499000440300c0c2e81801180c035460743d46a101c8007600800c6201d60340e4410381074452403d0f4040780314480041c00d0455110b5014401c0036010040d011190341007000c409000801d01d182241055008043c060024880c2b0f41c0da409211a1000710740790b80c009a4805c03100c0e00c80c0040c100300d40c03040c4507610611404d603c4034034085140e03c02c0100c5400a00103079005000e400e80c569400140405011207034440070503a5401c600f0f121070140031800c0900d401500c03018944403104107480041c035101c0300446c0f908a00c40d075203e0104880d03018103003004070300b50481c40102003c01c02c8040d071150480d001b00120041048000c0040082440d20743c42100350b1500841c04d54124586000003c043c0c541061046c400e8800c403e041c4a41c1c05d0885c0645841800103002c0405d955101c1c0058400965210921400894881c10801c68541201800300c40b6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 789899451 1250 789898201 789898253
    0x2718100213050111121b01292425032d0818070e0711010506060a02060a151205150109090b070f030f061509061409011b0609 55
    0x1d07512a200c100358100c90a130107000300042c6034551580d194000c0742542e1100300940908031244d10f0a11404020703a0a40081591511800032072a060344008013006208080651703101030909442d00010703000050716800c550707507400000a19111006401c2100c00b403071031024201c80815400841569600a090102401e04114500305465000180c2c034901e001446c0000403400301c440343e0580b40100407420f001d880c5441e03100c020216443d88110f500e80d00050200c100383e60940300a10030f541d0818001c2c1d942d54a8810314020183d580c0d60060403600348070b540d0b0319040107800d1000c0303550409004070f03d44403002506a4100310b580c4100c40355200065104e444000180719140b48549052290b10100c00404c943c1e410704140c410451001c0c810090584801c1142150001c6214490240c20400100c801003103180078010001422500040180310001d03000e0440084104280c8440354403d1901025400c0c1802c0000c02e10314030072800801d5941800b00400030400a0380c8400c06041a003004a11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 789900701 1250 789899451 789899459
    0x91e1a010b0a0e030102040302060327030901170405010b150703031d190501060b04030609150506090a09170c1c030209090106030c030e060c030a0b2718100213 70
    0x244406081c81240118203040003048001c0c3c1c01203907103c1500000800050400b41d0301d4007c01c820307034801c03209403d407000b03075074907510b191a12444c40344491540384008504114440001030b041901040303030356049c80180d00c002020810250051400c3d0a80646148100d801c480070303000054200b0325046000ca801c1c54050750380100401c82c0700300c040b20954010480713151038248101c88100e1000d020360f203a548808011134803503c240000d00045105020000390f0032075608000744101c26106200e40030508110038007045545414000b0340040c016100000c1038480c82c41c100c0d1445030100b2000300500400b0891b0b1910a03008551508102c105d031003954102460340074200c040b4403070603607000d0384180102c0051000c82d100345c1c080600840c041c10000364040d101e00c449840c00c5401c64404405050010402c440b02405026a14110b001a16040f080310f13001c0d0100c14102600d20385000c00112250001941116984010b0031020382d980f055038200e10404618a010f5031040c40410704040181d00005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 789901951 1250 789900701 789900743
    0x14130311010e0f13020318060405070914060906121e06010905070f0212030a11180310090f020d020612070207060f09080d030e07051005120105032e091e 67
    0x41c10f4084010505403503050301040000080d0005444101c15034034502d0440c84c13a220070092103004030b000e9001014100d240100240968141d0b40d03a10391000c81400601c9425190102d1076904035070211070003449c0c0c100c400d42c55803a104901001e291003000b0b00700e60014040b40407a50318180e4030303c08810f00c52990307640801e0f122101c06840c01c0005034469960f440341c41004402454000d840035001141808094401e0301d50f980007603001200a20f031908461001c1e04d0b0421400c21a004c8000003440550419120309180840810010f4041c0183c20404011903807981c0454003080700480803080103003041403009503100d8590091320003007140407006846540c01031a5180484010700d006000c04407494108402410070150f80c001070f882600004607650fa20300c10101710411140e035446803075000b000b003809840130060b07103d14007030b80000404140e0912100d0a460000030402d03440301c001c002c2180b68400170924050003410f0703400c4a065460000300b6511032801103a0044660200f50400c1034802c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 789903201 1250 789901951 789901969
    0xc07030f0c06210b0109181a0906010c020d02060d051014031204261e060a0204030c1a04121101030e0d0f0e06040e1510020a020d0314130311010e 64
    0xc03034029604443d00b00c06422580d0000080003006140602c3d0040d034520595107001c044040b604000341d1103204010701e4107040400420590000c940b6044281020340003e864503145960280c040d41e2250b400d001551507510490702d11004a0504008030300d0640c002842c2a90b450081e00659003c0ca030200c1c09900e400900c0c0030140c0389000d4241e103418506080407814200c188146d0340701c540303c401c40d0408181d00307000904400c00d003084000a92400f2882150070000d004101c416240d1050206201151340d00071a0b074107641c8040d809400c013480c0d18104881a02403503109070341c82d211027000f58042010084a60345252000c1c0c07002d1115200d401c51298491402c0442c20f40003525905c0690103191003044842403c0501522252910351a480a03a00e491012545000700201101c4000318038180080c60142ca03036401d2010b015030001076800030742032050040e4050204005000502c6800c404c0c90121010210307d61440858540e9070314050100c1060100d0107801f160101841e08801d04150b074103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 789904451 1250 789903201 789903227
    0x70302030408091c02090c0a090e01240207080f0d090914072109060b0a1a09090c0408010e1b190b030408040f0602060603010f1b0c06020c07030f0c06 66
    0x7078141011062070510070604c801c0e45202592030440d002003800360721140c03201030085100c43c0c41e84c0e40e18412074501500c010606d0b840805042e15401c01000407120384003121500c0e611201c1102c07850768101c42c00328500f480c2d0350041c001501880c100070490100c00100c01120721000d4403805121a62140d006003100c041e946484500c07941d40380080d03580da21410140303080c01d840e145202070011a0700c0e4510300300c480140007290074a40da5180385080c0c0c5046401c44009260361110b4280e598606495064280100f44129005001c034030003251241c50800c080e9406855003400820481c90300e6074070a6600c8840013038201440c006034080710607a0500c09560b101d07020080505410003440c0c415070f0911036000800541301900240300c04030300c03002018240c1004043c1c6900400035401c0c694105421101c8294007c5209498015401c1441c02525640d0200351100e04005041c44018140400030348250917031603580d80240c00c0c011040044100700598a50f005107982207165865107400d80d111200c080c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 789905701 1250 789904451 789904463
    0x70b04060c0302190809010e060d0603050c091605070b090703120203130f051503060d060228020606011d01020a06050a020a02010605100503012603030a230402010522080708070e0703020304 83
    0x1004080343d501901c01c10b042317407002402051a003100742c020038040703e40c240c0007210181c1080c200101c0518210b80030b980c210f4940d48030000307000d1402002410320711a41500401004c40680011107212090101200654008409004107900031000035100d038004055507040c0388802c2008117466581c0041c0307134141d8030054210240890000c00016982e00b00901c11a4800c0d0ba0303229880c001107142c0080c01011070b084004020143e002c000e001c07054203510320904219170051040007121f84e1300c10000e01d2030846c504008140c01001d980100d04102c1a5600902039508103000d0102d040322640c020300f51120154000c00085031141c0800c040300d90701c0c00c10400007030020300040c03081d00504400e9117503600e0b6501010b0079002054030b44a0468004440200f400b0b82d0300d90307001c2a030301c0c45034100790ba00d21000c04c0b04144500d030640c0081e0040c0180000507a00030040c802c10702c060b0100c0039090014111680451303011664035466907546407101e0040c210640d03100404121a14064020350340503541c084 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 789906951 1250 789905701 789905707
    0x60603030f0c03090a060c05060c1624060e06100810060813050708030403060e0109170f0c1c030c021605060702010905190e1005010e0f03070b04060c03021908 70
    0x500c04070180d8220201c1299180030400c000c1c089135070781540001c000c28540c0c1b01e8080503200c504200e81480d02c01840c80c0c0c0762000c00c0041240900a81c04d0801c01d595126141c041046903000f900845c41001c2016001542e151600106407204a10995403041400300c8042d20f0300c201c1d44008990140c01581c0341d050030040340c1c41c1403007803d010365030b040d50156100c41d0120b02800c80361901c0c2d151416551018040b030300001000e100380b10040c041c00c04440c160000901181406940da44020402d08901940201c40030842454210024040b580024448403c44804444c0c03154001c1c03600c41201403600100c1d00c0d00303060b4205580080303a000148155100344040443c604020b20020b0780c07050380101d040044405003c0f40326030321070066076110034284a524440b0340c14100c03003018540f80030f003000e494a0110741007080342d81e074084027082d0b0581040e599408a64481c00c0428945000c0c0e8111680d408000300340807e0040d0302600035071499000c1d41c02c40701016020420061812001140648034107010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 789908201 1250 789906951 789906967
    0x8030702180c0c03040e010609090606080f150310230709060e0a03080a0507060c0e0d261b070e01150503040c091107060e01061d07110615040e06060303 67
    0x34242442d070007850782c014076142411140301c060540d48103801024034a00f1313a00041c81a681c1c001152006400300307440c2042500d0402034050148640189200010f074800000111142c006070004007104070054100c2d41800800314108020b8207000c012074407030040381010b918221000000d11406445191120f03e411810b10300d0413511200881d615507044000401c000000484030802412404860b030360f10b90b120011850709000341d4070740ca0b1403041000410080c405040c0c0d54020b078240e416a2115041602c0c401c106034030112a609040a0750101201003400040801d01900381c984164041080c1c40708240c8904568a4401c020301448400101d800200b014150080c0000c40d0014011202c2c5c81e501c6a80da18494182e0314140821054900040303403a6040200c0c074050b03400c080002000030700101e8103108400320003d59001e91058040c490b100881c0c0010b0045000800e481d01e00c0058078a42d16010950201d582d180c1d440c124012032a252000031034a0010a003035003d030350700801842c682621 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 789909451 1250 789908201 789908239
    0x8040506030c21010e1b19110601060903031e020a0b0601051621030204080a0f0311240c1e03060411040e0f0619030b0406091a010f08030702 62
    0x20050102d480b82d44100710440311032122104140c843c00040a4059440d81400511104031102800c0c000e03409681d049017900c9030501d0002d46003d8a4a55034108404480700c000302d50401d0115210304082c0558000450010f500c40b0f000d605a80c02a29001d140f400fa5141414007004902401d40050300311288140c00100c1c0c943e420394102405140250070206036010707444480d00c8008045a103c1904e10300010013451003420341410100d182411406c040c036200b00a502e555046200402102e0010000c20415005910400c1e03000c0e042ca044036400340f036498090b03506052060f16468000007400000340b480c443e100403075010780503c0300950360b418000f0003040120307000a000c2c00c0e0301a03182d0f400c82441e000100041c100a1540c1d41d42a40300c1d0400203660086020040d105a0103010014810001900c0c1ca03d603084c22240d1240440e601030703459041000003000000340081c00701990780c1d80b070404107140b211803c1c140d03020b0002c00100c2c5940c45483c44d503240315020000b500300000b41910b09503404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 789910701 1250 789909451 789909457
    0x32a0d12110d05010510020a020102060408210c07050106120305180a05130b0901060c0b011205150a0207020a0503190f06020f0f04060305010503030f121504060801091e08040506 78
    0xe011100412000041454109542c0000c00c240d074041da550b03001044035240c105811411840c050019001c0e041d02c07500002c1d1180c0000f8005480420001445200340484502c40c640300c00b035010240c0e0040c2070034201030032150301541068a0039801c20300040340300c0207101254481c055140e215649400c0d6014000b00c600842c401d00182c0c03044007140c0000e0030380c40d0303c41c0b0604821507204000940000340c4081240111042e04044100300624602800041d68200c645054841c4400000030f0309a551a10070304e030400301440240d11228882c02d00c180d40c1400c0d005000654401c4800800168546061640d03580d5000c404518283e41d05d00c00c1c00105004113427114002e03005150151420801e464460320ba50320900d603040c2c120400040800159516216480c00f43c981100031318500124074450405134040c01c0810b548841d030f044085001c1c0010160041074915001e0000c0c4165a40c4c0e541242c005e0100240c1610850308204408611400b82020600b000c0e07800341e40c542c10181000180019a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 789911951 1250 789910701 789910727
    0x2e1202040b04090b0f06030702010609110a020d05030901020d150314010c0519140f03011a040302031b0409231501030c030627081c0e0d0e0a090509032a0d 68
    0x1105170040c0080c3d615a84010343c45030710b10360004a0000c4c0780105100859030800c00e4004081350621104001c1d66000c580600001c0e114a03106031682c8031210b9841c020310419460076241483c0000552000200400007412640070b0101140880c80c0341c180e00f4203849580c212940011001c010280342005102942120000f03541f03003001508001d124410050b034080b1030701ca6001e100c003000401030720401021410004400c1450396007442d14607408071780e0341c1d06074603c011400911214403062949803680000003a80d0084000c0c81c1d04820070b030410850300801000c03c9218000d40c01240400300c004442c5604803540000c480c007000c1d243d61030b88002016500d00300c092445a05000918840710f0568040125004860b0140d6134101ca5480303140c2442c001c51020245818032403035105980c00400c2080c1100440c1c104500a4140100041d403415020f80081c2c0c1d000c3e10740400c4c08131946001001d000140008003201001c050a01e4000302909410b2052043c198400c07141d507141c46205110800c092 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 789913201 1250 789911951 789911959
    0x203180621010803070203011503110609220f06082d031b010204080d0801180b0a12060b091005030d030c0905060a11070b0f0a0e2e1202040b04090b 65
    0x20780e4400c0d100d41e1440c070007a0b0150b21641d00c0890324605502d0280700b26403549030720f18034109995241da03441038a41c0020588080c4203680c08030318040c1d25107030b01c5012500040c40c40207010110110800540045c010000c01c00719052810300f003c900d4400015403540c881032800354041c1d00c0000210f0300c40d000c00700070303002150300c7c0402c0c0030700c1160300d90389000342e10f0703000290002503143c030700b0841814a440e100300b03040b00400105100400000c0440160f00403250f154003400704440542d240410180381c0c081d8000d64140c803e0300500d04c141324980e0320460400c80d044800d510707140c07150340e000c0352008154002c00d64580c011520403490360f0b0080e40802c07204502c80c2041042c1556520009030260046802ca5001c80c441c119140b07081c0a00707220440161400e41580340c20103568184200190141010303d0003400390704515085140c2d035040e602c0034600d508110800e5252852622940c6203100c109003c0003013503c1d441c58280401c4d00d4000c1e10191180102e1407402c03c0e1400f0a0107000c1c00a8103520341d08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 789914451 1250 789913201 789913237
    0x20d02040509100611030a0906050721030b12011a010f0903020901031406060405070f030209031204030c06020d020309031c0c0204060b090a12080301030807031b0f0b060102031806 79
    0xc01d4455100b00741c8107800e042c61500d145850144090500350f49020b031020743d500f04101c683d92240d000302180043d5441482d09540303a42c0c02e072502c07080d0403421b00c41c0c1059030042c00780352001c2c00d030b07158000300c1c2e1448003551145010841803e01a090350480080750320f48204903064a203165100e9400d25801c602c051401035101c03641c80e00030486000e803c0c2c005480c1c00a01400c00c030a07034081002901d8203c0000e80d0204624a41075200516008401c4011402c16400044d14099658100702011060604608180d511681c1e071801070003100041c0b090001501809800d6000140007109480319104060003502c2c00070b007807141c4001d031941490800c006000c2c442440801580706e5105480240800f1908555680c12803000c000d0300001e90b500045441c4400c1003180b001500100507281100e91062a85440d01110303d0241c40c2001c1001d803800384021618400002d0010305600740b0321250041202502c25110340d80126241e00c10034a0000303401e0b60186c80c02046007007850040c081000d0101203e64 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 789915701 1250 789914451 789914459
    0x50103080702060918130204050106020a030801031704080318011103070309051c0b040b070201150315050c0c0a1208180a02120c360405070e040f020607051f0509030706020d0204 78
    0x3170b100c042520700f1406c0e180d9a00790202103080900c200f502401c4540010075070f880059600604140301400010680524901281c0030006d0050603200034185102c2966143c280303c42c80e90000c000003c0345240042c003055070b8400010000300c1102d40868240da90107002c2400c2409200360154200004002490440121004190385c0800240903911038101204a030070440d5000303007074039a440340e8040c03080030500301000010745e80d058021040c0c202e0f923404501e640d610964042035014200003208103005000c404000c00003616012062407805454007075007a1a08111514006102c5106075001c1d80040182409854800181c151050200084030500010742000c074240c004080d071090524040c0021036484904000241d003c4410700300581c4100d86010703241c403030b034500d11441414403c0e0111404642071001544c5210409500507100d5540c0f0001381c9000e81c2c0e98500140314034442c40300e8041c848041d03003003030141a0003040d100c0000d5080000e6500d07040002c3d403015640310a410b5003080002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 789916951 1250 789915701 789915739
    0x7080405100507021201050928052e06060e0613091e0b030d0503010618080703140d1106150402160807172b200a09090501030807020609 60
    0x3602020303250b442e01d07210203151041c8804040442091603903641814208526201c0001e1604840c607429410030b0004808090290280d0b041c0701e401030814003400c0310340705035121034141703031030400010303d10841e80d80e01940480d00454140e4003602d030000d11050042c80d001c0c03030104084c20303c168400140340e035455520000c85003218812004042207040002800c1280d03261481110700503002907002e013003001e40822004007988014069001400b5030503c2542030055103000c03000c00b80143d40105d51105440782003444110021004102c01c2e44500907254200c0c07807141e91000309040703c4034014041900d9604440c0d08185e00c4c0d400e6607804c01e500f804000301c3c0701c50904808070424000d82001d0380c0c0b448542000081c02c0311192003a4000b1104102c1701c81d80d1070402461a5082050004110001952501c13042c041c0c151208000440c000070000086140d4ec00b034000d1165150544600ca001903840700b001060702c400b4440505146001e104803000350605a00501400782c1c001c198407071240303002c515a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 789918201 1250 789916951 789916969
    0x8060d0519030e01090e0103020a030f0317040516080c0306013c03020f01050f070b0a0e0d03150f030809150903030409060f0e010e13021215060a1d0a0207080405 71
    0x90b0001502d14401c03126035604901064041c0046a100c09600c3d811500440c80c028a030784401001020008031740c5092520460001d83e880c1071001c42a4242d00f480c0c10503070f6940d402d00030b409035207100e507150005607a80c0c0001d804660481c0a8040c0c6207070307803a11100382002048504100c0c0c86508401018601c01e400300811601c12170a0214400701c141980148480d8103a18900c15050207400c100043c00140c3d000169031100d54081c0500c8070a540e901c2402003d04120491308115126140c1f400307040c503805070410340a00100754a01c40a0a6454043d80300315402d500c0b010b00980d00802040b50b440c00c1540782c00111501c068801031508201d000820315540c0150f1060f04c1e01070340c480b0180320031a000401d0200518000d0f4980340380b5414690284c8820b54003400001c110300600308501d0442d00c5401d00d080d4080f864a095a01c0c5004000180b498140100c84643c480e909052001c0350111121400010841c00600030840790383c0c1e24403070b0350029030082c08141c07000c103001d01002400340c0c2c0d440d000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 789919451 1250 789918201 789918203
    0x10e070801050a0f090203151f0e060f0108130b060619021b0d030503060d11030d050915160b1e0a02070219050123040f0801020a09120308060d0519 65
    0x211031820300421021585503841c040c01301410582e00c08090307070300002d429a0030840d00c1a07602850702e85694400421801108d0302c6540820000000b801000303071640640304540655000541c01001c0d0011035058604541c02e4122544a6484002151003132118a502140140c00a4548480d140b40d60615240300342d00100141d0000611217140d003540842100703c0705060750f051444030313083c4c0d078003070b20a0000401d03190003a0103440a0105202403404505540b402c06019207510101e40c0b9001046540190986030007241000c0003040306140d030008444280040b008002c044400c5540c0b0a290b0b48800303081c00050342c0c00f40310034158035501c1c0701409000e000f45640c010f076a404548140703c5910486029078801400180c070030841c0c0d9804c91491040305403200f16100b03207c02c1ea00e515812601130340c1c00034006030141003070104030100154000d06480d081030300c515043e90f03540c10351032301c0101ea02c0c5001000a8880404034100b070500340c040b03103401c500c03c50030340d0701c0071000404014410150541c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 789920701 1250 789919451 789919453
    0x30302160b220c170a12020d17012907050616080906160503060a0e013c1404140708010e181906060e04030c3c05010e0708 54
    0x60010b004114540040a14010300740c400305040d103911803480245061003986144101e000141d91500f074148494506a9484900c103c4484890038000399075001d007100a4021809844c1d508041e002c1c3c1c0c030000c5040b10b0041071200451121594138088418501a010f8030f194414000f26002400502c0a24492400e030080384860741c804000081001c50060020f4076243c11400030f000341500415642c240881182c1056a03480e11107202082c010352031903100d00c1035425180008144103010030000e00701c10b84030900794915440c2d1448000c01c407008000000d40b4449000e0360400c1002007107001c20b403050720014400a00b0413600402c150080008070713451000030b100100103100520000e04602d0300a40c05201c40d0712335202800820b03541e41c05032070b009030290111080c16002c2080c80c0e040360000d0010070081d0226410300b460013803c0320350f810400b00c60f113003891551800410002044000302d03c2005035200b07201c2c0c540340c020480381c078112201501d66540700c0d5403842d90b243d0100010070082c50341c0300c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 789921951 1250 789920701 789920723
    0x51023070c050609010206040609050309132004050315040314160b070e0a03080f07050726010207020d021908032b0b0d02090c090a030309060f0c03090b0703030216 72
    0x1180080744034001d5080a449010180516001c59a0000b5800d910070b5100708000f81a10751030410b10300d90b019001d50f03558807040e240e4524011040d2900b02c036403900342100a460040448500041c03072030041c0c0c003500342c155004030303520b0f601d01d140107003400d03041030203821b00d208002ca4089011015903c800c5241d41e0003600b048003342003000806030f02e40d01040b0f07450080c285030300c81d00c00a2080c02d410700c40039200d0f02001c10b226103091005030846038007550000845200a0780c40503854001003040d80f81110301900301d48500000700b418000c4540380c0341d0003400c180c5102400d81c20860b042030500680c40c01e04000e0400802d03e0341081008009a458042d010002d480b2a42d402640841c954101d1865940c146206081d141d1101c0780f1181000368115464401d503aa440704403505800b8030031009074821542d54000007070640022410041d40c0a43c0e4034280c460306a0801a503292240800090000d500e0440c00c120708000d40380506201486072a015140c0503c0303550300f042c0b0201c264820f80c0c003c4c01c40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 789923201 1250 789921951 789921953
    0x2030d050705150115030c1205040506010806010e0c0f250b06040f020c100506010c170301090e010506010f031d0303040b01050307061412060f1f2705102307 69
    0x7007100801409240f0036510142d070410b030100e42c02c0200600414145600c4040304000280139910702c3c1e441c05a549000c100c07500e8a410701d203554520a207d000390310b01903c2d0010400c01d000303d04d4144200780c08201c20345490207500b1051910383c0081006407281340da41420841c01c0d526007c0c0e100009d4002c6c6c080d81d4031410584100411214040c0003d86413510421690116080208ac44a0307480f5130300304001503035942da03001654402454000209904e8000e02d01426060f8004c0185060f180c49090800200116010301350803107a00b980d0507800f00e22074030700888140c0e209403c80a104c60404981001221950014074030350340066070129482c9864100510481c1801c01c541e90042c2150701d04802807243c0500c56810070720620640700c0c0c480d840c00d000242d40e922180e011a0243d60090407401e401070400d03401d42c6101908010010019010141e41c0c107624108009241041551001001e205071604040125035030384843c2050601407601c0c0c070140c04100cac3c40780c0340843d0307944d001c240e40e559000c03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 789924451 1250 789923201 789923203
    0x30f070206130f061814070303180e0414100f021e0f12100e04050c0f46060c03030c0f08060f121b0102060105241602030d050705 57
    0x91007940d82c21120401c0380e01041401201058140d0007120004980c0500703001980c0000f105c4502610102030128241d41d0403c0c0056210304890081d075400d40f0310000c00e1001c1640c0401032081c8020081c0c4400458040741c0e56a0f40e41800b034002108441080c1c2074198140162064107480c40703a0154003007101c511119451802c0c521002022080c03a00d001400e000d410f10701c0c02000040030418000d600080c03205c1e8004540103002e402c0d0403003000c01510307161512070740d110005004d803802045507a004004a0500e040d0015031500c50f1010301d001c504109083c680c1c41c1e561a000ca410310303100012410032021031088038801424130755490f070700240011300700503003030f00c00c02460502085072500030008801d5011004c50303000a0210f40390410b8443c440006460803840d10080b200902583c19104482d21418403080800d50082c2c003582c1c180e0303070703103004020701c0805680c440c00d032030304420020a8802a400c8000d00c52010b810042c8100500396401207450301200390401808500d00244070f00500034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 789925701 1250 789924451 789924463
    0xd0602211003020913120c0302030f19300f0207021002030a0f0e060f0f09131b170f06280f0b0a090501050901050f0d0603020a120807030e011103030f0702 68
    0x444120344409a0042d940c1b039840303040032081b0b81010032416014400405109104886e04c001004000c65182c956414189448840503050207000c1043d800040c100c545440c002031483d9189000302002c0d0100c02d0100c50043c041c0005210515a0300308408030041e903500510f1074200d13515500654803070300d107858090002d01411000c0800d0084200c031b0082a0743c1c1300d90032170302c14031103c0d80090341724416420784c0e8030759024070300c80e2581c418083b01203030410303614645c00101c10350309030183ca0a040c24200070a80c0d101c10ba22003200b882c2018040002c40d801c1110708855089000600700e40c000800b403d40c8145080c40c1140106043c0e09807507010840107040703c000e0005042110f03000f030314000190b1b0000c0c01d1300030644141c03814000c0c04100d00c00b00768069415034040000102e000d96440d00b0403084d0300c0c010f2940e030108a100340c030b04440216509600000c0040395982c00040f1526102c20b40d182a5840460321403010304001000025040300329052014501846850340410030b14105400003071708100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 789926951 1250 789925701 789925711
    0x50109052205071e09020c0a050c010309050a0b0c040e0c0a0320090904060608241e1f121506050102060705250501060e0702060c03060d06022110030209 67
    0x604034640301c0c00842e0010540508541040e4103c0c0d0200f900301610325444501d50b8460410b480c8007040710800090702040350b0160341c0c443c0c1c090340c0e0740c511070100550480b11026805441a0b200e82c941d200041c04214800e50880001814142003681d42d845664110b20112080b00010310007199450800d500741c050308078410305000c02080e00c0004d9842004041c09101c40062007045084082014820b5982c45100a08404400d55a0b24150300e840c0c01c03040190b000201042120900c0017407561040000c0c03600400750341c014001c41c540c0741c0058084a800c800c0700040e501a0504600045203030119449c0400e191251420f03025460292404204031085070380329a055410110030009525440301c21503264080c80c820380d400400120701c020b40b503407c6a100040c2250f04e00b24020580c07003082010640f080c51998215030295a481c000301031580800d1750000d4009062000c018001001c0c0e030007507c0b1214218501c0a1015040928150400020b803544248032100c0041031095040890000e6404 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 789928057 1106 789926951 789927001
    0xa050d0e012c0601060f0f1101090605190605060a0c061805071e080a140322061407020d0b040804030c0603020909180a03030b01090905010905 63
    0x292442c00d118910b825040541240c20001c0c416040c1c8155646a07801109106c90036034814060342062001d0001038500400c0541d42441010b110380c0c02204045898203040c2c81656026440349115079550707040c600103002c1a140d0308c046815440c102d01d4803100303006181c00c00030010841ca0408550742800c2d900c0d000d052000c0003070000280c544030041c2065210216440307040c000b405106000054008071142004560398190a1461240740025285442c5401c50b18005241041003041d00400320702e0003d00a165110b02c6d190070310092000800c0c40c2c5205a000a200c1c0e6201c003000602c08400e00b4000b90400140d50183c030011507103c1c4412701030980340c0704050060b40202400b540200448400105100280c0903c1200084d480c0c01500380c51495440c124054040541124148110f03410001019001d51281d21f00a01c031141d000550b604060801c3c01064209043d51109 = true := by decide +kernel

theorem cover : BRFrame.Cov 789748201 789928057 := by
  have h0 := BRFrame.cov_init 789748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 789748201 ≤ n) (h2 : n < 789928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
