-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5545
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:13:26.792642+00:00
-- url     : https://prove2.me/submissions/6a45f4a9-9537-42d0-817e-8a058e270b93

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 997122302 ≤ n < 997302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 997123552 1250 997122302 997122307
    0xb060312160c530a020102010608010c0503130305071b1e08101a03070312021b0102211b011b0201060b0403080918090c0a1410030f0f0203090c090f072102 68
    0x65050943c250007943c0d10382e5070f9000080441c3c150368080c0300e598006c00094009010069000340c006289110081c10841e07400c0301020008107041c4940191507803994400110181070000390351180780d12109110348806070b2026011310000d09500c800307081c1112407242c01445070044500c40880540403506140c01c2240c055004407100d40e404015120042d80600c10650074100381e0b00300282016003e0300c1c50300c4801c0005480341d8450340c1c00240450404450306040c5c6607a4802e0134407090300e114040c031210303184800100195108006500c510340081885003021f0400c2a4503205a007031b01c081d4800d0740320901060000300041201d007002400c44100c0107140c8102c100c0e80c40c032480020003041c0c443d40116405419009454281a00c104000c2c040c00d408880c210608400040c03507600e50354441e14201900e440814044140c190444003c000c0021020b42d00ca25020046a6950f10b400c24840e220360700200202e90007418800e103903401039031960342c4c0303480310710314001c2a0b04101018071031446001d508 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 997124802 1250 997123552 997123679
    0x602120c072310112a1b150d0e10060803030a02031017030a03050c030c0304150b0a030302100c18120203070302090a050a0605120a0b060312160c 64
    0x25108a40301c01490491154640916000c12040306481d1140950800c501107100160850005286e01140504658060f8201d07030620100b2958200c81140001e582c0700480c0a04007030040307400081c0a0b00d1f0b13920846403e4980c6121070320540b0700c6072017042419001040442c081100e903400569100810100c05200142d03203400c40c02200319104c0300c2c181c0940001ca843ca0090780c1c513000b0641c0215402c80301604608002444c010380d403102500c02010203e48200c01d00a03141c840d000354a0210009040044480d541d08010b0b40315640c1080b15a80c182c030b0a203000f0805c5001d03400148070b8100707402c00b40c000340c2d0602c0203041c000340410034142da251040140010060f6500c84580c0c2c1b01d07a5100700301096070304210300082d05075089508294490980103410080d000b800199180046800c070390400c2003503c43d00c0110382030105406502074000c10029409960001841c200e50003144100c84421007155900340d101d140e40384400c011a00035410028601e456030f90280d0403004078142d405d084180807078 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 997126052 1250 997124802 997124833
    0x3031107080309060a0c18050409030e03061815040b0402060a0306181a0301050f1915141305072114100603150e0406050403050d02070602120c0723 65
    0x1c540f200d42e20340c051010044040454000d8600380d98103410041c1046070402c000340030300f50140c00b960703000710340d241c40200c00d040c4a80c0003002881d4002c1c09031122820300008614000d0030709000050740d842013843e0a9102c5079007441703903803045405c04082c50f5181c1700c40e402c005240e4072000d094410075440b0040850350701c041e11080207040c40c6484001404600900d180711300240036080e4a882a458201009a60300303072600c1f03065201318003034144013030756034030307500c000000d102e0555200b0701c1403403c20000c2031103410b40d9254280c0303803812261112112010050507090341c108954441c006680181d0b41d41c56122003100d0300540c4102c0c004080761030403090170041c1d1014011034a01c2a02d400c10700041080d107800d48204040646d120b84c41e42d101170b040c4980b03080e20680103800103207680d0f560300c0014103040c1716806561000d541414250760b03411290600202940080104598440d01600450071113a0b862040311718196101500401131181c003d10351020340316401e00d440440c091000d00c00700005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 997127302 1250 997126052 997126057
    0x207031107060804141b21160e1f060c032c09100605030c210a05040b0f010e04021e060a0203070c0501090612050910021206100305130303110708 64
    0x3110354508501c1e10b01070400c0091702c510781d00c4100c060740045c900348252066812025802083c01d4440103e44a001d081343d00500d00a400c41c02000c0c05210111020480e881030303c002150140b6405d15502c8c0c640f502801c00480c103034050103008100e40403041240d64000ca641c14445e9000342000c01102511321140d20715505017100240f51002e28240101031840c000d82c1e801d0b000721031812410205030800801612602c00a040220030030000b040c201c810b0402d1884000800b4401510507140e070920081e502c003e004281c40469401d22005c0004140c142d420481138103c4020181c10b1656441d00c2d000d129400164403156a01a0f125202078002c58840030010203d0329200c1d8000d694884450410f04201039050b003001d810444c0c001c80c1000300d030b0b41c4142f40811204007804005081d448140925140c442d480040d0328071980081095015040078a0030f03580f1403003084c1c59000c00700385174040480c03c40e8001c032403a03144440c0c101c0c02c10000c0f034866803101000c911031041d514986041ca03114503003580c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 997128552 1250 997127302 997127309
    0x1170f040201030f06080705010509041b0207060311071a0405070305030f0a080612060105090a020c070b0a030b0117010909020319050a1a06010f0509031c09060318150207031107 78
    0x245400800d000840d41d141c46854615000070408200480c00c050600ba1143d03281d110301c0b81000004150b0450035569640304200b00340c8420510b0300043e0960300c000e91140c0b41c074440c0030080f92908114201e5001c5040032a20440c0d402000d004503e1924910304d02940e0010f00283d0b824864040040b000070020001001c0c0894019445502c80742188401003480c50000c0c00c003801640a03880c80c14106500140d01415540212440006950b0342c8103a00300a0040151102ca40d10030300c81c0000b00c01c140d460051010340d0255806105c0c0700e2100c001502d000f040941618090002c0c07100410942345243d0004107414802000c1e41c01008038503a02501e618000407080d03410b600b12030140d404000400284511a941c84c4601620a2400e00000b9003d028402c10510901000140850580d038041c0001c10403441c06030381c0100c0c4161040d400500c0c813000c60050001091030118440c50348031144580e40758082c1d03c0b0a00e062111140c8000b00d0280d08208800c8003070005041310082c0d008814400f01018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 997129802 1250 997128552 997128571
    0x70c06020c0f030a050c010c02180c040504050a05240102030c070b12010f030f030806010c0503030708070201050633070b010306020d0c0f05120415020a1206060318030e0117 76
    0x9035000310411501100c2e585907140f0a42c419848100016004545024005c900742407451912805001040b800d0030519001040c1c030014000304640070343c0302c0020380240d0b0400e030780401c030503920902c0040440d0300907621407901c00007855130081461000c4032020b01e25101032050701c0c1044110440545404000e401094a201d80410000d50101207000c40e5030042400c1c43c1c0b6084010701d542c8409040a80301c0f00c0240400136020000340659001e006040481d5030310a003125030304d1a0118000700310160070b84401c0e0041d424400814810700c0c1040c20f103084180c41c2031407140c170000f00a0120355110103940c1e000d2016802400b0a0003c04c1f1142521402140600c2016a6943d001d10f00c03031048420f82000401486882c0c3e20503280c0b5640300c0241c0e06000428000650980c4032418502c0900c1d02c101d0224016a00014042e15419030080180b480b01e8001030301409802d460340010b400340c4084643c00305282d48104040b4020a04c1110824500360044c1050540802001c140d44040d500895003401d6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 997131052 1250 997129802 997129813
    0xc0f1203061d09210d05150a030b0403090f1508150306070504060e040c080c1c18050105060a030b072d090e24130216050a020306131214070c0602 64
    0x14018000c0c491050308003022200c0e2804c20940c2824041207010b02c03001440890790b240001041301c003522039071100765a001450040000d42c0d0746010b181c0e1740d02c00c8a044002079804800021590100b00e590000c1d04c900c012503c0b220341400d903045403282c00007814000070108030b0300303d20504e440034091140115640e5036400d59413410410041d0007424100c80450017185064a5013071455400b0b6a42500405220402c0d81c0d182d603281b918680e820480c00d00c4a844a00d0400210442c90b443d454020340340b803140d0024086a0ba1b42c07000c02c840b00800b44005421a80d800002071111481003030b80d010410900c0000c12241311311020040500c04a04120301c010034284081404401e003000c143d50390000701c00349070411045403000f3303000d1144100d86550b806520f000d8100304c0e4551450f01901c0b0070610f44848141c42038014140940e07143c110030401d074064054000414060000c11982610041d000071152802e06000380d81101c21903040c07440700e0100c800500c0060001904002c0d0f0f1030042803998020107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 997132302 1250 997131052 997131061
    0x606030c1d15040b01020a1a06120105040b0c130308120123010906210f020a17090c100509060304030e1f0804060b04110309010504060c0c0f1203061d 66
    0x11459051100700300a11031140782000710350810a0705410701028140e601043c850b19100040c3d18204840070010100039289844810055070712803040c1c8205030445203030703020301c02800c001e034201c901c140c401611510b007450006003103800c100018181401d52603140c40109a59407100c19641e0001c8058141d03c4c15003c00403c80c207a620750212501000f40807014030400300b40c6001078140c1c43c0c24032859051003491501c01c002c8541c0032008840d03060031094280400360a40b491840258005200c1c007000c0390003081c2d80d842000340c4010701c2d84640b482000403c00c00310f880c1c04100c801104000140e00708482048990219144c02c00610f000d00c3c07203901c41c581d18502c42d1080007a6102d60034446015048000f04080500d54410042a080381e0031520000d5410f05410204001e00105032030100b1a607000018400c1482d8154019032059000714002c01405080c00401c40c1d5600304410041d01100342c982e0703030201082d82000c000301450501d08000605030b175034900d0056000380c41148041d41d045a03c0400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 997133552 1250 997132302 997132319
    0x6041a030702010501061121130f17071a030c090d06230601050a0302090f03070806090106061b0210030e25150206010e130605040b0106030b04060b0a050f070606030c 73
    0x450150485041111280d1300003103126075508440440903223490b140c19800381e00c5803d0312003241c1d0038440d0852451441c0352201c0256010440500c107250760361200064400d141d41010900e0419555160f074911107150132840f003080590030203024041c40d21800c21107045203640f03203091800b1462280d0070100700a102d4ac40c91039809c0b00c040e00c00c900c15040c580700308003c50ba8400202c4600f14414200161980002000b00b0490380b2500320941d0144581c03000803c0c1180005040351040306204000d010b842d07165001100c482400010201070410140318490061030400d11751200640d05103000a0080c0e22a8040e610300320502c4800409141e2009685c4100c844d0381e103226000d8142910814100e030320f20709000b55a22014450795001c0244c207000710b201200d2040c18080d402c5d81000c13003401741c2d04040c20300100b0f4034801c1c45150082071a2003450016801d00d806600d08a40000700c01134206883c0480680306940400d5420742958000c000c000000b9446105840c00346000c0c6000a07401c90070174820 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 997134802 1250 997133552 997133561
    0x1f0902040b0d02060a0f1b030314010902130b0c011808041412060103260f0d0b10090b0a0905062a03040e01060f2a02040c030b060d02030606041a03070201 68
    0x390007140c540c81c10b003001da00c482e022100c9040340307443c1000c00101d000004072001d840d844806105c0103420605c000034168160002c005001c1400301060842e680c400d0f03044101e120f10311803d10403060140e41004550000005403050148040010442a02c4046003603118013510504950030000841e0a00410300704404440b814202030315070320031081d800c5034801c1c0c1c3c1c3c02051000805214400790500c1e4510043c0e20500c1c0e4001ca5111101d4440109802e003100c00c1c5c20911864003558603000840c0103e10b062040864021216202c960403a410003a02c988240e02135005030062042c00e0800003410b07103030b550042840700417815540112102c25941000103075042e034514245c50303109000502809421355141411503201c2d0070704000361044000d06803000c5e0714400c00742614164040b02c0b401c0128010340c1c03042a0f035100b1502000006002c21042d01100c01c41d00c0a17681065003441041c1c8034034080e500440d00006e0042255041c13a55404a4002100c220002c5244c2080040140069103409014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 997136052 1250 997134802 997134821
    0x603070e330a120c0507021008040302011406060a2318090c070209010b0d0b04061e0824040f06021606050c03042406050306091f0204050907111f090204 67
    0x4581d00e42440b002d8010322001088880310301480e81ea400c0345003a60300a074126107500e0f07400f5001c10861403070010082d0040c0c034210341c186c0c055402d04440040c1d840121803003910400c00201460f0501c0711007141120704600d501c00a07a0400510b084c1c02031803000c0d50024051584842e14448180b112034014072240c16406003641200384014400341005a9409010a0544203042046501c51003c1c02d40d2402038101100340380d030081c1c9010004100c5900c19042c0310146a001c50700b111003c3c3d50780304520740d5600354404203140d500126905c800201d09900d8259041800303032408018010003074a840703040703a00c4030107243c9540214113030301800c01105004141d030140b1150314007030841c13601e80c503045440c40a401604101000b00c1144444c040d00b258400c002610001e012102d882c40c003030f02600d0340c5041c4841061094100c0c4d9a00d4000c02603036000729010b541000e4000301c8a516204020349401721415401c0340180100c42d0000d62001c81805201c040c000000400f080e110818014807048951041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 997137302 1250 997136052 997136149
    0x120f01061716170a1a090c1f23041e08070303170601180b0c1005060f0105030405211e030717060415180507110a020603070e 55
    0x40305a041000c0e402d4200210740f401d41034600340c42c01d0480030300c0c109102080000c0c2020003400c032002806088084680c403030450001103030740d1100200208040c01005d280340c0b10350300400f011a811058071904440e4000c02042c041b00701500310700084042d0a40054204080007281a04000e0b408020a00611300810100d0042e004450070f541b0003c00f05404038620140500e8982c0100340c60380d109268106100002c0d13001d001109466200180c9143d211740401141407058103582c5c54011349600c1418000c44008180a0042c0c40080041d541d03908024801d60300c81c0601c3c0c0303075502080c4840c402566107840040d0361603645d00c81076401c8000c0c00c50321010342038000f106100f000309680e008000c2d400c0d070503100090306000d6520b103400074004c0d007403c41601c03000b1039466000250300d90324156400da040500c2901404281d4030540e0498190500300042141c542c13000c5400009802d10707000541c0c01c0300192400c0702c10607034040003088002e0301c1c01c0e81c0070458415151041910741200d03070005840440d102c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 997138552 1250 997137302 997137313
    0x90b0c0a091505030705030c09060703020f100b1309020f100309020a0f06120e0c0613030b252d18142809151502030301030b0403080402120f010617 65
    0x40c1c0c0000e000740002130111080c13180020224507023500701000d442501d20010800c80d500c921514009440350807204441d10a441840e088860f84006406000c0040384046c00e4640000906406c0f80701404450406a8110042903134071140b80e2924401c09071ba6003000d880101c1c2c615410f2040c0422007405601c45245040c2c0043c05100481c4c0c0b00031400b522241c242000702c0d00348503208140303043c1040007190952014000500040c000b049501d910110385c0200c100c482075a0b0782400300054400f001c296000c3d075441da651405180e50181c0c078802c002072a00b03460030003242403841d08040f2190441c4102c00101e848604c0c0c5002c001250b603800c1c000340101c00c6d14001a24003000120b0003030501260030480c0169080d4800361a039080186071801043d03808000c3c08012174040340b00001312024010305128a003032320744e080e203c2e80c00002280c1c101ca81c010103210b81a07945840484d26400b01420490f0310100149980682c03440400c151003030030445400000300607240051509504925010290b03140c0c000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 997139802 1250 997138552 997138589
    0x6080606071101170a1a04060602071206060b0a080f0603010b03120703030f02040b030402010f020d02031b0c04360c171c170106170604020d090b0c0a09 67
    0x8000c1540c80c100c1d070050382d4221901d440c00044e01c0700e00f59012211504400f10040108010081e04841c0c6520201e02d0340c417100721364140c1400700351501d0307010f40809a8000301017004075004010704843c0c4c95018120010b09c082d110007a450f03881e0b200406070000580f03140c1c144066000102205504540210020000300d1607103c04203407181404c12000c2491400494404180741c085c0c0c2002880c0c503080303d400c6540b1600c84040c401c60350000d07601030b400100444281d5034002d000040004512a20390002d5040c4071030302d4141071400c26400500701890007050a102c6050321103004001c48004840a400540c8011002d144595590400b01c0c0d00394140120001d4041a4100180d04c107a40d40d141d81d40d4035801c1c000da00d09103424080205115040d0000e8041c07000786a00c100043c4503c00299000c034420303681c40008035100140648003956445070040072030382501d031580c000e0511041c11038000c01c40c4489519900f070388640490394800a84070000b200710000c1d6000906c0e0b00074141440304064413040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 997141052 1250 997139802 997139809
    0x6051c050607050309030903060a0c1b05030d0f11120106180f051309140c01120b0f131b0504030b070f050f070f0f030f020106140d0f02040b06070807050601060806 72
    0x2000b60200b000d2100001c00315104074001d10464440e0031015048440c13a0070320480b454000d0450321a200d000400c3c0000340424032070b00050480c4542c0d04400213608200d00b441711403000300483c83c4186841c50b070f5080c00101006000c1e024204880b019460305003598948203015181143e0540b05110741942c18100b03104c41c4a16000b03500c00d903103082d07811031030044507103100d50000d04c00b82c0c1024040a900303007a0340384012000540f06400c4c030401e0740d400300f041460303414050649001c1d1001300c0c2d121140d02c0040c001f604055040107000f411b1064080340c40d026200305c00511614a41c1d5000008400003428000c6c03000b070b005415003003005490900e9840340c03a16001081c90040c07060805000f4030014001050040c1e2050100103203803c42c5450b000248a07140c0601642c046e422003c004d1350030550000b81200f00c20b1a01c80306810040d00165102c0300399641d0001340a48000308a900a87d6410f02c0345071910b9007030217808003c1c0305130461507a90101d410300714a0f052059111108200080e0b00f00980e07500d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 997142302 1250 997141052 997141063
    0xd12091a120a0908280207060f050a18090605040e0c030604021e030d051803060405120f160c080f0303070c021c050a0302031809040c15020304080a0606051c05 70
    0x28221407064285869654094000c1c04854030044c064400120320340070380e1080c508035440c00400d040b0006036052100a03050fa261034591040d040802c10740b404290800c0d00800c0101f44238042031134070700c03052a13004001800007480740c0c00c00c008459075101c00388000e08040c45800c1d82c00b00c0c43c01c003c0512500940020707507a044000c0000f401007100c0c80340c0c03d0382d510047c20407502c0040000d041c0e0b1044403c01c80b00500c40e0b005480c22100491946041c002242408a40c00f070003290481c000d131450079500000c886565200d000344481d85a401c21818260303240040c40710b04000c2c0715400c954041da2408403034506e05882c003401100303107410030003e000364641c128440310b02140e030503610743c01102c1407d04204901503012401030f00034094884200d042550200003080351200b400f100000b0b90b00e66200b44903d014084074010300758088010280710031140c6560b0440035482600c100c03840c06440305603103410103c5000c0201c895540f2140240300503d07201d0184001003a00e0411003041d410a07454555039a03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 997143552 1250 997142302 997142317
    0x7030c052d010e03070f120c05060c0a02040b010e0a03050a26031f080a1b0602010605060d15080f061005010e012102041d091c08010303030b030a020d12091a 69
    0x10400d0252000c3c5600c060211400030401c140b000308010741d8031446503070802c0290b1002c43d003000d20302c000072a00d858000c0550724a40c01c50001810747c59100d43c240001030050079046414000000c1804003d5959003072854041c52143d0043c207001c0701640780029040c101d1a080841c0c0d1003168001c2e400480c1c854042da584184003030240290305031a090403c00c048519086922180120306102c4203001a080c200300074002c2c0141c0640005a40344412406c803603140c014240c3c0184108800a603518090b000450032403000004000203035501c075008c0b4a000540c00c1200b8043d0802010490403058442006005040038240140200c480714002418110004a60701103900c09902c0784600300040e0303054801411409003e8090088604400300449808655664261140c1c40401c5600030b00720441c207041c0103041c1c03250300c051390071654290058062500500c0c0c161150306001009a0760783d9000d105020b0240005540300c050302c1030010311181064002803408915250740f500404640c004503902e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 997144802 1250 997143552 997143557
    0x3070605060f0d0308060604150305090c09070f0804053a0806090103030c06110f07050712020901032315060306101a0c01020d020a050c061305120c0a0507030c052d01 73
    0xa40d580c040005513075010b42e8120041004e40070b5040e003d855050707813003640105144cd046070580d400850401440c1d13413003194070400045008810390019801004a25000b52040003540c8100b014521008240c1004001c000396020b00815040b12100210440c68002c080500d02031540b40707844008168000010302c802020050610400028400700b907001034242e4840d51101c0d03a444444858011054004860588680c018040300007030300c016142555480d168082c1400102d03030303c3d5480301002124000720005010030307200c07050304601405100b00b4181450f90140a013003801c03d4014140391100c0205002c8001801f504244140c00465000000140303c103002e0603516130030180300c02d0190094082480707007a0f00119030b0b50401030f0030101a007800c006800c11a030803551041480c402c2911075080c098000d80044c19100c05030740b40c040041014055803401c44071400c00d241d850620b02a0641d03c191003e9044110901140c50100b00003402607c02908202c18145500782100c601401544400e05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 997146052 1250 997144802 997144817
    0x20307030f050a2027010b28050417060702100e190c0e0903280c08071406150117280501090b0a060806131d03070605060f0d03 56
    0x800c4000c1003c2500c50340c4c003c0c403502030340011400202040d5210701089100381c3c00032101c00115a8019490048840c100d502420740313900c0c040458130315901c090301104852440000d500904c2000c0c0030200c100c061540e0321b240d46d075441c105050f8904101e03214480c1c2e1941150b41400b903140e0707000540510b02c400c013000c00149825444541e40c60310715a4958000d42c20359015601307042c40304c40f0442d0b00803245141d00000d400c1c0d49200200342c480c0300d044000c82c4440c842c1032140e4880c41800340c00e12054151400d0580c007140140e1104184da4010303590845500c01d9014100141c034a00b800065082001190b40391920146030300040d05445c80e56456294001450000514401c0300f6040032842000409034414201d65541c000d5005e0202402010011414000301c4185820500e2048048a0300c43d030307455009858040400541c40c404814114106884000728144991629180802a840c1c4001503655440c1850854248c400042c0028400c030b9003481011150b855001085030f006600d132600c0c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 997147302 1250 997146052 997146083
    0x61305210706151a1216020a030c03030605040f09060608071815090c0f020d0c210c08040609030b0f13141002030109060e0f0114010e010e1c0c0b040302030703 70
    0x100b04441940092012160b0001410384040200000d11440c0017441101106950301000d01402980c001207240041c1e0000c401c24000c60b1080e50108031080c807a00d0701140380303607842380058140d807224080d43d9072450fa12040841003003500d2240300004e02c2c40c603000d4030306c2a1520711800200c1c0c3e03001290f902415100c82c8a04481c0d0b031030790074100103840f01803400c000d42c031601d1000400c8140c4204281c009403180704042e42c1000d0040554042c42c503407001c00d0701a140c0990100d01148030080d050b840606c201c400d02d440000340240050005002c0ea6a01c0b182207d02c0c0d070401e00b00e803400107002003090460302020b110035102c02c003911041c4241c200d042c0901094116040e81d141942c880c1c04004101c4c030101c004540c002054002a00303c0d2901c008000b02600c41b07082204010a082c801c9018990f0b448c84074504550240740c002b280054141490300403088114045282c0c01c0d0000e503041d9425410320b12800403c010201504050304070469510f00309400c41d030103e50340c1e00761400064040d610028144 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 997148552 1250 997147302 997147331
    0x41b020607110c0303070c05090c040b03060607020d05070303021c051305040903300f050708370606022404060203101d060906040c0206040f080c061305210706 70
    0xb01c00e43c000140c212556401e1906048410380414000d451040c000365012500c5a055003040e2400d0b030354002000d602c0c42d15210204640343c2e01819040740c0140c1c0103c694030101d60140666001580641c0140c1204042002c030b680e040003801e8902818001d00b40214202e440300c0a103048180e920aa50008600075581401d84e0141c0c3c0c1c01d101c0c0001d00004000d010502c100015081c281d5500746030090105881d1100c0c0e5005480040f41d09a0005d0b0f00500022201040001307207564810700030780b140d0080f8000144031901c990004007000c0c101515000108007a030741c100500c040301e00d1103081440284142d144d40b0a00c680000d00041c0001313402002142442003104e031040c00030401324000c0b6018281104410026480860311a8400c0043c0c400041440c1460b002d0341075002041e40c0070b0300d003681d1182d0b82d5030408641d04000f0b40e018202031040c0120b425040001ca4041c1c529041d290280e03060520b01503140c9400c4c0020020000321019010f241c586068081d184110707417200010958003101c5180c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 997149802 1250 997148552 997148563
    0x3051e0708060a020403060b01030525050f0a0309050606190e070917010e07050114040b0d0b032d030a0f0e0f060f07060608070302030705010c050c10080105041b02060711 75
    0x103251103010b21402e22600b0701e41d66000300100c0744510001d12000191500650407110102c84a9114140d240022058800c281d406002411a070303090040c20109108a40e918070340200d103400001c2035403000d8440512a0800c03101d58420001c46900034031410311015076031020f03600d2041c01072000c000c00128603007a001d034040b48050503103200000200c5c5481080365019010315211f41503a4050000003082c294420720000050250403d0818601440c0c10b00c803202d1503012015204140e0f80d030f4a0f500000e03940a10640c2103012101c0c5103c8890307a41380186020050600c2d80e015102d5204000801c6503d0300f0a004078102c0c1c40c00e05101d2000c43c00c02c1c01141c020f034020305440f9808903000079984070f20304248015080c5a401083c081001c00d4990700070903640c0c00d607400301a40c941d10800c0200101d602c130ba10506e160354411020b41360002502800319405a2a01e42c0010101e82c1c168010301143c100351082441c6007500b800c5c409000384074014003944441000d011034081114060840394000c504000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 997151052 1250 997149802 997149809
    0x1d040c050612040b060a0302030d1214090102120a0225050a0506040516120807110604240f03141b070b13060605010f0e27040b07030c030603051e07 65
    0x803955400e02c0c5400c0c5856960200d400721803000764500400c980d810144425030030380780c0c050003c04046500c04000d94400300d448115090503501e4810408481c1d125003801c1d8020780d0003800141c0c0360440c02a498000090080110440c60300c103001e00d03402c010084458840c850f40c40c50003101104c1090030443d090120468014041d48203441c1070004110340040c5592a54074010409800c041d20b0f40340c8104a40009000a000110b0502c0304002080d400320380e012042c4401840203103000d0b51070085600e00051030840c9142040030321100b03950780d038020f0250411aa1a40750802081d8141d03441c40d606507401400e60111118018007000210b490359044032142a08500d40c5a854a070201d0704200d1015200d200700c9480e0300780080000d455008403220404082c80d500c600c05000680400e210900401042c060030340c1c81b0310140c000f200c0d200701c0d080c607028900030649204281380190002d015208002680004c047ca00300d002c0021402c0401c001169101c00c11100303401c451b00c094100e01e005803d40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 997152302 1250 997151052 997151059
    0x10081f0b190504091a0702161d0f070203070f0302010209030c060301050d06050702030c0714030705010903030210050c130902030402011d210102091903060507051306052209060806010e011d040c05 86
    0x1400101600041c800392500c6a030120400d180303840701003200390b4109278080c08048440b20000b05e102c0101200c1102c1c1d1280f002d104890904105460b001303032422107240305402603540000c40e100396082c00e1241c060708d55800c0c0e88440c174651411300400c2c1100b151480103044165a503000c40c003821b00c00c1c41121085140c00c030840d80d8042d280c60f0090465101c08550740c1c8a0b110f0003c1c000f4413540030700356850459800d9005442c60401424807000940401071000d00c48510402981207400031440e015009407200e01001600e900d450300c000740c83e4507090340c40c200154004540c01d00150b80c0f00301d210140110000c81c0754500045626040b406406000c000c682e01000d200c0c2c0b0021042511500a01220f000d2031341844941c40d01d9000761203622940d18100142481c05406002160040004103000c80b4107510010710880040249030441c005034000145d000d4540381e080005c8041000390303030f014018142505050703501d0200702025010480400c0040100e91000040a01401288a00040c280079 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 997153552 1250 997152302 997152353
    0xa0906020c030a030e010e031e0706050708010806060a03050d030b061b061f0e041211100e070807050607141504051606030506150310081f0b19050409 66
    0xa01c4015140e0308185401d000181c81c181c1d052aa14805014448100e1032241c05903241684110346501c4400648040d0002c0b10400c001e00d20001d0704511480744680d8042c1e40c1d1001650400d0750807801d0640207010644682402041800407030804100d41003400d4440c1400034a10b8135202c040340942c0212111400103090b1709800101c0c021003c0f400610400c4d107070f4240c109400b4117902c4081030440b80e000b0001402801c20001d800140780d4150000000c9050402e01438405584103000c2c50041a40751008007a41c42d0719a02880c40001c05c081405462084080c2c12a80e04020216202e40a040c0000c0c0184102c5240721901040c20302012108110540c0803060500e00380c108140c0e070310000340b150007880d440c41e000003984a20034415a4042d0300010407602c0c41d2110410700c0403440e04080d001600700c100349000044ca0000801c600002ca00403040c02040b0841104000c80c100d550005085005c0e044520401110f051109940016518111400281503859003048400c4035803104030781034030f10700c1c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 997154802 1250 997153552 997153567
    0x109050102030f01060804080a0509010e0415050a050d110d020609030a05071d071d120706120f05070c120c0b04150e01020c0c0105071a070f08060d02010e06030a090602 74
    0x40d001144103060f075660809282c1d9030360800306e0f44031204480117441800148412600741d481039004001c80001450410b601302c0d41d0340001030441c2c4c05074030750321450141810304100c01c7c01e04001080c0288801c490480300034520317848010940c0400b1254500c038030b4090900030215601e0748182d030061031001d03086503c80c0c401031a0031a560b480d41d005100d07009910b038031241c070702c1c0100c03d0707095110751601c0d95511641082181509c041c055a0251b10b50700800e00043d441c40f1107801c0107a14018031075035079a000c9202500b404101281c44440c000780c4040c0c01c020400c4119070704200c400c0c4005600404541e0000682c801c2140c2d2800c2c3e018006181d1200700041c441070100500b03545003d519450000c02c440458034011070308034441d5100b440740076045015812410b42c0204d018040c0300f0701618000801a0804441c00b83d09407040390001c01103514500c1032001030341d20244496000074281c804007000400c64002808160300036900510034100000013900700021a00103007200c5501080654032820f6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 997156052 1250 997154802 997154813
    0xa050304030b091006060e0609011e031413020d1e0c06210507120b06090a15110105100302060a0e090108010f0c050f0912150408090a060f17090f0109 66
    0xb030a850703002a81c401d4041039084e8904600c210800c944494442d021380309800c10900c0010380000c044035046c40010b554041401d007000c40b030107808041039640054500c01e640328251884c24090b1109940c0480342c0801001a2203540310860301a4000c1c9105490240078110a040810001801080f503904070100050745034005545c1d6000a00d800428a07c041c054000c520440f08101c0d030810015024003040ca0306819130703500c02460746801805142c9003032012030114512103d140d02a503c8482610031040c1035561200317010202c24052030017030120b814400000d0541404d0f41c040607109000c0003449a01381c600601650394103030006407082544c0d40c0e58480d00c9000f840700007582d00b000d0f810f098400c1c0109200780100e03150405001069420310346414280a4000104981c9003c0351090f007101030894802e0604280c4643e21510510355104c0b110010b01000310f2980d4821000d1084c0c090500820a40141d180d00c4001c2c0111080c01c1e103950313060192454100c42c0031601c0899440c00036820240b10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 997157302 1250 997156052 997156073
    0x51204031a09010504050c19030b0906061c030c03032c0618030f1602030a0f0809040b0906060306010f0e1201020d0506010f0c08070f0b16122c0a05030403 68
    0xa03101d0740300210b640c0d41c5003400c0c03c1c1c48046400406c00e030840d5070520054544491100510825001500032068580c2c3e10f400e00300c4410b07030b040505940325004128031860b02c95548806100c04039091003c038207140d5009808021070240007000c2c16140c00c60b00101101407240241415030800c51144058811511345858a01c15600e40c06030f1a0071500000007114004101c4004403d410b03640c524100901040480c9060280e02c01c0740e040c0034001c240e10100e80c00d4150210f106025080d0a561101d0070800c1200315035a9503003060280c0c03c12810070038582d0711042901d0741300c0428204070504188015003120035181c0519042e61201c1c07002c810b20100601580544441004214104000e441c0c20b4015220380ea080000a00083d58a8940b900007603503100203080f095100745c1040680c242d03d55141c0324003010803900040e8031140b0300725650055074458600c0d03401c10741d8000204031074000c261800b444000d01403c08013102160300808a480f07442000845201500306007503940b110307100d19000c11301740c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 997158552 1250 997157302 997157333
    0x12040911160b0f0601050a090b1303060e25140909010f0501080a021305091207030e090c0903010c1418032107051608030d050c1902010203010513151205120403 70
    0x2c3c1c6190b00058055001d1405c40c0e65461031754880e1200c1034588840f6211030383c440d854202c0150b80d904000400103015000d0203144068200180100346040461580c1400451442c40014980d112041000040c11122101c10000940303021269951300300d15240504640f0404400213171a0200000380f551f000304003042d01030700c00c6518181021440d40c02201355102980d80302419000ba2185c0c2150103050001060300901c80d041c05007028028400040a0b40d101b01c0e004507140c10001003070700032482c0030311440d031081115007442c0c144605000a174a00c1401007140058049841b443c00b001d40c0d40d01006400603404109808a040340d81000c41001c881d0024401182c00b03128000340402c01950f00a0070382d09a415002c021402c0c900d1044104016241c050300d100c03803030341042140c5a500502060100e0990030760707030005a070b2941760a003401554044280c1002000346082000301c00d42c444030003c00c04640c80604103110b1062a41086c2d8240209080b00b0b118004000800008100300d0b0316420004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 997159802 1250 997158552 997158571
    0xa03080105150c07090c230706052824090b090c03040302100506011704030c0312090804090b010201151707061115100512010f05070212040911160b 65
    0x18580d04868100d01d4042c114a6528503081603205000e170519540c81504c01e18501c0c60105000351205030303050307005005410320f030b100c0e00400104541404624000c0b50380003801c036036503100c08034080458001001c0d42100711455103900c5040c00b030021244600800c5025000300e0080035129540c1701d00c0130050551210b11801001080f000078280001d590a492003140c0503006055401e4618103200028a0b00030010360500c061901e240c01e0100000c40070038401d40c442d484100c505843c41c1000782076503000314000c0d41da250602c60914009121001075030201d8049004c00b0650f081c6160050b03001d4405519042804010a20001013a0f0300441004030781c03101f42d006032070a0303a4480d501110381400d491036480003a48071488280c0d4a030110209107a0010414000c40300b1542c0f10300020b22043c442003800300c0143e4640080d03002c41903035882902d810290361f00080c40200c541030f5401e0729500a40c070440985640c0ea03d40402c101140380c00310386c0415080c0d064005480901c6c6002c040da4881968080c1d031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 997161052 1250 997159802 997159819
    0xd0210030f1517070f1205120c03030a140603030a120b1f030c020303060a1e0816030506010f030308160302040b0a0c033207050c06130e0c040f15110a03080105 70
    0x45120120b180740559940b00e80085440b8108100700146c01d03000c50040b2607921555425030841c00810018050310603118000e950340341000c0003c00152031050b8100d500035150703003082c00303443d66001044440c620b01a00b41500054082003115000302081e03034400e40c1008224072614a07a01c0403000c103d00d5040140c50410503a40c210030103e950380030032180981c000704252000d10028070a40404100c086401010701042501c5808076030800d180700e0341102c112070b4080c07010700401c403003408164054280d4442801c4a01d24607100100203038005001d075041000048222800e80344644c04580151007004103042da00c42031000c00901003008404150002382124820a255040c00404c1402610b041e58805540000d800402110b0b035200050803100d51081c01255000c0d074840038007418840304020328040c0e0391460b00310040110703840201858070034102080309100080f51a8504000d0701d11001280202800c1b10b1400d568001d40705611b10711074400c014a90303040507848103059040e01c0043d1456074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 997162302 1250 997161052 997161089
    0x5071203020a09092f1b0a05030919030b0708010f06021b060a20073303111b06061003020f03040f061404060902040c0503060d0210030f15 61
    0x5089004010b115400141040c03030403c043c0034144c11506880c0c0a1045810b29007111400d01d21a19818019200041070042546a00120340c404600d6400661402404507a1794a56810b80c803442611302691145159082c50a0314500840c40704001d03681c4200c403400c150a00752009408150244a8945000d000d040c0c04650f11f4404594040d4100511001d54040102e0a00300061038001d003110504101c4903000920410340a4289030760070f101030201924403d41091a1300348900a941d1504d040f0500308034104101e021803240301140130340701e49400110901c220f8403e40d06441210194480030040c0440100d0202001c90014000c0c00b044403940c078010449603095050340207001180c0e01d04a011f00020340442c0945000c08110ba210300c600050a60403001d20400004d8241c03001d48a4550b250300c00c00c114103261060138180703130090405a00307615002c00007828104c20300c00c2c000d015685c0c01a8400c40d03107000b60000301003050342c00000e0203040d01c00701100f02c8008051140894000d10b5803c2e10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 997163552 1250 997162302 997162307
    0x50a11040b031905010209060a0905030f01090c030f0f080304151505030304031401020d09050d0f1728050a0c0206060d03050a0c0809030106260d020c010e0303070501050403050712 79
    0x30740c0310a000d400390501c0c1d1982c9001c0c84410249110544495400300440112540d41c0401003d86a0151300d802c100c0508120505240100c40310341c2d0320b03250b0708d0941c00002040c401c2440ca003c0300d502103114901c00c1818908403ca800042d140285411004014030081000100c845009120740d0340d000c218151042681c004080c202d40b01d1240c154101300802e00c0442c00801014000300e000c0c60000d8074100f2100c019000311101c041c415241d40c0c005085800b00a035211900e182040524605000d0b42e0300c00c0080185540307000f0340320000c1d054030180c508048030303069082221459080d1004000e0b614200311041c0150055241c402c005001e100c0c0024001e00d0300d072078a0400c0310740542d507040c280130088000303130381c543c406e02c0042e00d205805008510040c0e03424040d10026007401c05004000c60851038058042c0c07000004108a95004400c0812443e540022941c00001003403904030005040744d004241148900038001e081035091608004c24190000028000c840c41900c07200040c071302c01c400c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 997164802 1250 997163552 997163561
    0xf1a190e0c0304052e150305060901050103031101051b0d0f0905030a0e0402211003140c0405090c030a02060a090b040e07170f2a1201061116030f0f020607050a1104 72
    0x1c1c0b412811248071017502d00004d65001d140d000240000c84d268143d1203480796840d0440c100c405500710303911100180101644154252040412900240a5400c1103105402001c2204000c1003505030041100c032008079081d00040d04d50803032940204500441030505e070f5200c0d030160b1141404134000b8000916681410f2080360307a00412401c40d40024510845030750180803000d0702c001481810b40307002001144114842c50107a040780e03002848480030710004d0200b03030740c401000c1180c590804106402d207524003094483e0b40700e9044406560340c0b461101d056581007556040700c0700c0000701080128030f10000098841c0241d550b40c660400804109c1244590f0410807030700c0501d2500004003044141d9502e01074102c144101802e0505a000e03103d80c1c884d4103402908000320881d8088004110b603540007040740080007100c0014140e00450509403103c0140720340f20003003c070f0706940180c41c148080b440404000342e034000e04040d59014107081c4140e55022041054515145804c039042c01840d20348103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 997166052 1250 997164802 997164853
    0x1a03070e01030b0403020304150f0f050712080604060906060306050307051c030305130b090d0f02010c0914041b020a0606090b01090b0306031e100f1a190e0c030405 72
    0x4114480d07038255501d0401404010304201d0561100b4000800c10340000c0440b081040a01d42e9040000110548014009880700c0c10840601c00d0422110012030094a01d083c50003200e42010806501c40e1004580148419400100041d141c0700740400c07419416004081260400ca044031400c079110020000c00c0112003140d07102c03100f0b202c1003120000740a6000203902460040315054498015190565103070f001b21103005190f08042140c491803600050b46942c00b208900c02000b00d01d003407190191445810b401100c10322400700e030342c24490355a40d070084107120050841240180969250281d55446041b0045425608090010406c51132522982c8056407050f075402ca0004d180c0078210b081988094410354040c001d02194040340003509059082502841d0001c1c5440c00f0b0910151045406d480803401016040000c0d1a0841521904c1314164078412125004c41703510503007030500491415441480d64410420070804100740c030402130740c0719502a100b5210307a00c150600301414506800c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 997167302 1250 997166052 997166069
    0x315092307171b0123031015080709122a080609150f0a0b030604080d0b0102061302060a09080f07031211060109020d0b0a0902070501061211131d011a0307 68
    0x12070002e081d841303255001c40040c42d17811918404c1c9040f6076403120980c41101d0260444500a20402c40f400510030780d811066100d05c0d03d440d45081c90300004120099034801e035034201011200c0481030000c4981d8010140312003400360710820f945560b0412125845200d030300c01a01030000000d00e08040499a0308210300d809070030b540c1c40e5407101010000c1c03050290035158003c0d0340700c10010a58800f084081d0249011f01d0083d601c4040d855000416078070640c14843c1103410000a1190918000020214160b4100d68480d16625100c201311011441a80400020320402e482c40c030307200c6030100d2400c0581c1e00802502081140204c410340d1003c8001c904401c0f9640a9801044004030503809407400b85102c120114903040240c0c0000d03000030300ca802903608030b0340c00140e241c1004801d11402008160000c4284038074184d41e03d4420005000c20007041c0030b09041ca00007014200280c1c441e014041d00d216101c01060481201c00e4002d200c44020341c0744c0140340003103114131460001414421100d00c1d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 997168552 1250 997167302 997167343
    0x115180e0a0b10111902060f0d140f01030309060503041a1b0c150901050702060c0a02010b0411071a0603101808042c01031509230717 59
    0x501800603594000704490000d03a990034a0303289940d82c100e16484221201e91340d50100304030304500d01d400c200c000c02d5200c0b40c10515000300780068942c2c0e825070389044201c102103a10b40544611020242400b59490070b0001c03840c0c3c0405c0202003401d00c210b4180c1f80a030741c5141100362680300550382032200f40c60140c066401d03801b21455041112820341e0b800a0007000700325282c810300b00c051001750001452441140c104000300300c807030305072102940d610516881c020301c06800d07c207030f0194030307a00c01074541c0c00521000545041500d0003500403101024014004020b400200706100703a2507001482c0c100e03000d0400640c54028404400c00d95030090b14010013802016030821645401010a500c43e103c000366903401d540b0100314000003500c000c158610304030000c1c551540440d019480c920387c001c4824440ba40050004c81e04024141c8180108103400041651031420700100c140c1100f0091410002903841004c0e90090100301c55003129000e03440c201c1b034208040f544036225002050101c0020614 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 997169802 1250 997168552 997168559
    0x111030a0b0a090606030e0105060d03140a0c0c0e0103020f010f02120c0703080a020319140f0c010e0604061b0207050f060a140f2503080406020906040b030906011518 73
    0x35a00100a80100811080a5580d1140c8440c203950071030340102d02003540c0e0181b200034000c00307000f07859001500322042d45038441107503000382c98000c60504198201c01d000c14100c0d6814001d250f290700042e0032008000e019036890603100c40846090004901a00da80404112039500030a05411000b8540c0c000e44410710300c0d0f1034280e084e500102e0081382c0f58441e0920001c080f5032038400500c4451072680c05142d0316240050803040211f20301c0408010045401a6420451116000c0e200c415007121b40c080d0740e500c0100b20107405000c41000790714090044030184802c001d00380e4000301501c8100386003c0e90303400c24900241c0c0c40f8401c0d40308094000e54102d401600302c0c134003000209040300795410035109801107030142d1003081c4c0041e02e140703050074070004890f10f0b4800b0030703280c2020b4491480010205858aa60b00030010a005000180540d070041071429803a503e900c15503001c2c101e10100b080c0c90b442c0100900f82d89540030300c80c640030501c242040c421002e2043d4101c0180700700c1c2c204c8103090b1914 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 997171052 1250 997169802 997169821
    0x1031e1212091e1731090509011e0209180601021612150c0e0f1f031a01030c020d0f1e050304060e0c010909020705030f040803040305010608011103 65
    0x984a45101d480d41c1c0e0759140c640052034a95912003003001003002410070740150325010390803c05070303164201d14601c03d00c00c2c02c03500d041d9007450790b0030901c0c80500c19072405080070701114140069004082c1c5035080c2001c000075641c05600208580e510188040780c58a103003084501240701742341c04180c020000b41c160a55940000c684990802030600c1202c010301d002c880c082105008035001802000c41e50196601845441041d51818903041c000811861444400c080c03c40304442003907030300907890150b6007042a40c54000981143c3c886505241d0742a000420050090011009403050700030000c01016855100f0301c540385010b0300540050042c0441ca581c00c0d94140001c03401b40341088440d41c28030300d0b10781079880021f08041007030321007603180d050a1401200703032a803040110b42141d1061003940002d0380c0c8165810b080b07440d0564016540c4400b401c01034114440c0c03541c00b001040300040e0004140c20000001c0003228001c6008000160301c6603900d500b61402d5907402c8e0391070380c81030012481451 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 997172302 1250 997171052 997171067
    0x1103062103040303210501031505070302032203030e12090103060e01051c0f05120325050d090c05040504120206011a09061c09050c18160509060f0d0501031e12 70
    0x3500102843c88983c410f417529804d46400f41c1007181c520711031404000344001c02c0d01401d0b13003052150900b9421071808540000080328990300315a01e4005802481e020325010341e00a89044104001f074900e42c1b00c0ca42d0846840341d100d8039220780000d03e40341000030941600030040d030607980000c204010442c00244140b9011700c41500550305060b81e40708100c0010010440208151029a03080d44c5a151011410588034640e0300c208103030209160341c040110340d011085400314401100300180000b01c506000b0a2074940c0e40100e500036250505200c10300c075448009249070011f075400c5580036a2100651810074081018001030944140f1007184285409030140a0030320b0700303101d4a1003268015081c00700b51a0110419141600715042047c081e0402e5003524100001084032505175080807810300482501c00c0d8038890400102080b042c0c21643c071f41003101c00c1c011044e052951160340b03a06101d002440e00b84030480300d0b030390029900340c00d0046e2600c0c0040c44036001032030001144441c0c0f00a03202807 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 997173552 1250 997172302 997172327
    0x15040b0c030c210601030501090c08010611071d0406151202012a03030f0506010314040206031f0e07020106050f1e0301150b031501111c121103062103040303 69
    0x103105008000c59a0164004908061120b030f0000d00f0f030b824a00d001404590068000c000c4040c101000708000c2908007004904440043c034101c60740c0d441036641141081d92039000016001540300b51086504103800c6d0300341c000d80c06203034200098041c24a401c140584207201d080c00880c103081803980513600820b10007074410b111690240742064004180c50500c000c030035044010a0780e070b641002c50024603204496222000382030422000c0c0c41c03d05000c4611200402c0203200d071200000081120303110140c0d611000d00880c1d030b00078003180ca5020312078099000321254001036190010002c0c0601c2c120524a19031440070f820208940d00b400200c404010445656a07055900c2d140400b11801d500c0c80540300030200e00360340c0394590034541109180d1044030032000c0d04001d81030504035003c040c049210700c01400228078140c8240d154140c1560b81080994607210b945151491802258140400540c410001118050302618181a03c15070b440481c0c401312406074010300050000034000d00760811079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 997174802 1250 997173552 997173571
    0x90d0b0103020f060c1b032803030606030b0d1106091017070806060d050a110307050a0e2e03140403090e09060f2703070c080d0504120209060f03071715040b0c03 71
    0x8c5100142e1010b001c1401603c00c44a03620455059209066161080c81d02a184516090000c2c1002c1c42c0007070503900001e4005883c0030038a419a80081c3d8419085640d4101d0103481a07a1040f11000301502d007041002036405c00040ca000001e0321036100c6d8286c2e91003807500070905400c10b4071128040d40102030042400300b49694541c0e004c41e10300f1800000d10310980d542d54409a0301d29625500500d0031000b91003060150680194000080b4454608100d500c04002402c075880020090100d0107000c008076420440c09503c000d0106241d446003c48040e24095007000c20f0544540c405181d885408696142c094a5480b01164044650701d00c3c1140d4280d05a08030382c000080c102d0000d0459010940441d14191120703000c004c11f80c82400500100c05e0315081980c03c0034601442c000b0140d044690003449105084000341a83e80e030b0010305588210050104d48030192035003505842003072803100e202c010b8400c9420000a5030b092075003480c4520340c854541da40070b03110821001103682026181c00203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 997176052 1250 997174802 997174813
    0x90e03070b0919050619060e060105071a0c09040c022d0c0310050906090706140901030617070f050f0a0905270c0103050a0903080f06010302090d0b0103020f060c1b03 73
    0x40f84500000105018044c0c2c0160655040c90007030030034610312014204240d203003414400c100a1102c00d140303030703440002820196a101400c0c40c240082e400f400c5c82000e1440c40e00c40900c50510319840c00f91880440595041040f40c080e42020b0341d4401900d2801d8201c1c4800b280c81d042620000307a2580940c040180840710300900b0440040d0400041d1415108002d94920030001d100703000700180d07a00080000e01070800103047ca07500400d210b0070702d483e14620860000b240402a4426071000f4000d00c4520310202c0141d0326916070a803038103203500c50000442c0c00c114011403030349407000007168240001490004824a0008031102401004019022100518500c03900c03101070719480000c140c0c001c1000d071401214840001d82284d00152120603a503142100080000340c0080d1180e410141540d5616256641c5c1c60048010784038800e14190018110900c24007040406207d03a410b0742d1084840902d58501d0106100442c0610900089140c0c00241030384800c0d81c800c01d0100400c03201505680 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 997177302 1250 997176052 997176073
    0x70806040b1c230a11040621120203090406090b1905062505150103050708120d021803120705210f21040308040519080307030b1306150801090e03070b09 67
    0x1130030304028083c00c0d10000020780c10005946000d21034940544400352100003803042c011898614100c04040007444121403520514803117008000740c80c41ca80300180280859900c070602d81010b0500700b03203224004c0d048500007058180040c1891820754201500c0182070040d802ca4540e00c041c40c9400e480e0f81e0020800040700800c4041c040100321820004404565516529010703240c5910395020400e01d0300944514240e1801c1c00f000c90380307481803410025072210422007201400c81c42c001c4c80c599141c0b240c41700d40210070640c0c0e00a4480540108140c400c03041c00b007017800c41c1200414804104800e0300700f01520000b0f800c3d03400740015540744a044102c0142a0400150444080d1820380108008c4c004110420200b044544414003440e205542d40b00090b5994030b41500000e0f00403014142c4071902e0748055294048001e01044d5060802d22200342d54048401c0c0103044080040002a0aa0700104040c87e40c2d009a40b0504018801945810304070340303445052502c041c0404246004821160 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 997178552 1250 997177302 997177373
    0xe0d0305090301231608040f02030c190f0608160807050d1401050a1d0402100c151d0708060a020a110f0f1905120c03040e070806040b1c 60
    0x41103130301032028011007400c034030301c1d8004103020090015103801d080b070320b0070444940d0000d00b098216900010180124000d440001d01b04518890040c2d0040c408062858481c03494404a40c211501e80c20003050340780e183c11003103c5940d81101d03500d68a100c041d600c00d010500c6502e11a50201282c5007240c18080014400020388000140712803820840400620880c5042e61581c001011698402b24442802018149540d0b10041020f80710302c403400d907450b20783c42c010585030f94000e5020380039969803904c031405200209446200758914000481b0109408600045d452060b65200030092203580e60300c46004020b5846092031208020228407030082444080000c8141c0320180c0780584520300c3c0c9146000d00d00610691800c62105840f850400030079404900c414010007201c294655500088110514510455200602882d01c4004010740c3c1540920a00c0c01840c0803102441980052001c1194860f5029140154010083d24450009401080e000c104241c8285228485954071058 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 997179802 1250 997178552 997178561
    0x210090b032e0612051009020c07080105010b04083c0c13050606040b030a0b180405150f01090f0b06040f0302010e0604060e06030403030621120f0e0d0305090301 71
    0xe030b4402a5030081507030220000244490781d402c03000381e40481ea24a48a4014507030b5442e00e0060008a0b40c460200304028100f40400340582000c0300d041d582e9034074510b4003a568601c540304211140d46800c001091038505802140e0807644050010300710500c0c001c0c4944150041c60200702c0149411021401d4905a5150000c40000701c0ca00030b404000c03021410701c0300460054820784203262900040150035510801500c083c0d40380d842c00380c0e440382d03543c41800d4010a1b2884680ba80409400c2e06010100301614100341308a03c90401e90345c0e01d06462007940c0b900f990036160031a008107000018042c004d0542d112080c1c0704220a000302d40c1c00501d4005c28010740c4140c2040c09092841c42c024800d6503004184800c042d0b00a0301d035030740b4041c07601600034502002c1e6481c440c0f01e0b000c0000820b040c944030350070500160010f130071400c04006882940302901a00391004548040c0c00800c0c0541c242d005400c01d500850f01398450100c41d19142e002c100000034004c9046060200c01c0c804100070341c070240304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 997181052 1250 997179802 997179811
    0x90902010e190518090d03050415020a18081c17040308041b031b0b04050609011803080a030501090b04050f06010806270631021614161e030210090b03 66
    0x4200306810905e85c907a042c4144403d54005250400080c840001d06180c1c00713460440782804010380b56840c4010450304101850080030318810708807004580210003003856540c1c1e82c105c1c004042c0c205100d84050340c04404948408000c1c00d4200005004030b03000b99210781c1e03c1481054450f446203548000c242205000c1d070001d440c10307120f03405641582026030f0701200c058070045508a040c00d1500c000a80548100b40440381080a501060300c8005034032410746014660150505440b00c1c0758440040050400344036603205182010150345d020f0405100f103074081c0314850b010000c0c543e103000c01511000c4c0c0c046c0c280f640100e12401c20b1200c00180001400d1442000800440903007001c0d000c0010002116600764181c690040f1400e12900341080310144d4407291580160312500401a40e12aa606103240501000c090340c1d550101000302080c1d032580b40c2000361903003000e0342e2584640d031000c01e80c01c020144001d00702c0c3c000307102601d0b01403084c2d120705800d490440101c6071220500c142c03a800984 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 997182302 1250 997181052 997181089
    0x90b01020c190b16050303040f020406052e0203070c090f0606030e0a03030c1e0309111504090c0e0418061a0618040204030f0503070b0c1303030c020f220501090902010e1905 76
    0x1400000b1031800e8001c1338001c3c4401c40e00304054584824000001c0c40c261011030403160303070840c000480b0a0003030003034407051a0454100e0b8155580c400902001e086414113000c0400d14003000400d044d402840f90242000b0f6000007070031680d0035903800340c2c01030128805090900c244042c140820272403111121034140c099507008200d41229182200065920b0304800340b095418042400304442020152422102001c41c0840c1c0042c240303006451030182c103800560480c0c24461104480b80c0c0d00e0b00310490707030340c410701c0300b040f802c0c89407215440580d0f1074010301d80c1d002000b0000d01000240b00903000d404940028801890306581c1e9482c584260600c0604450980001c54041d00384081c0d588056400b4428581651400000319000030780341003140001400d0105c800344043c1992210f03000e400692102a0596441c141047e40c100001040e9080c0304000f40d052000200e82d030041c074025001c695606840da80c0b452451502003180704034a010312105240024000042c0c1a81d40c0f0000010706031180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 997183552 1250 997182302 997182323
    0x2a031503200f030d0206074413020a0b0706021902010b031209100809160902030105100201021201052704030804031b0f021306050a090b01020c190b1605030304 70
    0xc080c000c0b50054124214480c0d000340700400c0340d00360045180c6030f0290b500d03e00f1201c64121070b03514089107a644851500c52100303e19086403101407603030454244894060715100256503001c0c02c056511009140290840f0000804001c0c42c4140009801c590323219170005420036510b1641030b00d181090b0001c1e1070040c0e4403272040c00a182001e108a448c4070205410300e03441d2226010110b84c034000305102100c01c0204500005004e01c2c03091149411130b004000f8010788059030340c00554040e410a014452281c4000c06404030428014401c849609160fa00d03460850f03031900c010004100da488001103102c91030021030311501c0c0002c15240d40303d203109132a0980c1609050800512600300b03e10291100c007034011851001ca4280d100c250b00070340c2d044650302030145426032920050820350788525002030b28440c0c0400c840e00c854100c00c448400a0707085034180380140f410448500802140441840c614510501600540c900104092032240b40c030110012a00e5640c0ba00c0c6030f000f12004c2ea40103808 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 997184802 1250 997183552 997183613
    0xa0809013011030c03040b280e10020a09090e21040906050a08152a03061206070c06090204110a0e04060801020a020d05251202012a031503 61
    0x107a108042d0211418020103065281040c80ea07007451001030800b86c4040c1d04071001443d640e40130054405043c040040244e600c1d402c86c420720340500342c3c40b20f80503510b008100d08400301141e64800c1c2c50031210302d5a12120150302c0c100c9005c0c02800d6480300418107000d50000c12b07800705100141c0321800641c51040d04c1e0303100d2038210884102d40341c503000702d4841c031400c040c00c000301100021b44481440c2143e0b420380381d54554880d0004400500c010307101203d11020030041a0010000c0594440d5a054440060011901010b251a0803040310381ca404605c88030342d6903000c2101ca0380710300c18441c4040c000041902c0c0144030741c00ca0381c21110b420387c0014045101c038056410103000710801040b288000750f040000d094030203910f4a4400310500708001000c51046041600b400c80d9015062800410103043c454905005001440314080c64015600b480503980d510351089071100c0108407540300c4a0254001e030007084002d0140c0c035a00080c0014202c1000c00842c20410001c0b00c090348180288141680 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 997186052 1250 997184802 997184897
    0x20420040b040618060522170304170705150c070305010501090618090b150609060a11150103121409030d031e05150918190303050f06030a080901 64
    0x40b852042e4413030b600d4440c000c004494000e002e4820303911842c2541c603e000c80640c10840e40018035448400c0210860324204da481401000034000c0d510b9900c8086507007194452455038910300c0740705a41d0400008111080c407195480041c01c1da08000d5070076601065602c1d143d250a440e020b030003c400c1c2c40d43d141002c0200c4503880004c1c032240031441c1d01c18403886026854401f039501d4024a100c510030218944440b0542d1808200c0710036140040c04140c841c141c0c000e004122401480c44482e441c032400d03001480c64107030450306a0480354000c101d04511540f100d4200d5402c2d119105602004009005c0d1400d2507405100c201a000080e94001401ea6046107070510008030104050b40060710300400d11000d9900c02d503550900b00b1003520403455a880b01054040c2040032209440300900400be41403516480406031010010300a950600c020344811403850b4107000180e9406a01d540306082020010707180501401d02c0c60320505140014042c007406948111b050706a080000e104804095180481d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 997187302 1250 997186052 997186067
    0x21070e13030f030f0f02041e080f0604150f0e0c030d090e010b07050a021509090c0406080f0a0b0604080304080f032106150706090501110901020a020420040b0406 71
    0x400c00d01011004039441e240640380d0b50300c2c18009000c258442070031441010403030b0080e0010700240201103540e41c0c0e40c0d41400c66841e00c0140c036202c810040d020005001000012807002e810441030107403540c0d854a64540c2504ac00142c040d94165464020a60184034148141d01010300840050244118041e080508101c13a404124060180e02e48050027221803c6c0c49440c1950214090180c4d1811503061042c581021440006e610035050f0302150203000d01d050190090b03050685049a07561503002c07450341540542e0040b84001070742d10b00003501e803801030207030a608007111800010f0004003c40100d1541d600c0364011620035480040c01300078180007040200d0f015684180038500306402c031070403104800f040c8210100030b25008804940283c1d50444c2d00121a0880340c9421f549541034a0504081c2c20720b0300050340d1035440e0490410041c404a0100c621411050303000c0c080d0b13462594204002071204411145140780401c1110121000c05d0000340040c00d200301d4000e85503440d02c8801410324 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 997188552 1250 997187302 997187311
    0xa0b100201021303080c1c0908011b0c0f0c033e06160302071203030b0f0901061e02010b0d0615121a07020f15011e03050304030602070221070e 63
    0x1a0310410400c0384843c450240d25040c2c0340d000329542e0351040700c0e40b00c00f0314205042d42d0512107201c03002e0b42c040340d01e508640c121080b00c100000034015000c0221101050181000505c00402e0302c0d000703c0c2c0c00044c8012954000107205002c05c1641076204c0d200c2804000405c00c0d2030342041814a010000d0340015a1094030f4030320512404e089120035400400c440e40207020252030300c87c0000320407004050003807200d0b4018000390311404010809a04000f0b02808280c074056004d20000100301a0500300f0070a0035060b03031866100c0d04410102d02c0c0a06002c0c1c113103180700e50119580c44409411607a01c1e503229031400d5000395000300f0a2070300c5020401444005600410344c0d1035050383d1807800141d800c02c0807072414054004080c0c6a41d6015010303828100c0a081d100e807540904120403031301c0712a00403c1030680d4100f40785070800211036030308044240502c0c08040c1c1183d01c240010800625142c0040082c00d01c0a02074524808150554000c0452048802c50703254000d400d0902c00032681c1c03d2500e621 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 997189802 1250 997188552 997188557
    0x5100803070203030f071a070f0f0e030d11030d0618060509090604030503040204091506090b0a03230309060c30030f04020f03030a0513050102150a020304020a0e0a0b10 74
    0x4014082d8006641c0b0b00c18041200d0700c01101013140d1007401216914914007011000d448603452a0406000709008000300b00400480c500c1080e01245601c1407115280c40743c805401070200c0394221109480480d03420701601c4c2c842c4010418001e4901032409584020070240d40184082045220081c041d80c0144d04114002e0700c4450411040c00310020b2040e0704281c1509090b40c1e203450b076001160103000400805070103a034000380d45c50000c24495120341d048030703101602086030804140401c80103520034440034117200e00904000c2030149071001403120124140088030715001742d4030b0210328150001680000c003a00035402000e150388421100303142043d005140842400b40100710f1080f2804081d00c20406000f058000500319200c0442e81c1c0c030036800003801c60f9102c030301c075a078000c1080d40f1440340b14069a0014400003059400003481060314000301a8001142c2d481c503140358000c0d003000300180d0b03000108010000d00202c00031030440c06003016500200310300781c0c1c810078014018410f5404104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 997191052 1250 997189802 997189807
    0x405030f0d120506031e031207141c1b0f0e010201020405060d2d06140a0b3a09022409040b040f0219080a020705190f0f0605100803 58
    0x70555105502c21920303200000c1c00a05038035001c1c0802e14284800044428403040100b0259906400001500384010507107428402503941110071078491040781c0c1014030301c92003401413450078080b02040c3c001c1c0c0c40c081400024242112450050001225000c040c081190400c2d030b400f4496226a424103450f400303000942c5032600d00700201c1c80e14403590300c0d560b003000c2c0d840c0501c00800c101c5108a250404c0c0c217034002070951002c0701600700184100d21545c2125400b4a24000041c00e00300ca09004880c81700d40302c9800c025105a802280c7c410086d80031200d0070f2400080100142c01036005503000302c0b035080002d800401c620500c0502024a400c41c009511074900c0c3c1442080c1c07001c1160300d4184151070206404540f080424064500440300011180c00450b46071030341198040b480c0c0f40041d5607035816441e03444202c00c00b01284100403003d00250458141f5500100030b9005880b003484c0b0602900c20709045c0b131384030300e8403200c4002d500b29000341c3c6a1b0180421b0901211f4840040c101d918041d62 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 997192302 1250 997191052 997191073
    0x50306010f2301020f010606050c0708010e0604060e0f070e010e01050607150b06070c090203070f0c080703180b12090c03070e04060b01050c0706050a02011406090f100b040b0405030f 80
    0x15071440c48101d106510b100001041c032042d902c02c0c00385110f8032075004000c1c007001c0d498075000313442c613042281d00c1d103101d00c41d5030800a48101c050250700c89403c4220050120364989803a050050110340e200c500c402d109080b000c902c107500801c100c1d801450700c000140440d5041903040e0807440c0041e800544648030501141020881404206500d0390240400040d001152004100c0c20700501001920100c3d416900049489080c0c0003540300708041c3d9501c1030750b940c1c8044181d603082058940503240d04400c2c840c3c8800680581c0742290700e9480110076581c030513602c041413445030f80460f60741c995039083c0c0c2091142020702004a03052148084000d44005801d0417120140880000d0000e403a040d15960164400d9002c0c400300c0e1500070ba400e056840e0241c6807034001d8041c0c0c1c80707506014015840c003159915940c440044141c001d040007000400c4d10780f030310400490b403400c0c040c04860410741c1989000400d030302020b005000510440035441d440350300e043d0030581002c41440d0302c0032441e0071100111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 997193552 1250 997192302 997192319
    0x6120f07181419180b0f0307030803010e0402010e060d0b031e370b040b060418020112141608010f03030917070305060a02030411180114010e1009050306010f 69
    0xb00d021068903076000d200c01c988845205483c840c0d11120502020f215144066070203904074105150003901c071007003940300040605030365020314030004e0b02d610380c14030040c045030611a0341c0b1904140140340c0102c12020141c002115540031014103204540d4580080c0f88a0a041c0109100310036140b0310300b40d0340000c0e03060940d224020110b2980030540c41c1101210015110000704441080c500c9040580aa4516040201c40c90560341a102a0103240014225141a000348021030750007a21402e10400198019110b0380d480c1841c20710380d95180c0c804651207580e4400794510138484040b000002e80751072030300540300b140180c000d240c042e010003c040c00480d40102c030720b000b00e6000072120550103c008480b030381406141c0c0c10051450054206002400340306401550251f070050410110041b40d000810036000080016511240b40740c0004100d692040351015074090f80c113041c075940d02c2015400080b02039a00c58a01408100d00c4032040c070250034100001809808a201007091660030078507235 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 997194802 1250 997193552 997193579
    0x91018090201091203050a171003030804080702181905090c0d1707060605010f050c07061202070b0901050412110c10050c0f0601290d0b06120f0718 65
    0x1215011922980480116403140c10808000c1801c2c030460300c004001c91900070447d0303200f01e044600281d43d1180444804c140390111901421000600303407621450f5030781c00e031403402c8020800d03030b8202818002c840c0940c0301d15502a030b243c0740c49440f06189140403a07080b411044001c50240d160761400c0104045010b00140008000303a04070707200754554060340f400c0c5140030029070415090900c007040303920410019070040c8007981c800b62070b1240a081981030442c2e0a005035403565003075a0204c0d1003001094064848052190802032001d890081951a044e1110038142c42143d2160f540f1000c004c14452480003d0383c000c14030b0f2606c2c61000303101c40d4802d941ca121042480307110321450011954124092011642900d105e1000d50304c0c0801c110301e80ca5140da009229810510f0306c05002403403801d540b034030500c100e10310b001c8a5038245014144804024100c02c20f48507044402084040340b842d42959800c0d01c28002c0d01e41011580c50a40b00c001c150017034031000c01c0e1a400a07841c00b0b014100b00c030303140c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 997196052 1250 997194802 997194839
    0x40509010909022404050f06070515060303041e05040b010e06030c0c1501080c01020606030f0304530303130206032502070f080f120c030c15060910 65
    0x200450490b500e4000585030050351081c1c00741203180803801049001515010f8400c8507003c5034000d040318443c4090004900c981000141550403044400e0040f14000a903560042d402808413030409072518142c64042c048140141803520f00050100130380e1526015180d1411006c0ca040311070001e50300c01103240360001900d1150042008501c0034182c8202b00006c0200070003100025056580daa000c80791658031000c0320354014003501c1c00240c0d81d0305001802445452410009500c0d09103001d9020485c000714050601a2a080500040e00500d0028104004480c0c9040e2140000503070446052140c42c0304241418a03001442003040328000d04003501c401c3d075016900d0a90f00da0715030840c0034440d11802e9640c05120300f918950089aa0b0000d0104242d90780c04110031a07940c1c90b0b4200e07503aa00002100c1d11440d41c4281c040ca48059258405001c80d464001f0850b818145070981c0c1d039081c0111100842c0801d8024401c22009182c049030f50f907084072651815640e814100114030b403624201c0715 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 997197302 1250 997196052 997196069
    0x4030921110406061b2906040e12190c050105040311061006090905071707050c1e0d051c0c0203130e09281a15011706012016091104050901 61
    0x101c00d0001d00000000b40a806201c15080c06c40104002204c0b85000030300341c801c2d900032072402c0300c10001404009020200800308040c0f00d0b0031311035460200201c090700c1c0d0b200b5804210500c0d00c1600001d10034011180100c0c440d8030303980d6010046411180c030748a00141400304081c0d4042080150b150410100c9003512910180840c0c156180d07001950010285030302c42042c10102c4007003050340c0781d0142c043d281c90f000c0002607038940d04400052b03170040c0c0c640710344440b22a0000e001445490b4080e50045c0100070a00c68a44035440d900b500380d0046843e003502100c05038200054040380d4181c14403194002d49082d110a0402d401c104c00320907602e91440540b8040008031070341a0300601d44400161200940c030503c02c220300c1d4007001003416400000c0e03410b54100041d100d944005503029024941a601c90680030710381558a1000444a5410f0120a4201035420b46841c00e080e5030280303c800000300020396452515440e11142404450440743c500103055804d2100380300c0e0382e60b0961500c1c11100b000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 997198552 1250 997197302 997197347
    0x709180507030e0d0c02190b0f16020a03050a0c0f03120e0f2d0d020d1e0231020f040303200102160b0906060d0206030403092111040606 60
    0x4040a038020f0804010701c102c076202e440c6040b4082030340005e144456610a44003403001c0701c24142c0d0100e01c268075005032244000e0074071058148031200b4001c2c29811550110240d850621078000c903c0c00700094200381d0351608070b40150000d11944406000041c6101800650320038515290000f00d120030b88a810b003001410140b60301d4554550b8080c0d07121071002444e00702d4021401c1030940000640312142480c1c110461808402c40c41d02c3d00591800c15005441809a0040790340d5045004203c110b0406e1000318403820040941ca607054886ca52710180d00299803501c1c41c1c5201141e13541c20403c3c0c40160580108850503120b100301003900c007241c0d41410440c050b508900038088111a00a020307888035840481c1c090703169011903004070b034420300a458125581c0c80380000d80740c0f242c030300b00c031280d0b00308010206820040c10810010350744240a4a4048500d98441c101880405503030000c06040e000d904800300c041c411002d0103140d181d00200c408010040c0707085006000b07807800e07003480b004103080e4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 997199802 1250 997198552 997198561
    0x70c0e0f060d20030304090204090509010e07032910210203071404020c030a2114070c1a01080d09140904030804050f0105040c031104090c15170a0f0507091805 70
    0x20441003c040e400c0242983e803203d0306c0c1c0780ca11000790045c0c4115003883d42401d010540318803040c401d08600241001c003400c0c4503070075512a0316910300361011740e1250b00060b29044400ba001009400d010340140603402c4081450000402d508201e442007a48600e1580900b41c2c4c01603500040340d500729000d000003421008201d2000500034010249941624080020380a4006074030403410103035a1403440400c5e90000005040d50102d99203c44110400804d450106a007113004000403c42e8500c51507200800c0e10901a421030307440c0080c1d201282540c406200f004e0115040840c02d40500400416556800019000610415400342c4041c0500c200f6801150a0040901101d0a01400d0500911072030905192604c4a00800d200030b490440c1102d402c0700c4586014000ca00c0342d50b402a01e40f5880c2801c080ea5006501d0070314072103006001030030f8a0640c00c4818502c40511480f256400082c00b00b428030802c0055442c010451000c014003090240107250300318100501d02d83c00f40354000340039a02d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 997201052 1250 997199802 997199843
    0x403200d060b030f03070b0402190f060e04020c030703020105240303030408090a12140709060608160912150f05070807030c0216180c080714030a0b06070c0e0f060d 72
    0x800d44c46265141c0000541c07441400b003400b1700325015034800d5422003641c80c85280545652007403030240303403091152101c4c100301541c4601030121031064014401454076140740780662541e44030358000c03070240c0d456000300142d400150402018202c801140d001c441810440007a4480c840144000c00000000c12070b049551100300882c0b010740992166110300c2c0105080500d026201860f20b1030310340c800ca07103010410b042030b80540000c454542d241e5003166200c1c4040480d4500341040318070100000441d00007240f880220f124451140110444984852311400800c150307403803a03c0c4485000d0804042c440c445901410039503101c0710b145030006a91544000480c20162a5101541d08044600303011410b0030710044944071441c80d4030820071402c00c0400060f00c5280d01141c0280c042104040351001700107900001b1a488004a000010311310a590000790a6030010030f016903200204510a0002018291800d40c0010103e900541c403843d180001030002405180010b00800c180c2c400c507805c850303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 997202302 1250 997201052 997201063
    0x30a0e01030f060f030309080105130b040b1801020d0213090c051204050109020d110f0312030105153702210715051f05240307230403200d060b03 64
    0x2000d1300b900101380c5d0f99050041002d182c83c040c200c05035207000f02103440c0c9010301c100d1000311a0f201d041c0c01142e40d90364076007200e0000010000d01180b070805203030940d8604284003c01c01810b44040c0140c66400c0a04118080f01d40c40c0c10003090760740f8009070b8a41c0759070480e090320845111050101603980c1c552400c2030141400400081d00320680002c10410800d01c400c43da249402e040c0c03010804540f004040603500c1c3c0350304100403415141040140a142000e6282c1c520342080c1c0305c1c074a858900c0c00d000c409c2440181034903180b280780c0508405c180c4441c01c3c01400001661600c020f003240f0f05c0e242c4007081411031880b880c11080e600001d4910800509185601c0c0259480130204103515161510440541e4030101100b21b02d1560800401d4a2501d00c104012a0f0343c881400d44d40d080101300c81e0008c650001c2c0420f0705010f00c0c88403c0441c9010980460301890860180f5500c4610f146030003d205000c12044c448010b81605040030a47c45141e2124550b40c0c102c0c1c0042030744490000403d0402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 997203552 1250 997202302 997202309
    0xd03110d0b0d140a11030c1e030c0306010e0a1d3007060b13020c0309060a0c0b090708060a020c1b011b05010e0d051204032106060305060f0102030a0e01030f06 70
    0x50007183c106020010079107140c4a0300504404010b40c4040c1c00f00340d150712094003020f41c00440f00040c010384050768000e001d5005005801c6a20303221807100020f113450003da0100b140e44613030608200c002129070041080c3c8800380d100c1500108910b0160a07202d560b6603990380455030716403c00142101b42a020300c5084960650340641d540390340d04004010700000310b41107020341160100324401200c10310846440b40c5030a0061410106d45500f00411a07108012003010404040e408001052000140b01d00520720398006010180c074007d401410150000c000072480c0344140494000c5640204000103c48521403c0c4003017580c1d0b860050700e02650a0040c00440f541161140c002c20405600200c4c11071905812104902074000080b070306441070307403007801c40190084d002c600000c0c010380c03803406030518410010355548a10351703144007102c002c0da000200080d2240c040c0a46410700c541c0090282600384095890400b4034400501014000015607040658900d1100d0700741d0440d074401c4c0082c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 997204802 1250 997203552 997203563
    0xa0f0e040221151903020402090301020c0708030315041406040207170a02010b0a0b0703270b0a0e1c0201081b1b0705010219020f010c0303140403080106020d03110d0b0d 74
    0x1518941400d10400080f03807041c00100300c0c1a00e0368018500000b000501000813076440c685541940e0034030010b5000112039580540d02070041c20607000083c0516005400b051000f15100c0c503150440f180d000c10282021030040e45000681c030b0710340100046080d40200e0035200541d540398075140446030780849a242949640012941c8080c081c1e041d08540b10302c1d6030468032410b01c240c84050340ca9140c4102480280030688000e0340d503c4252081b9034102540349040320008005a461000d2455544070b07022400000b404189110024940410300c150324101400b50080350340030541c0060300c601c030050494903030801e4400301c00605002d10000c503800c1d1010148641404034104040300d581c2c8078180561070240c0078121035110407075002c101c0103e0042d0002c3c010101003808400544502030324010680070941c0b40c8174210800c00d41c0d100301a0046201c2e544410302580b620034000d0420300c1680000b0101400d210f141406071407003506841d01c40000940c00101c0c11001800a9840c840341c2500915 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 997206052 1250 997204802 997204837
    0x15010c030c0f2a17030406140415030203061002030313080c0a17040905060d0809040b0616050601080105090f060114061908010e07030219030b060d060f0312050a0f0e0402 75
    0x229040030010500303540101c01d41455860348884c01d042a203c02d150903800b941d4070a00c4100f14507842101c070401310003962258649080c0d22883d030fa0494482c0400187c4c0865000800d000d9a41490300840200f401d651000d1402c504115216088180800c18040e01681d03003c141d003464243c00f03210f00402140d1142d146540720440034410110f0390403a12901c1c4d1510300d0a000900c4604182014034105030740643d41e1407500003000100002040b04068690300680244001070b8108440ca903007000310390242c00100071940c5410741030790035a98024102c4049401034402c81280d0100058000d056540ca0f840103607103503981c01d020030024041d150146100b4030345810408a480d4012058030305a648882100f04142d1f602002a8141d108203080c0740388103036000200020a030f11a601140341381c00d0040100d8a01960f101105080e250150030052a103110040f0810400c40c2c0503400007805a1113082c05d80c2804440000940301505050760142070210700196064103940b194111500710801d0800c184 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 997207302 1250 997206052 997206083
    0x9010311190e030d030504020d060c090e0910050c180f0f041811030a02091512010f0e10050c07080307020a1b03020112110a0c0807050a031715010c030c0f 68
    0x20712050400346814001d0040d4400380d00e4440c0f05c0e01a49100d5074000d4046019a6a603a4800008004654441081041035400810449200d126003070199028034018031422a41d82180401c45101a014009030001005500c01100b0070421342450110119103100480000001003015101c0003800c040e4440d10300414070303007640c0202440200d03450040c05003201d0345044d032090695600f900d4402035071150f50400000c46209200b101224034041c007074078151840b00500d00307003800d4650200341e01303200544511104100b8081040110b0602c071b0640014440c5040c035030043c0d00b483c03055000107408000000001406c01d4001c000000c0055070042c01d172120b10715110a00c0f1217081c0e0a0008034000351070001d18041030030142c010000620203440415240080302e10054810040d00c900858500e1010b1040c1000b050091100911141c0261554588185440c000c1c94841030014a50f4840c40e800400802142e640070840074500d0b5410b003807543c607920f650f0030400c41c1e40c2c1d007441000301002c40b0f0810b813a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 997208552 1250 997207302 997207307
    0x3040e0c03091e0303040209070c150606023a0207030f0506060406090c121d0307050601050307080a03090b03102402010f02040503060f1312030903020c12030901031119 74
    0x710300c9000034000752401c00f040c00d60002603880c80ca070710003035081d8404d2000c07801501c0e14540054020310a401c0c8231314003000c0e45c0e40d04043c1c11800081050010b41e1501d0410425405200c40046c100404610b00700090700c0c4050303002c810030801c20100c9806c07442d02d60800600d0007013188101035908803d0300c646a000c03500d000d40e510301c001c460140c0100d003800c02c0091081078501403d103005140740c490001880442f841d280040484e0201c011a541d0400001045158140b0060802c18051342c003502a541c1007000340761a2021991220110380c4c072803100800402c0d84411440309980c0010480c1d070360b07070b144c03451016a03a51007a005a070040c080346460f2141d0070825054040020714a4000384485007004c2c610200f03d005038400c55426030032810016a12101041d00d0300c5e0f202d11000703201c04014019440d00b06581d569501880c1c00329640c1c2c100c00c020701d50104a00d80a4040c1190a100c00a10032050a5220b000f0100480d05054540d84032208281403003040d24184218101c0201200c0e040b030000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 997209802 1250 997208552 997208557
    0x212040f0303060b1c050a1113031202070602120a020705060c0c0a0501090f05010c05010207050105070216091e0c020f03161505040803010506030c07060618051e01050d020303040e0c 80
    0x841c0842e18004001480b41086001e0b646800a00b541c50701841c42d50f200002d025003c000d042000356603584400340c001c02c00b2040601b4480e003290307440ca01003c0c2507103000c060150000300c1c40000c0d540100020840170b6400550044083c06025110751210440c0d10300b03a1818003a90085075000801007010441c0382c100091640c5d9441c0125000d005072941c2d080103544a00550058880705011070b4000d1005500030b24000403501e00c40c0c000103103000d103151a620b0840c3c1c030640f41e60740140c01052508800c2a00341e00d101d000350940020401c07003020301a148010107210100301d0861513895201030280342e03000340995102100b000e419640d5a08400d181c00d100355071200001c42d0000ba503500e031303070806900c02e115952040e68807a00341d500e035900702020400e054000501019440b10204414000260340e8068803000b810940d0360f450070200130210380c1080d00d0340200049482e03004a641e4082c09910707141d102d4111402692440380300a000d0010030708510468124030035000c012000d0080c200d603403000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 997211052 1250 997209802 997209833
    0x8070f030f030c050a0c0302030d0e030705060106030c08070e010e0a142e030b190617060103090b0708100e0c09010f020307111309050a060c030e0c0603010e0a021204 73
    0x3070307101901c942840158211070f16480050300054090004559007030083e52039040b114040e0040f2414003c00b06900000c0d1040803008a040b500045001c20130000c0801a103805814142414006c480c5140b00050410200400c0038041000b41500c0c64070176405050050301e025030281400c581c894888920503d400c004140b600d00401001040040a9009070b1302d4980120840f6614604000403040c00c4000d80140c1c0407481d8444145000c03900c03a8000c5904581c024000d945074242100010041004a511300a01090615003044000000680b80783d060650010700c9062075003194590f581075185099158011620201c1408188010400300c8009045024401d81c0c0c0c903005c1030380320001243c5034016a00c004001d5002c15424050302d2821401c100030120182d100090150141d40750b441c98110800f109580c41c5940c1d030f1129401c25032600510140c0c50300c00b00105180c50b0b90901044c1244070501c00c60300600e14800c00b0410186890301141c02c0c0305e039004083d203100d0a00f4207060950800351603 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 997212302 1250 997211052 997211057
    0x10c0212010621020a030b0a0228080a14311b05010201090b010b0315090a1a09011526040b090708120711030c10030e15060f0d06060308070f03 63
    0x1e0401e00f040c514180f034001e0159000c0c200211240c03465886421000d0050700c809a041c2d000c0c0940c0d12015084c0101c513120036054011091009001c240262400c400901014500780c02c01c2001101038a80c134456540008000c0103942d080c8034070542060980c64000005020740c1c54190300803007032014140e240e800700407282c00040310083d45c660059003200c00003500200000040001004001801d402850b88640c4501010749072000701e00014190003c2101c18840c170a031b40700c2ca034851801c00110700184440b0251812040e5506082c0c00101520100025500704098249030004078900f805410380c00c14801c46081c0601d0409142c00d6406070001c43d00443c4034415100c0c000785070040055001c0001201e02c45051418225440d69054034043c2102650184602c800380441c5803550600c400d01090b083d5400508007462000c0c10307040074100c1034040e0380c03115000300b48107281d9900703450a0580a01102e0300003d44100b458100013900ca69030018051480206002d0f0902108181030a44903102c0e9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 997213552 1250 997212302 997212329
    0x80f0c120301090b0108220b13081306120905030f091210050f09012d021306110c01051309020903241806102706030c0311060a0e040506010c02120106 66
    0x9205240504030b40170041109203c11f01c5540f00031500802d002e0380c01900b000c91411070030142d512510072075408104011192440d06d4404c001080e031000030300116504091051081c00d0540d12040c1d5a030040b0795406001d0343c00040c2c0601640d44a007040c41d000342101050350940107060103080000c0400301c50004d080281100091403100040c411404625041c04242d07081c0600c80303c442d40279024004403007041580c00c00414000101284d820002881165180c16120342d0942d222410010020b00d0743d81402018040b10710401e5510725002e0584814210040e03e6040da0000a032504000f1540200701d10740c065022004580c0d404485882a40b051900c00000d10503401c80c036030703034410881d070703e80201c60503841c1070110081c884443e03501600e0722854640203101c2c00c4248011140150300460310983c650350b0400820503280c460810300501120001d0030008003601c06440c0b03181d8054001d10465684d00000c8050b80500c1d60340d56603e4020b04001200205050420f00a210038041c4801031001da = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 997214802 1250 997213552 997213561
    0xf06081606051312020d050f0a0c082b1403010602071a070201020d03050406060801061e090204080a060902041e15050307080d030905150f10060507080f0c120301090b0108 75
    0x54000ca840083c040309100718001d14000e04483c032800485012a4401c42c0c901445001c40e0b010008800007940c040050300c07501d0200c0c035015141400070340c032000c42500b01c2c0050361f000308172603034a4002c5102d88080c1c91140441681040b6103403000d504544030840b102100116616074001a094140c400c030010380c80c01c001e02d01003058414000c202000380168880792122004520035048030b90007910505020880540b140016825500d080d003201c1c0040804079103800381c103469801c0c48401030110351401c41c50141864603050300c422400c4400b50400751590550011074030f0f5035002d0000111107108081c610110110b5860203401201281e5109988238030001c075851601040000840b0509801031840704d1902005601810000106590300d009281c5194a504500720314144a00307408003803450289080c3c402038414462030b800010800805008040002e80b5000458543c0c658452080f9183c0505007111403908080c8c80402c0b11070880400005525420740c1c014414000d02621a03041c9580c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 997216052 1250 997214802 997214807
    0x20601061701150e030d110c090115050c0a1208041b05031e1603061d12073306080705180f101a030a060806070c0b07030f06081606 58
    0x21042281c0e0414401d4034010400c02c071041c1e0301c5884640d45418051401407400c2c0000342403100c203039204004204072400c00780f078015003400344003400c500490302d02c4803d50408075226441d0f5220004002030040014580040c1842049070b00c2400e0b41c0110808a20648840001c060b400259030072103e03402490f640507403c039203d04911007a2800900100030306281c51240c01d48000410043c8a140d01840c01c0520303c54034000c00030b9001c1c6000c2e510101d00641d141c1445140c945543c5550301d16500140c030f04080000c8804c08440c0507a4120706040f0103603e46418041d405103c1c02c80b03a80300350f800110241c00e0005a50000b804480c011310507215000c0e0342d42c09101c0740441400b40340458503440c000181c40703500c1e40c0d0050364202064036850340f203450302c07200b5850715110a90300c002805100842007280580d07090203088003800c0484c0c060016424201e102805245040c84010f106094080015640700e10a91000c0b6240e006158148043e80e582c1074802d440300301000074045030300c202e560045201c60 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 997217302 1250 997216052 997216067
    0xd05030f0a0e010e06211b0c1b060406120c17090d110111030402190308030c040801110703050d09050c15070c060e0d0b060d02040e0303090616050a0e03030d090503040602060106 78
    0x70340d1080c07940108101d42090001a0600900300d2010007202d00302c00303541c00c0030711010300031842125000782042c0d03841003201c217a03d0400d00889ca1181508000c00e0007001d5100d600ca406100c1e00c1c0c10041602010118140e6260742500329009011100d030081110f83c0fa000110112540d000e0f4955100840c1c201c440c0034241c80c1044008480d01c0d4003000804d00505085040c40c2d00d00000e8181c06680640703c0e039942085d5071060391031a8000310080780c01d100520080c894104008074851140b80303041d0090b80d0180c0707a8002c01c00e500803001d84d10040c0b4010f03c001800076800c9401d00400074440c000691030058a284c0003000e007039404182480000c10030324080c40e254006030200815040c800b1280d6035a009103004000c0686404c4241c01110200588550160740204249940510380300c0c07400f485664034001c0d00170704200003002410040002180c0010440f12001094900103018042400106e4910701c02c0b0800e00300380c14544030300f40c000d0000100290064070f02c143c1c285c0742d07240d980d00340858062 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 997218552 1250 997217302 997217317
    0x9150c030c0905010c1a09030a020d050307140d06030b2e0e1602010b0a03080702010e01020c010e041d160501090e040503041701090507090f0f1103060d05030f0a0e010e06 75
    0x1803082c103800e00c0550b024201318004117200d00c1c0144025810241124003100c82590010402e90020503202141078040c03041c2d1585000e646880c40c00c5251a40b40140002900c660480000100044414407602c094110001940d00094903821030306040d800385100d0011340b0b204c0300c0780110503194a0a07200d030342c9500d0300840340002d990381c0c8661107101c90160f80d804d450341d0050642d9078804c100e00c0b861f02d650049000550003440c01d03907100d0301d460001402c2413a6031085207046411014058506a0300644d03400701028081d140015400042034080c10511342c05c416032207561040240300820100e0300c504685c290b40b82030341c803046820381c0e03481d042051240549005000b80c10601040c800707545d01c041c4441c07910b00c210b4000301d04500151221414000581c0084c1403140e111030f43d4682c402c2d41402507040048555008000d401d80c0e40d6a048000d00001e009144503810f0440c46100b0700070b0030010b40e0310080003440850317901c620440d005021129050821070128000da4601c880d64503190040c0d5042 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 997219802 1250 997218552 997218557
    0x270601090905040c15091203120f0228051c02030108010e070e060f041d010c0f0e1320030a150909020306071103040f1409101a030c0d09150c030c 64
    0x15600700315081140c044941641006c1003000800041c582d40800b07400480300d40661207002c40c2c8000011101d0681c1c41150b0700b004120b0041040d440030080c2c007104c11042049102c0b412100e04a2000d003200e9500c90340121015030b4458030400840d00d84150700460480303001c54001c028890302e500c0000c4e150305251081c1c2501500c6440043c4e000d0524042d0306504110050000440c02010900804040800f165214458ad07443c101c1d01c04960308032400641c001e42d00d080055503009842d0000b020718140c2d20003004c0d216142c05001c00b81c184a9076070007210b004071081c8161245080400c040040c0504050182c01d00303080340000580c9005442a4604d013a0041c015188580c0d0f691030644070a4400404403500d0321040000060700c00d0441110b101414010080b07400b803050113010001e110b032020308a0f41c10605002c508100c1c56500104141000c03201043c06500c954030410080e81c0d80c000c4001d0081c0c41c07410050400c0c104000c038007220b034242505010421001401c450201c00300e03460312640001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 997221052 1250 997219802 997219823
    0xf0512031206040f0207060f0c021204030201120605120a0b0105010f120903140c0109050f0d020d124a07290c0f0d26040227060109090504 61
    0x802542071071160340d1021000d00081104401c3e24081022071b808503c00f52401c40c1e5500900c07150303400e0760080e030094054601c01013101028030340401b68240715910009060192111211540643c81d810110007442c00901840b00803000c0c464468035941c0c10704080750700703d44100020031558091000600455140d581f4000062040803180000309030151050b010310000301540c0c000c0e100d82100070800c10f02c01800204910b801803130014039042540400e0f04490b00806280d4440c1ca50010342143c2d1088140b0b0030f41c3c1c2c0005000c80060050800d40c03010102049403801d0340030700c5008a001d44950100a0a83c4681c00018101c055131080030001522456041280f080041c802c284200240c40b01c0f0300c14110091a0862090408650143e141282141c0142d01032441020301070045410720728507420700507240c005402e589041d551000400e80c03a0a100c0d1804103041d03484907100301c10000760b20002e511102350308500b9004800800c580460000c0c6044401045d211807031701400340141c2d80200101c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 997222302 1250 997221052 997221067
    0xf0103060e0c040f1b0306050d230d1e031518150f03060605010507080405220c0207050901140f04020313080d0b150304050a0210020106090f060f051203 67
    0x100500007100c00c40215201d080192101a952072050700d00e16101620001414448800079690380e030080159802814681030b0b0801041d02c03555000240d5680c407111034828070089000d0b2609003a0b80017808003061103030040c004c500c5500710100c0300740100400000e40480401c01000c82c20b69000388000d9206c2c0046c4c1d103080100880c603448074802035880c090003180b00c00405201500e92025907002e000c0d03160804d401001032060502c42c2c03401400007842c14070300e03043e01900e0340f1030540300f944583c40c02040111034410400e21840d076490f40300401c1c44410307c08000c62510003540c070702c5a40150f034070869404c0c000086201b6001c020080190020f0489800300c4804030400c002500000c05400b032446c100c0d40c00100088101c4000d04080746800800104408003405001c420000d09880a616810401c240004148001540c681c2c450303040b40e400d60a100c40e0340c2c00324007524580d40501195410452560744224440d00200160f90020350584281582d4004100e60580c800c0300c00700090f0003c100b0031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 997223552 1250 997222302 997222313
    0x10e060a120f060e211b0607230409020c03090f330405150d05100b040e0a1104080a03020c060403030e19120b1e0f06040c090e0906040b0705030f0103 66
    0xe03840c00088016141c414055010500344a501c5d0000320b0b0a41030b0000741403e001415100c0c2c901c0e48404d6400510413880c050701c0150140e109260410801415a290410340707020100880340a80400503043d5220792107210402e40c0c0e60041c500d002e20401d2801c000301003604101c1c0c44047c12140503401c0d40c500303410401a9991001050002860401041101282e01d4440c1203401041e00b840e08940d5540d8905416100c0484a01400c01040c00340821000c002d40c3e1030300310945060b500b40b0402030803541c48100c0c4410080006034100492450085000907502c0701c0816580811800798082c2c7e5844900381342002841c0c45035000c020040f0380c0b11b03840741c8042e0a1560000d041c9a81d00e05550004a4031402205201c09904204030390018214040010f00c4a00c101da034907807002e1002c1105020300305601d200c0c6800d600208900d02032541c994928a14502c21803580300100702d04030030001142000c0b03a000d52110000c0360266140088240890000d500c00c2044034860b0001070050402e0ba421650f40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 997224802 1250 997223552 997223561
    0x2010815040603051501030308070908031207030207320c18090703050105150423150a0b0304050622052e1a01090501020102040f0b0306030f06010e060a120f06 70
    0x5581e00326554140c00302c0094020003c0c00c90301144580c0020056241d460000c10544d0020012020000c96200804c4101d100100352001c1c501902c82111444da900c4004030000d000d011009840760741800e666140000081210070390803620343d090281400c1c14440072681c0c800444000c1500b017071041381e240c1194403000c0b14568000c508442907601c2666642c440703500303461007924202c5459240d000c0401c9585824810968015960300c140c500d10000c80b0213a41c00c07860024400d840800a0100c1d01c20baa60355002400b00cd0460810019103d0500f070400d2079071420100e882e80c410700c0d808605041c8900321254030071580d55022000749004d94040f4840080306400800c649964184501214030780046405a00e80b100180d6280c09031403413000e0001007580c0d09641c05941907910400050040703a0246500b4425103801c0507003580d40303441d0b19010a00d45004040d0011150007884008540007c4400d0940c0c02184111f544000c2c0d1340d00c0300d410590940d44180002c044040c0480b500c400204541c21 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 997226052 1250 997224802 997224841
    0x20a0305030121120305150901120b1b0c03121305060103030c1b1203080f0919020f090405030304111818010902030105270c06070201230706090b0a09020108 69
    0x541e0b4444811396690114405003402c8201103901d81c001c00403144900e8000100300d003400c4900404c10752400100f009041500301c4040c214416410001c1c500c50b08450b000850080b03100b1880c1d44c2c0388450440c490310380c0c11946008400031442408039030885607041c0000385064100c009052980d03c3c5a81c20764a40c10300c8482200d40070f800c140031840c0d607041162407a00a1011400c444000d02040c94010319070b280050118580754508024000c4502000500d81c07103d100c1c0900ca100c83d03258500005810368591f49549070b1052640007080104840070001d58012807156816200c01c9010108100d0088951505111119403000000d548074010640c101c0151202d0000020306c240c080d00800d082d900300300d0f2240003e440000354081d01c01d4045502d52001d410200241c0b0a000c00e400000fa101c0c822003c01a04010b10061100741c480e032034081c000500400719030300699605042c949200030302100d40c402e403001000306000901991081c0110480f09505a445200940d02c00142048003000c1c0c01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 997227302 1250 997226052 997226099
    0x51e0f06010f12151a0108070804030e10051c0b0108010801020a1407020103091703010515040806010b0a0504091a04110a08010b0f120903090a05010c11090a1b0e030d020a03050301 79
    0x2809113003d90724412620342c0322160341420740030244400003509062001c0d14002c1009865410440440ea02002900e55a0b50440e58080080c00740700044901e4000c070150540740c03042007a10543c02e907902e40d0000040708000e0f00c07040c91980e039070314806080340240b061100108002c05607003500710101400404005d441410000390219070313501d640700d18000c40141d84511100000050155290801c003109040002401c26464035081229076922001d040c45403519400c008507070b08031014081c006840180401c0b100c200700842000281e81e000c11441050180078900d8621007000d8209400c040312844040364071044034503407070032041c01016400644030f502102014407145a0740039800301c54601580c10785000715154182d0790304014020006500075814400001420000658862318400f030b107143c11590125669100780300c1e00c000d07215242034002c000c0b00c0340d4404c14199810860408040c7c4046c0c0860784001079004044c1d940c1c0328032000c0500841c105000403c200700c10095941690344c03501c2c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 997228552 1250 997227302 997227323
    0x301060e1f08071103180f221d030309010501030c0f030515040206160305040f05060304210201060f03030f0f1b0816020a030308010e06100f050a0903051e0f06010f12 73
    0x1300016802d68028002c07416941d0004038a059052400c410301e60820a001c403a00d4070340b02d54081106e43c91415900c8494901c685882c01030400506e0410701d4174007945a507050320313900d01d40f40c1c89184c020482408204d0b1411070a040202c1c6d1034070411044010780354090002c291020708a40301d401c420400030802c0b42d019078104128400903011103100d9074000e100ba01c1e075070b49841c20070390384c014042d03525040035014103814420440490008810b001100f07152821000301213121074001c80c0904004c0d0080c1040b0900310000008040c1c0c0314440390030721032030b5a5980c0d115022840c1304842e900c00e1401c50301d912030340501264000c079030700e680280307450602d00284a90800d21030b8003050441038154402d901040d9180010004040c400f64440d40c0410110b070000c0343c05520301d40180060b01485441da003000030200395550494050381c10351000d1a00a07040b1241c1502500407104510040d07007420305580100008410900c01c0000c005060b901c200c0201c001450801d0021001000510015285040302c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 997229802 1250 997228552 997228577
    0x2040e101d07181e0f09090b061026040203010f050106020d05090406030b0108060627040f060f1d070504051e1b2a1f0e03040803030c0301060e1f0807 66
    0x301030001c000404d92509000d0707a64034207200c402c400407850780141d11141c2440f035035100080d140c0458a5100e0000c9603055003c41c020182240ca41c03c4240440e002c41d05015450400f40104c0851184924800c6009100c000705400d0300a05403076084c0301e800f0240c0c3c02850f102c00483c6c013a00207414040e01c081d2001885598030340720091041001e912510359600440140400382c2031941c04003141080e04c2d0355140b002c021003501226034450003000034165010b02940700c0104042900201030840560307909000310704150500020360303011415660f103140329242001402d4281070059034402d8901420031f40211141c0429584400c40c01000c0700002c1050350056212403a0035400b0300140003541840303c89501d03580000241200b008084201c1d203911855000c50004010070080c1f26089800b00003050a00152410b07074510302a980103044117001c00f0081154003000c43d80518100e900315590081a991080d082c000750791031110304405040384030301c500c0c95100d008a4586800613000d10340443d02011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 997231052 1250 997229802 997229819
    0x50c10050c0307060603050d0504030317040201090905190b1002060a0b010e0319052b030903020c0301111201150c0605150d0609140303010501050403022202040e101d0718 75
    0x1120f0002c0b603015944800503c103000c020020982000c4003800c0c014a07050031a20003a210350009070000d260090104002001c591092500300010056080240200d0519408041d00000428041210036280441a004a05c3e06040701e860b039000b40d4016080e00e8a0320b100700000303061038003440d5043c02000408403143c3c2e00c00f00300c0e9507981c06d0010440d29100700c8900c1e006040440718401c0c01810720324000500d5400e480036142000b5074086041c00140403e02d0724040e42000c52000580398194641074a04590564400040000e4102c0d06a400907680e00c6094900050f03008100d8100018075401c190070018050303a10054021449007022a40740b01c0d040001008004106400c59200e62980380c0042001079007200e0705041d40c0000080d60943d0306040c002000b03401a440042c0c4100038800c040c800b40001d030300c0361150145203c0720641d40e85488104442001270160ba80140407506600f000641b1401c0400e050403404d80509504025110100121003940d00d1040c003500c00e015a40300001c401d203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 997232302 1250 997231052 997231057
    0x50619110a08220308391b0f0c120102030403021213270507030501030203061f0504091109090a1e050f010f0c030b0f09182422050c10050c03 62
    0x61003581c400c5418a001c010310b0300e03495044146c4031218003d00500e800d90b48407200c42203210718072075601541c40e0001491144c1140364008819440d0303024102c240010f80034086400b0742a0307081960802400c1150312095402c0b40300480b005030058220310748041514042400074200005450071a490403070700c851651b03082041414002c16841010b4281d1400390748603014240d03001e0290f0078200701640c55a00030a440f4507000b4641c20b040440e500c1001008880fa1000300b000d07110241c070400624205107001d002030314007c600d191042d4851800a51829000150710b50100e90109500d003411540c020480f12480b2005011550f500034000381c102c0f941c009100300200341740c18041c0424041d21802002e012200d0300c1100c0d82c092070404248003000e845034161317035400004005840c00c0088401280ba0305290041c030a064042e6181100c0e03007915017180b040c00380200f5100304159503495200d108286a04642e1800501e41d0b081240420000c2ca07101d2501d480480003401c1c86450265030401b0a82140d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 997233552 1250 997232302 997232371
    0x6050c040314010c0c0b0601021006120b0f07050a0e0409060507170106050405011e021609140703050106020a20041e060b1204121209050619110a08 65
    0x800041010402c1c40704561150081d404041e0081141514044004142e0340428402808491030107010480ca03074800c10120342303820040401040303400d40310f510410440c64141400c1c0c1e0a94070a002240b00c16981b04203d600540b060f4844a10f4440d41030402d0b106d1041c9aa000c583c069501c56810b00401c205010309032040d01d6035956250044140410309c4c00c4628180c01a40c200101030109008590300036519591150016807011011300725200124a02540509180407180e135011300060000080d07004000809607420b010181556102d100320200c400034458500181d1000c078581c80800d42d8180d60701c2030340d68200079141090100c02c0124007955102030000080e1880c034542021200214410034001d0303c0d02404a51134000001c1c0314078004040a4000340ca1903c1d99041c101c6098050059814901001c00b000d002d014524100161a000102d40180011401c8841e100140303040d0700c01d07c0c030364040654900c0e040001b2410200c03502036004103412072083c407080450090322402072814909 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 997234802 1250 997233552 997233571
    0x4020a170f120c0c0f030307061b0905040b060d0207110301020c0d020f0c180903160303020a030b032d010e0a05071e030503040506071e0308010611070e06040b030a0605 74
    0x114003100301510b28011070014016407200d030500c190101501c000c01e00c1d040e6141c045840c00119104940081d04504c14080700824241c40c100c00001d4035807000c1c03118031210b8025203408070381b01d5440003484141c52950395031030381c8a02e080100745403a280c00c1e0b01904000303004940c41325200c0c00b820042400c9900541c51001c29900140300c1c154860341c10001403040b04800d00240252000c07420128660501c43c1c3c1040408800107c00100071660400030386020180d988440011020603007800350095000300c45110000c0c0c28035110f01e185040009105030810076900c550074441868044034000d041c4043c8294000c0d5480f1100b038182e80404200b203d13045801080036017074061401e544806110400c40300c0e5035820550410070008994048151400c4400545e4030555420062901003444020b003450503543c0c0c03d007210890281070784000d600381a40c50b5612040c410700064114035540e42c1c001c0c800d0b489000d203060005a12424142c100307481c1a1005001c8564060895858800b510b0003162640b69 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 997236052 1250 997234802 997234813
    0xa3e07290610090b0f0708070501020f030f130201081501023306031606053a110c0601051207080a0b070807172a0a0203040305010e0601061704020a17 66
    0x40619041c1030042d0350b0b041504040588130f2034009580c040f0b000c2c2e802181303481c1d84086441020300882104590500364010001c554540500400490030f4000b5185072480f40c80000c001200c40240040f0b8000b80b0342c050b10766000d10b541751070841c14808151080c1e64118081d2860304946840d055501e00e021060503a0140e44083e0105080c0f4034002008106512039441151412a40c40c40e9032541c0e41520090301d0842d075100a11510414030b500c26910b19028083c0d14240343d107803854150100c0d15241034141c82446124203141002c541409034038500c000c26085400100f25034034181708484411024802682c40260ba60203620303003010004541a200e40762950204544c0e0f5030712200da142d000c1c48a05001d0911410714546c1c000100c8010301c01c08103540700003100d40e41c0c40e80c881301c0301040c442c240d03102694a03114080029129007261004030780a41c20000d0015034101c2c00b045207810303a92541d0b100702c0c1d01c2c0701d0021049074412010700f0607a0081420540461091039085c180c0c1062800d0400400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 997237302 1250 997236052 997236061
    0x2803061a04060e040b040c0e070e0907140d020318010c11060610080408160507090e150402150a140304061d1b1014030a3e0729 56
    0x260310114424285110300e2611406110303c10000d119a5002a002032108149684600d0306002c05c681e241c010001507005001080003070381c1c1c800404031501100b980e0901c50783c1c84e5018103603900700040960040700c0405020349203094600c1e50140d40d00c1184900749443c41026040d10b6802c480d0741d8110b4400088800030b00030b04040d010840c03150454010341d910010008100c200508410014000400031100080d10310f01c0c0c5d000c07500c040d0f02116003060548400c960303151841d0700100400103d42c61a40111500c240405031140145481650040c0402d24058070070b641142043c0d2280d04000140306642502c1c492034807101020b144142d01c03030040000c240b205501010803c0041900381c0725164480e140d000c9038102142d16000030003109980160901030f50f54070a440c83da4240361440c270b0945010040140c0c07008550000c008c108cc82520440e0b100c0522801e00750400200c1144040d8840c103022100400190b00c0004c10406000b0390050504009051a5160402051a0401100d9030032400d10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 997238552 1250 997237302 997237331
    0x120d02070f080c1b0108071b02100f14070213020c03070605100512240615030a140106110712030e100c060f060509011403010e1015050d0b06280306 65
    0xf200135542200c40303604a800100002000324100414020030003c005400343c1c0c6907021650703045c0c4200d50040491081064028005128070025590000091074480c3c000d00c40c000c14900300c9507015000fa24104030081140030740000381d0f02c14400b01c40b140c80104129800f0800341e1140d54000c03413014029003503035032a0404100c007d800b2101c0b4070010350811407010305845942030800b440c002489024510541e40d450010381c01e02200a006001400000204a2803a0880d03105081080e907a007854103440e601c80104a40b440540d1101245540c400c59061001007010310450510a1003407910b094041d0303201c0042040000040c80400200d50360600110410041d4010000b01e0100c041082045505c0d00000410b006ca06200b0325640304010f10201d0010f8500790005ea02c08600b20048607031030503141c11180e0041030304c0329400f0b000114070040402c1d2072070041d0108076000e03003101030034a207030726004100251811000002c0c0700d0301000703800301c9001d040013680d600015801450300003148a500f1810 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 997239802 1250 997238552 997238563
    0x1c021e12220e061e01030f0c0c0507120305040911091513170c0103020702030c0604080d0e060304030509060d0b1002031e04150c0c0503150a0f0608120d02070f080c 72
    0x41011424144200034064482200104003200f0b40f45445500e07913094401030b00140126120f8180c05410100c144107119008051b000d40c3c18812411140490303a142040723046511580c0b0b0050003c1d10401c020020540650030407403002c13986000e01131528498a002481d545107240306500c018002065a03c642c0110464050040c0101d00c100f4030070107459140ca90301d803803030000c40506056000c2103213001d5440070000e942030120013a00d140d903a5038a0740d05240d5140c1f19240c0000000f880700907101e40381c0c1465400c0c0d034015a41500c520b07003861131400c204411604110141390b440343c4d46140d03040e00741d51405815962085681c0156030f4511200201b00d0030f40c204032141412100c4200270410072256007001001103002c062030100a0460a844c14001c142e4840e4052a40f500c5080100c440d001c0140306141c0c00741000c00c50030000304c0700485018099a8041c0f0524015030002004880345011000051105912540740140361400b140e03240c0103641c1d440d6005542ca440003140d0b0202c1003008121 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 997241052 1250 997239802 997239809
    0x60d0e011d030a0f0c0c03060902031002090d140c0a091b0e13020f070f0c0510020f0a0b0a0e0f0304090c0504080d120e030a0e01021c021e1222 63
    0x14065042100d840440c1c1d900d109800300d010130402072221602c0040d208030920703028240c1c80025600c00e1a81c0e4107103034001e8000804142d01c60300079481c22040010341c62084804074800a0141c1c0800c1040e922420400c107040028a045800ba686807405255101d001d00c43c0903089070783c1e000851701d81c1e000a68042085502d01e16061042c80c900c4407d151f07440d42132440100401c40710140e526040511010054040c80900508103503a001c01c610401030108202420740c0c0007601c043c420007800d5003049036286c4180c84102c95681000c150940424201c188c01e40c2c0c01400303540c01084039000440d0b480e262480c54008000240c201180601c002c6200b8045c005c80c05403d8a801d5082c2400d04440903180d89000080c1781c103212010341103201040513604150004680c00007030301c1e281e004090b4007508415038808050700602030701d1500c0c00c00c10b10514604420308682d40c010070f0301c0c808080c51000e42d11000d045c20f052611030a2038007001980c07803000600e03450440c521101040b0f074424081920a128640 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 997242302 1250 997241052 997241081
    0x206150a030f060b0a0f0906031115030a05150d030c15050c031305010b0d0b0a0605031609020c0f0f0a0b01061d0609190b040e10030f02130b060d0e01 66
    0xc00400104103007150300804a50880d0000030392004120010306400300c03540c001b81c00240c20000c0081ea0700e007607601843c1241e0043c000019646405000c220b0440102d2220785c00c89001070011403604c4125500044e070044525440c0d400c900c1742d0030001004c4680da0141100000d8200e001c8400300510325101c80f14015240800384440d08000100210a00000b4518801c4844840499040c04025042840c007050301420000c0c03c0c0503241084451040c01715103440d4500c2c10f0407000119410000f0b040d20712404603e040350022824041a00060b5010301e0023103c162150320030150104605020b00445001440002c01d0345404034903100b00c42c044140c0c05842805440b221a058810000034080ba80f80c0003118031981d40c0c81301500045112100c0071415071203c4017580d010440c0c2d9040c8004209481010364618a41d42e40d4140082070312684ac0401020003010f50074603001030900407403c5104104101000c9850307900b04000c50317a07a40111102248403a00c40c82c403001c001c1c20030f10401005d4201c10303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 997243552 1250 997242302 997242319
    0x51e13020f041e0b0409020c0610060230121603050f0606071a010b0901200a03210e06070e040e0c060c031309021902060123010309020907020615 64
    0x14103201d180340510f1040a6429075204003050541114400c070101610101c82e415484946a04151000f5007045119240c0d621644c070104d00d40c0c0501041100c00c035070b040d42c014a83d05220300b0300104c010765041100c5480d068491032412114440c60054080c0c1c82c02007509410501d007030350000c10708019007e60b40080c54500010f000c46c01142814695009501341d45055440300c551511418002103040344101401454002254036104000106050346099a80e005000180d075804111b82450444603050303548603100300e0340000d0150303034660106251050302c0c000c000d244645a0701610700d448503054054000000304013007103400050590b080c039815078003040b1450441c0145540e031814040554401e50b00880c001c03803060340c20411164016000a000900141d48a141032301a401450380c4045101d0080c8100507581d100080740ca0403540c0700c6101142910010500c85104100d051341c040c1015100e8402d0310168484041c082d01845856005003400c0c5007036580316401000000480d80b049aa1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 997244802 1250 997243552 997243567
    0x1d06090f0f06010c06020a201f0b03031603020102071506140103090c12030c05010c181403010f0606051308210c0712031d010903022107051e1302 64
    0x60800c1540329812140002160b01d40c2d80042e030796441901002841c041c000111030030450343c4240451080030800320503011005210480c0d68440c420315807000c003250740e40c1e0441c95000c1d2168126502044000e02a640b60412080910f404510052000c0c0d0150303400003841c100700009011006c4009182c4001001540d0800c00c100d104182ca8103442410591a038134400d051221802d00c4800030003a0700c4810754058000d1170003030110b48000e01e041e0b6455103001100700038039015903041036504940303000d0303c1d803030138100b031b1400c180c4060180b041605590b036200c40c007034100518880c14000d130009464242c1c407814804032214a00c4259002040c440d00318007030305503038000300e281c1c0301c000012082c00300f41d242c0703070200d81941ca031241c56844a02d20b109100c003404181900540c0e0383c04007568034101040c0d01900d9100549186080303120094109448550914048030032514519429640701c0a45211341c0d41c4070000b07034507000841280c2d03200c0c5d804624200014a4118110344002c0740c80d40081d41848030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 997246052 1250 997244802 997244821
    0x50f03040b04060e0607091a0c150a111b0f07081002161e05100506010e01050c010213170c0a0b040b0a020304080a05011a010c170a11071d0609 63
    0x8090001007294901c64045020004190808440c0c224030000b125002d20380500c00a018640c0751080c1c944040c03825280424000886040b940d21300000300c02440b4008156146000642c00104484074203a034485080d02100d14140040030b031421604002404210308034240750801060032000078282d0b112460400c0b8522001c154030760038507080c003801611007041da00e2600002d4440c4a00519900c81900c1c103041510030059401d550b0342c0644126100c50480718601c0c01180c0b000c0d01c02e90301180280e04228119031081c030050621006050001d410544d103002e000048080980141030105a0102601001c400410130001c100400300c80b045105403401584100510890140c030000040025031000c2e902e008204076030080c86040d0031100300c00e103241440c60003030204140c208580076440c81044220f61107105000200b941164902e0b0030b4408018125500354003000300e00050150b207541c0c04054100a0150314000c0040d18406585011407440c0d070360f5488001425180f2482405050000421 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 997247302 1250 997246052 997246057
    0xb0604092102160b0301060908120f0a17070c05060907120609031412150a03150f150e041e03050f030402370b090607021903021504060f050f 62
    0x141040040324498003100700407420302a0080f0680f80d900507407840042c440308010001c6040304c1c00740e910241680d80b1003100c03076220b00a0380201d480610b01844000c03500308150300200200c0d007146c2448212501d42c1c035109208054121003810206001c1001603040c000184503480c0e0008040019114aa0408241e03011a01c840321015085560ba00d039220300301401803111422303201c0417051490312185021030003004808111000f842c042c413400e1844c451414019103810907680c1c89049403080050160a10004220080d24041ca987d290002e0304180005c0031891005854403203070801305894036040440120310103440c2c24041441c9044141d0210342e008040d90903400502e00180d5907515103000084500c03e24040d43d210b1007046084403000c20034141c0360624910768030000c0070305440c0d80d4040e4401d107001da202c00a800c00c3c0204055001440c1460290aa43d900c0071030003840c2544980210340c5458040280c01c0d040b2200060500c030954100c0401640c007544c034036095151082008140c0840e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 997248552 1250 997247302 997247333
    0x6051201050f10051e030f070f030606140a03030302130b0d090605061e01050304080421020f0102010522150f020901090b1e31050a0f03050703120203071e0b060409 72
    0x40172011020503d90b0303050119020350b01c09002201c81c0d060302c500e00c0c4900707072210b40320440b01c603440c0040000340b207800c2445418141d80000c1408080d9440c545040c1c0107175001c4505500354601d4a00081074501411001c0c080d842c00a020001d00c0c402180b6006044070005003459100f403c41c842e141c0c04480704e03840c0c5c010801d0001e01e89691030344c44600d4806064000d50700f01071114403002549011500801f003070150100c1c001c49500551119002c016800c03607100740c4000c2e288607800c0e6045149600740301000e00380325108480e20744806008010810446e0285401e0351282500020400345540c1c0c0414030802904a520071245006e801031586169a44050840c51600501043c0007260b900340361030000c43e0034421b030624a00820f006906002d03030002805802e00c14801d108010454811035400701050f00da1010003407144605503190005140c00800c140005c40c801001540000b41202c049040c440b9200d80806000020528000c2c9000c0d0000345010f00581ca04041e1401282c90904c400120307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 997249802 1250 997248552 997248589
    0x50303040f050a1a070f0e09060f010207051801090506031207111c1b0603020f120a02040b16050c0915010f0203091e090901020408070e0a06051201050f1005 69
    0x42900a10703007207040c298401405090100340190404040403030401d110700c5130405940d86d110039045030b4020b40b2421881090140c00071000b00000e41e80f42040c0160500c440c030140100c405050b50355001401c2003e00f118590000031a038401040340d400940189504002d040f00a081d100030001d00035642801010400381060710180140411612000640000d500c0c0c03000329229004d420b41000c03803c032401c264113150315003580180024503900c40d2099502061425100d1450301507560740444140030f016040d160400c2d420840020032200d00030060000b0034086416115040b15070512900f03010340006002e000d60201b40c100140c0d07030b105000050781c083d42400d01600f40130080b00d04a1641c003466004036003100d15061340a1401c040c080350050302c4042140c2140341596180c0c040d0b4280c0c00349105400c9150b0011105009440c0341510003a4040407812000400c556910700080c8000d0428000f035500b40d41da0024052400303c03a41c00b0382d90046490091039503451a08000c90340c0860380c5e000b01440c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 997251052 1250 997249802 997249823
    0x3010903080c070602070804060203030603060109200309030409050405161409131115070615050114030a020c0a0609030f181205030d05151002010509061b0c0709020a0908070305030304 81
    0xc008130b0741e0595a80641286800303444644840703010703540c0c0c0d01c2920628030030302c034100000511100c90701400030405812003041c00f80246080c0400f0282d000500840410b0105000220704030a1901c10170340f02c0c500940c000d142e0070b040142d42d01c404035800d410040020081490110003510b40c1d01c80190040b09003118544200c129007030190210000418030342e0303c00c08070602040c001d4040fa0207000c200c2d00540b0104404080046035510444452054902240c413000d1240e0f140100c2001075a881102c1c1d030009841e00ca0b201e00d00b107040c0302e2804003c4403166a120349980c181030380302c0c1d003408800200c0c1c14405015521403048034a42c044a124080d003480343c0d14084010448140180e0780605c01c50a01807005d030504030401e21904075415000f90142c0822401c080800340f05010f0305000b620700401410704d035110003030b00c02c4442e40d4095030181c050404008909224404100716002040480401606e80c280204001c00c1050780d58484a40da40c0141c0c0f003400401d00200803243c106502c1000c264 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 997252302 1250 997251052 997251067
    0x190c090b100e131e0605090603060a091b0b042409290c010203150603071e09030213050105031605011b0f0b01030501020405010e06180f0109080106060c050c03010903080c 75
    0x41d0030325481c840d030003981130904040c015582c070020024032071a5050039003440700540302c00030b200c01d80c07408480c11a41340d4403004c0424520195903000070700081c05019a10008111801c01e551b204081c0e50190002010020341000500000325a0020008450004000340d8080c0c00004100c403980e4040c10041801d120510044240042021400302d210040550344481e91880c019000707401c11107100ca1100151410290940380807000c4910035011600c511118001c0000b4402444101c503a44000b0320000c40004805655049030620b0510160000401d0960410085c035062600c03080b00c3d404030781760707520341400703241c1c0c0000c15204264414045001030f0b91050408070340f241004500035010300c49040007c002d222064000300255034003a01d0341e0480c3c0c0e501b242481018840c0110101c0d0505a1001849052030552400c040b04401450f1881225841d4900d80342140c0a59125901040c80410b00100f0400144087d48188074101c0003000310804c246c80140482c2e000802a05a075440040c510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 997253552 1250 997252302 997252309
    0xc090603060613021b10150b031f050909030c070503030f1b0717030c06010506090a0314011b1110140c03071103030406060303031a0f060706020408190c090b100e 71
    0x6440900c1700c1e8172024480d4401410752034451186961003100745003401001802c1d001818a00b01c111141e0040c0149150f42e0840d81d8820700b0342a592295005030000d000003074079a10303a030070b55004002d0362024560315016020300a29002c110f5100c2406a00f00b844190024004042943c6080e4100310090903242c0059440c40c4c00c00c121500480345440d0842503440201200201501d020781c62202181c82c40c1c0d886404102c1e543c09003094565226145a40920010b80d5442446c0102598623001040348001314108921072b196002d01ca000041013458540070103002003100c609107501442d0104502402d4555204403180b004000a20f903000000200300413510400c0c0c043c4c140092038040c1c9450f4113080c038040d0b018042d60320041d40040e082580e0540c1c4451508100b14444400800c01c0602505190034041c907034020400654a440d07082c840040c902c1c0702070144d80070000f080441c689451070780e864103850054003504030100300ca150100e96407407912681103030809812903080a01185d01c900001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 997254802 1250 997253552 997253557
    0x903171614010615021b0f012105100501030203041511130b041802090a060e04060801060b070b07051204170d0c02070512010902090604020c2a01020c09060306061302 73
    0x10840da64034640c4454000066110310190348104d0707508800300840c0348040b69107402840b5150301c400d4280300030b03607031380e00d440580c0302d141402c1814400a40c0d0034003080084806000146c48904980f1441080300720214489210302030142400c0460650409031220b80c00001d0707014655007800d56600507161684113000584802d20001c0d040c070a003840e00c41d41841035540003031290305500555052500c4070002140240c6006420242003815901d02d003d004454203041c680e034054019903150004a1029002e004602c041c0a5102c15650307211380d145031906110200405000400c0018410105035a02d040030241d0041e0b0001080400024400c210121a21404c0045640c8514040340580615001b081c5401101d038212040191130480c41d45240c00c2c0c8440040007903001c543c42c0c00007007107481e203503000d00340c2c40c510380301103c07001a801c004030400c1071181c541611500c55000c1004540b03690402008082c07050030341d5030354440e042400100f40d40b00c10281c4154460001d001c2c400d002e18034031368103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 997256052 1250 997254802 997254847
    0x21e0307020f0a03090f05271b040608152403040602135307030206340807061e05070c0b15090415060f03080910090317 53
    0xd80b036140d4a54940580320800b17134070500d05900c840d0703000024030b032074202d030300d0070b450150000394068030b08011082018885004004c001c0d103080c0c401e0008503541000700580041d01c120749584101c0c3c2049007800003546100766070f062240c907a440f421041c0020082100320301c4088070201c0b540300c0c0c80343e20740003000e8001c1e800380060031440e5480010301e5150b00029074010b00c5e000ca070307402ca2220011282880050a00b40801000183e0035000040c002440020410b4841210261a1500e440e40c3c0011055402013400300c5030300110309180c4407a00c1e020ba03600f205038800d00454680341c548641c4ca2108900441384041e0000d81c2d901110304003c100c40c2e00b14070924900100400840c03070181c1026044000781041130754080d00180004507164009100142001402403c803d116995559050030f0091100c6598510b00d46441c8001015592883c41078051407080d101280c44d407000d00c043c0140241c00400070810400800c80c20000308840400c0b00c038110402c4022150b440c00b4480301c000c0c2090701d002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 997257302 1250 997256052 997256083
    0xf0807020c0405040b01140d21090509040602042d03080a030f06091a060403020307260316110d020f0f04020f04090e011b05190905101206050103021e030702 69
    0x900b00000c1190141d170070303816240c00f400d07954513a01100c828405c0c122035000004000140c0b1000c80b84150055225030017501045242c08007959440d41c0102c0d0041000b6241140ca070f640100c0c00f4004264145c48403079a401707180301c9440c815906140d5001e0f42e00076501c4060100c1d040000d1f4521f1080c8642c110021101040c0d900780032080d42d030000d00d0300070010300c000a60b8000b40014894058076203a0202e8044a40082c014034665040c0002680d944020030004c80000601101041e81164280054100a510391241d41b801414505219103860f0902803103d204002c40f03000140160b48080c07406640c82001d82c1d000c2e82800008011800a129511f4800c4441801084c001400301050300700015081c0c9040003070011040c020030035002c000c208104035010034018010440d8881203a440c5918407032441c40e02802c030981c2c0700042030410048620901c00100710500c00e404101040c003656004007000e207802c514043d1007188039840820189034102c400e02000011a03282c034404c0144240c200c4038803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 997258552 1250 997257302 997257311
    0xa030f02091e0102100204050d0602030603031b070609120515100b0403150b061303140307290c0c070302060d091707060c0c02060d020a140309010f06150f0807020c04 73
    0x20345403980402c501c44801801441802502d10f4815030794000c2c0c9003111005402c1000c5220513544450103500010541030301480180b040c460300c02c042421120300d41e1030710006001041e0500b00010300541c5182c121014001b81201880009100003031241c1c00740d030b1040c0031008107840c3d1348200d0414580d079600200350700c03401040110030b00001101081006100d901c040040d005090144451402030000540e09c00c941c148041001c41d18401980c0c482003070400543e1316010066035841490040013044080c4204907040c800901028840706681000c4401010750070542c0c1e00070255502c1200b4000203010f01c80100c0d01c070200401c0c6401c55140540e00090a03283c040e5607092100550b003140c1d40c192201030610328207020840c081e021901d2240c1e0007800c40d916000c18006940040d60103002c04004000e0340d4400c0400c0308c0040030185000d042c04030008100502140c02c01c80558100b500b00d0905051403040e05c0b800c803604a4010000d0320801d040601d113590307c81609034280410002d0707803500107061 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 997259802 1250 997258552 997258579
    0x1403161d09160905060a080d2a030c0b0a020c06040f1a04021e1206010909290601051c0c0503060102070905060913081e0712020a15021602040f0501030204200a030f0209 74
    0x800c03a00c0303149c408442c04584071901e10400c1c40e1044a00720300c010340441c4003280072102090308102001d9000088880152806660b21070840c6002011201500c0d00041c28a0000c2049042219140d00552525142c901e50609400040000c20301d41302010b55684d0942c0c1004450b241d07500081110b280c03d0065802d07541e5950014406010002d504440c0c5c0504410305408e42e504a4004180355207400703c4c021400c0d81c1d88801946c8592041080e17040c01150111510ac4100e400d0040702c000a210f51347d6141c5a040000008e4070780b01b4142c2042088500784820000300d03480740642030383d104210082c828501c8600c0d003021004c9125000b0600800d8021800c07510028140400900016110ba001c40708600c80b4168120f0f294074600c980100044004000782c05410f98980151a500b0003501281c002d0380000e40c0003804940ca008031603506c1e1900d540041041d441e0903c248420700380c2c41610f80c040c840030850090110710409003054281990361001e002210260b9060390090040604a020340321207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 997261052 1250 997259802 997259807
    0x120105090c0d05030d020f0c030304030c02010e041a0609060c15040c0e06010f0e1201060f0321120f09080d050a0f02090a1403161d09160905060a080d 66
    0x204503001252441030048022032401e02d401d092950030f8101c80514180604c1c0b490441c069802003a1400c03650109001c00c2504440038001580110300c03a0b259031442403018400580356801c0c00c08068402e52925808000100807410940443c003012181c1580c1c54011100064050040300e20341e801d10f210b0f62240704851a208500745006038041c8500c0440716641d5076602030101c000316081c600080c807603146046c2c039a004500d03620010000400d00f04200442e82701c0300c1d08480850303201c541e451046c41400c00c14405040301ea0070a079001c06400c50840c1e4180c0002030000100440c081003002d980700060072101d450303684011882030f800a165552a07124000d003901a22080e03c0d4081664500300168400103118401c4030a506000740041752030a03d0030b050516039480c0e201c00aa05409402c02c0d06210110041e0306102619070309001e2291952008001e501201f802003403884a0742c05400e004100c202030ba6403510445504070310208041e03845c40c000c202000c40c0d96220038001d1041e00c5081c220703d80c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 997262302 1250 997261052 997261061
    0xc0209190e031b07050f060c120c010207030909020f0319140408090112140105040f020910020f070605070803010302040506030f0d08010501020d140708160f0b0f061212181201 77
    0x10300003105a0a403261483c02c0c3c4440552041d00d0303200b01d02032810780840c18000c015183e00704054042d94504900301c20346800580c401c5150782c2c0343c0e1350300050000405030002c414401501c04980118101056150304904600c005030114001d405400c4070710050203941d400c1281c00c8040d24180030034906091034000081d8200c0503404e4007040c10107031808800005c51049444a018110624486e41d10b030405000c005c003100e031440c0751095020000034002d611a030302c08006a2500e50b0080998010b0b02c0f00d1541072054541000e020000100200380101d4040000e507410340384c04940008094903000000391504070040030703848150050041c6800c04075048600c03241290405c0e026500f0380030307114000301e0b41111a540005162070081c0280d40104490001030629000118142a10038031642c03038808401000d680110b0780c169900c810040c2d105a8004980e4103c981610514121301012000d55155403648596030705420010440c2c004040c10440320716070300c0070082e00034418102c80105c424041c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 997263552 1250 997262302 997262317
    0x3090203160312090e0f0c1b071418070203030103110402041203030b030f010207051504110a0e01090c081e0c22170d050307031a1f0801090c0c0209190e03 68
    0x2801c0d0580001c2a01e14810800e06c542241c100d0100c41c0e90b620744d850311641e00440d20180d40300c2c558480c1030014540400400d4080d19000e4107403114510101d0801c0810420100d20b90382c600c0c1c9100031b02203030326000400c2c0c82c19070344e0010092000650403c0842c00070b000b107501081c0c414191141440c14141c0540c0241301c00001982698442d54420b00845c2c281c0c410a41c0080866000206100350203001c601680c0d0494456120303884108001c0d400a0700540042d04030780500509500100400c82041c8141d2544001030700707103121146000d0f036002c100411151424024031516800003200c0004800072207011103010300103400014100440700324005102e01400c4c114410611b81c0c00c540480024100526032010384e2641c2c03540d83c0d00c680c00c40c0135104141111102004100300403d5a650f400381340380c115515480c3e11510800d141400506406060340a4426945000b41b81c1c0c60050703116540c03a0985806072108030481c4c98000b50aa80c02c442c0f50030009040c4c0c60112000c0c06a00d01000500e600c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 997264802 1250 997263552 997263557
    0x30b011701060f0b031e010e25050409151d0a0e0607050306011d0a06110111041422140a0506121b03030d240b1201051c12030c020706050309060703090203160312 71
    0x2027854401041c9000d1000009030003c11402d210404c01035044d60424100c0c090004840980b81d03607104d0800e807003807152000700703452207082c442040f040790200c1c17044503236040300c0b03100030312140c101002c014245100c0900b04504001d581594145010076400c10300c05035210140c0300001d440e03039408000b80b000d426002c2d00c0c02d0302d50a003c00c0c81044da070034805940c20303100b00d018100340008501c41001100c190804012000400ca0001e101039180540708031040d0315140c01c481c1d0a1840d201c031520341100c0c00181164400c5800039104240782400180c0d1883e100030440440c00d550f408103000901c1c60140e1b03a10310706074505001c50010f001410b510741814801c3340c00c040b0700603551100c0402c80030380584000010b407120144010800391a1030f40c4d181c44c083c1108041603030284507648440084200e104018070100340c0700d00c2030440c039039810441c0000414851030f01324114200228078545558001e01400c0415407208003140c155a8103200180150107885540c2c130980381d41e441d1400702c8041e0f50300f40074003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 997266052 1250 997264802 997264831
    0x10614090a0312110319030c2c090604051302041a090c04030507121104020901031103090c0a143304061112040b07030c140106030b011701060f0b031e010e 68
    0x1000c034000140e41d41d0034480e1072064a0900034078400c60007816109423000400440400406c80d2415100d4814107480962803100341000c009428400c946901500d6140a00c0c40e1034100402003000000541e04a13a040341d000c24003240b0780340824070108049041c0c0340e010b0400030602018104160082040f24401d50541e11034558601c2c02c60500c1080701c401400d5120300103a1441d0924150b8010454042d0505001801011601d000718058000b02d51140326075001090182c1c09183c8040100000d01d40d0310b08041044515801207003101e0b00915282c14a100070385a2200311604542001e041c52009910340c0342c0f955a10308000304000706000300c00c00c0c140101054445881d00500482d01658001c1040618003921741d9804c40d40302401c008141c03070743c0e072040103260002c2400307000d2040158010641000c89504002016619201e8040000000e070b1500c02c0810000c4003140f00c0d42c080701e41141c88161280c0c0c44620001d03c2403119001209074031011400440c98168008081d8041d110406400a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 997267302 1250 997266052 997266077
    0x11120f06120d0c06060f15110712050c0906060f04030b040602040806040c1508040803010e13150f0b0d0c05060705101415181306020c0109050304031a0609010614090a0312 75
    0x151b44003030600070010425000d0700503d074154044e02d804103421410800311342001d569030720303010f51003482d949003101c5a0708101c2030301320545403100da85030300100110b5002d46003c030207140d1040a80702d2440010300c09403e140001c0c05208060307042c0c9004101140640b29217242c140f9000e00000f00500500c084411036100303c1c0c20301485025050f20170780d80030030114a56424000d100e1407100008203070140c00000d00e60038070700050800000318482c540703280f408251144020103070003d565403003007054010403a030100c071030215540c920300b4030880b1010790322039548a2543c01c049003043c1c43d05a4512840d03080601140c141000071020310712442c000c585040c080f4045004014542c0c55403a5003541c4118200e0200b0304000000c0c00d51280103120760401803408086640b098292141c944042c0c40e2a040070408100340409140b04032071803000419004454601140000c0726500306000304d41c03c02c155100d0302005040b444049504100005004644150f92854190341c503440c804464400100000f0002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 997268552 1250 997267302 997267319
    0x50124060e100c020d02120d020f1f051e090c0a0e0403080604180b010b0c1c020a15020403050109150b06040806131a07110111120f06120d0c0606 64
    0x24010880014020060a024803004480f1000014002da0b4494400303c0001c0050781c2d200401c42150030003201610310030010142c083c2c2080010160601c482d04040b264000c41400308116642061078010001403503158020100c5100e0500300d03032010040b0303e030350612010400c00600c41c00d848030102ca903a541c1e41e03110125603051800603240140410000008a8414a015000b6055a00c1c00080c0b003d10349640b921010b060a0302a400404111000200e461800009100f13031070074071500114041d040c8400090095441c22001c0c006080d070100700c00c03040340c90b04803501202c00454121000744500c0c5094100300541e2842d00031111386962606040a2042c03c00c1800d650449143d00d010f40100d03038405d0400245440c0305a01207842124088480302800002006030f4001c02d410b035505075035400002c03001c5003102c03030201548240c0e070340c04d01001e6400048808159070014030400208940c1e180e100c04034035044180b0b5400701c3c09006507c1a8a82e03694021a4042c2042c001e403010300c162a03542811307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 997269802 1250 997268552 997268567
    0x302070e07031e021315050d0c03290f01020f100e0705041103061e0d060f020f0703090303110328090f06170a0b060901180905040f211d0d05012406 65
    0x410105006200c40440382107641d01c48451001141004074001c1146800b001c503c01d840e40c440d03844800001d4072007001d4107000044501100c07080c0001e010301c2c18883f04080e528220006020401511002c0c840158242800309030000c102c00341040c00700d240184501c4031150030485445010f20002e0004401c08414403c0c0c0c504944000741110070365028648a0801030462a290b90b11010380820a85c0f43c0100711400901c0300c03500940c2d40d51401c80c19407800810120329a01d50004c5540180444d000d4201c0f404408800c00d040300203494580002101d050740d054407a80d0046e000361039591000100366070041041002900c00310200c0c140c91b564014000c007181c002035990707a04600280100d00c40c03075005100c80d081e0580e0458141c4070503a500e020a40988404070f40c2142e81714451024081089000d0002d20f01d004a8040003034290002c440000303004c01010003d070700841f88851312444c03e645800c100b5401558002000344030b8041107040342009002da601c000359410066070400100342c0d101d40311 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 997271052 1250 997269802 997269839
    0xd02060414011b08130602031201060f1b080c010b041103010b090d141507080420013b030a0f0605041104021b0d0c0302070e07031e0213 60
    0x262424541010814500c041100111505129031806110003041c02c0d5514814004d00c1400102c2da191001d261000702500103134412029075005011524110141003400c5040d40e520f4600400c40d100c07030103000c940354203090342000d415540e01c0c540303d414412514000c1100c8608040240241d404403c02d200440c1c81c241c0c04102d850310240014000b09003582c0003860b090000810014600005460b0400103400424003201258080301031312142b1b89020341d0813135200b011800d050b24181303071544400c048021005035440d1703c0015001501d0041e0301444d110100c0f9132509540130420441d03120030f0400100d909d0303100264154034807100710052130002102c5520700d5101e28005070301041941d45001070440034004031641c0c0382a10aa05194695101030564441e03440040c40c40410000c60300c605008844402d0741c200205030040d0740100c0d8000498004039502107030040c1c441d9841400c1100100042290204002003424682d05c04e5503454001e0f1200c41000305610381e89035510158550312581c2942c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 997272302 1250 997271052 997271059
    0x81c02060a0b010306080d030b040f180b18071d010e0c0d0504020402040929030706020d11010e01060b0301090e06010e150a0f0b0d1a1c050f1c0e0d02 66
    0x50008000c0c840c150070501060030181130100c1d01d60b40351080300b41407506812290f800aa0b5410f41d10701c0354a003500440d1044042c850040041480c00621509103948000020341803a4040021401c510301c0d101200b60034003100c805941c0129200d0030354008802d12610600340c02c00c840c10010a200209407250741c024159031840a103001c00340101200688401031003070380c4c0a079090100094505035400740741d40070781d40c03282043ca8100300101103604070344081c0e214900030b6111300c1d802d000341a0005043d10f8007820b1820300001c2e80d005982210b02620f040100d40c000e550901000040c0e0849403006076050301c2c4a18000e200e022456149583e440600b48a4a070180030700101184000201c1d0141480d9003030050041440c80303860301615505e00900b58040c4549180c00900076592201c0e51081c442564500c007080710500b0340754400510280100004000c1180c01c840903d01088000c01100304000741950035a4400e06c0300454011500080c5003142d008a100203200c248149003107014400e179241d004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 997273552 1250 997272302 997272313
    0x1091d0c030606090711160e150603190f0908070210030912050705030d0507050c0f190201030510030c1503050612150c040f03080c1c0e0915040213081c02 68
    0x100c0c01c000013400e0291042c824408169565440383c0c40a210502c1012101c04104004c1d038940f101580f2010070041058400b0003103400f00500c03980e1540d08490700b200d0302400701c08903075030030b143c00c0300003420030441c3c0e40308561a280703100040043c6071b0050816107000f00c500041e203050103001034095407a600d00040c9004000d5080c1c429232801000580822801802140c1c02c00354254507000032500141d441c2400f003000801e24003c029003c10a2070320320400b45024003080382c409028100c0c090110303003000341410344400c005001c03420789810150045030403407114484c055a038112003010321160356500000034100300006400e420070f020f031880c00f041002d0041409801102c1c02c0d0300400805490740e00e848004010015403012400c00700c0f000366020341c0c800303540c0f0045441c2e004c0c508500b8800100e03c000310340303420701e05064028411a060b05419034001e05280d031140e89036400c03440c849008950003840880e186030b860b007550b0900400e8841280869400300219401c0011b00d000c0a8881401030380318 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 997274802 1250 997273552 997273561
    0x160318121509060f1401060903111e0907050a080a060b072003120405030f070b180616060e06280b120a031205070507021815060301091d0c0306 63
    0x4440e03411801e41d424035000512460903584800a8440c1d0040501a15442e600d00d0302d00e030025840c3c480e00409060400c8107841c0d1a582d1890300301c1d452062500c0c42610404d20010800c0c60010450a001d00c1c02408101a85060321000d049500502e46100000d0711040c00991740003481e100c0c3c0c03010f94150307888a60428076281c1d604807258600094a00180b0480c0b000005582c03010403010614180400c1c071640c0310f5080105140c81e00c038211080042c0b56010700402c200e100d0018007261100c0d80f9403603241030742c40c4080011503a01e101e0380343da070004140301034940380070b01040313502115122484c5020b80d4025120860544a401c0850358218412610508a01d82100c6207601501d00c800c00540041080e407683c00506050500281003031b80800e1103568800d006d40c0162081c140e03c00754904002d41070060b103801040b048500d0fa2000ba030350745d00907404644513902424440c0b02c000802005540d9940e1140c0c0500c01900c0d02c0800240f4024040d00c1591060a010650205059001d0020640c40d0748 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 997276052 1250 997274802 997274813
    0xc0308030415050c0d1a0904170f1b010c030b101805040609090203070608040b0f150d03030204061701031713080a03050901080105030f1213090216031812 68
    0x76208580910001d030402e0021462401020310840e40784040c261600d1500c00d104041d90703200782c40c034040c008002400d01141c0c2d030f42082441d0469000780c42102d80703074174074020008284500b0203000000c1e68040713150040f450344c070702e00c0010300185100244405894140c0503400d5400d81c40045600007a51038254003541d200b0100c0340e801c1060402c011800e5607403080031500304c0f501038100903035031074a0700690401e50a0401c00100204018601003200d45071503103a81d09005000f4046080c1d0980341c101040908851003001c40440c040200b40521006492402500a5010340310340703800709400107000a64820300d543c80e28100c0f500086030030100d0341010325035209940b06441b14480f1490015020070395050170002200d400e4031940711103984490304000500f4410059000e64031a620030810b04600da8404076055036a00c5a0515003031710340c05043c1c540b4440046030740201221520202d119a40c0040c002240400207010b526a104022544e220b40d8030040c602d4098500b80401d08490000000c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 997277302 1250 997276052 997276057
    0x3110f1b030114010f0303090b04150e040207050105150a1a0409150f120512160209070e030a030c111914031f020307020d051603200a0305250c0308 65
    0x900000d03c0e144006005a0710720800e0300304003412002c0850910805800c000280c0c041c20002415504051405880501c2040b04035007000070010080c50464803603e442e010346041315888802404186020303281994101d5441902c148960000c0000044e15005846030100c10f1480c2040145844e00b00340e91880030348001011064405000b040010710602d42c0d1a0100107004600c00b03042d8950040d0906900e441c0080c00211008e200420034411f02c101d06411100c0000d83c1030340d20704403030340d0b44200940300b220f104096a078050084409050030180d004009042c1c0e244140220182c0410b541c043c8004003580344401c1f4107100c54001c003800120b4a06015003240b0000804a449500003555280c4030528088000001960044240b00c0c11075014020b100100c2c0d03542c9401c0341010200e038032042c00234629250140611500070300002da00c0d0400c21407460003d16400403600504241e28000b0110ba000009280441c0c02c14000c80d20f5041580f010802c00b1500503d68604041c25502c0b0a50b055 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 997278552 1250 997277302 997277353
    0xf100b0f0d021809031b060c041809050106091e060e07080408040b2b05040b160c12021c050c0703390f09050f160c05100903110f 57
    0x807600340100103140b1110f409644a065600702035501c030a10000c92108039040d050005280360848020404020043d0007a202168104400c40c4240860400904002c015203500504117500303040000c82c0d0300303101c1c0d0400c201256400c41c0030000446016165001c560319401045484507501000c03401ca17a03c0394481e142c215010b008090302e0b040c1e89050300011540076004000443c07000c05c514003950705106401c804420750015041c02140350594560a0341c0d20020a2204812001c42e40514881d00c603c2f03143c0b103211f521001c03c3e0a0300302c041d1790207548c0f0300e5400c2c0b021007050f291030f2411440e01d03c9141030301c441d0428000240030160550340e4115412508840e1500d05c0c6444405210240c0c1c0b1070012441c1c1d10032040303045622542480409180f040c01a08051030301350070081272141003444d83c26a00d41c00304502038050303d0b4440040d0300f148e85400400300588648200040600552400d48c0101c162501c603869540741950041445078481099601e4021075803c61002c000007003185c2000102c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 997279802 1250 997278552 997278559
    0xc060a0513030b010f090e07091d0a11030d1106131a040308011701020a0c020d1a04120f0f2f0706050d061d01090f0209060c0f100b0f0d02 61
    0x200404546215064a119407040c0c1d03d58041400410156050207410030203000160824800c840044044603560a080e00c10402002c0d600c0884151031442405c0200e030103034503142543d8200c000ba080c500b10610000a100d032107400b84116a0007401c0c0108603071a4001d1803e00a440715540300000e407085200020003c0d03c0d0b446a1030345201500481d050887c1c4502c0c400d44440c507a40d410018403908036041c9014040b4560b10402403aa8042c1d08020442901a811650f818131280700d45010161804c082d650030ba420050601480200690070f49800c00e0201141d40e10b1a080d2240e0008950b440d15075501c3c41c0200d600c510189501d01d40300d000503504e01010350b81d010a4176441c448950300d41516070344180000f40001c1002c126002083c01024001c000038180041281442c4208092604061050b540c10702d41d42d145a2048181d290191407103000c0062085454642c8500140d80b00c40e81410b012480e8056005c100c0d0784581c0300d104680c1081d00141a980d240c0f0305e11828002050049501170742e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 997281052 1250 997279802 997279807
    0xf01140a03150504120e0102070515040e091b06160b04030e0909010608060c0415110a1208010503100e06181c020a0210030c050307050f0d09110a08030c0c060a05 71
    0x2044008080c2192030580b00c02c0041e4520300f5042c40d000c1c1541400400302040344072040585281c3c0d00041d0303441607800032200d40000c1401d0324201e50142c422540603401280140f82003080214021809202030b207202241b458100c4000010840c42e03105003000c000343d4001c41c49540e8003184000150355841442070a150090000e00400280718907402c494080c0147c2d150181400707030305824030000350807411900c03802c0d081a00340034100095551500c0c3e110100031440c450002c1801d41049002c1c81190001074000b100b000c4200000d001760b8013402568020b00c2106040d210b291054801c04000c0c055000240c1a1629070700900c4811207240080300f141c030301c11000c0d55240d2115007001c2101d076030029001030991301410300c1032000ea81c60f540d00c068141454003a440e008a5044000c5940c00580751400fa03551308901300c0c80c00e0040c00b406450421591600000314100482102c03c01e4041c90308856001c45aa640c00c452030741e91043d19808080c6070004130880f109810038101030505060182011070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 997282302 1250 997281052 997281059
    0x6051605012a02070b0702011b080c0d030501080a030c110402070b010b0d0e150402151605070603050c09031f020f131e050d0308090322080d080f01140a 67
    0x242075444400c030320004000c0301000301048800c040d0781480c0942c0c20340040c0031214a4014200701c1805000300180c103002c00d076000c0c084400385400c180e00b41503920180517034403104078103c41540c8220365080340c408285440c002003802500041e030b1403182c540c103070303115050107000d5590b281c2040c51050350700b5041034091003100006500782040501814045510035140d4140070155416a0241d03040000c00b030b00b01600b118490340034041301d1503119405580c04c00c880d25000412032518880e0410200041c0300b6228043c04202010402c02c0c115405542c042c852600c2c0c82d001d40c8000c0c495565080d074103034020210032038104440c92260f010028401c0303005040401c1500d10246035800010780c0d035072800e2050000d016003481e00490500c03c0d450580304102c11030500000c1100c03c240e8a03006018811040000342c98204204111060700829003041001c40036102c8031058001d400d40a40a064042c0300e03805152a84901c0b622846100d203954903000c6d1380d02e0844100c0480c501c4054030745c2c21602140340030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 997283552 1250 997282302 997282313
    0x60403030e010b04020d020c010615120c0207030803090f072117040b040b030a05010e060a09021b070f05090c0322030c17030415060803030c09180c0c16050901060516 73
    0x1d2035406c0140724056500e0314811180c608407a035036000031100844000c004680d40b60320140750000e0b100310710720001da01145450305070b25140303c640c001010441e0020400102400102d0041d8a413581801194442512100034689510041f0121f81c002441c5105040c04160b011a00030200700d110389560f841c040d1505040102d5500c40e41044511120000610074490418802c0c0360040c202804800f0342d038148400002c44074000742c826050102c4e00814170304240b402d084007032070725134410001302c4505950351a4000010070451040901c10301d0100005810b0002c07140480c2c0c454103141d00c42c840c001d1041084550b501060410079020425082c01850003e0150301c042c043d000740c04980c040e00d034030b010f1601c9252101c031b4000b4031000509185040040c4040041034a80050b2500391080c0c031405c0307800201c0c9030450007a0b0000300090500041c081c00305c180030010700c403400c04d100954a00a000e043d041c0d41801d46881116080307081c0400403c5510f2048000e400308240c0160000e0b24600f807034542 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 997284802 1250 997283552 997283557
    0x4060206090d0201020703090506030402010528230703300b040e0c22090807080301140a03030804020906120f100606170103020f0d050d2f060403030e010b0402 70
    0x4540580e2062062008100c020005004060034600c0207619019083d070340100790118178410540900804804602103a004400b03407000ba20140c0f40c1c0400c0c20a01c0341e40400d890031708015181c007003039402e8686110310700c0c24140800c40100d00d0f0f544071324260040e54201c4060301940d0002d0700c4020304419841c1182c1250429640c150005900410360b0f8581504100448608900c5403686500c00e201c0e804154a07011501c4d0031161500c191419503c840b8441d101c045c00c03807484004c0110034000381003800c021040010314141d4140142e51070140d80b896080c400b00091900016020640300c4001400620700080020352110340a030085000c0400d1078222407802203a90b000c0060790f0008950980100001d210f43c0c402010b00f4a07015084081c1030500f00000f001c18080640075090303480f0000b0064454548402010394840129510901d00c0240146101344091000c5494070f40100125144e20b54500303440c02c03c1d0580c2c4040c0809443d1a034040c1c00410032405024400d54927032500f802c10387d03180e101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 997286052 1250 997284802 997284809
    0xc0108040b0a1e02042303210d060b0301090c08010b030a09051615080a02130b160b07050d1803052502090c040602011d0a12091809060c0923120304 65
    0x1005603c45c1d051100340a010400ba189241e60b8400704100c000b1295000240001c010b40c8910051f410211000c0300040c4522401c5c0c0707400d5449091140004100064074000c40c12203400c08010424440e01540481e40040d0a104030342003c08180b000c01ca6000481e4030400076603118500f203c0403002e100a4404201105078844480b80250380001c000998100c40495804407200004510b05040603540d80d10844540c042e02e048440c0204142814200b480d080400890304039805001c5490403010041c2164001e103141c038141401c11000300708100d50039154441c9503605494150401240e00a100500100c030f9000348205800c100a1501585030308441501600c0354001c142d984509007a806402e40320003130440d821040301c0b418100260000412241061540103411400e00f03465034104494585854215064a00240400c0c2420808a900007031102d0301c211000c0c032071028000d6042c1d609454501c5003401c100b154640104108a02d581c0d84da00c1004c0c000e1400147d05020f0900b40c8ca942c000780c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 997287302 1250 997286052 997286111
    0xb0f09041a0102060a0c080a0b0f041b0908010c050d020d090c150f0e091f0b0c01090c1205060c2203110a1203090b030a060b03070309140c0108040b0a 66
    0x1040e0071440d40c1c14490658400c040c01c90500c01c48001c00001800300d0b000410758403503555079100f612070503074034030a1681a20b00c2c003d00c2170241c180301c01c26001400e080344030181c1c003254695400282101046c00b600d42c001905449042c2419200c2da0042e010b5031000d504541201ea81d03480040004101c5084400584007480411174000418080a48101e135800182002e11405280c1e81c0030f503607940f030746003a07204000b10060500081020013101000440790010301700000040740d005c511100541c006042e443c000c0e01d0f051209561055942044258910068881e0704982c00150001040c04020309559902e141101c040740d80b05616019400083c0d041200d081c1e40d00715030041a0b240c03402c50341010301100c20145a02d80320390b50b03003d04070904607c90498442c41c0803000030448042e580c040d1001f0030115064544d00c0c030700344134020002c0c0b8000008507182c14100184e45134030480000c06040e4100706840300c030300586581c0c582c0e8246210040c80c07440d0250712084080580301000d1004240643d80c103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 997288552 1250 997287302 997287341
    0x40618061b0e12030f0703030b090a1a09070e0f0307050613050a0b04050a06030f0212010b28090b0d021e0c150412050304020a080717070b130b0f0904 66
    0x40002010760542c004560700c00c030302541010804990101c2150320703140304c8101465a039040f40c40d055001c0c0070143c0007694000581d01c20800103889a4100c0440c9111425000704182c400740f041100f207a9041e00e4020014000341c000d41aa82807840110b400983c000303045803541c0e0743e0b40c40000e40f543d00c0300042100d0605c082904010318289042d41e8409000748000c410304003401c10300402e81c2d1402d903100344410162940c0c01d2f5042c07031040754101e498441e4501a8000705684030b209a072083d522078102c24400c614101c98200e650b906003651140c50309140d1340d9510030346151907588101c0f0780012114001269003005131802400c40c00c0d545009162841442a4803038105101c4181440b070810501040c8840704010400060211640802c01040b541041a00c80e111400414005092074026250a00c60f001c00400c0140781803004401508801c02200c1c00303aa1100c0351960540114008005104140c0e041840822210b8018001c4072840106103410003081800007001d5480322a840c0d840130128 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 997289802 1250 997288552 997288601
    0x60f05044a060301090515041106030f07020f0c0a052e090609090b09040f0501090c0915060201090b0c07080c100603200d060b0a1205100b01140304061806 68
    0x10000c0c040c1d004004900810100c20179844403519800302e0500039111b04110400901002481e4040000c00362026280a4691030200003424130080e0565590001d841032109041072242e0001e4800c1c0c5513100549000015032612050045a000882e03070811048911090b0b00004003480900a910080c150342d0780703680c03902e0324601501103d80383e0004801581080c110b44c0c0c0a80703440006580065010040c4000c0703038881e04080380140094280103002a1b0700150000d001413090300500c00050b4015103034400c0d940e440d2000e900b26280700400810001c00400040c0d40703481e100c0058601d09000e60111481c100c4c0c480155800c1424507510344030a1130f50344170b043c01803180309101000c07944002d6001c0c4910311600c030006505c2c02c4000d00c0c010b00c1203444058201d2035407510352444004181462140710440003d14255849180071089000680d141005c242d207298840c4040f0003240110a420500d103440c0d50300c1d0003014146005903e15030304076054510300024a984507141310341c02c0e480a0030904c3c104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 997291052 1250 997289802 997289939
    0x9230f010e0628170f060607020405280e19081218010c0509130c030e100515010c1e02040b0d08180f01020706030e01090206031e01060f0504 62
    0x44a000300010890b109038240070080c0000682a049106444800690b50f500750024405e88208c09000307401905000900181c0000080f01040c103031366844000c56043d9018449800b140c181420210850340164017007046400d000348004503007030040c00c034945400c4640082d158400820b0303074a6103001421104502e8030720000c0c4602000c005c62031030703c50710f01b0403d44001641d10500c0140d4004843da00c24610f81020700a50008021800502c151000c0407590b10700100102000c8480c00000c601c1000aa5003962007540310310f1030b05500915200118140d80e11050500ea4504002c980043c1d44200c840e90075640c0d9200d0703d0070140b06071462a580c4036420007850440c85054029800b4965101c0070407196a000300b80da00513540546000a801c8140303020305070252501c4100039420140000910042c99000c000442583c4d070b040c0c4101d00503903039410080702c0001000c0440d500085050105010f0080310b0181100c0320540050000000f045000c40500c3c102c1d040c8420310200c03030308000785000801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 997292302 1250 997291052 997291117
    0x20d18060b180708070c0b07020a0507050a0803161403040e0a0b030607120c0302130603061a1e0d0209040f020a030b061c020313050d080709230f010e06 67
    0x403041d00c405a4555080118502c40c1a000d840001808000e4000070411481034410400741034020112002c02c0c02c1240c0d0280d25580714040039200c601072001e001c120750600070350320b00c100c0d913162008514103000d81080b007020701c88a032000c9401081a100d0782c21142e500b0405800601801030300d00d009820894104012030f500201458084d42100f010030010340c0d04141050119580150b0100c6c1481000c4400c400900c5030524920040f420440003245056155006901380c5254901561418902d0300340c20341c45000c0c4000b0032074880100c50f000c0380c00f0201e00e4081c108040b0546c07809404c00140c400001e060b40d1881034203002003607011a580340201d0b418091024a8102903524500e040490401d0320340c682e00010504288940010118040c0b801c4241c881c2550360f08030f01524000c154024000b402d00b0400d0f92400c00180302c1715070110700d00f034100c048504107031000750f10080c90f01604020702035149450401c05050207111240464580c8442004002e0031000e0250702c070382c1d503198400784510301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 997293552 1250 997292302 997292321
    0x12050d03050f100b030603100e0c0306071d1504030204021b010c17131103060108070e180d0f02010204050402181206090304060c0503040b0c0f01110922020d1806 71
    0x80e400c0078818140605056481070b6903200c1c0030130b0b90325680c840100b4078048103020090b401c07074904041038105640c041004264120101d080c2e590688076510215a04081d0010b40b04081c4458002070185280c07044903a0301400c15400c4007030900d5680c1d0002030885c0c0056845001c02c9811303d0718050020020700c1406076004030740c205a000040500e0b01240c50074401050010b00c0760807440840c0074440041e01c0250700300401821183c144d82c480090548481441c403d000da42104c0e0301c04121820300084410225540c4140204140c101e107030320445060509000d0b100035954200404142030303c07980001c180c1800c5441d50040300e06960001c1c06889003c0714001b41046d0000c4080c4010700c6004000c0f9001c9074254505401522a9400d145056100f1984003041042c00042d03200c110103008078100e840d004242000308001c1c120441c1d0381d2080d00c621065541c0c0a0300000c4c1c0000308581e80410218584038055005040c4480308080700c0c03c40d0007440d540c03540385080581074400c00407280145841d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 997294802 1250 997293552 997293571
    0x1210509010f0227030a020a08100b0a0b03061e030712050f06010b030103140c091e1f090e210712090b040515160b10060801080706081012050d0305 65
    0x140f503c055071348521000d000581c8256480c04030001001e5a41c104048503d2030f400074003040c500380c1c1d1140b40c103a48aa08586402202d41002c0c11442c072490266411000c8a11405446107103642e58410844040302c41c034506c200071443c084c0d5108040d1401c00c2144040c1c404130307030741c900c1907100750805c20324001984c6115605644103000510a120599060f20b046980c44901c00450391300b0402ca581c10304010030324407600680d03031504000450000d41ca42d5a0a4050601c0049003521207047c640d6440720711071444011992460b03010000e00343c1560200007200c42ea9015a0f03504a0150100755030321000440030100c0c030034041940390500200c0e400c0c2d450600500c1c18104c0c0454640031200149000328030505120743d514a0034406030b000d11008441751070702d07003a15040b4504000d1a04052209013614030304070080c080c00010518030700400805041c1c40c603040060200c649084012615048000c041410354100f2810000e03034010128a000d07041e900c01d4005e81466100c19000504640c0b005052800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 997296052 1250 997294802 997294807
    0x60b03010f03060c02100504030903020f06160b10270b030d020d08040204240311040b01170603120d020409051003080d0b0a050d05010f0e0c03070b0901210509010f02 73
    0x200000941400c070880350b00410100300032140502c10b030300380a403545181c85410b080c20100300c00c050348800074600b5a4401c41e00b2540d807280000521002c0e015440240c400c07000d81c41901ea01080d5910040c5600025102900e28807984418590a0220501688007003400841c000c0100c4195203000e20303056000198010403d80a58003c029501c0612043c1c2078148041c0101140540d103458101c034200d00c800f5940b9441100c0340c20810b0b691990940700980d10702403100503158940c41d09010312441604160741c0e01d11542c1007484c030170f900010080c1c041a49407040a600154260004001e841125070003080180c80d149000c1140b826120000c04e140c03100000941c0600021301014141d0b005a200000700181716082e000101c3c0b540300298202030340c420000c0654404000054101480700c0451600611001e00c9000056a0741c2d8208800d595241d003003180c00b404110b2102000c1c1c00d00d01414035180c00c044000d4900f030090500c00c81e054141460303c840c100445400309004400c16940c0c450381c11803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 997297302 1250 997296052 997296059
    0x18030210050a18110a0801060617060d020325290306040f0e0d03110702090610020c1f110a121b06050f100905010b0301030f0204140c030a060b0301 65
    0x291503040c0038848000840d40c03070000c10b0829450303a1000b03000d000da030003524001e02841d0400080b003400c0c0307504207407088442c0070010560314010b00403002180c005403a01204504a106415240304000701505d0b00140d0040302c000160350704203d509280c585149605000851540311850241003603042040300400760762034810b050309101d044080b1841c130007080988079120000010046d1207041010380800341000c0c407246410401091045210035203450401c42e080b01c00c2c1402079540a0000081c2d84000281c00180741c0703040040c282440c000c074a1040c1c60100d03d08100041d60003841e0080c00706101c10440c96515410340240e0058556507001c030061801078007507600c1c18540d007070403603025041000f1440d4904ca01004003a183e896654403100c00e00c1189060003040d8582c0c1c00c03c40f40f000b070002c0d4100307002915514520800e0b060702d0b644202e41c0d00c1c2d60300307544409000d074414840c01c80c1c006503590031108000181010311400b412800d0801652410b040414409464540d0480040c4803010801003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 997298552 1250 997297302 997297307
    0x60c04030210030c03230a0605041a01110709020705070510110601170f1b010e06040e0105040908121003030e0a1d090708030a0e03150108101a030318041803 69
    0x24038502c01140380200b00391807540003c034050401c88072142003010f020404a10016500104a07118481d00b030750402c52903a03644100410b90340381217a0714011a4200d640483e85501c0340c0741e501d01c400007a1040b070b001a41d070b0354915002c9070f20109041c4c4540c2c1040ea014072803032500b0100c01400154519000300c1605142914a80ba1541881402c80321000003146903180b05090181107484e01401c1305560400781d0010740c2d21010f0100b1498180041d01e01d829902482c40c2c0501502c064035840c541402c2203a003405c09100084c08072020030354045405101d02c85a070354581000600c141803184038581d40700c0c81d5140c0603016849a00e4954030401810310705114042c5c80140210300300c00502401142c5440d000c00c4a4200396207900a2007a9002c0054610401508601d00c154402c000344c040351003c1008002d9404990030038000c140480c2c1203030b90202106036441d00f00b9800001c10341102c02006004200003440c644c044110300d4601ca11a03103010307040b840c040c42001d00710b000780c402c10580c02038030340d800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 997299802 1250 997298552 997298569
    0x1618060509060d020a081f0e030a02060406050c090409030e0406140d0609110316030314120a0e010618060f080c03031207090504050c1b1b01030903050d050414060c040302 75
    0x201d030082545111500943d604c0d10405001409010240c0d40c40440c12a1f5046c2038080d0004840b2600c2e052115030900704200104035955681e544c0d026140541350303591004054040500615403402c414032000c0200c1d80c945c0306034115a403080d11020400c0a0405c00d2000b17803030103076104c5112008000360880c610b07105c030030004400c143d200900244501c05840d01c01005207a031a40150580710340c000205c03d0785402a41401668003d4455400740807810042200601c601d8030000c2d414000d00c40420b82840b00c42d0803920460204030300116045032140501d014034140010402d811035107401d803c200d00030695000501a05401c006030041c1d40c00700f001b0036560302c03800410440c102503000000310500e102d40018000303090001c1c420b11260400700180103154010f1181311481d90401d00058441110000d10007013070a507409107004442c02018010340c01407581090980034003008003c0d6600701021445007a20881c4a0403841c0100c00c1000041407600c2c0d002440c414159000304010b2002d03989644c00b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 997301052 1250 997299802 997299811
    0x2030702160f060e010212070b010515211e0703050105012015070c060c0203031b07030914060705060f04030306050307080705240714191a04141618060509 68
    0x510000c07130303030903100102e10b00030103420032003617140010842e00100300c143d0300174a048a10807640090540d54114070741140748200300f03041800011091040c903900c07051003002a400320f103600749101404080300516100c0c030720845030540043d81d5440148043d60700304c04624506c00511078074146010f0000040350350b0382031501c100d8004052032800988060301c01d00c100c4e0b06280d0b0000302400004810740010795207400555121800d00d848840281401c9100000e5488407609075440d17102451500840541441e002d80d1241c0c0c00000070070108012a00030001c09000c1c00381074010061515103410000c04940017500300d14071903042110108181100026100181c40c0101c6030f0292910a40000100c54106080d07814070b01d25002c5121400d2140b00c480b1454400ca0800c260340c0d04806000204420b0201800000c00a036003941541c200100e4145841d64006d110b201100c80300e400a2000d185844510480d500001c01b2408081c0b105141e4603554043d45071040390103021107030402000131a840001803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 997302158 1106 997301052 997301057
    0x141e150403052107150b03030c03040623030103030f1101090c060203030402090f010b0a111e0d12060b0f0c0a060f02071b0e070f2102030702160f06 65
    0x8007251940c950211340d00b0041c2e0f0b101d1741000000d00030906031580500c000c0c805087c1e01c18041004001030b003195100da107403000f004071001316100c84510034041c4100c0306000420000c0e820102405d5046810f0402004102c0201c5a4a00402246101030200f05081c180010080d8022004500070350003662041516941c102c907070580e4120030310411000348030801030445080d100e601e00c00706203480030007504d0004d01c511a400c01e0f02d01440082800c0c540002d44c403a03503015004070b040a40105803030000c0c415649480000743c9035000710500013000750710016820000c130301c043c403092203001d40c480420860310044a140c2d40080d0401601118000c00740c6080c014403500204982c0112103c0c1d11404841d035607900c40884030404514201d02c00c0c00021a52a0300c08031201d4001e58507200030101c01a01c91404d89402407800f901302d04148480d9000c603c040c0300341038490481e40d0a458590 = true := by decide +kernel

theorem cover : BRFrame.Cov 997122302 997302158 := by
  have h0 := BRFrame.cov_init 997122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 997122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 997122302 ≤ n) (h2 : n < 997302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
