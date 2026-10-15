-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5420
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:48:36.806863+00:00
-- url     : https://prove2.me/submissions/09bf243e-134a-4ecf-a28b-0a5295d25f71

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 974640287 ≤ n < 974820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 974641537 1250 974640287 974640299
    0x20f1302090409150b0111070b031806070801031e0b0f090109171c05061c03020c03030d141605030411030703060e0a03021630060207141605150702030c0a 68
    0x10301c2010010844c0c5840e2132011809540b007868203060000b280002411380614282c0e00702c034079500003015084014190250740c81040310038081c00d4010195a40c50040a50440c2001d1070b40e4040d010380488143ea003500004001002c050407160300580c00c0d10404000c0d507840c420b02c1d025040c0040010204a401c180017001e40c0c0710031000d40200c46407490001c020581c070202180880384c00381e498a510004000c1c583d4010190a108c5074485403080c410f0b5a04000c104000c030745143c02c81070f100b141440d12502d20700c40202e200c10415501c01100007002d405414000c0004e0300520000d04050000700046424891036102000f0b00c00007140e00c000100a41c4001050312515004405005c40050282c528114480c03100c14500b0b0b8243c603004610000310703580e04c02171120a2003110080e46664044003101c0e401040c000d1001e4110f40303008041c24150680710003e482c1c141311180d81800300001510310140f00301c1d192030152003070900042c1c26143c1e4a040c40d00001e86000440008180e0040103000c000c514 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 974642787 1250 974641537 974641553
    0x307021b19082107080d090f06060b041e050d080c030c060103200d110415030203070b030103230c060c0312041b081b010c0c090504200607020f1302090409 68
    0x20f101900d107800300145561180350381c501c100ca601500c801d4052044074403001c1d90303511501d6014031450110b41c1c600c9990b0b8449003565415413000a0743c080108003040860030b40502e4500f401142030b50b004103142001d0009003036074090840908401300c0402c2d91100c0170350400c2210800406402128030644c1d5910b401c600c074801d0f0f10111100c039840000340d80e0840c1030880d124841da035807040c600c500940802c014000144815100702a100c0354160740000944ca007131210402810414112a96070360550510070030b1841d040078071595620358607444c6420701c100440d40d83c2c08034034116001da51312154141c6092542c01781c65908503040010805110811496415101c15014003a001d12191171303841d00400d4950b500c81e0800410507045003080b003031644c444e440d96800b2610420301d00344402e8840300d0000c200c650450382100c200c4076000300312007034902100748110601070440e4020701c2e100540c2e0120352586130000d42a8003a040034850b9424183c180e8040e2900d0103000790041001e2010343c100148 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 974644037 1250 974642787 974642803
    0x115141e0a110102030609072708150714040504231906060306180b011418010315352a0a050607080a121d120307021b1908 54
    0x21810359002e403039940700180250b03032280d1801091650550b440c907406840100c090b5404016a954201254007030306840501813025102c031800611628000800341c03000c044000e0b045505100810504e801c2c01080e4608507002c2d264161404281441d0070103d10409240c040030500c05811a0010022241031803c40001d5420402c80144000742d0749400a500b125558080c002c030b03c100038201d0402c0e56006421200410f1070600d0304070b1b0f80504411040c03040790480c101044581e50700c40200102c41d030b8540030340240b40498500303c1800c0f515006012011900c14105207404240348810524038a101c009101c0180c0241000e0300c03441000c1441d40f0300403510020102c10b032901d8513082c02e0454146411003030162003015185074a8101aa1240003041d004040d482c3c0411607107110000250100d405182040d288581a840284003000322071170804600d411000b2000d0703024020484255400101814082d48070100c003140c1c880c210707000c100a560343c0041d0a0380c4540000001482c90360000c0d03008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 974645287 1250 974644037 974644057
    0x15050403231303020415050d0b01030c050f09190b03160f0f0308220b040f0512060c030a2c061918060f02120a1a03060115141e 56
    0x600c80c4258207211038940680500503008900a1405000604196101714154441449207034080c0341e60b00001031900c3d2807050f08448003d0b10a004208200c51b40d400040075101c100c81c0c809401c103020001c1035171480c00500700349004020055100c00c40000b82d001100d00140601a1010461403e60800303100c807040c480c045400200200018045d00c41080101c15039a124502c981b03040c07101108a00040c620b41c680c017941c80300e48400090341000c001c008000600c030100007031903964509020403c0c0354184030481066070700480200310300c800605c0e00f1680c2c080d80d0018002400d06800e014030441c0003031008907281140e48000b0450410400056892141111b00003900c01035103102070b1141620400303010b0904510000c0081800610107070000425000c03600c10060030a541d500e16021200782c01d41d181c00000e40e0311210400316001c0d182440040c520300740c00330645940351003030344e21700c000c1042c058508011b2a101c8007400300c855541100c4c82e0001034000000c1d01403801642c01e201d41e000807000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 974646537 1250 974645287 974645327
    0x708060d020f0a09151208161a0a0911240d020906131e06020307110114071202190503122203111009051b04021c05010512030408030f0715050403 64
    0x2844071b499083c0c952040d940084071601300400016049030612107460100d60844000801c035410a0890703601754820504124042202d403ca400c2012001441484c1540140303480d40d14140078584501e00d0b001114070440320b0035960055401028001d004a03000b240c1d100b003000038405d43c1c14201306024400e81d1481c48180d40345410158043c40062014801c001c00341e002808030802150200030454100001810b00814060f52030075822082d6200e480c0417034142d94039071526503600f0740c10056100340c51a0700003c41024001070f02c403c0d60302c4c010001c00c40c040c120440e0026042c01400060041021000c401c1051400300c5440c01400c050900d8050405600ca00da16008261a81d8000c00741d155401c2406031104122100540d8032007050f10460680103034003040138200780300f4044a09000025845d038001a2541001c041240200100c0c891b078500d54402e01091204141c040121400c081c0d004414903542c0704030b40707850366a41140c8026001c441e807400302003200b8580c0200160282400b00340403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 974647787 1250 974646537 974646539
    0x50d090b0402091806040602031f0303050a020d0905030703110402070c17060c0f12060a080d050a120c0f050a12021201060e09010f05150d020307050715050708060d020f0a0915 77
    0x40c040c03013030b8185130003501360f5015401040c0410115401550810680e1080441807030781071500f9045000c0c1a44118005200012501440e950502030861401100d10f410b00429150900090b0f039007c1500000e0011404034006101d180c0d102c0d41207408141d400010310000c1951488500b03021105200485018002d00700000d0034a4910011a51036010300240e05050007044807004900a40040106401c24092000401c0c0d40b1820049041c1d40b01150b0b07141a81c8008a0100400040042c4014180a4185031901c0f2030075401c02101c208540302032501503264000e200048442c4411224520901440001c50302802941c0944442c1600c0954417086610745200c000e118104078244904400100140300500240c0780038591408038125418032603003040c0c900d1484c10f049034820f0b11110040ba000144450400c10002240e64100f4a02d10040000c2d10301580090000e03840101080d100d51640040d800c2150760740c140341103400001070301d0807400e5500c03504a54020b101d826079854854104501c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 974649037 1250 974647787 974647801
    0x1c03020307080c0705010f0f0f0b0a18180c03050a020109170c103c0908060c1303060f050708090a030914030304210b0c28050d090b040209 61
    0x3228000c031520303a5019125943e0a11481464014040442c0c85548648040c0003411080c040e810f40c083d28103c0c005000a41e03e510001211f0300c0e144c40c41d0095541a100f007101c4620300503c0300744842c041ca404140149030100300b0442c0401c03418000e1104400703000110038084000784e000c0d0810710070b88440c1c0c00b0310340b242c507a04108010841510440e5021041c1c0c002181400850320541280ca414401c1c6403494012420182c032009541c40700494004c14142220790310405050402420942010003a071030402c04c0d0503441e10b1000b024850101c0d00018031008908414aa4000450b002801008074180306840c10380a043c095076400c001440030404524100400b00300040b0702940f6403500000c16280c44440c45004072020903403079240c0001c0c000060103c1c40c61000050040303808400304050f500078684604059406416005110414010f98003800e0f00c080c035601c8044104952a81030450100c81202c1c5072042030114609641031a030281c0c10801030307604542c010741c400c6449080941e11a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 974650287 1250 974649037 974649041
    0x50405010f09021f02030d0e03070605010918120e0d0b071107081b06040e01030b0417130608100f060903051c020d050f0f070311061513020a0512091c03 67
    0x10002039400716191184c2c900c030b0340c0b5146240038105114010b0f00c4c10034803415508012030740d2107030301f14200d0b0b00700182d01001c0201c18031900c0e02620241702d040000e000d1b5840d054510f84442c10b001010405060000d400d07282c041c0394810300c041c000408060080c2e04c0b91400c2a4042da09503080c00c042040c031407220400e010041209420b1340c400400030950300c01d40030580c3c2101c055082d2001d4001074100030114249132881d51540c040c5004440314080b90505151030b000401c000c0040d42c22058042c043e250441c50100e49030400c85a0b50710344212240c4a904034400e400c0000c1d846a040249284d00000f00306400602c0c14044a00640c15200c00c580c0001c078400f01200c400b00c00200681100d100100220700420162074507030907080c0f91a0500c6010400b180c03548d800100241d0214907000004012010200816548a6a603051600d03c03000c076200480e0001c0e8101000415a0344c002c103101003c41d10502c01e640440359100140090f50421010958903440b41502000003017242070411f07401c584c000c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 974651537 1250 974650287 974650301
    0x3020d0e01020d200a0c051009030c0e060301020903011a010f0216060305040c1805060f03010213090b041410050a080712020d02060c010525092114060a050405010f 72
    0x40e005001c80007100340084813940c402804940c0307502c03a20382d01e902c2e50325410810114201d10680303800c0c030043d0500c001c00441006400c074083c01c010750381c5018000207413807054440c11695940c85100c0513445500009002e07014100030365405600c7d20b80c601850303508602c020904102d0a89480f101d0b000806003ca858160080070b0043c1c080c150042000003910a034421540540650380303140c2c81035160340310960541d0100700ba8842c1140c036a4240301d02441c4c00031046901010460007140381c514000d07544882e04855102c2c1c0b00303815680d0717084040030f83c560360480356822560882c034541a181800c03003d240c0c0c0140740940b9000703008034070300443c81d1400002c4040948104c80000352404400f42d080108020b101c48049800c002c0c04c0c0b0425181010074012a401510104141c0c2c4014201d114001b01e40640580c4142c01c0040300c04040150860600d01694143e0a5607405200b202035400e2a00718010401c2407007505100f081c040010607107066010f0380c002c6114800a00c4800b00241d2034400303075103007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 974652787 1250 974651537 974651539
    0xe070f0507020f0a1e06090b0702011e030b0a0305011d010203040209041506270b0f060d0e0c03030a020607030509060c16110a0b070605010b1312060906020f0703020d0e 74
    0x1000071201510f030000e6600c402e200e0051101c580d060703d5450540c0040b41c5040402e00d12000c1040601c01640c0184458010b802d0700d034091810b01190f81c0009150041500354100300074000c01c41400072501c1b030b820009606c5c1c009400b0340126940c0380350160086c031710911110440408103034051145041030084074021a0010710050300354072984c0f54442c00008613901140483e030355440014001e203003102e410000280d1a68080800980c45028009848640340c189108070301ca110329504507903e084c00e440c0b0078a4542710005803806402d4186241c100340c01c4543e40d062101284e02d14140303030300080342c503c500b0312030f501403086486070603d2503690740c01135614500c0c108040c010301c0301201c0e06061051a5501590030170100c4e0341010040741803031070309800029480d1400550002800424007a0b03a0050440c0300f071440c41c1508202d503441c2d0700801070042500240000c040c0c2c4051003d1500504152900f02e51700315581c076000c00040100758002d00084015010701101419083c0c09202d08000c4108 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 974654037 1250 974652787 974652797
    0x30120180d0f0314070c060f0210051012030e12031e031006030b06070c0e0a0c02070b090f0d0b01060915020c0108150312030f091614010305220c0e070f 67
    0x150950f425241e80741814a00c07100034a0502007400400c401d1840c11000b00015291050440340c4064000e04000f00f0b20307000440c0c0d6003803070213001442111030a46002c5910803022100884000e1030112849081207003500da001d09151020413404a0110041076404c1200b5142d03810109002c00500c40c0c1d006c11202040c2101040201b001500c0c002d41110990b080e0041996280c000703207564101c0b000b00b070f0350411001032004504002d1605514428515580c0090008042d8289426180c814a1054940245c01440f0850002e902c1ea02e070a15403071421540200b103603503d581c485030002d006251f244142040004166030034843c0c1e60010542e0040004180d42c1d13007460359100c5900504040e001c0c0d20564040c802d040200a0003c036a90185000c2c4200ac0303002e004d54102242640d191130030315405103000141d4400104a40c903543d58401d0f000c0c040c2030038081600d5a500c014042e0281618441c04421682c0c0524a42081012000e010680d00004011401c0b6203421008803030442d2400ca105000c00c0e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 974655287 1250 974654037 974654063
    0x906010c1e0303090515090d17040f0221010c0e010306120201031e2c0106060f12021902100c08060a05040510031208010614090604090b030120180d 65
    0xe00c110540d9003109020b8100882c1da0130003075440c0381c6005101c44481d01943c10101c20700c20854001c1c4102d141070035884c0340c2a03904103411401000c0e50314001e04018925074040d0709110440d100d9420702516411600d03043c1880c070306102c9581c1c1c0680b4006403000700280c170f180300c02c28007903001344038a0041e180703000451030b4084100e82c01075005046000c042d250000c00700010b9040340000f801802002b01320150203410517a012601e00d000091030321100c15070f5034101681400340300d900c40700341801c5400a10b020380c4126031000010000b4411001660140030400d00c02058054001600910924601b06e003000b00700c03681c0d24201c07800042503915662103046a2010041854503400a0390040c070214400c1e40060ba0b01e903640c9895045036131600f80403a4141004112107600b00b0030440280621046440c60001c0c0a0002503403440f40303000b46c1c2081681c4a03103203d001d441c2540711041c442c521030266841d0b507080000c1c2c0301ca03980120240122003e81e0b141c50040314203000c5044010154020010b030158 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 974656537 1250 974655287 974655323
    0x2120910020703060e01060f1d06061c111207030b030d051b03041d09010915091407030302030c010f0e0d0804030c06111306030203040b0f0705090301020301030b060906010c 76
    0x25080c10211000314824910084081202481000c02c0b200b041d50000802515248515500410650000e5070030020014000e8110040301c1d82554001021910340703917902d030412403082d01a41e100e0108a03841d03181100c00c95183c45014024182d444006009000d40c0e070340c07104103c09403804101f40c0394050700401103800089028070054400d0300b00280415200307040404006243d500301da0302c0807802010503040c0140384240e04000c44e030840c2650000307001103001c94641018078881042c40e203030070171341d1403503868103102c3e01107401c2c00c4429150007550a590342d01d0034000d43e66003290311584c80725441c2040d00d40c1c4000203403003299040110000079000000140d0015246164001e0080e001c0c0201c681401c8001a03891046450b41d002c4640d0864603503242072002200c1d10101e400c4201414410002d00003c6000081125404a2050080001a03030f0304c00085a41e4003c0b404180d4066002000101c20081d0040c2e4052089409881c0403542d950b460004540304030a4003c003410140201c00c2850758 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 974657787 1250 974656537 974656549
    0x207030213060e0901091403031b09040f0c031409070e060d05210c0c0d0807110f10020304090b030303062107030f06020c0c010e03030d0f0e011812021209 68
    0x441201c03150002006680d030b80b400c9190650031141001180d54401e001010401d803162100c4c0c602129600460841c60103941d24028002c81d801989201d0202240302c840d15520b40e00641d41d1741c0789040d001c9c0705008242c14054081c1c0700d1b0300c1000c41446112000194450b800049100c211078110235a50342940b12802800b048482c510b01c2a00c03c0d00030f00801c076224004080ea2900c84094040707240e5a0b4001840e549403c00310300030301080c4200c40081d0002c1c00309154600b40c800990704407950041c8030000100145e10075003010f800581000300f08546042460700880500304440c0c50041c00c1c00501d181404154507880111010780d03010303480d41f10100c6451100e00302100c4a298480841d0440c46d1252500d8901501c01c00084030004c1e000104120482018054a04225400e003010305c001c03100f240c00685c90340940b4001c828620741c0d454070545d6668960b007102c0785c070b00c8005e0002c114a1001803082280e05580c3d10096540061002040380214800200c030050104281000303403c1451000802c20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 974659037 1250 974657787 974657809
    0x31e061c0204270311030a0806040b1918060e0c16110607080304060e07050a120c05060408151b18030a0b010609090621080307050d0915050a0c02070302 67
    0x282060360340c3e11100841840b1208100000b44514110381030840760f140c001d1140c0c0007690101c0f03640d0000c3c48402050754000c07524582000c002c480c08541c1986101c00708500c0302c0c4060340c25500e4041c890000464040c09599040501c008500911129840f0745517208150010742d0880c006c1d04081080709401c1101030301202150f80305034501556a43e9000000b00e041e00300b00d40c240c8001ca400401d105c1009524840c1c8030010a07248083d2203014600300006185c1004c602c0f540d00307911141840390041014041078031014210040a840c2c40781e88820103546e6541c41c1c44941d541c20a40000800d000420341c1c03201c0f4000b40f280c2c031030341c5d882e007122400c1c800402c2c0e03901c1035500d81501ca03c2d1440c1d800a151f41540d6800713820559510707000f25241940d458140c0307038264045a038a1501e43c0f20314030140d1012041295040c2c2240f0520f90701e07290803604942c2440380120b58102039180403c081d040003a0084200c0f131003140600706000d9620740c0d030250401c5800a0b9029005a80300c240100014144211101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 974660287 1250 974659037 974659039
    0x50105071104050613060b21060a0312180308070b0f010f05150f181c0803010b1602060c0604120302030c0702040f0e10061707080d0c0c1703031e061c02 67
    0x2103541c103407190305d8005440309500008003164001c61b505401c1c40201c6901c04032100900c00c017466500b1301e000402c0c52035880d4000588402d00c0b1034403110300b060180a101c1d112602c80254141c4482d41e07424880d2464102081c01c030380344850600440d40040404243c1c6045c0c03410340c0d640340f49051804080041c0c003180d4510f0580c4030348003403007010400880d86c406400841d80e811a03a01004140741c04011024241141d0754444107000802280481c000009890550ba40b0700150350b41d540c0030303246100ba190348a2400a45c44400024031865505010540070300883c4140a14412103010001c140d0a0707020860300499240390a2103180051303d0580c00103209540041000a1402c240559060078040040c1080400135180e00c000c1280c0058240b1200a40150202801200303080038001902c6400c040142c0c0d0811050785494001d00c80e036010000002c0221192050915000813505078a98104441c40c141e501000c0302c90000c88144000c01c0c910a0b2001070424034081c071521200480301800030020707 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 974661537 1250 974660287 974660299
    0x60e0c100e190303030b040b03030c101d0f100506011e08060d060204091a04021603080414011a190b04052e08010515040e04080306030a150507090501050711040506 72
    0x2c00d4407000e800940c0000395000b9600840e5540e001003c0c4010341d40d51880060280d03108106419800901090070201903100200c0421810816107800c0e2036100b4442400e500c900910b18807900d001e5000584802000541400b880b0541d10000151070619440546580d840d80045410300c0b6207229618403988040020301ca282d0140071078440500326000ba81014848503a04d41260700d510008040c05002e40604031004d600e0409001c072820848a240d8400070140101c00d4042030402511140f6503040003805002001405006104410006a2a003c071801034201d0102d406030038854803509030648000445003131a042c80c03c028400d6503200030864a6802403449542c08000780003880d0301591440c5540c0381009541400200900d03880800070844c04040c0c108010070044000b1051290702c20b8016101c542c5030354a4030080707405e01300301e08030042c0451480c0c007500106820540c802e03400f60102d6618202442d890340019103091086540190455056441042d80e41c6066000341c0c5e801100a410313 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 974662787 1250 974661537 974661559
    0x3030a0905100507050a14090619020a08030901050402010e42040e0717011202040c110616090801060305060f0901020403080c1f0c17220b0103060e0c100e 68
    0x210040341c00c180c40d00b400080c00041d003000c4443d404905080301601e40071640e85080c2c00100003c0051081804a9072040e441161038070642f0300038820900740640040d02039940c0d25221013440c6c000e000441d42240481d41003451000e440c03c0800c041c5100044800a0340c0ca908005440d0081034540d42c0c0c1c1100014013030031440141d40c3c00b041c01500080401c0c2e200055103041234200600070200b0000c10803c841d07101c02c0104004091420702d40011a01075400007600365034254200d4070740d40303002a0419544075074000d00c000322042101d1030038480d44540c1e031401c4040d2180711032800d031440c3d0312020304541d01040206d041044001026900712004000061a061b6640d407a55202d410806021000340c2011411200400121201804208904504101c1e1444095026000c42d402c0c000150180314000006641c5c0c01d4814100c03c06030140c0311030313400045000d1825001d810424001160040d040040500d4118070000b8500000840203001040301c80340c0c8101200c00c140c140114075441900061 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 974664037 1250 974662787 974662813
    0x1e06160c0f0609081c0903030e15030c0912010b030304210203070f090606030908071212050109020d240e1f14120c13021b070603020903070e01030503030a0905 70
    0xc1020002c0031076455503140c0c00e2400d0703400350a00d580211034171451032281c00022021903014080d903080c0d0350b040c240015480e4071400854101c50181c0312601c1036850000512000d07440e40300240004110845480013002c030801d1720a802d941d5070030480c3d80c065100740310130b02030090140b2180705482000074010305c45910680000b0302d050205c0c0e11280094100c20814055a0079a010f000e019101070309003071003684410ba64181c4070b8400c1900140c82c1c511000105050244034940700c2c5440e21950300240083c3d6140d884d800029840400c01100d002d2070300c0078400815030314410364014004014048240f4502d048140841a000100300d4240d4001590071040303a003843c0c901c000c020703000000c40805e16409020070f0007031564107809a0703401036014606003146a0f40c0d444105503280c0040d030000d62151208a8040303001000c65460321124041d410010420580c182d01500b4240011001c940f00d19940300110021000203010281c000d420810001d0710b00b41a540000c41987d00c40d0b81222401c01041c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 974665287 1250 974664037 974664059
    0x10905060f161b0303110d0f0219140a08091f1b0804050d12020d05010b0310120317040f05011b020d02010c1227111e06160c 55
    0x1503081c49020036030030a0002520002d0b60912950481d8200320811007803080e544412001000c400404041e1519070016045c0b02d65010350758215654002070000369142c01d90388010b5045001041701d4030032882e04043c5814071584503088001c51002c81e181c50001402e00031103516400816060362440b402540010a00c001085c4009506035240000340c219032a00710840b011010090300d03c100052081888041900860b6680e004042810080a940a8000d03e04064020b441ba8212150301e880000240800b00300c0003944210504555030394030f81d0302c4140708040c00e0f12080c405000030b124020058694419001120b4006001e150201048129551458251012810000c500d45140030520904540401c1800803000c841e00091003c580840e0380105880b1400181604041d251400d07007100c203150700a0b000418504104064101c4140d04048142141d82440140907a443c076040c000c52140082c0c2203d0219802044a46000409010302044001d44a0b003a0794680ac2d102c0000707170500c012 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 974666537 1250 974665287 974665291
    0x906070b060f1507120f1e0905060403230a120c03030207020a1202100201060501140f0f0313050705090f01170f0303090a150b1f050415030603020f040c1d0301090506 73
    0x4403041d070390b02c52180c603088041c5c0c2105050344003884000c1045005075a0450701e003920200700d40c40401142c2c00036a000300c030040ca06070712460f00840c00107808001d104800c585a045c2013408180f20f80940e00082c54255a103180981c0500005050344140c84180d12410264500d180245005803c25a203900010401c05c0c0c903502c244009040c040f003520460070080b42c801007c542900013003207402c0c548030010385010611800d00c05402c10016036604080c0e90142540c580b00700350811582ca03450600703000c118054004e1030680362031207503c800041c0c41c6420511a442841d52080f140c603240d02e0f103810000c042c40d000241c06418060f81011800160042001d50702c1442884d0081048081500308005181c4a00e07001c02c0300d10781020706548082c3c88207054071100300710103403860241035420181140e680c0540e81014003084002264a01699819089034040d43c0c02290a42c0020941c40c0400046503140c2064601080107a4041c84044d00b40215082201102800104898000d980d4090804d441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 974667787 1250 974666537 974666569
    0x309062712020123040927061e02070503040e062202460c0b090a06052a0d0e060a051611060f100509071706060906070b060f 55
    0x4140340003015581d0250145034041c6a41d084800010074603582c00c2580d00c650300440c10215120307d05455461200003015002039587c1d200840ca40005240060180148403003040300341c4c092a40744200b41c00107100b121801940300d4000d601c2d103403034403440e030842141c01409564071071413400c0b40c0c9144a00c24090014412206100180e441aa00c441c0c0000c0344502c007107050a01030342c0e0078a9200500603180100f45202d0b0703645c0c46014114288011641c0c440005c8000380b41c018060b080c804000e0340003c0307407844184a000f007804559128503207540400b0752640c00001596408520350510040703040180382c0706002e000045a4031460303452051400000703855103e0301d181c0d190200141244141c6400c1d40b94031851078001d0760303035404c252181daa0380c134040c0000005c03201c080007080084c4c0702c03100140300522016054071602d107401000640350100244900e009078100031300191062418804440320104000c0145040023003940ba40ca080c40720080a450308101018100b0f0344550714101d80c4030990030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 974669037 1250 974667787 974667809
    0x23030a0b0112020408100216050a0302010f1d0a03110f16090605010305011d0a180501050609220f0521040305010605040207020913020d12020a05070b040303090627 72
    0x4503040004103003078008800308051600c10720081c00310a8000c60443c001c1d406008000d0303118260a1a000103c5244480050a610403e224401015019081400d026405103410000d5400d000c100b1010010305042440e01a0400f00915000074041c10445407082842411559510000c1c5007846c60140c846100b014008403001c0100024081c2c1d00604000e41000c0c07905000c2c0b5490b041c4030021441c003600000049001000000d85010304aa010080003205401000840340183c1441e03030082006941642c02051100c001030304011982e113032595011945c1007140b008130099212503664100e0b58004440c10300400104d0405803682800e01c6100381800e03003c4503907a918500d40343d800c4403000da1200e03020b85d00522505c005692000b01c50341d8001600341060134061041c1c4001544509400002003c0240700030492005e60b82c00180d004440d4444da0407a10070540300c0503041361030b000c2c0d40300060000354101000c0c030040d48124801c4412410384c0e08014942030700c4000c0e58051201d55041540c41d11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 974670287 1250 974669037 974669051
    0x60d031b1514010b0705031204032601090b04050f07030e010917030f0a05090a020f0d0203060a06150306030503071e0b0702010f051807030605060d0f121403090a0323030a 75
    0x10042e1281c00380101340460702e0304d00d000c0c035a9a03800e40764000c51400f03041c2181000d00207024180107605e0840d2990113800c0c4060f55540c9140341014114081c05004601860304801b18001d060611440d80030f0095604040381c030f940d840c10214003922902c0c0401d5129525001c45000086403624014844081c0f0b90f400e54891800280114101c40000c0c101803625060000740000c03075402080742208141c0569000508031140c4006c2950260310f290003d4151140400300b04405d0140d6000ca4240c5203010300e03e44506c0c081c101c044080d0707110b60001400310b4100b0800000010010084a1400e6010100320b010900c1d01d0b894840002e5000c0301ca00d00580d4403040110a220094401c1c86c3e440301084260013800b413030b042c035030350740d00c82c00c500000308020b40c0e0300d0201340b0a40e198804040e025038819400c400b0705515180140f074500010950102060003103110000460707120040e64170a00d449001404031070050780b0200c489103001201d495581754460718440d4503d0b2254011803003400c41c407801084003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 974671537 1250 974670287 974670311
    0x30902061201050114180f0612100503010f1104050d05070f030605090c01091d090709110715060b0d0207020a0e0a141807090b0f03031306080708060d031b15 69
    0x14184032445110504401c2003070840d485551b125003150300c0301c15528140020701d4980403400920071000c402c030140300201c042016039441400c8520545500f0b40c0248a65083d147c198401c1e54070190780da0214020a02082c40380d03042a40d20314407098010380485111507582c00400900080c25003041e0f4580380c030317941002003424007004240d50b007039400c0c68050300c21840c1c4080006494034850303941908000e55404503102c03100c00c0000c80003070814080304000716015882c690700703290302109080700c1040c2d00c116080050a010b10888088884000f01f440c5001c110003d103000940c00b01000300e80c0145009004a8082c800b038009501c11408004002501034141e0350000386c03205d00034100c440c12680101c00b04a41c4801080004c215901c01d0030220711301d8404c000040300e076283c1c00080703601440049440c081c80e0b40000c15101c06c544182d01c1e00c2c4c980c1d88800c4000c03103100310112011a044580181c01d48002441400c21284289050200c0544400c0b0740da50044085a90503a00c1c81040d2195000440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 974672787 1250 974671537 974671547
    0xb040605011e09020702120601060509040f0b061606020f04030c0914190f0b090703200a020d050703020312010305030421050606010e120f010501061d010903080a0309020612010501 79
    0x900401e040b5003100d41012031022034680c0c0d0398081c10720740a801041c003808644502e01405d0001c6400015203145c4d6031528001429900854442440703641402100102c5002600c2581f07425078014020b0351074682c940c00781c41c0e03280b0700d240011a8015030030000400c0d8136142002400140d4801e4544280e01031a0100c88801e5442d98080d4545468090040c00140d0800c1403080d80b862a82800101c0e4000e00301d400340e40103051803110307140c205c04a40304112030707541e03d9400b1074224400d055003100c0030700d84003641012074084c40307022001580c002140034a205000d50050f201c800d1203881101e01c0c21004042c0300c0555102070f0b01c1208d1a07407011800740b103040100c031003802144040500e2014203045130380701c96546000180c440c0381480031000c00340807903031a4002d80b600da080c01d00080342d00c10903906050718000c040900c180c1d800100030409404c400e03020300b409030140407816540c42c0c0d019401c6803908040759000c903420b403080c1581d41145c0780060325040083d00b140480021034400320342c5000b0000d81 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 974674037 1250 974672787 974672789
    0x303070216090b030a0b060f040501120c0806010f0302061305041d010c031109060a11030a120b060c030a030b01120e07090b090103080a0e01020a0b090a030e0a140f15070b04060501 79
    0x94031400c20403c032240c0c0e20001141c03440903400142501141d00e90348081610103d1030500c03190440d06010000c20215907801e0801805845001940601541c4050032521030500f070003170103003001c2481410805461b25101600032110b0387c10900060b940d4034030000c0c040380c4506401c510b444010228050189900784a04049540e890409009608030040f03003032600e101e4101031340d10400001c1141641c0c24880c00c840d00e600d01035101142c0d902c10180038041c2c0b5090500042d89041402e000c441d9405091003402e4401d0383d280c2b000203600f4103901c004150040c210410400381000880b540e82c0f903124100d4000e8403004029603000e00040e078101908882907407244807185014002c0000100005000b290898207040d52514109503802c07101c4004038180350640e900070300012608018400749000c041000c0c0d00076403003520f94065a040d03980c18081d03d074401c1d10543c54509005604014a801e0504001048800c010710000900c0d2000740d00d200244c0050304191080030321501017200700803c900c183c80c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 974675287 1250 974674037 974674049
    0x612050115050109120c050a06050309010f060e0601030e28110a080c0d08040e0103110102010513230307060c0806010f030e030a0c0f2003190b0c0f07050303070216 72
    0x10102508003000680f03135a003188144100b24101c5100c01d010710883d03041e040054000104094070107030341d40e030303005000e5002a10340c8542075180400340c4412036580c2c4250000c9601742011081c065440c0300c015801800000340d500620300032a8191600701c101d20383d40a00b110310101c2d1007801441d540c140104507480e42c440143c00f8282291041c404000b001960b4044243e0072260307036151150f141351540c1d01c4d001d50307403100000071840d80c008010068205e080011801003031380200810707a00c013100320740b1002c1c1c1010040c0c24036000b0000298000b20046509010134950070850b40743c40ca20750307111011034200040301c2d400105401c06001c0b5542c3d201c25155005021031406000020940503129241d00c1a2074042080c409038442c0b000400500c21350035000103810440a9585080d03130079107140390712106d08240b44280200c54941d41100c807103501c0302001302e40044100c40c6940e111080b1012683c010303c1030721340419080c0020030000700100019441000280d000d48400081103055101040b160741001d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 974676537 1250 974675287 974675321
    0x18050d0f121107060510080d09061103070f060209010c0b04060b090601021203071b120e03120c0616050903070311090f070e040f0204170105010e1501021005150406120501 75
    0x2070100607100d015210030f250400e10008258540008185072010f0603417000340e030f6001e01241d030084140c101d181071080756112703201c0000350400c00754456141c2c40758080003400180c40040f4900465110340c080c004142c81810418040101078540741c9400ea402c80d42169059196800d1401c2c909107000183d422080a0004040090404030500d04034000284044208543c130b0360f40004501d900c41c4002450b43c4c00590000640307141c4080100101144480c1c54080e104d107000f030700c02249040301111001c504240190840c0c2d2603501480300f807102d019001c031080040601603000d40e6541448a0340c0194411b940e0440b0815424085c003001050003000340c0c1140300c4000401c00055040302c8080c0c50820100c6002801201201600c0002d01541d0001382c4e806d452000465400441540458103a800b028510411030b5102c21414181520900c01540145c22044413100440e8803a0041030700300e00c070b0a55105c0103401990200d02224000c0c3c1c020380d03062848041038414440288102f5400300d00032005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 974677787 1250 974676537 974676551
    0xe041d070b03090a0308091c020102030928150b04020c061b070c05040c140a092103050a0c03030b030102070b0711070e07050715050916060905010206040618050d0f12 73
    0x546480d010803134009024424004000b071180007051000c0008414110f03150350450416600080c002d400c200e54903480e61040e035134188024490f010503100301ca100301814201e43c60307041e5140428a2260401c0340e0f0050340321894907600f5507441c00175124078900f40000700a98038048102a00034100c00a200910143c01c010003808501480c03401c0003038800580c0d002c900d06540324011103906400d102c4603050304002107801d49555a01c8840c0200703c503041c180440c460300013080c6890841a46060040200d00104021000c083c0903141414000b0b00900700050300d00c0e003680c00b0a09981c4103e4080f545001148100a0100e40240040030844c00400c000c00320b0782d003400b280d00360f40000609150305000d004500001042040f0600054103000050f041c00359082c4a61405c0d80c44150301003038404a80c0b100000b0441c2445460302004460050b401007040b0349440d00d84200400080003040c00055640084401060041021500002841d518140d01e0650108005e09040d01429000036840c20444 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 974679037 1250 974677787 974677801
    0xb010f0c0b0f040f021518030c091b0d110a0909020309060f061c05060402151207230c0c010e060c0703110409051b09180604120e041d070b03 62
    0x290305034454600c0d0300b0108552a2800c3c0020240d00b200340007984840711540d40c0b0700342001007000c0c140c001010340f4004e00714408030b002c00d42c403801d40c3c0311013507003011210000440e00c00404003651140c0307030350340c03045c2e458a2182003000381510350304003507180030940c0003881c124238945c4010300d4001460f45800860540c140310000d0b68803500090100030902140c4004034425a079400c52804850340803030300a070740c10f4490346010f45c0c4401d800c0704d00b82d01c80d0954543c4e0918100d8100200d41604c540401240401d6442071410794100070a2580c2c0012185004040d60145000d0f000900380340841c2801041c0d9a829600010004c2d07100c040e48070b004940a100f118448280010f00e03400390313a0f0041c0303104c0d8001100030102c0c2c0100346440024041d07100c0c05850824a40c1d01030824400e600301030740c2090843e540d04146038001d00000b900407001d9404140002c010520010100e142e003041441e0180e1000340040000f401c3d50010300700c161406171001009000c2000070070024000306540c404881c00c6240642c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 974680287 1250 974679037 974679053
    0x140409140106051911101e05070c080301150e090405010e07140604060521011502010b10090e1f06120f1b11211c1a12010f06090b010f0c 60
    0x13508206212025001001c11142481880b046200d405820003c40c0940c20300500b140d8180b04044071500d142802007400341d4419018443c0b61504200868516460044415000c1695482940402a10216441c4655130701d0305c1e002d0103a40208004940e4080918080303040000310342c80382c110f030086400300701c20320703250072003030303400321202130416075118140588111703124021f01040c1012040100004580305800c00c01d8115101e649a0080014180300c1003031140607002402c05401003005510708100c1c20409003006588054100303141c158152950580700c04080342504400c0109041d13100a000c010a00d1280c1400041807250910152102001905a0b184c0441c2e66100708941140c241c481d001080042c000c1d007034407540507144109031000c13a4120640107070100100a10044414040b42341040c092140c1100070382031990202207400082040c00280307281048030035501ca1070f45080e0600c503445000d00a041e00d20f400314032026400001020320b8114000041406421541074010500b00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 974681537 1250 974680287 974680327
    0x605220210030c121805060f0603060a05060d05060708011a19050901110d081510020c0402130503190c060504060203160f0813090513050a08070314040914010605 71
    0x10304000403030040140040751034144d060700c4002d940e410314400740c1c2e8070078030303410900c0c04207008009680b4141c485044c0c8890b20002540c042c0d034594030260101c0c42c06440c960000c0e410081c0101009509400ba0b6a401e05180c0215000804500c903100100301510081290b00c4421010110303513454001c0701c0004040130102c41c001c0c0303420014042041d05040c5d0280020174942d55001003100d00d8011040c00080020504940e80c00021040b84000c81c42e604010711200c0340f04200d84c01610242050b001440000e400500e0b158199484800c00000c554a040c020b90b545a010102c00741e00540850500300f940e100f0660121b0200300307040104000403035012060b1201c40041c480c0201c42d00c1000c0c10921070b411010380d8050f02c0148001041404034400400040440342d088105004655450312035154080780005d014103030340c02810740b00c0e000400642c01081182e04c60f0a1154600112140f86003039038001d500407103503059642011032001000e8003101401490280ba18915055040c0c180b250880c1d14 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 974682787 1250 974681537 974681569
    0x605011b021e0f06040305070f170a020f041d0106031e1a070507171306020105010f060c0206070501050106020d02190f0209190c0207170307082a0a06052202 69
    0x42c426611440b0b5a49000c0f08800c210300800581d1110348900700703a6210741540c4101d10388070001031400100d001144040002c0c05542074042c00d640343d05902480407200e05101c000c0d078420399420798414003100243d05484ad400a000000802c0c41c194601900c15511075421801201c0099400300001040ccc030581c0303050328202884102c02920391007070955060003981e000810112010401c4044142400003070071000305032403240398840340e4034002a8205c4100307009200040c1d03041101401000e0241d8120341c4c90502c040c0c0f042c1e2401c800c170b850305801c6410030b80005c001030f00170b0140c1c0c00002c2d0f0b04101344985205141070907141c00000d50303280041d410394040d000b4000e94114000401d03104c50300101001c0d00055041c00e11000312a007038000c2d101c0d1214007404858080310040185034400000c04d4400e880e078440744003454131003040210403030303130743d4005901703c44d9907011025030000f80301413001041e010f10034103021540741400352220030b03038902e246051010100a07082c0e010250b5100503501d448850 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 974684037 1250 974682787 974682829
    0x3030717070203060406090308131101050a020715020724120c030b10020c030111040e07110a0f0807142a0d0218090d0503040f030e06120a0605011b02 66
    0x1580210342801814400b0b989401140c041100340319094022006241c4295a071210f5507580c0e407190816541488030160240b5002c006040041d4080c02c0141484100c81c011600e02c00d5491040315506241452a100160041c4004000c00e0a000c0c40324248012000a42d20706800d2444000300118003004011004540f9207109440c1d0301d0003a4040010500050030400f01201c02460107035030f520540a00303038000d61801c3d99041c0f40c0030000c020b550a46803d112021280c1e220741900711490104503103c0c03100e500450500100141c01c50303102000035445074003108e84605507801e000140c00b541140d0301c80075401c0a0303000307030303110080740c000400c0b054a1502c8a00300500c030001040c00c80030a41070003500118080707070300514556078411a520511080302100c40c0c0c010490700895880c0002e40b00100844031403004000068012050301c09030075400703009182031500c3d4000e4014440c0b004e4405003c40c40d52210103000550f84000c00e01c00700d0260500e001c04800c40d035800b04081707512640903402c0401c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 974685287 1250 974684037 974684063
    0x102010b10210e3a1b030201060f060305061e090402191203121d031b1504031206060e13090c09021903060503150f0a111c0f0b030307 59
    0x1030060351210001001e160102c40107105240c0204088103101c0c444804c1824110000c0301d07049540b60419955204203070307543c0c001034100b0981c00d0303c0342c00e00d42011010b55407610004100750502d480d44038018036460350003007400d003080c074180100400d4614220500343c260b01c426017500d4544152150b00300e54141c07004681c4480c040e40b80c0e06159070302e8100d200c0d040303090041320040c10352241c220060407940784402c1001c100580b00401e0802d86014500300300350424088060303c0764090004d14070700e40000c810b44c1d0354027680c6811900119012201207001c207076071440c61004140d062107101c002c0d215500307100103241401030018015101d6004042c181c55101d5003150200103e08107000028a4458800d649507a4100a5021000c0b502c800c6080024074145000541e89030015007040706503202d03504009940c03140c00c098130b02c00200515413204140c136502040340308404140145505428401c0303030304031034007046c031b00303e043d10030440c0c104500c1400c010340c40081e543e020040b0b44106500c41074604400e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 974686537 1250 974685287 974685347
    0x30f0601111615090b0315060307020c1c03030c090f0b0a020c1e09090d0e0f030a0c03060c03060806221b08070302040b100c0318030c140102010b10 65
    0x101a8801160202d140c4010018032020009080c00d4414620303255a490036860b0081d034000344c04200c50030b00700300151000725042401c0c41d100031070f005402d40c41500d082440000c00f107a1002c1110396895103805800e004c110a050b803510540c07003081c41c1403504001703062415034843c1c6507010b00d010f51100c2050000c6d80d080f840e4005c01011141113800b90103e8901450050115081115422200d000d10301c404c0c0061100b0a0126545035580c00300e0b1030303403180300300001c0a0164000704000c1d0039030507204491000011410380000d0300010340c4034a8010510400c4410b0042c25a40c0d20791000701143d00c560b09000d4148400a108030f00c0211025800300c4c0c1000b103040201d01d4200443c0f140c11000c885900c007042410001c1486c005403402a6810700070178200702c0c288076110056042283c00103820300ba050002a220ba400c2c15001c0900c40710841000b52241c030740d01c1c1b80c00160780c040e80000301209001d4078656020301443c0d031511022211400301400760070303001d01a80301c000e24010181c180c1c50304040030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 974687787 1250 974686537 974686543
    0x30705150c0618070510120f0e010f0507031a01020601030f0804050a151e080a0902030708010c02010203041e1a09070906090903020c09090d1b0b040323030f060111 72
    0x800c41071108459203418981d1010050000c58030142200340510a00800c285c00d02220086014469640701c00c4200840355000000302551707000001029119400c80e840b000090040710884048850000303610305084e48081c007114261020494425610140500c96a8001c29054116038022090400b61440b51400151900c00d03a0051903020b402c080021030840e0448a005c031441650351204a900200c03203240c030480c200c03d0060200010030f0840064034206954100304251031003c2d0840e45400e440c1c2c01e5242c03d5401113401c00005030740c04010003060000c0d130020302441400000c03940d00d001849413200c240800c04202c01d400d01080d00700c0850440201004840020500f00c0b90401105072101c0761100a40b01c084000e03001440b850031314051500c1c01286035800340200f200280126041c000c42641c20244650410b10326001040c1420040f814070090745200307510990b507aa0f00380301c0e641100785004960288226460070180204104455143e040c0394009009081140b00ea11200c1c0314285 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 974689037 1250 974687787 974687797
    0x5061b0102120106051308031204080a0309060c0e1801030302340e01080c010809071e0f09050906090114040b090c03101e15030f0f060504150e0a0203070515 69
    0x10b030305a40b08000500e165101000c1c100e254800d00301d0b12030b03ca07610448503a0742e000e107007440f000480070080810001000ca400520203c2154100865484191b4072000212400802d025020030a00007011f005031800e400c61002c03030300c4080c40f82111541107440080d43c0c2e140c2050740d8081d09452421f160b40c04106042c01001c0408800402d01d90309482d03069482c1104020320800c02e107480341c004000c0103903000b1349420f84680c02e814003e000b13007807502401c41444045415640d00b804610786010905600c00105040a0410b031103000c54241171130250350746020030041820115900d40003c00060000080e4080d03000b80e000052285140c840e040eaa0b804c107080e60001c1b0703a05104100000b1107900b84c0e03801c00c01c484803103210000c401c41c0700300e6039183c01c0c0ca035031489000d0140c0002c40b05000042c02e402285c11064001c503498090100c159a40c1c20031120265030954004510000b0f05400440c5d600540a1080b00303c00500321205003640402d60f5482540901e43c447e800c040d80c1000c82d0109402555 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 974690287 1250 974689037 974689057
    0x19030c0f08041202040b0919020f0f211003030507020405280f05011d0c1612120501141f030b030d0309050c010201090c0e0403020a020406260705061b0102 68
    0x1a580d990350300c000c00301e000302c100c104a0182c0d0034080603801910b072580115104511240000688c20500003007107000394481000c0355607400090081d440084c00d81400381500b03200150541000e1000c08224a040010080c8540c402e80302c0f55206000081c1d10109a481081d4155000b148030388440300040b80403001c020b4902444820340e0100e4030510241d8111004022030341c4400c100907621440d02e1000b0740b02c2e1003425102c200d603500204036151101001014004030854400f070700500d0741e43c1c510410010b0034584400050994000c04154600ba00c81c0a004081e580701290291180c5404107100076600e00c09042200958078070300c01ca450294001011011004054868043d80318202400070025008255142e11441c4814a000d500500c1070024031a00b06042000d0340d0b1030a03c50400c8168000c10440440c010796100d400161110302446010300fa00741c4001c1c0000b20505d8404002c01c84611418006504c419000c1160703443c0c0c98220b450103a001c0f04e00c5030210b051900000d01920482d80f20f2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 974691537 1250 974690287 974690303
    0x706050406020715050601021e2103040605150f01261f0509040c05191517060409030f0e1f0203270a05010c03021f02090a0819030c0f 59
    0x44200320042e401051864071414800402528010014003140c400b10780090242e4022194809a000c11441c0d11510840010844d1070701d40400a21212084848c3c8607103200708000300902c020480140a40c550090000203000c8400030901e00055a080300c1602e414184961800c1c5c0500a0060b404102d281c4803920002d5403560400c3c501c00400c0203005c0c40c141407030648845000c202c0d8902207071414043e98200000403502418401040321020402e000ea1150203d01c50001810814080782e00c1010300054032400140524812000407403000103140c507204500d461301d11400a0382100c800c000c480c150703143c4090f17065500004210b511042c1e41c2100054445241401d0000340d00100502440d20701d1040703c2407185004e29802c0031a1519100d1030792021a200017030082c3d5114000035203c903400792048414412016100411660540034a0b07480d02d50000750003591070070020048001056268000c0c52004c1c149030014000c0041894014100050f1000c1d41c0c0912004c034200f4501c090b045018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 974692787 1250 974691537 974691541
    0xa02060a0e09150f190e090a060903020607030b0607150c090308040e06031e0a08031b0304113118021801091401121101092d0801200a05070605 63
    0x10866490b00c9100082d481001d010540030113600305404003129204080ca06a0416410030b42e2072000c0000040401055205421809000ca082402041460750094000c0d20031410f01c5032004043d5046030802c1800f403502003010400181c54031440c82080c1142080002e04809070f500101c7e190441c3c1c0e0310180c0702c1e03100031801189500d501d10071343d405880110100e0309240c080310902608107031081010324094100069980100720700034000e5600015030310b2a00c900c01000d42d0a080c43d50019203081d40c4080750400c0018050600d510b242c1d441d40081c0c080246006036024405413001004044020016154016a0681010412110040b590080100301d420300b54882c401007404091007403c00301410403840801022102021a050385e42d20b1121101d00c29a036214141d0f0380008003900ca040190214000514450800100303503103443c01441c0c5010350250b443e4070700b0383c0009900000c01c945d150600340903032003850601085203d582210ba89454910600c0291014018450054922410281 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 974694037 1250 974692787 974692801
    0x10b0c0a2a090e160803070602030601030207140a0203010501060203130519050a032004060308040902130e270f0706120921030e070b0301051203070606120201200a02060a0e09 77
    0x40110000c40c0002c41c0c102c02d4000c0c084c81c0c803d03412842616801e402c1000080702003030042e0011580b162042c1005890400c0c17130b527201c1c1520350328190112800d40045043c4400c601d001c0c081c490042205100843c24042801940c900000d421700c1458030401d0b9400a408080e594000340c80020300c0e00400a2401690f2810a0380e15844160090010324101582400700f91406100c0d03071f01602d801100003403e0906040b4441c00960105169100100384444002001103c030110140702e09030314a1400300988260146a000080301502e0540c10303002860124140e07180000d0a100b103580e20700e040c81000300701c00600b0009010354100a0498007104a044d0b00e4105460303d10003030040c039581c040000350341880c0d549446d0308840c0a0b0110814040004015501e0800308c1904094119401e0300d140002c1c680e1020103d03111540303d81a11048002d40405540e08405050000026841031660754203000408584bd40940070000744940d00c00300399407201c80d00c01c940c00c03811100c015259901d141031204e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 974695287 1250 974694037 974694041
    0x61902011e0516090806010b0a111c0905040501030b0a02160501230610020c010e0a09020403060605040b15030403030c030f14011502010204210305190309020306010b0c0a2a09 77
    0x81c0c0c403c0d841000041600b0102c0e200305030207000c5135002c0707010381a5a42001c0c0f10702071990000003271000300181215034495080c400d200790922030190700119002c0b0318041401030000d20b680e40c01140f01b07a1501d0010804074200c140e000340c0c44420424016540e91010703010083c11400d4040c043d11562a03c03810b49039901c140e0038940800e000c049510f150301d0b0346200030800c030198060300c1000141c0110b46503103083e5010380c0801080600042000f4441c50703e4540e403d080703801c264010b40302140c80300400c120f40c0c1428420980c072400d080e10461101000e1040b000c0d070622021300000c040656640010000b0b074402ea004070101c0b601e949090000b08000488908029000c0c007412600381000c030300103010140140300319000c941c5444c0201103114641c1040e88000700e00c449064083c407004202040b0848042400c407040740980d5140051498041e00615103842c0d0160050048038100f003042031002400050b00441d400da00842c6188500f1180e010041c0208100c00c05d5040040804004110701c8515 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 974696537 1250 974695287 974695291
    0x1c140f070f0f02152a0304150518010504030b011208040b0f07140d0207031e0803011509080703081605100c020a0b061e01080a020408030301032906061902011e05 71
    0x2224110040501d180715100c40380320304406481601600c217100122440c0310303402c500c40300203480c09403410299100413880740320554165200016000090307041c84003d80e000b50803070300e80d82840c1444c00c0a041d641e41100d40075060040318081c1880c82180d208010441c801c440242099001043e1500c244884116a507000140116040e20300e02c10501c0300320b00b0015040402c0d07c0c42c0c2c0d008000f10b600d151a08241d2100b61111a868103108180807408200b80c0c0c0b00440c000c0400c6c4035820504d0329205c2d0001c1154020b90000c11458005100c1040400c85000985070904500103480f600448203160051400601408020f412030502d41a070319000e07000b040e260304040c00b031800003c099940f10200000503100e01403000034000c401e0740030880ca500c10384626030321452910006152030780b10710707500b0324540003640304481c000e030205c400c071041e0701c50500100c881c2c100d0302102c04101d0422a0001307045004081100142c48036400100041d24400d4000e901480c3d204030b4880c07111300c244c0d0300c12401f4203c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 974697787 1250 974696537 974696539
    0x9012306030d030e0607200303180d020706050f03220b01050132090a27060e090c2205101406030f0a050402041b090303021c140f070f0f02 61
    0x81c40301c00300000b500034001c0701030400e20400030701401d680300c001c03c0d01c0d03a0b40c205c84480381e03100c070042a04400250403c002c0d030240340c90b80c14150b881151090300e28035103c0c10000b00340441d00255005c009254004c070590360180c0e070050000d0303165520104038401e65400500c01455882c88407406a0034002c421400a0580b1420b0341c0705801d100204903d46400c42a806402c460004030701c262451601942011300307410700004246a84103a030317030071003d40300701440c1c2c08190500407400c00c01490100c1d02d205250003880075202440142c03425072a071540f201c5003107511900629103102c2c0030f030824103c541d44054560103082d00300301c1801c10103503001c42a035590241038100c0303041401a42a9150040559108654024100642d584c92405901c05000d0243c8202e801c192070f00c08891210031290010301103400300340d0b00c14040610311706009181c44440030054240100c10721130415810f520070700081303180040b03160490b074448028003401200c0c460090080c05800282010b0020445688001900030f80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 974699037 1250 974697787 974697793
    0x70b190e0703020a031e02090108010b2b0b2701020903070b340204050c0a0e04111605030c070f060e03060105061602032107050f07120b0901230603 65
    0x10503052140d60340d00070b01020b54040210b4100700001b0b01d0388804403c1300060034107200030a044540c0820356010080e00300320f50594450010140a0608903100502c448403250022400d0110300010070f0b4440d41410003034200140c10780042d01041101001c2d500e04403c0c00d08140d80a02e096525900075044018510300c603001c0d10380c00203452040c200c1529518003850540010203811480c03120100c8102d41b001e03e2004118543c03200140c2d480b442071501c200d0110a0266848080c0d040c000d000d1190b400c0b04038840c5150083c408401d070700020954003441e003c150445880300341410058994094905030304003911820001040010341d12051400b10b500716142c10180d400c02104054440c10240100d98009500b0b11074275005070000580c41d1002030002e4190b6201c0000c0e00301500f1007030f210f1241c1d071307001c020001201c400f013001c10011000c94a8501024103a10f904010f0340064a01c9010700103800e448045004c030b51603003005c0d4800500e44030304008a061202c50f281061035154021100c80c3d100340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 974700287 1250 974699037 974699051
    0x111190801090203010f050603040615090c0e030105090618070f060e01020f07060f0309080909150f040902030604030822060c09090c1e0207030b0f01050f06250206070b19 75
    0x80c2d28001e4034141c8442410344e400d81070070142800000d070001001500c441e0784079450098003804455048010b05003051b0302054100380d190014001c10074000a0074044d80c1f500003007108900010500c0e9030403c00d01000d058410494102e96890200250450b41040203600030000304242c000c005907001030700a03025500006100384000391a48076901ca05004a82503601c0f40c40003a100b58001041617102d01d0500703003008201c501040c031660b8200c400e400405107049600c042c62910a045191038003086900780070401e40d60340800c0d111a0050402802d0091000200707018000c8100c0058151001c03540104440d4003e00b0090041e119040310840481d06440e80840c6401e094011201450b6076a2240e01e45403042e920414104580c0d1107040f0114000d10002000240100d05520b0040e15a0b8044042035410402081000d800440e55548500c0e410015046411204000501a00040b40f03504400030354500100b0014800c001c40246080d203c0740400c2841e80c81038181c40c0b03400345a10401c020710 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 974701537 1250 974700287 974700299
    0x130e0d050a210f0f0507020f0a0203120315031c1e0c1515140a05010f09030b040204061d090607080108150603120f0304060c1803020d050111190801 65
    0xd032150440800000e95210300081c061900066042a848003040000420540340c46040044540303949103400500d4a580a04c61115030402c03005c1c420f4500d0101031b02c80300340140e000950342c0b84080c078950364940003c000603540160194610b00b480350007406441c40000c0c00f07041c44a060400b80d00f00000f04088406e5600040b021005505407103a50f5142e80038051201d807104082c40340303940445a03a181d119999070b801038181000900040000140194649440104210303140702c3e907411450410600c10a0504625402200c04084a4000010b54215215800854041c10154006902180341640c00c000d0843c061100e103481505c141041d40c00b2a101d104089840000030300ca10603c0b41c0c010300c241401401c810070400d40050005003102d01a14541081c0c00041d0004d0140125844021003000240050b030300852420f205580b03002c3d210002c0400d200100d41d580e42c000a402600724003941010820254800b02901d164540815140c0030680f02c145255550403200400203103040f40000741c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 974702787 1250 974701537 974701547
    0xa0e07082b0f0c0f050f0d1e020606010c0501140403080a0c0914061605070801091e150e1e030306031915050601050f070c05040e16060f0302040302130e0d 68
    0x1405020b42c0d903154405100b03081201e40300000c910a40700c1c2d03110007070300100240003005404640c03442403002d49031800041d100945040b140021106c125048100003400304d41c1d0115030319034401c409081141080307000b4149140181402100303030340420b032000d040c8000d06420900052042c000608244a500c80600c402c5640c010709200b940138002e03440c1c038402e481e884d140303000d131480c0440024503070601c40494440e18070b040a181e00001660755220b90920900092031441c1120600d1015410800d41e210f6440b0103881d0080d0418070b40207a6110258a080340c030030b200110940c0c0d007008101c400103042d0b420742c0d501ca500981e0441c3c400d1041600c44820248200c0805e07044c25003100c0729818501034680c00c0d40c042e20004000c41e04010041010000d041c0c40d52001d480101d0043c0e412000c00c500b00360512045454103403101c0904e0740f203402051550b0a15020810550740c89291807038001c1710140040c0c02038095500700a5001d02c110618122007503056201d00c04a1034101d0440751608819007090311 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 974704037 1250 974702787 974702863
    0x2030702090c1c1a010801080d09051504080307030e0f150403081812010204061701050d03031a0d080d05060f03060c0c100612021212040e0a0e0708 65
    0x900440541c1c0002c0449a000c000343c2203103404005040e805003050701071902224403520300449512104803a0f1009541c0c0202d6040c054101c48005040c0280e4582d001342c11020342d031103039a102c1c20f078000305620940c1900e800d0b18007d12200c012aa01d8032150b10f0301808400181000d24011051000d000e150361a00c0340700944d150802101d494a400c0c11901c0b00350642c0d01c100d01c65528412200c122410341d468984403c027208907035100050b1900c2c1400f90041c041522400302d4054001c200b00180000c0d6618940250904e42c1404c001035680340301044400000400c103040396122a450302c0c400140201c10004110741403045804010903a00c80041191010100c003413a0380661103d00010951070382e5400074103460203800112212050140d0144042d901d01c2d80000341015083d00142d011400c10441c00c25003080030f040a0011a01c0d06025116107001d20300c5066489203002001c110540032551003048800c1030003045d12485610794800950710b41e803003d400d40e010300088005c100c40101e00003203c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 974705287 1250 974704037 974704039
    0x206010e13080d231303121b050706111201080c090717060d151d01060b12070c1b033c0c0b120708010b09010c08030a0e0a060615030e120c0708010f1a0102030702 71
    0xe400508c8039412660b5070400c200031501241d65120030080c620500c0003400b4a8801c80c0769170766056052019050910700b03207000310b50041c0e031032070705006150341c21040c1d540681a1055130405070b42c0d07501002803500401070802030700c0c81407101c482c0800101e140d04078600f01c02210b171042c0c1d503007411441c1e014200c0390148a0480740c804280848005024101d041580014032894840c40007102900d4111015925500345852844400c400b00200f100c1400c4044400000342c0c0f5400c640c0c4081c03c9850740302c0e10603241c0f09450000300b0385058104005880008058140540004e40340d850311513004207008001e0710a80c0101d520800001500c0d0302d440111411040107940307050725030702c46655884943e04003500211400d03840e04101c8000700c034100103404407a80103402c08200d651529038002c0d1414020b00d050010181011100c80d0024000900e03d40002d02c0d92074981c0c0d803203421032285828101036410140b000c0d428190100a8a4569001000d10302550310044408650410059070780f0301c80c10300c000b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 974706537 1250 974705287 974705321
    0xe0916230114070b071202030703020918040201090306050705070f0501020a03180f08181e0406050406080a02060a0c080a03050603074407060206010e13080d23130312 73
    0xc0001514104a00b900302e680c1b800c14802c11480c411141050760022035940c80000d030b0100d0f01c0d40b0589041c404500305170301c000c807650302103081c141c0000b0728840035404054140781c0c4034400b14005070300c100c0803070324a1504940d540502c0c1c821450014041d60100c014600040c5c2000003034044100d0030840c2046243d80045404a51201da40d01e102142d0860a4651900a095800000d450b00c440380b00d00c0301402008868081403c0e614100400c031410b581019000381c2c40c00d0400e0008110006100c0b1071660111180c580ba807400080486860214060040400102040815040e6015006240200021800d8840f115250780030001100620400a4040203129002903580764611901d49401036a92045248103410000054a020b80e65804040160300500042004c00e01d0808800d4001001441c208412040da403030300792070740c003407002104066a500c443c04c0d03429105034070043e00c020586040b004035525002e07249158000f81c40c00c055012403941103184e01c5000480c426241c0140c00d0b8040d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 974707787 1250 974706537 974706547
    0x4090b06120c0102250b0307020f1515130f0612050709020703050307030504050708031812010212060105130f030605090d0e0a1202130e01020304020109120308010e0916230114 77
    0xe1402c4403003484c014000c904400c45c20208520710340c0300c0110b11410150f0010700b850840420b030381c1d241070501c8c2104840c0d503290758107014008640500e08060301d002203600414441c40030340e010000b44101003010300e11702d1074003100051740c00b080302403403029a00802c240d0b0100366032102d0030000d13807041c1e03040100029810400a1120780c081c5d40181d410601402c12100c000e034407500700d185154480c0d91403c0d030034540310025095915146a80e03003441002c020082d414840ca4480350f003800d4501404003070503c00e000c943e0380c0b003020842c802100101307428629800f0240c0c0d28103021004190984440341c40d40200e605507030030309004600c1d8094803d0702030f108115481ca003070882c1503156a0954204e0380020000224410200c090141d003010840010005a0381e0510388005009025198407129a0840d42004800801c2e080550360741103500050780c1c0c0e00c190380c40c180003d0601510390003414980300f441ca0042281114054003002c200c0203141c003100040850401541c001030300315000c0d02c4031b03082040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 974709037 1250 974707787 974707813
    0x10806150d06020d050903090f010e10230d150b090a03144303051203060a090207052a03120f0910210b060a1d04090b06120c0102 57
    0x188a4500760041200500749000388640c0b01c1540c0c401d0301e40207240d07803005c60740c01c419203032800320041e0001c003d09000c2508a00140829001c95486149009114400c0c82404400402c3c16581194a42981c0e0312650b034040c0500c030300010001619080a40d0082d1314000c6205007203003040b5211010014032038050640ba6030b6035a40e80f10261403686a5130302803168050002c081d00d00f0320303030904490850410103d44540c202c0c5c4082484040381c4507504091448201301107900803c1c8850745c01d1802410b0741d500d41e20340c00410f910a11941c8071402e075600c0050594240308010072903a41c403090504410743c05c0300c0300c014a800c3d8101d15000c0d83c1e171305801c04030280101078040d40c0140310340c21044071007604010618001648201c010240a00820000c920712122981400000b00c031505500c54100020090b5101046060041c040007004bc48030407204a0030400882d20011164030000304184503402c07140c500a8400007082d42c109004000181007510206004507040500b0041a0300400100c6c3c0c81d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 974710287 1250 974709037 974709049
    0x2040e070b0d0b030d1b120903120201020d05070306060e091b03010b0c120304030c0209060a03140a05011404020d02060d0e03070f110d1101050f040e09070e01080615 73
    0x14005121841204000911440d11601520040403a50070000b401c1e8a164203060810301c140218004206d6107101903840132040041080a40390000402c000c1c2e10070600c41034440101680000c0c060a0102c107041c60310640c150018426000e82036414400340c0c4031740f44142d09403662405050041201e66258200d58140391000b10780c015405898041080800e5100c2e084030350080c2c004c0c94041c02c0008807501b003882c0410820200b040d980301c1161662030580c500402803013082500078496004074000c69515540c0c0c80001000d507800c103143c400e007020f14052596490800d00001c868030750034043c3c3c20301c5503281804094400c0781c010b092002060161380c00c000456018609801505544994000e00440e041010b000d8291082203070300f00f0fa0f4040c4c18000e51000ca40c41845101d80305000071000094459061003448003002e081c00c0e61241021000e070750642c042e40d042148600b00d05001c010401c800000d2060840300000d0b800700b1240d884411140d15440111940e01c45480d0702e18617a85141800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 974711537 1250 974710287 974710301
    0x20604031d04061505090a0b040524090a0e1506040e01152006040b1f0603050726070809060c090d0c090c0309050c010c0f20060309010504030f0f0c0204 67
    0x10400600913494004003400f59024150540006030086103420a90030a001500d001e8070f9a444010704082c43c3c280002c04021855070030030001400003464840d40d84625084c0c801d0350000a1565613080e03211071000c01e545070121111207000074180e03000091420200100c0e41070360600300f541381050303082c1041c03d074a05210040050411058642c0f0f05410908104182040314404016000f2810035003014194104040d000614620030100011051003050607582d00310358450802140e255030b0402c09441c1d0781200003800d0311032206000030f401d82204a1401c0c91242c801074403140d0030354844580c0c450b60303038000b22000004040204229415442c085510750140d620681469401d0f030740f118000b8003540d51001100700030985800b411400c00100340001c000401302803800707e80080301c40d01c42c910310516902c0050241e911100e2408401002a071050003a498058286079483c10714111850081400720340513800030f1400c1d91034150040c482e54a241c11110700e0741d14055a80c650345c081000600e41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 974712787 1250 974711537 974711539
    0x5010e060d0c0c120203130f06080a0b210319050901080112020301110c030c0106152102120f04050106091103010902031009060807060806030c010503040f0317040c080c01020604031d 80
    0x12020356000604d2422802c0060794450f8050340c1c9a00a8001d80003202805030070507a90752460740c5050201c56401406554003132103080b004100400b0300008294244802100700c0c2200300306082404112100000170480d00c00715420115070550605400c64160060300136071400188848010881d181d00200039554040c0001c000082052000309042e080758800000324100da00b001c40d035004061020321401c002060f82130700d40a4820170001000380002e01c0c010b0b800204041d8812603004000d4160b054030f140e244804640d40450601019420941e04129022030740e07507092000100700d40c08036009025400c02d40139640c1d41141d00344440440690401410001010708030703c000a101038050140d0401040c9007005801d00e60b042203402030000368028800f034001d610000d500d903c2a640001120fa015070001c0c0386202504951030101d6040c40480005440035440310b0521003809201101c0c4002c8481742011542d913442d1800059840f4001203a010300811051707207032880f851099043c45100d20324 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 974714037 1250 974712787 974712797
    0x31e0c060c031210051906201e011e06140906030c15031f0b040303030b010909090b0a14060102060601081003170307020706090b070609151b0905010e060d0c 69
    0x1c003c1c00700c0c8907021402c40e2200014455498200401e0501031800c0038130100e02c00741d1030b182c6814080003410380340c010303400705904c0340011448401c00d0b030050028900c45a00a542c50000741c81100c5c0e11406002043d031180c00d0503100c811001301c4000588540c0741107403502c1c0a103114203052401003101411005000907094058500d800d03007656505522001c021740788044480e141e0820f0701042440c080c8c0d00003900111000360038144803c000c281c0641e8110b85d414603010408950b46001214840155404550300c030382441c600404110500c140e541c40341c01404020030860100e8091503031030780c030300b07440c05c0d405604048049441c40d4030407200c07168001d66840040100f1a905d80d200c001e901001410f042070508040b05100d45650305200140090400d0b1402da4102400c14001d1b9100344501e00d001001240e0300c0354040e0401c0080c03403044601d6100d15408111540712200f190403940304090119000541c0a0008151580140c81d00e140758040686104d0801c4082181c48004004407005402409 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 974715287 1250 974714037 974714047
    0xc150209030f01050103120c0b06060a1e0507060f0507050d0905030c07230a03170c1c0e04140c090f030c0d120f020d1205130507080705031e0c060c03 66
    0xa2810002d0311444082e0b000002525803444c1000d440112104100c2010880000380c0000401c3c04150305136017200d022070b03610750b5880d6038180035605e40d940318850000701a80f95500d0001d03590854003600786240180b00034086d0740c51030030740134084880888150700410000e0112508001266004030410b80c81076089074500003e010803540f030181e0b66401450700e90382d1000e80c00e0200340c0c00c1c503100050300030603030b440e00c4580e0455035000d84040b241c0280048610001c1303810030070a0b0003000041040302e01503180b000d81c0c1c820040002e01e41d0b003000d0304850290303081003c44500800d4680d034480c03280020101d0a820725461204100c50007991412441d0300d8410003103115404c1d901c0d82d4484444900c01c1203030007001d6042000141140271002042c0f820340d0001805e984442d500100c800c1c8509017422000a010380d00c440c1d0411003a40115005421403250300404030b150007002651600369a021001c94511050141201c1c9803400100409540754005001e81c48443c10240060040c80e1100001d83e070a007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 974716537 1250 974715287 974715289
    0x5191b06170711030315010e030105011d130c06090602060906060f04020a051e040e0f010605031501021c0302041809050a02192103080f100501081b040f05011e0c150209 74
    0x680084d101b540c0c10440c1441c2c140480e60300810301c0c501d000c5003a0020b0000e50f02d4007400742182210b032014824150850300006544038000c140006805034041e10040c41c9a489200003840400035004100152140202041d68608006401446204010440c0d1000c16618080c48042c0d0040480402848428007544246180c5042900e003081c00c0d80e60515211032034108540382822000c0d09803d8003072200001405000e40c0700003220b07442207601480c040c40214580040313281850280488202d800481c0c03009900581c10740041040b40c41c00c0400c2c1203d8113005d04014212114008000c1c000d9000c410001e00500f4441c003408241d44000300c103a003110b03550b0015200c5850080704007000e01c201881d01d0808058000501c20740084409600c800c0c1c501d81784600c2000740c103282c0034407414009800005104403402000c20710540404120749516255104000e10640f04180109408102014580e030305078440c0c41a0360700c821080d0349d01d01c190b40c8680e403070b48548041c040c0f280c5600250204003446072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 974717787 1250 974716537 974716543
    0x9060705090102101e1104030b060d02061606090c09060f030209070215131a010e060d0816031806140304030315050a03050c010f05040b04180905191b06170711 70
    0x1e1101132417a40031400d14903000030845031040c03464500400184424400706050720381c52a03000e402039903041c01c00e10080c00015500c3c000c0c1d00418070b4104080d8400d9081202c150004890303244503080890341140c0b071750803540550782d00340112501640c80d050208094509482d01c2c0d80c003e145401a1041c00309203403600380710301c14110b4410b043c403e9107045100c2040003101c1e54514050328040d13517401c2ca50500c12034164900020702600e128503910003c043c24010071004599150300d20a059012440d03c82c900909607070040c2855503d510f0450300d0006900c0d0040a144101d48515148245151f0741c580d425401080c281410b01100000d034040030034207807501d0b40c229000d14051002802d14030381d070100050611103282c4030803042280911040142003046010b03501620300074280c51442c401011003420090500503c09029480f0b054000e454a00c12220200e26460142c00c161600e015007071200b1404130044e1081c1c00c0084da8100d91100e0407458010110303000000d40c5481c407400c0c0c1c07100b54054070b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 974719037 1250 974717787 974717801
    0x2030d020d081b040308070201090e100302031c0203030c03040c0b0301060c110f3a06140106110607110307020a0905091009110f0a08100f0b0301050906070509010210 73
    0x964802800031220542005290750f20030b002183c403c9841d00001181d211a00491100400f10351020030440216070041031000f010388202d0180102d20f2502081040e10350b50740348001c0e40207010f1206d5004400d81d024422009c8455107400031482e50304c482e274a0111030b500c000e000340e4030f0303480134a40460042d010303900440c020900343d0340f403114100003070409215540c80c0c486044d1059803031403203914081e26600200030640d96400b1200f61080307008461034030f0301820395501c4004882104000000c00400da8045051440d040071034403030710383e21010182d805500070340761071080b036000c2d50006100e1803155121240b0110355109880c00c1c0030040d80820b40004083d084400700585800402122420070172000005590350181030204021030b442c1c00e0341d41c00488840c03034000c120806428400d602d40d00651402810741c1411100110310600d2554010000e4900c00c000d40d40c14551149500d207070500416019001640280c80c403625040e900790355603480341c10400d041d401401100303000c4810700d124110b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 974720287 1250 974719037 974719063
    0x131401021c0c140a03020f040306020a0e150d1104030203190209090d0827030408070306050705070519110a06080f130803010e06010e3102190c020d0203 67
    0x35899001624225000c40d07024078032004440e290a80d0388032120f42c045942c804444009590310380c0d4a2400e001100a446000003601040301c0000d400403c122107580245104641541c50780a45651581044024900150305020410061040c4400500c2c80c1e400000718450121209240960300c1d800b0034244081c90004210b00c1c40004418800d40c103003d08513070384c0301840074081c00840314091800b400444c400740c131951009654191305643e008c4002d14100501c0e11020482e41c0f03503682d481c1001d82d02c5034640000c03921282000046410310b8012400d540b242a400400f0340700d407880c41c1c112423980d80e4a0b03000a40e101584038204a10300d86590310322001500403a139030230000e403620b90480c40030450f000e02107440600800e101940458808002d90b03042d01c00d00c1d40d06a2281e140c00300102e60070780000e60901c1c0d1083c55401c200030000402040c10380f01191011030004110804a0448220b0160003904964038144400b0b5107136140c412a070745000c1c14801481c40700414040c2d00460f1500020803210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 974721537 1250 974720287 974720291
    0x9040b0d030503100605031306050915040c090b0a03120e2e081b07030f02030d0c350705090409050f030c1c090b030c0d0e0303190207020a030209131401 67
    0x10000001300d0794003e50180c00a814100d01e18200b40034200c0b101000e00801034101e981d01d0001c039100c00c1d014000714410b0040358012034820b041604107031070f074580c0501c0b4042c240c92402c0d00200140c00d0828142e0112900140000d6450804843c166121001503051a41c4105804281d55485001c0b45444402d00742c81410f411041c442000302804000c0050040e07641c4c2a00403110910f0610403600321010654907140500d89903100c1607041e03155010f1707481132081050904c024013a01c95480b181c42c40c02c640d2400312a80c0d00b0707202004040d4001d175150742c25600d00100c803400a96468003450090071025000b400005114101d0745803503050081e0f801002c07810382c000240f007625070b4100f0054000850a002910090340c031041c000504110b00130b01c5004d03810000030000401000440060304d01d145441c040600c03030b008074104001d840e0b0b442102d540c2e00245120559403030b04082803099a061a6000e08100f142c5811074081015030038004068032440411f07040c42c1d0300000d84080d50078203541540400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 974722787 1250 974721537 974721541
    0x2090406180318060311071118090307021005161101020f1501030b0c030c070b1e04030905030f24060301020c10020a300c1808030405030f06070507030509040b0d030503 74
    0x403c0303018154090030401d0f0902c090450714040030f004a89480e5405003401014134100c034045002202c0c54004107a21102d0582000081c0001100406480748212142c100c10103030030405403a2401803c100c1828001c080100c6000030340c4825815000721414011141840c81e46030846141c00d09404000f200107071030030010410084a01c0040d604085910380c3c09065280c040200440748c005d500c805450021000c001c1511650074200e900b400451801c041d405919080c10064800b44283c40303040c1c0039114100405411040c041500001c1c0041003a0028540644c4407400803540c402800c15030345954200a45540c82004000c1c4d8984603103081405600e3f6181680d0250502100307501060090088802001c880d0f0011036030175001c1c110543d0300103017501d5002c40899208880c02d1205442487d8003401155049000001d0400c030b41d8110100c612501c0c1071150240c03910002d907540d001140c0c05000e0000020300401c09899104400750000445c14041e100003403950401040a134086800002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 974724037 1250 974722787 974722817
    0x1e05040e0a050402012a0206030a05090c0f06072301020c06181513030908030c150c0703080408031b0d0903030b040b031f020702041d06010608060904020904061803 72
    0xc40380d070207030105030208080e19241e00007800990460000c84e001c04c01d4400c03500e1411245000381400507402800320b42c0c4030300d40260b840340184000d603070314240380c1701d0901818118a0840e01d060b0111202514190802c10a652a07080c0d02c00406d4410300b5100f2000e44200920200b407000c0e207040c620b15002044103090400100e100d0300c0c08800111119085031f6803a034504564101120b8010344081c03204403940c07619040032607012100303400c18043c5000002e2124060180000e000248440c20a100400740d202c400311601380b4403d07080020041020400040c0219150314082c5078440c421583c40f50380a990300e5010350172a4028901b803c4281da031003c101080c144e00d481690500e11b4150703010010b0b0940c0d400080d035500c04a0701040684034800700d107100310440c5d0360140e03080310364003400c20300c84040140601043d40da0245640341103032003210000610a0301c10980c4034010351000d4558a10340c1c8460302400b1040300e005006131203481d200c981003401c0c0d803584031290b11a07a000380d07140003a8204d811 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 974725287 1250 974724037 974724059
    0x41a0a1802190839090d1a150a1214240421020606040b03120d1a0604031502033301110d02070b0901030b0a06110705060c0d030c1e0504 60
    0x11865542c20500d01940009101c18051484c86803803020b411516592110001a00640741080003410480d14402c001d0303080340d403503801a025070008045071200d0300441040c0301008529204581501c5841c1e07900c80045114010380303054402141b401d4662481c0d11702c0740070009124000050100250040400003808243c0741c1d90881c0c20400510200b244041a00095540a0141c6928810b1f9640c0c904540306036400c0150341e0704112520760960b228400d00d540e1400a1031441143c16001d5800300d1800840d140800444007aa03500c55000e4050902601d0700c06c0082d0001804080441030051a95114401d0111109022030500c84440700000000000502038801200000950b0344800361580d261600455144195900380b0f105c02e44071841d1500407009002780590061300400002d0022884580c402074600000c1c10b01021960034599410612205109542c01c02001e45c00500300200d02903c280c0007480a588589080c1e402c0d82459810b00d101c1c1407402c1c0c60900403440000b41007000a0b125 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 974726537 1250 974725287 974725321
    0xc03022809091110110f030301050405071106070c06020912010c181d0408040b030711071202090403050304050c04110904060807030f1b090911041a0a18021908 70
    0x1c04060142d1000d695404400400c0107803100e10820079a00c01c04601313031003450201c4610300c0714400c0781c08506145000c0b5403170f40d0003070007803030f0046040c10001010140202c62100348017403800001d041c01da44c1c0e100700720342000009030225400d035000c1240740b105a4407120450b22400124000084141410310040c043c10038610305c0c00300d0b90744020b90030810703510440703083d451071101d003941501c85940e60702d401452031080703401042003405c0c0401802055035202e40c62408040c0107070704955890f6110903d0441a0603403243c0258000d0095000400084c0310b0780103940c00c00d110700100c4410480b800001401c0e41c04240c1208906400440c007044145442c4c0250030007020814003814900b030658a07075005500741090068000190b090804001c0320300110380b07000401a548003001034a40902c8c022a4034183d8400032807091b07080c41f60822400444825540c48a4401004510014078203080711400710100b40521290590034021443c11450740501d40f03074003413003031b94800410f0301d402507030001e0744047c4d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 974727787 1250 974726537 974726549
    0x30305010e0a050c16021207060306060f0302030f131112030d1103090705090601110a0803011518060f0207051c0c0807030f06020711030f0d140901090504090c030228 73
    0x241010310240c134030024201d407109030380c0303481c500700150f058000319912030070004195a1500c00d000000842560661056065030600d5459040031005c03003104400340d00003038615000703641d4000c0205403103200420300c0c0d9160354441d801d1020303032201e520f00142e011480345210340001d0704005000e001d4002d02c2d05c107129003a05111030300b5040d814000c2842d40d9840440c0141800b400400002c00e006072300804d10044580415012603221070728500d842e41c03030b0350801c1c42508020041c1c59070303c000311806914240c4528003440403503044189012400c9034407164803204d400540c000c42e68049066103c2350100e41e8104905288001001d01da884c080341d184040d1740c0407001d42d800c002c00a000049401c03003c0b90115400100141e1140c00905041400c0400340146582c54810301c8800e886115002c1054008140c06866000c00d034110000c4860440c030400b500140040d504210510040c82e06a000804c014040e1600da80351035181d6012925820500105014040d1048400d0100346240c03e0841c002d008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 974729037 1250 974727787 974727791
    0x6070f020a050a08210106120b0406050f1306090c08040c050607030909091a070c03110d09050402030a1503150509030913020d0f110714070515031003060603030305010e0a 75
    0x820307910341c50f0b101d0321241d070000c0c4400c0b0000b45003100c000898405243c48004080d150040f56516071000d0318804202039000143c0381403494028051a203072280000321040501038181230800601002600b0240c04011004140d81b01c801186103441392046036110069031f210045a8102820720391795035112603104601c0b8001c100082c07000a40e0081803581200c1144d1004103018505107803040c3c2d035900007407106811460a50810031a00c1e400218840486d01a40f200001e414450300f00c1c54844130580310010103d62034001c2006142099801198001521030000800520302604031088060319841511880789006011241c22a11710410350044160402146800f40003008550304080c52180480a240d000c180c1078a0307100140c104041da20101e440400403400c0014400080d80c03c26403050728155000303005194444400644002070f40d2006289888103030240594600541c002050303000c0310410000000002003c41c080c03240594403e85021610b07604010600500b84401004020464 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 974730287 1250 974729037 974729053
    0x801150503030301033f0302070b150619050903060711060108070812090d02101e03110f070f0c08062211100507081605010b01140a200102070506070f02 67
    0x81c1c08008503070300c03403500c0540700e090a141180311451130703000d00e20f00701541c0b520048000b090707031f98594020b1410034410401c0d604c4030b803558620101d030301d000c041040740c024008100c01c0c64a00300a2a6610240f03460b450000c4c90b010150010a05240c025a803c038041060280c4040d0b86034414032106d405080320a00038100d0504d007404050f59640383c0c06480e209804001101c05c0c041d150320382505400d90300036150150b280034510008259400701082c2c10075106c54a00c40200c1c007072284c0900c142c0d000701200300328100201103200718001d41c8404401c4600408030182c81d400140c0c01c0f50880018801c1d20b000d00308c6072034202e4507241c03007001d40c10502c4150f016866105000940460b04032450a40070b0743c039084000040041070756144185180a000d2040100701c0c00d03840b0100c68000120b5611450091081c0201100107451004490891010400c018013034841c8092280003017111000080400d0315801008050541c22680011019651034000c0070803c0000c41e0801321014818a0902c0100a04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 974731537 1250 974730287 974730293
    0xb1204050c010807081f03061404061b0504380306031b3019060b01140708030601030209091501140301081e030f19170606090108041506080115050303030103 69
    0x3241c1c000340030000018190211462400d030f5510082c01841d23000e1070800c1007400103203108410640840b070403101c003400e0555a8030041c40105c3d0807101c8410030340710542414149403140a40030a03814044810105001988141d0140440f0501402c15800b0915550741002d40070325007006000d841030054100c101a0850084c0c4581150703800d03481c4007055110b82200c21107150441c0342c44412000302288203100103014840248034500443d140b0420781005015000360040d503880901207150080940203001000c00b10b0500402558005c00500d401440c0c46c0c1e61400103070320700c6411b44403203605c1040d00390f03182d416580001c6000d6640004101a50031036144c50001c030b82d6030a00540c00701c0e02c05d0b21403e02190011080003a00c0082401c03e0f50680c845401c2d010034009070001c05c100000041e49025038042d45614005031b54000d40340a01800e03d401c00b0500107481000003d003045480710001d01101c0c03011400ca1042c800a403440e04004130300e0400203401241d1014a641016100e034104000403c00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 974732787 1250 974731537 974731547
    0x60804030929031801050c12010e061f03090c0e0609060a0b030c0c070305070e100b031009050402011205240f0d0311031c0204051e0306040602130b1204050c010807 72
    0x1c040c0c008012150349695107542604c918803090b907401c0d120b40c01d02c020301813000c0248014141d10045031401d414680e99403000802c0403401694104d801100500260715000010b4503210079012030f0381404110003405039200b484192296200010f5801681d050018a1a00800e441d40003c0d0403500200d0071410b0405d100d52911005e030144c0c1c1000c030002800304100000340302003001507820005035898140d035148844542c0c2801c84801c0c440402940c00841e45030082e0090300e00900080c045048600d0901005000030f00c0003500581c1800150711248510075454001c1d64031440d420031424a84a03400121032200b00000202503100f281180c5844007076403603040000721a15050302d028082c00c0003c6000c94150f100c2c49100d0b18201d4124409030740b0080e00e0b50001c1044801c00e0f103940301c01d1140030081465281940f498503a00d134210602160214085070007410941d0720565003694107581d41c10018007213a0000704086074459019041100348001402845084442030a0001107482e102200402c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 974734037 1250 974732787 974732849
    0x1150f02010e0d0e03010902030f1510031101050d0b09090106150207141c0209090c180c0a0e0301060506070f0b250c05150109090b06060c15040206130608040309 71
    0xf0015002c281c0c09099401f500300d42059500901941c0425400e040c01035110300c44420301d100e410364103a001c070345901018901001203942042d40840c10006020044410380d1090030a05600c9840b288403050359500c80f10103a000d030085d40000030350a86080c1000750a01d481881c10380070f6400503e0104000100f0482a0101b0303042201c804000040a804e03c500780d000c4048003a41103003841c6c040045280000441c0110000222503611102255010983c1c60035821258803803088801c0c0f0055a8a502400c002901c0c2ca10060002c914951510049a00d5400c248030958207480d01c00e0f032080030b01c03143e0907840d40c0201f40c5040d560324071303000c45802010101301c048112081103292410407040c070100b072041030001d06040460f0300180d651100f00c48090025640300380c80302415840400e0307840c9810421206101e00c40d00103028026881e2030507550762503000304142c0e040842045502200c1e10348600c0720010381302c181c4034421581002d0400030698104d80e00301a410266040f5104803e05030842956 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 974735287 1250 974734037 974734063
    0xe010b2a0c130f111314130e07150302180d0c0b0a05120a020405010219020a170a050d050a020f030903030702090a090c0303030f0f270507030b01150f02010e 69
    0xb070b0841044020307407006040141580b0b02007031405015080d5100c3c1900206850510384482d4084e0b00d40f186114101912038000c0240d00411118403a1a03444250f000400c180710100183d0f41c1d05a07803888140d8800555100c00000a54000b91121820350200b03412660900252840c40303c84840b55114001180180540c13100281c002c2542510648514101c0d0301c04c403e0f0380031a502500f40b5a90360b4000c0d420901034240540a03080b400210a1540c00c032280038140c004151900103032800f444e012400341520403522003030203200a0200403400400401a280740320307a66141c2e4480017020021700b0000b44e0300304070020b5007003041240203a58000081d5404141c04566030381c05a15040030000050060f1078004100c40710b100360000c14160542e02c1551170911900c03080c00b01020f80c0800f0030807220045000e0002c10031a4000d000e0641c0074106d2070502074030403406c80700025101e4444604108090788960080070344000e071a809564000c040301c4914880740000c1c4982d800301c480b0a92140d100381114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 974736537 1250 974735287 974735299
    0xb0907120f05040f061e180308070305040f02090a06090e03030f06090108060403050d0e0a0b07030b0f060301030f050c0316030213110a0e060d09060501030b0903030c0a0e04060e010b2a0c 82
    0x3a1503c0004500043c856a8400d0740800c00765280c0901b451004600f87c0080d03000c1215100001c440e9402030281c20703c0340ba030051b04103c00681c40e0342005005031008d807826110680d12040414003001510a001055030b12100030360312480c280002030f8100310002e00c2c06004154010042109000c00165150015818201540ca842c90500303c0350082c81c1034a061074080c8035480d400010310480004207401040703243d41c03d001c040704e46020f111950f11184010b81e08200b08000400124049588510b006482901078400300d028441c0000d00c2c00000309000c1c4413140d0048003c00071441d1201640c0503409003080140102d18a1031041d1049000702c94505040c8080a08507441c00d96804049440f02882c07242c080204a070641469401818240001c5442c3c172101000700b0010303c0000181d03440382080440c150725100054408940074403500c010540c0198841c94085024094003a01c036002e0038081000c01d442c0c0801320019440844008003008100da40d40d44000d07185100410509021607065540c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 974737787 1250 974736537 974736551
    0xf0109030f110c090112050c030607020d0503151818010c1d0a032405060f0a031709090708040b070c050c2107090b03100b03030304060e010b0907120f05040f06 70
    0xb450820800800740d50b03001d2005000030807052104241d9190440c010b000715413001c98800141523540100b96000c0001d40d00200022950510604c0107592180300d21800440800f803d60104103245c000d10400700100b501081000030b10081c24801c440c14060890080c4501c02c0120700251010300010591302d00840003104110280c5c6681c40280c0085078425540301d1250301c00c0c0c0c1080c211450f1441020310381414040490705900d800030003c0b10001e8010b080400552440c1c1c2c802e583d02540751400d11001d5000e1204480540d50113228a209514039182c54249241a14003690300b003400a02400a000c03001d00d041010403400103080c040c8a10548480c1304c0f54a0b0000c1001105034902c4d24008280b050f800c01084410340b980045500600580031921800203480c502c400340c4e98603580311038055109000041c04140d494005d01c089010640002482004103400b0656040c012540400410024040004505014030800d841e2204811041125003016650b5043c100d0300ca040207070141e519804 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 974739037 1250 974737787 974737817
    0xc05040f14070e0a05010c02060a0e031c0201050f250503130227060d030e040f0e15071202070503070f110d2105120a091104020f0c0f0109030f 63
    0x70024a84400321510024a0319000200428214000c201c03240191440100041c15500a00b10f000180d44d0003800c060508440ca08101c1d081d02e50809101d81c188a8501040090140c0c000b09008440007680085400e10700f8954003549010081c4c041500070101d13020b00000c4032041370030028820060b00d44955603440794852042c605d4190000a544018900b01c5c0004030640070100000b65001ca91940c0c99070394544080003200c901d0b8441c058081440d09600c02c1851401c1d5000c4d01941c003543c44001541c0c2c09005a05143c008125641c10f40c0303c034040244514150411600b24054440c2d000a61070000c540d600c168590203010720082c0382403003901e01380702048503141100c0b030b81d0b10000d01400805801c5042c00901e84c245881d0700c0100da0703000d40075144480d00c20b000311420104002c00144032070b1513603900c180040c15280d4050350240300c40903207103500b650389000502510410130030094130791030014109400c00352a64607009042e803600080344002600310f0f2030740c81d0903001404c0405414026030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 974740287 1250 974739037 974739041
    0x270b120a140c0a1409150307030b09070e011e14011215080d0504060e03070302010e061b06011214010c0905060d060902040603020c1c1e050c0f0f190c05040f 69
    0xc4600ba910003908240402c4d0000e1044203404003d02c1100e542d0300341d85070051a44c40c0041040f40321509074010301418030200310b00000701c2d83c2150a8800720384c0442d59654011102c01d0702070b081402c40003c0910704420740090100300070302520441c1c254a905104641c000303040e40a48040c260281520b484043c1030131200381151000800f10f4400751003904800c031600600030f501901a240c0400c000340105899410005081c90a480e41a1280030340a0034800421003550080d16900100741d0440003903090544d41400314034001e0403030307050040f6500c10074906070035003542144104006030b140c02101c0714115402900001114400d0b00c2240c1d807240128201b03000b8140681050041600004002915075403690007000301c9030041054401101b032958a5607030004030100340500040021551036203410a040012401c03807441d0610710710b410450780246092500d030700500c4034075400482148810302810703c001401c40000380440d00b800c4c0841c0e030300e0540510f00c600170b040c02250f480d00161003a16280d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 974741537 1250 974740287 974740303
    0xe010801082503020a0f031b141201020c0a1101110102070b0703051308030c1308030a08011403010209040509031e0c0601091d151006111015270b120a14 67
    0xb914200380c00e9251840c400c000a014481156001b5230200344880111070518854251801e280c0a03c206402890420580c00045c0030b009000d55401c001c840030914007000001180d500c2803141540265101d00050017030130485881c0d0755280d0041100c2c400064605608550080355814001a0364441484165000b009410003c1c0741a0000040c007a00b802444080c0404582c481c0449620648441d803268803406980c082d800841d6500c0c0060001600d18080000000e41c041c00050070500360000140607100142c0b4401030f0760b00001025902110300800c804003210380402c0180c41e00c6c60321080c055642c80140300c5c1c1524143e4a407100048000746000d10300f210f46a41c4200c03581500488640d20b591042916000d1030310a0303036a8000b0700b0501035050700c50580c81c00006049090f54079010140a40100b0380450100c2c0a45040401c484400c40300000c074142004c1d580d01c02c1c0c128001c083c1e0049035400c030074a900c28003018000001c909030004030f100e4099800324410380c0c004901410780b8648004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 974742787 1250 974741537 974741539
    0xd2a0f08040e060103020901211e0f0507020a020307181d01021b010e030a120b03030406080a06051e210303280c050304080a12050411010e01080108250302 68
    0x21556210a0120080141003030702c02012840c4195101c1c40015001c034411200724034080780d4034542014071180c034401c0440407401c01110106021081b8003052902c03644002401d582e45503200000e626801d00303031051340d40c4070143c0e000420b014017440d00040c0d540d142ca4850148110040243c101100200ea00a4030300c401c40020105900710b0340c3c64030300e0b000c0c2d04020702c0780401c040c16840d0700806c104140948084661650003079464151600403c032001d88000410901107521000e04072820780302080240002c0c8102da40d400c5041c100802c010058420591149100791180010030300e61640000c0d0003200003008079260070000003041280e0351a44082d00b45c801d40c0f800088104820401d02e0702081c11080315008942207c401d030b12a00e0b00441c0c40c91038040e00028024000100064600e6005100c14007076400d2025543d070040000c08140d840c2168110750382d80c001440b07006d807560444812224281c090811000640c10044480c0c0e880040005c00114082c41c0002108840a00f40c0d2101c09150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 974744037 1250 974742787 974742803
    0xd0f0602130806070f08010614040b0309060402010909050f180c0406140321180a0902031306060b0304050c010323090a050c0303130e070504180b040506030d2a 70
    0x101c0000301001028410801035009000000f01020b02c60b10080c00e019002e0340360600180d007000403c54000c000b0640900180c030301040041012842c040280d0f21503441d1070001c203130b5440c0600c001890000c243d404401e1950401090145c0f04200b04103040d40812aa402504959900100340d40741454440b0003a400610300715001c60150700b0041c4500c0c031901d05400b00d034900d468603203c4c28511030000c1c4542a001d50f080c8031030b25984c00d1000c071034195007030020030f1039662a45501e443e00403640183c403a20214061a00030030104001c500a00000309414000c0c07500358a800d455082d103a071500c44d204c83c1015518045d401d8011503041456039011030801924000d46803810f2000d03500c410f8033b0780a40340b900c21582d051516142c00001c642e140070890b2120140c05140030782c82c50200c100549a2011701809000c045009103440b4083c01d40b840044101103441c4000205100413240301a000c980603400c10f00700c0030301958120a001510110000c412030903a6016040d00c402019085030081903c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 974745287 1250 974744037 974744047
    0x9010909180303050705040f0b031e0c03090d080c16230f010b0406080d030f06050d05010207021306051c021203030907061119110a1e0f05040603020f0d0f0602 70
    0x154002031007855129490400058484103800d58050041d4854040d0491110109100284605c0c0145070810b13190b07008102041003c60820410410465924460040c080708000c0d19020070441d1501d550403500301800c0d107090200300c5040c68480d0704441607081d580072a000081001e20000c04005071103040c0a1010311403194a8151110f150320310008440d800c2803c0035100b494203219500864641d00010b240c1e5031031b08130095000c1c0c00d0143e0105609070342c44000140e2502c400003400c2c4070078819000103903210f403070703104103c05200038500c2c4040e1180340000c18805601e8071034040700070014440000442c52440d200040001c07000c4581c0049a000c04070500411200024151041e50b400e41c9900d040062032032500b0380e0ba903816034051400b0500840b110b0012407500400c1c503c4440d006407450850f0764484aa5940e4030300d1040000880c90180d038401c00c44090100c04280103400c04942c14004d01d4036507000501204100d58802c0d101d15111105202000303102d00c0b210110542c0208195290 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 974746537 1250 974745287 974745311
    0x62208010b0a090e0309012d0503061003270c05060703031d1209090703240f0801060305100506060d0e0604150e1e0f070f050406210809010909 63
    0x28000c1051514058084010301292100c807130f0144e107048450940086080035441001110b032407070307184c0c4026a01c5110880006010000549072804071034180c90b41c1e5501c0c100382c410f00c18030403200c2407500f0030549040c55850f20b500da5544138a030002e203242068401004141000d8124407096846154041c0002683c5001c03d50160421858540c4601d0f12020640c2000000c0e600c0b40880d4800200c0c00100700401d0b0f1f001c0c6414101c00c1d4000a41d4940022045e142c04c00410321f144003001000211286118100700c0c0c503010460000c007030140c1070000c0c00140c0c510f9564035a19021030f204007a40940300c1c00001c3c01511607800780c44c1c014000175818800d0060f0141296240c080c19a0140e501ca41c0300c40355030300c140c1c10b140038500c140c00c07880d4000c11a5000d0b400d203041014148001c220000e016a00e901500b000e420041480a02501c0d0648900d130381c580707030402c0115003071640b140702015001102c840c41e42104101d40c4441c1c0d5040201c851382c0d4220754004035000300d415080703c02c04a141c100e00c80380e2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 974747787 1250 974746537 974746541
    0xf0f020f0303090d090503070806010b1810031d0c150304060e0a0f021309030c060e03040b1c0b01020a08040902030903190e04111804020702061614070b040303090506220801 76
    0x1890b5401d031210340c0d905d5154002c0c07503250506070142d07400c00c0e0311101c0100115000d0030001c2908000c1210000f0f00c1751031180016400e05c10300002e1100003511805840c0300c00c00c4403007808000300c0001c001440740d80800070100328805103403040c40441c94408030008007440311907009030101d184904140c1e590752110b460140600c050a080a80c040c10403103040b0300c1d2000d21403042044250705a01c502d58208143e50700e002c007411600140101d5400f080c00b00144c02080140a4502400348a00c01140f04041d141c081085982ea02141ca0441d40700840c644040b944290841d002e461304440003583da5a1180307100703491481608814881c010201d0b140ea140b595200a208810f490115414440003c0c1003418081038010020b134800024884400740741c2d40e103001c0c2e009101c281d00c0508174030f0524419201e01c5155540102c0c0c165030b030704041051198419010f2107104041e00c1c03000c000c282000d0a60718000c03d1480d6030b014081c010303500040c003000f81202101c0700104d000c11044a0301081d60722030f115640 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 974749037 1250 974747787 974747803
    0x809040606050c061b07140c06030126060f06090a0e060406051f0b0405060a03060e01030507050a090e150414010905030a090b12040f0804090f020301170d0f0f020f030309 75
    0x10141c001c2101140b50345c0f034a4000c000e40704211114043c2082c000e42c0320b4000c0b552110000d00701520900d0340b00d069070340315500514001c01e500030401001c0c020040703280100203005e8200b807140e42c2100c420410f840c102581c1290f000310003662407a50b15910346601c2c0c8014a1030f2448000d43d441943c0c02c1000f00b20090700042d1050b500c4411000d13414500f4404001c0310314a0b80102c080d04070040c0418801420444090081600c0c01c0c40d010a6050341d62070726640c001c200380c105440c82d81010f6400e1046003001c80c4003078002c05039200d0410400c003020031020740315280c00e82d500d420907003140c001c0f40922249900e000800310b5040d000f0801786082c0e140541da80e07844110703003001144000c2c40c00628a1004400d46640d40e825141c4070030075503a0340c1c0e5500340b9000403200848035500c0510012a1845040c030880e8403001c000c860041e525410929040300001ea600ca01c0011a8050030f115012a80c6c08000c001504880d8148140c1648600805900b054140d002c02d880b1440040200300206500190b41c0b4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 974750287 1250 974749037 974749057
    0x3030705010e0123040b0103020105031f030c0e010b03010b04231002010506011d03031b0102040b0a0c02040f06080a1121010b0f1215100906061d120c060304080904060605 75
    0x400c09030b00350440242c082150b024240040c1b041c010009940160000e5902210035003c0203501c40e141d00c0c16186c03050441d0810384082074450780038016554002c010380e0141c90403004840c04d40d858084c01c08540e10990040c00f09843e050072103601e135a1401100d000001e040248940d642549c211002170003440f046880d07900140c01400c03c400c81c110346d148482443c2a01801852401d42c1c000ca00450b501852481440d0940d4204000240080c4420203480c40103100c0e5103008944503907004201c26544812800034079640f80c07000c03c0140c0800010001c0885038015203000d00d001c150000103901d090580c141700005004004030460510f8190300071600400129241240e41c583c40d800c1c0125540b170701e03081c0030841d8001011030040404402c1c005501001c040d041072456511484140c058507902e40c480300c049240111004195070001c80031052800c0180c0380310844c985074071902c40e51850b0030310005000311400070101e400e00c00d22408031806444050824041a56241e000504640c8880c100c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 974751537 1250 974750287 974750321
    0x60314070f020307031d062803021908040309031b0e3105031c05091c05040504020a1701060903140a1a09030d15050a1d0109090203030705010e01 64
    0x3030496001e001881508001c990046080c0001c0e6039060300c1003002c1c4074220908030030501101038160744480c014580700c02981c1d5940307008482ca0043c04100c44508141109160040c00800400400701c0520810800d80d850248410303242c5042c1618454400e8001a1400d1540100c64000003d141e6581044886969035606144c1d500311182140c0c2c5003a50030120f42c005580c0d100455442e0f0388108000080c0507600b83d03450200e5034940c002504003641906074456841e01c1c10490342c61002d001805428a400441001d0b03003042100040080c07040303000d210b10a81d80481c2030f0350114407413410010b800f1800b04084c1c440f540c4a46010380b110106100484002ca05a1803a50b0103410110706241d040d0f41c0300801000f1401111807400031944024502c0c1d8845c40700b8072010000c07040b41d014001c609080c100b03032102c0680c01c01c030601c6000c00d5107802c2200d01440410025603c2560000014112446100c000036510001d10029045114020b0094455820000c01c0c103c3d914041d031104080e05140044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 974752787 1250 974751537 974751541
    0x3060a150506040e280c090e010b09010c0305031909110f060c07150c080a0801060207081b15130b130e16030e2107060609050c0406140f0301060314 65
    0x1040301520a601500340d03401503d20109003141710f0710308000301403a0003050016600000324442c401322807200720b134400064050542000780042494410b0301409e80048407515240700440042d050038180e803002002c00000000040d0303031925194888111301506841403140e50301038103000d0105800348030706a00c00d034110b803040b510ba443c0020481e00850601009803030120b01d03218400129802107201c84c0180040340c428100007912010041c20105480d40350310f4015418210001d15001082c1c2013184c49a1000b14a080048208002103007074407800c603085e54010b040e49450241500030200540020003010034081100c040c8000542001c10390491300004c8141d0325800b20300005010384070040300d98034410350950000e100790040c14481801c50203ea900b404c914100b607200ca2054411400a17103000309180b0708201c454082ca00050a13000804d00480c204640100c60f01d00c1544290014080382581c3d030b0201c0c500380c809880c141c1d80440d1a00e42c032980d41d02d0029000c2c0c440803400c98001105000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 974754037 1250 974752787 974752789
    0x50d0c020c0a1208120a050f1b2b332d030c08030408011506020c0105031003120305061f020309041806020f07030206070206010506031b0903060a1505 66
    0x107408100e8040200038a44040c50118029000700365003034156454035040040308185072044810130300440940c10300045525003488030140002e80138041c405032200040d2000b060450316415203407944249010480c02d4020065070a444035400b4861102c600e0808201d2105958032101c0741010582041000d145070b0409114000e10a03014026842c0d074031a0411900310101e11041c000c07402c410342e2100300c0c1c071454480c0c031500480da0150b44985080e500006043c010103c083c0507180400400c400480035113803d14101030340354000303409203904019022001034100c00f00404000c0045401500c405018220480f0003030142204441e0300340100e06c50f00c0114028205091351a00d10042a4082e6003052040e40421001d018105c1401103200324803040500894407030b20003805040400018155500642d140c00703030402c54010000c0703082d0340000780104820b403220300440381e1041c0003a04030303451031104645c8040c45005040142e40c142c4240030801031011240d030f111400d07500710149005000d541c3c9030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 974755287 1250 974754037 974754043
    0x40b150910050c070303110c03012a0302040531181106130501030c0c020a08070302010801080d0203040e04140f070515250807120e130204081c03110a050d0c02 70
    0x1082e100f80c1d66100e0541000428410b0b041d40c4081035481c0b065403400c0d001580040d003902c000d00720300c01b003495220358003e10a40c4c4010b15241081010700b001d5003000d241c03000103407411b02030a81512145000e510300045141c08100d070350159190400b0100034905504041c0d1094140500d0102c40500180800b40003501e44881a41c500300000901c00394003d090200441c054000401031505000c40c0c4c0801d02d0050707803030780e0304000540b416500802d6050b16500004041d43e0f0180c0c4a403440e03402c00501c5042c0640c0c00f000305c8040d600440810300254030b07146040c60004002e490040741c0f07402040c80300c0300d0001c8041031060440e542101d48042c0f0340c84090b11469140306030701540901e4440c040703034403038141e0030365420302091030140110b5408c1c03003603589a000a070714134286090000b0781c51860000701813030000407062249821001c2103081c581040308440e1b4984d94100184041c800383c00070600c0852094000b4a40501400f12070768964541040140183c1c002c01d00c0654138505101e01d140c8118800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 974756537 1250 974755287 974755297
    0x70b040b07110a060e160b0910050726040518060907080105010f21050711010f0204060522031e050114060319060f0903090303021c0503060609040b15091005 69
    0x120080c1403d04200d42d6000010120346000c10118050042c2400008094800d500010100000100c1d0b480110710108500c8a44400038982800000e0140e400805d200c90303043d8140c0a4492103860b4118159003800d645401180d01c600d80c0190500360790b00300c03442031108245c081c0c40c05a030031030216210b0032000e03110400c09000f114001880c0b00c102c070303040500c01c0440455030401410074000880005a1580a5900880703519002c1488039010304241c443c24801d035120501c1c0002d00714241814160001c11a1281103000900540303048a500c50804580340c0d2000156881400f40010383c512951a428480c110002540c183d441c000c02c410348181c5c21448241b286a000300900b5100203e202c0c0c81c1e21545d4200c1043e1201513952141e1803040c0300d00d228950210b130183c0c840c00816807a51030000d00d00352060f6403075086644c07140d111800c040d80000c1541c0c2c00443c1164136689414440c40406c0051400c040c1d0207501c1400e640d0305007140251003000b000000415a544420f90b803180e87c2c00d0f00c1364421 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 974757787 1250 974756537 974756567
    0x50106091b140d020d0b060703030b09130b150118180609090c150c0c0303020a120302120403050912060a0e0d110309040f1d1e1b09060114070b040b07 66
    0x300f003024414400003503000b8002e1a104c240c0000300406104c000c0b513000e80220070201d001c2542c440700710342c0d103250007034026a11003801d200400741c9400a596200742060007030044020b6840d4100101c2c65a07005440310b0078566031007007010502070755518064101004036a4000082d03441d1450100341d60311a405030841c01c0750801010040d1a282c09a1220251862003404080101041c040c500282049005000840c0240c2c010444401d103420803a40d10744071000301000745031042003003011942044c21a0b5500c1034041c00c1841d11291028003150f00c4000982c0c04a074540240b00401a05c3c225aa2008c81000341040441e14405510309003561204015002c2030501d9009000d01062464650098291240c0144021942e200c0c01682c50030501c1c1300400f0f406036500004002c034080071030321660b003c0a00c2c0c01c5009140584d851a030030074500101c020f089002d8041c003c0002e490307034001c2080d04a9074144c00445561644c4038141881100016501210061a0f0002294815205161960600741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 974759037 1250 974757787 974757827
    0x6030a021507032109060b060307080628060302072306010905060f04050403170f010b04062d05121e0a090f0206220518190207050106091b 61
    0x41c8a400754001550850400007400b141c150003844485088668070920000810304c1030207450914141d030b40814a10f40991011300c2004501c1e6840107090b0780105064a0809180c468064118144000310f9410000c0d00b0304004001407865141e4010030240b0300904031a07159403c0381040081d01010782100390702c640c1c446401400501400c3c1c1c085a00104010300190381c4250150226050350b8085034142c01040381c180c106070506105103c881c1d8005984401c0e8401d80d8146600c1d44a030b8042c500a00c2c00700442d5440801d6212080c8003c4005001da80304061410070108200401030350040400342200265a03001c201c10211400d00d00500e4803104100706190303a40c01c0c044400424001030241c804010000c0500d01503103481d4020b062007000882c140440d459801e803c1103000190b94040ca00a4581d4203400e9018002200c4660708049100d030b0510903c15a080144003a0047c0b0501808552030f00c500020380001c0703544603960808051003007040c1940040000d655040c685079107003122070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 974760287 1250 974759037 974759059
    0x9020403030e060309032712060709090e0106080106030c031725020325090e0c030c1009080609031306080709052701080c01094502071a06030a02 64
    0x201c0c01201842d031100811049909207c0c0c0b035402124516003241e5102c0d4011a4450f40741303a10304120607651040c0d001040140a1801d0880c8001c100e80b040e0300c14080c03030070360791a00c4510301002900058014561344c030003403101e146c480c20500c44109032032008458440006c681590740795010015112102c2e040044440c0c000949d40003500041003400c000c86c2e0500610700ea104901c3e0880790342480400000d118108040c1c1401078030801c89421010341c4040c0da1000f0300c03001c0c8035540000c050808410a44c0c00c00440c030b030388120640b05000c0c181c0240c08640035a508120040030000041c000b20321800203d9644181d8030f070070643d10002c040d101080020b010b010700740142d003414400d1003017280b00c40081c02407070758a581c105441c1120a0300124500d030801070304103d03290781c4140f224000e031100c402d400c031820880c803000c108441c581072044c1040750001040c034890204004a4110458420716040d0b60300c10a0345031050403071005043c6044000700d0318003c502c49050005121a1903603000c0c3c100c0d4444 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 974761537 1250 974760287 974760289
    0x3110c060a0513030206062707030516020f0c040b0406051e010318030816020c0a06031a092505071203090c06020d020d18050d050304061416150914150109020403030e 73
    0xc4550301c518002d0200408c11290300c2ca5160309024460b18503a81d00040d01c0c100003482d60190512800c1d43d80c1154000940034200042c0031a4400d43c1c803800315400a100286c41003c18050703e0154000b0341d000c2080e0800c040000058810703100b443c4000d981c00c2040401e130302c036201d402c075800f200050300040441d0005204101c0f043c5014104c0300e00c900407aa15081c2940003e86000d45070307040017000a4985200d0b40021954684800310f211007180d000c050741ca04645132105a45203021088140304416040b0360613140604c0c112129283c0040011983c0b40c3d1035500a0007a14001c0c00480e2030341d071200000104684007184200f5640d0f415800780403140c002100448414412075034141c104c2d15642030015403650b039440c0c201006489140030b19207031032034081c0c003a060128051a00c03865141c204801818520564403504030594041e81c0d8199040000c00c103d0700410710f01c14010010f20001100d4894030310001000c121f65138551011003066a2210b541100764040d500c030040120740c406100b0411 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 974762787 1250 974761537 974761549
    0x1060b0a0c0507050907020c03060a0b0919060b070804240503060d02040b060301080106060f09060c030809031215041112150d0c09020a080601020d021b0103110c060a051303020606 79
    0x1c0e018504868100b074a5100003000f00e00c00b40d58003c0540e00c004414101414284003481d484803c20070308101c4a9425404030750048001020419030300e540105000248002d0b07031100c805400c0d41e80c402c0d42c035083c040c940300313815074441d009080148404150151025a2881c0711042c140e841d90b95640c2103440312007e00c140c201342c5507412648581c0711f4480344416200d07440694002e00c801c100100d0141c0c948403000c0c082440c41c070041410420346080910007240c0040c0e44207106a40343c500b80004da0354070030380380742940a03500c0b5540000e030303540b03040c801140010000041c460700e04440400400103040780c403000b68400d419903c0440034900d00098100b0f81181c07400200300340085c09000100389244d541ca103c2480e1034000d00302c056400301d49a00250782c82001c140d403105080c0014003100d44152406541c0e0b8403001c1c120300c55030003401650320305644260040091714030321045080e2115004000652201c1c0d00b00c1d140c2001a11300000a8080e580c90301a800ca40d64050f0050042c4e5205e0f41e0501074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 974764037 1250 974762787 974762807
    0x5011d0f04052a13080a03171b0c0a0c050f0f0f0609030609030c070501112512080d240b0304110d050d080603070b1812010c0f0e0301060b0a 62
    0x41404140c1d26144141e4904103c030303c90085074580032541c0f484256444059001903070001c440ca0b90150300240d001a0304a55500788078070788102e40852581d110581f40003052100340c007040d1001004103141810000024828030303154820001d2000c415102c806103c2c0078000d43d03409540c010101a2079030081e040c00300e0402c0b80c019000d4130403850b2020b1040403e103000c03030903034603842c8640c400942c841800f40d003440a20007030142460070261102501c00159941e031200c14075034400520f4000980342d120300d10360380742008000300d41d40412024100e0800c1901c5400c6440c042e98400d0030124014040600562010382000d08802810055824071200d05844e802c010011200307410181031318038195aa098000ca10b5520076402008003d003003175001840c1410140845019902c00d03041809403ca201056442e1178150a0391401d10700e0340e900000c1c010710395509680425510b03060001c4141ca0f0302003000300c005c00450301c881c002140010300385030883d4003900c900b1040c2c0800f480150026031080703501c0703a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 974765287 1250 974764037 974764051
    0x102070918021908060a0207170901090519060806090403051909090501030c03020139050a02090a020309161206020a1101060b0408010c020a0c0308070305040f06080105011d0f0405 79
    0x3221507801c0d4007103188940c4401c0f8494503003256600400a1940c01c1141c00d41c001c100c1c000035410190f00d44d980120408030100d170014141804030704130341164803480304d41005007401002c14001d0384601001908868580c010342000841090000e641c0307013040014280070300c1d41651042e15191613480d4582c0492000c420200801075420f500140c08015405607a028500400c20007031070310b28520014109148105800807021004140d249060043d600d0b000c42e60b40c04040e1680d00606d0310320300a402c10300e502c20001c2d8005030500500043c00c1c280c4d07011354801c5104d08111400e880499420150202440c89012280c6e24103084040c00214503801030f01e8000f1150030400c40040000381510300f9206160001684000d01050801040109002d599000c541c01d002a0103298a00d03200d0b06104809400041c000000001d100d004051017002181d0051900c603070800021901c400001b00369040a00c1000e000404122182a004024981229209000410121110903100c003800098103000b0000303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 974766537 1250 974765287 974765321
    0x10c0e0a0f0b04030f0c1203051b0a0b010e07020c060705060711060c071707021c29130201021507020a03020c0a0e07030504050705100c060e0a1212062601050a020901020709 76
    0x60312101103c00f03041050710a44486485030000c045031500b11103803400cad002e015403156017800c002c84c2c2101012815141d98480e14822562404001ea03e0141880c000c03a030031030f5002030a04180040482c1080c00ba00c440d80c0c3e5030306150911452140d407410140e0b6850445c1c0000c00c118000200304201b0441740301940c4000038101442c035000160300b01242c00403503403041d01340070320141040140000925600210591051059001421001c0242008202d00c0e00c00000800c10030a5a0003003100c00703041c0c1e05080c607220052502c40802912100241d1044002d4030a00c840b45a00340b80c081d1010b420746420300000d81c074a6484800c11809400050000e036868054082c001c560354803a40654039105400e07407602800070006103803c0c0e00b241c41041d0301b0582500112144000aa1280c0b82565000c3c083e2810001d00900340515000070b2000b0f03031121070400020b000c0321601221224880c5004001c1c0802017107166217070701c0c402042e44190301000b0f0058100c42001c0c4805410b41c1e200604580800401e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 974767787 1250 974766537 974766539
    0x50a300209071101050906131104021210090507021902091e010609260606060a0e030303011d100f050d030207030b090c1906050304030e040905010c0e0a0f0b04030f0c 73
    0xc00c1d8035550a4480d18009510700a0103002d0000c24054030340c200f09100020310051414052018003112407001c02020202005115951030340c468041d64098403400c3c1c030404290500748402c0c04400c1040c460000e860b4100000074030a140046000002c00302c4d01c41d49050000707001e6082204410300284021040d411070050580800140300d2006d020b001c079900c43c41c0d4400c0c00c01d01085114040e04060801c5207000000500e00b012000c5800d03504140c060714200c0e00c030004144162041032842c05210b4240c403001c00002400b202410007562600a004284406d40d25180048151075685000354000b00c2d0405208000c40c1c144000b000403403d001e40b059800310b540303942c0c40400004013580d074505aa440f0000c2d40c0c0c0d4074600f4444c0c0c21068506052a002641d00c1e0800141903804014006024000214064119a100c9822400d40306071f220f0002c01c41940b0900026080304038003a07041d4040c8502d60b0003c1031005404520f50140e0b08840e0701c90b4141442c5643d09801c01038445821031b280c018580c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 974769037 1250 974767787 974767789
    0x21f02120105101e05040602010e030c0d050f0c250509090c010f0201270309060906140708041707031e0c030f02011b0302030901080a0522020319080304020406050a3002 74
    0x2a002d0001944d41e40c445a40f589000e50082c2558490311942400d5002082040050000062400c0714200d01d410081c0e01d034026140d48d0703010780c0907011500740d840c0100c074036000c007058452040050003507041c80c2d4050400e45610904c5440c20f0102d801040660002c95070101d65030040c484284120314602c000b103000d00501c1c4074802c1c02204202580441014048d0300401c142d00f140c21134016050501c0c00300da00e50314000c1c0c01800c81700709100c40760800c0f40001d0f004050007011320840740502030341ca003048880c08601100d15030300c1c03550780b000781e8440788142e500c2c0707112400601c0f400c04040d421503500e404290440d114560341c8981204100d05200100040c040401c0645801107a820f0088d00035641b60f8282c6000544110f034020020b08a40d854a400c0010680c2066444500064045070211043d40d007440400c0c503145821051148402c3c0714000582000f110800840c0700c0d5100391000d210b1180d458051000c11101750081e0030005507070a080e000400040c856030086001050b1542d005c002513a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 974770287 1250 974769037 974769077
    0x13200d0b060a120b2e15030b030f0709050a06081501060825050d1d010b010e0415051212160b070809030a110309030d021f0212010510 59
    0x11040340c0d54046603003080307014640705038600c2c000c0444001400d4038010b10342d200313403080c000248401d850040c811071244a00b6a00b441c20381241500104041c0d8098851208500d0000305106800c002801c0c001e84002074100802d0011041d05c11600820341113041c103400b6406010010005000313195078090001300520204249503513400100945806541402401403030340200074007500c40440d2030705040e118210581b031035240400c10341c6011b540342c2c10640c504c0d0300a0999400c481e0324a4484604c10017801c0320652100310410000d0301d603080005454020301050f2a407089039030116202d0941c081003d41410411405407100000c15904d80c0c0d046a5480c03000c942100b450782c2d0100a000c0c0091082080051410390003070400e003001800b91501d02082a03aa10401111307404011003402045040081001601c20921004003551003294070806c0c025030343c07212a800320f100070014200a004200162084409681c020b0012404980c284424001c11031460003e040420a0070f4084c0c1016075285 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 974771537 1250 974770287 974770309
    0xc18060a0f0807050c060402040c05070b09010e0d091503090c03080403080702010905220b0a03140d171306090f05060a09050d050f070605090a0804061e03051320 71
    0x1525040041c80c420000200040002021041405400c029110715480c00103070180c0d11a90480380400e0340c0009801c1100d2601030000010980034028050103042d41e4103400c1004c03001034a200303c1d03813a81c40e00c0c08200d6095002d4814000c1100c080311100001d54071980180b503c09004403a0039000071f070342c1d42e40c04480d60b016a00c10f442d810800f2503513204541c1c3c441c0041000740022038050000405011a201600110b100600c0e41c09980e41580706540d210b44010b5801560481200128850510f070780b143c848a4000080c0c000901d0b412010881001095603140160b409510b8102c6402140d0394400013406419400d9600718000e08078040011020014644103c00c4d4a50220301d03645140303001c03898588502c0e90441800303400d0203059800c2d1650400c3d200b0160700808045416104d41076040e0500e1241c8401500d24040041c2c0480d801d60801b08110a1074904a40d1442d918520300040f001c4a5043d00c0d070904d036080301c0c0803000210703101c40342503948040d409110102004003100020801118 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 974772787 1250 974771537 974771557
    0x6030405010605240d09031103070c0503060a020c2107080c0c0f03030a0e190506221e06050d060f09090203011404170f0f07060203150a0302090c1806 66
    0x12031005108504240e10b811042250030f88001300b108008100c18480d42c041c800d11040e1175660b89a0000a00d485001d011913440040420313241e64004c1420041110f01c030318000c09010b48145408540c8400c1c4034401c4907a040d500101038480c0c962002858002c512024440d520780d447c0910916000c500028010908450900d0060030600c00e00006d0010001c1c6400c2621311030f8206100280c000398110040411078201200c504600d0504030711141b805903119007203540c01c220080b940d046240c4402d00c03114106e0b409405907900b0b9541c5d9440d0550310720080342d80c0e5500003c01801c1000218040c2010304907000c002480480d0140d1a4006000114010790060700190b40700c0d4104401d5040a1140c504030142d041c54040441c685a1200c00c50007040c0300030691007000009a03505c1c580b8090064a01c2c903001030304040e40c1ca56460512001039041a50400e03108008200040c1841c50503d00340800c40c1e41c090034521032540d604007510301e1a00201022030740b000100540465540d503030b000420303417550 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 974774037 1250 974772787 974772791
    0x11090a0e0a15150807090803090f030a08030114010801080a03020a2009070504090c02010204081c05130e0a060909020d0b181f0b100914010509040f062108030f060105090603040501 79
    0xe00c200000380244da020700341c141071006c540740900419002100315006e0540a55418941c0c03001000480e1406007600c0c800740c51a40040004075103621201107031040440d003640e0f800c9444c0d0305c520040792201d0880400134050b07400280420006a031140185031a105c1d4054846000000e9902045100d1002c0702c0b41c01c0042d00020341032012911794800d00c85030010b984021810a401e0070003199a071070a401030074161040c101410008240b0403c111113100709006500d110440e07070f50b150310004a00503030b881c45805041c07160109040c42b0390b105003040c1030380050910382c038142c05444a610403d0080e01110503094183c004c9072480504011a0f00c603210940e152018844850b0942000c56402000c038610940086a008207119800811141031703409217080c103503e0243d80e40060303480348280088030303030000d06100501c46150400d80c00f94003240c1c850242d940312116035a10048a21503460710082c817515050000c0f0b001c401400340b04a50220040c101149000c00c0380c00081d03226081114102c51980d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 974775287 1250 974774037 974774069
    0xe01090b2d12150910150530060601031d101a030106180f05070807080901021e070c0f0506040308031003050f1e0c092404150911090a0e0a15 62
    0x2c0201c6101105d03d09001c0110203145526811440240e10955100380d04042c1030b9801c420004501000341d00c22a0303005001080d9000c6110345807001250040e001c24508007611f1a030f03600a03c079410300e00782c04502a1020080340d5030302d0b074000e02191103918903160114480b045d03151401d00c902c00140c400c00c02c0100040000400700005d485200b290f10242070300344814480303120b4000440d40d402c111076040c85141d5913134a44915009020b2000300b034001000c1910112590700b04800144402070080c5101c2402e151100050807182d400c0d4412917801031000c20081010525241c00703142c00503000c841c07204965a598695610b080c000e54510145a004500e0041014105c460144030300041d603809406c0300800c100004000b9007004240b500845112000c2442883d0702590700d542491009008021880d16841174003039543c1107000e4202c1203032034500000510b0090382c098424658005191582031420f0408283e103900014100a007401e444402d0011040d8810080390094618822549001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 974776537 1250 974775287 974775301
    0x7030e060a17011401020703021c170714010e06060d170706020405030f0c01170601030b0a030b1605073309150501050d20030c03070e01090b2d1215 65
    0x84203060313000403801c1a4003015001c199802080e5442180e8048820b001c421030b600a0303034451046c0840c1e00901213159071146c3c0601c2a09071000e00701042c06828040580c0c80310704816801c031920306504811540c000000101c01d803510a03070228401c0d1083c2a01450700f2076034400d80401740c0098600329a0140c006c5000c0c051750a0410699aa103c1080d0085c061103d4000002c0c282c41240c4042d00f1440c03c0c024001217080e40240c105d04503e08015010446899a0b81045066000140c07154818002a824841121403094040d5002103400c0356204116802d081c01000800d12504c15500100d04910600c0303142c1e003c94415405224094108007200410455070f203012140c058003d1489000c40c940b03500d0109041080c1c3c1d98440c040080d440100c1112480064500800c4a600a602d407096000215102140540450407140000401c0c00388003152020404070249400301c9803000442440c40c9408100f5a500e4500f950300080d0a14901c60329905201c1c5c01c200180300c1c2c6010483d01c2009001c15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 974777787 1250 974776537 974776577
    0x110114061c0803060d0218090606030706030e25080d1205070c0f1101110a030e10020a0201082a0a02030307090e0105060d090203012318010203010b0a030207030e060a 73
    0x1600e42004840d2001d680d5990303088480c00301034107403400349050f503140790b00715200e09050085030b80c054500c0c807481c0c5c81d10f40b1082c0c0c0d88000858125010380515203002490f24040d02990401917214405080039030b0400000e407042c401e0894a101107414805070000d0341070010302001c1800f2503c1d03a41e40031031007002d84810302652809005c00c41040410010745010446071301051400036841104c0c51001449800100c0b43c10903406c1011216010380700174503042603080001c070490031400340c0e000c51940e1100c1006a0700d84e8411100a804a150200015803c0040b2026180c425001000408400d0010702007894150001e550b00005a0700000c01d01c01450b400140400013081c080a140711251f0402000c220700d07000c0c2413454510b6030b4070b4901440071580c00f90400608400100b0400105070081c0080781c050020959840e41d42c130000a070f101c40c02e1103040c000c42e81618560301c0214070704040204124002c1d4422002541001013256428002da038840000b01101221035441961103d540c2c101500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 974779037 1250 974777787 974777809
    0x33501030b0c180d1a07050d0b06070210050721032c19051f09031205060a060e03031603031d010e06011a1303030906080906042111011406 61
    0x100c00c141440b02500140e108454000080d005490600c140b03080752810481e2942c00030b1722040307041c0c004c40c1040a802d502c030f4050120040110030910200c00c1c22000e100181c131807031078040c1d0489a4a00c1c0850000c0c0100010520346100d512101e002545c03400b40e21a00d4005001040000303501d84001d010326031007403008990880c1d10116080380020102600c01d50302c180d001940e402047e140515131043c090103204a41100513001118144404041485001002c4149080b800f03c0c8842c030044103003a05070300c80c03503114101c0a0040f4104030704010041d2145034108e91601c0e8148810005210b0a41c8515451400da900c603842c08262040b6550b6036046151484500c1d400681c0f4214520620740f50001c0c11034115020039800d05a1420454242d41d0f040c840e130b40c0c032050f031600201000010150300402c0c9008a41080d90f0324005a00e07001031050300c5807070030380307000d0444043c4060301c040c1000c0482c01540400b8041c1082e00c0001e00c44605107080d11001d4404101c0c0c290031004101d5541440b000e164 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 974780287 1250 974779037 974779051
    0x4080604030305181e0c0a150201050903041d04020a1806030201080c0c070e150604030f050105011a07060f0e0724020f1009021507260c0a033501030b 66
    0x608042d6512820740c4d10050701017420380408641451402d0143c050107207000e005005018495200d40b50902107450723203002c000d040c00542c60180000c50022021059a05807014940102c01c411000c0802e10a8000041c00999003c64100400903c0d4114503802c11240e01c485c0401203802c40c5140005062440014014002240e042201d64440e0310041030100680b02518400c2540e621a0b1000058000f00c0901c543e822810006000c024441a80c401041291180000f0712507603890700e402480522020b148400e140205000d40380c0054000c1d08524031845003000001981641c02c0612864041180d1002c00c0b4951300046007299030041ca040740071200941e0004201c40e0900741140c6a40d0160780c0c90441980c4c4c0e48161134801c550700d040d403a548411036002040d417200841c0c104401c02c01d1a5a010305c4001d26054444082c4c00e1074042074850b040080310191800100b1130b2401d451008408250859481c24908010540b45040610551710001020071042e50340c11454600ca1107030000d8400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 974781537 1250 974780287 974780311
    0xc0c1218031c0507020111160b0403050d14090105090301150f08100504030203030414070801050a0f05100b0d090f1a01180515010c0312050c030601173904080604030305 74
    0x94400c3d8000d4210b030126903083c6030010284902080b12820541d0202d90040300c52403212000941c580840050b0055a01500941c4c10304407001505464031143c1c8048120a030300140320901c80d0350b0061010b0034030980040c00200309140003040c10340c2820300035045461400340d005d105100c4144e00f00514154505180420030550810b52400f80d9a03020003880146035055100d080b00600400f0b0120400611550000b0b05c014102081003038040d0044840100c0307480e1420340000c0e4441d1042c002c42040728074802d00c3d5443c1c030030742160b0030010740000c110940340110b0110190001410352404841c02014100305600b035541020800520710302440c1c2e4032140c2908282c1809051540b8448032120401c0900b01241e8200340ca240588542d00c2481c0c030ba0400307519100c02c00490780103100055210318026a50002c0042c589461441010b0013a200310600302c03400004a03503081981102d24003c0e88074289031150448268010034100c0e80150885c8440e5003103c0140700405400d4010103030060b401c00c4803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 974782787 1250 974781537 974781583
    0xf0303060a030204020a05040e0406020909071b03121512021507080414150c0109020f0d0519140a06060e0604020f0702131b020319170c0c121803 64
    0xc0c08403041404081d00c00d43d40029010106c41c050b00884008011a012240451521741010780094200981c414020201500010001c901c07807080d126003043d200c0c10344003c8521a407070850f2218030308460720b10055034800d0800e410304040c02c0b404000f09400c6400503207a48251046c400d6884d0b0383d0840404c0301a05105041c00281400c042d0350a603007603011440e1003008050b0028040c620341c00c40d21142c0303000001d41e0740d0010b2419040b2281d068000e8480c240c030340c050603080c80581c104142e8040d0188e000010600060b806800c1c0d08102c55010703000705441d10291030740e0703141007041a1070201c07040b6540c1c06082000c2ca001c03041180e400801124111708040c03030901014110f120340480203200c2d8403031301d40d0603001400c541d00ca000d0b0f40b07600300d0802c94001415003000e980c0343c5c0001c005100345049465a126644d01c22000c0050f1007613031030214001034455140d00d00080e0000d80070600030f8042c205040341c48294a02c050038941000d0011181a0003c000606080c8045505040b1500503e41c107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 974784037 1250 974782787 974782789
    0x80325021305040f0206030c030a050105060a051e0705010c0f02070506090604060c0309170109060513050a03051c110403120e03210c15060112140c030a0b030105180f030306 76
    0x22290481c0181100c01045994561a10804e8600c01c480000c2d404180441802030072401200a548910441c620802407030740c85504228403402142180400610100f1141e44000d2103105c10215a00c440b40c03160b400c1c07501c2ca50f286230940e81c40c10140400181e0808030030300c003698100442001000151403503071518501ea408600c0c684642c2c080c5109120b81c001e4103908041c49021144014000105643c50711110900018044c009642d004d481c4035040c00f020800441800e14021421a070020080c00050b0a43c3c1e0140c80b070750040c2c1c0740d401412010034840082503e40c1c0c0100948000640c04031903489003545049100c1e0100d44181c2000c200091b0100f06544c0c0340051501d108c1d2008803c003030701c0f00c2c0d10311244109910036903001e14070314013848141c0c4004c810702034401303801070000740c8031400c038105000750b21b00072608200f50100e041c841075004581d02d000d0f13100c01150400615640440da444880c0042400e4440a41d40c07941540e00701020311595440520200d240c0c0c03401e43d0051407860520034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 974785287 1250 974784037 974784049
    0x1507050f160f090b010203160b070e220915020c24070f050c01090510020301061115160c3009080c13140117010b0f061207030b0a08032502 61
    0x1002d500310311681c440c1381c0590707a8020401c3ea500b0400502c031070a00b46266280204ca0b15005940110200d2500940c40074189412080c0c0707807052485054142050850f28206c074050402101d040d907201e00722000d40c0034007050500080403000c3c80305000700764500c101c0c02e407155200700c03440c801147c008106c401c1c8000680d1080b01f0b00c541e6406840c2c429222800e140c40d1600400107680001c22502c200b0052003070b14003290700610f040b80c0b180c0c0c40c0c03160000d9240c0d8501d5242d10301194204580b282400c009040c2d40c0c0d01002c5150980c8152801944020540d510382040c09001c040920800c2c00e00300d2107614159110140c2d0113003004910340301c01075919010a150342c9032091984030303100b42a0032801140e10800d6034818103500160035942c80e003a5a541c040388510800c64040c043c1203500b0154004a5424089010801c101028240e940382a120f034882d403d01107000340c440c8040585811001006940300303126000584665409996a07901000c0003094105031070824a000454005a11001d69528 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 974786537 1250 974785287 974785289
    0x11a07050c0409021c0c051e03071206020d0e0a0b090d020c090a3e030f04060f1508011401050301060e1602031c0c0f0207030803151507050f160f 64
    0x1d6401042038092413000440350b000607406441c0b6164160383c0030b02440040004030084031800d840626801c2080150000949034101145402d988003002c100149203000c0421002d01d03004030700040c00c00301d241d0404c030b080c0e40c205d6800311020313840300ca504028025245209504115900000e201810340b160019403540c03880c404052103501102d001541010040c0c00145142d07620854000c0c4100c4000d400d8040104000303903805d4208029000e50405800050403a0f0003082d03142100f40296480f035469001410100048820480e01c8400460070b0540f5a5a4003002c1c0111074004030b14801e4081038950303000b078143d00c468032aa04104041140c0c2d010712030b51a41062903500d00c00300c03899604205920718413178040d80700b0340c0040d10030141900080e140c0c09441a4003081d5940301c007044208004a03519a89070101601320742013000401d0020303c0d0300c00038485080d0050078000c00d10880802244464028003016982d80e04441d1031004015024080b00c02c00d12524008886594104401d1052030911 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 974787787 1250 974786537 974786539
    0x150612240b18030105070801240806060702060c01060801270b160512091615021e0106090f06030501060f0b09010309030e130e1002090d120306050a030b011a07050c 72
    0x41e0b003207842601c03075001c1c101d403040500280030f40e00704080018820b00c800d104028940003148803519411184201400c42e004440ea100301654441c9010042203500800040380d0003442008031402c0c00c182030052000030079155000180c625030012105011415400025841c074465200120010359505000d541015005400410015201c9420b84041c400c0301c24a90784a017080c1704100b481400011041d103034035034201002c1d80103681c1b5805071110100d8000c0480141e0441d1a10706811850450121a40c201c694004284103540d051004100c6241803030070305c44191180c1c018024002c090142030010b207441014000c6e0285040c080c1005e41c09520b0344a0304260320f03503103050300781445135440462104006120900300c000b488202c80040c40405201e803028003624082030750003180d504c02d0b208003041c081c10049a821040d5031700045040300c030241000303060340d030702c03001c1b826845a8911034051489405051059410a0f49111418047c1d03d81c2507800042080007500091000c0303800502404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 974789037 1250 974787787 974787809
    0x60903020106142409041e05090c0a2601060b0c03040f0602060606162103240b16050f0a26040521070305010f0209011b0b01031515061224 61
    0xf2115001070040c0c910f89500c5261f80d86010307400020107503107501c400c0c06070750382d80100d403000300b595000e00440c402c0e580b145071008040014040c0c41c0700404920300130700e0b441840002880320385508030440759800c0540d0408866001103014001000002c4002c00640240c0c00145042c0c90302c240060031a105102d40c0070b600d540902200000c0100b4015421403544c1004100c0d0403221b1082c400a0043c03004940c03084081540f89407480081405001640075038643d464858500a42070350310b03c01078614ce0008507118402d824100c0c0396048180300c400c000512800c0c8149501c4884144089080191000441002800c01c000c20143c0e488100c40003d6000d082c1ca80d40750b0030b1113503c1c89070a28440d40c0c8050995400e221641d6800fa00a038000e02c0305000c240c171494900f400704064105010b019007030041401003c0707070050000c18100200707003206000e5940007040e42c03036000e0506c0e0005901c561101c0081200450100085802e41c09080010140318401d605080700c2201c0c202d58241d00b903c16825020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 974790287 1250 974789037 974789047
    0x30711030906030a092a0515120106080402010917100e03090a06080a27020922060207060608190209090a0812010306050108060705070605070c0609030201061424 71
    0x140510558a804070010203050b103030310700070003000043c0088079401c44440c2c0201c0c054080c8a4041410880d101c000186480007a5040006100048440000c00c1002042c02e120182e00c00d03440d0820140641425a2681e040b402c19200141241c801500300d44005103410384081c03800740002a0f1191320850300a0302295088080c40e0301404d44c490300901c04d402c099002004030303502d5000300c2d1003806080c03042010010a0701e40c0b00b82d48c9900c1e0000b00c03000d10280d0f0300d40b20b01c2c02600d17001e485190458940c0038180040b040500851501000d00c5004540054010880205004287c4252802007a40e8005000c540901141c180c01d41041010000c0c4100780c00d50104085803410401014841d6100c200ca0f83c0ea0803580d510300203100003d02c000c544c00c034141000030a030103c01140301c600400707241d210182842d080d03075036080207840e00500480c00c00805022060110305a409a072044500a070000500d6a052040c81c0f03010b15110b01160b40107880d00d81d0400746040e456001010040014075800d5210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 974791537 1250 974790287 974790317
    0x1020f0a2001052703070501050a02030f070606050307030b09060f01030203101a0411090f0a0e012313050f1501120b040b030f16122d0b15030f120307 66
    0x307000d008610f12248407041380500c5a0713900f00049080300901103041b14515136540c0011100f81c400c40401c1300c01600180f0200441c0c010060107425050b2250201007000d58079400441c0c81c003845580165610318080f4148000880103100060700300d614600324130807075030554002c41d0342c54107213818a40d120395540d00c8400341d1340211003142042c020020030902140c91016031039001500140d500c28855070b10b0744581c40700b0345810090001211028440d1030800d80c80d0105004003001e00080c1e09054030720b00e40010400c0d50354183c403c1001004000700007214140020040c0096800070195103a0342c00201c002d503066030300940c103080984c0409070042002c40c3c01c000400e014118900038250580f1031285010340703034080824041d03131561801c440380c2c6d0750301e507030701c014052224110501038000b03003c41030326607840000051400d541c4d00914a84140203400c551380c0c0d0301440012640d41290482c0c0c0511941d061405204204050305088028000c417114001102c070070b0b201c09400482400298100c0e4004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 974792787 1250 974791537 974791547
    0x624070c0f0f1a04060c080d0b0607030305090d0905090c090123030f090c0a0b0d09140105091b0f0f010212070309170102211509090c01020f0a2001 65
    0x5401031649a007116961105a04a0074046004444104102d2140c680b4a001e080007a00d08407501a0346070302c901042c9854080b03640e48802005541d03035444000c49401521200d0003445854465600001c45141c10b960310b0f810600759009150421094090802440e65008402a08200d05289190341c0d55040b2005850500c1e141b114821900b109581c8140380400039409944078034055801105140c1d9810440d0780c03550704008006138010540d5006000080002c5c003e031107100341c500b800003242c14103130310381ca0003413032940f6132840c1300ba910303041001036215061000c2e01101078030000410b40540385600080007c80d4501006020340f40781680800c0c540e00c00c001e2682d19010015030565242c0190030010100b01c0f840c001c901c231100c0c1c00d00c0c4600b4006814821261121148640110100b184000350012114060034005694ad000e180004036075907060125806512503030000c14141e13041000180c05c0658005019041e504152114004038034000701c201182d604401020300d40707684100050351 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 974794037 1250 974792787 974792789
    0x1b01231e072105064b030d021c030531020102240402041515030501080105010f080d0e151605070605160809011205011d0c03010605090d060f020705150624070c 70
    0x201090081d40614040e002007400103c1d8003425000c0e6a4030290b280c00c08e0780d07112583c1071101c9607480c0603000c3c552200d01c80d40c0504d40040c4408064022240e1500040d9403841d469892840140c0580242d170007107603010403a007c0310385480c41084005610707040e0140c500c2c0100a101034003940d214244c90340302d01001114070300a0701c11401c13070155480d6030841c000c0040801740181c000e01c2d071030280040303040780c1080f540c2c1c0f00329000c003001400b4965400301704440c00070700d034540380d40c00400300d03c80f002038101c0301009401044220514031120754a20300740a8542081da40c030020500c041000040c0314000446050f2203156008941c1f00d64031010319004807100d460201c0389004192902001103810000c000414003001000704078004540c591784200c2006100c203226a8000c98000c202d441040c0c05c0020306203c4443c081c03c0006050348505807001c0c2681d100346003c4615800420b4241c0102e00d1001d08550407500c10b40306082c10a080034104802c0b40d0362900101e01e030100218a800821a01c0340603d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 974795287 1250 974794037 974794129
    0x14070606080a14070b1204021306080708010905010b12071205070e040b06010f0f0509120a050a0507050a06090f09020724021b01231e07210506 63
    0x61402400c07401e0490210149589401d03e90259080000d03481c1c03918000e0700d040c600c0b281c092145a80780c42d4200207524241c0002c03030300c6458542c00c1c00280700005200c41401002c0711070010500030418031b400d41c04c4403a111000e911400001a00c0107080c180020740301c00355420420610039064050500f203140c01400d610520810440c0d508003c10031111005643c000c000c01e0301c0707002410028a000351241700e5248402000180c082c000c2210910307040340843c2d00134a91a06842d41003006440c0c3d1420109103080c16200340e8041c1c0e00c00c11241c14006005c1000342603034504034803258101078094803029954405c1c5030030703140c01103030071001e02100a00d4a0b9544003888000d8002228503903642020707410106198071762140401714090303d4081030146500b04e81e17a00400e00155000300c001c540b041c800142c03401a4012803500026405480c2c0c00101e0700817019612820840001501c44113414403929007920741103410442401440c0d00c8070340e8001440403c2c030101d04040a400c12140704403442c00710540e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 974796537 1250 974795287 974795293
    0x6120f17070c030606050420030613050c1908040b04240c0e09010f141011060a050f1810110d09240e0d0c0c0e040b07090602010c1407060608 62
    0x1600b00103102d625007085074891082030008a5845040008450aa5200c1c40e1000101190b102c421040d1a00441c0d01840041001e115124008180f000f15002101c0781c2c80a1500000d0349003c0b1012407036110007414180c68071038407511301607585004440010b040200880c02e880d4007076048420075625003448e003802420070041d8140618008010000499403c0e004554101c004105c13140b4020b850b80585400c0103408607406000d9060104c04610050000100104420025504031088c070110340a400d5408000c00c150814402c44046000041d041c4000c0c01c0c0301800385812540d0200e10380b10b40c200300740d200240f5943d042014010500c10707064196409490456507100304034801c01c4c28010b01030002e080a405881e1842c0050071075840b602050741c10390081c007203009010700c02c40c041d6031402d00c288034158400b641c584301d041010b04240d800300d4000546c0000c000b681ca600c0a003010041040e0b02c024403482c2d4a000c1c001d0902d9000701c0442c41c52074030000d090402d010b0160000303001441a5012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 974797787 1250 974796537 974796547
    0x2010615031a040b031b030124060905090f130f050601080106140303090102030f0a0c02030303040f05010f0c09260609030417160608150306090d020c0406120f17 71
    0x300400424401c11400340c440002c0c00c40b200c49003028813488400c4140074000300f41108003c1c0000c226410501343d05541903498016a0003d0f0b0400c924040c03034102002c003400c240c0c80c20041d02401c4281c041d00124084c140020400c004000188440740e005081a20303100c00c0e100d5181001400840c0407a0007a002c4d12801c8000142c0c640305501c4403048540c0001c02c2c031707005201001059241d109040e2018010b038014800c02058080c0c1400810f105c1c0058204010b040010354042421504220340c00d840d5074030b200f20312006106081c0030342044d041e010071080261f08402100030b00800f01da806064546c4607420400c06a0500d0084410355489440301124420300d4403000c019030700d6006001b2100404108031800c1036009c0300041c8461070300c2a0035042c0103920700301013045030b03a0301000b08041c25030142607010b42820746080c030849002c0c4480c200901844803810764040e140464259a06004520b0311000300401c8800e2280c401c4959480199403c48480a0410036041c686a860244071580c00142c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 974799037 1250 974797787 974797829
    0x230102071b051c08044b0e13260408010902010207060c0809010302030c1612080612104101060e06071b18090c080a120807020106 57
    0x408011202c080324408004207006030f0140380c003c1c2c0d9140c0148641000d02c0b0038007040030102001c4092480342d5003c2d082400d414210f0903207891544020b151030407500104403642c0100051050301804100d40c900785281028003011007881c10905019081c122002026540d01c103010104000c85000940e210b500c03103403100d00e4070f4000c00c05807034100d000d449030038000141c0600504c211251182c000866a007040300f000300550103980020010004039800300078407403070802c1c00007044140b10701a000c0c0264807200d04101400030a000303821584240e080700340084801c2c1002503850301c041e40d50030000c45c40000e5400c0c0711401c0321400c0092160840045424a44514070030507882c00078582c20466105a681c0714410fa545001c214801500a081040000041030040840386400388031403140310a002c1c1d8900b014034000d01c01503100c0c80380d0340d00c540b01c0409000345480c0c0d43c0090041c460160455446130b50f00c1010114000c2041c030140030b98000010781290003036006500902000b0822010f5126000d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 974800287 1250 974799037 974799083
    0x31c030f1d070801050f0103062a02030d0f061217070b0c0316170705092101020403030908010e071e090203040809090906040b13170c1f02030423010207 67
    0x8110801e244074400000860700014000c49000f103201c1d40c045c42ca56425600c951019002000390366403461919681001604a0084c40040d0040309030702454071a01035a0428081d203555a00c240803540c14040b0900c000812908054200d5500c030042030844041040f0010260055882c0504003400e03420402514010100c000d51081519038541c2100d0600c0c01401d0315840c02c0811190013680705240007805c6240034600622400d18010049010f00f9403800500c42001200e0b0030460f100d07500410200100340d0801584800350074280003e200813002070100c03c0d5600f00d40d10803031a4001d00d011591100181e0f02070054041d00c00d8002c259624501410120601d50000c1c450340d0045d11000c0003d004610007207001c90049501100310105615180440c4182111400b800e46910504c590044041200e820041c40003183c2c09020780b503250040d820341d10010485402e0403d41078010000c0100040103081c9050034005601c4d8000c0c20904142e40482c02400750b06c2006103590503200e00d01d84180c07024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 974801537 1250 974800287 974800331
    0x50108060f031002090310020d140f0907030f02061b0c0a05060c0c010f09030f0507031713150207171e0d0507080f0c030313021f1d03150a06090b0a05031c030f 70
    0x100d0302c4ac42940b95121100061070040341c480290b50003d50081c000185c400b10040e95003400240000e0501000213a000d840000c0400001c990794003030802220942003250b1031400904040314a103052000d8204500d0711903110b00407941c1001030352200e120846016180c4240515000018038100c0c18071440c2469481c60240015940783c2211859450a00f8544c4200c0b4520000d80c41304c54402890420403195180c01c0580e0401540148680414015030302c4a0440b14070003250003d01d800803143d07844080b152038541c86600036800c0440c0d4402c000d41c20901b1241c1090348500c91560380e2440e12610303142c6004c1c8440321075243c0000010f209090740c0c5080e40d2070240e8022261540050041d0143c3c2800e580000114030203d0301c8820000b48551600004200e045805815a030030700303035160b032403c201c0c000440d03010707900e280d80703410520403c80240310304004424151103034410703207081c000043d549a42d01d18943d0400003041420a5040b8425003010041d03605428050050b21110206c1c81030078908 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 974802787 1250 974801537 974801561
    0x52502010522030f0e01050c010207030816080721060b180109050901050a050405040812040506040c08060105090606030406060e0106021b04060e0610020c060f04050108060f031002090310020d 84
    0x1604002010401440400c0144141d264894202c4d12465040a035604407507061100d05014007401035502c0b18070280020100580b080c0d1b1018498030b003041402580c0c09440c0c400c05c00b0002080c080000700c1345c208a08290f031114000008026001c40d10380d800240c65990071a48090002003015424440c45448158200b50241c03900030700e894590044c440c5a170700921070f6035480441050100000d05182d80700f241c100d0300030100e251404a00016030300c3c54a00030380d0100d40c2d41c1c4c4624100306c01e01c5411091800035001c0f000140000d5450000020241d2402800c1c1601c100000408603080000035131041c00100b80c850640c0c582903961790030282d119111700200c80e0b9010391250040c0304600d00741c450304003585e0140a185800d83c5802c4244502404100c000c08107511841c1d00c40c1500340e407128050710400000302e81d0306940d1403c00000620b10100a0032aa000e8a0300d4180a0b115075408a40c4034602500c4490058844880e030000900e0f205036044448e02e054400940165144110340207020388101c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 974804037 1250 974802787 974802811
    0x120615030b090d111b03030d050106080105130c230c0d0f02010f0204080a06090213060b180907171e040b011703041505090a09050a06210302030405040525020105 71
    0x110039904258080201e003019007040202408040f020000605c8090016040f00e0400c00d0020580003104d00030382200000c02c0c1e820740100924035005c1c202c0310328248088414080d03010100f00180c0440b16804500c1601c801d0b061410301010308074003d071104503401000721400b89100203009403410101241d110010750a0801814882c0124000c850840340481d0050521482c01d4072180d0003001034046c2240e104900e401d1500c007110140c0100006481014441da54514143c0c8450940700410318910340203024000c2088215900458400d40711040301c485d00d012555240454103510040702c0400c1c80c194540c0b010f1000f4040d03002880e034103840c1442a50106680c80544403552400380381318000d46408071450b1176914170711500181c01d01403805000c3c11081d5480b11040c000f541c2e400c40707045980aa4a0b1400c0107032010042a00141600f007011010419042d40c03002901c178071036402000d02031611000890501c441e80030f520001ca00d00390b01411052203032844024044d0109860f0445241 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 974805287 1250 974804037 974804053
    0x706090b01140604031119240f0e0108040b0c09060706020c01050f06130c02010b10020309031002040b0403060209030a1e030e010e01080a05070c061b02060f010f120615030b09 77
    0x41043c1d0201c1c0d065a03086019541d01315140790130810b070b2000804402d030341d45c001c902d0300003104529004c01400c2e4030180c118078681c11200440c02860420140c8041c0b003040b80c1c045a001141c0d0300200c519410030b8020301030904568030144440a584903000f9031580080002036014103100e410fa02030004501030400a210700d403501d403070100c5510b42c00d0340d080360f014070807449200400360564002244e1049030700010483c1e119440010f03042c800000345800140e000065004c4061405020a0041d580d40c1f02c41182020300702201584580980d010003004070783e00040c007000d503990410141c45d81c203a0000348503204d0b816070b031320b094550022000308030040323110390101c489550b001da81c4a00c0002d2040e51000c046a480070b0580d0060100604880148014048403c2c080380090007950000c4e51a2005600c03541c40312800207290a0b001008048440501070040c40b1140920315104215214512400d4032042e4504200380105503800039502c01c2000001c2c000300704460410b2051241e104002512058 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 974806537 1250 974805287 974805289
    0xf07090b0a0812161109100305060a0c050405041d011a1203070201021218030f03031006080606092808010f1404032012070803091204060813080706090b0114 69
    0x3d410728628008000005004800c80c50480c0501d80e00140c1c05010700d441c451030740b00c001ca840d00c40305641000c1c0d9000c0d1a01c0903c1440b50400c4090380080d2064800c100316903040b00300401501660042ca88950340f200300c1c0d4450003c41e60080e0300a008110000c0000400358400842c4a49988506a00070325807440c11481071040401680d00c01d0781c041c1c02800d90042c40d042100e0080d4400e032108808200051a2040680c500304010004124074200541d41c0c0d04000c0820010074505600513010480d040041065640f210010394440351001e1302c0e0581c03030100d5074420311841d444100c0100e11403e4150320005008105400000c0b101140ca00c08000b003642c0341122882903c0c084038040c0109880710b6003d1050310742c0250700c08001d09034100341c4181c98130401d6100a2a80300d02e070f0588040c40e000c010301030306903400d02c003021803d000d2244852130245003a1001e858144001c0004414010208104042c0840c100480748025400710302002504103030324001c482c4010030700500c419210303c4490b043e12 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 974807787 1250 974806537 974806543
    0xf1b030215130c12230a0b1023040e07030201021c02010e0a0302010213300309150206160206040f03080903071a040b31081204200105040e0114030f07090b0a08 70
    0x402d600704406000c00c2c1c2200c1d2a80347c40d40a002d010704407028211000010580c04d1090010040510610140d030041300c1e040c2000150740c40000001d100d60498102000141e80000e01045510444280e5148602c511402680103001c0b9210360011400f844406104050303040d03005240010700c03a00300606060701c0e02480802d4000c10664a080805056010f9071107a102040450600d0f1182c6000d60f10551202c50120348552001c0b441c00160f8400018040034400d0a940902611518801000c1c10702e1f280c4ca8400d0300c3c00b14440090180680f43c408030300b49150034011901290f401500c442c41250041c1152030803840100c80681d100440000821803480302802d010001c0c0b51181d210200201e84000702007400f80140c0310880304110200601c502991428600c24445c2d4028104d031020211020300050b0b1020044004074104030082005028061503e0806819241d51404800b00350ba0200d012a03d403010034000915188550f0000085440a0360410600c078501030f01d041d24002e54a403c2155 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 974809037 1250 974807787 974807843
    0x4050a030506011e060c02010c02130f0623010e100207050603070f0e0301050603031c0609150e0c030c0d0e0f011b0e03120f1312030f1b030215130c12 66
    0x40046c1c1d00c2c0c103203038000d5031151b00352840b254002014600290b00904e1900119000e1000c2c2110013515110100250100d007090560041c000e190212501544940020070218405185a10414240d01002c80340c07442005090080c00000d84040d030b036402d22540c06002d184031a0007100000b0000340c2d1051240c01c0c18042e46002d040090020360502d6001e05004203c101e0340101324101944d1745000044203181c600400300100982d00d80d00d01d0300d034180700700000140c9000f4103084040030200b0600c6898115041100c0d00d00065100c0003501c1240b0300d010341e00b810b61100d41400103600705590f00c021300c02e2451100007035641d1611a801c40c4040007040c5600c605680e462004000e00c01d00ca41001c80b00b080004100c1c80b151010324042c802d85448ac002c5107451411342c25000100740045402e885604420400c1c600185151071018622040c0c1c0c00a50f41c10588a00058001c07000c00800d028144892050030700990202070406455250071a0a06101042d00c040c1c1d04074541c00e50b07203640340b1001788081d8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 974810287 1250 974809037 974809049
    0x810030f0f021c03080103060e030d0f0207021206100302040c0c23010b0a050310050a0905160e13020906010e010e0a08160e0717071803050606040f0b030d031104050a030506011e 78
    0xb41c03141e2031908e940d0700401c0203164120041c007007040711500080062050200000301102c00580b103120b00c0c0103101e40031001040320407040c0c0c44074041c81485800650380000b03ca40c11030340813511001c8103c044031010540c0b42d000f4104c0c6007541c2036852100781707543e401d0104030060000300b00304c01070041000004c50a03807060030f405402c010304200c404281a000250f010750805404070b86141644d4406242003a03030200300e48480038005050152a00e40c00d8100d070004c410115503140100c50380c0004010345d1000c4c2400e414014000c3c0805042d9014400c100015000140704501c240c1c6c4e01d11640351592807403240c80120400c558408103d080e0380030390780d5005100b00c3c0e85044070b650485c046080712100c041d00349824172080002c001a14481c400740080958400c42c00341801d41030002c24070003a6207400801030302c201c3c00c1c0300700540c5136100080c203000041c00740c0c41c02084416003e9602c0c2c08038800c0d82c2060350031016000c2d020040c00300014046c1c1c100e407010380f091051880d804501240c800321030f008007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 974811537 1250 974810287 974810297
    0x80d1a1507030507210f11011b0e2101060e090d0c0308041b090606020f010b090a020702040209030709020c0d05070b010510053907030f030810030f0f021c03 69
    0x80c00442d10501c0500b0220784591845e013482880a10051505c81780714880c4800a070701d02c001001203a611a4100d0300c084a01e00003405616400503110b59a400760341507030020040100c00e00505036841c014401030048015503c0c00c041842100820b020300614020f402c8031184c09008262000d034000303410f00c120500d0395960b01e1f1461142c1d404440310b04000d417007078400500d58030000b58039029070355202c0c008080506002038907503e401006424400179214034000c0ba450542e4002054803425400c40c0e010365222001030307480205100140080c0100c6c0d0003c2c5c0c1500c40d96402050075003596009021030400c000860701c6500600004031707820f00c606003008010008150040099092424840004400c182070050802001c815003040b100c09078804101c07071500603420300b11581c281c00c0345000c400c0700c0440680b000703c0c1035440b0b19500c0c18560f00c00800b001042000207400c200d01d01c106401075948010490102140c9040002c01036010200692080240b01d283e0742e0031a407100c005012443d032581f24 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 974812787 1250 974811537 974811547
    0xe0606040e100321030c020309090f06040f090501151a0702150c01020c0604032019030302070212071d011409060613240e012a080d1a15 60
    0xc0003280d002800d01d5480c40014040800080c4a406801c1c82018a200b00c10350701d41310008008040c0c2e413941e0441d1040d0b400c00c02c200c0e841c548441e6000d590009800c0210741003904c0e0100410b0007840120101d00c0003500c0d1070084000c109064001d80110040c402d415540d458482c0c3c140e840c01401c14800b0301203007200b04071100c018240341c1300524101c01c030b0f44101800d1020758492a400ea9000b8a9820b2090b04054100020140c1041500c180c20907802c1650511070084e000c90b5a407a1114411200d044c00321524074402c06110740c04a6001d20b50207400c10307405007800b46a507030750748040703000f40745105240408040050b90380805072070485003051481804480032005110304044054415504202c04001310324074050b030014820020040134410846035101500300d8840d8000740c00761074040002e03491020110307a034480d41114688014002041214039070318401c0186d081d03503000c020700104001c160200341c09007544c0545040300039808440d41c0506500100104007600c0c00280c10b0b55101030207 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 974814037 1250 974812787 974812799
    0x711060901091a1b0c010f02010e0a060506060712080906060114070204150902031504110309150703020c2e050103020a060e0a1d041b03020a12390e060604 68
    0x140401c1c007040d82e01c3c46146005001d840140180004082c0e6642c10340c06013090001a5038010034010a003c0b041c07008010a84c864540315485904802018210076140c102061080e81e5001c100c3c0c54140c0d1003000e22211000c00d0102074070110040b01c2e00011400f44000040302540210032012141e15401c13060f80c42d0580c240c0c200402002c1c102d01d498208800c1102c049100c6c2c84030310003180106013070400e00c240c901c000810401070f40c51407107042500c02810300c03d1000c074500000d03c052700440c0221010200e95541c64045000340204403040d007007071060315260300d241c11166911080340305481d9a403035407510703140079104103480d820b100094200300a59001c01031944240c82d05414040d00800e4078202a50710201090b40c0c03102080420319018490303007880100452024900310422044900c0200c05217140c00007494a681441591040c13542000b01d8001c11440c0c5c21206a200c07403d40d03482603d0004400700851080310340e02131050003c2c010f0804500e414845040c030384150002031040349040e017410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 974815287 1250 974814037 974814059
    0x3020f06060904030f031506350403030203061203030f06010f0216090f0b030f010c090e040f0201080402040f150e0c0f0f07110a030f06060e0702030327070b071106090109 75
    0x103041d4420955252541803141071940c04403c002d1a09584001c1e035102600d00b00c14590310710392748489000a40180381c1646038508c0e02880d600c80c0d0181401603c9640d9a0b0106103400d00340e64811485000000030400c95140c2240041e0080c002a41c4502a4500000040e81d40300c5a8007480c03846044100410006800c29401c03101640c804000081800d555100100380b60601000c0c40c40440d9444542c03400c0042c1d13000b60010300400100b40601c41a043c15155006000c8503450040d0401c607403e4001419902c56801a0010081100e0100005020148100c10501da80d0280714410710400d40861154040d040076519000c540c1646036140c11501158440d00340e0110b00111543c00c0c031000c0b0300d203450b40c0b2031102c034004500500510b0340c1c952251400004071103140d044103015400100500085907800401c1d25446400407007011440f840b81541c4200700b503040000041940300b00f10000c1100700f040310181210610600c4c1c8a1307036000055080080e68060100420300090310fa801c1045400840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 974816537 1250 974815287 974815307
    0x14030a0b04030e040e07141f0f0c0b04050a11033403060e03132405160503040902070c0504052208190504050102150c0d0b0f0d030c03020f0606090403 66
    0x90410f16054840314020800381c90a02606042e5900081003c0241d6450806200c40d20241203442d5407260904a011b641c0480c1e07a03070000310070820003125040c0300501910010750001e800100c030000d185060f180c654dd5645006208460329155542c0101c0503060016088040410441c031140b20380703510000c0f01101d110044130185901404031000400310300b151252100812800c0d014654500c00e1413840e15610010b030b07014000f8030503114208514240301c1142841090300701e1508681e1008031900b11000c032041c1d200041c0060100140002d0102181c3d4003e1035a01d10031070a100d8190380d500d0402c0304840c0100c03601000d0f82e000c4024000c60036810342d0034400c0781d48140401d9003851244264014032801402010011880008003408a582c0401404100c00e414610080e01460100072041c3d03640258440b07122020385030038240213656224112950400009403c41c0300310410341c140240040d85250050b4058010142100b0100c100403900030321420002e4030042941d102c1e075900325403440c60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 974817787 1250 974816537 974816543
    0x120e0108040b0714190804032607050306130501080706120221060307080a29060d02010f02030702090a05062b0807061b021509030a1e0318050105090714030a0b04 71
    0x100513228007214000c0d1052400c05c00f0ba520020a85414074020b08449030603004d10001c0c5a503148012184110300048030341c8207500307141954580d242c14000c142d401e1052440300b01c149007044008518458002418030841d1855640c4015014a5801541c00c84c8900c540c00c980c034240030480c0704945903500105941011000e812250b00694030144a0b040081d40751007100c0341c6a480d031100c5000340301c507010300b001281410031000040c1020000980030540d05036000341800703000c02c1080745842c002d00c01e5600098016001c03209514011031602c00074202110401d1164903240c084403118449809220081d011070013141c140e584054603526a02e4000700400c0318010303140c8003c80e400075080300c0c06242c1c80301d00c0c0d001029021200c00000c1805030009207a20410741c801c2c130110480301da000605030848140c580e0303c640c40c89906c1c8012005041a040c448000802e0082140104841507014600c661141426254416152203a10b000300e2411505d265150344001c08800124403a545a140c100d88 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 974819037 1250 974817787 974817827
    0x3011518051503060115080c0c060f0606130602100e010c090614040902040e06010206061009060c0812010308040e0c04050d0b13051204030c0e01061e0504080703120e0108040b07 78
    0xd66240003e15005090300484048606d041c13030b01b030b4050740154005800100c010401d13401c001d00e903040f4580d180d034024464104507d5080c042a019180c810403141d4403c01d03a000000e000d512050301a50f612030008900702401d2821281028504c818460b24a5802450340c2d06080c032444d2807401c603142c5031207854a0001400030040020300000c2c4d440208000e000d0340d094218603261260000e0b0900340001c100d00c1c080e885600c0b840c2a83c640c4030485205407051824020125400350800c02c2144c029489507000340702c52800080140b02c8040003034003c4405809140080d55121284c45036907018601c1041c1e0080c0708120311000003208030130a56031003006042d5909500b54907403142c82c0350101c03800e0814a0f20b000040c05000b03010704101f5003405000c2c480003044480d450204024020f03442e400d030703011941e004200750310051071085044038001c0055804581520792a4140750701c20004811000c3c01149101d00c5034542540224203561040c0d80004050203a640d5010050300d04040400e1000d0b0850 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 974820143 1106 974819037 974819071
    0xc03090918230316060609150807090c0806151303080322020315060102070e090d2705280e01060f050304080414060f030a05060301151805 61
    0x4d400e4488141c02c0c8503c4e410305900a20141e0003c940303032130800004a0b0396142c503013144015581c502050340d40320303075442c01c502c000c03500c0460240011442000000f44145483c2400b83c407461134400400c0d00c2c1c0041e06200446031a40d5070011595108040140100180c0401c0c81e40e1404101108a019035a03903030700020b944446003415044460240b400040e03003a4801c0c01a10004c2001400c03813131440c14110305071500c4082c0e40c104500000c0c85141100007816031800070000c007074400000194030030300740014441c0a51601140ca50340030460a107246000ca03641a000c8000c00207518100f0040d410040024141c2510540200401c002031040c00046804002110110b0381441d6103c1d412091380800718003113001e00c1491641c41c0d100482004543d598a0b0002c9120340c500310f008118540b4940492003800b00c550140040b4420305014241011200d40e01440d00a10043c0c8110008 = true := by decide +kernel

theorem cover : BRFrame.Cov 974640287 974820143 := by
  have h0 := BRFrame.cov_init 974640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 974640287 ≤ n) (h2 : n < 974820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
