-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0528
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:16:23.140996+00:00
-- url     : https://prove2.me/submissions/46f555bc-4146-42dc-a746-4ff2e345e256

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 94784173 ≤ n < 94964029 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 94785423 1250 94784173 94784177
    0x90612070c020102010614010219021804060e0705120307030f1e05070b0105100c060b130509060402150a200f06090f070807050f060a0e0a0603090615030b040f030c05010606 76
    0x6800c007411542d0a0142000600341c4408014001034440d0000c3e4840d0000200501903685102a11055680741004100210545001003800d4101810a48060040003031050080d12508034002114203102e480b5089007030840003e5410030070030360f40031950640442c0c11071040111500c0511103e00000b0b4101510b400103444682d941c03461886e0880103000144e1141d4030480c1d20401480da880e4020380c004450035400080041d413500b47d10f0008050001c1001584000c902d02010070240140c00108940035038022201c0312041018104200c40c1c61043c1030b01000007131011038190318013003400c1c0e420841081382c101c00c2c0c034500c4a03850211407401c481100d0491896003c03410354081e14a09010010191035820301510371242048045000c5caa40078103454000c80002684250180c412040c5130921030340104443d180075980c42e0010041e001c26041580c44900e810072481070f0f01c01d583c1710082284e030702001240541e41d85858038440380340e034403109074240207804c10350000080081c898080940096 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 94786673 1250 94785423 94785437
    0x1d21071101210c0c0b0f04020102070b1e07080a02160302010e0d03030b100f0f0f020a0b0a0b280b1204081c020a09060807110c090606090301021c0e03130b09061207 72
    0x6090030029540080c2503c900410f40001f40400350742e010466100703643e04105400e41d9507200c04203040c0b401001e40012842c800b00491920304020300e940040c080403030345030300b158502c18108100d21544011440002c4c003040700c51041d4400350414401c07004110307000c2e040008026181c040070440200003002c482000070926a8a01a60380e004101d030100703c40a031410384a40c40c000c20000e517503183c0016000e0200d050420008058a8003a0420b51540300003501e030252807020560710030660308a91000c0319441e2400341340810400b00502c00d0702c034040500001c0315050b85643d04c0310811079001c031113010030003030440301d00703803d4054180010098005142d4401e11410307d4030740000c252480141c1100304000c07000603401c000503400104040c0c01d0030b0403900d44070551140f50005203c0d200300340705190554008201d0201107810401c2c20004880c548100f4000c40c1070300381c1c0044d100d01c00d0b84d400203c40d4043c06000c2c00340e482410094030b0041302c080c06552400c071510b801c0b02e82e403906c01c4071408006440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 94787923 1250 94786673 94786697
    0x7080403140312040303090f02030a0f0b0703090f0b0408090a0f0513020c060601181a040f0503070b03040b040c03080309062509030f02041d21071101210c 68
    0x1400d6410002500c0301c01c00345041600c40c1a04a0b81042c02400140030507032038511a00601042500c030707519642d0300501711003941405103480c01084054000c10740d418606000000d450600901842802c00d520058040e10415550343e042d80340c000c040c005031103052041c400340f9500c1c0c503050303000c802400680d003841c0c007068500070800031108030304054210000c1c014030480d9030304140004c603180c02c0102401c000c1442003440c90682c840b05030700e40c001503005031347d01e9641081e020303048001d0081e100890707043c10549490b08189540c8444038428580040d40070000030b8042800d048900d40c00501c02c44500d00318590f03130340b10300b283c070703002501c1e003a1441c0c0003141400008030040c00721410800d452011905603010558000c0c0440c13156220141c40f0500ca001e4000856a441d44610342c1c400e000040315145840141020b40c0e158080345c09100c100d030000c1c00d000310a12010b01a10310f1154480e00c0704680318100401103411079180403c3c407021141c001c40050b080f080c140038003200300550f81d880c0d044500d2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 94789173 1250 94787923 94787933
    0x702070f050d02151c020f0c0601140d080f070203070f0501170c0d02070302030d0615020d0903120e01050c0d02010b04060506040e0408070302030c06010608010e0c09010906110106030807080403 85
    0x4590341c00300e40b241c4002402030006888096140b94290425044607442d500c00c0d1241126400300800404c01152000400d001c1e080d96500c044c050b0704034880e00b282c09980c2c9680d58003080d406c50521140d4014100ca021070300103100440144036500c040601d0b070f8102442070780407915180c1d403600310020302e9100402c148055640b0a003001998151580034600900b400040b0741e8540c869420003045250b0000341d1042414020022544480c42e0b00900b040721503501c80044c0e0100ea92031b000d40005001c0c0d554841102e030b21403a00c0d80d094039080200914401d8440b0002e50328901e504180a0500c0400d101c0400050700c103010080175091140c0001c140703403010f807003040100c42054018a00c100c40c2800306000034000c811000f0341c4140d00c101c94036640e0099043c2a8030b54011083c0310309440c80b4102c00402c81d1503100456030304a40f000400c071981f0351107103030f0040c8090185e05507181c0000c40030002003007034038458200c494400c842a0000145c0c0d030380302d86420b030059000000030340d064440040c0030001c0103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 94790423 1250 94789173 94789199
    0x5030d14090a0f11030a201002060906060f0d050a03030c030b12030f160503070804030312091113060f080105060a08010b1e0a18050a0b030c3105070207 67
    0x303010401610071041c66588000ca010700f0030030003500e051081145000c441d01e080101c5a1400d0300186040e00811910101407400c07046101c545000300646241c40041c10300004030540100c01d804042d00807507880c1000d110400c20707100c18081e80501048208dd0209805003c907400140c02590701041c82d1281040c0503003601d513000b440034010124401403004024010041c1c035810844001034950f607a80741d000f0701c0d81092901802038a0b0780800113401c130400504600401c00c5a20a84030385010118118401c0100c0c0d201c20405000e920204d42d242015161421200002c1104000d00042c0d1640b603200b642004070380c940208145a6640c001d201451030720005010051003090001d00412907803002081e414071a4400010b420700300c560990115035905190302d400382c150003120900c954811400b00c0080e02c800d81e0340c035042e2440c0503205060345c01d01040307150351600051311134001c0901e00c038041204100f96013441070f1441410740c90703044504140c1c0140c1d4010b00e82c940c000c040303907414440048410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 94791673 1250 94790423 94790431
    0x7061a0a050f0105040603020f04031a040501050c030c03040f21020c01020f01090515090a0803070305010512010e030301150203040815040b010609060e040b031510150503090c060703090305030d14 86
    0x1c2c0d801d00c40c0904090381d20100f154280e5090f86405a1140c1e80760b20f02c0005400f941e000108034032900d000c611440c1a12000d00c40c0300b20b000c0c000a00c406d803580c43c800e9519110a031541061000d041001801040502c00408201845010a50f0307124414140300d0030540082403103280148c02c040110741c4c49603070410000d249029024000c00454001d07555032540d0302d502e8000700800d10030100018540e1031051103001d401c560048012035691400b018010014071b003d005282c4902c01a00112411000502c14050007546680c0210302d1a401c041d000101e11400d80013403000c62008110101e694202403103000d90310400500d04010f6800d00e45000c0350ba800d0305802076001c10026510030040300c1d609c41c40100b200702d0269030001e00c460031800030030300300304140d030900103505500003d01c04040282c000100441d0852444481c4e4600300701011503051105a8000703070254840304013105207280800c001c2400302d20901b001c1000594030b07581c182c1190082620300541c655614106030321080700d13462103644 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 94792923 1250 94791673 94791679
    0x9090906011701140703110f031504050c0c070504110c0106030c090b1f0804020103020c06070c05010b2d0604050a06030207020f0d03051c0b03030c07050a0e190b0102010207061a0a05 80
    0x38204d451542c1103024020104d401305511607207203245d0003070780c68111100548180b4030b0550703a20345a000d5890b510056119503000b617182c800041d803a0a09030050351440041c07807018204e90f030726003070422000d0702a19800802800c010000440b0200d8240b19182c02944102c84950020b1710703100ca00302c2140e941c1d140302401340d280401150b804010802c08000322084508100c4070b13640740c6000490080c0900304400129115420502c40c20381d800c0b40c481c1d0b00c10b5204500030301918004005000340300c010a0b040e25112160400340c42420341d400d143c40440c0c2400502041d090503a641e0004445081c0360f80414040780d400a6441c0c103600b0040c00d120040102034940e81002201564020420320901d03041183c004207240b00392500c81e46603004240c0700d800003011280c8032451329610355101c05491040e02d105144054000600e0010075040c90b00c90072a400444440151090019010f0500303012003a04656080013458006070162065800d0a00a003401c00c02600a200502c403034640c440e00308603c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 94794173 1250 94792923 94792931
    0xf13060504140f070807020a080d05061003020f18030111070f140111031f081c090e0601140703050d020406080103020f04050108031b0703020d08070b010b070f06020a0509090906011701 81
    0x810070059454001a02c1d245c2000f40383e480d110100e08100403000c00421110f00021003100c03611440d04494043c0b88200e42d940010414800150220310483c0d1800544140c20b0052040110142c0c5003083d00d0140507001240418540d00a111a68800a0b00f220300d280e00c040d400040c03142030b01000010224200003003044d00c412010745085c6000080840e00c500140908201006010118241c001c142d80d070101c1d422859a130403050781d48104c0203641d0000a079549000989640e0501c40603015250607103ca09400c0d2a01c03e01c0c4006502c145029002e0140410000c40142c11a100a2004207810350b11490994150300c100040f0070824201584902d00f000014010210080304954904150b0405010000c2e00c071050300d07040507030340d41c400ba500590500001060007002002800e0040c429a260400c583c2c95803110010b6008104016001001001d614400039805600401c0142201e040c09401d005c00320f00000c1e5840c05c00c0f54021516080000108200d03512210004103000341d01c0020302c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 94795423 1250 94794173 94794181
    0x204080f0f070b0a0c15020405010318021c0c030c06050417240924090d140703050d0b060307110606040204050d1214070501060806060a050d060b0f1306050414 70
    0x707640c4040030300444144010001d52520094055990402200d070310030580304071000701105c0b6500940091040a01090500300701d840404c012081075402c0360f6005003082d486201c4003000105144081400301c810920012000c0301080e480c00341030000305900e40d9550754440c10910180c4413004440201c10007a440503044404010b03441d1485004a9040040c1c420290f80f01d0802c2850102c0021074102c145200c0c50401c181d00e15aa51420310070301004044039518002c1c0002105c4880c11003007400601003040c4501c00000b44140f0081c081822701800100300445400006259684207480074808100ca5529405a941e03052101903486a0103c1d02103062616280215041c4400c106004160704025107400080c0c0b40140b00c40e480b01403400030825121040c61418a0081c103490090740c002c0c1c420070000518600e02a04c120040d104040c0a034408a4113a80d03480025000701110190f020b060a0b00318161502d0360b002c151003034110304102241251030001404200c80c00003000002001d41d80e0100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 94796673 1250 94795423 94795453
    0x1b0302060a0b0a0504060f090e0f190303090b090313060306050f0d080f031810020415031503080a090311040b030a0209070c17070204050601111015080609010204080f 73
    0x1156000c520101c010404440074000074520241da038120652191400b6404101d0501c9100e000c41522081c400070480c090f105591549e03204041e6141c0c89440d40596407003035090860b0300b000207001e0701ca4100480c000c46150303a0072203440e4044410407407a50010400344004078204400b00014600c5080401081d420003002c61920100f41d0441802011004681000c001740c2c2012100303210410a00192a42801700b04002503036400000c41e942031051801d01101c0440d50720031241102d060002c1d4014410488509601070704601e12042c008401030540040802c0d804002064101810f03175800343e065045140c00800d407101400180d020340c3c90203001e01d02a4030b001400c7c1021365011200022995195842111584091000180104802800b10b065522200090400e680c03080740c0901c1269104401100c2085015451081d81e0f44900c1c02ea000384a095848505651803e15001e0490354a0b90000c1e40b401c00b003039402583c04d03076001404002042040c4201c00080c0b440300040c0042010800007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 94797923 1250 94796673 94796683
    0x30e100e030d0e01050c120702100e0d0f020303070501240f050d03081b0d02090909010b09270303040804030c08070305120d0612030e010201050112151109030a050a031b0302 76
    0x1210b040c02503542c1c030008107a01500580e0000390740c040845e04a0814039401056a801400013223004035100c82c440c110242c0150350002d151130b00a00600d4100085031641100101c1918040e40c060104002c04000706070203010300c180d05a0700900c0300e03d9203007188018850003070559120040080c4580d90034442a0f4074048030b00e102c95010300e804c401a8851844092901d4883c1d9948500c20100042201c20018181c016164840e070880b815105030390341040f900d0903141c0004078036a000c0301d2000059001200e02014a0034990107032506601e0040010501d0301d90b5000742e8003562801d5000c1000c00400404280c2c0c00c010b00036a1028068480c90769071203696440281200513074104c0c000c41c1c00c0c4c0b080c9065910200c0201120070184c0402da2150501a01100301d8202c2140103500381030010440c1880394008005065126040e00b00c1d4021440e44c00d00100741d801141c1081d240e0070007400510b0341d0204a8042e041e40100c0241c64090038510f40548030611100d505256030818441210203e500862 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 94799173 1250 94797923 94797943
    0x3030e0d0f0b0c210a060f060e011d130209040e01020f070305030702120406030f0c110a0201110c04050c0d0e0a020d030c0c0306020a030204050a0506040806070f030f0207030e100e03 80
    0x41114640d0702c50802c1c12119004d0013401c0304410901c00d8048840740c4409050b035018048030007040103500d4940d40800f1404420b801880046442101000d4295208640418290480b031140350305000c1045d000a048a520070740c0994103035004984080e191509208420140020754003c618141c00c1418148480c010303200c014080c000084005a1040d00a024465805003655850303079803240c0310380c0060000e0040e01d400c010031380d181c00c2c402c50007030f070080d82402d21001d09507000705418400d5900445c0c60500760484080c2c00d00a104503454035841d030780a118041c17090b40c520a40c030381110400a00c00c940041d01c8114841d1f01400d6000c0c05038840c0490760610f035030945802e6007180c01c64104503082500a500c002e11091002541042c51076056001d0410380c0e40848800c0011543c41003080510b01450041c4a0142c00940200e0601c2e8000c218005541d10507080200340308900c00802c0c41260001c600c10341c00303c0c4146c4000d9034503160030420341d0701007021401d00708510b0340e00c5000701c2e540b201500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 94800423 1250 94799173 94799183
    0x60c070f050109061a0103050601050405041a060409140a05010f051203070b09160e010803121b210703021315030905100905071a030604020a12020307080103030e0d0f 73
    0x140000500401000390060941c00000a1040f4282ea10b004c00003800d200c182c44201e120300462403c0300398442c5c0103050068905a48041c206400d02040000400c2050f64110b15030a103e102c01915444020281004042000700002e4440340c0d40b0013064444030050468906503c5c1000600c00301c06075205000a46109490307540740f802406e2107a034a140f003080c4024116001403410044602000251100c5013085d40c96005801903440e5042c140c4528280540303e01c0d1b81040c01101c010110351804580c1c0669009001c0031200e40d40ca07003410181d440303845078517940da210524030386607800d440c2c43d810f0300007041d0b00e021882d08c0c25402c0c0c0d14110680030300964001c9210701c03c041c40102d100317401c10282e41387c20209a5220760010b005110090003980c1c0129550b000b00c0c88002100b198050300c030310300501042c601c41c0c84c507074401040100952051208005101d4084400c3c40d200c1c140d480514171400c05070b1281107440d41142009807604541d68401707071240d881501007100003004500300395446076000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 94801673 1250 94800423 94800427
    0x2060126010f05060307060e1e0109050d081207140d0903090902040b0301052107030f05070b0307080709090b01050702040209060d05040b070f0201090b16030603050303101403010905060c 82
    0x4040184888804080546199800e0880140c451070b11507100c140100340407070807a440300e555003401b035408281c00c1024540c0041003194184210010b140010084003051420340152502d41c00090754525841c4c200303803100000862160030b81012200299002616400c010480a2480d80b42024034030462012031041520707099800c0c01c040c0a51400005030050100c29034039151a03200c906419042449414400c0c4000712910b64901100c000164aa4150401030103101e42144c54240448a0213001180e091143d03200005003000003102441c004c503c540d40390703841c0f0708003030000625016058211104041c9001c44002c8541e8121003200c074810ba0590780582c07a0540000000c449002e030480501420741440100b204112600181a02c03400d01500c407041041d40b15401242200d40500e4004c01c10181c44000c140130000072101e10041021906e030204640e6269a101401d54005070742d0f000c1c180300e100c00c1c10301140c402110710800d500001e600030850310b00c9075111507580b01005843c2d80000b44d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 94802923 1250 94801673 94801709
    0x120901180902030109021809060d1209050603070306050102060f0720030d02040605220b0a08060607020a26030316080403090306110a080f04020d02040b0414011d16020601 75
    0x8040d00340004204080e411920380d80d603980a54083c0d40700a031000e40e002c05201d5503c800f417410910386402940302410071440310900b40e0390400404804860842071184100c40012182e60300720085100300e1442c0c0d00880c0c9180b030940060700c2c002029040c00758501140041017200c40d440040a140411441000f48900584120301801e42c4640c002c1031048600010b000b190842e0404020061150900800b04050450608c0707610140c4080c003450010903c1041510846c40c40341d10420380000340244501d01d062240d0b030000d101103549501086004c01c1401d0034008003490012803240c0309822001840c80c40c6843e050310274221402000c183d0501258001007014580300c0e0048070b0281d0b83c00b0000704141a040c1e0000d1003150030a2660100241d68240000c08d1101c09150b064001e43d40500366a122280b00c0e800c00c0042c060048945030400d6469020003002a030b100f03041402416803111119803041540ea21401441c80101203a505021580000e80d21950004d0700d641103031009081c0a5480341 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 94804173 1250 94802923 94802957
    0x6030424090b010e0709050105040311042705070906080307080301090e03130602100507030c020d0c0314130306050703020903300408010c0e010306050d060e0a0b180f120901 76
    0x1401c0c00361003407000c5800460b20001d0700c0c60807801111151904c02c007072540c032401120b030303072041c1d0000504c48040700550100e06d00b05504103103100002e0702130074180000038004c12075400300030701000d8903540c1c0031000800c50386c047c600c00e9002605501014505d04ae40f680c544141c0c074030042c0f20380304040e40d40d800113081d0002c0901c1502c05200d04140441034040e60340d40c0007941c03130a079070004215451070b0402081d00c49009104403281009990007821000b00d0a8200313035094600360b2016002d004e0703215000303910398202000030180c110380469080072003821810001d0494034014a1542030520403c840d0000d59000540c2401c148a000783c104864003412030b2500b00185c0783c80807103240315400b02e03001c1000841174010300c141c0d0300c403943d5010308410305500440998005200d216003141070581410081401d94220a00c5802500d044445200c09a80c5500d0245c0d41114000d81d0440c1e150080721038a0814050301c1003040750072006050288507010026524442c5000c494140581c0d4403031081c1a079 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 94805423 1250 94804173 94804181
    0x60702030c090708070806010207060801090c0903080f0408210301050607060f0c09050f01030507050405280803090a09060b04050d0609020909030c0d0306080c0d08120703150506030424 81
    0x141c8007400d012001d0030039110140a69405550382e40105115400080c459440003500300220385a680c1d07401d0842e4a0020800c006000200c0100d08019030908080042604240108009488913900c280e07114642001c0c41c4c03c240b0031030140c1083d40c1481102e894210680e0042d24195501162103d075507020381e180c4030b4000c00b804140e1032900e82c00e00c001c5030f02c401c2d0040020411244141d03940102c2880070001141181c600311245c502007502440141f1075420880728825003441d5400007107006050b002c42148201095130702c0205140d0001440ca50725080000030400242401c2c10240036060500b0f800002e00d0103280030b41402404594580c1d0180030094100302c15154002e8103012160426004a9072207503c00c6101a4551082c00d2031901043d100b40b04100841d00c0d40301c05000f0300c0040d07608010481c80c41c01005e8800010910040449140801d43c440c082e030115100001c0030454080124034a49142c1d0060744544000d108000100d00c910716258602440c200f0001000b01c0540c401c00010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 94806673 1250 94805423 94805443
    0xd0c030302030d0f0b1008090304030f0605041505160305070210020f03270c010305070e040905010903110316020f01030e030d02210103080a200d1701120c090213240e011d06070203 79
    0x80c443300e0030043c044580d10960041d80500505000c4102e5081902c041c0c0300180e44a084c003500b10032504d4030592180c0d000702d0f0050100d10595010341081e0050783c059800480c007100e00303801c0020600128a6200d0400301ca407801c4d4007411b091000c2030904064035a601c03440301906050315040000c0384144190f03964410128000c0c0204004202420283d00800040000320081000241c200c5c4003030400200b950700840c444a280700481d109035080c001e1000c400d1645c60f050580304e04510080040500181580201c130110042c1c0754a45058000c0a0104995a41044c10004401800070817003103421202034100505200071509003091010b200082c107161481c01d18010000340c580d8080d4810380c1c00486030001d8200311600e90b226501c010602d0740142c4014005010b0f40030800c601c0d2540c0c0c0140c400b100304010303c040303016a0751030381e503003024546001e8407008505008441c41480d003249101154102c00c2c0b03007850428455031092062090f6040c0500d00c1500041480300c11503404101003181c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 94807923 1250 94806673 94806683
    0x31502090a090b13020c0304180b060408150601050a050a05070f1e0b01050306060f011d0a0b0d0e0607021e0304050402070308060a1d0708060d0c030302030d0f0b100809030403 77
    0x1c616940e0318248014a0900c6880c1d210341c4c038286104410134028000c0e0740c0c0303e42d0400003031880c00340f90001e900c9003110f884440103241d80d12400044030a031b40d80c60180004020301801740c81c4901c20180c0041c00c01800405080c184001800700703201213540201034500402160510070303940c02190605412002183d00c0003803081c03a05a1116142c83d49a8540b0030030b1610501c8420310690301d0713004045c1c035036508039803550b00003020002c0940c0543c86074207280080928040f401e5202e0b02d5410100300207a4640c2c10140c4450000a030181003128a80319456000c0885005081c2c00c1c103150b14000c0d00e0f2900c04050308450140300603030021000b0240100c800130b0100900441d901c09861402400010007181c400c1d1044a190385d0001e9601e04000d1400015504d450810782141c2d02c076802603400ca8009064150081e01c0b030461413001a111030040005913019800864584120003600c600355410358043d00c40a0f4142500f84103107032607407408007500507003c0c10403c01965403003100e545180030310380c000740c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 94809173 1250 94807923 94807939
    0x150607050a03020c130614060918070518030a02030a0206090a08070e0403110d020c060d020c0109051606090803030109111c0b011403270f0a03030b0a06020607080103150209 76
    0x401c1603000211a44210307000e0328105c1d6080b0590208030704940b501d04c6481e0703940c105a41c2c489000d1804c00010401e1040081070951000c11200c403241440ba400c90f00c0202149001800d201040d14030f12481030307004421002031500f0501c17580880d4031082d48500082c0180d5011030041c08030b0f030394411408040c200b0740d02181e031011f91300d0b0140200101c0540f410350110f80401741c030441da1800031600e901ca03c00c20790000c0c0381c0300581105009003a400401c2c0152096800e01580103062005e004850ba454003480040c48807682001070700d070b038030441d9030300a40a0040110080040d00700101c1a01c2c1160f012600001d00181224652105846070000f450f07030b011441c1c4015580b0f0140c0d035010100801003070741d03560801500c0070003081c114031003521190980301c0d030388010420854071140d0490326074090f00c0030303a0501940091302c1c41c68903001180850109844195003040d600f0b121185000a142c00d2000b48440c0c200200041c04002041c0006090030b5035104113031a05061540449542c080c0240c01c3c40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 94810423 1250 94809173 94809193
    0xb091005090402070f0b010b0a140903031201030302010f0f02160f02040615090303020106090b150903330907030f08032503060e06030105011401050706090206040e010501090803030f15060705 84
    0x1400700080503812178110540b2000400c80180c58402d5541103009900c0700c10200b10ac00d4040c40c21500100349155040c88200242d103070220745005443d000350300c650008038040f04880707404400d80f0681d03111407190601c10300c10003a285609522541c44c60760054000140b058560000c1000707000103800421465200b00d01726185e43d0f5002040300c0440340030ba030003040720075150701108042d075044200d8607034000712041013280d6503d5000002d110f080c100404640020000501c25040c0d096030700031464420b401c4014182d500c0302c0010089a207d19078001130200c90f401c42c0e4403640340343d550b440098288140400016000b25103015200601c0c0f6a51060402200203000000d0240c10307903001c1e025a6559200200b90a41414040c0364160342048191000c01000c5c50011203e581001c0c1090710300d1a2114010800768559400a001801d140742640200d58100741c0050480c140560084c01141c1c000c100700401c0c002540c1106410041d1560558595150007001034460b000d144806015030056a00030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 94811673 1250 94810423 94810433
    0xf011202040303051207030b09040b071707020706030606020f03030106051c051f05030a03081f05090c0703030b150910110609010e0609030903071809051c0201150b09100509040207 79
    0x181c071744400e80540340d01c074503500d074070084040d65100340f01150008100000f160000e8100c030041503211565250110804a000d280406420020754000000d80c10400e01444101e0b1702d0f02956006c1c29090006154056180407000e03945e110501c52401001808924a110484003034201040046841024071850030001c080c0000c80310107a8144a0003140c07510b0001d05403e000c2000b0f4085038154842142603a6100800c3d01e46a034282401d401c04840304d5030102e51962001d203410f0150200a0b03001e9207415441c9000b400700c989400c5490710406050120443d00c412240c125100c00c0740517228a4000900c00000342c03954407414040c103034540911410081c00d46c405621a40703811058034200e482c50b8039000841d94503407040c07030748441d0150400b07038040c8407aa482c05030505107040c20040010780c0d80e20039105c0e14103008001c0003440d48009612031100250703909005011142d01c008003000d0310b01e86040354019a42c421400c24602904007a1514640140200c0076160780d404040c205650320304507447c003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 94812923 1250 94811673 94811677
    0x30219020303071205040809100e0d030c02040f020301050618040902040f020702031b030c28081507020d0e01030f060e100e010902030405030405210d030209120d0e0f01120204030305 80
    0x19840c0050358042004e11130110b1802032034022500322114510b000d200300240040100306a050b40c0a1010450021850f6120410302030301c17103030103980c900301800c03154410031040e10514241c40d21990300600c010301c1240e855070f0850b0800180040d14040d10801540444c3c081e01101c0d1019501a1030311840003011100f130340007010030500c02c80070384010501d5200ac1000203001c0c60007294155011f0b0382c105201d4103084482c507011800302110317a41c88501d00c2040071401d080380d070842e03203d50300b2001c0729100d103031440550190000c02600203455a0300d00d0110007805070501c0b036200d904054581c0751141074410f466100c00040c007201140c0103541e241441100c410007a4611a10785807000c5503000043d1a107080c42541d000380d5002c0080d601d01880e1504000c5883c0190320002c500300e0041907205082d910070001d1a07607401c1c80d5200980c4070b0060800300034000da48151513906581044901c480c846030700a44500b1070010032100702e030b08201e1180049035408082d90344105110b1000401009050700040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 94814173 1250 94812923 94812931
    0xf02040801140108100207020d02030d050a0801060f0c0611130305071415030c030910090605070e010203161202010e030f090f0604080601030b04020f03010903170109091502070201030219020303 85
    0x8002d0218182d00c0c1c00404468800344108480c940144948240d80350b241c0d00149000381c001043d900103ea01900001c1c100403c01480c0d40c082000012541002a080382e00b0034010450b41c200303e0311003400741708003901d2070548500040c1201c0d81c400d648039080756228152080b81c1d034840036102d8500e072a80f514640d01c100038000c0750a4a1148982d5004902c0e28802111202d060b42602c98115102d40f00210043c0e00007a141c0c000302e0040001c01d0480d682c0c00d01c28204500d0280b4404a240d003080c02d0054035240d01708075840d046420400c405000c1000c41d0400804050340800c52940661841c1001c9004110000301c00c2c0041c0400514000c81c0303c0c1e144054020341c4e17011600805543d51003420850244964400d640241d00000d00400201e0320740c0d441c440c0c0c418005840c0d5100f903402c030030000342101c4c420241200825a400300f5030300c14000c00d80d40715001d002902800c1048500a80b1895164100661048400c640000301c440459100c1e405840e49000c21400c0f03001072042c0443c0107522070708212 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 94815423 1250 94814173 94814189
    0x32d060103050c090307030f0f081204020a050a05033f030108010b06030405070e070903020d1a060105030c09091807030b070f170411010c02060301090f0b0303132105010f0204 77
    0xd80401c0082c1c100c8000c480f2a104c0040042819134035540d25a12089203010701690000340d003440725004540d102d4001c0000e120300d1400c101e01c070310b0a40704000c5500055000f0742d028002d001400d2141d92000601d06000900040038900800000c1c101c1c00340710070064440e4455441540c454445441d803d201460581d020b013030080c00301000c1001401540d000485020785294440c0308104030300700101c5145604001c0e5072404c8000903403680c0101c2e0084c817014000b1200d0103090b03107142c1c4442c1107081c0440d40005091074040d1842c20048106216406030240c080d100f403440e03401040700e1b081c1003003003101c402c0c101c00180c2e440030f5944c6c2011302500da0112400030100c0c0e0299410a001071240b425562034101c0c2c044c00c004182c40350707100da1584910b40b010140c1408050031b81400940d84100c055802030400703040105a100d06080350300261040b90b002e00303000382c1c410701400280c0c0c207014601d68203603203519010004c41403030420102c441c1d600a10025160b5440c081000d2001c50b4940c0050043d600e1740303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 94816673 1250 94815423 94815431
    0x50315090a0b040f09151a0d14070f0503060a0c09090b010e040f0506010219030504060305061c0605060f04060b0304021c0f110f0108160f05070209090115050a1a032d060103 76
    0x75400c43c06880d00d02e8501c5c0c44080f201c445441251402105c4408c100d8002c011040d10900d2100c581807804485070480c000380740002c14100101d1908100b50b50b4800d011010510440e254402c01401c105883c1c040c84032072540382c0d078080d48140d2098164450000e002801804506d040401140040c030003030712054014010040303c4030701c048641d8540d5150a9056440354505854100300302c0040001801980d40400f0710601c0d10440b01a24030681c1d101e5010700350024180c148402000b4141c440070b9006409039040031410401c0103014805d8961180c0c05507406112004078130441d41c4400741801d80200000350140500061000070f038040004254161481140b0341400340041d50001c03011201c01007540004205010074601c07443e030038a41c1308801d0820608007201540010116a411a94880e4980d034850080150344901c1c140d10300202802d0300c08102084c200302548200c400c3c03034004460110700000c0030440d40e05007020401c00c1840c4200e0090907400e14a42708100c400c0080d9501c0c0c0c006810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 94817923 1250 94816673 94816703
    0x501030611040b0901031d0d020601080f0718020a090b0711150c0a060b0307081005060f19060c1a0a0203040303050c040f0303120f02040b070c06050315090a0b040f09 73
    0x80e01c102d4080d00c440d22181400c0c14030a2004502900300c0008281c0211441c40390110104820418001091000d4014080700d605000c01585040400c1000107101e5100030004c01040140c40da04201c0c105d010200542c1e510120013050305d0000195112840c6290300190807800d00941c0c48800140c200d0499120152041d01e100ea4511802020402d1045800c6800a14000751850b48444030b0b409001c1c080d100c426030781d40f02260908010840c2e1154071601c610230088207203840204408010012698442c4100744149942c0200080340950b00a125a04201d80c1c28005903149c0b886040b16820b1307041246d0701e01049400060340040d1011000301c4d060001003004400c00030103440a95103a507043c58a024550345044900121003400c040c0c074586da5091081c500030050000300040c000c012195030390391003145000c00041103c1d902007030400c4020b10900c0114800c1410840c1b5083c01180c0c0300046448501c50b00c0300801118840a600514054070011140c00540052130102d0141a61000e0810 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 94819173 1250 94817923 94817951
    0x15020a0c1d06100903080a02010f11191d040603140c0111030d1a04020304030309031701080312090c0a0f060e030a02060f07050304090501030f020a15020d030e150a05010306 76
    0x10811101c540d5007009000082c03082c2000202d80c800314a80c4e1030121601c56990f20b038075a8642c429112000103035103c40403803044072144c2c024000a0542d560480d45040e809201e645500741c1340032180c604102100303100e401c07140c070020020350041f80d004104001540d51b038508107107c800c15600440c001d000b802c10080715580613003081c40d1004130000280d450207002170120340041c0100760920140c210105050340c004c2d12030f803001d14400d92107034500040080081c00c02401d00483d4095400c00b0300c00050040c4201c04000c0280c030668060720800c8a070548071a60681d081c501d44072922a00704907416330009107040070301c0541c0c040b2041a100c601180c4181c90901d42c171080f00308406504900700704484003034044660001d100d418020416241819256108501603072001e030b00c00e40d1010030741d100410951402496020090002110f1681075140f0004081d4a402c1c3c1c440f1a84289603650f01c0702c10740d294051080d406030149406d8924000e2402088801c000c00342070000340c54551500300c680303031020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 94820423 1250 94819173 94819199
    0x311030c10050f1201080609010b0d0c030b040206070f0308010626220b04050a03030b01080f0f060301020d0f0f0b0f0306041b0b030103031d09060a05060c010615020a0c 74
    0xd080a01140d924460842041c0d41c5980b002ca220401200108188540c1201c0e44100d24040c0c910640a0720550800508050a4030151304005104480400c000000243c41c180194222544008240120350300c07400081d03240d002c0d0345000391201e10f00841d0842056400140742c1e06980700c5440c1c1021401c03070000d02190030303010f4220071410b1001c410b011a642002c0801c2c1c502040f081e408491200041641e1618500c0700180d804680c25130020300c241003015014000e01c0e2210b0400e10748080c4030f141400e48040c554002030605050072811801099654500390103d800b070300001c0406000d00200454004018040408024620f91520f4041d11041c50014485002d503007000700201243c1d111620f9104170814070440411005030325035400907160b5203002c0618001d50080d1112100b050415002039448a80300700141d1042e496075007000030342d0766454244800c1d04d005a030150b4441c14400e1440380181056000860038400554001000310b50004014000e14450402d484d00780b07a5801c1d20001032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 94821673 1250 94820423 94820443
    0x50108070b0409021b0d02031306051204020d0f120f020c060c0607050a020c1c03080a0501210507120b090f150109020f1207030608010608030405130203060312040b04031103 76
    0x1c500c0401c0104035000654002e401c0002440c43e0110a040007125100e02d0001c3c940303c81005a0400300e00d00d000d1006950000c0002c01d01410a203261076840241c2c55104a8020002446449a080310b4810f00400550042981764400a014244007040303401405040158181900601c1554803040a40c10300000360303918612001c004000030307250503605070f0b0241c01605003d01140b0411680c40d200369600c0d6403a0507030243d2180045507010b1700d41001024004e004041040084c02c08004000c03c00d6000305040c5101441c25508104261324076005082016070760241c0500581403080c4800c2c00307201f884860190540d0421030b180010700c2d245058903001c0310380d0b04000b000c448000401c9002c2161b00100b11040013840c4151405800260f00d0b440c000095421000087d0303500350a2080841c240706800103001480029401c051034a000100b40401c6550454000d035001701c007041058408216080c0001001c4000d252070f0b50301d070345070705005800c40d01c010303203240c14501e4124540d030034081901c010b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 94822923 1250 94821673 94821689
    0x906050a1a030412050d0c050301140609130b0604050a030b01080105090d020a08030a0f0e1608030c0304050f0414091605010f0e010305090708010c090801110a08040b04061413020405010807 83
    0x10b40d40d840d20380c1c59044030072105140034808104030000140d02c180c815805d00e00042e40b1866100c3d410580c4000744604101b0680340180e2080040c0032060b81d420070b14900c140080d407004213004402c68041450380c080d90713110781d0b0080c80e0041c020080110508042e03041c0c0c0c2c0180020030070b42d0350303010342d0350343c1d5501c1507800202580010105074081000720000390b60040100c08041507410b00c050f01d90b021102c0001e00051280c001803500d8a1800ba400c0d001d0300100230200045081048921140352684218401e46110b403101301d4010100361620341040c48210f20304540140245131003c1c00c6c6440700303000301e24800001c1d041800032809600559150f40620306554078220141841c10054004180c05051044c061249500001d507040007400754510201250346c520701d02c646810026425111511040d1544050a102c2080080e0384001500c3e0f010b07800440301134140d1030f10f04095004065041c803030010060b0940c108040e0340007150010030300d14401d40d010030182c1e0303a030383c0d0040d00d8024a0041c452 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 94824173 1250 94822923 94822927
    0x20403020604030609030302160308040506060102060915060409021c0b010503011104030609030e030d020d0908030a0e1c0209010f0e0906010803090d0c0e090114250f0302130906050a1a 81
    0x2040713036940801c000c0c901c00e040043c9450140108420004840c4100b140010821410042040414452260406003c2c0002d001c1da003448019561200300504401c0088814580083c015550343d0300107034030007a0003500e586602400c841c0c8070800d00c60440000d07610741c00d22030000541400d05119000228010341c4545060505645d61240a0300d010841541040412821207070290f03402e10040c03c1c891929002400b19031104031010309940141ea20150544d0014010b184009400400112150384c0c11504080103040d01400790101e004600000b81d0044214000480c0c44408a00300909442400740450a03d9030f48a01541d0b64140901406107250024451194681080001034203440d12554002450703503110003c3c0c040c1384d0022107008009a4664815241c00000343e4040d58110308025070380b400c080d124a141005425034016074004002105901d08040c0f4480d0341941e14100440041d8074031300d60744a01d8840070300030a004072803003041c00301d02c0011560403002503141080000b400c071134 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 94825423 1250 94824173 94824179
    0x30708030703080f0408091e011209050a030e13050901050403031413020f0f03100203070306080f0c0904030905040c030f050c0a08150a030203030309010e071a030f0a020408010f0b1003020403020604 87
    0x244c4100c4040c1084440110521904019580e01d04032020096054880440308034400400100401d9658802c861a40c1c40c0014001c0465008204048255054103021450440c5036000c110358a40001141c080b4038500020b001c1000819040ba6005501a50301440f012003906014140c100094071919030107154003101c0401030901028600c00e41c080142900c051556410109042000c0c9400034801203600204200c00c0c940c040c41888042e00740700c0c00802c0080050100340d40d60f0061403912500c03c904070360001d41014400c1400c0d0000d0074025000303000a084006015025105982108820740c0c20540007580705c0d518a0143c1c0d03100189952210560740351440c8a070200b2a03888182c1d500f1040102c2c0100140e181007000710f0040c108200005840c00c1c140040d607041c40940e0300a000e6001c21358009030a840e036024152500012420103c2c1c00c87c1d15891000b074001e00c0355610001d483c1d400c141c00007882e802940c0c003240003ca0280c42501d103a64900308210308900c03803804029031000c0284024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 94826673 1250 94825423 94825441
    0x5150d0b04020f040306050105120106120303110910020303040501050f09120c010b10271d0a06030209090d02070b03010303050412061808070201020c01030b03060a11040909050c03070803070308 85
    0x3112090000c0c100500c0e04082e90ba605802c0d0f0b01540040c1c0f03115071a0001003010382480d001c001c499428010081029506001c40213a00c1111040301404045d12828400035035240c050880f00d0400d0010700004810450410194407500210390a4803a035207020001101c1c0211224014800e4203039402807c0000070500810780184c1040b00701c1f010540d82e0750202000780d140c094101a4458a9403078131b040d80822003203403810100c03040395800400a142c00c8100107040c0c902180e0760204001c80b2089075950381c0c07035084034002c140c642d0019500c6800101440b90307007400460629017161196003034402c5182c84010100c52880b0a10000300028000c001c204107426101c15003001c054820000410400e01d103004403159096012005d5400440000d488030856030100070002d03200c8400c0c20288502200380c0000782d294000104411400c80d00e03095012a11501901282c01901c4801010000c1c0f1742c1e1424500d64880c0b2a000143c064803907900040b0f00309600109071041d46625503900d00301e6076a400d06c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 94827923 1250 94826673 94826681
    0x2d1b0506010611010609060f051e030c01110f07060302180a030507030303020a050f030a0f061d0402060912100f0e0a05030711010e27130f020906030307140106030b0105150d 76
    0x203030300c600e55a850010071b4100044c01540010b03c4030803109428039003064100100c00d0051401500d00e842019035800c00d503100803c074051040000d0070301c20390200032002031a041070703170000c1150b24070f018108005c00e07007a03095400703032019035120408c0803484d61140d4184610851640000340c02c607030000f2401c02c0003d200350002c00401044c3d1410505149a820054043c0d4105981c0c0c500400d8032946d010710001014896a0300404002c00010641c1000f001c5000010710f0203007010340103001c00509113807a61200c0740e003200303881002c1044614078082111a2002030010195015505040c028070703020480000032040c1c0800c0e00322029620385046035407030708140e20101803a10b050100250100c02d441c3ea0300f0004c034110070326a45134a40c1502081c9a00001c62100611402d0b00050005001c400b040c0c100041c65030250f415036080302075860700c800191840c012084010712101944400107002c0c00190800803c030f900c0341c81d103992144d0700c80c0200032480036070b00f00070741540805203e1030702c03410b0060700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 94829173 1250 94827923 94827947
    0x31606110f1215030604121403130f0501021c0902130207150b010c020907030509070b031e0603010216051e011a0f010903120201150902040e13032d1b05060106 70
    0x82031a030340218040c042405c040089509407034910351550780848a5402c143c0361030381d09000c214080d266107090348a18281504d0460007a10030500e40004804002095040351002a41e807a000c1e01c0060100402401070607542500f00d0148508807039480681c1d01e64001c1e11260f540c0146156400841d5040100c001d02a1070802810041003010203405a200e0780200d6005808598000c20140760280d841803916051f6400f04800d04420020020301c0707112000784034080c0418070000842a00d1303642c00280603006e1510301c1402100d203100c90700d08001d000200520704560050b001048035100d920850300304c03400707a0800c001d40000e0308609a810724010040d0b640d043d80c14141000c107140c89448400220442580c8040507030b6494840030001500380c5d040794001c0500700000d510340703820001c0490440718041d204010003004084400100341c020240b80f00086003400300d46803182c1d501100302c90760401c0c143d00c040c0401c00f0b40c1c2d22144a071840e240c0409600e034008008000e50392a0100848078406941 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 94830423 1250 94829173 94829191
    0x120314040f030b04050d020705060409020d0e1e0d020c090411130c051e030405070b03091009030504050103060b030f010b03090109020a03060b120a05070b030703020c031606110f12 79
    0x40492110381d0305040c0009103000e0705244020f80390034900b0b185008041100303002590700c040402c03c810343d03d80c0f00311002c0c1e803101e20004d40c81c2d0800c20381000250000000c440d095000c0c0d656054040000e0144101413904107404480130803a84801c142d0f1284003409007290000f40e5240064007151900c4c800d500c003d04050004515408000c61000071200e402411a00103040021a41c18050301c0215106900394400030072407840c1410fa40b0345d66030f01e04c28411403689a5000c000900003000512000c00800c00d090750902c01c01002c0d140061080e402030140c140480e20380400400c40c07600d880c05032403084000340035601182c0d0800b480584943c10043c42d111030b40d922042503a00684806400303a0003144030300b5000c90f040d03d06004002c0300e80e0100742d08140a600c04107101020850000320501114803403410076549480d0303180c00b10080d01c5203800c0708a0610002881007005d20701051491025401200304100f0481a5001c0710041c0c4640c20300300c90121310501c4a0440604101603440d0000884 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 94831673 1250 94830423 94830427
    0xa0e0f220b040b010e060f0904021014030103030801061202030402180603030d0608100b030604050a06050c070c180b0411070b06060c0109030215060307030f1211010501080c01021204120314 83
    0x41d039035248044a085a0480c0c0340d282d031400411080e2400900c142d0030240803102d0380a0038a8000125004c00790042010b441001e218100118950245200302006007850b86e8140e525a100d0802030701c2c0034401e02c18500058a2104c4a80b00c40e5014800c0d28050b50b8020710301000155941c03d40300c3c0901c406001c03d0351500042107902c3c441a4644504001859042c0192040c005001e04000c2102c3c0039544a601a410040422001400c040f44107000594411400122070b00e036208945001c1c0506c11000300389141c0058007149081c240d10f40b450703118105680503c40541d0305810700003034411403a1034405000050040c6130014940c5110190300c510f000d420b960a01041c90070385c0b404d5503c010001e40c09a0400440e40c00b00481c1c80e4100c0381e0200094006209051a5944e05101c0c0920b03000082c0244174222400030074284103168110880c001a4000e000a58590000301d44640b0064142030152107001241e1b14441c0c00c0d0340580302110070040e040c8005540c5074409403411001202d21400c06031003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 94832923 1250 94831673 94831741
    0x110601241806020705040f020901050301050d080904020304030e1207180209030109080403060605010912020303030c0a031b030c0e01090b04090e030c0a110108010902090306150613140a0e0f 83
    0x2100c450798010040c5900915903140b41100340320440b04861841081a801005902c641c0d0b60418102d80c111641501c07080b2410040c0e00300354406004441c900d5600070f0000091200b0315074401503640c80700404503500080d03403560a0316140d0781d40741c1d4890560088062951442e00c80d456a000e084110000ba0010400950302d580b030348500c1e482a001281d401d540c55038240001d59000e500c10000d4100d000b0030580306181600001d42c4c03400b000308184407856002651101003403190b08140e61081d801396a030040f0002000001c0d000d00045001080015a07500744018150310070341d64442150482070886180a08020304480500701201e448222440f0402c007103e081c2c0300401040c1c0003e406002c1c8400c800110800040c026603069001c0807607a40103001c0e40c21030b036a000c584183c100c16031000400d81401841c0205956004203019450354010380100080c610100c500801440c0e00704a4005200640302c020200401800b1f60b81d145040d280100010000d08209a400381c800513414420040c0b000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 94834173 1250 94832923 94832957
    0x5180a020318060a0903030b031911130203040b0a0c0c02090105091308040605040602060703060b0d0f0609020409051f060c170403080f0d0e0c06161103010903080711060124 76
    0x50f06942d2143c01c241c0d2000d524040c950b040c81098840d10044000d00004180b40084200b02c6604050141c1100031101e100cae0013079a2070480c00e8404051281080d505d0303180c40c2c2010000300c6401c6980340d6803203042c00500c2c1007940c1b081950281c2241d0003030500c81e259090100323101610b0801008194403484285e4140c010507408809407005100755650030b40d481d41450030003400c003000545070a0505041110034044410000140c44440410110000d01d01591800b040041c165542c0901c0c0c13071074400074000c201851290010b601c50341072078070102603482d02150401e51110b4207114180014a2101c15280002c240c21007405500d50b00410150403e922034903803138800d500642140da9203044c009a00194180f050054130704002d2500041c0801c101030f900417a0b600d2103421202c04400c03000305424020003039401c2d170420444a02400810543e40180740c080c28242c41514a00d011895003800d407882810001000c1d816141c62106612000c6124200c0000a811030303603401090061940340d480d4042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 94835423 1250 94834173 94834183
    0x30c0303090a050c01050f0304080a031e0603060501140d0b0a0f050f0103110114090d03030608060403020309090108030a021b03010209090f180106050d0807050a1703010f05180a020318 81
    0x1494610142160040a10f02607152800c0340008605200f01440744c0e07117410107501e0940e17900c10707000b8051603545c0350302410882c000c10519013210207200342040b10207000d04040d800304007524485d403070811559807660001e802d03076604590310715400300d0a070104800103001805c146401c4251074002046960356201d0880545504a8540c01840790782c500400030700641406000d40940e082c24921015004081010840c0c4900f10380030b070040071242404800c06200c1d900640041c090f1400752082410949402920384d0302c0004545e1150300b101001240c904404400c551040503035800400713212000081d003000c02201442c0c00b40e415582408101d0654503052070962040041541810051600307040c0981411800842440c40380e25056043c03207980c94180800303042e6031b0030003007854650580d440c101f4a800301540004041c03a030740c4d000d030503900d441752801780d4180c1c0c607032856444810707440c2c0e000d00c03000d078112020400c0c00301e8000c400300382c0382c1107035034001c40c0c000e9800e40c004809051000f8070a444c0c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 94836673 1250 94835423 94835431
    0xc0a1218030821060a0519050604080706140406020c10030609090308040b0702240a060807080a1502030403210e0d0c0b1503030301091e0903050d0c03060b070f05030c0303 75
    0x3440001a00000f410340c80c04103a000e215465503861040d09000c0c0c04900302d03225600409000d10564041c40140c0038088041000801000348425070316a103d0010341c0d242c805900c1008007203086c240d10b5001c8235440360240d0f030070f943c0c0342d030700810303050100c0b20421510718080d0b0140c1040c10b5850001140c0c030000d501031140c101c0e0290b1501d0049007010325012510352001003c030011900604008410f102c4280d00e081d106c028291591055610741c0e02820005042135407001c0180e11801000007001000882c0c00504075004d445005407114620386080140e1008880c0200000c140b2902c00a9900b215010b0420704010140f0010f9140c40b82042c49190000c0c488041c00443c0e14161140100440399a5141c0d11410365010b00410030b02c132501081d41d03400b042c0548189645c42e094281d590000d41041e00c003403000d2503c41030104211508018204d41d005212482059007080044124103020f0701031a02182d8401802624001460300e5551006114000031100c82c0070030040d00058900c200701460003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 94837923 1250 94836673 94836683
    0x603020d060519020f0703050c152a03040c12150c0518060702010206220f0c0e07030e060a020a0c0b041103070e010503061326030703060b0c0a121803 66
    0x41e400c0503c2e01c20201c81c60441c2c58581640100403005095081d03a056074041135040c00c000e52141c511040351814241440d5682407540300b242c0400c4140342e03031641b0716a58040500c0d200301e9a40c203000d80d084014071080b00c026151503003070003040120f03108401c00080028050750402c0c40511a1200c51400d0350f6410f200040050700100369188002e0511100c40c181d080c00700c82d1645046403650001c7d485c0d1200401c502142e080f8042600f80c3c2020101c004d00c2125408031100108145a1a01006a101034018550390450356800150703818040d102d0340703d04085a000928003566038030244000fa510817050702c0100610054178000103140b914400b40900d1080261500b080c0c4034030103141c035005032076001301c90740440c0d06c1c010000e81e10003089542e0815403450f4103500c1d510b4141445c0065044045202c0d000d2040c280c0e110391003030004405140102d01655040c080c03c0d40e20706051205014450f8428410382100201d00d000800d05400d4001843c0c0c50b04004000390000061705079031502d16030041c1e074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 94839173 1250 94837923 94837931
    0xb0901031101050705120c30031b04030818100903110103091a01090c05360603040b04030e01020a030504090504030201060b04060c03090e010608060405040204020f070503040f0f0b0f0a030603020d06 87
    0x70704000508c10305040101c2c500001682002e890300b00a4611032a0000002401001020030303102034030300031011117102280000544d590b07542c0c580620164000c0c14003442400b913034101c0742001d19100e103c4401c15100c80d1b031840b000b181192910750340121007c1c280c506060b0340d02c440d000083c600d400c1c404a41e1a0950400600398075080625050b507a08400843c20444100b019040303841d501400807070f00141440c803405a411600101031406d0000200183d44160b01000700300401c452468a548140d2091740c900303546820f5000103aa8803001600006d003c500c00384003d1040c10f4440d400309500501134800407a40941e54100a0391513030050708001c00040c0314107010404d15030403050310710003841d01d0100304855625100005001c00000b03441c3e07078071542d00c1d00c0c081019581c603601695002c01d00b10039100d9071000d0b107107407a03541c0c0c0d42320b441a40c00249040d000010614000c0c00380000700d5807000c1285d132400e0020000f10016510041c2c55000349aa01c0001001503115240c0c0030b400c40d40715441c000303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 94840423 1250 94839173 94839187
    0x1030f1a10030204060203040611010b0418030e03280c030c03030504030c060503012d0302040c05070203010501080627010e0a12030b0f06090105130302060c03070c090b090103110105070512 83
    0x100d24200710800c00820305004020804c002540042110300701c561030b00d06030b91141d07006960307c3d0140411840d01c962060400120340050f10000a46601c0c5a10a4489021904200c0b00741500d070b1001d410703100207044507488041c0c1d02801910703a40440318070402c84091046d0302c0b41e85840c8000a41d0f0800d90001e0300c04502802044002c60b0110007030701041c01c2c41d50171585840000030801c40505515141d00380c602c01c0c080c40400fa003030001c0000d5940240180800180c00b0f800030020b070040c80b000d81c405d42c01c2200000321420702040e924010407040460b40340b980310b01500c20007101d080074004030056580d840c0b00c514103201400b0380f140c00c030300c1044400d08a02d40781b8002022742c2c0140c40071900c20720915400d01c029948038000c0701c40b10340c000e08181d5101c0d541e210011440070200e80c0701942003070b000580300012420120003800c90034410030385010030503140c03501c0f0300880744012180c5401180400040c004291024481d070054a814509149000c40030b9459038204201645d0281c0c1698000c5411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 94841673 1250 94840423 94840429
    0x30c0123030705121e190207050f06150109080a020603040f060c0519021c2f010905012706020904020d09060c0e150d050709051e0306010605190e01030f1a 68
    0x440c1d0440f02003402a808201002142e001064001c0d040c1c1b00400b0090509441d01401501650950b94005058501100c03166040f50b80340e07441180c5514501d030b4a49a1070905600603c3c4120a681005c4020a8100340c03545c24030183d680058402c0d00d100c50380006450008249004510030004169611512558108014500b03400c0450841040d50001501005180b01c549914500443c071440d0079400810b1707400849140c50051442c40d03118151607458200200815002101c1c400e1007500200000246018901144441007899010401c80030003100040340c02d0780c0142041440c020801490031151035045403c40702e910000300c038017540303c84400c0082030b04031074032800600c01628407851503080ca0450807424815031108c001095503442c04185c01c1c40c403c190a5000c0d010181c51540c425141c0040c42071704031703882481d9900c03c1c4548800443e10324800d00c103403a60301592a48503903440255040640f41d501210502504050341e41c403d2004100e192b008146446001c4610616440340c03034424 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 94842923 1250 94841673 94841707
    0x30501090513020d0309081912020c0a0315021c0915050601170411060705060a0b0321160615080c19050904050c06030a0605030c0a0302030c0123030705 67
    0xc1041240750070200460a142824088092a4111a416a400302a25051b6064403807900403149504c125142041100b10003150700b00920300074401e21400da944104101da8440c614421030742c014480c1c0717004100150700707100d2a0034080c80c04640035041c1a00c80c100e42400b0280b04d14441405038030341303030024103001030300030305800800e0406020710452824000203040d400394a90645501000c80000a09009d60042c4148464400a12040c1e41d090907040041c1d5803403050fa10017180358603114031b65100c4d10b400100012030303411080200390110401482441d00c1d411100484044150703a01e52440020f10902c5010180e940940302c002c515070034052000c1c6060440e451040c010103000b9007140d125203c002580040f500211081071965a45203401c41c1010841429140c0000c408000d0040441c400c0c1c0010081e10b4040d0304603075249003c00100400e203400381c40065050f0700a945400300952040c442100034118a11112880252041c2c0084083c0e00468a00e000600c0204020031041e0707030300c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 94844173 1250 94842923 94842929
    0x1140a02180d02010f05090d0803010602010e0d0309050c060705100504060f0b01080402090103020d03050706020f0306010e0904030f121d0304060e0d0825060e010501030c0f030510021602090705040303030501 91
    0x190704040403030b86030b002803d011400d600c80c800303001c00480d081500340d5803c0c086071000c2e03907c010040d44075692624083c0c0a411480b01009880c040c094088040741d10a00c240f9441c02e8110000f00046035024060007000da2150b00300340c41300d008080b007651040d0020300400f80141e1040400040d600e00b110f441303204980b501a89181040140b40912002d40d4619034040d06480c0c040741c09220600d8249410344d0301d071081c60780040102d03001051482044e007159005e54460341742a2034062100c0101e50420290910032103004010134218118500003610565804a92203000d070000556206207070321290100e0101001c000895000080911401d5402100d26000c400b040d01c41c2203030210f159507803000a000301d1801d0070b0541100481c1c5500341d00020781d40d0400c00c1c0c00c9001000040004801e5501902090005039114502e035034002a0700c030081c41076078040300e402501401c000b20f1a00905030181d4000c24161085c18800c20081000d81e480c2c0303007036600030301d50758481c155201d180d49000b40036900164 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 94845423 1250 94844173 94844179
    0x616020c010c02040b0319060203010e13080711120a05030705010b1002070611070f150e030607090504090c1d0a05130b010605090d05030c010207020f0f0a0b070501140a0218 76
    0x190140d00c180d80004454100950444010800c3e01d075602c0420700d0880e00c09141c0d2814505200c082060100b25801141640c82d154030011403a6280500ca8480484140004200b4503080007a400842d40f001400849040d00401400c11000d1000c03800d891702c2050f1005454a401c0040e100d8200a000d208000141c281580d021a10b0707c91250081c0d129a0944500c2e828440c40b4903022038000b4042c40001e02034900d00701c48004e0591150300b15060280d000c109070307012a800c40c80c9843d80d8503002500038420315090b038841440d1030030070052102900071410f0848100c0411100850810001824032503401c448411980761860500001810b4403405031500c8a1801003e04c25400314140308011419960702d4240940e41e0103564002c074961807000d21021b01540004101c0e0b246240c019001011514000c41d41c90b242500401c040080c4501e09012069002c105000c00300b200d0025003000c0d18106024200025111009070303a0703014150401c85030103240e81d0340001c000703444890034059600300b1034040e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 94846673 1250 94845423 94845433
    0x10815010806010b041a09060d06080f0a080409110c0109030c051b0d11010e13020d0b0405010e270609060402090109050915060607171b0a150c030204090e061602 71
    0x111800c2c220a05c200d000f40040a1801c1003558844c86107034003198400e040141000c0c0e966184502c08a0040c03140d80a803049038041eaa00101c180036002580241841d0048040c0d80303071518080c0348000403d04001001c102001c02c2c04441203403402840b9866030280030b910307807840713000c0c0c54a000c03800d20798070310501100c0720030f884100c200c5a1035440704049083d0b4007a8840b01d0120200005030750800c200140154407114650703031026040407a4000d4548600249400d00c83c40f2005810481900c0003401442c4a064086000401d80d00d01802041c2c070711a00c0703581c03a11900180c11080ca003400f008840b480180e03407048080c0300441c1007641e0028014056460b0400c07036400c0881150ba00c5443d650319002c1414044404a9850b0351000121a003003070348285031035541420313003900b40115001a0b180c400c01a01141014078800c20210724043c60356408625803d010704104801401004000b0340c2104141d400c0c4800311f0051524440c600d0b9a040600003801580740220314226080b100c407021204641007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 94847923 1250 94846673 94846679
    0x7110d08030a1505060a0903110604080312040305120108010230070804050c0a060e1c080304150f0509100b01030606020c36070306080a0b04081c0501081501080601 72
    0xc001daa400c4241e485001c654105064000c00461000b90032055100304002507001c28141c1204d55001140e00c01d01500d08600309400810031035020301c0c85480456081044072030b007642400b2110a034172a1103814100d080050440c00c1c0e07405200700340c1040d03120307a50000d041206200065078501e1800b50f020b42442c500c103c803500c11044040b01038074001c2801400300c04074081200a1002c2185180b02501308a141039482100416118802c0c05042c0683c0c0c48291a484d0300c0359007014410b5040c1c20003181d0b481c5844607a58180082c140b000d12031441503507814400c07800c4400c0c5c0146030241d04001c000f08480c80b0350500301c0089403c0d10508038141443c20798100900380d00410f12828408044801805e52992a0f2080070103d2403032403c1c002d0106c49070b46010120030a9440e040c05803c660750108185034980c109903560ba411444041c10850280380000c001407201001460408141810030058800e01e01800007510402c2c8c001403401d4000800c0321182204c0c4a000d540182080c5000b41101d500d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 94849173 1250 94847923 94847933
    0x40b0a140f0f03040203120c0c010e030d0f0f021f090b1515070201030e010207050609061006080604020304050f07090c0e030115090b030307200114092b060504060207110d 75
    0x4202c40208600c988040300003015581c0c05e10400c00030165020820b90703910030b071a010329150283c50f140315000c1303490501e140e411810b000034042e090720441d441d4082d00d0300300c1d00003c0d078100894188030070440c402c142d2541e0550040c90f180c44488141900302203000c0816140c501042480200f40b0b8002d0346151840c881d65589020020800c2c4141c1e140c0342c3c1e034419071400105e016048400c99207038258000201c01e0104000059200d21540c0e00d0001d44070305440b000b60460442c040780c800e05000603c01004215941b91035802075400c60b00c90022a2902d4255000740d909040c0c1c16840b0421040e81c40115981c0c141e0401410700c0c6040d822002005680001c0040034250b0f003040c060a11201d550f0f0f04e0380b00c40ca8a080044401e800d4001c17210b59800c00100c484994504102402140041c5240780507617901c0f41e0381c40c2a0344907a00c0080804823840351800c031541c2200711006600360183e81e900610400303d4503a201e031900560042da00507a070b52405041031100300d07080100340d074090b03d204110380700803031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 94850423 1250 94849173 94849177
    0xb09040f0602030a06030b0c0d05070c0503030a0c05091002060106030c03020c06150d021801030312020306030a0b04060222030c0b0c070e0a0b120610140a0512070803040b0a140f 78
    0x56104500507140e80390f1040040017031a860700020402c0c1110002d1050f129100d40290000800d074010503c810799030605c0898840c0c5600310014050307030090000c1010381542e13030024401682e86241550a007a5160f0004140c40c00400540026030828030050003072070340c90b028000010034181020f5203011015150326689200042249003100c038a2020554140c0e0f80e08480e2030030a400501e10741039141380d042c10b071203e4002840708034007044124607030288294060090364400c15004000d0294809141c0304c030325030114002c00441e00c3c1355080090700c9105c040c0c404400c043c1d402c901c040c02040d60440c50580401da4842d00410360404041c800301250601c0094440250f80341c5d00b00e6410140c807486c1d40e04001d400d8100040703510000c0503085d1040e81d0340001d0b903031748030b1900b8402018080381c0d142080a20180c4004203590450b10115092015042131a01020311485083c2294800d984d01c02c542400e41d0442e80021900310800959202010b81c015541c481010740d1651703c9141070944145170110f8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 94851673 1250 94850423 94850453
    0x9030415030b030f330f01050603040302150a060e06060f090d0f0b01140405100b0a0c050a0b09030307020607030509030414120709020903010612113703060b0904 71
    0x140d2150303030345182d83d28180b1440c907242c0d0180b400c5440190800001011070080004440304642c0030490754082c58280080c1980144c003c080c03803901d5039007080284074541d48020402d03805d61040c03540050880c030040650071710600780c10380700240581c02c00c1108032910001605951050070b00b0312a52800c412204100c4440010031250400150708038607140110041104000d0700010500000191549210100d103181d0b003411681004940e44099110705100424052440442c00030f1200760f201e00c2c06181c8142c011400341045078555240c0b035170355240d0507104481a1040da0004014450415010070441da0810b4007030170305002c0c5207030881d101382c0c1d240114821000d4180d00035a800d80c8644a010340c10030508200401d0301e20460b00c800300380002e0f600000d419406580b918400145482e10220700051041c0d20500414880d10b0040421242500c0c010302015040b40000c0d4000294001402071403c070b14001c0d5107400c9491440c28540125800c051440b0f014800800030031002034008014207042c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 94852923 1250 94851673 94851677
    0x80301060c05070e01060305010501030606020a030f0e060d02071103010e030301080a0209060d0602030a05042105030609040c150c030323070305040309090603050102040e09010c09290d021209030415 87
    0xd0300d0701400c0c010701e0030140fa40312488400c1d05200205515030f02d42c002d241a5403080e01c060111580e1100200c1c2e0b00c5814074401760004102031482001c2c0c80c13282906c81d00001008100c182405000752205017280d00407541280c00c10301080030340146040a004411001c80544059800c43d80360241c46900e810b40200000c0c03260b0403100c0052a265140c034962003041e50000821901c0c2e103005c00000d401001c081d94141c4902a0803100c0c030100040c1011071111000030741d039800323086441c0d0303505105a148020300200c540c030300324900100d06100b4407c43c0c54107803802c541d07490000d15218107002d011601c0002460940c0c242802201280c02e07003046160350406400d150005e11070340e550400700d0b49182d060300181c001a007000d500109201054002d44191000030903002c030303145c8503d1981c0e400c8505000041e40071030f01d002d0b01000a002404500ba80b030b801c1d8890650031030409440ea00440e5800030704a2280329902145003614030088c46102603100000c403005524150402c800c0b000140001145002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 94854173 1250 94852923 94852937
    0x50601090507180303020f07080601080d0809070306140411060a0903030c142e14010510030902062808090c0609010e09100e100623120108010b01020f0a08030106 71
    0x307014802c5008160b0341411078074020308607850f0301e8000c1d00d0303103081c0241d50034503c48d400d0045450395010403403504170f40b260001400b580544000650b01014000e00180c5a0301803410000042082d5000e82c5160058403100c400182c585883c1482403085c000c0c80c4c150180800b0300240c5480c54100f40a41d003541e802d414424210380b400e01e003400500a8032040d81940d40911108944000464088918900d2810988011040c00746000b54211807821851102221100d00104040c3c10403800d000900d1002d403801040f42103171500802d405500c10200440c0b0658407070324084d401c0300301b01c9d22149406031621702041d050a24100c070940d516180310002d80f08100008050202d0ba0050140321207040001d00030518600d02001d60303174645d0010340b05041c2001d1241b400204000301d907400e408162512070b21816040080c0d043e501d0802c0d161000410854001005000024101400c0d03082c02421950300100d2200c8504000a04001e4681030038039440c2c1c4483d4074440000c983c403050324103541a42c80c1140c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 94855423 1250 94854173 94854181
    0x1090509220302030408100216030807090b031609060c0b0f090304091404050d090e040b0705040b0d060503010e01151514031509060a050102101e0f05040c120506010905 74
    0x306001d08110280d0701c141e40c018a40e410980c02001904c101c0d40d100040c1e03400f2156046040c400d1380f20742690503208840f1a100640041e0150000a0f000999441d00118aa0301c40180c0403695106840e500760b1503480b45010b00c0d03510781c41030595001d41088e15000304e01003482e54800310120380140032010f0740e162203c0060040070081003520000e0046e10740500541c0c03280079442e440e120050300c00b502c4a010702c0c0410398103180602c40316012500e030104c0c521070310303030710b07038031407080c40100644400c003001002c020020b158405040582081c81c1c0c402ca0002c0c080c2d241c8810036084840d403001004842e410451250500d11041300301030115015061210145150807008580341400c150004000e07003008418001e0704020204114070b0f80e541590304202c070b0786034002000340684443c1719a0740141d11501010200d0340d4940c100c854241d026072202040001c0d0401c0c41e40640b03500c0140302044543c0c40c1e0801c414440000351520040200b031507420120740d03098030b5036510b034181401007111650f1210041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 94856673 1250 94855423 94855441
    0x60513111204140d0c0c090e151003020a1d0109060b040501141912050903030609060402160819080c0a09030209100915030204140f071b0f0605011a0901090509 70
    0x20500725500e41541d50000340998017400240c001d0340141c4804111034000b10b841c0c0103620070180e48001d40d03070041ca0740e07000c42d05110499180041180149007401030b000001a00d965601c0000b0701071030b0441100c4810116404003008205a1180012600f8404200400a164402c0340d00f40c44081c070b0000103800c8580e1514076503204400300041d0951142342845c518030b40c010100c40301000c0041d01440241c0740c18140643d0b07030009858940c6d211032140040382031032a1960050507107201400c51006400d81d035403194212a00103482091100e0070302070454114541c480c40159100502d040a90304001c00325070010450320702030000a00541d0490080f43d1805100704c5020010950040107000103409240b400f91500e4151204030702907414040d8808540380340f40c0005118840c000071085281c1e681c484121890501a08405426810040c0d01d00c04214207030b003441c0400340070b4031020441d9403501205844401980180c82900001400403c80720b80c0d009140200b01d40d41140c419056403150250 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 94857923 1250 94856673 94856693
    0x5060906060a170901020a02070603020415030f0f06030b090c04051314121306030605010302031902130803030a020414060c0303161209050d0e04020c03040504020c1906060513111204 80
    0x100c0d0107080c00c2c0c00c040000000054000384900b0807e903080c1c601e0f4558031401501070b80224000c04089072000c00f002a42240b099101030081c0422000104288400b000c07900120703587d1390002d40d0307035141d1101008031185080110781100315082e20104410703e4506503440d044643c00c07a004003054004400c81d0045402006020310710601180c2e05139441d00504030641c41105030f44580d10100f8100f05000810703600910a50b403140600c400070000303010013003c0010081d0700c070401210881d0410303040429106c0d0100302462080c007200200503952400c10002d901842d1103100b010380306003810071641a0009010040c0c9400003483d000e03002500403500c0b000da4068820506401081b80303008035801c113101000510501c10921905d94442ca12031b283c0502007a84101c00d40c0681ea9801000108040c3c240760f401010382c41c0c1c680b01a5444a03404030020101d1440540090300d00036180c2c1e9040c003880c5451503c0a070301042c526410442601c64811900c028003614540d40c0500201400003820b001001e01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 94859173 1250 94857923 94857947
    0xb010b07110a080601051f08130203070f1d01080d050729040f0c050901081b03030f040e09060a0b0108070f02120301080f01060b0c0307081e0703030207051005060906060a 75
    0x114582c400da440c1c80c3d4250fa980024842e00e0301c61030700d0011401890a1010040d8155100c030350320740b081555181403084c100791041504036018400d0750800114018890a104085d000d50440406c08900d40405a050040e060b0800400d41c0c0142074560b2880da00082100e210035803001c01071261450030788240c502c80b90180341180c07110050740e040008125040b044d42a6840c82000b11003100c2d42c490040c488075003024090070301c0d117138000d004c0308001e480c458600c00240c0d28010b04580c50016403002458981c0c000394881c141e07408803841032129282e03040c003103103a1002c07811900700442d1040c41c000824004000d03100c541405100222000c034180b0074084c009110041c0321305140c0e2560b56000d40c9646e2100c1440e2256554a070541c045003445c40342c4111010400f80100440c01c102c065280c10000e0781c00910b5242c0040c540520310903080c4c4041018026490107900c006840b400c82d0300700f00c0e08061071100e640350a1032824041291540d50380c140160000d5054030315584641d00c8880541c0c07800e48036a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 94860423 1250 94859173 94859179
    0xc070b090109020a090b1906020709090516120308010605120c030a0f050403051305010923031011070605070516030305070e0607050d17070503070c0c0302180f010f030b010b0711 78
    0x9000c111903100fa001b0300301000301554000d05108840e0782ca000d079110f1600800005070008035040190900a81040745981d0040040ea45925002c5900300501f0b0740c15840014031100e640c07501424560014201c45c0105000c4c1011883c0c17480403503201030b40a03030041c2405810800440407810380c07060350f48411101d58003503500704218149400c01074055001080080f031000030b44d8001040c40d511641d5507030221000004001c40c64400c4480b47c0d48070051010f0240d4044c0b040e1145030744020558001d50040d607000c4e140c032961303c150a0602d0300650300c005000e4814000c0030012140480741304036500350581e07058900006c8a4031174100889030415030702c154a07400000404d402040c02000710f4481022030007500c0d04903103c0d45000500596440031950000443c0080c0001440036002d2109280d04074803449031181c6054a03540040d2040070000381c04d50010815500f004000c0e82e505140c5070141416048401d54145580c6d40c1454186050040c040320542c0401c1010400075019140c0803480002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 94861673 1250 94860423 94860439
    0x705010f03060b0a18080102040b030402061e041509050405010305191b0e060405130203100903021501080102030f010819080702060408120a0201050a0c08010e040c180204080f03030c070b09010902 86
    0x5003000400103035500017000b400504020300024107020500c03c460458a00381303081801e544d900e4080003580e400c0001f1039001e040e6420070200024506000500103040e408041610400019800030700b13400e4281c00c8240a50314090045c400300702d001030004194482c01c01000300c0c0c1049450030b039400c0740c14615071141044403c1c80c049030004025807802d109403030940301048280c1c4c07107109240c2801e0310150044e406402c0808180405180e036004011154001d004441c0180c007c2c0e80900741204003680080d421342d41c040306000c440c000300d6a002d1300508400004000c903100c1c0c44960400c6032600c01001340660000500c030003c6403034100a44000b82003c00503640c412181c006450341d664808a81c060044d407030913000404402c0d417442501410480765840703521981c02d20038054203054002d08282d80c1d8462002d80014200f10100c5000030080c0094005616940751040941ca8142d180c980c6400b1900144200125000c01105565085420655130036060f00c4920060380145115000a5007122034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 94862923 1250 94861673 94861687
    0x3060b0a090503010e01050705040308030c0c060403090e07020c0102030f090d1208070f05070803011403010905010c0216050108040503180d08030106020105061314010b09040f1407020115080705010f03060b 90
    0x409890401c0b81c8080c0c00030310000b241009120300b00c46084801e44003299041c032081c0045801400650ba20003030031403480b454001104406072600c1c1d4100c9007140000c2c00c4403402d1122034034154149070071400030300040c04002c60f0000042e44a000384503001c45108400f043c85041c590303580c110007107a40e40019200c100c0e0f8094801c020895032088030000e0110b040c10304c160780064400c20444420640041c4032a00b16420400300c0b00604080300400c80d819034890210001144082c07091005003d4030f40c0041000d54240110b05800500c9580000d040c00700100070000498000300840e40000503000c458140000f00d480000d00c054a9220060412940400003290003501540410300400e41201c1c3c603a54a03640a0803207055421028120385120076400c01044681140000790003400e00082c404100c2070551038801f001c4840000b494425030700400180b00b00e8680a00c07807819501c083c100c1c0168500e040c010704a0766440184901810803188500403080d17103200b036003c0000340c007804d05c040303a642413 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 94864173 1250 94862923 94862927
    0xa0b15030a060e011a031302091e011401020a06050603190606081902030a020d02012a02040c02030a0c0b04030201060e070c120e030703061a0a06052d070b0703060b0a 73
    0x4031a0404410300c2c01c20045607444194403e0341c100c039085c6440d0b0744ca84090340d0020186420151408812034500c841890040e076406040c64031840801a03202c100303c02e4410103000e000e1041c0c2c41a01041c4940d1155012039901180f101e0b041604001c000c0f40c10b0b22001c001c2440c1c416403140d080c210958201010040200c1ca03082041120810411217111490020310034414500140c0000e42c15403200d0080801070904c0c184116040780141000003400025526500114100c0c03400701c03003160082e00320807007140f40c24424400024007520080d81419030908020b401c034079003080080d040d90000c8000030200351003500904082d20001800e8180d904052070301400e000000c1004540004009240c5081c40748100062681c10100034010304c2110b2a6031506070090414503d50180b068903135000821f1a100c0310400360003090142d807030300e980369040058064482c510317000d6201e1140304681054036603c0e10303006840042e60804114882d13610340010540041003550700403401001d0114490501603 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 94865423 1250 94864173 94864177
    0x3070507060b0f030a080406021b0a0612090602040b070b1e0408031504021902150c0301090903030e010c020703020109211101030902041e0c05030f070f0909060b070c09020711090a0b15 81
    0x90f401e07000c83d12b92000e07004030a078415207040740c1d240d0000040b10003044100d10071013a024025045070310000d10018141c45a2003603074010b4205500c060000540041084001c0d840181d000b05a0b16a030701e4052006050004280b4020b8800340c0440d4000c0085102e100000038004090400140115a91040d96141c1004205401ca4074030150141c04140c2d4041750300746400354403e00a442e41c00e46160f00300107050b030003001080000d404140c5d80d55a0208408003d2281030320031000358000701042850b501c0010300c45031468000480c1e030141880e0724443c04404c0038189000c2c95201003070003150300034a00128024139040c0d81c080d40c05800c148604005c2e541008111f0015401020144000640900181d495202c141ca0b10302c40c000306240081e914a10030000b10340a08041d291003c50150349203040e2060f6041500440c03008200002d89204010202e003560006101c0c50000303605003200c40d2540c020046462400d1405844007000260400311141d11000041400410050108144c140c0380b444035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 94866673 1250 94865423 94865429
    0x60801050109060b09010e04270b0901051b030103022e080924010308070c0f140307050a0b0a032c03120a05060d0311010f05180106090203070507060b0f030a0804 71
    0x76803401001080404c060701c22101044010f85940100700d03507004c1400010b0035415045001000d003100084550a4040b20f980380050003281196000d052488405003140c00143c042403444e40010740341e420918800c0705580c1140d4044500c415045070308401140f22030740c1180c0ba103116007412030b8182011900b0001880c044c0004038110340084400c40661a0f2101d8840c8a42c823a240307065004000240d1810b0080242d01e00c20080b044940e50385207178824006006401074070084c41c02d103c1800403420104240c000500c0d00310741d03550300d00c0e2400b41c80c0c095903c41c6540d948201070304c5452910400342c51180308901c074210070326180e0018102d07243c07458498200071414001e120548002ca02c5000c500e0103028064807004085116000300d940d010341c2c115040c03905510321952030f00f8588940540c1d9100f80740c8500d130340c00071010b180303600c2d802d105085581d15040607918500c140f061106040d4000252030b2165030040c4005003816582000817810381444800d15854420009031070108102e4001400c12 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 94867923 1250 94866673 94866689
    0x703170a09090e1b030f0604050f0c010915030b180c1806090603070f020a120903060c031406040e03191809050103020d032a0c0f0f030c0303050c100608010501 70
    0x11034490b5082c100307840303072038081c40c4182d0300281c200005542c03003981503010340100408a036410100a040c0d20304200003120f00740d402da0400c100003003c240f0b00703000010301244240383c402e14242c00c1040ca82c0ca800566003040b41010769840285240d915400d501e844104180c1b2189841450024407103070040e40049203d02610b1003500703081c4001d09080c802d5501d040300c014282400c582d2004c46c203c81e1110200040811880b940341d006012455048104540b846a030381c80e0307115941181000c0080d101e0700c00300c0c202014946604030404001407040e80740c0080e001c94001c51902c04504105d80356004511140d14044403001520ba005d94001b0000d42110600c6401000040d0341c0b035816000b1103d09200c041c0d0441d10b409240d2001070302c186548807080030203520398010344441c0010340c8004160408125540c6600f00030038030000c0846100c64000300500c00d404070f900ca0450351840c52440d180d09c00101804004a42c414540500340f204050091699900b00503a507603a00d0950f000e45003e00c0b0302d01d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 94869173 1250 94867923 94867937
    0x10c0f1d04090c090b01090312030b06040306050403030b090f0603061f0b030906040218130204020906040305060a0509100b01090504050901061a0d05060d080313141002030f0705070b0403030c020703170a 89
    0x170302d5009201200072283c01000c9060840d1305020254084e0034000702041d40400200000300000d80030f0300c130301402217000340d0300041e891038841e007804103070840a4010300500562200b00b20441c0d4001440303c0e80300c03070140300c0b400400e044546540e41c003d410340c0151181420200c02c00c450840c0000d82a4400d5000712030a0480c0b11030380052844592007540c010990041c01e4410340050301f400d0700102000c2e00068507407880e090341c1c1c0d1506428a18240c0710aa111905d5105100f0030950401c400007000300c40c1d02d0f0401c950341d400000a4a25000d910900b80102c1d200e0001508424007940414010200208d040c1049011104200c226510100c0450032091a020100d50f1508000e00c400300032581c4080d0780e903d16100c40040e6001c61009200c11541417000103c0c1c11105c1005000d003034082d0500c048056103d040043d02c0314414031009144c030042100502103000850790700406c0c02d42007a010304000400303a0400400b242000704603040602200c031410010300341d1020b01002451009081d03a5144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 94870423 1250 94869173 94869191
    0x1090b06180703020711060708070303060b031303030e01020c0f0d0221040533040e0a020306010c030503040c03170d050702070303020c1002012a080108010c0f1d04090c09 75
    0x70304905a00707001140001401c0082e000038000e500400501e030203103e0031903964840c500081c40580c414035040f601d040011501904042c1c2501175403001d03040c0c81075182d0071450920005d41c41107c00110203401c1503144c1403850042d81c1e00703504460700d2480c0442500e00030000803603400d9440090784600b0300144110311580f04034220b0340903000c0301c4d05624421189820310b0b00f010400707601010385a2180351400207661200348030105d4071204c40d22800300c102c0b03602e840c035003d07103203103800d400805000429004108015441c1c0c1d00002c0580313040e505040c1b0507125191400e040c540030103d030f08001c003a01d8880f076800004180c02c90240c04940511101400190380c9e0510480c0c80381414030005002da0301120400708145018020306010b0521071000084c2d9142c2c54004402c034042c82c100f04140484540d9103c0c9803580d00508241c0500840d8000b88200c00c50000300401e48079070000601c04100203140c4261461902c83c151628422000744144903880680c1050300109042d8032030786503080e20345600300e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 94871673 1250 94870423 94870429
    0x60108010630020111100e0706120504020d0605040c03050607020102070204060504090f030f020c03100204080106050907080406021e0c0607031b020a0809040e03070605040606051e0f1504030501090b06 88
    0x15190002d00b981e84404020f0740c019038110701c540c0d01120840c05003100c001000e4441d442210314860164000707103620307441c0c140041c069520454002045604220810015890780c0d0310070036451b680050001030710740e6241080708854000e600018142d018038024131566a0303054002e0318049008544c208585c0c0e664078200001c480c80d40030014a1800b1909040c000f1074001c00c1005051803550041e100c605190030002804d1a24a00740401d41544c0420f040c40404800d10944029041c10f0320340403400d0070501c002074001903005000030b2100e50009000501d1303e1100d03014103099807420348803070703150155480c5583e12168203c64840010345010350044101c0030301001b8802c408281d03000f030b0503800c0e0182c440039134503032180d00e0329600107890300310121440c01d04100800039503018440015280c10145080742c1039071480e0340702500c2008404c0c480ea2030320040c4a18503040781c2c821102d41c20a4803040300402e80301d0807015180c0f11700340d0001c1000401c5c0031040d089031403007500c10303210004a41d40c1c0c4010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 94872923 1250 94871673 94871729
    0x9172b020a0923040902030c150d0f11030c0d1503030314070f0c110f06030f070206130201052506110c0c0402030421021002030c0c06060301060501020c010c0807050601080106 77
    0x2900320030720840543c05107505113940700b015114005000d891a0360b00d09000725006080d5092168001d8000180301014402240b042030110a041d05013804100505d5280c0c44903408003906800340b5520003e2410008030083d0b00483d0007070110030500716119920304014009111460201030107001d46000039403894030807040da1080e03134119203d510202001d501d49801d20100d0450480c0c0181d01c0700039800c00c50b40c910015600c55034000098400c02c0c5801080241030480c06050300210000c5880744200503a004401d031400c0f10010072804104806c0c4d000d010820010015001c1c1600c0d10b42200600c8030170210008041c2c0d4a083e20445010b10030710004d21040740310841e000340204c050260807810900200d20500440e84451049540411203600c80d01c3c220303401501d1081c92624002800c03490000244003095000904600802041d850040040d44414800d880141000b10382c03021542005070000c00e958031550444201c0d0041c0d0f03122600c040c001c1141c2d0013030400c252402e141c142d4030100d030002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 94874173 1250 94872923 94872959
    0x2071e03170702070603020f040e250f08070809151603060e0f0a3c050f09060c0a110a0605010806180c0d0204020d0906150909172b020a09 61
    0x4000c0901c4d13898954100c00030341145507420f420700230400002030300860b801c40c04c03070086030790201d003a00030300c081400c8022481c10344000c0c8041c4401e552030303102e03a2074021803200d51101c0d9a0a046e64280e0743c0c00111400c2c00c41c80030508912044000c240314000c06a500c440c481200c494508000f0703652241c00c4c0c00c0600c40111494075a42212200250416401c2d030001c030184100682501485050701f0241c1c05045041400d11001100d000010200030030103000d03140e0000c00c404060b5146080024419072202c000501c0c0c0c0f031b000b071000203640007814402c0003ca8442c50f40081950014001c5180040c040d24080c41f03221003a00c20100400d582c400030140b00c10046c52038500610040f0102414407840f240c2e0500203a034803d50034443c50341c00c40c249015214015219850001c1c400c1510601e0030002400d5800c6003181620301010040010084045a03456440301105241c8503144c9100d80da4402d03541441c0d50f0100c65956407006541d2181383c000c2d1081c04c0780e42e224508400e40743c0a07124840c000c600 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 94875423 1250 94874173 94874177
    0x3061d04060e0c0303072d020609010c02010216090501080f060108030a0c0c0308070819031104030f050a05070305032805040b031003020a080a0209162102071e031707 73
    0x5404140040c400740d000e200e055800302c05403480415103c000034119004202d0642d00c1250890105e002c22058500d1400e0941592842181002558020808a000e80c54941e03051080034401c5d6404e6a000700403011030b1540302c1002c6121036450f100d00c00080e01080c8a001114402c03000c070320800c0316011842d98143da075904021802c0c08c515100480d07500400b194165480740075698040003080d40c400080c100039010f100096501d03404448480008030210050a003010728000d00c0c0705125040f10221001c803038100c4160300413445541081820040700300030040551003600c1d000403c010010010741003400c10041000c00b0522100c1c40401d074210b4101d0341c0c10005804001c140440c00802000d1904024613850154000e0384a5011034040410b5800040d0310f80d115041440440ca0720781e10b404d6012040c0185c80e034100c0d404039005400d20800b001115903002c0303a000c0020a04106134150303854107401c0030500c441800b807040c0c002410600498145e00041b1031500c41105121200d0b081c5020312030503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 94876673 1250 94875423 94875479
    0x6060d0b060127060e1003060b04090c02030d050f01030c0b070201020303010e1305120c010606090e011512020301150807050304050c040b06070206070804050a0e090309150c0d0e010306 81
    0x3800044a140600900b0504070450440d5118241c01e4070400c41000b82c2105c0d1a042010800b420801c00d8145012a50714109410980d042c010250a075050310110b407210391010988008a160981c25405040f107810b0807207103048100020a50310024143c101ca0080403984086030729603203485402d106607500a40582d108100403c111018a10082d40c0003603d12400ea603a9000c0e5500c150400950350303418420300801040c10343c07402c1d00a10540c00103000900300b07a200c40740380407060a01c40c0d10510802501c440b80503103c0c4011400b0f099000c022042e1940308560325a1030740d81401e4a8020441c040002607407410010300641d000c2d608890040360050020040306d00c4242c10000500154100203402c44000d00980c0016140e04018050151142d28441d07101c50810b001d01c03010140d160f000b0203540d564603052161001c00402242e8a01c4010f46c1d0800c089502083c801d20144154031407100b584c030400048a26440e4090445131744440266400e000c603e0b69216054200b904106000c03a202080d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 94877923 1250 94876673 94876681
    0x1d04020a05030631020619030b010302041404090204140903030108060c031905190207030815040903090905100308191403100e06030a0506071d040612060b0411030a090506060d0b 78
    0x313035026000c400740d04950348030f14003003c3d0302042498200b000703003101c40c2c0181c40b0754010294142c010310031182002e10381103003003914011810404540031104140035903952001d00d02952115000b1414140b1960f00004050a204415550780d601c03d20ada42114050301d8041b6404510702c01c202da009000d12000d42c1d440301c80081552000f85000f6114128400c0340c001a0409444031780060003200d8000d48a1481c0d51408082e200415550b00340c43c540302e00c1c90300c4481400260840c90303041c244e0b040000c000072583c1d18030a561400c000181c101a0807440f011880d8070820100781c55802030000c06540d442d9003000890f02d010441d00060301c0365142620040c0c03042c01000c1c910031186521071402400c950b00c900b001e46881d400c00400760b40b060b00080b4451480b0b200d03500740780c9050051040a99080010794038102141b0000c0040b10340c0100040d03120034030292030759256000b00509126014000f0307036a0178109680c8004100302641110207000b6070001403203c2c500070b195155110f81003074844281d036039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 94879173 1250 94877923 94877971
    0xc01020109020916020f0105090c011803020130020d0b010e010305012105010207080408010501030c0806010602030901110a150b010e03120d11070c1214061003030f02071d04020a050306 81
    0x124940e9004c0861152115010100384240610750082c044000607213170242c030000005003c191802103045204811000400040c0da101c001d0b4043c00312103000600703184903070340d4291254840c46105020141c5c0003042007540000203900c41d000c0300c84241c0310040740840c840015001d07074409100d00d50380c0201c0b05004040c000d154280c041d9030f80788600c0005281c6542541c9010260301310342c101c0c0c16160343d220018410404200f06035800f81c0529030007801c036989007240003596032040205a0341001502404051101030811103c48003a501000d003c3d640000c085c00305c0010503542454a00207040840200000e040200701e00d620310002507001454542011a007002401d015a00a0040c640c10007100780420b03c44036030740001e00540300aa11a4404a091549403200e81c25042d400c140c00600034442441e0000303900000f1258181401c403905251404203a0404800b9400012201c0d03100030b486100840e01c02c92079114500c2101c2e844100d03a142c1c414555a00c0381200e4090300e103a0300d02c0c4594180ca07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 94880423 1250 94879173 94879201
    0xc0617250e030a020612090c011d01180e0f090d14030a050c0906070b01030516050f12071703040906141806030c121006091a0409140601170c010201090209 68
    0x641c0c042c2c102c9030a607001d50301044855000f14041940c615404080c030880840911800c01c0380d0109280200d500c044003103140051081c400302607414400510b070b0001e00c01307910309242c000414642ea83c5181a1400d030742510040081103412000070301503451807901150180640750510702e0484c41c035070704540c2c848103140024800900390a40d400b00510050301d06565010040c6403052007005c891265500d9031410610301040845040d99110048038144007d45803404400ca100104036139081c00c407842c118410b07003802070079003114200682c0b181c000071444000000a200700c0701802000c000c2d031039680b00c00950010300041480d5100048080701c4048085071207040e030700003500070107485007140c0080001d410b0910100303141c0510340150300107400c0035065214244c001c00d030b80201405a00305801c5074103c1c140b04849018440c56880c1e0340b00c014450141d105664080320303074003103d1031544c680b000d4400c1c190716030072082824460ba0503001400d5206001c7c01d00da03244e01503d10701054403201c00200b091 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 94881673 1250 94880423 94880447
    0x8061017101707030b010b030c030c07020d02030706030e06090304260312070f03050610020709020705030702031902090c09090106030f18080d06060302070b130f0c061725 75
    0x8480084046000360b11a048101e40850507802056690f242d0710b0100081c0e04140d002001c900c1c4248100f04451f81e9103030481b588481100041c59580d001d40c40080d100c0242240701940601c120b81e004641c5075050f43c808041e94014004642d040c0c2e0700ca19000340e0b03d01c664058400c00c9520760f042c0000159201c0c0e00d41e80f1125581c02627070b0805811403909402000e0880c0c0500c0095040001c95081903094070802d034000c4020740b0b201c540c080382524041d50701c118070f224654507103900181c2c800c2409018000e59940f198020f041c0d445ca40c41d10041400e80074411101079204480001c040340468002c1c100b03c0da0380c5040a400c81c070540e07203130203030650042c0004040092a03075240c10102011225a00c154203160388641c0c20580c894608101c43d40440c1e00701e40080d0709041c8108103c0c2c000c1014034030400c0e480140c0760f954682c10740c551320303248208400081000b003040c01d070b217070b000b0501036000a0000700c9607202d031403030170b040f03a58014410000740140507103542d0421400c1c00030445248905801104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 94882923 1250 94881673 94881691
    0x8070609030504031410060632070b09070311010c050c2202030f0103060f06060c020609030102090319030206071d1905030a0c0f060206010e0a090309030b130308061017 74
    0xf000d80d29115a100e240204460429031b401c001100020084c107445a40050582407030311031682003851072550f400003035659600062000d44c0d07500d803112006d51012500780c280e11640c40e45007414004401030f95181c03c0e0008440d030302958008007180303511880b410a00b441d0081c004041c02804001407210075030a00c814150500c0c442c0c0036142285800f4002103018001d00d041c849959891410210200d5036004904003405080c40000c014155020121051148d0103e42c1c156903203603d080000c0c028400c00403055014040e4021403000411002160102107000e40c00303035405030740c030850104c90201e41089100030101c4401c103512090b040c0500010982c5500b0204010220f480d000080e192203400401107030080d00c074205c18000803c0010344003006008500041500b0f504000e14100011001030254000580e2100d02105041c45001010020368000e250408181490350500484a8560030264041038441c001303e03000342852025000d043c0c88503907403240058040010140b80240c050250303c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 94884173 1250 94882923 94882927
    0x10c050304090b0102100e0606011101020316050d0b040903050a120606080a0f200c071505070210031103040b150d02090c1e030711060114180402040906050c1b010504080706090305 79
    0xe101c0018801c1c100c81c480c803a4022300c61468030b040010082c40c1d056038521081d0340180180325000340e00f14580981c03d212401d04c1c945401c0312030790107001898032110195000342011041028150031400406040303a140d510b05100c0c0766802016420307200b081c458000000c5040e8002442000a5401240703100708802010990b03050660043e6007004032451003655855000840c0c0d07150013010068840100822036190390b0846400d80e000d085401020006030040341221180300d41c16200e5131042080c100c1d030641c10794890074a0304020035002003c64402e280c0c054600c461003480e14100e1618410030b030340141803005940c0c0d1050f081d40d07140c100c4d24014540895040b80a03545034010406144517840956070b00c860103000150f517503d491010307402042401e0b1181d0250700c03542c81c0e4807a20030041c40340c044603503103a07142d52006c200200741ea4640544030314035120a028a1203150720003064501120440342041010a811740c03422500c0596005041c0c100400840f0f00240300ca820941722035000e414a64 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 94885423 1250 94884173 94884193
    0xc03020f010e0a0f0501171311060c031602100201020702030d030e0c0616020a0509010810110405030a0c0504060b09090604090611070f0b010b07030f080a06090e0f01050105010c050304090b0102 85
    0x528042040d8020011300c20908405102a5a211400d4480b10002c1e410022a80c200394a458079210241400034207440103400a444480d10386800b11040281302c0c0c0216951020320f0088807039a000c01c02e4040748100d41081e41f034000340c2d205000341c0350758580040103495590b03c610f0007a401028800303c00881070180d100c060800703944031801b030100c59502e18032442400965204100d600b000c1500100e108401d600c0052181d81c2d00081c000d181e08000e580001034050500103840940e015690016605206a078419420010402c0b440e008885042e0740510240f40c03034061481460140305c412a40000070348000529601d0281c0101109501070100000c0c60300021305540c4440c3c2c8010400d59000341d165050104000140c9051401421266042030a005856400410141121048604101c83c12000caa0490203503441b400c002e00884104003c46214404101c1e00d600c5c501910104951900d00002055400340c4128010141d016019602e09403c00d10408020404a4141c5045111390301940c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 94886673 1250 94885423 94885429
    0x30f04030c054b131e0e030f0a0509040c0e01020d02281b06170f01030201080402040c03060807091508010501060c02100c061103090c040b060a21090b06011202070c03020f010e 77
    0x259006002880000c0749801c1140c07111080c08030752101044c17541d80391481005001402005540d01c0901c000301d440d0f91904140300c221010701a041200d640145801c200200a50b001071100e03406040a07000c1d24402030340b0a80903038582c00c078040d841e00c40b20100e205034544c0e00b0340d58001005684c49510500311001c0e0340d00191007082034580192020846105400780d00c03082c06140185d02006000401c40a50304641c002002c3c1400a00001c1c080c6403200000c228082c0240c20010141603490101d500381c0e82c2da84c01d01c5000d403401c185c69203201000303010040307124441070240d507050301d4058468243c10b00300ca5081c00503d000703a0b03042d401002409400d0800144041c080c42245140348210240c40e82440c55071b9500b401880210203108901e0050182c80589447c425110482e0303a60500d069000002c0d20208402c02030749070b51010082c58850741000f041904d10303016021718400c2c0d855000d108840d040c032004a11071204054440f4501c528200014070700380b0340080c000c07941803410002101d225404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 94887923 1250 94886673 94886689
    0x6020a0302030402030f0102040315090f050f01020a180e071103120c04030312090c031502071e0308011715060f1801140d0206030a020903030f04030c054b 68
    0x4820009800105000c113501d4100320940025032544000c51400385540d079103102d8070413074444100c0216120201d01c07003404100c948035086550000141d0b070420041c0321a1074000d5014101c601c0124680c1e41c0ea5000c0e1000c40090304040d80c0c0c802511202c0c42d1541142034a201200e0081141c5a03c030400400c1000c1618000311401040070a00d02a1a21f0a5103005001442a00148190780b403500d0111404030b918590400200d0f80c10908010074640500c0b400c0000c0e01c0340ea0009484a9101041d06204001c14000c07480c00500a5031032500076600c5a0716070f0a10300d00503422811a511586145140010311070400c2c0c2c00150040c1003090740300d1700801069800500c0407d140301c0c1c05650004121010400c48d071400c1e50b10003198484c100303400725800181540009003020030a540d0104c0c0420080e20304004951440e11032003c01919941c1d82d1404840c1c8440300d00903503010322030070107180d41c0d45000900c070501c034030696942c000d01e070b880d8108110001e01080039024500002c0e40c07026403915150360b20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 94889173 1250 94887923 94887937
    0x4060912050309010f0203090d110705061c0e030301050618030c090f07030e030c0709051902120405011a010c060507090e090d030b0a2106150e040b0f0105010e1009030602 75
    0x11802d869280044029085400903040516071500420820050b01c90115009408080030f0600803035400034503440c2032400d60242c20960300140005820402c0d01d40c4980452540207192806110000c03182900c1a2240028883c43c1e4100c1c10910400c6a05011811602803e000c0a000c880a0414500006a440c1d0301036801c807040001810902403290742c94005c0c403440e14411802545882d00e40844180d4030b04547c0300d0150200c0c0d640020950181c402d070214903c51150020035034494520769420310300010242d0b42100c6640c81c014ce241218410300c00e0811943d00141c5480c1c0c1450425110080900f0004004100300007503280007242c0c040d40388a003280651060802082003200d0200d01408a075510352104e481012040c104012190110480019186944140090b12041072806001420419030021180b0525460116007542c00ca00b081d0b20960003042e5041e19030312424000c1981d2402809401c0c0010701e814030050b62401c200d0b0900d5001e80a5150501c1100d6494640b2403c90304624 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 94890423 1250 94889173 94889177
    0x60301030b09010c030e030a05130506030108031207090b040b030601050702040c0201020c0706050909221e0204050703020c0a0201030506010513080a1403120114060408030c061009020703080f04060912 88
    0x1c1e042c086110800d00c2a030b108000b41c4d042c20450704001c4a02a41d8130f00030080180700700302c0002113030a56020404800c100610014103442d4607542c444e80219200d80203003c501074003900c100c0025940c0b500c1034000400701d03481002c840c0d14044c14019901c01c04e43c0000d1a550501008101c20f1005880d10700c03591601004917800184c403201c002140508180e03840c2c3c0014200a000d014001450761040320700c5030049051008501400d080c658440c0c1c101d54155030140050707804443e2603103400082d20000407440d108031000c0000ea030ba0801d01358128060210003450581c4171030000e40040d4020b92210307400c00c01c1410070074101200d00340ca220003000c6503005901c0c01c0d04031a0f5000e04202151595681c000b014402841c1000800b102c0d42c01e40070014480ca86007205148582074058840b5001c0790f014100b0101520f644141e02c415003076803120140c40010020290341030014a4045c90300c02c0d03a00032641665826044d440303090740160b60f00d001800c2524a40d82ea05100000030300304402d111050034241d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 94891673 1250 94890423 94890443
    0x902060913150b09011d04090507090c080709060e040509070519050909061e04020a09050108010b030c01030e0a0201030b041d06011706040b0c0d060b030709050a170d12020906030103 80
    0xd2000500000803a445202d40b000c0501801500b03030b800c8260311b0b071249404501c3c2c94400c804540010094540604080d1184c01128004162107205810551003000d09458208260315080c00807200c00c0003078419000003d101e441002054a401e410184d0800d05401c201c6c1c03002500c0d000040d01442c040c23074684c10500b201d1041000709003011048507503c4041c041c0a80040c1c40c0ca6400c1403440e0740ea8900000c0865000c00000d801c56882d14611005000385510400c110f40c4c40d00c0486000b0720b0442440d510030302c121b00403110a50b11a002da480c000c1c044030040e008502d00d650056002e010740101c2c1f00c1d4015110407a141c6400c500007203914000310084010b20955140c95641c2640300807143c00c6005a030003881c10440401d0095080e00c1d000380c400306055a5a102c0c04003804000c2c9004d03041440043c0b000810700400661000420007662400c0340d046003116955120031407103001c2c18034592807941001000881440c01440804100705d0403160140c030308441c00f400601258000d800032030700c0c880b01c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 94892923 1250 94891673 94891691
    0x20d0b15030a082d0412060b06042421060503010e0a0818120a03020a03120219050a0c021e0f04020c070b090307030623010905060d110111060405060f0708010e04060902060913 77
    0xc94056034a170403c2c01d50750549028104101d032003091054012f0900301107400540e02040901ca011840955003104001600d08441a5800e802030400c500caa54031a40c01c0494103c0080000b02c3c50710300d060b07031101106140c210105402c26100b4000c2c1c2d041c991102d9901a0904441420301002c6607062184c2d0113000714010301c3c90054001e0402985960102d4410302035418800d40300d03482d5548000c801d0501c903841d980221411245443c1407880290008000c03502014414041c0c0f00c140204402210f05001564100051204900079a80c6010003588120b5040101c8000c00e8010a03c80c2c01c0503066070406912038644806541101c056090f86408034503440c03100058203103940c7c3c0034160990b018000c03400e10710006001ca841502000d454030b8a40582030105a014100c02007086200f001560018038203405c203c0d4451000b21010341128490000040041d8442d03001503060740d403020f08400035601e42c0d403540b100410112200320303000001005513011503a1040c800da0313081074a0082c04507900715 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 94894173 1250 94892923 94892933
    0x14030118050106090f03061a13060807080d090e181507020601060509030a0215040f030506010305010c020c011e0201020d110a020114070e0409050a020d0b15030a082d0412 75
    0x44143e01c040c0412401c1d410600c40f4a40004090049079001034000c50380114805042400303800c5450001d174071111180c5403038001c06164010b9003c071003d0005a90a499450107079603241c02044e0710b1600080c2180005001480d40c0c01042038100140d802a01c43c041c003801c61445c0780c0a01d15503110040f10814040202803a810050207000d003c41c0d10b01541840400c0c00401d59903074000d1300003842600805840745100041c1c40c1a41c00038401c0526009555030359040c66500c0340400e002c25509035082070304240d460740c000516000c0d80c0d07406a4402002e40c4003442070035482e050031403680d021075408114408140740d0501032500b01ca08a50980c50f61180a08c02c01b908407001540a0a81502000100b010351a00070084d84002501650082081c01007403030103904094090200030740c00007a64140c48188100c0001040c416101105040070b455200410540d440c12000e000a00b02002044524010704080150303402c2c04803803548041c0350024441c910780b015081030b0044c071400d960030005002404 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 94895423 1250 94894173 94894181
    0xc070b0a0f230105030a0f080a020c100309051506060415020102091003050f07030c0e0f0303043f080901050d0b0d051f0219030c020307050106061e0f0c0b060114030118 74
    0x20200c0046c0311070070461350b4111010401c01d00142c000c4c4e601207016070304203000380030702c00700d003000100920800f204091001d80103160b6440c095a1500c01c98808510400514041601441d0010810303800c09251801c444c111600040b5007104554091080740c1180d00d40c409040c0d43c0d100719031404580703840c0c26551450b11902c001c00d180d0800d42014001202603401442c0c42c5002841601c481d0301050080000c02d1443c41258080f040665900c08000c80f451003510044880820912091070541303414030114036600841d0f1700240500008002d501d02540c000c000070038845225071004038128607410002a0001107042c000e403003540020520340881c4c0d42c400540d22800030a40b80850403d0301000c04d140d040020001000103159030780c0f90041e02035000b04156010300b980310303000b03010b0b058442c0310041a00a80040982418072850011000c0b035002e601c010400880603139540503250310300d4950030038038a4060f00352818031603401051a004114000110302034441d4100220000481e488104116 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 94896673 1250 94895423 94895429
    0x2402030c0405040b09061f051308010509120a0f080a0b090a060503010e0a0b13140706020c01030609051e04061b020105040b090a05060112110a120b06030102030c070b0a0f2301 77
    0x18120750b03040007040d9840414040c60180300da00c501c001500c120031705a234070f8421414500425500c0f44400501028150483c1d8400d220b18020303a050b000300d05009a210780604042d22011414003c401e001e0356118a0350750364070500c988000b24034001c4501c082480500c0070f0310356841841d00c0d80001d0100d400d09001e202a40600e05009090325039150300c0c0c40c2c1940201030002414a013035044103209114490000c1c1000c0303042102a40c1c11946d0741c2e0300107503940701005007481c042410981c0c000741c50b051034402c4d140300d100d000413051000403061010300310104005004961559852100041080090503250602c04090b0000652030030b15041014402c01c00411120282d400040640e000030300128149045405424000c1981c0f081450704400080c3e10700d440603007103560000c0c00521881d00000300150781d0302803296501180c6030041810300f030348403c81e00b010940c0820070a80000520b03042059a2046000c0c03400220003000054000030398034105080a95800c545c02c260800c08503d41c0c0075401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 94897923 1250 94896673 94896679
    0x30203060a0f050f06090310021308160303090608040501060906080309130c05070803040f020d111305010e13020112020304080306100c0210031a0d03050406090b0c03072402030c0405040b 82
    0xe031516220008504d150007428140c01044045843d1405c3d46080207004010500c1c05015505e94458a4032404484181c0c8030301c1045204ea031200304250200f6102c41401e480c0c01d5900d84940c541041401e07078007110003500403640c9650b140800500c5031098030581026010400165a44055850401c901a180042103049003403800c010700400a40103070441d4070a0381e02c0000c4946965590070b00da0004214980080d421818404400e0204650000d680001d04800c40f041280d030009001d040040320403d0145001240900010559421039aa0003181152051400c00b060340b010140c0c000c01d80e0002c0c1c41c2212040d90201c140080c525129190803180291362901e07010880071500040c0d00020501080028159106200c82c540201040080790b94040503007442c0c5031500c01c3c500103080758001d228110018070085000f050211002e0100d0f10018a0500153b0038035015403034120b10700440c0b83c0310700610300703a800072040e01141d18000703103103d500b507007085a0303c491034241400182c03803005006501c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 94899173 1250 94897923 94897949
    0xd0503180705030c040914010204060305061e0102121c02040b0d060b070c0b0d060902071a01080d091e0503070807090c03050403051605120706090516080607050d110a030203060a 78
    0x160b62000211540b4580b422240032800e21b0850500d01429190807030241115400024041461038040d00111f00520094480d4000c10103030203001c004010829001034010b03000719078070941c08010a4081c2c81061403170aa0b0000502200b5500c1007282e10940c401283c00d1404661002101200c0c49000000c10000c0440b518000707042c1e48249500381180100c40582901154030300603074116500c108042d0206d89001c46d1344902c10305080103500c488000e52034450030380c10004a606080801d80c01d042c03d070702c0e0325022181403c100f085101809100b1b03c0c1740548011040c0010650303400c0048000800c00d82019004440c2040442d2090350001010718003890705100c240800698020200e80170782c6012030083e80c1000e003d10f0660b0401804144012100c80c002c80c154050010079070000700003d2241049500e1001c10382c1e1105403604e124455903110750410030014082500800051a01c0c0b0000580000d24014040c111440c80c1c0200c4c803644c1c0000d0780801000120305080e07006034040d003030f4020608 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 94900423 1250 94899173 94899179
    0x40e04050f0d08070807050f03040f020f03030a020c0f0d0605190608010b01050318150a0209090f0c310312030507030605100323130b0106080403020309041a030d05031807 75
    0x15080d5880034180e0720400c084179001071480c9100347d0a0390317010220b0070012030740d0b4100f5082032042c0051071081a8480e5403003800319107052070000100c2c1c00d81442ca0f009000c420013030034104400b14a4055145420000d40714040700024410f00c55030b8400c807140c01400c0c1c0307040f010f0744c82d29044441035000446141e244c0b11480601e41c1e00038058070713803001c00014000141044852213a0401190003403c0020400e00310a10040720501d0300030b031415140654403108181d131010032a110729482642c40242c00d0f0320821a014008402084c6019069455050035400c8000245100403441656206582d141d0380f12078040d4480c0d6040c0140d5800069600e000e1004600700000034016030b0f81c2c210101d05041d90f0b00040410540011020301210742c4140440d61b0514041040b0044130701c3c1c118048a21650240022603150b0140103818003854043d0700440c10503d800c4144802040d1007000d9903003034060300985002c00c0d9000c203d0040301401541e10039489050600c441081000b01c0d0303521803134540060f0304c14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 94901673 1250 94900423 94900427
    0x7050f1b09010b0901021e060105180105060909040f150f0c0804020906040f0b030304031103070e0103030c120c061a0103050c0705060c0d06050316060e0906220f02040e04050f0d 78
    0x69042d0f40400309016a0344040e203006030b140519090304480c0100c04021020400c18000c00c001d0304039481525096020f83c405010f21908841c03d0040750f500c250103000380c0c011400c00050f0180d2007445551091402030603a02c540580d00600c101560720942c440da41107982101e2030043c00d1840c030b82c9090010440c20140e0000791280c500406c0b05010b60b03680d84804607120055003140158840c045c1c1500d9071542c0781e007049140c00000c8120107000b44501c200c00140503941d0f4040f281281e416550303615820581d030356020381c85030301c20f440c0ba01005804000301010440780c3c81b41026200d40480c442c0311705010304001400342c1c1c5004048100e500d8080c090807000c038070042070b80c4d40d01040301e01e4419038500b12410240c004000303030b4100540602c281c01c41040c48070800c5c58168141c0c0c031151690782d0072034068802c21102980840340c00f5000710301a800850b644500f0441e0020041c0c541c0713800704094110112000481c2c02c1a800f10701d00300c0c049014042031001c1840700a04e01d800c0c42d0003401d0000450703880 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 94902923 1250 94901673 94901689
    0xd02030a0204090501060906060c020315130305090f18060f0303190302030604110c1011040302010507030807031d0304032a0e040309050307032f0109050409110607050f1b 75
    0x41e0203240c83c0e00307200e0200f040a5200802400314030701c2c01c04c80192640c030000c08091482c6c0f02207020b849203086048105446140c002d100c0c900c4100840d2060344a079400300c400780c00c021482c981080c08075004000540d9030b0842001ea0a04d41c2d2007544585c900384040243d0305808941540c0290001c00041d0403107802100d0181c40c0741c00030b04000d65203440741008200100080d01e42d035003904102013480030f42c2100214600e45840c14100052086124041b00000188660311000707000c40c5c820030140b00028051f0f4411940704a66007000148032140303804482c1c5185240c0302041140c4c000040900410112800c8850710300c1c000b0007500400e26030610310390022410b50203034400c04203072a0001000c15122359520406848003800742c401183d50b030700d00011002041c42e2415108e011500d0001c81e108550724216403103010503581c00124a140000f40001801c0e000c030161a0401030007403000868644000910955104000405031027440c14409814200610307001c5100c03180d1020080d02c160ba800c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 94904173 1250 94902923 94902943
    0xa030f0608061b07060501060503041202010605090610030b0d0c0501090603060e010504110705030a0203040f05030303040f030320120105191409280b15040803030c0a050c0712020f0d0203 82
    0x220f0404054100c01ea2103d0600544000074a07050a01002040c1a6841006103020b144507800b461007030a260401a4241c820328051030750807070f0410303002505505d840200c1e1000d051442c02c0c001058001d060204142400c0c091080d00c5000710810100702650380655444020070b03c2d403604028903801c2a2040c03501305018840e162289840388001c00307d110412040314411a80241101e0b07503410002e40280d00d941151043e0a070104520200081905020044074802c070382c041e0080d078850410340c7e0286d004007000c0e07008203059011002c0012520030803000a011110300032510402c550314003001c001c03000200c1c0d4130080d0065500b001c10005450f0540024010000440304091240c1c2d40790002d00040381c404030f8807284152001e58560740348031180d200144185042d103c03a41c01d0a0803454180a9104504c19401b055000304006030f4a25401e4010b01261081032801500e40b004141e0701a2911001741c02581400c41d1482c144021071505240001c1c0d160001e840c54204074400f600020b8480f41c40003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 94905423 1250 94904173 94904191
    0x9010c0804060b030c060a081f450504140a02100e03100908070c1e060c020a0b030408030907060c0b0c07060905060c0a14030105031207031101110a030f060806 70
    0x103c9140000d0f501880fa440880701d0183c8002d071540c0c02c9030001001c2c15000d507039204840f804011009542c00c00404108141d1f01c0380c40c2d99884098020001809226425041c0050684584104680050145038695001c11280f070042042d0425003009a018019440483c1c1c0c20350003115080d0058440400503d00075a29007807000711541041c000c01d017030408141261b40540c3c41c00564400b084460b0340a040d03018090005e4420554a54030750b6000f14000c0700d00580b144c510040204480352082c0000c0d07070168070140040003110303034400203520140c00a45040b01d90381b40220030455181c1c400c000b0b00004040a01d0140080501c546034125448005058506410300001c0c0017000c4c001c7c1600704030030242e40802124541d19005071400c0b090f03040304814030700007484408003009092204090324140c1d0390040240056204050703084465030710290084051110225800b104903100b80b00784010400340314802a80c81001c0d140013411201c096000c550f05e1071174060306214107107001a03601e41c8a6105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 94906673 1250 94905423 94905431
    0x30209011503060e090a0b1f06110c040b0618010203040902070b01031b0b18010e031501080106060e0f0919050103030305010501090b0a08011502010603140307111012051305010e0d0809010c080406 86
    0x225008140300c1c444045000c000100041c8c0007655640c0700c0043d182c000c09000036030710004000c0c42001300307071071201e10081d40c08074043c4840f01c10158206504001c682050040305e09e03140c4c1d20b0a04c0d4041e80c1007400140e8000f00e03004010401e200a4400b20411485d50343c0000651078103045074950305d4022104030180c03108032503a054655900503980c66100950041c11100b0300d411003582c10500340000d014814280d400d14500062072401010071001e01e400040505a440c040c00c81072241240700201084103400c03c10788001009006407007170030301842c080c0e980800d441d8100701c0054012805039005442d0140c1c100b2026114550200400341540c450362815805a00ba182c4101d0150000303070809001c20210400801a0395000002012114800e410301404c210340344081011040c6032140310b03000300d68100241030a410459106980c06000b189009100c11007c1c1c03600c42c08c50b04482c0d80d503a4541d1080002614498110480c03542c0700722002c5c002e00104034017420040c414400940f004001c1529 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 94907923 1250 94906673 94906681
    0x60212070605130b04050105040c05042c030403140705090c0a0e0d03020f1002031503010608120d021306020607030b0a080a02010c052814070308090607050106030209011503060e090a0b 81
    0x1c1032001460741340c201c1503045903801e04c0d041080c028101543c0454100d0007401c800961802c06003d000341e4298903c050080f94040e030410705807543c0010b03514601c0380c0000c01020000541c0ca860780c403030b08216030004000d003500388418400c203c030000d44241c0c1091b200f400036040d50355004204e0100070b00300b075034141c840b40340d18a0160301d0300c090800407540f10700402280b00020340c40340d8040c52003000d00c0e129950181e500303102498225160b9005804103a000600c00b22614047e14004201e0311000103c0149030000c2001d006040d01107940021005801c50418014000e034140140d40030103004072000b007a81403604040355035803a14144000c0c180039031000740c3e005000e810b1007041504040210480b64401c108a0040e00351149803c2c129541c40c4c1e000206905003100143c2031094039800402c551821240c403040007450b0304000c001b1038a42d0f40303ca20110041c1c8508406d10700030420003403142c22030105028050b00f511000c0d00004c04641c910010080d1910000078814032480c0c000e200740da40340d11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 94909173 1250 94907923 94907941
    0x130f030c0203190516030c030b1b0409020405031b060a0f1106040c030b0106110303010e060409020310020d0f0902061e07050f03040e090c01091710060b03040c060212070605 76
    0x455040c010b0340c03500602407007070515000709480c0e161039486402610098200300d002003150302542d000180c00c8101c802c10900000b00c0c00e6407074a420002c0603500c95019544a0003041040d40b1641010070501d4000c141008142000c01242101710880301989100401c1c01c4007003206401468195010001010300602c0c80da8007503a44600c0704072070b160903100070f0b1500d814004100051440102c40c40c081000001800d1841007148201d001c1d180800385185910385801c846111070f020f8901a4416a611031074801a60304010030103404242e000c003d42c4410396101018225040701a0302039106003400e140400594901d07044664200b000352051182c101e0381c4214020178092504014034601c907061803400209400800b810840304014040e1034a50781e00740c4448d4403600300c0e064a80c003148000d82c0900c5010a00d00c111903554108030101e444510260900809441c0c4550043c10643c90000a00c81448120845030026003c140020141d290001000d0000c61061003030103043c06940c2c20204080c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 94910423 1250 94909173 94909187
    0x61d010813060f06080609060c03070e0f09190506030307020f090403050909010e01050427140f01020a030501031a040b1302060d1a010801090b010507020909010f090812010b03130f03 80
    0x15030007200401c04a040319090900130710702c9000b0300003a03105a0b80000c51141001811a05ca91903001da041c1c255150018180c8034001040c03541c582c030101e11a1480c140d9152841d8884c85800b1000110070000461035164003210707005070106009400400107400503859482c40e51080720025900102541e0325070908444c503014860010354045c10403000001c00d0744461103c0b5040e240111020815242080c0c010500c0715681c080c8080e81490001d50800400e81d071150a585260b101c800303803010018425911402c80c0e000e0b1105c5008640d9a000510601541d0403000f81e0344c1805840c1170b1260305040c0c6400340d641200074120040c031039100b80d00c40c0c115111034065995840c8842000c3c80484c062940d90045494401c0d006c1d80003070840c9000084ca81c110b40202400d40c0c10685525152155030b40070700801075001440b01d0010741d2221541c3c0134094062245a41ca20b000c0d00c1c001c0d403101d4444181340d40450060380640002d413003d00c140096003c010100c0d070380301a8810341c1c0140002d86071a085e902c030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 94911673 1250 94910423 94910461
    0x3030e04060909120807030b0d06202a070b090d0f0b010b1c060e0705070305131202120c060d02090f04050c0c01060b12130c170a0c061d0108 62
    0x12824143c0344000c00440b010300c020155a2510b4403600c0e582c2c1e0410803000c403030840807070581c03216001320043c0200e00d540d401710401c2050354003013140007801841000344550140c01e981c0081021070308500d00c0485982c00944860003c2e801074051280b500d140000ea500440b02c841c1e205130390308019242044407000313100c401e065021410f00c0031580d4800d44100590409000c16210a10403000c42c0102c0005109072000c0c0d40c035240175481103480e0032404031a950881041201407080410150200c4512110a031004008020b242d0842c5581b82c414494002c0515500c0c10180d40f000b0300a072141d6458500ba9440d4810303801c001621090b20000040b10b49495204064101b4a44400d00c00d2002c2c0c0c810040500c00a00c10080c42165542c0704800d003d48110600c82048480400205000400c4103180c0008903001d0b020340b03c005611403402d0424880c0038038580e1101d84c880316510f0200461b01e18540300515440c248150081181c0c1c04020350000c00d50901810003462000080405d8090242c1c0828 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 94912923 1250 94911673 94911689
    0x2130e07020f07140a05030f06010b0a050c0703060903030c020f0a1104140709091805060a050907030b0a05060f01030603030e1003060918050c0402030606041a1215010807080702030403030e0406 85
    0x410b9500c0301c2c142c2002c0081c3d4141c41c002e005c03440002c605410300150748014001c02c100101426840c1c030038245103a400c548120390030040100b0031002d81090400510700514040c0b200001c820b840c40c907014048551702410801950401c0380c2c100c00f0b4900c04a040b43c0c0f10b50b00a8010031882801000080007841503070305100d80c0031a00700904c884076900112000c02d5801181040102d10070903202113080c0c1c407280ca0000c000e948580c0000b0598146a00082c2d00000c1d48011078802c25120f688c0c000c40035000f1100314603070741d0382c134020443c151801074062441e075102803c0400c249030450f14003d152082c6c8070781050141c45c0310503e800c1a903109078804030080c5603c180801880c40d038800728100099642d24140d40e6803240d1886082c4a01e0184200ea01482000b058185810314242c08001c101403c05003040e07422070184880e000321040056074074403070140c0b140c14071101001e840001d170500030040c1203401081400c00410a010b038001044400b42c9415040c0780b20080072140008000d0219a0080340c0c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 94914173 1250 94912923 94912933
    0x13051c03050915090705040b0f0301020a05180414010b070c0e070e0103060b030609061003020f03040b0108100504110d05011e06150c110609042301060e0402130e07020f 74
    0x45080d51660000740500000b0301503601091008012a200803020f495401c1c243e0081c440c10841e61030698410601100c016191035140000c40c00000d003260000a8200c001c0746001540744200b1145107180300d48540100c4003048840300c1b81449036003540d014010300c003100800107103420500007011038040007421120300c1e00c44503280c2200001c043d40b2a01c4099070102c1d04095000c01c180e4840000d5a21a650250001c1102d9031520f041101c521254541d101c1459400c21660a08072118002507100320300446007071409524002c60036141901094218141a140c0010b2100081001403c0c00b41d1002c200c1d50100f070320f44c0c0e07810400d005181303080c24900e0b807034882440001440810341000b0221074054000030142c01c4505400d698210b1000802440c5103e25004134003249089001b90070001d10181c0005225401020416001d071452103914140e00c2030640100f02c0d95034415851280030105441c154203185048011a40301003440c011400403404a40000752554030030011030b860050040c1c1254 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 94915423 1250 94914173 94914223
    0x70305030409110702030d051608040602060403090801150915080601080606011b120c0314031311100c1403070203060c0d050f04030203071203021903060e0f040b1305 73
    0x1564a500510942c142c0d54203001200e40c070401c1050548400e141c014015004c2c09405001c03c54003607003c03107941c0001c1c0d000607800c4008284120b001e440070703100301d030000c0c0f480d0304180c01c0240400c1c00980c0210844d0303040c440c2c58544285510100c01c1110580351010480c00038122440485280e01c0d0400301940c0706040c00003c80d103034001120341c000e01c0c086c0c84159010b03144101d1b41da1a0b0409000c050300885c0c2d140c1200042612422082ca62030b400307454504100e0014008401440c0d1050307540b80c0060501c40350030014000081750048400c80103e8002c00310014264025040d40b00744200030b0800c584002220704140401c0c011207288039401019510784d890306040095084c0c1002141c000301a1421001807440c003c48180d40d402143c241d0020760500c42c60340d849440c50510484620201074092002002c84019050102c1850200d502c000c0f9059041c40740908056800a0071000001150002d1101090303d4140050f0800c030402c1813905402000d040051420340d1404a541d04034048124403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 94916673 1250 94915423 94915433
    0xe01020a050904060b031308090f041b080705041a0c030705011503050d03020a0516020f09010b0a020f010b010f0f0c0c0f0e07080c0a1b0204060306021201090603050c0103050601050c0703 82
    0xb0031041204440400c00135455802008550008450802100d40620100e0b40828040c601421800800410f061141421000840d05035807500d50380084103e50b40398bc1015084e00146495800310303441c40c0c607609192400154810a15008200081c0324100041d01140d075a400c2c004c43d20340c950000024000201000b0001c07412200520007a0791500031010450702c0030f8440e00031200c00100300d50703869040600710140b01e9840d20b44003c0482e130101d24001512091b850319a0344e18001d0554002003500c85034400c10180c10010600b107800340903458a00030391801d07030300b1400c2094100610724040d61100d440e15000c0d100760700086405090403120b508000b07a1050700081c504280c51125106101c1c5031200781041e15001016243c01950b40c00c24040304003094410045003221040030500d0801d038090640208040720101d0300280e40668002410780f20034070f00310705054010040750708208080c505d503071121074803070081c9000181003644035000315079542c0c401c205544a83d4086815242415520300d04 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 94917923 1250 94916673 94916677
    0x60a0b09120316140601151218030f0906090302060d05100b0f0910080708150d0f060c1b031202090a15090f0501030e0a1115030717060d110103090201030e01020a05 72
    0x2c00ca40e8401000120042488041401412602c3d030184040720601f40440590701981d554204100559031400c0f0005030f241c0040068100724000d440302c2d08450201400141442c0301e44d0000c506120b01c4150800042c3c030342908031125510480c000149944030300c1c0402503007000ca5444030b8143c00021502e5030120b59031b03600034007082c0401ca600c0840e6100319131080c0e40342301040b182140415144000500e01014408030300d08895001000c110716085266200d1000d2450000305803101583c0d031708a40c1f00c180c2c001c059500d03509080350030301c1c1e582052650001c08441c40122032403091a00401e004c05103464020a21019041e4003030011460b03002204002c200f041d0900c5506940810301c0b000150302d5009104c0c069900d1065400340c4820802600ea10365400903010030b4075005415180a45140c00740301c00a140203015559648150440380400c20390740710f0019080900c118480c03189007000416180c041400d4850030308021801803040d000680062940d03c001c214079500000390703a0000d42d0304c480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 94919173 1250 94917923 94917967
    0x2090708090706140a140405040c0504090c0206061c050c0a080a0b01051005040e04080702060318071413051b0307090501030e210706060807150e0108060a0b091203 72
    0x300700e400d81661040f0498100741011181c600100040001207036451148a003d4110940c0220aa2811740c3d070324040703011a9006111b0000140000c00c003480b00446600410221903041d1000b015981040c400141e800c008010780082c500d00c0c10300f0031904102c0f06101c0c0c09041e42000b03007141c051030361b2111401d403121840d21080f0b404800840001c1202c3c600807640302c4a40d00d40d0b540303803400c07e0b0401000522400018100b560111001d1010900580ea4800214402c809a02c0c40076251001c031481c242c5000c4103500811540d0402203195881c1e6100c044081c03039580136203130b0080b9480d1500788024002010034000710b61690000804c22602c103030011190800c684c000c0e40d0804c0040b2100400302c0e00c0300c2c60f00302070f050300c0c0346503c0481c80349215000150210078000d00000070060307954131546190000540c07052480c200d8a42d805100c640c2c00c1420901100400c0c20192100e251030713000a910710150b07000e1003013898070100343d41800752a160309a101c0c003544001280d994814407409505d145003040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 94920423 1250 94919173 94919191
    0xd050703020d08011401050714070323030405060f0307050d090b070e03070f170f100b18060a0302040f0207140a0c080304030b1909050604061406030a050c1005040302090708 76
    0x12a07a200028400e0f9011412910303034540108414078100011506c44d842004103980314980100c04000144040c4013100045200e08000011060a0a90b084981d1450450717a0030603041400100030300d844034011103440c41078126000d80e40b650345c40c8003902c03140a0340240205442c40c1a001d03800300a0705948590241346030783c640301c900c007803407004040d0b44910b035001d01e0388008080241000254080d0036400d210300030600540303880c0001000d27102c0c81c00810600d1074020f00c3d1524040c407424203081449182c002c50514480905160180101c2e0141856103c0240500c1c1c3d604035905038000710741d0582d046168045500c000e09100d0303440d00e95846407040d00540780721000440c00151300703400100300c0d4201c0e035112110500d1a81c4801c030b010940900b80c03148084083e110340f209000104240001803045204600020720b00000b1104103000c01c1008244901a84c0300120320408210300041001550904485c400807038103003820219024001c90f44002d4000c084c60083c00724042c0c2124000c1d100369156 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 94921673 1250 94920423 94920433
    0x2030f0406061a1803070b030c040603050f010303051209100e070504050a0b0307151b0813080c0102030f0f07020603010315050c0711010c020a0806180f030310050904060b030d05070302 81
    0x515860f52040d410500304000004104004000710a200c1c1c040d10803488003c040c0c8103d5617840c1c80710310b0b0340d61040b03504416641c1c0014091118940510a10b90000030310813044002d03605554010f02140302d54000c40b030100d8400d100060f05410100040c1540c0b201c805d20030b0202003181002c01d540d40300381d8000c1d035100c4c1d424407000400400d41841403c600c141c008009083e0f440c41c00e0b0035100c58100c0e1080000421500c4181c5a440c40260180050100d1048480540ea90403a03109010b00d4030140e00b08030792a401a0182408076a400415a60000666003607541e6407110480d000e415445651070007034002c1c07004000002484001c2d5041c5100f03602801c00ae1201c0c1e030b41c030880c42025204d90742005003142e8a040c01c4101a52040503a140d0701031016044190300d944440181e464003200302c401848103603400500c0c0300c101c402441034405084003040118250309020b40c60300090407a60050fa1700613140d610008042c000d103600324482c602e4016060310b00c110402c0000900544c01346209401510030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 94922923 1250 94921673 94921679
    0xb04090b09091b060f0403020904030809010c091a0a0203040305070303090806010b04050307170a20120109050c0613090e010606031a090610050c07082103010b0f1c02030f040606 78
    0x800b103010f40c04150048498004002c06600300311142d0810f040000c1555400c0c4800310058855540703050040303002e904ca8010624044012500396107101314054200705d14110300b00300c04038541c1c1d030300065815060286521480b100c00b080b499409030f0b80c0050024403440c0f100209254204c103216096480d110309030791090b0380780d0110501a20403841402e801d58041c42c01088559014030012403845014015507240500c0c1c2d8849003046003c80c0b041c0d55042c441c840030900c00c2c8ca8000700a4a0b0002c08030700a021040c2680c50b01c80d02c6440c040d52040c0106d40011755001906c5001c01c2c05006005040700411103000800e5a1500030304541c051035000c0303850402805a00c04485118003601071000b8410103c82c1d850000340029414039401c0300040c0071041c0b001d034082103001e1101c40f000c2d0080600034120011960041003110032807821003100303017a08100600c40c03c4007050440c0d001029080110307640320a05025550511000344510140038400300070302c01d043c0c0522410342d000b01d014540c00e0150640f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 94924173 1250 94922923 94922941
    0x130b010f0602010b10021203061804050f1b0d060914030301060e13060b07020409020415030f150504031d19060f0e01020303010803160501090b0f040b1e04080c01060b04090b09 77
    0x10885d003011000d40c2c401c0003007179a6510705c440290ba000c18060408840340c00d2035095510041030950f812506c43d04980401003c1e403008200a0080c00701c1c8010800307110382d039000400e10b030340b41400c0d0203800030386c4541d920702c00e0121040b083d600e04080300084036943e694500d8005e140c1c007951204103102b0000f0aa80210032005400350900390350302c1850381c2c1e140180c00ea081100816400c0c004980240c0c9a841028119041810045c000c50003103c0281e40030344185480401c80d000c100030720b410240303040103020200303612070400510340303003484c4440040d0603c4000240310401001c90840c64985843c40204030f46600454041c00290651a14150340b04804010f81e00e030f01090040c1940d43e0b0051010807030740c542d11300764000818001c900014003c4610b45a0302d01c866000c440076031000c55810240003c00002c07200c0c0316070066001d044058100d204c1d9450061a0a000d40301401b12200811410801d401c02c1d400440208000345480340e130b541e60703585c0d01d034060890781c410280310b0f01800c40050030083d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 94925423 1250 94924173 94924189
    0x1b140306040314090a0512150a02071101050d0e0106090911040501030503031f09020c010506120102090a03060c17010303020c0a0812160f05030a080a0501090b010e0405130b010f0602010b 82
    0x40d42c0b640307501c2030003040d040382c0c031420b50000a07080754000c1450354001815102c0c40011250b010809000d050031000c1c00c2240184510080d01c1c2807403c51040001070003007603040d101146405024600176035502020464200580342400b2040150351030700000040b40321199004100081c071401820070021480001c0000f25442488060241d0700f0800c000740c131848519090084034946141c0076148a911a000b0008a80200308240200d0b0b54460034491145030001c444000e6801030130003940780c01000804598103e020b444014a030359101c05004040a00a41c01200070060201c911000c642e1b607418000e55039000203100b1805100c1250000c60910310205210f0140740080c21800c0c0b60114000303400c40b41c100c1302541500c1404124600000040c410300040c028480c540d80d0f00082d50400841c00c030112501a070104003414a01000304440c0d9807c03801e0180310070300031200056607a0310000e03036014105200708000e080450280000c110810403440300320076681c255000700722982c00700301805550b03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 94926673 1250 94925423 94925431
    0x1050a0c02010809030c0106030804080f0f0718020408160513060303021203062806090f15080a06080d030213050301050709181103070c030311090609090406091b140306 74
    0x448034103108015502540c0180e03081110001242c1ca090007034452682100c0c4a03030004c9490314000102044800b40411103113252500603009012a4118110341981c0c2d88414400d05140708802d2162102d8207d0307d0b0b054174000c01c2e802d010b58600c040218202514201140a49486010b81011405050304244102000d0f42da1603002485505080002c0030310310740004040660040c1c084000e0f03000d02681c0342c0d01041120100c0c0700ba80000e810800301401901140d0050b900e191b030031850801042c8803003152000040c00a00f0607045545a00c40428050b11031600842d04c41e200b20b80313144810540c1075000340a40b100040d03076450302940b6041054240c0d030042e0340752800109a00010321030810904109003104800402c00188280464898011a00100da80c100400c500c101400d0038160140120443c0030298030388103142c41032080004d05140166048140101c1d0301800107010011030f80d00c00000e081d0003c112451030f44007a6040317890f25030b49006008280c02080144543c9040000c3c2d06402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 94927923 1250 94926673 94926677
    0x804020a06050f040308030a0209030118050601062f0106080105010803040e011203020a0b070c02040903050417010c080a020703031e1b02030403051002032a04080f1209120a0c0e011401050a 83
    0x40c2ca4031715100c000b055000507184070070316a0300304400035080d5024490340034500c2001c2e071101c0300614103043c8a424806c05a00040c14800c0c03201c0c0d0294604201e405c1c00c0c4034910650301d080040c00081d000640148002d400c804102d41c80c0c01c1c000304207001d0000150044074442c3c915a0361030380c0c940019450502800310002c025a01044021000074542c0b005654081e03900c4c9800070000301c841e000501680c424803825004903100090900000031200215550292258003c0c0844004100000c1c003040c0003d0090007a1a408529102094400c0e089041c1d420842d20210841c0582080601c004000ea0316940003080c04042441091383d0010055404076500840540503240300c40710b01d1006980014200b4500d0310201404514511000c2403a014007590721b441c158650341852100b80c54000d00c5c64283e04142c1c0708002295181000c5001c0b220006016544000010700c0710701c00d0f0b46000350200000f060540311b00d502180d114a00e042e218101c84504001c402043c2c50f584c010f550501c02d00d0340d0030740 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 94929173 1250 94927923 94927927
    0xc070b120106051b0a080d0516020604030806030f07140a050d0b04030507060e0d030509070501031505040f0e1009020415050904170f2208070501050301060305070302040f060804020a06050f 83
    0x404640140040e108880f0b501320200e485510550070103040c142d200000700d401800200d90f40e00c01c11594070895a00000605802c0003c2d0441140650745145c000c200078100310b440700028600351801d00c41d0a0031401c2c100c0071107125944070191203c1c041c040d1450a400342144890014061421810b0100056048a0784011540f00d030749080301c0d590f02006094880c551940c00c07056651104000c000c09003007155030006000e04241648505202140c1d0102d0b0405080c2420350304025120b50800d402c881003140c2c00900802c0040031200500107400701d032580c40c0501e45040a401c402da81100420303501c2290200080001e1035810b82c8800301c980140f9030041d008030009000a40000c000a08038100c20b40c100b4141460200249900e5005080c4d6503140003140340410501043c0116076805010103c015100150400d4002481400148104810580c0340c0380800c950300d00940c1200d020300402c0c0c0c0600a840e4941c030300500783c007100742d400300c0c020b0307054020000f03d03144a00281e40d03800215401c618 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 94930423 1250 94929173 94929179
    0x203060a0213090b040204030f0b060108090318090a0f090f0506090d0905010e01020709050c0d06090b060f0711060d02040e0f1b07060f0504050c0102060903031023040c050c070b1201 80
    0x18004041e64501e0175089542040f0100100710400c04108110303105e05411031051503c0c0740014581c003006046050340340d1040c803180717203858100300c84142d01e40ea09690880750f6540c0c0c1403d40000c0c043c000248000d4a180030422428485ca017100d19500c0c500400c115081c6440b1089100d07070b1002410301050024403125410b22007584680007e000a010520449032015120303142c030301c1120803d880c0c0001c0c4d480d000400d180b14682501601d402050003201c1005003200c00c4021414521038903c0c000400c41c0300143c070700b04004110091000c20b00c0050002501c45441d040008025032041c010307401e24080f02070009c2c001c10707401c1c9a660710404241d0101d042c00613041c04603e0403a00201d9040300c145446600d503810191103881900d1207940a039004140c0c04c006c41002904041c0040c002001c180c20401c100240d5100c000c1e070301c03400c44100e10300d142a5410050060a41c1d40740700f0381c11a5002e41826001d24003542d001001e41300c11242d40d4256403240e9651303d080440b501c10240c001c1e5000600c14010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 94931673 1250 94930423 94930439
    0x60108150414250506030405030304030c02062b050105271503031603090b03040b01030b04080c0607020c0405060d0b1801020f040807060f030905031803030d0c08040203060a0213 78
    0x1a401c9441501c6050240d10303041c0006042519407810310560100c140c900804244505801d00014001501c80310318500b082e0310307125100c0c0b00052000e028441c2c06810f41046403a044200c0c0e400004500310b1220183c080d410700704051100301c0308004298201000070a076482d041401041100d80401d0b0300d03c82c01c00c0350844514204d0020841c4218070b03112a030b1003407551020320040240c0c080d01d55135020070900e54078028003006c0e40340d04144e119020500401c0009020803403034a055035000448510540e403240b0700741c07180d0b01c281c0c5054003090140b00c0c140241c480d00010000328914080b102401140d48440c2840b80f40300b183d560281654401e140420081c1308003500d4285c40c00b80e0080007502d859a0519903081c5540282d05c8008582c3c0000e2040001c242c0c012680c0c4115856031900703111b02200d80e1285c6a5038054100b40c09141e45050680301c3c0603030707400c0040395510f4210280070302c4400002d61002e000c02d0801c450580c00b81c002c5200084024180e842280e081c00c0c00c0b08400b014044c2043e0785 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 94932923 1250 94931673 94931713
    0x2090a1103041106130602030408100501081f02131205010515060f07020a080703080d14010506180d0b1009050a0902060a0c030207030209040b0601030b0f10030207030306120302010e0d02060108 85
    0xf2042d00100c0070400d00c10903840d400c0003072010309550b0700203651f91442e0407991443e0a02e403030b03220208945894014049402c02140d0348510440c2092154491461528410000d1188a048011aa4001800180b10782d040048842c549002c2c40003007001d0355941e03070111402c504080203a5030150080003c52107043c401409800c010740064885842d01c0e4a07045114a0000d841c0c1007034a8401c0040f880c0358003190340e070041c000101c03204003110341c07554035141c04030f01e0500681042d003407403c0d1070405d40308460701d824001c08031454012103081003038203007241d60340c004441d2400f404054504060001d05585c0070741c05601c50040d03024000f5440d08956070360440f9120300c500421011405440700000251b514004402d0103140038a60307680890a04100143c100c034111a422802074100311034400441d91075151109400407541030140ea9101149400c40c0200100d8202d041c0304041c07402540245981548902072803003499085904070741010350240e80c2c1d00c000f4440c0c1e049903441000060a8004a201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 94934173 1250 94932923 94932953
    0xb0a0311040503060103061b0c030c06020d0b090415060605040b0f0307120c0201050609060d0b0c0c07030c030503071a040503091c02130509191707030c0804030f02090a110304 77
    0xc40603080c81c0d2a58002400d0070401e078030a4582584458081583e4019a11181d281c1d0903203060494134400305940142004030414000740195a01184001105903241c00031402e402006142083ca4a414508564105407403c0351004a9142c440c1c00b2590750b004400b01c4080ea180c9008d55400d01e0417800d00c94010303620051030201000341c1103030342c41d101c9001801840045042078002061600e000030600c900b500004008d0f500c80c1a0640c4201c001c220b261401c280c11010096040d07a4680c454440d8038642001544010565108400000184200030000d084501d118010030048103088c205804940384041d50041c00d41d0b0810800c1c5442d80c034003202d02102180c403008054811180ca030300060354100d0707001d640306d08940e1a501042007064051058561090341c483c82c81e00c50f50300a4031808900041801d15041c1541c00041e45030600d406180c000814070381c005121703552330f9201d1400d1418207003000c00807400303801d00c90041103c00144e80a001c102c0f100504403281540d03915201c229194070415 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 94935423 1250 94934173 94934201
    0x30204081c0201020f04091e05060112090309050a080f0607210c091d06040b100509010c020a0b04030305040f0605070b0601080a0b0a080a050609010203040f02091803040f0302040e070b0a03 83
    0x5c094030241d922080500001c224600c0c0000b604840c440718840d40130000e1200040041c500700030000b0503a00001c6600640d090347c6c0f400100089985016601c003051a0000d0b94000c2031140d00081184001441894918820055502940750300d48140d038074680700c038403410b03c0c1c40e00d44001300010300342d560040e102d84d6018903102c0f0407159030b8540c0011a01019400110800c2480104200b40c280740c010502010000d840d42d43c0820f0711828020514007608510030b040054454849082d5a6003800d590058401c51042d241d07196500c0c600946658403611492081c4410b41e80001101405241600d4030543c10080c06e40307941c1d440d100110344880000308046152036540c01040f00d1500d40c42c8102018048007001421401a6808e10350314040e0b0051111050b80e004204200c005410000c002503059410344010307040d9158040c44c003443c0c5071200c01c03448a5101c04103000605a1003411b40d03d0031207000b40c07000c01c5020f100c0c0881503107508550080400241c1c00b04064101c17144603600c860040c138440c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 94936673 1250 94935423 94935427
    0x11090607031403040303020702101715120303090102070201090605030f011502010f0e030307122003091504050615040c0807050f0c060901050f060603010e01260a12020706030204081c020102 83
    0x1a181d91940c3c1c0c02c15141600020350210b002d5003181058015218000850f06004495510f001074150710000020250402110b500002d403006440c0c00c4401d03a03164034a001920307180d15006079007074001d401c040c2d01a0300150325060700084c018054000c46e4021001c206a07082c0580c28564120440f048188034881150759501030314462280c90b1242d03000360140907001e5a0b6074181081c004140e403480c000020740780c9152200d203002d40d10110b001c51443c1e00c86824040c0d125640c0094050405500350b10b0b0302e0305c0c0f5814404000c104840450300d070388607407007017501d1000b1404030b07800340f004840558622101280c41580801c07109806071018241001c651b8010a2501070010402030130320384291494206691a04140420707030410400c0e19500c02c3c0e0540d5485d0a540c509041b00c1c01010381072103480340e20501d00403c1586440c040c40d000c200d00e2802e508a40d0449158a170201c0c030b070754101000340f0041c0903110b00070035407500c01d00032102107600f054014401c14512440c1c1407402946424010190765003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 94937923 1250 94936673 94936697
    0x70308040201140a200f03040905060d020d1103010c03023c0f0c19080d0c260601020c010201060501140d09052a010f0c03082716091109060703 63
    0x3e440c0186000c21903903440306074a0003c0c0c02503010035001d0154620054005c0300c0412003800002066500720741d0700001c0858a80c85000202c4d0111500c960080e4000fa9400710708400c1c00070856000c050302e030013600204490705031500100e04074040c58400d009106000006030101101014002c00352844203014201c1c4840c10a900058a5025081c01e400881d00802c021005540900201c4507000956920b01c084400741e5454103600d00c00c0070221a0044d555100b440d010a00c43c3c50048500c99800c3d8524002c400c03494018820944112042030062042c4500c0c1c4860394418040c82d0222401a15925484003210704400401e4000010900205d0740e1002410041041040380d440b1000000d1a4481040710380300172031000c0751981500c0ca0610410340a4150655800b014003540e00e81c151030408102d80b10201c0c812502c1d118a02c058940706242c012541c1c08000110349424510039840341450070a617180d816000350344e101c5000007400007080c020b010150818030020151240309c0e240c0100315080d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 94939173 1250 94937923 94937957
    0xd030908030307090509060a0803030403050d060801020f0c161511120406090f061d090403020f06070305180a0809041d01151d06030d050d02130914010e0705070308040201 75
    0x120307107010006035a00d0b400c00050800d10901b94100400380c074544100c40c10072200c90b03501e10000e40010300f005400140a100d4554551180307001c0d0903540e009555525440e500c445082d000621950103030302816051903042c0281850b520101c950a20b00c01808103400a410380740c0c0b2200d5030b545c1925000c1d4040d4031b40d072500c1074030041c4050440c0c0e0301c0c1c007440b907810208414008282a00320038107200d01c5410301120500101d141b40103111080783c01e034603603903540c4c50b0480c10030b1040d40713070002a8482c10b0207200d403c0d40c060300324512407098038115001d00b98024000c07135500d406903c800b0b4407002040190815500345604080d8106070881042a80c00720404c858608450707100007002081c2d03144000a1020810700d04842c0d04407410103444010034101940060340351040d84401c50180b100016000300603132142d40684400d80d50f286044003000d503172000f842e00903098400008101401080010400c500428100c6018075903541c0d445041030402c6d501500c44550142c004c2e81403011118010351218 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 94940423 1250 94939173 94939177
    0x20f0105040f0914070c03080105090618041a06030d0e0418020d1202010c0503160804051c02030418050c03220f050a110906010c06091406011508070503060901050d03090803 76
    0x403e001800060036400e050440d40e0760140601902c04001444d051540820360005280d41580c10403540c81a060721136900140c1c1e141d05c841d00c03007016040c0200800c003e010b503842c1e9540c004070300d800c8428526552002010780b554423542140010594180109a407414a80d0110103508500d441d10b09820032680c000a58121081404580e5881480a04130310f266083c09007039014455424000e0850401d82894001401c1c0d0105607410001d5060002d800d00108000e600b10b4481514200c4041c4100044c0003926584180125120702c82a1540c1005015052044a1095524003c1d0500316281d41042c0107200c0b090103040071002400090b4400800c83c1c41ca01507203039500c81c6005200c0900d292900c03041c00d902e1002800d115036844820000d203660080c40503c80140d1210300092003c400e89440c401c0247c0c0034901c2c0d013a0784500f80021851041c01048010a1906a12480c0082da10000c08982e130740b1088035901d4018820380010402c505103001c041e4405c0e40300303003010001640c0740c1420305d1440e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 94941673 1250 94940423 94940429
    0xc02040c08191e0e060406111201060c0204290a0503030f03160504150503010504140603191b030807020a0b040501090b090105070b0a05011e0506030423030409060e010e060d020f0105040f 82
    0xc1c0d080170043c402040080d1140400c110711710b81d038050401c2e040d1090ba0301484014030501e0144000715014504650750303070f440102090000d044004001120030740d4540700004a0010a024001c00c0e10049179a00c0c000054074550013000c3c5085203942c0d207004070041e08441514021090141c03c5c0000704914a0725040001104516a203081c0c0300e42c9400204003d580e424000220030b41d0b410b406121241c0c4010480c0c101c0c1e4a8801c607a80300340d40c0e0f5817400c40302d2900c501444d81c2e107141842c1400301c10071040100600c0030074001c03241201b9860b10344000e1101841240304040c040346450100304980c02c00100030b09200501410f240c0e0826421352142641e051044401818090303035000140030361684025264800e0599149241c8000c3c18840810390743e10025102400310030741c500e0700c1c000e085a80841100c02e02c3d40c820030349071115039a00080001e04118000c5000c00f0200c0b00000c110031000364130036071080030b0050440003a240c80d40c0038002800201038901e27040120410002c220000800040c00003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 94942923 1250 94941673 94941701
    0xe07030b070513060f0f1b06020f0a08060a1211011101050709031b06020a14010207081b0d03050412140f0a050706050114010909050601031b0c02040c08191e 69
    0x180d000c1c2c0c041040c0c040c542503013142c030501c082c44183c09000c80e8080d02d403aa020050f41040441c200001211880c900c024440040201d030000410703d0f10700c40c448000d0310201c1540d440380311258030f0303000c1000808042405500d032038400344000e960200e4282d400708202e05c079041c1041549203546401440c20340c0c40495500010a82801c410820080315905420541c81d08000107502541041d40084d00d80c102203c010740383c1c1d18507400040403507000307504a4040f141d00052195448a08854107450b56000c9003072040ea5005411000324024040c1c00b40c1489258000380d552010740c1985400d8890852030048034444040a01c001c4460b646080000c08c50410562030b040d032502e800c0c1c900001501c2c0160130500003425000e00c103600700d90700b00701c0c20408c0d40c8103220046080d071f0381d280c0120028001c42c10080201c09180460b410b007079030000c914043d402e0013591709003d0b800320301d141610301c0740058643c0b41e00929240d051240810440d404240c214641c41c410311070070900d40c6907100c1561104002d14803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 94944173 1250 94942923 94942927
    0x6030a0510060302180d020a091e0e0604030905010f02100c0c05120c031c0b0a03080d0c0305060319140f070e090a111002010b0a0b25020a06030e07030b0705 69
    0x5045807241240c1c01c0100340b40e140951500d10007400801041c80b41d111001c5c0920707070818207030b821591041090f4000e0034507444c0c10010941e091302c0e580701451740003100108447c60040d02c0c1c0070040b07010840380c0c40f03290075880f04400c00307181200444050b018a82c5c8a0110b002e240303551304003a00d46000343c61056203550384800903800141040b50610400180460212004001d420000c0d400071050783c1a4102000c07456012003441c0c50550068809104165071200004401008110811003c0c04001c03071190410002900340d120107404a9200352581076055000da407212192040212a41001b144900001c03030508100c503028070302d09507940754080703566000041e0038018042036842071540034550400030041d44019480300d450350f40440030a0790085842c17035500070f5428000d40103107400aa0240c002480d1355666003118000f0f40100c000da00505026140b10b540b05c202c0d01110700122a0003c04020100c2c1c81c0c14400d40c005c003015941042a0b00071048004003040a440c01c0f54480e40190310341c55 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 94945423 1250 94944173 94944181
    0xa170c0a020c0102030c07210c09021804020711060c0304050301020d02070218040308070507081b07030204051311060c19030302070201020d050c030a0e040e0706090305061503030a080402040b06030a05 88
    0x1a042c00c0d1850942e070304541c014040b070040035400007070941c2101c000000f40c4210801800307072154802c04444000e0802d01000d81c000884005507402820140034540c3e59134404451802040f003688502e007405020300d0100300c029001c5141440c01004900e100d07401310303440d05076581d000c41e0076030b044004003444c6c2d42c0d40428200150b040901046604503107006000c10b051400781d0380074200d0a809400c003002c001010a90204000e0304004448450300725507071900a5807000000950384036040d020807401141000b001c0360f401c0c03120307a910010162b40310380f040c20345c10170704401e21515030050014036401c0c0c81000c003841d0400003c0304840741c417940a42e501603500c440c1400060702c0d05040403464004c20508004c0420a680007100b52421003238540303003a03145980260001805003034040f41c4404d00380038507000040d840c2d8100c2c01c810100c03440b0b481580e0a50760307400f4801c01000d0b119080103416400801907003440c02d00c2940100e074081d00c010400500341e060400403642c80c0d08111440c1c01429a100180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 94946673 1250 94945423 94945427
    0xa050406031a0906012301020705041d0f06010b07021207090c11190b04060903030e120c12090102030a0f14070b0106031a0307050f01020c1e0a06030b0a0302060a170c0a 74
    0x42c3d0b4411041002011154507029001c04040d0b10f50030a642e503011028800e01d181c0c1c1c401d0100c84001c080080042c842412002f115054502014013144820310509040a020071004a0114100c0313a41c4401e103070510303a07540c0034000c040c44403241c010300c00d002e41c00010844803803a00c074200b0210401c0d65030749070754402d41308002c1c5480400364105040c2c6c250f0f180745031b001800042001d40e00540c00b11002c280c21840340344c01d901400c1108900d0070300d8014602800c602290340405030510042c10310482d481e031040028803251621455401d68016001001a09002030003060b001003189400c0c83c245081500d100031184041e00300060480715406900010801c071541030103040484004a4450200305040f4400a039803440030b841000c1c051a03c01d4030600444c0c0c0240250320001c500502030310b52144c1030541414030603542800c12807251140784804604144248124068000050240343d84903040d5020001c6c50703000540107a04100f50b2000410465610f030203118020007003840000d8580ca02c40c140 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 94947923 1250 94946673 94946723
    0x50c0f0d0e100e0604180e0703211103090103050c0408010509011b03020a0917011e051006020a05070e0c0403021207050a06052505030702030f0607091a03150a05040603 74
    0x240d02c03c01968074072815103651400111030031642602003890104100800070b0380a051030482e43c00301c0d030040450000034403041e81c529001401c519445504481c00d6050242da92900105a0041980c014850031036030313500aa100c5c0381c20070030302c0351801d0606a0300c0e182c6c0c07400d507032080322080c0c000e075103c03c4160060b41079110817001c0e041141c181507041a00102c40100320003450b10a0030605420401d2218951000390302040344400a240c01420409508180401500c82070340c11220b1003403540e90001340c25101140240280b0b40c440d000d00216860400090b200d1207000c0e144030f2000200f08400401a60345000d50b050768880b1030040d0410740e14040c20440c044c80340b0f43c4000d00784081040364441070111508a5403141d4400403203803aa8030340d2420090320714014241c0080d054481c2034000c102501c000207802c0e100c0d00c06990740c0d100440c0c60f050080001e162100c844044076030103201080e0059070f0120381d841c2801018001e41d0820b07944030000360503500701ba807094409100104816141c90101e00d8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 94949173 1250 94947923 94947949
    0x2d0d0c120323181509041104030209010803040e04060203091501030f050709020a0c14030d2301080d0801050f18190f0b03030406120f021c0506010c030807050c0f0d0e 73
    0xc0ca50403e0300b500743c40f1499484250360107110303d601050199038001c1c100160303010f1040203030003040b10020803038040b4201d40c818041684201c1460f8000074074908000200d07401c1e070f0b009105074001511030356904000381d00007402c4d807840c50061075038550079404014141802503001758040d00b103503000c07802c1003030400b98541c011030512401005600d60311600151b0f844aa01d6001c10700e014050810181d0780d0840c0074040110010034202000c06122034040210b61039080c0220111a4860766110f02450b86da1412040143c00705040800420075071914401c440a80b9002400880329448800442c0e48402c008807000880c0745407550008446140d0781c41400000306000d60200300184100d230002e0360b82d0141d88521350401002501c00d12a545045d04880b949140209055498a00381c1ca1800c07000c1180420001c915403600001030394541c4100d5500c400e064140d26480920b88030020304503003550000440465a1007501104842000c040040c0e18180c021641c94100140000d42000720714002c4038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 94950423 1250 94949173 94949237
    0x303071d040603120f030b0402040801060512070303140702040b120303070225031112030d050a1a2b020904060606180b030a020313051603022d0d0c1203 67
    0x80000e2001407066041030b04d03004124101041040c030440c1c8101c01030001040c131160003d0002c500094000f005401240c03c0d510103d0b039407480348109045695903800d4511010b4005080000b041140342d81c484004c02d901e40c005040440d03044460800b05203e031295959000d100d030f00c0001000911a81405005080d226000050740904640ca070f1000703002c400d600010785014820151824166600364446090700440c1e003d4a032a030b00d03400600340040004031581c14a00381800911080003103035601d03a85c0c5109e40144040e440704494103803200c04403907540d0a070392568a40d803001401742e0380700700503140710320b2043c800411b8160502c0c83c000c091310035141403041880c51001040c005000a002640e078411030b0210700503120381e1840e0341d03251582d6455002600310f0040594190380140b19249a1064038000c0e608030385005200e940501c442042000800e0748044520107000541c40c1a10042e00d499010755843c10403c0d48404206231041c070740040881c04a50100c2c0c281ca030f803291409038810596190 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 94951673 1250 94950423 94950431
    0x90b01030b0c16080325030903020601050109030203030703080403050913090221060f04171207030507020304080a03050912072706050d0b1015030e07050405100e040f050303071d04 79
    0x88000390a042c2031003801007829030040000b408030051011b40320a400c40150b14803090412414018009148103002074005000349400840c19500490350002200d070301a00951802d00d5540f01110041c8019204604002007001210a29510421000c98901c44040001440c0465104100c081030110031803001000c000c1c010604212000300d240d590000490010014696903031a002440d000035444504404401281207420721620300307842e500c0340c1d0341c1d5101040591102c1c0c0042ea540d000e18800c02050754400540c0c0000207110724041c20300d007030000e019030301440e801e416100d05150040e0050080341e200410303000c084540b1a5022070b80148005801c1002034102030200312400b001d003401903d40400200856803041c1008500001007041540c1d4085d030064940b4010064402c01350495018820402c0201e1189010300c26180102c00d500d60051100f0700d810303640001d0b424010030503105800c00e0089640070070b006000441c8103140780d0f50340010b0340315047c10b501000c41c02107002ca0300035850 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 94952923 1250 94951673 94951687
    0x1308010506090606030414030c0604060203070e0d1203020f0405030703050a02010206070507020d0b06011e03060602071e0e0712020706090606080102070c0515041706040203121e0904090204090b01030b0c 89
    0x1500044940054109400d818042d01c0c280f91180b0714400e0034078004040c8910340420051140c0d9034065800707042c03c0e980d075030010074381c000c10060301d50711041e0082d020590488117070b0304141c001e42c0103103611000e04010a0405c0c0c0d4a0740004d061444c2c3d90310940c1d60750001c00d45901107603414002c1c0c551181848c20008e051513a6034000c038961102c00c000040c2180e02181c04241e140e07002e2011120159440c01d441c1c3c00032541001c004000d071040f4030075200940325200001c03c130b90309081044660113080d4003000c04d0700c80c42c00450b260603040181010090004000c050503500a03c1d000400341039024610100307840c01e03c2c0c038044007122290b074800305550f48103210220009120858401c115401110148001c03954a200d410587c440d651100c04540800c11415503030420118400d40b20758000c80a03200c02501e2480071509a2185000007042d8614002030400075204010241204040c064000a56181c046d40400c3c1110803200080d15140001c1004100b003040304c40c0d4481c0e00c140e00c04030303040c14440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 94954173 1250 94952923 94952929
    0x3060c0405010c030507080310030303110a0219080c100510060908101a040e0105010801050f0402012024041205090a050d020f0a03030f0e040519020310080313080105060906 76
    0x1641c0125410818038000300c0060600c500c05036501d00c1d4210303c126549080c50030a020400b13015100450200f810003002c00c0354100c500043e100780c04402d130043c11b659945101c90542038204580101c540345805d12904052803020402d0010600c3c07115000202410147c60250071642107620030820001c840030705000240300401d61030000c221300310010420304403030b14410421a9540e40802d0f0090724251107580110015000181281d842c40001c10003500c50503070031007100038111400b902003203403082040071000c07800001a0100181005444551851081920842a03103400b81d030402c003d201c0910050025031000004030601c5410698903100700341000c502e40c0c5205101e4a845288030100c8881991103080e00903003245001008444515280e16003e06000c0300144540b0015154010300c1006003060f110f510f00540103c040e0707150740e004d0182c602c4080d42c40245414102900c1c400002000c950410161404003d4210303031258880c24980c00d6400c50b40c00a056034441e80b2140148046a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 94955423 1250 94954173 94954177
    0x905070303110d09140d080d0b0a050d0807080c0a0c1202030c0d0c05010c031403070504030c090c020c09040f06090503030105040c03020f0403030c0212030304030c12030504170306120303131103060c 87
    0x417100c64507000640b0802c4c0000721602e015100140490b50300054035814500b440d40700350150f400440d983c00e402c54a0f1001c2c02002408004010070504e000c010341c501240c03c5001500c00302c0d641c00c00329100f503881561805a106080e9002000c50700d9021060401c44c641131100d920510001d440c111003205045c0c45000c90650a48a5103041c441d07911065001d151180d086282c0c0c0c442c80300c1c13100c0c0d40e074242002c0c000c00341d5005200542d079101c2a40d03404192510140208416900c540e03004000d2a17020400f0440c1912018004681450714003d0100010b038a600070543c1060041015503220340c541014401a2600d00c842d130f808152040181c44041d924403016102540d07003518103411580b0756440070030f0032040c03054440b038558440481000201740d40000d003110038912a102c41d034403410304400f099050f54000e690041800d20111840e07400c030100f90020f580d115800806410b1103400c8150f07094119402503444000031103005046d6414460180051400c040c0c05400901003494000382c203410b14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 94956673 1250 94955423 94955429
    0x30c010804061a030a0b0907080f0a1b05100305071d150306061e04080c0a05030c120c1e030c0f0a03081c1107020112060f03020603090f010905070303110d09 69
    0x642e2203000d00c01680c0e40041c09400c3c0c920180c2160034002c01c50800d104e06002c110b400d40b40034496050302007615803001c521424078640c3c43d001080940d040e96285601401c0d80908100442c02155001509950305800690041c420b40c60016003400c00303400003401c1d60030031400484004220041300000d9240c0200c05400603002803146502d039101d240020308607224060900b01c110892208520a82d007410b4018000c485541c2c1c110383c031101443d01070044a48c0ca61007480c1d03060704a00503100c0142000c1001802a9445005a03440d00d034540c4000303405d0b03c1c64502d0054100303005540d0000341d4201009101100d042c201e400340e14070800000050465419400010300e910000305ea04030101140c5c20400c500c9016280042c05040014450105a078010180a034002624070070342d545200303000e00c81c1006440002180c0a0b80074116000e1080b1036002502d007084511844c030f01d8100c0c508081c4540c0508500c160090b1103c00d2850400804285660161446a821000c0c6400e1001e401100702022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 94957923 1250 94956673 94956683
    0x12040b0409090f0f0506070e0301050f010510030b120a0c05120a080d020408150a050a27080c030a09080601090203010501080703050403170709060906030b060703030905030d0e0307020f030c010804 86
    0x42c09640707001082680d100c00300401d1030f00c0c00d281c50000c001021502c0e521811f0280d4030300315000e1800c4101402d82f801900c201106050b40300060005041c030003590160b074145428081101445040850f500b070b05210700c00e290b03076040a078204080054481819005202c210707065081d030040c4010301c40d00d4130307000a001400401c00040954042c3c8540e010340380185074100640b20549185001c20f184030f041290f48100e032030314201c000b40300e030340641c070519600c0c1d89010b4010110b212080ea01100c4191803030310655880708148261061000c08100505168400d5500c00004034940000a8600342040e0408071401e07006000610040e640000750981c45002460702162035291410240d070b03070340d42c2c0341c400100400d041d000b00030f000c5401484890403182150382e4401d400d507a0300d4044007150410603019038001e50810004000c20b200348c02ca090120300403401c0c0c0e40307004084151a03003298040303040d20b0b45a4002094000c2945813840314071400e0302c0c080e0050810180b1690000b000f1020080000305 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 94959173 1250 94957923 94957931
    0xf05010f0513092408030a03111201050603060301061809060b03070602060601030f14090d11070303020303060907111b09010603020a0e130605060d050a05070c081206010e0d08030912040b0409 84
    0x30748603d118104000d0f80d03a4100c4040711382d82e21042d4140d240ea0015402c000801c2c01e000009812091110403509840a05156981c45074281010042603030f1001e800c0c140d01d50f481d0740b404106280d4841040501e0b81c07082c1c6000482181a1800740d0507541c204106c0b5105c0e03040f4220400007242c002c500140d000f0070901e00020080300c01450768005044442c880c07003000b0f1905040000b421000150b014019206482e403800d100b800445080c0d41d0241c0e804014010b80042c40401d95904080c08003d07082000d5003401c822160002d00c1c0c151800c086200d0921200003035104444041c1080c50419024014500c0c0a52401c8042980600a07403500c0145500942491240d07000511041e4040000b8050007842c1d541d81d801c400000c1c40c003510054450080091411380031a4465000c1c49011700c103254003940c1141049120250054044002085541070203c1c44641c01c02a0fa2102082d0030107a1140036003a81700e042520905160003400e070117860005108010521103107629201340d074200c1d141902d01003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 94960423 1250 94959173 94959191
    0x30d02070807060608100509070503030f160203160905010603150b0c0a0b070512090304060e01120e06010e0f070c0309170111070c030213090f060c05130f05010f051309 74
    0x1074142e00c500c40c0050032161034801d000c5602200801e0b00c00c0131a0300000188040d03108e5a0342d081e151a506c0c4035441d455407003080000100c003076240245c0748071201c8a040036040181600805c0c04d09030400440c0300e44990001083c40710045910a240c05042289420040d1610007a0790a4145e040350103182c002c07201c04908900d0f16001004440e020710307801803180b1924105004090541c1d008a5030300c910107805040010884000002960100c0741103961b100500080200103603441c5403980c44407401141c036101d80c9040014100640c40c000c3c140300c0401300f803134680030101048200010f0480000c201d600d1a008010a5000b101e9205a90400324030014411840b1030a078010030900c4204089038001142035800e01481c050400100c9000341ca071003c0e607000c0031003d1412980703a000000c000b4400304901e60007003100c0c1d40c00800100c01c030f401d0961803c020300500481007200307540300340014040d202040c0a1941e02111a2a02c9070907410480d00700f403080440340e00f8900140c0510764960365940024 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 94961673 1250 94960423 94960433
    0x2100b100503180d020615180105061b010204150906021b060309010e011a0405161b03090902030a150b040f15350f06031b040209031914010905030d0207 67
    0xc184404030703c202c541d00704000c0406521480b003200e0100030340e08403541c1480541400d00340c000943c0a00c804810490307083c841000103a420480c00c04200c0140202c9801c0000800d100500280986003141141e04442c1840144451483d804c6041150018400c1c640e42c11041098210502800c450300c0d520399580b14034850041880d01c580740040d40c2001d0784400c80f0158500d002400c481c0c1940c0501c526503d40c4840c0c2d80301c14280500900040c5404912070300081400040c1e080035229180c01c0544540d9010500c1c2660402e50b290840103580388500d401102e1100700d080000c2201610007400c040c602850900481290b02c14100d50100c284103e03e2824441c0000340d8400882011080f44a000480c940d0200c01034041002854640000411207a5540c601c0c1c0c1ea109000040c001c0014155800b08985042e060b04400f80c1c02c682c0a100c5040641c1d4148060310a03040c15401e04100210300d070a01d0300c1006040c0c602244c0c164508504900420004012034081c280200409aa02c2c503151500c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 94962923 1250 94961673 94961701
    0x1305060102010e16050405010e160309031707031d011107081e040303050c010b0303040f0306020d1d0123090303040b07090504020403030314060a06050301060e0a1706010602100b100503 81
    0x200c200140680c051404c021201e00c02d4203001d6410a6030208500ea032191146900d4200c144c42c800c214080a9031382d4000144260400c3d040e048c82407410099150021540380840c3c0010380e141c60120741c450264001802401c001c01d00084400f400078004100301a911342c5103442040d4014000701c8002540c5040420f11210744003211000145441d503695481c1001050383d0800b0070001155400c0400710410f919000040c0ca090359151a1f803c5409491551100300039400396058045035a00d40070ba0b4903c955041c0c804080e030351380c031070000b00746400c00c0705510f1001c2000c240642c0c240c410507000d100602e0000019260b00540c040da808030aa10f4030201a0b4142013154000f680c41070000a0200c1010341c03503080f84000350116895880e0a807150010420014998002c0e100021028001006207a02c5031414010140010307111003401601c40030400d6080019140415583c2e0000d4010000c1c2a4100031561002c2500c2804001c03410003c40055031005400328850200700d80480410444242c10f50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 94964029 1106 94962923 94962941
    0x7020d09030c050907200d02162303120315010813021e0a030615050306010608040f170f0c01060312020a03120c03020c030706091b05130506010201 65
    0x901c103000d080104907000f0004c1c0c110115411903140480035098503120000752611f2102a00040d02c2e002d8400810903000800031b0040000580407181250004200ca501946100110000915000342030125441100c000410f01c101c8101603460031001007002c1e200c5241d5683c0728041e4000985011388041e41048601050a02290700460206100b0707a0041201c40030a840b9140c40044594244400103010304074013080c812480e0410200d40100068540800c1c10300d0709980f050785440c0d1620005026039080480780201c1d4001d04183d0340ca0b0358281065944482d0f132102d809010304418401a00c4448103011358141c0680b0100b000d001240e0140c8528260b501c00054001c020201c50b00d984041580c00d0205074003480040c0001c011540c001c18020508545174141400044101c04042d444000402d0080000e81c448401d040c042c0383e4005000581c0e076544c68010303405001440 = true := by decide +kernel

theorem cover : BRFrame.Cov 94784173 94964029 := by
  have h0 := BRFrame.cov_init 94784173
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94784173 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 94784173 ≤ n) (h2 : n < 94964029) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
