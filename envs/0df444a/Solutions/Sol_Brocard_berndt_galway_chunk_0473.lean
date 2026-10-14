-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0473
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:59:33.493706+00:00
-- url     : https://prove2.me/submissions/498eeeab-755f-4734-aa10-71ccf287d3f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 84892087 ≤ n < 85071943 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 84893337 1250 84892087 84892111
    0x801150e030a0b0c280207050d0204060312110609060f070804140102040602010b03061608010315020909070c02010806100816050706060f030b070c1a070e0d0308220b0f090a0803010806 81
    0x1009a2040c2e20410540c1740e106602400c01c203410710040101d40340040c84140d1b44191140700c0440850310700c406058503941e0075101d074002105180c06560401800a010341042d8000804100001d480c950780c05504c00d0551402070042c4c0d8441c5811841c5c0b00c440c0a11034013a600c04100490520340540c0320080011044040b9035042c0d0702e42d110b01e4040401c81e1160800140c240004000244c004211040e6104248101504215600000c00c015034000c8402c0f170001100e1001060555800c07000ca0f54110b00143e540040812911902800060b00a00034400e82100c200c0030260782c42c0f283d0140e40d00b080e484042800f25175680c4a441c1c464003050300007074074185a43c4010401160040410785540c0d035002003080b060101e4030740d60000c0403030f0082404e01803002c040c800d0486a99401071114400d44607444142e07980c1040d406004150307075070103041c5045280ba022a10301041d200051a580421a034a0301891956105401420041000c0004041d4800030001103602c62011488038800c00b40c500203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 84894587 1250 84893337 84893377
    0x304060e01062702250c120b160507032a05060c0d06060f09090c09030807050106140f01051e090d140c01030b06090d170f0306040c0801150e030a0b0c 66
    0x31500302d02c112a980760400c40744600c07400b1a017003062a0041c0403400b801c04400d0341c0d5076610803401c4800c00c03004100c5e00d07002150b04102c07024014108603240032003903103005420102c06a80281000003204503481c1095241d10b0715a02144206000003c0b05a000c020f40e040703400d0050240720160800e007042e842403800c0c01c0d8041550b0307208001c400c90615403503917010809460410050000e00111048108010aa04002c4041340c1103a0081c013202e4030038000001c0a0b4580304482250182710185039200f03091216456405a03405000d4480343c1001080c04c1151000c181c140d04400d1207100c0a4035042002c1610351420300081f0007402d10001c114006880031204224011012104e441d4001da84c4600e05022820840c14403480601075244125100c0e1804072145050a0064201403810780115030300008006950600e40910440e42508e0304080301294140121203a03802100042d00f0200034002140000f25507040000400d49a00306120258500700540d0310352075a4400c8500030b20036022080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 84895837 1250 84894587 84894659
    0x20c0610080f070b0a02010212090309031b010e0405060a030f0312141603181506031b03050303010605030a020d0f09050d090b030a020a030603050f06100906030209010504020304060e0106 82
    0x1a10050700380c90b0001501c2014103040c2d040041e5048100320604665091002001c02c100a0802c41e014055840055440e040e49000f0140b5194070812a1001c1d8001c024045d02d5603604501081d080d240100c03004a01540c031100842d005445580c40507081610119911052607080720180341c501860b96410301842401081003403401030b090384d4018042c885808100461032081d446440c0c540440100e03142c68017401e4482b9060320304140c2e9651100c4d03544200420070410300e0404c0d00c9081000b44010140c562070364036825280d010500c121800e02c0000000152114040e90403200e0341c281d44501000200d000740d8107a0020040b60004841d80d02c1240440d802e582c2c040d8105c01c2c211001c01c401c4910f95510404520080c1d0080f690311002d02d03441e0000400010428045c081280c07140b00700404151502009400c849500d503400001c0b0303a0300c0d0117000d2000d0788170248400c3c10340700c0036280540e690f2907514010300140b0f008103000c0415441c2c034a007c41c80802240c40681d514044009401d04440422 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 84897087 1250 84895837 84895843
    0x212030405010e041a0901060f020d180e04051002030405010603021003020309060610020a0803090c04060510020a0b0411030607110d020c0d1401060f0e0a060f0308070f15020c061008 80
    0x200400380401c003400d50010303491030326030032815145ea1644482c40740e41e020a4041210001c0c00c0c1c11840c0850451921240150350400c01290f50100c1880c200c441038040c03000c60b80c13000ca103034000c4004064143c400a010300900300440740c00380b100010110350b207240c0b60500500030042c41c00200d2099212101417844140f00740207590090104070090035203500c606c030800540004030b0036070038294002d0030f18040105982c9005944500005005481e0010b20f80c400c000480e4500d8024601c01e05074074074031110f400c1d40041c440400d198412541c410503122030401c3c98007400e01211041d41803082004105c06a6408600d8450442d14001162204d4007071342001d0341c541188910560304083d01c44004400f084044c8a000109040ca500000e43c2a0722102480140d1805401500c40750205a003070001000c41486200d0041c04010040c2c060303c1d003980e0b12809244a0a80d01a041c41a4560b81c00c090200e414442071481c0c80c001e000b15035601c42c0041050f02d071602119000c0401502e0340000696501c08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 84898337 1250 84897087 84897089
    0x9011d0f06010905190b03011b05030618091506030a0f0624050f0d11040903110c01050f041202040b06040906090609020705120c03130f03050d0f0f0c03030209030109060902120304 79
    0x9a40c1c41c014400e001c041758000b049280342840c3e256484419002c0701d00d1615650301c00441d4242e49480c0e80e0300d00441845036100c1092000c0c94a003c0f40c600304000c04d10081500044031000003d01151a03c0f80b0300005c0c0340c0700e1082c1020300710101c4101e00740100070060b0b018040014420555001c08211030000012180741840790b0780d048405040046203501d80200800c02991152604d03e1001c0646000304044070042c803011004240350400302c040c031100800c00f182e030540e024a0605e143c05104003d100b01c0f4000d602c510710311141d48000c00811541c0760f0700240411880600300907150b90352407140f440070300380900c40e0034105880d0440110700d503003a0740210380007650403d00429500d10284043e40640c0c2c0301c0b000015950000384450819444411002001400c10b41190741c1c0ae06e0a41c00d28038100000b20b0582000d0082c81880441c8550708a907403444d1080030381c104101c118030340d130a0507406841400f100c01d030b055180209140400001750b00c02c000071802591002d03400440303444025034a05c11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 84899587 1250 84898337 84898351
    0x13061803021209010225030b09060603070e040f02040c020d0e0a0e0105090c040306020d05060112051312200123090a0609080403080a0f02010b180a020309011d0f06010905 75
    0x441e4001c1c046100b600350003001d8245040c8112a1820022070070b0920303541d010b4802c900300154005c0300b0801c0c000c46070900780d004070001015004905218001030f540345100c2c410492481c40c0203001405100d40c25145009594018105010005040600035119065400740c0000318804800c2141c0a003011008174054a101c0c000d000c0844e401d2000308104c803407000b0f013515140001000003000140c45030015204a0705003c0c0d000c103142c03d000c000589101800f41420b00f4440c03501c41080034800226400ca01203503008078415803840803420048400d40c000c49400c01c40c15030340740660440880b05610540340194032201c234060503041510702c00b52140c030036602c0d003500d9440a06000d01090302035001d500b00301c3c410701d0001e1a02e60b43c0e5179495055040741d044000410703001d00000c2c07078441c2c0a00860600707480031901d03a49113501100080c501100081d0601d1030140e4040001a94a4000d60006840d81e11007603010601d49403074214580d0300c44466a06581d40e00a200001030b86146074040c140c080d1030b03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 84900837 1250 84899587 84899593
    0x607020d0804060203060303040506071b060302070206031801020c01020a0c0b0112051005090a0b130b0603010b1302030406020d1803090f05060d090c030c120203060603031612020a05061306180302 86
    0x2c903a1542800b03500064681a414001040300003095a00c640042100b00d1160300c2e960300a072200c03c070382091300745c03180e2140301454010440400180c0c2c504040742e0303000c100c00d01c5007000c0101c1c00d076417580240102c40c041c42c2558800210709268641180d8500342041c810401c00035a6038841c00c140513140098030004285a2000c3c640b861090202d070031180d0b12250782821039a4280060301d42038415402590311649449408900c98240091441c5541c0d018030250000d0155105400c04210000f130354034064402c0e103030b020000c00d0400400742c04440d20b400310050300f03100003041d4511102c82040c281d44201c0100d4011480003990082100f113500c201c81d001083d050030184190540300192417140b804640320f801c0500048002543c10120001074599001408041c3c48a44141842c0c15809018584607a20038040055003548101c04445260b5114100361074108010b10180e01c0c1440921006060b40a6041080240e90607000300b800c400d070041c503003403080c50845c091000c01141841805801030b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 84902087 1250 84900837 84900841
    0xd060332010c05030f0c1306050a08090d02030301060e060409050109060810201b0d02030c0f060108030702010c020312030f070e100905150904090503070501110f0d0507091e0501020607020d08 84
    0x145d204c4d0841c0d03902c01c4c00e2042103803a017500c21800b0884450079030801d1000c00d1001c0340d6031003441d5104860341c1c0d0202d02a001000341980400000e59a40030510604080250114803090b03c1d80300c1030140c074000c24186d0014132131561108903140c0540340900405065115000708440c01150702c0c0144654500c1c0c0d00e20080301040007008004003a4030013080c2d42c0a100e0020700c0e19068020401202c40c071504213a000d9615210b0311141a8285245480b0405599000788010701440002204580c0c43d00d070309080659080031107102007414400c80c41c1580445c0b500100400000c0500d001d8864880da41503610a8141c8058004101103690784080c00800543c81c40018846410500c05c15001100007004407400d10a2000c00101501c0a209088925800101d010010041c090103011883c5040400d91420000007a0807212140132300595040d615840e41c01250146001e042c946020381240d40d010701d4010320042401c103c404191068a005114480024400a10100304414012070540e1090525 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 84903337 1250 84902087 84902101
    0x5030c04140d022709070305030d02130b04030c090b0a150f030f0903020705090a050f070f12020a08041a07020c060304051606020d030b030c150d060332010c0503 71
    0x1840301d05007000e411503450281c640c00341c1da80391344410904000001c6001c2c40c0c00340c0014801c04440c05080d00070b45a005507401e00000700e012040c0c40d07161400400058a13240c8a00030801036805039800818495000117004c8240710a03042c1d44c00c195901184d0510903254604140413800c0160311030b900725058840c40c102400c0c0e02c5030088605607000b03807401180881c560000d083c12a850900114056400a0340800c85428040c4032158409000700007000945020755000c48845001070200e0f0800941d0049880700c24002d10a195020500e01d90842d100c6228400103020007100b90f4068407a150740d08020150f40d20556100303481040f455014110646183c0f05116154102038011907030b50180305031220480849503c41c000409295000b4403c641d020380c4050200c030280070409000c1c1d004206c00194070f8641c80e406c4151581d10700d4401d5654541002218010841900001e105050711000d011510903003103007800d4440350501c5d4034910300d00809081c500301c2c3c4102d06400080341c81400000d101d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 84904587 1250 84903337 84903359
    0x140d020f0915061314040203040b0c1e030a02030712060803090607150509010203100e07080601110c12030c0709090b010b09030304090f060e07081e2205100c05030c04 73
    0x30020b4403400c1420001c500c0002907441e04107010200d1040340f801010440494000d91094904a0641707045146d410640c560b82d6004030b0007051400e8801e00021081043c0141a6008440001c7d54580c15102e0800c009098080d504c107441e560f00049149080c11521480e034420402201c0c1600011440c2c070420905020158019190980b40c006540000080000b55801040e2003440e0070800141c0e07910300301c80c00612081e0260054074000c0e0000e002c01c4032040d000440c035500300c0c209080c01c0b130f03500d1781b88201306142501c88802c090308400e2042e00303020754520020180c44029402c5056845864131211707110212515008050800349004e801000075600c1c01000302242100602038a01d01922020840159902c0c0751040005c3c6a58080030411006514949904680d15283c0303040300d801c2c280d4072070401c0c89a07801d00d64045400780000c142203800503510102c241d06451403100b14494613090103929004803010854140b428400c2a03041c662007036040740d21407400e10f194141824108400918 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 84905837 1250 84904587 84904591
    0x302150c0d1206090504050604032d03021b0d08160e011d040204120b09070501030c05090111160305060a05070f0c030c03030605090c03180c010c0b0c041707140d020f09 74
    0x55050f0b03039140b02003000000c5000c0c40307202d280208000c0401c0d050034500204908000d90401c60a21030031038040b00403c0d1000890740c80313503403035141c0540c0381c0311802c405011020341c04a58405e54170911f91501405904012454401d010344003c80c4034040f80c8103026201c5200403540c540c0041c0c80d01620802d150041030404402c4000608010306141d26065100c0c04c80a400320141c0d030030360007003040242210302009410f000d88028601072110180c514409000e502a00c0d086038140305036a015208803100810a1403026008001507940780340d5a4205107840e101c090b150f0314405403c20002400560082c1c842a0f111203191f514920403191580701110924046c0b80c003203040507246d200c000346d00c0c4d580000d158054103104003260b0781d070704082130100b801009005408025401004000540ba0782080c440c2c4011a04103140341c20a95078a00852086c0c42940c2024602010307800c60329003d007030001103403401c3d55a49020300440403038880030800140c400c1c01000390320a40c4546401414280310300d02d95 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 84907087 1250 84905837 84905867
    0x501031202061f030b100f0e180d12020c1c03020d0501121703070504080304060905011805090a090519080a2a110102030c10020306012607050307021e06010302150c0d 73
    0x1b117040d0b20b038892038211810641c800261014540107200c03070f4600d81084401c2e040c0b00300d0010900c0c410041c1014003061040b068002c1c4403507010440c0d50209809001c0c02c1c081c0b0040c1400f403000102c0d07220000c1e000f9000080c0d00c241080c030b05000480c0303045880b8060005a80c01154902032448402200d09240c0c1c030040a40302002814400014501000c1020700040c0442c0c1d141c03001c4480c2483d0005140030701e0501c0f0b14074519502ea404001d09e0b01ca00c036105400001c40c500106505d20941003d03803a0580340c284007001c84c0c0078000c105c014003a40c50060503642806540c2d0b010850030607800c0d00b500c00d4600019500605052241c4c5000440c11019902108030600581e4103140d09104e80328103001084110f41d000c2a00081000f401d580d0101c000742c0401410482a0031011302480d0700d403501d180c02000f440611800002280a890081000c0c0100b03090201c8103c08120501885c161200021b210407400b0303425401d0302030059000d180940c7e0401400d94028000f6000554040314151300c03100a103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 84908337 1250 84907087 84907111
    0x304030611040305070608070f0201050f01150c0c0e06030105160215040201031e0c080115020705060a0201140901060f09090201020a230f070e0903090307060810090501031202061f030b 81
    0xd07400c0c17080740c008007441d880b849054900020702400f00585050b0610869241a08000c01c1d070f0200864281902e0714078100b800e14015142040c3c591040c41500900858038512002419800d4440c1c0d462090340250000d00050312400303225500e860302200030201607013100c500680c40d503c0d48540b140d0b000b4014940490001c41298224810b0354450224601a9807607652802449400c403500500524522407c03650084004000945440c81c60099070b02c500c20000f81c0c00e141c01d2003500001007105840c500064603040c0300040a000740000e00c01d1000d070400000c2d0003d504440c61040c81c00f4680c041c0c01402d07100c151a500c200c00000c1e00d44161180c100b62002132415000300304200508058110001c000032401c00b014510400c000604459080d841008141c5503070700c022804204072100c0e41040d0182d500c0740401044807104a030059600315140200000500121046c018040003480e02580c1a07502d84401d4100c0c0b102402d400700000703103071f040c40402c0003a070000c19848d0300164503c50 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 84909587 1250 84908337 84908339
    0x21e0a0504030b0c040e0c030f070206010b0d021804060b070c0801020f1801020f06070e030712020607031d13050f06090912090f0603070908060703090507141908011d01060305030403061104 83
    0x42006d810400f582c1c511035080002c020007082035407200d82c42d0b0708260140014501e030740c58a20b0882540c030072024030201e9030341c0100d0010599026460010440400108140001a250781814825420810041e14400481c4034001620b550600c02c580001c19051400340c078010994802003520b185540c02d160461060307008103256043c1c14405e140c007032580b9940303070b410554a100815283c22007c0d04241c410701c041e46600300050343e400003290205076150030110401c0d2242e0010300125046401d109410550100d03040c281c80103203903c081d100e0380003010050510380f5100e05201042b88203d802038000d0780030915031100040c0e20b4000e44050031008241c800840b0300c40d0701092060b04151195400f1902c0710505101c444400d10a641e4449001d1030b0410900025458060361000d0500c52a14022041e51942019407201d2502c90201d0b00d000c0a1041a503070b582c500c0600070108103c44100d1007203941c40a040c582c8041c0a204101e84e0080c0041d0300341400e40c0c4402c40102068101c280d540c10007004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 84910837 1250 84909587 84909599
    0x30807050c031b0f060301050306070f110303090601030b22080904020f0711032b1d09150f06091e0d020d0804030201021506011b02060c0709021e0a0504030b0c04 71
    0x204540f04807051850410f07114822051000c4c41000c100c815105900a000502080e00c0024035240d006840b40381244d0b04060008040e94103083d1030001c2c403500d000c0002008a0245c002800b103040b00c1c8242069101071f590408520900d9000079100a0301c608904001e00104e02c1c40c1002c0d1409403001400103142001007002a05c050b40030010172071f19680c1a1103454014541442811001c6080e030745180c0d030382820a81541c440404902414051109900001240802c0c0ca80f8034046020043c0106c0400d00309140c0c04000000c0c001920361007000007460030ba450b8180f42c7c1c20744020a078090304c0903034690781c01c10108100042c488145e030b4008525040c0000075903100c8080c45002c5016441e01640c85046000080c10450324010a8030b00303031031034400d1250f6664001d10f031644050703110b18401a924010320000d000c5115081300c0480c2d501c6003060225140035150f0017441c11103440c0541703511413644003034000c075240110000200402c60038130081021070a00f610035a03029000801c09071074207071141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 84912087 1250 84910837 84910843
    0x9241b0c031906050a0603080d0c0e0d0f140f3708040e0606030c0a080a0b0402030a0c1101090c170a06020406080114030606092202030a050607021203010807030807050c03 75
    0x4800e00044444260b58035041c081284503041c0c00081800c0144541401c64803500c84130720803c010500302d5692880d0b81070000d071003298424680800104a201a0340160400d510a60305034003040e940d0880031006481c00c400c00150303000311900d0240180100c1c2d03440b1069003000900c40b04000401c05400c141e12400b0303403801c05102e403c40b07104145c026121820304664580c1940000c2085002d078004005018000c4081400d60345500041e20380b040441da01c44954401800310790a0441c0c0050011052100c0815180c006004240082e80d51240141501d004c5030300341c910b48075003e41070540c244001d0080c0000890805c58550200d0708541c4035035440d41c1c03204126841540b2602c0080d00050050048103040080c8001c580d004800030221811f10000203200514041c050007814070703240011404800304441d4541403e03800406071040070400b810010380b00c0d48210350010041c01390700c6480d911482a0401c2c0c90503207480000602c00c49065994050031540190b605607540d22030000a114165010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 84913337 1250 84912087 84912103
    0x20918070b0f040e0c041d0910090803090c030a0c060311040f1d070302090f04050604060b161101020607020a02010f0c150b10030c050d18050a030509241b0c03 70
    0x8502c100303a40342d140c402c0c0c0501c0d510010341a0303101120200020001c0080e80030200044005401303002c110380d02d0320304210340792400200144110f641828000002d22002d400a54890901c080684001540c035804041d01c8129165005068481305c00040c030040703100380c4c0100d04502d4841e1600d443c240d140c103810034127a0040e40c0480b0302c0740d240e03106500c10401c07201c000a0b08100d050031b007541050040c40000c3c0034004032291087c059a0f40c2c02c00160240d8454000000400c111003c2e6035440190000710034600788040004d4800000e120000c2025504c00500c05206550726070180107000099401140d01c0350100014508106d240d032005400310b0041c1e00100c3c03152207841c0e00016000001d0040c404000c10070006101031600d40441e072402140c2041c100d40b00e400043c4000030308922a00d81480300000c0c81c0502611611030350030b08100f00740e0021b00500d5410340c00c6a100c5082246900703654681101e017107684615038810301c0300130340401710031141a01d03d01d121030a85170066408404a03240c9259 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 84914587 1250 84913337 84913357
    0x1507080403050d14030a0b01030f060605040f05060301050901030605040f02060d090c2903060a0b041806050316060f030b1207030201030e03090907050706140a06030510050103020918070b 82
    0x201042001420020103a50403143c1c04c0920103c0400b006001060200503c05480c107520351000c01301a0b880f942c80554403c0000c40704200c0740c2e4854000400755081070098282d00041d800002c0341e03900d040010359040311802411304074180c4c05c5589407006801c024100b20b48014980040c6001030f80d0f444041d017494845900c0001d40a0701034104806117840c168000410303070151540103101154004c9804492640040f1607c0e2760ba105d00d030108001c20b0181d400115150404500440c2c205030f9007141c080c0c00c282118081c001d036926001003685814030201d40240419101c4410003080d8062403c1480030002c5040c0020104101c0005c00c081c07809640c101c084642065009004661f05440390703900c1641000b0017141031000d804080b602d8254064010700a04c9004260307801006034542048035850600000c0e401c00f410407503223401c06804240400c4482d0b000302068400c8c2c840c624440d00c0c0c101d82d001801d54940751940c900c2c1d41c2c4a4030014544000c14040c45201142e612400310082ca46411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 84915837 1250 84914587 84914603
    0x120203010b0903060a0c09060c020a0803030c09030d03020c0c210a06050105030d0201020c0d08100305030a05030a06080c1e0d0209010b071406070206010603020d060e070c0308060604050603151507 86
    0x102c0400309410020010103003813007a89050082074006500a010800740d59845c00e108030000c840c0e0000564001065100c0f4040b071100000304010159281d000d030092200035000c6a581c5401240240c0c00c0c1e020f02c10700040550b00c0380309800382c141707410a0810006806180d404c8104031403910740c90300b46512840e081e558141c03158010080c5003000c10850389c0c004551710003181400c105406091310785034030300a41020410514003050060fa800d007100c2000756070001c00c0320f90710121381c0c9014109030411152201203929148000810840c04184c071200448020038102030302c80560400e0094039210a502c0e900718404a01001c016202c0c0c0ca161806020020103407a11040c141c600b00307040898140100e03003144c00800a012295800044250642d2890b007400740e00c0b200d1405401c001800190300040e1941c078000c003030012031078004e5000d031030325402555070101c0da03038500c1c0a114140c4190710038103400071001c000007034004429850400034100000c02524030f141400c02034003003542054030191803a038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 84917087 1250 84915837 84915847
    0x1090b0f060a140603041403040806060f0607030806210703061e0b030304030605060d0b0408090a08010c0f1b0503030420041a0d030c121106011a0f0703120203010b 72
    0xc000c201441e404181101c40ca200707182050f00d0701d0b48603001d850f0160b001e184048003013010030000c406212540e0340c000c81283d4503a0342c0d4244090b601e000590700c150003207400c01008440b504003030044070720254050310341d045543c50301d006200283d0040c8001000340c3d1040e40b150310002e841840560002d501460020584940704400d80c1510880c2c3d620b550645e626298484010b5100441a20100c1307403c15130009196544c180030405801d800e140041130288454104020031001c68041c084c40101a035201e0328158031003e81a00301e0710041032070400702e0080ea414a0f92148910003070204002c1e400900c0440341030560b1903c0c07071900180c60442d00d494048010030880400151300300c201440c2200c0238411003101c641848a07202220000350f016025604590041c54080d441c00c1e8030303041c1d000a0f2540080c0c10110003e280740311309035680c600c80c0500800000e021510100760603145140c482c00d00d10705042104240356551000408600b0711a1908a000c14072900744040d50003424210360003030341c134 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 84918337 1250 84917087 84917101
    0x41503060503031813060905070908010f0525050705010c0207061d06030c0c03130303260f2710090201091211040c0909020d0605030d0c03080a020f090301090b 70
    0x40c80319500841e0080e403051226405541610312268059401910303c030191024104152002c0d000d00d4008550050411040c80860343d0300c902d4007421110f054000304511a45200f10905807142900c0d88240710b911590003503002c00380201c1030001c00c100350421500d03159031552250701390790380030143c0805030700f0081c07040042c0707904222101010b450f000d0040012042800000e0902d00001e40080e654280111703581503004400c004498000c0407004000300c4945e9a407500a001070b907100d2038142c141000120b07214002d070300c00030518094802c203031443c2c40c1c654a41c4421440304050010324407225886c01c80300c20100e0b234203000700140f0340d0003907030003048044080c000941a0b442590082c04210ba44541c2c10000c550381642f05090400c01311400301d40c0003c1d40d2800c89842030a9004007650302e100007889426074a0307690040044403010781c20348060010302202130303070050f0010a01801040f1007000041e00e042c40c82e4010f0902c41c00c1d02c2202410b0940758070100c1c0c2102c0e0301441c12100c11403607109116417 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 84919587 1250 84918337 84918341
    0x1c020a03260a050a05031306050423011521021203070507060801050105091003060b0406050c0f0c0603070804030903080703020303070201050f13060e0727050609060607022103041503 80
    0x11450100078010715001c0d261800400034802c0070080400c210010000c244c0603201607540e041c030590014014015403c00f800c0844c100c2195581118010101288401e10b035203047c06111100600804260040c515017044180d0300d01d01191808000481c55500c000141d848c034030504200c1020030700458540000307207005850309040d904502c2c00e00a10200400550fa030090031036040c0e240036100c03031070400146001600039060075084185c20f00780106000c98803a9128001d011584904400c032061200349900f0140c646070300b0711086401c400c0400000306020b024044494110780309103020405507a490310741141c1030700702ca101100140c10000c01d220000d6424003525810210f40e07107003800242480c00000c800e008500c00020001911264800601c280c1409a00001d00d40441043c039106401d80031512141008054072444502d8040410828184101e050b41f10302009441c0c00d2500b680c40c3c080082d0416442c0e5005220650040c15461501e000e2003e04010300c0d0031280e05c1c000604040001d02 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 84920837 1250 84919587 84919643
    0x10606050a08070810030f060e011e061203080402011d0a060806040e0f070515040e01060f0206090a0c030b040204021b0105161110150909050307030e011d1c020a03 72
    0x30850804c06204880c2c1090303481d501240e0b0f104002c0164240e0500c6c1400141c50001c050a11552a00008804c4640781d01915422164415810080742e516030000c05414208044054001170903440041c0042d406125050340d81c50360501f880100b4105840002c8803501c0c0c1e41c126a0010f6400010b2181d181858090503485128071030280040d20440103540c0d0740c2c3c4007030348125880f17615a01c000120f01c1c2580022035020301a00304000c5102c2da1100d03805040300440301d960000500c01e01000030410480401c83c0140980d2019082d480d043c40c584584140d401e02070700690780710740e0812102004004c3c600348180c500d02c400c6c00102d070501d4403c1d007105000420458850602c002c540c149040700304080390842a0200c0204001001d61100091290000043e0001480c4d2071030b02d9610414407400101412820740309990f9a104081c090f0b004540800d0700082030034042400c8092a00c42d071030040085440d61480526512050b82c0c03d4000a0301d14565074001c5c0c07010031550319041300d0301904170800d003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 84922087 1250 84920837 84920851
    0xf120703110316031b0c12050f06010e1605091c120e03030f0304060b060c010f050109060b070b040303150e0402100c120e010519030f0b011b0204020d020408010606050a08 75
    0x941080e2004030b8030075144603070703010050402c0003000000c5200a02d5002c81c400c001d0b01b0800540030213884400e1400c00d8060785400f5100ca1041401030030300000c002483d00e05075004d40c4200c041c942c0f0b401a1001c42d21494030101424800c00707104400080d100c0f0004004028103501404c0d41101c4203003445081400070f114817200300282040300c0409900c00004031111440d0501110340e5940d00c5013800030051510040341e42e4070042c00580b80c2e00300d0005401250641c5e02d4880100a2660380303000c51411241c0c0740c410b20340208400e020041c081038030403003641c0c0e2050180c107020920f02800262900d002c04141c020100042403d010300c000d5040801200f4640c0d1154109107002c100389881c0d1401a4281e5050032040051151100195034402e00641e40b20f5800780804504204640300050041c200c102d0081040b0761400708804050340c0324800c048103404c803800441105840680911000c4e51003801d40398403da40801c40050700ca4024400c10000704034503903c4540312202054001e180e240f000d0581c07 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 84923337 1250 84922087 84922093
    0x6031a042f06091503090f06010608010e040602031f0b0a03060b0f030402130f0903030c02010b011404090b04060308131e0b0904020d09060615020f1c080601020f12070311 75
    0x309a03034000a10928007070380ca08031041620b82001c180002c200c0ca50490a1101c140c90200500406000019102210034076407400d65400d0713a201c01c0111041c0703200340308098820384080040b50106185a004580005054032500c120700480d2507488161a003552002c848020300080c0007000d6a81445800c01428400480c07034504050010740c15010f0202402c064410328480b252810b588036168005550045003c409024141c8a420302038010300ca0064880c0165080c014404160761041d2410401c003006a1074060800c0e04000b0018000c24018161381d030040e44e19030f00400850b12010261400c902c2c12420300601600b00803040c412607006101c0c0811040d20180103110307903403c4500751007840b4000d460050301c81c103229240d0400780182110180189192010201c0d820f580c01d4140c080d20b81d0150200d425101c4001c1400d0f54800e90a60070f40c0c980000d040310300e80c015200f25034494001505204954041243d48540343c180444402d80044c034100c00030340c090030160000031084d0303212000070103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 84924587 1250 84923337 84923393
    0x8090424090e030c0105040605150f0d060c020a08030c03070e030a120503040c090e06010e070f08060d020607021f030b060c03032a07080405132d06031a04 68
    0xc00c0c08201041c010350444688a032940c2c01881010002d03030b542c0c0c1d20400000e01090170710b42003030f5000300403d81d000c2c00212030320325503000c144c01d03d40e1881c840400c020b069982d4a10050715244001d011a8484008501441c03403490045403071b00000d14003c000214100d55a42010710000d030400d025a48200d0180e00032100c42d10201c1c1000041c80015282d5042c038540d02c0d40e5924081003500001c3d0000409585058a01401110001003032816560401e4504a440d1a811800da03401e184500a92002a0f80030780000c413581010b0302c46800142c400f808440c1030109550014144138410500d018151100d80040755400e076144c0036480303e2010950710146890361215401780c60b0320001305904180000301060459012440c0c1810745000001ca403500c0d01e40c440c034980103445601a00c82d4a21030001c84505c440e10007103603c10f0200c6200c03060105a4140d8000042124089040510b00402652003200101080d070111451220204556070410302e0318092520101c0b030b0071020601d041c107a8401380 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 84925837 1250 84924587 84924641
    0x8090f090f04080d020d020301080c0112050c07021e040e060405070b09060301170705040e07030308010f0e010510050d0501091e110307030b0a030203030705010605120109020105030f180109080904 86
    0x81254002d60001900d60344d6103e4140031502a2017401d1110382035610003c0005090000030401c040441000d0f40c40742c0c0700d4002010b4880a65000b50f401900864080040707100500e05041c0040750842900e1400303a0481541d400501160f140800498180d00b080080000704041400028080e01c0943d40740e0341040703203400128500340014091242403220600d080000908204201c000620b0001d0050050b04448070b01c2d5a1501004d00c0b084010480790340000c0390f0381c0e0b00b004280e0181c0f808a001c0700c110f13a18010420100c414240442c0e4240041000310f100c1040c954018107000e0a82c0c6c000c0400e0382d074910300c1c0050100c00e54111155040c0d1918003101d02010400b01101d0708504e5910303011a040302c0b01c2000401032041584003d50505c03001519104005044d00b00b1800c450044400502c0d11002071100c40c240c1b41102d40c0207000031030400000d0044c00300141800d030807000c0b449030f4086045490b0601ca00b107820111007503e00c0310010a90146514050140044c101d031700039070f05516041c00781 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 84927087 1250 84925837 84925861
    0x2708121e0402090915090706020f07080a0f0320011a011106010303080603072402120c1c090b070501050912070c140105070c0e150f09130c090908090f09 67
    0x703000203100e210a0408222030103410010340a21041c100045429410800b010300c0da2004a881404098006c48182421100000ca85001101c005d80098a80f8200c91f0b074440a1544030401c0443c144116606100080c0c4641c41c1c170015145039002c000250107041c480703c49119004204c925041100751100081000b0000ca84c40b0b04580d494140141c442c1c5494001074140152034108020305c03552105580082c043c0320880ca01080190307002d41d6a4524502130b088814421001c040811f9800220000c4c0420040130130001c008040780303040c8802a850310450081d65104400981c0c05a46843c01e0000112040c40b02450f580030305c034440b0b0328002096880d81c8107a440b074880c0144500810745500c0069002c0c40444894a610009842103940c072100b9641c49680103480d110a460b4030a46007824505002030040071030f12000380701c01001d40d0342005601d036124803070800b03c600c1405480c0c00502c0c8d104600500d40140d200b9107101d91220a4a02400a90394007a5100c5100d110110180b2048070900 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 84928337 1250 84927087 84927091
    0x9110402070218070e13050105190317090402090a09050f070809191118180307230a050f010f151208030915070e01030507080601080106032708121e 65
    0xd21010400d513030311001c091350f40010790a801c5401c55010028902d424103154012030603a002103400c000e0f4403200c0c0301d8070818820280002000b814121000812509070203002e4450050001d10241c5030440802c0402e44040840c2d100a800316107a000303000120030100f41380fa92181c00c500c0c204a0a00d810b0115640e60a0195443c001103011014400d0500205200d214109240a01211140100c02c00030501004007100c504842483e03040b1000b10001000c000c4481c01600300c4070740d54500f20b541c0d2030700270000c45605c2c41071920300c1515028000034005001000340c81e1900d40000907150b80305540390b01565054030707160404600050b000e000d0b840045580454585e0068900c41c2c8903a00c95002620b0511410300004c9081018010011159845000944200000c0c0e80501558845000680355400701341c8109001c074844c800140145442070340949001c2029100e180d03907446e40e09040144890200c2030694501c0d60009036000c0011880904903000381c48402d0b4110b0904d409596003030001c0b80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 84929587 1250 84928337 84928369
    0x30406030c0905090412020f1b0103110c01060b090a050109030b010b0703050d0e0321070e010807030204090513030912050703030e04020702040c030c0e0102012705011d01091104020702 81
    0x5202803018280c0c0c8120442805000702404c00c019505050402164030101c0f014120010311407220164103215002c40c03001000d08182444a000d480080019000b501020b000c80a03c1c04043c4846c0e00100c0c1c00740100401815416415655000c0700e80c240b041209058104e9414803405507010400120b4103e40141100d400101c600c2d02d421a903d03007144d01d48901d117084803186040102c02503149002100802040c042804084000d0300e8100401104071002c444410200c0d0b5210415043d5500695546520188900d4014501511344110500301c6009070398402c1440c69043c2900201504040828098106404884081c0007544c0da00c658400050200804200030303000c9140132034072960161891a030303005005005401c60044010000c100481c24540040c070042d41e000003550040c807034810322454a580d88038100300c0c4150700a01c915000a001c0350f4641d0b0f13521210114208121060071003030b001d4400868100a00d0910040904a401c4810302c900e00c108103002c0140d403240241c0840e424 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 84930837 1250 84929587 84929591
    0x30c10080a0509070b0d020a0e0409050c040f0e0f0610050901230609100509090c0c0d08060a0503060403050c06010e07050403030c11060d0b090a110913180303050103060b01020105070203040603 85
    0x1850b24200c0c0e04052181d0f00c5011702074408910340c4070015203500030f0800c0791800d5480e108115031500400007600c02191010304150061944100942000d80054410b91743c001800f040d01c10442d00c1451800c68109610206034020303a0a11106440402d6080000c0c041114440119410921107102c0c800c40601c0d08020f1103200503007000710341c440d0310030b0340c941f01d80c0103003203042500c5040c4000e0682d91108000900c81c1c0700c040000745090f02e085080d500c0c49840000208895a000202500c8051005e0700c260707030000080c2d000046650b400c0001c5407041c0c0c0b080c0c2d82d02d82c031884520030b01441c080040c4c01201c4411050003c1190450b4050240c0e002ca94241c5400c403001011800e2050002072400841d980124000440340100c000c180c208000175041a2280c00b025560f0900300030407190726420721580c2100400600880c2c1c0b502110488080000a40002e50070800c4040a9075440344940c0440c04a41c55000400038424144103121a2440030300003800709150554000b500d0340300b039010f00c0b01496 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 84932087 1250 84930837 84930841
    0x150a1e1119020a0b070f110a0b13030e1e09091b151b03040f060804020a0501030e0f0102070b180d230f040b0c06100f090b0d0506040b0402030c10080a05 67
    0x24401c00c11142041d40110501d002d500307004600816803131b4000b1002000c1064a0240021a10001288410140c001c11110f007140c440f0111511500c076014010b40c00c0020301489480c00341c1d01e05071100e101101800c0d90840300c400c03490038030007039001c0280308800300e400c48841101e10303060156080303441c10f00132284662003c100000c5403919004182c82508144440d8140c40401c00c0700200400507070b00100481d00b000743d07484500701d80410003205e00a4000007294401c00965002c1d03040908044203801c1940c141c11000e01c84c8a089800010b0292882e4888100307200440040a03030080e001c6083d180605082c48002c2400350096811000c00c41080d0380e64005a4a0b00c13040f0000d4691804101068660329a03580d007040700e640d0005881c0ba4210302a00020594400d503d1034941c0466503180342d101103061030040c224006010513801550415002c151080000b1070501c0b1182c402ca100e402c200300d0743c0c1054014076182c00c01d840207190080342c071050441000d0780c03c03882d442e500540100002c6810303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 84933337 1250 84932087 84932137
    0x703050d050a15090207080904020d0b1507020a0902041d06061e2106030d03020f190c050705030c010219021c0f03030e01090c0306020c150a1e11 64
    0x9205440203002280d250000b8010140c20382d8008044408010310240c80b001e8607030303440500328450010020704a20007000300349141d0070079802501e40c50102c184005803000c0190040350800030625102d0003114400546201103260084480d0060710a042c0d00318240750070510240000d4208800203000f511085d400102d860307844504460f0b1202d01c003131801c1d1104c06801c0d0010001d40000d0003000300d00701c09207401c41c104c140c0d10402903c40e510040041c01d441060423000d400a502c40040300c0000c4030308120300310681600b8079502070201243c0e51140d007401c40900f012418071240342c2106100303400ca011000a82d030b9000030207001110250400801030740b402e100141c0d44404e05070005503c00c0740603542c001400136440d0016442c03406030b241840100e2082400030f08a541001d001460300c054620140049000c507809441c9508990741112144c0025001036407005e1411a401103140d80c030b078a00c014810054590000c141c0e991004140222800c3c00c1d000219405000e0500e0b1072641c01540e04000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 84934587 1250 84933337 84933347
    0x30d44062115060603060108010302120a060606092120040603060f02070b0708090703080309160314011113150207090f050f0705070f08030a060b0f030402010807230703 74
    0x300c070201003103100c214011010710744400c00840d84008008000c070000700c82d401d207002160701c40c000c1655203059680c00e42d400c00c030440110701220480c3d841504142800130b03205104410181c040c80c0c4030210b9042c54141c119031042541800300d941d140c0c40c00d03100b1001803182400000d80c116039610105105844c440403c00030304080c4d2024120506000d022001140d0035401440594025080c1078581d0303903548000e981604060b95010320740c1c0d01040c0304101040070b42000c0d580000c00c6030182d540d0034905014280440a40d60002d5070604030307271014101c01c020244100012000c55409080c20604540414803100d0030500c43d030a04514151900030b003c2d4800c0c0f2522001e005e01d81410050f828000e520701c03004001c1100e0506052040d4170118850038003803002d0b103510743c3e0f112440e483c40c400c4554521541786c1016048214803a00d9905c0403c6105105000e40b50190801450680780d15050000400e9440c0103403060040c0601e940da02c03030201e00f200c22003207001038441c091595604030324030f01125 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 84935837 1250 84934587 84934609
    0x1110102070803040f03030605060a020607080403030e160f090b0303040b0f040506040f05040b010e03100e12040305030c0105160909020a0c0206070b07120203070903061505030d4406 80
    0x4601e42c00001080100600c3c215503031180d600941d0f0411a854442062043d14407404034800301603401000000c003c60b01c501c07061a4070030b1092401081040006008031b1400310301c074040c00c2001d0140d050620909000007000c000403e14041d0500140c4d03000701c00310341c4a10a9000703060842100060403010744003c2001c860090034040c244a41e15079443c4031030405440c0501489219134100b12164485621440812011030740c002c01078100814070030440c0d0000c142045000c60305000328006103011004203c003600003180558091030380d404c219080142103850043c10028080d03d48010031890b56071000e110815140b510310016075070308000c02e09451038000c2880080d0302070b00000d40441002400d0010900a2143c0d0311000811310b11000c0b60420703800b00301c50f4400020380d442c03c01c00210b030389504558051104012202e440d42c0d1201e010900740300780c1d007030b22202041c001c0d00c5021481ea28100644c569528006820100d000202c040e604c02c41e0001001d15030310307a50000400c0c40d42d0b507031485030a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 84937087 1250 84935837 84935843
    0x12090f0607020a030b09030d0c08010501050f1e0a0315050904030203040b030405030408010c090311010906080a0f140901020306090f070c150b10030c020d03060e010e04080c0610150c110111010207 86
    0x1760702c910f0050030f0340b42d980e40400c40511145051680003074602c0d00801c40d0605a440585825003071201240400f1216001400c0d000030503446200c4180080c4030010060104162554002c103c0e1000c4080400807882d00341c0c8150b000b0704d0140708210101e070b80401a5030541d518129002d5403902c982c00c1c51843d502690308030b46019440c00f01d008560036000101c41d02121b101d0101c0394140c44201c401034440324800e104440c0031501ba840010143c580a40c07082d014600e41c00400141802c0313050010b55420000c81c2c5110450303500005100080c85c04800c8181d02c81108841c81c8560301c1c02c031000410303004100100400c0311654501540c5050f035190000103034400050040902c005154400401a0041300da07048054001d905070519402d2190082c0b5080e20359182908582ea4a8540b60402941e4020710a40e40d01c030090100f03640314941071008c90b00442d100c40d5800750345e5040a41c0c40816819078505070302072024240c180000507240f5504403007081402d00300003100c280d13070b080042d01a1190080007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 84938337 1250 84937087 84937103
    0x206070c0b030717070804031b0b180c0a0614070215030718050d02060715200705100513030309030504050406090f1a0d060203040303090212030306010212090f0607020a03 75
    0x119100340d944015603c601d40e20303035400ba4080e681e40002c4a02c0d14040d10072100090904d000240800c1c0a08950703180e00c1101c1c502146440020f440b4076500ca4401d44540b8889080c0c204109030106003000b070301444076400c0700d44502c2e007031800300e0103030400e004009041c1101c02d0128404041d0b64500044000e0790780401c44043d42d902d0702980040c580e03022043e100c280041b10002c041218144024201081076020700880d10b03050080c1c44002004207046003020303170145c440701c2c06201560080032280e1090030442c0100d0319841185071a905184d4401032011000749000c080101504601c0d90384003001d505410b0010340100340782421203041c407850b005603400c2800d1010010340c0c810075520503002c40600d07080400620007002c0800002d010514210741d801008401c0030404255030781d00564026100c0d040c00544c0706040d03404540e148502c1180070b0816040401005043d5806001510b814a0b107105128604003080340045c410b110000390f41030190368082082400c54403941d030060b010315084541 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 84939587 1250 84938337 84938339
    0x151c030c06060504020a081816061101020f0a110f060c070b060111160305060603030306030d1b0606060302090f090c0406030b040e06040f020a060801081011120705030a0b0303030408030c070206070c 87
    0x805800347d042070324002c05254402d50003141290300414805c040404c103209007400e45261890403211214041c542342d5195608126940c441004072000705151311450b21646907041038040442d04000c41088102d40d00d4000c0c8003040300c50820078041b0303145ca43d40007c03200070944a5100481c1c0b41031142d00da03000301d0304c00c030011030407400c8151150208580c03140e0100d403250b80c0d8480038180c403400140c806640550103000c0d0110843d00840c007405000301d4002049030110902e40340c003002e8840e01e0380460003190b80012400140d0905482a0503004400e98492041d414564041005440340c1e104000c02c0581c0c1c1d0f804000d035543c45400c1005035003480c10031101c45003030a090005101c844201d08a00c140c40c200d13070000d00640100c00f100c1c102e41c800da020340030043c0a04d42181c0606074910350114007850410611100d200504d210901850240e91155180c0ca400241d513011561580320286c4a60300c18401c0100007188001100d51100d070401095841d81074904c003090b05402075010080600700c44c200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 84940837 1250 84939587 84939607
    0x40f02120109050615090d080c0f070b07060c02010903020705040506040908040305070f06021f090f02060c06010509090a021c06020c060a05070305070c120e060f0a030203151c030c0606050402 84
    0x101d54084d660071650742610080c01651200c06108603030410b42c00041701105036000c50030007805003110880e030314150303403001070400502d600744100f540001c0c0c22000040ba0020601c00a4490802c0021060008100d085810748010359030b8800c52240d140b0880d12500000c00d03079100c07078100c5046994000401e544a91f00c1c0d1500907100e007924007071010b444140e44400031308180b0004285000321a00a0040038204251140c84040d1100c0c00342503404400d43e40ca61001a155200100040341001c4040c0c492941002d00301310320100060f28040303180c0d01c400810300c0580e0b100720341151144003014003050092001d10b003060184c010500008094001c01040240d02032143e040305215440031f0f981000304d41d0b69820b046e506101c034401c028001c07440060305c210440e4003440e82c0800302e60004040e1070525008040884055102c510b03028002074011013070012032980c1d010128100718040758040d02d40b92010000fa208501c0d069000b41c204240e402540081c05115032040028010142041d5a1410703404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 84942087 1250 84940837 84940841
    0x60906110d0204050906040903080a020304020a030206070302160e090d1d03070303111216020105070204090602030709050901152f0105043e06070204060f0e100f0b030105040f02120109 81
    0x8441c4d140035034060030010345289030512464a060741c0c15142c80504c0d0703d843c2c00d004002c3d00020422600a0701d004804030160740c0700c0c00903281840c4030303074024210610340c242c4c0c0f1520032008ad8401085140401d040c000e041d4000b2421a502801c6032030458110460398509074040c0c011052a40e826004004000c824558401d85112081c1110812030711602d1640044841a2161020407000681d05a8107400158415030081c92014001000402c802025407a0f003800c0307070301c195845070110b91900d0342003045007031230580180104405100200ca0307141300800a002c0c0441444c03040b45280c072001d5400b10a0390721560042000b60018001c100c940f6162600c045000d500d4a40d200b250308540d403400e42d2800041d0641ca0130300314070035a0341540744401c00c18454181c010490480e4070a459080c00700300e050f2208030500050000f07c0c1044224102841030300c055040e16040480456406501480440071080440b030444a0558000480d000b0b9400c1d5036009014058500b200304a1103400003605514070b03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 84943337 1250 84942087 84942089
    0x21e1c020f0d0504030f0f0201030f1410080604050a0f1a33031203060a08150f061212030c04030803070c020f04020c07030209090111070602190c0f060906110d0204 72
    0x4401210042d0300c2e114030585450080384001000c0c0c41e5607624002c0040d41c4191040000c1d03206040c08a090703404079016406a8000c0502e0b013030180c68100802c0000c502c50b02c4c80400800081c40034000f41d080684500303850b0240c046000c2c2901c02000428010031600002da01c440510741c8a0358008ad040210646440c001030458202c4c0b03440307800314031503005009143d00000c6040d0080c01410f007030307941007039810395504010001584100d8088002039807000c244080b48800317152208011161a00b401d04c0c2011480140601340900d003100b0306580c3da0400080d0f000c0d0f080d0244030200b40c690b501d002e0075550030301c595000103051410100510071500e400c0700c2501c00f010f100311010341c40304112005001c120b0103424841030840d40310f000304202505041d922282c02041e90320011800c00c015a0f0104c1140c0e201360021540350354001b0703aa0401e0300c1500c048240c46050303403501c0c008407030303554651010010044d800501501e0f9103031401010042940d01101921501c12001501c2c0c0c7d606600e150029001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 84944587 1250 84943337 84943363
    0xa05060d06080c0f03030a030c11030a05030118020c030f0304060902101805030f07140f0a1e090b0906100e0a06020d0210060b030711010b060f0306040c03090201021e1c02 75
    0xf640280340d99514201c1c03502d801c010009001181001c513080c10440240c86905003090502644180ca015011414002007100240c6520b520380c0d0f139454210b0761800170030980000079000b8814405544111408421541c0c0b02c7c0d0700494580c0c594940703003000b000074103079040c0c0203612001210207000d03a40d80115007640c110f84d541540041c129074610034140ca400401e401400c0036000010f050120004a078010703599810f0190014001d460300d500031980c0081c468116014400d241034070041403a00d684821030140419140920900101101091780c0301c4000d00003510a400040081300003078450207140120070001801103030800c0c2c1c1c6400103502c030885000f2042c0140200030702c2032184400c42c002ca10444200104691440e0754a05081b5101102014910b41954852304520b08a94480c4d015240e07582100f039100742c4d241460000c0004640e0140008010b242c10300803281e0240c0c1e0046003d0b80e140c012186658100c2c0320403140d060403e02c08070700050300d9000d02491028140d600040026890030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 84945837 1250 84944587 84944593
    0x50403271e030b090c10031e05010605030f010812030105010309030e03010603030908010c0809060402060c030730020f1f150902090a1a0d110c06090a020306060a030317060a05060d0608 81
    0x1343e80395810384400c46081da003600a480c0e2590865594820f5100001e520480740d88642080f4140d8a101c080d20300a1b404480051008001d101d41040f080b0340d224010318a100051005010408644035140414400d840c10b060b514200361041c5070003458601400f900050007044060384916010380600d54034014510903601c0d04210401c242c0c00740c00384038007840c2084018111036071103500300403041e40160750b02100e50000b48102d40020300d510141080d09039903075416076611960400c2c49224029030600c080210351008005580902c0041031503d088507003400c0c248084403522041c100500100507110080085031000020700d41c9040e40540b8000340c0c100d5801c3c454580d1420340ca1104020501006503c074400c100613405100d49501c030b1001d00390030150083c1884500580181041401c64000c0019008407840078210b00c1c003070103425071095040310306154090a58500401e1354403991492210704584c1d00100344150785180710a0010407000304001d9a50207000140405000700f032041140e148 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 84947087 1250 84945837 84945841
    0x3011407031503080706020901021510080c0a240306080f0312010f050a0e041b080a0506090d0c060b06040b070c0e011203080606030402180a06060206010504050403271e030b 76
    0x70340039480d902c01c807078006840b942003d65a4494100952220300c80310305600c600c01c404416801f5030454a4070075440c42e4010420245080c1c4c0050502022405051050220000a001c0907409503007202c1c60300c251803110301d4041c800d80380c282c00618040c0c20079016442550b0901860030b40001c02410f0003402250340003060790366465900b40e0342c200b41c000d8a41c004d1080105001c16610240e595038018016443d0307240401c45105d0494100c0076a400c1030035560450320500040c8181004070f607400140f003000074020400102c0d0b00425800300c0c0c071001401140c036003d941000d0782e01c800c19036014028034909151ba50202c0e06c0c207404d100600d07104154140218a000041c1c0e020321a07000c07020030340c06480342d0030940d48490030070009510080c400c17a846904180c045c00c140e00c031820881d11940c0801000120503040250184c9004070590106214500782001c0100296005074104100a40460302e00002e091300c0d80752400003800e60300144907840f0050076908090001080038411a03006000c81d2140e5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 84948337 1250 84947087 84947111
    0x2040b090a080106080304050108070504030210031b0816050f0c010507030203061903020f061c0509010b030717250b030403090302100203090117090f0105090604030e100f1d0301140703 81
    0xba9000b0f10482880350011f00003044154018503c55600102529125207820788a40c0012840085940350800081d6140c035862860784035032880071030002d160300b00b0034a02c0c50f10740f282e51a46088034000718100007012400d0001000f00409a13890a40c006000344654500f00000038002e42040340c0ca58480e4005002e4403a4203110800c054095036006040c8003e003250700001c2c090280d02c003218a1704107408d4080706280b01c40c0700f41f1030640249550800410300107942c4003050b2a000342034214280094520300c0540750304500041000390520112503540c84030000c88490722005200c2d60008000748400400c0004140d808501407003600d108403492030910300c4100c401c0365031380a0030300040d000caa1241402c0c900d07240440c024035405441202240c601c11644c49038a825110203454440c05a40070900388003c154000014108200f010344400d0701244141fa0001c4c1076400030b039940c0301408180c09004901da4240344a43c4079240c0080e000b03100944041ca0300e4a22480116502400a880c1110174444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 84949587 1250 84948337 84948341
    0xb30010e0312041205031504050c0c060403030c140405030712050c2205010f0e06041508100f0501060c1707020118060c03020f0705061b01020d180501050703020a0504060f0c0602040b090a0801 84
    0x1d01c90b0720007c3c3c0740c05800c01d0144002010080c001400d0103906000500308548100003d0f03214522a680109603a00c220802a080141c9554403002043d01440180044d440005e1070104817070508561185d10480390424504011151180f9a0061440400080f0807442030707100c0584404807440401040c5e03031f40c40700300c506c3c0e44140c0204c40c031842e20032011a90034500b035004a06424500d0100d03015259a800500c0c0c5841074507100300720031a4540030307100302d180c4180c0f0800b8018039031f07400c01d03c0300740780e041c0d8039600c8040411080608400300400c280c030030b5910603281080391010420100820710780320400a030009044403003ca0041c45a04101c41600d0004901e0f00c0845001034055802e0a0701c881c40003944082003001c402d229035003800009070b8031070303540100d0305102c8442c1104680c800340d07406c041e800d540c0002c0c808001d06004210f03110149900200301c07400c449141c81e19603202074070440d00b11949003600c440540f030701e40003180104214004c03500500c1013100884044800d1130b5101030940c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 84950837 1250 84949587 84949591
    0x304060e0f010e0108040c0806090a1b06090b16051e01050603010603110d0503090607030504050a0902070f02061809070e01031413030e031e060a0b30010e031204120503 74
    0x300150144100f04525402070110075001480740d0180d1140e940c42e03031a164030785101100c00003d00e81c0407004640c04d00284422180040e101201200003040c10a04040e280c1d994901c65800682c0002840204030144035101c4e020440e0701605a90b000450301d02d0480380345034803512240c241e502e8080414030b14a01441041c080300e511000c0c5d055485441400c001c114001b008043d10303140410000401341e0b80d160700040c2030540c441d03103c0d075841c1c9052009001c5060b0407074000d2600284104065804203411403044405142c0c1251004c0da41c82403a8848200800c43c0150150401d50310030501444a400002070361240b0300c00e0340d0410021191241c11042e002003690800c03282910700c5010408030f81719500309401c4190142c2101c80009000901c4c6140312180d84a812094125805000040d4150300614642e0b24040f9510602c466681100c40c0300e0a0011428012480c010b0001d6420030400303401c954004941d070826251100e03803a141007015400100c5045070384501c80309008201034000c0c0705581c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 84952087 1250 84950837 84950839
    0x60d020a0603050606040801060b0703090f080a020613030807030804050c0a1a0c0708030c01060801060603110a0e01091d0405011103041e0f0605161e0509130204080a050304060e0f 79
    0x104030145014010307401810060301c000e800100410000c20380810034000d03840101000003102c0d58400031410700404040c4590011903808000341c1d03042044100008907404a160100d5080c4c0d80c0f0340440c8011240d00d9229440180000780c0880c00006154001c1d4495120b00d010f00103550446905100300440300012f4052000e111620510324081000300700040e00d040c030720050480f00d809880b6030b0028a9a0000400c0d64903a03034440c00140305440084c01500010170b103500702401610ba0b10141c4801ca8004c80461504002400b0301c86401c3e0781c0b007882d02c50001c100b000f80039503c0b01c0c20750a4480008404076810741c3c2544c244418825103500a500300c9204079000031001582d40c05501c80001a030302a848207a40c0c0607511140600800d5181c840c06002d038910801c0840e0343c14042c030000d000108440d02c1e070b007051030800c00c1880700c01d0340040480311551400c8680b020100d0440c403050000307002c0c07034118420503c241e084007001c0040000c0204243c881036103034901c8981c855410401d0040b8010061 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 84953337 1250 84952087 84952099
    0x11121306050c0a0203010207080d0c140415090512010c0e060405010c0f0303020c060c0a0206091501090f0207050a0302030405010923010f050702040510061b05030301053c09060d02 79
    0x1002120320078000362a51441000c01c3d100b414200d50000390981e000041c0039965034000181025181800f8030070305070140404d04021a900050a4204138140260312401c610710b510b003907442e00a240b140e078900000c1d01008066005080030104c9450092081c00c80480124030085203081440c9800400e41e421190305a492842440d101e42d1000f61404140e5000c1f01415007d0010380106c2c0024401303207105000302c035800f035290074501200a20b009005058041e040c0c010310240f5110510451095040d80c03070002c0017149046100311844000d10400501030414040d0300d10b00420581d001c40200300703c0394240c1c0d60300340942d150010000850a0810100125000e07541c4001a40d40607503140444510142001400c00c02190085000e0b100300b00d0710000b140520070301c00d000041d042107149441e0008004000c06040341031307036400e83d40c0c030040c002c4a220300809441d1040c028003604080070320210010f40031040e00c1ca2011105404071032629000e12901308900002c2850a24680307001c86140c00070b060b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 84954587 1250 84953337 84953339
    0xc0a12061404020a180b121302090a020306030705060424050310050d020411120106080702121608041203090503060a09111005040816090509030a0801061202120106111213 75
    0xb0000254083c450640521401010ba80f8680000342c1d1000010051480f5581c0c1d40c4140c0c080242c1038000007800c80103000318920314800540c940c00c900a0380200c25850041c0d5944403100080d14240040d4040d950040c0001004248281030403444000d0710100445980c030702940c0c50302036405010498a10259034220b003c100001d19203618501e001030300141c0001902d0040c0c00004070150300520b45032101c440c40c400108500765000064942c000344920151015680c0b0352681800d41c455801c0714004d070715601e5019000e001d100d074101c83c0244042038071502440b03540c6c0f4001e40050723918420b03107103c0d0103004001000f4600034004c40c0001c551048820300107518580401141012000b211030401c103042c080480d2500c400c01250030200002c1c40203a0388980b910b07202d0000e4620007006044079030028081050903982150106065a1043c14495160b261402131035000703006030081090008409000016000d030851544940d4070083c034180d4000781020040134081e4400c00d01b50f09549041c20b24 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 84955837 1250 84954587 84954589
    0x601030b091b0d06170709062615090a05070522050a0609020406020a0506180a170705030424020a0803060d1a0702030307120e1b010c0204050c0a120614 67
    0x20b400c80c045034446401c60f0400c44060020000c031403440d00300a070910108004005281010032000c3d0081c01d40c000c085c41340710b05010f01c40c105a14030f00c455000d2110544641040e11805219505908a40c18112030072032501c0b041c001c1d91000e0710b41043c1e641c0d0080c0ba501282c1c504140c030500120440754540c0d4411a58804140b5004050003800300d2052a0ba0b00c41c0402c5c1180301c0c2c00244010855540200f48000c0d850034610306116004d442c000c1e50148040d42000502c10110300003000d26002800304002010b282020f0205204010b0018000c1c0000103002c1280700641c00140c0754184080d84000603e00741d00c10030399980322651406400c0030030a10004402d854140c0ea0715a81c28460f05a06800c86241c0f41d111910b40700c242c56000c00360f0004410445a19841260744003021031080b01485130030115840e064480c0301c0402980e030080203400c1c1102c8564010182d41c1549603000d07200300258a0008a94501c0790400c0c0000700015000590207001090705005440c00d96014003010030343d52480700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 84957087 1250 84955837 84955861
    0xa0906062a020d060c020c030303060a06051606150321200c0303030c0a030b0618040b040209031506040e1501120c1d07020d0c050307030810170309090601030b09 71
    0x400d2041c100c6428001c103500580707500f201121042e2294401244441a141e0040e081c07912481025000c3d510a00800c444c80d0307280310740d420407039441d030403c99035956034250960301011803e0000380c00c903814801198152101001440101d90041c2802c0d0f280482c40401c4e041e0301c01d16640041e00250050f005034901944142c2d80841842d07030300044071005003444000c00d0a54000b02c503400200c2c0408103014103500c0d01070181c0e40c1e080400701e904d00e02e8040003203821994a40e948550701c0c050b594482c1d54a40ba40c6603541105c1c25071000404580d180c1c80210041c0660580c111522400303241011068554054005480580080071030a02c015170380c2800e03038601c100c0711082d03000e440035074180100040d0209003d0080083c000c45051040d010f1405071000b92a000c0e24180b13141c20001d82403285c902040c00842030f680e442d41e152410070080e4464681200180c95103400500242d000004081030541c0004003d00c04a02c0a64a111980c1e4900005508440f0b169414503000f0219500240c0400307100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 84958337 1250 84957087 84957137
    0x150e04060b040b030a080306040e06010302030706050a0201330501050c1207020316080604170a05030106030903140406021018031b030302120f04051b0609010f1704110a090606 77
    0x70b0400070341d144000000034a000120303182504d1811000003404202e080c00e018500060710050004c010317a51543d408280d84a80601c122020823070082118070085100790400300e182d0068004400304a2814000181d201c080411509140b10102c00002010b502605c140d851068465000d0401800800c441c00c0e140d40c8990012603050151410b00b00411468801d840050500d6200070300c0c00d0728140ca0440c29080b414230245070641c0341440301182c00b90b0f210040340e042d01d600346008525400070785000d4a24081005480001d64004900071400c1e0303074001004014505600700c01d1003009100c40355404000303a41800034000402daa22903040c095204081058114801d240051034040412000c080140060b00d02d5018003071050f0900050007810400409540d0b85003483c1803039150240700144c010322809007002e050104150030001d0982c0109161045141101400841303490035145c40075080403d812054032404800c1c0700031504031000c0c403512054403ea03842c0c003000b20381e15203070300360a02c001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 84959587 1250 84958337 84958339
    0x140105070507030215120a0203060d060e031603021c0309080d110c06010605120708071d04020d0e03041d0c04050f0a050301090605100614040e0403031503080c01150e04060b 76
    0x241110000068030b866082c517015908007200107889082d00102c4506604024201e028100c0c014828040c3c2da0741e5440c4442c080c540e112100094075548084500c3c1507004040c2205030441a64010009164022981802200d1a13030380d0304103c403c0e0f0b00c03400e5089518481303000d00005000c1c0303c4802c10003442e51005a640256004032820200484400742c07400d03400360401c030000784010458009948054107815003206140c18103802e10301d00701c1c03401070401444003074594204440c40d18000450700d8542c102e801403100040240018800c00a8440c1d80f5880ba1148024402c1c815100c4200b01035520000c0d40a094a250154a00762806082003441c0000c0d03403401f80e0108c0d103c800020301d580c003403141a9905128000103d0035240c281c14540340c1c01d101d64014424400801341030f120aa80e40f008603000d0703600e020803410b4a03441c4c41c202100145162509203102c8081d820f8040207000041c405031102020b400000c0c403904680385240c41c841e16452261343e1160030711a0100e4000760030b40c0c00104074082c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 84960837 1250 84959587 84959593
    0xb0403080c0309100201140703050c0d051f080a0b0f0403090e090312040b040309090605010e1207050d0803010312051206040b01030b04020a050405030105090111071506050a030803010914011401050705 88
    0xf100c03100058034040c0c0c402c80704000d40e64030304181c040c0e40062070503c0e5020045042c00c00461070a4481000740784101b41c0c4441400356200c0000c1d071664405043c140514400541c600d5445440d0180079548111645040d10b00300098000580c15100d801f203080d101e90345c940d4410580c680f500c410700504038405003408049000500a1202034003d082120340303e2401500d0b13107646800c1904028014030b096411001e0801d040c1300061000781d03001055500200c001ba10494407032140410709501300100342d044594000401e120700d800317001c940700186043c7c82c0910810b5402c1504d0a5080c1d5a4ec401c90820015141030000003030b08038500f6500c2524080c4040c140880c04008a40000301280e010005403004a60046020300c6682400d00c0f50617440000e0714020807900c1d0001c241524a40980c031401400300c1c40b052004144a01240c2002009003409458880342d1a101e01e0320103030a400900a4040140c608000c21041844000c000c40c125100a098112030131440b5004407415800b9030001d0751030384 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 84962087 1250 84960837 84960847
    0xb0306011e0c08031e09010902091b070803010602060403120c08010501110f010507020318151204020d0501050412030c020606010801030210050c060a0609060b070812060d15150506040b0403080c03 86
    0x500103c0214864403940c004a400001e8400c207080c607401c0f015010040c0d51389060250001078440d40601500b240001c00c1c103c40400c0d60b0b030144071080c0b04080d00180341000100001072015000030348180134038402d4135101c0451904051090817a142006850002580080104413030350203403014a5010348414140c45425050750071060a49a00740c0e400c000580c000903410780c00122004e0784802c000401c44403002080260841192107008900c41c10007030a21a8001c5000c41d46c0d1004031101c07582e8003c0080c030251074681840050110901030300c2d4046400c14800002051003c92050f1140e6016115a41c0756402d54003400150040d0044440c213000b410000903081d1078040003514415018041c02085550034800f1840640d8640d0380064440c2d50188030700d00004241d0f209442c44540c40b02c900b000140d0302d003c00500200a214806040729503001d4000d44051000c0d0810b2036008107881c4040451a514814000c00d8030441c0f2901c440c826042c0414070020300200010108560500c1c1160704007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 84963337 1250 84962087 84962093
    0x6030c030f1d0606030102130923040804091112130213090b0a06080708100f110a0305060a05090c07031101061706010801060902040308090603060d0c08010b01090b0306011e0c 77
    0x680d030105444800b40020303030001109000400c88154480d00c29130096040c1190120041c058181d607000f00010030b6190322400100141c00281500c02945409820109040608107100035501500515504600b007502840743e1942c03120440b01c004001c42c4440c80580c3da115254110444d8903001268014407010704d505c80585207004850010340135640780003140c205240b400080724a40e6000c2901a0440002001840008104a003940020600c040340300403c401e1800010700c0d00a11103010707081e001c555500c94a50507400544580410b88480c1d8000340c407001004441e850071503c82040010410031840001d100f180200d4210304480000701c0c03e60b490710b0402496840701007490295a014070010460358100340140c8004100c00042145807234116201c01d51103100d5041c805016520020209515894210b0000915900034100d01c0b203503074440c420030740604281031010b80050000400841d843d42100b044a00560050711260315401c3c040890030482c03006030034000248103500c045c0c2c0001c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 84964587 1250 84963337 84963341
    0x20108150a170d110c031507050f0301060c021206012907050706020a03020d0804110402031f0b0a090806061e0102030415030501030b010602060907060e150f070501180c06030c030f 79
    0xb56807100c00c040c051010200380020300042264084c40c00a0740090b19406040e1404582507c07141c0c00d20100104542e501003054455100f018581c014100c400000000c0045d0302c400b008524500c01c40d0b500c00c5580503002890380d11002070250341c4d040c4450a4a010300c05212150807000c452000c4c10440c06d218080c1c503914140f1b0b1441d400680075030000000c9001f010350500039501d00880600f065041820652103e290841340e1008440c051940000402c4002d080303991031004041c4a201900345ea0398480346182e1154220100c1d14000c120a900045103030400440d100c2c3c03040c030340a0007001e00c6503000320405211240c4100c0440c15030200300008a8004100881482c0311911501c01103010752461900303000400b4140d0210045400100902c841c8982c08142501181c00a00c0d03c80759540001c80040c0110300f140e0010860792400189404ca0740824901401d070450080008101c43c0144900c0d0f4407200408110003807140d602e0f80e80900100b8020b41c40490403108520300042c1c481854072078401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 84965837 1250 84964587 84964619
    0x513180506090108030c0715030b040e0c040c030b0108130303060503031219060302090f07030e0a150c0903170d0b04090f060509030a0e01030b06070606170c010903020108150a 77
    0x2548610800001d03042007400240144100c100071850400504001521b80601e80640c3c00f031000741a101060141c8242c121403100d4038000d000700001c0c11840e00c46a0380b905103984e250b00803403c0a0000801901034401c6642c0910103845030b0055a45081c03064039220541001102455a10030011460f910308002802c0c1c4005007082c0040507007801059a604c3e20843d0200007911424860b0500050300c560080036000802050200c1d81c41c1c03600c0700c05401500506000c06450322421004a0510800c4041c03405900310145040195041e16441201e201410340405801c0344000d505460009001a008081a0003815000900300d0f01034000902942c204081c160742c03600c004c8421005004040c880c01d074002d5a494020741c50300307000d810081c00742921009441d040c5595500b4482260721104120790140c7c1e030102c010005151034540841d01e2141c000d401d807000340b10f005c80d01401940104c186100b42c070340503150412a950303440030b600b200000c1041e03001c1d04035149884c00204a2480f000040c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 84967087 1250 84965837 84965879
    0x30405150c0d0b0307060507020103020c010b032a030706020703020d030e10090e0609040c05040e0304030821010609030302060f0a0207061118090115030e25051005030403020d0513 79
    0x25960302c400ca8503607016103030726064040c030135009034004200c2e558100c0201c401d82e03582801c000da15082c3e0025050b00604442d400d480c1c140c0254001c04452072403031007030b00c040d494007c5914800c2c3e40100c001c0c103039250400c0c06200003681c0004802c0c000340c82d060041d00d404a10900d00840703c2092280420264130b0301c0110301d000700301c80c00e00c00e201c4c3d03910202d07001d907000005450500e17070703481e10f9201d41c030720841d0612829024560351258080d51030005c2c000c8030301940c0c100c02081c0e80d81c10800d50000c141c40c1c68210b0403143e038541000108816100d00c800004a0f90140d0091503140c4403007002011020010346000d80c241e13403c00425000540f940500070101010414481e100c0030303007810a203403040215001501c241030002c0141b000e400e1001107104014240c2c0b070f00140c0498906042860b01c8030301c900540a10360308000c16464410310410440983c0c4003500d001d6031541041c1001c0c0c81500090342d0013409604480302c0d1148487c4a0b2014140152240515802165480035250038a8841031820 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 84968337 1250 84967087 84967111
    0x20f030a0507061206061806140423040506010503090d050a030603021c0506150d0f03050f030a0510090207110d0503211506040b07060c18060c02030105160c0803040515 74
    0x51585000c69105c0c800083c175136420520224074040100800340342840c0224070a000c1720807080d42111004205813001b80c00b40d40c40039a0302803000f802d2841c080c0d8104c07417414030441c02d01000481551007041a00d025480b4107005000900300c0d000f0544054001c0d007010b00415076142000405607a07104104010722106c0414100134854a003401c60504c00024124041d03108804550801925180450810103802076101c00c014295807900f151184520880448403039004014001296505d5005030300a1118100c141899a52200c402c1e05a000d9010080c18020260084070f00d50300f0550444a030940c030610a69250a900c01455414241e5405d01c040d0014031501c2000240d011003042c0b1034404400303d6040341020700e080d850300080d2060450041000342c0f50107691010724056402e04e14541e01882800c08a00c0c0c65182c01029903d6410702a81f10750300344000318920080400d550301e0168101d03502d480207d400da03200d6200c942d2010308102c440b1311540c0c1003040721403038041d02280141045449 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 84969587 1250 84968337 84968357
    0x1302040b1306031104030303020d0b04050903040906060906080c0309070e090c030705030a05250504060608040203010b150a0516060603050706021002030906060f0303070213060f0905040f020f030a050706 89
    0x10401d0903041d00100305042c60601c61801e642ca00c80240d50403240d240c80c0269540f070300c8155071009060103214031908a070821081c012424408809807007561828001009410f0340c0781d50031640034070180300b400c01041408010804c0c000ca03c0c0011035010525070103e81c0429541d2a90241c001800c58010119800c00d4072440842e10307003800000c00500080b40240155042503e81c80d440340307000a094040f066044c2c00c12a046c0040b20300c4080201402801040015626400582211000c4608900c2540f07850086012440c20000c0303a2082c1440c8002d480c28070915420030f591540c405001c8106488001c0304e800d0001e9241c0c055200654070070405070826500d0b00c50081c1c0b4258450400381900380c01407080101c1002c000440aa104804982682c035100c14030b0007080c11440b0724500a904540500032030075040c1041d400800451340203500070224296034024500031174000ba1030007050441146021070140c076018650004080740181610741c10100ca03036480380707411182e80c00380003c6052000c0d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 84970837 1250 84969587 84969607
    0x5120f0105100207051e2704150507090501030507021e03040603110313020411190807022401050d1707121d09041212020a02030403020a0909050a060207021302040b 72
    0x10b00e2191004072070004090a900b0a00010820302641e50661550404ca82500396140d07500f0104180d182800f00f01d141c680d00314061008409802141c00391051900c009049080a000e8412a4410185682d4103100203013000c1c0118003803c0e02402c540214818000700c0080030b500c81d80c554040450300c2c00250782e17462400e5400b4090315449a20b803107410390300344200130000300010406002c5581c116800a61190780840c41e032202d000b00700300c0f000c1360184005140540394000c0d00c1180103090759002c40d00e43c1499810100c24191781c5072801030b40b000140300100300505025600e45e41d15446280d00d2640682c00d20100707940c80c9c004406c00d9070107010344000c04a925401c044d6100c64070b04000b00c0c07280b00719803420100d00c0305070380600002c10316a071042080d04180c1c440c0300780c082c0311a92a4001e5503146540c20009607603400602082e0b02c42c80e100c070b00014501030741c0d00c502003800364498058004203480e9100d6400075008450142e80090148c40c4000080300c1300e02c003c0016120321698551104540d00d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 84972087 1250 84970837 84970849
    0x6070c2d06061a04290c0d021501050310181b0609060c0c0b03071701090e0601050a0602120a090503030703030c110604030e041802030d0519020304050d0f020105120f0105 75
    0x790003004215904400001c0f030303a89500449065503210020813244140d050b403202042003440c800002c0420740826000340600700412003000105481d400c44240d08100019140302503c00c1c030034980d141e0f0100303026090000d05a0010383c000ca80158000c8840d13002c0d03403114000300065601105020010030000e0240c21f400041d403001602661500b10102041540d80708445e0949010390000b034040840028441403180701015120140000041c0807940d40c1c2c0c00401c0035000b20400610349014260010449052555090080382c4541d0300a140c1c03031a00003506031043c4d000c2d9544a0800c138a0020118140d01c041000344a0319100b5a00010b0031a4221b00041c604282c41c880d000003a0841808d10000c213030301c01c01d0407189040c110303000948451407600c246024280080029014021a5100c9658540000c050310703c0e405c150700420040001c44100b20388074407447c01040c1d1b00442401c01d200200e2450403040c82001c1c41810840c2c13a0032400d00c25400075550840e00baa400c0c4a01000600c007a050130 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 84973337 1250 84972087 84972089
    0xb010e18070501020a06090510090b090c041505091e010303200c15030a06090f0c02060601111b06040308030a090c120317040f0209070f0318020306070c2d0606 70
    0xc00040d000c914100350000351211400400601000d48840180c0107108081c008801a00034446042061074100d01e45038215070021a401102401101248282c41c10280541440380008641c2c0087c0c0600741010440d01a03009400c3e9480d8200c4d22595901000712040f046000e14081c0c0c551456a4a100419100c4400066001012604a1404000d050f140c600060442188040d81c0b03645a81d5a54016001000c0d50340c0116141410001d6a0f030310304007164440c0c68910341d687d0956040d50344440c015100c0040440f0351000741c0c2d21205604c0101d40050240c40c3c04404010085490706030399403140403254206445880b521580c644012082001c048034001c014821740384844120314850f00c018102c80007205c28403400d01ca29000080401070703c040702040d4240e008081d92424113154600034640034940da40b14000c44d103449455070900310610700d05074100358000c009000f25518070700e04403440b01178168215191a48a03203405041e02c1d0710305460021504064042c40b03900c000c0d09011040d581a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 84974587 1250 84973337 84973381
    0x603010605060a170a020c01020a0e03070f12170708070b070206091618020f040e01030303050903030f04110a09061413180f11040911091509061c0b010e 67
    0x1080000f440e02540042040c0c10541030070345000e129956450914000e445800042002c2e07510004420703d08a13045001100044000c1d41216104e544074114115802c1d00d0380188940c01da000408040004c0242100c0160f07030307401820007810041107649000040c8c1143c00210342000340501000940c0d68100216a8808480d8004020610726000311a1289505004800c000b102d502109156424160104c0b81c46400e00409190384556800604840150a0204030002400e10b00400c045003400000c4c2d0740110407403000d01e0b0300350b2202d07600d583c228000b200a00350042d50341034002458481d40d00c1800e00601c1d0070700c1c8040d5881e03400000c0100301c1070100c0641052a1030803420b000071000303080100a455500c45440310480c0424205100d143ca07000e00d0a5500904044d0301c00d00300a481826000c111ba41a2403040941d102c241040b00110051800c00b6040300541002031501e1510b8101e5051201c03035019250007013282c585550445c50806d030040d0400c80d0702c0000303000540039850441404506 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 84975837 1250 84974587 84974599
    0xc041a100305040b13030212040e01051003060605030114040905061918050a0b06211e1903120605040e0a030e1801061202040e090c03010c020c091305010e03120603010605 75
    0x94030b913a9041c41084040d1240521081209140e02014000c100790030384041c161071500d440300d540e1b4400101200e024010700703000f844041e444000580c001d009400c01e8640c59103a0320700303681c2070082c282c180f41a0040360603442620b9600a03004203409000c13043c01040c4c1c0d0f000c04c0c032505002d41288400d407000b2a84020784108000d8000c0045100400c5502d101a030001d0340300c081c0d44404001038003840300340004143e5507580d11024800100001a080c00c004030101d078121f1080c404010329078a515000b009080c002c02c8030303071111001034420441041104084034000411980f1070010600312440803a80100a602102d00d89041c950410b10032104140101c801e101100601040d0404619040c40b450092100c0c4005610a001c02501584c01500340750302100c10f00d11780081e00c17559520030001c030580203521f02104803500d5440880c2d481201c00000c1d0a02089894403003071140c03007940703101003a540f656031620845c0f45c0c2c2074180024003100200c402920007030f04010b4205421561580e0040b840742f0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 84977087 1250 84975837 84975841
    0xf0d1a0f0d0203030414120601121b0303051602011103070b0f0109050601170c12070e090a0b0a030f0f120503100b0301060e090403030b120d09050f060405120c041a100305 75
    0x10b90008102c6040c6c55840318602030041c01c00c00452001401901d086c00a8010500042512040c5102c980b401c04d0154103a0b61602400c20f0a030300c40c2848500002e0000354040002c00070031203426007911302043c41850900960300d0030790100f0381150060712040352601070490510140e03081c00d00000b070251003242e0b0104030b10704188002906410100c100c078010700000c7c90014011602c0728043e10000a1100140c070118035040071700402c2c201c0414a4903203d5800c010116402c10440e00c59110700d0a03002d040c0b003418a0a5440c1c0c0f02450091140848050081560340c1001400726803000840301c40c541c41e400e4880c2070900308454002519080091300c800140010000d8039030008060803142c005940001b019100d50608134080c0c1001001e482c0c200d08081c001c02d4900d100045c80311044140c9036200c2c1c0300c0907241c004003c0606c5412048650140003071106100303d00c0c28a4090046101c45000c954810004002050540781c00c800c0c048502604807060ba4054242029010040b843c00e140c100031034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 84978337 1250 84977087 84977089
    0xd020106051e0913060f050708090d0e0105070501240302151908060609040e0d031401050f010f050c0d0903060b010203130312050408010912020d050304170f0d1a0f0d02 74
    0x30441c8401e02c40c41140d8a00208207089034240070780c40e03200c2d04048180031042c22500703500090002520503600107103a103c0096204080030a022903090041e540c1e418004581000440d2540c0080b8403d980c3c075540c40416189130042c02400c0d00409541c0390340c02603c949103004100e2040303a4003501d549070300000c2001140e220520b02480740d54091500308000b058860801240c218015a0300164203d413500708040ca0440b000903814800881d00d81e004e01c1000b0301509040d11a000030300c00d090b0016801e45542400e5805880b03505429a03461030f15904007860060410b10f0700036184080c80120311030a0083c41401600d001d410700c1c21030300b0f000851400d0804012181400c059200c040d0000b0b00f00100e6440c41340c4241c2c01c650040ca9084000d1203140582d090140e488502d0307110902c054811500340341440ba01501c01c0d00c0c071803500100c102507103e030042d06100099200c841c1c400b1805404010800303401601e4032664040c000c0110035581110034260512003988142d022091050800f00030302401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 84979587 1250 84978337 84978379
    0x314030411151207120509010b0105090909011413150204050d06090302030415121a0d140a0803040506100603060803090105160807150f0203061c050f030c0d02010605 73
    0x81d0319010388100c910304292003000552401002d41e85955402c0b200207004c0c24030390240740d05400081320101000907440c0c0099040c00c844900e446a404a001842064441e162180203150f1041c56800041074074501d00a0040769071804842d00105580300c5074110081c044051800203000c076543c1001c62400c0d041c130700014002c010306000102003c1d12440d0750400c00d03209000781c80083c6824806120901c014403405810601950b9880d070f019450714414249140c074142c84540480405852620146440d0711089951a440921000c0a116200f05400016044801944101d000e80c020300514104148507000c1c041c030a0703008008050030404140943c0102008494061b4400d09000313075a0080c0160780c040410746050080c280346400b0071204107100d10110740980700300386040c0801413800d001c2d06c41c40490005943c07843d004109041c0d4601c002c000c4284c02c1403014011821038181d041099042441c40d801482e210001c2d030030001e040140150240182d5025003011243c91030102054022914 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 84980837 1250 84979587 84979613
    0x901050609130230340e09030f040312120b0108060121020403030905090705030c04050603070c0f0305040906060c021503060a03080a0e0a0617191104030c0303140304 73
    0x48155040c0355244542d41013804861040307400d2103d80701d1800070390f0003000c1e102c003400d5810280e20508880c0c0d014091100810401071010b09031400840d40e41400d607841071104009000500511040201c2100d202014025000641c170030040c104180718180310040034030b280700441c4a10607040c020310200303036a0000c003d198814028a1709100d51090100307042034240c008004507003281c1c800240841450f0f07100348004150303107060342c1c000c4442d11060421140c510007101e0b400e1107030805000030310192410100468210ba028644011441c01c107444820244600302011804a2030028081141142d54000c1e00e00030b100604117003010030031507004983c026241a0b040740000c2c00000000d006541c0e07000d10003000d903400031980e07a11108031a0015060b009012a00c41c4550100c403070028003c1d11410345c41126101e010303088030345e0b0340354240000c51808030032440035111034440910390265100c1101500046001d08500c03011a031440c1805814101c0013807018040500c1081008007148901070010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 84982087 1250 84980837 84980839
    0x90909120e100c0305090a03021c05060f0903041e03021c060e010c0e21070f080601170a060507120f0203040b0c0f0a0e010912150b0307080709020304020a0503010c050309010506091302 81
    0xd46d44036901c400240e0889102d0300025840300c8101c002c000c0303440140f45800d00192050089960b01c0d202c0b444100e000700002ca520b054035034004c00081c001c1a140001c0300e106880140c60280d241600c0c3c0d40052008075810980490000e00e205144082c4503803402840705080d5024020000d604104600800452201d00c18502800031258a800c01490600350811051000d409070341d411603c415034107045508078480d624680c4500c13000450741c1d425266000c000051403200070941081c4a0b50340001801000f4042020310030500f010001c503840e80d000d0201d0090f842040140d9a28080c60007031405040a030840708907003010700c81c03058003c1d503041c115080c4c43c01d00e0800c0280e010400300100c60745101398001689c4c0d1100c00514104003c000c03c08055130b515031079028006007040c4420305075500080d105403041584420404c1140499650003107801c14000380141480d16107d80202c3e00703640414010300000f032000410405501820303c1215000b000403603905940d03080012800c030541400240203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 84983337 1250 84982087 84982097
    0x204050303071e0605040b040501150605120405070801020a09030314071e06020403020d0f031e02071502101d070e0c041401020f0d02060601020c0102060c030c0a090909120e100c03 79
    0xc00f201c480046a80144140c1c4020700303001030b1410b0b150094040c0000d68040b1440c1d0300b40b21406807000c1c41c0d0454032040d124a0782d107007030602504001c1c40200c000302038000e4a160003500d20105607420280000c0c007002840d9182c1e600030341d00c4e52038010f0501d1810344040312100030510001c0001042020038058543c016420304aa007049410500007c3c896540000c4d4807411480d8000e040100700c45130b49181c58041d0700d80001100e028848052031042d0400d4000068001c0c20043c44024483e040640310012284112403503c40006003250446806100c0820040031410941d0b809240c01c002c803001900c0c05810f0340040307041038600c1d50100d0055026120a40ca80070318405074691080000100740450041211588007211f80e02039120441078425a0050181481c40c400300c1d400000c5480c00780003119900380c907550b41c0a038104825045a18a4010050700d200c2c002a5100940911011a80a145030282c00607820b100034203c0818031412a00a0301341680348030a803500031040f0300381c4a03058180307 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 84984587 1250 84983337 84983363
    0x81906020903070905010906050418020102281401090b0c070807021309151406030c0a0e060d0203070b030603011503031d010e060c0106080f0a051e010f0c030b040b0103020405030307 80
    0x41d04112040c0c000b411502d240400001f0440f441780c01080407540184c40c20804914103174400b04030704100c0362001e13000d684042200381546c03404007219245403109403586840080156030340b5030020b5607035004006583d115841003041c09905886a0341000e040195a468802c1e45e0362003403914081d40c80040c2c8a010200c0010b0a8200c1d01e4202c10943c591045010703c9254046d4125030041a64042c03080f1088400400616542030004c3c040408030f0f001400c90401e54913100b810940f501d0f000b0f0102c0e8100164088000c0140c0302089240050001d046041343c0340c2c40c1203000d150846281200c440030303104207850108040380c6c0000314a24803050302c040da5842142d481005980440103d0034203a04001e0007e0400c1081c0e0b0b040d8042070941e0000400e840e4000380c01ca184503603c0034070200c041c1258101e140348007601c085184200b140140400c001103141e0581600180860310111841d10110751100d82801507071a02e40714407800340d002401d0440c202402d18011a540b4011290001c00c2c0c10303040c20b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 84985837 1250 84984587 84984589
    0x70807020c06030c070312060515071703040b090c0d020a090f060b0f0409050a021801050307030f0504060e0c0102070807060c02030a020a06260114060d1b09050a0819060209 76
    0x2a80d2109003000e4102a561309220726484400d9001c1c41081d00001e4120301182d0815100780030300d004840000300110610702c0c9800b10010603900081080340e500d2184100300f140c1d0702484010790312660044c104042c56103404804141005945001544540d001c43c2100b001607441e901e001c01500c14114000400780100c983e035034000c01080d0007960038000d01044481c446c0c45928014401d44469a01c2400107465111044080e4000d52100c0701060104980000040d4803502c091a1701000703078035005c2050143c0d802141c0403076000303480c107413500c075110800810300200c104140c0304001d0081c40201005468001250b4803117000d4022007040015800c07410742556020007590103440d4004005c074181c0bd66075080641504080c034640e160740c0c2c0b04110660310000700344038824120340201002107014208081002401d071300854140e1080d40e84e4100d850129400024511010a03250701c8860455040c00100020390010303900040a65000303400c0b507002c40d5046072031103030120b1348842d0158550108034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 84987087 1250 84985837 84985843
    0xa030f062c1c031d010c030605010e0303040e06180a05040c081f0c02150f060415030f08090a09051302090c04081c02010207050d030515121e0321090d0207030b07080702 74
    0x992400065000c8401e28000d036503040d440340d111b107051520100b02e4145d8031001558171096000c00194540c000b81310800402d4004020705a0169005041c204981155003a03e60600420b48900182c941d484081004021002c401000540358180040c608540c141c00206042415172404c030a8094868502c540c01c180200031085400807107081c0b0316110710388901040d1b02c440d02152943d01c124104100c600da00c00c8840c50410590360030004900c2480c200d520b4002030340d4000e056840e04500b02c00301c00036440780c942c0704040c0201410074500581030700304e0040002d03c0d07001510340107135041d04200810481c8400105620010303916000002e904008e484180d00a005460000c1d085000303441401401c5981588058400d001c0180c5400f01701e40140180100c1200f611001402d50340322502c01c9501c407850952922702942810101c130314182a0b145003041102070820303043c11890b01d64080c401240000c0c800c2c403010302111310091010610f591100106924041c1a0706c0601c040c2c0008074012500c24 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 84988337 1250 84987087 84987101
    0x902030f04020d14030a0305150105030108120307090f030f02090a020309030711030c040501060206070f1409091308040f050f040e03031906030609210e030309010e0a030f062c1c03 79
    0x160599440d0a80c614000d805040103c5509c01c00104000e58038401c0d43c054000d480c144c070199002010103011005004040f43d10140080b014000ca480300000c1c40c0c850103c020000d14400c250792008030780a88148000c44401500345103d4030700510170130079880400000d80300c00381d41101003500e07101c0024000c24104513155003100d8005082200114005800087d8a4000c032226951081d035001c00348012103c03600d04004001a0050810215030203240c021510354101e40705481000c1e003402e141d41e483e031703050b4456442140214032010b002c200340d00d4101c500000c20030050341c090000a107840320040e12031000420b44480d1843c00c9107001e42c1c200c00d5603c54001b45900400801050b107032424143d48100703417900141180300e4480b4140c0010b81c880d02c2800803d01c1d001d80114100070340e52006484061030501810f030090008880000490080c8040d584d40c58090030380011000395880c00e1555645498080a04078080448900707070824000400781415801c110175100580d850300400c601801070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 84989587 1250 84988337 84988373
    0x3020a0b0703030e07080c01030f0617060603060108010203040206070b15040c0e01090603060e0103061d0709050f0a09030e060a02030d050c07050d02030304080702090402130c110c10090e0c0f0705030901090902030f04020d 97
    0x44180034cc00302010002d0b0b402d00440c030032021600c442e0f82e10b203400c90a0344411200250050b1052051100003802000c1c03450700003280088122480b000c0c84c020904072005c1a21141c0020703078201c0d000030256040800000681307624a8144003817400d0a070900526001884018842c0e943c460b407840c1c0d4001c0ee0f40103a02952100d04c10340e241690f503960580042d02e01620826a4441042d02003031405a4901c548002150b040d16020110070f10b4a0030083e10360490000c14003940000c00c000e50080b07003580309161150960042c900e44500080c1800340ca8041030000200540d4400c100384070100b038031803042d80d00d03156045030903807942e03035861000c03803200c62040c408101d0741400c100c00394070160b0300400b44d14400b104c80400c0b80d00c2003284800700455031700f0000c461008503c0061040c0081007241c0e501a50004d8100c540f90716011100884039401ea01240c003d6070713540c101003284252503900818500c014004540190705505084080390368019000d0002449802c2e071500c0300040080300340e01d13050a032031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 84990837 1250 84989587 84989609
    0x3010e06040617010b040c1b020108041712040c1d1b040f03120e033004030f030206090f010b010e0103020d0608010524040e0604030f020703020a0b0703030e07080c01030f06 76
    0x8100784a1030103017a4010010340b04505050b01400024072a070051030000d0014140803412001c5900152400d6802410a0720f41e91404030303040700000c0342c5074010300031021840e04040f810324042c1415100d00362150414500005a2011582c6240d510a0321940000540308589007a00c03c012104546105550046c400c1d00050b0390000188180014000c480e000107480b42180c14050000301500c07040c0d2064450003c070304e0002e034040306210035a0309511000ca06000c55280a840f40c50702c0d550414105811001644031004000c4070b0f01d018400304824034649002842a52078040010700303142d035514149810994046404261190b181d08450f009006460081059003010f600315910f2540a9a50181c0d1207002c80f208900303400c16101e5240c060602c07078060001350300d90390740c210341d4000d0841c0d0080440c4500c600c0071000d66250340d000002041d40c4404999581c1c0b07185230240035103a00d00750b4040035402c52202081501c1011070302c01c0361180240f07070005500d142040c405005008075040310010903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 84992087 1250 84990837 84990869
    0x1110c09070e03010e1f09020103020903030d02040303020d0207060c140a0b0a0b0414010e010e10030b0126011a013006081c090e060f040507020601150c050303010e060406 75
    0xd034100303080710b40500d420380003400410503030250b40355150f82d4464000203016074994088a41071503540401d11035032052501510b030243d1480020300e07603040707000c92801d4280d001a0401c20560100614600b240280c0041c05403d0300c1e05001408420024030301500c3c20398080031801ca082c83c00d01500c040a980320754030116a04103400c01100405142641a0045181c540381c0a5443d1114040c64101e6400e051500d50302c1c4e00b06803442c0e04040c2d0240c040c3c803020b81c180c0400700010b0084014203021700f80074100307044006014041d00400c2c13002031031640c00c1645002c5030611240358801560707130755040c03c2c200080783c0e20040b41c20300d201c0a521200700c41c010744070000250300c1032803540101088450304011a1000083d810100210745000d0048001040d20b0010402c0541c00b0101a07961105000741440f00e00d0500d14017142c29254120750180040c2c0001c070050250700c0052034600d40d00d001524040c04a0f10f406e42d103240d074901c018081d904442d008400009c066035603d802c140c026001e6900d440442e4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 84993337 1250 84992087 84992101
    0x60307030504140304030c14150304051011040b1204030504122603010506031906030210030b030f030f0f0c0a0c0f0806061903020d03020c041506030509030c060601110c09 75
    0x18007082d9422605021a11050080f9001c000305903820361f030b0402d25141540d403800b040ba9140f1100038920035002490b07000803205010382400918403a40c01a0041d180183c068400031049440082c9031324003804081c0024804228400305036079031140419003d041076100c0382015101409550f020a0311411807002c150100220640d04080c0a43c8a002206007a4541c0540c02004d000034060240c11020500004480c88802d16034043c0550501c3d4000800d55129008150141380882d0110302103a150880c0c0318150508101d0311001502004c0a1070800082040f0040c8611844490000410010500c648440c800340141308000e940040000a10707551144200c03105640d0380b0034140640903140004a150030803816158070b800003e0190b0607000d00f1a0b0810100c4001410103404603c41e0728040a0252918071a54148500006000051071310300007004040e00c4005100050540061100c0c0082100010f03401c1d820070001d0070122801608074003000e107044000074071194001001c505100c45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 84994587 1250 84993337 84993341
    0x1504060f0c1b030b06040b150d11040f1508060319020a180b03060a0e0a0b0c0910091806050a0918050102030709061119060209030c03010e0601052103070204020904090206030703 78
    0xf00ca12407900c0040c1503407140c0801c01160a111981a00500087c00e140b410511103c004c200800c2404000915080e02d803104003100e80244d04206030317242c070b071000c148214080d951403510b41900c41c0c84c2c1342d506403030084080790321415000f03010b009040110741d0100440d50b0f581304080152415009004240544000740f00281c0b6039040b03814006d009540c04980b5a15590240182c00c00d51f03240100031910841d503c42903081001450812006002e00002e101a5540300b0a0900f0780d001e580d40b481c0c0c240c00c140c0c11708941c032640c4032041c010901d0708000b084940ca5001911007280c85400002950807500703d42c081e24a8a44007004013194400403c00c03110a411008000907601e407561030403411160303016000e5880c3c2e014400700700c44d0124030101000140b4590014a80d03040b004c3e0550320b201e0b0055010900b5151018443e580c250800e00050180d410880701340d10341c011003880040481100054220349900c58407034041c0c0500c0d00052110115101c0b90849071400c0c0e8040c00d550769a240010000300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 84995837 1250 84994587 84994589
    0x10209060f1b07030b0c0901030b100c060e031602120a080a03020403050709090302030d05060307122103020304120822080304050601060e0f09090708010603050610051504060f0c1b 79
    0x103603a8102d031000744044000080d0b0300c040d03960150301a802501c0ba403105e00d10540088210b82d0400d80c42c1d2001c03074003d40303c4c001c3c00d804084154a50700c04150f07081c03400505071801c481e5190096842400003005050410041d81c1c0ca103501501d04071824458002c800b0308203c5210005400c0010000e48065450703450b9008008803030003841560103d40d1100c0084099403040c1c4000740c0140e00a2050841c400310300d03803045410400c000c2c00c80d00041d503540c1c281c0c642134000b85015503a15030045040e810386910701c402c0c841400c49914045240d0f29055442d041c0150302022540108040c00700007a16400781a802d001d0701403000c21110320000107078038002096610071181102d03940140000059414010300f0f201c01c0c1d902006106618441024051009801006250b848544600d2000207281e207428881c0768055402040075090b1440c1c210b611809851a60b405940145003c0b81c0c03c600d04040070f800e031402c1c0c2d6107515102030b03604041c0138103c07035800e080c4a000d0051944100d8101c0c40c203a00041c030314 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 84997087 1250 84995837 84995857
    0x301060b040f06030c0903080301140a05030607050a08060f0a06080405070509042301091e05010207080d060303020f060c0a030e01090203101e05090a0609080708070b040b01090e0d0e03010209060f 86
    0x200850000d60303421501c541c007611008040c0c550032700050007404070908000064140191464900c03d41d1817002030f18156081e03440380c001c19400200d44058903803001505501c8201510003034501010500856041d440c240304d10001c00c010440894104003003800200002c000080c0481500e04043c00c000103060742100340d05540d004c800c0301c41044042c040c007442415a8000d0000740d6040d4214080302c14460700c4403070403666550308112200001d100e500107001e19141c002000140c090071440e01034a00503070642e00e580564001010072031a03a04034011201e100b10380385808a0380310300b0344030703072074050081b0350360007035040c022340c80c00c80e00da80402e038445000c454000d45070000c424803c0d03c6981c11108186e956500c0c07030308254038240102c2c483c0c1e04a045010b2150016030303c1c0c403403280c07581c000e0380d0802407080364030086890500c0180010704800c240035281c040c41c1004050032401710943d9406140340181c05000c180740c010340c0255070a50540d1b40004025000039a038010328200c1d40d910f680300050070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 84998337 1250 84997087 84997091
    0x405010807030b010905060a09050d15151a09040e030714010609090c031e080f090a05060306060d0b06130b040f06030c080a0510030c03080a110102031b03060301060b040f0603 77
    0x1015240300f40034604040d203060b111841020f0400d014082264000544c00f02802168040002d842e242c03005e500c40c0c414054030141c2c02d40300c0707119012030a50b0801c00b80704040401201c004e202c840003544500c01d080c080d08035141d5603401040c0115000e05003d0340c0303050f403902000c00c3c540b040c4003a0421002c400c40c0302000030004207403645005d5007100c10f46500504030f50080e140900009112544d41e0200d002820038082910000359120070041d401190f440c1c264140100e002030035410520841c2015100482c1d005045251800104400d80516202100c440d80c035035186031000d8548808440b6000ca800c3d410f500003d4580906e05002d520030701c07406442ca50000c000040ba544a4450904d254441c0d5540ea01075440d030030303041c1d401360502030400c003041e04c0950000000a56807012010003988a046100d07102c0c49400000fa0000100050000a590040041240703401544281d84c001c149a00304441d140d4440c071011038010b16241e0060740c100c0200140c0400c03200000090070048070301554007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 84999587 1250 84998337 84998341
    0x50103080d06150f080406020c0a0c1403031c02030703090813170c060f030a0b0612150d050606010518091512030406201903080105013203090703050703050304050108 73
    0x283c401c00f54820900c2800104003803030a0701e040d482090180c1e0018003075040941440b02d460300305404d09101141c00c4074821980401040030104102c45401101e0084024505101d1403500511006040400760349100340c0c000300050f000c07402a80070018283d0030204c0d0644508600306080f88015450003000203054a503404075407030a4000601c56400d51000e000e407420501107a007080000e810140c800e041c2d9945a40e40b031859500c541c000382142e6100e0100b038070507034188041e031b2a07101c84802480b94012014144400b000c140b002514640007042880c0250fa03848240c0085038924480c80210f40d8481d001405002001140d0700e02c0c455140001c88241c00c1000c800c0c0e0529170390380700e40d100356400b1481c9510801000d640b42d11400d0202121f841c1a124a803c980c2c0074603000604800301180480c203500018030265078001044c0c3c03203150103404100c0d42050040c900c110203921000710140304190020000342c484030700f44030306002564480112030402e92603180407905d0350028000c040c002070076140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 85000837 1250 84999587 84999599
    0xe1e010605040209060708161a01031a040f0201050d1d0a03020d0206040b04030305070e03010905070e06120304090207030c0b070c030806010e180903251505091002070c0504050103080d06 82
    0x401c80d40c2071007001707013403602d82100759482260581080c5120038105d0803500300080440c26600300444005400e074095070036581140761008400e4625904d44040900a0081100040a00021408464090824076203c0b290800750f40003518500c40c050030600c1c4240e07400c502040000172a401c2841c442d809451003481288012650394204650107003440300000041808070340658855900310b500380c58104a407020b807002090960703100c1442141c03658082881007011482280cae0064108100300c80c0c5a4020420b990100d941e40030300d0180b0800250700188690406000d5420745940395440041034445c3e20380042d01410341c0420510540200b125000040c0300340d803285400c07a903d034100810034005825014481118044000e06522061008001802d58182030048103559105078280c0384030a680c0038030706010040070190310f00d400103081c4800c0c41064000031465000c10480c0000c016102c215500b0000f034008899408180c01c1032401e4001320034004114000d10584001d00c07005e0001940d500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 85002087 1250 85000837 85000841
    0xb06070809091501090902090103020412030c110a050a06080619081f18150e0f240702030316090f0b21010f0909020402091203070203071502030307030c030e1e01060504 74
    0x1103c550000c2e059103c14080740175141e025290340310701858010709054650040e0740c1d1807181c1d8402900410100310320141000050540c010171482c084c0c40d000c0180749027001040941080703000302014445601c0001d4030f26260b020f50008055010000d803ca016a612282034545442c6141c102401700102c0350603030713403402c180607101c0f901c01c220107003002d02601c5444810740c03600b5080c11000d219841d150b410140c00d1042040003008241c00d00a040084d003003540c2c040d07030701002201000c82d0643e00740030881065008000e0b039522603041c4049206015414501b290746000603001103411a00c030880115440520348042c0004144400c403051540c014031890b02e0709900241302d00100030110000c180014035240d013000440b5031000e0400340c1000d010300000341600400c1d03c5005c1042c0d00220388441503117000c011030f80081034032285030740c1c203002a60b10003034a9100040000d0203054941c1406800c0a20961190070042c4002c002c5c2d40c941c1031701807101444480d400c42080c071a5030903e400807a107490030f4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 85003337 1250 85002087 85002121
    0x27061803031b0e060904020c150114011205190b1504080102030121020906060d0e010504050c01020132100305011506031112011a04030b040f031805010c020909010b0607080909 77
    0x4c003202e0070131240c0410400a94008500e500440c0105141d55503a0744100c4641406040da0018506840400000042415043c0c8100014a6050005001864414244031544103844490100759070b40d00001144d0803031310300307690316510001c0000e001403900c1c019806541a50281208580300c01152103c8038400401d10788080c0d4071058003004101c00d40740240c000c065000c4040300100700500268401c5007140e0003181e058809801c00c42c0380b040150780c20710030051513007206458010141103600b40400c0280030500c46031104041c480110740c0170110400304100071035019000b0b00034026039820b441c844480d00e02c038650101e4101010f154070400c400064400c455036407030007014140e00c2d00710003900c0489007001000c9981000c11011012860f103c160900c114010443d0001603080d03450018480485440c1c0020242054036003400181c1e40610042c19841e01103400c1115512008280c078010582e0b401265130110f0b00007881000c00840303402520440301c0c00c0710704d1100c13640c404801100145503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 85004587 1250 85003337 85003339
    0x90c0a0b030718050a030f110402040b03180a0f0615080706270e0f04030e09040c090b010e030d0c0302061008030f0c031309090506070327061803031b0e 67
    0x10910000d02c0d40d92040601c800a03100e1091002c0d6000c4c0c0d154046401003400790001c1d5002c40891040d4001e00001c51180401d004007503030110b18081c5001000c030403a000c0130700342c0301e404507485001c1100f02004209030159590040c909500e82851072803e00d0081c418045c42d042c2c0c1c1e80c0b0050b00019004000f24088044800c5525407a078003051030010042404000031602004031191000420424040488103106071441080d042c458101130a010b4100c210080c0018801d10b850010400041c4041c0091000c5032010840400d954040f01e0058904180d42800030381c0503c18400514007503a0700c040d901c010f20b0701903001d545a5071074800310780c040a4054010701c0c020340d0003001114544043d01c0700a1400181c4403050324107011040040c10140c0c095980400e2030107132500151002d11000340721041e00521142020003001400090150051800c0810303143c12522811100060040640122460610000020300440084d28000d0002c05188105036081a010f50850b00ca05001c0c0d0721107114840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 85005837 1250 85004587 85004609
    0x1b0201050a050601120e07030c0305010209031209030d2001050405061905040b070f18080303061003050601080103060f0b03030d050a061d0f1e090f1603020901050d020a051305090c0a 80
    0x4550f150706018151b5002c01c0805031044070000000f01341c0c11805000034600c118005650b54190f0410985400b501d0114018601c20403c030010343c079030300000d00000c40b03540c9003401c002c86100b580c03113480c038084015802e2240e5401c0a040008011003c40c0030742c8140448032008070752410061044003145d0040340d00405400405002ca0030b00c50040074514126a200d2074800c810b002951402c240f00c098552112000ba4004000e00405182130f000f2590b0707100c0e003868204458540000001e00414062001030903180c0d881500e01e00d180320640000c540310501030f04581e03642906066140081038115000e80100740340403808200c084035540c28034080034400761360141e1910703a044400d00942c2c0181c250311505480740d4186511402850840340710702c848801603d054102d0f050b0890030000a94000648800f401c0c0c1e0a0006941c0c42c40a035065800c1941e1902c0f24014038804101001200e0700100d5014203a50f503060813040c06508414404d055120650b540d540d80a424401e0701d41e41c90040d040000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 85007087 1250 85005837 85005857
    0x61205100c170c0937050105070302030a110c0307030b04020a050402030106090311011e02030a0f09060c03051b010908030406110f07020f0103060522050903030915070e041b0201050a050601 83
    0x1c082070010b4282c800300203000101d000800921040b100e079500074520071381171400c11907040d0990b64080090040c8400c0c24100c1c60662142d5000b03440c2d100e001c0c102d82c103010501020303c050f210108900c910301d04010b02124029500c905005800680c00c443c200e205044801d004a00390505009a9040760500d0300e4400c01c41d03003160766070410400900401030400c1150050804550b205002d41d40c0c0380002e036000ba654441c4a00d04c01007411003c011b92100780404400c0400038554400748103c071050f00351422680303646050a50707800304d50580a010070715600703010940c001c2c080010015400b4502c50502082640c80456080cac0013405005c1218082c00400d0100d071340542800e445c20300722007405250005425403601c0c000b90f03102c0051980c040a4034a0100c284d9500902d922541e42c12114100055040d8030703020004c203503100010b601a0350302840400100719007a000d00b50407400c2c2000144180a120011044800c0c031214141c45940190700303180c04100000c7d000e100d014040c500c1a50f41d0704480c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 85008337 1250 85007087 85007101
    0xc1106090c0a050907031404080301060e04090b0105150c030c0f151e0903070b0c090a05040b030d03092402180402210601050405040f0204031103070b0a030b04061205100c17 76
    0x81a030040040c4c0906da01c8151099840800c0d20006106601c503400a64880d410000c000b007500100000881c003480c903000d4443e000c01d0520100701c0c11614112002d5144146e01901e00c00c0c1ca00072185052040d210200d1103100c0c03e41d001c0360071042d0120000c100c440700c3d1141c030010407200c5000d90f071119007000d003141005007183c3d00b646800e0b40543c0c403030126840e140e5070b40d90f070b800041000c0b01c000520050100d684001441c020940740700070441150301303001c24a2940006915a80911010070034595035590703003020040742041010760581160301124582024031080c0002c0d62064032030a16041d4038411521040c5080c1c800c2e204032900c5400e0124203218403102e0a0b00f03d90020705414107011017400001740503038070341c012000081d0b0411005070f16540346240c580c1c628108030040728030a8028050902c101417001c0152034110b0344a240105901c4941c0b40450024161500809481d107500d0881d6000d0000c001034803681c00860340c80401808444540482d052182d000c240c0500c1c5050002190742 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 85009587 1250 85008337 85008349
    0x312030c0a0905030d0e01111f0504020d020a060c020310110306010e0a1a04030c080c0114030a0b0a090203100e01050f0402030a0b09010f08070e061c150c1106090c0a05 74
    0x42140d41d8104520070584440000707182ca00102011030020b072000140038540d5071301448203210087c0745c070700510b502c45200b503202c00e070010701c0c1c1c3c4074a040550320000a015542e0310a61a00c1c0646c020304140d440e2515440010310601c9140c009034064801e068030001a1940c0d4454820a2455035034600d0864841500450340d000014141e01c1d408903e131600803c80d03111a10041450804c42001503603607910394684001fa00c102907200b0b08080e00040800301c16a42c00081c0700c1c44907120000300d55a01d03514440c541008115211006030024036081003c10742030243e50081d8010f6650010440c032180e07440034001440c0c1c10901070940c02c45100c03100b00c1050300b020b0700a150005540382c00070804a0710f03003011404404003603124196100c0c1e2a402040381c070704d0038400c400240c0b034070200c00d046602c1d01c10046066685800040042e0482010018042c08003004010070044030700202413192040c20f07036000340207030107109005503039001c1c1b2404a81c020a000604181c4a80050490100c043c500410400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 85010837 1250 85009587 85009597
    0xb0f1804061506030e070803090607080c01090f030c1e03020d0f02030d020708130b070c030b0c0c010c050405031504150b030f07030b0406050c072607060e0703030e0312030c 76
    0x24400c1c0c403500e008607644000c1d010807015040644d00004e01d580901a2280780000b00d07400300c426504108203084458983d01d04030b403412031300211110340e0345088032805801400b51020141480b08410400c408140d48000365500481c0100d600c0f02d500c0920400e0f03010b0701000d200004002d87c1c00a984600c100e4010801c1d070441410302d0060720308050941001c101607070710202086a8801000441e8401c3c1495a0f400307101620608202e01d042240079a2520640070070350102400060701200002c4030148024121f40001807964024888050b060a000c0c0c800e8001e40181d620900500c94200840c2c44c038111b00c2d41c0300c4c1e50040b088044c0e000441192100400d0409049501400f03109d583c10080a020002c880082d440b40030701c0a410318040c28440c086600c041c20380f0741c0042d41000000301003801c090710f1040d120315134040115503400700d4401c0e0010740308880b0000e1185040480d1000301d80c1c2c0200d0918100c1c4e0082e00e400005c1320301f41c1d040544035920382100d520580d0341440410741c08103c07000030301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 85012087 1250 85010837 85010843
    0x1081608010302012f0d080f0c0405130b190503010b0301140c03041109040f030801091b08070306050a0305010f05060f1e0307051201050a0b040204150309060605091003060b0f1804 79
    0x54004074175410702040c1c109105182c0096101050103500c071503101900c503038840c00c0c81c2c600c3c00380d0781404202c00c4c4481c801c0c0d02c546445a03540360300051082c2c040d5400300d8880907008240da000383c2641c030a8801c407074055100c0d4a110f5482c2014152540c10180220340c262400c09049003503640c4e0b01c03c106441600041c1080d200030606001038a815102c1c0c8551500850050b446002c101d02c080c6030050000b00143c1042008a0406841c40110000a60903103142d48081c140343d103455445a034200c00509403644001d03403000051800006020301940001da040716040b0f410300171360340c42d50203100640040300040b94004e5050342e10f00294108980d0030703070740e40d0030020191004d0a580701e00060035481406581d040a940d00c0d03003880482e40031445420203081040d01c06509040c40d2550014920314542002c0e001e05498244000811100350b000001a00004090341c0e40c60a04048000a03d0000d020840301c140c540044441246020b00101c0c0700b541c802000061030301449480b1501c0c04601170012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 85013337 1250 85012087 85012127
    0x4120302281419200a050f01050703110405042d06030203010e0a03050f2b020307180308031602070305010e16170703140307050601061107050402040f1502030d020c010b0108160801030201 82
    0x51413008906005040d4901e024030010b2941e40c03014402d04e421100045d0030601072519040700100ba552104040d02c088a0b01254001200724800714441c880b8482d001c00ba03840018914034030a080120b40d4815400d0360700982c0200020102c0f0001241d0780c070184c05000c0d01145007802000070700c5002c1d0004050002c1401100c068440c4c2d0002c4144200300205484418180c0110802a603290711013126445002d001004234002c51541e1203003c51031001500c5d000414820000c00071480780208810801150b100008015500d03482100700d8540c4240100145202d490340c500082e44040319104081c4140c1c000d0107403102c203203141d80b40c010180c0c0b2080c504078503010921201c00401c0d0148425802040c0c5034860202001d01d1203145401e110441c1c01ca10b214510500041c800c20905220400640b8400394000c001d0340c01c0554142d10318024012040140c43c00042c28480142064002c1c82031103a080c4c98080385d546503c103200282038240d039401c0c800150428010001741d84941d41e44006241ca039442 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 85014587 1250 85013337 85013387
    0x3060e0c1b0a0602030406020405040b010c20030a080f040303080115020304140a050d3002060610021203011502070906050d0f0311030d02030f060307060804120302281419 75
    0xf0f040d00341e0308110360950705641d000c141003002d82001e0041480d6071001b4a40440018883d9507080711603a144c2078284a180c00c046580011a02c0411035404e01a40003440d00f5190043e4411840865020380805ca0014580340000565218202a0402d42c44507a070007440c01e1600b0b060321480c4000c59441010f41c4100f45000005242d02c42c3c011042c80c0c64040c11030380745060078004a804400c08000310414801d40c082840711550341e404205150484001c81e1060b1006404507800c03442c08a0b014001e1a042c0b2000000080401e0101e64045100c440b5400b41c8580c56035401d81c07803007180c0c49445080d41180420301c80c4d60014001140c0741c070783c0500c203060191030750980135002440c58115400c08448564000305000103040c0351401140d01010460007008290b080800040114001400c014446084600076117192802901600c50745134480341c00100a4204080c990595000d9030b600710041f4080c54182c003402e001755821100b414a0900500440110b82e160848841c8030783d07581c0e0314a078819904 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 85015837 1250 85014587 85014593
    0x30603100902031c1e0e0102070812180406031e05010b0303070c290a030b0a0905090d0f0212130314070b0313020a05030109081215012c0414010603060e0c1b0a 70
    0x9184c0c41812400c0c4c6d0381800c94030310b800019160401030f420000556102810f1200c0f100048011030303026107002d01092405480b8440803502500c8690801820704000000382502c002c804803a40c07244500400091101c255040140341e124461010058007a09100200b0b22101c504a0b10190b001404248642c01502d001e801c902440d800c40141c0308002611000e00810310300c1e002d081d100142c03400400400483c10b041004079030368480d52580ea030521412501089040b8001d0202e43c3c0c4003905105125610402c1d01044038012440e0302084034034280280c20110090000114203055071080c2c1807080c03850320b604214912908414400b00d905c0b601c060000300e0180c4007805100c03200d910480844d621811791141c1b5001520300182030508404480c11184a90b0384d011049000120b4160b203410f4a801c90104800c0310462407030134881d00b00d03040c4040800310100d0400e0a0341290303034a640402c00706882d1114010801015601102824000d101401c100204142c005040315a1300c82103030302c0366903155 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 85017087 1250 85015837 85015877
    0xd050c0a0e0108070b04050f1002031b0d1205190518010e0606030f1501120804170a0203060601022a061c0b180601270515030603100902031c 62
    0xd00710055000c900c100400c58804108180f00241c440703d4600f90500c2d09020100320022040d02c00b15104618440910001b98000e20031181d101400341c14000700d00c1c402c2c0b0b90b0340d562440d1b404020000105144003441c01000b21344500d034000c8158100215418880700070a2002d0b0a000c2c002040c601319440d5200710400003481454440412113010313200340d242c44400c150902c0d05046030a842500310200c6204107010f0000602d041d100f0610b00c0d03114001d01810150003c1c010740c0c2200b4142d1510300c40d6100c58810006000c1d18540c4224111a0b140d03940100481e21140e50312000640c0062407405d0a1720008106000e000b42d80c4054503090030f100100c0c01d1440c10f0701403080c880c038800380d5440c0900303d40e0a1105102025507900e410150b41401c0c030100090011203001006541c00d01c10f0700014050744c06035210342004100081034264403506807141c4c22800d9100b5100c8610a11075040f081400c1d071a0342c012141e91300e4006001e4000c078080205401d130451960101002040601030151403040128 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 85018337 1250 85017087 85017089
    0x712021014010f050907081602031903020c010b0a052d030610030b0105010906090b031803032d07140c030c010507050a0305070305060310020d021603050304020a0e0105010e0d050c0a 80
    0x101c41450034552601000420480441d000306004601000402000740e0700043c0b41358226921042c00da01c08520118220701713501682c5103880e100702503500d03a42c00c2c40d40e05070090140f032070400c002089441c0266041000b200b07064407580350452444240301d0864001d803070750b0581c0d80d0b418004000d603030659240000c1c244013045604c040c0348980f910007403040c0200c603d09540507140a003808802c00782001c0c000360030306046101e0107020b000d0000c00100078440081d0040d400400400450f51241003910b52005000c265210520403003000e402071000c49609035038080d00441180d220f0300e06201042c050954660b02c1641e01048500c0108140802181c0900c280e6208203c44e5272016124990750300300900b81d800c003414401c101424001404a182d0b00456040c54003c07405100603035410720582641c0281c029001800300b041a040180007d0603000001140b08510864804000740e4032030407a007901510030300501c0e000481180c540b04081c02d0150190200c6402001114601103d00300050850805 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 85019587 1250 85018337 85018361
    0x222090b0f040b070804030e09130c0f090f0204120224040305010902150a09140114040806010f0803030702030901031e0c0e040e070815040c050904061b1407120210 72
    0xe008200014440c8401903190458007a00c1d212000d420240c600038001405823035920320403940032001c038000e04203946c0e014044581c400312162885035100f04115110f02c1d284148103d0900b401e00c0703804054058402c03103050341d1a0f4003c0481464075902400240c7c00d081d04101140382c0c0d541800c56080b4850005000150721a0700003241e0302410b44140400b0003024030031401020402c0c003c00f103503075400120007001d03900380a80c4215030801103001212286413214040340700f500000340206050300c010420b581039820034030035060340b665120071075a130341e110803a890302c0160810f000701e00241d03101381c200484400390a8852906a12000e603620304441c1040341c606c0201e84c0101c0c5d0709260741050b014080c1100c0a180181c0101450300080b40d84890051a000403000100030005042180c40300b021006418054007526540c0340c52f10b0b0000040444642d032800c640d1900c210411080d101d80c40b4980d0561101031102d0400020385d82d03202d81c2140a0500c0410350242c10821800740c0c62500c0303083ca410103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 85020837 1250 85019587 85019611
    0x1021b0a050d05070b06042004080a0c0b030403080c090409080c15010905011d040203150429010b1c0b1507200904150608030d0903080901090222090b 66
    0x3000e14000780b800c006080c410080c44002e00a44020030007200200c0c1d403056050710046052034480c0c102c48499451821810801100404e0201d440c400c00600841a54480d0001035521900e4541402650108883c001c0000b92036900048040030920054003460401402c00701c3c0c241410355401d001500150004419a808040c0c00b118070b011160b1814010500081c00f00101d50502c22807411405415502411050200c0b000c07508540f410014801c101d50b4205a03030f0340d20b05182c6000c550640c1000401d842c29090500100400c609105505048800c5805205c0c0741181c021f89503103a00c01c0030a90304580316aa00c96200d8140c44240c406515041700c945860b41c4c0700712900d06404039075411492003004074480715a50089031a909649034101d0703048503200e00881000c000300c030040c22440d04082460700000c96150310b4004960447ca81c158070a4540a0150f035030704404508075210100080c0d400360f0116601c0414440c0761000500c00345403407a0108400141d031701c9000d40d5004c16112079004c45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 85022087 1250 85020837 85020853
    0x408011a040b0d0209060f0a0308280203030108150402031c030506030f03070c0302210f150105030c130510080303041a07080408030f130204050a050103051c1d0301021b 74
    0x4a801d02c9072000075182100c90310708480543c0c0100d0055500101100d00070102e00c040240c0c9a0340b03502c00f06004560001d00f1596505450340318100b4504100282c011321119059040e03031050021090700d058840e0880102100c101c0504001034515014005a170180207941b08103448000046200d20008070300e072004a01c80c1401e1050500d060040c03100d1140c5504188180f0380040c014004010881e078044030401c0b03048034071248a40407582005d4000e0301c40d2041c1c0460500400001c03403110900c400325121040c860380d9401c18151034407103944003240c1c4000511402d091440813640001d4000144000620380d043d200c001280c9180e1013900c040c0e40d00c09002041d801541e284100031076000556141911007400c0940c3c40c0d02890102801d6400300360000400180708490300c1401d14181c82d0014014040b03402d0090340700000340420701051703409000b0b015940ea0145a40710402c200000542d0342c028181d043e006c00320210070103d91800d030785550200803061401e4100002e0051018214000e06450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 85023337 1250 85022087 85022089
    0xc060207060912030e0309040b030106050907090311092203030b0a06080a0e28051002030c13062a060605060c0f0d0c021f02070902040b0904050a0212060d03050408011a 74
    0x40507014090f401058140f13000800d41070313408015a401020b0594001c04e10107024000240900784603041a500b12016000300900294003c5004048074000c51514600381c44010620840c508c08880324900c0780910f26200b14040404500d80619034041d180000d4401100030002e83c03125000d5200c140020b03941380511403070181c144540c0381e05190382401810110307100300302c2c1462507004400d0034464501811101e814440144825078100c0d40d04142150b0782d01e007000e4102c035540c02c84075041c84c4049034610086002801250140d071150030000d07040c0398054070452800380800640c01700b11901b035102c5500182c1e98039610080e002d03000c0648090000825502c3c9aa4034009583c01d4010402603503900510140c0c40300d012003840300d45080901580c40614000507840c0c41c0c51540540f0710f41d440020700290194051024010448080f00c0a00058071f07400011816401007841402018258802040c41441c00005000c0d603240310781001d9041a0340e9112060840d0002ca2b158440c82ca024034458200d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 85024587 1250 85023337 85023353
    0x6031e060303070f0305210a0903030c0c020f1509040606170f0705090d0302190302030c07050103090b0a02071412030403030b1f05091c0503090103060609030812070c0602070609 78
    0x44030303106800450404010384c88542c00001349900280600400107141c0c9528403000552a01081d00c1c485460106e00701203518000500c040c2c4015400245016000d003503c510912841c4a0150000c2420700c100403c4020040019500400f07228950b81c20402c0c02c4c00307034445001d154001c103c2601c07401c5202101c000131105200006281180e40288002040906030700441a02c02c44001a152121303a00a60700d016070ac1e00c0200c60000942d4030580d0f0300f100400d03074004001c110f148024000e81d402c2e1552440103505480009000500c00e0b000400000c1954216501034682c003409070700061200500180d0050404044013103481003040d00000300814141c06014a002001090354020440a8020312408c41203a0803402401005000103d1542e280d548a0005c0d0810031600d5860540d04040d141040d40c95000c03545c0540880c7c00c0100c00208240942c04a40480e50854841d518228810803050400c180040402c02030010014450b00415198400b4250340c502c030765400104c1034851b0904600c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 85025837 1250 85024587 85024591
    0x20919050c03041a0c090301050f0105011d0604050d061509050405010c0f1b02040605190314060c070b0916090b010801050f1008130b161d0d1e0206031e 67
    0x56a060100b0a0100080ca440010903000c2084110041c1ca500d40341003419691060384011a415030811302030010b038280402d1128101e40003600c9131400148083c52031846903d112445540c4000248003c00883c24204204859a481400001101600310410983c8080c1582107005443c0c3d8a008202c10004248915400740c0302604080d07203010101d550081c00f07210505000000e041240c03802d0030864840350001d0000c0c2800806511034440c0154400e124000d103840159080e0710030aa0444460001189c041d006201040c0c04a00d4101a501d68501c01c0001078100c40380347c40b500f1025140c4030b03460314103480685080c603408510180007030001450464107070040c510074401b40c3c1000c800742d80c1c0d080746000da0328602c1c02c00404039590001c4000e508044003070064119100101000501000b04039007003c0e24009403200140c01c0412440101032407500107040741c00c07075910894030010850400c46e440d84006d90f8081c2481c0d0710902d9001c120290000d4401546034440c62000c0ca001a0403150025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 85027087 1250 85025837 85025851
    0x10f03060b01020c060a030b0d06020d020a1e09030305070309090f1e060e150409050a0309050a0b040806010e0a09060603031211030c0415200606010e01020609060f090a02091905 78
    0x80c4130b000c00002001ca204484021041c983e4507034002425494150440f00715582200c2c08644401c82030700303c00040d511940b9034a002a0003d038001c0400c03044a410340008844c81da48002c41d60707003159016102548000341c00d50502001601c006800c0303140340901c90700c00010f80404640d003600d907507005481002003e01ca058072404d1550910810340d401c0e207216400714001504d4141d10b05144041340003810320074406840390090050000615030040b0301c02d411100152100002c8503500c43c440b40c221b000c4d500070340182d80c02c10740041003450202d503441900b202000100180f03c403555a10001183ca1941c0224017083d0002d201e018403410606c62255484650300c5881d1a62901d0811311007140b1450103a410643c1601140980d4a4464100b821450132040c60b1181c2031100c0c10503066680c501115058001800c0e60400c1071954408200c00d030050b10b00c40020010380d1100d000ca411183d03001070074410640b2803c1d0701403015036200c826040c01901d95409038013054801c0320345102522401041c00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 85028337 1250 85027087 85027093
    0x12010203090d031a03032106030609100c030e03030403020f060c040f12080f03011205010b0d08120c1917060406150c1b08010b040b0a1a0c03040905010f03060b0102 72
    0x100310510003094004a0000c0b5160000308401c01d040d100c0040d1301004480c60b0144004a002c0200440c2c1c9101e445149200003400134503035441004056031100104c0d0440c846412010742c0154071001500071190030b490718100403d0401d400460f00c0d00e960012941580182e00080011802d09010b11001e900301074024402c500d002c3c28209514004400c5100360010100d60741e42407000c0c008008286c0c0c80320700e021441030707580c0d503503071000099803205080055800354030f001000016803900401034800c0c0c90340115418188840c400c40401c007440c00420b880c45a1104204080322401451088601d81d90070341c80364000b1660705031441c40316900040425018514060091103c4840e5001541e011a258580003549450503d010700000a140d046183e2105100001044982c0190440780300c0c62829a000c00880b070700407041015640d824072501080c0740d0070592100203c10300d040105089640501180d14040e6100c80380422101301740c0c0050203080c40d0340f00030310030042c15010700039007404240f0007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 85029587 1250 85028337 85028341
    0x1903061e170f010c1d01020d1215050306100f0f0806010b0a0e060d1b1d0d06021b010506030d0206100611100f0c090b2a03040e04050c12010203 63
    0x24940d0048107030003a5841e034400e000c4404a252030400c6a0b98000510300028840340184140c090100d104240318400d240700d203c074151046510004804658808550301c0d1900d040b40041084028209452100c900c0c01c0400d501152a440400c200c9000f8415203d103d4112031902c40c80a04024558026646c0140342090810980708001031070382c156004003410680e80d1101e0322080c7e422002480030305802c4400400c0180107000b551f8000c145c0844184051a00f08902d040c0480b6074507101100d0700c0c5000310040144040e81421034442c844036104100040c40d0101d003c048550242c08234008070460b0703448030b042020300e050038015201069103034001490079050000c0f160030811141c4c0200d1080084100c052140b62208002c1c0751450881c8900800c041a206000000070385203000882c0003242d4003260000c2d0340710611342115824101d90082135298860115500f58140c03201e903034484288014000890303602420744078140110303c1007000308940e14144c0e080c801c075000412801d074800d906c140300f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 85030837 1250 85029587 85029629
    0x2011215090c140a081f03033f051003060203090604030f11060112021c0c0905070507030c0803040206090a14100302031e07210f062c0606040b190306 66
    0x420744d141c09995040c07180841d9144034102884060340c2c13010540d1210303454000001c0c07540015026005401f2081d590840001216020008080115844c90340c410340d00c60100c40c074a150390000c0d4203c2800d1001c074822035500c4d11540d090b0f070402c0c0c2d00c1c510300740c000000780020980c0010707410b90441c00905041310501d0000c2c02c0d085d01d07a041485035151078000240b140086503119905100c455507021252214002141850943c0c1140e9015600ba05417500020a09441c050000e0303e00c429410341c0c504036180040e603a10703511a00050000c0b030f00000c05211b05822135032800031450140c6030b0384080c1340c10409084200006017a04021050038180304001344035881c005501000351403092003060004640b5104000c5501d4880c041c0c000c40c4040c0340b541c04041ea207485421820f40740340910801c2c04200c3d12070044118009015040e45007002c80054404260940201025480701008100302d0415070748800c000b6541d442000340510a080010728503090b19010303c209d1020305481c180d07403213403180d20803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 85032087 1250 85030837 85030877
    0x302090f040612080d020405060c0a0501110c0703030e03011128030b1003090222061a030108071211040501030807060e060402132403030e1203030f01030f02011215090c 74
    0x50f0024105000000344d1000518880d01154002c21014105590b030f254425909030f261442c11380101d0b069401c0012031081c400542c025521700341074120190000c01d1440c0e5040d202c2d04820001542c01d07540f150a1000d03503950038809000b565800d032800b2105140d0007400030703010014040c0362a081c1498500e5400c0c29841c0c0142c4c040b5440c00d2400c000841c100c80f80001030703072004185582c464800800140c42003040440c3c00c403400b240c000b20081080019491042e401d1070009010302000d96112000402600303480b24030f00303003035540a4407013180014540300202b003c1e10400d03001510f11503030001d00c45080040030300c0b0f120a1040c0d0a006000103040039400151181441c40c10b03403090f180c030b40b14402c6600d80d0a40310025034a00c01c410781c010240d62840c01521106007000f1440c4500d030320403004800c081001c000c40e8440c01443d008403940780e003540d40d51031070884030400c240e04101c4800d08070400361032240328003800000101c01c2580d0403460144408141c03500401030008001802000746a501d5400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 85033337 1250 85032087 85032119
    0x40c03020d0614010803041a0304050d03110705060f0123031f0605131a01020d0c02010c06020d020310030c06030b01020c0909010b030a030c03090905010b030402040c030b04020a0302090f0406 84
    0x4036810085105603041881c003070100f8100d100e403008401d9000003148a000402001122081204a0401c00a401c40042140000c6034050081d402000c144281e0034440d074801c00d80c03412041c00882c00c100c2c450b20741509e003072021907410310070220500040c0a0344010f40c05807040c4041c01540c0541c10311410000c04d40310144000d03041c40120b10520301c440b050945070048005440c7c0900303043d80303c50350044000c3c0900f034808001c2a89c03142d40107140c3c506500c0030403202025882503ea80c0e109400325801110400c42d880010f0b41d103240e00b0b0020302a01c403001e000950080c000c0305144209a800c5082001d00480150b0220302450301e051040c450710b907000b040c0c40000000490350050183d03100a6094050030740005016850f004030344099081540103801442940d020b940c6040006032122a441700b154000e004404903090244002030040c9851b42108001c01031920b008151030180b80b01140a0307030044020800440e03000b085412032410071900690706000304072024003030240380c40000c00302c01e80d031 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 85034587 1250 85033337 85033339
    0xa060506012003180f12070302040f02070803070c0203030f1611010504081b03010e030c0723011407030e03011109040f0501260703050601031109090105160c0c0f03030f090e040c0302 80
    0x3513000c141e903103666116448855a0f0000c0c06100400c2240d4500c1e0b41c031201c607400201d1059180410101035090385109443c04154400e030100d15545413400140c55003509944120b0749440304202c07002c0e2205901002e40f00c50002203c100c0450585490201030107540c075078180d030411105001c20401140002401c64001c00c0c4c01c4561041000360ba40400d016080c0001200c0c0c90303200000321a1070f505070000703003201140c00240f44001440740b8400000d0000d060304600600007080201641215480d10300107001071407090a00601103e4004007003401d4400250414655400201e00d401090415024036002001d0581d41040310758184425424200451100e114a01c680081d868401d50f008000c010017a6400004540583da9039144c07081004024031020360155800d04046803101f80140200340c081c0110312222410440d005c0e030120355108811500361407410b04540300003009803d080c44007000e140a580c41c0d80d0040748900e00a000e81c40643d00c410010700601d01000086141512030b030b001d80754 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 85035837 1250 85034587 85034617
    0x31302010203040b0301060504080601060207062109021801080d03050906040f03050d021303020a050303090a060509040b06070501050a0e0601031101140906130f050f0109030b07020f0a060506012003 87
    0x406000407840c0d4001c640103d070503d88000000301e4190b8000000c0c0c000c5070b0038003085030056a240e600884e100c40c51380c400c810218013205042000c1c03820351401059000f00002d800160900749030001515144855000e804d070b03441c41001030046080500c0002c004484bc0d05041c04a818079514191790792030010009490401455845030405104400305e6050304500034042d919210320b04000085054a844100c0c41075860300000655804c01006840380a01c0c020414010145002c0050740c25030b000c3c039441c582c0540d03200300b4000c040d5241c0018061840c06600006060b1401000803404c4510036800d240c02a403040004000090b603400ca10790b040c0e14280381110411a05d03013040e041074094640180d5200202040340c5080d14a440b8400c8120703a00095400c0e1000e54400c2032000c0b0752001c25075940004c000c40002d2010840146440f500b108083c41101c1030003491240b050301f024030402c4116001615101444071969014030713402e07004980d408400910886008050303a90b440b80b01c061482c459 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 85037087 1250 85035837 85035871
    0x20a05120c0607060c0801061106060904061b1808070e0109020a020a02090702030c06070e0102120c10050103080706060e060105070609140f0102070303050a05071b062a12090803 78
    0x7445441100381001e0240da480351124035010001d00031020022000468000000500718481c1d55003211444040014066940b41c0206100c042c075801081602d0041d02d4202e40c020942994100b40841b02d0243da60351101e01055010180c40d0b070741c0d60b001c40400c4d8417a100c1404450900c0c0c2da154111604140e00503a1400000c500380d0400440c4140654400e5401c3e04101049070048020304038881001d0584860365207158040e10040c1f8658412401a44460036910700e9009a4005140c1c1482c00c40840301c8802030b9202103016200240c108a501039000302c1d00404000550080001800c03820802500900d401c000080c0140151030010f00003e0701d0b081c501091111184007030070081840d1080d01c2d007001091000d05d010f50302c000300032000249086c0000319584501c0c420719009002c01c2e92850070003004071402880d0311a04c00e0003602c005a0b1400038078a00100840e1482c201407c0112403402446034400123091b807024075515400c000d0070511030000050802045903032041204094400030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 85038337 1250 85037087 85037119
    0xb040204032a0f0b030603100e1c050403060c030e0d0201060e0712150902090307090b090406020a0203040b0c01090213141b040810090606150c030e01030f0912120603020a05 76
    0x1800e400c3c0c0c8480303504110f024010440042c0701000354071030711040c0d088680030902026081d04035808801c000406030001811080b050b0000305030b15090720020301d0710f2810031f901d81d1640c00c1114030381e440d490080395a503030160440e8501400003a03101c10442c0000c01845151140b180c1002d00010070744410000d00500240c12098698049840507030b50020003070b4059114112500294005007409200c0d21490400107044d064a0081862030b04014004011a440307981d1218080d4000f05900c0c815400240804500c5680740f901a180b20294a400820141480d0040c07000007100d6101940c90035040c81882540d0300c25040c00c16401180510301c80c80d080d8014000c52025006039040003114bc0100f0040312149645500700c3c5003450300402c41001100e036a500c4401d00c42e070010440101247c400c0c03184a020900071300c0c595000b00418100440e94440c100d580c4012aa074a12044400174100384202126070b034000001c41418407604010850581113800203080c0400f184a02071091036481519422 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 85039587 1250 85038337 85038413
    0xb090f0c04052d071202070804180b0d0c0e1623090d11040c0e0907121401090f0e03030702070302040209030118050d140909010303030b0d080a02010c030b04020403 72
    0xe41181c1c0000c0d00d02c0c1c0f03091041400c080b400c252890800034184140010359885030b8401c80d0291a48503e4140c0b40c1490601d80000d00750310504401c150303a0345c0d810782141940340c0d08100e40c1d2040c41010001016414070100d164007090151401a0300c184541e5140185a0400582d251400c01602c00740c64406c0d0079920f8070201c1c4555003000360032224442884c410071285051440c0b2104088900b803000351300001d02290150195480242d01c0151500452038607405401c0f411028008040003185160400708401c00d80344013a84000802542c035015030425241c20b00c10002c4100000c000f07146075050240e030080d80c80d81c0c00d01000c0d2046900194144580e03500354001d1901d00c007420501e03404240c0c2070901c2625089590b03804004100100280c0e21000104002c489038620000c144003042d0342140c5045000303040c5a032210f5040814000c014002c070710003001600102c00c5a5001240da5220460001c5c16504d4a09515028034018402440002c00c00c2502d82700782403080500500700909602c2c50a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 85040837 1250 85039587 85039621
    0x30c1d041d0313120c0e220b060306060f03071e150509010f08040b0f0705071407140909101104030c090c1b1101030f02071a040b090f0c0405 62
    0x6401582600e002080800640691401e040e1060000f40d620b59001c0000c60903144000c3c0038451101091101401c0c00005a070003050712980305240010200710f504031245d188505440074884031003042001e240c200002c1d5030110301030340d004e8a8100001d0110f0340e5404a80900c1031217050302050083c0038404503ca800040004019542c1c115525150207407a03070303000350300050000c0c41d03c815100969004952050040d948140701c19850f54600c2c1503000400005001401004000c02404000c01c41c1480f410301c40400c1c8030050020701d8074001c5611041001e280b1842d0188490004021140c1004205c00454010101c00405c0001d0492219102d80c4074030340000b000b115215101294018280c2c1c03080c0b00191480d180c003030b0740c8080312420465002035002d00030604000c11300c0e042c1036948a80c200a02118410a01600b0010b043da0396001c9000d0040c01000002034010801c011301500024558101490340098442131400d41d2400b52200b500038070541c001c0d512080030500040103040464 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 85042087 1250 85040837 85040861
    0x1503121803070b090103060b0a1b02130903030b03060702070b031f1d01030614090c010e0f0406032f03030301030308070c0803090d022503031224080d030c1d04 70
    0x184007a4a0740c0380c40581350000351002c0d000910709140810f401360040c04685000501303459003040203949030008441c55414400898018a035120520100b60543c010780c0794603031180c0c0340407941240b1f09040c903207010001021070381154010030742040b100b0300e01c608030b0b03800200601250329103007501c1c007400c0702035640d40e4803400125106038003000d041c9108140440c16203100752800e0080350880380c542c1903d40c800355241906600074056496180d80a003080c0c040341071018054000c1c90745120b0006040380d203541c2c016a204e06000310780c41407c0441c00d00e2881c1c5180000c4104d45800510f0000c03a681c0d00050200600303200ea4400420910390180605901030b640c030100050360392902602660b2504507440c0000090700c100302200c01c0c0c0e01c030060032808040d01c035007041c950024a191070440f0b02c90180320750130015541d158110f01d407494034070fa15100869008504494042e14000f2218a0800f007841100105490256003020643e4013808429204810b0201c0c1c0400e1b1040c2c500080c01000c40e5212a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 85043337 1250 85042087 85042093
    0x20712020616022706090402060904050709150f031112040803150301020318010c0801060203031501031b0f02071703040902091c060b03070501050f0d0507090909050a02091503121803 80
    0xc00c03815080c00c000036903460700c04c00110099448841c140b100c05101a00c000303521410030b0000e013400b400c065110742da01046910701100141ea031a00351500c803000441d040000900100c410481541d05805001100c17192044c08601e04100c08149400e9814094002008131000001007141801001c01419123850010000c66980c1030410200790000915404d4036465400c21a5000c4407a009404680c105c40e2550065803030b5a41e4041c54801d00088800c0f8036060540d102241030808801c981c40c500b20090316100c020000c0749202c1c020340360004c00e40c8241d81000d40a84c6c621240c850210545c0e00311251400050b0f19560340c01c00082040c840c2d00c1603030049010800136a400e11205400003183c02d0015000d65200540713071001101c0034415440c07184a0f01ca010000c0103000303007266001d50780c071111928002c0707886511058000e00b0307180c0044003541c3c00d50185c41a50150300c0d0404400740c1041528140401500d203900c0400e4461090410001d1500c6000c29010303e82c0702440a4015042030080507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 85044587 1250 85043337 85043359
    0x1030201180f0e1b0702030a03030e0708060a020d060f031113090b04050a03090603090203060609040c03080d020306130204030b0a090c081f0f050601140307021006091b02071202061602 81
    0x50f144480384220380950061031407240016075000c21070119454560003a024000c1c0b03103030648080c0d0103400d40c1412040319114220002400700030501c4110f01178484040c015070f03125001c02e1581c0c00c1d6030407030304008145280707004100006090080340c8260148195103030703c143d070b6000302604001e00c6402c00c05020004503c0400081100100d41e55038001d00c42d8451030003c988502044013141c80f1440000d405a105030302081c0f45251403446194410303c11851400000d45070f80d02c00c210350704225400901240c000c03090180a00d031224040c41600e07441344046080c207180d610380e07000740b0b64090090340c01c06503074003290010300c241a00d80c54042c0a04508031080c00304050080e08100b4218075103508081d00d01001654109054094280240700503550701012921800030181150310141c0341d803042d44146048042c0325034a50140c9401001800e41c001140828021140685500c3c600c140701190810300e018032500d4444034880c088150140d03040764548040500c060800031300014041d60201e0701c200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 85045837 1250 85044587 85044599
    0x230715080705090904061530050a050d170c03070507030e0301060503010c0903050601091104051c020409030306170109051f0204051e0a091a01030c021006080c030d0905060301030201180f 82
    0x408000ea001001d0080c0b0710b0341e0303075020105902d8911a0b41c130540da012900d41708c01d6208140812007507103018030140c80d6008000d0f602c05190601c241c001d40041011a849500e4444400042c0d6034440700300300c401c61a5260181c0d00a005200b1043d0040601030443c500e00413685003584598040c050182c000c10640c001d810f030140881e07004d4031044840d032103140004a100801c9005686030101e020038114105030414040040e00300c600d400184084801c80032000140e5030318000e01c21514060f80780003c00c2401c004180400e03031081403042d00d517681071084140c0000d1000039030311203a0303440342d1505105640c0e202d9000d02900c9150b00055000d100070b10070700c5c500407041c0c21000c60301000720b400e03800c6180c1e603540c040159289071b01094248c5450700785030390b0340754002d0300110b5102d0650310607a001c1c40c00c0304003050308640898021812550081c03500401904081111030340d2203000307042c030134100d41c40d0500098035407205001c02410807000c3c400d50424a03540008070f0025146600c40510383d103444103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 85047087 1250 85045837 85045841
    0x6040501061401030207020a060c030c0b16030c0516021905031e0f160b0702010c020402070606080d1b0807030212121e0c03061905030a23071508070509090406 70
    0x4080c0c203007400341425a600c030b990700a1003110450360b406000c00c3c20051401106540d10150b0303140a41c00d02003841010f2000844d15500e00348509001040c95080061024008044584d1a11050b0520004100140c588051448490f0780258122800c0c21800c118030350140004006034080780d05403050001170118040d028254038400b500302c0b0704031010031500d180e0007079940d500121014160134021030203104180410008001150041c10f00d04042c1d041540402c08aa101503029110320350756800030301003100d040c04521040526454095441855914202c41c0b0011064005250b40d02c0043c030082018000e0000d4003420b56040592600d071080600c4045907560200c0c3d405840c101d014400c085480110410a13001e05800102c41e0f0440d0349072420310000805000301c0d5554219120f00c001103941d004c0240b255480e11500d8505101c41443c410900042040d642c15485078101c442d05100340500038498035030204580c07904480e240c65a00064070240704070701c0c80c150447e0080b402c101c01c0c80016 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 85048337 1250 85047087 85047089
    0x6270606030b070807050304062408030904150f06030f090b0403080106080903030f01062001050a090311060603030906130905040b061921080d06030f1202010218010305180604050106 80
    0x2070b041c41c041a610004100e61070744040395401d02081c01407012401140859008902607000005c10047c1080c2c200b6606950b408264828220f075440000c2d10302a81c2000d004203502280c6800c1110030341800e24a444004420901600341010ba8900100400703c503140c102c131070704030f0b0080100a10750405e0b050041104400f40a000c0c0401c1150020a042040020441f403207490401c0c4004002d90a102044a080c074001a02c080e01e01f146880e602c004d0340080c420540140c01c1400009480c14107490702400b56010488200c515801220810680d034501200300c51030040101d6038a55140d0304d00041e9600e460458000c071510314a48010007080040d006400c1d0b00510341180c1c00e040f944000780c1102240520341c014400c600c0c91081038a0000403503002000e54051107503c040d410b280c03410200030221411340d07005869035a0011140000e011200b88410118491031000b5454104d0440c0e00d50103107900b4500a1741090b59a1000460b82c46030700100600c00ca01a0f01565090b0500b814154040e21031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 85049587 1250 85048337 85048343
    0x8030f011a0d091103010c0206060a05120a030305060d0b01060c1403090a0605090d080c16060f0e0904080c10050a050a0c14180d050a050705040603030c0627060603 72
    0x49440042400c00c81104403226054041c5001454100082c4022001d08188a030442e6a250007080200781641e0070b00a80380c00014942c018042e078600030081101a24039035008502842d9413048d4155442000300f400060b9a406003000301c1c203a00d0b510041205144070805c05000c0149100020036242c0d480b02c00604014050824085c14001a10b8010740300c2c811404810703440800740e40308010f9140602d01030000d42c00024a000e0004030b0a807503214440d03000035041c0308950094140e00b210074000034443e10203071165140c000d029508803040035001c0115207081d1841403481d0000241001711410840700205289425a20a502c0c14005000a0305054544180c11400e08000409014041c81009020076050359001c1440007104131001d05c0c0d510085440c10128910034010445881c1c0a51926045105030010b100102c04c0341003503803c1001c01c0e000203104034103040c4108042980041c490003025000180010302082c045600301c200c01e0b400307101003d11040c1018030000d00510ba4482030440b80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 85050837 1250 85049587 85049611
    0x403031706030a0b0703020f1318020310060513090f05040b013501061203050c01150b090f04060338130b070c020a090603061404150b0f09040803 64
    0x2503203495540c089803441c0d0154000012807000c00e50300c50742190009850f040044c54804400044400740d80101b02100800050120130080a683d17420308103a01c400c038040443c11410700c5840e81c12580621311545082010124818841141c1d10710000001c01d100a420000b401300c68000c82c014020803641035600030b880500001d820307030041034107002110820811042e140140c0e12100644c2504181718036680d941c401002c940380c2c0d01ca802d80a0f915029443d400d8450000c181000d082d1442021008040071540d8010455004c0040c01d450340001c04842c204906860714000c180180030940c40030b0103d8080b0307594141e680c07100814640e0300c0b00c00d60004010072000c54401540284c400d86104194030f00b03481c10768002c45c0c09851290340000d01c52910554047e015000a00181d485800c9042c003140c0e11001001041854454050001c2d9103d42d641e9907840c1503102c1c01200010034011a01c041c0e00d8160921255070ba5514600341007500070018403441c10181040e101681007281d118404003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 85052087 1250 85050837 85050857
    0x4050a05060909070303050409020a0302070503030c04030506130218040302160f090b01080f130213020a020d030c030e070510020c03010608031e0313021005070204050a05071409240f0f040303 84
    0x200111300d880c1980c2c0c06072075944c42c013850841031030000d511461010040590910100380024030503c021401440c624640c680c8840c00e50a080c1c0c100f62024001c00750219442014000503241e010070ba940c00d0604011500240d07031241410ba05122580c00c510020603420040032900c108901007030401c0d60540882048010310550054840350002d4408030610701d441000596400483c44507100350710700c040c1519415400d0401c1100983e00314443c00c201581246101d420440c0e4184500585000203103800d01070a196401415229111805450b000d89465414045418000c010b02c04020902600802c02d55548400c010707166040303800940804460a103c50034403403102c41c140c13402501117110503810440c4950800000a0510041005100c020b211050142ea00ca106a612500d02d46802051038a00444c00408402006440300c101c0c8005102c0c01220703032540c0c200300d08483c1c0e48121540d08460b0407500304e6030304d00400000300c2d181c0b03400140d21004900c000c005001228425207402c4420 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 85053337 1250 85052087 85052101
    0xa030c09090e060606070303020717071523060a0807120605090d080703020d090f060f0506040501120206070212120717040b0d181b18020c0307170904050a050609 71
    0x82c9084040e80c80c015030203038011820700c0c542540101403080c803030f040062624000382e03280c0504800d403103221001e0400200d018410302000e1160542100b00c40c0d00c0402903610540505859807101c2c0c03003c0d00b940c2d80d0000000320a91584010031003d400e110040b644259a01d09000000011510045481d20f040c0383c046060380c0b0300051080f0612000b40c507101415980d40c0011030094102c03481e80f00c2ca181e141c03456038000c54002c2000c0d0000318041c1202003400103860b0540e006643c3c000c0c010900035441e05004000c481485035460440c181c0c125005503442e151800040e048105034900d40c8440c0c05120000c40321081c80600421805200301c1c00034201420038511a0240d0040b4031035501d011004002003000050650300150f8070f12032001300a05650419280c4070010340949075045001c0151400074042c41070001d460015a044118007540b90416001c0810786070b006140f07009012590645412940941a8003620500702020b40104103074a0041d40c001c001c3c10341515080e000d850310308081801 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 85054587 1250 85053337 85053341
    0x3061303020c06030603060f04470c090103021605071401090806010e011205100c02030c072c0c0c0105070906030e160b0c0304030507030606080601050a080601060509060f0a030c0909 80
    0x3c100001401f82080f80d03201c155034a0140b000600c100d802c008085980070300c2402c203403036048020072245481c90301250400c144c2d4a42204050390013060074110020020301d40301020440b00c040e0002e180158a03895071001002c0030303520040004000380180321022425034000c0e014007041007000d0703072440303045a0795040c81615a0f50038041c25140040a60041c82007424100c5400c0e09580304a040b603000344ea220218800315040c0d8241c030f1005810008060720f00040420004008c0c104019501120016900c04181810846508500c1d4214444000344030b2001240540f464841c401000703002501d4040801414410300e4014080400c5c900100084160400640b02910140300c0e020099030b907081042c0030400343c0001c03840610074441040080009001072103a01c0081d84100d001068840c1404003da00306081608801c1c0a140301c8401003095410002c2e00c1811140c150400703030ba403800c411000c5481d61240316500c0540781000100c2c248103d500d54030200005069070750301c1c402540c55142c0380c3c007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 85055837 1250 85054587 85054591
    0x2e260f01200315010507020f040c090602060108151504110d090b01120b0402010806031c030510170a060e01020d020c0606030d0302181e04060e0702121c020a03090203061303020c0603 80
    0xd4483c00c0c194500381c294016001802214001019100c1142e641c10000d0309031800460110300041045508004090b0104103003805807003e4000b0340b050680b15180c1c10407400c00240401100f90864280003400e403504da21541c4a4030f500b040c125078400710740d04000060000403d0849003200c0d82000051204900d8024041a650005029651752034076001101c080301c003d025075905005102d2560105850240240d030301c07650340c2d2004600d1749807111528608801d02d070700a2100160320454015680008070354107003003c1d409880040d204505103603641c0280a2982114100c610005d2814104c0100240c52489400100c3c00c64140b8000307464124240d000d8078002d10001c1c8000010a000c0f45889071515008840b100720f0302050640e26400101510701c0e5070f02c554855584807003885803140c2c1c140600d4401c140d40c0d03040f051500b40742d0110340d60707a805a0b0540e440071a601141c0c3e8108a0322a4002981e629001811118141800145100e0034a0800b9048026215900741884207040c6101568 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 85057087 1250 85055837 85055851
    0x925050901030305030a0e06130506010909020603070804081917070216050f01031103040f031106190e01020c070f14090105060d05190c03052e260f012003 68
    0x24030380d00c0c69a0540b40e03900b001d0140000e460b200c6451020030342c170400031548100700c02094a051002c0c039051080c181501038004070031043c107081104015840e04002c80c8d8020b502c5181c03801117603407241444003990044c1c0b08181c00d0072002c46c2001b080c0d1580184000754081d54540c13a094141c031410010f07680d91141000c05c000004501030100903905d0144065506c0d850107050114641d00b200440400d1030b4001c480032155142003041c075400b403650290070b420b50080b0650050a0b5410203980303140a11030303440071107404c558031200b84000105003901510600d14401044582d403d03107402c0c890f41030440d280180780c4000e41c10103c030411454241c000d58101d96000e800545000d0b01c480660000c1d240080000d2000b042c07071103000c000340c40703a1702c9005048001d40d54001810f09283d10003180d0280000300e03050b40c11117a0803a0000041c1c80d000040c04650f850b908290b10f0140010305a0001c6012241c1c1d42c00728007074480414405103042d0400003111a5048205521544d80d20043c601c42c0070542e400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 85058337 1250 85057087 85057099
    0xd0501060f0c2316090c05040605090d061805060106120c1205040204020405060d0207060b040e030313051f020301090b0301020403050303011e17010c080901020c0a020d0c0b03092505 80
    0x2c40800d200c002e200c466040f62001c007044034002000d4042c03401c01c108404150014841c0801c200301203807840390050031111132034602d10f01483e00000a080340125050076114850381540401042a1903011683c0021108030904003c043d508180352034031804d114150110316022183c05140700706118031f26905050352510421b80344440000070040500400483e0031907030802c008503180d41c3d010081c10303002c402240056035951580c9001000d542c0001102801141444036500e909100070055030351104440320034040d8203102c0e051141c81c00040c003180d400d01805590390000c00782000e400640c140ca22014040c0500c2c0051400e040c200e200e180710103001d9410901c010301440e41c2202d0f244c5400e451030b80302040da507502e43c41c0041c0f401e4400c00358440169503480d20b0304c00454000da20070741e01240200003141040e507003110b415102c903a4050000e10400d00524120100300d084511040540a030791400c549a1408c91801a501c000e6800140c85001e514140c90702801020049041540c00c00f8100e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 85059587 1250 85058337 85058357
    0x901050c0703052101031214040e0f091002030702030d06050a0b07081b030a110c01090305030d0c0c06060305060103050610030c05040b011209030f0914030604020f1f050d0501060f 79
    0x1200e140e082000d0f130000c00c2c0340c1000420342d42854000d259010318000c0c644082c42040301040a00414508465407a604405100c20002d07a400c40d410164000d02204161605980343d10310301c3d04054031920940c12461000c818841e110b0b5001029041c5100300c11002c0108a4640082050720441e500c240d0420182c10828000000d5008001e80132441c0c5440c2c01c0d464080060701c01c0c03402c680040c0c84c203d0001e8034801000491010811803501c28030001c1c240210400e0031500e64584030b208002d42c50540d00d072030301d00d525600f034801c00840e04c45a41004c1c040026030345034a09a9240c080a10058030684034550104041180001c1c0130021070f9484420007100754646011300014051070741d005414000c1050340611340656900601810b03511a5a6a00490044000241c016000e80d00050180b0440007000d001716180082e54617040f5404441400c285c1c50b25074009090100d003040141240c600074000142e400c0e41000103082105649032003440580c1e29420101c81082990f9286400a460088 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 85060837 1250 85059587 85059593
    0xd0e0f011b050f03072a171e0705090105090f07031a060d0e01060b0403030207030609020f030a030905010305070c0f030804080c0f07030218010302060409020d0902130c03050901050c07 81
    0x84481824401c0c040041d40000ca03907201c660404031080211482c5800005201c0104440c1d00707007102c1000c8528907941501000311141c091114680c0c021207281e1701c0c1d030703e06c40c0012110420944c64005000d0310326400321012250415107401ca64031500b401411941d0010450349045039015100c0c12441c9142100c0b46c1d01c80c1400c40181542036140d038101d0414861811881e152080100843c0450b014080f60b140d09400303a65085580540c402a40400d0a0000348000390740800c2040071aa088900800d400302c2e03900014244502d001c201650510070641c05104240e04603070300c03000310b4a09880401003580d942c1410760b40c0591049006003003ca000e150480002c0c0942c25a83d045800b89111504040218990318a048030445041c2c80c1a406544100214641102440001080003407002c0f4254550b43c041041405a0300408503001d0b00403d408141810643c041c100c010780051200300c02c4080240d00d20000c00f200b44003400082d09000004203c804140205405035901203420303441c20405403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 85062087 1250 85060837 85060847
    0x20a1407030905061801021203060a0b030c0d09030f120504080a050304052503020307080a030503190e030706020405010e120303150406090c020303190606080105010c020d1a06030d0e0f01 82
    0x204084090052540b0003040c191542030291243e0b685400e000300305c580c03000c03001918080c401903524144880800c00c12003151030f141c503444111254074409a072070745c075800281002030003203c00e581c80716840e03e03076a4410305a1100988002e40001c2d112404141c04403c503150644000700c2d80944091410031079456000c0c071600045030321500032800c0d500c2401300708040346c103640100401d1803911460007405100b9031906005a600810031100141000104d580e40900300e404000c00c00804c001c10240001040716498000c4005801004148c0380d60f01180e24014000750410b0290b1400204401c80d000100e00300041c103802100c140000039401c654800c11b13402400203e801c042034100b07071510740004207100540a94400c401c2a50099900ca00d40000d24440390780c0c02c03a40301003034241080c00402c48a500000300c40d0646100f8a004001d80010340046a0000486d480003400305200407040c0c0d1114642800a900681c0c00f01c042e07501c4000c41120864607030f8010410070381d1003403090064807070640c014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 85063337 1250 85062087 85062097
    0x1b1a04060e0607061e060905100e0606070506010608010e06040e060c0306180406020301090e07030f080a090806070f020705010201110d0203091c0302030f0105100e01030e0106080706170a020a14 85
    0x42c101450614565103200a0300c902490b82c011303010711211030b5060500503004080c00380c031440f0801c12040c0307071210034011180094401c800384142c6e150b01040094480358101c504154100703080301d038156035541006011100920458144d610220041b49441c9058000c0f2007800c0c00030002081c507502c44c0b0540089a40c40580f64590010f04c04203482d121082c10b5080c0c912450142c200141c807980342c0364408043c0c03181e4440c101d4140e00141c106200080503810aa0113654103d41c00544511100d0415211540c894114850900c603071b604000481d0f5204840c040b842a680d0300780c0d03848070340c2c07400168240d8604244400b1810800d0182d80103d4204d03a0281d0b511002203c1140d10300024440d40b0300c0c050224100100c00030f42c0020400801400034080c00d030040c1001c1d5000ba514104441c00207240a0002d00100d0400d80c1341c6191002181c02500410050942c140656030080d90700c41d00500007800d80520f1038580c203049000a41181c0d824402d81c3c1a49080340c54204120a00c58075401c140d90007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 85064587 1250 85063337 85063339
    0x10c11010504080a03080412031103010911091c1103030a051e0f03010e0a0b0f0907030c02070e13170309071e1d04060506030a050c060a0201090803041b1a04060e 71
    0x410700c0000b90410342080700b0944e0301d0298841c10014181f5007410301001120101000a03d0704140c0d40d000180010300450381111444000010b10ba00f0000c5400c0080c8100c6404c1944a02071081c031b00301e00c00f5103284920f15070b8428560b5851800840c000c0c0f40e00c9014081c0208040340051100d850040041c1500480f00b801c1d0a0f002480c001c00740c03030000c080350001e030002000352402c4400c001a001e01882281e085440850b0850800348000c000075503819001407046003003580b5404400320942c0200540405041c040710f282c00186014104407010000001007501c003401d90130ba00038038600300041181d000320b0021011300005da05004a80d411401c8024007848407042420f800550600402d21b44168200a00420a0542054103180056400c0503000314030a40180e65504009000068490f5800d001990003544440c129482030f401010224800340203010300000308400c100d000740c0600c0d4a0b017808207841a20075143c5048050942c1d030345601c0704d100e6404000501000b40903940c1a1000ca030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 85065837 1250 85064587 85064597
    0xc020303040305010606030618060305060403050a0c0f24050402030a1b0905010602061501050319051503070e060316030302251809060f0b010503010504021b0d05070605010b0405010c1101 82
    0x1c2d0741c2e07031600c4c02c40f07a095200340c001940d204420320090220401c60031052000c0d0300240442401c1d074844980b2104040d00043c140310001030b800c01403500400903020b071944c1029056224807481e080c01000703000001c6d00c0380e00100103c2e4891808800501c500c501468014006200a84541d6280c480343c2c000114a4044e41c3d468040c0000c1d00001c500440d030184c006603000d854541040c0d80f07041c02116a030a9181c1c1801424020071010fa0052421164400d1224901050036264113001910020b9620407007501806014800704290482c0d01009000795401d4040b122403244045409a0844240c000100140c028000b071561f01c500c6030000c0d081c030340c00d48440030035503643d074100840d030300000202c000000e542c0300d0b03a80310140f00c16486105411500040d040c0410490100000d0041c401400707000d200701e40c04113803642d0700200e0a0821340e0070300300c40c4210740d025400e100025006801040084400d9401c02d000440c0c40300694054034229203068403818004550350ba40c2c4c20110140c2682e03181041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 85067087 1250 85065837 85065839
    0x20306101a160210020f060a0212060919020a05040f05061207030b03070e0f070f03061202060d09170705070b0a080406020d09080307110f010b030715021009150f050601020d0c02030304 81
    0x30b551052a000c0041503a00200001101e01b02c5450030018000d185002c01441400302800d10900d00c0c1c02030b40d00c100300310b40f413040d107544144007075205403d100d400480c07103071000c1410050b10b5008401802030350b960000b0310401c1955042080001d03c61180c100c811002800c011800040c029001600c4110005080c2d450281e110082004500c500322441c0700082100c805110b200c5800c03004a541c4401c19180600001c3e007480c0c84068103200a140080c0240c10001f0524512071b03e0f50302050016138030944070307144281040382141c0250414035050f9141c0c010440000b8400881c1c000b110740b03a4802e602c075410140d4a03501d03080002d4215103482d00300903448009480000d041003002303610404043c0c0760101d420040540c06031401d0403100185503180c0c9410302444c4540c0c0d0014104045440301d215072100d90b202c0b408100d0900e0380001156104900704204401003000c455604813803031841200401013445503000003800e9070420341c5c0890160b0400880001003e1054102200550014003224501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 85068337 1250 85067087 85067089
    0x31d04020d02070b0609010f050d0203030d0f020a0f03020c060a0f0b0a0303020d0e1c08030c0f13030201030e010b0d060b010c0f060b090108030c030f0a11010e0703020306101a1602 79
    0x80d030700c84090141110b90002e040020450001030041c3c12100c20303520a880c560400d08440c40720000341c05001d10643e1810003441c11940d04108443c042404030406101604c10226a40e019400604059005c00c40304038503d40d0f140d102c0e200356601110a80c00902d26911400480402018100d800e038180710748030340e804030300b0383ca41a101400840c4690b00078148140030f000300070030070000c2e102e84a208d01a00038414104101000c2e10346a40c640100070705543c0d88461000030072500c07581c518090140408280c261a441c40b14100000300da000707803010301001e80146041c80c2219291516207500c034035018030b00c002003801d5a1011000003010f0400040341800350301d508140103181c0004440f80307620350000b040e0504101032004d005128140003107050400380d00307007681c5034007a10075201c800080c00700d2040201c03845021550056202c550007001900d062103012a180d900e140010782c0244162000300e0017401501049008407a10402240481800a80c1004495001d84840c101d0003494038107031005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 85069587 1250 85068337 85068341
    0xa03090206040e10140f060301140105041208042408161101180203011b020303040809040603021518100909020c0c091602070902070f030c020a080709020418020f0403031d04 76
    0x10f1140b0300325001c44c0301c2c58104c1d035a201c500d55003051401644148045641a2113860035203064881000f40c071412040c440700103c915026a0780180c0d116000406032000b0701404d60014000e03076140d034000061079188460580903014441010200107041c030000108800080822040b0f0708a0b14a002c110500da24482c076402d40d0500d800c417144550310b001a03074045103024410091010200841400b94048850003e500c0c0d006c020405800d074680018150269506c0340e020b5809503070300601c0820b02841c42040880b03990050340c54401075080030f0b0441986403809103181001030415030303102c0ca030072403c000c000c00281d0003080c0b01e418188592500000700b0303502d80f0311035849000c1d604240d201c3c50f0366002c0020700d04012940114400c03403042080c0008203c440e41c58101c0f072034060515920741c40d0248040f41848060340e100c10070501415034003040031840e071780040080340c51404000d0301034504508140101d03c41c03840b84034482a800c000800020b401201d07210510107a110070441c0d4440c015000c0340c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 85070837 1250 85069587 85069591
    0x60f010f1e120b090f01030b0a0905010207081b070b030105060c010f0f091e0305040504090305160803070f020619180c0303030b0a270509030d150303020606030a080a03090206040e 79
    0x1c0401d1203000c0080442c242881840c181140484124078181080c2c1c8414012400602000d440010034000145095085800c143d0729258440000c550761449403d0040c442e810496040300c00000111512049800c0003131641c0540b0300d01c0f20030515591800d002c100241c3c0c80092040003c0d501c0744d80c10910710050b8480d44002440007100415a408145803c0d18880c400c030351460442d1a84003501d101113075000d0213540507200c040d0b40002da03e0840b42016200c0f40181c1d500c5001c000030801101040150300c1024601918840d01d841580103641442680c4591048449444a041d1104480391680f96a008180140e034210103a001c0303480c06450b003003d00c4001e60000c2c1e0200361a1b254650550070403402480c01031402d0b00003034031440f0954116020740c0c99442e90003481280c984c0d010640c3c249060048604509202e0300410001c070500840c0304840407107120035000343c02082c0001707003641400309003c8090350317105c02010324169001000717400500c00990300783d8000d07500b400041807403d10303010214 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 85071943 1106 85070837 85070897
    0x105040e19120e190806070207120b04030c0b07080103030216080a02120102040902040f0e0702030a02032203020d0b330103021e0703080901050c03060f010f 69
    0x95220004043c0345a004140300199803801d001e840341d8104488400c0140d4030a03547c0c00e0010798450100d4481d600b14890041124400107881c101800d03030062207401e081e2941025a268400030311340482d060301c0494000030040c003d254040044507110700034000c00f422000e060085254036a21a628000d004d240e24034481540c0341403e4041d00c0142c0440b482c115155070b91400711401c000001d2003070074180003844e008034070418070210445041c2082038001710710780420000d0a0600c00c4680c3c01035001d24440100201c0140e4030b08612841c041e000f03911105940c10822020420341d80301602030b09401603004200402d1104c2003240b0624030409080c0142c4502d2000d907c0c401592100100036101ca00008444c0101500308060398026880d0000030405036481003900041444150340455000344108540c0075590b1080300141e401c1e190902e40101d2840b0f0301056041c59605400c40c0b2 = true := by decide +kernel

theorem cover : BRFrame.Cov 84892087 85071943 := by
  have h0 := BRFrame.cov_init 84892087
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84892087 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 84892087 ≤ n) (h2 : n < 85071943) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
