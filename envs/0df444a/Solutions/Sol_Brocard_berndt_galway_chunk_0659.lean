-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0659
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:59:12.011206+00:00
-- url     : https://prove2.me/submissions/68b3b5fb-55bc-4961-bed6-34448f832cb8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 118345323 ≤ n < 118525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 118346573 1250 118345323 118345349
    0x18060d0f080a080105030105010f030204021b010f14100b0708070c05030d030218030c0105040611010b0d05030301050112140f060402121501201203061504140f040e0601090506060405030106 83
    0x80b45034400552800350000710000e01c40781d454008514200c003031500020f071003180e00080340f14504620503071401c04c00901c00000d21a69032030241900c0100b0520420713500c41d201103000950b55600300700c950010345080c1c2c182642480c0c0c550300c8030350b031a4001000031070b4902207144001c00d44d550104541a202c0721183e0740541c0d20360a8801c811911008500746034042e500404001405a030458280c0c1c050754030506d80381c070b0340d44045c1c1005400b50486014142d0000c040480600500c01c0210003036058a0003a03d034001402401d0116074111400c541d07603010015980d1000c6070f03089032244000d5401103801040582010200c0740085100b010981c4c0c00503c14a000b00084060b51304881e0078401d5550201041c44c40715048031250361170b80c2181c0e10400c0d28110000c00a03001d0b80c0d0340f80181800000d801c0307071162659190048030b980c481070050034a00ca9103050805051924090081c0e12240d22a800600156440c1410400103000050151540924140300120b11500e00348a45001029586c003010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 118347823 1250 118346573 118346587
    0x3080f0408030d020d06050607050d110a1505090f030708040302062a010905010c1107090509030f040303030e100b130b0f03010906050a0b0a0602070e04390506030618060d0f08 77
    0xc003116581d6012234003070141030040c04042440072130b21000c01515414103400325010024018101003180e603005140b02914140a40da488c400e910052142031140f0443d401d07400d00b01e40b4a940d90051300c03801480d4a8042000384018108500900b01013900d40910b44003012041850620442108940ca5103d82d92515603205000c03090154400a134401d00b010503402001d040030b191943c40c3e0b4050b0800198803040032a903040010012280f030810894585515941c40b49801400b82c814041580d4641c41148c040115141c614840c2c0b80c040000144550110031100b01d000003e850407481c52070b031044045001c14000c1c1c80a0240b8032416104602c000380506d800d000140446e0b11a1400b1340c0541d801c0340c0309220091b000948581915285491042a540d6528000c83d815858202c10107000102245072200321400580d422452144d141d6509850b1791100c0500080740000c8400592101d108030369600c200304030701c1c0400c0d00320b0b8002e01143c06612598540c46000d400003001214840c030005680 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 118349073 1250 118347823 118347847
    0x111030406090b1f030f05070503030f04060f080f01171c03020d110708040506030c1315170c09040c0e1c0218010602060c0901181e08070e0103080f0408030d02 70
    0x5a5205030329011901000354803404d143c1508440740001003941400244000500408116100050000904582d81c6000302c501c00d924540140c801e0901040c01c3c100014966400380d50250702c516280490f42840f42e107413080b0580c07080c01c0300303209000038010415000c800b8440d1800b01100d41d402070305c000da030319103920000004844001c24000500385090141d030002803131402c1107404850003260403946980704c52008050750f1050813800810701040c0c1d1400a03000002c100d51501800554031010030445080c1d1a000030702800b140c11000018080000220070302e49544250381121840c6451908110810081042400c4120954038511343c401480340441c948600151030035038500c500e10b4019450620042d41e07030b0340050022040103101182c49201d6922412070203182e41d0b03032650751201240d540e000101455001401005a0b00a400300101d42031100085110844140c0d030039a1455a2035510760301e44c3c0d5040b0001040d40d1174400c00c80025101c40400141c0f03070b9080752001c0141c0d40d1011f5054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 118350323 1250 118349073 118349093
    0x180106090f1e140102191109090105060f1e03070e09010e0a08030106031d060a240807031b0f0906061b02030318120f030309160f03030c0302011103040609 68
    0x5850201c1e4200341c0081d000c0300b040ba40c200b01c81001051101a100300e0300181d05010000c00c805000182924400040c031669000313000c441c00041d41c0224440d01c503505198283c1700210365a6400001300e0101c1111b900302000a1802c1d80e00c10b480d140120200e0703d00107410040c03141d2010080c0200300c424812410303000e202c0e1030b500d49010301c010821250380b03556009190005100364010b0507612240da10340b1030704c4040d101a04d088030400b07032103040c030700100658010081f9095111038000168000807400c1c1c440d03001d5409603254600200b054520350b5507115034807030282500c040796204040f0000b50740c1500c51014806060098004601181080c000030000c0345400a40e0409610702d4403034030090b84011040703440e4401340d1500f00a02c00300800105110400d00598120302d0f10440d4450b005040c0302002550049a180382926402c0036001e46981000006015110382e0700c1c8410000c10009004200c400e1500b4420b00000c182ea11000d0403003110350300708841c251882a1240c050600700700744030007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 118351573 1250 118350323 118350329
    0x7060906051e0a020c030f0f070506150a030f0f06021204030f031b03091a1501030f060f12050a1a04060e0d0203190e060a03060e0903070201020a060506180106090f 72
    0x40c040c0c0c1e54001420110325140409400343d20300a0780080c03000c8102c0c0051040320050300215000d190340d10003640880800d0b42c0040b506450501510000c181d00c00e2200210f0000300c0402451882840d0454070b540036240405003003240d000e20350092020001c0c84d240042c16400304055a801c04602c0c0c01c4c02d0151441c2c40f100070070810149028218048002c21220407100300503d490300040b103000528140c02c0c018140310480c610740c0440b00421204c02c401c003550300b03048842a039092141f84c141d4883c1d4002d4981d1406200b0680200703520030321001c0648000310700d04901078403c80701003a40b251035480320002504c0808140050100401042c0310075401002c11804c0c0d40d000808050000302e000035240d000e04201032010300c0501203035880c43e034414045a01514401040507a949001c0b80d00a402030849124855200450341c0006150802c04001c0e2541e070ba03010380180a100900d59541002454010104c6901160451072400d0b095081c10455000e440107880e824441800c280f02c039414914554 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 118352823 1250 118351573 118351591
    0x911192606010e06102a06050a060506091c1e030f0807080f070503060d05030408030901030c0c03020307080304020d080307110f0a05030906070503160f0605130809120c060706090605 80
    0x1130043d6500c481d000d0f12103c40ca580781c040000d9402e90340d96842e600c0c00201d88490100300e60490340501000307a2200c1e001d000f04110802c1680c1d501e40502c0103070b0107428916503000c3c00f1507504490b012209880110510700c101078048902c1c0050b20300160501c1001400d60000d00600c1070f102c041034200200c90b4102e0300e01d0a111403107280503109140010b900602c4042001008400716100c0d131207805e01180140c1d801000d42c1d07251034490759081e0760717a0003010714240003030304050136402c005005000c1080e8068042c0e02070343c54102203498010840d480a801241c0202c280f000040108981c10b0245025070442d0307443c05041c1c010000114607200001c10207070b1080d0046082c9200080b0008111849014151007071511404070703091a0f2305600031b000d1518049100d907404001088070b500f920704000c0303205110402c00d036141d01c07007180e42204909500500880d0b040011415030701d85004900c010741610000c0395661081c040200780f06030003405089918503252a0302508010940c014258051415 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 118354073 1250 118352823 118352849
    0x21020d050f0c162d02102c0d0f0303050604111815040906030f030909020f0306120c13020d0b04050c07020d0f0c0e090f01091119260601 60
    0x100d070920091042841c0755403180402da06000410480380402090103c21580089507051304020100c3ca146030482c0481c400d0310808951072806002d84541c001060072601240340c800c8070300c0144003441040040c0e26030300c5101e5058000029540c580c007001540d200340c0c2c01141c3c50801500b400705903045039146061a034803c0c03100d00315020180101508010781240d07001080d8945142c0701946101d50740100100f141450f00110a05c180d40000140345403280e544c032541559500c0850080f030017006040000c141040010a07001c0c680030755003c59103a0340301d0580c0d013540c16260000340c061000481e55100e950b004074988124803058400c20398810001d82303041c400b81c9011045800b80b0310580d00c009114081e10700341c80090080c0c10f0b04030064140d02000c05c281c030980f00c0b10f60b41208641103510b9807072380c030501e4032880c42d0040c10700030a06056403000108054107416020051020800b0009403441842c41c100000c040f02c2c0c8030054414071480d40881c0c281c40000c002e1050414005800c078801444030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 118355323 1250 118354073 118354081
    0x7050c010516050f070c0f08061608010f0501051b06160e0a140d05030d0507180603090510050a020913020903010606022404020f091006080912030c0a21020d050f 71
    0x8042100d0000d0342c18065265a00f01521b1b00c400484015000003500320740101c0e01184030400040e00901030810000c490b814a0110348084814203800d0044078411200d942c020400c070b50088016121420300d101410300b1414904040520303003407085039045000040113552a124603007000718075200c4082075a05141d40342c103011568856030400c8440500440d6621070201c00d0200c180300303540b208441e1b04400e00c650b06188000408120b1100c806140d0b400b940e2a00041c00d9000e84202000c50b6444800b819065229588100c02044020010001d494081244680d1591180c0c4254102d4800420050716a64208185821140e02e03130050b006540c00441241c42d2400124a24168030001c00c044580c580c2d10361000c6681108820240c2d50441309040a01010f2000030840e10107441090b540c0c0c51040e50340066595546c40004c0307162512440c1000031400402140004014185250a0035140c3d401001c0c402c0300c1d4070320880f881f8030080b40c0c04200d40050300c030303a40038194019001305041741c41424 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 118356573 1250 118355323 118355327
    0x702030705030306100203040803130e0a05011809081e03241507030306030206030c19030c0f0804050c120a0b010909240603080408070302040b1503070f0903050607050c010516 77
    0x10002d004c0138401c0ca56000b00300581031080044401505c6220152030311260381112030300d018400350066501c040c0040c40000e41c5090305202d064101c0e0b6401c0100501c11001c80d81038001040003403001d5030000030822115940c003201c0700101003c3c148005403252f403803410004c40506551500000900b001046410560582c0c030241c01c02d00035003210a12980d105540e00e420f8004040d645d10007508901c0201c01c020400107924041c100d50b0148400f41c0308020712408045045410300d440b1840801d0a1900c800344c41c911070601258403074820030464240070041c2e00050900c800c12021041c03107500c40c64081040190100d0140d00500c10307030805100d81c0003203507194500e41c0a119140341e503422140004480e203c0064102d90000c1d41c105c0300040d50785442d2a52992141d049005c01c1c1c3c0242d0500940d01428107010b2443e80b0701082040c003442c1103444801040700c4240541507024100055180b010010aa09002e440d004840a44800e941e42612807000703829a80020500380380ca0342000a140210350b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 118357823 1250 118356573 118356577
    0x314090a061a09071b121e0207270209060c010902031b030c1003021308030904110304020d0b0c0c0d02060103020108011e030803090f0a0510050c2b090b0f0609070203070503 76
    0xb00721400c1100c42c1d80f48180c003054080c0c18005018100c1c000d016206502d451f046407020090383c028001c4020403560b0308000341da4602c00d602c500906407a85000a07828628520034a40003010202009441c04503200700282c2950030034258544031317964034142801145003c004641c0e075850001284000707450b403400000d441c3d40070550a140180c550420400b840b5102e94100c0b402c2c818070501d070031001ca4982072032954907080314490030302030707031907e501455a00c1000c3d05882c405c540c001c00803106444565514500008090710741c8038a080184280b641e220418000c1e0080000168018122580b442c00018141841a842407181c401d5290b00940c1e100c0d00680c8084c203982d04890701d15601c0d2a4000201d01c0c0c0344aa00380e40c101c034000c0d100343d0000c01c2000701300740c0c2528007001003e001644480c24241198800d143d400d4500d00c2e000040840d801f103962039000b0703080d41c1424001640c0d4020b80c072840c6000004a030582001c1c680700042055614140c0038142e04101144011410030300550f032826664 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 118359073 1250 118357823 118357831
    0xa02130512070621090c0303080a140604090212030f07020405010501030207050a0210090b0417010506040e0703030309020604050d1104050c030603030a081306020406050d050a0c1b030314090a061a09 87
    0x100d1048000355005840491003140a2190b4004000700305c0507083c00303203020390700d40801c90000d00720f240880c0000d00f003401000a649544410244651900c07420003005090b01101240c10850002190001500c1840540100b60320120101e40d2488140b040004440058010030b06152043c8000d50202d0000902c50001c03a5040c3d80103001810701210a8469040b241d012044d24000002d02151410044034000055400742d00240b00c02d46502082000751241c0407500b9603a82d001e40c0040012910a421007a201400505aa842c0c0368441010a555242c0c6050984014140381c0301c0d4540d0b81032510030f46500a01101e9610304505000002903160b10079042c001080107052400710f841c814580844842c2294000c0c01103580740d941c3c00e400ba0484c0c110f001c6220074240341c9400126040d00c14014900780d4001603560580070492200342d860315401c0c0c2c2d03030f041e020140d85814458600344606041405013049900030b001d1040703145085c009940940c2501d80c03458400714a80811030301c0b002001c80c0c02c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 118360323 1250 118359073 118359077
    0xb030f060301090602180f0409020904030807140f0403030e012a0201120e0f120a02120d020d0e010605100c0206040e07121404030f18050402130e0a021305120706 71
    0x1540c4401001901502491002821036840000c10281802c1d40d034000c0710b00b440081d110705248176465802c1108684403140007a4200880c00e00190020748a01c80113540480c550621100c400400c0310024005d070020f2070344810321440001d05100b815086801c181510000740703020402c0c4002801898428140b023015401800c8650035028216801050700c808140321030441007101c80d4550604a40d43c801020310400c290141001120500101071704070303400070381c6580040c0306101c20343c1402042603000080240179281d082c0000030301c841c1c1c50302078091103070302580004c0b9425040c10f00301301039a0002a003a03410b010000000c81e00607180c2105131822a00f01c1e2030802c5841d6500e580549020f6100072818558500e49107154030300c3c1c051400800d01403802a601c40404c409002826034152a2002291044131707800c0c0c40800c11407402c1e80080040045000c0c20300041c0317942c0d60742c0300d403030340d0007030350301e0120320343c01151003103014070200d403a0001458220b404c028001d01d41d40a01d40c85450314066002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 118361573 1250 118360323 118360351
    0x110609100c02071d0109060501021203060105030601170f041103010c27050a12030f0507020f0d1112070801150b0a0806040914100f02030106090b1b060907031b0b03 72
    0x1100302d00078000140145000704407035041541105210304421401d000d140740403880d0010224541d44005614000c90180010f40b07491038031190015510390f0401001b060400003205540040707001c034002c0081c0101d40c46c0500c0000d5080510f03040c10800d207859030450181e0701d4080540c00603030703000025605800c0c4003580304280c001d15103102850042c980c1c0006402201b50000042c02e901580c090f1501c3c02d01035590302102203880c1c242240d25100340c01000c0d501c420701b110040a14940482101140d80c07040c1c40e0b5407041a0601c0100d030204074452094111078021002c1002401800c1c0a580c1540303400d1800700c00030741d0030803640d0700b00d07070003403d1200b01000943d40004619849035480544100e4204040d07400d490701c110241555044010248d20109041007040d203841207a600aa038142c81091301d619a1081c2012000c0c41250015003000340401c0c030711203002c1c8042209010481c0600800c0c005083c44a080d41000890312001012060414003a5042004258912816280c00880c4840742c0e81d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 118362823 1250 118361573 118361591
    0x10050903071502120c0a0207060302070308061e0301110a0201140103050a1704180603110a030209010603020c0c040219020f0f06070e21030a2006060105031003120c0311060910 77
    0x42c1c002d024400c0b03090040c03160740040c08007118802c4064403c801080c0d00b11050191a010704a05034041c00d80c000b00071a4001000c550300c0e180c503c1e40a0ba000301314054003a80b0341c540c00c2c0081d00391414107400180c079480001c0c404400c41d60a00071141d48846140c58282c043d45541d588940c1c94400c0342000e080c1c00c80c0918500142d21042c0304450042c100c0d584404e002941000081000341424071080760b5401001004802c9801c084031001c04598006012488a038a8001e09602170b5018a8050301c01e4018400000c941d03550314800340804480d034128960f14211000c1000e40f40c0350007849500029801025140d0004130009a8181d11608070b140c01441155401c012403002c00ca64600200c5d0600e500521030204200000030b002e40b544207507203a45c1130300500214101070390b0b0b11501d8280036802c4600000c07025405a0010354100281075450b182040c2e0381d4640000b034140200d0408005120100010305142c1c1c0404072980030300700640a0101810300108030365036000f02c11101203200d0780f9102c0f50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 118364073 1250 118362823 118362863
    0x2010309030917061501020a050a02090c1201120501060501050c07060f110307060b01120c0c02190b030403050d0c0e0102060f0702030d02040f050a06030b0d0f050715020a03021005090307 82
    0x16030020146182c034042800314103c0a03640310107044410b100c00080341d0103c4182c5600c0080c50811564203d00980b140c06026020300494000040460209010401850000d0040702c5805402005d00610526001840d80740c40c5080d180349601031410440300344006041d040e40822110219102410700c03504441d18000c007515080412540712105000100b911400d00c003081c1c01210412200f40d075030003036451031080382c501141d1a81d191a4000f0b480c1628980040c02c10840898014460f0181543c170f05554100e442c1c21a442150b0031800902c022851382d00641d40d41c000c001a8000f1803e007541800ba00f500001d40e18500248000d02945c103981c00300300b0b054020f100310b900e00c001002081d13540c3c940300c84d03000c0050705503441568054205100001107041c0f091180f000f0522004007080b2460f030300c0f80c40e907181414480c5001d440c58003985e00d000800030f40c000c1d940704440125401900000d809810040c0c01d220581d0b0342032030301c00d013000c4c1002243d01c804400c4403100343d841001c41500c0b580507000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 118365323 1250 118364073 118364087
    0x4060e0a0e01060e070c0506011a0703050c07030804030f0c21060911030d200f07150311040e04020924010c06091a090624130b0312180a0b03040201030903 68
    0x400000f503100c800038094003c0d4804101c1a1b5140100200e901c280d80e25000400e07680070440c0c069078501c0b0144000d0700000e100300b00411485c03134070104a900340c60700e03612605803e0303001f0740c070031510844090f80da10704001030503000d070005000450003407000d8012000039554440103184000c000b640d80358040f008004031000340001c403202c00740469010020002c000344c2003002803201c1401070488501c001980302000503c07590302c511a44044c04040b450411366042003000085240203042d142c05950042080b1040900002d1184841c00c480a0400c1e0041c0562000090301c00c8042c05498010070290f52586100b82403940001e01c0c08011162250170100020148042c00034000680c0302c1038100522030184102d030140210405540c50b503250486c0d407c840103001d841100c0d0b096109118056903203400d9060034920401c112002c16500d61010019090542980e41c1c8001c641d408594100c4d03181d01c0007079150303449000761a4811024200201c02c4454000180028101600c48407507508042c40340017 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 118366573 1250 118365323 118365329
    0x60f0906010318060b01020c09060a15050408122817190504050303041407150c0c080f0d110a20040207080307020303090610121b050d06091104060e0a0e0106 69
    0x222000030f020a0311307288003d45903240e0868010b00c54516407070b42514010000c140115001880c80c0d46483c50301500280100448100c00b0610100b4440080c0d100030501040d10481e039130440d0680d0310038202613032480c0d21500500110840b4a1030036105036407a0000980c2800c81e03006010504130380c0da0810360686205040b02004801c6050000b0b000030082d001000c4c1d40928840c4207400d030680404583d2a9072002d0a10440c0009031600340030708907050080c0708500701240110440b50507141ca0f0102e640c5040c2040320711000c5540f020b0100301c8a0380c0e00c05003500203e00e11300058000c0c006680c540311840d004a22809801900740c4680385015a140e9044400300b6500249403030301c92808440103900c81d0803c070348a14542c01401c000641e982c00d160380c07000a41341d0007074803850007020940351034400c51484a250070060700d0102e000328070350b81c17401541640b05101d805c0c04100d8500138902031441480450b501c500a6007044411b1056602078890150301152480b030005c1c10a809154146c0548040c2d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 118367823 1250 118366573 118366601
    0x60a090c0203040906050607050a060b032b021507120203090a0b010b031803040e01030b0a0608060907060207090501060503010510140d060302030d0903170a110607091d060f09060103 80
    0x8184854103034002c0040c0c001c580b115a82003106580e100244109440f0303509000b03105030041e9a603c0000b458691020f043d03110058100c400003000701d00302e43d41e900c0f043c41c0c00101e00c61088102c00312007941040404404203a1554488407414803600c0034158a1b0031031f0f00c03028155004000500c1141c002c00c0448800758114014480e1940c2d02d407546556a4825103001540060356440385583c0d030000000c45049030000c2d0b1012010340c6c81d6456142c0e500501503c0f04807425221500010020002c2254500469151000d006a05d1501d840a8a0032440d94082880b013401c007001080840c1e0841c00341c2e41103030800d075410802140300700340840d0080d0381410b040f40a650003164901c01c0c88616403000051320320079000c0f2003085140d02401d0310b0a042510001b4004c401485410b08030480e5000500100c203400d0804c8881701c100700800500b00501150602c0014404120400c00e010358288800c01c3c12610820540c06800c1c0600410a0000c1d0401a035001d51480c1c00820300c164801e9101581c0354030a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 118369073 1250 118367823 118367831
    0x70b04080406021002190509041806020d0c02072102030a150501050f0409050703060e0703050304120201080f01140103050711060a0c1d1c030302190302070201080c0a0f08060a09 78
    0x1403800c040340d90014010840103106241401d0310401041c803c0711360300354401c0c400d401d0b03030510034034120303044e0380140138458000351900904080b40c200c9840001c1c01030b10903c4056242d0500e094000f04031003259a44004561051800300706680c81c04502c40c107d0544a840c101016a00f400420b00e812145140241312004d503403442c04040c0c0540d444036040e5902166612030b2502000c1c2003100352a42d00101502c10380007030000300005105c90340b00b1014507000340142c81205d0340c1c0e43c480c0350454016902401070703122880c01d880d045607441114164020400c00d03d03a0500d5040000c00201e40711140c1140341859600c1c0080740185000d4503050f1203541c1e140f01102c20394a02040600b014003a99030424011581050904807008000801401d440c003000d07042100a1310613851801c05000d075100e09406159003045400c4840003c029030450f0701c542c0742c90242c4c4c0c8070500d100043c2186002402d00141d43c40500c41102000d9000541c1d0b50808400c0c0760610342512503400003118035865500c001642032034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 118370323 1250 118369073 118369081
    0x3030103031106130308070806120a050a0b010801090c0320040c0c030906300609020313050601090209100c051e070608060303190507050c0a0e090607030b0123070b 72
    0xc0054440682c16440068800030b072a00c02c2604000002c450006000c01c00b00d03000103920500c540030407a48090000c05000c60304e5400000c2c6410b1809900055035290485116032051000d03142d038071401081c0c024002c0090900360b0700c4d131000b110a103020081888a8022009008101c809a24180c40400802c10081010302510140180ea007a2004402154a024001584a004106404442c5100803880094001605c076140142a4908010140c42d6440c10041003c003410310186125488042c240c6480c3d00b1a428010b1411070140d0007038000034010080d15040fa12411040b00900c03803c6d01703110032032000c54500300e41810700e0303410341c0301c0c408091030100784110b080010100700710323959a1541c240039100d0005043d00c0c4e1095200c2d00c4240c44459108002c40c074481c200500c030250240e410303203400d5012a00040c1e104201a0b0001255544020502091950034400d0b0f0340c0102c22405c4c1000720360494070010740502800404046c014449200041074000d04004894039079500159990207458 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 118371573 1250 118370323 118370327
    0xd1a130203061005090f01030b0c1b030f070507210f1104050405010b210a141009060204090605040b090109020306060c03030408070515100e07110a03081504060f0e0c0c0303010303 79
    0x88138412244248108008240100900105c40e4140da0f0020404c985a59824100d141183d100390b001d00440702c40c460b10380e1203280d010300203020460348040d00e40d40c0c0e80d2120304189282c07034100e030000031190507414140601b25000e00840c4600c264040450280c41d001030620398215a00540c0a1350058102401c00c810410198007201c8000400c8411469145184480344c149403100079000400707500c4540078501180213504450a02c07014981101e0301e03842442d444400303640d40c11030201d03410b5401050a001080844c002d040141c20252001c105c508003900024000d00c07010b1190481c5a507000001c52880d0329402c040302c00d43c5401d4070842c3e43e05e081602e03020880781c0c40800144c2d07007401008504010f1a00951005006224003d88092982e040c00340300811410040c020005024617081020007030343c8240304003600c4601a40303460b0075074684580c00e2003a60004040c214451450071900307101d070500d112100015540707542c205910341d07502c05907901d03030301c3c031400302206840c3c4000300000007059 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 118372823 1250 118371573 118371601
    0x11a0d050916081621140a02090109020f0d0f0b0d081305030303090a11010309120f09060206130303020c0c04050103210203160b061305090102040f050d1a13020306 72
    0x20a8484003440d0190740c0302083c1d612912001c011158541242804002407110040c50f04101680c1140b0884e80503815916a60130074070a9154229941108221906502d0001c803400d0040c90b650000b5440c1c04034082c5602c40c11f110342203000d00c6c0c041e990144103002010a034050740d890b00d000740145018040d00e04002d220b079044440d001d100c0c1d001e1104040f800d803c0210650740035184400050035082d10640d03511800450f40c5902c94105a503030848003000c070f120018080035141c6a502d421402541c41c080081401d0002e810090655200d8030600c09420081d07880c500c0e00307981500e03005032a02d50108510303083c000f2181c120380d881400c0500210a00080c001c1600c5070749a03d03100c000d00b80045034801d0340c03280100c0801c04a0002e80e010b0341000700e2008203425a020314020984c3c228038004080300c108071007007542c181c4201d81d40414140a5150164a201d02510045421807140743c99a0740b652170f1881034903d064181200c0e0302c042140300c0e4603462140d2100d6030042c291622071410741c0a1840e58 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 118374073 1250 118372823 118372843
    0x20a0b13081009020f0a080706140c0d0e0405150a1806080601091b020a031e0c0203010504050303090c03070305031e04090c0507020a050103021207030e19060b0f0108010608011a0d0509 81
    0xc1c1020702c5030170204d0314151502800b298000d0000d00320451501c0b006803810450520201d403c4c2004012500003550240141c1da00b02101d6124041c008980c203080c40101d6400824441040701c02c4134072604159500c404100c00c071002080e1007035041182400c1c06025043d141e010016038496400042007494960f044241c1080b001500b4010744030406500701c1c0d80d1b281e003407805004600c0451080300000c201c500017000c1820f990070049c0002c1c0c2d0380c0c2d022a086070f1080b030341900c05030000304c1440301d03d000c00e000306410304d40101c000f44000b03415070300d80c20f840740b0580b2489034030106030402d145810b08100b01030b0781c002c0c9031241c002c010004143c030b009031070343d80308013001ca2103024100000b103070940c00782c4250b0300840800e11820340140c0d90b2034000d80080c40040c46c000d801d44291610481015180500310403040c2c450040419003203005010f200800c12001c8503181408442d00c018404103a01145282c11509809e07004003903011015982e2081c1c1c030404221924890500701044810071000030443c0e08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 118375323 1250 118374073 118374079
    0x190e010803071b1410050702030604060501080714010509120a080a030203040606050406061e0203041e090c0201050402090a05060d0807120801080d0903030522121b03020a0b1308100902 81
    0x10340c00071141c5603c2c8403030050103041d1014410b04c05200320384c204591450640c040d2801d0103403400d445900001d2a10608540841e1010745a800500c40c2000511a2000030a0101405180d1801c0b07000040c20501074030a10702e004600c501c0c04a0045541045080513032034101c40c04075682c01c02002c0081c080d509c100c900791200d5040880c00102801d2503c10103007150780d242d450565030807241403502c22000743c90105008511052201149484182501e090107108465142c52841d262442110580f00d00c5440310082da403411040002507141c1501c4140c0c440321048001a0a680741c1001450780600520040d1030013401041082c1082104000401801c145481c0c19106030799a40d9441c0c0e464945032900800100040c20400000e0300401c09400d14503284084074102400350683c0c07261000da140c0c07080110000c103003400e1041c004032026aa001d2690f00e00032144250854000c5445643d0500c0f50700e1800300c000600320002040c81c0c2c1c800c809005404280c0700e11854048641016040010003a0300c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 118376573 1250 118375323 118375343
    0x308030a0c0f09090911130207150908070b0705210a051b0a030b0303040506070f02090a1b0e010302090a170d03020325020a0b0a05070e060304020d02190e01080307 72
    0x1c1c001c004a071200c81140c2d4803d9410b42c24501342d840030b003401e00000c80c2c4101403442c2d5120180d40c2c1035806031035090303c641c0c01a03c0304610300b07010100f6210301c40c01c0d84032940703003560040c00f1510000480d80642c0d0000c0114504da00d400900710348070f2140c4d48001d1010b83c41900b91800e03041d15084100d00424045109104907103070882d600703010b41c0c00f00e89000341d14641041074140690180d0401503c603070004040d0f0b405c06607601d01256166000c054202e40c0d9801c0f05115800b103242083c05142c00c100600410081c0c406600c0160750302903202c00144051000000414110741c1c440d404540303000801804000280b80e44d520391706012502201200c0300360041594000310b0030701c240300b568802c0c030b040c240c0c00520031408640018441001400b00003140100c4134440c012910b198075050003252104000200d620f840c1000410030011915030a10540080091001581c3d8020200304c1c2e550f01102c40180781019413541031508415039001c550303000071407000081c4020b4003001602e1303160b0007045007503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 118377823 1250 118376573 118376591
    0x210201140f0406090510020f0d08100509041401140103050304030204111605060906090307080301150c020d0503090102010507031109090619030c170c031f0f02041212030506060706110f040308030a 86
    0x1980348d842000c02c0f01c0355607008a01c105800ca120311040d42c0c1211941c000c17a42da040e00c420120f16003410880303094601c0c10b1300000010340680300b403080200c155140000c40003154110360b60365480744a1440040d210390740710f00c054061110b515007290b0b500003803070003629148004c0c1d00e8074644881d411a982c42d52401402c00059880344080202c603942a442020710b0b16680c00c0401004a09200600c0d941c1088004869100107885261118031028081c000454031160b22000080c2500d10040603041050304100c150300d50a400001640e00c8540100c58040c8140c1d40c0c1400308240c031030880d084207080110b035000001400f07200310300d1301c1c260303203011070079120000050104c15a42e00c071a140e9560182d005030340d8907900c5c465003180107010004054001c10102c450100400030f90f00a50041c04075540d01c02c0b0032004021072000170100440980c10144001d24211b400182a8000c0b204c02421a580340da00c01030500c6144421103800c119101d10064403282c41e810100520780084a448103113034a407a00b41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 118379073 1250 118377823 118377827
    0x90a0c14030705040512010e06040305030a110a0801061b06020a050408010b0402070c1a0d0911030f0a0302060703021606050a02030415050609010b090f120d0207210201140f0406090510 81
    0x592090403543c440501e002c3c13800c42401030221686103240d070a9543d41c2e078026170107141840030a000f10700036512161603003458000102218010b0b54202a2407001b0054070070740d29000440f89045540904101d1030b80c0c446401100c107412030a600041445100080000380a5004000f4200360381c0640300800074000b51100b400101d00c40c01c00d01600301700301032004000d962240d80001c504042c04a090900f805001c8079404103a0b000300308202d034411021400c0c0800c81c1000c1000048040e80395005282c600d103681c8000c1d44030034001e80800201a000039040c411720b041c204d80aa0800d902c1103007005540390682100c0c009401c19031b803c540b203c161a0490200040901500d8000ea40081c0b040c04186d1034800000000e6120803080c0d600501104020403165549101c00050039007400054000c000c45020024180511500706542030a50b40710380380040c0700c108484266442c0d080c2041c540702414000420654020006d440b00c0411001078045440d680c0b000c400f104071002901c1880850840000c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 118380323 1250 118379073 118379077
    0xf0115050301050303070602090102100501090606110c010c110a03080f0406030b01111504020d020613080d020307110906120d030f0b09070f080a0b10020a0c0e0402090f0a0209090a0c14 81
    0x4413030b85507000380440384c0440c0d620f40c0104851841401210b50800000740064181c600036032080341480c1d540d070820070600d50030544022950079049c1c081c1101f001d40304c00207000d40b1301c90386d0b014110015140c540c12070b68607248080c401540d0002d00d120749542868290000e140d019000c1d500001e400c052120b01300c0d500a010390402e0f041d0f4180545400c101070074400090309d000800903640011120810b10250720b681004040c01622000e4082c4560304007190545005d5040400001315407003000780034040b80c540f030040301810204540ea80c013180c40d94000102c94040c0090208141c0c00b42d9403022900c00d425071300c5102c011401d4031081c4142d010500800c054140708403545000f0030313048450350305000e202d48107540d44040c0c065000110741d001400411408614545000d0150380070100d01d1003031190340d02c0c29000038110040c00021500d0703d0340c08100c1e022006407140042c41c40e10004909510071980507940c02c40e0015000340100d00d0700320b00c02d4025081c5007982c4004100d01c843c03290740030503202007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 118381573 1250 118380323 118380329
    0xd0203040f0612021b0d0207060908030a03090609060501061d01090b0d0c0309060c2a020d02060c280204050f01060e131b0c02120604020f06030a0b03060f0115050301 73
    0x105003141510302902030ba00e425811420643c4540d00700816003aa03804140042016400c2c04010401c410003943c02a01d00740c1542c201505104082800b005552030000858080f0307140c502d00072624070a01e240010142c1940316005200d54100400440d5965205000d4460704000350403903204c0300c40c150300549180310a8002c001e0803410410000740d80070750940000d0340380c030302601e40011072807800c1d01c0c1e8600700d401c8010706800240d40260001640008040f111150810274103010f03107000c4013980010451580340000074090040071a11424000060010030804c644111215800062a03034030712900345a03c510491049142401080740d50300b10803003042c1601d00c0c0c0c0e1251280c407810b0b00100200729041c543c401c03040945038038101500d100200c0014030042c0035070310782240f40c0c01c82c0e00c100640e84000503031060a680c402c10070003000d42d442c91101900c0d06000c1c1c030348990743e4640e5180c11003d0100c100702d95402d072042806100c060680c0300c5080d8100d03070701c100ac014002e00c400c00040703840c1d11083c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 118382823 1250 118381573 118381589
    0xc0909020901080609130c03030807020d0e0303040504110d0e060703140601020706110f10050106090b120106032705060f010801151505130602010204051003090b04060902041e02040302030d020304 86
    0x10740001c3d11340c100b4411898010740140c1a90351428410740e145c0400709101d4201f1000600a082031110a64041084095244d1a401c00c1842c0c50001c6000c241e49001c1da21500e03129646403410306000060b2072003103505076000b0312403e100c0c25000403960f82e501d050594400e00003e241c5051049080c4405402e80c0c00380c1d1050b40900350080c903218048811084100d24150300e4000d41241c0c6401c5881003200d10002004040003042561400304003070020526540090f00d070042c20410b403290492102529415038007241800200e40d114140c452081e0310031100460301c3c00030a08084410700000088280c81f841c2100614141a80ca8020080c05e8540700c200b10344040e400d9074070a104550701841d03244165000c42c03810500f440c48199050a00c0512541b020026075800181400035007003800c0301c211903c1c5142014000d041c0183e480340080e810003000078100503621001c4070115902ea40000707181c002d6412030445580405201000203501610003203119201d0748400c0c4503103d00200659088407400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 118384073 1250 118382823 118382837
    0xd03050405100b030316031412010e07050705030f072d0b10050d02040e030c06010e040b15060a1b080a05040906050a030506040201050c070503031306030c0206010812071a0a0c0909020901 82
    0x20500e0117504410041c8107c081c48130b4895285980107601009e030541c22000e0906004a5140242c2041540c40182680742001820003604010801c00021554a003500c0e4229958075269800d2100a206c18101210183d016810380c601c80d102829103166590350084000c5500750303c0f07000748070401168a100c0d154102040941a4026140540c00400710b08186801c3e20b180c46246840241080b200740c001352880d60a210030712060001444640d5441503140b000c2641b24506000010301a0040d42a100c00b001035254401d40605000d4991605e055030060b09683c440780c0840d40501541c125000f0902e4803490324a0000b0207103003102c085000c882d0028090030494643e50011034040d4040051440c492094170000107203a1010001060701d104809441d40c085420071000070144c035004451041103521100050002c0c550124a85282810141105135140214600048220300400c9800c084118031070030884851031503080174020a00c9540d03802400b035201c140c46402c900810030020300081071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 118385323 1250 118384073 118384087
    0x9040c0302090a051503280807021f080a06061707050c100e150c0301050d020d0804030602131707151407080909010f06080105131404030c20061801030204080d03050405100b0303 78
    0x500140e004088c09690074030710380400354000c0740325002c0d101b14800d01a5154000174410f55030000c2003a4000c1b0314020144455482d11200401e00000204541c0c1c2c98107400001c04c00341401841110110140c181c1650030020140c54490000c00034569540664058040d540d64101d4904821a200b11a01d0280b94216400d00c2c06110301e80b0b03c131440c01c907004a00b036403001003c1071030b240103000114442c003405a500c0d1000c1809d80024010b540c40081d200c40c180b0340d0309100c034030042035150507540725146030303030020500300c4044a4000c00c4200c00242e00e0000a4204203100446000b490081c0041d92100180d0742d880c003911001701740354410b0800003041d4070010700c11480c1c1201d0000d11442c0414001c00c4011008100d0209110b00356021030101c0c1e0b10305401000c10142d110415042903a00c5400722140201d000469000e00c074044500c0403102c5001c0b201c1e4a5680268192000342c4800c2048441c000c5403058054010f050540d0309807010700c103040b2404404420303405010390000300500910f06002c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 118386573 1250 118385323 118385383
    0x1701062d02070501020616091703040b0d050a0f090f030806030106120f06060602060106050a050913060b030a06050a060e010e12030c0304030506160f080a1d0c090a020c03030609040c0302090a051503 87
    0x27420055072160387c00704100000c0c08104403000f5040c00c0d15a9100040d46080452180703088460410004580c0c3d402d10081c407000c2803048060320021601810001243d40c0c1c1c00000038010641a00b12011252103026030405102140780c040507001c2c071581040260b542c44070400c1c1e83d2038030240324100000e50100940700b85a03204101802800001900d800c0720844d1a010000030340714079400503c0c0b82c0b8004401c10074010454009e80c0014501900ca0306200d0f400d0040051443c940754656174140036400011038060b45a4401e4902d07002c00d40000c1e41e484000d5442c40c95129405031000381c1c2c19200381030100710713007884191420141034101c0c0c0b180076841d01e00ca40156a855001010211005c2d03582414940c4a845d40710041c1d5851200c1020740002003e040801c0300c0c0c7c41c0c0c05000c0c00a2240305200854a40c0c0002003202e42010044490068680e528074201d0804030301030700002d4101411100380320015203240c124500503c03480040c494a0f420f514103040d601c198100d00300e00240c0103002000c2601c6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 118387823 1250 118386573 118386599
    0xc02040b060c1213180218040515150f030103122c010309080d0609022d0403061e020c01020706060e073e0601060206071701062d0207050102061609 65
    0x7110031000114650744c42e40ca0001c05d9250295026041c2c0d0005940e6080156001e192500310300d04880c100014105030055004030081943d0041c00b901d50340180440c07204241c415200d50741e00004c080c507503960316403601da0a20744203901424045914800f9510101500a9030b82034420901360300c03400c41d032100400442c00f03055400c00586104038100900d001d41e0a4a010b4000034002c031010160342d8032070508000341850380560030200901105000200700040440444d41101d4010801141c3e10140c044c0c0411052941891640011310000311068400700640191220500881082103d60790fa2103207120207040441e0740a002505034009019401ca604140040c40d0800500724240d0282c1f4001d450307056040100c85e8100ca5101c0801000040c0c2d0400a4552091041c90014061000c004041c83c1000040c06158144220030640c04803034071400b201d005620540d80110041d00c025804060344417003441c02454014014800087c00415143c40380510b01c1c0601d548407a02c581c85c0a0850881c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 118389073 1250 118387823 118387837
    0x609091b0317130815010e0a02160609110904061a040605031507030e1203010f0602160626010b0306040b01050c0c010c05031306020f0105090a0201080c091f0c02040b060c12 76
    0x14a10109001c1843c42c03040002e1110701c400780070725800c0c65040c0398014196210040042301410300401000007909035082041001c1544005c1c00301e5200c2c402d00e01b00e10455580d00c101900302440200300800e101039908048001e8082558601540c2100c40c180b00036100c0c030b40100c5805074804e00d110780791007001c1c03054164006460b00d000a00c66040b5540e090a040c83c041c1c541608241c0400140445454072040f04c00500841c001040d2046070103841c03400d43c0780c40780304000620907019200300300f80c0c01c490500200d01024020200c52580c481a2284440d041035400c14085c510349a003050055008004443e0080030080003030080c8212035004440110500c3c100f100c082c00300740080c420024442081c1005818250060722020b90180c42e41030848000610300140303584507940740c60140c3d07008048607401c1a80380208982d01c01c3c000010511400c11a020121140710300043d13148210340c0071007907241951085806214011709902042042d02601e0aa0782840e004103c030701c00c40440403c018002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 118390323 1250 118389073 118389097
    0x50a03110d1211100b031c050f07030314090c0f1002032101030b22110402090d03030c09290304140a0606030308061e190503010609091b0317 62
    0x12000c6030760b684102c1800340801010129200d810100a101c01c1880080c0c19240407510030000d840c071500000b0f640c0c2030242100b1820348203401c21204554424000c80305200d0038071400690310b51352032400800520454000c10030051030400171a228800200e4110501e410007460118104020410400c2c1440341c1040701c405d511080100300b0740702c451032041211880306400c45225035807450402c400e20741001403c101030104010004160b9807140402c02015540000411200303644080204009128504074540d0164014100d54100744d41500403a013540744558a03205183d503074180803103110a14440c6d034040d14040c4445085c0b8407201038091944540601111030a01d0b071440c0700d1605004500e10151801629010280181500308003950b8002c00c0c25190790320414188008158072062407d0002c3c410400d520190405040114212003d428010f0003008000e5452107044010011450300b2221941c0882e80020901d00620071141203c0d00601130040e003459403001c0328943e1748200781f0041 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 118391573 1250 118390323 118390339
    0x9070312090815060301150605030c03060d02030a050706140c0304050603070318080d1b0203030402040b0a0929040902061606020706110a081f050f0d05030a091e050a0311 75
    0x24200410046000314200b945584005410440117250a64480308a0080f04a010250401185a0000480e9889034001180e01e89039201d02001031480058008069414880c401503282406404a0500100d8a840e15280e00301010304024502d5800b80d001c0f1821a07170402c0c0010801070070403a0055501208514000407019034080b04156218407c0070300b40d44050000c42c1010110641d4071961040e0030003015110b19841401c20001d5480c440140001d02468807940c1c03003c9241c80302c05049020300011380382030000c1c03005801b400c40c00e400e203081e200e4007074030303c151048140f800c0c10310030b00b0603d030b070003400c02880c02e4100140b50800403650300e4211181542009010080b602c13034490702004000300004d0707a41e5502c0c0e48200406100c406010300d100c01000342031140031000c14005850440c2d00c140c80941245040100184d1050070340c5001520718040007505107889948054400195445190044200190700030103203551042c0b40942034001800520600101c0c1c00c0041c80d41401c0801060a9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 118392823 1250 118391573 118391579
    0x10c15060f120c0504020301140d030c150b091b0a05131208070b060a050f01030b010212040806060112050405060c070f0210030506041d0a0201050c0a0f051c0203030907031209 77
    0x342641d54260710005018050440c12001c20400d041e8010080c03104071002c0d800d550510303840c0d420396a0701040703d512491288101800701401500c41200c00c07038000702d0b18030100040080003005009070452141c4115101d80c002400313100a6500c02c109214600040340c00c1800d0b07542d065a440c0d00c0900399420b50040307054002104118060048440d51160b20401d403079079034a00e05081500c1e00940441d03c5500f142109000d00c9d2a0030502c9030441c0d00918000c11030191180050b0300b48224030034000d00e0090700190220340400300151981c040d000a030386d52581c1c04002e50804040315001c1c4ca0082c019003100000c0f50040e6440c0018040c0c2ca4042c401150119013a540001d90039000910081c011985078400c02240e80b03024459001401880001d8200c03c1d041041c80ca629030200350b5009050042c00300345030391010010007601508650001d108021045542070840c0d0f0f40358a821400f540f0001603003c3d4040d1840401900c1c015295440140001030a42e500c44070726800c51110301c003c0052070a000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 118394073 1250 118392823 118392839
    0x140f10030e1608060a2016030318150213050901080c03060606030910050402011e02061902090108060d0c05190e060a150806030f010c050d0b0d02010f030e030d0501080105060a090605010c1506 84
    0x103010b50420400b0100c507c0d032061401409690002004030400000e125044021415224204403110388841c40145d444030120340c225a80420b40d0801600b100b0440c00104000c82c0024600c2c1826400b1000c48549a4850341003001c0751000310b8041c40c50340c100e15502e80c4c25030041d030442c40d0018814108134110f202d001c20700c0030764101081aa680182c0c0040280000c8a1640721002d55000c3c582c5000d501e400020f4001811020001d031000d401462903045440502c24101a200050540103000807a120164108800c040c000e43c02161500440480810050b02d48450000c04a0f007c0d03403400e0398501d410400564089100a05040e094003c800d402a5210801c1c03080c808801c581b41c0314640c80350800c4190710103e802039003116018041152600b03005d030380c0004440c3c80b03c000900e000318514250400d034078150b00400310368580b810b00b040000300d2000010b4019a06c00c010036a14140c002d0740d5501c0f440190b9040c0c1c861180480d25040e000c83c0811368806c010400c49500a0011450380d55034844 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 118395323 1250 118394073 118394077
    0x20109170309100f0f050c03220305011b02010f06051305130203100608120a021203040804080106060507020112110f070c1e0518060901140f10030e1608060a20 70
    0x1407070000743c10420102c607845c1d007003058091084180e24025040108a448850352403042a0388071184224018894400304580c1405801640d4440003d01070342c11918005c0d1101c500644049001d94204a0301031030103641449024201d400040c10303280f0b001403080401c4000c040140800d0391600300048560050385003004060040340a10000080040c5080100c81c28500c42d4621442580007c008004001c0d0340052003044c504040e008641e42c03600c85107007001c0c4512a540c0215015402c28000203111034021010f41030710b9000ba220001c02c520306c5102e203022075403002241084584244108100300c0d4450018005852080106556003a120b01d035840704000130074804418280202d905006504200101d0348911a42a008424904014000403072412050145450b02d40d0981c40725461a51a030841406145010703248d0303840d002c11440000c01611000f403c03145140f0405507800c8540b494140c424045544031800340c40343d0303181c124030750003e488503a089543e000b85040042d000301e102703240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 118396573 1250 118395323 118395349
    0x60807050702121b0301090c0515070c030b06040f090b040318031703041b0e06060313140a11010906080c0c03040b0430020310051015030603150504020109170309 71
    0x2001080e0200a040340450742c0500d604e4000d9040c900381c1c80021308442c840e501582c500304c030100b118403000450584c0c82d00402d18080d10082403500000140000b4800c010f0050100b035038180000d039080426242070750190f04004000107901c100042c040b91040202444000361180345a611942d40e88801641e6405241c010712078120000a0004020506064105250720040d02e914020300e016403082281000911085c050000080060b01c1030204000ea030b880300303900101141400b00c7d141d1000e0b95807518040125580300641d552a661580144250400c90b07402c0c2c0e5a0701d000d82c1e12081c4071880b580161441814912040c070003c20303050040005840900122403078122400541c00c400c60703a0300301c85c9040314400f001c0382420001503100803500681c9200007807404503494a600c0100184250036502031030449072044415801e0941c590020030480380101455041c06100d1a001b108841043e0341c000d0104480a4040085080e0200b5491003030b00003600382d0341044510000b06004244580c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 118397823 1250 118396573 118396609
    0x3040f090e01140408030f04020103020d05090606030708030301150509040209090103120905060f0a0e0d051b0a08060709181e061d09030a0509120715090602030304030207060807050702 81
    0x300a20a000824429080b12060f801c0050310141840d407a10b4480e880060200c059000d5080e000805690280d0100c8410014050301000a440d01c00381094407807800b501c50610038003802034009128a00001070301d058405803220300000540c14a4240c0d0154010130f142c580090302404000c0455072400c444a0080d40a0b200c403231104640c00000070142c0c10359030042031080070207101e6681015042d6007079500a00c01800d00103d0303007410200094245c15540c02c001d061f441104580390f440070301d0080b141000d40007610100c1d180d13611101480c1d01ca000488030300001a04504d0f0801c00700c0031074030f2020036150104000052303822100784048141e1849030240002540c82c2d400c03c201004408040303041c15101a100c1c540d290800309485070700c0f841108c2c0c16200f0080f0101b0b040f0183c1e61450408180800b00e10100c40c2015520040c0400015800c0071203404102c00000008600b80040100d074480c66156007e002550f0900340e056520680c00f5142004101042c0001320058a41c1307030414010107212 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 118399073 1250 118397823 118397831
    0xc03050115150f020303012601090503044b03140a120806031f2306010306080f0d0c03091518151403150d06050708010506040e0a0b0303040f09 63
    0x300c00d410312409010764000401003c3c800c030344240d0740e011040c1c81c103540058040f0f080c005842c0482d6402540780301c01004455103403450420070094008010021030b24411540f030304a0260090503400b0081c034118015002107508000c059082d0845400e00042c0d4885a0850445449454405c020f200802c103a5969030302903882e0400f842045052503884000e40d00e0001c4046c42c0110110791188136041c100401c141c400c480715907200d2181d8108042048420104420b80000315182d1414144203803109808a03141c0b0030b02154a08011800402107840800101946010808100d4803940c0c0028207408000203198040b0744481e003a0840f128100300c1e42c1da800c5e0f01c544125246850b0408a6000341c00e40c1e00100f00c1e048016030419001c080300c564808440742c076076681800c0f4810000c0e1203003182d9445a4552444800c000c41c030b510603406404a660340c008141e07254001c2c405540300c1c5004002260f10188006180c0d0741817074100800c17610f4041c00b52810699107141c20315020503107802580c41513484d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 118400323 1250 118399073 118399079
    0x81c150e0f06060403051504051c02010504021806011e03151206050a050106091202120d0801090b09060d201906020f0c0f0907020a0803180d020c030303060d0c03050115 74
    0x24290745400c00c07021158036143c42d20b190398440e91041c1c0d44100900c0c4403540e1b8000f800303000c1c09000003011340c881400448a103094005001307000b010100c408a204003502a0064481480280118032a510685a07460340600700c46a1640a03032180010208142e100c0240c43e4074492104031a0f0014200a80303c0c0d28100b895203014001e640000700120101460b02004204d03960b808410002110300c0919100840b241c54004110800d070340c482c055005100b010b110380022a804006d0074101d131002e180801c07014500404209503007009079030880c0d2000071000240301242e03a803848184002c40b40c01110946620703050100340100c5180180070424501c0c001308000440d018814000401042400381c807601c62010005811800d4081910f409220400300007088140200719483c0510b420031011500c91401c400005003903a10401084800c1c0101d044281e0082e000294492109000501860a5079210300a21065000e008803e459107803007084008040303513081c4550740c07003561051503405501d82 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 118401573 1250 118400323 118400341
    0x110901080a090308061005040806010b190201140105090901021b010b01090f0f03080c07230f0402090a0b0c010b060304050109060506150d050a0e100c030b0a03081c150e 74
    0x1000900781c1000c1d90400c0c0341100000d600551007035001c0b008441c1d1214001e1541c2e800c0b1458060342e003000074035204003000840c48001910107081c90300002c04280c49041e1030701400324280e420001740c0c01240c0412f00d0051005141403e500d036071050080c400107040005199601c0c1000c013024940e076441e03035514071002c0565644104210050301700461480f15452a2805544034050548009080f1250100e075842e0000720600c40c3c60020030b2000d07441c610b034140130b980d0b200300002e0020400c3d00c6030341c0f20303050b02d00366003030078001d803801c00000070421091036241081100690341701d000800081d5507241084d40c059640d0a02031030055010b40e0001505000302d01c0c11030200d52000d0405407084c151031550016000242d02103900000c400c803808140c036280c01407100054103203034501c0345a074054203400700d80c4000fa95000c100414a140d40900c00040d400051013121140d07070001030b000080401c03203420b00c0c000c0c8a8050f808404820b00c006011502404004802c080a41002c07041b00c00032414400194 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 118402823 1250 118401573 118401587
    0xf110a03060f0f08030f030c1215030120090d050c030706030b10020106080a0f020a0302060a0f030c0305010b0d09080405040207050708011a060d090c080d12050a020a0c0206180301110901 82
    0xb0402c3d100c001e0950070148003035980d00407582c0341e8850050000015401f0f40011054589400143e01d804c2080e09101003100c40007081c0c1c43c0721601035882c00ca4a0340c08072100c1d50000f50048015014946020381140a011401504010a448a01c503071b0312229800c1c0c40400440300204540e680011b005080c00b42008071500300c00c07a44500310780c145501031148503408241000b002c0ea020318200034400061010030004ca915603c080d51104020400040361504041442190001c41c0e03800c0044a005840c150116207080c09107001d07840c010311000c030b1880398540c002c4905902940409080540d10702c005800d0340e00208003103c054010034070412500034240542c030111050b02468040d1240790380b000c90b116020f0303120151155030712241198284500b6076004400b07014070f1400c4d680030780680310020304035038810100503034580e00c0c1c02c0c00100d101286200b41c6420902c1c5030b13259580c1100a07001c214141d00120f18411103460040482c0e60f9559091090082c19480600000c0d11500c2c4440050118 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 118404073 1250 118402823 118402829
    0x30905010b0904020303090d06180602071103060906060607080c0f0a050f0a02010507080f07050a0309150203040b040311012607030b010c0b0622050103060e0f030415030f110a03060f 80
    0x42e00e146001c3c0801030798048140c9007000007d550707082c81040c141c1401c40141c070002d1802e100c4544181c40203401d0088a0700108a0342e0f0084a00d84040380d801b01c10b040d40c0710004c940c01c80280d00800c000c500c892030250000c140040c0141415400c10803280c10f600c1c00d000140c101942c00743c0c4441d014034200441400681290803032103001c0d1015007416000a4001e10944a0080c2264030010b0594042e000e6041510030213074111085031a60310315031030003528400c0c00d8081c05541e40780120007000c48a10000459050b500741c0b17103c0038101071075603817001170110003032054a05120030b10072141a000b1b10203901080145001251402500340240701a0840d5500c02c0c0580c104000c6040c0310001c140d02584864010b00113485001c182203180007070803441181d0910000c02942048000000e01c69250004c1e40c41c4000e042c2074607034446001c8940c660380d110318400c29010000742102d0310308040c000d5000d4080703540c03003d8010400c80c1f01910038020039440a4500008a540c40e0341c1800354919509010010f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 118405323 1250 118404073 118404079
    0x50105010b0705120c1c12050a0902120307030c0f0203010617070303080f07050702010e0301021b0c03010606050c070e0601051b031b1618060b0403120807030207200a08030a030905010b 81
    0x30300f12840e0005c1d511a1b0750b10860fa140324581000c0490803a2040813041b41c04400401d041100d0700f4007490210181c80345600503845030b1802108445903400101c12a1001a45078843c881000c0ca140d540400380c480011050360b15558405001038001c941d9490fa1803915909030251640354110315019010100c0a4030503100034003c4810810f1440e0400100c640d080d80909008800565407000280a0b100e42c00c08040c0c210028042d40841c020000b0711134158241c00c078002c0c0300302611000300f1034060085842004aa0340140420031080790140c1207144c01c00320614000d85461a160b82600d540480e012510146510004428060b243c40214407041030801101510040551002d0402c3c444040e02607000030f000b50081620305e600259200f10010000c04051a0315207aa81c148040c218a03005042c01c0822407100000e44468800e1003241e2403554810000c0d009241229042c01c2d074030307422904640e00718140e00300108010400308090240c200d65a603000c0f0b1514030601d046425155005900c45c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 118406573 1250 118405323 118405327
    0x4120f140a171b010606210b011b0c05030102070b0604051302060307030e100c0201020307020615030a03050a020c0414070e01050304050606060a1416060e030a120216050105010b070512 81
    0x142c0400c00d0254840d1039075040a0b268605125207050183c000e18038512190300c1c201d00068040d4000094040300455245109051981c150520040d10604446180040c540b48000b481951054440c61509406100c90b205041c0d1104046822039000140c03e5903812442010081c0340d207014060a0b901c102c1410318203c0c5c0b0344c9940c4c04101e203400094022420300d500c400907012010403c22038200919400b038424040d113140f20074064002e50040c1c41080040c0200c1e00001c504070b200e5a064403001601400070007085a01e500c0480b29034100d01d21070710840c02209913010856a8500910144c803008004612a0341450340380039014a040085450500006204020100d4808a602030b8004010b80340d1540e80c0c02042d034200d84000729401141005100418a104c0a40441c001e50300060310586007000010780b1100001e40d01e0084000302c0001500010300503040310100d4000d0710284c04142585e01c507650017560b41d20b0956000b42c01c1940015030208809003030000411000c039030b403a510303101c80d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 118407823 1250 118406573 118406593
    0x411100c05060601050903010902060d0204030b100f0b0f0405040227030a020310050601020a0b010303090807050f060717040b04170c0907020d0c030c060e030a030c0905010207030609050304120f14 86
    0x754656000400301d5050000105503580c0c142c03020340102d010039900802d540c0c0c0d90051410b010000390054001034412402c11f40008155020b0032150f00242c0f84450348c01c801c02460100c603604141e0003054550702c85041400000b0f001e0326a0f002601c0c011030a650380c81e401c1c480d40441902840d440040c40d074429071206070a000540c5011170b8540c24170000801c08152a629075005078034041c0c050100401c800a0540000141503202a4142c140c0e4509415544d0030742d41c440030040800b4070b205800ba4002d1007002000001002969039030705c0e03a001800d803103051554800a600c0943c0040d07118500440c1000320300c1000400900c0401c040d04422668094241800c1c54025a81c010080041052003401208482450700983d064111903900440c14850400003070f00d11500ca070000b80d0280b02280c00c01140095160007210020191201a802000e0051454642401030200d01005407620701040001189840d010004510118040c0d09180151066458041d440c080384000440706504000864 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 118409073 1250 118407823 118407833
    0xf050c0d050901090812010e070504030827060c010605010306050402190f02010e03040f0e06040e061b040308030c04050a0b030c0901030911210120030a1808030411100c 74
    0x303101024018480080c16a6900b6800c60041c03961103070140c0341c074401107400b10910700c503824994103030354808030300106903141c800c8103035035031b0055010080400c44140030301c06407440c2d24400b40300c41034841c2489241c920f03440d001161f41c03a84110301c0100681d4443e90180259601409444020841aa02103242070440a403803100c500c2c46020b5407080000c1c0f941c038858024803d400610350840035000b074075681e2b0b90390108114110500d1107452411101040000ca06d0f02c2c191142c1c090300c0003501c0c050f01090b910f03441203880c1c9031b11039000c0d0f040b040d00901001c008291104051442000c00000c1c1c180d030f65081c0000c01410440721350004111510400401c0314031038010041c0c03801c61000382404180881e0601d001800000303540769540c1c002c9440710303d101050350b49000b5603920500110080201d0501c3c45108540d11614440c500007140c400c00202d0400d8400b980908001c48c0c444118050152007999000416132080d00d09840d400030000e898400c9290925800b2821561400c103240548596518 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 118410323 1250 118409073 118409077
    0x14010c0804110405090a0602030a020d0b0102030703020d110a0506010806151c02060a050405060c070e060402130302090406090c15020111160308040615080a0b0a0b0306370b040f050c 80
    0xb050055480d0408520590b0b4100104d00e80b10b507226005540303034503205050740001d410190010303000d05d0610b442060a0350022040b9800a90143d0180482c44e40311002515142e02a11001c04031744150004900800c405110143c06000c0070001b80030107041c00b001c2d004400c1e1400d131409200b1104205000ea4843d40010600340455050750034580b0ba40013440d0a96403405207a000580100000550320048000802c050065480701030a41a642d04c0f000c080c80120f0144c03070001c41a1076401c402c14005840e000d840d0369030052081c040440c41c02c910360740d41070500074954851405c46062103c1d10800e40d070203004401251030701da000306007410b580d0b2800c03800b5440c44400107810300074140085828840070740c00100c144250002141c51203641d9103882c9a503806c03c020207464800000b00450b15060807806004400d2400400802e5141c4a2005143c20745070446400b03d601444074944614004042062044007503400f4800990550304030184404e8947c46e01d00039056601e0082040f14030085102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 118411573 1250 118410323 118410353
    0x6020703030f030603020a030609060f020313060b03030c15150108190510080601060504050f03030a0c0803090f240a050f01060f02010f02070b0103051504030e040504030c0f14010c0804 81
    0x502103002e0810b103202036009003203680010f50080381040e804010300c0095086130402c3c5101c2c4000300494100422044101e00042e01d000300800000380c0c6000115030107030044428110000c1c29a4600b4040c0c6a54070700d4041d900304a01c070954000000c0003403d000166015141c03520a0900c00d901e850f0040d1150405000c24000710030315580d54003c1854811611b0800c0c2c05030486908544040d42c41d0400a002900300e0701c40c8a106458016240340942000f101340c502000c2c180e1100c2200040d82d98030f5a060f504010140202881003122840c0c840c903081101c04e44070072203480300d40d04119840c2d0040c1c0454400601076111a4140710500410440300030503607044440b18504551a140c4290303040f0b000d030540c40008100342d80081404010300150807141070403070b8420743c22038840803592007034100028030884025010a00b031607540c15080c145600107960191013850701c1c29000f6000d07601d000501c40100700c141c3c1c2904841c507040180400034031500f030002440d820304240c0c0d0310b096601d16143c021404 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 118412823 1250 118411573 118411577
    0x90106030903390303020405040b01020c0a05331b010e0606090a0204240e030a08030408090a050303030a0c0f0e030a0f0602040b03091609020f03040b0402060d0c0504030b100602070303 81
    0x80096400ca100c10034007924640b445410315800f0b00050070024060b40041c01051710640c613124211401c1d60001411210001001e04480303107080c600b408029800c0c0500800c4040c2c1e00c40c1d001b80082c00c000d030030341c403081c0e41d5180c4c8041c94031040e4102418407141c64007071480c621030303140100411351a0b400140c0564080d000f201c80b102540d0315042c00d030010f409980e00c8403807031826102060440406940090030900c500d1f80d00c00540c50760341e0040640d01d240307146001d011030748200b021601094a0000400c1c0b1100003600b0004119078460220340346a00449084081560301e020540d6190f500c014550800e4070545040701842d0a480002600c410300010000c02e90318004c5515800c2101580584005103100321a4680703d00d000100305441c0d0000281d5544c0c0000107041c0414054828420b9a40300d0300301003442400d640e21a960609103001c054000c0e81d00c070340c0602824440c440f0f02d00400c1100342e000daa07150b8649245107480481c2c00005000416107182da1582880019800103410b800c494140c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 118414073 1250 118412823 118412867
    0x403030f090b1303110d0c051207030503192d0506040e0705220908220b030103060b0102071e03060506040c17040f050a0305030906090604020f01052214090106030903 73
    0x349000c0d00d8200e851703070000000340600307403d1043c0315400000241c2824081e4055a07a4841c411506120714800c0740c0c8003d0102c0c1060000c100c0c0d250071980c4014140281043c00a4840c0d071442c0007641d1020040c01c003011460f98050071014002c0d96009080d000303e019102406102950769409496081c00e006003805400d180064680071310700f520b0f40010706119100200954051420003c1283c0d01840381d01c485050362445004801650045000c00c44014031001401c42e401c603942c082c043c02c103d4924904605c1403410105400d01d0204003200c8040014807400d030250715510b4440266500241460b20651811300c0c03d01d2082e4000301c00034048250000041102d80c1d0324544039400703d031040e5005c0d1030340c4140704240c0105a0480001e5002e031814101720f81a40e0344100c8c1a50f5501c0040758025001804003005207201d5000340c01402c0b0303000c8040070140d0848561046503200890b1a44404c0808180d201100040d05003c20254017500d0285801d0104a09640340505180480c104440050000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 118415323 1250 118414073 118414111
    0x303060d1e03020a0308160206041202011b0801140315040201030e070305060f07030617070501031d06040c050906013207021207060e0f1f180902030403030f090b 71
    0x35214501000880d92000719880500e080c0207595038941c100890101c0c501c400415041c1c918200880181441c1d07600405060303581c0c1d40c800e041084072049030401d41d03480746031069501d11810f1440e59451001c4e42e90356034540c546480c440ca0a10602035a6000740c00210030b104076100d014903800c2e0f1103902824081442410880d2003850121194809007140c0900c4081c0000c090681c05160302514140d40d0522000382c6601a41810400c800e0b02c2c041e0a0340070407020051540260071405650310300500f000c1030942e601d400c5500300031013103e003101c200703503907940c01d200c1440c0000031580c001a081c41c1191a844c4040c0f89542d0350801203a000f00240880400402108501e000300c580156000e00503000181d40c11541560f61480c50084101040c0800413840050814440c03152044400420344c10444400c1032440387c4000c0140b800104003c41d1003402001000200c125600510070301d00010382c2c0703141c5414020122b034101180c1c03000c0c981c00d08040310041581200c0361030304441c09501d03098400c04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 118416573 1250 118415323 118415333
    0x70305030117210306130c0c0f1b080c03120c061b130617010602011806050417040803130b040b070201121e020c0601080303040305070b0c0d090b01090e010605030303060d 75
    0x4a0b00e42c14400810751900c00c80d07038250140c006140198410384103400d2140217106d04001356800c140f0103000040a8540340700c041420b03007900d4820b00e03018094815000c0107160350910304550300d4222440700d5202200d04c0f54a8202041191120312014000c0ca08001401070007940342c0380013801c651001d22100400ca480320307003800100c80786141c8013220805501d0782d80d103000c0c0280440914010242d66014000200320340180540c1a0354040f00d1800031341031059a80341c06c02000d0284c01510840b1003441b0f001c4002c01d440c0300030720140450344019520340743c00b001004020446038100c00052001440108280000310050b95241c99090800302c0014001d01301c018001d2022854441d562960f811900351101202e80c010f000c0890f5035030507546a680c031958002e541c0c0c130068400500290007006072601003060f44101c1034000380f9082400d03140c04c0c40241c9901c1654200301d4184c031000101001004100528440d41641428100003407001e01d10b00000079450740001441540107100816499082003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 118417823 1250 118416573 118416583
    0x21813022101020a0305070e090405070501180f032d080f03041506031101030f091a07090306050403030c1e091707180b0a120c06030911060a1106010b070305030117 72
    0x200c1c01e40c00854682004c5080100500300035512131004c6803c41d450545c55061695006200d02d4100d8018a105480c0c0b000444800f40c1d0360010101d0b1002d2001c000ca5000d94011000d8000c41c01840701c2500c41a85100c450080440c610f0440d291030040070217000000d031350078240c07092503408203072040d01ca607503d08102c140290303000d003000d04440ca008408010451200700381c0306202020399003080b0718540040d0a0741210300d1000c01034514010502c680f000944140c0400b98460300d83c5c501900c0055407552a402034a0003514120f010030344070700040a1003a03000d004100302083d80a0340300c402d103011180103405503003039020303505620f010120040c01303615080040100030700c4236059504500420004201c0140031081440340328209140002800d1400f01c0847c0e8003264006115265a903d0010164018014000102d840b1801e9034400c2c90555214000780901c0e0420761541c40380100d0040345c40c0d0605005800140524409100070004680d004003642d041d105025144080300107170200d221310300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 118419073 1250 118417823 118417879
    0x6030504080d0903021606090e1f05060304061a040b010f03090c08030403030207080c030f070b0a12060306020a03110c070302240a17010b0702090f150301020a02070302181302 77
    0x1242000c120104040c1d0000311b6034407511210b01c510200f2501c514046550502c903100740c0c040c00c1141408a040300070245180702c108108900b9540d44a680c8001281c000d400c00c0f10700f13442c040d039205010301c4100e001c03501c1c0c4080c0e004200d50402c07080700f1550000c0e00130030000d01100d0815503124016010040c0c0c3d441030304007800480d011241c403a40d8038a0025a41c000c58081d811050041c4134555090b4100002c81054022901c030181c259181451035403003180c0c102c1410311081004008591207824102d1081801071f501602c0056511900410b010381500c0380c0340310030790649008000000203400c021a541040e0307941102c06060f5951004001c80c28809809540303065550001100740d01c194002030b21100c0c443c0f6215078001036a9948900c440c89000e1118081e40000c0a600000ca074021800d030b17800d601140628810903e07041c24008a0708980103051240e000d45c0c444002801945844e1103e8039002850304480e0000d0b181c8416000e25004401c0c00080c0581803200381d141c1e036550101540c0c080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 118420323 1250 118419073 118419097
    0x506060a0c110604090c11010501031101080714040611010b032a01030f0e0d020706020a2d0501140901140112020609060c0132090d12090606080105041a100603050408 73
    0x403561180084c038006c0090358042004a10800080026280107010300c43c1283d03000080d055941c15404015078810303800070300d4a0304118101d000e0b507000003c03c001400103440c183d03440d00f41501d400ca10260841e501e0608581c1700748c3c004040da40d40e25414015441039034045000c00d100710041980140c000c3c040c10000f501c01c0d2403c7c55000400c0703500000d0502e0101d05203034202c0e41c146a5800b0182d03109c243c042c00c0602204a201c1b00102030306288441104414800c038604409011141c8603642191110808644482c54600c01c1c2708040000340141c3c1130545154040c144554588080603c8403030f942d450080c001e1401080310005d80d40c8020544001e410410002c0c0012401c90920a003801070221072001c442c0303e02491980c4c0700e8a2040e00c01d10941854005203114150484141c81305003c07001e0030008981c42c1c011003030010300305000e403400402c84c00c000480d45081a1804c18409890355903a003410049850400c041c80c52034030103000031207145050002e06030700c1c1c9050079002403150031100e0751 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 118421573 1250 118420323 118420327
    0x6031d0703060905060f04030f18120606080c040c1704032006190218040905120703110708030c0a082107170901061d06040906050c1306030506060a0c1106 68
    0x103006103504190f000c20b00c10000d41d001070740e86556500c4000403d80d000307400100d0f20012220b419000b0034142c01c072000001040302c501d80d03a446001c0740e094224102142c400f903c81e9010841c40000b0801440c0f008001c442c07e00c04065036001c01814111443c42e5240d2100c0700c03002017014540183c485402d01c004410760f280040d060002d405903541030640e0010030b21010594040c3e103238a494400c0c0c4541c040d03480114040c0c403190034200405440344100039281c40c06007803000345106000000a1400c0381c0700b40c80c0c1e407245111800c3c80034100301c01c55200307080e181c004024005400c03d021400b590803503800b29806446960a0b1304041119600030200c1c00703c20003060500c04c0b0350342c03c4401201c1c0da4642c52415051956810203590995045115000c0030002100111b6484500c0f100081d0748403401400003d11104261562025074509484404c01042c00207072442c6040d07240340829001d80054141408941072480c0420682d1113452070840800505400110070006000100269240010084c41d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 118422823 1250 118421573 118421579
    0x5130b031608070306030b0411040e0f0a03020106141f020a020a0603020903012f0a170a0603020a1d0f040312111c0504051b0316030309060908031306031d07 69
    0x1000e4070801d00d0085040c11002640d180e20901a074815070360711240ca204181c48943d81c0306400122034000c5039120361540e100500e80d10701001a208042003410041140c88a40d040c00ba00b10b4a01e900804000c1e100041001525125168044580d401d41d000d449040c0d11228000c034100581c0200c001d501082c01b440008540780d064015104e13900d0120000c000c041728110540e504031000c1c1101100200410466040c0c41c03a00c81c0c0035003888002410412000e1100c20601c0303062072012203a05120715900e000a005608001208030060003500800c210440c01d072414402014030010012034884281c04000740805115026001900d1107000341800b100c00e401a00c400e4036004003182c020007002101408071000098060240129000b1001d4401703041e100c41d98841d54815220380700c1d01445281301030b140002c5813a0341c0c6802540607075106602e090402c0d5005000081a0b03000390710320381c0184000080d48003640015400c0701d40d40d0400190032a901c0c010014001c28003c0c4984d49805900000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 118424073 1250 118422823 118422841
    0x110a170307060b010c050d050c0114090f0105011203091e050904050f0c030703030507020603060a0e01080109050c040c020c0d03091e1505040303120e070306020403081b06090d05130b03 81
    0x2500300075100300d4007401000d071410011642c4501010001e400369021180c108200c0303000f0b1004080031003d1300c0020942580300001a8400c082c1520000d510303501144074151000d1007840754034050141c2400210f10901e45440c010401c000c54040c0c08004900040000403d684900c0171400400005c0e01c0e05215103007900700151070710489800c00300070740602c00300d441c500d00d004680041620390540350783e8281600f60302400091780009000c20380003080c1c1080810030031500640d8a00030030a400c0046480341d000d260103810284a5180c45c1c1c022401c0008840503181c003ca481e0300c0d00002902c0385071a4405c00c1c02c0807521b014032a4005d82847d0b00c00810a00410300101c203d20540d6080d1b07000c924802d184000031221889980700c00f4001400000c0312040c0d8160340e0b00301e607103e1000282141c002903140d4a0710012a4042d034011130f04954001110f04210341171b0503d907404040100c0241885180088504e6169604030f0694003c04c24006101080d203000003600c440501280c008150b12490202c40c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 118425323 1250 118424073 118424077
    0x11211070210020309031018020d080a17010e0402040c1e0e0126060105070503040e070504050f09070e010c0203190b06010816020705060d201b01060e04110a1703 71
    0x1c1e40a0240c0c0403451001d03d0000044501135000a4002e05846d1880e041180050403008040800010f100101030007582d603816000360b0355806904900c0e60744050040280501d41c040d030640308140080b00040003114405124030f940f0a806440c0824503a0346814211500180402041e031540181d04880510603408440c001c0f42e281c0a0f2550b01e16507850300b559804d8001450403031000c80200c00f0010f0b4455108001405015229000b01e81c142901d841085006103421685a00002d81c0803404004c68500700441e05848002174a121840d41080900282210440c854007810f01c000e00a092085460270000746117109021100024042090f141150381090705940b9180022202d8011540000c44120441c040d0070694008144041c0b50200b031102607042002600c1d00c065440c058112001801c15812040041005650b65940d4040f52404c01c01a842c6070995174603072410a00303001594444200c0c2d60003a4004004225078070651002684080c0c90ba0070043e490760080c0310300c43d610040000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 118426573 1250 118425323 118425337
    0x1e010b07030f03022115180a0c120f020d05010504180204051e180609030c190c0b0318100204050105030109020c07080307030c0201080703111615090809030127060209011211 76
    0x84080b181000302410840780c02c12401c0c03454110082c0401081c0310208e19402101c4414590400c0c0c1d00da00003400a0504640410703800503038654000581c005515101e00c079590150004603400c0004440104030700c4140402c1d03080003809240c0e110f0114510915120040207110800c52001c00c46141504482048060641c4800c8070351054901103000b6800c0401580c0003042c0303000c02803409003251640c1e40403100c1c0b00803090f00c00b070030080340208000c046c810045100e004041c00d402083c16200079450718200306441c41400075481400b01703020307a80e03109046034110340742c07010056110b1340e918047c142400c22a0303003c0400c6100c0050142c007016008040d0a500b00e0017600c40f051a42c4d2500320a80548001040c03075210040c040001810340788440b003043c0030b454014291a0804030202d8a540110341d8500006c2d10302c02c0c07020455103002c0c9024014042c0700d1050060300d240c204003009100c84010841d05005161617000b164500c0c01d83d105007903d00c5c01d0610b01d030041c40075241800859800c1d43c4601 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 118427823 1250 118426573 118426591
    0x8060106030603120c030c0b0414120a0e040b040b06070c0e0a050103020904030f121e060b120c07060905060a02030402040b04060506030601050711090702061e010b07030f030221 78
    0x1000040032802446600c0c00c50b60002c5401315400d4054404031520700e1024402c40c02c0c8100c403050346000c1201b54609a01c5944076a032040d0703110394280c010903d08201d1480072186000c04106064901d6402114040f1442d0160340c0403444104841c000707005001c10303601e0a03030006804255603040c040399190b44802c442c48902c1c5031101752507200300002618024080079401007078100104000030311070311034a44070215a2070b01060243c0340d08004e4003036502a5914440201e0550b084c030380141d156100f40b400400318030051034500000d02c0c203c1031445100502d481c1080c00007103600030a2100540112002551040a6495a01c4c146412030005c0d00300b514140d015034601114200c6508040c400c900940340000d1400782503648010044400e548502c1e01101d402d40c0311658045242c403610060ae01074100b540103010a85414064454040030441d100d540192050700100148102d00341120040c903018540002c003080c04040c150b0191003440310300e900411040000f00d100820f07204085001c1c10f890 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 118429073 1250 118427823 118427833
    0xf1b010f0201020901090308071407060201020309150f0103030e0303070c0b0a12150302091503070306020d050702060118092a0503010506010201060b040905090a080a050703030b01090303080711210408 88
    0x6603030102e00300d0140d00f880b00c5c0400c0185806001040b111406041010b00c40e4540800408113503070384c581441091750080015039008424001d40311014800395a1110b04045070041034500700640510404042c0302c05418010945a40055524144100d9004903007111111030080c1d9105018040d55008680c41000210710105862480c0f18ad0300410046c4154400c101c1d441600f035400b00038680c440a0040c6281c82903101406005072028007040c070080d4001c00740180c4880400c114170090f01c20091640086410a100500100c03026032140180e51030002000200d4580030319002c5512815100f102d440104540041c1210501034601e02d07054820035002404151103a20059003a41c02c5030203101d02d01c40c410300c02844100055404144d105907018101d99510007181c803840750070340c0112024000143c000640e01d0a05805002d0750480c0b10081c41d29400c03281c40d588005007c1c58000d440681008806080240d01c0901009070f41884050300c8000a2030901100c10400503038003d01c0f4940c7c0600030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 118430323 1250 118429073 118429097
    0x12070c180203070e01080603010e070315110304170901020c040e0a140607051b0c060a05041d0408030402060d06030b090a06053706031a01030209090d09060f020f1b01 73
    0x4a80280c9004450685584000c000700b1303401543c04040003003c1c246c01d9965130140e4807090000b0454234005501506040c0c110105041c4038009661900500c220000c0c402c000748000201e01011100c0750080e01c08a1507280c422210040342081c0340740200c9940582000d400c4246120301040c664011440b507624042241007031322425440b44800c4079030310040b07030703040c0300151042140705031641c0342e84900000c5d2407001c4500b0f00006d241390001940c58000680104042c00044449210b81070411208403204030186819030f5200d000b1311000340028020318012a4941c500001500504041c540c03290520407980341c50306149698880c11301043d21280d0400001c581c40f2588000e20fa2980610341c00d182e0b51071102c100d61061100380c414940514155103290000100300d01040285141034540d000c091154510700420130045c002504000722604519440c01c10366411810310000c0700c0301c81c14582402c82a52805a04015048885110500501000c15100b00c107016040c1c000318000d0b204c414104403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 118431573 1250 118430323 118430369
    0x3020904050901060f26010203010e0108100e0c040905010b040606050c0d091401180b030702071a0313140705030307050d0324260a0b010302030106060314130512070c 73
    0x8a174810642400e810030414000b002602c4290741440c0200110601c1d040c83c015031032422640241c0c084110501c0b41e070018030400009000741080b080b032103a801e025450441c03601c6d58444032040c523101d20450791410f59000700103083d0048001000010020003a26940300702c00b0f02254040c00043c1c5a0b402540031180d9424059038840c0152407a10344052099400d000042d108480c08550580e000d001040c0005118410000254815070695004e0541546001a100d61303103540b1011502c001042402081042110500e9002d2001c3c0c02460404071020b91071541818024a40c219035014000015014180130f0002043c0d21080c00c80c2d641002644003903c80d903089450891540071841d014170408119030b19a95908201204031541c0180700d549201000600d041d0303c02070120b410240e29801003003135181c20b1040b4001450302d42000d2006d40b030b40c0c909401c0c10720001000301041d0a15002d000d400c2c0b050030000301c0c80b1049020341b00ba54800440c02d1825180c2c1c40da209a5140810100745400940 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 118432823 1250 118431573 118431581
    0xa021b0a0606060e04020c1b030304050a060c020102070f1202040c140d060f06020c03060c070317010806090c15070f05070506270d20032a010e18040803100906030303020904050901 79
    0x19500c10064890b0300c200c940000140c0014400310327130381444103000204d055031718107501c07600401107500c9000080d64240b002904061265001401d4071000c00c004012080f0403014000059034102d90014a1a001c800265010000ca4a03686407804000c01c20a081024680c08201660031a045101c0100e560b103070700320381c0e8401031001c0319059000080814100c2c100325000e42801442414450301d1945110420726040340240d00071070041d405002405011503007031000c0c40082d00c0584401410380caa109920505220307441000345270081c00048542800400d11404019040c0206180d5440c042c0619240303800311070b0509131500118001c50141a1719064540100c41a4000f40101507045100500030810305405041505030081444543e0802816041002680300480007061360f07600700f0000420388911404100e005d541f402000000003881c24000c958450350002056030f80342c0e2000050031100225910640410f41008008070405030035030003610040e0b80648041156a584581c41703803e076 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 118434073 1250 118432823 118432837
    0x6050301110a200a080d0b0405061011030d06030503040e070f0905040902060702100f03060f0302030616090b0f03160302120105010807020102160f02150a05030a021b0a0606060e0402 80
    0x30a0200040324a040c060031507107010080c48003100d024052146001d6040041302134003243d0200340002e0804105815120702484454291360800032850994007140e45121604640700500c0741181e244c40d0409010012100c114440704018050039036640340c21aa41d411901a18242886200001d005648a42403840d030540d103594a99441d20710f003405200c020450450300f6070b00b100c0c0400205000d0f8440590703c80d45019144d8510000141c100e80040c01c079005600401051081a0700800141c1c0c0e00103026904500c4500180c07005600c19001a11884080c1d8000700b034a0102091001e0003203480409907104211a48502c04d651200c0c0c0c1084003284141c40540c0ea01e0b480ca00010b20a07940b0440c1d134107a101400303000051034503c6003241c0480c40d03040e0843c00c6440c01e0170601e80004605020004114251140301c3d17960410080c4200504603000081411381d0b0503501150b42c00d00c0c04070000223619445010015600c1a10050510301c0140003240240404540d486d21b44940e20704151080350f241c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 118435323 1250 118434073 118434101
    0xd05010911030f1b040b13090c030c1d0a02030603010e0f07150912150612050619020f18150c0c0108090309010504140406081509060a02030f0402100306090609060302010306050301 79
    0x21130354641c0304220041c02c28161041d0400e10805c0341e031f07056415510460b0b100e180038038001040c691131032400300700410654011045a290300b0181c410446502e5002c40c1d04800204400340c0c4039500e080c00f0a0062008880c03c420340d10a40c07403c00740302c1e1804680e04c03041d0703901c0420314261001c1100060765031030600d10036140c00009580c024130110300341c502c02007801d400c1403102050031a40d0300111421114421019140d43d081601403029100c0d2050f05103010b0b030011201542006900c50100c841030041107858510b0840b81c03900781c4482d030380d8180524401081610060b8035440103006c0076a4442d40000740c2e44c0455404800705400300000400e840007940143d44541c60581015041140d01d55961001500151100340200b05e114007403000ca003803c084804038015030301d0300813615450000c001d058198058410400c1c0000503030b5010b022980300c1d070166018824281600d50031130080c0501c8e0320021005150440100301800740303410050440303000341c0c0c0501205465504042c03c8a04052800c50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 118436573 1250 118435323 118435363
    0xa020f060621010b0a080106061b1106070c0305120307080601080105030715120c0503042f150712090f050a0b090d0302070b0c060402040f020a020c0f0d05010911030f 73
    0x540c0081a1400040200b006000440d44c20801008a03440c90754681003108981d440791003d00050b07520800303000289908168030403040e030407a1500400d0795a1303100c0550050500041d6802400b64512250005543c084101e494501849600c41445e40040d41c4080009000310003192a03980700c0c00c1010705880700280030b0508a440c1c0890300354030654852800c81030040b60b4480d103644200d2445120300841c034645403283d40c2e281030f181200b450180d80e008003640442300c000860158182d00840c8985007001d5510b00320740000384030400014000c028000304003180309504080816032192501080f00c20803107051441984540400145103140d02820000c4007081c00b00d0481d030b01d01440382ca0030040c040d006650045448040c0003c00354400420300c85d603603000509000440c2440c3c1304400c4240c20b031280450811803d04c9009486041c95000c552040d0b801680c0c1c1a01541c0307a030000f10103e98060000c000f52859880c0500c203814100c01103074424050f020403220ba40c3d80c085240100f0307180c00c04280d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 118437823 1250 118436573 118436599
    0xe0606030606040c14040f06140a0509040c032a0f0e0d02040c09050d110112061413060f0801050a0c030527030f1b07060504050609150d050403050a020f0606 69
    0x44020302c1c06208080070000345c19031840451040c1c0008102400400d100500301504080020382820070501e09807030035207400c1000c004080d41c0700064070440d0504075004142802e4241d011405052003440d0b9200504080d400c0b41c201025078044121101540d0300c48508040c0d8403802030741c000024001094118607040411001031400c0d5102a0000b926401d01c23002164844c404a40762085420301155200c00680002c45a903800c1812103095041c04002844114180081400c030b183c006440d9900505588406070714514444d08130074040c10f03544016049072950b030291700d07000e000243c40481070030345000c24a9040368845d008080c440e07042b98000a41c81004c0d1840603000501402c80c41034140002c2c405102d0350801c55004000da41d5103840c4254422040104444c1096000c0d0300c1582406001c0108004c2505e4450688040e504100d444e2110300c507070740641d05140c0c070030300c190b09890764a080108010150000c014005190480d800c036002169541d008a94500082d605154480120b400c5a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 118439073 1250 118437823 118437829
    0x30e0706200f0105131106030714160204020a0903170f030103020603090f0304030f11090103051e01020d090302160f06020a0b041401060e010603110412030c020a0b0a0507060e0606030606 82
    0x503100300d0001c101281c54090b42455141e08465054134504d445805040d83c1d503080c0400b50540605040f01111840d01d5403c1c80100500040d031001782a989451010450100710ba40e04c00c00c1c415410303006401555200c6054400500c143c0e05404201c2e0000000051151200d1206081c1c810404600f080d85146900310703001c10000e0703003005159080c644504440e0342c04905081c8090b02c011881070744d070700900d08207a25016601c0f412040840c0d0084a06000410104800113944075100780c0403580082004042c0181501a1250641032000715040011007010140d00013130300c00d02e52007881c84c0012102d8480e030b851143c441491150500503070201d40c4180100f43c0d1511101e420900c10395924020070281d01d2101d0a54011384d00c42e00540319250010041190107000340e122851040318140e00e410b00346a641d0042107a82c4902038100304140c40342d8001c6498440c1e00380f004e050000e07406600c89401c83c1c4014030540c006002160080d042c288203010090000030030900175030f801405083d10360742d901c0c18 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 118440323 1250 118439073 118439117
    0xb0f011503020309070306020309071a0901110c10030b2809230601050306040603020d061b050705071802040b030c070204060e330a2303070317031b0a02030a030e0706 73
    0x840ac5490050900004180e02001c030750144480704100840c0d280c2e009000090421082c500c9901441d0f0000a0104100e955010003c00c480c1c00e903013400900e003480d6901003092018001046a00c007080c85440b00307c10b179136900340101111a40d15051019228003040d20700818402003048141056000100341c8660050016503803120340940000b42150381c0390004ae2140303050340350964285c0d5a4070898041340c00040b4280c0c000d624103080c03151421000b5134400360740d18481e20698025035070b48400e06200071180d40407140104003c10041d41c403414030140140c05540040d80892041e0315000740001c4c200315202034281300c0c03600c1061640f140b50f1222005c00c100c00e08000b500f554107a08444d181d01c240d8900e0410405000112030104841d180d1001c048c1608107040042442076000c04000c00c0020341d0050380210310070465610030340300d444502ca04803140580001d142116900441c080300e5856001000c0c2030600350964040c8401100369403a41d4880d541c50241c600080c0301fa101901c0f4213420145 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 118441573 1250 118440323 118440331
    0x51e04150b060406030504020114040f0e0a020d09210309030519020c040c020a030813110d0302030c1506010f0f050901051c0203010b070b01061707030f090b0f0115030203090703060203 81
    0x11400c2400c1c8000181e007075100d5005640866503a600b0b110565904c41d8901030314400031007a043c6450b0600c0800c201ca11880c8c07003194001d80913803000880c00000758043d540d41c95a445018029242140381a0100d10718104103007840c00b13051041320128601c070703009000d0401c3d01503d40c01d140010301c2c088032254111028000c001e620038011901d400381c50b0340c03007104501d09083d030150401c0291850000c002c56000b0b011151801940d10b10741002c91040030024110060480e003258002e001c0785020307401c40c0a41d444200b0140944a0640c086001a078001c074818402646d400b271548500700700075030786a10202c02e0240000e0050040c900d540d4016402426586450000503140707110320034807842a680260003541038024041640810170070075030380081c050602d90901c0300b0808045043e0784c1032980c0081204d001c0607210021880c9140480c0e20290714150000c0050f0744a14280c860035040800038407400e001d50052001e00303a00c1c40d203c0c0c070075640200e410001403d4641c1c51929640040d40002d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 118442823 1250 118441573 118441613
    0x105030604050403020a12030204090c1715010908011503060b03030a090302090c07080c0c01030b06040303020c15071218080a020d0b180313080601050406050f120705040e0105010801051e04 83
    0x81403620121f1051a5041020700940d079000da5202e003007155000964044440410034880104040020b4848440003141c3c0020190610040019a40c0c01200d00041540c000321040d480c00706e0408540b01c2944580c0140c0c2c1c000c500511840c02071707900b419981d10400400354001280d0b540c050005103045000d09400c1040340c0c1c03041d406c081c099161601c440e84840c8030740625a01002c0d21904a5030107010b441c058840445d002e07404c283c82e64a01a48814580081c3c81c402d4a599001c400032540c0c240683d84c02c3ca4020b0840762840e85203a902520450204400480030b61140300300103040c8a000510702c131080d60140c04c406941c1d41c55502c6030070010010302060301d0034000d1841e04860100410150400c03a40c0c0c00c180c0b0b18014940720240b4108038043e045180241d007858000e014685818094103d484015520b240c0d0806540c06403e0404295410040d8405d041210038001c504054024034140d0720100005c11440d100c0d102840d210002c000a081510083c810024001c1039014011011a10101d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 118444073 1250 118442823 118442833
    0x4021201020a03060e060904150908070b090a02010e0901082a0306070801171c111203010f0e06040506030a150e060c07030315060909020705030708030405030702030f010506010503060405040302 85
    0x210441400c1e038000d84164000a03995010400181207008071441c0c0140d03041d5184401e41c1015103130f0320800304200c80050327262a2510b2946040054050444e151150461120516420031141c1161203641903001640040d44548003500d607407411107481c3d8100c0d8220030050013212502500380d201c9680710000040c10360130070300b45184c041d14140036540c410b92981c2d03261403043d814440481080028400e00c0b81c4117501941190080031a0064458008141e6007401c0344611440c0e64203910701410104071702882c420210000a09954007490f46041e40c6581d030607681e40b40c0c1d4850901044030412034a865160b442900c0207404a48404107901642c80c1c83c56000c1615609020007520b0b24500ba60f0506102d074002540364280340e80b40c82400c0381c0f05429a24110344a1600c04014aa04003902662280300d80c00510308017008000c10481308d46a0340410344c5034172843c1034100b10f038a0f0f810480d03041c3d0084c0039801c1340c08450401845018841c1d901615405e046464500600c4020a0700403c214194812 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 118445323 1250 118444073 118444099
    0x20d0203010f02041509050f0603061908010b011704261204120f0c050c01030e030c01050c0d0c020706230d0f0506120312041202010209060a090f0e090a0b0402 70
    0x420701944090300b00c20200541d42d0752909a10072100303080044450204811036505000d40e030740d1804d862095041c1140d6244d103a49400000440c0c504408080040b0f401e03203184c0002f420201034004810555007601c50050f46505205402444c000844008080310a201d4401091800740500032503041100102a405c0000c5c0c0c040b56907502c20103650139a03502d003007040d1781070031254850000500503071a458140302c000c809a0b980d541d1a100c45100c103051549801028100c94004c00135101c544011038000c3c00103080c1182040503030350020007556440c1e801c0800e0400e0070381c00020380d8000c5880aa4400700340c90541448000c500d460158000e0348040c0411a80f170314191b03180505509500020000580c031b0805408000c664000034429000941042c040349c2e0305180744001d000d03400794000c0d80d83c0d03048002c200c0c0c1c228028881d903036180781c0c03001000c5140148280d20070840300c01d4440180c121180c80c2d4407184c08041100089500c0350160384a00d401d000040c4180c0c21b400c0c0c1042c8080d10030444201 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 118446573 1250 118445323 118445329
    0x6181203020a0c0308030609101d070509030d0809010608010513110607060903030b120712060902180103030908010501050f0d06021c060b090a1703070f030504090c050324030d0309020d02 82
    0xd84c0d4400d40381c8003c080107011491400c0c038611070b04000080310204260789000e2a205140b03202c02000d0380b0365015480094161805001181d941e400c000307003607400082c92140058440c200c180c84a41d0550b213445000f18802405114050140380b440300b030341c29a40410303681e0030f250224400445070040c005000c0c1c0c4000070443d00030003050900c0303a10003181c2d5403243c0d800e10814a0000d500d41c495544010410003082d01140d1040d548180c00c04070108454200e40003054405c0d0001d6011000d4000510000003410b034800d1b00310b815030303000320001c0c40b0a90b80d5500b003100c1d81d252110056440800d160f240b04c0084d865038002c101c0c9014400d00c1d0200c43c1600480707401210f443d94000130f030b07035000000c00850510700a240c200c0900b001090f03501c003403101d2184150f500c0c0185040102800001c007602c005050080e41628000c0092070014407000460960003403d03070304107961201002d0000c1c0c40c3c00109aa103000d40d00404c1a019005080c24400c1940482c00f0b007860070f100341d80000001d6a02c80150f2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 118447823 1250 118446573 118446593
    0x408070c030b07080117060705041a0912010506090f041101050a020f06090c240301030602070309080307120807020303091f061805060109050105040f14120604030f0906181203020a 79
    0x1a902e5144c86401d0341c54400d40780540a0640c84090140e0064000c00c0b0070384d6001415039090300c604040300907000c0c490031501e400d1440b038440340c0f603800140e4141c480040c150541000384283e0042e0b8680001d511803400200580c0b0055400034452035217144064401c1d40f090000d8036001544d407044620b0200c890401e1810180e054940300615002820744038514203201000041d400b1186c4e201100f600500da03d50039040c001030000824040c1c0000b500e00c24103114a81c00b9020702101c0d019039690b0112458040310440c0c42341c00d0000030a1520340001c3c84180044103aa01c00c1c0c02c850050b100c0c6444580ba2940301854041106088075950fa001040d641284403501c02155140c00780082d06003461000542010116400307141000810003040c0200c070f82400006048405001c00d0304203402c0724200040c0b83c03e20510101c5030601c5220200014141e200d410100203a046480d4804403039255481111519200011034049441410007000200100c038811144c03680640f042d5600906c180d40e03403100d18 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 118449073 1250 118447823 118447831
    0x6020304090213030f0b040c061713020103021e0903060f0705090d0c12050109060501050d02011d1c05060a06150207050108090f0a080406080702031602040b0117010902070b061002060408070c030b 86
    0x55070546c03c0000f000550000c200240c0114140240080420030f0040c10010008003034000010000c0032030710840e40aa015030341004000400c5910030488900c01005c1030300401c00d424800d1041c0d03008079000c20041c00951740100541c0c2c1d981e5141072800024001c046514480446803425000000521641403200004196200383c0c008602a19942020001e542040e04158480c03202c00c085280181c0e0400c1c0101020580e41203181c4200c0e00410006080d208000c40140d00740c560190344000304100425000c1c464200709500b001140e84490312100445008480c07034026901a0901380829802191402e911810200c1291100401005100d007480c1c60104200d4000c100441c06110b0725030030402142d0b100504d88001c60902c801c01021642d0140c10fa00084e00942e42c0d0304900d031325640301e6212421040c2142114090550303580c0d2148000b540410425500c00c0d4441c0040348042c47c0070070b019040380d18982d0003001d041c0c45c2e6450b400c51b598801c07402100c0e051068040000002c482c0d913461841 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 118450323 1250 118449073 118449083
    0x90609211005060f010e0d05120a03060501032d020f0d02070f020102070b0307080c0a020f0106031103011404020609010806190609030c0602011518020f0f0307090f06020304090213030f 81
    0x8251480e400700780c2e04040c101d54428030201944d101c03d641c2c132080c0a5024401214000c041d041e40c0d05029040c140031007204041c01e80001083c040094041d004041102d40c280c0e820400e01c1641910540454200c076464800186288437500220380c3c0743d005004c0360b1044045451801c9817102c070304412a44060f00485006d90342c003070050150b40c1c041c081c042c0204251044145107150000008080d448000d00d42c4074007038008501410107504c20000100d00c0003c071002042125180d00341341104283c6680345a20a46c2031503005802c0c100b1002d07406025a42c040c0500c3c2c106070070716006450429009001c2c40d0000381c0424585e030f1500c0e040782c01383c00401c000c1c1c55201d500c0b421414680f40c000301580284056a04207080100000ca0b6058601e0403501034100340000301402030000700c041e10845143c031441d60b901007180c1c640034509a000714052500350f26550b00c1c60796500440309181c1d03441d108100150b0801c0c002005106459002000c8010400064201442c0c0b40c2d43c44503031543d40ca90058031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 118451573 1250 118450323 118450333
    0x110c0d060516020601030f060f06030b090604060e0106030f02090c160b07020714060306240408030d0e0f060f04061d0a111e0d0c0b120a1a0609060921 66
    0x2d00080c084148000081d1880941651360450700c42c11810a150103006000d2903071500e903801002e90503030115000c1c55000d003148105c0c0c140644000c0d40ea24094500b90f40c03081c42c0946030304900c5414401c0f081169440310b072802c050741d1940c00304061007000402d40d14540e40308002c044a007040c2c0701d4100300701d02c5c03080e90580503038189940001c4ca01a2280c0181d1039489a40030603944035901c40c2c003a03a034001d50443c0c0403100110641040160b4003070340a01c4074419000410089940d22007c4060084841c55003010802e401444a071195903403907120300706170300ea04240081a17080c410001d100780c0c0f080c0103480219400e00301d4102481c140c43c0070502c02540d81c00c01f12501041241203030141286d03c10441f2001c0c100d2031780c00811803102048a50759481a00e1010800b01080215144c1800078500b0008464036007980b0104500402c030308a903044142c51030180c00a03103059003600070074510200508014104050603060002a60100083c0d6034000d52801d40010100442148070198440341d0300500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 118452823 1250 118451573 118451581
    0x5030a151a031015090f06140906091318050114010b03010303081302100801060f0e06030115110307060b030d08010b090d0f020307064b0504150207030b0108031207110c0d0605 77
    0x1128000040d080941046a03035160030307000c035850b08295000508104d8102d82cbc2c4410103000114504244901c04206a0074281c6280d80c5e46032a8540000703180c080e5000303109420f10283c03107500c4408240a90940d0450030700040c0301185c8140707801d5501505c0c20388041407164290300014601350382541d100c4c00003007440005001003940910100f40703040b41410447d01c03171030901000442502050007980354019803140d9890003940f0940c241884c1c051004d042d65940c0a071030400d60054100c495890740a44548988541d1040c8554600c0d030403100c2940b8200d05048007182085080104008182d40b0203070010000009aa014010b0b07000900761900c542549484800700e200c0c0200c2e0301d40407400403442400000d1842d0b1144404980c01403544003449565080031402a00d190246400020b600869802050b26040c3c001030403505890103405142501e03a41c83c02d41c81e03601e12402c0d46404500182c40c020484007409a885400040c0c540000d42d8443c402c00740100704440c0c04100c094841c1d40e140d4040c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 118454073 1250 118452823 118452839
    0x20c090a0c090b0d09110d051b01020c0406080601060201051807030f110301050906070207050f0105040e04020402130801050a0f052509082b140f0f041505030a151a03101509 76
    0x500c660000030b541c240d011136000c5e299642c5840e222000709c040500800076144c4940c0c400d00c21016544001881046509e0311855125a07410090052070055860180850844400c041c2d01d1250305001b8801000f41e58150341d1501140301e07010000712150070743c84000c1d05642d9020b0080030300c15440100100a986070415000349045299030001e80202071612040406991007800c840c15540c0b2038000710031603180c510108000380300703404031029651415440824000c1064021500845c5100d10511003e14014078040071284142d64a4013807449240741e04010f007081d801981c1d01d2079241e08101031709035521606079041c10000f445188c0700044500d1610b00740104415003806104079031400c10943c3c0c158039501f00d00e91041c003011080306007000c94015031843e040c901b110090711458440c104000c0400101410740d030802d642490203907003400e01c5512080e138a94440b00407240001c044d05940c0c400e400303600225502c0544002d0051440250100309041c506410701d072400015a03805604901c0c007545 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 118455323 1250 118454073 118454093
    0x12060a0b01090503250b0418060e01051c0501150f03050f030a200109061125020310110d0e07030201140c0303041101030213091b020c090a0c090b0d09 66
    0x1154184502c60405000e00c2d2070004181403100c000300381401e60001303000c3c0c0001c030701900c9074881014202d000070301003190040203550303403541a4099002c0c004180c07280f4400603520024040c1580001551408000c9815004c2000c01001d0043e0000299864420392940c409010350b00a849031103008601003041210420a4a1220f52284051410035542200061481c0415501080c030350540c1084e41c11190300030f5100150721a40326108009400100142d01e880e600956401c104000c280c850700c400c0c0d010380c00491928164000c01400160448403030343c10007400c1d15600c2d000c80d0702c01444500b00091452280c40041c201000080401516502c0010500c8098005142502a090001c00b696400010030380341c20550260724904074020344001200240101104a044071600c040d0018507840607500138403400910b4120f00c1568002540141c0c0c0d6480d01c5031305640c002c0e080c100000d4240c8855840740303100303d6031450b02e052860b1b9a40c03588052600001c400743d5965a65244100070046001a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 118456573 1250 118455323 118455341
    0x1104060b090f0105070506040222020301080c01080703230c0702060313060510120809180a0c020706031a0d060b0d080306010e0411090d1704120203010f0504020a0911040512060a 78
    0x1070311034906a403d50750301f03880f0301010300000e014014840d0307003002c0c0f40301406020340400d02c2280115103d41c1e59002032550340200d08000c2c0d002c104480040799005101b40500800d04044424480f40c000c40c0d5841010034080080c181d0f15241d0052000700c0046e96501e00070341c040c88000ea62405080d04504191044880140c00454801541c0c00200b01c0303804903003041c03491550040d07040c0c1d0701e9009400119a00301b0311510307030a80c04404481040840031040d0310804824440303a0031140304585902080c0e00300c07000201c0c00100301e04106a51803c0c2c0ca00000300d078a01d140b00c0c030070100d0700201d4031000c21181410200103c507079003404010400d295074801c030303159401c0c5000c8400f40410f80d0000c2c0031850510a103220f040c059030340000b410003801a11142002490401900c813a501d55603541000780c00844071004910030750030b00e201c13458000000d00415004540081580310154588010790300141141211444003100034400006c03507544000130501c04200d1a00030740010b2900b800488100c3c0d42d225 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 118457823 1250 118456573 118456577
    0x81b040f0801111608070501020d020409050712150b07020f030d090617010e010302060307032a08010927031803030509030607090317210702010c020f010203010501020c0108041104060b090f01 84
    0x1c4004d000700341400d001ca03002c541d0041105586e0b03813800d081c6240a0700c80c2011140c00c5a0002500103001071303255118611039840c560710307140900d4079211002c0035640e224a0310f00c4903201303140741403289510710002058203920040c014940c003680d0001090618403841c2829001c18a1842c040003183c1d003100003540501411680d144c0f01d5814100000244401808068058000800003a121600940c4500c0d0034001403100e500804001d8403c0c1d8420980b061003600c00218040c000084900d81030041541005061a0928040b04484072107005070418810541c1003001e0b248241d4007200003e1091405107001c2d60364683d0700e240c42d0302414500344004c2c185204000302c00c0d10410201d00c841c0d40424071110030360030300da58401460270050443c0c018250000c01c02110007080c0103c490b0158000720440c21990251010303603241c0b003201c900300c0c0402d1280c28007680100d40d0130300a40d031140194a92061151150010083c4041d0200e0700311805500040341e01e410006800072140351521591280901c24 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 118459073 1250 118457823 118457827
    0x21504170a020901060f030e07030506090d0203090d030507031202030c030604060b1314060708040e040501050609090712170c010605040b042703090e0a02040f0e01050d03081b040f080111 82
    0x303940450300401c1c3c144141c42c10003080030b1402000d28440e800c4010074107520f4007201c4031180c0f42d040681d103a038030541d1040103502c6162280b1b90b045001005403071000d0402001800e005c00e094600303444940c4a41ca084041140564903c44a44d20b18405140122a4900442e44900c0c1280500c821190035401a001d00d5000344216100b0100303400f900700644416030052a003501000d40070a000e4020800020300d04000420081440e00210412038071460140c4001d00c010740310385007488144901a00d25486541000c407090101d15011440280241d100d004c070702805130b072200c031981c105401000c00780d840c5944441c4100700c0c0f86450702400312200011907040000c031090349240384500585410300720101d9444003501c0e00703160048034944010003003851600158038104030010300961040c010f28181880c50b9a010030914001e07030f0118160354015240c4400c22817070751003c2c0d44840d4001c3c9103046030b0b450a611031303064540b030002600042901c010031203103190419817510300750346240d0002286120700b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 118460323 1250 118459073 118459093
    0x2030c0624120d120623090606040803030a0506010c0b010602060709060206061309022403090d0903030c0f11060c011d0c01050a2114070f0201152102150417 69
    0x2141c81002003016040004e980340011310242c010748016480107001061306907074810f8503540c080f482c0c41340480850b80c01c015561010108031860080d8040d04120380e0051000030041314040d4407070303500210705040c0038040820640d03410242c41001d0b000200140c10440a00001a410036415800b81505001034400c51407d000401c0d1a0710000811418480e19550614155101c0e080d0741c0200c1166101c0d2100607110b0804268020391056440f0400c2d4070405541c0c80382a07200c0e440035800d43e94150764031002a40301d40c81d20f01804645c2c02c01a11951f060700707030300c0d4025643d00c0000e004004445d80042503002c1150041c00403c52500502e0080e034001f000051003507079200707040354030a4040c2d0078810700110500e000c50020011180f04d80c1d0b11145082118040c8c42003201c1c0e50303407084080d5594061010f0401508909840c24011400b2408c46070520510014601a01d4402180300c171404818680b001500000c044c0410405205422a4006020b0000200c00c044203121114808020010284 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 118461573 1250 118460323 118460359
    0x60302010e040b1e0d0503030703060614090a030b06180a05090f0f07050402030403120f0219050a080a020a050f03040c0602070e040c0902030612011d0105070c08040e040302030c0624 80
    0xf9040c0220711100c903002c10000700d1603885000e0040806c2d00308007100e44914201d01c02a0041402c4d020b0100030841035030402540d4040e18040f9400d804020b040000442c2c42d55481401c4108094069a80285a842500010307a00c60604a100e0b0034201d40108640c10403680f521308280000505c4040c07600a000c10b001164000102c40085841c02e40300180d5070354850804641c000581c21000c06071030305062603e107000072250090044200c40031140d0516120724039081c2c9242c0f140e0f582c090f0110f80103000040362088581c0c0a0810900e240c20b04610f40340000d03080300d0f40c03603100725401ca030040c011035424802e03658104107440161102484d003c0e890b0800e0703159a05074449603c01c443c40daa40000024800380c0303030f41280190040500000344911030200e04090b905820003000c902c0c081d847d0000180200303105602d10a640b54101c40c285282c1400c14002c019131040007041582584800c0043c03704a50701044403901c10507445d0503902545074811000c0c0d004416540c811880b85150b45110082c0384 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 118462823 1250 118461573 118461589
    0xa0501020c100318050604031d0906121903051801030509030d051005060f0a0e010302090a0b0705150c07050c0103020a1b170a05040e0a091214040902070303060302010e040b 76
    0xe07404403454a40726a03942c034110040c100e030099070821400140c0c4100700300600017502c94040c0c1e120b6118000034132981c3c10899141c00443d0452944080014040382e00c5042c580340f208185c0c08031030242c1c1c40d01d0300714003c2c030205203071090811800640001080da40340340d01e441c48c0181e441401d2130b0074132450a04080b01c640c0d90040b500500c4071565038502065018001c00d00340c82c0101006003071152100c0c0740c01d40e0f00c01280c00200711900890040c9000d008158440d10071030300e45510041a01c06690309100d0118159044103004403220302c181524001c0e40c0c0344601e28184100050142e59030781d0390107840e12504020400381214107150060083c103000580043c00410f00c1503809070101c0c0c0b01403450400685660510803040c0c005c0500140100901c2d030300c10010000c0d80c5002e182c8441c3c54a03a20b88400458200d1a0301414020b076840c40780480a1088022a49400c42c2004680c24642c5502846007260305c00b40301140070a582d01c008104550300042c0f61002d4030801c4a04000460007213012030030036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 118464073 1250 118462823 118462843
    0x6080114071803021c050c15030c070c0f0801020a091e1512090803010f06020a08180a1d01050f01030b180a02160501050108160b091e031504110a050102 67
    0x84101c410101d042d1444100c070b03241c01990001d000d900350500840948055050211060b00c050045e80c010360360900b0080e81b40390840009910580c42d5980d2200005036a410000080b2400748983d100060b11031401c03807440000c1e02d4804001a6100850704010f40040e010f913005046070491424032010000f01d4444010446040a42c0c0300c021403100107003141c10828001c0c2e80700c0c1c00b900d01280c0c40103101c0b011016605a90314044d10900058072040181e82d1075501d100001c2c1555420000190745a100780e03900340ca5110040c10641820380c84440385041d003500c41089040c0c074620400100007502e0000401540d860007801c0c10401d07007407010301080000c18031403526503c0541c010f0201d40c0d40320040d41141c203503c8070080041d1542d6042d01d03040303018020038810184907101300245030380240780380d01c1c841d022280880813181c40c0a0f07021003801038070600e01c8074081308824444010312a5490500034600410108421003c04d80381c130385060030072000904511800713a80c52860522650760000341000c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 118465323 1250 118464073 118464077
    0x4020103020a0905130e0c0301110d0207020a03020307121a040305070308070203040b120f070201020a09140303040e01090c022a010e1207121a161b0c1203030608011407 74
    0x24600d2030b1801a208011a80d000070b800c9221000c545105e407003141d0280b0241c01c80c1c03e013a03400c2401800b0815080c0c4040c0710000904880400081c41c2c400c1003a8001c04202d403016041c0945c0700d582360000f90410300e665101d29078008032409400100108070b501404100503c407100c40a50516482c001d169002d41403005050018000c04105102d000300261030040242c1481e0350396034503420803512461501a22005841a0100d010031070301401030003522205901030307440581366482c01081800090f0205100c0c2e425020030440401c0c2008141100d6020788109000400c10301d1208034002d14002c40c0f5031004104e03c04600320b00184118007005403100e1582403034104078400722040000c0e0000c0c0c03025901c074503070300c1420740c0001c160a2100d0b41c1d502044c000c0303407020043c91100b2610a011242121800090010008942125401009170482002050405024240d03559030707007a003003035035542010407074040010507202015450302511001c1c020a070000c1c000c0c948803400046100c40b000c1e0082c0c1c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 118466573 1250 118465323 118465327
    0xe040303060b0f07060e0304060e100909090c080d09030b0c0d020d060e04021302042103050d0f051503011103070302070516090213080a05060a05060a050301091109010602060903030402010302 84
    0x4245442508644080e045807402c00b507807884802d24030304030ba6111100481d407890903c1e42001d000107000c025942111200d0b11820740440a06003003091005081c10344a0a1101c00e54000c17980420034402d810629104494070a5920b007042803003860042d942612070104442142c1c2480051038042d8101d4000300c0300399480c2c5d12201e20b00c544001901441c856190800d1501d800025108520140c4500450003501c614080d00403600e00e02c4103911880c010700c0758124400303203504614a6000f101854050191a10707a0800e00d414800740d040c2d0303119030071a000b007640301c01c140a10443d44c20080300b0408c80c00c078003c211243d15500600517034000100000f01741030380400e84070144102804011540c03074440c2c1000d503101d511401840000d4100745105490340c5900100880c0703020300001d858007607c1e00480101001d42c1e940c07010b500980401410075402000540d00000c513600c0900400e200b441c407440300c1c88108409603040c403040c2c110580c4a0411540b000091002040c00402103980054080c178000d6 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 118467823 1250 118466573 118466581
    0x60f10030b01020c1503040c0602062a070b041110020d0e090c0403150e061006170705040902040b19020606010f0c020301060b04291908041a040b19090c0e 68
    0x40c1c01d000c0c0001e00950045c0740d5018200881074200000d40c4500d1181e03006440c601d841e480101c0c1d80340030459101000245049984001c900b14106004102c20a080800c0c030b020119a101c40f100c0805440481d4451480c107070416007894141498210041644010200b1a04092008110b207080e41103c60080c0c01b220081030030314052004480c06160001c8400021a40da0310440700146a1040c10000d28082e80e4080f64400e25140c0840045807001c0d543c0590140345c40002c410940d202802e120140101040005100102400900000c2441d440302680790044a9016944220043e070044115080171080115076a0400c201d41d44501c25072800722071f02101880801d0043c0303600d8001a06400e0003080c00140f41000701c11541c0c0c000500d2241d003c000b81446d1a0701514000c1c01075800c1d0401440c1c0301c50346038034803c5010507070003805100e0300c422080360b420519140100c00d89040d105540d0b948104040070b80f481034105030404010a0411402d610368540e5906202d07103008050301300300050089 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 118469073 1250 118467823 118467827
    0x1f0f05060f0a0509150405090a0b09150a1e0606020309010905040204050d0305030a2c0c030f0303150f1905120318120f0d0504051801050a03060c02030c06100e060f10030b01 76
    0x9100405e0040c108009034103040324040c0c2e980d07400c0c09040b141c180040002802c030200220380802120340c2c1c50700308251601d132743c040800501070756190354280408510782201085043d008442c0203085540296549050300c400040440c2e405400c814004c5004200800150711011138401c80a901840d00d0394880e19513807826009002d501a02100d404408641c10065552028600300100890400c40d04019050014191940c100d210328103001e4000344000f500740100c4d05402400c01c04014158a01042042c000a443c103000c030002d00c0c00e0020700c11060050b41401c80141c1c10f01c03880c510040d41401050310082c0103203018486a00e00607560401e046030104c0d0200041004032240700143c030044402c040d802045608184a40c51007402c0c01410300d1418141b47d069103044c1c4402a102040c2d142c25500c42201903c10551141d0444c40104401c1060440c01d0028900499020800004151801640d81210080580b42512408a11014503c05d683e600d000808070b0b9101d0401045003c840001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 118470323 1250 118469073 118469101
    0x30503070602070c031502121e010e060a050607080a0e03030720060417010c030b0a050108010b0708220609050612040b04060e0f01050a200406111f0f05060f0a0509 72
    0x20000c6400c040311018515094000c1d0090001e85001c80066949009c0c11003001d096040c019507a484d503d400502100451080455000502514480751165102c010844640c0311502c281d80c00c0d01c02103911040c1c1360f4001030081006400700c00543c280405901c452080421600805503402044103002003240c032203100f6a4010b1201405d810080020300d40514060240104240006407501009407034914100c1041801c0c0c40c0c06944050050b800d001d20398505500032030060350303c102c081c0072010750814282ca41c2c0c0405034070187c0360b031145c0e46020009056002a41c00180c4a00420322085182400c5a40b01e0755016801100f400c001d5103550514000500003100ea142d034a005512102c01d00c00c03415000f042c021880380f04200542e0b415114140780034882c480b00000c2d00d80040004000041c4940c1d40581c07e4030212041c2c600e521154401d6580a020b06001481e00c1c68403441a000554200d2280382d9004105175586c0000580c1c00b40000d024005070f0040c14411411140810320165540c06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 118471573 1250 118470323 118470329
    0x10b0d08120907061706130f0506030106050919050901020d022a0a12051303020a081b0a060504030f111009030203160605031f0803181912020603040303140c0c070504020301030503070602070c 84
    0x20302304103801078002c81030b004d440101c1e08135000b9802c040e00080c0e5402c100548510441c50042d0360020180224180b070050000500818074564082c080181d03892600e10003008141c0380c59001304188100d22a40c0b4400c0d51020b001e9200076040b089522010555105a541c0c102c07255103082952030180e0358070032100c0e401540003c0d40010105402181c0c0980005000303010401c403103002e0301e0250f036680400c00d0307118060280300d001540905c8104001040c5102140083e440345004400004071034021a00241042c0c0f46100040c02a410810540c1801d0143c42030040c188202000d03094101034004e0500d100183c1030f961110506404c070051007042c1a00c10707000e401140f09803a03640040324204072038583e4402303a00c1c0c4030782c010740c070398044408081907102d086504802440306400707110b801304070840d040100150f040c141c6418060811050160403135105070007c0ca1001c3e100c800c00301d60a40381030480c3d08107900448c030410040c0041003001003900c0b0a194015005a90b5410b01d11f04020f401149038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 118472823 1250 118471573 118471609
    0xb0a0c110d0206090c0d02030316150e07061106060a170109080f07120206130f0807050303040f06051e0f070e0307150e0d0305070212010b0d08120907061706 69
    0x1500c01c2042540400c070705002d004040c00302d54940072801c0c1041030003e040070300203500d0b038410005003120b002c400708080c0784ca80c020315180040500109100c0107480c1c0320503100e00550010740040c400c6035048104c1c803d16020100040001c0c1c0340c01000b20310300798420301410503c0312504c0040280841c00f500807041d041e40c000b00c0729494216120100e03110b40c0000f0000c6802904005403201c06d144002986c61141c5d01fa5036095907042802e0b01c5241d14041504d2050300c054100300002c201142d010401903026510a070681104000c0d0360400303a00b00e80f80075105a0906404504c401440002c09002170b800c1804054103490544a485007507a05a1b610004e054140c020580c0005821400c549098562001900c0b0803540300d0403c02081a00100000b005010840500c01807003d810b0a82140080c2840750000003081001c40e000581d08841e0844101c400c9400000c900e60f100c103515540c6600089002d0042103013605020014109814002040c14002c20903c00140303155036242207440030710000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 118474073 1250 118472823 118472833
    0x9010b040f0605090703050709090b010c080c0607080a0b01090b0c210a140f0304060b0d0219080111040506030f0406091a0103050c01110c01050a17150907020a0b0a0c11 74
    0x2080c1480a404548980c0341300d0002e000c00295520701a00420b80b141e41c05a50381c41b03c0034100541c0400401c1d0f81000d01e03041054400480c0f0005450000400c3d152000c00021300042c070300380350020004140104644070250400c150700c031007640c010b080f4000707451909840a03118a070580c099403410403100510701450f040413040082601c4008010804080c255840303c038014462000300d219403141c9034041c01c00c07001c2000003d01140c2c0b10b51194101240081030201e00088680025442c03020720350741d801c0000d820640c2080f207600c0910529101030070100b921420603142c074001a0280c0001030402d10141c481074001400c1010341d51250b4001c9a00101140035030b03901e10000350600034240021520b522485020500560050740c2458410908100030011401600d0044805070440c41c10b030010310400c01d042e21410348401c281c5500c110300b104051294021382c442000039078800601081d0030354004100c1540401c2014107920740c040107007080403920040e00301c012030300300071b5881a031800da002e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 118475323 1250 118474073 118474091
    0x22020304031115010305070b0d02070c0b03010906050a0308030a090c030f0305071514041b05040f0902040c09030807060504020d0b040b01030203071a03041101051308030910030501050d0b09010b04 86
    0x410b200c006512040000c4403441c8202400d2114442c0e4280405805984110790411035100d4403802490b142403c0b4a0260130300e8074503500c40d00a148640c010305000d020210051200d0403e03403141d00c0060008a4a0700c5020303143d0b444009240c40045c20b65400e00b51178042002c24000d04120710b070011a0310015503100c000c0242001462034001103421203000d400c28034051b600c0b4005004140011240b0302c4c0100c1e65484a60300c01920b10003c41c00491640080400041d055480344541245c0140c02e02c03000c283e44040b0310411044980c10000f100603c031001005001103402202610b0300c0c2da80c000c600081c240c68900006d9054040030b98010002240b030720800080000c1e00300064126407080e000c03030702400d480d6400c07030302580341c680000000e00506200207030100d40c2d8a2580c0c40881018103200d86003000c41090302c4608039080d001004103920016110b1002c3c1480e1846400340d50007403808100c154107241c0080c00348000d02101070034071303d02038010403007150b420751150450070402001000b1140c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 118476573 1250 118475323 118475327
    0x306060c0a02130b09060a06050a0c05100c0c12030c05030a0c0509060304080909010b041a0d0921090905060d030e0406230a05030610061407050106030303140a09112202030403 77
    0x2c1810105030103036410b0008261319087c0f0b000030310151001510390508010600034100d800f00c40e40c20094490344280d013103030b004a420b40e2140c03065400c0c0036580c0703d00a81050401030210022064008101460a0080d442543d441010b90ba0445407818010030052022101150346004940f10705034040000020310040044840007064082d1041d9110704080e03a8a00040206014500c213803680c0880c0d109020b4000742d070101c0203045240c0b50304e00016000070300740c50303000f07420203030481d130800d8003c400b81999042038011400c034004051403c1e040c481840d00d100400c0c50101615401810300029280070641555650001000741981c20441c07404800c5000c0c84904c5c0401680540340070328808800070a1134100412801c4c07040c000120403445003440c10b40304681901c4004c0428404500601581000070000c2c0202c1e07005500035500400d803c2009101c401207114060301c40c000d0319290891400c00034851480d01d0940d400203c400c0b102c2c20600d010716403c080341c3c07250700040c0b09100000304001c2613 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 118477823 1250 118476573 118476581
    0xc0a0203043f03090603020f0d020307080f0a05100501030f0e011b0306080c0f0904020102070e09012918060a0807030b04050c09010b030c07030c12080711070b0306060c0a0213 77
    0x5100194503015480300c000015898600c6082c02070f00140329200b050061038001e400a2110349401c501191034000303201040c0c81280c00035200300c400102c4641c00d0140694620000035008000041c0800141c2007102d902c0301000c9480c4112030605454010005e580b1003a176010581d41074020000740076160200e01018809503512442c100420700d0f0803c00b10714600e001880c200c40b09400303811040001d80250420040f1980184101d0451003921404924000c42c0c00c1c5090040c1c5000700082211034003003010a00842d40c4044404c030301c0c02c0740401000250303525a507145061003140c4031008503803501c02c08035189442c5900008001c0c454100c00104114a0b0381d03445110f18041c50a0b9000d0440c07100c1001140e5030284204040c0c1d0b1402e1000c45e040049030401404024400c0c1010042002c3e55512400100003c180070b401041400003000a80c40d00700340d447c40e02640308c4001d03011803810640105014000900080c1c002c0e180450012039090080118105a580003000d00d82440f201c110701704058 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 118479073 1250 118477823 118477889
    0x80d050f0106030e0706091703040b040f140f0f040c02010b06070b0417070f11030a14030307020106080102030717040c03050703050d0f0207030c0303031503020907050406180302090c0a020304 84
    0x1380340c40d01c10a281e640204a82007540c405540b5030714001e1900c0e0b51040c103005d81141e49019404100030009030314185ca00140010300f403075880f641c5202d1074620721880025901d0780682c0100000c0d80c2c4010256142c02003414000422100092182110b00b000c03801001c05540150300290002000000c2c015042e40340381c0700b01d101c1c01c1246501a01991035054034040c0440c000c2108060f0046000020b07501c159a0303a11490140464031030443c41d40341c100e0381089480c885892a0400410721500903820302641000c2c03d2601c00940c40e40c01c08010040003039136010403c41d260035101012030f00f0001034a900070f00454100080b111030648070f08100d0341344c001d04020708012038140b6964008c2640046070b08400c030707600071900d1309205145403426005024401c0303006058480c1c0040200059441d20f140a0141c4501c3ea182d40d1140c0c1080c00c0940701068800d108200c50041c0d20082005903240c0c01c42650004540c0b00c2c9984030400c030901079165001e1030f0421101c0744080d051080c0e54181c3c03020400d0003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 118480323 1250 118479073 118479077
    0x1809231e010c1707020c03070902090103050601080103200a05060a02010e070e040203060a050705090d05060114040e030f1b030d090b0606190806010504030203101a0303120105010c080d050f0106 85
    0x62a46003100326089400080c070300d401007581c5000400540352a00c803004da000300240161840e0b43c412800007802c2a0340da0300f11030107091780883c03039481d1035070305100380d950108080c04c1401e13665042d80c4441909080d4809511203c1d903a4611081e5161201c4640d00d0041c100a040240c840c0400c01c001790103071058016800b00c61059500005039001e1601a00d801603030050041c1c070f0705450364007850002d4240140034000b4844108610303055912124040c55030240240c0141610354144903940b1203e951128219200328103007071040c0400326004c8102d803403200d600100340fa940c00d9001408820320481e9052007200b17000101300f44031507100c95004440d100b8483c000113801ca980d00301c2000030ba801000e211170207010b032010aa034051030081c00310503013003881410110705080d0f4960020b86030025540e01d5001c0a5100e950100015a080c602201550b104a01540c103041c4083d00c43c4414402c1445000c1c108a8880742c0d04c0c05000308141120302d000c1404105202d6842d04100088210703a0030b00c60440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 118481573 1250 118480323 118480363
    0x4030b06040b01020a0308070503061f020718150e0a0603020d08070501060b07050d0305070531150c0312090b090c1504050f060304330b03030301180923 67
    0x150b103600c0402e4010280341d0603200c4901c01e88030404125081d40009080c260494181c150082c211011410214669070069004051280c00e0040c0c000c481c00c0218021462182064100504a0f201e4030100065500100c00c200c1c040c0d9504031008017402c8580e002940140e1644007070420f11a0744030080103650701038002400381950b214090400c07442a24000b900e079401c50010b2880b07283c4a508490f4100c0c900f80340050400f01c01d070107092030780d010408821140059041000c41840d080102c1c86008007206010304045680d031840182801001400040c1080b8281030303001a101601d83c02280344a030021094030007850180c1507a40d885010724802d0307201e180c1c4030600068560090301204d003940e0020341109090b0a004081c05907903000600212852a003445490510182481c80003011201050059171b510403e280300404030f400e18403403103009800800050000c4c0701c151042000540d003032000006e0b503003603c5c101a002201000e0404d03c85503405165042d8440c0001032101201c6d40c0090400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 118482823 1250 118481573 118481591
    0x3020721120c081e0601030e0102030a020705060c1615061509081b22020c01090b0708092806021603050a1b05070902070c0905070207170c0904020613090204030b0604 73
    0x203192601e08a4072580d100c0312129094142d4413000000301c0c0c111030181408900d04007541017807801d90f00100e41e41210990b0204204050102c100460b94001100030245443c0c00e003400c03000e00720310f81c100501030110f0200342100d00134500d095200c4d0004104003032402104107010107001f000f80074036115011b060702c1204461a03007081c000c000b41500b020300070864051100c1c2d01014628101140c1145060a5800d1040041d207075001c3c00750b900094414107494400d0310b0080c00c00fa050f504003504c41c0c00749a11000318000f8640c11031050030080400c12400156849644c500000030b0310440421880a860300030880b010148c00202a02440441e52515446003000c4042c10a402541200140499010000420810046a00426201d4058542c0c2a01c841e1114801000e90307405544580c01a0b224080400aa80304020310b10400400040941419460440024820180688041d10900740040c0e103005400700700700100014602c00c04155201c5030781c0d00f042281c501003160300c580124100340102c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 118484073 1250 118482823 118482827
    0x90c05030606210c04020309030904060e0408090d0c0504090506161b081b0f071d06100f020717012004030c0605031e0a0207060b0a060f03020721120c 66
    0xe2031040744040c05400001d0070003142c00f000e280c20b0641902c164014000303a80100d440d40c0c0011486000c1110003169243c0899091000300c0d40035600952409014405000c0010804000c443c900c600032900c2c0d98005d9170505180580b060950300065002e4680b11540f4104040440c80d240705100c03502c2040c1e49610f8a00c800e49041600da040c060b40448415182e80c00580c0c103d0203484608615001d00c62007181e160700c807070325007241180c1c0e440c4980d00000040255a400d18070980e822144600015011f0610b207001c1802c0002810000c805e03c00c921070015041403003044044020314500c1044881710864100c03030b600a0202c9200f1603080c00710361000c1c460502c0c02c40f045404032a840a07411000b6441c08204031915000039114108075200d5900c9a501800b40d020940c0c0500614200182d81d101145000d074119622070744024045d00840c0c0b0b0800bd002d805c2850300ca14801d060401607a124110707e460310301401041a1216250703032a0102c4682540e101a58182991a40e0070800010b9242041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 118485323 1250 118484073 118484083
    0x180302010509030903032502060f04030606050d020a0b03090114070c020a1508010b0705030715050f15010504051509030609030405031509032b0606030219033e04030303090c0503 78
    0x101e4059100704070047d00c614811150501006000c2074100d4900c4040e0b0002c0c03170982c0000c100024501c0003080034010b00440d84074980050200b15040c0c2d10004095002c240034207010b200d40c2d01d89240210002e08018020741225030b0001656040c92214074108102130603944206500340e0203025208000700700c28901040425030714007552103001c01686003629405055009001c1210349000038407014000548228070840d04004007200810b0714a403140810a403100d000f00101c034540c10302c4403016072a0741c0100855044d104281d5001c141c4544120a006440c459040410341510400301000108503000c0080c0042d28002c40603a00d00b409410101a142401502c614503590410804500311403d4903001c298090500000460300442c821255400c40741d040d809075000c40d8000401c00306007884006507100c0710034181803c00103107d0200302c0d182072011030a40c0700e200001c0340e418906d0300344401003001c0c0c030318801c1c0d24019516512464000e0140145030412901001c881d4004030320740c40c010039 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 118486573 1250 118485323 118485337
    0x10b0405060a090504030203040b12070806061c0216020613090e0610060c060608060a060503010b1801090902030f0a081c090b061306210c080a15091518030201050903 73
    0x450306200e410038103c40700074900504200c0951104002c0000e5a41c01d0b000900252440715031140711500e8422000340c0480c0d00100201e10910b401c0010075104402c201c0395100c100005200182c03a541c42c265001c81076107520317901070b500080c08545810140310b00800790081c0d0760042014450741081843c8550364071000c0c1c8041d820030b0140d5005102d12803017080c0000c0620f00070000030403074690300c4141d02d0070482d0554940311426100c0c441172290b030a00740104c4060410503202c0c1c04000b02c1030045200526018003411400c251581c0c1910159a0b0803c0b19503403010314041626480805844d2007409640702c0d020181d03c04410352102e0401d41c0052041001b002c5d041a240021680d03500b08200d00d02c1e507403c09074030000365556004112407130458440d80b0320200640250140c4445410040c0b030401d615440341c0350540c05401450005106950098030007400d480d03022401902c20300e0040a0180f00320340c5141032914000801541104465245600341d00130380007000340b500c866030f1503a1203100d094 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 118487823 1250 118486573 118486579
    0x316020f01171302010e040c021b060c03041215060b1206041b120608010e0c011e051e040801023103050616030605030a06051609080c010e0d0f14010b040506 69
    0x81e075654070032100043d00754814503044c840f601e04200080c003210f102214030001640140081c0301c0341c0c84402020760740d6140c1101d82505181c6004105541d074800d6020300140343c094188244100f00765940e4041e42c006811009105c400d031240000a055081440f050b000c003da030401041c45420507101d02c0b20f40140340c000c08041040c01590650303030061000c0004070707495501c3d03500003031440c001c3c032420744201c2013a800740c0740403c0884001043c032003521110b140b140e11501c50380085039410a00b22201c441404a041004040b04c640721400c1c2d01490344403076019400003c480024031203601d800200b40200740c01e12240044031174014541c0c103030507000060041c0d01100c08111410001a04040d580c2c04610303000c01c109440d071002c01e08200b9070603c104c0701251a0821300200c407019003803810313140d40d892400c81100c52514000540e14015190b40c3d2741400445040030500391501400062515000030041c40c1d20891391402045038000700d048610103500c0c00801e030702c0354509406658080e083c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 118489073 1250 118487823 118487867
    0x90c070b07031805060f07020c0118140d080f0a09060e0306010509062103130608040506070f0e060a0c06110906030117010603050a060b0406060c05030a120e0316020f01 74
    0x400705a00a200c0c0c40229000921184880800500d0030042188500c030b081c49010f119091103480646001c40803401181807148214012054403001c8500360100c410000304c0c10b482c5603454000c00e80c40006104c0103002c114000a0507000c41060800414107000d07281d8a044a01d583c0e0742d0201c50301c881141c103c07075154115a00400c060f16281d880c8507048403004203660081e01c49016103a60f00400c03020018015080070500030b0310b0030f05c2e645000700184858280300c412450203544040c0c440030b00602c3c51040c010342d0b90789400b24500c0307554220b42010020303086a0ba1409000c201418070490300300d04455aa0524a080b42c0c507009000c00d450242202600c2c141c196400c02e4101b2403110440700b0405034543d620704001012030710400c9609020350040702e0004000c091082444140d4032140c125006000722009142c000801c0002110540c00541c0340421a60842050307000140800a000089510000c103260b40190030100520f04154400c8a0001510001400540b802e42e551228400c2420742 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 118490323 1250 118489073 118489081
    0x50c150708090909010605030304081501090203100e040303021312060e03090a061d090705030906010e04020d060b01020115350d12110706022106100e06090a090b090c070b 75
    0x4440f241540010000c000400c000e0b4031070001c6859504641c0c003858003903112041d420903800d8a841e4107400350a9054040d842e500e0640101c0c00b2202a521846252861000011b0207044c441d905440721043c0c444180307060155214114119074483d42401c4d03801901d17100e950350845400000301c658011020304140b20302c80ca8a841581c404d40080070100da01080340401e110280d90b125016445130003140c81d00b41c0c50381440c110302464982d058220740340c00d95040f820b010160341c2d038104001d00540c0c001c0c2c003c00c1f9a407500004030b02610122906140015003038001045000e0744018402c10980f120703550070b20151204044038404150180b00c0c003500d0300700501d29198288926150070a001036542c001c5071140c000711040109502001c0280c1d941a40414450f5100c805405030080d50100700060b2601400c0a00000703a161083d00603003018000c0c228843c2c00c158036968150750049800908902402d551a00050090081c00340914070038010003001900000d12241511455a0407401c419078a80d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 118491573 1250 118490323 118490329
    0xa0501080f15060d0c0312180909030e06090d0c060e01020c040510050405040302150c0a0807051e0d09080f04090e0706050406031508010c0f0f0c1e0303090f050c15070809 75
    0xc4c105816030350203034841d0020000c146402011b0030544030a942c5c1a0b0407034904000c82c2130320701d1282c104458284c00c0c80c0c10703032021039070003180740d0042002107500b07940c0c0e852142d001030344151000a00070180c0c0c01a01c4000b400a82081c1110403581080c1c01b9070b107450900c00104011035408507081e0203891403407081031156007010b07400030f230b0300c1446401102e035181c0c2045443c0d0304400c412100c0b007010110014607100c450b544180305076045401400e0041c1400c955002099221040300c0c1d194408031800701305055491600c1d002070100d5a080789007030f40c1d41c80581c20360f84060f40c414010661b0090030000c04162901c0300050400c11180140c0d01d80f030416061085c101c000d89a88621000d81c466080c00210701e25400b8440c0380c00d901c10070f443e40d00001d84049009000d0013054040e203801e014201240c1000700d1600040d400ca1912844030030300004007a450294024503404d03002903c00c00c007800c1c80c2000c01c003002032803a2518000b00d8a45401542e000540d00c254031070720f88010420700c410711035082682 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 118492823 1250 118491573 118491589
    0x305030a180c0e0402130e0a060e0304211209050907031a1c110102010e0a0b0901060b030c030f0901090218040302070509190b1215040f02090a0501080f1506 69
    0x84440c5400c040e03040a4880319180001c43c1c000048403500e81c020b1008615000c00701c910402c0707140c2800e1240500300f01040c1c0c0c5802c0c0c0107102a04594541c0002c0342c0c54070060041300c0180210076100742c400c1c03140c4c140b0f0074030082d03881c08100c1e4403001540440b132030300d4010313803030b80003110303402003030001d40d640d80c44000c40180800081a4210342c03051100049641d9a4100e450782d0189880e690740c64a00b03050903c028424007401c0940e0540e4503060f61860300710004a0352507002500040c210b5030340d4442007140c9004058562081c00644030100074802040d05000055006a058103500b80310354650f00c540300d0884401282c000c2d0f0142641e02040c6c480f1400100300c1d03900a019006850109540740049102001c0c111003001008003c44210305050348540314004800f0803d9882c507010280c400782842d51108208103002c3d0b1010880c001504000c2510104132840e41e01504500e11130629200c2c89010b0304082c0078142c0e00707005001030305212440000d80c009581400c88030324421a2968401e11041c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 118494073 1250 118492823 118492841
    0x301050423010f0f0e100e0d03020a020309040509071a0406051c1409070f1a1e040902040f050925050a0302091e01020c12070506091c0510180305030a 66
    0x90b54980740158411081441000911840c0e501c0101e178941035944401d041546006e01c01c0c0e440340c075200014001000014015040301d07518100103903151f441020507441c0d401403022051b030141c1844100b10080d0800b04040085610031076401c090030401c00301c0c03a0507601450207031307500040c0b00b0b04ca1400002c9004000400c20340101c4e00000f194214800081010041150b00d8080b42c1c2c00b1040401101040e182028006d04a203000a03200601222000c1d107980300b00250016441d8025034880f04070703400d0900312002070403152011541d07a642c40c00700e0f0781d0a014600c9854410500c40700000c0c1c0c0c500c6181441107000321807044420540c5207803030b07098526410403462101050b609001d010307029100c8100300c40c40c448603c40707101040f5909900091030100c40200c0c250040031043c1c290000d100b000202002a10000c079815030300c4007428000300e4804009001100b00e4034000086a20602c203011a40400499000300180074800010b40d03817403940c10000ca4010b0002d8410000100031050301c1d4403150607 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 118495323 1250 118494073 118494143
    0x507080f0706050403030e10090807020f0a0803041e050603040305091302090604030507080709140708091011030a0b010e01050702060912070305030406030e16030f0201032004080c03010504 83
    0x40075040c0d201d0808640d0100c40444c0070a0359855007840c00d040422015507a603860500a00903085560303926101030040d5000240201e40075429048659604000840900300d08000c0700d8803240c0da5201c807045498425401143c244a1300c401050b1414944e0469100726015110a40f0300460380c0b00f400500c0319a03e001040103a42071290080c4c6684031750043c00298014001000540d05040059041c58625480014000d01d0720f84040001a25000d495901104ca400e25402d01e40d210700700300713061a03046016140003d260005111070600c00da03010314000d4207000d9040246900c03080c0151010704040845c0d60204a05000c04001403901c80e004000812029190070407004203480303100d01d080310582003140c60390030214003400100ea00d0f2241000c0e10025070010320704481d00d40d075002c1280c4058040a010b142490340040196401b0b030700069034030254158801d0300c802800340340c540c01c1e81190050503200d0080c58690780036442c6c1401028011b0390081b01c21a0410f801741000e07903183c40c00f0090944 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 118496573 1250 118495323 118495327
    0x31503030409090309090b0a03120e040903030204060809060c04170a05150403020d03141815090d020c030703080a1809110301060912030c030509030c09041109070503070507080f 78
    0x552400e00103000100b04103a0b0100301c0715007501c1c0242c1120002e81107000c090b468900c0070074203039548d01c44450890341c0207004481d500d01c00135000c8404c0c44401107a00d4015003003a03008800c06605900410488009545034644c0b6240c040f0844d8590005442044551400340801e1040582048103e500c0c1d010f18411500c02410369603541c1c4c10404807005020380322440004100500d60180458030990495180070805d01500d0070061046083c0980000c0900c046501c1821004404000c001400062a15850414904130303a4070380c0da89071000c0c092001405078800120890800003166000c0e65071060390300741418040f040c201d0303d01d00c12808100005401c0c83e0001140d4a580c410300411003034621055540350305284014014103000c4c5c0c42526042103882103d0040ba070301c070301f1365441c0c02c0d418a0540d07615244180003074036040396403006a5004184406001c10409440e04210701c181d82a00da1410300e03a60107000351070301e00040f0707103d90100d902003040a0004031124010500d5814404100b4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 118497823 1250 118496573 118496611
    0x15180203120a11030a1d0a0905091b01030b031902010c02060309010b1009050108130305041d090c040b03070b090d06110a110105070f080a0e010e0604030e1806010503 73
    0x920704002000c145545003400070703620081039849441c0d01003010004004601d400444800189a44c144844040c42c01d00c403080c1032007481c0d643c4030f0400c0080078039401c14802420201c480d10f0300d81182c02d61181c003050f6200c3c2c5d881ca4550081c000c141020400030090203032010b8103900410416140740e0128100f16070461401c005a9608020394095201d00700005441d00c1200c007803080710744009174508203200081c64108607030303030740503500542c800c1d45a003070602030f032400740380548543c040c54200090f02d1804447c500c4041104101d0f0340c2c4500700f40e1b400c4401b9005900240001c82e1107920702150503400072442408030484140040c100310401a04c1c10b8600301042c1c6030741c011a540020154000540024100c04956011000701390285104008100500382103602070300c03000c18200510309022403600061b1143c0d946034050045545902c000348010a0209174080d00c8410807101140030401202004030383d4100f0082106400381588429203490f210000151a5078000401200d41110704103884 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 118499073 1250 118497823 118497829
    0x90d0218010306060506130311120d0513090b0a0b16051507020606040c1d04020403050a050a03270b030a02160b0604060e06030c040e03040816090501050301020304151802 75
    0x1404a6200030300e0114015415407820200f0364401e903000764800c103c2030040300350360000b03480340204480d40400808110405e0001061203001107001c9503a02d80503031000d0301d8010390031a004100441d08881036075001c0da1555041812a0310641980b604503d003c4000d02c10012007100910b01d40081030f08500e892022903031032034540f08401070b480c800540c2e000c05000c002c0d0f804022042d00b00c00708403400c0c0403004800b03800410081c0c494900d140506c1c0055010302c0c580d00c55504031405190080180c503252059820310680d1040044d4007207000a0340081400c01803070b4011003401004c0b0b4008400f6021905d06000b030920764101070050b0106560810803090141404610751200703a01c1220540014074119017080704031080d551010705140c0549080158540d004980d44400081c21100011202a40080d80307140d070240c3e811804040c400c1c0c400b108070703015042d881ca00c1211040780c0c050029031b880b00300381401d0780030903200148605c0300c045595440c1445a0407140048011103180e9018170099000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 118500323 1250 118499073 118499089
    0x703230c01060f0e07020a0204052805070908030f0301030b101509060f020706020606060c070f1205010c0309050c13020d0c08060a06032a02070b03010305010b1320090d02 75
    0x11040d803980d90b84004111032000ca5602c1c2c1c006200850701c03141c82d0b1038007400294850492400080c8500d5460000501d0070b001e0251140050614508030200010044051401850705444010108020000c00580800f000084644400a06544a04503440e41d554801d0368940a4060300c01850b040b100405d0744411910201d0000c000d40e9503038103516260800c060702101c11403d504003150040c20341440f549400044081d04622f043d40c06568502d0080038043c14440990072001510401c0b0000040d001164007075030780c1c00b60245000b0816180450016802c940d5002c80082541d0080128800e541c40c01a4a000741d100b032421b40545808078040341d000c12510148419070100c3c240c4828056181082c170400b1001c0d040c035007130030005140c02084818145c081510f42901840c00080d003030810500c06c0c17240000500e0785000d55504c0356141e15040d0301825182c0c4086004107200a2144140d0405e802108840d030080312041141d4040b11002d64000e60103d0102500842d007226018010b80301d12031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 118501573 1250 118500323 118500337
    0x124180902180a0501110307081803070e09060906010303080135010614030a02030601121505190e060f011a070c090b13050405100b1c23070308070323 66
    0x10088190000201040625000c82c2c04c032070304101c101c000d41030240c072001044400203500011a15103a21a8403a03620f116140d10802a402d4007882400046403182c449140d8056103240b01039400703c0e41c0341904199501c07400d1002800150040c1c3c0101b2600c1d40c441c0c64540700428080c2024041070b40e2501c24080012240c1c19842c0b169901c0000300040c07451003031f0b612003065045020701700030f8900b9000640d031000306005000400c189240020204010300940c5140801c0c0741a0a10062812040c034000741c00010310400e4140741081c98000c00c504021424074400c07240903400c0340384e590900041c440709020400f00030048020030400f110108800e12090f00003000244408508846081e017403080100036950940e030b50500b0602800000b402c0892012250307620030a00003200036016002610030520180320811000003140c4d0081440340000303a2855422000c02080300805213482c089940b1800740c400a082e4880502004000a100700041d0902100398560200c5141c24100c01000030761140b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 118502823 1250 118501573 118501597
    0x19050103120f11030a0503130b0903030406050a0c022509020f03061002030403030e130605060c0f0d02070f03020d06020f0a03090501060b03010506160302030417150124180902 77
    0x1020100d545540320200b5905240d240c942000c40300814000307141c0e07074060b03124040c0074060f0101c0010051843c2c3d1b20000e402c3d9404c5140c0340068100325940315200d41c820b99003585c905091800142100c681400f034150700c5001a4000c0182913412010020b5508110a0017541d09100d0040040d4400103400a0220005c0100500c1e6a0707050110801410341450040c030f2065410034401000400d400004140c0c03020001d69404c400c2c00303900801c0c1c0c00100425000903500c03040224580304804000240d05a401448104039242c000d281f5105a0b03481280340b14040006a24178424401414060090400355120b20303009030601c035903602450a590044000c1c4000283c0d02c5123001d0500c4003d0060000400360703000b03c1451541048040b42c000d2013504207642417200c1c0d0086040805200308126001007400f11f000caa02585100196034584a070a01c90401c0c02030310f0400414901000d038041c003500c030220a043c6000740c042200660b03200c5000c41c50b00b0f641c81058100050782c0e11041c001050801d15403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 118504073 1250 118502823 118502843
    0x9020f100e270109060f140a090507020d030510051e03210c010f0c091205070b04170c09090a030f0c0b0106081f05061b1e01020301031403090a0e19050103 68
    0x2c003108034440005a00884050341440402c004a144401506c0b059455406141e8000700854011445100c942e51011684910302400c00141503400300702080640e0310303650140581d0316039040241c90044180212a403020b90313941c1c0101281d0b9800750503815000c0142c1921008849010502c09030110070460030b641c0d550001d408000a8000c2c421080044400d0004102000240f48002c00c00c031100d009401d4800c1880b400c81741417000408c0348000400751104250f80d07554440140c3c0b0444000d00b00b01c100a4415904660780c9850a81180c5101c1e90080009184000d07841d1812039007001c1d00181c89082c06041507550b4007141000020501070314039901c2c0d810b61130800c943e4060700e040112021100845128002740300c55550b0904880d00c1c404200031402400c003d6040c5182001050764040c1c03003211a0490f40c1d80e400350190003443c120390007948200603280c1900640f6031a0310400700301c1940720841003428850340ca501c400164128280443d948a4280c3c1303035441c0c1044074420381080e1101820 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 118505323 1250 118504073 118504129
    0x20a09090c0c0203160303020c0108060607060f1b050c06150d0c060302070b0105010c02090115020f0a12090806100905100503010f0902030d0504050a0312030e0a0b040605070309020f100e 82
    0x3080002c03c0d00c425404032440d00d191b1858030000c3d112000c195005042000c10070101d01a66942d009032401c140c0c02036010046038402000ca08004d040b050781d401c0000148a00340b800a50290003070b1080c64580201030640c603583e031084000403d85110480e5131000c810705910010031640b80703007c40509095180160b44550604145c807031481d0591003103040002c1410b01d00c00603125500c841341120014050403440c150f120005904000d84a400301c0d0140c407074514040140700420004031b01000036512031003c10390320782c4201c070786072241207514100074003145000b01301c3d0f00c540343e0242d80d110407845041c42c000d83d203480c002400e4030550100203003450380340d41c12003095180a010b04c90b0540e41500b0020325141c541400704038130300810b1002906075008000c401544c0c0b40a900180d0b8010002c3c4140c0b1030111072407505959100040c0c43c1038840c3c80c54280000c00d601d0191041d503a5998009288903012403031103040180301003544040e8000c00111400b480215100c90303500e419294803003000070f0070100d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 118506573 1250 118505323 118505329
    0xa020102070b1005060a080c21010e0f0c0714030d0c080613060510031802090f0a06080115030f0507090204090b010201050a020f0301030f030e0904080307020d030c0f03020a09090c0c02 81
    0x4090b0000710000010f88080010355101c0d011074400320124240611995034808841b0402e029164018110325000c0c1c8606129003400c1c50168107039000d800c0c41d06815296268246600b990403180011081c10400c10900882e4001c040032000380098002c403442c000200c0e020900340c546240140300130810702c0050250501d000d030300040c0d10040c010001c2080c0e606d400c0c0080d0a0072041107003d03042c969220f607001080d14004a03002141030700582081190308086c2040e14901c1c0c001c45403184000d16240c000701e00c068041c01410350b401d03d014082e10b5450b0554407006c051a013645412922072042100000d00001c1a001400c020b04503400001442c54a220000e801e4850042200381c2d054410020481c5010a880613030741500c0d003210a40d0741d1400700b494240c9510b44075806c12613100a039101048101700e140c4004501c07414190b402d031018441d0b41e80c000c1e4260b0340050394641c04a42034400070340e50503102ea40508200421840d107012580da56000301310450300c0d0b28001a00003044043c800003035007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 118507823 1250 118506573 118506593
    0xf050f0108040206030a0e0a0602040e10210201120b04050103030e04060b030123060705030c0105071409010c03051e0c07030308010509040507061b0b0708040201120204060e09100b0a02010207 84
    0x8402030030041618549540042d01c244001400d0a512503a00c0f00c04548810040150002d083c2d4454011551035890340c41d0b502c2e10758011241c02028180c41070000c5051809410390704414111459129201030140e4019650714070400310680d10075070750b80c51007466503845000f0320780203500075195072400c90074960510084d52070300e4200c121285020001000519000e209500c2d22841030081030f140f43c054940015154801c500d8040c215110110f029041100103600542c09040c039501d803d104080c4554551056001d10030f02c050200c2c0042c001080464020310042c00103140d00140700c068907507211410003890b00180000030160b802440240100346e0404c00107030240004030b07207040c068a4140e40e00c95031810380d0301034201000725a040d424038815400c400150085e900869420141ca0900ca00030200c4104403010f0380001d1700c08619407280b164907c210717015500165030300046003044000b80201040043c19103941c8010345100000c3d800c00c40805003807801042d80c000b51340c406071400c280c4400707 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 118509073 1250 118507823 118507849
    0x1406190e07060918060305060c09090a0506060d05060102010b180f07050c0703060e0304170102130509070507110303070203030c07061d0d0b0a110406020d17090a0308040f0c0f05 78
    0x1a81c006507041c441103400019803411940c281552016000348503014070080e144a0303000608522a100a004503a0810406007038888016100096141e441e80860780a54000b5510326030401400c001143c650030243e000300340d2195040c000400c00c0d03000100441c0c80f01c1840c2c842140d00072692418415002c2c00000607035003080881c5841c03030074004c8600851b900d651203440020b280c81d40e03c0306035240001081c400c2d40d005101003070101c14212080203025010394400440380300e901d09030070004155490060712190141441d9951070341010925076a0319012001703680403d50602c410311000300160b40c2007004000710144003002e40391040c9880d4020708802c40290840442c03411025240400d40c0742c805101110940050f0003010b82e03100c01c442200200003180ca215104100082d0200b2240e4000a258030364900302c1c0d448040c0c03411910342801d0158800c0d00c1511854021064040c042881041040d40044c05001107802481542c1d9407152501c09031340c029602c607100c1040c200420302e4228040094 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 118510323 1250 118509073 118509101
    0xd030e010603021503100f06090501030c0306030b0a0209061225091d060105090301091b0e06030705010e0114030405011d010c090e10030b04110a1205120304140619 72
    0xc00c2d0941d070002d51620030603041d01d65603200110010348446000e0800c10700070032203402c2400d425500c600000b4040c1a4a00809020904000001c400c161081c492681100e030400000341d150380360700105401a601040b0322541c000001e000e000c10304660904024050f40e02c0901d42104400031180d8841130780c8044502e1400e11802020030045014000e0341d001c00b100489240e1341c547d82d603050050341c03940103100c0d04030780661a26411804119400200d50040da591510101c0e50f0fa6641001e24502c903021a451501070700000e00c01c01103035019516141158805050114660f000c1031a50055904100c0d000c1e14540c2d1500620210b042c040725901c8000c407188002840025182e01c0041c082c15a18890007902c0c10594000624034107a50641c84047c1da80300d46001c00f681071505006140007116a80f491045040080008984207103407085100c0a07801800b80504001e0f0648240c6d01d500004c0003a50a500580b0640d64056010300120748514000b00c142c00c11211821b41540c1103c00704d401d4550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 118511573 1250 118510323 118510331
    0x9050a020c0d050f16031106040f05010b0d08300f0601030b09040201020309120709150812160f0204020d020c0318031b1908010e2812200607020d030e01 67
    0x1040c1140e0a048401c3d45010a402e174603036403030900c1c00300e4560341c201c3e041e40d8031805904140410046070101074005540900b0003444070744807180402072000030000005101000400c10920702181c1041d00015a07814203040420210b892508080703880300480e101007030200c5200c10000070b580c06214080303001c9401d4412060700c0c5410b0740041d50b01d216000486105180d06035100d01c2c0c803c01004844050040d60320700b403090703a10b01c10030a6854805401001018050f4001d981686603410050b5402c0b003181c00c4800703001d9503140e100c2601c100300c0764100380c0e0491340070041048100a02d0004180c1240424021a600c5e40821958a460840c890200e0b101e50020301544c06d5019001e480700100d580201e8060030703041e0035400c0c90315003007009610061055007040d0b04030100043c08100c0c5902c640040101c100c10180c01403201d40056444080101101c8110304400030a0784182c070a1400c0c01d040185108010310250091071a00600711070ae01c0040e80904050110b1907454003d9040540101000380 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 118512823 1250 118511573 118511587
    0x12050f0109150e0a08030a1d0d030b0f06030405030f030901180809010f030b0f01031a03060a1b02030a0f0302070305070c090c030605030f0a12050d0507090e012102130609050a020c0d05 81
    0x5a0511000c0e10142d1070306d0712403103c4200c0c0780a850310002c1c080044000c89d22152010040500549404942c60344a0070b510441501c460404130708072803080c3e6004020710718001d40326400d40015000506104240e642c0c03407911101800c003014900e0304260140b1451521800024001481c0c41d04210362881054280000f148460712203070050103500c034090801041d09801c01444000c518024000241e151151700203110140c1281c1d409100702c6207419082c0301e1010129a001d036620303c202c80081001407550084044064403a90240c07400030320a1500a01e010050748541d00040100e40282c0d18955441001c001c4450701441a03000a0405601811104d44007084464687c642070801034000d00c00c21500c41d4405204508480040aa040041007503040c000d000601403800d0380555203c080f0084000300e000003e00d24801448500f012841c3c0070b4010701c0d4240810940d1550009003495100c0b41b010400d03a4075801854401c061030807006032582c3c0850b446500e094100390000d414413038100103238 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 118514073 1250 118512823 118512833
    0x4060207170406181203020c04020a05070c0e0402031e03030a15030b09060906151f0302120a0e1005092e06060e150702030601230607110a14010912050f0109150e0a 72
    0x1000c8ea060045800507280c0c0314107442500c2c02c0c451408000c0c0210591880824118186454140607034003d404480c24046892810823283c0385640d001249075000740f00203500b03c000f80d00941e240940030040c418405a4a03035402c80104010340d400c0c0202e401c060204880044c0411841d640103405190b541c411000000114807668038013902c0c41280e8500354101010b80f40660101ca80c00050316509224a19001111100621841030500ea003801092905101c070a41802201c0c0550320b04000b0b46104074041101179403c2c0c501034925081660b0522288104580c071b4414103004108503200ea000c1c0191410030040c9241e40c05650b1400400140030b00740160f00c0010313843d4152584001c07902403c0034900c07a202e007403030b03000b0784516801305002513071108000801800400360b44069400022141d1219148c00c240381c00c5504240c009002e04508000c182600108614014000c4064580c001d482d00030355401d450240c10180c5556020700300d495401490342c4a40c4609081c0c800180404d2401d507511 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 118515323 1250 118514073 118514083
    0xa1b050d0b0907150903030e060f030a0e1615022a100504090203010603021b010c0e13060e090f0d0e010903060b03250801060b030f0406020717040618120302 69
    0x2024200080700e000248442c24200144000303041480004103020502400060803003190307000440008509580c0c2e03444c2402e1231019a000c540c03254103103038150303501d10700313060000d01d45d910100c0043d1198034141c2c4180000030071404c001c0c080c0801d010084000e1400044c1c070b80318060062150703100000c5c400c2c004010350b00c003940c01c00c072204684201d42c020201e801101c0901032900451803c42c400000090f00503019401072868880310304a04500e4000e500e00710717080700c0305840202c0c0841e8120b038107200c1a00d03040030046600182c03a48d000072000d480d01d1800701140e40c00c403440c0103e68418100c020304c01d80300300500c40c0248151f140c2401d8004c4c4200c002080c10b00f05101c02084991100f0820307030f07150750600600801c10621002110304808060481c40c42d01f84e035105155080d4640ba5002c540c1c0000942260300c15a811140c04809884643c2ca80c2d000350301460042da00403030051102004001004010002402140d9801c2201c0d0521640c1c0c1c030b2991030b242d1000890704200c0480700700007600030903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 118516573 1250 118515323 118515349
    0x11060903160c030c0801020a1b02010e101b2006030919061409100b0a030b0f04050309060c01050610080601020d0c060b040609150803030f1801020f07050a1b05 70
    0x103080010615546400307810034000e83c000810700c0c810400007240651056014101d261810782d50307800d0000d62225001120155444064002040480d061a540c24142c0340c0004500c1d043c0b91070707001d014940d0030302d8a414400c41000c50301c01c408440702c031511000310341c00c025955500b21146840c0d8284040c4943d0b441c0302240e0000310045501e40c0c40c200348109a4000c01020500079020700592519143c0241c8840625100d118014503240b15010796003465007641c0156580242c0116468a401c0309000800d18000c0c011034591100704000b0003a600d03808094000055510000f1900341840310403c25104005081702040005e201e082004070780c0d00150358588074000381003400200c240d6003030160141002000ca0f6802c1400c1140c001004200f40c1d0049440c90140c566101c407150f201c500c00740c1c0720700c0140d5240c2082110700300410502c2048203440e0303848203202c0c0001864064030550310130f1076400c424410f1f105600005088030901018040b050640040512030b500b4090814001a501d504811 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 118517823 1250 118516573 118516597
    0x50f010603090f020604120302061008030412020f10080703051605070206210c070201030e0706021c02031201240f021b0a08060c0309070906050109030b040201180b0a11060903 77
    0x10b644810b010407028420883c640103401c060351943c8510078201c10008120044005216400c006080d01c140e6a11380c105950980b0065841c00d490004801c0d0401900d00050768004685842c84c84e1554800425201c100700e0f6481340015494040e40240072201c0040c1303050001c1070500150545947d1040496420950440d800c0b51942660700007000350180348030000883c840501d00b48180d9210110190124a00c04d070380c1032001c40307200451240c440c0c00d5441282c0169000c1010003148022610380c0741c007a001544101da051841c0ca4115460540c400c1c0e2015480054000710b83d0030103c100d001410790280c1d50306105072415050b06000f9500c400002d050300c034003a011307800340109541d03d40103a401040c00d00c04a800038100105812245d030b100343c41c90261840303451030014003c11240154821928140c40310403425145071200501004020000c9040105071120002640f0f01428403030081c1028880b50307511403000b0300340a0f1420307a114001c0e000c154405820821102d0000048134111078602d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 118519073 1250 118517823 118517831
    0x80901030504080d050a061e0f050607030c0803130204060b09030703060b15031602071d0703020d141305010c021612050106050303070506090105010b0a080f1b07061a04050f010603 79
    0x2d06190f60940141e04900700701e181420248900000c0c550004410344122a040312400b02038959510141c0c0c0103441004042c24520314200480d161a5025000040c000e0504862006590341c0308581079008132001c07500280c9030044103003907041030300c00d810190400210031031810801d48006540d0b401c032444000c24440c1c48681c250415121101c0c00e002c414000000d6035201d0410006007000d12015015010051060b40340c00a0160030549103043c1c0720100c8114440c039519180000c5001c1d47c8a9a41c0c1e038401e40d1924842141e40e030319000070b14401d0070758ed01a00d1001401d03150050a4030303408000403007154809400407055411043c002000c0301c0140411014200c0749150007401342c01c0701e40c800d9900d40000314002c400d000c2c000c60710a03c1103203100c0c020401c0b0f0381c80d8000d080316030060703407074a2000030101000162080803003410243c1000103030340181a00218110582000c0c0d0098200311362a907110340106442ca2540021050b0a200448040c4500c0c5806110745e2448201441264105511 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 118520323 1250 118519073 118519081
    0xc070807033c080c0109060203011a07020a120f020a0303050901030608060c0d02090d0c06050d0e120d0c0207030c0803040e01050a080316030e04050a1409010506210f0f010c1404030809010305 84
    0x1c0e08115a64400048006d02601d0410b040c0403000b501b017403142448204009001c1d4080c0036000046902141e4001e01c10007a080c2480001000714114180896500308400c1c00000503030303100410f01008502c640d80c0c16a82d07908400004060f82c20715031241000d60f01c86010b100d10048100c3c180d6404402d003440044e1a9000c0d94006614071304012000303070441c00f5201010450710703030001c0100b40d02486450148094192002d0303180d40c541d40103102c04860710052180a0201c5000d41202040d44444d2040301d090355240d4440d000002d4480d8008020750780001010012040302c149210700622048070500c1c1014a800103040c0c5070f10840c0303900c2240d0305010480208042c0182c001c0601030714044d10800592600b03908010050050f0340c0440a69200600050b502190501600b88541c00c0600491600640004c0b012081c1c4402280b4806d54004c17181d040310100410803540e0700c0144504000725034141c98240c0a06038403031080c1d402155180411041c00403680c440704a07031507102d0078640080c141d91 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 118521573 1250 118520323 118520333
    0xc0909071403160803070201140a170a0219120e0601030c030b180a050a020108090c1e040906140601030606020703030c1205040b070b01210f0f06020c070807033c 71
    0x52010f00050090400c010b0203d030004002020303140c1c041c403e894503400c0070220a0505040e00035030100f1000285180c0c036460304004100542038101090a0016080240380c0004030300c81106030b81d07240006022100000c42443d914000d01003000c0c81400685615411907ca442c0864803070b0002803d034a0301c00700426210403c002c6080c1c03030701c8418015240030b07840c02e1400d15100c0208000c182d002911510101d2250900481c40c0b08070007070003e02c0700001a4840e00404501100082c00d0b036401a0780d0080013000c503146001d01c041c45d0203424500d00c41850144005011602a03030001021035108000500001c1e030486901c0000c103401c1804140440384080048560388104e4114001d00b600101c0c0d40c404008000420390b040e2134000f82e003034040100e0303130710340c0c2c0c0e890405400040c4c04164064000c101042005010302c90a5018003800f610b801c4041021629109059101c401c6951200b0010021712889500e440104083d03480505e10b02e48144024560501010382451a10f00c452106001000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 118522823 1250 118521573 118521583
    0x5090604090323070302010f020307050d0e0106080a06090204060f0b0304080d090c030f0311010c0207030605150a0f150203070b0105010f020c100302090120070b0a09080106090b030c0909071403 85
    0x4100c1c0b030030320b0303400103050588031004e41008030100c5c055030808459075001c1010380280ca101c0d0302e03141c0e01d031800c1208074294500501f01c0c0c15070b1800349560301d58000c42c44500912a03050264018030313020034000414414032048810640c800ca12000c1100340a000c85483e0b174048070340154008500507100d00240c40110010143c0103401008844174500c00800c0280e040108200240a51510742454956440d41403e1b10292009400140c00402c010301c000307121035108507044148003010340b0355549118049480000b290b00b107002b6020268000f080070a02c41125081400b54500c040d600f000301554036000c1510341070241c40d040c410981c0d0b8014000703100304505408030340b0041110000d0b02844002a00079441200c0c0a8000782c26032580045c0c03070500b4406c10b10300340050402080c06038601110205640c00c00c5601104100c162140090094001d002c4d0720050f018180d070000300c0001c22000c00d8a40143c9407030541c000d840440030803468810100c1d01d17030112004c56400f95804a03940001a05103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 118524073 1250 118522823 118522847
    0x308040618030e0301050a06150f050405032d1504020d0614070815011403160c060c03050a060509060a09020a05160b010608060a0308090409080c010e25050906040903 73
    0x9640840d0741c031003410360000003010142c0040e0001c10840d1241c12001c4261600c48c001c0140c000e80465807411014072940c6400c1440b002440e01c1418141c07254002420020b280c1c6000103142c040107001000707502640b601003802000d0900a040c0051540c51510036800300a001a206d5031400082c90148001030704000c9040c40e0f000c948120b140b4001d0806802510281c80180b1001810266491154040c0c0300a001c580d10440515045507036449021000700031002c0c0c0c45007040000c0e00c0f05000100140542c0c00752074a50344005c6614546041440211100d03a030189200c0c5200f60309000c0b03242c840407039a0090740c0d400000945d42d002c03840004d8810380b15102500350b607100d0348842c00050140400899040e03c070300f030b90398100a80b500010001503405501001e0218102001091030718a801c2d403201c415244034400721402d200596803002c0c21035a01c10920300c200d400c20302000301c4030580c8800030051007216900b102d0700603042202090f04030600604280c040ea544409410904d801141600d0b00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 118525179 1106 118524073 118524101
    0x1008061315020d0b03060406050f060f010f2a080d050604020a080106030507020a02040c0206090c031c0507110d1202161211220b011106010302060703080406 69
    0x354401818004429569a0311104c940c805100162046008400000701c0d49007044818002c0a130003041640314610560480c100785e0313040003190080983d40c0c6407100b0f000d030610110304c0701000803172002c801015160b040e842c1082240301c0207081090f5080014002c50302c2c0c0310284030580c000c08282c600450510001849403510072b5004545c400700e80e20454890b104c264000c40c00310b400b00c151410058202008012085d042006001d0041c1c00c260b0017041f04c00c2010180740c010549401e441c008015002801c6014040c040c2042552448010521080c14000e85400c00056100c0d001c10000b501400e810f004090300b000799180f048038540284082c0c0400c003642d89034000f103a4001046e501800d003007500d002d0620035044902c1c03074081429000a101103003c00152030f601c11070b8000c0340d8a9201c40014001612036105642c611075141c00c0c02000c80e281d81ca00f0401905440c41038100e = true := by decide +kernel

theorem cover : BRFrame.Cov 118345323 118525179 := by
  have h0 := BRFrame.cov_init 118345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 118345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 118345323 ≤ n) (h2 : n < 118525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
