-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0508
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:10:27.846092+00:00
-- url     : https://prove2.me/submissions/74b57f82-ec89-4864-9e8f-d3a2d244415b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 91187051 ≤ n < 91366907 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 91188301 1250 91187051 91187071
    0x6090f050708070507120c12020c0a0b0a02120306120f0303010f140609061b0f070302330d060302060412060b03070302010219030507051c11010209010e0f04091208 72
    0x1c00c0c030390380c02032100c580150420758580b4034014030b98450100710348080100108200340040c0c0b40000c282c8500b80a010504664040c0c00340300c40820401400d07510a400c031001c0020b040004030129600003405403c10b024409115840c0d540c0d02000540c0380c840b00340c054400e4014a060901d85242c040700560682d66500d10318035402d0b4030b55598213148680080d205030041c1c82080203001600d407000140201d82281001c0702c0450003003907286030401e8141d101c030341c1d0365030b1009009104501e07104043e032816400ca80421000d442042051000c0104000c0c401d512045001643c0080c10740740350081409940c000d005030f9600c940d90704100c044003140c0c3e101a02e82914000505680d4580415441c00b1250164000d156903119420803150070800b81e68100c0a0080402500d0005001482581c10902840ba10301c1001010a4809003044488008a01c0e041e44108190f145036030300b058440300b10f00001d8544424128800020800500100c40040c00484d148403800c0400b65204040c6032142074141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 91189551 1250 91188301 91188311
    0xd0e030a1b0f0b130b090409140303090f010908120606040f0303020309010809010902090c090a03021c03030b010c0b19020706050f04030e0f09010e04110a030f050d0908030304140f0106090f 83
    0x140098003405240c07110014407014100c200400b01d00d1170090404503e0060001400380c049542c0e034254200c003040040002e400100800c2070b45501032000c0307032045020b01c00905c044601da0b91004c505124501021100d401c214000c50002d84030801078a01030106a090f01c641c0380d4803420042d6480d0441c11b500c80c000782c044070000725160018000c0641050740500050410b841c0d80f0900b4075a60000340003039400c40055400000540d031480c41c0060070306200c1003640908002418000c1c1600c0342444024184402540d22a000483c41420107a00c9085500001070010001c2d405170040c5c0314070107014108900380018844210003c80440780510311070b8841202c07103401074040c030415803000003071654800390b40c40c010441c80c80c2008a0583c013602c03030f0340d0401801c4003c00c00111250303001e41081d11040d00c000c42c882e04220040050796440301482c01d10710040c518100440355244401030009211a00b0314281d038000200401003592900c010200a00c0304070380311b601007001418018a440180c83c00d01d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 91190801 1250 91189551 91189559
    0x9090610031b4a0102120703050301260d0503060105091018050909030d0b0f06070c1a0310050103020d060e160801171207031103030a0203060306090601080d0e030a1b0f 74
    0x802003a0b800f4100c0034000361070a503101da184a05050400503072505500607140816103410f41e010082c0841842501e505481e94102500c4441d042d0a50004c3c0344040007125003010f601c0000503c5107a40341c802d14019540f82e0316000100c07040d000d200251500401d0008620b0610b07030b0004400900000b03503016503205996140d0030440036007002c0d10384103103e400810220100b0302141d0030110104030050190000c504091020500d01e500084095401014071403040c008400907a0020111a074518a100d042d401c0455841154448500c52103040c950300142e43e4480c8035450308420020321a240800409181a107041400712040e550340c0c4c070010340f00c040040740280c0f150141010041e034490050007440d42c081c01c1c000c1d031b60f030000c2c0c02901480110384c2180b500d02d504000952003464081740240e12401c00106240c03a08901078400c1c1c61f182c10540052000d560000f450300300e05130302884e00c1e4400329040004242807003111403001e0300c42c0c2610b0243d004c1285a40c0200000c56008000079074a442c0e031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 91192051 1250 91190801 91190867
    0x30804170d0c0809011b08130e011403070b0313200f06040f0e060a0e010b04030c051e010815030604080304021009060e0d060f02190306050609090610031b 68
    0xa0b01d80c0c02441d0000034004946503501c5501003030521041c001034120100071548038881d158001d00c0003900500300004061049544602d044c0d0f00414044081ca5401c0402c0c400098688405001d040c81c020004030005215908495580b07014540004082c81c01c1c501800c2c1c0544071508060111340a01411a05042c031030a04104440031604018100d465131402d29148030884100542100d601000000010400418807241a40203184005015a8070f52039854980921400e0f540103901c5907a04404400780c2c0d07201e0f10b48980f0300700c100346850780d05551406003480821181c16030598051080208200800c424074004600907402200d4040c261020b0300c1c4100d600e80014010b0400041c0b601154138110b082401c2c20746c0c0c595200e42000f05041c0d403940801412a00f01824180540160302540521150075204100203400103032040e83c6040780203030100b44c543d840540120b00911002105400c0548240e00c20361199504400f81d0303400c0b1107003100041695042484440850360030280c02c29450507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 91193301 1250 91192051 91192067
    0x9021009030b040f050c1009051302030103030f0c06020408010915060503060907030f1a0c030601030f0c020c120712030c061a0d11030f0f010e060a050402010e130204030804170d 78
    0x1a020144500550b610f56860f504a040e9844c22100745c03143c2030f046401c075524001000c1d05454143d48040309603140100b040040c0351300c84145d106180c410801840426442002085164003170304080f180c1125078a0300305c0007481940d02a9000c1e503e00b860000400c41d90402c484408024200103002c86602e800806032114000d9500d040e030f5a11241003000007414244a18401034001c1d00c2d40c2c040e242c1c0d508a01c10300b47e8021038000b801807100008000c002e40e0144148020140280d42c00c2180e80f40030100039594494000039075124102d000c2114400e41020001c14000c0c00b120500d00c15802050725003c0e100202c4100101d920b2030034022926121800d1100788038276502d00030320041006026844102d402000d031700040e9010b00440c1c9882550440070411300802c80a080c1c000540b4010851a8a0801c0d001400c81070400d4100414080941e0748440741c296040f0003141e020078099510308031500240310303980c001001c030303800400d0009000c1c100d140c0851105403900c0030b48400d902c81f1101103891107 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 91194551 1250 91193301 91193303
    0x100f020a0906120b03030d02070b070e0108130507030501021207021902030607030207060f050412030606020f030a180e0103030c020a08030310030605070203090402030c04030203010e2e1803030902100903 89
    0x1d00840080110030700c40c84074400c5914184800040002854000c6401d55201282142c00d10350005056010005002d40d20b030360028240c60040300f03140794180006c25204001d000c54a00740d014000c0007080c441d0600c062070045602c00001c540d1040d12705039691245008440708000340c02000300120101c241041004040380d4024050700c2983e881d41420b038029004444203544c0c0039a5100c207000342041c50f2040c0f90180f40503900d56a43c0710b501c403900030203480750364200608541014100a035611000400c1e6000c03c8000d003880c03440300c20740030001d0302030a00a5120314010461100000b0905400110503c00c00b03000365000b04160345c803584126924401540c0340220890003040c20804075400d903200e550051a1441900c1c03608910a0000d000e9030419660900162000101001140340c2440303100c04035100d04015220749008100500c1c9200d030081004e0301c0105208a601c0c0954115034400345101814200c0300c0140011428000c0080c104128124000c7d4480010945101d0203110b85404230307 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 91195801 1250 91194551 91194557
    0x103050a12110c2b03080415060506030a020a0c0c030b0a140c0318011b0806030f06070c0b10030b09030a12020429070b0c0a0206010603050403050d05040c030204020408100f020a 78
    0xd101400140443c4d6486940c0201c07000c0b01c011090358103580c07942c21101e0400c0c0290b850581c0350815050a22040520102018003a03181110400071a01d60100366907014000d52401030312400003203002c2d00c0c0c955030b51000418030f0341c0080020007040040c079022809928140802c0180c18403d4455401c400002d9507614003a031400e00004000448207a811134440b01600004900d04068910514042c01190b0701100840d101408120241c00c01f00030040087c0070701c1e0024a05800d240e800503200302100e800240003200414001640840034a00002c02507074010240c0c04503203040780c40551260450704000000410313480c2d440c0e2a49040703000366801e40d05115108081344a01e100c141707040106641c5ca9004000003800204d003c5001607841b2441030707150b550b54903035907246540d0090030100c0517003001c000e051601080c8004603a01100751074210800c1e0000080e1521103003005142d031a160b9100075481030002501088030302d1b01003880403039101201d1040c03210041000d950400e03806004241400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 91197051 1250 91195801 91195813
    0xe0703150b0913020a20030301050d0f080f0403080702040506030109021003200c160806010b09090c07050f030c010b0306040213051308120f01050414060f180103050a1211 75
    0x54240d464010409560010f10321440c0e00720381009541a6000490200d0104150f1002c8445d0f11401400c440d00740320104e0040c1d0724641c1032000080300214011300151076009184043c0741040b101d901240c095007041e402a540381c81d940d04d4a02015441200201d01660401c0c02095060505004a14445da0f00410905114042001c100e00418180403180303040c0b104480d44610041c4501c0c02000c41d10b440364003600b00d56482c00e0344202d0302d102c56840030300641c4c4a01c00402c4441d0040007500c8014104a07880701807501c8614500da541e024048005d80103014182858220310800401050502c1c2035000901042840004049d11140c0440707029411900d60049128160388550061380c0c489444c8548200041075034071400303c241c0204800c5490700607004148280e4124080d03456004280c1100e0034040c0c02a045a003241000c005000207000311180201d05c00184c4d1f8594501082c1410500c84c450f0641e900e007445941d0b601008415a40300c803585c0b00401c1c40c0c900c210040202402c4110007011 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 91198301 1250 91197051 91197059
    0x702090f060105041a0d050c0c070306020a170f09010c03020c06130606080a2f03100e0c130605040b030d02030a0e0307050904030807080702030a0c080906040e0106090e070315 77
    0x900001c05882c100801000040f500e001c0c6048402c0c0e07554a50b003012500c071805245820704458002e081440381030021700c40c803411007800245c0c88082d03a41c09800582c403000ca00301e0035600b50a4812130a00001c024000304030861f130743d041c4618070849040700244011130800e030061f0200c1c41101c10405040e004a00010074620b841e0040c0050184607410000b42c00c1d07550020390b810017011507412903890702d080d090140c08050b0066015010305080304502d2402995030006552218904000c1c4189500c0c0c455155000d0414014040c0da4000a010342c10684003a0308110001c05580c0289880b1724030300b400c9480369040c0024040d601016a4004628140c00464190f400b0481520186d601d071051440226454542c0e05215000301e2003500d9a0030941410100900805002084507007194001d0041c082d9041d40258403140e03140d0003c0803283d0b51550400410154440c5400441140c441100005140c81e40002240f040750200d580c0341010b502c401170100d064501240d01ca10070110b00180901c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 91199551 1250 91198301 91198321
    0x506010e0111030a14070609030f0e0f090403030905100c0c06060f0e010b030a0b03030706062402030301061229030d0305060f06030703020d092d12030c110601030c0f050402070209 79
    0x1000e00354221417a24102440c9944d03810039038241c90801c40010303001e590501035150308120850307000001102c20034041e80c5e00c0404180036035802480030b020107480744465010300c801030003940d40c04000c0c1d4805102d0003043d820b01a100c900c00110071107840c0e02e40040000c00040d0030043c40107880740c0c1429100264a084541401604050101003005507100d02c2d0400c41c0e50100004e15200d4440c03100812002c0c40c10600c210100c1c0051380c0042c00da01840700e24003280354080216410758015061019100c80b04405102c028400e044d1030305800840c1c44150b2010007650304500e401c0c01d10403001c580c0c408401a000b02d0684030300b540e03007035008012400110b442d8940400555800f03003081ca001414414640d044000b40c03600d510081c2c8101030030100581e009884010040f01806e00b8130640b1042916681d6029a000b4100c82004209541d42c0100c1c0542d0388200342c0c5203561410710080740d2903961a0b04010180d11114403d01421a081c10000036085c20980292085550006c1030b4110a95544941c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 91200801 1250 91199551 91199567
    0x7081203070c05190f021c03020a060c0908031201030501060522020313061d060105040b090f0403140c01060602061003050307030f200a11010816050d0914010506010e0111030a 77
    0x12a0f09000700e10000d14a2141e51842030741d0540200c10b01d6001c0341c22801849144140300f0f0741c9410498031101c04074080780d00091503200041e40301d20000f42c504207045c8104c54840c41c2d501701c1e0019020000368a0314803481c40f00858180d90060001b0000c06a840c41006030740f0701005191748881000351b4040c00c406c07460341c1c080c660040c0c1d060050071030074101e40d07110803c0350290b0b980490780b070381044c8040e44006020031200d03000d000155000c01c4050403103c000b4440b8107000703020fa0086004c82e000982014403603415281442101522641c40d0440305010a018000074002e0b14010b108500c0026491059035012108903a0880050b526244083e28101c40420304140107e00340b00d03800110a000415030005682c1407002c2001a040c441814a4803040550144d00c400c2c0c1080100401d00640d8503482d564403940052504000355215141003051000d8020305c1000350120005144000840d40103410892094109903282800c03042d80c04015240611401d00d071040950051084000707841c05402c207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 91202051 1250 91200801 91200803
    0x10020d0f0201021308030c0c0108130206070204020403020306130615030201080109020a0c021f02010501090e0304180f05040b0609070201110d0e03040806010609061202090108040618050d020f07081203070c 90
    0x5460541c4082e138400b1185400d078403410a41d0320021302d441c5507000c140070740b141c40442443c10100c41d0500700d01d0b10752081c482580c0a481240000b07a1403045540e20740c102e40080d94082c3c10394015103081c003c0c046e51202c10110030b69540c1c2c1090b10a020310b25100e403e007003c0d2a070507140c449440e400c2210800003504000320302014802004403a801599800d030856140001001e600b051000d510310009003500d906a01924106040000003a0b1018010041d58141c1e08414203005000001900900107070100040e200c203124500400e02043c801c480c0b1031a4420b030030903908441d554480707000403422543d01039040c5001c01c1e014012588002c2e4142c2142c090215880100ca003050384686015080034000c1e0300c108041030414004100c1d10390080081c4201c603c001034210704040700400040c20303003d0020f00c0101119034403005007071031151040d040c0c0401904032040329091100204040c0d6500641c0d1340c080d846225107240002c010320001500808102c1c050104c45c00c40d181d65006440302409454 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 91203301 1250 91202051 91202053
    0x5040806070c0b2a07051f020301170c030304061110150e0708090a0210050c0f060f012102060a0507050a0c0608090705030705061b030a08060a050d02090f0408090a09020903070510020d0f02 83
    0x21180003903498046480c1444810707c800103a807940352108440030440550002102c5400402041c03100d60303004002d03541260300d6802c108011aa10010041c10041c1c3c089180c29801d140045584c00b00d44030507034500903580782d00b9062a040d103130f0000540b0111001c882000096101d121943c006040204850f40105542d090090600e012510b0443c1040c40c194080c5803141c2c8102c04209004a41080346030061800c42d41c01ca00210308848983c040180c03022029000e4500052458401440f030b80884016541004c181c40150304545409100c4901c80e1007224001006500401c491300808500401201c0f00140100502c0e03242400b0300800d904100d058000040808840009102040c8020690308009550300c9015203018404c0003500c0310b6a40015010740580321072080161207040185401010081002e005a9518989844103209904050380c10040005000915080d02d80141201d0380044054581081d100d40c14041c402e4281c101d40302c0140e01054840011600500340072981607a284 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 91204551 1250 91203301 91203313
    0x6090f0203010522020906070f050601061704120507120806091b070f11040c08091203040b070806120f01090c080d050f03090a02041401061e021b0105040806070c0b2a0705 75
    0xf40d6a41c01c04079081c0c80c2e140d00132701c000b01000b0080c44290b0140446040906001d455000c01e00560b00005100800040030b501c02800003a0084050b5892135a125035003014030030b0500001040448284c1d80580111008008680070902d041180d920b4084880382850400b01d641d11480d203c00307421002640c001d000c06401c550603031103500500415020a07261100d50317007020203110b454410b017880f140b03202c0c43d01403040c400061801c6403500d80115080c5403291460303c0d000c000071035488109103000020b02c51042c5107840320106401c02d00201d40551b01803103a1350381c0c0c0c0f20126107900000d481c820010b041042201102001540915001141e0b1402c0324499149079010808680d4020241d16055100c5001008070542c050590132000c560104c042d0030050b9260b001035503502c41d1002646c040c0030030040c403c1099105000743d8008100c00022200c0b07605185001402454940205944540840002515051919090108030300d881c3c0d681040740c5003107142030020358214078001c4400c1d004034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 91205801 1250 91204551 91204567
    0x303041a07111f0b04061707081507031d010510090f06030503091909090803150d0c03080a030f060b0408070b03040804120c15020d030c09080601050405090f1006090f020301052202 79
    0x241b18210103011400d1200800d0b0203e01c0549240a803070340e0205900c1e030700c4010500620711107003d110b50000290300300400c8007602d50303441e2111b010500c10344040d01d41c602020010740e0b010750400395044030b95140c0d0400c80e94090841101c250381c0c207408060301d00e0340100b140940608003140c8044502503542c0c00c0c0aa00b6880301a00403d03106100703001d03104000701006100900d10444a0250070304011158001100704135031750b03076044811701e10016040c18404288001d40c54001d40104a02600c1400100807954032200015103542190044840e68480d001e00410803070310204c01c0301e00498004611900700751a118590290902d00030742200c60080701e2100041031414055510221009a001351041072400140101129a4003154400b084080b850802001001291340c0e81520700507a8046419907410102500e041c00303078881681c482c40f031061410540d034101d61141c0161441325109021218900c001501a40028000c2035400ba8104550804032400350402e064508005040541000c40e0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 91207051 1250 91205801 91205809
    0x80318031c0801061b120e04020f0c0a05070902040803180613060503180105011202041505210d090506030a0e07080d0513081207080a0e030303041a07111f0b 69
    0x250101c40340442c031404010700c00150001980316000201c0700c44190707100007130749502c078000c1881e500600a01c10b110302c20340c00507100c0d9012140c030752048040d000d40e54a40c5a00342a80c44c3c03a04202a182400b0f01d41010540c0c003014000c45088615800c02141040c00351420300b902d0400540ca51640080100480505040c10000310001084542c844903102e1174500f00c0c0c4a80070203000500c0042c0d0f4903100040c4140030702034a0302842c8640544000031001d201058045816006401c42c9911050003950000640d440c100348000b44200707201500c2c4410040f80d015102d0b51218000c13154040000d00001d65000d0056100607880c5288004407100213170f031500c03598144040107540c180043c2000440d094a9000c90811000612422000f407a20281c034070545c2502e8051003a000380000350000f03202c0404c07807040c0741c00365401c0b5000301520b03030b00e0400e881c01c0740b00080c0102c5c000c10300d45141400030f540d07203006d44c0e000b80c0f1416480e000342526070000405010321010312944e0340030781691a800540d20740c407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 91208301 1250 91207051 91207093
    0x13020901060504091a150d140103060c020d0201140103020108070302070c060809010b0901150305060a081903030b0904020306010b0a03020f0f0403060b060a0512040f0203010f050a060f08031803 85
    0x1445450700b60f0b82e281010f109000b900d14a00828100121101002c17189490754581208038058802c1c0d120703115901c0c0c00310710024002c01c0441c400c200240714000300c10b108040d80081084001c540844000040e061420f80c01d841c01000c0802c201c031100e100400255004400e443c1e1702c0b001178600140741c00107503a0f82c04018102c0d9000740001980280c1045545013003442490303508881100c0c5102d2646c50300300a4a51a00c00d142d03108201500c40012170090f40382d04102c100504040026640350a507007050001d140425985d0a1740042c0c1000c1c02004142441c03004213024a8026016103160b80c2040070707000c400c0e4450500c070410107508101031480481010007500c0c0c04d0446480950f603991a50404009448850300340700d1140c0c03400c204024610350800111200c40000340c00b4500180c1e503a0804c20030080c40d4190194141d42450340e03402c00000c561748411320541e140320701017203040d450703400245010586015044159000b0019021140c0101c143e4040c035002c0141180c401030558401c4219101b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 91209551 1250 91208301 91208309
    0x507050f010e0402030f070e010309050613060e0601030602090a0506041d040c080d050301031b3b011e090b01200f15010f060e010e01030e0a0803180106050612010e13020901 76
    0x342c2c103c0180004c0d08c1d8424100c4010320000d182c103000b4041075444403911104090300a02c0000c26581d40c0c5c1e810002c1035000b04440c20050015603009695070b05161002e9400414068481c130020340010620313142110540e010f40300d48850b07442e007d0b4100350317104100820280c0242c849030200c079000142e07845cbc204280d04074200e00b035403503039280c0d45146400c118001418a900c000b01c0010036040c4080b0282c400710000c10021000320b00381000e01030301c04495405031301a5102e1105603000c008601c08880300910b4983c201d102d402d03040056540e00c0f0304030850319001b26140c0081c20004c0c10309402070043c6a8a4800241d84080d28104038040c0e0b002c61030072007a820b040440408101c01006084036065030342000b03118504110008001da400001c0000e01d4024105051550b02c0d011f2944003603007001481009035101681907035030f01300800c0351401821684100400340d03090000204080c00c217202a02d201288462502003503034200380311076842000060440500d2a0000c0c19180580d4602c06010700074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 91210801 1250 91209551 91209571
    0x91908010c021e01060311060703180f0501110601030b06010e18071701080a05070e09100c0513080111030c070201051c0515010c03020d0305060d020618010201050f040507050f010e040203 82
    0x100740c010075100b800d445001c00f21810340e49408801c01c0440c00b43c08072044031180440c0c280d941d500f4140b4042d80d0340c890800240d001d0254008011445104952008095410036243c414808084901c619540c104c24000200814400c402080265008800e4461640401800340048504440841c1c941810071541c01c40006d01e4940e65002d540087d03500b403030152071044c01070030300c081041e1101e40e50f80c0060b00c100c08107500201c1c00034031024802d1182800294550f80c040c00008042d5100500316086030202c3d00400000c1500020004414410b00b00002e41030440c0c5403c5070b98028010006804c01c80e0144d06000e0100078280c9010500110840038003c0350b03900054508108480c1d0280004025400c0d0501400490000c0441d400082c0044084030f24a0b0100e5560364442c0802d0b10b404503000c000390400404907100315084060650b601d9459000e0b03008210380d80d034201d40301c5220201910b0181494000c41d5080c0043d05000848000c0c103107046c1401061203045ea00450100e900880b400040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 91212051 1250 91210801 91210813
    0xb0f06030f0a051803030c0702010903060c020a120201020408071505090904030924020a0b0402030f0709020c010b0901030c1518080c0a08031306030b0d0807050601061211091908010c02 81
    0x12090b00d51180c0c50b003080800000a1406200d0b01900e0342da0300c4060011480c0c1359021440404581c402d1070148099a80000306012040d801400030750342e81d000d02c408603075410707030074440d140241d105202341e42c22910b03590000e100240c58425080c148110061142c02004000c010312402502c1303661002d8002e501c645d031001007103481c0184a00340c450100f130301c13049a01d1600c11210a41503000070038065445c0c012240c240203485078030000b490004030900f1003c0f140a0000d002942c85200c1e8080c282c1264100300a1228003001e208001a50000f400014240d0040701814001c0b648a881142906203003428088071156541a003000c2e19040c0f0741c000b0329198000f442d030f009181005036204000702090710095040441306050310a107419180908420503949043d0034199070303603910401d10415000128956a1030250074040d807510402d010320004520f2461201c0400a000d01c43c80f03900758207680741e075801e0102100410403024140e903400d4242044406000c20038031420310800c01d4040507a001000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 91213301 1250 91212051 91212061
    0x200102150901060f1e0b041211031606020d18060c0b04060b0402070602071209030809120c0904030c02150c0a031b15050105010306050f030316050f03040801150509190b0f06030f 78
    0xf8045c079068000321058030061008025041c650180246200c0e070101e4460200c000c10004079103801c110704a1001000c4011500060207030f00860085032498207071ba605403010650742054485001c4074400c0350300081a1003850700108071700308182600680710700004107000100b1000078051760840181a94125030010f181c20402c00801811a4004080e00b04800c0700740c80c6864651680c0035103080c0e0b60140203101141000c201c01401030100c402001421140c5602305420024104481903104030300036084030024105c00400001a0703512601001c004184210b81e0340e8044441c4040804600007080402d4174010000d108400f807403055a54540000031507615240004041d40e100c1d600490245903082c6c02d004850301c01104503000401982d0b000c42440002c0e181152501111200c0a9824040482c0200700c002042d00000120340460b66404245500c650400901080944268407980c2c1c0c9503e0043c1445540d8100100152000304281080d0980754007248a50b88215100300c0c050781c0d0002005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 91214551 1250 91213301 91213349
    0x20402091f12050f070807050a05040f0308070b060616080912060901200c071202031204080304030302010c0f08070e010908010f050f09070602030f090a051c200102150901060f 77
    0x1d5004105132000c0c509410b0008020788850070103860345041100c0000c2e031001d200d00840442e00140740c1e41019401c0326a985c01d00520035040301d50304a0b0444c45480c00b0a82e00e1400d101690070a0401d1000070f0a50384840c0e6400a50350300c1041441e800010b003155200d0090414010240308104910001c54802c1c0149142c48440f0b001d0007000050000a008002c0c3d03c250020300d403c10340f81c1158030391b20380348254000203141c44600d200d01e0392403080014001c65a004048041d0040720b1082c1c000b4803c0f8400c0c0c0c002525180c81960a250000d002840051001c0307100340c286c105c040c030b01810003a407400c0c2c4805001d42175411462840b00500d45400038024071302800f03041c445d4004011406046645d00b0044001d445c0d110341c007408030f9688008240f8481c3d40c3c3d05c2408a600804000304607111402c00d5640d1100c83c498001815038600721001100c020001c44860070024014059019041140070b10a80320717050f200252084d9561740d43c8680104194941d0708585000e030044120021075000081804 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 91215801 1250 91214551 91214561
    0x1802120f010b0a0810120c0305160e130f05030c070303020705030705030706050a27050102100b030d051606050f040b0711100b0613030309061b05060103020402091f12 73
    0x1591588210000400c0902e04441c291540180b203882c00602e82d0f21440c03080425130003141c10003202015801c4000040010492070300301280c2c030407802e850b82c41411945040c2c0b2404039208000200c40c400c0d00180441c02c0103001d44030311a20644032005400030548800340345800a940c09000da40c0100000e0081c5601040000000c000071002030030828145400b098403450544520002c0c4003000c070720740c0f00140c0109840038131740d60291007643c3d101c00600400c00503003515205543c0540290000c41226012602071f801900c0d4000d0001d2480610a4808541c0e41d07002e40145e41c0480105000040050350600030303580504400130341c1010a0510341096a9001d002611034018494002181291258042002c000e00071030390b08005038542c40744c0046000d070300c2124030705041c0304191b2001204140e04007046100333032805641c425000180c01c80400c1040501b6100141c0b89900100c010401480d00307030002c04080a0140200180e800304419001082050844e06000708030010b08240300c0049500c64 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 91217051 1250 91215801 91215811
    0x90b0a05060702130e15040312060608040309031e0c080c01030e0609062212020d020d03090203070b071103030c060601030b10080403080901021e1e070308010b13180212 74
    0x403640b07001c040d40d001640c0b0703030480e501424409031a0006162003500611000800c030702c140c2c0100141c3e240034038009000c52140240c0140700d614011300444c00b648220300d003a20583c5e00d0f484850459045458009003007020b0301074091804110b0224500107211100c8002c001c0164400401030442914000b500307940c1c400103140c50341c0c0c0c40002040115180040e00c0e40c2c1041d41d1000c041203e0f041b001145805202c1403034068a100040c40152102a0b80050346604a41d0355500707403030b41c4c0c601056084081e40c00e180c501130760640c4100018001904640e000700b00c0c080c41064010f245a140e000440d0440d004294080b000e40c010320100300742c658260003685c00e078603030480e4520f8001c0301c481c1000e400010090005001c000510b07002400e403000950440b4289003014911011a4101044440703469010707180034004003200a9000090344d482d6815140c1c41645a02c800c0b560340c1c01c05054060729009414291900d0604940c00500041c82d82c02a000d50407800c030000da0395040603241d21000382d40c0588 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 91218301 1250 91217051 91217059
    0x602040503011b0c120c060c0507111903080903100c0503090c04090b04030302091201050114030f030408061306090204050123030c063702030a081506040b0d020d0501090b0a05 77
    0xa0b000c0700a5201ca500041c091703010300b030403155080e0b0f00001c07900302c4071302840103140c1d9160100c100303d003c0d0401c000e000700f24800c030f22009500d070000090100da01a03504640c82011080e40060002413510805082034402c040c0440380001100705201007034903190001880450000018048031a209001c01d0340d20744e00544060112107220fa41b0846406d400601c0130b01010b90120744481542c0e110100c035154003803414000d100c256140c62500b00c4000b60460013a02c0703403140c401040358010b0b011040da8200e40f406005024035030344000303e1400c12080c58104441c0f1640c0e40210b0001686c1e41e1003260b005c0c0400c2c94040e0000780b0700404804c11080100c000512a5010845141042c0d8070380003120001f41c040750710000c2c00c0503d12605c4c4011303681c03244020100b1140c1d41030300108039800005402d0341750342ca130744050340d1f030320303600c1e040c05581002c0995903400070000c02c01030094845150080403422003c0200505d0a04003c80300c50413203400b030f00418203007a04c80001c4000361900c0400c0b0400313820222 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 91219551 1250 91218301 91218341
    0xc06080c0309030a030b041409070f060c0f11010221090f0f090411010908010e010903031b02060c07170c0a0203010b01031505130605130e07140f09040507050607060204050301 77
    0x14a0440c1d070b80c01524031080c01c140e220001142c1545542c0c00580803d085e1001403411414116100c032b840f40604d0040c8002080049000503400340b0510920a2080d00000e13040c10074826516002003c001076003a0605600c030303d14002500d4145040c50b905098092681e00b0348a40d9a80100300d840c00304c200b4481c0c4110b05c04a84942035a8410880d1a0001e5000c0050b0540340c3c2c401005954845059000040551924030311b098503003c103400511082e442603800700401c81c11078500f5070b0844105205080180e10003800581054000d01c01424600d02a00100903018001e00645040741e0140c0d40f101056045140540b085007002d00800403a00800d00381448103442c21540c003220318001e03105540c400e4090302c0c8102c446070b003581d1212018050290a48039804580d919034400703421014501500d07403003a120001500c1e07240118101034014024544044800c07903100b04402701e180640f00340e0303444c00349080026442d9a180003c000a0f4402e43c000750300c4501d4a0109402c43e501c000c950241c8203514 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 91220801 1250 91219551 91219561
    0x309010e09271002040b09090601090815070507020d03030e10110a051b0102210604060311060306011e020a0302160e0621241005011e02010e0a0c06080c03 68
    0xb03454500d081c80500e4040c40100c401e00c007503942c41c003055442658080b070710000300425050005402000c4440040e80c56500940796000115038400e01e5110340405908103001c00c40030000c0d58002107030010120300d06941048001d0700061088464400102d002c6540c80e003541044080a011110710600050010040034041d090031100710300c1600c0b11301c41008000a4294020f00c00162844400003c40c0b00031522103032500c00400c2c1004407a00e030002d40580c1540024040c0c60940215401c0c0ca6229107111092031407082804800d410250456060029644c6840c40b600781041c0907800d07100603a401403961040398103002e400c00d280303070700907100c80a02403000f0310a141d01408886d0308510103680781c030010906040c0542145070800d0707280c2c81d0381c01880e90071012549610540501e000f604000e490145d120301d1030700c09401005204083c0030a1180001c0540f20482180d0310b20548441e000100c0d08400a04080d07040075000501260340c0040d40340c0c00d1200c0c0340c1c0000c8a960140790a94240d10b58240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 91222051 1250 91220801 91220821
    0x21206030c100c050708030c0c120a030903020103020f0903060403081905040b0c07020d080d0204090606032c0304030204050103082d0702040f0618060602060901060b030103110301060b0c0309010e09 87
    0xc0c0034000c2c42804500d014103c00c000341005001c000b40400000c1c2d94036421a148a2034030b503030b000b06a0610400401d40c54480ea014003154030301a255042c0c9606200500c2c0d80d0055020350050b841c8103948000500c849600d544081c04294802c501c40e40c1c40b500c0c9031400b0040080d500d140e04040c0320b1aa80751004000c0000d416202da82d81042490700300f2511580c0f117100048902d050420b00070008800418440588030654001c0c0081d5001c001044c404540c580604a0885001e000b02d500c6002140601040c038070644243c8210400540c01a28902a2243c000c02d05a82e400e0f48212400c1c540050801c181c094041d00684440303100c140c40d8560907100b580f003080b42d4002e6076406440386035070300548408070b03070b09034080002410210701100040d10041c204600824540c031485c00580100780000e0050b030810b00c1907600f6641c50f243c0c0c103415642140c49030005080c1250740c00d90550340c0c410b404911004580b01821030410450020340c1d46101420005240b0301102240d1801544640300380071246103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 91223301 1250 91222051 91222069
    0x1120206120406110c0105060a360e0118060b04020c06010e07020106120f020112060f140a051504080c030309210109150603030809030a1b05030405060d021206030c 72
    0x4002181c285440e98100300340101407000c241c0c0c6403103d000442c44001601900100e21446080701e140b1405980d851700303003a0005424214003010410742c22031081c140007581c50701c0c80542d2001800035030300c40c581c40410700b102c08a1860054031000300303c03000100041400b0b06c04402c01c00741c1d425428032424586095031040c040c0141e03040c01030480d00141c0709a200750b01c04001010008141c882203102800e048964191541d82070340000c100398100703aa07042150264200321041c460700460510f107002c51081c4044800114650b02ca1404d800016095584075803408046200124a5513114948105185403528840d1094001d40083c05442d9155a46490240d2100b9070203c814800c461440d0401d40140211a4007c00d003044c0c003200c42010100c00d90000d0140da10940310b6545607281d0180441c0d481c01044103000001301000400346000e030704c080c0613030340091080302100d041c0740d01c5800086440e0000710030107402540c08201900245003800c0b032241c200809802800c1c12502c01d2000c520850 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 91224551 1250 91223301 91223317
    0xc060316030e0307060b030c0306040b06060703110105010602070510090b030406020d0b04050106080702070f030f020d03120204060302120703021e0f09043b071e05030d02070e01120206 81
    0x102054001903003003402a00036100d103480c0e41c41035035960b60301c51624a00500101d00d940d40a845902004601030030300054040c000d50b0081220f0104d81d90fa00100440380d0b2180354210200007038080444017a8000b401b807240608215005410001e0a11003400b1582043c40d090500700300c1c011908111140075907040b0390704150010400369995456080d109c0290144440c1550414604000080c0c1c20b9486030105004000c07070380c21f403205a40d40300c95091a82195000c09011517080b150b10304010700c1c0007260741c16810f01c6030511598003186507004100300d80056100c400441e40018040841c0803c0c22580c83d40400241011410308403a450000442d82c0c41c9900784400c01d400084004079101071070183d40c440d0340020f10a002105440c0741044014219100040150000f000c80703940c2812903881d1322003510404401030210305d150a00f98141515444146041c4165060010410781c5003070000c101440c440360001c1441c1803070143c0000b0160416840f0070410700210340761800582d10305040324440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 91225801 1250 91224551 91224571
    0x2a0a0905010f030902030a0309030b0903070503180102011d0303010806010b0a08070c050c0411090f060f03071803140303070f0503010b0f07020a0e01031401050705030f06091504060b09040b030c0603 87
    0xd02d840410030f4000b0710007080040c0d0b01d031103040c903600201a4086a0780c01540d104070032010050b00c80b00c44681d42c0340120040144603030018040700c850101c0010007200c8500c414800030504114408480c485900340b9007214a20742c100100501051004010036401030450080302450109100c50003030a040020345041e00b044662030140d002d000d001c00c0601c070806401401000194901c1107054540d0b400400954094104d00008060a213030060660f081100d004a01d54510380d00c0070340456259102c000e200060008030301d408000f181da11800ca60030a4810b00080d07a4a042c0541c2c003601c242c1e4241103460810104100502c44560750f001070b1518610740200d03a41d125102440002d00a410319040b104808010100000903c25294003000d031184504000300032a8844e1402100c180c881110070740c0c2d012031a140800c5031810700740201940300c02050064840c6416010000701900d000394031110360395101281643c0c503072030180700c2c04404e56003c400803c0e81008900c0407030800c0c0001001c841d84 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 91227051 1250 91225801 91225817
    0x603141e04141614060f031f1d060103140601050d0903020718022124040e0d1107050612010306020307020a0f08070b0a051311060f032a0a090501 64
    0x200442c038401020340030b0400c0162407003160386243c40501c2000c2c0e88503041e070002c6000c1031910b0034181641143c901c0b0940e043e00074550f98419449040400c2d040e8810112110b20100000d640c0d6031400d0b9134030111010380c903140350f203040600c001410b40c1c0e960282502d598030301c3c0d03041c840f0030383c0c1000484030500c01d40c080204810126060603407e000c2194010312078001d000900c1e40302041c0c3e603030003400320a04038519040142c5010b41040700340401120440e282032800f2000c030714010350182c080d41801c0390017000850a2496014002d040c4404040c4080204e80a240c101c02d04910500030040501030580b0a18201320f01d0745914075035a4010b11000e409154008041550244280983d4805a8100003031003081d07849032074400703070651004205503406034119003c0303411301c0d81e203000e154024400d402680c446c9600e6911034840c11141065910b500c03413800c010300090b40302460f000d10304c80c680301103045424010300102c0f54802c441900d070245901400f080360500680c3c100c0c2c1c48005a9a0a03e09401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 91228301 1250 91227051 91227053
    0x60f0903090d140309040e03030403020610080607050d060b0706140117060c0c07030b0106050c0106060c0302030d0e010237030c020a0f260a020f0f030906030402041112010603141e04 80
    0x1003540710369405e9580190400d030480003e460000025801760f44a5401c40d5156034a0075070004c51482076004240d840d41110340442c40d0584100050200c80440b02400221195194800c05da40c0e401303500100e540d03984600c0049039401c40c035040d03640100480721445898640c4164031a480e0755006020010401011070824808403042100341d0186501007540d44281d6121000509503400501c90301700c0c02d6003444004940103106130403100555905800441c24001c09188040140030300da8070104080d075003804a010104119014100307001c0541d6280301007000240190303404580d02129900c181400c00c1c0c0441c4403694006003200407aa04559802c90325040c515184202e0b0030a4400d90f0317650802c030310200303c6d0444070348003d008140d10f5400321032080411600d1261102030004d86103038140c109200381880d9041020040d9031140c4002e10006825807070300109040c0390803070703a160ba00e100320080c010301c03680b0381521540d0620b288100400c3c18500c3d00a0714402c1a10986a100802c0d26002001c20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 91229551 1250 91228301 91228303
    0x501091a04030803090f0105090c0916030e0d03020a080a060b16080d090b1e060121090204090507030209010b030f0103023c011206030b010501030e0f0708060f0903090d14 75
    0x1c0c002e5540700310074a5503402c1016040c0d58803820b00101c90309a5190501040303144030000307840010b584000c1d0654074550745100b904003044080000250505880d018401008030042c0aa60300a00b0300c0e0b1001031312080c24042c020310640004106038010392400006100c5400c7c1001911a19000b005c200b0035040703844c4c54280ca05006100c5504205d508003842541009100301c98248a00313201101606078003001c0e00c02c4105a002a98400d010034404040b544400c03220560441001d4010280424480069070100e070460341c6142d0309038cc16800c180000d00c210724040c02400c1c01000c807010303500d0031410f24203070143c0c0361001031000070304c034440c0e0401c44052003015811031098070244000c074294a0440c500141e81e0000c0340c19000b800a402503004a0b0006098803840d411749400004241d050f80c00c001c01940200300304503091505110326a403e84107030300b00700701c001e000d8503905018282c01d09116108000e20000a0000c025682050111841c1c03903c7d51700311852110381040742e4207a021604100c20b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 91230801 1250 91229551 91229557
    0x9030903050a0c03020f0f1513030203070803030108120406021504031403040c090608030a05041a07050d03150506040b0a030f18080c190507150315080c0a060305010501091a 76
    0x61050161108510a03c0b1002c8803140490303000b55540182d01140c5005c0280020022032119401000400ca40c000c2050b020060f10308200e441390302ca201c2035141d80010740342a000c1d9001410039071001006006051003884022929844000480e0810f4244000030351074214420b21802101800d00c00142410f1042c900b400c000070034041001e41c0d0381018180110161024051080c0e12418214005405907000048480c855641d03580c03941894101107810b031140c0c0381491250124581800301202080d0309201c842036400242d00c000910100410610452414a5012503c9a070041c00f04104424041d03084400d000c0c0366140c00105180c0c04442d48004244882c0074030005c4030072a00c95020441c007030004002178560307071013180c0d20388412400c407512400301103000030803d03007050170200f00e42403406009203007414050030007084008080a0700300e2800740036800302185a000050020042c1410860800078040b241b03024401c56042c00006814021a03210b101091243c01e5800400a1000019 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 91232051 1250 91230801 91230803
    0x5030f0c0c09040f06140c040e0a02040b0a17070c0314091518010206061207051005070b040f1a100506070203010605040f0c111c050901020c182a030a09030903 70
    0x70b071084606040c1001480c9241c04002140d4040c40c1c0929043c05c18991480c2e24482d038002010546854100161101516400f03031003914025004d010102d010100d05018100810007540c07084d520f0000460440702444001d0480d405000b0210280c50220380e0041091405001091805550f910300c580820405040c054241982810206020540d5410039440320451030f000da00315034080d00c0300701c2040001401400001880da22001c4200103c0c18003180c206645405814a9828050603440c1d10342031127401c031401c480f4280256115401c000480b6090150f00f880b501c020100d520b0005810282901c0f036008840c411140030500f40110741e000d40260010b031a02800502a031418040040040d2100c122281b0101d031415440710606c0100050101e40c3c1d0103034000001460200072402c0d1110b0340304003100c034114003810407a0002c644450806580500c4002c6600c8240c0c50b08619010342d482c071140c3c040c11360041004424008104020035250031000c00036001428030070514065481e103140d640 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 91233301 1250 91232051 91232059
    0xa0e0f032506080c04030303050603030f0414100201020702030c0f15071407050102031c0c1218020405060f0a0b22060305010810020304200301150e09010f0905030f0c0c 74
    0x11001405481500c0d5010201d11544220350858445000341e0310070348102c82109144c3c6050004202203442030700001c0c0c01c00d1000e8140c0e0310b010b0105110140c2640180c12445954071184840783c0182071100032003446080901c002c40c245003036a80069120304d600301c4803a1240400081d84c90080d80d4040c61301c0041c81d110910f0a5030780d0f0b420701e00700c895030454003d01e03481401000000662940003100321200240e00c000c03240509180b004000c1f00410b25803010350100601000d44502c03010140c8610f8540b00744a0b010612003801900c10082554401480c07140910640d40c0052450703110801c05409845100090f01d44407a1540c003048c40300d460289181c1810b2414a41c0080e409405074003c1d4142d039000003d641d120001d0040e40b0040e4030082d00c1c000c0c170b0f82103119504984180c0d0f54071015201d4500800102d45135902c0040104044055040b00c006004007100384891900240b145680d0700c0100c85090011011948884c0e86038028910f207d0300100c00059450704852050141c201c11000041c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 91234551 1250 91233301 91233313
    0x21807021c030516020c0306010918080403030c060c09080d08130501060e0f0603030315060a0905030105150f0301050c0f070602190503070201051506180a080a0b0402030607050f0a0e0f03 82
    0x101006016000503139003590101002021501c44500c0803a001440444c003030020031590f403801c00f940004040b01002c0082c030106c40401240042c1d2000000c100031806aa128402d40c0340c1d40c10400202d80c544074000b01404280b160070800e020002c500b40c02500120f0514080c1ca540b81d41d90100c5100103482d00510030b51810801103481c0010440c081c0c040c4461a011403010358821050540d01d100070b41e0713240302d81da04101c2002d50900d0040000c0000b41041d01d40400e21b0795031a00440d095600a40300040f07100005101207000d401c1440384021000822002440941450074000035248074040e01c41030350810016815003480099011204582500000c0c03200151613590000c0007500251003420055003064003003030000356111880c4514132001011b042c585807109a41d1541100440d08468100c0511400010701d64414800b91840e180542801c1400745841c3c4101400c06e000100038a00b4400207200c10f13000c241840c4181c4915800340d0800e01d0b41980d07a040001c207001002c40300c550303040c8202 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 91235801 1250 91234551 91234603
    0x3050105090f010509030403021c120f1404030b0a05100e01030605070e060a090e1b190f020d0905040f09060207200409030203030f04030513030809100c02180702 71
    0x158800c52041d003405099820920500051a09031001aa01060554814003041c005841c142d20301041114400c040d44106201c00ea0b42c0b007203401600034600d0041500b01d01c4500780c40b500000d45050744082204010701e05415a0340c2d424002c5000381c86207010b41d6507000040c01604a034944140648402451103c40d9a50703850044c0180404550324000200d0642018902d820300340287e543c107032060b4480c4000c10382012000d01c2c040400401a49010340030030101d00740b110351500140144a0040c0d281000a00e0640001d4070188144010038115400030780344041c0f00780d0004202d0140c078401c0354013081c078040c003a04201c0a0300d06080058415071000a06c131042085003a02001903a15400c1c03030030050130b4103d0030841120302c1003401401580040002803040c0141401d02c0f41c1c485e1090034014108100d4016260902844d85c02c100c400f103900181041d02271504c3d0210b0410b00e102031038030528000715540480e0411000303a044c0c0c0f641d2142c0c080405d000900a02801c414901d40c0d0040c05c40c10328503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 91237051 1250 91235801 91235803
    0xf0c2107050c0307110a0603060509040201120b040213050a080f100906110c0a0309050906030a0201200a0305030a0f11040311010306080111040e010509010302030a03081e040309060806040c090501050906040f0305 93
    0x39490314810124585c0c000347d0b043c0240103080464000a1191442c1d960750307001900d2003c0075481280c065030f5180240310040d40c0e284040c090381e044850960382c5440c1403c0900070000542e40003041c55a000f00703d581c90285001810a4265a0907003010030014483d1428030b0141c061205650365000000c500003003c400f001402c002180c1c001c0d5035888400d40d41c0c9040c8100d00d20b003070314229003607002a0071140245d40280c0c4080103036000348103600307003107141c1420072420441c1c400c6003200002c01c00800d10016034020b0280310791100000d103042080f002a040d480120744140c3c80000d10010004013a040968000c0d44120010200c000003480701c00c0da440034000480e4042c0c0101c414070920000041034508110140c03d058a9020700140000c40c01c0b170304d06940110b0700400c140e01e104283c1811140d1001c0c550901400340d40f194075000207290410201801300340c0d00500c1a40540d183c0b8080140321540480120b046540030308149a07292080302c0840d60740e01c6a90031030000400010300010030004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 91238301 1250 91237051 91237073
    0x1a07022d0a181b09140a030602040b0a12060522020c010609020405100206040b06040510090905150901050403080402011d03070b09100c0308060f040e060f0f0c2107050c0307 76
    0x2000c11010440d41900003c80d200c0040760354000400100503200a21204449804d90458420000c0c01048600d5513981c60304166880780d0032034511020301080201c84190044005950030701c48000c00e002e524188000f00302c05411401c1c841d0030180f00f591043c4211413040d070440301080c0c0448000d10819456508540c042d502a100c0c0d1402600a2115044901e102240346401690700105880003610f41200b0007018080c00b52441c04910600d00c40000c1e14140e603c903c03030340d26100310060315660110400340068200001d085902c2c0c2d9040504220000f5070007551154441d5090030603182c0d044001032101c0b44803c46901e40350b01441400b030301142940d518405401e08501c00c4440103141c140140e8103c03030016032240002c1c04680d6442c082042031520710004e031400e50000d8000568289001401c3c0c0c03511200b96141d500401294090060307274a0360410142e07100300c6950344145008401012107400304183c01c21400000d0a0078003090200780b0403001c0315251001a01141c2d204c0a031070a00c03c42d845 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 91239551 1250 91238301 91238339
    0x30f0105120d050f0a020319090311090c070b150a0609090f020f030c090d0b0f04050706050903030f0c0106120308071106060a051002010b06131a07022d0a 68
    0x25120500244024005160300ca0b505a0f6a02c850408001d585100400d80001d8814401c2d80006d2146000d20580100d0f40e03030200d11141e841806a500d1428203100313410000ca0040d003d44900410002000c110714202c403030b8540e00c1400c8d56010303070350751041184550b00030f160b807940885824030005000c1da03c6842e840030f580c4904802c21800c00c1400200c02244508120000c9901040c400a0030021070f0002900b840a0058122006011603070384a50144404840500003a02c0c043c040c0024404e003005200c025101d03c1c2007141ca00030022000035502e00680940313110707000000a404403240000c3d00301e103009046031403810100101620f00078103840c1044441c1800030b0108a04141e5030724000030302a000b030305e000d010590030504002c1440b01030081108041c2c103540d201c010f05000ca8890600403c96104e42c0d020080b070300f5041529a032007190040000b10a000340c00d103e24009a82c0c0d41d8202e01a21810032418401013418940850f100841c0100280c1d003c44002c00c00680001002259030303501d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 91240801 1250 91239551 91239559
    0x906060504030314040e190e0607050414010306050603011a040b030702012f07030f0201020c0607021b09040b0a020702031005040c03060c0f0c110604090603060603060501240f14030f0105 82
    0x1c13600c0004183c06000e1842040c821070314940203e558180022410219046140404100c2071109a4064a04007054480784001900006d081100c09100003c072402c0c10001d280500c40c0500d454005495070006015101c450701402e58070580440d511404c840c010902d400d4417580302e242c04034019000b41001e0b0f00510902071164103c03007854150344d20045c50071050840303180c2002620b40b0104c0b89429400a080c1c15036600f01304098002d81c0070400c55202c0c0000350300500b503545140f921130104200000c0c5032409001c1c084140000580307681c04103548a040d0390001a126802e0b03000091500e8400001e0800840c0341c60f0600060000030410442a24007401c0e050000400c9076030f00722807a100c003240010018000b580904000780078400c4031924180002d1040d400e0a4403030f1800d0b01119082d071320131140381d50351311010010040c0034011503005040c03004241c0710000082001250045070040700303404004800c40e03008900c900555004d9005041c030b1108546a02e061040060381ba41d080c001c89201d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 91242051 1250 91240801 91240817
    0x3020901020f0106140405060d0510020d020d05040c05010f0e010507110a0302090c070507270506010e030f030c0f0c0102030f03040510050c0306010e06030618040c080604120e010903110f0a09060605040303 90
    0x1c904291240d40c401c0e03a03010000b80b02f84080004100000c4d00301590f0903410300d408106103c0c0c00043c41c01070034040c901400c03040c000f451030000003520050f10360b0400c100707000799020841030a0303030020181c035001e580242c0740c58a4140d00ca0001484250759070002503102075600c2c14024840741c10707805086091b2048003240c00c0151a42a400c60f40312020b000342c1340440304101005d191544541145400001c1810400251080440000e0030301c40d40219003245940085080301003041c0c20440c0014030440140540256080500000d461b0310541c0301d1061003640000101e000c200f41005a4191000801010003090909101e00e58081e0301c10348640f8001004142681e1842c6040d00450303008041c014092103901c1025020790034590802041611210101240007a91003001e1043c14403840c4100c50b000341184d8800806441e00702e480340c40c0d0b410412600c4082c40010440000300c1c007034600407201c41d105440074000054010f82d070783e004644118200314001845a400070701a100343e80c07003a02d400c01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 91243301 1250 91242051 91242061
    0xc0114041e0f03031e0501080d020c04151710110c060f0118090507090504030c0317130618020a080f10090b0f070203070615030b090a1203020901020f0106140405 71
    0x481c44100d000007a100854411003036001134026400010443d44504082c0f4081001400550466900340d101d010a904041e01984d0b07100e40c10310a5010424040700c0c01c220018680c0380b0588540c207a4010b04880d6600d010801c021a901082980c0e440c4a895400380040001c8840180c1950850380780346545c1d1041b000440c071071000d040541c2d816605082c3c0c4a0b4506101c2d90405000340c114a41c0c20307100350203454800b0940c601d160040e2403140e402600e40c540460268a0010b0001c0b00a498100781d881561050040404078450700305001d0b80c01510104c2c0002a40d45c401c440d018400c04029400200b8000004001790041031708203d40e00490256984681d5072101d031016074181c044020300c0140028002070504051000c07140c0c103d60944100c81c01d1442595488003180c516a20201c20000c400780200204010070021350780c081002e9001c3c01ca0f044c525540d03c182c118000748054241900410b5103010317a4070802907441462440b200a010749643c0300320321003e101c80103440368010303420800051 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 91244551 1250 91243301 91243343
    0x50103060608060102060c0f041a04080601050a14010e04141006200c040c051c0b030c0103020f0307142709090c03070303031109061207020c03011a010c06020c011404 73
    0x143c0b00e0501a0054419031b5142e0742008125070266030210050340c8103100102d001d22510402003030701c64403806501d648a050161042c50004140c0c00702e03110300003014041c0035050b034035480803003003031028201030a00c0e8a0100000c0c0c0034096000301c003400c1c11121030401c11703051004a98201200d51f5074680b80c0b00600e0026074030150074092002031203940c0c020002c1800c0c1d07040c5588507051074504d0f4078046081085040300c10118802c8030000d611103513100d0001c480c081c83c06000240200d5402d080c00c6181105283c80e403402800010480001e00086c24881d40200d110641110400e9140c85c4c11003103502c5103444040c100b9015034024901900e480400034041030b20000713601c00700110060060210601d144d8044002e003007a100145882c0400780300400994803104040d080401040c000c403903e914240c00022300d0601040d45180c440e80c1400c02c82c1c0300603510b148030b40c4e1038080c0a00e060800e80c3d40c01d0a090019104503c0380b5041d80d03203800409002291000100c6003d940700300192a0b080c10700050700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 91245801 1250 91244551 91244567
    0x14070b0a031e1802091b040b070b0a0603031b020a0b0c03040e011706010b0c0118030c030e0103091e0f0b04030801080d0201020c0303060607060e01050c04050f0303031303140c0a0503040501030606 86
    0xc2c0c982c00040031100241c5024150550700c03540c4d0039a41c90180038980780110b847c0e0046c0d40210f107016004a100b80400c03403088541a40402000c40410420f4078546008080c0360b04c04110242c0400c2440d4074a080d034490480c114003411040007250354a405480c2115687c1e4410311a0009032001480081900348002c0300c1d080f5020840002010a40d0800c00190b0b0b0903800441c8046c01e075075903210b540300300c6240b90701010981802601c40d581d2600180c11b024018000342d5a42d02e041528085e0f500d00043d002280c5c905c00c00c4051001c0500d421154a000c901c240c806500c09040010303040e0400c8105940601c80a050b07800c5e0605a5480c0000c0000036400c0c3d0184000c0c100240e0030a1000582605004014040f210b0140c040410740d00c505880d42800c641040d25030012800000030305006604240080c1000088160002c6141d8500503401900324404440020f0800c0f080c1c04400d41c206120106030303030f1180c0d040340c00d44c0c80c080700901c1d1195891f03210b0300c43c0d180840d00703080c03001814900841d00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 91247051 1250 91245801 91245821
    0x5060303121e0702010207030e0f0a030b0c070b0903070c050d031b21030b01030b03030703090e0c040e0705121501020a031110020a030203091e0a14070b0a031e 70
    0xa40c14003514185001480708024402c4070b1000c14003100350308218481a0389409200b8030f03000103135540010f00f0000c110b40c00841813180140075018075103e4540700c1d0140314086030b4000300f00381220349a806100707103644601342c0003510b1080c3c00028040b0144c4003200500c1080d00c10207514070720a5803030b410700403180030b5030304050013048880026815104003401e04007100c0b4882e007400c0703d10310008844400722942078003e000c002952840185119605440b03141c02e40c01e011001141006e8680e90010300d689680c0c005d5031621182c220220b116200e078801514040d001108804025207003c800050003500711700b06d2118004e00034400314007815035241c420780f004041a800381031407201c3c1707880030781e981c0c01e08030045c4809104070640b04841ca03805101600d04a421a9400740e56406c003c00c3c05403030100108810a11018401c00010015000081d22020b8550121200500d4180213500c3d40c18400c840d4418030710f520340001c8184000f503150340940354900d060105000c04130483d61072502110789a0030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 91248301 1250 91247051 91247053
    0x50108010b090a05040201141602010f0816031a040c02060916140d170a0201090b060603010815091504060606031505030706050c0a051c17060a03060b03030d062601050603 75
    0x1000c26141c5201350040c942c05030060420400030104900500c019500111240384d011804144280440d030344482a1880480e8528200307507141000c140c03041030041415281c4050540e20418140258801c0c0307845041c3c8440200104080d036844a806034135520103c6440340e584c0102c1060166075111620603e080d0796101d0910341006040000b0703c102d5a0000c223098840d204c030308041e105006a0719004040085141c0e002080104192802d0b01c40c80d94081c020324412802400180942280050510068040300301511030b5a00c0e040300d04da05040c03580d011a111407620208210500281d500440102d81031307560204141c206401b070a1a44018901810f58107410ae40c0c010880c41b44100301401c1524032107400d858100c0301d66a2890b10381443c4105440680340c510189481541e008498039040c50008100d0310018504034000580217152804000e240036610b00480359161010825603448110b803000030800c3c0d50b161410344a00c00ca204215002c02c1c6021141e13075000b501d0600a1a01401001e4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 91249551 1250 91248301 91248319
    0x403020f031603080c0d0504080406020f011109040b01110d1d04091a06010905060c010606020d02060106080106050304210e030c10090e040204090b0c090406050d0510050405070816050301050108010b 87
    0x70341d0403101d003803005d01100310700720040c0321882c22060284941e43c0900c0c4588045a0b469152a201a08081c003121508a8170b0b45048401da031b000f80303940100c03540d1002c11980044c4020350900181d540f1448603099840ca40716a125810007988c02144140806d00b10aa0104c0c03201d105200304419100480c10003000606056800d0302d10000740184650814014113015204544503004500190002400071030680c1d181c001c02c0042ea81c06000d0000c2c2c1c00114400360016606100d00500444010301c02d500c2000000030004041c4544071803210124241c8070b1601210580501c8010074010065015500c680034010300e210742c5203000b0000e15080703000c64403044082c40c40d100345078180f050010016600141c1742d60038030f40014014080303148071b03982d114403483e01d400c16a01800700b125420307085540500120101c0c0004110001913403401450281e001280c29580d6203042400c1140a038081d000900ca1000740764606000103034104c06072001a40200150ba0b40c1d070030f0250988001420050300142c0c0340d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 91250801 1250 91249551 91249553
    0x1212050105152209021309110c1b0619022b120203040f0501050c040314030702060301030b15042d0203070f0c05071a030603010c08040201020c01030f0b0d05060403020f0316 76
    0x503110383c1c0104018401400f4003207948980c56000d030780c0052148030070144e0310042404525828071441c0c405000b4040483e0501c0005d0703105541c4c5082c900c400030306130308003c01c0001155541a089803002d1948640010300000c441c40e0180d40e40b0032100190000d904022400a01c00e5901c990424055031903596540c1c0203a0009040302c020740c40900151030040d811056440425001d0003250700403640241440d03902d610f5070622324100c0e03d1001c0c040740190802c2107030b00050381d5084141d80c107681d003080340500a51588200d02442c100c0a804242d0040d00745007245072080b003e600280c03035a8034422800c101010240006a040f03100417195800841c03e08c5030310110a03482034039207007042d40c0705808580407152240350040705080102c009074640c0000000300200ca003800c3c007480e411085a4144080541000da0001c5c0d12105c10194090405682d04030908510005030040b03411204040d01c0517050404904020f03444600c202c400b03a0140c401c200c88a80091000011140c0808080700541d10031141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 91252051 1250 91250801 91250827
    0x2040e12090d05120310050109090e15061809010b120f0d11070b030906011403010504020102070501030b031905010903030e0610090515040e0f0705100504140d121205010515 76
    0x3002c810380300c40c070551801c1c3c80748152080c0118003a0311012000e580441c5020700050055002d0b0f0001d5840c10b04016a090761314000040080c4050b841881044950340e40001088890145141025810b02501300b402280c03003040d40694041c1d6001d03211401c100b8505100c00340d441c01c040340c1d0503c1e594040020200c0991180d90b400026007110300c10340744856500d00d10244150000d84100030550441c20040110f00400803402201c2c41d0300380c0082c003071440c1c00e400103500c400044c8138060501d5150020a04a80e9090084215100b1400c201c1413809149013003190003030000030310840201749080c14420a542e40081c0092051400e00c20507a03a5605148419010b00f6010300309210700c81030700e4003142003542c0e170b03005044d42d01c03091000030080c02d0341c024200352400c01c00b80d100340d010300018071050400316440011242a00d0134148c01c15448008000070a80b5100c4030b41000c0c0041861746da6060420f907121030396011601c1541414081c5903200c408100700b600d05019241c4400804009c4001014a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 91253301 1250 91252051 91252069
    0x100c0b0a02030c0909070201050603060703091a0606130815060d081e040e070e090f0c090409020d08030c13080705100c0c03050f010c27030b1306061202040e1209 71
    0x44602c5243d4100490003020490806060b030b003560150f51110300300f1605082c20041254014483e203024056481591180900d100480300c0c030403001d200c5040020f0464807494211624420142c000e58445030341c03007007242d403142c02048110007100700c0d62022441e0f502d00040c0d0b107203000c1d8200e02513500d488a90700c3c040e016442c507200b4140d2520010b100000e454162181020310501680e1604242808200104441e011000b0928003d2001607414460071000e40801e4466030700701941c0000b40c1000d40d000182c1819001c003070040c4045800000c014805c0000c5000d400d81100f0180140c200f59191280240c0b02c0c5124014240c02408110181707500074815401480424003070100380c1107070741d03c03500ca441c00c0501f28007103c81e0684d110500c81c038130154030040c0618000500144003840b4401d116040c06c880c4140d100207000706c801c5401045444044901c00d85199501c09001c0201c1c59580c5170010307201e038503628240d1040745401002d220343c89010880851400c0400c110301c0c80c1203081d42c200030700e041d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 91254551 1250 91253301 91253311
    0xe12030a06050a06110105070315150c0b0c04050a080a03140918090d02150103171c0203040f06050f100308030a0917091212071e02031b100c0b0a0203 66
    0x9600c1d60720015035901c0b09043c000207000141c4c1c56500d0180142031060035181c2c09802c46041628152607641620400300c01c20040e107455920954801403c1441150010600880030780020146802e1294030300807030300144225a010703200c0001307803682e40d00c24640362101d094014010456956600c0003d90200000f464820401030421101c03581c8100d83c2c141408088800340c2c5154061109284195010840e9201c000c441c2042015250f04607582e00c045500e62244410420001165035030382c0b4090041c00751a031079282d40c0110f4803403510342800d40d07240c042c81a0035a102c40c60f210110701d5400720360200701d1050403c800016880d80c607666a82e82c10b60310080c410801541e035910b032400002c2c1c90742e075140b00748003010500c0364a0b00144001c0104c41c407070341c403540e00080e80420714810f00010010b054030604d82c1c01810644242c1201d0452605c035401d043c0c1c0c000e5050040030305540a0010956040301e2103131094540c410703c0010000103030759201c07041340e010f850546110009003c01849400642d480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 91255801 1250 91254551 91254571
    0x3011a0c030705010603150603020f30100507030c08040f030225140d051009030309170d140105060405040905070506160501111204020108040309030b090c0301050105040e1203 77
    0x50300c118042070840c0c2150800700e5460751540c10400502440b140002d007441c0ea2400c007004030070710355400a480d6a0700d00804501a8040e40c101d2144203548150251511222803090310496024546007038580031b1881c58000c4861800c008550514480c0c85421340700002c98450902c0c3d0384035522509402d0101840072400c40c0f02d90008001102e041a100311120382031201650705160030a01e154601703800280f00d2034014aa10745089011600018220b90000000b040c00180c00e64241004c4019251560001e0541005244107510104040e0020700040d603042c902007000902e80e030344000404da02849001d0344940103020610062034158480c804180c41b50003203035031055903400400d610380c203c800740c000c08214140c11039046c44028003500c00b10a405684007444c01c414070001c0c0c40070440241001e070401041c00001f500301030140303040401171600184070008034902011802c0c2d807034207810030a41c025401c0c8800021030703003050300810207a1414540582030141624400030310741d40008048040c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 91257051 1250 91255801 91255807
    0xf01020304110f2409120303070e010c0507030b04030c02120c030d030f18030903020907030501120f050307171801050405060403030503090a080f03010608010608090604110411040816081203011a 85
    0x1c2075500b601c120030480c072424044d0b502c8442c1c6208002641c15900c852a606400030810010301541c818401210b020007400d061000e20b00301e00346245400e2140d040205050020b00520041c5500541c1d078092461007101c80403181c030018503c250b2140d0001200c10740613801488001081d40c0603400c5064004002c40000507858402002c04403082207069054000c610740b14014415401d00d8195070307902c40c119040a002d85e51400b50381d024494188500078108500c1d01181c117041180501c01c556856401c00b000f098001940d50f441644c517482044101801044d6020011065020b44180c030b08403107008203c203040600e161016107803603000030a40c0c3d04a003d50221000000d54003c06841c7c150b5050103004d40329070601b2400303044503d040c1c0180040c00b40d030100300080ca4800003582544694402c24603241c03002c1c684003107800ba200300b1640c1744803084007203000b040c0d030540020001059064001c5081c0d016035540c5a56403180600904484645410001400740103515039008104001220950b45 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 91258301 1250 91257051 91257079
    0x402040c12060f090608030a080406020f210108011a131a0a1701110f0a0c02041112040c1202030703030e010c14030d050c0a0504050d08040302041107050f01020304110f 74
    0x2c503640b40e0071035898207041500600020604c2d00c5540302600c1600011890017030346100140800c0001031000340016000204001015a440d05452036101041c0100462507206070708441c001d0424040c003a0290300e071841040a0307403440994502030880c003601210080905010700ca0180900900f6040d80a045045090131900c1c1c05100d44002c0c0a6000d03810008002689250f00b9220310f80c0302d445c3c041d0020301c00840c03441d03404c000300c404180490801c01c0c6101194404503025100505050084000120b07034444a01e0440c00c0c0a440365105003110013406803104041e40c40e1044680307010f500350384142d1084c400a0301400707418001110506101c8010041ca0f0303181c269072880c26428020b40d4001080d250100581d41c0250b40d00903111104003420900e5100008100307001d40e00c80c5a2050f140000c1400030300030054100d0303004d55000f500034010604501032544441d88000400c4544e4440c4c0f40340480583c106200741d80c00f80303501c030f030080d6800641ea8003007180080301c184210741e205c1c42d24081c0107 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 91259551 1250 91258301 91258337
    0xc04060503091219021b0f0409031202030907030618030e100201022502030c030601080d0f09090e0c100302040f0506070203010e0d02061b0c030316020a0f05070e0612060402040c 78
    0x403402d813001520740504c800d8030080c04d0034800b0640c3d0314603481d540c0040b031280d540e100087c185020165000200c2807001d09013107901c00c2803040c960011a10000501510360000729004080e43e00616060001c080d4640d84140c0605a0301800fa00042403d204504203140811801e40320407840d20015040451080c01c561415013051030040108804c1c42c9804c04505052000f14070102c0e0032030240020798948174260351156450848a0100b000340c42c018580e483c021402403018140c2900e0401c0038948041c4850380c0c1d031b40b410030102d110b00e208400710b000d0340f4482d00844041d03840f40c003200012036103040f051002941000038201d03415500c0c0c202c45100804108044144101c455005080505182c840030100705501e504680e80c1030303030800108010507000000c8a42010844554038a845100361040b0309150241000a04030780b1313000c1500c024003400044000590b4410400e44090f03444100030094402a1008405000c2d0050300000d8003604d416403000800c6c41340341c10400000c136071456a030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 91260801 1250 91259551 91259557
    0x4110d060f090b060712080603150a0617070305070303140f1810050903060402151210050a050409110d1b080a11060403170d09060212160302030c040605030912 70
    0x1010155580c15010031110086003d00b0041c00d0054030400d01c1d0036060344030300005ca00480c1d0400700b8803810502103030494070108100c82c11103682031010140c5041100b02000900340f10711600700000c40e0182c00040030318012800c502100e5000c80140a03561843c1d0f13069a00c03040403500107480c070a05200b00782040003640014805100584414403a40403403c0800c035110701c40181207420401d0500403c00726440020788180c10580440b01c611003800103900c40d100d9446600c0ca82403102c1140e600b800300342000ea01481c426103e003150403036540d58440b070074803084480c68040075000c201d103840607a00c1410000c2e054003c081c010540d50f024645070a072030b03420301c000551010780c05511074403251041c030209041001c0181c07400c407221840c0c640b545d02d410fa140844846120047e1400040c1c426080c40e2552107100c4031030744072900f5511143c410400720280c0100302d5008801300310b84e081d005e04141c400e1003103031f03c1211940320090030513042c0b10088800303810052118a1309d00c28500030f400207050140103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 91262051 1250 91260801 91260809
    0x180509070c0204051506090d0c050312070b15090705031816081203040210050307030b09010f08060603010c020709020c010e102a0801050f01170c090a210204110d06 72
    0x50701c14070114501c1844110354008051004000d007076001c8444036640c1034212210140c1c2240c005da803444640c00c00c0340c0b442c0c019a000d26854850000f94901c070304040005000c54600841d4004002e607112045000c0e44c9230100101c3e5884a42d030ba00044441c1d00503800365422820303620309003007a80390b8040703224071b0560b900d00c085800c0e81a042e020841600100201080401d61440050441c00c0607404a95600f0202c4540c0003880400300004090503c2517110129a08000b04102035a507980c0c0e080e0664416103003d141c11902480c400503041d414140100610b600155000349480c5241541c008002d400103a43c0b10b0032552201074140044000700850300651980c03442c0090700000da600c03040305c00441081c4c44c80200c1c0340c00a40c800704640120045045070740684568030040c54800040b9826000001260720300480d0740140201e005440b0f000e00885941941d2112003036450360340c2e100d81600b02c100099140b6515011400041c1005d800400403542607010765810310401280e90400e071129504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 91263301 1250 91262051 91262057
    0x403080304062a1101060f030816020112060b130803090109031b0b0d06050a051002190f050102030f01030312181203060305030c010c12021204140313060315090b06070318050907 78
    0x20300144c0d800b0300c1000d00410b050f4103102d007030728a035564070302090003100d41d403010210035827880b1802e690040c1d98062034a002c100080141c1520ba0029140c02e8000c0c0a1440e0402e11001b00800c104800108490902c07005071900e400c21859641ca00001c2e01446081c04060000d943c0006210585200640102014900003182060802c003c0c000980000d41c0062301c03c007440b035004d5400d00d401003054252154400b90641d901c0707085017040002d4031204140104550301c00810072480703c0302404c00300d058920036030b640649020f40544040540345040d001c0c401401003080c520000445842d00100c4060b89420082107941e581d0711414115000319035039002c184d44a007400322005070302c1000360000d00d800400440c10550b001e5107002151000800c004e000012144500320000030805c2510410300080c1d400203226515214000c011740101e002c2000d54849013800490084003901500c11008c0c4068000c60500e109520300321b615110038101001841003035240403c5a0b1120800341e841128191 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 91264551 1250 91263301 91263317
    0x30705030d110f032e03030c050606060301081902030f0d08041208071b1104020f070201031d0a021306080601030812070806060d1104050306010306140c0403080304062a 74
    0x1c0c1d1481c040d66103404038042412010000c45190340702d05010341e90000601381c81310b1503880074280008241d140105031002c032407400301d03000801c142c1d2001341030040520400a44055407250014092103000a01030440070ba048041900d0300000d402a07038402490008044a0300c0c52500360300c90f41803c40050220000a10900400003408840c10100d083c1c41918034000383d40346040280140008580d061b032185800c00561080140103941c03111603560480108111365800c1c0081d02000705e64060320049001c0f074202402c1650705588000c1c0c460640100754041c00320312160340d0030001170440b20381d000d000d520741d61400401c1e4218100302c010701a62103140141e0703030754600c1180b01d916003100402d80c01c02c0100000401020352074900a07240c8c0082c00c20070104400c10700399032055944c05280c02c02ea400d07200d540000002e02206800800002d0600340c00e0144644801c450703a0024492400701074035498040002c40e00080260340f044800001001d05a0009031140c0f18010a441d000c07003421001075542 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 91265801 1250 91264551 91264567
    0x90b0408010e07080a03080402041805060703020301051201020906030a022a010f0b03010c0f0503060a03150b01090506030f040b0c040b0307030506090916030605090f030f0d0c051c0e0c0303070503 86
    0xf08100d4001c0e091410040050401946d07000300700f40750042000380a25240c0b0300c20301d01d104448030030300b20043c0e100c42900c0741442c118134018029082446860311491400341400d10411042c403c1b40c18805015107040d2a41d5240c00e1074402940c842545510811024090700c0790510000c8042c030450402200045a440d150000386010754201c0340c41e03940b10380d1500300084d600d42d81003081341c5903040d1310f030038400c2d12a981d080004031500404e5102500914071324464829052107070344000f0101c84242c03103508400e5100e009000243c00201c2c2d19080c2c44981e0000314021692006245138040c5c1c4c00310055141986901c00329555070829680c000c0403a49641c14020180307040080741780d000135008001d000d04802001c0102c04500c003844050f210a030b955000c228405800d01c000c101070a49032040307a80d10610b00e4048490707580302107003910620380f409601601952080c421180038400507102c2d0700e410a07044a40704000c0840c810480e907140b040c0d04440315662030900103003a0203801080610f071103c0007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 91267051 1250 91265801 91265803
    0xa090512060405010b011d01030b01120f060509011205120c1e030703140f09061b0109210306050f10020a020406060504050a0509010803070f030c0503040b0a11010c140901090b0408010e 81
    0x10207405c075411f11205100700c0702a0041095450420103007403174045140c24403580162010507846850900803402c01303a10f0508140303281c001c503045038810741c0c03605a56aa541d0300ca0700c1000321258000c00c0c9800c042e803250300e200000405410302c00203107425107417105039a00c0c40c03216010920000213842d420204882041c9a00701031244500da1000f030500b4500038111920700c00c1813080b12085403060f10041001a00040d4040f0702100c1048288020002c1d00e00d40d04042c05105142c4000e400e00d940d210406034a00c520038000d0004541c3c0c090302803280d1502001c10800480540b00030002144214820200941d0303a6010300d02c02450140c03951039840b8246400d00030044d003141c0000d401000002c0040123689000411618031b80c0e000081000c40032428030702281c08034002d1501414a11000c81d01117040724cc2c0000401448629450741002c60051203801406e80e0b07242009480420729418145155940c40700051189980501d000a069500c81502464a8006400250290390b56580c0002d11081c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 91268301 1250 91267051 91267061
    0x130b10020a050c131d010506030f0114070f27050102070905040c12080c120d0c020d020a0201050c0709090c05010323010504021606090b04050d090b030a020a09051206040501 76
    0x1040c8090101d400340381d140d507070ba904104044507000c0c0c0d044407040407008540e640300d0389062011040c003100c0d580001d2080c0b4040c10050f2101e520901034140c0254541005120341c882107518000c01060740c0d56049010b0350009052251072041c0800300098a2078050102c2603078000300c07802d9149921142c100b40009107131550a810550781546001e085c04041551100401e0071940c1c5e01e2000d140010315490000c401d4020751200c3c10b950710911400c0d05031000740d003001c0c045680f401e0b14204080b080700c19040340e880803413210f02c20150300f1030001d800140d481900109035549000b0200d590b020b6075441407070308440e4103203c01d4400600704035042c046585d060007000070084107030800034241c480302c8010180102c01841014401e076030014025500c081e06828010320107400120030400c0b01c1703045c02c1c0b00d50340c000120b034112181d0040c013802c00075541c00f0300162030568003540c2629045a54002607040250b04c18042003061112994000030346640d41c3c04e0300740c0d401801c940942888d0419107417040c00d450b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 91269551 1250 91268301 91268329
    0x180b01031217130804031b23010f080601051902030702030706031b030b180705070c060201020c0a0b04020d0803011d0105040515010804170432030c010f020c130b 71
    0x201140c0da02d002c0400c40380c41c2c19000098043c000220481c2840c003107555101c1d550000b030501c1040600075544d182503110f11003c603207218000000c0d5900060b1a910120546400709001c54200d414400f0620320030645c440d0b0080040c100b40d4030f001c44004404200041103034a010050b0b00004900f011410b003801044000c2c0043e0038240321030f00807055401034105c0c09812400170540e94040e918065552085511000302600908011074100107071b00508550008000b03540d003042050000441c20b2052086800c1000312001070b141c0028640c0e02e0070201d50002e40142d070b111008a00d1a008251503500031402030166001d00d1440450716058801b01c0c4034141d002c1d6201e54500004c20500a0003070340081d010600900c0c0c43c0e00241d4071480c241d0710220284611002c0341a0104000c905c41d51084059507511000000c0c0c03000d0712400603000c64000d5140030015030590400f0010700503c0d400355604c0c00c100411030059070031040c0020040b810448002013000c6800d500c4803c041841c0c20420705001070a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 91270801 1250 91269551 91269557
    0xe220b0f100212280801090b0a030c12020d05030f03070206090a110904140601060f03060902090a030611040305120d0b060705120a02010f060f0302040b1e01030203040303180b010312 80
    0x148141c100060b4840110a208504100300059441031883d40389400c803110b0420000462103080304507100814180b02406401002c034a042a2400545800c1442c4000c40c0e920001c00c039030700360500411400c0e0681e414012600b28101c403146600054050020f00303e4902090017050702e03480d10000080c500300f000b50245403980c10480181c0d0110311008001000740000b07940d08003450315289020300541c1e01c0b11810300d032a03004010000c80c0a86d4080382c10f4242c5515694180070150b100c1d40381c44220f10658400d2071b8460f1b1511402c000064098101180594000d60395034103061366510b6040c10b140c041910014000000a8507020710a61803003074003121402561500d0070704029a840310b075502200c1d6280003c030b10010401c0c9007000d100b500308100025990b81c0c01c0c80000d55650030300754041c0d0240800c07131140b0301b01411400c80c3d041401c0c402461b50101c0042d0580603a100005600030351002d4000d0b000c242d1600d1101806c9540701c909500450f01c951591500c641c5075040442504c0c1d1080550010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 91272051 1250 91270801 91270819
    0x10b03040c0e071715100905012601031104090f03080405100204030210120b0a06020109050c03010c0903030e0d0c080a0501050609090307031b0614070e010203040b0301060e220b0f 79
    0x260b900c44441e66110131007140c4c040c459200c0b00c15a503080c03080040410b6100c0a03d45002c150300340d0245407113003120301c20303281d108901c504a07100071100f81c069a03280c08006561401000402c48048081ca003e00002d0030004144000b40c84050303011654200c02c1e00840c40700810710081102c200841210750080d40d000f10304007401d540c009805104004809010820b0f040c540c0e00040402e17a1111802c10170007002442550b5070390300041e01070b00a8950a55040c0102e610310b500505060041c01000030f2142c3da03850041e03007595402d840f00c482540280f9006108032040800040404c1000c4c00500203540040c103102150380b6116094a4008006c02d0180d4255010310400072000425100c0c86689800e11819110048451459103427965a0107061a41442c08a281564a40003218040c0c20159942d006002e107803c010380c6c0e640f14910a0404a101c05c00040100c0c91080010301c0c1c803130000422411050340603041c00080105070094046600703641e810302e1505407501d003203c011500c40603141152 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 91273301 1250 91272051 91272061
    0xc0c070b031609030809041e0e010b0a0503060403050901050f0904061d07020106030c120807021003020406020706080c0406110a050106080709060504110d0c0c1407050a0801090b01090b1305010b03040c0e 89
    0x40354000d0a41140c0201c1d11641d0740600d00c2356180300c400340020b041c0c07010404404c50a0b800741c0a00100214640a450700000104107404c0104510b0720594140d22010702d8a1903160045841c0d501083d444502a9006e01010070180c0d500d000b828001d00c41c000114500300c82c0011050306540c0040c20302c90030b5a141900030000a015400000201c0310f45101080c84a102030030308032107a20035524005d60060b0b0b42107c0700706072a003603400741040c0d03030b596421505100e4840354180c41271001170364000302010080c0b1003000b08500c600ba41c1c260500b48401500c00c411030325900d184c291400d6030012013540d0401032050007401543c0c8a06002050100c406110340d5a0001c081050f034842c901094480b00c0d2a8005e00091601030480055240e6212403080d10084000d101c15460303484601940e0700c20324403004006019441401581603064001d0800d001a034a002d90041c010400e0002154002c0c040c0d2001440391203403489043e00800303401e1005035880c6400d01d002000c240040c0c03ca201c1100d058000d0007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 91274551 1250 91273301 91273313
    0x1b0a02060103080c030c07030614070206010e15010c021804110f01090e07020c09090c01080a02070206090d150e0114011514030402040b1003020c010e010e150c0c070b03160903 77
    0x541160f402200540d51500001c003414110b104800c00588140301c1c1403000401c003c200d0380100c008030343c1c892a55199813906401241ca0b000f00380310f14901d20703c0803004645401800e8018014544050500b45c07120521980402c0040c4000c1107801500d000f004100418000c1504003107255a6084a508226900c00c0001808094041c0111042c0990042c009516240200541c9502c0a401000c04c8554541000f84035914a82120050f0020f44d07440080b8100f405d01d0300942d06166402010942441c0300c510901c803503008400d0066030318429980303015002c14490310884040d010120001b203168000c00980560601c0e041c1e0148541024049160001c26400702c600f00090403030350b000960f13a8a480c000174002c0d140c0421540e52240e0640035024540e40c055005140c01c90320300c0024040c0d8526603e4071422105000200310b01c0390001049101100c02030406d00358011200b491840c101080d101c95149001c165400c8cd0a11440010038001c2c030301c042040e03001d40c0392414940340c07125900b103645207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 91275801 1250 91274551 91274563
    0x140607050406140f0f040f060206010b090910090c0306170604020312030702010f0c12050f040b0a0b01020a05030a02010608100204081c021009050c0f09060a05060304020a030c0e1b0a02 81
    0x82030030050001c00c203c0202401404440b942884000032131380702c00210b00030210640c820710481d020b051003080d00190103070011407480d040b1451020b005003008955024070202ea003008204099040c1071940109020056208841c262440d680d000603441d0b0411905c4160125003d0a0614950207641001b005a40009034101c04c1d503800540b40c1d441b44c6a082050303000d4440029015511070402ca40582c03030304d900809980c6c206190400920168039407502124450344282c0e40680017030303190000036a01c4034058010780c5100304e0600c11101800c8241d04c2e4242960417400505e0010307516454100210481082000e07144c0c26100001c528043c50311000035541d0345181070b030181c0003558a00000010f13000b4130107010300c0b2140c0d6030244409190303860302640310100a00102d1181d0180c03181012281040700c0154401c44001d049816858104010003d164100034422030344569070a90100020304610a800c00810030f00d1516003aa042100002d044413842c80312014031003900f40710f48503c4d203a0020300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 91277051 1250 91275801 91275809
    0xd050304120f1b03020610060507030c140a0602030a090303050601020303070801050f06070b10170c0d060f1803120c030203130b0a060f0b0705010c080603100b030c090403020a1406070504 82
    0xb10100082d66400360794001c83c4001d90680054408000c0c0203040d00412114400c8952115902005440704010340d447d0082e84130180008951284207000200100c59078000000d0b0102200c41c4150590b07500d07001d0ba44100d1705185007036101c8042c05d04245d010301425403c040c00340051411031503d10401410407105105582c440c81c110f40c0aa0340070b40722901103a142c01d0b00700e1070140d100d24040800c0080281075104000000c40c0024aa031030f5100003080c03010510030000c0250125021a40392440981200e1641410180d502c0040100301c43c80d00700005941807107502c60400440318002c0c1030040b1a4080c0c4d0180c14540100200078144442241100e15a6404940725550707449440000380104840d40207041d04082d41e100100e100c601d50300144c04d0140c407884c003d115046480400b1034100005035070540e0140d214112410b80b03c601c0d50800790b01030134040c00712218101c2480c0010f403001800d58046e809604511103007814000d03092864280340f84800f0040055003000003004140c0d201c0c0b441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 91278301 1250 91277051 91277057
    0x1141e100b07030302070b0c090612100f0312120603020a15110f0f0c060a050306010507030507080a030f050a0b03030306010c02010314010308030603100e030319140a0e0d05030412 79
    0x1000980890030128690058503400500588504041c50050001c0d801402c00f40e40c415107107000038101c9114601140ca000303201404607400c000c488600b849590601a00014060f52815408190140d8021600e0019030052000744c81103140c24502414800d84140103030f0100382004020310168607201103c83c2145c03140708041014140b0311004030b40c681c9a518001019004507100e00b2400080010345002007240b5105441c4a82c96120401040707100c0c0d9240c010100d501400082c0c8158040d03009003080c64082e0a20f50718103585a03481404590104d1a1100400c5e514080f8001d01411842415400b00c02c00d20b0400403034002c140004c1e581d00004110904004011407003d00b1644642c2000c45030005a034001d201c0707940c580c074228507e50412229075009220b038420541140c10140190360350001d04201442c515101ca01e403070f8203240030031560340a070706484001c0f11084170590140e0602c981440c8000003110203404038028244000c180e000800c21a00b40103000100e00502c0380b420303801c0c036241 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 91279551 1250 91278301 91278361
    0x209100807030b1e040b010201090f02010804020a09020406082203020a110402090d080d0b0a0608040f02010c0506180c040b011403180f0c01030609060806060915210114 74
    0x1c0402c402600c0241180c64000d410280d0143e0500074030001203400c000c040310140600c080c03040049080b511128005440040b4003d83c03200554051103d02c1d030041e0016021026064450011700281d80c002c0d408400011808401c100c2060500c03030900b424620643e1801400f2201500d000350f454040d41c001510030b01565100d01007070381d1194100e64040700068092880c00003181000c807141c2c2c1041c0e10102c034060818848911a1904241100590754151210807443d20b558840e280e4040740e01508a040c40010900c10010400400207648900306042030724407080f1038541590304240301c00080324021070030300e6444540d90381c1100c00e11540c03009843d00c071030f1290f807950311803250492199030301555030041c4040e01d803480d10003150380ba803849402c0e241403020785c1d5100d01410460f16144500112034000341c0100b4050303d04080401d8201b98804e0307413170b1010080c1400190025640000c5010760070303418442024035103001c3c002c2d81c080208400b580170305880e00c0c005504c0e0881c0100c0051022800c05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 91280801 1250 91279551 91279561
    0x10080c121015020f0106050d0c150e040501030b0718140d080906070b04140703020a051002010603050106080a0b0f0f191e0501051212090d140d0201060f0902091008 72
    0x320381000340b00000030b00040c520000c1003e51580340405103070805500380900410142006454041a503030310010f550102031606000f0b280b0480800718010422100107a41c00d45130380d540c015a4040c502070310100d4200e081808003d13024014640d04c007440720740982e400f0403003010b10398000b154210047d40c48584142547c80c0c0b03034410344105402d43e980000b0208140061101101446218070300c91024441c400c0404005240d489415201c000c1d4801700c007440c140047c0c18001e501040441301c0c0e000209105403a40d8455080d2110750f00300c400c0c2c6034080440c14060211152a80e03800500c10308100e601810422000400b03400c00074070100d01c0c6400c84180215408d069407004a261800c1e89807801900c000401c540c0c0a0203082c800c5c0e82c410030035120340301d80c10303500400c911001c21544907242e864821703518240400c1210300711080d10521800d070540c40c1c1c485070a0200c103440210640c00020243e08200a080c00c102e40c03a0007440500e4418403291181d9120300780050b030244941e0808070095076038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 91282051 1250 91280801 91280821
    0xa03020706030b0d0f050f06181207060b09010b0307030c03090b010b090a080102040801060611010c0e12010b060c0a02270c070c1211030601060f0c0206071103150610080c12 76
    0x20405004205c400d13034580030310a204000c00c07244109840241916400d40302d841d000c0e50007c5180c1041280380c0c000e15002e004060313000c0010f000c10340c0314110124680422a00213034041d242640080d402801c000100240d03958507203d46481615142002c01400b030254a0b0300b440300105000c1c40418000c001884551551280b9544008002c0500250360f90f41c1c0740c030f41d11406071070320384201004590b000c6002c1d0685a01070040c021541200e075502c5141000c00d000300300d058899064000300d01c0d583d03444100101e4558800900c002c0744e01c440200001c13400c600c10300414034054a900d0200b20074403400300302004e21794559681c01c00a0380450503100c0c1211b0404a00c18840c41d40a6142c080a81d03440108102c0018000c807591041181928402d1780d9a04090715a404004105000115241043c0300180781003401b41081c5400b031410340d80b0328060300020903d0f201d502e0308044200c1c25032004221991810b11900003003603210b131030404e1036800d160a4480d190301540030b1001d007120403040000c1440311 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 91283301 1250 91282051 91282069
    0xa0206030405191b0b030f1314030703031508010209010503011734090b01020a060228090806060102030901080f04140304060906032a0c0f0807150507020a03020706030b 74
    0x3200d0080401c030800720b40f41c40d55008501300512800c0c0e80b40f071440040d0084003041980e1096003540c650700016501e80071141800745002d18102c1d1107200000000712441d008201070f14069110341c90008013101004401c40c50b043c8164018600341e0300420400e00b041c1da0242c20b807411a19403140f4209000d00151009041442840407076074041515002c1c403c0345886c075120a0a444004040d40c9542510348500c4070070780720001c0c0902e0140e4401030051000940c0d40c0d00405001e00c1c2c242c088012010700311421092040c0f002d0608000440c1900248001c24092007080e401c80c4090004500e402d01880c0043d1880c2001020004030840c0100080c1c1440b00440004240031907030010740355966281e1001800350403040c044d00002910f0302c0b08407102c01d120014004401140c5000760350101000c880200d0315400040800c59042050710b503000c0c000b854003005850250b210704c20010711403070086009001c5a400500c01c000715800704001202090300483d54209640151070081010b02c1c095010540e004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 91284551 1250 91283301 91283323
    0x902040f02030414010606092c070509031203010503121b01110d0c09050306060603040320010902010e06031512010902060c1501050105040303021c030f14010509060109080a0206030405 81
    0x181000500040000150700461280e4881c07010b4509984070113900e507088901501804011500c0000184220745809060b03010b800a01c8501081c444005880086100010f071928000f240010488600780c3c5070500134042110480c3c020b540c107641c035110002c0d80e5405005c8205015100001d440400401200d0002006645510003030041000048140000354000c10752521021315002280c20310500c600d0030a421205e000b001813441e0740791842082420b61024100f2000e200c030a010b40c01100414607000340600e03240c0c0c40002501502d900000d02420384028440d8480c107010003c206914030030748000d00503540140d80c0000c451400e04112401000c5406019510140c04944004820f40001c0ca03640a0f4421410601d8140da03120010b49590045000080140e0041c000401115000ca0500b010755141c903e00030502c82d000030700c5641110429100d000010b05035600511290811403400c0380c00c94001e1904855407490b103c001a20f410007020003e01c55000000403c06015041004412003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 91285801 1250 91284551 91284559
    0x14030f1209060d270201031d07030605130c081011090913150f0219020a02010816170103051608070605070f050c04150311090f0411030a080301080d0207090c1b060902 73
    0x4880d04c80c07a034882d028508900280c00c0c900c135103072801e0604190114040300c0c80010501542156924006840300034241060041455030a502248030003102200034402c43c4003a01800308504600019240020701c9210003040403c01d41540f5114418255070084491800014103907580c07901d0380355004001c10400c0d156040000111483d01a0b90060683c0310fa00a02c64890012032542070782c4402c03038200060701241108002401801d800c001001c88003225103400c103101100c092035001508001e8100f5286540b12010203a0382d0341140000d00040e000240003030404501d0184000d2140c03080c80c2c4020b101400d00900303001000400c0000005900c002081805082c01c6950b0352020040d103032000b42c48c4221900c400c003185042002240c1d005200c081d202c0201a500d90310b0303481c0388a580300e10540c0c26200d8030b9880b50115103a18003842c0078100840180c03d40d102d095400920302515a0061503d00d403078841101002900005070900c40e041030015610381d07042d14240700000700035560010707401c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 91287051 1250 91285801 91285841
    0xb07050c0303031302010e18070f0e040b0306010302090a0e03030408071101030506031c030e0303071701060c020904060903020c100e01090b04050a1e08070b0406300b150414030f1209060d 82
    0x509411034020102600366a4a90042c203443d0820071003918de40503240d03501904550014405800c100044640c00b8454803404543c0840318041186198801c88050f03c00d03110104003e42008440c03488050001c0007444e050025007403c200090300c685083c28102844003904941b10301d9640070b80c0100e071245034000241c1303482c2d00e803816014000014115144013001d89440010401c1da000b07000040d585500580000003c0d40d5540d100300060a81c02401d8065210711050100d007603940c0c07020440c6109850391010a0004800005001c0308480d030000e282808040c003007071040391500c42120f0110780c210018109440041d40c4c07040d071703501e0f629006002c803030059090100705044644020b1088581c0d42d0f0f18141c0340346061b10070f02c40f580c0402c1080c1c0340a051802c60103541d907219401c26506604014034107070541c414000b203150300f54015071000d8900120413401a03a9440c0034000489042048030190421f2460154280d419228550280c1c0c40b6240115148100200e0303a0300c0050400c3c0c1276450081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 91288301 1250 91287051 91287061
    0x20c060f070224011e15050d09020303160c050a05060d02070c050a080105010311040905031209120714070501020d050a08070203040504020c0105060405071d150c06010b07050c0303031302010e18 85
    0x460f407024082c801c1c8244840c43d17030a200e0025000c100c400c44031004140c0841c046072403800c844d103a00c42a032504030951a00c110101580d81440149881180e038030080700102d12604d4564400c1100f9440a40311300241e0b0320411480d05c0c0d9600321141c00400d4640180c0d02c860300d242003c48820540c000d80e8010002c40e80c04140c0280540c005070503203019000d10301c8070052901c10001500c4402c08010981e42081c0003199204030409580c50300f103080001522070b050704042225090340c004035400e54803800300c2e0708031820108050042c5000b4040030301c0944035010902e800908184280c0740c0c00e0040010400008501c24424010344014100c003d006558450607214a41d0107000e055820320b200300d1804000c68181070045070000c15010513070b03401c0502d2280e04d104001941080001c2807414810421a0180701441480702501801c04807000c9512508142011842d0401003c8224026441001403003d00501000320444a950901c3c14009007100d40e400309230483e1135030041c00d01e05200d0302d05200e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 91289551 1250 91288301 91288363
    0x190203040f0501060e0c090103020309071e0915240e1e010e0a0f0911070f050303090d050414090916150e04060b031515030a05010f09020c060f0702 65
    0x14296020300004d200309074555140c0c10011605554000c4180342c00c00104149501035005560301c040d40c030040d10340319651800322003555280d80c460b9140000d0ba885e4180720392440d904c9403840c086101510503805508100030301014000d880403003030340c2c1c002403000c500f10310748034003981342107203c000e080b40d50040d95002c0220317a084000b6002c0c0703011555140012001d801d01241190072590343d09003003000d46251800c100300400c40d03030319101c030349001c20440c000c0440e0803022100180380c4900001c659910b4800708050412000712200341c10084100010065a9222868078a6403001183c521145849003800a40b42844007418000c500c0c140300700000b600c004491101a20002c80c4d151001d04500280c100412030b201401403030895103050010951801502500d04100d00e409004102c00d0100b100940c2c2060300201c03642400981c0301c400600490100c00448001440200f03800d6040a40c0503244546030940108148000c0907440c0002d400180700b004070a1685448607d200d501030b0032220340b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 91290801 1250 91289551 91289573
    0xd14011e050703020c0d0e1c08031012080d0507030b0d060b010e1008010e0402031204091a060a020616051606050105030f0c010906121b020c120606010903080319020304 74
    0x101100345007000103104580a4001c541e00341d0362440c081c1c98100d02c28502901d040f04c040c10180d030440f414a4884c04020320006801030070902800030144c803854505001c00c641c0381e46410500c1c45c80c09040300b00000404000c29140c042c5a941c0b0081007a40e40c0072411002001c0100c00d003903006101940d17040174442180d000309032804c800e0781d5048074440b4070310a01101e0b0100c86426400140d12034010800030f00c00402c0690042d1000703013618030851604c2d150715101c1d00940c104180c07035913a588201c818101c094100b60250300081c0c9001e424641e240c41c001e519948018111010380804001c0102e06a01c01d200301c03076102d00e03c0180390843d45040d00b00364000346801d01895009100c1c0d01c500102d80c11300003070f01032102c600513914060114244042111a40e05480ca52016940c45070703a0348040c0072403c02c2c03007205900c05a004006250b095010000d051100058000c1943c02c4002031201ca644c1c020040002d1301d400c000c126503603448016022201c45102545440820310100501080064040032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 91292051 1250 91290801 91290851
    0x906030a020913061206050921040e0709060c0b070e03070b0705070b030103020607151107120e010809030306060a0908030f040e0c0c03030a05040501020714030a0f11030304020d1401 80
    0x400001e0500e0340c2c12103132903000340c207524843c0c0c014031000101d41e030300720b91380c08403e14050b45c07a960b1b1003200c80078401c2034919000310aa0800f140500c00ca4001076245031380944a071520300e003104d103452030140101c14802d60183c400210007001940c1c85000700d403210b80c11000a4100c500301961040c0800c1f09802520044503940181400010a109007400b070300d06032600100081c0c64061150365800d08440b1000490380a591242c80740c1d02004c58401c0644400b6005445d0003c90101e12034008020b840d03011401418000c000b001d004510f803002013520750240c0e007940c980e641c80302d1000c02691403051580c805425403000080250108401310050007c0f0f45289520701881c1d03c0d07500000c015405150704003001a40300303000090b16616203030000c58009014074001890401c2548864140007680c00054451740e00c002044542c0c1d940c40780c82d520f10034030a49443c07010380511070003845e20380c030029101910502600865100340450019241103e28441e802000b00f140000c0305e051030010001d030303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 91293301 1250 91292051 91292059
    0xd0b030c0a030b370203070c0b090a030806061207030c0e06070c08070609080c06031005031605090703060302091902120f0712020906030402120f0304141309120302030406020906030a0209 82
    0x441d088a80542e44001c1d0000a801c86102c038000104d02118002504020010f00410012030240c0d008208001b041034000c840000141c50701c00024100a006907a0150002d0b006020030042008108603603400c2c20f40002043c40c01282d10041c0750300031191100c04552550380400c0005000c420000d124080b03d0403202d048080d1403409039515000d80303c0441e00c0c4602442d5070071100c10242c1c0340c07400381c00851f4040d92000781c0c02d51064840011034604405100340d503041c110010030500c240e140c69480b0b56070003075107403a0030700c28682140e01103032018801030700c150318003009042444042c01060301581c08800074241070320713520315088011544644041c3d4094000c070b02018480c41d2009054000c440110340050542461034551741d00384080084060a0102d40d405405642d18081c242071008000500480c6440980303e140001040385030602c1c0088107416a01e80a40c04000407240d8420f221422041c9c1001a1643d0755820410064482c3e0220203910400000401900c4002030b4098041e03858180d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 91294551 1250 91293301 91293331
    0x9021305040605090108060415020d11180a080a0311010905061e01080105010e010608090a0b0c071403090907050d020c070e01080607030506011b03030b0907030603050d02030f0d0b030c0a030b 84
    0x1030240f1200c4802030003040c86c076410180025001c03c045080710380c0c07503041c010801450040344c07440301002c440c40e11106401d40c0d500040d4400c0440e0402421481c40700e421504811503c1c60420f03565500e0030303070640043c180322611082609045080d40400710858000e002d58ac030300e00e0884924880c5200c08622032981168103030002c0b82e045014403c13181a5820a0003076013050b420320030255404540201103540d00c1c46060b5210707001030200720003103010f00302c61200030380c45501518001c01700790780084840c001640140300700300c100d642d4260070a130840c130701d41019680e170710711200a04080c0c440e601d0f900d800ca1040610005140c1041c000f0345040f80da03141305680558861090482c103492081d11902d00084200d500c0080001e030700135845801c4c512038200000c80d811858041b4040420468440c0046550349030104148882401031001d01801440610300c0c0075051501841c09015854402130040c0e82e55968071160b4504201c1040d00312001070024440c181c1d00c0c0340c02da800321012940444104490307 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 91295801 1250 91294551 91294559
    0x40f0b0f04030207060e1903051006090209060a14070b01080606010809010209011e1101060b0a0f02030a09090b1309050c030d030b09010510170c0703031107020609100207090213050406 81
    0x24034003480c080c40d4940c0c060080245003c50494194000e03049007580308070040404100c1e00501c4001100840c030a1000d0700110a0140ca44c000301d440c580d0101d4001c500400c180552642c0392001c80d0b88004e014209200507040d4116000e04900602e10010444030240c00042900c08001900a1040d4004d03a21071201e6620310004500341d01032031031010f01054514116148000f42d06521480110442c40e0061148c0b06011a45007550382640c81100a007000050030f42c0e03c158031144681906c40680003c500c0c0800082c0000e010742104d11814403102e41d0f4005d40d48055075601045080f01076990014003d101650400342e407102102184207121348600b1560801c070500a00400031451401046151240e10b010103009401c5030b400399200030400b10038009410200103a952500442140d00040c0d1a000702d4507020381225035a070032904108105100c198016a00d190480f21a464160b8601c0303008140c3c820103a1821500340c00c204021800883c2980d8003030300310304403c0120f50044809120156031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 91297051 1250 91295801 91295821
    0x150207270b06072102010b0d030309050d0203040303080f0402060904091203050a181112010603050717120d020a111b0405180d23030c0d0c0201060621090b040f0b 71
    0x3c3c0507401840070030303142c0003280310088a410b4220705203410300000c41c480038200c0003c1c0420200440c2200820394130342c800f200b0312400b04101c04005845000452030300c0c3c02e40c1c8000c3e003014001050720000c6100c180008045484941c02c0c1c65440b00302a100f0310103100c03a0324001d003101c1102642c02d00000d1402000074000095801900810103d00c490f800d644001d9480b0140310001c140500c90700101854941e480c060000d00c80d0100460154000c5c10680b42003910740200e444920072844426880682d0301c10b81e12140400b210f2041d0061240141e4944c44c050042d00c0d1104000c0c00c810290249031201885a1000d00d80c01c0113501c0e040300e04001c035586001c04600d0301d0154210200e22035201200107514980228610100002d0402d6907695011000507514940d0f44100e6640c900c140e13004c80c801c50018800d0054402c0091540000c1c880e003424040c000b80100c1807034100510800801c0744840d180c40481e80310640e0540c00569080c25882e05040c4401d902c00411001c4903044080300005141c080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 91298301 1250 91297051 91297057
    0xf0e010309030e130b060711010f02060106140a12060602060702070503030c0c0f06040b1603080109090b0a020307030609020304050d08010b0a090b030a0b0306040b01080606010c030504150207270b06 87
    0x140c1502c0c0c0c103400b02085014044c4030fa0007641c004031120f95400002d00c0541c0c6040240640c2442003803403c04206050340010001140e5017448801d5522030401031048035040b402d21a03011840301840d079100d522140007180c913a4001d00342c00d6041441c080000c1011940032640e244203048ada002c46440390340d111306244e5a071158203d007820603040008600e0352440c0101c0e04004140c0c0c000c0443e070a19403182190f00740c82d4405803d034030708101219008002c01d5000000e56004081400c01003000d01840c0d221003c803090010b0005520b2603000000911480c0244e02a0024242c548811500ca241c203140c00e170303592042451003a021903508400015004407407000c803600401666682c84a1390b01e01172445d905c942026002c40c40c855110244e00c1c64035141080154800c1b4002d0844007542c0d450585101d0030b0603000f90070141040000a1a000840d07084812a81128602c04102c0010034020713000303c2c246000346d0001c0341c40b85500d80b0007105894110071305655075005114100b10700c11b846410004148 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 91299551 1250 91298301 91298303
    0x1603020105092109210303070c0b0f0403080f061c030504030b15030d030b010c0209040803100902040b09091503030c0609161d130b09030406030605030102030c12250f0e010309 77
    0x80708100000e002d0030802c2801401d000c8180ca000c042184c85c460041c150f80084a0000c0000d43d19080030f0b040c000c0400e4202e4011100380342190180c1040d44000f40507190003454584208802c4001c64255121031212030b588514034510500c01c95000c2c500109180d00c1440281c0e0414060b0002c80e03042c1c401c0000d40c2070f40c1ca00017402070082c0c0781c0828081e00907110344104113041c009103400c0500235840305d8005078400ca100d1040e2076901d14180501d2010009550000d007202403060105100c1200848103c0c2e030261806c8032a440140d40d201410079664a1110150b80c04d4080030540044c0840006100f40c0502c240005540c05003000311040f81c81130001e44191030f03952101d20001c2d8215a1031644180d040700c185c0000c2d100d000c095403111801d164041e0b440c0e8403d54400030b4100013155143c0b0446010780003c900039491414600d400d101c0500034003940340e0208141e10b0101e05403008000d05001102c0606000c02564202d958010b07200180a001010202d00900a0700071a580309200d101411 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 91300801 1250 91299551 91299613
    0x6020606040e0601180908040f0510030c0509220207080702012a0204020a031503141902180c0c190201110a0b040803090c0d060504020f0a0f1a160302010509 69
    0x103680f924440c1101c61704510b800d00c5003980da92075007102082c2094002d0000c0c0c07011171a401026803500c4140551902c10145d003d0401d4071300a00c10301846da00c8412510717000307022285980d001c0d841402a40c100004424a5240710b84001040400c00220501500e1028000d80383c07021810f01c0c4000310120704002503101324000c11030001913001403074254040d1088540c40e1030001100b8400c0440014090300c180c000b61b9102466514042011104200c06103a82c1c240c11603215258a19501082c404039455450200c2c1e114100c0000e2110074840058810803100c0c1c1d400c403030402000008862110011030b5090b400511905251814003000241c0351a0081e0b01084139240c541d640c1d01c0c0c01c9555080900318056501600c000c2c83d40039030b100314044440387c1c020341000416080510400c03815010101c00766000e910314440030840442d0000740e6108803407556401050000c0302d56410380941c45649141106400307100d01110915a05502c880c0c440c03502c1c1d804440c03c42c02030b40e041c00c082d658511903071800c13 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 91302051 1250 91300801 91300813
    0x5040b09010b030a05070e0d15110a020a080c1203010308040518060d1203060b0a08010e01060201050402011e30060602030f09010c021305010303020d0e0118090203060f1906020606040e 81
    0x150720551740243e0f801621450401c0540340400b00003504800707500c0302a01da00f10305491280c0c1e080100d00c20100401d101a0905103800c1944001075141c7e40400b901416100d4085091902c041302030100701c2c0d00401c0b1800325641c80d038413480c084074150014028640902c482d11003103404c0210a40e8464000c0343c004109583c00000c694509141c2000c00b810038082540394040010340c1c1c841007000e004da11713000752035011076581412464411900140e0024085a040c10f0034000540d03000601e207031210240541881d60041140d105948040f40443d20200e54004428800c008071711860325020340e12640030081c080360b55610740480c0d580c021214107800540e400c1009912035802081c1246010b8405410f074030711440600c080c1400c580c0243d00680142e0050310300501c070140d1010700c2800d0b110090825103411711174002503c0c1c00d2075240c0a081540340d4004041615956020f035819999003004080a91044201450030100f040e580b16500152044034045400380c40e243c041c254450710b8407001010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 91303301 1250 91302051 91302061
    0x10906080a0902030109020406091a0a0308070b1e0a0204080f0c011407030306030203011802030d0513090b01051902030a090f0806150111010204030308060f03011a0f0111060f0105040b09010b03 85
    0x401811241001c9a140d0350740e1201800680b5227006840040c583c00c000001c051840031441f00301514406480741c4140c0c1d00500510014228006445100f501303d4840d141e1955444500c08191034003011080143c030b003540070809203a1040c0c000f0005d4600324810b88669182c800c4041e5640c03000030a00502042000c04108003211a042c0a0400c1501070b1402159585c0d482d00403c1c01c40742107203001143d04401c881e00e1f20650038100300c0704681800a00e0200e01d0b040c2c20390800764286503140203840f451a05c2e03040c0884c030303030781310720180c0701002c5190f101d180d1850111480a0350b207900008242c804520742c00760008641451844030700460718400c0c05131509070f46540d03044060f420502c441505000e1100d0f01e90f6a429003d1014101a40c4a51140409403c04c00c00300420400d40011440c820b80c102251744a42da030140301807071846402541c0c8500c0c004a288010380d801041c2c00c042d80b059100701c0d0304200050407040368040c102d420645007007082c500c1d00014403011031824000d2490000040001c51 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 91304551 1250 91303301 91303321
    0x20609100b03030f12010f1505030f0a0608060a15090e07050f01090f08010e07050907020d0c030e100302030105150a0c030507021c060b03010506060307020706080603030d0606080a0b01090608 84
    0x42024000b02642d29107078200c4a80c1490340c0040d1030307001c3d8980d1050014000c501302100340c000030b0800201201c0000c800264024550b100041c05003030780e000d0705808182c40340c1c00c0d50804c9001d08851001d0310034a18200e4020b100803d500350645c0c03c10341100f0000141c2c2010b42c4690b0341d003940c4200281828504240a205040e401c6060340c41c1000f030201341c0040e14191500600b000b906203a00040760408090780320600d807903060b0300203d02c40c0341d0306002d000055400189401c00000070b818a203070305040504082e1600b030f00b5081380c660015480031040284550590040d070684174101c800381c0d081c0300d400c52600c441d4014015500041074210718044042405003014021440c8020b06848100b14455150042c0c07009030082100d0707560f110741017680b01b85030070300480303910903416501a13042d40b50484c4003c0da0780c5028420001400500000307d40551410f00c12120020b12640e418002e072580c1d44001028a44216401c4455a14280c50822690300c80e0321000d040b5042c6603182c41a903110b01801c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 91305801 1250 91304551 91304561
    0xc0d0b090c041e0f03050706030e0c0a150329030106080c012106030c0e0402090601030e1e0a140a1209030803160507050a060506180c0a0302030408070605100f0602060910 75
    0x10070903c464420f0005510b0905402800c0614490b102800f5a01c0c6441d1024061741c040110251144d08012101c00382d6881d00c109a60403220044101c20054a0801c1c00f5402804020b050a004052030039282221558031180d4007481141070303008026003540c2d2490280c0b901c081c220340d02d0020340d04003040310040e0300009046600109001c400102c1aa9966440741d2408240e4084422596450108001d43c030300040c8182d8010003e080900030501084481511400240d0000c0034480e10101d130420303103c10821080c88069445003000d0059650001c3d066680c0300c1d01c0900311814005034209138180380c07244099804880d403080c90141140c480ac22111701d0303441d41c00c1d00c14040001c24040c010100710300f00000042c25024510014450802009009001640481410741e4015080c240401a03c0e050300301e50028595140044e100d8607145812803040c85006809402a07003084140090810428480030484142c0c1040c4042c166035803000346d0300c23070301e046403581000e030440326608130307414010f03045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 91307051 1250 91305801 91305839
    0x1202010809190c061106070c0204181b030605180c041d031306020c01030902010c060f090203070602010614040506030c0904021215100902070507060c1a0c0d0b090c04 73
    0x996014049070080c04010b81020714082e121a0103118080040c690003001d06000c00103001c000d40784520b840d40010780100c5400900070b0066603901c81c00c2c0c558014030302440c2c1985a101442420080001d001030321040a940800d035009403420300400d40342500328041b2301c5016801000341c060030710004c0800c002003624002c030740c400c8040c1607841901a401440103103141c8040c03003180884c650800c04028a481801030b51507062519100030440581c0c0c000000c0b0380c03c02d62020000c0341110305682110090200b03218025003501c101c0f100803481e290190041000d0700d4040c0c2c442501001030500304001c1e81c00c2038800c940c140e0403404816040713003001000e10b98030030f0000e0b142d085401c0489282510741030f498075801c03900400000510040060701040900104000703602541800e145032100c03503c0d500310b032049409000000e10000d08000c6c40700ca030880d1110280c0c00c2c25815140c20a8402d0302584490100003004d854480141441d10b040c803200c1d030040814000740341c20300d42001c2411101e200d60304a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 91308301 1250 91307051 91307053
    0xb09061f030b100f0906050c0304090b03030408030c10051b03041103011103070306030213091205070507050301060603060e06030d1d03010209120c031209060304060c0507020d08031b041202010809 86
    0x22042948550140d15428400f658502d01c04960b81c0f1001440c05540e0b4103d0420848200112070b11040e0020654040e66840c2c180080d0840004000038510f2085512541080c04040354100454002090a08020032501004d21039981c800e0000c12034090582c1d4003c40d81102400030130003007010070300ba02c150084050000101c4982401d06916560000c54051002980b00d400c10f10071401d0a000c000d804080b004010700c1051600d0ba80d1015164881920340d04120f00802e020040c800e08200c0c030402040c0103002000700c02d4440000034041d1240380681110300403140e0120340b060600280300301e0051429600c901030000d924000700b54801136406015803564090100e0078459803012513205503101402c3c0185a1302c3d030a01d0074141410782005d5000c4248400b8015400c07075403a8001180d50240d804080094002e54130b42d01500c05004041c07005e5003021000054104200c08080118001c115564000c00f000f0490034501c0350781d21880c0603c03080250600c030246c00650154038250341142c5220 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 91309551 1250 91308301 91308311
    0xc060c0c0d081e04150e06040503160f0c18060503030703080f130b090a1403070b060d0804030b0f010311040209010516060207020603070c030914211f06090b09061f03 73
    0x5040200030078001e132420b42d042019038100f80e020584510415070a000001c01401c4030786800e0700c9168a030b000345a40b800b940041040700400300700301e41c511644ca0300c8e4041c0b18404035a4488034040450421071a07600511890074101054624000080c1c1c1d05040e41943c0b490055540c5d0030f001e1550746c0d1301600901c62800c8010042c80001c540c404a9840b07003840c10020f04406c060307400c0c852a012a0080c547c45150401c0190700c0c0454449040c940e4009016244c036418000c162608100503c030342c0c0c0c805018098808240214030201c000c40d141268041c0300120500d001a108000c01c0f0701c43d40300164041407003009010b0010848440d006401c07030045000508080715034000c143d160744201c82610000d60345802c84420150056441005070050411516204015a0100d1210201ca880a100d0000d074215a90300503002000201142d50147c00e5889511420400e1400504014062811039604002e61a80141041900355201c0d6200406510800100e07003140e80480204039250000c040d203032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 91310801 1250 91309551 91309591
    0x506120a0f1b0c05190803280e1b190e1302120d0810060c060e0124030c08010506031c11010204030f0203010f090302030912011b0201020c060c0c0d08 66
    0x7854100711548191189003000560340350603030421090f80182c140160310312405d4004070386c8403004d42ea800549200550082c1c008905e510031324030b0040605c2c2c180c041c02d00c040100c0000300412601444c401d0040c03003401d00380302603080084807104101158448544108200b00c011548000c46400c5112002e000d01c1c09400e54010841d080b0981d00008102d87c440021800081d900c039a52076030280501d1010840030b800c0242c0106055014480604126200c902e094241c1c9002e500100400040c00c4207481d1458000c03984e0f904007004c921040d1600f4940800001e03031060180981442204001d01400100519240542801074003611000030042201160b400300301c801d20041c0061030088640032481e00c0780b4410542036030144001c40a0080c10f00a80c800000c1c3c00006880804001300d42c075046d10310f61482100d00400608850b40040030960515242d01d03601035008010610030141034400c180d450004002c5244292060065280e2041102c003820502c151180d54000c80746400030380b80d48840b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 91312051 1250 91310801 91310831
    0x6040302030607050c07090b100302030606090405010609141c03050a020f030309060103120516030302031819260405060715020304050d0207151d1c03020604020a0506120a0f 76
    0x3c07290f031030119a0001c2c1203c148442048100c0040c4080030041c48800c420314081400c1d148c070009003009160700400807561aa454038281ca61114015000300a952703034070031004048a41d944282c0c49102e408204c0ea8140d0708040d00c1c807040d12900188086169800d40d901180c559010401210840c0141c2001c0042001c0900c021401340c030a00f40107105950440c02c04081d20f11500303421005100c01004158911002900d05501c8141c06043c01601c0f55100010407030348001d0b0f0100c1d1081030048035204110001c101d1142d00b150307800b400c68400c2c2c003201e87c2c0760100850f140e04070a02300d0480a2000304602d10b00140100303880c80c03240060301c00c0c0d1050030849005a1300255000c0b64241c01410141c010990b04100c4c0c403004041d01d00c801044200500c03070181842480b0315001d1040d106814428800303450718000700c01c02c5080300015850901460070000e4a0703103400c0d18121b03c11020780c40300007114078024003919004148502401c4032a120030035000010b00a114000060720340740c4e0035074004030345 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 91313301 1250 91312051 91312063
    0x29030316050c010807111b030f0709051f060903110a090903050a0f02030906040603020c1c0504030605060402030c09090601020f030409020d14012103031509020a0f020f06070e0604030203 82
    0x1100744010402180c0250014045070001801c0000308034014407403810440b030014801e1111014480c205600003038110219080034410090300400d441071000014010b1301aa2020384940c42075400340c003051401c4800c12180c40c640f8454000042c003802801d10114020660304024090018003298205559008900965140d0081500402c50128100d024150800141840d0b402c1074800755203449503807000100300b40154044c0c10109640410f6009031410100a0342c0348610098078081144016094000c003258440d00040f6819410000030400c46d0401b802135074001c035030b582c554a00302416034081c08a0110000c0076181140300b005450b034400c2c2c0d424002080134020000000d0383d90412007088805640843c0d00c202040e080d19401002100c02190044150510143c80c040c2c81e142c007802c003180585280348098522302440000000c02d050503034000c00000e90952aa000f1070707803100e002681c0b29403246541850344d81100e0b000a600b0351203045138002d44840217004030b050a40703e80100e45826 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 91314551 1250 91313301 91313303
    0xf0d0504230606090c0a0c14031309050108070504020315040f0b1002070b040b0304080f04080304210209041b1a12090609030f03070509040906091529030316 69
    0x140d02400101c24070340451691035100324945000b8003190400b40d0114080308001003114409540c0450040c00b410f00c20805551a241c2024410f1060403070f2500d85600e0798003084103030a90b0103265100040004141c0600b034100ca0107400540025450001400003960000b8240040442d03560001600c0340e0740c5200340031a4000d5648002181101c42d0b061200000300b104001c410365004501c100300c101131038800c641c07da44040244a403170341c40b545012200360260450b4182081008203001c83d039490000040e008072120309800c1c60305007501c080c45510b06148181c001e034021441303800040229400203244204116510120340f502a510b000c440740c850002450303040320741c10000702c00c1c80d264001244a6003000f82c0002820b0b081c10018a00e9540f48240d000c0813024410110001c1d9240f40940f042c1d40c1c4448010703009000b409007a1500c00c0092104850440b80d040c0450300c0106480803d1241c4821201c401c6031441c41008040603a0138001c090300252980740c442000a03c0d11568003510480c402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 91315801 1250 91314551 91314563
    0x90c050603090d09170303131a0f0406050a0216110111030406030608060a0b090412140301030f050106061404090b030a1e03021002030c041412010203150103050c1207050f0d0504 78
    0x41c00e20481c0244a03102eaa408005d010030703818840e0f80007800102c1202c0c5c000300c514003040e0728090280341c968420250020000c48200d003003000c100c9080001d5451601c1103208007010031080c0c2d00d40b0f003098100e0150740000044081072a2911000400d5800c20001c0c0c6601410142d43d98001c1d40344044c42c6600903042040001d0b12000100a01c1d4000c2200d99046030b01c0740c030240203203880c1002041d64000018000341c6401341951418028501610302240240e8640360546e80d40e60312400c00d04804042c0880441c0c1c030b50701e86500091424170030300c4143d2004400b181c04c5071400e40f500c54888040c01001801c1d95160107654013000c00615858034045e981060790f42000e081e0f0361070307040207400c02c482e1899406c04c840c010001c0005a2041c0b20881c0c003521181d032807101e905e00304038002c03840405440514400e01d44c80002444008400460313103031401c4209a0f8240001c0d0340c2c0c80082b0340e8500451140c001c03083e4800000c00e044a0180000d03040c0969510382c0c00b400e00d03074060407081c01d46109546c15514 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 91317051 1250 91315801 91315813
    0x605010603020705100209012f010f0e0d020109050d18090c0c0c090b0109050922150606020a0507090509030f0424031802060c0307061a09060d0510090c05060309 71
    0x104038080c804840840310317014045003440740c20030019042c054285d1400415011005030007480c0b031032800020308288210701c001c01514a60701030704d100802d4001c00c51000c500c98242c0309600c60744140564862258000083d0032203000001d401d482c090f5104401800b6580a410041620045881165503070ba6580d034a04240c01d0740d5041c1900c00001d40d800c44880541410348001080c1d03000301c1c24400b196070695156020ba514001400321490a00000352009083e030b806402c14041000940c100840d008034080041c5695888180d80e43c01c88070345c0c004c03c940c202540400c48050154020755000f4000740560b032501d28aa903144030158855040a0b4581c800c806013030b04021801c0004848282007070604000c01340c0b0140114002904e1000c3c001d02c100000290f841c5048030034003e6615060b40700c6000c2c0092602030100b460306030003110380140a01d4182001500a240c4003001e080040c2e00480640b00354155040303201c0290188400a0783c200c0d01805000680713807190f90046d486038000b40d01a21f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 91318301 1250 91317051 91317053
    0x5090717071e06020601260d030f051315090c05060f07050105060d051902030709060b03041a070f0c0206040e0412031506021f0609060e010806090a0309050603060301060306050106030207 82
    0x80b0211801e5120300100030500e40c01d001a60f0001748060668011840030500b80c28001980c202400e0261507440c2d09004540c0600310203034060f008900c08140d11001401a83e5402820461a9048950140c000c0036501801d484411540d806038401900500c1400b036080d403507000ac10032552040100c95000178000aa07041880b00078403030749400c000c0850740070340c110b511a20b620340e80740004868403910aa002d000c0c202199800c000703040c002c0c901100207112040da1421400480d410448003130311140045242101c1c00340803614801d200303546503140c170740349006038010460365000e85950881e0007410070080401c0340e48071200d003648070350311403102c907802c0018441c8010266003202c19018043c05580009001d060740105100d60030b4049805d0004241100310a500301611a41d807182900e00d03d410f4021449442166445058500c90350440e60300c0c0d19042261540c400c00440302400141080c10107102c90f140840085400c41c50042c0080780441d1a82c40f080101e840a9000c000030076030000c7d07920 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 91319551 1250 91318301 91318319
    0x405091f06020a030903081b0708010c031803050301120302031c0515010c02060415032c070605040f0b0a03140a05011a03100501081008060f060103050a0b01020c040509071707 77
    0x18054a074910142421012564000c1d0501c4a14003005048800104881d8200e240c0000c412070f0801000b0115110b0b01d6a03441524020160038004d0707000281031410035140340384000d2110301004e905a55080c9540e2900c0451400c003003801408900f10300040001801044010401c0311082c2d05000780040c890400c8000c044403048030080031414403200e1000768000da5100c4d41518101d44109080c0750418001d035000302c0040003002c440310045c203600c1d044461264000c04c80318604010040844030b540c2d4452009075420300851240a801e82e040e07000501000c00320001500b01d0400c9810082503090b80e440000440200403070700f42d802c0c55030341c000420001c070b01c941c48042103d000b030ba481440c40c213107a4661004851940200d40c10701110301d0200d4414041644034030000c00c50b51041d2030b40c6040610001c00c103410300780c8649000a083c0740225005d10750904c03802200c000141c0081081d001d1f0f607014000504001014050700d80120070001918000c0344015504c1814548050200541814a18 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 91320801 1250 91319551 91319611
    0x90b0901080606091503070315061e03080414040b310207020306040b2d07030614091303140d09050115051503130804060509030d030e0a080c0102040509 67
    0x41c4803258404003d0007a80c4d224a0065074001c8170511181081d040e0400c0400e2800710309500c01045001020042103000d1a80e80c440f4094071041190248100801241c0e4102d444483c0070160846400300800c11a142c0c041c420202d801601800214034030301c2d4640040d03407003400b003e85500c0010078004500c03d140718000410800455408045061003070640100365100801070004249041020200d40041201d000c0303040e1071a1034660340040d01d03031030f62106940c1c880147c500384007003406c022000c201c09280987e828680135000e050003010f03503a07075035903007901d051442070a400740b00b41c107404d10903540040401010150000f54010a81d228241b03015401c4440c505030111209500e014240503542e244000002c0005c4516002c135141d4071000c0c9034014140115000a0040c1c400040004440e604000602200d1504505407114044286000e8043d540100e81a035485d03005031185000041c2e03c04060101003000c1400141019115401701303901c0030003030300c1d59944503008034003c42c00c0100c5405d00b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 91322051 1250 91320801 91320809
    0x50f0106030c02010f0f141f090b12030723030304151e150509010b120103120e060406030c0f090312050c0a0609050705190506030106050f090915010906052d0f04090b0901 75
    0x700035002341d9102c607668001002030080303039070560321005140020768031228500c00380f2281800352a500c030075920703081182c568a403656009a21150b0002c003900d51001c0103891003243c00c061008c0c06513046500e10401049000d8100c0f110001504a44400c9001031154003402d01e134442c0014042800d110400101e500c05a00c40c07a40080c040100480481800c0c5600703044950100c107807405003a8143c03050301c1910100c410b00d034002c200400c0004081758582c010340c90080003521400120042c6d410210b170592410301010b00345034010613118002c5482400101038650050042c0e030741d500280d0b6a650103607003c00d070003950103a00001082c000e034500490b40440d06000c0c550300100703280c9041e01140040c00305200d80c0e4140080401d070180c0400012007202c8862000034104000d0b0318050b84200b00602d900641e450004140b084040307210b80c0500c00b207030440b07205d607070038180c9003000078042010412a45407202d240d044140180ca001103800e5003e44003401c4a07e90118a8103104014000781c01d00580c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 91323301 1250 91322051 91322071
    0x20d02010e06131202030d05040c060f17070e010909020309010204080106060908070315061205010608060606071a0703060b0f190905061c0209030a2301050f0106030c02010f0f14 78
    0x418044883e00001078022000d0380000100518245040c0590860007991990131226003081304010070001102c040506503511519800070041060340111452542029120080480c075008109030a0180442c4200380c1c0301454080700d0241c0f104002c41c140c0e0001d88212405030340210301402880028000d0002506c154503040728071134680324a140d9200c00c144009441d0b00b501403840000301289030440002340040300c0c490156100d00f403030464000c0070305c0e100d0344a060090401140c0286080320031034003982d80110b1a100f00109940c40c1590040c0c003e442041130583c3c0302d000084004210003d00080610000303456240d41c0c1c00c00112426680307103004d030006c00140e40c10500081e0348010a499068400301100c840d420328000050340248105901c1350360610580806000b04164900c0c054030b140103001d07007800308d00c5844501c18240d03101940c607007000904034001403226910a52054000d801188008154240d2003548101100c1000541509a41d141c407a19903002c00008205500049444 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 91324551 1250 91323301 91323313
    0x7060e0c011b17190c0c05090105060702060c0a020d0c030510140c0a0c02041104050111010b060a0c0c050a0e071707081303031b110714181e0106020d02010e 69
    0x40c0b00300c0d1041c1001a0000c022620000c0400c42c2d0042410540d00a00500b400c1e14200d10f803001d401034651580f903407086801c3d1030024404907641c10802030481c12250b0141101d030070550554200025a0080e401a80c0b05100702d10144015950700c2018504050049402d01511425400d03d64201040520807403505820911580010100c03041000d80c0249200302007038545a42c400101c0b4000304540003e507129007450350420544030f1440046c0101c41c42600c41081e5540d111181d01d00f42e603d40340540d644a0018400940518020004081010712644801e08080e4071600010200000c5403c4281e00c40503280c10007074003a40043d060811440000300e00449442c00d0100102520002000281c0c2c0f07005981c1c0800c101400381c2c000014400c90310707500305c2c8800d41000c1c0040c103e03203168a4a2000e80320700000000d22007004010030289043c05001c2030174000e00c4a000e6110321001504410f1201c00616084031140201078103a4040c1c10700350302625803500e104a00a0030348400311900030701a0401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 91325801 1250 91324551 91324577
    0x100801050c0406030b0f030124050d080a03051b19080f04020a05063405071505031b07050d0e03060106021b091018062103120b060f07060e0c01 63
    0x7800c156030481c0c0b50b500d00802c0f48422403011075052240100325035015800c09000202c964050009407948201102d1001e208598810412030707a15001c08000c0c090040411014814a1003604071035440510707646102d00303040b07200f444140180e0000313002019084c1c00070f60080794264030208060700400744d1034005602d800c040d00003500192103481500d1159030300203021130030004104240e0408105480381201d07c5420901c81c1801203510303c004951900841501190b1142c0301000d481a554269813000d0840d07840700005c0084210320302e0b20480e114400e0100000244040200800401c1030707550324140c880b9000285882c000c01070700400c056400030030300c20000500d02d44003070800300c40446048004d03880f01d9110000d4414550010381240205071038101a08849400800c116800c1c0c0c21000c038941d034400b00f8400c0c200350b4440020b000a06050030794075154201d4100c0d1202c10b00c01000e503480d04101e124604159807003001d0480780c036529441c01e50104c03102400b103440202070a00381238030304400d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 91327051 1250 91325801 91325821
    0x9060b0d020f10030b0307030c1a0c030f030615210a0b1018030512030117030310091a030d11060603010603050a020d05010603080703052d04060f050909010e10080105 73
    0x50b558107000791502d800c5071554900c2a00454640d607400b9040e01c40540d00c17402d0244000e482c1c0d00030283c101500e4800e0740b4000c3e0300c030012104a90103481c09181410007a0312011405da001030a0b40c3c1d40706001e025031a12410f102402040c142c1903c03e1540c000c9013600d000448090001045010f08624050484036940c031101240b2440020b5032800ca044c0992907a040c0720900745582001d000340c80b40e00060002121381e04010b5060b580c455841c0f540e001c10032188103a03039200454000c40c4030380c40c509081014040c40e4000c035203c03154882c1010320034405c0303201013441d00300d580c043c68000801d080e1840000032010301403190030200c15002400041d056440c5d4a69070480480001e00031155601c1c4102440350a50008014640c014403031641d0b13002d18180105140c00003502441c5114000362a00e05944e844e400d00710820000b820703050f05081c68824141e034021200407500342402001c1018400654070008154080d254185040c082410100d1080011120035001200c00e40c0c5800240811461 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 91328301 1250 91327051 91327069
    0x6020705061e070302150a180b0601110d030605120a0f110d141005010608040b010e100504050907080d080408040b0318030304062403020d06020a0507020a030609060b0d02 75
    0x24054a62a0791004041c00381d034901488070350102e4140d40c0219407502003650100d0314075140103440c2c03411101516400340c50000c64064600480742d200083e40148001b580c29028181d215405062032454810202103041c01d11262260b0040002d540d0207041c4001d00d060060b805190722410020b041ca000c00c1e0380c2e0702c59112004080908104000300c483c80a0b65120890401501d510a81c2d521070f0500d000d080343e55070046c110250780498182030001c50020b1080100e01e00c11608130110780020791a00262245c0601c0290000c03012403038006000c0346940b2280246801001da2400a04020340b511012074144401040c04008005505042c840811002010759042d1543c1d0860559207441d030742c0c602c0710500d0410407130082c0c07030001204120600c0040c0d48080c034845d0041030001c0c140c081810841d0402803882c0002035009040d0713004240810041d50240500d8401424001d2038a0025000244c00d804240c0c01200c0740c3e41c4401c588020003d107030048032440c8e07405030b07020b071202150380e40000c641e44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 91329551 1250 91328301 91328309
    0x1090b0a02060f150604030c0e0f0c0d0e010209041e0c0302090102032b09110901240309051203130c12020d02011209080415080c0a30060f051009060207 67
    0x40c0000c55101c4c40c0c02c1004498050004082c550b03140c1d40d80ca030001c000417081c4603c0c0030000740a000181c80e1200106014801d0b810008010b19008804501c1c4008001d2480104220f66091001c403106880790b1047c20926481107501c4071800261840300010f030341d0404041001c0600500159082da42c0000985421b210403109501218070380b445100c1c0d00303460526002100d14100034117881031041070503642c44c03035420994444c206030fa00c0b0002912501c4054500d20240002558000c120610a0340f0281d880e91040d000d031807022150403040000740d0000e581103401c64841d01c00060811182e4240480104110120b0301c03501c00132500068014940b07480040e0500007030035020b4030782d281168000c01449a0100400da02c0c0d503101d1480a584c84190550034010400d2540854410444841541c1400c461641c1d4101c10b85180c1100c40802403901000900d61600d14107451440001170050102410400407140e5640e860401049405120144000c0501c85000420302059a000c81c14006035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 91330801 1250 91329551 91329571
    0x1050a0b192412051003030314011a0c0102040b03160801060905060d111c0c030e06010302090604020703050708031608010501080403020a140a080d060305060105120604060f0e01020a0e01090b0a0206 87
    0x100302c0350070280c0d5440c4444042d00400c901d03000c1004000700e079000880d420741c0e010365000c0040030342084910541c080b0a0040c1c01010380300e648054950f5240c0300090824005480015040ca40c0d0781a20f1fa845c1e800641e001400c5010001292190950280c0070394010001468014412490440826151311406401c041580c0d102c04101812100007400c43ea000012039400082180040c5a42c1009104040524000034101201c52409020006225060329001482c01a031a00c1e08402c00c0700035400000e0403000d00106214200105203a040510311803000e01c840a068a0ba15020082030007078144c22003818000400705103c0860340c002406e03411140e000418000e00e8003081010703450700c9285030004120040014030810f81d81441e801580880e840b440c00c0703881d0781e62201c0c2000348903500c941da02c41d00c41d40001d0001d408140c25402c0440651254280042e103995818555800e90307000142d1240030800c0c180746220996170001058004000c400011030074030b044000000c1d2182406840d910701 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 91332051 1250 91330801 91330859
    0x140103050403050403020915030d0e09060f04060302090a09050613050c0f1f1d01080c0a0503060f0a1d0601050c031b030d0603030207080105010602070f030f0c0801050a0b19 76
    0x402d030048084034051a0010190b04407403400e182580e8814481c2d90700c0c40d01900400c00c121586034011907090308884801030114007966620b005200d1a400841c1c4544da000e9101e440000141e2240081907015205003c804a1825450708166240c910013410720018040403048440126401290503420305030110f41d4030503429488000242e8884504c0c101c442c0f6428501c1000001541040800c000e00c580381c510b1204c01c15401c001500c503003404682c655980f85040140d09034452140c4002e692002c0001c1140d842c0005000104180341c1007900401d41e201d2010003c4030004568030019980607809183c030b035241c1810000050785034080d4042c40203071842c901011044951050081c0c98444001c2202001141c0d6030f824001d680e605140704230030f002c0d403900c000802c1451000c500d02054500b400041c2041600c0c50b40c503a20399032004a8203543c502c101c3d0702d020035880c800f801018042c408054000c1510b55801c01080071101c41b0b9140358a114441d204100b2a491503111440d8a401583c000c07100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 91333301 1250 91332051 91332053
    0xc242a0c0f02060c0f1c11010b01170711071508060f01140703050c330403020717030c01090305040f0b0c0601030303051b0d140603030315060d060506070602030f0c041401030504 78
    0x214091100382e01e40e24601900540882c6e1049803000b1700310360006680e400c03c907a162000001e0172a031100301414001200c115851040d2503200e030032180c2019881c0340c4906803800700e09485007441c02c260004000c042c60300c010b5800580e0b0101c44a500400103c803070a0036103982d10300180000c0c912450910b11100041041d900303050042040e10784505010069a4180040444c5256101d103806100b80c2e150308000d4010f18205000d081d4140300740c1d0f058004000c00f90a0403100c01810000b0515180d10f4030003000101c080060130f00948584600c6919a00e0721282004042c00f40d40a50750410120703000d00340041c0710100d900048060440ea0582000103441d12036000500b00c0c1412000e04004910002805011071202640000c0712010720103034a0000361104d01c1010384034401522110747d9903003944213544903450082e000b000c1d081060f40c00050841c0c3d80c0c00c04503400d41c1101c8400d0315402c2c2d000c02004403024010040300d80c00b00d907a101161515040c9150600d901504880d90b0f17042540e01e80000d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 91334551 1250 91333301 91333303
    0x7050a0905120106080102070803041202030c03122203020610050618100207051e0301050c070f060509070504090b0a0b03010e03040b0702010315091d010209010c242a0c0f02060c 78
    0x1402e17500f402903582d40414100b203581a40152005c80719039410150701e41c2c0e850f20202c05c0d2824244e420b0042c610b000c002c100d1f0800002d00240400707418824050703610008038044003c0c1001c45220307401500552410801450612180764042c501030241001003101100c4400c280e200100f6046a0110030058948001c07890082503402181d04811b5000941601c03a01c0300c841c424000382c01300c000f030082e9911900a0079090051718001048000340000f110f000130308603005240e0098031030045030701d120b59440c006019a0810001543c03482211790510012401c0c1e4002c003076101c00280d0091145452540300c040d84c1c1e03c5244620070202c40701061460440e07100b5000302241112070b40c008040301d038481d80b24100a01140013018801d0422040d0103101030b81c103000303462510105841d040d1882006482d104413480c0f1100340341001600862140321201082c0c03085100c020a0605a81441c0c2000190381c5010703980b141403001440190740407035000801d80c010114240d03506962807916612494106 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 91335801 1250 91334551 91334561
    0x105030a02130b0d0605010507080304111f03090b1b070b130206180120120c030f04030f03080106020f030301050d03020307060629030c030103020103091406040b0105040507050a09051201 82
    0x252107008403000030410f807a6800703004c69500381401003044595510040d90346103c1e28200070072045d0284000b901040e012006042c0400f4090304000034000d8480010028854110725400881e65820440e004d01140c0d6241e07d9001688862209600001010060b2940100680200003c0500c00000e004c940f000d8810030700a2f034060903043e19545146c80c3c249920350100c080d18002042d5141b170201c11140c4034803448101c48400060300010b000c4204410081d40700600b0044288810460070705072511101c0200006c60244d03000d000503001610b0010a01801030f40000115803140c1b1050380704400c0072045a044407011580102103444900e4143d003580529070020b05040d161400025580c010f002e00802601c84918000360241ca401c090400c89001c00d4070f56100c01794003407005000550013580110308544c01948070001101681883d245009001c0b07a0880301c40410307000412081c1018080c540c0c03c54810b080030b40c1000147c201c020482c4030544591442440c800669094003a429400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 91337051 1250 91335801 91335817
    0xb190c0b0a020d0506091e0c070807050f06090f03180f09150114070b012108040f0303080f160c080f0a0905030c0102060f0a0f230f0a05070c020105030a02 68
    0x40c605081d4400082d0010700008560304c0c24400000c29900d803080c1803a00c10461124181c00d014915800079080300401030201c2041d0104100c40d40c08100040003520402d0300c9038009011803281021080d05200000c0c1c030700d400690203000b240d06081d07008003d684542c0310350450030240b05042070000b940003000c16000c0d80c0101681d801d101c0d00b4501c00102040c400310a032070f5081186007543c425043c034814041e020b4009005440140808982d2400d010800f80c1031b251070340849400c07516061000c0e8801da21010402c00f00000420401d0f402400b00c503800a59840d44191628103420500c4030b000e2040c0c4c010081043c4442d1950400a5502c04c1c2e0b40c100310459809905c07880407101c0900f03c03c0d40b80c003c3c07a10900c2165407803015903200046d828401e500d00b030041a0b00da1122000c17500170b06442c040380c1c1c206546802c2c80c81e00c0a07444801204034501101c9181c026401d00c2c018020030780710080c00014941e41080200100c00d81c00a0540301d02e294280fa04559a03500e400d81200240543c0c20 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 91338301 1250 91337051 91337063
    0x3060a1a070f0303050604050709080703080d090222060e01030c0308070311030d0902030f03040f15030b0607031709060403082205121b0f06011206021c15060203040b190c 75
    0xb5201003419403580c8064480c9105680807c526201c41354183e0710754401d441103046580c0070b40070500008012070007500f0110312800f4042020350f542d070300060740c0c91078051842c4010703c035040ca02e03010021a03008001c0185401d01100f0850350550721440c0c1d5404181c0000743c4523300c00901d800403d840340d002c001b1034100e1030060b2602e0390104103c0c1005031141000c283c1c0303c0c0c45103041c0c4c001d03240e1010003200e04540503043c0e4000341c64682400350780f045804000d180140343c0d80d078000d9903172601d8901c010f01c0f00d40d00ca40d44070b03d15485c0d88648130320981800741c01140190700840401c00041e4200007016005104090b040c0c03000030b00d038a200301900b010402c0042c110f00803107071128110007150000c0e000300394000e0aa480354a084d1100d0355904c00440f0f5818680d54843d0004128001e00d05041d40b040c1800354074090b01c0d100500c04018051640f481c0441c4d00c1550311609215681d034207413003680107088035102a41c13810740b4081d12160740340074079085800c420310754504006406002d080703010485a480b203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 91339551 1250 91338301 91338323
    0x605060d021e07050712081e090a05030c0d0308060102190302071503090b0403030203130512040e0916030308060a03140609120c0c04020c0703050f030a090f0302030d030e01020409090f021503060a1a07 88
    0x1c0d23811107260086a070850281c202c1e968080341501d400309a241416001515445001036180c40498110030041c1c030590542c0658200340aa40d00d064171240c0100340242c0040ca142e614004035118100c04004803102050702e071110107800914440e001c9608036415240260302c0e61900d2150b60203445c0300150081c40c5210b81002c0140b003100e960068800c50707481900c04030f555518801c1454485160003c80508204811010300020b40215080754000b10302074000741f5029125507512010103200ca0f060b080650008080015048003000f0004a401e44820354908140c1c010031880c2d914010024903510454000c03804942000003000048001c6402c80125034002008909054490f07200101c00c00004043d03030004600b411281e40b00e50106e03903002d001050f02d481d012104500500d44042c00341340f155000c11000600f136a40380240003182c0d024102d218104803081c81000900e9401c0d031407410195105004121781941e400d1194812a0403102c1c20188105441842d920144a8000000c100760710403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 91340801 1250 91339551 91339597
    0xc0a080f060a020319050a020d02071406010b13050f0f0604030309090608060c0d020703090e01080709230610050d110403050c03010501080c060703030605060d021e0705071208 77
    0x503100024400a2081e20110340b01c0309008800d0344001c030b44031000000407400720b101440c041e40c002d5030f21071b070748aa0040c28429001c03000000d980c044070003030b40c800048400d05d07101d5540c01e219160050040100c51440c00041482900074000b15100d00da00c81d0030b40381d503041c3c180d84402c410000c0c541001803030141d4454907072a0142c19130f40c080c01490082490070030040317a00400041c2aa00500c0b5103202c0d14100340100d40310001941c8091012400c0248050f80065202e4455007001c0c042d00003680a405018189000b80c0c00301c075000140c0c480c1c981e030b2101d9520b12484601060701d400100507a0440015410301d10142c9080c4641c0b01c00d40c01c1a494502010003102200780a00140c034802d90136550901c074040201401e0751400e0041d00307280e8000c507105010500d0240003c01c08148203003004200165100005030300340d00882030005030203800143d010b02094005c0f0340707110b4207000c4000e031030300f4449580c450304c5d40da60b494010082450072111802c0f0034000d03800c095410a81141e002e4007a80b10780 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 91342051 1250 91340801 91340803
    0x60203010e0a06031e14162139060203072003060f1803040806060406060c0305090d06022a1011180111190c1203120b030c0a08 56
    0x1003407140d01410101103001c5094442c940c00b40c101201c1d0001046580c81240f000c0034034a01c1c45210040350807540640c07508074139041c00d021a0820b101c5199030b0b400352500c0c0c540000001f2292031300c40102e543c1a240b0b9440000c4250a1494a100003880d680040c10b0240740c08440050040300542000c58248000040304c035400001003c80034402e442d95221401d6540700c44506004940d0302c9070341a00040000b8000742d21101c8400d49c07007502000c645030244210202a410f640c000d8008203c513030040020020641003c3c06024000d101c03524126002c083c094800404030b00400d00054407413402400c0c0030f02070042c02c1e015207403403868203c10050f00d0004200110000034120090070a540501000034000655502c920034202060540b102e10300a5061003098490428a40c01c5041c0007000c90300310143d14041100c0704211144103040a01103415050035240c0e480d0ba0f60051041d459841110350010303034404480044030003106404646000d2003c0040e0522181ea0740407a00032901d8400003540d480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 91343301 1250 91342051 91342057
    0xb09150a09020102161401030506030c0a080604140606010507240606050c1005010f06030e0a120c170418020702030124030605010b04060512090106030804030606080607030b011e05090d0602 83
    0x2c401d808a50821034020b104905869280c4108050040d500b6480107031940640c20a43e031081c402010759881085103800210300240c55003100181da80848104010400c4643c03414003180035400c010700c1903281c030a000a00d107201e03034203000708a05106070b21810300600d051543d0780c030300d030020006019140e1039010062041d00140d80107041840340700b12961458009101d918182c1e420319421039000c42c100751041e0061f1000241c02200f92081540e100d000c50b005032952808002240d03503400e00b408250610340720081c4021040c80442c28108030800076100e4403171881c101c42104010241c3c40f00741e04d00001c5c0c01407203041407562003250110500d4030f180e0007408848064034419941003280340d03240d401e0080180924012407010840407ca0108a4001500303401d91015000c00049400c50310380d40d40d54103d81065100311002500c0d42c1050003500d0090102c1503210b003031890200107405c14540002c2c448a50030154030303c240c00e01c1055110440c031500842d00454400b40040381c070349280c1e10307003103000354 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 91344551 1250 91343301 91343303
    0x71101080604090201080105010c0213020c030703110f15040807020909010506040e0705060904020f040f06020c0a0603140a05070201111612140708180409030e03010c0513030b09150a09 81
    0x180d41000140842c6050311030200582e40680d11404c03140c0c00c00005484481641d48107aa0220451234120f1900c0c8844c002040c00e400c21030055525a8482d25002d080d000440a4100c403a410500005c20003074400605d45000300f07815020090103403a1030070301da0854414940c0194101e00c1407010000c01c14030541000340100b0f002c1d20200a949012001c540d03d4400c0d50007030030f40c000c804120000380c0e40380603009041ba51615913285803500c1da5622420542c84140d0788510003503000b040c5c0e03500c480c0c982030000500404260900b80b14650b201040c1c4c070000f14004007800700c100d0340c660104000b01e2003503001c0801c800e116100642e8890303102034210100f40f01c0d014200d408170703000014415420700c50340007507420300b40c0c880c0e50b2070402040344d45a26047c2c20001ea020010003011507421a6030740c03540600d455481c001e445407150084600180340c00e40b00c503002260180602005031180d1a0001b2a5100440383c00c0040344046481c0d1189260509043c140c15400c801900400c1c004501d000f80e0061401c6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 91345801 1250 91344551 91344557
    0xd031d100b01081501020c2b0c030b0a11031b04150e04050a0204030201050f03040201140301170f03040f2c04120905010810050904051c050a120605090c130902071101 73
    0x3551030b104c0001201e201604c0c9240107800c0002e1078482824103808042c00c90300c28201c040320032040840c002c0760019407440e081d542051200d20070410700c412982e00c59004100590300303024081144203010002c0c030001c1d081c8203859203114880c0c3c400c0882003083d1406000b0201119090380800700000f488107002d2000c09228038a00f0001c07a050591714405c88084a82c1a150207080540062105038ac94200038020390500c41014150480300261000960280102410080f0b00300024161607103444080c004020700c5a00801040c4000700e054804082168190840f03594412929420030100c80060003618443d510004240001c001d0464200410300d003090369500840d581c0c8100455000c8020345594280f40380680781402941802a0310551080c060011140d0300c28484000c41e50700d91103800c08000142004c07403030b84a0540e00a00d4510641e6800c1010b2242a0808000904440010340311000802002940b50311100030020084003c04110808640714641800c154400f100440941800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 91347051 1250 91345801 91345817
    0x90901150306080d091d010f0b0f0412060207120215010b0d0e011d060a09080f0702030a0512030106020c0105120a021b0106030302241018020f04031103070f080d031d100b01 76
    0x6051b50540700d4100e982c20141e0200061401d02a803100b50310400009121100800011460b004001030b081c102d140709440050380c90100341000040449101342070001c640280c0d65415003000c0d4003503428192080c00c44225504c04541031540700801c02c041003604254206a08001a001461020600640d428050741c1c00d507650344114808690b0b5071140242842e0703003401070650021081000d402c14510140441e10450469141c0c2490042e01c02c0500d058a107000005100701c55050202c04000d100a003081c600780102e06806800d80ca100a1404200c2503000c660b01c2c4008190040e00014403903510000c000f00c940360306000b500d030000c0745000c080031545c809800d404008900b484910401d0218080807150b41807503901c102c80705a041e050003285400740580448075a044001b0002181f00d0300c2101d14200e0000141800d15500d94000c0380d400c0200c80e810098400d0204146000b80c01520740001c01d00040c248008451010607039505052003480c45003400d02c1c00c02d6121003445402600d40d494 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 91348301 1250 91347051 91347089
    0x10213031b1a030a110f0d0504060e010e0a060207030c080c0a06060501090302061206060915030a050105060304080a110709050415150b0f09040e0307210203090901150306080d09 78
    0x1034600c403114034034581100800c000344c1c10100c1a813040b0294001003140c40d2800c00d40c42e5901c101c0c0d070442c0d200074800342c0d550310a000c108200d500c0b41340010848480240300143c241c103a1755485295042c40a8103090b00003a040080600c00d105442ca403581c0881c20f15295100c00d049166103a50402080360101d15120340450b0070340c09482c0d044c04803a802480503103084807080b00d10300f42c0d00010382080d4102405008403c241d55a02d29107020f00c55062440b581c80740b50a5a003242075a506a116a005a60810610011412940c100c44a002250810860541022105511b014130703990107c0419490070b402d100400000e039918000c15294480180b100fa290090005111031440c4141d41d08444108405040c22950b10003400c0c1c140c83c020030004802000310380d40c03030840e84201e500300c8141c411181a540d044131000316040322014248000d40c14818040041680141d041c0681d41e50f041080880c8494035110344c002c84080c10700d0605685148010040182010b00d082c06800601424440048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 91349551 1250 91348301 91348319
    0x40314030d020406051b2b030e0706050c06100b0405101205040f02091005010915050d0614130501030809120138060c0601050d020d0b04030c03200c010f02010213031b 73
    0x1d1f8001d0b01600012507820174000700454a655104d4260240360b101da214010100d03041c00400000c04042d04e41d103961320014008a03003400300c0281a105502142c540078080d0081c0c1e0b0040e03e060328000e50704098030300d00400056481c90104440680300c20700304001c00080145103107452402502c2503503441c2c0075466800061024078028002c4c0c9000800d1650200190141c054a03281c1000c06810411300e090a010388000644403035810441c81a2100040d0741711604050500d4107003204512010007865041d42e0740c0742d0184c81245030b0148210350240c001c040f02c14080d448403880c102c1c03180d1103050404c440e201c01440200405004c90a00d0340c0c0c0300010b00c541c245041201d014030f40e03030707409404261700f0041004a104010441680c2000d14001071900003410000c50740c1c015402900e031440031105601d80102a02004a641030491008408645801e0270018081e14015402d08004a2265a41c4c03c02c0b802402010f106001110602030000103100d0752109005403803418180b840801c0e9160b05250b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 91350801 1250 91349551 91349563
    0xa0806070f030c031e0903020610031a10120b0601030b010224090c030304030305031005040c0e04050601030b0d0b090d030608060f040302150a0509010b0411040314030d020406051b 79
    0x3500850041566800030340c0c442da2000800038030f40c2c18001401c03004034010902d151502a103490034035030340f81c1981c014980c040229582c0030500400480500d4219555032030712001e9404564040d04900000c200420038208680020b8040040541254071186c14500200c4000352096800f007468101c4a66481d403021035006064040d20325612083e00c081a19186801d10041920400780039404000071959400c0c0001d200544c029074689469003007011803800d00b44800d80c4a1486289000c036210002a0400c008400c5c101040b03400143e669600310050b000307800f000142e203500c284040e582004012828400c07038000c0040701e08940e40300c0c080141c1502154130f41e018403c420792042c1d0008000e00d4203d603003141d0040c0302c2d20507203220340b05c09544200c2d40101520000c82c9561201c00700100741c02e00b44190844074400300c1d02440751042e940c42e10f0300a407155010140c001003420b04626032504081044034642c44040004655960381e0f140002c02c960455240c2a4a540c101010114607040000d08 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 91352051 1250 91350801 91350811
    0xd031808070b0f0f040504021902010c0801320a080318180402101e080412080403120f0e0a060917040302130905010b0901031511040806010306110c1603020a0806 71
    0xb41840c254510341c101e0300302d80254481e0040c00c00100030124031901c170760015150840e4201c41c0d00c1c6040f040c0c83d201030700350356201e8294402c100610004201c00d110381380740168482c400428451021400304c540001520b00903e200350000c3c41e0440000e03c1100000003000e0003946911007110b407910480420084031148000341e070010003d00c001c43d02500d0180c0c1c540b40004402d0034404c04000e0b0403143c141e40050790030760580214410070100400c0c800b02c40410f0401d140c80d85006a1a03252554025040c02c032090920310000e80c0c0c4e0383c00741c0c1486e2140d6004200c00c0340c11000300c0381e08141c24500440505141e1004894011840684d50b0700a401e040907141546d50003001010b250004004140050030040019901d40d0740b5040580c09580b01c04003131a010394011007000d48000c02181252040da03c4160845c0c048a004010070040e46501007291410b4a40c02400803c54070303144c6c581e40d103003401459401c14840c000d401c0303803112403000180403408607407082d40e13806400c50362030f0011a19003404035070b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 91353301 1250 91352051 91352069
    0x1030206070b090307210f020102190807120608030a020f0a030503060f040b040f061509030b04021203070c090e10090b18011b030f0605030d140d0b0d03180807 70
    0x4110006010b420025802141032084900380300480c0c0350711100554025051042c0415001c02070b0300d95920071260610410f1a000952821040d0041e5402e801c105c60040c8081103501008180f0b0342d8030031542c0c40c034002843c1c5030078400e00e0384908090351203030301030700c0900054803501d403c1507400b43d00072801080e00703501510340d141165a0101840f40000c102022194084e640c0c1207000c150359211322803160402400000014118101349111007100d00e03448403502031002d0010300b0800104c0b4241c00701d5020780d05542603480124101401459402400d0000380402e19000b40850341c07030324513449500e00c031700920704035980080c900f0205012030b01811405012000c400c1300060000c4c03150311010040041480c00022801d980300000108484c49a020000094441c03810041c0300000d80200c44c0500ba04801624282c0e8070610040d10000e501c5008150321200803890012290701d41d48102c1c07182d00040d05500103000607140c01401e0000180341c2a42c0960b0031000400c46090010b00d0000b80d601d01d038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 91354551 1250 91353301 91353307
    0x1020a1205070e01090b0c07170c04050109020c0c040207060b060a0f0206070309110405071103040609030204110415110c090708071206050108071101020c150402030708030a02120918010305061b0301030206 90
    0x191b4044c2c256015101903082445448070000e03406260013a440019040040039041c1c1000b1107003000192001a40143ca640e4014080c2506040000c02c115402c07400c01c6400590310302441c64054013400c030005060364000700109200c105690005404400707280e0507400d5401d0756446801c00c0d000c8400c3e006001d4aa8240e030b950a510504003580231940018a905040c4a1211056600740c0755034029004000011a000030400450038103000e585400308800000904043c01d10074007070184501d198044080101200c46a807940d0424088000340103409440481503141c4118040c2001784152a00400690402240307d0a24114401c040030386005a4446401d500e0303a08003152404411070070012103560800c200700805008100c2a54140d00038001045107107001c0c0105410400e00d03521400c00e54004214107545640d005c507403500208a158110750f200d28102010502c00d02560021a6a060561001006020b000103d071840759440a241d0015280c090001d4907040c007003888029041031045c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 91355801 1250 91354551 91354559
    0x50703081803061e3106060501020f01020f12071806050414030118080d020c060f0403030b060403081606020702040c0804050105070207050a030f0302010b03030f0d060506271201020a1205070e0109 86
    0x78240d00c8250010b070140780c49000c200c5d80d6030101c51200b5074041384c0e140d0387c44a0030400b40d60180510180a165a030003103090201c105030491071442400c442070b4105142e5800038680ca801003070030a803410480d80088030340c9a02c404020301141e106000310550f06804c0c1f084d0070101c1ca4140560743c0103054030316115254240641da501c00d20340100d0140220540c00340201485039400f0001e0520502102e500c0c2000d82c105424068100c408401585000c1ca004100c14000b00d41050b04a405034101c2c441031000755001810980024024250025881400d007109207640c00c0d8006241c0303025a0180000304680e8550103000d07a070341c59491086a41180d01c0b810308002140c2602114010640030780000324030790080c4e030002070445e401180700c00c14814010503404e04400300c038170418001d00b8040c1c50140c94500c4000c01c940a00003056030040c2244120800001e40707440d50761407400c1c004d08450080d51145241d540c0038080c114002c8031005900c0c9042c00043c4024480e5816803292841a16a004041c5c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 91357051 1250 91355801 91355821
    0x1080a060b1603050c1009020f010206010f0e0a090803090c0a05030309010f0e0406090c211103060d050a05010c030204180204030305070201081003080307050c061f12050703081803061e 81
    0x1c80d0081d01031003130034854101c1c170780d006100b050500f5001031000188000144101b1000c0c8525420b40b5045601070401130040f0000341602c0c0d015600000d01c41d03640c90740c403001e500e000350840d400003c125020100a0203255040000c81a0301000100e500744e03c0c0503150420305940707001d03224980d80040e04124544403410b0107602d40070b41c0c076a40030f440407604c151500100c00568000c2c543c90400941ca42c441d1151070300c6050464072142904000a018400030201580c03858000a00280d00c901f0012455200700030042055248a50b40b0100a1064003a8000090000d401c144610300c0c15082c00c4800303070912043d51084509403a4103848050a00c1d109030011034200b5030060038010031a81080c0c010021680301d001651203004695902907850000c600c5481c1000707000707480b40c400304040c1100060040034940000d026120000b5031a42c00384a507007852403034034646500c041c0502c80c0c00503070000111840200001001001e5084481544508480310380c20ba0705000b0540340c3c1c480d004045020020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 91358301 1250 91357051 91357087
    0x1e1d010e07140d09110402211e040305090103140a0506011403090304030f0503070f060c03060e06030a140102090901080307020307050319060903030e0f0106090513020603040602031b0f030601080a060b 88
    0x5c003602202051840314401704080b644404426a140c2520035614941d0101039854960f0225481201021076505016400204c100240c0000c0502ca004500d82109910030b42c00380745000b03580040c480c050700b000d0304a070300103000940790280013072210511100e40001d004201c1307004040c118020361829203951544e41c02403111141c2117800e800108044030210350150409005140602c20002d00795844100160880d00c00e984544d000300080005c102c059035022031507586403030301320100c0002510f811854600a102d1100c5540e03018181c540040b50a000c008040e0078264400e4003181c0100c0d44840405a443c4141d00f0040d0400700848540400140a5080026028440e09010a207200510b01d00c60401c0110003520049a655200401040111b03000b00d54200035140403d84c48a00b440c2c000c0742040c0700c001c0000d0401600000030401c040c600b05203401006822402c1d90382c41e021590034046590b841070303c402d4001130240c0081002c101c0c01d07105240c119401c00e1030076441c001284180030341440c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 91359551 1250 91358301 91358303
    0x212030609060a050307030303050a1b02100b0109050d03021e03190302070812250906050d05090c030703080415030203060f0f01020717010e011b091e1d010e07140d09 73
    0xd0b00f942e400501074408118a0014610a440201d11032510302d00080803201002c3e41d0031046460844c50b9854541c0106000360003011172000882c4400c81c0100607036010001e54040d0781c200003d01c00503418150301040420802262841d1400515101c0c04095600c0c0958056004031503241044181da05000c0e030f000b40384131803003002c540303061001881280d9104d031421107120380c045510303403000c000d49450104041c90405050030405111800c0480c02043e90190201c0713800c856039a240030411040040001880c64580103040b180001e4592070460340940203403080132150610072000300f2071140240252031140034080c006041444034a13041160240c62015800d0550040500100d08404000e03224541e14400b9800821700283d01260350b8211740c1540c0000b403d4007048c8603514102d6500c104480120fa4501518407613a0808024801d980100c1d5440b0110f402c091030503840d600031210000d641204c06031240700445656141050303030f100c8000942c404540c002040a031660b8045644960303456 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 91360801 1250 91359551 91359559
    0xe09040c08030406050a020c010f0504060e2101020c060f0c09010c150603060c14070f02060a09081605180f01090507030603050102040807030b07090308030402240d05090d021203060906 81
    0x2041c1ea460403941168000e400c0280084c030000b8519800da0303010040d40c2c14508003860840703021150100300401c03600990180600300003032800c00700d455603941e02041030300d00540d4070400015445009814000c0d400070032603050900030003000456400c21368200714460140c4960b40340ca044d4040c0011145020001c40843e5800e4080340700c1d600e04401842100c0c00303103100712400100c0d5103010202400e100920303c8840403c101c100502d00000380201942c0004690544019031a5100e40c903082c1c0d911129a04580d15510425182c5082082c0006001c8100d400030345191081c2c2d5405401082c200c003085850310b9004d21b9800c010407004007194040e55001c1018038000880c181c0b2a6a076600f03aa210360300501182c0e05c200b000380300348145810f065821924504203101c2c124078503070700c400190100a002920401d00340403000c139011009030350076001c004000c071110b80d15066040200001e10301614009220306c07407007070b000c1d041c1400003038012110100702480b07504556400082000c1c08234020501900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 91362051 1250 91360801 91360823
    0x3150a05041e030c03110712060b0604050306070302130b09011d01030608070f0f0b16030e010c0213020a02100b010c02040e190c08061e010501050d0e0d0203070b0609070e0904 77
    0x6402d40300303806003524402e507140038166441e0b0600400e00341308010b0202d2541c0100c0d004100420a650010a80903800a8040b92450103900050518043d552210341c05010f1001041003080d03241d8001c03c001682110301d1421a502c80c0b4007030005024441a4501169941c80786c1c0300010003120a039030003000b0514011a030562944855030905680303500203040450b002d0820f0041804006847c07001c1c0010860450500030465004020616959005400e101c40f205903c4101e911505c40c03440d2041e009441c80284d035a51040c1440203502c400712140046c0265a00d0b00303030885841c003481c0780300a0165100f4601315840c1c5c082000401e08840ca1182070710a800001c0591580814811030041c090a52825450319040c0030781d00304034000b40344c1e850390b5074400d026801104491807020f0540b282031078900e0311070400c02034080c02483d50003e0040300380301da1494298a80d50000040c03050741e201d04104e80242d00c5000c203200a441c000e03114000450f500b401c03610300c5800c018006580c02401410300c491 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 91363301 1250 91362051 91362083
    0x5060a080604090507090f0e060405120304051009080c0d0905010909110405040f0518030c0d08070e120714060304020303030c0a1b05330604020c0c041b03060503150a0504 75
    0x840c000c5158411b00410f91a8030100e2080081480f600042c0c00c0482e007e40040e1030300d42d42d5161201222140c000340f031400400410240141086401840c1c822400c0c10009400c80d0706082e442a04003686050070fa200707181e101d442c041d10950a0f0012a041a114140003500b040c2c0e0800281075004044800390200b2705c03000960b9a02c2c5e000c2e402561841e41c44c0022182004101500c1e03070003040714803140c981d000700030304500b544c000203010603c1071051408620715110700008a03052000300d0382c8031788d1044c064031540300b4040b000b00d024070890350407201c2144081000c405105c41c60000315006580364206000041c0c0394010000200100101c0746011506000d0032845a81011413034081500d0b2503000c581020080195419450f100823a4100c0d131090340c2040c459200c80d00c4500a00c02070086802160f8540034070000c11040000400080051140880100800329604802c81400c07000a090030800a01414041882c2100b42d040f0a2000c0749942c40344070700780c050300019008503203141742510508 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 91364551 1250 91363301 91363303
    0x50c070e100b0c0705120a081b0106080304030305030f180a0308010f05030106030302100c02150a05060108070509061b0c10020c0301060f23060d06060806010807031b21060b040305011505060a0806040905 89
    0x21113841c400c2782d40200305109103960300342154602d40181c4042e034402c10052011a030004145c3c0d9010050300d03d03030070450707803884454180038460500d1a10340e0702c511050f400c20560081046070603a0649021810300c1941c1d4010182a2104c6220207009a003206507040f01b02403c0e50080d9402c80054011102010b01171916540e44d00b40403074510f112590b4407010300c034440d81c0c015051a04506a0701e0620308000f40000010414403610141c10b440c140f49001421040c8030511009005210082050500030414840a0b441d030740c9004145109510b0910041542503440d9141c400355511042d03941d5500d00400740742940c205046100315803100c03084c060f420707444807103015100290408e50b40345101400e1040002d08050000b410a0f0700789824502200515645141c80d1038003480749143c242d0380031186c15400490018042d51020301c6904140000c280300d4401c9008208032482240200038a0180c0b95020b1200c0c001d600500368400313000c0210700c0600d8454002c031034014500400008190724180d07211 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 91365801 1250 91364551 91364557
    0x61e090a0602030409060b04061e0201060506030c1206030303040c0303120b0604030303140f160c060905031306110a050c0108040615060e0103060902030105100c03050c070e100b0c0705120a08 84
    0x7034001684000340c240319013032407809a0720041411251ba1400d003400c002014044102d038440ea940103000300741940e00580c0c400d4001400410000d40815940e0802803c1c0259035400144d10618184240380807503c10300b400801c40303200380d8200f8000e1030800c0c103603a81103c1000c0310752086012075031a1101401256251001440110b109440001d0100c100d41022080504014406220030400303504000301403000403003210280745036140070a0f00d03444a00e0044018503141d0310103802032101080d0120200660b00d020000d454140c1c03a00645808044001c50341c41c84443d9009055800003104420b40e07501a4484540007881111f01050030a9903000d0211010610703400440004c000b10607072580f81d40c05100b60005010031220a41c610360400c00400c0320040394a410004106850302c0c2502818032a000782c481808101058951055960541c5450002d060707a640340c200d0840d40000500d105050116201101c000000d00741c240d103020104a10008480c0000007140507078150034001a0701a002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 91366907 1106 91365801 91365809
    0x20a06020306031e060106110d17060109050d060f050a020901051905040806010e04060b01080603060f191508010b0a05010804080c0718050f0702010605061e090a 71
    0x1080c0341c100e051900d00b0069080307090b80d1415138804a0814102ca91a075038540300c41c8041c049054607030900706100c002291074030707010764018076031400990341c4000705041504ea40c40d92400424122007403100200e651350785e6107100b100e04400d2071084e01d07080700c4004e8046051005c818000b8006104100e84030040740340c00f0340c81c080395a110300100c1c0c0c0075108aa040d80c460b542d41d000701d03404460041c4d400b214098102450807840354801c84034107104541c000d00a00d02602c0360a02a0310301500a4048100c803007201d000b800108070769018103803070902a107007404002840d0a5100e42120b880c800e0603031054142000c200040c1c6c0e03100d444260016008242c0304d43d03800c01503044038580310869105403940c0c41d405249407441c14075903200c5881105100c103811210f5031208000c03400c90b14607000b85980400144040702001c0000a40068074003550300300540351400b94400299891841c1d40 = true := by decide +kernel

theorem cover : BRFrame.Cov 91187051 91366907 := by
  have h0 := BRFrame.cov_init 91187051
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 91187051 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 91187051 ≤ n) (h2 : n < 91366907) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
