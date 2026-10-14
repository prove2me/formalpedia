-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1508
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:18:38.768087+00:00
-- url     : https://prove2.me/submissions/95715cf6-e28e-44f8-88ba-4d7c97d2a649

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 271043165 ≤ n < 271223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 271044415 1250 271043165 271043177
    0x90212011215020310090609060506030601181a030402012007140307030804060906020d0503061014070f0318050102011e0504140708013323060c070303030b060703 72
    0x40040301d440201c4014000c0c0440440940440c4181c41030f80d0080312140560300b8150801c10603914039100b5a0000c10a81108001450400c000a80a4400500bc0d903040003902c403031246411901070084401416206075061200308041c21403c042d41040701c0503800305403104c41000072003880810340703080d40000c0800303030100e9030030400704a8082000c10801030f0144159200880003540a10090028085e940c03100080715140c90b01c02031404800c401003004014051041c4505074903603102c608152000e50500313504004000014440743c1c022080e014045d184c0c4000b0007070925400c003108510900c5001034201529032210010781c01e0f241c0e074903000c0421800d58641007100d03801c01c2d03000a070800e01c139501032507002c000b001c8507610f04a500c3c0c0103403405035580c0c4000a81c00c001a000303100c2c0b16100192980850303040d801080442d64161181003402c8800a0440881e0304511218203401078000b072110351101401e110a0fa51007041c1d000450100c4d1400f220f4240a03d02441a0340e00203034965108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 271045665 1250 271044415 271044419
    0x1509030d080c0f181906050a0509040f09030c11190302060c070e09160f050607110102120d0506090c03040807110406050907020d090506030c070209040c0f170709021201 74
    0x46a80080040c0101c500000601690f28030012903c01403800680903149140b400009208010603c81444110b40b00044261030420000f900102618000c0c01c150070050740780c000b10b902060103010030020306100213241082d43d2080503000480d00b41d05600031041c607640b205000040c040740b550303040f03c41c5140d850300c02c1d801c00043c0782c03d200034102400c1c5c800c145c2c0cac1e4496490708d402524203000e90b10140320b03400070700d41c80039601c0d19142c07020010f00e228803c0307640c45449c000c041042c5206894001c0e16001003004107580e603074006c101d8040b46c0041d0b208440d0703440d6442c0200b41e0040000f500c0302c6100349070b0100822180b01c290000d0b070b80103039000700701c545c64500960765034034440c2113030504190815140c1100003520744d00d40d20814032a01507034000d09400c66083e100145498596000944110b10501c00d014841d468042914410f903410790b030b110042d0302c1da130a00c0521200b259101c9c000d1048400b03030205e800040c40c02101e1220003c101121b6000c0e494042c1034090f802088042900d112201e001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 271046915 1250 271045665 271045667
    0x40b07060204030f050a150c140304140601060e01090f0f1e08060109020a08070207080d03020f0d050c0705061303081b1b010c09050102060405070303181502010b1509030d 75
    0x40640510900005140564a9a50018038100158142c0b603540100300880103000c87c030184803c07107020800b02003001c8000514050408149264125440304012000508101d0408506d2a90401030022031f4203640e50b4110080a1082e00c505103400501803a10000700341a0a410407030540f594046442e20341c03820a07510316800604241c0b6262036071400c0a00103210102404010f000e804c0914004d80e80b0304100c0000b624844000d0042d07011580a2203041100c5003020401079201c8542d882e001d6983e0701c041400d003c45014460000229515000c18028892034400040100302d2040042c2e40c480d9440300d80020310f540e000000540428218000111130b034500110300c83c030b03500104407828105071100501401b1650b0f501c2201020b03a5503244400c8040313800440d050f008000910041185152540e101034071506644070040a1008045c010f91240c8a241c00c0303c4050034185007a03803006482c2c003000902a00007c410300e40120808500748588400b01c10858240c814083c1c000c040780c2d018100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 271048165 1250 271046915 271046917
    0x2150412140c03220b0c03030402011719050a020c1b15030f16050409021206040f1e0e071a030403030b0406051c0309050607060e060a0504020901090b13020f130605040b040b 76
    0xc803501c04c00888200102d0214004400b4180003140341c0700441e181d1500b8400940f12041d08420005003184170010480144140543c9007500448100701090580396030380c1c0400680142d0091014a0084808008034290700d440007142c4803908175416840f1880e0180c034040c0522065480960b6922400b00080c00c0f03920131a030501854000746041e49c5080ea9650000080f40c01080807842500f80d0b44c5c060011130301d0070b40104c6510341c6100c13004100040d029041c1ea034109036515800ba80c0345840c0c0c03140200403c014010140108801c0160001c10012840c2c0c080b0182c1c070460f0201d02103850200742c809142418800c0754141c0305c0151801101582c2615100481840e801c801c40800140850209050b10303003102a18106110f05004a54616883c40c1a8100003000b040b2841d42d910f08405c000140e5201c4212504580ba0134400003009401d28000c60300c00400c1c507000101c05400080c02445090b501001840301d642c21060861b8241d8a40004032a00d2040d403160301180c19042c802480b444113070b00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 271049415 1250 271048165 271048207
    0xc030f050d110714030301080304030209100504060303020f0115050112021b030a020a1e03090b070c0803030f1f05011416050a050303070f09050a0605070302150412140c03 75
    0x82002800c150180c40d580703040c0e90522402d01c800c02000700d040003c01c0707407100c14400302c500404003131801c66041c021050f41d07900544c40040d2140c83c4910106a4004d0021101c0c1c0140201610134440d107030b203034203000c1d40c0c40e200c00211054942c0f030a0701b0740000021441500060b10016900c0e201499041c0041d80c01a40000380b441100364020b40c0110a220340820080c000c44600e0740181c090600d450800900001c071010560342a05a600882c10010758441702210a41d40300c498030540707a401c0c44c01d01c2c2000e0b66054102600a12000040c171420140004034076204204200c080c90422a800030b80303a50701180c9210b1203001c070744591a4295281600c41c0500b1005440d0100d03454075140c07a0b200c45162140e519070030382e00e81c0c1000082c801c0c036580c419a40c00c07011005042c1100410b1034980410b030a06968400c48040000219001c81014403c0c002c0ca03070403210501d000309a41c00c1c0f030304240020480fa80c4841003c074841d0010b40c100b80c030181041c0c5003030901d80406141001d480c10382c41904c02e0103503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 271050665 1250 271049415 271049417
    0x40f050d050327192d08060406090c120210030b0d020303040b0403050105010e01140d0314121618151b14061003110d030306170a0b07030c0c030f 64
    0x10b203c2c840c0e8019888884440c0c1403070460000b0300c240c0140c001d104031500c0403c40c0240551040006001c90940044000d4030301c01c042c2104400c6241031606003010002a410102e0180149010f20081c84100e410039041c9501412090a19980d0345210155074040080d00035000100701c00c0406440c5c0c004c0d4041c40e0000c034054109103004081e5400241150f02c02d0308018040791000c1014000d1000902c6924054800d5041000442d410000c42c00400c400d46030005100b600c52245c0c0300105445090140e0640c11b4071400c113525505051301c8500070600455440c07140c90b2051500484243c03246084a91580350584102125810040c02c40b5451511f048100180203d014052030203c01c040802458a4090f50005800c11110902541080d501402e1601d62840e013500a00108804140005889808441c00c00b924400c40c0f80036030140060390300c1904012004101481c042c1d2011641c440164810403441c2495513951000741c1c00c03030300c8185400380043d030300f2640030b80064040c4071010429212 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 271051915 1250 271050665 271050667
    0x1201060e011d221503050f060105101704060f05151f050d0203090f030309060a18031d0a08100609110315010f050d0f060608070f0e01030f060b030a060302090c040f050d0503 76
    0x40c030a131046101850781c0201c449a00450030300c003401e003040c00010b004d0729088861400e440041c1c05e00170542816030940d46200c640b2035001c641040600c0c0d100c2c1440c1c01d6141d0043c0003038070745806081074040e800d04d2801d0280d2207075001001e0707940c00c0c100b0000e059a9140c8405040560b42c00c9060000c0d0401014800544954503248a4005080018502c030f450408000c20861511300f0022040d00c01c1c6801c9040c281d0300d000050300009403c141d4800100c40d00b03040c00b403c0300100500088031032849501c95541c60041d1040340421071031641201090f030307441c1441030000700349042e45040c1900c0100d80001f003c2314510140011903100d508410300070b88440c6081c50600c8540a5990201c45504180b0048070383c0d0307400200000c54000440613801000e508007002e0b50440500040c00d0132030340c030783c01034101681d917110078403841b00c4d42e4800701c05049002251501d902d42429100001c10840c08260b12544d13240c3c2c0060750071042c2104980540b0403410350421003619017030500c040c4141810301240c403404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 271053165 1250 271051915 271051931
    0x9060c03010b070212120903100204080c041802120706021b0a09091703010f0f150c030e010c201908030906130306020307080a1805060c0c031201060e011d22 69
    0x401b00089183e0340280407401d540c503210303030782054940000500c420f0607050050000300024100402e41d044982c90070b54012074103085941a003507100c408001c0082d0b0082800483d28840ca0000cc1c0e0141500c0c11a000c45a80810b0b00048040041114400c0c41c1d0003400c030072041c041d40d1159044040b07114401c4000c4e07641c1c0b5126907040c41681d0000d810228804055000400008801c80c2c2c1447c0240460720034864914840070f002458642e00843c040c041c0014010901c0c120f0b4810200c03480070f1a00000540c40e2202e0021003405c2440644551f10322a0b903d030402520340c0b9240140c0107085400680003586444408003e116145e000700409041c10050a280000820250300082d807090403640d0b43d0140c80c0c40c2601100080318a842114041820700d0060030001030300000f100794120341011106600c035031030840e0503841c5220700c4217000566002c501c00080d444ea00103400890502090300c5080c100c2c1642da90f0f00b14440c580c2c4035501d62001c20241d14104a50403c0c40d41c8003403002c14140420801 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 271054415 1250 271053165 271053199
    0x1d1f020c060a0c0312090f0b0c2205030606010e03030a080c092e050c07120602090a0303080435030601021005011e0f0e070f17040309090509060c03010b0702 69
    0x2070050008035010601101d540000c045d03012040340d04200090300c1c1001782014946800e4448000010018404503040001c10702c0024204140d800400e60042031000382d079404c07426600d16003064420980244241808a407096004010822098001500a505005101c034044540c3d100c00b44c500e840341603082200407801d0b116180d08076000b908810b40151040d510100241125010307c1d0309004105090103000c10b03400c40800c0c0401241ca580a40900021440c10410000e101d100210380d403081d07100200008058012213032520550140014400c492a13000c0b441c01060039243d40590702e03845590058081c2050034000c1d60700000f040c41159545007000d408282110000c1e00000300180261400d01461030701c1c02106000b130020016580d29880c9072161030130001c840a00490f051010810003140d189218089056030380050300d0390850581802d050260442000c0e0050502c02800c00e000a48417200006885000d0306051000070b2841c0e10f09820961150052001260300c454811403000d208 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 271055665 1250 271054415 271054417
    0x20915090a020c0d0c031d21240403090302040c1e03050108010c030b131e020f070b0a0c141c02030f0114030f03251509031d1f020c06 59
    0x25440368100580d10a01c0c0050740c0c2c60505494491401c00607216500c000080e408404507c98581d070000e01c40451820000289284048a109041809610070704071003000300010000d6004130700d1010484145405a880c0c0c07101042120040c0115010f0f520030001410280d0186072200001d18010003003000c0390305030000c8101c405940310006038880c801801071110a20400c0303541e45190900f0010340c800302c0c0100c1c504070f0318804002003080d51040c0003004440f13031912030140e18407509011941c0d0041d0100782100d5801c020019509d80781c1550000d116032155100390300000e029511083c001d20031012001646901181050b100c0c03020800f070040800c90a8000345014072800701c4901459810081e030790081074070302071013144a1f62000c600c0b1000544e011049402a4014600c0812061f40c492000c00100d045048010110384000d00c032010440000d50004450131311a560b1b20041002c80782c180c854002020814a9001c1301150360140321090207994402921807600503205080c00c040700045203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 271056915 1250 271055665 271055671
    0xf030b0a0f090c0806060d03120b0102070515070302011d060a050601020f101e05010b2502060c0604060b060903031c06030b04082206121d01020d062c0402091509 71
    0x20030f0155079030600402d0310a01c010f50788100d00340d9114003074140c181c40c018200ca03030705180046100e0396010302d105140d03c01d00c40c5002422018108030b8488400d8042401c0e50750080c8402e030015468240100c0844140700241c1c1d00c0009003200401a54580f41c3c402d41c010b041c060081415441140503c10b03207004c0601618103d039101000000359048089001d4021840c500041a400c6240c0001404040c69103c01c1d12003006202020280f458030000048170110108070019500c80c0d80403d84440010001560a02c19480b88106010a0601c2400c0c00788034081c01b0b038016819041031203503610310701e10341040300d001c03107180350020609a82c0c940b0340325401c2109440690f0344210010f0f0b0390791540d5812002038130082c45c403014281c8440c0341803401403203069402c1200c000103031980300300000303082e000055024012000c4000c540c0c6291040f05100100094403545018502100100000d030007409030754088940541d186c52600d5446a08003d842200201010040b40442e090419552115000a1701c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 271058165 1250 271056915 271056923
    0x8060711010b1e04060512070f0803030907030f0f020d153e04120c05012d2607200a0803040809180112030801150e0105030c0f0c011b090f030b0a0f09 66
    0x901c0340c09c010381400341d10200c3e046041c00303610410034056207640002d00c07081102d4100e1441d4030782d15141d00d0700c2001c04142001c0070390b021b1540011601808011990040c092108400c00c100c0c0c0090b4089000c0341c40d0701d000100c1d41d020599020b154a031444912b400324803007442c011942c9040e4985801c0621940820b5003640c030340322075040034012941c0148501f082644824522500c240072010305c0c0000b01c3c080b00b513001c20001d65080c02c0e03020713407031600044588981015292200d0f10f0204001020b81c84076010742c0c10f0180341c2d41203508410700c0100b2003811540d006181c00d8915a21611030740303005d41c0500c24581e00450340404d8946501b5000a00c14041c0071040950152503000c1d080052001d1010f070088401480008400b9010300e0700005090a10714003030138107913103a40d6445c50580e900d0058045200e50010000b5a501410006501c01c1062510307250701503041e15103044007115401d0044c05800000a4800e000b80042010712900c0c9070311220495003ca5401104540e0500795100e60000321 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 271059415 1250 271058165 271058173
    0x40f141609090506010b0408070b092e260c0304020a1a090429040f020c070b09043c02040f060c020906061903020309070302030708060711010b1e04060512 68
    0x4004003800b0f02c40c010080760031b142e030034103082001c40c41d22030b174030740c0324043e56280d000500b01010380320f40709505490300307001c2c07031521000c03003610354504683d2a078041030303000a061200039083c02080da450070701c49201c13401d040d40515554415143d00c968000340040e81e12407103120000800344072480c5010b0348e03481883c2e4599152403001050105a9422a9140d00d405c0c07103141e00c01103160240080440d650808680219400c800b5484288c02071140303c503018105d0050b8400458211444401000982d4003034030200300d00d02d404041d902c2d070245001051004d40100c460050520598011540c1c0484c413550350061400b6a203107080d16408689901c03089c0821200c40f491415031400c6000786034482015608289032240c21100355036050486c80c0b452051650200c007040c2d411408001c410302455000d0101d9103120748690701180d40d170004999200006900d44034035144000103002d59001400302400300300c00c031030f142c1501c804030f80091958203411940e554400100c50355074108044201c4e000c60090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 271060665 1250 271059415 271059431
    0xc0e070f0908150a02030604090b011401140306010807050c0106091b020d1e1b05150f07110709050a0b04091b05010201021e0c030708071101090806040f141609 70
    0xd400070407650300c109481e42114020751001c8181c81e04840e4030003030701000166655074400005008019440f40a008400c403140007007019010407003510180d240c240c071100ea4072070f8212244a850b100031a009400221200023145050740510058840c00380088004581c0c02d80b140c5004040b40c0980f10913024076105114000442901400258074a440d03e2400c10700c3d010059007914200da9a41105808201000120302c0090810b01030001400d51f000088d076484c45e0030f921002c806000e003a1031f00d950b040c2d1000c010030710b010b00503000c100003400104040d007481840c01d289400101070040802d1340c51900c5454215aa07540c41c81000f26040c4203030000090540c40d0710725200d41d18002c1d001241075a20401c0b200300f01c1d08489800040041d0110b201658505540c881c56043d0302882d28000c0407050081110700400038440859501450280d179248400d696070405280d4035103042c2c40140540044c41c00360000300710030310900310007124020102c0d0403000c00b0300131301e40c00a4684d5014059050f074070354236 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 271061915 1250 271060665 271060667
    0x50f031614010e060106050f0c030c0601170613060f020c1c110118020402070203030715230f1614040906090f0207050d050a0315140f041e090c0e070f 66
    0x10074208001c1207002041040c02c4103428580d00c0b5411300500703041c03001c0411203030b40301c4580b80c3c119400046c20390141ca440795001424a581d4100c00e01900a040364032400d8407500c2400040c42501c0380c24031488003140d400313039925018000e00d0f504443c906070300d40804c00c004603c00108051600c200d0711400c501200200400e005181c00405c42c003c1c1d00503418003119240111642100c40d00f0355404460042e500c4c2e00f00d100284c90f511a01c50300034414150702c41c003000100301c16801200290500c0c5501210340d002200e0207400064110b8108006592000c0460580d6904c2c4800060100517400c1901d410500352502d1744a03a0040e5002c00a51900d030720041c000c039203160058120400126106508240d80f941c0c0c0c080d282e0780404000001c110b400724040004500c81e4112a1403103c50b403e0120205840d1038085c050501c0c80038059008203a0030100c000d040c1898400e0340a082240721441211540000380031000d002c1c2042d0548080500100201d40103c505a0145c015110f54454180c62030302080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 271063165 1250 271061915 271061933
    0xf030103030c030e031603030e040905010e07180b0a0e0613020c0c0a080a020f0d110406060c0201030b3102190804021c0305030703020d091b050a170a0f050f0316 71
    0x41c000c0c0170380c108950384a03d0142c0c0c003038800243c03645400d00181049801000c00d005100144001c0c00365030811070749455150021a00030196103204022602c042c41c841c07105030a0310081442250070030380c0179800f00080704014445d0740d0040802001c00040f1006006443c4c01d0703800c01d103502c0e4282e4010011600041c5411032a030001880400302818003044c654001603008400e070a00140500384015118003000396195500307807124002082046101e40343d80c4020905a45008101d0210f4034280d071544003450303c00448200700d46280c20505c1122001d14841c60018044482404455020301a0500a0412500c2554004120f644071041c0b0b00d868010000c00d0f008040d4030103512603032806008003080d441012039034410301c1030a0140e82d55017070f03010780c200400c800c9001402c101841960864034696078407a50040b40c070100c4410a03681c2e00da602c0b003e194101d810004005078403009134400024802d070310f00c81d8044c0c00307070060701e0b905008112118115802108109a40c02481c03448a0030820100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 271064415 1250 271063165 271063187
    0x16050a0801050c090120010507090608010b130302060913020f0903070509010e0c250b0f060604061b03180f060212070201021011040b130503010f0c0c060b060f030103030c03 76
    0x800a102c0740c10250241c00d02e52207581c5515041018803d810440003c805281d9410b09403910000c220510b4070540c0149055024011080002d070103400000306010a442961191001059030b010135034035541c200496079002c03506164000000040d901480301d42440076010182d02401550303030b2060004100760816403207803c500d10403923000f0014081c1d02c0c412120641e00104c001242c41da507600c000440d20030b0b0000c0f60010810140702d40d40500030400d0555206006049a10035003005848140422829000300c5c0035150014080e107003400114081c502140e4400340c024208244034072000390b00c007c000f0060340c0290140c50310441c01041425030400429543d406819100c0b420310340c0942c0000e490310000396201580c03603140c41c18980d41c40d50707103c11a070040030000401c03650b844100c81184070b484144d105480c0700c1e52070002e022001308018080d00200d0103150380e61540d0840d0b84e0343c1d03480003007011400c2d072070300104140200002d0040410055002e10700070f448034005510207150062a070071101e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 271065665 1250 271064415 271064429
    0x180f030c0c0406121a130602040909110406120f17040803040f05150315010e12010605090f060a1a0d0204180f1b03020702031906050f0f040302030a2016050a 69
    0xd0101000c02e10b4110405451841700f41c0000c42919900420541d0818154000d1704040c4000303000200400aa440031800038030841420000715a404104002c4a69500c2036084a502c007440050000310324107000c0000511980f6040c59145020340c00c0443c1c1c6c0c00540000e500c540c00098144030307107c44051050300600c0c00b203401c9c14803510a209006201c0c0000b40a00a003e0032923100f40a0b203130301a011800040501509210f20a01d440320058043c00e01e42c031989000d0808900410341810f0741880c194842d050103050314040a02d08008003c410011000c4424960424041c00b4140c26840c00144010100b03412202400c0c0003d11500088444140c0c903920704919110b586a07030803400340710100c00c0c01024100142c45240d01d00129081c0800d1542e81074820740340e850241304100d00c81c3c1c4440e0203070403003441c80d01143c1d1b5030307142050122200303540c0900076a005110500c0480e1042c0c10141c41c03091482c50703031714080000003910741c036010030014176414826180a040c042410a0403090b0000c2800b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 271066915 1250 271065665 271065689
    0x10030f0f0c05121b0405040b1c060501320904020a0f0608150108061e04180507080d020f0712140a03021c0201060308030604050403050c0609060a0b18180f030c0c0406 73
    0x6100384802852061b40701c0c05011b140c580180c62034980d29003012300c061424441000744000034a1134075030000e1800340600700001000c40d5140b140004074450420f68941414042c088040c56441040031841d0000c0040382c0c80f01e65070304c010030140c01c0707902400000c0400b600da0100906200d0300100b0710340c0482c160a410480c00008100499a54206001c21021449220500c0606c080041000380031541c2d030380000901d400110310f0402c2000190341c0100d44c8600291542d1146204080761030364490500c54403648d0100c0c1040c482d48414201d9880002e2044400f042200031201c0d07580d0810440b0380040c0c015030025441781c5180030b200014901580054030007048070a0450ba52200c40e40000b4043c0e43c000c590301d00001d02010300038821151400018000c660f050724210080e156200421682c44030f0140c102101c5ea003c0d400d0060138030041d19840c50800c6400e60314030400c4c038000c04100706450040e12a00d61f2480b107180e01400201f403040c100502404071200d43c5410702058901d07950000c0507001d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 271068165 1250 271066915 271066951
    0x11d01020d080709080d0905130204032003010b040c02010c0f0905010f030e01090c15230d020c0c0a1d010806040b010b1c050a0f051510030f0f0c0512 66
    0x80d012601d15800901c9007001445502c03014801c9414040c9034100070040d106454107a8082600b00c80314000b114000c82d011f040c421840c103c250264061840020000d4624041a8a0503007005d0300006c55014050000158007a06034006025500159074241c050f0f591017117900b10350f550200003021050042c0c1400100e051508000924007070035903002c0410140d417840d0302d240c0d03c01d081d003224031019000800350050f50388a596420b020210403148001040b054450010042d11002e40011055a8600301c0760820b600640c01d000690700000e000c01d4a4092014400075a942d2201c040c0050000880003900c0381d580301000196041e01078000c41d529a0001c420403001070808200d4506490170710704442d446021000000300060049079001b00b1160038501004914080c6500544220202d140103008540751001d8090301c00c80c01d41c04080e040401d2030000010075009401c03a904900340040009180d4007200e02c4a81102e840d100c030240040e10016040040007440000070340c2082c00321800540e200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 271069415 1250 271068165 271068167
    0x80c0108060112090c03020a06050a021006062c041119080c0d0b0d05061603110702010f0305100503060f04030201050903030f010e06041d1c050405010203120a0e0a06050402011d01 79
    0xb0072500c804039810313500d0740c90000030803030010224001180c0c05050081900d880700e0700a480c54200e0690007005106490300440840c0320b40c00303481c04072042c648513610158071282103405110f080008903031418030880900002ca454503c01d031001607541280c0151109441d051850b02134100a10002c01c10070000140201e041211040b140c4050017100000b50901008000c141c0c5d4200790240502203002d100200b0005401c1044024585100e55400300300741d42648440800e20700074254007900050409085003003090180c0c0c8a150404a01d0b42101034184d070f02c1e0006890401c08555500b5901030480900040603024025142c2000d6104042c40c1140381a0040d5940240140f081928203c2c419010918980383c5504c140c04c180c45855130007200c0c3c0d80f002280395441ca40c000c0315003a0410700c4180252030500c0351003902c0984405a02075468114003401d8050844400f4203e10010381d951a82d11440020810100846e144110307000700d96854140009050881c01d030703406540e401a107080f0f0003039503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 271070665 1250 271069415 271069427
    0x30c05090a12111815061c1d0d0c020f01141c14011e090606020d0c060209030f0d12020702010507030c060e12120a06050906060d1410080c01080601 65
    0x30b280c80d100001c06402490401d032207616150012030f0707044100c420403950202c60707010318140308000000f0660390341840c0d40e082c080180b20780b0345003100b01c046440d841c03a2603031200c0d00441a036040820f1458100703008004000d040100c01c085260204003064440001c601b00503a00c0c00189009080401603140c00800501c00751150103010348034500300303004400340300308160b00103105084c45030b541034030540e19034001d41c8800c1000c100c2c07030200607903c030000030f5584081c1c00750a080d115a41d010344507a02485c0b0040d20020b103501c4044400e282c080c003070751032141c90401864501c01c0307040009010420480801070000c410019811010710300400981c030150341c000d01229a5654141340c10305040100b410300700001d0502c040a82190b002d41600b08080b0360f07050010313000c815221901140192904080203003122000c0c824035400200080c0040c10500e0400c0203000706030310004e80803c0740310f007040c140e00035100d017122031100d40c07900b200c428007402e401081130354000c031000c2c20f024440b403c08500190403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 271071915 1250 271070665 271070669
    0xc030c0105040b072406050f030a0327031a010e150618130c08011d091902060f0d0501170606012a05070305011407020a0b0103080a09050916030c05090a 67
    0x1000c080007130143c007042120040001454404007a28001484e07400d01c5002030001446490321802a64555400328500440c114588650549a145c03806800461079801851101c045042401910034000013044240782d5581603c4056031040c0e11540c1440302e044410701001d000e03149c45180d2180010070980340d03003003141c66584a2514250b903c514400016640c2d44201039404540c0703003040542c15010350803004550598461030300d9092180925020540d0003d8200c03400b004036071104107105601c6441c8003240011600107003031117103408291380c1d911f81c00b94400c01d80740d4000b80d9038000400502065900403000c0c54800000341a2908100e80020200c841900c98032a05411440940301c102d04400c10303c800d00766024081e1614165241012402440d80c6410304007041c0554001a031080d1000c908e0300380e4154000b026103166401d41d1504c807010b422000c8414180b040014000ca01c1d5031b184c1405902c40d0103815074604100b200000700800361070303400d02d030f075824801d00b88100d279509d56840600c001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 271073165 1250 271071915 271071929
    0x5030706140c2203120921050c090a02070210020601050112051603050c0d09061d0d1b0201030207240e0f0d0c050a060504080c07060e0d0b0402030a050712050c030c010504 75
    0x507a40000c3c60100401072030b42d8402011840c9281350325210f140c02c840c010080b43c0301d07108112030403214041942c03140805a00000c0980c4c0020000c00881d00d4800c034141d4000010040c0182400740c2d81e07002ca03078450820141e000243e8001c80040000390b0344244500e110a400e00000d0200c2d040c0351031100109003074000000140368a4100003203005076139001f511a8045c4656041c4684209401c00345e00822900d1000b50b080300040d4800403d0002c00a85c00080903015650400400c030511000140d00f00c00d04002c90415808101d24000324176442000a0151214190001c02859103070102003282d03607006000009800c144070039445c0160210b454140c04136581440e800000052401c0c40c14044007000c000c00c207503d01b205100a005040c8080c04150740e000003100c0100b515040191000c01035640aa58000400182080040d020202e03843d0854406030885140d4142c0e6680c541c286034881d0005032411844406c54800c0c4442040303136860021054002d4101e03000e400d00020a0f40c420307401401c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 271074415 1250 271073165 271073197
    0x60a020a09151715030f070303020606090c22080f2b03110c010203040309060305090c012006040302030c0c010c02030303010b0703020f060a0c03320a1805030706140c 73
    0x2911406050754540300100b4601c403028070f240c40c4282c2c10441c413003004828080c0c45005940710000302c0000c0c0c12410380c0d405800030406651030008128440341c0c002d10307410392501d050148060741c2c040000d1100d1982c058070380401c401c0d42041c941d00c0c5011041c4408241c56402108103104c0021710019910302180410700e0324000240c1103000740c001d0701e114a65880c2d00b0000180300b444404065000d076004601c666141c0300e1041d40c3c0c0d0000c40a44405039071001ca01d80114100803070340d600580c1d801e201010058035039800890340844090411500710303000c1d00560030004000c1e0740b0b01c1c014410741c220000c1c03d003031840603038103513801007503403804140500e01501c900080c0e000d050600030018804c501600208990091629625003400351a08444c0180401d04000224081104d0801c581d02c07101ca90414a170f21041024040fa9550740d0301402070000e0550341c0c0300b5285050341c80c1b108808102d004000031079803012503107411802ca50380007400318041c00e00362003480702040900007254600e00b0f025280c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 271075665 1250 271074415 271074449
    0xa0f031e0c020111070c0e0702030a02030a0305061203070507050f0315061216120302060c162303040e01031b030506040b0618011d013501060306060e09060a020a09 72
    0x260f00410708880148820040800e80008022460030740809a03101681301e1100381d2075403071040c0c2e960b0144007018005600180a02e00c0c0c4a4030a078000d03540008010100203100030100d4001e41598445002546c85400c101c909020f1403c20444950b54407030142c000303001c207403004101211030100251540703205021120121080980420994501542c01c2c0032460700036550707070310b80c00480352050403c4015000d28000991030502101c20b0f14400440b0039400581d04d59259034241c60200a520007900c607440d4480c00d000e802504201a101411482c80c0790b1002c3c1d411070501064651a4500c0c0e505803610402051000400114a00760019400000180241c4903040083d656140410909902c442d003040000b802c4540040310403000d150b040c0c401001a42c9410f02e02c4c00c1c00d0302845001000743d0f8855081e0724070b2003075045d0701c00d800043c11000041664a0307542d50303400d03141355520060b0305e022418144418520140007482e0024246c0350110301d800807415024120b620320b485468007040e405102 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 271076915 1250 271075665 271075667
    0x1707060912110f092401050918061f0c1103030c0c010c0c0503010c0e0112050603060c180306100f1e03080d090b0f0a060b0f0414010c05120a0f031e0c 66
    0x9948010303c0050981225140041c141c11182c00c600c00802000d20300c4000091465008008983c00b080014041c03c4401004809002e0015006000c0540241002008400840c0c0c01880020a40752075070f0b80e10100031050604000c001c0200c402684a5001002943d0603540e0000790703001c140d103080c00d201080102d241401c00404605a1000d0f8144d400c00760102e4030994020b030f42401513a000d89a40d00b4840071212100300f00c4200b05d43c81d6801d540010702041014400344080c00d8481210081b4030b490000310804203013410410340f04c9000c1d07407015400c1400710310785402e11f100c0a0454079040d0122641d441010945080080c440507000010000700780385001d403581c000000f00c5070800c1283c095400c2403042c02c03403d440c0c126600c001c12883c00354041401041d071404c0712035580285601d682010b0404c40300401803100402c0042c18440e910ba03203c4001182032081000c5000c410903010348405003200c02400c0b010228100c04205441c0c224248542c043c001804440c0786203203c07000030700201d0004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 271078165 1250 271076915 271076929
    0x4020315040b060705030418060902160201140702030a0b0103140607090911040302092502010b0609190f0905010e0105040c120c021e031c0e0a0f080d0501170706091211 74
    0x1005d400c6000001d40428000c48001002c01c00d0003e4201c204019541c2c0ca03200c5040307001d68640b80c8101c128202c0048003561280c84040e446403100081c80c0d1900380998002031820b9441407045840005030b00c010418445070425055542116801808107458810401800112a0300a400c403a9948030000e4003a42501c400340c401465019200c0c2104e400c003160f10780c0b13650140048103040c91440c40d0312401c5461048c0901002c00c0d002a060310b081c0746003030042042d600c140b1109840b401000b80300c0050044544a8580020044c81c2d00008440d41030501c107004000050300001c1c011824100301100080d44001905881c0c050032038009140580e4200407810501c045900003d0500d5048010724440004802851440c110103410060b06480800c0d0000b55450386081d580d064206242c800d01040c0d2410607503074040e1144006914242d40440981d041318001e811807d104040c440c481d68000d0300030496600070304100c1c241401401e1806880b2421600d03c09802400151158000300320ed4495070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 271079415 1250 271078165 271078177
    0x607020d032f0a0c0803040803180f042406020111040e070e030f100e010b0105040e041106070b07020c01090524130b07021e0901060c0f02030d03150504020315040b06 73
    0x303064182c1516002503229540c0710768150a84007185008000143c01000001b12000c550320040a0760802e079244064030050708030140364036003010701c0150b0500c00307581c0e80c03041c000d400c02480341800603501449144c45401407585c11a17425a03140030001003e4076584030030340b000c4908102074050250303100a400c40d0600c451070450384d01442444c008034440380300482d003440d41e004020000c0000010303031751801c1d09950300c1d00d4055010810801c014400d86032500303030746036005014050980b03402d10b00384007081d01c550007400c0c141d6000000c9024407000c140c0c1442080303207001091a1411b05c0754106000100d00c5a05c210380d420090810b0250000d007002c07080282c03884900c00800c501c2041c9e80d540702840265102c200300301d204044101003041c083d6000d030704051010402402c2c42a1a0b0301b40002901c0799000c5920644507004250f0401c00140e03800c0018a4070074400d40e83c0422000303a0b00444c3ca0019000e0f80116204070f0041c810845203d0408489611030241201c01060450204000c038120b80b09003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 271080665 1250 271079415 271079477
    0x12050a050115081203010f0308090117070302030402150a1205060109180e07050d03020c06030a09080c0a0b010503013b03040914010605120a1a180906060607020d03 72
    0x48140c05401c154070300d14508562050b0150380c03030724030901010000362001f4015600d0780d00e0350201c01c0c00400e02c0c40d0b000d000d03034440604010201c0c24100c50305c4920160202c4a540009400004000460400030300c0d030b0b2640c01e10310901600341010301101500c4030080c4050580300307aa644c000550300368451550900107219042103901c402114802e18005050200086400e611405500055600700a00d80101c91901540508980c10281040044550000d04400b50700c546a070031007400f24001c0c0c4010003080025a001b4454076040745824000c0e900164486407003079140c00c0c007a91150305100704043e0804c00c0c8041001c0301120401d08001d0b2103200c010701011910011070085614030040c0d0044a90b80000340144100341c0e070315841140d0600c2150380c14803850080001081c001d01103601f20024582440800c4101c0e402180c002c2800409028080d100c40c445000a0094440c01846010340000c410344849180050344d4006c01c1d00703e910316000408101982918100440c0090340c01c84956240d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 271081915 1250 271080665 271080671
    0x902030c0a030b0a06080703020d0303050a021c0b01030629030c04030b07020618070510110709022209060f060f020a0503040f03020315071409130203040302071d0c0412050a0501 78
    0x220700f403020424408685140419281000c0840c0700b61001942408580d402001790b400790b030b03155500301d0145c50003500c02060b5030303004e000c0005808511081c3d0180f0a001e201c0001d0700c00c95140004042d40d40079400b900002030b0954a8a1640c0604481c0441c81d2076401880c0d9035949490b4034107400c0d40705541c4003500161058040c40360169003c11824024945a00310100c40c40441c00c0c465141c0789907116166100c6112440792410038050010309a4031a814000d42c7c64a669514410003603030322102d6400c009030809044002a5500d284451014145102040180d1420a90f4405a030702c454000c0c41c0a000240c0c0203480e09510800c000f10006900c03105480d1600d03601e4603c04c5406071940822403090003a5040f108110f401d200040740b0030140d035900c0742101804c007480d1040a078040350b00d09801c80e00050384054150364500096016a200b5802442407a2400044ae0076000e103c1d88480c2d07001c0303120001d110003e4216800d4400352101481c07136500c3d00c0780528106180c4040101e005041c0e500f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 271083165 1250 271081915 271081919
    0x110a0c03090f061e0e100806011e05211317160501090b0606122d0103110906011b02220c0c0b0601020102071e050f0615030c010f020a0201030902030c0a 67
    0x144c841c1400c2005134154080d4210448109000c0e03c8000c04028010340000b0003e900740b45180c0314081441d0009810704040c032000c06141c140d0414444840b407404080784000660449031822404184d101c0e504203120001e10b800c1c1402e508004098003000501100030044c1d01c0d00302007000b201121140782c100450050711a140e4940039018080501c03041c2e88450300c544c0040d01d41d00b003100c202e03940300c00280c098505642c2c892410843c1e0f9000f90000c1d00c4510072802c0c13640788001e03808030614013071030141141030820305001c0100300d14524001c00b01030400003540e000020405000d200c290803c1d89c1221214801c21001281070301c09640c5540c0d9140b85400d0180305103117603401c005c00c1800503024400c004040c3d907540d00168240e110b20140184090785a4464138401c81d005280b014915202d5415959248020300001e41f418205480000006440c220100040d203010480e500140e5001e0030480001441c0100103912070034000f40280c145501d4140402c00c540d0140810b06c0c6c442c000400252000d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 271084415 1250 271083165 271083167
    0x1e040f1a13020f0a060e040c021e0c09070905010203180102100204030308040b0708150609061603081012030818010f02130f09020301080307080c1528110a0c03090f06 73
    0x40e02002030340203d54100000e08541414014070b4256a05511001e0f8028a44c00038040103150120707030002180150500303081e80c6ca07880b000c10006512114000c02011101104209841d039014060b00b0902c04440320030003141e60040148d4810b481214050304040d118540140c0c00c02e65107071a941d03441440004d02000301900b2101c02c500071760042c40140038503a11b618007584d9014054481d03095058410840c400145003010080200c1035020b00708508001e29002080b040c001d95000440100d00341200f00280d0200e480c010030010f000303018020303030182070a0302c024003940c402034002d043e2981c0c7d0010084820200f50041c000d08480d50304219901d041211034056000294003801e50994445400050305a00c14001d983c1662a140701031840c0140599412a103540200916051342c0602c4800c2c2044545d1b0785075044c1304014541a58183d1a40790309039074041038080070001c1c801454030030602c56503141d174000e460103030704941013050300c2c40300c9818103840024595005422104501034086001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 271085665 1250 271084415 271084441
    0xf1c0b040606120303091a040c120206090604080604031b02060304061802120606030f1c0804020d05010e03190c12050d020f0d0b03240601050d06121a1e040f1a 70
    0x1090147d0361984104c4a02213041030b040c202a540038001c04007203103090041c00c035411200c2c2c4110f40300810140c0742000740c0c0003044c0c0c1c680103a84001076907007101d8100030178950024403692000740c62071101490310120b5030024a4501000e0300250031a6514104500186c1c800e200001020790000c0500c04080302492041c0e80d1500e0445940f4003a015007141001200c20014814000c5135100c8030038603c0c592150340c01c03540008000c10690380820301c0c0d490381c40440e0b400c2c414461f014a00c80702a598a03d076500d00d000c01c0c07000502c40c0c0c5080000102c00c1c01d0205180c500000205410380c602195102252410710340031303015607078082e000c0c1c8500007540e0144003d2a4000c8904083c00e8081e1507280595101c00450410145502500407140e48001411136100b04001c00d080c0003d0f400004011b41c0307617518948100c811400c1118442038169024078a2111602240d5003c0304001803204000685880d220401d20081c0c001800c0056062400040001107050480c0a241181c040d000502d8569482d0b014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 271086915 1250 271085665 271085681
    0x2340204110403051b06210a0606090302060901030b040f0c020109020901051f030203100b030901090c08071208030402030c030d0f0306060e01050403120c0c140f1c0b040606120303 79
    0x1040380341c90003040900101c44141c80c2100e030040c001d0010030000c503018030340072290a10800c0d80601c0803c081541c08100c8030342003028102042d4003842c0e524191001d10222078598100c20140f0601000400040e6250011903000140070b01c4c000c0307518401000441c0182c1103940c1c0b400007190030881c2d0a48103a5056011403040f80c0200c6500b052a40e9500a10408226007008002401040b80183d030311a8001c0d002141c106510442290b055682c4417200021504152400c90190351610701034002c1c1300c0c42031041d0016180e000027421074203151418407544581c9440c1c0c01070286901000041c190350b000d00c0032f81118540a8140c03030780070041c09001068041141c6810340864901040450309501c6902d12940c0f418040c1c488034501400c0d500c0c4c404500c0110300d2040d0400103c030300080700140d214080c950091025101d59090100d09004201c880303000340c00d4107030140c0210822400001074891b00000701c06d80001c2944081c1d1a00d042450161046401042105107980301000800d81d043d44a215 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 271088165 1250 271086915 271086919
    0x151809150e090f1c02030403021c0c03030503011806080303060f040b0604030b07140c0a03080402220c020c040b0d0f08070506270a0b0601050a0504051c1a0712023402 73
    0x780320308001035004c240500a030f03180310069209000600043c2070034040215031142c038400301740f94a42941d03101143e000483e0021000500c02200412002020030b0a0222130041e411051222908213031b0125a44d000040c01d051007800700844200c80d40c0ca85500000c01c015002c0c00007075075991039081c80c3e0780401c0d00343c402d071000400812011105480b0303075007a900b000088001a140b415610b4404840d141c0c0051303c1079a100c85540550f2101d99141007100c03840103800d40c00802c00846230100641043d600205c200d0245080945482c3d003641c0700b820911001e68040203044204501d414505010f01070500018010310030340050101817440d030420714029214902c1e103c1c5000e0022102551a0740d01004020000f10318400800c2056007e1005440f0503c1d603813800c3c82c01c0c25074400005108405031300600000040c204c042d14240100e14111048a0700e1480d50980c0e00e05115400800c4800c402600d513081039400300e410003101c2d015142c0040c0068842c03c03001500e410700f01c07259a164074480d00c128 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 271089415 1250 271088165 271088173
    0x4081212060904080a030b1503070305070e01230a0c05060f0105090109090f242d060e0a1e140a0b0306070e010e030c0a030507151809150e090f 63
    0x82042c41c1c09020030380b085902c00f6449040145042042d000342c98a0f161040e808181098003040c00d2142c10007039407160045540101742420125009414000c0c80c4900034104105c1e041a00003901070038041031040e6210380c64035965900784500c1210070440100000b00389004100601c9094088100c1f00f42c140d031800c031210012660380c0c08621044030300640c4010034940009946e40042105030410045840c2c03080f580d148140400088001155100028403e42c0e0707452540640ba2a004d410441015480b02c003401c202d0702d4148101c64920a20042041540036100d41c400c01004c0c0346504000c0e1502c05000042c001d100480021040b100d100300e43c2800300303070300c0e06915036464500007c14601800701c544510822903414001114850408103407150507100d10030300d40700d05c0d031203000d0380c2c0e0300442c0244043c00c4803c1c1081c00d064410508160300408005200c10b4402941c0150031181d000c0b5003868a0005141940e6480811100e0359580f180c60700070b82e054204001007801045003135103540254161 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 271090665 1250 271089415 271089421
    0x3090c1c0609080a12020915030a06051203121e01031704031203020c0d0c081c0204080303070302090a06020f07050108181f0b0a0e011521060e0105060c0a1704081212 73
    0x2d80308a018130105283e0082301000515100e044c0c100003580c1140b00b074000416140c0c1c03070b0030224041c1010300f844d03d0705580c00060313412645081e1101c090b4000f18000d0000803102c90540c125401102c040c0409400303110344c6007030700d120305a41c4401c460041d54850f0f0090300d8000c5450f0090000d4101c40108106030159102442c00584120900c286075a48200b02e41d05085a804103080c0121525942c00d6151354200004a202c08042028521680700c45e940941c0e540546001c0c0051b07801568004015544036403000b041401d00403030980261074007032030004110368403900820b140e401b281d40c0021741030040e5088402c541900258807990164642414081c100c1d80c242485020000d82c0324a064042d410001482111101b0494002e000b40c40d10340a044100343c0c000020141000641550382a030f039038442000140c4205080500501007111480e06005054481c140c8608020030000c22407035032881c2044010211a00707843c040e08051040300c2d100304050030410100d0780544610240846000c0c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 271091915 1250 271090665 271090697
    0x12403020c070b0a020102070c032a030b0c0f040329180a0813050a0906050a0b0c03030402100207120302010911030610030b04020109030609060902010908010203090c1c0609080a 78
    0x220740712004440018520303140b900394000400d42088410341c086540801803000462950341614000e5401003402c1d40282d40d0b01c03070100030240700400144000e0040200204041517074a0300d0a070340801d4103070b8915510820030111818074411500020320039800070103048001140c03000148a0f1101020003d40c4c20b4a6280d0000a5462685000e441c0c9500550844c2e000400ea04080d1401c221a041840c0445032510001f0700800c800d0b4001e0300300b41b99100f1040015203443e07002903004100c010011850001804100b9032030340f0000b0000f90141001b894040d003038034800c00c5a00014007244003450525a814034009010388220101a14190340c00540c0c401a4580890302d2070040001c9250140424a541e03a00b0f204050010b10980c18003028080000c0820198002e180290703105180004810403288009400b000d201e421202081c1c5c070500070040249000034400060000464468608130004404140c0350b070390200c00188898140030711502001403580c0a0b040728403154442998151843c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 271093165 1250 271091915 271091917
    0x504050607110705011101020c01052401090f06030506030708031b1624030e030703030c020610140d061b05031e090303150d051f1103060306070e03031201240302 71
    0x2005001c0d003003507400708105e40c00f54888454141d0742100240c00c02c80d00004032400c4035802ca64804100399203001c2041c0c5003011010081c041701c03090070101c03502403c02d08209005c80450141c1000c0c50740d21030115102e5a001c00401000380324401c04c880d910132100b00401115518051988039902c96410600486188484031505a440c00da03510305004004142c820419102c0d002101c00b49a52102200303000c150a00091000a000c0c0d2804a10b0240081c0700070700e0318000038110403051145440600881003401c10f81d5207117220848012003002211b080c01340c010400c84100c000401d00107200020b10715000006144100003c1c0c20032940d00c0b103031400d00a21001c0490302c2c1e0490313810405c00030b26041e4584d020001c500d0400b8103500207141c2543c2e24603240031400c4102c80108a8549074080f1030001e107000e10a0002081c20181d4150f0520001082d9079410242900d0140500603164031920f40341041519604010450401115603641502d10990000c264035482d140d80220000c5100380d000e80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 271094415 1250 271093165 271093187
    0x30a03110414150c0a030806180601080a0b0a0801020d2307050306040c0c05030c060f010602030a200102070f06050603060604020702100309051609020408063907020d060504050607 79
    0x41c02e030209881e1034900708640b1028076a900f03464100203002d840b43d00002040400e030100d01c04d460f400740e00c1c103010301000b482610400d4555440c0744040d04010159034032005282c1c0203180602c0210f0840012800a1102d002a4001900d590310105035203038004803540106007001e944044114110320030300164032400d60200e4102010440401c00701d910740c285580030a00411052400001841d0f6643e603641c1180d2000c407100d50782d940000c080c00001d10461b6056401403046000540c54038080c1c10024014480e058020034880e040c101020399805030a404a03400c0644c00b103000030542a143c58040300404058441d00e0080c421500020700c203040c14402c98000f40e800905403007c00c03902003001c4010780b219081c226858000c0c00014071510000040c58000381030385407400350301c1d10308051205140c4040107050360410b40740090070b91100e0032200c982c01c0c4002803001d080c51094019503000d0b802c9215038203009400402e0b003d0b4020a11400e07900807805584a003054a8403500d03a644220354080c008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 271095665 1250 271094415 271094429
    0x5120f060408030a140a1b0207050a0605030c1201030c081506010c0623090304091407050a081f03240524010c05030d0504030908030f03130303140702030a031104 71
    0x800704001c00c1c14240555484440c00703101003114800ca0062054486060305c24100f85500c500b01007511995200e40f100c50024540700034010f0a20f0a80001c00106152040c802440000800700f520034503000100ca2084c0d1841c030140c080c550b074919045804108a20070000c0a024001c076803c540d00440301c0310340c041c1c50141c0da0202600d9054a030403005041c01d03010b810304220010740c100d0388100041d41ca45e108107070305009946c5461620103444159450606c4422206210b00704010708070340c00c0403c2c3c0341c0c500384500d0701e20025a103070170701c10304408000fa020204c01e400e0702000108124402001c0d41c60050501c404280d101c039808048010794005503041c0603509480140c01c5685a00d9a403090340c7c3d00c00526007400d944186489680c00d41c2c2c810700da900c0405e6120020402496001f5128500800c1030f03800a42c034103100c2500300100d900020f491400e0f0710600380120300034544a5001203c840f5280700315901c8be801d180c84080e40c1e07503001c00c0d2140d004c00e0401e401d0410100040b0706407070840d510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 271096915 1250 271095665 271095673
    0x220852020306070c0c06094a1603050f07031518060303030b03190201030b1908010b041d07030f02130c0f140f070b1308040b040603050a09050a0f0203071502060105120f 74
    0x30b00c102caa0844041820f559509405c4081850082240704021490041c503d46050040d05085801e8041d941c0ca4980d458245424401030010f20250824003038dc0c0500e4900e8001030001d0703400041140c4510380d6004802c0c210407003180400156556000ba4101da20a8504100810045042c15120301020600b030101000010122026502a4002d040015001843d814912194801d05c1180800540010369560340d01c0c1c40c030b0405405e052003813542181d418101c080d140c0f219880d0b410b585107014000107004003040c1044a0840d00e44101c0084100342e042e20a02002203030610080c50807854400c854002030310745c040744030b128151101301d6002050303c29502e4581440b030346402d0540a005090208007011008222021544881c082c01c042e102503100c180e0746606e0100020306982c03000d007242090504c0d0231100d0700050381c001001403100d640200d0000d14602c05000003820b1144551140304249040c0c00d10111032640402c966060302c1e011204040f01461000000b541c0e00351740c014000c05648 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 271098165 1250 271096915 271096949
    0xa08070b130501080708040f14100902040b040b061b010906050705093303131a0403030f02040f030609050c030304090c1e080609220852020306070c0c0609 68
    0x181d000d048030038041c0602c03000427078442c14125840c504011141c0d140e10890b9910314040c02c510301800f8840400200321824040c200b004000146a03106546120280102c022218048074100390040c030303002a0450000c0203145081a0040c210b80d100303c2c1000e210701c4981c007410000c4124054120320300c400c0300b1002034602d980b501300c0b281c150340003526103001c8895070b0400000048851002c0b940300c5480041600d00c03400c240c80c0140507108000700c50012640140b0080c442c46400264200c1203a1304954080b0b07500349a41005400c00012646603a01400700040c00300345002c0c190070407040041940d841d04c040002c1107107546161402d1100c0040056100008510355281590110b41c0003089200d01c00341080e103031028007401505800c012642c1113800f20724040003440341c5480410300700c1c204c141c00300b039030f0b200e1506450641002113805282c00e400c04c84407003003071203c4801c1030004d42c0d01a04841075030a100c035003d4010307054850103ea03a503480d02070100b0418480ca5001d400c6070885420b81003801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 271099415 1250 271098165 271098173
    0x306040b130309050307030c0602060a09020607080d021c060515070203070302150408010c02150a140a15080303012d03110d082b06080304061d0a08070b13050108070804 74
    0x101c0345032010303400c0003e444404030f401da4041c824800114801c906e0100c007246844800b908103070000380b140700440d240042c007001603201c0e80c040362002e603884040e4035039902d01c524803034000b40105800c00301451a1031501c01b843c20407e03805603041e02c804841d01d0303690509441014505108100c8000e416402071201007005041c1105601d68140911002d24206902c84070f0090031118074a9101e07005a00c0048404500030242d4a51900007080f04000c1c0090440c2c40311a0780e140b6000303081e1440c1c09680302c80c2c84078031100c0720a034240136000b02e0007aa566540e44800722281d000f000345081100b009001070025030701090740c0140080301d6106400d1210220320504028900d0400c480a40c0c800e00e04000c03020300e1101c3d03e0101c61103031000c00c07420341c017008403224003404440c890703005502c447d0b100b0030091044a0b000308080d820480d282e015000481c031840c0102d1400b08280d44640c0c014442d440000c9140d50a420140c5541e8107504540e01400d5520301c01120b803d5402d80d50700d80400d4201010401103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 271100665 1250 271099415 271099441
    0x7080915070203030c07060305060108010e04030e04020f0c100f02090a0303050c0c0918060105060307120b04060e010b0403030e0603040f020f010e12070504050c1219180f110306040b 80
    0x384020031400e5050440640101e401c5a1002407071040e170760401c0005000703150301441059001b0b50b00386003200c000d605160b4940340e11140500043c05215171080d08002540d960740444030354000c01d0312250b031202034402c0c1c1641d86111581c8400d05d81800d00e611210038407510310030307203866400040003403007814030310340301a100e6a0000e00405103d01580001b128a500e0304d0341a28000c00680c80d102d0b010340050001d141c00c00c60306800440c81240c040081c4000c9580c0300701015280030b1848000107401c0c0c000d038005001020964010340d07040c000000002040ca440d0006001203901946414509030880c1e4104910b0b44400c1b00c00502648684d071000000d030518082d0545415410304214295a144c10006450703001001c1468003141d001c000203015a082c507015054015810354001403c0c402ca50b501149035010062040c12608000c10109182040e40c3d0403c0f2034a902d141200c00b004016402c1c00a003503072031080c0551713001c49900c10b401c141e8100000e840780f081d600205006015190a0012014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 271101915 1250 271100665 271100689
    0x902010207051315032136030b07030e0d02010b060a0305191505030c03010506030c090606040e0108012a020a14010e1504060507080c041a0d05090106080111070809 72
    0x1680e41e5509010b01c4141c0780d91810000d140a00d0002d240c0040342201c03c49104246c0000030704200c403110a03012642c0e1000085800d0001281c404c03001040445200c224040540c3d0001c2d00c0341e145082803050541c3c00d54040080c41c482a0262040d0540411040e0700f41c95203c5400c503001101004580160352190740a9908100413000340075440310b1a00310351050f514010030b441c00340d190004040005203402c100084d12080300703500a21452030030b0704c000390320f034000000f509020f18480c0e00010856981e003c11074000e400c3d0183c0000140d41c41e094040c0c000c10303000740452140b0071301034801c035140c0c001c400d100000701c1415030003081c842281d55240d001e8094800d101810799925800c4032200507100340000305200101103800a046e251a003004020340700b0240000d0280b03c003480c18003820704981d100300c80c142c2c0c004490000b40075132040d800607428442c00b08149185403030801031202409042d0484400c0740d01d800d0080c0705600107122400054496204000c01ea03140402010a80d41003c1c10542c0c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 271103165 1250 271101915 271101949
    0xb040b071101110a03020601080120040b03040f020a0303020a03180b090d0501021b010213050409020102030f03071b0819030b061b030919030b0c04050d06200d0f050a090201020705 79
    0xc0303039010203440c1c80e1405520342c13402c0b800341c2c200358014081401c09100700010308100d00000010034012070305591082c0f040b400340014610000000609020440c1e0030020035a50140c40382001d05d0303403810f0003911078056810850008480f802010342040b40002c50b1000e884051461600c0c1043c60010814015240e55003100e0554080c08154000480d4200d02005118010300140c0e407401e03c0842010182843d400c101c0c4a00d107481041001360368000705443c06000030080150b5261600401680e0181c0144083c800443e4160607840070886034030080c0244109101c1c070f07400a401c840809806403400300401c90f402400074492625811103000b46000310844235000d41745450b521001040c0d0b84c0c1880d06500318024040c500c100100048aa181640031a801040743e040504000024850f040d800d48090182502c5140c0020b00e0300b48000070342c0040b2703100c441d00d40e9036034640950580a0084600c854907890300d4840040d0040900340640880303d603050303024150701070901040205a48421060030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 271104415 1250 271103165 271103177
    0x11701060c0510020310260307120c0b04030306050315060102061501052713020f0904050a18141b1327110906060702012a0204050c040f0b040b071101 66
    0x10f5408142e10040d070290500d0444440c60a0529440701400c600d080c01807064030031701c1900c41001d5240441900d0b5007c0c0e100c42c09030140424103404a0300c07216010006040405020309000c20035405a000b00c045403819004e454480b1044090000d40d18011100180581c00500000d904240500b000d0034540300c0c14140700b030078502d40010030310941c505003680385446450150b920310945000e05040c0100441024254a0a45c0c504501150390103100c00c120302560f103c4e40803e0030805031390020003600c5c2a4550008030308209040404027185480e100003070340c1c00f91448002402d0354052084844580291600c0140100200018020151903640da003812801d00603013008056906042c0800034050b001c1c2107100b240f04000c2180490000c2c00c214440d0000f0421040142d8100c1215400c00303100318801844e44400c0703442440225440800254800d00c1c21080028130100e4a002d80142d801c0d13003030411100c6031115218101d5115500400b1002d40303050200070001040c404e422814800706160071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 271105665 1250 271104415 271104433
    0x16050d050a0b091f05071704080f0304110418021309020d0206030601031b020d0f1719060503030a0c110f0102100b01090b030a0f0c05090d030309020d02060c0303010e0105011701060c05 81
    0x21204c42884001c00c0603407541c440301840046a4400901d0a1400c0380784441e030500d041c02e6980005510130a80d10140512002c0005800d02040561a202c45200540300f40a0040007001c6003c3c0781c204201e0491007203e03028284e00402c2814070035843c146502401103a10a00d440d000c0050b00e1300300600890401d516128142000c18502846d94010582500103142c1000c2400300600360080024100c4100811400c840c1072a821110307510781c02c00c030f6841070080c0307900b070502c40c031f81c06040fa54002e55054800007689250343c0740d01c118407a000501880c520742c05107107444d04000084c2002811207006034044865030b104181158041c1001003414100030062554403614526103030401c541124196030b0781c04000c019245a8059204850024a040c0d4503000ca081d0001c0e8070000015405070030595501c51600843d19510309540346070b500149825241c031040820141d0343d0703109001c0c191001e40d8000001626500503980001803100c3d5040c943c4d0075a08111040f81d00c0e1682d81020b0b15030348100e070070b5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 271106915 1250 271105665 271105693
    0x11a0112021b0a080a030f050f01032a08030d0605030a0c0e0903070c0b0a030f052208090a03060c0207060905010c0b0a02190504060924030506011e0216050d050a0b09 73
    0x50441c1c0358130400c0810303161040e4070400b900300d03455040030110550071720041020428010100d641502c1d4845c0510501c4080b205410520404212002c1c0c0300c7c00a0210200e0401d20000c054100d161280c1e1052003020b44401c107140c0c4811401000070860b109419091004a008000350781d03005a4140442e4100130558131034141c01444c0d03600400100200064402016034180228600f4184894044c41541410344100e5011030881c2c66060021583e0188102080508030440709900f000610765481103459080c19001403420220050141c070440c0800a1f0040c01900c291080765016101c45611044a444401e10080020300300640c0c158208120f0031003800aa41482e19140d155070f6444d1110f003094009060362140f504410418002000c132a665100901e507090305851040c41d0120311a00e50900683d4604c80f0b0f00c25142000c0d0002c80c2d0003051660003d021000c5400104940000980e110140100c9400304100504250058082c0c1070104640b00d12403500040303114110307840ba64000311 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 271108165 1250 271106915 271106923
    0x120f0501140f01050613051201020714150f010803041806091e0c020705030a0618021804030e01031814031309150b16030309020a0b0706050603011a0112021b 69
    0x1400308600705000c001e0046100791040c0640c09410144c4610346002c2034056079441e1140d81d8400c652044040c0c4910301050741d8290150b0703405070f40c85042071030350030203030601240c49045801c030000c1014500c400145041500c8200d0305d0403126128040d611301400c02e03d4080290260b4284480419291180050700202600c43e902a850740041c80000c0540c141721014140c50060f41c0032002c65100d00d01c00d0080e60340201d00c2d00300603544200c0018a40d4541442118400740c40c4402943c09500d01c502038000303046071980c3c00e02c01c82c4240d07907022445003982d0041d0112400c4085c6101d510452b50a103070001481d940e0b09042c04952641100d081050100509858107119000450313481d0b200c88601c95a860701e061407201811500310702c070742043c4110360052002c03080504041c08050300c0341c1b800825910b41018a0313015043e101c02d05aa1001c003802e0503805031400b0388401d4007a61070720200e48800448072812140d01304059542c0340380d007403131155904081e40000c665101c2d200c5c07500070212000f504c204 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 271109415 1250 271108165 271108181
    0x4080702030715080901061a090d050a08190207080d050403080a02100c0201091505060d1209090218030c03060720011b021518030a0c030c0228050a0f120f0501 70
    0x10f13071541c2142c80c00c40441e50a4600c181d01000212914200407950b03084d00c203055400403e02a00c0d400000d00709410032602d01400102c002d0300840002400f005a5001c109461520002507001c941c0400e542e0f48209030380b410340c6814075001030703414031040c000580414020000259107104860210f10750361940000c03603800e040c0050250303569410348810003000f00008212f58940300410041450305002040d5400740012000741010320700494040100c3c01000d0807005004401c5085403144803110200e8462000d04043d240321340b103001d203e42c03d9403a000548a00c91605651414440d400c05003c203c80a4090700a0400c40d540f1003003130901400f04030402046222040d802814142224110b0b5094401c0c00707001551042c801c03041485403c01c00100b12420b001881ca0100d10038800ba042c11034500400082c0254801601e00f0141c0b20441500010410461648100c641046d42d89042213030045243c03080308610003042c44100010048100b56404c020300031080c924818074107595250848140d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 271110665 1250 271109415 271109417
    0x3030d0e0309330a11060106050306120316020609040b060c16050d2d0b090106030302010c02010207110f180c1215010215100f030b06090a060e04080702030715 70
    0x106829003185070050511000d5003120341552520040f15402d107071107040d451800c3d0382c1c08200241c2644514410011010701061a105848095844160041c282d500070750340603129521b0883c1c1d41800742c00120031201e440041c00d01441d51a001c40d400c1c0a040e400c8032140680c0f040d03850442d1a01a1276000c01410440c0d240006008825600301550009110b40c1e0000c0f801808403041d10700c000344450780144120140d14001c2c074844a02d000c0d40700700c004031a020003407607060890b080c80350000e01500100d05a070311a800070320846400480407801c0b4025a41d001d09590b0380c1015201c01800c0110101490041c040d00101400038100c00907124940706031196085c040b40021262a9529290a40e0350000001100c8800c13030703c080310000b0f50b90b6404e203c0300042c1c040303910080350490715114000e00050481150314150a07a503810500f03d0040c046441034003c115003000501c04c4200b510810068036400048100c40c0d4840c3e458a070556000382e242241c1600c109a00070490307011144030303042d902c811 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 271111915 1250 271110665 271110667
    0x705090919110306040e0c010206040f05071505180301020a12230c03040605070e060706021305030f030a020606180103030c1b030c06020d0f020601051311070b010314030901020309090603030d0e03 86
    0x204c0c1c0140402c6031170303100301c0301c0541d0005050003607542c0e030106200750400c0d040565110181c070786e410440c1c01d0100c603a103d012844005840060f600750410040c0c500a1038078035134011040c2c428000d250030b0b88104403141c00022140b1070300c0d84101204e80d2042981484103402404a80d040c1035040300d40b2070003036980120304c1102104000c00c00005005403680000585070a07242690070501161080c02107100082404d900496940da0080c0012030301e030000c110040440700c600c200d060800d81c40c0e5001449030b0005004000c002800f50414074402d0112045511307c1074003580c03858404945210300c60f00100c03407256545a295000741482c2a02c10301441c0103842002d04507180010184c60310500303100c0c00d814080a41850b0307071000d8001c580c09045400a40300c4440903a810008034004003007071009681c2c2c1050104d001402e201031000524182d0348103840d1440c0360807000159540c0c034000c100e20640164000c1181e40c041c0d052541c5025048080035040300d041c140303401038002c01c0d02c80151245c00d851748 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 271113165 1250 271111915 271111921
    0xa20030114120703030806060711030a06060f0603022a03070f060f0f1526030304080a03060f030b060f0a030b04052109090609070212030c040f05060307050909191103 73
    0x2074402400d62120042c41c0c001c20205155540c00342c0b8082000700034034810000802c00c50184128150540303002e120040c03d94010046500d0480c006050030300517504400001e540c0403480d24001c0c401c0342c0d00700c5607040d0100c01103480006032807d00d402e080c080c054140010711031040050205428100b00c1072080d0b802054a1801e401c4000458545454402406040004040c03180700030b00007520a5684000b06000340c1c000b42035a0f22400648100884070902c8000100001d0000c40170103807600a420f650b06200a6a0701c1d40003160150581c00050400810300300070540b00e18010000d54000000646070303007040c0b0380e280c0f16240540c0342194280c581d03402907041c0b14409041c0c0c07440010317980e4484650600b0001c54030302140c64040028440c1c2d02401c48003001c00c10301d80c02046965000740d2440042580c901e0003007520f6041d9005807080314040002144d0200e05442c000050700e12400d00303640d5207418032080008120366803402900b0380070440f880681c0c02c4d0301d1034801d0086803004080701e030342181e07170341 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 271114415 1250 271113165 271113169
    0x605070605060109060c120509100e0306070504050102121c020c1f021602010c020d060e07030314040b0f070c05030d030b010e1903080d021314040c170a20030114 71
    0x1e50010041d50400184000512080350090712442d00b4070f800c250380044039044a40203480a105015074180e1050241c00d002e80c10701e9002c01904846c100641c2035950503102d60805407001c1c02103000d100e000d41c025043d5412a50482c802500034420011042c04164242c1d014020403079008c04808101f070381003100c0e034405009040c00486610101c404046103450b240c500081c4255243e03010007410018054225015035441018502580341c000d40100405000c010082e03a8400a5200460114035000d40c030725085140c090a1302e0444841440441c03500c0c000c08030341c070000c0c2d0000004403210b8110007400301d00781d2010041c444000c641a1400151542284d0000d88805aa1003182d07101d0601041682d00341095503440d882200c2d0f0044001c0e440304904500200640030314110725495080003200040e04c0b241240400f000c850b010784081014031200c60342100c1079442801040911b00c24800414520101980002c5000c60301c0301d0022242c40d03d5004000d85076100380d0202d0400d00100c4292140d078 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 271115665 1250 271114415 271114421
    0x20312070c0c260609120c070902030a02090a060806090a1805010527010207050c010c1713050907110a3908010c0f02060a0f11031f090e120304030e0a06050706 70
    0x3d090300c004140701d24184940d40c0d5122014503d10740ba03900c02107039403010010704003c2c102c09031442c100c1c20b6486c1e00d00030070450001e400542c200341c031038401000c0010f8100d004080442c0030710700140040380503603507008070f07000a42400c11300f48600013080c5083d040801c80070f01c1000c0c02101c810f613009040d1040300f0f110940301c40d0b80e905030504c280d10401200700003607030002d1032040c0c015080c00d0075034200b5014140040700c00d850900c11400d03901c0c0080c00140ad01a5600c005094600841d243c59068940d03a030120f0714103041c01c03202d14899009408400110b9000540c92007141d0070b0516040000388142020201b60508046000f00211030310014003842c4400e000f034a500410500d09680c0d808004078000b55a0380018001000c3e0540d121032020682c4429080301c032516030345409407a40c90400a221800c1c00070046401d42d41990312543c08520002503008134814019035500524a101c04a49060300c5d541c0080c004405002d00340403880c526072120740d445002400d10741c64130350b102e81c000e04141c020703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 271116915 1250 271115665 271115729
    0x20d020d08070f141f0b010c080406090305100e06070e1203120f060907050a0c021f0203090a0b031b030907150210140106050706090f05010227060901020312070c0c 72
    0xc6401c000c5032441d000c807415640121801020178045603c8040100580b420404048082c040c0a400a008102c15400c60020382c1240c1c414402c0b513000418122540c000c03200c092001421036040b85011840940c441c0b107000c0d1900d5401001e000e260105000d00b41c3c9983c0c441514040f440c139408040054000940038a03581c081e405846150041c6001e1000a05921031740f01d112040c482c00d44040d60030340d01c1e4069442400036540000d90894240400302940d60b03040304220178402d042e012004181c02006806582c000d4644485107104590010800c00c4142c100030074011261141c9000060350051a0340c0c50759008000d40c01410741501140e0586090b200c0d0b01e15000c007a42400401040340c40e920000b1900e4103a0060000034104020340b8100c00f0200388580c0c00741545d0b0020901902c0000030016a2002d4441481013010101410041c0f049038011b5440d910b025800c01d000055000c1403503408107621140b545098071003860070f070f6541000155640c219580900c41c2000c00444140c1c88044e8000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 271118165 1250 271116915 271116953
    0xb1c0209090102070f0f05070b03150f040c0504300803041703070c03050313140705040609050417031008010204080102030411031c140d06120605061c020d020d08070f 73
    0xb00c0c040682d20380d1810704544000007000b92036010400c2081c42011701408000e0140c149c40c107903582c00d04804030a04000850f079124461051311002c544189407906c0f60f400341258039100c541c01c0c03a1901f0200d00c20705988080070f0441060600029403580f416085035485c4920640f0a140c6904041c1080050300c4024241500001010424000e1180d0070079a8281015413600e4200d0f92681d801d0000c3c4c4043d00003580c000c042c404542c0003600c0550340803071603a05aa1080e034003000100d9481d0b03214000d8510507600034212200ba0b03034a4134508000c400055501440c492007800030a070f6250744007803c80c0d01c41e6118480603540030082c00304001114442401e5080c04500900c00005c0444528107840c030356600100601c070380002400380368014001900c10f10f02e201d8104100c00e6548041480810002e03090440320b46d85018005625032400070104000c02ca1107401c0240c03840020f80c20300c40d1b101c405000030780c0d1100221070b02070000390101c8000c25007071b403260f030000c52028081d00e0515550808008800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 271119415 1250 271118165 271118167
    0x203070e01050301031e1514090610031106070311030d0209130515010c0312060803030906090105010f1a070b041a181527030c060c0901050703120b1c0209090102 71
    0x10100b6401b0060114040800b90300e01c035801514513254a80e440300c4108100014180162201d4400c101d170380491041d10311100b80d135410340c1c602188044040407800024283c1c1406280003031181800c801410708503100e400d03e03084d40103850004031700d50780051009800c582d400080c491990f09001180c4408c85010b002c003404142020503112400c00d400d001068104034a030005181458030502031035000d05d8401d00c00304180740e150551b1907240d6108448140c132a201d07a034081440040144102ca04860350341c030321050395906008400041c1000b0010b1028017034010301644000c90701d08030916000d907220350780c0320488030281c00b10781c00c12544c0101030070035840540f28803084417000490b80301c01e00300b290340383e551050f030316174540b414144501c041640088580c2c0d0080c2c05e0140300080100601d9021500311459652540b81c500e1683c400c1403002400a941070107120006030080440000c1e00f07003402c00100c0c01c12480004614961400050307920711003201c141b040c0540c01d210525030b0700540301500035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 271120665 1250 271119415 271119419
    0xb06122a040f05090604060b0c031b0307050c01180306021303020f040509060105130f1a1f02030901030e01020d0509030a030e0111070206032a090a080604020310020a030b060403060203070e01050301 87
    0x54101d841c014403e16015807001d2000900e26501c03a4441c0028105500c031854460784920340d00755032034110040200352a0360043c01c40d0030151000090b10300e000c2d40300c001081040c07508001102c0b40c400340090b404051104081c0800080c296001500020301c04100c0303440454510b0040110224068400c1d40c0a10b19110a0140905010a00030b0650741d0541b2002185c54001003445d00818013036083d503060b20b242008100303011022404000d600007080b1818085226202c1d0711070751303407000d12801e0005640200f00c0e064503035010740c02c08a40d1007600300006040c84411940c0301c007507410807152414079400000b40c4c0d824242d01845042130014500c0000c0207000e460706054601e034400c19101a100c0c03480400010300303002c882041a050170700c0908a1100e15000f80b0100c003041d82190456911502d4241400b05050200280300d620480e0028002c2032014a41e100781e100030751005041804150300d64000c180380f80c9822008100a51088200607a645040e002c0100321528020140e41040010001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 271121915 1250 271120665 271120679
    0xe1c110a05061314120319080603031206010807090305060f060a060905061602060405031b03011a09190b19030b0603061b16060e010b1318060b06122a04 67
    0x5603001d40308107040010448084c0400034100450500554400344400504030492503040700307007003100303100607295080b25480c1c042c201500c0e40203a0b1400f03e8900d5109000451540c031034190342d81c00000074200756030b280d6100c2d10381d00c0c1802d0048505944088406050015604140c0d10160080c0080c0c5000ca20040c100800503040f4807901d815158542000c0100c401555540c2c01150001c000c020101c6042c5c41c8002920281c10b05200e650510a5280800700711001d124010302016040d001082025a55a991085041402819010100c65969040c52845521404038011003e2086400c204505240d440c1010341940c00030b0181d80607420810a11003e1010380451a60740d0241c030315034588401000d0800b100061034401c000c0c103020f003412188190000107612513113001009a402c0c143c209403040342c40b01a14190180c0e52451056a5007a01c041071807540b1140750700e00014030603850000c1d642d0f040c0f08041070513904030b1141800c01c110420084146d80036a60003146855441d03084c0303441e00b00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 271123165 1250 271121915 271121947
    0xc04020405010e060d1512050d08040803010909060609110c0624090a1413030807020a03080114030a121e080f180a060e0601060224010302010e1c110a0506 68
    0xe1564000c01e0041250107003510301d60818414a0403441403503e07603503070b47c42d150200030207a80e10903992070261018045005100b04c20040c440e40d000442d0a02d5030346458040f500810703200364181c41055840c0b41c0414040c0007030064244448222080303a0f21480414a400d0400d40003030300340d1030311441c0500070380c2d010491041c3e002440d90048031517082940c2c4400c4080c0c0a4500c031050072003035107050b004004010064105074024580240daa10303180b580e43c0386042e42c0e69042c03480c0180c0440c8070303a001009100605a84d00c0a480030140644200000c90398a01c1031941901302c040b00851074000c0a410b583d00240b00c481c15590032840d103d9490306007100045202103014190302058080c0001d840582d420802c515460241d00c0301c0100101062050925110002801803030300602a030b402060f500302800e5200a28018103502210259207903600650b040310410192360b40215050a0303a03480ea1052040405400b40602101c00c1d200703421800704280b038074243e00003c0c414141440300d1202c4071700c02c0c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 271124415 1250 271123165 271123187
    0x71406032a0417030a030f2c0c1908061006080708130b091605030109200a0b0409020904050a021c09020f030a060204080118020102060403050715020a030203090c0402040501 76
    0x420007403009071140d1003000074861500002214954200d03007031060380d800802410000090b98081001d2480800044141c8040030f10440d1501d07441804001e01c0c020100f0b5120481014204446000c000d003400701f02c2111005250901e901e009800400c608081800465400140c04180340c071558108480603041420162040c02040500c00c0050b400b1039041001a000642020036407400303250a00455940e42601d14600c43c00051002002625040c1401a050100d51204040003103544440500004602d1500803a9000031074500c00140255610010409002c03450009607032868000203210030344034058541c81c003040c4100080840d110003e1b20441d41c409944101042004050000440c921021072001d5894010505c01c8410804954001c000f11601c1c50300a1140c02000740c4101c0e04a00b00e40710180c0560480400213000910500c014178455100d04211006000e0900e6400100e8000f0320014010940c00414042099010030080c5d40005080f03409618050800c2c4c0000c0807001c0e00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 271125665 1250 271124415 271124461
    0x1905090f01020f0a080c1207051f060f091a06030106090602060f04020906060c070312030e010b03031911030c07060314060916110a050f0c130c090e070201020702100207140603 77
    0x8141c0066110080c80a400550b404650403900d2358020700b0691703252050040b800300103589601200c02e01d50854000c0034115440d41180c94130091a0146d2a400750404120300208040540c0910300a5030300c2d0f0f0047d5002c2c0c05d055494400c030b05d08200700a45002c0020b03184010494442040000613540c40c113909a006800350f60a80c0c5400308030040f6454076406420003010180e070719450944056155014401154050740284506a0b03008141a201c0c421004406052a0381c1c83e054555680110482e0908407910b0701260328222000c004079081c170820750072240010f03840b0303607445a003079285811a9411120488619480b41040807100398080c41d1000442d09000d503024141c10b4004040c0039000216812030256104510b910440d192205100d070407080c401e0100c8908a400e1950314450300c04281c0d0b03170341c40e03504c82309082c451001c01c1a0801041502159020400c460040e01d6642660f4041e41040d0000c146150921001180500400300880c0c011081030040010240001d44071314507580b04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 271126915 1250 271125665 271125667
    0x30e0405041208150a030f032f1b090c22030602180102011509050702030d051801110f121801141b16060902040902060a120b010903020f090601051905090f01020f0a08 73
    0x71fa85810f1300c02107079252048640403c000c104100d21089424540c840d0340d545000c0d20480c84844072802035100384003164030b4101280600051003078000f80024030309008007070a004c58009115140d000e107142c040e0411114030360041144056000c034040c3d45081e4a209000a04c1500c8294840c1c038000c2d000c5114414a035510303140130406480c02803045820448200c00e0130310072071500c2c208a14000f40200e03540f061a6180c0700d00d0310400500c1c80155195000c440b2402c0d0b00d08a45117640c001c204030040c4c40c214100d9511400a440307803900f44108000d908050301d42480910342400d0b000e207140d181304020002c540c030400080d0416003003004000001136000c48000307100c0e1801e001007002094560030081d000800002d4003800542c02c112030101d0066803480a001d6110300b83c0044940d5001c070310000707400142c0d45d15020340034542031000c1a8884010300d405424810f000c01d036000069540d03c4035401003140060044010f09029102c03c1d4101000e0008100110700700301c0d80c0342d0b0303000520400350a00304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 271128165 1250 271126915 271126943
    0x1b05090405040c090207080c30090a12140c0909031c200c070f030f02240a091403010504260910030b090a06051309030e0405041208150a03 61
    0x500340c0f0348002030920070408640319001440c0400c0075038420500c15245205030350060700310b41c8104448240024920801410541c03118003c0381442c4c101c0144141c0c017503090040032411029400d100b1801500614046003030030101c100362810800c80340d540c640580b0f4114108810600c00104440c008800d000820310034810520303d4500038249044c91380d0b0a5000c01d607600301007035044000317000e9010031001134880709651441c05804801b002e120041043c084004003801626002d0780c207065051451034039890750034440b21018116404000c000f8081600d00c4803d01440a845400d0058840c064000b0005030030261076517260312102e001c0c0003c00c410030802c504006510030781603c0c0c240d100a810407507265410b25004c0c000d8554800b5203401050b41800007808040940640c0c82200c4019080540f4208021030035005400e6000c01601030040d03c620308606c81c5c54521800d48198098201c44030f201108140041c40720700c001d0052941c20300c030f5444840207980d0320540c41e005c4070b82c006040c1e40c0c282 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 271129415 1250 271128165 271128173
    0x12060e0a091412032205030c01020a1209021003050403020c0a080106080120071407030b010f1a070c0b030a0204030503040f050102010b0303070c05060703120c12060815010306230406020c011b0509040504 89
    0x1c1c80c2d0403170040140c00081031030202c0980540103001124030648900792044880f0b200c00c2c088461000001e940b00d4540c00e80740c0380041c001e130701c601c1d0064042d03c140c031140000748000c103800f100319520184a6a548200801c4901020710610b40b000b0240c2c20a201045002ca940d59042d024541c03018207081a0300c0142002c890303040103050025135210a14000c1076075645491500c2c11058458a170398100000c0c02d159010080f042110341e915480180719054a05040b01103189401c000c20b038119483c0e00b00408008520104003502c000d2130003030640440c00b404c00d80024291103200f00d03401d0080c1d00501000000492610542d020760745c2c10b641c5035407241100d0a04498842e25201400285460105442001648540040c080c06110002400040c0d81c40b1010303a500c01c040710510b9503a0303200500520001d151a0014042c40107508c01c03080300d403903403e00d10300c11a02040c2d81c101c2d0442c0e800101c0322140903080c012000c034030b211220303405c0342e140360600c002d0f1503031080310400c0e4411341d40c80000800b08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 271130665 1250 271129415 271129471
    0x160818030609010c35090718020d060e1e04030509061614070803040e0414010615080a0c050304030318170703080912090112060e0a09141203 62
    0x100001401c5803070300e0401075007241c000d0414414003400640c006000c101c024502c40460300c210203203d2030741003140c0c00e22140451090b001801481c0b49019000d8001096242d10081c00c0081d40135140040e40d400310361074250704903001640548001d083c14010002841201c0180020381508a0800c03901603443d440c086440344215940305034000e03c0807403c030311442c0c0c80a1f071001585204100d14540101c1c04002c00396211074610851010368820803040c0140071205140941080c455008482c55028856a072820740350076401011500069070518500c00d54800d14058000e0400074040060b0350380e56000500300e02c002007002d800e0503101c5840d5035000a6242040c2c003040c8e0800c00360705180c42c00c66420500c55100e25029000190040d010034407000c0041108806030103100300b820b14002500d00191401514120700c266115031b40c03a0700148400750741240710300c1404034030700001d02000342d85000c24011400d801c1c0591940d11418003d00d8000c00401169000615014940030303005400c1540701078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 271131915 1250 271130665 271130707
    0xd030b270c0708130305010e0a11040c020708070308130b04080d081503060703020306040c09210f0c0b03100b09030c04020d11041203081f060f03020903011503171608 73
    0x344072000aa40d0b5166821515403020741b4841c0c2c0003400445901d842e05170344e503203440b40e002e442c01100c1c0c0c1000c5283d29041c2d00003601c18a03940162008207654200035030410000c1e601c01c0c1c1d602c820014400c040f4400c00580e820207401304144541c01e150820684642c1c8011290300d4105000e17030400443c0310300166920304da119070001030071a00d9520700150000c3c007070342055440c540542e00b01403410f40c505006030380c440256a04042e01c0741e505c00c0350000480700c4c0032241b4000da542c400c0c21000d110215007490101409091200b0641c0d41d01d04003d0a881403428003039005080220050188405607980460001201c010450300581c03a0140d0005120060414074101c0b034010100180004101c0c0c1c0c5060175502c400d010b40c40d114444da5400f9150005078500d4100e111101074250030030311446008641c80590203406180050030003d0000c00f00e07007100d81c803410440f844001c0400070400c0001200e00001034003c0b14100c1c0341801050f130003542d2203c2e19000d000380b42ca8004510710214501c81c420b82d400b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 271133165 1250 271131915 271131923
    0x703030c0e040f061503111206010c0203030703081005040e030a20030c010b0f0306061302030408190c2f150705030a0503010305011505011b230d030b270c07 69
    0x2a0319140043e080100407604c1542903840d981003440440b60b000744541d0406400140c4680d1801080040715000040010711603814401344800c81d01c0907172070400180006070711a403034580050411b1003004800704859409144694100407441d4074081022040da0130300101405c002c8003030940d5000703520074030803082c3c480c00c4a40700100d000740700510150443e1341039502c02d0720701d80c01004400c4e0505480311811124150440d85060460b00340303558660003154043c0c0190140c1d070034480c41b544100c2e0345501910303400780087d0000a0500910142500c4400080d155101906020400c552403031920800110000d200384041c144010100c0c4055084440704c40d801010303203035180e0305c081c40981550000c3c0010340e0250710f4540c69a85235061883e80009403070050b16401c0701d511090f01d0685149980101c122000b65604080c80100d4080400b03207560510000054544001000c0707008003141c8038001450b2095840c14071400b40d6083c801c0b0700d80e0390705c0745100d031030b60340b80d500c901d0800d103d0711480300014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 271134415 1250 271133165 271133171
    0x1528180506091609140103030c080705070f1e210515090d180602030403110409050f0d0f0806130905031201030f03090501030515060306030a06140105100c080703030c0e04 75
    0x701520b2000719100b94607a14044042e801c01e510b4010700400c40e100302d280c07405c0d410050001800824000e030310351031800344211000b40c82c04200d03079181410302e200c80e44540c012001c1c2030b5042c80501441e50301c1403c650000145050014507040303413034841d04047d000c0b5110441141c4030030b4091190602c0290310f00030310b403010b45a00382001e201141d81e40d03901401c0e07840064480c40c1c4400c1a600102e54941c101c0c2c1c140c0c0c3c01503013042e056481300c0081100322002661b010341d03650b60400c0010024044400c0f601c030410040c0811140903240904207044480c01e01c803c10902508028407981d440b44a01c110040c044000101c802103807905900c4c5204110741c0d1902c540401000008001c0c030110a040044c0c072a9407548885a0350b000150305561098450031407520003100f00782002e04140740599031005008080b42d0740c0220640f2150222140b484c41001e0100c0d64000500042c14103071040ca000f02c070b85140140310003c4545820040f8000d202000b0704164031540c8260030544a00541c0c8013100c3c00502c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 271135665 1250 271134415 271134421
    0x92f030102070c05010e01020706021513050d030507030f09020a14030a0c290406080402010e241207020a050303070309020f06030a050702010c090803090f0409141528180506 76
    0x3c507642624030b2203401c0c0001c5011240e0800d41d4400308000e812100b6680082889803168200034240c0c500081217403090880c510710030004940108140302c0c6a4200d07840c00036a5062011b4004c0a0303440180100114904103180307403005803100c1804030111200580501415140f03080001c0c2400740c10600504014180038000c52600640c901c11b0042d0084080e0041ca217000c908401da0480c01244200c4020404a000140140d40500200c1c40f891100601140300c21f0608403480c001c140e00c5101080008201080c01059a0108401550040e20380e00013851f291440d5036031141e0b02e2000805200401d0f0b1030b581044219180c403001c0d0811002c1c001c0015851b440c1000000009090885241e4019802c1461448d6414040e0403144103480084000d5440e0003401c2040c020504040d0f20940d0b0045d984586800100360a218140c10386445a0082c008840816131800300c8404050048000004600c04086031520301c50ba402d006440484404220341007105100390058030100b001801d0f0f8002c40c410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 271136915 1250 271135665 271135673
    0xc020a110a030b101401030b2107030516031b2d1511160312050705030f04080d0207090606050409050915070e0a0e040221030717070303050703092f03010207 69
    0xc1c107001c5e02e0226500311500c2506400440c1618402c5041c183c01001490049007203c0711213aa0140020b00481114040c0780e9a0b51180e03e401246030b160000e2408000080c02003041c07008001028401300840c6c104040c2c03d0250010010440840c00c4d81009040c2520041c1c0e4500c140d4240000c2c400d0300b25955440280580c094002c5c03140b52800c0301d00e40260f101c0c000820343c1c80300000c0c0550750041c070443d020301480a8107036a0f81c4d0246005950342c3c4014400540421403034001031020302010300107810301120008001e07140116941000300d100e4141036050169a5104003078401b202c0c1a40300201d125102c0c14500750802e5464943e20131146201d00030400b00d60f41140300107a80130016614807400d41da803054030310100002071700c00a42c0305040010307541546e40103190070482002c0050580c0e2406c03809688410b0081c01f44140061001070210304501810780502c545a4403401e035085c140400c101c950340b001c1948030015002d16001d103404501410380e055410700300b944e80402400031580c4002d5410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 271138165 1250 271136915 271136941
    0x3061306060801060806030615091305010509030c07061d01030b0f03250801020f09210d020604030e04091a1b1204060f2a021002030106050307020601090c020a110a030b 74
    0x42e603011417182c41c0802e0341d038100000e05901c40c903045000d610301118090200f0103105800791202010070704100348500072030740c203200e400e001d401108010750f41d941040010718240f400d60742c0200f00744900d0314120700e0769160001d85260104070034600020282136082c0010001c1c0541d070a1150544508090200000c01c00e4840090039042e882c0b49000e1280c1c0c0703401081c2071348121a58004400e9017445520840e003400d440030b0302407803c01e020051640c0000101c01d49420000412400164040010b200500d6001448a140310800b41e4003400108480c1c0c0b02c0c12103501d1a4440c0c681694030401c00070340c405120400e180704508c416002c03c0c1da40d24210118044400b02900c0c280c88151078500d0b41c40c050141c0e8440c0b10000f07141c0c000c1d104075a50100b034641290050042c0ea032029405807801e24040305045100031800f0b00748603220f107a1a8242444022300e0000160810340c1c038649010030360307681c140e000100d4600440d4030002051144841c00085103503242d81c1c0c0d10050412802c0402c5c0011118449 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 271139415 1250 271138165 271138169
    0x406022b06080c131a0402070b0a06050a0f06050a0e0901170106050f0a050907030603080d05041209030c0b09030a051207020312120606030402060712021c14030c03061306060801 78
    0x52010712150b611082241e85aa6905803001da014201000c11381d61154960030040b2129082c20309800c44a412401060a0b6440342100702e40c84500d04041049001d400c0c401c0302e01130a42035910101107800c02400148a10481c042c013801e002010418540c680d100e561284280ea9020707202d0002960358248100c0c5101d03058900440c0355081000c0828107040404c503045100d40020001902140744c201802000318001c0d0041040686484000c000300c0c80c0c0b0001030040740c4020f0b41c0080c591420303042600b004626220347c0c030104818110200046505010300d0001da42d03080319100d540c4c80244001a16202d0001c1d0b00608038080c0313036500c4109007000b00181c400c01e4000e8054520f150b80713869452500c0d10581d00d504c500544a000440c800c2d040120165a106202920403882c040d80c503142c81d601103042a80c0c0c0c500690005042a404e08810700b48410701e00303107600f00b51242c801c591004d4400c90000800c4180395480c0440010401c3e5a01580320030003400401040000340c0d00d4250003440034400f4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 271140665 1250 271139415 271139497
    0x1009030e10020f030d180512040e060145080303012d030f0201031805060628030b10030807030914060a05030a050a2c0c04050f01030803040602 63
    0x34a5007410550700108a0440d81da81d86005545000303a4620510003e04003140321104481000724440c1c0019001c1001403004410003401c546c40d02e20701190f0a00e0f100004250701d0401040e83c5407682020044e11145040910001840120603688450300360034100d5168540040c035445200015498000720040d81654201c00200058816020656814070150058114400d001400820105442e10703840c00403140305150100d541c400008205036010600d080c25130305e030307000b2406200d11441d0400c5100341c0e44800411707410700da003903034041003950030107034840a03055007030200018440c107d108064401869011560b142c5480907030034018a880700c2c0703000300740041c00d80d070560784143c1ca040b509451201c1040d030f03500344c5113503500010040905000380100141c41c0c0c6949030400d08100c80200440c0c0222502092005d400c040c40d01703940340202d1610b030980524601420321580400d41200355042d02d400a280c65520b0b100c2c3e281c410300901c1900e0350b10043d072000d02c0e60b6800101c555041300f0800c440d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 271141915 1250 271140665 271140679
    0x1d04180506250f0201020d0e031305190b03131b0e0f06090703020d0603021203091c0203031209100501091e05070801121110210903020d08091009030e 66
    0xd51041100d070103080c402c1c50380b0241d141d030340002d1640d00c1100900004031041c0300241c2002a4a0300c1c200c19204000f45443c0300390004101c22412100440002c001490210355403040c03841210001c402d640c0307990042000c01d010000c00a4151010b440e9008940350340412540361000c0c041883d0b0032501301700e00441507041030010200d2400c580000810f0b005480c010b0240e15503803134492095000703520840100a0094031a0800009640c40c102c3c00100706100d007002c1c5036030b50184010040402d80c40303c07004640031104403205016072000000c4d100c00e1000e00d01804071589405003054903001e14448080407060810002150301c200c55000420b00058018444c1282568411036400341ca40469030280042c1c03074100100040940c44092205560150102030000c00041d0b002c1290215118040d00214030203541051150615100340d00100268040070481035a0640d002074403160708202c860100103212010410b0a03009107c000080b1045070404c1150300440d18014284403c000c06040c41600c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 271143165 1250 271141915 271141921
    0x506030f030307021c3b0603090304060f050f0705030403030801140d031b0804030b01061103040b190504080114040308090106140904080c0601091a1008071d04180506 73
    0x110001c20349002d046075402420312a110041200c0e02022118550420800c5440002c43d00100b51008200e40e46104002d4102c0c03074850103900c00781030b054510b200c0c4c001c0c10100200180c1c1c910100644084c0da0321441d145c0306200360914101e456000300540907102a0002030302004000000006204807442915001c08983c1d035041d003240003218407000940c101030038138100c1f800039100340d01e598520455a1005480c24949803264020350b0459001129006071160045c0906c0d90018a6440ca0b00d40f03000046180c20b0500310007440c0c80c062850350443d040d803c0d03103c2e010654014000d6070080c1c18528000c02a50b240040701c039141c214191010342c04900c2d1500400c03030009042c01050113458040166803425200c1d001070140189000748241c480410605c00900c05840a1100d0f038000c0048180200b203052056840c842d210858441c41c034424030300780541c2c5142076008011030f640001c50f42015444100c04907c4241c480b14201c040307541c442e1400c0d40314401c0624007800158894001c0040320055a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 271144415 1250 271143165 271143193
    0x130e0a02180109061211040812030402040e06070f05030901110d020706050109060b0f071704120b10030c14030c03030a02070f0503070e0610020703050109080c010c170703021803060406050603 84
    0x280e0310b000d020001480200140285c8600390000340c0c00804c400c40c1c2d075150564611159050100c0c007030b100d40c9032180000c00e10055143c10f0060018030150880a080103082c408805001c441c1c0b410440401e04c8008000036020308030079404500c8088558200341d41c1c4810881142c0000d5001c10800c0303071382c3c601e031900108008040d0300ca544103644a0710450340c5040c51a40c80d140c103c1d0801703c2c040311100241401019100100800f038802069644c03003407021a001850004c6401000401100c1c0c0303081e82182c1080402c1e87d402da00c10441706807841d031100c19000d80d80032a0512144906c0c0c25018800000c84200c5950300080c0741044036011051103000076141e03010035845645070302c2009030141a1b00301148d1a0329120300d400b19800307403030f004949046030b0381d81d12242503070841c0f20155010302001c03a10340c408031402c0c05a500480c0143c9030a8007403052050311903803494006081c038400c141c5e000c5141441c0c01c1c0035410362051410002c00f2203210b4546807900c03001621040b034204e4002c3c0290380f40a00c2c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 271145665 1250 271144415 271144427
    0x7020c0d0c15020f0712060b06160c0b12060114071a1501170703021303150525081603060806010b0d060e040809011b0b0f070806030a03050906130e0a021801 69
    0x561134000540f0300e9501c3c00715500d2131100404e1003503501399610901d10185646003001071103000300312081a9034450f170504200c1c070707954599806007407210010070404030208014031603d40d000781c0074201405e0822038520700c60014000c60740020300d00c0c92035401c00d890823507101211030b1145620700c81544680340d240004441012149030b1943d10b43c400a0007090100380a60094400181c2003c654501580c1c0e071f4031074055013007410400c0c1c0c01607941c41e000d1051143c00c2410a04000c0c000d03c140340c0007800ba2250040c1280c00040a001407035003401241041d09100c0d40141006140d440200c40042d611518201c03c554091042a14820710300000040e4200c189041c540c40755410108560514105d1001541d0440e508110307000011100740c00180011025200180180c00311002c80041c0e19083d040681604006800903200360310400242c0b0009501c40111030014078140c4210f81c40d0012042480c0250005400521000c1c503600200010400700c3d0b4040d02d00e40003890000110006400019555 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 271146915 1250 271145665 271145683
    0x12060f0515100f050f090111070303181403031206030f0a061406030d05040603020703090504060e0402040b061e0c10060e09120f04030303090f02041e0f0509031207020c0d0c1502 78
    0x104d40305020040e81d1074190005050004418101000d10503101084a800c107401d40d0800c40110b034078100a04030030003a038801040900082d000c0c40200c2201180041d5407030042d8548940161103510015006440c02e022038201c0c400302004072a8400f07058a00400548007803c045825041c0c3c45001482c50701d400110440c141c900c0c1d0700c45500d840d0420604074042d5115040540c14421400b0f0b0005541d02e80d441100c00070100403481c03604505081c81080b080c1c5180e080c00c94402c42e020702c159109101300d0303e00300c1741000e40c1242c0705583c1c0b807110303107590b0422141202644040d40381840000e5000d804242d0b0902c92007890090b10956820801000720030700030079048181000f03007480b0600002e4040d50040155502400520810b4881640000c0c15950b4841031850300821074400c4207801d4845003e90b0000010314803060160f4681139400e16524081c1c00c0981041e101900701052501d4028480410404c4016003130a001c0d400038280902085030b103105050502c401004280ca0b220b20200304444c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 271148165 1250 271146915 271146917
    0x20a0b0d021b2415030a0c2103020c0d060e0d02030901020f0a0308040b06040207140c0f0d021003090c031a22052508010e071d0c0412060f0515100f 65
    0x51032425255083d00c08400100f460680c84006040700c07a4503901003201c0605917206a401d155410b05040041d0000b07008802d00c5c99035010001342403400a900483d48040400c4256840c106002c05070504901502248460340864018030b4400804642d012005010742c0d10300781c085868080d508650503a484403034020290000b40d040d0003160008481ca600d0302c1e004400100050b0030800c090729604c5203100400183c0000e41d200c800b010096086c200710002d40d54038102d0340d8a243d03590f43d401041540100812080400d0381e6440c151040082c1707103010030003441d002840000c1e03e4482200814000005442e0030080401d003060039413521a01d004170342000c65001010f044128100d0a4807010b21000366000030b03080103141c40102d010b113002d21071000c01007030100003003a08616000c81c103400283c1c030449410368200540d0810030301c04070f09422136048030f52681c809500c032451424404010007803402852a61410031003840720301c2412900d15140e2140072030f40094010882901030340e404c0400c080302c070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 271149415 1250 271148165 271148203
    0x90306010e1006050a2109030f0207030b060d020a030c080309011824021c05040e010806010b071101020709050103060e010b100c0311070f08070e0f04030912020a0b0d021b 75
    0xf10160b0b1084024201200242c10304903c1c00041041581640640c035045607460303603845801006040e803169811b1140e4040740003510343c544c2151100715031040c000301094064590f8034110000c64450010480081d078001a888540a0301c1f100381395100e43c48803008a00140421030310414408a00003407401315080c11010b5903c03059404041882164101c0303103001980159003104072031f00000710340b081031040c00d66109940c1e2818942c000d600000e060308042c405a12802c0107104007000d074800c4410464101d00e04d40189446040100e15203041904460704850400c40000300704203a03504112880e8010b08002e000500002d03080c000106400e42d040c0000440f6000b8100c082800348211140b01c0841106a40302182c136441c282942c24a1030303019810302e90259200300404001c0e608001e41102849440e0542410240c6000b0003c42d40e50050765030101d01ca183c0e003c11580c40052907030003080c11a054640302c24065020f24000d400000701c10142609000101c6960080450030b54406a8002001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 271150665 1250 271149415 271149419
    0x30a15050604140409061814071a03040501020415030e0c040504030905040e0a020301020a08040c080601050a03020628020c0f0f090f130807060614090f0a020a05040b040b090306010e10 81
    0x10301d034807985915001a83d4211142c0454428002c01f210002a5800079005408528140969401102c8846415000183c00340040d007954002c18480b034007056112038903900ca50070058020301c121f600441940c551007a0b1610323100c1d01508118440b280e001d05407050300072850184015603004640c01000a441584140054507290307201807180c0b90032504480500a040c0d020030f08a0740b1400414021078054420001081144c0d00071b203024144c400094101c551412002c540d40e1151030200920a040100d000311906d90300c4004d10307521821806040000b0508520042d4031100f15a42c1e1601440100c0b01061b001e09241c00284004c1101522040c5540e9403c0c0034001d40e55406000031182e820a14408000310740d1400141c01c0060003160001260742c9410b690903850ac03184002c06000d08011810000f00003c03040d0b280e035020b49141c4000d42d40304215042101c59101c0d613084047c0051000c10301081440c800406450010000c0e0b049680c16601e82c41214400101154144010300c001c000c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 271151915 1250 271150665 271150679
    0xb10080412120e01090b0615040305150402010302091806040606020309031009080403020312030115030e030d0e0c0a1214070503030a0f030212160f0305060a05010818030f030a15050604 81
    0x1165410103201000022001c203d01a141c0c01d4810181090750240c1250051250354940120404134103080c10b0a103924141c69560f9494413441c0c414403c03484001050700050a5901940449041c490010900c81044805409003040f2007000d0320480d00880c9402804908240008102c558886009004000a200d2001d400010b130422a5013102d2200052000100585041000c1d83e61001d06d20a1603031258100800360540300c100c008200708250030000442682c010100c1141c0200b00f0704800400c2d10040350031034900d080791000b00d854028a0301480028078996488104130201d00c81c0f600306610542c0ba00c01659140744601509606410400c00391800038022602410b50150070b08001d410203e02022500c0805021203903001501004032504244c02e80c0700d1000740000c4690306082000b0306000d408604012424000c950620400ca0041030a0144040f0b2000e0a15a0300040342e548182d6125040001c1c4c005581c14a201c506102440442030905078962080e10741c050200790030180b510700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 271153165 1250 271151915 271151927
    0xc080a11062a070203010603080a08010311010503041a090a050601090f0f050c041e090c0f0315030b160302040b030907060801080a022d0d0b092107060507020f030a02010b10080412 79
    0xc030480c1d05d0340d07903580c002001031303070401c090a15001d1684400c041503240d41403000542c0410b0342042d040107420020000066604001d03a03450061900a410b91681c800c094240b41920380740000e40035100d28000002c0300c100d140c02c004240a080f02c3c080c400c0c00400c032814010346800f550301c900c5c07910080c402403015200000d8136500500443c050b10269640c2e540c121000c07100305041d8540025184050103c040c1d400d4000c20f640c03c2d21020004810038034680700d02440e00006042104071340d034a91201c0c40d0051094043d14041c041c1c861042c0e07035906000c10360f02d584801911840020032050800020108004226091881d030094142e061000c02c0300c50314803204040c402d0800c0c0d54a02800c01e60b0700d540b11045070b09041846a104140981009001780b407810340700149000003424051030005044072020182ca074251b40c000c0000c501512000760a0341807000d4094030100900c808076186240030b905404c182c94400084d07035980c450000384602100c0066080740c016040c420b0701192a064944911 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 271154415 1250 271153165 271153177
    0xe031e070507091104090908090a060503060915031018050609030c1015080d02072103172a03010501080a0506011b051608070e070c020306040b06010c080a11062a 71
    0x403001d511702925140f01d0411200341484c2070340d200d100415003203001c2c14401840e101800460a0050461404c07500140c404000140034580b0f07640e03a4290154551020407681d0f0039480082d03400d0200711507032400c80c0e04a10030103006a40c0c92140d2804684116000300c00c40d543c0920060140c89803414504124002d0302c08081500031603c4031a100140080060091140c104103035806002200d140254242002c9824424004400380e940c0c44500000e0b08520000d680e03800200c0041c45940d1440c024882c0c0b80c2c11003004820700642c0000f41c006080c200070080d8140c5200340c84420254507000103101c21201c0c1192a1404602e807500c14441610f41c17183d541c1c880034499001ca41703190800c1caa1100300d0181540c00018103512040040c01044400b00c0a5580202c0c81c0c50701c54041400782e00040e90352400540040c00c08240c440210704164410a904403e990f00b2600340c42e40e4100d505001030a02d54002490b5086000d00c4010500700c00c5442004158088859170100005041403030301d408a074000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 271155665 1250 271154415 271154441
    0xa0b03150409030f02011d2d0613120c0b0406051005060c0d02071e06110102160c150804020618061b06040c0e09100c050d0e031e07050709 61
    0x3022804505603075034064031144a01c2640c130408408050003010303096420080c200c0c1022400c80703180c0a002c840c009000101c200056580840a103010890ba4484506c000d201e400c480c001d40e01040080c0300b5403d078510129102c3c82040c8404c03291aa82190f45a04081c07004040c09406c6010074003040c030a410480c0c00c10714280d0014515950741c07000480b16030005010f031030700ea003210b000c034500c090301409403e00a0001c1d01c9040e41e4102d0340c03403808a002000d80241024084604062003400f40e095040d2102e14044191800000015080c1941c84040328400c440c884000100032841c034910405006001d079034040c20042c10483c00d01d00703000868090202c100d80040c403e101c1c42000304075800312803c00400c2030010b8516410701f403d01290300e0140b60840344600500c0b10034000841c5001500c290740100700300000550100c04041201c00303100e4600c1207040700d0700307281614103521004402041c00c07c900c14206826091070304400701050141410240403038001100c2080544001d0304009540e40c00c1e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 271156915 1250 271155665 271155691
    0x1203030f391303030306091505060706020a0c050a0614160c0201030c1205010b030405010b030a0f021c0b040b0105010906021902040203060a031205120f04022101020d1811040204050a0b03 82
    0x1950301c1c0d410b025582c01540040d444950400030050079105520750030344910031042e507580c02e200109840c0c0c13194100042c64140d001a05140031441740d001d0420081c3e0140a5500b5803005081010152141d1262034108550460124000c042070301c3d0480c2c80c6583c04e07120360354101404e8005400800080341040d080c0f043c9503d899155072000d209a9010304088c246403520b83c10503092403800c44181061a60007a0700038100000070030380d12400e030703803081d513048a203501d0910700c04a0040d240c4c03003500c000400010f01e01b024041081500503905050700c80c21b99402c00480c1d61084100d81d0b4440c103010303c5003d55140030f0020094282074000b107030b002c000070300707039a44003547d903a6050071800d041e0080d5030010303a0206182610105030003205400000d00145d42d0250300307003078000503865900024810020031540350005000b0001f07405403110b800c0100e8040241c0110007808200181420307c081f648203801c00c48a000d01d190a00c261815100c02500c0540d00505040c110501c0da0720180c45514002c0e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 271158165 1250 271156915 271156927
    0x15010915032d061707030206030109050a09020607060e010506190608061f0c060606181502010b030f150130030e1f110a02060901030f0204051203030f39 67
    0x10a022100d48021442d0030005000c0c0d01d01040780454601d030700680c51260308102e40400150342c03500180d038195159010001100d4076410003600042003510b85c0250800700c0442c03048280140ba074411045030744c10000a000b596189000c0207007180801e243d240d061b408000c1e050001611a881b00d82c0c0c0b050000d0141c0042e0111202c00c10324160700c02c000180096902c060090400426000700f0000340500e0418060072030050b03c0c001000c200a0103109083ca100048481c5610720035044505540805000e42d01c2104400783d1140d1114103020f0a500103020b284c0000400e00c14821452181001041e0380b030344a03900104100b4a03013495084140e007000b9491040750381c2c0350399007814014a1038803035812002e610034248015100c10f000781e041c01c4075038200003016409625560700301c60103103c00b481d0001d41e000e42e034400a0000d01940c1c000c250451104044a01c0340c1c440040158084d072145260340c00c503130f074885505641241d24600300310902e0006002514018840c000d40709071440641550130700b481 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 271159415 1250 271158165 271158221
    0x904061805041703011203050306030a060f0506210a030f02101a09010501020a050a02040f0f06030501090201140a0207060507030908060f1008070509150307031403031501091503 78
    0x219014012100ca0740c40007840100031203107101450b4140d074158054103661510340f0f4115200d840c840081c05001c00040091026903040c005540c205c0c1d48090200310101c54440c0c802c00070302e01140e040f8090ba208035001d031103010f82c180402d04190101c0005101c19025554201c80b00d091004038201584214444002c2c7d034084e501503003500c901107074909001480184100006000c040e8407060654202c0080f00022620103d03a80004030f80645004c21807401414000b070003000624800754034980744c420048104a4190080804103000740d83d424103038513110391102c10502c107416422015a1201c0300030001c480c065400303094424001d0500c60151507903010090300341a4200da651010a440408200b8880c1441800d1307400b400c11040204005800d00001c5141d040c000342081c00504803d1071501038175a82008a0030142d60b020707a0301c20040d92400c071050f641e504241c5e03da800d008003e05d807400e85944502520030803074010382003402280d80c1d00402a00100203520003414050302c024040c080f88 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 271160665 1250 271159415 271159439
    0x50301201b0609010b150901082725050612070c03020309060c010516050426100e03030703050606030c0405300304031709090402120f0a081206010206071202090406 72
    0xa0303c001c8001081e449000c9040103c2c600642c00040307800321051102e070a9990f0b000803a15401550030040d5405107030340c502030100007101406540158071540744e0644a002580414a070035040c0f060f0200c20650f210003c01c00c0500442c01040d40017010b007400140214401c0e582d00398014000e0050781d10b4221440c01042c810760100049030041d81d101e00920503004000c3d41400b0300203c03a89055400c0900707200c584011404094410038480d1010160518265000d1110a0481010710010840001c448030b00c640c413508126051400700385400001801410030004aa20a051000100d07150900704810004051307801c4154980660100c5142d9848011043c2c200c041c400da150010f649441c611318051a1844c0c0310019624a040144103900050b2210100c01c1c2c0c03c24ce04641c0030b80c1c14014000d1552514130680991541d80c0b245120b101c040c400700b0070040c0b009266030210054556200c20042e41d88110542301d010015140401200c005000c0d503002d448583c0008102007074150741c0340408100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 271161915 1250 271160665 271160671
    0x90d0606060e03150604090203100f050708130f0f1a0a0519200c0f0601120c2702030a151d0618040209070e0301020a1701050301201b06 60
    0x8196035a203091192541210008103001c1045004041100383d10130008006034000d40400d00941e100c55811b800c568040c402511041043c60302044411080e68100c8083c003015611072020401d0381d40401c842d5070100305a4020719070400c00c1e40351601e445584080f59075664480c1940c1f0440208100408a50300300e841d640103031800c110115030707814200c0e10381010b604c4a2000300c4000e0b240c40403001000c8240c0541e1071080035604a501d49540c292426141045480152104503004080000c21000b20266104030399900441d15602440d803108590305001826104200f410a040b040d0206029640d40003117a01500b40074001ca0032514928401114580507013112050f101d00c071640403890641110419403001040b84e080340505055400b400c649203014102900424030200000c0d00a4028000d1001d01d110150007159690030440c401807080d5002c46c0c1c040321401d8106c2c000182e0785414012144d03000400d05204c03c0804980031011100d90007150952030f180c0c4021254890704100f03101c0c4600c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 271163165 1250 271161915 271161923
    0xf05070807030e030613020906210d0309050709090b06090a0609060308040e16050a08040f170307110c01021906090c1214070605030703050403020f0304081e0102070201050a14090d 79
    0x1c0c10040c20205410004001d1408106c201000400405a580e01c54601e4001c00180c5614080884040200f081c41c0c100c100316159920035600100e564952542c40854003502034016581c605444000d204240c03188002d01414019804010030400d02c4d0029640b6000310034103400103003407070751403240000703407202a84180e0726504c011030100030900b5943c855981c041c4100601510780380014002410a000748034001080240400000b810001d541c800c00103060341040c800000c2c41c524034800000d660044541600040c074150302c200103504006404034092030141c000c0d0000141e00c5444143e104031000f019610309803181444400300b0070500801300038244041c03040d80001c84508000c407051800c045c01406a40c4a150708000c5a41d210342a280c001c80c40307260205081d1240d0a003245001c1001005a065000000300003914200018001400d410120f9454424010149ca03070b500700e00030004040e0224004010601c0d40e036110305003c84488040c204c00c0e40c02d102c0c00e81301041e08403031140401c075 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 271164415 1250 271163165 271163177
    0x10c050d05130f03050310050d0b06030c121c2f12040303090611031b0d02010b0307030b0a0e100e074403160b10050102120a0f0507080703 61
    0x4040112802101d03400503041014141100881c0c2c2d9160101c40d403c40003400300301e004004145004075805c101802800000c0c240e1044d0780d201d0403e10402c6200f40d078414481d1240900b0050306080446000300001c0d5610045c02080040c1d524050500260301500e17010400c0c40303003500f4810001a00c5041001c1004240302c001030016042491500b021000f00c800360000c24002000000e500860541c00d40d405c41c43c3c8522010441048070b0f10350301501e44401462507191646011410780000e8803008e1083c0c542c000d001040205043c103442d0395031800040c0c10482039200050000c0c10642090001000c0c0d801151103c0e607080e03400b801103c2c00c0150000c0240c00403038003003001c02842030f04012030030201031501c400c80008451001d61028441c002d0201381e003280100c4400e5183c180240c0f154480421140001c2008914203030f0300d8120226004000d400d00b5450100d040d510029500e42480c0c4004c190785d2030145002d400b5901184c1c1e0184010400408000340300010b0b06945c05020041c0c0b203603c1702 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 271165665 1250 271164415 271164427
    0x20c010e1207210f111c050d0507110909010b090604090503030105271810050c030402040c02190c08010f05040b0f060a1205100606030b060d02030606042103020f0a0308012105010c05 80
    0x4d10030041c6c1c440d4110340000d0010940c0070500c0825501011070f0745080c5039035241940d1400040c0c0e21182c0b521980e02c50038510410480c128190080602c110b400c1318450b035103a03500d02c1040304540c2d0100000c0c1c03450b401840180880e040000030845010710500f09a202d1031805444244406021500424404043e8003030441c0d400c8104449042c03800300703d40038000340c5801040324496020084c40a0720480e00e078842a43c42d64003e220321400c0380d41100c011107615509051010301a0030500c1144019803030442095200140351240701d018651003100d040082d02c886101840c0440c020744401c1c2d029841d208001450103505480e0080b962107203010703009036060302c0140c0e030884555600640c103041c01c041280240c0c0da5a0821201884006900107844e91141004101c06000d9030b0491010401d010206402540340302d490b0000244c031a82c00c4680100960030340c02d4842c901414000c01142002c001801106003407140c1c05200c11004c41d0450580030309490b0542904d45c11001900070840014403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 271166915 1250 271165665 271165669
    0x1206090e0a0308150906131509090c0e0105061b15011202030607090506031602011e151505030c0315090c03060a060203070b0103061806060303020c010e1207210f11 72
    0x310359001c00340e034019110241450011172a10803000b040b00d0b02c500e0489080007001d00041e801071f011800e0040207501020f45501c110f9000301482c03281136541685403400029421803240f0320390b058800103880c0600b031000840030302e03206803107000c0c010303016018036640da1300c41c2c4d0844038042d03000303104401c140216030590380141402c0c00710141c000b1003040028002030140b0340b107040c112034210010701180c03100503854090890040400040c006034103a403040c2100041e0145801c030145c0241115585401280d591003080758410f001424540420350900000b501b00b8039100240d40d0088070522000d1116500e0400500d040d40125110b070460704000c17080c02400e080080d20400070780349a000851030030400d0303121543c2801052100500340c5032269540c41c1100031b070740700060b02503900c61800d2142586920700a900c40d000340d004140001e402442c0c00701b0724585160758400c4a00207501600410b42441c120b507120000c8140c4000000a00e42072810015801041c080729007406000d6884401d030802c02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 271168165 1250 271166915 271166927
    0x1060e040203130b060d0204091203110c1f0f020307090e180a020607060e030a050c01050a02090d030c0512070f060b0402030f2212030f050a0c0e011206090e0a03 71
    0x20540e0085105000f0070940b10388a0106401003600240d402c4905da07598000240c02c9000392000075001414400341d007007001080c400422102009440034441303801a40c400701802c0c00355401c60841503111003100c040346444d072000005500c00890b408207462903e55600c0050b03034010b603070860014014081c1080505800c13804941c02403c01428034034481040004d02d5950070078801c01a03c61480041c4107010401d00b68041e165000d80300c81580e48580103031001904a03003110800007110350811000a16002151089640c0644000c0803c10b0801ca01d860803114040720726070403245440b0343d42200038a4441e0342e02915040c0c0c0b14160700b24010140b46008002c2d103124550580c011801407003404072049540c104a9402030082500c6910114020320190205210550241120f00d101d070000c841140d25410a03100c00d07c2412003444103490740101801298401c12f010b8000840c6040c1c5a00e15610440382c0500c2c007800301c03002148442d203503500a411168101050800d50b48011890410107401c14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 271169415 1250 271168165 271168187
    0x130c050609100813020307120b06011b0b07020709020327061003080c0a060c050304050c0a081c0306080d0c021003051b0a02010e0a1b0e22020a0b0a080106 68
    0x28400e0381c1081089800b01c0c0e010030198106905002c280b400194140c00c031400c9400d9244d400034112511981e84036248154818020b030161007203003280c00001c00c1c0b07502603c00502500c5c0200541c01d100107440c0c42d90480440c016041100318005c4810008060b00c03603001031402031a80c00b851181510b04110504440c8080c044220342940100007040722204810450008503030304000c2041d81d84103081025428000d801500816507403500c03066140d01035000001d1827245200d00c0885001c2e00307800c801c201c205440b62051302495404220b40c4240c040400e4160b06030342e4030300c1c04c000ca40b5030340ba80400390802600f0b0803c131001a0180001c20300b0740c90800b04036204402ca078141089a0705061000d05144240380003407001c40ca20009500d42014400d501c11356060391a0820303911191140d25240b010400c000d1a5502c0c2e45040100c081030802c802c01c0c615004040c0802e200141040c036524a00e000c400c654000d0307a0222240c2400601c0044042c0200300170709056880075043d40c10260040c009a40701 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 271170665 1250 271169415 271169419
    0x607231506030d050c070909080405040c1d060a110a0605090d0804030c030305070509120c0a05042708041205010c09090908120415060801050a0e150c0a050f03130c05 73
    0x80c0103054a011031243d045814502d040780e500c545010003145801d50913404424410300e060441c805121200d4094410790b00c0071602808805841603040b9031350403000b9044140340003803d40000c110b103042d10050807030405a05005901d5501c0a100e40d04102c2c1041003076800c65101e204012100c582400840f41316045420a103403642049d03140203000041e00240141455500e80200d5205070180e4182c40351201c00030100200301852403c4640c4414034a038400780030b02c030b01d09008130b070034541070040320303001c00400c1204265801c10701014000d0b00280141500c4e000e50800c00072a42d03210b40e080604d06a0f015000100e200d20458000034862401d5a1200c04180c1c5841500e400041c001c0c81203a0310040c0c1140c2440982d00c40c0e060a42041d9850702409012600c0d0040003d6003200640010344101e820600411040350b1101e19281c5845058132041e69420341d40001a039002140c4024050030101c1b0b1130401d003040c9034010301140c50307441664585480701e900c4044608101064034a08060001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 271171915 1250 271170665 271170703
    0x20a050d0f0507120e01060b041202010206090c0f040518030a08011508070f031e060609030b010b07022b120c0b100b0301260d050322080304020f060723 67
    0x420f60060000c1d4118038003001942c4c03210070440020400f5000f80c0054620307500d0b0700d42d49030359468601147d408614800c902601800000030008100410001c1100b04040c00600d0b40c01100300411004010040c040032071410846520218248100090001d0390955200c40d001541890703900d4404c42c5031092444c0401c010070041010b00780d44046c1010a010480c03d0210b0111000072034a54414042c000030750045217010f80000302c0e10f03803120801c802c0780d00038403952542ea41c0750b0049070700074815064041e411442c1242d002e90340c03039200b9205400d0f000051303501c201550510f42e15460031031011820300c00040e13003601620090000d60010a0b800203000d070400407140780350903181c2240e80414030a400b103817140d48682d04200300074600e09012100348a03082c0d03684c020321710760060007940068405680c0240419000c500c0700c41e25454504805410400450460b6141e908004220000e0080e00782c000f14180130702c2000034004010031070002c0e5121810400c4083d007a903140d18208026981c40880d1030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 271173165 1250 271171915 271171921
    0x3030c03040c080d1e0c0210020d030c020303010b09090c04030b01030b011502010c120b010e0307090c0f1b0213020909100303030c020703020901053d03140c031315020a050d0f05 78
    0x14200f8007040380d09145d0345506140c3c3c0f004072001c0da0784a81417803019400007580f416022a4582c00302d209002805a52010000060000f8040343e403800309000d10b030300c408010008810b40345045c005030f640c40700511a1581c41c250300ea9444500c5c3c0c200a030f20440e40c030401c44005000c0b010b05c03c00101c5035200303d031008201035828050020803009012480c0340032641d5500d0b04040c00e901c02d08000000c484040e0031074620a5891580900526402c3c0c0c080000030310803041d058105100d101505542001c403001407103200429000c008805052190300c1c8203199007000508050344902d403140c0e02c035582621403010070034610304001d019035200484070011034001d214180700590b1004e00180c10741e1810f503000b42e100b168454001c441c0b994030408402c1d00810624803044500d9112100054015031070781c3c02d10110603001c0280512120984041d900c1c40700c1800018034240a14240d182041c0c002c90359a0790200c20310030814200c0e03000380c0e41000022030014001c82d02840034060190f00c00111b44080100d89 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 271174415 1250 271173165 271173167
    0xf050c030f100b1e1e0d030c1a04030801140415091b0e060a0e030f010527120a0309051e0304050f06031b131a040513051015030e03030c03040c080d 65
    0x144201d00042d209060300580007405214460889145d07100140014820400c1410094118951386408407442140d090303008000d00014445580500e505449280740c5034200f107680d021400075003000b281c00542c0e49012900c40303404440080c004140c09240090039944240d9000c0c1000d03644441d00c0c060002c92800c0540d242c40e804101c0d500d1010034036145001a081c140000c4c24003030b0305903c91890b50f00305018820441c01064400003280c00c0c3c0b00803280103006002d0b20360b1f11000720502e240305018041c03110b040c800e0b000790400340e0007038415010340718964946810400020b00c03810070000725600100741800b03a410b058014401c00841150042d05500c0c108201c94150141d24115850002c0c02242d00c80007655208105405000d2019810000305000210742c40c0c03540040c070070b0340d02c124141e00c82e004540115105482c003c0c0c0302400301045903400d03d07031141011000c0038444000c055907a45e148800003020b001440c0a004514001903a905103803c285c061580e0f01d40003070390b098020700d104400312 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 271175665 1250 271174415 271174459
    0x709050a0b090406030c140a080f070303030c0c021306060e01020a051009140a0303020304020f04022703070810020307020d41030a050a05090a0f0f050c030f100b 71
    0x489404000d81d03901d09100300494094213a07079000400300b0030202d802052103214000742e200c403100291007903000b040e40c0d0380d02141d036941a540c60540540055205001080c440d0308600c02a041c60b04203d01c00102c59804900782820003509418416525101404003da01c86058000d03410244000d14a80384251601c0c2d885000400650f001a50365070301c80002c008042d2600c2e81004142e0301610040070039810050b0203984100c400300e11600d0701d9901c1c2074407444c2078030a50b0b00b0401c2160300306800b10700d03854454040207204030405d0390510503006c0015408204107c04043c0c50301c40c0001580740e0400c568040d14150507503183d0414040800341a807290b00c10441c1a51020f00848540004880621007070414484181c1101c01c1515001007084240031071600034074051011120108942e03070391303425201c2d1141055140200606000342410003c10100c3d00407481c418000c100340c43c80b8070358180000e8075000c031015008550780c2228403508102e0340030388920040e41a00b6210030080041e410403000e51 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 271176915 1250 271175665 271175669
    0x703051804060b07061a060c031813020c01061401050a050a030207032610052202070203030c0105041514010b0702060a2109061802030c10022805060709050a 69
    0x118000204400d07552103030440e000422240b8a12940c1c0c10040c05d0460141a21001c1054092040030a903615418100201c80f03040c400c4801650900000c000c100d01450030040398030742d1220b11051015005003151004109810b107031000001c11901c0d0905040e62100040c12450502c64213120f120303003052b000001c803421140240b50040e5174600078034054840364040d10480110b448201c010407200840c01c00c1e0180540604865143e508e0750b0382040014010041c0306905050b164125000f1078401d0310f80140ca01240b00600362030a100407541104c3c2103038022a800c0d601144080c0c1640e41d907150610580700381070301186801c40d8541c100083c0070090b00c28113500a00030000001c110716214810001030700428101114041e2203900c80c40600c0191000d083c00b550498a400740b1481c00300d4070443d5249165501402801c1003003002420002040130040c400d00a502448104104103c1400d540c1b0829480c0001d83c420523560a0500c6460100020114018030824400034000381c2e68501101c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 271178165 1250 271176915 271176937
    0x1507020612040c1a0c060603010606141605101b0903030206180a0b0c1b0f060106080c070c0605070c060804020a0302130b03100204080105060d0f020f0604180e12070305 74
    0x201c1c1d4a41d850180c0e071600e9580d00841201d14090300c03007403c1d250b84000400f040c1604404403207030394030f4403010503003280e60034400c071004120442d00108000d43c50b4005814042040d19009680005e01d444290030004001d6a652070180c0c0d404100f40303030101040d4a600038074424501245480d041d9034000e503407040701070203048650038000c070110802c907810004003501c1d661150018142d4140301864841540001e41c10034003284055003d02c64a001c0012180c0c0880a11001010643d02e4171501395601c51000c0c00588140c24100b104001107004054118001c0c40d0030b5940c0c690f80c0f032441c20407041d0500720380c01603801c108140b8144030250b60340b0003500c41541d8044840b8042180726984900c010071b4004241e58250183d0500380c03d0340013540e40036000b15401d0030001c3c000c0e5a1190104001c2c5251594001e0690200b01902005400c10034100d81602d07074068001403400b034640c4a17244500c01c1c045200040c440c0c40e160300d400100001d203c0c2c9a0500c3c0300e0001907041184950b00504507018003c107040b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 271179415 1250 271178165 271178197
    0x9030304151733061b07080a2312040b041a0301060c031107050a0e0f0c0a050301090f090f08091002010b21010605060f0307020d051305040e1e0a0215070206 69
    0xf850102c8800a501d589100101081d5031001e90007444c0f410001e290b100f100050080c4c240c00111590301050300907285030300c81c0c1258544e045505804400721914082c054203481001004008609200300a001a00081c0e9980741c40f1844c00711039601850000030884180d40042c0010080d19070861201110141d050500c0c5401d00c01b6480c0181ca0303c020703544000c0d401130307050360001401248040d0060184010746070200751030340c0d459440351152060618120008004000400545250b03902c91590140e0704d042c0410080c0b030980742d6040c04c020448060700d0804000070018800c0ca01180c0f4038140c0d044500007444a10150300c00106c83c003012855040303602103448801703040e514082d40b011001c2c140c010803143c0c886190b03510b08030003034008440d207a01510608541d5a0701d54001c4c3c003034850254055143d0149503007132005000180011922403240d6100c0c5840d800d20305089075528000001c0070348000c1001e42c0480c010001034080041c820030f0400400c00c17602e405030300d8a00807900561400180c030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 271180665 1250 271179415 271179481
    0xa05060406060c022202031006020f010903020d081b03010b03220203030f0f0403060c020a020a0602010b0312071109040809040c0327020102030714060a051f1a090303041517 76
    0x8001700e03400e000f01130880b8800020020601e241000410560380a9421035019401000441d42200d01e15030000c0d01507444126040042c03031258178035541c003100341d22103c48147ea07801c200d034110390070a802640008001000300100c900ca900d900007909071090000560420280d0086600ca1052322448800460000307482c018440c40d0500701c030025540f1034802c004038403000b03000944505043e03204070320420503242e0010305103205000c0d00117003800050240c05038102030315044a0a41c40f05204680003915800c00204a60740c41910611560007203036503640e0b0784034900401081f1060141d003981407601c0c040b04181c0c56582c200700d0610240901850107100501800181d1841c001c4050042c1070082d0300690b000c06800100b50745005494522080c0600d455848400401d0141841281856096172508014228080344c00e04800c0383c5000b005403421415030086800e5902c96013144c0050300c5412420a89190f100044c001c411164080b481071a0034108a50310050b41841c02d0190403014203007003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 271181915 1250 271180665 271180699
    0x210b010b03090a1704050108090304060f0c03030b12151806130305041206060302090c0f070209041119030c050a081509070b03011410030c05090915040509060a05060406060c02 77
    0xc8140000e401408400654500c416903902e40c0d8098055640023804010200d04e0703040300041900c09444030364940030f074241c4840e02c6c1254a40c0c10075400f6002c16451395040000b1b620b035074010081004440c0301421001146141b034607440e6030090321000d0042ca0705140c0094007480400e03030541001c451440c899141d0030900f0704403030318020303038109080c420003250444041000d1a0321101c1200d1007070741c1d12032240e41c0300e050040040c01510403032800341204014800040c03034441440c5030321138070500c1c0744500c1d51070382404195072503d59060f141c58901c0b60001403040c481c62031800c000501c000c85503180114100318102e07856015104110800304044800320700d80714000d210740c40c090003d48500302d4496030f65504050304030000601c003d00030b229022915100030702c00d020b0a6603051b40e03600c030740d441c001d64001404600900207100400541c44107407500c14550365030007080c2c0214200402468603090000c601d2040b110058032a030301c224500364042242c1500a000400220380450390140e06900d5181 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 271183165 1250 271181915 271181923
    0x70b15043218071202060c0d020f160608010303030f1d032d0f0304080405091005040c020105010b030c0f0c060a0603121716020c03010912090501050f161a0103050601210b010b0309 79
    0x3d042c04a0048c481d490300869800039540010155550440f0203036081c2c050050591050341c018070f40040c410900500c01b1a010703070001041c0c1c8800c0703a00005e1622900c01103502403070f200071105196401c0001d540c08000034858042d0203822260500e4403103e4981041d170b003c1e5215000b00c07143c2030394000c4005803c0c824040d050710001c000191841c2030710701d800030000a070503002d40161741c070580c0b8001000017004d20501c2214144c4248980c0240344d0f44850320348200300c1d0820300c4203143c80300b000c0048640b05102840014040e040036a4041496802c510348010043e002801d500c040281080d030700a0406004c118181c0c000261012a440ea582590401c906160a003010160598201140c9100b04508640544261400360391003101c0300b900c81c80119443e12481503190704696050241200c07489a01e90f0551030648205035003c40c9075215248501da542091b80f065440740c10690042100d821212004244d000f0450703440340c0f41c5003080d581e0030080c00040c0500000400e0100c001204010104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 271184415 1250 271183165 271183177
    0x1e090a2301060203040e011d07110a0602070c05040e0f0d0c0201110a0f06060b09030c060a0324030c0e07080f0c1b0615010203070b1504321807120206 66
    0x328038080e5075a15a080a5500c0c0d010340300c0c413030b060100c1c0c03030000465440380a05c04c02100d842e101d41c038965803503100b0111010171100600001c1c074010807103003d001460f2840201070540c89404d01408c0740f860207080004481e04c1b0341000e17a59802052050759241404101c0440c07515440c103000400140760300040729116941e05681d005446422054802d01034118002010346215220a02c81951075a600c1c0e00c1c94016600200e80550059507520450310b0102d0240042041d5460005546c1c5a00031005006082d40f41499003d90315000b02401407100211200c0d01400c131031515039546080074600100f01042c000c02d000840700ea58000724020803e080c0c11501c409910143c00196141c0c02c180043d11910240c0d14403c921803000303007030700b61540080240e594003904060248125519510703000b500300e091048455006555100b69000c0301303c2d41c007018a0030341600302c82d003801c1421000384021456000d031074002000c009442e840c3c02c9560000740b0b00b050360040d0714101c0c2c1c0b1b0750b4944007107010f6000306 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 271185665 1250 271184415 271184471
    0x60509010b0a060507021f0219080f130609080a08040b09031c050d140403050a050f0403023a0507060c05010207021806031c09090e0313030c051e090a 66
    0x4800c000340659000b03010b0300c1171314000c1318031140c10780001540c2e50030032603214901000b40e00802ca024440d010144103903600c0901070014540b42c0320303002584021944c020f11a81c452000c821106000c11130348046e00c0b00103000074100034224910a40c0b5080c82c00d004034801d0248000000480c81d406071410300050301103517450480704992060340c00b0060440d42003150340c510740391b01e410794151101815800c0c040c01541c043d00d501d031400c0c3c082ca00882d2240d010b48051070900c9400c000c0000186c4904c1d071214440b0b2117500d82081900e04290b000700d501c0240b200031400801d151041f50002c224045041421206030b03060840900f9941d180040c060701526034003a41c440d1030151909c2c2c08548141429204001c11403d68411444100d01440134607004941c0030300080c2c144800384078800380d0741c0c00799425261260450781001010782c0c0c00c94119500c0d42040720300f2200804100318900f480d181e0740407551064030540f04601503074000b0882c020300040c944240e954503081400310170314151103840d07482c400b8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 271186915 1250 271185665 271185679
    0x1b01140406050a0f09020d11120f0304090f05070f0806151309060512030a1d03060a0c030605040209011403130f030e0f0616261b0d030504020d060509010b 68
    0x82810008010501107501c10059420200c2d0b40c0c5250313016205040803d58000c0102c40c02d203450b500c90742038240001c05215000685001e403110038040401201d20a504440001c42c0e4550034004071009072941c443d440810b09084c4810b00c010a40c010344504503100d4207140c4490240d40b01000540c801000480785801e0440029070f5004000c40180641c0030358841c0e540511129540301e0900c21000c03e00300000c0c01c40d4006000307280c1500c1c4606c40803804400c404a00c2070050346000000b90031b000e81a40c04850350340d5a0000c800d6a03036050700a41006000440f411800c05c00a5400a080c03d46060f06070002032000000150210945501828007240c000f082c00111000500e00649800e601d0038145108031402600a0042e151140888100c5980d900e0a5924010a6611605003000d4650703000d4440d0081102c00c002204214094543c100c1c807810301c01e09582d0040b03070301c0b41081d607404100020107040404020250712401891030040c0d17400000004c0b0395079141d0500340100035124195600c000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 271188165 1250 271186915 271186921
    0xf020c01020415080105061c09152918100b040b130906030f021c05030c0d0806090906011a0c0a0f140601060206010939231b0114 57
    0x154041d00c10348800d144000c50f0038400307400c2650011002d02c5400d91101c0d08002d0aa400e00a080364610301d0480008041982c0b5070b1666048003100e201c0e6505040596500481e0200140c60849076813000c1600c1590401d2131030040115600386002400004030b640c080c0d000c81c0b11188070450100c002c222100e0403580301c0d40c40320380118150703004000d1441445010400410350f02c03014865002103c0c3d01010750903600c242c95081c805909440628101d00315444a10f540105505000a19540d45414064450007000001c041c0c40550003800c068003a48040c41080740c0300d00000f0f856410342d014480b41c0c003140010040c9000d214031803081044090f0045035000c008101e018848840d50501c00c1d40c0c40f01c02404094401030b61400d00344904001a40194010450303401c01307501000d04202c5480304c80c01d04661092a201d00455598000c0000d030450441242e00554022006d07400b040c007881d6244040c01000005000d20302540e0790580c00400070b061b450850940c00d6111005005554080124078a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 271189415 1250 271188165 271188187
    0x14071d032b020c06070201080613060b0c0f0f0c01081f0902030114030a0b040b070509180901110c15072106050301151a030a06050a080d020d0e010806130f02 69
    0x4807001d0310404012040d21001180d0001c14004442400605524200b0399203400440d5010000b6100d141c000f0985041d92800e4407250103a800500200b00c1c42d1940d408103075012601e0514407071072207c000c0d040345450032554400032a8454689100b460720700125140c01c0a000021071509401e25617a00c07010100145107030498010394100c403020f641e003e042000010a145d03d40f50702c1400140a001d00384001000a12603800c40c0707801c98520300e0414104410b0701c1c04614401507411042c0100301c403000411200060034020034034801e441601f114100551144020f42d01d5444c450180a140c44880000d00a94452241c8204054141c282944143c1034085000020281401198029400e02c2694002103020041c0507040780ca500740100c122465040c20100c403500050300040c109521a0b00019440c0c0c0c482c22442c019000b205c0140c0024581c2d100083c1c0b03003044105102041c007000c0d0b0148201a80c1000485a2000c020f58401c8100d00032034002c84010845010845001803012030295021 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 271190665 1250 271189415 271189453
    0xc0506070c08030313060501270e07120c0e0601030209060d0f0f180302070b1819031a0708101d040507090507020f01150f0312020f0303071d0414071d03 67
    0x290103811b08103e1070762503d982141340784000710418881c0c81d001c0f0b408040c0c00c0c3e60340d04c42c1d0102520901030300c142a4480c01030b101e01103207804040e140185820000d01844100300b840c02e40024090a00314503004034003000c542c550160403400b03580b15079501401c2c60742c1d0007180c01c5900000706842040050304c0d071541d88c00803c1e90008a0540041c4540200402d00d20700f0881101c0340403d8043e0188000e00301141044150804048900705400b901c3e640000010180041841d210140c2040714140b0b06c2c25010007003082100602d5400034110031903080054608807400243c80250400c0100c9050b552410703e2441c01c0c4880c0d0061000b5440d0200b003019440c1d010511020440401c0d0003803100b10142003007005280000e014640343c040d8400801c0000500e0a541c040b102c400f6401510414a8007054041c01c5030001c440c248041150b84007a07103c02100034944082050040301c04005685400c04e6541107a5401800d04080c40008909022207134418403910681070302c01001c543d01000c4c0c03072519482e9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 271191915 1250 271190665 271190701
    0xb09100806070f0225030f050706020d0e09130602070c060201020408010b0901080c060a020709051512030a020d0503090c061602010e030708060615090603070306170102070c0506070c080303 83
    0x3030381c0646004904194458003806200407aa903009000c2110040d8020352402e0750003103000e4900d980d08800000007400110391084080c040c9010b003810a2420502a06001d10825440c042081082d031000d0b40f5920b0b4000c0382d81244114480f041900b4991a204009110b180005490300501c048006030140d4150000c20903201c6034402840100d612106001d44030354203005001c03286c4c0020b0300800140c00d010004d0244c1d01902e1040b1150304ea41c4655010442f40260785944444200182c010041c0c00c2030b03101c200458080e48015840c01031a450029150317103907404110208036000010507a400410820140c407200d0082c0b1031607070f0f0007a0f824215418042004124085982c03000400000e14012078900308455891001d061290303100c108102d0181c0c0c10220306501c12406012072000c80c1c50700700165108840903100007804c0e47c1420b098444542c400724007000310380c0c010052900052890b8180b04111b600650307505072074160503c0c20035181070282c3c000c15103a10002c410055030491031100304130 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 271193165 1250 271191915 271191929
    0xf0d201308011a0d020402160c03120806010504060f0804020103020d0e011401170a03050c01090c12030815130f020c1f060b041a1303020a270c0905060d0b0910 70
    0x300c015010082800c0f4124200d18036032180c2c44c000e03c43d0150170540c005007180e5100345164903c07050295244807500c503140c0c0056031140041000c88250b103400c40b034401c1c0c00031800d08156041c149050340c0108480700c602000c0d0300300840c600200d02164043c1d010741d01801c4002e83c06000c402e6000588500038440140500500005c580c00054258441400c440d41c14003620301070010540651000c1c1c03581e41c40125202003640d0b852054030f0110f034040103000003a180701a1484540041402d0003010614003415207001210384031410313100c03903031041010300d43c01da82060003043c03080304110100c3c001e001c2e000b280c00c0d032400b85030309514070a504074400e106900a2401c1c100551501c07903444100d2802107000e40c03182424619040201060743d00050301007500301045500e19281c4030303804914008029441480c03040449048a034a07125904200301c8103e11403081000440c01c40300d00189404954440c040c022100050314214503080307504520401d0b20041d01c10161418070746a01d4881c41481d205080b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 271194415 1250 271193165 271193171
    0xc180c020118051c090e0408030915010e130807140c10030203011211030102070c0b1801020c0303040302090414011b080603060f060402250602041401050f0d20130801 73
    0x4038110102d2200c041040c0c0c12078010000f070750009506404910120501006101056200003624a08048020310032440b66103019164201900d50f80d00d00303240741400548442411006000c0a0800404581d001040c0407805108583c035007402d815a01c03801c90060301d80e54054410710300300600080c076a0f07480d0343c0a59030141072803c051400c0f01240828003550382040c481740c05060104004891004403083c3c001e0006290410f01d41c1c0b2104c6024207580020181600070034481004c0d1010703254200207120a0003c0c240340c104101c00a17450344034030b0200900c10b040da4008130b014005c002c41c41d4060b208901000300007184030010b0400803110031286100006c0c0300704000503003e0402045190040d0105101c40c2410340740d00302003102a401c5100c45880001e00b01c0994142910b01c00120030720a0f0060000607919410041c0c84590602501d12081c18410104038140c1110140c0c002c0b5410480c001e04005404450714180c0c20018401d4a0409108100410b0402007403405682c1902254000c0c0c00030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 271195665 1250 271194415 271194431
    0x32f0f0d0c03090e0604020f0703020d0306170c190806070801080d140a0f0e04090602091504030302030d091a01060203031915030305071511130603180f0c180c0201 72
    0x11200c88400301da0040001e4452141004411101030b11660013440041000d800c10307428007100529a0002901039006030b0000c8900e6007501e8140c8501000341200001d44029001e145c807003144d49100481c0200c0c024490a0842d42582c1d40b500c44000107021240d003901d80b18184100010000802801803102c94005c5101c00398406009140e884051400c11a18505001800506984180b1441c5c69841400054500f02450380d07281c1c820380200c68840c1100584038000700090204440c0c545015004102c000c12043c070103c0d400000f0b803411256403400116a185407854481c102d88024031111a5000b400030000c030b02d140d0017001452045031410119601c2482c490304c440142d99003603120414611030b050301440820b02c1800104400d5014400e415000c1e0190400b84c401c41e031000c012048102000b20360300394200c248120081c018600d03460244414400700c805403a01a1100000810111032447d40c070b020000c5403040d10b0001d091080b201540b04444010b40740141a9080c600c60042d481c0400f4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 271196915 1250 271195665 271195667
    0x902130305060c1204150608160906120c0b0c0115060c06050f160f1b1202060c040518071e0801080111190f11030a180603021204032f0f0d 61
    0x1601c14010356813902c0c800a0703d440d20b0b103140a048842e0140714a83c1c80d02000301d0180340c100843d201d401c0b00310a40c0c10845140181a804944581d000000349440c806020400300744c10a510106413040e9043d00e0783d89845585049004150040c410034007503000440c00034107940c001040403000d07802141c05120380e0743c0d1105900d00300d0a0440e142004111b41903149422207200c0c3c2c501c041a84510306106e4000c3c070b2401c03d00180c00080303800880d07108065520201d0300c183c0c140440c44d002038600c1d0f5490704150a0400060711007044845a2a000140744009043e25214a018881304020544a6a01c40d4035006004140c00024001d2900660801e5581802504150204c4110425403510404040c59003c000c80c1d845c03413080050720401c101480a0003460380103000500c800c078141d443d0030422403681c85498801c500c45a000307200341441070041d00c40709440000126401681407400d2020214850302c04014805841c4405010710a028810745600c2c03c0040c0075400f030281c081c01c490201c01d400304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 271198165 1250 271196915 271196917
    0x7150507030809010506010c080901260106170f01120c120c03020306130803040b04050c0604080a0309060f020c3708061302030a3206150109080d14040902130305060c 73
    0x90031b20300103910200590045030078400a05041c07001450725026540c51140c106101200e000d0840851625a00040020641100302ca0071200505000c019151070100e0295100000503c1110b1000d40200c1340d410030407200f1310801c8040ccc520300458510142450a000c018004580022030280c032616010480c88242502000f60103580709240c40e00e5552a540c0b01c419001016204440030b2181c900c5007012642d83c40c000d4009002940000c0850990a040080003520365520078428002003088071504144c1c04a04000f080b003003a40c001e05080c190603c1528842c11313084100c114290104c042c0d1500000c918400401c40300005d0458949859410f07401aa1650804000b541035110400c9000041c8920300c1d10200030294481c050790134075200d558021041800907403801550070500400c903120b004074144070300d04030007845c10503412800c0c0388000b0350700c1c01001c245a0500840b50130350807107028030000f154054510f0400c1951034030500031110840d42c507a4001100c460240400007608504240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 271199415 1250 271198165 271198171
    0x1103060f0402161e3306150518090903040302030c371503051e0709140d020d030302030609070c05100b120f0606031207050304060e0102071505070308090105 69
    0x707189414510740d1680c0d103100c13030145410318801c41e2160b1010400842d0900240141460b4484660301c28a81d44001e00c81908042007288181d0f140362441c28841c1034103103491425220346a0600a50310900d90020348409200c540c9840d80c8402103408103c2e10610200c05001101e10a4003102c100b411040100101e14481d07040115400c001c4000300d910b0180030480403140302d4410480c114503162244601d010044031208074001180c0c80e0011f004507000d0803088880b0411881201255508041c01c0c002c21620041c81a852030101500d80014145c1d1402651000301c3d50003403003035017001311f68034014002e0341040380c042d80300d8504e0b000028840d80c040d84d40b01d8042c6510001401c50300540d10700b4103008001100055402c10b1113400e100c5406d100030801981d05482c40002041a0b1404204140c600103000c060419001c10078089900092800420349050360007600340b03a0f06540c00d14004078a0a211584520786048030303c01990b01caa070308400100902c2c0c2c025a1050215071b030301c0401c50f09983c015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 271200665 1250 271199415 271199437
    0xc03070318030609030905090c0c3004031a09030c07030305030403050d1d07090216021e06120f01050a0312030b062208060609040201080c0703050d1103060f0402 71
    0x10800100020710030046440355011003110021400e88940307441c0c2c00c0303642107a000c034003103074540c01c0502461600c2c0d6090307a4046a01500e00b0300e0000c4060b402034441504855501c92060700b01c10764011040718948041079021112299600c4070f81d01d0410709003445ca0503000c4070000104d00d01045040b8400300c01c0f0340e80050654000c211961070b66608a44c1944014401c0d01000000c4c40008440c5c00a0b000f000c08611481e02c0d58410105403030451810040305a00281e041481003103c500100e0030314030b0004c0402e40440c0e00100303400722002c1d000000c07002180425071019000440c5205c01610040c02ca010710402069408070780e03250401d2200c10a12400042c01000604010660300352003604281e42841010b08042d01b0210610002220f80ca021100380690301c140d50018400800e0400090780d0124007210384050070305090300042c08850014010b4400588006060014540910111000000703400701c20041c0b51515400d004040d007040e10306030320903c9141007540d1079203801d0003602c043c0550 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 271201915 1250 271200665 271200667
    0x9080310080627070509010b1206060307090504051b07050d110d05121003140d0e09011202010c110a0e0f0901060612020d140703150902040f0312022a0a0602030c03 72
    0x1914883c0f6100007052900341d141c0d4441c580300440d1130388410300038034003c4c0b03600341d000f40e19072098000b0f61188490040185024003801c1c010049181e9000c0c2d10042120b40944000a8503261150819000142c00180400500d00001d04da01000800130b8191200e0010fa0b44590b640ca1500c0305068440405001010000c1c0c41404070309000c880700c0c844140c10030f2890b4481c0700903039078a82c1e5140300040d201c0c1c5007405035003100c80a42491a004441c0e4407002c8411640302c0c1c0150305001047d00d400180d001c029041028680f0401c04112040b100c240d9003c100034180c0005c5640c48545000e8000100d1f4070180001c4401c002c60703241d51050003100f040e5521911510001c404548422000f900204441907d6584510800344242c40049410b40104040e503004140d1800034104421403111a6105034241d0384108020404540b10429260a03a903002d2612100c4c085000d204a1411070003e03203044030a5944800c1e11004508020f0b0401002c40a90740c0d00003507540c802085e82c40c1d010780010a203151304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 271203165 1250 271201915 271201951
    0xf03021806060315011b03030c1b0c0308090102071206020a110c0d110a0905090c12030a0c150f0e011a03014a0105061903020d0605060310090803100806 67
    0x2001c180c078003c00107410314010102400340000c1e500e00c1b20309404180c011980c0c81c16850026648035044058040a5484520904e00f542d500d48031034520340c2c40003404005004c583c0c8040c1c0d030301c244207500040150008040310040c2c0f45c14500000c1d8469061140401c0c2c84181038920800085000100500010140c1c1d140180b281c5499018640010700340e90710817081d0f640480e910400e40318060040780d1140040074020840801d02500d800c2282000c0c050b54010302400a1160b881000001a0342c1c0c0619030100312502e026840c0c01521100a803403850f241440e041d1140507805600560316250f041c000c1030324100e0184185802c0300c60842188042d01180700c03040c54036464030a1200c61400c4402c0c03901583c0103090441c0ca580305545103c590f496512017003407000603d003407200d00024022829842400b64038685c006030b550350072400300802c119182c10020750760707035000d0000706806c02641c8000e00c40901c56207070901444d80121000b400308048200d0100c1c0d500000914140725a0003482c3e40d2801c1a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 271204415 1250 271203165 271203181
    0x40e01110a030e06280911040f09060b031207060209030a14010f06050901210f0b040506040c05040c0503060d021801180f06081e0708070b030702010e15160c0501060f030218060603 79
    0x21260006840211211f0000d034440d4440e44039042a81c0d0918000240301611442c1042c15030b1070304000036119070300c80f0a01d584144d00c54400c6946a0f0303401900103aa8010201c0400d042c5000a940a04060a0303802155410300041d0051b0190540d903100400015031140100b04c034803002806000c0402d00d4010628003c061400c600701d000d80c0c05200b500c0ca80c80301d20340d140006400111003c84680d0014030502c01080194481d85000e804126002e000144000d040241203010051189100d0007a00c00b8880564481911500f00e4054184a03400300790703100c0303a042c1002082c01540954061a191051040401910881d0151030b454000380c62680340441950034940052112004280140000014540030402235040102250746030b9076206e00c0c10030006401c6403002c40c055031268100c0c40c85c4202071172030b0a40059000003204042d6040e00709081003101d80b0619840700500c158640100441c41050382c014003400c69108031101d04040301a80503001400c036090321490341045050010034021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 271205665 1250 271204415 271204421
    0x6050a110d2706150803030705300a02030712060b09040510080f1f05090c0108070203220512070e070503040206072f010309030905040e01110a030e0628 67
    0x1081410b050100d001c1c0e2007090414003400040000c642240e60f810715141420420814440185500e03400342d4210b180003d40540540306401240c00254969509083c001c000c1c4031f8040320840d042001d56195283c42c00303814000750300507141000454203e009800d95024180906410760710880002410600d90704140000f601c00545142e01141020b00041403c801c2041345c1a460310010f00241800034401c1a82740b03001054100103080c1d941010f080000342180010724240c140c1080c42d000140341d0720b0000481c01c5004202807055800401c510002e0000a62060780090700ca040f200155040e20207110240d565607248101c0212405a8000402450066005e594800d0015141da07141514541d14010a42400ca4941d00c0500e9055200d002d52100c0c5d5850003001070003800c0070015034810740c0300a4101c00c8184501e17071141e41ca4000184140d582900641d021904c801901138650244031700180160080c038150782c002d445514000707008041c54000d280002c022001c0c40300d2640000751544006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 271206915 1250 271205665 271205681
    0x203071719030309020112020906090d020609100e1203031605030603031327060819050709050103030215070f0507060b01030608030f07050705040c0e090a06120303020706050a110d 79
    0xc01c1c019541c00050020300c800e09020800d01c40d075030000e40c100842c800903283c81d5101c80003114191050001c005d241d11074000b1140c00280803690b0302100c1041d440000d0781c2d44510354050f90801040c0101003a182d07044824074042c18000c903641c07512149038581c981d5407400100c84503e2107000c000051920140220001c1d6044400070301a203140c1600100b150741172400c1c0b5800a5000c903000078035039460703540503207040321383c28072104060003824649943d55949103203403041c0e00004060803009400f00b1600b00981d80040442000601c80da6070b40c0d084c00307501c4840c90250814000000000903907000c2c8142c00d6004080010348940b4101401911404001e08500c0f034440e061641d961004220440100b001d0500c4c54a000343c031664400040c0340a9040403803603404240546e007803501c80101c0300c0d007006155403804015a4110826030b1008131a0000d4034483d4088081099069107030014140d0540007050120300500e41440192142e186401c11540ea1000cbc8000003881801200440c03119a009154 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 271208165 1250 271206915 271206959
    0x1f05100e04020a0504090b15090f2b0302101808072604150206090a171c0c091409010603050c040503070906090e19081309050708010e0c07020307 64
    0x10040001034045000c80e8020070024000c07a002160402248480e800b45580ca05001d40701c0428041c00c800c0044154001c10306403d02c10803124044100307030345905812001c1340b00c1028011f4914012204900502c20f09030380c041e801030042c4483c07960382403100c0c02244500c821003082c0d0280c10b001a200d0600ba5044003d0446c0c00c03000840314000c0340201500000c1c81f50040c5003401d0781d5207140607441100340c3c1d840e80400003075410100c10004036100214039a106d0941201c0341c2608209004506800c81c0b054040304003565800c1007107903502e600541e100e008003000c0c0d5190300c40c10035154180d4117400f0b80f050901700d500c452158010b00c41d82c2d110b504840c0d08032090304011420151a84002401c15809821a0030341c1690b0300820820b2011501810202004d024050001141400d40d00c244607059000080e255810009020390078980043c0c0c00c1c001480410307400c02c07541c01e00c4507004001c00c90a02c0b42c11007425002c1d001c1100740a01c03a080f5600940d0003401400c402e8688501c40a04015004480d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 271209415 1250 271208165 271208177
    0x15030a021602090718050d05060609060103020903060705030f01090506060a1107090e0a0605010b16300509100305010605091c0c1715040305120a060b04080d03051f0510 74
    0x3030060300d410744907900464503600c4007107003032100c2d01c4107003240401c0b540b003180b007500c1094002020503404501c00390462b4040d200b540d055500c20b40168040d10880030140d40510454042003c0c83d98408007441c0a641869200420359984082080540d00c00f95841c540c007843c200140c562080c06140b021140348481c00a0300e40c01a40c401d000011942412140c441c41c1d003000c500ca1003080020300c203060140036072241075070401c0c0c00c20101481103521910028940c20449070403c0458480080b51102107186d003004800303081481e01c00801c660000755445000301c00c4208140c1c0d03000c2c0240660781c143c0395076907900c0341000b0100c402c1114504d681561084602040790010000c070341403902800c05845583e80044240343c030f40916500d011319012000091400b44428040080c3d441001c0b9011882001c0f1050801e498602c0280010003a40d1700020382e030386000600144103400400d4240107800c844d1010810b55032070326100705040704042d450480520342032000380100d107008888581d018400b0b00d8a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 271210665 1250 271209415 271209457
    0xf0a080d064704060e010314010f050d0f060510090f0c0f1215030803040201170103030e040c1107032406120f050a08130e01080d09060813051005010e0615030a02 71
    0x1d100702e0340c4982c00134400206000410005540c0501543e1541100440002071030f62500142c595600e61600400344142d1340d4003400c1040c00810011401d2417500603a04015600b0144200411411207100d000c5031b02d401d00350003402c0100c0c07a118065030454a600e0310319003580f46400c2240c00c0c400341a80480016544c2446444a142c1e213000721014501ca032404540e80d0515000140800f442c1d24984408070f01c00360010f10000394412007080413030300c060350701080300e0080d01c9007551400070390218009030b1f100e80d4000006110100d607a2141030804004401c501d070280c203104e00c0588583c0c2c003810410b48950081c90000640c456000000c0310b000d00140c40800a1b6035039140c91951000f0011034083c003415509024000104192900400d142002031854508011002d071600200e072103000c05014070b5100080103168600003002d600d5900c1400d0351640800c0c070100c0c40c0280028020070344a2000c000004141e401c14903400041040c01c560158110354500d84800082c0d030010f005000d219a1303007a41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 271211915 1250 271210665 271210799
    0xb010c05010e01050a050c03071b150c0c1713120302120a0306140a050f0d03090b1b1b011d0102030403022715010f110f0a080d06 57
    0x20020300444070400421340342403138400f0100b0b66070003400c072440350318040050040b0307e03401031503c0c406003030380130085070b2111080c2c00c7c0500e20500c0500c030503445600b414000c240303180d072000424401034440c1101405181e000101860907018040b000344010900f0710050005100c01203440758903d10a104581d8420b02101b440b101c9a0803161042c0d0109480d001c040c4054805003155208040003034500b5001b041c81c1c03500080c0c252962401090085042140760001d1500c102200710240c0100d0401c1070341c806140070130080c00b0700c0140b02c80000c3d0142400740656a070f82030310a06014003059480d0b03030615495090050310080c07410322441c1548801c010020040e200c86018092140114441040c903400d08070000c02802340060030641103142e0007002030403d84c1c000c100d1040d01249454103030750100301c0e058000c1c5003021040720084584510541d40042004403c014250880f095000b800803a42d605404a042c2d681e01c0181c0d9003440715035004e03e40c0490708401440c440355503440700e4040901c070905 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 271213165 1250 271211915 271211921
    0x405030d200d0908070602210304050c06030c1c0c0203030412030212010306061518140109051816050c0a06111c021806030105060d0e0f0303070c11040c02100b010c0501 74
    0x403070b010880340c4004012612040c04050002c11113030000d00001d03940307490302c07e0042003a1800021016404004101400410400105d03007070343c040c00b52560390400400500042e0411804541400803404d900d0209a8082c01100c041e0300c00e40c2c00035425900c1c0d903a1600c028608011034442019801c1c00240d48000d03010a500c1e00031400743c200007610780d007004800e100070a01491a001402010840d40c00c4401e00e62a00c401114400c0126850764a440001294143c40d50f5000700e0780682051400d030162100070451600404000440251003403960750150f07451f004203240c20381e80d5000700049502050880d000034000400c207a400500d068000305440c43d0141c08590074080255004c00c110000d6888151102c029102c00c56030541150b1403c0c000a107144107104113584007945543c00750b01c034040c00b00044680c034403044e810340381c0303910340500000d24400c0783c4da1013541c1404038240c01c51100d09040c0f02d000c2c2c0c03105503a40500f00032441503800c0005030001314416410000c0352501100130800c288 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 271214415 1250 271213165 271213183
    0xd0510060b040501110f0714192303060121060e060907060206010b1e0706021303060c030f0e03090405090319020304090c09210602040317070201030e01020405030d20 73
    0x80307560b500c481c1807100050420b4440404540c0c10b0b0301007500880d03200c800144403001c0320042811003820604010102d174420314200041d07004810f2110000c40d0301c00081401030000c41c00c1e040b000d031681282d0001c060f9150828811000300ea8000364142e800140101d01104103140140400b0401c425055481860100b0885a406254000703c0040c007010303606010301401480098040ba08107440300b41460b03c80b0500001403480d142001500000700300407501514040035424070b42d02d03012556420501c000e00400038050000a1400141c000314042a2141c1d42554005000841c10703d070444050000a003000741c840780e410f1005000002c8000107000813141008520b40c051a10340d4902420341069488070b00818051000c00101071204600b014100242c002040141c4140c90000342012402803155030000f070117070312014408408140c0f42d1002805140c2c0701717a900b0019000d0b102c0c01e003400c038000c901465506070041491a064144280200e41505054043d204d0a012040384c0c202d01e451600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 271215665 1250 271214415 271214429
    0x70b090f0105010e0126070803070c0e130c030210140f13080a0201170c07061107020102100e1b040b060301060905130c0801090207031b0b0105040f02070209060d051006 74
    0x58144010602000c0c0251401040566812102035061051100f030402140b04048a0070010a5000d1b502c0f8908004000090200b03200b900c1c0e50f5079060800e1005412280640341b40f00b03498a0100301e210074100b00b0380031019004010110b10900719801c104220105056010030446420f020743c040c20308420060003008181c128495880d40e0b100c10f80c626440d101d41c81010640c0100c2542e602503600400740707001c400858212007085507580303a0840d807030b80610f4001618952401040941c0c1c3d40d4401e0061214074001d8003190403034194429801e040c0c0341d01440d0a401c80e000010514806c00805802d0440300000500c0400c54021607004900d4030b0b0001d078851400200b11000030481800d0418410311281d410080a01481c440800c001e000d084041c0b00e40070900f40d0008009003494403070036803083c840b46100c100c030f03140c2c95175070410900c0340030207008840c0704503c0d115128640c0d04841c0f08803031055501400c40c8800340e80c0c400401030051060042601c0c43d020700c0010b800b0b48201e41c441c01c0090406 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 271216915 1250 271215665 271215673
    0xf030b18270f1e19050105040c05090402130b150c0a12050708040302010e060403060f0c081302030a12030605030712060b010e0d150f0c050c010b060a14030a02070b09 73
    0x14140c501c0c00340103035501c0c06100390080e90107004020720102c1d904140780148003440100701c0c925100d031460094904048018100d02c80c1502d01000f2040d00540e028500480d05507114039140c5041060300181928000c2d44003034101c1c100390f43c98000e508940000280105040ca209100b01046401603011100c2c0b6901900a0b2900b00104241040c0b4542d910f030551800368103100d5250358001c50340c4200e000182c140002d0102c00740681c1c0ea90b00032100034691242c82844407114018480d00601100111403010400480c0002c4c80044810848120950020014103038010607072900052015030008160030103071183d0011400d03440400005000344030300780103180d100d000c0d030901c2c0301240c0007030480604000300000540075680e40c0311150b5246541114074080c0203940c2144400080180d00650360070a82400100340d030f2150081d002d0302c1d40407500002031020402c9642003102074800e001b5560702241e40b820385140405000c00140da40045c50700e800602c0c2107120303140e40c07186400031101c0500c1980 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 271218165 1250 271216915 271216951
    0x1207020f07240212120406091e0320070b0306120304031a0708010f031e0606060201060509060328030e1309141218011e020307051c0f030b18 62
    0xc21510000103220340c0c40a010403030605103e0b41110720812424140540d1807402042c2408217541c0a0180c01c2d60000506c0c0d442d070b580b201c241c049880c09c0c01017580418007552401016002100f609004089140003911849040a9012035213401c0541011741168035110303e8582c1c0c030810002400914002c00300030f810035038080c00030000c030715005003440c04211080d0b0041101c04624180c1e08180c0e0b521807080c643c801401d01032030b84142c0c0d002e07402902c00d6081010014a40350190701100a846080d00e14204540e02c0c2d006150340c1d1790700d00f290310001d0040c075065980c12440e0011081340e414400c1c50300001d843c01503c00140b06100000d1010f03505a0707901300e0441040110200307101000030b5000a09180600f4844120007402110f03116854248030750035050b01c50388225a10307400c0038040314041c1c1c02d41111407402917507a08400002c581521603d09001a002aa8941c9112800c0c07070340d44805030310746010000c4000c0d0002038009900306042005541c0c01d810100e828078854000d08542000240d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 271219415 1250 271218165 271218209
    0x307061514010f0305040303020d090c090609050c0d0510170706030e0a020127050306191404120c0305070816050d090803070615051e01020601060e01051207020f07 72
    0x8140d070001c403001c1c500aa05018598004283e250600e420b414000f41981d6541001e401900c02e02d00c0c400045407408202c03000b040010f692442c02d907003580c4410840c2070341340c5040900300c55081c2c5036520031200501c035101c042d42c0c45812250788407460444d02e503100b9640301075003014044445011047c41e00070f540140300c0b040d41445016140540d24000385021911900040e203c81c4030602d0002c0c1451050840c5000a503200d107102005001c081c040b21050f14150901c43c5410183d09021041e071070a04030074000100c10180d8190003681c00a8039841180040e00056070007902000d0114103000b41031019101250015000d001e040c00d0441243c00304194628010f03090a040d800c440301800940c4405100c0060b0000503507004950004000030f0302040900307004038290381075100f550300445404203c0000d0b0358070031a04200d4802038007190160303602c0c1c1c4030a40352814040d101c0d600040c0c0500c5070014119500c0c5005400900e5401500c0c0c41145000703d103401c00e0080d820207007039805100640b01e254 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 271220665 1250 271219415 271219451
    0x2030c031b03060708240a05102a0203060129160b07090807060318171815120a14150306100509060d03020f24062e03060305030706 58
    0x3c5100c0c07405d91010b1503d5070700c0d90400c039000360710b078841c205501e4202c13509070b156090513038050813000700201c404c000003540003095000d000803400c0130031450301d0303088003110f0042c000d140380d007580180549190313801d054040c070b060524000400013503400e10b50180d402062050040c2403002020000a10002c0c96042002009602a10810401c030303042e20108003151011450340d0070394a89140225540020100600401001d0800034120300e5174442e050640d01d00101c01891104800000d40d030800703854004003c0f00540c2e82d055954840b20412003030b03050a44540603d940020501c81c0024404e03000c171002031482c3c03412105058407001da95035823911403900300881c943c0301c0820701d01d440c516030900010442d18100500001e001c3c8181101000826000340b112500741e8980c002180c01d18416000b80c0b4080c40606441c0030b0200d00c65801007046c2c3e0a028402c55a01c000341008500742140d1541c40e65513856903030703400008140d0b48500100c0040c6050000b0070001d8014400802d0040c0c0c5e0060701240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 271221915 1250 271220665 271220671
    0x30606061d090a11130609150201140402010e041e020306040e0703020f0d0c0b03070806100203190e0d0c0b07030801210f03050409020a030c02160e06090402030c031b0306 75
    0x41866085920a401d6403660061548102030401c045016084503036404d0981c0110030781c004083c50260404030700c80758407600120803201105050020908088016400c0707840c5115040610001d02c40080c001d5401960425982200540000b8010101d03d568900c00345980d5014003e041e000410701c62149014020f5000b01030309440a400c00d40d1a590018650f0803107040005d005a032100e80c40d4080c170520b00c0300c0c007009200d03409151380e1f6482e224a00a051384400c0320800d00c41c6144040e0a2460b034800410303075808004030b000103000030740c0c128002e482c0003e1041c0a0ba030f01c00a41419040080d0303c941d80340f4001c205244529882c0c440758500075108030b6058000d014050314506210341500852070f0b80075040c035088081130020400f030342400c550512a50b0000c0c3c501c50300002c0c00741ca0003681540100500e0348182d0945040e01c2c40301508502d03a1119204014650404601103041454021049604148005d00700c90340e04d00c50001207410840c0241c400c40c031800603840b004255080512120364 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 271223021 1106 271221915 271221947
    0xd0c0603060303090b0403052a04020a121a03030f0d06030606030b04020a06110a02040b030a021c0501060f15110109051c090f03231603060606 63
    0x10340070074407044000030356681c00000c0c407a0309281074030309a80d8407038007824440402c410b070311000014400c2c00c1d024a80b15a242500d003a0f440b44018840d51500e03880d02001c6407070560314030040f94001c105240f0071902030ba05c000342c150b6001c401c076010024181002c40d21031100c1c0074140d00814041d04001c0c122481c141002c020300c405030140500c036910854280801c22385800c1c0854180543c800e402c0000d6200b004404010b10b410b401414107000003404441c00103409030001201c820f090014507180b813040d50340140503c8420300805c0c010344a00000c68817510700c1c01696881d80e0398031040c58000c0061521900d032108100b0740000c40b406070400c00325400982c5000048042461407480140882c1ca00580003c0e501c43c810307914811a03401a21002200300260100b20354810620b04a0645002d10440c00000b80c02c180c450401541c040c01c0c0008420707003001c10190041d030540503088 = true := by decide +kernel

theorem cover : BRFrame.Cov 271043165 271223021 := by
  have h0 := BRFrame.cov_init 271043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 271043165 ≤ n) (h2 : n < 271223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
