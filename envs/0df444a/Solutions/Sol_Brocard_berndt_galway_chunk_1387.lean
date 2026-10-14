-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1387
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:43:19.356909+00:00
-- url     : https://prove2.me/submissions/1a2521e7-8106-4f8c-8b7b-5ca504899492

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 249280575 ≤ n < 249460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 249281825 1250 249280575 249280609
    0x1b04090213020c0c01030e0c031504080c070e010e071d15070602070602030105100512060d11130f0b0d0c050904080d02030901140f04020a03111804060c141314 70
    0x30800d103503042030010320044d10a0080c2c0301080305404010200e501c9007240d802040d015841800800b0f4441030040c2c00ca544075014240c02400c052a10328480d091a84541c000e0140620800042c0302040002c2042500b2a8007070400042c1905520303080114111944880762103426401c0140d6600394600c001c0b5040240d00850842d40d40da200d1070000020b40080c0100c40c0100ca24401c907a5101b4060703030845074862008045103450f662600c0412402a545000c11541031411100300001c0381c4a00900783e001d40002d070008528a1310301e0514000b110b0401c80103620803011034505c1c0003c075240228541c1030750000d5440b0200c542e21400c1c202468400c5181c41c0b20b02c0c0c0c0c03000040202001d01940000704030b0354180c85480f103549804c0c03001100304d407080d60040d502c0513814108100207030068051603503401010b08052810302d046180c082c02c0c50411503096540c240c81d00e11000001d903020307040320b5054140c62042802c101c3e06d46c0441c48820201d0140145007048061a40724503030b507490402000e5803c1d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 249283075 1250 249281825 249281827
    0x2003210a02101d0d08090303041b0302130e010f090305030406110f0a02070302030c010305150f0f060a021018050d030f090206040303030e120408190f050d08040b06031b0409021302 79
    0x1481201c1c0b040703468000c080b0f00807035100e502124405c40286001c1c03a00070000718155122500c030071440d644080c2d00041c080c43c48010000058840e004c249904482c00c0e403000034a0f1140100b0350b030030f40c1c0001d03110218240c603101c0080d00181d041003d994025400180018100b2810710b42500b00b031080b00710740e010511000c604510707190781c00030344141942d00c290300f038070800c0d041e180064043d91010741d0b544c000c8110350160032000b03052080d56035030200c3c40104481010020324001c116160b000b0008280141c004061841c1103000e60300865000c2c503542e1703080504000040c1c071101d4951034646190f208240d1252410440700505400401c01c081e001400503607aa40c0e01d00e0f019008119250034400b940c0603a505040359081d06038192401c035000100907091212031301649050b68418010f084030b444911409c0c00300454402c0140c1c6040981d10744031401c1c14206802c00e20f07010400140307110301c41d03402015082540118102c24852a41d801d0341c0c0410340078501e00c0020714020891003d400241e00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 249284325 1250 249283075 249283091
    0x1b0305030403120503010f0b0903070509070c061409030f13050901120302010506010903120f021203010308091f09051c150501061202040506040e06010c060204032003210a0210 77
    0x30004008880c821444002c07415402036050ba4540000d10900c440b00c696100100540f102c107100500d41540300900b03950006407980f0014152100c103071010400616120954003c20481f07210300118034000b10300400b0503142c4240340c0c983c3c0c0d124950b00f546000c01d011a01c0b01c2d045c450002c200014020040140c0d46660b102d50342c440c55079600003000d9006600300f201250341540140408010f40e5045240d01d01c03940c0d00444250b402944003080b150031886032030f002d00c7c001458a0099400385226030a41d0b9510020a41045038003407004100f6080494540b401154481c1c104502d0003c8407029500c8105da918038802c8020070300500800a0941040e6083c0000130100a60050781a2500c9886118410704260702c660124092401090f410610400040c40700c84d1080e61981c0c0e104c10140f502d904124120383e00c0300181c0c1c0103030b801101d007900311351412a10300c0b04c40f180c0000da21000750000d00f140611810408071788480d20301c280c0e0b441d40000980b07140180c03081c01000c40c004010302050204603 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 249285575 1250 249284325 249284333
    0x3080d090201030f0b0906091b0c0d02070f0b04092c06040209070507021e060702060c010c0801090515010e04150807030b0108010606051e071502030406061406161b03 73
    0x12001200c1280020700c1d20120b6800d0b0801d521909141e84000f070000d0700c0c00c4d610740c0300f84900c074a409001003003d07031490704082100c001e45800a2050402402c05401101200d05029103042244c1d0070070260350041040900521400c0d10079603003150740c1144042429207240015a02c0c9444804c54210002c100140100300d000c000655280690302c00d83d960721003603a6100e02243c0e107000d0301c50000d6100100300f44008001d0a030507200200382c0001001c007840e10f0400d600145a41d4407079000c24186944941c10980141c1d007200885004081190060105150041c4d410950110184003a41807205010841d0f0094495a120b103941c00480032118100a0320f400d208c0d66075040900c012204210344074008200090103003e4001210b40e6502c401e400c0190b08100170b80d0411944110044500041c000c00010810004d50800181e42e55040107a903801d10307050280944410f034000504d1122800a86c18043d103500048402c6030030f00c00b406040c015002d10b0400c0381ca140341c0c0540c0c4071506680402100740 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 249286825 1250 249285575 249285581
    0x12180803060f010504060c060510120c06080f010302010504181509020405031c021c140708030708070f081f09060b25021f050c0f07080d020a020d03051303080d 70
    0x510700c01c95904542466031401142c1c0e900c120b0140100160400654500183c49a0407043d0080400204481a1a22009000c40000a4020a4565030599402084000c0c2c005a41e650840d40d8420b801c1800c1d81182c001801d184118800d210061510550f05601c000700d6034019906812034610f40510a90742e4503c80c0c0103500207002d5144640104564a450910102c0748502c079402940c000e004100700032901009121849281300b4184440003495204a8001c2c41c001c2050710b12403001e607910f9081c5408014483c01c0e004080000303200c118a07110f811250004101903020202c0c80650154090103c0c1d0000c80e441c0640c0300e1400503080070700100703a000c076a0015143c035880c45e4800345805842265031300c044122070300c00a504084035600358200020020401c0604034401d0400713071303d0084a20b12003803070000040c038080303050b0b084001c0612003007009100d00b4416125910007420080030030340015244000f00c440040600400003003410b10341c500000e00400070358000005540700c1e540070001d0809 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 249288075 1250 249286825 249286831
    0x20f010509010b03190b06090c070807050703030e01050a08010b1303020d06060504110f1206060f0a030603030f0f0e04020901020c030a1a310303180305091306050d0312180803 77
    0x210f405900d40310071144203100e04d44d071419a0040217503511600c912048c0141d20001030802e501c4903104101c14404100341500a00d4180d04c00c0e40140071007031941c10024140b0204661075410805c041002c4910283e03c03036906410b448000c1d1181d555030305100300e00954810b0542c802500b05141482d031205100703c3c1d92144e41114030036101849106007509022900e4460b48042c000d02100601001307441107030801e0010b500110180c01213140580002c04407000303400c00c4000034002a1103240600070142e1241504c1141286400c1c080610034a01ca0050724025026030b045021300c0d40442e10045981c400c101c2d01c001080c2c05019100a450241806c001041001d54140c0480d0082c0020681c0d0300321a50314840310441820f8081e12410748081443d400f2103036401c6c2901055110b00240301291840d0002020051190301d901d13907500081d00521040c1910008000b0900f85464010005912001b400c00307500355161400000d02045443e00780000c000040d01c0c2a048000440003100300a010300040d40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 249289325 1250 249288075 249288079
    0x90503150a0e010207020315101802090f01020d05040915090213060e060703050913320a05040b060d1505190b03010902030705040e03040308220801060b19020f010509010b 75
    0x400302003024800b500381d1103078a000941591120403020039505440301c2c0c081d004844054a185c0c03066561144901840041442e010450380c000307100426880d101d144420101000c0c000b401d05c04010100150990056200e4500060348070383c0750045003081d203080362002c0e0280744070454551040c0019518500030724003038840400e4a450171100d4510300982940c0d1103075131541c0d6213490882c40c0405d1115043d985000c01180341d40380e0011300c9154107146154801429200e840c100c9401c038034005c80105201c050b01f000320180c501024800460840904c05900601c2643d841010001e80d2134001d440d1032602c0c040c803c0c054644800c0c003200711070046008400414403541806081d1032003003007508071100a00c0096040c1d002250400040c00e050300610300010140007500e007013681d203456a840c141c0c06410180e0981d140d82501c1803442c20a080307040d002e050004003c0100500340410441c00d485030844654040c096855600d040c1c5100f0464240d40c042c81500902c2241401300006000c0d02e94022428 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 249290575 1250 249289325 249289331
    0x109021b1617030306060d0c030b040e0c030c0108010e13052415010302030921040e01180612080304061d16030209071b0204020a0c0c06050405030706030501060e10090503150a 77
    0x2202c01030004141c0340180701c0180301a240290344102400180001046e48084c50f481e0001d0101e00c0c1d17110f1013050025030440010380a8088010209410603000c03030300460520450000521a002d886910300d94800410200303042c00300140e041892a1500318145041041564600c008581c45015900d07402090b80c8030071819002d28a500541c16804100e511961503130146071411004ca0503581000708201c105805686041e8070f40219801d2264240c102c040042e010041e8a2401c0e1520f1003030100800000ca030a00d1109126030324040030f4400030f400640700d50f445207920240e00840707403c240061691401119078400310b08402e070715214280e1009030b10a89140c40001c0c0a180100e46546001800f04080100601076030300700002504051045010851080001c10004440a135007802802c04c0e51200c644a91400c42054942040e5030441c00802d42030800410110390010491188810704a5a00710340d00b010400c12140c15a1581c800c076458481e0301d4074401c1003542c0030cd1580c002c40c074545082c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 249291825 1250 249290575 249290609
    0xc010e010612050303041b260601080708030703030b01200f0c01081003031103070b070804050d050f03070e0d051903020708070807050907020f060403050a0e0a0e0109021b16 76
    0x2942c2d919810b924040c1594000f0030008000400d41400c2c030220821034001c500209072250b406181081c035442c21072000c10404541e0000d4000704018050060140348000c1422500f0f00f03000c04d881c0d014208004050548800c3c0301c01e15a0b002d044d0740d60240c42104030042011004128a03079840741031400d04c003c140142e60007603496500c1601528880c00301c500c0b00c504031915640c3c04843e00c0c200da0348800c8560206000f402d00040020381c41c507009881983e00c03c105c03403d143c01c2c440e0400b6840807940082c04002c101401c0058503580c2525480151401d043c90079886c03a00203d8046d86043c00002d00c50300600f103014a54400750f80601050901a500f12500f4507140d60009948010901079051550b00c600f034200800e1030401c1c41c8691010309072042d110320078101c000841c608041501d00310046000864400200359102031041c188280c126456001c040c80c11050802456060064034070117030700081e541c1d40714545000090300029400c000c44110f500c401c81801024030781c1380034502501040e140c40d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 249293075 1250 249291825 249291839
    0xc1e030a0807020330061912050f030a0215090609070b0c0f0706030c0306090b030c040902180108030304021e010f12061d060907090305060f0604090516090b040e030d0902150c010e0106 81
    0x80c15100140c000702c258102420040f00c4854285601c08c1183e0511400e202800f0000c001d002802c801d01c0c9980050105004401c1c070001c03142c000a01001882c0c2c807010070040c900000140300001c4805401545a0710207801031070700d061a0420303055020078802e070340d00058400c1c0d0642c000c1c00c0b070001640d001c1080d15200d440480648020203510380e0305a0082c1c01d00b0f08642f9083c0c3c001c0181c40c0c4001c003004030b03900c2c640000c80801c48003684030040781d806c0842000150705040141c45070448498100b81d407a0040c40c000a0b0559804900203010490440001284106243d2150028003c22946000c441c0d04520f044a0000b104541440c09940100d0219440134061040102940e511001078042a590301d9002c200412008000961168a03900d5080c0420403c6c400d10744041025007801d90918140b029000a8650f034105903030159203015040d00180e41c0103c251085a0030b4007202182a038101e00004407820b07070414440b041064006181e02c2008415800030f400050010000c0c450580e42e040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 249294325 1250 249293075 249293089
    0x905160f080c0f06070515041b151107080f0a02130e1002180a06031a09060d022206080a170a0905040b041d030c1e030a080702033006 59
    0x2040055039071000340086214035040b080083e9441024060701c1c1040001d450b8035140512204a5180018815080c001070020504044404015140f60740440d145810080840600400c10300410000d09641c585c00e0513200f84450002401108120b50410740c09444c42600c40c20130b458102c0c0b04100b00b1a482c422010a03020750116090342c000905410318640e40d5502c003079402285030012050341c1f00c0f4281131075524485030401400150b5400101400f58510300710740000b0260045118562482c10410360f651a0070b410f04045138141c503041140324002d10194a18a41403a164a9041c00c10f01c02052420b00000c046803454022400c9503180c070200380ea1005c02e481449020400035821346428070880c28181c100c003146a00180c000226043c0305030900d500d0103501914820320390800141c00ca00e069003006201c00f030300b0150003842221281184240d569118800041081c4131452001890300b034002e00540d0010407005801c0001446c2640d020074000c202d01c084ca01c0318144001c045080b0381000c2c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 249295575 1250 249294325 249294329
    0xb03072310090b16080d06140d1509020d02090403020d1403100b07110d0804170c0915150304030c171801110115030f020306011a090910090905160f 65
    0x6100e2003061410f104000b205640b018074400c680301c0751040c02100252041005081c242d40303101c800502181030000f46d0801c608040300551003000311401c24808195003240300c3c42c04505c10b0f4070000f4250400d101080705d1046003100694000d026071b08000a040c4c000c10f41807185070b819564420080e5680c41241d410b408203558401c01d0382224042404030764140d5008014042c0034101e41803400405c640000e01303c20610b18211040040401c0400c40a540c01c4482041c0f10382c40000b0307141508208010600c007240003003004d1300c24804507544107050b031035480c9000038810f40d81050990b2480c1904000d020426004400c40707220019421001610107020250391010780c0701200303201c51852070001103807402c5d81c50801178069540e51191021680d4850212802144140c610503070103d107600406040c80d005034440c000a0306520040002501c02000319507039800b088900e02e02c50f889141c548a0400c016400008920b898090040c05005001a0941d0007001501241c01c0c60754481c401d04544207054 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 249296825 1250 249295575 249295577
    0x10215010b0304020607060c1d0402090102060a05041703090102090a1d0f0a0605030304120507060201061811040506030c0c07062303190c0f020c061213060b03072310 73
    0x103200c840c00800c002c60b00035000510b03460510300399444510840d000a035028010508420000d900101000080c003e6180226011800d00110343e00113034032502c0013000b15008030b0f6504000b0f0301b041510035900b8411208240c0f40c60322881c007102c00c0ca000f9445009450311840300200001001c0750600c0c005a1508682410403590f603c03224005070144c100034205211898642c000840e90ba201000900014001082e001c5600b00c181d040403410480700c3d8001008590510000b4050020100d000f2000e80c14500310004600000320030310a01c81c06590400c40d4020340010a10460b603807070714003070443d007940d180584188a6440100f40c81e09007881502d40000a0503c0da02c40881c80da2002541d270180302c9240e400340e0300c0403140c3c1903000c4542d1000d03240040f8690f110a100441c2e170401562400c0c810540d005031801c0307240d0010102e5200020551a413209500da88002040140d800007181040080d003202d02c9103480d181e62000006c80391200b14178110610305032925a04d4003546a001030102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 249298075 1250 249296825 249296863
    0x81302100513170703031701050a05150d0603080c01180209130204060f0306020c0f010e0c040c052a0d03140106030e16090b09010b1305040f061e05030c0102 69
    0xd128400e45031500014840c1c003407807000480000740550101c0d01c02c1c51000800010b040c83c54150b14000c1d1880d4030700030001912080d981c005100c03549a40701500140e500031221602a42d00c07440d035170b20031440341045208849041c400000f081000c070f40060040108802e0080c4501d203228200158030450740c80010f5403002d66000400e8a40e48440018500580084c1000c90304988501522461201d260310440705140d0000b0801c1380700105200b207803c40703403005009015014050402c07955860807211271500c2541e5804c3d00c04035440c000d00490311a074412b01c02007246003240720421454504c5585820080d40225013040b2a010300c2442031415100c17412001040690801703601300e004200405241c8014030510102d409800c030104e4100c070040a48020204180d503092081c046044030690041030030213000c0c811050030310b0040745c5007400c0c1c40055400040807828100760070050a01507101000046825044d01140b4074207c0c0d046040d40c105404454000b1501401240d5608940c508100b0040c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 249299325 1250 249298075 249298099
    0x1b0f020c1e0a1d0f0106090308040306020a092106150609181d010507031103190509030d06060e040506010806030303040f02150a02060f010e090c0909030f0f0406081302 74
    0xc1d20140c00416144041d0800200b943c0303607801c1d10010320041c06030690f4a0954410810b2981c05101c000d405080c1c40d141c8031711060700e16624a0b140b4055404001d00094000c1000c0305180e06c92200900200300d034070039403000b40001f00100f12218003845002d4543c42c3c1044101402001010945411111307160b5501ca4002d2403c00d80c18503103001c01090309817182c1c0f2000307001e0003000c2d4545400701c000f00950001400c1d06100e80041c0440d405110000542401442040381c0c1d011001031202018040d00000700301540c030071075194154401c0c010801402072400d00003042d0182c0c0071a280d5a02502a1400c005903100d4000544000008036000f03036155000b00005400a00070225015030644083d180508140c0040034040d01070708130388110310069001300100100f4514070704125004040030440f10040b4101407590548808100c8850b40c000e40d820740100b81048000c004544001440300381da01d4980f890b05243d000d25034018458070000404140200300d49041e00c0c600c80c9a000d40c024100c0040740 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 249300575 1250 249299325 249299359
    0xd0315170f0123090c131a06043c0b0a12050f0f1806130c03020907081f0806041203090f050f0f03090a050105031305011b0f020c 57
    0x400020410003150050640d02401e0200900448025540340c0715030300d19100c92121480b08020340180b4081c40d070703800010b824646880340519203026548004d40425030030244c1c041c81c45441c010000854100100050015004901c001c151030700380d000c94982e107001078280c00380f08000324041040455070300300d01e40c04000d802c1c0717120028a0445142c0c1010307030808620f8000c600854a0450301181121030324070400c141b42201140042e844078244000012030403110100560300c21004210700d4550100034444070621a154817800d0007540d00400d000c100e40f4044500811590041d075442000008a904030785c803002d10300503000c041c2e407885001450581d44503195603001012144010b41410340c5c607801c0c1e10104209103000000c1c14083c500401e911101c130f0481d41d28003130141401100070f1f0010b02800a00c0d540b00701c03803203003100c41c24a0302581300d0725210300b1800000300300d030002880787d8a40203031450b02e000c80241b0000c3e0580036403110141014519016a1198441140903900004a0320030550318 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 249301825 1250 249300575 249300599
    0xe0c120601052806050702090105010c03140d060e04060608010510060c03050a1407060c080a060b031501020316050a020f0103091104090c051017061002150a02070209130201020d0315 80
    0x1094074407184148902d0f1800440780300d070542d9000040080c80014100f130a43c203200c80d07407500400d001c1c40d201c5402c1099071001030492820000b80c036416940003610140c6c094468009202511080c8075400c0b80741001d14203580245000e105501540d400c19000481c900c213804a1002200c1c056180c1d040b5900c5c955804503826402036030b20b141801409803941d040c2814078006070503414411100051300900d440300241c44581c0090a2440c1c031130400209001c0690210180c0750451400180c9802d2050510011303810750040110003035442d8a07460042042c031100140c02600c00b4000e840c1c00b6200d082010045054030201900907094900007031403011103003000d60207040341c240504080c0351a20b44460000300001c01c0c403030390f0800041c059042c10f401e40c0c22000415412103400c40d1038840d100344081c00a5140e4207040700e8507107041c1012001890200c3c2a40440d01c205500a0502105103841c5400c95003107a1415000c3e801032254003500d4682d50f0180c40f030303004008801010451850710b031105031144 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 249303075 1250 249301825 249301849
    0x706020c0102100f060f1502010b121015171006090b0109030222050c04060305090d020703120e130e010c0201140c0c0106030b1513020f0711031504060e0c12060105 72
    0x41e80c0d8000040c02c541e03150086c00103000d845105039a510f941000081c2915012000d19200d03e00e15009680e1441000410090044500c5404980c0c2006050203030001d010643c415116010462018280d01d20b000c035040c85462044601040219121200398088481d07084000d4082a0204401c0c0090315000c4000d2001614010841d105080400201d8055440a40e082100410f011038148556034041c0601c940c401d209000034004101444c01c002e503110342d00d22001e420340030041911000940f0450440f0101c50001e00100d206680100c8907100400300d8030348501c581d52030028100002c501c10b000301d019103805008454620b0316070600034011607100441600351036699810000010700c4102915128100740031103c201c41100c04248218001c40703252002ea51881088822485003101042c0c882043c0c01c24401e4403160003036070102e458503c000d03e011420201c0c010401007000069000800788041d12802d80b5040e441c48414404100041440c0c3c03101030b0410720050000e410308400c20b00c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 249304325 1250 249303075 249303101
    0xb010f170c070618050c011409060a0e03030408070806010f170c010509060d0e0f06060909030f0d0e060f01300b10150e0108100b031b040807090504050706020c010210 73
    0x45841c640c0100540600c0100e104807411b8000f0301c0311100300d680202e03404c01031640c402c104501d0500e16800044242c41114000c0c418071205a122a0301528200140c07006403042808941001c2c0c1c5074010340399511024402c40b642c1c481000d1700070445541c091000c0d01d00d070490707500414400e5400001511150400609282c0000052003a00805691409035126104086000d8444541d41c0c0801d50308094004207024042c030708800c180065420000221144e90540030140703a161018280104040e15081410006610489040c00304019141e041e0034100c03001402d042080c0c1044146000000f10f81c80f10224040f40300d082c1000100e00940d0234143d00c0045803e0b40e101c010784480506005446100c4d410307000800e02d03804a13046580106645400c500b4003903070007401900e0200054081d100c020000504c15401c4440d4034007005000f404c3d24090030706035003903980542e01c0d40389200092800712000d484500c1078890000d02e0a00100b4201840702041e070141450a0000c45102c01401c8000345001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 249305575 1250 249304325 249304331
    0x11b020a200a1d090313060c0203030405040207060f200a0525050a0b06030307390602012003060604060c080d090807060b10050415210b010f170c0706 66
    0x651141c1c1c40700300e410040e03c20281c2400090025003500c1d00e41a8004182881580c4104040c012a41c1c240407110b0803180305103444900e864140c804070f403d60046610040d00540040380d50400c02c03415801400012480e40020803203040075442d0180082c402201c061191541003000902c2140303c0d000a1a2117404440140341045015000001010050740f055656401116400c010421007400c2c203604000e04400650400c0010303100c8c0402c40d42840000c4110300c0d00e2403101e03131080402a00c004800c40018040d4040c0503681c48010f40a4200100b40d1010581c40c10400001480c115099900074600649100d0034181021402c2d1100ca5144c48140c5242d5018845100f250500e0b00904403070a12450041340c0b61481071925400342c0d91130030030507807140a0710003405032620f41c008143d90032500400030110f400d01c046801518822001c2c9403901c00211340c01d4510500050941102c0388481082e030300c030848a00a04400c031962017441800c0480c14282c040401c40720701d00c4001801c0c11a00a034000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 249306825 1250 249305575 249305633
    0x20d0f14250602090102070f0f17150f1005040522020105040320040506030a0201120b01090305150103050f03040f060e0609041401050f0301060e04060e0111041205011b020a 76
    0x140003000c1c44040100d81d03503a00041e01035020350341400044020010004080c00702ca051000d05c44115103a4001c3d0000340b8000c46429030210b48c104100a01300f50002d0900c0d166040c032898030000c0400c110b032401c10301040d8920019050420b03100d0741e442800580700d003c4039003030020b042080d03c0890040c10790400201784000710210b00b030502018081405580301008803594001448255078000341501d20980188210a0140c1d0f00300d0907590052600741800100e002e204801a80d8801e4140c2014043d8440c41c2c1e00000064522000305050301c1c00b1740d08903a206a00ca0b015241d4174410b1303020f1141740c128404070070840c440c0182c20080b443d80340200014244212440458225941200c000410028160041000c0c0c01d0806010542c03e209800a00c41c442c14483e800b44c0b0000f0140c401024243d480100c1c0c2000742080d4094040d0000401d021980c032a52a10315405010190200355015440c040741e0589040c10034003082d019090176005000e8500d281c3d2642c90b0015145c01003060070100c00c00903 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 249308075 1250 249306825 249306877
    0x20a02030d020304061209020f0409060618020706181205030705120901090c050901120b1b0417060f0417030a0617100e0a0305040509150405070f020d0f14 68
    0xa641001c1000350700440d01d0707610301400107045840244c0b9940945140c5403054016031108113442c130442901382c40108080640f8a011030040c41e0340d81c824031165800c0c528040f4030710078a400410043d4007555081c40358821613a204850005c141e500200030014001010200a0060b40650f9120071141806414000d044103410910541156070b080c59955440c0c08404105104085002034034090b140050658101b8075103502c5925811000ba0221008000241441d44601d5124080b080344040701c54640369942c2060b60304981c074009140031400b82c54002a55034000c036405511454001011042c0c43c00080b403c411140c6c0090504d00003517885d0b110104030404032004191100381c0c03020003015030481c120100402c45403030200f000c1030341c0c003d00080300100f40d1010a0300c0c19103000304c8680d10940c07507003234055040070580d081d00c0303070010704100c00c121416402045000c0c14003816000ea800007503c2000880d14030607070030448004681d65040950703540c180320300134180140c0c0010840d02d0350001591 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 249309325 1250 249308075 249308083
    0xf010e070c0b0a0b0108100b0412020f0a0e0609130201050706090503090a0e16110d0e1225050f0d060c02010b060c01061d0705070312020f0d050411120604020d0201020a0203 76
    0x583d01c18266102c003102185940d2045104c2c3c0d00c8085204481500341c207000e0028031600c00e902c0351070715840541e8840000d40d40c0ba410324660720007000b02858984c0345c4d1103010b141200f1084a03514450b0200c1d10014205a514004100e01c441e8144d4405203082c0c07030707590342000505009000780e0300d9120500400c645d648540b420700002e0681003100c0340b000d1905800c05920345494220001c01c01032040218282100700180350741c031442040c02c00074034062003000418800304020744250f03854428044440181c0fa9425008a41170b402000c4100c1d07407948490034030402c10018950203400044400701040841c1c815800a9815071882c40003180b0504031100058882c0c006090260681c1d56074602000401c40404000017082922240c000f082c0c60542005003090007900742c05000c0c0007100c5101c800c2d05032258103c52140203401400364980204002000c02000b08076021541308071800c2c04040b07107181010056140d5610000105540e54495003488545c401d0b14174102c0c19845a030b102c080040c0c4d0148 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 249310575 1250 249309325 249309331
    0x906140405010f020703080112020114042301030501290f040303110714010f11150c0a170c16020f1f170610081008030d020715050f010e070c0b 63
    0xa001000241498180070342160741514504a02d244100201400640c106014074111080d015003480109228001600d00608117203000710b5030040007401048180070041c0d40b482d9888510741c01c4444c01d800c1c80056013107440131301620004a8001c451004a9a802d50203d042d042580c500603040180d03e00000015030025041100855401c0128a2401908100580080c09450301908800302104006851144040b502c1c0080004400280400c24020030446900402010b148081803070150501c0b580d5410030700e005400610900e9000000055021109000f41a080074441c0f6001043c8501e441c4404206000c1303030021072103110803c1310350310403034811803404080fa13040f480f502c582240144028030071715244146200c21824070500c3d03220750402402160060814902c6501c401030b12900c1981079512141503480002102451030301c1680180004621500322114201e2081d1a10401c0d070b0b0080324011404194140104030040d952190307160090782c02d041039482c0d04115142c0c40039441d411 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 249311825 1250 249310575 249310601
    0x90618022a0a060e03130506030c0403050d05041502060601050d020903150a050105031c0e01200f03130e0c090405101206060f05060a1d131401050405010b0708030112060906 76
    0xd02c202009000c3c01e800b60500094040000c0d41c90800094030499052885000720b501404010000400940e1104115000380d034001c01119080310886000812940c0b01d40196040301e404a000b0b1b050081c0002245406808161203190520604000e0b10b8001d4102070074103030303252251003110b80164030303030000441c0110103880c004a401e6052a0a16141c64110800100c0060341c00306100703103003988568180e02c0040c017468940c6030840303000721903041c8010280d010907044c011388401d1080a40000010070584005041911403180c0c1e424801c0c104000c101d96082c5140c00820079403040e85065400341b54000c0b204e060802849455140d4180b40140800084130010342e10041406811030102c0302d80d00030441120440d04c4c000c00010700800900000120100101e584400403016039101c0c850071400148051040000203400009160f0a200c00e10405015030300c1c040007c5090403070101102d011580201c0c501d86181d10f0001e5401400f110542c040c1c411550312200c140018481d0301400d0070070841 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 249313075 1250 249311825 249311833
    0x905090606030d020a0f02010c150c020c01021e030d05091f0b041125060e0d0503040b010b0702030307080a14040e0708010618030602071106040f0e01090618022a 71
    0x203009043c0703000040c01d8403a040d50b00c84006100000e024000c0c6500e415828649203810540d1803411101040a440901c44541e0030308204150b01079000422507100c040c260b00310b40940c00c17800c0320b034280a05008202e44031a04100300e00c0f4000c1400e82c000c5034101c10014100c0c0c2c005c0c4408142c0200703d071001d01c10a4540c0f6120b90180b002031030b090050340727061011100e9103883c210303c803c0c0956415069903050031a6600d1601080103004540e03001066200075a8191540d6006624008000364422a8220744010b00d4100214040740e0341003d403003906902400862900106844103506900240725000420044840340b107140c00e490f00140005120340b462007483c50070103100c080e1030400141c10500c2040101c940698103201500030358022250498401a03a81545051140e90304031000011500f0bd0000100046d01580400400301103515050724405640d8840e020001503890901c2040900c41e2103049200c0030030b01560081203242e1a451207240c4146000c800a0420740358480d8524a07900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 249314325 1250 249313075 249313081
    0x50d02030f1e2a010f031407030e01060f0608130c03050703030302032a0a0f0306090203090a03091d07200f10180210031112090d0f0507050d081009050906 68
    0x30b000c100c26010800c4444925a02d00c514440c20b68072030342d08600c035904104070111461a000d00a41c80124030f1121016400c8641c07a01f4040a009003052101c082c90b03943c41d10308001402c0001d0b281c401c1c10380e0502c2d0340e2910303661955400700c1d07030088656400703460303804111000000064007000044003c6100351070250301c0b86049072600400b00840350f110350142d4904501e02c5d42c0802c0c8081102c40c508400c1c2000780040c0c5813800210014507103500405c902500c0001803001d400400586908028840da8031050801c0d2a40382c0d89418a07040703441200c08440f000c010880701401402000344031080044484046850b15104e00d1502ca4006c003502816000b90f5459000e00180d40182c8444201100d800005952954081606400842043c80c01c0550340c1e110022020400d604442d22001d0200c0d090405040000000303444102e040c0190020401ca5007803d912280120150340d0b289400801501602110f03c0c0c058416403401000c03110344503000900454003c10521815000310341c050000c00484c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 249315575 1250 249314325 249314383
    0x152303041b05030615010302030702010605040228020304140d020f13291e0f2107092c01110a03051e010e150a0e0403080f010b040f050d02030f 63
    0x8541d9410841c003981041c0c040020074074080c07000301742c0d12000b0b2800580c0c0c2d03940e0500813801401d00d604816030150001901c141d2010a450100004c8403140e64a40c0c0d81d0403070590181d92320f210381c3c810f20015510168002031680f4000540c9403030746002508058000c2c0020700040d03071084605c3c030a401596603038009621a00c03400d04101c40c0074804105421507a51080340020101c80c0d044040280b0300700da1150389145926a1210340f003204901400c00740c400419480e1070081554416030889941c0302d034034000680d0101c1c0d8001c0349080c01c2103c001fa00c554005403494031440024480c8103c55649071415844682c0c09400280b00021707042d58002141d040161541a55106040f50a005c2c03c40280061043d107080040c074a80140d0303072135268100c03c40d40301d01007a100c0d18294851140d004001d401c020a054010710f48501c82d60345140e0b96649030303803034844441450256004c3c21400d54280340050106003131441e04680c0c46400102100c1e14864007850305443c04c1d902c010b01b00b46401e54904803920f03103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 249316825 1250 249315575 249315623
    0xc0305090d0e0d06090203120703050705010c0216090930031109091f080303040b07020f011407140405060a030617010501080d05030a020d0501060f0f0915230304 71
    0x20401c945440c1014000c144001014030062000261110f03940300b01880031036800300045a07160b14030707654054507503000e410054541c1d001070005a426500b03200f001c400c0244041641c0c10785291520b540000c40d410050341c1802880b00442c02c542094140e080081240243c0310306110f00143e0019a1105c1d02d0010070003011b54015101102c10580d091080c0340c802c0e55800c8000d9409a80001d20150f8a9100800070f8030b0a203803039102c040940000010300c400c0c80640c1b500c0c03910980a40d000c49809045a540361402c8901034045602e100011a022801503849906c03542d0086840d01c00080c00c154848001031001e60004d1202008241d88030000c120310541c0c3c00d03054828500a400800c00c80d03243c03098071500c40c429058000c04201d000030000780c802384180d040d0b07240f17588808810000c0b580c407800f0203800ca00c958540c1c14042001000454103540c442e004600544800200c9148841c883c2d0809a5805102c0031040504503000600030400c00c262070b010398401c0380512070203204141c0c849022000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 249318075 1250 249316825 249316843
    0x605130203040b0f0403091502070f0b03070801170f150403030b241e071212060612020a0509060c03070303060b0405060a0804141b1305100b090103020d0c030509 71
    0x59600600030000424002c01d0403a902c0040c4610300c11070390355586422203010100d5041f40c841b038500e80108101040d4001100710035245d904a0040c3c126480b6101031010b07000882d1a00002504200103100086150344801185107607001124000c81520101500f00421250003101d201c0b84c6004100a250341409113080488099480c401e202e03070320180104584212004400c0350a800042060800f0f02c429502c000c2c0120241c2844c0e03c600062411f00406100d4203442c1001030500c0301800c1075294a03200e08001c842064545d550107800450100d4041d401c210988028044140414402a2035400003040d43c03002000245503241140c0c40c002e42158115005981104c0040c0300600840d16484100c3d5070000181c04c14908580c0c6030b01c1c1c0004004010086a5030307501030300344050b02d2000c0440c1170130001d4800300c41d00207401e030300401d0350012280100c8400c080c6100f82c68017042040c02c05001040c1140040c9400f620304141c1032031004c103075000c480400d800250b03244104810b0b00e405000c5003403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 249319325 1250 249318075 249318109
    0x180503030c10390c0209010810141e040503070206040e070f030615210c03090203060c131701060b0a0c14070602060105060c070306140906011d0f0919060605 69
    0x30042600f100080004544902410703840c440c00b039208902035000c0d540707540c041640105508403660b141c1c0c21007600d40102c40400c82400f400c0401c54203121310441c012341c1c451441d20020005d0b14024482c07042803001c01400136120360008111100140c2c55100060014282440704c1d21441e0030302c141d00038680115110300004040c13034101c0c03d1188401022a03011941c11318a4a00510000e030420100b00c1c24114090200e11403030304d0000c0781119003503006000e40900031030070b45105980340e98540e9202d101c0e213202e030700c1e150007003080c2844040d840048440c088240348000280141d1500f01c98095540401804401b0890701c1c2c0782001004a4460f440c414001482d02030244945001d6010350303034050601030613109402c081350010000c4003c02c039800046800c94000e1010180c0b00c00394810031001a01d40100700d004100c008298420106004181900f15072411561075440c081d41507401034016201e210303180075800071071f010b40f4000c0b0380d02e0503924000c040000321985010100031070b003207441ca004a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 249320575 1250 249319325 249319361
    0x405011b050a0203030403030b1f09090b040204030503040e09120304050703020901050d15020c0102090405100509160203180105040e150a090e060408070602071205030a061410180503030c10 83
    0x450b5a94040103403a009589814041845c40c01000000d5850501030301c8460701103c80c44d40306070700513880010034013155881c0310108181c58041040c80164482c1d404044d1003940b007000308000b1000f0146041e0b502100382015640d09039242041e20955501c2a9025550b941c0004000e000b50300d41115501d0061a049a1070061a21140c5e100203901d1556081100d2040d404200e00c11944000c1d0110703003007968020000c12507403074050b440d0401c52545024150151120000150072100421400b64a003001e540045d811b00028064002da2402030080c0d0904001341800009032040f00150344034007603440d4081d0025800c0200e0f06000420180b544500007290070120b010030400700116405400c560080070f11955241d0a06088010f4868540001c0007088490300980d0590707844000781d030180074100070522000d55a000403a094282c0b25110683c010a42002c0b00410b9004a10341d00500d4081c54030000d03d5a41c51001034110740008500358042d80002000c4d0340142d074144240c10103114504001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 249321825 1250 249320575 249320587
    0x420040b0108070c050304080a031d010e01080f060f0604140102010f0501050a0302121513140703170306040902130b031603030813030908060c04050f09010302280e0405011b05 77
    0x20b008600240040f024404514081818800d0620860380070f03041e29800c940350a1681c0c50028080c82c1007a440b00c2c400d80301050104080d40c0318a001e002103a005039503d244036100c40041c1540d07070070042c14481d4012100c24929549441d5103015000a2a1403428601c05c2c918903400a402d585110426040303c1e132030f000c014081caaa96120300410f4a0701640c100c0d803520250302d110f0b071420782940401c1c40d405001104025400d04068100d04040d4031480014980107000d21040780c1ea904135000c000c0421565512003600408604003950b403205000740702141441d0240c0106110014001280112584880204005090400007034894580010700c00b10b20034a5070b14024060403018105991030704c1648540001d15204000ca480030306550419200c103400c0c404c98080340359105100311405140c0121101c0d1103450103814550403290080c0119407401a0141c060030a0f040000e13850313103900c810b08000300350344c1030b10354215128500c100c0000607406100e0f003d100c0407141b556484002c1200030401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 249323075 1250 249321825 249321827
    0x519080105131d07080705150a0906050706091403030a061d072007081507032009010908010f050114030303040f030302160f06090b010504060602120c0a0b0420040b01 73
    0x4404000c0603a1400141e0600f6070700c03844060701c0c1c0b10030a00d01c0c511a03000b010444203000724003070040301c1c0c080740c0f500e00c018001e58503028a4020080c121010608040e020400c1d03030701900c01005100d103e6003000402d5603640d40c03500840a0242080f4420703900100c20450541d284d40b2a500207408000d048c0210350410070100c40c40d4240003003090040000e11120720044c2200c04015a003e540e040e0180e9098584552909545500e5142c210a002140d040400d060601901c20464480400e13096400c0c03040c040d0500390380300d0b84003131811030400c0002d82000543d42c40030310440184846242d00418194034080e190740c0d48012000c4294801d07041041400001a91000101e03806503041c1000350312500c2401c058089810742c1c1300c0c00341142c2031450054007040300e180e00c4901128032681d0f088100e170b42ca8001f44000c0340c203c0e00800d800369000e40c2d00314629400803405456010f00c1081103034905180399880019441e4103660807540000301c0302c13903041040c0c0c42206210100c007040e1001c00c8a0202080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 249324325 1250 249323075 249323089
    0x2010218060a0e060d0507170f04021005041e080d020c011b020d02060a0e0310110a0c0c050a06110f0c0105040902340605090604050a03050d0207020a060519080105 72
    0x880380700c1c0d600000e01c0d02000d07000c0c0d614803280c0d68004002a484445440000c0701078142181d01e0380c0022804e2603601c1c0b00c4107058001ca402210aa0050502c0f591180c2c244900c2d809004190030901400b031200040303801c006e1032645164101c540d0058061842e0010541c038020f030000c940019900031110030081660300080c0c00d01704110184002d00000720500104604c96080700011f5003100300000c50064003900b02104040f082e90039400c803034103503060100c0740b070440710904583d4418132001c1204402080c4246011002c0e6030060349032400e4156241c00041c1030341c126a00c8000418015407445210782070500001030b1000404014001309d10bc07907800248648164000c5075021a400314105a03540d24a16406028880b01822204100b0078000d404060120000044400c1d030308040001d0011540452464050b650150003090012a82e6806403a50741004000480d01a824484580580d807560301440c02071101d07840312503842000c40c4030708400e00075440040c1d060045000c0100b0068458503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 249325575 1250 249324325 249324367
    0x20c060a02031c0e03070807140105040c17071d010e070e010912050c090103080d06091107030804050a0b1f05100e0603060402280e031f09030c02040e0c01030c020102 73
    0x50004001040510f201c03078000c10128100c40c6031840041079810030002c0c000f00030008c180c014114040c018002c940120300b41ca43c1198010001042410b04000107400050101100f40c282d1082da02400d031144e400c0030070740e54492215200740d070001004110844900c0c421a0f040b00162902c040492180030020b44005014850f5540d1005141c2d05103040c058140030b1180074890050500b183c65940741071040c0113411651a0001c40c0b890084005041a030324428089030320b40144000e41001186d0301d041d102e4034001042903400780a1540c1c0200007900c0b005000c2d10a0b50381d5203281c000c6441d076919640c6810155001540280c003040b400c1c0d10b1450f0403688404080c0011035040f035899aa40010030043e005410703961144041041c2c0401003000ca54610350740104140d0b03a492048401c0000b056070f03901464268984603407030303034404a071852000d800c013400142c007a09107042555401e502140448868003000c0d01150818042c806042da03160103016a20b001c548000d50909070040c4580503001048 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 249326825 1250 249325575 249325597
    0x611120103030c030c08030709080c060a09090504060e0f2b02060406050901020904020a03330b0304020121050f0c0301062f010e0337030b0411030115020c060a0203 72
    0x20f0340b2050802d8415480300c04980c0d40025450b841f802c11003400350280c030540c01004598001d2019080040c2040350a58006080d65030700c0701c0025103082450401010302900c150f45a0b503c2d1001040440410003201200d40c4107400103091401c4280000118880049034244001003404568100c0704c0d0300040703a507042500682c0014107a1a10350401d4028401c000505800500101c0d0703062030250598020b81d0080a0360205403841d1036111040e0b4510003094400c0c3c3c80c0b0052540d002c0c05012000c0700915440361040c1410410860361100c0c2403951000c4458035151251603208000045002c1055a5040320001402d5407c55040000252292460084280310038404040a262501c40d000c2c021203540c0c5074800800c00c074903800c0c42464486e4070100d588030443c180d0007040506130081c0c50400d0391100c91220b461850040e000c1d0704801030107480404561140d00c0e5003c4003081c04441000b1030003800000b0700105c01c1032403050064104680703042400c0c41481c060208164580d004800c84510a00c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 249328075 1250 249326825 249326837
    0x1090609111b0f070f030b250f02010b04020f0315100f0c06090c080325020a03030e130f050a11070506040f020a0b07052d0709050604090209090703061112010303 71
    0x2c00030380c961508402142d542c5080c41036010009800e0607810008041c6c07802203440680f195506140c00780e002124503034010600100070710620065210f9000402d4282c000e100214107055214001007d030f800003001000900e9000003807185000504e84001c08801003913514103019014004013401e094240940c000503c118102d051041001d1036000c19941a405821440764030340782c40038656a43c01905180d428003265405080070489184806603810350b004100321211415542c084030340000c0c3c0c003050b5070070a15512006403078810070b0103075040c0110b00350070014003458003030101426110041c44610340d1680c03c0080300081100440c0c0550701503009044001c1681ea01d2020494051107030b0b100ca0346070340c00820f40384104040490000d590180c0815480c44000f01c04545d1039000481c0c0300e89281b1940086d00400500c05035420442d0300003402000000c28070010340104e10280d5044890703000070b4002c41c1c0140100f01e594840c0c034500b4203a00e2095030800081c0d040102600c801800041c1c24469 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 249329325 1250 249328075 249328117
    0xf02010e0d0b0c0c0d021b01050d0f05090a0201020c04090305032d0406092112050606040b0a050c1e0304061b0807120f08070e090c070b070203030109060911 69
    0x59044070300e4151603011400140d2072400a541d41e40c42c1d00021481001400b503015120061342c40040c1860aa02c845100c40071403d000c4401904c9903481480103410a03900d60b200d00c50f031070300303a441340a02c00e40c0200c0290040118500c002030406c0380600f0075510442c902801c1c5000700360b00c4020f03640d00c4410303e501010b02154a40ca5240400344400400040c07004000c10802004443d030044185a031041032401d50320741c1c800d400051540000b80c42071002440d00f020680c400c29441c0c108540110000d08480d191075140c1c00d002070658807205804010403c0016100c00d1450100125000c0c0d07090302c2e41e650001c40c40c9484141c1c4a02c9903110b21010040031925040d800f4030385907400c05945500081e5550b940e50245042100c55a40f41031000200b80c42004444c40140501d0314103108804c0c07a036404810f081e01c0010043c03082009800c0c60b8500c501441190000341c005400d150241015030002c540303030361501c44c0d42c10030307180039400501c0d000b03080991324150040e008069440c00705131070280f40c441c52 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 249330575 1250 249329325 249329329
    0x209090d0f05041203030e0115030309030b090a0209040206130f2702090a0506030c0d02030a290927010501030c1a0f0405041109150301060e03190b0709150206071101090f02010e 78
    0x4000c800e6209d1091130044000030806420510702400c5a100300c890107e980d4401c4030080d2030b061340502c0650003488800000e00186445001049844204480e55124949406c038814000c844c94010502c01108600800f000d9000030b985121200c0386907009518207200d02010400e6a0b07800c0c40340c203000310004804100c100c00341c2c4003610506c110341c4004644a1500307444000180454010108030f184071000840844140088034005609001c4c000d401c0c151507000001320711a60a140c500c445070420038124044200a000701d50095014840340180603041c2021044586204050640d159208111580b41200e00100740c904540d4215000549a4604203030240f0a11032100d04660148406d565800c45601034005141a10b2a0703035078500d8404828414540d540d401007190358000890850300c203002401d49201580d100e40c0920740011965901c042e0f81c40442c12822100000da0000030800501c00c1e8810345004914041034002c0c0909802d58031028109880c130350000e810003440d403025400039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 249331825 1250 249330575 249330581
    0xb091b0a1205040615060807090b0307021002130302040c020d1d06090301020c07060e0a0e2e0824040b06010c1e03031a15030f0709030209090d0f05041203030e01 71
    0x30251603200740203d00e450700d0714200810408441801024140c1c802099003803040d20154130804558441b08003c504025001581d90002841c890452107a54208034144215001402505400b491065403546c2144104400d8481d41100f020840d800300c02d54807480d59004022403440200741c80c000e000f40007050041881e42c400c0501e000d405600001d1001b5816800040c03035012a1129074540510190b84000c11001c00c3e05071240002d276a00a80104d40002c0c409001a01002c2e200d02086085110000001e00410940c0d4018034064112003540b041c2803070000f2444e440c5068481409600d45040e80d00c500401101074410303410001100c400008009000242e2014a00203004404020b0030600e0000c2c00b03440400900982c003078924502502a0801c0c20075182d000c10012041e9085a45100000810800c000c0113441080404440000581c542400d154001c1c5925030140a02d1041030b40041c00d212a00050102045401c01041288005001c0c0c030b090115031624010030f030b04500c1d41d022805 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 249333075 1250 249331825 249331847
    0x503060105031c18030b01030807060506060a050403060f091b17011407030b120601090605030c030109120f050d0903090e150a17150a020a0215010f050609040f061502010b091b0a 78
    0x406c41740c100040b00740008400900300240c442d40c4240140e594903014848180668008440030400600041c800120710303400051034100340322000a2604119102c21003204644074000b00412280502400064500303407580303908444500080c0148000901d805003400d50090290301010741d211b51050096585025030052881e0311340c200d41d090b5854106100c0201003078420280301c0c0c8950140c2c00100d050602406084035009003071030030400440c0703006413200c0c042400303441c00b040801c0241d851600024428000d00c2c900958502401504151200d010307840301405440702c02d00a510b45202c956101e004642c1502e0604117020900b034a2113100518001100d900014080f4509082200c1420140c0c060040351006508030741d000b0200061412341c2650a01414002942008050003942407546c024142c0b904064000101d01e642008a881201d5a5411801c00001c2400b101360105030f090084041d4203404540e10342c2c1d00d0601070400401940078107240c0700c540c1d00100d440e080396405030f201ca1792 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 249334325 1250 249333075 249333083
    0x906080a05010e060907120c0e0316080a1b0b07030c06050105041401140d0812040201020613031d0a080105090106030b01170a0b06120f030703140a05031302030f03070b010503060105031c1803 84
    0x11031075441e01d0b0081d00001889c180c540c0a4032a00322203e4206022051100c11030704240081c1124010301d0715400007a2107005650034000c0e41d162000500305044900414220740650b50300d000c1100b1610340345042e1501a0b001c20b116074203240310600742605007118581120702e6154200079030fa60744400b141301014101c2001e4828440403901602c105e1510942e40e01c100e101342e0aa59840d030b00d003840000500711441010b0001049020014800c80c0c50b000c80a61110b0014401700c5080e036a0007000c0d0a480b000c4031844916512560100104102e007084c0340d01400030a54826680b044000c02d0590324844c100003d400300801c680812510740386c07612051243d02400007600e01c00c039100004140d50f5408030f001140090100820010b0b904c0c681010788a442e859540e1f0b151031a210030707016412007402c1400a981c50f00400319100c0a9100410041c006140700e103445070402e40c0f41408150a00d001640f145000c0c3c3c1050000d00a181201c00e0780d2041c04c1079130309000c80360081d214040d107040016600024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 249335575 1250 249334325 249334331
    0x9090a1e050a0c030207031713080705010c020111250f060c0206012c0c0d110316030f020901140d0e010c1d04140112080c0d0906080a05010e06090712 66
    0x30003011081d005244200d01960080c803c0003003201c001c40880c452484040c00181e180544401d0b12110269074a410801c006208a00d10751943c44440c541e27482604210380070b0f992560000181c40d020f015650729000003103000c40c100720380410940034100c0c483c003175480303d07101c141c1203002003008c1121480c4603160402c80802101202c200003943d603010a000d0408100301568403200f50010100d100820324039202e000c29403a44070b00c240100300c0d41100003418071894980d6080d29800c0c881c2c5018600c80e80741c0340e403003011100788440040d080780c05852140c000a80100200d802c01c2e6049050002d150900c1d13180255211441c051100080400c0480d0b40000e5003018002480c00c1d60115a0b00004d41082282076805503118040000300d03400329072007210542130070004004012110b800c00e80041c0c05400390030700e0040050692800c043c4a8402c660204800200a109160340103d035141d0107a9194010050b41d410200e24258081e4020147c2d8421201880013488051068013000b4000002e69424 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 249336825 1250 249335575 249335621
    0xa030515060a1a070b150909011a091509040f080a0302040906080313050402030a0e0a0b040b280f06030203190b1005010c060203060a030b0403020d09060804050309090a 74
    0x10306200c042903900c0d610445035120041849006a07004140021141c82c0d50340c90000c49503103040c03c0b0103008200c0c0301002c032191509015500d440031403510034000800005031419000c03121100c640c841201181c0501282400c200307001080495800c00c2c2034088030328800942d100d2034008900c81000c08001c0c01880040745000c0b110703425030054000e8070103040003401a00e07280d11440340c1d2405866200d000c071803106581041641860350042da0041e90000d03000c43d032041c484001614049121004682281e15802080140a102e0038069003060401010f00c0c04074524443c454840c0c070701c8110304a24580e80e00810342520305d00354080401958050199100b90251103890148a41465000c2c0c510441d480e000441c001c0c1405e81c0242641d405071503c40d540941912010000d4100400e600e80080070354002001091600b54031520445c441d50040010b075881c2003000303048007001d5000f1000d11403000148800618084184c1e100c4900907141d03c401d507030f2801c0d078401c041c000043c0d80c614840410001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 249338075 1250 249336825 249336853
    0x15030a080406080c0f03160908010204081e06010501080c300601020111030702030703080a0b0303040312020f0604030c030c03120f0b0406050a030209130812130302010b030a031d0a0305 81
    0x15008582c02c2d512880b600d41d03201c91007008140701705403480c0d4509038200002034807491405130310105110702d4a00301c52480e4a403009182240c1c416000404154000130549401d1850035098030210303c022405016103500d0400080e03c00c00018010207500840416011321058030310781c40c9800b68184411460000b0680c9140f002d0402040c0e440074019401d101120b0300d05442c1c5070849000e40c0b0b440c2e00071858000c0988080302c4900300605071750f842689a0030350070196075003040a000618090068031000440040c406071800f64034004000c01900101e0800021a8221920381e92854240c101041703022201d1030211206962034040c5601d85180154882c0240c802c0d0340103102110742502e04000799a120307000c004025409210082d13010a41b500001c0c1e441201012800000c0c3c07180d20781d00c0c01c0400305070702038400f41c8040b1120407600d42c0b1800c0300400d055090203a040341d4030043d000748c20400c00685008091120b64049001d0120340001c60b4600c0c0e455a0800800841c0c100d01940d89021f10000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 249339325 1250 249338075 249338077
    0x12030501060807030507020c06210408030f130201020304031101170907050a060201050c2b05070507020a06030c022d1c090f06020a120c06140115020a051515030a08 72
    0x2440c0700040a00c4000342c030640c020b120745170040b05a60000e04010300c4660400070307a03a0080d002e4030078500101680115800240401c28082d074403503850760380c49180a01c4101d141d15402001c449001d0361060003c000340c2d17000300888050700d4001941d03801d07200c00d17403005031007d00b0260600315424004000f04400c0100104000302030700c1b01105c8201c0c02d10b584080403800c2e160199940b40040c1c0c001c2007041c0ea6440c1c59003800c02690100004810346600051640c000c035202142c001000c1a80000c0c03000840c645503500d1005000141010043c00b822008001d5503811201414140f044900700c02841015109607100540846d40003100c4007043d8640d810302401c41a125040c0c0821400503022440e04a503880041c1a83d40359401401500c0c61030b00c030300680c543c05983d40c50600c00b1b2040c0038400f06900e030117a6180c50101107580072055240004030588101c40500e44021504003035030003c0011008a0700c030140210b184200d100d03071346460320344444a41d1a10045030b40761203040514410042c0c040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 249340575 1250 249339325 249339329
    0x51305030d090b0a0c08151f0302030109060603020301060203090424080f0d0309050604290a020702030c040b011d0312070f05150106050a0810080115050a140d02061612030501 77
    0x290100c0760f10340b901034820050300c800001600100f0300800c005070424000c1c03c180c080041d4000d18984952600b01111449081c7c10340c481400642c000005000148060007030300028582841c04624543c03600e10001c2d1a070080d043d890348030390b480700030140640050211496174030101c100e4803102e86d90f82d40490f9a4480c031214400d0050300031840754100d028060710882c40059044806000381c1c0e41c43da036900084050180004910141d50005201d0070700d003001049110751083c88005a032100580105454013200e060801d2145040620700f0445980c000170410020700300201094440078405c0c00241010f2030b40d03c413046100c102283c481d080c45400307461082864003403019580202e9100d00b81f4420071009026100109400700054003800e8400c0c400164829030691600c030300c0a8440714018250703130020303402003c46a00740ca000d00862030012810001406042d40c2003c01513162400b06080c407500b554061301c18100441d02d00c01d0514902d580c21405644407205030340e002101140500109028 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 249341825 1250 249340575 249340583
    0x30204031406130f0503040e0429060f06090a05040f0b10030b0105120403020c0a1e06030b0a09150905040f0309140d02120705150301080d091404051305030d09 70
    0x9491008070910101c1c032180214242d20306412044102d49906185100401d0102d58a00c020400098143d07056400ca9001d80d22540480500c0141c1d0004404446e01c1a010001c0515030b440501c0307181d07030310341303582002c5880c00346c0f400d6499019641c0000c14941c0294001c0e9082400c00803920303207089503030f44000003980048403400740c081c244140c02c504944100c0c0c502408680100304841d210040043d50607405446481125688140303103000c40d004040039404648003210225112813140016150340010b483d0b00d140410002180e44005032112507030b80700301c10540d6962011008200045400403000d00300c0a0b00c00d2155042600d00707001860300c0c120098002a101c6180860800d03800150b00e041680000c00031000a800b507000c00010180404090300d25101d441c90002d0241c5421100120340303091110080d40702c0d0f1410002a003844a500c0006080050040c814020780c2c440307100412501005581c005002da4909040d400c1030080e10038040c102d4170001c203a080c0400c90340e41000003e5441 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 249343075 1250 249341825 249341843
    0x3010803042c010e0c0405040207051614030703020d050c030319090f050906092d060f0307030803010b0a03090f080307021005090c09060f04140403140406052704020a03020403 77
    0x180841121440c400c10b000480b69142c00010040e4a820142043d0448001094146000c0d55000014100da0040400312070b203030495a61128911003042d40c12000340803105121b1590740c0d0171740020b5221192404028818118249408144039040041d008c3e64100601100d544010403c400c50380d07201180a4080050f03a007120215440560410502c112800908000021b8842d2400c015139090000c0413003000801d401075400c034a510224456008607161690f011282c01c0110034050740303011111086021b40e200180820004403000300701ea04603460100b65584411080303004030042e044c014005002010724203d10b42c18000d0b040300640c001c4209400b221003c030410954481a580c01325120501d907004262100e010341000b01d030141d4451030051515002202c00f1000804603040b44450741440c0c03001100b00410903170809046214282030800c6981001d24201c00103081d03108a40540d4010007483e0200f10000c0315061000000740d038014001c0d500c0d43d0074000018002d402504c07094a280c04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 249344325 1250 249343075 249343109
    0x31f1506081609050904030c060902220f050c071407030507090501060f021209010c030c060504060506150c030a26010602060604180507150507060507030c0e030f0703120507080301080304 82
    0x4050300c0f00f80100c401c068100500c503521614140d4085030030303000030784405445000560046c0d6480800c2e0841d07a04000400c50b181d2110303980e002c11203041c403480d07402043c980004e11003800a11410395044075804001b10000540410302c642c10a8400d42c070040c21440750725408101100c154001030b060307600d59900e0b2441c188405400300d84c0d0f68031582d00b200180900700040320165209404001100c0c0c007a09104090a01d10340d40c9400b00d8a00312810303540181d554061192601d45003c3c2225501e265010036030802c800341a03060388034030a001500b000e01440e070a03840701074200600c44114004100300010341940e034a42010352100800c4a95a119502d00860095400f684000780b0f1300180e0845c00411425041c50b103d20b9000c80c1e03003000d40c414003509001c00d800259030360061a01c110400da40c00700c1c90083c0540c0140c420f5203902d8080c0e11907003018006502c410380002d0385204607500820201101401d03507500707807854820040054054000040007203070044e0000000d0007102e0381c4040c0c1800c07180c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 249345575 1250 249344325 249344327
    0x31509070206040b04080a0525030f02030304150c0c02030f011b1809020307030902030703030c0507050402040e0a0c050c030d0605030d020307150203040602090a14130b031f15060816 80
    0x5048400815400c031001c04200456886001b401600131541480c914103c49101c0c3c1200d09c040c40c0d040b01205640d001042010980c0c49996220003465500003542075003001d90f9280b03010300780360020300011344d541c49103030010034483c001d1707007007140d401070162041d520200424a01800204541815a0440302403100d600d911076954521005004016401054141b00c18000654001b6001d2000c043c0c440e03064101580d410301448004603c1398030b034004102050b18000b4101140307944541e1180f441440208040c001c41160f80768029000000000c0540c0005400e503034034003030350002800e50b20000c10003828031461503100c031040d6030086003141d035143c80001d0200e80da840707800402080306000000209030b8030007036000740da0058407610700035061a4150010a00e1280650b0104014041c1c6056260300c81c00c26100a00300c40040b0a0140100c840d1040400d81d510b411140d00f01c05030031001c0c0b0051040d2465840408040c0c9440c03c0c0e001c0070b540e20f0000404001d015030b10014403092603050900c0305 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 249346825 1250 249345575 249345583
    0x8150a0e0703170c07141503040204060b0a050d0b0405011512090c080c1e0d020d03020c03100203160e010206011a0702030d050705150f0705030705130e2d060409080f0315090702 78
    0x1130100a00010f0203001004247c406500050403c0f41c010f9110f01d00414014083d40203802d6801140d5113840c3c550309600050002d03242420015030090785458014000854600da41c10040c000c1e50030684541c1988000d9000103040301c11001d00b50290400000c04c5107a0007050b0b40d008a0001c8600d0408094403201c4035007400220102e0075408186d54161000500741040c01c1003866000b801030301c60100302040400e007080000201c9800b665170020801008900b10304e0f024100c21500d1a10084e0b2030344042c0040d60703409060040c0c04d441c0410800c0c021113003c0307600c22140035940c040d00f900c2c0c508400c81c20280142c0c00200080320fa6005808480c244c00e00f08442051203040b402d0000505038071945001c0c0c40075070020700030b002000020813007030074443d10800e031081c010018103140c1c29071858804580c1c62810000b0035040c00762040141d06401155503140c07880e82000d011036000440405914299686128004d1000041800442041456550403050b000f64050940380b00b0004d0352070940c201d8607 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 249348075 1250 249346825 249346859
    0x6030b01020114010b40150c020904031202130306050109110f030f0411041508060a02040f14010504050d0c0518070206071812050a060608150a0e0703170c07 69
    0x35041c4207105048100f2540e4070051141c07100c01d2080e04250000c0d01c0c000326208145400e8122240340280100207c504030040072509958610b040302034028145d0015041c0314000d40040d0400143d091f0100c000440d55044440c1d00344000d01d0303c0c80c2241d50740fa041014103c00d2162032040340c500b0004100c400041030480305040daa80b60400d02d0341d61008000d41c0140703000b51040e60407101b522441c038100c0d15641f280704e181c03000c04402101c04901d4042094501704004061b03104050050104010ba40b40c254507800507200750780401034807021900012240e50040358820303648034a8a1000e0030a00030420f1240042c0c0340d0a88035411128420400c030500140e0039203100380103030320040c0011b9689200f40821510b10700308031040500140d452060104080c07051005940c2900050012010004288118001841104050801031100105007200114018426002607460b44c24002119605014a50140d60301080080d01011801080d001d560000441c00c05280705902e0042104440c02d0f051540c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 249349325 1250 249348075 249348089
    0x105040215032a180f0a0501030b030f060f0a05160c0605070c0203061501080609061c0503120109020702040c1817010e06010e040b01090c0e06210106030b0102011401 73
    0x280007004604038011507480108058941002401803010302c0d1a2544100304000940f0155625242c03100c0710741c40891460059188144680010600c15440e10801c0c81d04451003400d000424a1810011038200081c5c512000d807140500c01c10840040c521402090207558990010081c50703a5511018030b031600182025008981545e14042c00285079420240c0c0c0600c103840c1c800c0210400d0303400301c0d14000060380c09404600300c00303c2c216902d5a0081515a0000d001c640500444c1428404101d01180381d5003000340c1c2d0391542118006109042084456040d001d107041d0380b966030f4403c0292300a40082804900c15410080c10304000c80c4188442481ca0744000324000c0c401c0c0c5030491410103207540d03d07400359481d500e60300d80e4041e00320103002d07a5000345240f00f1528182e18181c681021a100141c1000704020b14003603809804e00d40c4500030381840340003952055030300c1c1c1200340345010000c0b21007046018803460900103e801a8541c01003022100d01b0380080c0b01402008503503141200c0c090080c11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 249350575 1250 249349325 249349339
    0x806070c0206070b091606050405190315050705070804140a09090b07120603150b01180806010e06010e10200106050f040207080c070303110c120c09041b03030908070801050402 77
    0x4c94142c40c42c031504811074004079805880c46030a411918031171a4000c80209030080340c10025800c080f0840d0402e2504201c4a204031411070356070404100769641c4187d0710340d40e00c80010328801c2c0110226040c0c181c200025a4440d940c64003070080c01c4c00e190504500482e012500018121290300074000c9640c0c2c060f8100409690307428040718203608041091226a0322020000003003508001c4040801c00984070100c1c609011200160010b504003148000c900f680c0b907001c000b41c00001c1501415504451b481080ca038542c0d1004885003070142401503841400110400f0040b50008000700e0350140048956558154842c0c0c0f2508a034a00d10890341c10810713000c0101708601d40356004000840c4100d4482e0b08011503403062524103662900100c2c0402e2192064804000003007000ba1000901201d13000c0da0080345c1d010040c0ca0b05081d000140c040c017020b0340400e00b0084149000800b900b000d15260f00416507a0500910401e20b40c440e4403224007801402140110040c020184100d80150201d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 249351825 1250 249350575 249350587
    0xc08070320040303051207050403050d120f0f020d050f01051005160618170901090504020d0b030118060605091303110c10090503010e010b220f02130806070c0206 71
    0x540190000d4900140c0000891450880d01007181000d08090341c000c0d50341a0300d0300c001d10380072040b1a10141003042401814401000000c01c0000c61454030f000c01d117001c0e444614030b41528401b5141a002816a03e400d0ac000d0f02e2494580340d0181150440b184801c1c0b0a540340c500d0319803c109800c0c0201600b22401080ca40c940c2c601940040051185142d0250b01030b4950307840d20000c49050074200c0c1482403103c01081c045c03000782c1c030381c0c0c00340d003141e1281403840d01c140c200010b010702c00e0a01c1060f000380d4022808847d0543c1d280e00003200d5400c050020320944044084080300c9542d00041118858900340c404175003800c1c03406145111784c0111614007942e48598034191088000d012000200d071041d06151100c80c0c854100d00040002c00b512840e10355400c2000701030a4070624240c1c00301c0790b85441d40c219829503d44803611044180210030164076460741d588400507050520072120b01c9400000e10034828092108154115962081a1100c5c0d46524100316154440c0c3c0c40003940c441020321003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 249353075 1250 249351825 249351827
    0x60f0409050c0409050a05060708040510020f030f0601020a0b01080717010501050901090e0a050f0706030f02090108060f01050708030f0a0c08010e040312060e07020114010501180b0a03060f080f100c0807 89
    0x22040560096040b1b80f00b1041903507505141020844045001402200902c401c00c0780c100700502c200c408004082d8108400b81106100c640401011900d280003840c0c007050481e402444038219241c0c12012141c032941c1c490409690b04e0013144101c94004500a60b062101030041c4140c034180e03500107141c0455640381c4125800076001d105001c0505010304018940064410082c25000214000240c00700502c1d11001400700d071904040150f1280c010010b01015a038443c04141d4481b04c11a20300b0b12030401c07080102e5043c092640000c03c2c00c040042403102e6990022503540c854a0845000d100380c0c0307403182040710400002e204040c608260000441c2c0028000c5d82d6080b40b03080424000200142ea03001142c41040c030035518030700540d45d1005515090358000c030401d8050070342800c1614201c20400020f01c82c940017841101460075020030108002e900c0394006030300810030750512804203910352000c141c81c1c1c1d8411071030b10702030b01c6809094243e4840600550b08003001c6611400032565407a10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 249354325 1250 249353075 249353081
    0x110c030303040602091914040b0604060c0b0c04090c030b03071203021b06070c03060203060a0e0c0a050c160b04080106090c05160309030203010c020309011d0d170903010204030b060f0409050c04 85
    0x5c829030b1101010703140b11403861107a809440141505040c3c0d00c1044800b4090204485000780010300540d070400c030910120790403c580300203407a40242c80410a544008040d926401980c0142d40300900f0700902006e01c0b41e0540000401d0a421400c1d1001c4a940d02203032550003480134001000b50b040410a2501c00e2007040c42c0c5900c08101500700c61905d03090303a9406a2012980c2c00071142c6035408000c0c09400d06000b0400c1c0040c00d042120f00c40c1c1410074101101160182c28072280401800040c1c03143c1d00901844a000164004401c070b0104039101e00b0041659005802174101c40d42c81d00074001144034150069428404041d1681d0349404429111120a04c0c21528160203100a0720b40000060f2024841e041c1c5e07103407a560107140c4407069440014445003032050140f0449801c40c06980b5a1f0361500b50950301c140d03022612955481c10000c0c15040c6028032146590f041d4800725001003070240c0056054484ca408403852084020301c90704110444040c184050440d40c032102e141151400e15078 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 249355575 1250 249354325 249354337
    0x61b03020106030c0f0315090512160203070312021b150f1201061e110d03020c0f06090601060908010c0c0308060a030f122006040b040206121006110c030303040602 72
    0x4030000c034105072a078541c902c03440c2c0b19900c41030381d20350076800c10000d001c40400d1883c844170b082c000c240104c1a040d121643d4901e84404d203182174060000c2d40000900c1341140c01050301d07601a040c0ea10a590320308100c03001140c00500c00003d40201000d2404d104206010310f070240c00700505e072940c2030100842001583d0010a0102045c400030800c4503071030721030300f610349008000035038aa0080110592141c00030a540410800510031a06091100d1110105200b0320b00e403014034006840d6a00501010728002c40381611011a016960510124040c0450518103803441922003480d4590750f50b050b1803ca5484540b44000600354946070b5000034828135040e5000302000302400120f0392207440703502c60851009400c9841d0010840e281d00000d800620659102000780004c60022a0826a494681c030b4000c000414041803500010f0071580c0e5181565204010074000640600c0e18413141015100e440c05840e021900701c0c040b001181c2d00000382c000c0d00d010091301442c21519640d4500000c0c1d0010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 249356825 1250 249355575 249355577
    0x90f0b0f12090c03120702030613050102040302100c110109060e0d0809060d0204050f10092903090f1209030d030b030c04021314010914010c050c041d1501061b03 71
    0x800c1884901c20701044aa40180044006070469990a5040524084080d2220b50503400240700745c8003daa00071880381d13030051038141c10030380b498141d240185c0244200e030002503000c000c1c41a442200759209801590b803130700c00c0c80b401c08216000001503820050620130f040004a519400302c580b4207040c60319403d003610500d10310341004040000107aa43d08003601c020041c41d8045000c004503e010705025112440a980c40100c440d81076000509001d15805548600440180404c0c00401e0050300016400c4103020490780740d061038800c89850328100100c0c08007900c40c01c3c144031f1100b10170800300c0350341c402d00030300810982c10501025005818001105603142c066110f49001c03540781c90000b4200941940c1d10070384444e04210104128100e0341100604000340da403c244001c9250840d180b46580c007d00340514003000031f1404a2901e210f940b1010b4206040400202e20580c03049403002000000100342d07001c00356a0107900118400034803408000610040703500740156203840c0180780660103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 249358075 1250 249356825 249356827
    0xd02010c051e100501290d050a050a050a062304150905040b07030905030901030b040906140a1409030901080903040803122d06060a0e0a0e09060601090f0b0f 69
    0xc0c5403196030070092260302c2d0005450140c54141c248070014030105280601a076400c01c05941400b1408400684480000140305c404c5200c88010000340f02c1a2030ba9030010f410103100c1480d1401c1168060503041d10400319030342c107290118065900d14082c0305d0950b0b0140c16078004210388140340214064130031500350341060f512a100e0042c00510319030780c3d0160240c902d011030b450403d03180141c00c03000d00038038441c00c0520b85081080090f001004a601500091030b0104541c1400380001d4010602c04030014155480e050b40c042c034120b190340712a03110304c0e2080c100300300341400307410026840002110481c030341e41c1040280c0d81456008607084d540080091048a0405032207c4911f40303142d020541802d908000329042151110400c018180311000340743d9401200d00041903100c5040e000944442d210310700104404030654425400046990401400d8803a900d07130b20f2010340c05951094503c40c0381806983d0004a455000384501c41c21200303003040d1040b1203403805500c0300b000d4100301d01e04858000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 249359325 1250 249358075 249358097
    0x190309050c0613030c03061a0102071212051b0a03021908160303020c030304060609111c4107171902070c061701050405010b040e040804030501060308180316050d0201 73
    0x3610307000217011b18440c440008168100c072290150700220800c12030b0441d400040300380108404541d0b0012807070360058a506d0302e040c6081003a43c01e070040004861a0014110850403c80c01c00100300024cd4026000c2d01c03c00344404001d09030180381100701030145417040003c1445000408a4a4070745030092400500b0006108109802c5900a98040e55801e4171480305000030b04845c0b00e104040020b440905d8030f41560703610010f00d00c6405001304141241c0e034100c0030b90f42c0d480301400000e2075030000d520014050b060031404030080031480c02040d000c01210001400043c06107003608998058416140f286035550300e60030301e00c0c0ca442e81d0702c030410b680c081c080c0f0340001d400482e80c04013421716515042c00620303c2400308550180305034070191195061100400c8032100c079204032015914080b04540290ba1a418501e90318031441e48010f003190301e09000041888502c2000c1c0c03000c0e4604184191040c0707190801c02d992210600c0e2032140e01550031074100601d1030040014410284181400c51802e0303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 249360575 1250 249359325 249359333
    0x210705030601120501060207170708121209151501140f0406170705091c020d0803040303050f0c180f03100213090b310c02010e0c0103090b061c0501020f190309050c061303 75
    0x19133221070442d080c030012940218185091040c564001c1502c17000741001080d4201d1584050005400049a4040e20b0101c468a0344505201111810003c00e040c3e07942e80c0301800c020086c0d11a1060f600000c0f03040e941d0303146c240f5202051902428040e99003031704141c4d4038002c1052202c016540e25569041c3c04044070010723110751912040e564001c00312580c4030701d01400c000c6c4c280d0308010f060381c0c0f41459a0040009118038041521610381001c0415505051032a0101d0b030f48001034070f802c66240c07251060805820805d41c004281d84400d520f1511609941c422040081d2940904640d40c0800e070900c0c00e004000c08807200f0070317075030902101c282e0001904582e450704403110048840c0050351035940b4041220310400a500c84074800f0721f01080007120903214010342c1c44010345118400c01e4070066010380341000b0710340d283e090b5030800001c65650a08403440c0881c2d0f44505441c50300035610048194036640a4442c011072030782c010010b000c0c0625510100480340d4000c10161444550030040072000c6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 249361825 1250 249360575 249360583
    0x109022a010903122a02150f0403020114040b0a020d02040306020a08010801060f030f230f010c0f0306060519020f0a03030b0a0e0c0d02210705030601120501060207170708 75
    0x8200c000064804180d04000340a0322112004850050500c1c0e90350529043e203031008881d80c42041d160b070010f1095040101c2c10710020303c00c0c2c40d490000070020f00030105000e00000c0d000301d200c0e0f0003c0184460015119210841c111400750170450031100284410009400030103078040c0046c1c1c0149426102d54589049030801001c080c00680b8404c01400035200910400b800780003050310303030b08095103907a46289550f20130542c000c1100c0c0410004104052082035142074202a990907540210312081d9594000c1070008003010000354a800c03542d045034001e20a4005581c010f40c1d50302e01e0080140f80020444592071003c07411417140d015200c4205a0074040b02404512030741c3c01241030010315003040014049500b0550840c9640c03420301491f94825802c03030f40030b035015110258444c1a08140c0400100100c69441641c103003090030002000d600c54020351180e13400b41c035000c0704003126054840448500b4000c490245c0c1c8185014846000098140780c400a06035046502050326a48500e0070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 249363075 1250 249361825 249361897
    0x3011d01020c070503030306130b03150c0c24071d10030608010501090b010504180603230f01090c0b0d0e030a03050711060613050a18082203020603010902 68
    0x903960129080c801a101888641d0061800300e0080d41181070902c0092120b10f41f803030b0a4150745503100704a0b200c50710180304c180048444640c1030640740c03a041251503440d038452481805140079088400b401d0945981682d51071804950240c1722a03619500217503001040e8010100c0300c0814810b400c005d40d41e03038611440186102e81e40214026160602003800c1d180182c0250700407500b031500f030718840d0340c3c004291011200503203140c40030070042410020040405400142045012410210801441d260310a001034454003c03980a04c480c0003400d8200ca02c0c2e840020000c80182d50108000b0300c652024103555070740c9280000b12070000d180c6540c595889444c0742400729850750304000011380c109142d650000f880c00040c086078505500040c00c0c90444207160700d6565941e4022030303502c0025a0002200d620391200d0401c003e03640342021030041e04100043d00341d045404c1c03a20510b0281070000c2c0400c980e40581140c2c1036900305040200030350442010941004094012150200209110003003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 249364325 1250 249363075 249363131
    0xf0509010209182e0305070e070f0c05060a0203071101020d09020a05091501050d0b1002150610080402100c0b100f060e030c011805060d0e1501030f03030b0301 70
    0x6541d0b02d5007001d201c006441c2008a50f0203d10810411194902d030341d40707512100100b201d4007101c00e0105003114241d04440d4001030300b24800c1721000314000842d40c0c0214000c03078154031810132860030010101c45000017080b008045030048004509080140d07005990001680d08000c0521110310011600b2a040a0b420b102266224260301c2c040d8286181044042d01064980c0616840c0c0320a1070526031001b85017050402900007449200b01c5140d80c40003000c080000d101721004451031200035602c0c81410201d04610392068080f0300540703010450001441d0b442d80f144140c0707075601e4003040b1a07800c681c03103188240020411801c00050744000110300c00c104083c03009800c1c9041180341060414a900300c2024000e440c0c40401c002d681c0001c00c0030401c00e09103804107070034040b480c200403110003076807020b508101c2c00b060960001460390400b044000c00141124540030303503091540590f0308213104c042c260101c0d545498002c00d200307420192140d03001500200303500021200101d14082991031a40d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 249365575 1250 249364325 249364327
    0x21e031908070b010504180f0c1715070216060305040c0807081b0a230d061b020f19020111012702010210050402030c010c050c030706020c0a0614030a0c030f05090102 73
    0x40c0800443c50100c5001d82401e48003040007400540c40c0039072444510001038003d0100041305030400000d000860054003a0001c10301d451240e400303800d6a1000c9c1d01e2003e01d403280f2400000f5601510000d2103d00e05031001103600001032400c40c040d4000d22016100b50b8a510b141d80d004951359008100680042104800400042d680082071840998a510340a840350460500800140700c00f1000c0400b401e501d0182041108903103800110b43e4070f00c1170001020755040c000d054980d81c902010b10001000d0719000d0303c80d04000681c0598584c44c842040301909582d00c400c8a000d544991881364030b40d540707180002124916015070a10a60038664544094500c184415045590500200900315000082800a030034580c2c006070b00c0d0f0003c0d0a4190402040000c02402d1102c00c010000d50316801809403404140c48110080d15010503000e494003440311720b940000c02c0c5104841080d4919401c0060342e09640b02c4081d108040d18101042000f015240ca0041007588180d110b864003e408004c001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 249366825 1250 249365575 249365587
    0x30f0302340c0e0105130506030a0506040c060f050c030307030209030a2001110102160b07020102160b0f1f091a181f03030215100b030c07030813021e031908 69
    0x1c0b48090481d002040180030260040000da125018100051460303000d0101d5035076150790101e490100d001d01c0c080d10074801e80c0103001c144115114080182c92040e5960146400b00e20004c2c1c58034800c13409410403a80c030410000303907400e109a020b0100040028152040c514041c2c50721001200a20441d02c4428414901d410789980c01070b200b0155032904100a50a000c00d001c0014a04d803203224015180b002c6120000701c41e24801c1d8100c405805042845104900241c201020b410b40110b8501408200a0b00403481d0f40c0740545113040e0f01402c800c0041801801c2000d044e000d403144548000c9825280c6038100800c0c1d9441308109049041806081228600070b03103803c0710b8051006007100519000c3c1d07400c0c4082640443da025102e02d80741c4460041380c9031199000c00700c27511580304194a90011042c40440303080a0001c10140d030003a03460b8000398603221103c400c4907d0f680340c000d6120013071221030154000410b50070043d20400a059451a040e101c034480c07140f90a516040341c18110004031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 249368075 1250 249366825 249366833
    0xc0609071511060f0a06260607081b070c09021b07050123031302040207030206040c06020c010e040f0e0105130203010f06050105072d121b030f030234 66
    0x3204507070401c5480c241180741c50b400007058446001400402501e4010000600d40e58425005080100400700c03505141881401e2983c1c1c0942c128800607004e40a80030101d813a180c0304c0d401036805a845407015140a14040318007800a0f07100c001c0490b990510840005000745861010b0716101d003080d5041440e003400b4400c103a0034038070950001814030060742c00500c141b0400c0c10760060510f1b0107c2a5641c0d0f0344411001c9018030b15142c0000794070a00015840c8205a408114980201d1280782004807140c1c64020581c3c503252440760280c0002c1d802d10500317107245047d820680321a0140c400004280b200440e441e400c3d1350080f16414201d4580b255410304505003441412040b2a840004000080c10540000c1c014810790700b0107055001e559a510324081081c0004454100c828001c0800283c982e24002042c1c2070900818000700b042026080703280d011811804002c0d0341c0c10340e112041c80343c40003015030003500444080030f5200301e40c860050802e03502403018010f82030354540e80f15081c1e6861030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 249369325 1250 249368075 249368099
    0x1306120f02040e010302030f0d0905130213080102090109080c06030604050402120a12020d02011103040f1406070e0906061804022a010f0605060c0714040f05160f0f0c02040e030c060907 81
    0x1234800700d40d0740102c24001081d5405582c0d0815141c0884880c440c00c092065144041d008072808004047c4104200042d00700055005100d080130a8980900550352411502d45846030b803200306410080807c00945249001d6105503401352004100400c142060450384d868200303502c41c02c5880b244c59644401e105034042221a103121940e1009101050790200700e02c58078000540000c0a140412250008000380e03600004084020b8800312410344c94001c90003000c100e0460207841c0550520b101040c03007410107030200c500a8108014120440160340d00784402980503040c1c590070349029291880d264011882c08088401e0302c00000304141d0329281280d400c48402c0c0c0d00242c800e58081140c001c2c1c050303003c0341c804125042d55540254520462000c1800b400d011041500c07850b14000402c403050b00728880b86991041c3c155100380c007000070514280d4006180d00c8500f000308000d4410f601c01898903400915484107031005490601400320b0405207803c4003a60781c0d1300660410075040c031010010341 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 249370575 1250 249369325 249369343
    0x71104050c090d0f0501020c030a1e030605011d030708101b0e031903170c0a0e010302091c0503040308191d0627130603020103060b1306120f02040e01030203 69
    0x75040e031401c01414000b4120180c000700091014001a001000b0311000f036044d58031840b1140c0503666100141200100380e1010306011018008508604001d458400d118203429500103854114008181c02c500380a00b41c8000a100d500d0b20581c40042010344081c0309003000902d8001c004100645c4100514140c445841800c0c01040058400200307940d03400072700e8a080300c2c205031132424070b0241c50078115070307004043c83c1c480300c05040c038001c0c0180c0d80c0c0031303100521416450341e079814070be46003143c011020381c400d03c4801580182580f01907000d44107598000c01090340700d2800c40386880e580350b442003465042416040c1c0484400c0c50004241c6400c060001100030044407800c44c540291b10000c2c9884c05042144032025071500080300c40c0140346100401154002841410f1f0b8825841c000740243c81c03940000c90000b030074040300143d191100e1064600d100c17141d414660866080080c00c5a501c0f88079445003001507182c1d110a0402e40c480c0c8002c0024040750390642c0700e50341c111b006040c6091900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 249371825 1250 249370575 249370591
    0x603030801120b130822080105071e05090f150306100302160308070e030609061b03100504051f09020304031b0b2404060b030601090f0b0306090403030e0307110405 72
    0x203142400010305480a0b144e000d0742c1400040c22085543c00d0208071801120840540603110345d10000384119021040300450f18a80020f001c0c2d640c41031403c460a400c59032125070056401c804090045000c1e00107030141c040060608680861000009504816540400004408000b050000c0f5041075140c0031580c600340c0c141585411101440368904003554100901000b2090001c1005903105403c0b150030b0110080450784681040000c0d103489401c01c4d10100101c42840303529060705038403181500c0c40780b0601003110307000c0f503d00000d22003c1c00c0d00810714003100421620b221007600d8007003140409040c00b5000141c03a840c02c0d00c2c0140c40103460204007029040540300da07400050001810b1075004400d41c00304104802c544122800100004040561081c2408000b20390040c00700082d510403007090340c2d1891115900c1d40c0540c0610707054018a08070340c40803c00140541070110b1150742003440381c41c000a81a500d00440c508542001c1030482c5d0704080d10004000c14035041c01925000180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 249373075 1250 249371825 249371849
    0x2010c0903080d090804090518070602070e0402060c12030a060519182d09020405070503040f111f02060402040f0b03030915070f030f090603090c06032408010603030801 74
    0x541e00e0b90341650050050146034140c40300c180500308002d80c0203032401850090414800da0400c070709480d440250701c0c22407003903a100e070800c0043c51500c00580002115094010f090b0356417515001e01001d82c4c000400601c0a108500364290481c0102c401144100130705a000600c2c03a0a000c100b01c4501485a44070070142d1800740140a6801c0d541c1101040c1840d040c0f000448002c100d2840321485010000c84500c6400c1d03085075402200d89401200c1190300c225000c004599442200340d0b640d000944000d0030280c0140220000a41c01540e07601c002207000341908020709100c2c031444900003105403000010380002c010300c400c40c24540200d60940103010418400d41030810080f980d03900500710790602c0341020352803001102035040c00f01ca0565402102122900207a810094802290310f601e1a000680c01d800018009202e0b200311044143d000d8000008a458031303800f10b000c0c10303858041c00c001c48608170444801c40d40041e03126006005d55400031454502e1410060b10720032059202c40c540c146 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 249374325 1250 249373075 249373079
    0x4030b011d16050d0b010e04110d0605030105011511010905070603091a0603031603120e01020403020111010209030304060f02150702010605010e120a032601030506061e0102060f06180a090302010c09 87
    0x14100c0f00f03640c540007403154000303221039115004803038240845041c40d81041c0340401310703107849210600034100740030300c000d0030b00401c0c0c3c0c0e8109042c201c0744240b08041c10b5415030840c121040c0d2240004920a203844070002c20f0203200354544506182e81c940c8168003090350b62401d4001c102c0c0300b18025900c1c154040001c1120324200f4007103a01d034480e031182c03450b5120214111204160059503030700040d004543c0d00308996140c1451a030300039071281c0000c2e80400e02b400b42510b40d400e814021070341d16031400380c099030415280c08000c1c1c0e0030404d6075001001b98080c45d0100100395002e000607034810246079001144881c94180090310b04401c598081d03000f011519441840441d00044100c442681842d040f91001162041c081c049072a11084039017405c407040c000014480e00082c5640a08e60031259031040c0349800c90b0f43c1c52090012000d1a025030406070005e2804258558103661100c000307840c1448029001c0801500f074401100c00c00c440c1a500d070010410f050b82482041c00481107802c2c044000741c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 249375575 1250 249374325 249374327
    0x80313080a111005122d0112020603070905031911010c02060f030604020c0a030207150503040506070e011206030308090d050c07090902011403070807030b06040f170304030b011d16 79
    0x64000a409406070054071140c43d0054490012144079034079001024a03030f8184140541140701005600003004240b901c551801c0c804a403840314100e403a2070325000c0b40e54400e0741c240811b0760001030214080c88a100c0002039191014000c100080b1107401200b82c0024041c0f400c1c1c00c07001d06204041d81004601710280006031100421070307402c1112800260384a690304000a8042d10401c0e6007060b1500030307480312804140d00040d684040d0741116180110085090030100d4141c04111b0b000b8081e640140040760940c0d001c0c1041540340c2c2818942016110b0003200c074202658415841200020114420040000010b0113a00e00200c00d92418071318262140005590343c15003409154000742d40d50b0020710846e8000c0040b040030390801c1c50388130303100e2415940c0900244c0080790010042420207201d043c0d585000002c403015200441100e203415801d10116003400319038441161050300c0100008804504000103050082c808070b10900c54001c444801d590000d0409000d0302e50090240e44004542c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 249376825 1250 249375575 249375593
    0x60f0608060714090a030c030803070e0d0816050c0603010b091206040210110f10050a0e01090b130606080f03041505163002010509012d050402130204080313080a 71
    0xc1643c006500d42c44290220000b40c0000701540028a1000301800000400480d04003452060801d6200c0c5900d01404409100c181d00814a009104502c01c100b04050810a04125107440d80079004551310002c1075404928254002e801c1040188000700b0300d0105071600a120090802d90304000e00080d0409501040071440c14042c1042441428030070b50504c0b240c100302c007074910030083c021038190112411000c0000d24040d01c0407000d20b41003e41c000380f503c0e03050080c40c1c900d0398800c1c6070343c00c130f80d03100a1145812010762908070340058032000b00046130a030070030040910500b1000916911803920070140300701c003103440e42002404014424507a000001c03404140c10b07550030420034142410301101650741c02c50400e03d40e4110b0340c0001c0c6904456941580b007288692100002005a00d8042d4450403d2650745550f03124140c450701d888500907903e03a006503820510141c00d5880d1214040300400907a0080d8200c003216520110707400c1e070750011484030030b40104013001c05041104095290b422107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 249378075 1250 249376825 249376847
    0xf0705130320030c0f04020f0d0c080612031215060d02040e010603200901030207030509062d27040204030f030e0405010902070213090c05030a0516061701060e01020102090a03060f06080607 83
    0x118a901145c1904c800300d07001c0132503008102000041052103a050b4010344a498250b881c2400f9074405070307c28371084c000000312401004246100840340c0d603100405000c0a402118264102c0010311424202071035030300103800a48004105811a0341c10020f00a0460b11840b0700c0310703201b0003a0700c0205e50554440e8200d40b01403c0070310300980c0c0e40b142410243c40c5440740d20101d03a0030040000701c1c98820020700c0d00c030b140a0441d640a000190003001004151401107032052414416495035101107512400c10304603900e100980090305080d580c1d02e60720b141203e41517040d400700b050745902120760724062140501405142504508244444d000b250009400c443c1d400c1020f80e941019400384900d10300c1603402094028102c50b00d440c4136103016501c07248034800e0000b0044441102068071030240d05040d00e200c1103400254460f0f840c00f2022158103600014403810765600f013100700195181c1e1400030020390f00411011072681c0e4102640000c5440607480880ea03500510f0500caa480e43c48210185 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 249379325 1250 249378075 249378079
    0xb0c0a120b030106050a15030e01020c07290406080106020d14030c030a060e0106210b090f0703060b0a0302041d040309050d061803020a03170402010203030f0705130320030c0f 77
    0x400c0c21070640843e0050126400c195406120713403100040000d00703040c02c4001180d03250350038130404084d907203000c1c01c0c0d0080120122941d0801d56043c07100540e040d040c0300286100f04141890740d10f0360800100140e005400c58000a016040148030b040d4041002601c0c0d2031007840c000100c1c14182d0b54481a03804050511003007945e0000115035061003540081014210404440205580d00d000c05405100400c0b80c030456215422040c0e200c0c1415441040084003001d05141d1030ba55654101c035140c90070041064081c0b65a0b2600480d031100c1500180c01c0b140300d251030050f034a50600292007025840e2002c840849109070303042000081d8450501300072a04140d4408000c540e5600c4c0c9500a403510200710410b03012110042410305500142001d54640241c5a00d51000b8140703586c04155a0216170182c090703841000070940c84410026400d9001d030442c0f0f4483c1c2000c8034081c4c1c10000f241b490740b09a0303030415958500c165000481c000341e01c0710700b421401444030303285600c04605051047c10f1001c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 249380575 1250 249379325 249379331
    0x609060c0d0b0f10090f0603050f0708040201020f10060323070509070203041d0103020405090a0b0c030402010e1008072a02042013030b06040e03070f031b0506040b0c0a12 75
    0x411940343d001c0010710850008080180b400000070300140031076007912a4185450aa64001070a203000340300d400d0290440c5820380311aa41ca5020590f081c600203070080341140b04a0380040d51f103d40501c06115480e031001004140700d03286007010b040c080442c040740d503054294062882c00305580001d19004662064441307174806d0340c804e41c0c182e055000750b9200c42000101030808841003000d0102940c140c0b842154200802d480d903d051070756801581c04010301e08980038011410008519010f9544944145401810741c020305000c206030101d18a20503000c91082c009000103503400030800d200c55040b400407660400c0b940701c512034000d051f100020340110341da041074400d09546d1070481d000240d4040301641d90b9802d040d0103103524650b40c0c0300030350390300b0001400f08006150501901c0401d00810004509040594440802e41500d40608034140b0038240c50030740801e14803000d181c00443c007880151102c1d24182c00c004100c00001050419511001c102d6131302c40710b4000b1005103810351b03104400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 249381825 1250 249380575 249380591
    0x9050c16020a0503030703030213080a0b0106050d2d0c0201020c150a020d020c0303420301090c08030705011a031f02041a09030d09030803060d0f230609060c0d 70
    0x45a010b24041e00019014040090180c0a158054009000e100104440840041e45d80d004050b1a000c005a00034100c80ea094010003a03070f8070410151100600850300020030719031100c0001343e00209030032000642009542000301c8111030b8492816020480e000030342c6420b19005c071650b140d18552070902c140384008000b2030300402040d4151150320391243d00455070f4200e140c0c003040d035a0b00100e8270158511442d0305280c00d01400502d00d0b084043c0400b680032314030810001c2c504e83c011054250150190340c1e406154000c5103449143c8801000d034107001d5541c84000e030800c0350035108a07c110016100d907036040c0e840e050f10002020494105401c40c1c2030242c2c06542c1c010350282c8603680c0145801a00d542c00c4500b810f259000415080c0800c4085940c80e01ca42c00c4159a540c2d211b101c00b07420b00c41c0c1400000d42d20f007004d44012084501c83c8041820100320340ea62075110000042c0344601c800e0a08001c150f0070042040082c0d001250b04001307003054504810400600d01c164142980300b01c0d01d410f10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 249383075 1250 249381825 249381829
    0x5100f060f0530090307050c0d0614190e160510020f1623090604110d020f070203070f12020409110607150c11070b03060118090f0609050c1602 63
    0x192480e100360040d002c0d0901a014400026042a21920f40c01412035100400c50200000045444291740000a0b044101c1070030200000c10460304410b80c2c6964035811050106110190111b1241c800000510010540c109031401243d0381ca460302186948104014900301184204c010101d41c02241c003d2b068025080089041c4010b480240c207136403151819a02d071134400806510240d6881e103c11060350076050200880d01c0130004181c5400070076040118000d41061340140484914003400c0c1490050031040c05004ca911080300440010700c0481c42104624003809030b44002e14607202c02c11180380c10800050b556008140d07000b807040b41c0c1d80c2000c03010403501500c0a005450f0040429864261078182807051410f41c6030220f084500d0901120151802403076003580404d0308000130300303e4909181c07010400354409010f050501481d1103107540d054101b044d2800207440039620100f03441001c0c00015083e11590f810880005050030100403800f8003400c2a500e80c08100720701d6104180d61800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 249384325 1250 249383075 249383077
    0x121a070c0c0305070501120506010f140c030406080114061207030506030a1709040c030c0c060f140106050703090807031110171e010f060519120603060f05100f060f05 73
    0x260007081d00080c20000002d00002055000c1104c20a8980010766072100013804202c4104480032400310300d2850059154070300c9682c0802c180540f03000954507100c40080e00e2803954101c2e510120016600314014840c1c09000404035503c4070065801a0030301c404103101446002c80102140201690707540001c032566030410107103040b030350882906448021140050586a80100086070141d420312901445851080c803d0000e401c51550700c00704094019503541c00540a049240c007030342625440f1144020800200c0c0e24001d080704e03212203503102c45d9850041d00507103442d4084e02554008a0b03080010a03048150101150801c45002d2440000e0b004199050000001d6404c002203d03c0c0800c030541003102c10811032650022020140340e80d0310425940501c449006110006030140308030040e00d0031046900090790307a01d080c441449000b100c2e40500300c6030568415500c25440c0c0c4030214a8807100d100d07c90b0400ba0703803040444140e007048115000c01e2400d204540c10040c1d10000541141c3c4124 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 249385575 1250 249384325 249384347
    0xd18090501030308060108060f0f0d0606080708070303091d01150c1b090e0f120c0a050609010f060509100303110a0b010801090b07020a0309061407020405091006121a07 74
    0x45020405075860742001440c1d0f0000329005808141d0700720200d40685481c0804d4a01504002c01103c49280000c09119001e18242001c540c1d0343d0b210580031802c50300600050003e000c80c00010030080745141001000e184d800c0e400b11090901d502c18803218641d5184006054482001d450140301c03220f464116044040554003600340c0784819007851100c3d040015110032514441018820040c440b00080e4031003483c041038050a52100d0820b0600481c2400078003448002030050f03440c014500c0c1c4403a401d1038011118064165511000d8010000040c0701e948040c05094038221814900010510102515804040e042c0080c0b80391801491008101c200e0300a54880100d0016585d201c103c1806460601c40856641c000c07840003c891900c002441030640c1d4150780c0b5107002500c0c20209540307414a20404100d0b000c403c1000c100903881e28003030240125140710040003040d502403078100856441e604608501c023030b110103800100d401c00d000318503d503800301c001c82c4141d2107266042d2040300b0700c8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 249386825 1250 249385575 249385589
    0x60f150c06010501020c27150d06140f06090f04150c050c07050609010503011707032901150f051c090b011401051c0207030e04050126030406020d18 65
    0xe52450120300426128100c0301c080c2c0886106460800070000404001c42c007031100180c141c00d8640841d1014000590007944000d07030700b4860641500130440e010880a015070350340c0d4807805c1c01410100445803a40e480344442c112180c10b07051040001d400c404018200000c004d02101c0464217108940c00d018a44000d100001c1003842e40c041d60103032064100fa40362034214000e40c400041e26007001d100300c80505605a403851b00d0340e8240420281040605c587d1400703148140304010001070300c400c009445001c03c00c80440f0800d0b1410301005040354051b007160303488102510758200b269400000070b00c40c14005041c019110211045880014804882944141401c09450501f0700108103007a906a90720100c402c030040c0b561b600192100e2040340d00527500302d040342c0c413000520582175025040c40e5200c0c0c039001c1c0000300e140b400101641d00a800001c018007014030398100e640d0105882c002411040c03c007443c101031400e4806034448000227401400d01c1a1043c4516040d416000c0390790241247e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 249388075 1250 249386825 249386827
    0xf18040606230103060f0f12050c130f0507090803250813030c0b070314070516300c0e090f0d0207090b031605012609011a0612060f15 59
    0x2080354016441000d404a40d40440d00d050f5001c501030102c1d031030440584444503134116287c1c1c9002c0c0c0e2180389100c980b0054450340a5151508101d81d10740c514403030559242e050101d1002250004c610032901c0181001050044801e001c002c0c46e100801514100a07060044d01101343c3e4501205468201285e40206890070014420078a1401d40104006803402040b0b0525200d8a4882c1d4003a18030880300064007040440c1034120700031301c03110002c00d0050721603801d031125040307020740c3c084a040e0907070085002003a81d2003d141405411004e00900e603060f25685141c110695140c520340e2058074020001d100451345d00040c0c10510030000072800c40640c0007160280022100025110041402100002801d00d00c0b06100341c5800212041c14006111001c24000d00d054019262100c88120100d40529000c1e118030070080e0301400c04d1b1089a480e000807480b0021502d2206644140d82400c0e4443d030300c18004451800c0030001103940c042415200c01c060040d581001500c10410f008000d107400320 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 249389325 1250 249388075 249388109
    0x60606160215030f07020601081c03060503030c0d020f0d17070c0506040303090203010c0504050112050a060f030b0910060b1804020d02030a091203060b09130f020a0c110f18040606 79
    0xb120a0055104070301400c5032141030f48920804a071620750a114940159002584102c8940300340382901c0c5110f211801c002501d960358002007411030f008142500b92903040b01e11000445070b0188201c441c40c0c559138015006048810304041c140b40e10388a807481d090480040043d0500340541c2d409c01ca45134004080740c041e460a0303d0002d0151140c0d9034101d01031750801f1854146c3d01c0c02502a5025994142c45500384400b00d07210171002400d0003048400c84988407039001030801d50030304044000c0c6005203034031051850403d0282d8580071462043d403400340c1c60224108403031000c0c401545d1501050004811380640160002000ba0140c4001d114142e480041404089600c40c0c0c80401c00501c600c00101c16494210f8007a4111006071041d0102c1c410108130300c49092605418510b40210002800111800c0182400d03003241c101511400103c0c1c41182003400340039842d842c4035103800c0120307070781c1d02800e183c1c1000c030710000c0d04100003031042c94240303020500300030b1180c0001010b0f0450700c1601c034041c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 249390575 1250 249389325 249389359
    0xb0d0f02070f060f09020f010f03200d0e0a03050702120a06110a08070c030206130c0e0720010b1318060e030405010e0901030b060f0a080d05130e0601020606061602 72
    0x100c2e40000c44600707250110101d01c2003858081d9454142c0c00615910300c400b04503005403086c1403403000010415680781c00d40406400c0d04c242d018118400c0c20b60042d01c4490300c3c0a2142200d403a840643ca181c0c1c0081c10040c00030340d01c4011599103980c15036540c00d607000c240000902c1d1001491703005100c0e0741002001c60040120601600e0030100507900c4500c15102c5020590740740c1d00e4441c1c0500141c000b0000208a020328007081c2c01081d10aa80000e45103a4681e0b0030b9a0190381034500c2000540110501150654907070022082026850000c000c0010400005000e440404c4440da00c0162281c405404124269035041402500200103210101c140c4030318540340c0d401070059602094200340e100c1c5250600c07150701d80c10707240d004110950702d403550b01c10000180125901f20303600132200c00700842e20640c1404406c02c41c0085440e100c1d1606c02d40080c80003c11404d8100562900044040080581e40024620f0300100300340e400d10340d5400110f0500600740c402650107174120381c2e10b0841103655 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 249391825 1250 249390575 249390593
    0xf1a0d03140409020a03060504140a0b01020705060c0f070b2106060403050f100f06080318060c0a0f2108130303020f120a0608070b1819060507050d020c0a0b0d0f0207 73
    0x121011b40d404111041d2501c082000310791052007641110706c0a580051a0034046501c418034404050044594503662140003600c00d602100000c103154000e2880805810003c00120001d040143c01c0541050b00c0b5000c00180c02c0c522121411510782c4e480f02080c201d482c0d04040740d02554120065403403042080c08803542d40c1100c1d0041e2441186009030441801c4040d100b00c0043d45c2d518805580b4066a100084511030101c00745680e00540070003c0001210040140ea400148606c0d0304108400300ca06005900f4401c01070385010f11002c44440c20101c0e64407903c0513078000c14501307841d19081010f003812002401290400082e4240001e240c3c90741340c0159601d07502c0b0f43c582d00d40901c042c42d1680310941d2142594413415149143c14030540840d140790b0100d519003101c000d026400300e10302c4003070039aa4840b4580d0207080460f2b00083e80c102030140511a15804001e94002444403074443c80c04560103510611805041c8200851024547d2900f0b0300102603012140e43d055440f0000b40c203001d200 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 249393075 1250 249391825 249391837
    0xa0906180b1510020c0603040804050a030b181204060804051c0302090306011d0613020705120901020c010201090507050d05031306020c01090e040b04080705031608030a0f1a0d0314040902 82
    0xd442d0054001c14200e1400c00706881d40c82100d940500401200c41c000d02100da000500100c4400d0018000491244c40714134640700210300a010302e0600b418649054090b0700c140d0b001580190300705074115501e00c6040011101210303140e1400300d0a9586504225050881949020158285107101030764000e5043d00984807000c012401c0d0f84103643da0300c0101c0d030380c1c80d04075000020703900c03d503070010740185040300e030a51090442c00d0015180c10026580c6906261030304c0c0c038010002e000030806d802a546d0403c030300d020081c0c01f030000300f01024140d02e4180d510704051280922451a090800342003010501c151a10b0a1182800040441e00e030600691691400300089001075290400041c0c80300c081044680540d8114107a40c8058540341c0361070045610912054845101c20800241120009840428690700544076142c490502e51110401d80d28074180050a0b00c3c100078007000b03503000944080700b015104985c101c0c401300c0f1a103420384a00b0505e035840710304038501080002e0a0700d04d907001081 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 249394325 1250 249393075 249393091
    0x21b0c010f020c0306010902091201020a02010c27030602090f0301090c05010e03030f0409050c12040302010b04051f1e0e010b030901060b0f1801030e1615090602060a0906180b 77
    0x449903200c40000c80e5a40040c01e0084e9040c5c0c4428010003d501c81540107090744140501010780c20380103018100d007a070348039079400c00050713546004152480d5400640e0445c12810300522200d200c00840354411031000c41c1c00060126940090300c04501d544080000c508648054024403941c3c071181000c6207107000b28890240032506000e2042154940881140c983e5151038440b0f030304007800c144a070001008018950704041104200b0801c6601c0c00e4410b0a2107103200340e0000c01c014040710248000e40d038000d41000b61401050414422812070481e032001070f220241c910701c01140c4046502d101400b650742c000c82034904040001b0135080f0104005500c1075800a0003400081c0d902c0000e2001445904000309600300b050015411081a042000c0d41300641450701045013047c40b0007460800c501c60b2400200c40090a404001d00c09070590455850030850914031412880c240000c0c1d100c0b940281170700e840b65681c1c940c0d0750810423030340d0200360301419840c0c2c12074200c591440c14020720402030303d0801c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 249395575 1250 249394325 249394337
    0x5120604150203040f0f0203030702060327030406020307031206090914010c0503060906060a180b180307050307171533010e01030e0718060e070e0d0206030703021b0c01 74
    0x4510030424003c0343e001d142e0010498404101940351017102d10b10810089905000402241002d070b0744100207036001d0341700070340d00d44030700e50340341307034246052034045420039516001400b08111064000c8160740c0c0003070b05400c04a621403a8500e44400900c0d00f0307000882e00614004c0c101062003495600d00664103002c80003046008018082650300d0f0008403000ca0340081d54030000f80c920300780344000c5c090304200390405000c0705011403440b0582410603003100658520219840c20700745000b440340b091450041d4003034040c0303c2c00c10740840d0325641c19001d10356030b5000ca081b41409540040001400382d001c040d644501e0350404140003280e500d0030600c0141841d40582c008011160000c0c807100780d481050b102c0d00c03a91021030b001500901888050300c0218040c1c1e12000851108040007004150300c6550002041410045500c40522016000e141004610b0540b41e1458448404843d0b04940403144c25480b0394510b0003c4010388035140d00500e01c08000e01d84840740c10340003c0c036180c0b0040262919 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 249396825 1250 249395575 249395603
    0x110306090703090215071401050708060a1a0a050702120a03020d120e0a0308060d20040c08071b0c0305100605040c02010e12070c08150901050708070c0b06030705120604 74
    0xb101540d20080001c0e6001500c42d1a56103082625801041c42c14030400096104410420b2003e08482c0c0448884001c5400b2408100745840c2012024018101e1210194000c052007141c0c1c0b02c5600940b1215024000001029810340d030324051401104001d0800b200d143e10700300d02d8000d488090507401840440c03040c102c1e40d0640941c60003481c03602c0340c0d140300908980155880441c3d5040c40940016008070400100d9004589002205082c90418011340d803140089201880111001c042d50311007080b101d0002c0c0641541c0c8084911500790741048019203080090600011b06502c03030b80014190b114540c4d0880641301941c0140d002c841c0c08450420503400300030350580c2a02d0302424003200b29008001c0d076900b0b1040322000f078841640110315140b19542c07a00c0c1c0d006c0c0f404941c03803e03070380d5003081c208104540001b003406070a1b80f0020768600710142f4101804003074004451800c000f894a0b1803840011644e40b0704000000007464000c1600841000443ca520f4440342c0030381d0141c400c10f10741408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 249398075 1250 249396825 249396827
    0x608011211041a150315030703021008070215011806080c01050a03111b0a060b0103092f041509050c03040804170a080304060605030610062a061103060907 68
    0xc00004280c00440700240c004000040000600351101000c040209540320b14083e40c58075404c22016030014000750f607503400c1c5207988611524111030194400d50241c807003400142c884030600341140da200d040000a039180c40e2000d07410503080f0032100c1102501c0000000720004178035496950034046000420240d40c580200720b40f0381c807104c024140842d200300044000c1c503200e036015000518481018604290101521200c2a030b8103080210490707001000340418041181310f04a02c0d84002d003010003145074581c2e02d04100e440c3d030106092511010070600010241150b0f03a26800c21b9000b0020421400004400780b001304a83c011111890318150006a241e480030048a004540081c00c039030401d0700c0e002940b1100480ca4460780400e0040440450000c0d00d104003942c02244104000300700b80c0c0c2403030140351802200400c0780840b403070802d0f0204240d41e00030f4403121690107005d00c1e003a440b0a41c403845141c032005001008280e2850003541400b0031f41108065030048004540b10740a540740c004d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 249399325 1250 249398075 249398099
    0x12031b030915031a130e06090106030218010302032d06090d02011406030613080408060c090f06120601080a0b210d080702031602010c0b160e04020c071401180f060801 73
    0x2c034007110781244c400000d8518207110400c5032603000c00404509070321302680140c140042a10034420b40d0b91039031400d104518082d240880503486400303151481d036241d50006a5243d88020f84000c05d11108a540b0200340b007985460180c10316404125000b608264044540c2c40301c2d99148000194a000c1c051a107041b9040551402100b0043c001e0100345c82c2c3d44440301406149607000c80e05502e04100008200806021562240001d5900251900400c03024002800e4401292134070685040121400c00e154840b44650402e10038605580141d58011100f401880144030072a40000208503440c2c603c084050f107620b24804032002d4907130308212640e056901100c29500c1c10050b8100303208903000c280e10b807030081d100a070052414050b00728030f036143d595060000707455002001c482d140b9801c0b02c8a801130300c44222180203550031854240c1c1d8804080d21007240d0b005125600190024449003a0701c04c5114200b80f44d03a040d40403038440d56035604041c00c400140b01d440003081051000081c480d201003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 249400575 1250 249399325 249399341
    0x50f0304061d0622150806060703080c0903030c010203060a09060e0705030405070b030117070e130f021503090a05010605091e0a090c0f050a0905040c12031b03091503 73
    0x42c030380c03202c1c0d1085040c2c002042c1c00626140758005000340200c410507001c02444140040340e94068a40180c01d0210781c07840e48a04d90125000d006841e4140841030320b074a811103013065014507140405880d600c009a010344101124603606200100d2002490302042d4015030203042c0c100e511500450313550700401c0075500c0754404c0304000c00484000890681c015002154010b210f0010380d0744443d2100840241608282c0095000307070a0381c1000301c0014810894030024190013095042d040c50008041c85500103241d0000b000e584000218604544440100a00303550000c0e00c000d4582c81c0c0307c244250383e180c640c10269810360030540001140d0818118090191a0091520642210060000b1088440541000c2c6d12030390303a801c048003141c25001c60707601406c40401c240361050b10303000c20400302440369041015050314160601000440d00361207401114400c2c440c1c049107040d00d003000c4d00c0a01d0741151400400040100480815a11200700b030f047e036040301c003019041c81c480c0d40c0072000c8840a03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 249401825 1250 249400575 249400577
    0xa030c0e030d091a0903060c0903210f0a02010b040212090d1b03050306011b03050406020f03030c09221113080a150b0303073c030801030b130b0f04050f030406 70
    0x80d80c113110340480b482c10500701d0016401114a0718124002191070b006045840101c80500440c440e6924942400303110300517080245107001309030030720380f5050079841b600c91503e16681b0002040b8103814000c0d000104e8180e0010710841d11501070340301d800c181c000c0899010156015480c0081201030041b6040d00300505000282040d080013503900382c5069101030150740c1400301880c0c0c4030b0414034420500d0489144240d95180d112850100c3c040d140c84001038807442260418410410080ca2a20540c0c296000c200c500169103543e070101402c000079000b211110040c24030480f12045003000700142911442c54648052650340d6021035070722000010001400c0c100d80660400d0400390303a07000018a104018140d038545021643c0b0050710000340d114802032011f06829459a10480001c3c02000090010a403044145c1a6500030104001404010702c5109180d01040c1205496000e400606a1109074034176a42844180b11942500455080720903100380280038858400200c1920212005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 249403075 1250 249401825 249401837
    0xb09010605090d06060803032502210304080c03070804060f080105010509040e0c030f1518030a0810120b060a06180b160f21032018060a030c0e030d 65
    0x141d04100050510382c180d040c2d13082c54845802003009030701800154000c480c81c41c903c15481c0800300c0e081001c1905500c04c00259000070441c40d41540c41c5103c4058034401d02078403240d036990f40d0700c0c181096001301036081e256031102040301d404003d1040000c0050354020f03120018001e80b040700480f140d6100740502d40c005042844110740d54123041c2c001c203001d44d145c1002d0f0784501c2040c10220340f1f42011040c0c9801d940d4080340e071101c40c6496800f41c1d0354004c0f189030001061000c0101d0f0301c42c0e0b00c0c07280c4180c0d03204010403500060003100da20034000f405804040320001d808a2241000031202105070f40b2036210b404a488005000741c050044032400200340030b0707559515071904907143d5050300f12608060300c42050324001030006842c0710310680f80301d104002d074501040075499014100b4800341445014186041c3c01004c42983c4402100b114000010301140e40e8159510403514120505c1955508840080303a070300c91558168100c2102c460b440e80d2802c42041254042660b00c2080c1c4241c0404281 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 249404325 1250 249403075 249403087
    0x2040f03020f040f18021903121223010e0708160e01020a08040806040506070309112b0308010501030f02070c06080601090b040b0d0f090203070b0306010903140705040b09010605 78
    0x1000c0d042e800207007600410000350f4010144040058a41e8a918000c14501e400d610608601e007105203400c0700e00d40b4501406c902e030708568503c1d5080b07204001c1d00040c000620300411188000e0b400400220100400100c1c0d429880040200d0070b00d82030052003245014400090083d500c10310740e081c400c607194142000304040c1240c0076038020031143d4400b811801200d4036040403c06102c0284000c04941c0700901407031a003410030303d0410101400392803c16003400164800700e1000e500100800300120345850b8520000e034050a04e0b8011080d4407002c2e8001050b110382410b03041f450484c101e0b00c0c00e803000c1c0b0a143c60048120100c0c810050010220311464100340812449400800d030312030410704190160b9a151400c0070001e81241e4014280074400041812181015024072a8514000c0e0000c0c003000c2c2180c1e000940300d80e940d0084507051071000c000101b042e0700c65041007000b9508212416100d081e4106e5203915110180106809142040303540040c60606143e4103048800995034181441 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 249405575 1250 249404325 249404329
    0x303140601020a231b011b0b0103020415050301050406060602070b0c030d0f110403050a06060f03021e061603080f0105060a1b0302013308061e0c040801092402040f0302 74
    0x81004d002d00c440d003c1c0b10305964101d95020410390400f8180c5440300303450003051130700041c00e0504028002c07050140344061480090f105201c03480c1035030390440c0c0110b441d80d00d2815640381d41e08a50b000690541c04c0030140000c3c8043c590007003058552031b6082d40e01d01da48030000d1501611644954203642e81c02082003407403040d03507075000740d03603410000f400450808585240080c46800c550030690fa250805009602000030610aa200400030502c030f1004c07003480d5400086240030704030b00b00c1c1d0485a050050015a0b6601c80c22102d101d90740b162030400256290800400c001c0e4211807880346091200004104c518121081c0c40c259123540e0345060000b06c040100c0031002044840490540d900c82113080502504501842c0400c0c500350341d0f00c1c42c1624690441e03003110111350b0001485401840034800d800041e0200038030030034281030b041141502c81065042c0248180c1c0d00070410f42d4a001e1102d01000600f49102410fa03481403030b148200c41c000644201240326602c0f0700c2070400000d0f6000c00c014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 249406825 1250 249405575 249405593
    0x8210708060f040510031407080114010b090103020d0f05161d06030403140f07150c03060803190c06021914120f0a020d0518100509030a0818030a0203070303140601020a 74
    0x1700014903100c1240d80ea41d500614001101c00394446422070300c2d00740f2400380e0901c503411706001c801008401c554509800d01915119040801b8100758000441148229031038205c0980c3d242007050400c610310f415a00303802c0207200c000440c0d00140c2c2004414402d54085255038400c0c00e0018040c602c1c548540d502a252005800da9042900c4018003041002c1d41d80f0344083c3c1507940c0141d544212031213844210604070b801c404c00000031700d490050140304c003400003c2600c55942c0d0300d443c4c40e060421500e505a03182a0000002840f80e400001c0310301540e81d850508400c0004241c46500e0072050b42460701c1c2081c0295034a11000c900b1038400070f1a60450703d00d000303030031084c586001032505044401020517240c0803074610241c2054060038815801040002c07103051521848200704074200340143c152a881000c140400b004151408035002d02e0003490b10624031101c1004482c1d84042c00c41d00079480b60099401036021034502004c9003129810040500d2244c0303016070240004110039510000c84d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 249408075 1250 249406825 249406831
    0xc0b0606161209090b01020303040b01030605130602130806060d0f02010e1c030305010807050a0f0512070803030a0b0405011208121f060215100608040f05010908210708060f0405 78
    0x5140020750300352000ca200e0451150280307501c0d50310480e8050800d1003400c181c442d11080d480c1158010010000460200307414541502d62202c004100c40d100d0074407541d40c05407903040c041c06291000801c042d0102d00e41c52030b44100c0c0c0204007a00c0541d5110400c00c0600d44081030040c0445c4420703204000190700c42c134400d500c3c40e540148004580351107141c136030b5103040c44680c00f200480d03a50341c01406000d008100310801040200c0321a49101d0405610306882e0880307100c0d0b980113000300450440002014415800a080744608a80c0c0b00d141c501201b5014041d1414050b015a00c0c102c0046222140a54110740440d045041e02e0701c0d00705d00f10301c01c90b40504000c00000f80410401a081d80f03500300108410f0003000c140d0300425000142e200c04842d1440c0280081012080c01c810070058590400d11560340150401c0e404403007000f0781d09109014007000c80d00240424000165480099150248030301a01400483e09419039280300f000da50351030040c1d0340070703a111005110021251030070b6080030354 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 249409325 1250 249408075 249408097
    0x20060c0f0913090609051c020d030908070503030f01090506010c020a1203090306060b18030120030702011509091a04110409080c1207051603030509040c0e030a060c030c0c0b0606 78
    0x102c80c640341c0508040303c421050441c3d5254a407500041881800c1000e00c21119050310644202442c0c80d80285d138030400c00414505041e126000d24040c0030009080d10105504901901d90b68074007101512001d480c00d000b42480070340750001184981d44030715511249582d02904140310716050042420030120314050440801081120100c0020081e0141e41c00400e24154081d803151206412940000580e1000314041d030b2400300c07080141e2807400e098240030b58011086554a44449104170f01600f0358088480c8031101c120400200a4800d9000510340d034051000c1001c0064018942c884400c1d0a89025060b0f01d41907a42c05890714203a441000000d1041c40b02518112022100b03509141405900c24000d0f0b10104620062184c1840740055076903000c108411400d0070760b0b40150290141d81c00c0240503599480b0034a11083c01000c00500032240242190728160700c603cbc081d4003070b208405229000030f09100b954150140a884200c4407250b00a10602c1d060392180103002040d045103150030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 249410575 1250 249409325 249409339
    0x120a09020315101d060904150903080601090806280e011407090b030103050a150b09130201140901080103060903051e070b010b0301030203030706090507080d20060c0f09 74
    0x1100603501084020b4400c0144800700c4028940300606154007090b0350301c4980f0700c2c400106000c148040c450459640040211065003194446080200c0c950b4405014124010b1420317589206050708610400d2181100b40c0c0d4041600740c9440c80070752202001c1e40c6903030607040e11000011151241102c80710060009a2001074040414102282901d00c004190245040070b6014005440d500c007000001909881d201c60380b030b651450703858039540c644401014141202108601d42e00f40002d402a2080110042032849c2d03901307000c1a03c00300c0030b04804089010802c80b1035051850001101038501c5100142c50f0b00419a18546522b400b82c03842c0c01c0c08908100041083c1a030110310080301040405110800c581c07036440b2803074900c21085068004180546082c80104010781d80003084964282d8049000b1505003203928110389401d910384c01c15031803406140210240d044c2c2c84a13041c46c8219007108184100301441e80780e1615040b0503642c40309004000c000341d0402c001203100804180b08058120 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 249411825 1250 249410575 249410591
    0x4050723013002040f1203082d01080c0442090e0303010828030302130305060117061317071a0403050d0b09101703160605010f0b0a05120a 61
    0x28510300c0000b540e060a070303507000c1000d000030701428500c42c1c00340070854414a41442d8945001c0d1001500a102c9011114a010030258a9060341c0c0c1100703600c1c8a00b981c4900700c2d40c40f0001141c0354014503610a0007546048165449030328204940c3c1c682c500c040c01d062521244203643c005200314004034510180d40d441c00c0c0060800124464441e40c140d10902031900d0707504090780c4d10305228008400604490101d4001c2c014051884c00e8120100c1d0305040c0160385519100381c00c240344081e6407001d4424003a203000003d0020400032800c40e12461002a41c44aa5616003440b6010701110300203800782c1e480c039040c0c05040c1d1140f40105442ca0151040d49000042030481c011000e104a80441c0003c0380410081044051801241a0f0900c00c40e000b030900d103490b01c4c2aa02420f03161041803112a5842c1c2d08042c480b4040c401c440300c01000404c24204171a0030305110004c1c15083c42008218150700400041a080784000d88000880981d651498038905440b40e103a00b42d000b030032034010a5650420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 249413075 1250 249411825 249411887
    0x6070e0616030e0303130f0807140108060117042301060e070c08040e04032303073002040b070506060102060c0702090403030b06030a05070f09240c0b0f0405072301 72
    0x40c00081b0045242d101e2100e0401c802c00000e180c607607000050b294013503041404400805484015003060078a0101125900d00004980e12070081340e07030b259042464000e2209110524030200b82170802c10362401e4004403000403030ba08036856481101038600040d8042003c3c0ca206801300c850007402051800d040645807211010440c00580e030403008924003030303141c0007002240102002c2d0b43c020944682e04520f0641070181c10003100c5034900e80e580f5203660381c14002c0364282007a107000d02c03584142191110748a509103030b5590f000b414140ea4034811600000c1142d031001440380e203c1c0040e41e060f00e08010407542401004900a030044051644441c51000c4a4035980c024500c5a52000c2002c5400c4c00d10000160042e08250b1352001040030b00c500034883c4424100703500c41d06c0000303000c0ca51403c0e44055400c4444e82d003140300090a107062041800b8940b5150303130385180600d0040c030650b0f04980e41c804201d451700e119a00e26129601c070742c0140310100d600404150240d0b50309040404034442c0c3d4484 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 249414325 1250 249413075 249413077
    0x81e0f030c0d1407080411010201060f06110c030a051f2310090b0109061d101107090b130e071a0d05060607170f131706070e0616030e0303 61
    0x10301c0d5141d180c00841c0610542c038160061404104140d0140c00807070920400042c8040c0c03000340050720541001c01901c132a82d20035800760004004450340c4e40391003900c070440102280c00148190326030344180e00300c0003010f10700810050174a95200c40105180c08588002d94009500900314600d020740d66100c3c040b250340404d102080764900b200c03001c0214a05041130906070455900031183c098030300740c030302032031070360002041000e80f9900d04060b00c4482d150400803070610300c1080c0060300308425101d0600000c1e040010040000010001da50078252291041400c84440110302944182108607a042c1c040f20750b40f007100007281c0340c400d90307000b03d840d00f10750005100032108104202e400000c407606c10304590302c9055000705046845a19140e100e4503203d40e40c003040c1c20001c41001002404241d210410400c4402c2018840700780d01030607607074240c540c0c1c44120301d01e00c00c07115004010019003268852440ca24102d072000742980e08254841113209903845061900300e0078481e81d48008502a0340c100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 249415575 1250 249414325 249414331
    0xf0c08070f030f080906040b131401060308070b0901110d0b180103111008011d061c05011b020a030c0b060109031403030103020f0102150a0917030405070e0c07081e0f03 74
    0x81c07501e4402580106008184c0d002c020400c4000c0d4100c0c03001d01000400301d10403190801d00242c6000700080709801d0542103050f050416242a45c603060300001000b46641c09041410300071a07001c0140d030b40b295281c50982d1403c205100c1c0411080207800e017028290b82c0010a0b1941c09003a02d40707c00f8038413800040b4090280c00c141c940e0a00209000c49500d40300d12407819540203480c004901d0b500d000e204080d8210300305040c2c289252410005080c64482c015403400700b00100c0482e80710780f0356074100b050082c1400b580e1125046d4200520008160000903050f99060b8580c0da0100d4001041d141c000e04004041c069604000c98441c00002040c00d181e051460720304c504c0017443d42c0e0351440c070403c0a02c186103000c06055410518030000b01c00300030040558040c5ca5076001244004a038030341840100d2800000042180c0084203200502c03400181c0c03501078411243c0b4444458448540e800024010400e0007081c5110800c50b9524402c06941410585007035402c4043c01d100b44070040c900c040e0012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 249416825 1250 249415575 249415577
    0x3060e0a05191503020d1e03030b0a060915080901020f04141801050d0b070e090703090303060608060a030303020d2a090603060f03020f130e0f0c0307060f0c08070f03 73
    0xc90510a5100720502d80112258003848108003c041c0c0a40c40c403000c484512010340304240412202c02444014820750003a20b2241440640c242e250b4a0044d0003403d0b64510b96001d10b903c07540209076503024032560401d960080c03035a0701e4a8072121000321a40d11000340f014206540911000c10503401d00b0000c1c0001e888010b5480300c44404100a0000b0b61200740c649032960707000c4000410040d01c5425502d01c443d504444400c03c180d642c82029035522181411403030b0411510010001000c0d89503001d0104170344aa40d040c08020743d9000120b07401c80c0184c840c0c0340d008103006003c0000a020f94001c003030310b407206003000c40c014a611514001144209085030300c020191900c1d802c2c4582c2c0a10b800014151900b41000702505000c0e0ae0310300d43e40107010084c001d5100141c00781450f99003c07c44100840174000a05c910000b9111150319402d09038403000301d030301c202e00c103001e424030300031800c041550b1060f40d075100440507040044a0340e05007a1030030764600604100c400d0200e0f03402013001c0c60144c02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 249418075 1250 249416825 249416831
    0x4140d02030913020310050112020903060a02031608060102030f0711060304030302071401050c090f01030209040608010605040b0d1a04080c032a03070b071409060403050d0f0504061e03060e0a 84
    0x40040c007161041e0001800c3d416441081002584280c40d00400242d075003e00c0c011107108a903005c201c009205500b0800e615101e03c000b0003030b1005050b00110302c03c8002d204e4031074030f034800032409480803503083c0c0e941805a00140650145084c80c04040c00a040c022071000400d40b5501004c04c1180d40142c0302074001903000690402400688441d0303400c0c20068000030403032446c1c480205c40c840d00611800510070480b82154030b03d60781c825010f0300c861800c0188108481d07965481210b00902c81d41c4141c0d0f000707900340000e0001620705050900066900001b0094641c41c000051004001c40140121000300041c4914944c2d5002000900360031011860301c0d04405020034034406080103003601e000101d62041180c0720000e00e00a2625030840594100203032541104c490f95205401001150b80d0005408903000003407200c0052194420300890301c0e15014110a01c104032001d05c1680034500102e071412903507442c0741603e8221040351a100d0b10300022070702c0d04c5071b1518141081c2600c1240c90b07103072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 249419325 1250 249418075 249418087
    0x6090207020f030f072c0907230a090203040204021e04081c020d0f0909090b1b040510051c1d0601170c01050c07080604030807092c04140d0203 63
    0x101002c0d20b064a4408070b00406120510310a004c0d590140780c0103003035445040081c0381c0d01202d44145031051581c18214946007500d0080100c0d507940300d407403141c11022003146540d4007582c810040b01c00700320039000d001c1c01340312400c000c4004003070340c00948201e801660801001100c0c40e04004c0d12244a03000417511982c82d4036104030340303142045014031683c45051000c40341d0780140d0002080c0f0f6060900c0c0c00e1180c42c3c01c0144030705441621107036022295440c24107000c003081040c0004580d00c81d03486500e00548090003448501c1c0d050045004003a00440c0d00d50716a000b96000350702808800c90150316035450324240034034140c140d074078042d240c0440350203402d0500d4104005102140c00360108212918a40c0b8500c40034594601c10741d040b00707051200c0094402e01104080c06414003502d0942c0880d00d480c1040e1a00a00a01c021901c610003c0c8200b000030820038800a1206043c0c204c9074908403520615041d9a404000083c00c201c413119003801000ca40c0d854180f014100358000340d0042c41d1200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 249420575 1250 249419325 249419329
    0x110301030b06060421060b0306090a1703060609150f0d05162a0302030f0f0c10140a180b091b010c12080915010e04120309030e060c100609020702 64
    0x81000751009210703e805200510604150313543c00110307585002c1590190384140d00b840340c014201401025010300841c0c0800c40f01d2080014500c0c1d08a114102d820352008007840e0007002800145c1c1d1941d0703c410100840c203060301c0d0100381c01980c20525403d5600d880301c0b103c030a128940c00701c00100e4100751203c1c100011100a51b101d40c13405132403418084180c40c00740921031001d240c20317003550391000c20700c4920406051003002500d001c107812802d5645e0300d046012208806401102d801b40b01c0b4443c03102340407280c011034040d095003100380456a1410340c8403008c007200504401c1c0703450794041d18900310900c0420f0045c8034190203544080080c0248010300da0007011103801c1c04402a040c8144507681400042c0f074500024152207291a0080454481c011401d041450b41001404501c0406001260034048403500d40d000e1840741c9102c646103500800160243e41c1000c0000c1e01280c0b40403114140350511200500c448062281903032181100e40328020b04445460300a05150755010981030214 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 249421825 1250 249420575 249420593
    0x6030c05040e040c030b0a15090c1407110f0612010b0a110a0b062403150d050304060e0316080c040b01050d090606090e01090b010924061e050306210a020411030103 72
    0xb847e14081440200100c0c10b003111450814820342c0100f0b1303618030903080c95502c03801040f1202510110b0709035680301c0a003005529030220300c0103140b207000340301200020703403821a08503074440402c2548429141e29103000070085400802801c018810728890f10b0011040c18005042094032945440e0310743e080030018021202d141a08108030914804e12a0250700704480c140c0341d210f5082142e0303403946c0a1b5140403969412031100011b02d01d01c80454040360700c94220b102e00c00c0d1168180c1c00c84115544440b00078055000c00c3c4200700c5250070248640d0300d141440d41122071058010f0525614020341c01c24075604031400e416082c0d5030347d651004240318401440c00340c01d4034083d4845c0240040d00d200e40b079a038800a410301ca18172440d6683d41140e20700d024514261f1044504501d000703a800c40d41d50700042c0190540d90411403403910030340f908900d40c81c014404d9a00807480540a442c1003020318203001202800140c2c041c0179480b62901c2d00c0c0c0180d4590207800c1c07007659500f403c161694558a4100c1342 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 249423075 1250 249421825 249421831
    0x14070b0901200706020c010b0402120103050f0d1b021203040f05040b0301020a050a0f0c210305070c1110090f240c02030a060504230d02190c06030c05040e040c030b 72
    0x45551026824140b0941a8042d1680c0307a40020005985810704030708640140401e06000d0b030818000304080b003074800d00d01070340341c100c90058090361046c141d002c080ca51a43c1040c0c0705140451050310780c444451a40350107a00c00144003409418410b07120544c01441c68201d80d103d4005400030120901c060309103401040d0164005400a504000c480d0724050054091402220100200c0748000a40c1a200d04070704a144e1f60070841c100300018600202c00700035120040f1140210b820003000c504502d105200090440f5040342040c108585a60100042c00d04688051010840780590104102003041c080c4401401c000e2049802c06045400c01132001d8032440c1e0f14000d0001d0181c2c1c1c6005a180031507610b1803076911200028140e9114504804102205117103400320030620740f404411082c000a1055010445808403071302c803a1130280e0409044140c0f18000c100c181c94a004000b01c1b4065001350310a00400d04080e0305194480c09017000f03e07103044400fa0f51074081403004006110901c088207170 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 249424325 1250 249423075 249423101
    0xc2d19020309060307030e3406053603190c060203030f0f04030c12031406030c1f23040302130e0303070c020a0803040603050411040b10030b0114070b0901 68
    0x4142142c10300051018000100800c00745a01c40d03811440342070080c00a1000304e03100c4803459103801042e404030410114201050180e2503442100402c515010b10156008100001040310091000c038446c400c18014212801e11540031240344041166014420203680d0600e880445041025908044d101c02146030f10803001e40d007013042401281242405810b41c0321009001542d9180c440b442c003120185046500a030124400292141000c0d0707040d04040014082501d9400c0643c640c0400c15445200d00150564080712406620075500c0f886121418403002c0c6041a03198000000c6220300d04001079074184c10b12560002d02442103140580341000d54800c007a84c00c01543c03854100f86940d0303100143c0700b8030500403450184021551400030300da0282540c42c098988336580ea850141c040d0000b5241201c07501c0b1040352050290a02d840384d042800c034000c20030681413080f600180c008044141025041001440c520900384000c08028683d0070302c80d042c0070f0903a1520580c0a0300311020030140310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 249425575 1250 249424325 249424327
    0x20306030622060c090b0a0f0f02120d0b040b0a06050705060a0b0108070e150c070602011d0c011d030a111003050c0418020d09050703020a09050403080c2d190203 71
    0x118100b0000103641ca0507030301000006900e504004199074520551788406890100000c0748a0166806144004100301640701c0c5282010600001c0c2d840b08004080d24003000e40501c10400ca03484c1c603030008281e00501410009012600d403000c1204000240c102c240407540008901c0c080003820040c06500058100081245081e03800000b4260200540242d0400444142c0c4072243c2c0d803000e0f140c05102e082808690303903e0240c01405d603103c112903c02c5502551030a00b03000c9042e1064020000444586006032101e40072540043d100070290384440000b00d4140360707110400340c030108680001a8083d40f100084030169004010078450081e1701941014101001d008202d0341440c1903030140e95001c0300c50540c20b02c20340790322402030044c0012804039509228522041c0103011030f803101541c3c000e40c0c42d045940d440703070301540541d40140c07002800141004000340c10307440a003000d000703014406203031481315040150980b030005040340448041c00e1000901400d80600c0c19a030b007008818540055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 249426825 1250 249425575 249425611
    0x20a0b0c0f03010311220b0109080304080304091509020a0315050d030801150c0506180f070627081b040c09120204023108060705190e03070f090203060306 68
    0x12001c501061100810070400a03203043c500342d8800d5035414010803801011000420070686003800303080200400ca0129000840100300c0c0c0310080100c03401d580781003004524043c58a01c10a00600710640b03400300b80340400001090147e001e000070903201f1020340d0040780c3c910341209203021091076540824480d010154031280029085210141141d41c550b0105411044032182692140009003000704680145010132070798108100d000c4020403d548100c8032441400c0600c560768090b00d0017050301007500120180c07101e100c5099000380000071082d0a414603079990000300e02e082840e4140c00c1e602205685600c0c01800c0621032181c032030303296145c03500c1c1c1c562803c1100c9050f0210100c001e8040c075000103551841c1368a07000701ca000c0010400e4001b041e00d1302011564200d092501035045640500e00100b40520f10500031365040c1099101e680155280b4030209640c852800c4c0d084503014090070314005202e1101c184c0d400000c011115001d030741c038a0f085e810103042c20b200504180ca0401c0e801c001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 249428075 1250 249426825 249426847
    0x30b010905031926070b090102090d0b0603100501270b1c0c030b07170a060e0624031801150f1a0d0513211e0504080d020a0b0c 56
    0x44019059043c403089040036001d828210000603003140303c080e60007041e0f000c00c03d0502c000c400911015014408602c21a250100a14280d04c150450180d200b00c07201e41c40c81c08079521003500740c0c0150004048a1008098050801c1a81c2090f40a0035440154040300410740600c030300401090002c03c4410000c4010010006c1d40c818a01843d01e9005004d08501608000e04600204055504401035001c0e51420f204001c02201740f210040f8150401900410400361300340c014034007680e40b0101580f43c6036450009100144407980b81c0080c9040c1071a0940c091941818010760080002c04070703c5510310120b00c01142912164800c00713203c460320550811941d108100c009040d5811480628881020004019005e00a014402c103c151518042c4024449544c007090903240c4104000c1c0c982c001e01d0400c14684c502e800e05146d001c1102e0400c0300400c140c6c42c000c804107281c01410590308144e1241d4810b858040c0c501c0320040542d0017034204034107214036800c406e680f00c100c000a141c40c007021042 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 249429325 1250 249428075 249428083
    0x8090f0303130804050a030c0f14010c03110a0b09070602071703030a0b0d150902040c0503070c03050a1b050d090b07080a1812050d09090b0a03020d020d0c08060601030b01090503 78
    0x101d4518000e2403000808108043c1000b140c006207002080b0000054a90400180c2038195100d2020725a100440014403640d03144400c2000400507110a1140c1d82c1e5a00c040c2c0d0340c50011080a6002e00071800001d001915501c0303800e000e24580c0c4001c140d000c2c24010b02078900318142e000809040510400100325490010840f0340c440c01860340891103178582004260100c1e02c261004012540c0710905100900c01039000c610410700803181804060a1414107581d140f0044e16140d0004020968120100f4080c400500c0e00e090b052030005801e040c400070015100f00e84110407142604401c0302ca11035103500c100d040c40540011913001d887c21f21107668610b1588030710030515040c04506400344524040642d0840d004211115020303200040c1071802e20f0300d0344001407521001caa401c10001c240490984514200760300c024001a0083d8215001c0058076111301d081281d0118450808030001140c0c0d41c4c444000f824854014911801d100c070000d03054401e80341006d810090f9000f02007000d954005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 249430575 1250 249429325 249429331
    0xc020f060c09040e0f060402040c0503060607020103050402060c0d050904051605040e0a020405040218030d020c0a030f0602090d1b0b090a0b0a0e0a06091802030405033a050708090f0303 81
    0x1241c55680d101000003003409040228074140c450702914401241140c0007182c0588241e2084404000d502d40410098400d40410f03903038a13070421400d007c0e00d4019402a0301c4290404d00062006040565182c1c01a10300f005000f010360005001003001c000c241400d0090340d410a140d4540c0c980803040000004009010f648a141c50585215012880c0e0200e07aa040b10090030003c0d005543d01c090464845a0102c81000e10307038000c2c0b0135040503018803440415003c81c4448002d0020b0081c601d0350300c40725000d0124180550f01d441d030800021003d82e1301c8240c0445c1a505c659480c80600014101858034080307258030035001d14100304004080781c0c0d2100990416901e1030050b0300e0700c8443e2040111114072071003020b55041010300002003402d80c0c00100e4801141e00b480040403030925902d891905901068800508aa10501101d0840800c030142102007241a02ca6903a001e43c24210720007104090030391100d140b954400500c02c01a030301004250f4050001c0c1c008020050a000e015a6a44401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 249431825 1250 249430575 249430591
    0xc05030c280905010b0304020310060605090d030905061b15070215152d01020a0c0603180804090c14090109150e041d0c01090803040603090204110703090302040c020f06 74
    0x501070125014908141e4600601915041004590303154003803903100342d1094406034032a100300000e914211015014201c1502d2850391900d003808807c205015004034903400890610a0040d00030641d071b00d81c6030181254900e810400215120000041c3d0b00b004040703116050516040c0c4104500c25800261084246001901c1d032042e6545400c09000b042c5c1041842c1c6030700c06040c84460400d07410b00c464602144901ca0101561754040e1001a43c1e1032000c15001000044030400401c0824000c0d48184140e1740c0340c41e101c100010450b42d8909071648150051003071250740b0020b031013990b03500c41c00080c41003180400325481e1a00c1071001a1200b141403161142440814402400a0348039940404124902500c280410004103100d4610905401c118904512900131758000940c40b5240350400c6600c8400514545414504120042e10340301c80181d80041c0c81c0c5e03060030303002d800500041000c1400795071a10b2900307086104210030781d524401403c0840d8045c01198a8056011801c03517000014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 249433075 1250 249431825 249431869
    0x2030301030b18153903040507210302010c0905091501030615020a0212060601050334021006060302091806120f0d14031501050309011104080102070c05030c 69
    0xb51402c1d242c600d07080002c20000f6000c0d00030061080030100819902941c40c41c86245d200500a0312000191020301c02890080303015519101c12002c6200b0013180c1103400780040d01c4407903403541500030010103000c201520b41e400125000b01415070a1041360b82035800f5250861106250000181e448c4901030008440c0d0b20f10394582110321380c002c1d40311800a00201e01100d000d04480c00c00030f0340b01c1c012050280e026680c000c581002c0180c001c21817511807581619110304507162040c220310102c9484042445c4030601e1010009665030f1074010b050180c00d180e00800d11420580010402d40741d0551140080c1801072240b809560749900c007041d080601d41e01c00ba42a07a4a00300020f5280ca6400310b150700c60301802401700701140d00418000300c5042144c4844451404040d60b0381c58611048030620040d9000704105042e56114000030f5422449680c00410300101d1040c1400d00c551207070f40314030400ea43c0045e0305420000040c2d4060700510007100500f050180382e10100780010300c41c08032200d951034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 249434325 1250 249433075 249433081
    0x2040e1f08010c1d15030c0c120d0507030e16051c020406030c030302060705070f0f02280602070b0c060601030b1309060207030e0f0a1802071a0103031701030302030301030b 76
    0x10034415004020040d0700000e001d860b4030440d0140c0125498201c00443d03440d40040f1003881c0c18070181140342080720101e02450356460100410f556041580040820b01480300794206401e07004018240c1c0840c601000100c0c0c1c10151340c0034080720003030103210f002904210100c460f800c0001201100f1104155188058400c0d80030b0b0900c0002c0100400070342c80303450102c001c0b05210048000d1000d9034465021204262280700b8203a9090050310030042801e501e80d68041b0024184a180912640c8041d01e038600d05140600c19100075220000c84034906c80b10800100000c560410a0500404204100341e2a2418041c0c10039218080200180d0500d9191001c001e600e460300000407000e00d4024908004002c010b1911102a5105410a60005180d140440c0040c9010750745801c0060000b0200c1d591039141c4801c40340406c1650700c0c03841c0e503682d0078001500841c401c585000b05090484855500a605500c2c0c0540388484003840c0d0070351450140c0050000076000001c680c1502d421082d921071035a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 249435575 1250 249434325 249434371
    0x1308060405060601050d110d2301030804120305040306020c0c040b12100216200102010c08010b030712020c0709060e100303020706050d060512030a0306050f0f01031a0910031502040e 80
    0x10907e1110034610000366203e140c0700c540d0180081400484043c1080c481000d01300044840a0001130030074002080104600381e030040340403000c1d6103e818000d04103641d0703032141c504a8000b00c0c61410503403c19403240342e95141502c56820100c1048031703405d0156001511a5988400d00c440c10310300c050340001c4400b080b1100401103412070b503215642110907001d103c9409408010410410b0244d130030101d00e003200354000d80c407041c1614a040303100760440e96a40801c5480c41c4540300f4586116a0800c2840306401e028032005c0054815003c0100f1120b24200d400c03130752442c00804800a2070f0340d107542400001e81c085860310440c2c80300d240441c3c640300c117202c514004144580c042c41d88080c00d0b88101d03114041c04009455844110b460400603135554401b84140c00030103c0c086035201051000c010159070180e4040c10700380b02d958041185501c0c8007000b080312600d090350901d0b0440702075401081000107035143c83c0e62071150724000350b042902e80803004500b006e005d40b024201000d4034206480710 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 249436825 1250 249435575 249435581
    0x7320105010f1409090a170c060105060a0c020609010903020a0f210305030105010c05070b131502070321050d050f040b0a0605030705151207050415080402180907030c06051308060405060601050d 85
    0x45600300421f42100019540c00000580c00030720400b146004101c0001443d14060050319286070740b42d100c00410407a10341c2004103591141d400a030612040c0f007004005a104c0b1078140c00a404c4002c9588111402c240403002d0010084024000d0003121800c02d400003940309040d6411640c1c207081c0718201c1c81c52403401d1030608080382c1200c102c00d6030204000f2400c0024084650840e00c28504003074480b8121502281c5464030b6000c081c3c40782da181d0000300c6c4141500f10000010040f03903e0424184020b00b086039080c1c0300c080e900f000c510919841030005002000c00b0a903001860030908100c502d00c0c1c100400e89410702403094903c5038540401b04032909001e14205c0b6241d52890910b0141403908107000340841e001801110b440380b0b50202103081c481c2c010311289008030f80040811100c0c1071700c41e8956a5a110081400c0d903d07021381500040010400b8600d00082c00d81911459114030782c0000f2100035041c0d42c0e110b40354070707881081484003141c00803560175001802882c010340d4503450101100d0107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 249438075 1250 249436825 249436843
    0x902160f02030a05030d140106080f010303080916030c080607081b071406040b040302060a09050304180204150c1509110d080421020307080309010801060507320105010f140909 77
    0x81808002401c40c203206c2d00b0380c00000c0201c0601804815079032104801c13981e0785402c88640c4d00d50403000303005001003400307005015070111a130001c440210b00c523211003105060403a030040fa01c95001003c140000d000c00e203e007a51011040c90400b01e103240c010507500f440d4028000140842e1000a500003d0164049004c91649401000c07207000d41402c0c80c2c500c110310422030301540180180c8001c15184d03403590241d2000c082d0404025400e15041c121192583e804041201c07411030b50821000603483d00715411a110340c9526200c0c20006403050a003505042c0c524a200354a0034904142e01e00000c0a650280300c803e80169217a803c401f109140c040640d104641010349031200c06103400d240c000301c918008010b14401d4069820007a078540c04140c1c3d0f07000d014100d9000c035404000600400d84a00c0142c0409409481140901070b01120700d100007000115290382e050520314144800e9103824001c1a0043c2254140700454900c0c010048519040b60482e0714071a524140c0887d4100303800f000342c810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 249439325 1250 249438075 249438083
    0x412020a03170309010c03050c091c21180501080c130506040b040603150e0705030901021306090303020f060919170d020307120501050102120a1101050c040f0902160f02030a 76
    0x2c038800e00000c0c0d2581074004840c0e08030290708144c10951442d100b0702401e40141541800d5904010aa1040041e160b013021004d8144070003003100000401d812951f15504400d026200141c039072190040100400401c1c00c0308003825150220401c0117980c460203541d80300c2c001c0c20915807206032048100011900e2a88055803092000c00c0108003000074000420444680e610204003643d40c0b203041c4000030819120f400c1000d5808400101d10501031001107505c90580000140341190543c401c0345c0c2d40c3e02c281c114100040461000740b0415804000f8416404005401000e26160411240d41d0703908003892a40585000001e164040001461540c039001c0c080701700854488001c1810f410081d042150040d0009494002c0761803000c04030312501d03050320010b80c080c3c0700110806003505619400203100400300708800480b102500c2c420320500340151802c40b0300650341e80c81d015003110303180355940200c00c05034130402000c041409001d0a071601980c1c44000140040ba4034000a030400d400198050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 249440575 1250 249439325 249439343
    0x190e160e0a0b0c15040c0528060e0a053c1518060a14032d040b0a021623070f0f06031e0504051905030705060a020a050412020a03 57
    0x110382c1e101003501a000e400150000c80b842c010070228482510003064030041c205100c6e0000030702c540d0030115100b56501c00f50b041a003400d8410b601409480c0070481e4040b00025540760007212144c40c0c030203c802e0091070215440c402c1d0401208118034034142d03c42e41c62130b4022845143e040300151040d000c4503084d000a0125001d05010100c0c604031358060011100240c2e00c50510500c980350080940b11041e80d159128480c8182c95452110320b5880508804124800860350640342c43c0f4601800d0408240d42e42c03001a01c3c1060304e44200540300140c21a244203006000f00e44900d0850741079060700a41084c00807080c1c14603500200403040c81044602400e000307960300070807003213980c600c800111746101000c403170500c0e925501142107940d1103030ba00020b01400c190510985460b508441d4106009a007920540700100c10782e03109034691a04119002c1d040840c80b0824003005002c00380d0302c0060098250301d071150021000301755110340d000e081c0e5039104800b440e0065498411a2102541d4007400711 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 249441825 1250 249440575 249440579
    0xb0112020747150f1201231f0915030609050f060a2d0e01020426030a08070c02040b090a0b01020f060610080703140a0e011803090b09041803030209190e160e0a 70
    0xd0640707a07c040034541c41765403183c80403444402188491440b00c20701c070b20b0180403050600b4415000303051411002d074044004e180c80400032580510440720443c2c403480003400d03410034200e800382c203108008101c024524603021404c50111840c600008590a5640511504031000300501d8000c10440c00c0a01a641c804a804200300301d44c12000141175400c041c51848803803842030029a81e02c10400c4400001c0e0302140814021401500007051807880100080b4504d920000420354141007295180764054489416425550f01840f10504009401014004a1030100c01155000349001d920310f01700b128850014202c01c0c807c1c4d00100c605e851034401c24500d0b007030a0829001600c1d1000782e810155203805d1a0749441d80740280326808480d8907489120783c0c41d01d008590314181d0404517626030069140c03042d40303100c511050f402c003c800348030786c07401a11081440c0c14401c2a14014841c58000e8950b0041404540c0d9010046035105500c42d0128240501d0035000300c440e03103050f40d01e61741c10948103040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 249443075 1250 249441825 249441851
    0x904110309150c0a020304090e0c040c180803031006050307110109050607260606090411071b0e0702030d150b1303060c030b0112020747150f1201 64
    0x582da04030080b0b81403122007502c81200d00500c502c600c2c054800076070b008100c10000c9000c150022003a40d0468406d8030b500d688101c0204054640c1542040e0024030089205101e90507100c03010405044130f60010340c154509060750400c0c0c01e2032130082c0800c1c00008000280700d14802d49a030005c9400c0c00c0001e0100d0429032400716901c1d142503c00c3c00108880b81805202080600d010806000c0074040480c443d80380e02e42804900d50000c0261908551141501e140c120186001008400d201d24040c2201113050400d59180c0300181c1c005007034629070358040c065555070010a40b00a41258840007903000d0b802203182c0b1110b00a03034492030000c500410070940e1098242d4490003100d004801c140942003c0810850880f440c04035040d0101b506038803c40107a03203255000e04140340c4105c100000692140718805441c440b1500140c00c44010202000c4e9525850364114042c1c0d400e1000300391007414030100042100902c400c1450150784180790706006a07890080806c4480c01510081160103840c40e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 249444325 1250 249443075 249443083
    0x40e070303050702030c1206070e030f03130906050d02060307140714010c030c030501080d05030c040504111801020109022b060c020102042405120c0c01060902091908030d020904110309 81
    0x10240d05c28040e503541c18442c2e040c94103812846031202da014000340c0c0d842c00000c2e01e220b00030340307003890301840f5444408060041c2000100030880b00400c100c2c403180d19021620301038401542000340a004035182c0c45005844620540380c000c5170300d06040d828000b0780364895519009141c005042129100b90b01001610306500520b681c04850741d0612044414030340507000d9440c20300c20f6013550340c0030700c45101c085403148010350b42025001c90502c0c03600750f48000103800e4461810b0f0301c0880c4000005c680b07013585c1c41c2102501440350b0a000a11208840e1740000d482050748040404641d07018210183c5c6030a20351881c42040d50f4001400c1140c4040381c807000307000303400a000e10440c0315482407840911141398450101c2000c0b10303944803498401518054159003801074203040700da44060102402018080c09000b01070400130f00010303198280501000402070102c4101042c0305035903401800301c1d10010045034482d195203600540e44081100c0400c0040440c3e10080340017035404428000d00c110003103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 249445575 1250 249444325 249444337
    0x7140706060b0a120905190c050405090d0f0810030f0317070306090608030301050f06090307030b0103081306030b0117090a0f11040606140d09020109030b04111f0c020906040e07030305 81
    0x2030780303124084002155075000c45a0450380603085900050141380030491070341607010004e1080301040d40308e580eaa004141501c0c410750b80e004142e001803a1110220360300c92070b1401c0b02840c6241c00c8501e810001c00451824000e4000a0141e40032f41c80d1070020302d40900c2d00b0b51101011981c408103140381c032403c028010722582c01019070703541c101000000e02405c004162410b07244024040b194403000302d010400b0300d130f100a8003d030700760040c541c00001013601e9190240c001d5010303041e801c1e540d0000c894030159103501d40d0001005c2c180b4201d080c1da51642e100b13200e2162045040014050750b00d802c1d4440740b429020490003002801004460790400c10507500c4041c26030b0003a10180325494035040180c4032020040d804040520f018000c454260b01e60350090b240341401030500c04034040d02c940b562404200c00f00d03810b940000c88400c000c2c45038100300848409110072403030072600e80c600004004007206107864000e442811500041840c40e034883c0c0c4032110f01000c034021135038010740c0da18001d02950841 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 249446825 1250 249445575 249445577
    0x2120a0c0207060c05120c0f100911041802120c040c1206060302040303050f0703091d060a140a03080f1303031d0901050a21060501350607140706060b0a 67
    0x28480026914010000c0304c400715071020150104001420801c02039402010070762030244180168440c03854428405049803241e4050089040c402c2c40c00c0c114881c0c101000e0076401145000f1000c90b10003031101c009017000341e04881c0040180c012005640c81c040d65081c1c9941d000d4a00300a5441158104000b0300b070403c0c14903020301c001d980e50f480a5040b0b004611000d40403840c10000c410411076000001c1180c14820308200c0b400760f407103154048800c2509804140005080340a205452400201c10300c0140340502d080007104118a020901c1d80c1d05502c8000e00c00400483d003000d2020310740c400c1d14469a84900d10045003980d0381130060606c01e8000541c8905820609240c00300c1c20040b010505980300680203030703803103450041a440340a24000c9040e504075446229280060900d001c1d0b06d0003480ca040f80d0702988002c1404035840c42d440504411416400384400114400f404502c3c1c1d64440c0550030942d284105c0c40461140b54030950100428540c9440c40214240d2490f4010b80000035003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 249448075 1250 249446825 249446833
    0x10e130606180b0405030c0d081c020408190222091a0403081023030a021504050102010b06070b04240915110c0c150d061d061801050105030a02120a0c02 67
    0x15902020105100301d001703168043e0803020725018503081451015050911070704099240070b2440c4800ca200100108180080540000781000071032010850070700000000e044520101c5220307400502042d01d0f58182c1d404041f5004900f1010701c0143d445086c60302c0c0c201c40342c0e24064844003546007a184c401c54007200441c8143c0003040b080400c40300c45038191030400701204803c407000100050322200d0b08818076407622550080d500162155003116100060a40b1070b140c40768107000019007510303a0072962500400c0203108803000b14101100e0740c4d401c42d400000f650031111411045100b81a81c00310900c0722541850b00e020b0802004400c0c0003001211040100b0000002035981c0704a4499100c480120380d0201c81d40d80d210b8641140c0083c18001a070068914107001c00c020039003941c41d076a2020304040558420b4451902e00009055407211048400704000d0100144007608450180282810880080005202c01c08075034111804c1115070980c0108c00d20b00300a030345003e800582e03040801800f0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 249449325 1250 249448075 249448079
    0x3070507060807170a0f020c010606091413020c030403021c03080106050a1d1c11040b0109050904080a030b06070609051c0207090245100905010e13060618 68
    0x4461000315001d07504030740d11500f403940082050300080d50060301004a0561b02c40d00d02910000328030007050210074141c00424000c4c600f08000d0300c2c00c0703180d40c004c0000b008003550000301c5949000c0083e10081c4485030040c0c0b6034540d580801c0c91400746400c001c0d008102c0c22001040d00c0e091a0a002480340702e9034551806a0700d40c181103c40d40500e041c0b013008212070111052440805a520752000e01c805041c0d0030762300b2140d025450090400038000d4600d0000c1700f1031408030341060300500215180a0070308104442c90540400c0c00303584000d0014041d0351020a400b801c02c1c3c440e401070000d000340242160b403540c1060500070000c01042d00c04843e40e1049002c00c50151403007480900d15680380303801414a003403520b044400a58880c0100d020020900c030540f59101d00c40039001e18000c542c0c2290381e00c41c8002d150f031038085620340d000c1d40c6208042250418070260343c000c240c442175640c2881c0400d0356000a2002c83c6109030036842d40000d85042003c0482c00940c0801d0701c1e201d98400309080d0382010303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 249450575 1250 249449325 249449327
    0x1204030303020c0721051606080c0309151e010e010503070308070c0b040324090201020304090b010e0d03050406020706091202100c0614090c0a0302030a0f1506080c0a0e070819021201080307050706 86
    0x40c7c8503104200105080f140003980340e41c003007405542c4c080084401d8603140c40500a889000c10022940b00005a000c4825219402000841c0a01610741c01d0f044582950410002136903ca00900c001055950005200c0080090503130345000202880f07040e00b41c40795128a004000040c034000300d880c940b59001034081001c4064001c00901703e4042c0c01461409040140f8034000e030016410700d6040c09459034000619468181c480c02c0103d000ea86d801e915036080c00d00003401c0292aa00041c20840032030000d1110420301403030079014550480302132041c1444000159495428000080d001074a40700c0903400c4d110302d000e1110703c1038000c3c0b401e83c0d00400503881006454541303400b000e50154130100c010300c000741903408041501c038060140c62013045601000002590f41d103070481102500400b011180c1810319900c660040c110416039004140b8140c0001400d0840c01002c0c80d80400000d0718040034501d5940c101c900c20410340c0d00d903811a603151038846907654010042152103110300c0b600041c002d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 249451825 1250 249450575 249450613
    0x5100b041202040e191203060e0c0403110307180f0f020a0c02030613240b09040c031a04110f13020c0105060f1008010603020f09040c0206090105091204030303020c072105 75
    0x50600c00300c41d07442c0b040081c0c56044817407415041000c1496030711320020032701980e802c01280c815072003001030301ea0707880c254038094800008107801503020b80c0c4034100034041c3d50b03542841145002d081d03600005090318004500c6003e8a190080d01d04c20a100148007a0040c3c0d05c2688100501c1c02075080301c04584440302400140c15001201600c07010540c1141000c0e9075407805100f03080000141c0201e00d108040000900c5d00700182e5044804000c10b490420801c00030440000d100e0b00e40306405400c41c41e01d0b49071980c08004a0403403501c20381e43c80c1e24000b0f00355164201c0d080c5903c032480007151100c0c14400311500038002a14002d120b82d034880003c1c042842c002601c1d200c4945c856960000992a00e94150041c2d0403452080c420110306002900598541c3d116075012800c241c0d004042c1c504000c1241400c503000074254000f40c0c0c010310000401080d5050442e801c4a505217801a40c0d0380e4500740c1c103414a8815004485040075610010000c44d003090311400b0401e00960640e00000320400c001058 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 249453075 1250 249451825 249451843
    0x507030606081501110709140a0e0c0f01030e0a170901030501080a021c080408010507080f06030c010e150c030a180f03121d0307061e031e05100b041202040e 69
    0x25042907030362000070651150144803c5c00c2d111404031602c00783c880040009039078070f50034071181e200300c0481002448001800759400038071810b00980b1402c10000042480540c0070150703e81450f0b15108507103030008040080e81806a0000321041019100c107034840490fa0140d07500302d00090500001196028000c41c5030b01d0317070541c020503650703864071186480b4814070f5418006540105080c000020181400e00030315100d18041e40e01e15119282c070b03410b80705d6865405400c0c1c41c045c0e88000071920150f6001040d10300e038401e0807641990101c0540c1050300c040d109202e0071061900020071205c4500d5041540e0100c4981c8010070f05400c2c0303883e40b00e00c012030031192101910741819005152a024002c1c2010400391850003203802d8030703121400100303192840c5d607880440000c1c02c4216070b103044a01001c040c0494005460184410b41d41c1e10b80000074085800d0604509a556001003807080703118018074002030051017805605c03a81c0e0391a106501c020702c0c0000343c6c0124106400040b4a402c00304582c54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 249454325 1250 249453075 249453091
    0xb01080105060301031e0c140108130f1e0f0b0609090a0c060f0908191707050303180a0512030a05010906120f0201020f1504050f0609061302010315060201050703060608 74
    0x4110307032864a800da01c00031b1050855030344844050031200851a41006207014108001e05034241704d2482d000180082d60060032406d2409200320004002101c90034070503c6e441c5c100e010104010440c0201011400e46000300a2100b115999004100400c0d84400c5114010807500880e540d0381c0c041e0903a4503240030301001400c40401d49400d00100d405950000c031180202d10744030b400750b51103820007840c004d0a144940c0511040882001c1007201c222071841101c03140a150f01e0420718aa80d03410b80d640000741280e029440c2d039801c2c950703204404021040d05103410400f268294042103403640360542c0241c800b2002c503030820001080c21710040c000d2038201e618052210142400507100c42c100c801064000724110b0090f9800c400e85104200031003001c683c0c0b8000c40414a0920f440c10f00c0c6041c0682030400d2080e0015802c221803044040b4086601100400c83c540380c028041c80124020200c081d10040c102001d080d005c21034550560201d40709045903102040310b20f0300d900c03040c0c94458040390404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 249455575 1250 249454325 249454327
    0x9040204142707030c0e060403111525080f040f03060e01060311090702120415021506030c09040609060c050309010506240a120908130905150409030c2001030b0108010506 75
    0x4107807034800c5d488040d074910700389800d520b840003410008020368015442030707440041048000a103440c1943d11340d9411007003000d607a4030349079640c03407080040654840040c4071030140b070207200c00f884611001c5a40b00188403420540e00d94aa00007103000014900007560035030324100700e54540c22030500c10300d030950b60800c2088e0800340c0c2400400c80c0c14803005040c24214050320300301a52840440c0050b1005e020190000034442c0707013101c2d000f46400c0c0400f100185512081c2e003070020079100860507442d4080c00f40c0e11030015555a04040c0041d01060b50020225450400c2804842da4400c01544c050510203008dc000750320b0344810041206900409090541e102540400340031000900402001c919400c0c0442c05c080801007103011101e90700e40c02c4d20900f10001d908c0384449911580300d00641006a8100801d00b00401010010710305103076943d0103240d981803c00e09140c020304001e20001d034131032265100104d081742c90207502e50442c0203443c04a800c01d50710722042e600030b2514605a40b0040c0c246 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 249456825 1250 249455575 249455581
    0x1205030d020a030e010e010c0f1e05160c0b0715020304030f1b240e0601080a03200105100e060609060706050403090503030304050607020c06030c1905090402041427 72
    0x3840203500100c4000c1c10315664010340c0b0400002070098404403005074000040714143c809000d00359884100d900c1041140c00525020911910a0b40c02080001407900640b1080d0f00d80903044204520b290290a41030051000118a03040710002c2041c1481840c800700c02c0340000780f1420030b030700060718005c2c045111941030319035091003560014100e04050a10182d40451600d5524141c06010280848131200b080101410103050003a8861146020018009585011401521019a42801001c0050b034602c01d0307000711141c0b10b03000e48070382c4100e00803c9203081182e200d581c0d4040c40d106106549810702c0004899203401000e41d403030140068086450800c2d030303036508002088014021424881241c00c00314642d14104007031840741d0b104100416003420030344c10191030440e400541714030030b003010010408030880200079200100c0036000110442e51003014150381038001d10341c1050b0050b1003c20001070403101c9407011042407406540c480020349001340b80326224a100e0340360f1001080d0382c0c404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 249458075 1250 249456825 249456847
    0x1212060303020c040c09090e0309100516030e0a0b0a0f12150306110f0708030711011a10020f030d06030b06040207080f03040804030203010504110306150102060c0a09050d1b120503 79
    0x41403c0d5003400c0e140901b1080e4441c24418202c0e58405500d9001c2c0c0e00106001c5c215042c044a40a441ba44504166040603030300c1d80040c01c98142c00c9070003001c00161108140041d1a04c80d40007001d440300c10030b246d84a10041d200240510300d070b54651800985002c2c0d4100b0742c51003501c00e960720002036600c495101d5040d92075003006001e452982d03480903101044419400d1030018040c000d4a44203561090f581d0805070350007000d000308102d0744841d0742d00d0142007040403080d40c40001c90085040d506083c00500c1503070241c0c14120812003024150000003a032860069059100c14252072107004209101d84800040c40101d000d6a000101644010822002d030b0910303141c05103038080c0c07090103070524240c3c40303a01007403d440341600c01302d410048011a068085c0380502002e80d02800f40349000d004410000c000075560007024106801192001541c1484070340300d81c01d5203014007009002001484503a00e042e14403103001605808064407803120104e55200c0d00e100103200c1c980c00200440c108041c2c062 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 249459325 1250 249458075 249458081
    0x160e1503070803031513020a0215061816020d0e10300504120c03020d080a140c070c0611101e0f0b0306010510050d1104121212060303020c04 62
    0x448240d05100d07112002030300a90800045100710050100c1c1e42c0c5004448040c000040340f00d455910201f401406001c803501d40c000b81030136036001e811601810f80d0700d414010840344001412501003e461110030449a8200c82101c0b1003200f5541d0b003104c96000b44040100d40039414070f48181d03403200307421103206141e5104020004032801d8001c1118a00c00c50100c2e1030846c003c1105804541e1501c44081206000da0580f0a684000007410842814605940e000391148074800401041c4890040070a02d00c414a07400072003042d01d8502c20003194202828540d48503080720b00c1c111000741000c040070070054410364100c00c03001100001004140781d440b9500703000d88411001c00f480c10001251441c100700b200e010b044404040c003440010380500314014913007003c005030441d5000f61441801d101e0242d07480400c88112040490b800240c4207942c01c9900341e10b10942c0d20204401d00e05a500c40140200c0707040d091101400d50f00e410029134403c042010907504240f2010b8056044060b0403401d42c24076030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 249460431 1106 249459325 249459361
    0x10306060e130b040e010f06050d0203030a0309052118010e15070602040503061608130b0106110705130204210807030c06020d020304030f02160e 64
    0x880030388403005854541e40226400c000c9050010030980c03101e101c4100c000c109010b030008610655000e84515400008600d01d0310310f00050300c1c984204003580c47ca9005d0060344c14903d031a44247e00801160301e091b102070040410341041d16840000205400b89540380003502c501e140d0250005503071801e003950f4140002d1513191010380d40c4d41801201c02d03401895499070745640a10f00040603007d142e1096400d4454902400600c3c3c24142506d07031b03601e51541c0c4035522595840c541082403252444003a0172000c1e0400144201803140958100305152070301100d0707020360344038041860304811202d00b0441135070104023800060003105180078408011207030b54550103c0c40e161000588289907000f0103020114210320100038540e0180c84260051000440d16450b107401c4c0503004283d0001108018001d407040e800c5c02030141d29420059884034842c0341090780e200f4030200c80310100c2e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 249280575 249460431 := by
  have h0 := BRFrame.cov_init 249280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 249280575 ≤ n) (h2 : n < 249460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
