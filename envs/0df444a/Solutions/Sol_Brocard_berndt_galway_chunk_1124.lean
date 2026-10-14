-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1124
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:20:35.480441+00:00
-- url     : https://prove2.me/submissions/5d045c72-4323-4bc8-a70a-fa62bcf62c5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 201978417 ≤ n < 202158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 201979667 1250 201978417 201978419
    0x12050a020d12081e22020d03080403090b07020a360c0210050c0415020a0605070c030e030303041109090f070b070210110709110705160f170c0f01091203020105070801 73
    0x6071200b016039213022402d07220100b2012850655054981050000030003503038101400b41c0d070300007070865071000d9426030119040c8800c1c0024564080046800b801540ca2410f02d03002065002c241d0508030ba2090004c100310080492030850200c1c01c0c2d0b01d04207550054503043c0b03001c0c21208600140302d0ba0603d20094499440b03111f5101d50b66010700d030300c200c406807034440c1001e1a090b00c00401c00b0403404200d086008501d61100000c405101e218010781d056603984102002600d80600720032406050648240c0c414000c01002920646c00d007030a58809445074440c1e621024403051604d065070103514020f000305100824900c10442c0506a06402107038a6076810130a1041900c0092054001540503004004140090354164000941d05000002006d00d01845600c1d01800c055003207003078411160f4000c808100196104607440007078084c1c040002c1135100000c17000c954407185e0400490195014605010007603010f0300c02c0c64010304540320703d004103180c5031800900904c0d08440c0100442e4032200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 201980917 1250 201979667 201979681
    0xc0305090c0109030605040c0503070b121803160312060608061302030144010209030f0d120b040905010c080906160906110c121f0c0912050a020d1208 66
    0x303191541c1c21410b031a094006400c68450501a0100030000e842c2c280300c038180005c054504110b410014600340f00e143ea10380d200b0038100072a00f00064900d07042564541d14007002c0c00404011520369459024020300b80500b5841e040e40e48561003540e000030985040ca0024515400c0030400b48a1001140d01d12440e22030500c403d000c0340028064030b11260070704e03d0b0000c1d151500440e008030b88001c100c0c0d622005250203041410060060a15200300c1c3d4011900380010300b010032203400060401c0019218002c0c00c1d0b80028201c018110b41c0340032107078490303240400d580c507240d0141d05415004070080c86015241003000d0700311201030740c68018030f100e0240041c40100c50801600581c0655980350103131185441000c84050013112484100d6000d500c4840410703940d001c028011b6850034102805070261041c540c445e6040c65407029040050030103581038404e07680550a04180d4400000e99031102c28035050071450031180301c1c0000d410045500300300c014441c402034482416000c682d02c401156031124 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 201982167 1250 201980917 201980923
    0x6060f0812190f0e061812120307260901021b0c03150a02130311153408030c070606170c040e16030f0303060f12080904020f0c010c030509 61
    0x500d980b54007485800744511014800c80341040010308514000944203070300c40009505502940306421200c0c0c41050a201605210240154049020b009452207060a103105401840000c26034000c020b040f0711940702113082748400e0850500082400080d85c0362802c03c0754006d40c4020107685013a0130f580d64031140603400141303840c0c50000103009055003c0c0f0384a001000000d018107460001a000e02c03401180d406028030240065004a10300032400900b0402e000000d81c6c00344050b66500010041209848000e0700c8640d10103003440d00307211507103920900414508078220f0004150000001c14083d0402d540310252804501901040000c5682d8920100500b5450007400405801c4603001890b2441c25034030400400c00c01105a42590042e001a03050329034254108860402c0142c42c900181945449500f0180400c642d415080c1418810075520a50318040003c00e000800104074040b51540d8065400b8111190f40b03a0307844100f82c017002e034084c20805000da00000c3c03601c8006403410f0400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 201983417 1250 201982167 201982177
    0x705060406020d030f060e040302010b10090806040f03030e06070513050103060e040609080c0d020a1101020a0b130318080307050105070306050f12010212100e07020a031e03060306060f0812 83
    0x1e40c005000d2410480002d0f0040c2103a110548a20f9585200001e00c82c06500d243d030340b1a81c82075000040001000c410860500c0700000d96404104040d841071024100000740f040d0040d8025001141080982c64110081c11110a100510303000340010f11a0b0260403c1c0640651851760660f5808561144011011907156210300001c2010510215000c902941d001d500c03110b01502c070f210b140c89000c0100c5890041001e02c2d000051380702000c2d440c14820141d110303003005c1c2001d1020f4010841c00341c0750400e031907501514001092002403a030001309130052502c080d804140ca400038410650f20845c0c01e490341c01c5140b00343d6840d4200700019035202e100b4400c04043d030310014040a00003e032074003803041d000004905140e1666007000103013001d1891944462248503105500da40d15801c090201c0e00c00712002d4600c0d429980f15400500009810060381071641c00e505400b408840052041280500125407015000c94034000c03004c10140204414103082d0340c202c10844452b6100f10340091028820 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 201984667 1250 201983417 201983429
    0xf010216120f08010b0c0c0301060609060908030f03160905040c08040b090136060501170d0302030708040201030b040b0a030605010620101e0608030307090501020604120f020304030501020c0f07050604 88
    0x1080188103041c0e408028100d40403022007100c40101007c2c010a01315102500200040381c02c0b01010095240d0090000c80500508005141011643c100107016400f0180c01d4401c0541c0300e896011030203208140c1e40008160041c000c1c00356100f0000c000c0c201000965040c0c1c3c030035480200243d0049414001e54817002c0300305500158000403280075114201e050f891000045a03408032200c080b95190003214040d00c0000c501900c0340c601c0c4214603140010181c00841854014020060103580010304150310680a007408140083d002c0c00060040075110309155200701c05070000f006008055000b50305844040c0c403200601e400410101c0c0340d87c2024a41c840c91940490030103044080755030082c401c8003010320804101840c00100030000d0390050b80182e000ea030703c0441044900341d88851580000d11081c00070301118242600e80700000c00200e2201014410101050b003d0140700700215401940c07c40d00031510790742d041c8000b0384c6806249002c1b80035031003004030204540c9412002c503021100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 201985917 1250 201984667 201984677
    0xa051302010e060f1c0c1e02030414040207050604060504060b01020708031b1207080706050106142d0703080105040e0d0206040b06040902101e031e05090f010216120f 73
    0x85100100019580040942c4184c0c10060024640414490031903410b0030300a10380c08070781c580c1c104000812480350704a10f400740c0098480144101c6802100311004c3c0e44040381d0b0a02c0701100240410040e11403048000c00b00d10801c802c01c802d01c40b13a540f1085c0072354403c41e0306006000341c0400480c0c0c0d070080c81c0030350b50301070708104014203032404100c40e072400d451805010344004044400c071100f400d405c00081038840160002c2c41008001b035a1040c2800b601042c20b200d00a41040c882120b1503000340b0b940d92840c1d000440c8088507070b06e202e42c1c1d40705d0746200c1500c00c160345204918000340300c0b110038414940114140744428840500c049240020f1600642c000c101c5c0707030354035281d42540d070760040d26098101c2d64405d511409030325485021100034000740c035103d010451035000c0d941c00c810310344845401c0600d085002c1c2d0417400100c008121a078440e41c000310f141d440b2013200320b0030043e14961150241d07100040411515000041c1c2c031816038001c4440c0300201000140981c2e68074061085400021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 201987167 1250 201985917 201985937
    0xb01050a080d260906100b040609150e06031801050108010212060d1a0f07110f030d020d0f0e06010501020d02010507081b12011701110403051b0607050a0b0a05130201 73
    0xc0c1c0308940301c3c0c008a00c2c1900e0380f8400500140301d8083c00400740ca1074000c0c1e80220301080011010b50540c00c004003004941c043c43c1500c1c281008008511600840340d10600949140101c41e01c00c10f11140c0f06080103290a40d0303402c104281d2002c00e2250340040180d942440000610500c1c10b01c26a070050401d8444481c07150b64460404c011103800d44002ca900e54100b00340300041b1106020568071412203101b400d200c900388030802410988003010080042d0b80984900e854400b40481554140c4030281c070301581703079004030f41400003401311034010004162511700122543e05000403058101c801c281c080e9041d00400d074004909a6604880001c04914a2400316800c00d1032030034000134205030540d0440c1007114000451a2000c02a44200d81150307031500300601e064005c1c401c55214401039442c031032605183d0f983d465100c80e802000103c0184030303070605040707545a07001124000c03503008064802c02202e5152000761090145c43e11005c40386800d00242c7c0410060303240940b2141c05840d495024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 201988417 1250 201987167 201987193
    0x30109170f0d0203010b07021e0d24021c0e030703170c04050303070506040203071e0b090105160b04030e060301050d0f0219060903050606180c160b010801090b01050a08 74
    0x15511841260a0000c4100200782d85051148080c60107004400d0385e45544003540d004000417459007481d0080044000c0c1d40402580d41d0384d0b04001401680100d111010880d81c42015107800b4001801d01c159a00000c0d500c40b0111040c14803020f03149501e2010000e90642e440c003a0350368060410010049400d501d0800c10100600d8800e99018020608040c686078132038010a0468105034403c407515408101030100310b08d024807034103015041d0030341d000f40d42400117032000d40c2c403803441d100d040c000d0400065269a940d120710102c60581241d90340e0b145001e007080c43c220070161811030341a4006102c40c0c4000440b4038101040701d0407070b0002802c10303000001c0350312014080071100104030b07441000124500e07048a0101001002488581c030b8105899142d4100141000c10040c0b00b2449840c01e140d070301c1444111210f0039030300f184d15060ad09071520840c60b20302d4102c0b40581c801614080402e000040c102c030054114001d42e5100d1412000c032a60384100380001c0100074007502d0042d41000100c1d03090 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 201989667 1250 201988417 201988463
    0x303020706060302040207060911060f09040f0615080901050f070f03051e0903070b06031603120c051c020d0207060807030c0314070f08070e010f0507020607050601140a05030109 78
    0x3505015190025001d0340d02c1d03001404a07803007203100710f5500d9180c0710908103100358071070701c08442e030010303103d0500d00700d5810a0102d0b9031050b0416188100c4c1e60b081001e100c2c0516a1150b00540324407488001c0d01c600544024000b114200e0381c0c034000d0341c00c000005a01451200600f800381c5455100d9140d00c01e0008001d0b0060403004000c01c4c18421801141c3d8000065540c00600441080025640e00da400e070074040d0400c40000c01440c007130b60115002500900c116003c180480740c0000020400b443c1500d411200c00d40007110150292090f03207214903004c055604451240366450f021119041c03070341c040c2a62186035510612011071982c50000d2003650103500004150160303071400180d030141e406022220b280c000c0d9000305c00200240040f65195400442c890341100d56810200003060408000070100c50a0002100c01c016000c641d40307007152102c1c419101c1007580501500d00568542c4130042c4005102030034a403159007003a0000443e82018424404191b41180300401d032104515480300b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 201990917 1250 201989667 201989677
    0x9010b0d0212070302041401090311060f07060203070207050a15020604120e13051e04210e030102180a05190b1b0601092901050a0f05090307080f06090c010804030302 73
    0x400c19000c120b01e88505101904a0f44035260980700141c0780ca04000d00140b0202c4001c5184c1d041c40492881032021a14514410b0442142114182e079100b100e2080404a8060000e0040034140080240000150045601c9041ea0415a16420081d03504c2d41a02000803080c11404050b07080f200128011450045561050f40701f28100b20b042001d240c0003281c15020b04c20345503003c8603900e00c00d00003d520007803104074000c040c1503520380d940e09041d111305500700c0524841c6892055540003102d400c5004408605841d00010021900c620000000c140842c0c60001501d01c01c2d02825000b14036454592a4040b0709000851000100c6050415810456011a5446e03d1180c2800b81001118108005141c0641459035001c00c1101c9000e052000c02e2103079030000e41400e40c042e8607204559030b012003030341c0d0091214039002c40c0060000e4030544551094140f4103406008920000c500b00b800021880403a241c4541100c0150b590101c103a5180d40001010600241c411404500840e110b600600313 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 201992167 1250 201990917 201990937
    0x206120402120703060504060e01090c3803061011100504110301111309060303080f042102010c020c0301051501052b0605040c030501030b061203090411250209010b 72
    0x1154103022403001924080c0e1944c411078402da100e07010402009071501624101c50a01002403221010995500d4403c2041c1d000307501d02c41d0b9442203941c0f6038903206921240c620807035803150204540d500c02c40d0b6101d94000c65007a80110541e07901500b19910404280e01c1c140d00c1d00740540a4a21000d00d03da001c0c0802400a960a03144c101c4000a155420300c507003011a51032521266071482801c0509040003070030b500c22690300b8a440300410100c2e400c00319195002c800b40625148955031842c020009500307144091100361000342244d03586603015405443c514000313400b141c1442c84140c0805080e11000c40d000b40000c1000d080e08409540a6805402d113455034520088000014108020216004400c0e014945445200801107420315109000005400745028001981145c440403007111010780898019951280035448002c0180b0a072400510000c3c4240300212400002443c141c1100c0300d241c4004104541c03003c50b2004820f10745a0325a80546414096031030308141d0361607604004481 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 201993417 1250 201992167 201992179
    0x403050c011409060c011b08040b10051003020a110f060601031104050d062a0306061710060809030706020f0d11030108060103111216061416170f0a030902100c0206120402 75
    0x41c00410007140c01d13541c204c81f075680c2c1e00440b4581414144030140d806440100310801c808000d01042c3c5440079904000801400c0241e40d500341031004551040411b040681c1034014801450035280003c00c815000b040241d03403c1c00080c4914842c03e58600c184d110307803584002d441c0380e040700140c820740109456200c3c15012804649003841c006004600e04000f20300042d88e00c00c014030800d904a6405c040e0200d05088100c014a0010782d4083d0036000c0c0c1c02901d00b407200003800250390700c0c4200215070400750322400954072a0414480080260001d4495241c27032401c1c044860f03100500f8201b80c134100c8240400606559185442d495080c2007280d001540080800000782d034040820850a00700c0901c444940c0c942a250001c02807000074841002440030200f0014180003400c03440844006d6900100c0126440c0414104507001e03100f540c000345a07504010820709003072a055440900a54001e907032880c2c00c01d001300b0302185c00180402d00294441e509103c52160840d2400e4203a41c464400341034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 201994667 1250 201993417 201993431
    0x604050a080c131806110f04080102040e160207030b04030c0f21080601020a03050310240f0206010614090f0a170c0a030201090302131b03020403050c011409060c01 72
    0xc2020444903410030100e60340000905421414403168049150701559410021000700704000010105007010103000c0d60340360180494069081011940310142d1018207990b039a50b40c6030164085d41091040721200d01e034200c000344400c104c07850881070081441d40a00b0401c0c0c01c7d40d0f103880503003c010b0020344c200300c10051003100241d0040f181c04e46150180010100c143c000100303410201803200d020070200501c1ca401c0c0071059800107034017405580e01d818100d07180c3c1c1e501c01104184c140554082c111504003044200c880322540d91003003c038089581c0d1914010110784405030396544007032244600050481c0200240c2860190242240391001004404030700704100c005615400740b600010002d0080c3c003940d807415501085070b907040d811b064801c024003a20710780000e0b2082d0038510019025503809441c094550b003440d80110a030402a295800c4419800400100250454003040302d9922810300803140740e43c0500580c90440b200707072140524002d05001808940c1d00140d034084015034072500703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 201995917 1250 201994667 201994669
    0xe07170a1b050607240e070b0a02010f0f1e0908040e09010b04090c0501090807120f0f0c08151f15020a061103160f02030d020a0e10030e0c190e06060405 67
    0x3c002d2211900a1014440c403541d400780511041900002103200030b8a0300451280c215404501402140c0d180702c45180c8520700341d442640507240d40008a41c0780c80c6401d914140c01c2c02154400074400d07040038007507081e0521203022902103641152000d00390000a02042042d1551010502d5200c00408004100100350030007080c2583d9a01600311109111a08180710f103590188028005218200c01450207901d07003030343c00318509400030001c2d01910515034400c05008080d1261030109500c03400c00c4d50056036902c0c146803a4801c6012140c0c40c0107030f070400703e45550b4a055580310342e81030415250142d00d103009120f00202d0100e084c04802e40c0694050003001c54114401d06200d190310354940381e580d18242d421a07001121600040301807042442c40844d0840d4000300742c9880002c84900180e44059181003920844440703801903501080e0351500021055040c1c01031a101030901c1e0840340519500d00400c42801c01003c2103039a03043c40c1c44070400000c0c0c00101c08070740050380901101d1829032150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 201997167 1250 201995917 201995929
    0x2250b27010f1b2907030b0607020603190603020a0b0d0506090411090603100f060f0e010803070303090f060e15010e01051c0c0b070323070209060f0a0503060a0e07170a1b05 76
    0x3034284d980310074240804c0324841d003600074020a5201100c4440c034040c00b030750000d501c4d4007004d000052150012800360000114a0b03200d02c01450300105061041541e583e242c100ca5449020f086900504000c0400c2e02400d01610b401d000e9036008030b02030b01c4064000c081c801000c2000700010791520805881e00b021048602c90010881079605001c03600d28200303008104c00310110341c000000614948010000c061011040e10380c07481c0d041c680410310300d00c0f50400c41c0b41c11038441c401403c0240760002e40d014119000483c0488080700044845c0b450b82d81d00b04064480f0805d20440f03810203005022841211081d2080410301881480c1c19000541c46515444003504428000c401060040c91502c0d00d2000290130a400f000300065040e1800500c0c1c0d010408524018091300d00401c01356139510780b10f65030040f40b0070141c44043c0484609280c84420751011f4062198a035003180600d0002284010b008c42e4148140007040c8028070b00c007406999440220981030014000054107000040780c155120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 201998417 1250 201997167 201997223
    0x3051608190f060e0f0709050d0f06050c12160e27130b0a0b01050406110a051510060e06090f03070e0a0c0f0302030702250b27010f1b 59
    0x2031000140c3c071400c01d071072024204005000032910b994241d0420208692009152040d10301c15922400720884d030346017441401501030f030014603903400c110800001c841c0007006040f8030b07490481200c581d916007001000306444040705460000707040000f103c036242461a40d00b440400012650a050302c51031008a4405800340d0302c484e02c4645500a80303041c04040900c02c0e03001070310440308010300060640042c0c07145c4500d100300810300c00700b02c800708400f80c42401054220703a0810140c403261000c41c00e407102031010448220300c1740ba000400c08190184244618080018040c02c080c2c80c2c480b246040000c4000000d220540c503215002000c12240e204480035401480d0505020802100100380540848840f4031003400700340c81441080051031380003800450100708039000c142c0015010003040c40c0c003405a0030250450600040c100c6080c01c0070b840782048007111884060700b84260078011943c0d00202585a00050b41020800c815185851520b001c82407040a1b05200282c11108012180c022 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 201999667 1250 201998417 201998441
    0x3021302070201020114010e072f0604030207080a080714010209030d050a030b100c0f03030e0109050a110a030b0a2f0a0201060b1c0b03010e0708030a02010c0305160819 74
    0x4281e010465809018100030b5540303c001080c01c0b0b41c1008806c031081c902c0100707110100301004554000d8203614070301c50b8a480e084105401d40160b004030406076542c100703035011001842282d2002070307284804149031031010382c01507100c0e10341754007500c65008082046c080d080d2955420000900c090f42c0170488080841070680b2141d485041805c1c01030f00f01ca80020b4004d0140048480b00340c2803d9015012303000707490f07002141032422045810120000c16004c040c83e8015882d02914000b80400029071400c007610031301d03000c40c0244154041c42405075403031000a083c10020000704841c0341083d0803074240d0400c2d48541003250440b01811451040c0081c10011190400144400d0b90a50a01841d0f001e00302140b8050310b4480c0e02100302d00d064a0055881e031880b595250b1030f5810b42e500790820031607201100d049811164440c01d950740c499012040a5000d5031a0440c514202802030007080c1c4500f0700131044007510f030307005141940e54401c0180920420f20040c81000e000e01c84a209003040002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 202000917 1250 201999667 201999671
    0x1012020f10020d030b0d0f0803040f0b1f08010c080c070305090603040809120c09070c1106030f0f01210201050f1b010203010602150903030a1503051c0f0c0c05100504030213 76
    0x504500060300302e445c1aa40e40307018060340b09244022501d1000c1d04440503502003009980d0340c0d5103060130621142c585030b00801200c004424448080c42800700403840c0840a03641e13660700f0340d42d050b10340c0c22241040300300004941050300181c1d21403050000b40c20316500a003011460080301030006040340c1d004a50849841070701107003c1e01142407428041c156090040b0007002612003510004801d100000d12410130403110340d00b207008100701e982c01d200d21014007a00e22900c038282500e210a03505003c0f18100030314854880006480b00900c090440c5924085050740d41c0300b10146c00454140d07000c5154043c000308200290074112140121a45a68000c0400180c8a504208000b410400c081d446040d982c4d1a90082c480440740101c2143d030406000e600c00a541c440000d1090303140d040e154000782c4180554100c42c22509205001000410ba0a55a000b0843c01c0388506030340c210310501001d07050070a6040e0038021070810403048248404942401420182e0381d900080d40c00c1f0f281c0300b030201459 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 202002167 1250 202000917 202000933
    0x1141210021312150203180601141906090303050721020a03030b0604030c35030304050717030715110d060513020c06130305210702070902031012020f1002 68
    0x4848050b000c00501551100f5400d410010703110000444002e640c4d400034154000301007084420b00d012200e00203500e02e0141c50466a40d9440100c0400e04000c8c010f02400d500040306800d403c089001000707440290f1a1004c54a0540d04c04031000d401049044800e00220707004d24040060041300c54020703908541c0180091101071a005090b2581c000c8454002c00050100f80002980d41c042d16050310283c0004680210000540405401c4107648162003d40355080781070664501000451181e400b40080710b1045507a211880f101d200e20075442c2031260000d00410340000c1c00eaa0301c0401c0d0340c240700d0b804202075a540740c040c411039008120f400c1085030342d5030b01040142004c1a25010000e00d0040860030803404841c0c0030703140c42005000c40d81c0e0a0703c040c0d4500405005000f59552003400c10562a441007000070340c450031100070364001e400751266500008154450b070080780c0c441c25140001c001d02c949411212005034884001c100d030711a48848408050352112091071140d8405135000b01014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 202003417 1250 202002167 202002187
    0x6150f0c0c12050309120609120d02040e04031706060406081303020a15060e060402180603070203120f09100911041a18010e10081506060904060905011701140114121002 74
    0x1022110042203c6c3d50001c404205c0b2840001c1914103501032410181070b65000154141c00092103a1303002300c00c1071001d0340284014194000e008ca6112080d000000843d511b50351304000d00b1f0301407481220300041e1007200141c1100b00c0c203007440000c40c0c030038011079003040e80d25170b078045203000303000d2800c10f6550340c0341700070450240381c50040c43e0071403416141149004559100e0018882001d01c11900412001010035501c40c0708004441c201450b8003000310203410130003040f0070303081001e8401d003040e0701c6400d020030400c10941c41404011503111115104501201c020b2002a11030301000d070ba2280c0412600350050303110880202c00101c1030702c0700740145605111000258100113040c006c01451452414007084000240d665a00f60048014000944d41d04000500381e01c1041803007a0041d040140025500015030403850582d80d41401903180b00c010030301d4031800c0b41d54800c400130030454a0001040051621004040f0741d040143c03071190480101d510b80780c40c010800c4454804154001652034076 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 202004667 1250 202003417 202003429
    0x4150303050901020d093c1202011205060f10030b030609010207140616082203080105040f09020607060e010e060112120302120a0f021b060a06150f0c0c12050309 71
    0x14504a41059181d2600300b00707650499140421440580c8003c030307500860000d80b1600321010003d15030b90747c64107041d218001c08403081a460f200300d020416105450350102028041c040c8118406051441c2d0b01904500304001e603401c000120040c155503400403480b5490600c04a1302c500110800940d9900c19460600404c40a541d520b0025401010500c00c5260843c002611611414984854030b625400c25052a807000da04d8829184030300780421200b01500070311424102c2d801210104030386540000d450041d9644007200a40c40b600c00c01a010000d08641e11444200203150000158072325680410346c5005000c0c0c00c4441c002035141312550400417002440c1c060090345107001e5003010b0080c21031340c1c480e402c00b0705618002525548490313680d180d039078103540070301e0519415143c08070b4810300c0041d2031f07000170b03078070440700c14108100481c0315070007802c141c034141e40d440e59000d4455400040427121a041910704603810842600c00103000e41020306d03214a882d0181c00915642c201090400c08 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 202005917 1250 202004667 202004683
    0x40204170609060106050a05031f03060906060f1a0711090c04140312030a0504050a171201050607050706051e070305030603060f0603060114220e19020306150415030305090102 77
    0x9441e0f440318005102456001c000d69900c450142019070701da468011a40c0e200600780504031128405540b000418005540c20400185000310020807043d40c4441000440725182c2c06615034444d10300d4010804018914014008140542104c8003007140c3c810015003108815100708003002400308060200070300440114601c50012030050000c0001762481d00c1c503e000003000b21403001d6032200050280501840082c0c1e00300d501202606098005119038030554001340701d1a621000b500b000462241044002c44002a81113001841c6d681d182110443c0c00e030780668030070100141d001c1d29420b6000c0421000e031007103501c06d880c0c3c0380e200e03d4018207040c038294005141442030030020b02131003041c0d00d021132500c0c1550680340141c2c0464140c80c0116420381d0100d044201420700c0040b24a000e07406503031040002c0e0f00020242c510380b201805082c4014550601c019506421100100c0c194603824012000e50405c080d2010a112180c804401c515850680c0306030046007000400c02400d69041c0f146003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 202007167 1250 202005917 202005931
    0x3030906090e22050d03021902030c031209030403050d1d0405160503060621010303110604050d03090204060519060801091a0d03030b090403051e0c0d14090402041706 73
    0x315031580b4042c954040030a024184a84040141004041c4005020319280303045421000315013002d6404030005009502440b040506a03091048680c82d0318400700807100c000078500002c60402d48031144200c0000c901a1504e50507110801c00000010f030140040b5504560f035864a1910501514855a00203081c803c010721072480c1c04100b259003c4e00d282489041c2d8424601691640d40e9200841c40da44181e210f00c085018070342d4441c1030064400448503046e24425901d09034032034240b0071029542c41702901c00070425001807880c840340c01c0c1f01e41e00c00c07030705140001d02c08104c1d075980c2c001040555800c0b0080003401c2c0e00602d0140113064120510703e0040039084800c00050b610034074584154020304002e01e220b11495440341040c948079030890902030000030511072407402c0a241c0030741560312001c50400c0b212924181208401040c5083d10a40c101c5503020b02100c06004504441d1854030030880401c165040c0500c031000d443e44e1010b80b01034035090108070728131410f4010061800100800030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 202008417 1250 202007167 202007177
    0x60718050627010203130f09060b09030a0b19020a03050f150102070e06040e070f0612060f17070e090d0201060b030610140c030d05040209061e130e01110403030906 72
    0x60850300480101d64040b05440c0c081c00e48500c08040100d040d03202e04413000d40c2c6084110380c0811003103c010030400440d909100b04015041d5144005200c6000d10307075629605420035040c1c800030175015200719230b00c5a01030060407424618001c0703d43c200e03000031242c00700282d030313031820858502c00c4441d07190b81101201d8240641900c00c040001d544111300d02995200d403560384080342c095144c03500044070044000054590254031030b42c80f000c000c4014400c480c0020f000503000004c5070000d2144005823415030461413046828024003400c5011010782541d0148a15000059403e0f0a500914043e1000402802c001400200028295400e030741010481e40020001d110381c941d00c58000007031420740d40c14030750801c00d06400340da5501c4c00b070300001c45c0b068080050b02c40c0685003103901440c1300d544215451006501d41d5020320000607811042c80d030b042c1001d18241c0b85680317021882a804442c0c11400403c0700f0750780b0b20301507080d200c0162400c0c1ca01000820141b04142e0403c0301500034007500d19003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 202009667 1250 202008417 202008427
    0xd140102030f0f180d0f0509030304090902130b0a0501050a111608071e060e0a0305010c020601170a02010206010905090c0a0e01061e02100f0204081501031e082a0607180506 76
    0x42617480700302e08810f08050140508030005403500950981e484200c0c010103407522981c0c0d0703000b124040e10280108a1103500c803400410b94036a03a034410712605010180c02c28041500b0203006640d2a031058500b9824816201d0f44000404010400c44120f490080108485c0038500f00c0860302d40710603500031715072003130521a20002420036008400101d884510b001c0f00d18414000100744840720681025207207509108041040c141c001881030b0485818041e0704003400750300a1219150110344e4002030060708108010001c0b000c00350041e0b900966030b101035443c18600440099100d002650090500040e6480100f20311a0060a0000c260013220120090969006030081d240d030a0307014501c002d16900d41402c00300341d10503410380d03000d880110103c80182104080030100304d482403008540314106c44441c08407442c0d00c598030800d4650b101d44601d00701903040701c1c2840540790004928030448620003010f00303014820000c4600403092074903800740c20b58803078109201425054201038050401004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 202010917 1250 202009667 202009711
    0xf060504060909050a0f0f08040803040e0a020412111302120105121912031514040608070b04060507060e060f100602120403060e011e060e10140d140102030f0f 70
    0xd1329210660b0140d903801c400b51aa01d00307e08044040c10000c0c0201038049008640e90000000a00654044009c0c079002541d85c0748002c07060b84500e000e00d461848010801000080c00c11042c000120300c028080c4208000c1c40700503d080360000aa001c1c2e129070a034004008078200303c1e020154800c044405001c1c0301c0c410342c0d40c0c100c0603001240020700d0003803412030800c1039620960060745007040ca034003070a042d40d543d01c040031034100d11031040d644034602e00350002492030000a10102200e6028000b903040918050b01a41c084d00715060983c0d000d9103454013203c06601c140001846030703003418400840d46c1880c0e403040c01036040d02e40002065500003006040c4040011040c2e50450380d00243c04500e0304000c210160150000000e903448100e006c00d4450381c1da01c01d640115086d500050501c103411b90b0780300c0120003510000d00c01e4200784112540319000030f041010b0040480c50103018803000750171070f80881c1d900b280d004841d9200c3d031030b1710032060106003030a0b0140d0642151070010200c40c203620800c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 202012167 1250 202010917 202010923
    0x6150e0a090b0609060a1106100510030c0f0c0303060905090106170a0503030c0703030f11031614090d0309030c060e120c090601050d0e030310030302010c0206150913060f06050406090905 82
    0xb4130600c1800e0206444450741c0c800c0e40b2002c180d015040981740203080c2001281d5910001c0d004091041c1c03041d290000066100b4071440404400c1656407408034240b40a06417010050180b080d401c1541380c07240481e032441a80511809050303107900000d0200d1616050142d0250040c103411581c0d04140012000f00d2000010b580e0400442600c142c0d82c3c003624901175008010740d80302c1040c0c136414080d00c80004501d200185204085580b42c401c014055200211011400101780420202d800e01c00f400c0d4604003201940d045a1003400c0c1014030710f480b80c4411604805035440000055081090002281400b01100c0071000c84d14000349443c4003880c0002e8004500100702c1410410b01107200b0103c100e464001e045801d407008140c0380c3c0d81c00c2040d225500005140030a5000d0340c00c00460000c204e2000031510300c01c03003010010b4108020700104200c88188041e103039460008a003c2c0b0400840e03064426910400724803080010468034140500c015108a03070320142400c2d1524504c1000300d6404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 202013417 1250 202012167 202012177
    0x10e0907061d010815030609010609110a08010b0a0302070b01080c011404230406120506250c0f0c051c140d0504120203070e0405030a0311070c030809030106150e0a090b06 75
    0xd00b0300922179a00c02c2c0c40414001000384c1d1042d170612415042c480560f1040d4040f00079180e43c0802401800c500b0403001c18030748624104807000840d00401000340f00070f80d402400b40f0010070318000d8900380c440d4803001100c6100307070403401d0150030040d25030307040e9070b000604030300c46d40304002516003400c0c074000032403400440400300b580468860010961807581c81c0d50104c0040c007807000f20310002a6480c00e00c2ca540d90421038014800800d404500c000d0540343e40e82ca48810044c2d5501e40c8011581c0381d80d10709030002005021500c080300b000340032401d40d42d155080130020a01c28015414460b5078141401d42400030101c441c0d00d0b400040884440031341c44422181550b040c4651001e4202e46840420314040c620b90111070fa01c60b1040030b02c400c010f008001015100c54580d0140400011348210722003601c20120018164105842e00300b0000c1c0c0400043e1a030f60308024000103003165541906011203c91820000c00600410304041151400b256001d01030100300d082044403805d0303c0301081c240d10032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 202014667 1250 202013417 202013419
    0x6070f0f12170c0904090c05061603121406010f090504050f041203111812030a0504080d051c0c020c031c020d080108030f071712040303110c060f0705070b010e0907061d 74
    0x720882882072000942c45079000348405029603580768845007202c03814072b18030801140001c0c4044010107600286000d0b414680c685814140790b0360316054019100300c0c0385c110030482032080e410800603995440b0312806110301e0150482e003400340307841c0c41c218680a41000f40d01d0306052520341021440300301401079602020703140c41815500039005000078002c2006000d030f40c45d0791100080b100c8040764401c0c00791048a0f45c2c1001c8401e94000c1e08010f8655003d080f19088941c004901101c070201002d4101c9506060b40340159040115410f010a0500594186156440c2118508060313019810002030901035040d1421a60340c0d41440007194603486240c1c2107040c151408100c0c14140003000000b0340003152100591a0760b040030b079041120801c0126001d0700468541400740b004441c0e0441200d0702c1104440203403156594100d01004000c1000e0309020400000740240000115140c0d2094064030001c40c0403c076600c0d181c040e0b01d281800c0d0f0782000d404c000c1044145106024154415051060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 202015917 1250 202014667 202014671
    0x60105010e010306030803010b0c0f0d020607031107050a060e0d030606090b180d1202060a06030b24060c0f12070203150a09020a0e06040c05090f06070f0f12170c0904 73
    0x41c082004a0280000d41c002038808100000001424854170000f4068200400c05131001c805c512410316880b20020340d01503000d46c0104002902c0704d0300c40d03031102c244d07250b0f852160ba0801145889483c68070304429011a41304da59001c0d800507012040103909032200d014030303040c0201414888000d00c1a084d521410944480100d0050741c01240300000450800014204426480d1142003420700c80d0326000807100540105c00114844210303a0003620145c070b0b0401d02c260401e4075604c0083e28410f109402d484034071201c55000c1c0381640c0d00c25000b840382802010052049040550016040011600d610950b00300304000450068401088070586142194620149039480c01e801d07001908800c54029480540300102003000c3c001201594020380003580d0410a21041d541d00780c0700d500c0f41d0424036610950300e48400b4510f1030106c0003000868440c00a0049200840c1e450320205003501c50203d0300742960040e50508103a00040784940c0c5e4003005e0f00081542401c2c00e628041e40324410307890f40126 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 202017167 1250 202015917 202015937
    0x906030606040306090309030c06030204050f2206090b09100e04030c050f07060c05100902150903030f0705030a080f220201050909070906110a020a050415030b010902070210020a0506010501 83
    0x6600d040542d002150030220600071403001c0c2c5402040d90105020442c0c0a4031b0010020880b9846803090300d050725005802d56045400080030081c101d19610300c03666202050040d8850812624049c0b03100030090000b006c1001c06a81d803c00084447c01007001c0c42c020144901000310321071703007a800d64003d03400d801d081e0b41810060030818140329070030108606500c2003407000075a0550148160415a0007801130307441200d410040c10058030000c4074040d43c400500c030180342030320400100804101c40d004044a03c2c1c000011061030311500311103000e81e01e503000810000c00890b045000301b80d100b0b00c0010280d0803403410000c1446500c042c00c518049240c883c01034401103900410071101c03219002400c00449150003c00100400817a000c2e2500040d940a5001c440f00c200140c08280c16038003c0007a80b0560030642404000d1505000a0154440c045400004a04c801480c24003030000c41d0b80250b41c40b0380c00d0049c810010886480b00045500240d15000410340204415056a00910709902e0300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 202018417 1250 202017167 202017169
    0xf090206032809030e040c020f1f270c0e0403090b0a0306030602030907090e07080303340206040b010e0108030304060f0b040228030e030412061b080601120203070509060306 76
    0xc8140b41030403070149014000000c3c181c0110140c8210f1300125000c0c0851403e000040b600c81100a108406603400000d5010307a1080405420300c5600200d40001104030090320744021821107821009000e074034402c2c0f83c40c00d00c084400c0d03001c0078200c3c0c0039088443e4186070360010b20080ba01e1084204107603010402c8018a8880d80001d00110303000002551241460000750b43c80300070300c2c460000c0851404274100c80d040300100d85881100d01d08809581155500c100010007413001031901c082c2c4000344403074560724107608a4207409034100b0754000d00c80b03881c21749002194000180c20420b00041518010070409400000b281d40c405c0d802040800c98008a00000c4068401540d003140e2050012585612880320303250544401c1040c0f080507400035441301d10aa003241d00c0ca490420304c54008010500450072000440c02d0424403800b00040c82030038a004410104000f9281c80c8000707000340041c0320a942c0c2c880c213030312916440303d8411441c50030580c0d0050224400d64014900901010000401c0303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 202019667 1250 202018417 202018471
    0x90d05030c071109012607060e120f0303090313060315030206070f170903100504211101050712050702121c060f030303050912130b0f13060302030106030f09020603 72
    0x10f030005000c030b01940d40c4810508a42d05807020152a00d5269080d1585c030803600002c414045501c60f49403c040781080c4010b000c81c030805071070300c0c29070f0344110110415000801c00040d840361031440d0255407220440c99071280141c60321352005c0f007010b00b801d0000d0f40d01c03c0ea64104108680c1c4c101da00a544007120320b0a1112002d2404020341841d0089032406a0b801d00b5100900c0301e10022016242e20031b00c40205001251410745000c0c0510600c07244103d041d01418070701135100185407c01101c01c04050a0b19030a4030350895000c400904d800c0309020042810340a1a50008202d001400c5004820000c0510b6801a04000140c0e10022907100754035540a0f80403401400500c01c0e0380105644a09014000c2c03c001c0c0c940031000c2c810034821100050805055030030070320340d514910200a1078030141c4e10680e040070075580c1d52000d0800501c580760a60704902e200421442e100942c60b50b2500e40702804540310b8010342002181048003090040c2d4407101103a0784480f00381c480100301141c000c0d149a03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 202020917 1250 202019667 202019693
    0xc0307021c030605030709052e030602030a02280c08030c09060c03040602061f030609030314091e030a0e04090c031b030219060e09090c0a030f02030105090d05030c07 73
    0x903114007103000c4103050360316400140c26280240e080f241180d0f61750f00d10700129142161460101101d0030781a014401b00c07030780d080e01c20240c40c0c10b9141d05591241c986804036401503401460003540051580c103001d14032004192594903c0e011222000d00a050150080002150040c03d5040010004500c00800f205481041c41d003e41003603150710340310f4a080d903290b0081c01218003600c5400001440501c908240001080c04000c030380d4030003490755a9030009841c0d104002c40600d40c8030f8a1800700b5000c28003c1d948030b036180b00010038081442400c4d500802490384400009a041040910070107078100070500c49002c03043c0c0d00041c582c00503041032050703501550001400c880c80d00301e610b1000910a0960710589000f02c0300100c82c552160044900f541f21440340d940800c0c280380110b180c07031801d00c041503400401d050994085002d81d90004504d581541c00813900080c03c640742c0004c2d424240310303a5500c400302c9401001c0d003412344007015140d400000c11032a04200c0025201c400c100000500203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 202022167 1250 202020917 202020943
    0x3060602060f180a0302010f0b0a05031005090102040302061204031202030c1608090627030c0a030305090a0305070f03200307180f0c03050103061802060307050d060b0a180602060c030c030702 84
    0x2904c2241c0d02e250082c06400c12100740d480d01ca040480404003803070010184001c6840c010001c10301f161100100c0e40141c180280383c1000ca5509100000c0581c07603240090007100604510030070780b0705d8603140180c100c4d1406116000158410f008201c414001001118012a024842c001c1c0501c214074000c0d91900c9060340c1d95030010301c0440c100440710a40181d03913142280e20300f0b81c10403504407e014140e485000c180f0703644e8822034540e000c10109005000902c401d07803000c0c01d80a281a01e030740340c031850310070141d201c41602c1d881241e0401c20301503000e80c0d450307070001d403c40c200c0f001d103540c000000d907260494094100c0819410f10307201000301c1650700c61081444441d409101100740c1da2809001000240f00070b440c40c5051205a94030070f22010542c250340c039030041c816406e50b11488030441e45500701c0c50302e03003048a50311200272414a8485016126007074940d0b13182d42d42d0106011403d844030f030240e0f110405541c0018140444082c802040d84c0d40840380c10f030299120364030303103c04174644001140740e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 202023417 1250 202022167 202022173
    0x30403140601051c020102030406030b0303130609081006052110230a0c2109080706021e04080c0411071a0709080f0322030206030a140703060602060f18 67
    0x8980805010880c42e040314022541880c28a40d81d944007003900c0344002c0c009005800c104800d01200f4081d44c040c22a4060241c110380c2031120f448400d002080342504001c0108401c990104030403042081803440704440c00b1002e0240c00c2c5481e002c80c990400161032400a207140024502c202c000c10440903190301e40002081c041c1d0700c00150500b00b840500c0d117518003030417005000120f0030319190040402200482d62801c0c28080c006072009080c031504052010b85986410080020412072400740500e507014540040c0c0e201c8007206403907480c480c501a0002d4101c800c1c841004032100200300711a46103002e480210b036484406054480e540315024001f4103140c080000440074000351003503944952a20340715291190b44070a01c8580da0324a811032035406a00412a07000d186041d034000c02000c000d840c0210f40140d07161750009a03181c004890492780d095640144c03580d0882c107011195000711050604020302410154001d4482c840101091050f00304240400c20300e0105800101c0a00351503026 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 202024667 1250 202023417 202023443
    0xc0703140a0b0109020a1416030305072c040b0d0210050703032a14032208040905010b03091207110409230109020406140603060111101d010c03061a0903030403 70
    0x4e144000d4000403250300029184020500003540d0740d8044901d080132034004008210440e58049001c1d0100401c05420410346e00700c100c06004895500082c060401c0d09080100041203090108a501100380b041c804c0d00b61003c2500940c41e00c100302914541c0313a280c10b81d45c50303a42c0d040a6015024064426240d2070008082501d691113811444000d5051a03690700026031002c500311400b8042038a27200c0c9100b0350319030382031000300078560100307043d0307205581c3d07142802c0c2d94150942c201e0f070007640f185405800020412452800c24021044080700c00503c403420250b85071200b94004a003141414001c076074400080c0184059a940a5094182002200700c0c480c44490518060603882070100d00032400c0800c086200c10301302d102c6100080c000751043d400c41e900c0c0001156070700c11165180300b1900a5001100f49006030340180d482c0381c018200ca0505102c002144242102c2200803810101480d04800740300c104107a0781c0304100003040042603a1503542d030000080c158489ea81c0018140700b00c21003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 202025917 1250 202024667 202024679
    0x603050304120201030c090305030d0b0f040509072420210a030e0303011409061305090706090e070206010510110712050708060702030904090c031203060e0c0c0703140a0b01 76
    0x2000b00c841074804c0e6014807040590001c1a203c2408600000b84160030030300c9130f204d03202202c0d0700812618000900458449445078003040403104241c48603410760b00048010b0007014a41003038180125001701410705c1054034064024040d48103014004901c1c4c1224540c14074050b010402c82558410401f840b0ba206c0c060300802c00c4159100c1480d0034007107030500c0700000400358044252412034008480c0c2071410f052180810800d00d600030006035000a00030a500001c03585071040b60700c50001100100302a030700b07000000d040d2104540c042152034480c0003c001915501140003411260103660000d00c480864409889615020606000324461100300282d400090f1440c143c510703000d042618044d680350500b40d91510002c442003400359004102c40045420560300107030a160160780581c50090f1039584500c0d03151011302c008800207440d03c0051050030910f4401e1500102038101041c64506000c402c15180c2d2481d1201401d01c0106002c4030b60031110510494044551040c0c0752549503845803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 202027167 1250 202025917 202025939
    0x70f031e0218010f02011a040507052701031a01020a0f081b0703110301060b3903030f09010c1710090204120c0911122a04170a03050f0307030603050304 67
    0x140b15400034401480c01440c1c640184203407200c0041500420409a60800900000c0c15010301620100142003110f2810b178041c0d0488440f010800743c90221903100b140d40010203440c10800c0a00194002d4100e105e50b50f07800003505002d540d0b000080c2c0c2d000d00409c0c20240d0031070040381c0110191308540c014076410220f020038248181c80c8518180c080c4248881c0a140c02c0755024003500c010a441044410307000044050200d5003000808408201d00c41c4980400040c9504103100550b55032012080c00940075100c141e460380404842d008005220708010020204002c0c004000821b240c0b80c008507502c6841e0106481c00340c0000c100541d0750f136556502d0101421841ca0b000d445103070200502086c254107038010240c0406045101500307040c110459503840060203440b0888107003c1000d0003030407041e04013031100e40c407800713000036600c0b24030308401c000b110303000003140803034a400944040d070004e82c03c4410b640440c248036030b14903280d9949042c15070050032540c2000c3d00030701c03010900046940d011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 202028417 1250 202027167 202027207
    0x103060509011401271d090606130b0301020703201f0f090507120c06020f0304050105090d020a090b03010e030405030d080414060103050604030905060a0e0103020d2a090806070f031e02 81
    0x402c1900d01e0481606c440c4030100b03030a4560505c203410000c04a021071070007520304200707112004000910b0816a0300003a003240d01000c1d0441c049000b007038880800001c0740b07080480324102800035061210420915060141c0c01d540c2926a41c2c3e55081c061000e40410391003421314a600c0001c40d5012074445880d0381501c14004022500303582c0d170303a6001c44c5c1e861000c24020011568180110704060602c40199000c0c0c020442d0f00b5086152202180c016a861410400080c01d0303002e1b000507610303006e030249425100c14805490040d4000c00040045440000c0c507480b41d01003034585006980c94518201455031041c01038000c2c40d105107030021040c01404a030a03800f1ba031182e100c030311400e641c80d001d0203854041d10300c880c07010900c1422008019402074000b003219100c041000607154114055001d01d500725600c00c446000e211207900d00c030407504045241c0141440300028126481c050200828a4032a10f100d002010389a00c04800e1010142c1c40c46400b80c0c020070b070b0554882e00e41c890346907001090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 202029667 1250 202028417 202028429
    0x140405010f1d060115121803030b03010e030708070f1a06010912050c13020f07051b090606180109030f060b0f0105090a030305090310020f03090c010306050901140127 73
    0x18050700c1030107010b14004480039030759861002e0b103460382c6482c030b542880a41c4040401d062201020091402c2c01d60341c8644031000c6000b00072610304c00c0480c1030003001c4410740c112540c0643c0c580740c01900c80700c000005544202d6030000202c3e42d648280d250180640310b4024009006401070003031b22504064400744a40719001c281d84040600c0e64440c00705114880c80c030744c082c01a070051942d85a6500b0100e88030b181718100000c000d07113007908010305041da90303005240581d890382207550303400862500110f0200d82d00004660140c15800c00800040052140c81d40074500301c0b820144156090f40241c94043c011500450080d00c04615414054058180d4421880c030403190703410040010b6028106659000c1000703828510120300b9954251150380c0184002d81c5e040c818008900c5400c1840e0005040d41c186500c0c44d80c1c2c9a080190b0079924040c1c3c1d40f0691414103041c0340040c001c94945000c924111b41650307142002041c2401d0041e00c400c90b040340c500c1804c0c40403828070400c0003111000c40c01240d030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 202030917 1250 202029667 202029671
    0x250f050a031d040b0d0b0a0603170d15150f0905090708010918080f07020409020a0801090320120906070b041b080109050c120f070602070e060d03080118140405010f 72
    0x54000c0108982d0382c10f4145501170904c01000c0c001c101c1c08070b0342035031016045a00190040c0c0701c0d19884408651000000c060a500148070754030712841e0f001303c81940d4816034000e02e400703040c017450590041031030041c0070810a8107007030302100d40e10514400000380b102600c409118140008000c1c503001c0c00f4024003580d40d0a10052484000a0b9805800e145401c88942c900307103014411440c01d075a001d800d040c2c0e40076032504480c002581d1039640d650022310a140000400060515000c2c0414140c18420b1840d01140c40350400d4500300862407032040340c0c0c1035001556030002200010040e025503034001d042032030000c041004021b503200f0320038110203600e5200c1d0300c200d696285181c262040c4070f034014429085000b50041070700700405002103410000c015102c80304128282d081c64405103902000041c0c0c001801048012102580290803040503111ba808450aa80b00580915418862081c150380314001c105405a0302c0e40c0f103003401820034100c00805080074100329000c2d0040e200803e08040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 202032167 1250 202030917 202030967
    0x7080d0c020318011704110411030a0e150405150408270306061035070e01030605012606010201021905070b0106030b0d06020309030d061706010605250f050a03 70
    0x2d80229031000c0140b00304005884940da1b1995410b40d803403581d00300690499124619031516141c10170146100d1301c4240000910307134500d8007805241050214003103807910b840f01e0a010200e0070106e1100c0604403d88020107144d04c0310f01c4c01e40b04511030034900c925040c44547d15808006400d02403d0348442c401ca003280d00a880315000c0000a000c401030050119407020704140510075140120501001d8060048900c0303002100f08007540a004c41790f02000610b00d04011440c7e680610071800034010a103804071807650035186a14050850600780d880006900c400070310603a100350103c1e60714102d034000b04040e0b01440349006c1c2c4150030629048906003070349000821070512920400c6920940200180a10204e9444a00003513002030801883d0f40410091489021494000c070001032400c00945042d6840d130f00e20f0142403103810380281c02005010804030301a10001c0030111100e05541600c07009130a42458a0395070b070800104014100e0103402010024550004010302c1b03510754000c440080c00d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 202033417 1250 202032167 202032169
    0x303050c1c0c060e0a1a01090f09080307051e0a0c11030607020316060b1503070224060111190b0906010f0602102c0d030e0a020a05010507080d0c020318 67
    0x2101111010340000c1c05840c0d48004203c040c0c2190b0440b00b107610699449000b583c4801d10040441000200c8107003c03100104440100d03441140d007180c9481c03400b003090a00f281d845000038400500860308115021410b1075103000c90305401207407040d01d924060351b41d24032900060050029561f00307a800310101400b003a5541408180a0721402c01d5601451404003a40784581a010300c28100b929000d60301c000c1002e40c0e46441d461043c01d10b0f0081035461312841d00d188000e02d80642903000c0d039445408560b01e440c80d95200501c50b60000300908001c1c40c480e2451200340d1038120309100c49651aa8407040c0c1005003e000140c40707000d0500c4000b52000c0c2c0ea01c070041e0010104091152400503401906070700d034200d1a0360b001c8603c40405105210b02c481c0d1000f18116200ca09141701082c2d07400c045103640040740c0501c00d0849400520015003407101e05c50f0001040c0c084644256418000700040800804c041e4104a403003422640c0800c0001c0520807500956941050301b07444500d1003a003c42ca209 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 202034667 1250 202033417 202033453
    0x11010c08040b0c1e2205030a02010806060309010b130204030605060a06080c0a0e04091128090b06090a061707030e1011130b07111c080310050405010303050c 69
    0x1ca10303003021070a801901c0741181000168008201c2103088180b0140c56240342164400030002400c40c80c01142c0040080607082900354184e9214901c00e03404400d0400050f604145996030007041124481d0300ca56500d11b0307035400340451404482c1e01544284012080d00110340c060415203020350410002607459100b0b110b203c103814010100401c1c280c038001550400e00400a121039415440c1442096040d10045003d94483c40c408656000d825040080c1600344801c0c5250020341050a28900542c020007a12008015001d141c01d403d80303d00000781c0c0343c3c9420341113030700c1900c001d401001d10640d5080700402c000c181e00c0c4c501c1399402d03503c404078482c64402e000704607000080d64003404200c081c444200c0020503141d5102d103d011410700c08240c0b03003160003045030000d001145200da6103000b80c0c80d14000074109641454400e4405100c000350151410032034440241d0b020010582d06d8850200c40c000c420b07855482180d2050811002104056010000d840300500c4c113001c0703601d602c0380c0080b0101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 202035917 1250 202034667 202034671
    0x51302010203030c090103090c08030c010b010201020406050d050901021204050607030609270201090b03013309261006050108091b130f020d020910020c03030412050c1011010c08 78
    0x30050784140045100b08800c8001000580014100040c444c081d55803400580074031a030111402c0d800c00f01c1c10390040c14080c010549485800d10007140b4003030074408068000d02074007010780b0220360b0f074030b00180e54004254105c03041d211100300040840e00d81481d00ca1350700d00d0121400301c0040e0620130001794039040c80c003548052880d0301d000b000300382d12050001480d40c500d039007050b4100048648002440c1c00c003480254082c1440041e00f081c403c6a00e080d04c412200b56941c12004001c90400c2061110360001d480d0050b41e0b0040300c2220713503045110340000010303000380818a0500030301c101101505281d81c000422150f0a032120703441555201c64058450280c200000c51454611b03c2c48000c502e807142c01e54400c445c0343c107400104003159041100881e081441c1904080b03500145004841c684400421130440030b80c802805041080004652603018a215500c146505540074104110040c8075020b000345000d00404c01e0398000c14402071641e501e000001c4030300d518001c0c0400350180f14410141c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 202037167 1250 202035917 202035919
    0x20a12090c0315180f0213050c030604110c03120718060504060306060e03070501050c0a150506010908030408070b1806030f061903080906070809100206013f060605040603080409051302 81
    0x8061303042e43c84000c1c1a011201040384c2c444074180c92101d0394205c0c1d20035a406134414600e801d480b4a0a10f0a10048401601100000c0c0e030040c400e40c21701900020880c0d45e80038480c140c0c030280d6240e14405540b520303005c0c001c06001540103000170038180e620801074002c840d583d41d07062102e5580c07268162150031011140d1605500320180c00d2086500840c014060310044a0855450041c1030b00c6451001c02101310882e021621032050248541c0d00017a090054280c65002c2e515040c1303080340c540d0762201c071480351300e11780c2d003000c11600044513507105040783c40e100191495a43c0d2600100c51041c81c031045075002d11035103a02d40017070441c0101c411060256940020f5403464150100c0030403209421035141114405801c010072541c1c2c1e03d4100303101a58410540044c229541003000680940b0345c00b01812180a000100700c10700c052486802401125013000c0740781c042060342c02c10001829064021640003418808004204405000100112502440200401e4460301d804000d00d6252180207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 202038417 1250 202037167 202037201
    0x409091a0c0702221410050105160b090c040203040308060a150903080f090a0810050921031e090a0615030305040303050c03070c03081b0f0303010603020a12090c0315 73
    0xc0070044c2444c2c1016400f052845035503060b10350382040450190350110040d080002d8080c2e082c80340d40c4103c0303810007028000c00d09143d410b103600001c0c1c00c80d44000d91030014010b454031388003003461004240a180c0c888480508217640c2d03440c2900707018208003c1038481c07500540401c0c0c0b0002e02420307625407060402ca0341d0341d1116031241c610303203414403107070021301c001d000b450b00802030111581e030744214100040142c070000c0c00c14004400c5100c822240010801e016541120030390007030700d04030302e035490716204448400035840340c8806804100048020074a00443d2117035205000080c00000f40d900301051040d0720903c0742d04500039000d00180714910004010400074441440064054070207864981e581740c045904080954943d8080400d040e4410380c1d940c0030001e1410049070400300d0008083c40180010310100a00c0f00c14196a44414894001016800304d40c0b110264407419504d4910740110f0000e01031000e19003410f00c801c3d4464481150091030720300308a0410b8040c2e0040c4610205101c0314 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 202039667 1250 202038417 202038427
    0x8031201210819181d011a040504180c081608010e0c010c05030f0a03230f0105040b01030b150a092718080d0b120102160f0201140409091a0c 62
    0x18212401a00c10070f84400e0240e14101c503090540b546a640008102c3c40d0400d1083c1e400c8400e40f1906040183c11000d041c03100f00404003911000c8800b25000c4841c1070340c0001303030300541410052808409210003845c0710700303036030780000d50403070014050400b910200e0031a943c46030354652460886186103d0007041d500850a54021580111400713240640240c2c01d6030314081c0c80b031682202550191042d040032968510b8203040ca00d1034159080c0140e985011959050305001341e802c200824148a070078425501c070942d1540f280d02c030b038200b41ca03003220103410700861072481c90480d002a0880a100c10002e41c040a00041100d036030051003ca8160101c24842d51400f0a601300380035000301e503440c94405030300860001c0041d603c900142000640d20200081e0002c46404100e01a550042c241016a0040c02075038401c100110044440590040d02e10010342028070050b2181000455800303071903c4e010400140e4004190400210644581040c6555107107411008040200c00d50301c0c0342032060b05000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 202040917 1250 202039667 202039687
    0x50705070e100807060801080d030605011d0402090d1a060f0a06180e0f06040e010507141c05040305070b060418020d110406060207050a080604021f09080312012108 72
    0x711450700400308141410b25543c885809501e00361566201d1000a0480001003150305c00030301031019541c400b46000c0c0403017850800000d2016a003100c403655880000440c0614551712941103503200e5038040d014114648440c20136440d160340c15010310100c22074900000301030b860511001d1101103401030401c00d130a81043c104440d0003c1614403031949448480020410820802801d81f18002070446007640785088414042996035040c86824240e0502051151451700442c26420906032a030105440782c660b403041060030001d4550f581209807030131042c0000e08d903103c0300510025020385118401074032244113005c120b40e00e080c01d02207074144508400d80140760408070880400d00808200004081100000e4101c1e003032940708001603800321a04009509082c0e6100e00100703081806042c0b14605500402c0b41ca94400103015400c03401220080c021381d015000f810080c0660a0489e921018094400300c1d040ca400e0140c85940a600004a01c4c000091540401034a500007503050130642448 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 202042167 1250 202040917 202040939
    0x5010201060e0c1e090d202d0a120b041e0201080105101101050c030a0e070f06030903050409020f032520071706071701120b0a090812040203010c05070507 68
    0x3044111044e10100181152a6589401100c11a01400b015039440e80d064040c0640d01d140c19075400d0003075a00b85120407004e24002c4101246041120311260f46505110004800e00745507008427030003c0f00101e00505202e06400c000703124038030278824585180c03821104000c055403030324402800184008010302480c1040c419072002d071100c90410104503280d10f04400d0070346504652458600c44040100700392050f0b50301a040310a0040c0d00540740c42414003c1c3d84000004c140924000d05403600140d804244c17155048400420a0074402c5446806040090a00e03030300544002c10200303607030160b40c2d0903048140c4810f620010a03440d401d00c08140c45440201d241941d0b0086403290051807000a06407029112505d02404020003030520703468400307800fa202c130340300d10320721986400a6401841035a4a0340101d50b003507900a40e10803c0c0303a0300c5d0044840900b400d07400003010b20001069242c410783c030510501d8082d80c0b08400070301000003040000ca8040c0501000580740341c1c040b00040012040030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 202043417 1250 202042167 202042207
    0x1140d09110904030c15021206091305100b011409211c02031201080d0c060f2c0c030105060a0909230a051c08070503060d02120705010201060e0c 64
    0x641c0740070000c840784400542c8804049400340d0103d280315080d10b042108107890320503200306203441142008000c0c8514224440c006010502507040d1070041125200b001080d00c06250344001100c803a0050318180401a00d401c1c1c440074082000024801e00d412a91000d840b000400500302104400200d002640c1600c5101403030380403800ba4821540405540341003440c0712032101e0700119592003034072000e10034044050344140900d4100001c2c929801c0e0b03110f440450900e40103040400d4007203074045000000e00d03600f005809003a4843e250300a250013468501101c0c40c00c0c440544003c0303041c40052500f610802c4a030b082d4401d4003403806000d1140c2c43d51045000a00860149102c0000c421070604070401500e400c80746540091000780400100300401801c07510803c0294503546100e00d00a022400e001d040c20050240100004000b602c80c2c000c00a0a19001070103005207910190340f407500d43d4494040e5a00550a180c1c3c0440d201c051003042c3c601a10807030030941d15244004512241403d00c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 202044667 1250 202043417 202043423
    0xd0512070804150c05070212010b0315190903091d1501050a11010c09051f0507080702010318141204031106090a091112060409020117062202090102070501140d09 71
    0x203c02e00f0080001d0341d881880b034008405c0e140c00ba61002c040c010028468850b80b81500d080c0e042a02d01603a030303140841c8482d20341040350100d00c505e03240c403451030408000f004100e2001d1850720881005240d0309c02000c00440302d58140360300d014101900100c0d400b110446920031542d00d6030790070b101c103948144004c00711801e03940b4046030002d1420820714252030545000d500080c10440307081c401032405015030350110240302c1072400c0d4000d01075000303881c134020b03898090708900000c100c3c1403e59002c3e030070903032580c2911400400c1c842290320b403066003146101400c50075031103881c0101902440da041280c0640341c0060044900d8114401040f000781c1c0541c500d582c002910031400602495180140c90280d800c1c01751080c1c03136808604944110600061143d44210f0401e410324025036080750408101d542c100051010a41c3c030040071850b480d410700c050050380000070303142e5501c0565030f50103000041e030300343d0a50321210382e41d200448844600f00c0c40b04044580400039481c1c80d202560200e80c0ca584 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 202045917 1250 202044667 202044683
    0x90b042009061b060901140702070302040207020a0308030a0504050705120c060a140a09051e091302040e0d0903051912121b02060415060b070609050c0a0807080d0512070804 76
    0x3000c1000c032800120014020f9241c2e1041c030038841c5001d000c1c080c41c0450f2074030181c2c00b411490100802550360b03406200c040d000b280d000072071b5009e644a000b00c01001c0c41d0440d0303c141c2d503410b095201200400044501b5203550060f03030f601060754500030441c41158107850006050714041c00041007455481041c1c18024844840e40c030311401b100d40d1014000501054603030405171032a00302808014200400f00484101102d4030000041d41c6d035800c0c8a402c84402500000d41001c540301040c000e01c9203550b514454030400f14010308903a80083d14a0649106100341c03010566405c0c40d511075800d942400500c145403600394403070424440c40c074515030211040d00c0824960581c000c407075088903201d4000001a00800d08000a0040030503013490801c0c078000041102c146803140c00d00d880d00816200415194a03034079180b0510100300284403c1c910020420107030309944810090352404188182092400b0301c00051100074080e43c1900e0815890700b50980c04c942c0c9541081b1131240f80140b04640c82c0e6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 202047167 1250 202045917 202045927
    0xc1306080616020f0105100909030e04180c0f06020d05070501090b13111914030a020901151106060f0d0503192102192001020a030204090b04200906 65
    0x5008000c100d006180752074110b485086204002400c009624010000726030402041c008002c000074000021603d03843d400190003181890100c0e42d2101401c00194068104504407005404901c04c01400c2032007001600042c076a41d404141e4035802d24400c2401603000300400c010003a01480080c9511032040c00001007202d16541c0e880c10401c401c0e240b000740000d0b03090030078042148100b102c40343c002c03040f81c64074505080001e5000d1455045d0068203504c8d10102401440368902308651358140d540244100c02640e181c00c031040c0c1545200b4680c1001030706c10303c409080848046182c80c000c6030082c0c02400e4025040301400890300d44900200c03030505c0100100020941c0103d1404041541551400c1c0040c401c10501030610108400912100d8070400c03040c0040100d03524214401c144500742071000300e0300400032008000c0080d0601155500008a003254954107a00034003e8466914080004985900c103200c2111460907259010481c04040042c0050080010b008180c3d001001c040c500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 202048417 1250 202047167 202047179
    0xb06060412030f03050901180318090504050f010501050d080405040b0a0b0a0e0306010807061e0302040314030c0d03020f03130203192612011403070906031208011401020c1306 77
    0x510101d9400e6000600103800c04022591602030a034004580200a100316042161000c40300c98803c40001c09200752070080041800085001000802c1c1d00c24040100c1d16090802d152a98120081c5070040d51038080045154944a0011080d9540000800b800c2a00b02800c0c88014241c0403080c036400898401c0c0014094801001410456071607170795202598070f13020034035150400c1a0001c02035a003100c0c0061007480d5210072503d200c81d034600c9407410b0350b05011006800904c1141c201608681000040900340c0310004000d22052085000722004d18108078011003c03400f40040c4034020500410100702081303200b094100600780024255000419680d14584002850b80421121000c40c2c891a0315001014a4100e0121001904051a15058280c40c0c401904140170300240000300000440258508020403409071402c2d002c20414a0b44030f0812840100f00000c15070005001030002051914856800c0662103506800074058003058a08100b0314003800f01d04142001e56929000542c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 202049667 1250 202048417 202048439
    0x703141507170702070b070b13021009060f02031c0b0f040f0903030b04050c040303080403110304171c09050409080f0d0204051e010c14010f140105040b030a080301030b060604 77
    0x1503601e038035a40d0b510410351a48000e103a200900321001d54200503000c1000c0100760741100d91030b030740c083c83c00f4485a507040003c018890a0040c081d402617501016034040d5070700658800207039900764031400341442d40c80034200c0ea6881103041b0700144016004c030800d81c48a154000001c0144014019429030f2010320101d4210f8010140303819071941c540f2800e400b030580505c1342014592082e10240054900f041d15940a807249202c01010854100006414184502119401c039010101a070340d980c0c1c0d0341e0441801001c13030403200c2803603801001e0390300c495201e4290b00c0b07031007031011038848035482442d0008200040c6101c900c15249400d04202c4481054002c10003001081004840142c445007003009004e118403071007030b04c0d240301c882d0050a00d0440c0c2e000354031341d588254002c444c41d0495095010060141a0b041e554003d400d0920701102040140440c2caa416602c09440c00c0100e00c15050406541d10003040020f0420441080144045407050802590010014143c81d150590b90f14070428 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 202050917 1250 202049667 202049671
    0x81504050c091203070b06100516031d0f03100c141b1e060402130906090b0f091203012603040914010e3303010e0a1502040807031415 59
    0x11440700024402450f40340450004010200b280001e60174400c0c0d982e034115690310050f021a00c200c500300030b03c04000d0f224400312440c12000d841c19684160441c03030090b0030390505098454504c0c1c505001006241801512044590401030060510980b142148002008075940c07010811000c5c080304080e002c0c0384402001c000a054080300d20201c552011581403c1c0083e500c100326000300c0e03420441c4084000f4095800c80d4046914406469808605400400424200816a07400c1a94840c1031140200385184281d01041300c656841c1c0d10385400c107880783c62481c001140c01000780014802141c64040c10303440000c01488005241e40140c100c00e03d140c00540c00507409640790141880c10003c505411030061120174001c240f28140f401044140d0b844207040c1c101500c06070340e800b036458003065021410194002c4d0003048040c00c000621510740e180700b00b05641c0c03a80612403090000311103101b12003c5030019405404914250740e80c001c0e0380065100000e096100c1c01d4820100c0e105420340040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 202052167 1250 202050917 202050931
    0x304120c05070b0417100e1005070c0605040803040302150705070f11040207080408010c0201020a0e1918020c060f071709010609020310031e0308150411030106021e010605060a08150405 81
    0x11005c039031a150442c6060042c140c5d84c5102410500c00101800c800113100807034032400d14001c03419a0324003600311481c0720291405031400c0d003008117110a0140e680000c6004030b029609580c3d904004900f00000e00d041a100100003980402a190105101c91018031075684038146090f00070080d0301c0003038180e070001001a55000c0c000202081002024803a6a8040f8010b000039420301000010140c41d01029079070040c01480c188000940700340362440c1c0c410140c00c244d040d0720826500014010006d4120309041e810314030455020880102403414094816205607441e1101e502940b0300d25014031074058032801c0190340318280415040d1041c005544151001c0c508449028034508203c0740f40d0101c3d50004901c419a0f00b080303800300f9880119a0b50150961a08480320500c0c0800b18008002c4c0002e81c411000000c40003198132035001c2903c1480c02940034132a14007503201048c40d0300f210803c0c0309180d40030b40304001d1a5091402078000b241d12071201c1100400e15400c0070041800d6401c11100c074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 202053417 1250 202052167 202052189
    0x304030501110c161d07030e0a050705011202030c18010528091d06060306060906070c060e100c020d020424050103060b040e0109020f07051009170304120c05070b04 72
    0x2001040003c011003d100c41042d400400038074a41a1a40905541e0b0044c00010585c4000041c2180740207420400c920340310a004c440da030019509101b601d54606026550000e0349883c005d4405d043e0b54000d49006141c01032040b1b28103200e8904404012100c658920705014040c4000380d20298000b0032030307409401107600d8441214003c0d40007400d4220300d400036a0610400b860030070441003182007203a4001d4095400381e41daa00c030a00007584500030618541d40c0b1940c0040d8840c204101d60791180115602030f03c600045c4002d030702c2000740847c40c3c40351042c00200412003000c0949881042da0900394006800040d201c1d4808240c80f02c1000c6041080080100b01e500800a6503072500c1031100030091290b43c00d050038100019489100702c18450168401e0b00032420050381100c0c002240c184651180881c0e807107401009000011304244d08050b2000d15119566040c40ca45000489120340e901c1805020541d22090040d919005054000d440903c945c62010445a9400001340041c000081c26 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 202054667 1250 202053417 202053427
    0x918131505010e01120b1f092309010b090a0203070e10050304050c190e091002160c0506040518090c030106090b13060302060301170f030a051207091809020102030403050111 76
    0x1041502441071703002d01520022504c2400100301d00c995046c0e08512840c2d4070005805000d01420318007407035900207181d441d24056561501c1d600c42c0d2204244041c00982c040c0440e80c80c0540c4500301c8401484240d00510928001621000c0e254001e41e406820350034201c61034031001c0040341011381011410f01c0440c00020a100a202c02040f820a401c4d0080b105101140055451030005031428455050006c88000101c0c060940602c090100b90741403090031900c5001030000000c00b008a0f40064646030603031240441c1508101d8100c40070f6400c05030210900702031803a40c4400000c4028900d8406010300d802010956400380a00c100501e0151400313b155506981006000a40c07441d840e01c0700c038900f40d42080180c0b9201700f07881c11290402d001d480d9100d00603050740d00340142c2503561041030000007005245950084046c180980303c0810785020b941e1003800030b840314207640c042d80c0c192a2080081c10006c0b4030710340140390840e1041c81500d040c150b50369141ea0a43d01c980d1142000301e140421 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 202055917 1250 202054667 202054679
    0x30c0705190c030b1b0d091a040c0b09061c09030906030c081602030d0e0606010311030f010302042a080f28151e080606010813060b01110a06090611091813150501 71
    0xb23620120344190807180090304040d5115134100e1411b2185d4503040c02d02141940c02551800b09031400541c90590090652440d101e003a402015025011408101c8000c40030403558880c0c440c480c0d000205413203090300e617141c480902e070740f0755848040181148000c00c03185400c00b00a003d0304259410090050070f66041201c00501a2603c02c6642c40c1d016006004201d0b05940800740d850440740c0558001a4078684a107240110358290302421110b030b520b1240c04546a50b002d401242301e281c02d21802184c6071150305620840c8803203185000501e99406200700e20954007030303009a1404c1441145031104a0b980c0f604503005501106407241708141da500e04000158050203d680e000d0402d10340f000062406100e82c4174041c100b400064101e9a170b415040e5183c2e40903002050241805800f103401e05d107801c2c5442c8025000b81402207401c0303070900d01505020718203001035548040e80100341d00700d20800902d40c41226080100401034918008044001041803120805524030b6905400708131981014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 202057167 1250 202055917 202055933
    0x12150114122406010c08090405040212150a050f040f11120d180902030709060c05030f160c090b01090b031902070c06140702060706020904060506030c0705190c030b1b0d09 75
    0x41203e8103000d82101104000784841d0700b16000c0c00c80c1110001400d48580c004203e0302903100760103c1c01c41c4200c080000040340e507014540d2040e640d87c074003488a0b40e10b00c401c13250640b1080d01d000700200da0f007100410004582407444030318004050300682a00740511110362a20710068445000b040d0000f480c26121081d0164450180001140079840c5090035030000340000c209101c0d0b14108203003030b0030039010064207000f01d40880b82151105034036668412500c0040400309542129202c40d15003000500390100d004010b40e00c03078161216200c1916100b690451a440200004000100c0644e0b1220300c54840c800390004600035442d03546010300f0280060b150905406c4204020441400000c0050752100101c54034180d1181016031103c0f0b424000c02c000c4c04c12a0441e90b070048011040102096501e409082c11600580444001000f900d8054650380b01c2a2005406182e100c5400d00225000c05507513508100c0004803a110a11550041030b50354108642d1a4029915014020140320242e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 202058417 1250 202057167 202057171
    0x130506100513050405030306061e070803190504051c03060e09060915013c180b091e07140304080301030b0603030307020c1002160305030702121501141224 68
    0xb000410003420183c507031a580b03020041c2a40d101d440b0015040309a101c13030010400341d8200c11354502e03840b103040340b510b59400c4c1c10031075080c4000219401100c00382580790140b039001c0c07900708000c0d03d141150a01c2a40400b0310000130390051546414000680f007643c4046107209000f598003900032030418103100307420078503409480074000441d2401480140c40c0ea01d0003031300c0fa40c034070040f0b8403100503035841c0e000ca4600b10080220800c40150750001c0d0000089010041101e902038040200b0400ea07402c019110b01e00f6a035006440c481c0300107810310307413440034482504000642081648546061858500c03603104840c1160028400f00c010401c100344900d245411500c201c02550035450b00d02c0c6d00958420203a001107110b09030410b0a00381c114000e014448000b044250601e4103c1d4480c00c1c100e9903540316000481c0070f002e00b04d0015912210206898204034402c8414190f143d10384908400445550341d1446d61180010b0b400455001040049660722041e1407841403880c4088170b000b11040b040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 202059667 1250 202058417 202058449
    0x60a0e04140c01090303140a2a060b0315010e04020d0512180901031a100503070b0403050d0206132607060507080903040510080901060b0c070f050118060302031305061005 75
    0x101e10313810b1000a400c90243c03900181c2615070b064440560500459080c8541e158140c3c0b00070b0404151601803039040f51090786540240380c1482419180014140d54901c28862440305400c20300042c4601518254010f4015000500122185080d80c0b551418042c402009000d0008005188004039a4031104410f82c24402c640b0b9061941c516140c401040d4880b10f410541c400c1000000f4010f0519035451201801c0080c084800054548a03089400e5111b80402d1310144034841110052920018099104001c004c401921800e5265203520710005e15a03001d4050566800c80c46080c024480041c201d1103000c1c540226581c00d14034130103480c0501c0a8240c440036002000140016214200c91794010226442c180e4815a40d0802070b500400c100e80050401100024a440010710005a140244d03001c1005000300b595840006540d40803a031055040c01100c2ca41e02008501c5c02079024682c4118250780d1024044400d0391810b06260f02101c040042c41d00d90301d000d2107142480b105075104414 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 202060917 1250 202059667 202059677
    0xb03010519020c01060807062c0a06140d02070303050a0506030604080a05160506040501020a0206010807080a030c030e0a08010e070911030103061d010c09090513030c0b060a0e04140c01 81
    0x141400780c2800350595507414441c07941c000618190403802507001c08001c1c010807050318030543d04c0d02c50042c003001c0020f00c04811a5440c00595558100f800700d800b03500d0500902442c6d105103071040c213890301c0c14901c01c0a01c1c0b0701001d001c0c01d003460046000030002c540c481e80d00000c0b00d2400c24182d07000c03280040c0c50b8a00079401082007100082001c001c56883c0055400d0141d2076044203070342882d03103104450b401011405108240010040150040c142c86503158080d1146130384c8608a40d0769035081c91043c2145540140041008a80140c0d1102d003942d0180c03400041d10003160700465141803203a40240c40680d52a08103842c552800c0c0038401c003801c90406e0a00419001c601c103903806000600015001c142d4034031141c010290b89912800382c030100030000340080381c140ca400ad4a005100c0c4034510904d0308120026150414ce900e01c0398000b82c0c941c4466410500035103565103039800007403600390460345889012841450b24030b0078034441c52040c1c0350381e40030090242034581040d002c00d401a05100c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 202062167 1250 202060917 202060921
    0x6080103020a120c050603060301090804141c0c18020c031308190309030b0901090b090105070801050604060c0605060402041d01030c051207090915050711070b04060e01050d0f050f07030b030105 85
    0x613400000080c01c840c400c1398545d840f5183c01c40000e0041c05000c0c2d000744550340000d400603003000d50301030203900010b040f034092802c0c401300450070202441602c80205460303607080c0c0030301150f41c9680350000c00a400300320060410411543c503d00d1a03100a00760381101e50301003810409140200301c400803d00341444054000b0307c00c0c3d80c01400e9940d041c000145500200000601610025441014296080800e12600c0e0404403951402400c040d99080000b604040010445043c0401190115200f40c0d84071f1a100302c0031b40b181c000824020303101591043d005c000010f1122041c3d4140f41d0243c500241c480c44a5241d4600100c242105900c9540142c84412550b54202e9010032034808540d2020004210004140342ca10070806c4403070203003100f4078039140038840d0082d0f00c0000401241424002c07564015180d16041c08180214401c990008000300d40c881c2155100d4000b0300b104c00642c81020030204201d40e42c41d4250344044441c8194040001d0412502ca5071601403a80c1074141a03000300024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 202063417 1250 202062167 202062173
    0x8010c0c0201120b0301090804080c010912110d050303090d1b020a03021203160f02010e01110d030e0c0a06030209031204030203070302221b030c111e070e0106080103020a12 76
    0x210000c200107030511031a035122035401c4825401c08550040e006008011200480c40c0041c10740c1c1141c00b0b00385a91007000198005540900190b00503140c0e04c010000490300382e0b41d61101681c214912132500040715404080000b41d080000d1401007903150003410016007110001080c0d00d149603a40d05902254000302005a100d55041d02c0980b03406441035000301007420031b00b62030b61042c4403680c1c0001d04a41300540c1800128250000e03103e2007681c9501c0711515980045902044c01c00c080b0703406030030070912103100d00d02035400500600a60300c15140c00e4581c1c030000401e004002d610040220750002820310301da1400380910071072100444602c50401e8107540111756150510301000380a80c9103020815082900400c07c01031310704a620040c1300b11140c1c0c1f1007120304a082c0d2140e00c40031a01b071640c2c41d0302d142e008108410fa104000c900504400152841d02000c0203080c0c08956401e000311070000c580902e00440d054043d001c2c5d6210046654551310500400c800b0f280e004902c8040030a00000c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 202064667 1250 202063417 202063427
    0xe1009150c020318181305030c0303040c030605070305101e030602030f010806060d050a26071b050f0303070b07050708070f0c0e0f1501140d05010f080a02060a030e0102040e180708010c 81
    0x300b00c040b600800d100047c60030514510500b0004070261001200704005c214070507541d4416a88540010300050300c0796101238041d1307181925420340c408007440007400481c149203010a107905280c200604070300c0c0d490b00d80d00200c1c0e1044d00c0d81c104844500b0b0050020340c100300103c9420070015980710f003280601c1d8440503103503c041032000b4401241c5142c0c000d003144c001170144007800e118042c2c541d47e5504916141040391481d000d0411846900c2000085c18035000d002005c00d40700c050042d62801c44280d4820642c440000c10403421710400f4070900e0301142001c17004e440a02e02c101c0411080600350301b40240a403046503c201c0d01441902c007080100d0021401990f04000c032280500b00407203030a0010384101120150f1040c100b0030204042d040001030f500144e040351807045040e10241e40760715030300351541f40b2080041d4202004100490605200f40c3c446080e01d10181c0005003881c0c0c17148101c21185405a5001c02c82050048046025910502c80f100007009514000c011030112a00082c0c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 202065917 1250 202064667 202064671
    0xc0a050607060b01020a080a0824210304030803041a15010e0108090703050105070302040515040602120304030e040f0b09060108061c02010c050312011502010e1009150c02031818 78
    0xb00c466107448036034a142c0d0082100003001d6500c5648140c03600c140c0b40e0000e014071004c40f034202c100055081d08000c090350766071070b000340228040c0c000c4445400e10a80011112070401d0705401500c000c2000001044d40003016500a601c0f98488030448206840d89031002c50010b484044001600200301040341c0c3c201107001040b4400703082404550b0b44a8a05900308a0b59038130240032942050100502158107900900944800b01c0e0600b04140204c04401a02d00650007000e0250748500050900580000050740e0700c0741c840c0c50190307074450409000c1030907181e070240c0030214a9160b00c0410403502c1c1071000d00b80d1080c003c0ca0000854a0024005480c8058900080740c212420a842405591241d003455100503005021650740f802403000a5002c62424401c0c42c440c07001c064412101144103028079003000e10410000c000c0e11986000d410014200301c40d08a50680a00550170074120360b50041c0d842d03210307058000d51344805012170b01950503010303084018414100307901d10030020300a03045419 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 202067167 1250 202065917 202065923
    0x120b0a03020f04021905090411070f061113140a0b030912030c070c0312090506030c0d021b0d0201050402010806101e0513031110031b0c08090d080702030c0a050607 72
    0x2450b050000408a0000e1040321201703c8507056200041814a800800820040760241c80c100040e006000801c5014043c041c00140448031701c901e44404296941c0000c4112026258510b2601d40312610305504610103612080c4003c0440d4044880e0f03140088200c801030a01301d024514503c0c080030104c2e180c540a8521070700440002c00411402c20303488050380c200a50000c071180c2c444d5281d04012080f002035001000004204c484080344034100041564003030319800703040609100040501d48003941080c4946005010542d20003c10340da01004014007507030a40d00000f45904140c00014a580401408540070307c0540d03080c0852030358841c13901e032140f55451820508031441a60708071400d11521403204002d81084802105010700c1e110580c3c5c2030101155a400301801c0c002c010f80030380d21302240304541162070030dc041318014020004548130074890204076160681f07980004031002c0c0901001d8580b51004150710086040c200300380d03001c4407070460307502c814503140c100003c4042c1b054000003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 202068417 1250 202067167 202067179
    0x1c110607030f0f091a0903060610050d09050312010b0a080105010201020c03040b0d020705030301061205090610120f0605090d020f010b0307060c06060801090f0302061f06141603020d120b0a0302 85
    0x1030850301c102c1c136510140901c170006510301603c80c01c0960064016002183c4030b405210007140c100d1510803d80300c102da4082e182d031401c02d01c480c04104000d105040b4195440d0004106480614821141c0c00d406440444040e946911051b000100942c10503000702c0e065a00c1001a101d103000d0004c2501e00311120003801c1c543c1c46000320b81d14406401a240e0050980c0320120000c601d042c2c20a8002c6c40d00410352108202585d42c1410f00d42c0d035054183c4503000c0002003410f090080340303040c89003008124014131030039002c1001c03a80d454045130000c40d803c40b00ca4000e5000151456414450710364030b00c1c030380700081c00b20200d840b0000e900c400c498400c1c28144070307442c64024100302c9103800c513500801e0170400030041b072181802c061040901810040300180141c80001e4070010002800303203030724103100071158405400d009058030061008002c56910342002c0c0070704c4155001c214000f004c1c203032003a805007007990110701c0c020f032100d1004490200c000d4103054001c0003d443e03800d80c0300210b980450305 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 202069667 1250 202068417 202068437
    0x8010305030318010b33040308090108070203070506070801050a09110f0c0703050303040b0a050c070302060103080306180c0406181208070c08010c030e0f070305120a0e1c110607030f 80
    0x454010940c803620710340c00404900300105030300c510341071b05090382d5601e00444a11350f03c00c2c0c411581c54030482c04010b0000c402440068010751184e120154000050300450f8079044941c0ca40c2440d08904030341100000d0414070040c001d60030103448450041c40f451100340300903d02928410351340d0280d01c0000725220b102003045d8003007503010031100c4000d6800c130341901e55905250518500b446030450319030038000c1c204004941d00669603021944a50382540c05402c860742107580c0d000c03031940040d084070f2b804001611079003032070304880c9003041c0100c4080300007503a03491410f00302038842c1c1c006541a07040c6036101038003002010304008400b11001e6100400564844031450080030040c00f0b60005520f0398038044103600c8041e0598080350a031030003401180c0182d1314504981d660340d03010f808000c20b80d4102c0c00381c4800c441c8481000d030406034002d0038030304104e40048010032001850044116141410041500305000280e50b174422020800e441d15481e040d030940b8060a050b041030010f200308030b06c481c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 202070917 1250 202069667 202069711
    0xb21060f1312020c150702090f04140d0e0301140402102f010b2110200703020307150603080403080304050708160e060603070e1905030607080412080103050303 70
    0x9503800c4041e6009a40c081401d48644009541c0c20107103402600070659140641740c01010310040d03481017540142004603680d9014958000c940c03019008559245a108400e0544001400f10000500d443e43e115841003002c80300f01400d498a4001d1000d2424490042c8000368940c41c2c5090f4099615003081002c0d42d030221002030132010900c1e04403400c209846402140b8800640207100d602c1c03c102e824640240781810a003c81c184145202e214031781c03154000c581300c1d04498018003a098460f5040e410240d001d2201d6410f580d00c6500101d005030400907030003003001200c1c5104d5148052030039041207298111343c1c0b404220311450001500c02c110200004082103001c11400340a051041d0503602c100c0b120300717281d2007108101d0050410a802c0c480000d0410300b0300c0001e4a216034241c0e9113880c100c4d6070704401d0200c0343d15421200c90504d0706402c00407a02e41c904002c80c500550590355043c0740707403801d1b061540464200100390b80c2003000c0d1000400105400202740c0c3c0c1c201103c08407140f500b200c0b00b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 202072167 1250 202070917 202070941
    0xd0909020721120c0815040c0e0d03090807060513090b010c061e060311130b03030406030b01020709110d0e03160213090f08040f050a0b040b0708040e0a0b21060f 71
    0x4440009680e0a240001d22025070141c01d040c0182c49040c6d4203d006d0b0940c408000903240c500c50b8040024013010b0b1403103450300e0004d4018510ba8000c1c1001c0e4517040c0c803458594188122034000d1404110b00041d8842801207081d5028010300070800100620303082140028980402c00307102502c004e480e00305442015003880c124951505039540300704140c40e524649255061645d0362410710464401d40501d05996481c01200717581e10b0300901035850301d4100340081c0c1c02071604c00d544c5e074118450000c02243d4499140700c0c410840012240103030702c444640c0300d4401a1501c0718050f1105400174400c424030f00303141c0307485c6a81c9035a044415003055000d80d002400101807010014010626000c0050144228800144160b61040703015410309a00e03001400138007007845c403032006848400c0104004800e1828003810055220f0104a0f00d8240d80c1d00000761070b0341054481e004440e42d20030132150b541c54190702200c4c103124005556010b800000002e55102d00000380b4018041c41c1c0b400002d00200009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 202073417 1250 202072167 202072187
    0x702010908010507030501050f04060e06240a081f030503092119020316030308010b03091207060f050109060f050d080d110c28140c10020d0909020721 66
    0x5a0003c0000303281402004010b45401c1c443c80c0d0040d08006441441410107004510030384100704020100b07926000180043c0e05445140100c50010a00d044654402590003c0c0140f00c036680d00c100080c104113141001000d100b1140070b91014601038200b00048022080d41d00915007140c1051040c809515070107038461403002c4283e15402000e2a16000c42d1202140c403862500030f40c1100c1204041084490f440c20352408080e000c20500001007007400c6582c4025984803c00310b0a485001070015070580143d00700c140c00300c420f962a494031001482080c4201030040007154000c0c00058031b024080f881c82d200354018103009194600042052258540868070580c0c1400f004124924841d02040c1d21904160500e100030b002d0005804040c502c030b10359080036040c1c108a4810702402540d5060200e00180f40128114050100005401c4d40d90a04104584005c0e030041c01001c040003400400c1100d440c3c0180f140e151040c051600407640450381950300c0b51420108041005111070199110125 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 202074667 1250 202073417 202073429
    0xe0f0702010b09090706030e0726010905060f0103061b120b06090901060c1203060602030f09030f060702071d04210507141f050411091008010204090203180304030c03030507020109 79
    0x19560600945038000995001211443c2d0303401c1018801200c0c40e03503101e21103445980f0081e90701e02d0040f41903850310700040cae0b40c60000c0d00000440113481c0ea03e09090820480d51820f004220400400c2070150500846040710343e00300e000700308100050070241c072600100180c1138145a0b1290101442d485d4071080f544100b0b4020114a25581c0d1440000c000441060b42110405c0c40d0940385203c4038001d000314000e80d4001c1d00994204030701e8085405460300410001d50741403040300c0346062013a10030700c07d0602424856000c1c144641c01e2401e40590900c103001c9107125501c5075410000480c1141811068444c0340e42010251104032450480b102d0107040c01c0a070002042d0703210170190a0000800135030032940ca144a00144404d040b5280c101c0b2030480d0302034070100c0445800c00291900c20401c6501c42030605450319155181c205540c01c90f0095004003030729030390001c140007003078120010540b000480c0100440c942800c6035242041143c05210080902c0000b080207002c6a00441c2c1040207054 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 202075917 1250 202074667 202074679
    0x3160e0112110702030d020706050702130902060304060516020a02030705040507020c0a06020312100302090f0402060418061a190e0402090402210601031b0c02031e0d09050301060e0f0702010b 84
    0xc501c02c401e1405612180c0128403d11500780c600304000c0c0003207680d00490780191116800c00100d9000d00c008010092898a14655078241280050703a40a000d140114018800082c0310f19040c1206110303000015400001c2d0340c0300d80003038401030750009100310640b44103580100d49a2120b04043c0d24000701e00c464554800500e02020840035800000b40c1901c00801c2051000380c1c96441600c1000c9401d0b00010f034218400c14002a585100c0601e1a500144040c00c00c034582a661b4280c584860b0748941010201070b1101c808001400c0d1300b0b1200c0b04405070102a0a181c4403013500b000450281d40c056a1052002410303a1040e2540c50342e0544601d00710140084d981d5031035100c028600310fa14480340564624400c408149203501c203204000b400449007034104075401c21001c0948900300c030000201d0703141c4618282500c40030084071007412695550750041070005000d80000d0302c03c152681009000c0d80c500b074002c00442d01d0103103050760007402c02c01c1c80f40d03055262920200d02404403401d0301a0008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 202077167 1250 202075917 202075931
    0x201230a0509030106170a1b060801060e030a062c060708180703020a061e02010e0709020f0f0f09030d0f020a06050601110d0918021306031e050708190203160e0112 72
    0x102d0294119840388c07045042c8101e84240c4d0034050510744c01207000150402d0300602c0454014034481350000c100400302c0b600d0303403c1036880320151000d8441c003814200d440e140380c039080302c03410308602744c040030f03c034060300503460074140040084500a15120844031140d80c018491042485000003658024026044031130b00d510002e000c46009e00409005039507004060082140b06210f5640c801300c4140c05800e0003464022200b000c3d410a0042180700700b02002005800180c013001081c40c140040210342d1150644800c1500305650240301c0b000707210361885803240c20781d4003050b504c0c080356100c000041c8039295079004862050b41c110b5a47c940d41b180c807065101582d0050503003412078040e1a9540308251a0346500816801540015404e00e00c00140510020740250003a035100c0c280801c1c188800e8001c000c54070140e404c203941c00c0020504890501c1010401a00403002d442c0510ba000d51540c246403402c030a031038071400c40082c1041074078661000181c2c89903001e0020b400d01840f0500c404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 202078417 1250 202077167 202077209
    0x4171204020a05240d0b120a020108010b040b070b070e090a14070e0a090e03070f0b01060201050a050105030c01030506060904091406090a2d020405070c0201230a0509030106 76
    0x4040c0c03401e030b01c1410402e10001d03491034140704003011a203007102845808005241082155041174903a4010651502d203102c901c2d03110220380c900300098160040c14501440d00000d484e0000682100c1143d00c0708202c10311900031030b0300031588103542c401c1c042407042c3d460400403a5284032001c00503a01c00c1201003449540c03002c0b604100e441c2d0220b04070203843c039107826400766903141d00700b0050b41c0c00a00c6210100f140300c65660141d140301d6100340c1502d15101c0c0558940460399200d4004030303040c0048000500203290309105842d480304003000b08004c0c03035041c8800240d0740d101414943c2d0400d40c94000180c69a2198419134940000282050207064260703d040c043e00c900021740781d00d9501c60b400020349400300001d0200d0302c80e5005044a80303141c3c5d0390f000c0079502ca05045030890b05541e04120303005c01a10f0354032900b0f210f85a10f9031503000307401c1240f00041c8180c00c01d1010501482c1c0440d415a64410408202d40560703145040850396a1003c10102e409041c2640c010700e040c0c8501c1d0000d40e58 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 202079667 1250 202078417 202078447
    0x1c060b030603010f0b01142107020f0607090b070b04020a0b0d0603050c031209010c08270906010f05031612140117070338071d010806060904050417 65
    0x1c0c1404500034800041004626001c071103a0b0808940002d0303503070b84402c1d0341c190b11030010403888010140c041103003c91254031013440081138030740d500185d008000a80d1218020b0081030b80204a51504051492818411122600030a03001800e0324001d11301090440d80c2d02c020341710040c010a6a416102c0c2d04403510305004100e280300a4403140035100d0601c003e0316010038240d0301d00341184100c6081c80c0c00704c4011118804000002c5484070340030858004100c1030b482201c6030710b280c1c000500407080c1030b0005200c1003500c0036100328140038502c01d05e40342e5a80c1040649a020010900f805000503004604075400346061a441c0c0c3d1070381c50174114050084a624030745040e115850030280e60040c8000f00159141007901c03014044c0d07502e004800b40c0e010882000c800d400684001442380e40d4056860000e507004050741c0d90408500310304214001030700c400c0c100041140003400c282507986451004130b0014032443d180c4034032480d0740740006010402c8505886450f10b4814040700d484204207225110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 202080917 1250 202079667 202079671
    0x8010b030a2004080f010b0d080309120708090a1d011a0904090f0501140121080f0d0501031407030b151804080901080114030a020405042f041506080403051c060b03 72
    0xc0a00400d0305c0d0f90703900001401030a01d10040640400380210384d80c4c507002e0b07060b0806480c410040c0105842a0070340e0b08804091701299004110381603580589200304903102ea160342c040c40c444980804000d00d841c200e850f026046075540c1075080c80302c4c440110065440d200e4102403d60182c07903c0f0260f000d1242d06424031100e00e04c9180204114020b1109000b42070314244100180340c0b03410042e41028070440b10f124080c0034440e4039010f01380590784042083c0b031b8015013020704226030350b2401082809600c010400c042803c080103012851b003180c0700d4440080d0020301040d00845500030b40012034a4040c5418400340700c0017041c00240c100303032400b4426548213000c0345002031041070001c0b41c000219040700300d18040080041040052642c248800381500600c141c0380700318000c1150202c6c406c05030001d5200046800c00a4900c2002000c01c01111003464203040754130b201e0039050102d84e410480702600b06405043c4140c40f00540d002605810500c4946903090a080480004690301100040c40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 202082167 1250 202080917 202080929
    0x118050a120507091118030a1509020a050126130c030507060e010e09040f060b0303041517060a031b0801020f031806091207060608060c12010f03020108010b030a2004 73
    0x6400e540d1340d00e1080d015900300716010061000704101e0006040424014010010405401e50b2904407903500d5502c0c2c040b0b44451140c081903150750511046182c40842d00e00034100900303121201c00080b45115650614084404101e020b0320740c0421040c84034a04010191036000e4080b032446512860070a0310741e00b0521401010400c40212040c00d50300401d02c1e006aa10040c0c03182c0003603a60707034851f031000b84007010060743c1890381c803091114280c03001e01c000d0002d426000b40172490300c81d00c0340c1e00a11f80a01f0024882c3e2480250052002a0f1b03102101c0300704503500320b010701811200030f4440d41d001c080d060f401484550300c0041c0e0a00e1104011000e5807245042d4408080b040350034501e030036100d407000c40d0044000d41164000909845550028012480c051400043c20300e480c2c020b014a46003040e90841504400401e510030799400c80103c0c54090a1a00c4540e070000f03145a0020701900410700401440c081c0105c00141408040c0e4052400310389030341090111b05090030402d60095103c0e0280c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 202083417 1250 202082167 202082173
    0x6140a09050d080c0304060c0c0f08090a060c050c0f210c10050304031e05070c0f141206070f05071e05060109021c090201030209090c09090a0603110118050a1205 71
    0x34042c1e042c0a9000c50380701d140300d4500c051455403a90f03503040003411820760503000d1100f0a020b15000c1403800c010194054801e0001d1942c0302135980402c2180981c5a215034100210403902000196010661580d0b805081d10321800004031400040d10240c1120b030280e500038104556014861800250701e101c41030152038142d80340c080031200300c2d018401102c002d40810207001400c3d9084021151003040c4a5a510f88117090104640e1120882c50081d400003510084640d0f082c03001c1941c2e102e444454610441d5411140184c036001c0548030800103142d00705008022074148070071800b5138100c2d030005c1da000c480c00c1c01c0b0340b0000c031018940e0b48000380247c8007807081d5000032441c8165482180d4144910b92250400551650685805800c010004a0426400740100c50b804d843c0c10170220b02801d03140c61b4040c1c45406050622a84000051a0b100607a003043e80803c049000c1ca00f4000b4005400c0ca41544500100600c40e48655000d030b0003607412a40c080c60018440028154090301d0610440513 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 202084667 1250 202083417 202083433
    0x60807050307020606100e03010c030209040501050406030b04084f0609030f05070e0106090305150c040902090409080316022103160212070f050c0406060509040906140a0905 76
    0x4200d603107000449622000d03900000100d0010b15002400e001c1ea0760040c03401101d1a45d5180210b400d5554480a40012940118510b4550b2a160044901401c0e0a450412a69141d51550b4201e580c019102411514001035450300d0424003030100300d208014156140d10070f400e0084d1a1000c1c070300200c4210f00d006100c20784408a10310b0b80e61810115a40d544d03072078140c00d0179526480c0390400254005c9400d403154501c001543c140104c125030090206071600d2003c0d5245042c40d508003130114040407003c403040c00812860410034015034080d034030b00300c40040e10b80f58008042001070150030009001103c010003003061040d210701607441181503035801d5411000c0700024034040244407124114102c1c00602c0048c0500b2805121500340002600c12180c0328900d038845600c0c0c80e403040c003040e039502c0b5801495005004c0100f10703030300450b9029941040054a0060004d005003da9400c65101b2502d500741c050501c0300542148042d20740c100134a40c21418908504401081c1071101112903014040c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 202085917 1250 202084667 202084681
    0x6060f1d06060421060c0c0302060f0c040e0c070203060c0307110a0213050601120e0715020d140912100608120a0806010c3206010819060f0605060d02040608 69
    0x14101d0140c5400b07411242014100218254404407140901a10100f01903a81c0003040043c000c0700d540400c03d031100c0184d0050f03400c00a0900c00028204403501c036072103043c466031020302e074100d508070fa009186103107064a401080e010a840b400001a60501c01c213070a201818009400071402412030b511070030201d000d4861070588803554920040d6120544408002000825030081c950007441450407076484c003146074085c0c048070705000c9001c0d603541c4014410b0200103003040551129000c280010000c1038400d107002060040b520b079590b50851000301c1d003401e50b0b48812950b0000c1c80b4004060b900c15256002c24100145210322904d811403190103003038406420003c0031268100d00c140d64000c4266980c600648146c01010f40c1110f6040600d40600e00c80107160001210811541c10070204103e04da2070420b1400e401a0411660703500001540f1411208409140004680c03113440411008101d0030b0910042c0b4250b031000c3c0e080306c070001d2240750b80083c40e4010801e90f4016101c10f141519103030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 202087167 1250 202085917 202085969
    0x6210e0d0e0f030c0402030a0b1003020d18120e040e1002030a060608060a060c0f020a06030902090627180706050c070608010e0604020706111611030a1205030c0706060f 74
    0xb81589400d6007000c4904c1a140c1880d400035544240000804229445042e01045007800050a12000240c0c045561003884145028800340f007100720b90b0000c03142030152100d03d040648000d248007407294040d040d03409034a85800c4059040c507031606580d030721884060a4406903004a480e4008075241c00310100310780c0c3c02260094050540907081c00d40c2142030000c01d0380d90351003080041c0c880c001d048220301d0041c0d0b500013500c0042d080b6507030080b51001035407052101d0200d02402540c0b049030640f111500402000030205031400d004910011507460340000000409061200e0300c40360302030f4200c0456001d41000007081c8540300c6c1c0b41203a10595031400f04440206003070080183c4204030202150041c035180d005454514021100090102c0048142d82120307405921603038019600a14080144000186c201180400c181d010780303221b0445a44180c940f0064400c008280700000c030201c1c42c90003422007901c001c103600c00d030100714150700d81204d143c00707840911585001242241005c10030704007072 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 202088417 1250 202087167 202087189
    0x13050103080a0503040302100f06060e0d150218030a0305071419061109190f080307050309011b14010501030b0c0a0f080606070c0e09010501060203070b0106210e0d0e 73
    0x20030389240c01c0c0b02c1d490500301c9050f4806402a000c510840521749814410307071080510143c0c045a00107495071600c440035203000711026041d84131310a89407009010030a070b520b164043c0e000100f00140d860300b000000c1502d50000400054040c03203038101d13850070513030070000820000d80141541401008c0c07103040c0c01d80d104101400800d2012a0399580d0000490320f80207001c9d11000e030540340c2e09103180303940400c280200340c0310014005600c10008004001008a603070018048400c0510700c5d1244540310b00350f5030300c12202800d0420128483d5030546555002801019517805001d401545030031040c414007901c4280019150f0b039a14202148a045001341140c103c089281c90340000d0f0a21401c3c280d80710400107191079041342c0104a100002031001d00e840e00a070510a11080c00c0b420852182030854905030444415503200b00f0585020a80e281d0701141124050725140d030707102c1130f14900c01c10b0031458521840300341410031000503030700728022682c0030245c0240e076034901070300503101d041284080360 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 202089667 1250 202088417 202088423
    0x102030a020c01030519090c14120a0b06010314091b0d020607110607141b0907020606131b090f0e010f0909020607140c01081b040b0c010b19060311031b0a0c050105100513050103 78
    0x2071a40c3d034002050a40d40c20b8dc0301034141400150058900c142c4152800308031642d20090308003d85c60500d403000c0c041310f21001002520003071003040440d4007040c0c40b40714032103002d46101c8120348000401c2da11a8120b401d00c65000c1d0800e080d01504484080e65116103402c00d0039a041d00c0c00f02c400c02400e220700d403148500050340c000c0400d80c030b4002c02d214a0440c0300c018040282e448140f004000840e1025526016141c1c1c0c0e21402d00a00d45001c41440b56051b40007814400224001000500da8000d510004d40e200d05074002100b000320f100150305441036400003011011034404030f5505076404910100a01000e894454160795480035107000100200114401c1030307014482800384640f0003018003041c04245000043c2000c0c42400220020100305070032032642c0743c00e50305100080d81800340c690038400c0c8036441410741c00c1c10b516190b82501c02c01032610b0060400b09a13180114880d0081184064110000704481d041140c1c4000551049004250040e0502605024a10b15900c45c0700d0480390 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 202090917 1250 202089667 202089673
    0x80a0905030307020d060e15150910050102030319151d06010c080a12110f031f060e01050307210b0a0501050309030301030b06010908030c0c040b0102030a020c01030519090c1412 78
    0x1a54940008010285070311f909031003080b25241c00402883c0d0001e0003003240802c14503124420908125001c0700003000340041c500106010812640c000058130b4001e0b1402e04006441004500b8400040101d00d82c0812108490640080c0e8038901c03003031841511003402c4042c8503580c1d88170010754042c1703030816008140201c1000384020692040c0c10b0500c0101c01d880c004640c5d1192651400f61a400c00741080c00400720020034400480f00c205080040041e00b1610405094a0080c014044054031040c080c184500000010303116031051112410303450f030740486440c1c1d0002c9988600d0040501e1303124a4080c06070030101088030740c041c005030b83c03040c10500025032850f0b0071503840041c200360140509044c0b0989140c08900e5040600c0540524164880108805501c41040005031101a10402d040d5001041000005c690108410715582030a00b40401c844d101d06400c6400801c500d01859006840c007003540d010087d8440c1014100c41c40c0212111411940c001080f1030710141c1d0a4040450f4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 202092167 1250 202090917 202090939
    0x110a03121d060103060203070207080d120507090b030a0b0415030b0408070503090d12020c1503182103090c040203130b0c0d1b08070f090e22080a090503030702 70
    0x124150061010101e5401d400c51009082070009440c003002a00210344081e0040308000c106903040240034020001c810081841b034010540c094422542024054481500c49001a40c6e480c002d060705001851b244c80360b1f036030340c3c60449081401460480002440b403070500c60640101d440c0d50102205594111248100c6031b269995107030190360001e04101e90718001805205400e90b1945001c0c08111b0040440ca5090200c001d0020304206010101d14030910380017819403412100c0d8419254005901500b040440d03c1c2c0380704e16454034440c5c8101e540310500054110945c40f0100f4080d5002e40d40d0b40d821903202200781c40800090b800215482d1050704480e61039440800e0040c200301d0b80043e201e030020344c0381030030152022040d201780011590010340741c5801c40004660000c0529440513451a000e00c140f20080c01c010704d81c0e2518464003201c410001c01181e540c0c0c1d0301130140c4400c1074000c0d50392607400c4001d26185c001a0084d00d251030114440701d034001500d04011044800c2254010301c080300e58 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 202093417 1250 202092167 202092197
    0xa0f021204052103280305150609040b0312040f0f0b07020d0c0e0c190804200f0607060b090903120103020402030408070c09060503010b0616030c05030f1306110a03 72
    0xf43c2404688000030b100f08030703040c9180041c001000e0034401d060f803150202d05010000d56601401c0c1881c10205490318041004505007111030040060040721030fa583c51500d040001e01a0070240c4090b41e050140010021500c03040780c0040007102e00040c442000c540d9612504100300409125410784100d0401844006291840d03545100320b00ca120700c051510f0b10303080c20119495080300c811800240004900350802140d900054240007149021800b618007951045400c0c0440001040301c01089019407500b69155650340c02000f501500b103986401d114104040a00903041880340280d8042000c82c1c40c4600200c00c17a14050b100d0305a600069180da401d010080d840180705440c0d98500340084c00011380d016581100425812901281c442c2c104000c15007100c0145240d148510350400400e00343c00c4040d108640d92903058107080d0031f044401d00b011400c3d03100e24032504404420008800b8140c4012210070415500315580c0c80d0180c0010300b01d841d90b14019003401401145158800d00b1007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 202094667 1250 202093417 202093429
    0xf070302071b03050c011202090a0302060c030408160e1003120f03020904090605040b01050105120c0a050c060f0108070b03071e030f0923010212011404020405150a0f02120405 77
    0x502c1c0b02d07141c10002e40200c4185030b039a00c80c1c690001c684a0f003100c00400099a0b0008411600b0f01900d0421440c0840c00c0300003c54102c46807200a0007240d01103801e2110701010b2080d2002004103a0946a0101c01c0c4501188050f0a0707010706408240d060001c82d0513069000c040740b064a074080c0c070141218405c0354058500103040b01c2c0c144109a001c11807071155460b2070003072580c1d861051101244c2d07414145810350090105030045810004c00703000c1c0701c5182c007000c143c3e5600941c402401c541d60b401140c41c01c44192094199080c0c1718480e0005004c440c02c00740b02454102d54140003038440c110340f43e00e03480710148015503141c0000f0b40c0c03642c01c002070340520316440c40d110b4081e0b0030300040d24161145102d065440301035090b21844071125450b2048240c503140b99030801d041e00e00071890802121244001203906001d40c9044405402c2209200d8803203904450150200a0903030012660810100256170700c5401080700041c558500c165460340000764040c01100c0a4083e0b9050904240034804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 202095917 1250 202094667 202094677
    0x120203100302060703080a0c02060601170c040905040b070f020d090501030c180801020a03050c04031a0a0207020603010e010501110604031b02040207080a390f081306020c04140f070302 81
    0x260500d010800000182e0700c1d680188040d9103c1d48030100c0c1c62500b06e151104551441d10301c3c1080d07402c90410041140c1e4490b0540050006800403104d29407240c2544070481d014a0300503ca9092a100c2400203200f00c10b403101f44205402c4d0b407a03a0380020400340898903021012099004507200340b8040c001c2d903000745c000d154107041902d0080c200050b84007514610b20b4040d4461074459500040e40ca0711940e00d4002e0036030001412420500e014519a40c007100c049078592400103120248003c01e00c5100180c040315015600101500c2c0c482d40c40d140e019130801000c1c81070a01107441c5445e0303240c2c0d220b80403a00511454150315246400c4030080c141e00300031036039540c04a0b40306070b00300038000014800d1805070842c208103a6808042d001812aa40300f86242610b0900c3c0710180c480d18484c5c6481e2500c00d01c000154800440707120310703d803458002d1842c0503903040c40c54081c89540c80881e0440e800141107610400c1228288150030246140929801c0182d9080902102d00c1c2c0028281c039019400500d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 202097167 1250 202095917 202095931
    0x5042403140a020315180c1b0708060610030e06150303070c0e0f090a12051b03160c1406190e090c130e010b030604090206160303200901120203 63
    0x10840c061403162109074403a040750881050395011040c495400900d03103450380031400c290781c840d20313441c040203070a10589030040400f201d1550008020012550881c40316681010040c21103203281d1302e804c1080d4403184115059405000300444213440c1b42d00c02d0150300407241900001d00f40b580c03500c0381d4052940107000d85c03103600f521041140d00d0000d10704a0302d05000b40b01600e10070300e4504101d43d40714203c4001601141280e40100240c0c2c001c1500d240414021038020f0900554403540c0e100160307140440b007444000175020104844545c0300e40f0401300c41349184640b400c540c0040d2901240d0911750903c00342982c10800c144401d405031454042c0b0301100943c64141303019244010301c00100583ca0840b111200301ca00400c000744541c490125102c0a8120140301800a42c184549a00680401001c40340328a0b2140c01507019522803200310741c0c1940e20302e8000c00c07005c0701d01d043c082c0207031a02c4003010022800c1d1905800b1000310078019181c065005039076039000041d01000a80103904060200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 202098417 1250 202097167 202097171
    0x41e1805062404080c03010933110a021002040f0302010e060c03030907031104180b0604090606080c0f09060d03080901061203120e150106050a03060504181205042403 73
    0x307549000901c1d282c031484640511241980c440c10200c1c801d080078104188a40240e051095040010b40c0c00b400c0700c0717000c140c80c0c6072100c03002001c80e00344485060201c4e002c00b62145491088072006500704000e0087c014107408844103d01c800c0c41010891217140300b0610501400c240610041d0f20568a2403000c4000411260520201072010380c02e5520584803000790740d101c00030400811001540107031030400100d50400884050440b41040701340700c00340007030a8412020005003951703102c7e0b200c10306140e0084030800c0104e488a400c65540d1001d84805803040301c054054a4480c51b010000700c0c41550080c02445016801c0c3d9800e032404140500000c0d003c0d5260031001c034600ba049221007107860700954505408800e1000c0342c004840070188101c00c990003045444000c0418810310a044402d03510b0b019136600c00d040801c030700400c0c0a4210030f034040d00700400300641500400b01010000d02440c00324105501c0303d1400d954a2085101d00c500c500310050070215406140301e0742c00c01c015158140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 202099667 1250 202098417 202098439
    0x100312050c0c1302090108150a060e012105070908011109100c05010f0c080a09020f060d1508030703080702031201060c0204090b041b0510200f030f041e180506 70
    0x60516420004030700b01c030650106520000b507901c10345150300108c1c0003207895542c0c404400400c1c22010329006620900858030070405140c0d200c0c4580d85552040214080c0803150040c0c01400588410b441c0580020b191443c082030340c020620030003a031003401ca0500b07864a150728003401031a4052405482c1070241d2580b03000003040c428000e42c850b1051610b00040c0000d90210701428001019000c2c1c0c100d04d16002100c0b0040c2c56100389076002000440300c0340e44512034a9101382c003a100c440c640d10401000d8520001e4420000406018070b5882070b2208042581c40c981c0881e601c1c020070301c0283c4181103410040081c28095038415503290700141000c00d00744010348508641031002e5900b01e030041e01001028103010210026500646000c4071600005400d046005142c1c0314441c401c842003020350508511955400c101e19003030f01508005603611103643c10080c0300b080e00300b071003910a500140c9580f201100340d100e83d0321043d1000c2d00007c1c01160b4400d846440108001461260000781e0629 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 202100917 1250 202099667 202099669
    0x103050a1512020118151202090f0d060f020403050705130b090c07030201140c0d0c021f0e0a020d05030304030908190f1b090914061e0705090d060c08100312050c0c 72
    0x517039400580608201c090422140000c01001c0710042030701020042c0c41070110301d05943c0c5594901c0680c04d03007220643c58050460030b02200130001e41514006503403001400204005c0041164021900225001030700d03264400c40318130a03a25919035083d400200100010110304481016102d00b0340640b000062102451a8025000800b950016940070020500a600021a010ba5410a6050300c00740040510040c000c04511042e0512030701d40c2921052503c2500b04200705024083d0340040c80c50f440c50300340e810301c02d031642e100b80d41c15030001341082400700310003000085000c50400c0000c2180c481c030310641c66954003a0001e1000f10b8054028000040108800039000b00241c08100000910301c400f502c0c11400400b152807084c0f40a4101604104030076500f00d00000c3c807882c0100d40c5404039075a48004031818070641140320f03480035400c00401d06000c4603900220b1018000d455050090f00d07500d070201d01100e0540320003881c02e0008482c040d4494403641c060144e00c0d032040101d0b125410410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 202102167 1250 202100917 202100957
    0x40f020d081908090d020d0509120c040f05180601030203070603020309010b101224052e030614030a02090c091908010906140903090f0d081201050103050a15120201 72
    0xc00b0210008030704000340700c100402070055101e4881039000401a401c0013a00180c064015401c1113441080c00d9030700304101200901c4451203e1100500c20004d01000e80e41c180c004080980750808680c060b0b000c0101342020008056068a400900406a20346881d600b240039601c010300c003078025504d40000048075103884e01e603070240d0411600e030100b200020802440407a0405070b14410800d0283c0042c0100d0800701a00c00103440303090f9008a40d1600140320554059614070540710f040107035030480c21043d5410750101040d6028460400c0900e1501003c0582d143d2400750040c1d40080d006001c2340c0040080305c01805400b002600b003840b0022240e181c03402c0c103607142c1d0101944c1c1c1d468566210810019125001070301e441000b4403121070410390714843d03580c050618401d0280c2c1d4080e5064130340f5511044820201e60307110a1a6603548505e0741344850029017842001c0c0400e0070710000c41c030f105100d070050b0b107803450030f0413610701c07a0500e0b003041c0c03c84500c00581c0c00c5c0d05200003407107103c101c44505 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 202103417 1250 202102167 202102207
    0x118020904140609070e0f0f18010f050102100203010518150303040303170106020a0804030303110f0d1a0427080f12090601050a03120e12190303050f040f020d08 71
    0x503400c1e00c0e0b941ca040b07401e00045880c01400c4104020001c405103600c1c0d5588140400c01c50b00a9411040300b4414034081940c20628038464120529144000a401103041d0003100a8070303403e030300351103104540c1140d504c107070b02080c0201741d8000380c01c40a50b40c1010b4010f5925601034036000f10b002c03c3d19806030200341581c0c06a0410b9000555039041c0c42803c04000d030380d00f40109154401030140b004036440e47c042d00d0055010003010140c58105c00b8405400d018192210581e114120a90391100c00c2403402c02080502c404094060000d00b4050f00d03490b240c4140740060f03144122607448601c040c000300075020300c0300208845010060082c850601910f8020b045000c81440c88a0614240118250302c1c22005912243c480c8655130002e000290b0965400c0311860503904002c05100f500708001030072000401c1a4802c0d61080724682050040c415140c0984e050003600c00f00107070340340c0044c008052741742181c001d0400350700c0340050f00050500880c100c0b001401040030354100007488400040213022 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 202104667 1250 202103417 202103441
    0x60308040b09011409010c0b040302010f06120614060105041406040e0f01030c140f0d031b0b07030b03011b051e1206090109051015050c01021b071205060118020904 72
    0x404100d42c001541c000450104a041c1d038007240f410440481d0000b01071000b0f16400800d03000754130004c501014001d4000781d04c00402000305000d080e8444007860500444108250346180c1080d90700014500b101c5a00c50084c1b0043e942c0510b010705105000450a20890744a0b4010904000000d00c084841021300e00901c420001d80e03049503d107060040586240e43c100000a0030090340001141d600e16441d27000040f01070350480742000300c90400f035807082440e078008002c40c181c8441803001c0141216010344100c110381c0b4108107801040d0245800c03208081c6401134800800540d64040c47d0180010b484c45104054048000c115586844c9580e030300603000c01030040b0b902506100103407409900e22805004c0301038003000f2a01e0903a9000503920840e1041111508c281c644003081103125600300c40c1824800c1c40250340d204c00740c84040e0381c240050f104040a5000c0e040c2c01041d407984078016004d040f80c0110050503e039081c510340c0600514210303910040d0a41c200a0011903489a020764032107540 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 202105917 1250 202104667 202104689
    0xc23010f0213081207031409040e010b01030f2c0f0d02210901081504110f07020a0f050a030b062106040c0608011802030924011401030c050d09020406030804 69
    0xa81c07480b8034080c1c0311840c0c003d02c0e42c907001010710360007004071801503440258152900400710030340000a0170303941c8680100c5641050501a0304110000150800301801c3c1c400c1e80c04000c21010141200221044180f4502d960000702440d80b0300c4030440000c401c1d01d0320344042070754846e07056007000f00d2420112104140141c0c00c131200e42c0c0f081201c4c902c0b012001942d001105490581c0c1400000d154000040928961020341c0c0030609040e100c03035000701505100e07104050b031348154104900030300d0340164030120300c81c2c9042d40d408149501c4014001040340d00181c0b84139640307070540d41c841100c1c00009001c59042160715026481210341011481022203284000d04130030b041c1820f0650f00d0020a0b003104040c0300310300300100155401100700040040840c0c40060f200d4031011261410301c40510103442c140060783c2e0551595034403403580d0b0b40c1201c007800c1d52070225554210040d01507a140340e10010119405000640424846800c40c1e00d4440c0300800004a09449076642c440b5a00b29820007513100d5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 202107167 1250 202105917 202105927
    0xc07210b01060305070e0d0c05090a0225020924030604080406030c030b1c0c2c0a050405030d2a050a09050307050d06020a050f030403051908070c23010f02 68
    0x144000080e405007203186420301c8540f6240700090716850400480d14043c2182c0d04800e000d1001009043c5c0103480000c240820350f050a40c0500d000e50081034091014030328101c0700301e24500250110400d01a406400c1d8403c03655101071803d0510152051114041045101c0704000d50f01886024450752082400c682c03a54140240102140c00400e0948185850445000304e0b81c0e42c1d108248184842100c4220038201e924545511703078030696801400c0c10103441095000044030040413001c00719036003600c84043c1c1c0c3c40480d803005075841a10017400c150810807810410302e4483e008508031000c0c40103050b01800d010088103451000141003a80000c0c004502c840c1a2070340114000010401100140700641c2007100044401c81c0d0050010403003580050000b40c2140107400340e540c21500c0c3d50096491386801d0038054040c0d401036141d850003104494080c0d107418024029035003d2075107a070742c20801c1035076503496810752402c0b107034a0550704507244550058140c0c03d0048214000c072545000d6190 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 202108417 1250 202107167 202107173
    0x120102040b1c15090e07080303191b140d0b03030d0b100203070305180f0a0f03030306380c07080a020906010203071a0a1409030a08060303030106090b0c0721 69
    0x2000382c0310504150400a908107281110300e01030059401c00d11001808061010550346070403c940d00101e00b9000100c00c0040c08001122424042028a8030a0080c80042c0b02c0c09840344030000301e0303d0301140d0100c01c402c541130454809000700021541d0700142c60113107940040d1950304003952203401c07030361100000e81040c02c00d418807100149a87c0021800d00c8000e0b500a803460184003450310390b45e04c051092103da9601d2006285442402811804107e038544038030385100389641c00306a000c0fa040400010b0605994003240b0f01c40e2880f130000142c031209039440340407090710040c1e050320844c100707224540c04284140b10f010b000703100d100014042020f66106000340308000508007419500240310500c00300c6c01104011403000b1400c40f139081542e40701420b00000b0300180069030300002c0240104150f000001000703048900064444140c1d95a905040503600d10007406080b0005240c98420031615a0b8440a414980d010f0000d94000c07030b444207040c841d2414550f02c5854140e4001c110702c024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 202109667 1250 202108417 202108447
    0x6120411060301060f0c02040902090709080f06061c0c09020408010b010207090e0d0f0903060510140d030210020f07080307050715090b0f090f0d0503090c0108010311010e120102040b 80
    0x5400382580d6240c1036614240000e000045c15018420501034aa00c0103021503507280d0000600aa00a2480c01c190602840042c0b0701c4085015284d91403280d07030901e100103000051240c0c841c60700100440034290501041c4150100940703030441d5002c02904000c210100c980c0094030150640344000144921407900092602d440741cad100c3c42c80540303000c11a0600e2403000c03c1c595403883c01c034101111542442001120181005d0340083c103420b2034401030100d400d05000b09203040741c0100d90290f03e402c500b80100401080d03a000020b01603800500c1a6094404540180823544c1003480101c1c101203054550303000701d5100301c4a40c400520005141c604100c601200c5400e4450700e40743c00c129030341580c0d403000f00b42c1a000d041c8080445044000a110a0080007002c200070818001c0d40d0b41507145003000307030032a002a1100d03000c41c0100700800809521a6008078101d9400111086000c0780410064540e40302d40d03184035030445c2c0e085a00080e10305003400104010520400c00c1c039a0ac80000044010f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 202110917 1250 202109667 202109693
    0x50a15050402160f02130c091d062b05100c090f03080f070204020c0d0c0b01050102011e1112070906030b090c0a200724050a230405061204 61
    0x1101c1c9105201440381107041500ca00d0140360300010014070380c8920300002c0c80d844d840b0015010b860b400c088200042d1035100340f09200b00c809800c01d07100e001c4500030441041c460104e5034640c000241d079500450200c000b042d400c148000840c10700b0301701c0d020340e11071034209944901c054019507200c041201420750f001d00d09500410a138811555160701f16582c5036401e229410110721000b10209044083d5510313079040310320074590a42222650400c151002d03048484040054801d50a02c0000040715401030140c440f40d1109512000c2416000034081c5005012460105514100074072508810300c002c484039034045c24044c3c4884051500e803078402003c1d20704c5041c641d40255505000d0011030710306203095a5680c1d82c01d0030403584c45000340b1a05240ba100309110002a48100e03031002800140000e00004409480c0140d9402002a050250746511072915090002100110400b0011112420003981c2c1d05102c221903141c29075500000b140b54104c003103400d01031005030f000e001c01c2103a80603480b5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 202112167 1250 202110917 202110919
    0x606181e1d070b070506100302100e0105040f120b07081603090c0f030c0e010909020603070f1103030a0e0606030c0a0509070302070c0b03091516030e0f0f030304030807090e0424050a1505 82
    0x1403001d0304681c0412401c4991000010a0142e4002c5440302fa0b030149041d913002c0c7c8000c0c145980308503a1410004d940044110080d645501c0781c01c0490683e600c91003050b441401008902060303034001403009c07401041016815100000340190104104941076000350082d402510400d0029040590710014042c0680c0310300f14441ca4000c2460040e100e5100381c030341c80f401c10308042c1e0505140c01000e50301020385002480417400004204810351300c0701c1e03004800240750b40e0103c9034a0b9840340c06066596881440f801d51060200104221034074040c14983d43c490440d15005d030a198082d5a03416000d007013a000494940c03000300820407601010010105da5440b4255204250f0400000e03410714080e81c5250070b4101a1a0802003807201c0007086242c65101d080c0f822505403070b8007070810701d442e5001540c3c00c50000700e4220120b18401d120301200d2099802e0140c03d0701c41d0b5103903039607034880d6000c4007a2100c000c0307504010f0b49a910b051501c20b81c3c0c030030302d4200300c0841c81e07855411112172507a116400ca9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 202113417 1250 202112167 202112191
    0x6021e070c060f020c04090b071d090604020a1b0308040b0f240402040f08071409151903051c0f021b0f0d0b040606181e1d070b070506 59
    0x1440100e100072012000320365003401c21020081640208030b0420b80d404001c1904941840707030b241d040040d00106d9900c100103d03521405d555000441001c8000002014550b03c00000b60118489260a6004080f606014106803030942840480d40400e4520598242c0c0801d0059003003106100c1c0300e1041c00da1003081c1450803142450a01282c07202c200315001c0a0025140d00303007400c10b00d602c60b58120381c05001c0d4069960405541c8400559540b412402040e84015146c0841c2c4040d00301000c40500038035182c403c03030650740c48150901c07000d00b02c01d0a600856070a214400004648280503480100c0c42961840c030702d8401c488009404101034100340800c561211360655601c0403042c40a0000340340c00c070350300030808550a000030140e07644080054282c002d1038007804100300f076507444201180d0001c481da0500c006405068003c407940905040b8001c080c800c0b0403107180044e070744200c5404110140c0111400380100c0b0091811609070400c41000b41c000400c2c1003882020001e00707074402004104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 202114667 1250 202113417 202113427
    0x4060c080609040f05030c0703060b040e0a05070b0d0f020a0f030e0705030a14010912020601031403040f060e0301110307170f010503070b030a24030605060f0901050d1403030406021e 80
    0x8691a00d800030405408078116941391420002e0520444e0203502c0150122640d20307480f4100880202000c0e28043e00c11490081581d04105010400e180d0340c0d9000005404002e19003800680180d00c140c5103102115175036480b00300701d09103d2001e002041030307583e1614000714080401504968030b400d0000c0e242d41c13009034100300a9a00040701d1204952003031060651190030081503016040130140205001d4107148059070581e03000800d81c0c1280d0080000311404105842c7c600d80b240b06070b000d42c40340c51505990601485005484c0c01307030421405000000c107101d0b032a4248025420a031683c500190014100b040310f0b003e0b0180c6960411000074080344554034040c0001c1c3e844001c0d10904400c4030300800003820715034480e800106110444080007491800c1d01d500410101c0300c6000841b52280f600011404a0610354003c07829440060040c1d0702990a2100300039011030110030881c3d50140300c0320340c000d0700041400070f036004a1017840c0258031071000701d06040d48026041c0755002d184500b884 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 202115917 1250 202114667 202114669
    0xb01080714030105012006040f020a0f0e1303050c01090b101e060e19030503090114090f0111190812090f0a0b130b07020d030b0102010b13180b090604060c0806 70
    0x812a81104c0342403d016600b4441d18107a40c2d81201c03140203075a00390103013404000520a000d030080c00c095200311001d000b01d9841d5100c03029898024090307612011740110000760951444001c0190107402420290700340450b0310b0b03c45003500e0810500b20b89010014042c40300000508203c103018003607203c4040c0490729684040c1e00c421120384205410004085e06203d07103030f111240b4400f5421a09000154520f0300c03410701c0c0b6a40e5000907100c50000d8800e141a05109041c1c0d02030302d80c0407030028042c4c1c1c041700d0309900444000b1500f03a14481d5a024105001180780319001e2101e10051080460940781c6603200c8860048010061403044541c01200d146d800c8884040382e00c8150950001851481c1d4a801008100c4d0102045004103503000010903c40000d40018080b0241881d5541c04e114054011004a0980e000c0104541d0040c1414180c802c8001c9241c00401e01d021042c540c80031216265120b078107104605582daa0f20a401c200c1c180000d109150241d12031405039801e1103035160506174 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 202117167 1250 202115917 202115957
    0x1a060a0804060f06030506130506070801031211010f020c06041406070207090f0b0607051005090d0e060d0e01091b050613030f0c03050d0203121b0715060b04090b010807 74
    0xc1c03008041c00d03503e6464450522540d0b0104000e5500304048070010710708035032810700f8000d004c1030540d0544641000128101e1081070780c64142c1380d105200c2e4040644070b5500360355100c0b035624261501c1d5210940191450014405001c0c1880600014072860030302e400c0045490340c0b41055862542c12030f008000826800140c00340c101c640c00d08001a031183d6a00c0e84000500e0601c0400b64050000a50f40c414028002090300381c015250000b0003068071741c0007066581d03000044546010074860040c1140074544100a8143e10007164000b0954501c480311607400c4401c0104201c4140c2d04c600f0410b003104071380001e03081c0500320a9072001d01d0300c80011001c3d020030b00e40d0b03c00203003d550400144010055503541a400540d80a0203c4203044a0103030069140d41105c1540d000024440c0c1c00039544500402480d003040309000061883c00d80c0301d444108505105035024141e142c3c580400080319581036004100903c180140010407881e002e00061a14030060b01100c00c01425809d0818120740c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 202118417 1250 202117167 202117171
    0xc0e090d12060803044104090228182c0a0512030108010f060506070b100e040302010501060807020c0a090b0d080c0f07051005070605100b0d1a060a08 66
    0x7401d10560300201c8100640140000b41c2221441c0d00001c600010012070f599400100407a40d950855500980f02e2114042c0b4400c1400f0f4550355880f14203c0e4485041652050a0060002e4030750091004c1c40308040c03907035034842a002c00c1050041c1104001140f04c610200310765805090080c805d444000d10380000b004440314030041c41114075025004d59820422042030000d81c0201518840e20070900c100d082a0024440d603880d135400c01c095086103151600c05c480585100400903400c019540d02c42169484004180c00d0040852513404540542c1c1400e062344501d110f07a0000c03c1c0e560601340010301c003100c040c202c0c20940d88040d05000d8107a441e02000d105171200d0140009204030b215000030051220210041c100b10800121b59006800100e5030100744c88103201103030f8080343d82d00288005801c4105505000580030b1003640c00080690300255080710790070310b0402100b520385034007000320b6201c40d218000b40c1d6980c1c0d280f8860100d00c140108003640d400c40300d40e0705004001d040a4440100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 202119667 1250 202118417 202118443
    0x30a020d05131d01060909060501051b19050a031d0609010c031b060605030705010c031d030c1e040c050306180a110f03042604090216020303160c0e09 66
    0x404100c012480858181000081589a07088020384218400c07803c1089020f00508000800360040880e040e0031030300136501182c8040c0c0d03546141c01e44489200d203086411200c00080b9000345100410070980d0540b110705010300540152071203080c079140c00340410144456860001042c4030b078800d202c0d90342d9401d45101850a003084021081503103400c5603408480c14921118042070717400e01050000c20780c000c0382910026400c89800075102d01c01036880c0c2d140380c40c0040c005038000b0b60500c400780003049030074001d0802800b250312055a41001521010f110803d0a80d00f56480000510500e814060100020300d2070078030a00e582410000710f00380d0101070154603480d402d2500480c568016950102c900d486c0300f00310140d1212055070400c5a103074170031742c2e0035a583c103c0388441c03801b18850084143c10402c24003407090b203001d00d081c48620180d0401c1c034180c80d81181e000c1c203290168400b440188541e10494045441c8101c0520307104245000302d4000c0707410800394500f0002881c000055000910f18 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 202120917 1250 202119667 202119677
    0x60d02030405011410030204050a02090a150905040204031a0609010825080703030302030106020d0203040f03140c1f031404020a03020433170a031d06042411030a020d 73
    0x1840b070402e03901402c0d082018400d801096810000a1300d50740800400b5244229800d100c991501d40c90701e400d902844032015404841d62108125221040c10109040100c1e800c100400b10390b1080068205d0304964000c1c0c5007420304089100d0407900504002e580b101c3d080325134002035410215400e40d0f0f401414500030468131008102041403000e410f5030401400030f0402c44042c0342d01c920700180070b0341085c880c180251182d1900e031104180007100340d409840101c04407030074a40c41c640b035040d01c80c405401c55407a40d0013100f07030200c41916191010703d1050440c3c5c1c030140d005100c180f0f0040480e0700c20400032044580060034071005a4648207440308907034040b5004038400d17610881c104140070b081c21107110310807840b40c1c004039103079040403840c000c94150100c038040c5003908411503500c0c0d03401294000c00090904160381c80944001800042815028001e10b00705501c4100b01105281001c0d0f025141e100f900f03111601c00c82c1e0080030380a80c0c2c03101802940c00c254041c24041d50f40d0a51045800c2402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 202122167 1250 202120917 202120921
    0x8030a0306120f1b030f14160803030c030406060504050405070302030f0a0206071b12060506040507050306100f021c0201060317040b1b010207021e0102070806011a1c0903022505060d0203 82
    0x104400804001d075070026104a030040c0c1618081c00004001c581034030660141c501c01c00100823040c403008084401e080060740c610b0f46c860f48030001c00c1d40300034804c4070000e0395200d0114550310380e4891548182d00c1100100030041c1035004040c80c25459a1003081079901400f61200140c60b0141518005503211001d0105490040224031817584280c015019440c00d03e0b03980014020140c0029002d6a015a810000c03520341c258100c8551004680868001d0040c9410301c1e0114800c0384e1081c0b01c80480e10545180c035040d072103480600075250383c90708010707074503540b0034414880c07140d441c81003103c18024142e00d8545000c1000b8918000c03120500e0200084040d03100c5010000e404031812558010070380d5003044840914804007119422b41c99006110315440410b9400380007d889050b2000c80c0c2c01807072802801c0a40d0815581300c001500700341040034446003100041c41c000c140c50548242c014009500b020500044004c5406070003420346c1858103030030001920703518115200c0ca042241c0160741c907 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 202123417 1250 202122167 202122203
    0x20c0709090218040305180d02090c070c051005040e0916060522090204030b070e010801120203030906180907140304060f0b032b0e03060f1e0108030a0306120f 70
    0x810843c103030008082019104001c101030384030004180c502c1882100a10b082c0d403000903c007010119801c029000f41c0d116002c02d10003001e040250200911170800003100c103031502c01080001c11038503101e002203030021505004001c907402480d944254241d0003800c0101c0030034000440e141d13080c8102d10502800040c010b035030203034216070400300c10240c42d84031190036502c0c2140c1009520034071040e101d4141400104070600e01c01c01e25200c0c1440c0594401c0c249900f0094030f200c141c8801501264907200402080002c0c0d1118009407807406210b0704402000e40071036052101c0e100c2c00902603810021056201d10410411109507900203400441c0084c1c08040480541c000b8041113500302c0d4184250740040d40342c03211103c015100d00003a001c40b14207051a07207600f6601207640590701607040d0002d42c001080040e009400035803000104111251901084100d0f0003202c00c02e80000c0c005410020ba100142034041c003480d00101200d0842e00a4411b4a8481c41400a07450310000e252001e83c64460800e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 202124667 1250 202123417 202123429
    0x30a062c0109021f020319050d14130803060a0e0a060609060203030c0a0e010509030102122e0b0a1b0b012103020c09061302120103020a0906060504030308040c030c03050a02040f020c07090902 84
    0x503020b203114070a50500442001419540110680040d2700c4e0400c05110040c0c45440c0e182c0380600717080c0e08890235101c42e956840e142504000d11581d000001008001080e925215695010f0300031345030000ba01d5401d0000081000000d600800305562040043c400966804002c50344005c10601d00701000c100454012141441810440d550560010400a07502103806420030b02a4000c642c00c491001e0040d404282c840303210358035421382640d0080c03040004c04440030041c1440d105500d409c0e10899030754071200028081d415400e0f01e04400510050103040ca40203841104010208059800e03000c0c00c0da03000390b81d2104070440500072070548010030829150440200e5a0002022082d0b44941d030465082074000c45c2448168891010345500240c003401510500b015606555a15880c203825174a080e20b00140152040b680f41e00190400004242d00d0b40d2380001451064020300450744050040009a902c4030001e4216a4410032807152076a00010700401100d044100124000e0514000192 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 202125917 1250 202124667 202124677
    0x170c0a0b0403021501080106140f0612010e01030611121f090c02030a0206130b040813030f11040c09080601060f090806130c090e030301060806030a062c0109021f0203 73
    0x106420412007408101070300815607658035141d80180c0400d0f0b03aa0b401d00207080c0e4815110707607640307110b030000045085d080c0f01c2070094000714041d20f10703440d14180700030f0080c042100346d00002a0310310a00050040141d01d01a01e001a01c1180c0c01a0402d450100415801c000151110100224074624090f0184144e01104001c115501040081c202844400f030b403607a010300841d50060188400084402c0300f550841e204154200b5404d0f035070742d0b41c0c40e80e858a60750300c202c0a00c2c0601c80070180020004000c41d030741030401441f4880394012a40000c003480251010784440d0310611428a0003804030400005200703045810a1800040100080e5002e41d01003c0c6500030350441d00600081143c8088526000d0003058400e80c0120300e800e6603049024101c2e00c058281d80041c0d0020001000460300c5105074a4001c1001001e4544185250340c40b40219089045441c0307400e03548a8001c08104592007048500740100740003805110075075800140f400d0005054000741e51986504041c0551081003610 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 202127167 1250 202125917 202125923
    0x70b130b090103093c05070303051b1b010e0616061802060d060509180309150408030c0703031215050915030d0816110309040c0e06040611010612170c0a 67
    0x420441c41000801c004065a0070a1a030200c0c4c145048480506035400304c501751034000700541500c2c0e04554040381c959218036150701140c1844690903900140500c01040120300d124240d544203201e00700098105c40c4003403405840b40c0d000340304024a211101c40c07007582041d440500020b40d0000d004d0f014000c0c9101f000c01a42085000c904072941d22010f81c070190544a0403100c0400c0c1d40d85007402d40c180000150044049a0014000c2e244a03091406003200340030503110302035040039100c0f0300091464100082031030b165404500c040052542145001e07010000022040c019910164101c45003404140b041c94021510400064103410400c5507149032804002d050700d07101009c0c144001c05601d02944c5040c4c110710080840141c207070180705104003001090000c1c5050584240c01c000040c000012903a00b4481c002d285161706594100080000e0511500c421a001c0f02503015642180d0041d080749010b4000d080014002c208100510241851a1080e0950b1146c004207040d0801b040f4510003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 202128417 1250 202127167 202127183
    0x120b13020f0414031c0e03070504050405100605030106081b15030f0121171b0118150b211006091d0703020a2d090e070b130b09010309 59
    0x18540c1c04070303103000400c02c480c1100010800c050101d01015280d06420078106184004040210502401a8200d8084180007020368048075034a40c003003402d030b400880d8103c541e0740001c84d01ca12040c1d101c3c0701d00c5000d008160000c1181c00c1c103001e00c059581200307248840e02d4015108040b02180d454008002c0b0324102c8a050075204d04001161a00d50380c0203005107025010440c081e00319505d6204e81d00161540c001e0014203200496400058165000e1950151010060204554412801d01814880c0c40103c410000c005c40c0d103080c0081e8000010584c2c070700700360400b003882d68141c0e038410403840e1840306101d0584d94401d540f003009141c0b1103607070b007201a01c90521900240c42040c940c4210580d55000307800900141044080507100c0301107010095008490321000e1105a22244211150032030a21315080c0c81501e29407102d070b003042d4685c40400016212031b2070401e41c80d010303c08400109000108642000c40704106050036a0480c09110030050010503400c1490780f194002d000711607084401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 202129667 1250 202128417 202128427
    0x30904060f05030d23070515163b06130305010207060f02120c0a12150305071502030703050901030f09110a080f0309280803030f0105060a120b1302 65
    0x180604900746204075031003802022412130b14030313028800000b4181c0c0d4100c004071307101c540100040d0310f07034000d04420b03583e6204d4110541c2a0610001025000f00c10440012a0713202078807000802021360700207080014607101c2c07840e109034042c407072401c50542c46d0000801144a41040450014003e0400750000c840000000005015065004118060140e135080c0942d500e50b0b2410701c180d100b03541c024651003031076600080c0c4184c60b0f14050081440b01786040b0100592903135901341680d0782c1412040100091035800c00421804115500040100542c00c00f240c41540170069128012081c0c06420f019001401c02070a0303219a00c030703d10030010385504104141a03410301c800211b001006080c02000309a20111703203480002030100f0184000c0008501d05802681400005000790414001c100c01401d450380c03040080e041800d019180605c01141c583c606120900d82c210010791100d40140710410008149030340c0800003850400040d100460354020301000300b40a0030686135416401840414 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 202130917 1250 202129667 202129679
    0xf0d050f03040f1406040308030a050c0f070503030105100201050106140a05190509010e0402130501030b0a0302040203010806150d0b0406020307170a0b0a0806070917010f0504060b04050f040201050f0c03090406 92
    0x8222040c3d0b81140c040f090440d544c0c8080c00070611507400041c201601c02d02c0000c05840854100135446407084ca000342c00d006410009003243d4201900c206c40315000400140306074104503280c0072160340588001c0c0055450188090141100d07a49520003a07540040c1c90082c4074011011140b03214145580c10b01d484a005a0040240e08013180050000c0c2a10750800b4652809009032135031448200740c0d5806242c81d00c1e00550040102000d02c0e03411a10150000015a40d640f01860007014107201501c2c035880c10004001d0717141c003c030410314031a0321480489404511250801c50b0702c260300410050382e0381c69103002a00ca08c0001c8803c00c201c070107000304120030520030381c01038005110b0540381903039941e4030f454405480307070b90071a880750009038102e00c1040510301c042c090038010038a400c000541054650340d9103042e01d02c21a0241d6007252202011041d070f040070310803e42e100c0b025203c800d0031410030380e00082852040750b801c003413401804200e80d1030741801802141d00d40e810080007041550b903920 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 202132167 1250 202130917 202130939
    0x60b0d050f0c072a15170403020303011401020f0d03090309120b150f03070605090102010c0e1318081809010501052a070e1819030e100504050603090601030b060f0f0d050f0304 77
    0x1140781c0c000103906e205114500b604800d5064011503043d000380d400d6030300b40b203034032550641d6205c440c0c1c2c11803140f00c14907500e5030020721181491420a540129070000a800d000d402404154000d000080ca000c000e00003140344c0504243e000300c030703040c1c10b0b08030114280c0028102d00321100710140e05006107103000803160742083c01004203d03800e0f0001e22070310b950404155841c0789921400d41c0c20090301d04208011142a510074520008205502680701110351120b114581112807440140d2015007580c200a10304414400c0c010002480c04908d408200c03003440c0c002c021303d06140500514102e038025407074003060000001425080e0700403152850001c84640c181035400741100001e000300c52100c581c01088010340d034543da8043e2180e185606200050240c202e0149103001e0800c5024800403c0d10359a02c0000c43c0502001c82c000d01141d411030411402c2d56001030500c074498140c07204003403e2901c0712844e80c0c130350090032920314940d041e00741815403c24070b144e003908149000006d0040384802c088 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 202133417 1250 202132167 202132199
    0x80d0305150607020108040b07031e020d32060f030f010902040c0c050703170d09080d0e010b010905060f1b03120c0301051f0c020301060b0d050f0c072a 67
    0x1451032400c101e01d100091015a02c036400303001c2c0c002060840024041265101400c0d000403140c0f4001034000300200391700720319801c03001080010315000100b00460503a40d02800c40765240402c9201030104280b640307000d421480701c040c171000c00000b90002d017040e5148030030f0f180d2003000036003904c007440f8100010354000c05035804124030a51400c00c40303010641c400e10340d24a81d00d80c424024003c1c94295100c104040506d000031603024102081080140c42032401121422403084c20055103e8050b401000f0075901003540030b640d00d0b850148640b1090f84c7c481d20700c2c01211001d03646107590710500c0d0000380080c030580d00d500034400401c00361601444c6e000001030442803110700d4a10100d807035000c00070705688420b100d09640040d4030300302c4000c900c411140b0001d0320b40c000d0500c101e0040c010703404a401c3d00d00c00d034010035140002046117030811280703011303c940c0000398014008252800007460b40c414002d55070040c00e0580702d1007000c00401040400001d03114800c8080c141d04039038980da80800c642003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 202134667 1250 202133417 202133431
    0x250302040501080309010207030305071b030b0103200915060405041104080d081902031e070203210103053301140a08030a0c12020a081216090b070201050d06080d0305 73
    0x40d00e07000052031070012064440075007050380985102072070341c2c8044542d0741020106032500ca0068110750205403d4030f506600841c41141040d80940c95410200ca5501c4914002e030090b000303142500030742c4d554411420b5032021132034880f04200450400840c1107406150000c6801500c2c10590f4a04100c2841c0030340210b43c602412500c81c8881c0c040e048480960541e010040c03c101c82000301e1054000d600070315801070b442400c5c0200c0b48904070216030400030503104040940c1000490005001140320701d689603101c0b00000c201e4039407465a845030350b800705800f0030001160086e40790868488000610846101d200c0d044503041d6140e400d0b0408042ca14820184140d26041c400204c000010055032200403060b114000000a591034084810240e10081e038210302659002000055460028240c0307a4401850b80700719180c074084418001c50350407215010321011810801415540c04102d420440c3d080c6003043d19040b40903202c40c00b5006c59040026a8043d050010000d90342c194030551003081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 202135917 1250 202134667 202134671
    0x70b07111608010603120f0c081810080907150203040e1803070606080106120809040c0e03010905010207060506010513031202071d0f010911070303020304020d050304030309060f08010b040e060325030204 89
    0xf11b020b0040d5420340150385203030017040f01d62482c0300104080c030004d0141142c843e00040540d030000030000d840055110702ca0004200c900044c042d030502d042040d4070180c48841405900d41c0002c91003e981c1c3d0041d0310400481d07159400008504101c1213495110078a407001c1101e445004a00d4004081c0c03003680a1079049610b4204000380c0302e1501c0c6007401c584c0f604030a00300d1804079044181302c054200f005280040c40000204080c154400744682c082c1580207400040e00c1d9134617440c000b001e803030020700035604010091086c0396604400b160308134212544250810382101c50510140e0030001180e002203071400030f001009803445240d007492841001190001840c07030303032106d00e400c0450f41085002610b0703007010300c603580019001364011134020303000500d074841d2500b0a94030186194059041240000c0000c1c2c020440070740c1042c100b041004060901c81150b6050441c90b1046003d10300c5114942d25000000c00c035161014068074044691560916500d80700000400034000c1080c031040380118 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 202137167 1250 202135917 202135943
    0x903040303020d180603021803190507050603011a0a17010b0a081003030e0d020a09020d0b01080a1a040b010c051204050111030403120302030415060f0501080a02070b07111608010603 80
    0x1610404851904510507492281c0840c18010128000e42141e0502d1441d10a0b0100300019540c0400c12b0040000c5035a6100107064020303c4c0042c1020900d600c941d00034041840140508810b0803901604568000c3c0003940760b02007184103d500126850010f02507181050001c1803c0c034000004024011864940e0340c183d8070343d19910018100f0522018000030400b044481d22031a00289129580f07000038003014040b07860b100110100d0344072081010101d85e0301c44c4598020b503001444503500944816007040302c034440340d01c0d031145c0031100f03807005124076a00d01019105a028007840b281c1950001e08880105c029071f40c3c2000c20745d00070300801d80454403400012542c038000004481c250780e030003401c9000c40d2140780c07400e8000c2c3d000a00300300c44411400c641040006828070a04000340001040b00b1503641c5818000b418848000e0b29a6039254010460300c8013003281da005890300152140351020f4082030800c0c0460401520440d0014032020b44040014103000540001003500d0090114000407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 202138417 1250 202137167 202137193
    0x201110609070303030e010b090a02070302070503070e0406020d09150501170d050f0d0b0d03090515070809010e0f030a2102062a070c03030309141b04020f070605090304030302 77
    0x26401200e229981e90b111201c1440000e120341c01200c2840d40c82000490700c03404100010312206001c0b5100e02503285e022a034401815810400340b8000d203402d5001d400305d03500b00400650924002000504113540004812000300c42d40e42c440041e26400c601070108503014440d01741c0141c074082c490b40c1c910008000340b1076034034600484c2ca00921407803a1510303032510001d000000f02d0351700560003117102c2507036550903c0402d40711200aa80c52604ca6911000c0082c2000200b1501f030b07030303404080401e1a10902045000500c0c8404a070b041d003000f406c181e040002030500260100e00c61080301605809003403007000c200001040d00020201240f90005100303407144100320707a6070b00b040b9512000303402020901c44c403440503252444005018001080c3c80c00030380c1d40342e032000baa12560040300002d503624140020b04c103661201800d0f000094015000d554944161845840c1e0901c4000c0e00c219030000303040c0f540e00c1c010802c607184140d02001c203100d03d160126140740c4a400510064000d40a49500ca03c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 202139667 1250 202138417 202138423
    0x1d060a0e01080a0212070506030f0403090b0403030f0c0f02120a06050a0b0d030c110607080417010e0d18050a0f180e1c11100c0e090c0a1b0b01090207020111 69
    0x60341c64542c000c0c0902da4950302006610015092661a24004c0850114031521610025481070000c1550a09503007800d1600a1400c20241d2011054010511050000951160702a21900814640160a80500d00302594610950340c0000e5001c0681c1c000c05150f5040441c1200b00c40303000c5d00040000d5510b1a402006540352120410350000e1613114041c0042e004000003004203002d80c14422040780c3c118085607003a809000c040c0c0d00f82c0000303d8104000340c0306000040031102107030000d1115241c03101d14150745560340e0403904140100050000c0c1907504404040c0c006090051001c54080c0d40c032641c0c402c09500381d0080c070b07c01032111054807400d9101ca005040034071804078024084078201017421a01c0d00d1800e40d20508000303204c055518070360400c12450b560124003440c00505490b800d400604020145003003680540310000801401795003500c00d40b1100c0d21103040c00c0443c4007894000726000d15102c00001c0141d1134000020841040c00d0303026040ba103100b03803640200c40d81071204181d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 202140917 1250 202139667 202139669
    0xf0c0c1f02161d090307060e070509070e0d0b1807030623040b0a091e060c080106030e1203041103030f030712020f0d0b010302040f0602060603010c030e061308041d060a0e01 76
    0x1603140383d0030040d08400c0242e0000c06034070085140a50381401c6099480c0b405840820f0007800d440d900c03600040c000c80c0780c545403607900040d40e0b041c299501d540450100b0005c2c8490130001c0c261000c2580000c40c80001c8180a81144c2180029184156168074000000b0010340c484640400d0390600c2d404010851208028050340c0c100b03100941c547d8a446084001d01156841152417a0b111100e20400130b4207140c0b9105051300c5508007241c0c0c49143c0400410340101680640105030809c4503a0950039004200e07504516600d00780309999903503604000d010b40c6070f03c0203140d41500c400149580c0d0070b41028007944c014200c03655031008846072081640282c0c010300ca80480e1451040041c07410050050740488207407901810b01504003991020385000e002107a622442c05038000d801044500e107002e200c2e141c0d84088070b050411240510240542d13039804001c0808450040c402248810302c440394060706e00400c1800ca41004040c0c51400d050107200d01550f220340140200c0d000824400501d50b8954 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 202142167 1250 202140917 202140929
    0x30b0702121204031202030114040c030c0c030c020f0604080304080106050d021302030a0905010c030f051e010b0f0403061d011508030d09080d050106020f0d02120f0c0c1f0216 77
    0x14140b560107810200307000000391044040c025a0117507640b2044035800614028480018103c01e035403918010b01041d291480b01c0441014504000c103040c558206210352201034251030807801320801d52010500880d0148007050703002e100464001803012001000300300341e4000200a224455555040c0008070400802c02580701505d010b540c4004e000b99409541e02641c0c0260120b140041501e0700307401c454034004541d001a890340038580045196000b5940c201924209800c8c418100350201c541e60300c07040c0101d495460000480e0401d940707100094134091034000104203c90051055504044c10307a180c400300c915400c0040c4400c20902d83d55145084582030006585004800c4044c0001400d543c807089410303000c1407003160340d2102244101c6000c0c0816400504880d40c01e103138101e18001c0741c0b8400c2800c551000300fa0a115901940503030b40a803010140268540180404060810b04030341b05040d0030036013200d9440c49035481d100034007030155002d8003558114003141545041801581c0286 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 202143417 1250 202142167 202142203
    0x103201b0f0601090e0307060903050c0c09010e060108070c05030c0a15020304050706031509110a0305010e191a100c14280f020306100302030c040605100f020c030f010501030b0702 79
    0x420144020350001080c101171401500d2038803801e5a280d9048074041002a0001103000c41c511715046000c11a40e40f41c04000c8504c000d403907140c0001c0301d100040c002c004504100990303000c04c82060184420004136580042980d03100c80b0003c080302d81d03514036184c0035a4240e01c48490079900c2c81c0648200c0780a00d800401030f0262505120055024055494281c1044a0329000000341c0216610818046002080d621580c0e01c0344042c1c001d091f0742c8107800450f0186850000c0c0003000200d15102c03912810b00c040007296070411401704103903555503090043c2e0000d241d40c40401c0714030341c4030500706500d5106a0180e5241e85400442c6540d592621300a1488540500d9202c00b565041242011030103100c0d12940d803e282c240d9010a09111050303804091002c1c40c01070900440c50180820001540141c0d000c00c03110f4507002c002410081003a82900500500c6022403501e113100b48140624032401408540c21190003424850003480c09100c00c1e212030101001080385184041400c00e6103400040103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 202144667 1250 202143417 202143419
    0x30604050903090a080106051002070f03060b0a03080307030902011106011a0c070308040f2c0a0207140f0d1106040206340f05010c030b0a140103201b0f0601 69
    0x5020040001034036020103844144a4000310741d4509921070040c10a0100220380c05241406001281c00c0d510003150a541142c0e000340446841c3c00403d00c2202e03082100480c03d08082008540c1d2804545c2014100e600c0004c03c001c21290150090030006200703a8841e411018091401a00c07010300380690050301000401d04a6141000310140040c0c0301400705545032656241d656050603401a44090080320500d1020407125100c03410000008001040c28089002c2c0d031202182c000c14010300ca2551583e020440310103018000c4400b80464000e0000c0762040303103000600d40c2c0d0f00d1545510070b178001444180301f5400301102042c600d015a501400305406d01c030076810180c00c0c0cc041c03158005000e0660750100c1440d08400c0554402084c00f0301800b0340c4040e580d042c050f0a4895511080e0181820070003840ca2a07114103115008a030045200c0154403007003400100d029240304d00c01c0340030034010030310041e02d0503c01c840140010440340120002c03042424400d69242c003803080210410b0b41242e00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 202145917 1250 202144667 202144669
    0xc31050f0103050f070c0317011413110a03050c0c06100512010608030f09190b120702030c0601050103180209041103150f04060911130507080c0f0409020c03071703060f150306 77
    0x80480c6d0443c840c4c240b440f01d0288103c08000400700981c40140320b10703001e625020113400d010401d003004031035901c82032117610700c044d5480c02e252050703403000402c05a81d10b0010720321400300019a00301882c640141c03401e034108031104a05429481c01081d05c10f0360012102c2040d03080500ca407400300d80d4080c014504103045040e014109401c25507070690482d1684010511484420b030b080320280601e18140758881c41d92400c9a00c80c941c0c010040340a552080280c41454400040c0150444400f480c001c50030307800e4015544440181088025005074040e002e0204020203100c54040c0e08000307800b1180800381912107503a0f80003040e80c0c0d0310140394080c404100815000e80048001a000d0b08005d031000c0f9061000c562400030541801081580e1481840200d80e4406800d9801c1000b4408190a240720000c040050b07101d1849140e00080e400510301d00454024415210025040554884c241880c09004422503000300c038007078499171041c01d4403000c41c82c2c020f0512201103c0e01135041e04558840e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 202147167 1250 202145917 202145927
    0x20d0f02040b030703080a120c0e090a0f06081f05010e0a0504061104031109090d0f051e0406120b01080408030412020c031603050f070e0c31050f0103050f07 69
    0x480140d8000707858080740e0788561402c01c010070056101d106090381e12541c1080040c4000c409124054a85007080c0c2c0e09000944c0c001088880450100d505800740d0f150702c4480002440340d10b003070203119420450f0000340d1075008181c2d021500070103007995689000c2240401c0445109000e44c034400c1c01da440124165141d1031748640e074001d01c204800211440c1c8111204c1658001e51300c01c44a4040000c84100b640c10701c04240e6400680000003004080d1454202404072840000c00004109003c070305000051078403880070100045081143d40d4554403000000c0c501a86103158400507420480c2460315075100b003004c40d1040d03410044042c150b4445c0d946003015503482a0200c003c51050303010743c400981e01405204440901903012030695840c500c0d1480c200464410142d100d900103200c20000c200440d454190f0186660580036500d0b80e6a40443c5104024201613807080d102a40c85445841100ea00e01003c0c1d440403030340c400c8110550401101030b200704a901c80c501c0c0d0890408540b103e4003030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 202148417 1250 202147167 202147193
    0x30a1b03050408120306040e0a1515090501080c0307170606060d0e07060513050414060103090201171317030603120c01090206070507050901061805010815040e0607020712020d 77
    0x19150403442c15036180310207031414031440d5581c40c0c1a08008140101450940700305110b200303204000c0c040c1c80e03995859107001034100d085280002034484880c44a2840304000100207401c0c03000c0204801d5840303800169868011003012030191143c40d8000c9050760405d03500c44842c0c134aa0340101280c1d03035600e081c083d45402102020041a032100e19130001d040e0140844c40240545e0f0fa0b50f6074491020203038101200c2407581c800c41c0290320f0207200d102d808030390226140e40f01c00282008224100544012240d0760300e80700800d120040c1017014012503a03850700c200901180103810100d00c1c041d18000c001d140784400d5845941c16030050350601c055100703080107080100d52480000440000c2600030480941c400b510460300d80d040304406105906e0043c0216004d04014035000001012101d011489103507203005450501035800006039180d42c140d50040701015010b04240088480840f01c2c0c0e640e11803d0b00c914015010b68075012510400f03000300d003051590000c0c00c2d10209825501c03030980780455 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 202149667 1250 202148417 202148423
    0x30d1803082107020a03180503060c13030b18070e2a0f0f04031202030a0512091c030506010206060603070f0e0d06060b220b03010e060f03010e010b01020c03030a1b 72
    0xd5848500103007120b02486841940640c015000424031850000d01d100061302c0504010f20f0103050038880c58a0004241e54040000111695134005a128213941030000b5400100480d8200003000400004601e400c1c0e081100d4800302c40340141c036150104c120300003c440780c200f02019002c0f10107603081180041181003541900c0c061918850424030019030f4081395107442501000681013040010360190b2105503221031014500740201440d0052161040c030021004082402d004500302503014400d2800d881110103002506040c00700b40038002e04000c98440740980640b100142c05030820700c1c02c50b8498bc00b241d8429100700c1c0003150540340c0c041d800c0d25498101071010f4032040001c0303c600c22030b0068848090b015444002c07464030b1802180408800100b0000c480400700032881c0b594054906482c1e0042d1780c01c0c5179648050100ba101071001c10043d90560074180c0407822020b042d44041036000c2d00307030b0036111100c504400b41503492080d00300070000210403031101001c42c0140c8130000c440030301c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 202150917 1250 202149667 202149697
    0x308041506030506090f060109060b040510050c030a09171b010f030b0913120903080d0b040212010f0906080c03030304110a03080309060a0518060105090601170a0605030d180308 78
    0x3841c1d48a41e40f41000c100c0d10b6641d07586c090321054110304420001c003401030400b0542409018100303015207070b090007148629805074031004200b806007070055041c1d900100c501d00480351600c0d50001300501d031501f640b0940d030030180d0030200392031804008200340c0300180d91211112050310071b030307401100c0c4442203d142c0010183e81d0101c035081c42c1d45683c0c10f2401408078103001440d816003410710203030a4800820b02c00034860440420000645d076201900c42007880e4110008000c12140003140c00792141d1180c0b000e402c0b501c0000861121214041041a11704d240000c20000313441f4400559601c0022004580c168000c0c000500041c0e10100c040b0348414028101440499996540c0101e40d002510307030a0681e0821400c1000c4e0908078401e07075520020326621103e40d64040b1752070a40350441800340c80d020700c01c10350014400341d00582421002000329031041d200361030080c00e2200100708070b0144a102c5d02524041c2c0301818410741034a0f0099603e034911400d85450b5a554a105070301c800bc200041003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 202152167 1250 202150917 202150919
    0x10b091b07020d05060906101a070c05091003030206090a08030f0c160f0308071b0b0a06080a0f11010c3305070c0b010b031009020c0a060507050406090f030308041506 73
    0x18851245032007409210b0801050f40d41006c1070300b07a04250f402018a00c684c0a01801040301221003407050b054201105071803a0743c0c1081d42800d600d800c040c1c0e000250407582580910008000041d030140031079001c3d50945840352210481c43d030b1208034601c00a080b83d14280007080c0b81c03c0241c5086600550b803454202d1400804e44e210030000d05260744141c405880001244c0141500580000e03406a01031500c100c0c03228411070444241a880074010b000d0300c0c00c2d140003e4140d1101e0b844203024148160442d41410400e00d81000da00e00080c004490700c040c86143caa42a5002d0441603141a600c100700381c9240445070385040e0036140c80c0360382c9400c07404030320035640903117407540300b090300030102550384588500352414419101d800c10307400b030000030f84d04100f00510a226081e01d24160b4a64680150365540301c405505c1c6000c40c4258042d040c02c3c600380038004d4007500f02e03006204a850319192100815540e4042e80800d0300284000382c04940f9080000300041c0e680f6008106452603c0800107c2d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 202153417 1250 202152167 202152169
    0x30e030c0d1205104704080c090907031401090b04140d080402030d030c0909020414130903090b09061306030605210a0b250306050f03010b091b0702 65
    0x444444070380c03404980c0101c8a20108009800f40c1c0c0d5000c1c00c001029007010340351408808103100b00d4140c40502d080c000c03503100c54440c0b1540c1104100710642000c0c9100ca8210320740c01c00541e01c076102d044150b200d001c9000c9220f041446000c0c0c451020346010300960703407a540380c0b0303114034810301840e64a80d5030356000c03080010305000541c3d0090340104500c906c8030300502c3d0603d24010400c02e26600780400141004010780d0000b40718007401c201440d001c2080c244038101a6800080c580240c45054004503000c21010740112060354005000c4480083c2c2c1c1a014040d80c040b100c00003000750004142003401e1198100c4440208841e880140c0160f240c500f10004100d0198034170b401c202d0001e0f4462100304014a40060242d600003146202442070382d43c080c00d19079a440003440010b01c030320628000100c1545140c2c10800c3c1c540303015001c541125002100040c0100303d1070040922a00c80c4000b010500d050501c00c02c04072540c05440c0192a0304c03000030014141c0803505407181004d204016003001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 202154667 1250 202153417 202153423
    0xf0209180d032003040f1203110304110102070b0301030b010915080102120405010b013002090604060e0102060106030207030503180708032113031409030709061d0705030c0a030e030c 80
    0x1420075500059510b00d4012441c10a410400d2403c00a41051040c400440c40c1e45141c14502580840c0c411ba9400c0c400d48160090702c0d82540c1c980b03241e20044100014007101c00d110200180c030036400d49188a4a858194040d4082800098072a42031a001413001062903844061140082c1c80050713011035a95011070b003664005441c40400d0708032141880700b00f0100b4020303244403c00908181040401c076941e003001030004c007189a690003102951031840f441d8907904807215040068120340da5640c65141c0504103551042c4510300501c2608000901170303229209680185034940d541e5072440e2a0720791142080301b00d5000541440c0035084001800020410041ca40020704110b800e0050740e0080c5030300e02c2d140c0001c08003442d100c0c0080005000913803100612a111038070000c41925600175101103490581d003a00401d42d200d00e00071000c107130703044071402a0f07041c4050040d1080c03181e030b03610b80c045505000544414800203410b01c2904480c80c0a81c10440100c0402000c582c107110380c42840314a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 202155917 1250 202154667 202154683
    0x51b0f1002100b0405060d0204090c0f0806010e010b03070f0e18090d1e050a051309110705010f1b051b010609320601031d010908090406050103090f020918 68
    0x26070b000702816a0031400d079002d189020f500403036003004180361080101e1806036175408000e100f255507855400c10008990203000182407103e103aa21041c0e1140d0801d6030352682030281542c00140380000041160101c81103900c6603503680d59181c541014180c041e244200308600741540550100c004009103144c0708203046c0b15020b00c1000308450351582c0c2d00903049030542c0b28103d504450002d200c100b51034202c8102d81b10700707040d85003065071030039070b0000152041e040c0d4000801d100e040c224040c10446800700034285803400b81008101c0030307003c000f6507001c0301e4040b12220801903166490401e410300980c00740c188003078a81080355204242d425203e003100d1030b50f000400c0090351030300030302400004d198186170441c1004c10144810070510340d20500d601402815103041684951a482000051034084100309100d0002032004112500c0d080c52560011840070380100e2402d48001003540c0b181c0a415951a04820b10001c0300159130280036a50304024480c007404481181d65581c0074a0400c6080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 202157167 1250 202155917 202155949
    0x3051c02031501111b0a0801020c010207060c050306090a050c0f0304050d020c12070b070309050d0c05040b041a04050403051215011403160c020a0b0409090c050607051b0f 75
    0x10380e240b6140803503001c6501d80c00c5042c1c0c1081494007076841054400036006044854452103000c0183c13a40001032000300c410341065240b54008100031200d20320540162041034417039401400721100a800c202c85500081f64036641c800302d0003000c640070294a50106400030030b0300010700d01e400b0540d8000109507000f50703411034040c3e11a11503080050b50506c140c40f11000c085580844034026110f10954a244a024882c101c0c00f000420f45c08050041741440020303c0090000e8042401e0f60601c1150210584a038901075824030001503907602d000d100b5400d01c4c0e0681c102d8110080b02e00c030248001404000c00441c2400030801041c000d10000040d0b292160880115240c582c4881d1400102055240846601002030500c10310004640520411074004103914124582000c82e00006803480e6840d4082c860062000a004c0350761301c8150070014906000d80c2e801c4010542c0d40040c01910f01c0f44000140c1660040c2855208a0b0140301e0070303c4001c0340040000700c20103010000100c400d0801c0c8118 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 202158273 1106 202157167 202157171
    0x1d04080a0e01051201260708030a08060d1e050c0625061401060e030115030305120a0b100c05060a0e120a02030f04030c06110c010c060903051c 63
    0x10720720803400c2451586807540d4403101c0144290221b2415228050807560b500100e0200007070306000c6500003c01181340400c400002c0380c0c840f10240c286540038125071b030305801040d4520048007007003500301e086075940111880d10610381003000803024011354052012400104403041c03a5186840400d102d10a00221031a004006110300040e08030410341c0300340003155187d070003038030300e048180203400800c40f44000c1412030014540c9807000400240e0104041540f502c8407000392a0041c1c41d444002c20400d240303400041c5000d0b07160452100051a84005009100d420000030780c00c101001800c03c42d02c8011510247c65030403000440c0c1504900080c507880141c1b00300203c038018031207500c42e1900d40c0c0d240e10303040c91042000d210782c2000401c02e1245400000010401c41c80032030b816103400103401c06c20341e43c0c00090004143d083d01400030034440c3c1c070648418070f50100c0c0560307160140 = true := by decide +kernel

theorem cover : BRFrame.Cov 201978417 202158273 := by
  have h0 := BRFrame.cov_init 201978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 201978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 201978417 ≤ n) (h2 : n < 202158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
