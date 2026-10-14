-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1126
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:21:16.69368+00:00
-- url     : https://prove2.me/submissions/e3c553f2-4733-4d82-a703-4f69b7c570a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 202338129 ≤ n < 202517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 202339379 1250 202338129 202338179
    0x20a080919060f2003071707050d0b040222050f03010204052b020d06090b0a06061d0312130e1501021b0a050a0b0a020105090106050d031d0301090507 66
    0x1c1c840030040c012040000c1580300d0000541901c9241008004100d00c2c048011102ca01e28400c081c142e5203400294043c100300d850f49840039000300c40364000c83d0030444840340024024440000c1c40c2c1c1c655044090358a00080c000341c2002030b00080c1030102d00c0d001c0e00c8201d12441040c01000702e414150881320046000340c0007549850705041c08520114078088010024a10800d100d1074a2000ca00e0a021702c140d00804807c2039140c9810000080c01d128007003520444440703008200c41c0ea4042c070641084501a480313400b6482c14142c3d04850307002840c0c408a0300740c041c80080d9003071030008a005007480b43d002000c034180a81803000355503807134100504001020340b014501d40c000c0c0c0e13000218512260285191821110546030108041000d07a50000c0d0308a1981c22000c2407254409000e051506400e40c000c1186a82d0285601d0036140c142c460950826602480480420b1107040d000c1c801810320481c210040e00c0344404a4210f9250400540301c0f5082580b0501200c402c0c00488250000d04210b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 202340629 1250 202339379 202339393
    0x702011d010e280512030f010e010302090402040c0210110c10020405060910020c03031b010e060403080c131503270b0a051305060103030818120d0207050709050a020a0809 75
    0x2d103aa0f0768402040642d9800898035540e0001402c03045544a00c181e4010700345e0f00044000340340c00107203400640d07880d0041d01591002168000840c18520b0403070390014400202900d450302440002d2034020001401c50140400f1143d040c15070303000d001010301135221000d81d50301800e14085c1c01d107886848202c44241c0104010410782d912a0183e0310310f007508840500300d812003140241e00d000900c050280c0c0501002c40c4440401684498840e54030700e0801c020711686801c0381c0c0450310355508640050109900c0030205003c90f44640240020500100d8020076007a2210b41505050810402500000e42c580c070042000360784080310322074000c9241808140650656a8109c50520011311041c0c1c17a81d030301e0000420381c05504006080e1542c0240c2a1440f0b942c49041c002c0c440c0c40c04560a508903203200390742c88580c5a0010b604140c9a07454058141072020302d101d940080d610880c070942d1584640d0302e020032181d215100b0a4000d41003000010b80d500c0c800b4034050305500008100d40b00c1034100352 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 202341879 1250 202340629 202340651
    0x1608041e0f05150d140a0614010c03080a0908031006020c060f040b2a010614060a09260d0918020403030507020f040213080a050606060406140c03120702011d01 70
    0x100c80e110540308200c5101c812280700039645506401075402218059045c01c00e040c030680e01d070105150055181c09028010562140d502840801c000e000c1c85000507503846105001c01e101f0203905400600c01c000c041000c0495803280c2003550400c0d6035503030309400d005804200c555010131208400d180e080d0f0342d02d4281305030880540018003171813054040c00c620010300f108146d4a07044400c0042d0300030071040416069000c1e0b040d070007032896004502844815010110341450b1036020b0352840c0d8110342c0c40c06051070401c610701003c0c2144040d003c0803496030b00301880244c0307800c0c807c000d01780302d21340d039402e500c0c0d85403902c003404800381044404074084c4108070a2001c070740c0c040d08580c5400d4068580340c2c822009180840c000f8481c0302c428030042c0344880808280e008012540c0250f5034040c0f0201d42940c2c64000801000b48218861030b00819001c40103914040c1505001c3d0080d000440c007620b0903d0103465410380c005d48102d403c400180d540b0021217a41a40ca85e92814040728514020002c0b0602e01e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 202343129 1250 202341879 202341899
    0x40308030907120f030f0e090a020d05010501050f0904090221030705060708040309060e1201020d020403170f0304020918031612080115030f0e0d020a03080a05040b0103060e031608041e 81
    0x343c68040c0412a46c55188007481c0c0c0240001103034001c019018842c0c0f450a4080381d002504844400c4100a0400b00001030a61240d025904035881c485003451800716184100300040a800300d04a07000384501548501c544e0641c08000344409107480695a550002c1c5040c0342001e030003d20f41800e000300e220503c00400c0d884288203060310a40d0410840850f10840000c0040c41201d41111281d0700014003001480c0f520340103030040300d1041480c01d40d0012002c1124015016001102d500d114050001602510705007000b140c1100c010014200a080070841c09400c0d40c0c0700703008200c81e035088002e0362001c104080c076038181740c04054540b941e50b650411040d101e00c85071400c5540101500e403026020b124545c0c6e804501e0086a08044610b142400e810103900d8100b208029404551514001020088203014861055501400b641c1c80c580c06e40e510040188284c542c50384051000b130100b10401c0003400310300c0482c0c40c018170300d1988407403800c4e880b10150104442000304400c10b581c010003007103042c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 202344379 1250 202343129 202343153
    0x90203100615050c16170c0a08032d0c070e01060f0801050f03070b19030c021c0503070c08180301050604060f030f08211501030218131104030803090712 67
    0x246056030740c4004001e2214900400182e40c40e10400d0002c05c001141541c0001941c00e0b140400292410f2211300810412070900780d00c10303040242c2007081001e030004001c8122881301601e06561400c48400c0703500701c4150340c000a00300c40840d40404414000e03068200c0d825801000d0364640300034036800e4200001c12041d4103218090007651141111015aa018017641c400340101c03600c070359107484241071005014490040c3c0d000100345800703000e49126101248507111610303107030368480d0403140d0480100c0e203642c0018000d004003d1140c55010026803508010401d03a144698840d0803890351004040c03c41d1400350440d40718600c4c200d030422014603c21801ca0807a81c00c1700300c1584c150784a05000e41c0f5403081c1d001c903400e8110350400c9103001c03e40341c111070782c004c3c0c5000302445003583d02140194220300c1190000700c5920010501c11203d4941200b500d40d00903080c042c080380f51031002c0c05e13550007500550800c0b00c00791000b10411004507070400481d001404400c00a1102403560303100c030b022000c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 202345629 1250 202344379 202344419
    0x30f111207020c06070605041416180b1002060402191203050f120115120507360801090b06062a0a170903010c080702030f07020f130902031006 63
    0x1650030002410240248921004048041c0c41240c0e42d14072880c028008000464007100c80000d04200e50f1004400090307010206415110780c903644908203920007001c1c1d00005502e0915a07191886100d2546582c119000000ca0b5500209802d007418030400c4104030484da2240005001c2240402c03a21800300003044010b5050b0810641d1484803501d110454171500c02d41c1d481c400c19003000090310031081005600303408400c1d52050011501da00d106030039a8806d641c00c02c0060640442041c40c000303001c542240f4241100000702090389c4031a139044c01c4140300d910162481c0d5455542d0000d20108a080c240d000d1001c41d82a850019103c0d1907a031684007041d03030000b010210b11075104c0c28080c00c004c1f0700010340c0c2240c20041d51480d0308030300c401310303a0003012202d00035404c045003000c846003c3d03c0028000e4106030040c0d41403450509840c4140d13001180d080e41d119503107130030007003845e00d48000740c440780d8110312008500b01c0024010701d40b405100c00d21a8003c6444c0c15010400d091145020720050b030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 202346879 1250 202345629 202345657
    0x1b090603030f0f091203030b0406080a05060a0504080306040c02030903060903030709060c050303070e0a1809060e030c0a11060f0f13060203040b030402010804080c100c090602010b15130b0316030f11 87
    0x5c8180e090440c0100441740c8000d40007032500f000030941070000100d56141a00c02c90854140c0d60380c00c00b0620550f602030b030700100100c40c24004200c5078a416040760140c0c00035441104d007070004510000746800010b07500111070382c00000a0080e00390b84495140040c00c071a00789078400b81d072655280c555a00c0014001d5040000d4011082070a5441c50340000060610300014006801e10000e07003801000c0c0601c080341d140e460480401d5940b4000b201380e0310041c0006018110050742030303c40d050b0160200144946c02a0304101c03503105055018080c0c0050800051042d4482407042c4698025144641194065600034041084800c241508480c0d000da130a2a003042c00e51614a007d0005000b98081403c40d0701850104140481c95a4012040c101440e40c8141200b070740c94a05071b0032242490f0619800054000703404806a030104020035005030070b0f050076030745150794202c50b01d0250030a1ba04981d101c0f94545080480329494050519074403540c08080000000704062484d60344145400e1040007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 202348129 1250 202346879 202346909
    0x7090e0f150d06020903010b010912020112022a16030c0b0703090902041215020a09030318050411030a05010b09010509010e12030d0e100207050a0b041b090603030f0f09 74
    0x1c054003030212821080180814001d01498904007010b9041002000c0c0250b03e017003842c0d481d43d80305407030b020200c40010100780241c0c0c0a035001140d01c4121850200c81c1141c007006040c86142405001d242440d6034640c03d204541c403110402c50514465140c9103580f00303200c083c10b1005c541c1d40032405080f0340343c1c5082650f4400c10703440c0c1558415400e60041400c14404030300001e001c01c1c807080161840f0f1003000c103220813100c941100d100f28010b62500e500040d91907070741440042d0040c5d420f840c840481010f0886126078400014082c0d07001c0c00da0500300e440010003400069201c5000b56809003086680050414a2840000704a4011817030360b02d0400600d1031700d00300c9a4447c000312513100340003501629580c150100201010b41280c80d40240340b4800c140c0e0317018404031f4130320a648260394801d0103020110041d0b1540c0c400c88001510a0b525000d04802d0b01e10b0700c03e0034100800040542c441c0104801b441c0d420081c042e21100403014060000720900031081c0c0b94469070041c01e5070440c0008404d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 202349379 1250 202348129 202348141
    0x150a1a0a0c140304090b330f040f060f12020403030e30012c0d0e1302030406050420090601050c0f0307050c09060a030804090207020105070b15010807090e0f 69
    0xb094011031103026040c0000107001c1664040e07034100d0b06648000b65403078003c16600300b40441c0d81c0d030400a0301042c80e102c02c0720641c17165105040142200100107542a04140d2125404520f0190603403005001c9220198000103864024000e6100d1082e02801141002c0c51501c01424049040c0d000a224500341c9940c6004c001003890544800c0900d20003940143d048904518001e14983c20002c41d01803c60460040c030100d001c5a244001d55404081c10341c0c0c80c4520f8003a80e44101c1600f915902c0100903103100d4044400d03102851040e40100380206031400c1130f081c440301c83c090700710781d00c2d5066a803512620b0300d984030f20b01c409410920038a40700c0d03036034010034042e28184030742d140aa07241c900000442c071003404000200207002240403201c160868443c1400c04c4251481d6100007021041c0030704c420041c1b20b030107501400c138045c01810070b5450036440359900b2403210422141070a020446064101c0d103564049400740d4040482d003411044182009108070705404010800c0d168003546200043d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 202350629 1250 202349379 202349393
    0xb03073b150607060504060b030f070f05040504050a08030415050c0c030702090601110703050a0b0901050603060a022b0e060907051305061206070203040303020f121207030b09150a1a0a0c 82
    0xe5040c4c00c00010881414a0b25209018105a0307408510900c205400d03d00348100200d171280860b0b00e680a526541454003050201070400108240c0d801c0c0941d01c01d1002240703c0100840c4218031071900b0b454003203200b009000403070380d0181015643e4002400034580d00407001080b9800550101c510215955401004803a0100f00031488117590060382c1c00041001000a106882d0702d05c9800c5c040c80c41c1d520701c01420300300c4000303d03059a45940403001103145404264000e01703140410604104048280000c1650f0240015043c070f140c02d503072205200a501700521485030460b91240c0a8458580707800006030103c40c2485215100c9550b80010a80c1d42d0740710902c0c0c80400c81c001090758a80d24100030b02945a804c541b105030050b0003960310b01401e2960114034245403400c4680f4550505c41d0016002004581c000c01d039101341642c480c1d00c0003c40d0386443c4506d205003500300040c0012050300d404d200034694250f02c0007076075078407142e19101410080f001b030f28002d404901d480b01c084166410403034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 202351879 1250 202350629 202350637
    0x2105100306110903010b041404081c0212011e050307060e120a120215060102101d10061503020702060702090919050102131712030a0b03073b1506 64
    0x80c6001c2c64081c410600c00002c00180500c81000c4000308503c0080100344000d950413001940c80c81000c07000002c001a01040141c0030001d02c1581d001006000c0c0c040e20b0781241c1c40880000410041d410040009002500b107602603e01c16203040c0318501e1910020a907254182e000303650512500110000d21034a5101e400701e1140081c40c1294198040340c1809a8045140307602d58005028901101220640c0024440e0060034184d000f847c0134082c001380c2c8002050200049015042d00e900040201c00003005850f400b070081c8100059090700e4040c805c110003250300f00401c1414018008c00025076920030039a20181d4041c0c1c1d0a00c00742c0c1c1d400308441d04005402a810b650700002c0c3e0486418010158054600e03112840364511019407076440c044841d04400c0c5070fa030143c1d80011001842128610f02940c0c209085800118070021803038002070500000f504400300d510103007403015030a440d07405802880842050402036a2000c064a01502404020451035840c00b56508400660f21250112 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 202353129 1250 202351879 202351883
    0x203060409080301090c17010602120310031407060f17010920030a060f050901180911030f0115051c0602090102032503020c03120706150305010c05120721051003 71
    0xd540c0c3e50703140c0f00d049000703222a00c030440000d6100440c9141c0c000400e00070605855140d0000c10310004028041d05d060380c8000e045074070b40000c44c2d000000141441c103c2e4100f0b0751500000c0e0115501349640202a0003103400392030104101e00d0043c41548030011104c5041d030704013980101e8007003503a5001e00f66421410b035070140c82d01c01c00000c204502e25141c2c055800e503001c602c00c2e514003940e01c60802c00209802e01404034140303800e0450f81c0040b43d20fa030090b440c00d403140030b03900380304201e00c0000b90400d44128000b07401a5150303030360000380403c40c0c1200fa000e0b00b0103e80c2e10340711030780c11498501c100e0001d00700100810303800140c44038581c0c000c02c01d070b8100e0000704000d2801112001c00d01440150341d41c41c210007500c02c1071006500380c40c0c00b00b031052250000b983c503182007070700585030074000d0a038011080514120950010011a6080c0189580c0540f030b51507a40c1d84540c1c00c88140400c41c4014802001c0001e580d0f0401e0884482820200114007800000300701d40e180c0d1405081160303155440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 202354379 1250 202353129 202353143
    0x507050a080c1e0109020915040905010203010909110a1a0315090c070213200a120f0207141504030509060d1401140901030812090a051902100c05100203060409 70
    0x1221220780b000500d00490b0807180d008407043d02c1503040302d14241e559050340294031000702000034101040103c00c03c011510f000b031020038a04580c0d2981c5007203a10a8000c280f206481e00000e03c24000165003410f201c4000b0744a200d10980361040508010180340d44040710f800c03001020402004d0400712340f0a100200900b01c42540c24521803000069025442c12030140c0072800c5003840800c0180f29100d4152103880c601c2c40c00110140d07409855a108200c10b03014401c0280c3c10b0300c0000d10502c52084042030441e80182d4030069428501c0d00e81398118561101a0b1064107991800c0c40f1040805800035454140951105851030000302c8500601e0903d03256241b8051030420000380c4144058100c488207075105001c048143d041c0075540009000140c10200d0411011003c140c0011b52158801104010741d50078040c1d5070340f102d003899071003202980e02064000480095141020050740410942c0c201202100c00d140d407100d40b503890130222044680d41c0400050403035160fa40248501e33a9014503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 202355629 1250 202354379 202354387
    0xe0106030e21070201080901180204021b01150302040e06070e09040c17010f050903040308120709170109120e011b02030705040f050916030c0e0408090a141305010609060507050a08 79
    0x15582c2c6058002c250140c2c000b84006000c1110500117200707005c2400c0048840c2d41c0e0b000060f8080c44007035030281c540c0945840c00288140c0300300c0000e220b1140d40c003e4040300031100741c0c5140104825503500119111243e0800414801c04030b400c40c0c0c1c0f070300c4145002e503001402c56949060504610106602030000c0200781d0004046e01e200640c46030042203030300d031410803903502c1d489142581c80c021800300074640c010800980580c004020784140c1e10418901d00001c0d016107038400c60f85412000c81a08032107a449041c10345c1000342c41c03030b01414514410324001c03d0207015070780020041a4440c80c10341c8506002c103840340540d2428020080a04809807007845014240d072a01d00050808481e0218140120710044201ca0740701e90340c174021250803111050055007407070324512400790301420854200c401002081595100c06558200400c2c492a58040c0c80d20404140320b64258481c001c2c9e054140b83c8401401515040700c01c0000760b400d20b10b00b4540f6500e0350700d031081c5072041c4044003902e1610046 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 202356879 1250 202355629 202355683
    0x30e03040302060d021b1902150904022205030d080a0c03060305030a0207050306010e04020109061215060522180b01031e06051914040225030504050f0a0e0106030e 72
    0x180082c100c40c0c81b214214004600001c142c0c546a503090f102082000c0c088103c0c0790301624240d1000c1342d5510088080c0d51600903404009001c0383d012030700103107580c401c2011705584d40000c4114500100400c0d00076224080f00359500400c5103000034001c4008a58801705e1a018034440c1d400340c0c0c051513019085a5491800010195544003980b18091007841844004039220789101c803e02d004a40c10303110a26407604101f020b8031101082003100f0203459840514138101030603c0071800040500c0e45810390f940f840c0d082c12400b0300c103500e40840794000080d40c04000403015800d014004004a010000341a1909001203018140d4032001c0d00d00388250a51125040135141c2c0310f07004072001141d11804110040e6980010050503120381c1068030981d010110050400790014600450f02d04100858451180311100b450141010141c001900100b01841036003010700c14a0240d00c8101d40040555180c40703640d00024005009803001c141d00c881382c5800c502c0003007110007000c1e00078107000031410711a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 202358129 1250 202356879 202356881
    0x30c0c0c0e06100c0807020607031701120308090c0a03080f0409020f04170a050316030e06070b1515090f0d08040b0306040c1d010e0613081b0604080706030e03040302060d 75
    0x155195840b4029400b420302d0340f1030082d01d01e00e44269114404a04000454081044940040b44198180203c040810315050032a200301030190000100000c41a50301d414001c0c400710b801068014a94418095a0b4160303039819452011682d010440c15075901d1030b03401c0454140150780c0701e2424a4000b080456008031b405001d0019039107003030810580203e0034000e542e80c80f01c0324100542150000c00201007021007902c20041024000e0400349038500c0c401d80842d1a640c001c000599003141044180103003440f030301a44801c1340d1811544070102d992180d0303d040c95449100152031158096800b900119116403921542807a00529010740740d640d1020b0141c800d82c000c039030180c802e0b4074045102d00100d00a0329000c80c0310810000c1c00c11581c041d00c00650f010340b5080c0304e5503406041806515824480170911801074007080c1c014201c850442c3e8a60300c110703004013118034414802408103220500000484000303e4680b49408603101807400b0000307041d40b10355000690021000207402c1181101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 202359379 1250 202358129 202358131
    0xa060c031b020c030c060703050d150b0a0221130e060d020a0b0c0d090b030a02030405010906050108010915061a0f0c0d030515040c050a031d0a0507080616080403030c0c0c0e 76
    0x81076090b16101401c030010091b0a205000d0300030041181404103e400001c16403142d4001180300204e00110f5807036143e00d5940c0e412100c3c041c4c0050348140100c81081040e06500903107a00c0440c0da043c104140c15a01241700c410034025044021081400160141e4500c603030b40401d186c01818010030f0715281c0885050552100b80214114440c50107000866842003415000302e42803041c0d014150744580450782301070361019106851035900c1d010030a001c1415840303040c0c02000d00b0300000803a5a01460074801c44266100721162032441d000c0c0805c00418500500c2e24039022103004a80c1d502c542c03e412880c0750207030602110941c0b00e540c416030903060f0035a1220380245818100364915010400805c03003a02d04d5103000c540000c0c000d02090203014060780045408111000d056007402000002007468107036200c82c140c5040d800f01d0810081002c1c244070160700441e03070818804149a542c100940383c2c00002e04028101a41c0c0d501d0444890310806000205030b40c803010400c0116620600c410b01c100c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 202360629 1250 202359379 202359403
    0x6100e0a0806180706020a02040513060510080705060306130b120105090d090506210c07021905010e0105030702060f06120105161e020a14030f0a02030309070e0105030a060c031b02 79
    0x4400c00b00074000700f8009215401c0703424a034000c2081c250700354280300151902a0041d100e0280c00c030030400c0003d1250007201d204000c3d40c584c6400103454030303508602e0300c161a03208500401e8100103014481e1110a1036031900c0c1074889012481980e01c0f00400e078907040014812995500e1301041c8199580c0100b0365078811031b0030303030b03100700929444008101c1d1034861030101025180c500002d070000c042c21981441d81c080802180c080c1800090340100b01c004c4d411401a1748246011041032186682007000c0911000081c40d0035030942c0f4003540302030354844002d0400207064000d0000681c00380d848011450551500500a000e00d0034001c104001c0041624072002c04030780c480c8070400c3c95241c1580141e84840041d8010402041c1a40320908590044002071a06001c20000070402820a10090684a13840e80c0203540d80d00e8484070890030043e0342d40098000c0842180108020f0f07070001920b1140c990071440024000d001c0c2c030b01c168014000c0d003e07260b00c0e05182c80e90300d5404640225071841180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 202361879 1250 202360629 202360651
    0xa020c12061f0806070e0a17010e0706030603081c18061b030e03090603061201021317030406050f03090a020a080a060e0c0102120a02010b030a0c03060b0109080606100e0a0806 77
    0xc00c000b50740749240140760103141c50540c008400280003920501080141d0000036101004164642c4105000400c000624030200c3c1c1d1940703901103112204010120080046190421295003503070345500d082e100d1929002c990301250344580402d41ca07150b00214800500964100b181c0300c0714034094019010740015941c00c450900c0032441040e00074001c244a00c00204095480d103500c0100b0450aa040500b0241d08245a0180c1241d0003500b40b0040c500305901400f00d83c00c5600c1c003011031054004404c520744141d00140410001e00c0e4001d010355850001c1c1c860b51644039564441402e1070318940c50b00103507003c401c10000249188002c104a003005004034805c2c403500110901096507201003044140c0140c2c0005004d01103049040e0162442006c980300102d841000e10000134a000580c10701a926407107952070420412034140325400785c41e81e081c00d040780d12901e09000c05894250042140d402028004170150301580714600710720803503900502d21450f0344e8076250103941e034800c1241c10510350 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 202363129 1250 202361879 202361911
    0x405011401031a030d0f14040e10141f05131412011503030e0102030409060e01061d0d02090c09060d0905160e01030201031112090a030801060c030c06020a020c1206 72
    0x1c03a000840c10040600f0103001014005d410b10012950412908010300c10032401d10143c22250342441c1c01040105500c0700440054145680d0551122010307074071100301c4005510709140d041d00d0b010008150501210f642605000c280d000c10f50300f034440c1c00180206c4240f03c02011504181d2000c60340f02640d4203840a0650b640c0200140d0708070b46440440086020244208200003882103030300071110101881600d0030982d45a29100a0307540307a8014015210002005008030b03548503810540c56900081c0d40d004800303450307000c103400d07520b42c3d94040d003c0c03d0b042d000a4150f20014084641641c00a01904d54032180c0a000400030460600300721058000e10b1815aa140708006500c01a00e81c40b60360480e02c1d9103585d00540092551004846107a01c06001d03201c114901c500055206094003005040c44c11002d203802000074030140c00620500c0003210405010a41c0b080700713100c80e00ea20150050340c40d9640541689080c000880c015030005002100100003407000c20030a00554071401c020006e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 202364379 1250 202363129 202363151
    0xc03020c07050f0303071208011404050403120b03032b0b031c05070606030c060e03060c042612070f11041811011403010b0a09050607050a0b04080405040501140103 72
    0x503482002040c250940c40030000340120301d0a0000811003540040440b4504030281e0b5401071810031101010010542e03179401003162a010040400140104440801080c40c1544c0c1c084c080c01c20304040c003070404d580d0340d81090254408000b10f54010350446030795602c180341c40d1040101c030421000e050300441d0821440a4645c2400101c2c44020000c04c001441114254001114950880c8a094070b8407603d8201c0000482e808500d140c0252513140e480c0d18145100703605140c0352000152490454020402042000340d22100b0850703030005220a1a010a06124840350f00e02601d804c1124000000021050104002101c11261080c401c0c16450700042c2c4030b8007040121622030381c0407a00302c20010a4200001c0d00b00700d00c0507050f1814142681d114003e500b4aa480e6002600300800f40000003951010454100e00d44d680203102c1210080d1500c0701940d6101c0d200c0004481c02842401e07104041400c00c2003910135a800340030041d0041006681d94000c4112030b00410701d06a0100e880d02e075040720 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 202365629 1250 202364379 202364381
    0x10030c090e0c03070e04120e060d06090c0c0c050f0a08060a061e0501050901110a0f060f0b030f0703080304080c03030a0f1407080f10030602030f06100203160605180114010303030c03 80
    0x2085444691700d0324229643d648552848984281c071003010407407920b40c44181550350001405800590f2000018800d06118001e4100c0e0789013102041071000203804d46c0c001640c1413090b10203031141a10ba00074880002008600640c4143c0c11601203400344000b000541c0d41103034004030807a1204007600042c21031540408000710740358015640000c0c010418086694004c0036420b580500740d200f1581400c0b05034803401d013a880c00c03080441381c03982c0314000f1041ccc044c0180510b840d0040120098030072211701010032961500c051000a10080011002400380500074040d11000140f0400b900d6a0f8a4a1406c013401019070144000b12940780402c020b5140c104054034a10078015511a43c00640380e581c115029150010050075004820300c00110020b0454000b0b0340c00b81050301c0c5a11207a050100400003500201810700045600070300040580703d01c500c0744c00c1030541d0071404c0022207803158051011003800b621030718482903080c85861289644031114042c106d074042d0358108150584e00d08110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 202366879 1250 202365629 202365643
    0x609030905011d010513050d0303050a05010f0f140105130608070824010c060e0a030e03060901050c0a0e0f0d2906060423090f01061d061210030c090e0c03 68
    0x565004841c0303462100e00e5020740000c1c81b0701d03045c1025410b0070581c1d490004500c0c44140d903040f400651620b003407101e84483c9002c4d030703405003d01403280040f190920302180c000c00040d04c50f50411183e0000504180d9000384211107401c003050b6405100f007510b41001811f0f0250513902280002c0b01e000000b48203c0302d250003003a480300c60304803261046400300c004485001180406841c0c05903a40242584444100490400b07a4800d88600b810568040201810114010300780c48007030b41054100b00907074140da004c98035010010300301080d10039052004100c483d50030000360382d00112060680010322901e0020580b5007009595240846d190007880c00404010a4540365004101800244114041da5601c000c2800150300080620602d40d0002030f03e45d00155070540001000384014040303107611101c5008440d2460721034154200720407001c0355092003600c00c9500c01705503080c0800d901000550b0144025034110001d03800752911141001c0081100c4000c2142c43c0c860751400305480c0c10003162034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 202368129 1250 202366879 202366907
    0xb0a02040509040209060103110414042a0c0c05040c0305150a05060d0c020309030303040602040602060a0209060304060c0509030607030f0c02241003050a050606040501060516031b0b04060903090501 87
    0x100099103c503400e01c0070001010740343c00e052684031000b0401c0010f400010f00020000c01d0854145c001c60b50b010322080711240750039031082d0000485030488015401488151261031480d10358207410141c1001111705e0b5150f00490750050420982c1d903d01039243e0001c9d0700035807040f000c03507501c0310014042140c12080d51041c242c01c40c0341407200c01c801c882541e01c802011501401a01c1c40d22022100080c00c0d64422202241d40690100d000d03c40300341d04010881d480f090041046103007883d55000100c02c1c3c00020030082095454484541825128100740c60b803200011f01100d01c1c0381024000600646107044d00c0c440c40fa89802200c081103031000440500040f00c20b0b0322a401d10002400031741c000500180007240c0510800e40000c0003500411030f044a050085010300054103740003000203a0b40d06a0044040000500c4204006140242d06144140e4103045c03034041ca448a0326060550026141d001c0c1030000382d00d007040f051100700d401007907031644299034034680c2ea529100192a840b0200d205 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 202369379 1250 202368129 202368139
    0x3100b0c0a030e040e0106030c1d0c09040b0604091503050c0d030e0f030f0a060f0501061e1124060a090c02030d150909050319031a040510080601060206040b0a020405 73
    0x11400201e8001c641480e40320303002030f1000c12485d40800e22503095503640d038012203420802400130130200009000428410440e502520840d0a14096801e20360090540780d5100d0307992505e4004265a5a00c01c403001000d104c0024044140d201d03500d248504c60b1171106031598010302c6803402081c41c00c850202240b9526440f10005603d0303890500010f01c64514440e901449895240b050040c01040340f420080e120b504c02040700c2c2404020300064400c1030303200388148000b900c021103503103041e6041482c00070580e1030604007500c020b5103058640341904c112f4901c101c021107401c6040810901d07606200e4481a10982c801c0e959485c00c100454521142090040e04180f00702031007800d1680103842100400000d03a00080d0f200c0c81010b0480b19801000c4805610001c0c080c820f1074468000c2c0a60190345080030840c031101c0c0041800c2803035604030140e120b00d94130400110703500c2c1913103008006846054100e51083da10782901940da01c500f9a0f0696100c4101d400045261a5a00860b030039520041e10b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 202370629 1250 202369379 202369393
    0x11506050f0f0c0114040b15030109080708072103020c0c060307080609040501091205030a050f07120225080c1e030403020904050c030105070905120106080303180a0b0103030503100b0c 81
    0x1035010094203e048841515501d54041190389144140c2e0f060159010300650002401d100c141c400721118070f0440c0b2402030341050f520501184202080d100b4103500419116a1030312b0900d0004204900c150074685411407840303111001c5549070340502070f020070301c40807900540c000c8010460140000c669207030000d403000c00081c083d03080980b00107802622480012510704d02540e12044044d0b040d0034030f8000208007100308803040c9464010541c000d510503d6620035030414100080004000c4201010156000280d0700c211100c100500707000104003410703060100c821481e10000da640709442034401803161189450020082400848801e201d40d00194501b40c516070911035030000042003600c4074002c202c41014146c9080c0940b40c8510a00d47e01c0c409007905207170401c00880f000010607800703689004414403a08200004480d00701c02d108464000107040500810706e4001c81181c0100b44a1300c46d0000800c040c1c001001c0d60049904c10810030342e2544500100b840c5002e0f00100000710341c0804 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 202371879 1250 202370629 202370647
    0xa0b011806022d0709090305040b1c06050402070f03051e030a051b1804091104021318090b130c05060d0506100e100305100807030f02040b0102010b01020d0f1709011506050f 76
    0x2d800506d1051103828514105a940d4032080003581040034445c056280e0300340341c140e9443c4140b20700e001400084800310b00f0300c0107070f4480030a02010114020180903001540410030000e6a4405140b003541d50415507403803406290f00005448180c2d195445041c0b4180c050b04030b4906401500c0403c00c0b000381c0504200254420000a03080b15601a180002070b5440842143c86170b000034451400c0b0310541e080c4807490540300000c0d01c0311054648401c1c6141c0302c4100c0014441007101ca40101d80345c0000d481410f0103080c084c6004401e54032050780000d0007c1d5988280e000d0303400c0548510402c6408030f511680d01481580c00703110010006600806058804a4003130180d4021030f041101c4c481404481e580314006646040050f40007961100031150144003186060300410104d83c50a20003401310460f0100041d40d02c45c03d02080e40e0a0004000200310802c0c860320154541282400107140e1500380454001d008240e0110030003104051650041000303030042c821900c026407840c0e01c0c41d10f0103c0503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 202373129 1250 202371879 202371881
    0x606010c081c0612110f0a0f05040f0608010c1e020712030f03110c330402131118010f140a05130314060613060e0a0b011806022d0709 59
    0x82c01004030031980d904000f2800411900d12004a02d210f260003490301c140301740421400c8069070800703038864094020140503d103400080c17102103030000d0305c5c08160030368184c4c422409045140c20482a541c42c0c203442e54000c56001400382d0824510421110b4070045100041f40c9034500ea0040e213807090010b80c050300001388034000340384401d8014900002d43c2d601b05004520503038401080000c082d444880500b44085c0c0c1e400d9801040c901c0032441040158030900c6103005118003c10103403080d0002d00c9448140700d09034000303090301744c121301c40d10365200446058100717241d88080c0864001098075810300e12840c0264580c0e543c1d0391a40620303030704045180c481220154010801040314060b84500000007800840403604068650b40141c14245040710074007140d83c1c4898080c1d50854180101009440c3d896540190040302c410701c0071a102d2280700058a100404c010344545140d08001c000551541c0411940303180c0f078220b061110603404c4254884c400003a01200400c3d15001510304000314412 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 202374379 1250 202373129 202373167
    0xe0901050105090c22231e09040816080403030e0102010b01020a020907090803030406050906090a0c051329120a031b03032702040b040504051504050304090e030c0606010c08 76
    0x3c01c11041d40405c0441ca1241c2094056034010741619000c2220741032110203804031401104400c0d40c1140c002490004003410a44080c10070380e0083e111500803c051100080848507401800303055100710690602d05001c0c81c1d40726101c2a400074074440c040300160341c410b0003801e0603200160b0040171511429000c01540341d401903c1181400714036240020426024400380d48214002e050001d01840d0041c451400c00c18002c1c180c88060700100c2501001a01205440301952002d4841d28070354041441c85100034800402021041c0c003907084101d0600c2d00c00c0c4040c003071006068030244900050f0074121596030490100080125030011440002d800d0503a182c1c940e000e000e403501081c0404455101c900c0444004188407501c41595054410350400b40140408000706413000c20661401c0d07100c0c1510b81c0c2600142d4002c0d40800808641480f20800550300a01185c00c4100400f181041c8080d540381d10200c03032103200c1e008030380010f51550f0055a401e0402504482c10070302d004032a01c800250108 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 202375629 1250 202374379 202374397
    0x10510030305180f030a0804030c0b19030222080a02010207060503280b121509030a12020a030603050102030915100312140c0d080a050a0618020c070302030a06060e0901050105090c 79
    0x140c08040304d04559041040000a6020b1814143d690741942007038100c0c840c40d5040b01d403c40c9802c00c02a0701d9140c0c07000a24013524214a40141c0b100065440310b05501013245c2d40c3d81c5419075000c80898200b10103d44155020f200740c0031145031030380d1014161024041218442d0000c131a065119003a02d5980154408141c0b4071040058000c034144e0010307074080f9511200c0602544169041ca41d4010054640340d00900502d00031070805620101c000d140ca00030740141d80c0100c4c0c010418154413030282d00500055a4820025901c0740342000c516071f1740321400d070741c00c401c1e2000d03003404600d580b0251152102a640c1081c0120030302c0806510960f0040d180c42001c903000320b810400e1644503402800f80c0d901c000703c0c40e82e42103a41c0c10881103240544074003801030f82c101c42c0382807010045a030100d1413050704900c0d6010090f0700c85c0d100010b141d0620400307500c041d4240c003d401003c820440980c0c094015501e10b110580110340b035200f034042c201c400c24024544c10451030750101e4984016040a051222 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 202376879 1250 202375629 202375639
    0xb0a0e030304050a0e04030f0c0b0117030d06080c0a14060f03130501180b06040b03061906081203060301061e031b1205060f151503220f030201051003030518 69
    0x40d42c1c43c0301003045500c1950220380b41060f000c06200425600c45205c038900700c09841c24403181a0729442d050702c036045c103101c3c4801c0501d240e03404505211040c4242e903501d610703003c420403440c0e0f0b0701e00c5010b49070342d011a8060700c5240314450202e412103500701410801d08000d0300e01c0342013910b44104c0190a510140155010900400014000038424000c071819400388500c482c6005d407461410341c80404003e090b4500c181d0030030000b022203803400501d4030350000740894411201e041070405280240016004004203011341c1c01d8514210b03001d50019406410164001c1000382e50f41d400603801852800c0c05403800040540c005c04c0465103e900e8000c0d51241c40e2950302e41c080c1c0d02c0e0340308082081100d8048800d50000d03000c00c041d09400e499081d42c0f00f03400c2c0c0c10b00e011400401e0001080a40c10440003100c9400c04404214140c0405d0100c0e101c000c140d20001507402c0050610721034107000c0d10000c400660800002801640390056143c045991580350740c1e050840e891f440c84244449580b44603002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 202378129 1250 202376879 202376887
    0x905030a05340303020307021813060504030e03070306050105030c090c040b070501020d0f051806060f06071a040b090f15160c02060d02130906030f08030901060506040f0e060301060b0a0e0303 84
    0xc42500b140100441c403a800440d9191028818030109980c400b581c2c003881c0c00070714104050004001c080503d19a0b04c0440003426540d5498280d03800ea03910382d2416010f214045001c002c000c100c1e0b00c040c0c1611002c40441c0c4220081604102040b4402c450040e5504000d0004000359407150000d0449144150005818000c010585200329662507031002d800b29162014408909998500c1a07645079091010f807006181003000304201d40355000031103000d22000943c460034490940d603044071410850b07041c40c44904242c01c040c00200e1060710780c0c1315140900c640c480b0551100161040e0303044405030781a552f075520601042c1c4080c012080e001c003441001012040141d0701d040080c030645025550050716141c0c00a080e0312024030a402c1329118501c0c1000600104812a1248080c0d61740804402d6490395050700341030140459a000580100c008030303004c81c444a256100205885100c0480c0300a5130301c80d4105402d0714001d102c0e22207180810011604840e204102000422101078120380c64 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 202379379 1250 202378129 202378213
    0x910110a0602030f060f1e040f141b03062202070b0108060115020106030b0a11120a0209010e010c0201080105010f020c060f180109061b02040e0607020c010905030a05 73
    0xd040100608884060b400820000e0010034402c020f40c011600703940c080c0e8881c0c0c02101103105055000740d00c1020108420500242c1e6950340c0250f00d11750703a00801400300c2004060456000d08003907911901403071804400d80d82c613920403000e0740c1c0301d070b0801850311030008107854a8424548894580c801040d400300050400f0801540d8110300134003130200104490343c50b010503581420300e66001c400869040c40e000b000840d45604045401c030050400c001401c000005000005228a458283c07003001e10300304100d020300d020b40c00341c80c900b002a01d0b8140e110440308011126412920802400700c1d0440006119035413041c0009440c0c64980d004545607a40d0000000c1c1c55038001c0d1403071004c44e050000712502e1802ca400320403545200217003487c0c0511814030134064001d000341d240f9407030428030b80703407900c801c0d50f41c0c0341c000301d20b600e400c82c0951304103042c0641c000351142141c1004501140e20408001000d041c00141680c405400101619404017086103c0c0004020740a1401c20503140080c2008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 202380629 1250 202379379 202379383
    0x90a0b0d05070303020d0906020303060918060705030106140301080d030e21090406060e01020307110a15030e06091b09090111040f03050d0305100e0907270612030203091011 76
    0x180c010301a030014000700e451854001c1c07034400da0400c136400f0000c0c4e400c020042560000185d0f900f25108940c07400d41aa81d02800d2960a2001015840284104400e025425800074020360580c1e005542e100d10000c3c4200081c03007688028405ea80c0c080d4050701c180b442660ac698000341d180c140c0d200c291aa024121014100d540614500480c3d01c1c082c0000c542c01e4516140c8102c000900503402c2450a050084001075124080d811000d030210070b001d0a009411743c0d501c48680081c188c031508100e01003030821001801400c4014024400707108003408640300720000624070400703107800035400c4144400c0030f01740701094001812030081992101d01514900c182c5102903c0944481540e95800500e1420591702c5c101c140c0d024001410714040500405418000e000c0041e11600007141400342c07a9401c46501d00080d51388051882a60a80c180d802a61030018101501c1082074041c0a01c507200c0780844e000c82140c80c40200540d1040021902c14240190700e04d42200713482c18200c1c070303003040b40c00018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 202381879 1250 202380629 202380649
    0x9030c02030f010b040e0714060c070b030705271e0301090b07080402010906030c02120c0309030d0306050a09051017031903140c0901020601030303020c0109060e160b18090a0b 77
    0x90b00c103944a104910141c18148200c16814003000c0081c450b45280422299614090710001801881c0c0021130150040080044a00602d00ba2005555030300c0d101c500108917030000316030a8418900b4101200680e441d1160349100e41400604a21401c000d09010300e600785094464160955243d017013120209031520341711882400b0a4940301118602403000501d07880881d0090b0062501d0480444034480c0c7c0000c000700d074078018801c02540c0e01600e0200e42c0c0755000d0203032050f50520903100074600d090f40c5600100100c030302c243d400f4078015031aa2410010713244112884089032810600c1007010303950102d504c0c400f40f4085410390340f50410600d03682542410902e19540070a880340c064100c80000211103551141c0f0700d041c41c601700406840000c1d295041840003404054021886407804a002c1d4085400360b03920180401440615403520f42c1c6400e9032429102c01d010450350000748c1144500c01301c8851851900d445038100c00c10b1410025800c2e0302401181044c2c3e583d41c220422070726540c0d944 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 202383129 1250 202381879 202381903
    0x90503010908040f0803030106020307031803021e09010801020f03060d060213030b04170304110108041403070b0414070b0f130e15090a150303031d030a0801140f010c020409030c0203 80
    0x2c80d5880e82021501000d5010aa00010050b40100010081503074048242e801d0740768145032100b50590081d522100303482071900003030341c0400c0d15100e103044981c91003040c0601c41e40903100311400d40e0740c1d208510708034024601c2001c03003000204002a581c2c504000a800e0181c801c240c01070400009042078201e100007074000700c920803014414081480740e001c0c841d0002002000680345103143c1035603178004010b141c0340454103008446011508012503840c41420b51300b0b102c401c0780d03101e44d080d051003400c07240306960503a07403011155008150004080381080a480703d00d03000c607103440c410207080342489e8410100c1015480c4640d030701240e00481c0c8040a4010715002d07103c003005040c0001000030111340600500062860b190101d29110840800c0804030390b014100018100c84136030704d140c07040f600006044624000007419062035604280c10f54140c52485880b4080d1059139018005002c107088400c50104c0c00b1400c0c0c030703c0145803e800000c016442458000ca1000c8260b002c03c5c0380080034540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 202384379 1250 202383129 202383143
    0x30f12040602010f1104060c020a1a07150e03030103080a1107090b030606042c0705091f060203040303090311190303020705031612170f071a0601030509120a0905030109 74
    0x401c000d803640c24052000c030714004807010013040f901503118600724030661188a0a102540e00c0c80c00566844054031402040c220341e1081d0f64503614600e4041d00e502c00601100d07004441038009596038024807070b40e10203244040081d03280d41d003140c84158258100111400420550b0000f42c5604001070103403e005103c06000403902d001c40c00b081601b041e000078000da0040345414410368594002c2c9180398154840c070302c0004403c45003500c040c1e050014030340005410801c8041404924580d007580180035032108060780c824191540c004236240e10a511002c0c00183c0d0190051000c03d000c510740203036051009160720003c0c0061001c00100e8909a40f040d40541c11041c4108110f060511800c0c4040c41202c41c90440d003810040003400886041e00040e00c20b610640c002c1c0c0851003c4403c550a03011580503294507800c05190881c20009000038010441803404007003400755029004460140c18101c01030700711003505068103130441d0046a4002e04001010300c0c0003886840a2003503041c60703805490 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 202385629 1250 202384379 202384387
    0xf110d0207152408010b10120207081b0d02060405030a050306011e030905300a090f03112d04090201020705041e11210c0d0e1c0f021902030f12 63
    0x181ca0140310080f076000d103013541d05102ca155402e41e02e107980403030b100c0605c3c24107800c510390a51503400203002d00030004000071000140c1c040034440c40700707600800b454100d00301c0c0c1c403990218500702e8489000b5a0003c0281d401408003016003806600030359400304040c9032503503034010100c0840c800b00e00c0300d40c0c1302e20100e5902c100000034098107110f8110341c010303459030184100c0c2901c4017011070070401c0d00b00f21100340780100b03806032154440c0940100410502d0102c0c44081c0e04c905160025041c0f84076828400e4801c061040d00c5841c107485c5400c0c030702428840580c0220403000c18032001c0d0460040403411805500804122907649203d0b03000c2da200740e200501d1012080c20307200d40885280c0c00202d021500f0a1154015006d481da045140028103001c02801589480342081400c5c064512858686410b00c010011341001c001015a0100c80f4007682c0b011010080381c095a6070b500241e00500140c10a06d945c64160103a1654003800620180031240b1406103101241e007001484100d003000504001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 202386879 1250 202385629 202385681
    0x17070f050105010504060f06030207062c0609070b04150207090203070302090117010803030c18030a2d021c051510060f02030307050a0c1e05060601030f110d020715 72
    0x440b8450262005a504101313160070032842c0544084148252003c05800046402c00c00120360400e152441c18018503502440d8000a0540008101c900c01c0001c0d00c501c04c009141140c001a4481c212a12095800c2c42c003400e10003c800f003a1411200700b01940300d80303640041d000d815480110b2041e10195030051700d03002c0701000100b04240004148501c1ca10540040c80208004070403203800c0f1400780c035107643c5d4458016465900c00d14100c410703035041c020700f0341141c03c0c09000c0c24964041c0b02030401e040b40c1c18030700f000c81490b400110300c0082d400c0240301c070100017007144417805c45441601a1089620740c4000d0b41c1205074808080307039100c6088810312000c02210ba04017111194580d40303170024604516010384000c1440c0600c0110700104070098a500d018001d024080b0b001e013104000500b49954624204155600416207604d070000349005030006110180d4841c00c0c0814841a620f20310780b102c503a42032006904156401d0f20001d040090340b4142e0a0b00788107992501d6a02060006034a503070b4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 202388129 1250 202386879 202386881
    0xa0f022401090c0507050c240c0610050d0f0b0604020f071109070f0210110405030a0309050f0a140f04020412050105010501020c0105183106050307060e01080c0717070f0501 76
    0xf000c200d0007481018404440020000b0803006000781c1d00350b64640006000c000f1051580207010f5100c206240001030030b0403d680040340492003001d114200501da0355550081c01110641903030301900c5d1031500070513000041c104440440e001580100054100403034142050202e9001d01c2003298419092102500b850170b10800c4160710000e54180701d5406000c0480294413082150380c0c0401c40c566034000341340c8040d69a8180d030046c0001800703c816000042ca40600480014001c0c540f00e9540208407109900d00344040500b5650301d07070202201c03074200c0c07010301c1454045420711943c0203409100114030700b1210404020b0990043c00003141c2549040006801c02104001113410040b0402034814001c3d0103030300d02e00c07000e4030564900e8165424485648001c2500980d0194558010b8001001f1001e036074104d00c007664402c4007590500c0b42e0310340c410b4555512150307080740840c910a0001e1452100d040240482c58010551503244d8500703031000e09074641c40380d282150340c4907035820803100b0311070300b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 202389379 1250 202388129 202388141
    0x40302010b04060f2c161205070302030405060c130e0a0609022d16020904020f060a0c0b0c030108061308070203100c030b0f0109120201111203010312030c050a0f02240109 75
    0xa1202040d0003911840e00714003d1405c0117203640d4842d0090299082c48a1003040d01c1d4030807460041c0d04001d2802c2000c3d005011b54010707202564507104040c00315514820314011100400d82641c40710504030301c2c18500e81c0c6860f00040c1041981e99440c5400100a06680024409a04091104850101b4401200c0f85524070414140c08502d81070240e030001ea80000b0081403800e404840d440080c2c0eaa510000e6540041400015005500030888074070182c0c20007a0241014800c010807034113135480c1c030380007410760100348590200c5d98004008140c580744860032a080003170090200328034042541d0040391915603550b600f080c40f195136482584030542d042c4202620b0030b00888011205040e8203000821101c7c0500690800d50580030006086a01036086510400b116609660044c00070041400c0c03141c000340b0090382d0303404569009002e114400d20920b0780817142d60716024200014103001311039403c11900c07014194800e0f1a0300304189641c101445022040007a0b91101c20360424a050060f104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 202390629 1250 202389379 202389419
    0xc0c0b130b0a0504020a030201080402030a020a0f050a09140402010c1502031905011508071d090406050604141b07060212091c030204050307050603040503250606050a080a0308040302010b04060f 85
    0x103d0401444010f03075402d031200040300e40900c3d00201c1601c403800000c1c02c0050b83c120081d480010101c000130040a49249241110000c841c1d00c12000d90300e0a28905507207040207803088200303001000800560041c0e03203114801e4000c00142d81c008548191440490307100381e0744041030050217200c405604449008503030241483d8241c2e5030030034684410150031100054081c8052000302d4010020307554603c03103034003400000100b00025500345424410018030742503900e01d006031309100d8180c0300b603582c401007a806914840314000031459640544021900003201c1120700580801c07070b4601d51101014500e000c0c401e01009041101c0c9050105203045c140d200320b120515005100412103075402203101400c0360000c2e12181d81e241d45500d0060700b14454103500081740050f210046958070001078284441c18030540701042615181c2c070070007c01710b00911407034607198046003400001078480d0300e00c0d0360468864000800e144002c3c02c0001d080e00c1071608079035071354506501e0812074140060303200c1100c41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 202391879 1250 202390629 202390631
    0x70311030f12070903050d080c0f0d0207021804020a03030c0305090a0303020c010e09011a0d111204031b08070201050a1e1110060b070f0c0e0a050105120c0102100c0c0b130b0a 77
    0x11725690307a140d01c07581c41300c0c0014148150301000550340c1048404692907031080c08502e540c0c2e103421a075044000d401402d41030f8091100701d40340c11000071181000318012900141140013403460359030110754501c91801300300c2c10403509111420680e29881d00140245109402a00522000500041920507c1441c035071007203078103c004010710091481c069601059440e00160f0700d035003190f401005044480c0e0103000840d000a9450158003104050038002c6100385e44d98501c1801f0190241c0034107041c0d03400680349203010090030005600401c0248a0200c00741014407a0b84225000f00042440e40303100030700400e03144020310b03103210700500a549004042c402e082004038100882c00c4401d0180304030051405000655500a0003169007200b0020000700c40ba000785840c2015200c00540821711499005000c00c3d030f2003244201c1c02280403a110601a80208258812940114081c00d110140802400305036005600460f2075241824401d070803049000416405516042d0701c011b6000700030186103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 202393129 1250 202391879 202391897
    0x33010311090603011e150503030301080705130b131a03150711060f18070306021303061a030a0201080a060504391707031118130b06070206070311030f1207 68
    0x617006509203e00100c0600710000f50910101c0b080300351448a40c009651621001c8000605280e00040000a0303807019030b22020280702da0518601034641403d201c4d0380c491050120a0502080c66001490340c0c04120486036070b0001d200040b03030a220480520210140001c810003040507001b080110701c0c2000d4100906039481c0208880c04082e20281003406005003c841030b41c044142008140301651300031908660303070290703207071101c0040b4080d01c81114002e0801e40561401c1d990b0715241c0b4034500c0c0240c007800100c03440d40c1c011188214000c05090030305550315408182912103101d0a8404a91002074055030b190200455000c0c000321039000e00491519151022103543c0241e120718003140c0d188811100d91200320301030b000380c101507020301045000400c400f0700e1039440c2800300c070703640d0303005c0c5c2c0e000039922920082c5e8801e40e015916541c0c1c0116080001c2d0005041c050b00402d40c4c1402840d24000c9030f240050320038103640c8040101032880902250042200c164111180d1304020241000da0074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 202394379 1250 202393129 202393151
    0x607090f0506030a0e03070506090a1209060e040902010201180b061807020d05210705210c0406110a1707060b04090213090f02060f04030311030c3301031109060301 72
    0x2041c4001001e1a06460300c1c1c01208840e035000b01b080c0e6800a603c103090b280b00c2e140038543c0d20f0741c44100e0202501c802c0d440f003001103101406100c541080e514950390705040c0400b400c0c140000f4014542017241150350347e25208461305000203542c92028403444d103c1446041107010400e0941d0f0302110021182201800e21004a40024602c0060420781c281180c40742e81e4540c2640480400038668100009000308010700d0650100c0201095655403d220030304042e184021071040c04c0c1140d00300c440ba8010071062101501501c112858003204800312041a4040e0381c0301c0801044001d4102100c3c4008980c0408200381402410b0300d0790303415141000310740034580004111001c504180340c444d07950386414400780544a501210f1441d00a1b104c2076440d90190300480c500d9105100580018104058022803148040101c07a0b41c592050002c145404406101264800c5c2400270700c281c040c40350700b508100d0880c1d012102c2c001e41c000c01c542001c000c4c0a0041c4031403184001d01c0c45200340d1420401c500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 202395629 1250 202394379 202394389
    0x506160e0f0102071e030b0a061701062d260d1704021519050c010e011b2f07090615120c0c060f0e0d08010e0a020f040b0c0607090f05 59
    0x8110364040d0004440b905e118103482c0c3c90320041c0d82005d00714590784410004803160507000a01150304100c4521641c5040340400390803112103004030208011981c1401541d00841c0c0c03080b80e500b00501000b02e030410781d100c0c0389034010300d40c5e6003280000b030620390b950a210761010700c282c10440d90306050107c5002007003607913425890780091001788200012510849110249c40035101144404005201c0c18514540c0c00f030082d8000c896114800d60170200c201e050448180100c1d01c1020b440303d03045441c0f0415a509480740400d50a40500c2c1c0e4581c20550b8058155a1903522580d0b141c0c0300140c41e0013414081c8800c1650400d03000140504010758100c0452540082030010400c502400002c12003607a00c404c036640780411002400c0ca40c100039524546003159401804040c0200c0101d80c3e080001072816503180009206038000036110320002099001c00e80c000b41039101780e4400381803800d5224100c0c0d0350207800511f48400b0b02d03031041e030070000941c0d0070503109000780c440710b00005152454a80041c2c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 202396879 1250 202395629 202395643
    0x604050606040c0c0f050a0c050609090f0603010e070b03100b0a02102a08010914010602061f03080a0215070e030a1403070609140106090209010804110a030506160e0f0102 75
    0x903001d00c3e641c514090b2007911690a590a981d0312115840614107281050740c1c0e00e401b10501030741e0540e03507a04000748030300c3c000044400d4590081e124a0391542c0d8039440140c00c079401031509030155200e00b0718000c0c1c03120500c0408003400111030700e03503264102140d1040d82d0040a0b08101e507904000c00102004680018403807040b0120680c0104010314a92001e101c5007000c446241d000001d0303e0f907140403040d04501c0680c1640c40c051004c00ca207030b00920060f104180203205020150701720302c0119040001d1462503819040003800c0d0128403903940d6a80355541d41c80b5000880060b0040040d0080c40d01084a5158203e0000c0c0381980301104107000080e2107540c0c000d002002c0149103130040340c8224080c03080e00c60003900101d08105c40615400e10441c0c3d007000e86180b044951070306030080341402c10317071007a1455600182c2d60044142e6a40d612000c40070305032500c01f0f038044101d9100000058080050b140b00c1c0800c012444000800c11501520703141c1c80040e214403a9941e50b410700d54070f903800180c203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 202398129 1250 202396879 202396891
    0xf0901060f0f03060608060d02131814011407080a02040e0c091002070803030a09060e10020405031501180209010c021306081e060c0a180801090c060c0f150b03062706040506 76
    0x1003503104503034400184001d8110b2088040c0d1810180300503070542c0c0220704848100d002d10140003648031425091800c039072a88126010ec0c80003030001c074000c64400c2c408950300080e44d81004ac41c042d224616144924030844030300c40000400280358100381890401001d80300e01500003072155500b040d10072500d0f4000148a110ba0303a13541c4005d0b1301400007a0300029072003490403050b50120b18801484070007075402405282c0c00b03803003102110038000c0b150981290403105a03807840320b000402048040040d44c0507803c4681004900c0c101c200c09603840c003a01e2458003025410001e03c45142c00070b201d05040341c20490100007443d49117a8009408003140090340070083c1c441e40b690350a44d404041e107000740c0d03002008800c031303484440c0032500e254154000f040240c0560020f8109542c2c0c0d030421101c3c43c0780828014180c809442c12413000520090006590030a0044007059040444012910300794080728036045030503c4203404254480460f15030040055042d01425007407506455055507414080c142d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 202399379 1250 202398129 202398139
    0xb10120b010203040e0126190201030911061201030c0f0305100e010e060a020304030206010b360d150e0a020d0f0206092112130e060f0901060f0f0306060806 69
    0x5003000390b807080c4115070190000d44140041c0b5612461030100c0000e0344c060340040102080000780c00140000b90455000182c005041c4420810f503004401608142d041110000105085a2090f58a09001d040e40c0e40c00000001d61940c95420140c116103c00da02c661000180081309201281c0702060b041107501024002191015511522500600e048220306000340140c40078030940108680045024078040d900700d03451a40c0320311110f0864400ca0014001d410114a90300c1d107400302d0030404100041031540c1111010080030046504115441c80031681c11011911101c0090420320410710440f649000824035140554041803040d0f40c08000a840c0c03440c4511a44110b44d68031007180c187c000064404041803400d44050a044a8030210101442c0201c41010414981c05070071798142410100c01c1424840c5000c00d4461900f102601d8160800c41d0700d1020078032034462046060090036140e65280c400c030500b140040020390030b50031032000c05051510805c0115400310209800000031a1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 202400629 1250 202399379 202399391
    0x3060607060b1207060f020c0a05060a0c03030605030f030a0315140d0512070803010303030e0609060c09010e100203041a0304020a03021302070b0a06080c041407050a120e030405040b1012 82
    0x1e103440040050000c3c24481d52801103241540515084440703d055001c03660a04135a0003008091000d80c0140e41c0c00180600c0700003002e5208001560400e8001d090004600c2d8440780480d0403d0303c01d0f00745c96004d0b400002c4040d0215858400d01910416035072507402c0306420700140c1004106c42020071072207212401e6946042c420140070b81c20040785103180c0540e442c0414582072009410901c401d0740803030b1900a0044146501144142c0700d0f01400002d400203a94610a0440e075400c845003060400071008a15100c90304e8032032607070761651f5003600103640390381c60260010b140040c00d0080089200042c03091100589a40401100740d90741215001d4000340c0f8084884000e0003101c01c05000040e00d80f0034404500100d9000c05d0581e2a54000d580c0c031650036801b0b2100746c40500c0c030700d140404007040000300701074820000f030400e002841c13074070080311541c600d8000181c03403c040381e48080340c0002404001d9440d251007010344900e4107864008004007c0f1001605081103c2080820b45032991 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 202401879 1250 202400629 202400651
    0x1703061306180c2601140906031e011104080a0b070c1208070c0602070605041101031802091b070b0603060a09030c1b05060703020c040f02030105091302030a120305070e060306060706 80
    0x15400800e056540d003042d038055030300c0c003040c4102072020b1107909410321000c0103506c0b19040040a50384240c201400078000600f80c50440c481130100100e2440c51550703102c0333030318140c092404001c20040c0522001411954100e003011401c10304050512018008108480c000182c1c44444040c0d100549003081d20309941d92220079980042c10101c010001440010740104002040c0d1045005501415460750130140000054044880c80740b000a844046016144010700d0010000caa01c40d00f160805050b20380200402907007500180c05c1241d80c1210142004024103081090703941c4140e941d40148140d0a10742c602604a00b100c0781e001c2c0048100c400c000b1902078404403010018500509003e640d0201810000d483d046020300c5d0a105504088000b5202242c50080c1c85c1a0303400200030080a8036002d01190021001c00700c220b805015124400c00800d4119104201014190710049090315203550001e115103400e80399140b044000b4030a009040d16580300b0744101c0c2e54810030010b0540711078 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 202403129 1250 202401879 202401887
    0x60e040b01090c09150512093c0f210906030c0c070f06050a08010b04150f0e0306040c050306161d040b04050109060612050c0306090a091703061306180c 67
    0x6410040b486142c840c44415400c1c0d110004000c0761a291f4450740f002c0c2c65411b030301d546840800c0c1039518958010070000201c01c40381c0c0070345440c203d524009415108954500c0a040588401d00c107038250300482d14410144055102e10a408041d80c0c001030f18000c015400151140400f400054081d2404500d990000404000d104041c12034100050446a5911401016075014850980000d2010000003480100d5441543c06031042d4028048210300e001000301d51000112001c00d04000c0030592813550740d00c007801807034040c9004251540b03400e070906003803500c6c01001602e1190701031500d48000c4805c0d0f034041710398155480c40018661a24140c2800900540a004042ca920a241c200006030002283d8000b00132101c0c99201c01c00e403000050341c601c3c01c440b4120380c040c50400e0208001907403403400d2245191b0010ba20000068400c0241c0c44461a0080007950800d6103603002041c05044e10307202d0548040482c2d4080144034030703410039200120f0700448044625045480b60214a816401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 202404379 1250 202403129 202403147
    0x4030e0d02090a0213060302040b0f0f0f070803181615090504020c100608030717030604060306090c0e0604020702150c1c080103030914030a030e04061203080a060e040b01090c 77
    0x103028114904080f400c00b0025032000c0030904007031421040c00908035010b4002d0b01c044608030407039a03040040b410021080f0f9403115000d94500c0a04000e1491881140c9000c0c0107040d000d6544161249071200e080d900d070100003a00185654003442601a00c04203000c0b4040659803516914030107504200c8080e5000c59494000980c894004141c52040c014000350740e0a1401c0c032070000744800c0d545d03418455201d100b1080040d189003403400030640061540c400544d04488064800510b82ea901d440d40c078202d0f800020201c4141030590010011500c1806005070480401c44045242100c02e500141c0303401078800b080d960591005c0f40c40340d100d081c02d110381c0d1454018000044c82500399600300401c01d21003400300300c000c0b17400e4a00100c0c04150149800034440f801400901d00380380350340c9003951114100d1060f20362081c0c035114007044c003880c0c030301d01100340318483d45511902c1d04090080368117640083d04101c14200080c004c0101260143c0c10980c1152000d940024001300051011a45011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 202405629 1250 202404379 202404383
    0x1106130b061003060b0a0c02040b1002060c0a09180b01020c0603090a140c270c0403120305131b0e06150f030a0b09040f2010030b0f1e1008090604030e0d 67
    0x8000f0586d40110380d0004005502c00d84226000c0042c400100104012410840405c1005a1013480026031b6824143c008041c4044941007440e2840d0340c030744022001c068003001c0d540c40c0507102c0c0c000c01140d5030108140d140a020417a0510b0451929008140e96170102601c01361120302e00300403540c007400b824008640c0b0030030081c004200d10801c2310780600c490702c48002a8440345c505c400000358041d01c0c21b0150b405484d4000c2e0783d60381d184005132080f805810082c041144c4540408030b14000100c1c2e0020901040441c1c0c0c0c0314181e42458000d141036509130040c44a40555a2841210a41c5010750b084841504080740603c2e22511891580c1c1c0040004418441c1c0040c20001440280207407d014894054880c1441c00a040141001408075030724a101141d0080030000500305010b00075003240070009009000060880b0b05500011078241c080d910303030803181c070840e0080b41030381c1030900e003070050800e86041094a03800c050b9105507689200620290401101400c1586c003687c0740101d20401c16 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 202406879 1250 202405629 202405649
    0x1e060d020406080106030207020303040e0c0c0703140d090b040303050a090305030a0804021e03070315090c090f06150e0d02040b0607050606090601020703030210020304061b1106130b06100306 84
    0x21051402000290300600641c00421081d800015041e4070034002c40d440c1c50ba01401441c1000d1400e201002c0c00c5501a003c9071081401744078000c00c0342010402c0070002d40c000c40519440c1583d05c1400350500305070245210400c0342110080c80b41c6000801100c0403039905242155513841041c0c0300f150402c605400c0181035000001c0c40758070a503400510399000c0c5000302c0305945030041194006040b900060409074150b040068200301040b40020703c05c400074124100455900090340c1c480c1000300e21f80e000521407036503e250100c40e00304148110006803821100d04911402c02210160096072081e400b24441c414215410045440300e402c940c00d00c11010340a03075210605443c1040e140c02c0211010342c010032a0744c0c00245158030029104040340e8160b0040c1800c1c808448411020b903100031b0041e01c0060b104c007208010000c2c00600c0c40020321240e5924039241d8003410301340e41400f00241504052091036a003450100d80c1040401ea0010000c03100e00c40fa400f405501230740078001e140d10900650b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 202408129 1250 202406879 202406887
    0x414060c030c0c0a06030b0d12031d0f0c10090e07032304140102040f1205030403051221010510050d060801051e0a020f0306100e032e0501050f1e06 65
    0x902c0c0c000031a840c07030701d104032118540b05445200031022a06070600391540144000840700105800304801e103134160f240d1070003044001648a4402000da500880c582681c3d1110205031200c070010f10011866010403100d40340192103d8400400c0805a40035000c51584000003203000310b0f009512100e40b04543c0d20943d02041e5258500041d0060308640a41c0d6080d120f01d0001100241807003190150b61120b540c6048641c2404080c0f2401070b88580125407a1204010100100700e0401031080c0751440300342c840395200702c420070b80e40e2007082880f6801184001e041c0107208950b41d150700d08102d0724280c03410315229907164490601401640d400784449518140501200c1c0030030f56080403480e021901008500d498070240c2d20100e119003922082040c0061010405501d00f040741d6100052052801c0e5090345400340000c0e040500b882281002281d10341240d41e406c540d50f07521028401c0c046803041003a50f00d08004a109440c140d004903100e803801c4d078034401c0070b40c08441d00c4140000001e0600384d12 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 202409379 1250 202408129 202408147
    0x605030105090a09080f07020604050a1202120307110127170c030606101107030b0708040308091f020d1401230a0621090503030702070f06090303050414060c03 70
    0x41584280030301401201c0e4a00003900c082c407640641e00c0d050b54480710301071509840c4090701089403c201000c076400a000c0000045a551301c41c0600080c1403148421740e06c000715441007100e02c2c0300030503012500c0d400512004002c036040a91500c1480801c1c20016050414244031203c0320041e4001d44034084013a070300c041030074920200700030210f42032070301221042600c407410599184000c4520580c803a102498800c6c41c2486000142440101d6408540c4029141c2d5100300d1076a1080791020001018401080141540020307090740090341d03034003e40402d00a85000d420081d5800700f0528400d03400180411b0101402d038881c1c000040145440c80e05075031a0b10f6080500ca01c2041c0010700012481c400a1035461700e80718801c101d41198403880c5d04400300714600c07151080e10b020486069a695040140420000c0c001584102c8507070740030304256410901412a85201900000300b081000c0e0390500000760420300300c405681d92100c4222040407003c000504901c645c1c440310350307913000c04558204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 202410629 1250 202409379 202409387
    0xe070e1224011d01150903050604050a0c090203010b0d050c0409180210020f0604030c031701031b080f0a031206030f0b010f0b0304020a09020a141908010806072c040606 74
    0x14001c0048106021566641c1100c08018651440e6107031002e203030b640040024890021206221945034282111500e03a651561400c0040c11181500d1076046948074508101c60001160080c10030a20114290b506290341e42d4810300818008850703156035a400f04402c80c6140c0151170042090603414400030300c070030060508580c40541e0407402425500c2c412081140041190200c08024100a140c01ea0759500d04549400041c181038003403181e0100040b030b080341d4404407507010758011513156015462284010090b94440d501442850300500c45c0c441c40c418000c29525050354262a0206960f00d8030000ca000a054640c0010303f0341080010a2042010380400b041c100c0c0c9111014203802d5650703040a00042c80102d400940c00303000b0410078803820707525a000d0030f500d1003503181150f046023480c4200c01c80340d8001140342c201042059002c115883c3d00141035030241040d00e020300024180408081d0101c0d195111410aa9154019900c20070350300621000c0c5103100203000b400b2050355500702030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 202411879 1250 202410629 202410673
    0x91f0609081209180414070b030612010908220807060e03060a090308190b030703110307060e06090919150303031b0f030506010c0212100b0a0e070e12 66
    0x301c0d50140340c1154030409108070555400b90b40c060007007000d121411111060408009104940d10091112a0b0a444a00704030407005001f150340555a1307420442c0810050001c3c0c210701794201c2c2e0400450100140104007519005001c01ca80d0030403441c0b25001030a0380c04001d400c0a440f9100e82c10f400994150b00c12942181100c06909503502a11250882411f48291a40c0034000c0b50703500020540c4141031502c11041800402c2e000a8401d9000c0300180c142003c0c0e900c00e03900c2e8119510f1400785c0e403a06103c4140188180c1c00d1210200034030502051190082c04001e5118203040070000e10b13024070f806801c010742030380880100304a080c0c7c0403102840140718042035002034503040e1103142100c1041c003050800185903d410040c00d0340c680d0128013070400105468100b06091005000603190b4103c03c0400c40340c0140604400f10240421400720360030134a0880c46003900c000100035441c030b0118059000a950302d0200b001032000c5005c28400810500300c114284a03200e0690070101482440c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 202413129 1250 202411879 202411889
    0x408030402040509061303050a05070506070905010311090a0909020103090c06050403060b0a0e0604091b030305030a2012060d0206030405100605040b03030909180a0b0709061706091f0609 82
    0x1040f46031541181d680c2d44440445150410351074001102e40482d025102600d55005540b41007850500c41b943c80c05d06151040c0c0f89600456643c560a000d55a014000c01c0700c8022804d440c41d050088013400507512281e54400c40110790b590301c101d5010b5901c0703900304490140d08680d0503124980c1d501c0c0001e00540c01440165811450f100d00d0600914008003500111882c0ea203c2d0384850f00d500c02040010038400c1801c07180c2c428501c036003528200c0304112401c0214007903150790751a480d00524100a85906d01c05003d0000414a01060380480c2c00e07003aa80c2101c0d00094045866030b135040400e03260010707090041d500c030f80040304110402c980080d000351030024802d01409000d64840c14442a50041e2001c0da6054009000b21820781c103040c1003459000f1119043d034802a010301115a04203c1c07c440c06070740d100101d030100011950000003c400a050a2900c04c2c990300c2020204810340b030340a0f0285102e02d40c035002007a800a9280041c0c081050310701e00e40103d0036542c910180c241801807180b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 202414379 1250 202413129 202413131
    0x40f14061005030d09030305090f040f021b0a020102030304140f01151401030b06160609080310030b010b1c05180f010e0c0d050c01210920030f0d0f0201020c06040803040204 76
    0x8162810007103610b5298440b1916205d104a0850b5800e662581203065081c0e04902c009120b800396903a0340c06070112003000c041006035250610303104039020507020210003034594040e520b03280041c0d9000044070350154104141c1d10300c0520540d12507060503401012019503608040c00388080c0080031042d081168807e48081c0c002c00f0300c3c4070065060711741030980d2030360000307040c00702e0f103204030100080c130080520903000000c9501c240d68845054ae0420303a80d04481258000c6e050040042244d13205001d4402100000d00b400c00d003030b01000344c1c800710000c42e0341c40d151148089003c19038201140d0718124400f4054034070950030b1102d900e008000b82e4041780c51610075542e10802504280b5070441107560000003820700c2400b00b500554031800115a11005100178240303910160541d803290221052080009c401900d441d030a041c500b03081d01c1e048682c441d4000d01190b42c1c20400010f145020f003140c5007007a440f038510024041c3d0090141400802542c042c0d00c0c07c000800000c00d0045201d9442214 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 202415629 1250 202414379 202414411
    0x501050c03160f080103061e180501110705121308100516031808031b07050109020405150105030a0c110f030301050a060906080f0a02130303020a03020111091008040f1406 75
    0x4040307650b030f074004010f8404210b85030014400710304640c0140807a01d880010f0945508400e440070030440d040c0008013070441c0b80b12020070003000820f000718200359031701d10607640c10b0149503141c0d1a111041ca21b04129513a40016407207030398268900d42a40208200000d448640041d01107100140c002214501e8201031400000c626081c028400d40b00303c1c501914914522a00c203603155811580090700c0c0800a444241c1d41c55807075441d00000f0840c0c188600300100f00001c03544140402d0300c0c40903042140b44c01b4682c801d066680d0303002c8240e079402909603801080794082c410050302c000e1400501c140c40c038014582c1c03411900714008005d5040f00c50a44000000d01e6403005c00700c4141080e40136100c0003034080c4d8041010381450000d260b801c038142160051402d91a89000c00303426002e503104030f0160b000b08130660207068080c45154003400100241a19000c00c5100080c90942d55560341e90610001c10040f50900103d0a1010380031580f10348800340c82d650458800d40c1d5020100c402c01c0e803100942d1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 202416879 1250 202415629 202415671
    0x30f040515010b090415050a060906090b0414040b010e03030d0e07050a05061b070b0d0b100311041205030d061217070c0e041e030e0a05120a02060a020a0501050c03 72
    0x8010700d07040310b00480074035042c02007007010840901801c400354507814078101da011403a60354400f00d580c000c1c1500d4664a07000da00d0000040c4c01d0001e10707480200c4c000c01c03c0c4010403800600d00403982c03403141c08440001d0809420001660841c04600740c0c5070b01440080b9400e01810100d5000c20112900801104c604a9403041001003600c103900495030421001e00003241038192090a01c41c4241048058070320076925440d0841076500002140d00105403128440301c19410030f400d0f50503128007203180900c40c0d02d12052111600303104503c550101d2515a039211000d110f0140151103034081c1004040c014250340b614001b0301000348203415240342c0800800c0b1b88100030224112200c46030b000c402c03c003426280075440c80740000002d10940b03a4000c2d0040035030000341d800e644074000c10f100e13443c0d08002c411040305101540d01c4a400c060700419100f0128a403910340000c07800495503040362955500c095080007242050103025000348103600780818401307004040c4020314401c2d81000710144201002d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 202418129 1250 202416879 202416913
    0x12030c300903100e0f060a05100602010c140a021608100b0303030f061905030102030708160314150a050613090b0108071b02060f0d0915020901021b0301060506030f0405 74
    0x410100c1da040c3d0007002e20900d0800550841d8044810131800c1c0c03010075030340010072801c280c0100c0310003030102d41d01c20801407558101030240c000780c44103200030002600c0031070014228000440c8142c82d900302c0450703110f800031300c00c010210f00c20f0f840c180c180d42556501d440081d51800c0940a4078030850502e800308103541400415a0b204004400c10302c01d4a44074038003400551009280c0440106110303400c00f18131521709000450040d602660b440d0403034076000070402c04103112900041c1c1018200a842130a900c4200344036600a070883c880050900c06a6000440941040c0d0000342c109001040565612484c06450030482e075078844240100c011010046070428405c581a0300826245000603c3d208401c1c103400203201c3c4083c008600d858000401f00f00d06800200d010f1031419222950b003800c1042856115115142c4010150304001d00da00010f926070720403c1d0690f06030b000c4d00382407110f1a03809400c07017002403001408556480c103150f040900002011501541c1511075204885008030f1742c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 202419379 1250 202418129 202418137
    0xa02090d14010219080702061b040306110405030106030807051002090a0b0705010f0608010c0908030c06010e10090c051b0703030e060d020d050106080702100c0503010512030c30 78
    0x302510380304400c0d591000410058003001c900c6565080c1301020560651040d1090704e50342d580c07114003c500e8540d400900d0102e0003400f019050000741d4140e04030014090584040c1e1741c2c0841d010882d161000020412402141c1c459a411f44c24030400006106480d401005103a0143d030540d501d901003040003000783d12401d2007054104000d6003081129608080107032650138810000400d110b401100c500b4151145908140410f07595004103000d8690032810700e0001300100f00155082c440842c0c041600c0e14014805e4441c1d0f940c400d0001000041040040c1d009802a004100324950701148000c0064202850003e5105013140c0007c5054000188000031282c0c9962140750310000541807085982140d4040c04040b9024840f40307016400900030389010f06282d50f00c4200302d02d0320750002450000c00608142a10b464007c00c18031407680102185e040d100b00341e03401c2d010001c020340314610b98031600600c1c0301c5500546940308001208840c1130100c00c0514007404290311030840c0d0205442c42 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 202420629 1250 202419379 202419397
    0x9120201090b070201020c04140730090201120f0501060e010c11011407051903020606190b0901050f0a030501090f140109091113051e04020907030e03160501020702090a02 75
    0x12001c5410058002c00000a142640c41803050313440e0515610042030548140c50380b080076000c46041005041070f03000504070444da0341035404140c072210641ca88000060300222102e030482d11000364500350b900541004c84d205407484400c0205410f484c0c2d115000300b100303000b8040040c0c04081881107a40c4074a0b08034a003990019101c641d03032520b070340055400c0b000d0801009040c0405001283c003040d81030081007002d000411a6030956441440c00904084004001c00d00c039540b4a282c251078000c5441c2024281c83c881c1429985d1010280300580e42401184a4610800000100140350b6503041d00079a040f82c030719000038007a15170212942002d0f02d02c50307079072202d1003000c10b030040000180a800040000d4091108101072005880100352200b0b1700004c6184115201c0c000e1150511031007022000007e4404c00349807072818140c0c0000c4401401a103140308050f1290392805144a090044031484c200e01442c2100d134004600e0031a001c0d4200b01c00503445122072000203a44803803203008607040e1315 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 202421879 1250 202420629 202420637
    0x10509060316110d081501080f040803060d0804120b01050405011401050d061716090204060e010818011806060803130501050c01090c0f031202070b0a260a05040309120201 75
    0x69611005004642000e0401c207042000f50710082140e90418400440841c2d101d65440146150003900c10030042490f0b40040d0401001e8010084545080c5880342d4000d54856403180c0e0b01d48076080041c021880c40003000d003030341d807000400190100c842d2048200c81031140707103901d080c0e80e0b9a10811040701c43c2445000c07010308602c009032061758420310080101400480000482a44a2510b4a2090b500c0405865a940f0600401c84050b07112180000140820b0074290701c3c3c1810114000c000c0c18545a40324140003003d0085000000304c8074aa800030303c01e200080041c044035900c0300c50a040c0f901d10903503000740341c0ba602080d400380120031180300402280700f90041510b00401100c60390b100c140ca0491656a61800d4000588a4482c00000780b410145007108035003182048114400b0074681d1405641c01a40d040107120b60100c10f8900a11039402c00d100340380442562049488240c80d40d8a2a1201e0301c010000400c13080d0b44414040d50180d034070440d4980c1c445414080080300014040c1c081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 202423129 1250 202421879 202421881
    0x41d04051b0a03120906020601270f0f0906050105100309210203040806150f0d12050c1002040803031608090a0b040c170a02030105060301020a170402040b100207060e0105090603 78
    0x50404501041c00c510016040e01e011580d640c5504074400411500040000c00c0c4050400c099a41000841c0c05040031101c80703500c0104884000c00e41151800c03040078025103940c02414659a158080004e1070740c002d806000c02040d9140c044020031f802d004031440391040c0015500d03c0340c4a441181c0705590300001d180040f1b140c400d00c8042d01c0004203007180031444200800f0a4041e0f0a104040c041d400000060060951103410032605584403155180118100f00700400840d0348036061140c804000d04000743d546014500e0035082c0152032010264071400080c3c0010121400002503100d02c0540b40d20480105032504216a0348000351035100b036a0740b00b030006002182007604601e4100d4441d90440000c40d60b2004480c0442c1c2c411580f00b0460740060004a007503003001c3c0505a4001c03400c0700210314141d400440074001c040e28512030740c0907000c0311000a0840d242c0d1f50022104040003440c111846000660095440c2d8842c0650300010b0b885070601c0640394019420366242000003000b19084d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 202424379 1250 202423129 202423153
    0x70602070618050a020a06140306120708011505040501050312190302090d14070b0a0c03031d010230060d0305130b13030501061205120c1f02041d0405 66
    0x103504002015200c01e42d0b1a03034103040502c1c0301081500e8681c4100040e00d940040d0740108840844654016024071414a0004299020b48030840e940910100c0b00080000c01c151040307482c0030b81d2908841c4440d8641200c40c4c041e1801007841b85e084510864003444503030b88480034542c46017a140c08000200ca000d010301c40303a1000c501c803140caa1035068680181000c01640024010205800b03040d10400c41d1811b503403044c0306043c00280d02030081605110700d001110240144814903214000e42095598210f040016440003044a0000c1084009548401d9107001101e0f041301d00f1402099200303050383c202c61000c1046c1c0c150b20701ca00c900030200040e501e00c58505840507484841c011400c2d0380c20280215120b841c5a01800114510704116001c2505529015003102d1194016026035070040d0107000000740e00003403010020b42c40502442d1201540802d151405000640400080840d44003200100f001a40a0b104682502c594525003004569840c1e04c0076030f05880140c00d0380c1010800d003a0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 202425629 1250 202424379 202424381
    0x19051216090b030a023307020103150e0601110a06060f1d01030807030503060f03151f03020307051005040806250503070905040e1e0d020606091003110105040503031b160b0706 77
    0x7040c1e400301b018414185400d0b418000da070254481b043e54410702d01251020030340d41d05103d000c884401d090384664000381840001900440c00820b102c2c10000c17141a002d0f01c80740300380305c0c1d0300703819920500034800580c403017020790360303090b01d40c0602041148802c08903d1120409454141280e07003000650b072602c905174400702e416903c010407654001c0041b00342e107001c070740f0100710380780460310000448505828010780802401800346c102070545030441c6030030700241c1c2d00820340c40c0446000305d03174540342024852000d442038003860344402e807180900313010003441c0701b403407803c03200c41c01d421241c121914501c50000351154001a0791640c0011421b0a09000d80c3c10154008100103800000701c41d0f8604501d0403480c40b00007000411052904a010002c2010740c04000598214a0444e0041c0301361504c07800b0901284518440034001c00c00c2c8514140c4c5e03690185003194050140030b001c0c0c0380d484840074002c00180c0d503090300c0c001d01449800342070f14112444403164000d0780c281d425180e21700600c07522024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 202426879 1250 202425629 202425649
    0x5100f090927050120040302031225080a02160605030a110d020f0417010e060a05042409110907090611160f0603050a02070b040219051216090b030a02 66
    0x2820b14410592118072404011140d00c581e61052002090860400814080e2143d000c558942c11210074442480165004a1720581e0020040003542c0c40315060b2031022502c1d0301e0304202e0344030074403480d0305c00d02401034900081a070078521390200c81041c003100c0360810000605100f0540055000d1000c180d001425400a00c032032142da072855070500d007410301864100da2200d0b07010a071404002174204990a0788440401c0d40070b00820003040424540551540c076040d0007401c1407010707917236000000c0c00c00c0300d030501c1d00c05a001008204007103090b0020820004007c0c0705400e80716680104001c400900d059000c00344141c026603070741c603a003520b0071000780c0e00004100c00b091042d0007a0360f005001821111014030080ca1070441c0ea0003400d00e08076015048950262407124014010040c180118003080030403600150b043c3c1f13944101f941c1c1c0c0300106003078503c25008242e01035000021100d2103280018048070b040d0b4070381d820a480c941e58040b0501111004201c1c075070140c2181c001400580360000c1c40e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 202428129 1250 202426879 202426901
    0x17060105031005060d0f0c050403050c04050702032203121205060306160f0e060304032304033f02030a0905030703210203132c061e04090204060f05100f0909 69
    0x12517040300c2a1515420394a1fa00089000120082010014001d042200c4600e500080e1420002400c00a0000f9145d1103141030759200807089a00b008102800c1c410b604004607085074400c51003580c0148000c1000305940c4000d0219410700000c079506150102e1000c1c0246000d9031241400207030200280ca910100001e08824000705c0070342c80003281c841d04000d6200314403039078402018850401d420a044040916215486041408188005401d45000f2100b900b203005800040345110300e9001005090214200c1e000310a842e0301e00f40309500040074101300c80c4035458000a8946034414103984194a02c0007a291442d8010b08a4110102c110503045070a00c03841507038603010485d20400e180308101e5225103154490020301c01070341011840702c540408211841000303c1e0520380e000030380101224500d0910703800c400307a0700c06140c5c2d500d80c0b12541965010f0014440305a0f2801c0040f4100d01c0b0307101d8540a0381e020860380c41050701c20401c80c0225440364076860b1b01a81010025002840416a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 202429379 1250 202428129 202428131
    0x9140601110a020411030901061502070315060810050a0c03021c020c071203090315020304080a120216050303010f06020a0b04060c0e1201020a02070602010e0a0303090c090203040317060105031005060d 88
    0x40e07074003d43c455004542030504901e40041d0789042000c0b02c6421220180d000036101008400968038603076001c1124822070381c10000410418602ca50703400000c00c06a400740340030b172041c041180c0c103118054024600c200302408081026545007002a000c3e03201e1240d0401c0034091002444c014040309901074010300707200b64201e6080603220a04050034607043e00080d401302d8101e4004108010040e140c2c101c840d5070480b000e41c15070401d9074810006000e521446014848014002d00c070085442d415280c0280068044428001c0503080080d184c0d882030040c41e5641e039004030045540f900000c4c1c0000c400381e014001c0081d075035a41c0c9135600106800c8480108000303201c00b05022503a02c95508008408030340d0001640c5025a410281c68201103500140569040101703000d100c0e800405c48200d0680c05087c00305410b0801d10700080070543c00d810080b07860744040240818981e00005506100f50080500e9070151160401903886000c11201000f070385c40034a10501040c1000005442d09039a0448 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 202430629 1250 202429379 202429393
    0x302030c04050409031d01140304060914060a1d07060c15141503011a01050a0f0318050a03091e092c06060a060c20030a08030709050a0914060111 64
    0xb000505440100d903068000610308145041420800d040010100340242020b258280500b100000c89000060001d04045d80d41c085560178040c2d05c1102000c80541319098612600e02000b000005007001d0505961540180c220704480200002d21b101c1510150f0303c0c1c802c1c8000d230550714680d00310135400d41c2001c015143c0044400071501805000c2c00342180040744000a0000c005142c02c6561501c2d0220b070701c0c1000a404003040c5d8000049030702d6150140307002d441130002c0782001e60140c001c91200f0303207940001104031024824007250250238903101e41c0c0c0f5034401e41d681da5045004181c103038002089841040d1020031508041d94043c0201d06185a202c81020102504098408090a20440c0d03a50004006c10181d40350811000c00034000d1420940c0c2824015111000384ad0340072540c4040c0c2d02000c1c10f54100d15a410841c081c0c007035602c20b600c07030f60343c0c50b1011005021070300c5446194094407800b640855814041c0c040c0c0c44a0f1000c240c005520341c1e98420046400f06138050f030700001c074013400c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 202431879 1250 202430629 202430639
    0x3091605031e07031a16020105130602090a030b040f050609030f0a0804031b0609111002100b030f0703080a020709020a0215071101020408070302190e0708070314130203011514010302030c04 83
    0x1000b81042d84190040c006541c0b420050306c2d0b03100407640e4800c1e0700f1039241804010540e101040c0ca80c0403a50810380041c0c4511754180442c3c41c09102e81c00103040d42c000c1a0410082150000301c02058611460580383c0985403809065580c0c001c0a8a01885200501594110324460b5000c2580f090207480c009008250303112000f40c003660b000900396019a2180190b900f4040001c00c1d0206814040c1d403185a04c0c158441e0003502d130b5200400c501101610342803844829607081091000d14141c2d0401e6982d00d513600e14003028640d000b405000050b000306800000c05140d288203442c2c8965194001c1d05a1240a10f20b2070030700351001300b802060040c83e404015001c84244040c00240c408103006025142c2180100903038082d2001d92801075140d80741040c02501502006290007140b2801c0022175520703000802e034040d05400049418010301c1108201504a1a100f00fa1600b0300903002003001400842c056401c5050703500409010004074040c0741c407154426802158001e040190480c200354940d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 202433129 1250 202431879 202431893
    0x1060512090106181d060c1c0f0507122d05270d140903070b0705121303021816050c070504020c010b0108100609030f08190503091605031e0703 63
    0x1131894071015542e900001007009002e84d8101d4210a507070340003401d4030300e40071141440d140f0500a41b071600b058101316090416409410420185503003100070702c1107181100004106940624000300c400b4100001700503031114014060000d84202e81d8060560f4042c48c0291000d450058040003801081303540b00d401c0c0142c2c45c1d070000207107510100604102801000000d000c1d8505200d4680220002c03c03030304409a400203140c100300d40d0000140d0f6107030491030810340c0c02d108030f408108d14101c80018244d40787c0340104a5010540b4800c883c81800c243ca1058440c000d004102c4030301c001e0400c40c900002a81d40a4005001003458a20440710341648034804a81682c0000540d5200c580d11826189072a6800c0074072550320000100c0004e035080d10f0840005d103500c085200280407069800c00e200c0a1003c1d81088a00760f40f550b07500d1b8580401c1c24103008225510450b10181c40780510b41400c4802c0e05021032640483c5d10040017840300c240d0f2101c040c80800c2c0788610403482482031860000003e050307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 202434379 1250 202433129 202433159
    0x30d0c0b070c1a0405071409150904051011090103050106180905180f010203070327080f040308070507080f03070b0103080d20040302010e090108101113030f02040b010801060512090106 81
    0x21034400b400c24981f078041c2050340c5400c0a00028425a00542004103440e20100060f005120440d5400304d25102e50034440c3c201200d480d40c01a80038141150b000c3d078800c0d40700050408503400e030b03003c00691380c1e5480d0445049140c618683e0814050072410030013141d05410864000361602c1c4100302c0340c1d22040303000f450312980980001240e5008810482115094800d901c0c030801d0320030684c040804000b21054010081810062070100302140310382e54440c00d6003e035070182d580310105555072115402c2c1030b80d41d075400c1c1c429031005119a44040e1507080001c01540c0780b00e54410101e4980b41d085a40c1c0c107409070000c2c04030740f103140d43da424001102d40c18480c9040c008502401613950365401c40c000108011061307843d0601842107070004001000000411000514400100140191461022000504c5884000c00c50341d16480404402e0000005c8174209031442242c04005a07681030f001900c00d175000b4030400700420001d00040c0c001c4070201071090b521520110002940988440c010301c0c501d06 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 202435629 1250 202434379 202434383
    0x40e13031d12160905060d08030a05090304091113050f0f1512040c03050609060c030c09180115110a080a08100305010908040509070311041403030d0614030d0c0b070c1a04 75
    0x1c1c4007000700250700591103040d4010105691947d0a82c0d60b41d103c013000c030311000d080e95003890390b0350b0005502400c05006990103404445000e2081c440c8002488e00190029640d03a96068040d00c0001000d103840e04d04043c86031030143c18854400001801c1011041e0b02080b100070141e0104806482040407810b868030891103124190744c07560441c106a0300e411001006904c00303a02c070105020340901010282c0c0c0d81320350129042540d44840c200424441007903c858014003c1c0360030700101d80103407808005880040259036140041d44092041da50702c55000b080a8034075a420407060080c0c03031140d0201d907071004a521460a00b1a520303a0b4090844403440020f4a03002c40c042003e110620b000b03050203401c1030b0300745418010700c00b990544201c0751140381300306e080c492500550601c0544041c01a164117088221003007240300e5450320f40c80654440801c02c4c81c8640260044441c00c0d500500d410650030f50014071b1284643e940e600d0948885440c3e034410346813099262034600c6900441340542d4442c0d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 202436879 1250 202435629 202435663
    0x6030c03050105160c03170402060705010e07091a09010509060d05030f030403031b080606031e0a05060f01050c0c060d09050316030207120b0402060a0e060708040e13031d12 76
    0x710340054001c03004500a000c51381046440354070180425884a5503010900340d580e044103a036100c61000414510640c04001d08a5003008115032900602040440c00c98100034014400c03040703411030380e1521f1104807600d00e5215440e140140b2850902051440c0e104001030542405200652145031854011041c00380003481c0000420007010340c180240e020301d01c1c85800a2400100c0c110000e40660070081c4007901a40380800007071100030b90340c03207098041b00d40701001c4010740c1068608200036180444040d40112824038100d84554801c60444040c60540d10142c0341920503201081841c1c1e008499100030343d0749a0541d00d022503014801003034402e9010850345d4803c0c0035440c0207414440503511640c407891006480380086240c3e9010140d0050781162071980d500501403003510050500d9148a03040500401c080041024242c000c00a860720843e24004076900d003000c00c0da0304c95003030310300030001060000714110b8584407921005106c3d030014841041040350100940c40c240825102c80044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 202438129 1250 202436879 202436881
    0x303090a090204091a0f100203130801061a03071e0e0a090906050109020f0d021308120d050f0105060a0c020a0b1303020a080304061713050d110d020708070504020d06030c03050105 79
    0x4081c1417044070340c441c8180b02084120384176000050340b24403107103100f54050442d201d40e000e10f05100b4000c03900b000311785d44102c22095407280d5146008102d00c1c001e00e808408171042030b8400d04845415648520040c1c3c0e04d03200301d04170308890161480c0c2000030180c140b00c51103580189a55130b400180002e02604100002e8185213424608182c3c3c5060b0310080400d84100402d6110900050403140c4103582e8440140e5541d50440d007103804070550713034030596960040e400342c0034544d1548401045100e4030050184850b480e490b60103202d0300c0d800c0c41a0741c0d00042c10048910481d01a15004601030b000504d00b800c000e81e6103c45035007551080d24a040203982c0d190091045181239014500982a01c500450900e42171190280c1002176860034810b0350b5400700c0009643d582c0401e040050340c0da01805131000541d1078400a4802c80000b8000b0b40c040c050082d455003018800101002140c550800400c60145001c0a20002394000c204da098074945990340030003c119450783d21001540329030000615 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 202439379 1250 202438129 202438139
    0x1e0309040603240603021c080c01050901021e03070f0c0221030d1103041502130b0d0f1a10050c01060509130c080a0308061009051f090501020a080f090303090a090204 73
    0x2200d80c142c1080c4a80f901e009424405a1502d40c025502058042a02c1e81c080845061161450103031031030441c503540c01e103020407491002c1074001c0c289400c0ca00c00d03e2000315060310342e40900360004803401e074000340144085003605032240c40002d01c507900240807481001036007501000d80385403407403401006074800102c0284148603481282148124004810306600701396494084000e00c44032020324840c2c0215110007106540100c1c0c4000b0b040c0900382d255140554141c10300508404090440100d203031101a0001e2884018440d04000009102d0f1800d4201148203540f10781100741004100d40d40c5a070045410703120303065410b00624100708505103016031807500340e00301180b03038120303076965001001c107100001c1d004a020340d0845000c039080007040d07a403520100d609048581c44564060403800c1000002c4010b40490810859250781c0c00910030b48078001660380f92443c0c0402000104100310500000d640c04014081c11040101030702d190000030b40c0060119620b681004e440c003580020200302c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 202440629 1250 202439379 202439423
    0xc08031006180810021806030108071e060503070305070e100215100b04031416061808060c0f030402040b03070e090106080109030905040f0b06040f0608181e0309040603 74
    0x48610048800c0c407050402e150305440700e04e01307452400e48a8002c2040d11101007040842d24050101902c065203e680d1105d909903a0001c41c41189009207a5080c003024030644081d07440140e85880e200d143c40c584510108a008020040c0a00c0c10271605207900f41c113980d5050544900c1e40b40503801400f40b42581800108010740240072a0b2400c0c4010f0700c1000540d55500981d8120b98001842c4412001494a071070309114007886140240d010020b0081141e58000c1101d42c0e032031441c004509403081d1034428162369880d00b03840303900341504288070003004000c1c154001c42e4058805080890059455000709203048044c2d0171030191410600100b0100a8013481448001c20020f00240030011076910007804025140c0145401203031a8400c5155480164002c2d2184800c00341c146540c444d1344042009000e80280501c1c00041c1230300002c82c01440000035081c2e0344424800c00303000880c20001419406a0340c2884012040c041070084041c540d546205490003140103000c00c52000c0c0400035500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 202441879 1250 202440629 202440647
    0x2031003060506091302091b030c03010305010b090f18010905030309030a1b15020315132403110d020d050114040b060909073c03030e1e0108070c08031006 68
    0xa0181400d0410082c3c000310040c0302803241034051f940740c2080e844a81c410704000e000300c8243c0c2075040d0004240554850070b00c00a41c1224044c8008215510021081010810b401e60b0008402881000407480c100b600c1c00750022a482c00d800001210140d60365103e0564100f1200101c01da0004901048a40d400c80c0344010780070102090124400c0465071880044806080240d54283d404000202d820484600c03101423240020804040110040c10400107090b04a01c4101486012090481240405016a02901c0e88415580c4203408004140903c1f0022038000307a901c02010f82c0c00340d012650030712450001d1a0304030707605039061905045c03284450001424440c01000f400c0308201314a00041001420b45459490b20b4448829070040c04ca0f0724485103400405991030400081090981a411141101d01c2925015240b0200c00b04200b00748403074030500d1451304080e400d03841c0307550700c41c4000039401145820010725614542d250308955400c12210118241509a0103004043d00000f640d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 202443129 1250 202441879 202441891
    0x703050c030f0c030a0902180103170f16050a02210c1e100201200d0506010509060a030902031e0c1f02030414030c0303070c0603050603010c050a0e040906020310030605 74
    0x10351950400703144100b0440c0000701102c0341e0280c0440442c016070410340080305881d4006113441ca2109034182000c88400081c84110390401060201d03400003041402501c50211901e0030450800f01c803406020010701400d00d003140c2c1400340c1e468a200580da50080d0a078200c642c6030104079400340c1e02d11785501d40b15050b10388034801d0404e0040901e03400d101842035101a401034562034a03202992005901400c0140c5020304c000b04120981001800762202a2440366044881032166850300f100640d5107100c1c5040d200c0d00003608100160003603000750040100644043c0440b03000c001803000a8041128042c03070001e41d40c2115407007491924010a0f9681503034454100c401025000c40790281d6248101d114081d003d00d040c4110300c01a036010b001100314440042d0550355150114540039243d0700c1c0030b0103a030300441d01d17000203e00182014880c1021445d201c0e190f80e4504184601d0540350a0700c041e00c0142d100d03444094000006015001031801102e0395044120b05070700314500b000c1980c4005002d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 202444379 1250 202443129 202443151
    0xd020111040b09031203090309030c0a0f0618260606010305010e0115020c030109030512010b070b0c160501110904060905061804030c0803150120061609090501030803070305 76
    0x200303010142000c1210102ca0310b041519580302018800300c3d06024040300101a0408040100f0007002c1001c00245000341c400c4050310441e000c05402c108403075129026094500500e0f51084c07110341d000329140070a15000e20320852000f40da940184a013403c200c020400f8030107035480204a1a03004101003608210700f4201070040f9030410703541c03130340703481d414801c090114907140704c1c03045100d000b8041e00003099006002400f1814041c20054807070360110a510100030f500303d00001c0c4803018902960502c44d030210349400c16465280008206410070340640b501c0ba200c0004090001d00b0901c26220200f010038084d5890740007072010007040701c000390b1001c060b260401c0c08001b003907680c00004003461a0003405c0704229807a00c5c2401c0f64103030b00070100105240c400000f0303c411080d12000c1c12140038004da03916501024401d5042c0c0d042480b01101200941c40302d40400c001c20041111504a80d1080c81e282040e19590300314441501d00c00c0e80217a42d400c1c03000040c48601603041c0904c0394440800d00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 202445629 1250 202444379 202444391
    0x70203070b0114040c030b0d080a03020903031b0d0f12050a0b0d0b041209081f021e0c060c0a12051b0a11060903070803010b07080409050c211b07080403230d0201 71
    0x101048c081c075291a03004140c0c40e80016080c5500b8081c0e815a030098001900b1262142d0702c5c19040c2500d10300825100c80315120300070720740d81120710074081c03110036189542d100b02c2e00d0350001e440e03003000e0803019110750682a1104008410358461807405001113004441c0021541054141400f60f015041c40c40303c20015400300500c80d02c0382c0000e4105910056441306503159100f0f07140c6030020301803c040380c0107146015210b208001d0b00c100140103e0001e107802d0b50710641381c005e00f4104d02e10640c07285034042034000e4804800c8403a40d0b80519070010440c2c10074218541030540800032a4841e41c44c0d00041100d114192200c3c0004011032540401140e0066207084c43d40e071141072540c0014031400315001c50004020040180040595004145104c414001401c0030000c4e0a0940c211032121805400310000c406000300503075041e60b0040003500c4440c0c841c54111300c4401096405050b0690300000304000c0000011010202c003c480290720790000d01c5120710703d1a007801c02c81c0f44c100d00c9085a040c02 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 202446879 1250 202445629 202445651
    0x18070c020a062318030115060f0309020f130b03061614161401110412032601140d15090212070f211b05040605041e05070203070b0114040c03 62
    0x416540318a02501072040e071902405a04040560101084c880d0154200030548001c2902294104c098030440d4032004584001d02c18104c085508514000c2e5004030020020000c508151100807080132602c140450102c00c0240070a10f0240f040d113034942d00c100b4407000040300581c42482007106001c1641e0491802010044d04072000a4509015103185070021a85200d45000d5121564415040304059192035498003100381d1031003000d405801091004044400c00c4820803503000d00a00103030054000e0f82d00340f440c1d40b025800411030164024010400b900045001c0d04600c10105031039210105061805105202e07000e4501c201642c041e61000e0320030301011200720440d00940e2000c110301107840031400000d40c180081d0718005441000301c9070700c0c15070590480500e44107445040d141407203090341e514144002c840c4002441c225020100c04003ea880000d904282c2e04800c0500c100d90816084d512800d14420082e400401d030414401040f05440c1468000c003480c080c010700f010000c40c0000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 202448129 1250 202446879 202446917
    0x15030402090411031e0304060305090f070b09040f11090f10020c010c031707081f0b031501050f0309070501020610060206060f03010f0e0105090f0613060b18070c020a06 74
    0x900000c1c0320034a40c80f2210181d8a0030049052180e03282c141c6000b8a00d080c1c4c46240d241da01074040c100009007030200041d031040000598404404607040100215803509054603403d400c0020016441034907041c0d0040e4104ca180209000d010340b40c0c14031a9603201020812149007080d01e641030084140c01804840320750003143c1c0f004c1088081c00c0419075800546011110700552019440d00030800c8401d000c41281d022948500c900041c0d204003a900c03185500c0210b41601911901d00301080400000390f01c0500c039280a0340503001810294104040c0001c9a0450b400440c0c05818035405420104100d6030304000c501d402842c403094013548182040c20081d01e07460001c1189026510300700041c0c1d110f85003540106000b804c43c003010801c01611510b040d010b010141c4920311070b4030504280c2058030300701180c940c0c0580d149442c0d11300300441940e21140604005401c20740d000c51a41c80c00c03800020241c021074813490082d42e489000b65102d2040201c61205500b08000b001500fa8204410801c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 202449379 1250 202448129 202448131
    0x3070605031801021b0f0f2a030c0d0305030a0f020f0406030c0e060c07030219060906140c060a09031b0c0b07060b0d1b0b0c0c0d02010c1a061503040209 67
    0x440008003a0a02c103509505019200300a481003a203641d021111495034004607500880c03014000a507080b40042c00b0110b55100c22187d00008000a0960342491038079610182c40070251001e000d660700c0d6a80103001031841e0034032800039130110f00000200022003510303110345103004c042d03001300314140325000d0b00c0719440d402070303004400904d07640302070b1501d040e4001c014940542c0c0e0000d015968810540c2a5140c4030b01092004a0042c00307420406075040c0f415440f5482964420f07a00c80a03058034040341220043c1d400c240c2118040740400c0550326101081c0043c5105007031202d400708a65281e0f180007014944826040c940072540c1c0e858140014000c20044000c45610054060f182c12036030500000078251140b420340e01c80603c540c00000c2201a1341c0c83d804009e1103242c0c8080081e038030402c0700d102e84903c682d08030181d006036102e100549015411540054018074040040c50429a100e4102d50090403c808a0068000030010a494403040d0a803c180b080c101044c01d50526034081021a84 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 202450629 1250 202449379 202449391
    0x150e0c06090409200a06030902091612020304261903051b0304050106090c09030b0103032303090a1502040b070204050a02070f030302030f06041a090912040609080601050307060503 79
    0xc40021032241c00c0c1d07200d820004a80f40c101a400c004e0325880315240320040074001926024403043da10000d000c0f0b0081c82203105032500034040c1c4182d9030b00c420426900d86071b40004501842850682401075900a201551084e44940c3c0b030f001c42d1052000c6001d6985040502c0a20088420007040e4195800301c0c141002110f803038100800c0907103074204c1c64200880109501140d1071404002c1100340b0005401030011600200c504202c074100c044402c69035400c440c040508040d580100400c0004c3c410700c0181018500e020480c015600508121140c0b680306881d02015640022400e4042c4101c600d040000c1d040b4594045103864600204118940518070021744101e544030009901c6013541d8044995080e40540e035448000142c0c64007400035001070b40e007610414803450010b1620b0510340f044500000803840e8a10304000032004120342d1050040c00b0320780500a189072a201b501c012030260002d00103a450320103405041ca8411454444140c0c040c901c2588061001c101558101c1e040f07c0e0040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 202451879 1250 202450629 202450639
    0x207051f023c030316090503120c01022710090609140a030b0f190506090103020f0f040501061112130b0d0902030607082202030d0f09050319150e0c 65
    0x103401c0320b280d018004800c400080c0807196402d210800030000318490410010064880c2070600f90803103006a81d1f0003810340590200c1e807ca419a51018064890030f445000054500140c4102d282c5224003880020444920b501809000c2d528054600900503a49454041c0f866841d00c80014110076082c0700311000d000854081c0720300394840b14648809141c00044c480c405042a9030440d5100c14100ca401c4505442031300c02c2a08500d90f4007400c3d0007094002c04120440e400c2da000c0003045402e00c03000d1980090340d10034066140d103950103264000c02103515520006203107070140790b0034080c685c155001041010800b060a011006144134141c560350306503c4e4035540780d40c1100d00102a5504069414030941d010040d41d103500040050ec03400907602c1e184c00301c600b24105410345004c103010095158001311b0603086414411500207480b1141e42c42c0800b5259a25000729090903d24640d00c800c0c141d0103c0d9100c10300007515081c0a81216480c020428602d032440d604c0e80f299403460b0554466 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 202453129 1250 202451879 202451923
    0x3041202030708010c2c010903060c030209031c030f02031003080714011107060c02060402180c1303080a09080d0206062101050901091707020f0d0203120a0207051f02 73
    0x154800700a601c0180400340f00030012100c00703190140c00313407016095070010544112410792036035a140c1d100307056100d01a142c4200e5203055650740c070b01808101c40400200b650034803148000307541c10080c4c220540c44a42101661240c02031000b0103840d000b101d00704586d4010414001000021f03c1950f00b142d4005000c02c2c1c5031a01c03483c0803040c440000d51076860035070a090703d0ba5107820701c1c6402440c08a204010230005a020100142c3e2246d5086801035448011785101c80d451103c607100469200c4055040940350041e100300611201445401c10b98180c070003c43c0b4286119002030305030307024008030381c0180007030020014001d680e980020003031802402ca014090703241d00d21030450b0340200d0030b2902c000d201529041041c10b00034005500e0a88034007404902c0d4440c00f0f4040c004492051340c011b0100e502034454041132000811040e00c0881e018401d8211000e404407d05000c1c140c1120030703501500f4000c4c81c090070851400e41d5520b1041c5407413071300b98141c408103400156000510170440c40070080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 202454379 1250 202453129 202453133
    0xb180603040201031d010c0206010e0408030604110f070524040210030f0902150d140705090d050a0b0c03160528020c0303040f03060f05072a0f0b040501050901050405030412 76
    0x242c4a501e8070814840044045c40540003819000342040c1240c560031a0807983c2c0e00e28400d08a00c000759401340408000304041001d90806ea080b075600002c410042620301491059000d10300d60240800344d0b40c2d80c000030042e00b40501d0410312070550001c00e110b0b694080c1059000551080b14001042041c0b60341c89465002c02c3c1c82ca0b1b00309111f40c940041c1b020412408007500b541d580c1c0e10070002d00c51528500403140017403403030351a11103001d0049030384c07000e0418000d50180030882103008015221072041d14009800a02a100d000c2e1017104028122078a07401c00d0042100c091854803c1c80c800d03c1400c0c0005100700151404010075442041c83c4090003504041081c4e0070807255060f1070742c05002c009800301d10315000b2070140c82264030a6600f007104440b03c2e8016405c96100303503081400140001010171001004040d450517502809036070482580c0c0c10f5480710449414a44c0445404007031100304402c0c481c00f8410664007840e101c00a100c41d00c0c0554405d500d0b840345000c0c410301c0e0b42c0b4020003901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 202455629 1250 202454379 202454381
    0x91e010e101d01060201050f09070b0703111006050111070509070509041b021c020f0304030305130f0801060303090e1b031008030c0109020a060f230903010903180b18060304020103 79
    0x400104148a20802d00d41c0035042400c0350074001c0708003560800002c917130951601c1442a1040840700b014000003814038400603255404040c0507000c100c0c401031041c003060780c1400031800c0e00400392030000304e5609d02400900240100b0002d080d4030b0700142c00400c0300e80c0320518503981c03000180c60120307a10319a520000f070041030041440d400c404182d00318204101e80003ea0440160b0354048200300d22010f1704001caa0f030710f0392140c00390282e40003404104006030149000d09002c41a0301c924140e40b03a00c1d5100010044160707400202a691501070810078103401035840400380102005401c604d14201aa40c08414103034819011148800030008000b02550700290b0081c04e44002a03e035038054500485010f05440c940070f910640321101c000815a024120f0059103500d00c0c1c0310000e14045400301c1c3c406c042050014407040303e10030409502980d4081c07041c0740c40d01c0c3c07081e151100c0812051001144000c40d40c0c000150080e420449080c5001c12401e0810134190100d032115a203a81f5072004070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 202456879 1250 202455629 202455661
    0xd120f020f0304050d181a090303072415060206070c032a05010f020309060a020310051302030a0c091208130906121118010e07020a02120309091e010e 66
    0x520103402205103c00c1000203c1c42e680040141c0c1d403a04298000912a006424118868540c81001030502400c0c280810700c0504000134005041d20308280c91511503003070159001000b081740116aa18140bc001079174442c4410340c1e0050000380034124148003020355103010261403501840a00103032101014802d50b1002e0f4080b142c0301c1c02d0300118640100c01d001000d031078070088030703154241205107000022a100b41d0b803007403540000900507038807002d10402c0203500140c6801030b085a42c100124468480c0c0c000841d6160301f103080165a450304141c0a02120000000a400c0000c0d1220401c0000c039000c5401d00a01d070810040d640c2c46825421081c014892644111071031418003200140c400d0f8603102c3d9141e407500403d1480911a1401c04100007212400462400c4036910401071014007014124140d00c055180110780900e500d6400088803040c1c40001030a955200150b0042d96080c185441c98000c11002041c0188503404200000450814002d42605800d50320021383c002c6440030100b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 202458129 1250 202456879 202456897
    0xa0905010e041b0302041d1512010e060f04060b010c0803010b0d140106030b030d080103080d020a021e061509040b07051c06081605060c1b01050903060108010501080c030d120f02 78
    0xc900390900203940900170390402d219848174000714004c0071903065500b0090320310445100c0020203003038626000b08031840f486520550210341d13a03074196160443c02082030f540102d080f075011a40341c2c50607240080c1551100c81031507040001c1356215400207000c8009403815680c20010003a141c03160700040000501d1002e1401d01054001d9000050254040d1300410903d8800d07400c0e125104c141200aa8051a080c0320003414444100800784203da565070103800841c2080c410b45656a80700d101400c0344080f00d1074441c106030040c0040c1314003444200c14844100f40c0a030340a160510741500e0350400824010701450600000040001c0d0a00000c90142c40040c0b005000b04030858480c0b4800fa6220b090709000f1000c5032007210041480d24129080e911003100071001007100d5236046003d100e11070050745150703060100901588201d994240001ca01800040c80001055803401d07042034901290303040b6103802074100c1c02c40c1c01100b40c0e000c25071707044002d0212808100c901803144214001e2191201d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 202459379 1250 202458129 202458161
    0xb0d0605100302030708191104020d0c17070311070803130f0c091404151e0e01020315100807080601021f050609162703060c0504080607050a0905010e04 67
    0x300030740d0000380c26155042d40e0003501100e04517500e601805a45000c001504e6509402c0361f19404000740c000b00c0012a528405000541400088a0554152040000304101084151481d00c8504141030503550344181c1c0c52506000c58620500c0111a034890540054402c2000000150140100440564582d5442003a030002600b090a15480303418541c000e0381503150811060343d8044002c01084c5025582102801700d150040c00702ca07100400554210b0500c0070640410800329030712520617100f072031540038000350b0380b0300e040b515204030314145682d010701ca0043d803400c036800c450b80441d280c0e6002c131075400d01200c151181001030349031010004544080001e0001880c0c0702c4005c5801041c02072030f05603a94002511050724614222500c0f0030f808000941c280004042c2c02413000000449600c0d1200e4034164540300c0d1035005c180c5100351405008100000b03410043c504080120b55031048580c504507003405450746001740203405031711600381005513000c4500c465075200da0083d04490310080c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 202460629 1250 202459379 202459381
    0x609060213080f06070c020901050d0614070e010e031b270403270503100b011418030709050c04030605090f01060e090f0106030c1a040f091d0c010f030b0d0605 70
    0x410380750f80d0040b00703a900780d26005510109406a000740c0800e40440d600605800c03050f803c200500c4940781d5100425a48c3d10303110f032002501c04000310140d40c068202540c8070352020020301c00140452241800043c002c1e8450303800141044400b44440c450b03204c00715181c1001c550110324402c09124081300009080c5038203030a0104150b08004414180300062040c910301984842e40c03001100340f0b6114241d01500011003440313102109601140030305005043ca4840c108200700c0000c0079800c00090040c01d451121a03100c1c140c68204031900082c5440c00e028850340c50188410402405a80303c020911511140822100181030016000d00a240340080000070380da0020b031040a501525402030a026500142c0b00341c01040c010b59007a290000190403001d850204d00340840c10212114200b48541403202054550fa0000031400411031280007050110a042040140404005207000e255000183c14001a46c00884401440880c1d08000981000c01404103203001100c080007461070345400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 202461879 1250 202460629 202460639
    0x513080c210f2505010f2f060c220311060715050a05151008040f03050708030103200a0303020c01360e09010e0a080f37020105010f030609060213 64
    0x824032440e40314044000e200c1076075a0401511100802098040014003003480c00c1d030680b40100c46110400b01ca034050b20a1f0307c0301c500c811800d111080d51204541240002c102d6240440604003442a28501903102c00c41440c55442d03140802009400900a050100301c1109012803118035030300b86003140e5400d00c644d00d03015101ea401003000715a42001a1804945c03c400e0781000c8072030382030003411a110760b06c0035110fa448107440ca8203180c100306e041000801120000481c001c0145000798403490351410742d0506d00c404c6810001c03a20f96914060300c661901000802d90008a00c0f010001c00c0c2010420000401c600c005080301091070884400301300811403a103007640c0c0c400841224103024000041c1e80b116407402d0b00340c85410402c00b409910102e51440481c03160002081c80e44000c8510750302d00458030000608241c805d0001c0452182c40c0143d07400b40d030981600020541c00f0f10310003000306e5810b000c1c090720500385500001e401d640d51020540c081000030f0341118034031034110f1000000180c0e20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 202463129 1250 202461879 202461913
    0xb03010615270504020a11070e060a120204021b0d110303161805030f070602010609060b030f0705070c060c0209061818030412050718020f030103060203250513080c210f 74
    0x406107c41c0601c11004000f17115980e41e00118000c00380140000c02d07940c174011210601141c0c3d1902a03034403640c03c00c80302c4068202910100801c0d90402c015011402c203d0074041d01c6105042200c0080750020010402a4074240d150030f41c0e06505801c0882c113350b1101c0c403d100700da8844d0000e503054440c0d1009558040f10020340041100ca8a40c002e0004540b9401c008054919070320505002d11b00038002701e4142c0c00c030b0b45a02c940c0481d1502d409401c00c450b030384034014002003550141010422411107002942044014950311450a03a440d0300741241684861488500050508400d1901e0109080d40350605004031030060251452003030110050741000c0d070b01e551880c031038038618a82d42d548030580c804450094a402401b02c20740581940e1861f00d409019600003804110310b1300700c484041070200c0d6103959810380e85045507101901d0f6055604900d10222581d04990007590200c0006200e594500021801c0543c03059081c051030040b040e58a8a0410712000003a80340c040c000c01c070110500c032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 202464379 1250 202463129 202463147
    0x10200f0102040f05121207031218060c050c07050111070314030409060602190605041e030f080a0b211f0b010e06070b0f0c09040f0b03010615270504020a 67
    0x8108042d051680e9444c100b0140544155124901c3d80010000110906c0f40300050000c660103401d16001e043c80748120501121030344d250004100c0308500000c41400b41c1e40c49101c010701d44c10700b0842d10704028824a55690400780c49030904002400c0c040d03020803074040c04850000d5600901601e207080c00003030042d460741c0040c06032800951900500003005840001d44d5200c1658981920402c00165142c400141c03000901c1a50304038044180407030040060900086110f01a42d14005082202c1c40001c040a901411000b00181003a00031541a0741340c04481094401460100a0000746100c9240c141300b480440d01c40106000b4002c21032050030707a0404132071010f09a0360540090404002c000720340c06812005803d21450343c0008945170b4184000a42040b64001428200700103903000405441305502c400303410356154203210702941000d01481004d00800c40b04184441030000380202440078020038030000f6064241c41901c2c8000140d0300c0005010083e00543d5510200140a000500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 202465629 1250 202464379 202464389
    0x504080f0319140f03101701020c0606040516270e090609032104020f060c010906050907060e100306080d090302030f01060f060f03020405030307030c1a01030210200f010204 76
    0x181c420b00c0c61a042c0f2591022070b20820346407915051800030b03501296603810003840705a040c46800001310b1031550600071240c003a42250009690360420488c103e01303100015005a008034100f00c06e100340e01c45041001c420f10300092271f04003e0300813100c41c00c900c407002e150001d46081e44a00b002190800780031a5091041c844103048440688401410580c0e900c128843d0205044448404400c01c00310001980c1d0030a000410f009c47c14901c1100080c110b81c898413100801d030303640d19240c42c1046410300070713280c1c042940009000f12500d003040c040c01070b01030044c6080c452200480070111040c020350003c009024500b081340e4001244000c041c14126450005a2080c400ca1143c0804c201c4140a82420b407000d80001640261512009590800c030310034528003415000d01021940751400c0014000b242d0081ea42d481e41c0c616a41001201400c25480041da02c4054500500158031f445c2c2040800b03003401c0c50700c40004202c060300304448082c034a00819040c0142400015900e80540140042c2c403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 202466879 1250 202465629 202465657
    0x2010512041b08030f0d110c120a0306120210050304080c01090b040308130f080c0721030f0207030308131e03170a060f0e0c0f03010602070303120204050d0b070504080f03 75
    0x2503c844110781c0d41c2c010340009800c546030401000400b404190028803600340346414183c10b103100141020304106d4403465040d960040803d583c1e021541c107000b20001810503409214001d903481d0080345007001602c4d1085c041c07050005c0810104166481142e100c1861400208020080b42c508500c080005407030684c00101c100c0007244aa1b2900e51000c01c03401d0780002240c0b0b50003020b513504d0300c664200d044d1101c045d010b07100e0300044117030900074128540c000c1c00324040d00c22221440c0180c034540410340d120085500052003440042d070407072140b9400182c0b0790100c005071520b510b0f01c41d2000e006a1901513040b128514004201070f080140c20a4000040361442c50a41c1c912441a007111002c0c441c2035042c0280403001c101040d603840d10719400c039800c00949842e000700300d8030700a0b080d40700307a00c810010780c081102041070507480b604202040001450951425141a0000d840256591340140000c01000c000c91210360245040328010030005082e150b01820400c0c4054603a0081d841c40d071041c1c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 202468129 1250 202466879 202466933
    0x7140708070b1806060108061c110a0e0c03221203051009020a020705040f09060c05070506010603111b0c0a0f03050111040503030f0c010e06010f08011b050f070201051204 75
    0x4000f005014580300f00d145030040c941543c60800443d001d42d0094441c640115045548065880700044011a0540108200207100781c84405010880c5100c2c0d202e41d204a00540611509001032002c80c2e800c108a40b070f001c07901d40b00d03a1044018414260800600c01c00303040b4405501190941c02251041003540401000c140c2d445e0040d6041e803280d01000001a004840c05000915042d807010340c8116504400095014050341d807181102e4003500f056022074400704446080000c01c000c0b1602403e46454140207a013145c1c1c4ca003178814000c45001c82c0b500461984545501c81c1b04012540940c2c00007840c25071569070b2601159000300c00341c00103a59650804001d800781a41071400c4408591014004500e0034100142c103486540114207140050354039200a00075210040000ca80030701081811740250500c2d000f0710500310341e0100c084030544494060782800003074104c03060304d10b80f006410b00156140c0040c40101d495206d0810140550481001404280074180b020b0361a8480204484506 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 202469379 1250 202468129 202468141
    0x60501030e0a152c060f0a140402010804060e01050c03061306050a090b0612010602060708130308070f030f11120603070b160602090303031503011b050d0507140708070b 74
    0x403801030020150945620350341801d0f01a001d940444151101070140c100c0041400d20301641c6045000c19040c0c00e60310070010305c90342c0205000b240350450041c203410080041c480c602140034180041000c0d041c0903003000000c0903c46141c0104800401c624000c100c18904254070035036542080c0c40c01801400a00021a490348aa20585041d00d4004001d06039480c6050344880c06096134059903908000d041c424201006d40b004001e80c041d01d40703a00070b4209458440d900804602005000d40440d80013600d01c040400d81003909070344c0014542c6001203110100c1001900980240360f03903001c0c42490300c3c2031240c80813602406051104510010a0155200c3c01e040680d600c0380760049580b194020008a20000020f26040c42c1c030500c20701c005410450802c0002c0c0c150b030000c8401c6031a4100700718035041ea500c0d082c807625040da400c80541008082003004000d005004414400302c00c1c44d41c543c040f070030260241d040010304003400d4038069a00c42c410300e850082e60300502d004444003008600440d007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 202470629 1250 202469379 202469383
    0x1303030216150539030a090c14011701031104090c1a1e0307020d03091a010b0705211c0b0a150306121a04030e1504032303030417040504050a060501030e 67
    0x80c03480400220913109101001e003c01180d0025100542c5650f80b00310420020301d106408070010400361008910f0250989c00141600c0e06103a5000e0390440c1d01c0d0010310004a540b01071245080e810303680007039080858038181d803400e0303043c2e00300c601304116800c010712504054400404603074030b841c2d05150701c0c2015102001e2003030100780d46020240c2c00002c0d00b9900144070f035100750082c600410040e06803d5041428907014802a0003d01011400045800070302904200c101d075540d14000040340c60700c14280c02210940100d075012252044130800212183c3c41541000c401c403031009000710211540e03402103401342408030740c181c40403c1c2001400510320b0396405503000080d4001c28550311030316106406540046008008500303002107025001e03490f8030f4a101216000b510420415980c40c298141070481d00c10210413600d481402e2003000c0d800f00f10100036660403d0740b01000c100707046002c2070740d207100c1e0040c0e401064025140c801040071020041c1c00a40440750280c804100003001c5850183d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 202471879 1250 202470629 202470691
    0x11010c02070b03090106091401140102070302030d0c0203030903060f04021207360c051b120412080d0e0a060e0303040b070e01141c05010b0313030302161505 69
    0x9015070040c1c6001c011280c00000255481041c030303400040d10a072030310707039071011500e110041d101c080610320018008819501071841d1590000d0000f1b02c041d502d1640000d50710341d5182d03542010000355402c0e100464500308150380b651440182038a9070381c0f030104060141110100c4040e442060350422884031708001240100580e030100d0040c1c01c10304403060502a10617282c07464203400000e80740c408070105807248070351001e1044030340d5503a1356281058640c0c00c0260414134035030001d41058804d403a800a1281c211801c440f0f01039820074180e500ca007051501c0b0b004201c41075030601c2c10000a003020420125072a4030b1203100700410409500c425003450707601e02003210020b04c80004503010401481c002c41e61030702d1445052400413680c000e0140a10401c0c1c1201105508820621045001d0180d0a014190241081185543c02e500d0b28500320950011105005824150300043c2003201c240105020404681c220070680070310303590100340800400b0202c0e22030300610106110300041e44a150196 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 202473129 1250 202471879 202471901
    0xb0609040f0f02060918010302040c0e030c040e0708160e160e12070513140105010519030e070e040b160305070903030e0a0302030f031801030902150a0c0c080d1101 72
    0x1c6035010071550b603140503549581d04240c0e40030301c0c1402040041d80e2542c03524009043c0d0b080d80000c1c03a502d58170620003078401c038460007800e000740040207800649001400d00c440910031500800c5500341c10a0b02810005a80c0005043c1d000d00c1c403c1040e0f000c0e00301d000404a41c5400500c00e02caa45542e4550b03403500b0002c6000000170604150001a803400351240c90440c3c0704202610b4400b55500c1c00589002000106842c0540d00d51054038201410044950300404083c02c0c00b6182403086008034400400c0d04080c48185551101041c9420320100f01e0000600b244c420482024105400c00a08060302159410803c022000121820030b101c0c1c0100d81c002c071125240e03c84401d04646c7c064034800140c4400b1500045041d10000c09641c08010802c0000c1780e0901560b40ca419101d914580d028103003440d2814182001c102100607128800400c15402c0004003007a291111884119902080000c0240003440b4401d404a0100b20100e21045910401e0b161800702040200c032981c20382e0410188 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 202474379 1250 202473129 202473143
    0x90f07050f1503040c050306010914091506150f0d06031e03051905090303030403090501090602030a0c0b280506031501051309030c050114042f28030503070b060904 72
    0x415420b1000300b601440c0c109100c0c030ba14002650b12840420302e0080d00345d00c5181c505031a608a4020641d602c591550040381030700143c540305064100c2e810700010041d1019005d24050304508004100400540307540c03a0102c0d26140e52a601040024050410340c0403c2e0303814124055051040d8080b126610451541a16090304154110381412290303c0518010b80600c0f80410540850355401d00048d4440c5110340c8400203440d09040004040120b10703005581950700401848070f46d0360308859903024090380400314071002e94410300050100c0b02c0841084109130008904081c007c0455000f1512a48042c0c04541c4545141455004030100a1107400d400603d0383e0319440e0416415044a003007140603043c05419400a0b90380d0038219000e030f8002c02594402d04c010712040140d01a0750a1703004200f52103c0640110014803101607031802403400b84501d0401030084d1680000d00300802c031080074041d0600c0c4003a544d0802c161a5440508225080000b490014002e0b1415a1800303001e075405c110 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 202475629 1250 202474379 202474399
    0xc060c0807080702010b0a0315020403060204030f17030c0d0c0c1a091204030807150b090f010303030b0607020102060a0b2220040303020319030b130e06061f0503040812090f07050f 79
    0x7240c60480c00503030402780d1415002c001c0072000c16041d000800c0158820384036209620030904000305110f40180c0d004201d00d038200240700c41692448140c91104002c0a00000d9143c00380d00140c2c0c8001801000030085000101c000320402010004071703216064280941c0c980e040d0404c42500c0a104070301005000c14402d000403004182c10301458426403900d807500060009036540080d4440170116005807803007054400510805500d405070f200f8851050380c0107400c2c20029400071352540401413400900036910501d1a2580d5100c200e000b00801503100c5480b07171090303c08120405841948140c040909a0012415030402031800310b408494041d409035040c104510114182c00139800b21a40425840390220003282c4e0795502c004000c41c4200c040001c9040c02c425215040c07010051820348680c500d2402a401480706480c000b00e0243d81b441d02a603240e560b07180075006406120100c4195000313280402c00b54080014440038805030301d0b822034020300d544000704420304007603d00742070304060010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 202476879 1250 202475629 202475633
    0x3150915170f0a050a1106030106050409020306030a0b13030206130201050a0f020102040f090209032104140312160c0e0c09040f020c010528050f040b070c060c0807080702010b0a03 79
    0x400000c1c440842542a50300406408510710b14103c81c40000b82d51542200b0598010440c101808001401d000d0324000d04540c508a0085c3c400e001c0e80c411950b00030f400100084036a03400b40314460195070b00004110702810118a001c864200a840450151082d400840d442a03109004103403c150705170359061818280309400c9401110107014107042d90b40901001c40c10b85051340340d0b0307000741070410801a00c03070345a0803c0500c1d02420507402c0c1501110310109400e08640401110700f42c1d6440c0c40e80010503001c01d00400d1030004014160075400c140403501035120031000d4081101c2500600b210b4184075110303211041060030a81e8103242100c0204109440c41c201500090b40030744068000508000740c9102150965601b1a002e4111880000711a925088220500c61801c6070903601048285400c3c9080f542480d00900060496034180b4002054207120310642c0700041c0c0d00c010b043c040b00c1c00e0010301800c00001a120340022914000004903881d105218900c4080c41c000c0200c0000743c616 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 202478129 1250 202476879 202476899
    0x70204020c160801021c0209130b0f060c0a060b01050a05031b04030510060501020105010605040f1a1b3901080a0f1d01060f0f06141903150915 63
    0x10080031a01400b600ca06403111000c80d4800c0c1e402018200700250390b802d6900c0701c600c652070500040310341c418418400320030561035030b03000c08888107550303d8005607003802440024643c03c41c2c80c03a0603034054000070341d0306814200481d4130080184102402e100c601401e4005454500651481d034000a100b400042c183d030903071441c9001c0c03d0351000c005902c0c194698440d41d003041100c4880d801040c0e140c400402a9590900c2841e0041813503140c0181400c1c20301c80d4000c1c040f41207100310051401c00007800f96004000d00e0403924075182d05074440050b00c0c02400d00e40d4031940a410003524010021700d031000b00b02c1104040004446490083c0700d100d125290054a502c0c3c6d003c6c000380c000c0755451090780080d42091140c00c80f4018180d5580150642d1400f040d8290340440c0c01c0745403410b40b040c404200f00c13001500ca480076140b030750400114401c0d030441c0c01501401051400a0900840c40b0709070a041c0c1c05a01c03200609080b01032003100d4549402141065031120044070240d4030038450100420408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 202479379 1250 202478129 202478137
    0x50915090109030b0a150e07022a0a0303020d0e0405040209010605070f05160806010801060b03070f020111070f060506040b010212070201030e0d080f010e01050a03020d052104050307061407020402 86
    0x41414400c42c040d80b29220703128040c0c011035440580b070351303103810a44000c42000c07180802410b03040010641440c0810009440e24118130740710700b2250011030140069991400c9180200340081c2490b000d542da00c0c1402595880207822000100f08030078080c41c507900b494041c1d0f610442d0054441c1c42c0036468000e040751103500542040c0c5000603071110000000b0000d022407c0c03240c440082100803182800c0301c50b401d10b1b00c1a842070241d681b40034420400c0c1c040c0f07417098960081e02410074102507650710500740d001d81a440301c03024640c200001d418040142c0040701444140c0a560100f055aa4034828482250382d60706505015038425890f100c2804004030080522034418036001c140421032201c2c4902d088840032000001c1280b010401a10500c80301000d0300605442c8222181545040c0102d07241c0c4146e03000c040c3c0150b1900b40b0031000c0c0030701003240c0c070654280260f8403182034042c144896215041401150301ca4020300d100040e205200d1000e4012026124400e031389807038916400c020007580 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 202480629 1250 202479379 202479397
    0xf090c09040603080a03142208070b0103050105070e0102010212010b0904110d0906150e04110d0b0f01050a06020a0c090e07030c03060b032b030504050c030a0c05040507050915 77
    0x90401110800d511940078620003144a51989511194100405800c1c2d590122031703d4924a8007101b0400d00d8040d07105da20405142c030101122034080d007030410f08083e01c50748101425840c0800c0c000402c02c01c055010034030602c1c0780d58441040d401c007580120f09030311074080300c1d000c1400280018000c00f8260f200800364008010400104500001070401040d08a0411000d4a50b5548070b4041071148038003039a09002c8a040820101c5d504003400003038aa03002510140c80240d4400e02401030752101c0703062464840e08880b0038102d0386810784c1140d207800024045c542c0a03000700040050040c0c000140801038aa12040d201141030600d04810020314509815103a5480b07296400004101114440000f65008217004900f80c015074081c585800c10f00f000030ba40304095203e8441900c05007041c1484000c00516010606894070f00305645820345801c00c0960500517401c0840810000c00e201408a4605030307030034480c0d0359500209844070301440c60516000a01d01c4250401d518088000f440405 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 202481879 1250 202480629 202480651
    0x11a03030a21090602091806180a0908030a0b0a0e010803161a0910061a09040905070e07090501032405012607030911090411010509030a0b0a050121020f09 68
    0x20b0b00c030080040540c1d000301425110598000790948071800d12200b103007242112142d0341c08403800c0c80300104900c8074401600e800c078541c0000105102800c0ba403c03900040d500041c080b40c072410042081001081c00c5100a440b59075090000501d40e070050032010b0403580e147e400f450800002e0030a200030304100700d0741140e500c05802c80c441003908940e030b1180e026025160041c1070903003640c11100d0403a029500800084a2804910729035026a04220741c02c0d058143d40120780000d0364507003d40381c40c3c4c15800c0010340002000400c803805034003200000841e0403d0ba8148413481120080e0181e54441c1c8590045041c1e00401c203010307079401025403007500c0031304503408522040c08601d282c6044005a070080b00080e1201010707418020307030b11460600503004440b402610300385551200d0034160600581c1e41406800718025000b50303000d12110b01c0841e001603049090b4905805841e006201c01d00402103688804680c010399031008803034500361164054690542c2219550030031610590040001900c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 202483129 1250 202481879 202481927
    0xb1c020619050d06090605010207080313060c0f050f030307021203010e0408090d050601080102030105010f020c010917010902030724081b03190e0705090702150606070f0210050c011a03030a 83
    0x20a003034464013000785400540016150b06180c002810440300354041d00c82a03205000030600d40e01440840412510300b82056040c228040c9401c4410312038540003e8014000d50320f076140b52040110007980304400319402d550440e0252a892811804203001c0e0f200e85080301000140010b40d0b8500524450000800c00300b25a0700c030f40d4415184c00300076000a00103035004001000a540c00c0a52029540046e0010707040088910000804000ca68401c21041c4004403080c04e00f641070a51100e000d0302d8001c0d046e80c6d1641d45408955207542c044580e41d50b604010704206e0f000c00f0b40f0803900240030364000480030403062580c031540307805600003404461080200032940c2e050541c19101c1e5861401041b03001c0d109243c6441c041200158001b4002020b5400210f040d1452001c610141941700034116500e41c1c46032414201740031030100701d4030025000241c0101c0701c65950f0b000b0380503000d01000f41d4020b000e29000001503441400c007851704540c01d980280826030006000300c41ca00107864541c10300b5114 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 202484379 1250 202483129 202483147
    0x140111070611070f060f1d03010903020304030c0504020403050d141207020a06150b0f07060b0d03180506040302010e09060d0c1d09010c1e09030b0a0b1c02061905 71
    0x10050654003010106407140203800c5020b00c10f00510000349101010314200c0c6152502c064824114100c402d01003245811080e2034011300c94103124000d17030024000f0031a0706607919000e5620303441030009660028a03400700107064030307050013110240d03540b0038043e05091001320340503903900108810750000c0441c02d018800301c0312103000c1220b109031041d50052880e0002c42c1411000c403a8100d4031854881843c020078000300e18980100c0d0400000c078203019a0b034400034200a802060b010001d02e603c41011601c0308141030740160503131415030403105810403155585040207054400da1000902090114080382030a01d020810703140e0000b40641b0030b07611100381e5505c42d0320b04015900b00034034020b440505d410700e407004c00d550f665101c81e5036002080808019a00500759640d07902d080c0180d00e1800c181120b20380d2141e41c040303001755480021907501d03082070208803000d400c05d045001d0168203400465155a001c00000f450165009001a860921300100a034440c12403030b41d0300d00c02d2020401010760 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 202485629 1250 202484379 202484383
    0x60b03060c0a0e0d051906060305060708040302071d0708090c120d1101060b07170f03040507051002031c0e07120c030302010513120525030f0305060d0c140111 70
    0xc860803140221a664072028600500764400c0020802d0050303075074004d05000075800203544000c500c14000b19501d40d000740e162101c081e00f070940000b055801110b05000003160400304003405144280c007951110b81e240d49005000852501541c1d126440070720101d00c001e0b01500307200750042001000d442220144802042c01d0007404d03001d00031560302568001c002c0c0c0b580a900060503944900084c0035051824406420600509102800910398490108000c1c1d510404842010039003000003500da24150500c591a4a034500c81c890140d00e54112a400d400d10200444941f40f1861414800355540500d416000384506210083c50b84a0200081015904a00d244a00c144070701c01241019083d464004e00b520400381c2650f1240d4180c0c1c1e44000013954552404c890481070303181060300c0d07042c003800c0b01000c0f81c0d00000350041d50f00220308000a060348050542118641c585003840300b9102d190902c008000800c1003e4401100000140701e1025012021010b100052520b40044010b21070424 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 202486879 1250 202485629 202485631
    0x20a09021303021e090a020a0c0f0813090b09070c02120a14010b03070e1306090c0905090d050a120203090a0219090c02011107020f220606030f06050303070f060b0306 73
    0x11001d0507010300410440c507000c600e20040084048940d80c068045901003450b4a4001d800c410b8131503008a4002d0b8484d00c140c92000140d500001d01c88420403ea003080c0e1055407000d4203265020740320701c0c0e0108090520b802611280300000e000251140d5170b0a20032240204100d4003207a00c24019a01c201c0041020040c0c040320f24050310707420f81910010ba400f64216641c07042010700a4005001c200b008600b5100c2080e031200d0345065075140150285070400003400400c030010304030102a0070100e00c050403540072038810350343c03101181d484044c00c000c04e03112402158071010000e80c000c01030110502c0705401441e00304811008940c090380321940010303000e503801550590a001108410000201c03c0d009845445000d03000802030144d076041c10501903c982c840190060141c1010300201d9241e4020f80c005c600031004011518201142030f6901429080c03103032200003808d0001e1454010307198801d000407584000c004614003001c0380d856011f4111182d10a8035805c0e0b03039141c4200c0d151401e1000d1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 202488129 1250 202486879 202486897
    0xf0302091e01022506021509060105061612050a110601050a0504150504111c0204030b04061a03060a0501091103010b071410020a0201050703060902070f021201020c010f1a030a050c010c020a0902 85
    0x11350409080c00802842c0c41d00d5240f80104031500e280c00e1000c0079201091f41415908140c610543e540c101840c8442500380f4580020110140311444000f1142d000d0b0281101c003680e591041e03120380c1141c60140d03031501c0070b004103580210500401c00030781c074159200400e83e410300350300c0f403c030540c0d00c01c005412107490b4004031400e00b50009155007501d090400c1001101021501182014115102c03681407002c014030050a090b40c3e20900d42c0c1c01d040ca0581001c1000005044030107502d021420440a001c0a10442c000303c0d0602071100000ca80107400e8906880000d5100707420040140c550b030390030a01c50b0700d02001381d000320400310a8a60075400140100080c80e00081018106070100800f2a5900d038400d10216206101c3c040c00035460903124903140781c040300d201c10f4030400c011500d130091040d10407000c210340ca0040ca600c8629801d810065031900841030640d002481c00d02810384804081500802d00d401000d5481c0180d8082c00806100301d0000e0130004040c3d841d101c0d00b0080342c1c0b1040407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 202489379 1250 202488129 202488193
    0x60f09090c0108100b031b0d0c1707090806060d06091502041a0910030f180f05010509060f13080702090106031a191404020d0204060503070f0302091e0102 68
    0xc1060103581090443e42c00a48440c1003035000d81c500520303040d59000203844030004d40c031245a5103009031041c070160782015121010400115019a1000d4031040d00c0c0188040401641800103003000e00601c082030850714414084d102958a01003001500b0b8842103040741d210307039a07008038004611625100f500d0700c2006500140c0e9641032541100303440008034000700c855501000a0758082d252032450200464450030003150460891440c00c02403c13a49800807482c2d81c02c80000030901c814241103560080c0180005c2186403104454161194801c503144020200c0c9000401d007082e206151000e8003d0103034000605003411030b4009200780c0400c0e4080c0000035159003a541c103000141140789403884003210140d0141450010700700c240c00b4980f2940048481d43c0c804072000352290b070102e84040400d24411941c554684002400d140c0003914054000b0390114040c1039003a001c0c0c400c603400800024003009400c0840780c12030f41d14144412031103045000e82c04500c00301001d420a8001c0d45524450703 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 202490629 1250 202489379 202489393
    0x40503030702060a0618020d0b0306070512010b09090402060d020f030a020a0f080f0c0d1803050a020601170a06050411090403030c0f05040b0a0c031806020309010e0306041208060f0909 81
    0x1402464010044d0103a00700514001042140318081e6040da000c00138107100240c0c4504210501e10300800b069450301d501406020108511154440020502d040035000c02d40110f9884400550550141d50b40d0b040d00000710704082009440c121028104561034030308090f20300a510340d882c002c80d40040d64149891500030500c0c7d0500d40d0082d8001100540ca860a2102480d00d4041c00b104a40003602807105860300166003019a5007a4011807020302d03c4519107a0354060340e240c01800340c0d2140224200600481c800030807001502e14650944412050003040c815041c1d031100b4004003c041c004540303070024801e81d0718042c1c54072000b43e0b2080d0701a44001800c00c0d01ca20003d0000078400e50700c1c6041040420092043c80c0d0590203039007000f0b14520b40440840e0240c64290f03140c913141500007200000034840004d4840d8000001c0c200a0000c1c1c0c0d0b030743c0b1072908040c01c0c55a100801d842c0108658110510004130030700c103200c0143c1c09040103281c900d903c5007000c00700300e11030029150b100c440e4100e41c07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 202491879 1250 202490629 202490641
    0x140103060f0515040f0b060c1b0d12030203060f04240503160317040b1210050a061b1e050604050606090622060f080109030207060509010e060c0a0b04050303 69
    0x222484914603040c14042c040c1c0d190000b81c3c95801900c012246105680c0c86000800c90820381d80007040c0c1a03405080b07941d0b01e0385d030000701940d40c030030841c50403107007080040d00710320139040000b5005481644204a03101e2480000b40030b5010b500020602604400b0b8558142c000380e85034054170822080055900c855551a84080c0e03071a03809070b0f00601d001c3c2d0f02a65684040000c101074000c112900800150003a01c1d095282d014030344a95480301c51070001c0840c1d00460001d603a00098001e01115184400c86aa41c1c420300ca0440141d1080b030021528044505101142e5a44603c4079280301701c5851084010b010390700c42c00c60200ca40152426408481003008014040040a4000e28100d400004500d000d1001480d1500780d0210910190b00108071181d0040b225086a8080e000348800c00c0385d0603880c1c0151038002c00ca071490590052141c044000380742d80c012412030340d9818041c0c2d108140003e01301c05201084c3d12200407442c40b4801d0140f1680499520a6182c1c0500d10410285580341040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 202493129 1250 202491879 202491881
    0x1205010608071713022d1f1803080406022a030a1202030903010203040b04031803110103020a050c030409020717090d06091a040b0115030524031014010306 68
    0x140c02032800d0040c1072091003010b54000c00c4490265111540b034a0aa5849214891124051503c025000034031948450704c030840720b284412401880766050000c0c030808a0030041c00c0d014104401d90346e11600042021020f2003001b109068150300c10030005e07955039980d20014680e1240d0300c10801a0042410901070003c3d980c491401030300034540f05c154107441c0e5400280c48020014009104800d023181c4120014000d01c1030f240103030380080086440b441c05003018500414122000c400081d40100b00241a04c01c6101c0c88080d80c0e00401c00d0f12a030444080154002c0d40814600300900106004d1900100303c01c0000f807000d45141e00c800358071401c40e0f140440200300b0841d0300e801820780500043d21a600d0780201209000c0d0401c0c0042195441342c24841408410810101852072110003008240600e85100d1812200c0b034101a52210f103404808404583c000d444440d01d0003080c1500c811041c0300c54201d0b81041c80000c054500490700f40558004441c1d01c2c1295540110a0b0401002030207c9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 202494379 1250 202493129 202493131
    0x2106090106080c132705070f0806070905010305090c04050a0b150a080f0c0909280216080c120a021c0809150a060801240503070302012003191205 64
    0x71401c003e0000305400c0f00082e8104103420320030303246107070390b030789859884030200c8075a02d80c1c1c042199084820782a141495510781d2441d00458044c040c0074403000030310450000c2c5152084c556551000001350500004401422002e44214094441d00e040c0b10515130702c0b0f11540f03002c1c8505447c0064601160418416410a244818000200c1c103000d01c04807150011042544204007082c548082c1d0380ea505000d40b40d003e0964080e801c001c1080c10411083c002113001d4001100c00711101d518101c4d20f11001003603118242441c1c01000301001c0b0640055401809400340110100907144110081f480c6030140d40c0042c0c03100c030016802001d400c80c1c3c0180304241030035101e14600e45010913190130040c455881c07120421410315040003d0005070410980e0380030358050320382d41000f402500d468100c6d24448a45000800300c00600f0742c48001000d140c0040d40c1011a40d068549524091880841d60552038400301e5130602400304000d2003114440500342d80100c11120348440040c92924803e100840e04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 202495629 1250 202494379 202494389
    0x101707051c270b0415020409061202041d1e0c04090b07081e010b1b120d11090f010c0f020d0c030506070f1407020a091104030212030a05030a02092106090106 69
    0x40d0040d1000c29840058a54080e8100c40002c4d494400c5d0380c01c00340240314960215080c0c80c0381c660041011411005030383e189500885040c0902840b24080010100b40c01c103007541168058208003022820000600d40c0042500c82641d040340040f001040550341d003c07100300d50601a901c20446081c3c3c10644082e0880760170701041028401a8001e5030425406006d0910001001709026111221103580d0020303103a4050190740840309082d45501294000c0219030411904010002c082c0c01d14000a8443e4904010b0250b5405125003006440040721a081a10703210344100101000d07803100c1e940c505429104808641006103941801801d00c4030251007003041100501902d2072043e480400c41300090b0003c94103507641c2480780f00003115014141c0c40703400c2e003e040c5080140302c25207040107801224000e41d54402c124400c000d8460b120701c16104410017164062010800300e0081303030302806640c00040c101d02540340360300c0b0000000040f03650b031004d4194804006c00c404840c0c00e02403040102 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 202496879 1250 202495629 202495691
    0xc030c12090a051548060a0513050105040503040e0c0a02070b0c030c100c0e01080f07230d051501030b0d0f03020114070c0201030b101707051c 63
    0x141c0d07100e0000c2c003140d80b24454035200b256001410000e00340c0f41c0045840b0941c0503c03034054010340381c600d4000120300d034001c0d0400c010f0080b2070f601e00b08040150102210b4500002a100c16915480311000800000d4003071240512907540520000b142480f4050103203000e80021a140d500e070240816020030001d2031011281418480760f0640d6400003548010707a0320700910b6035100c5054a41c59407450040382a0083c182c4500710190796030054030351001030030652030b5131070000801440005640c1c1c003400352086108a00c1c242c0c002200284a0036407000002c1c2102c0f05d07100c05103d2400c409200350801072051074042d03502c0040c00b0404406098030b0300311100c2804d050005c10070742c0c0c002501c6c8000c1000d000d00745100c0791141008242c802c0d4080703281c204520301d2201950820080080403c030005804034003007071604500003400d00d014011002800020368841c003031910159a90f28103008003400810600400b488500f8400c60b030f2031030000c1548441c00000501440004c030402c4154500507050f8541 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 202498129 1250 202496879 202496887
    0x8060f011403060f031204030309080d05122215020a0e030106080706080903070f050f070e130807020109050604060512010f030203250302100f0305070306061b0f080c030c12 76
    0x31414402983c1e80110100ca204000c8061800820f08181c104070701240007410010340423003056005294a402e491080d8101e03516a0b400250070b076038500c59001d034000807900d80d00004088054000c3c9440c0c900110501c8444410ac0c603a80724040200d141e0140682644c0110300c034020300b5448012189080421030080c00068581094640c83d01000e01502c420449403100003074041200704211031107107074441d600c4103440d800c90801a880d505c03555000400e501845c1000520450042216400b52207940c810a01c10704003607540134150345c005813049040c00b4520000040070795500c00580000c204a84905640e014910441d011401c030581140d100f00c031039040c2c2030025803000664040c60001898002d085c40011580651103070030030360b100a5002d40412441c050a56000c1008a464581e40d24107002903194410254141d0b4000d004800c0000c0c20201c084c079500801c14441c1e5005405240240310005007605d81c00020391100340ca02120380e1000030b0403030070440200202ea07064000801c80320700f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 202499379 1250 202498129 202498157
    0xf0201060509150a08060906061503040201021c031b0f09080a0503040504051f120606060806030a02101403130b0907030c0504050709050d03170105010912140a1208060f01 75
    0x2d000d07018062445500000c0b00407601e50700c1d050850300241c8610f03011607866181c8851401e541e03100880f80c0314041c6c41841c4110300c8284020041d02d000b254160040c00c02d003940920304480b00420500c01800701600e89d245010909041100554400c41a56070111400c201d40805890303000c041e40800400d81c40030031100c000c1751022003a83c00383c8004403004207042d1038900e4102c0da12000044030f5107020580301d000055640d0031000d20100c0612a0b1814040309640d001e058404640807542c4030f4140e00120032510040c980016041a07202e86402c0182c0c074030850220551150f00121a401038458038007801c4803d00c000c0324449517010b80d403880241405411039480c0c1c0710101e010710903140106d844002142405000f00054030203410090442d0541c1600c0342401002c01c400380200c60481d643c084004540c9510400c46103003540c29003850400300c1462596100400721b0205e24040d0355000e081041e00008800301c07840314800e442e41c0d075040305904080b810000090020850641400440700c0740f102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 202500629 1250 202499379 202499389
    0xc050c030a030207230303040909110603040816150c230405060712030b04090f0c0509240a030b0c0a020c090709030f0213020c1605040510030209040c0e070504060f02010605 76
    0xb00755462442d405c2c0751103000c00c01c0000e444028100305689400b001c54045000701c81507102d282c0c0c040c050b050356800003045100380700c100c3c401030750050821501044907418a140f059503881c440b502c607801a00320b5070070384560141102c154180900004d4481213018003004a80e0f29403c0c3c800c84180011807070140b41600240c0b040c030855000038801c2c010551602c50090280e80240100000070300240105c3c00d41d4030304050f54101c180300445000d01007000104040c03c0090901c0d11400c141200c007510603c0211220035070120400f803996024004420200005021100311801078189411503601d85903001c9010341000c250803082c502844017582000b181c03540c00022001200d400071a0361000a01d41e002040509050480046140d400069100c3c28003200003041c08903140d01f26012040c840d01e440030042903410545502282c10600c7c0300c1480035141600e4025002841004600d2900b96070b0b81c4513161541088507035001045010400304151078000c403014010b801244020032105042c880010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 202501879 1250 202500629 202500643
    0x60c061d06130812010e240112090609080f0901110a0c0603051e071d01080402060f0310120b01030210050703022e0207050f0d05040803042c04030c050c030a0302 71
    0x1030404801103524805209910013100c1d8000070403e2000510b41e120520320054071003e45000014507014418003a141c00e10584c2001c041005950f03e090a43c010f03030070760001d0210a03e0640d8141d0366010b169000440a400400039444015400c5494511110001d0041c004040300c00040d90096110f040000d071031390602000b5141c583c20000b406803034801015a61a0300c46800401044203001440305241d0498412032030b481c104414420505c00040c011209604255030007900010140944180d4206010242d540422907a0355020790f01e5076070384400100c0300003000aa860020b0200180103506018400583c070700302038100940303455900c8e94025550300400562040c100da40c030116041000740752017211301112168078155101c44c484c0c1405034891129069401d0740d8400c9840301d10016011b41c050b00e003100d04000c059814a407030424840b1141d6803c04a80b800a405440c0e148449007210100360701030350203a561800d024055184c55403900c0d555007005d61080d80075498043c001382d80061a1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 202503129 1250 202501879 202501891
    0x30605090115030914010509070e0114060301030f0f020a032f0f09040303060b0f121510050a0905090a1b0e0a2106020708032203120b0d0606060c061d06 67
    0x1d60880301e0706202d103001017100740030f500950034401406281c8100207aa40142e42041061180c1640d0f00c60385c100502c0b41c25100942c02c940140b004201144400c3d61000544d800741e0380d4429546100c0c0d00040700d006250b0011100811100d84501001004010012a440418101c1003112001d1400184450030380200313184074114480005003054481d40000c00180140364080d9111550380c8041320460f00080040d0310560080c9000a0407546881c01040c070410015051807035100340e21204850750390015095000340030050301d0001c2c00c1d80f680a04c081c4510740c04400010203611070600281e581c11001460700800542c00032080690365807005503003c84d101e40100c90540d12000c0b0410700296840c0da80504441c0c40451135500780605d002c020f510481c03800010f0340440925000c0703c0c00c104401c84002c0e000903415a00c80308004181c1e8456083d41d40300600c001c14032001c81d66040140c07505a0007600020703083c6102202048203e0041a01d40c84510990404003425402c035103541d141e0060003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 202504379 1250 202503129 202503131
    0xc140304080705120409020a0201240b03100e13060c0e090606130905070c0b0702030708071202010b03070b19083c130c0506131403120706060603060509011503 70
    0x1d81c0d0100241009444c40d039240c00e400c200e4486640350a410000c0d0010381e480c034007550800500a0101c50070000d65801d82c0407410305103030f031207007080681c844a41004013426055564410701140400b001a9828410010340407403200242c6113203070076400e035181d04042c80c05115502208010344c4d5900d480050b408403045d551a81c490030800c0246492140562140b014a407404c42889540d5a100950f44903079400380ea41107465840d01041243e4074400c030700c00a08000d4003401058006070300e01424480c064a248004100b5183c0100024200f91655010540c0e140340001c80032002010284103c460240c941800302c00e07860420400602c824040d0603802d00d50700c0307011004150001201019490119003002603900d4984009195203080301e030041a101140031100006480c03800c44111440034180c1c80b05414030700d05d00341154040362050001030f50715008490355201c0c0f5450310340142814074010140411050714000000d411100150801802200f544c00144075140d4940c051001d45019460 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 202505629 1250 202504379 202504387
    0x5131205070813150206041104150e07080106030c020c030a0807060212160905040908090919090b160207151b08070b04060507030605030a02063106030c14030408 71
    0x22088603507100d0204002c2142e4008900303200c5815040c2c02800c199900c81c803214088082c41001a6501c2204a5008291204110101c0040d00300782d04042603813003240d40c4241c2c000e03841d0322406001490031560f040029400707400400034140d150081c045022900d00280c0100e45c10640800d45038103807084040d0030203c00155203c200b2041c0d50480d00060310703207070012000e4182103008241410b00c0c100d0120002d07400354000b003450300c1e0500c50149081d91040c0f03568503009a00061200a00d8000e0210007101401107903504240c01601480545501c0f41e01120b0305480e00f640300300011301307400b4803500440d48008404e01441c1c040c0e0112014040060429401d40035403602101c441c80800000104200070101e410410081c80c00c0740d081c02035104a409002035a07802ea030407002c40d405031044c142c1c541e101480401c05400c3c681e000f403100306403c040402c0050b0007080c1ca000b044645003102c0b074081c240000c0c208141070349071240c0000354110f4581401c091040d80740e0040d060002500c00ba040040001b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 202506879 1250 202505629 202505663
    0x30c08040503060403180e1504090201030623150a050a110102070507060c031d09060103020c0a0507060903020a08060705040506212706060901090902010c210908010513 74
    0x29050380c0c01010000d003140e45502c0e185c680102400c0c085003080d408100b80c82008a50850802d6500d48210f103940c00c0c0c460050b090404000c06031128501c01d80c10f00d40c0c1c0b041c001c1640da0540c070441181c42c3d8041074102e0000407440034004000034070080c03500185428000000010b9100044034100b20301c5140410903103203010740b018021310a0380c01c01030080c401c603080003400c190045272101c03040740281c0f140300009082034100d00268600001c010b030f1080714400010040c0d030099010700b00410b0503030200c43c01c61550f03aa8080c40d040564102c400401c916150800441ca0031045240251190300003500d01c0c0d0619840c00741083c0074a00409104030804100b14403403c003400380d000c14040790031506070f001e402d2242c104043c1070001000b401c0d40080080e038001c0c4192000030000c1c0100000351030341120781e01e0810508010428480200d040150005800d03020413842c440c0e50480d1030101c96207040d0b805032408090321401c016448000b141e41000c04100e10b54285008030b45040340c01c80c40c0c07510085214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 202508129 1250 202506879 202506893
    0x5090606090a0b1c0609020702010c151d0307050f0a03120b2e0f090e16170705030105030d030c08040b090709060e010f090905060103030c0501060f0803030a05060f060403030c 77
    0x16401001c002c0e0700c081040d15010095030510503448404d200f0400a481c2c5170004601079128607480640424509a04c120004240c0c80d4000300c40420744400241a841c00f5402c6488105407000014442c1c0c80410f4180034040c00b40080410080d0040080140b00d110340c0d005050300106141070040c10703980d10340040c0310351100310200700c40710581e40210f0101409200c8441000030f082c81c800c00043d0103034004040040c000c1c0801d03825030b8101c2e00141c0e002d903213121440c440d120203802190100040d800382899900030a41406018a0844e2680d40d140d40c1004145880e03c1c95801d486400c26051512094629405c010000e4105800c0305c60103000d55500c0c0c00c0b0701c1c0390200c40e9010505884c0b514a0002d03040c00101c03901416a620200c5600142e40d403070180707d055a80345500a051900141d004000081c00752014100f003d20807000460523694500305444003038070542c001c0d40d194100008016003611544a02a440b80c0201d880324038441207030020070004c6c000e50000900340213102560070180044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 202509379 1250 202508129 202508149
    0x40e190b04020a0815030705150c12190f0311070834050c03160b30041e0302030910020115030f1202060603030a03020a052703160509060609 62
    0x80503005550320f02c07050b07100900c496011100c00300090110740c1050160302c0e002c225101110b00040c44041e024203029a02c80c0c1507407180e150107286104529440325030001c000050000c45040c00c2e180441c01402d50405071100040b00301500400d403510070b1400d159585d103000d0b07881d05a0004034543d01d80340418000c543d030b00180c9451079000014403000e0302c7d003400d129400610b203d2094003980c00c0d43c0d0024062603074442504403004101c840c5460b01780450100080502008040300d41e0032154040c100c2c810100014101e500c03402d0310805032040005000007441440404510b00814203850070300d42d20002c0d281e010f2140014856121020042e405e18800d401c510340200c0900c07a01011141e0701e2800c24450201e03004111550860081c0803c03d6500204800b417040c0c83c0070f000345141010701c103812002544003c03510001e12100380031429002c034456007900e6802c030200000001a11120301098500311410780308a0345844420024800b688271f04011680004003a20315035266295900080c0001003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 202510629 1250 202509379 202509401
    0x40f03140a150608010b01021c0f022b0e0607020d2402031509060612011206090813090e010e0a17070b0a050a0506010f0519030605031006050411040e19 67
    0x1d14000d041c00c40c0a210f41c001011206020000c10130f000c130402c01a41c4a010010042030b000d1281e00c0745201c51401030441c00034840300c5205507280b9034907016511281c3e0800d41c4000a030003010046a600c80d1707822014002414108035031003403e01030a940007880178484000700512514040280a0104101c494403c0016000301002e6440389441014000000c84040c000351080e011031000c64014100102107072181e112410341c0342116824001400300801100700100d51540d90380c1180e00200e014036006d041c2000b02c41a0880190386000d141c0c0c01130701e40001240441e40d01d000350140c2d03281000123004500c56440384202c1c003c02c0ca01e41c042c03001ca003d042030161088a2490400c10005040d0344101e00c03c0716050340401c0395484000046400c0811403c00001080e0204661a0b48120f804d100800c0c0808038a0049009500c880200e0b003004040f03020308003110b40302c2d1070070f1100e45001c0c041c40c1010207040c291242428500041c03200280405001c030040c2c04a4002c000c41c00c0780194105940f162 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 202511879 1250 202510629 202510643
    0x7240f120618050a060503120702150a180602010c0f0c050a02030d121103010b180f040c0903140102090306130809031501080f120904021605060108010203040c0b040f03140a 76
    0x40c1d5100b800b900a60b4204441c10181d524000c001054407900307118030800e40d0310160040545403007400c0e240420b9400000b0030b0740e02040342c0b10740e05007400da1a00106030034a5a40d880811118080c10700503000c0895410110559042200d02d1480960150300c0e42d007400103a1511503413900c401d00f012414074102110103034040c0120411003000c40c1e003010505c880000094810064991071441d1001240828010300c550118200441d4a42a0706810b880002070001410782101034811000501102c0300000e004002c15850f590400a001c5d000c44e41c03200c250410703c001e5140601c46400240c45100040c8107440305580e008002082c8070135030b0140c812020000e42204d000040103414103115510900c2804010700c41c0c4140011240000708070069040c3c240c0780d000c0d0510007280704100194200c45d840c0e80e400420b41030380c2404114100041402091418001692814282812214100a504641c0c2c0c0410300b080b080020420b90600007080344e410031450849980c40d14015820103004000c0500a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 202513129 1250 202511879 202511891
    0x30302010e0601060f09030201050f091002010b0411130501080907080304080105010513020a080114240703020d08090312040c0519150207120825050a030207240f12 72
    0x580561212141c240d03200e04950b8503a130303a8441120b040844004640004000e8070782080154082c0b4081c0c44409801e80b14103041201a4021038100b0040c00f03a00313030050b0744401003000141004d11030b00050038101311406207854400e00074101403a6203071042c01c2c1044844000102c48607018005440a0804401607e50b540c0e0346a580714040c110070301403188210800350915410003014800c1320f06c081c645407210182a8070b40900c001041d101c4080c4c0b550001c41c44018149501c440d5040a8600f0058541c41d80d11003c11b401e00901e448e0b14a501d0009121007003060045500e40001070304c1c002083c40c501c03511560368901c0e004a0f14a520b138400c54004e0340d804540140500d40701c0140d82507070140344001c0b40030410340c0812a41d84410b032141001507613405072100c0200c0d070302ca002803520b080d010903034105a66001000002e11950036909940c0b903007001c5183e004145e0705001101c01404c0300c40301280125801100c010140341c103444000e0030310984ca0445100c0da40105080c94076a003641804120b2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 202514379 1250 202513129 202513133
    0xb040503120a2105041a150f0301110a020304180501060504030f0f17070b0708010b070212030f040f15081e04050c03160303030f110a080405030409020418180203030d200403 76
    0xc0c1c042505c0840d101141001e80134030000342e00b00d41c18400c211b4080c0d40d010010100c010310001aa03040101d40d05035491b0750340000d0008121009103240c80280d0700071030b13540349802084404501ca0000c2891440d051400410030142e124040e902036a4000e000e894148a00d407a1035000d80c3c00c50280104000303811045000110b1003000640055806410b061200c0c0e51080000c03a0140c1e402d0040c07502540c1c0a01000000d0b040c9403004802c3c102010307048a28002810710401106e410640c0211030004040f60144034618420307418000150f02414032046a00705240129001c03180d03805440d40c1002a54006001c2c490104901c0112220180603a0b600d81c000340d5600c00015020301080e40401c0c00c0c540307205640d031100d104030030f001e000c910030300c50070841031000840f8a604003030803d881c24441840b007c14038107640e1000b440105000d01209044490341041c0d4001c2da0784206188400706007020304400940c42c084208c0f2002a201c00e00011081d0303001e0030041c0c4811a407400154181030101d00442 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 202515629 1250 202514379 202514381
    0xc150204051804170903160b07120503040b0c18120f0106080a0b2e08030a09060e0d020405100b071b0e07020d050307051b0a06060b040503120a21 64
    0x16a00103a40903095548201d0b0a2100c440081d900180640d40000c544100c00c0104000360014a6008090700c00100c44414020005411500032495015000907441c040050300721180400b991181031480c290b1405448200b81c0800044c100813142000041d0314802404205a092491800400700c10885504003001071396280318005076079140d0320b894804980198005801e0300103a41c01840700c441c071f03615000103164041464186512103107804141c401104010080e9a004e014070301c00850300c0d40900c0030000c3c8051941e9000000b0f10142410304c1e6610f4484440e03401754030390191000b280c0e0f0b80380c0d00c04161907990a81e02c203c1e43c2400c00f042000800450881428809a080302c0a0f122a43c49140703080e008141905c0b000050390060b403800022038080c202459010780e00f8140700e03003040113103a0b8041d400d032200f420310203603a0040080078081000901c501d0020780210302441d4100780c10400840c1d99010307211100140c2a0000c60f1388601288140c001c4086503072140e00302d1614545455000e8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 202516879 1250 202515629 202515637
    0xc12031e120501231009050a080d031a1c0302030c0703060203010317042409030804181401060c02040203060a1d0406140402060403020d0c0e010b09030105061e09070c1502 75
    0x204181c20180001100051030b204e603485104540380050146a41c1800c12041c4003d04881000b88500048001840d50710581c612009044040203004803188000c402000c544070401e1013140b412005084000c183c444858101c41130445a01c000ea4010044c10242d1450040000c260600d219014002c004c1005a4010b14122482200000c141102c601b1454540d802140125211071482e40051003512002a0740782c0441c00031070404d00305060312915182803660043d0856480b01c844510103a21a0560f4419046092506000032040c0d50600b0802407285403400c0000c0d2259030040b01207034036903607184a02002030148000c0804010f240000d40c1032401c6e4100c600b92411883c280d4030030024005411030502c1694000e080034a850700359030030808070078405481a64200710b440008a1a5000030724014042c2005070b00c0701c0e469404000c01c050a40e07100900b26405001080c0d00f01c10f0301a9020a0070311420400c8426030302c581c0c0da11804039264114981d0103020080c0075114154402e51a42c014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 202517985 1106 202516879 202516907
    0x203220504020d1b080f070c0321061715040f060219110c0109050a15020a0c12030e0108090a060c020109020a1e0e040c12031e 56
    0x4a0100d0700702507004039102e07590b0080440b1450500021411310200741c80e00c0c2c002c40c94214600380e60414054059814029410782c810101030207204901301034079455280c0441141300c5041100901450b02c05c03c082800c2107002031007804004640b60151170100c0812490640743c40d91000525111401f040d512240d003071016840c8032a8561401c0355401d50fa84d50a01c04c022403801e0b030b038201800c06030310301e061014011003000030351180004801140c050440c0784559102c2c413001607040c48030214004012210122012540c001c03071503540170b0302d94080d5441100d928402d00054410300400d4440d450161f000001b020002215500140e08081c070520002c11041d540ea404507401c030001da0009051303000000c942c001348410800010707005010005601c240d50505888038440c80710203004161510196000241c14507000f0301d601140c200300034605814240d034688005209006080e88 = true := by decide +kernel

theorem cover : BRFrame.Cov 202338129 202517985 := by
  have h0 := BRFrame.cov_init 202338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 202338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 202338129 ≤ n) (h2 : n < 202517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
