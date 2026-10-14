-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3175
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:53:06.466917+00:00
-- url     : https://prove2.me/submissions/7f56bc06-f838-4d46-b02d-95569b6e60c0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 570863309 ≤ n < 571043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 570864559 1250 570863309 570863323
    0x204451703101d042a06050319090512070303090b010308220f0b03150a1502010f0504020603060f01170a1505030114060d0f020607030908060a06060f0e041512140f 72
    0x28203005c28062a00031000d000d0369100000c3c1c0030a07a41000b2840d91450001c1ca25401102d100c21031038003a840956210000d07009146166800c04000c05112042056032881988681d500310180b554441c4c005001801d40191203000b50f0003104520384401000800e00d00c5151181443d41c017540b2b42100c18050b039100820514292200c4016103600ea68441d0300e0741050b143d005012540c40096084001504c5014140321041c0b14482d5009004100c255010503013641c200f902d00a41c080760503c001174860800b107000c030009000502d080483c00407801c840b085155000e4441c8001c10b038807482d407007204140b400304903070085c04141c0c02004803481650003c881e211020709002d20030341d4410511010f11005006810f0550380082c1816512900d9140c040c0040c3c1c694403404a290240d4030000360440714910403007088030b00f6925480040c92000c4800c40e80120790122056100381d940b5a96000c0c4440c0070384100140c03010038184a02440316040425034041002110b0825a00030140088d54400115580c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 570865809 1250 570864559 570864563
    0x12306031e07150e0a03050f070b04051f03090f0c061103090603070e010507080a02010c030b01170c0901050d050a0504171305010e040605120601030204451703101d04 73
    0x41d140b01e404841d42215040c000c80e04040e801910701001005100000c103200c10b4114040046500271603135100c100d000c5000d10b1180b0396011119040500d0a07440c403e4040500b00f02500d00024a080c0507079581000c4c0307149050541d0a181c04403414001203812060150392410351171700039420b02c440070001a0140c44018015400c000340022a451964003c10a450781d81d030780101740035201d010000c8002d000300501c1000764002804c081c2d00c0c881c0e55002c0c0001c12030000c414886807a0503a6058183c0c202036000003425410082c040040500201062084a000b030103c0c2c0380214180c00e150401211500c00c0704403603004454100081c0c103121121a4080040720350a0030500e041103110000100100840d601c201d03000491307807049010590000c69428148c030b2080740c00f08604408841a03800380d50030300b4000c403d16113100e00d41141524550700b030f0320700c01c409030860307890503941e01d1352507004070508800306409190010041c00800c84450400e50050600e0600c0c0f12002e1003061071340f6001ca40b000e440 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 570867059 1250 570865809 570865829
    0x14160311040917040305060415020c03070615171615020304030b070203070f030e131505041505030f030d0c03141617011715090303060909012306031e07 67
    0x10400304060152640d044403e07815926031510394a00b0010703118a07040710700700c079006661911004210001e02c04d54000728070801c01581804080e60303482000784002c01803141945203100e0300003400d4015840900f40300c51400c0142054025111686c0100f100756004031031640c0700c00081d083c240341c0c008107840449401502a800c2a19110030507822351080000c050300340301c00d04c420701c1c00340b607000f07004042203100903680c0c4101032541c40706003404c540c000ca60310440c202e04428100f10a107401d8102c0ca031406200d0041103c1c19549200103860b0108018a01c007140d00f006c100613038104424441e100340b5950703605091041007030321207840401c484024200048007000381c5618103460b1165800e44131613017480400d803c01d0b5031601c5070742c1c004003420609a4600d10030030700700c100c208401c880103c1c0140d007000c00441c11070312003204005c00460014204110f96581e41101141490105100300f801ca902801008003810410207050506850214821201d00c504035944c41a07140012481c0c111410291 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 570868309 1250 570867059 570867071
    0x909012a1d15130308070b010e1003170c1002040603060317030415020f0903060103031e020a0c14120303150109090203062d031506010908071503110c01091416031104 73
    0x55000481c05041e0005002400003140c1641040a980c5031f01d8162050100c140c41c85540b0031a04080d08681808010045141e00c162101d0130103481026005154001003503500e01c000c00031014040303802580c400300000b0788400081041c441485001586035a50031100c0e440c6107060f45a040c180c0110001c0210346079400144442c254001c40e09541000c14010301391481d5503981d0500500b502c400c65038222540709400518468280006460003810758419403c1e80001c0c608503503403540c00340c0d1405143d00109041c0c0d00c00e82c01182400111301c19030000014041030b041e90000185881141d8102c0a43da51042060144554400080c5490740c104c0c0d031141164031000803a02e1203a002c0c0780c07140c03541500ca00040300d00840c1041c0840703031140f10280e9450941e507569020041c1d968801e07104819144209420040480c1c0c841d40080070007851310070b2414a0800c01e841440d08546901c13030184c802e4500c50035950b000c40d03400d105800072421040d006040b45410f5444060056050b01d4425102d07d036181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 570869559 1250 570868309 570868327
    0xc0a080d0f0906050f0601020118060e12071203060b0423041503030201020c1c080c0742020c0c010c0c080604140d0c0f020909012a1d15 60
    0x34100c481c03841e032020018407844845241a001800040c1c4031940180071120005502d03510511926501c0d826141d5140c0c0e003100507868810003800000c010a88034015004401d003803821390750081561074400c14061190312804c030f5000301140c005400640355110100800c2008901c40078620810109006614110543c03207400a0003d0032030180508440520b48c03070020515130198060440e003240542601d040800075a0980c0340b585451000c50301003031040c000b0501904162025000491045445411801d40c039a140385101c1403600c43c2c44910340810580c180809803000360500781c000c0c132441c01c0d03040c05140840107803541c0c507030a1520304029001100c0d8042c0a86da031214401007950b1020f03116541058200070202910011002c0c5203881b401000303c01b040e106219000d002600310366900420300b81e907030070000e1042e4041c002c10510740d2200382d004d4040504c1f815a0b03680c01030403250100c002c174001c03030090138120203069040820240845d031b400d480d444280102c00d030700c8620302000340d55030703012 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 570870809 1250 570869559 570869561
    0x160902030a0e0d09050a0e06090f090c03010204470a0207051903140a02090601030c1101112a0a0f030203040312031406091303080a0603080c01051602030c0a080d 71
    0x1006160b81c1449006441408160031011401c140d400c03d0f0341c50f0043c1a2a41900304250100307548007904101007400060303003c1080444035030404c038400c0a60704400c1003c000282a41c22680040f03c1281103149219002d407903140150000c1c810329181c3e01259501c5504440d00c0e070038003c5002800c1400080ea000e0050300c02d00121000e00001405070340e081c2a0204c240400c40010301048694003103513101c0d080c0105000030680001a401400c0c142c45603a11001140584120802d00d01804401440068002400c1c010110400c0c4501001c540380d1004007002c000321000f102d002c0442a600c03c04d41c222030032000c40d6142400b50414105085580349240c03c902e58411a4800f03450118101040280c2542c5500010804819a05008075503143d06042011580c000d035002188104440503200000340201151644a40240c40001d034840e0303207845034115580801800c514a075500d90402402d4180c210703030070700b070b04003148029410480d810700442d60794140c072500540845001f2404190182117 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 570872059 1250 570870809 570870821
    0xf110310110c06011211040c050408030307170a1401030b0403210b030115050108130c090e0102030a06080d1b05100608010e0d0e06070803130b0907080f160902030a 72
    0x18610810800e0003908189000350040502c10711203000b400c0002800794500080e00f140e9907046040208900e446a08110003400800c0344a8117001f41070000203455503041c0080c6100300c0b8181c03a00d40007905401449100d130750004010f14041b902d800716030001c1d030444440c4141501e42c8070325844929240c6042c140c801c0291020344802d02c030340840d0741c10040003454119a02804094000340300401110304c0306070b80c0c0c02e002e000711400601030600241c80d812841200041460140980700c017442d859440742425a00840c3c500e0040d0b039000810300c10300103158820034006103920b401410400c03240200082c0305811410248103c0000c3c0500c6106126007800f0802c090002c81c2410005940d84000b544d0190085020340e018600410a441901501407034483d680408000c0c000e902e8020070350b0350b80740150005003102000d2081720101800044a40d808980100100d0004084c03080c901000d1629101201120b4202c580105204184403070652580c9010303180084405131b102d0751089415401080c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 570873309 1250 570872059 570872083
    0x406050d0e03070c061106190f1104060e010e030102040501020c01180815240a05131814070929040e070b0a020f0703050c06210a1a0d0f1103 62
    0x4000307003802c20813a5542c50f0300215506919003010302c1c144001c21300e4850300c04a5014071640e8250708680800390302684030181000507a1400907082d0417944030082321740c006400c418003240d00b030400f10b000c40d030b0411000c0b0740c862000c078000c0d4541410301c00000e40300c0e00709074015414002d0b0030f58510340b8013045031040300142040d6421100008420360a0f401135020944540c515029030000d64001241806000c461002016210101d00c514002c1800305d128840f0300800046035031095013541c0424240f043d40c1d8058054140d1182c00c020313030414981082040e030f1100070150b24200181c0c4901030380c102650700304d4021000510100c030b01000420081d0503512204905405411000304280c1030b20341c0a09049800c65080b210003a011110f4550b49100d0ba001c058159402100d00d5161840c0090040102090b0325001502503080e0744802c1b100700d10184c52118200351038a0b00301c1d0609005c0a0b01c0f03020101e045038209011070030742d16211040ea000d0300c0f000d0060381e035136020703500241c03003c0107642c800c16 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 570874559 1250 570873309 570873313
    0x9150e19090305090f0f03061b040e010828050d0e06070b0f070f0306050d0f11060c070911030103030518040204120b10120c1403011d010c0807030e030406050d0e 71
    0x80c1280c90b00805540c801d00d680c500c036400407003580c04941000e507014018224058002c05084d246d40800e01420b0114202c4005800d80801c8003182607000d645a0768020602c039001450314901d00700140c50f0054101c119a01d2080000c00e011012400000350702800245a0903c102c000b9800340c0440d04e148241007014107003644100c18400c0c40c1011004507031040e946a40c41460109400c00d0440c2510102d20540783c0c84003c003015040400ea00300101241c451141d01103940c0c8880480104105030040e1a9a2800e80c01c2150308020aa4041c090422000d500c07070109441d5604560b0042e00030300407051080c060183d10b040c4000c0070703100c0b03904a03805002201d1a03051980c03141c1c0352612405608440504070480000c0002038060000c481c0c4480c9550b1014041aa075801c10040c01d440008120b00c0560564a0382e5420b151b400e040801103000e505850004120881d03403800181420201134011001c0610300007500040c0013006c025242560114503280341c0d51200504064058021282500b00074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 570875809 1250 570874559 570874571
    0x120408010e070e22030509040504080319020310031104020d0905030319140c0d11040b090a050d051e01140106030e011406010504060e0303090619080f040201050927010311040609150e19 81
    0x84122f40000d50305c1002000d0081000c5000b104e91082a0b00003547c3c01060010040340c02d000141c04400c2a06800002400040c2130410305240031040c3c2e091184151400d800000c2448001104405003102414040105200f4501106001103040070f00078640004854081740010302c001141c0c102c101460303640c009458680d502e07040b83c10740d21740c04120100e105010003000028141040da218200141d0040003800e41c0405004211114290300c44c0442c420f9546c40014203540988030140d18081c084598000505151100c50b0608440c003020080d40314030140310810009a901008840940d1143d2402840000c05000800c1c07850080303c5140f688080040742180c0e00001d440545003010009030b440c00c002d0344030091070114107141540e000e40003507001c008000082c1000c916040120b26241c0d02240400e0402380201950203007a00700300c07864215100ea070582860103020b06009040c218800300410b40c001d440e011444202407048034418514680081d08280c1e1048040c0313040310701c140c014003103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 570877059 1250 570875809 570875813
    0x6050702030405010f110a0b04290601030b33041a0d0507090f030204020702060c031b06060a06120b0f0a030f0b0f01030b0a090203120408010e070e22030509040504 72
    0xc03a0418015503000845e0480203603d0303148601c000245a8625401800c6401096210300c40250401030080d90340c7d500c54203109400d404124008d40248184028043d402d0401400042c19600e00c0b41603141300e500c07252100600b092802000400e04d01d42e246003121000d075070903002e1000703000d02c0d80f1107807032901c1460958682c00302e0a0010300405aa40508202560b110340c0156003402c1940140c44101c5411501400181042d47c02040b83c1d038002040282060f0540b240f89265601c104000c01c5400031601682c000b052040020070740101040354885541e905001d0000e20010042403c00705c41500c61082c1020741c1c840b1391707101c005d03203002800031540180c4a081c21020142e500300112220714000c00020b030110768818005050700c3e03201010500a458002145d00507141c0e81d00160f82c1800b4648420250f00000380c010402000d0340b40000c85c0700c02c40600d625040c090341d50b00c030651500095081181180b50881c0004441d12200c1051102032800c6c181184c1c0c0f07004a01d001c0d50014039060034001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 570878309 1250 570877059 570877063
    0x30e030a032006010b0d020904021c020702030f1f0f06030f0503040602100203040f080304050c2d040209010e01110703020603071d030708030301060c080708070f03080702060115080601020a06050702 87
    0x41140b074800403030209031080c2404599101c3e0244108000c00390140013184480001e40c00034502c07014014000f5007007040d1415080e040c502c2d944031710300c5e809a0001c2c0a82c11400c06000b00c001260107000a040100c81c9040140980303007500c000070000340e6030755030745900c0030040c0c1c1c1c08031015540090018580c0b01c02c0f4502b8030341c0d83d801405030a0140c41442411501400c0740d0084a1245a208400034001c40840d9640340306600040c0c02195580540b0708840c10688600c901c2840d80c1503106154541045450340301150072411146031070196004010b058400e98020b0004082c800d428030303280a0038105000030504008040d00000e60091001050000381d079408140d211050004c90a20490a40142c1c10140d4640451191150035002440100041401142c1d280101d030700909c0d41e2480c184440c1e560700010342c8060b60803958180c4503a001400e050340450381c1540094540000c10f465410071803005221054182c2030410000540000344059100740021850f880c0d01c0541072003e03060401000e5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 570879559 1250 570878309 570878327
    0x1e040801020307120e07060305040503122802090f060723101a01120c18030c080606091b0706020705011802150a05040e0915010902130b0a0813030e030a03 68
    0x10f0002070007504c00d80000c404901c00c1e40e00810445006000440c0340c28010780103400001e00c26561404140721040c0100402e9581c503100301c0344480d035041000c0d02c81c000c0d20300a80c1080d030120890352042c0488641e984802da08d100c4004001c682c4261500090f01e0301031040e86241d9082103050100c1c04403d80d003648002081884141a044280003c101003200301e50580c5400b003483c1d001400c1030003418683d034203541c00290103104c146030404c543c00310000d46481101c500c1c0d008455025540382c08210000e01841070a0700b01c441242d401c0482d04091000140301000d10741c0d07052640030001040c2080113120781c100d802c1c20358004000c0c804a008907500e155882051003080e4080c021280038400003111410449200c401e4603220302d0704050070005d01d62502134008040058922466040c2c51143d80103c80190007029010005a902c164100d01d28001c2000c5a0049156500c140240d490954010a846a03c180d6103204134000c401c985c101291088010204660075001c2c400b903400a040d407005900b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 570880809 1250 570879559 570879571
    0x607080301031205071203093806040507091404090212011e0b0109030b1005030106260309061210050405071706060a020613080f1303031704030807051e0408010203 72
    0x2e0355a5915903e0645042c402e400c00242480c102c8411110143c1c020303842041d40300d010b56110070f01e074080070798045800c004003002c1c51460031040601c03842021030030343c18a46c00385064406021504040700c01402c894000d02032800702811a075413490f215281e541c005110641c000b000186400d142e18806802060001c9107035000c8048100b0b1804414510b02417002540780695540c1107561960300c0700c1c8803000300580b0780c0481c8000104005200c0d6800d00480000d0710801e42c01c00690381d0903604d042c41c2a07109107a080b2083c0c0040c420540e09540c1c1d1405e441455269001045180e5141d03100c8100f02d10302c642107541d05c0b03490701080c0100154060010040e9100d0850908120b03160708041083d50301510201030010b81c041d000142c04041c5030401625007900c035040080c20900042c42c44c5d80b45030000d41449a031000407960400074150300015489142468084402c03a500342528001c200460003042d50040c040001403550702010392000450310f0403031050074030340c9540e201e208940c080c4d070094401e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 570882059 1250 570880809 570880823
    0x30a0c030e01061a0c071205152a090112151401080c040b0c03070f120e061e030907030c0801230c03010501030b01050403050d1107080c030712020f060708030103 71
    0x1c0d8a0035400144205000c0da081106940200103604080700440c1c0d01c0503000c91100d024420000480f40e4011084218140c45140030307080342d080100455501e404024820350804449182c6480c080000c1c19100200814801d034443d0342d042c0050069405002000e4130079142481c1100704030641c58009a171100f80e625030314038002d06000810044608160070b940000c1d00b19030401c8104540c090000c0100b4010141005427030074802c2c11740710390303540d900411001d032000130016079000319060384650419044d1a04031a010b0402901040c13022601040446001c0506400008544000001c0050303c0085911100e015209134403a035105000e032070408081d041c0002c5594035801400c048020041c802d00d20780c1c4226003507030718103030046000c0c1c404c0340000f034180801017102101041c000d01c0b4141200c100398407215107500300244100d1034030348650f10282d090303001452441900c0d54041480c0b411280d214070258413494007800018850500b00c44001d60004000070802c04015160000e58120381c01080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 570883309 1250 570882059 570882071
    0x902030a06090312020a050f0d0b0d1109060414060d2402090915010518061204111e0a05091e0f070f020106030b011e030213090507090b0a0b07030311030a0c03 70
    0x15a110981c081ca840741c0011440074003c039100c0b400a2805003101d14050140400c0c00030510001c55503200c4400c105a403840e00c042442c3300c5d181800c0e101c280d044a0184d030200901c030003030f00c0c4020506030003400300d81c401c1c035840c0110350510158100034503106001100325a43d25612002071002544024951030041a810b00081d1420310460b0309912030580c10707114545040c40061800782000b4903c3c0300c0e80d62181c002d201400c6c4201000c00c02a110303d118800003082c955420040240d0244851103a0a5060f0a143c1000d80c03902ea411a500c119003080d2002d0a10b51079018045505042d002c04402264204000b0052a0208a803995000c0c500d961503501114901d140100e0130b80d00903000280000100703000401620f00c01324011003003640300312160211700c1d8481c0e000400c0900da51413001041911035a014042c800240030320001404204da0030008404044040b07402551144140c054040f40442d1050501d17020350003100100c940c0080c1c0680c2d9150500c006401406803507415400245405 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 570884559 1250 570883309 570883337
    0x20a09080c03070522020d0c09051e1c030201140406091b06140a0507020907030605040b04141302011707050a08070f09031101110a0c03050f0a031d040902030a060903 73
    0xc43d005003500c138050138040c8007030070400010f1950303440d070104440faa56082200400981503441840700b1494141c0d901c8a25501c0c0c4010403404001c5100e044010040402c003031482076580d0050a00c01c103900341da050290402da801d00364018000e10381c1318440802d40384100700c100845980080e04007403042d00c0320440b40c050f849203021189064000e01010451000060b4450816903000e05140e0741640781051130190705074045203401000b52404404644c460b00144061b00e0300e40541c1e002c40005407002c2100000468815520a1024021484044203003070044196485072701e120300c041000c44070120181c1044a8000c142d40d001610880005010324045034a59105004958110100341d845030811411074880410142c644100681480b90503040b406502106026a10001d0f008800340d103143ca1850501c80d00704045a11f13410b609400403481040040d4100c2c42284140c0e8240c55460740305002c0e10f011030b00410720081c3c042c0d0701d48600b548010402002d5008040014400e036034046c032201603a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 570885809 1250 570884559 570884563
    0x204030503091c08073819020c0c09061906020a030e01080106021b01030e07060c060c090f0909051204080d020106060e1c1a1f121104180501020a09080c03 68
    0x300f00188259000c01c00342002c607007a0241410007000b00e0f009480c2034020400d011403000c0002c60b4800d24040c192040000e40c80c4100441060a1840d02e01580b501d5081d20b40d40e502d40043d8400c0500c0f4010030000f00d041515035200b00c2d007403880ea524511041c662903100203955881a0102280000d40c1c1c04141c554a502c6000058100d4116030014060401c1000e440803020041d0396886040540c3c42110002c480c10402c40c510007000b054a82841c01d0000c0c2c1850800e4074001c0100301d0612003070450070010051041c100d413049070225000099084181e183c0701f82442d4030300e10b039a001c840c804280803420210201d054000c951540e0003c03c0b4440c4d441c1d0f400e440d00c1500c0d0540603400075041450078600c031844900030100c14420320014800381000707041010011010748001d03003010040030b52041d68964000e22680607141e80118911046119901c2e40504c1d00710060241c00340c0d44603010b1782c1c0c03554620309040c1c0e1416400002503446103424135000303280034440d1041803190320505002054a00380 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 570887059 1250 570885809 570885859
    0x4050c06070f080a0e09150a050607030f12090f0c1d01060e10020a0203010e03120a0b03060c180a0e15011b0308070c140d08061e0103150504020403050309 68
    0x40080550203002c40c0351036658443c0c0015201c0d40078840030741e08444251791b440c00c206108001285001014020150a0110703c000303079004a4020082040740001107500321032a9444500e20345040c0004030105003e04016000340b00c0c004042e21902c0f0310720003c020080e50f03c0c0d000d4900380010b5000034030300e0f10314007441c049003841080c010032141e85506106003407203000c40d011144940111a64a00b9a9000c6801c681581f046c1d18038035007001c9103607950b14040402c92508166524000d010001116000a4807a600070300000b00c184000103860701850010306d00c1507000d00008050001c5035a0b07500c940e4a060100300c0d01500c0c0c1002c1180440525802441c480400300c1e5081c0d403030769541229960641e02010301074107040911000100f042d0000c2c0e5041c015030041d101130400f40100e84603504000d041290040c1c41e0300c1c41009800315040343c12840201464540d0400d28012501e100d11a81c201e400c0c81175a003003c1d0f0460300000b00401840000001010600800e44050544002481003d011118 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 570888309 1250 570887059 570887063
    0x90c090d02060a05071a151009120f060e0d0e03121605010605090c0703120507050a0c17070c031203021c09060204090212100b0a020d1107050a080604050c0607 70
    0x9105520009802c001c40a000f0390b00480c10942c0c42d008094540103041c60b40c01649100644e90101080070304407070b5001401030303840c06585010903182c03c45005000140326000d5a444451014490420b105042a5030010150450304c00c0141c440503010480e00c40041480010120300c00e64000e41e900d090009030200c2180001c400d0070b080903203c0c451862030204108080e9040d41d2980e802240a43d218400c940c080c40c0f001e1425951000d00b440c0251100f6003081099062501d0a010800155042401c503080f0701ca2030315207030b50b017a1143d203000500c1100742180940801070114001c010080401c0340041030741d01410900e21030a09041c0110140e2040f00c2507400d8450107080f00c814600881d410840f0118130400000d03041030345984488080781c100400c0580c190342400c00744220080e9003c60b210262280c82c100c0c0c0d01e04161020069a1081003900560400061454001a46000788800c1000c1c1100a1241000c6655021300c160344110644003621701d805880c1511605103401030441d04019 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 570889559 1250 570888309 570888319
    0x40906050f04052104060e06220e060603040c1418070f080c1e0c01060302032d01060503120702010e0603040609050d030c02071a1e03070e0105030c09040905070803120105090c09 78
    0x1811b000080b120035040b548015004401440080d08081100d0b480154001e2412810031b0303010710b130901101003220080c003540d01411013002408040b07604160034000b44c0d4003c0d111041c0300c408001c00b1500704610342611182a00106c000d0242d020342c0a136002000100700d03a074400ca107032908594000c03e48039841880d030750384c1e2010111504c035100300e4005d04034410346c0300e00000c4c5040d5281c02003414200021411541c1842408817000c03080d032880601054030062000801c00d640c01c20010036600c45202184202020300441d00800310fa00c00c0c446c4103c10000a02403548904051416802a14054108540c035000d00b0201c140c6d22031182c03146c400003001980c010807441d13140800b05001e50402c0d03c2402c46121003000312040c8100110703140c070401006030b60100e95034a4542d00003004040c0703406031a0b04001c010428408840341078401c3c2c5802c3e50b01242c0c0018100c3d950b1500c98600725082d4010b41c201c0c0070228214052a2881512074125007082d04d201c10320f0350f01d0780c000c3e0b0020320034851496801 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 570890809 1250 570889559 570889567
    0x5011719020d0c080106080a120c03090501140904180308160507030507030e030d0e01020c06041404110715050a050f0f07030b04060b040305030910030e0a11040906050f040521 77
    0x75103010880c40007a1402004440c820a071603560301425600c8542096603030340c0c80805610100982c81d110901c3c205110b02e05820b02c03011035503004040707921030301c6024100540c4201c41840741070700008444801c074004008020740031203512518000340c0d8550307083c0e002c2407500300061419510807519140b10707403082e51010b1a240096500340c6490700200c00aa00f040b503240f034034103d1a1810401d074840f0510603200c2520a108071f1000a02d07040c010390600d805044207010400854552a41c01540d40c030b011a00402c81826092002c0c24a0140000c00703047d00c46882c0e011101d10025900c901d000d1200e56500f8461551030300d256101044c030940341e040481e40f2490008a28a102e42d1120f46c1c0e1100003800412841c0e078a603540034454011b40c01c00c0d55640c100050305c0f840ba03c0c28162030048440319003002d000b05086419150744584a8103000b40c004020f001100030903503110380c40341c140c43e9448441001203080401079141c41607400c1f00c0403902e030b00c030305840f00c3d500c091080300c00e035550000000308500e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 570892059 1250 570890809 570890813
    0x2205010b0c03070318050a0e0402130605010e0f040b060313062307030504140f03040f12080912010207020d061d121917070e150712140d050a05011719 66
    0x211050420170110049100e00891142e9031100044000c07d1117240044650a15004024001c0b080c181b01004075480e0031400c01899030801080d003032052040b14129110841d40b4082009001c1482c2c00583c401c40020401c07581c0c80c401e82c00b800c8918000c15042155203110b8108215a40610392440c91000d480d000060001d48280c0101d9446446601900d03503244810528502c2c0114040144645030008902406200b83d00404900100003070541c0f07082540f01e82c0c950303000501c601da600500440e5803000f05041201e09404803131809038054a0a504c003181410000000c00401d144235034640100d51007440b00103000a08071010280d0310b01c0d400d190000310f09203a440e00004180030810310542540302a01044003012061081c6142c1d00c0b8203040e00c621004000c0381011055503a408024280031440c0402c2e10440b03038845291380b80c04d020003814548901d004546c05164031244900317003040104807806c41c0710380001e4100c40c640107403001c1c20200440e0759a141c003148003103400030381c40319004100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 570893309 1250 570892059 570892067
    0x90f060c1c020105092104050d031404090603021005030601090918020d0c090c0807090e180a050a0312062304020c0f071809051507020c2205010b0c030703 68
    0x880c68246108860440034851125000d1040200741903016035035480400c100c426040c40009202c001d5101e42c08031404807800201000c1c0114001d49008400d280e0712082014005c0c0d902038501e000424103031317890760341e540054005000c0c14001240500d41520041032014061030980380100d805031540b0217000e08003e000300080203c0010f246074254100c0541015880c0d540c80c80603039900035845144503034103180c03d00c4260b683c400040e80820a07110200300c509540701e15007000f038071610884004c05441e1904080300202c0001d215002500660b080f08041000006903500541d100c5d0315004400341c0515440300468615110b5250b010125501c04191f200c0e0b88078600140b2400144010704000880d0000ca00e0819540030548007640700701400e026400c6007401190396410346d1041403224440540c2c4007522a024110058415807584d804100460300a2024842e40300000d40500e44043c1c1c0d10310303041191844c00001009035450320002190381c4018030f0441e50b4a4011000a514103511650115 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 570894559 1250 570893309 570893317
    0x610080106270e160902070b0903030601050d050a060f060206040302060106021f020309011d030c010b0306190c140a0203041e030302030301030f08090d0c090509010c021b06130609061103090f06 85
    0x41d49501a400d01450010b8080c14801301a0100080040e113030000741c64001002400030f444960250710500c1013045a0b80e110b000c0300c0100c9144400403415444e0f00b00c02801134010340c8c1111004005076800401d80d180d0010b54640f041e4040d900b107032440c5c0daa0b0341060b611200034441d0400c09800c00c0714105016030692b0011034001004030700006603442c0b52000b29111400f0382008048641000070400c200a07000d00a8002d41c03d000c40c0a0a42800c010704078841c20301c1c81141d0205071039110244000041d003c1c661003803c4a1401921a40d0b401035144c009469522500441140c001c2d0b00130941c102ca8007481804c0f040e00c0c0e041e00218550b03400c0d83caa1440301079032003008441006082020043d203440d4161041d1113a071240c6030079141541455500c0b002d8400040c65139941d40e14210541e144c5d140d002400c503040c0e810040c010564240b044020030006d01c0f071400c01c51200c4203c18000911136038481a120100c03a0150745003e40a19420141912841000f0328554000c8201850001ea803070004024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 570895809 1250 570894559 570894581
    0x30d0302130504050705040501021002090108040b041104050406060609120807140a060e03030703061205060f181905060105010203040317090d0f26040605120c0408061008010627 78
    0x1084800e642c88000406651007250940d00180000c50100201d51301006528443c00c000c090643c20041e80c0c8000a0103020010300c00b0b81101c0c80303d03000c078040c0b0491042a10103200d001d0810b010754903042c05c00320050a454443c480001e0b58140b00068500c5030b00010b6101c171544190382626210041c0c50f212804800380100400c50f0158410110009240344920345841c43c0140103940c49182130f05000e011912564041151140c440416100080340415950391018401e07115180680740c501c8075030075240d41c81c5601b042d03501c00e005004210040c00780306042024810740407185d04d0fa1302c640049071070340030318800180754a0450041ca96a01900405400d207000003420562072441143c8800b102c003000844141d401426503440c0343d990352048810310303880c21418002185040e01e0007400420328820a15020b42800102c0081010920b0103012940203041c9401214560305041c0894031451196203d169101d61a05a0004040580e11022001e40e400c1d1110f0780d40c8032040c525640b001d8041340d004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 570897059 1250 570895809 570895837
    0x70e030a0b1506130f0501110a3302070203251505070b0117010b04110405090c0d09050618011b0e0a0803030c070c0e0603030301031b030204020a032702030d0302 71
    0x5145416202e010203050103040844031004128504185007800810302d40110f07041001d6031074100305234800000c1a0120b00d03844030030801d4044101034940085550040c0340e04405030703411490003a20303000d9005045103034001c6040e55000144282e24400f41800080e0440c0510b80100c010007660a07054560680e458107030902901d860402d61300d03000c0004098212841003080c0d10242c0e40095002d1040400c44882602e003000010f21841003021a4040c52041034410103522000803a2007a8400550700a0421000244078105003841d0468a8100480301110b00c030414104116812405005501900000c140310060001d0500b80803190103d00c3d48040fa08400001c00c005081c40c02040190700c200c1524040a403125010701d00700c0c10106240e403001e00b5548011003445180d40d000700440e4110ba50144040301c01d02ca2900000c00389402c3c942c4041d50091000c5207890344150540c01a00304440020303d01c100440030050540320050f031100c8041d4244c0d0114a590a0740390183e401008280b00240f1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 570898309 1250 570897059 570897091
    0x901110f061e0f070c0f141f0e0a020303190507050106060f1d060f0a05090d050106080d0809070506031f0612060506070c03030302090109082b05040b0901050a0c02031e06070e030a0b 80
    0x4680c6140c4500021400c00e9941c8523010b1009400451107051000340e8100c01508204d0003903000079640740110602080f030113103505420040c06000b04112506558010004e02101c2d07a0791201030200031144034003102184090600c004c00200e500284026480c0c01844141000c0d9400c00e4071215400244030034050040800c04605195190060381c00c2c854405c4d8000326400782450b5510307007001003c0448206000b40501441000c500218155013540c00c01d6883c21384941d58041c1c0da21060181002c0690440020302c40030900c0c9074050308000d8604421039060002540c0e032428040e5911803d900989100e140f10710600009100307400400480405240c9141c0c00b07071702e039005281030644001d40d900c1041640060750590140281e0a43d00d800d140b42065401c06181c055040002c2c464820158104580054884211401804030181e030a03005800c817038031120a0700030f0300005000000303810202d12585000414081c855000c1510700c0001401401c9502800d5030b4201e00d008026000c121400323441d903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 570899559 1250 570898309 570898343
    0xe0f0121171c1b1103090d030216030507090b0d020105030601211118010305040c15170108030307020c1504180603020d05030a0306090506060901110f061e0f070c0f 72
    0x802c11000510065000503107640140011094800820625828060741401c0c902c0f149030044242d980c45a000d60300784031300521501c0c089041c86040c520383e51551104003404018004001404029a90100c1d0104402c0c8034842c02c00112800c040d90003400145e003000051115442607020558a0964005080b51b5020004810040d110007154a0918400104000304d850b0410345000712001000c6c2400c00c400d04268440c8180d00c601d500402402c0002c041d1b096030241d124000b0408030704110500102a5612038200d02d84030b034401d4038410018821003402c038a0602d000d4101001643c01a21154501490a200341308408242008054060365480300007001d030b16100001400c1030700c0f8401035940d030140e808029007110003e4000c01c00c11898801004415101c400c104c841c001c40034200716800c03054030806a4981413000b40c402a0500641c0240035071a00c2d6907284503074107030041b5143c5d9043d54610070100b0100c84210b9850000840c44c2048001017401e8419540016020b40d1f403a401c00e000e04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 570900809 1250 570899559 570899587
    0x70f020f1c021002190c1b0f0524030114040207060204060e0915030d030506040912050d110903100b03030706110d05250f0201060e010e0f012117 64
    0x90100300300e40040004420a190b81c10b00030320700301c944101d204504200c4080000444000113040c00d00074408034580355000d00284051010002000e1010000c68a880d0050b05100c010648943c0303002c0d02c0e60000f1500c0c86926903102504903d1626030072070540c0e10f404a16005c03150026010780e0026420001900840c03c1030009002600303182e198a202c5c1c06d100d40134000300402c0145035060b044001300c00c01202d55004641d404005c0918600410140c42d41c9000400521001c07500030095814580d101c215550440c3c017030104200d50031020820f1402607103103c062840340e61280d0360f05170041a046100781d002540100c2024202600f2070341099071640d01c107412502c1e6910a503400b61408203600380c0900e124003550381e010240e49000322040009007400c80700d091102170700900f8480301c0c12a410040b8407d5208200900c80c3e071a1568103546e4aa24035400d1080170b481c0b1014110342c1c41c00218221060000b00c0140c11140304502c1d4a04025842d411004119016280d014002c00c0200c0e03a400084 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 570902059 1250 570900809 570900823
    0xa051f0803040501090f080a060b01090e180f010207030801030210093204060303020c0f041b030b03061812030406020d060b0c0c0f01200a0203010c050703030c0215070f020f 76
    0x3000c0c006660700c40c142800075088603503a170b2210143d01507902e01071002d0b140210340c0c0c040666111b4030208500c0641001038500381815000f8803000d045501c2005034081500048001310034907901680e15540f0780b0b4103154246d106031200a404550320704010001420f0800c074039241586549031258000e600c503018205103103008440400d00d0741ca10240b803000c0c0c020740300100540b120112001c0010380e10750358000c0e4980d00b4a40c001441129015990340640c0c60355040200e40c10620018041038020310320001d0020818003200ca40284180c0c0001554161040404802a8594402003800450034419100550320081084a10a0b000d00c40007052807103500a40e030252460682040e1070310103050041c0d01c3c2c041400095442541060491b400503608410301404400000c0301c1804d048007001c0e0045d20b04890020025050361070100501c0f03e503030713200001d007000c00d1003a0750600c105000c40c075081f030b031724000b82860000343c07400c05011402c1c0c280611002d56601600b40103840491907201c0a8034240b4613 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 570903309 1250 570902059 570902069
    0x50c0402072003150a02090a21290118020d0c0f0f020c01050a1209150204031a010605031504090212100609090c09150b03150f030c090a051f 62
    0x1002d01024640c2c00c0ea20b00354000d0440d815002411401c14009070004180e10140c502009203074000383e8400b0a44070440c0c0340d030107024001201c601c280f081d02100007031000d20301416034008a000ba8010501401400301c1ca0101c4040740c02e80361164280b98034010004145400e12001d07690802519000c0d201c070b80900e092015180c0c4071550034600810002c0c001a44d0301006070115000f41c845444540c0c3c12006890524080b482c2140e010902015135070010000e901019141d94102918944a105944c0040083d20f00c80c03840500111447d110b40d00c01e03641c2c04e020309000706100707100050071000303103086601100c0380007000440e00c040c1d036402051803140300542c480c0c01508240b0043c0c81074403a9008840c010180b04070308104055403a154000c041540b40192000c46860310b90601c1182592040d0402600200c1822552410102185c40021110042c803034050f04100440042602e0b02094009a0140107000d8001e070f96a0150b0b1000240001401d54035a01080e0480c0340b90108441c0007070000d04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 570904559 1250 570903309 570903323
    0x9020f012a03050909090a231609050702010b030303040c060c2405040309080c01140318160e10050618062502040b09090304060807090902180a09111204050c040207 72
    0x1200e4100740404401d0003840f001c0c00350b1044d141d87c030004003400550600c90911804c46401c4040d4204481e081c0105050240e9082040c08004543c821844d4003a60158405400811003840400c062544901045501800115100d582040941d0040015158891180d0740700c840454110711188416214126882c1c1002d075684104010550046034440203000100b0041086185c580002001d481c00ca11a0500c00030012000c1925038031700c5a02d660703d01e00c80e4429a4650341030b04c3d804568034072482c4038174002d40004901051415204c40710400c00c1d0f0300040d003007524201c0442c039100c2c01c00401c5001690001020400301005109c0d40074148050440040303000c00001043c010070064a2013042818031a074031000500c001d000c3d0000403075085030214100031140f0740d2440c405a440b10740950180007520700004804201c0101082500758010003100d00600f07642c0c540700100c0485201c4202c41c0001c0c1c00070001404900b203220340d1558000d1040301200e02584600021070180d80100204443c44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 570905809 1250 570904559 570904567
    0x70e0d02060a0f0305220f080d06030f060f061503020a2f0f01050708190905100c0f020d0f03020903160305030306010915090e19110a1209020f012a0305 67
    0x202d42c4c140102500461042d04071560a070030150f030f11400c400c0e880c000600e2510348504840402601ca81036444041c80010b08102c000d90302d05018540d80c2e1803007812240302c0d01c0c3c202010143d0340948510000d0b2110032285102c030036040b030400e80003540121004400e001203007040c900c4040d008200e50300310390030100060403510014100203140612a9036110100d9040c003040040140e80f10b150603500036550300c0c016040c001500c40c90740c018214000301078401c1c091103240d89210000741c2c00c000e030f41001c907030703a0108400d4a903a8100c0e100d200c0c050b81c8000282c104c03082e00c08014420b40280c652a0070081c2030b0341d0407000c840d10710240030303095030f2049610b6003022080121560304440c03040002c114140440c1c8111000d20001000c002c0c007400781242e030740c6001000c0b44050300480c541110100d102c0c4001c0010509080203880f213500030303141e0240018082c131a0500458a1405500c140c11f40c040c10030707501c3c0d4091500540f0b100c0da030403e4020419000c1d81180010742860030000210078000e481c0d60ba55 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 570907059 1250 570905809 570905837
    0xc120201020307060606031e020717090d05010207030804020901093b0a2102030715050406020c060708180c0321070203070906051306050607061a032506030e0303070e0d02060a 77
    0x205100400c8201c005104ac00000c0100b08001207200d451050780400740c3e1303a00003020002c1d07a060060440580658400300e00a400c040e0404000d034007c50080712404035580e40c0d50f60303960030303114054400400305050405403c04081410384a2042c1c0d03910105030b28907541400b031207905c1c08a50480540744520580021000700a208240020b500018030145140040a44995504105290800c062551f0340d1000030240031450341035130421041c00c0b050314a90b04249a004042d42c0050340c030088501039080142e101c800c80004c01d8680ca072000b5001c2c00700c9401c410030001260320509070350300d440ca5041002c000103903000e11000016010802002038034500702010b000c02c108107903104599044c5044000e110716990241620042c960200b030114180c0e41412201c40d80c0404800c155805110300510746103520080e141d48000c803040c05800701c51103a80c42404030180c4040c2444012260001c00100715502e11501d004490300b44003401c070303015840c0d850b0302050251f800414000d0021b281e080e05080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 570908309 1250 570907059 570907091
    0x3090a08030a0c080a1211130801051603090f02030f1b0a050d020f2805010318020609090c040b030c0901111222030807080913090c12020102030706060603 68
    0x40540300920003103040460321075001e4081c000001c40035001000100300d05d81600d116090152103588103480c10301c8200c800401803043c540004949150070791200c3c001094000051040c2c1d80300300007040144520030703206402540248580301003030750380c80240d005920150700c08000c00c00300060070400070440ca000701040c1420391720740d451a581c402c6821940030001d980c6d40c0031080c18502e4048580003840080c03140000c50011100000300c141e030500c4054400b800000c2200a0b0032110203072400d009036102d003078404442c0520100000d521420502076011710781030102489501217098040146000c0e204c00e03000d00b079500102d40425070b0360702c00103070551035503406061441003000000051410001c0c200394041240161543c29174010342020601d80c0070008a40030400954001004075910704031418011410f500c03003102d0a006250303a003100003000c7e10038031400d850203801c01c1501034000e0070095601b82021842e0341c16811840180310308400320f5090321841004000d141c81c0000d0040300384803000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 570909559 1250 570908309 570908329
    0xf030106171501080c01111912110c090a09030c08131410140c010b0a0909020a0506190c0611030a0605030613050709020a02241e06030a320309 63
    0xb250040c03558004004654001840c41d0084409003091000303481c40005492614680321040310100840c0707807500090011b251803190b00203255650b1401411086070019540b900500c003829000039400c40060000c100f07aa1110300020320901d05109400303020780301c200840c1c00644003034011070100c040810481000560001d42100103075042480241e00c01c002802c15903164002c8180072100150322100b0000070341c00502114002461501c2050316880c2d100c1c02041d20305012400341c06103910100341464001d060741e0001d40008041c6a12002031281107030304156082e0215141e94035481071100540f01c00d0095449a00f035040b000900c02c1c541810146800d038054031034031191f100d00c80c0a00118102003003c200352030302c48502580e190401c500482c513228070089020580c0341d140344070329403c81c0d01d0380a05018101303200c40304035a10880982e8441822050781c00c1da61603480000120300103210040300200c40c01c2c1071031100d9800d98092091000c012801240c01e162600005030b289250329040510b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 570910809 1250 570909559 570909583
    0x40b03120c060106210f0e070605040f142b02090103050a020a05010e01171005030a0b090d03020906040603090c0506030108030a02010e070602060c0f0d020d1a0405070801140f03010617 81
    0x120b008000c3c100e8481c02107080b1411740c2d04e519110b00014803080280d07000b4500c2c107240107003141ca03030742c1d5a8040100b05030018041c15042050003200080e800c85030a00b000305481006003920301020000300551903000b03181014001c40e040031880c0c1c00c090703510f80c8021402140217901408846403603204119910100e0f030080750522400c14030850302644e200c00c0d000314036040740c0c03a40758a40e02c580085141a481c41e9200c5d42c5d1510800f01711000700004460014003c800c1d5408807000c0010f0b80009400b81e0041514460b0041c0c4248010020070303210f0f0700030702065030044801c20720040d01c0c1c402051407a8400d0f00030060030341c8005034256409509114080b007104884019156080c10141e0007516010f000d030843c10140804038854000340030050880f501006488003c5541c1d0900c0d4036071801400a8140d010f00381c020f2074644110390305142c02014070445960b61880110781c24502c07460300100940703450903040300c0c000702410b402d520244503030005010300e0010440110440032045141101c99022 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 570912059 1250 570910809 570910817
    0x12130305010b090421020c090c040617010644060a0501050304080f030601110a0f0b0a020a09091a0405010909170a080604020d0906180c1e090b040b03120c060106 71
    0x401c03000c20885035454810b8041500800d00f050550017041386081400300700b9030340c0010f00d42c042c013000c50140e100610403543c0d103031150b41340ca0110390804a6012002d10444002c103240c08141c0c5192418142c04200411200d001c000b00404401c0314404180c2c9401c10390000c1689503000e0100e40d10304981800028503003481e0540c594501030340c40d05200d00403500d822462042c08408503600d81e0003003100c0858040c01f0011903501c42094204140e0082a00900380c40c20021040445c04c00280d40c0219410b0341030780d449403810715140912580c000d003160f001c0001054a00f15041d09282d0311806810b000b4403204001003004030035070401d481051b03401e480003016100b0802c114405180c100300300303031b40c084c1d81128016142c09803c48a10090201f034200200804d2600610319030704a042c0020b010b220740600c8110ac10141c80e030a000385940c1c03c500380d5a840c020401c3c410444580301b6080741d44410b80240c0003191720019100420300c0e203400d4046018864002003000380c1110410801d641c010405464 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 570913309 1250 570912059 570912061
    0x130e1009051003020d11061c14010506210403120c0203030105040b0a080601031b091b0f081314030705060112031d06030f13121d040501050a0506070512130305010b09 73
    0x100007103c0e085200317402000d40d1804c01c0c10b00e80b2650f0304029155541c242a1350640042d071488041c0009203941907120013484c5807d000450350b030a000b0300341c0b0140c004002c07227011203000c034141c05c40300c0f500001c00032010007134080c203154009040c50003262407103902d0307800464a0b541804200405c0d40c0d081408540511382030781003008518070002c0c2d000d044030381103210f02d00e1402d0440700001007903001e500b0501c05103050a075040440e000900764411000d07850382c1c2d1010008101f82c6d0403600d41206941d003c04451100061001080700285000300c4c40e020b02084038035140039507035901e04000d02680702484980c840e100010600d030700f00c0164180340c41004105140030003000000b910500014200c1c8018000c0000010300c0304441d03841c260b038250b0f040b00458a2207031b02500c000b002c0008100385681500900525610700341070501030103040e00c0008001208050038001404400c1e0003400c000c0d01d291060802c608080c8070810700418803001d82c00a03801500707041d8241075096904441f5003c4c01805a48 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 570914559 1250 570913309 570913313
    0x4030c03080c0c030403030815120304150309020a080105090d0306080304060f0c17090109080c181f15031416270b0c160317130e1009051003 62
    0x448640501603041c2040c210320b8590410a0b40503000e1400c0c18600f5100008020090541141200d482014100068000c620402c4c06101d004501e03005010500c2d0f0040c002804403102c10400c510046280d8078000810b007c590b00018511011503100c41400d9555600384031200c0310130300c01f03039440312080c0c00d081c08074034500510244d0300e208910440d01040898084030768568404c0c009010310a0b0084990031404500503848030302688000e114502049134a01c0001d0000000305495200c1600206406000b140400b075000010a006144200a101003000074641d5401582024080d1076841c050842810611402508407004036121050398002c1400300080f07600394103155100c01d8103514094210107104041c000000490000c00342c14000c2d00d40f40803400c4c81d8150301500d00005101e045034650204450b64107144104e900005e01400040b4100303c1030044070b1002003100c403d0800008a80b55a1046203142124041d92100110000c16104102c050002e0198640048884c0e01e03594403a80380d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 570915809 1250 570914559 570914567
    0x703110f07031d030d09050a050f0d02100311030702010b01022a0f151b07050d030206012114010914490207080708010603020618130e070e0f0403 64
    0x61a0002e0401c41c01200400100400e407062454100021302241d280000d400000740280704c260148a0007540203400c002858508a1581d550301c00f170181204107910201d4080c00b0700076280e08040c00a0580310210806c2d40e6005200541c0b0901e03855000080840c0f50000090400503040380c01690b80200f0b1030741d524001140000d8500c011011078000f0b042c03090007804111440c0070105030761800c400101d490f8003040e418180340c80700880400203580c40355494108000c072402032882d01900590001c0014401564164010305046010250705001401c9981c0c2d0040035194144446403207944401d24003003008a4042c0d55170042e0040c40240820b01144a006180c020040003005241d10300b41c00e041c0325010550101248640e01003010708811560140042e50f50100351040150f0341c881c00f0740000742c401c010710842e030a03650f00500c0e143c68075076603444498003400b03c40011607003d00c0e040009803110b065445109421481034029040300c034a4180540260800140003051180c0d00008100000e41d06c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 570917059 1250 570915809 570915817
    0x2070b031501030203040203010f06230a0f151103190810140d03050408061303081005030703060e101505030c010306050904030503040c080a240e1209060f120703110f 73
    0x400c0c0f0b0010b80740d5680c1c1c000031340507102e190140c0070ba10385001d0b00401d02c2110f5040e155920001c40b149502100f01100501012072054805d04001d000c00b40c00a00c400c1800134154840c075602480c0c100460f15a09004500355840b01c4020b58132124524803065006405c059182e034070800140e0442c001030724049a9001001c40100018820140028101c003010b000fa0240d60261110b2000c48050b89449502c4800002c114032003a40464000d034001246451200302c2541901d50203006414540c0c80c56039154080c003102500000b050041028440c0e510b0090700c40c000d0010b00b0740da500d0b60314524210604d030a100d0002d628a04160134501d017801a43c446042c40c40d085585803030b01e5944d907540e5061042c108580d0790000c00c0300d8099540d509052161000b0908210500300c04081c00c460440711182040f1016150f106080741c02035045916207000b640003030a8400c4001d040c181ca80465482403c01c207030f00c031400781c03044d41c6002401d220416a0502c00c8082d010041c1d002c0c140342a050480340955401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 570918309 1250 570917059 570917101
    0x20c130507051608030108151005010c02010c0803090106031e03230f0f0910090602060f04030e06040803070506060904021e01030f090b071d101103070507030b0702070b03 75
    0x2446101040c256449002143c1c590b111880c041c4112494a180c4880c4a5000380b24030f680e58480c2d001414400c4255401060084c10107560140c1c065242c4401074442050101d000e070705003e11804000b000c6254400114417074035015000042c0c103404c520746000c4078107400005101c1e0380b02802c00c03440085c0d0004443c0901d14411440c1002e05034030380a13215124171800c0e201f0821100c0100d1944196800c09002e400b03281801c41e8007841001c200002146c0c402c0c8030307220741e1005902c170740040382e01d040038103610940040c082d18103203402540c8040400c641e41e00690008141d40c1c0001118018070100340f00582d0040c00c200c070700a5881c10b01d50005140c28004400581132043c0560400e000e40c0e0007039000e2240c0090650041c450340e403139414607440c0342a0440b201c0000c5200d11040c103034803141c514400a200030000f0008058241001d400b15410303010b20181108a00c4100f000201003142008000001c501c10031a021452a025070005d081c10003e0b40181d821010900500400c064003840c1f0703100e858 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 570919559 1250 570918309 570918311
    0x3140a110d09080f040b04030c0803030403090b0a0314090c04050c0a08010b0d02070203060106080406150b0d0e0703080d051603020a0203180d06090507080c03031602010c05031201080705040c020c13 87
    0x3503618146030f0503500c80c00a002800301c00010300040c0c02c05038440078000701c80c09040481c02444e0341c1d21074140c4030300c01164010001008000280601f5940c0b0028040c000c08034600002da0410b030030501c01189a0a4803128660340c440b010010392445d060140039440342c101c8211070b04120007204081d210841c18000c3e082c40b0301010540200e003da4030390607a4030968004040384c0f1296910000900006800d4a0a4800e541020448101c100a9182c180120351707038501c01034505a06c4200041c0203150308415036603079000360b08001001c1380120014120520017084001201d0a144444079003400104940c0d4043c903006220107043c054010042d642c200c02050424000780c0002d1002514031070340401c00404907454100d1640601400240c5201650040000c543d0700c0041c0108143d82c034000c2038002031406c68604221300065204003400e0031114031803000c03039080030004185900d010800360095181da5000c60400c010380d01e8280281443c2c0d4000340090000100e003c00410038540311010314011403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 570920809 1250 570919559 570919571
    0x43308040302100c0509040b0117070318080711010305090607051603110102191101092001020a051b0a0b03090604030f14040303091e0f140102011b03140a110d 70
    0x1c5402400350985200203803d0801890410403c06083c0e078002c8400e05002c1c0e0302e8900741c0406075014484909107404e0000b0a160243d448110440281400580c02461601c1d00250940020f034178002070014603100c5c0c0040c03040d44031004001003c41c2c100131304c01c65207039100340c0503c8003c0c2c2d0003800f00c0d20100310341d100323200b401c107024101170700d200010280340030b400d61002a80b00641c81005c80400036890555880401d913642d450320541c242e5000c2070020340a0007166000000700c8203a40b2840115100600541e40303209020340f102d40c18040080c848038038400e0300e0304d0403003094035083d120400505955003040d03085041c22064280d0f14100144005e080c80f1b01440000d1540b409042010f20030303110105000c1d034568407407030020425003a074450419003150308402c0143e10449151000280c2e01c0781e40c41c4000b014902000651103921005103581595070391666009403980b00106d05000c1030603070300e0104441201c0d0b651002980c800419142c002403500d052520b1809480049640155a140d008504 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 570922059 1250 570920809 570920813
    0x50612060328021e03030a11010906060b04290307051602030607050c1b10140403151e09050c011107050307060201051008190624060504330804 63
    0x140c00031912a86064000005042a803600c1c02c809030801e040c42520303054007082c060345200286822a4107000c1d45504244a0481c205209410b20f0310080c0041001040104850b02c1d2942103a265030842c1b01c0c2840e000900340002c42c18805607621442010002e140380044c40c001102450201170703c0b40082101c0001c420082500801542d01d403160003e0913102c5500381120050490f5200000b9640c0c0d50185050001499042d400400091803016140503a0820b06107011541d413008003866030000c43c0b043c4030101c042024071840000d011321105000417052a11b082120500d1840000c05200c1810203c09800041e404035416100030402e00b049440b00516001d424104102d42c0c01c03040c2c1510a416001030240d90540119018000300704851007655182c040070703911071485410040002900c0050b0000003811070703101440070320464429005c0720900420001404000744e03c8400054004901400380d01c07117035201d41c0d001c20082903203e05d000c07041990140c20100c02202d643c05004081b170000e02 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 570923309 1250 570922059 570922063
    0xe0306040f0f14100c0315050603040812012c1b0c150f100803041d0c160309030219050a26030406020124350f07090e06010506120603 59
    0xa030b520341c440d80d00e41c1004002120700f503403950764483c602e008504048096843d40d0080c404c40900d8034000360301d600d64034200700a101560780094000c640100302000600b9181202030000f0f4003a2802064205511400054809040d100300c20216010706415040c131110003c04040d090351803803c0030b080c540700c041c0840181e040c444012800150300c0e001c0c10410014441c100b40082c4203031096080714210070b4464264694034011405160080000c203a44011445201c101944e40820002c140b03d00d402c0140039900c89074200c001c021002300e00b8480d070500c2107240a100030441d6444060301500070324500000281c610a0301d10840c0b2207203618108002444040b028444d03861071880003283e580356910700d0024020004010075503600d8295500d61500b11344101d1464007100e5441c6071000256401d6000700d00722501c0c40d95216180d803000c0202003101d80d418070a004c031401d02c440207040250b14020945c0107441d2045961441743d0094001030240d6900c103000e131921030a03420807464865031400301080c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 570924559 1250 570923309 570923333
    0xc030506012f0706050705011a130f110a050d0c020c0112020c160e010612050705030109181b0609121e140a060203010302040c022a04022206020d0e0306040f 69
    0x194481c003600c400130610f90b4218000f451039034400d10003005505031400c842c00712040c90b05419540003000107450381c0580200d4115411401d5032070000903c07081e00120f46106548920100e4000c103001265a110440b52480703031401020035400a852841c04407400217000c11010079041e0305440d404a94000406030400c56614a4100134401280050711864411400482423059100141d140c031409502c109441c040d0a004a01c0c0e40c40e40b60442e42440e080d00090800490403460704c3d046150150003199000030121480171480200401c082d0811034020902440c6030852200c2e00400701c280c00010f820380800318180074094840e000b00203550700e8036910035020711040000c10310864003004d0901400703a0085049034400ca80801050205210a036110070311001044500c0599000c80403458071507420f12580058020001803401030401001000b444540c036040042d039201c0402849150b40401804180300c44a080107803056090900180c3d451000420040104110404141c2001840364440c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 570925809 1250 570924559 570924647
    0x1706010c11012a05071701090c03020d0f0f0803180703020d03050c070b280c02030d21020705011a0105040b1801050c01050708060109090b030c1c170d0c03050601 71
    0x2107401c0804504020307a407107005003e4900301b400d0120207a606004144140b0b88050303070006000b1801881c0d034007085890341070000700741d5032440044884c8001a04020b240410300d4421028140c803400c0c484510f4071074103010b03290b0301840e0f4400807081c00580c1d2145c0101c0141645480c00d03071382d201045c00145080005076484888405408a001141c0c0e0180080100e00e0b144918111106650320007002c54040213600030180d019000201142c032030b28070400d000c00c806c201d04842c0700c0b02d9040e0841d0090499004e2071051f03c0d182d640703504000c080302031005107400c4803400746405410700b42045241440361240c40845480e034a140001070302e00307034044e4050b9814025404000c0006150081001c1d1a07041c08032000c81c00110300d004003140b100b02d00c0c41035400d00d000c081d000300000c00b001c1c81840010440c0c44c0d405004012841e080c00d00089030006c00d15401c071070f8140c000ea26034504103240b1098649115107801850705000403c00166440200403039208030080081c9580303a080c00c1140c81d184410400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 570927059 1250 570925809 570925877
    0x61501030e0607031a0609010c06050408091e0f010c02030d0c0c03061d01050117070603090204141905130209131a09030a020705032107060213061706010c1101 70
    0x100300700c0d40e415500c8828016039846040380311007040305c1040924490000c8881c00b00e0035440d0106c0118020368001c2c1d6216209030482407410742c01000141d0300411071b81122000405003494109542001350a82c1e071034130802e00340110703400d526900081d00c0f5004400030004000041380d2510510010881c1c1100a5400030790400c0741c10703680181d0820030f40100302c02940d15802d040c000140703105080980c0240c000d080c0c0142c0070040c103003203003240a050f402500382d9100740c65190911340280e05135041401011084000036016010061107000c1d918001c1188100f03012000e80d4001685070f1903540c0e13920034019001180f43c61014030b012285101e0308008182d150855000708000308100000070407070507245408961400d5640c800f056a12900440c288800120a0286221003040c20300070b804e0b510b00c5018007504001c41a0820b601c500030300c0d84031070300003480c0d40b59400a0000300b05000d0740010080ca0881c01d914015190b405ca5200d5801020b810000142d10201c04603c102c2000301180302e030411 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 570928309 1250 570927059 570927061
    0x10f0b0d091703090d230d0f0f060501020d0e06030106110a0f0c0501120e0d0e15070516051c030e040e070e0103122c040f051014060408061501030e06 66
    0x10000c0c02d036082192209050321906990321490790044d01a20008a4810206000c0c51342c00c1c10700c01017a400c1240080e90300e940f5480101030301516401955400080c42600080d058a058002441d00750b8a4000301301b84081444d4070b601c40d444000449054400b039040c4012001c11001c841842d01d00d903113101411200110b01440c040040c10007640c030032910309070303100d0004000b100411400c848809001588990200054502c89405141a02140e1a0041401400329160101e180b0349911415003107070b840d080341d1029907070685d0703c049800c00341c4016500052207101d0000d41d4001d0380c0f169132003d4148824500100c4956a41d6008515203005580075503480d0366840b0b05a815401c5e082c00121191400b40b8241c40d1994403c120b264200300c1601561034821020b011442a2804010025a00152036040403100307240c15001c0d09000300781500e032005007140340821000542d18800f084030301c202020041001010360001c1d4030b507009038500614203c0c640da50001a03000780040d040c0d02d003150003018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 570929559 1250 570928309 570928343
    0x50d020c07031101020d021b1f0e041a0d02091b07050307050606030d081513020f0c07150e0603060d0f03020318090601080703090302010e070f05030f010203010f0b0d09 74
    0x4166401101d2158041c0364581c0f0b007400c0160f80340e1000310600c00040c1c4c0145050f59044120040e43c2900c0000504203810310602c216200001e90746600468020600c461408030716414a8480d0126503203082407500000100480001e501c3c0d2607250010f0711406007900851181c0c034111403a14081b00c8100c110980d42c0b40c10b8502180c07650880300d0140d9440c05001c0004075141800324540080d003030076555040c02d690350102829018400d2224071a00030010000d08404207e05100a0441c0c0c000345100e00d40780d01c3c011202c6c501e8608135400c03c1c3c01c00500405044000f81d00a0b88000289404540e425101d1351104003041e0640380c1d6500280042ca01c84552100381178021008210300c0b0810030141d100c40040409105501d1415507040c1d000458010024008522a91010f81c0d0a407180c4008107500020805891510f2180e811008180c0c000e080100100c4c50208031107110315450320001d500f550f240400000503d6560300c203e000c044400a100b00e503c50b09503000c090314542c001c0440c05110500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 570930809 1250 570929559 570929563
    0x30a0309030207050f06072a03060608061f09090f020d0b0106080f19020c030c06040b10060810091e050c030f090a0506310510050615070210050d020c 66
    0x40d550a0303000d0b0141c2800407030513042c91200188142800b034001c03840c0c01c3d2545c0e10380d051407040f481040c146c01c0304004103028107004182d40c400118003841c1c02284842c1080d80541c107081c0003030310040c1c0407902400300911040744807685000310350000d100007401005030300b8901c1000d40040402540440c149800f0b2003001401000ca5040c0c4003541d441c84042c0e46c0b14912000c215100b5240212070071400d0202c0da61b0541c468004264800c00c0606a9042610056516142c903009980880342c00074001c0c01c0040360708065680000500d03192503c14014200122950030f034a04d14002c00103810707141da80d911142c3d803070b1030900f00020048500810030f61801141d0000c0c40d400a0701e52122400083c00416000c410010b40c0346140e0b070b0020040e19054403607440d00a8586a15070014000050000601c641301081c52680c11000e0f0290b0041c124420b64281c4140449400a090314441c00b801d00660b03c0a030030250550b5061681617441d030100043d03814042d00c080c0078000140520304c1c0009103040c910180 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 570932059 1250 570930809 570930821
    0x22103040923011d0c07030905060703020604050609010b09040f060e07080a03021e0c041e0903080610020706140a03060b0c030702010e0609011b020a0503061303021504030801090c11030a03 83
    0x90348030301002c90341c0781d1011501c0f1409010308400b00c3c0a43c64042444484000020b02d4514480d0401d1441c85948001042035500844d000340c7c0960001c03400c010034800e0030301ca055032101290000300481091140010040e000140c0050601500f03142c1e00b00400c40d10760f021300d030441701076011640c003141e88401c0c25076604100d000c21001802941ca407840c000c0700c1c040b54011500c00810180c800c1c04545008e10006020030011424030000b0746900d2050014184180341485000c0e0383c40d40c000c4d00d440d40601200944280c240c1007158003030401003261030340c415031402106494010349a0382d8190b4080031800382c00316030002e032000040000c40320140c00b0f0000041c4131a610070b80b540b07601941c580080090074003503168014040350070003801005403c61918002480340c4002c09000c17060b82c890000c645003140484000384802001d10500040c19010010b10715035031400c0291904070301d01941c00804811041c8541c6228a440300c8541040601500c560380c14940803100301e90301c81c418801c005000d07100c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 570933309 1250 570932059 570932111
    0x60903070f0812070809011211040803130b070b0402060304030905041a21030301050d020406090203040b040203060a060605180423180106081c1412010504180221030409 74
    0x81203080c3c036503203e5502000d5a0702c46400030380781428040034000548944901500c0841884d5594207410740b800c0101c03000e0805040790030000c1d51a03401c810404210081076400c04c1303c0002c41840100c00240803840e5281e40513505644054490701c540c5030940d240903030b68201a501070f0400101450000c050010350308804401c59011844000d409202200307100c000c51011840c0e00100014010b50511030800c00c2d8031440a0720005215603203030400012030300159400c1322407150940510044d07142c100459a040058058104070072894504041c10b03500c998104088445000e000c420460b603116404160301d808200a105070210754a103001030b20f42c000710303001c450080d6222403001c4055014800c5809070785c2e03445d0003054480c24100e22000c800c001041c000e0b0820540880080b1407940042c0546032001e98000d200c242ea50404082209940c8490140d191400318500c200000d0382d20f1945c40300419070040709030000d04510744407890862040b608402613440c14050500340703010300b81d541110080d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 570934559 1250 570933309 570933313
    0x1404061d03032503090c030311030f0c07050103140f01061d10030e0607180b0c0708100606031415100201060506120109060b0301030503120a1b050d0b01110a060209060903070f08 78
    0x4030071040700313034112880c036039015010090760b400c2800000d0040340300502c0800213408032030a004000850800c40d0b40202c0280700340e07410a81c010081540c0500500312842d0725225030000d00d240c11011403c05d03540512502080100c483d12850340d0016207090b00e045000b0140c09140d01003000720000d030281c01020301425040c0310319000251164490300786070601810f04a01c0e851554601001981244c200d2843c0f151980615080010414420031201600550340c03203010595030b143c80360180448000940c40300c1c2a0162004208090f17042040103804458104c460710550102d001d0100c0c0103241c550050b6403c110005030003051040c041d1400c40c105d0325188000d0051545031281319042c1e000030320004000307503c140801d6103170540000c484c03640000414000a600000d5500c10185a164001c101000c01c0300061290b8074206140103a828080080c00c0c400050f00e01101d0782940d81281002c00341ca000d601080c2c0c0e40150780c41908868030034034000c1c00c980d0f1468440c50592904a21881194118 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 570935809 1250 570934559 570934621
    0x708031506030c090607081207120e281401060605250816260403200102070b220b0309190f030f050d0e0606131404061d0303 55
    0x2500d0103600b01ca10079010791039035505180b902800d000d200d4009200860702028103100f40083c20100b43c03800c910a00b42e907995040c460403251304400c225000c1c00c3c2e080c2c4a41e08040741000d0040c904080c80350036031081c80032401e4210380320f081c0315000c00075014184a495091040004a9030703072001c054002c4100b40080c00c03950302e002c01c545440e100300309035008000000521060790260b8480b001d26180e05d0164079102c036a106e0380c8240c06d1041d403401d200380b00c4070b4002007014824095524000031488000c0c000c4c14000c401d9500020b56100305501c01c2012032400010b03100700100c4000306401c2005e940c084d170410125101c010308000c40c1c00455000000c0e2140c0701e100800c07040c00f41e541d0980d00760040310200504035030340c400729941c141040307581d0107100080051509607091031250100c1440b09001400700c07800c00004012244400d81200c101450805006d41c482c0d1841c100319541041d404100010851141540b4010124400a0011303c5000c040708214040f0411000202d048c0208010032440d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 570937059 1250 570935809 570935851
    0x160e01080405100506270414010510091d1e06220b0709150206010302030d020c1302030603010b130c0f030218040f02270f01021c0804020a0b070803 65
    0x401441101e01420940c4a2007111440a1150780010b800c03100140c802c43c10301c095208a04c00358002e04c04c101c07031440e40000401051001c100d8a101d903861410000380101d0800c610101000e400a00600035401d540728403200c2c99607103035990074040700300c51010f03101c070204600710b13002d032100d110082c484060007403c0010300304014264403086403002d4490056150860380e1105011180010403030418001e081001041c60024004406220501a40100039540c1140f042c1401c0402c442400d41c15580075a501402c00d64450503846042d42d00c0705001070702e81d0f42c5c3d980001c3c0908580c1d02450f400a402c00c0720200000041d4000c3e500343c10080c0c456055000030040110100c0c0325407004d12680840004000b2301c14580ba40043d09500d68055000d41000440040c0c04940c01d00c0d0111000204400e4101403610704200340b61054400007400680203200030500c080c05441c04c00c10703600c002c10244800080441d601c42c503000001e03000355098651141c00e5883d280242c3c0d4420740381ca025003100c90b205580 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 570938309 1250 570937059 570937067
    0x12071b2108011527091a03070b070b270708010c1b021c06180203010501090c020a12110601140f0415090c0507051b090a1a0607021305160e01 62
    0x8100d440e541e41405050b442c3e41400c13905400c04201000710300b144040b182d810b501814804201800000c0c00c0020300c0c1e42c0c404400c40c020a01e60313003121300075040040c00700014400842910b80d04e60f00300320740201c00da90780126500800c150301c3c01042c40428a100788440f4100c0041c0040030f940c1c405d0002c005812154005407030181d010279004001e900c2c45100100182419440c11724240d0403049043c4103625142d45113020340e001c101c1468031a400e4ae8a010080d8502409040d0041845040402812010b003000a440707422003503014200c4e2103400c145c68416445406120710200307040381650301c2540c50300580d0100c00717120b0016a1123101d00e0400504180b03000c0c0314940801001c4184444580e24154814019140300301c8080c05021092003058041401404000340500346101c80b80000c02e07031502044030b000c10141041c041d292400c0c0700300d444c00c080600012032143c030468040e51200d030b40b0720020794468083c0c0c50680301740b070a0009002d07482e281d00c58005080d254941311000002d041c000116 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 570939559 1250 570938309 570938311
    0x4060816110307021e0301052505090d11010c05030708040e1510080a0b030f030307140708040b0d1b020c01110d0210020711030604050c0406090501030812071b2108 72
    0x754441d0420015140185811002c88840c103454603840302180d03442a0000e0308440b07084840b85401d400501c0405400c0f403021040203540f002c035062060400e41d000020449062078000c009000f6404954006002e81c0581d0002002179404800c03643c2c0c41c4000e05d007200300703504030f40310703c02822907a0004142c6110340111010f1340c00d1030203042006c0604164504580001020300300d040308076035840007401030b5281401100e1807280c3e40e90003181e9900381002c005013002c0154054051280f81800700000180300c8030216012079408000e01c41e1500620448000140140d00341114071900d85461a081c10b07801044402c09a2801d803110103d88406120068944a0302001800181c00a0140c0300c00c0308103d601074003184d0f0042450880781021440801e103020001d80b07095455034030403140002c5503d0280541c0002e030510341001c0c84594516614950b5a00074000b03001408100c0a000030105071045500c1c2c000300d0440d40b4030750341c146840d08040216502d002100c81100c3c0301201c0404038103006403001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 570940809 1250 570939559 570939587
    0xb04050c070f020f0310053705190204030b060a0e060109120c0f0807090b03070630061203020f01020a080103140a06050c0307030b150a0513080304060816 68
    0x80c9181c00c58503518001089001241240d11100d4003240b04c0c1c05440400030301c900c10f040041c0014183c1480ba0700c01202030005080307410004101101001401e250f07074401c00640b1004000420035444500e08402d0b50446401040c03411480800c1c00801c3c88413001c0442d00a0006a072034440c41e50700c6115910300d42d181201c855001c02ca10a0f0100580041c0b24103881c085400340401c02c85464660f42d400f461014641c0c4500c1c19035000c090240081130441c4103c91512000310000c14010b8601040500110b01c0412426514481203450054940740203c0340d00098030031140400030542c598140c4c40c0c001d40115400c1c3c0c014420b810340380b10b0b407140520880348540c2154846605680c070303503602e1840d03184253b003da250354081d26080314005640c5018581c00386404d03c1c40c2c59100e20300580300400f110742400c1d0441c40f81e070400391b40d1048400c2d000c00300e40090300281313021655080c804004140303c1c201680a001c2a200c0098001a425482110301d80582c3c004a004060710010060444550b83c4c40514 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 570942059 1250 570940809 570940831
    0x9050702061b0d091401050124020a03050a0203190801060306051c0221030a080105281e0e1303170c0301060e0a2402060c0a050f07030c02060d09060b0405 68
    0x1281d1080140c1c0094400a07003000d03c04200e118280e5214200008951030306507603070703440f0070060201c0701c8594000c66501c10050030010704900044002965a4a1a50080d0500c0800031300d0500c058402e00440300950050f880b10a141c1718070783e00060a86a0074032402d00002d21306000411903244c2110400521071024840000c0d140e01e9408005c060013104030542d0503204050f100d410500c00520180c114000d01d0f0300c40816940c500b00a00001840041d081d49a4945001e480041d41d00f261a40070191010710918600d40a00758490030040540c40e0420000e5401410070400194141e0000c85841d81c82561401d10000e50031803070500a201c241d0351028650070a10061042d20320071a809507400d04000c001c5584643d8a8448001d41912112541081c1c0400011198525010001160084035010010380303810b1388103600402c00d0003000c0c9210124240080c2c1c0e0410325100c0c68a40c2c004580040007140e079103000f03c03040e00c01440c1202044a40c0c0c0d04000e450004c5282601c10b0300d10034051221 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 570943309 1250 570942059 570942091
    0x30318020a0902250b0405370804090905030d0c0e090c0f0f0f031806070215040c0308032e0308030a18080c2802100521040c0905070206 60
    0x88203000380d005110030000d00d00a00c0301e03100b10044d003038510100150140d0754114203400d0500300541410150000c101e5119800b01e050001086041100c51036010312140c3c1d2040c003103842c80d060106108541c4001511410b20005c50244600800104900e410b001030070440c60030f08001c02e1f1000080203420907400149030001401030100c5500070b0921801c00802e040c50544822540ca40e02c0d0003a665040b4580e401008000d1001166660b1020b89400c95004201c54508014001e545a80c052a0b5591014110020400b00300c40c0c1d510941c06943d1103640a0707140e03e04071803040c0c807002181c0014401d806c10344c103a0b1041d210000c1a0141540d40082c1407a196548100c2c0c3c1a029004005081780289a40b18281010440060140508010440140c1040b144da0105180800c8541141c100907030b1180b11103038016500c00c16500307645515410191744074500c40003007005000d0b4891540115003540010042006594018072090700d410381810082e58503281001caa0790712044030120503540700c080c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 570944559 1250 570943309 570943319
    0x10020c0103051e1f031209050f0111032b0e1c0503071b03020a0c060f0905041407110a0c3507090b0a0518090c06071203050a1b0c030318020a 62
    0x6a800c414501301000c0008220741d8982c5c40c820524908106040003070a050300501c07140c68100e40b40101c552003440d01c441040b2840131819242d00c03030907038140b603403c0003404810f102401400ca40760450141c0c2400b0088010400002d41c1c5617918900c000021001112200721154000c4040d0707030260885981d40000449040348020904000820540075846100904000210040c401201504007640c0e1000b40801c16000a415a60707130380c02c8140f1031070512105106c2c080140c5001c40d44103826141c4a69040800e060b031a080a6044c1e6000d0b048018015010814081c041300c0c80e200c07080d0300202c0c4004040c2681580c411445901340700555500b10440411042c071243d001074452003c0182039202c0f00d66514000b03481d00030800002c030f80300c0f22000c0030000100803d20103881011001d4803100d2428125035900c820b5800c440c1c0d400130074599a44003150078a83c195015045051024030500c6203000048009082412000002c4000904050700c06d0f000342d09080c0c0c1c40701c4095010740302d4044c040c104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 570945809 1250 570944559 570944581
    0x50c0916211a03060105030109051504030c0212070e0f0610121b021e010207020105220e0702060a05011e0b0d0e06131103061e100510020c0103051e 65
    0x40d1441410080181d503000740701214034031501d441000e01041d86240c0480000070f1606210050340310701e20a900d801c0f00d0f8400328401144080d0443c45e2120580c1140e80d5629054507100c0e508034010790481c140720342501280c000041c04009440c80c12a28102c41d41d00c030000c522402c04110351803038024040150408034140100d0142c05680c415100104003444001a60440440d01c00c01d00c5c00184d1042d40d448616803518496034000490740c0009500e07150306900040c11f54820441d040000c00002100c44400000d51a443c4020b8841d50714446454240300000a6660380260303180315181d40b40800003c1c14540a010020f01c10074541c683d80c0c80f062601d60341014a41005c02d8000095494a2001190050500030940f044d03051a1074951000401e080080c0d480000030261170080d845841406071140f1180014400c91011025000250741d0750342001d402c4420a501c801e03001070b0340041c2180800c2d000b11342c02d448500281d0302001150345045200c000016002c034000d07500b1503141c01041c0a8046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 570947059 1250 570945809 570945827
    0x30b2a0d091518020109090204060f0f0207030803071d0901030201081302030106050306011e0e06091602010f060303271505130f030602030406060905040c05060a1416050c0916 77
    0x598422003010801c1c002c0400f0b0f9810540480e412005882e01034045680001c0e81c0c20203044524030450920341800c2e4090001031340c0c13480d4041030200b40341048000350301c00c20405001d903a109441d680c5a003804c03100a800c03083c560414120a109042003918a418241e0046041f01c0d0140e50301e40c01034403842c2403148000a4000c0903601552030700000f03e0140c800300500b500810200304449440c80c0b40c640702d10030000054010060a490700e01c103110b81a90340d40b140c00d4001030444070700c248600c20103805030b0041c003d03105a4030006081c03982c00014160000e28840644800c60051f0810800c0104004148041401000c603010b5032040781c540c0d081d01c140090401c04050041118805071200c24040440d8504c0d1b0045902d6030f0000108004c1100a024960050040f9541403101d400c05a80e2038000445502078907000b0300001c0380c0d60301c082e4030440042e00d240d01541e6805665002038481240e490081b00c406891910030b11200c1c106504042044500c03070045410340c00d440d0a003d0b4802c03508004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 570948309 1250 570947059 570947063
    0xb0d0b06040207021905031c090b031e0f0601030b1903110a0b0706090c30051009050a0b0f06090a0b010c14010e0d1e031113030b2a0d09 60
    0xe8240301110042c0c0707641d015117456441100000c980381d403420f0101454140841018591000c09062100f00e59410503410002c0e034116070b080540340e544008201200b881d4000140103036084a90603c8111070003a1074280c0079000030b9070180140c2400800784038000944541d001d0b0000003402003000880c400501518200c94020240360740345a40b17248408003504001d0082d5105555041084200304030580190000c00d0303002c10120721250801803444200b41d1855041d00d00b06001403405003000030600008820148241041002c04414100aa51800e110100302c1d850421840030a07c0003e441c05075034072542000b8920720300d581d51440440b000e0181028058140130840300c200c00001d5200707102e58220100c0d5000015451014000280340449440b240410f0000c00d510541c03c5c0941c1000c55208154a03003008903004502400c15540c511400c0c00d980b4004d85e28030000700030003640c2c0c03410340d028014104c601807000704445025408981e21910303036030004070b04000d0805c0d10200c0d500701c8242c00d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 570949559 1250 570948309 570948311
    0xc090408130303080a0b10050a0f0207030209130b0c0c0a02060a0203040b160b0f0f07051602090a020307020d05190804030e1f020709050903031503072d0501030b0d0b0604 75
    0xc14040d807007400001c950070480200f9850300401513412424464660180400c4818003408140d80710094028803e01c001d041c00c0054a01d03112200358020030851008580c00750201c1001d03d07082881d001c0c622182c0704200c9918802c88045003106014405682c01400d060020703200b8610980d080290507400000540103500090100051b20b92242026102ea1054010741c800b0700b50f00c0c1c0c40c04903c108402020310030a440c4070800e02c41030700e42d580759030760784240c3d942882d41c0e84820f803044000310a00e4810000394003e060100300304507030841d038000d18040d4000d40c080303c59030a2082010b6880d4040d80c40b441d19841d5000745c07044a01845070030300607046030007400d10140704d0000e00c0c0464040b028a5182c23441c0b003000380202c2c00780580d0420070030004001c0e0910401030350034101d4080380c9a10010b002c0d51003404030710356202002d03501808228000e00d0710940c0d4141c0401d035010382101c01c2402e21030030f5800c0343d007c800000b480c1d40070b4054200803040040c0040030258455955143c2c990002e07010503042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 570950809 1250 570949559 570949567
    0x10912180305010f020405010f110d050c0c0915010f111c1205040f110a0e0606070503040e070908160302030d11100e070e01060c0b040b04050a02090f06210c090408 72
    0xb040c0280301d480c022807100ca001580c2c8504203c00036005c010b01c0d00e0100c040054a02c0d81c180344c0d52010510714010701803460400e81d120046240540f8082c10300a002e64400d900c0014403150480c6035420b610074800c02e0701c804030400d600101c02d40300c156000b520304c1d856400030700c40401d021110511000001312141801412000302108060455004542c1113400300200d410300e10500c0609981c02c801c04070101d90303000141c0e00304443c0105815004e0445c50099502203071141c2000360900546000d0009002c65015034074240394002c1c0b142d040b038030483c0024000d8031038805035640d8103094001136030740290007043c17603408650045035102440420414030340142600d40d01c40e44105e00a40ca00c00c04810300901003181807030155010703440182e04c041c0500040807100e0300003c1001a150b03034030580080c0703040641c0d0342d0303130401604004d0031a000a40c803020075010050f0001305036500342d0241c94191040c0e680194000410351018151404540050b40581041412031800f8840554800c2c8540000c90078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 570952059 1250 570950809 570950813
    0x140115030203071218051b01020a1407080a03080f0c0a1e030618090308060d0c0e190f06080609060906060d1b080d12021801030b04090507081b030109121803 69
    0x84454800c40c18029540c803203005e00074031a04001c9031400ca040700c4620b5140103207400002c1c1d41c1d41c050250040000c8905440c0c00c14107202448118003c104010a43c0c0781d41e0011310b40205052412245a090146048042480317040804259000003001d601c0d8203695280c0ea080c02d444110a01100d64101500c80c1008590b401e0010701d18407040740460804100c2c1070705440d02400603035000b400e16000b803886010071b40c003058800c1221411a154100340002546036031018802010514020280841c201100e01c000144035a009004845540023558615180c140c28107481d0b0100360342980607a403040000c184070b8905640f6204c0840e2081000600f01227603800800300030005648469429048410704184441d00300b01c4560783c0d420885411890501401c4c0080c44c2c00480c0c84100303040690300c13a58181c40f62a903501c25034a05801508079803407150344a88840d650a0100008030188901045940090030140a00302d80c46034017101c44141205c00340800c4400b041d1004000150b0b40100c1030000c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 570953309 1250 570952059 570952061
    0x120a050708010e0f0a0213110c0d0c210905130207020306090606010f02030a05250503161b0b0906090619021c1103030a1a1002101401150302030712 65
    0x8020141c450001c610520105112070405a00701d136401c4951700036000c52401a61505000303020000079030703000503806045555242e0344d40100d900c40340480c440e05070046070721600151003006d55032250074044a02ca00c005c000e049140c1521228801040b042c030b405000e00d20f051003001380c3d0381015140c01410b082458002a00d072403020340308547c1c650016000d010031564001e600c04c40d040310fa400150f14001510400400074841c8080e60000c014198442c445c00800180382000b40c80d07041400c0fa0348545000002e6510340801c80703022150300300401448644c1c0113040e5024000c9070180c006490404080c4410307c90240c4c06104903d610150801a01d07480d01141150050b51480d50341c000c021200d68114100100d20241202e101800310400b0048801d40000044985c001c03a255004200c2400d4001c0182016915503080b580c407455070303100c1d0b03841d155000410240b0100d0030501804030a0080f00e01c0c20302d0796820301400d00b810b8850305210700031500980040da042151842c101e1148105040050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 570954559 1250 570953309 570953323
    0x18010b1302091f08040b04051c0528020c01050d0902120304030b0601030902100e0d0b09010b13091e1a0f160f09050f060c01050c04150f0e120a05 64
    0x1031030380468408803509282680050400d01c103c0c0e60040c0540c04100940f04004c0107000400d414918400501001018440c00c40c0000d001501e42503011000c003400380c400c1d00904250b441904154403070700114900a000851241d00c2c980203810450209401110581e0003511800c20b11f0ba1112000c4c8016168014042c0c4600382caa806141c540c4c6c154548500b86050103170180e4101818440300f0405039460309601980182c03a4280000b0340e44d03000c3c012604c00200d02d44040d20f03401000040100b210019001080995401c542240c109803204c0001022140341440162054003d6088540705401000041c2d41d594000c515a2122081c0b680c0200801c0340111503021b090307400c1c2c00c240010343c0090010484c452441e41408241c00f815124010150344441c41141e10903400240304517181d031a058219404100240000d000310310701800d203600c40794082d110301c010010483c03010800c081d04c510504003000751243c7d9080171740380c0b00c0720400c8410400c0c06440500ea00a1002140001c1c0d001c0110f1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 570955809 1250 570954559 570954589
    0x30c05160602070219050f060c1c121d060103030320070f020109060503040f020f15070c0302030c010207060212030a060801050f0403030e07060c0f1103060103030203040e01140918010b 81
    0xd82d0754140c61040c02a008101c0d01e24903ca0f401d0000144642d0381c41e581c82942031102520b2040c0c031400d694840310b107044082b8102c0841500b00349400c0c1340c8250300c25081c03916421a41c00a000070b111000c2903845400c0031516500168002100502c0007074030035080f00024511080b81d0034420201000410600d5200e600125030700348010307c1030021960480c0da500c006013660f040c49400c41c50a0344840724080349100d0000c0c0314101040a0181d50795070050f4501903500c6400c505a16001c580c6007290b800401408164805d21401000c00c0703466200040d10819245198087c0c25034110342400d0070700c150405060321081503100d0801164a506c03d1241c80d106503910400303200e190401d41006821181d1004400100d5080990144500c940110700b001110340c0c40302030f061582c9541d052115125281c1902e8542c54000d010001003410780c0000a0800d603400520b007420325981c1d80720401c0080f2010b50301c0c0d0380c00013413140008841001c0c410301d007483e800c40e0030000714106500500099030301000881d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 570957059 1250 570955809 570955811
    0x60a03090803010612050f061e040f0f050612030a021911042405063a0e07060210050402150a03150f06090b03011215020409050c070b090606060406030c051606 70
    0x900d0b00a810180143c43d00b00000005048070740c1040c03404240e83c1c03d1580d071027000c04000d12103030800c84c0e2200c0c3c0c05003091407018602080019920311002e0b02070602510740c4d81c42000035102120b54450040129403032101e003900100418003c0b00728440030491300b01d5003580c0d482d800c00c1810700c3da600c3d01d0080522034241324440090030380300001c0d011911242ca41240740109018032108400d81c00f50007a08000581480240c1c03500910200c107922111a9422801c54103402c00b03043e8800f0220002d01c05056032110340968540f42600700803482110400c9130041c4d440490100e40a02c1d000101000341803002440c50041110000d2013002141102c6a9121022000c8bd25100f0400982d1040e4090040c10407808064919403400846039505600d1075809002c0c3c41e0f0000c00b040981050340d04882c028001050184150b1a00d0380d03059141d500549800d03a268030b18900010303848000424054400c1000420540c20141801001c40040402c0b440707800c1403040410242c03c55070108148040443e2150303030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 570958309 1250 570957059 570957077
    0x50111030f0f06062a030a020303040b18030d050903071b14041b03050603030d0e011a042009011107260f0a06020d140f0f1302060702060a030908030106 67
    0x12144400001c000c254500b5040804240700040e500d88081341c403045042d01c02060708412010031007101055182c04200c4610000420140d419008006184200d000c2e003485503031a83da080040702d201d2640071040c41160420080020841040c0e4042030f00908044202d0f810010a5940c000d600752101c09111103042d00c1c10010400041040000c65402c0c000b524103104101c000008803100400c0c0711549410704d900c4500180090300d080080c0c5084c00901c003030601c41418001c0c599070090011041c0c00c0740320340c4c070440c0a00c4c483c03e050040d0390000d00c84034544a00040c04100c1c00c84541c00c83c010b0b1074100f094180681c02c1c46001002098040c04c44002d030400000700c05046000c02c8106000503180c1600010280d5015040220302c0303a80301a00402c016079a017400c03522547c000d09001000710700829403174080c81482c400c02010076208624a11001060b41c9983c002c0f002c5e03074041c220000b540003001708860310040c100500682a0b6044600b004a40c072001e41c0d0b1144010b070402d0704a03000281e0610 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 570959559 1250 570958309 570958321
    0x1305041e0507020c030606040c050c060a050105010810051018120c08100e07060c030302120112020a140f010c02030a1e05060106031a240a0306080f070e011a0705011103 74
    0x100c10719420440d0360004046202950010903210800107201e24442d40d82ea640c0390051a000701c0480e41c4500c51101914190700d4141d482100818081c060b241c005104500043d0741c60440110b1042034960090504100c0291070070201d82011004640c3d441078003510030002011420f0541880c4500c2c8141100a030881c1092107251408003c00c5140c48198140f410030781141e94086000c00940d13659160508900a19042c1500640314081a10b40414407a400000781003440711501480c00b442101d19403641d41ea180d140d81348000c240d29440d903004051100d00e10340356000781d00829809202809513480d10b900742e101d980d1182400821250035099803820034003084801c2c4121400361071039007001c0001e00f1502d01d498000c005803644c124002c260b4100368010a80e40c04203581c0058110038140c545c0c500d44080001c001e0082071003050135510079185200e600c84804599242610460b20308442180c1ca0301c21001d40840700d0b10f01005406004000340c1010840a014a441940d0400707801c0390343c2d003041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 570960809 1250 570959559 570959561
    0xa09020a1413050112020d0501391107140a03060203041a010b040303021207020f0d03020f070602030309060604110706110403120302030f0412090806130605060d030f051305041e 78
    0x5140303610542c030301c0c100040c00b02d01401000c2e100381c2501070b5a119800d00c81c901d440c5004041d0b42489194400c0c41540c40480545003100258000c0b0842848240d001c10b03040081e01c8a000c00d5180f141c039900111000d000c0340c030360110b0800084e00f005010703842d0241c1e29200d80d0700300d85c0103a505440c0ca80c0313143c0d20f040882d00c0301c1142a0061001d181e04915151843c0c030003c1d1203460700012084101c2c40040c44009552380e510010b0000d460041c080080c050007858080d5585103818504080303409039450009038140003000345c900c0f035010320003e40002d0740d0700b81c10400101801e006020544074144002d4000c0342c01d920408050480130300380103540341e041d414002400000c0b5203040c0b08144c01003040086000307400700400e0b00164402264070402c242010181d0790080d280c1c01400d0b80e4480caa0030042011100310303120215500859040045445240911040c0c1e0f99201e0083c01096581c1902140148210000c00c1c0e00ca5010006001441d154030004081d9070092180001c1c509111820090050342 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 570962059 1250 570960809 570960829
    0xd0305090313060c080d02210907030308040b070203070804080c0109050405010803070209060604081f0c2f030d090303090203010e031303060b060c0627070612050a09020a14 76
    0x800d00860400c045404054002500c0740602c80802c50305841d48800c01c00c0c104140ea6004051070401e42d10380f692855441045100803c1b00800f004091011030305010022a00340246da80565030300700030343d8032a11440b104e103034003a020104600c400c1041c1008600307420041c00151110001914501e14020001080900543c009502c00d510340f000400205070000304580003942e058541c0d0f9026514a00080c8980c001e0354081d860354010100c00c1c1c0c2c00340226000903071311202c08050400051600030411640c0a403101e80d65100c41000700f000340030342510f201e071236802c6600b0481141c1c42c05a52a604605a45040004501090316444003000310320f03080c0560460782d00c5680007103080106022911114101501c0040c021f07560311442502c041e21001c0480d4100b80d1140200c48090520003030100c200503404040000000103200740c0240d500d030119460044030510341e0f6000c184c60364161454010200500740f540056900c07080040141c98002c052401425001086140c040c6d42d241401004a8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 570963309 1250 570962059 570962071
    0xc120f1b06010315140a0f0b060f07150c080f091912030f0b0f0103020904060b0a0e030706020c1815030607090f06020c0303070b060114040b0307110c130c02120c0d0305 74
    0x420207104050040052045c164040019000803a10103103446100000303101c81c264094102c28001020384a400c481d50081a013035201e09032144140564601c1401240d040400d0480010700703d81c046902002c2455030785400000e04404d0314041ca800c50850600220a110304a801202c02c03203102024076010701c100d03600b515507003105200882c00d0000040c0000d204504090501d80d0224141c40c0c50b48469100c4400323086042c003125920072416001401c44680c0300d0350544a4800c20310049030345407010442403400729005c0d103980c04c008006541600d044400800c50500e03c01108440714656804020f00c40c0034005903110302c20074034200748044c40b4481032a0098015503018220210700390310000100e5903800e421020340700b1141c54610048907004000100e4528181020902040034151b803402180030b00910344617808030010703081c440c946410101102590092181c10038100402040c0c0100d03104044a03c1a140350031074030315024806030085000b0b803944e40d02000326400e02641501c80c07650081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 570964559 1250 570963309 570963311
    0x304050a030e040b09160504170f010b1005070828080612070e062b060b03010507080103080d0515040f050405120415140f07050a02150c120f1b06010315 67
    0x140201e01044203c00c006c0c00103c00421924005040b01c0c5c80340d030542e8080d10001d505840341000e600d14243e07a0361707602240c0b0a44e9500c3c1100d1241c06140400017040a415561140ca041c041103031a0328810340c200208070390b903020303055544854403080e906190b112007019444960050a0071401d00a03000751240340c148071940241020b00c0941c5030481055881346040724500c0d002401c1e652071a441115888101030000700442010040042d250006c04013010203900811981c0d507026801c45d100c110a120281400c14200181000141a80c0140d54411204162900c28100c224013103001c81e03110012550113690381d0410300040040030300c4810311800701e5801082c2030a00340035080d805100300030000d9060000d0710b03007854503e00030241580c803240100019141c072503041f0f00740325071900c900c140202e1151020500e0030402106c143d00b0740c0c1070701c100e40c3d004100c0c902c440e0600c40d280303038030180091050780700030f000705000da035010b0203448120400040a4111035256240224055000c148064036803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 570965809 1250 570964559 570964571
    0x906270507170603031204030203030103060e03161511040f0305060901020403240b060d0e1507090501030b01021018120507020f270109150b0405130b150304050a030e04 74
    0x40c940c0019141069030a000c1d01d40c2d0140c8070000020f180d44601080210300a04a20030041890340100185040302d000d010140588003212840e15201d04c54480303c10840e09070840712401282508400414003840e91030700040e10a126820b107034032501700d5406085000b004c0b55052040001c14000c06070803042e01802541800d04680d0b5103400c0c110b0860899019680e0011036032a115490f80042c0744005000e00340e01c3d5255000035040700500301d449100e0140d03129030f0341c00d440010610600944031354680d684042039113043c0001100906801190541144501c1c2c1500103002124414001d1038a013000014019015a240460b01c45081382854400d20100307001301e00160300c4060324a101d05000315403100056181610b4255202c40443c0b180300c61419800000c14003440603802410694150284840200d40d1030b410a91148218010b054201d06680d080380d01405444e080b22130011401804103c50300b0403030701441003036041224103842e154031400e14a001e060704080d4851035035905440c18018 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 570967059 1250 570965809 570965821
    0xf071106160f020a05030d020c030418090b150f121609090311160302153606131701110a020715080c0a11120414030c0303070c061809062705 62
    0x1d900a40b01a00038036500095a0501c49d6030030300466000d800e01104280b500710f120f41c82d0f02c00a00d1220070480b040413850b000303d0740c81001160300c03001c0c404000700b80b14071064551081c0890303c03a4074049900305101e1480c2e0302c0809500c4204890113041f01d0000020104150308000708100c01c462040c0c40140c0107807084510b404c410300428800e80b070701030f10302031480450320015181a10070800607202110601440f2050001c00400300b43e03103200c40200c0c1c551078030410010083c0510441090000341c004003181000b200e01e20301803d00e040205500002410f000404032240d41c0e520030040d620061b00190b60030b0102c0f40d0807400d240646551032804907150300e8810381e14072451288104020078480440101190100104941d010001002a10700e80310381c2d8801d6040c1040e400c0b11441c902c280170301c4a4101c01428004180c0e40f01d1034210761200c0440341f62200a860880044245240a81415002007600915400b8400050105505460f04298525050204107000c0c807110209035050009200b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 570968309 1250 570967059 570967063
    0x1805010609110417030409020a18080705100c020d02090c03090106140105070803040203210904050108060c041502070b040b090306180616090f090605011805090f071106160f020a05 79
    0x144c2e22044050014503141c0b883c00f9186029981c0301040e0940009096400c2c03641c45803985070a020301d1440c40043d035854100b0b0640b60900c0e80622600306111a0070b040e41180f10ba18840071250002c2c11023008080c494011501c40c1c00c040301c81c580c0c481000400c0c4410395a091040c00c00034004811030902242c00d401c0001c006104034040600581004404141590f8040c4a9075419100100507510f1040f00950154200d4215010162090b89044000640300c2004140c40d031041450001c098a024205100d0341e0000e50f00d500c104007140b01d5240e0100308401000c00400c05040b01d1408140c9a5007020205880d0100c01800c8103410010f107280352841c4c82c00041c90f550040022708030b40743e01140c81c92003160107403500c1c2e1000758081040c050018a070080390b40140191003082c0e85509100d07009a540d02d44a003400d1241a40000700340340042e2082c201e6140c2550400d000d0320b40000b841000042442c600801902d00082200c54024803401d115000441c07480404528005000641203a0715126 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 570969559 1250 570968309 570968317
    0xa0914150f0705160303061802031506030c1204060f0b03030901080a02031321031401031709120d0e0f011814010e09070c20031905030d180501060911 66
    0x4a0360308100703000c42c403007500407429101e500c8810340300042d644180d0b06005002d00b1051150300541c49120700707100000110380c0216072248169550300c1c845110103000344456a4002016031745030740f405204e0754007450080110b50380158054480412850307100f007076050480b100c424560303100364820010f40901c1d90704a01e041c0c0d8800b0b0404001a01c0f9500c66240000d01d2603c6d0000801081b041d010020302c031504001503050490305035404000005d40170460b40d00f0480d0a0001424031003001480141034440c020041104a10103008241c070781d0000602c65281594184003000071030306c030044541550504454000c061602481e190f2594100102038124a00042c024020710404600c1d41d401140d026880e81904280040c3c110702c5e552500f1a0000c0100d50054021074000d0600380702c540e40805480c44003103c8100080103000304135254031000006110300c030710841d12400213100d411801c81d19841216404070019801d00514103d61400301c0c2103407101d0304004180d0740740c81442c074402e4007030800751 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 570970809 1250 570969559 570969571
    0x9130b130c0e010f0e0303070c030b0c0406050f03060402091e09060102160302011d19060f0504060503060d0c170703050111040e16030906060b0703110706050d02070f0206030a091415 80
    0x4112020301381d000864082406003905a050b200011b036860401500074060307030459000d504400203c0d15603001d0040380d889a4440d107000140c0500c00c032059400b940005580081c40144014985150800803c442c4036044140c060a04683d84110485d401c2c500c900c0c55020030f00b440070313000120a640344007880a45600010f0304008a000701c0407480440c204211160403002000402c0400d032101e4804030441040c00b40600180d401c1d18000c0140f0302400c169030035116070341c5683c8d003540e50b1201400040015410140d4608003000f000003440b20b00056481c0c40e02001d400075005880c2142829401d449452111034503d1904001c10408803003544441600010301a13064002d1410704402140a019030600c040c10f01c80c9003800016400750030344000c00303540e0720984410048145050800e47c40380d0141c85010045603040120f9030030741110358024107000d07100d010406203024450300880c00c141c0085a01003c416640e90242c418002d00310ba032081018841001051072403080e01040101c5030000d028 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 570972059 1250 570970809 570970817
    0x10180311121f110f03040b0702071508180a1211070e06030c0609030f0129011e0e0a09020708030106081f14360109110f0a030209130b130c0e01 63
    0x1d8440e0003c281c0b030031074003800112540151241040d081680031060240e807240b002d88100840000d032900810000c8072000e9403070702c5000362507996464003500010b1081200425002c2c98003000002820444103a0340c09500d9910350140c1003805402c02c3c58042150800b0020f03d140d0000c202c401d90703001526001062040e20306075100d40720403010a140c000d00d0b400130403055080282c90444070030a200b4150036020003a0f80711040302880c4005403180c1441e0303461508081c40320441c40e10214061a4a050004000f03042000702c80da5901a00c400c98000c0c110842d0308080c000010840140c0c00742900b50030042c80708052000503004000c04242c02e240388107007030f401c20400f03542004a81e07581a401e80c1e04400c8203040c0d480e036540c41002850a02840414540d452102000070551b0803161060041c10404030082920b00144004480241d1f0048214641015020800c1d59191344615114595550060102185403192841000100b02c040090003440b03501d00018250016403150360720910000a0034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 570973309 1250 570972059 570972071
    0xa11180307050a0306051e07020a0605250503160e1c2d030f08060a0302091312122012090709020a050c0c03060c04030210180311121f 59
    0x80460300300344060307128079400442c0300400000d10150750403c3e84248844181004010300038607010008020541c0c8030401030748020031410029409920460b001041014064070000c900414050020422000c40c80064000b02c280200050801c250381d4a80400c0d040104c0f4410120004c1400c480109420b13070f0907114400ca9440c10b012207011585e407410b020703052146101c40003d100c8100d00c20116403c80004440c2a2041c203450310a00c0220301900300248031f0b1070002d00d50707020011500e0010300b0100b2400200010392000541ea10000300011a80e5180d032403400500c11036010445903c40d100203403004052442415a400e0381045071390f40400000c4042c443d0301c455070071724580605a040301700580e10016040801680240140804c80c80700300c04c0324034425000d000e05031502010356500085020510007803005103807441445085020514010003071110000c10140a0f0250740e2040c0c0e0250041c1904c000d10341008a82c1010928601b0002d00701e8000c644108000c603852086050f94540c0d03614 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 570974559 1250 570973309 570973357
    0x210206190207020a0b070312050f070f120e2b0e010309030203070506090c0f0303070206030a02090619260f22020d0c0510080f13060e030309150a11 65
    0x507040d141800c0d00a400404035039140c081c3c443c65a030043c401600810540d00b0868155071160284a1180ca18402e00c005a6101ca18040c1c0712840304444201c1441658002504003a003c1c0c410021481090b0000f440c5020803071b0b1000f040005481000f801c100c2102c1c2d050540c80fa007001807000b01d481e080c41e00041883d80c0742022400c5024814005008d406074906000c0300c8840010707000c0704804101d03003110710034481c0c1c002c26a0b030b8454284002d40000050002501498aa5001e8506810050710b501c0c50701e4042c0c1c822581c400303003070407160011070b00c8030000f90b405802481c1d00d0840d13064500490880e81c14032001ca8001c203000281901d51f13016640702c182c6003510280001841003580900b9201d00c8140c2d515114191441030b010ba41c2c001c0c451540c0415600d407003040e046004a901d9a682085510748150018500a860009071000c54440c2104004080104021351040080c200038040c169104407091036515805050f01040c2c504003800302c401040f00c2022640710220580260f00415040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 570975809 1250 570974559 570974561
    0x60c02010c0501050a0c0e030712020607110a032d03211506050702130b01140c1501080114062b05010b040c020f070f030b150a0503010c0c21020619 65
    0x7024020031a5003840d0074072003540160781005400340d07060b40320301c00907001c0e80e81410b5960503140700b102c40e2500740448800c00f40c1010340041001500901c26404080003082c0403407410300710b907842210f1003c1030800d05c881a1070300294401c400d40341540103402001e041d44005103082165100d01140f14a103031800d90301c0000365444100d544103000c0d11b00064554844000c3d00d90740003800d041e0300500d80240c660b20403841d24071800200d000d051b160000803208041d800140380d000380c42400090301c18035880c0311548070740c90a118000c0003003038004941007114080200d00404003901d4540225460740e00721000303030f001401c48020070902d61071140301c83d007141c00e11074007402422990640081ca0070001c02c00d1a580450080c50040780740d02281c4503140c1d80c007007040000445210152803e04840007246e4940d01d00031008114090003442942c03010307103450029007101c00009003000415098a268400c000724014403d2201c50815148901564811000f075161007000704054502640f124040c003114841e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 570977059 1250 570975809 570975827
    0x606040b190c151d060115080403030b130b01030b22090201021c050a08070f0f031d120c0d020a02030a0609050a0c0801050a05010905040312020a02030919030b01050303030c04060c0201 81
    0x10360180c03c10200540003030003840010452120070301350f03800c0b40712032080005446040b02c81683d400d0325003d080c010304450820780039204a01701911440b89965950711900410040801a400001c89031440c00003d001c580320b04031618040c0055800c0e00102c1030744000e88030b81c1d10581560100d404100c910040341080c0408201100c04807025441072526588040500310904103511610301c50b40f500c400175906042d00e1501400011903900d0020202e52080d00007100e180310744003200420414620034913090124004174812540780100e07112035012820880002420401e002074000c01e0f2441d0040b9460701d03c91003003d0225910b6a40c0c2d20f08002c400c0240300c0e09950401c0180c0c0045031203c51290182005866007c11681480c001140c00030f0031707205860040342c0c15102c0503600648880440e0107074001c41c120000394041801421900e88842d2070715074010442440141c2c1040c21441c04168041040e0420781c0070350300c28403c20070b02c080301100701c5054610900b40400c103d8450f200403110000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 570978309 1250 570977059 570977063
    0x60f110111030703050606070c030f08070803070206060112090206031f0509010b1908091015050d1506090c052203080a081008060c071103030706140108060606040b190c 74
    0x21800c81c0607014892607201840c00b4a2003a6000e100503142d00c07040200754024030760060249004a0410000a022100950f030845d21400d41942050380a03214000c0580044a50034056040300013003007825a442001000c407510f0851b0204a00d2540350040b4805000050000d040d000ea9a29400c00d003440d032a42c0b09006000c000c00e54a000e603100d01c40a8101c0d041164030b40a106489611201000d0040781e0161181d11444000d0401740400c1c00090064500c400440c01802100d04001c6401e8440e241300392441c1d80a0210079800d103803110305400c21110203a202483c240e107880b00c0022070b16409000c80f5190950b43c0034500160300c084601624034a002d5000401c1d20360002a1803045035001007415100380b030342c5103118202c3ca582d0300749036483e10001c40744d0095200b01004000b0004811801c1b0003282d9402900b00d03403c007080396941104407105285003800701c100d284010040d40e0402c1060662284050b200359003464602890b5580500602c401528008120303905101181d109983c00001c4c15 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 570979559 1250 570978309 570978311
    0xc0909020c1608030d110a0c02060a11070f05090903040501050702280f051c03050d0e0a0c080307140111040605030406150b03010f0b0c060609040f0f050c042301060f1101 75
    0xb542e508016541ca511141407003102500b809030940760180540700352640f00540e030302c2d0a500320025a081103410740c0405080020300106800c841c041d400c0c10001e4101824038101d60b0041507050000304a0541801081e001c05503004000510150340e2040c1901c294a41c180c0300f060b0882d0950004031800303044000410300b0401d40392000030303119500c4190712088407030640b0811810f42e4040b050104a650341000900803440801620300c40944541c46550046100700546050300602c2e40c0c1c3c001102c0ca80d038004c40d070380d6002103080402e11125081c41118028104001c001c03004041031642c00714040c51180e081442000310024092001a410000f20f8402c6000a8110151034070007150b0950420300607004140c200d61000f00b80d450a000840b042d020b800f100420b02071707403071008000701c5d00c1005004950300c015007070019000401c040889050b0602c1813001d0003180d00404203100c00c03194280380a20141102d440408003207560120410706444040c6445121b0b40c00d0150b09a40c00020190200d801d5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 570980809 1250 570979559 570979603
    0x10507060c020c010e0102010203100e27030c010b120619020f030702070602060601210b0a0503030a0503073b0a050d0606030c060c0c0e090c0d060e0f010c0909020c 72
    0x2907003c00c0010324110240c0701c6040741540302004a00b00d00007241d034071031200440041442404801d2100b907600414880b05070503e80d403040b006081c420681446140d9a51010800c6640c050085c06034151046054541d182c494182045595482c003010300800d030214051079220403420308a0f01121410300305034006a40e241000b1600968901c00c80c49404014041d500c013080c1e26601c150b01990520510300079a6290396007000180009106500e20305a0140c12001d0000301030302e052014025940690320703071603103a24240502804a09541c03818040c01980c0848200c10380c44c0f6925603103009045091003505101588000c1001012035801980e40807000701e410104100d01741d04050181c03445083e814089655452003580c4044150f0801800c4500341881800501c0c1c20389811030f0702a0600084814403840c2102042c2c8410103410b040e41d0071034448d411006001d5003007000040140da103074020445080300980c01007400c003450050460b11a00000c0442070b03460b007004841908842c11003031902c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 570982059 1250 570980809 570980831
    0xc02120609070605040510110f0601120506010603050c0f030703140901020703180621020d06030c0918080d0c0c06020c0706110a020a211a1b03150d0201050706 70
    0x80c0301012a032069140c420b03401c01003101032060741600d00f113500140c10400004901c000550b02c6c02070760305043e009446512110322800700104240c42c000d086005008000500c01c1c2016030034a04160031400030325050005021142298004803010742d0b03101c5d000580c90f078403409130490252100480310304011f40001d05022180f0410342c000c1000b103200f520342d42d00085541010780e11703ea40e50710800e400702d1b10040064010300b42c0d801000c3d42c0e01c00c1003500140b40600f007960101c101c450300d401c00d9425860b0340d4000e12000c0d0072441480703022000b0f04981c0e081c0300c5560380e80f20864480d000000c0c000c151102664650729016806015a19034000015526172200c0317001c003035550190388201c0c0700042c021b40c03039500c2c5c2035004101d1800c01600680002640c9007016044a4a04070400340714030f6154286840c00b000c10000907020720f070141d01d00300c49045800c1c44001041202207421966007001403c2042c09a00320030815596003142040d5924503140b021400160341c0d5008100024000a08000d4007601d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 570983309 1250 570982059 570982063
    0x1090209030f0a02130509071a090406060c11060a051204060506010f0c0308010608060a030807050d200c0909190c1d040b0f0408091c0b06060705060403030c0c0212 72
    0x280529040e0220380003129554820307592980399081c080d40103170a091601205803056006164080c00075400c840001d40c1d911440810701c1038402c8800540e50000c540041e1520381030282c0c50040c10585807042d02e40d00c08d0f803030f00714040003030b9000644103c0c000109807004038016001d681c6040b001100105003440c260420b140540022500300f400181a03940e03041000e40075056202d90356070180ea40d041d040c1e007020350683d40b500c005415142e005031090310020003e002d000c01440c0d005d01c184081d001c03038031510b4030143c910101c200b48078007811615050090409000908985182030441e00031640380c442c240d010b03040403401280500c152000561090500100d2003182080316240500d0665840b1302d0f903080b1711943c405490040001c212540450002002e445180340c00034010b02a041c90310444000049440880e040300700348810400c19000d082c890110701c090760054003500c03c613144c810a961002c0c0c443c03c00920080900da9601111452180705d048080c030440c1e806040d610054408107003181e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 570984559 1250 570983309 570983317
    0xf01210504051c0f0e030118050d08090708190f0204020f040e01050108130f030216090608011a060a081009020414041a0f061b01020406050c0f15010612020c06010902 73
    0x56800d100300d01001d180c0302030f0007068110710b25003035950242903c1007280846035a840a001107916640b07880369140180384800c2605500c0f84140d00031300c4540300c125806080705000410030401034000302d604014800b800301c1d80e500c4208540300540048002494039821420814401175005840458058448240c80000b00305890506096000030303a41e60f00116440e032011904040701410302d610040000d11003810804255200303005685c1108030200840301c080003150b00c5200100d84031941000030b00802e11a401c1d1000d08119041900d00340c12000c103065114004484041001201c00541c103641d07111540406030034503030810741d03a580ea960322000140110043c1103110728500105840d80c0d141d4600d01c80d0b10120087d091014800001e000c02107241c1007800c1080014940c0d03c050400c500c421b02c0140091301d11501c4007900c0325003400c1c03450f180070216000c1e00c2041d48486d120f405078281c0f5554803811507900d49030480c80400c1290058019000f184922021482918004141403a40750090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 570985809 1250 570984559 570984563
    0x14010c050403150c0c08090607060515331e0408061605070203070306050606070803040501060816030503040515120f011a070f0605180f16090501140f01210504 70
    0x4802010594006004403a03d18081c2c0c008241720803000000525040042e000c9441d006080c80e05059a40d100c11050b00e500315404a44c1c5500d0f041480e440e031400711480307500d9002c4a004446010710748140300c905c07048c1c0d20b085c40c080c60b07001003000e503c8801c8410011b5600007180ca110358945941303041940d600c58090b200c440c10b4441750f42c0c1110fa010322030401d40f90001e030001c0080181625507100d0400400003d03190340d410410820240020542c504021401a8852000001c98600c2c01c6002e50800e02c0030908581d0180d20768074104042107001041d60252042100c103100110070340c1e400b40c4600d1045956900c0803040e20010885c0b40100346092604a5071004c2c00000440d8014080005c0f910400c0340007880c420546041c80d01081079030303200652018449031b500304042e440d000c3c1940380c640000c03072580c01c80e4007280e005020307600c00e560100000c1035121028400d55040403e1170b03441d0f4050b510480d015468004005140d68440c003040c8501881211145515101c84103010380030b854200e40c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 570987059 1250 570985809 570985823
    0x2030c060d020a09053010090f1a042a1a09030709060b250b1315090c06080901140106020a0c0503160302011101150e24061614010c050403 61
    0x1002419007410440000815140340e41e50b1800da9401e100000130f564400c5946210707204070784803c5d201107d0b45c460090224040c0a02440320300c114035002c240f500d10f500c103205039a040303981808009040e9010981e02240c204101c0b1142c8102c899075603110000356400351034603e2400c1c03c541c007810065401032282807419070560b4241526500245c040d10010f2103103145d410340820490740d2080f090218005d0b0103e41c1305032013402c0750503500d90482d129000c1c0d90944c002e11105019408001c1d207048035098841c483d0b401803100c4441030b125901c81003141d101d08018080d046001072200a800e601010030039004207840c05c0d007541c480400039038031800c411781141c4400c0300301000714851400050010441d8013550380028014107642c01103484c104143d1980300c1c10340d2504c0d005150752508003900c130003501140651140ca485e04458848074007202603071400096510030116450f0b603e98108031001550340081140d40341c12185820071428400f82c903a10700715440c0c080c5201040e036110000344122801604 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 570988309 1250 570987059 570987077
    0x240e0a0b06100c080d0e0319030212070903020a06030f0b090709060f080c04090902060c01060b0703030b0f1f09170c1519180806150909120f030402030c060d020a 71
    0x10b000d6a141c403654070054001310080c0301c500f55481c0240c01a0300320710081c100345d03420803462042e54100804010104408286c002c9980462640c1c4220a80d078040101d1910020207403841c0c002c01d0000407a1300a1a0415031200c00e1400942c105400c29131948801811a003403070f20304964003c10382e0105000f5040058400703010f0b2100c0900c180240e50280456881040c0350500e40a2000d00400f02e2081c0ac0b60005014050480e50700300a214860003440709441c19960f50000b0f180080480f94595440d40c030811308100801318540740d50301c0300c4800c00419509503280da94142030503509500964000e05420101c1a0003111240011403402544002514441ca9542c40500c00080c240100e042c0d036a6200d00301070000382c1181c840c000403814924003030f11a24809072078030401410110304540c0702175081c1020b021b0f000e46080280005a1020640000d80340380c000500c1c000c0020321594010025541c0d0100214040d17503014042c203003201800611255840909081880180d00000068001324003140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 570989559 1250 570988309 570988339
    0x21b0c090915060d020324090705010521060402160c05100e01170613020f07030e12030708220312020106050a06080f0405071a0405040b0d240e0a0b06 66
    0x3460502a01e82a003040350303a592030f2030600540e070040c0241030303905115140c0055041c2c03c2d04241c00318440c0c0340c003e0041395460102070091034003429034052410086d080004c41118101c2100300300054030035220342d4444da00d6042c00a8041e000d400c446801919030442e2000130030460080003000c94105485d8050b4a0394003400a0301c1605020710140c0c0402c4400281000c17006a8483c4158412030007000200c2662540c14100c01301d8000079845100b0040008a1006054210080442e1424200c031000e0041c0c800011310b80d101d008011004041038000b1609001609050300004100c01c201c0001d90152136603802c0c401c194005d0007900001652804402103406e040c0052104144c4026031598001516201c41c80f40c1d0741038000344240c400313008645020610b101403000a41214103001e00080d22582000d04101c12502001c81c098881e0202d0300c071541c0040d804080d004540400c20440d00e4100f6003070319181c80946000d444400043c0101d0200004200c100900203008241c00e03280b0480c1a0001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 570990809 1250 570989559 570989563
    0x70203070e06150307170112021f090909020d0b0a091a280b1005030115080f0403050f0712120507110604080c0c0a0b0a0f0918050703021b0c0909 64
    0xb80c1c1d415402c8400340c1c1c04a485070103440b0043d070b0090928909492141c0b601040940485001e0304a80d40a81b606118a400d61800381040b240007040c01c414041c03280c132004030103440748500d403083ca03410f642c0700c070414030075947e901d00c0030f9843c280c2005440c00f0134a40003841d00014034614104496a014108903c000b82d50340c070716098890681c41c0443d003642c0300303c00e6821120081c1c003901c1c405030f80d44901d400295a03c584503a0380154400e511119100d506010540d03007010604001c580800c00107204010000b000041c8594125405081c000d61710000140c6401c00780c81007480c00390410b00004500c3c2d41d420307400b184207000e180a100c1c003040f150319040c6c0101d481a4248040584e075500c150046408159082c1c0240802c4100c0f4045070301c010070010100d4441c0003075500040904e0008100041e00307075004202e44404104a107040001ea600b850990029480103180106c0070b955200d000034501801307981150035542c40c2981640d0101c0c0d0280c0700307070ba981e141d40508600030400f41c0b0120b1402100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 570992059 1250 570990809 570990811
    0xd050108030c1015080115050108060105130312090806010b04030c0506030106020c041e09080304020f120718020405040e0f1005070c080706180b15010509010503010608060d0512070203070e 83
    0x6401c09000d000c10703c5500c01c8041c20f0b296800b0b485400c504000058440824810f0300d404291742c0440c04602c501c1c190000d4086503009041e9414410208074003446010842c00e0001607d62011006000c060326900407140300440703401500309482114008030306895030030040c10441e4880d1b000841c620f0f880d001400b0760350100f8131882e00907a100d580741045918141c5c11800c11100b066107032400503108981c0c0714003650118402a030304001c2c00002c1c00158144006040031080069682c6001d000c00d01403a6a03440119120741003401d4644d00c8401003031426901194011320005100b40f004885d0280f000340c40311410300392102244540c1407002061103143c01054811402d03034450400342c1070300c2e40390a0f00590244030200c1c0d1645e9141c0130351061440d00c1c04410f454500075441340c2c3c0e1a1910020001d80c920707001540d94140142030104c150b40745c0c0e02004517810350f00c1610701180c0507100c13a00811400d07501980c00920b039029804211418050682c00b40071514000c404940205950344058000540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 570993309 1250 570992059 570992077
    0x70503030403080d0e0f0d031d0a020307060f020106120b09061503120a090e010303031e18020d11030d02250f0e0714040b0310080f0c100c0503040b0d05010803 70
    0x1080c0100ca2104c2059440f4110002844c81a1048051114501400c00c0c0c061010000071030303a15000e160680c41c8070383c418903902c0306207001001140700036000030356210b00f24410503041114001701103413024800e4001c4401450a281003d04030701041c41c000d04114000c0b030b2480040c0c41008000b0704007610b00307440c640d8450406805080900300402c00c007019030380308152800034851225000030700040d0b0501c90303d0080d40260350002d140e05880d5182540940008070b0024032a00f450002c041c007450715072080c030321554120b80146044040f4a0302c9660100c1a016041d4140100f076404031045401203207046030f0130300c0401e4051b074648005401c1d00c41031469000780740b15441480d0041c440401d0f0700080c560420002d040403060381610140c031001561182d0402c42040384040248500c129044103401c0240168102030031450001c2440a070341c42c0002100c41d84240544140e11410501401c1c0320f43c082500b00007520f5440c0c0c2c1350064a0000d900640030102000d14160000605c1c030300c00300c20b4560303040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 570994559 1250 570993309 570993323
    0x40f1401020c18100f0b040f15050a080411120105150a030f020405091612060609060b0702040b0109090c030203040c06020d0804030e0105040510080f0c1e0309010b09090609070503030403 82
    0x902d0715041512143e0000701480e800742450040440d40052504080004020600c0c034941e480b400e044a8040c0d00555500076030025601007501c218054100c0103840d025001841d04401540c1c0354180070b41903800550f009600300710300d810500400241904600d01c94445810100c1c80903000c00c0510150540c9440007030124001c100c028001450710307800a98000215404031988c1d520410000000008960701030611040803110610400045e4040e01d001028059010000c0c10f141c19010003c502c03c5a000900c55541c42d03c45150f02e07130142c42c040b4082c00d44084200400c10300c0c0507002d03000350b00070b9805680d1720050303001c0010f00c00d1000803000d02c15083e070b59035020951510340d42594920b11406804c0e05000b001c0c0000b02e5075440e45120450083c0d000c0c1d8400b1a10304000d50803040036140a442c80c4e20181041042000c861621061080c040d07405c540103503a00c2e6618174649004110740c101030384c4d00c00b80300c80c184540390400050741401270030500d0a45500f0740d0b50b101010b94038426403000078261 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 570995809 1250 570994559 570994579
    0xe12030f07080d050f041b0e0601030c1211120606070f02010c1a0c071b0503071202041e20070210080705070204060b0c0c030c060f0915040f1401020c 66
    0xc801809801c200303109520150801c0110207201040c0d0f80100c44040f90104090300304018003440c1400b25102001c8080700000343c604040001c1c1d0900c0c4010403141c1410b85900c0d4000d002c922519152a08070841c080400210f403140c81c009140c4d034002c00d0f01c014900403480105101d45050412120070076031142c0b10140303c141f00d9005441300303910010260b0b140f07a904402c034842103040c0c04a1038880c0c400740400544e2001030340b0f810f5541e034239441d10150016290385010701807030314009a00016669200c1c6002c41d20b0099200182c0604a03001c000b40d005c03a100c6051100c850710941016a5903190b0410360214050320329444c0a4900601001a5125203190715255001e030055400710b8001105207421713480c04e2240e40104055032035a070712410b450080041e041040180a1104800d900c20840141040c068040700041044c02a03481c16080395100044151803130b958410300e00c00342401c40c000c01e40c0f81c03580c0c0da104501d58081c900c030b110303078884541041d2402c030340c80400c0103555443c1c010500914 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 570997059 1250 570995809 570995827
    0x1302040f061817100c0c0201021024120327030f0f020d110405011d010902030903042c1e0f1807230105031e060f150306010e1203 57
    0x100c0d80b025000008001c141c1c03100402c2030800203125654000d041c00041c00d015901050041c22102c00d207101e00704001d8680c1c28800140c0c0e01080e07e46501101d035a000c1403544618041e0301549650b411402c60f2004410400907110722001000c00700540285c030b4503020101501088810f850b00180d4800421034550002e000098ac140640b014540c0207a00300b95050354181d0206180b460607030000c1c1ca071503400140d41112440c0c5405400c3c0504000380301d940c0c40380c40140c0900900d21040c000c40c40860740220006580a00400548006000d010000d594441045007040c16000d01c54144400940c3c00e80c0003d220241d04407120610380f004c035007038035801c0d613508070380b119080d5000b604002c1d02c52018114044110000c00c82000500540901202c14805402c40007241c103010071041030501100384200b11070702c0b02070902114801c0c0e481b040c0b5444c590f14980000c0120020560181d80320072414408410380c10104082d5100e0b0300c080c0c84000b85180000c082050000402c80031602030342c400c00164107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 570998309 1250 570997059 570997067
    0x305100c030b0913050a08070f06051b270d0b01063b040f02030c12180a1e080a03020c061308040605160f03080412030e1e0313080105061302040f06 65
    0x400d440c0100301755201c1b03401c2940d45924a0b070000906481c80f81c4224890014002c80d40302d82d907001000b40700d94040c64024081580310345e0180003445452440082c10006042020402c03140c01114006e110441224251408254088084c0206400507103820220081300103e8a9044048011303a0400444860350085003810f1841214078250060703181c03101011891040c0c005140a8504c8845240e2500800d0484c265801030041401000500b0000c52854901300410700d16100da40150190382c0e00c0b04455149098140802c5004140c200005450b040043c0d1560141c144040b40505072400c5407650300c904113a2414802001d401c142003080100401d5000e01d00400340300380d0480300400d0074400c5071601c031304000150009801107800c4400f000b0400c03151102c9424a120203040c100186501c114205955140740c041317211407040660152882544108241d602c8020820314001130a500c50031040d02900040e5003e900680c40500314072868010740c000e841c1070716045a030030302e22640741c22000c413 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 570999559 1250 570998309 570998341
    0x60e0f0c010804120509090a0204051e0906091b070803340e0d0c140907090312050702220e06010801140a0c090e04030201020403110d0206090118050a0305100c030b09 73
    0xa42071000801c00c0c1b01242c2c60700003605101e548414401030302c0d24500001e00c2107078148404007490140c40c010121104e81d0390721a80c0754103c0c0301503d6890041d521f00124401d4072480c490416070351b007070205a420821a40c3c1d401940316100d8203a0040d10302d0344000c1140c10468410300781303520400101310418004c91003446050041a401012002c0d081c0441e00c0d4065506029003040886004512581202d030a22480702c540094140c60302501c003524545580c4c410240c21101035040180015060701550b44540300c140140c04c00c403609090740d1303601d518007900a10320003014030440c1c09018000074000b0300c10712404d40e400d240c0149002d0345917140301079003000b03041d030307815045c14420f08007808284c00074030410300c51041d48a0f800060f51142581441442c0c140e81c006400e1042c20505100001070f25090141c2d041140c0a080800d41c2540c000b05400024074103400c03080e00448418400000c2c0000050809507038144440200b0440e03000c3d40f000c070190703540d2131845034018603050045040071480314a16 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 571000809 1250 570999559 570999593
    0xb1c0b030c120f011a030d050d1e020d061502032b05010f08060a06140d060b10030209040f021305060304051c0806101829030103060e0f0c010804 64
    0x3a80281ca107450000e142007190300250307050381e4020564000ca1840034443c042c81c00880900044043c0305200c0061780d185c50711205002003240204004c40501100c1d080001d801391001003202c06005141389080003500503504084010f400c2c0400080d480c808841d86007601d05030350f4055031504031070458144108050304010718229a21800c1c152030601188911130181c40b07080403403008546840c43d544d01d04a0054030b01e140b40c515003803042000304103180703c0c2400110203450440d07a103282030600c071008150200300e29801c010038404d0742220b264560300400010348102e40800000c802c1d0343c0301314100d0050000c03461a070046202c0600c00c5140100181d1f40c003900c1142240d00303407480381c2490344491804560600c003041800e010f0107010b142218080c4604d40013483e00c0640300002c400c440c00d05803144e01c01e06980812424510b902514040c01d510182c2c0ca085050613960759480c90500010420504800c0c4070780074902e41802c0039a408200c2030910003050307494142e961103580b90321180100700070356 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 571002059 1250 571000809 571000813
    0xa051822020a27060809030c031c090510050106030c0e0631090603020a0503060421030f02040b031e09150a0f05100303121104030f020109031a100b1c0b03 68
    0x14080f190014a03030100d03110004a003030600840c90040090003141c4040d00e00d18071504140048000e07681c000080d030302004d101000d40e40c18000151950b000402c0102c0d005031840c028407800c211000d0f11500300078101e4005503010083d10f074280c4070440301c003861940c855500c08000c021000b1030054030300002c9007161010345070f401080481d117180007048510381c0c090802261540403c20540c6411040d1100420301034026214500d465514074541d4261004100030900c030f0652650303000d07031007548400c2d00000103038000c40d50f65498204442c800d03003088034081507104c0710203c032b00f51a08404a486018030042e8004201d2200e1059035580b024500820000c405035840d941d4000071081402414011640422441805419810002d00340501e0b00c6400071400d0911440b050002e01c890211003c680c1c02004040a01c4068030048613410015800074144243c0300b682c640340c0d44006000c031801002c0301000ca40e107160340e4412683e254002d400c0360401500f550a0b078008112b14a4125170300c6560b004007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 571003309 1250 571002059 571002077
    0x30f060b0a03050607030c080c0306041505181909210e0a0b0d0507030506100e03010603080c0303011706070903030e040b09090f100b0f0d060b0301020a051822020a 72
    0x850804440c90b8000d880c03562100b014420943c6e05032041403072084040c50840340602d8110160081c0b848080c2c0500c1c001c0740e80742442031181200c8840741c00a800014103544400390450b070341c80100c14068802c00c036410581824602401d6452040086036503006c600380c444070303094a55031000c07c1c0c44004500d00748201c009403c02e65640d80c1440301d0203440708060381c6444078803902d01001180c0e001042c2e18149868001809103d940720075462965070003514143c0d84030005440800e002d0116988010161107021542c920703000000700181d410f9540c103610001025100c1c5d00d4403030356801c05480705004980c5214080c00407900c03801560b51030200181010443c5d28101010400c012001c65030810f4a4100380b0b08481c081c6418005004000740580c0c0038443c00c0344810010b010706501d0440780e8422862140100108080380d0800016020010002c44d03c0c1d10401001514591200002e04044009028400d40b607140941e1070b1000c036503260094100a05800c14188001d50000d00310400340703c2085 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 571004559 1250 571003309 571003331
    0x31006051e0708030412030e07090e150f1902040303200c0a060305010f09140a0b130501030b0f0a290102030403150f14090a08181206270304030f06 65
    0x44001d00ba5103101d820015074a00d42400d16484082c8441060820141050b01c00145480001110b0098811451001a0070a980c2c520903140003081c1554882d500701003010014425400b018552155072143d00c41d000f0301001003101c1d0124461404000c02055085502116842d6511740200c000c600240444500c0484400010480400c0c0d0307000d41d0000c2e8880006005d00703006c8198000c0100344681c0300f03005490224101c1114240010b06100d141d82d51003540b43d040d903403002114402c003107081004000558407410b04a031031510841c2c0c07941c2d13003142003400314080380180e02c150030007000c06a801c2c1c0402403030303004000030400c64403690031304501c414000440480c040c06690b441d000a003490019240441c040c800e400c2d81e150340c2c20717612580a41c0b82004040e20300840e13400d0019500981e9556525046041c2c5403502c001e403a00940c21003903940950040c0d5800040c1c960042031111140c07410900ca1011280d00601007450041d140c0c0c0041c0401c000161020300c07e09401c030310450012408c12804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 571005809 1250 571004559 571004617
    0x1106130801060801180605060604050d05010e06072c03011d0a1406090d0305190f0e010b10052d0304080d15030b01290c01020d1103100605 61
    0x19198996044095081044120000d10039a40100b80f060b009014400c1d84100d4080780c0400301a0107080140c0b01c50005109aa42800311005000c0050219456448605001e4000d0262080f18500d600c59140807542c41e0b80180f038035a0428444080e40c1038201d010000040401070601502a003640d02d03410000c015000310340112507a000004020f0010340702e5424030001020030441100b0498010506100c0c80c2d207804a50100d2228482c20049a00d4885018010141000b40350208a49140c0300b080c00600305260462200c8401c00d4009000fa000c0e1101000000000c040d505ca000c03501c10880c071a51a0301059044c48481181c8640d52003601211100000d5036100700c4048812040001e656492000d031407092820345900144400e015038115951170300004418096440620702d000383c04c0c070110030724680081da2416075072402911000510402030217504074030301080c0301605000407184961503032400e4074400c1010200901486140120548180e480403030340314900162184052482044 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 571007059 1250 571005809 571005817
    0xc030e0102041e09060e06010f1101140f0f01050a120305090d0503091201050f0705070501020d060f050307050105160f0f0b0c0d050708060310020a03140f09120c10091106 75
    0x100f40000304141e00414056030720f00416048000780314075068042c0807428040c126203600c01003e01b007072510b0034040c040685280d92035100e02d2620f982803000c043c0f4102035014050b8020880100c02c1c92540d00c1e2102d218400b45da0902403aa005202500100024000b0b80d500914032400303410a645040c680c90302180508221b42e60907265030b4000a10890141084000441c14020b00702c001c024506010031080641d20001e071980d020040045005014041e080d4115180140b00c00001c012460307407403004604602c101d1180741c0c0700340204c060014903540503e04079a00f01070b40c41e281282405040c0c4d10007c0c030000840c8141e0b03e41041c502c85000080041d04d11701c0c00b84d8042650191108015082c040550303600400700c104000d02c0103703015450314005004851080c0b080c10158a804440350110000c000100c007034a01d5030904014000c1500c42142d04e41c0c01004080d048d508100c800500c049114410a11081c0280e4483d58003442000a81d60080395450310409600c0207000386000000d8007504 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 571008309 1250 571007059 571007069
    0x7081f0b04031e03090e0c0408100605030c040915020f07020306130b18030a030515040c0c020a08030403030927050901020a0f08190506060c070b0c060703060b0a030c030e010204 78
    0x1c0900c1401208116001103a150701002e040311100390350020041c03200c52050f913082510780404203c410344c0030002d48010704500c2d82110b01c90401e001a55025000030301c5054080d000300310070841c540c105801568207254121b2100c00000d080c801c0c0181c02544140703101101120705000c82c02c0140d5081c80707624020250f50030f107209420a49c0c1014138054402030b12040d11052110043c40c003d14000c000e5880c00b030418180000c42c2e0b903441100c040500718050100b58007601d0294242003c980050031121807900039104500d0a50321014180d540c1d2103540400303000b01d001c0200030860303800441c5003250b1017510602c0b1004504083c14005c415100190790600082e500451021401a0702000717031501d038550391401c030256050034902c0d03a400705000d00103151201d4550b000503a2a4407042c04032a10381201750112200c8650383e141ea182c3c95000209508103d00410020401080c40786c0124815510001505440d003001d00005800825407811030303400b4140c50341ea1040003040c00b03101500040c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 571009559 1250 571008309 571008329
    0x602031006030501091512050106030b090312010806060f12010e061311010905100f0207120b01030507080c0f0f031f0606170907090b01021219030605011707081f 71
    0x103800c00e41c02400740d45058101118181c0340034030342c5010500280c001030490f11701d08070100c60003000d81007450141ca40e40c0c0026008114100070301c180c02c04000020b04122019018109084c0d0300c481c1e06989900042da5040d40c40380181c001101c0364035120684e914000c041c000000f07181009807130320700c3c1403081c1201c60648444050b01b800c01031108070b449214150a0918112442714200000544401e451400400030411003400241610380200b03d050083d000d2005504240b14641c90031440c00502400111101d000d1241c00258600380003401c0c0f4408000240f080200703070401e105004a4003140d03d0b030365600d44a0f0301c41d130414507881464001c60410200340e0104400d030400001420180810401c13861050602040141050700031030042e043c2c603056040860039800d0140100d207000541c040c13000d070034030380040c01c00d68003a031300400c90000220949007800019500c9005440072011103903002804a0325a0018014908c40d01426522100c8001b450681c020800d8418000d080d01d48c020302031903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 571010809 1250 571009559 571009591
    0x9010521010e16062c0f04060305010c020f0703050a02010815090a0b0916050301030609080f0a0504060e0a030228082a060313031101110c0a0b1b090f0409060203 71
    0xea0704103140070081c1544d802c101404001a0510070130700480400012540104560346820f182c1c1e80e41c085041ca508001c0c811312155440342400d600074448034103894003510a900c104400c410300401d000301180e401c800640940301285c5c0065030603100042440518410303102070b6860503581c40c00c0b042d0140081c10000250b0136030301418803078000c10103031640340308403c014001c0120325405000c50381501e902400210381c2c80c80514102a082c082c0c4c0442e00184140806d422000139400f00142040380ca4665403280b203101588184000720105020103900070380240048040962911446924071008100d40050705664040d05810500040103a079415120b141c04060740c13903d202c01c1460301c0380040b0b407107519605005000707039141007000800805021003c1500e0801d41c07000c0d8050340000d0311010f0700e140c2c0c40800c101100e03120b1441107001c4981c601c0003004102c103144015014a118800c03803404c00d180990360004c100c011512094141da11a446d11130500c0009c80034009140180303a284951101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 571012059 1250 571010809 571010833
    0x140904021911070608091207060b22050a0203040b0a0203060a0807080114061c030c0507120f030f021203061c061a09010b0702010e010509010309060e0606100207030209010521010e 79
    0xf011216403082c01042842004c2c42401c600108400591003546800780c1c3d5190780d1440c02a0140c81100340303d541c803400b00e185d00d0009100312075100e00c03003030303411442005135a075085107840c124041581c016040142c50305c0040c4c80340b107482d4011504110010490700903140c2d181e0381240f0f003a00542101306265104c0c1c0b200c15103114403c008580007201190340c069494200e0b09510109202e0300009410090001c0b0703c042030180502000001e0b25000c1c03941503c0510781e0810355581e6035840c02c200c00003080405208103161001c04c10384042401e4003041459030722074108100140d80b20a8016580d8440b0b000040001010f611500e40e1010079032a42e41e284040d00c60400031070050503444203544070000c118000042c2c0c0e100c0071034800e5100908069454445040040f401001a40001806c161038111014010600011501d2180804a40b00e004007092064100e8030b070740c0c107480000c3d04481c2010040c403040c0341551145182c051320b807108603180390820021509481038100d00041039041810b120710 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 571013309 1250 571012059 571012063
    0x3130305010f140c07170f0c0d0e0303090f0420030406050108190c1e0506070303061503020c060c07050c030303100f0603050403021902060c011a0906030706140904021911 75
    0x1420080e0810024003403600307200301300d418468480010607259941c1c00d910001400d18094400789207803a400c0688a12104c54842d98640500d00600c0108440100c940400c1c90000100c1e404a02701802d0021002007900500000e08412602c00040c4074860054043c001403c0d0041c51147e4011100403481c0e501d00b54240d4100b042030280d0f40d81c020590074a407400f04810100301d00c21100c0c18180a021000f88082000703d070401a00300c99031100d000901442410b0785600300c403094070110410400340c04d500c214107808030f10480e900549030360880c200090b9800d2981015207401c502800c1502c0c1d800026100107800c542c03003191121204141d00c0014402c900782e40080d140608110305082003e402c243c0c0380a5520740d1000c61820010304440014411511480140d038580d50a6400a01440e1118a50020051601c820701070041c50000300080241c5000681b07041100c206444120200e000148220804d40c03010362036580094080000101100c00139a24045940881c0e584403080003030200814 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 571014559 1250 571013309 571013321
    0x80f01050d0203030a080a18081207032f12091609020906070f03172802160210050408030d09110307060f050706060317040302030d020607020606010c020303130305010f 74
    0x380105000300800c401a00d002041700d610103603900b00708081d55035021600700030b04010450b4840000e00307024203804110824028188040030000c3c004400e503510f01c801c804841d03505e0350803404100c40520030b080080390401c404010143d212071007482c02d903210304030408818080d60704249540c00030082e058055210402500030740455081945810094000100d49010302003003d0070102c255450541054090f281c0c40d001040417010310440740c50140755410954008a4880c4d01c2514100d0402c1c2800c0b1040c400c40d980d1600c41d151208920816030203001d8140c021017032a406103d000c000c08684d100c010405400c0907003280801284222651411740e68004103221a14007170750248100784003454000d4001c0704026810f1a11907168403050420714013403c281da0024241c00d04a0214800e2081e0100c02081524026030885005101a2204a81d5018129448001600481c010586a40c800da111100d0240001c00322824220345e4074015030270b404a030f4000c41d81695502c09070006564035028032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 571015809 1250 571014559 571014569
    0xc04110c16082119052205030114090a06020c16080a0314070210080c13030c0305060f0c0a080705091909051503070902070204060312081b1603121803080f01 69
    0x11a0b00c6051602014446000c1e8101d00d030882c014405040440510600c29901c070345080d8880c00a2148006c441d004402009000780303400303035003084480201911100303c00c41c0620407940c000d0181009940340c0c00001c0d0011080c0d40824015403a44d00229103007810588040d140b2503015116100d02450090704501c1d0b8100484242c100501c400310150ba5038400c404801810750900c01d003240d6407520302d400188102c2184aa007540001804002d00c02845103040680703201d0406c454a645a0f070b20700300141c1c0004c64a103111000100190003180e80309040c0796801c400c060503c10b080001303000c0020f0004000c3d1000c4c40664820f200204080b903c0303400303040e030000702611701800c1c0b00e100701c07000c40c3d10b44081d4000c20b64015000a0709404542311035111074010764100d4820120348040400082c04840305594104103551207a01003101c40901070100c4800150110b042040058666011b0751000f000e19100e078140e956a02c0c5003c45803206611059819100f96580c0b80a8a0007102c4600701010603041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 571017059 1250 571015809 571015843
    0x60510053108071e15030e100e100e030906031807051206070e010e0a050405060a03020301020712080f220201090305030a0e03210708030a1e0c020d02010e0c04110c1608 74
    0xc10440c417402d84c441da045540291030f000c03514050001c030389031a260043d40c03038604040c50800e00000b5082c011424441d1003540010074820326042c5603005542e4040d0b034581c1d990107a0200003054819180c42e550310001c15100050f155038558a9001030595070480341404200d401c01c8081149080c0d100407031104540c0e0034202000500100c50120362070511303500605024981e02d0001c1102942c0b50303e03a90340215801002955100c03030728900030a43d01400008580420000804100440c032482d28107032240d414140107400c0c00e62442d01031881d0300035030361050303061005074100400031500c2400180740006850300da80030b55081000c145480e040f842240ea1880c800c4240b0084282150441103c90320b43e000036000303031a5120480100c000f03101404000304103c480e0700310100884802e4002e84003451080e02503c100d10031459041e400d0302e95004a60070313982c010310810289482d25610085083c01c1d40c032207031418004440d11030351400c40407420509805206400c1048406410000310002000d2900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 571018309 1250 571017059 571017119
    0x8132402030d0b011e0207031e0f030305041e06051b03090d0503040201140d06050a08060609060603190e0309040c05040f03020d0f06020304030c050106051005310807 73
    0x2009440c0c1c02031400e00051551922202441680b00380c188003c5104400720312400f120154001a40d02d00ca1444101d410f1100c4000b00d104006944080031445a0802a40c0802c500d203903400710300508005100b100c034142c99620408050700003016030a80305100c1c2000250034140000c0c04040a0000d000d0700040071020000c205401d1004200107103006024100305441c1e445510040c0d1b03c15603220600e11000c180840c0b00a404456500140112141a282610610f8590000c203442e090100d49454100589601103007107424180011a408500111b0b80bc4c448030b601c2c5009010303034132205004441c941c8081030011407803405208103250a040760070321904c0c0515042c0c01115070341c421301c0003a208038228010307a801d00003259443c884485c3c0c130001c111750305e14007860b000d07004a00108081e42c040d0310300b103000700b41030420000381c22041103103480d10390920046450071030303841400c0e00300c011441092444503c1418010040d01300a0841140644144d07400c0800c0c040b85a8455441c044000580b91 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 571019559 1250 571018309 571018379
    0x20a1203020c0d11060a0801050a0b0711010806040e0703151401060206070c06140a020304140705010e040b062a0f070b03010909050c10111b0906090a090813 69
    0x103180c1c0d080d40800c3d504140046480d0800b40310500c00d01c1c0d10b09801400024500080e640d22522650580310f0464581080d15103c1c0c041e250107006103030000307086600c1e132a0300c481701e50b000d81d402a50280d0001d00125142da01a040241809003640c82201c2850040042c0385d80c81003980550696040804840c02c1190314001c0000d5580d44007070040d40a11000350403040500100b9000300c2ca121280c1051400039040c4424000000e41c01140d081c0c034110185140d45001103400b084003811504141d5a100c001e040c2070b000c101c002e040031030246600110400003038900070460f03c041034000440f0354440b0f20040c030700030703146041224017028803100c2c0d0010304050041c0e007104410303a815503401c41c100260442084c80c01ca858401e207110625800b5400c655603080e080c1d881215815034880c641e0130345111701a01001c41002c3e0100c3c1550603445000080011410700308a15074903405800220301086500441e11140314560001651109456800400380001a901c90380110b4482c0c14044502403c070f046 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 571020809 1250 571019559 571019563
    0x160e0907051002010902041802010f111b120a08130f03080703210e0609100605030c0f1513170a02030c0405060f031c0e2407081b0a020a120302 63
    0x1030060700c0c80b488800001d0201107200758041c1d543c007075000c1d10412806101e060840031844c0c0880c0704900043e02d840c2c0c912005032045030001e40300100f0740010a10365601d625100044d80170f031042d40d46c11000c58411440030980070881c656001d401349080c0c680e1600d250560001c440029002805800101c01003000050344410490b05041d405280000302d007030851044602c5074400c0c28011145034201800185012408944507010303065040441d1810701340746100d4000c0c1c0329684117040d416044140036030307001d0500c40d121220704007008000c3d0007008984040d00449402030480d6a0b10240c40880a0001000700801c0f10800c0c5c0d100c00040010108a600099030f4122018405004507203e401044040c0c0b68010360181c240030080c141c1c0c000103428002c2c0e0718003c00c29501040018101c91a1a9181c140441c032000e4902180e8005060304e04289a09603641d40481011a98181c0c100480700c000c02140d4003080b0150000d0f009495180418010020414400d0300807907858020881084002900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 571022059 1250 571020809 571020823
    0x323070f0b0a0e030c060f1e100e060406050a0302060f0c07060c020a050103050f130606170102030a0510080307140312010b0d1b170a090f0f0302010507080f1906030204020a02160e09 80
    0x400c010452030b980c1c0c55023800f005c1c602c4100d01d4900c0108a0309200701005c40170a05000d0703078500c030340e60f00340b60360391200f08001e60b00c80c1d206194102c0d4a0f0403051002d41014401401c0300040701480c0c902e04110302c08403a10301401e9034040000180d600d1488811443c010302158010a003d02e000e00c1241080c411508a00801a0050b544e100303950500c0d04c10011141c01800040200017058081d440403894014040d43c41140c030005442e14003000128603040660341401178a415030021130401c01c05c4e58411806500100d08070318a07210501000c2d070500c80c00c00d481d0740a840b503145001d441e50301015829081d00e08111441a034501d0b500903841c0d106500c03c0381040a031401c207500c0b8032542c5a604000c2d000344100d2501402482103001541c09105522541d0b0300301c03c0c4030703030b00801c1650384500040f00c041d6402ea03103240c2c1c06489440816440c2c00d03165001d200300c1854101c0018880d98a80c005403c03030340408805c1e40560404088910002800c5030148002d110180514082e40740408a10340c980b03172 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 571023309 1250 571022059 571022071
    0xc030b0a0522060603150618020708030711010902040614030f0106080309010c02130c0e090c041a0d0e06010f06090b0412020402030c07080f070c120323070f0b0a0e030c06 75
    0x2e51411032400740f002640000d0021500308008401d5080c2811950000d00301d280180b010b500c482d5201c691050026208845001e82c000340c81c541035031100c4000f01c50314005008444855902c400c0080e000d640c131842071000810306046007480000b10a001e15003413000200d69402c142e45491400c100c16580401180c041c04001d1070f05440d041c81d18400036007400c000300c60705000145440c400c0d01002e6000740324610000411140b8a40c0c0341d954142c100354030300c82e40c02003051440f2442d24101c440d100c0f42c2d0150211102c0d070b4101191007d40d902800e480d01c0000d0740041180f201c50f140400c90641c10580e0340340600000a2420318050074035000340400c1c0301c001002070091750b002000070f04234418801619100c40d404086c40780c0d20100201900c2094001300e070705070f40291011000051100c521210003566680c5601c40100303444001040060302100d44225503010b000070403031140003410b4150303c0610a841005c00707042c00e0905024610031514018210b001d0b6038010031485400d0303a800940380780c1c044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 571024559 1250 571023309 571023361
    0x908100b10020312040809041416021204350a03020c09070c030819021303081c090201120e030c120408120408031914121906141302090604030c030b0a05 67
    0x622600101c0d00404051483e44d1140c8290070520920084ad0708a0b0380b00c025180d821241400100c3c44a004688a00c0c40380707000c1c40840640030007040c01284038a00c2c080b84c0d040304015458140d070035164200f0761404d90440068000d400300d000386181039245250040f003545007042c1c0e507000715a009004140082d00d40400d64603030100c0e0801c4400305404a4000b0080b880313440042c10750b00c0c40c1000440e00006880e00d4040070b50f6100d01c3d00315040f4072502400503016501c0301082981c2a001c10010001010450303c42c0c0410826003000c114208800b0030541301c0c88035141c7c0d660b4640300c41d40342012041c0303c140100d40307000c0200700203180d0000b00f900d0041d610008074410005400c601650008010322854080c0c003400700e1800405060802c80034030499180c17000391184008204035000301c2d8458050301e02c0381d040e00d16140040381400b000c28000c40840c484d00500c1c20352180000b544c550016403040b01e4030702040d1428001c00034100c6015801004c81e010600a0303052031194000e28030700c901d01900101c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 571025809 1250 571024559 571024567
    0x1020f090111071707151e030b030c04020f130b0408060c0a021f02070506070207060f05160605090a21050a0e030a17040911041202060702010908100b100203120408 72
    0x700c00c00d20010f0020400038011070b200511100030035407541c0b5980b1401c1104030141c81c0c071703406840c0141104400400c01500b202d08030280c00c4801c1d002810b0049155406101324219021a40c0755480103120254100e07440980301d0700c030105414164907258110050440c0c042c0700c10406503030000380160b0028100c00c0740940394160420300f20301d010b000303d8542001403105004000ac00300281d000b410050700450640700141d640d103005a0782d44105118480001d01500c0301408a640b00350041d0022010f403a885083d0031140b926a42c055400640b110406500b00b40401c100300001480000251001004046900c0622450140c814000c030b032464801c3c40712810b6801541e54061081c2c404140d400080c4e1481118046151019074005020310030809103050001d1902a001500380c0f41269000c000c0c101c0d07248000e9003802015000200d0407410303c4804c0c0008510b5074414418504a40305004000440c00c60380c10802140d10014030081d020740d0020000d01c28901d10312008580d019400c20440ca0f61 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 571027059 1250 571025809 571025837
    0xc030609050a0b0a090b01061707052116020d0f090506090d0506040c17070521010615030c0206010e0f0a0507120f061403030f120a02040510021e01020f0901 69
    0x802c00102001083c1248501c00c000800c901940425030300340c083e0611030341c580c1c0c132202d050310503010080e002000d0800410000d002140300b0002007005408541511112620450100f80781802c103685e0402413080e00b014451010ba410801420085202c2c541070041e040740d5a005001d9410300d0240d01c0c00307400b00042840b89919840100540036038400125811b034901030600400c4440c207030141040007122070416441c00c28000619109071000108088440c4e61468605008108d80360420b140340d5403295000264058030b20b003002941d01080d1030105401040003802410001c05801c500c0c10082d50b2000d22a05107074028030103510220010b03001074251554803082c6c81170000c410104440c18140b8182e400302200380c4d00326030704451800b038403180c03501494410151079000d0f0b061030318429403062000318503450300c0041194110b840814014981525080412515044174403203801680c8950881100e00031600800f41140303008070002c500f4207201c041a4070340c5110320344145040210f94180290 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 571028309 1250 571027059 571027063
    0x105030118090803040f11010e0f1912030206070e061305090702150c0903010b1503041e170301061b08030c0d1d010c08070c050619020d0c0302030615070c03060905 72
    0x4003454003c3c03006501ca10702482c0901c41240000d204030303184c500224410302c043d4001c040e0104181e400a00c1d0070310168095040c8000080075005050a00c6501c0c0400034404d0106207400414902990141c03499181400029000410b2031140d140a60b00c100450f0004001d80305445003520340489201581d503c90400803468840d440312480a182400d04c140182e01440000501c10b411045e402030064943c41020044104030702e0142c3e44000c0310420001d03000800d4000300000444010300b0f007410140c4c994441052150194400490300800000103100098000c14080e210b02d002800300e01c60354040e503645c56030900029050385240780c40882d44401c1441582c000030b403032403000c0740128032881d200b1000d0341c00382181c400c0341804100f2000116544512811080c0c0009802400030300c0e00fa260709010a407004044006001a44e80c02d00c0b4880306d00c2c140307020b02112400655005078a0f0700b8020200000c1c008040c110840207a001c00071741000035080001142281c0d0003a000040d100114100b080c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 571029559 1250 571028309 571028321
    0x1020304211b060b0a081b0109030c0312211a0609030706030f0204180b1005120712020c030d1a0d0b06060c0304030506070201200a0e040507121401150504050105030118 74
    0x7588400510310114142000086000b87d05e0030380324400d0b8584510b6001500c0080f5a400080d0840c120480180041490601400d10007403451404450381c40c1b211030000400602104000505500d034030440c0d0100d40c20b048007081000d001c07542c1a11742400480040d5480409215180030b060701e0b0403181b12040700070b44c1a1780c02000700c580349040034001400c1d0f1800610414180c0f522420031401415503040c45541501d20250f52020201e07070644590005903080c5000b414514081c580800c48116804000d2012300101c15100c0350200301111300d0900c0c0520308d00070b004210301803c07078080003c004c00e80d000b041c0c0da007000003640e80381d07a07440c00020301c9821032045401c042d103144103000900c61780941c1580403440541252980b441d8034544070603000321603c03424000030000b609135140c0f407400c1d2405d03601190300401d5a04000c4200344072a171144080e244680442d014603446507004200b82c850141446140c050a07161035031070703d4204000a072480c001805400c1c2c44c002e204056414400301640b0035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 571030809 1250 571029559 571029581
    0xc17070207080f150a0501321c050d0206090d0e03030c0a0c210206070b0618070f1b12050a05040f09020d1a3d0201020304211b06 57
    0x10f2000304821202040d40c810345140c140750300c0407a81001030010f06061003114140c80c24404004e00054424040310006140c01c03048510b003202c02c4911302800d80e40d449070071010350084500c2d035004107030398241079007031007446114802590400760401420001c0801e41a80f00c06560a003040e9401c9031401091450080030f50710042440341291010034003143c1940b200403603007a0711a803d14205d0412191110b10307805107000350031801c2404a1b100092920324040c5d8812400703400605c2208024040b149481820756203080455030007501d1201080d8042c1c10906005054031036450039100554030540a1441030384d5a00401c4008a41450b00d10320440c200d60050450034035800b01d450700e0300340510003540036400d440e100528000c2c01c020031940f000200b944d110700080a5500d0b1000601c3c42e5109951841822f4011070303c1e03076904040407a00a00080c90608242c0d000580342d1070f1a203844180301d001d41c0c581407070600c804212104000e80c42750300080140500d290301e00400450345042e40c091f040340c0540e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 571032059 1250 571030809 571030813
    0xe0709140a0b1c1b170903130303120f06090c0201060e01030803011415040608070e040e0601171e031209031204020d140a1a01061409061605160305100c1707020708 72
    0x11121070744488119030074541781402e0707545a00c40c0c48545a0382d00c2010107020544608603410408603005141031038050900b8a80810501001d40c075150032107100da0002d1407410b50b960107403450140e0920403000034003c65500d43d0000d504548511005000500c540200268007124200080e02d0308071801c00c0141ea070760034082e201c0341c4404011b402c8050448400d80040d604d2452049280703424046c6c030b11352035003100140142d40d0801030300c07600c4000381040d49041485440601203640045140301201200d4a002031505c4d5601c0c0d08a854121001a00c1c00e10981d00c00e000580070125400300c0306070803a90407101c49040d0941490071038010f066070380c07a11007a409400c125000740b20028000b4110110040c51044880c0c0c0c072102c05803403003114004001011784041c40701c80031034101180100114501c0c50a00e1241800a98415280c506c0b05c0c04040340c030500005081040080410800d088000000d1041c0080c550085e070040a400f114203007108003105410104040900a200c543c020740402e0302 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 571033309 1250 571032059 571032101
    0x3040201140408060a1407050901030b2d03161505030601090302040617060601050c0c061e0a05041a192d050a0905040e0c1003060e0709140a0b1c 64
    0x180f4035031680000c81d4a0340d50181030003006055605002e0f103451080040e512158281041100110001c0005008c080d8220031000d290b580c0800041c000c148040440a900e4901c15441d0014181060036a400201c2105601d003018003250003241030441c0383c04190725101d52259200d01c0101c032074041c0c0382d00c040d4025250420225500304051240803d03024146c0c04c407052902c0300740045a20b44600456800d550b0004001c0359628a4a200104500400500d40000e600784441d101809a4029040f00c0081040001d080000c41c108060301034003140d544090324140301c0100312600108074000c0d08282000302e802ca5480c0a002d050143e641d4940c02c0b10031704461601e020f01c002d0800da000e03000c414041160144006140d1a10b80900c000b0341940740003170603007020480148803400150b204c401c42070544513800460381c0030030001c1562103041c4070380c0c0f01c40580b07280c02e106105003010554814001d0000140c02d001072100e0504480c0702d10800a814100080380d40d10203801450543d454141e5200107036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 571034559 1250 571033309 571033319
    0xb220b0a05040e100302060306150706020d06170f03090d140d0905040e0303060a1520060f090c031c0302040e010e043305060a0510020f1917030402011404 68
    0x9001e00166243d00c0b1950207591148048071072407078603500c0300961200003000001d0705800c0000c24000c070290444404c50a10045580b1601279030040d00b1012400756a41d80708020071480b80c00f03080b82040540300580148003408500326168490100d080303004041142c525020845e200001400c80c15090094a0001129002c010040c0c01603100d4588154240501d4a0a010700801268002e460040081d00030925203821400000000300411091002000320400ca20000842030798410150001074a610b1518a080043c05100900740b02d044e584202d1076140c1d19240050300040c9040003071481d1006110305041280644215082a00700c01414000007440c90300b040d0b906406684102c038000260071690007481100d44108011280c0540117011012112800d90700c840d400010141c0380c0b208071910ba4000c1003c3d001e42070208401680500d204901020b014000c1082100ba143c1801440e05003e40303980c85881c1c1440e0b140c440300c09000003c01d045a00904082c0c0075581c0e030110260300e8035621 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 571035809 1250 571034559 571034567
    0x40c031520040501020a0b04030c020d050c041d061306060b0d0203090106050105070c120602090d0803040507060206060114130e13060506101209111e010e0306010b220b0a 75
    0x201581c21200e40104801ea1400207007a0782c01d4a006034020003540006450b10907070000058415018000c0c4c100301140036884420074841d516005100415180903c00c061004540404503010b4203801c1c10307403c102034444c0c0420303441e8010301502402c41da40501c40c2000401008540c1c00603480d8040022111400c4a0300c4e00a9032080740110003c00c04203030385100540e4144140e2800a0a1101481061005520600c41002d03018011100142081039080c003040c58401c05d0401a50035000c0131041104210080100c0c602400b0541702400b908e003491000607100d156050045008010040741091407000c51280c00c0c001031001d84809405400d040a05c0807400e115840165066410640040c440307051000c1d81542141c480d03a14040701c0c2d03034200c20f400014110b01e903045400f0380080402c01c425603190070600c0c1c0542401d450803118a082403001500844556030054001e401c050b0040015690200503900c14181c0c000c4103c0c0000c4c5031458540006e2400d0300466002c0b24003203121608107070301c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 571037059 1250 571035809 571035821
    0x1091b060801030807030e0111240906012603120a021803121b030c010908090a0f0b0d0b03150c0409151a03060a1d0a06080307051c09030c14090708040c030209040c0315 74
    0x200080209250311101603503510ce0b8000d000b12180d8000b16440c14159003500038510401d100c0c01c505490400d0284072560340c11203026102e038004190040703040a41c0c2c503807500f8111201c900440050501200c0c1d0024000b0500540b80c0c2c02681c1003031000c40c41c191260a1003103658a11001c0001c0242d0201031609844e0743d0880c058840c0030b800440c0002c100510304040801c19209400522401c0c02c40704c510140c00b81c0b0000d401c0503014019a224513180750314002200e4022141c09d0b4645403203d04103c0880c040b50517000810701b0354484202c040003940d120040704001c00003001035403035a0f41d0fa00000305424001591019020081c0080075600680c1081c46860140071102414070089550301001903070b034029140084c010b40c00c917010b08d80d591001c4481014401c4050705025050955988500a107084107901034214810240070b5103903a40362a8241552001d2030b4103100540f0304090321020030410090200900800a2002040034410f40c3c0009400642e44840c0009400304250032040c05045 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 571038309 1250 571037059 571037113
    0x103110d2a17060f150c1b060724020f0c0604020406120209270f07050a05012c010309120309061d03071e0501091b060801030807030e0111 61
    0x1800c4418500d0003031144400c0301481c0524450070707500d81c840740108131105481481e02a80600030070141c0c102401d502c8090800c2548220182c0141a1100c100c485022180303103070988100404c00003100061001e04a040b440c0c059191f01040441e5115041d100034480c940142d1007091703010481c1342c0c0e02400041c00c64807652007079409001050b43c3e0040d01c44000d09100c1c0013540018001c8c000740000e03030602e15400fa0484000c1522709040204e600d01e40c100b00000748507542070f070080c910620003820080c50b00740c0101420301c2d001c3c1ea2504806540358020031288030400e00e0144611840c10a6840780c0c004100e0550002c6070046501d00184000c0e008102e095411200f503420006103035241c0441d203d03601001e12518026501c3c10100b030f5148100d00c2181281c07556209544104100821001d01c0340203010b0b072040f40e00d01c0d12922212199003100056034450410440a13500510000d5001019a41030640c10308204c01c0e904110fa0050704e509800e401e0303206092148142c144060108001001c0c0350324 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 571039559 1250 571038309 571038371
    0x61401060924030c030f05010807081b0307210501020406030b090a14130204320a06030206040504051909051006061716020a0506100f050301090308060103110d 70
    0x40d68a004841448041d40c0740c03294002d4940000841c1c40d80281c22807860704070b85103000500d010303003c000ea20803518207801a665641c131000341808a00300822101039503032944082c2c10786902100002035079030003440c0103082100740034043d25007800101d00481151b0a038044000c2d51921b413101d400500410a0180c03a81c400d40f5460041160364230140306044045000d5804442640c0d5080c2c10360030509103464080b60440c0d559408107061451020b194500466132071503810303040481b1040702e00346200c0a48a0081d4602c1c0c01c1d000c10050b6038020031030f07040b50360030b603004601590764051401444515014250113641020141020482c0105072600002015030081023400c1c2c50705012680c807100008452220034001010034034104045260000b580082e104480c20700c10f440c1d41d0a4107200055620075015010640180503c140001450b00548815802001000c4098400600001c0e001d400705040c15a02e585112007600c4180441d0009010008180003036010009101c04000c000680744002c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 571040809 1250 571039559 571039577
    0x50f1218100210062309060a05060f090307090b040b011b151407020a0201080a02040605030c130b0c0303010905162712030207080c1c0611120103030c02010807180b031306140106 78
    0x10f10341b901b142402044040d02004016040905001c1243d1250f014107240c454140320455160354100f00c000c016040c01c03000482e55040c1c86040c04107076184104c00c0307414010314484c81d40082f0061000c100d1020780000d0740725008010741070443c0081000c844015101c841400c20000b58580020f150300500d031003a80c1d40b4a0079a43e400303209080307000c3c80c0101c03000180c0400c0803c005100c40b20241080d94040a00d0b081081d40d14100011258001c8800b0740c0b080d000440104070039011482055804024038443d15051508070740028042e0314500c508400142c04045204c1041c0d03050307901503004d4030440400034160440740c10040d540300311610032450700740320f0310560400d2800c0c54404000c0400d01c0381c86102c122442c41c1d990002501030443c070022103000510460750785100340a407a60003180a40c9441001240302e000041c0020f800410401c2401230340107800b01d40181003024a0100e40d5440e00007038a0b40c8948480100ca046080740140c04241000d0749440181c0100d60894122881c90315031003030b5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 571042059 1250 571040809 571040879
    0x5030a08010e0601050702041104051915090e0610171f1203020a290c040312140406210e011d0708030f0a1b050f121810021006 56
    0x2c802080700e82c9400104140708000040c02c0541022284950214000d800c082c0c5440204201c07011070b0040c910440683d0750304210283c7e0138042d1110391000b034903000150038200400c12207585006000c03a4061680781e4070310060140309100701000b48a1051840700c690400c1c4180c0301107810440000490310741c0400b000980c00c220322042d0568640c0c1900074120000682c4c4030070385024078502c0d9031b40c200c0b108040084803d4018004540c403840d038840d009074665046007081d200034040881140280f09c10480d030b1070246604081070b103003224894a4021507070410045003880c0f210b1811040c125190415441089841047d0031556681103202c583c2c040140e038178001550b0b222413070706c60490a90410090a0349021300700d001445800c03c642030201c0000c0300703015070f03000c030301d4a1680c161761070b4015003008132010909000c4010840444200c180c24440c415044800300c603400700e070b1540f0070418085a034031054001d2014600c442400350301045401d0b62103c00034440000c01c1400d8054448a02070410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 571043165 1106 571042059 571042079
    0x30c012f1606020604030e0f0a030206120f0c2106010516060c180506160f020a030f030e04020a02031c0e01020a02010920030d1d0d05030a0801 63
    0xc40c1d07103000444a044044640c0104085420900900020a038000b0014001c04c5d41100c0040380d0081c00307c00181c04000550000390001d8011a40044411011189500c258582020012a641c907202040040d2003034178080102c0310300c143d9031035498505900307205511880604001c0e08d40103003003800707002041009101702d4049449030620101180d0000c8a14801c03e00d0720f007040004c82c107100001d00c41e40105020401c0f035601c41c04071003041c04018100c28900ca40c0160803015902d1b00c1e41441c580b8103030203c07405d03030214070520710504090400e40300321240840c03217601035402c2900a029100070810302c8114a130059450b9071018410030020b1004004003034654000140c2e4011745d1802021340b00c110351440c4e011100b41070f1f0461041e10f000c01c40943c2c41d82e45140c020703000d2100d000c4201030150b40d410400d4100105d00e4000081080000c0103056014480d01c030300c45142c2c0c1e01c2d00004 = true := by decide +kernel

theorem cover : BRFrame.Cov 570863309 571043165 := by
  have h0 := BRFrame.cov_init 570863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 570863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 570863309 ≤ n) (h2 : n < 571043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
