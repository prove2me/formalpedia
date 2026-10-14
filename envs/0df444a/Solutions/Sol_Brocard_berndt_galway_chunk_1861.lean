-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1861
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:56:31.011753+00:00
-- url     : https://prove2.me/submissions/6e1148f7-55bb-43f8-97e2-05bee1b24226

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 334532374 ≤ n < 334712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 334533624 1250 334532374 334532381
    0x1e030603230105070507080f2b0b030d051c0507090b07030206010e0a061202040914030705030304021203040f0b0703030f020415021005100e04060b0301020f18180f19 73
    0x2048907001c216940440003415085640c0a42600c0c1030140030310544001841c800200c0c1c0c0004008220b054842040c00c1c0c115064131440c0d8060b60552441c203e0200e2401001e0744044101e5204600722001105078420a0b40d00303101d544203840020802c410110701060342074000c00d800685074a8031400355551000c5282c6c90390824001100141c0098004000c080411001c10350071204101080042c540b80c140145540c0d00c103174074000d00581e00d4041c0031f002d10140c8080454050308141c1a00da032000360f072500588a40c002c65003244114110301040052140000980f01510003899a5401c51400c0c03014007405504100411400c058070360200b4181c0740c0382d40c000381000f13011006540100c101818000b07400e11091509840d050b0f4542800c00540031801b1054a0444005000d9003c03562228100030300074001d21040c06030950f00001e540c11501510340014808000780b4810076a158642c10200460030f0841000820039404407400f1900c0000381c480c0168202c50300c180b0651540e0310420100055 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 334534874 1250 334533624 334533653
    0xa090e1c09091b0c0b10171f05010e0f09030904020d090b07020f0d051c0203010609030c15050316020f0109080301150516061d06151804031e030603 65
    0x5400584100101e000501403021441d0300c82110708490101c00800500400b18020064440b40c0300c50085481d00000c19003260203031105060340442c0d18040401142c0d940c0a04200d450f502140c0c0c0002c050102c004e204250585498be00107038581d40312006681001040640480c807503000030000309030284da491000b403019084030a404140c5d0f44280c204144060f41c000c08600c00d5400c9004880815071000c90801c0841c1030504217151118100c500f8070700380d08201210180038502c00400811132a403c51f0300c070801c40348034400e081e803156200d06028203007000c009034047c0803903420300110703a40600d0048003140643e86441141c14114500c11440e00b552019401078502d024008010701c00d0020032206404000410309180c0e24254003055200006c221544024101035580c000c00038421100401072405060078904542060500b50b00002d1604ca00d000381921071400d2540104ea401d262120b074911454040d1281c001400041143c0c020700d030b030a203907108109030f40c800022000654201d805c103003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 334536124 1250 334534874 334534877
    0xf0b04053106030b0f090604060c11010501090e060c1603050304030c1a010504050610140304240506030d0801031e06020d0c05180f0904030c151107031206050a090e1c 73
    0x508500c0c60400c1390b01000060820b80103880c48108000d11101c00040a41d00310394032842c00a00121148030446403111081e503000304070f500304400012035100941041c002c2c1e100002c140e5809031a1440840300c58402c1402c0c0c0800300100766140c2001c0781c0520080c580c824041d043c8155811540ea40c4c0c01e4910f00000340e034a00044004006000b43c4c1014403400b940204203460301c00f600041d80c5070151102e0240340602c45420000000201041131205119982c840ca0028000071225001601c0d03001c1c0204862180c00303840303450440f05500e071180d94400d0407660401900d80300f90840c040070601004948400303585068003040404401400b91003003500700794140e80c826854100500c8850b030501c1401c40841c0c4550150b1040601950301d640c5100d030010341c1810450075400c081d01e4080ea600d0360400c141c0701034521b892401820403505400415a20344a03030303220740800c45120150300c00c0b28510700a85030096100c00b01403085071010350024118000010803540c1300c100310412000005040c41c8900e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 334537374 1250 334536124 334536131
    0x30706091202010f05060a03110d080a021f050408041203110610090b0f010219030306081e010c020f060604020901030609060f05190b0a0e1906050a090f0b040531 71
    0x4140303030b0a00c02c02c0d9589030301040500c1682000c4002403c030f059540805400c0c0244182c01040c07990780e1031002132009500500c100c3d203990700f581c000ba4940032600580701c0300c2d891100e200313005010b10b0300c1200d1085921a46117406e0504201d007807480201c1c01001141840101d00011941d40c0c030401500703225103507102d2181da215083c1040d5030151a04030750243d0140c00c14920781c0010380c0e0003040c041504103c0380c16a5040510606049010703007031135480041a40107140354600d164107000392680c4887c1100c802400b4010341d21744105d03501c1c0b0b1190568113194210901050640c074060700100640101407501280b543d40b103400c4041150510b91103441c21914140c0104278505107614041a002a440720180c0b82c0c510344090510107200b0180350908001000540c0c10031a524000000283c0344000040074041d911114064201d5122078004400300d40c130020005140e00c501c015500c21f950140c56840d040c2490b100a01051842a0015030203030074015500c5511440900302d0340d058101500d6011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 334538624 1250 334537374 334537403
    0x90c09010e090c030102090906040507120e010b01030e0a2315010e06030d08040f020108040804030b04050105060910030c15021c0306061725051c0615081b03070203070609 75
    0x2c500d000340c0520000d000b640180020740c0140e0b20740c070282da4041c2050310041034070340e2a05012915400c952091039141842e20324154030014056000e90442c107000c0c0c9040000c0460f8030741a03a9a15901ca03001813070004042005200d0200b01e0f83e5089101651703604403442d12400e4201200c421109030441032003190350b0001c000140c5800c01545842c8401424500302a0515403038900034042d2044c4081d05116042d008071b800c01c5203540440e0010f54120030007600f141444d20b845406400140c034500e2003142880b0200b041840300c401403400300e0b503200c075090701c80c3c40c80d14120140d9844080705980a6004e21581c1c564140001c42d2858034480d030030382c0c002403a039003422400303892186040d40c981d403000c0500081098030300c4002545000030349030150680b11090508401c4503903206041140002c2c0c0c0d00070326481180c008941120064803241c80241025143c4854102c40d0702c00b00300e46261014204040110284d00e04400a40e00080c2c244190f038034000c03041d15180c0030b40e0304610f0116280d80405940 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 334539874 1250 334538624 334538641
    0xb011d0f0f0307270203041a0c07020418060614130e0712051005013002030c0307090e07050f0d0b0405070302031e0c01020c01050405040b0103021b03070c1205070e090c09010e 77
    0xc800d401303840100441c25401c00c0d441790880d54400078421041d5094050101e80c58400032001d4404c2140d0003001801920103184400140300341c1450304451480c10302c000031601e0101c800214451590150007401e0b9191410444030107016008001801c5018140000c21042d0854481c0c03040b141c0281c00501500244007400d500300c81c07050f88242c28160200a910b000d09103110b018104484114503090f0001c0102e00000341448004c07215103070325106a20000610030301540280d80c0400354042540e1040d44e5580500107860f10014459501a020075903d60005214854507034200340950200c0c6d50311512540400d28010b071101000201d6503d070880032030020020800e8480d03410082c030203402506400c9002070142d0040c0e00485205503241e103403c0f1030036480303a4156298400a086104407003d07610600039100d274440e64099506d4034040b00c022541940c0fa0314181b003425030180040400c242381c480e03020042072001e41911210700070600101d02e6075480010841c00f91008549001141c1041e200c1c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 334541124 1250 334539874 334539929
    0x903020c090a02030411060912010501080d03060f030803010b0322061505010e01090b0318030d021b03041a03040f020910081b0d140102040b0705010903030b011d0f0f0307 75
    0x8010b03020700410030000042c040c0d1001042d000001d80e103590b2552a84000140c21300316011101d840340d8a40307000003030100000180030850100507107042210380d49404020327501d0440741c00090b010030400c00040003540001700c02180e100d03c00070050011961a0a0042d20003020014291174917511003480315200c0041108e144010304003403c0058070099440f0000c3c050f12101d1203545c0c2030720400700004601405145001d020f20707421301e09517603039007d0004818000350085c0c12150a0203184004c07900c4400300000485080e40c00d0384000c0040c44403028003030312542e407004104035160300700c0c00841d0340180c5400c0c240c0303030140080d81c8135001000e041c0403030700e807030800203075044440c540e4185500744690700d80341d0b080301d580d81c3c0181e07042c2001036a804000c0e019125580c0607140502c000035855003403180644c4034180d1a4820758080c404552124011241240200c840303103141e043c008140e03015440c01c0c242049914402802100d805110480028180810390f440402c0e255480301c0001c03c0c001c48240e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 334542374 1250 334541124 334541131
    0x204171506120c090c0d0c0206010306060b0f0f0a0302070c03230102040b0702010518220c0503071b2d0303050105060c0a0209090f06012303010e03190c0203010903020c09 75
    0x250840301d08102410150b0f910350f40301c2240b03400b40700054042030000c0e0485c411611400d04c109024807100e0310403800203503504000d200c1924407519100c00803c04070120401c5411400d4070440040c20030445440c080c080781e00203014070003419170030040f0b180024452604440194000d02d5071010146010114161b1140ca140e041080b40e4410002404400d908809030340b04640c083c41e205403181010900310b045104e00403122030b130080801c0192880d0001c0302940800e000d1070007506010303076103e2000588460005441c80ba0208464079810302000200d046510318541c0a680f401c480741c2403000c0c03803604000124548101a0620201d00b20a26426014080c01407034142c8620340307400000e1803d903864a150510080c82411410b012411080003040075440e01c41c031a105490306540c1d0b407904074401c85000160f100d804200c0c022040036a103018401c070311700054201c02540c50300e0310501c45070162201516200c030510650304075007005a1001d114a04900b440394005007030a08d06001040300a0b28001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 334543624 1250 334542374 334542379
    0x112030f031b030f090c120c1a1c0f0903030605120303010e0a020915030a14090303071709031b0c01090506070c33181a09060702040204171506 63
    0x100c49a00b00008041c110b40ca6500289030000382e2030014241200a84191a00a071090a0100c00030843d10070107043d840c000f074850010396410a54405450305195000f0544d102155010300c50100414442410301898104038000001c0d518201ea01c503404844c0c0100050b00000c2e501c010500941c01c02c00c0c480800703800041c00450941d8507003507100340150780c000e00402c041ea401003041806c41d190f100c1100402c0c07401c03001c00b03038a907e41480100001e0201c030045032059070f40003003c1000040e01000301c9000701c0c0207580322092031003807550082c100d54024201d090284010849030b40f00308070100c2d00040a012000103050b03416401c900041c20348845420444c801c1c5404c010a07800a2a6810140c0840b20020003e003002035540035190300300d8208041e011000ea20070940d0a4400e5408000d62035100c2c3c061042600098070381c01c000c0c403101c4822581c01c010f070000f00107407640c0d4580480a426441e1008102600c4e2540703400310981e403018500b0340b51030564000000c2c0c40c0c480031420011580700105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 334544874 1250 334543624 334543631
    0x140103021003110708071b060302090a1508040303090507050312030a0c030e1504050703021804021e010c0f0c0801060b04151806030203131e03031103070f080702150112030f03 77
    0x2965003100f0300d21a500008000300c000050400800c92494501a8947c001c0c1e000310102c15660300e800390280d48000c3c615803085d0f00301c00b004603106d614076101c884102c2c80c40e034071031170036540c0c030743d4141c009001c540070590305442010800112a0740400c5142d50714021060116240d080201106c81511015008142818106400821010000509540c001d500020740cfc4003140c40700d051030b42c1080c049410294001d015140002d104484400d0114042d600c241c0340a120313201c0d2541d075109182000b0314030034001401c1c0090b00002c0f9003808050346c51640035001d481034071a07a0f070907124210ba00f280d0264000e8100810104900d000c074a0084441d40001c5c01c06004100c8881c644840701c0c80c46000e078005156001c0003099801c03500b40f016601c119407110003400c820744a1043c0b8a013150711a04e0490000b8102000d40074101e07144010340e802240c480e207a00400d8422000150b600c0c01d0010410000c40c810f294039003402d40c4040d0302d028006c00010301c00c0c1050703c2c00b1341001040902015480300c00d2604 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 334546124 1250 334544874 334544891
    0xc030501050a03241107140d091410020102090402030a05090f0604020d0b070c06060906080c0d110607050f0a062c15190f0b09011e060e01050c01140103021003 70
    0x2440e110f08101480351484483c103882c1020350040080001440d8891007645c085054002c21044c4405000081200408c80c2c2030001200c504541c100f65500810001070000b050125090a16403004601e002003400050b00b030030070040c086002c03600111414841aa00c6605010340c103403051010183ca450398102518180c0b034a034012039400c0500810081c012503900000556680c407c802a0b030049901c000103100c080e54465243e0050f102c0740c014070f0054020700045010b07500d4400140b01046602c803042c50031303150350241003203c150070207007080d1074a02905040d000b81880c144440300f04213100d440b001440e0005900b000c0703040315801d010074482034030b91442c11215260008a0510301c0180c881e80c0c54456552506050340d0080524402c110030381060003d200700c250742d03000b5400115090f00d42c084141e0b46c1d2707801c6003030fa5141080392085c540c0300200c060100e02d104101e0011400d806043c80c40c580041280c44078211004903608080015129005200310b290185c41e007942020145020b005112 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 334547374 1250 334546124 334546133
    0x901050915010804060b120d0806040204060903060f0605190305100b01080406110c0a030806040b0604030f03140708030108030903010c050c1e160608040c06020105070c060b040615030c030501050a03 87
    0x48000c0c1c00d0350b060102d1070002070104a440d4114210b10800075081840100620461598603024400001d02142c050300c000b6049041c148240e40031030389039a842801043ca162103e030003d00301d601c4241c00440d12401d01144503100c2005200c0740201c40b00c0ca89031382900d1401d00f103051004540a807080c0a080119221251381c1c441c1815070090b802201c000303000345020302c08510074880c0c0864030b032050140c25500703001e02da0800442c030700c6400d003620b0070301c0104c0c0300e2410030102d44114000141461401c105100100e841140c900c01c1e100c1000e604545044400d8540c074003103030800da2211081350702c0041e801c03940381002c0c000c9000c0d01405007000c82c20b003048c0b140b0460f1141104c0d48800c580c2c10002416520054040000260321401d00254640e940c0d2500d0008108040c00c807401d481394001c80400150240c4140308151160000790b41c0e0034034104544d500c0d4805441c403038101640c41621403001040012101d0600c8100e080c0603240040c0320003000d4000b50690308142d000b0f078440c0c0750420003000441c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 334548624 1250 334547374 334547401
    0xc0906070317330a091a03060f06031c11150a15050f12100e012c0712020f04060801050703060b090a0902160b0c0307111615032909010509 61
    0x48100c016200401c1e8081c001c22404c0225500c80c0000e00d007080a001e004044203c0d5241b24908290140d40041d0380701030701c0c10a1203505440d40c42d099070018410390b0b030415461a8000150556140c0308030384a0604418524101d1015a01c200c0150640d042c021010024858400a4015410210030813407030000062221103440301918001e10120b9004a000981840305c001d140110300400c21001c43d940450500901200c910b9005030760b08851444a6420300d00156221450140c004000b9030f8100611070342c062015842c101d8003c5640714800e001039541d401520041c140b01c40c00090300d07180100780101540ca040e4450b624107042080200d2494842d84410815144040e8025071f84d10403005440143d07036420b0201501d4090303448280f12400806c60004c3d8001d001659402d0701c0d48509981d4a0b4580301c00d502c120b0f8009181400030444900c1445140c44c4000b9030342000503010050005440c07041113006a03100c00c01c08080711120642c505441003c0c05402e065035441a41d203480303440720300b1300e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 334549874 1250 334548624 334548691
    0x60e01020c15071506050103201611030105070f180f0e1302060408010204030203160608070e030f0115051008090d0e030a140309040e0105060d0b0c0906070317 70
    0x48400700390300303000c60034490120f40c18075900c500400c0011075800408030040905020300750000c0e003049448050b454110b036155546051010700e851410400303c0074048132220031001202d14030584846140503640a120f075030300c50b054903200c44190007005030008000e03020003841180070a01e0403500b03100000750f0b00641400d8a0342d400c906090354880302010211070794041030095004100180205602d54190054400c90784258210303041440040e6101c50584003d001e030348001080300000a1031944100c40780303011000050150782e207c103440d806440c2134580d10f44250000f55400380c4100118184402ea084a02c2501d00e00501c0904101c0711007501c0d41c5031524042d04110400360046150350b024080e1031103490b80194080001c80c0e081c0c0b442510390f00701c08509031140d854400624131014040c0a618071031040289500f24008181d5182540c001d00a4100103d40106101189070b40c2c641c10010011a4069103400c14000c0303140c0044800c1d040e00404031491000070005054012035101c107560315 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 334551124 1250 334549874 334549879
    0x7171b0703080403270e13050a211713141015080106032a0b0a09030b0603010e190f0611030405160b07020607060b0d081803070b07030c030c05030a03060e01060e01020c 74
    0xc26444549003120701c0e10b40d212003c4c0150040b2805d403030420580c0c407904404ac910965203480381043c554001c1d11b00e12802c0f05c24400c007042590000c0e05040440120344603403031190201040034a000542c191501c844088072107116a95000d40b20704462840003a0b00081011000038030605045680d43d1070080900038403c0b0200c0c2c4d95220041241074150711440c0a0003500380c0b130750b4503540d580c00300030304840340c620041c0d0700b2495100119456003818050020b600940500a1540c5102440c040c201000b031b41d181902c0d803004030790040000030283e0040c1c440d15803010032859200c0c00d0908100d800c00b00c0c2c1840300c80d51412811400c10a46a038013054a038942e030126501034032030341c1c5418900098442d5100c000d910149100181080280c140c3c0034041c0c503640030031503d9401ca10b001c285641e81c4618007904003000b0091000c1c600003841031400c000714520901d40005e5041c495130301e0394550340140c61800b002c00d444003428030484001c00007040c010070640c90203040b00c0f2120f000103521014046041d60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 334552374 1250 334551124 334551149
    0x70611071215060329161107090207030f1412010302060d060e010f030b180604030e04021902070305010c09050f06030a02070b01080d021011030610180914090607171b070308040327 79
    0x12195001480323800d00500d01c9031800d43d940da15600e0004c2c100b200c0030800d04003140c84140b028510111000a035200102c580034142e549908640030015907030010705003020401d07101c4c600801c40840c204121402004106034480010741945400504194000d10700200340384a0760b105040e03c1000140150855014100803083c03903400c0001c14068030440b03801ca1032800c5a0603680001c2a40007034a0300c00c03a0b01890080003848544241100c1c43c500c0b134495181d1103a0ba21951202501e404d000071600030300200001413808040d941c481d4070b0028240e1207002141c2050403240d50007a0144540702036401404010001c07400e2030358080905000c05403ca60007613240c410b04d0560140520143c00c5d540c600a28442142036480919001a10881d114110703091007160201e4407108000442a000e8a0140ca8000d100f0300c44c0c2103c0003013102c00415104400e0300784000b03080e0000e89800206411402681d500d50603240c2414040c0407501201c0c149160072103482ca005007441c40156541040e201c5450175070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 334553624 1250 334552374 334552397
    0x3040905060d08070b1602030f120603030903010c09090e1603060923072420010908120109050f01050114070507050303040806070207061107121506032916 68
    0x209002e0401c20014609080000d600003440220b040180c842c4522409003005030400140c00c81e00d82c000c100403003103000c40c1481090000901d00b6030b02d5a06c148050126070800b4000000203080d16050300c69000810400079060020114502400c0e1004200c0802802880a07501c180c0c5680d061505c40030306030503610380c0030404104d0301718007540150410302c800004010028205641300d039828821111105d0103c2d555043d55582e61b050240711002c541c4a003240c035400c41d100e42800e0f180d44481e60181d1b5681e0300300000015000c40240113500103c00f01500f45604010031201218009807a43c4000d669400040100fa1b0340080041c59800080400640301c81c03441c64082d140040a402c8280e15002c0483c0c045550003001510031320449507542121603c03a52501e040e50880112a4543c0e020341090505000c1210080300f814580ca02c1158103900301c0f4280000e1200301d0b00a41c10485103081d141c030140b51003403074010004004120050950410b4104a60020002e205000c40c8a00340001c51101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 334554874 1250 334553624 334553629
    0x30a0b0a09050a0b06010f030b100f052503030b01030b031f020706112115010f050f030a0906061d1504060308030702030306100908030a0e03072c06040e0304090506 72
    0x20244840c2d0007003c403030b4129182c0c940450f4140c0225001400a82001c0341d0300c0c5501d11a00802c03654400140489410f40061036080340d0417030406a10009001c410880201c00e04001c40000d15014940b01d0092140180c1380b0300101522405290241050304040c1c100c1240d9501080d014442000310070445204180d080e0020041e0060350f402034000791610003041940040311000713003c0c0211412102e400390795492200300c4072210607100c1c1612640c03c02d41d44441940285079045080085042850030200c00480c51041584100d803c00700094640f183c001c108143c0b4054075000d441c204425507003544080e08016040720b001095480251401840e60010344c0703a030351050002d03541118444e6500d180114000c0c0d80c9900a03550540919007070301c01042aa445541c0c1c403026038240c100510702e17010004c0c404403400c0344506040c560500070700d1070004052101d00ea0491070400d40c0c0f010401801700300121181808402041a0702440c2000c228410381301002c0708075001d60312032945c0015291a41d801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 334556124 1250 334554874 334554881
    0x80c010315090f02040302090c070c0605030c07020a1401020601060e010e060d060e01030f14010903051812070602150a090c0314010b0d060204051f0206131401020327010902030a0b0a 80
    0x20400074600f1000041e1180150000d1040c0e034001d84003c03080d51118101740d0090b120709800581004200103086c0b04040c864002103402c82d00c40c00886003008082d0f000100f00b00c400b039200c1018004001010380a650f018000c10740103003514100215460060f80005e0304101c6001496071040500151030410642c1940c0400c000c2c20301c0700c031201041e40c0c581c03078480c0030255801000c1d26280c2f46007034414507242e01405002000399050f40d0707040c01c03d031003201e10241081c100035001d9272103105000803c0c8440001c000a1005102076802818600c4110050700e842840c0500707440c4140381050746000c08a5118800c00003225800f5540c1001c0d91b110204842c01050410311560784507041d0101642442066005807003511022580d0800300c0008854160301e40100302c0c42c410142e00300200003030003010021010000301e801405840c100e0310481d50842e007240d01c00c07280c070103180031000942209402c0038492820000c08143c000c00000540d500000e030368112110004100c01c034003000060340c2000581 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 334557374 1250 334556124 334556129
    0xc02060c010f1e020f0f03090109050a061b17060d031404030c030303050f10090203091e0312090321070c05011e051f15020a150603110901080c010315 66
    0x20000c01a4145003640a0701815041d03000620380e4140c101801c0000080d4404c0b40e4030b45c2d01c0c8030000d500d01010041c1030b1046401c000c141d04c3c1203540c0c611840000c140709000b0b00002034400c0c0b10018100c0192088024881041d80008040201501c6091500400c00c48a5030304000200c43c3c00507881450301c1c0450700c0c00d281081d03080d0003850100b00003080200103242a01640c1c0301e80ca042c032480c2d4490841c8844004215000d8810200c01041004403c816030300958020395a50141c4512058030202c0c10000707250b800e84224107600008100c00d1003200008941d400c072904001a51614520380718090008541280400507645c241d80411500ca0080c5805a03056a00c24000d201c10032100d04c0b0408000c00c50a9110aa5420b110001d01c00b0070564509050391098440d0400b420f504022260b18111840b03008003042d48140d60201b40820005000440c80d41d020300c0c40401c00a0851400301004006074005a00444401006000c001004182c60f9500c6c03600303203000034011740b07008100f1807007152a9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 334558624 1250 334557374 334557397
    0x60b12090f0a0803040201020d080c07060903030b1008090d030c0f1107030209010806040c0504060b0a050f0405062818091e0c0207090b18070f11030f030702150f01060c0206 76
    0x100b40d0810042000d0141d44500d00076001e6405502c05000e0a03225048129216804914104003450010f8401c4d4010310559001c0d00e000191310461401080d50540c0340c3d81100042000340007042030040041003010780c0841b40f450240003544160078050408000c024481c024801140c0e2424101074080000e5030095400525140d50380d40e450359003a480c0e44054609641040001c81d010401d070805000b8141210340c1c91203524505802d40000300d49980000701c0010b44010104030016481c3d031810060055010015000f101c4e40c0c6220400400d89002c0c119a0400d00001d1041220a0303500b00d41410200ca8005101282200c100c1c150b40141500103922080c44a00d09000d620f0031340d9001441a090340c010307400800020b204403040200d05540c0081d090030310302403040051009407013048480c0018495061202003042d0003040d02d42503400001d011211507a0200400c08180d604000c02004110005500b003290b0520000001c500141401403074284031081c0b03500790454132658100c80400445 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 334559874 1250 334558624 334558633
    0x30f120f031f06030507030f050f160909060305030a11070605030a05090102070b04080901110a12030209130204091a010e0a0b0f160515010e1012020607060c02160801060b12090f 78
    0x15100c0240041001b681c10000280c0360890300c50181c529840b4480c0a0f4144455100c829a80c3d40080720505000004030810061000d00010303015015005030005144200c024684a030302c810070081101040900300a040c0e0b200000c1040203540150842c1d41041e00310b00013050039921752105038007900c00d0709401804580c14a0800090105050142c45030031400d0740e88000c071405038040c0a6842d0b002050103031071304102e01d2184600600030340c01003d14480c0030740a00410702a4401c10300480c0c00035072050914684130410040e01c509a041c000c0304200702428070600f4400040c02244c0e02071014082c0003503e00c40051484180a0050162844100c2640350100078628078580aa1180d1552001202000030a400801c078401d800406a218500030380d108040c080c5042010000b0b83d40440c401da1b0080801c0240b20081075190154101c965140d0300140810042c5000390640203805506c1030340d80b030b4503180b401d01030124910100c407040e61481d00c2e0b4000d0780d20340140070390030300180360301d0403909108 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 334561124 1250 334559874 334559879
    0xd0219260a0923030c04020703021501080f0105010902040b070b090111040807080706030e06160e040609290102070b03150319060e0703170c120406050405030f120f031f 74
    0x1440401d40c1c060759200c1e1144000300c00d240340072501540110404944c1a00b1840c0500300609007503001d8000603002e8811a4140003074074044a002003030a07040b0300d5654000d0085010340358000d005803030060072212011071a00d807074407140b19110b0240702d00003800c0700c4204011400d4060701750041183d061104540980e1036988044c01c65881a05101e1a140c03030144140001c0c0c00e82c040d20644c0c03003a280d0400900583e07550b0503c940c10a040d00c0000c075040c440000715025842e15070340306210141060080004484071400e6000369480046a4868400e4901c002c458030316076070200782c00c1b0848450342135003a160f0711403402d01c1e2586521041070799050322131501001d189d208030518180403940514810402120003800c1141c441c04140806070150140012140c94820340400502c2e010f0b800c542070303546003c3c540d40c0b0b28486500079440540000d40c04501030040d8507060007244010201c0d10000c0026982301c01a800e42405041c0094400c01000300018141e42c41c244654007440a915620794140c0c0e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 334562374 1250 334561124 334561127
    0x7050f06090f012016151a010806033f0a050403170705030405120c031b1903050c060f0403050a08040317120a02090a09060b0c0d0219260a 61
    0x804030003410360b42c0d801c12031031031800c1e803449200c070f2400104148198545004141d4240f04c032121620b045913202e1481e881d10f1180001d52003240d41c14034040408001411078100018107a40c0b020704880d01c00e4120540b0800301072100c000f410a0365049903881310340c841183d0030344081c007040c01890900c100c3c3c00003050750b1401d034400000c00907a481400155400d8130714006070b11a40c0101c4000404542c400c20040c08149443c551015402001000319403c0c0c0507888042418403000b64040003a060200c0600d0066161851001c2110140d06a80022091968541c16074404201c0500f5010b5200001d43d11000261841110059a01b040864060307000519000031260f001c0c0c0300076180041001e1a03120006401000c5564050341d034490100903031507230800c80e402540101481940803202840008518042d4000c040007482e02c203845e00d80b920b800c00441801c00c11000300a40840d00050494610000d0512086440681007285c40ca90003c0a058100c50722148010144091102003204070006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 334563624 1250 334562374 334562383
    0x206070b07080c04140108040f061b14070b01030f05250e10060206041506090e030903060c13181116030e040b0307050402030901060b03010605070c270207050f0609 72
    0x260890359401100741c1d60600d43d0045406603024002c40d5030020500203803250311541040c3c4d000f074050050090b4400181e070750603048454181c0f0200c00f503a00710a80b0555107801c03603042035010101201d01407a00105a5540800b07a03814040203082114036604042400030800c01341c1d203090803a1000461407450034101109202240c0b007408270301c4006070001501c0d05124081d00e811034000c2d03002003442e611a0399401e0301c44e0000016a01c4e06a0f42c40d0340015441d0481c0c0074507504000300ba070103180c0e1780090609041c2408402004d01824070010452200c0440005401d042200c0c0d0b481402c0300d941c0940320310b40001c1c100600d1804280007004c02c030891580d0803030514402c13961098462000083e0048240070903100c1c094a4903038140c00c00c000820050070079070011644038101800004649848a1100b1800e80007a04154005200820400204196215604050410300f40082e411a1010b5171070b0303940b5140000344d0181c031a00841c04508001c2d04020031410b07800100b058841c986011801995103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 334564874 1250 334563624 334563631
    0x7090b0405120a2a050307050105030f1503011e05131110030209040f0b010206060102070807060e06040b1912140109020703050c01090b16080606090f13140604060e060906010f03090206070b 83
    0xc13503040000044529001032040c1c100d0310181c56050841d40c4100480055420040c0341c00e900410f00c40c426011550207214149044105860640402402034500000ca85c3c0c003c10507544141a001540301007001c442c10312500709070858082c280711102c1c0100300d002c1c0c00f890107074541003400c00160052040c2c56402c8503140910030790843d2125a985401240d17904030300d2103201c41c6074000348020300001c1e1141105078400040608450316250356220003c031a6440345c03220a03070225403000804400e5a201c2c00108020f0064a400d200300610303c0307040802c420040c406e038100580e000400c01c0c1014001e000341e0707440d070040400800c12110035060000c00f0788022916881841c1544100211280c020040075000c1c00d00a40307954140400c030f4040c0804a51030400d1560f01070f6401025200340c0c02d2038020003094501705850fa41d00d81c2010340510003500e146811010f24200d6101c00c0200325200c0f0800340c0d80c40707102407a00f982405003010080c1d0091a0b10040650010800500f0328144184510420300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 334566124 1250 334564874 334564943
    0x26120a06030611030426090306010b130b071a06010309060e150601020d1704030908030406020106080c010e031908040b0c06090d03060e0c07050106120f060507090b0405120a 76
    0x21510320800b42d000501c003c907002001d4022410461b81442c1041c50403200314288681801c1c54041030310b00080c03404600360f0000460640001e4400328070150201c61a0080907640d006600b0120641d071002c921408003403102c0c43c0c522440000400c04ea21a81041c0f50b8150000030401c104810620280d48514401d144e100104000402043c2d043d48002908000400c4542c1c07107039403031485080c0c0d020140034060000d07010010400c1000c100d00000340024001003000741c000007800b601e801003080c10502103240c02410300a03180680c44640e1000300c0d581c1b1010481504c156176881151908003c0d602460b00301d080640070104280c005640c0024441d4051315004045410b0303101c050320b0440c2035442c075001c0c414130080b043e0b01003501c0c00001000f420807503101d00d00104500d82c84e02040801544501030944400545a4515040c06007e11401d81c2201d801d140009185040482c92525803290344034050145c0c076003004942d600341d814080300081c4d5a00880310b2035030144190021140c014003951410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 334567374 1250 334566124 334566131
    0xf09050f07061b021c05060f10080619020304020a08070801061a0a050a0c03020a0f11090f01140613050a030b0f13050a1415010905160201060326120a060306 69
    0x30740b80e4040c2d01c490344510901e0062075140350442d800e00c9034035083d80600d078412014081401e00000d1040c40010700c0b480704807002d02080c1c6055401c2810802082e44880c005422080502482004688425010b0800d84030096a00d4803144081011030f49540d10a50a0780108880410607610640000c1c0880b0303010b4020201c86500408000100e01c50150504040341e020820303500313401e0092550600c083e000b40190380c081612a02c032441d50142d80001210000302450f44200603103080c2c49410b070850852003c0c04640e41c1800850385038001304a400b944544804501c292113a440c02d150b040240c10050304c0340860513074a207042401083c05640301c02c06142070000090070318080c030728040c0302c003600500140441e000b55282c012042d0a5210188086d0040d419000d29505018400e5802840c1598001565261415040304400e000210010459040070010008a01c40c1d41d5800d030a00050380300400546074210650496104404d03070320351101e890104200c00c44c03405030300c03407011a801a082030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 334568624 1250 334567374 334567379
    0xc0806161704060b0a08030a12050c0a0f08131e26090f210a150e060a0f0605091807120308040605070e130e1603150b01030f09050f07 59
    0x162551512080d14840d12000c070000580400c01e990031950612001030050784509071540c0481d400c0d07500090034600400c04000d10440f90280c6482000c4c1d00c80180060241405000f80d8020800c503c10f0b4038a4040200007800b042110b0000c00390500b1050f0300103c5205500511503070080c00c0381d140310f0f0907204009202210b00e00103a021900f850729070035403520340e440e100e0080b00700108203c10810341d41d00013070010401d46601c0301c0107005002c01c070380b070300c0040c18848042c0c98140d184c0c655440c5186202401c1040382007a90100280c140d400c114441d0700031841c0b0720602c4d2010000d05569220390360000c0c003002840440d61450642c144602c51410a48003201d48034003031407000d10303058240140002d01c19030010b0081000ea920440e0440300c2840d00d402e080c0c8111001840540ea903503009540e4559840345030a07941410800b00c01d64890548034201031a103036407581d00a0340c1040403100c16240d225860f01c9516886a4809044521088020015070a090410591743c070729100c1c94158910403420003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 334569874 1250 334568624 334568627
    0x414030606090103030f052107020c15090a06030f0906090308090708120315030c3105010b0304200d03030204031101080412030906020f04032f0303030f04050a0c080616 74
    0x140da040e00e40540b5000060009854107d82c030b580710060300100c4100c4a2900700b4013040c003a08050241015a00400d900581102049a00e0a004a604050308004c00c00c82c20f0710744030311003c0812100756050004010a4428018016000e00c1e42c006202619109204c010960000c0b03103d4010703040c01c4110341d100c50329160101c4ea204031322442c044d914001800092007841c1c180d00c02084100025066444229094002c21045204c2464040442020044041c50705400c080c03000313070302c142c2440d041c000c42d40b60006040da0f911000d8809040340181c0d208102c101824507160803103000c0c002c0c08c03191a40c90513090090094015000481341c65161617860555588991101400380e50410381c81c0c5524020a03500b50f00800040030100d5041d03409001c0c00d46804001800b1700002e500032070b2142403a503031441004c3c0d815010f407003100c038002d41000c641d003135030782c80010940381d0100c040c030500101da88441c1056840c00d83c42c1e260050610140b5103002c00c0d412001314403280075002001c002e4181030b2190a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 334571124 1250 334569874 334569889
    0x902070b0a06080a0f02030f060106110d02060f0a05130b040803040311010b0109062a06090c06080103110607110913031b050307110f1503040507050105161104020f0414030606 77
    0x4035015980132031218004281c03250182d2a51510080494a02101545115080c80d500761321200101e40c02c0c0d403001c40c50060a0188040714405031000c3e240350300e00302c0d400c80d400c0c04003c2c1801502c80e42d1900058103104010b80c9144031550010000034203403400d45031140c000c3c2d008a804034005041881d0034040c04805006104800d80b05868410701d4a04004d400ca4a0b440c0c84066141540d85014411503111400106110510700036a004550b0802d5400e01c2c0c07283d017071590b2006c0b0420064100410103d00ba6840c1caa0404a00320740d60341d41d424417400c03d41c2040c40603160f25a0f214076500180080381c3d40810744580e00510079111112000400520034144180400d4040c107290020009440000e15006600010000007440350080c030706420301041480007003030785807404000000103210900000b040008020002485c2c003d24144e130140b091021901034040c01005030b1980b4040c40b040369113a030103580196124692503501d43e5a02c00b8074a0780300071f4092006000b4080c400c0490980c1c00c2070715 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 334572374 1250 334571124 334571129
    0x501140c0304020112092006090406120b01080c0a030f0302070e0a1505040509151b03040305131e0603050402030a060f0b0103051501021e0c03100c0815100c1a010902070b0a06 77
    0x10302da001e0791f040d031626414100810501c19940030f41d00b0032075046580d8540c420742c00500a00c450f060005140c1c1c1c94a206a4081a00034080a900510001c902650b91042a0701620f52200321030844140c0c503e000d03403412080782c0011411f00b071850308014072401564480900c956a0814012000d5501d0f401d00044070400d4604a1450700300300c499075042000200784c40d07008441c20078060200040849641021b030400c0d18210005840003c80d504003202869109014040d0700000f660702942c4a1815541384216109000a050301c500002e001c0d07540602414030040e03003001c4140021402508180c000f07140c11207020780440e00d040045400c00c031040e040100c0040068000b810900841d0080b401c03004c42034429580c1d40d1260604000c0343c1e4500f408030840d1340031803000102c0c82500c50400942110001400480c0c2c4a01404c0602d820f9901c80d001c81d450902c103410080000d48290825501e01d0200101d42d20705e01e0b000b280005000003007036000740800d40c05440d00c01d03120307100d5410341016a003e51 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 334573624 1250 334572374 334572383
    0x1801150e0c090a030602030a05070f08010807051318050729120415020706050a050f07140313061103090601060819110c0a120e0d0b130501140c030402011209 69
    0x210300060110620074000c2c600341c0002040c83d480541c1d0307580c0d418240da00032a040143c00781c80f1001e1010164103c101c000c0ca50600d41000c03400c940c10401c02a90303440c05813140b00d01c51040031600d580d0b8104240c0c40b6403894101d50900d800c21507500d0800d1562102c0600c03850032660380c000c030f00201c02000c0c10704e002000030780e10035002d1412000c51020700e4400c0001c2c10a40d200c0c10444c004d074090000c030b80b0082801c5482010085810318107401007000300d84d0b004100c1804c900d45201040070700c50b44446841d003043d66400d803c5840e038882d0008040e1940f403800d8020b103044e1074008084c1280070f03000f001d07621884009007114107036a00e80000700c9003880d00b41c03510b911180d140a205c41442134039400c1f5a07000c0382d0b82d1200a0500d407034804031601d441c803400002c1c1d070070b4101c0026441075980d200c0c040c071044601c1a500804c0c001c042d0307038030064a40c800070714490b1078808841e240e00030004207400140151201240010550904500298065005407022404110043d0790030724a40d4160003090119600b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 334574874 1250 334573624 334573649
    0x1002030304030e04180c030507061d0f01020c0a0e010e1b0d050421020a140316060504020f04050c0702030609010516030b13020406020d0e010906090302100e0405090106090b0604050d1514180115 85
    0x1030814040330a000840250560041c02140e120a403030b07016581c03009090f43c0619410780d500d084010603103888054619410802405c80e8000a8410001200d0030200c401500003005e65850070001101c1c0684069aa01c42c200001c070b001d0056030004028220031701480c03904c82403504ea000b1255480c1700b030b2402070002402d54001540418001d5102550041c00981310b200018040dc00240031030308215424020100042044400c1d402c080005991011038003008001d1810706030410420603404a1080d01010303264031183c0d1090b00c0d90188a00700007030444066407115125100651500d501c0034500001402a0341c3d15005584925840030454215496141c0098110b400f0301c80c0083e2540e01e400240020354103c205a5261440fa017441041d818000181e00ea0420050784d0a4803003e141d00b0388501070a0006005640d1458a007206041d03000d4402c51104000d450064003400414000c4207903400d01038200100301b20801084d031b07240f00c0707410000c00182c10214002d511020307440c01644040f819 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 334576124 1250 334574874 334574927
    0x207050406061e0215010b0408010b0d031e0905030105040b0105011803150e011d01150501050708030a1d0a060c080a1a1003020903011a0a051002030304030e04180c03050706 76
    0x1c4501c2e00042d43c501910580c0c04000c0188413000040070207900101d200030001a0402c600d00080c4102007209808540e2066950542d480c000c0070081141c00008a00450f00d42d80007003280149904001403101074001e1050380f801d0305000d807003002d0904c01c150105080c000c40520040c514032104003030302c0d4058040b5803404821080f1600600c01403404001940da00c00415001c1500c455246224901c82790000c20f0181040c120305180c0c00c4c01e40d00190500170144503640016100b101582e510940f20840081d5102c04005a0b1a1ba0b44503012a2412406440b807000248184e9400034051025140c40e48441a00c6031540c4004a030b0880c0080d8405200d01c2c1c01d10f500c82e1400c85603410309071030240740150401e208100040d0031030380380e61141c00a051980c0e003048032604004001c40000c0c901140c10700140141c41c000a51a4440104010100441c1000d0300c030180c2e44e2a1300101b41042221860004005a890260300c040000c3c0016292032080b05000140c444c40362802d0b0340d0641c13400c1e862221071031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 334577374 1250 334576124 334576157
    0xf11010513110d030f08062e0f0311181503040501050609010e0c030a051017030c0c0d020303190504030f03030b120609070302060918070f1b0201050301030f0c03020901060f020705040606 82
    0x3c00252607103038000c01c0f90230b50241803003098880807442564142001060218940090600710a0420300f0040c14140061007800d2940441a2119881d80070048141c651100001404d00c4681c840880d010000c08000c0c031040c03120540c081ca1264070203982d641c0d5203076221407072004440b50480b02030b00c0c110020400600b01500c10703088141c01210540d10003440395140c8148000001250010211682c00850183c80000082124003201030003aa45200c105119402080d12889403000c400603540000340042074080c82807040713400554000c51b500c4460311103490b00a0140030490b107801d00c680c0501074510391314000428024010300c0000000c1641d68a541c1c24005075800099a4a92242c60303c2e0607aa0347c140c1c100d0007140714840319038440c3c182500503240a4110562110059201200030202c440180d800200f140e0543c0d400881d84464800d2a1800e02e40103405034000a411000400001032076a800c4118207100c1e64564080c1c82c0d0960302c40c0706200c212160341c800c10001403d10224046000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 334578624 1250 334577374 334577387
    0x51506060424090302120c041a03060106050c03090a180f1e2018090c0a0e0904050a0f03080a1103131716050c011403160f11010513110d030f 62
    0x302c51800c0c0405110394913000075070301003a0b2030100b00c816008503950340f070540b6140c461340c8001520164114920b0103e500803070b44ea07200501414050040024034803242c0e0400300141c4400010003400c460300542c0ba00240140e03110480e6511031014102600c810813030707030280510660071410395100c510848500d0004000f07000310070490080c240482000070219580540100303410341c0c90240c2005501001e01c20700c10480c4000f4a400c1c00340343c0c2441742400040d40f061562100f014100d179012015101da040c21803c0100e01c0350020260368801c0000004c042c0c1096886125204c5c1000c10015002ca080f414103891000b12200300e81581844002400603c0f411502d00d4851072008160f800c0c104011032249400d403620000b0358596200c00c21181c2c1381d41c0d1048192181112140d142800c6062505160005601c410164018040c0c140110030605100b00740c041044003c50000703108a0406660246030341651080a9844d100f110183d40345504080d8400003003035500d9070f54200b6080910804a030030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 334579874 1250 334578624 334578689
    0x20307030906020c07061b03082a210603030403020f15041a091912030c0302100609050108070501031b11030405090c090306060f2215030515060604 65
    0x3859600c00c84100851400d00c0a00f00c00512000240052410200c02400c4c240314400c50140f0720484440c804002075020002541200c10500004000d5444000b01b600041d450400c01689810100d01044c503000410400c480540b002c1c0e001c5015a1106000d0580b684554000603401800b5460060036a060503070040f81580303080740104e405c0507250090101c080d20351a1440c509444040386040d40b42c5000b0ba10b482c03952100781280d000240c030b0600c040c0c00300050501d0140070f109045441d00c0070305000b0f0010b08a401100d080400c81345441e03031f601e40e0080500780507141c0c01e80f081070b0011800f940240700b2030202c0758240c0c0d4440b981c94090b00c0b007280d406641000c01801d90109010001d41d03a01c824000c18015904081e00310789507900781041c03514225005142074454550007040c00e10b123880e07828002c001070700c1212801c0304500310503111001520018403e0181500e4a40300003060110106050042805070b40000e40251100810000c142c0210700500300134545034030f10710a09845a40c0c22840 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 334581124 1250 334579874 334579877
    0x20c0c18092e0c05030901050a050f010302010507020d12020706090b070503041502030720120105160311091c1a010e01170a06050c040f17031b07080601060f0908010b13020307 77
    0x3400c140c48480c420fa81c0034003489000b1400220030304c00410b90a0081592010f0008810080b030302d13100300704901800c41880040c3c140000080c603082035440e8200c0240c03805812502d004944094244000d40c0c039003943c800e210003d03600000208076000c9000071100503e030840000d5041c242054501e01416214a14076015803100b00400750000700610030400a0f1000503409240518419052000d10416580e8901c0c0913490502000040c0e0b814078a190181c03803182c07600103100200444076003201e100d0403404981c05100700900520010803802d0340312215204d0680281c00c5011000960b881440a009000800b02c0c8000103005811041080850b00aa044110392201038661502d608071602a02c042c101444000742c02c0c0080d04440000c100282540101401c031105082043c90300c03400f619200f1315520942c01c01d60220030404010600c09410b1101c290380180d40e54900c09892090700f000c1031313008500042030002d01c543c81845850704142000d445201000100c40d000030007940003d10090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 334582374 1250 334581124 334581193
    0x9040b0607050105101502010b130c0905060c0604050c0907140d060308130f0506070503090f1503070806010e01080618040501021b03070507082b030b04020c0c1809 72
    0x102040e804d0207410700070381e440c080b03215942d41050900c089450200b81082c096a040c6079550340a500c8401e4001c0c80c00035401c100144c40380c5080c904407070b400d2099001c43d41c03043c1e002c125114104004505107015070b03c0b0300f00b00c1e24031078180382c14400c12160484481d00411000c200c03281c00684420f006003100c90b0045000100191030390344505072900403100c8802109002001071281e10403502c145d102901d401c807110341c1048182c0d500c00390b40c1c3c411210b0850040c403c01c0d12090164868410303100c10500e6900200340c4925048400902400e400c448542c00120168940c0c0c0845d40078011603402110050100510440c0e001d0b18602d12580c06081211103642c2002850301044d40d0b05850358400d4101c074069940c0f086e06040c841c2ca4001c4580005080d60010002d540154020b0800b07070310304102000400348155010a010303001480e4600d41c80717070480c1c00001c140c2d01060000c00c0c21845158100c80d2101104050701c8800c41508007151102e0084e80102c5039070121007801d41441000d182c01440d0b40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 334583624 1250 334582374 334582387
    0x52508090a210908010e0c04020f07020909030a09090c0e04150905090a0b0901060509071d192c06041a0a08010203010f090b10030c0c21020d05030c09040b06 69
    0xb0107044400035101c26072200300b100310260751000c40d5400800e090002842a603080c03142040c0c84e44400780002d446a94005040300280300007000380c0b840982c00400c162194500b94005644a0784030390282e000042c2d00c032501189604d103d1098240746501a901d841152500d00180300041c2034a8aa07030303030801300e011030000c0e07000380b0360088603c6040e1650103007210521070f20b010300480c1c40283c0341c401d2690400d603040c8060f031107400c10280e015542d440c281310b50366001541c02d0500301c032421150703803c809500920745d1030311010740740501160028100400c3c540f81d01e40c05045a404800506099a1302003000302e132103850aa00044d50000f48a82103460324800300c80052145065944074a01b035035004401004100c03100c0f0f090340700a000800003846500c9042001a5030408402078a000703140d078071001d0240040c070650740c4507035280d40109502070407882c0c440d203101540d001412080052081001041e4014843d5050364003c4051315211418000c0c0c1c002080060401c0c034000ca9000304050081 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 334584874 1250 334583624 334583633
    0x3020d0903091e140607080403120f110d0806010305060f0a090e010b03070b0d050711061503060105150306040c261b0a0807030b0a050303040303020102030109052508090a 75
    0x100c2039400e00c65112148018948140983e00c0008034540c890701c8650943c0400c0b102e60b0f444541e000900c07003160360a513940c03a5458402c0441c00b0310782000d010a06a142c3c180d40e0305400901c0c0c040203c005032240c0c0c00f008440700d8101e13503410310b1030f110f0310006008101161865000360811500018001c00e410000c01c8000c000c02e03010300704c503840204042e0b04c1e0040c440d40f0344820b1144808240007500135005280c03c021485141d480344040d0510b100d40e0751000240d44a1040507000c0202ca13010056880c2070800049020480054070b201c0c40c481e0190000004651070040030220160040668042c1140d4071102004001c0902c0c2d00b51006201440100d0900711400704510441042005040e44c81801d0280e643c5480310b40d5a24419415034080050540729600602060740c01409440e000c1240460400821000e405c998401303501172001040c04010143c040d0040d60680c1c00c810420811641c604055504001c0040712150152181400032500340b40f0550b105644000c0c00704c00c5601440503680ca = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 334586124 1250 334584874 334584881
    0x6061e03021605060a050c0f120c04030c1d0109020405010f03180b0f15100503060420030a0903020f0a0218090c090a0c020c010f08011401120c0e03071a030c030703020d 74
    0x2000c40e85070b00913808010100005114040d002100705030000e050404a0040c286144a41c0440a49001c1f0480c006140404008103c5010350b5100c94903c40c000c0c0c0d41d040090110384000c00d0380d008a81c298001161440c01813082d00c0460b00141e4412264400f00001500101200b00c3d0182c070b002c0300d1030b4501c8041200c0c3c2c14080c0c0191204511004145010760400860102c0140b0652061517007810b4400000d0f40081a81c0e0003203000c4400103942e404c0b00a8290702c59080214003035505c04084104502a82558042e13080c00f07000740c0075210b407040c0424810340c9645030404020b500440041580410307251030f801107984000110106c5241420110004800040c21601d403500692218051080540d0500c408852840d0070300f00500d502c4090000901100414040c2c0c1c14004144000d2180d01d078403410f82e00c901c40c1c540d03400812034040d400c44000c200c81d48007450f0b18001e00c154540002d50203c0f4040c0107016044900540c1e08680360031161400c50350016040706e082680901041c10300000620 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 334587374 1250 334586124 334586167
    0x1030608070803091527131406030c0102070803041214030c03090406050d0b010504110f120a0507020d08190e0f07060906030608120705011401060201061806061e0302 73
    0x700219100c205030b50400015800c80581c100001d9420301401480046000c0001c070110041103045d50502e00c1c1502045580c40101c1030000203170302308035040e80b4840c0c2e2012045e000744000d0b0150307200913000c10016a5503144074800c3c07d4a50f8420001003041c0c008070442d00448030311812100840400701c0500c03a03d90b42020103840f599400c0002da882c00c920341481000014102621070b50005c1c181a00e038012103100c14070505004540720104d18001044000845001e680003549840c0c982e0540f1010001d5001c08840c1890071074a0180070419050000942c55028903942e0b460a035150b031003183c24503034a0301da4030b1042d03159a203030a03100c03204003414003030800f000c600c2800528852f40740540080c541355103a445502818a041c60a2026040114a01e204098a0715001d039450340949417050040c00071920656460070070301c0011a01d60fa06410000c119403c41c04580d1070703e5040c001c030400700c4259104400c085000815500c14033f00c004102803806200c076041c014140740040c50410580010803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 334588624 1250 334587374 334587389
    0x2011407031e090602060f0115030b040b0a0609030606050d080316091203020303090615030a030c0c0e1e0105010e09062808070e100b1e0c030d09120309020a0b07020103060807 77
    0xa0f6403d01a06504114065210f4207400402c20f50754980903a46d9a207181713071140b010416407a0036091a6035156900907500418015100100300c075600c0700018088182c2e404100d41c071a090480020b800d251860a040126400040d120b103141c4030f01c103c1d160360500d001081d0060103002e07140003890055200c001215603000e0340113140c1e246805080c0c20f0800d00020003540c410340c0415000d16991310000b54881c0310300da241c20044006403036424081c0b90540a6170101004411701d5041003840000c2d00c00000c0c1841c3c400f40d1090003a45c8540041d034440c2036054a080d040088000001c1ca1032501800384904400126049900c0c52441d2050545240c0c41750000841a8846a0208954110110301039400072141e40350031011400c001c45290588680d8629140d030300c500800c50041c4c4607140c8119050b1507a080200c035910100d4003580c4004d00b040d00015102d0b801c1d542c0640203840e0081c018400c0083d0300801003030700f103403d04040321b01f00d0304110002e0b070401d5510080030507800c90800034032001d442407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 334589874 1250 334588624 334588637
    0x106030207140a05030d0c02010b03030703030b01021006121709030f010c0e1207031403040f06080106090603020c06161214090c0d0c050d171201090506060702011407031e 75
    0xa0b410308098100b4410400201c40e480041004049007011003581d14032440c02c80042101c4100d5603003240901141144150f141c00000750100030103030107920982c0514030a80981c3e22440c000154001200c0c0148621201c3e00305000e844000503c0004000ca840c1c031400319014240848103012a00c0c0c901800d2210b0010780d51103000072a0140c04c4400c881813010b00b15510007480b410842c407992034114512008104088554a0341c10940c002d005640180035501e01914031744d5603c14008185038028401c88011a406400208041c2e120380211000c54a41c4001026103880d1050903520891602a680b0100030201e0507544c1c2c113200901595055100c150000541410300490450528845040d414810440305414030001610304400c04e04880d01182d071b8913515401418000c05400001c80c024420381d60010f4030b900700440d1782280b0ba05894500004000c02d903111410702069210768a4083e000c075554000304001040d0010007400c541d88240341042808020802070084e58400702e110702d02003140e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 334591124 1250 334589874 334589887
    0xc070f060f05040f050714030a0618151b05190804020f060f0304061a0a0317040b0a03050712060f1a09030105010e1608040b0c07030c150930050c010f0501060302 71
    0x4004030801f50402110080a491140001070380d01c0700980c1d0f00070640c81e140c038600484510880c8042c24603035000808800d20f2202d8001900052541c500030031403444c2e40b11050340e4030609c503000b544d02c900720000450701340c61202c106c01d403590280204206c2e0700843c40b02d1440c4181d110a40508030200c0780b072030020b440e82010b141110079101c4501c0074005c451146c0e0001c00e141c0d521140e440003183d400c804078801c0820303000300c521064030a07a08180381e00c0000180d05820540d056010354498400c640e100e1410031480880f1005541c820310482900103400c0200740180d85000c11904c84105410001e00e1a00a007800447c2c2958800da100c0c012014030300d0108400400c1214904000c1c52480ca000085480c0555801449040c00340250800100c00300365a010540182a1002010741140150380e038004615000340c06010006022201c240c20300c4941d804c20001c0d084411000301164001041c01031150104070703041e40000c1044845907403900c4010366442040e2003041e028108503680507903600c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 334592374 1250 334591124 334591133
    0xb0a0206090604020a030b04260702090f06010f0509040e15011d04120e010c050a1110050f0904150905040b0402040b03160603051009060815010e0c070f060f05040f 72
    0x400c0240800116003060040000580c3d65115640540707038031400146054880d81080c817071142d02c009501301141659040c40342d502220002801d101803084404581079624442c0f80200c91400741c5107507001c21801820259140d008401910300081b010740006181c0c1303204c05950b40340581e2035205c20b80340000c0c4401030103440c40c2070311081100b41f00d1400c4800141046d56030400051006e14842e0b0800c0000303500c25050307a2050300422805600300c4102c84150000741131208007420101041c512400b22805103401050081050780c003c2c2214030001400d06544505000162a03142d24408402c032a0440220300700020384a180d00482c000d029030905807416106220880e00c50440c418805e50000045440f440d0950300160141c540916002c603468451070082030602c0e84c6a00004034007404c100c40030a50600c001010740407950181048407250741d0703400c070b07811725844150b50219070203408000c088081481841284100d0348600c0001a08005150b180411548150f80c2110160302400d111020300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 334593624 1250 334592374 334592383
    0x40f030f090602030d0c140c16080f030d0c020f0a0803010801061a0702130b060f07060506010f270f081c050f0d0504020409061d0d0f0e041a0a0b0a02 66
    0x108031908042504900788540a5628042d00c482d030302c0c140e07455628100d52584500340a00045090100841c1c03554600360b4003c2e115003282d8200e094200482000090000c80001c05804d40360460000e140780001101d2008060031018040500394410b148a03543d12400030484029400c1c0102030490b10795040000590960300d081c0e00000505150300840da0040001d40304407003040d94102c13640c80c0f040646042100c0a00b40007202c140e0300c194041401e44c500c609103401400d81d688200003c0105075210300065980079031301540340000503407004403040792220f0410780d00c0c1d6100481c1100d024a0344c0e40c0c00d101d030341c01c4400d42220031150800d0490300c012114500c400070030400b90f800c10f07604080903214445101d0107082203a2680720b883714041401d40d00c60398481c13141c01d90412f00038048208041c41c0380d100c00c00701e0842e250302442640460032200c0e200b8040c801039486160346800301780c04000c041101800d1800c90540c050000780d02c44511664401c10000024004041c03880e86075019000040d050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 334594874 1250 334593624 334593647
    0xe0711070e01151b0821060402031605210a0e06180d121509021c05070206060d1505090f0106080f0c2701060507020901051c110301090b040f03 63
    0x10074040300040c00785140c000a100241030f500e1a000b90319413401d14110040982506014141e10700000b1301801c0402c1042c007801800c40d1078003a07407003241c5501007130004910085503146004050441990304841c880e030002d14440c00807410100e010f0344110a600031015095401180c1c55650b4403003020506e83c01d1103915405599140c0100308501001051500e03055841820010808001c52080d455442c541c8210070848191440c0300c1050345840300d14001398081c204e01103003c4481c5101c00d0780f9191902400c2d1082c0e81c11350103000c186d140c810030301100300060782040361450003070000010480c50718450079125000b40c81c000c058000c604e0308550300311589604003442c03a4114000c070401e42c0714005038000300440c007955500421a0b07a4822000c07d100c4c61102000450540400004d54503805005000345500031525441140d030394008200110180c00600140c1880c1c040b48180414403c008144442c4000780020034106215a1866031003002207408580c0b004a500d010420f250b44481090329 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 334596124 1250 334594874 334594889
    0x1d0703050c090f12030f0301080312180a02040f02210124140c011104090903030c0302040e060d020a1203030e0d090302090a0e030405040219020d140f0903070e071107 73
    0x9404480ca0101d19183c1500c0e0340b40380030340641542001c150004000301c42603a14450920303900c1e940c441009036101d5105107a40c00b21501c0305000b00b90800440c048040c06200340000034505c0103e1030b03085c040503040060a0000300d41e400d100c000b01c58590310950300802440d000c19600b4039810211241e1806501003540d2030a02001030f0b110a1694020741b5a0b148030601c22107580d116941811484e016000c0e0381902d090380000450000f4030101b181d0401e03640d49100b610140031405138200c084080f40513500c80e04c081000d40102207100703801c040c402002c0090025264201031512150300b50516900300340103c0020f56034a40c00e4040080030311840074100710310300c0e1840c81a0f14580004490b848068401d0303040315901d08600007248810021a0014403020b0010b6480303070741e0b00004085441142c00400c000d40200520740014910440f0705100b003041d01101c0b5810310254000d60717011904004c820315051f100301b00c0007040114800383c1c1c0a2003100e4a9440300820401c4844242c00c18209500880 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 334597374 1250 334596124 334596127
    0x9141203010b07020f033405061e070f050313060909020306010c1b0e04030e01020d02150a0903050705010204030c05030706030501080d05032d01090e0f100b03071d0703050c 76
    0x442c6114420460743c00b1a0119080c40f14101340c0d1000a041c900702c0d40c03001c10a00c00401006008500400150800503480c0d0f4081820341c1c0d540707003446454030803a031040c540030644000500d02500c0e80c00103084154028114001242c0c0960740e003508c0c41d8451561241c1e00b15104030104002d1358001a01c01c05408030000940c111705200c00041c18400c010b200080401810460a0000c0480c0a03000c030300400320042201218249410058150455030501038014061624203550b0075000061480800401500b4407800e503070303520f000b08003c0403071090890811008002800114000f400500f02031401840018a0249420205884c1c503003242c2c0500c060608080042210a03404985900412101d04090340ea0341d0340d90710504180c0d8003c12046e818100311046a20005080d00c5400d411780c0e08501c01005240800d014840e5220420004004aa40f0000056004180980100010309005411180c0e41d0b030300c80c0e0f01404d24144058541c0400d400d48010000030b59414001c0b02d0308070b0394410445 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 334598624 1250 334597374 334597379
    0x5150a080f060606160503070303061502010b0f0105032e140d0305030705031504021803010501081501181b230306060d05070909150312090503101a040914120301 71
    0x1541c44003801043e59114400214036240e1003102e45240d1036030b640d40700302600c1eaa40402e16000c0c004004500841d0039010b4150340041c01e1500501c1516803140c0300521b2a0414140b25004495980c4000c01c019038951010069480340030208590040140d00c20102c2002681000c0c8040d1010940c4000da5125801c40e00702c000100340c00904581d0000b61501d8510340d80c0d541c040070031203004450714407207422a1001407c0f0b082c65040764a10300d9802c404400900c0241d9031810003c1c0c0d43e2264010030284440c00b40010810140b401103806200c01c0c003510003003140300001444041100000c05603802180640c103180d42462a142689100400b02001080c04d41c240700340032500b14050000b404c110603a80c0c2000c144001d00490b03074000203040300c0c50140074a07603690702081d0064030b1501c402c5420f046680900082e050060050714191000500203081521540d01c0e00030240040b074081c030411302102200b50446403554001d0314010f5010300d10030821203099504035450440c0307241248a5150050005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 334599874 1250 334598624 334598653
    0x61a100e0906090c03070e0f090103080304030324050603040204060905090706080702030a0f030b2b0506150904030c0f1203091a01061211090901080f0f06040c05040e0a020405150a08 80
    0x1170741c1d0002c1051a2807000e51500310b020807803980b5045807040d84040308200000800615100561107140700c0d80c0c003481403407c02c1001c0810300c046900c14150039041c404052209080080245070701a00041011408640c1c50603aa4110741090f42d107a0225084000c041c04541d8004148503003256092000f18a0030144000081054220300304280400d0b44030103000039035544a241c20f501500c1040350070807001461401d06e208074240144c04940d5805014000b94513590500607444510740054940d0303031181e8036035400301e80e420160b0204480322400500700e40c01003002500d0a0a144030140ca002a099800c0d042403028185800c80d080040d04549005006150380308034612105024020080351468050015034460300403c0001a08406104000502640d00240000405421409817804155131b40f5941d41c80301421200600b0f40e4103280c0c0e0402c180d042580c0600d00a040400990301031082a134002400e550044d22002141d40e000c4402d02e240f4075041c07040d072009082090080200300c1c0304655 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 334601124 1250 334599874 334599877
    0x70207170f1605010207051c0605040f06020715051302010210020a112401120321060b0a082d040b0c090a03030c050c06030c07061a100e0906090c 64
    0x100c411100e00c1584032203596008001c8400c41c59001c0040d80e0080705100c2041d22640d82c98400d050051146801c0002d0900300321019603034241c100d000380003407000d464652402030700014204440344150010340e000450002d2020f044064480c842842101a403a209241a110007600303512000e015081a080140c3c2c0024070b8500228500c0d8026840b030348428410b45000500803074030001400340282c401c80c1401099800b11403200d000b01500c840c1d9889070345403081ca0316401c5004000c290f1801040400c011070081d0703400443c1c071101c408113000340c0700c0710440e01036003111078204007140c591024405140d01e080d00200150120700c4800e1600003405442c0ca2464401a001401c1300d4002d0340400d900300740300e50480e00309000141031102c07400d99901c0c1c010480d580a6500b5140d500452031208140c0c038242c0222805000c001c1c215604014560302c4150042001e20a403030034920b0310780900491034481d440d03003001c2e0007503c2d01c0d504841d80320302c801e00101d81d40080003148520000010814161003100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 334602374 1250 334601124 334601129
    0x4050108030318030d15080f0c060319091703040506072c030c090702031216140307020705090109060623070308040507030c0306020d0b0d0c051c02090a05070f020303070207 76
    0x40140c1802400f6078202d04620511005420142c101090b50420396401c03e421402c031350408003214602c6d51008561a100e0070803165076940082d00300007140345240170000c0c0b144030101030440000c000001799118004201141855141801c0c040104420700c0005d01c2444c0c0e01c0300084c18280e940b68000380300141c10540f05210000390010f5111104102c0d10f00308142c0000d94006010400d09040405003c0c0d0380360000540900c004030810006200c409551402c4040500551140210f1b062564807140d51904000d1004046202d1031034006090307500c41040d580205800743c0000b80c031604280004001d003100103a5084e801c07409496884400c600902161011501071424480ca6217461600030b003490000e0740060304140d003d40380441440042e40c000c2c00d5502500310204141c810720000c1c0800361845500c0907143c03588021080105003004c0080791807040c686103000c0e80c00c054030b0740020681c2d070003a070b0508015544c1c2d004214005400c0448040c61442900095044d89001c240080d5a03480c60f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 334603624 1250 334602374 334602391
    0x613050115060203032a040e04020a06180b03041a01150306060206010b040b130b0705070f080f0604080903030c0106090e120f030a0b0d0210080f01060f02150903090307120201030506040501080303 86
    0x208840a0008899141b003500440301a40d40e9031b2a540c03051601500d0381c00780d070705030b06c00c1c59054400110b2502035141c0c01d14059171081d003200c80d01d103005080d4285801c001c000b50381b105014005a01004109580c050281c0420941c0c01003200c00c01100908846164001c10155032000006000d140503a03802d45085900c0c0c1480700e596400c00e03503010036400d8032981c000c030b030ba11901040810400c400410450240c40d2036441010025507a5440c0c65078035030b08461a5010394001501040100d1440001095451000790440c1d00d4000b082e28a1421560a9841072005540d212116441000c0500c00fa00502d2502e83ca03940c20f028101005809601c400740500004968842e40c180140e1120900b1545040d0001e02041840c040050f024001c103c0c00c90b08141049024400400d8490007a1104545d0049590003080c00040d00001103003190b030080c026074800d04c07080c04084065a4100198400303000c414900c180032404620005d01502e0000e025036103d1400d140042c0f001000000540781d001480 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 334604874 1250 334603624 334603651
    0x601050f010507050d08090d1d131b020f0c01210207030219061a0328080c06160206250309020a09230906040c0e0403050408061305011506020303 64
    0x400182c2d1548141c10008103580180f01c0d44200f66500b00000c203101356020710503120b41104608080350003c900020014030b030020001c0c0d1b580075050a12441c001c2406002000a0922620b81d540d41c41340040c3c248980103070f01c299a004141d0400f4002a12548001e00b09050404421840d0100b0510f898411030522076000c65034009042c800c001200c00844512156030203035903141400c4001d000305911300015040540c181c007801d0f003000101c01840510761083c0320600001d011034500010310501d13058400340001d04c4810404441030101e9400788801c1400c1d04402c44003800040e00304a002010007000e40e81451000c0f103441d4285070002c0c01d41e905441c0004400744d103480000d80c1c203601c0350803100c0024a410140d0f800d0b9062621025a460903440c030321041c9503511200a9070b03d942c1141d00a11074089580200900a07a0000541c2c105101341001414283c5072402545400011514102002003001401c41404000e10a440580500004006109040c032102a40c2c903c03001c0c0500001444 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 334606124 1250 334604874 334604899
    0x3121b05030f09212a0904030e010e0d030e221d1207030c060e0f0703060c02160305030d020903030714060f01120308010e1306020d021b070f030f06140702060406061502060105 77
    0x504500b07085c0c2000030902c2000382400c0c03c006103100170300c1014902294800450070351518260060b071210135819910b100c3c10141e1582481003410710003e003080708003102c0b9058511104c0f01d004001e0300040003160102091001c0651b030b490511200c01c05941c00a04101040103c0c0d4003004403c1003039000302e4040b54480820003414604800035030401c5860240c014003001300002e0b500407136840b10503942180c0c0401e0150102d0700c43d52000d884000c281e5802080080c0440d8969006450000802001c1e2400c020300754a40c00c455822000840c25241c00c071348100020381c4904041980980744602054130203c1065070058a0752406005105504d0813010014140280310080800107a0f0301100030342d01d4010014558001c4c0d00884240f14001280c82c02c0c20781c805800042c440212107456010107071103031541d2200d04001004480c1502c000340c5030111410614056070041d8010b0300e00d54005c0c00c0078901428000d0845002d03802004003c1c042c032528201480d800500349040d02c608403a003801110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 334607374 1250 334606124 334606183
    0x705191703061f030f0b01032a260105090c0711010c080f0721030905030a0f030b10050d0b12070b030c120c13080703121b05030f0921 59
    0x4580e5100d00c891a04201d00f072004040e415000720000010012040c880c11120341c00540607264401e40c82d00e490340240c500c0880d104d04c0311500f694000207e01f403c0c4484445450f03580024007807066040b04005003034004011504205844540c0170542003201d5081070002e0342e400c080f4004441520741041980c209100501071a031003101c2103400c0c0e60310907650b0b0f0b000d40d160041908010b01c4460030268004100d40d4060780c007a01401c0b03110b40d4040061407901814040c195900054024880c042643d07640c500e80007500d5030704034041440030a8840d55192010290090103403800030354903038021220060300051a410010720744050f07481c0d01c64015181d640e280350308a0b050180321704005003602540180514109814000d0500c4005038416208040c3c50307400ba60fa59030700302d1000404541788a040341100074400da01002024030481c0c0c000c11200041e403205803544d00203080101808400041c00d032500c1c51700c0c01004003882c641c0042c3e0701031015008030042d1a9040d000749a9000f84442000c4000c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 334608624 1250 334607374 334607389
    0xf06091005041a0909030412080a030e030a09140f0a0b07110607120809030703020316150501270e030304021507050d080103031202030610030f060305030d02070519170306 75
    0x1c02000e0700400211200118109010303c0c4041898011203802000c9021030700040116020341d11500c251084400d01e654030410143c2c4504a00c0c4c040542d12100480c98250601c0102038281d01c50380d4440d0031034141030000c201200d500d825030f84500e01d000e07a0880709440b07170b0000000700d4034618241a103808071070802031a4040b04001d51a841400064050100189984082503100b1729a41c1e82c0059035503800f09030358074130134031030301401592044c818122800025280781c00254842c0c2c4090640340d0302084c0c00015524281c1018401e605480a2a144c007035002e16081d016010350b0500340035960700002e6498592201400107401044d000181c4030304c940002d811260141e601100315040780384500002003140c2d00a000440c0003c40704184900510114000c0e03034081c01c0f000b490742d201c000c0110410380c01484074420400350b0a848081c00004102c007480501000010398001503030392541850504c0c1404040c0303002411040505800c8004520000110302010340425103041d56902c40e1000204031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 334609874 1250 334608624 334608629
    0x60712081009140a0e03270d050a0c090e0106050a03020f04061212020d090321110724020d080a05130209070512010522021c060f06020609060f060910 66
    0x203240c18040d40e44070140c2c51080d0140b240703031031940400c103140a003150a500c0c0d1145c0311850444100c3e0107c3c0b0408100132603008004040c0c02414200c640040d81d44040c107081c0381010580318485201d104211041c264041d0004480c50300f8000c1014604250005c1e0705116240406402076141700c103640081d885660001003e0401981a41c0e10398041d89480381c6d94000c9810440018010084501840383c0a9041101601d0f070000001080d4007100080b03101c2e13100500d65100c2008495015070401c01c1050250b080139001c03c0010540f42c150110303070720080d0340305154020708640c01000c00c100169804020700f80c1124200b6404030306922260704120f062001100c02a5000711050180404a82c0080003040b1510704204640816a621810403280c21000394a00e94180c220081c010040c3c1d1250703005207480f410354106016580c81c0207000c10121010ba4011510300a51140d052244c0307501088110ba0084140c0c0c001d180525001c40ca15020030000745c0704901466030302004c5110000c8107001070f8007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 334611124 1250 334609874 334609889
    0x3030f02160c031a040c0611010b040203090a05060105190e090a050735030d11040305060f0405060c03010f18140c1809010509040803060d121206050607120810 70
    0x107116490305100035281224801110909410743d0384520722140e401a007885181c1101d403400800385086e0080c1c0e400038003419224515566442080c40f15a2248042c602a40c0304000038070580b0500c2c50014580b00042e08000d110f100d9005140c0f9540707510400140039905005003500c1c103910358109562a00e0b5020600410500884001160ba01000c60b000d62212201440003140c840441041502c49002800c150000e6001003003c0200c41d221500440102c0030f5844a0718035055030307629502e080c0038040d512500d20302020320901c001d1104c2000703101c2d00107401c000007a165501d80007281460554510441c00e50351f40ca06a00001d00ca910360000380080150146d40400b450028032040480c0e20030b5180c001c1c0c032400c40740d10004a080044189041e540041c0002019448949030000e40350030041400d42c0c0a003200d520301c800100801c280f490b04039000e131034001c0d51000303100e00340007a42c3c0d03075802c0140605030501820000c00c00f9031070b0700c1d010a030007030400080580fa010014045200250000031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 334612374 1250 334611124 334611157
    0x90412050705010203010e101502060403082802071110080114060c010e060601030f15050402071407031217040201050d09060e0304080c0f030703021e0406030b070c060515060703030f02 81
    0x2800420041c940d5118510f001b241e5800d150b109c10301c0003488031030f43c011400103130312038000180081d026001c01038020314408402c1000741c207007a60190201010010441c40540c02140113010418264048442031307000716034000c00362548480007443c80905101e0315040303200414040b0442d4845108071240801048000c2c00750040d01c83c1c116075601029100360303001903c1c00035010400700301e5100b480da0140200d03540380f0b5083e10b060100300181d00416420707100300c560034514449443c400c00000b0003d51056540070076601a190000c4c141d45044d4054a113030010a00c10400180e0f409821150008c0903000c0005405621381890b40042040b0032547d4450301c00040c000c120001c001505400d20b00c800c03280703808811401e50600d1380360300561000940207400944555000d84244c41d0706140c500c005040003440a41e240c4480359054000ea0b41000851281c2d00a80c080c030003a40134840d4045144404090380c6003004010034014822404e01904255a03a945444100c64980440307030181000386444 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 334613624 1250 334612374 334612379
    0x1e130203070e0f03010501140f060c010606090303030b06070c051011010c0207031b05010906050c1002030403050405040b010c020918010e1608060f100905060409060e070f060c0209041205070501020301 88
    0x90b1204512080b40b9200d07420001c071101061805004050582d00c81c0940c0f080c80300e940707070705200c0079400000045901010030300c800401e1076001d1081e000106181d41d921680355196007009011508020880346c094142008940c010950303035007076601160025542d83c01c0c01c00d1842000c5401c00f141c441911082d5080503d0780c5960f0b540025918140c07401401e01b0035036441d03800c019500c541c8440c800d103030104000314002c025250007180034104c40c2c10030400f980c0d51915444042402c07648115001c802180c404942444141070a00c03400c8914082030800794880700c0950005400988014941c00f40c01c100c0d80c40944001100303401251407040c02c40100c44648a0344240701e005259030740111502449240002006400c01200302801403442c45485a031203805c005030000500402001c0d5034006407505d8400300080e40d68428454407003d51005085d54a041542607000c40400303500000c2000000d4104034056600c011500303403c207030721141030008100780d250151410302a1070780c050311551010000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 334614874 1250 334613624 334613627
    0xb0a050d0f1209060f020109020906010807111005010f06020303042301060b030412170c120403050f130305100b0114032203030c030605090c1804021303030e0901050f1e13020307 78
    0x3c1606841e040c0e1103440c40384034002401c9080346c2e00080007a6000404401280907540219000f50f0000042d20f82606103e1036800994544002000c01000d9541ea07180104043d81e091026680500240c0c4060340c03841c1029156183c01714003900b4082c2407191f5406c007038000f419095111b1002010002401078581ca01420174030344901c403860b43c41c40801c000d45400f80c56100c0d0005e0322440b860181700207034100b0755441e6400c80d128000610403401d200c0704019188581c60240e000e00049031f000c0600145550035480c0103401c207003046020030701150510b050f072a83d0f80e0b0401a0486d005244403203240d1030342d542c0b00c8000d00701c403203240c10b1100c0e108010042405055150300008008a20391700c003800010b94400500031104000c41c0e452b0202001030005070050124085961040c000081001d0f09142130b2140c080165042031f0310450100d618400a0300e0309041100e507581c01080103c41252003031035514045400385250900c50070318060a4a4219444d03502c1d601d49540320302050304210344a01e0007200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 334616124 1250 334614874 334614887
    0x10b0d0c0e2805100207030609020609041a10080c0906070c0e041a0723030709050622050d05030901050c01020403061b020c1e01030b01021905010b10030b0a050d0f12 73
    0x203200b403240e181070080b5450410400c0d200f044005540100503d030300d561614401040028800c0368031160400c12a03099075100c2c010700c084c92003200c0d2031210100d8a201040400c28078503441c101480121004c2010b0400340ea801e0b00d0f0b0044080c1d4031a82d9510720381c036045d403c41001d500a085204c1c00102444180455010303002901c400b40d64a982c0c10b42c40700e507000d0b90110944460303091550182080f544018401c90051500069981003401d4525111000200705820010758400e541034003441c000100002040c0c0207006201c183c43c131401480c0d403034035496164810308090b03505200002030400340000c82581102d00450b0490401c01001e80b0242e21651140f00e0307040304400511400760176040601e814482c0441250345400500c5031940840010350240c1032071211541580a40c02c90409100e242101000102d807144000081c641091001c01c0341807581508248209441e09204c1c2c111611642141c00954034100c400641c10b40d4540392940054a150400901442c120002d2481c616042031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 334617374 1250 334616124 334616179
    0x70f0807080d0804050c010c02031501180605090f01171c030207030e100801030b061206040f12080702121602180901050105121005130804061d09010b0d0c0e 69
    0x41038411400b40c40004a520000070b5401400503001032800b0f40c0301d503004101407900c16202405464503200301100b4203070409000d911144100300a445103071403800c8a0300c02c02c000b0b004200d4a0094070305011940610540d8140510b4003a40400348002c88961020400f4201c00802c4654403032041c1000c0038020041d422409044021a00c0350746216600d20f4001800c9a4040c070580d28207a140c1c1c40c613114070113007210103003c80d42c122024000c41981c0c1e90050200c2c07403080b0700680c00c40b4880e400e203107044403c44546480800c00c01540c10140000306501181183c1145800d100864540143c00b501c100461450000250b00c04603001030010981014204d1910901c8800c008100d541e80c0c0340240101045c03143c14480030354214813805110144180e01c03160300500c0d010049504c0c4c1d16641c0c1d64641ca0b80c081e0300700c440031490f0a42910b501c0c420000e409100070101b0342d0202c440b94509039800d0700a0094081402005031a56a041d9145101d038503000c08031800102010040c2018200f600001404078 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 334618624 1250 334617374 334617389
    0x50718080703030314190c031e020c06060603010b122823060d0813030c0f08071e060f020c0303031e0901090c0303080c0c0d030501080f01060f17070f0807 68
    0x70917148001d40900200f02c1c403c541490084140e001500703441d1004000c035140a40c20f1680c1c0341030458408210240c151049500030301d0060392280c1d04c00c80e80d483e0030001001c1c2881820100014080d0109540541d2610114800c01c94020341740c0300d12031610074440a1850170f88e40c620032140e000424051b0000c03020582007600c280038a6001e504910100d05c002c485d02500080741c0c064003c0010060401480301c9000241341443d82c41d129034400552201d079602c51550ba205040f02070103500b1050081e1801442c4046507030008045542400e8040b42046c4a8541400310b0b45440e814401d0090100140744600141581d550b881e009c22900980c481752544040c0320102500003501d841c85c14824060143c2d0020390700782c80c4a1542e6422a000040100703981c980a50911134140341d220300b000010010305954401103941d604101509150a41c0280c01e880c1c01d03030502d0310420180510400740015120410302d18084c0000c000141c0e450034800b035000c2448207019100015007080b000c613108080d40d442 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 334619874 1250 334618624 334618631
    0x20309030c0f073b0408072010210f0219030b0f130b040f02040f08030f03010b0c07030507031104180b011a090d0f0218070504050d0c2d080a05100507180807030303 72
    0x1044444234540c2d84078050f0800c03981d2030001410fa000d041e200f500d940511210203200c10f4011000c06c10b454140b1120200142c000c40d03054550445403812501080051800f00603500c4c002c40082d60b04030030304c0180ea0141d001c00800c0da49062660300014031021000c0e000f4000440d00d030348010029171043c0b140e503c040c1340820010540070710200840b003080700601c43d000e0444c0d0038101001980d900081c0029550f1007480c0c2c0000021b132050082100441c041c3d845080c510b455001404246c0c2d0400e0901c03501804074400440006400c1148a815111650a13003101448071a500d49020b21841d841164401044584101081401074114040f80c3c82514064032201c138006403589134003415103506021170810701040c85a0304048580b18034031802101c40001140d41c800c6d5100001c000782c0804071120b1030074003e80c02402e80008141006003000300062100855513100e498440f00c2c44040149030544440118600c1445040001c400c0d0b104645448210b40c0d56001059503010188403c0700400d05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 334621124 1250 334619874 334619903
    0x40c0c0204060501031e0b0f13141003020d0b04020310020f03090f031201120201090b04081c0f0e010305060d060606050a0e0604030201270306020309030c0f073b040807 74
    0xb09000d841e01490f0b107046510f01340b4070700407482d46c0903004000c09140c0043c201c541000160b551b200c01e00d1208400080005100d0f0044003010845c038400415a16100c00210b000304016100d042c0000780b004c6d003020089100b522248002400c1551828070071242a00104581680f2140c4c0401503001c0e00084044540da486003548454603405802800014080000010051454440c040c0780c40b161052404909880d00c0f143c10301c207180c1068100b56075070303881000d102e084000505c00d030b01030340300c000d00304200100c544c000d00a102d070f1010041c050402d620344000c590551603c800b50102140d002c113051060a46504004140380c0000100800142c0c3d0340328030304a6401c0c003508030f80940b501a50381ea441f1240800c9101c0a0f080881e0302032500d4100c1c4080000465824030213180140c07a60005942d80c2c8200482552502c441031584800c01d03040480104013403891103661703800c180340307240c460060014400c0c000c4184d2031081580d0404112028200b1013004a114028012988202c4040c610401c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 334622374 1250 334621124 334621127
    0xf1401060f030b0414040b0403020a020612072303191d0105040309090908090126090718060807060806130504052103090604032f1501060206070504051e040c0c0204060501 75
    0x400001c0804958417600f4042004110b000c80c00c7c0c0e80c428081c0c0100c0303241b05d4080d4041602544110a481c6040340054140001c60303520504d904203005200c00021002c1040c2005080540b001030411b075054240403924207070b00c03025904240d25218003038450b510380c42904003007240681011281240010041480400c440105119503202d458204003004d0030040d4210066404001554040460310079200501546c2ea00c201003292103003120001800b85c1c00d2802c1e08403290301002c00000300109003071240602146400280d80e008660041c40c00c0050b0ba214040071030304407400e80508040c03007400d090401003401400541740524a008144a405440742c55103100c00c10700082d07501d40741a40240780843e010034480d582440003c04214084d15101040500809a0035480c46001120303401c503440d1f4021708940c652041d80103145900140c152032070900c40c014490300c164002d06105169080c032a800700500b0b5440e040c15094094010002003030315142c064003190412008038403803410000d0200b10f55 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 334623624 1250 334622374 334622381
    0x40f03170406050901050306010c060e0a020907020d080a0b0a030c03060509071a2b0608060f0a0207051905101e0b0301180b130512070606050102060402060d0f1401060f030b04 77
    0xa880540e1280e0038130381828011142a84040c01d1700303042240982d012404245180700322118100c90030000c241e0348607144184a01d010000348544155041750410440847c1c0120200b680100d0012000402c03080010014108c48290342000c2c0c401111000d01104210b03807540701da4084c80850040b180420381c2e41c0c10741030008900d144400a40c1d00c081c4409030b01246010300c2c0b491904481d01400c200c20690400070710803550341d0f03407056040d036011400348502165400041c54118410100a514050742616003c1c4d03140241503804100220a1a403003081c0401031000d62004d10030b6a40031704c4502d21040030842c06c1c243d0501308004161901320301d05030925052054200b60200340c6012a485e95042d2074800305900021b14003000c5e5407d9100020000740c0500c48036021301d50503110740b13403120b6940c14680c08503031145d013000c0e040d13610400034400903988000913248104e0740d0783c10200307980c10200035100140c880b1085518900d00e03640008211960811029680c82e155036608202c02d0b00210200400d0303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 334624874 1250 334623624 334623629
    0x6011a090a03080d060803190e041a0d060e0d080603060906011401140c120310120c120f02031501050310060f0b07030915080a0b0d050d12060506040f031704 69
    0x11004031000c1000541400c003400c0213030460040010101d0b51000304c941964041d6418840c3c003e00c45a2007554a030b000102c060205005035010020107203280c114440e400515144144030312420390300b8004200f016001002e0300b14540c1c090301d504584400002d000c450b429988a48240504800141c7c0a200000e01c0703412101c03840e45518010301094010b40e4140011210740c11800400c000c02c2403402c80800c041d0078841c0e146408079039646414001c03800c09110350340100009030006000d2201141c45182e04405a42c5644003150000425281000c07004280e07000080d014054ac80031500002800c4041d28101c50b02501560001e07a124001c50701120310900904100280d001401e003c80032008000d0010039101e0300f07044203a99100d48007400c1307034410400e4000c00034804108000340c46286002e1007480208c140c90b910000301681e911592540b124034040b00400c1081000307406051216004500100b03005000c1c01c2c0d4030740e12002808001145800700380d400c00e50b4149140304450061085a04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 334626124 1250 334624874 334624879
    0x507030b0103091226090705010305090a0302030703080c0706050a05010302090711120915030a0c1e08060d02062a0c01080108060a020309030405120a030f09060c0f020307080f06011a09 81
    0xa0080311010300b655601c00350040c05c0b507407440d400c2e1000c2082c0702c101c40d4280150f40b844014070b0a2840e013000101034500041c840d03c01d60300b0007815040025000410b032542d031070785800d0180450b42c0d498543c0b03010b8064a0009481d0301d0514041c0450000745502c4103050301d000359144aa281c1c0c911f58140c0741450402c3c00d4007465841000b20802e05140c07c000703460308080c0100001e446044841420815801c1a2409490b4681e620304821940b904800100b00107010851000c0901001da20058000b10000b05201d00901204a14030115070310001155030f44110705e406801c03c04858440101304100203d590038441c400c600112415600074040203040700d90740300092849549444001d006900050b00f6002c5911040c000032803030369035614910803400c80c15001010100c00c2424018001c10005100c50309000c052300051000640c000c2290351002d802079850000c800d01071004c2440c0600c245d124405a0085140103803c9400103e0762504903031029207511016810703000f6801c26882040f82255 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 334627374 1250 334626124 334626143
    0xa020c0705090411311406060319020c010603140a0809011803021507061a060412080c03030403030204050901060908330705030a0e010b0a050411070606090507030b010309 75
    0xa82c0c903261541550041c070a007810504d51060360041130801400c0815030300038040c9a10942d400c0240c0350180400c41c1c260000c184507114085250861450000d051140210303c0000040c4038410070301c0301500c10754400c810455481202c0d802e810700034030090200b21444101481381c03941e14100011030080c0c6075000b11001d880c24030000f00644445c80303a43c000c0500d80901d0f900000c09a84c0b8101c004038544c10031306980e65a103c542c58a03030111001d0100002c0c44002a65a198060b110031081c1c8055680e8146410741114040c10000e02d84c0c06100b001c1069484008100810941d154001d40120f60040da900801a604c1d11400c2e9001c0c4c40c0d43c0601042d55214548940e41004480380b0641c0b44400110304907040f131400e6000e8203041508441c6c140c0401c0e000070904c09610424861701450314503010082002451f201c000800d911010f20405d0702c116102d018a2070704400c004100c2d854035900810401030b40b40c0e580c0403003000d490200c40801c0400d1030700c034800f00e00354020f02508016590100c0d0b1113 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 334628624 1250 334627374 334627379
    0x11112011203180311040b10021f0213090209150705030703030b0a0b07050a020f0a03030c060c03020c0d030b030106120b0f190207080903160b040e09101103040201080a020c07 77
    0xc100082806800300403600300f40c5604002070203003c1c0041c6000c1d06040051002001c1404160340c800c0200368042c602d02d95404800b81c0e4080f50700c01c06100c3c214031034041502118140d601a0099411034403000c0100440068480c050b0b90042c621482d0035241c4110a030300124180204d802442d201500a40040110200081c0300f07501648085400400d4132040c0c5031141d074088082c2c1c0201c141240c00d5030000c40184250728010541c2a041507045910408850031540c00800c40701420ba0020305158036200540d0105c1d0194050701d000c1c003c0e04040b200400354a00d030041c0034013102583c0c903000e54641100410064016500700c20f80580290a804540e194400c0140241c3d0300140200042000c041c02013080d4543c4c1d000030104980903422040d191000841050f0500c0e90550720040080141d24082007001544015601240c82c106c5c005121507841c84d04960800c000308003641c08a900c0d10034503202194542c400380d07024034000e80e20f0f1482c80c0d483c86410401ca02c070703c4084040c283e00c100800c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 334629874 1250 334628624 334628639
    0x30c0307050d02040305031c050114130914060a140106080403050a11010501300b040206070c0503030d020c0c010f12090512030408190c020d030e060c0601060f0201111201 75
    0x1140c00500074503000346041c0511200ca81203070001e80045a030380d0000101201801e8032101009403e80b2154010403855240400b005d8140c0d054568460291580070601c4803050000d50101c0682900100020303001c03404443c005440d40c2044079001d003164a0450048040f03504440100d068801d0741d1502000760b02c6903242911a80c21149581c810081b0458059082100030300070356008009801d01c0032143c1908002405080c030700722b80f01c0b5610f14001700c01c04d00411542c003291600030746c06a41d059520304d070501b000084140107070001c0b50107100005e40c0c682c030900705600034452100c419068654083c0c03c1c0c0011078a01500e07010001c001201c3e155103d1280c1c00b41e0f030020900501c103400b152510034011140307601e2034008640c02d441c008000b060b40000c0b007440205001822810349802c2070042c03159400980d00d48070075070001d070030814000322071900391711f4000407607408940040840d8032941e50b41d00010201c00d81452440010f500380354131100c0350b20070703201529015820441520303980c3e07090210 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 334631124 1250 334629874 334629877
    0x703050f0117030c0d08150315150d060207030e0907020d020a02131425090b1213050a0b10050a051305060118240c11010807120f0504110108010b030c 66
    0x10b1141c81c0020002c0350354449080012240d64801c2e0340311100245008104d0600f8490300442ca02d00907000b440f00c41d6982d84000b00e41513403248085501e801c0d8a014040403604540000ca4002c2c405440020303a4414550412401450300c10304403051842642c80ca042240c40d00c00201801c0c0c056401842000300524080d41ea503010a90340d9030700001c2d03001d0300d0303a8503d040b180140c1c1c10361100e810807520508190390203510070070321900358240f20318114030b08208041c0a10800124000440e05140070404c0d045285241c2c0a4540d00700086607070102c8542082e21220f9010303503510000070190301001401f820078a107020100c90000300900103245108001794046c00000300418100b081c075845403149000c85850040103000460610f205100c0614020207a85002c00d03c5c0c5c03011b00986142c458001140e400f440d120b040400e192103241034403925410f503401a0b090b140f50b140c9604001b1442d40180391917121900c03231030003159440c00c04181d205c015102c9680a00420301c40c042d041002622800c01c440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 334632374 1250 334631124 334631159
    0x90d060c0509040908070c080105090703080a020a020d0b0f0109110d0f0b06120f0106031a060702040f0218150304020d1e080d1d0d0f0309031209050c01080703050f01 73
    0x10721a2500322850002001c440d2104001c40309130401149481c24882106560805086050002c110900b407014109070380f10018800245030540015400c08030520038030a110506034090564001c2c11414070f0020302180707084802414041076203000044203602801241c85201c1c18403e001e10b400801025203005c0c00da15030714004140c1d1284005070040d21004014400c00500e9260712055080c05200050006810b078004d404060070302000c642c00c0d00d441c0e441c0b00302040c01140d0007603880c0d0142c40481e014180031651390710918404100d541082c580440c1280f00307203c080b541c034807000c02c4a00304101d9900041c2d038083e404c1074103ca00304002800140d040d07645a201c2c2e1000301c01301a07030b41d90361010700e40c4000300110201c4d4442e10603030030f21010484481c82e40f0b424080034284622160b5001000f0205c0e1440b010200340d02e5490a505060040984909962140c201030114041074208260380d8407018a81500080007240000c0d903043c4207108490152001c50302c1c42c84981d203020b2003d019080c4e287c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 334633624 1250 334632374 334632377
    0x40f06050c1603080913090c030f0201020d0305060102060c0304150c020313080a0c0b03090304030b040f06060b3606070b06010f0503040c141f080f09030a210207080c0c090a02090d060c 81
    0x41004e80046848460400300851044030ac821011303055100080c1045841d5450a0501d0304080a100c81a0380124880c1c0e44281320044007500d9a81e04d08041c1071042e41e46445150043c5080d45009407181d01100514440b04115801c4040950f2004125079803219804042e00d5049000c4052141e101d40310019a0002d0448084906064030b0f520740d021000c0701aa03003100c0940c40348801c7c5042203107a0159000900c2180f9400741041030898070116030032484643d03911440404e6660103080314403000540b490000c0688000e0300c0340d84501d802c4d030517048240c2d0b905011501803000c009040b88201e003101d01ca070350b0290761041c266182c800003404802e1000c41403035114640c21390b001d440c00410b440b0501c0d00f07074440c1e50b0f0405500302810b01c020712401c090802d2500b40c00403c80c01035095041850343e000203000100c4021144c0c244c0900500a0084000c0101500c0c40003840044000c5d0020f4166010b28007241d201c0095101e001e00a002c82c40386885860304030959070100c2021900c254481509640715 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 334634874 1250 334633624 334633631
    0x15030102090a09020702030d0c03050307390b13020a061103090d050d0e010509060406210c020303090709091104050411121b09041115040f06050c1603080913 69
    0x1a40008407014100e0f08441012507000c600e480542c5020007154002c54520f04180d524550070b918014060310004101000f800500d40100b900700320b140800c038085210b035594081400380035160081400454030f80640e03450b141d000c08190064120f1507907100351580101501001e61030400155030030a0118121340181c0400d100c0c1d40030703030388507488000801c900c1440508641c0c29015009803046c0b141c61082410050103103c4000c80380c980404560684809040c942118003081800703050040b40b0b5034441c4103a41c00c0c92203420b40580c0000103180226198420b98652589480d01001260348056024002d01e100c92a41d11007410540d05c016002405030140741c445459050108680f07003194204d0007515403041310000940c1050151f1640c1c0303c4800c0301c80380105e08003600d2b21409051000b0038144035070380d5580b81001c0c0d080c402003202c0060505801003104141c1d9850f014105802201c01225140a07409030301812298110742e810035a540160302c50b05040c4040d06000c0840b02c06402c17064071903603 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 334636124 1250 334634874 334634887
    0x10140f0c042106050a14130602040b07121710150c0f12020d11060f0613090b0103420f1802011404150509010512090a050f031215030102 60
    0x1401c11421000b0190316684240c04803620304902211401849610341e01d01d0040201d42c11200080500d0b0880d9401a2440b0038070200d04250009114a40c0040c13071401c00014030030100000801800e916040584500000300311940400704162800c503490480d011801a043c803142e211801500354400b80c1d817804118030300d440c2c0d903144e0300c425010400b921108900d400c4540490350400082030800414a0581c03002ca0650500d19074602001d0400075880e042c03440010308517110000044800c0c490b0700d2080c003407400340381008844028280000c1d601281c0c0c81d08111039103914024034004421080411040c5651448101010a5004071000307103880c2d100ea100c01d0000c02c00c0e0045800700070307414103a0420017207184009010640181d12044600d40e09110400c21040f0081410081c0500c50501542c1c600c5d0100048480740b040c000301015040b65101400701100c40010b040c10800e1103042154580015140c10956a0250301025001c0f014000c0014020106240b000e00d03490001600141c24480c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 334637374 1250 334636124 334636139
    0xf2103020d12090b041a070f020705090604140a0507020c060a02100c1209060609060909081c0207121706062502041d0615010905091f05030303130510140f0c04 70
    0x9000740c50688403280c2a0040c6c20f42c03402007811103900401941009042d00781908806504c0c1d003101c1c4180b5104540c4080040c0c82030311142c0000e600c0855011030500035251060681c401004140c8104005228500410100e4101003046480500150300180425055030300707458080c11341070000384104020000d00d90903a0646018000c4014820318011441c2d906019402d0220f410300c1e800070500d10b04045560002c20301510031200150082071040c442d0405110341000a1321030000020129610246260710460303020503c100303400d21000e407030701c1e254660700c04014647c051310301e0076600c21070220400c00d10b012040a8a40c43c031031003c1e001042030b44026074200c03c069200701d03040700d03540c00441c10410304900d000b9040901030024202008400e00741008500345100040501400e020506e020407002c0004880304001000003c04803a07884c07501c140400e902c4074203070701d00712034a04c159100342103c03c900e40100303289215104c031000002c1d6141425545004406030100f01c00405c10070002c034911 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 334638624 1250 334637374 334637393
    0x60d0210021c02030702011b0317090109020d0c060201050708010f0902300f07090803030601030509011803050d1d060601050a050d0612021002010506030703080f0f040f2103020d1209 80
    0x2103840f074000c1c54650000c6c2c0005410070304e49910002c0100c2d1041041d00010f50007408110310100d80d950084100d80c1d4501450f80104044800a035000150180c51010801160705042c151282a0700030300513900d40c180159441002030203803100304820741c00b050061004030303809051206121920704011600701c240340c40030040134146103c421a03050f410400050340003882e080e00141e80d031900b140207500d0000115105d01000e05440d040640300c4011800c6504250014482e0141081004036601d1080ca0082e00d036900c9810f4038a03805081524800540260001280320383c66000c01503ea00c4c0d0752140115070720341c030115480e0b0521005121071507130b0102520507140130303203860350130035481860600401c0140519040c1802c1160b041004100e10307600c01040c06801c4a500103121500c074400c641c0c18030b0542c0180f156880d09801c01042c0044c0c4a829aa100000c44855031950760fa2121300402c80d43c1040350581001e00903900c5480300c403144038800c5400030390204207110006a45c030020f94465011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 334639874 1250 334638624 334638673
    0x20d0509010203040309060503090c040c0c050d030509070906031a041703041103120421031115060f150403140a0605042405060d08030903040801020c030a020f06060d021002 76
    0x180e80d0b01008110070950060015806081a1300b40603045140c0b0000f03041c4c0c0d80741004a040d0055450b261610500e6014801d004405640700007580c451450121004008050031141003000303104809000400c95810311526055075000300da80d083c0746040c240591060080548111016001001312246141ea468050340c021403150596416424010007014608000b201d070305c1c0740c4040100310030000c07901c25102a220413103551008540b051954103041c0c0320712a19180c00d0130a0301804401099401d50060b015200e52411503503d0152018042448203000380c8000803001000204001e0002c40c080b0a40a080c284998040701e06541d000c0e40d50710709540c0151001c5840e800042e80c0300e55044912600000c3d00c104500e802c210078a4500005030b40c098503140060203030305001000c203252080c103108903000391016070000d541c1c445142c40010381c0d80c0d220b1402d8070014001c203042070b4120f801c00b0030301c940110002000d0b0101444944c00300200c0c183c003c035810040d440f408109580b212040500303041c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 334641124 1250 334639874 334639891
    0x32a10111b09070e1f17010e04030912062018041518020405190602120415050c010e0d09090b04110f031819060b03010203060102071503020d05 63
    0x200c1115028828034064100d85004102038041e0005880e0b0b44400c0700c1150b00c02c0c035a00d400030042124a0105030030f1042c0555084189840c0c00c0d02c9404d01c1d0b0040200041240c0710210100e40342c0c2d07a0740c003815550000f036070b008001030380750b24040060785d1840210300895030190800049103106400582c0c4000c0c41111254504c40c00400c90031401c0c005148400c9104030151001e1256140f035490703035600d486082c01000c030903c6e020100e24550b4202a415900a014090301c070301d0b58001c05003a100e00311042440f800c0018130503c008880821885019101140d08a515408040300510816903690700092603006c095980c0d00c1c0c1c102034402c010080c51141c61000e4445040b0a42400c586500703981c2002541d40c040c40c205503060b540e402c031140842c0c00002250540365180d8a40e8150444100c0d0101100041d601c1014000614400d04910007400c0c1e0384190f8040016600c4081810300381d01044408502607009514104070700c5031400d031000c1030315089280051030000c1a02c0c2000403030381c3c151000704 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 334642374 1250 334641124 334641137
    0x60903050f0301150801120f121106130623060d081c0509010c0507031d0a080a0510051005012001020919090e071208090102100509011401050f032a10 66
    0x2001d40c0c00c010601c6c0580050300049146030150348580f2882000418002e068842401c1c040360118450025072100300303861400c0d1900d0781004a8030390421282440107680300c80c54802040900c070702b09000740c9180c00c41540c00c19503e6440074208020316050b40c006594100b8108034030140386041c4030300003c9101c0f07081000035880c10101c24613402c44010b1040402480020071a200c00700e40c01810760222440034039104101e0001c0720300495200360081d4400d14145c41405401c0c0c007080f01c04203a9003202c400031902002961364030b5501c03c041e81041c0c41000d0200e00c00030711803221903117203210074004100824000351402100501207075601c1e0031546030001d0f81071206018008410070340039059103040007000900009003081d803c040ea148143c180107284c012300040d0301d04564000d0141d02005400701c0c800308103520b00b804060b0b001c0c10020140e4000320500c103002040a1406251074107007a00068000c2000580c1206a4598150415400302e1480c0d442d10b1560b42660328900748824a100340c0d600d61 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 334643624 1250 334642374 334642409
    0x30139030b091e0702070f09020702060436061d1323060c2a010e010906060e2a07020d020a09090309060503060f040b24030106110c0d060903050f0301 66
    0x40f2011801070584c10840d045144100002d03206010074200f41d41300d074070307005070707190210f20016865216990003051507c0707140b002c1d00417802d03e07485e41c505002445800c115542400d1507215084480c2030140c1d41c0c40c101e40d0051009820303000300d81543e1055801c1409401c401880e110240f100f100c960072060b1401130071241d4065404240045038100c684a0380c0c80d400c0c0141d82e181d071038040c0c0c604070884041c089540e401140d01c420940101c0d0141d00c0c6500200702951290501c0307800ba06643c040e0704030303440c60b19001c40c08140f8009031002402881c00400c8480b0b04005040411a80c4104016a4080389020020380545d95440c1804001c2005890002d00503446117005020220aa48920140102417082207059102c103500340d041c103981120002881c00c1c0520004055551400c4040c50000210b01ca12101106040040d416075095071545004400c0c0454190343d200b400001950300039020404500004045401c92401a4480e040040c103006401e20014281e4200760f014034640300704000354 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 334644874 1250 334643624 334643671
    0x11506020d090e040b04020307030611032211040f02130e07030e0a0302121b0a1a09031c0203040221011a09060907270e0105030139030b09 61
    0x20401036010074288440400e19041d6190a50383c0300900192060020200040846d501400458041c40d80b004040100c0800f40f405e05a00b84c00c1100c6008140d5072038424403401c0071044d642460425032100f40d1a4409050106000140c00401000f01215400b8404030050004c0e2001c0100030f44452440c2c82c00038544040c0c004c09481d8a404184540c2c0c010000310300100b580420030905108502688aa842000d0301401004803003081681c5014044d505c030039420422402402c00a04030040303010b6505440b100f03981c54817846059103403103c0c04003056900c0200707409a00659401400288500030940d81e05842c1c015580c0000311260365655149001404480c03000f041a4204505075a502c10524041010821a001c00b80084017400100081840a4041c1014000c444c0c1e20412a03c00c009546050f6071980da8428002d041c8070394245a1506e04412406060030b00941c3c8100400b804024000e01d0324107243c2c0140302100c1055210035907040e8035114840c0315030203107a00402c03100c82d0a684052 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 334646124 1250 334644874 334644883
    0xc0d0c02130501061b020f0d030f030c02062802070519060501081908030a09120c05100e030708030c0d230906040503030117070f0e1008010b01020a11011101150602 72
    0x1150141d246030800500110703030700081c0c003130a513100a2800008a41c0900008414501c0520070583c006030072a07100c2c1c01c00d9070100702808180c0b15034500340060448800140d0300d81e801100c95542c51035810f00e111800c21541c03031103003499034100341005181132a5074072000d0901580c054a41d035006800141038040000d14441e26004151007005445080180e031100006500c4600000d030003a8404008034110410a9000c00d12841e400a42c1c005500125200901240e0b032580059607540100c06d0101c0000201c1d0140b00301040c560b50143d071500510385d981540582000d000318241c5013061104900308103491240e0702150461503213140d01045010ba0581905030014290070090f00148180702c00214001300340c9042d2000e41440004109600000c0391a140075940b011180d500400030004031204541c02031401270804402090440c0d0700d4086840c20b0700c80c0c03410818016400403422101040b100d200b0050000c105151880008010300d5866081d600d00440c000c00030900801d0800101d0780401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 334647374 1250 334646124 334646149
    0x41e15020d020309010302071a09160e010312140417010218062706090d060e15090a120e0d0606092f0a050702030a0b01060e0402071113020c0d0c02 65
    0x801881c0d0000c0d0094000d449002e01001c05051540220f512300422481c040080c06814846c0c4240c80c0b0b51904620301581c2d00e04101c0c0d441d085070300002d000718050411056a505994001c0031407540c0b90b130700c04402c0340c0d5441d20340300351680d02d03c05103c0030420f4030001801e80c4644031040005a1105006100b01c40c0c0c0d030820750003940c0304d580104400100024030280a445100345181c850400c900d403400401e03172030b1103104c0013035600a107410307808010040e1507070082030b64041c03140407920600e1320381c0c03400285c0030400d9406859139880b07980141c0005001c14424071307007550f4a05d0300404c03051500c40450840d024024013121184d0302d440c01800745c09020311542d02e040e0320880e002403401030005400b20b44000e1034149a405001d002607041c54081c09070003280d4001d0303409400c95401c03441c2d90905c51181c150a0168100040725001c070ba840c54603003402036640c290380025000c151403208100b005404003008000141164003405104039905003408100d0502510f601e80c5c1e40c9201c00780c410071038540580c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 334648624 1250 334647374 334647377
    0x3010302030607090e0615160b100806061c030315090504050d03022a03070c0e09100902011b02010e060a030b090c1201180605030717010e070303020d050708041e15 72
    0x280c4200011600c105c503145c3c00150550741c0a1700f000068502c100c952103001e141d0030044802090110802600d000901c2c4034840c1440043e08083e1a2590740761101e100345c80c2568000000041c0f100000c0300041d100401c0d078071a042c001240c4003800a4012404a40d0340001c20701503840007003209000c8140091000c50340640b800f10710b0400310785a200d542c0c0712030080d2108400160504840690801c008a524498118100d6800559901e43da41540e4604903255441070240e03e00011103e109030158204003613051319032040a1064011803120b201c0f0033301027a41003004482c501c08041d1956402006400155540460000b05107018440c201c0000750203265441c00070000015804824a01c2d07038191005540d441e1050491030444030040c20507038200560500807a140000c041c400a140405c0006141c0700034007000c80103407101601c441042c4005805038010380900c181a91160f8000e28006114540c218203043c2c4a40c80018084184a080c0e503071036042d908280800380c4507030b9800c0c454941e103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 334649874 1250 334648624 334648637
    0x31208090a08030c0c01060810020c1506130507030f09050c010315051809120a0c0618120e0301090501140106140c030a031a1002010c0e040603080412020d0b04050303010302030607 79
    0x803956000842d1100801380307100340d90089058105400290004c0d40186503000496540100ba0320114000b544008405031461168207155842da001d201d2041d48210002401421100384803c8044080d010081c600310070540d0750420600d48004600c1010881030055005001d180461000501166007401404c84144080d440070081c030750b140d800300c1c14050800080804c0c1a210b40c0c0c5807500e0301c85083c0425003810710114600300710703a40c491040040703540a114207109103405000d095910744201400503004c190000140c10751940500d007819501507002e0f00011700d08001317455007400c48911042c00c400d1000004010400d41d640140c200200c40c52940407180340840c400c0c00c9950300d1103030303c402505241d100e02e0040c0120030b20000c51800c1000c090444401d511070700100900802d10507091201280f082d10104003607040134800c8a0580b0361040240b4a494100740b0418501d10880800300e901c10b10380c20400000030900c1e503000b402148110000c549950451041608051000b00130781e041014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 334651124 1250 334649874 334649893
    0x909020f19120e010212060607140706020f070f060c020114040902070606150503060a03060b01051c020d050a06120b041110080106030b060909060d060908130303020708011418070f03120809 83
    0x4415900c41d07041f404c00c0350b1a95454140c0d24049405c400400aa90707040c4c012190002240380d00882e03a8080e003071844094440c05915481c1e12100801c640c0903103400070b5030454469005500404078402c280903686004c4d0b0a041d9605003030010382c1d100ca1411511151103001c00c100301c54007122601148403150400078210f10780500800c030019000e11010380b00030744544550711207074051422540360303c5013440e18441340c0f0b2040b00080040d6101c03545400740d203840e000000710050318504c18401550100607121440d5041c0e03403078808440703101407c19500c4019000082066a0714849000c242011648490201c2d41c5003240240031200000c18181c0115410084940741d42e0381c0e10801503100070126680c6000070418101003004050b550300040c2540ca00080018400445400c0b00b41160710a508440c03956171581c00007406e03100c0361806032581c22003c101099900350b880305007402569504c2c1c00c07122026680e58001c500c1c40b50950098450710b05802c402d82c1040d900c451503540c002c00307402c014100c468 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 334652374 1250 334651124 334651147
    0x20c030304060c0f08070209310c060f02030f0a030506090f04080316020c0a0e0621070e1902030a0212010b1e0306030a02031c020d09060909020f19120e0102 69
    0x1500d0001c002c02c414403507201340c010490180107950380c0075000b80c1808078070b1411040410710002004070000a802515039601e42d00701c1c44282e840c5420b6880782014003001d10300202600c51060000e000c40c19030209201c0f10440001c1c0001600207812555001700c0c003401c0c808180049114081c0484007000600010000401c0048040341e8200c0b80440149202c0315032204100c0c10306403500107031507205800e41c0c4001180100b003440e184c0a8281103460402880401010bc1000341e29140200701c00d42000714100006d5009040740e41e40080e01c1c01c0f039181003110f0f01414008036481151342e40082507000c20310301d1030780d05038483c0035000d0110810312901d00f03402170040c0000d8100c0041e02c0d0524850010000701c03d9101404524000b40d805400c4989883c0020038224202d820411000f00501c980303082070ba421032283c3d9041c0200e4040e034444010b03280c201001d09010354400072405030422130400803500603441e249066201c00b00c0c0c540e100d0500e08180400c1c0c0080d9242514a400a42e00510414680e907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 334653624 1250 334652374 334652387
    0xa06140306010b07150212090c10030c0813030c050304180c0906121104050a060908011407141608030f060102010b150f13090e0318010215010302062802030901020c03030406 76
    0x340c018103451000c10317802c1100b0b40a031050300c1d4400b5040401c80f0600c4641e150010780504405801c80d00030341c524912060440848113003004200002d820000030428014030714032a80712a902915110801d0b80c0c55888151441e4840c0e0311008040b46440c142403581c580d00c1c4201802c03202546807581040d46004401011400c0b4034018111240d80d0794640b411002a01040b41c0007480040d001c1e0707070100c0ea110b03c041d02e4500c04c0d204142a950802051007008140c00e0351f203a00ca20019140d03414540306100006031503412081c903440b100950403a48502040e090720241d881003902d030720803c0703181c43c1c8013000900b0b54049a44d11ba02401d0301c0e07108800c000c1c08020556504e0238440c0200340d110b0000e804e45001700c44107540300c1111540761020919601700c0203c000d240a0100a00314038801c04500700480e61407444183c12a80c04401d140140010301d4100020300220490701416080c560350a10805034a41c903412654003d80c0c8001a20006540c062050841120045001d1400c01d031400001401e038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 334654874 1250 334653624 334653637
    0x80a020105120a0b03120901090b040b1902120712170103051903090b04030501141b03060d0201030905010c020d020d080c031602070b07150e031e0901020c090a06140306010b 76
    0x41c122100b00107129071109a02c04518010010212180c401414020350016030000c191030780001c20400d00403603a00148001c0724200c0d501001c0c0300c2d1510300900a000c11611035011030070214000d402c0b815407140301d44409000c0c031600925208544107401140644888419903403406800d050070010004110041032801c1c3d682c02042d13070f02c603070b580340c515041783d03092083e800483c0659404540407003800015440007041142c801200c40c41a12860410079840018002000011404100203106030620b181000b046a106040201e08502c031680c4642c00e540c802d00c00500140c4c801669818020f504014040420344039042401e4241003a2481114902c0000d040203241409401e0405031140b081002c1e00c014481d041e2040c0d10384a03245070084510000c0d04011030461305007510041820404811101c118045e50103c280c04404c0340c1c20100381ea000420b80c541940580d0300040c0040e180d441031144101074030640003c03201e081c00d87c82c0282402549080e4001d6001c400117100c2418540c084170304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 334656124 1250 334654874 334654897
    0xf05031f110904050408030906060d05030a03150b07030c03031a010215100b0309030406121b0309020307050301020c0624010801090510050d060f0e0c1818120c07080a020105 76
    0x82681d0010501521485125811070f001880c01e01004140401c010185010b50300d00e400745c4082e41c48500420070480d90f509400b0f44076800410881c100580603a02000c81079540c0603500d00000c0eaa0003012559802003841075010a800c0d155a030100340d818400c000c001d00078a0424250600b5900c0000d41d2105500d11107260340340482e0115000301480b0980078010007009030125078a00c1d0101c5036949075000340c421400400c4400401c000700100038002c01000811303141c119203503600c0581d8210084c1c000e0400c166054001c1d0000800d60391020b000416801d007403030006002030304000100303450300b50b4a1030054909001c000c0000c403084e0382c861002070459031070382400b0542d0b496052b105850221203a00c5540d2000b29100751108105c40c64000c000300c050312501c2004614441244151141811281d460b84011000d10302c1071128030303980c151600040c1d100035441040c0c080c0702c0000d107001c0701c1a5103919196404610001815010450750028012103c0508070000701940003800902070808241c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 334657374 1250 334656124 334656131
    0x150b09061b0303130c0b040b120709030506010909020a08010c09060f120516021b1521040813060c02090f13050d03051005060412030311070f06060f05031f 68
    0x24401c000040d440a0002440c800341e0f079403424941e80051948260300400c45209041e00000181000740c0c07020307241151b016620007440c04034a40241c0710300b1480106600b007808170443c40800030a40401031203020301390303103800042c4d582c00c10300400c000510903601142881e81402543c1e42c2080c1d0104d425421601c4a080c000d10041422000b0303a044050001c01409003841c280c100a02e05898400400400b0100d0302a0b0b2200d0342041d4601c641d0031004414590003250740a59520a0b680d140010860f0030b42c400441031422024194490140700c060320b09581d02c0c1c0b00403417484110750040c002d0138014141170800946000b82903011814140740281820704001c0300b04005140703200c020458450650f4002c0507104400248800039004043c141c50203000303200c41060204542c103001c0c2c1120203407149030703104000500c80355504030301405114082c58412001403014500141029003c155124414140418803d080071001041c01c443c9900c81842031380b0410345d600d4070744c0c40c0c44010b0f60072240303501010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 334658624 1250 334657374 334657387
    0x612060d050f1b03030307090b0a091d060316030c050d08091f11071202090a061206090b07141902011d01020c06060a08030406080604060302060a0305070201150b0906 73
    0x450366041400090120701a0442011404001107000388030740030420810a003800d0080285940d0f80000c950000100302220b400344540c003001405030808c130070540b8100c40342e41d46501d901802d02e00c0c80d8111040101055081c01203e02d0b06000c07042400c0341049078006c01d06d2452700c0e202e24402040c45400c0c041c004000404003400081811185400c0010f00074900204400b912030500310060311031000050708841d020200000085481c07004c403550510003a50340340c0701c1d40030004d080d08080c0110005e50364800c400204c1c0752003000d889030814082c450000350000141840000c04500030008010031041041c090914000601034403d2107480282004403e58029810303801040b04001410b070301c140d40c401e0b03200b84040540007000c5ea000040305440f04d03511043c00307005164400c0c1c020051036030006e2005000482c403c62a41782d1240c0020300101d50b8542c2c9402203281548448070620000f6140d0b0100300c00b1a4090041080c003181d007100202c1c00e41e10b41200d1000741d005041d0030030f00c90013000501 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 334659874 1250 334658624 334658629
    0x40b07030219050a0204050a0c02070308130f08100e0105070914040f020301230a0b03060603090109170304121e18090e030304051005060607141f02040f09020405061206 74
    0x1c102e010562240d03549104568246159580d2818a080340f10b0b80c10100040e003000490300a25806400300d8000301805070459884c0703a01034000d4868001c22310840840010b481d071a000c0c03185e005000880160041e034060100c001d042c0d0700f28443c0341e201a03052209000980e1360220801342240c4110052a000c0700d040c000107405403c1016544070b03001d001000104101e007a0050265904803005180b10152090b1002d00c50129564450203d02d80418000a0000d09001c00116400440400000f60005180d0ba804003030111050110f441c0b19004801c200c100311203850803a03401505410a8109484c141d125244408550801c0c1c20810140c0710650f110f41d00e42c2002e8002400000c3c0090222500394070150781d5a40040307030250f4040c0f0860024990101d061b10135540114006404149000b44a8451015400a440c1e04520b18400c40c04146e80700801381c00c0301c034001c41c001e03003000d03070b40c0c6140180000094415402291001c1e01c100400c001c035a442030300310348030000e01d083c100f109035581c0d500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 334661124 1250 334659874 334659883
    0x90a0207050d0201060503010e0f0c090603071a120a0b0a0303032c1623150408010f05010602280b060102070803040303030b040c08010e0a0e100e012708040b070302 72
    0x8018078074070411041d64250380d0190812010b5072425402041914004800c442c0d880e1215240340080d6040825601028100b0a294507400403000d0112000c0543d0740542070800f030700d240624001240080781c400c2c0400d201341c0c412500102440002e00a00b4038000c00141922050b105c0142415641d030b800309000585802901d64828001254501c251161820030b074607800c404614020307650740407501051122142d2203598500c00388000e440280c035044814421110054000d07800d081e01d00303000024400b0300034021554420b003010720114507949040006454003604103c0c03811a40c02003203c0c104c08850070040c03e040f041e0010380b200f000b9185d02c07006034140100360300044801d000c00070f00842859055007240c0781d0b401081d0750800c014480c0f2041110000b10a0190000e0032141c03a020070100222600100c0701e91030400241c42c03030103c03120b1a0f40308440070f0382540030450b51542070690b0024400c400c0c0d07a401d11010750008076118240d5a030036400b84158010003a4998010400c801414800c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 334662374 1250 334661124 334661137
    0xb0a0927030f0c051e060f090102031b0a140f0c07050306070c060b0a1a04031407031110091707050a0905090a2402031015090e0a0b060d060e011505040501020c090a02 73
    0x803100000c00130407003c07511200c044171f02159529243c00450b0005030144202d91055a520000041405601e51650b000d980110950400c02001c0d0900c20a40c17030490f00100184951180800d07030310481382d4001400c1241c903038002031080d003060003000001d13500600b00020b42c1e5800500010b80d05030010000f40e4000f081e030442019800750381391750440c6100e180d00400c2600d00804440c100c2c0c0a0303800d01240d0381d40317450000800229400c8040704160400a00c0d90760f0084203405c0000b0441c0e210140520100c06410110180340c0c800c0204001c1810b203807045601074048003409001501c4c001040554800418000612142e05566800103035a42010100c1c0c800c51440c00555403820108080e2151140c01d000d000d441103075800c240b0b2076007800f8203500c00441e6031a199000d816500d030304420004141e03003c9080d0300500204904203c3c18107901c05c0201030029910021202c1d410710118000905100d840f20041c40701c204800d01003a078002408021000302220044a9559400d071800c003e8040c81 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 334663624 1250 334662374 334662403
    0xf03070e0d020f0114131706010807030c0303031e150f05010302040e0c0906162009060a0621060b040e130512031e0a06061b110f040b0a0927030f0c05 66
    0x81c00800c1c0c7e01400c0c001e02e0000050300045496990720f030003285803186190320001300080c00d003c00c02c01c000f0b0300a800c0020409020030462103000b8405041000303450000c0c28502d45131103800c00600840c8506040200908400c1c070b000c608041c2000c4134920462350207004800c1100d00880c100110313580b8501202d1081c2003581501c035040e071080c9894151603480e44c42035418850b042d0328036030301070801c01c03c15440780343d0040c40340f20003526002d815920903071141c140c078401e019980b007001c1c4c0500b280d01409c8024025400340036643d40c60f0003030f000081c890151000064030710400e503010200304001034082d0180303501c803515566629150f036145001c4004c02c0340d07010b81e900c41408020400c4a2035001c1421548070751103141c8500500c10004000a00c014002000e0b80c441d21190080e0f804c0c02e00a848686201500010351302c00b02c1e000141c50200c0c5540003801c49521114144c0791352000070450071103854071000308804c002c0d0300e0703038080c2005510795804420409150036000a105040040182d0007070780 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 334664874 1250 334663624 334663657
    0x4140a03021302030f0703050c0304020d020a080a0b04060b010c020607080c070512010f0f020c150c070c0f081002070803130c0302100306080f06040c05100908030f03070e0d020f0114 80
    0x32002c40019400844005080032540800154118002d0144a1003042c0581c280c5140d80d440d98208407075150420420f9070031030100d4002040540d010044862014098101803925151a05d08407054926100445040004145900c401a2101c400b0ba40780281e00c907629645425500c0811803401d4155803000343e00005a655089c40d040041d40204400d030541ea0051007080c0c580200c00003039205644403841d0a5102234409000d880401e6000c9401580c12140d0754a01012500c0d0311103400c1c01c82e08202c002c070203264410420b80201b04098141d405c0192019410100b89840c0d45081d800002c018070b2000d04081e20742010890303050000e5025550052880002c0304100e2401801010f00380100c0c400c80c40b0302c0380e2131800d95000080c05449a6407158001440d40e08090510818a5100c01207009002c00c55001260300c3c842480503140c208003500e0826141d18000ca4010a4002c5c90420380b40690303907003078460340540c407900d4000107612428280f6003914901c03c010403d05108800c901120a800c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 334666124 1250 334664874 334664899
    0x5120c090c04051807080a020901030207020402030705090a0e041a0603010e2a090c0403080a1803030f170906180a020301050c0a112a0607060e0606040f020a020304140a0302 76
    0x1d600c06003054510070340d910707100804058848980f4041c01e841c140d0115078034100184014855400030030810106250160038600c4940c003250070b0b60816281040070030310110303902c1d440d801c2c00c02d1000010000d100503101142020f444200211199480303034511804080001201910309401c4142440040300840e003e00000102a805206845c3d28101068001c40211100c1c1e00c4c1022281d801400e00c035404c140340c1861669004c40310381c8502d50840511004080300d4402102c6004494000d40c0661900d003c0b03804114002002c16000d401d03030a000b88050703030910510200000e601c1e079003e400031400130b885a4080000340d1802942c0c1200039415802c103010848100300e0701c4041c000d03c000c01d0711501488802603c09544840c82040700c81d41c03034100c003a19581d000d4414402078880603001b4114a103080c1d81d0340c0f91903007954020741b0b03d0340c0c2ca40e029000b4414a400d0038854907c004004000840c1003202804d0004e481c1d10032407007140c010380c0c0d8030000100181e50740f0021000850f4000d1041c1601c0301c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 334667374 1250 334666124 334666141
    0x9110301060c120e0d0c0608060a031a0402040b09130b01090203070c0f080c0a1a0601020109080307260c09211b0312030f0a150b0a081003050f010b0a050a03050705120c09 75
    0x3440c1c2d010350000035881c800440d86e01c0c0ad01d24107080075294494490100603404501b035007a040c50052040c4ea000ea16400e0004e16502c2daa076100303004100071020300c0032651150900c003aa451040c1d0224100070b2041081001040d40905907450b8107504c1300300c01400050f81e00340510725004000b09042c41d8090b00c1802410065a5020607081850510404800707075110380040e82202c0c490800070302a50740030000102d406105181e50344480414002501641c8401481620034002c201c90300700c00283c00144103010713454034a94070390018080449140341040c540b00010780300c0340d0b00760420b100080003076215042540c0c00e209140d40c4c807603032040391616450100e241d80c0c81c80500b61406007407140342196044c81e0461408407d815038a040c00c0c0342d49000d05091003103d03440e8005100b01a440104800880020400c0c05942c0b96401140000b10300040d140040041240c500e40c0300b18403801d00402c0030400520081110011604204c0c2c0e40041401031898007424280382050465111118038200704542 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 334668624 1250 334667374 334667393
    0x2120109081c050f0403050f0d020d0f050915010f091e090b0103030917030a0c02010509100203040f0506120a24060824280f030c09110301060c120e0d 66
    0x114540030080c440b44d1241e10840c046100c0c16a03000c0c1c0064010031100f06d0021044000308100d10804a0040c907264009035410103c1781d0003540c0908980e01d6506000003c0000c100c0c42d500c02d1440c001d40b000304d500d44032944002494511078108800e4a816507070922032000001c41c00c81c00d0f0064802d0004245030301e09100c0c0142e00740402c4000c2222082c0215801e49100b24000110440e8001140b408411200954940421000c01c07810040b0402842e0300c1a1185600250f000141f50011512541400254004a041508181e005040520503a00ca00d41c840044580040d561440043e401c0c0726607200c104030040949041410045905001400c1c03076000380410302c200700c10990748803001528000d84403200c1500200541c001550100b00354658141240c12010103004249a00740c00d50714000721440030310310350040e00d50020407c0d08010401090003031081c041031a03c2481c1c91036040c0000504400048100940b1560f4100003040380903000301c551130750400c00201010010310480c64000e401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 334669874 1250 334668624 334668667
    0x6270a060f090e07120b0103170403051501080601140a0e2511010c08090a1416091a0a0b0304080706140a0218010806031504171611090c070212010908 66
    0xc0e11401c4c2c000512a5060040d9592640c0c0c48400301401d40d18545a27030010b200b0401401040e0341c000c110020014400300554525082214115580381d03151800903800c080301680070690a501d04988070103660741d1010901d003921413255140e16a510740390000e010400701101004241c0c0100c03e5034176040c0e138000014040120b01c1c100240080380d4903110440b9201c50076074030880f0503400910481c0000c0c2422443e541c1603c418002c5030001c20040521626842d80f585c88000da0079692184020003111104a81c4ac0c181801d03601c4450003403400709244e00900c0003c00c0a8030b0801e000c6200400c0102540062021055036080c1404a05188903010002d600010380d04c1c0440030411604601940075150300c9200b850020080e00c050240024007003c0941c0c010000c44000100540f48207112510b140900401079a6070b032880c58600440ca000410042c042250b98402e0404900b001841c0d5441021680701a5041c0d0300d407400036000d05085409003001220081011102041d903a00b00c182100c0c9030f45c00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 334671124 1250 334669874 334669901
    0x910120614100e030114160806060309060f0a0f021c180c06030e0a050a0c06200d14070b0c1c021c0216080406030c0806270a060f09 58
    0x4060340d0356050207100d01c50740c207071250800c40015206154901a1890720100354010f40046500c412038000c0032040c0108681080d10b030760701c2c0401c04201e0356000140742c0c5e2141d02031302d440c0e186051008101d95038600c0200321440360240500040c50a040a0700701e820022400c82040d0740710000c0d507140c82c202d07111109051009a25140c5031464665a554a80c0c040c035030407190000c001810400304030701130f100f070941607800c0340324058111002070010080484400d01803e201e200481c20000001e1040080a0303c40ca44286500c85007130800c44040ba00703100108883c2001c824840c2030a2412004d4000d602c2d016240100e02c0c800c0041000c0d6000080001010500704e07110b130300c00f08480c010224011141d101210559640710f6820000483c5c0c001d01c04462401c4075422003206a40d03074171040b42d0040e04034900098658081801003500200595081002100d0007401c0c20405d00701403902c001a148800d60140d03280cad022480c05d20081d030120000e01100303010366a405031984081d10140c5444113146a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 334672374 1250 334671124 334671131
    0x140d08010911070b0402060a030905030f0301090509030c0d0c020d230c030106030305041202060f030a0b09060d051005041412130803031315021209010f050702030a091802091012 78
    0x300082a14003c07030320455030000d001002611a9004c1c403040740c01c00d8410030145a070718601c0d000822000c00c003810030405209003250f40c0752305000040054403005403440c0201c3d44103006514044c100450710030343c103031714030310b000800c0d0b4402c1e00010b203007101070b11009000c0000e12821501260f0024113070344803080d46082100d1030340070300d00c0600d0308842c00c5201c0500052005d01c424413a440e403540c00c0c000500e00041401303040244243c0c0302d80c2c0075401551202a0303e07503950620642402d00341803140d40844210b9503c5011400c50b26a079495080c00a42c220109903138200250411a441445510700445403048964240040e00e5014245c0d1050701ca04e00511001000003a030781c100041101d22500c152068441c1002c03080e6225442c204cd100010603071a5000e0203e48a620030541c2d04901c2044813500115103004203030f00c201c0c00c894001d00200119002004008042904003004200702e5080d82078840f4520200110b8100a00410a845074410041c1480d01a0160701151104000344943c41c00c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 334673624 1250 334672374 334672391
    0x5040c0b0c0709020c100c090e0901141323070305011d0a0f050c04020a030204150305061f02070e0f100b0406020c0603040201201c020a0b010e04140d080109 69
    0x1880341c0c060700100c91540e07888507000344a0702ca00344c0c01801000001c40d04903030341da00d402c420030402c0c4c03812141d0792000290401810000b03800c0600e12150001e00300e40080155800781000c1200d84007000f0441c80e0a003121600c18810003503503107074288168400a2181e2a12503d0352440d5032030350107501c001e031620b600b4800003124007588040c0c00b00ba00d00d0b080000f05910300541c0c2c0c2e07003a9006142034086c0c0b510f004400300c0051607129030000700300d8003205580c016a540e06201c002d0040114644000303081503e00b10070044940c0b03410f40750000002c2c14004400c48014444800c1385042415041a4400c15070340c42171103501c420040c1003500450095110000e03564840a081e03290303005070301c82d15005900c40743da1501d00c2c0c18864001c41c0c00900614012445424401c00782034000e40328130b03003c146640604588020354415104143c01140c0300d1000d04010503158a4412120506008a112541003000894100324403d000c9500340340000c41a05c0e1040315000000d03003002c80c00d1040c90100c40c2080242d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 334674874 1250 334673624 334673639
    0x5040e1510030b011223040c03080301121406090c0f060d090f141506060a051603110c0f06190507051209030712030206040308330f010314011202130f05040c 69
    0x2421420010000a2036004c1d080c00202c48406d88017410940c1d441201c50300100100f4442c034000c50280162040340103400e030061900c48110114403060070b840d40c001a00f8445e03100004210782009903412502d24a107501c00b400021064801c01e0f0a00310410305d003140710000c00c4168841079280601039582503c85d030000c882076548481c000445102a80c0526000808614100c0060800303003d0518206007061a02c000b1200341c40c202ca041500410451a40414410f00810001c0c0d0a0407040c2c03001c455582611000c0b070a103005da01002d41040703041d009400c180911460a50b0702194008080726070804c403c049001e01c40c2d002072302ca50f02901541c00040f52055400020060181d4176034010501c582d00e41e141280c000b00b0180c80c4048800f010040ca5002c1c921100d00c2d5116038130040c0004034002020010000307c100958000c9041c54205150a41c00b5081a81c3c140c1c11a8491022252805030910028420f80200761900703020381d01c0c0840b003552150307242d840548514464030b11a41300a4503641d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 334676124 1250 334674874 334674881
    0x2105010602070b0f0702040c1101060b090d02010c050f011401141f050a0e09010b040f08070503031c11030406050a0b03010e07090c0c02152805040e1510030b0112 71
    0x50000035901c910810000302440c500141132281d10050a2400d04449500090544079443e001034002886107081890041003031241000030070303585807010725100700f400110703102041584019043c80110189074041c840c040c4007000045460400030018074400c403041e04240e40080c010a441ba44102c0980c440300d0610905074900d41c90000c100300403c85107414104d403607030700c08511281007248100300840c5a484e586d141078040c20b01f800703030b140c3c6450070203016000c4c83e00c0c942e000d884294480b560801041e1004001c483e030b00c60700305050380c1e01c40b0300400c00e0360040c0c50f1000704444581000401c2000340b0180d0380c03005024a501c0c240901040741110200340c203075002c2003036003450390b0007905042000740381d1f80d8003101c0e5040450420b1640450070382c000030400340702d002d862481180b001501d0b202c070320b4680440a40e141000340e002c0100443d07001c0010294083e03405120304640702017012aa204175500e1005214200050030500c08401480d070003000303401e002688a0200f12891a500000510b500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 334677374 1250 334676124 334676129
    0x20901050304150b0a0305010c031a0901031209080a03020c100216090216080d06031101090b0d050604020f1914040806060d0f02060c0c1302250809060a210501 70
    0x2540d03603046464036140c01ca0500c0030856011010b50b69004c00c4d088a841d12030092000754003d03000000d1303a4011010150903030700700c40c1c911038007911011aa210242c0c0c6820004c2d040d0398102c1c80904107260350a074142c4856200703800148540c419142a001059400034030120441e1081d5400c2440c07040008040c0d0791140c0031004200c1d1903c000c4414481038050f036014080c083c40c6043e46103071050a0303844910041e401450460090358a40a041c000d0008100035511020800c1c0f80075000c0c2843c01d6072072141805105648094240c845020507401d03501c5406030307565003284179402c95907036031641d140140a0480c1005600400c3e00032003440d030003800301c030b054400300c0d01080081c05007540c8402c10000a40740151003100c2d001c00300d04400c00036031584809082c20030001c10003403821240380c0c001c1000149484008480c2a801081005400c1c8100603a007001c3ca00d04644104008009203810f15160084c80d0895800407000305a1102c042e85c0300702c011100001c00802c1d20030b00494104903106807507090 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 334678624 1250 334677374 334677377
    0x8040312030605242b060602030306030d08040c030210030e0610081f241d04120e010c170901080a1107020904030e040204091d012c07080115030510020901 68
    0x38040b03120060710804114000804d4030489207804d0b1200e458070400c8080b820010351610700b08401c0c221014952140d10050710080c00214107628200000903512030013141054200404880071800b00b00039000c040020b10b0b4001d103280000020104010010302980703000072091b10901002c504000700905280c8140c4148002070a0401e0030080600040d81f81ca101c4903c2c1c041e5a01a92041f035000130b07c266010348400c0c2c0045403d24902502c2c0011441c0f00304100c401c059a04051000081d80b014400b0712550460030610ba0b00e1a480c001610120105070b00600901148440001f81e5051803000b09901c150036210824181c850140c1c640c2240c900c5400c024140348204401805441d19601055005210f071a04107400d5030a0408601aa00564040f55040b5116220001681207000440040d8030704800200042c52041c0700b8001440744050001e640e805021140c1c0d10000428480980a084ad41009110300c1320340c04140d880d101e80520050300d490040001550300c1141c0f0780202e40c10880305 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 334679874 1250 334678624 334678639
    0x1020c040b06031f08100606021c051213061b020706050309060c0306031011070605060d120e210d0e031b010e0d0b040b190b03030403060b03150408040312030605 71
    0x10b131001508a15141442d00c0c20f116141c2e14001212070b010010141d080c00b03407103c00b0640d01c2c907100020b450060002c8401c0c0c00740b40c4407d242c4031159406400c2d50b003c0c030040f51001c4402e03143e03139100d048111480c81c0d003e040325041c04482100c04840d004030900b4030800e0703821aa65569122000c403410b000640307894145d9000700012800d50032101000e142c01440c0101a15184a0382c2007459044801e82001e003201d80d0300206520341400417510130385501c5401030b00e40544144050307540246800d045400442405052203411070642c46956115041214404080c1c0014201c0c10030280d9580c44150000002903150201100318200031030a40d507400e502910100302000c000b0f0054403101c001c8454203401210720440480803944440e01140994080c2c40c2800407810110b0140307034131303440f41e030700d2000400d040003c55031003502c1c0001214226a0090400070b149050703000047d081105d58200050115030040a200038800e001d0010400c40c0d1164600031403844e5007100503010349010340f242c2a40040e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 334681124 1250 334679874 334679881
    0x1020a03141305030d0210141509091921030e0703061112070e03160612020d090602280315030809010c24060e040f0305070c0306091101020c040b0603 66
    0x8000d0007502c080b541c060581d014003512200070919051204007084010303448200104150221440340f40c0c1e05042aa04c02d8042e450320b030305103414611700200404c0c02a440e650024404d54014000784582c3d0281c804c100440340e14a0908500410001516844035245c07810807000f014000c0c0700f0800c10b2140500900503240c0b55459079402030100c04e1185c1c5903260304101c01900e5104501e40e1078462072542c0c50b035002d00340c09078050524218200b140c0102c0b080d1140000c0c8581074008107070340c0030a9400c00c2d0160365060488900da001c1c200e4140001c0c442ca0000c1440101d201d00707003164441150740e045124584c9a907401046003918404140c0c05c0300035004070805c0c80881e03444d40003401340d9441030420900780c40440d0380742c0700801990005c0030140040d9031128801c2c4c43d194001d940082c42841d480b406a03041c5615503060449400c01c0c000c0a0200c00601701040040c118800e90046821010801450416080060003500561503ca0042c042e8000c0c40d00140b4042c4650b5500d484050685401e50340e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 334682374 1250 334681124 334681157
    0x20a23030411060a030e030d0e0607211104050a060804020306070318020f0105122d0114010f0909050a020315060c12090105161115030c0f16060c030905060601020a03 73
    0x601540130407080503200d4407041d900750410002044041120704000031400342394030801c0d00f00fa00240c002070422484040a410380301945a1400000303140c2d50000500c004402d61498007489907038041c54000d41020b0703000802a420113180da01c564000d13000e0f502c41d90340382641102100c2c0c1140940069900c1b208000000d411303e8078024044a4060400602d003140f40c0e501280045400c4841c0c807002d00300608000c201480141d17020300d83c55204d01c5509081d50405c2c040f444582d1440581d00e0422040600c110b25403440b4070010001803400d96001c02c410304007041182c000c2c5d84203c0307070103080700c110069200f41030810800300c84900044a018110041c07541c101d12102d64071880300141000313004e20070f8112984001148440301845801114001200c41092051000320410100c1d007078501441004942001032007124203c101c1c0040b040da80d80c02940c4001c8000c124a0806407507249000360880c5166015400100103c2c0500101c07200c6a5410f401207030f4444c903e40340240054070000b811040b91 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 334683624 1250 334682374 334682377
    0x140105070f020a0f02011205090f120a0504031e08030f071409011b0809031203060405060301020a170a0f180c15020706030f02040302060313060b010207060807080910020a2303041106 80
    0x4d80c030525010314800300c900c101d0820f40e074059a050b6103a410105080000d8034080141000c3e0202d00840f050030f058a000303000c4c246000700d11003d8445069551509250701c13020203050403803580000116101e0400d00340140c000e941c21a00140820000164045102c1c00d400645640c071805949510350b80003c0c0750352104a941104044450840c103200403840e6580a120340d01041d11680b100540324070307003001040156880580528002e9204011015041360f02001960310070140c0b0340420300d00c0e01d130351000d00300405d0b0000300c14100c5031500140c006640d26014454580c03074001d042c2041d42603258a407141e0710b00460700400015a104150400c2228000d80004425541c5081d0060625980380c011a03415881201da00311070103644014042000307807900c140c4001407404e100514040b420503102030b240c007001403c0c030010f00005000045000104010162203814610310039910b4100c1503c1c06007121800c40c00405c1d00b402c101e0100c80c00490344005484c4a40c4e00025201d00e584060320038031003c1d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 334684874 1250 334683624 334683653
    0x312040614060d060b03070512030a02150405030717190c02011101050f06040b04331e030b060631091103010317121003060b0409030f0e040e0a140105070f020a 70
    0x1b5000d07015002415568050020500c00405005160754483e1123100074100320b0070754519942038154106000100e80300100781c5154960210041c200103207980d000e2502c0303000d1280802c4142d1041400c10f42100d9008151540452003070700d44c1c2e440c400300e80d5007050903690101d42d140c00c03504215000440a2030150000000d08501420020f031a1055580c01c0000c00c0400f010300c90796000c00f8003400c0440e600c2c03409a80040c01c0704100f10002c080160b48440e54111a8400a002001c0d2600403482e84e545402c1101c2c50a00c0d200b200e0800d0041e0109130350f00c21900542c821a00440042c40050076040c54050358601c01c0626132214550707821940c0c0c0c4007144000b071544180740c0f901446402149503511030014060f0682264602c03001e403851030312900359402c1d611081d0243d420030990340300103900103c1040c043e514078240031145002c1d00303000c2801001040300d11980c0e071007015202c406000c00c0c0d4400f000003a003040c0090100795694103043d1402c800030444000145e01c03c0c204c01b008034103100300c80c482 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 334686124 1250 334684874 334684879
    0xa051501081801050c1224010c15051311010215161404080f19080d050903130603050a0b040522050102040f061106071d13020702030312040614060d060b 67
    0x91041c0310101d0b00d08440003107488149026001506600c94240040d901794414802d8014a42c4549000003800f502000100810f051142c10075480e004c000d001c078851400c40034814410402494003035405850826210f50689002540e02d540e103150b9440072440a41c21305245844200c940c46004240754080c540030400740c200305041c00711203808524030b4000d0004004150040500c011700000c05805c080c2d0300000354503505168402280002c80003403d46d0b1018805c000001a01d644441000d8198440e44800076034400c06203070080789081d05a448140603408004081040d603e0740e000788000c480c4244e500c02d05450301002040d0648049520088009200c3d030300142c100740c1c6d1005d507142d0703181040c0c01c503c01091450302c442c00c030300c041081102c1d071042040c1382146c0c4621464802c2c02c4400b540d000c2e40c1e4001d0b40060749255500466070122108507601408aa950341d100e0642c02c080c1d1501900c080b160a810303c444204261141d14281e0b001780001401c04d81da40c00240d68100041052000380d0341c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 334687374 1250 334686124 334686151
    0x1050d0b0307031212020a1707022e0609061d04110d0b01030311070e0601050d06030503030705190c020609120a141b09040f0212030f0408030409050a05150108 70
    0xc0c0661424050318000754030030f100c0d0070035603101850007030803008100200d8041d0620511140c4c811542c0004d00080c2c01800c0103035950301351542c54040f070505003511aa03500181d00d0018640107400d01910405244034480800c000c550340300c6d40394030b050714054801c1100c42102503102402c1140711f04403250b0000d100c1d9107104103400480e00803c401402e00b00e0143d03407511340480108203042d0411442d07e41c590710380001d0300f4442c2c108180712592080250110b410040045070981c0110400c0d401880919000350440e51203262030f090003031080d171000c1e9000540100798060004100d01500700c0100705a8010903c5083c0b00c0c2181c00c0c0003d100c085601384445208950028000c039400001210400c66002d0140c5041d6421450b8040c0e106d8448400c1070042c0b00c01000c01c03020407612404d051945504481010401803005105440c5004803800c1c5400103000280c0001c120000100801c119500d09500380030560714212440c0c2200c004841000400002e114485419849407501581c040100070490 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 334688624 1250 334687374 334687391
    0xd120e0105120103030801060e060313142a010201060806100b030c2503020607020c0105041a130f050307090207080315011202070308090609120d0203060409061103040c06110c01050d 80
    0x30306092000784c0c0300f074000c0342000e801413051543c000c081d1225100b0694089155040944200b1030395401d14a0180c21100c40c014840303000c002c240074584450071014426040800040210411003500d5154076003d0f619000000903c0d61011483d188604403ca07a002c8046180185003495684001c0105140c0c1d4010066115000080d400e40c8603103d030200c0304034040c92034518000c0e1800788054080320641d800181c00c050b65a0380b0074100c40a54040d038000f100703000803401001303220f406104030001404401100c046042984121101c04843c070460455800c0e80d900d807a0741089105400c0041d000706002c00000f402541070411098601c0011324141303008555020080b012608496012070004145005000e010002045220b8002c03503008041d211194400c800c0c24030f40e100d0005075503005c0381c0210014030035a07100c1d805010269003201c4280814a1500c4020007264000c40d400c492070041c0ca680401e21034450030107540b40d420b14000901440c006080159007030b40100d106c440d46152141d000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 334689874 1250 334688624 334688647
    0x60a0326071e0c0b0f04051203041706090d0819021b010f09050c030d08070c0303090f0b1e09070b0d06120803011a090d020d020f09100807050d120e0105 67
    0xe80c4101d41042c0d40c000b40700d401c900c1c00c41810501c42e4000b0140c400f00b4800c41074154500f000b11801c4460460b441c918120001031701c3e5007503000c0c6a00c440182011610220340d1140c0c041503462244208030250750a10300410b5060740d40c840300351803942c00621a40082142c180c1158000c080943c017400503000e801da20350340c049094640704000004007e0f02d920501c1c2c1040010019080400411005080a00c50b03a42c0300800c01e60b0020007410030441d508c6107081c14035000360701540969402c09000c0d0403d0500d814144004141550080d0414500e683d07120094103201040d03178020200040941040c81c5401c46012640d00720f0901c8a07901941c8144c0000c8031200004845c1c0300c10f20403c0c0f056140d600d488019090903100018841c0e140d5010004400142d54440070314040340d50440704009110150b00202e85d1030058100c0c0c0c941c01810b40c00038000487c00502c0100121501b090885090310745071414844c0c1000800b00003040488510076003c089801a03016001011061524038140b00e8804c0d035 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 334691124 1250 334689874 334689893
    0xd0c200607061d010609110d021b030f030708013606050307030516080a080712030908030910060b1c0203090a080f03040204050f04050a06090303020f120f060a032607 73
    0x103e800100450603600e02d01d5080038000c0800030094050b041040801810039035605104104051039000d90004140345400744034a2056401c201d42c0080300c0d200e40081c90049050b40c400c1da00d0030046000c00c0000133600700402c00e402d500d08040790f014000d00d821600b0040a0101094446e80500d84986012441d924100000401140608000c04a45414440c0b41c284131550350014109a00000d81040104185c1c0c411101d184e5445100c00c8042c0481100884c02000a04402001030b030001040c070102c060001000710300900f05403420480310380d407046c0031105849405481a0300012036200f00100701c441d9805560303ca9215026240c2c1080320307554244082d80515407500c040c0c4000310911096040c9881103940c04903882d490f521f1182401d0b100c203030352000101c000030302464a030700c0d01404052098040d18406a01844801c1d150301000c920030714144411920490500c421100140191824414900c2280c0d005071100b642c0c0400c0c026440d07026107814660410481003004448005403a098 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 334692374 1250 334691124 334691141
    0x1409240307050d030207170c011d01140a0e03010605060a14070c08031c050901290a0e09070306050f060d03080c0717030117010c08161206030c03050d0c20060706 71
    0x6014041c05030804110215080c1c1d030748804d600030351203054023003046d0341c00020501c0e01c28214a00702c0d41c1c0081c540012240190001803007000b00d203010503074102d41030f0031400c81203a40c1801c800038002151920180060360090210b000d000456240290301a1407030740c00200715070390080006940301600c03510428034584c07126106003022a42d00050b10050703050fa1044942002d680c00080c81a840c0140c0f240300542225025600400343e0100c10480781e41e80c2d81103040040805082c1244507241c80d01c0c100ba100c7c202c600c8207861040c10140021040e14144640611425004141218015075520100e03002400145080d040320020080f81010030202e040000341c115030b000915940e5814070314908002d000e200f007440c5c92a8104800302c0d22003500100c1c0150b016148004064260343d00c0782c02240da001c200c85007401e06600e41500401404401034180050302d0054045464406400c04111780c0d0030400358006e8042540020a0600403800d1005004440402003c0904002160302c8103811a5000b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 334693624 1250 334692374 334692377
    0x1e150d0207050a1505090706050a020319020106140a2d0801020705010906061e0308090402040b07050102070c1a0a12140a0e060105010f0203031302040e0607091409240307050d03 78
    0xa0590b80f0420100c41030b4902040e004440c02c0c8964240922010781e40d002600820050100200b0305071142c1c1e10800039240c03013010001400c1c0322500c0106019000304107e00030607501132140d80600482d42040d007848000c031400504000c140c40c0307042041c503071150141885440d1002d8140300c0091180c00900103001c145006074000166803072070703150440448019034880c11500103d070f00510522400250100100ca030000342042e40e460103c00090000d12490300038218050000c16141c040c40015400703031420354480c0c82d42490580e1500004c1e0260991092410403c02003004100985c41c03081908000e004e09003113011405240c801c0302c04070006800c0310345600c510707034a900440080c24100300c1217006000c00c0c24201c50a24142c0c074020b40b6407000400741d98604141d00e43d0202152260744c40000e105000406465883c20080c2c0020f000801901c0b40b03070b80c2ca82d03103814440d004c0e1501ea81d40e2070050702904120701c030302c81803c6491050700c1c02c05500b0340d0f0306005140b40040c180d21a1030b0900e050502c40d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 334694874 1250 334693624 334693633
    0x4061d06090a0501050d1407170a050d08091e0c040f0209011403071b110603041208060307050603040b0711030a0f12050f130f060204170c1e150d020705 67
    0x5000d002401e54020641074810307042500411140d141d917103924001941003110180d50020200302180341c40c20b540c3c002a2940d06581280581320408a000344a042c40b803415601d44508440c4211201002511281d4081c0c001c41c800c4080200344804130107481000006a0740044c0794000044c007243c038010120b99500e40c00152203405980c0c8007910101d50586001d0060440c103140b1001007510340c1e0b0f141e110404041000b40142413008405e1541c0c500503000701210307030340e141c03910740210240d6200300044007140c0c41070082080c07498080350382c03020303240e000c0d20b8103045984588941e401031001401c900140480ca4010f040c9485d800e100801e50200d50391903054001d1400100201900c081d4500100d807a480c01080c0704c48491046803964205c2c801c401004402602070a01443e0100c0e0b190000302600d10004000900d0f103001840042c444044e039094400e9040500c1c14840003100340112003988c52000b00c03020f402c5103008c1011f0805281c007500d0007130620f04000402c1e000c0364880101503410394031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 334696124 1250 334694874 334694881
    0x152c1008030a0e040b010c0c09020711040c090503120a0807050904020d06151215092004060f3e0f07030605060415030c05040b18070e010306060207050d06020904061d 73
    0x2454080c5170300c10b0b503081ca82091410050b44070180700814502840e1035242d0001414001e01450642003d01450300902c02c01c003030300c43e40101510b02900c42c41618001d01403090302403000c1749100306075800c2e809a82c540c402d09940d142c00448240e80b00e0380c1501d44c0035509000b1210354024a2080c0d00103051050b143c0c11030038000356400343c003280c038501d00d4280c0203003010b020b0b134030343c422000105040314044407003c01c51070102902c42c100c0390051090b17420032000100740001c2c0140d010000344180402503e4001600280352010440c1c83c40440d9120500c02c102c0d8031201480f0900740c41c202254031054141c1c1c0c990300b1001c05a030300f4400150300507a401501c0e101409408d242c40d1140d40c02404003001e4080e0085d2440c0d480080c80e140c140309191183d5503030241c5040e141c0b1840d160b902c01d10a40c90364480c161800d21300180442c0800070349680000d19140f1f022400301d0002076180b080c2d8078006e02941401c01c055581401a6100781e4003550411788038180054655004141087c0d10301a40e50020510318 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 334697374 1250 334696124 334696129
    0x8390703140102041d0604060e040609230303060f0a08010c091a160308040606051f0807030510140301090605010602071401080f010e040c0305030409152c1008030a0e 73
    0x9101e01c0524020791040004201d40070349614000d010005852031009156505d50008000b0700b103a07803107d03480450131410001048001ea0090366081e2141400d09c00c100030807007101440391342154400f0201d40c81080403074401d01e46202e1040c901035000313002c00c451944030300c845402c2d6903040c040040440c412a40a2000350007840b880c4035000302e44205d030f505161049803c1d201c503440c9010302605104410020030107000315500060090040505015107400c00d124102600701100000c00340000d00c0b44011444d02803281c05080d0094013420403c94481d400c2c030541072504c0000140d141e515640e59024240010b13410300509000341000e4015002d414540000101c1020107000d10354100300c0c0101c10001c2e20000c142e511810b603041d6aa1130805075445203400c070340540150300040d2417480081400260100680c00550700354485010844030b5030f82e035001441d41500c4072242c035032403007002c161140400c030b0f845490341d640521801030209140c1d5455000a00756481403036503a00103071008411101c0760 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 334698624 1250 334697374 334697393
    0x40605120d0e100203191404240801030b06011124091203010312030506060c0f0d1101050112020f0a0f060203341205090a0e0103050d050708390703 65
    0x401c400e41d1402445054483c00941380d01c100f5603060040303000304030100c0b0380c24460028180440740140002d543d85407210761701c92454800401200c80782140e0803045200c24898800c45040b80d611038046045a01c0321001590020001c00d22107619101d007141c50907668004007141c1004150305200104075040001640341403003141c050900e641c100c2000100001654800d060700c1c5210149000103071526803500203040e030300c10941461130324800d0050303490b14040d02081e02c1a0418154517401036500700c02110a00360b9a0900c200d10203201c18902c0e010140c20034007000c040480c030040c10220007a803035501007000c0e0410ba4200c200140d0012503020194205480484810b21703100f0f1540c2c4015031094110080e0039140729004002c0c0d2100c0d81c00c100c16502410540d410914003c08001d202500c44d040c058185009200680d482d10840e1011300c210b501450403142d9203078108001c80d1500341030720703c0869801007113000320400306070780d541411125502d000030308018580c2001801e1040e00e581840c0d42e90 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 334699874 1250 334698624 334698647
    0x40f050a150203180114070b0a0501090c050d0209040e0d080f07091203210204080a020321040b090f0a06022401121709030a050d08070503041a0402040605120d 70
    0x3000d80781e901030091a00041a500361900e54406190448400c83c0121040c10390351004911900d8007260220800400c46500c921451b001101084107a030798450901c140e901101e00c1c2d0001c00c2003005081980c0089400030101c840015002280d40c000c205000303441d21031a4000310300080c940405001d15030307040c0c14841d60401d4aa10308404980c0c200340d04070f1100e080c0e8504c010180450013601c201480f003001409003510074003010454440d41e940800e561070700c8000c40124400c1c00b9820110304c003844042c441e220f10101d1901c04030304041c03d004480001c3c2e80485022a44120407031440095503941450718000360413541d0107080201107407902485000411446004441c000d480140301d0070301101074527a03000750400107445689502c000601240e201c0c2c1000305805010300d02e14101840000150113000742d800b40c0e641d8606580e448812a464001aa00140045d100c00d076031030713580d610091085410078002400080d0b140c1d0b45500040c0c9550300440610682c0c1c0203100602c11007a0002600c2c40ba = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 334701124 1250 334699874 334699889
    0x1d030a0f050909010e072f0c0a0e070c0c05092d090c1003020c010501080601080f0c1e03190b0901150503151003080f04090509010c0c030f020a08040f050a 68
    0xd02c140500000c00901c41400790503400580400040c2400384180e103480c01c5860703118514110413041c030300d404000400e0300c520050184500710761501c0d1410034400e60320448450011041c169102e00e81e08071000ca406080035144103250090209541d51601a014041c0b062006548000b41c41751058410403412207103600f00b5228080200403d00b6804145008008000c0f40d010084030102d007402d6009010318991703980135628002c00465400c0c00080d03528180c072040c808803024091b403043d03060f50701c942d5a165241c01451440d1040d44c050340724224106458001025035180e0090701c0300801050540c41d6044c2d5040d1202400d00083c0c503000e1056181d44400140305004060401d80826610481648241264901034000502410283c81100051079201038110b561310059a4950410380141c065004060b01c2c00010800120051142040740016902c1c2c5004410391034405803200307151450310320b00f035018900b2504000340c540ca0090004d4100c04a40320401800c0c103080c040e0400380c5800080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 334702374 1250 334701124 334701127
    0xc0301050f06070b010e0c1c0c2c21010213030c050a0e040f0c050a03060209030105071b020108040c08010906060911030402010504181b020607080c130e06041d030a0f05 74
    0x2003caa0005101819202d1a06e4609000c3d2688940444035103d11007001a03041005181b0019035490340d001003d190702c85940d03c500c0c00c6808071140c0d984600c0c44c0f540118660162508038024200a81c07140ea007102016100c58249201540184c203907404100d0000d05411034005c00d00c1004600c900d040080c100c01d0b00c2000c003241c10708090098940c009000a0880c61a1324003250030003e080c40d00c40301810000d001151101e03601e00d40303140a50070450080e81300e5400c1c1000039098a1007010f0b280e124803142d00409610200300d80054810341c401820548100352a8400841e0001090040201c454441c0c08002240b5240c602e0305000c0750040c0c01d4580311244104140070250303a0240c11348007900e1a0401085540300e20300003a40007481445911000e40c0710a201c01400c0c280c004c58102d109074910344840119031b5400201c08014411038003104419104194148420f9503401d00b8079038081409007000803800d040d0004015210003d909503e1580c0c00082c7c1c042415034400300300c1c1c1d030307980060400c2d0b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 334703624 1250 334702374 334702387
    0xc09010803250807020d030206010303080f060a060e0a032102010f0c02070611010608010906021209061902071b0909051501030c03030324091505180402120a05060c0301050f06 77
    0x42c0c0292554140c24591112000103680620400c2000c540701c3c0fa50003000260f0005103440d01a454035400d1109070085061b100000c1c860812035802e942c4540d00003450010b1440c2030150964140c000f658030250458072003400400041e0b0b40340070a142c2c544486903005080f8000f41710003401c3d248071002104942d42041041400e0540014480c0160b0709182090804901c400030014010300982d440400d596080002c11b00510200344e000300b01f01e074201c04100c5800e80d00c0d02d00ca66500c2c00280d4002c036250394218021000c050560740074050b418401c5c40c1200c0031030b403402e13811500e03584641c100031031540d0364884036001c02404108010400d001d0502481d103c2d0324640322010710940b00c0c4809400e0581760b120791181242c1c0040b14048031b4500d51102c85599448554510042c1001303a490b03000e42001c1c00e004182d615250441c10809201155443c5a0380d0b00d40d428464400f503a081c407003010748100440da01c0025410310125101300303032202c01251203600d01001c21000401104149010311801c00c0300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 334704874 1250 334703624 334703647
    0x307050f0f010c061a0f0603060102060604230f0601020106060c0b0a110c1b090106030b21030f03070f0201050c04030302060411030304081203010f0b04081f1104080c09010803 77
    0x124400c440d04464010115071801c006950106030160000c11651130401018030500c54624005000b0006a81c8100e80700000400c0c001c2d113210603161940541d0015000500b589170541107070850400c541c44680c0d04826144d445104100242c561000748840308040000650342403003044018203444c600144421717215103414089840c050030300e20003562628402010710139584100c1d00350502920844000783c0740024804000032141c10742920540a540000400500c280a03001c91a2801014a00d40c42d1744042c01030442c1c0303541c01c203c0c905808140101012004090091446448a40c0303c00064122100c0020700f1208010001110003c0a00042c0b010075400074181d9803041e40411403909104407000002d02c3c60040d607100d90040d21818101103900f040d090003850480c3c018036061400180c844000c41030350700480c0582165907110b8581841880d210001d00c902100e12003000003281d10000c03c41d60250f40c00703500400041c3c2d00440d421607042c144804018014400100918201508904e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 334706124 1250 334704874 334704889
    0x204030627030e0d0210080a0f0b130e1507050309010f0c0f051308030408012a020a1502040308030a0b030607080403050a032a090609060f0503010e04060902150d0b030705 75
    0x4040c04000f81c40d2001200358840c440c800b002c041c1c00a00d441a11610f80500420f00340b1300301c450550b030900b804241c500102c1769010303204162000038050b8900001c00c0d4810300c020124600220101d01c19209458a02c104051615001b40600d80e40d00f503581c030b080040c040c00e54070740300000300e1030920b0300300c0c8807494a501140c0d4840601082c50000e80d103081c415094407000c141c07900b0240c002d000004000803072200550091a075080d512180c411032a4141e800003a0100301580c04002503003103038400c1030004040b0781c2d480c1c40503680c1400050600f5140c0d200c0d030880360422114012126690058003540b0301c0d081207240e03484000fa14200886e031509940003043c030300036811044140f6456049104c04290000c4085018001400d40801d044a60103001000c2400d52320a400110b000004d01041481c440d001d600c5009000740c4489244d6417038030358400000c00c0c0050007911429a1074544c0401650b0301c946600e5282461825a0386410b0310281c07010895400b4030440703201e54800301080020b03896411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 334707374 1250 334706124 334706201
    0xf12030604020304110915040608010b0a1e0e07030c030e01021e0c0c04092003190b1503030705070306061e090504020303090901150813080d0504030e0a0902040306 72
    0x30380c00b50322901c90b49007620700300715070400055000c00d401c1e0411000a081100e05080c01c2422030f028404540d544002e02d080b66503a40751660810382000061013010504089000c444004455202010f0340d0356044481e00b2130b041c1d8110000070340710f4800d1400381e40d16005030030000c02c0e240300031440c1076a880b510902e411081c1007805d04175100441c3c03014848070184210012010041e02c2400806075a1408941c4c414020340000011208101445064100080d24460b0080001421500c00d40691141882090000c1032903c3c1800351511103015034074240050081d49100703200900324141940303800342c1a0b0342c00c0e03089549402c0c1b0700e0b6414680c2203080c4031150200c031250031001031039460318000b00b400d51148170b20b010b81001007071000007540794004090152207016a41c406c0e0140c0c42e00c6505410602031401c020700b0b044000c0c400141103e895900c1309401c03034400d04003c4481840f1001080820b0015403082c41015404181041805800e00800c20a94400780c0c8d002c0002501500d8000c0400d8101d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 334708624 1250 334707374 334707379
    0x2109030a0c02011b0308040b100b0f0328051005190603050901021210081002070803070e010210050114040501080a0f080d0608060c04031406060a1217030c0c0f120306 73
    0x141c807801e041d6402071540071868003144444c0c07081e4944030b04001e05500c0701918201da1a1147c1c40004105007001c80105040d148402240382c03802ca001c0459940680014111b060b240004a0300480e101d07154cc0d07030720010b840741c925003c92103142c810241d01c8004804e03440280200020901d1240c0d4a29981d1f041058032181c0c00c000800e0340743d619140e4020300419880d08003210308441400481312001d0203aa00302c80500d0f040300c082041d010400c030103034082c0540040400301c00b0700c0810f410034094034442e4602141803040312002440da01c816415a102039002c0c90041c210080030b100e190903d0300590b4094101c020081005248654500180c074440420141c400c800204a02015007881e030014001024041d040741c42e141400c04503105142d04c00d1000300d078203103600d2071103450f4040d0109182c4d1007411b000301042c1d403092900350900d080c0c3d10304290490304c4942c24460600200d01c902e0285000d80d851036052070320307500380c5182c0c1480e100342c80650b803205074072101041e1800c49400c2c049070350040c0c06 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 334709874 1250 334708624 334708637
    0xb040501290d02070804030209130c1211040903030203151c0816140105070f030e0c040b011403010807080f070e011e05060a021b04020406050d0902031903052109030a 73
    0x440034070155800744074003440300030b400020700005001600c000391044e04c2c0221007203030103515400d0f194850700942010050125840c1e550801800001c46181e900940c051094227003202050070010f403c484103040200d001ca03a010060110300300000c680309003010070968545000712405c41c40c600741980404001040384800140c0c140d0100c080c411001680703580303d03101710130300c42840804601a0504031003a1001130501002d00c0d032801e00c46c4c0a00d40c1005400006040000014420b100103080210030301d5041c0701d6001c0d2103030400c2c0c0c22400118001d15980d4040c140d06410250707850305050701e8210000245d84080c000b441000421a12a41150003840840030042e5829031400000251540101d40c401c202244031080e443e000325030540d500c001c4544155500e042c14081208a01aa0160a0024105021024540d00241d0294400e18002400c40304e885404045030410700110a90880000b0300c0480d00c44490303030208840540384880300014031075510781042c90315500d0040070b05100c02c20a0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 334711124 1250 334709874 334709939
    0x1051210360902120a050f010b04020403080a1404170109050c2d1f020f0d020f0d120b1005070b0705030411060a090b0307051b0304080a150209090f07030b040501 71
    0x110749044d090705007121000c1c2c0300400c4182c20415250a00710071000341075424104c0241c05407819100b142d003620760140c03105040003403040341100e008180d20354900c41501c3c00c00010a031411121925425061040c2c004501c0100794074280381040b80004921b40103100001c10301441c4e40c41521055800146c05000b41264107060700091041030005c0a11620184451014100c2c1070380494000c0c1c4c4168090101c4880762030001040740e03220320f00640c2c201c90782c1050b120340102078462100d494608011541c0407034480e13590070010b51104280c146230b402103800020401c041002d816a02c2c2d91016442c00c000b415460140c03212034009070085070003841071070009001d440c10f5009105500142040c420031907160300d44004041c10607409141000c4011294122005d0201c40c00000c80b010b8601c0ba81c045d05510056584031403207022020280003251b9001e2002040d1900c0d40240a80f040303404a189500c503007001080902160f600c0d6100314022420305005212414070720b418650515052094294000d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 334712230 1106 334711124 334711129
    0x708090a0308071b05010c0c0203060c0301030507030f15060305010606020c060f0409020a021513020f030d020c09070c0203060c04030c060906080402060901051210360902 75
    0x90700c81c2d0019040074403403455038412418403220301e2000340d2280d07121030944014072030b0200000c0380491783c0400d40c42d04000007600522140305251441d4119224251200200e01000d0804101142c00d402000541d040704c60800e985030004002c8c140d100d1614a0203410184180e400502c111105211545481313822140f0f52a8404c4865180520b031680000203900480a0072080d409210281e079103da000b00002440f0b0140900c011041c9100e601c100100d1010484411340071380d0041c0400b5240a40014049011600c100c1e4000c00d01ea84800044848150100f0000c1d0103015180070312002c4101c1d40054400d503481070701188607040d10f468040303507031981d188a1000021034400105001d41803141c0108210380061402c3c0d0b2a22801c2003110b0075400c000d580007403607081484c404014601740c100700d22150040054032640d40207043e20070f9046051805080c15502583e0724024000c56 = true := by decide +kernel

theorem cover : BRFrame.Cov 334532374 334712230 := by
  have h0 := BRFrame.cov_init 334532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 334532374 ≤ n) (h2 : n < 334712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
