-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0404
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:38:22.929989+00:00
-- url     : https://prove2.me/submissions/e75c3476-14a8-4f57-8af8-f09e1021e5fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 72482016 ≤ n < 72661872 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 72483266 1250 72482016 72482021
    0x15031c02070806150901090b011e1206030302010605041104030506010e04051c0c02040b0d0218060402130e18060c03040803151009030506070c0804030602030a1e02030403020c010908030304060b04 86
    0x9080b04011224a441c1000a00c40100d44801c030141c016002e410001c03c800c1054043c0320500c035411394034020f56000b1040c4032074905103032006c1e400501c8048140e041c400307451030150101850180c0c0002c61b41c2c0386040180402c440414641100c100414001800007c802040035811100c0300c01c049030030794079503082c01403d01c05120b1102d00e0303030603c00c0a04003000350012040340d42103000b1101084811009018000820b45d130350b100a601c01020700d40c140082c0b441c4844103400240142c07005003444840d04404441d00c0c29500074800d42d12081c010890140c65214003083ca007411200030b4681c0d4100400314603410b000140c4010310402c40400001c42d140c510303000306420b0203401000180d81805a0b80040c02a41072800151098080d1030300040e540e500411b141412076501044480c40c2030700c0c2d91a404020340004c3c040740700c010f885a4410600d4000909140300d00d02c0c0640c00160369050038500039140c5040f100045c3d05110916804015a000100c02d0b264040c1d0491400f01d009012040001c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 72484516 1250 72483266 72483269
    0x20d2420180d0f0308060d05061305010f0f15050301090807030c0303020d1d12040506090d06020702190e09010605090420060c030703120203010b0412031403041a15031c0207 76
    0x802c41e8503040d0700420700c44006040340c14107000b0345416002d0f440d1b0100b80507820020342c0300504203600820100702d506140801d0b031601d4034041e000000c3d0036594201103030199588520030251181e1141c0751904450014102c12005040c120000c02c2840016541e04000340a0001c0280034801c0d640000ca0506000b601214040200d201c4200200c50103038035081c40d40b070003429402c00c652140d41d406e0640b040c04030741104c0544800401c1942040010010446107000c41c6804842c0607409000d41c10050f168102d4030705004c0b411008400c07a0304c2c1420403003040450300802204c2d041e07043c50402c10442d02c401c01411340250b041800561a035072482d211010300b020b0750705081e820000004d481d030410003010003d80b9516110707998402d0744074003514a40c002e1380028011000a418100020401d80c45104440520a0b10a040c0300f40e0248000f01d05c00c103560021501591440d00c0c0c0c4c107144118548c1442420340c404e01c0070380c86480c90700c0c1c1000403991751400c84610345406203c507020646010300810001c0b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 72485766 1250 72484516 72484519
    0x60421170a080106030f1428020409020306120601050a050d0f0b04060b030d03090c0605130b0c010c140703080412020c03010f090204050c030f0a0c0c020d242018 71
    0x7650303020141c20040c454482441504002850f0039483d012100c4980502511741c201442c17007040d140c5892580c41c109040354000081800a059851340405d034650000e8402402410001a185d141a005102e030b4900106405407240d04840011721103070340e849078818240e500c00d0b0b50030000343c541ca140c0355507071010318030020705001d4490042100304a056008000b42e40b005609444034281009400d40c15200082c50090240f00108024008103204001400b007070620740c9814001a560703026100d0842e4099689070400e41d45602d0f50305c0b40c85030811080c0128070700608969142c00c02c1c644000740311401c007400c0204401c02400c4810380e661b00c204240101500020020020089160220001445080c104138001d5040100081364001140c040d03d01c07450644a075401c0c00d50318451240000d0680000f00002e00016a45000250300e414404007444c92152408a42d22000f051030010810703001410381511608101020303652125045070845450741a14055490340503034410120180302207012207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 72487016 1250 72485766 72485813
    0xd0504020a1223010207030504050603060105070f03080603070e01080c040f06051908010e06010302011209020d0b04031106011512020f1b030304171201030f0201090509070306050f060421 82
    0x700340803d004041e014200c0346002d4029003110304004500340d000e40c2a018000c40d405200400007410b084000390350201c4145421407801c041980d0340c0c9507601103150b0513000118404200045424100301410291a070091654080d6140203a001d80d201c415143e4607010f2a01c4070582c1491296580084000d002c00802c400301509050701c40d0b0030512200e04c00c0403002c1d820840504508400401c01ca816260103944031140b0030f40003803074800900078240c03040f60003210030170f9000082041c0304140c0f80280d20954401d1203d9101101c0e0510301113041e00070f403003e0552161129480ca400c05003510314005240c60140e1282c141c104c6204840c000c0c200101c4018400c0400e0410154010000754800c0c1d1089074825201001140410440c0c0280200c030120f00038880d00500100d0340e0b404150703022610500d00400c2a540710000700d442524260b4281021030f4031188d090101f0314201c0003081641400381c80940c01c192400211950307150035100c402113078120901901050001030005000c0480c01d05106 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 72488266 1250 72487016 72487049
    0x2304060e01082503020a05090c04030803151927020d0204090605100201020703120e010209150d140405030304140a050307080d0506040917090607140f0601060809030d0504020a 77
    0x1843d1900c10280c290450b20b140006842000520320441809403600501600181818a418850680009000070039006424080000060340b00d0000303520896803660000d02482507c0300340124514001c1852040c2031101c01c1c10710040703a600313480b103403c00c00000780d01c2d003292076a40115000348520214613848500025011840c03d050390440c000715182691030140c102c005490807800c074020302100400090030703000114103240035034215080c04040f0308001840c0242c6000020121048200b400750f1103d004101229110020300c00c1c00172428115104910f1441c1a645250f1644401000213220f8203101c1c044808810b000c1180300400e940c0700302103d964018030b00300f6102d9908410080d1010a0626000410380d0400d801204180380c0d0260a1194400301e624000c042d5400c86500a508002d060102d0004107080c41d031800340b5840c080c8040d02c2441c3e40c8444581c00c00005070881340c20b000e1101c09110726400000101c82c446003e001001455031550b00c001090b08449602886c2c2c442640c03100c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 72489516 1250 72488266 72488279
    0x1050405060c180423070516110a120308040501060501090602250b03010902030f01090b06090f0f1c0b0703050702100902010504030b0109050603010e1c080402040608010e1005102304060e01 83
    0xc0f030050181c40c0d6142c11840e65010412152481502c0728103801c01c000740c40c0230b00050388561412001100041802c0700068440410300908802d4071400d0700055003072001d00050040a00c50307117008c0c113020329200d840c11b0304041000e9035441e468000341d88514a140b8031b810059030030402c0000684002c02d11140e895a51740e1002010390015517200c00c052010344000541c2c907509210312001050080d2600d800c003641001080100da1014074001e4006600c1800b00304250780300c40070421400c1400c0e0300d80380d44800f18205101c1c60705005002030240351504040c00a001c1c0c00080501e071100a41c02c0118142046200403540e40c0510b038802446c100c0c9860011558414a4001c50700c01c0e4800d400822007003001d00c07001982d5080c1650f100e104152010800e0980520507008150b20500240010a01654a402e40703400c441c40ca5640d03003455000030390610104c818500031281c00075480390b20035076040d04121407103410b0a80c18203000f00c0c5041450000410784c0f50307a00200b005010300d03001501590b03500e0a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 72490766 1250 72489516 72489551
    0x30a0c050a0605270705100503100b0d0e010506030c15071415010819170d060b0a050901090605040806070c030201090b0f070e04050103120516080c03040303080901050405060c1804 79
    0x2061350748150720455044185078000110700c0e0403148000c002003010380b2282400d4031103501c00b81c5000000f170306406000c242402c2030802046440401500060303210b000010040c2166409007890f40302e50044040c14201f942c807500701403486500119066603504043c07500302e404624410305406035010b580c0807220882c03040352416049850150555610000305a4100001e0407012001000341185480b0840d6468004026101e86500f50f540010400c0d2990040c15090300310001e07806c0000e0300041d18070500e503072044241000b410b09003009030038034bc00c000255403102c10061140c810000580003450a0501c05d40250031201c0e046041d401c030303500b000c03c009145028100c82000103d44880013003100b605051040c28100da8102e034285440c030b80d0070750044a40e07610404a08490b00d4503003a4190210303400000800d200c81c0c001c0000c0d85d03580d2562501401c1c4181c0204800e6090345000100710101e2800b1840d25484644640e029643e51684044409044e90701000517411034980750b00e0508401c002d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 72492016 1250 72490766 72490801
    0xa110a030302130501080402030a060b041e0204090e060115030f230a050903070f020904030e0312031506121303050d0c0302040e091c0c0302030f161101020708030a0c050a0605 77
    0x3c649002116440d0f90040d92aa48180c800030b405600040740e401c003003443c9030b0001c10380200c002c1000c03030f030001421340040400e841d00ba0a1444540e00281c2017000c0f224612400c400c0400c0907014003030b650300d414500c0920049068002c024035450320000b48845200780e0200d804000c40300079007014406003641d11036403058201c0d89002903501e000d0100f03007580000000d5071003455103d8032508410010760b081c4101e92801800c22802d01c41c694a40106640d0240800c00e100c001c6110565240d1404400c1480b0b0880700c441e10a0264104010522111101510042c3c1c041d41081c078800720312140340390481e80d038807030000032500d060316018078031343e056501d50028421159402140303c0e01761100415203483c0c65107040c4500c1400042e501c01c2e4401070040445c10b12003406401500d041c03038071694100300d00e07074418003641a1203450820510b0400c2205511004101c00038402040d001c0e04141010b0381e41e02c030b0700d03103031038140010b0311040000c00404004944a0b264020760a0009040070580300d00c100114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 72493266 1250 72492016 72492037
    0x1b060f1d12031b0c030706090510180c0303030e07050a0929032e0204090905060a0606082707030b0f0109091203090501090f0b0703060602030906040303050a110a030302 74
    0x115048000c6101070081a240228003c6800280d0310503240310040d65a40001c3e04400d5900040c000040442e04074420100141c0c000c2010301015660703030b21107034110340300c4510031030324040308110030008500c00c15403140680340d050030001800c0f04099a1685000d80c10b5100c10b6100c5802d08020411300c20765005144d503400d09800480507501c01010704500c1403910104683c06620040c40c265101c0508412420304c90b841180e00a8010a0000e50005a0b8007640109440e00c0c2ca8824902c10800d04212190340070310084030802881342450740007000240b0260031840c0144900100c1600384141c2d9140c808000c03d14022210400d981e841c2c0300d841c0c0b40e012503900c403072200240b0001505c42e2450240000c0e41c1ea212608450720b00708400c050b401031a5501c1c2c01e980d60365035002e0711000603002c051302080c20f41c0613000019081c0344c140c034002d00745d4606410000440d041482070800b5919440c0135182036030f603d800c010340c9074410010110380104c0840c0800c011842541101401c1c580c00d42e0003084c8032f078074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 72494516 1250 72493266 72493273
    0x9280c11030313020f0d0b01030c0f0501020606030607030b0102070506030f07031b08040209040609020910090f02180603090f07060801092702040b030309060c2406011b060f1d 77
    0x400c41545441c0d0200316074802149210300b90340d50042c03515503583d42c581200109580d06401690321541421502600221890801e0352010320034510b4042005001b4042440280024900000440d84030000540104103042d164000381500768001d00c00720001d40b501915003520391030210301d141145c0d541a9030710408079240030005660420b040c0b5101c00107006a0b00c81782420740303a91b070a20100080c010800d0300d5840e070361264140180c0e50611954044c03c01588101805410060211b0403500141e0322002101c4c810059064401d07c1807810403d045030455034951250749000c091030424055a01303995050003109004a00e5580048a16060301c50040d0100700f213100d00160b54000b488042015900c3d004c1d0131020304010300d82030b00038240b07401d809070960381444901004904070790050f944a41c1d150b000302c003080604008401541c1a140b035a0f080c1481c4a08101d40064079142948101002803061100c8160030300c042a08032021f0200700040400a911070715660419001400118070101d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 72495766 1250 72494516 72494537
    0x170a020a0c0258050319180902120601090810020d110403050f0705010c0b0c16020307080d110a02010c020d1a040803040b09060727030803010608180102041409280c 72
    0x142c000c00c070920f884d610000841c80c111200c140040303100d410343c0c80780c0108500c1d00c1d4072140c103c1a40141d00000c100619015846425100004404800050260341001400c8004100901c0001f1300b00781c4101d9468001070741e58680c2407501c006054008a1085040c8000400000300000015110054509a804c2d0b40c07545403218011920300001400c05000b00c0320190200300f5078215100105480014520b204400b1034107940401d0034400103034031801c810b4000c030f5610300820350405c0701c0741594410704024020520715a40003814103061500064041c44c51210040e0421800a41e0030500b100309d0003494800d40707060700c1d182c8103540c0103e4003250104840f1006c2800d0f18400170340c060052980f0745a18600c405009480c1c0c8407141c2010040710750300005800000410710240003580a0041940d600e0302515041910f00c01e814408480180513a104000810040701c400185000e0104201e0303000103240c1394020105603245515084813200075284030040c01c80c0c49194001030100089888410001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 72497016 1250 72495766 72495919
    0x41a030601140618030c040c0509010207120803150d0b100314010c020706080a06030b09061f060206010501050d0608011a0a06031505060d020c030406170a020a0c02 72
    0x801010b81a190032103414480041440c1203e803107040d440f900030b0211074050031050001025180f41581100204a000440d0b554a59040c0900700191041c400e0021103c0760903551040603100080a0307400d000700e100413681c020b40d81c0911006409800c0000104903081c1001405200515480100d0301041071001c100800c44e018002e011502840382c02401c11a46841004d50700090001c00b00301480e55903100200020f018091041d009102e6180141140e1901100000294000a40c61400300b100f0342000c1002c0c0743e0001c1c0080c151b450a190880d00c812148411901900e81900110b1144d420700c2c200c2081d00e00040403511041e0b008848000005076110826000c40d00d050016032044605a40144010b041c100018840c061540b2401403910103481e10450650f0016005400090749084001074400b883c0400c0c01e4101752020341c210304d0080c0e65000074103040c0081384000d0040100c035003403c402c1c20450590814105580f60b5500120a17802071901018860070039082c3e051911201400e041d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 72498266 1250 72497016 72497039
    0x15030c0b0d180b040320010c030b0a3201030b15070c0b03010b0a0c020a17100c0e09010504090c0807090b0307121e110a0b0307030b0108091c050702041a030601 70
    0x107070000c00700300f455215502c044030084442d400714044862a180031000800c401d104d0b041500c40c4035070700005c580f040041040299551507200d000d100c0e1211030040404001c510300004030100001c11206040c02c3e40006901410b44101c440390321081c0c080d948510060040000c0900920940c40024995200d03907164046010078041e500c0314039401d10000060038000c403051b0343c0306400104000c0000e50344082041c8c80400c0e500c80464240c000c001e01c061192414007421590043c01e0402d658809504408a8143e107814417420744036035140c1c0c10341c5040c002d030140d891300070f444101e080d41d41c00c0742c4440f8064041e0200c0038105010784900100060b0b85980c1e2070750690015132100d1211008506000c281c9024456a841520314618034a40841d259840d10002001050702c881c00319160328001c5000340840e40f03001c2800703040c0700c8203500b040b4403100c0216544c0d40c00c0200a04074182040800c004550500a40358000d4100f0b140c40407038039140303102034100c9143d40000c40031140140e1301e44079003850303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 72499516 1250 72498266 72498311
    0x1140f01030608060c070303020903030304140d080115050912060702010e0c0117041b1d180f0607080702070906030507030c06090b0d0c05121003021f0503010915030c0b0d 75
    0x10183c0285000c00c5000e400d0385c006180030340c02451f0260510140c04002415540161000c445c0c180f1300c883c080e40c0904042c019221411b20905103504d1071341c5024401c0c100001030844001c20010001203448155490a05240c4150f0b0b1b203c045800a140c610b1020303000300710040702d0661510984001801543c4a07107851072501d80e940b810b8007a41c1d201c595659144003603185843c41e840780d0b4402d012078003200ca01c00f070407980340489400782620308142005414800704124180d155800c04510015850307000500540c104207180303480009995122001c90400b040c940004405e1420000c0003c180440040d400d010740e405400b9175001941c0d0b9000c2a81d000c841031103244407020050000c0b0306c03111001ea2000810045505005141908800820a4000c0700b2101c08140656406050055080c03200c825028400d1180d404072036101c0d030340c0c0c0103861400144541c0c0f200f1b0307440c2c030203862003200720880f94401550b1000088110175101d6010540503048059078000852801d5251041c0c0d1010254611 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 72500766 1250 72499516 72499529
    0xc030c010b0a05030d09090507030b060a030506041401030f0b180a0803010e070f0f05070813032301020913050a0603020d030f0206060409030f0809150c0a0815010509010c05100501140f010306 84
    0x4159907c1c2c11412406014010410f0b824960356054210850f151140100303045030080d0f07400030b0303145042c070100000c90f8580780411040d0380340c8400600005110702c500100590300100c82c010b040d6035a81c4040d5000b40c0607022a81140104e000301800c2000180145040e40d2003800107410556500304111049903081903050006800d41d01c8100c05103002d400248003150007a84200d180104a03003071036801d40e240e41d004842c2c4011020702800402003121511081e003080c0402075143c11201c10000300481c2400c032140490303580e2403022440c2075800381d100c40021079001e00800b07080d684a060241092080742d001c24054096880001c3e400e15141c032580c5001641500d84289511402408551201008210b00078030710402034400c0ca088800d07190244140201b407031480d900c24003da0020402800506122642607040b0104a1682c1c1c104042e502d22003130070701c5d00c2d811841340c60804902c0c01005419000301d661901c400460031145008140030b00d64015140c1900c0c6451410045044448074070a01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 72502016 1250 72500766 72500777
    0x60f060e04020a0f0534050c040b0f0103181a0f0912040b0c0f0109060b0a08070518040c030b070804030306050f032802030102040902030603011d030414060c030c010b0a05030d 77
    0x858060040c0094860240108a611038080502c41620504c1d0400340d06c000d5200c48030300c420410010308101d0590341980645082c0454107400c004035801880e03414800341031540303031700b1080c80c00a500443c00d00110f4014030340810301e091910710b07008140070607611241c1d81500d00340040d100d000001510b00c448081d042c0c00b00d01e024034000242c2c003150800351281e82c05019152901c040c0343c009001d40d10f052801210002b071481c2c0c41d0010000100c0c4254084000c1d42c110000c100708990780e182260b40704143d000780d0100e0350f03656454070f0324801015801c0200020b0482d414800283c0c1c0c8180a18030492003514100002512101044502040c03120600d5240d8407011a95650b4015203c8449846501c84400c1c3c0e01c2001a5001070300f641c0064125a50282d404402c01c4020301d002d015000d40c011040c29441c1c80e42d4510303003c1503141d00c9079000d6400e40c286000c500c00350580b155030482da2003c0020041d44e45071040b449049000e8054900260b1184d81941030100319407501052130001843c1c1c42d100c9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 72503266 1250 72502016 72502037
    0xf0402120a150f1b09240203090d0c0f0b091302030f070c141905100b060d0b01050f0309010b03010e01020309030406080405070302030f0708160311091009060f060e04020a 75
    0x1c07002614112110915141d150b281c01396040b4146942c1c118260340035207075400346a0070111545030680c1203a01612080300c011a0284415401104880c42810169200681030006040c44203081400ba40011a20010364000058000c420000307020341d104101d81c03a100c2c24500548007416030000f651540f40749403c3d80046207000740500740a5072140e108003900c001c8401e645100c80e050103100140404442607418108040103018081e15900081c1140300b004001e03181c001191040c002c2e0200c1e10421655a6103107449680100b060f120b88407010412540c1e44c0c5460103030140a00309800c10310340a9804c01000f22652041030090768070800c040d000450401d4988502291444005802603505004099004c00582c9040c80760000201400c0c000f0310b54507142c088403a1034440010a00459a403040000f44001050140c89002c808001c4501083c6a11540c440d5241019154402001140340210004003611200300c01d9003124030710b4882d4030407403046406001c26480380462102c00201c0c0340b00b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 72504516 1250 72503266 72503303
    0x7080a030209040f0204080114011203021509160b070303050a09020112090c050d03051201060804030f0e120a0c050f010c0f02040504080f070c051002010e060105010311070b0f0402120a 81
    0xd4407003042e0040c80401d5149210030702c5000ca1744550030000c1c16945500c418250b50b01040c0703100c0e00400703610089030301580300c0f518025110a0000003085c40c0040e1113000c22954001080705039043c0300300c2501d9103881c540d14006080180c6c0264000c0340032a081c007000402e045402c2c81007507101601a11880071701409000d284004210380803088410540007200840c00d5202c1e4000142c0c80386c86034135002e0341c80340030b08494010041c0507071020041007030705010400003a501c00000d641d00960703805c1c01d40398000c0003000214a0907005040101c00d20801c080c203428400348508000864500760303054040010328100440c2c1e04c07403500401620070701ca00714080005050650007158420702a0b0f1700f03903080c8403400c404611180d1000b42c2c16581400300c00c1c41400ba0b4a04600103500140d02c0340001c0185500761a01c264403480144946418155034850281c08401581e003110071407031703104030000c20030302c0e04845202500c60180c40580c01103100e2200700007681800103035840c0481e046502040340800405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 72505766 1250 72504516 72504521
    0x16020a061104030501050c070b011712070c17060f0601030603020a050906030a0209040f0c17100c020304080307060204080105090309060711011803050f0105070305070c020108060d081207090b07080a03 88
    0x101d219241d01410080080403804c2032198074040e01030b04104950790095030074506001c50060300404110541013624204110000600300902c2a019440300c1e25002641001540030020398007034629032044104850010f080800d900e44595181300c41060962200c20045080305d100e400007e40042040509007c14500003405075070000000f4201c0d4505841580460154181550b049840c0401da082d0302c41084450785100c0e000c0c00003840c030010b50b00c1d503800c0d80942e03550f0401d070390b645804c4d91154494203da00c01d108540240800d181181d030b4853320340c40e090b002940544a2012607510b400041146140c011040f600e10030002003819040c0751b15601c4003810007900160550500c00900502010742c440f400d0f00c00700840c01000034241c01c0b10156502820b4510003031683c003c0518103010000345680000e40d0101880c0c0a107060b040310740e0740300089220340369017002c064940030010401c00c510700510480c0381d00c42c030744940d0b81399600c80d598411407800d4024800c001300785d1900bd12100301c40c2072103075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 72507016 1250 72505766 72505781
    0xc06070f210f020403030c030e0108130f03020f010203090a0b0c040812030a061805010501020118020a060e01110a2105030403090923160908210a0c2916020a06 70
    0x58000042c24008458404100c0e4496401100400c0e41c4601100501d07400c050f04078211002030810448030f292103402c00000b105014002401600d1140030b4409051003042248904422580210765074105000304540d10f001c5c880003201c80003d0180001c6032950447c3c1924200c0366102c00a01030000d1022104a05400080c0700002c0c043c1e0781c14002401450784410103034400131420b000a41941400002803d569804103507200e0203031950b9600b001600c3e032004060441d82c1c1031030a44600b5400c840102e803c5440b1844443c503600c00e09000c001401030b0041001c83e125070b61103070705801c00c0d100d0700d069a0b680011540640403c604c0c2c10304102c40078064210001d104c240018105454a8070844444895800d071024040000d652010040c40b40e00140340d40041c01408009040c80140d502c0343e030060000345401c1703030311400c004240f038210305005240e075141e500c1d80401d01c030100e8601c110054459150303200102040e400d6400100715117015062147c0100c0107160701030a6000203540f9040080c0120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 72508266 1250 72507016 72507077
    0x151211060309240f060102010203040f080c120711090105030f072c15090912030a0902010e0307030819050406021e210408010c08010506030106031107080406050c06070f 74
    0x1890004401d43c041c4a00314012042c000049481d00d050880820071810710003411a81513a20401c00d200200760160340b041015a0b100325850350f280ca088a1140c00c098445280940707070325011800c1810445c00e54003c001b106001d503a0781c203180e030b07950b020103940f1780010a881d070b80d41d04800c90512a10049102a0314007a1121004042d0703200c2c00c061910b0588400c407460807985c890011751130b030103180c2202c0c1035402401c028021711501d4003c050004603844098448058181e40b03e42c440c045900400400c0d1080c44010251903100350f6900f441406680b008500b2020010380c0da4035800d00794010341c141c03025a5156801412120f4401031103003000420f561907081544503149007655400c1c180e1588164160b000c442c2d850310380d40b51803846429281c4501044084c000010b0042c48182c0307070242501e0440c0d240d031502003600650741c5251600303071160300b001034559140040c010802a820800409401c042d07441154811358a411301201d83c89803400c0e03038030b000461000489400300074108a60306111a17 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 72509516 1250 72508266 72508273
    0x60e0c0304050717100e06091e0109050a0c061b0807030f12050115170103032f0a0b010e180d120f051005030f010c0804030f11060a151211060309 64
    0x445864000ca20100030402100a81c04217801000742d200c9800742ca002448140700030011410044140c5880c3e2802c1840100c9005103007900c1d00140009400411400380c00c4800d403040c11080e03003000200b000b0b00f4052078000c00c903440b01c0f40041c0c8004030302420565030004580d5040c45003681d02100c214103849a404200071041142e0400d240c49481510300070a00b0b19070300d290058080f200900b00d1000e20fa042034546090300010800310742c0000c5407034003070a9084d41d08407100d1181090000861004094025103224076030301c030001c00c08061061030623642d1041951000356100c8280c02c002801450309000c09800c00961034000d680038510a8200c0d0502d00e8000c0354100b240740b248411210121110400e641c486801082a41000e000a51046079000020b2050850303804025018030310141000f41001036209201c501c2e0303841880c080584038040000ea0f8982e0500382c5034080603190076000303034929540300d10000524a00e0880000180e69000f00003000a90910701041002e41000745000300d07502 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 72510766 1250 72509516 72509519
    0x402030109020a0e1006031e0b06040305070905060913020f09060a332a080408010c030501050307090212040f0f0510020309070e06030a1502040902040602071701060e0c03040507 78
    0x2c3d640750f03200014000c002d9030714159151214401c03640340c00ca9800f820a151401c0302401822403000901841180b40e9130b80400d0700d901c2d005c0400d5080c8030b02e90010b000360040103004242628150031460007010102e0b051600c1d23441e5800d0b41140d20901c4100203501409001c0700303021a0030f0003a41c0a81c401401070905c030b20075035900c00c15440b26003125402c1800410120781500203241c0b1400f03030140c0c60f01d2032600c241209150210910002c4c8240e0b0714001004e141100c071000c000c5038004960240c00c000c1d00030310240a4006000e006400d080c042c441c030900a01e48089000520b074030a40b1500c945490b0751f0344440c2c5960711034200d603042c03004042d100e1751001e0075981c01248041000030200002c100300185e0740d2524800c402d0510300d00b81c229100e002044418081c4942e00080c0d10101c654001064540c40e1220207140802807065901411000d400410300207400c0d138001c00e02500300e420090301c01032850501c80b44a03088600313600130030448008035004030742e40044080195902610034000c031419903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 72512016 1250 72510766 72510769
    0xf0b030f07021c090518041212110a030911010206090706110c030703030f090b03060a060807020c1c05012403140a02150913050702030a050a02160b04030302060f04050312040203010902 81
    0x1d515603281c3e480400c041c500208100d091011020350859000c10045900f401d060355800341c4001c850303180c0c4080005000d6110104c041a500003401100000c520a0361081d0000d005400307415a641c0079507060107445048080d135400403800070701c10b24a0304041c04105041181c20b50306002c0c0098072004074840c1d001440a00d8404202c1e45000d14043d40b00c1d607541c1403866030000d00902c0c46070881d000c003c0c400d009204c442d440c1e40c0407075020703241caa041c0780d0b01c6c40c1d8822400300e142c05594032100e6401800a003640101d000180082824680140002d00221460102e101100a90107065040301d68079050301704041140c00e0044e5501c00c80e0b000580780054556000503110392080300700050f0002c0c0000b114001460640c040c8060301e500b20070240301a15008201940300c0c043c038240501442000a504d04845100f40044050380c4050b145041d00b041c2c655041440f5038001d40412005407041c01c01040c290300d41d840800340701d65032100c02103140c06850032030881400d1010f070040781c1641d00c400420006 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 72513266 1250 72512016 72512053
    0x4050603011505190801050a060f090207080409090f0f031d04020c0606061b01020d061701050702121804140403080f01030b1f080307060b190302090f09031213050105010f0b030f0702 80
    0xd5442c8238408034096080400030110441a6400b8000c180e10400420000514035015038040b0380c039442000a4410803030812200380d61013a50700801908a10102208040d0043c54100c50006030303490f40381c8600d40b0f903000c1c402248240742d48420150300c004001001840c122000b07200090b801c200118505030342190031826038200c83c45d03068000b902c44d8800c1c462662004504072504e00c58000901244c10010406525403000d541849001440011414040741a51075004400c80029008000900c40c621000e149450190340c1180000c031110041a4038202058526041c0c81d0001c5041c5803e480c1c180e0244058144003010b04ea061001c0720b40000c1075501400070f0b00b0a0380c0a0a404030350300200108212007008060a0281c5030949030605102513115030429992019511303411354600d8035013102e140e1450107000405000d6114000400500f0042014484802c40c4200000c1c0501d988940c42d1041104281c0a416003441043c000540702880d074103c55904038106006075464266824100d160 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 72514516 1250 72513266 72513271
    0x6050c070b101a04060509091b13090501080c09070f1205010b030405070906080a0303020d091209080705010509010e0402090a03121107150203070213060f03110405060301150519080105 81
    0x18803250b16001008a0014611884985040c030881d1a1800b400c01c00f02604900944075124000c0c16950001200b8044460442c1c0350641150300e03207a1101007001400e0000071190103440d0340c07a17007081d000159249001400103d0020020710038049596190000c0720503000e82441c000c01c1000d4004544d0034100d4620030140a81014006a9913031701d01400e10368903040e0a940a81089407070070f0030030848103001240b50050960701d8039015a44500e0106000081c0c84d00b040060042000c4c4803c0f0700105e43c00c20510001c0b40d540d082902c5003a940d440066a50307000d03c1c90041c0c081500d0594001c120320300b0354000c02c5c0c802c0307008090b0030702c4640300c1e119100b9900140700f020010540e01c2c4129418401d0400c50b11004001c111802e08040e40d81d41c80c02074880c010001c0c000c0c000c13030300c02c03a44c0b00d0a01125041603001d0600003500f14061540d03070414202100e0380380440c0d4040e501d041e01041c46400c041c01140300142c2d440c0c070381e11000c92805082c031483c01c8110a040302c41c45500b2901280b00503003070043c0390 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 72515766 1250 72514516 72514531
    0xd030c0f080d09020301150807150302120108010c1b0305030106050304050f060a0f060e010503030a0809030c060702070302040c020d0804020913140a0506010506030f15060705030706050f06040e030706050c070b 92
    0x42d007640c071403045c1400c6401c007402488404c6e426810820403c80c0c00100031040c0c584015584a400f20040c00541c042d000c3e0380c041d030450003c0d850000c0390031407055001c400101c0059990101c82401e080448404010120020700010020401445841c1c06440190f40040c45601102c00e8843c1c044440707400c0882c1640d13809103468070f0ba071405800140f0740c0030f01e10140801c140d0000c0e6651510000941d40d1040040000c10300c5845c100003000b8140c1402a295402030f52002c0e11042d20b40400000d448540c240800c030301c19071408419a496034030010340c0c441d00341000e4803540c0450315150200515488002e0580e41115202c545038000078142c800c0c2c40c0c410b5001030000380308010592410504118051b007105024200038420800c541900410300c40e0494030a030542d00c0c140c59100041030031403040d940302615500c000603010042100c2035002c10300c00d000800c60362503d51202d10404c41174942c0d00707501c1400c41e0b06c140a1a40130076400c0c2e003c1500454010001d600c3c0c1240c42d603610321103100868408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 72517016 1250 72515766 72515771
    0x30124110d02060402040e0c0108270703140d1d2202070b0105090901022109011401080d090801060501020304060522120c09050c160c05030f010209011d0d030c0f080d 73
    0x1714141801080d000c0300454019211101580c000280b02d000d00420f0800548440304003840e075440960b0516050496005c10307034801c60345034204580300c10b12100040d00103100300f149914900b8401c0324840e0007501c43e5000d08000d07800319401c2140c24111037403503000c035850035030340c4c1e9606014901c01002c12510981000c6502e42c03410081020020b0014076050460340104200400300680540c40c2d43c94548509c1481100d40780c101c0000d00410f03250b0081c1c40554240c00010500c01c0f00010840e01a0680350341e890f030305585418030b44c1c0c280c680c80d00c11240981d00500c030a0190350702400180c4039204694103141c050180000310011a00071551101e07400c20082000307041480494010b9901511140105104e10300709104c1c0003901e8410207005004c120782c2d04203031104208641c6035000044c2001012100346400004005000794406903105000c40d04141200307510311070601e0141007100c4010500c44022006460a940c01e4608101c02c90782d0700d000d41c0d2108005003400001c0c0100107002c4a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 72518266 1250 72517016 72517021
    0x809120a090f0f030b07080c070609030806120c0604050d05011803111c0c020402091c0819090305030f0c030403080a02071406090306070516020612060312030124110d0206 75
    0xc00104040c0758020b00f40c00894040c0510104000b8403000c1c0c0c100005151040e4180d0b43d04084280d06c0c052074000402c040d08003d240e2060640c0194001c0c029241251110385120030140c00d0307030b5105d4505030a640c000720240700401c11031600c100e40010050084001090900380c00d04035001504200008401092008a000e000e2900c10411450040c4a81c5500f0f2229071001780c002d030418034119002440f171074001820142540b07070ba055109102154016a000e0465240b418030103940145815101c1c110302c400c40c115420344224000411250130001030740c5060180300c44518280d12051011003184030804c000800070310400000e10075407000d0307805400118140b0290400c2c9101072440c0511500d0300b806414466600440e003190460707201d0030110f42d00c040b5180028051a04076102940c0a070010503d12a604800700c540c901c950411003e4a82c0c903041c104030190fa5000c01e00481c0796500b4520030342e0089080d00020f1950760200c0d0704049448480301031800385002c282141480050304040103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 72519516 1250 72518266 72518279
    0x11030a05090303010e0619030b04150b0a0e0a020a03111b010b0907120b0103060506040306050f06040c1b03020c04020a2007080c040f0b0306070206180304030b06010809120a09 77
    0x3036036000450600a1481c1d07501d0503100403007625000c1c0031184601c40120106002c0d60342016400003c40d84075040d1180361500d400c160403c4035150000b03107981410803440c10070a28000315030030165005089030811035195604603500a41012014a041c075a540b000c0c40a4041002c000c1c2080c190b016141c50150317103640301070310309698040714134a0040704850188159135070018500481520070320740000d00c1e0245040120060031459006a07080707034000401105200054114034440d0301d848400200f88d460300402e11085034240d81c8010005006068500300325a491444101358501910480b400181c4000c0010100e07400044085c0205800034040b80d446c241c0d100003484081c003601c02501303000345480304040c1c6a00d0000c201030f200744c0e50b81c10400d04010301035000c1c1d0394210015003280d0a071b1520200c060355500f02901d0070f00c041c14a41c0b01f071412101d400822607090701e51000b510310f000c0d1510303001908c040c4006000d5000900480300f880038500d01840180001803003d84c0c07204501c5280c80b5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 72520766 1250 72519516 72519521
    0xf021903080a030e0115050108100b1b070803040b0f030c0705160303020c0a05011e020703060c0c03080c040b0702130f1407182306040305030c010920010c0b0705090411030a 76
    0x40d003407211350b414440c400a01c50354081588003215002e080803662551403511402c0000d420383c0000b0354207480450004041c5034245114000003456400300d0700703401d0f01c034800f00c1c0da03c1c0141e00ca50308404908110905080c0070140c080c0d508600610080e038200080c070b0341d0f01070402d042524140d42d0b1480020007081455410403a20166410603180a45880d0400000910310004400d01c40301401c00030410300314652003040103030020340e00030300200202114150010007000d22a4019000240b050f80446c2d410344c0d01400711001c0b602a1207a6510348000b9509008607010f000030a0540c443d41c6811203188400c40c0c0c0140300301c80b80311181048051518040c05407200d4494802400515900502030208504600c0401c10744482c1e1f00001e100c40c10180c00050380c1d4412a04021311a0001140703d210704030f0b0542081600038400d40c20303905111040106094409008940c003400100000c5040001ca01702c9070300da5421414928082d03180c09020800700702641d2018035440d044440010070030a104101d132 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 72522016 1250 72520766 72520781
    0x12030c09270c03151903050705090112030c03051b06040201031a060301090e120711040507030b10080604020d09030c02120106050d031b060e0105040c0e010803070f021903080a03 78
    0x46000180d1004540e590526041000b00001111000003000c9154060401c401d100c0b01600240190702422400303d43c0c03e4905a6403208a0f46031003011004139007413809841482c181c3d20b030740b03115100f03000150710b049824914040c01942070100402c40b4602040790018420140780c4148020003150400348001402c0303074180c4910807940d460560b00041c01d80d440d40704590440c0e5141b000802c4916040000a08000e20740507070a00610000404c1c0d0204a29003010300b10fa42c1044508000c95a0f40d21025000d81b81c07106005944100324141d0303007803050302030349456800c007402400050804283d04041c02c1152140102980401c404041940844ca00a0340011481e645c401c005d2020514040110360f42c407030043d100030140420702c01c1443d02c502860030400c4201d43c10807000d001064901d1300305402003106803001d0784e400303528840205401c0400c0400504076540b090080d4a01030141d1290f00a404403110100d900a401c01118580700c040040081d01642c041c1078950395460b40c3c8640a81120110f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 72523266 1250 72522016 72522049
    0x111201080a0c0b210603030f03100608010806011206050a06031502070215160f03051201030b0115020d021b010e040f0b12070501050a0e0f0d050f010c080f0a090512030c09 75
    0x70800c40700107000c13202050b40d856034003501e030306030913152000042d040d03001e803c07024402090b002c0200081c7c90189195901203441c00d407220000c0703036240c030610b1340c03180030900403000741c1c8128003498400510140e000a500c007850010008000791240e55480520070f440510117201034000c41c8400c20340c50513122101e0701000e0304144500e002e60342c40c022001108041d001a00445014003001e0038176003d00d0840310f005c0004030100a880da101d00d018160071000f0f02450100200003000a03082c0f034000030b14140d003516140c0040000c180d4000101d04840304800c05181000118030003c0c0450311540500c1e082000e0007030b80440c0d500c0784c2d00e043c0000703043c55527100300e4180c0c002d090400803642c1100c1241c640c440780d8a4640240c02c00c0c60042070380c2a404008142d0015a022802024400f0203c1d1100e044030802d802072101c22540401100c040c03c007030383c903441103040e00310108910507603541c40390700c031300748074100b0344c1c03d541280c0c03585100c40c6d0000c462401d034560340001d201c0d00c549010055002910311 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 72524516 1250 72523266 72523289
    0x510060806030703060905070e0109060e0115020c0907020a0204092d0c0315110c06090c010201090201080126120702010210140a1a0a090207060e0a0312111201080a0c 73
    0x400750300095a550f094407000e801c842d628840d80050060030310500c0c0c080c00701c5007a010055603640d06458014449c9200d1540008900e90001c40d1010040064440d2170020b07500502d114000002041003844010303081c002075100c0c0140c2c1900580f5103000300c0f10100d01500400c04a40000c5103040e0a1080780c5c0400f19589030f443c00c041000822004170b140a0303a4004045041441d02c41d04400c0c01858081e40303800c074002c00428807095a41d000640c0900c01c40341002502c4280c00c4030300059003600d502c5803000340405c11020060114121135803100d000d010240c1000780441105902a50400320b02e401800e9145000103580e00955804100c0c040134542241d004100c00949030070303404000e0030082c2c681840aa296400f060586a2944801407080b100800190901c2e903203095880081d840590100d580f5818100c00315090b1002081c0000200d400d0f44612040110451f10705000740400d1440c00c02600f8207106c100321102c4072011103406001980000d081488030380c141140c900e1016400a0300c030741d8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 72525766 1250 72524516 72524521
    0x30606010504050904060c1808030306010e0a120609020607020a0e0709050105030f0c0c15070903020f030c0d0b040503040f0b04031506050f010311040b07081209010b100806120d0305100608 83
    0x11103c095070b42c0e125801210003e51f201c45008100d035501c0d0030714441d004000900d1000705d1081408030045000e041d00342c0320030703000c850a9024440141010f200c0c0d06c00500282c02001c010569a0300461205d42c4020f1407d85400415400250903a4441d00420b02100018042002c860b81020328071000d0300c02402c04900710f1030030080011031068002c0586a100d1070124001107034907c00c21040042d80146ca083e4900c61400d00c00080c0800e02074030007a0702ca145184856209800c0204000f202c41c0009070041401c0b000c540c0f00d200d11881e01400c00c07105071100704000221111103040c0600078110100c1800d641d1440d6003010880700c6170418072096042c0c80c207441001990350382802150022420b003404207810340d1900404c9505d002d207a00043e019100054a034007000009001032840700c4981c0d454007440c0d100d803901301e400c03101c000d1900c98006c201c5a0690381210700910940d41c0c8403000400101c6811002c09041d42402100904078011907100e50612614011049046015003402d252418680c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 72527016 1250 72525766 72525769
    0x10e01090b06191718070506040305060105100c080706060312110c1201020f130303170903040e15060a08090105090a080d150506070807050c04061d0702100c020c03060601050405 78
    0xe100b040d00784506503003142c15111003030707000722000a0020740e04c2c900c9100c0740c41d18040e240d18181003041c10300c0260089140200700391034405e007600d0540c3e80060060400d6820321044c85883c1d00034440c40070601c1400324084000070340c03001c02046414440d02e40440c10360710b907103841241440000b844005201c1d840030215403200002403e00100042140c00464035000706040c1802442a081c0d00c000b16440020a00242284c6510340000c481c8a661040c11180020315602c14405050b1800703c07454004000c00c00014103603091031908000e081280c0b041480941c0d00181440d070242c581a0041440d100400c42c0741d10080c402d29074480030007005800c02203101d80d5004000e126850021980683e03078100540d1249421100303034050100507101c9a500d0a990401403001d41044070121020711038030030034030300d20b0419000b408100c80030f00980541c000d00c9455801c00c01e40000f0000b20841c884c0c034803400d00400d458041c102e24450207070043c180301d80c00501414140309004001d60b061002c1007004000b503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 72528266 1250 72527016 72527029
    0x61302060a0c110d0317010501080708010902070302011b02011e020c0a0206030406060512030706060801060f09090f0c06030902040e0a03080705181807030b1e040c03090206030906010e01090b 84
    0x200810785030004041c181c600c3c01102e882c110041403500007a111021004040d0404401c1c807400c403900796045100e0baa1031004685d66081150200c0c0011801c80040154402d075402030000d00e07100e8000400c0706055020184030100c585100c050050707443d14201a4081442200d0212141d051241589402c00c0035100d56507c0c68003030402030181c1030010005041c01020b03400a0080c100003441050740e0341092001680c2da40200c0c0f000d6424514104000a030040b051090780b040301d90400300070301e12505e805003140003414041c109440102003004185d00080d408046900036040603240058203040d00d005210484012091070240e6921a068007404650080035071640302407180f922968614540700300807034100003441515004810b0300802c405a0603041001441030400d651304000d090100403c000c41a00100605803c1c0491020400c0c0ca40c00d0a0300001030100403810003007056031190b40407900c42c5c0d00440302c0e843d280d0054001441000040e000046c0100401e0409000f5100c1d03400c0040d14 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 72529516 1250 72528266 72528277
    0x1115070f0e0a2301031d01020405091303020604080306060706060f0f080622170409090201080a141f080f010608150c0906071106120103051213090f02070f050304030506130206 77
    0xe001a1011015842da80303e500003000766802c0c12026000e40f400c041b00300380030303420078016148103c2c9650000358200c1d0207641c2880c1c072283c05500070105910307070307442d004000e520240645030405400c001900104905d0301400c4000d0039080781001c2a00e180400602800100d600440d0594000500344000c8e03a9000300c10300350040805601d01c9210029140c032816050f03407190a600c0007500400e0000761801264000d001290007a01e0b0000155603d030b004000701c1e4500200051f001d5480c1c800b080558850803c19282c2642410341c40607400d40711192980b40142150b100e41e0b4903915080180030500041c0422248408204441c43d03881c148204c0c1381103540501c26055000b60700229040040c400c40380e64020401202602d942d50300c2c40481506140ca000c01d001c00d80b11441008450811082e0100480300004038070800509454280604840906503141c66048055000d124910108103000c803401050340c881e4004640e1580b440ca0258205000188005848981121134001684681c1c00b00c44 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 72530766 1250 72529516 72529559
    0x30b070f0806090601020c031f18050307030e030c1207080d020708100902010302041802070507050303090d030309020d02030f10060501020c011205040204060b2b09080a1115070f0e0a 80
    0x2d44e03403440700403407500750102c01403641407041d00c0a0380c0234003150b4004103024085641c0c0c284420220004480340b100640c800c0103145500820031440403d11590501000d10342c002d0640d24600080000144414103841560302a5007110b10100304110080061031000046030001d4040700e443c003074099445803014500d030143e80e5120040c0104584c420360444000e44040000010f800c950b1004c207900940010030211000e10030f0a0010401d460000280c0c1c0310a18014000c0081401968048020b009909030032038100311401c240100507a0305001e161440b0b13a060000300303084050803c0c80d5055038803a5000da415034020f0750105a2590703008891007100c5601d440081002d48a501c04a0010030042c0c0c4503a04200004c02c3d400e11a400d14542c0d6240102d141c420400190801c0300444d003101c2c1030b2040105040c3d0f042150300e415a00072480030b1480d50b411001e50314820441d0710400c0340703000d048407408001441c05186070348a82d00300e40310310b48410b070035100c180c003d83c1050322030b42052440e8a200f4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 72532016 1250 72530766 72530779
    0x30201090b03181207050c010903170906040b0703050705070f060203030a091407091d070e16020a050a05030307031103091002030a020405040f0b0f0108160c03050d090309030b070f0806 81
    0x900752403c035488600007005018100c1e04c074510f049040111681104000312400d00800607115540c0d8440c20069081e650410300e10b40300f51309042d06944030f550100d03003039030380140c4107000010b41001184003a1034a00c2c041d03121103907200e840e490f0403400c084071500014080083c00c40f003030000d5540082580c3e48118441030002d1032250b181094822000c04e40348040040c0301d184d0010840c044190025a41c00c40c0f5842c042c44d680f50000741c4a81c80d500700c1d01501c2c001c03200d50b8000035008220340d40503803048902801902d501101d541c64550600303103d0a81070300c26a0001040c0000c0a0345407003511030007582510700a085090100d0419200d0111441e0380c0c54003500440803643c1040c03a0f034126401403500400410400f06003680b81c0c1d01070079001d5881c6101d152020700c0089154069500300c3d10402400140d80030b00d030240d05c02610303103044c4070509904115040c41440c1a4902c144100c0c14401d00075102c0c03002461079840c1200c141100104103904012445906613603e41e044031b40e0941103038007100d16 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 72533266 1250 72532016 72532021
    0x3021f0204050d0c0509010b0c0a060225110a0e0106020a03032c010906060b030c040b0703030204030606090f0507030c020d0c050c09010e090c04090b010b0310030b0a0f0e0106030201090b03 83
    0x5400a03010382c0e0440c5a02c40d0a40165400704520405888111039055a0852007070782c1e5502c42600c640540c0740c824180c0d400c822203180c0012410b034014010010b0424040b020143c0300cae80c0d0300d42501d21500f0110b403d022103490105207840e04810400081640020012056040c03860081d00d88000c42401030074540c441d2442c0031103c9000c0c0d2a140d911011941340c041510900100a020344010441616441e24054012840c0541d0a085a100d2a80d9400051915140a501e800c0d02d520040c8180d0816a00380070100029125014080c024105040c0201d90600c0a1050600b150740c098401010f151600c41d1074a070684e00072502041c200d00038188201d0300a024104107050035512580c641d41b0140040010400c1103d034010320303004404213821140c1026401083c042103607407510000e0141c1c80110010800f9682c0c000c01180c5c4490304101d10707100c07581d5a40c1c40788403820090764600d5860b41c460b0b000381009105445a140d4800240000303016440c0345070006004200c00740900d56868400100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 72534516 1250 72533266 72533323
    0xf0d09081602040b090606070b040501060b0301090903030c0206010501080105060c0f010c05030108121611010c0203010c0509030d050715050c070b0108070e060102031e03090118050105150306040302 87
    0x104042440d0014000303030741c440342003440c04141e080e9144124070030b91402405000c942040c080180c840d5001510040c50b20599403204181d007007000703000321440c1d0341b070300b074040340c1305000c00302550080c80e941c840800e0234031152030050199415400380d9000c540c00b5a0040200c4d83e40b02d0072a60448006459055440311024407580c1407004402c0103142560a01160f00d465550005c0254126058401aa48090283d0149440d5031151400310041e403400384900d8030100c0c4c0c0e050001e04944a0505008620b104150b0100b800d55000440500104d100410a03403100c3c1070620001c0c4680070b0618041e4904146c0d41d5442101300008900c0034492580d8100042e5620481800c40d25010f401c40340c0d001c029039480c6011a510f000314000e0701250030764000401e955500002c00d864083d82c00c50401070407106001d020000a40008086030300c6036403240101c158110600608118150003a400890540361a0b241c4410300101071955030301a9009000700004242d0100303004001c1c510030407600000e4403030300c00f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 72535766 1250 72534516 72534521
    0x20f0607020a0f030c1208180409140d09090606140d060b030c091e0906010305090c04020a080f010807060f0c061d0c130c0c02090402060c03030c031f05060f0d 70
    0x22002900842c4444000c03a845250030200d0040342e114a200f04800358460045484215030480c00810384030040c402c0c440c0c0b0602954440f061614003800002d400015034440c2c01d04c42c510380d43c0551a641102c04440011684041c01d5409402c0803076041c0302540c42c0800040054100b0600080c40e1f44000c14220601d07442c9810000081c0325140d903d0303031130b41400d50000103a5406491110300c0303910110810303401c940c400140903e00780401440042140d0390080194049c020040022071345018219a05000341c1d80c5101400201c1269071350802e05140401d1140420b020680040049900101081016981c4213107003050030400f80c074141110840d0380c81e006025045000a2a140e880ca04800c90350103040041c080e400c1010032030b100e10403901000c032018103c801103c120000034402500090160800000d05a04548080c0080c0c1c50078240600250031500f056500c1140d074a000024008490507240000b84609009003884922038078040c0014614403a15120301c650250219010800c2c11599 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 72537016 1250 72535766 72535777
    0x12070807050f0304060906020c03010b0d0f0507080607050414030a0822050d030804061406030601060c0201020a021305071214130201020a050706180902040f030305160501180201080a0209090103020f06 88
    0x20421070362115180e8901a02603c6d45000703a100500c540482800c4624050049103480400a0710005036440075072152442d8260000081d15544113a480004404c00b041000d0381c0318400c0e17555556150f604050b10442402035141110f48694460f05000004c00c1c0c8070011103054035030000c1134504042001030841440300c2980d01c10341d44002600c52200c20715400c060781c2d500c11071080c1da0401090840c41300721810700c00706a07541034140c0c0c426001400014010303d01e650849005004481100149600107281c0742280810104007a0300c85003031208203500305984881d00300c007120003440100c3e81c1c2510107041c0300b8028254151a1250b140140559000340044441207400c072042d10f44064540c10090003c03240c03401d040402c0f42d00c403c0e00141544807842500e00741e07419803580c1c040a07481c6403000c0300c1c5a040400f003c144000d80c0000b01000030000d204a504286048030400c5030510203000140c0058001000c00058034010050403c2d65036681c1090b9043d00d80c1103034019801c03142800400c2c0035000f130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 72538266 1250 72537016 72537043
    0x5150307051302070c0e090715050a2c0901030f02010207170c04090309090203092503170901110303010f0303020d0804020306040210030e12030118180602030a090c06030c020105091207080705 84
    0x3074410302841c40c7d404500740c4d0549a90b01c003c0c0800e030701083c2c42207416100c1c1c0700210001543c03440200b4411401c0c00d907660030361600c521440840c00c203d18001841884280d10854149280b80c951804550f01840620014145000421300712811204078548401480c0211441030355904010002c060003814004060305040f00b08541300c0c03030030b406007955402c040c10101c904881c0071100902c0c8280090511415289e02240c490b0000445424104842d040342d50b0803818000d020700b000d040140c04101a60080001119004100b03285040c00703414010342030304280c1007103405003c100158400150b00b41c1c1181c0c0c1501c0d07005120021031030840c02494402501405805492030000b8030700c4d601805181030f2040c400902c6031003280446030340100c17000a0b49030b000807010420b02074082211035001d19031201c1c60a81c041401e6107e65503011031040950480c401081d95030145003405130b8244186503000710305a0007420000986100e5000078015038200601ca001c000800368102320042c41052320083c031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 72539516 1250 72538266 72538289
    0x4060b010c0b07020604110604120318050d0c0f05061905030601030905010c020708191a0702070939050f07050a0506090c030d08010f150c0c060305150307051302070c 73
    0xf01002e0094603171205403800d44111241d1003032958585005030480e02100da86141c10080740b007465034140d4501b1000d00c582c1d89801d400400c0012951140c80c3c0580701d040c46008003014150905a01e2032148200750070640c01a03400b840303802050301c007440e52032080d40d22f80e0900c03640700e03911000124082c2804000c01807095091980c040081038000510f541a21048020381b40301c107903060241c505a0901410180c100080086280380b0168400340668100c1014415114512f03120341214085d03c030720708480020b000f07101c00c1040241c516294503101c90a80b088607480300140c8003100034028001c490804505000008029003005410080f59000590200c103603034842c542901c483c1d03240c1c1c28074594036009010315014199842d00c07800766075040c2d401c00084558000c3c102580ca0b01d0404440d0782e10001c1c0400d694184000c00c1040001c2c800400082c0d501240314034200500103031800020102ca8001da001a6040c0310940e02c4c1008006e09481c01d940050f08c407065810054214001540402020301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 72540766 1250 72539516 72539521
    0x402090301020d0e010b03010b040506030a0605130c2709020a030b06130504081206030f150a020d14040c050a14060309010902120a031e080414030903011a0405090105040b04060b010c0b 81
    0x404c1034000301c582d684103d00811034200c110040c031003581c408483c01a07064104410810008003182d00c0550041c00030440048908001c0d0740e00d0100501603001002d217000d00355440854100a010f821801842004040c0403801003940400d03089600ea000003042c60305800c0000ba0f01d034640320584c08100310700403030500160909041016050703000c00005944400c6c0c4074000f55090600180240e1412034420040549082c4150341c4000480054113060440d5001c11500307a00100038018084c0c03e41c0c5811b000c41c0d445c01d00d8504000c202c0140c1d0b0006004000f48001002140c0850040f500c071600155401540c940e40c0101842c0101110500250f01404910051514070400951400c00d28425298101e00c88400c40c201070f41400c0040054000500410001d0b000803410050b40d03224103403940440e414182c40c40d00107030075102080c40f02100d40b030668290030340c107181c1030181c0c1d60090304100007040036060585501c0170701c08000f08054041da803210302d007088692007041c0320342900e6005081281c550 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 72542016 1250 72540766 72540791
    0x13060c1a190c0507020f060405090c090f0603040605161409011101021327020301030b04020607050a0c082a0307030215070501020406091701050f18070b07050d090b030907050402090301020d 83
    0x3138104a80c164015021100c0710b20765420007504450030b8130401440c8120a03076550400300500d40c08002e013940c0000c0c1020f4142e80d0398580402445c0603610501001c61b07a0b1910160410f001118217405a0400c000d050600b4214200b1300c040b40c22030b100a10341010015090f5220368003901c2030065184000a02440024000028102091002150b6601032824544031074200b4207900003030102500407500100400e00500d005030007442c04510403411340364145042d864483c000d103040e03880403603190020780e40569031204100b1510741c2c1c0c40c0c101d959030020302c100d040801d6481c021400024000e1141c202241407012903a405d940392140c0c080c00030f41d603507501c4d002d0061040101d88650260f280140103810710340241801890310402106003840c00549d40e402a03500f0000d86110300d07503840d000e11840030440c131035440000d0020b9800b503001810b0714400d075200100f0191b181c2e848424035000034014004800b002060341c02c200e600403540940c4414040d40043d00a11903030545d02c00340c43c80c000c11080403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 72543266 1250 72542016 72542027
    0x160f02100206180a080f07150c020d12060305150603120a050d061712030606120103080304050c10020312181e010f0c090b18060309010213060c1a190c 66
    0x1e002410303a808260f100b2004055984c155415000f084024240b00c40c0000641d900d01074954140180a80d181d0894110b1034142250001e070150300040e0420035100c17400541184481081d1004c1c00420000c4074550b0b02e40603201c000b00c3c16204490080d500100e0f5140d5004c2002100d0010f242d04030980e00d05403a00c001d8030a510070f174084142941090030020300c031001c0c8508500a168503001074030688510824442c540d1f480100700650183d8240700c052030600c2820b070400d018500c80c0d16859564102810031501e00544820403611442a0340224080b695001c42030f101507000b10480421182c50f5400641c0760841900c0340703601c1c1c0f4400d41125810f000050380411407020341a40081041d4888105413078181c948502c480004110551403c10090480c407004051803404a1305c441c0c0c030800c0c0840000c0c190782c81035814494030b80d000b00d90400d500c10618240c10040c02c180c00c0c11500044180d50302e00700381c00d200ea0500001d014002c001925100c90400e81050850b5943c003c01c800c14010201418 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 72544516 1250 72543266 72543271
    0x10050f0d140708010b0306010305090708070b0d0b0303090315250807030e0c0609120a020301091b1211120f0303190515010903020d1a0a0c0e1005160f02100206 70
    0x105006400200d910b0501070081e45040e0b0f1840c0a2552442d0b0380c010056001d0440506409a07610a16500050401d014040c5002510080360784c507a9880180b99000180c4400510300d52180c2c00400000d2181e9500003080081000340e030307240466036542d4646200c004032400381440f0740030200f84082c42005501c200b4242c86001692000c00181060502c05541e91942891050300300c00204441502071908010783d082103004103080308c541440d10360201c0e00351401100d0441d130248801d220000301c411903a40240181c10141c04980412019864501c4e490800504160041e45c903484601c64417030050203039442c0440f41c4001c60707550b03050508001e001d880407145030046a518080101e80280a182540b070b01d2240140e45202c041c0d4259000c20100c17040c02e01d0120740401c0a4140b0211400500c0c05c0c5500c24882c0d0b000002d89800324036000342c52000d4420f912481987c0c58440b41c50349540000a03510b0040383c0403070f8048605603518008904c00314414001c1d6208500410f44034825600044403407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 72545766 1250 72544516 72544541
    0x6020a03140f04030801180e0708030c0d080402010206040204020702190b0c07050a030b0a110c060c0d060b09011707020a050a05030a030605030307030906050a030b060d090501060b0c03040510050f0d 87
    0x3907a039445504000c01141d05a0b070050001d24050b00400076150340365100e01d0311641300e40000500800104c1c4075481c240666100042c42d8001041080030207000748008900c103030607420311440919051380002d45842e00200001e12a0b680424024299241e14120420303180300000081070f0951990101c00c3d00760000c60030360030300d0b00c40e010011415082980320b01c0d0884c0d43c1b15440c2c00c1c0710f4a4052034640034151084a1100040e02802a200c07800000c1280c0e40c020381002c840e440c2c3c1e414000903042c058078960741141c400d4a204000d4607c903640d100c0b20b6180d50040364510000c00b500d40f42000c0381803a0907460013074402c1c41850050024000044000c00a04290b500d0401c04559650149074032402104805004100001000c210b507d00a50082040d40e00c90b20340001c5007400000083c142e60800b010504510759540308080c100b203400d20440e0040c150700c417650b40c10103c50700356180d500d2085000b26030089050313180c0d05080034001d40540303404c29a00340e0207a45820a018100000b40081e92607030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 72547016 1250 72545766 72545801
    0x4020715020d0506190b03040204020d021306080a0501230d030509031f050a0504050d050306030a0c08010903083646080d1e110405040f060b0301030b04060906020a03 73
    0x280c03100c0038154200c1700b04c070100018141959a103408010003900b01c0070349031000a0702007000300e880000419038030002c1e1503582c0ba081e4032170400070041c1c02200c0701608200c0300c64490001000524800c09001079110400716440890100b491404030388a0285c4807140c7c0d010701c501e44131200f954000c21000041d0b031941da802044260f4800148234260b0742c0c2658098240d070440400588020b00c100000d50380503002400700c07644c18180e5581c0144078413055010b0304050755202c018008059200d5110b0750020814402d548485150142a1000890300714840c0f108036885140c030990154140000444021348114544401c20400c0425441c2114000c000312031032441410024100070341c03460440304c10b0300720080c94181401a0300307440080002e20f1440e02080a503090001988640317000d1411415030134000d09440f10302c4c0c00140400c0e02c040380300c0700042c01d0400a060000410b080d003640d044a801c07410a901c207131103600306480209103000c8090304640c0001108030609402da000b503640400d40d007500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 72548266 1250 72547016 72547039
    0x60f0f0b060a08010e040501021e0901030f050c0f0d1b050c070603060b0f03090312040302010f0e0a0203030d0c1206060314070305090a0210030b0a0906060e0105040e010504020715020d0506 83
    0x421016110307501c0e02c980411030010050260900b90000264020702c03441c0010702e8012001c1c26100c2200d0042142c19804100107480c9c40b107941e0500030b0001d03110040e0020300407810310711400c040e940584800d0584415012030540b140c80081e8001c0c2e14040e0091540d84c107000d141001c0104140d00400084001d44258100010b81078441c0c41002c045a448841c0d060400413010031464180d48003500614031403006000b800c0340307c0110030f891806144283c00000d0024100302000041d078820b01c15070301164220b076212070050384020007284c4c442c0601001c000794198040e4000e031780d100c1045440700442407802c1408078146806501080c50b0110850b084009992491011001d41d14111102c000c01d4001c02c1102c401410022241400c200c001c0c00d000c40c008002902240c10030103194800c44500340c82d00300c10803456070414803c1a00d100c003880c01515050500382c6841c00548107205a50040c1c1c4d000801009100d400c042803c000351402c0025991a40d401d072948001c1c01c010782d031203445820b01720701 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 72549516 1250 72548266 72548269
    0x190311040617030d0209121509190201020a12140d0e0606040c0c11220506040605060c031e0f070308060312090f01030f0b0904150e0c0d0210020109060f0f0b 69
    0x22030400b64040741c000c514154507491030402940058031003980000f440400d03221400003d0003151540711050301103003520b243c0107482d1307882c103001114002d01112020b0000310150b40e02207402c40040c1d82103c80c0069400c0c00c5082201c41c49928841940300a1000c16190800d100c0c5030080c011400c18182240d40c1c58944030200822107241c07111140c0464000c55400b000200901c441700040b00004090700b070860035032941ca070300018110200c1038032159200c081110610341403042c3c00c0600400e840e01801c00f580c0c15030340c0707075a1702c0340304440c95403c580b100544085200d0102102d01c054850341a164440c0c0c1c044c6400340c074001d030036a210b41c03083c01001e00c42c0400018076015036148902c0104110f20020f01d01c00190014010306106d48a00d6445e032040f41c040e502d4111005005a1203540b80360403504610902070100c5808642c0c44c901d542111300e100019070f960170503080342141c04851561039488081d2081e4018500c1e180020249403d0040881d105a410740c020414020300f503409009803a01ea00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 72550766 1250 72549516 72549539
    0xe0c0103050c0f0715022a070f031218060306030512030c0f0c0a02030a0f1101020d0801170f19050d091202010302160204060e01050f010302130b0c070b0d06030c0e060a141903110406 80
    0x80e0700170540c0c01c41d40030400b207a032f15032501c0c2041409041480040c541302a40042d600d04a4101c0004030707442d04420000c0240410188002c41c003407070503060450500c0c0c03400410500c01c50792590307142e800c003140e0450104802c1c0301d40b0316090f0340241258a1255546002640600c03011820303601800031004404040d400400d08010340380701a44c8200540c2e0030905034440d41c00ba003007005000c42c0b14681400340c80400400400305540a80098031940842c00d1400b20301e004821b844480400030307900c0080180ca484500c0c4410050750908016840e099418071302c000d540341d5101c000e5401414424009114030503805c000381643d60540300103c00303055480054044c0d201e1600e04884403000c13243c040006c07000300070103000303200f030b01e401034030300f0990350b00803c00f11a00a1800c42240c4c941d0746400300100b0031900740481c01021038800180b03003840d20000246502c011445889400d8036070061001301507a56540521400c402c1444840c4a0f549a0404001c01c01a0060f5a80247d14007000880c280d107940c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 72552016 1250 72550766 72550769
    0x90203240f150d1202010908030a14060d030203090108131b0303020705010c110d020d0b0a0623090f0703020c0a0b0910020c0d210f0e0c0103050c0f0715022a07 70
    0x1403c0b20b108400d684c1d6950440c2d220080c07001085540c1e400d181c00c006038480c80103501400070b980000ca1018030700c0341c83c0c10036240c024000340e100d0a55030250b00000394001c41540e41c46e10b800d003000341090340c400c9040141644500d10080c1074004440025907000c00300b0000005480c06a0300310307101c1c0340e2100015244103020600c0a4011082c0110780d8019251400350b540c081440038120006a20040d03030340714840501a136490317907a182c40c1d08090015528010500700c0030448610f401001c0c000c010302040d958107014000c03a020100400c00500c40781d000fa0121150021403508a9941039858104031440c50313402e950b19203150113070720300c06d10500d8264000c2d60304130b01e80701000d0311344a1740c076001c160b86c0c1c040404410b034080341c1134911b008001d5080c3e10a44604250071f580124104040311102410070514480d42410f05113004103000034004013009640001e210071500f01d40e80c0700142030030b0389800100ca08103040c05000041c070080840c0c82e105004859070a00f03414034004101201481c2c0c48074500d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 72553266 1250 72552016 72552019
    0x3200f010c060b03070305030708030901050f010b04062d050a080a0b030c12010f02040608090609060c04050d02010306080102130302011403150d030c06150f09140604090203240f15 79
    0x8401c00c0340701080e07440d8400000d81000400700c882640e60b031755413a0b06540020205982e120710110400c000e2000030b000701503014018400c070180d81d41c10151440c02c03074041c42c01480704020480b055050000042d181c0d00380e00f40340442a55084016010b0000c165512003412507000400d0f00000c90000c6609024200103003600802400d03030b065000091002441c500018964250349480c1100c3e038441107440100041c080d140d894186901d4021a581d1401c1c0003c4c014004075030000b400c01800d0804501620180da0040302c100740c080149000403030152449030008111075100081e020b14040c40c880455084038401c1c1c849540458440780100c4a5000851750b00c208071144035590700031072404400a0440c144603003008560b1034a0f41c3c94101c1181c4c420300890b000003085c0c5800740505030300104010020030300d00505008007030309458200c480c0d08001d09414041c6444081d0034045650503c6010711a25008221480c1000d264bd06101c610400b503a0b09001400c60501040150b40c4421900c50314140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 72554516 1250 72553266 72553277
    0x60e150c040b0903150103050705150306011e0507081b0105010b0a0e010c02060d0e0109060f0e0c090601090806090a030e0109051c0602040f08030705070501030608210d020403200f01 80
    0x5410302c2c1c40c08a910401c000765060040c004030380440c0c80ca012209000e18001e20042c011f4034188070078000030800d81d40c6902890a01402004502c0c0c0e0305c082045818076004031400448a001c0c9000e6403140140c0c0d9006040040104001944041f01270282400c032100320b000b030041d40d13a00c03002041c0c00e10600550704002441505861800d500965210b10501e201030001441c0016016030501190062084076040765111a000000d1040030301503d403056008260402000040441d4070340d41d0208009801c0c003a102050000d0a031341e000b49d03081d40c001c004040c141c03011031030415421502c0314000310b012408245074210149903035100d6600c5006450011b003d901070007440f0320241c00c6024411004a50700394082002044503004219460004c0c199240215205e01140c58014100306994011504142c03a1460070440d920340003901c00342000314000360984860410007041064810880440b0f600b07030001070004200000d2441c1c141480d105440c7d1a50011031003410414040c84000c3c13440e00288 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 72555766 1250 72554516 72554519
    0x3020102030d020f1303080703030c0503060d15020c160303080f01031a090106051504050a08060405060f070c021905010810050105030a0b0307030b040c0510030504031d0f0a03060e150c04 82
    0x2106600400d84c045405030700d207041107440c52404650301002e400449907150081409000c141c3c05000303c0d8050622401c1c501d045186c000d022032208401004041c1c040f202541103608060000e80c11520240070030400c0e2901405042400342c201422803004600058610b400079100c034400c1c1c401541600c0e485404400a4405c2c400607a0200202a0404255540e2058002042c1d5a02441070340340340e585203200c0c1c1c2c0f105d160104001300c02c83e10364488051a040401004005880802ca4071ba201710905640c2243e500e844c2411544003101c014003e4005103049111074502e40301c80c0460302180c8090761041c40c20307074455802c40c110800310710070709002c9401400459282c0b07010b50400303560107001401301d4102070340c0c7e0780310f0140402050f00c054480400d000000d00050428130008058440d240c2814000307804c09503070050030204551807510300712443e10184412a901d0b5000302d04090001403030107242d9a00e0b810118014410b03100302810320312900305906000386031303030f0304440c820404004200d0405 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 72557016 1250 72555766 72555787
    0x10908030901081b120109060501020c0d0206040302190b040305010506130902090c03130602040f15080106080c030a0902060309010c020607090509010e070509030604060b03010c0305060906040c020f0a08031e010302010203 97
    0x4840e52802d20701303030030901c0321a0605000c9100e1034000c14000f40041030484c6018006410641c1281040e8010340c2042884005601c841084500b2070b03034140c8038000300d1400e410807683c01c4200d0350002000420000703000070910005400c22405940c0c122542e501000c20760350a2000c942c882403000b03401081e40d00010706a0560400138503400001d42c4074000c0c5210066960304126405a0005600700031518420300003c105040f01ca541643c8504001140703505000010701008400cc1c103240c0341d04000000500e02c02002d8108035440c540c064051622410091a0a40648680003c0400511449000a5405109060040481c1d5028103207050300c3e404d00030301e44021a0000c000340705200c0c04000c0440a03881c100881440b8902a25000030a28504810182540e2502c00484101400d2506100d03460381d40c0020250001c0303007240c000601d901005401c0c0d00f000c0c04152030079698000c000e925403c0c8941c020085218034515180010200d814445114900fa002c3c04040c0c0181d00610050909 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 72558266 1250 72557016 72557041
    0x60904050c010c14030d1b020303100e09150a0209010e03030307090501050c0c09040f0302071a0f0706090602130302030c0402040b12070e0a06030c030b0904050c0409020409060f06030201090803090108 88
    0x22400340c00300804481c01251403070b00d584c0c0240e02c203540d80340d55880d81000410400d02004030190f87ca1014615500341009448000c0c0054005c10801003848804228849000c0103c402c03400303030011a0300b64038607048602c003000303400c10a4898041440205d03000410314000c01220310441d100e8403001c0b01c49051500445103904104a0384d2200d04c03555841901669400e40c0151082e0b118000c00c170031203141403030000e0501e2001e50091210b041c00c04460741c0d03001d070900d06943e4034840e20280c990301d40b4003030305010016200c3c200004c0e02c1e2170710005002124201c10307601103081c2c0f8001e0701110866001a0140b000324803e9210f084040365041c0454038813040201052904861320f0f02d49400e80020290008056420360740c41200030a41d125840455140c041c05030240302c400894001030145050740b110b6844249500019101d56902d00f40001103645541c03004000340c2c0c010b0400c00084140d581d56000411480c0002d0780403840b104000180d130000001114856001a0b440d60242c2c1c0324148032200307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 72559516 1250 72558266 72558287
    0x201090804061412010e0402010f0504050d02060a020a15150b0403080405150408010609020d050105120c040509010609020c01060306060e040f0b07120207061a010504080a080f0903030c06010905060904050c01 91
    0x1040f403c200450400e40e038010b94440d0180114a100c1032403424144005844070780b103c0f0920b0280401840200807598405100001c49501a2075242c2e641d008403400b241044140034000b0600c1c100425040843c03a210391001c48181d40c240c00d442c1c800c940f54040d40c05d0301e0041e8880208084800c00c41400076041c043d8200b01c54003902e5401c6820280c50714151403d64041e5005001207607408250100190280e000c2c0d00d004203801d0716026503540c3c4d0b081070309072a80c165100c0356000303c3e1030b040410300e441403d41c4003c00800d90240110b45501907940c140780623100600c02620894100200400c42440c242e120038010307a8081c00c403541c40e03507450780e950b070320b02200810032802d208003041c50410261040c00140f100e18401e0030002100c0d5154925038200c3e0400392080b504001d0300b4401403003090000207120f03405642040d015a2103024100c2c444505202d607040c0160140000300300d80b540680c002814038160741040c08240490f41d10001803103c252002c680180459010040f0a4dd840d401000a0344 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 72560766 1250 72559516 72559547
    0x61a0d021209060604060b0f07030f051b150906090d030b060f0301030f0606060f02120d0e07030819021b06030a09020405010b07030207050405060d02150903010c030b01020c01020109080406 83
    0x1401e184001c1c03506100003004a40c007603040d41180b410018285014030625019101d0f40c0d14641c1880740d8140b00340454044c00b10000d0900549100001400c0d01a00c2911030041904240d0814082205005603d40d0744a9643c0d807001d00b11500403c50240012500d11710a100704001419200c01c11030048002d1b04260781e02ea90002d4041000070a81c0501d44020340c00f03140a40c410080450041c9800d200311006035000c1020003d203a01080c0806a000c00c1600d104c00b030612640342ca43c030400e030345a4010010103814860912480714000300308003c05010700403600414400140c4c528401c542030b61941642c1d60349851300c0e2503a0072040c42038585a00138541001240702c1c005a004000e40c080b40480d0760a801c4920074210100300613041541c1003191001038141a03d003070106e0b04003100804c1000441c004000d01c5460040d02455900d95100b09507584648003d009105070800035074080c0081c62416003490041c0150400f01c0c495500500840310007641c8407080920303080c50090101d96042100c450071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 72562016 1250 72560766 72560771
    0x71709011704031403010621050705160c1d060a0f080a0201030e150702030d0c05041a0a0507060903030c030605030d080a0b03160e01050f091303030b060c0607020f10061a0d 76
    0xc9020144c10000d1400303004291030382600b8400d501020000c41044c1003c13400e1190074a030400802541c09010f072289000b260522005040301e5151050b0714034401e402040b080c242140480070101c500034002d42c09000c041e26817400c11601c2e200e020066200b40d024a0f98294400f40706c400043d40301c1c0d4064000f0384140c2c1c003aa00c0090000c500d2016903901503c41d1740041e4800308080038502024400c4103800c0b0b8050600603c0c0c01e00d400707000341c01386a40440b008881070009c0b40c881a40b502400442d031700d1a42c41241000050301ca490081c1c014103002100000281c0b03808408a803602300040d0b03042d60040c494880452030f0340c2e110301c6840074040b1070b801c3c580c142c01880003000000780680c010300b01801d203147d074122440d8140001e2280071410800b003c0c5c031402050b000d01c15031007000d40403115000d405180106007039240701c02040142c4202002d03148540700f84c40400c0150b55000c078180c3c5922041d0020341da1605c042d060701100750b50140c011841c2c2c405500c407150b424070304110000c05000c4043c0001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 72563266 1250 72562016 72562037
    0xc09040606030f050f07090212060d140d080f0711061906050a0308120705030115050c1203130b150117090a05010507020f010c0306140d02040603080309010207170901170403 76
    0x910f00101500d01040741c00b5030105040703503028641800110040c102d0a4021414178800320710800d0740c900c015104a015044c0c17401800240004000c0c502d540304100c200b00c0756200d59007a4010820901100c0c4454030055840c0032820062203641c41c103019044490040a154071381c08055800040d04100550800d0ba4446002070281c40d011007980c01940a11007103a00c035444030488130b00c118070062100302000760403c0140401d103406081e841c5441042d20308103880d02e884c0a03245150030100d000403d230b5440c012081140c0281c001d221200d620740b01d07020b80b00103920380c58007031050b9900d62500301d1f0103d044046610b520081485943d584050690b0031981c8400d110f844003403c69a081c1d5950006800c07441101074120402d0143c601c00101c070b882c2c20408145010b15015020700d030114007a106000402001040d507545812100c084c0d80c01c0b01010307075a8249403203054003d42c01350038222529002e20f01450b000640b0031064175442807040c3c4031040c0310b0000c0a07240460080060044042c448056030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 72564516 1250 72563266 72563273
    0x1051b070b091201050708011a0f040f09150302060301051201020d0e0109030f02070513050601030905250b070206040b0f0c01061d0f04030f08060d06140604110403050c0904060603 79
    0x258401010304603071040d03490702640c0900c00b4049440d1407440380d0360b04060038805031682c00910681122280200e645801c07020407496a070b2442071200b84840b0300f00204002c26811010b04000301207d1118030208141305030b428040d4002d00039440080e47c044400d0004100368106281c045280c5100b1800042c0391080440c0e40340100e0320b100b83d0b1440380340c0d920101d40d8101900041c030101a0310240c0000d01043d07280800080d075032050044074070000c9450740003040d00c1d41d000e0740000d00102c1e4080240c94680c101840c1a0240b40303503247e403182e80029a5500010a034040000b210032071a000350805182c24201200500c65501804c90580041d034208180d803031900b401c0c400c6070098000d040c40910f0f10707022462184401e4002900c07011030503010605000010b900400c0d0443d001c44a814400019a1800d000440074004034102900540c00d110014060361460601c151155508403000c20480c560a4841e0f4824003903030100424a50101e100e00640d40380c502c14a9910600c00c2001042481d200d69 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 72565766 1250 72564516 72564523
    0x20c13150302041826390d090b07020d0210020712060b0102010c030b010e010c0302071d0603060c0c070b090f0d0803071710290c0604110d0c0501051b 66
    0x1030031000d4260304e140b240030030070924009501c01c56410101e6165901c09846074440d0900ca0546044684809a80100c04045910500d181e508048000b120080c41108681940707070702c0050441d50010f0710b58180807501501d00c1d81641c0080740c010b00f240c00400c540b0760034400d803460302207101000d41c1b281043c0060356001184a0030344042c411403010131040b15070000a0300750f900c41c000303d205150420740d4100103a68001ea0003208840b09181c41d8052444a0409030f0030f1a405030040035000042e9800c40c80c150580c1e11001d8014103040c0c084850f10b0f980c0806083d0740b0702940e201e2034080c0d007064074104040e48618015000c400700080c0903c0401c964000000c000102c001011a050f00d4080100000b180d04825881010b1035000d4080145240441c0c8000b205840c0c2c0c007844803030f5510000090410b030320f0b0b030b1100e0711450780d45560544d40713072381c42d00103d50384890441d02100c2440d0784000b41c20107801d00b0418151500e5020b1301d400b200c10304203401510b0390341084220f90350b02d4010764941d11202c402003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 72567016 1250 72565766 72565781
    0x180f050c1c0605070804080f1c0f020414060a020331140f01230a120608070e100f15032a030b0303030103021305060612090606010f020c1315030204 65
    0x4040c41d0088031503403400c98140d9000600030003d000945041002003960342c802c980c0513400720602c0a40e9244083d540340b054551500c5402580c1d80b500d444150100c1c0f880d402401500d40d1003111540c07641c8100104465841031440e00d0006070018042850320340340b51254176110b0414944009040e8022004c1801045040d500c641c030500e03001c0c1c0120650382414880e44c1c150800a1816800d051f101035155242020054101e62540d4030014180d24428880ca00101d410040240c0500244d607131141d20f10303520b0038180107048441c003105022400720140d010b10300c4100d48070520740001d002e01d400c49141d9400c040038501800d060701c41038043c0c20b1a81d0b05a501c00c160440868041d460603551130b0003005c4410002040380207030700c20001400588ea0b0b400460300400003c02c1d02040aa03250030100340103010361646070755080562028400c400c000851414071589007a680e80e015001c41d014100e0307840d0a0147d071349411405c407510383d2841c00e000c2d40107100f1240410881510165803980410211840c0c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 72568266 1250 72567016 72567049
    0x9040905250303080702030a0f0f0e090f07030c020307031b080d09061406013002040e0109022203030c0f0516090902040c03050405030a08130b010e0601030c0201180f050c 75
    0x40c0c4009100f0180c04c00f02e56900580d2910040d030500d12104070291900400c040c0e0501401305110303c0c1c0044038803c10010380d054601408000007810720034071440c602c040a44508012030304049084c2c0d2058400401c1d07480d4543c15503166500b0b0122030400c054100b010701001d8401c01e1042001440001d1540100c5c1001c91140e440040c0d5100947c1280010000142c4410704025581c41c1c29002071389030701c00c45c41e051381d0003254070004d003207001000710700910845e4400b8008a030710324000240080c0a60103040021910102c0f400c5c80d41c40e0500d4050002e107140001404200003000090124102c43c902011151054080314015540280d40707010b0006030760311001c003040c1c07500d008408505041c041c0e40c0c0b0014881c101407040303003080c0d40c515440e802060045400c01c8680800140d80c803200756284c14110360880365514076540c4030848030b91001001c42c0c12901290420f4008060300d44140301d068030003d20040303080792404440d03880f101120030072201501e4910030750741d401416948454204000c10031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 72569516 1250 72568266 72568333
    0x91302030724020607090b040e0c0405030a05030a021b0d0b04030e03071403070503060705041a0d05010f1d04050d030c05040816030515060d08160c0905090106120809040905 76
    0x560301e02c02031401000a041800308802030008014401014003520250b404800c100d44060760303416a20682d90246a002c180d16101da07544002c14171070044000e24110400f80e00f0765031a2504000043d4101c5c1c007480090f070304284d801d5030301e00c042040c1c105a260007501c20714040c0000300d5440002894030710707036800600e44090000d1054045d840c0130400e0200809040c4c010344445d1404001c050514081c038450000803000c240845910056603070116013034100607032410000d950f101c40c4160741251250040a640c0004e0a0180d214a140d880d090761199074003400034591280e9400c407c40c0942121030782c41c0180102400045031003001809a6129401c03190704420b406d51841c10034900d004048800080300c0400d0100703000c07281d1204004100c1d00d07500941e190341e4071044500a1300b5820f8000d0006000110000808101c143c0c2c0d40c0c00080c0208010310080c00f0b556101d03000710f4104607080c1c000a0400c0000c00108010b418150080041a405103041d242840004a0039000b50207012005152404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 72570766 1250 72569516 72569579
    0x210050f0603010617060f10030b07081618090b0111070e09010c09030b070503040f0506070c0606060908031c060807120606061707121e090605150913020307 69
    0x2001d101e420000c10303102ea000d8006022110485d42c0700c0d04050480c0d050003503540001019140010940c00c02550700c25540c3c40a4170305881c004100300b0090390405c2c1440da078442803411080c42188480c426003c1c50380240812740c6404e0001e801050841c14071070502c40f6082c489141c520703051040400601c14195015118507282c54030900b1220a80d4036403080c000f8454090020403a0051000e07408801c40c00c140380d4940701d07410040c03241c110b0f23020000c01d18450a41000304d17036507112018055640c072a04080c422142c50f03030b00645061400c2e01450210381e2061104034803024628804503501203180400051070340d208c4000f541040201d0f042480b55010046041e0b0030803420f4801c0c440107041c9450710b2255403d01c60507400c840301c0d01908844c00c0201140030b58001c01c00c075074481d1600180000090f10f04070315101606020304001202a030301203103818000707462000c0150381940740038030040003080d10f0741e038070084c5034625a9050700c00e0381c06202d0440080350319102001c1d2000c1c209510501e254684 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 72572016 1250 72570766 72570769
    0xc11070b030615040e070c0305090406060309050601090509100b0f0301090f0b0a0203040305030f0a0b090138070201050a090b0d0207050f070e0a0b0d080a180f05030d030506010210050f06 82
    0x14500c3c0710942c0d44802c0208001c0094820b01a4200c3e0060b10518011641c40c4550030110703420300445a02c1c65020303140500c0090040e03010344c41700c0d6505114006a40c1143e1740c5403074180c01c40b04d040301d070002d881d080120015107003011648429803e500050468001080230004242122440e50301110f074040c0ca400707000b0520200c00079003a80903915460551039454290b4006186000c00750041e0150426071002c110010301c1500044041003015000030070940c0d58424194020070130201c0c1c004e80b4454406011071b6403488003003d11102d4070917410b13907151443c0c5a00441e8141d105c40c060904000104002041d5100d0110042c148084070050250300c65025080080c208440e03108022542d6005005c10040100c1000c0030680c42058440005455011400450403100c0312100c002d0500b0000910307148070942054541d03c00c441c810320f0800d209501d038040c1c88021140e074010145d160b07104082d40110725205ea08090b6100006105440d41180e1032140c90054642c10755900040c8030300b00c800c21405 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 72573266 1250 72572016 72572029
    0x80c030301180b0f011b050d0302030115030e071511010e0706030f0b0109090b0a050904050607110607020a0602071109070c0203010c090b09090a1107050307050105010b0a120c11070b0306 82
    0xc4020b441c40070030254545400103642c516132040300a040c80100c03003040c18120403044400000640240944500005000f402002035009025105c3d1060f404104052094460301c00c80380350024440040400c1c0741014200341020505010400812400f0100f16042c00028010004801482d0740180241402d110000e002d507803010103007840041c81c048000050342e0b4007050a800b1240144000202585150040b410031075081d0070641d00080c07040240400c0040001c0c400d407040d000355881440700c00e03601451544070751083c2c1c7c88000580c810b0303102a011650590003409481d01c24210186150807640214213013070b00c101c5410022506120359481582000c0c0256451b04585260000109003403680e84042e90080f0703068680940030380b00001310420140d910003075004990560700758885a0030300d0a15620743c440e100031601d95003040700000b101e54860007601c11000031511019800390004031040b00401560481500b04400180c96250722407081c003080340501480030960790b6910300b00050044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 72574516 1250 72573266 72573299
    0x4031511121009022706210f100b030403080702210c060f190f02040b16050d03050f0705030912131a0406020c1203040e0c0a0f0806010504050409050307080c030301 72
    0x44a07004000c034544000402545400000c0c0b8131170750b400c3c1da40001e80813400c0ca014480d480482241e141c46440444110160203510503a0b40c00302d00c170115a546401c88441d0714951181c2c0400790b00600129001038020440e06074400c0b2603104030342c0600100000842c1c04c0380024400b40c1220f01c0041d0b44601d00c8003e2001700d40c4000041203913491818003c00c010b280d4040f0101c501020f9950b81026000d070704044c2c04440c000c0002507000d94403018148408801c021000c030040310141f0420300c45140c02030003070047d180f068100108443e51076840c5541656581c0c40104508254001e03c100b82ca6031210718009008610010072900007114100b020a0400900898001c400514180020007449500081c0700101840c269130300043c808d445135200389103020710f820505201c41e9036010001d4529030304000d4590100550fa41d0841001ca4400544034904113965aa000400809c4240081c1c200340d0016000340e88100c1c200c1340341440c2516142c5494210494030301e0f26803c004010080c41842110005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 72575766 1250 72574516 72574529
    0xc06060904030f0e0607120908160e0402131812110a05061305030c0708100506010e180c07060218030c120604030f0504030f060902010221040315111210 67
    0x105181495140a00207401015000c010040000c200408a441c5c61040e074036980da112041c010342d03819100c40549944d070640502c0d0710500c2045074000c040021100f1400c11190044101410342c0c440341c00b40a40d900d00c41900d0358070b00f84c41c0d40c2002c900340c0010f500c4007080c41c02860903500e074030f400307001c010041c4810b105020920f42c404003a40c40820404624103810106501b1055211050b51a0803415401024514600c5010b91b07540002d289001180c42001710000610400507a43d80c40019640640400301d50f5030044007040c01200d8590302e00c403500d50412a00303041c403418a6111340cae420059a00c880690301c0a41c0441e980703d41e0b01e09041140c2040382004232484070601581b03c20180e5a8a0000d102601f0054501c03180305485004104450145422040010000b502420311002800aa0108074010701c2504110b00c000208480014051107000500518180c51919200c0d0710094180525280b0380d0b46013507191002900b04e00800401007501c0c11441d603890000344020756000b10703034030a0703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 72577016 1250 72575766 72575779
    0x13030b06060405031914070e090114090d0c020103020408010f06030209010501050c03030a05040c030b0a0207050d0305070203040603020304110a08151303050306100c050106060314010b190518060706020c0606 91
    0x140720f2a5008180e01a20058040f01e0340c031080c1c1d8508188000402d00009074072180240c500100b001c642c0110094841c51001000744800040c240911092040c1101c92101e107401141002d19094421000c07402101d005140c0503003440d803140c0e00c2c41d00710380c030b81584211031565502080003141448051180140000d003401414042140c1050707480e8840141074440960369a8000703010007007103120680107150403134200551403400380c15810096120301016901031040b825481c0f40700d0f210b4040c031407045049501550138940341103070540182d0400780c0112064418102950090b446202066008205100062072048000545040002009001070f144140400b000402103074002c0d0469400c081d05440d0382c100981d035041c08440e95150707802d0003080c5500700003001881c194550070200400380b6940181ca40d0b070741d981f1091029031003641d040c1c000e4400c2c1e2002d4200c902d801031340a03008000100c9091084c100fa4100042c2c415840501e080340c2c55075022500646c040d40420030154040810f0390513 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 72578266 1250 72577016 72577019
    0x60e010f1403071d0d050a0201080c0403080f07050c09040201120903030e0307050106051e1c030201090b040821010515030c040f080d091d0609180708060105030d0504031101050306011413030b060604 87
    0x4a071f032140d902d150041c0c14400c0c801c000c11891118241200c0003140c02ca400d0a443c0e2141116094040e8002c00d000d4444c0d1046051040c401d02d40380c40020300441e03050311040382040c114103258000e44914a01030702031580d40c60300300d5000e140500050085c64803c00c00000c86a05100400402c049002440136030200c1c280b805120075219540324001d03400200000a011003200d20342203014100102d4002c0c581d400c480144020001c20501a0000074446120403040c0003420681c4129690700740b1405a2004102801000613070003c0b0056400121002034285016110080c1ca26804d64641c0005819481003038032a20082c0e1013080324014019842090002e00c603514031003090080086c02c1c080c0300e49a904080740b02d06400f032840314aa803425209450040740d0f1150b0058503845e0900c2524002d01070b003c403600129100e1310458007541d50000e40c100c5003c20b044011111608010403881c14040301006581d07003450940c0143c03503c44030403c08900000c0c1180380c8500756035409096030b405100e05110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 72579516 1250 72578266 72578273
    0xa06060329090d0c020f1c0b0601020d0c150e0d05030106030f020f0901120b041107050c010201050f04060e0a14030901020111180d1b060801140a060e010f1403071d0d 73
    0x84100800b002484c29400340d022500000e400d41c0c080b59040e030b42c407c6041030050002c244000424003101e00880100032242d87c0e40d001a612500660b403c0d07400141e1040c4203a00103800c1d541e1030f0614040304140019003640100e01507180046204046003c00c0c0d0210040155590500038040342d18a0168158141404642c1d40c074101d0040c0d5038030702d0506c5040b964a107070360b41c4141c0c0710b500c0c1500000c2051107040084414264141e0242006a4103401580740701d02081d401406103500a0380340c01010f50721640c4e580c0f01c1800070708203549001800d01980b10030001140844112580c0d840355a4091a95092614000b90841c1d2086000703290f18001404209240310850b414484207250a440305d500b00c501030300e40b91804545412400f5400b000012020440784d034040307061390685008254400b99165000300300916200d240c8515000980f6100d00e92285520443c0c2880410041d81003400100802c00d0600d111500212403d80000d40e090740d02840307640e61742c050700071008001d66142621303074420b44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 72580766 1250 72579516 72579523
    0x6080712030507111314060402070c030f0602041a03010608160503070f0e2110060308040909021201091227060e0102070e01031a06190303030e0a0606032909 69
    0x2080078090000c007180703050500c0107080d8402c600440003002041031168404500c001002450381d4902d0f07002d0380000154007800d081c400c03942015000520700041900d55625161040c1c0452011240e2940a1000003190005480110800c2040204840d107960504070010703c03100005140036406d00b405c7e2071081080707800804803030f0040001e24100b55104881502518080c80d0b1804084d0083c28168201c80c4050b4902101d0416081440c241c842040c0803604910039034555000250088104010801c01710041b80c1c400d1200a2000d406400f520031403070005402c46540c0d070010303642c1000d40c070045101d0580c0142c82e5685c6103c2e0b0b800b9030f4801448100103d0680304a8000c50043c40007144d400b6000d07a00820441004100e0641540b0341c030740e101e1421170940c000141113030802074642030100d41d6914080c20000f0240260000303507500a899600d0440c0a0424a001c0c0c1c04180605c2c0d0020022665501540029501440c040c6030f008a14400021070f02e840c00c1c18110411912500340043e01c1d1010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 72582016 1250 72580766 72580799
    0x403050307090806010f17060910020307090b070606090606050a0e09040311030c030a0306170a0f0c15080f06030102090d11010327020111010510090e070306020f070501060807 77
    0x5140454807559201801d40d002001500107a107140718607000080c2040d100000741c019114031650441003c031003203000668440c01070340c4408003504003126a50b824400c9a018551144062500d626400c1c2d0722650390500303501600040c1d801ca0b40380c003000d001201240c0203800c002c04082c030f0070902d0301100d10001402e061076a480284582c10641c041810b242c0308100c41400301c081c2c001500e82c2e80380162006580d07a030105000380c000c40c0c105480003c5d040740108002400c0f016141c003810050b02e9960b246070224803203190445003c3ca0103440881c5500c04c0500b0144100310b15250040a820192125405070500030320480c0320f40c8c010481c000c6583c44103516401c0d4107070300c001800e20307180c0d5000043c0c0180c03182441201501c000c003800c0e20018820041e82c1751916000780c9a426800000120090a98a0032114141000341c080c10401c0501e41a03400101d000c0102404d44642c03d44a940700f40507a80000c1c0034803070608020481c0024407600384143c0004240311001030100314134000c1ea040890307444 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 72583266 1250 72582016 72582023
    0x70206030c0702060a08010312050403020d0b07020709060602070e010e1608090c0603070e091003030f050c010e0d020102070b16120c020c0405011503150b09191505030f06011704 78
    0x32021846501d40c141c140c604440e8003c01d496110301d0048402400c01c030003440203541c3c000404a0805695000314106d030141e0b6006014000503424035141c0c400110400340000c0300318418200009226852032080502411640e405000c1691900aa9410303820060300040751542241c01800504401d40001143d8100030381002c0340c0300d0341c81015507420241d01c0c10b40f140e0024400010426101e9000702c110404c5d440031038401e100c03a20348840c404144943d6000040118103d1400080c100340210040d000d00340a080000c100701210400c410300b4102c4524611003d41e402140041c104140096102e074001d10001c07500301900d00300e410042a01b2403400d031b505100d5030b403010201da45138424070000c0310b0342c0700140060085507918000342e0a00d00c542400040084c3c907001c0980c8861603950707a4101201d01010485040030140c00800c02d04038224602480442201c900006070141a50406900742003030340c403195141d01d000c649081c40001700034030312410081a0628a482000030380d00701d0783c01c10741 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 72584516 1250 72583266 72583279
    0x21b0a141b13050417030921070f17070807050c0405060607050d0309231b01090303080411010203070b0a05150d200f040204170d020c0a060305150a091b02120702 71
    0x2c1390704100458001000b0701d80713201c02000003000b09082e40002c0e450403844100c404c20840c2141400404a28083e05a00404050900320000c011428900c00729119083c0c1000c0140362007107035038810b101d503402007008445903006000800428134192140ba13a00900c01d5070160300c0c03c42c182c0d03112500e40285505400034182d581c1074210901000c00084030068034282000d04804641d0400c1564800e50081c1c050f200109030f0985100740c0d40300311440000ca0390300d030b12440700607111a500e6940c0800981441c90451005205c00300200340240e84060040b80034440000710390500d040c5410f000402403094501490320500a080041d81e14644d603100407010018961494200200089884140225031984140040782c0884d082c0403005000b2220070340c0c281140c4211500d2101a61154a00c040c1c0680c40f0007180410030005010f50007241d0300c00403103860768005210b02c50000d000d4510326000788089507554580903140c0500b0080c650071054250008000d0038080e0380e140c141c10302c6600d03802405090b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 72585766 1250 72584516 72584521
    0xb0a06090315090206070f060b010e03070303030f0905060103032a031d040905030c031309060807050907030b15092103030106110c0603070809070f0303020c04021b0a141b1305 77
    0x120300741d03c0103580560080c0001d903035110a0814140d10a0304036401d4030514501200c204182d030040010300707089600038001c2c07c40311785140c9094000b40010340b01059503580380c00b503100000b034003402854080c0d84603803280300c600c480d02030a5500301c0703040c0d05000311085615115140402d401c0030301103e24100310b001c3d81c50b2403042100030602420f0034410041c10703444003207a0b1510100c40800501070b4003404241c4080707010f07610000304041d0785071485008007507044244144100e007460640983e20100c00d003400b05a0410f01d2010400d040b203030750369008203000007095001080c0b80c4082c0c0110484003030321042d441c80b1480840981c8900c0103210b6a42032160300003020410f00418403c1d800c3c0920000c01c259120701d04180c019042940032101200a400f400c0c1d800306221412101e0705068035059802810503000040a120003036000862985c0c0050003100d01d004403c40810003281c00d680714150b003100c03540c0240c0d85145401000b82e505402081c080040100310346802102c481c0d2010b1b18040403a854 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 72587016 1250 72585766 72585803
    0x201050f13050a020307090501060f03090803040206030606040e04060b0f120705090618100503120c0c0616020306070c03080a09030806061e0403030201060e010e0c07020f01090918060b0a060903 85
    0x3e00200c0004d40500030604001503d6580741c0c0001c1c100c0380340392034003492401c0c0c5020032022076000000041610000344046405410007138040c55000f000908090315040d00d40003055203c00c42210f040b40c0300340d01d400800c0102d0030b0104c0302100502042d20050084141d403814240c80c1d080314003441d8044c1000c0d90000701c03580e44004001e0807050405c2001042401c00400e007107000c103c503000340307400b038801c51007060181540c0f4000c903100e0b0210140a8202c9903141d10030000a1740c010010008124660008000541da00f4844140901d9543d21001c004c0400c0b0710b03001d0040c41006100c0100c40307150261171404030750404500c0798014000c4410719540c42091115003002c0740500740400042c2d178041000303c10035405500c00d20541d50b00c2d03180c40f4050703a81e40d105412002c104461440b41c50328140100801400e00b6121b44010500505100c103c094680750114129014403030a003004400f60310740e40c8140441c4d48210250502c0c140c4229201605000c0082d0650794244001808003801c445500303201c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 72588266 1250 72587016 72587023
    0x10b090d02130612051c090902030a020909010b0909060901050d0602090303070c030821190b0409080a120608010b2b15141510050a050412050d020d0201050f1305 71
    0x7040b00b41c0100300805038890000c090784a40e450400c03503081c4514500c0c1d169412000b0300700c1c241005142c0e10540a1400c00c212030303002c0e40001e0083c5503d15000d0001c500700755919a1954080c20041340c081d61035001e503201300b05075207501500305070289a4040040c0325503103072000d0f000c102603008030026035103140080209203580300d01940a00700207008400401003002c41d03001000c90300b61410310504111407200590b8402d000640700495841c9034901c017411009255040b6210301c51004000280011542e242c44182d540042d11000015051099401780401d1501c180c4c000b40c510b9130020004c0039404c1c0d0115003400540c82603071b886091607510198110300244043d0112a40c0311208030b03a00071581312104080c001d5940319030000c0e092440043c0c60740a940d000c0110004c0020300c0c4030440a280d01050707946511035118403040100c00c003c0480d030714540c445102180c1c1d01c10001400c0d0317001c415030000d040c07017642c60341802164180021300402c80074501400303420000c2100300310b080c003240f40343c082d00d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 72589516 1250 72588266 72588289
    0x402250506010501021c0e0904062009120115030605060307080102210114030616090504090f02030c0a12060c0e09330607081b03071209090203010b090d02 68
    0x884285042000410a022511504807002a004c407500f00c0902104902190410302c12400080c6201a54000344d103416030140e034000c1d001c1c1000007145d011401c010601141404000e40e65110b0018110b409820b290002d50702c46c1d0000002040042d0a900045182c0039080c4809445983c81e2404944156024800030b4020109007008541e210a4240300311226203044100c03120045e112000000e05803031034204000c0d80c4034010050302c0300f0340d220401d8556405004250108121080c2380100d500e07107880c8100a000303409141e2605243c633048c030402d441e240340d0b9691340f0702400111004000d04280e241d941744140d43e000001007683c0341d1001e412030728201103660940c0d0041c2c0c45018460100e170200152803a0018a5a00561540302e101d9100144920f0000140d08110208026000b085000d0042c21850182d91031214007098010741561461f0010710040d0342c4c2c7d80e00421030b959580c0e00320034008010804d8610950841d031502e0b2014915016000c203c034000c46003901c0900856a540c0740006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 72590766 1250 72589516 72589567
    0x1e1306020f0c0c04060f0e0f040311150a0501061829030112051e030d022d030106030501080a0309060305040611030a0608071e03031803200306070c0b060402 69
    0x1501c03440e42d144550341d00c1c000d00003428042c515100d4040350980c0200388200684051b0303401c20020307880c0c511800303005000c01030041d4104040309400844030b0304144042c0080d2111030f2151101401e24145100403074074107a00c070f4070510205440002460b4070300008a02252500d10000700320106036503401c501c110341d19001e51151030303001001240b00001d004da610005406542154004500001c0e9011000102200b140495109002440c6007222540080200d24550701c086481d401030081010302d50223040c000107451006c04401070011036450b220740341c0180700110040c1b0340c0146a4030007901602c1036001d40300c10580c07907600040038007001703400a10034035600c1b2506661341d2a1003000038004010a0050340503a000d030a400080e00084140c2e408150f24000c11025010741c5580c0d8142c803500804110b80340c180e640d0340310010118502c01c10840340c0080a500b001550540b0408250030540000c104506005112144c0c001241501880560210083c0c400580d241e0240c1000c816148046c0b884d003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 72592016 1250 72590766 72590797
    0x608091f0207050f06060105250b01060302070510050106080a05091905030405100503010b0922050a0c090b0316050c07050604080f0607110c0f0d0819081e130602 71
    0x44032651036005010352406442500e801c01610301e43c80c1d40302d44098a090340041d4060000c2d40d03242c224001d2101c903048200c0b03101002030181d0390310200c02420036030000000c40c1d408200c24061045c1400710070a02030454404220642c1460409841c0d080080c064001c3c1540e9100040d003813220400400c5c914052040100980248500c3c200750b90754006d0242c28025107151414501c15801a801e803070680f4140700c51a4100004030013800201c1c0c4105000444011181c40c80465400c41032080c0c03402101420400306032074050f150080c100b40c00302d912003a0303400b40401c2000072590000c1c0700700004400d40d203011559044100d50711807410116412241e4001c1d000100050104000110002103040c4d0700140ca009a81d0540c1c06c0e43d1008603540c100080d84c200c16680062454a89181d41d480c8800403e0038080c0c00e219180c0241c00c0c2c00141100c003c45500b0401418541d0f00030500d20b5110310220a4604910310b803d0a05440701d50190003038251101d8040e4907010000b050301540c001c41c1040059 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 72593266 1250 72592016 72592063
    0x30f0b0a180506011818060908190c020f0906100806031c11010b03030a0909020903100e03031503010e0309010e0a080a08190c02010801050f010306091109130b0307060809 75
    0x700d4a0f14800c1c401d240040f203030741100380c180ca8503500500d00c040c2ca0f2089172201c6400681c84241c00340c42224400c40e0350350810005900b600c159003403030310608001035503000640d415520601140640c071035817103803203000c1d124100240d5a850700102c214020951800c520b80d03445420119103401c40c0300c410341f43c609030200c60341c5c8241940b044c0d0002c00000048024480603580505141c0c892149050000005080400900c699000c0e0f070010040120301070121207810001d1010300040300d084900e5072026400000510007071f03100c2180d40800090f0110000c0160352030403000030303079207204074015a17050201240d0403060b6a03407150741d441c00074080035080e01c07100345507890090415801b200d00b00c00000d4140201c84045d80c4209041810340740d041c0c5918035542d007800b0422541d4080008458100364607040003081c0c10956004203205079031000881a2a0390124040281a041030a10507c0840c0b804c41d07846966540005c00780200c824a003031007030243c0c50f030065580c109400410452110301c0c1c81280c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 72594516 1250 72593266 72593273
    0x20105161b060c11150c04030b0709050a03030e0102060f0c0313060e0a03020a03091203120b030c0315060102010605040209060409020a1202070b040c0605070309051201140f01050f0604030f0b0a18 86
    0x6582143c10303644c4040ea0003440002903190040b407029500381112400510040c80001c0c035661160b40c00c8401814104101940e81c800540c141d051a00110b0000302107006c0d140003940c041040603088000035000040c175141c0750b6034921040c000141042100c042110b045014083d080d8400c42407507088809031009041c4509002c1d41d1044140011030001346034450001f1064562000e81044030b5040e41c81c91280071402c00c12101428400c0081641402034042503851541c040110352080c0c04030b099079455a2801100184c2181c000e0381c840c50086004002c00501503480303101311070903a01c000c1da0040c2c9a240c07054045444005140310856a02d01c001146014052010003035482141320f0001ca029030f640356041220a0700a2440040100f01524014030080c2f0740f00c8510340c1d103100d00300000100103040b2007080f8100003044d2110900209014014011414409103c00b0400015034411b490a0703d1940c501000101c0e81d00c01800c10081d000c0450711041858001000c0e0307195101d00b840c060269400e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 72595766 1250 72594516 72594527
    0x121603111b06070903030203032a0c01091506030201020304090f0914030306040f0b0906010807141305030c0a180b010504030204020301080c2b11060708160c06020105161b060c 77
    0x9a0380c1440d1040e8000a032650b4841d590880175281c1c16806142151102100012820140f03080c0403031550303038442580980c0303141502070200100700100100303030748040341001040200700388a0010302078140381c028005030346c0000c11a8110703019a0340010308807403104601001030000040040c001c0c0a000043c2100b5100080a14010788046038200050415207854204565000708a903801107580000110b2540c011106964800118103040700f07802000342e10182c1962106581c1825101c00c40b42c140440d080402140c0c1c000c000958a0441160404105a200c4411900c11074501034580c0141082640728205441c015039000e44199282d584820100d032b1034205140010303019400821201c1c442890604000c2c1c1202c0541c0320915001241c0e40b20305c1e10400841c48401d401070001c003d0b4a00140e01100101805c0045605001211803280341c001c40c603d00c42d42c4041c00310ba041409212600c0d0009408030040748103420074007056541c460391032071b8040c2c5410000d88541d15103c0040e006c1c5030081d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 72597016 1250 72595766 72595807
    0x70b1b030a111b1e0a05220605060408060c0a02070801091a060103090b011a070b010602010617010e0c010f020a050a060203061903080a030905030d090807150212160311 74
    0x80e10350301240720501940b00240301c2182507000300303800c5203018051354400c0d00c40940d0402030300888206449401007080300a501105c07180740300e00c0544e210320941e045d201d202c000e40f000720f520616086c90042d0203a80d44401808082c091103000078400542402002164010800c0307074002c1c4014611418030486c40003118203821814100b04e40010400e601c2803003065a4140d012151031542e90078042404010000c034459045180b4040010700003096910a01d0340c007c0c100c0368000700c0d000342442030400f1501c545202d6258580e051010010030b2510105d07031a003140c1020301e0504035032400010101d1400d019440c0240840c001e00105030144111070300158131907201030700d00d076a40e121480340501503104144030141200d84240444018644207401108503107008004480c200794621030090215601c0c41e8044898050008403001000b40c450f031124003c03103a4010841c1041e03d959035481e00d5080c0202851484154040800b21f810700a03802450007010140c80540c0300c41807a03089603203840f0355 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 72598266 1250 72597016 72597047
    0xe090d030f0203131509060921050313020907120507121b0c300207060e09070e1201060f0b0c010e01020715090501111c1a03070b1b030a 60
    0x2009525207200c01c6900032a03014188124816180e0b01c03041c3c540c020203405400c18102251303118a00b050102d5001c0c010841014007804501c0200303010000389140d15010001002c041c40001d0040002407034071107420441d15501510301011940c2e5582085509040c0d54281e6000b1034900030500007556448602c014142ca082d207400c118020300102c244094807109080c10000640310760500c00000c0d21800704550700c0c580d08481031100101040c010404003d1641803500690010300104a0140d00c512662803483c001d444200d03050400c120010404408200b00740d024118500302800c1d0724009600c01720040100f00a202e10051b1203503400e106907401700c24070003c1982000c14101c0e40600c184211040240e1141c0c44040119141440750045c0c41c4140d010740300380d5a1648500c42203580a0f00401e461100030103800f8502c18240c404004031038448410900680c040504c86059880025680c1c040c0ca8003008400d46440820401c01200d86441e41034403614000070603c04460354210030100d00c4d0700d10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 72599516 1250 72598266 72598271
    0x9070c020301110f1e0d06151418010804172109030f2208060c1c06030b0604090f0c1203020706050309030702010e1201050c0d0f090213150e090d03 65
    0x303200a1050544c041c030300440032003c0040041c0f01022120200741c040000d40305002904000c0102e213280100c036210780c03261b0050860301082c8001d42d540007020b03002005990210340d0401d0010020610b1600f011095103040c4003200001c03c0134800c5a040b0007007880c1052003155500c105409804000011400c8820181540c5e000803c0d100907010054540000c2d1000005081000c2c0800305420b13841c0d44407180e01c2e05803140101081039001030000c5407040240684060fa51189607040b04036041c0341c052208040303403030071005100207003551100c2038224500301c0c0c02003050034542c2401303010010079040c02004141036410008101040fa646801194069000d682c203555a405040d41d0511040b80d0201690700200000001580240a0034141050141c00030705071440f031590305401c6807010384101c00c03185000306503415060742c1409034402c00c1c82403a0090200313400300c0e40441c0051058001040b006605c43d49002c0b28402080303894001403044180500041c2000e0760410341300d02602a00c00002070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 72600766 1250 72599516 72599531
    0x5030912070503070506120403230c010b0f0d02090106030f0e160602010e030a0c080a111005041103070e0a0b0d0b0703020d0614010c0210050f0c0304050f0102150c07020f09070c020301 81
    0x30700002602c404110a50380c502c4240d50300e65045495440d1001c610070002e9880d85090322b01d0101102030086441032400008201540208116500302980c0c02d42d88103c0c1040340704001621000b1195045480350b00300824850640c3c1c08220140c036205052131403900c40c4001d404008100480301e802183e8450b00200000303c104200941ca81c070230021100081fa1601110070000b6188c0c1c0020700e0000c183d403a08006000482078800c0c20100607a800944c06d0b521281400709010905840034001d05080340101007207860b0011319030b141903004000e400c0c0c265071607142450b81d44540720b070f5002c1640d01200c2c1884034504208003074000d401041d5807100072480c000011840760354041b000d504e0a10142c4a44c0c244031065402c0001c84000e650001007009000d00c00c0003108034425028240040034100a151658280014030548001070280c1504560229840220091405225070380000018500550350841d500110320f584111211054001d4061810090025800940c1c585414400c0f4020700c80c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 72602016 1250 72600766 72600769
    0xc070e0f04080412050a0204020c06040c0f15030e1e030d0b0a050f04091506060f03230c0a110706030b0f0f031b0d0203030f03010e010f03050a030507050309120705030705 75
    0x6240840d00181036140810091100c48131108101c1601c0d4801c0044400442c3c0540c0410140d030814010002e0607807149051200304000e0110314800380510790042c0b13040034545107110300084401d5000206041d91120300b14051401801640c44040c500d980d0865851411003003903503258072107a034181080380b9002d02000c5924010300050212100108184116807614080000400d400d140481c0c0100e4032400804414819006580050485449443c02d4084a240240603100c900902e0141c0b05416040d0000f008501c01c8041d0700150351451854079000d00c03160a40700c08030038101c03800503132041190000301658960401d50080d07000b60b900700720300c6500109000e1100c00c000d20341603140c0c00018400c2d0a54114184010380313010000c00c1d8030009900d540209045034041a441e420f4810004014440441d90000b814010030a00a074001d100703203151038241e16002000001801c1010005803502801b8081003a0b40c5011310040c002400300101214082e03070b4101030301c14140070780a003c0000030103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 72603266 1250 72602016 72602041
    0x80108010e0d0f0302120a020c010b04020309070608060312040e0a062312011e020a091703091302040e100311040b0117090f030a0815060703050d0b040204050301020c070e 75
    0x480c44006105006503101d0558804070360300c00c800f04066003480059003985034010748501a104003071005a84c2d242c9a150f207400c0d01c54003000d0b14041c1e401041404400c040010b00d4004980c00307860400000c0d114000042c0c185100c9000340c081c000744c08a400301c0c440b0151b440450044504120401080e80e89511a51400803441b80c501500c8030398001da00701904201c2a01d510040d8130200015015142c1010b545040d4580841201d6450703004c80c120540682104290010381080d03080140302c0c421080c1c5040d070341e100d60781109000c3c203006000c0d1185444070303806950182002e20b0301040c5a160800420144000310f1106985403042e002c030303d60440c04c05124a09501c134041c0d44210050758540608401c0d00406081150540b01b403240742601d000c8180013030a8036051f55950a1a0b504100c0603444640d40e1140c629413207080d04000c003000107a000b404407100d0988640303020428000d024005002800b80d54002601075000181e0004446804507001c01035480c03814620f0304688941150281 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 72604516 1250 72603266 72603281
    0x1062003090f04060b040e040b0c040f03030f0e04140402011e0504050105090a03050a150f14041b030c09140903031608090703020604031101031802030c010e0102100905070608010801 80
    0x116400c200500e4005003881e258280340c686010f0008a409a40d900030441107501c9680402140380e411020321040240300f03401c00d900a108030702202d041a041441c94800905944002070505c10080c0d03d41e525140102d41c14103403110000e004020480c00d0480c2c2d605c20060888049000402458810200d0004501022883c0b002c42e0344040c140350074140103596540c0039400c5c099222200b9080000000d10030002094a00c1c815182107484000380b0380044c0680e030f00110070412071800c007030200200710402d034811355101c1e410103c80c901000c07088448021308207030f9401c090003400c46030078089140c5185402007601d10101d081540501e03515039803007980368001903840e02c14020a0a07254200b0034817400700250030100303110135501401e81c2d95000440e150f200b43d004403255125054801059070301403107454001000114080401041c981c0001e4580742162030050502c441e0b404070704081d07403080006107070892029008020440f82418020380d15202446035000041e50b4200101304520306004044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 72605766 1250 72604516 72604577
    0x31203181b040b091b0903100e16060309080906090d120f0f11100c091205010c03050906060d02090a020d0504080d0501080f1b060702060a090503011d03040302040b011e080106 77
    0x11440c5c4c0521107041031a5100644d8140d00d882070210401c100e4001d40704a504940140009124015980c24004a83e009940c410405c3c94030300f52082000c07d44031021070f40010822141955185000c0d0001a00c50030a000007511041c00820034944a03608001b041503515141c0c0c44881c011100ca550031035101c50284140340e03842c0c010703140c08002c410705500580781000380d03414109505c1c3c0d15001d4106100083c03103800e44090791903440c000d494039054490141c10030340000140ca000c0c0361800114048a800e0700009005108170780000c1c4081415905440161224060600c03280c2082d082a416a80004840d001c55519240001954610000d40103044030030b081c010348010029904800184050b10060f51b400a004028010041e070714240100b0982c100d035140c0c04001818241490708455890115003c90aa40c00052410400010039a400c8035812a00855021900b400480780e2084c201d0345004e011028a1100000070740282025042e212203680301c2c50b9545488a100452811180611 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 72607016 1250 72605766 72605791
    0x3020a0f080307080a020a1a070807030506060304020f15040303051e04030b0f090109020d030503090d0306120b13020a08101a06030a050403110d03020a031109031203181b040b09 78
    0x9000049006020740340178009401901c100b140d00351660303c400c0013100a5075054040800c02c201c046e64000c3c0000b50810458a01000b05241c40c10200d01c82e80b00107407010703100e0b10070808154a181d45000180c1c1f9182c0740c940d0711700d80b01c0d035503441e001c0c0a5400c1102c94120310f0034034075840b5201e0080e0744281c0c0c00f201e03040896203002c1d4603400e5070000e1038000a8001c014a540750940c0f2005a12401210321410b8400d44d641540c031301e0250045c03802d042c94080300784101030800904014407000d4200481d092508044000d045884503d1110309500400f030b002500055810340c00181c503203000c906020300358003c00e81407251108040c044007514918404580c0d01c5182070000c200a8041684044d0b0f0043c402d0030302c50a00080e510585184c001100f100200113a0000344010141d613140c0504c091170075401d00a40d0a02e62090006903c4103e010421078803541d0200000710011040100d0b00d0300360001c8030a41b00d000b12041c10703a000ca030382000003060046090400c0300c1a5070808130751b050300c25035901689 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 72608266 1250 72607016 72607027
    0x110f06040201230d02070b0612010c0f03020a0306050a030503090a06090302011202030403021009050303061e06030403030b130e0102130e04050c12100f140603030408030306010302130b0a030603020a0f0803 90
    0x7482240100080c41c0c0c083c0010520161403002e0191000340710a03030045104d880ea508e0110200718004e498942e1040890341070410426140d60002c80144155429040150322150b0002e0124003c0c102a4016940322410010000c00c1c0b000c00300003042c070010141c1725011400e454400c103039a003851a00c0001d000ad40e104001418075041640550381051091041e10354580c854282e140c21388207030840035141a0000010305c6190701e040c2c0c5403c80140341c041c164200004003c00010401e01000b0000360500d9120300c0e403424195a48020b20000e005402410007401a114100034001e41040c1a44e07004005041b0000c1403800c0c0061285214591040041006405030f0081c48540c03158170510407440e21502d04144c07042203882c0107280290705160f000080341b104107800718480313481c00742025010f80c00400c818040c000020089a60008003800d001d40d0710a00e502c2503080a04260b0300c84980c4400110b41c1a8145038980c0040c0c040307038000c40d905060300b40c4402d01c43c01c0030211441801c1e1158010840c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 72609516 1250 72608266 72608297
    0x306181e0c150c03070c0e0105030c1e150d0203070315230103201306051606090203100926091e040b04050108070e15011d0a08030406110f06040201 65
    0x801801e29500364031070b60308150341c0406140c0b40d5080240200c428a0115a00b0320900d1002c007043d03801440c3c00c40c01030808500d0080071411aa4078411140491015120780d0b1810b0303201c07400b0228214071061841541c038a040c200f844001d4009444440000342018a601d8004044466403019103030f45d007000001c410120080d02c0b80300815602070b18149074072800d072201c508000c1550101285480c02d5500d40c0c07803142582003800c00700b02c0c0d08520103105c028421000306040000005507010f9001c41c2c001180f60050000a00d4040d21390b403150001401e0894210801c2402c41c84240a42c42201d01ca0303500300550008040d241c0144160141c000b131036400b007900044c512414102c11108040c100282c80c00140001c1400d40c0c509070014000c660100104001032081002c03a690302400e0401403011400003800000c001d44086400c100e4800d0204500440903580c280556000b804084126aa42ca554000c080c1400c1d0303002418611901801c0703403000f4015030110b1501d1013039505954055003c00c07501c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 72610766 1250 72609516 72609529
    0x506030604120804110406060e040b10090b0a02010204090c030e0c01020d02031903020d0f06150305010312030207020102010209090f0709061d060304030207080f0109060e0102120a050a0b0306181e0c 87
    0x90040d601c00c0c0d001a071030105c548031171007218041c11480d52a80400004c620078081a600d950195a010740560105d000348076a010695000741c2c1c4070065155941d00403403408a01a025a030029002c403031501c01e000020540560080070b200c2640c10075240c58880b40401645c80385051041c801c00b50b00101b20b140f49002046146400f00385540c10b005042000c40c0d940ca034200d40544141c0c141490352060144428650b180c02030020100c64070b800d000b15811503440d14803907ca068681d40906401040d00d0f02160700039010b88a08120281c030900b02443d180c8540f03940e0030001d94050000c200e418101084031485400e1985031008014070340000f0a80740b00a201c000ea01c0180268118011940085861030040c00300c428800403510011849404c80d003000340c200d41d14640100456031040116000383d0003142c0c100c5901100300100000d00780e0b14207003550094408000701c2c1d81e050041008120029040481c0001070b40d0780407040358540c0d10018005200c28a000c1100b45491344402c10240b59032401c103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 72612016 1250 72610766 72610771
    0x30d020d0f09080604050607031404030c030c020a030f0b01180b061204080f0d0b09060604050f012106060201050103170306091812120a0b0301151703071a0a05060306041208 76
    0x5250803200c1035038030f0b201039040440a65044420b80c10800c03d0061031a454052030b40b40c0102c1c8602d0038840c0c2050340e000381000800400007000d0110141e83e6006541d19680c4010046401200d05000c650441c600754400003000d00a00070400140108143e075031150384a411130000c4007a14113072820700d0030400619402c0000300101d8218200b04510700142300500041d00010380f420102150045044041000c80d007001000f070350140005000410107030f82c0307070781e130203130040800382006406034181d00c40003000c02600d000b04100040c109500014001d60540c021070480340248186500420182040651032005440d280d6000a00001107044808840c0380702d01007204150496641c03048210140b50160030060080c10012210020481028940e0041c1c90701084118000c2116030340c074605600c500360050160007100086002107120f01079040088070702c070640240da0f8030070390701e000080c1107110320f41150b031000c04508201c080b80c541d00700000c0341030155500c81c040003060341482d60119940c0000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 72613266 1250 72612016 72612047
    0x1b17041203080a0c051306120b0a23040209030d080c0c16031406010e0109090203010b090a060315050910050601120e06011a1e0903030408060a06090b030d020d 70
    0x10040050080080c60010001034400c0c0c03681001032914002000841c0c01680c1d41c4000e100b03041103c1c07107104980d070440c3d4041d5415820b2402c0402503008021008010007180300350030500d040004203c00030212042e041d200000070034111600e07542c201f440240e01407922080c0e0160300442d4225055030007007031155440303000c4038901410144c2094280d03143c440f0344c003000703e4199140740c8240103004044070300540a04412005107800d52502040d01c0740d40c40144513901c0c1e075a6945404604541e401e400c60f0440d1000200004410700341048d0703d0005014500c4200c508110080c2c042e61241040c0c01080e1280c016840507040800a00b41e240b809400014111030401900240609001a451055245085d07290000717000035810086010005d04004014004906003804020a85041d004161140c11060a08162076800c08030200380b40d40070300e800151031405000d04001d075000c650340c400c01c101c3d07844031000c1c0014041201816160402414250010303000203404084d0640200c0068102c2e118 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 72614516 1250 72613266 72613313
    0xc1106070206130909060c020102190e03030f030405060106020c01020d05030c0a0306030503030f010303081f05060a090e0a090510020c0a230a05010e0d0905060301031b1a0a0f1b 78
    0x1002c250f03000440020b0f400c41d1650036a25508002808950b100f80018181d071400214a002a0404040c441962600b890000c00030603c11401c41a2428000e451003040c15a00035034581c101403614039244d42090003240d00500c0b0b1940c1d40b82c40d542c80080c14404068454480c03034076603110440c80c0404d6901c20103807003080c16212580040001e03c10030040d4801d1a40180701c11300307941140340c018500e030f0300540281c40c0300b640006908150410420003400b100c03412034280b5900c0d0f10a000945054030139502607440c0883c0602003061410054010f40d2902c1d2050007a100c0b0340d1551200402240203882c81303498203501c072005980020f200e05c1e0030030f00402c2c03910781c0180101280700901d034a0b10715051001c8030240d440d079001c885159410080311300d00400c103041c96a1070500b00004103040d400144805001401b03805d1074003000000c03070000d85d00a0022541f646d5044507081009083c550b0080c107103840001d040104c0322494601c294000070405141c4104031403a45043d80310621103008000d01111241d9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 72615766 1250 72614516 72614527
    0x306020d0b060a030b0a0e0108031204020301090506090a05060f0c0301090b0102100c0507060b0409031403040303020c060c030403180f090f020c0106090e1b0d03030e1908040906060c1106070206 85
    0x60b596030203449500c0042d600400d150f1820400c0c019000e8903a40038076a000c40d8007006200c49230001c02518400c0001003d84030144d03070350307000080c050020902c020300180100d8090128060b07021555071201800303003089032803640311140e0840f0300e01421510201040014001030024250076000445041814811590016102c943d2201100d0480140201041d800201c107020840c0c68010ce107064042124100403406591300c0203440082c941c0f4140c14001e030300200060401d4081d6040e581c078104a40e04480c000e25080e20503d0310b0307600039141a40030a1a0864001c4c09200042200099605a03030540d40603900c2c1c403907107501030701a4010300040d40c1d40911001200480c00d10601c00102110480807407144020b44220b400e2481d01c040103003003000c0340d002c040341d20307101d101c01d498929030b05140002e54458412a0307503041000344505050b000c41140385080a0100c1078000d8030541e0552001040f00a94801050315032011a0f68010003020305403104105030301e00207000d00556170015080d031b440e14 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 72617016 1250 72615766 72615769
    0x9040f0c17010c0201060b0d02071e0b0103031b03020717030c060c03040c0b03070c0809040f0207060524010e0d0507050613080d03090201200102092223010306020d0b 73
    0x150116045110003521407014501400c0c001d02401548240c180020411035062464400f55881900030340d040c2c0c0e0f43c0015100040140c0002032007000392020b00c000306d210747e035447c3c0a00800c0d401c4c8000d4000900c54070911641c3c55000c0550146260705070000d0140380d142603840640c14100403041e041901080c000407040350400c1c001c89124245080d2a66070340d103400e02d0304001201c8150400356041d9018010400c00c0e07030300300d60001d4449400c90802926000072000180c0605414003061039068004500901002403c0c2c0205000f00c040400c0d101c119103000080c0d02c041001d24000c036001803806001c0030300c00c2c1411103042080c24000c50943e000035403101c0115415078450031501c0c0483c50b81801c1001440c809000d10b102c2da00442c54103010881407a000281040200c2c423050100c16030201c1c9034192041c4c25411110714800103418460505103c00e946003a0341c20000c2c031408102e04200e80b1a03220190600891070000e50209141416400c5032183c10081d0024030300d812030703180d40e1703c1c015409 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 72618266 1250 72617016 72617033
    0x20115030b0915010303050f0f1603031a0609030307171204050d030c050a050711130f020405180402030a0f0f1b0315090201270b0d0209010816080609040f 68
    0x518001e00160301c25041120000b4500350309080d070101041c500500500020342e100045411400300082da0f5a00d42c141c442c2030307081920940c04021400c004541d54401010b4043c6c00960500120101000c003003883c000a1010501c151201240d068000300411340000d01c07448002d00321130b0303541014076007841c46410381c40622020588083d903903a4800306951a807a039150041904003a400d207411401c03c07880c00409031160048140040030302450b400c44003030750388039401110920801700c0c90503c000c0d1200c1000d980294418000c0328002d2040841c4462044c0441e44000d0046502030011f25141c045901d070ba02021508003c110f0303552441c9182c2c003000c18604002c1c40040d9502158000c812490740c9400c903108846408281011030034140a070001d40e800c0500e4041c000245070301c1c0301c0d00e11001402c2cbe1741c06001c1c541101c841c001000c0780d8418948000d5000e055004820780f1417142640b208001700d80c1c00c10720f950540000880c0000019150300700019030f1a0428418482c8101c504019070f540400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 72619516 1250 72618266 72618269
    0x9030504081e06041202010f05010618080601080303010303030905070f080d030b01020c0306010312020c190e012702300a11040305070308030c0c0f21090607030f020115 74
    0x14404942804101e0042c040d41c00c4002c82140d400e005055070080c4162103c500810103450b0002c40b1240c1d5074214000e4101e08000c541e0148100902d40e140c60780904080d1002d07940740e281092000e80414080000a21103040e106d841c0000e604607869594118043d05c002082160f45028030040003803500010b07081d03c009004d2000c05051070720903005000701241c1e60907001c2411580701c6406504651408942c0d03d065039041032aa40c0482c19103142680f40c030a14106060b003015052110a0b1200d00582d0414160b450150b4036031400c0c0da0301c041c2c0302040e00489503440d89083c24401400340200c1560b00a100280d5910404152601a40c60205016001c01031101110b1001d000b00452400b003445072150400d4803501c02c40c140340c10358891585d996494040100042d0000012440300c2c13100c4400e451010401104541c42441081045a00d941d00044400d401904500e4182c05140d904029100c203d500600002e00300402034030211001038a00200340e0075556200300c207100000c01407583e5070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 72620766 1250 72619516 72619523
    0x906040807140933030106050d030e0301050a0203071b020a030c031103070803030c09010302030a0605210f0a021c02130e011409010504021f180e01080c0111030d09110409 75
    0x690700100c4420f02c030600c0e070000c02554510803101c0011058240304003803501c0c2c0d204000f5844c40121011804680145000d400071a0310175800c6902104065004c0e51010705000254004e01450310343c2d034000c0080e8002550000c010074042800424030300340d001d810714011800100f0309940c00d642d0b505e40425512041e00305460142804902c0b070300c0341c10b042110710010310f50200254a1481d00106142c524041d0ba1105810141c00002080e02400c10b074104901403e0700504520200c0e000600c090410000c08440300c0141c00f412101c00070905001c0b0756821501d801a09911a04011910340c0980800c0a04106d0740000060301034140c003d0248a0040014001400092501454600469282d41c020701c16241c90303040c00100401a2a258101d042040300b540d541011144180b170309452000181715170890b14110074500042c0560156074860407100441e003030f52000182c050044a12a82075114038885500811030381f114580302c0c1d80017030341d070a01800c26050080321203030000d030540e607803450140c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 72622016 1250 72620766 72620789
    0xd020105071a160314010e070e0402040504060603020c1006080706080403110d0e01030b04051012050a120203030601140901080c0a050408030c030301050906190306020304110409061509090312020906040807 90
    0xe20f80181c05100d80040c2c14080150800075614001d0000680c88006000328108001c41190701201d0715140c06882c06040300800522a15440d8180100203410100c0071110078403800f880c10400e018244904002c1d6201d0b40081c08440b41050010389031010007034011420000404449611034a080c8203444244000b90741d40c8800c1480003000400751099245a14490f0b454402803180e400d161210340f50485005040147d6215510300740281011100d810103020310b50158072801c00700764080021441000240c0303030011480750140c110347c004d0040d00907141c041120f0f24080b80c9005a00f81c0a04006000351410602c0c0c0360700c0d061014210780003030740401c189600120040c8107500d4544c4c011940300300d00fa80c030511800c2005040e16484140d0784400b800c2c095000020400703218020a00c4d21090ba4042c20074005034060345002d0009000c4420b600e060355580e4000801c000c8800e0040b41c405507007541d5100b2251141d0301c0c0c4030380254032082c03403540c3c0a0408c01c0000380c03110040c00300c60002d22040714070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 72623266 1250 72622016 72622051
    0x8010504110903240703020a09090914030d022101030b04021905030706030204030b070f020307080d14010e0901050f100618030b0708090d050715050711010f060302030f0c0d020105071a 81
    0x710f1a100401905c0d4000781030040c041d020302c00740d020b41d585044810900010405040c40c0c02c1246414100880140c5503000024a03402c0000715074000f005c24160f0318100328014580d9801e940002d01c0c0078000101070b20f0000703010501520f40241022002030418000344078441c0e48600084c43c045081e40b24001103034010500308240301c0e011003900d9000503070f41004412810031140080d124816400024201880401c005c240c110aa9109c075410814003030b12040c032035031203a020f040540d41c101c507540e01c25801c1034000b81c0d48058040409014100e6880300341c1d503c5040c0740c420f81700c0318002d1502040704081c40310004042010613002038003408003911a9940c41c03e0022300d15003498410850a01400003c006140005d288aa40d541d02183d03a0080011145c4810030100c907a0130304c8661200380d070760910325100f450b2485a800001224422001c658070a040079542d180c40f12814207050b039000105109800155001320002c0020611801c00c11000c41060402c045440c481501c60300300c048806401c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 72624516 1250 72623266 72623323
    0x9150c0a0507050409030c0308190507030605030d020a0b1302011b11011407020619030b10020c0316051c051204080a030806030a051f0905030301090b01030b1008010504110903 77
    0x6040050801070744d0a101070b108585005e407001c0202c404c01000c1002c143c0c00260040c0ca06085030000d8450707040300740454206920000c0142550b400307054480d0081c010b8442c0d69a00002e00007022a0b40079030360030607580c0d910013035588011880c80306905211603003054610009a6100040500380305420001510790036500052860840100c0130740c68a80800895015940e2030701900ca0320301c00c04040c0f2405a00c0114214090810140710035081a07500d080507031265008a140b90340710f5402e07003c552246c01c0a00084208103242d21441c1d0700000040040c40c1c822914644040629008004560304110030480550301548554031401c0680c00c0603002100301a03100712841d8120804074010600100c20391a00c68036140c412603401c00e2001d0080103004810180d40018818580240951384c413981d681000b0006231100401060000789405405111440d02c0e080d1000a01210707614125107038245810f1000402c0680440a100c0f1003e00503407085540c1040fa40c15030b1350380750409994460400d074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 72625766 1250 72624516 72624523
    0xe0111011e06062a060b030303040309061b030c02060d1d060105040507050711121c03020306120114071b0606140102010f0c0c30020706090807061409150c0a05 70
    0x4105204100c41804004202001c1200c1c00c0c02481c001c00513000c018415251140c0104050300c0c41c41d8050002100300300c1850b400440e030320120740306501d400c19042041103071030404003c0b018009012503e0f0148a0016040c14030242401440320040095004416030300310003000c010002409080d444107005004a0926001e85a040350490030004d00300320803030707894030740740d00c0001d0020380030345018241100b0011042007a52080b1040300c03a8640c000c101e84000034003940c0304a400078041d104403107580130510814400d0840c00c0e030716000c030100242c4802d04e0440d1702000c00e060400c100c80055103031001013001c522801c070080501720040144d154500c8006800e580f4166910551035180c030046d4104280c1104070291180e500c000703000c3e0402041c01940704070f101c419180c40700c007001c210300042c2441d4000500c130040e00c005896107001c0300d030349074100781d620740c4a402030b0340c0046c002080400d00d07038249034040c0044c1c6100801400c090062841d0200d02170704440424800c82d400111490203001091 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 72627016 1250 72625766 72625769
    0x6010b040609090908030103060b01140f04170f030a0f03090812061908030a0c03031103070c021305010f09050601030e060411180c070809030312041a01060e100e0111011e06 76
    0xf80e003d00c0f04d290180c4480265000c14480070b4181500c4804084681e8856102c450021421413503080e1034101d9004040041d4100303000b04010908d94820401140c1400900604220b203440000c61600340d44420485421410f003880701c06143d103d454050010300d17410041c1c810000100c0c02c2c1e48036481c2c000b00b0085101c0200b0707031404255000c80c00a0062050100c11249548290f00f483c2c80400401c0c90224014042c40b21046c0100c0360102c18041240c0c0d1204c904941a402145c0648004403030170070100480c0c40038428152a180264000c000c414000d80000d540280305040004d081d04c0e45241a50414804442c100c5811079036009414052410054008000340b0b03c84210740c4501d0640a41d10081c03090f441c000e881d1240100b440b03401664100202e8031002e580110784c00c403508041c40c140030740400b0302c194a4040f01c03c0b14004074420740320b50341560031410001c0036002015103504094405d91481d00c041c5040002042074040c174840300340511841c0c0204c0504100e68142c00e11900d104540780e5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 72628266 1250 72627016 72627029
    0xd05071e0f1106040302060d050a061d0f04021c05061008031326030408010b0907080603060613020409060605040f0503070302030d120b0406061d01030506010212030405030c06010b040609 82
    0x4680e0340d01040c0c1c24030212154540c044450606100c800001074114012030b48020350100380029607a0b404900342d00264054800420180301c0151128810488000b039114003120000c01400010040e02011401c40d07005400605010010314184140c04010313040803405541c1548143c0c284201e01c040e105d0303114001c0c96000e001c3c5040044902151110441d41e200c1e03a001003a250741d002c5030841220a840b000101c2040480b90384958905081d40a000e2403031030300340301d0418000002c424a0040d004107104480042c082e018a540f280200405a1070307820401104030b40c240070100300c10503644140c1000c0e1056484a0791680c2c0383c074050109003100c80d040707540640c04c03047e01040140c50008000c0e181d8100d80c2001d1401560580d07120300240054117103507921030b05066000035000d8100340c2601360200580d01c540c5000e000360300190141d030425240540140d202016094580f80c054000d1030300248030300306492409a110601601d000030a810014180303400080c2000100d0300403d440009004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 72629516 1250 72628266 72628313
    0x150903070b090315061c03020a030305060d1106070f0c080106050f0a15140d0903050414030f07090b0a080114090f06130201031109090a05010504110c0d050a110d0507 73
    0x41401103134a88a1a034165049410f0b0780001c182c0c159200140f6481005110203511405d004d9030900079907408088100f5008a8940401704919060036840341c0350760ba07000801d008050030310b0b00520a990b4040007096404100c40012040005c3c80324420f10020003031fa00010409504020070840b200b24000009485040d21403000c01c21503034028081c015400032806e00002610229894031500d114902c25860b0083c6880700318001c154120f40908141c03607094a4a00303003090003206150381c0348503000064120703038081e8404000519660f00104004a0060003400c0c02642c1c03820f0107802d540c6040e0101e189407039034000f0040b0600302008480d211b492844020310050501003424409150a110301038101625100f0410724850800200c03000e03000040c201c1c2a2500e40040c811004000a010b0107224a06151800c2c030501d0115050b00d84035100500a840c04801c2600c040d075161b07010720701000501400c400308940500c410b1001501294440d00e510355100024504002c000d01c444151214100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 72630766 1250 72629516 72629527
    0x23090d020604020d060b0d0605010305010f0b04090b01031707020612160804120e0d05030a0c03030b12070905090705030604030f0f080108031905040b16050106050103110304150b150903070b 83
    0x944181d401d0303d090390040c45c0000c1d00b00140d40400c0c01054014000f030131450804000004014055110356041c000c0301e441000704019100c2000162440c4510180c9041c14103401800802c0d42c030b00841202c045140ea0052a120319903003c10b6954011010960140d09c0c140c3c00c00040581141110103080340394608000e443c80d09651700c1240b82c80080c0a041044020300700d030911610303420100340760a9009000c407038407030004000c020010750010360704900007070800c10700040c00d0901071a2911018040b0b0080c00c50395080101810040000907c10501c1e44210440001e82e5202801414041c03070007551a0070320303c0074500c2c0203002d19054424020821545400410000c034020090750695001c0d50142c00807001c0640d81120b8500441d0070203400c0349400603036640300c600340c640c44111592091000303100c0e41d0b9a0b031005500302c0e0b0721039180c2c1166401c01c00000300021182c015081544040103000100c544400b800f040348008885020b081c2c04c0c000240c0e03641d40b490200600001001010304091615 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 72632016 1250 72630766 72630769
    0x501090e0d1209210e010201052403011104080a0c050904020a0b03060f0306100e01090501060c15090c0b030a14010302010e0d030c0b090307140105060307051323090d02060402 77
    0x1a040003a00008220007141c0300b80c544400340d0000341c00c3c0703508070b00090107419484031950441c092011041000c50351200f601d841c15401806000c3c031410604012a24a4003048240003803924480480c503495580e941400d10320f41420000350002c2d09000303005064108107480c00c2c2c5103c40141e000241306201c81b00030040141c0c0c8035a1f99406039050480c5040e101d0701d40700007249005007a1407810380e0500034442006600c0441140c084211066440003983d0359984040b114211142806100001200b1580389404200e001000d0704001368920b4000414010603100c02ca0351400c0c0381c001d04035050303000080c00700c4502107020b4505003488203220b91006500d9503002070109025545078074060b0600c80800c0c01454010509000c045400101041943c039042c40c0c21a101e034841d00341120a6030000301160342c0f40d1414803d01d8483c8001900034046c480c20001004100740b4560184040035840d4003800e48042d4404003c40b520070100760160416040030400c4604100240c085001150302407420440903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 72633266 1250 72632016 72632023
    0x140a0b182514030a0902040f1b02100501050a03030e06120f010311030c03100e0313080a0b240103110d18030e0612040b180a0804150e06071403090a1205010501090e 72
    0x10703044c00c000088a000920106015040d41103140302c03500d1500e903120401140032001381c6012511642510004004a0860b40403100d00303000e038a40241d60070000f4400240204102402100b0081c0841d01f04000801860741f520002c8503112034481c90b0900400c208a0108028140800c0c00c41c0500024110742c40403960310f64602c5150346103c0d031681c4001c0725000b000d0003141c040000f507a06c8054015210303195159207050070039007190320201000002e403405410f040b50400001400c510070303090b8a10300004501070000c803c0d51381c3c070aa20402854006001c00e1041030300d40030350003c1889010803282806464102c1c204e100d64007038a01080510b04a8007071850182e4040d038030494061813900c801360b5602c03044a41e0700c00320700346109050b090b005010540000c0c00c200d505e524592250305511290403500040c1902e81d00e46c00c64418015200003942210b8602441030244003160705220748080010910b00700355102a001216100390030050150038015103001d028507120034419840d103503500315079 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 72634516 1250 72633266 72633271
    0x3030203120a0227090906070c03050a0224041202010c050f0c0c0405011205070b0f090d060e120a020f0105060a050105130306050406060603050a140a0b18251403 71
    0x9001c02036000980442c5035506460840692004030421311000c00c0c69021045442c04242d171046034601c00041403075000080c10352040755aa559a554841903030b8040d512604040d007500158020b0700c48062910800003030180e040c40038031413810950b04050504d900020b002c0d100b41d1003164101143c1c11681500f00040700c182284102074540d49800044440e41002c420b102c900c0e44c802c0c1000c0001071002008501d041c45640103030280d680c12a80c0e10b22240d4a84508696110540340c18083c40c0340c070340740600100850a004000c007180c0061043c0c401070074801c1c0200c14600d54080424a0b075199581008648400300c3c03514020041400c200000900c089803e2143c0d074104807000403200503100c1140404002035030720420a100720f08003850728030003800880c0903c0000900e4880002c040e82624002c40f07030110384c3d0000101c010303101c1311040c00c003a0402c080543d800030800d500500070091740d14912403240903082c80d0051082c01003d010f00f030071620b15005008108414510201e005c80e564201ea4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 72635766 1250 72634516 72634537
    0x6021c0504350a0b072f0303041718040f0207060905030a0905030111030f04210c0209130f060c09050310020405030106060504030c260f060402270c0f12010f030201020c06030103030203 81
    0x44105582e42d0800340c1c2e60310001e00c420010f401341c0e01c00454100c0000051405070740b01d0f000c0400803071114001d41c6040d0007a409440300300c0882f04000005d5050540c4580c2d084c401000d0050302d00251601d4440688609c4041102c144e84002581c41c2c0d400e0b401a5034cd0b01805046000f84240320200030204001c0c00301a014164500050010604000c0303411060021141001101d0b4400c400403140a00900e160783d000741d000d009042c00203035414070800c4910040c0c036404281d0413844211b54a03080002e14425448405103d03499101060968003000384c610341000e28800507986509080503d800d687c00c0303521103010f01c0010303c030603c0022010b014000684511841340480c1400180d8004420307081441600040d007d41441002d440d500485d82920541c02628fc1080300c10003517412182d00146c4684841e00d105d010001718140ca07101c9402002150644120b20b4103041d980c0816038090700342030780105080c4c001e02d44c0400031541c05200806500408494542c159850354802a480c1d102e00700360b24 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 72637016 1250 72635766 72635777
    0x80c0915090409020307150207060f02100c090506070c05040e01090305070f060605060c0d17090705060313021503100b1204020f150d060504060503010606021c0504350a0b07 76
    0x3900303611241d20400f08075400404030b07107140c3d03507810341c0001049a04d052880103012304403020440074040c1d0910b4113400c030f06900030f020745003070f403542c12009081300c596413010065540c20001c4c003580c541c00a01502e03030007200340108140c0b41c401040704482c0501c07205960740e41016044030209401c81300790365820b6040050200580c9c503901d0710740014110f03078000b141d10403000b05549c40c000200003a03441d042410703611001036560309106451480301d803c0300c0b1034500d41e000b04001d00840c10090055034008a071138040201d520004e40c005420402c0045a80700040d40100403c920009240704120042c60101100e5103040a00440c80c40c98540c0140007070b00600710044800b400f038031801401143c5080041c801c0d0385401e040c48a00c0c1c081c01d80d03481403a1166003800b2020803680383c18850142202c02c290011b052a03407a07843c1d400c055150380d01d8403c080c000280070018010004400c0f50540d881c40141c446081c808403003c0443d404c0c45448070740d0559006e040b1040018002c401d00030f821401a0810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 72638266 1250 72637016 72637027
    0xa090e0c061c0903030e0c01080c0a0c03050f04060f02070e130605090a240b150406030e1f050f1f050906030a08160203060705071509020103020c160501080c0915 71
    0x501600b40803a600802900d1600c6081d10a00d80d066103c1040b0030a0801a034190b507407064011a0081025121805100d07400c01c0064900c038000c0b005880351903c2810aa0b003000c10b41600840681c01540c80400850310a0180c400180c0e03043c042c000240084802c05d030110705061403e6400c030080090003c0c20241c2d25000f240c882c4808110001d600d503801701c9100b140851411081102802441000c02e8072802d191150016142c601940b01d4130342003020301c440c10035181c0301044026010090404015019003c00e00c00d4031a204602000050082d24010490703080c14803440352800d500070308c0442c4240520120490382001581c90004868044840c40d0b412380301e400010b402d02005000040c00904006000c56159610900d09000f140c02202540d03815520401c0a56251151441c010801204446800c10706017103a40101000790044c500141070214a0038070515000791450503000441c1d1031481049150b0340034042a5101951000f410300313108081010682c0440c000d0101207418001295 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 72639516 1250 72638266 72638287
    0x15010309110918010b010e030303190b06030103030203040e0c07050a062403050a0b0601030b03062d09100501060e010f030b0613151e080c03040201110111090a090e0c06 74
    0xc004000c240300400544150400c0f04140102609a0a00d00d0f219400e10805021542c000c110300101c01001901441c510390f244141440c0034003460070a914055641c2501c1ca0703443d101c00300a140a5482900210358981c2010110400c07068028081c40007803904001c0040090004034035000c449500000c0072030b0007040350301c00c800c98100b9000524000c02c0d030941c000050182c0055611001030244490801c5c1da103510004406843c4010140307a0142d0001c2c020444003d050081003883c1c910044d100c4c0c1c0060030aa0141d50085020350f00750015134020700300c219035a07200344202c9004084600300007669401c0d0b500081d1103486544106001d2564030403043d4010344641c0300301c2c2c05071029154412106070f100c10034081e4000018141400280d5403480710340401051500b134514a0240d5112035000350740d21400f00321030b9400104200e0400058200c105055402405810044015400319a44a80d44041030140c90540c0b80c0c8507080b0182030800c5d1100d0071a010400043d10001600d030aa6154400807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 72640766 1250 72639516 72639533
    0x11a10080907080316150501062012030f010302030d020c2803020a0603091502090a030611120a241401030203130b09150a090c0b0d06030203070314070e15010309 71
    0x180000a0b41c000090000d03940b015a146400f0251b104003c01818404401c650000302e5400740100d50100e480c8442d1a000e981100717551518451030341c0101c0740720404455030b00e55107800030741d6000c00288800c001030045140038010f40030411460310003845c50180c0280041c1001d9007800016007560b4900183c603529404280042c0040c0d03801800d20080705039200b5000b001800e050b0310036500503041d004e250010a910313000702d03005018010300341c48000e41142c6880d0b004018030702c4001c05030202040315901074140500841c0c8148500c2c000000d00440c221466900c6650180c032a10807444803000501013020401b02d07103c0e14910a18005031a585c0b0b01c440e00901111581001d4142403a410800c42c5110340003138030485400d1b00c2c00d00c14001c0d03211071482c4c01c185c070703581d0400400508103a141481070340e9080d800b03008050701895011590b242c2d2600480c1c1001e10b2a0000c0d1010b040c01002c501145108011000040110482e0100b182c90407410019806528100b443c1c105a15a01d21005000381c10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 72642016 1250 72640766 72640769
    0x80a06050a030b04030201060807030503040b13050d060609060602030a08013005030d060510020d08071b0b1e0601080c0a0c1505150303031e04050a06020318011a10080907 75
    0x1a26075030290351a42403481e40701034100e60880056003000f10104a1100103d10b900899030f00030011410035080560040d040d41001c0042c6600041d40344001800366602d46164103c603008180c0022264144402c0c00181d42854000c8402d542c4104114401954003511103030448412080404503001581c2c840c441c00d05204045003a1b4110900e201e5040c800c0204c0140900d41e5a00d104011550b951403c0c0140541d11420341005a08081402d412a90007013031340613071161551400303c415038030903c07980841180a00040d9803100903a020800072481810b003200180c0071096520207181b408000003800e80c20300421403402c450010421040309406410741c6903907030358400c070002c3e1120440c104050040008807411007120041407205038241c10080101c03030060000c2181400360070000d460700b8000c20806002141d55100d03070a07110010400909c05503001c0c0c0d43c1c088102010f1a00d1000203400e54454030009411000000c0c2c000c502ca80e035010792242000103d042c01d00190740c0700b844c02c81c10400706 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 72643266 1250 72642016 72642019
    0x9040f0906110a0e0306010b03040303020a09032301050a1b05070f150c1e1e05040308070c063c0e040905030306130605030703060b0a08010207032105041101080a0605 73
    0xb0b1212901c2c1040b24603001e8002c10009603207038402100c50f40c040580d152001e1044020140c010408100420711030b07002051071304110304100c42865a695039048804001c16003d4200095050300c03800c001d1000e007d030541003820420305004040102804900f1034021174854800d1000002d00309007009041c4a00ca00929001013405200c0e0004200c103801070244068410700061440b0060b4101c1d0001c1c0d21049003102807545ca44102c0f907000610084000007200c01d0707000f4410240400000501d5000007443c4180c41090203070641e41c03034020302424815a072160349041b0f115148001c40d02d03501d88400403950f4100301c0407039540e01d100ca00050b2554011040703a00c3d0400e081c91905e1050040000085010342c10075900b000030b610100381c500c801c41d0118003406078140c006039010400700d102c542204051318401445942c2d529a82d4407403500f2603001d0b06045001c200c8a05038081001040300c62402104202c14082c40581ba01d55165610700c03509800d804d0610004001080710414254000b2015040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 72644516 1250 72643266 72643271
    0x40c140315010305070219111201020301031112030a0c0803040609140a050c030307030818150f10060801030201050d090c05030f0307020907181802091309030e060405010509040f0906 80
    0x100125051500e8201c203441c540820b09000120b40c44510009050409000c000f40c0c0b1101610690398681080034000340040e8400080c61070507580880c00c0c40258000c1d4815a204003a00034040140b0540c1d101c03801078034003190400c1c818501c5880d0821030020145500c150741aa9942d190f10f030070001001c04200141641c04034624107a5048400903d142c3d00da03018034102e524420100e02055680d02c80e01400800203941e400110300c1c4450850391038401312850340d00340d481d541100d5107500030100040380c00307515441c03080d8203109a080104060708003410311464800c1e0703250305580002e003a40c4202d00003c1c4c009a910000b14041c80f0301c01c07003801d0141c0002001c1c2e503841034030500e08603642d030020f071070991182c48042c004c90441c1c0d00400001511a0b078060030000501e00d04628130003101d016200001d0358a4007044004010750710f041c5007583d90030002000040c13885880c01e00600c030f9000078500c81d0086074100030902150303800c40103844d941d1000f1680408c1c0380d28940e0503140078000c4108010800303070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 72645766 1250 72644516 72644521
    0xe151206010207090e0c060304050a0228050a030b0c03040309030501020a0903060b0607020108060603070201023015010e0409030905030a060203060907020105160c23030310090203010311040c1403 86
    0x1450a0052402400c090b8201c580594858100c40215001c001c4a540d03164009001d04d41941090000b550b0f00034003800545840c2201500410790002c4580c444205180b130165240d00d4040620084401900c0195814803d03141503031342d00c150000c2c014080b05101840071000504042c411102d0030003071a4030400035911008001c0d005001c1542c640011158641020003031445414071605961245030141d4404c01e0340e446001c240003040c1d0006d0300c900c00b1075400300103201074180701c4480c619420054260302c1c9402c00010003024071507040030340340c0400310900000550b01d580e480410100109011100069082410b207400c2d501543d442c0d00440e014050540c58005000260303004d0351042c801a21080d00ea075803074640413800c9607802c0721a44040906140540030b0544540c8030942d44034072512044a659803c0f110942406400c1c03140d41031246d000008002160600c001c8407002440051404d500395410743d92076684d8200b003218924000ca03076400351006014810042c481c0c22800005160356a070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 72647016 1250 72645766 72645787
    0x1c1202030306010905031c0810090e0d08070f020d08131424010803040e040c030f0f1b03020f090907261504110d020609060a0305010305060c0304030903030e15 70
    0xe8104940c4240804c1c0440000549420041264404182c003003040030884c1c280c5e0035003561001c00283c0070852609420a01280141451040001d00c20691000f041c801c110b0b0030340180001c0b03009221a0800040e02d9404c0c818607000516034000100c1c81c00c01c10150342d245c1103002041650510007038400c6410014600c140b0001180d0035880c51503412800c9000e22072500c1003a285c020030310032620540c2c000c100801440100c01d10080d0002e200741501d4a006540307440f003d051000c2d90800b56154520034000c0c0c4100b040a014020303900c481c1803920300c0c94130f10b07540009030f4640300401928014101000020040f560606c2014050180c0020a410fa114410640000c2608079404481c0c184074020320a108080407400e458851603112554009005184c0d05001200c100804101d8100b01c0c00c1c0003c2c161642e502d00640041c90b01681c00149661650800c030f850a84098400000c5040030028440802c1d4054042c41c10b89400d8103040f60458204408076040348020319060000c550042541800c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 72648266 1250 72647016 72647023
    0xf01030213120b0c0a091505090d050105070e0a0b0406030e0307060e1e0102091c05010603081b060117030f0304050705030a080a030b0f1f1202040b03060a080c010804021c1202 77
    0x40b500900ca0902d940c1d03a198108106482101002004295880030130403d01000d811600e1102c1c01c1031400b181400552404200006d00e4100104d405944950800020a5000c801d042400f0400c2b00d80d450744074640074010b4802d00c1180038100c10076071190f06140203d1810412038020a034003100800c500d2101002c0140c40c1c8891a100000c10380c60218081000318050003034500c071500040c0280001d4a00040d42d907070300c11500340c007110995207031071002003c1401d44000c1c0c000c210070701c8040109602803103a06820480c05030000c1035052003500310440b002d103001080d41c00214813642010b545e500d80d03042071427810045030320060740b501c1005910410010b015000e486040040c0e18103000c070f10400307020030811400403807005070030422804840300d42e4811498509903421041c10022403039070844582d0400d907400743d04080340151f4004148903407070038548400c0e0b00a10582010b400c98401b0f000000b0443e54001d040a4800d000c00059014055103078030f50006405e40c003094801c001e20144801944 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 72649516 1250 72648266 72648299
    0xf071a070314030a0e1507020601051002010e01060b09040c08090a0f05160305280201020a0b0c04051507020a0b040b12040c05030607090609080d05030a0c02212508090f01030213 78
    0x1003801145d00306c0080180c540e0300903000b405640c000c2c1c032281e8204004d00503000002000f40c0219901d40301c0c2080441c00a101e1080030f440c040c2c9520b03a440e10620248402d5602c6c0b0f690040400c504a8104800c00ca400b15800d00802d40c80700141240c0701c80b505000b460a0384500c04185425103107003002041280c002482810043c10300c01034440b0311484000d4440a8115500103405600401550400078601307810700b56001c00d060040744e00303054441020621100e00000c841001601c00600f01040d840c05054410080c9401c4003003624181c01c00c0c0129596005801c0440794010030b01005c9010000c00b80e2010f030240c18050101e030040d2030314180007040c003100c80c403807100440c03009540800d8508000c1500403120300c59880d9245582c65a038103810040114144000450007081d02e00601e0000f2410304c6807012801c80003007501d0b88081c2241c8911581c120030214a2400b40c00b0102000503140015201d44410882c1c4c1920300c2994000141d010784101214200001c402060210f2a032030141030401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 72650766 1250 72649516 72649541
    0x10051b04080105040c33120614031006060518030102090612040b010603020f0702120a0f0b0103031407020109060305130206040f030303180506010e091002040303030506030f071a070314030a 83
    0xc41c03d683d0303403040781b50100c180d20700003c1c240c403109440d01c90700c00d003c9090058a5403440c184000c14000f0b400401111520b070050b040e80d02d0071110001240c5401c100409286820100801c24286864030141c04e5100b41500004022142d04c0311440e00c4d6001e6042c1c4282a002902d45542e510000c018112039074801c850407100c0e00f03408400410024400c0c42900d003c0b51101860515000d0b040e000c0112402c501060005617220b03001610b80028083d003002014544100403a04d165411407401809001c0760301074500c6c1c0228280035600240c1e03409609881211440c0c2000581a1a444403007900042c035144043d4106100141c0000c42c0b110905100b400c0380c0c0a46e400300441c0001c00c440190800c20013201900580c010001403021008205200b600600c245049a220548454000040c0e801c59401603021030b80d900204070f6203042c184640e40030300180c0000780c01c0c42ca00b0412031b0b040c080481014805c5028010401904050082c0341e9452810814601580c4a1501887c0740d40948891060070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 72652016 1250 72650766 72650783
    0x14040902030c030105210303071101090510051905040201080f09012004061b020a030215070b0709030308090c0a06120207050a0b060f01080c030402040c03091a220510051b0408010504 80
    0x1c40003011940c1d1b46886500c0c3c04000f07186191141102140c0c3d80e02c0d00c0c0110320580d541c0d03840b4807001038000c008022200c2540003010542c0d03d444540a07140042d02982510102e00b40b108000050f0307444140300e64421500f100b071076050785940d18260300401524482820018880d0303074120140041c0f00240c812039002d6999221020400c40c030301443c1c07141c0448005c0d04496414410b10040c507101d060484c88842900d20f841c1000c0003900c640d0f0700c010040d185035021841c03040d01401819881070000b0b81c0080140020502c140007240401c0c500b42151080300200a9000320400c014001e41e0119406150400308450101c441c03400d01040006040c0d441d948946100741e80300000d075016403803c61003507003010303c0c03181507a8540d008e2102904005d0800340c00c0640d150200070020300402114610003804081b1701c00c007880c260b03000d81c159200003411884001c8900344c145001450004508807400884000486d5079203405107215400d0000d00045240c1240125010a10300c6056000078411405111034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 72653266 1250 72652016 72652039
    0x70e03070815060f04022208060105040203070c0209040314040b1c1104061d060c060910111e090907020d0906050a09120c080304080a03080a060e0714040902030c030105 74
    0x140d5203200c1001000400c4042c50006107041c83d1292604081881c0a4070151520340f44040200c002d2440c0c1646051804d9a03020521160318104003d0b400341030103643c05c40c030b18244100e02500710b114500c8001e01c1841280b00089c01c0622400209070f5110908003034a8845848101d5aa615000b43e0203500300c0412407148810000d18a02602c081c400250001e54036041c10000c044030034104d50345143c0300b1001d0030640300d0300d5900c038a80201584581a03016003001c0c108445100e040a100c44845a078079428246041456401c0e001281c09600e13602d422001e000100054107100c5024900840d81e108406500304556643c02045031040303103c00d03540d55000ca6844d140182c80134014200d0400c0011240541800780c0240c0800c42800580142d010402407907848009600e15032140c7c000b240c0302d4101000f50410582c00001c01604441e8260301809202c0c10032280454141c00180124100014034004005030301c0100b0458000d447c690b10290b60340d107441086003065038020b10070039000d00300b000d20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 72654516 1250 72653266 72653279
    0x1e01030f06030305070f030509030d0c2a05060c12190810031a07030e070b0c0d08011d06010c0f030f0f0f080105040e07050414060a0b07030507060c1205070e0307 71
    0x500d07026298141c54540c00c3c580c998807150a11860108201c050100410000c12103070f40070055490700c40055940c0206134030315441c24040030007400b0540116131340d02d250ba590b00300210701840c0054a170b0030340705240c07500715800c0710604c4c041d50070404001e580c80000d0300300040d001c00c101d04e440320001e0344c88103070305131720b031800d03800d580d2000d912005e004c41c40c01200b0010559003051226400c80d80030315002c00d44000c2100058100352a5030320020b1508400035404420860500c10604e840c2c619007407480e80c561401c07132071a50b20408011003040d990719540010b4a80ea01801d101c405c45600003d800d902c4820624018145442024444000c65040988582c0851213548214100c0d54540d4900e02c0c0b40e442c1c0424070002c0c044500c0c24400384d0081e80c5002c0b4054440788585008090a5000e000445c20701d141802102052508014510401000540040b079000011500d2440d407044000035198140c000c1210720004031040710509908001c144000694005140d05070402d0032002c1d00c094664419 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 72655766 1250 72654516 72654521
    0xc05010507030c060513082803060302130b060f03160e0f030a0308070e030d030f05060301020705030301061d09160e03010209031504020a03081207021b090f151e01030f 74
    0x25070040014080d0621140002c0b200e401c0b00d0b401400c000d01181e00c00e95940c0d20611507030440101501c80084802c46420280851014043e1042d41402c0800c0818115008121882c0d050900c81c5881502c51301d0b25078440d121642242c6901c030300404942c1d1242411a02d0000080c003110740350b8002619488084094604030048000c0648010028041d00c2c949a406072825900289158144414444884100d44051011200c0d410f916540010124480c44810782120400303030402c1e000380e106001c180b000a0000044a064078114100110068484145041d418401c010002c1c1c11003d442c0500140a0303840012500c903420743d44841c1160300d10801410708034080c2800169160f8408241715002c01404038100342c0007400640901d045036281d81f41c0002c240d0200e1190001500e400d41000f449c103605021101c004100c0c3d5500c032024010709400151040c4001c0e2040303400d540f01c08041250f00c681402d41081010003e4588260700c4882d203241d48039285c161854502017030401941180710310803131 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 72657016 1250 72655766 72655777
    0xc042a03060e0103023c010915080c0f0d060b0405041404050705060903030c03030103050c090901090b0c091f030203071b05330f0105010906020c0112020a020a0605010b03040c050105 80
    0x1c03050302c0340a0707203550200820030b00303140c5100010b1240000800000c03101c110301e41c10006003d101c0045108007200004000714855403007428819400b1840f01155a070040b041030300041145620b43d141e04034440c2507102486441c071210a913602c1c00c80c00080301c1508402800c100d880403641001061001d04940b01041403ca4000b0452f03045210300b0b0006142c0403000c0c040d01d48018003200d003021a441400c92440c0e10030303001514141e21600c565a07445c0740c03c4110030392010400b0002d2146070829900c00307030f007010060010903030700c04040f418443c603889603965582040c131040a20358806441c1e40e000b40017980250340c0701c400600064218425414103100c0c981850360301c013000700700f46c86124100481d5040411401c0315031032003054a4030420142d101c6850302500314507510361000c0d49082c0000d010715501d81c0c00541036401601d10040d04d40c1c0c10803240c41801d11201d002607500c075103511049051800b48040103042e1403900c4000300c1c0c0b0903111030146106a10030700090140e2a110001981c0a0054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 72658266 1250 72657016 72657029
    0xf030c0e010803090f040203090304050405010311030616050403060c0e06070c0e070f0207090902010c0516092316030f0e030c010c0305010e010611150f0a050601091409090c042a0306 80
    0x4041704203966003001d50086030b00110f004207590400b074883c000a02514401ea10a480380907440414000c0391406000341904403a04400038250b407030344901c001e41103000d5840050304a80c1c1e500000505903020754036008204100910341980c03500039103030881a0030210b02401d001c0004071000504202e02803245c5605c400a1a002007a2440c608450703040501100d4a0403810031206d07000c1d81e40021010050900c00f404071012490307200303003440151011294808402c2104000703c8089015403240c1c0407483d40c101440c1c5050309220100c901b01039014080c1d035800899418601342c803e1100400101c0640245500e0000a001442703461804a00390f602c01c0c01100c43c4203110b0b500400100d409004407a0103003c2503010358210b05014414144c0c0c5540c00c071988028a0810802c001054145118140e80708030309081070303500b290924045401c22859000240d019a00d020301240e0807142c02c1102d104200380003001405a10140441d880050b075109400d0b007041d171049015901558002d000c4d48040d22403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 72659516 1250 72658266 72658279
    0xf03020d0e240c03040b0a050406020c060f18030a050f16091a0607260a03050906100501140409180b01091109010c110a03062f0304080903070f030c0e01080309 70
    0xb50340d284003000758400c1c282861144000c100004443c6000c402610070300f0310503141c6a440783e00c1c10101074106815400550b202e00420071942807101d80d900142ea4600c541c181041000c3c40514000ca486c050301644060682e11034a101100b409200007854422568065000311304569642c40307260658a807010910b142981203001c1c82140c0c10003101500c5108d01490728200410344d10003040303d8124404504440358075000904922a58160280c1d41d001215900103040c613140441e0318030300c48000e40c020581004005424501000040401c2d513002d040c10300410450b62400031244284809080e201712410004180000f446040600c19072000304890010f240c034008002c001151400007109089400078a0309035101059154450b284000c1c51051100040e0700701d030000c8000361076485d00100075400281d0349492111610010035243c1190384502001d8031801c103140000e00f044040c0d00f00241d03028080c2c00000c24040c0000c200000c44180301c258011f941d8a80801d00d4807807140c0414035030001e9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 72660766 1250 72659516 72659569
    0x301060e06120f010501110c010f0e060c01060e070206060108070903020f010c0b070e04060f0b040e042306061f02030a0804060b0406031b081f0c09030f03020d0e 71
    0x5014040403015490000c02180ca03203400803503040b1084409071000e50011540382d0041c04a560407200007104030903400010200e009500c0002401c8000c001083c10401c09288002c0140d910303101c05540e407554240e0020f21400d51100e103d00707640b0000700c400c4001441100b02065003540210b252038080c3e042035076014a658296020700c42c10150740d48070a81008180e6603024082004018500d00a52465883c1004220540708001c203440c40c81d080780c8801b8203c088200031007015041224100d401c1e5402010303c60b61642009210140021803151210b126005041250b07940803484500c210700c111242900e003c8401400000082c00880f8000503910400403003042074020343c82d03a0f0f88140f046001058242c4110080380c103850583d8030480b41508040c0c00e500b00782c1d15190820015003002001448603080d1140301500342000c0400314103026a499040140c2540b042080c480690303000b03030b0300b01900c454500d4020b580f1301010400000085074040085000d15010f02c1c0326007400d042c5038000001c0c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 72661872 1106 72660766 72660779
    0x7080705150601110c090405030c16060909020a09050108040203010f0c020a030311030603060103030f030f0920030604030e040b01030b03070303030204081e070306020708130902031503120301 84
    0x451501803c0350301800c000317258090030f402162802c601d42c80720704000e8150b101d94440100f0034003d03822140500e02c00d5541d02003c07594269504011381c0e0341c0c0c1d000d050032030041040030400103a500004109640c4a132000c10381050000303000081d54030792040d88204580d0000341d00e40158205000390418160184034000040036040149840e62a1003000680ca81405000003001c1c030540051004002c1c3c0b003940018007503044a601080745022600341400e61908606070b0420041c0311384c05e8500642030101d1010f0049a15071280d041c21840001004060181356811a04060303644481c4034072581e0400407000118080d40b03005a0b1642007898542c01e04440c2e070707441c45003003000c48210940c0e1140012400101c0350403600060311104a450300c04424850740094540590a40002103a4400954011801050010711505900d510801815165001142c0e400b1400301d050004100b035 = true := by decide +kernel

theorem cover : BRFrame.Cov 72482016 72661872 := by
  have h0 := BRFrame.cov_init 72482016
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 72482016 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 72482016 ≤ n) (h2 : n < 72661872) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
