-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5372
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:39:15.542639+00:00
-- url     : https://prove2.me/submissions/0ddeb03e-458a-462a-b6f4-af36049ac045

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 966007194 ≤ n < 966187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 966008444 1250 966007194 966007219
    0xb0105030f0a0f1802030d080c12071b050102090901060302090d03030e0a140d2c0910050613050103150803091005130b040305061e010b0901050c0105070503040b0108070b0702120c 79
    0x4c01c0f0380e003840e00900c02c130200c64898408100807188080180d0300c4001a120910407840d00034228510294000c8030303843d014103940408000700f410403d50100c166100d940c00517070611142007480d40307a030241010781415454040c00c0004030b0010040640e000e004c042e40c0e00c070002c031031240510200c0c503001e070030042120f1121300c001030694446200000f54000300300342000d42c1210b03000c0300c40d101d00e00d81101000c03020105a00414007821603c024140070003084142c40201d4599502c00c040c18500f000b0f0604008100c1c20040090b0898900c200b0106840030110800c218516000080b20000d20301540c400440b28110241942d55005100c6141c20384c0000d4900442d080214202400440b400741048800b02d40b503111840044001741d50021695012103001840703100100c5c001005400303418500140307401712148802e802c5440982c0c92100256000040c0000e00820044490142c64400054400d1510740b1030308240511070103030020300503d2100313558541c030501400309a03146a009040ca0110b83d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 966009694 1250 966008444 966008471
    0x102040501110c01020604140c040603030e0103060605120c1c02040b0706180203070b0a020f01050c0c010e030f0d0504060e100c0f0e012705060406020f100b0105030f0a0f 75
    0x41050003a1400140d01185440c2c16460004003800c10390b5040e0050803035074549440c3c5500c80e4420039542d000300d224200301004240c41f01c0c8038100045010359100100703407642d01c0004042e1843c41d0b01400400c03105000303070803801c00c000f403c050300b140742c05620740d90340c0c092a000d21550781d5901e40b401100500c003241c002228121880105422481648108081c032100c40344020800c0340c1810103909039000300d00501501d10f0305002000c4000071401160050351120880c2c5080d10b0003101c8009158201041c80902c0840901420006c4d00002c0040e5003000e09848108110380102c0000d05800c0b81c131000400c0038001164028901001948150b514075101e080035440076044140602d00055903800710711030740c1c620524600714241816540c190130503008440c51a1020030f42d03008030358a51140040081c650340c426004000420140d009003403100030140002d810002e00030f112035078841c10541e82e0300d040d0382c0c0030003141c0e0700200200c10803019803107401110000300541c00034285018a0710390180501c1c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 966010944 1250 966009694 966009697
    0x1c020306010c080f0d0501120f02010e030c1309050c180c131502030a081005030307080706061d0a050912040b0a0909060f0e010503070e2a03070503010e0f0907060e0f0901080102 78
    0x45d9080c0005208a0b40d0b0fa5540104c05001c81da030207404103883d0b6024400540c4070340e034011900e0000404450441c4080c00010f1a2042c00905228115641c1c1107110308104050110210030b00003200c410000c2001c1006844071260014040028440b00246000006100039610303c0a496448100b04e803591000001075941e03404410715070042020f620018080d804014405400d490010b005141000c910381d0b16441c040d00500000c850060700c6100c0892010b084108178024008200c10744005130601220120494002501c030000c507030824100751200070b1959003250212001d80c1740307599907003e5802c4102d504e01c80d66005500c8807400c21100003059190740380d110b07065801c81043c01546983c0c1e40700f010395805951049080000819002440202d41005032004540f000c0840c25604691050840855030003241c0d0480030070400701c014000c100d80078000503031004481c010300780d05040038800242d5560547c400d0f2400c1000d0031007901203e8940710340c50040c4070005408162a940c4030540d00e4040d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 966012194 1250 966010944 966010957
    0x311030c1b03070b010b0d0f0c091208043c03020a0e1801151503230603070e070206180105070c02090c0f070609110102120403060c110303090a14031c020306010c080f 73
    0x7c40e41810850fa11032911881090401482601c503a84840c0c079186010031002445142904c032484148000620300b600540200740a101038540300c480c071400d8a9540402400c0c0b80c44001180301115010300042e02c4441104041d141d00c00d910300c440e960360000181141c054056900c009508016100c80c0e41417a48480348103a40540283c6035580b0030604046045455015607416a0762a80007650b400310310042040d500310304082c0c10f59103c0b607222000b03564241002d541640c01640510200420794030400c94107030000410400034401e500300107070000c1400b040000c0c003921a41c2441c0109900c4400c1c4c0040790a411011414281c8440880c03e1680c02060701c694141d40e031088503d1040219803000c41c00c0c503c01c9040c031a18034109415611508014108468100d0500080ba030342c0d40380820003080518460380130f10f4020720a5291920742210599004200c4500c154424040fa69451040d818070300710307030284020016280c1e5a4000101d60314102c01402418000000404007900d5403440c004208 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 966013444 1250 966012194 966012217
    0x210405062a1b040e0705060f0910020309040f0626010b27100825050904110a0b0301050f0105161406041a060f0603150604080d0311030c1b03070b010b 66
    0x100301098070511042d40c1000760308200c00d400580c03050280f4a1f0180103414421a00041300f07041440c1000490306c0c081c00d10780070170056400403651904a20b4680941c103801c460402c5c0900800d890500d100c05044079000070500b84150500c0c0e4050745840941c0034941c0b0840c000d25040340740644000e0300102c81403040c4030000d00d001d00c4000880000009658801311413025005040c044040c0e0003e19a0b1541092054000d03d030400c0300251540e00d028030107004d507002c0c80d0b4074404c0c00d41320020400601d0a950201c4c03160041400104000d41c0c0f80b003a0410110400c0c20b20f246c1c0d603000111244170b118284180201560b0015880150f18040000c0c0c05204a00c01e0100101001e10100351444503181125440d510010041140813a42021000340d41c00000742104c060301305009400040854001e50048101075009051072281c4c03a500d030041c0c883c042401c90800341307141803000720034403984584200070300d40c9012100001050321040048901d110313005202180c155071a12282003071035001c16880c85 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 966014694 1250 966013444 966013483
    0x807170a0b030c0316170a0b0f0a201b01020d020f090321092803060b100509240f18150c06150a03150e210405062a 51
    0x3c07114100000c8017a0000b480c13284180d00c66140100b8541464188050a80640030304102000001c09502409010715220800b640c094680554002c040741c031585c810101003481e00b1302d040300203a009422104126440618441c20300e10712a040750191082c0c418551429200040804002060703c01074000354a00f01c06844a41706640148022450140740c4c000745000208a1380d0043c0c64002c82c881d50306480c00395100303148030284041c0c0b941060598400d4602c0c40d254514001c2501d08006c01060f042e0719420000d040003080800306981544020510089100d03581c1003426410340e003010707a03041c0c1a03e00900e603590410b0001c4074141e0b8410b40c0b801400744408001c0c0d420f80000758000d0301d40001c4440018804d07a5101d000c044265503030b00c01a0f07134002c07903020b402201140307030309429121a0078000300c04125044000c0c042e510701040c0b1065001c08030011106960011100d000711421030b40100c1d48180c0b01c0c1c00b007420561103801c89500f43d200d100b02041501d0030464010808003200c1072901c8205 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 966015944 1250 966014694 966014713
    0x5010506030f060f0d050f0708010c140d0b0a0e04030e09010605180f1f170a05060a03030e0301020f070506060f10020c090907080d050d110405010507030807170a0b03 73
    0x4507030100782c4010381041042d600041460030412500c0201c600010f100040b2004591102c604044500c0004025504442c0b001c0c000d10000340900d881c210f500e40b800018241c0c80f038044800c64094200801e4045071603559180103643c1d60500b10001d0080f80100200500302032602900b42c1d60842d45190140f030035400000b501d0307030080041d100c2180c0c20000700c0b682d04c0907100401240d00402043c45c0d9000f841c82000c1c1c038180101c0c04041404503a952a07549910340035507036541e22200300818100d00c0301d05050402140c1d4440d400b21030b0842c1d50504021490860203c0081c0c064011052440d4081d50003140d80360030b000e800194140a030b18255010400c50301a04140004100251620009a440308041e0344a41c01c041072960781c45038500c004d861100d5102c20703500b803c020305e0311034100c0000c402045c0800340c100c0301c0c0f040c00e40c500d08504c03000e03250030300e031000107031042c001c035280a030620001e40d0000d80c1160140380207a0040d03841d94070300c0d450747c40c040c0c941c000100139841c9101d009118210b603c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 966017194 1250 966015944 966015949
    0xf072c090604050f0a030905040203040f0c090228140a031b0f110a08040b0a0c1509140a15020d0902031e070e011809030507052a010302181002012a03050105 69
    0x1640ca0aa01540c401d08001d00744230a0001070b40c0007030001c4901320404504040855110000c00380581880e071005a80e0705d103180c4003000b02d900c910103042040040400142d4a03560454403403040d09281c0050140c556201305415002415042e01c02c2c5019416020b00c5200da50340b010301407642e901d80382c41d500380c5801020b005070f41c1c4400c961307001048650b0401c000d00c1034040c55000b80004210b0b40c60241907503140342c2d43c2c0a841c0074030390201d12402c580b2803e101c03041045c1d1807010080707070751756000502041d04a6186d41040101e6658041080c075030005004000402640098003c0c0780c01504940580b201c401c0c01c1c0c0342d840c2c4001c011078841e000f42031740804c0600311000e8a504880c04511001125550500081c0041c18198811024010200f04c04000140306000710240801c9540440c407445403101c1c06c1503c134410b40c241c040d040602c100808080c29100807050f6101c5e0000703440364030055190650070307401859103403081e81400441c0e50710003030548521500d070f00480429036018070007642d85405 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 966018444 1250 966017194 966017203
    0xf07050307090308091c0f05010c1704060c0e2d0a050a1a1e040f0905040b0a11040f08010609110a050f0d0204090c021b030f072c090604050f 62
    0x40c41d0380041d03606641000810f41000140016403401002403501012031182055500d00d1000b04542c0301c407620b1180000c0c000f088c8250311326403982d030600741800055042c4034038841e200200000c3c101b954a0728940c070350720320803900c29401907005171582c10038151050b5901d001c00e0301005c0c0307041c00101031042c0c12824140815460700b1500003503d080301d00307400c0c200c0d44545416504280342e903541c001d2014000c80c002400f41c00031a403407200980350342c680c01d10380c440c000d0300c1c1150490040b4504180910002914a10741c56034492407000000425009040c100180ea210b40d44c05000c0ea0440c44401080700c24040d80181c0071078072001070400008803c2c9020700402d0140c02c017410003165061148919424039100208410401070740d00500d026210701c903100c00c5450040b03071000183d10028640000b0f0184122001050200324000d0103030a0103505100d0f500c0180b03025040226142050480f0544014205e0390416054190440e402d498541d1090341d58140807903054502d03200e482c1030000f0f0b02c00c1c04207 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 966019694 1250 966018444 966018451
    0xd090501050904020c1516030b01080c03220215210618130516060f090f050d1406042105130603020304051905060117030c0304090c11060f0f070503 65
    0x21a0075003000701d4941040000c0d04242d004c94018041e05048001079050504034134403480c0600d4140390902c1d40400000c04076240441c900f03040c04a60000d1044203000d82d010340c1e62006864002170a6010058031100c1d58a001e66002034120205040600ea03402c86c01d000780ca45581a80d500440014810800e00030103075068607602d4200c044082c51a07502100c05081642c0084c40403e6421107034840c0d40d03500c0c604601801081030390a92503000703201040c2d00c0351032901c2142c454582510302c242800310021010442c0c0c481e4510507054105044104014050040000e0010005484e003d2619041070313070b11504101d0100b503100d0b00189610540c0c84c06482a1036005640d8a0360300e40240c1003102c180d0095101800a441c148a296801c9542c41c0210714500e007002e2241001e0002d0703514200b5000c0082ca06001e460513150824400988031110004c15213003251581034012a440c0c012480580300411440034041d8140150002c102a04c80a4061140207030040722041405542d40e09041315180407d4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 966020944 1250 966019694 966019697
    0x15090d200121020a0c0c06020615030c0f100306030204020d0b0907080c0d1109040510060801171f090b04050303060f04060305151f0603052205060117151302030d090501 74
    0xe0642000d1002030f41c043c118208090074507145032941500c54107036a05461f4480340060707104008005c481c50340c00300d601210400540040c038448100d6800078045002080e0700a00031019004602c480c94400d400400c02950080c00441da0f480440803903a0240442c0500d40d80100c82d0303200480c0d522449448054411400b862100f03081c10030240081d00034141c440c06060a0303200511800710b0ba036603503200b50340c0101e9010a81d64101442c20310007506002059202c201d521104100c0ca00780b0b0030000c202250584c40c4010102e4000410b624900c004260801c0c005d04036010303800411080280000040d400303600c040b0f03660584444810200025520b207404010500d801201d50b20f200303418103490446d0440d04e179080104245182c1035040110720f142d5801a0006521142030103010447c402002000c0d0516070000c102c03128107a1221607a4507018072511410f600070a000350089442440b0421006032070000059140c102501b901002482e8a201644a401803200307001900d40984ac0660840300103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 966022194 1250 966020944 966020987
    0x8070f0503210a0e060a0509190f30080c0105061c03030c0c140c09090303040b0112080f0a26090d0c0804050d0c0816050108040215090d2001 62
    0xb40d0b100e4a0030360071282a400501602011071011540c1d6800501181202d075500c65454411311004c00071402860b085c00320003c04041d0090040300b211207051801d58101d12213058802c42840800d40881d0318140c0c0382e440302080548640200031000000708503007000c030b100901954403000c0c104000300c10349140e114020b404070090040003a000ba0009025051581401e203042103003030315420034000d04000d107140c943d007002c000d0591510701070300641d030030407403130030085055141030740d1400020305042c0a845044641c046401c003c00002c24200e81d1900340c05c0001507101d01ca4503001030310039440f0802c00d5002c0c42ca00e1807640507916081180d103102e501c81800401c0f416607038910588910a0701c07003040d079021004000115a80d10358603480401c244c840c98401c4081c80c640700b0007505010200841c4901300d0a10b201c104560f030303030049025801c0307a0112100f600810800d054503903280b1a400300f56070013940d206542e105200c60a0780d255074a00100801c10b6500021200446031403051404450002c1d40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 966023444 1250 966022194 966022243
    0x109140111120916141c111212070c051c03020a0204150803040b0301152d030914010504020102100e0303010e0a06030510090c050a0e1b0f0408070f0503 67
    0x2e26540700350003401100c1a40c1c06a000b002a8503116205900225062185c50000070340c0c9080519041d014a4600d1600004086882d550400d261a2580342e0920418502d10780c0010100c0500801c419800480d49066a070080c510b000b940306041d80c4560ba1181c000c80441c031543e0880c0200d10780d00070798564051318030302c0007079801c001c020484d81d040c911015000d8200860a00350420040010b41a82d20416482e58900030003000e4114803282c1e020200560740c441d1f40704859150b0788210303800d83c918004e0800140e5503041100100200040901044d04a40d00a452440d040d405503005174000e9007500c07040700c001e1104038140c5d1840345504005034000c10040000c40020400150040e00307662000c91000d95075121039160526105648001e83d603a007102004001361a25084000d21050702e1020fa0b051400c1c0c404802d01100602d500b2103000120505800460a0702c2110251a012a00c0c2621552104103070396030f481840c01000380030185d10001107103610b40002c4030a2202c841e114855910607 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 966024694 1250 966023444 966023467
    0x929070806010f231608070b0a020702060a030b0d0c032003011a0f0d060204031b090605131a15211b0c0a060204120501050f0403080604021305120109140111 69
    0x130921038200740030200078002e40461044102005200d5070051104a03243c0059080c114104080034050707030070b601c6c03040001d400181c0324103056580820041c01c0025441b00c440000c0707a210060703c800146214032240c40030042003c40741e54030394041045081540c12905150605003214801503200310341441001c0e48a0301880c0a0290410842d0042c00549400003540d440c401030360080d400854880300c07118400308002038640c0007140140524142801400d10f070030046079402c0540324a409101d41c4442d41358821075150700901c0d04011024043c2e00d1300005241c41c000890b003000d2038440d0071046110441c001002400c100c0c2c0d00801e030036401400340e071005500c007500c90740c00040c00e00d68502074480c003107010414a1020300300a1402080b60100c3e001149040d030308550004115440040e010824000031036840320149910500558005941c0c0380c02d201c89940c0c04e00382d0351240341c0c0550210089003a07042c06420803604d0501c01c0310400d66540901407111f00340c42080c00804801c0d803052050a00d0031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 966025944 1250 966024694 966024737
    0xa05071b080c0601030b220c030803180709020301171b010c1506120201031b0e040216050f030a0824040906180c031209180929070806010f 61
    0x201d104008440c070340b4408030001420088240d0060360310818540030000c06101c1c4e00b40102c540042090035440c140501c0c1e8400351960698040500110b03804000240780d00c0b00f8000c000c10b00082c0c40c040b41c00d055aa110140041d62003406813a4440701070043e460408080007030780000c40159031000030003080c4442c0045502c80c203101402d0314940724006004401e820641305031805010042a10600000315000240c1580c07100c001c6001c0010302d0b05880c030301150b03010890b0041e40e50b04440141e500e04482403040048010054064038a0013800c49420034104000003c2c03c4c0e40c0d01d07940f54070140d80d40b12041c0506007440105013008821100360841050301d0075a05c00c022041c8160300009429181340101c103150b0303225a000710b5020844580901c148030b80d110001204401a140c08450b0b103003411041c0c01007800f518512111030392601c12075410071840c600c3c01018401403041e032117200502003d50b4000c091040d594400410841d030049416540f0400c4100401c042c1074031407e0240c00c04405141c0c42 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 966027194 1250 966025944 966025997
    0x6060912060c0c1e02010f1d010f0e04020412110906060a120603060504050a03230f0705070902031003060f050103020603180109170703020f03090a0e07050f040b040e0a0507 76
    0x8010103901408001040c40184c2c0c00c903000300303079040140032003944009071854040e24a400c007444030100d0f294010301c2c614209079040450a103005141400884402c0c0c840c00002444254414008a800b1031040c42240da0b800b0028000c0418060811440301032040c1c001040d108650040410002001814060894880c414036200b10000d0226500c1c0c4400c07003140d9054400b06c0315501b00844032002c0c503501c504003000801c0f01c11098020b240c0c010b49150f9080c0706002d00a90031217404200c12091102c107100e424010045950306541d40c1c6042e00300c1184404150104070b610758a0444115402c514610649050300d034058030b81455030319500540d1000031245201d0012543d21272a00000081c100c040c45080e510920f080c0a8440c070742440c02030f003004c0c4080c1c0181e400c0d41c0140b1510605942c0c1c10300d1041203890400c0b18804585451100315450b10030000740d14040500010000741c0e8050702401001200e0b0020048a0300e81c49291250040d10300c00c0d03840f0343c0010108000d08407010102021182d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 966028444 1250 966027194 966027197
    0x30103080f0c070b0903150106020c0d02030a20010f020708060a2c010b031509030318030c19211d1305101e1211041107110406060912060c 61
    0x2010151020b09150041d03e801130280000702080c0100d440c202001a00700041c0300d810070310020341c18400000e40e0f469105102c18880c4080074000010f640303042c00741c0d4013459000078030386010050500000c0c810b1100c101c149800906102820a0040c1c40800d02c642079484100141c01d65032200d0741010301600c9452200141c110b00c0700f603c0501c04415a8682154455060004c100c003994001050f0410382c4480359051040800c0d0304010340d0410102c11680c1c8508a00064180d03c1e009000847c9075010340c1c4071004142c410201c0c810108039140d13080c1c1d220940705610b904a42e24088644a404101420540300030480c802c54000c5c030014949856005540080c0820010260440c142e20540e41d081d07400c42204040004184094182c0f0358070510380344503900310651000d240c200141c1c1c442002107c0a032510305000b620f920296240d401480c00505185a51a12030206041c4002c0400000c41614807c514042002803401d0242a1800480b18401018003443c0040c0e100c2c0c0c4050710702000ac090 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 966029694 1250 966028444 966028447
    0x1140f03100e041101111504062726090f0f012a0204050a060506120a1e290f010302030a02071a04030311090906010c0f0203010c03150515030103080f 66
    0x9501001444500c3c0303c2d0340a10300c2c040e0001c841100250502c551544000c0307050300306611103100340394881d4400343c2040d030004001818920b03003c1c080700f10b21201e4600b16074130790070b030203ca00c00e00c001c1c40d410741250704d03820311040100074203550b01401c1c600c1640c240a4000e0301d403121304009403821088442000106040031890342c2c1405000c0382c152031000c04020300803451031030381c3d00075420f05125660740f183c08074000704242414440007582e54015490000801c0d064600020903081031a0094500c160095141c0c4050800d042c03001c001400c1e0030520081245142c00310308034540c000c01c951802202d40946115080405000110007030741c402880540d9a90702008030900091440c901f02d4160b02c120b400c0744015040030724000b01924402002414080380c103021440391641d5240009030042e00034203054039820950f180035440300c03d07030f4440694594038010080c1481c541541116190354a985d50f0742c42c2c900d89800403c12000c40050b042c201441060005100044510004181040e032089009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 966030944 1250 966029694 966029699
    0x61b12230301090c110705181506030a02030403031406010504170c10020d0909091e1406040506060a120c0b0901120e011407030e0d0f050706140708010501140f0310 72
    0x811640c002c2c2d1003ca0034070fa4034200b0301030340d0358000d60a24a000d444400b40040603d0700340000c910004815400c0c800c1003180c00414030003030028100c0e000140001c0e01c4545c5078584000c911b0000d410880d001e8001c00d041c4104004030540700a9010710890050b100c0d207081c0340c10400e491040c0403c09030717410514030402282d810036954108080031000141d41c002d00700742412800046c080401d40d80700e8807415040140c0c940000d04441c081522200e044a20703501c0d0100b00c0c0c02d207001c1949003c05229070030702842003400300f804004544284145c000355070b90300059540d2000300000c41c03165040030b04880a0f880041c002581000010088542c051600032643d11800e8070042c222507a100240031035030f541c1c404608000349880c81c10b60b406465804c04005510f1a54403091715404030102070401c2110140068a01500690644544580000c0c0c20041055544541801c180e802d8401c5e03400700d0380c20000001e031988200030b1328681c1118446c4403810700003440139080964001406920441d030918101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 966032194 1250 966030944 966031007
    0x901090b100e121912050307080c0f04031203060312050f0f0309011b020604030f1e0f181223190c05100503190c020a170408060f01061b12 61
    0x384084020960507a00321140c6180074005500d05a01c400c041c1b0105208000a440e08815203650120b40d070340496944220383e010000041c89150001031180c0041c2081d940c45039031561040d010b03284030b0b0604454240c0c0882080e01e00e400b482d01c01101582d01046541c0f02c544515019541041c030f808000b148030340c0008034190711800c0c1d4107460b0005034014000c010602da40b1680c0714800e4040c40c14115101c072450203109084610020900080c0301440401c0304240b171064840b1740041001460030034602c1c1d12114103040b00f900d4500f0990f0f000e1110210703404507200b0f000c07860743c0b03003407040c40100350701d01c00108000702e0003c0800c0280c1c5e980030321440000d0b05460b295039445820010365075859691600346011a46010345149242c11289890503101f03459400044d09808a5000081074000c41f1100445400714841c903040440180169028003a102c400d440009058401584580349040350031301c0e45240310803880a0103403248810101e222600ea00400d40e0094200c06d02180310341c81c02000c00b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 966033444 1250 966032194 966032203
    0xc03030307080a050109140c07032007030327031209030b040c2903070e0d020d0311060705071a04060b030d0f110303040b010b0c0f0d0c020901090b100e12 68
    0x180070300440c1000c020070002100600c41c407405011010b4080040c404c1202800c40c1d440f000401e00c031f414120020b0701c0c005150080302044401889049540748550741c2034080c0340c072000981b10032004508560070220f20443c40c1c1d510520780204400c0014529460340c0c407020f624862507640030f024820010710210110b481485480e00c510701440c106020580350a51380c540d00b00b481d4401103100344200c042d00c059449100b0490740c00c8a4a843c044520380b54000008180d50400840290300504000c50300c02055013055000301c101042c5401d450b00c654469009840d14821000000c15107100000c8501002c000d940c0304e903403c28054400080c803041003c1c0400d203044240c0301c00102055408221040c52a401032100b0b05900c1c0b818041c0d81035003025500c800c0011010700440070313070345000b20386071400850811008000802071021074036080c050355009000706482c60001c0c0e005480d0f403000491820030714014081c1d40c14000d441244a404400c0003102c0c0d0f11400501954482c40c1074180a032110707402c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 966034694 1250 966033444 966033451
    0xc0a030c1514070828081602241506030f040b0f0903070f0f06180606090b1c0f1205040609121a060609192c16050f0301060807020f0106050d03030902030c030303 71
    0x711384200c10308243c124001c000302c03e21111011540802028001c94102750801d170200b9012084452490304e03900780200d103040c603000340681c0059000c001c10510000c640b080c1070043c0d02480400c1c001da200c203101c045501a040b203101c11154020402c49002036174501d44104a1400b864584171001296a00c005c01c0c2d800a001c01082600c03c00d40d080b052040910074030700140042441004510980700124420401050b0001480c11040c4041020f0106844c1c817500364070b1780b109210901c0700c0c0b41c81c000713005038019020741000aa500c0c640480c3c244400302c24425550f801140140d040c10258045005843c0001c0050f074001c41c00340980905601c2d500c015040c00510b001408106070f00307110006414828055081c0601a40c054849001044185040745c024500404080c2100041c003003d966a2141710707251100720800200018003240d01000c0e240c0030303203015401e407400743c541480d1407802d0b23480b58011640c1c41a88030b0900310000f4042c0c0d010795411480907003502d42241c030304000641590000c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 966035944 1250 966034694 966034697
    0x9060d021806031b030c07081201150c200d12170a0522110603040c15020a0510020c01140403030b1815040b01020c0a030c1514070828 59
    0x4959041920484648480541e900341c502074110714202c2d5030340402e0b405001c15902500d03c00008624600b0908048071641604074010560392101e201d40d01c442c0324024400c006444041d0140023400fa07205002e540c50b041e030040c0c1d004401e40d4044c9403403181e8043e03500030680c1c0300810104c0c1d00e001988a2074094091111034603114691404c5100011805400600d000c4000c4c0c501000c101e4181d4061a81d440c040c41542d41442082043d840d00d407025940100b80144d000038040100000c120110303060106480c04a10010303c00300d01c2d12000d9070f40f0307180448000d20541000c0e01c2008030071820703400f6004c56070400001040c1c51914001c04803d040301620150300085d11100c604446050801c43c20603070340c20600c80039403d894950b0500741d6420010100320700c190344901c0708501c26842081951050803000b00241c08055403450480101d0b6060f00c0fa01c4842110128481401409510081243d400f805000c5241591035510450342c0d611403032030007101050034046000c000c001d0300146076406005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 966037194 1250 966035944 966035947
    0xa151b02071806030c0e1b0f0702040b011d12030702130b04060816120201030e0316140a03020a0b090307050313080115060e010c060f09050109120e0a030308070509060d02 75
    0x142900c0c00101005000321003003241c01c0c00000c000250a003418001110f842e011191140d403070720050901d0310380014212a5a107075001c101440385503103408c01072501d24802c403010000141d1103001500d041c43e0041110039a031702003130680c0240d420030058643c5100c0880307058a10300511940051000340040505c4100c282d907070740070452142407610600d0080c0103400c0040c0000504410141c5051103e80560000003e840c4076030011a402034100361a20700c060b0040d41c0e00c880b03414500050741103d81d5020f4a540c1d41041c2943d10520001c2190246182c140d40030b0f142110035602c46400c5840050242c161501c000c1088a0100300c01b84050300030201c4c0110035030019440c00c0185c1e403e4a0980d1140d0602031980710341000b40700c0e001800001c00364030a08052401000c1400c03c0700c01044003080110403141018084010480d042d400400b44a2188484210340d5090745421110984181513040d040400000d0610110f8020f003011580000b0a152040c81d040c03410012130714641007005081d011b980c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 966038444 1250 966037194 966037199
    0x2010306080a081e07020a06180f061101050a050105061218030a080f010b040f0519030503130314070501081b1603050901023007020f06070b06091303020a151b0207 72
    0x10740c402164124003d58403d9805c0402a400040b400500c80c813900091164081411614040103004c004c001c0001d0404020465615070016122000282c2102d602e9440c0c030f00010f10b400b99900c0750f58140c03400544120b0420340c110919511440e8081e20b5003400d40710b5800190303410f8904100921002e00503540d08009420202500d01b130f0f0034010703004660340c0d401c1803105002051440b00c0d02d00032554211040d402850240964084483c0d0a41002d0014040040c0c00120202a01112800ca0b8031460720794405890b0507100c242c540c0c1c0c0034003c1c0f034006100b90b00840c102c001460101c0c43c031154030140309440e1440329079110303a000c0f090282c2203011a41c00b1078618035543c2c042c00900112400c2820380407070f008a0b003140a001c0080c194a502c0e0708480410351034259101c10811441c2203501505c080d40c0ca4845081c0920021400c80b21603200c3c2c542c94000898200c0c50705812a0b0003503150f0001c02c510346d1640c1d60b582048181c0a88081d54603501c450700d64101d900031604000950a035000f0701200d50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 966039694 1250 966038444 966038467
    0x6070219120c0e0403021b0f090106021608071a07020105040b0a02060402040b010309170a2609011503050601121a0a05070e0109080a1b0e071e0306120f02010306080a08 74
    0x4081c2c3c003c007080403008080101003500882c100b02e8030aa0700c040e0841d03215050000136065606241c0b11500608080000f060241d0001641887d43d00441607604d96642d949130a90341d1800e80b4012450741320441d900070f0b0820b810720700151410900c1410550704181d11f80c0c1617500d458100303d60010060340844248415400d1620a11010801c2864140f01810254441913011310301000e0700418010002242c3c4a128420014186411032090902c0c40c00140083c011002d02c2049c0e820311019444c02c080411941090300ca0107040f254041c001d440303182c1c40d107240c0751b10304441254142c03070103031503a89040201c43e03182d0300e5a40b040550000000d43c03420300c9000105036400400c020740c10311820107000e201c0c290000544d00f140355400070340b02e00e04000740d000b10080074403540c1c0542c0c0034a007e0001e1100f40d49e000054030fa424901300c003140424900c0407004509071502403090b60030100a03480c04101160000304a42505801130401150182c0d0310078560b40751081307050090b80c81c6580030411440c103c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 966040944 1250 966039694 966039713
    0x151b120910050405030d0f110d020a0c0605030f07080912070506040b1014060904021909092307110f24010806160c050109020d030305010303110610050607021912 71
    0x49880b032034402d0400b42048003181d40c1d0a2070401c2c50052060b507507170050050348100313019502500360702c0c2550404c003519800a9a00c00040c081200c0c1c00c451301001040c118881c205880c40340c800c4090082ea19100c110003a201a50040c1a15242c4c1c083d40c164164104a00c000501d5044d108900919032840d003820248142800608111484010b103141001290910300880c016901d0850f4603039a40c103149000200240b02c1c000700c000006d50305005c001c02c56034000d0790810844d021250140701040e5441020b180c88088603002c240105441c0c0045000300b0301c2880803180d80107251044900010440a005150490100c44003060075101620448601d42d5441200e00400c0c400000f00769605084145803295002c1c5038440041014034100141401000d402600601740c001d400ca00c842140b90800a0141c1024001a404100301e200450203110001902a01c07400840e01100591414501000095030010b0001d0780d002e012440071400440900c094040244840403413181c2c01400da1905500c130 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 966042194 1250 966040944 966040969
    0x102070303020601091e060807050306180d08060303070b101d09031219110306010801080a020d083702010615050f0304030504150804140c151b1209 65
    0x4642005a080000940019403903054540e00600031a001c05200640c001004945035408061411b280300000c0c0000e010640b070060f5a800d4068800c5940e50550034500c0c40c0c202400c1c0411075024100500b96584200100354200310014142d1346056500d40f40c2c05540081541c103040c420350380680401440ba200050800c0180341c060940015140480d41e1680700e010b0319a075070003e50720190028001d246230300109083c00001d0341c1d040104400c0700740600c01a0b00308440b05030115003614004a050724000580d03400c5958001d14100d191200c60b6598815a0030044c0e05d031002c2030507050b20801c00503090710300d10510031200740900301864820b10000c0c04d40301c2c0c682c0010150710000c2c0c808040d46034031400703c500750703444441065030706d440314a01100d861259070710068000b80d07200204003495500000b000d00440c0100701c0d250b40040f0079055a40c5800c1d5285140740c1c404500e8240d03181e0000c58801030030315034450600f0212a02000c0e40040c0c100100c2030032440065200140041d41c078a00811050070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 966043444 1250 966042194 966042197
    0x11010c022d0d0804120204020912011401270f0f060602060604140601140a050405150c0106271505150415020c010c0809030120040302031b0a05100513030b070e01 71
    0xc16002910355400510440c06980180410751701c202d07055465940490303619170700c080c4c4903600c020b4031006810300034001c150396512549000400061000c2555180c2007130102c2d000c41510121810848140042100c003c1d0b10400d5519407592a80508480c403a0000510f4660045d00b002d1500386c0c1000300b02d80d01a804043c0c1000c0100c14401e099038084021101904030400c03da60711100b03140183c400303004562009622280c01000305920b542c8180c00b82c02c4135400000280400c1c0d0301c465080080113222180d280c50340f07240350320480c2c118481782c04c9003408000080400c005261642c02281300c0141a42102010800005041012204848481c101f1040602c003505907041c60000082400e5000303180548004804650381c0c403d070b0750a501c0310034030402c1e0300f120361884020b10644840d40d800c58032090b886801958204880d1084032801010385050081000140505150411a8844096200e0301c01c1210030320103212444000036000010314041d82d550032a61500c600020701c80700a6041450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 966044694 1250 966043444 966043459
    0x7020f0616080403111011071e02060927070f0906020d0f0c1104050a1a0609061207051204050703021221030c0c07380711010c022d 58
    0x12078860303009403019001903243c40d00032080803220341a175103090741180504540c0707440e1914120241d01848010710240d80300d07125103210300c00304044000e0300420b0100e020390400c2d020041c0c0c20b0a49801100c040c0c00300000c500802d0080320343c03502000c1041c001c82e1081c000c40c1403451220005604260380500030051403009054000184c0310003440300110415201c28000025079081c10030030344c800d40d04000e45018004110610740f23142d500003e0580543c41142c13a000d4081c140c4c041d41800812552044400762075146000f400c00e10100f00c1e441c005000608000b000d00c8000309420032002035901407406030f80100409415030040004101d943c0c0030008032a4020f048140b0000414060030030072428180c1c0d01030b1259980c0b8030360307680d43c45039402003000e5028013080400c0e286d6605515651085c0145103035a5003a01003039584041a102000513044280d041c40003a0006d070354461070310403914040c900000040d400303a002c41d056400c84c1c0410540400405c589a41506c10303040c076044640e1040355400c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 966045944 1250 966044694 966044731
    0x1060504180f020114071a061905010c0f050f061812041520120408010f020a02030423120d020f03090a050f0a0b0f04080c190509190507020f06 63
    0x180c02e0038040640241880a80150303803009640d4541aa000315801c10402042d01030806414515842c003190014451004103842c50748002c0f0001202d010386c0c1c0103031900418070001c1d0321000385400d91113208440510440b0500407840c0400d0000600603c3c0d205aa2648203286100c03850604190800d050a0700405001c100031240c1c2d081550803255649041c4860070048860f98101c0b003000146082c0700501c500905031b580c41e440c81004104441e0003000800440740220304c0b05050744900c02104005a02c180010f1000c0710ba0030305e40c01c072042d0311181e091481d21400000700b0000b8481d804840895040302c80c5242c0704e0340d0180260b15030525184055443c044030030380011000041030003070320300031603401e034039240039466090824016203c80124580c44040c4800c1c804820392007070059102c1801900762122442c04e280e180e40d40c40d05840040d652182c0d007003400303200c00c4942c000d0985850f030036a40400c64440e2160f10806016083e141c0c05842d400c5500024580740400150400d20350006901e80c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 966047194 1250 966045944 966045953
    0x100b0613030b0615160b0a1a010809010e070f152307050a05030f032a0703050d0b18010603141003241b0e0121051003140106050418 58
    0x15105595000c840c008403611508003291600010462150b03610303c0c00a176180040458401007488240305024418981d603e0030107440540d040355504100b08410360a00c101d10b9800795007040e5004003503400010305120100c8107a0302e0040c0700e910061003010480d1041c844611000303c401515065414010740c07000e449420039001c80710f0980c0303441d44c1d0a4003107145010060144041c1c02c1d0550000308894035240c3c2c0141f44182e6130b20950b499602d10725501420503001030200e04e854007000c0302100c41814045079403000d882d80d5005060088046680d10b284004030343d00e0016142400c4140d0045c20711540c1009806011209610002c002040100c020021002a8880c021090301e91005c00c80362030040068561038001902c004c82c00e00ba50802c992712030b800c411280254120b2003995038050030411800d00540b51010f0b180072001340440c603440c9103401138210350000d075000448100004007095894445000c00c805104034580d0a0f5101c07402080b00d450980100d0841e55200d0041d104501d56541c0d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 966048444 1250 966047194 966047227
    0x1209060314061c0203030708120603060411100c2108060d080712020106030209090a05010b01080402030307170f0d0e0601051f08040303090204060b120a020301150c061508100b06 78
    0x202c61041c114003030b240585940352076481c00e601c3c0d405404c580e1030344a00e01e046800f0b074200c100060040c04880700046c6003441c0000b4050300581d00020b0700710340032000400b440b00d6100c0c20880042440540d2068400140350166019035124210584101c03036100e00c0c00041a140001d489a03120311002c403100b8010a006008030f581071503000d6052240100803600990242c8007a41c4041d610007080d80410000c0400407889461082c4590000c01943c006200150340004066030042e4140d0300c18000c0000140f042a0385035040f144c010081c1e41010300d0074804003010740c080350383e00b0502a21600b1007108440c0410901d4007400084a1f184441c4107488107030034400c0d10140103031003041040d0020a091602030b81c040480e258000e00180700b40c80c6caa00307031110b4a030b0154000c003246110500c00034804003014400d80c0d040c3c50350f0003800004c1d5a00010105c0382003408150950b60300d40d403114402007111400100d0380080200b40c0241203800054040a0304803141048480c0c000c1c00c080012100c805001301 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 966049694 1250 966048444 966048451
    0x105090c03030a1d04020f0c190804050609030f240f04080703080a0204050402040306050405160b090d1e0c152f01090c0303030f0b0402040e0a0b01050c06041209060314 74
    0x1c4c10b02e0007142140c040384007510030740c861140c000d8800240c0c012200c0c019001403008201c0f000844440c5240310342410800aa482d00140032020140024071041c0fa1080040c00b808000a0440318110345c00d40c019030410081c00303580d6036000e01071a8240c4841200c21041c2d0783c00702174000301c04550714081d19220704603ca00b0f03d00404110303c6000007451103610303078162406020007800440d00c0319100c8c07404000603c01510b00303403602d1261602140d08900c012140c40c080e140010b0301c2504001200302030240004d02c07008201c0e10f2a840d140d404408801d10641c081350180910007040304245405685060884d14081c0e08003000140d896650020a40c00700302255030000c1c2443c82044035208281e580100040340000340303c1642c00320300005060349904513920460390f02c1e40401440c1850810441240300d5445401c00d40310201c00061144c04055102e182c040780103041a502d06190781e0304450a1400840e0300303c3c2c2030920f8403081840c2c0ca40c048800d41c050041410300f0050300440c48890004440700a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 966050944 1250 966049694 966049697
    0x6031d060f1314060f0f06030d0e040509030706050c030a110a020c09070e0d060b090606040f140111120409050f06011d011101060902180406180b030304030f11030105090c03030a 78
    0x11101d110401c50240c0310b030443d100d1038100380c030144d09044130724004a42080d100b24884101e000041006480d01003154081400b040c0c98203420700b00c8810a200c0602030042008016000610502d40403400c0b038040c5922662022112650743d15200e400c0704220780c040741c07422811071806e1200c841320300d03000500c81d03203080d5045030200301039a100c0c03900f105d800d00344494460300f1241c04281c0030301704a52a000700211580844104865036142c42c240080c90196220390b8080e500f06079403c0211495514035402e18a0040c5811140015142d104a141512010300c5010301003002a007003158001922031079820103000508001e01d0b080c450002488404801c41031000c3e4690003d01c012941c1c059140c5c0b80ca840c280000a02c413166683c2170300d5000390422241d802c03608101200351100c914207441500d095030014901a4044200c03c0b0407a002440881d11041d0944000c00c008008141c1141800c44868030841c00c141041250500741401e55030301410a5140d80d000760309518071940d011060b52903003807a5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 966052194 1250 966050944 966050971
    0x10b040e0408090409060b041407050d052d09070e01300c08070e0109060819150219110d02031602030a0f0507050a080c0d020f061306031d060f 63
    0x40303007400d4810b0b1042005030f81e882803070080310004109190300700450b40c1c4000c413810020a100d440d0030107004c04c0d080b00c100b00000d408200080010119030301c401d400c5403109440300c2d19000c00d042c0441d010000744541080e941095070402c090500704000703140141400a92414255241c2505042c902c0000340007150b611840265190420102c2c110020140e5000030710728454a984128054580f141800b468250b400301c10004a6161604d00130352044a400000900c1200d502ca0102d0200c010104800c8130754960240c2c0340c0c2c4802c595400034000440300900c02d00503002c3c0324800a403100300058004c2c505a0402c1c1ca03101245038000c02a1401d500c0803032402090000240f0009042030310b8548000c000d040c03404101800e100b4009901c100752501030720101d00503501d64981581e60380d158541c0135805000420344100600304000c10401e0760b803010b8065420008103518000c0058419006100000c0e6140d40c1c003005000c00e4102d0b0036107914848080d00d00c0b401c5c02a0421480300f0010b00034000c0404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 966053444 1250 966052194 966052201
    0x314010c050d0b031009061a01020f030304020108042112240b0a03060314280c0605161e0516060903020607020d20030d08060603040321020a0203071406010b040e 71
    0x80c207201d11010424405d500700059021440c4c00d01c010400513401c481c11100d4944201807075400060180100b1907448000d60030f40c0d903660300440718003038020700071554440b2a42e0120400010008c0380c1c1d034200c2c0c0c0d039103401c04d0070200d0000100865911180304400c01c24880b0162040c18038040300c14042e1910b5010480e80d0760390320704e400d0b000707010541d1000b45007078a04000e1201074040454941d400407001d209246900e428200241c1c1c110400017805800c00f0410842001628001d80040c2814055140b0860303808041c0d880d040c07001107008a0003440d103840d03002e803007041003018851240f0501204d00c55060950600f2001811020940002030140c0c2000071007205541d200c0b8100c6044076807018000c0039401814040c51315843c80c1204143c00380c0304034943c514415000750700c03941c881d00001d001c507819039440c2d403030440e24030a078a0800551000c4407001041042101d000030038a407a09a0011980e400241c0b900301e040d003602100612142d0801001446000c640c14111002c54404540c1789000d41ca = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 966054694 1250 966053444 966053449
    0x7081302180a060b1305042004060503130f0308100504230c0705010501030f11060304020d0f111005040503070b040501020712061104060c1505010303050307030207030e0310060314010c050d0b 84
    0x14032900150b45500e400b24200c205c02116020329001c0c0c8500350760510100310b040602c0e011030b484400122807500e03c00d0000f4070001c2e00c9500030b50792000c0040b80300588a0340540314640850300e41c143c00d800291106d420001605103500408000b00401d407400c2000e00c00300c0340701c0100980707101394800c2c4807840b0308085294080210240c41e0a0380c7c100000304420359481c5003042004060000484258802c402d071503400f03103001d005032480340d0380242c010805600c1a6030b0f0300c18000c1c00240b0483d49403090442405480c1c454495a000c100c51a480ea01c0c1e8490400040502d050100e42c040c1d000c0314001c00c42400340f66070115850040301c021003682031a003002407610b100a460b003c461403900c03503400300780060581c0d403080c41c1e400c1c0c05020300c0742c0f0241280244103880988209020160114104101003818907200fa4010901c0f680280b400c0303150100810300107800c10582d81c5050342403540303a4000344103010860304c8411084100780001c005030002810081e2060048604001c002c0d99900391044064 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 966055944 1250 966054694 966054701
    0x11160618030c0b0a02060921070f150b030f01050103050c060c0319080114010f0c02090a090b01231002071802091012051e060d02060c030d020307081302180a 69
    0x842c0d002150022258a480c0120400c1d08800c00110045c0700b180301081b60704401103081c0485010320382844642c040a9003000c40c031980030072421103030f604000080402150085e0822900c00003c4100840c00401d020101480c00c00a61030304083e592600c001000007074800601242d0252050312400c4d140c45048134194254024260b04260040103014003400e4142d004500c541626560881d520182c603c03200112441d60544d242800400c107968501000341c80e082c03100e154003c403c030300045182003580d6034030074038541d007a407051071003501c4000d00030083c1d01c800c0050a05d40704152145402ca40c40c80c00c00941d5000c407440b491025080c00d0955241444403601255490b2601900c2015140f40c0203c0050001807541c4815030740e545040045110506d40203081c011140b07407072400d404c01345c581204100301e1006260b0120303400141041302c1c81ca2044c06102401a20111990041e102e14001c90081d01182009110948000321002c0f00c60040c1c0c1c6d00065042807448400132142c90b0b0b9148007640005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 966057194 1250 966055944 966055949
    0x1030f08130305060103051e10051504060b18040c0909180606060804050d1b02041509050f040c05180a0515031f1107051c03020d0204030c0611160618 66
    0xa0703214a040402404000a07103141240e209008442c85110a2400b041040c0e0010410400d40e030041c000c1c2205c0f41e074454100e19004865103c1280407034912000040850302c0c154003200784202e020801d150070742d0481307450028016081e00d0920003040f076003070010701240d9103014400e4510b680315140000c545001c10030f82c0445030300a000b00301c45900c40c100134005400403202105c440c4a4200140b00144c4603160030b03110a84007a0003001e5071111542044080e2841071003d03080e500603039100080c00e8031180600c0e402950039041c40741b41e60400b030526801079130042e0840c9001d071010b0408410f00040c51301d030301c0f540400b03254800519912041400840d00e02c0c0a1011a410f1284410210580c2c1036010107244d8019620001c12400060f5062408640a100c0c80540182c0101c0340784e01c03021014a000340d48107107251400520b845080d0043c01c049030002c0c0c0041d01e4044004a080c82005d4011715900e15040017070006015150b8090741740c0303046000d94001c0c48104282c1c580c0001023080740700340c003601 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 966058444 1250 966057194 966057217
    0x10b030730020d08091903050d0c1b0f080706051201090f090507080c12010e12070503041e0603050901151502100524090103050607030b1512070801050f0901030f08 72
    0x241d560360350400741000c5e0460820030340704011401003018001c1c2400f4100701200d071f221014000040d812042642c483d40344800c161001c18000c4440500004440b5099025058a01c41c111070142015040c501d01641ca400c01000d1100800c910b00c032489025016034116044424049401d4010500d514040c1040e01d03801480c9215082c1c3c0480d88240c0803411001c0300704240c41448403442450308480c00e80b607950030201440d4000f102588901052034000300040c60140045070301c1c2ca40d540440d503220b054a0201c0403030301071050350107000c916454051240c00141d145c00a2006a030107110310f01014480f40b0800f611102001c19074440c00d4000e00403d2007119614108005030300d803040c042c0c6d20341e2507442c8070001c0c0f1a48000000c00c442ca880400203060f6900600201116617078130038145c0040c411210315580c014140c0c00034402d802203090040c0240c8603501021800c0f8207051703c020301241d2060b0029489440da84882842035190103c6050450350040301080b103c90302800c1c0f10740740b88241605c1c0f04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 966059694 1250 966058444 966058459
    0x9320c0d090b0a141b120601031b0507150203071d1504140a0e070f031a060307020a061b1b0c051c0b01060c0803180709021308010b03073002 62
    0x3d003030f0300c0742d6118800074408013504181c0750761000410010f00101002d51800c68400f8001c6058000c10b42906550000f01818009058802803840c008a8000c0c1036102002600000b403003010801140d8400981c14500141542542403010000c2c001e8001d03ca0407000814034200511300707580e0f0308982c489241042c0c0c40080c1d034998a80c208056422a40d4221034000c103080400051000c41a03200d6510031129950f41c042ca5101207081140503091001c40c040d0b008013405101178043d80c03a10300030b50007070300c142e00200310b8680c061820304280e4261f4210050028900404d41400507080b6504240801c2c041015400075000c6180a60300d441c0c142e0001c5070040c0c0342c1480360398203000b10b10900c2501350080c02550f8550380d031400115001c008581c0020003904042c40820899041da450381680c90490f04161130003503171500007050880c2c0001c00b1441c001196000e04214911080c1319102d250741d8190041c2005600302940c48120303900101c0700309500705209948000240d4003103020712582e40d00900c040f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 966060944 1250 966059694 966059701
    0xf0521010807030318060807180503011109091303050412050f010c050705060901092301020d050a0c030b06040e0f1906060201050103020906090603060417120109320c0d090b 76
    0x56594042c03e000132030200b02c1401009800203140548101120304130303510011156250038080711281006092501c5240782c1c5500414141c1d000e0040d551051580c1d071450b51034280031020080042400f9003003a2400a868003000003080d4030104441c2950100d40c1c2d4034031000c1407841c0c00c91420344000c0c0b06c032815520341a0a14905540140101580c500582c2142c41c0b980391121420f08803903503a40000c14041d180024650740800c416004a081d0080c40c000604040c04140054140e9804490064900341d0341e01d85500400c1c7c040c0b1544200350001c0c2e0391142403900f0b000900308000310244c4079070030000742c2c50000354090f03484a031100fa18200d881c41c02c1c001c07540c1ea42e00280c060202030100f00d20a5030000f000450605041e82200e00c074403002030080c035a5444940307aa444809000d00804810081000141c8160001103030160080c50610400a51404c41040c0603141d40400e010101c0c44101100248020308141100310740c2180d04049850350b03e20709102a60010804800000c00000b0503d040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 966062194 1250 966060944 966060959
    0x27060f0602120406020c0f0d0f060b100e0f060c0f0d030204060207050f0d0f1704080a02040e0604020a1a090d0303050708091c030b0402090a240206070f052101 70
    0x4050440d1030380d030211405110b025090803030b2400340b802203500503405180c4044192038280b18060b4042006440d4440c0d420007501d86841c450540300c0b00380c81c0305c0d4951002c60720a05103003480c01c0340800c8600d4140506105000041d030541010100d05114090114040089180900c00c203040080c0b06401c80c2d6019480b840c0c050041d4015100e0b8401500404100003107608021402c0f81840d20000c0c0810980f1a290791101c0e032154003400705880040e0452509502c5203c050018409041010002e19015100d80b0402064422f0003d034205660400424040141c40d10030060050710b072480100d2103544908124040d880c001c0320012548100307250904006d05170903030700803070040b0f0b90f6030ba03070034159624103d40030b03500d00d54454065440e1046000d2052041e100ea480121104001040540780842100003d403c00c00b10ba04480c24542322200d03251034204051000080c4020a0b0010f4200d074038150314041d000c2c2b0489001102880070005542001c00b5035420044030000e1804000d48855840303811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 966063444 1250 966062194 966062219
    0xe010323040213051815010b3901020c0106091104180902031504060b0909060118020f0a021612241b0806010e15030c0a0c05030d022808012706 63
    0x207071000c1794010301c0030322030b11116030301c0f041c5060341c0c0a032001c28a031548851800307150303e41c100301a112004000540d5040101200300b0b1100319400c0200160700c030041c1c103040c42d00b1034005500880301c0514240380340804030300c3c1030107071411201c240100301c01c0341c2d0310300d001c401c0607101c2850025803500880000c0c210303400301512490701440c0a48020481c040010040c0301c840302081e1880c0c03410364400c00041054260303100909003042c0d02c000000d400e042d204820346400d600302480c0000980c101c24800e1010342090b0785423400901ca0021000030f40e1066860350700225101441c028000140350700080c04901c80e03074229114420048020203078a404030040207000100c20740d0a02c1c005001c0c2c1000030a80e141a003000b0340c026030350300c0c00186181c44824100c085644905842070500140c9001c40c004124203101a19115180007405661180d8011a55440303030310f0200d44004205007125091483d51380120b00a0560700a105040a121000d040410301104003130b9642c0c50081c1840340125005071100c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 966064694 1250 966063444 966063481
    0xd0f0519031d1f020901030e0a060212090303040c0302011209150b010e0102030a050426162105030a0c11100504050906120d1b08030c03070e01032304021305 69
    0xc2c52101006a00319055202c100103000e01420f503801e64203074519904642e000f05203003041414000f402003ca24440c90610390301600a0750100d41c04a82ca00f184c07821010500d0303019410320080d40c5107141a950307815011183d4003010b030400c0403031a900311111b4282d50080c09aa42c01c2200c0720060111010802c000d4030380c5e14101070009214410300400b81d400041a60160f01090b1501b0742498100004071880c1551304610350f24500040c00c00325500081031180da0407034001d4004441c842810081c410070800201d04400d8481c040d040700ca80041a0044142c401c0000d807407902c90114810381c1020031b411400319074071030f60000304c400e80c03040d900380c00100400032900c00b515440102c1c1e844108010f0b03441100700c0c0300c103100e0b004003480126051040919104c0441d484462410080d5140c4504015404c1102c4c88030740c00f540041840f0b200d641081c54040c00d91300c2445c0038024a03030040100c014040c00d03040300350034909540c0c01140845d90360f034041c084944481c1350202328a1810710441d507122000704 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 966065944 1250 966064694 966064721
    0x403051b010b130515040e0c150a0207060801032102100c03060305060612030403081b162409150905030f012703020601031103030c07032a080d0f051903 67
    0xf0070030160300e911030040c60701c564440702104c1e4024100200b800301070241905038001c1d600070002c0c0400d0319512880c081c4c0038080103840b50341c0c54910380617000e86404e00300e4001505001120700100700040180e107010b11308805454021039031207000401a450308030068202c241490a00d000c00740c07495850ba1003401124000c40445074507031246010300089141403407d03501175420401050000c6040c00c8010080050150b03c6540311a409a24a6080080440200300c849607410f80412841941c2000c3c4018041003880101c0445038116024120104501c5001060f5242484100b5014052400c120050401805851505039010489802080344050100800007c0c5500301084151002c1c05084036525800401c1c42e6401e54843d03190b51104489095414402040700d104200d10502c0000015880346520a1351943e44013001002208003040c2c07404800c5a16100308982c490000d181d00c0c040030281400908844455801c1714144034000c1d45544054902d01c4001c1c01d594164043c41c140200c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 966067194 1250 966065944 966065959
    0x2d06040605090c0f030d1818060302130506010c03030e070306020c03041a0a084012301407050a03140c09010810080a03020f06180303040b0403051b010b 67
    0x1000100054a10300300c81480d016404402d54110703041c0107c07210000c90f001d01c25594030031960f030580c4003205021114000c2c201c9856000410442c2401072100000c12400b80e030a012504c0c0c074000081850031140000303803c16031911824000d00c6800d001803005190402425135550168025503590fa0b8441c1c451071030a030f204a01b10303107410b8075800140c40c10b080d030580d1420601e84030202d4258008215680088049e414401c0b4074546140d00440c070a04901014468000c80c1820f0a00b50840c1ca90032000d01c060204201700402c81041030030415501480140e005500d03030107081f40440080080d43d0000310f07180501d20500590641080103450501c140d40c1c4c0a10072551244944011000d085e150015480070500c041e19466019440883d4890215540020495070301c0c140c007803508010900130f40c0540c1100e04000b240c1181481060352101204c000d0070078210f90b0200c0039650388001040a40650f4115000c541014440d400f05d4000d0881c07204d0a030109444048058024180c03607900d40e101d10036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 966068444 1250 966067194 966067213
    0x5180a030315050603100311041503050a0201080105062b0f0606081803040609170c150a082401050c0a02090f0a05070e100e0301020d09030c020310020c2d0604060509 73
    0x42020440340700390f10410021b40c08624503501c1c509038001001007650301a031039421034150850003c11000056000d0300003000c9840050001502614040e0000c9019000800400b998040d192580c5c08070300d010410b03440c07021035010480c4c01c000c00303c1804a200c600c0c1000e6002803180e0340324601c80e019004d0b514010303069240c3c2c0c04480355a03228501c986000314610b51810020100c3c490341c01d050031320380e983c00d8400000340d220000c2e010703a682040211400701c0120b4005510b03179008454a50120001602d400b5100d440040400114039078608603042010000d61046055014000c032031006602030a98030079410300d14081c07207c4080c100d4200212508d440001086988200c55003141100098042104075840400480c0c2e10000402d0540d059902081031189062482c410a443e43d03009030b80b80344d41c2c2c0d00d00f44101410041298407000400340148800181048042445240085d070702200d2041030390341ca200c1a8034054002441e4201e8003550041000b446410f8100341c0c82141c0c2e0308240d8a8040303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 966069694 1250 966068444 966068449
    0x120207060507230c09090d0e0618060a05040b0d0606030e06130b0a0e030c0c10020a0b1302131a0f030f06010e07170a0906061505090405180a03031505 66
    0x10700321010780300f98030300401448580d03118901ca281c0d102d00b000a4800310b18001c008a03860324010780320500d680e801019100059580040d40000c1d840d8101c5141d480e1503106548600e20301e02e406040303440740400050304889140600100e5004091070740b10700c0e494600181c00307003000b031030320348074001c0880d04010455815020202d41e05204032842c0d04009a9026503458800e1201801030091201c1c0f982c0c0c55600700000002c02c09080d801160030002c1c028102a1030500c1110701800c0710600c20341d4003840905000441c03055405a0000310b00c0c0725911620000c2c000a00d210b800c0f944110307031551a0036442c0c42001c4407481e4101c0315036006e8840e0304d02d01d5240c46c103042c1d0391f40301d500c002d96603900b0000c010f102101c8910306141d0040014038058030031940b41d242c28091f1941c2903640060f07070750790360701e102e001c11225002d010000d264003450344070310b0400d1940c040c105120381607103d40310395520000070b0a484100c2500405803c03028044601420700741c5000f0f0020010340341d060454411280d80004d040c17 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 966070944 1250 966069694 966069697
    0x6041b030e101118010201020f0d0e300705030d090318051203091905030d120606080105062b050718050f0114070f0206070803070f03090c0515070f1202070605 70
    0xb00001000500c1c01c510640c5031031803a1038001e1302c241195020040c400a0406030400340940003008140010504007507200180b030000018100e110180000950503840705842c3d100303440c0c220034108407680e10807480c58100d0031485030710311103480c091900540000341a40b10070203022040480320072560483e240c004010f1008900300281645034004c008192032410500d4410500c0000c450606a0b16038550703000905242c5400100c070700060404240e440005c465002c0d4000134407603400c0102482d41480c006c514075124486e202c80041d11184101d828400700c44c3c0d400c90500c80140e4040160f403c010000500b00901540c080c070207140ca25501046a180200c16031810242c140c5405169150b4072a10002c107801400701500c2083c4100c81c40405a140d0400402603103101d020030b40c0d52450003000c00303411520045000e10805241c010040002500c0481100070307035604a0f440d008038035040c001c1c1825031068050040941070900380d0a810042032600b00e800c240740580a45000f42d44510003100c0d00e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 966072194 1250 966070944 966070961
    0x60d061401020f0d030b1504090b0907050306011b14061812040509010509092b0314070e040f0618090b060105030f010b3a0b0102031c020306041b030e10 67
    0x3a400c4100c8042c01070b03003c2c0c0c6c0201d5103144040c2454000455460302c450064105a01c040c0e03443e80c03a10421b51207413070584a250391085417420224214109800001c0078800420840748005a15155a03070501039020541c1141d2109101260f0252620702d5480840400062500144d0300c034500d804d104030003103581501c094501c040c3c4a01000d03840c03c0200070501402418054540c01000040816500104040292408052010980e4840088000b000c4846203403000c0d05904201060140c43c036405406035601080840e00850702c640c0c084c06401c01402c035070384040031050b040e0580040748400c58000317082c4607001c0c0c41d41480e19520000191480d06c400c44e46001410400710041c000110254040d0500c2e01d294646002c902030b201079550055000c04080003005d000c50030314610829030b1130140c1b0703c01d040284041c508041c07040a10b0540c030555130713003500140d030707001300c00522151500c3d44003c0c9031032081a058008000b08080142c02407142144180c0c0501801a214001c45d40c9801a44e62 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 966073444 1250 966072194 966072223
    0xa020f0c03030732060106020303010e0606030601081b04050414060901080106050a0611100216050c010509181e070503150306011d070903060509010c09050f010c0f0f02060d06140102 80
    0x107211038484100a00003518400043c01134045102c900011302c1041054080c05071074005623980c1d410000c0c401a01d5600524692082c10b04000b0808181da2014803950031481000010700e649803003440349422030046400c1540c119281030075000301c160140001c180542402d4031000c10301d0341ca032800c1d00d00782c94040c080d09400c0101e40504112517441440380084180040d42983d00700e80501030000d05036408800d10500702207000c0000c406100041c0309004420209003891441d001082c00031601c1c0048007140100038040300f00008808280c2080d401404943c41a0117200c00e18220102070f00d260410356149a2040d00b405800303005060006001d17058408045140400502c126a410001c0c40001c15520400c0400301000000419500030707135008842850010a111492800040501d05654000c92044501103490b4240da40c2112080e0080b6410130b0f4a0010f1003030034208055460a4070030029001100050074541c1102603030300950a488125200c401008070340001284c1d81e5820850503103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 966074694 1250 966073444 966073463
    0x12070905160e0d0c030b01090902130b15090d0b0901020c070609050a0b0c01020c1225110f030712030215090604020a0b0310030f0803100608010e0408070212030a020f0c030307 77
    0x5420f4039058007410074a5200d00c08900e24541c0342d5a81008490303080e846004002c0d182c0c43d9490452400410310340301c16654a000704000c8400d03800241d22062403c2d084102c4000015900007907484440c0d018400c69001140801e0500380062064002d5020380842110340c051418049003162068104074110f9800410010304503080c081c0c00091a840410540c00c00d41d42040b010349840c40038000c107a0051488403a8607110b60001d02c1424020300c0c40310011034108100401c20b000601e9006043c0103100060b981c03000241c81c910040f91410040c0d410648101040d00c3c2c40d2010517038001072030554002c5031400300310961107102c401c9654410a44009501c143c01c0700041c0400704d50b84010707551185120b91281d4086540340c0380c0c03044880c0c1c210707000d07292502c0c00400c001780402506414001850350b840c3c954110340c0360640000310a800940000e18902e40007070280103558070b8001c00302078000c100094076680e12250070081d6991840d400400014043c0c0c895169581c0741c048140c5180a400c403d001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 966075944 1250 966074694 966074717
    0x15020601030803131a0702122d07080d09021309030e090a110705031812070608041a09151612150b0a0809060a020403110f0f1207090516 60
    0x8561a810081a0318040c2007811344042c003242030b540261100c07070710f00d032806202820283d000030f007041c10a000590307a075202049085403001d072000e40301c0364000c070000380b01c41c141c8110846008140300c2c2c1403024001c2c03080495000469200c650014900500c02c90b0300c0e0700d4030104071602c281503408103074000e03000c00d100c0131070944c0070309000d241c1981c0f00c001007100040115550207611307541e4008103000d4070035503c0410400d00d0118103c016502003141103600b0011181107070344660341c49046000c1c010401c4040d40100d410006e40e0100111003444144005205103005206280e440d2585600c03801e08820540204039104201e020302141a011f507541c0c0301e160010b140005000d402c2051a00070720340000c4034001910b40c6600c2c06805030109030340d2802c0c043e0408400a0749000009411002443c0c4100010400905001110000e100d010b60f00b401a14840c000060841000c00c01c40a0300607900d01d0310032201e46e001040038403e868000740104110744440c442c041070b03606201c911030003091414214 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 966077194 1250 966075944 966075953
    0xb280807020d020d0e040f06080f0a060e0105091f1413050d0c1509020d0b09030a080c0406050715090611030915010305060601200321010e040c181503050304050a1502060103 76
    0xc2201080d684049155035a075801c440c60700e00b41c00d00408413500140017140170010354dc0601c0845806440080c0403d007811950340d80c032200c0c200141031002c88200707000051090341d0b402c4910b0a8141d00d000c01e81c5482c0c060000d8a00c0180c4c41070032280c90040c2e9000d85d210030f018442d942002030b00f011204061000840c210001084582c502b079a2200c003022001c80081c002001c0700344201d080401454071544503620103032005001404031200074105100034401c0c20761100070380748500d40110042000050030322048005051504000d00a542091002245108007000441c020314101080b00c00303200c15100d480300142c4082c000103140381c00c040041841340d0f1081031081c100045401c40802407600240c0b07403901d5948410f000340b200007401c0044220a21943c44460300509190025000c0c51030181c0e9030b8000341d00305020702c2c0381502190110701c41c031000c41d0b800b5407940c058025809281a4030380c1052681c9410610031076105000b8224049811034003541c014468111030f400500b21642995078 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 966078444 1250 966077194 966077201
    0x6020f10021303020415031a01060c0227040b070e010c0f02091f030b0601080114030604031110150f0909030504060f1e0f0201240b280807020d020d0e04 67
    0x8400302c0910341c4400c007002603902c3d80b185074024941c60640c400d42e14618607112207409906100e1510f4860442d00401911340c000360008483c41d81160722038408240f511602c0441407005045c01440c9200d241040200400031102034060b0134241c0350801d1132240440111200d8009120041007440126042c03001410254171140d00316064040c2601410a05140c450000351203038801e41d04142c00c14144081541c1100b01e240c05819010b160100d0110702001080e0f4543c0003a00080410084807114000c8410070300c14042c04080540e0180700011401035403043c208154001c0014a500441d80040c00c02d4103440f550403007a80c1a20749c3d80c201403a014041e01c040712580e010306c0600103c465464030411762625001c0900302c6c3c6403100a0071110f0b0705402400c407900710540c814110030064020403655401d020380300031141042800da9403120700d0440d4002c54410542c4460f5544140040c1d01c01c1c25411101c05803048146900710303040c1d07104c04081280c1d1f42003014200d5012440e814500c103003906041c3c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 966079694 1250 966078444 966078457
    0xa150305090c03011104031b05060f07050c06160606080a170c011b030608152503020c0a050703032c06070602070c080105071d0f0405090a120804030906020f1002 71
    0x1d0a9809156690010a0944290340180040c010001605008000e40401c01a0001c291303100151070240c10003001c0b410394440c4140c0c02d160100c0201301c900070810100712415407002c000d4a01900d42c6000c40581005034250395007103e615040203030208050200060271220f054108014910703400b00d111868a10b82e22401900e000fa5489071589102c6c2d00c2000c241e4041d131a00341d54001416490701d00071070700b131501c811100c900ac2c52a00040c4003142840f0881d010f1244100d0781d510600b0350594806400074841d011001c041801559821003d010000ca409001ca9000fa201c0030000031805c0322100a01c046d040c074001c54078441c0036110126040100140030300520070f0700014581401a1514074040c1c140d82d02c180e130280c0d1520204840c6581c030002c00320202c81d28000f084c60862021001982d083c0c540c40300c7c140115603030000600111000c1100711489908420080a04c000100c4001c1c01c0000440c0c0a0300805c02036a000900c903440011100020128070001c0d04032803201040d404041d60254 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 966080944 1250 966079694 966079711
    0x20f0a08040c270c02011509050601051c0c02070602160e0709032307050a06080a0527032115010f1e0c0c050a05030717030f07080702040b0a150305 65
    0x1801c0403504815540d0314400b80000100110070f080c803400d4280050703c00d003251020840e410708400a5281c121070b1030758010303160544c0c4042441e07692440100c540b4090000340d0010040c102d154603036896002d6000480c031180780e60a0701d0141c0e407607001c00d03655456103c1644030101c017104002c001100e41d5401ca40c1d00000d092800c0d4110b551ba940769104070807041c942c5040d08403400c00000d03241140030000350303004050035070300c5050107850014003900d0401d0007820711003160b0b2100d0002d03d1003c0c602c6122102100c8005615140c00b07040b44c0081c1c2c0d650440601400c00c10958000500041d912aa0203441692480541d0940e10018801140c089641111860074040e00c41c4c030305110640c03284850811071246c1e0f42c461210000c241840f503c400c2a0364045e601500d62400d0034040c98a001c80d0312002e4602a0700c104000803120000603280d84100101d17140c4110f4042841f90410030f41100801c1d60720b000300d40901c140e050301e0703041104800f09885040d010503e460f0090400030300a8000340d9202e01034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 966082194 1250 966080944 966080963
    0xf02120a09080d0c0f11071d060d0204090803160e0904060f090c1d01091407140f0d1a0a0f06120209090403210b030a020d1e06021c020f0a0804 63
    0x1940380e4003c0c4c500310500d05001c5403210401c041c0141c0e20501340d4400003107410060103e640307000b0310395007189982152000ea840b501c0f00040c4413501e500c01d00441180d40036108108107443c9060514098106440d44030303c0c050078841c0501c44500c942d071524542c581c024006001c40d16140d980800030540c10b803041e070030f8640f02d03400740700890207146140c4020000440d09401c50007100c40d02d082c0d0700c2c40c160080b40704945440104062402600152644200582860296442040c40000050050216079036814000041c018110001038001c440031079076018000c4990300440080004e140b406004810b120700140c0410000380e0311407c1c01c0403801c5488a0018900b046043c00f0034940d85048074180c0100303a118410191840c1c0212420352480304a84040100e14407400000b6182e045403c4068800c0703200010070f40501003200740d00c0c0307810150410000500011442e0107030103504170101000d003406030195501128240c03802103481e00c04081d9015403030701c082c502040c3e500040c090425510180b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 966083444 1250 966082194 966082207
    0x152803020c16180f0f15050f0d051c020a141501050103021c02160c0e04170c06010302060307050c0115060f0914040e07050a06030515010906080f070e041a040f02120a0908 75
    0x800b84a80f20100603046d43c00c0204c0c5090800f400300c0382c85c000c1e000500500c0b4180e01500456004a4840b002d04009000708140c0d0302c0491089146c0400a940580380c0305040d40001c580031400102101c0f40c50b082c40c101410b50f030303a43d070054049004010b00340080b00b105204500d01040c99900904504480e04004800c90542c1e84401504001d580c006240740c00c0c1d004140024002e0600c201c200003000300ca013039483c2c19900c0b41700c1070303c900b01803100034011840400850941030042d400d0707500600c0d4100c02000f44041a01268080d15010311801e00460a20403212000510884201d02601c42c0b0003038202510041c041400001d1a0703986001c4614091081c0220302d55034ac3d00b004100408460750041002e04100942180340c0000083c1d05050002103401041090b8101404642c0720810031410b41003556940010b5400c1480e10b00010350052038102d0b04000d4040d441c070905810502030780e0800c01c441d21f00405204a1064070341048100103c140024000000d41d04514407040c80b4a02c00d50a021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 966084694 1250 966083444 966083471
    0x303150103021603050903511e1b041e0503010e03070c05100807032408070f08010209030a1b0b1602130506152803020c16180f 56
    0xd80010300b140080d03000541d821540c5008c01c80000c491505918035104071418420b8111000300c104801c16051002d5010300f005003001c0c0081d40b4030131aa0280420642c500000c0c020050081042d4680c480f005c10b501091003100d1058201c03000d02c2c181e580c007034a040c2c2040c2d09082e00e014664655246c0d26403804c0f0100b402d407028064280002020002152100341c0307450b013012849070b0354111501402440280302c44240d400074040e0f80140082c10001400451035400769842c94080210307140417100c1440000f403110001034003004071107003aa481c2400741c2e00c2c2e00c1c2c136500340c2c403551303146039850351150000d940070410000002c14a000318800000050b6510408420182c010800d000c0e1004001807807282075080030f0b42c9001400f1a505020041403500344c0c0050f50344a00024142a000c1c000b056410a5075112510100c50340d8900110f92100c0307000c408020080d52080303041c082c56000b002c540c000020f928909050070b42d5200d01c0b9442c050071a01d80c0f090001c0a58115600d940794031384940c141c00e138 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 966085944 1250 966084694 966084727
    0x905070c2d020d0c0f140f01082e080c120615060c060a0915201806040308031005011803480f0b0d0b012010050117030315010302 57
    0x14450713480c0140f43e80c58140304500d4003400e90f000c0c2c6500c40c1e80001c10f8000707941e0790140781103105007420807003501e490b43c0c84c4503041c401d901d42006c001441801c4180802140c100300c40e5089850301c038103c42c02219980140b00d00e0340d84000c0603282e01c2e03100344042030242078004140c1038810300c0139001a06200210548a113000000d03a0a0400150340d802d1040038420040a41e50000b80c83d0be50501003a840d0b101340300b5400301103058403020003401041035200c1a800076007030002e05000800003a100c580701c0c20000c4117517100362401c00d2606604000060194001c03d000c0c40407066800c82420150300c0c640b00c084101c090343d10400c544c001c0c580c1c2d80e42d8140049004000c0022107400c030340e41480c41364500c1d103640702e00e039038010814525007414104100a0404201d810600b2406404a2540301d0340f4016128205a041901016050304d0002606000001141241141c5e850000e0015903070301c81d00c50006491001e14983d050300204001501403140003042c20211006141c01072500d070108844042c0d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 966087194 1250 966085944 966085969
    0x70807050c1309050c101205070905030a0309051804020303030705091305070f1107050303071e2a052202070201020c03032d0a050415050d060f0905070c2d02 69
    0x207030b0390740d1002103003805003c00260078042415136078940c03c1803440380054510303404500305e0603406440c0c4002404680c8544d02c914020704014007110b0854500340b40192031003210f40145170081c1c3e40210705520101845806502494004d0044c1d0703c1c51310f5080d802c688a501040c101c82e00408070a4221300140407511071140700d1140c2d651140080e002404006295500c401200d840b16070001d00305002695000c012030742d401e68840d82c40e070444014022014111042542c000d8403280c10841403005082608100c403502c403400c2e00359480c0e010740311000c100383c54030128040084240c4940f10500381420990041c0400c0d40140101c500010750940003d20b15444040c403001c12990124091550205030f903001080465480e01c001d040c9141c0c440020150b0140b0702c50000c45c00e0300b0300c1d1081216402617045800e13074510860b0503c01c3c291560264500718015100303002e01645020001841e0f18401c80d24880306640c05066180b48020b20002d006000700c0f4960900c4021060703104540050b0380d40114003c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 966088444 1250 966087194 966087229
    0x30b011d0a050121050a0506010f0503122704090b0a1509090203060a02032509050f06070b010506030a060918020f03240705070f1a0705070503070807050c 68
    0x400c0061402a020400015000c1280e160500005000aa0803100f003041e981d404009512100794607810701d585010300c401809459809031600115402142111450946009408a80e61140d0481c1c1c0882c4500c22401300c0220070720b00340350101090b03c0b000603041a2400041c004a401291511140941c081c290784480c072040d9603180000b018010f00800d1002041c45240c10014004540c01192311035800a01c0c02c1c140c0d543c00400074680d0110605002400e1520a07515010741c410032802820560b40c5001c3c03a4410304003c01012a14039010f8100c8160350381c45001010103919000038010709400c0034086d070641b41d441e000d010500d00424407401e2018241c241900c00c4801c010300501c0b0f40662851042ca000750032003071042c00c07201c034050214000c00903542d2418009070344221046a0b40e010f10500107052907030507451081030190b038628500f5142d20156200d0724980340d441d4160390b1442401001012a00184032a002180008015040c5140500207842c060a005400070f01c40c04d034411078091 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 966089694 1250 966088444 966088469
    0x4110d0c0804021e130b01110d0507030215150f01050c01090c18200304020d140303041704050f0409020402131508010504140f06032a010810050108040b04060204030b01 74
    0x154070300005000030350000d000780c1481c0328880402040343c4694014480301c411780c0303e9582e030740143d01c225400d611948c1035005456118074a071100074241d900c0460705034010f1041c0d414a210303c2c4c2e41c031592240108145200040e4002c000d5061210f0311130003a40c1d0318180b140c01d0200102000d800c0c02402280da206550a8850a007855a901035011070100c445d515540780850300c1105003103880d104004407400182482c0c0301d544510005410346000300c0010102c01d814503000d400d094000000c1c5018138800c502013a0840e4016201030500e0140744110340e031090718111804524142036000384202c44c0081d2002d03107440c0400e403103030112006903171100603028014040002d01d1903100500601402e0122414049186550103413642000f018200d0014810550081000742c0da081124160402d0344e1960300b9010307404040b00d0580c03042650019808a4000303c00517140742d2016400c1025180d058541b01c8003601c032a1504a18003200403c2280c034194208800b001007030b02c0000c540d000300312009981 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 966090944 1250 966089694 966089701
    0x7170a0f06080d030f0c0c0320010c0804140606090a0c09080109030c0201110c0904020418050607051905120412110f061e06032a0a031101080708040c0504110d0c08 72
    0x14201d80c504820100b055141001c5100c20030350101d034000c1c5264142c50124000d0382d030012713800348c00c080a5a0180b425880d2030300042546030040c003124450360091b0070340044440f50700b4940383c451508941030341d40070720003000040c028411580503183c0034401e8031700410b259880e4040c0c5821108040c006901041d43c0c59444130842da80010084001070300c110281800801e00c90101e5004180a40024032454136100520068605900305401c46038124045403241d0500c0000980b555112005001c0c07000c0510612041050189041320240181444800400c0c0c2d00c640303590201d0311001007200300f00f004006400038140410406075a100034007202800031410440407030905200ba041c0ea034582070b503940f010802d1070343e03010404034980e44023403400405130b0702040464190103a4010002d80e011003400c0707021040c0701c1009071080703410710280c032007168070b49400340d0a40d8a00c0c02100c008151601403c4144001d04044d040401078007400e495090602c4182c80c2040161031405800d90002109030040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 966092194 1250 966090944 966090947
    0x110705070f0e010312210b040b0a05061204050712120f08010815060a0f080105090c03150a091511030615040f05060714011103091507170a0f06080d 65
    0x3100010074908004001d014030348031250359501c00500c000791045818403c046401800b0343e520701d640311102d1b14130303e8143c01e207114080c0c001e0018000080c0038602c1c06c610365440c0e04091032610242c507002810340781080300d0705050901c003d500420842d10390007003a400241099000c01c1410f00d051103001440c04542059000030401c034440851001000b5080700104504603022804401d47c004c0c802c50115a0340e240d4001c240c164417250b002c0300200400440015001d60306602c00340c05141100c0075078008140300d80030035950708942103540d04050783c010003040e50120700358000c0344000d02c5000c002607420a05541002141c1c0650340420741c0e020000f04100b894945a0030b5424040300b0007074041d0034507007007400d41034010f03a10b0f02075a40500c0d40001e140043c003c000c52811050000303407000b40031000c94014501610741094070a858548210b01d1842c0c8200800c026070f03442a40d1a80d80c0e2100c81d808201038040300403000e4208003444c2c4d0b4505600032546900d0141c040a490584c00502102008040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 966093444 1250 966092194 966092203
    0x1030b0708090106050a0b1b0d051b3c010507090816030b0c0a1404030809010801120b0a0b1f030b13060b122203080403113409110705 59
    0xb119030b040e45000c106005c1562080f4843c400d641c01e540380c0d243c40e1150790302050728182c0d0b513980c0302c0030074032038a02240201759108006204442141014060700441d08030415956800f08a0b003a0f400000d4103460304000303170000190070702c204803280705030300250303802c042c0608490098840e400051603090050201ea68100b0503141c104000c9081e40a00ba85151122007026038003910624003240002441c0c40341c2072244003a0b440317200701d05820903a201c0c0e40b85484022540326001c0680403c07001c0340001518220754025003121500450100070031381c2c40020440003881160701e41c55120344810317490b20180d0350504104074101da690301d0004140d6030140c1042802d103032800c0d43c1c26800d810000180800000501600c00c0c1d20100c212843d0603889000003558078104140e40361103008561072540c0700345540025240d005d5070007602e0700204103158801c010307240c200f0b6008000342d800040b64140c1c5a00303507130f80300c3c07408204e6550355042d61301da00c40d02500d0a40d410b05125030f800c0100402e191007170000a02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 966094694 1250 966093444 966093451
    0xd06050607020108060f04110340290a050a11070f140703120e0f04020702030c0d11060a17060405060a0308210129031e1e01030b0708 59
    0x440312810495107500007081c08800525036400344941d814600c1c425210703a00300d0030340c0070140c0d034a01ea180d1038101200804011562120289a0740414088445104086007504034030306070141c40c5c000310090740b62200710381e1000201035040842140c90905018540c81d6460280d66402e80200301814540205425613602d61111100544100540d4001904404014454682c400400300d40e05996060750760038100280d00c0608809154240d02c0780545c0d00008404130400115070760605036011909100482c024608025003542c0002c0745942c441c6030401481019510030310403003001880c2c42c030115055801101070040031652a00b01e038030020800c207046560100c0152001c100925184000549071400d0f444041c05115002485500654118100000031b8103075005120203569640001103c1c1c403c0b46500001043c4c40600146040d40d210f0f0480c1c1c0101102c80349010110b581014880d008400941001500b42c1c841e244140d403a40200b0b2400d000b0350260b41d004500d0701e00140c01500c0f4443c000c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 966095944 1250 966094694 966094699
    0x7030b09033714070b13080a020d020d0c020604230a08010b04061208071412370e0f12010f0506120303100b0a0314040c2607090c020316080d0605 64
    0x404000000385104410b40703a02a800c0b48174490b807610f8001c09111a02012040176106040005110259503000540c07101a00429805c585058a1444e004c80300240d1407100290310403c02c000410802258503032040005201080c00c40c450021000018000401540118080c0c0d4544245d000c00c3d00d4148290300041407140e40c0d407109019131703035106c0490748124400207010204054900428607070030007410070300074145412659200354000440035821051101c1d4500c00c2140b0b4101032411801e04c0100c005455182c40325021421007004000d01822042d0030140c01080c1c140922880900c240100c0c07402c665030110000362800d0010500c031100b244044d07074080b01d6000f0010b10003032242c2c0b072144400300e86011311000d0301e60040c048200c0140c01841c1c43c585607e00000240b200b0720a1010003401226482000399000003110040380c0403074280c1000c800c83d107401001d010020301c440c680004862082510641740f6010303000b290350242c140018025101344c00c0101c1c1440100065128540207070008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 966097194 1250 966095944 966095957
    0x211409041b08270c01050304030c0b2a07020a061d1302040503010605030f1902010c122109030c1b0b0f1305010306030b06010e030f10020c06130507030b090337 70
    0x509150b0355844c0701204850420200000003814103121b0705007070708080d03800320480005003000300720800c0420721081c070000707400010a85855403c3d0f50000320f50601e9405001c2130101c7c2e251490076503440c6000d041409150821003451462a81c413083c0d20203a1604401c1e0040e15282400309141c01c541071034120364029440010b905d032000e038000401401040140004a110122520040b200b8881070200104000b02400c250115203800c0002d040245821140000d02e40c0e20282c0008c2c00c0d548840800780220300102e0200011a400201e109130902102801c00358880da00c100001e101e40c400d1010721b0b0305050200d11101c02c80680c04403031000b80401d180c24000242036071111420f08001038000c0e414031224180c0f521543e1824000a4150181c460665001442005c2528080e501408440d802402004001072150502220354000c8542080c01081070900790f80e00c0c00c1001401030b21140d07072440b003402002e002041d40c00c1c1072946080e12070848a40310340c00144038601d01440c9490a0140241c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 966098444 1250 966097194 966097261
    0xa1d03060702100e1903020307021008010513021b0a0f0c090501210203070315060f1e18020405040510050301050a2f040f06030207211409041b08 64
    0xd0015110641e05409040024008010503500b840c1c640d500550811117079025140e9400d25170048041c0c400c075030081d1080546080742c410115012a000d0085a92100f0141c0d00e03502c030f0910903400741482480344150051507182c02440c02c2e2070840032139001ca03910302c1c0110242041141c0004240c0017411000400d01143d41007074240391003201e90008034000300b041071000c00255a010056480115003044010b01101d100e50750390000b500d52402965209609550300041c1c600554072110000d0b02d2007001c90500c5402c1052407040b404540504942d1640c081c42f010400713595920620b4044c0d280c01e01c040c41c02615007020300d800d403840107090f01105807404808000ba030000700d00c5c07042003841e051041021034801c0c1110300020f0040d600003403008140c3c13100201c0c00c603400d94000c01c1e2103070041d02600505545800204c0d5907084100174400020101480300446a4400c40500f01103440103001040741c80350b000704842820a100c0d10440050b1040050044e031040c400440454950b0381501000440e8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 966099694 1250 966098444 966098447
    0x2190209070309210e0103180503030412050d020301060e0f0301150501050c070b030a0b031606020c1c0203030703080a150308070f050f03030702011401051e0d0312020a1d030607 78
    0x4010a41000d01d600c4103c42401c1010110701d080007003143c0021190007000d4480000c01001c002c044a5001c00c0c9130036210f4141c000c160800f40b0001d03500c407000b94a141c2d910303900c1051500300036101109102c01445913186000550001d540a003603503a0f0741400300c001b50020020611211a00c0a000c0e0b45010803c044450b0011140307001d469080c2840d81e0b0341d5101614151802400341c1c02500c0307810001c03007440507205040c3c01051003044110704892100400d11000c5865510b5441600d001d0390100e5034082990400450880d445150003d1450035031035280c01103410340c2e10500e0100c000820400812506543c80e102c3c0c11050740070045a10000c5086035502e1403103102d00340c006420303d1103415541c420098200415114080c05609a0317484e42404400030740a0440340c100c000705a55150700118050510080440c0c804140a441200e10490360091250500310030205504000300001192501c040340d00081241441c2a0788000c04c03090381c3c82602140303a8890203128400c1d0451800e10131041d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 966100944 1250 966099694 966099709
    0x6012403050c090d05010b1203130603090206130b070204050a0b0a0608060f3003120a020c1c0507020a08030906071401271b210c05120a03021902 64
    0x2801142000030352612035101215880c001c18001a40c44051503540000f006419040300321030110a031461001201d802d0006a100c0c01807003c03107032031084a080e0410001d4401d40101110b940045c1a8600e000d5083c0169038501c54141c110380082c19000070250f0440c2800c0c481c10b0b0388581d100c1420003605541c1c00c0000e2907188944a002c1c1085a0280842e200c1c1d59408025620307808000d0131454150240d000c0400002003c0d01d00350490501404c0502c0e00c4c41021040720260700c2515021402075480d075910070b009404c4507145066520a0140320f01c00002e03801580d50ba03400480d05c940380c0f41d00452042140310b0b5043e13040603503190414025000b0f6521940162440268004240ca0307103d05440100c41c0100809149000e18102c05802000918504550540305034000c04904c010bc462080958240d10130911625041000300c128000340c40204c26181d900f010700c200c0301181401d50700d40008003400211101c030116078210200c02c3c001c064040101220b036000d24a000c4e00c1e86a03841d00040c455 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 966102194 1250 966100944 966101009
    0x2090c091c15020715062d0509010b030405010f06060207050307091407210221150a06141c140f040c03020d060b09090606010e03032d2a0601 62
    0xb9950045000d03030401021340d000c40049030701408100007050359040080594002e0740248910085074403048060284104218015107901410750449030f46440d2007400290f20003401600c4556176881c815400c640280600001050b056006007003039130810342092309182096201100d11460400d58080d25041c00500581c0044142845100e26142c140209403030f005000c1100c88151000540e44c8005185100300e4640180710300c01d0a50036580c9407100d800c00c0846045040e40300b9565141080038a2043c80100a1074403481d45040c140640d4120040040304454008110710341c68900591407121444580c2e64442d0704c0044521843c141511402c81c0c286203804041d000b14405110302c014480d8541080081d01d002400d051a03d14004a8454403032206444130342c002020506640350300d180000980b404494000000802065102501c00c00005c2050b02c3d004480c106000e02da0021840491400710004c1800550559a05417202c0c98201101608454080c0304c40814500144038441d01c0b6196 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 966103444 1250 966102194 966102233
    0x6140712172a03040323071a01140d06061205061819060c17040308090c030105190b0a080d050c0129010c030210060f081b0906100c02090c091c 63
    0xd0343e0b113031400c0484907a0b8100e41d0408010800750854050003000b54000c1c010785000f41c2c0001001d440b92054003603229020b00c0b88100000481c28010000e10708410891045881024001021980c44403800130841c00d40805031072a800c200200808080c49000400c1c2c42c1c2000005060781c0119240c1406408500f04009091607954000306482c640c0261005606070000e00c0700788203103182601d40180315900441d20030300303c2d008003a1605442c3c101401101d00602440207080980a0008851310040c40100c0f007540e84011a0b5000058626050064540c101626a101592104015055401e44003058240340c00036142c0e00703a2000c0840c0700080540840310074644440514102d081c12480c289603000c3d40c03244035141210000f19034580709a5a021110260300751100480c80348000c04015003103c3c4843d0308010007900160306842c2c517000f204030951041c10188069a101e401141e40d159088401c42514900011103036034070700d001c2c0c41826281001c4160801c5050080d49c03507034040d0343c00f03004451 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 966104694 1250 966103444 966103447
    0x170a0207020910151b0606170c01020d0f0c0503040302060a08040b1602070e04060e07060e0a080a0f0204110f0a05130e0403210227090606030c0406140712172a 70
    0x220b0368154000e0f005074240c11060a0100030b8175005440d5100c032000c8841c186d24400e999049c50b0950004c500e2a07625019600c0d509854180700d0380655541c5018038040340d05020800001c00107a42d1345019200445195995140d90700e060302d049000c01402a0240451458140f8000030303165001500da42990351182c00c07000700e51503134a86003000d408451303102c41c01ca001d420307004584d00340c0c840e1140d06029000c84940300c01a40d40d07200c00ba1101c14440d80989460000c80307124000d0f0034280c004882041282c2c407102d07e080c6005a507118282c102ca031265000039800076071112205090b402d110054422455044094201940c01911800b0032801d507440469002d659180d030050705605444054003160700c4042070340d084503810301007440303541c2c0b030340d4480c088a1001c50100d0030f0040a4a1140c030030000181d150501341101600e5140030160303240d40d0340d80104180c0c00041d000007140f009104003600e0700401c501c102c444284442000510034200015100500509400180c01c80c480c00fa00340c0c1641e1303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 966105944 1250 966104694 966104717
    0x50f0106080c13181811040c092417010e041a09030d0515030f06041704060f0509130612140c01050406030b0f0405010e01081612060b01170a020702091015 68
    0xa40103046203040090101701c994000e202145204042c401c0f000c9400700010741d00540306480b1401c0c0c50040d03074001c040320b0318500000002c00020045034009400d01c462042446000c104081009803c91018500c41000b40820002007a03002c00000102c21003144017454100c11090f03981c003444090703007801604c81010400c8582800040241c05c0c0c40501a42c07001c6941000c1c1550f100400c4e00c003107071000212242c0a101c90010410345060321b8042d60ba4490028200900700c4694100020203680102d412508031000f242611550008100c0000c031011401c48900300030040d000481d554020541140c0c0d50816981c1e44801220300b41c031410b042c0003501c000728801144c0480800e850030f40d0405d1502c2c001050100038080600c0c100d5042c88111101c0700d0f000c60804661040d41d100f00300d60f1400d0140c0c4900015641c1d000b00126000600d0110480c6060a0100303071000d509603004000694002134080950418143c1035074040220b1404015941c40c001d10204101040700b0048104100d00704407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 966107194 1250 966105944 966105989
    0x4020427090206180f030714060c100510090f060e011a0729100803040b0904090614061813080a0c2a17060106050a03020c01050f0106080c13 62
    0x41a500c0740c020706415103d1a0560007001d406440389013462040705810340c072000d00e181c00a102c006441c4a10840d10241445406200c41ba400082007100d19000300750710b41c43d006030b1610500e8800c1c1807003c0286000c0e86082140ca044a0b4184050703030001c0e003001410321582048a039011b044507400c680402c951000110240c0740380c0984e4400a000fa18015400d040849071112807151401e602190402c080d1641b50840c100d4041d584a01e64180e00709000404c020f540000150079400c501500108040300142d0b00d020032184a107441c1c0d2814900042441038508268102c00c1c01e10251902e01a40c0e814003040c0c06003080c99507480202800d400040000c2c070b080c07103810342044255002c90701040c7c2e500d0308454460510b82850042080403a580030000750035031010014030b00c41c6201d4001d0465a42060012105507000492110a140d0200b10500c401d00003481554070070300d40036141f158103505011005006c28000352034013940440a1244111041074540c2420440751550300b40d084a0104031071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 966108444 1250 966107194 966107201
    0x2401060219110114070f1202030304051f0e030a0f030506012f030f19080a02030609040609050c130204050301050106050403171e0d0207051e0a0b130c0b0406090504020427 75
    0x102111803510200d0b08800300070006c075500710b2046c03040d141c2e0600d50341c901c0002c80e5240000c03507000c0c12960000b0b0310495400103202c403a1480c0c92100102080c4995120203c1d40786500418403038000950104004401c1c4e40c3c548075668000600346080c07103403900013240d8400715481e9144e480c99907842c0b8000301d080d1a101042150002da01d51000c0c41d846020401040140c00c260720341c05008a080480058450031081c4200d80c499100101030340381c035480380d8071900010440e03a5021107181c8030301300204e00181d5a01410b52a0050110300150343c5608207002c3c5425240d040c1d0040c42440f038140020301c0003550140c041c2c044030b49900c0407141c035001c0511450700d020109403c0003405407000107a6508080c1d00340c00034441d060182c0121041b0001c1000038030000c04441c13008210300d4101202d503d0020f80710040b12a0804050801503509010303544405000325500e9011040440d400034080008030380000c00701008040440d07045051030318006000803243c00486121802505501e50350248003419031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 966109694 1250 966108444 966108467
    0x7140d020c2b05030103020901121104020319180206190302040b07080a0f0c05030d0c110102030708040c090c0206060f03030705070308040528050409020a0824010602191101 76
    0x404a840c2d00034159540c0011900c903191080328050442e01a154480c0140c0c201c2e4100d07640a0400f45150386414020f641c116800601159226000e1300c1c900c3c01d0765201c0c00a10700130a545192042d4402a1141d140210b444154480758503408440d43c0320056680d06044e100d1500b07040c0d824403040c05100e80210000d10550700060b00307050001c00ca40302805000d202406030302e050b545402d1500c290015080da010b202040c401401a0310070440c0801700d03501604403204242990902801c08030566800d5400d90300100d030f8480000324481c1c108402d022144180a000b040c00d0142001128071a0100a481d010010907403800b843d003001680040340c5081081b18080341d00002903601d120b4136450070440070381c018450700340300f4442c1c045040d02c0843e03180c000400d490103001c400b070403081c03400003070001503c0e80c0c000603640318503a444006580041441040300c40c1044610301150902d80c807002c100e0403141a000b0104551140081603100010300094802054001035a801c01000107801280c1520020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 966110944 1250 966109694 966109717
    0x1061e2108160b040b01030b061e040b0a1d0403021504050a0b270c0102010b120c0d1a04031e0c030e011103130f0302030c04050c1213060e0f070e07140d02 68
    0x90100018420300176003441c180c2e84142d0106419032221001c010440f951030390244c803c1d00348655254110f1819900c800188907019007072042c2c25503195411a0a0300321881c000c000b0500090030001003560500402da04141406103d161604240d00d40c0c40d030f50140b54000401145101c804283c9000042c0000074010721030540940c10718008103c4182c4070140e04a0319405582480b102400a00d0045d40804240c01000b0051a104501c3c81c00c10050f40503c44068440407254416056401c0e1000c1700a03101e14001c2d119444000100c8100301508070001074038108002d44452000e0001ea4080c0142074140c0d42460442c0f06808140315007400c52040b422651482e89508a0003d482610b601d035603022607000302c2c01e507406810799105110980e4022210007052082c1044079609440942400e2a04984240c0b042c207004020340e5940022184005100c0041c2d034404208002800300400540005d042c02e649100b201c0e0030a01805003520600d6101403080c80d00202d240034942e041f0b6030540d540703000322 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 966112194 1250 966110944 966110963
    0xe0424090618110403080a0c050610060c0b15120723092e23030609190f0506150906030f2a0904030c050f1207080c0f01061e210816 58
    0x314007020b44400c0005800b260395002b000002590354a46001c014215049529054005406552629424032004200c0c2281340b404648070903954864a41c005030b10500c00c1d005203d01030070320400310b007081d810b0100345111203034000c10303500c1c01e480e10a400ca401c1443c1e52101070010034030103500050105901940c9820b0309058000080c80c4010740303460200e00c103002007000c07442d03e1007005154580c141141c8240d8254000b01042c0341041d85003842d481060300850124103e1022561500e0a04106441033580500850314104442ca07203142c035940c0055040b0020400c504100c0340081d210300c0601502041c11200c19980c0e44000454024842454402808980c0518040c900900005010302041d2b5403482503400d100c005904c001443c501410414503054203119859032288529440200e00c440c050041d0390340709040341024003030071015040e0f1a04416110400503400221580744d9804140c018100400180394500e04a641204080c2c21200503035a40f40284d600d001000590800144903082 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 966113444 1250 966112194 966112207
    0x61410060203161a0f0a140903072307030c17030c06010509060d06090b07021905060c0307050705150402040b0307060522230109091103070f0e042409061811040308 72
    0x95041c5c4644100154441089440440000c1407004c4004881d648002d17401005210045040b6281c1d414140500c035141e0190308849248190414685900849039a10084001d10002603604e8031398514ad505c01e4000c41c01c00700c2080140d9900c00040c400c0c0c500404540001c140e09403290b05244802c55080350051080011614240502c00303800c84003c07006002d490340740000007807030181000107547c00600605481d110561590300c80d600141251003808010000400050740038840c0e0440840d03c40c00c5c0c00300600c3c090041c0415502a08080c502c41d8002d500140440d03604441914400e132400c40f086440101d4410b0040c022608a801500e805070001980102e5403031141e6540803000000c1e030300c60745415030301c031400e80903a02d6003032460592050030f100040005103e188a03072003429084c60300c1ea44408070b0b0004241180c4141c8100c14002080d0184601d002c0140551300004180031102042501d142c43c5501500d1402510300450302500d07060546100b14002c42030718003850f00043d40655418 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 966114694 1250 966113444 966113461
    0xb210601030506060604050a06050d15081f06060f05130533120f07021c12050c03131b05040f05390c0a05030304061410060203161a 58
    0x1142480210b8651049200150480c10480180d1b0115a80030f8080220541440000d0b9101c2c0c0041d000c81c0121a620024000348440880c1190000c06d0850301402288444190009150076000b10032100c2c1424000c040000c3d69102d000e48050601600d0095103e0021892810f490000c84e4465a8006000c0400d030202d0300d000980e6940b00e091501031000c1002c222040c1903840e001c1d00b44489403032105840000d101110012000e61f00c904b451043c0d804c2c0480c81c0c103201e04a06400c0140000081c1c9031025041e6050052065035080807440b030440b0308518221180081c0c2e040c00c0b400007002c0c4200f20191130103070f50201d04800c004c3d00e4010014050086800d00c84c2c8000d1504507400c548840d000c1c40001c50700c0c41c3c41401540c042c0e07100c580b10003000c0310001c010701103540a02000035a5200d201c0526010610500c041c500407807003030344042040e80380307001c0d2070410300000740051400104140c410448035400200b04c03450400c504c011000302015a003000f000d0078004198041c10303016420200310491b03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 966115944 1250 966114694 966114703
    0x6130807020a0f050109090c050a1b15050a0e030310060c0201110102030c0a0e040e0a03030e03121801051b03040b18100615050901050d02090a0302030d080702061303020a03030b21 79
    0x12042030346d404010329500c2c0d1002080c1d518002c03190010031020407030025042d00c50498203100e0309090314031440d0300038a139841d14225801044010380542d80c80e418040014001d0181c001c4d12000e0200035400d45c01c02c009503010b40040b61240e102030018100380ba2046900981040003090313400c000841d164a44211042e07284c0d40101e2031040002d005068480700c0b891305200e40d15140103150003c0004441307550b010b600400e01d02000310243d100511200c00340c4410104003600c181d22662846400542440180d42034820140041e0403100c0c00e2a03100508040e00e2081c2d96200350030030404a02a1516210400c2501e003801c00d80760540181c0304a9200660f080e041001255124680840458006007040328907000d4008003e00055007005030200d002a00e4026040b00280140740403240e03030b606d60000c3d00e004001900c00000c074040740f040112041e01405030660200044070084031441c09640e0080d22004901d1004050507524145040301e070b00ca94141101514a0100c000c04110601c2441540e0303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 966117194 1250 966115944 966115949
    0xc04050906210313080601050d05190213020409200c120703030b1503070810150e0a05030106032d2a030206040603060f0f0837080c0d030e06130807020a0f 68
    0x8a1054000029090521850414004ad000300181200c2046041b121199000d5000161780c084c1c1c6d0b65611001c4c00c00144000c100900c0f80240c001794009a0f40d030100c08010708941804003d000a01c03650030101c03030108004181e2903501208555035401460241e0061189041c0960800102c0403181e030140310b208010750151196407110300d80c5984e90810380c8000c0e02c45002e80700b6524031030170258903414020450500a07480041a4912843d102d002190071100c89074025600c1d45014002d4180c5440d800280e488200a50760b4604039025081e1502e140e41405050040700109507904071124102c10751003000080d5034020005542c03141e807036a00601411207030086060340c16400c0c000140c1441000c03001c100300d5001c000542105880181d00b4580740c08254080880c111800c8044090300805c5451100902c0c0704124a07601d40140300101890200c0310482d01092500e0004a4001300c1c138001481c552010415913101c6d0800c03074074070f0b21300e00328010310200940003107403201c02140040006010340706 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 966118444 1250 966117194 966117209
    0x120c04030201170105221b0207150503100308070f0b180106091505040507091203090e0a02070b0a05060102210d050c0a080106031119020d02060c04050906210313 71
    0x140f050007103020300c842000f0302c1155030000040e07043e142110605465100014403690001880070b003181800207951612140314801038003d4081070254140d03042c54458809010f00e0160b055150905040c0030a01c22400701501000c00031030302104201204d0322b400046503001c2120801401c0040c3c10076590114203207200c182e5401e20001164211440c03140780c0d00b981110030042e00582c030709000c3c4002071101401110412034005408618030018407001c400c050710968035501c00a2409854000d000070151051072290b0042140300d0128281260307054106100c044000360644503180142c4c0b03811030120303400051110b00c40341404030f030007020f02078021280300c01c2040c042c55a4406060103184902e05512000c030340e1440c010300c072013407203036010241204c0002e1045140c1044450000f4144041452b5480140d0240294800c182c1d814003520385c010500d61003050a01d402c0c40c0004181210050803c2d018070031406410f141082d080b030094820800c007906495499048004000781e44001e40900b84 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 966119694 1250 966118444 966118457
    0x2d051603110d1505070309020909160603110a030f0b0a170c0405012106140a021e0c0307081312140105150916021f0e0613110105070602120c04030201 66
    0x3007a50a001030702c141000d50040440114100c454100300041c840078040204041d500c6d80e0010040c0c403000c0c3c0050140304c0d90700c01807003125010902c14030381c032003d6049001050304107000c0042100d04181560000581400c001c207150220f134684200424000038103541c880a110030019103c915681020314400703282c4269100c0c040e400d420302090300c1003031007150401314241d1591810300d51980610b030703842840350201042000c5a5200543c201074256102c414044e40080d204036030100f2299903580800c1460080da060900800d600350701c86c02160b4014010010010300142c228245039004c1c0d001d800c80181004011442d03050516600035198284442d42d032800d00418440f9603030002040354200020000c420654a0000301b602e9a04400700000561081640c4c000d03c0840903010b02d050440d5a80c00001c400039410401490303c2c401a14141c40e040c80d0304524070118840195003851080d003800c00c1c076503e00c40e83c9403040017407142c8200480418054010302160342403404c020030841e8001d03079461 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 966120944 1250 966119694 966119723
    0x1050915033718020906011202070c0306021c091713080717101512080d0c0201050907060521091e03090a0608060307091a0d0507060f0207032d051603 66
    0xf0040186001029510441e92800100258444c14412801001b094030144c14020035694503005018250011120541c006c00c1c10030f0780307020001d8160b00250881406200002850721158460400e601841004520020b6034114503c00c1180c40c0e4010200d400482e614031f50b98030307900c4106141d003030345100880c01891403001d0031103228000c0c148035414480c0e620021515003120148000c40c18503044448490900480e05425024030449110030510380021036203281c000c1410713080180ca40c200c8014070000b80310043c030b0815103015036030f40000b075260400416110701d5215498848110304603500c00445880064884c44040042c05180c41d080d00e03246985925520180d8600008a440c213406038800d0f101003041034520b801800c028401385080d214590403043c0403c0444480d03070007c0d0740036406100104000c55001488220002c658400f820100c0d08607580c0b034000c91001c807034540c02e04541300140b2082d690704100545540758084101c442540c80401400040c0f5400c0c8401d481a03016070a40c07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 966122194 1250 966120944 966120971
    0x121c030b044a070b280e03010c020a05031903111b12030601020a020f0418080315090c0a0809070b04091409070605070215130305030408010b010509150337 68
    0x304007010b40c4040601012820701e120702070140c11052041c0d549101c0c03030020b846868448188290030450507950070302c466685605050940e54000311910031544160074a00205c0c02c0881590689152082112035507d02488102d0103401e49502c98884403600040a103021000b160301c000b4014901fa068030502a9194150202400115012405a00200080b100600c1c00a201c0301c546a8000e000007081da02ea01d400c4901d40419120132a035913603000050210740030b1203041d20380c015101114010103c2c5000d90341c001300d500421800009020407040840c9505900b440b90f0005031046c40700f5103031501c0d510115503000d0442c0a00b5141e40c035048401240034a2000b05400003034600e281c646030324050050f801e10840840040300c480f44060140304410361092000c604200030741c02000150b449a003041c4003242107407070070582941445820452017110391112088507030120300b8a42501d48070307030b9414021000000d404880380b009a405a030340320600d201081000b02c854811210800c50060034104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 966123444 1250 966122194 966122321
    0x1b030f0a0f061406130f17010513030c0807060e0615120c0307060f0306090f06061709070303080c070b07020f0c03061905040c0b0a0509121c030b04 65
    0x503c208040c0541102c10b52400c14800600c429405042c29a00d0300f65146100b44c002181703a00020300c0c00814065103a00004240543c80c0c200060807104078000040340d03405001100c0040c070041c981c91303000c2980d10030b100302640031802c7d0003805010340310300385811003815031010300406101c1e00c12010032001c40e41da030400150304080801c02400a0450a040c182d05494449803c0c030000101074907281c02046800090292043c21144410041201c0e030070160060460282110001c85201040041152106000481c00103c5e9094100f2107925210641444403e100303001c000f07014461403105201004c0c1e800918422512113410980b980340102e44201501c1e60740c1680c10300c1a8000383c0b02075003c4404a0b41c866504144281c0141141c20754400d00541c484c0c0018120700d0100700049100309403810074000c146500d5580c0e101800401d003221811615201e444401541055501c90084c00c081c0c4840e48461408000d04c460116400207060b920074407603d80100003180c006061700f8100f48100341c000e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 966124694 1250 966123444 966123449
    0x30c010f0b0411121504180602030403020142030f051516020a110a0f0308040e071e0c11040207060209041a090705030703110a02010b0411130e1b030f0a0f06 69
    0x4d0860340d503034032120f440b0f101030490400724640c000d81d900c02c18407441d07014003645c40c007181c4100805600d0345842d090280c00c549542000402c09000e20581a442c03020701044024102200c0764054038811031030002641d000351541004040c1c1000e4070040c0300744040080d080c000c80e14850146119030741c5030341c1c40740700070311b001104103015038010900c000024807940201851844003400f00c404180e59501e00c800c820940741d10648107071100280900101d9613030700700241d00503580c0c03d05541040c440d02004108201444a110410540303000450402540280380b0720031000080056450f141c0c50708000000b580034201c100c0c821460040284203185a800d940100000000d02400d6103379200c0b442030707074a94030040ca680300305542d600c41141100242c4014000b0785295600004054494a0500086400740084d07440000400d2120354103586000c045002903030110120100552205100c41c01c0503000b4403468821810040100114a40b0908803e44540344c0d21001b030100d07940e0a4000c404846990 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 966125944 1250 966124694 966124717
    0xc0203070507061b15021908090706020a2d0615062a08031905011d0f2205031b0105061e10030c0507050a0b0117071214030c010f0b0411 60
    0x103503d040c000c00d0b034200c0300d8a09450b000178054130380b030304e0700c0403001c1c0d809401200d80002c100d0100612604403000c002c220017802180c0010b100213900340d1185202c0011441d28001100b2000615007031004140c408141c42c3e9900030018440400c007031900c018821400c4c000d080006d0303113006c140c0c521020340c608144c40c2e0340440e018644401c1030300d40310040b0a03840103001c01030b800c40e64180145040075034483c0c0d600900915030b0b00c4440400e1012110134030b0384040c2c401c084990b40c18061100180c0769504092101c01000c00c0b45900302072174680365086000720104031014031a006100c281c894410f41042c3c1c4180811122004504158805c070300f200201814580d81000c1407007407981e4014041d901020b42141c46003092030030b0070091f507034561400d08902c40c22a81001c0d80c0d0010030483c0c802808240003588100003618100342001c4060941411751a070140900c842c040c04003488100c2402141d06003c83c180085c40b650781c500105401030320f1242d03a22030042d0301d0814641c05140c5468144c40c00071000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 966127194 1250 966125944 966125987
    0xd0f020711091b032a0903070519170606030f03120c03040303020f0304051015061d0424031506080303040204151220120607050c0106090c020307050706 67
    0x48006109401c0001002c4110749003c0041104030252480f001e90b114a00c580c1c4d02c000b51407501d00c1c80c555401205844ea104c908800e1040c1203c40d40c000c0f901e5016102d058501485001e00402e5500c02a40c090b8011180f00c5021140d2101d01c034008680d00348101c034140d041b5401c1c0b18003c1c9080750399100e081d803400b0710b1040c12808502d0414007080250b03041402860090706000103502c00071020340c420383c0d003150300354442042041645c03507900459003408240255103c40c2440c0050250107000303440301c280c03d034000c6107a0600140d03845601080003445040105841101c2200801d0351600103408165080190a4002010030486009680c01c2c4ca806a000e113007592666400d00001e0304813070403517030342c45044400003180024268a2140040d409542c2c03401c0d100360201c5003030410301c2000030301d240259055420f00c40e4641d40042c11941041403458011355513481c40040a0040c41983c22030315070541400c6940610541c00001351205a00420a0394070381951200c041e1010724080700d108201000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 966128444 1250 966127194 966127223
    0x106080106030b03030403020a0e1905090c0607050a120c1103010c050910021213050a0e0105010903140106080a030903060c080906180f07090615021506130b12030d0f0207 75
    0x20a03040525000f0303018003142e00b00754596001030144402504044085900302003004141841000000e2115101032020891070070724121494070741003408081c60048000180315000c0150400503a1807803900650a040042c80d43c54000302100388510040c0d502241e17030001c804e540c0c0b030103100315018003c031038131114074000850050081d00d50170018207506501540104030a406400c2c030042c4404028501e100d0000c7e401c2c041001a42904c40d000354816a001d000140b0036a40c0201c404410b0782d402c07171004500c0180741c120035809021541c105004600800072071508064002210805480c400d0405101d00281c504080743d01040442d050002c503440280801c0740300041c0c4010210440c03c51058416410306000c041d8905102c1d64424000240e44090801000c082410300201190317103880a854000b400e071004c03912900000d046144603005c4043c001007900340c40da2040010030000790001080c0b40b0200b84168480d0042556074008600301900030060419510031a10140e9100004600082 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 966129694 1250 966128444 966128447
    0xe0f0f0a021507020d060f0c031103151504030606180c0804080f120f15060a141308012c43030c050109090b130506010201410106080106 60
    0x504581104152003c200d02c9000d40c9484d09500c41041c010207011401c0b2a501d01c00c80e0480d020012114100b52034408100d20030305082c8102c0e038001a4040c3c0840d00385080e640040c07000380300c40d201c02058520010700001084840c2d0070140441d0200c01f500d0054000920b02074040c0d45450f41c00b04001103200d400a0006007080e00907020072074514800b01d08240c1140101d440740b0780c01340c560302c41002d00c3d0307410813440950081c40400c5800080c0c40322410480c40d224050a070380804042c105c0822000704080701051100d15402008080d9103000313002d1280c2c800e42100030b88608cd40310140503410922040e011110009500594a0210500305001d800f40054440c981002c04c1c0c07030600c0fa82141000b06c0b01d0702542910b14000d50300652440d8a850329100000d0120144c03644414416820b1124100103650b800002d80c1c00380c0e50084011a40c0d56860004030700500e880c002c200700f420a41c111500460301005585031031949091442d04409400c202030407000744092203040d002420420041c0600ba = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 966130944 1250 966129694 966129709
    0x30709050a0f0228030b0406030b1b0708030c030a090f0602030a0b06131a090904030f090e0c0306010e01020c0418020f0406080d1821061503021f0905130e0f0f0a02 72
    0xca18178a030000b000c500303210000e0141e81260380190b454071034020900140d00c2c1806d500c4400c000300b01e21302b0703464440b103a40c40c0116800000c00e8005c0341e800100000d0003904081d001049420b50001c015081100d05242c40d01c0290410754000c1041448d00715100c0950030704000319420710f01001c10700110985817458116840061030000c00f4002c0d01801903d4a51701c88040e0310380114800d0312160700f6104042c100929900c48c5c2d40c0544404245807040c40707042c14464086a41080027803910200580c240c10040c0d00d0801c42c54112a040f61401e00000303000001c10390080c0000307200f01c2d54201c841000d41c0400060f103d583c05160364940009003040ca4581c050304043c8400789c1070203a50031202c2d944110000c0d1341540101d014403120798203c6502c08000b2148070701601480407500d40780c801c904603000710f01a01002c1245003a14842c0d030f1880c4400d203020b4010716009040050640c804001d103680b1240107032410466804082c80355a441d01d03134004c1c000c699009401c1c0c0d00802850501030700d80030030050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 966132194 1250 966130944 966131017
    0xd0209040603021905150412030e01180902040510180e3102010e041506050d0e120a021c05070602070f0b0708040b18030403080a0509030709050a0f02 66
    0x401c0e0740e05030000043e00c5400c8030103442901c00c5001104030746003000340714900300003e078840b6000c43d0410040c4020582c0c1e202080d0444d03018940000148503407401030382c1d0320081203207510740100d120f480021001c0c010740082050f0b9205595140d07451620980507a040003081909164074019040c060041460420900f988034950b45000900003060000c40c0804002802c400c0c110b034110300c2450419942c000c00410066032051350100000440304000d400300c1c042500501c020080c5c0020316100c6811241c0001640400c900207032500401c2000050350213600032420500035014002d1100400301c1004101010560540c44091400c42c6541d0340303500a500c0080c0c02c03140c00e251290f007038000c100d080e400d191098510740c82d00a0381d4182824407140203403000300003003583c51444402c4102d50102105407022681c0c0b1048403902c074004c0301010342c1c1d00d0003520420b03505817040070800200d81201d500042d02030892040e0801800140c02072000c107920030804c003402c0c04e42e401090b2b00110056048031440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 966133444 1250 966132194 966132199
    0xb06040513140c090f040c030e0d050c010c0201020a27031a040c090209100c140303040b04031823130f0b040b0d0c05090408130605120604110d0209 65
    0x1809454000180c0403070049a034400c0c4069469005141040c06200515048101207008508041403a80003d14400e03100d141203009030b445041e1048a640030790002d4448001040580e21704005151005141340c05c200c040001030b41c240410503074114018070884e540c5003030580d80e050b40ad003803601c00350740100136502101340405001180000410260145446494100000c1c06054106801e00540340c95030703604503180c0d541c810400c456290fa580c190190155072503040541001031141054039081380d40581c20121400000100010008841c4006114601c20744a00e0840c0c00701c04481c600c0d910380c1d400f0b01c11031101910800c180b4030b01c40710001c40d0100c2d001000d011221284001d00420303640d400510900164881c0346a4001d40303818000d02c0d000170010742d203108110b0841d40362100341007000c1c03041d14042d5402c1008030f020702900c3c00868010751104520f4140c0180d8942e80140503502c11402000e131007070100081406403425008550005034000740d99410300f40fa070710b20440254001e520710359 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 966134694 1250 966133444 966133447
    0x801030b04140312071e0503180705060a030902030f0d0215250201020c010c0509090a0903020304080f0c1c02010c1b0f0308180904120509010c08121501030905100b06 73
    0x358104004d00015111400301d40403820240800fa01c2c10340101c110211101c5000b4441000f03550000903207501015203419002c0100880908038100115600072030f4006800103544a1040e800d90841c0550b00c1c030a9044071140c60011203007036151260900d03000700603000204a42d820002c0d20710041d40180c003020311121003e8078010b080b0107042003070111070b026035008112403444500a00ca2558003007401c0c201280b0341908000000d85e40500140b001100703d68480d625003e142c400c100340c41c00343c81c400e03007155074112124280360b5917050313041401485a80680e0b0000032000301c00c020713102c1165046c3c6582c40c404100343d9420501c3d1a900c1c0c885103c40c0312110000490800d80340303e0000560140780720765a551100c0c1e0010840740c2c440d44240c1d008090708021b10000840c0f400c0001400403c0d403409075114035410300122000c0c11a604040d10581010400504402141b00d80502070031219441a45802c4264015070646841081c043d00c030790410641100d5015a03a0090494181d000300480e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 966135944 1250 966134694 966134723
    0x120a0c0e070e01030c110d0c06060b04051507080705030d0203010e0112050307120e150d0e0a020325090e060906011e0303110a14150a0b0a0302041a040e0c090a0c0801030b04 76
    0x340ca0a41407e4070b600005140d41003030810f1103400d2240c000a003251410441c5400d09100208607010300c1c04170f1080c160b1400045031003e000c2010165a940c0c0d602800341c940d1051900d00002c00380d0000e001c1ea0190007005800010300d02d4901c401d40d80341591207009103051002545440f00ca000700c00c001c0f00107204004000401c1d030b0b541d401d801c40f0000b00c020840d9844079142c3c007001c41141c40b4101800c0c010b5104092a101503a0300194040111000b04994000e069402480c20540c0204c3e60042e4100ca007004000801c0d0500414298840c0340342e1000c455103a0b030794111414a1300c90f031007005603c4d0300d0314490500220340f0600050f08120b02d04000c4a10500580da214a80d5503281102840307240c200320b10f10740765516030560b490b800003424182809082e5410703001604021140c440213100302e079a074804640c200a1406ea0070f02d1040024002c000b54003a0300f00c00794952039804192445100803a000403a55031940c4a4050f0a03072403a5035075503c41c0e0940c0c5d03a0046010026109843d480042441d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 966137194 1250 966135944 966135977
    0x11d030706050c060f0603030301180b03030f09044205030307050a140708070e091f151a030121080a0c02010806030a111e120a0c0e070e01030c 63
    0x40c0d0004080995403541d403400040141e81c101310018100103507440100b02400740a07036000054a0554400b01b940400307035074140104800400356801015014000841c0c9100141a00e9000c4c05030030714150b405208d02580303a1039001203054010300105001180210100c2c503801109031001460842c2000075116a440342e0001385180c10902c07041b00d0302e62250001c101041061340080542e01028401481e000c1c1c20200c07510340f180344601445014041130380005041d400100594800d00c0c1c1100070f07401c99941c02a80540141900003603013150038940c01c0d0b002541d003210080c00c0c0c0441c10860002802c50b420005000000c0209800d000a141c0d07002e0741100110350f8443c0240059810740d203610b0f00340e4400d44000f42c8040d00c0141044c3c0320750000d00703441010034020f81424505520442c0e003081424800c3c91600e0a165140a185030440a01d01c410406500d001030049002030007545860304480d0b990188160310101210718500203001d00d000409103500036000b240c0741d1aa40c2c100b040300b40b88080386 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 966138444 1250 966137194 966137203
    0x161115010504110a1202090a18050106090611122101081f111207090801060603050a0b0324070e06070305070b1005030a08031314070f0b09010806011d03 67
    0x10248804012801000740e450144078501e01000321920160030101c0c2850058090403c41031149956a000904640f180d82d03040c0614010b003d11032040300d1640441d0a44d440202000d000d20b41c086007005902140c01c5006555104a600103000100142c40740f1640061894002c408400ca0350000350f40070080c00f84c18190024081e0299400404007056042d0b070301030343d004050245100e8103240c002042680400603040719100780c8018210f00e4071351a07068080341c40401651191050b035113802c0d00400d040340c0c10b803c1940502011300092111607201c808068580c020416000286004100d440301400c103180d078000d034810110305201e900130f24107201050f055800b01e01304400242001540340104942030200c5508072424280b1800700303500f070a0202e507681c0169000903186290103c0044c5028142902d0014042c0e485940414110303414041a60703600c10b98000c0b080708113500140807070780c84d02c0c40d415180c030004169a801e01d20346a102c010b4644e021090050f0070306050084460159450811 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 966139694 1250 966138444 966138463
    0x26071a0a0206070c110f010e040203090a0c0f05091b09100f030c0801030803011205031c090b0a02031501050903100501081e0102040b03062e0f1709061611 68
    0x101a40d403022085402810002c1c003d0120b001e003d40c0410000210b0742000c0042e00c035210507215000215075603c0180ca40e0403000b4881603000d8000010404480c10120f0f800120f28801d03445101450b8540355942040b04a6000c2e4031340044e10f21000030200a070340c080d98516104038008461a114040f00855a41171040c103c00010950a5000880f020380c544107044070250a464988020350543e559506148018482c100080366080076400511a05000700d603001403c0c00800086800820551405040d0032041582d24142c000000303104500b0500840b84611102c040134540c111b286001540c4a80101c1c1c0c030182c142c840c260130201c40c85120320a150107020603800821100f070036070225041c00048034008098a1740188420045055a14140c90b0481411111a0340300c0c482a507420002c43d4030741d08683c02ca81c16a055080d94203420014541280c10940c0c2e1300300b50039800b000d82d007451035810b1314146a698400c60008001400703600d800f5001c00b03410318107090810141c0100510708050407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 966140944 1250 966139694 966139739
    0x917071e05070f0602010507121113081e030c0304060810053703020a050d08070f111314070c2a050301061212030b041b0c02010807092607 61
    0xb01414000c107240c040e9001e00030001071009102500e003101d0001c0c48803a50106141c01c1b03035161101d01c00c80562260070b545240068002103800705035502480d503541c10182c040000420384904071229036001c08001c441c2e12180c00c90040d0310b02403034054220745901000b404850489101c2c030005c11169642e055011174104c01702c40803074040c980f009588407022010401380c1e402c481d60741c42c2000140c0f00d183c149400c0711000c56110001c3c140d64141400544150040141522003254800040100113121940700210580708155254008003480c011075501030110400000c4100000386410310441c08841030034400c0c1c1242030154205050103d43d04180350714500400040d072030034403160070248100710003040c801e401c0c1d141c6280039440308500c020170a00c1e4a401c1545a200a11060300e0741d81086100c2189001c0c5200380620841004041a801900c100d00203280c0001180c485031050002d80c003580c10705000846402d411509528200305070808520080c010000001590b10030500e4585844401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 966142194 1250 966140944 966140953
    0xd11120412120908270a090f06030501020f07060b0628120e0f15010311010807020a05120307030b0906031b12010603121103030c03010b0a111614040917071e05 70
    0x900c10402030540d5440090b40e0410000c43c207411752943e80b110300c4011108400400503064461110034070203407840e40c002401942c0002189014102c00600a0910380d0251004200d0741a1001c100501440b07801c40000904110140d29070302c0641806040d0740344105404d2507115100040014001c1d00c02d030601244440d00410507800b6803c1d000c0c011100207280030440c00d001981035646203100d12884200c130f24100500c08000966050007004807142d4a900b103001c90303811100b2156130014641c4105c49043c0000c0c100180a88135007442c812140c0241c0d0b00802600c2c542d0304c03035040343d0700e0a04524503090b8022020142240400030030701c41e11024602031180d81101551040c03001d8008000300d014903205034010420072005e000e455081d241554600109582d9480405404858003003402d4030008050081207580d03011390540a602104813500d140c1c041c802404c041040100712001500054811004040710038912034041d0010006644250003103810300c3d2182811011034100c0c4e01045441c2e030301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 966143444 1250 966142194 966142207
    0x61f0203090405283c0f0507140a021216080c010f0510060e0f01050c10050114010f09030b090a0b011d0f0603210d0903050d11120412120908 62
    0x1380307441c2c040c00d58102c0c1d4034240908019101c20016100500409045540414032401c0c1d0305503001859420788612200d050040036082c400b0040240000d403800c10104030408070902850f00c084040d0756000e100ca402034043c1c000031480c480c0150f0b00035000005080d9001c0e1010b00002d05443c060550903400c0d400002ea0f0500940b4180e046644c007130410303d0050308007201000303010b84c4543c0c4d40c1207400c010380740805604d021000684030f50140003940f00b2103024102e440e10504407142d100381d04030b9101100c100c801d070580781d0064a84008200c94003000908160301800410070079040c0503001a18503042b146074143c20340f250151501c00780c00c0683c24481200f4a50b183e115140782c4039401818110902005042010009035901510000308081407000c000183e60788072210b00b50783c0c1e0b0001d030f100d0502203140a42f500800a90103242801c4c00140340420541d10100403800399101004600d02100d646d443e1a00c500c0881e11341c100d4410b081214640951003075211780d00610110505c1402450b44a40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 966144694 1250 966143444 966143491
    0x160c021831021021090204180f120503190207140102040b031b04050a0501081003050607050d0518060402150d1533030e0a02030303070c1505061f0203090405 69
    0x1298a07090100070200f4031321031a80c09a241039207900080b2000c00a22441140f02180150081044104a912070540d8007028000d85921402c1c8161040c3c9050070b000d54003000035140d40c0810b5410701c40c0007410600700d40070841241d0003041075a00034200385041441d817101042c2664000d4200170098540441803229103444d000c00d1006020340c04011504140c2441c0108040c101c26105e41410402d80c80003081036003094800c420059504803050355079914100101510710b03800303015400c010501d440d00040819440d0203910550304c04541c040d040c0d03500c4980820101015813060511401c004016004480c0058850300c0c0190320004001502c0f03516007040c0200201000c4903924902e94801c6080d00752000048441011103950300340058204901382a185c0b5003001030700000c1d0103100000901619541011002102600c1000545025000c0680202c2030f00c50540c0c0b00ca400c2207202084071150340c070300b40e009400c006092048a040002e5038000405860064900c3c106240c0008045078408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 966145944 1250 966144694 966144709
    0x103181403120c0903030306101e110d1803080f0c100603020a2c0c0403020303031918030f0c03030b03100b010f03110d0908090d0506160c02183102 65
    0x3030700310700d0904c0c100129500072988071f2000a140c14850b0300c1da0f0408a1855000e60300050980004060f40503180c070280c940508048405004900540b054100302c82c1c001d441243d18407015642070748000d8103a8a103540380700c40c40d00140000f020340c0e1014896808078000802000c030120107100c0001c94002e1039401442201a140c1d00b1210000c094000005180e0103c1202050804594818450282c0d00c8020001d414051500000d506001c00006d0000c1805060005205940134220800024100b501c10101c48040080700402049100240700402030280d400d00715024024103002c10702d00e280c0c03000a41071600e48c01035210210340d200b00c441080c0d64001e280c10500140c508041000801c0c40e0002c01d500c0c003d000c8054941030725485104200f00440080d0b6640c030b040580700c0090b1003114542180c807a58101c070307286070456004000c44e100c0c034400e0b0160341c080c0d81c001d0150710340d403041034107040c0d00d0400080540341d00e501800720034207110010404204184c400100000070b041568410010760 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 966147194 1250 966145944 966145951
    0x30e191a0703021b03010b060a0503060f0301050112152d1a0f0d0203010b0a322b080c01150b1312111905040506040c020c010318140312 60
    0x1291081c0034000009400203100d66089422200080519035040000303800741441d9582990420000704a5540303c503041005540103020446501007101240018142290400d00c159081c0084403c50f200200707507074066484c0f6039203d84c3c1d00072850b03180c01455460b04012400d8100040c4c4003072811000c0c0300c00940715140c84071881415000c00c1008810028400502d0803200c1c07403043c440c503e4020119a001d43c00040c4001c000740c500300d0190f0303442220541c1c00c802d030103030307a040400101c80300c0030559085194451003801c0142001900a080c84c0c3c1e8042650304584080d44903060040020049280b0f040600010300f0601e0003c2481040c84141c5078800750326030700c40a1602414800c0c0303d00c0c10703a03842000003581c00994030312108060f241480d008000b00391101c1030f04010400c072402c1d281c5149000e010183c0e04180d80500c95a1507581c14002241c1409648000507008441003036102d6210f5000310102d03072018101e81105418645039030000710310019003d80141d20010b003040900c051704000950 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 966148444 1250 966147194 966147239
    0xb07030e01020114010501121506050322020303070b0405010b0d082d0304021012050106030903030e03070218090c060d1b0206040c0e060d061d01270f030e19 69
    0x1941c0d41803511300c03039000818029039050020021203001c101c2c0c0360794815903001800340f80040139203503103290180c4030f42c5c0266900e407040802000c10840d2a11440499081d49a02038015441d207095034903000c40d89000034104039042e54031411010032556071011169038041c05143c08941c0d50109244d1181607543e042c211200d481c0c1384184240c0f542c00048192036105405649605440380d4200049900300d820341d40c0e0b002e0040c5084000304034141c2c1940300c02803040c40b0386c500304100300700154816500d0041d144002c0d8005191902e582c110240e101a150308800728000301c81c0300d9070348000054a9500110284034900d80d4807403020404280c01d85c1700706521020390015281c1030810303859100d4240410301682c00e0b801c03d000d0108900791124554101ca00c1d0308131000700030030040c031001c0408540d0f54890644d07407582480103001403200c0c0c03180d0f001494180707c8055200348106540351a9400c410302c80075409d01c1510001c51341242c850029030f04202e0030920380c132a140c0c1d003021035111561100000e00c26 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 966149694 1250 966148444 966148451
    0xf270d031e0e100209040b0d0b09060a06230a08070608040c0f030b0a0e150106031a04150504050a02040b070507180207020d1b03150f0f0e0705060f130b07030e010201 73
    0x140024408290b054803040c03c40740140e03a60380400c0105000c3d02002c98150b0b00b00c0d0350a030242051100c0101a5030040043c401521902d0710340e0300e803040a950b228014854104c04941409000c013945140b080300840000e0b06800d0003594815100b07042c10350962005011446690420003001072411032200a881100e01c0001841d0641d25a4920fa42004050703003c62a9a002c0f540c42203c4100040a006102c10241802540c0c46d020014050b006441c0011860f0f04c00418039403551a203800f52208800c01c8101d2480c070301780380c0740800000c0c14020b4010000b8603401c100c00715240c40050003d29005000b8401041014030301844c41d156540070740c0d00121817510512103800140d031100c25000c1d80340e0b048041d0700c6003815101c2e80d500c072200850348024142202c04c0c281815a55207a00100b88450340d0303131010015040030b4018442585e0640391a040b10750443e076804e02c1a403818500ad007982403202d100302400e084044051016060390340e001060071000110303c1804256018000300101c41c6c0c01e10091 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 966150944 1250 966149694 966149711
    0xa050f030c100216080d0608061e070e03100f0f06120515040206040509070e0d030e10021501030b07110a11040b1906030b030a1b0f060203030f270d031e 67
    0x12007002401c00202449000116602c80e103846d500810702420200d01552064107021110580700040030781002c4500b240030002880036402000027649002001d0040c2c09420844d1b40050f00030708202102d441e0582d036a2640203014a00e62055034050940f600000c0030003e52424040c5c130700181408944111001e0108000058a9040a41d011201e0945404542c0e4a5040054a510031a0369005030880c10360a01281415800340003014210380c16101440801b410b0700080f62215a003000d043c0e83c0354110401000002c04a40340e43c3c0d80310000740b074040c541010410b08242800c41c03800c0d042d21400e48144084030706140c18403443e4160300b0200c54070b8401e20688204204254002d12035201419a41d40c906ca0080d203043c0130b110500c0d03038408582085100350350520102207556000394214600784140c081240d900020841c0d014a04000c181c2c0c8660791841a82c07400001010241d2289100360410502140810820250210341645000c510008140c107500f001191403d0030f5a030850401035072 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 966152194 1250 966150944 966150967
    0x3180e040f020111070807210609030e1f05030f040302011d10050709030f1401061703120711060a0902010903060e010507031a0d02090c070b040b09060f04120f020a050f030c1002 78
    0x207000326150003008101e08d1000c0e4084c0342480e00c0420f00075141d9070410711050100760703105000d00703c0c5001c200e84010b801c01341c85102c0000044c24010020208508002142040a04803120f0f039015200e84008a00c1642003000588058001c01c1000707001d41c030210380142e083c000350203100d81c03000503481c180c008103181d0740b1102200c603a10700340546a03480c204990602c8078800e411641c06080d00003102e00c404110102c04903a00e81c0b03c80210300f02900a02c0204002d50b00c07a040c0040094000c1c0014000d0b51180100c43c2c3c01030024200c00c90500140100020006e0031500500c020a60204000109440d00001c06416241c0c001c1a1800300d110790301200940c1e5403440501020290180c031102401c2c0e5495480642c140b049070340140110140f281008200404030f283d0b548110000c0007540e0090301c80180018280c2019100202100580c46950900343e00c1440d021060045510403605090781949030716080c00c42111014005400000c1c9217039040b00c080280c080e411884070411460045103041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 966153444 1250 966152194 966152203
    0x290a050f0a0903120e0d020105060406030809060d230411030a02010807030f020f0c0c0a06030e0304050405091501080f25060c0212010c020303100e0f0403180e040f0201110708 77
    0xd07121100c0c1d946128a090501c141c607116003021940c4000c2001100016445a0710340480c0d06040056080c08005445403d02c0e000703400c200c941c007000380c41c24003224008000c6244c001641c1c00d0007080d03590102807115080c40c0e03845206820302c0c0f12840020304080c2450981d8907840d048990184e40120111300042c2d034443d500300d604c88880d180025100301c0380d40c1080701030312420081f01642c2c807010401c05040400402d80e20090403040325a44140f0390b4a010507001ea0395034110818040e00305000c208400d040039001160310003c1036042d120340000d85c600c04820305200ba080941240c0c010382c4400d0b0550310410010000c175255500e5248040104450844010200d01424003040000c003134800031516046c140350b14200c0c4000081c8403240c0c0c2800006d55035002100d80101c0c001e01c410002609814042042d805080c404605050a907581d440581e0b06034101c45410b07c0c600c000460004481d80c43e8542c2c1c5d401a4441c158583d4142c2c408e00005000c0c40448a2080326504104820004a0b10005 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 966154694 1250 966153444 966153451
    0x3120c11010e030a17040603140c07080a050909040f02010906110a120c02060304031701051c03030c140403150506010801060228060c0818061b031003290a050f 70
    0x3070165204000b42c0046410041d04100040140703002d80c1c4102000382c0c0c0500500182c1c0d017156010420042c081030890841e41c015134075017409510401080000c03d0240000b00402c4000c0d0800d40e140c59010b1000c030700214012541030340c540f000a102881150303445040d0300018201c80c07400240c24480c15510030b440e01450340008021030341000074480494000c0289490581d00100340a0f109e2500f801c02422607016210403810342c036a6480080358502c0d05000d40f030a40b05141000b042941042e1354160020001c42e0b8090042c84550399011400c03c000600902c051031156040098503a03a2190000039541c019081c5818010100014041241c2c0015000c00117110b03003140c0c00940c42c1d0b41c042140c2101c009180a044581412007500d00d42d07170041d14160007607a50042c5010082c0f040c4001c81c2d100c1c481520180c5031005810001510342d1300b00006190021103940000c21501ea49076644c1d0007080400000d9105080340b440007008112024110580c00490540b05000925019003003210703281000703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 966155944 1250 966154694 966154697
    0xf090910141e030307031205101d0a06050307120510112502030303010f050306090105012102011b061508060405060c0703030b03012f13050f0105071b03120c1101 71
    0x4070354400d041c6071828040c1d0b54108000d402c1e00c1c0d4620150600508801182d40c400c00780a04080102d00b500b0745040480048031200c0588001c0c080208426114082000d04001342c42600c550700403c042d0b03014012400104081c0c589420400c01300c3c0341c064100424038441c400c1051800039001014404281202c0d011001500d5608003006e400e03000d0007503590a00d2003e50944404000490307188005038031203095440031412600d1503a220040182612424005c80020703e030381907807000b4440103000745990100d2050622201c42004500003403182884c00c403040d00c4031502e501c013102c40b800d100d01ca500d0181c030485000d0007081c0b4107910b4295076100043d201072408040042c0a00c28140b003a4005400340c140113000b448042910084034001d00d9500e90005410407503126840e0b0030044200440700700d41001680345a01a00d0281001030780c003400240310f418040200100400541a041610b01000322101009041da05608040c00a01c4076034405106004c1042c1c8581c001c14550310314000b814030309 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 966157194 1250 966155944 966155959
    0x210060b0a14210402090c07110411120f0105090c16020607060f0e010f23060f0a0806071d0d0201080415020903010c020f0c0a0b120a0209060f09091014 67
    0x20241c11482c14803d0100d5050311103040041c400c90495090300080c05180221010502525694841c000b5445641f50040c502509900300e0f44003400c5c95089540350307407512203c041c100094482c40c641c2803502211005598820080103200c0340c9049090a5085a904840c0508043d05550106841400000003074411003000c120801080000d800801001141200c14041c8851019800e07000c1c2c48440a09002d032400d12618a4005030046407000d1501e440303200c401005c0c0c40c5c01c1c0501c0008440f0307440040d004140c214020034140000c12000740200a43d40c3c0d40c2c044081e604400042845884100c1482082a1134507403000d41e0340500d0450b0481d40115405c2401800741c0b01c140000c1c41907001d615099420100c403150a1134010403856140d0310700070280c40390004100c04011505446000e517815041e02030160903995640178200540c0501515401480e14124030001340c01c0760080d00740c02000480000f5034030041d051040c243c54000044248034402c440c101408888542001c02c1e10900414a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 966158444 1250 966157194 966157217
    0x22080304151d030705010c0e0f060715020c070f091506030c0915020a031b03200a020301090b06101e030b0301180c080730050c030607030203070210060b0a 68
    0x340c41c1d000281034000d40c10342ea90484480c01d0002d88030f0b084404242c1d002c3d40b9040b00841c140b4015140b405164000a000540800f0003004200003508140b5040d95001102241035158808908c020700386820902e005000f900d10740210f040501032260890003009023880e0100910700300c0024110161030583c14041021300042e00200e6158078a607100c40242822010440012500419040c0c4031500a98400d00042c0e000b5084000c500c1c0001c100500003520400c40c80c050302c1142192000301d80710403007501c86d910f00d035800081c01d42e05840f10a5a800420f40240811480c00090a05c000c0341c1d13904000a9062000804054000030001c50f1030a05480303000c101c5503030360300b9070050030581c01842040003000100d042c40c10b0788260501807040544950780c00450014510301c110b0b15090711004a54105003040c1421944e14250010100d030103210325603070303884143d41c180202c0340b04400b25980142c803840c002d00300030320740401410811141490a102406207000060890b9403002050401305500c48 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 966159694 1250 966158444 966158483
    0x20a0911120103060c0210060807260609030a110109021e01090906080105060a1208031b1902060f010611031b03090307091a0f0105180406051002010522080304 70
    0x440c01d861490240c4040c0d0000c42080840d52045200b000541e00b251911026a58404110760300d90140c4009980070305002c0264040904840c008603000050043c2c9425030001301d54900901a00c40c42c917039410206119a07400e510040c54007660719000000c3c081d40c4070b00d40100341c0c0407805170f01503204820307100c0050206034024405240208508081000400c3d503e686590082174165003040c03145120400019503031003a55192005150002401442d544842c01c0940040c1200303030304106a1042401442e4950744840d007002042501a0058101c034034100550b0280141d05811036400e00c03010341d06145640b5400010394044054000c0e03240c01e81d00040041c146180101e0301503950600c541d070004120905950000b1a2449040144401c82e0641d0402c0048107514221803a00080f010710148bc80804c4013030004c01000c1020b000001c1d00358031240840d10075040c1c800340b000981c5d15401880303800d0b02074442e280c082d0041215015000e01c3e5650b82c0124620018101400c0d0544d0b010f0b02c1104078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 966160944 1250 966159694 966159697
    0x4020d060525030b03060901111c151412030408070b07050a0507060f030c0203090105030c1303020a091d030a080c13120c1403012a0233070c020a0911 66
    0x12502d40d80e102802690a12009028209001c103050082c01108041028140140035080d0070b030307081c1801035040c01d072480c8505c0403900420280e01c68141e00c5940c0c0800000c04048882c0c0944561f08001d0515602c0c9400c1c80130360401e0242005140d032042008201c4c0140100d104025926025001c41c2d5502141c10447c4c50000200b502074554000c2c00400511543c118003444600d8060303490a2200c00040d0509980f42d01449800b01c0c0440c008000040703080c2003a0700200a9a01c00c440d44118a6807a034011603203c400a0708500e0b21142e960070001200e06100103102c02c00300c040b400079807070b28840038070003000c00c10040c10306007020001140002c21034024180d90b01c05010010715203181d240e11400d0902202c10709200302503c203040c860b03034010130f4101800782d41c039900599051030f0003524a8405806054100c1100301c011400382c158003030b0f00703039500c181c140740c2000a0b460170b2002c030b054031000b11f29460005000710003480b0801c22001c0042c3c540010110440f120f40741c000654a10100f11030700035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 966162194 1250 966160944 966160981
    0x40b0a060e01180e100e0a0c0e01200609030901030b0901051806030a050a031e020616182c0f070c0609030504030f0b1b0a0203040b0c010b030a030302091804020d0605 73
    0x84800d540c0c1001103030f40710031300c02c4000c0740d580340c0c0410b8454031002c01d900108c822299904c000111040582141c55000c2d00744012450040b501c0c28903c0b001990500f801e001007a6807c0a580e040061500b40b69a8140200204540b040b07404000c80d51405001606546102c1180301d0300b64080ba00040956509100860409800c41d090300d88140d042e2500a03c24440c41980d61902140c04200615107840062558440d01d40e0380d2446441d0075030700d801078400b40440100c49002c1c0300155008100381c00102c03507003500c0d0010f200d205081c00e62150008180f4010040140e18009103083c100a40140d01080407154950883c0000604000900b812610351280307800240c803405c400c283c21010001218030052041314954846003542c2c54064181c002d0b84903d07000320340140e20500040c070511011900030010901c907040001399a2200f50003290030401c0340002600441d80c0880c0d075101605110007809a6070420600c20317141c40c5083c1d80040c24001c90030301d01414280d91480018000894020000d15 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 966163444 1250 966162194 966162209
    0x40207020a0905220803040f021903080d050901020c031b0c040504200a050d0b100807030308070e01020d05040e090111030c13210321020706020405040b0a060e0118 72
    0x8503142c40e4400c03107025000555003406031038401d001c035648141c940d41c040030489505c407803400e207151a00d403202281d9038000c000aaa0105125174482c48030038280903002e00452090001a4584040201d10000c4890080441e861a4010052490a100e0100455206202504c6402d0105554040321890003064982c43c40c0c2061800381032000341701480140c2412070754142c910713142400514041c040c08801d140f00d0550805d00294420002416032103540e07034010034140c692040d6079614000e81e13140000d10b41c000d40220f0300d2030041c450083ea0043c0c0f042d6001100303000421185155010040280c4514406d100c00004202c0105000140c290080c04200401c00300d135036140d00701003242d07100741d034417007160351f103000c1d00600c40055403080310580d002c00561030880340072010001740c44c2582c40380e102610b807c10103000014480c40c685a284003608429000300307001a1200d09043c01d001c2140c0c5200005881661b107041d041010550200c0308410100c02841d201c0d6240e03c0012283c0319000450f00a0788 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 966164694 1250 966163444 966163459
    0x30405011e020408010b01020d0801260105011401020712020f060c03160503041404050c030c070525090e0a051e161203090f150f111903080a1a090604020702 69
    0x34204001d50050401c1c0c0350400020070401070607500580c1c1d40c480304e070102408078181c1c0004010074101c90081590f0001c61002c0c3c8240065440451801c441c8240c0085112034502c52100e1140d5070b040040c0c00217403882000b0321f0311f504010740000314070b998000f810502c2080300003442d001004050055803100c3d40308120300120150b541c545142c03a83c006020700300c900200d00c602e007000c0d46424050b00b8015166201164655140c101d0440c110340c2c0900415102c51041400004905070200940d161450035401e1003200541400c0030001940c0003000052150b03407000001c0c0d0013241d4041034140706003007500d8800c2d8080300c2c803810003410014146840c1241c0c134415440051180c03079071300020809a200303645810b800c980790103022051443c0c0b80140800b1560072060540c1560040c00c0bd55151403c50030880f8500d241072070340f1840c04ac0d00d07102d80030305c00b80c899100b0002c250b08940b10a400204100c0c0600c4512150f800078004c0151910303034a40b180c06840c011542d42c1d21742c0d0f412140d02540162100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 966165944 1250 966164694 966164741
    0xb04060c08030c120f240603060d1704060809060a06081c090b16060b030a2604030c091d0607020a0609020f032a100c0b4b15010503040501 61
    0x1003042d0400c031500b03a0208081b0001c401c961201c1d02e0940b44d03503c4010301590550b188c040038400001c0d01036000325160040510041480740200300500003c01d010b5480704a0b5291009019042001c003a20a040b1242022800e015040001c14003040070504445015101405140700712000440340d4001d54130b0b44c0c00021b800215000501d100b04c01d0354080c00e400d000fa0030340740050540e030706002840540248480d882d43e0001070ba82056250541c0441c0d9411800e080d1284c60f0f01510744000c0d84002100355441c190825500e000c044500b0f004880c0750040c04123482c1c2140040d4880d0030490000748040d540c6c03a0020215501d8890002204101070116448013039044508240c11070140d0107a2824000d0350244807442c9019a0f4070401c20850743c0d98400714810540c1e0b007030085d910240290020090241d451824030342281c0b40c51503000a207004540c0c03a92600c0c0810440c514a240342c210030a1888000c10440380040164198900f00070318004d540c0703903240e041c450300400081d51503001500c102c8500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 966167194 1250 966165944 966165961
    0x30e030c12090d06050c03012301050f0d09151d0a03091703040503030d0605030105060103090804140103110a02061f080a0311011b180b0c0715050f030f06150c0718110316090b04060c08030c12 84
    0x40c2030025643803020044401c0340140042c1e0351807000c1002000924842000c0c0407609028240003101c85000040300e050944800c0002c5c11a080800010689a521907017041a46424011650400c2e42824104504007698640c4010b81c403da003c0c074800000040e4440d00c043c3d100c0c0e0700c80b10b66207241802464035000c00380c40c001d48925054950102c80080c5101d003c203601d403c0c0c01d0701800c40700c1d503900800715a03d0b280d50a9640e44403941c00c1046555031080c1c1e00341030a00341c2e442065104142da4801d031445010042036902c2c0c0407541c0060a46100607c030b0050105400038222040d1040c180e440149101403040482d0a44036009020803181004001c0c070011048001c0c5460050808070789000e031044044d00c001d1260b0050103000742c4e580d800203004001c00c01031030409180104501c040440e1100c001007060025034010359103071103046a11007076045881c0e40881c100005e41706004640e45403601d0401e0040091502c401d02801c1c844000002c00d00407401c0754122101c03007007400040034191901110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 966168444 1250 966167194 966167201
    0xd05061806222909150c1c020d02160c05013c05090a0b090f03070308071e0b0a0903030e030c12090d06050c03012301050f0d0915 57
    0x38a654612072900070a20581007544198865040c40012814524843e252002da030b01d040200380314412100d40d2a80c0101003062070035842000c1401c0205081e504240649001e43d100402e40600ca4506103e948034900b1115540140d01003005070150f154090844440005d1040b000011458441803e1490800c80ea05c850070044800907201c86c2503001c0c2521b000c0340200c0c14102198200486115880041800680c1107445c0760780c039107415420507000030003003481504580c000010420f00401d003003000e450000703000d0558a0082d0041e014203807440c0c3c2e4202240c0105880101134180704080c0780c0d00007020380e00142540389c00200220950030008040746c01411300c0041600020309028001107408000012214401c0340c00c0020010b03160110498030158100c0240e0940c01000c03000c5c0701000c1822401345070701030340c841074200365603505d000e040c01840241c09400e540c1c06c4c80ca640740c3c3c48da41c0c1e070040180d40c14a2003d29070300d13a41d4409000441d00620380b008005200d08800009080d071441c641d407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 966169694 1250 966168444 966168481
    0x1b0c030a03111504020d06090606082d070302091b0d0212091509060a20030906070f0c050309090712060f091d0304031119030f12050901020d05090d0506 67
    0x262100c01c0e0701d000410f10319460480c0c3c00b80d0006800c2640100141003940009250b034090b5200040198071021924280180203d0310441c0351030465140c452440d403130307416410088a01c002003002e0317031659005c00c0c20200000e02d01c116003070203803444940d400d8000b402c41c1c1501c1c2c0c1c952800c44d40d5480034848010307840f03000d6500007110b1055555020b200307402c055030b041c019440b41c401056503070350310340c01000503162001401070004480501c110345003648001960184e9405030180900e482c10f0280101040301c121901001c119101003142c010803004001c13911414415110038019582e002402d4880504503105441014030784240041c407248452180c4058800101c414080040307141400daa5500f4404071842c1140c00030003003040000c010024801201c1c00140c8070108403da00100d070b507110b141d158820354036013001004240800200c8101040c0907130050404600700313003060b40000d5072a010034040c0e0090080000d03000da010780c0c3d408022195507038800102c48207407034450081104100c0e82c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 966170944 1250 966169694 966169727
    0x71a060a0b070b010f2c0907030615081504120e0a2607140315070c0c030302061603050906040219090c020a0c32040623010f020708031b0c030a03 64
    0xd1711301040b555003500600f00c0c040315440b00d1508004007030b850158a40009132030b10040d4400d51600000080c214001c0c001d4007100380744640041c0340350400c4641807075100c582c0c0c1e9088200304000c000008804014070040090186000d051b0103051714042080e614507038000401d03006500c0307030011070080c9090600380155040c000740c9603100e540e03500c64100c0140e587e6080d07034546c0000c6240e0100703030209100c0943c0140e0510b050b000d0f041d110f44519140082e40d030015401078125030b0801500c08184201001c0201c01071904102d40e1a021020a844040281c0021721480e0383d55020b140901d80c1c555106c002c1c000e0588200403502107118042c0da58240c1d00e1088982c2d0709244800500c41200e07007400f00000c2d40c2c105454034482210a840f8200c0c49041403850341c400e03074408011400c1e0041550401c0002c040509551b003c100d001c0c0050002d40001e0110001c542c059401440100004030564048140c20070b000140810800c042604010b0381c40140e41e01441951800800c1c1940700e1403202d206800c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 966172194 1250 966170944 966170969
    0x140d090c06020c06180f060a0f02010506010c11040504021318030905100221160809120a080405060702030a0204140415060b03070e0d0219090b06071a060a0b070b01 72
    0x140c41099845400840180e0760215083c0490b05d10340c2d01c0c1421a00080400400f51000c0485c070034001f40083d00500c0302000003480b286201408107409102d184c0e0003030002d0a01010f90034644d83c034252801070b940e8849000d140c80303801041c1191540071007649103421054091041c000c00c00e0641041c000c140070182c0c0020b210100016440c24840401c3c03551503070fa5406090390088404440321020b075003207040740c4100020080c01400560400f03080c0311041c840c00b0115503c20400041040c01814810703800302a810001d2400005512541100c0c02c50b07030f0a0f01e625880716070f140006404c1841d440c1010b5001824007041941c00740442c1100303403041b4800d01a0004005045001e0b1044500c94020002048020004109160700940c400009458010f000c28001400c941c0403c005085c0c05083c0603a8041580040c04150b10f117010360410140180d400500b000d0f03039a10354081c1521407100440400d1481d1020822944641c000240034042500091f65518018606003045207801d21505000b802c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 966173444 1250 966172194 966172199
    0x421061415041a180405031909171506100311040e160f02070b0d06170a0606080a0503031f030f0f0201090f052805130b0a06030c050708070201140d090c 67
    0x984901140500b01d000c3c3c42d940d40101d5050101420581c068000c6e03505200521001d40b5004070000030311694022555081070f00340c503000700484900f50000c0495510381004000e003c210846080c1036030320a80c12261807030400c04440e0203138014203c007204100400340c005000b00307034031a0001001e03010340f4080500942a032800c020442c0c44101c0781e10b4141c0140c00054013000b10002810103031202c508003003400140e25a545180804103c02c039664030444d504188240c60900c4071501c9040002c4c484d42d00a01042c0300e056440780c0c0c0300c0c4401401c551000e04021a401080c1c84405a807402450f030090302da40030790440d82020301e01c41c01c3c6601c04900140240f1740101e006071070030644400301d9501904040151404030700c0e42407500054040104d464290715400500e036902c0001201c03a6220500c0006800203005091114000d9103070000c100f498200840c0d07001041d40001102e04594000054507184c1d40365100484052017401d9800d0000d42c000704150b10340c10b00c0c0b9801007040a11954404150b540e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 966174694 1250 966173444 966173471
    0x306060108010b0d0908090a0e0906010501110706030f4805070f05010e061306050a140712020d11120f150f040603050307081e042106141504 62
    0x4024083c1038580b401c140414142c8220b50b03048040c85606c00ca2501c0d0a04419101241004d007240d409542c00840c1d90f003d0080520040c031105001d08030030710740300c03080c0241c1007a10b6645003070521a090400d070361600d41d0380034101154005128040002070740d8404e11010440114202d0585501208880e13521645148e9070745200400b8416a0154031044d081000a84440181a044c0c00050707509540314980082850801d00003203200d0520300c56880d041800500741201220030081800d81201c1c901485c1e0403180c00d5080c86290701108915020110041850780500a40030b0800c04003181c03030270710710803004450151002d050f07001c840c4002c1d01100c1e0354098040010740d505584072240c1e15101c141d40d80340ca08044a5014a204000d0000314042d5529592286198461a001e41d184480404c0e0288284508494040099102c208250403c0e040c1846c1c1001c80c1000c0e509100d40d100c228408408102c0305030000b420700b10040015550301e2609203080000d229003514110322407443d102c1980d4010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 966175944 1250 966174694 966174707
    0x80c120901020a03200f100b03031602150c06070c020f011805060c0f07091407230d11030a090605010510080103020906010e130e0114043909060503060601 68
    0x440e05a004000c0c103196601c00b65031040105440c15a00840302c445989243c000f0030a01a1040305400101b2103645582d021a0440e2606030110b07100750020854501d0306283e00d107440c8095501102d002d072909249111215151107011a5002c8134081c0404001000f80c00007200e10001c0d000f42d4040c1d16a4440c4d0300111507500c01059000050078401405004500700400545180ca24480464031003c0c030b203665207403030105950303c10b800c1e16484004040e140c801080513140c1040103400d03c2580d0b12440b002c00d4643c0da072501c100c45584400480d15070010651500415580d80c20070045583c0e905204c9245070240070281c0098481ca418940001000c0c2801c060070828160f4035950040641d00311b60030820f050074003805107410000755400654240e83d07800c4000d43c1d01d103a0100002000c9103159015800d491860380110756644500c01080081504080c04200e081c414000300004250300380202d010802c10501c032503036911200358020500c031041c0d030b0080c02600c80440854000340e50f070000440c0c66 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 966177194 1250 966175944 966175957
    0x30a0c082b0813081c0b0a12021003020a03090b0112020102060c0a2102040803040b04030b060d02010e04021315020a05061f030f030201141314060609010515070b04080c12 75
    0x5402400141000c0480000e041e0300c3d5200c0d50540b8640218402c0c402000512007006401060b95048148903500d05205494010211400984c07848500798000a01c00e10880c6428003d1540001d020011a84290700044041e58440507054086d41c6805d044e0f10105c1d65603200700c3c054401c400c0401c42d405d21300c5041c0c0f1031080c655940c1130311010400d040039035004440072a4a221a0f000d01c4041000c000500140018004108070302e030701ca03851414500c0c01c0c880e0150000e070040f441d6400c5d000150741e104a001e280940240d40150350399566100c0b002c80500d06920a0309258800303c01125a5039000c9204201c9a00034003c482e800e445940c4265000b1607284030422162840c00d408000189800462840d064040c1c000042e0b228290220012980300072140700c040a802510000e081100300840d90b562680f9050041c4410b15107000440e00d40d0206004444c440d080c03520309249441100400c07039020683c840000040c5060500d01100c803078020003100e031858042c4541c840281c20042094890 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 966178444 1250 966177194 966177197
    0x60903180e01050d08120a050403140306060421150e100b030618070905090d1e0801050609030106230405070c1a10080d0801061d0d080306030a0c082b 66
    0x1501c0e440e000402c003043c001058100e0714a17a0a1110021001c00504071510420007000701107040d00d0705107801005212204071000303152100744140301c2c8940301d04080d981903c034006c02e081d80b403060010b16412800c1c118a0b0052031842240700440d550711054005501ca400c640c000c0b01c081a0030254107d0599082c400540d415510880000b014500c010f01f00b0804c0b070406c4010340e2035441d180e03107000c7c050b5001101c02c1e46d400d034099030000b40629400b90a4200d2400841c10000c01070114400c0142041018860140302d1040840c0864203a64290b0108009180310050442102041440b40711149848031905200303615000001e1800307030140e480183c00b01d520482c042891100c200440341c3c0c600016000d9500d8412800002c07030444d10412400c543c5100c541c070f44142030361410800034000e00e203520401407000078507a504003558031030100c0d00340130640c04034081e0740726075500300480c1c6860490070000c0e101201c0000000b4030510007240924174803107851141d00c4c2c013200700d035840040402082c44000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 966179694 1250 966178444 966178469
    0x311030a050303190228020d05030c0d0e03041e08010c03110304080307020c060301120507051e010c05010f020f120603031821030a020f0c0301060311060706021606090318 75
    0x11426a4103030030142e06107448960060a04546c51094030b40e1380c80b42101200c0000300300303418020244d01007000345600912450040d01c0c40c5480000080b00f07014082401c100c0b5606e401011400d00401d01c15039018000540c010350b9108502e11001c0e401c04658031500388154030300000d00c0d09040c03003030250b442200c4500900700d183d500ca41c1d8500400358401450341046010f030300b5104402d6510000198000c1c020030441650f190714030b040c614107000140d84141d205208562821810580c1c8c00b4007941c2098003400c00707188c0500503040c6140944211141100014800500f201b68140000013404e2940314443c00341200c0d130ba801c4107140d517030b1190125030901c4412490441c070552070b01e40450402c513403a0343e03003a20104000520711441e5170400034481001d070700201400d003c50754040102c41c5104108800031f100c41440c40e1a0003c00c9070a840000f070050f41d000070100e040c0030654044480148a08081d00c03c501001d0400350021719855000710001010b48140e401c404030800c40c8142034650030400304 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 966180944 1250 966179694 966179701
    0x20f0915090a0e040f08180108070207061209061509060f08030a0519050d0c0e1005042312030f07030f030b09070e040b09091506010203040f0621020703090311030a050303 75
    0x155034080001c4c012550000a1200d41c400078024402401b00d40a648208a60b41c40c1401d0014088910091540c0110351012030308000081d40541010141c0b0060580011650702e00d0600601500c006074031640d013505010400542d0b81d5103903200004580c0c555941c03000c1c41d512261490707124070403541d6a500046c800c1c013075841e604443c0c1000c006118081d04181c0c1c40c1070103210031101a41c041c22503c40110f03d2880c840341c414140044181d200603868a0641d281c1810a0082a90340240c00095900b80b4080f20801d036441d162104070700780d01284082140e0311390002180b07460890780040e10440c00901243c1100442500900501e802104000c101e2113a560395500101c0e41007410b00341c429486916600c100d004c1d40c41e00c0e002d00340180401806080d0140c02c500900d0302c0c01340085c0c61070f411941308000402450001101900c10b079006d925000e034410380240394909070107240781e6008840030300c001428020141c10001034812030707100e440b0074030604190303808141d00c030824020050310700d40040001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 966182194 1250 966180944 966180959
    0x70303060b190302130306090c05090a06060215041e050703051603020607060b2214010b1201090b0109090212061003200304081605060f060409020a05010c1401020f0915090a 76
    0x24145c24111400190754080d900e0701c0e42c500f40e0b4401039007039681810000b010300c6681001d40c011940301819201c10300c02c2520b00f44000350307198942c43d44054200c50100c086003c000f109140e01101e00080007040850040500b007207901eaa41c2807000315413501c80d440d180d40e0b486120001082c01c0700e400a00c1c41d82844030503200c6c40058070340c030368420364880004e01c089a00070301c030802c0142c400f0102400010301d1724610200c110003404180c00c0f00348008402c1c0851881460341d207075500d040d80d240304408100d02c20729000584602d80950000c00403903002051003030303201c80c9403070760540308a204903000c91036401410f03015800c5980064a0103d0034000d6407654091040c01c1c801990030070300c10f8824900d0301c05c3d0711001d83d6020603101d40890b490b400130824441c1c01280742e90b40c02d40140040f601001a82c180780d000070342031603c5100c3c0c20306002250461a003400b495002c03074138400713289400941d5941180081d07000703240e00111160344180c00c8222122040d0b0b003007005a4200f400c8c0604190512800c02c00f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 966183444 1250 966182194 966182197
    0x80d05070201060e0c0403111e1c060903030f05160503011518030b0405071a181f030606120608070603020c0304120309030b130309030b09031e070303060b190302 71
    0x140d0540d900c4003c001000c3d4070320340615200e54541603000d07454904602d0024034000a14001e14450050300c22940c0001c2c181c2d104407002c001040b00c280b680b000d4a0382000700107901d0f085000e07042c24501603004050580540083c41084d00c02078041056a858a40c1240d400a01240c40e078001907081c801030100c2981c1d03142d08070a1702150700313007601e0780d40b002c0c14074042d07041c865042100c1324114201400100501081900094200040300c4804620214105682d41c01216904c500c0c03c810b1300204900e0352034480c5010303104040c104681c0c41122402c98054080c10741442540002110140520341c040203d1240703400b43d60b40d0801500701280746c00c0c0308401941214000300c5e400c0c0402c200001c1c4008250f651465414401c0d201c04903258954104003a000350020300444560012440382d4001a40c003070402070a50303900c10354104440c3c85265000c0d20358000e00c0300c03c62003c2d030f061100303500540d4074402800205101c0e64051000350744138552003215010340d49014006495000050f06406c0c000e40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 966184694 1250 966183444 966183451
    0xf0601210f0825030c14210c0d0207030809010c06060302040e06070914130b0f091005190e130c09020a0905040b011e080615031501030f060810110f041e05010804080d05 74
    0x7011594100c084440041c415414080303401080c0c000094180002c8c80103204d404034604a40c00644941e0349992038402e000c0c40742d541d00c5810000342000300c10410500381c2c0410082c6070007800400070700c5905c030380e411398076403007a22598003103152220000303488154044030780c0c00d075070300905141d05418030f0800c004054001190001c0d48800072400302c8056440b100103851181c405040d81c11300039403805003031004800300c924880750b80c100f00c0c00c030034081841000d13491900b06101d0325145007070080c0c0c2d0410303861000d81ca801842031240006151042554403505080a45a017154200b2081540600669184401c3d155001c0c0c1d56880f06d070092401ca000d540041c0d0302c0840540010100c43c1070b12213400c0558011a000310304a41c2c00d084004055904d0711034072036007601c06501040400d0826000030307601c1e2225041c40c8411600d0302c54144a454040e000e44000754810500c5070b0b140c940714400400140300303400d0701e010110101c0000065541c03040d01058051a0401c0d0450310340488003204c41c2c0078200c0207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 966185944 1250 966184694 966184733
    0x24050402031b03040807030801050303131401020a02030d0512010b0301030b070c1401050a05090c030106080634090303080c09060f0a021c020d020706020f0601210f0825030c 76
    0x512602c00101c0018000758400c0d80300d4403042d9610040c03440c0140600e50306800ca6806940148031059950f07040100032415079984cc45103100f030340140d000403031900036640c000941501948414181030b580040161009040740005800c03145c4e00c1d07981041142c0801d2000ce0002607800002c2481e0500500070103a030b4500400c50308000412512031182550301c2614056001d1303940302c00b048400c000030711001260920843c001d01403075180012040d552036014016100c400702d80c2d122000311111000c000815402040b202c200d4000d00c81e040503092411910098010400d0300780041c4400e150035088816000008003043d0401000e80d0a1510b41e0308030510708001d500c20201c0844201d01c20b09940240000a41e0042c000c541a080d0003d00f41001c6500100565015840000b8400030126605064400d010414600d040d40e03000030f4542a09801d80141c4200d00f150341100900030b00000420028000708248154115011039404070308007070600c06400510240503520014040c8040c1f07003d910f281 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 966187050 1106 966185944 966185971
    0x105211b0a02060f131a0901060b1c05060109080f0109021005160b090a0b090f0c1203030f091216020415080703080304061418012405040203 62
    0x80d10700c07854204040005041d4000292101821720707040b0034400804407540c3c00f000c00c1c410301680e95040a509100000c1580401e000c00c5405541c94800480c0c02480303414030000044c40d000d0155030400c402d8074000140c03044200f120400346850340c000025501c0d52441045200c000919010091150502086a182d0031a4440d86011908032401c070480d5900e00e140700341070400c03080004290300c1e0b15a043c070802c0c1500282c82500740701c03850221242030044100704401c102c4201b148011992040000840040d0300041c42d98004000100726424441e00d6041040320f40c101440c10006604c0e1a003500040d03150074011240743d080794010401107503003072210442e06c03000b075400301400088000002c50200410317584424a52030900d8240b1041d401c4c103001984c1003248040581d803956003070a1448040b0381040c00290700390b51000c0200301040d03182605203c084e40004006080c000e80c1d = true := by decide +kernel

theorem cover : BRFrame.Cov 966007194 966187050 := by
  have h0 := BRFrame.cov_init 966007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 966007194 ≤ n) (h2 : n < 966187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
