-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2327
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:22:24.873631+00:00
-- url     : https://prove2.me/submissions/75d77faf-f411-42ba-bd86-88593fbc6913

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 418345323 ≤ n < 418525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 418346573 1250 418345323 418345327
    0x1021207240203160e01050d3b07080109030f03091a190506040b150f0d02030a0501060810080d030b190f1809210516051b180c 56
    0x8001e5112410300300c40403441a244407074280000520000d620581d0410a912101880002c0003403040d07800d0004140182d45540c1042d51001d1110090a80700b01002840070030204031603111012000600f07211700e849400c091140b0700c04074446040c0318150b0484082641400005000f00b5000400c1c8503107203800345030010b0305030040c2c1040b80c3d821380d00846407079401d240030047c0500b9050349503500c0c542640b1a101040146c441d50100021500103411654008903601008a81c400d2148040c0032200d42051810340390590b2641010100e81c01151400c00342d03a80c0707c0040c400681d000c000700d03a1101c241041d4000903401c0c4022030b41c0e80c201c2c08880904064460b0284030a0fa2100c185c2018801281000a004541c4514107190f000b0024011011500e450420801d03000340d2174003858a0f030b160003c031041503040d8040085015441c62124040c280041080031100c2248180360304000391340143c0240034a40c60700c546603804401124401d5100e884100720f903440586800c0226500981c3c0c4401c899 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 418347823 1250 418346573 418346587
    0xa170f120601120c0906180f060e030a0b0705030a0b09060d060b030a0b090d030c0f050403111c0f1e08090f03070e040302060f01052209030905030d03020903100209010212 75
    0x2100f6084150f0800c00321810900002c080d41d4000d910030050302e10f140c5403442c01c4800e0483e60700195291740315144800e04090741c104082d50180848007401c010140c01c1c3c900341500c1e6154089045000d0380c00000060b400810001800010b1080706121041114030b08098101040062406443c44034054040b1b0780d03881e59624295400c0106410013540094604140d02c0d2041101e62242d440b2100710300440c2c10001804081c80c0318401404807480700da1149410541540c07101d8510302084251140c1107400c42001442c0c141c0545d0307031340003250300c901380301070702064181b411429030008003641101c0100024840c800089181c401d07140303514815148064a5504000040d2900140d940044215151351003400141640810424450b800030b14030740c1080e07603031401800800048900c040024800440400e61021042d4009008150092802401c200d0b1520002030030901c4089000c17010030380c0000c00c0700150030140b0081d040310b0b10680045007020407810020b03440740600201d605030010006962 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 418349073 1250 418347823 418347827
    0x30906100b040b0318011b12181208071202030c0d0b030313090f090f0c0801060614030114030f030a120b090112030c05030d02130303080f01031e06090b0403020a170f120601 76
    0x80d0f820b00701803001704040f07005000ba01502080c031703d40c3c0301e85c0042d08200c1127051043d5005202c000c00360307004112030a002c040c3e000440d00600080d052404128064646562404007400514042c485035020265103030051041c44c9d084507182013a4902030f4105100300171a4244118445044600c21000880c10b8880c11702054000e05c0c0c800001420015020121424003561500b000c043c0c2d002c0900030002c050311800c083da0a01008860381404070405c10050125120300b00c00100072800190881d1301268030041c603d411504040d01185c006a1040510303082040d140c000c0342d5210300117031703031001480d4100f00000354a5070849602a052000300114807080240405c05c4511040d006c100441d1035180e00030318421103070014802500081e00c000f01192003550f03c40e1075075040340e03401a68006a081080c0c0040030503011158203075052680d80b40c808010600c076841181c0301d180b00b5406806034503900d243c1070408642c65000c260000b4010b120079180c1850302c200300d40c441c001080c25880713aa9904001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 418350323 1250 418349073 418349081
    0x16080c07020d08040603021b0c030c10020f0601090e1011091005070602070c0611010b09010501030c090305030c0319020d1b02040209030a1112010209010e060f0f030906100b040b031801 81
    0x1c01000f1440c0024002411517260b8064500003443c2c8058006542e02d59120560700e800aa2041c0e5054200c000c0842061400b0369041c1c25030302c2e4a0058405481c5080019818003509a0000f00c11603100d401031318403800300340032001030703500b5951003001a50801c410401c0781d801200c02c028041c6281c4081613010b107000c1c0054540480d4810804c0d96100e009240c0328144804600c030380400304913403c030072000d00070042c0500d822000000e00800400ea183c080110058003011100c403080c03080803080480031600501c002e000782883c0c58000c507503481042c04101d034511641d002810454000000000e0b060b503000d411846a84c0504100380d0070000d90780009030081c4541c2c0078040e410310895540341f04204001d21841c00c15881241c02c00011300340e21500909034441c80c0c07291030000c0d1164a10b0000d52900e08003401000503250301c21030802503039444803002e96100303552218850b40480200028007100484850142003c1107155080c10f240200e61040c0e808007509202e041030601108103a44002540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 418351573 1250 418350323 418350349
    0x30e0303030903040608010e06060d050c190503012d091e29090928120c050d141b01090501060b0405090105030607090b07030e0a06080f16080c0702 65
    0x819039a490415001d06503880c1c0c0a1310a400106086000008802c00100c140750321a60000e0080c82c0360000680c1c40318000c1200034403511407003600344581308214088020110741d01c2c0d4035031210b0342d8075410040d10504503008040e43c80e030081c0ba03001e0300c44051180c941c03003003081b03494203c004982c2140618862004501044840304070341d01c0d00652921459088110103a0040b40700b010f016500000800d05c48030000403250342600380c0c8244d0094401005203080d46070000c5a10007074010303840a0340d803403006240a01200000045c81c540000d01401070500c0607218800b000d090030700550300070034000c04036400b0b0304c0c40c0e1100941114444000f22002174010100c9554000c00030091151a400c0061440d0020700485004185c1040045501d080c002045030003102141c0b41c1513034062174143e070703402c180c0d000b02d00031800c203c8142c1d84801503460700950000508003d49034403005150a82403008801c2c001070460340c0b800008101850788607003103106180c00540c0900307a40d40c0e4600074008100100c40100c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 418352823 1250 418351573 418351579
    0x315180603031b1f0f0e01060303020c13020405060d0509060c09030604030e0f03060108010e07080718020f130338040b130b24060301080c060d0f0c02010b030115030c12030e 76
    0x14507604041c041c294020988041517170010007000d6900a180c40c200c0e5002d000c000d0240e0301010100c801c41c40d204c40e5030030240c4a66000989050f440f40007040b400e4010344001c0c98440d49400900c42c00020601c00168000e0b00d10b44100c0c106044040000e41d5082c1c0030780042c05102c100c900803034058807000c405071704c0c030035002c1c00704d88030395942d05e091500a04110003452114042c184001c207440d100858070700c00710b036003459a5100e007104000b0700200030f5100055501c0c00e00801c0100000d8564003d490000450040305400500055030700c3c00040d84e4041d240041048484405c58450502d06002d000d41050f00560307140c1c0503a0f500c1c42c2d000007034844240003a00146000f41001341c5903030183c002d2001c4400400140c9105a414014030001740028010709030150031010481d00e80d401d164024041c8401c0c461804030340102d42040e8202110818401c110050351102d031034040a080074000d1030038200308500c0c0b01508a1458540e07034041800343c0507070707991800100564001d052040320f0b910361002e401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 418354073 1250 418352823 418352863
    0xc06020a050d1406030111070209041b0302030a050f01060b0c030a200106090b0f100203180406030204050a15050a1401080a0b09011706010e0c0a1809020315180603031b 74
    0x180c2040034403c030700700d0b44940b082d0b00b81070310035107143c9008060310021540a04480c0554966035101040d102542524440651181c180007005d40d41c10091401c555000d04d0140000e401c400c1603560070b45090b81c20140505c0300030480d90022540c00400c40742013001d14607040030809910801600800241549840d566003401c501081c0790b0016800380d012070800326451000d8080003000e0110b0304d107003081c0d84005604144014a1410030340c4a84a40f1007400800008039207489034006000c030744d4180d0f107401d170b801d40c1c902882011121858403507001d48401c69001014900d011541e851100000d800c05041240d2600030518290341900000b817072840080c06440d040da1522034a1280503501e6034802d1107841940000548615098003081c01070b4080ea0b155442c1412000c8155208030038007081d2100d0720f0240000190000252001e9401184002720000d4001521000c001c84000075048043c1c820241600780f20340e070359000007200d544404620308070b560f0f450225002e07410018101c01a00d814021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 418355323 1250 418354073 418354091
    0xa0c0e090709151d0915070e030a0308060103050a140114040609020c0a030f08010303020a02090403050d110301050f0418140319120f0b090408032e03020307080d0c06020a050d 77
    0x41c0003014080c0d40704807964440d036280c3d203440b0804903030313095400f0007850f00086d018607245810303606e41036800305441c1449040d210b210004689021a118000d030002005101880140d40c0e050140c95040108000180000c8030300766440c405a40040c401e850301222018000075480c0c841d600140c00400c1030000440d12108041c04446c0c032075801c2641200010040d031500c001007030050495505898055005141070304096082c4030150764043d200780c0900505210920102da5140030303d0b628a110f441400b030712541b6240a020118001001d220b100f107040241d8419000d9170130649241d000e4010b035681c1070700150121414210b1141590031202c514084803242005900a0820305549280c20020841881403240300303030407030b00c904048070b61012010380130501142c1d0010145d500b08070746a0710f00e152103a82600e018030400010806002628886204000b03629080c8006030090044d40050800c001c4c650748020000000010008c3c0320f02d901080a08074035110b041920010342d070a840070400c0e501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 418356573 1250 418355323 418355351
    0x30803010f050909060c1b060a060807080109033c0c0201080105040218010e01020705101716092c07030e0c030d12050402040905070e0906090a0c0e090709 68
    0x10003401205400c1c010303000002600c0c10f00f240c189108502d144094000e0307480b000c1c3e401446038020016042da10022079000b46114006220260080c0c20504c0000b031141e2800800a0520760300707600c41c8190347d16000f00792002c207400420a03440c004010601035007403201c5503010001100da1450308410020100c4400d003a09030004801c02e1018001d0b240d076000ca1b030361002000280d205856071003038140d041d03c3d07881e140d55000d180e180101d841c050064407c51031700c3d0004500f0000000006000240340c90044044910400c5256600030400e5003140102910581c8090000d840c1885101501605442d00654413110816180c51645410f1910044c03802c3c0918010060304080220b0403050180c0c290483c1c080c980090a0f0805038810b40f604285002a02c807400000c041c02001603800607195041c400000b0340c1030000d07801910429900800c24140703045403900e84103000740105050742c090708251001c03d06090914084410082c400c1c4400c5d5156600141407044980c88010f410342000d1219017009 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 418357823 1250 418356573 418356577
    0x81e0708180c0a030204020307140319050a06050306071b150f0c080f010b090d050105010b032202060909041401050403020f0c01051201171c02060403081e0703020a03150308 76
    0x1402000341ca498401000610036260741820303803125403120760b900c410401800e054001e10351200d0b45091020510900301350b400f034036038000c40f40114110752407903001b40c12842034803819420200f00c02c0304102160600300440d0759010090010743c14017085030392803006543d8040701303c01429070000700641c0b14415568500302503c4151105a0118280021100064854900144074100c0c5005040c02039280c081d95050583c080c96805400c05116008000490024007459008040c07501c944c0d5540e15141c1040700c2d8000042101c00b2900c09645450000350b0307142c1080e00d04280c000c0b5041d40312074444d85000210081d100d88440d002d94280340c100301c107060b00071400c0c180c8801c101f0182d0b0762548003c0300458035403183c80c005440300c1161a006105081500031040c00141032801200c02c030700182c08120301d01005540d44040180c4c0702c01c042008250f4050b04403500442030303081c074a1032840081100d9100400081000e0201036010461500c0c20f4483c0d0800c21443e01d003803101210854880c1401d069603 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 418359073 1250 418357823 418357831
    0x9240106080105041b050c031e04030b0903070b010510050c0d2c0108130201020c0a090209030c0406060f0c0516180b060403020a03150f020309060703200a081e0708 72
    0x1c80d15000c00018141014003662510402c1c1d03241d400c0d152a4070305800e42d040c0c0c101090b0b2610501c000e1040c01190440800c80300151750201181644407442d61034a048102e00007414010103401c14402e00d00000c02d044540d6054a0044510215140b65560202c40600600200713043c140301e400d440201d03c58000e51404211038041c500010702440903498541c860035000740c0240003070218030000c2c42a07a1060544c41a89105105540d901100c00e070028458020076000301405a038001a01031091070b04214402c11400706407800c0c800c0c90b11740030001d001000561041d50901600b4105a42002424003120310f0020358141039801058981003204090180b007013a080300c0300c3c68002424041c0c41c1c9941668202da40c000c1641c20a1411a554000c6541d8420034900c01a5101c4621050078102800510b2003001000003c3c55685080f0344020240e034143c0d4524086080c11444084244504100700c448500041c00d000d051519810440f018401d101070310390030800d40c2181032024107a4030101040c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 418360323 1250 418359073 418359077
    0x507060516030b0307080c010804050709141806070507150912050c1018030f090e0420010806150703020307050f03130608100e1810050106020706140f0309240106 71
    0x100d103801896a905c10900509040e40d2104119064540c466285960700611a105990362540c2e202403031000d4600310b01035910503401c0c1c00c01300030021801d200c10704103250300305004103038904002c40090141d03c22410054540d101c00000b005540020741c10a4201c10361100d040350605050880050258100004e00621801050082001600c0d01c0c0070305210203003440e6008080d1090760343c090300d1050116142c2000d010b90b8400026100f0403000c01c40d07102e503004079400e07031103504802c0080e1442c80514200c1814059204240800b9132142e0321420782001c0e4000f00039a4680c0c6504040e880c5000700d020080241c814a5005035000001101800412411940d4a0521529003805449011044403010030407520100104024001d4502154024030407007040182030214190140c20304040b11810749450341c0341c0300100a000c0c1c0c10003a443c010b000030716111460340c00d42003907a0030354840ca10898807107400c007001107042c158042c01101c10440e1014101c0e12101500620408049401d01c0740c400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 418361573 1250 418360323 418360331
    0x801060501090803040315020c07090e0a03080906100b18041508070506041802090d050f01060614090f100e0d0f11040c0c020d03050408070801020d0b1f0807050706051603 75
    0x50074201c0002501c050b291f02441d9420424100c2950700029001340220071105d01c510344001900781082c0c881d40307807513220800260164214a0902a00d0100091302d40d0780d43d940200c0420880d04008a00042a9030364444007950b00c24907400004061022000c000340d201d40b408024100210b4000390001c01c0b00d0021003076820f9903582b80104003007400b0300d00c141000101034891070481001d69030f00074101018000c0101072040d101741c8800b441c1442d403603402001030795180303018410349402c02c003280c440300b44001a50340b82150800106201c10240822640500082010100b600b800380b0a01e40f43c40300080d000d041108005d0410894112540307200382c1c0c1d644880104903859007002c0c01030010042c242c0d110004824415800d00c40c100d084003038140c2c00c00c54144000708081006010100c01446010009a2a41180103034141150403840016101d005541449900d060340c43c46280c600c00c40c0e50410003915a505c580a82c1d442c0700d200802410f0b2840c0108000e91054034040341c045400103aa0104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 418362823 1250 418361573 418361579
    0x150108010f02091e0301151e090c17100e04031205060609210c041503050705030d081f120c030614150d210c02150f0901111501080106050109 62
    0x78040388240c168a5030400200c0400e03012901c0502841191414041c00019242d03124102c0184103140c260040c861503000d0710311010303041c9001c0c402c0001a00864204220000409102034900c543c0c03203d9612442c003040b40050743d01421840583c00404400450600619140c03030020104c2d5200c040009442c0e14013800325a980c14200b054502070304c406040d040d0089403400d1244240c4140404070780d401e12078940c4104494840d40945004041400c0740d0200c071504601d0320380c0c00c040d11504024007071340c030445d0590020b660041c3c1c0700d41c01c14281560407000300b840080703881d181041500f1003500a1145400002081a0981d644003264000c50081248111701417650f1101c6209440041e001140303003070491102e00e084410200014460111041003400e000564041d00e03080300030f14070105030601003440c19800d00140c110125042400028075000d00e050b8056a5802103502c010304000720303c13a15030000f00003045003400d276500e51041e0207425a5a460300501038881c41c01941c2c00144004400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 418364073 1250 418362823 418362851
    0x3180105070c033f0516060c26090a110307080304121202010902150a020a0c0e0703110f030a09140a2411030105090703090f05030901020615010f2015010801 69
    0x128441241e403203840021300040c29421a65500510002445000f41e0068240000c0030fa22501400030140d480b20052640e01d2092460b004807074141c2c00c91074404040401c036040b8004940155420341c480380744000702a02c04046840c213a0300b5000414148400100881c90203003030456940703002e104051542221807004000c900341c640840000f50052000c2210b01040c206000152400c0d022500c103c030022106501c80086110301a40715605606001060007101581400b962652442c400911484c0200c503030000400c03440014050100d8070f40e0390342460100068000c4072082000c2c2e40048491161503800d0035400000d2440030800d00c1841c500764024400c0a03406078000e100380c2100c8990440c1e1805050002d00000280040101230361201401d0015091040310030840340258000c42c0c0b01d03541540007910301f20014103c500e070300c00780403c601c80703581e4412509650802d07a490220002e20028000344200d90004000800d02d000740e511034031402054a5005040b59102c0b00244201400503a01d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 418365323 1250 418364073 418364153
    0x10c03110304031d0d0303020702030705041503080d1e140f06060a0e04150b03041506141c0c0617010e0408091908013b03180105070c03 60
    0x1840c8905200140200c0d0003120145108988008801d61180755080000c241e0b00c1481d90407400301e80d0105071002541010807408014003003e80b41044000c1c03000c00005400342847c0b00082105d0380005500100c224150050b20b260b40403070083c11113498050700c0d298054030102000518403c40d0310005000008420129070213004040d06c450300d002c00484044510070740e00c139070041e0000e450b00c22100702100c00811200c01071220340c90302c41d100c3c2014586801c215030354504880c1042e04009084c01304080802c400c4156007402c81e080c00c0c807143c1002044440042e140e02c00f4025200000c00015040c1c0c21055101d10b848078100e40c910141e0300c031a55201c00d1002541e01030318052003806100c01c142062030000601c4d4001d19a0642c14aa072a82002e094403030440d0400da80301074018120210070812406a000c1e00e80c4128413940400d503001055559014210b007050059424071081e61082c0d008000b141e49864111104078245500c07428090240d10f94900100f003000d11034440d1800c1800c0c4655 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 418366573 1250 418365323 418365341
    0x9031605100c2a06021504150b030c04050406020c0c09041e080f070c0f051f030518060405060105031623040e010f0b0a0b0a020c090405070e0403020f010c03 69
    0x100c5040000034101e002c48840c030005000316107400d42181d54030180e10501c24031010360b4400341090701c0140e051180090070721100300d10f0140c0c1d0801000606c800102220544060a03082e02400141d85040e0000246000305518920340c01501c5d04052105101301070b0018210099090212054404800e0901100100403280a480c40d40c08800941541091201285e442400f0702012420100856920107544d8860601183c9414042c01c042149001b8000710300700070703c0c5c110388a481411500b081c16400c032410400720004c0541c0c820026102c00e80f058032007026501140101c800c2480d1500c0c0c241e98400080c090b443c442e00c40c0e0745031702d404180d0190640d003c1c1d42c10401d0039140341d0074009440700c40000e41c3d034100754400c0c0c449610780390b0036200744981810300b980da030f001040030390f40c03803082c000c400e6116081204000030403c01c1e00440b0f50000392b0ba440520044e280c44029a40e14100380d800d2044c1e03500b01889201c000c500780018541c0c0000d50145440c1004c6c008c00264104407019400c0700c043c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 418367823 1250 418366573 418366579
    0x60606090f0f060427140603060f180312040b010b030610050906070f05060402010f08102105120304030914010e0d020a03050d110609010e0606220c0509031605 70
    0x84a5150034542c02011250310040c0920381851340303500d91009402105100220001c80c0d0002e154103a203014000c5010b0030804201e1000c0e142004400300f0b46a450050490520100440125101e04111703503000424482580980e61981000d003140c80d805d202c143c7c0c040c0c59062100b800450080000000c480c02260b00800c10008480058000d940c00e0b0401c0c035404d503000c41d080c01a01f01003000400038404442c800c1c0054401860284005403888090101910030413402d0030400480100310056072051728140c8820520128460720f26404012a14034010001c2c0600e41d4012400101d00020b18003c1e031081e211522159165006083c0c001122420a800103400c28807601c00b40c2006003195890f50b002808202c24181c407522500d2600100a005a00250030300d1180d400081c0d061203035540004040300240070b00c0000302e050560368500902014402c00260000b0441011003502e500c5194100031414000c480d0300000c05003041d0800c54004e4060301405002101a00e1205000403d0320001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 418369073 1250 418367823 418367839
    0x503031303140a0204150e071805040b1306030506010f1403120307170f0106020c090f0c090303070c060302070606050f010f03020c01060302040504050d0306061707081b07060e06060609 81
    0x1d0b40391609004419038a100c0140183c3c5000c0c0302503111402142600561514860409071074940c0f03d47c480b1000814000404c1641080e81c000062500c0c008002ca40c01110042a1002c9100c001061401e4040d0541c00603450007030700208024002c11081d0403a40d031500050800c960b51030300c00803c0c80180c0e04043e41900501c04501c6200b081501458008095280c100d4404440303180c030b900d0b20341d415070303d0b889402c241a0041003020350400039480c10060503210b20b01541003801c081d9181c0030703024065407500a07002ca2064002d0b2001c000380c0e00e05070b4014404030342c0da55031030001a00039403001e00c0c1600c480b07040800100391820074102c890003407141a1b40d121040703000c810341200207410801550030a95241c11000001d41e40740e01031180110b01602c060130603030490900280480340903500010074401511039520312800e400c1045035000c4828180700406948281590b0b00580e0048843c0024040102c1d5003400d02c4160fa100c1450403000c0707400c554840d100d10382000fa850051410040c0e004002c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 418370323 1250 418369073 418369079
    0xd020708030f2a0c280909030e0607111003112d0a080f0a0504020d03030504080912101a0a1a070611180603160309030207031e030905030313 62
    0x140d800100004041c46810b6003483c0c090f40c40303400c03080e5000300d0f1a0050344c1c40401c40c001c10b80b900301c1c80c80314440031441069400301c081e2098071242107a203104d203003151582c800b5080c041c94010010213000e0308004207015a45d61080c54408080e0101081003805a0319100d0400da64a000b481802030f80c522001c81035040c4448800c010810306043c030714442d01c903d5400038400f1010b01a002401d0820309503203a0181900d043c40003c40568030003000e005450b4107003002e000240e02c1e80d03a00d0010b810303054a40429140c4e1380381440c43c094494080c003550400c0451803050081f81c4c1c00310300c00411705c8441c03600340424256803801940b6901815509030703000c1c520540421007624440c0c2d00500355442d0808803810485a501d40c1d030200d82441d9104086c0810000c0c00018078440c4408003150108202d8499045081441d001c141c1e4940d007000c031005041e6140c5d200c0091500070001040116803040d0841d25051000c0710304c8007005a60380c4101c0114003495000705080c600881038031060841502089520f901d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 418371573 1250 418370323 418370347
    0x20306060909150907230906041a0412080d0b12070605070c03080a020a02010212040308030f0a18080d060927080d020d0c080a0213091a0402030a0902030d02070803 72
    0x2034040d0042e4101e243d03401141d6119112025a42c4c458041512a0304030769200308040346041500f11204186490100040195070740c44034240d400b919800c8003410a0000142920003083c81143c000c5889820503459000c200300c1550020311195040760410f02180d100e05c41800400b0907210804021a008034409102140c468406066543d0051183c40189945c988418180c0c0e03002c15502d0006070002481c1c01f0075542c04210307108088603405550780c54503103543c80d01060707404040e200300b410959840104003089a070741c014a0743e14019100302a0300d04610300d03112500354400c24901d000181059800918540b01b84104482641c6550510104850686851003050300c180400c03070728805c0602902805401c140b01506007107107101c00c0041e5803000303407070084c00c10f80c00180140300c014010440c07100136098001c0d1440031207002d00d1010407801110004900c0310420b00400541241c800f204000d001c01145d00040242030094080d9103854016110481e00c5000078050034007650320400c08104840 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 418372823 1250 418371573 418371589
    0x715090c0510030b0613050907020604030e15190e0f03030c0618071e0302032a24120124050715060f1e05040203070c021c0204020c100c02010203060609 67
    0xc2610b1400003900c0d0b104c0c3c2d0000d0309a401035400c401401c614801e0078021418031100300d9070400c01ca8001821140382c41d40c3c000b0616a012000c0a000740355984410030100e01031015550310303d400c03117036403030505032001c4000341140925401c451045403130482c44e84060601000710b455102130007010702403a44da030050051504400c66800052031084020010b07030f400410164045145c00218402002031960040601d4a08141e4000c0d01303800c0b00b2401c4441c190754290f0b000500300c5054845c40c036080c8981c4140158049040d211224086001456810703840c10350f20036905a07562501070841200004820740128101620711070042041009040041981d540e00c00b40140d04540c1c0c0440c1040d2a07000504042d01c060348041250402c0c240300e9071006078458485000740c581540e00b10b00714030344980018109110030030040c0c060b41c0702005001d21000340811030014181c019000399030f504d85010035070313a9502d40547d00d000403034680304020b80c1540c41802141d0054000400a5040203042020410790b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 418374073 1250 418372823 418372849
    0x609021920030f0703020d39080f0a02070f210c051e040e0d0e0d030504150c030206160e061c050f150a03020310020f1605030715090c05 60
    0x1181c03030026030711451282040200059010703240c456854007030a10300646040c0c0700d1020101808060380e0900008400d12084a000c00d81c2c01c00414101e40030382d104035015510701a4041e0542c0ca000030400700000040006000b404d51503421a06407681c6e5411941c1002414000e004040c55105500e1003008000080c0d011658001c07500130508071307500c6000503c054032000700b00300d80780c422040e040c0580c0360612903001c0320741c80e07030001d000080040d5030000c0554505072070140c8116a105150820305114609450103084000c00d1860058500b2801802545448204400610902001440b0303010b2514a030003030b00c54103869808103c0c40110410980350130010380d803107200c0d8803c030700756448030f5003130044a018018103c03c0402030f0900d00e581400702d0850740c0e05c4030301511100104100685000880610140000500688860001d0340c41c00e040e100313142c1541c01c80c004000036401840808001005580d11034030141d0480080201c12000f0703103811001c00703800307810309007410021801c10400b40044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 418375323 1250 418374073 418374107
    0x50f12060a0b0705100e0c2805090f1f08060406020702011e0c02100e01080c0a1b0308270a060b01140f07020a0b090d03030c050f04170106090219 64
    0x405502c803100e1010681040c1c1c02074500f80d10141e03001550301c1440c0304209041d03404034043c0034043d82410100301c40401400000c401c201e1401c4004031488070f40d11407040600b40040c40b1541500304080038002c0100c003a200700f52910401e424005000e40c0055405048548c40e50140090380d03180d03145c0d48000d4121013816414017041080c0903403040074440300c221341d442c40d60311080810300150040c0907800c0a0303c1850000d00c00d4003000d440b4140c0c1c00000e40c1e40c1c01120140c040741d4521300300108540c88810b0303074060703503440c07294000319420580c0298100b80300b8031140c50b180c0301e4040c85c080c040d2001f02000e810302c0d082d6001020b090000c038929030001207440f94181000c90880b0303401080c5810702d60003c59084501040402e1180840c41c1014102009101780c02c42c503414034840c000091040d0070818001000c5c90303510000c0711201801101510b80e078182140e12142c580d0b03a02c148406212072407850b040070305d500e810808110f4410620a0f100d61440c0088094220803c44000b510000c9140200d820 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 418376573 1250 418375323 418375339
    0x80f010312020a0c060309050c030303010506040504020706020d0c05030403110d0818070f1412060c0f031b07080304050105070207080d030e01090507030606030b0a060e040602071406070915050f1206 87
    0x40861300c0c004024005000581e03001400c0903c1e41415400c00366082012440b82d08100300420060307541c0300907182910300c110380050780e43e46c2500c0d011009108003032188080070300301820740e0340b03042d00300c000346200318001d03210740140c1049040c00d1500c503540480c101700800c41d0701c0b01180e10901040b000b40c2c00c103080c03c0300b1038840a845020414804801e580165021141700c50320002a04215030300680340c03e42140240903c1c20b156450407050700903000b000010440210019840e0b200300440b041c50f20b000603801c1c580e10303945400d140e081544212810703225907081c0000714020502c00203006045400c4040a01681d030402c0104501030007401d240d481c295034a4403d04000f0503000d0081100861082000246071440c5103410112010003c003d02e40a40c54118204421f00328100c0542e4840ea000b64016aa034080c3d141c00101401c1c4050586400e1150303404100d081030300941c141c4c041d20000110030035910300da410216524442d105400b25a010217224060560300341058968000d28010040a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 418377823 1250 418376573 418376593
    0x8010e10110d110d1104050a0501030b15130e01051e1215160206100b0a14071b0503060105030d27271107030219211707080f01031202 59
    0x2c0242c816400001103030034000501211040d0041c0310354000f041d441c1d00010300309403a001c0000d015007a03034407425040c503071514168603203560f800380d02c0d01e0410400740c01c2540380d0310001480f10004265006031142c00030000004a110314040504001b044010b0515800e50020302d0280540e081a95940e907009101e5100c402003207001e84900144030b0007003c44401d41034106803100034940600038215011090100c0c0702400b2492102003140c694402e0340c00c00c1c0d000150340b0740309000702e8400ca0300090721000620340f400000005d1140b00c001110801c40c11074241780d885804058a92401d40000c0d000f095040302c58407500d520032500b840c20060324840805070f641d0354038481c2d2050040c1d0074640d002103074140101009071100c0e22039403402e411740f08035140c10052140d801964a10609400000700300a80c0b118104001d1202d00b450004003003400302e071140030030100d00501b040d170104003175108906040000502c3e0502c0f03140a544100380884140850f6440c5864204521184400d140c003180a40c502070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 418379073 1250 418377823 418377847
    0xe010f020a03090c090e1c02120c0f0106061416020d14030c0105010608130b060a0504060b130902251b030f0b0a09032c0a09020301050a08010e1011 65
    0x6041040007a40b0080385500180c80e0100102c00c0c1a0052940c07649058080442220002000416945d420b03542d0103440508000691800aa400490750481400a58010610302c08600700c0350f07007280a0700900a0640b540c0c815510318003120314540800794140881d00c072150038280e4840c030b16070001c0d00080586038252114901802c4807240000d0715880016103000c07a000900c00c0d540102207510b4405158280101c26210350701e08241e000c2d00c0e102d462800310328140c0c0d0700ba003004001c08006008001c010ba859048400303580101d5001007410800840c006985801c500845a40c035038114030024040d140d01d007222004044410f41a1260755001881d80fa2220f41c01a4282c06140a4030b240141002980340401f61080d0050007243e207141072800c00c100180d0009c0b146c40c80c0c22002048005598080c0c07020103c4480380c105611b6000d8072940f400100d0b65541d600850681d10162459406151a103d80d5800d8881c2c08240702415404020984481c44039680208150003104071454035016190212b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 418380323 1250 418379073 418379077
    0x90c081603020703140a0509180f04030c060b0a06110c1507030507030909020c0102030f072c0112050f06012006040213090615061b0b01030809010201091208010f0f14040e010f02 78
    0x11b88003141d400600c0c030602e8a006543c01c011a02c6021180e240342c41c00c00d005110000025000800f8404c0c04100070041060315004070f00722840250103d0641d07661440010066200d0f904038200c1401010340c40c08503824559118803810b6040080e640c80d010351795408442076401510305074104000ca01010401145600080960310502e0b800980c80707041c4000143c144400c090405414010441503100402d04118807440803900800030500c0703415524401030380d54200e458051080c2c01d1034003041156001010302500e004000170303620000c14840f0701114401036204090040c1c01544202d000400614054107420200a1840804030340301805aa8103c00c1c0c4180000030814602480310501140d43e00034002d80b00e1280c6c4a2040d032484810307841d62401e1b08018000a41074143c005403540395130b4001d4100207661030b404120b900740c28400f039100802d002002c0c090842245540e00e4002901160310700c1c8401541e6607000c00c2c420103981c0c1410040200b0382d41c1107240095481c2c049400d82d05200b440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 418381573 1250 418380323 418380337
    0x501060c0230031903050601090e151f1106060904150b010504031a040b1f03110411160c050603010b0a030c0309080a0c03090902030c0a050a0507020a030c090c08160302070314 77
    0x2c40340e0000d6a42001a01b40c900c001c010604000005100f0003444426a07191070304160300d03584035241d01e0314070400710306c00e80f040c00640c000c00610b44400a440561103034152541280900a0ba0119128081042081442600d02500149030712a01c600c1803503d50b84542c21181c01410854613095603a0345141003060b08603012100030900408200034402704a031a26403044031201c0007412604007541e0040302048900000e04a2141c07041c2403c5240c4a9a101040c44c012004209440f0401c1000300070340d040c041c00040320b81d6203080c40009020305012003501d040c4e80c8030540c0300d424203404140840052418030540b00400d905c5a0140012030901c40060000b07805c250f03107020640c40b05040c0600900300303503801409000d20400400924210f68010b81301480b41d540340c415070380c00e6100310446460140d51006580140700c22000010050484920b40449000c1001440400a1050300f40c0395038030101c400143c8040c030084511191446540101822803182c00c11048140e8107062140e03650700100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 418382823 1250 418381573 418381597
    0xc0a1806111e070902070302030405040f0204150804020306040f1505040c090c0e0a0b0307140409050a110a020a021012050a02070303060519050904080c1903030501060c023003 77
    0x40c40e420701140062003500c0041001000a00040244a590590300e4440d88600302105601040340030400d0301c28021940200300c002c3c424400d01041451103c020b50003445000b4401c0148001000041d002d054428440e6030020301404240c0d1b07440d101c0c55000006c2c554101d80b041c003542645401074645205290249000e86404d203006800c184844003202c42011030401031210450040107031b5070303508170300000b92a1078400d62030703e90f1100403041d5400c402840402c080f0442c045004218032145600c0940b080e02c03620b03014844441c1640c0e0003516032080e80c049000503080080c00e540507040203085a1401c54070b0780b0f8414428800c484811044440640720740f000d00b40c00080000506515010744409131400f15601c8404124107204485034070310a11074140100b000100203000d2064507030030303070314a02c0740030f010f403a0100417070086038080d00502d440c00c90100e454031001080482c820908403403400d60242c101041050741c03c00020a4412009022106525103082c1140e413040a0001c0c4c04804084 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 418384073 1250 418382823 418382837
    0x5030a052d0a0e0703051f0e0f0a020a05120a03030c0e04020703230a0915020a0804090507090b04141203041a0703110c0901140307030605130c14090c0a1806 69
    0x10010b030190380c450380601c0d03015805024140b003c1480407030000f030500d0030a4002d001c08010701002002070600b90901000380c2c003a09150102a80c0701003400c075442ca1007142d0707194040343c0b43c00c00c02c810080e0313103410713401550700c4910303030900081c00385d8000d0b00b044500b42408440c1d0401e170740005082e6404880c040700001c2c2d4044541c0c40340d20150ba940c1040306404e0602600700f11111200074000d084c0d520031070110210301300d0400c01c00b0307000b03010b8005401d81005810b56955240c4230720601401d0700381c0701c02002445200d0001480c1c41076905513400e45005e440501000d5512a0411501136148958a52640410440022401c0418a03a5110524864071054458242d410040d04282100079180904c1d085604440e03441c2d50740d21320b218152000d000c5011000844080803070300d001d0310340d00002e020520b003809000d0104000000c0010310752107030780c15198050319811806000c8072251961900005031402083e401c48054001d00740e040c3c0c1918080003001e80b040c54034807400a841e170080001c2450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 418385323 1250 418384073 418384081
    0x406030531110303030c07020108100306050c120a09031b060609020d06030b0f07021504060207060f020d0b0d05100509150103080a0305070305060d231e0601120305030a052d 76
    0x42610b00e8a07841000710041c5066107000902c21031a40728400000381003240382c00c0021030008040380890040c42e0441403c01c10740c49c3c0f404400f60760b58880d01112100d00c2c13061000524001a600884040c554983d42d05402d10121448000021465000c21110140c503550082981a11840078041c0d1030310301440440d0180ca1800d004895503006070a08040110311800c0004040e0009611600c241e2903407400410313503031103080c00700003400303582c1000301000e081c00144c00f40f5200301e03000783c5000460361004000211821042102841001500900e1904180b2101150000603404598040b4401d0140c500c0000450782d0012040e000b40c100302d800d800c1c04240a14620b41c144203641c2d02c168141000c101c20300349400050704020b040d0380020a0103186824000040c4074600d45038100e410707000207c03090310701204c00425141b0200100b041040c80384070000075403038004032903a10400c1c1c1c2607102e0342d1440e11150003400c0900310080c20522215013114034040d182c8403200401002c01502a40004c040c10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 418386573 1250 418385323 418385333
    0x2210f070521070f03080703180c06080601030608060f27161202010806040b03032106090a0216030509040b0603150405070206011a070c170a12050403080406030531 72
    0x3001e8011926409002c3c442c5000081400c0c41c5030451542504040c106592041d008502034101c4a40418a2200c018202400c102c070208984080d623606440705003c59540c1d074011002c81c0c156100f251900d0380f20001041c0941070a941c4c0c076400c0528400310044640e080c041c456a85c4015001b900c15513800003004030075154100031010050321800c2004c0c8400102c3d500000d012803005403e440c80342c0c1d0b541002c42c6a5507400c10032660207080c0d8440b102a014000704141d06010021200c0e903004912260000e240b070b40b090320031505003200744a01d0301680c241c1500c3c200c1d200e421891543da0410ba455104284940d90600a10311480d004898207403d10006000c0c0030a40c0e90142401d03040d58002001071001400c07880d15501c0c208002280c0b6078440c507036410500f6084c10725900044910304d2642e40d146003070402107042507015020300c0c03d00d0040c40c07403144115043e2040e80f02c06003403000c05001c103010f524400c1d080300da00a00120300c100c41d41c0008208002040c28050300030f00300e01d541e84800d001044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 418387823 1250 418386573 418386613
    0x70f0503071a16020a020a03390512060601140307020102040b0f0a0e0f130e032a0708070f150e190612021c0c09030b0f070e030d02210f0705 62
    0xf0109101905017084240d01044411106000062420a030001910141140f2180c1d000441c1003260014030403c01d06562040799030a64041c450107484403000c6d14100743c1d0000355160249406a498000780f40e4989441c00c5a030300b011f810402107540030080055100783d06405442031525441c1d0f41d980d03c0718909005010135118108460064070715070251009503440c541d40d08052006880042115024041000d00354032400c2240c8a5044241d004030b682c82011040d8100c003001c008007150900340e150320245542e02d90904c40c000010300c86803428010942c001400c0c084454050070b00d9940035050308005032012041441c3c41002e01c090b40001c004665010091400304070b41650110720b44ae0740084040c0132905079841d0343c00e0300781c2c031360f40c0c810b0708517105041c00341c000e680110b4000030500b000e0a02440303201d015502040021581141c008451402080901003a8581e230000c2100140c8801a81c10980b018204114072280a102142034800c410009084080c4200068116101504840d840d55 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 418389073 1250 418387823 418387861
    0xc0601090b1c050c120c060c030702040b030703080d1d1c080a060f03021915110c06041202090901061a030a050f040210050d02040f03080c0609060903070f0503071a 72
    0x10300b0604980c0840e001040c014112002590354000e101c0407140c80a29007800c140303059401190008180201c0840032015100311131084405025115620003010b54540450101500c101420001e51011098603400500c0ca18410710104418800c182580c50a1042940751009052070344085415580c1e406040135912120398182048050708060400528415030300009014136410010403075200303070340340d00103004100b107440c0ba1a00d4404040003c3c03800c8400b200e51040c0c0c0c401c003081140c4500c5e0060545003500c95010070a224000107400300070304000d000d8200011956039501c0440c1c28142c51619007900031400c01c100b9070b41c0c00c0c002d03000000c60340b00a044e84880c0201d0b0050000503924051400014a058030340207488810301001c00009103d2b0b58025100120602c030000100a19000a8940c6404079001d4036015038a44060390384a03801215000101d400030040240014203140410f0b502d1070180c0201d9003404c1c41e1780e4405e03941e80e0320b486804c40d541d80e101081090841d42c00c1b480c0300328 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 418390323 1250 418389073 418389109
    0x9031709010606021b060d020a020f0f0d080703020904060e07020c0a0806060303070206180303131d0f0105101b0c0510020c03070b0a020f1509010b0d02060409020306060c0601090b 79
    0x20043c600710009484000ca0590070305400301000e0000d40c1c80d80d0f0007040d504a05811071046555004064001e5640d616001091000b4050ba10981c180c0b4000031031204101400b42d240d0f9410b81d903d042c0c0441c029400119810740c403e60721790b07020500c81070a4501d140304140540003420401b4038031040010200c61a4410b2905521030000c00c019500c020050b14a46507050b9013154448860589031001d05103440b504030b40510010039030014038400c2c0404502260b101c090002020341540c1d0301b403001000c086070400d5017110035400420a41c28000d0003d501c290152501c1103003070920343d8140e0003625100805a44130006001c0512452411080294641a85000410f81d071200c03580400d88660b8940301e5030b4804c007004138900303103030741d000344410395041421806450380d40148215a005840703051359101c1039580b038441408940c3c108101c601c2813298004264078105890106804044e500042c50150403000501c000d000314a010410140605503200000c1043c12480d0180094100c118040b448 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 418391573 1250 418390323 418390331
    0x60f03150f0605031e040516060f0f120e0327031911010e030f010509060709120204050a02070804140f040203040308040f1b0b030603010b041401090510090903170901 73
    0x10995141030000000c603840d034107107a1380b00d64880401c00d00d4051600c5404000e44c1400e020041001804600c18441c0c1e0011200207421586030501202d1103500c80b03400c20081507071004003a103071500035030201d0107044c00074602190000380003542e1419900000d0580072211540c20034801c098070580c0c09183d03507800c280c0c0100031011070103044090443e994240a00000070b1081d08a80a034841d001b0100c045d0300160454100a541070091390007080300f1540201607016880205c0e100c544103032003a8007241c2250b440c8414450b03991302000300400000e0b04910300d0380c0d801c11081e400941c01101034402440e8100441910038000c0051244118041c501c6c40d2141d84104200800640c010142c1e03078200d0f41014135500017848a1800899081c1d00394114000d03200640800a4010910707401140b040038254000c0c858a8491020300c410703140301c0c0541c420140c2404006210004081d4040d0758802e1104034a0a036055071804020100d41171900141e0004040b40d0804d280340c12500101350f04206900001c02c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 418392823 1250 418391573 418391579
    0xf060c03011a0f1207031a010f03150509040c080c01020111030a0b0a05030102030c0901090f0302090415090611071a010b1602030309040216150204031703090a0507060f0315 76
    0x8049403105004100e0041d491050300000c46000c0410f488181000c0c140303065a500301c2c00401880c2440880ba004e002078204038621158001c0030f4140a102d64040e15500344041401c1d4059000d4031441108003020317001004005925038030b114010b406280034040c82400305041220781c60406207403d03401415681030041d0419420304600850390301c04407072a40040e4400100f0700040e003124003580003e9140d070021085c0415050050b000f44902102600c800b400c00c1d542d00b0000780035074600d10010394880000000180415600340344032030300746503e610004002a00381e03107034011a0040154401e1203540400c0420400c6104442c0001c421460030b0707007045542c90098484158030441c100041f00c00b18190b400130854800f0010303183c681c43d00600c295292105511004801c000036034040c0c0340301840c065900c800d10114400c0710162a0404c5114405004140c84144c49600150a184581c4150340c402c00104034140000c01c081c00301ca075500388080c403015000405a4610301c0d890382c01030103070003010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 418394073 1250 418392823 418392841
    0xc0a1a01090507091a130303030b120f0c011b0803070302191e030f18050102030403020d18050d0c08060405150601030c0c0f060207050604110312030105031e101107050f06 75
    0x2080456810108481a186440780301100c03030f000b0390344a440301041c6c407040441003540640020b00c07064429030364100c0c0030350b84425165036034110380240d000940040c03481c00c00c554411074803500c0000e2001ea103851441056551280c0780c5d403040714141c00203980031491761030072442c000001c803ca0505240c4602104484600d100580c13440400100c140360369011804814070047d08452644a0b02c1008161112003908041e400f075841110204c00501030070388182102801011014411102c099481854904007018058850950002582e001ca02c9803000500d2010070080f0328801c0340b0640c064000c03452210700707100504602414440c140360810981d804003a900c04610040320703400c030444030303500200d0303080210003846009000303416400759404000501802c10160150300c0d9085d401c4411240504903011001d000078010554142c1000421601c0d05046113600d408902c2003905603880c140031070348210126000c4080003803840380003242030710500c8004d200c400c030030041120291007245408521 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 418395323 1250 418394073 418394087
    0x50918070503190c41060f09042315010e1309020901050f15280906080105010509150c0f0d0906170f0105060a030e0102030403050924041502030c0a1a01090507 70
    0x140d44111041c01e191485c20380584100c107420f03c4130103014286d8401540052010940c040b5030b45c0c60155044c054003400030a0750500349441c070b40c0111700180450f111046d001e113200307280b91181030400c004d081045100313075a0001e541c0744141000c0d40c0015003402c1841840f41c9240141d11407440345051040c84c1c80961282443c9c8090340c403c000845584041074064401500b01d41041004161548000390318001c0c6c029034144240e82daa0707100c01c20260303610001101c1e030f84280c180064100412f02d02c895440c01c80c7d1800b414030304282c54196045040a00c50403840c080440c1100000100d50980420000b0341017003003080b400c5102d040b0b001c158941050740c1c500d90403041c40350b94060000000c00080c81c41c800d520003942d41c01200029035803420b090400610b2500b1403444144101101d000100035080d0315111005103d42460601d810107241010004601d202d0702008019800200030700242d40609010340e901440c8a1040c4030f555020b01c03884000400c80503088a82c009250400340040300f504595 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 418396573 1250 418395323 418395389
    0xd050702010903051c1d0f0f01020301080a08070f060f0506040606020606030d0807050d0c1d0105070b041502040305070306050f1f1a04030b091b0102010204050918070503190c 77
    0x5806045d0340100751408024442c02c461b107902410b9446258140c1040452038140e4003900ca811074a0409410300d0403400c0344403e1190003040c1d800041c1d150f0000e50040050001d09000e603103801c41142042e00c54005030b40307504000103c03150f61202001368925003440342401a08817480140402d1502030082540c030416443c400c0e040c0f100c2100029040b9100f00115104c0c100f4904043c4921062420041d10301d052401490105521b42d4040d060a035200e803040c3c0d60103c1c0c003e201c011040c0ca494032580d2100034401d104240e510307020000400460b80400800005612403035001a40c0d14003490b0002d0442e1002d054006000c0c130200708030380b0b09101d0308454426039615240440a00d40c0c4180540e02d2441280c2c4028800003509003081620074000c41c00206052030001e140f0340045003880128201d10450140c26030080b610008140b0003101c10345480c1c41c0261360700c110341055403140002468050114120041e10900e03001c420100041c0c0142d201c000c2016400c07510303031020040d08580031203034900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 418397823 1250 418396573 418396597
    0x90804030615080a030507030305130302061513060b031f0b18210c09010b130902030c0403082a01090308130f0204060f05030715022815020d05070201090305 69
    0x4400301c1d80b520000a1032400074007051080710107103030142c41c001d05590808174054020070f00d0100010012881040740c2801c29500da4040c2155542d0b440703007840303c1c1c01c840381150741000a01c4418030180324548039540c00f80c42c034000c42945900d01004460001a030880380303081d01504691003040a9030400f000da40c03490f40c1c1c0303061182c00c01c4480008940c8030a41041002d4044410451080d01d11801040700320900100355050b5080307a8a4518040841c03050302451603180803d034008002481140d805190403494012043e4500b80e500e0f1070703850081c0c001603003c80e0751100d009000d040b0034885c1c4550340d1403120104000d0201880944001c7c1081600800717550302d200d009600301041102c035007069400380343c0c010420400385031a84006884442a03025090180c0f10700c840118101134000e90001041649500601040244405a40050361850310b00c0340e035480c0c4c1941840000b0228041101c141c0b20740d440050b150340e49149454143c541c094120700543e49000d21141c0402ea00c0f1045608003950340c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 418399073 1250 418397823 418397831
    0x3061911040f061d06030a0504121e0f09080115050901090b090c0f0714240402030d0c14030f0901120216080306060d050103050a0b0115020a0f062409050a0908040306 73
    0x107260f503484c81d0050010031591100f000010004100040e034403417070040b401407800d1580d016603500b065922440c03074452820400308158441070500c3c4150b10608810b000d62a184080390b40d910340c1c15080d6800c00800341540480c140092016041006805004240c0b09c2001e00c008681a00420b8084001038200b680715500014144285215041140c1c00c50340c0c0b152145142c18a030b036050980703030b5081c1901d541100b94401c0c1070311a40040d0050a03406550002e0113848051a1508143e641015051040350680f12003200141d1110092014001c200c0445402540d10800300340010f084090140d501904148140010391149000c88070303803025541d01031840c43d43e07603d400001481c5402842a0780c040349040038008410403101041c5030035142c0c420f5081c81d05690f22004030b02000c040c0f0b1140800141e118a280c1c0700465544103403a800b89004950000d4810041c6003500c4580782d00d90310300545200035050401c80201d0912403582d05c034144501c10402024641c0d0380b00c0340f5104900c8090091621 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 418400323 1250 418399073 418399097
    0x30415020d060b0a020c091803030c0306011404060216050117060919020c0a0c15052709090a050d03110a030f11040f03170322030c0203061911040f06 66
    0x1607120320080c3c10440640e80d26040e805000a44e116000031030603028200c03d902003420803004102c40031907800c0d24409141507996410281c041908020880b41c104207509240180281c40790000348003404117a40036003401d1000496800c450700301580f125040049042a0041103030455407220f800c4001191041007545803940b840b003150302102024202c5901c0014007001d95039000510040c6244510a44000141d542d0b10020741000d010140c0720110700100101192004120105001810144030070352a006101e400314403105400c4901103085da01c8121104140314042140e40d110540b140317001e000c0e40b04600100e0708240a881055400c2c56103482402caa026100e4000c040c01c00c5114010503141c5039280a0b040355501c0e18441030740c5111203140d910104a543d04100c0b0b104480381605005d074030640d01c208100030245001c05500300300014200e000160b40030302440740109051251071103080e820740480002c85481c09007070700040004120800c08041120107c2082314a40d00b40741c0c032090a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 418401573 1250 418400323 418400347
    0x9060409050c0402030c09041107030509010c030908010606050c060901151406120702011d01060e01050609030c0904110a050307030c0504410105030d09050613030506090109050c0603041502 83
    0x20820350302e00d43c0140003104009604054002a112884003214280300c8880c007154401c2052281d00d0001d03001030b80030000030074154054408564041d1007880e111854580d2408040d00311a026040103000401c006060400f00b1010403560b600400004020004001c1d800802d54000070305214401400461141e403071919500c80c41540d02e120440da0a508a51420050081c02050101e6070b43d004203280f2900e00154610511400d0180e0346102d58a141036428070080003500e03048440307c182c0c94030848400341001c0d100c0e100c180c0d021343d1080c56041b0404020f80208804040190000c81c040c0e84804410000704090340415011581e00ba5000646608941c1c0e64820b9a40c1045d4045944100b000180c803d641c2d00040c0c062000d1044070002041740d0f01d800400d0b0701c40340c8003800d40c1d0000310311800a101a1030088024090b1040c0d000304110141e54036a503440c20410110b4803400965960320385401885030601038000c0c044000c80c0c4031460362501d940e0b900c0019084070862500c090b408520180050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 418402823 1250 418401573 418401583
    0x90c050705010510030b0c03010e0f0a060b121519030b04110d080909070905132a03060801061205060c0c01150e040507051c261201091a0906040905 65
    0x41d085402030041c0e1070032550b807159201d114070045600040407800698140e0402080e00e0503650181650482a2104680023608400280000140031f0340c1d1a400654500200000e04070015440405c003800d19000012441001c0e54003000c0340034445140d01000301c1400c0242d407100b07495000500d40d05540b20390400403080c5031003000083d00039680681c142e0a001d00b10b4060303ca4203e00720340ca280e842c0e962181c01c548d00c103d544103042e00032201c80f031142c0f405a003e4110801d220440b0f50114a420026100c0c3d00f510b91040520001181d582c480030b20402c0803c6c00341d00082d105454000000311003d507121f50713680c4c9006003020040000400c1003400c1c04000e41100c4800c0740000a00703c81540c9905404025a41c03d0f14120b5207171240780000101402c207c008c200000d54401c445425904180d2211001d80010820342c2003c140000689161580d4030006001c6400161214032029030410f40101d080b2606207030304020084e0501e4409009603580d140030341e80444203440c0802c01c070b1011700e4028684 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 418404073 1250 418402823 418402837
    0x706110d0903080f060406030c0302090619060302090a1202030a02090a1b0809010b0306010602060115030e06010801200f091309140d260411030a050a080a090e10090c05 74
    0x255007440248014154056001c6005a00702c000501880d11840204412030360144801049400705100400152506410040c0d01400103020564030712400710111182c0380c8103400500201b58003048a003400d09202c3d01420103441840c0640e00c003460303103800003035485400140081c8110341c494001414012190030039103170010100e000155440304a0005050410110f668100940ca400e058440c07038a000100d1300d040f14480d40107050540d082007904454840325007119824140c07520708004000c402040494002c1401c100000f0f040c4031000100d0080e0502c40000b01a00803060002d103810322808012030b003591108444011854181d180300b18090f203c580c0014007105103015503503411560229a6545035402c41da21420700c9464440c850505c9400d000c11024490517540c00a8009425070a0390030540c40004c00b1100000c05580d070301460001820012a0141070111380403c02540000e052806410220300d019507618244241404900040c803aa01c561074441c125611000d0240c403c840071 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 418405323 1250 418404073 418404097
    0xc0708060c18091603020c0a021c0311120d021803100f050a0c0512061207060c060f0204060c021e210f0a0f0b1902030108161a070611 59
    0x41c1c60000c076001c503a608044955542d0782440d00d0201c449150020b021032060700ba81c80002420001d00340210025003180c59048a10701c500c1d01c40f00d01594131655042180207040104c0e604c05812490020700c010000142c2d100c0c258408410341107905001c90a07128404070800d00140c0300c03805c40c24104038620201d00d0082e010b01681c403242c841081d140c0c10440711501010001c0c4025100c8540c1c0ca0f007280c1410102000080080c0001909a410582c1031900010003c00c001c2d2000039409529081001030b90040b0b002c900d0403c2138004002180c0501840404480801c60426182c17200150009401c004021310803100032003002644500612007038061040644801880c07518410b00c01000305501c0d01907401c511034281c00004420000914407022a4024890490003080f941d407586107103006003000000035a4107210b1b1621050500c0550300802911005103826804011140e00b1900e403a0090396080b500e502d071181180c51242c0480d00307100d03030041000074228054070102c1e83c00e029408450350b03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 418406573 1250 418405323 418405333
    0x507030c0b031621110f040e0a0e07050913210c1718061e030a020423060301150507120201060e0109051009020a210507020712050c04020c0708 63
    0x707400c45500001e14440c0c020500502c4905040d078100b6165032480300516042000c018000314414500364200788604600041d40a0620711881c3c82c0c940e054005812131981f44005e0001c020780002c45004110f00b24500e100500345060511000c038050300c030014110b4000c055404c02100030025032079a000c00340d03a0811a100348122016400611040000d84155400e40b5800b021305221458441241d0050076080700000c2801844030078008a500148000c88440d400350300400c62204079000110300c07501580500503610380c1041003840e481640d08000a0202d8405044c04070240c42c1c51044030b040d203c001100300c400d000603400440c2d00f446020002071810090050b2851400c0c0c05400c280103940c00b02d000480280e072201c04400880d081107030510400f44005108100720b01c42940108031a240c0c0e0b00e052001580d030f5a80c0341106038448121201010750740c0c42004203d550502540340a802d000804000d0701c600703915074070707500c44807548814030955000500c0001039504010320710091540d0b0055403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 418407823 1250 418406573 418406579
    0x809031501081f0b0a2c0103062007050c0402030a09150c02190305091009090e0c010e060901020c19080a0b060f0d1505040312060806090f070503190507030c 69
    0x160f2110402e50501240c3ca080078140840f2035154095444001805440350099030302c4c01c140d01c80003c000c0c810700710600350340e0028020f070304414500b000e0203580a4078012136182c2d040452098081c4040703600d04660700c801e2254500150010074000c070442001c80b8056100c1c2c032030803140c0000b018001802008403420082a040f095030542000e503040d00c0980035265100e201c2030317200310700c2142d003040140022020010001e0724a803441794a4008030300382c40d080c03084684822a050441d020420b900003a50300083c149074a40da480f041d00b43c007103a01540c5840c10400d031000044c0d9100a900805881842c480400c18040b46090810f4002800084102c4007001c08a0030014880d80341a101140100c0300f00344442442d05110320445109640007429080e00084105081c004200280c001c8003001100700e4a01031511540c0110000b40806402804c81400d040110314a0140c102c88000e41c560000182080503a078040b8024102104121250080000d9440c0181c2802c0e800d400c0104140d0b003a480c08 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 418409073 1250 418407823 418407839
    0x10f0e06010602060402010c030302030c040f080c2d0f0d0b0c0a0813120807030608030c100b0a12030f111b0102100501080d030e01020f0d090b160c0809031501 70
    0x21086084800251422640c07100000c9032904000c48029012894907000240060711a034010f50703010392080084c0d420540ca442254540c680b83da84403105950103000c03000041d10300840105802030030300741e402030034904040190185210340001c082c0308401403840000c0c03940716400c548000d560b01040c008501d10704250081d8040d040756500a0005400100250142501d111500c00c0d054001c0700c01c3c14200c8204e0301c203c40d1010010302203130806072100d20000e030030b800800180c04001a400082c100e00c204c1c0003111011a0500031a0b9417007003044401c00c10900c0c00d000f0000d88025058a4808003401150304240d0b59000c1d50040803142d485103c0c1007004a040c0c9041e0f070920b00409909440c120104d000e4080123862080c00f5940d0f05410000b00855481d01a600c42d440505000340090f00700601c22081000315003103d00d52440458442c40804e0801049031007141d409810118a4211039140c100004c0c000c0500d840024844a40000d941c0341d2a0b808002d1351001240c2c05400030400d684680712 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 418410323 1250 418409073 418409081
    0xf0403080f03010e0106020102040b070b041a090d14071101030b1516030e0405070e0f0f03010f0509240a0f09020934140f04030b0a0c0909090f23010f 66
    0x40a2510304c401d4004100a8418001c803401c44002e024250b0a2881d00c0c0c8031007a510101800c00c4820740020300c1005403484000c00306510a400d500098184a01800c00281c001d040d01d90340710841440800c035000c0001d40b10a200c1d05103031001e180c009002d11149000c80e40d200204000000c3e02e82d00843c4100850003041d103004a414030035a148180078070f801080c0b0045e02c0003503d403200402e00c110f91f150154100445141c459500043c810f032100503103103010034210740c441d02900706100e0310b034130030086802c00400a100b40d07000310511204009494144171070313a5140207031240c4403240e1603003205107406070b0b0f5070440c80e21160000e20714411414075480201e02210300044032141c0307815946401e07600e00800882c4100c4443c00792100d20195102003c0f071a0316500c10581100f82110074040840410500070100c0e2055680f42000113034982c2d80200905018540e0740414234550520342075a00007004116007152a5a100303074801c04d8000c0a251202106a04034880f070461740c6090302e8600382c4511500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 418411573 1250 418410323 418410329
    0x118050f2404020f06040b0c070f06080c1b070302040c05192c033f030411010e0d051230040b0a06080d2705090703020f0403080f0301 59
    0x72904440c40304480e0426a080821061490960702800074001d030604207108450104024581454191110145c907170310b410a03545d411136a0f001150038032505d8890103412025202c542001e804602e404115082d0910a10b1a000051a912501310360200700800c60013000e1075008100b4400300c0001032000b01181c0142131940701c038081071580513903818050710421150b0500040910340c00c260505c4410161444014011303054860840f400d1400d41c83c20880b825840110141021000c5005803c003200c4882043c9408084c001041400000782010b64603146d1043d0a0070132213044d1011000183d030004011402600c0c50240d814114508843c480040220b000f40c9508c0c0030715840d010804126058420540d0040c00c00c41c000401d02080107050219442090040042219915450f038641800c3c40d0f09102404689940d05104494040c40458401140150f604480207442c241c0003656010014111000341a4005401c1c1004400001181c02035600100d400c1d41d0307510701c088c01007901e5100344 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 418412823 1250 418411573 418411603
    0x603091101080c160321020304030f020309060a0c1407090c030e0f06040308041b0e060103180201140d061e0f0609030503030c13082d2d011805 63
    0x480c0c01815503015800c6140580f400c00081c90a100d030b0f10301e40b0400c0801e490030550a001d001c1058100e412070800d4900c0c0e80003800c140c09038490801c3d2a0250401080c00104006c0d500180070500c080d860f00d005884031350580d445c1c19104262141001602d03800d0049882e0a107004080012842e590140c1282d03021407291398040000c8000810425101c0900590800150b00701b100401c02192265030b01c0e81e0031034000d8101c0c0b0310303040240700c01c1d0304019032503809200c021804108018596030144070705070a421408528071901070b0355074002407000d02d013482c0c0d15111240c0400c00b681c49000560002002e0400f07500080302408441c000300c0001c182d07071f201c1d40d020094120300120b01540714034045000c40b6403001c02103040d9201d4159040d501d41210702040d100f0b4440381c50014403c08100700b1760700a110304644034520845a0907240c03003490481c85104241d580a02d0400038a040b81d40040c1c621031405901e0311107405a5501194050114003042450310481c00391640103000001c5000740e041d0f900e00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 418414073 1250 418412823 418412843
    0x647030a1214070b2e03030c02010e010507080702040f0f060806040c0803270114041805010f05030d0809010b10050c011a09010303030902030a06020d06050f1531060309 74
    0x50703a000d0002d80319a01d0000c003407144020109401112401c0c28500181600750401c2c000f140c807080000001403070354070a600240406d440d11041d0b507045048006c1202080c600a45004026100c0c0c009500c030f03d20009006640d81e420694001e01d40d90300c80d1020b003611080a0003e0fa0340c0d042090ba5442042e0380641e442c0001d04c0e000a1290800000c81d00c0c504400a1321200180072845410b1000514400490500031038010508044800c40000d10161100300d0201c900c3e09100c40030702c0104c0c2c005801c03001041d41028401d00c5542e40028292504010b130317240c2000e6a5481c9012180034210484481e50490200660700c90701540010241c00406e420710006c000ca881040030030707031201c1c803001d00c0140c00040302d030014400719102e0340014018500150131600801e4070740d070f0f804e03089070721402c0c0707a01510b913941c0c20070f11417450041c10a1140c400e0440e50740101e402600081025032060b2034400125031011700036a10800481007040752080d0403500e2078001c0d603940e50030140241126060841d00369400e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 418415323 1250 418414073 418414097
    0x315020c1203060108010314030712031a010906120c03090615051c02010f05072a14060306031005040c03060204090c030c02010e0601060810080102160647030a12 71
    0x40c00b620b2064030140c4d02c0740102d0b4699210029956030341030b58460a80020424000860041044101c2e40c08c04c90b0340004102e00200329480034440d6018002c0e0401210210030032034640c0c4120034000b05101c0c0080000c800722088816070040000340801081a400e0880c1d643d004100c041c0324004451060354140074000011400f1000304042150090218652098880d031685c401c001400445106281c009080f0126081c00324901110b4031041650004090003032084070001080e0b51421241a1100e40c15030a001000036107a02141441c428260754a4001a05010030085600025500007c04654964440424102030f1800f04010700203e41081c0510030701e03a10510800c4070710b41110014044603400c146084138800c002030106001440b5211380460782000031320040102d210703000b001894826603440e1100c182e0781c02050f10341031034071211602ea14800300390340804c200c080300345009040009009905105411400041c03501441014920005c225880d1850f06400302203444081d00104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 418416573 1250 418415323 418415353
    0x6060c0111072a15030e03030424020c0312040204140f150901031110020309180a050106020d090b070501110304031805101d041d0615060f07030c0201090315020c 71
    0x141d00b0900e48181907040d808000c0005511310500348201c152502240444007201002c0c6150400c0e0703003e5541201000d112012200e0441000b4200c8030700076420343c10101e0080003183c5038024004851000c414100c0090110741c1c455212f00d012500c40c0c9014451801e11107180100c0b150220348052814021900c81c0400f45441003825041300d0740401c0d070702e00b01e020040a003c5694002d05000c01540f10905c0321007102e944040d0b1400c481d16440200c0442403608082c01030076218180d01c01420354004120f0031581640c410302d510181c40c03a07030030381640d100c14a01d02140100045401554050000b02c2031204040e80560f00c3c001d03060740e1003841d80d0782540310000c004440d100c2c0d54024012801d0b250141904078440c0d0b5241c00c418000400c0002c05403050f01004072818003400100e07105400820420115020b00101038100e200c05507075203030401031a040750030300e54406c0c07044c090280200482c82e00d0841e8480e03180b8501850740220150b141c1c42101204002130b40003503000000718060076094a026103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 418417823 1250 418416573 418416623
    0x3050a020f09040b0a080133050a0b130801020313021003060803181306031a01140a091e06240815040b0312070809090906041a06060c011107 62
    0x450015407035440c0480c640304020042c03100861081e0444112480010b0049003031040303070301c0f00d000341c0d18035103442d0038480b04a80c0480d00701e5400200412003c1092005495000140040d1011000d400e540c503101c01c0e1200c685c006040c6d109148540c0008100b01030040440c1c002400b80d0301c2070343c122a4106180b001078050720814054400c40758811701c00da0000f48032507080262080d40151101d0000300361144000d080d00e910307800903140c6031048646d4000b2403e5000710103004004418510204018642c00101c036808903100340d42101d0b4580c04c1d903603100d004150981e03140d074005040800116070388070100c200184203440701c0d00320490401c400e00ca15600a180304d0b4881c0c0074424000342000402e07400c100051030001c074860342511444c03110f0300400c52420000d18030304d40a41081516802070300108200c0c0d00b0010f10f520004e401c050103010000c8d111200000031031456203e605002d50310003000c13030402d020b4a403280c0515800c0018248400d8a504001c04159024040c4035150500804400800c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 418419073 1250 418417823 418417837
    0x241b03020a0e090711100902011e0c0602030604021b06060114040b1b120a050c06062707030e07180b01090b04030807081b030c01050a0c2007091b03050a02 68
    0x4150681d220103014501420703e96800080c908281c2e221001d40c081c128900910000d901e00a1581c41840c1e03425982c108004903110f0321100d81c508580e107231a62002b4202050362000400f07075500440891100d542d42d4065030b019070000003803440c8581e11280142e907034100658225000c94481021180c0ca091f01508403026900c00320041890700584007184000052210b440140d14041c0b1800351003010814801448110303030903a546604e620708528003a040c24409000184288500348071404000090a00002c0040301c0100c8641c0690f00c901c001d0380604002042910b00380240440440c490b8100500c0d600d203800086401c00042c90076400565089032140110150b0070803d200400c0007600c5e801c01007a003540b280d19020f08040c0754105600000b180c641c40300300d107500081200581075a091040b01e61040100400b4010500d84e4013000d0012500010207500c0a424000c1d05400c440b070402c0030100410061104004600404080410920300064a8030001e801c003c007240d14405107000750341070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 418420323 1250 418419073 418419077
    0xe041718120304150804020a0806100315050717090a0b011502150c0417010b1903050f011e0209010e031e190c090c0e030a03020303090c0a03150207241b03020a 70
    0x19810b02e0a0240c45d1a40d0051040382d22400310f040200340c2140902c5000e008544180b1b4105900d4154a02200d1010751441429400da05c3e0000300300880c2c3e40720010b04d8482005a50103040342d1115018141000500308000d0b2800040701d0000500c0e14071725030350300e50b004001c0c0d0075180c4891552880e00c05000055603d0b500100042c801400b84080c038459006140880000014016440c003020401c0506081c590382e146559a00c42002440001c4c00b43c0c0c1150003010b80200f0000c2c00719080c0703051150142080010f0b007640400c1c8040c050340990340300c2142800c028119100f400e07445410f900e004142c08003403a07150060a10600d07000b0922001c000300690300086581002e401c1050700e40081100418031010010505e40002d81e0351014040c03a04124048e9005d0b42d600d1030303e90840b0341b030b01108512232801001014410004905418801d28109201100c00360f5181524100001c204400c012204561290032800c0718800900340d0100750b5581c0b00b1002e00c070503d804154190b040303005203035010300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 418421573 1250 418420323 418420349
    0x70e031501210f0803181c090602030c2d060c0c070e0103110405070306030f0308070207050303091e06070c08010b04060909080a030b01050d0e031c02130e041718120304 74
    0x1900c03070014551020b5250306d075040c100c518008440c40c0100250080e03e600c0b202c1000c0f46d50b00c0360700c0580c0c480542400d000035850001c10503411556041001d112004461046103c200c09040b131141c10400409080304840c1607080002c24101182d1040301c0e04807240c4a9040b00107103149200c40040e04030394010320590409000141408064a03009150604140e5221800720004509142c2120300d03d010307507a55105031418000181c5812003c4c0c200f640f00c0e510502c000c594940d1403096807070540040d10310340f800350340400d40412400d001d20240209034000d01800031840c000c055001c0c1c00d28407000c41d4248100342e900c800742c04c2180d0032481e001e44000d0081150340d400307500a03000036590000616205243c9058082c03860708981e408110f251840d000003912a045000d14403031440801c9d1000400c502d060060080010007a42501c10411032803201c0c8002805e00010101d1000101c513907400131540d0b90441141c0f4034a051601859074400c81c20f40d00540801d0038000246c03029140c050704115 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 418422823 1250 418421573 418421603
    0x40f050601050a120f1b27090e03040521060a05010e010e1e07030b04060f05090f070903060c030501050910031e3f050f030a05070e03150121 62
    0x1030380301c1c0060003540003081d1031710080300da919014030074019070183c8100e40c41115942090010501d1004028400f404085859010b2030503115462440444603000c40001341c154001c014182180036943c00320703030b01c0500390402d0141c8480641510509141e1a01078075000d1f030303d500727000e408c0f035000b070007100075200d441c1c0014030401c08044c420310b4100e03000640720411801ca4441c6c150500e00201c50600001c0d4468200186500b020700030744010b0000c3c400044842420600420320a150061015143c10341200c0030550080c0070303001c0d0380041c64101034140600d401c0b041020300609000c2c85010700400303904000410080b104036400782602d5000080340c2c44401c0d01004c00c0500102c4841c15140310628400d0300c4007100c01040d1010360280e051503138482000800382130b9030f0201100540001801010440c0600c00e122040c1160340c80180d80400180d43d4480d16411900e11120540283d094400c0811450100318580030141c12600a83d41810306442c8015071210b407540c0d18100100701583c107070001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 418424073 1250 418422823 418422827
    0x60801090501140d02012c1002010905030a0f09080f0a0b0702160e07020c091008010513030e04090f0b04030305010806011202030307023304050f1206040f06110f0306040f050601050a 80
    0xc541301401490b00e407d0840302c01c0502d100c046104c2d00031200c514891303004003016060441d00055000e40a00080122072546e40f42c060f00d0344968602e55007008a003500700d40910313000310b00100c042c10000040b1101c080701010381a90b13861065a0070345210101d440050500fa00c0010301d00c0e880074088045816031450001140b6030440c1c041c11000950081d80c04245443d2640703003810b44290301c0603045c1c501a515000d001400c45002078000080e50360241d00c260003080c0c0250202032940c80544d400582018036040260201298070002400d0012850501044c154107800c1181170b07581050035616140d927515441c103060b003107407500203402d82c00611019000d440d085d0091207429805041045a022041e100c4098940f41d0440c00c15000d98045010300490611142c1404c1c00c840995020444042c3c14114507aa1140240004d040114044003481001850341100517998060200c182d2115010420b003543c50700211501d40c009e520740f0ba20000703a001103000e050f000c3c010685580c1c4c5805805117017 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 418425323 1250 418424073 418424089
    0x1103010b0c0c30030415050d050a090c1502190b04021906020a0818120d170c0d0911060313020f0901060f0807031e0f0e010e0304060e0d020a0f06080109050114 70
    0x10342489020a000c00210700780b02d0801b00d483c0e0041a0344581d40d1b05108401481183da000d401000864582081400040e02280b658000e4441d500c101f21110100910105c0c681000645000d90002075610280200b20350a01c01d18016807007215010902c802e5007000b114801c07030310320654005030700860680d00400c81c01c1e40180644000041001000b10010300462a454516500085203a2100f4418194503070321001c4000303440380004980340113042c00c982c2c640040c081d11000c00503641d0745002010400050880305602280003410740c607128a44042c10254034051404280d004100414900c0d109183c8808064180c0381103072070300c0318032241241e070407a242034000b40f483c403c4c181c0d070b415003202c00c00510760781400c0e54401040c00716120032001104d00540d51000700c6417003181c0c10179a20048006000c410b65050301c00c2032420055203002d00c0d0029455103042c0700084e4020a034420f020807841303082d00200094581c941ca5103266642ea0300d00c3c3c04100e42007441040408a07400c030381d542c0e0764601420 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 418426573 1250 418425323 418425409
    0x10e091f0218030a052103130206030c09280b120714130305011e02070c060518041107030305060d050c0f0a030501020a0305160f0206191103010b0c0c 66
    0x8142d8040390000d800b01e413070102c1ca14000d840c60b5006802c01c4403031440c19040e00014100110941e03040d810601106504207908a0000784241c00c007000044041421038155825120010320440c2070b19a050510124a003035880001030040b4020f1000c0b81003110707601220030070004000c9040040c2c0d20f19401711001100f402101040380800c00104c10340c0844601140301550041000185850200e00c0c02003070f000008041a4540b801484400045000c045242d0211111410050703038414988046400c0380c000e1250b1517034064940002e40103000400d102400710b0901c2518100615240c910800000e6083c4420040407540402511142814141c0050b4805030340503003910262a00c99540600b1381e005050124002681c502c20850750380310010160768a601582410044900c82c0800251246001449610340c8495184440313540070540e80a6900120020748450302e0396140d1114082c15404401142242d1003100c0640d01c2a2811400031500c0c6212244024045c0d0b9140c01564141c02c1c0d011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 418427823 1250 418426573 418426597
    0xb010311180702010501090c0c23010b10020f010c0306080d0309020d020a031b0f061709070305060f0415050c070b18011805120307050f0d020409090b010e091f02 71
    0x1030001c0c1044040c0301c28681c020300c403603000860b5541c100a0f2200c01c0319062984901004488006e40307000c1188032040070f45892501643d042c4240030000c03400d001d009080b9065411002c042d0300c4c800c80303d60124514a245081e00d000340581580250110207545050207808600d400085040c01c000e4003a600810f90184050003001011003690001940600164001d58040310f034040b00c2103144403001e45040c040d050800035200c5190030003e004140c14000a070103c80c0241010208107803003070411032180210b034414100c41e014a407802840d0058902a2822915a800c2d14241240d10280c1e00803148a507414400d42e50030004642c0b50810401c2c805898480320600c03880f2000c0742d40e1028020307031451034014400e441d002002e51408628103580350031b805c54084070600034000c00d2503020040f00c030925032400741103854204200c0c0d06d1000f441541d20041d511403a150401d410842c400e41c80c14101c41050821130704541d6440074854440d140480d40c0e44c0d03090041300904034880c1080c0e02500c0d401201c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 418429073 1250 418427823 418427839
    0x20f010b0f10090e041109070f09090b03030708070503041802160b0402130f0b1512060d2103050406111801030e0a0c081c020d080c1c18020f010c0b010311 68
    0x31400c03103500180a650981e49030b040750001c07003a14240907c2d010341003091440d00311034031440218010241b0841e030080e050010341300c0011004035501042558640d54005d242c6669484c8207103003081d075990041c0706d0b04080c0c04403100b0302d0324040058400d8511032904d1501a50044130281e440001e0444001e00c102e911103201e509504030fa1085118031030000c01c40140000300026060100000b6a000b0b04621103812000c10502861010700142250400c00c00c0c0c5401c1d1110105140c100355050204008041002824140c682c001d41c1c55002513010364096a010803c04401004889080c0b051403e02100d5900d184a50321155100350302440c9014020f100f520f0031540d2030356411030340104642c08400143d0081c0940f4009517003000d0459a1080302d4001040c262030700742400741c0000d000408034107074100041503001d04d000ba16050740350b40d03220201e001c0042c02c1e20140704443d0300f5074164042c0d014118185500c1925409284c4c60f032030700340e00404600c0d460782c40d542c0d445000c40c2410003c25000308034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 418430323 1250 418429073 418429079
    0x9060806041a100b21011719020d0b040f02090c030721060906080a020913120c02010c0209010e0a1b020a0f0206070b010308030420130e012a020f010b0f1009 69
    0x110000b40c5180041c032080380b4840340340b2405000d175550341038120104000316000c1c5445c0d041000610400340100720364522540c1d4845000050504115084c050001004842004208408a00a010141c1c400c031100c00c16911090700018850000303c4642c004500309500103202602c01d4015003104105c2d14401182d406d895800d00403d03203100b940021419030000c429541146032100d0011b0303208210700c0310040482d00c0c5071502d6280c116860586800d01098002440035079201b214400300b4141c016018580030350390390740160465a003c8595120941c9010300d110b40c009a0000d011003581c43c142e00030000240c098680a51400d00b15104a0303000e0000c000c0c0360700069a1942c990300860040902c00d44a14040c14400c1c00038801c0b180300070300d410350800c03400181c0da1001c801c0580340d03003020b00000342c00081d8080e8070300520325000103a1002c0d00c1050560381c601c078000f520100c418000d80c00e036a42d07224152056030a8030105071405502c041da428402c291030030070400d01c98405241d843c081c498603039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 418431573 1250 418430323 418430339
    0x30a0e040b0f062106030f06040305070c05101706010c0201020c1002250f060206010509010308180904080a20070b071704030c031208060a031101140f030109060806041a10 75
    0x40409200880303d840034100903100721355048015172208050703014110181682100644500340204000c0a00901151381007c1c0035200740d24002400020b44079180031849100d001e0030750071410b00c0181161903c5000200e5951103100ca0303882199043e0000d01c0010008405c01201005c8545404110f200310050700040d150364102540b80d440c03007600340382c1200b420844c0001c40003d90350818819075100300010803260b200c00200c141148e0300030404039129038880c11200c3c0b5121020116a500020f0b03802440207100f010001841c440e035454565000c012040340c00068540d200c000981081d8000074030410901030a000245411803107122032611070030f0707020850100d0341c025030003c1d641d03d4140f8505004002c2c80e1044188100540d0a0410803031400d9000100c5401860200030101c00a42214480507401444280c900011912805844401b140001805500700341300360060070b0b0806000040420011508074002c581210388400300d4440105102c4203150003405c05011400311102c0003411107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 418432823 1250 418431573 418431577
    0x6040b1e0607150e06010807181d0f100f090b011a04170f0706090806060d020301060b040605071209050303070807030c0c061d0103050c270402031f08030a0e040b0f06 73
    0x3400240000313138900d4808582490140d05810098650380050784c24030814209218280f11000301c0e03800031480d1071174401c9501e1680d00311041c0c404580705001404036803403c003040e0424602002e003010000c0c5034000301351406884410030003408000446005200610b03200c002c00080420070742d0003034541562040007440d00c6908900303540164020204204c9a184140060030003050149071085c0654100780005807a801c0182055109064030702120b0304540702904241e0042c008041d4a035240c0d0340e01d420142503540420340885413002405007040b481c41c020b1940100b600d402400031800c00e01c2c5a80c41c0c0000354480401541408000d401640019034032012200c0680fa0a6031051008a0244440d00042d580e1080146c1418109420840204032a200f80c4074920200805500320144406424070382d80640311696411600020401c52002a1010100082c2c2440c20100300341d02c0e40c0d0514561240104260400001c0102e0642010307482d2035048914001c40c0201440c00110ba031a001800ca6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 418434073 1250 418432823 418432853
    0x20604030b0727060c0203071701021e0c0706120e060a020c060f0c09040f1808090a08151305100921020705090f0c040306020a1706040b1e0607 63
    0x14503a0082241c8654010301203c40000c0361101140c08002c200c001c058000b48901454040121440500c0706542d41006004007c08800141030740000d074180410f80070354807102070b08000c00d2254001210404000c1d00301c078500c000c2e090203402e0309801d0a40c21180c04d08611000b600c8140c82e4984000501d40c28000c0a00843d50380ca00103070340d001c0d0452000d0070000028102c851400c0b0800421400204610480340210400c60f40022500ca22201b101c0c001d02888241c0258840b0240b103a00800400000501c0007035411510108030a0fa0b40048642d5030b000c2d01402c40d040708100000c940403a5440804841407445807040ea001c0c02043d01c0400d040f144074120035121005007a01c2c400400c82d1b02c07010a07003081c0d8544060881a410071010400a0700c000d00300e00203151020000907103a8001c201034030081d5a00072029552800c40090003440707004155041c103c04a10440800d1180c41c05100e50a100c1c14080c0455510100e40701c01d072031382e14882249480e00301204101d9113000a101c2c00501c114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 418435323 1250 418434073 418434083
    0x7030507080d081305060a0c052701111b010e0a080d03090b06010306030b0609071403090303010e010b2805040f08011401150801030b0601090f09050702010509031608130302060403 79
    0x44a242c0d9000b0700411019140211403c00340000c1d0000c201d020400551011045001141c03a2078202e100f15054816000003030148a281e01510703c288000c02c106d07180480c001d90300d5000e070031503030800141c88880612040c4000400c03072174082e82650150141d1240080c00501040319569160030450401c1003210709140040d640e4a070700340130041d0342c00c200c0750409000c2c40d040004508590720705143c2e1f00c0190819100742c0010b00002e460740e00c145042c01992440174080d64a071b091061000b5500e400c00e000d4000e24200d030000114100011509440d1090201405441e204400805010380791741c00d0007000c130820408200220b40e01c0c2d80c98113000001d02e4030000018039446e081d04012241501070b00108080c030342c062010802c89600408403070550f60040754202c2c0c41d44071400142da003440264030038200004410000202d140c9103130b2103903204d11010740080c061907441c2c0c0800c40c0c0324850202801d46200d614030300b140119042e80d002d4032083c01000c0004400c4e83d101c1e00080d86580280d841207038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 418436573 1250 418435323 418435333
    0x2070c060810080304050f21150910090b16030b100507060f051314011e0e01050f010f140411040305032203020a0e06060904050a0501080d08010f15020703050708 71
    0x1045144582d80c2030007040c1210245007094103000000361358a4860090710b01c1003204100b4011446910301c2440c041c142e0b0041102e580c50144d091a6400c82012a20442e16008481c400c441454090240080443e80312550039881d40d229450024240564603451040550b00e080e102540d4981c032319000c480c1602503e840c0c0e02c4004603e4110291025031190011841c101402c0c41084401c0c840d40201d915404105103402c0c1e0344a43c2502c1c0185504882c036181034480000f031300c03a0704115510642030f0f0003610f802440310341c1d504580c8032840c81d820310806c05810b05400703007004640e29201d000464114020000f04012071003404032141f40e0403a4100f580c841e000041d82109650341006c0080d8580d00260303140700400d207940c00007858034000340304842d105183d4600050b0a950b6040c211002c3d01c000401c20409810846441801400c09008842c080d205110076200c5e11402486494121026030700c2d020764044c1002d00004c00740e00c24600300b02c154402c882000c80013440074082c1350060412407000341 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 418437823 1250 418436573 418436581
    0x1090e010b0925020c0306070e060c011103190507020c0108071b1a062d041d01050402010e0f0a171c0203032505070201030b13090c0806070e0a0e090102070c0608 71
    0x8030030801d50308003a415544008104c017402c2d1404110181d10120b01d082004130110b0000110f400f51060002506643d40f8200c4e400e04541142000b03180200e1209450418001103034040e10102c5e00103840d003c000d0381c0300f1940c8110561113280300f42e6001d119403030002da000344590b02101c165000701303004940c141d510740141d204201c1d0400004d0f40c0190120b5920000290308c50f0180c03610741d60612000b030362040c00d810f0b01a9985503600070413504e03072030900c41110b9919140d82a17802420103850480c0010011381c5441e48030b00e4209103801d04000000c0c9102c4501d842c5c107503000301ca5900d00c4070040c054001e40c1c54079100e030881e18800460f914200c0d000b440c1d6924204421511003982095580800001c03007800846c030710b81c00382c150345441e41e080c03d000540c48502070000304012903400c00076603150304085105082000040c0035800f1212494101c66003078944440a41c0c01d03094541d4041e030002c450040404c01140c01c01b03461a004540080018039204c1305807161600d030b48c03480e000400800c3c40e14040c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 418439073 1250 418437823 418437871
    0xa0303052505030a05040314030415150b0d150803070803100b0403081b0106050a08070801110c0c010f030207060f060e0906040803070302180a1e0905070801090e010b09 74
    0x4440381919840076030707152480580014160b404094080c41200da640c00c001002c2500a07182d0042801c0c03000100354882c6814500b000c0d01c0940c035008600c0315400c0c0103812211888801d6208290b03104050310504107a0410281c60041150001c941d004e07480401001400e0380c0107000421032540034811940d641e1400c000d1400041606610850704072504200c100081405002a110740302083e10441107144086941180035103425008a940200c4460000411600005415048508001c008d01030320300e15040c0c0c05401d00481c0e0400045070041e000c59542588914030311040700740c403030074010704140c0c0c10340781d0718115048621030140041d500c038810b0040150300c40b9429070000d07c0c01c0080c01a0726081d6221403a90001034820742c1810780101d100c0d070355048a0001a11183d902030b003800f038500d03901d407102c07241c803001d03140c1054808800d0300740420352925600415201c5d91244d19020005d1740303040b503000000c10743c1000c42c1d40507550b41d5980e51400c0d65031030380f072030300034103065038a04004204440c4c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 418440323 1250 418439073 418439101
    0xf0e06370506211005040f14030301140307080c0411130905041e030c14150915061f051c0e1c03060f12020a081903031104120615080a030305 62
    0x100320f50a0150800d40b10842c040012524001c00390703007a000c100741d02c0e149081440700c2c8407260010070116202004c100a244000042c0d8100c0d80101e1420f03107a011854207140c0c070b4071090b0180000e84c8d0068a488802d6090503040703005a00d0503461820b1400142e0321811201c1e2003c0e402031803099450341c0a00040c00820044408480b0820416505c8506d09580250203542003900040030400c042c0708005140e03605010851601c0400980500c1d1840d16564640d140d840d6024002e21031302900c00802c0943c1040d0310303803030460b0740711a00c82a40d4440d1042c0c1030740e040c0c000280e0800041e1442284065550150082c845045a024001c00003002c140c11006018055807800b0420940b5140d0300708003411001e01d140088611a603070a146260550022440100103508002c0d1648540c1000034200f035941d0100b4102c6a0007554104064594000440c83c50b11482c80381040c0c45c0140c414070310210740c00358041002c00513410680d5510a599010060070280006000d4001c03995400030880c001d000c0c2071b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 418441573 1250 418440323 418440349
    0x11030a180b04050d140c03031617090102060a02090a1203120b0f221104080a1110080c03090109051906050109060e01150e03150106030f0e06370506 65
    0x30214142810400810a00c2d003280340060304083d8440740440f174411040c8199100150003600390790761440a504812410f00b00c0403811108204404800da4812000b01c007500e50700c450585c007500c00d945034850000c0194208240459000c15902e40c00200c80d01120542030f240751081d11090201c0343e8003d204812550380921aa004610b2030840102d07607501e440c0c80b45d5401000581d80c0980c510340c580c4010051224602c425104000044d011644800002e252103d00e803084000d04108505241408030035294401e40c4408901e403000814410b010344006590310001d04000000c6a443d103494252402d0040c0d119044403038945d007450f00a0140a004050150880b4070048c07040134640341400000120512815140c81c041c84041c80465101c2c0707900e604690401812120b0400508110750f40094080c414030021a140221041403000207026401001203c0000740030076940700303a005802c1c00010110705020a0a038070485411412060b80070031510b08207500007400e40f138144288a01c03100401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 418442823 1250 418441573 418441589
    0x180c0901080309100c0b0c040f08011a040e03070f0804050111011a06070f0c03110112090308070e0a080f0604140604052a041404030e0d0b0c0a11030a18 67
    0x800500040758000100d03030a4400c1564903180c0d400c4d00d20011504021034060003440d0505010a0040e484018000780c0140c5102a043d100c03075940d00e09500317080b154208203100d081280300040304114a000c0d48071051005040c020b40345014229502c0d41c04282640c203003201c0150000c01c040c065035901404000708403c02c0310081001c0c1c0c1c01d00c0c8804034005048009244142d00004140f0b080003240a01c4c0360a1962000c061031405442e8600030341c2c43c082d20241c9600180485040c12102d6149001305020503800d80c40e441341c5030304c4500b01200d40001318000302d5080f108100f000544000108000c0700102c07000300c0601041d06040c41d0400b580542060f6017509684050107100202e8808a110115140344801c007540c0c54242c4000c00b4000000118115405032600208130030a030040c2003001e201d90f119030b4442a401d0191801c1080312500001d02502c44440e0b9000145050381e40e20091680918500f00000760245044c3c1d07080c5036610003c03680c00000e06a00000d4001401d417040a00a4009a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 418444073 1250 418442823 418442839
    0x12071401140f03060303090a0303020105071803261c060e100b0a08060a1503140a05131b080d05040e011d06210105010b092b080a1403180c 61
    0x901c4840d0002d00803411101d034942c1c00000032a40c0c0356820002c403940d2400140c515a1019074a04019001340000c4a820011500d0340d00c0100102282c40241d0b41943e9126070045041c1c889422018811454031484403100101040082030000031494035a07132100d0a214041605802e040c881411400d000d402a81c44181c1100140142050307902550b0022519280c03901403035968400003402c034440c40d840b01070307100718a6040020040c0c0c1074101c02802d66001c2c01000c019258442c801e4225442280d0401c09c21034102d9044000550710031a00440780c40380c26010400701d442c1d059241c10a550003201002040340080c04104082c00c180d074803030041a481060340340d210004c0b445141c004000400540c820400f80e8400c94005401030302c2402c40c0c0c031609001304281d40c0c642e11107000980c00040c800740319002c0340c1d0607000b100d41130008008403001021144800d0700e69175030707815016800c10031250b030500050384100300c55500c040300070b14401c5440700c007084100c0741e111074031905110f5040030b254080c00034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 418445323 1250 418444073 418444097
    0xa021302131208160f02040618150b2203051c140c0a020d02030307150605012010092f0a1202100807031e020d050f130611040512071401 60
    0x1185041d111141c030f40320b1208512441c945401c5c268503e071002c0007035002c1c0c0f60070310106d003180060001c0b011a08111104010311400c1003120754064406105901c0c2004082219003903070582d81503d4208483e01c0a4480d040310348a650740d0f170410304920f000115040c12042203412280c0d008541c0d00150002d141c10a00d45014020f50544585c0c03240350103402640d040240d842151010030885003010381110000198820461140000e01424814980000c41d00c524001000268109203d0090411002049005141e0704e08030f0240004900540f000f807409903161003004006003c070550800011400800c0d00484003c2140202c6a40c0103e42d085001280034030041e2682c81101059482c40c0c2000d01195031281c01c110060030659492008249407140c00042c034607116009004045021901882280c2e100c4452155089045503420021003040180c1000f00341b542d400000e050200d040001e160a480d030b4041140d95054a41d41e00d0780b9849003a081284005012810396035010905c0c1c04c050340c0f00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 418446573 1250 418445323 418445333
    0x9030d211d0d09120b0601120221070f1b0201170109050a140106080708090705040608030903010e011e090c05040501180506060306060a030b19080a030f050f0a0c0201020a0213021312 80
    0x1891360042125403001d0101e4100e030301901035958203181e032030019940c4801c040d070500940070310108241c540c070302d4680108401030b010708840500c510190b6103d044400c04408150034160f6010800c0c0e040c0200d034441404a000310540b03c502800803041d0216003828181508002c984020300d800c44480e00c0240140324883c0d1040e0345603000302c0c41d40b40264aa440396000c06090054031791040d42e001e850004006000000400a0009d9040c00c8008001c3d01c1e842c01445400c0c1c594040e041e06d2006010504d452131000d56900c825800d86c00b8030303844d4a90b691940041002c0b99002e800c400202041c0c6a00300000d0543c501442d90701840c1034542c0e508600b090300200f02a80a070044101c145034441230017155942f518684804a03c5542c040000e01d85d54403180e15494031600001600041c0702606002c800314011822101041044c0511a18007500588102c48405544904074118000c03030b02e400b0090f030b6480b0040001c5131550000107a40750170030210104009080d51010405048003528140491 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 418447823 1250 418446573 418446599
    0x1b1202070f02010c03030b221d0a081b060a0905010f0e03180612070302070506130c0611011404080901091e150c0b0f061509030d211d0d09 61
    0xd42c2828000e41000c400c0c80c098001e800d4920382c0642156195003175000000c8480385a4990040c125420429210302c981c010b8101041c0b400c01d10b1441d40882d5417280003030780700d0f8000c041106025455816440300112208d007051400d550010b613941d111444141072000c28400c094044091107000c01190a00b01c107020380740d010b120280d81c1c03410300d0354903120130707607103c0e101150110131010404415074501200c0103002500311310000e840310704c00e800000300804140251083c50b56048015203124a240c18011107030b030194421090055520b131150108146200070015001d90310404081c3c2e1151042000101004c120368080182e89c50084420480503a401040c10300380c840384012a00d0006502d101a5411765204400620310341c1a07004204440c0400311700c0c03600a034011115402c21003004d00d040742090081c0c800040d4540c110074030b520045402001071610f0040ba80035020400e40069149608403500e0754024540400b4450a044000c6000e02c800d804c0c4a2460812030340c89401c01451080034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 418449073 1250 418447823 418447853
    0x60709060315091404031116090216020909100507050f071e0b01090501090c0807120e010605030d1707140d0906060b0309010c09050108190506131b120207 68
    0xc5503407002d2144407120050300d80409084002802c0c440390807084850082c1c03880c210342c1940041c00f9a103900c03a40079804503920b1441007121400300284e90418003000020341c0315200320b0313542c241e0841d14000142c81e081c0c00d25102d101380c3d1014003031034200c080c0c40307000340c510041000b01000700400c20482102c2c10401901c0c80903800c800c11515151800e200180845000359001c0c00b00080d8a00003d00325030540c121034141c0f52665001e00c4a40031241c400d0341d004a060342c2c2c4802054905110810801c4158802010f03030480d6400840e6441d80c8070302182c2007211010001c8000303109151184000300444900d03c0c1c0000092410070071042040305040c0050055810400003144c035480c452003404166004440902418a40241d4130306280806a0007005440d5203140800da01c1e90300054958011441c1074170031011852441030301d0401140d40001800d009010a600030b468000c00040c1da415840317a4540c4454040300309035141040000904008003a00343c0d0044d4900402c81840081d0310001c1800758 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 418450323 1250 418449073 418449077
    0x1104020d0e103b03040305031909090902060703050309070f060e0906030d05091509060d06050f09060a050415080d091a0703050f1605101b0311030c090d0c2606070906 73
    0x43da48007512054214420f542c000307421440042030760251000d0888080c04d81480d192242090590781b148010107641c04004040c0d4882818813000001c00c0c084c0c001154040c99000075141d0f41516040d03014410f01c0c0580101d00080c090f8294100c880c1484410144c124100328018411540f07117406c0105148203005c4958010780503110740740040010202668451180140005d84508101005d500201840d210303941c41142c01c2d620490082c18811035440c014a005002903c00509140a01018200d0700c1c64003160380d0340180002400b2030080c000381455042c180d031440d402a1810f821309502680c1c0da00c60400200d41081901c001a4200c2c0484007044464418942c03100b00103030003400c1c40c04c0803c0f4050128001c030194503500d01016445450400f1145410340d2441d007907500d084040721100c0304074001e0110b00300040f9403001c1441014001440d03009000010030110f40e900d030004605694040003421241418140c8514592600001c000d4844ca00420749442d100780014007050a52040c101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 418451573 1250 418450323 418450421
    0x1104080a080903030d0608061b0909041101050706060306020414060c03070318181d0d0e120c0d0b040611190f051b1606090506071104020d0e10 63
    0xc03924180103403900300c110f140003005181d030b07503008180e08c41d501203c24011800d803414a1f1031040900a054410310036018103048500e503141d80c1c4060800308444425814054103008400000d05e181c01420081e61082d00c001d603c4601d880e00c08820b00c0b007122030782032242e14180000c03003001500001b43e840480d003506d0603100c80021035120121045141c4c0255604094001030a0f100070a40d400001218103080c6481010f0f5415503ca01d8850101200ca44c00085540921200510705aa034458007201482c042c0d0f0006620600020526080b041044512445001c20082440440d05c60200900440060b0f90f01e000c500e0214a0b845420704e044840038000c3c0c803281c3c289454070a505554001050440312845401c90700354065491840c03c61550044200311300c0031030200c2c07080192504944014011508101182d5540544030742640045500280c1c00c2c464007441040901480140032071140c040c00000c90007040e04015203080c1a100100085461001490b00c001d29628030413004848a03d1a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 418452823 1250 418451573 418451587
    0x91a06010f031a0a1205070608060a030b1503010e0a03030f09020913050c10050403050105060a0b030c0a02030903030406110c01140a1103120106080702071e05060f0c010e0309041104080a08 83
    0x1a00f03080c40855460341281e0305110108a51008601580d20a4018411502c00301e554200844104604880b0540c01c01212401000001d0b41302e200e03181c1010b844c1642c103052021910209003142da071142c98a034030f40c0c050201030302455050701c520f00809254140a010744240c0d80c010560420005e050000061202c1242034140301f4144800744081c20000d149084c0031206007002052504540800c1d80c495107080f020030600e00e005101c1b50201da0400c64498110381d01e408001301e00e81c00c40c00742242540000c020703011550340d09100034400f034052a103515441106208842340741010b034070841c0d810301517070ba20302114200800b0706a4550301c040b4600115800b50140c03665040d03004a9880740c901707484074000031075070036000341031544161000e50803106902c0c1e46607400166800004c400b10300b4808100e10502160502c80f000b032148a541d4803000d49042012664903003100d00704002c0305c04581010906460030315080c001c29402440307000110307040c18103000b0520384407110701c44020700100002480d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 418454073 1250 418452823 418452851
    0xd0f031205010b090f0f030c0d05070b0d140a0209010e0910051305040203010e240601090305030c0706020f0102040506090405130203120a0806010903120c0201030e10091a06010f03 79
    0x106903a1803015030184500d503580c0420500f550049000729215500006481080b4145980600c518010003001400c40000b0030041c088203c00300507050325180181940403640d0610038000f0000e03005404800207a0040200321003080402c094800318920340104140e240c20784c0d0110a001c1e20002c00c4500c220b013a1120158242d41001c0c99004035000b081c581c1c54000c00205a42c8828402d6009030b000703009440801d20001d844d0038130340000201001c840000f001060b90840c40440e4060010704200780e815440f507d0315861500101c800c12030303561001000b4004c0517814003508860002c000000d50605060100003460b0380607103010a401142e541e030010b0700c0f80d40d0103d10717541c450750043c090b07420345420000d800c5c801c0e0f4040210300000c9052240840e015500c0351400004498001079008120180413070100d48828130510183d04040e00c52110140c00c100a1050401c840444440021406940e01d4803400c1031034155400640107003500200304080e600078502c00070440e0355280000d005103040884c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 418455323 1250 418454073 418454087
    0x60507031b0f1b0507080d0206010303140307030b041a12120d0b0d17070b010506040b07030c150e07030308180c0603040f06020f04050108090109051011160b1008010b0d0f03 76
    0x1d0300300340f803d2445003040c09000f0800c507050f5825182552102400e0b880181c0c1c2e1104284001000941c51260010899081c240596000031541c40c02040001b40e490000381580c0c0241003032181c405040c641d40e81c00d031405000c3e101c0d01003030000144ca181009400220881d0103003080c45080152203e99810580c0d0301d402100840c10351224684141c208c070080002d050360001c2c03204441c4041000000300e02c5140140c241c60485d6020f0404502c4d00525680072241440000c0003121126001d81d2400d0100c44680140e03940d120340c80c00100511843c5040c01426000f01810350202101524a90720342c00401081a140200040d80c02a940c0d03156440c00300291002403030090b210f503201240500c080741e041d000400032584e0990b1a58038a4407541c100703508071100224010144e510040a107001c01d18503400000320074410703109070743c10a01181c0460502c00700100341102c00191003001c03c441c20301d40c0760b54030018000b070314000c01c412001d01000c00c00790700e130b50f40002e0704901d41c11610364200b5201e840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 418456573 1250 418455323 418455347
    0xc0f0f18011a04080d050705031c0c030c03020c0712020a08060a1401050103180b0a02042102030d05210c0c0312090c0f0a050f041503030c060507031b0f 67
    0x31200c0100c0c0c603051400c2050310360a015410500300800095100180d0040c103450548040e80090020a4802102a01c0c258070105049629020a0010950001281c01c0c050300d640d54401002c281407500c5030009044507806400c207001e0601c140040301f103442c400603107034081c0c4405000802041d101c03030000550225141d8800c4140b48101002c100010140d80c01020200074908809500352340c07207800660a03109a0260904002c0c41490030038040742800c6241500040c00c0800140f81c183c440748204084012000a0b0120103200c0a1031021400c0070481140c9403205860210705240c00c071141e8a0362025203c1d0b40b40c80c2c403103e110200b503c24103800101c800c075100030000c0320394070750010700258180403044405100500442ca2140c450741418017551101080051031010118180f4082140200c403454120783c01994131244010035031140ba0300b1101031030107030312501000d0480b464080c0c203884d0f0050800f07007098103000e1081400034240400b030046a104c0c0c01c2060315150550780445440d18082 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 418457823 1250 418456573 418456579
    0x100503060411120a090317040201020d0806010e0a06020a02090c09030604030806011704260a02120d0e010c0536091e0c1b010203090606011101020403020a17010506040e0c0f0f 77
    0xb81132100c02c448a61088658a04c25125641d00030788951040c81d000e8000c03100030340907030003007851601028403443c001c42c0c0c0010305044c26600450f40c00d01140c00507100d50001c0016a0040200c03a00391300d0f04822451b40158507080e41c070b240580c020013003625000301030002001c1c0850716001c80c0d940c2e07010380151618900784a241e00c4031454581081b01c603034800075a520142a4200081c608400d060b201100c0da9144907800030080002e0410030560281c2c03142c3c520300140c59540241e148029801c5c0244900c44000b0303030350281c58090300c07402100e880e4800010003d030150822030780e4543c1001ca00542d146100c1c1158100042e0342c03401380450521715010000040c0d1710603c0100107061034042c01518030b0148a4035149090114009010308030700c401d60780507030281c0c0082d00007140c2e0f41c4100b444040744ac0000c4009420306550341e0215002e07261300c3d0011203c660342114240c0321175078244185075001d03000712014881065400b03500c81c3c032600c3d602c402a0180380540c07520043c68891100c0c03516103850107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 418459073 1250 418457823 418457857
    0x30c08060c1e0412080316110d0c020f0312040806010f030302070e040201032d0e0307020901030206160503040801020a03290103050c070c0b0306030f0f030a08190c0903020a05100503060411 83
    0x24174200d8072541c001c440399419068525040112030707218a807001e640801c6480141440301041d041510304840d0900b003268080d0419660300707055101400060425001803029075203580c105486142408016003042070240031818003000801c0d8002000411230b01c141c1007449003a252800100c018110415180081080ca0520305068400c0e90524081c47c12210b00200b01d40030301c1d0701e1030350b0300e80c42a4840650321048010040c405032500400404403041482001200080d80d41e80381c50440e00032743d0044103d82d50200d0304842c45901406020044506448070340a000010504444c0003010b00004034101035459000969049003074044a40d0075401c01c4c40c0d0540c83d5540c8a050800f54001c403069070180c00741c0000080102000540c150706244d00300055070030100448000ca540c05001000d22203c45200300220f66000024810b404591015070b503407183c3d107415801807280c2c02810380c1c0035600500700241030110315503100c030590703030018811200400d1008102ca01482e00780240c0c011840c82d1804 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 418460323 1250 418459073 418459109
    0xd060b0a02100c03060806060906010c0212070608060406030b07032012040c05060c250905070503160e0d080904020f040626160c020d1b030c08060c1e04 67
    0x2e100c0b080140502010311101040c100210103982251040c00c00e10751000d03001c94103515003010320652100e010702d0602801240c0d5000144990001a00c4032080e400040b4188040c660290304140d00403026078040c000c0c1459a6a90440c405001f0800810559075281006484444084040355081112041901d550082400504000c02a10101c52150100d10009418203068055a00b07480c82c07480909140c810501041c0d0f00c8000c1101c036014490b910903004580f004007846814021505542c546482c1e1034480c0340c42041d41e80c003181702d40034803210a0f2501da09948000204114a030300c11030b40c035100d0b504070000c41c0280c040c0074801003810720b002c1000300700640e111701d4000b103038458603041c40140500102c00c0310400c032066423070800d00c440281c5018a414081c0ca0502922440904000000d100c40e07250610340d0700c0160200c1c0b030482074550040052241c501c45042c050488030300a800941410b480d03582252280700580603d0034402104641143e02450583d801882d185500700f47c1024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 418461573 1250 418460323 418460327
    0x615040b09011115010e071205040605010314160b07020406030b070305041a0705070605150a060302031f05060405280306020a030608010b090a050c0706090503030406061205070b0d060b0a 82
    0x49401da45000074040d41e07807100500800101658181d07400a4246403903400d1140c86210094004d21840034000d9213415200d580586107c3e85200394090f5600113030075415807038981005100100e40308003a6006607292161003403010242e9044a07400d100840e9102528400705000c1c001c60b61014200140c0d07201080440b54064000e14403403481100c5d1704000002d100d0340d00d10606000c4d80d248001802c144540f2000901603800103030014011020180003903284400038070150141d800c03140000b40c010040c4801d0300040c00130902c8408810040300100741c101030200fa5a80203520030780384502c025806402440c5080b520304400c941f00d030011114002e8030707410104040d601061910b03000034074003100059008410b2003200d860f420024446d41c07050306d40c9a0030f50080d000107040806008010000792000810501c18039100c03c4c1300304003a580307a143c030381400c3e011120103911002a0300d50b0021803000091000c282c00058500721242951980280c415000c000d000b01d402903180402c4c002800c4140c0303a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 418462823 1250 418461573 418461577
    0x6100302010e100806010c06290901050409082a07030b01081612230727090210110c121e030a0e2701180b04140604050615040b 56
    0x2a0003078a40080500c28181800203140e24401c0000000706400d001c0b071810343c0301c0c1503d0351490b4054032010035840425903543c04920720020300072034030340c1e030b070941c1c901135410f00b110040d00401e01164100107403032030750329003480a115510085212a0b04603807615050581101d1041c000707200751341141c48050300c902d4858590300c800c0c0150101c03446886d0034100301d00e142c203c401c0305540130390740c070f03007aa40443e50b551407408000d016405c0800303074003902c04021054042020b0001450b140000b08501c100c1421450201881c560880180505003c1c000c405a110388100c140100300030720b8102040c050780c40c602030a01850082d0140c2c01140994203446c4114001058030040b026490015110000200e240317660b489984614008500074145180311454820790140303002071031042c2030610480701200d0484817002604250105c11617202d44920100580c460f0703442541c1c01751070820404240d01a0207801c650010040740c03089440d0400110309890700d41c06111402403003411b00d502d07951229101d214035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 418464073 1250 418462823 418462829
    0x4380a022503030f0c15150618060203030403110f0a06020d0f05070e060f0405091303140403150f0e0d1e080408030412020a15020a030b010e090c16050610 68
    0x22614644080d001c00c0511a52030701160f42c1034540c685004c01c0544180c0340c0740c0c040c2406035044154040d01510f850034034040d640502245240c42908a8213044020301124403601d5a00d00811005e1000d1003016000011290001c0d00340c206485148001c030403880c0b4103080c1d01e07050b2045014540085081000d19000f50801e03054089060114005c01c640c45022a001200c10300e0003d542c644550f8070508040703009202c00365503989050324040d11000804c404281c16034404a8001920350342400341035010154205c49901d0800c030307a16041c0b0b185c8410204c1681004024565039903200441c0c81039107241e124201c1d035514135041d2480c210a042026105816000708041c000c04000300e0203285900c40c0f240c092141c1c0e07200d54800d085071900d4031045504800705280c40b055204400d010000700315400c0803160010302c000030159035420381c01001010703110886c01980c14805804403c0e80701c1e070345519030300d80d0241d226420287c0790f1035094401100c4812802020300240582c0d0144000c1d035444554032816 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 418465323 1250 418464073 418464103
    0x50a060e0105450c040624050a0e0f0a121b080f0a0b04020307050a03080705010c05030402100804030e0a030c0f08060f180a200301050c04380a02 64
    0xc860103241060340c1d4161045000400944030900000030005040c14000050030f141c0c11030341d4200784200410102ca03455004029503880d40c00b400c03e5560003400c1000a00d40b170b0b51501b541015503210b0003034a82c0c1741e0401e071144603000000d1000241d48403140c480300203052130b070304811070b91840f802c103420401e080a001c0d5030070b410609004200d11400240603403400c1c0c0c0d06002001c000080c1d0312120003141c80544100c1c2d25026800c00051203a40d2107080c1d6000d1130094009690755138051410500711120100c00d2410f001083c41008056500c9200f220044c0303184e403d001d41143e54a1400b183d41114074202c46a11002240d000320038045502114401d03100040d903845c010a440310009a41c5840442d00203a0b48940c0c1d0000038032100c43d01d016000200e4880d011070310f504803950398000481d5200e2112460510014010342e5035840c00f4083d41c1e4200b80c0003c1910310300b03401d003140c4101040c0500c007060f0b03103110036043d0405840b0344513140840c0308c11071002054980100c500300945600001910010f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 418466573 1250 418465323 418465351
    0x501090c060c050106050105090d060b03010209060703121b09050105071502030106050d0f0207080412030e031911090103030f031d070608040b0c120a090f020301060602010e1203040b060904050a060e0105 89
    0x98030b540141c00b11070b92410002c014003040810bd40c2c886000d4841080807641654084c840040281c5903003010388550f0f48070780c82c0c06c060708a10129a01c101e2b55115030345100042071020f103240150304114108181d6000f864a60340d40c4006040035241c4d042c1d803002c03c00c46140b0000000440c16840000f800045d07009031002c0c0f01258a40016106a0151080c09411480308000403c4030351032030404681142d1090420b42d02000f91100080e042008404c4103905480043c03442604002e0300300c07071480350a0411281c0e400d0a50440d10010040403440d2440028950384100124801c00041d91519020b01d2000442c1ca0b401c0c5c442d03400401140c002c1d03d046171068407803000300344010b6003542640c4c00e401d0030980e502c006594041410010304503a8006a6200844041590168400b03019443c05040a500086135030000407000f0391800c0105070965407c03c03814414400081e121940c2c071500060100d5004034107880f42e080032801c04184bc0e0008104034540f10140f0304244040d004140b180c04541c034200c2c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 418467823 1250 418466573 418466579
    0xe13020d3f03060f14060a140706150501020105090d110708030417062a030402130e070f050f060403122105160906020604230f0105010312050909130501090c060c050106 74
    0x15104004134001c80c05c0000050092040b10b042c40c00180ca00304c400c500d06488241d4050b021140543d020780320a035541c940700c0d0f42801e881d043d010149002003001b80700801c03091404500d010f890707403107160441c0200001141c070f000603144100100805460400140e81d03a82e540c0d0414980902100000040c40e030140034006851609aa0808400d000320105200181c41c4d254186955503440140101d911016800706100e02e20030500c40c82e65900c01030402040f20a0600044104402069205070303c41c658007000500c09480d45019101182e80c8030380c06c95640c0912802c15143c0f140503461720704022521241180003035899422050081c2400c0d00211503070510030904803001550345c0281001b40c0d0150700402c0004400c0d07181110880080c800c1220b404208031714090400e04034040d031201c1c41c1c0d1200014014001e55610650b03500c003450804a140000750404942103560080103641415000314080050080a402682040c0c1e8420420030340c4603258200500111900b0b031003615950700e8980c2c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 418469073 1250 418467823 418467839
    0x30c0118080409020c1608010e060f130809041b0507060b03031201060f03110409021201052b03021624090311100203070b010602070e13020d3f0306 65
    0x140c05560004041d620305802d22004602070350100181c901d10340306401610000140e4040c410700504082000440d0b22090552034600d40000a85130500b01c2c07e107002804241c1542d940060306559011003015211044000060001c1120541c8100240c6000c20b60127441c6a01400401c0030f13074803581c020007900105009046e03032405101d9210442900080040c41101d014503100c0e54a2489490701160b0341c40101143c0107107130030950004211075000315a605250290301815805448259501005007240034070b044c40203090244000c0300002c1c4543d8100130b00d442808014a031541030a0755004940c0d445442040d0080c1c69220910040110259200c250380701c0c3c89400708036600020604044200e500400505201691011055100420500002591008880b8000c18954014113000340c0b4018090710404801410b60030142c04103082c2d40d00503039840460114154019961301c0646401c1c04041c0340c110b04100b03581800000303500001000d8060701d0107082c041090350b42e090001c40e035501c0300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 418470323 1250 418469073 418469111
    0x3081b04051e130212012301050c0a02130c1205160f1b1203050901020309060601030b1c06020c0c060703020307150b04020d06231804030c150e01061202100806041d030c01 75
    0x1207242c5c000741c20140c9081f0350311841c060a07001e03480750305403442c12002d03030b0000c1d04880810700f0004106480c4e00348200c000e50000b010180c48544420140210700e405405a404100c2d140d652806010790365007030354019449107940718001a00c2c1010790307804000e2410030140d002c1010864030700090400c00007507124403040c0252800303003038450010005d0741c59640055003e040340b0f00710107030071038448000c480c0c1d01ca454030f0941000354003403e00180d6518001082d141014055680d86005c0c40007040500c000035400021030700480c2d0002c1c1800c0355590001c8041000c0d092142280380d109d800881c504100100c1640400c0840e1303504d46803200380c0303880003507509480d17500703200500d61061681014041c041900d0442c158024800c1c5401c000f4020329039590700c5442c5048011010542d5200c032072007020f140074404c55001d090001c0103014480280e42c0080ca21200315600384040111035000b050b1309444076040100341c0000d64201341845801c3c004104d54a03040b00c00c07108030541c00c0503a842407691070156 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 418471573 1250 418470323 418470359
    0x405070e0105121518061014040905190f020a0f08190203041106040f06021005010b0a05090a0812121302090606070507031b0303081b04051e13021201 66
    0x541c1c500303103803900802c0f030100d1000a010405150380c0c6943d140c680c2d9582d054080002480040e64034480c24043d041c024890180740141c82801414001104403c081e9016181121044000414503540d83c0303100500d600e0010306c00721201418410228074200490f0090603445e41c0a90354070744e42d2194100304547d0300380e09555101e0b4205407402144640d15141e0000c41c0d0180c0100750500000d041d80c408104141d210b5480042d00d2040403005201d03441d4140f204006d41f11200e0000e0001d541407407006079541c40f940443d0710902c580010304440c1c94544a03020001420544242c81e001c0742c01c1681242542d21400509008400c48000030750807100348404006010f0f00503142402e90760f502024400c00381e100b16001d490920640500100140b08074000708514841c28180000c40d5107585000b500d00c16000d00060010403214603888a104090000d0f00e080b00d204a410309400715006002510400d04a80e020f600584444001040650160010081c8182400844840da83d0f60401510b260010709 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 418472823 1250 418471573 418471577
    0x50613030806030c1003022b0204032907111006030606140618011404030f050304061202071106210f15010908061f0506030906060405130302030f030912040609050405070e01 76
    0x1314200c0c407180c840e87c00781c0702000c17094907240081074011510b0444100d4080c400903038580c000505204120703a03241c0c1c01002d001c10024401c60808003103000740e41810014661010002d1421840c0114002040a001005580348003004002d40b80e090140243c03445004040c000c102030008840c1c9030030203600302d40684643c03210749501001034900455803c5140780c000801600248000300100301c003007401403030b02c5120300c0c0190b549514202c8050500c0c4010160020310354030500c111400702d2040d840c0303170303800342c8007105c2d00ca60b41c031114100e01400c86458204103440d0050682000300e04440e20250601552544074055101d51840c1d004644005d01e030301603401250041030114441c1d101c407404094200c0c1d44820036069050f1544086105900201c0d010f004584c4000c05110007820103104d4150415401030003190040c1954070b02a5503417064480503000c003000000050290304003031202da008a295141229542c1e03548160007400c1c0b44503030042d41c0c405c52901c4003044180c0e00540d03502d4070140040e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 418474073 1250 418472823 418472839
    0x9070c17040303020a12210209240d0b120109030e03070b190c061d0a141b06092701080d030605011202130807230a030209041e050613030806030c 64
    0x2076503603030502c007448120006c28841c1249800483c04c50050f03c3c3c0c2c80f4514509801a1a100134030100002d03225854112402c0200b00c0c01c03500042c1009004494404050f0140452085442c0300400d07280c192003814a0142d52a01c2d4a032000c15903c80550030802c1c030120211961252180c9042e895440348810842416030350a80d0f0140e943d016840314013801d1300490000401007071540c15007a5406c0c9801712620242c0096a400c405c02400d64204405207128400601c203040c0071491724040d1680c4039540038403070407000c2503009565550300b24518403601c0c903094545668041c1707841c607200d1050070300583c00c035402800c0c5003181c150f00c00c0c403895084410503503600e91414103444d8000004e6005000d00118089260710200700d032a0200311041c014403540e282d4903410824181d621000c1c201c403412443c4514010041040940e46004010360059040710350f4035000c5901500f00c0000382b0250500629900498003007040c1c0f805220314901d03240d40252141c0c086541d8420816446800311854298441c8032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 418475323 1250 418474073 418474093
    0x30c0b190213090f050906072a2f010504060c1b090b120606011b02010c060e030319090203060f1e07021005010806040201120f06240905030a0309030f030c0209070c1704030302 77
    0x4107407654281c00c0000c0c42c00c01c0c00b54600d82c000700a501d03120400ae481d4003130f1070990389292006004084103a11081000130b8040542d0000080c42842248512800c0100c1c4241c1c400600c20007a002d04175a9149500000c1045e40e038070002409030806156182c45402e00301703046175590501054880c0301e00300503925022000e00310100f40c003881c0d100704001d07410803181100300c900188043c81005000c0e2058401035450703281054401403c080c1c98059001e00e1402c00041c207005841c0061119000103440003191642e66034032908160b201d03003034400060070f2060007091059a58000c1010b101580034400c0510040e81c0b61800c2e942e07616000d9a0003400074810b095002540e0503a580014a010721110020500c540d65003510104048007030b0440c10266044074400040603041041d40c0d0090000f900074210b0341c580c0b0746001e40141d003103200181c0b424625039003910806204150006205a0040602c0c141c5c1c200303c0301c01002955000f00480b042e1000c680469031080314507099408480e4160700600003004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 418476573 1250 418475323 418475327
    0x8090705130b03030c06010e0c040f0506030c071509020a09111207110f1c02070501140702030c0d03051e0f1c20030f06040603030c0b190213090f05090607 68
    0x101e244400707215181e4071408480305642c01d200034194071441c04010040c070b50414071410345260340035000030030318001044100a05145011a03508072101240e003140c41c0d58800c00405064412208028010300d50f040209407034075004c0d809030040350b00954200440365140d66080d801c40380d00c09400d006c5c605050141e07040c1d0401848409500c0300d1141740034071075401ca007903a07545131542480300c1c5490740d0050f540c1703045c801e0110902920814031038402403611528040001e0302030f0020110941009200068000642d01e0401041c003160501422500f180407040c1001000c54100c21403080c3c00450150106010b40c001c0419296494842404549000c00d8100c0070344240e50b141140e54600c6449610503441d500d06101d803410b000502540456a07440c00307075915101000028103080c0b00714949001400826440350204900c9070f401140a000d0351200d105004c0c01405862141040b107000242603c1d00007171341c0717248004880030b12005000c2050030002440a5400c1107442c6856580301e1000120054 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 418477823 1250 418476573 418476589
    0xd0b04110a0929060306010f0f03061d1905060a0909020a03020603013c06030207050102090d05011a0607020607061508010c1d030c03070303110c030f01091208090705 73
    0x1801020014001d59554964054444510064540314440000301d0411500f654802160080856007985549004c10001c0c00041d00400c504040101924aa0310703080d0090703000001404c2214010420b42c1950801c50b11040f904880e00c169030044011101c00c125001c1c0103560080100501c035070400303400c0030923480050111324400d9911004042000026841d0000254081c260091200c00c018002a6903182d081400d420000802c41c00c07007840000c5907881c40d80003020303074025150151b41c99826082140c00390207802c091644c01031a18542030100700b8154803a613540906120003540c041c0b031040812a880c011110b019401c90010801c0d40009403050b800350651403002101142030036290801da50845901d2030320500460100e541041c010039049a0511a41804600a040622040011984420140c030004060000b001840400c0d140d0500401d0000c41c400b408440040540c0c01c020742c080c1c4000d007010398003000d80350a55510503219402c514865018400107040c2c59107000c05000d056 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 418479073 1250 418477823 418477853
    0xc04050606120f0103020f0a0608070507061b0801230609100927150501170a06270b09040302120d020409020f03040b09010507120e031e030709050d0b04 67
    0xc441c0420809911031002d0000303e0091641c00c40c1804298114414041d800c4120b807411481506025800c01c60960f000b07402c598081c0d00d5140c0b1a8568603a841d06501604003801c8540c40c202c0d2200c040d000c0158404407880c122609102c502002c0e2070407112007007034000c0030700c00103030000d008000d075171043d080885c2204008405071400b102255620360b512100060a8450304480a50511085625074003600a9550460034842e14808141c036050002e401405400078101100303003c9800102d56406686c483c0004121a2000140c9043e203401c0d01c5000899804403680f245160400c170b400241000f5041c507200e2a8160000d007242e6010040c0c0c2600768006901188640d0f03020040030681901c1400034000710081c4480c01c0c0d0702e07400d0900e000a0300b41c0c1c00504120b4107a150404021580382e008103141901c0503020800030344103102c0c0c180c041c250301c11035042540710030581310808803004001c0001e622445081d90f403d8610b54488081100d441000600a041528407001140100d42c204d5542c2e008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 418480323 1250 418479073 418479079
    0x609030c1b0f052707080a0605010504140904110a1502010e0d080c130b0a09050414071d01050c010c02030403051207020102030703141b0f10060806071b0c030516080f0c040506 77
    0x104e0184038200d110310021203401c400502d500d0240041501c050085101402c0c09080c11401d082c00d00414800002141080c90300c91030412000c00d040c0f1041300d09003860b003440600048051502d480300602c0030003481c0c0314240103620704000b4840c01a404030380071208d0500369551030582d03103426600108580000710f8000000e0919200068040d814034000d122481743d40d2a9506150306d8001040103c45d5504181200346e48010200b02d050707135001194030000ca0301d0320100e07200700b002e2000490311405071b1100c1069640c64840104211900000a4012070740b080086031550a03450050ba4641d0060103002405a40188207400c0064060b00f00007407000d20700505141020302c110200e141004442e00c100d012130f04111650412040180100e186152050805008961620301c040340d448030010042010032011129003c13010f40309880d0144202d400c83c2003c00082d40740c1c204552a4011100140344074850083e0014410a0101e1011080380e0f001026220340024501800060b260041225034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 418481573 1250 418480323 418480369
    0xe040504120c02120a1a01061818230103170c030d27060c030e01110f0c0a0b010306020414150a110c0d0614010603020f03010303030c05070609030c1b0f05 68
    0x803010208241c0c1706103405406a195400602c844030846113034180c00c1002042192220900010a400312070b60071110070050603410341d01d100a019005009007034195601c40f80010756520141c40ca1681e4506882c003070450110680c00800c0942c901d072007881c00c109a00d40040c007400c1844d880c01d60100c10f06c03425444017031803d03400d14500394144000204040700d50039612961503900035414420480444080d500801c00082020440b44460003595515091404001450034640e00203010301c0d40e42c140e020030304075002d5840b072805001035040780c0a100030242c03504441d20100d00d403031a901d0101c4e04201090910b441c0081c0e104559010324010103010170300c10006c003420592201c4128942c0207004060001e060f01c500020b200003060103900c0710b000c040c014885d60351044050001c6904690b49400c0014010311a55001c1e1030500403c00080d141fa441c1145c10700038590001c43e81a40244940c001e040c4075005080301c5202d25083c0d02803180721900c014020f00003411f0503142d09005050b2845915 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 418482823 1250 418481573 418481599
    0x20d120e010915090c170307080d06090504030c051c1d030a050d03060503064203011a030c0108040510020a0c0f1103120c030a0f031805030a0e040504120c02 69
    0x10440b410080e0400b600f0f240c2d030f00f0441040c4040c0d010703101c01820b050b50034101e00c00e00000700d1666034081c03500b010304200f00000f0490000e04099104800a1040312020703c16032502c2d0801800300604010196054010704041c44d40202c51014034028030700700d07500c0e590b40e000c15881c4038048021242013010303050303c9aa514080424030400c121140701c0015900443c000b4280410b250800c8405080f103100c01400d040400014401c0981c401c0f4100c407030002154241d0a6206500540b03001100d42e03039015481c0048020400091000d02d5580410540403150800001001115a0481110040c0982c0c00c803d10301c022444c855002080d021090781b8281000c008561505943c0054040045800700302d41100e801180c1010300c180f81661042141c5141032411003403d00e500c910951143c1d00402c12040c03c40c021242c040e42c03103d00498000d69200042c0c020300d1400540d40d0b07005107100343c003140091070b81040314545409111300c40d0354000185003207968421001d44000601e044101d82c030044026200c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 418484073 1250 418482823 418482833
    0x20f0a0f170a0605100e1c0203070b071b1203020714062104020a1e3b0f180309060a0905030a0302150f0f0f090319030603050d020d120e0109 62
    0x5000b0003407a000014202d280800704180501c070b41e40d029003400ba0414400312160b03150840b0f81400c410241d1a80907110b44c920001c3e0424000c0d41002503140c401145000034805900700062201240800240e6100d444503402c08030340117200c6000f001680604070611282556110740a40d0f1040070780101e09280c0604403c0701c2c19000c01c00412100d022000400081d403500c0300505004191401c4217603004040400159180512030141400e5524551034a594a00792010b442d4003481480d400e5000f89100d45951b00c2d00e101c2c040d03448100e00070401021946914012000e24032407001440210f1910216005105803034108514240070301035014000519510b0612000ea8418881c3e80074080000c0c072006260380040340a045142000d0840c1c0800860321070342d1a045802c1039500100d0b9030640c0d28454030701c1ca584039200c410610402e4168151400302e41542002c0c003682d00c00c40c2079a4880c0c10f404030880c1d45030701a5060000184141c403001143c180654815042540b0781c400200f0f41003802d46030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 418485323 1250 418484073 418484117
    0x919050d08070b0a09170c03090409050d08070509010504090b031c02030a0909090803041103010f020a170108012a020307020405131104050705030a0e01140405070810020f0a0f 77
    0x10955009400054a608110f01082d00a80c0448000d00800104500742c0320103c018030680901c046412000440e402d000308200b0a03140c04400050080c4040e060610b440361315000c44000c01004a1040d1000c250060702403001d845403141d041e50360b181003c2c9480300010160100e00d9056815000b403803c0c500d03140741442d501485440854008664400403204003c1883d1410350102442c9443c0c09c04000004212008a0340c102d50880c81101c0854007020000740104039030040310101c988000360911103160401da00085508040800d001e05070f90700c440701c50a0740c581296071501c401c400c8081400d43c1c030003003060009541c502c1c811a410b00310030303034049011a80f044e502c0758005612521030304c1c204a640d80041143c45001e480c28030003818080c8000e081804007900d503030181d507141c2d42c49654000c025441007042020202c5520043c2c00d103800c105407070b01801c1c02401801d028001c1c0b0414003c9440c001c43d0180c00074008003030f00d40500d440c1d00325500011039100300c04100780c912002c5a00700003c42 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 418486573 1250 418485323 418485349
    0x3061302010806270f0403140a120e16030615061b0303150b071a01060f080406020913050f09060903040e06240a02010c020c0409080f0d09081804061406091905 70
    0x15105e19900341030401920415041c00e0b41001d000b001c00483c000c070b80d8011540f02104c42800d2001c1748032841460814141381528a0065000c3c090503000014002150802c0c5e0b0301408003621800003580b510000c8070308040d0020505121010040d00b500042e21a501c00100e000820000400c80764a41d0500300341580329400558000150b80c3c850003841618a000500401d8682007800410a0304a4050f2a4030001000a80019408200c1c0340054459000486003445001c40400c100d2030040d10034a8411010707100c0c001c10b8403440d4002001d90100108803810350303203029111a40e56403000100306502c1c2c202075600450b0300c114619003040c00b26403000742401140c9900045800c04880d68001d1030000c00200303d5120b6810702c0600408100190212841c1c0c03a1484405a5164801d8106034054454264028820038001414010a01c0c2d0203d2075442c0100403101400381c0b940d40c0d840150403035044207403075601030703c104a80c600529010601c7e401048080007a411104c0e514000610400c50f055 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 418487823 1250 418486573 418486591
    0x207030506010e0f1602010b1302040e0c0702061b15040f030e0618040b04110301030b01230117040f060606090305010e12040b07050c030d0e0306130201080627 70
    0x106104004080c03080901522180c5503c42d56132400110024180c0c0d006000a41810709000840b02001d02c04e4000c0100b0700c50242521162040c0b692110000350b200c0e03c6000c442c60300c0c000200f40c41031002d070211560960010852030618652008100d1420000019110a44070b01c500066001d40d02e00300c104d129900034410043c0f41c80d81c03400c01508611107482414482d120402c981801c48291000b240188041a45c1c0019000c1c50b41010800506089400c0038040034040000402c02200b0b40425044c0c030b103c0c40d2003451803c064005042c0c03100720026100e0200e05554031304004407000d030342d41c9607000340104c4d16440d81000c01d480300030494150303411110029049280520911809000318000f0b0f170341ca00010701210f10500640aa180128000d0000d400c20001e00714040c01020866480050001020b5405001d00124081c0c26007840012a5020f030182030005600500542c0ea104002038040c3c55540490f9a80c004001c94a40948a00c3c20001404c400c54900c0c0c0201d811410700c03411001c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 418489073 1250 418487823 418487833
    0x3082b1107021c08160c052e050f03040b04081c0204090b01080f04020d030c06050a05220203150a0914160e090a15060509130b0604062711070302 64
    0x240c014002200314080b06030f29011141c0b68400001100310080f141014050321a40515120600d080710010400f40c1c480c0c0c1e40031903c07100304d8104000d0018540054040344044030400000e003981500c0d503014144100ca81c1c560709000140c041341014042561052040b41040d2500001c0014a02c40c020425054440c691780414103000a005602c61054200403d00f031034042e81c586002d80211418000300024002d012110890041500844550455030f46c0300b6001d012074a030041c107003030040c40105c401c900800115400400070f001c06040a120303407034024024000706082070fa4101540b00020b481004416a1110004040340c01d000d4408110003500c0064400c505103642090608040d5401000c1421b00744020b01c80341305d0000404480c0f036035100001e505d22185002c0c0090051156030300c80d80e0000413050401042c0203008014400640c800d1048a8481c0c64840c1408102c9150380900b50500340c40c2001c040100e00c009003041c00681a8600104090b090a241080244c009400840c05a401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 418490323 1250 418489073 418489087
    0x110709180210030c0e0f0d1e0f1b050409081206150c010506120601060804060e0309040507080603060c160602091201091406011d0601050904062105100603082b11 71
    0x809516405c001c03500f19401141580030400140d4003c1030032200400150f0100181c441101e080b480410303581c0d4101e0420707c50b01c03080d030401c80018110006a0207040b0640e02002c0b80340d1501e4800c03801c0e05604810f910f0305000e103000c7c1d003211210028240c02d0340440c0c0c1070700c450072620303c100007011407508001c00811141004828400c00030001d5504448682050006202c00d96118607401d50042e040320380030a80413980d0003c6070a512400501c260804d06000801c4491030b044482c9a008030f82c250202c1e02e0350307075505820403000c3c0181042d001104a00d4480340340810307a51780140c01520300041030081d00003071055101d400c542c2e00e03400448101c0e81c2d10908050308001481030900400085040b0f10f101040e100c0180c0c4035260003848141404000f04a40001d41c07a1588424098403014112029071142c02100381540c6400050031503c03031185654071461511280030310411070364008490340c00c2c0310440350107841e61604202c010700003400e4543c681844012500a180300c212403103d0059840b45 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 418491573 1250 418490323 418490327
    0xf01020c0f16060c0b0705071a07121401060c06020f0a0c030f0804020109170c0301060303020c2d1014030c04031104090b06040b0102010f02070803060102060106110709180210030c 79
    0x4003201c0408030b209000041005415040060282c90325070001034110b0907a1600c500b0307101c0d40950031002e00f1400c0c824000006529170042d4550003a0a981c07980b05008070302040200a0310130301d100740d5030310300c022a0040290318004d80318802c40038407440707015080529400d96106240c109008220019107503109000c20f260304030b4a110241303892450603d03442d04e0140c002814010540c841c0782c5500e4400901500c0059040c00b4280c030640004000303100036a50307814000d40e208425545a8800d880e0080300780302600e00303da1003494000c1c5c0010703040c0c5192a01701c204000e40340f4048900c03050111480c200701030010342c41c00951280340f0782c85a141d280d50650510403d0100600303070310343c000c9140c60035040109059910065103c44202d0f808103001c15203c0c0100d01400305004c01d00314013400452000108981c2c20040d501c28002a805c5034840d0380c2c2d541d81101c00c640308402901d45600035001c00c3c0150115a000440d04046201c060050800c07154042192555405041c40000703a54840703a8648036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 418492823 1250 418491573 418491583
    0x108060105030f0121051009060605030106050108060d060b0306040c060807050307050306040903020c360609160c171909080d0e040b090c0d0c0302180108090f01020c0f 74
    0x910a280290541c94207210b0404006418040c96110705807800f1031070050012488903410280d484030948a90580b50b40900e00036050202080310702d1800c0c1075002c111810140308480407105c050b900e4500c141c60f40d90610083c0324045d281034809c15180d03580682aa142002001d000301d00c101c1880000900d0610020b0008402405040c1000000c005116002e40d0001c213584d008181100c001030b0103419460260702e04402030b202c4030340000048415000c3c40555445d26095110304252481030000032010001c01c0c4041110040c3c1c0c0003030500b0100d9201c140c0c4880060310300c20103043c03840c1004001e845504555500c08840d000075000042c8500d441e900c8042540482c822609260b81c21604207112141ca6100c0c0d030701d03c2c00401840c2140c25034241c8e0780e60054100e9840280c1111140e0038800c4074248140d0194143d10780160074408085c074900d1007403085503c140300b1140007803c40d4400d840119040b4502424914484c0304c2d4580f030000f484420310080c5440c1440000a1000c4c5400050480c104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 418494073 1250 418492823 418492831
    0xd02092e0315090c031e050f010605010e060304080301060c05190605061e01021c050d020703020c01021b060702060901032c07060c170c07090e010b0a09051e090a02061204020108 78
    0x1040c01c040301030340029116624902170300e901100401900b600c150283d10030609400c405801c40c0304529942c000303204103500003419a0001e0341c40d1140d681e601000e00099110980b002044d1540c1040100000c40c46001d001e420a442007082d9814600303d100c8030103a0b109130340000e49035240c0c0c0b02c06000300d51805811041c0c00c0307902d40300c02c034911000500010b51601c60744c0e000b00c3c1100d200070346100c1903d40b142c41104e19801c02d10004540b9010a400c2c003d60301c1001c006100d0140c4242c0c52940c090034450f0309260015003000740701c3d0b07180403402d500740141500300200c214141601c030340702d41e03c80059103c0111544401072030b101350741c0d103000c0001a16001d02a44400b05000101ca2034101140303504101441c000e00f0116080c1d85c07410083c2c070444c40d01101c7d42c40301e440c041c40c0c0980e1200800e4107401080c2c800c5c008442c80000d880e142c99400d411204192081000b014251442501c7c1c48595100d40d1b81c881c0c03080b001da0b42d0240300354003c0342c0b02d5888000340ca010b14581408000071903800031501904 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 418495323 1250 418494073 418494113
    0x11010f0f140907050f0105221a0301080604030c0204090f030e0406050105090102100b0f0904030507050706050301080c0409030203040b0c03030123010c14030f0a030c020705030c0d02092e03 83
    0x1070350030301c04152a25806203000d018000e0310042120341d000e074007840c01c1390202180c0300003180081d4440000581c860026016000c20001014841c0c182c291013a4281c9040c3c80c449406841107031a0741ea4107440d4a1402c6000f01c2c1c005403101c0a62012420792842c05c096180240c40e01d0035044815000c00c0121107480d003045050000c240050360365a40d0000c1c0c80b0000c51403046000a558141000252141c1c48a841c11980070201701d01704002c05501c10080d03c440d42c4030704105c80c0c890b521070f42d0a4400d8002400748004a40c00080c3d100d24a1030581c002a4119010380166450944c079041c3c0340c0003c0d408901a035215501c000010400391a05e44420000400340200d920911131101000902d0b451a960010309444a1241c0d81003100c0f000344212501038503000d502c103a440c0f2403990094054852560200054004c051002640307003408aa00400008002c11000a0350314590800c0b10100014048080a005584c0d4080c4118a060b1701c3c9951030414200f80c6c0d8030b040c07440c1f41914172030503043c0611075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 418496573 1250 418495323 418495361
    0x7060c23070b03040c2414040828050609030d0c0c0809060a090b030a1505042c0304050306100501030e06010e190609020c060f01090204150f020a020301060e100b04030804090c11010f0f 81
    0x50020041049042201016070035221140c802b10407816400404c80d0140160098400344840c0070b00c0007006050003081c0030004c0c800102481c00560b122507c145020f4009281044420000c0c5400c3e00101440e03041070030302d00e0304541c5031414002250011140700440680d101c1c0c0b101c0010044c2c8440070000c040444003802044040c910724034020800c2c0c0a0380440d20410500f1803c4072400f40240d601a000c058101d81d11858201c00c40d00c1510123510546020074941008010041004100320307042e80d110848410fa00c3d00c070034898040254654540019090380e5003004a184c04c141e000a003003814048005203103d051805034464103038010f078000040c5610400080080b103005028901d584002400c18501c01ea00702441030b8100342c160b81c0b0096140d460100d003c81d4807010310b05003d004202c224401450582c035025000c0c4180306500000d848502c007400f080000300031642080c0f40300240e078a401c115a084a100107401c2d12500d1070740145c0d01d52140c7c0030b02a21205071049065442002ca003030700c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 418497823 1250 418496573 418496579
    0x91416120518070e0628031103030d0c05070c05090f070e18040515090d0e0f04020403080c010c02010605040903120b121203090d0f0e10050c07060c23070b03040c241404 74
    0x200340a040c6100042048c000c400100402d913505005543c07005c401c1000601031102d540304001c0c02648a22401c072084c401c0c03140040381d036040c0841d40c50312512407005800b0325529410802e68408070040d05095025800055000d1210311304030007940103a200301c000744125813144040c0c0c01400304c0201b0004165200c480c0307035a81181e00c0942c071420700c24165100002c0d088030001050180c440c6d90000f4143c8000007803a0900c0c41c03815072000c00380030080d6000b082040d44500401c815200c1807840540040e1184003140c0c011205580070030301048005083d00200200d89603643e09140c180c0561b00c41101000c0700300144410705128455102c1c0c55440c1800d0044140d11002d000550001e407124080c100c1c0c1c0881d44207440c0144111560710728440120b0b1101550b501000b02a00c51540f4101c82c01f00d440603c241807101e01102140c02d41030114050140281014245100c80e0002001903c8000c0503641c0018440462020410001c41c2054401c80d07031110040c019101008058503103c0d9003008220030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 418499073 1250 418497823 418497889
    0x1c050f0c03060a050a180f050d020705180a09050f1c050f0d0213030516050102010614060f22060f08061e13060e01091416120518070e06 60
    0x10756101c400c80d100003803140c0383d02170003200405040300130a02c0c0c003489804486c03e00c13000b1604901c07054415000c035003070844034200c1207844000a02c03615800c2a21001080e07100304e10000c00e143c2c000084d01c400152645a03403121450540c43c00d000c605580c000d00001c06074500c020b400d02c200c0b40d58504202d490181c00a100500c6032280c290b040c45400d5021030050151200b8400140003582c0110440328406010b9038903903c0d035402841250b0256180c08000501110a2f540c100d0342d9180003003000e810721200c04c10480151b880f04034180e8100d90002c40024910a030f0007504030141400d65134070841413403144005005124080c04151040b641860002250051a0380b40443d00f00c080e80c0c4c90910b5880d49070703020007810f41c07030708010546034101c3c0002c0b0711a1017540c4004000c100010001440752100815204942e00420126001554401900c100b0880940180e034125402c107410910040c00561414101403c0707421404049505a09002c16072415100b4400e0959000903616107004400c0a4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 418500323 1250 418499073 418499083
    0xe030d2703020c100309020306330604050105033102040b0f1f140304061a180105010c0c0803030f0402130b0d0212011118041401141e1c050f0c03 64
    0x501c91041c00c10340000e4130840c0c4641c02607100143e019089541c00e007065044944040031038070130302402404000d0000c09549101213458403000c0040c2003075227000c0c00e10004603010351008252201d003128000c1d0880322034000c0c0100410200356080304009110047c4100030603990402d910510500c45604000700b1580d03001c500200002042055000580c122a416107400d80b02151100c00d0520200c200400d001c0c06400940e10b0341162070352002c210034072004001d0200e07086044071800159071001444154001c805011080d801030100b0b840746c540c4d038201c9525590080f601181c0304021340c1c00b804114180f2034004990b000888006010004c0b13503502184c000716980388040e20640900500c19035044080d400350441414454005076241001144851602e02c0c92106602403407919202c1709421010540c020706035400c0d040005070300c41091040000000010005000740c0c4044445990315a607880407200900c0c05003500c1b49090303500c5003816800c0c4030030390603404210f40140b0b15252181e600468 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 418501573 1250 418500323 418500343
    0xb01140f040b011202070b010e0108030a090603020d1d150a060b090f0f030a031706090709060507170d09140f0705120127021f0806040905010e030d270302 68
    0x140001e42d912030400100c60f190b1500404a0105100180100c14441d5144030241611140f10025986903660204995a8030584400c1800140320520034482148070307400420034030031041c101040040e07880c01280f404a507030602d440c00a612003000d9000c030b105030795042c07540450340c00d00820860745082e03918451071080c0382505102d002160b40b0013089a54071000145005400b80407240381c00c65603d005440065903225440c00c0740c1360b000004d150b034544544500d202d01038075035403016010703e03080302503804c1c3c0c00c040b604403540b405403000c480c6580401d2000d45507204901c071000c607a00c4070504144104100850528200360007502c1410742800000a4070001c4541c01c0d90f000411049140c11b007801405060f0405641370805a0031541d403c107120355040303099000700d036844120b2241d1400710720b15810840c14940407540850020300f00703190580c40041018022800403c0d21109051000d0555014201c3d0f51001c564401c40e4040c5802007400da107030014080002c414801107251000313581c442d881f070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 418502823 1250 418501573 418501579
    0x1d01081902030a230615010c0201080402031014150d0b060910080307050102190e0d080d1113080c1002070909020a081b0310110d0e070509130b01140f 66
    0x402048110744081001000a0390040c004c090f1803410400024031160030f1a1650400b48200c4000c2605900c10300c40c813510481058596041c40e40e1a58015601c0c4c2c48024402c0c0c1e410300a4030082d0b041c42c98107001e401e00c8006045842d44203071a04440100524484865080c0240ca8415900c00041d0740704022070381040b82110707039401c203507141c0701540e0580469401090040c0404034040c42041015009807040904903001c074080120320303c00031106040307151303060b5600c0780c0110042c802041540e4001c006105052001090b030380c130310750740294450307200006002039102c403400100082d803814030110000c1c00d400c45030340c448000e008000030340d109080d001d11310328166a41e0440c1308641d141040d9600514a001c2030710308001000c0c00f01c200f0980140302080c028016402411b40c000a01e20074609079003500c82d003043c00c041c0c0b10250f140007080714846054081c0300b2004040381d03d5440c088581d220f498a82d02410881c192840e00010401060303000c00b0103264101100061036864115611804900ba = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 418504073 1250 418502823 418502863
    0x106050102160528050a060804020f0108060d020108041e0507080f0703052a100302031911040b0f070f0b1905070801050402160204180c0503060903030c0a02160f1d0108 74
    0x144d820300b0420b02070b42e03001c503a201c0c030303991030005041e50010025032145008a40f200f03040c1c980940195840c0c281218070381d174048541900c0500542c0508519a0454050800b20500340040000c00c130750f9485107942a48c00b43d01049040050343c0c0d0400031610b000e00480042d000183c51951581d0360340c011000242c0c42030588141040690000070400c29080300014a940e9281d040110058025401501d0448002003509450f00c082c5900e03010705144681401d084038038040c0380a4101034035400800e07a0030001d100401c0064042035984209a10040c000c8a07281881c0c00d000d003c20200130004030081c10528101b6007045880d640010080f0704403041901d0150380c07220380700e00381c4c5d0f6200301d0608000e40c810312700300070200c211402050113600184500c48060041d41c44008261356040c0403076a110351544100300040120603090058541e01c089801103e5100961450600c031780e600b0340c0c20070815612905c3e010041c9076803244001d041020b03048400d0303176254180b4034480d84034811030a04025500038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 418505323 1250 418504073 418504129
    0x5090109110121022113170a18031416050904030809010207062a0c08030105010302070804030501050106030207030f080f0106081e0c0d0c090e0f07051204030201060501021605 77
    0xc001c2d002595000e19903c1199150415000c07500000035030386100203510408800a003100c4801740115200581000e0640201940c80400d203a00c0d030301c01c0d112401001928803004000300e00e500b02d01c0e40230b54800c013500c95040e09901d01c014940b10101caa485011101403808000e1910f41c0460140c029425252040390303941d9456000d070280c42142e00041c0b04600d4a8503509400311104060500c1148600b0103048c00c09180034100e45003070001c9005402c0344c00c03c1004000a600960040c1489c0d8030400d00c1c0703420075035030361550340c03c4400903803140d00460b0300020000105a030112014080600c141020855410011490080000e050090a0034080301c107010888071f0b4003054400508003d900c2d80d010035440c2403e03440b00250050a20b840016041444011819003c0c030003520580c0c690481c025101e903a051002c03032481202501c4441800000c02a00c08107106c11044148950700039000821701e28a000002460700c1c0c8404042500000d54801c1445650358641d0b4403100c00f40e0899400c80e032250 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 418506573 1250 418505323 418505357
    0x601170610050f2802070605040b07020a050a0803030708010506030403170c0c011104090e010204120303020702060f030a0b030c030d02191703130327090c210609050901091101 77
    0x4903c440b00d8503c01c03408a9a1504084941ca0308100b01d500401c0b1529064030485003603942d9103290081c5004540140001d2140c410085e000d000110b0000300030585082d52400412900e10300340e048400203030000020801d1040e0010481401403200303070344061551805480041c005107009007101811840080071841d4882044241c0c4e0144400100030400407051030740040381075005200700c400035030405862000421040c4280c9044543c40c0c121034008a0003564210025880148102d92200c010300a240b20618070310065441060041c0000414080d000d003007518201000c864288a6070001c003070f00d0b4201c6d0f400f054408020a0366489400e4281a034540065104500c3d034000203a10000300c100500a5161146002054040d40301d40c1c0520301c0d80c40103400741c5140e001040c2d00c60740300071204020040720b80e8840229040646040351040b400c1c2107110052002510b5440c00f0580c81e50b07818052082c540c810150092820b40080180d40203a13940c2010302c2e5101d281c03030b9050044040c136060503e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 418507823 1250 418506573 418506577
    0x27010c0807060c1727010c0801030b19060f1d010305070b0c120c010516020a03020307030f030f050c0a02010c091d071b03050403170310170703022205060117061005 72
    0x2210350106001646000c0d1030b03800451408117055440f01e018410f458400300300c10b20a85100b110f0703d40d40c254040e03081d0303110782c01200c1000e010211190302400008414442034424000135080c144003c1d4040e51501113440030410100700d005000f40c0501c0c00410002e03c000440c0e00864481c08035540c0c9403441d498000f400c3c5200032042c2c01c1160b000007881c9101401c194001d611030000782007400309210300004201ea503000461402405a032007041560f020074000c40349c41c2e00056440c600440d040055040c481c00345d52040d10360100d8441c01058407004181c082c010040b40c60a9882c0c0350b581c440c50145c44c80381540004120301c0134600302101041080c0e200325000c201c2c0702601c02c40043d84100c54134008200d50700130704c819070b41c1c008000c203141c01c1c07030025a00716030141043d410110040c1e400c00d01ca6180d400308100c600e10482c0308445d800030050301c2d00c04030302200416100382d0300000c0d003801003460144c4100070403150400850f0b840c0e0510782c09a50100a42040341581c0d02c21030b40e2a41e000584081c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 418509073 1250 418507823 418507847
    0xd0207180609090b040c0f030c180b19081b011407080708040618120b0601080601030b0d060204030b070c0f030c1e05010903020f0c0d06150b27010c0807060c 69
    0x200f03091031064018008501c4031036015a2007280628200c81d0750701c0c00810001d5290000030700035403983c00200400280d240440031041513200c800124829103900041070001d46c000725050141c41d0345810040361200740300e042452016840840500759090380001c006030200303034080001e440d002c0780d030500b400102c0c0d05a0b5000c0e50312100c050b40d50343c0c4502001e028100c40c03800c20785507a010300001048104d007d9000840d039070342c0500c010586032039075001543c131100014080c42c1019a030b8400750300140d0f02c0380070144c051400303000016503d40c15400c0040c50824011f0015041c09035500c00000020186411207a0185d01403410a07039400b114906101002200c85403021320b0444a1001e005110341036210440240c801c0d000c440207845840c2071136031101c80320b11690b80c0c800c0581400d034020900540100100c080c02040d140201504c40e070100c001d5402042e42417403012566618440b10098607111030754001d000742060410752545039200d100a1291040003003401d600c659071011414042d00304200c40c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 418510323 1250 418509073 418509089
    0x50d06060b120907051c080d0905030f0a030f050106020d0f020f010c0504170c0f100201020909040b04020a060503061005090409050a0503090103060b0306060d0b18130c080d02071806 80
    0x910070700c2d2405258100d40550f00120f09000d04040000c152134614038002d080324422407030b8180ca80050300e601d01c00b40c1007542401e00303e50303e499501c0700240050005000b121510000c00b41c454000040080840c0d8006145241c920314004c0103100c410740000f111414181145006005003e01e5001242442c4114440d48801e600740001e032034405801402034800d840c0d0340380014800022000a01d5074600700c820031280c001058412886140c24100000740202d003842c0000742c94031a01d030300030500c0107030701b00c405560901001050104500d40803140c41c0c010b0100740b5109046d41000d1002400729042507a1080c00c1c0b0000240340700058a40c0d81004030740380d42110544841c9005c1d42421901ca505c0700e04070306e0029103000d001003540b1003000103482c090342c00949010f040009407065840100b02d0b40000e1603000b8610a0001c400004600c2141d01c10605042b0802d1138030b48501e03050081e4030440e0861413098001c13528219100e64001996400c903403005001464444540c0c4201c4018000c40d0072141e0307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 418511573 1250 418510323 418510327
    0x301030f0510050720032b022a0d1409010c0f080705011a010c05070504020a02070b030c09010320220b0a02030909100e0408130b030f0a0f0b0a050d06060b 68
    0x81042c5c0c10400840120003425007001c201074980d96120780300d01c46d1094003421003101d2014120320f800701d402e4880120511601c0185040075a89815413007d285c650b010f001d6464545801800e03550501c400301c168452810603104d5035007a034800a01c1d81c040e40003158100101c68614206004050303100d21042c1e60404145952040740b820400e01070103c0b080e40007002c10401d10300300a03551148017820780031754100000c1c01c1240e01b0b010030040079602c0358905108600c00c0b0200407449000d04002540111800140d0503610b201020000d0709480f500000d00440b588000f20005482e50349100b00c0341024031120056444410342591a040303020140c00108078048040354444106400200510300000c0c00c41d007a4515585184130302100d00d1440c050000d800c44140c0c0401d000170700000103415140401d61441410f04e4071048012141c4d002290509021845c0c0814420340148070710071400e500b61840360910070181d00c600070500b00e661900c01e90340100c810211038024014150b0222000d031040180c3c5603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 418512823 1250 418511573 418511581
    0x1116060906110307031b020f0316060b041d0c01030b060405040b011e020d0809060105100f0c1b030201030f0b09010b0a021f14011d070807050904090b19020f0301030f051005 76
    0x9006046200da8440404414424240d0036400020300c03207042c0230700707500652900c00581041c69514030503203c115074842e124916a5515a581e000380e01c10006c418141c000202d0003440118034200c10040e169051510381000341e8040d86a2804480a4802c260f901084980729030004840c00c41f030072000c8000240c0f441404180f0682c3c08240d04d00340b03040542d128007568440890154590400707104056107c0b003a41c441801141c080c1d0510b0b500e0503c54100074100030501d40781c0e031000c0f4a0500f6910540341000405108560700362141c408400c1001070b04001241642000c260200c0c810700401e000c0b07000105401260710302c03c20441948541140400c00745a21040041e009030a11000550650440310000b05030b43d601d02420041c8001c1109102025072030b0030f80c050714103a00c0a4404000c00404001400c0ba175226402101c01d0180b1501211485241c01c80d1380c0342c0707407240b19517034018580d004100302482c0e0723412402030b41e054070303084140c0003031040d26071030550701d0a900c0e0105030640da41414104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 418514073 1250 418512823 418512827
    0xf07030501061209030c0c060806031002030105060a03051807080a03140702010c060e03090d05030304030809060405030403170f12100812030a181a01050301052d060103060918061116060906110307 86
    0xc20f00654080c1c0841e03414400e03605100cc107901003400350641001082c481d0700e051078865005103401070542c0c0300100c260b0700c5000301182030001c640c1200c0e06c0e6600c08401c0b10101a07212000340e28140c411001a401d01c41c07590700003011404194030250003684c070364040c610004070074400c49025040003010070000c4802440c00541742c0e00100c4055010400c01c000082200c803000c40c56601c5103034040003451030030303085039036001c0700100085a07140ca0390000e02c00c00401515800044c00f906c42464402402c41c40d108c804040c03180b1484d000181c040e0082c5003100128422103055a800c40761034072001c80e02c000c0e00c114021403180000006001815007503558440240400f8840c2e0594209072300138040396480c90741c00000310102d04000003031020b039840c42401e00910550300c507811007014500070880c10764905c040820344140030401d000c00010103000700c04121081c07040d0240d41c0d100d503000c1c6040c0100c0a01e02c0d031807071680e5540031f0700b03090700d5030b540c03000300a042d078000701074002c2040c07a0750b450342007550700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 418515323 1250 418514073 418514087
    0x1107211203020f03131104020d050a050601110a03030209040905010903050c0c150403020607020d02040203094b070905010f0914061516060c05030f07030501061209030c0c06 76
    0x960356124101900040036100c0c2c000ca454a504948a0520b140c4070740f001c1290f550300791042620f804c242254186030543d03e500007841406c0c4081c502240500749000c0070001c5800180010f81803081c04203001810701030118a090049070507080058640307500e44003040240c040880e00034000d507c2c00f508501051b800c0070180140340300d0101140e01e0705441e5800c0c0801207035030300e03044c9034140d90030722040005203410f40c000e00c3d85a00c09003000411120950100702641c2082e5442c21450300050070544401105141c0c2e075a00110481c0d030750082c01c0740070f20521002213000100c4044650f003841a445140d004201c0e07400200710480c0d08116569444a440e00c035540c103401040002801c0120108080803103d40740c9000c1e038801403030100e803000d0849903084603034003082c0c0c0b0007110190075500c02d000c0760840c07041e03100e03060145e10345503030324900840000030b140001001982414505401402401e070710403002a074030000504000b03004071031800d043d07584041c07040e00201440c1410202141d140d61000e5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 418516573 1250 418515323 418515389
    0x312131203090611010c17130c03060501060e03061017070b03010605030610020f070b03062d120601060e060906070b07030c030b151c02160501050405070e070509011107 74
    0x92201004450101e4950076a494600c12900250b41190b0313400101140c0781105800004683d00085031541c1270b59400029022580281ca8050f039640c0100076483c0c10039201000c0c1d1074104c015080c94a00b0b131040c081440080d01070000d1481c42101e0100ca4030f40108600d80140226510294485da0340c1d601c000c202c2d502c01c80f2503d0140842c1c90400f0b034845e0000800d601d00f038075800044c08045041c85030361803958200800711580300910804e039107512135565101654609e406592180134800a8003400308107a4608441c805603449a0010005964480003003514440c04442d46592980c0c160300140c014055610003a0003e4040301c207201e078080d0150303c0300d0400790a82c0c8050001204c81e40070840000d02c0101d0a0080070340405c824005007603803c6800034140d94102c001410f042d51524558010005c0034021280b6a64a0051006000007041004c0042c00200c0c10b13210b4518041100902602601001c036062001c800034400100000740201000342c29529000010100707009000014108054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 418517823 1250 418516573 418516577
    0x807020307031a0a06141e010504051804120512010b181f0207060203030108150405100504080d060801020406050a0f0c210815011e0203070203010207140c0301090203121312030906 79
    0x5800606d07010012480054441d0041c07009080503030401003410b004982403c3c485c1000380400c40443c1903a5001d580d070103011080030a1000c0d030301c3c1501c1c02d46003208009003103000f8482d06001c3e100441c140d05044c507041d2989500300c0f903121440c820700014280b0406411947c01440c003500242148a002035080c0441d10590844800a44e244416601c0f40701c01e001c4d00c0216040806c100b42104000310040317400c5031090003281d5040d40402c1a9004488042e20100c8040d07000041c2203c0624990144c030000e0090140210705d030502d48000a46284501840e1405108d0012840781106000300108a0786c503800c0311010f00c8802c41040c100540c01c44041c00080030030a00030108080c2e16052840b21404141a19211200b5105a0340b2000b810310bc440c0400461008011110040c2c6083c006400d0640c800c100b030003e83c4003411015400c0216502c05036001b0782c500000100981c0d4005030940c500950f81c5626590344c101100d800ba04644c0c2900a0082140300030301d0501010b034001c0e800805c0307070896 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 418519073 1250 418517823 418517831
    0x50702041e0b191406040f0905091209010909054606120308180706020a120c0510020d020702370f0303030519090303060501030c0203070b040807020307031a0a 70
    0x2208202800c04081d0f460004405841d00c10320000303400007410072070300b407000f0181401c207550b504a4107507003220341c1c0000c584140c84405014130604200000c20201c0594403040341468416130000b04460444e00c6090503450f2504042400c3d00100489400124168485104460710031505c10300d600312100d80100984d280c3e41011402c0b040284999015182008681c0e080b922050b00e0803641024041c00072130120502d01006005440100440310040c200da0700603000d00d080a0601c0242079050202c1842031000558480c000a0008174820320b100700c0c214001a200c00052042a00070f0140001c0203400034003101000d00040007a0031052100341d8081c14400e1114040310800c6405e0120b8030a5524180c000c06051000034041d403c1143d202c1c41440c0601030018100d404041508e104500590200345c0e580014005540c1c9400740d4802031032180000c40ca0076103195601003400c0d0000b0006080307508040340d003d0455505000c240b0055410a243c0300c0c0600d00c10701d8047c40c403001503c1d5041c1c2e491038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 418520323 1250 418519073 418519091
    0xa03060f0b070807060c0302130f06230313080408100501030213090203030f0f1201120308010f060509010c110301090b010e0f160503090a120f0806090124050702041e 73
    0x954102d031110b5900803159800e00c0c640d541e0b1440603007101324183d0181602400704080760340a42401000401001c0a020311491400310b0140070701521a4102d8403650148440c003400c4544001200c0d04030b8210f5070094041c07611828194030070b00032504000c0c000d020300c0c1d00c0e040031101c07030341c00a41c1624000c880003810341100040007000c44210050085d0160014003c410b070106141001c0c1103156015086e8a28084003c03000740c2080324260008001d0b480a411400e00703050b8098882c070701401040d43c0903d402824030801800602401601e06e040050301c1c05200c04000c2d40001081820801400a120342e060a140c9980f40001c24003c0d50182c25072080002c940303141000e4030130b0203031880505409a907940e40008a5140e40003c1400480d0b22481440e01c001174921285a80c00d03081c9551142030245c44180c1c01070400d03902030b000d184540469001400a4070b000000e010b89a05107000343c40c140007101e003007561640101d24010394032601e0036500b07022440c2c10401c42601c3c4d002807042003183c2c00c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 418521573 1250 418520323 418520339
    0x80d02060903091507060f0219030e0a0b0c0f04030516051005090112180b0f160c02180711010608030715330308190810060c1e0501020a03060f 63
    0x11601d040703901c400001195807240c02120020004140140004500406587c07104000e0307901460100341d803400400391140e0b10b2540361050351010070111015109122494440c0408488081c000481398200080e41880503846001120002c540c00826240150110f000740303000c1c51460701c100f0b401644081d0511080900c20002c032842d4210503140c2e400240e20300c064002c018500c448450b400390380740703a5510f00030a4150058a2150b01d01054242440ca03100c90008100d48552803540140b103c054103050060b5103d828800f000c21051480c105035070b886800413100c81c410108141e5655190400c0840c01e0350001c4010004103000b5940384501080043c80c0300202c03280c2315040d01050800b140b4014440e4561401c0940d00729203400700700c0e02d1a80340d440340141c65003c64000700d010351940c4040358005030804480b90348208143c400210707503490440b01034202440c1990081601a03811001400c2c0d207510804800460f401030021501d5889084000d002810103010740c54203078000c8200054441 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 418522823 1250 418521573 418521577
    0x3030218031b010e1f03051b0d0618020f030a090507030b180d0e030303061306051e090a09170306010201061a0304051006060f030203060d020909150a02031005010c0516080d02060903 80
    0x880c00445c0d82c041c440c000070048008110103028140e4410a0510303004992220034003030070b00340104100c0011842d19205081c4090309036151501001c60041c0030302c1d04240d51040c1540c4d07000c003140c0b8010036251144d01d040e0742050580d400041400c155042400b0700c031405a6028018550040b007150010441d02c9016100b6640600350103a143d0f01c100000b030102c0c146045c01900000100501140307058076400010740d144081035210302c094207810304800d1289043e081090b00000315040030401d0140c84d072904c0a0816403403d02240c00f0304008085510ba034400d5108200914030050518155074242c141a50b00b940306440c01d41c6c0b640300740c2480d41c02807080761103030343c08445039500d03130703490030700f01c5407801c1d4041d4100504450303200800805000160302d6070784800c0c4c45641d100001d002a010071408103c0d030660013500d01d9048030303c14802c004010030100810b02c02d8842c2401c0000d20b4803903900d042841c207a800c000328540c1c0c51690200142c50348000403900c103000c455070281d410654642595655034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 418524073 1250 418522823 418522849
    0x41d070f1701060e150307110c0406031703040507030f030e030606030105160c080f0c07030c060804080f03090a150501091a030a03080619080318010509090403030218031b010e 77
    0xc1c1c0303401c2004000c29400b83c14903103402e400142075422206241000e15640e071b002186c60a0201c1c0c81c00443d0040e00e00c2c00c0c003500ca0f11031021603003040301a0450305c681c40d24032064900540d03060000000314060100801c4001c3c000c1d54400c001c01c002602624004140350000ba9546000307100d200003042c090b1a041c042c162041c2c2c611007a2400310303502c0300c00444542d00100801c2d070305140100046803000461000401d00500c200340200079036480c614214460b841d2a5110720200501e080921000910b07540c02c84502c0303a4541422a00d9440ba40400da082c108001c8005181040740c4040003900315075034000c0f90403140351000c20088554181880c1b9030b0380501e040c20a0381508000f0907480003034020044a500100c0203800c240300d80464081c00c543c2c91840d600581c4940d800490050020008646006100b41b0280f034074900305141040420080040035000509250b008130b410042200502000000014010b04a1351565110903011290619072134889000030200702d0400c8081c20818042000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 418525179 1106 418524073 418524107
    0x31109091005031204060905010c030329030601050a030308190e1608100e0d0c05031608040504060e040201021b01180b030a0b03010608120d02041d070f 67
    0x500b425099100c00c130510104400e2003500d0344480010700b00c0e2001c4c2804290080d86240036409044007691001414444010001c1242080c16140e12180030039019500d099880d40d043c0207881504e404080c3c042050b0601007040080c590710308800201d03000c0000550900c201207407070301384101113600701c2c4003035500f5000340140303441405110810592117000700410081c8103090340d180d142559201d42030003000242d40c1c0900c00d040c001c88607100f8010307008200c46049031074801e03016041030050703e004031f10b040c00100310300c03075242d06940c01250140c0080c29140b15084451182c000400c042c1410003020b0441420301a052122080241c01c4c420382c0e40e500c07882c1000d031130340c2201d6445450311b210b80e04050080200c8100452081c841c240c030b2904503592550700a900d0406440703917500c41c5200024541407903170001c1003540c50500452290f0344541c6503000c031007000ca0ba52002c10869070700c = true := by decide +kernel

theorem cover : BRFrame.Cov 418345323 418525179 := by
  have h0 := BRFrame.cov_init 418345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 418345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 418345323 ≤ n) (h2 : n < 418525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
