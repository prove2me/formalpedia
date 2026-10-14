-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3792
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:41:09.888172+00:00
-- url     : https://prove2.me/submissions/a2208096-e6a1-4006-99cb-08101b8b2095

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 681834532 ≤ n < 682014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 681835782 1250 681834532 681834539
    0x303060f0f0f080313060c1103010e0609010e03190e1207080a150c0c0308060301021b0709060b070804030638030c01030606080109020304051903021c1718071e 70
    0x2e00304105036100a04030b8005000b4000d8591071801c0172002c542d02c9180c40580301d1070600306401c1c11100507540950561a14035200c10000c4082074003413203100404000c001d400c40480541d038981c894000014100e100e8504100d1400c6e0084003490000c20001c2d2001d0280c1000c1c40042c2d24009007a0011031b1709034801682c00d410808181c88207548441d042c1c20034001d07484503841c00382103541e119100030144100003000910701c1e00c00354142e0300e01c850200791451202945e07096080c1c64650f940a0782c0162810144041003400c820070407107109a6014618034038151440c1c03107120081910310882201c2c0c504060582200190707000f01c000d008a95006494080383c4068109403030220762310202c605050130200100003c5400407541c1d41100c0c0fa40c2c40c05a84c3c1e0791a85002800d01002c4100d80d0074101411121000f450b9001030140c481d110041c01240c184640018251510241031a04401001c500e03000070340c1807100c099450040b1902d50040707811041d22802080921200201100c00c26200941c041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 681837032 1250 681835782 681835799
    0xc0801390e1e0a050105210c131d0108151f031415460507020607300e0c0a120c09060803032707090f05060103110d090303060f0f 57
    0x80010402400c1c000d21f091442010040c0ca0281d4205010341a1082c0e000070700070b00080c008903014030300c20181030032005881d00001c034641c40030807155110148288001040c0f2900c0010b00040104445240c290301d0380e034840b80040c05104c00d10300c0001a18100f040080050500c041448110b06210301405c2c0c40740c007241d01e20b21006030003006101da0611105c40e1911600d901c000e210f4504502074501c082421140c014490500c1800c986403a08500d4081000390329a8081245801040181d40e800c00c820704501c009000144404040e5100300d8094071071202c404142d60201d40020502010b0360940640040025060302966101420080001100c5000c0001c588404d502628102604000c060b0601605542d2408010035503001c05005e00c2c68420300c0780c034450800d11011412012103c8164680840102906075050050b4081d4100004034101e1341c001d00074455102c20202081e330411600c005410090401c81d1000d50a2669656000c01e400c401c100300703000900549852662900d00e0304085 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 681838282 1250 681837032 681837049
    0xe06010219031d01142809051c050a150f060e0c0733140a09030f0f030e01110c0601080d080417160c0801390e1e 50
    0x210368441c4021010300040d0704a00e064281400c0102040200110000161038000d041d081403404503002080b01c0c1c0031061a1080300d6040700f105240c40701d43c8110300e0000e49016805e4091380c0e80c08600c5d12070007001580551002c0c05024050001c5810480700c0d80c0710301a104003403145184040d40c4413007040c1401e291f14000c000050130000c1c016100c80c03034051a110070b0750188490050003101c00156482d0f803014031f090b031900d45110300420016002c151904660041000030400c00d414148040001d0b4400c1c0302d4801e822100f500345d01e521031466280d040c00c40c1c0f507882403005071061590300d0440c140030030024401c40e03c1c1c1180d11444076a45a03e50b022261034100d0581c022403580d44401d0620844d02e81c880041d68119030300c1203980f80d000c0383c4042103650034016401c030f002200180000394402d03c40b200e0b142508503581c2340e008210b1090f00c520042d000c103500e000c216002101841701c6141c9070a4808501003902e10602e0200b002c03464a80c0061002007900f600c02c0c40444080082d00e5240c548540f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 681839532 1250 681838282 681838303
    0x15110a230f090f0a05060d0f0f050103120c02011806020601030b181009060f14060f0306011208161202030a0f050a0905010c03091e08060c0307080f130602040e060102 73
    0x405081c401d800400c11010b00c11410501e000e2450510a1003140e154080342c2c102622000f880ca03030b280c0c040b00c3c40a80c01400e400c0c10720342c49641003046850a01e03079503102c0d95050380d801a04074030302843d28810aa56149521400328108240250010400c0c2501111003001e05581e5026001d19403550400404006000c0c040302c480740204440030285130400140c411484030000c50108000c40701d8100a07000704842c070680d989203030401e9042172000814803545440f4580440f500d40e0131703e9082d8141075a030b0200b4000c0710350f289101800c00000c030700d18101600b101002c442c2d20250b1482c40d55aa1640200d6000d00354000d80d02c0400e0214460380c03c8500c1201070040c80c0303420340c2060000000203054059520078207040c48206000001070601c0703074201700c015050350034256840320511442e01d0440400b901c2424110300491021904c2a803000c03040b603010b04525991138129469206420b0004413020b4204c0d4544504a501c40b00043c1941c000b500082ca901c9050400e20301d4103400280c10124441c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 681840782 1250 681839532 681839597
    0x1050c19170f041b06030b011d24190c03020f0d0e0d02040e0102040803090907080403020607032406021b03010204030c030b0711010f0b0a08150a15030212010209030d08090a15110a 79
    0x29282e1076a9112a012b50000103218851080b444480a140c10710710701c41c540590400040056900e620260803001101d03001e440781c1d0172591035030981c1c0c82e00e94403890101680340004071030a01902e40e524080e42034211180c0010000600f036945008100d00f240d00c654400c0302c040c1c02c013141008640c0750194000c1e0b0b005105e804c199030b00b403405990003510b50b8001410381040c035541e0b0340c1d001075280c80040500741404500340c1010209407a80000303540c0e48041c100301402201a0b00c1070450508060007500d00b182d50010042140390704503666581e0b1608001c2541041007404101c2481b4032000740a030720032141034180c1c00980c1458240500000c400135400070251036000d0b080300010032450340c00c22a803003024900005945a0080340d00d2080c58000d50019502c0740511900801c6481306500038031240b40110b08550181966400680ea0b400f02241d0060383c1d0381181c000c0d40003090400360f08101100313000c400001c82414507400005160003d1080305c0020f283d11500103001e25455250741c40701e11420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 681842032 1250 681840782 681840827
    0x603030a1421040302071a0c060402060a021203010303090312034514011a01020312100f08060a0e03090604170f01050c19170f041b06030b01 62
    0x440c0c01900e00c111520035140c46500c0001da003110014280300d803860a1000ea616094a41072505000b9601c42d614020044092098200804040c5000c0c0854480c0140b19004d000a5500c036020401c5580040d0150820340c0100400d107203584031250015806984281c0301c0c0441141581050000004040307201c0b010b161070890201c0360510303141e80c4903011b44080290410081c400c4ca00320381201500348698044000c0303a003020b030204000611680c000010400080020400e4408458446401c0c00041c502580081200c4c1401c6910310840c141e10070300348480d140ca01540e405c0e040ca40b01000341e010018035000741c07050240c101c510f402044d18030102d01d002503042c40340705c1c0d00141041c41244180702c0c015507287c45506040d0014032420800703902e52030017080589042c950054560340045a900c0b810000d0315448102d25000380108024598519012a0550b80b100b240d08040031020b007040e910707110251300c0026901c1c6095003001c040c3c40c49640c08182c0038590030000d4030308148c0c44112040c91284 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 681843282 1250 681842032 681842047
    0x809061b0d0e150f090d05030c0d110a170304060b060a09090c021f0e010608030304060501030c0e0f0a1d0a12020111070206090607080c1510050306040b061e0301050406090308060303 80
    0x3c020698407001a500f0780103680d8441240015520007080d0402051404042041c10304100049189100a041ca84031a2644071400c030105407100002003008001034a101500030100d5041c1d80950b90041c40b400c0009040d0203454002102908154510f80c005003228401b4045034059014151401c80240014411540540c8401080342c008000da000050390700c000410380030b038003508000010180c01d010740c0c1d52414103003080b1014113030034001960b910540e00d800142500140d81304d030748a40740140c000c40e0030751a0300039100068000060716440c2954030911448a540382030003450780c01842030b06d580c40248961803010782502d07000010026412014003002015845400498080b4101200c401e5614031040c070b8455618082e24503070780d019100349c520360346c0030014409031213001e13060030b0740c1d01c51860703039901c1c10503a548000705d50040c0030740740320000300b0b484d4204600c07012003041d0071440380c0070302a001c200070030b003194030031501504c45548500035401416082891150404e05c203a02951516a9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 681844532 1250 681843282 681843319
    0x2150309060a1a0406121202030319051e100e0a060503150c070b01080109110f060919152102040305060403080c04120302010f05060604080a0809061b0d0e 68
    0x9000b000449107580b10342092604240742d00400d0680b00004200700a1766895401d42614941c4140007268100a0200c030050390360b00006c2034a00c07030348054043c00d180d024004044d00c060301c0b01030500041041c0f240c101418525076190300780d00c0b65401d10349544100d440c003414040c0140d005080001410702d0040240302c40c2d02c0101c2d00d40da1060f52010300d00f078143c443d400301506500c41c45801910507407040001003070410042d001160b47ca805030141110385440c078420000d08071807210455030300800412240c4503a04041404200c2d04449034400045240d4510700403441c0c1c0e64806008000604c1d400c60a0882a602c0c44000503000400c0001c42c00d02e420765882c3c60b0b40d07040261014040c8640e50340000e004c1025101190301a0219a80701c030865103403860043d000c0d0940c0101520b42a060000080c2c290415000396000c48440d00700a05401c00c481d155507405501c02154a40c00a600300081e6048455021a880c11102020000e20845d80001801441014103421680c0309030701d406000500ba94 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 681845782 1250 681844532 681844543
    0xb090306160c0623040807050c09070504030b0a14090106050901140303070311012a020d0c0503091018030323070c0b0c10090305210f150d06110702150309 68
    0x10f5201500040b424040c590f1004191561050000190440020030040118110203009502d104a040314044100c100c1040120300b0200d41c644000340080c4410400305054040e00c41d040042c4000010f2000800c0c1441100c203003003115980300f030b0303912440300300b00c3c508100b2546c90040c511100c005808004040000c2e86a21840340301400700000a00801e085001c04e60040c40b0540003183e80058020009034240c4000412203500005401016855410b042c010b0f0040c10300c280d88a4051894081c1c903408010100320160300d014200f00c04800000d0050300c0c203034083c4000d907010b600d40e602241301a8861250000300300221240c481e100344510400034207114001d205880c402c00b005621410307460f100c00d2074100902010340d421070420081405140c0c00c58000c0085400314108001d080590301c039407481701e500942d030301200d03141014000744414220f20071440c0e144200906290403039007107498410036103510003880009028006010011171509500440c0601c8500507400c1c114139140f0049912607 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 681847032 1250 681845782 681845807
    0xa0506030a020304050f030a030c0311130303351005011b0b06010c05150703051005031b0118090c02010b01080402091503010f060b1308031e0708040b040b09030616 72
    0x282d00840803038200f14013889400c1040b00b1400880e134641c1c0e0000030023009440c07038035003c00100c1e14181c1228005146c600403512001c04600c2c0d5030201c50301d9540e08649145038065402d50003003001c00d0382e004007641003c2e4002d60b40722605140c3c40501b04980c0c0340d00003601c0d41e4481418024442928840200c225814049061f00800f1155650317488a0041c0c80151001c44010700d180a00e41a4002c1a1070103c0d0b414000e940d5640c00704100d40e07408044851107200e500a0351f85c19070002d241c090040701424002c50340000c045c9040c820f80e002041082020000c550018525113072550301003584294244221642400300740b92802082c2840d40215490880150690880c5c2d0481b080c240b0150320250400408150000001c01c1915074440550540da00602c2a10301c0040c00d810000503002d000000303807000202103451440c2255003020b101f44040d030011b0000ca444400c1030000190801c008809000217282c0c2140c0c8640d00d50780705c0201400c182000b40310b82c0004000107085c1002c1603000c40b512411 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 681848282 1250 681847032 681847051
    0x61c06090902090f0709030209390f090406170303070e01090e0604020c1e070608090f03090d0303140408030a0b10050901121b02150f0c091c0b070513050a050603 71
    0xd0f41c0b03c002c0300706e44259482c2c0010707412100701018410702742c10315969514200d1201c200342103043d46283e003100d80500f2030320b0a6198a0340600078907003007200910080a04d0400204005031542c1e550309a0801041030711000129500701200b0810666040104d01400e9070302460494100d07030400103403420316440034090030701031540460301c001c4882080000d001c03400c0100821000380d91032a500e0aa4440c054001c0c0c6002544290204940c0d984c000b03102d2041d01c01e520701071801c102c600c03170501801c040c218205404250321400c500380303204020105980524014461030340c1e03030301d84440b209040d42ca0b08a0706600075140008600710841d031003001e480d1108000d20313154043c01841624031000d0400480c2c0f001a00303504036504030a40e500080c0c1c400c0c5420a9406a51a565620040301d6940c00102d602090005040244405928006c007250980a0f000c1000102c0100303580c840b100020001c80300280480c00c002020669030050782d21260003040215402103008e030414011800b907020103440c4091 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 681849532 1250 681848282 681848311
    0x2060d020708160501061502010e0706030e03120a05070e010f231b060604050606070c05100c060f2a02070506030934091a01120b061c0609090209 64
    0x800038100300b03e6491410524038450745038858101107000740305034030804062084181000c2050350041c001d92981e18a88005010b0300391a00b2000d4024014184082201d40810860820b030180340c1030025000341c408400008841ca000c00007d4081d502c4151501e050101d07040021420303d81c044120015125226020880f07910640c2190381d42d80100060281100c540e42c0e4107455030140020010b1080340111030601c070540f5a08140592486004409851144d1211040c415424100318501401c83d040c81d115901c642c2c83d03290002160311086080c1c101a8482140340000c0310100c40140d40c3c10030310386e90615401c41101000e0750341e07542072040342e000320000710011300030350b00c1800b5024040300400c4500041c801d0391030250600c0d00145120340c04050007840c0209a00120344609503601c405140c51a6200a003180156152001a11202e400985400507801030b80c55000180400c444924003500040042c8003545040d80c1d140d07001520a6440d040c03a002c09642c95441007508004404140310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 681850782 1250 681849532 681849547
    0x10c0516061509020d022208060703050601200a0506070908100b041b021509010b1c0c08010614120607050a140d110306040515210c0904060c08090a02060d02 69
    0x90100036607900c0980803d2000ca040e10302c10166070003c002504021107000f040c80c04c0c1c0024014032900318020640323550700c440d0000780c9650207075000c1c50308841d0504003001001c1c0a964103120001190b0790703054998109111980800504021780354001e03072242004090030b800c149429a40c0c0c40c134030106100581d2681f80104654846921811810301c5a0300034500c5148501c502942c2c484500364000c59540c11900020380c0140103100d070a5529100078541c4020f51481070380020310721050841590030610010000078802c1091003620010700144a8240300074215030104420000b00c1ca0580768a0b030420000c105002d135100c030486040b01118149400d510540d420701003032902501c0d010610091034010b030071203401c002c040950704c640c000315000d014583d103c0c4003031250520764000440e0004525040b50010801902c00030100300841021030311600a10760009200781c030180e03000d6407641ea03181c0d1400c4034160310100c2e603680900c1440040250400c0c40e03002c00c0c450b118a44115003001c0e80880c264 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 681852032 1250 681850782 681850811
    0x2f040914010f0e0601170303280c0806010e04230c0f0301141513090518010501120605060d080307052a0d030615050904090309170f010c051606 63
    0x440a00000300208480c00b66507544900910300310a46864a00c101400010200f11011511200f101a48082d5086466800071a120400181402c519007081d209410309006441c1c85000034154565450601034140100054000510300c400c0c1d034080d90610600c4140742c2e607504c141140e03281c400b585441140e55800288207807030103006940164058000b000240040c90b0540d0310340848411240c0442c4800010703056040c80c802d02c84010b0691000300c1080040c01d4103540300035400a0503801e03000d51100303036010301e0742191000d0700054111500302c00c490080c0440e51291070f501c0801035405201121143e12240706a0000070587c104004000940c0341700030602184143c50040860020103860b107039404016107600601c0700c10740000c0d14051000403000400803511821050035242d007894822128244005062080802d43c14006130010026110b001500503203110109a409045d50780c0c0030320301e05402e4501707254200301001014069100011511014010b030180e01800008030005c0c2480c0c070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 681853282 1250 681852032 681852053
    0x71e0204090506100806011211010c0c080a08120604090b01140a090c0c0318060e0609060f0403080c07091e0e0f1606080901050c090105031e0c04032f0409 68
    0x10308070b0250f9414000340b11180303030410040e90304600980b0b4440c1e03210f030400440c1502d51f0201038003451000c13200300015401a40c1c41e0800500519504118507201d482c0185001880303042120307815000030301c110050b8240c5201030340001d411030b403d12901c080c375140c03040b4200041c080d00c00601d400c5242c80031141e64070042c0c0d03001461030040038032821196001c06481201030308400d0700401c0ca000c6e29080310f542000d40300d1040d107020307880d07903030505540e20103020860700300580ca15003200741040089400065040078000840c41a0300641e40c1e8902c506100c3e081c0b20090f03000c2d11a1a0802c0000e602c00d2704020004100740400c0072001403000d00d10a040e41c1347c0b0210740302d441220702401550400383c030901501380090703a44940b902c880544642400f907089500846032491145814005c030704942d84200c0003075400511002c03240740140c811a6030f00c100c41c541a03c6100205100003805c10400040b1121840142c00340755034a00210719a400100701c0301030100d80a4415665803101c5400c1102c1040c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 681854532 1250 681853282 681853301
    0x40612120513060908010f050709120804180e12120f130c0b18030f0304090509070e091f0504020f24031801050603060c070b07090510020c1005071e0204 67
    0x49030084540c3c503a00a086880c0c1ca0140e10303065420440041d100203100c0c0203490051740c15507035a80a2a140241ca102c0003140c5050840c0d90b900c0401000440040e0061a64103010004200250209540d00041c2c0780001c0400b20b01d00710f800602c07000002480c4501e80c90f5118103510f481e0a1543e0b62040005088104410002c0100c10200008204402c02030003600481e5220a13491055000c402c4c101a5291182c20420780d141e4802c210071300c18400f541e00302d280c003d5026001c545240d91074031002404540120f502c1c461550066400704020310343c0c0d0030681c0b41c02051480c200450305254020500290004032824001c500c504048001c8802c00c807445042112001c2c0055180d04145141410300048414039900640c00e12021803254540401c00f40d0058110f440054540181c031750b94207411840007005541070021210000501b51524081e400c00c0101c1903000c4c0030210554820041d0710384001e90741d002003107030510905002a1a0303c044130711140349004040e4103690588002f4000c0c041c0c850 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 681855782 1250 681854532 681854557
    0x32070f0807030906020c070f050a0e010b0705030403022110020412121107030b06030d090b25080f031008031329160507090b010c060504050a051c09050406121205 71
    0x514190b4980081070640c20f650309023130080407155884040116022050042c42040c281c410010000b021410000b4906030b4829810341e820b00380c1c1c075000940720b103100214400d41110010250481d14400784443c1e10680703141141181850f04120480d00c0401d06484010034503e030b0001c0c1006030b00e0061981050743ca07030000444513400e881e071401e0502c038003081c1c81d5280030b44907009844442ca4000c042d00c0c0c0607100c024035100d050401c07807404020740c03804417191b03002c0048803a0a00f102050088004103c1d00f204c45000790350383d04000701d419070702e400340c6e90016a8036003017841f511a00851031000310080743c01025890b101c8140b0b0f020b03128007903813002d01d01d041c0310707007000070426440b16420304480000c5000d4000d0b00d615540d00c0a000d810380d005909068000f51360502002c00113255548400d4015001c1c40407500d06900540d2901e141045c0e007610b080107003800300000e0b10030f15446080800540b40683c3c0030302076689002d42460a40e0000e92000b0306200344100803580082c421b80541da00790103c40b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 681857032 1250 681855782 681855787
    0xa0e160f0e0105091f110c0d0f030c0f1a04050f0601150c0606170a0b0a05010b04050d0305090306040309090c05040e040303020c19080301051017010e07110132070f080703090602 78
    0x30740e0003a20303c0c03086e042d41000b580a94500c3e481180b402c0f03150351503016000800b802c0d0010b9903940407911030b00d903080d04440c4000701c40c85000225009120000144a110000042c0c80c1050301b0614503080104030f4011460b0300100040c00340ca2031002011003040c107203086c4516107404c246440c6024003540e400c4428402c00e210300c5188412000124040280d0049541402544038456480c040e40d800340118211707000100020001414608041035803180685415810020f07400e00003403c1250030f0f40d0960000e031809130705100c140c881d40f10310040d16444d41001e43c0b60a00d00f10041c080c0b84001070000d018564049903601591740e042c08040c10205103e0b44011000d0601d1410310000c0d0400e002c6c00f4018040c2c4a2210301d0203009820050341d4424004a60610340c1c42c000181d690380c00010564001c0000a14210090b0b800034050018210780a081d11100c01d0ba03d0300365400250400c0621000000303d02c010720816580140c60a03401d0b40091415404c503580e07a417426006440c41e0280140000d100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 681858282 1250 681857032 681857089
    0x215040501030e0303010819020103020409020d09060b120a110f0909071d01031e05160306020405040f0c0503070305070e060307030b0102060705090a0b090a050a0e160f0e010509 78
    0x404020015108241c904100c400804044182e40e4042406085180e6000d90700400308020b01c2c00c415000d0510516001d0714140d141e14103103040c1c1c0c201421040c0e0240d1a5480c070340070000c03a0300a2a80c6448182c41e00f56107154400e498964032803181001a0407000001c40b4a0341680b84d00c40460aa0400501203086a003482c0e02200d64404051041000c40c4042094a60f010306404002d2812650440304120360000c080741e010001c0e013100603088915115010301191000c070803881d03900042d8055100140c41d9850b10051106481c591030078250f4513481c01000003000c5d9000300940f80c0009003891b0020350341d078620009459103022080f00650228002c030070000c609074150085c49002c2020b909881a40e260060250ba00b03026030034141764001c403000402cdc0039405928000d80403008000301864a403d6844012801c0c000061300309010312039404041003580c060100105101480601c0c0c00c05603502c42c40b1004040110004035181003220004803c1116502e50000300b0b042c00c0f240350280c884241 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 681859532 1250 681858282 681858319
    0x10e211605030f1306020d090303080a0f0c12140403051b0f0a0602040645030f0308040512030121030c02120601080d030510050907090b04060c030305160c06021602 72
    0xc450380d03032000d45261a0010940c10320101e02a0100400c7d0b846400320035046030b41c00d94801d40300805142c0c0d4540d903207041c00364070082c070b000c0c0e40c81b41c0c1c00e65220240c180500b40000815201d0038495000c80b0b68140083c080003aa20008071460801407100c561001038649001c0d605013004001c00c1180c511680258100303100d500c0e40104211229a1150000c000c2081c1000780c07000840c5c4502141032520301c4080300030100780030400e01c040302c000c4a0750859a03281d0b07840041c1c10030307950015000101034004000070890100402900450070303801c1541158034101903a030407906950f602e44407403050080302c0010103000c0c48081100e5035004005244078039205003801d41c2c070340c02440364020b24424100c40b04011800781c860302e4002c1e206801c038003040368203000c00c0c0500810301030190303070070802507040020b00d40401030098009050690b94900c044038903424000c054410140c1403451407841d801104020f507070000325402c00355a0007040961188000c100240b000c504040001c4d400c861142d1444160a5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 681860782 1250 681859532 681859537
    0xd051218031620030a02030c040506030111030a061a071e02010527040605270403020a05030c0c01030c0504080606090403051e12072c0301060b0a0f02010e211605030f 73
    0x243d2490b01d6803240c50382c0301d04041c0e071140300e0800a0340581140c1c5e4004c0050925030084d9034402c0e0042c00200f141da4814030703801060342c022520100c2c1703595600313428441090324010300450f250100e400750381881c41e0340c0c80d110080c1c0003100e00c02c1d88a05038503c20104690242040d10388960030342c082d00c0d02000e41c0300000c4032210700d4003441e107221b40c1c40c0020105c1e85107441c10781d0041c0503850490035805075008084540004c440904181c0951140e0b0300781c0800034104100908001e80048049c00c4000201e00014040d10301c1290007405001d818072040c0b02d40000003480d80d03404001101c4819840d100c03400c0a8500744202500c07803d0340c40d042c4035192030b030b2404800103200c101281c00c2101c06076941e200d02110b148900244445030b104407020100030568250b001204640e20041c00041d401d9039030fa100ea06c0341d40c0403d00a5000c6110090b05d00d110135020310603030701d071000c805021f4030b1010000c2080c49004803100da805081c0170008140f10303003481403640201c12500d030f001081f079640381408070000c3c1264 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 681862032 1250 681860782 681860813
    0x406060509030f071805040c030215040e0105100f030f113c0a081e151309050606010f0306030605010816090b060a080405010e1e0d0512180316 63
    0x3803080303e10f0f401003c00c0c00255002161038900c604205144003210407009407101500c1a01c400038141c001002590728100d12000d071181c4a40b08036070341c0d031510060603032042d07050307001c20b02ca80d6012607807041041e0855491400051103180010700000b841001c48c0050525400c00b480b103c40119060340040f0003000c1c2c10380d41021002c440411515105412582c008840c0c83e00112920140303e42300314140220034182d0004500b116203004080625103611500000f02e03009100b1100c0c00d254404282000c000001d800c124555003403011135800d480e00ca0b40c0311030141c0081d0400014081040384144240c1c8090b0203150310600512040d65242c2c0800d9445442c0548241d00b5000f103400012070381d009204094440401608031410601440403d03928145c0080050341c3d155265881c411800030180100590b1071001c841c890f00300100701d441d8a02d425580c2284030280502004004135610400d0001e9a0000c407400381d41d0700d20842225054214002c035402030040e803c1503000d100030002c00302c0c44c25014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 681863282 1250 681862032 681862039
    0x1020301033f0809100b03030702040e070b0c0303010e070f091403510105060a0c0b0a050f13030e0906210d0e04050103021c0227091501060206160e0406060509 70
    0x841171490070700e400b100c6280c2202545580100301c0c000c01810141c10015050300c403503094803203407542c1e04120350aa0780400380c02d900340c0d00000014050446100d1f00560007406610f094034901c419040054000b9502c1d02035803001ea251107110b01c0c1e5940c4c04100f0040512980c20211401842400310071180000d060321a440e180000c0c0012080c8405030110310221595103401040c81d41d18040c144101075003c01c4000d41040070b100c41003404100d07501a614015040c82d2030014081ca002407008000240142c03000f4190b160a1a402e008241c0c020422400350000702c8000c64035444800000f20000b414803504200c81d003500c4512801c0f02c40c04200000714003429100c1c1003c03442000c0400c800c9803804d000080d4000858168404050113410080c40450f101a00c564070a00b00d4a00781c8801d041646550b801c2c96015104116490750240b00484441400603101c561950600358041d48410008091390458a07032031850244043c4504124604200007a00030414141c481100070816842420100d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 681864532 1250 681863282 681863293
    0x4080d03140c0a0207031509020d0305181f120e070e1b0310122604050a051017220f120206090d050c0321011701020301033f0809 57
    0x510107114821100a00f600d5030140491a0559462804820700700c680462400e944448000040c1c5800d144021614003944985444082c0940c0c1c02001441d51103080740954405281040540c1000c0a40c00101d11103046c04080020604061401092900c443d080c091080c14000282c00425075152401902012074454003c022400801150310081d21800710074400d90034100b0496000000c1e10010912415040c880d6000c03004c501d002603c0c4000175444141d41c0000d0400080c98012801030061a00b514800c030100050b107005441c1441e201e0744000e19503c0100010b410001189112810028100e0480c60a10480c2026200002031103400c4a441404070394400c030841c00024071910807402d400042403400340c2c6910407901600003180c11213252005010456107541b60b0b80c1c001282d00c5d503100d2000c1c9690f24014654401c1038001d0346091031648100014070100b001c5664910b4003a00c0404174140258010f6199000821620001000b2030031000803c0000340d4000181800f901c40c0800300c80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 681865782 1250 681864532 681864541
    0x207080109021323010e060a14030d051608030103050a021305060f010f18082b08060409021f030b1306050a12061b0507120306061b0804080d0314 64
    0x10300700c944508000e0f503c40e665040c4007440824682201600f110071101c0c120320f80001150100c0844400c4c1c10001e0901409410001c2500344001c1c1c0c0340007840a00038540b51810b2080100c5d4aa82075040304108200000070740e501c88024032031401c0d88080d032112003141d032580d490a101762154080c00003203200710f00f002500f8150300514041c0c103004080040c2000c02d40da600400549658000b00c00107418040301403000c501c89071034140d41c1d4008040b44030280004a201a42e405a2040c0e450f010800300b4180d032504494a0b0b500c099450351098060f9400148458039000140c7c0f0780d4100b030035120b07a03803007001c1c410003809505401010340207109490308407803032014489c82c0003030301c2c0070b0301038607412007003130300d010404074046c100c201d49098000d160008280407030840080702d0b410680310000c0401d00010b056410400102001002d26505140c100440e03400c00e10014074115000078021000d0f200e0820b0b41040c460510200e0740103011007421198440c05400010f00604030031350030103400d844d1010009 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 681867032 1250 681865782 681865799
    0x7051f0f0e10030506190602060412020d120b1507120e04050717060a1508090d03051b07050f03040906050901091a09070e1c05011a01021902060f0d0209010207 70
    0x15001c400060010b07005482d000070450044c0750003415241e018140e81c0700c136a000d00c00441c20f540074101d9540a00794134901400c0c0f082d80d81c52826a0a000c5610041040d55001d0f031004030002e0034420b42e90042540d00c803003c0001d40d05904c5d00c2d64451512400944141004135110500105505685402a95032142000c00c01100c01c1251240302117140030b080701240902105003207070b0010000f0180d03100aa00c1ea0000210700303030083da071040841d90082c1070004c80300c010000740060210900d0103001c0c518250b4103541d0b0761459601c800e85100350103c4d414040103001d0000c124078030400e00480351525a24401c2102031320035841424015220040041103643c01402408480301c542d01d0035000c2c04190f481070240c10f110040400080124040f0350708600c1d520000c03484000c4c015400c500c01100040e04015085603411007120360071110310380c0d03907013002e90700841c0710b034240807582c05501d14445450000c2043c9104417107070000b4041001407103110180d00c5a001d0501ca80003a400c854941e502d40841 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 681868282 1250 681867032 681867047
    0x115030e0c01080106030903180e0603100912080c0c0d030204060e090402030c01050705030f120a0c0c0f150e010216260f09040b060d050403030b0303131707051f0f 72
    0x4550010342800014080c003406038111f0b0000314032910304070016441150308107e1880d1603801140003a0030324000e2040518080207000703221110004208003507559555594001e00c0012004402c0c8980c20000803900203070384055035040d9080c0001c0d00c1d40c00421000060080d449402150041110703104207041c20f0801d88081c1d407199501034014000009404015119904a441c04940e10300c0200070001980c42c2c0d800c00340032440700690010210f802c1224401782510442c114100c07c0000c40c283c0c0c0c401140d4501000000203070030100485140c0143c0c0c00c04405840305201800440d0700015042d0f00090101e0400f260840c001c440c0040c90000c8094440c0440d080501901074090081c0304820f401960180203203c0181c0080c0001500540396021440ca900f11200c52142c2c103036500d0410043c190035016414101ca0300b10042c40c907003680c0c1d1002189241e014010030700e850080c05d8039994000c0c000c220300d0000c2c110080003081900f5002002d0502d004011841700005914061540089805840c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 681869532 1250 681868282 681868303
    0x120703050d02180303070f03030f020c060a0c0e0411030a110903061b070f0b152b050a0506011707060504030809090603011e1a1206010608090f01050115030e 69
    0x4403103162001406090010b5040000d80b0314034404100c15400141c0c0d020001048524481d055050790140507080c050111a0543c143d02e00d00c2e40104114801601c012031002d601c441e4180d400a840607400000b1251041043c0300c05401c01d240050018040b010103014611800e02104203000035113050032088420f0040c0208503815621110201c4d044800a58040251003016004113043c1314980e102d991180c000c4000035601601c01509215410b085409a1030f2070b14070540717030000c843c403410340d100d8400d0080c0b0280007401109801d41000304001448190303142034100c2c044407540d503100c2c01421000c13000000210b2951042807c00110140107600b9a003c698120660340c2c14050000c082c040c0c0c040009200ca40d0556968406168000034145500606020349800142490919a01045c1c01c1e5410722030714825071103546400c503101c400007000d505481f0180f80c5404c094807444044c41ca04010314441e03003d03d50811001003412082400078200caa13680365014003840a600180f10f4541030005c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 681870782 1250 681869532 681869537
    0xf060f03210906052110090c0f0203040501030e0a060e1501090b010806062203050f070e27030d020a0c0b160c03051309060803041a0313030c061b030509120703 70
    0x350304115541c00388002d401060000352401780c00031a2a03040903c9103408076128000340208110601c54001d0522404004401c14109000040f24901000c0d50324081da11415041640351101640ca605060014405c81c40d8071271000c2c0242c82c030100d80d440e102c0100b85901c401680801000061003942e0b8007501200080684404010f40c07038901c00e02000b5804aa2841d556200c070400842003518192a040029401003015041118a24000d076003001040d074000266a00c0110510504106045c02440c01c9010b26141107514030b48000c0340c03400c5001c1c04580500c580c5c03001c210003070303190307001140068480d10030a40b08807243c1d02e080342a4081220b001400c0001405580030341c000a003d4030080801d680303548040c05101c2d81d603100b000191003a43d080b52038241c1003c10300f0807540c02c1c00f072100e0880000022000f41140f4244c68003090380000c10f8005410004d1707144c0c01300148861a031110a0b004408405c01015107842c1b0000b41c00b07044143c440d07071414810f801c102200f507412582034482080c1e041c1d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 681872032 1250 681870782 681870797
    0x306040b062127100501080c031002070215030f060a06031404030c061808040f05010e06190314131101020c030c1512100603150f0e0a0f060f0321 64
    0x440c601d56082c402065000300c030030381001c0020840b01034002da400515940004004d001c400403181030540343c060b404100182d100300d05810040c0c1d400709241c2e1003240051401600d61613030303000040e103030040c00a40441c000400000e102511070340d061020f101c2c0308191248000aa03480c1011400c4941840128940c18460710125000170311913a03404001d540500004144014082403c8113141c0003e00200c441c0040010204006004501090007c09090800052080024002c00c40a2013040500b550018189107070110b214000c0d8031a004031881a0034a280a01c0e00b00f5003416240e803c0981943c0000007503207500070a41c4005070300e0300e0303d0380042c0103002000d01030800c0c042c007000c1c120220640724000b40680e5600004280303007944940d034481103540b40c2c545840005030445260b010b1049011452a07014130081c2c000100030002c541255400016980ea400f01c680000c00311201d100030b4860a06400003411000071a003070302640d00896440c40e40070a0303d402c00302042b000004410208402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 681873282 1250 681872032 681872077
    0x706090f03020607300206180c1003140a020a02100b0a150203040b0a02060f0108030909220f06020a031a1e010c08130f0530030705120306040b06 64
    0x4a0080c0804e03610903a40003da400f120724401d421000442c07414441c8000c00511116119410800160400c40000350b01d1004810200c8540d203c0d243d121085020f9080444240c41c45403107a4001500c1040c8210084898188005410040d52082d01380c0300040c0300f10805019006c01742e01c1307800d082c080018503418103030f40740c482040c1c02c940d010240c0f1011341c00184800281d11100d031000307000100075680680380328038101c03092588444060304441e110364028011844d003519100a0380b5040340700c0c1c08828100104880c0049481d0750301d403100a0811503035038418001c009194001c0c043d0b10002d0b44090003d20516100e0301c1200720a42081640300c50f1040030382030301041e010714a400d403400602d40010000e00ae0b843d0400554403440c19506c0d04001c5000030088107661482040c090704044518420803d4500d5400d000c11030140c014240f101900c0c1d6103c02c141c80200200c3e90762951101c2580c803010400381d0441c4440d0001c0313a00c24000c2e414100e00f05080d182480c12100342c4062110f500400c50f00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 681874532 1250 681873282 681873289
    0xa200a030611040f030b1f060e0d0f0f03090611010b030709111e09040c030b1011071a0c0c030106050907180e040605041101051e0f1e04080706090f0302 67
    0x15082d041c8242c0808110104088141c0074902020318042c95050705203003407100400300081d59040e00d0080000d08000305208882d4030483e103240d0b0140481e2680001c0c0541d061102c140e40d080d000043c902c11b040c40b031540425800c01d820000f02c4040f611042390001400b075495090340c10b1540c4180d4107400410051110710309a034404144a00300800c16803c0018450155882030082e030507400c854000460103004506d840d00a1402180f901c0c074040c40120f005c0700108242c0140e1200f50424800c0060600000c01e00c104955001050802c690001d900c1801e82e10b00300e41d620503004c5503042d000c0c402010b0040c0c10140a05811108003620640c002c1c0c2d98140c048a00d4052011944101038410a00040f01e40d081540a4000c0d030041c1000a11401d01e0328180403110050a40c0034140841400006a041154508800b861914401032a82e500782c00b12888a00d00c6401d504070715441c555010b00c140c0c481c0030710141056805500450301030a80702d24090741c104140f03101d410740c2840f40c52010f000504 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 681875782 1250 681874532 681874541
    0x30a0b1b0703021608011503111311040911040602072607030c0e1f05120c030a0605041a0907170309090901021e030108060601050c0a060e0a200a0306 66
    0x11150352154a0340840600034003000d6000c07003016001a48100c41c0305001c1450b0749115001031802070002c20031100d00b081c8103800301c0c00b184809006a0302c0241107804941340d000c0d2004d00003420300005c008210a02070b010341d4039001401920541c0d4030304405070703003009104011241510758a4004101c41403410b00700313001c1e182542c2a0f600b1016103800b40305180000c10411000554480c030207014880d400c040c902408402c00038003031400c0d03c10b01210403420030b841074440c0e425500300703072405d01d00a15072241240c03a1800300d0341c04603054400d4224920910000b41d01c804d024030320444e0400c4500c0380000c0d1720200f0090035111464181c000c036004101c06001c038201c800700c042c1c41d182500d003000d0a0034002100380008031340084590b5000039a4040c2a071148951010b00801005414295410084110b96030300000309800c0c14840e0018055000715420031900c01c40550005081c0541403090140b00c0d1100c0d10f14000715403181d505084102042503210300c0240c1400082c016816181c51501c4020240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 681877032 1250 681875782 681875791
    0x15070309080607020d080c13170106180e0f0307082d070309050a06020d17180d0f080a05011202010c0c170604020a08070f0303122c100b030a0b 63
    0xc1585000000c6030041071104912802035600641034a040740d841c05050383c480208144480b02082200c8941489544822020f541041d1310080b41054068500d45c01000342d604111a0385c0d02500e6040d40001d40ca0700f20446941c8036000356106440e500d10403555074011100014800a001d1000352280b06d2407086410780b0165500d600140c3c4500400754420030382c41700704c060300060421003040c00682080c0150000400c15480100701208216030f0003041024041c5241c0081d0308203070040307401810303001500b60709103003070100341c0326403081d1220003410b2000702c05003190108a40f500050300303402052041604803560700111024503503a90f401164090300308082102c903514100c00c0441c00300060b10044143c0c0c45148010509401d250042044150170f03a40b010310f042d0f00050060180e00d2106400b40d04590303160070044e4400034022180e201038000201400031200400802074100c503024004070748440e01c2c1009031295080c00c01003c0741928918100950180d08c01d41d00c0c0300016072483c090350b501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 681878282 1250 681877032 681877037
    0x209010e18090c0307050a1403010e0115030605011e0b16050f0703031106070f050706020409020315040b04090b073510090b0a0506070203010917042102150703 70
    0x280e140c00d1000902034801c8021200711214001c0402c602040300300039480c3e102c03104070014506031340750a000907000501f600444031528410139100940c1d45094000c4030110081e0f000178050010001c0c0d141a6000c61440140c64003424403000094410007000c06440498001070602d8581e4103040041c3c031194020309030032070304880d1000100c0c0482d00c1801013000300c5520402500c0d2040c03450800404c1d11a031070600310803581061042c042e0141e0070040207907588c402030524503110380f81c80c00c180340203024561100000c3c60000082080a4820711050b17040f11404640401459400c4d40a000489080d07500040113101c032000411100b6000301d000d0351403070309101c5003c40035841144001c0d40c200418034440301c800055005201c03100707080000740006000d0880003002081c2d0007000003440c1e103000e4072405020b5034002404d00f0030b6440070f400084055810a01000980c640074188901ca64040d21403040703003403400b0b031801c00b1502001529202c160f4004005203860604030a01000940c01004210b05 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 681879532 1250 681878282 681878297
    0x20309010c1514011406090a0e071b050c1005210c0417030703020c120601031502040b030f06010f0509011202031e040303020702010e0913060507030f090c03140d080406020901 77
    0x260400b600807100c2c60410305400c0c0559525201440c0b8400e5010380c20184901b10900c08502581c480d4190381c0704981114842c0107803500c4610302610347d55009060000500303040307031a00c0c0521400003100ea00c1100c040d5050081503084ea60202c64078021414034005117840d00d01c41c2d116009018080310742007030496a00c1840d0517502c41141e40d2519504a066119800104118051540520a402282e642502c1b481c0305075411803429501d17a041400001d260f00d10395003001428503200e034192405172800586e25a528205442c0404a01104070f0f20240081d013141000880c640c40b83e015244c0254060f11100c2c507005821031184040d410090401c181c1a0055400c0302d859610059440d01490181d100180d80d1a4180001041c1d085640b804a01072240301c803d00000c01d801409001d440d68010000003419150054200c014000110400d2811401c0010401c1440385460038001102d01c2410b00c145000e55002e0803588505055000201123a40d000c00a40460165001030024940500d031461 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 681880782 1250 681879532 681879563
    0x1b0b07080a0b131a010302190809030d0c020c0a0603020f04050108041502040b1c020301050a21023028030504090c120f050c09010e0f090a050f0115020309010c 70
    0x900030600121040005130310340b5150710340070b28034541c0c4140d01c020030310f42540b45c006030703004104401220102500c01c00180000144078044c051060751945515032109000301c3c00410740003035440d1003801c1d60a10401c458030000646501174401c45001740e00034018541824a00320040d0380403940100305a592400110300d4040404a600c0180050310440b2801034940c503d84036515800700e107912384401183d00c100300600296582343c0c4601c0494040b000240c08008580d00b5151340b2060000c030003504882100800c0291f030f0700a5038a0b5100f1402c030a0144921000700c1d448658030b4070040c0003944401803041c6548002e28604440b044c55038041d041c0149070650b03c0c540242158083c1c00b4040018071100f200050120340c6000e60035002c801e9a1080c0300c54103140d80028010300c5031521150500c42c0140c21030a41d074032018803400140c14001d143c085030b03192080c0e420024100c1203410b07a02c02d0000701c00100b5800407051060030403841e136a00031420486c1003001900d8101c1400e5068031100c0f001e01e002e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 681882032 1250 681880782 681880789
    0x5030303040605070f021f051510080a0f05100b13180209041803020c041503050f0102030702011b02030301032d060f0507030204060e04021308060c0a1b0b07080a0b 72
    0x11402540b00b4103002400f031805210051101c00105024000c5400c101ca540301d0b5450000c20160070141b02c0c0034005020b1302d81e59802e4a0150702100352980003000790804040c0940c1000c5980d20803551500113109000c007502400c4201c6e40104d0f0b58600c5190101c405020000060740034106045140e200744414030384400700000c0319100c4c0604180e00135000600000c0a08050003146500003541005602c03055090381e001c1d48800404501c140281e60700d03110070520032700d000a0307000119084025112140b0140219038040d42c4100c850034055800e051018102c0c2c0d2181c0c40c2c4855a000b82e40c05542140d0071076490700c0154105055001d22508204401203183c082c0501e5801c0040c4a40c2d40050075020119406054440003040101410b2045c08104401038100c50000303211102250700590b00c03a02900380107c01e0000e43c2000d14548281d60402c00c0c6205d040b0000d1100410075101c2421801003242009036400072440001d10895402020803000780c000d110003608080b4001c0003080012480010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 681883282 1250 681882032 681882037
    0x509030307050a03180e150105040911032202010f0f030609110d1a1020061338040203010e0d0f0801080f03070212031c050f070206040c051504050303 66
    0x42d00c0540245015100b050f400240405031504160700c80c2040901c2c0c5044580043c0b4000c05a82580c0a441015070041c0c3c490012100900310f03000040103c40100d001e030744c040d40c00c229516051081c070400b11070701d0029084405448141e05a40306001d0081c80001120410700040502003416103d100c0800c84600c903004101000d0307500392006480350080c030050701c20344075656000588901c0883d02d903030b055125461401440c640030300b40041d112120f00b11703803050303d81410010f0000f40a82d10601c51801c0c10482d076064114040d010342c11031100d8410005020404203054081c451130000101032512312500c40c80e80d4004d000800004500e010b401303c0504100e840b00d6000c000842d03042240c0403854120b000a409420000d004010010007018440d50301d200e10000039215003060050000c0704101001102d0064981030031503151148090500e50103800b003034521483e100e100e100003d0a4520004805104a410603001c840303d81c40d04007440000c0e05c1200c1040d040c00c004010104031920200300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 681884532 1250 681883282 681883297
    0x803220804121a091b010c05030d0219030606020d0305220501020a03060608040b01030f050718020a03060e0615030c07060207080406110a080a0f03020c0a0309050a120f08090105090303 81
    0x2d0504102c4042d00d01a018032280e1000c400d8a4180e420900001140008005e540c101c3d24520469040d190440140d0310005002d42c001e259120015034150243d8907034001d00f03038030411407541c183c000c0c1c034525082d0281c4006008039001603018902c4401301c2ca2082d00415003054042c2c1c00d41c0c92100c014201d010b020040c541040d19913a400140b01c0d01002d902d841030340c00401141c03902e6100c5040c0f540e0ba841041d40180f202800451a422152060260901c0240000e0050103605124107440c0c00101d0007075080b0380c210401180c03900d14000380500c0344000c0386100b46401050074401550505d02540a5003004d0164244400207001c200000348062005111950140c83d005440d986803240090655184c40e034480c40f00c5e00b00040c100e0010304482e0680d80e03800780a04043c40b1000d402c550844c000d000d078015109480c41000b180303009240d001b003040d07401d80e6401e9031301070700d0f594544e0024200040200c500800000850440d480428012000341035010b074140340003490444a0710000740356801080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 681885782 1250 681884532 681884549
    0x30c180f0612060901050f010c0821090d031a031f0b04020d0e010e010207020d030309020409021809010b100e01031a0a180e010b060405010c020d080409140604090803220804 76
    0x2c14400300380ba045052900500045403004034140000300001c00d0054000340c0100192000300d400012880c510150040003083c40d050341800307140030320840d171b980c0041c9507005022a01e021107010b00ba044803110005401030140007042c40301400c281c03c0c0c40c1003000111980300a0741d1081c5121180d9514001041010241d840109499803070341b8059085079003541e110641c981c41086600010b889070601c02142507010b08000841000768004036015200d9003c0c020b610101d43d00c07800700c454012010303080c01601280002c0224911403802e02000240410b18800410800000e0f4602588039401c40e07501242441520301000c0400c0001c0361822152341c2041e0380f400012a841240c0000911a140c10490801d000f40202c030021000309216214901a1504003c405502d81041d511489035100031603030302650103942c460b80d07151144014418039030321800c1ca00000c4085000c40c82c003070140300881504695550700e107807030b03822040c0024042e44550802d58040c80002401040d2250041c00041c085c15 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 681887032 1250 681885782 681885817
    0x3190c0c0806011e0f0302010212030405030c1914060606030a0c02010f05070c03081e01030f080c0d0f0e090606040b030603070f140901050103051603020f07020319030e0303030c180f06 81
    0x141c4c0d2114140b000c1d080315240141001040015030b03800500905454003520100d692510380e82882c2e81503124481c07404007188503c40da12245580c0507444508901d0040708800103541d070b0148100d407030300c0040c2c46003030b440441070003c501284100d80c07110b54003c8090000280c4260030304c1220095076070456120001c90f118400303900c249504000000c0d03000c29a1801113500c4820b4041000c0e0181060101405428500810504010b5040120b42102004801b100c6240310078140003455244142007050026410581ca0b5085007004c20055000b0310000300510304060500b034401c901d9410091469501d881560000258064202c00e8417000d458000001d1241d0300c25481803100203a03040c0d00441c100340c030b0f2104024200681550384160f0165500d400341c6c0e5804140790400d240e009a100181d41405050101c0503801c680d041c0c2d00d118030344203454500050380010100340d10f07408100d03400710f0318210030001d00020007c0428176210009000381a050407c04540c0841c290382c2056407101c201c503110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 681888282 1250 681887032 681887069
    0x20c0714030a02120c2707030f110d24120b09161818020f010f030209040608030c070605280215010611070b090a03060f0204030605131403190c0c080601 67
    0x1008006080a040700c0d06d80e000b00500410740e1000c80003482c010800d651344080312010401a080510082d01e1501e44640f41e59441130020300500004520740303e80701d122003207a104898601491821516004854030212005840e0650132480007810028a40154503030312241020200c0780d04060281c01c2c4451540b4000410b130130040380c816000141c201c0c644a180c000041c0d03501e41700310400e030f0030a01e00b500c4c19408405040d8068028071051643c8603081060100d050580000501640000c0302d04950704c0c1aa5100700fa6464816491003c2265424050f40440c17164800d2280352808201d1040310304009001c82c0c03054401e0003e07040302000800d03103640e40000313040800584e00a44129424030303142c00346000c006440a107403440000c10090315118441c01e00d85580d410b5400940d0000024003840c078003401500c50628228030210f4a07005044440303032840a00005a03072080309074884035000c2500504040ea0a15000c420454011126000c0400d0741042404054000c2c04041e005031a5000f0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 681889532 1250 681888282 681888289
    0xe060106180602061003080703030e07060c0308010b1305120c041b0e011e0e03010e0a14120906090913050a12090e04170319290301020c0714030a02120c 67
    0x16a9002e0021544114244101090300043c80b1048a0b0302c95080780d600d41070b42c601900a041e400c14400018021170f900040c0e03254006001d602036500c01d03910a184c036078850f41454914012a0499519004000414003083c2498003c000e84003102d40b04a44180c401d0500184c103a948110440301e55450907810000f9080c2c10850803803010009080ca02c44030b00c0e5680079011031191a10205040200002c20030317106803001c0d407240d05410240029505a0030181c282165241c2d2070b82110b072040d2082b0b400e1561894101c4e82500e00000c002451940391100d000204491241c0c080d1190362815002054a40040e00402071640c2052050301c11015034040b00101400d4420740b503000844950395401040000785d810352440002c00c2c0b003588181d0b1280c032807501e20481405040c1036054050314000303190100078620154400c01c05041c0358019100840117040c94280d00502ca240752481c1d20400c404d003ca010007984a0403548006011101480c0160b00094000d9181e07007085280c5030090301c5030b042c5508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 681890782 1250 681889532 681889577
    0x30c05120d140603150a060815010618061b0c24030f09020d0f0302030408030a03060905060a050306060904110d060b0405090102130b09061b0c0a24120e060106 70
    0x1440c500399610340e407800c000842c1e203174044489089501c110450020b080501c06a1100d00640720043c2100e04c0503188500000f0202400c0c01a4804038454840344450a85410644030582d8042e5070760052284510311110342c0c1c100e4822048924840c0b17088081400b0003200421407000880c06408480c1c000d4461002e01240c0d02c2d009600d1029007001150303c056211100600030950b480b41c01c0349080e01c0a81000c82c1580165001002d95003c00140034180c56455005882a00d8010344100000d403910010011918180d2041903010b401c050700244c10b500c0d01d2006c1c01da00c5809120301c0300600315000c0c0001c20a140001c0111806a920040703a0003d007401d01c41c2d05c0c0e200003210f008514001504108180c10601881000041c00c00061400d580303468503416585000100120b1402915281c03c646032580c03003210070700d402005046030001d0a036000003801d0010540c01c41c0540390001c5425400c0301c0070502550069030480e00d41061645070441002824000c15242d170303800e60030900c04280c59075031a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 681892032 1250 681890782 681890801
    0x4030215161701050a1403010b1804031b03080c1303120306030506061509150702060d0b0315040c090c1b0302010b120102070209010605090d02150307030e06010e01030807030c05120d 80
    0x940c0b075100144040e44a01c0c0c00c00e02a528183c141340480305564000030b000d45004245990070018440101122a003160f80c1c0500541c03003902c1350003880001d41d00b1040c1c80b444445019001034003000120307c0000b034400090110b43e0200540302600ca0302c9031900d80980f6070005141c00043c1c0e80e480c041003800010b02445e504200116400e91402d4510400f4401900801600034816881d44c7c0361204907115100803591071541c00f90445031a01c6040c1d4288006180c1c17110040e010340204200b4503800f402009034544a17035423212180d02014244000c10303000302078410441052208030440060f01d0b403103041096030b8062095001080e003a15910602c07500c0001074100d0001ea0f80103002080040e5194a542c506540d05460b209840c3e07103100002822400380c5050103900200360409031050300751020002c40c402e0321140c40034019605c644d001640e45600900c101c204172003141005000158222008101c024040d19280380030b968240c4030075040c402d100013000c086000000341d5040301003160240e040c16 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 681893282 1250 681892032 681892067
    0x150c0203030c0f340b070203270112050a0b040605060a090902030c090907080702060c0403050c0f12060702030c0705060f0a0c02030f0102040306140a0c0c0b0403021516 74
    0x840c105001d5a00039402201c0043d4070307100c004503c180040c000408005075960a860240c440f0f2903030b05940701113103001c0c07403030179150113042100003050135000200f160b8554144012413001c00d6850781d0351000c56049501c4060400455480b030388541036142c01400e009000c00440014000013401c108411a901a40818043c101c01d00c240c260841e04100680b0444038001e4000d40d983e941c00070480c0301417043c604e04a51110300b0000784a2180ea22400c81031165100d502104e00c1612400c071404528061131000401c59403240310060481c0c01c040140341c85904002c0c11080300712804c6840d0343d0803c5000c86920005900200b013580c80343c00708001030030082c1002d844035840e104008081e0515403043c001d5032014032a10159860464a0812401c000c1c0c40401000315205c54a83c90003101900960a0303c1d000a070486001c20683c40451080102c00c804613111140b0301c007042c2d80d6a8183c6840108246d05602070311611465020040c0100d9106081c0700792000840c02c200c900107048848140084640d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 681894532 1250 681893282 681893287
    0xb04020a260709090b190314070b031b0711120f070f0311010302032a04030b090102040f1208040515030108010e0c0105030105041d030703030e0d0503040503090d031b150c0203 77
    0x200c59400040502c00d0300c0300f03130700003003511007019020425a080032580b400c01914120400030901030004c182d008012000d00640707808903581c5951600318001564014045841502051600f841e07038401450005c0c03145007155054a5610001101d00503941c0002103a40c02ca04184a51382c8810302c4240041c081d200c6100c0704040c00d54681d50720f070240107422107062540c0000416120f59070b064100441c480c07507002e922401c0303440014491054100b03110885001e81c1c402c1c00f141200c0018001d13a801c2d640a1001d0709042407400a407108805503032601034409910400011a55445030b0740403110090890340020360f04c2d4506180c0600311004821022a0b0341c02c81d00343c0d03a5007683c1c8030040720b0440d01c00f182c0206030106080b80c0b40c000c41c07510201c1d254140c800000c001c0c08058040d044100700c400114241d03055540521002d036494442100c00078559081045000a0762524850412405011785000d445418013010701c1400c441c5841800d60362069907540c0c145045020b40654408201c4500c090750 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 681895782 1250 681894532 681894541
    0x1b071b0e0f070314070c15060314012016020d060603030201020702100e011707021203013302060a1505090406141602060109020a1106010312030f0203130b07030b04020a26 75
    0x4004d40c03000d0f00c1003013003200120080d010b00506800440d026075151300100503142d542d1909420042c68075213900352035401e0400300c8200501c20282d080c950105c80500c0c9140c10740e00403101455206403034089902c03050208002011604900ca2030300a548039800060344c880e20f07030040040c10b08400c60820200461400d01158a0740c2c41946c02140811150701521140c9032400141e08002641a0079092948040b0001580c52480207070070403004200740d21801e40400381e5090407000e0f8803000c0c40801580c0960041032400318a54803c04580e02c0d400e100b107181c2c541b200e000590408043c1c07016112a5200d0804103900d1104400b01a01700140e41290340e01c4500400019445040512130103400c1c83c0d0104030009c1c3d050203100e411100a00c0401541c1e101d607140e00d820040c0e075400b2614200007901d0811500ba01c0e10692003140d001d107110b80b6900810404556a0210040004260340d04141d12000300854548850024000004440d03c44600c90300d40c407940d0240d1100c821745c4010556184030b0901 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 681897032 1250 681895782 681895811
    0x5010e04060b0901031a041a0a060f05040b09062511090610080a02160f05010e1204050d1a01141206070e2e030914061b071b0e0f0703 59
    0x40d5002c3e602804c000c5083d166602e804001000140b1401c0d800c90b0030110050f0b070301c01c1100540206800c1c201c4048100c2611450f00b101c0803403100a02402040c1c04100030703c500b9104038058100c4440090000d8500b104980c10030310b100c000008207407281d040c800da00794204010014503141a8400f9525150a4a0428000b0710401d1030011140180480341000c0360416105030100e0b900003203074030002c0045003010329241881140c020403d40f80395180c19051740f10000d010514181c0b61880c0703503206040500340810072100c2030b43d011048551510240c04810784900d2540190b000300070214a1000f0030004000b8050500403140c0200c2058100b01c00704400382e42c0180c0c0e442d0140200b83c404c00940504c8030011203c60850505100b901c010000c910a080d940c160081a5264407034040c240c2281840c4291655a10040c2c401c40c80704c1c042048130901c075190f090080c1c03a00c14002c5d04403030046149031540650178141500102c56202a12007000320040c03603072119a8102c1840d1030100420102011035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 681898282 1250 681897032 681897037
    0x9120a111903020c0f0a09020f0a12140114060c01240f15050c03042301090909050a02060d200702040507080f0118110a03090309080f0303040b0a0216080405010e04060b 74
    0x1003d1040c050701111301541d490303082c501b002401c0c48280455641c250390441c00c00c0307a004006044000b88075060707012035810007406810550030084110f26441c0e404d000f500310500b5060151560014410302000d0902c0380f090260911f46820f62240344060040310080d000b80702060b404c201e0295101e0b034002c111040f16071000070f00c1c880c10391034425100e00e84102c4040c1144240d41c41000b100e20751030f00c400710544c2c1c43d5181440107242601c030802d02d00e545d85204415100d95450281c040d81112403039501505141c00140068001e140000480c4210120021414030380801d030441c0e280f2300890742d44114105440303084e41012050806d0201413410003403481c02450140900303000104520030340d51130440d080e0003018684240d454070686401c0c41c2071004000307040721172081c0c0000c0c0d1740400c005010b01e00421801e107882c151754040c5245560310f8603a200308910280c0045200d40e801c02200303801124035060042603e200326a1655614030741000102000f158030700d41c500c501e243c148104240c00c0450304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 681899532 1250 681898282 681898303
    0x102060c0703140903010e0706030f1407050d05090309040c0c0204050f2202030109060f0e010c091a03130519050c09060a050904020d02040e1501090903080f09120a11190302 76
    0xd91684c3d150380001007400750580103000d440030300c1403140c007047d0240c154200f0810380140b010208009030b030640e40c03803481e56416201880456000c001404505034950019944841c0030301c2120301e0f1401100100701200e48a02501c0f001800d00c500340d41c00c51806010f0550042019000003005051044a0300c8560340c0710240080c8040000c4101c50464030f00f03412650029400c21420802c0ca5004400000035090300300c03c102c159440d1000c00000140205031200a031a42ca0541c140b060100a042032a6a13001415464280741c4c43e0101200142c0104200745100011405e05001000e4524003507103004010401c1c1403190703c0640802031a0b8590060141c11603d041780d0f0005580c45034004074540c212003041c084c2d041401d00c051144d03032503400540441030240c0e900e81048107a0761081c49000b02d03515000024009520304c00844c1d12a4403040c9883e030040110070a40e080701f2241d42005c0556849141048089851200b00009104003405101c40c0c1c00156031508031203500741e40d0000c0d100c149410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 681900782 1250 681899532 681899567
    0x20a080901021810170c030118060e0112060204080618071409070c230d141201051002030f120103020f032b14040e010f05012303040f060c0e0102060c0703 68
    0x840c0c0300b448521030b10000b1034000340302500105c5d80c03c0015020a503035000f405082ca1400200070341c00750716000e51040e00200c0c0c0c19882c00007d41d03420281174886298203200240d410b15000e0201290b000c0e01800414003c11404c0c0440314180c0e1282071050900d04d65520181d001c0d00030910b00c0845455460a50f513001907240f03048125001180742c10150f0010043c2420300300e00c052a95000c01540c002000241001c06072581020398441500c3c407120b44c402c1c1e40c0c41c0d0364030306040d5004110604080c51168440c0c245401a070b410000c0310404035003039403c503030301c4807001c400306100420550414484240c002c40c0c065000d04010040388460354500d5042200d0241101800f080e4425014818413082280c0c20300d100b41e013507031580d8802c0c00740543c090a002e000060095550005659070065001d2001c500110041c414201402aaa007281d40c00090013500c4524003407203030100003002c0e40f1400c40041526161f54065a5894000a10f0840c00900901108008021490200c4d803c045c200784c03442d8901 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 681902032 1250 681900782 681900799
    0xb07030c020d1e0b10090b06271e1e011d01090503030c06010906152309040501030b0a060e1e0907030503040f090507020c0a06050a0c0506010603020a0809010218 71
    0x2860301003140c0c002010000c0c0b402e035000d0f0203c03040200c08002280940c42d8030320b100d216281c0720540b003001c135002e1002403540604100009480003c2c0000341561052401c00000020b10003500881c8030580d590342d82e1856094000c14022061402c1050301016141188180030755414400001c4c00d07051150000d48401400e0a42c00035441e84103000d00350241401805494039100208111541c41ca0700380176481d00c4504203200404c55032880b200f194242c1d03036560342d4000c00d400d40c0085403804000104030b9040168040001408503103485c061280203611403040154a868000b08503411502c440d000424001180824001e120344020010010070075502012000c035207840102c02c0c46d002040d80018000e01020400181c01e0202118903800c49608801c144250b64aa0b10308a86890520401950005001c0410f0020910a001801c01c02c0014240480100c1180e1103c6152a909a2102c00003039000628130150950100050340c01c1029000290f0400b4107a08580141001c8400202d0052495 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 681903282 1250 681902032 681902059
    0x1e1e180906030a050d02010c0e030a020f010507080904151d19181e03020d230327060610050c0c0f0607080304050c120a03080a1505061804060b07030c02 67
    0x103000a0350040e6021048402c220300030380c170280c080d0240044400c0030030300036080d40199003008100c0c04080c40d0f0042c50b0807440c140890042d6000c2d044400d00740c90007a0107024000d442c0d00e4a00c5000c134003030380700c10041c284540b03440c00415000d001c4880302c03000107050300c0910411181e8519660728038a403424000c00c1540100c0b040c81940744004001501c0b12522409145515410340084c288480c000d500b550002d5441d0700054404801c1060740300d036092030001440350341c10416000307560003440030340d5048000000c05102100791080100d114401e030b0020010301c0614a44882c03080c207840b0345030030004d042269103400d040d182c45407161428021010868554010b90f1140f0032038a44a038800c80c0552a410141815543c600d07007105101d01544186074201000303080055405034080e450380d01c2000e1030740c90810303560140c580680040707480800204080340c13646d6a0000741c00d800c00c816601c0394445400000700310540d0030682c030866030701c3c0082228001007070f03000801c604100d8040d210260b50000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 681904532 1250 681903282 681903289
    0x50706090f02091807180e0304090f0e0307110405041707200d050c1e13061401050903031b07151d04090503030c0f090a030602030a0c08070f141e1e180906 68
    0x9000c7c51010035000c0010003007031150003a0b109001d1074568100404c00804240000340c0d07244a00a4054440c440d90180810103207484e81145900502c144c60700381000c40141c0035680d89411460040320f038101d0102c14045c41010b94002c3e1503000104441080c3d480080c0d40b01ca9446502d410b200d18010000394000400103080000380c0301002d58060550a02c03640790340c6450300284564080c20142d0801594020803541c40b900071b891068500401840c40c002e001000c02808440f01403006520740900c84001980c40e481040100750b8581944540e0400740704969240c02010400d80394500c22840c0442c9070700802c00000a481e840003503510215074940000d02d540d84140507883c95503a002444030000b00030888590055405801010414020b03a02480002d50b10b03550115403550004610b0007850303181d41e00c9403140c21200c03141c0e01d50580c6002c034a415213a0040c03616040e403624050300043d500040390131007842c80005680d03224a940c01c24070b00712072100b0401300d8030400510644a05010401c0350f80c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 681905782 1250 681904532 681904541
    0x6090b0711121b2407210203310e07030905011a030d08010e06040b010e030a05010b0a061e050703030b0a0e0a1503110907050706090f0209180718 64
    0x4000b0907050a41010b0900c0a60f900b900407400703038142000d06801089420201d034665101c0042d00c40c80900390022200320000e0750400502a21204c0840d01b0042d6041c4a07000072110002c80c5074041c680ea07000303040d0742c91420824610307101945984c0b041c005d081010114011000d413807103c030710740c5001c0e1581c80c0118050300740c000000e0240c0d440e2000d400c071284070f0500746203000c1101f40c0540e4001480c0c1c050944d0004400d100b01800b043c003020000d06a4680743d401100220300c14148408035900420100380307011445141296640c1d554590440d15241107510400100b0342447e22588000d450801c2c08a105081d40610090020200d50f5200b05406a00020803040000d8885201581d40d04484c1030740d0341c0182d0702d98000a1500f0443c0d03108807030901c4170f20107a0b60040d00000f002d640400521280c0000144600d04014081c0034240000343c2c0c60051014903800b0707543e05101c035105401041020100a00488411826031100c04911080400d5000884e0303402a81407882c0842c001d060700192 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 681907032 1250 681905782 681905813
    0x3010b0a053a0501050d030c02060322080703022802100e04020705070609051e060304020a030b1e07030603110f0a0b040b0309010e070602070e090703060f0b010e090106090b07 77
    0x8851110000320707001c403072900381401c1c221142c1030150fa641c90060007044601c0f001c0140014064424407005420040e008640180f04240406143d81040d8000341c502800d180c4102e44058000841d407050550401a042a4114000e00030441e46a07900001e8529102c5500090180441c41c3e4540320f500d01980510702984c101801c00e540d00c1c419890007589034030450294602080452501050f241007050000c0c1c1006100d06141051282040400007142c2001388104c1e84000c40c05000300000c1c00d90002c880c000d081d000d03902680c0e0005214280c0c0c0611004140000b00b43c0340078000c1020903480a00981500006d590b0401c44025000104020b48070603001003842100010740000c2a0060307500039481461044020008549101c0c81252500761500c07078800140d01000f414800c800b050361140ea0404030309d20454100541e41c1e50390764103858540007858022541c1e140f980c1c00d15600800203151112088610007059030500801520045042c01030f01c58682010482c001008101116103052 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 681908282 1250 681907032 681907087
    0x51f14031501030c0f02031e040b0a1706060306060405040e0f03030709030b010e0f180313271b0e1903111503060112020d0f0f1a0603010b0a05 63
    0x140c0c508902a840c031120032040c0e1600082ca001024802c0700e03c05c114034081c40425a01462401c1080b40000c440d0120340c5207440001c1c1c00800000803100082c4000381554800740d211240c4e1180d6042400c1d4002030010b00c428002c52080042002903511130080700d060700c0e0300b2500020a2003108064900d0458000c6260a161000000f0b0007032284d0821820401c5900c2a020000142e0702c0320080030094000b0790b204110034212001107246071040c2c240741410001c1010890781002261141c041c0002c91991003141d407a01003080c1ca0504034401d20b02124518164407060052544542400c041a84100070250400641c12614811076444c9900100590705622680340c00307586074201803641c9881c0c0c18a16100710445e01e07550650b02d44203003d481c0b0a00c816111800d411000040150203580001d10164005603200704044150103103201c1e0351074941d00003000141508411640391a000d41d1003c2184c4640c10500041180d80d00000840d003c01c0801d140c019100c030b0b00c04000e91180404480755045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 681909532 1250 681908282 681908287
    0x30702100203130b0c0d020c060a0804020d0b012403090308040204020f16080d0c111b0111060702100b0118090f0e06240103060302100305090f160f050109051f14 71
    0x1303070070b4001800352014903460030944045900e075450917139455000004841d04000144844401c180c005c4c03000c168080d00280145003051042e0381c4131168207409030881c44a5a00d0b0b006007403510b84500007100b00811141c101080010300580380540345041c0180020300c150380001c0c40301070300e00905068507135403505001400c40460541c500303214160003041e0b1034028289001e410101c1d980c03203100c48960041542c0042c0c609249a03508040d200d141c0f00381080c0c14080011220915805d080100c0740c0310309002ea02a121200d1001480c400b07642c1707184003d6040000e03008658000110001b580c40880e48400000241952110b214030702030016401c01c80107034041c0b402042107488031600741c0c0404a40f10364840501c3e80902c2c1c01034080307d40c0c5000180d0410724074207035441c02a000c0d902c001e0f00a24140c04840740b0003039100302686004038003941400c000e61000c4041051420540d00200901802d00701603010700e0602c4e0104a411280c9040030324164284d0340414a00c4d03006007000120720074809220796 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 681910782 1250 681909532 681909539
    0x30417160b010302031005010b07060c030b060a030c08070518011101090501140a0b0d0b0a0c1e0f120203092a0405011215270c0b0a030e070801060302010203070210020313 75
    0x41840d0401d03c8241c1c000c2c00f42c01c0c0d0140c001056886814142e0761020005070900c10942c4030000100741c42107000007416507940c400e000340d540d040b02521854555503000b064681e0601002445030030054103102c00d1160030312107040c1c0010407808032072061400b860030105120880f11194054018584098800d51800030076102130740c3e00781c5140d0b1041140d1101445407122080c144011446000000f600a50394240801e140502c540c018074502101844d0010b01220214403e141c074000e04c4560740007040201054060075500b09403541c1c0d507032006203011801c516154404640742c0c1542c030801c0c1e80c6546200e8600c03880701801c3c90301054100016208000e150b0312000b0000321301c581d0010036507a490544481e0b1440d2034450007074888081d00c01343c454040e100045100170220011000c101e410340c07070f0b9601c0400d5002e1a140030b040d44502c90744e40802d4071080a824035040c40c880e6000510700c1d90400d0f10520141c0d030008100e030754441e03060300c00080580510504030300b10300861108035a40c0700c1541000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 681912032 1250 681910782 681910793
    0x10228140c1002030408060a020a0c02130204060323070509010c0c0626280f020c03030406151a031803070c0314010b0d080c0703050f0105010f0510020303041716 71
    0x1c005845098503526501001c10005076a80d000e0b03481040382d543d00107000074820a0301c0d43c000c0e0400512900306411a4a0a640000c01d2006112131071071083ea404542003010300d9050188206203400c100d00403e0034954020000c02c1c0c103500400e6070003809030006071004664881e1001c1d207001500103c441030003a40303c450082038140312000c400a040c0300941c80301402003520403e580100d0441c1854020303d940c4040d554081e00c10b42800c5030080b41e4400e68481045081c0c001040c868601202850b84c070700d0a440c03e501291401c01500154040c0400144030f038003000a41484404108003c0c251640d40c1e0f403c1c62806403c501d00c00c1000d50101041007800c2040800280c03064078802c00b1101582c0201c0486142254860081180d00403006503c80000c1207010700140b110260420a88000546039100c0b10700d0801b204d00c04090720380d9504010402c84c1541d0b03610340050803048a14900c9554000c1d402940ea00002c0c10161200c02c201419091888801003118010f6402d00b40c00b1504240c9410720 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 681913282 1250 681912032 681912043
    0x9020d020a090c02070b040803180102010213030503070b0a06033f02060f07051c0b0607020901030b09060f07050702010509040b090a090b0a020405030304150e0402030f041401050601022814 83
    0xc400151017148008078200390302c0000d560a03240f41c28025400c1882c400900880c8000343c540c03030360565608100c512003440002c070315030000e0340c080ea00941d515000c40c5001014a00c009080110041c03404000784005541d48243c064035503c4601c0d0b04544200c4000d01c0c641c8404a1644003240076030f201e840303596158020601504c9006482401002552034080c1034031a8452020b034130381588001c0046807900e20700b5500008030598098461402d003944c40d8049030301d118007a04192090b55280381004004003080002c5640720048040361200741c20b1008000e4207500030a0030083c10b0110103d1000010348581d8042c29141100824080385420990303207050007051660342c1030b41c111702e407100000d80c10341c071a008540480c0e5000d802546014903084007205000c4650540f00108008800800d0280e620740c0061802041c18020121882c141440e02e403200c0224420200320690504c020000749a0300030401c00d41341d403042c10501c05a024031401203d0300c103880c1c081c02403030000500c02452204400048 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 681914532 1250 681913282 681913301
    0x90e1608060f03120d14010608100807050105090607061506080a0c080405100e19150f090b1f08031207030b0a0806160912110424050409020d020a09 65
    0x80d0111152074140900c2064600d02d0039080e01540720082c40a00d05080308020046030401d5580041c050036010b0307400d011800d085e444400014500700911405c07001c2c0a0184c40200151401450094513000002c0c182c2e005010255100750400b0030b4082c00e120680c1c002e25a5102154600407000c2d85802c800f0b8000c8106491701a15a460b0140410b501805922118020b43e0420001d10842d802100c040018081e4002c4c44041c2d4020120507449102c9503038083c15a440c17040440703146004005c106501190040e02c0d00040702401c0042840208401450700d6411041c14078808040b458624040300d003501c0b440e80502c01030f210000d140c508020004074894001e003036a0340d051101c21004800c004480c007160003481a581c0003c004910480b1044c14001d00095580c1400d5149070b6450408094084450740b0a840c1030040072801032452402c2c2c4280703103010003030703030722010590661039498030f044d6046024041c003032561401c290007950364501f0803a01071a4001c000c00c0c1e11a4442c4d0f07048029191601 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 681915782 1250 681914532 681914537
    0x30d021b030a02090f0403021507020c0301050a1413020a0b070f020a080d020d0f0e0a090507030c020105070210051306050c0c011112161404090b2b12090e16 69
    0x246a40310341c580425507061041d001002070f2035548a000e0580808903011b0000c400307500ca80c0050050380180f0043d110b12131000c80c0c02804001080300d042c1400d681c2e0090401000e1031a0444c0445000c81d071220341e5800407200d40d0b4800c615401440402c4820800e03402c007008245001c03a20f10300704000c2d00301441c4034074820b42d100b1000d00c0c4e5401c8100c3d900c00c1c021410380096089007800c0070350503200d20100d0f50444030900e0200d410303d5903070700030590100958000403134458550042185c2030703400d401021018526880200420300e440030740252145d03410000074624940701c40c0442ca218500428000045810034800c0041341480030754006581d201c41c0d00741c440c650804031440c0700e01c46c3c420203030b40035503005c090688600c0d5039000000d03110650481ca08d50510030403080b0004042202c8000d000940094100000c2d0403004404210342d90440400400f0103500c0a03242040c4140b40c10980210640d000b41e0107041001c0a0f242a1540f1000c1e80041e51000d15000400aa43d0b040030b1074004540b501d0b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 681917032 1250 681915782 681915823
    0x2030a0b10031407050901060c08190f030506030d0f2105013008041208070501050a0e070f05030319020a120f03053414041d06090f0f0c0702030d02 65
    0x10343c591a1074030000d1041551124a0394010400b084c00749100e0040c0e1480392043e10b1803c40c4007042810340820301240000000c0e104000000c0d060b4061003140d4100b182240100b04285081d0f200a20844a02c1c0b070761010001e5405c06401212003491444015801c80c80c8180095a15042030041180880b0700d210900030b07543c80c142c061800702220f02d030019600024058602070801d01036034098418007070100c03100c507070801c014030110b0403e10803140168140100460300c40041600146040e41c1c0c0d4000c0c1e5a026086003040005070750010803a044e0201c3c00713441024400c2c643d802030f420701381c54590140011445000000742c943c5e01400d00301001d003058404000540385c43c0600b0006010700e0313071826942241e00c010074500d4045180c08001d08122890b03c64200403417040040000d030819488174107819010128000c81c01280702c40698001000e4896180900d071140d6140c28051025201c082014400d1000c1800d001d481ca0807500e2403900601221201e2046040003555140402d2000c2c69040b100c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 681918282 1250 681917032 681917063
    0x61e090c050d0608030d150b03010b090a0305030706060e1e180712030c0c150507062c011d030a0801090b011e020f1b221b0f0807020a0b0c030402030a0b1003 69
    0x7c102d2100b900c906588881c00d41c2c0c00c100c0002025405240d01aa01041180c0c0000001d04104024416540704460100d005464090f40d80c40c0550b019040b81542e221803581b00e6242116171784121b81c0318403076607100e081c0c03000d02c060804c2c00c0506640003141c20700c5440750350000b8950041d051002403882411004d0081c3d81d501a502003481855280000107041040440c000c40e0498114103500a46401d0b645114a000d405805100100c01d61190050351035801d400e401c0e8074460003246460034044007451520125450080c880f50050040400090341c0701500105a44200d42c0f0000d81014126084050800388001a54480c4004c035014004d00c1105500d020407482c04000e00b488001c0035020307400f0b0500c41c0c011086503005000e130280800d40d6800103101c0d60406054035089080e03041d21038052081c0c5441c40107002c0380000b8940d1007907501603200b5000140c03013010030315444a29000b80580740d403a21300c0041d08217254400d0180004000d00144004a04181050411240f04000c41c0800181 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 681919532 1250 681918282 681918311
    0xd0210081e0114063108070906030206040b0a0903021009240807050904020918010e0c07050d120e0f06070e01020105011401031d010f0504020103061e090c050d0608030d 74
    0x90080a408901800340c07680b0130f0400303c024110641d4010851100d03c41d0003172000c401c0b80c983c1d18041c0044480610100001c05042c81604050b100940741031008e282560007140580c840c1d4414403d01c8030f00002e01404643c0310b1000e88000c0d56004206203885e00c4c0302800149144d20030b0182030300003003140c903a107107006002080b2014100031980f101d00865881c00720035510f035040b140d54640c02076002c105103c1c15030746030b8181c620340b0300c0c100e540c04145505201c0005641400205040000354003003101c0303c0403400005001c00a00c405141c10031003940da910144000c0c10074844031010501c04c680c14400d0215000c145207108099540c0c800d5554980500120b090b00d00030710444020991085004100d03510a8010300312801c0650355512003104c5504143d401c440f008010403010f0707688c5406000841d0b906001c0e0350000c00071000000d42d191060281d135058a50075214140b01d0340c2e0389030849030308076010b0025101070158901c0300300312a0b03035120100c64030395214480210a44d40741c40000355110780d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 681920782 1250 681919532 681919591
    0x9221b02030a120e0708070f030308060a0602030f1e07060c030b04140402091b182d13061208121806070f02073627020d021008 56
    0x142c2541c507241d00d031099104041c0240f082a002d5049409682408203808004100c0b000042841182c0001c01c2841d41c03c004141d108045c204c1441035080c0001000b60960010a503032920009103030741c03a030b15600070201010861914203000030110000c40d0b508140401c90717000d20f144880684040c4070408030300080000321000150944805806c000228016007010300f88642d01c410400082c07680800307030031846086c41c3c000c0341c190f6004001c4225018943e042000b024a10b04103150003102001b4440607a020101e010f00c0181c03400744803003004d1032105094540080300109214681021100c0103818400e4042e0301c03420010403001c1d08000032410103010074004020100740310002c0d00158548100868108210546840c214855000c0125407592600d20480f12030180b00d440c1c1d101110304079008440c030384500c0d030080c0c1c1181c171b070400301e98280000d003541c6a241c0e4086928052405402d200080c01c0b001e44d100040c0d0403c7c0f144c002c1d0000d03140c0007440d950040700c0d0b00d0646050071003285160645d05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 681922032 1250 681920782 681920797
    0x270c02071d040c03020316081605090f0603070f120302010501170c10111516030903270f0906050901080304060c08091305041104060b12070509221b0203 67
    0x404250300c448a990041d0601c26089482100c0340100169282c00107460300000d01012a11300320740400400807a8401c0080190394840c0d0b20311100c02c10b15082c00103c0e20b0f040244000c1e0600d00e1000010469174080c000c90014007071001e2640c02960b114045404a101d8070003081300950328050020580107484818015107680e90802007001c44201401e0011856021038214103104404002015600080c00482c41034914aa103144007403038809001c1d100510241d1030902031603c0c210808010035070045481c0c0e4143d41c24030340650300000c3ca000c01c2800440c1030707012180350500004045001d201503084082111011901320114de41c0b135504143d00c0703228622507800400e801690389000208010003500b110600203000f83c0c00388441c08448410f5403c2128105c400c0c4491000490180c130b041e200d500003038001c4c4000726081000000c0d8900350100003030620300034081d021800701d00507600d80320b000e0703042e60f9030041400785080080702d21000b0300004202d0031020403c42c10700142c46440001641c001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 681923282 1250 681922032 681922049
    0x6011d130f110f040303051c060e07080c0309150c040e040c29031b070f0302070510020705010c14070b16020a060806010203161b23040504051c09270c0207 68
    0x1c1600e5a94251115441840b0404006c2d19035003824420503009e01c107060050400c0102c407550380c50044001000703050001d0141000c06014828041404000146c80d06504007440039142507881e50024071845002e5584241078441d08a02040f04100c0c034484018111807000344550071080300071a03446021107104518244071641480003440c807055802c0c60b01c60410300c8120241c0341450300d03100c0803050080c0e2001640540d0107120f041000b814141d50401d2403284a10203400c80d5030034880000c2c85c408a0000141c103008200403116481803003800900002d180100b845641d9106001480007410038454041c0e01c210514500024628000c45c1214891181680550b15100e0f000d40880c00c82246035038180e0391103200041a5000c1800411410050200d04291800c161500c0142d0003007044490030340c0f4000c90400e824800010300019020704d2103040c08540161402c043e0004a8018020381c0c03010352188407481803803141159000b8081400030340864244803a2010740e5060740c1d41c840a11401e0355 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 681924532 1250 681923282 681923287
    0x13020c0f1c030b0f0409030f020c0405091b13060e0103120906050406030504050106210c1d061005250b0a0c051801030f0c1107150806011d130f110f 65
    0x1040c80c803950015460900c004c01010240142501050407628007a8040703001c2184000d0300808507030100401d514120003120107000b030745491140e694440480b0002c0c203940118100c94041705603a501510460408106402c2100750750f43c0f600701c04200800e21003034038014412002121214441d8034024142d440d581c4800f460b25140c080110b004200082041d9855561020007017690291440d4020311042d03006117040d00c3c1e903400c1c1020718445a07154400e501c0d02c43c2c80e0203080c842d00301c04860983d00c034500710f490b000075620924040d41c46115284520030543c50888202c88940180050300e80e8190086c0120321079aa9022010412100c1032a07078200400c0b030038000518010f07009904116240d4061501007035042e08440d0020aa520f41c90006002c2924016400c08030708042281d40c005041c4580007640403051010098508800681058100a1500301e030a0103111110101c1b01100c10160002c0040c2c81c881603488000c0c00c801c00403001103801c181c40d510b1104a00415070742d0b00c4002d07620711071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 681925782 1250 681924532 681924583
    0x80a050d0f05090405040311011508120f0409050c0d0f0b0a15030204030804090c0f02120d020d02123d0e041b03080a0801060f0c060e030913020c0f 65
    0x128401d41c24400507040010810030340741c03103480c1c0f8000d1500544c407d455030b41c03501c0c80c0d0454150075581c00b070103c0800e10b01030b03407020040c9050000f890014140340c10b804c070344d0303030144d00c114200c5500c81e942252800504003000e00011641d94001413018406205040004c028490300e00000d0b180b40180c00390740444045014070545410340c15110300509141401461710740d80355282500b54100f07a00502803d651000c1d200d01c4c60350440e40c200300b003800d0351000d040d003640626100140340c011a03041e05044e175404901c14145d658290b040f910310800340c5000020070701d0000e00c01c2e4112003002c01541c030b0709408c902a0300201c0d0541307118180b054650345412200a07003444c18520403003400420039101c20308240003410018500392114030140d400f40a049503101200700002e81081010381c00311040099008940c40400d51000014814030361100c03002c113010508003000c91450041c0c0d030f442c0340c0c01842072100034402100381c1c0c014903c1040d502c060f28180b40740000b00940b2026103d501e1400d076006102d545 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 681927032 1250 681925782 681925787
    0xb0603011805330a0c031e051b041505031009020c1006080106180f09241a1027060e0f03010b0906061615050a0b030d0f0c0201051e070c080a050d 64
    0x11105c42214030b4009005881038a02c0050b1000034407182481540d01c9007400100024215000780002601007001c1c50607107000c81443e0400c403801ea01d001008004030120740d4104070814400002c0c00d1900c010340d110805140c460b510303110f00080e440280c45c41e14034001000174042c001c580448120b4861320718018558001080989001048610360311b540c0e26509000070340072280303400c030b031480d0400064006162884580490304000e1340c20754240001c500c80e00c166501d840c0b03200b81c2ca850078600124185d42084403000141d4003034551440c0400d2048002c0341495120030010704401e0100c401840d00740510041c10700303c2e044603961640145410700040ca00d81400070052407907500b200e0104151090700d441e103003c024501030409040e640c03214244840d40219004543c1d000404a004e030005420449001d44400d0041b401e00c0e0a11402076441d40c06c2d6801103081e1070041020b000245c0c003200780b0030340013a51a402060121401448440c0105030b0b0440001c800c0b1b1415440802445440d00501e800e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 681928282 1250 681927032 681927041
    0x10c090e131e080702090f060d030c03030e0d0201020307020111070b1b07050609060a0c0f0e090c090616062306090612030a0e030601170a0b0603011805330a 69
    0x1562000c2c038411a40a011908003409400c0754010f14407591a00742520400c42511400f52090681c480c1420501c15a565007280714480c041e4142030224015034079240503000317800001941101401590007901205406400551051003941d0007041082c0f0030580b042418010f0000c09061a185400007502c0000c1641c00148035007280b01c40345062042c40e42d1000d181c04003c43e0a06150382102003031103a140a00d0160103680c201a04001c00300240c07009000302454200845ca81c441c021450100d00c00c10958411a400315401800d01582d94100786d1400810081c603020440740580750000c9110302e6120084140c4d2240c0c0c4584c92152181c4a001c200300c0b040ca000f030203943c2d00240c0c458074403610039420401403182c81155201c1d9248403515000300b40c00c01d1016800006408003580b244404c2440220b60640700d140d000c0c01020303040d00c4010200703004040100300401c1d402c000e408144148440003440c0380b010034040b695070b400300d43c03040c21012041c000c400091034112410408203044442e01d400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 681929532 1250 681928282 681928321
    0x6010b07060b090901090303180503030402010804030e03011508070905090604060b0105090901120b0108030a050a03020310030c0e090f03070f02010c0f1b050a0801020c0c090c0f0406090503010c090e 87
    0x402d0303400d00d80c00026001041610b048880c0da64079540c400405406001c1c1a6410440d4020280c080d502900c0d415124400240003d0411400100007004c16019903e07072010442c0190003042024800d103284007550030780f4001e202c4540f154040000344071038140507441c414104003010781220348903a52a5809031003483c884034140b003001d01c03071103c403600c2d21a0281d0007021841480d07a01046581090183c04006030064601c40c0c00030070058205507000700c203d9900640c60300c1c0040c0e9030b941d203108003180c102d4107400c020011a003020000803104407a482d0140620616000e803002845940342507943c9118041c0010300f013071031400d45c4c81c0c05503001e004804500350240488059903911581d0700341d1014520b107405031491101907002d0281342030500154002d001032000851401c0b0300303075174036a0765105803508040c8503d50000008112100070000d071010302c0c00d0407002607185e507144c2d0030140110069000d1b10380290300e080018074800d480b40120004130380c00c25807540000d0300c44907204888001c0c402c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 681930782 1250 681929532 681929543
    0xc18060e013b2701050f0a05090405010b03060f0402030a0803071803030f0e0d020d0f03091509090c0819020d09051905070b0304050607080612030309010614040e06010b07 75
    0x986140051600e80c01400c0e100a50403894400c00140b10b041111440101103001810140ca102c01a40c2070380d4401d9003030664030126101d0100032000301c000341c82e003d00b5821036078001082d1801e1000700081504054605c2d02c0c05c0703080d90070654480018280f1108100c078040d42c036500c81007804012a103004001d6030801da0740d02e490802c0d5400190080304030502c0f40d108a0000c0c00c901c0255000d0382c2e1149c861510118101c0b100c080c1114550001840751a440030041c0c03503480c0c03021a4800301401039182c0c0f00141190070182c808104056000f60145d4640c1c070907580e1440c20801d9150710740d840b40408034441e810b141210040a440c521215000390803c4001003103a0f590b8654400109004200c0920700b20340785d040c51f10311203a051800c1030518026901400140c0402e109000004001169081d444003052500010769a11203000804681d501c064143c0e90740000002c0c03001108040d0042070590301240d41d045101446201400101c4424001c01000f07038001d84014040f802c2900700034100c150240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 681932032 1250 681930782 681930827
    0x4170d020a0602072916020313051201020712050d270311120f041404050c040308030c09041805010b030c0f01030b0d02040e0f0c040c05090405070306180c18060e01 72
    0x1600d01400d441c9000c000d0360340800c2c00c0411002802000184000d1003052000c0c504000303c82c0030004c5460349601412f8400d40440c45980801c1c5825415502c03030503086000340c03903c0004100090034a9022419032300485041012500a01400c000c1074405041d512001d20f2181c405520104c0302c40070103165610441c028030024540e056200806000400034010303130160f0390b500d0a050090420500d2308401d00850910040102100b03000054408480e044101c3c41e44c3c0e55100c0c00410301c544102035129078010b1410000d008035041c64500d0a1189215074000c1002503446030030140d0726041a2400d6078401010f0f0b100300104c1d48250820508003c0113044560380300d2003540003034140d0b0b41003c0140d64517480304510400140c1c04005111035014140c0c1c0410a501d50440c004040f071003502a140d004640f03d00119022a11a502c082c0c014082c1c224040051000200004050840f14400600055110141480580040b016a02100d07803030340780c44c80b00c45504001075445514079407000d401e41ca41f0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 681933282 1250 681932032 681932063
    0x813020420030a0c110715051e0f0406021b0a05040e01061a0a0912200609100e010e0105040e010905060303070c09090b01060c230307021504170d020a060207 69
    0x9900c060b6002d100740f91404210110768800c01040d90745000428142d55100c45d030200b0013000034071710b1200d8120306454010341c3d07501085000034002400040b840d0802c2400201a48009120005001038641950a44115682c1140c0c192500418000d03903d038888840801049186010350244952600950001c2807059540d0502409640034460340056940001070f81550705074003143c000040c254a01a0009604481d2130b54030b0044080002d420307444000620b030000e40d030717603020645502c01c40003880200100c103480300080c441c04c2890000d03400706120b0f01c01d20f07623a980100c05a030261001400d00608982ca07180000d80581006410305415000410140d4042198071501c3c07000741003103100203d40569580792078007007203005901070410410740c0742c04030f400100404800703010b103010f04092007110071540035960304520074160029440080e034881041c286a8031780241080754840b10303241c0b2200c41085142512400100700880050308648000000540c5070b5020f003800c14040d4116202a190 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 681934532 1250 681933282 681933341
    0x40e030c07142206030b2a2a0a05210f07030e060d0b0a0e070c0b060a050612160509093103020109150b010e01110f0d180608130204 58
    0x401d81090f81c02c1ca0300d440c01072044c4000214225044541500a010483d500740320b121524044207894951000f800100400d40448450b0800031078400f80644240d205091000c07140e80c0d88180604484d00e0103220440c201d07545200b40703044400818500c5151400d0303442010407840d03134043c001c00c4003800342001d030010311a11060f018054090000c4000600400c900e400c11807010400c1e40607000100c08034040003501e590214402e00d005611110314511522403400052202c0213680040d5000300300844c000e002075445a1110303014441041841c10b12444040003264688541c01141340c012100d4408104d444184009032013844102c0500452980c0c1148030b181d02c0c08005140590043c0c1d180c804100078051b40040c2c10f5100c6103101f800304040810f44002030602000c10703442a0500c0310210307008240c035805214030b070b0096541c42c0a40791260340c1c9107000b50005510071140d146030304071201c01091480c081c03071030279000c2c030809000c8403030121580d401c20028101000c9003003420483c0403150a000c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 681935782 1250 681934532 681934579
    0xc0801020a0512010e0106120c0e041107020f09040309151214150a050f040b040906020c150a02030108151906060203180a120b04050a0f03050405040e030c0714 70
    0x4000eaa1856a9403440c800030f0f20032400181c00020707024240c8801008140e803c604035206281e0440c10103d109405803405882c5201c2a8103040d030014180340d8200d8010707808200420206200311040c0c641750450b00309103c442a811035005000c100d41420610121908c03030050110152146010ba00c4848012030f04416229808510301c240c000900c2400b10350003051030459401c09081d2080c4034643d141000007100c9510f03003000280541e60f10400000340743c60f1a0030641580b500520190340e990803016001d5540c0c0c10501c0d110302e0b0210b0a10214413504043e00850381214a824020088245003407040301e00804090840782440c1410098000c0e8100240a40002480c540e0050758981055480402010010b24442072055400300c10901042c2c411b585034002860b001165410950b48920f00035203000e04040010344801c15482d07802d0704140e4080c0041007511002c5e1014800c014010f00d0740f0769203002da0031144455030007200d024003120b9440380c0c00f6280000c0080c007403042000103910705003001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 681937032 1250 681935782 681935797
    0x60a092c07240e040b10030b0d0209040b04020108160905010e180709060809010608060103061104050310020a030b012c01210603230d1b1509020f1e0d0c080102 70
    0x103000b20032581084540000d480c405040c0255024007040740034000050344580380c282104181942c801d01074a0a40b0f400c088074100540c09051481c40b41014240082400d408903412400a49000000385001e0003600e5a44403421203511000c50b030300d0401c4015149260f190a10759041000c1050700d90300c0780255a24a030041d0015104c801c0c42e5414000003c00c580001004071500307038181041004113803c00100030741183d4100000090024010305102c2c07452250b0303032110b54940720786008604410703250390003082d421420362000c203d0f1140e46030041d554805040c4064403807545c090200840d030b030120b0496044000e014035084400400380302c900f2010182103d108943e0306d5507060309200f0480c491b00100e50078244810a82d400541d941500380e9260036070007080d010425101c00c105034010752000c40c3d0f24070681c40484070f100007082c0d80b075000042100c0b52080e071240b1811040c22006007400680744003a0716a01202c0c3c1c1c400481241408180300b0b09500c02ca95a20035080c0c000b40b44c840070300c094001c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 681938282 1250 681937032 681937079
    0x30308340c051c0903060e0106030c0b0408100b0a0608060432010f2d0302030706050a03050a0b060f130504060b1902010e06060f011e08060a092c07 65
    0x110034504259180040c1000032940c040d01e0400c0703d41c1c0064200d98004226a400500800c0070b07039100380001e015116551005107121001500030810b038032424050019078050104944031204035644c86000d4580c1603040c1c5400c551003460a1010030701c83c01c6000d500074070180010568012051174000b02c03001e01d009210711140078007040322100101000c0c00340186484600c003407a0600b805080b85a07081ca030b5617032694200d038250401e0070404161030001e0095130000d041e44c180340d5640b04084c0140c0c0c842690000081d28100019076800203600c0340d0014081d019199508000381c0c42c0445c10103600035073f0034820fa24000b18001030159514002d640141c0801900151100801c162000403007030130601440035a410440e2808a0520018045a00078800c80f07031030f1203003088480180c5003039800642d09401014035050fa1850300340c104060b1801000190365180033f4907501c80c0110102c031114282481f0405c20300711b60302103144606101100152034001600c03081507032403122401001d81c02150415 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 681939532 1250 681938282 681938297
    0xc071205120f0a060801020304050c0f19180605040213050103022101080a230d0507081b010501031e08070f0804080d0305040201030c090e0403110c030109050a15020403030834 77
    0x407200c014000c080c01170241800960840c107056940c1034841113552482401080c480c41c01d40b405a444405145040c0c20011070341c11400d444850a00024000c00c3d200c00c0e2040c100304001585090510882d110342990401e40302d20281880c004401940c04900d0172401e0f42c10101400c4a651408001c041c002c1c80e0800040c0700049062038540000c00140d0080d07502c0507100f000d8a07a2498000c602c001c1d0350300b16494400d50355079007890403ca80c5e016820340000040580300040d0764440055003c1c41c1a00c0c000c543c035200741000b0420700480149000300c000c00741c00d410311200c070010345c165001c00003013841900203d04254132440154540100d001010b40080d4035081800150b50309031040342c68441c0c039464211442d40c1400c889001040c005000142040440f0520741200d0b00e051042c0143c10b507000f002409840345a080440c0d4031050320b04151410704400b55002e051200034402c50301240d906071034420041da101c400110145a649000e02864000e500e602603c7c5c1d640d1903140c103ca106152284c06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 681940782 1250 681939532 681939541
    0x21519140901060f0b030a02030c070c270e03090d080904320112030f0e1c06050901022a0a1a0f0a0e0619141602060f0c071205120f 58
    0x41c00c0d20303800d5204a16400c5510802c5c001608501c045990110710444007580e6030f182d8240d201203034402c0c00c9000e40b059000e0100030440c919503100300c0e44120720810071500c98080090394041100c5d40e0143c1103c142d072003003000c421141800002500380318016851a030615503c40040340545401d510140c40796450000e009200d0880040800750760350544200d10b01c070350304004480403680180440502408409129400c250303108940020f40340340d02600c0e03a03004510b0313480c01000b140c0d048241120282d040c0800501a007005200b48c82d8803520700303001c18503034800d00e040a80c00749518200c1c04089008a00324040828800c00d82000080004002d00c00c40c1c1c50a00592807104030003a129120ac2802c0c44041c0141c08000241545c00070211881c0c0c803039203903540c04144000c1c00b1100300d03001d03a85408400c0200740071407920040540070b442c0e004d40304540c0c0e0b4079150001d828021151540c01000030301c4910085001140c840c0040b529a042039440c2182c0002e45100888003250b01c1c0748500908070400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 681942032 1250 681940782 681940801
    0x10608010b10180306020702040209041406030c3a14070f05030f0705060d0212010b030f061507391703090d14010b06030412090605040602151914 64
    0x2039001c02d50074a840c2e8103000d01c0b1600d4100944082c40050071468000c00e1500a555441c1e0403648001070003482040000540303c40004500001c4910030f103e40254064940b40382401183d54171090f40705580145888811a10301c4240302c02c409011307007141400d0146100040300200400c0e4143c600d400101955868070b40d09034590f1f1a80d0300034501030307049843c104940010020b0150140c500c00c95a01d80c5480c84039804034003d0046d540401851407818000140f2903042000440c0514403040c03401d4881c1da181014410140c00208a407164030004100400c0410108400442e00d49032011045500d0074002d02002c00020001c518410241040c0404100c80044032496402c51500000a1420908400700182c03c3e5240c80c0c0d0054030040412142e140d1640d429880b005041000a01b00d0f516410103082440c4420721803201c03d00440d040c03d20110350140503070207403800c076201c56000b000c0789c0755045c85a480c6031001030f00e40e810303044c2c0381e03003000c00d00c409940200c4043c0d4004130135903d002d10f00745002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 681943282 1250 681942032 681942049
    0x10501170a2d051506152d04060905130207121206050411120114030c01183305120703022a031e180d030210020712020c090c041205030903010608010b 66
    0x545224580700301e00340403854015411f0398044500e441c41e000340544044413601e581c2040004c4030b4500707100000c0100e1000d030002200700a440c410b9031482164003400c80042c0c200c0c401c25101820f8a40d4003000c0c400c0c9c03940f007424050b03c1906ea244011651603540c0b030110341034540742010300030f07a0600440e200e40003114603484d2a004007440c0070414441e00206c8042501d07003904041050410801f0700c4a40c540803418201240141400046c400d00483c0e0702e24500030110b42900044203030401c110340791800c1d510620503600004039510004802d41c44d600e03400c1c0d00a40c0f0a400c80c20380c0800401e0321061004081e0030720311084202c44041c5548559222a0b00e0300500d8102c4c4002562109220f007010514000c402102081e406544d0641c0700140e03810243e1400840d941b003000200c1c000102001040f40248191840e44050b07022180507001c1e000070404108011a00214020020b03c410814410302004222070240078205492415a8190109007541c5481e005600305030b448a00510190070700c104d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 681944532 1250 681943282 681943291
    0x190e01230a2007020406030b010b0403020a0e040b2206050114040b031b09041403160c060302070b190b120f0705010801080a0312020d0c03050405010501170a2d0515 72
    0x104100c80ba120b000e410203840088121124100c0000c5031840031912150f110300d014542101c2c1c2c40540391b958409841c0581c2c4180030481c005c0b41c1440c03001480d0702c901941a805182d1100320034109a582c404644021903602001340a45481183e9482c0800c0844c8180c50182003000100000c5265440502081d20a003995140c0680c0c444900b030400b208003285183c11408084a6600c080d40b22414260700c90020b5007a203401c43e001c00240107903204820410030b0391142c072502c0c02c0e0040a0380d8100a908034061000060110840c520000b5514070f588801a80c81103060340300085d000d0405c40100b140c1c09020300c0c03103a2840d0302921240c40c0d40e140800010000b4030091a0000f425814403514944071501c07010010281710301c2d940a40f0b01c0034002c0c0c0558041c0100381e4420000c5075042c000003000b404c801d8505580c00e518040000c14481c3c0714401d26100148450024203031800e85030f0384e2a00c40d648403c65221040d1441181002d2980c01d4010001c0a0f4001c200620143c00c0d074401e540081c540251 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 681945782 1250 681944532 681944551
    0x9090b0d0f0f0b130b1501092304050a02030121170d020d050105040e0d0e0103091509030f081b13030c0b1206010e090610180603020a030f020909190e0123 68
    0x2001c400020b0301d54805d160b0700070580b2501050000210f0010b030303020015070f00690b004500c444100054480824140b03d0280c0c82200c0500c00e5488440c8403400b244401e020300c41c9210081c0071035201c0440b9a42c03152003514030403907900a03030007034004041c0ca851300107100c103003100b50300000c00c1080d2027814042c0303a0240204440070880d12054810150740c842d01c440406080c02481152050280e01981c420880c0c1034102c0d800c51111304e0250501c10040c0100360b42100800c140503014110148600f0080f846111017541c41c2c09640d030f00000040c0c0036005094214903030008084040001124449c40c80020015400155100d0701e60040b0f60081c00402007030b140c10003c203162410450750b900301c00c07960019001e4442e0320990b0520403007200d1201040c00c40c4031b40c4c10300d001000640c059044d0b0007401e0146091380d042180302500c50b20b4106034881c0800c269400010100404c10502c808095800c0610710312100080c204921003c96007560f00d106141102a41117242c1c0b00c045c1b084044e07000f0f60000502 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 681947032 1250 681945782 681945811
    0x1e0207061709150a06050904030309061a060d0e251d070c020904052109011b080409020c031308070306060b03040c0902030604020702060d0b150a09090b0d0f0f0b 71
    0x6511807981c50f80440980110030210b10049000840181d0001018000140102000e89031a04024025105808040361805c0c41d082d1504400310180d080c0800c3c05100400780e51511480c0e80708600502071074102800b584c0100c0b400400d11503803044d420324102d00c1484141408a2034143c1e84041c1c682100c0b24404e0340802e1404000b000d40d80a01c5050f0741035411101890640c541d414418a0700307403c804003d0544a450b425038484d8810383c2e000d404108000d0340c50450700c000341a0b030150b03540419000105205400c0c40240701101e000d80280c45c030400345008580c1007040e40d000411a481c2070b9403160901c1e81202c6814014082c0300e02506000c1d040d200001c9286091982d204031504000c1d02c140907605074040b02180080d502c82d01200c0321290014030a944405024100b43c000b000c0b20120b00d4880d0005440040e024410101542c84500c82038450860f80740c9042d0002010344644030705903a03c60329072104440003c560520f0701e8103080c010140c4d0840c9213454a0540c0f00c007200070f000b403440c900070b4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 681948282 1250 681947032 681947041
    0x9010f0f080f1c140a03050a0b030109030c060c030e031c0b0103020f120a02090406080c030708010b0d030e061b1c110a1b09020a0c051501241e02070617 67
    0x2141901c02d04450504080b2a43c0082c0032034140c2058030030202c0c4042c000816400c42c0d5810380185000340200c2a0400c50b000f03c0310109800c1301c80010380140440c00014854010a00c10341c060507488850342008611414100c40d40c6040d90f1000c01d201018071041515001c28a0080c803030071074544800c2c2000c51404205504c1c05000340102c0d9a08101440c607103001521004254040d10b60412000d0028402e5603249d0680716100c41503124001e01030f2207490701c0082d9030041400345246540024008a00030300d89a1070890b01d410740d001c111030308600c04010806101e2041070300640c00000d03035005130403855000350f01c0000d11364850b0303004020030090000c0580341880c08505400c1540c2c1c0a0503c001c3c608850b1290100901d0503440b44810a201207200c19016403c02c03100000e0904c0b030415590845a00c650440c0c02c02c0080c052010550000c030205002442c1e181d400c0b929444440c1415074103140c2a040b01c0106004441900c00143c00103101000b6244c0c0045804131802420b401020300c0f0710b003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 681949532 1250 681948282 681948313
    0x402070b040b1e0604200c0a030809151605041508040b0912030718030602040f0f170303010b030702100c0e190b03060f0a120c1d090a03180509010f0f08 67
    0x8020700024840c1d40c1e14480c04901070000031005c051b84d00451343c040e841c1c4c204440c0450321150040000c5e4042070404000404108020074250a05119909022111b4480300882c41c06a0401540d03003023031003810400801c10030052000944040c180d640c6004051400f4540b80c440c0d9003026141805640c0708000643c40b4640c0720094a51100c03040c41c001c11104001c4111340c4041c8041c0d03001410042c400500869030181c0340301d80c00203480d00801c2b20701c80103550f05846500500d40e02c1217070845420a01c014411035600c03200960700004e8a1044806034401c180240301200c5042c104040400c81845131003500d402e240741c254040c8200c0e6040c0008951415150390340c5407100034103e920070303202a4403810450351180a002e004e80308110b00c074030b211500c0d40360461031a03c0e13038010240d2021105ca11000e102a00c2c001317003480340c08030030040c0404074416902914030395030710a1044a00b400c04d00010800303845210b11140209a40c0300c020000038900000308002c0e00854004507660780010300c02c3d65000c038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 681950782 1250 681949532 681949591
    0x40f05030a0f060b0a050904060e0d09140402030a0b120115050f011d0a1d0a0b060a020a0f03031b09140604060f0c0203030d051f2408060f0402070b040b 67
    0x680002010541c444c00000281c6000e2007038100560169001044c4070600c070003075102c1e040c682425022124207101201d420b0341c14290900c141c1c2c4e882071200c880980c1c0c600f0250091a003000c15043c3c045045118070000440c0c0c10444142001a40c0d500d17000e100c0e545000c070b15405d0050005440d0809014401d400080c01803000e13604100341300003a1885080d032502c41001540081c210014452054205601090054581902d52003178071800e1a030046064540038040381e000803400e40080415081c0c40d46c3e0742e01440304500007074081c1661070f070f038000900c11441003191898007076075942c809850a081010b0074490400a440340a00400d00040c00400c1d04010030818039402c9080201d60603066200091440c411540380c05400350a10040c0701c642c0401540329810a40010100b00200382c0700c0c221201811641715003880b803a00e1103a03070f4141983c0164001a0004c401410304c007030225590001c2416030348903050031030f03d0b5240d480400052000c074111030740d08020081111040155451102c48058 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 681952032 1250 681950782 681950813
    0x4150b01030c09050904050304080307121701050904140c03010c0c0501150e2e030c0815070f0c0f0503030f1e06060d0c020109020405101503060e07030207030c0512040f05030a 77
    0xc80c1605c1c045000e02c90200241c1d00202100b02c1200d41e152454604100642d0382141400d010526600a6641242c0080e001030b040c0c1d100031700800e1480c0c1d640e484641501c0c5820045c8000d601502d0345d030514036142801442d02541040d00d68007003640d00c41c80d000b801c540e4000990303900000600d605100340c1260911840c0c010490000d4165510603056040d80012084501c071014038641410000c108407096203400111a4a6400d807110a03800b0800c104510104848541c000f80e449444046001e000d003c5100c0c14134043c0c1114805201965940c03032460344103039146188022040e081002261a0710315801103408440006001414620080382d414003941d41000302c01d07a01e60700001280c0f4400d42c42102d8540e0020030600490a0180b112043c0007030700d000f0024008080481405004e00902400040b146200c084c5410382c1d0b10500300301d0084d04402e2003201003204146166011510400c070700380042000b1020140e80b46e162405582c00303948a58405800391700701a4050300460700741034044602c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 681953282 1250 681952032 681952039
    0x61503030207061103210403120207050618030a12050702030c0a05060105030d051305100c06090b0403020c041848120515090f030c011b0c120c15020304150b01030c0905 74
    0x20740c40b54523050364031144030b10040c1d040601c003040c03a109124002414902410742e00320201103548031901502e03108e03c180c0c103039000405c0722510440007401e401d9001c5a8410f584e0b105503414414845059400e001d148a800d03202540400c0041c80300c2d103030a000c0b1202120890074014545106482103d004d64000d219140c89105258001611280214040b480705540581c04004402d0207240c200503081d8203a60640c01072003081c02e02082c07400c0c01d110314103000b101da003d03101d40d080460b91401000302d0054000d006155103050000c0e1168102900326441502c1c1029020400320f40501c03a40e0800c006034003640030101305250f510f02007600803c00003c084401443c4a5091399040040c911344440300003800001d210000c2d94409000b01035111900300320b0348242c1c030001100008811207a460080c10060310221300c20520030009809040781e0007001c0d2041307400203030010350183d0580c102d0b0021102a180d0709036183e15403030000542d10480383c040500b4202000032100000b0002c05402a50155502 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 681954532 1250 681953282 681953347
    0xa1e0f0c05121603111c05071404260a0b0117030403110f0d120f030b0405011d090f1c020f0f07090c0e0d1b080a020d060207061503030207061103 64
    0x1c03036038481d405c9107261a201c414580c0d6560301d12070b02c0540c402c0c0c038140c0c8111124900401b140c400c5216001a1201c0406c2e106180d00302820f18014008005000c04600000349003403150001c0b158042c40002d803c0c80c003c420003200780d85400c0440034130b5601c0703c0c038820700c1d900200700520004991045100d1098000d80d90821500b400303001003000c1c0185020045d100c05d08824400005a92218814041602c0383e80c1c10b0099601e04014030082d2403007809110220b5030b00501b0040d05201c0588000d52203440b081c11507048502e00b000107401d00f44107480801001510303c10115456404021030382c0c80a0480e40100403450740858401d4455a403801000c1c0e10030303100c910000e200c0344515041c1c414600000d215107408030861405250000945111107084a01c00c01d0000391080c02050300143d860f0041c103852503094665030f032180250721643c411144a0740c1d45c1d00f01001311203008000c1014602c83c0e0003c0c4081400d001019025100350240c2c1355031039004110346c04c40180040d03030164184940400500c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 681955782 1250 681954532 681954571
    0x20609010b180606120f060a0f0308070209060d0609030509010f0f090618030804080f07080303010b04030618080313030210231512100b090402010c02090a1e0f0c0512 73
    0x191a8444d0b0b0717900012035448003003031126000004031228011042203408501059a84100c0c0c00c2202c0303e8440a0546202444100054240290403d41c0f190300103262070103003507440e51502c00b1a07550380c4080e800103101007811000340d41c001850100074a0306003404200c2290756200180031501c1c038001c0b401000480b0811000c12915580620040c40e80881d9154a030350300e80d1330703060741c55800e411001264030460781c000034905404400c4a060300c1c89042c0312443d103030454076608050680017100d540c500544004480c00f180c643c601560003295a084c45911b14501e500b8002e282c5407842d449021914544000b0344a1900081441c07010482003503200141948c842004036800060180b0b91500281704452401d24501e010a800070002c80a801c1040304409000c00d00c4481841224000d0114140030410005407070304000759a8091041940458048844001c0502c2d034145260a0240b40e521890050100c03222405080a024240e02c0c041d4288901c00c10a0103440d00f026040c050360071030b0b414040307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 681957032 1250 681955782 681955789
    0x3110d05030c070e040c290708090a030602030a0b0303031e090a05010e031e0a05070f0203070f0f03020906030607080712090f0b011401030c093006050106020609010b1806 75
    0x82c1ea6066048050303038581d82d030350030b182e4000c600708036400c903854411501d0100d2500c084007100a62201100d00c980210341d5405014100e82c0d110301002c4d10514801d028074a80b43e80c07001c010708091403181402580341d00381841481c0030b440b6400e8040f03219070001e004200e441d40c0b81c07a4544082c1e14024841c9040e5403a800f00c1c8a080c0802300340040c00f65400d2222004031448008002c018000d0005805010101142c1c0815840d0082000741000601d00f0003c042c04107040d0203070303070b00064001015100c600d03540e4134850035000003650108010248805041040d49080c40c60268400701c250082d007080c0c40c05030001404c0407001499070003804009110b40d200d039901030b4013106031254414100d200e000e4260602110740c2200b48a040811a01c40145120b554464000c108540c5840e071141140c0300d0070f0524407140f91128060100c10a0309455030100321b9806001d0560b0068082d031380006640d414110028105080109000d046070304050840e41c450315071110507a1501e450360303105809600ca58001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 681958282 1250 681957032 681957037
    0x60d020609040f291c030219150e0d1202090f090405030c030f03040c142116090902090c1303080f04050907030501090c0f1e14040605040810050103110d0503 69
    0x90110408507a035582004c0460f0700310003156182c0861394001204e10340e540e215401c11070150024010303041003640c514682029056280424815900d01452404800d841021130719000c120075082e84c442a814030f1165003020b0b070b105030030607000425803030f01c0e82c0007001c14054481c0a105170f005a04040010381800020700a61700c184071024140c03540c3c0c43c5103a07144602c40e00181c1e000e03140c4100800b80050100c1e2a500e0f0096940d1000c0e00e4540c41f4402c00244814030120304001410710302500d9844040c9030321051007880504484500020154954014007480510081422a880604101191449411445000440e40e0151a156551a540c884a0014065640540d4122400b042030015154040d00b015040e11105442040901c40500d411985a00140301c1280403030400c10301f601d402400c440c4002550400c90428040c001c9081d42003c0c12076200368010000980c0208080c0007841080c00804244ca002400074030044d4190349501c450327071482c031044510960002c800402008018800d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 681959532 1250 681958282 681958301
    0x22406041107030302030619081e071a1e0306030a0809010302090603040605093007061d100b030c010e06160803010801060602101104050904050a020316060305060d020609040f 77
    0x85640c94044500e0044c01a41064500c18803541000c5460880500204040c1d0b00f02c4440100500080701c9100e40815103000703448002049015200740801c0144070708192040d07003080c9800065603046612040c0090781d4000070802d0046c2070400600610380da00041920301e9507007040c80103650b424002d0050f0000c4c071601d401c1c15001403003c810032083c0007295001c684501140020b40e4640e0080c408441400d8101d0581c050500314844c3c104200244003030064001c0b5131041800003280c12003c0c40c18a8480350f460715400544c0e0000c045140b640386103014200f17442100b0740042c400c0181c1030300040c01e40c0d0703443c0b40103a002c2c45021a2070320046600c0e102a162144c0c116581c0d40e034958407880d009029149074099000580f040c41384c980301041051081e840b0750880900c08500745402c200c100124201d02500c1500d4506c0341c02003086c00341c1d40c2401141c8810202c3e90251180501e011006819200300038121481a00311119641c0986c032a1022100121411100080e0301c107160a51000200000074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 681960782 1250 681959532 681959561
    0x2060105011b120e030d03050105010909091403070f020a0806040b06121f0209240d0902060c01020c01061502030a020706081810061e0b1c1b020a0b0702240604 70
    0xe100a901ea900b1031320940c00d90100f6001d440f107074400940c090302518000c0c822030380000ca51450421145506a001a056030b1141e21041d03102c070050318034103203907030020b40c0240d440b00c0031100854110f1401e01140002060761a0140c003c030318107a10741c1489400c6c0101024001e41c03104289503402c4009018981c2d40c0c554503680301c003c2d081500b140070000d4118184280c000c0000010749450144003a40100841d2a1042000d00c3c01c000c1450f01c0015010100c030490300035609200c110f90154003800903100101c00c18000081c000c0c6071a1072845801c0b040b11003032095410030007850401b2507001c185802601c406003001540340c0c40e00d1406054807410480005c55500408000c50704a80301d94000d00102c0728480c1007040c007030441c25608840c06080c0d01c200806000b040001e5550524180e0308620807141c10000042e080340d50a4107a142e4294040c1040010303003045562800b00400407040c107801c0411440207054044000505480d90940d0410011007580c603030000907a20768468000d000c540c02080b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 681962032 1250 681960782 681960803
    0xb0d09050a0b09060c04122009010e04230a03030b0307150302120105030f3d0902030708030f040e0c0705160807061403190b03031c1b02060105011b 65
    0x14240b408840320203451880c1c0340d003e104085840511450241d8040e913003840199a50301d02c45075500c004010078500d0b00031440b8001803003503450395903108a10f802048040c0e0150101c0c50309280c40d106070203042c9242d80d00c01100202202540e2000503c018046a050800064003200c03840000d280401d01d5022000701468510588078a0f46d040e0081c01403100c5480005c0b11903601c41d41015125071401c40410f01c00d521600704a4101c0070140041e040c142010701c18151641060301040d07078400004080000c2003030300c03a20741c8800c6003010854000186101c001842c100302400c000342d40c1511071441150401016100407980355034000c0d088406842c0c1c00401c40f0751140600301d0078122100c4d68481d450050140060015855004d0f0700401d035061613003620586540e6075400018400740040186010f6143eaa440026503074038204005d0a000301c01c821030903d503603100100d0109640310440345200c1d0f9045000041801500090300b0740c1510000d0a00070807208040300550428140c0c03040240280701c92 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 681963282 1250 681962032 681962053
    0x10f0e011a030c10180b07060902010e03010603021c0c05120708060f060a0e150a0303020708120c07060f110d1e110c060319050c2107090b0d0905 64
    0x158001d14545101906540c140d80d20501010340754504001503a030462548142c810b00c03140b01c1c829500e01d115910418107201c645440b240741c0e050f004248110750303e5950b40c2c0880c040d503803c071400e107016100880003840355506541c080f036000c0b16031140c4103210344504032043d000c01900344a404d0181c007020309030803c1043e65801c1c4940d01e46851191441a010b50740c00310364800c02445020384611005420b24000621b44940c0c600c5240004001c407640030000f00c01d004250383c801d449500114020350041503103a003080307102130401e20001c95030116035108101000c5043c1c2e010960000b11860740c2010701c20005400c5c005d507645440c40c1040d944d10b0048444884686400c202107041c0300c821141260b0004800c14026546800d01c5011011a07500030300f040080346c50042c0003580e20025011048400c01a00d0b40d014080d920151040c1c030f00d0040c017251140c012880d4181c3c80c0e100c50004104e4452506000c80c024040740c4a60041004100c1c00180800f8074840c15004a01559070150842d40003268 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 681964532 1250 681963282 681963311
    0x12020c060a1505030a030507020f1206070f080c09130b1810210302100522030504090b03010b0d060b150f03040b0603061b0304050a06060e04050c0301020406051209010f 74
    0x30800e042c80400d0318030341804101420002503003007030254140c4400c0e1518401d034003000b20303103040e404c003c651185c15284a1036040034103000c2030b0302800694032401c070500341c0c420000d016210b00030a41450a0001e111b0700740655140b074559460b001690700700084e6148900701041c60122000030301c1c04030030350050602115007900c00c1001c007280c59030300d51002c0301c0c1c4841c0b9101006506155000d80184c0c4240c1602c00d00c06159800150003180e2081c641c03040443c0c2d9000000b003481c601c507060380400e0000c00c04210740b05440c041d00002c3c000c210300800810207020001803086a9011004d00115503c5038008451380300c0c00c801300d03110800c0003d059101c401c11052100b583e4801c84044415280080119046080c0050568000c000c82c9400d07100302500c0040c1d05e00640c20080c4140c540740304001440c800320b0b40324801c0c0341c060328400020a40602d42403e100c3d1401e0b902a00407030090384104810060300394480251842e100741043c605005e61606900503014080d612241001c103454039181654002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 681965782 1250 681964532 681964541
    0x60310050a030c0305010b06041d132102010501050604030512130b07060b0420090411070b090d11120415020307060e061b04050303031803040e070c02040501080303130312020c060a 79
    0xc2c07266000340301e24031f40301c01032003505d000741e1282d403014050014082c83c2c0f070f005546180d82c0c0a42455561a85a8203c0e100d07540200745c1d9054000c40b04800d5500d50756480d0342801045d0150034165640361074545141d40b0b0310713038070b03140700850f034003103d40200300039202d0b0310284ca0500c002d020613890183c94240600b0032000411008141521842c80e11510140384840501c5031a500b01c0f0311928141000c2055092001900c5002800c2d014240100500d200240c4070200541c0151200001004602c81e1002e000d82940c1444100440990200501008070b240c804c040310155240da40ba00018140111002c0c1d2441c0680d80340101120b080402900030f441001841a00c6042c0882200c030a1a800c906020780d940704900405425820030000240035000d00c0101c01010f05031282160b140954420000224401c2a1800c200040c85812442f003513103010302603c3c2c05010f511004c0e40c55420165014401e500000000609102c2080e000e2401b20200364165040c0c0304092007074520302d2401101d240b0080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 681967032 1250 681965782 681965789
    0x307050a06020a180303080a14040c09050604020904090b01090c170a15080303090c3a0c08060f010e0a0204060c0b040606150203041d041a13020402040303200c0f060310050a030c 78
    0x1c0d07181c0000c40b0018800310740276074041c0d6000007000392803506100001d00500001050341d03030002e40800403200561039a10400048a004000640b030550401c0400420340e80c0703000d80c000c1040641050020342180c44d140e8580c210a2541c0000b45203005c895020010740362551041080d80004410050b503e1008110f42024030001c60b01c2200001c2c41951312152a4140e20b6407820214202c0030b0351181003e0b800052407501d0150102c3c1c40555901e42c1360710728003503085810321205111040100300c100b181540058000d0b801140540c02c00e4180350b0000c041541c04c0d44050054224035001c1030501c900c50b030081c4007502c9007040c0840615003901000e50380f0b030300c41d11600c203501218070003d0f64050440d82d0440e004030b60200007511400bc40c0000015488005003c0401a0250342020350050340c9a2008200941c03003a141c5140c0908607001012126407151b5140c6255013090368030700703020f60f5401032140c20260100c0b40103880362251554081c0081143d004160085100ea501200b0b0000720344981084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 681968282 1250 681967032 681967051
    0x130e0a060c0513061b020619080106031407081308040906051c050d200102030f06040e0604121202070b04080405120d0e010c151a120307050a06020a18030308 69
    0xc001c102074225018860790030b2000110340303118010710a031803161180c007000720f41c2a02d030143c0c201020740010780719034006403000038004441035002038905d4200200300e00400003400e0822522201c9005504080c3c0024054820484c039800001ca841c04086408a41e294015125a84854132100707001c008004500890b4842e4a02401c4c140c9440c0c1d464200000075903222000c0c0031413030811001600c2c0c5210703102d8000d2241da8060050440283d00f44061807083c03042031104002800c0046c203010440b50b0400040b0196000f150030433003c00d20901c01341d50755005e9850035040e00d03020b0405400090049080080034001c80030244418030441d4030161040e9881100c02c1c054035a6441c0e005542c07070f05038100040200b40011541d200303660250f185054030714003d00c00041900840d00300700c012100414070b100c800000e01d17850400303242480788000a0410000e40114585269912890383d100070340400280455000140304203d503104582d24003008480c1245050840c1e140c1c03034084e0807104101d44030303c00c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 681969532 1250 681968282 681968291
    0x603060b13090c120201090914070908160b18030307080a1103190509060c010f0603061a060f09030102090a090c0f081302013b0a0506070c0b09130e0a06 67
    0x15065118030940282c01d030b10001e4010341c280303807000079080003140c00313400e030705100e2403480000e010700c91030280300042c1c114088070300114944054054040030190300040441c0d4808403038540740510130f0364a0410303110a030340800c2d212101440501003002c1c074006081d8140c00301044400401424401520912049440e00310110440c0040b41c1d0b070301d000310792030543c1d40c02000c901c400d45107000390004c00c43c025020380100d10b00344103194510309440c074490b003c05e68560703a1384080080c06101d205080d1800306489100e1001180c507400070346c0e0b038003074041e000350008000a01c3c000c1b40c1d51f095049600d0b00c440070f000084004d946041c0000146075030501880814252092035441c1c5101e0f1a11500c13921200710300c003400501036001150000b105240c40e81e01c003008519a59000d882441825100c922203102d5414240c81a00905c40c00401c0390b8005400340e0000e22a64000484030015417040e160000900c50b00c44a600e000540041401625204428641107071030303d190f0f901103018011340b07000345418403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 681970782 1250 681969532 681969559
    0x70f1d07080f04240501060206090d0203040602030423220605040b01090b0a09030c1220010804080c0712080c150105130917030f070f020706090b0a02100603060b 71
    0x50301c08004544107036005412200080002d00b4040400303070303244401641d10306400d040d0000802200c0f420303040301002d03038440400c010300c141d01040070020406c0d891015504143c0340c00d40203543d901440c0200d05001034221425917080040054010784c2d1039004101000c0d00894014080d9100c402c02c8419000d03e040c148081101d0801c1e00544480d4507060356152001440c0180e04402504100001d50401c40407580000c0814809030110025203080b09100400d1012854041c1c020303804940704000040001040c01202ea030807034078207540180c000c040340395540782c00e54804e410320000e0740040701030560b40ca00b200b082c41302e00300240c801c03020110211074105c480200740fa2508402446403550003201114001e500c83d2041c0c0200050500c0f07450720780b0800c0e459906680654200701c44540d92000380c8410061829070140300100d004038240041c01c0e000303041c00c0005013070744068018041c0c80440081c112041d54820030032510346400307100041040c00d84924202c00030b06014140c251050fa1501c038101d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 681972032 1250 681970782 681970787
    0x61d031305010503040f05100f1a0d0339030917060c0c030403081207030513080f1e180301060807120605180d03050a051509041103070f1d07 62
    0x6a165040c0e110304a000c00e85000011101984028412120304142802c5207000a6040118128403154120701091480307540c98054116400d01d01110341e00da40c0400050401d0b00e5244111001d26054a040c8009440451900030070b00404044510742558154004041040c139145035011284a595580301c920b682c0c16942205403c295100340b83c54006001140804a56000901c408005103055905290380c0c0e803228511030300b000840e014440119001c0040d02d503498070410703a000c0c44a0500300c0e07100b400c50315460b00034012540c076065141e1002924252180c0d000601e030400c48003841145aa079042d881288190340500320049020f503017001008504454046201380c1510380c44403400c0c60308021612000301610000e0070400040d82d1030000011111001d110b18410080103490106041c1404034907041199401170840d50700700c403410390f00b1050395150492a0341040d08030184002c1e01c20010b002905100c0107510820001c010120002040207100c0501174010109c0820f11350719a5805006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 681973282 1250 681972032 681972037
    0x12041403060a0228031b08040618050a0b04020d0c080a020a15020c060d15030f0b09070e0705090102150109060f08012f0d02040f08010b010c03020c04091a04061d03 72
    0x28021041140c41c940006020131106000c0c11355645c50041412000c0c00b00700040201020003050001c0d50500807c000d00005002e5101c1c420440b0990700d4100c411600c03080c2e00e40c0001c1074000d240e1660000454155034907500786117100b541002c0d2a4a225a8a0590b41e6541903981822401000c21650000e60f0148a42d01003500c1074094002d0064510540c2c2080440d5228002640712180d03a00c0d081c404440c40d149000d405144100e40d4076001c81200c0c10f1900800000401c1203840707078005842132119076080401680c000343c1074140340313480310507450040c1d05003d1540301d41030441c1d40010000400c44030581103041150b410418000b5001d4071041e801c0e0aa800c0c0b030540c0f02080422002d402241c407035203143d1a010369019001d0354180010100510140c0e4055800f0ba40d008503c03d505000300c90082c841c0b1200c0c1c5070242400200103180d40d4010b0745852407070300d5051145565108800900840d044540415507480d18958501d142914114004200220106d11000000c010302e0700b00c0d9500104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 681974532 1250 681973282 681973297
    0xe010f05070f0c050717030a120204120204020f12091b0406080303042d03020c1e0f1302070b1312140d0b06071406011809020d120212041403060a02 65
    0x1d0b600e51410001e00d0545250110910031500380c8540e001c00201d10303000f0501c0c070781a51b0b00c3c1d001455030f41c0201e100c010025481d402543d8565881000300b003004c078105007200340010390305440158607000307209402c28060080e91503000c001a6004100003120a012401603542881d20384420400000001070104542603806200110791003040881d011607001c0514800813481001c5000c000c0c03510002ca2011500d40600c1200582d00801c0d00c03600c1c0d4645002e85100400c0790b0640703810401c0740040090f81d6074010b0003050780244800504121525075a8048500e07150304840c12040d01d090105510325020094502a03c03480201907001c1d400502c46e040008040c17842c1d5211b541440070490803000241030090701c0c1070340b01004000e00d6000504c1d05099440d24010800a030103e58540004180000010400c100309107141202e0100165105c2e0f0095030302070b800c090203030700321070080302e040c0e142210214814201c0040800e000500f0f403107104a0f400702050540541d00c540e110142c03114241c2c09a0304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 681975782 1250 681974532 681974537
    0x60f0c0405030c121c050c011a2419090510080c0315013b030d090905060301060b1c0b0405040c050915090c0a020f030702030c060f0702040c030e010f0507 68
    0x50083e180d07140801141640c00c039107505607240f040300e00e000b8400c070040e0a012a404550301055122000030300388505140c000380040c0140ca81c00c031450000300d101c0801d41900644403540403200e00d51070320100944041c202c1c4994051804507480303c2c0a0f0204c10140b148174490480c0703602c50300d4083e21403030203203004000040c031242c115120040c03c64254080f07040318a04000e09015102109841c11044200000f0f503d20800429007081c0607040d10740299502d154000d9000c3c1c00031148680e0700c002a00c0450340545000201c40d145c00001034090b000580c000c0e50581c401041441600e00e054000900d550280c48041109500c840c0500c01581c06c01c5601502003001c1000810850800150031603000a0a0019610f40c2c040704000a40d2980b003a52400c080c40e4000c40c0081415070100b10103007600180f0002103040c00c00781e074001795640110b90411401800041345480155000380103541110f6402081072049075a14100100240141c0100900d07540c00e0103140e11342d801c15072180b41d006010300e5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 681977032 1250 681975782 681975793
    0x41e0606080f0715200109020a0b0a120b060307050c0f0604030216080a0c1401030209040f020a090b0c25030c06050a03110903151801061514040e01181b02060f0c040503 74
    0x1503803101458206a4951a246e54a0381403900060341c4247d6038501034002c912805da110056110010700700214191400102e81c5094002c0b50f25644010981c1d50080c01440d15541d81d80051b4121418480310a0409119210f00e0061104060b00412200203a114040501e00e04541e03421806941d01c0c94101c01030000062110140f084074080003800d102050103050240c41c142d04000494100c0d03550549402005902080c042e4040d075205081000800c00c007100300d07042c020400081520741c5401d050800300c07000e5002400c820954410501c1c00250341207091314440c0d985d5104050000c0d40b100143d02d0010b403811124203490705840c000e40d000b5550240060161081884808915401c040d2000060b840701c8059540f201c03000b4000e01012388140301b4840d130303050740221000d4031480903551021841c280500040c07000c0c03400e00100c40c1c11500c902c0e80220198207001640401012200c3c5d51010800b4030035010b509039038000907140d010700c640e04003001c0c540d0f5481719100c0c002e00441c0204d07989034100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 681978282 1250 681977032 681977057
    0x60804060207030302070f0312060f0b0d090606030c03150b04051501030b0105090a0b09041116062408031803070f03020f0612240f0108041e0606080f0715 68
    0x69074040d102e01c6100f4180141342014a442c0d10302c11500440c0304038001008a04000c58008241c000c100003002045a940003042c20103040a0403030041c0b9420301f0f0087e030b1300e41802061040700d0f048440150b411180c200d00481d12030620117100c41190010190550074400c1381030300c5041520413640302d07100d8000c3c84204000340c180110041d01080007070504004003405441e04907603d000d0106e008244400e01c103955000c014041c001641c2c0c810544a0301443d0600c031034000ba403d05800005141e0344210000344105c2401440810704428402040086d65074117030100e010034001004003c3d0b202500c68108980e11540700309030380c801d00d60003008140340c81010204018100940c1e50003030300303078000c01d0345041c070160095090200c1d00c00c50f85000030b888208160094200304095031a4111000d03505d0560001005001904100001e40000c05804030f4110080c4080303283e01d1070880c455031121061101c182d5540401d95a0280301c805101580149080014000c82c51301144020080c0b41d251039079000741 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 681979532 1250 681978282 681978293
    0x1060e010c150f061701050901050709151b06020301033e061b010605011206081c030e0a1407050303030910090c0e0a0204030c05190302040b0f03060c04030615060804 73
    0x2c511240740e80c094a440103002444914095800948000d003440c550709600c50101034207540e0007818142e0325034981020700000c51303400b02c1800140c5200c4142c408090101c040115905900d8281040350102c440700b501d030030440a0340086040300d000b026022403d0805903104200e40041198120381003100300c44a60b610b01102031050743d0342078024681418200c0b0460821180719403581c0d50000c03655685402d10803580c1009080000c0c0d2605c920800050b414018080d564900801c405180001c100c2c292626142c0309400c544c100182d0541071702e136020300750700d8079102d2050410107955090085170340c04540d604000041ea44109007403c01400300348a803e02070001000e00500545000744142400f103422900d060700a4090030082400503524be2a50410b40404000368000900c1000000c4090704032920003400001502e8045074002107544c040c1d000524450203174010a03030180a450208032401c45840c1c0a031040ba0701954042c004200304211950080a0600440001c6009003010901261 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 681980782 1250 681979532 681979553
    0x6041a010f09080a06050915010f091e0e061012020108220206220909080d0b01050904090809040b040e060f0c07170a030e07080c040f110408031201060e010c 69
    0x6580b41840905207803101d680c0c40c100070841c0b005444013a110340501c03810b103404214040f583c0c0c04102a03a200740d414202200800442c03803107071084e21a2034141010307140245100700c01500d6a1201d0801030360100302c600c03d403075800c11104e006680082c01000194214500031840e08103070b05a4800b040d40d562030f415445281e1420000403004d0700b01034440d10068071920000c150b44085030074418841c241403521003007d52120341044c0c59540c00c00c0c481038006a400410380c1c981d0038200c00049001c1d9030001c0100c501e801103031850b640c46420442e55a09100082e40100041d04007920240007031310703d12051109889091008102c9540f028000924003500783c40595048607030000030919084260700c039095184000800d00080b00c40000720901e542c0c3d010300c45c0e000035080b50b2015010ba54502502e040d19180c007407200c24000c9440d0702d018142030801b41c2c42031010031403a898840c2c48544600d2019625000340788100500d124003000403c48600a460b80d41195405a483c1203104940e59119038981c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 681982032 1250 681980782 681980807
    0x160201081b07060f06090c050c060105010f0f050a031e02040501140f07140f0a0b010503061f0506210114180910020d090c030305090a0902090a09240b0301050906041a01 74
    0x45ea101408110140c160298900364031555031016181d2110308010f0b410b0a0f01a8031550600001000d11208650805900c10201c001407c0c01600c1d20400d80040e4081c004000151090308081000c0c0e440d00c030070329400b07041580d030282e0750303189810300e21101041039220b42c05c1030780030340402402884002003900001c18041249031055410303140742c4401841c900104650202c81260721140144080e040810945034001d0a0f0380c0280d9459500140d01d1060503441e000b0745005140001d803000314506006200c08048003410049136031036030340f0050b04403040040c4c03140382d00c2070b00c500042811035400c240301507000d400400041c024941410100c1c034000c4d03000118100b603807901d40301080c0100b51510440c000540c0a5200c0ba6540d621850402144841c40d0704006505841400185601d44980220714143d6a2010b03001400e110200c41e00400c508180c1100020f000059102142d1254503d000d1030480e20181c13002e1005446039002c00080d60b2107006038100214110640401c1ca620030008020b10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 681983282 1250 681982032 681982061
    0x11b0f080409020313060506010f0e01111f1a1806090a06120303091101021b0f010203040b19021606020a3c0b0a05040201050a111002160201081b0706 66
    0x240390b80e6035651003d83c0c000300d507059a000030080c0090f05000d068029a50b02203803d10740500c0c0c01c1c0c0e6148000d0113441ca0010700d00e04000c6000540868120200481c0b01c00b00382040d405000a5000c84124014004081c0340100d40c04020200f80e04d1420031414030700241c60091110101a40c8000a2142d000c1000b40b040003801c0c2c841d080080c2001d1000700e16a80640250f6010039600c4003405d203c0e81000040ca000d034115070180b6000e00141d0381d1021180f031001e03400c0350112134500c051300040785036000b250484082c96100086400b41070341d03110387d09442c441498080c1c4400301c00040040c180089148980c6000d60070003003d10000410110340540d0b05903100d074201d80b010507500040c100328060034501400b41c40880140e00240724503000f036140e101002102c144818642580001c005004950b040307400d1040a1a42580c40740d0240404090400541c10464461120312024101000005030a9000c036210030301003540c4044442a419010f805005a5890308500d6920030000f000121404100d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 681984532 1250 681983282 681983287
    0x30c020307060c050a02070f120602070611031003170307170a0914012703050a050315031c180b031b0405030d0302090a1502060a0504260a0e011b0f08 66
    0x1010b6200b00d80c50f400044da0741c9501d848502502a1034060183c01c11100c049201a080060f140301688105280e540110003588850345490418050300c40189a0a00000040104003950f440308860b00100c2c1e01030341030281d40840300e03c5031300d003c1d22042d20044000b1340c064406825081e008002286c0050715a41d00145020561305c40c554545031707881070381155944440d460015070924040e45004074080103446080029159005009889542c42070402e0090102c00110544109100c2485c40c0d0701c043c0c01e42e2089007070301802c06e64111340301464202294414980081180068040c0400d4680200d000c0307286444103100380b06074402d01d21818120301d504020220701c03510706006182902c01c450300c026031981d0b2404200b062041c03d1350032103042c10400c244455203903580015126009404020009040e07103a906003040c450207c200c0003482d40e0701c05003030740100250303803401000c2035489503407503981c081500401118140294000c44141d03010580441d0080380c0058295100c6a00c103da2051 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 681985782 1250 681984532 681984547
    0x414130c2309040f0515040605060409050c0d05010f0911031611030d0e010e0c030a031218200102100911060a1b06140c07020603280f050430030c0203 66
    0x201130340d0000b090000c50948440a00c00404d9403c61b0190740780108560a20200f400c08010481340d0065202d10000725441d000800c0218840d1b10440c0c025035a203078003d100b5503071034181a01d400301d050310070003a00301d240110503c8480e254000fa41d004510b5004440021182000212520300b0750009244040c00108881440710350381d446000c005044410001c541c03032407075280c15401c091040c0d20309402900501801c60001c2c1d808140c07030155032500100020b0f10441c06000400b800c00c81c250081c8003600ca0040104890b1900d80040030800b400da08440f121810b925034041a12111f0100800c86100206688018640107001d0000000540342844801d00302080080134210b03918401d80d1503d44e5a1440d000300c07104109412b500c007a00742c005519108240d408103c080c80011b2014599803608407200031144180500c01e1010383c0801418010f004620240e0340c01481d041e00c00715001902c074a40303d081d61421034040702e000400d64014200c00d0901c0c4070260301400641c2e850034210300042120706c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 681987032 1250 681985782 681985789
    0x90c091503151806162102160b0610020706050c01140721060f03110109030209072a0506041209030c0b0403060b01210b040b060414130c2309 62
    0x302c41040c0485a259000c2c00c007481083c61803124141805160b4001004000d1081c0c00b104a6880b81241071806041e0014103112586200070440140141d4a000040b10854050f0b8039249004c82d600a4483c803801b51610b400300700f41a170411030054096013040c0010006a0b0040d00034000ca0713403031a00041075442842c03101c09200703001101c81034049598052680ca40d104c505c2d188090500c40c03200200242410310504005610030351200030200900e8425078a016446000d1810056501900584072418401c070094483d0003c21103940c0c40c0c9040c0c03c800b40030300d8410f00d8600d4403290004d01401403920f480e20380b8000130040303955100920400d04030000000303207840c891030000d0090200c000d03116400c40c41c0240c1665000c0210504100d02912102d10314002c40180003203444070044000b030180f00c6d80000c40c0241038452030f00c0d58802004a0006180e5940801c80b80401c101102c102c1c8000b0080c580c24011034480100a0002840300308060350b02d01c102d40d02d603001c0a507600c0d118a05158200000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 681988282 1250 681987032 681987043
    0xd090f05151213030f030e070302090a0e0f1c090b0702010503040f0f05011b0e03251a04050306341b0f0b0601141210080d0903150203090c091503 64
    0x600b04141c3c1526a1a00741944418400740080c0c843c80c090183d00010304c41565210303240c2c000a0f20a101d4080482d4001d000b6911000032146c182d0300340ca80480950b4070a6464405500f40002c3c641c10305002c0805051003000040142c40ca10200d0604207515130b0011116070300b0042007103410884210713842011036042028220740601c200300114081c920590150f018017040d01c020000e01c1241e203141c5e0100d81d4081105148410280c2c003200401c0f02c0210801e0000d201c0d035005a11001d5110104001c20108034001c0c0306581d01036044071100e840d041c5a0302072000c0ca80e141500010060704444012203c640202c1c00c204e400d519040341c840c0c841c26804181c0c00c08000d01180c40b0046ca0261600700310348500b019a20201c01d003000700c02ca0040c0302003402c1e5803207030f89a10500c4140f42d000141c00502401050070282900c0d8040307502e40020104050081141404265035805041c00600560500390084a00c0796004001900d189075070027081c0140c3c102c3c0940741580d0015400b005c01141e450400c030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 681989532 1250 681988282 681988291
    0xc09040507060306150e1509180103170a02071a250b0906090c010333031506050a0b0304033b10050301051507050d030c020d090f051512 60
    0x3411000d454180040e0031a0029481100a400d41c521840000f5400a6200c0306c00d450603900d298604410403103031103483c491480a540d03c4806031100b545000620a08141600d1107459102d01505000c038941219000310744000c40140c3c8802c4d4103104a01c0359105124100000c1801c46090000000200d00340502e17004411001c61403d44403001171055012095400040040252440e0708006c0178654861070810035403414152a039910803001c49440c2e02d04440240340c0e0505107004800d4041083c00480c0501c0240c48014258034600442c1d02d0a200f14401c403840102090341513490301c03210310b0654000070001d0b800e012010750f4802c00e00f0001901c01050769015090412000142d0b46502c00112400c0401c2d4080c0960901c00003440fa0004112815100300310380c8040d00e00522a0641001e01c02c0500c000d002d8094070704020b5105402d034101207681e9009800341c9030b2007694134804070b500100700e2242103410f0303042075420816818101e0b00e01c1e4105001420f07951a01c01070180c0c0b907080c1c0b030f010f65 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 681990782 1250 681989532 681989543
    0x10b07050d08011a0c0c0a0b1b06070c032604080a03060902040e13020a1e06080732070204090c0501030b06041a0a0e130615020111030109020307020c0904 68
    0x52110410009020311808402a03041044580d41003c40001201c8883c1d0110404000b00198a0340c0041040040c2149010024400412292100d141d291b190b04608410060500b80c1242c5086e045c001080b10fa108070311b01d50343d481d060345098030110f4004034000b40c0c0607941003100d0110020303041c08001051165010320300d2250340b1106120010228ac06592240c00d240303205201c2401500c0c8240da00c0ca400c481392588501070a903903400064501501c43d40300608100c903211801c00b41d00143ca940e80101ca0322a100c1440541da001e2064030f10300c1110880c403815520107180765108040d4481000034851106003c44d082241700c0c0d01103011542c18500c280c0d0042000c01c020000c541e858010031880e00300c00d90700b203801d00b4507068404907400328010070416800c0010891200580c0700d8803400c544014014170006414803400c100b00020001c0e4002d40c0c2a00c0c81c50000d007076401c1e005010b030645400d660040307546142c0ca0300c07800d24000d420242c60741d02140140354002280d07945081c640390149004a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 681992032 1250 681990782 681990787
    0x303110714070614040b090d050102040b04031109011a0904051b040b042103020d0e03120d09020307050118260f100e0109080a081008010204090e12030f0112030c0b010b 74
    0x5011808139041c0c80c24640030800007481589400d00607181d440200341d600c0d0711028004e01d00103019019a030132450005030082000002c3c41400014441c03000e000391140c0d1080c2c0d885811003905440d000700320429600d0200404000d80c10103a000551003601c80400104001031942c1566a41d8004d6005440709240400c042c440c481c0d590416690b015a00030540f104004580d40181d03c3c1e40b80e0381e0180c0d01340402e4540c0454161811f0041140603039034214820b0303483c0150882c040041150307210607802442600404a05540503020f0b076403011040c00c0001044510b080350352066881034030600d8580103001d014000074000304000264400303001c040138000244181c4800400c840c00e240b07100c0c41d0740c4c1c18194a1008901407004940791001340b1300e8051a2982c4d000d01520118007141d01214080d03100050000d5030074107540c0028944503002c810384185600c0840b440d0194001a15403525030001c1c1707001013202d040782e0420740743d08500c241403a80006265454950b50f4041c241d01413181c90200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 681993282 1250 681992032 681992039
    0x80307120f0204081b030d0f082806080105070e0604140109120605010302100906170c1e2101030b010e2d0103031214060114040906030c050f090108030304030311071407 74
    0x45e418681503c42090300200103241c041e981c0201382c80c000140010620051b080442c3c09096065480101600a007143d042d10125a00c041b00c010b051034030070f42c42c05510302000304844900c9040b0985925400410340344c02c01e4100381100003509821980b04c0e040c417107114030000310224000540e0b04420300a081c00105c0c1e40c598010312040d1407030300b100300040115804050110ae500a5034008055059601e0740ba1141e895800b0101540300c2d0324404010056004283c032100140080100781c0304a0350300b05240440c00c0c03420710f40038a14003030000030b04107034084005101559400c240280e0006011600307041321503c4d42c6800c81841400d078030f03260503039240340014000d150300301c13490924000d9a01c108000d40420300140500c540380c050419410000918043c20309040d42c401a2009050410020403030280d0368035208a044480e840741070b000e426201d940600503e0b103400030074100c41221028505e580d40c0d0380d804a000f0500da07002210400801d010540205a400e0601e601d200200c00041c0585400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 681994532 1250 681993282 681993313
    0xa020307030b04110105030c0f0901091d0405010b0d080d020703050f0c0c010f05030606030a0903050d0e100e010603020a0303030b130203010e09060604050106020706450909080307120f020408 84
    0x4d0ba4810b10b041c09010002e0003030380c00141f0708903001c0c8205210a5074480c40c0c1540100c4613682c00d9440b04005092081ea202401f03030800340254000e07032290b0002c00c458201142031140d400c00749030001e06494428010f00300c3e030f0246600104132413413103890018545520802816040d070070119003511103602890b0024a55608280700b0700000000703090150070742c50108005881c0c1e110003410029240e4444000604043c010ba080d109004224402030040c00702522055580340b00c2c41802181c401c3c101558000744007418401c2e881070340c2c5c01410400266045031416000750070301041c19500408040305081001c160303840958041c0203558426001420b20700b041e107140c040c0251955106a03d4100100b01103600007441d407084690341c0c01c25504049a14a44142d07414401c092a05655901c1e5070055201000940c3c40100790030404450741c40540750160141203a40d00c0100600203036040021400441c021000e035020342c52942c10100d0245280d2031000d0690b081a844094164000c001000507040b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 681995782 1250 681994532 681994553
    0x3090e01050105030c03130201110607020109061a0d0803091006060c020918072709050a050f01050126030c0a0606231003020708040e0108340302060c0a020307030b04 73
    0x309280c0f050543c1000840544c00d0300c0f000e02040c103860a17865200c0210790040b0002d90551490f1020799605280041020380606007081007220000d00c0c006400ca0032413503a0710f0580c1c09200c047c00d40500380286555034085030b4000387c0035008034031a20480d05d075168443e010311000b8110555900d8181c001901c10b2101e0740c0000703085000902c0704030042044511002032102c01321600030030010003407603109140301c20486003902c01c0080181040c0c00f07003051003000124800701600c40c10843d64510681d059080c201d80080c000c540100e401e0126421080342481400000700e500c09095034501000b0b510400d02d403072101c1c81c00f1100d550300c1d040100700900b40307071b50704ce40c60050403540549410b11030300018400d8285207024078185580810f003001403000c0c2405a40261481304080749032940c5030b1440c50358441003c90f84180300001c0032000d0380104d40007400201c0e02e0100c2e498034402d00e400e540c02c002c07864000394491030140c42213440030000359804014100055000d00803089a40c201400c20400d181d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 681997032 1250 681995782 681995789
    0x8070204360c12150b0a0506030405010912050a02030406030c0e1f0e030a0c0b071109010f0312050405011706030322090b180a1a090c0d0b040b010c0f140a03090e01 72
    0x1050441440003080b55a60043d0301c460980c240003906044e00c0c0d000907011b48103900001d41040e00407081004110341540b100c40024001c6c2c1d05003901000b01441241d080c8604403541c401a0000c0c40300700b00d158025040030000404030f080080b041068000410b400104940204400300d5141000301e014075000580c00492103001d4000e824429401c0e1074071581c08103580b041000f10034000408500340660407281d4a44408014540c52017569a9001145000f010740001e80318154819890304119000d10103c4080307801c10385505000c0081c2d005e154507580c400510958050004208220100054441001902c0000c1200c13580c0c0e14101410002100c5181d90754900884000b810254000c00c1c02c0500703944100c1040f404240480d803c0000728048100645c9a0342100005c01402107400b0f01d8800b808468004123802c005804408080000f6034100c2513a0a01203000701c3d1441c80482c0740c01544041c40342c06004110f14280c05210054900300312404240c000a21450050040c1e011016029005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 681998282 1250 681997032 681997049
    0x1e0b031f152001110a11010506010801230112021b16030309050d0c030b0c0702120604080307110c0306091e010b0306060d0302010f0609020c07050105030408070204360c 74
    0x221142400c060030039525a0400060081d0b088001008100d007504042d810700412101c00d51998500f0340040c110400c3d07044018060b500f000e0004025510444c3c06604079448001002e5407001016011904a105101207034100050310b01000e207592020700007051420600078410366a9444219401d0410030603d00031402c0f05039418041012941c000700c0b0f80c0c1038030000c4480c840c0603507891034548240100c43e8001425490f0342010003042c00140ca0207040218001d40b1040302e01900f541c016a281d0008540080c104001440818501d1b03200b090b80d010500451f030b08807100b1290990000b8602102128444841c3e07100c0205000450842c20b6140300290900d0002c0c070503c0025000a501d5180c000c2500d07000741c0c03404400c1000d05200750402d002030102928100009600d40101a004c1d51100e85690104d114103035001550794410021039105035040481541001215800c00000c1c11194640e1000750100c0a180038440c3c04550b40032034600740c0e01d040d81200d052031345803860142c5259480100b4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 681999532 1250 681998282 681998309
    0x40f0503300d06091b0201090c0b18030a0f02040b01230f0d020c010f0c050403170c0f0f0303150904080d0c050409060803041805010f1e0b031f 63
    0xc41c0c14400d21000100d41c108111282204900c0d2050141c60180030001ca011504000c0c00154003080c990040000211100d000a100507070200168282c0f200d0150007452690000810400130603410003404941400420400354411800c00007440d040c41c0c04000e4641d1081e0108060851410740310b00c0390511020700b051640000c40038580e504081c140e43e0000900c1c200040d07002c036000007850882d0703040309060004545644040300c04c42c1c020541d01c2071140c01036191a0000840034091010354040742d03403049411540b01095580d4200310b03000114240e0940c4900401c0407441d000500c4005010016500203640381d240007648011101300b200f0707059010710040803d00020a800900700d82e1003500d10400404d669034210f0048403d84100e9101141e2645000e0011450110100007001210400109050a220440340c01022140288210f00d030120401100f080040d60344c0c40300c030810886119a8a001aa8482c1d854105a0040307413500154681540707c1190075006292010140c8044035501c007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 682000782 1250 681999532 681999553
    0x110406021f11211005060a0f0c020d12020c0108150607080904020423180a0203310c1e030f03110d12050a0603080d15050d0305040303110c030a0204020307020309090c040f0503 77
    0x100781f8412000ca07802045907044240e100680244030205000d54040d100070700c3c0c12214104110a074070440d001e0f800500a041c1150590f610501c0c0a1303006250902940070b05030034840401c07495900041c400ca641a41c20300020120703039281e2004e04000c0c002100340c2d01103940c50001c0003070104200f140c1140311390316a01070380915044000313200364024400880107a883e00d400144185241c0030741c1c2401410b005080b000303a103c0c4101d03118182403620407034840c05591b0300d40003d1051149045002002e50440315410404203485c80480c4200700e01a040c5180e1101c44107071201d0900c000002c42d0305c0811030700501e60124143e41d00c05e1981c04043d15104106483c04c40c3d40f60302891165850303010b1a5512284181e9000c07481210b46030080000901d80700640e060303464040c082d50880d20094004c00e2500c2d022031b501c4403011a160a800000a014080002e1240c3c2013200a40014142100710300c4284040c0303905407a0781e44180d008803000b450310358490303182200c0e0054661007604400d0098011040a8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 682002032 1250 682000782 682000789
    0x5010b120109020a120c0e0a08011d0106050306040201081009020d05070e010201050f040818040911010e0a0b0301150e120a06200931060306110406021f11211005 71
    0x4a010162100c170200e80a0001d54007140d109100b640201d034041d69510b00001d08090540c08501c18000310302c10b05074041c007100d0700d8900700c0e407142c45403641540049000038011362040140e1580510b541c1c550180341030321400e4413030498000201807000c0c0381d612070034408415003006000581d40d500348000e000798503240c82041c0d4005e20140c40148107000104000010108018200e0b4485002070410420184103045c04200002000030450100380d140c180303501d06013021541c000070b42d034003105a81e180d40d02c0c00c4c1141c6402c1e500c1c9403d600c1002000144000b9540d944555450350f44e491070000d180c1d40c040c6007084401c0312104001d0600e0304459490b80381c84016280142c0da80ca450446124050030f910072040d07140404419800c207800c248400c00b10b0310381d40b1154022002c0d0b034081c0a0030010302041442c016000d02ca180900c070056404851a0206c608805001400c400002c52021580441c9000220440d800040880d240e0320804005060b6074090341c0c40c1e09501c0406802c1d55020709180c100031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 682003282 1250 682002032 682002047
    0x12100c1e230733180b01080a17031003120c06050a151710060b0d0e06010303051602031c120e0d0c0b0723030f070e010f1b0605010b120109020a 63
    0x865160303560f00c0f0040100031000d0420112a546822000d000c0d01c800c541000a000aa010f802c070382d0500100008140361700700040030756800303900c0040192040d04001000070150001080380581c0006004084001a04202845039940c06521142000390709464010103442008045016151070700c0000c1c00744103080c0c3da404049481e0880c1b0050301440c902c1d00e00d8141f0200e9804001035508280000070380c4041e000c002d242c8500c2c0c000e41085050509a404c5444420030310014000410521540216114020104860300d10013803c40b04112030040082d078002807003c884001050000c03370450200d1115015440c3c2c4000b40340d000c5c3c100c40380c8038800940032980b5a4030151542c1800ca00240c04180140e11504040c0c00444030074000300b0900e42400419407040303c0000c8681605404288685c1c02504101d0301110161604001c030300e0450000c54902d0461031084904c0c0c6103c00241c0080341e058401d1078040e1400f01e40700c07551125240301e109202078040e072103502c40c0d0307104026850200e80d00449 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 682004532 1250 682003282 682003313
    0xb060d020a1a04030c06090812120402010e0f1003020d0c0c08032a0c07030309090b0d061109180f070c050709020901030609140f0612100c1e2307 64
    0x141d0403614984102c50007401c0c011504010005c0c008200c0c041a00c0303420140761001c0b03c1465003102e01d40000c40401d0b68103402060340d20040c00030800302190040d0b01461800603081000380019801a4420000a680007200c84209010950025040c01c56003000c1c01008241d4150342031450a41c0c2d150358500f001484002d014280c4c15482070001400118901607040e28854842003241c2c50308600c8900c40e45a1035140b000b1400704c3c105000000310000c01d801002c20581000308581c600c00403c0c1c407184042c00b6480603c5141e03590804c1092116600c110711044401c4001040001d24a0a03900d08490244082d001e9028842025110310015200143c2401a46c2c40590056110703815000162301900c0a03030000d0420a0034260403483c080322800c480c0c2d206040201c40d282c01d40c0c03200c1d802d00c4940c05901820b0201070f0001980c0c00c0b4450016001045081441e182160400d100100040b4503404944884000103c00450300003241385c0000070212910b8a01c0205032600e050f550301e1846101c0c0c1c41c070307 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 682005782 1250 682004532 682004549
    0x17011401050607140a0308010e0a06050907030905121b21160507050a060c1109060a120c090203010305030d0f05060109150e03010203100608010f050f090a06210b060d020a 75
    0x1214000c001134408080b40405180040380c601c86294900500401d44c01d000b00501510351200085c2a14124003440e0300303c1d1000341142d00030783c84003001280948148402079a0343d2040c0b110340156520f54100814645040c04038000c944032240c02c0440c1080c81c801c219240078021341c1b42412075011110212001020030700100c000c00d5003e49009402d228242c0d210320350000d058500001e80580003404540319620070140340c00c40c9103040040101c0000203441040c0c00100815060080c650710401d001b80c0180101007103000c0d40c0d9546c02d01f100340d174400d0300300711800d4002003403171041c0344064001c854258020080600040c81d00c000000d0040c0f12510440303041c00044281d60321002d00403410050000304c007400039503032840c24101e070354400d012501c00c83c40010700d003000004800364903200c80d60586200a268016619850041105240025100ca1103050307890000040b640b4010ba0712292805501aa0b40800c8000c1d0070200c80001004140e1802501607900c2400181d8540f03a196043c1c4000351b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 682007032 1250 682005782 682005787
    0x4090f11031005091008010c120c09060e01052d04081603030c23011515020f060406050603071e1505090a05010819140612030a05040e07050705100501170114010506 72
    0x71505100c81945e26030250ba200d52130085c181e88041c2d4400c1038545074020b008014006104c0c0e4000445607011a84101700000d041508201b00641c807410044c80354600d082c024010529552f1050400d140002e0034180124400103020000444c0600441c2d22098000b00c60b40540b529646000e006000e080400606110020202d1000d0030b406204400d03500700309030f008200301e4105880f02e4419130364a0280070201070070a0303000411a403000402e00c0356010188040c00403621141c0d9030b68040c01c005484164580581d0340d005c01d0f18040c00034074154842120380b44600391031a10070500300d20350900c2804403c112080040c11007036114405804200d544c00c0c030b0b000289980e8080060341c0a041410442c400505000c400031204c1c80c04084140507250485090040e04610142c269480c41940c0000d400b0460502c0304024246c3c407060f48551182c0907050141c900f042d584d42c1c06081c20241c0342e28a10300d80d034034001484100c5c03c0072907155411940d180200140e00101d464500d4841051040b140300341c100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 682008282 1250 682007032 682007041
    0x5030d0516060b04060803030406091419140a210915050a080a060b2a0f10090c1701240b221e09050a0203040c181104090f1103100509 59
    0x169440040148408400d4907282c9c14140b07000300181c031075444145c642508403110b50a161001041c0e030070340d20024031850301d410f201079941d16a036901101788100142c003030401d60f1008914039101d011040d45040c000424000c07142a0b02800407103864000104504070303503820804d0240c00a0407074031102c2e91820045111f0703498000da480540380c15005051550008540580c0c2f40761007031a02c61075030307405200e1080420800c1c0c40c0c2c555034100c0c2540b0703226a9400404840b00190700b40d03014a200d54001c90a40090710f031102a100360304e01228200032520b86d941c1c000d20146940d04080640380c040b5282c0c0300d030a1249454039551040c05400f100b140070000310b8050800803e41c2c48030240007000c0c519140074800030121120150040240708241070541000d002418103050b42c42200d2040ea070082c000500345003081c1c020058036100710035000d609070340c80711448020000031000c2c0c4002c10f035149000c03500f070761040d0044003512444014484c9d07030030707040c010712a00c1c0102c2303041c42d41640d2040e030701880079540c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 682009532 1250 682008282 682008289
    0x30e070b0a031a04110708070311030a11010c08090d120207050d1e030501080a03080a090b0f060a0503010e03090d0f120c030908150c0307030b0909060105030d0516060b 74
    0x40c0d4010440c03003800046010049806400240088544103090140380305004184800e48410034812402c9071030820080001410b244044c0c40030380c1c060700e804004007426003113691542d032058100c000418135800c01111410303000d00464850f59034501d48841c443c00c01143c03184e84d441c0350386031800170321001d14038010b04c030b00301681683d01c61900035003140c1180711036080203089058484008045d514808061402450003405064101c03071590006055030025510110384034800541051980364580180c040419141c05c041802802c00d040b0503400c0d410b00380e00700110301c80280d200c5802a4100344980f29004008010b031840000305039002d954002081c40d110f0800c00030014018110fa5412890208440d4002c1e41c0c22110b40c4030b03446400c500350326140c40f940c0e24484030506404c00d000071000a0040002c49000e1604130446090102d45000d0a20001c1d02903881141c1d10348503548201d004009a16042200341540305490400c50300e00751504d401144002130070080074140a0319200b0764121602d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 682010782 1250 682009532 682009543
    0x6080a381206040c0f12081801030209060d0c021e0613031403070f08130b06010c03031b0e15041a22091e180323040b030702010e011b030e 61
    0x10340a009442c0940f60500e0038410221003800340a0305070070344403000706214811040950303003103400150050a0258001c200010800c0c0305628a041640a201990a58075440d019009401e5025404900e41441120081c030b49650300b070b010301e141409105500030fa00004903805c0c3d0002e203110000c4420140c103040c1a80d6110314011244101e5100100300320440d0303442041840840542d40c0d900751a500c61084152803600b900e14003802d40038985000c11002c0d07010b000141000c40c440e090102d1a40e00b5a16429100e0b6008140c28000c58905404035105252800c0c20a049400c2d44013010704107030801c070b41c0d060f280202c02da0b00020017a000464000d01d2016640c9a04182680c03000c05941035101e0310780c20040d1000d024810107007500301605103000302d10383c040e401891040d114900b03580c5085480481d0103040b45130101d0b02044802c40011544900440144040c11200780c90542da8288249e0007800c41c0c103981c8820240da4500f0b20b0f070444215514044c0c2e00809034a15000c80c0c8624030103403660801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 682012032 1250 682010782 682010809
    0x10509040f02070206032d16110c06040f0302090c03090307080d110310060e090c032206050a1401091b050901020c120c040c02060921040f06080a38 65
    0x1140481045001981f0b2810000c41c44012000380e080d1450061100080701810785241d0030380008040900d260074410b4004d10300100700c0b1030894280d880d006011407219881908102440b104004081c01035041c0355000c5508a800311107010328629100003020744a00400500408802c2c00140601a01c41240c12840048a421401c00c0d5a030800c00380c010741255051043c000800c180041641745407603c0c1100c5840352440344d0606145544840c0012020030300800c601900c254809900c2e030100d03e003031084a210b0b12940600003406007081640d2010034105a00420503e801c2c00d14060b812040021070209100e00b60502c82c0e11001c811005030b0800003c0c1000360342000d0040c407020f00c1c650001a603000c1c10328069504101650f900c801c100c0c0c07940780450700b8007090350110300c0c214084c080070204401006200c0c58458242522940032500070b850b44e5102000040154084c0440003201c1e10514140c610394821210490b5801d0311004506c226504100325040007190341d16109803100750350510381 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 682013282 1250 682012032 682012039
    0x271011120a05040b0105010201020901092d08060f160c030804031106040b15010306140f0105120c0c070b0301060e2b08070b0709081f0204051e1e010509040f020702 72
    0x914140078204002c0c80111800d4807130030111400043c4550040c82290009a810307540d441003d8100300024010349540c0348110200c02c2c00d80d1859003800c44446082c4058802c0802600c2d0b0350a10346140000d6110107403480000e941d1200202d80490341061f004180c0d01c1d81070030190426a110b0a082d00c00403040690b2684500030b400400c4200610091214030448404031040818450a0011002c5a00d0ba0042d039040609048030f01031640303080350b0200c88810f4145045803030840c00301031035079003640f05441506006501240c80540350400744108801381220300c000c54155890b0800080c60a00c3c504500c6008502c0c2c841c607e01c02c2c3e140300c002d03219522245c0000b2000303021507151078035003503000381c17030548040500f1408940000d10440f802011510480c00500c0b01b10482c00c03c4614581e801c0360341d60b00c910f03400c010014960300c803d0300745400e026450100c0c051010200090100104038507035800074401455810001c240e8200c0280c1d060000c1c06d590000d40704c0b1407281d0b5203000348103401c2c0c060340c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 682014388 1106 682013282 682013317
    0x61b0f11040216030909051e09011d07050108010f03020d021002010e15010617010e01150203040503031b1009030f08041a040308271011 60
    0x26150040110812180c01400060202c2c0e0041403510300743d80c080c038414418180c2100340c2000071300d11014144010b15000071000328000072131803008001c240010114001560942c45070031302ca00280c00c0c00803062030075400c0343d0b42d60002c1d119140c001007080d0001b19440032141a010200d1340d0140540200c03800c0b40d82000400703046000600e04543d43c8814141352008104501820020440007003a007950510320020020910a007000c5030181c0820010080da0410f08199411940095611003d0111004049041d482640c0c01142d040c0301c041105183d5042c4200007400751145941102d10408004480703800781c49180c080540071460032000142100d004900c80303640705e0704c2904d44e42192040100124100b4038240c4003507002070030032002c00c101c1e03844440041c0c04a000741050b2400d50000100030a6070385008683c4c40e4036042d110000d4500095001c030a43d0b03000c0d0003124250b813 = true := by decide +kernel

theorem cover : BRFrame.Cov 681834532 682014388 := by
  have h0 := BRFrame.cov_init 681834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 681834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 681834532 ≤ n) (h2 : n < 682014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
