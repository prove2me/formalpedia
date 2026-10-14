-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3446
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:41:09.355831+00:00
-- url     : https://prove2.me/submissions/e2213553-19ce-4df2-bded-a185f0d41448

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 619604316 ≤ n < 619784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 619605566 1250 619604316 619604327
    0x40f0905071e140d090c09060e040c1202010207050d052508100207061b0503041703012409030803070e030c0d0b0c0c0f07090f0e07050a060c0302030c01020a0201060609080a03 77
    0x80c0c10609002e100300050801408a2090b80d02c01c0c0c07504c00061144039582d0501c08060a491b000e6072031001c0c00d0400103d0b64400004465000d650703c41070030840380e4685955801200541d06049045008001e00002d09035210f91100b18414002c90251001d9600d80768601c509000710104081131301d1070504100714180003c1114010f11091150169981d58180303021001001098007a02c9001c0700040c2c07411006500c000550b200b14880e08401002140c10000c114450009124150121a1803601c44031040f091300e00d8505160070505050039450f46956841341d40da0070880b0b000c4001480301401368090f107000c000d5000407840c107440071800c013400380c0c03203001c0f028500812444d00500c00060041031184c08200003880301600c401030700c1e5804d88908400e0003030005411411201c0e41400c401400e420804602d41c411a000103007401e20552800c0803e40b0048035460080e815804280700e6141c0d441c0083c00108000d01c1c0540c000030b1030b07030304112000d000c2a050303030811038143e400f25001c10002070b04003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 619606816 1250 619605566 619605617
    0x1020601080615010c050102071b0b0403080a0309032d12020c120306030a050703241803110307020405040f02090709080d2001022205040c12020915040f090507 70
    0x4182d0031040910f01c1e070060301c0b15090303000010308941c03001902c5000d108400100001c003180034103800d00030390743d1580c0b516400d001f030740800340c9a40c904100120009000e40e00060a461081c201880e00c100007484039100b101c035001180d0364100c15030701c0721410250b00000900c48494690345c118245044c041c0b8080d80c4140000046043c8103000000c80c06640e420044c803820a9800801c4070290f81e100e00e070030100190995000d0042810f01401c0c80041c000c14000d0b00850b081100c0351078618401911b0072500a0b1a4022505082c0800c01151000d0b81703c9000e21440756004460f030000c18840c078030500840040090000041001860f820300c2900004200018481104e140c8101101c640b0f140b4451010b41c01c840c038040c298400224128603907200b80500c244070f041101905066540c0d2000d01c420789400d000182c1c00600382807442208803040e41e010304035400c0040e20406940b03072640f2041c1c07590741c01170304102112a00c0c800100701c00d06040c004d06a02240c1ca282104040010f514078000c1140c00307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 619608066 1250 619606816 619606831
    0x20c07050d03020a020a06120f090305070f080f07030c1a040b04080f25061104050a0911040803030f040b06151204031809140c03101205031c020d0b010206010806 71
    0x290007024042c980700300a41c66405400403d090481545da1001610b1002c6818a180009080540340720442d60584902807400d90192200303403030b1031000ea07981c1d4140b0856043c100c50600b401d007c44400b5401c140040c2002d244a0b03120446214140d041400021082e445208030f60303445d800401c0002503e0b01041e41d001a80070000f0b40d180c00c0008003521050055958040f21002c070352007007a80d81102c8081d03034815076004040400640e2890f00c03038030803103100c0e9004403504160480c0c001c01860a142d03024100501414000c1814180c44594440c00c56006a520205107840383c4140001d0140d404100c64000900702e42c0c0c00138501c00044140120700401c040742c80821010800a020b1600079800740c0d818640808016581d2501c80500c40c00510160742e46070f444002c500001003c0e600f91034101d0380556810200ba000240c94025034032040d405102e0102c0d0340e404180005ca680f0104414001d040c582902001b40c0c179003420f19422812100366042c02d41c1198440401000702800108445800000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 619609316 1250 619608066 619608079
    0x41502070e041a0c09040f090b070c0c0b0c07050a08010c08010902030105100c050a12020313060e032e0f0204031e03120c0c0803010e160503010602030909070318110a0603020c0705 79
    0xc41c500110103601417403880c59009401c10030743d48808500307036101101881c410880003c0c02d854134001200c081d4620760b4001c0c020134240105009209204001c1d00e05802500200c80110f604c2c0e05c0030812140301c40d48151980ea4581c80d426640d540c01218240c050701004000f1810f56142000140c2c0101e00c00041d801440750004d185000e00a0620020b80c04642044524000c550400310096980d4081946c01d50000080c4001183c1217103d00c6840e01c0505005009000c090f0072000e02400462118214105c0c0300c0240c1003c902001c1a406403a0031110be0b03140050b11603246040642c000341768042c0e08a04420120704000009411410048a2070046400012458080c040c1596454191036001e000e424004c8000214002c5a0368034900c14240300320ba90511099108083da1607000a000d2036000d44c10174042c6a10a040016400d980b0420300e20b40450081055450038011003038200f030644104142e640240c210382060034400000701942c2c60210f1030104d119400945400c01401014070412 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 619610566 1250 619609316 619609321
    0x13150b070302030901030b040e190b060a060804080306220204050406141e4009120807200f0105092e0b10020307050c0d12051e041502070e041a 63
    0x702c2e640d00080724000402c1c101c407207140c031082000ad2182107070f1008607904481c2000095080c1007002582c412900562900c1e003c4d5100c503030f5040c101e1f81000300f0319600550000c1c1c0c0078000300f12820300c025a400440a006a81718102012f210690304c3d070f078002100d161400b1407d107440d615041c10404c507500c6601c064800c0007064400060b541002d154407180540c106960100003041888604031881c0e04980c0122201c200c100030007820f031244510040d2010118ac440c00744468001d40040fa071011035403030154113404c400c600a00c08003543c4940d1010700d0b4032042004603100c0c0244a055080f5007038800404a021a040c080d4103000c0c0041c054508486d030307050208410110a030800760742c000c0005c04000149614444c025501e03004a00b00741c60511500810404600b0484095212581c10211440c0f9484d079801c0c0598450340301880410010202c0d5002100f01c1102501600141c2851500111054a4540001c0c600080d80e0890f07981c1e20100c3c424000000d034103848000704070025012108859 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 619611816 1250 619610566 619610569
    0xf0b160224040f08010c02030906070302070e0c1b010623030708030a08061504260a0209070302040906060206160e150301080a020414070f110c13150b070302030901030b 74
    0x158002051807046600e400052600c14441018206803410352030031140030369659101c40c0c26101c524180b000503030020080c03c80e481c18400f000341030080c002e004540500341e650400c1700c0c1c80e00044620905120340401c0105c00e41c03d06110301c03800b0350300c6500203101c213034240b0a140c6c903c803d4036503120340540c201c0711068555440c18400040100050300641362581082d81c805031150030200c0d06588030b01020146142a040c0e21025541034070303441c0b580324a109140300302c40c07030807405800385010844c811455010300590ba01c2200d1441900350f80e4000d070f100d51400703240809032481500001c055400400400c0581c00400e40d000d115031415160a28840b003034800804e0003005803003004051a580000007140803080040c1c09106680300343d60802452a4080c5144003403d41919030b10001510061400003062140406151040598040d100c48400000000341251800340007010001d480c1c102440c3d542c02985800f20050a4030040c05150000654009407030f441103c0401741415901c00382040705 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 619613066 1250 619611816 619611829
    0x3080c0a200307020a21020d2d050c0d020102101a03031b0d0504030b04120311070b040c120203030d2004180c11030412050a06051602070f0b1602 64
    0x584200010075185241c00740724040d201d0348400703420380c0a02900c030000074894150555200320440c4205100e00b84000300e900704902408001c005035000d034111030303602c001c60b803a0006035100741d000c20402078900700c810324066040803801c009551140400a05060150b60080703640e0a1500e07050000007402c0d40c60410700e0032100071800001d0340610000c10b0360034000b44450200400c00d03641c842110b4005185a000b00c50320712450200402079060341c0c01140c0041c100da030b5400802e803818100421b461303895410b040d03943d40044209032a00096031050000b488510441d5070044c20420048418100e01074001c260790f88903002807903154968403004880c1503e00300940000c100d0081100943d9540d84401240c4610510080c0d003180c1d03490205c101c05464082d2049007010303d2190051410140f1700305510361300e804024015203003030040705036120028003503119092003844aa414641c903e5203d10b4005c1c82c4c00030039049140b036001c04090a00c0051040425146424508100c0790742000b03003480803801c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 619614316 1250 619613066 619613087
    0x3190b120304050f0310060b040e0a051501050d2424020a0f030e100507030e09060a05010c0201090b0c0604120c05031e13090509120f031522060501030506040903080c0a 74
    0xc0a140440210302045504020000c407440c50400324401c0d00c500c0bc2c032074101c68083e81c412041030358a44404400c0e500030703000f600c130b9000c0300c40700003d18940c014060b50649141e224180204200580144200c1c01c5400c0208003a14104552190030b045512011b59039400414003d082c0710510410351741007500c680da0002d000301d000384c58010640111302c4086e1064201c10021000300300120848041400c2481c45507200e10030003408580614907000043d1005030030044180e04200c80e03200007081c0d1400c024018403820030380c48002d0a2501c0c140c1030050100c0f6946038203008003c51381b0702c8000802c0002090f01c0c7e41c0d0780650000b030045480600f404800e8030501030b051094141c2900006607844041d03000b148500b80300d03415207240c030a00007201c2c0d016208035102d880d032021090010400d124000080108813200103446041c0d101d044803581c903510b90107440001c4509032034860a00c05541d01d40147e6800000580741400514226980507140d000001c1443e8000c03c00400c0700d00c82c05118149466 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 619615566 1250 619614316 619614343
    0x160507051216080403050c10110a03050c01060909050706031103040f06020f0705010c0314060d0203030403120c051902150c03030f061c0f0b100b041502030f03190b120304050f03 78
    0x1944e40796070307140c8640c41d000114451441507140810f840c00e154041c04150500301186c80c0501480303440c558080d9400d800118000b01ca031741d070f1a20041440001d034410400cac1315000784010441030345404002801d5501044040780454014801c1c040090184d0540506250b030282d809a1580f907034544083c0c483c010310344081c04540c200056550341940580c0f104c200f01c0301c0070f02c41c03101e55903914080c081c0415001100a4040d441044100003080c54070f0512440300e586071518080369000c54845526002180c91940c5082030321108540461804203d201094400f02607068144030b80c0190aa8030303070000416900100c5e0a40000404982d124401440000820341a114007000c940c1452902c00c0d841001c2211844400000305803182d80451f800c100b151800f4081500d020f0801c01c03400e0f010b0848021030f1041d48828040101e4035441080554818031008a0342d4135544a2a5100720545541103480c44c091108202544205407000c001c41e01940d80075104180011190404a0314110f014031208 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 619616816 1250 619615566 619615583
    0x15060f14030111042d06050a26010f0612060f05040b010309020a09022a030717070203060c030a150806010b1e0c01020a0f0306080c090408120c03160507051216 70
    0x311324081420804021240c0311170340c007108400c0f8a43c5c0f05940708420301980b8081742c420f110f0106241c1c03040079034030303403102d14001c405d940740c002e85810400c3c060302a0450201014917000034000c42d40d010110240322a0001001d1060510305056103840310114001e00e80503a85a5094461590180d0800038445502a0079000c4ca1640c4000d0700000b07410603908010340b11000c030700c80f080000e1440d000740a031803e41d001951501c242c50b912290748042c0c04440701843c50b400d00c102c002694080c07242ca8400e45054100d80d42d01d2406440c1c0a040302c10f19102d88030301d0901600148150f54002032998151802c0c020502e59030f90b42c51111500c0000c02002840062a0000d81c1825500040d0087c000011a030b40303540ca0080d80c000000d87c02d0301e205004900c803d50009840c4a020715050401e01d0300140038070300700c528060800c4d00d0350164902c11030303c50b200e150b800418000315182c0d840e103069030107859141546c10300c0c0c2c44d580c07699100c0058a00c4000d4202000c680035071342c00e140c0d900019251b903001c00207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 619618066 1250 619616816 619616819
    0xc0f020c01080a0e191101020c0103020909011e031b0608180706050c0304051302070b13150203062215080d0512070207050604090609290405090c0d080715060f1403011104 75
    0x901c0c80382034000c1b180340140220201c05503194020300a840c0d07404ea0007400000280c1c2054400100d101c100c48806441000111000001c6076420142c04106d1520154031203007503080c01805084050042c00f5039a040c1103000c03481d50f2a500124641007a03d039240340850340d40303035000d10091075405160450f5501802400182000210740c0e401402154810003090801346e4070040c030322038000b0480c0000703025028041010704101c0c80550046500074402002007009882c049602c10300c00e18011040c2014030b681e034026929455100e2001c0008040c03903070050070804c1402e0001071260140301d40411050f01080f01084809000f0301c07080001d40b01c0a0005a2196a1035411074060b00e0fa80c41000c0126180c01c58000030312802840901110f20304400d900c5910240100f40001000c000306029440c0c09030f80540e030003507036844011205880c0240d0141c1d8a444080c100441442c94010720310445510b02181003009201058240d0200c401c8125088010044000400c0c05041d110340c50314612803000a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 619619316 1250 619618066 619618073
    0x305190323190528060f0308070b0108030a02100b120303040803070905010302040f1401030f0203090706141801110a0501050c040312080402030c13020408010c02010c0f020c01080a0e19 81
    0x30a1003100c0000540c181c880080340d840049490a45800c0d040b0083c000324100c030b107220741d040c48a04c4007207050001031103551800c0300030007082c00781c10485142e2000030b00c11003440090f40c0c44074090513052000d585045003211019540300c2c08103004422590321140951010742d40e40000a50f1a03c56a0a60b9900d00d010b10304200b065004a07055004500000300c0495203511901c29203060781c842402240055052600e2140240c121140c01e904041d180d0300c418590002e6400554050245a00100b085905000c000b0300050014070601d0340c190b1042c8419600007401382c800413413001e02801c01031244200784000314200341d05d4013009001582810103001400303d000c0014000ca0340038030640700b041110800c0c01c68010780e0544010394990b100410a024a1800450009183d44440c0005180c079580d040c68a0070344050094901c00b60355601c03503c18038140c018000a000341c100380301910100c810100080c2241c44040e102d10110740e43c410008182c2c2c001000343c16000302c19604c070300c0d201881038039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 619620566 1250 619619316 619619381
    0x50f120a11090714072414010504060504020903060105150c06010806041103011a06030901022226060f040f1a06010f020706080408070c18050906060105040303051903 73
    0x1202c1c011151440090a444d1041401000d000e03d0029090328180e03654840c42100d8400e464012480c9022415540c1c1700b0b40742e4495a190802c8180340e202c0310b5898001080105c0d80030703a014500807401002144142d80c0c0206038541522012524520008661440c50795140102d04441a40348100c0c0d0004c940c8460001c1c5061085118248695101140c031003458203951914465180000708440095105d01e0108091540407101034001410310326290010300000e01400380e00030350700034284405c1c86a0035100148480e00300c02c1da901d4082418001e00c07580d0b501e0f07600411100c1e42c40c885002140410180700c10300c89801d45c0103004030b0031101d030000c040002ca0605460640c0450402c0203d04259030020070800101c0303403252903892180e40e03527407030740311895124000484003600c0003540407072144940200c408280001010014031458210300280c90554060080c0d41480010320007040041d50080c12111010b20506c0e0501014500483c00c0d00542207401fa1400300e448915442d882c40e10015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 619621816 1250 619620566 619620593
    0x607060e0c060c0a140c060d0501051314150114030103060b04240302150d0204080304080115030b0a180507120c050a141216031101110d0801050f120a 66
    0x40303081c0c52980640c9020410144500825075441d40c100c2240480842d4045903800d00140c10181911000d060580c0054415845111004a025501c00040c040750620360040f0004043c0c0f01810070040d034054503800c0303404400402d008062440b04003070380200e0344251807001034080c0258003240c1b696100d02d000409805007620b4075003d20302e030030b020410109030040030090050900001081e41e41c1143c003402410110b580709044043c2081240100d19082840103100400001002d50f07240d0b400c0c407498509590910440e0480ca03c5604030500216503009200c90b0883c40d10310001030701501000c01c80000311124a400340c05409a02c6000a020a0b11071900c1303041c5110721040c4000b2a100c3c0100944181c2030701441c10307207111000020b0841e090030301000c41603c00700c0003150449041c0c04105641404190400c07106220420b400500c2542c01180010703501d0a80005400c0c05c25823030400602c000c90500c0f441d48180e0b00130414400c07948580b00c034421609052400c1d100952128100301d02c03003080c1c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 619623066 1250 619621816 619621841
    0xc0305041a0103080f071410060807060f050412061803050d110f030609180106031505010902120c09060c030f041410210e03070309061407020a0905090309060706 71
    0x3181c0e0426410803408919810b036940100454240380c0200115004c540102d88101c98410421254488411042200300c01c0506009008140c04c1c1c00c1500e000c2c28510150b01036000d00c0f1038180c3e074540e055082815074013a07982c2c01003c90302c0030752281400c9001e420011f400c0381c1400f024030780d810145031303000004040c0541c1e80382003442101c6400141d1203071032080c8500e506a180040c40031860340c1c030b850b80060390403c290780c0241b4550388420610908450b800c0d07101f15001011000100b03c441780c0c0303003d903038014403c44808504200420f410300c8864a0300610b80d407890700340040c404180f076407100e0a030713610540c0560452343c42e5513600864008903030290040081c1c9505030702d50300e0024a0301500342c41403130072076503101c948518000260600c4541d050245080607a140c0c5061000c007102000a014854020760320401e1451820340d020b484491840409203941100b0440b000c05030311281d00880c1114412200021183d4400075518110701580c0c1c9800d500c900700107184c806201c0180c10081d820b000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 619624316 1250 619623066 619623083
    0x40b2805071803030207030b0709050310060501261f1d040c080703021302030a11030a0506131a1504050d1a01060e0d0809031509010f11090109030b07120c030504 71
    0x4a42c00c0c0030b0040341c8075100c01801a0f01c1040240009540b03100c1481d049445801c0440740d1544400009060001034810620001ea556400f00495a400000d00c49e03045070801411440000001081e030085038018150381406d0f03003183d04c01c84910030500060008190003c4401d000842a1118510029095805403104009010b01062602021600d48100c0e5070082000642c08110103c92001c1e4200034903000000741da070401950140030b210000d5100b9901c1c1400099185000020850000003240c1b80054032444c1071803110451034883e0030103406140403901d82000490f480060b030f03a244203a8008903006414212060200110250500c28071040140e40d00410307a2180f070126409041c0c11019680211403c0e9100c012803040001492660001340c00d0f5521800c0c42c000d0800303202030030703555510169507801030410602072511072940ba18081f1800d0034a001460b40000f8914a56400064030760301c1124041294540155203510f4141e6104105004140550313102034014041160203841004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 619625566 1250 619624316 619624337
    0x30209152817120910050d0218130e071e031a180c0901052b0803160c080d020307020f0604030305010e070f02070311030a0b040830040b280507 63
    0xc408200c04540700004440d050130070900c8020000c050440c2c90341c003414000200229400c19045000610010b0100f030080740f207800714581805049026403040600b45880c1a013441c04200c004140c0a0803102041806c1c0380c01000c0001301c250040d9280c1c0020310080c43c2c817040035070708854209000d100ba082e5105000e406a00c5000147e203510305c00b410070354403401e2a0010b10051034030f00b521840410b40c41d801030740c0030354081815808610100341c0c1075404050100800c54007000310307441c1030941c6401d031403c0401003000703540300e0400d0301071418030a00d040d4011001031040c8e4030070044504220821002c9070320324205428050300400081c0101201c0141000c00109650300904014035115103650051407101d06d90303203540d0305203034248440e10361500404038510f022a103101101ea008600410390030740ea40030004018103291804074011042d480c0c640d400594108800140c050740f00b038001e52141c0300c56844081e025080340140c81c9107814000080020303014116190321503441007071a03845992014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 619626816 1250 619625566 619625609
    0x10080114310201051b030a120f020a0203031314031b3d0e1212060405012103020304051c260a0e241806040302091528 52
    0x741110507800002038512915040154400c000030316144841081454100c2d81c01d8803443e0039030340107507140400541041100c41c1856070511a00c0d20b40c40b00c402017140b0b050142c100103912400300410306e500d100c4021703c001060110841e03810b8550111402940c4e540e01605210180b4440e030310341c50b0500ca11400701310004c40c88000600b00c15078060481c0c1100c0c0182c600e040120300300b05201d81c001280e81c441010301680342040010082c420640c2c1c401940703890304030300c0b01044100c000744641e200314141401081541c191851006540040c0d0900f00071070a041c1c1000da203548140e511a0b0307001319074030426018090440c51461303561846001181078513240c2d000070741d035214030380c140e41240c5210410040f41780301e004030030303000c2d4000026100c11074030b10004902c645941041b2140b5560944d0000760800703101d2200500c0c145c6c0003400c50f0040d0900e4115004652038400062030f510b46421142c14210f000d82d58054031002e0303d81918609c512360740c240160300340c400c032080c86000714151070300004d030800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 619628066 1250 619626816 619626871
    0x70b010e010e012301030e2d06150118050a1d0603150619030c0605030f010f0305030a14070b0411100305090a060506191d070c02150310080114 63
    0x100ca0040e010444c1a149424100b501035a402c6403160500d96511003441002e0303070910400c440b011f807030544112424105c0c51200c5041ca401043c030300b06170b000001005004416610b441c00c181400386071201d800c2c0140346070000038803040e03085140c3c09540d03000001108041d40e40303465003007100c401c2c0c8021103071240414155501034680342200d003001c03410f00040c098101491101c9220040655040d5119a00d03120380d1550802030b000000020000000c02c03144205044000780101143d5414682ea14075545035141c0382c3c05640114010486407040c0d001d061000e040c16a40c06903041410100641800d151003c603400310004080c0c081c1004a40310b00c1003900902c15a846000c090014040d035158070343e10b80300100710041c4034507801b40c0c041d0783c1038251601002ca80006020542703004614500784102c01e00c500b61000b4050010068646840b0340140c0300c54007004401c80c0d1402c4415140e848004010002c1c1000f0380041d500c0e907180170031000440090311181c0b070043d0786043e9061507809021800380da1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 619629316 1250 619628066 619628069
    0xc070c060e0901060e03071206050402040c110606040203040c080d0216061704060906020c06090d080f04030f18150504050a0b030606190302120a0b090c03100b0d11070b010e010e01 79
    0x1031020b1060010481c442c056601c0541c610f400030705a41086449000c1c01420340011803042d60400e44d140104000c5050501c00c41003d440705051502d02c1b258014004c5e07a440400400c1b5500454001c00460100400984258094004079064800e035818040009542e6403450810112500008200080302390085090b41c6403031a001c103181380c55650b2600d8180140c02d80c18800c80f0075690030400c428180c6410302225004010ba400a004940c04203007000304444005004c1401051a0000780b10009402402c408109649410089940b4110159001d2a64082d9000880c40c41c3d41c10341101003580d0142c001d0003502e1088410300301c0719454500241041c00120f50031034014800300182c00d80c0d032000c152400120100c13460f016150950001d8801000c00013600c0c20030615071282c4501ca240c0c9460b4402961000042803800c0c15450000e81c0f80364400001e11495000304c0c000680e0103410b080039007010582030070390510507989003600d10740004501000d21845803c903c3da0000170442c00041c446090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 619630566 1250 619629316 619629319
    0x18100c081b031b070f05030a11070905061807020a0203030c010c110a1e06020d0f06170105070516050f070b0a090f030506240415050f0303030417070c0e0c070c060e 72
    0x442c405403d071040b50003640084015681801700190010000ea01000181034041c1da0317a07070f9481324080308260b00385000718940020f03101d64180410010280c03141020000007000d094080c07a01c641740c6000903403c1190a040c0a03401d400300082d201081b141c15000740c01c00c141c0c540d450801c1c810103000e00e2601c918002400508424280da440004100303180f0b44440914042c2d24018a01186080b91000319403054650001c800d484000c1081882d020f8070a10151600ba007000340710a15001000900318450000500b111162146008041c00002c0180d10401402041116215500c07406480800c1d008484035100080320a400032400c4002d0407050000c80380d105c07004000585407440d8130000c0c2e00000c000b02442010f031030350000da10351751402110070340307402c02414103142810039080c80260f803141801607001313620400910000480e102c44d00b600341100c0700c8a0b2030b181e0405103800c04400145030f000421160010741030020501c1e0500090620038803440d402d14030342c0d41e10481130b60b1303040c00b811400b03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 619631816 1250 619630566 619630591
    0x1e061308010c26060402030c0d0e070303110105040c0e1504090602030f011e0603020f1606062607030609020301090c151e080604050702070f080109151418100c081b03 73
    0x611340c0c1010f0700510342000741300300d884c3d081c03030341003014407040700c1c080202d40c511940901010010f15820240070069428004000e00c560702d07058403203500324000d1b0b03c00e200385e41c0342050000e103155904401c0030800220041c000e102a070703407504204c0c011303420585100100900600000510204200600004e070343c0c0600c000c00c3c05890086e0a81c02504045030f032b05180c1d0300401804581ca5201803210507903a1062320002810360921103107100340307a40302082200c0480c0060703050170b1340307400012140202c039803208010402c0071755880070038050801131500900c0c0c0c26442d800484d45c0c1e92840c8802c14203c10700da88500b8480c0c0902c011746590003500c802000414444000f0500e50700345600202d5220b4014011540090760341c500c0c04410a035582c2c0200c8103650742e02c2610007001414540e1040110004006000f06904241d510b024040003426007180e40010010080a6901c184440c2403032411a101c108100c0c201c404c006444003800300d45080801c3c6001d00c2c00c5036a405041c055030f000e01c81001d413a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 619633066 1250 619631816 619631821
    0xf04060810020a0207170105040302010c0f3908040e0705130528080706030f061d0a090203030307030b0f0108040c1208070507090b0a0f051e061308010c26 68
    0x1e42000758002c2c0240e40460141200c0400e00d402c0d10180c0054641c1e0300c600008141c03405040007801c440040b4021b404002c1c441c107484040c0d176448a01e070b4498103241d12601000c09494800702c0c0701c41c400d48400f455001d04141d03421301031100e104017a001b2280c82100a6181d9036401504030750310f225104600c444030300c05010911290420900e4441c4202c54440f08100030750b03d00c072401905101c02c4d48048c1d101c0d0f11400d030502009500d070007201d8000c40074840901071141864810507481c0d141062103042040820000342c40e144064002c10000c0b03401800740da5a1303041155008020341944038845024219501c104080355111707581c0c9501c03403500420307441d00c400d081500c6e124600b80561000e541200e400d2005c440810b2061228200811400c2d00000e081d080090030301500b080b090b80056a80311400c0b000f00840d45540400c2d4242008401d0807509004015000540070300540e51105d04075424000045100c1030154040c41030890280c813420304060003c05201800b0200c80b00c83c4c00c0d0710030541d02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 619634316 1250 619633066 619633093
    0x60a1d12130909150504020f0d150c0915081b0d020409060b2106030c0303041202011b03081603020d090b101403150c0408060903120f0106050306010e190e060f040608 73
    0x88290011f10040c00c0d41d206000b048002850904410419158094010b03914000c40b03003188550812030b90305d070804a600b0742c60541d0002910052901c80d2041c8412000040e104070011517070f03032003410225281709071500a49208440203411030b0003940c40c05450301d440426502003401c16602240000560700721033300301c049888403600341c000d8801500351041c003080c3c6100d51b030144040e00140c110f10b00d400c05120500d0000407e10680746481040781d041003032a820100740c1c0690540c2c0e00c003460708600c8451403c0410100d0080c0310b5885540c02241c9080a45000c110940c101c1c0341c050a0484032100107941c4600000300c51070000032909070325034090b41800401b400a0000740386d110074107045c42814240d0b60340c015800c081c0b040742c003074116070000503441c2032003000740c00d00c0c40e0405580424440103605019024200c0e00c0003401082c14024000602030040c0e40721500c11905800c0300600e0007206646400a00340100240d800b2441054200c9e109040380c145441200e0803103418600401c0e00116405 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 619635566 1250 619634316 619634321
    0x3030906050724110c0102090a210b2205060a2004060c02040617060403020d0807090506161203060303020f01020310050d060b10050309011805060a1d1213090915 71
    0x405004043d40c83d660b4102544509402621103000031400241e510035040d020064500103540102d801641b000c0300c203040800c05010101d0006501c9588480300b40c4690544010f032030714102868810064021646040000118105010f507000500a00000c04900e195140706505e0351a06411090103000070002103128856240f0b0490001d4000035400307484007850600c00c00c007043c004005511260078001003590402c421010504a440c0411160403c124002c110b0844c5201c0c45105907400301c0c20804100d00025032048281e0b0100700000e00710b410741c1c0301801070036661000ba03001d4024540c000b2100b9206008580c8614100d1001e8090103040c0340400c28800d240d00340a8489556580c104542078503070001030f0130000c81688542da20380c58125a001d0946401e51034890843d01e4000606000440029060303030040b030000300205000e01c116140d0016030302c401c04071050324030400b802003c18040000050065900c04568880742d282ca40300403109980665030028072140d640a0308900078411703035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 619636816 1250 619635566 619635623
    0x62a020a0305180a0801150312050c030702010509120f070f05040203010f06080c0c1002090a120f0201050c01180f0b0c1606090c1d220f060e010605060f0301030309060507 75
    0x90413a401c1d00c1d2a03005031400c44200c420210b040d81703070401050051100c079000300c1021503481c0c81d02a1404840c441507948074001d81074000d042c00000300e0944000d40d0341c0d44040c5016089002220f8a000740c8204069942c2010710500c0ca5001410340046903d00709402200d06a803044d240e11071102d0b1900d142142c1a06000b0400c00040b20144600c0c2c1c1188400d2120045802c1030500140c4c4482144d000c01100c0c4880d44d10010f20300d401001b0301800030304020a0189c9461702400d0070707511404043d5500d40503009095011202035103000098081114544010f101c0750b006d03149046051380d41d02949425803191801d07441e0521121900f541c0004d5980d0840b0047c07520810310300c02e900399213000348003a54068101c14000c0c07440c820b00708000e4000e8580c080e10484502d170f056034000c010030788038481021a0a08060850f80e240c4104035660f5a003500020f0040c070015080540e00e940390031000609800030300085000a520740780000304a4441d03000d540c91140c00418244811456003005841440301 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 619638066 1250 619636816 619636819
    0x30b03061f0e0705120601110d1404120b0906150306130201090906090e0f0105150f0a0f0e0f070f081f1a070309090606050421062a020a030518 63
    0x1d45802188902e80340a50360f008a034151143c580b252050260700c01800301c01400b0038100000f000054044250010303180d8000021428003180c07104e5200503210807403089412440111202002c62801c000d2000141e07407290030004281ca2450b1629014a6507043d060a0156810341c0180b0100d206282540a0746404038070504014a900d695045200b09840085c5d000c0c80502d65148644da90521090140365005100c0000801140c03130100a5a8881f0440b440004d00602100c840194242c40e5804094050400c44107403c2c0900d68642d1822a0000111000828071201c03102003120540285801010104aa10b6503180b0340d885542c144c54981040010b0360404076007040002d22807265100800201d003020082d250b50b409907040c041c2003007190341d010011082c41c010f400c20030603a00105407400c0c0c4030055039087c2c4007020003461200303407185000c000c0e060600d0410031000c003130340714101d6a028510a15048610201d0414140d03290700e40c064002d40030070020006c08021700208101c40350310220 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 619639316 1250 619638066 619638121
    0x151d0913121106010e090d0c03020d03020a0e0613031703040302280c0e060316050a031407180504060507210b03190f11030601030c0506032806090507030b0306 70
    0x5000c11003d1a0000a0f4440c0c0001082a002d200140c4024848005480306d541444c03407c41c80181e90003035403203e207135000100701a8085520b8036454450000302c0100340b8010020780c0c41d90344100c24000c1c1d05d40030303110850341c4075070300c0d84e60602c0488000c4c1a64071894050300039101e00c0c200d1460a003850070454513044c0ca40c012800c42180002c0322100c011000d005030b540e4869a51410500349032070b00c0303e5140841d800101030201041107030340340b03642c03402500c2d4089001c4002000308030503d4507085081e0810314180640508150700c050302ca1340050700c1507009243c103102c0da80b6005010345032010314000150340d207162441e00110b0048c00303800c140704041c005030403500141c16042c80700f11180c02200d011500864040c40d2175007405654075011206000c210301030100b5500d90798500355083c4092040c00d02034000440045c0214900303c265025007007410b500401300c090740b182c0e488000c24407402243e001c50302e070030301042c0031a12070300c500c003021400a4010503480d00c0c3c4940b0030080444106248030b0460703 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 619640566 1250 619639316 619639337
    0x5030a0c12080403060203070c03120204120f03021e0c010e0103050106020d111c030509011a030a06050a0f18031106060d0212010902041b03230718151d091312 70
    0x40e00e0384002c40c8507918594500c0c4054849140040c4030032f40040000b0b80060040c8005c0c02a0058003250141d0300b940440040f05016692805070304081c40e44014100081980918030343c5c65001042061180409030799403010000c9031801941240c000b07005800040e808180e68042d280d0051130007403c1c80000e80c0496050501740304009800304060021070700041c5d298020300c081310500340240302c500036900181164070300030040804e03912002581e002c1c00380c81d100d0001c504d80c1040b0340c3c410141502c1c45070080c4146072401950707461020100c882240080c13540003000f859084040f0313030a4090320b03000700600c02030050f036002c0009c465154500000e0555071038811200591b0b0398858011590f91682594881c00b009004c05070413994507409008692803444002c14101306001d000c2c65100801e802e0081c500b521807022541c1100c1d07140c21a0b41001505803d640c0c103a03400100a40310f800a4902c09080d10140c1e40c20310105600655050a800002d9030701c1d4800284041100c110203081e038a0940700c2c1c1b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 619641816 1250 619640566 619640573
    0x1504060e0d020a0b0d1803080610230a200c04090201091e050a06050703080a0c03090b0f0108010606030218090603150411040606030513120c0c08070f05030a0c12080403 74
    0x40c0d040d80d000500d0013000141a6240125a00480310b05000880e0041a11001350b10007606000b401401c4a10810316100c0000340a0701500801030303100010013004041c5144409a01c0d29a800550500b010a02d03141d4400c0005074801c9500003e040c100000c0c0000e4040d09042c0009081420301c102d0510400040c00b003036103011224805441c1c140039001802030341c80d110a110220126070010010000c080112402094001030340c150001c3c2d1115000440c0b849030f02007100208030101d8020200c030350b54018044242c04602e0b400341625041c0c00204659541c810702074089110340c800c1400e4808034542076100d03d10b4400491503011030090103a403c2e06c01590602c810058044508883c500b84415154885081070700c039003c0501541c2c10100310b07a041c15410400040d112180040020300c0d400020401580f0a50f40700b81403644c4611744408098980c003010f52610194040c125104003030b43e01c0005c6904e800600399405a80020741c440c0524145034039003203099071114099800c92010000000003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 619643066 1250 619641816 619641829
    0x901020a08120106030c05120106050904060509040609050c040c1b1109070f0e0609090432030403021203030402010504090e0a1a06040c2109020f0a0e0f061504060e0d02 74
    0x380c50040c260a0b04540c10110040c044855110284040000a022000100c0007004849040d41e41d03134140941c44910810000d006000c49810036034100511100780820003416801c01401070784201c041d80c05546402003400110703a08847d0700c400040d9104451400b12010f0031120301441d000300c841c400050302d2500031801001c000d41d01400098031030305400e0019584508413a00e04581152518500034030400003d00d81c207400381014000795580303080690819940706c404e0280380c200003541d04120000113801a100e0304203120a82c010108010704c3e1002c040c6c04002c880c070490313050f15050300300fa00f0440d8900040c400d140e42440036101d0b228000c400708540d9241c0c0c1c11200b0100410020a20b050000c0c8005c0d662142420401d0090715050b0781006101600c40380d10401500d18005400d4805000098030350203004110354200701000408520004503080c0729100d468011020122602c40d0000e00800b02c2c00c410041c41400c3c070522061103007610a51804487c0c40c0d0091400900c0e04094000545 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 619644316 1250 619643066 619643077
    0xf180302070306140115051305150d140c0a08092b0e01030c120e0c060c0f0d02060c040311030c03100e0c030115060f1107030309030201140903120901020a08 69
    0x9079108040820801090b809540102003250814514951500c25082c0c5030074215003110090100c0407540e0420a1f8040149030002c110003095006504e51110100b981a4891400780b0307000b505100301c8034000d20002e081d83d8020040340840031700c0c1414081007110402c80281c140c400c64014501d0b8054a03200442c5000080d02c002c0d82c0180d145503003200c0c0503012403185c0004606050914402c042e084d03410107007401d403d10000001080041c0003440c1c0d00d09001540604980c0f0500c00315000d00091400200150341580700c0307045031404864600141ea40b124121500083c514041005000088202c100109036140207401c684503041420700103405d0a5080828000c11035444110800b10502000b10100121095008011803030201800c8000980b49020b044280440641030440c5244613000e10304211407982c1c15100016105d19004100c00400c1c030050b800a405070000604a1a4140840d40640c82c010001e014000400c02e401d643d80e0011118036040d4041c49030410045003201c4000c01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 619645566 1250 619644316 619644323
    0x170d0908030f06031618110403050307050d052803090f050f0c0d020102060c0c0f0d03020909010603050f0612011e06080609010e1b04090c15140a120f18 67
    0x50322841e140c1a20310740d2510041007544030344e106150f007000e81070005c0c00610994011006150510402d64101006001da5083d0410b8182c000240003040c85408030103004004e01c103100f03881c64900b070194111441e00450b002440707130120101c2c03002010b402e01c0103032002040c0316003004104003200ea1203645069907201c200b526160000034400e130802609000c4003824020896001210b11319980000b5940d50005000468241c0700103080c0c000482c041140b041622001422566118071082c40140603401c030340342440c000c800100010580c14000d00a25108546500c03060030f0380e81e00c1904010200c401004060425581c84d048290420071034024428818075000c0081400e610b052074551a2140091507014103900d08032403503c02000c0840d12840221001c034014500e24038800000d0300038014908010541c2038035400000300c3e250704200f003d0620315a5299407421000e4000d0000941c030424003000000b44518000640c0c0103500d5114208464440c18001403d82c4420020250070508283c00e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 619646816 1250 619645566 619645583
    0x709020a022e0b0108090d03020334120506010c0f0c0e150108010e040f0f11040c08010503010b0a06090510030209030a1a090307020901031113060f060e0301060b07170d09 75
    0x910703071403800b49000401c028030b0140d601c6d15040301d400f500c0e50342e409580c0e800c0540000208112408602501e400e00a034011564400050015540d2202252003450400309011214000f408a041e00c100b901c00c0c0010307180c40031005001d43c0c03401da441440d543c1c125000030f1494000b003418020807056034400c544500158030a08101030005d0410f181c168007036074181c040101003000190005800c03043e2280c0c004038038070301c8c290145442d8400040d50041c0c0d6070003c3c60320036800f1001e640001528100c460580c02041014007040900a0041c55402080041885048108814100850210b020004030302d401030030326404070006420403900b810180c038071074903082a402d021101d4aa2054100035043c009610b040760790f80c0400e0140605100c06040c0c5a005101301c069610794024031150311810030010003189442d100e400301c0307070806d03405504005450b100d5010303028141441903600781d840d20041c41c1d0510007103542d0984460a60403070103940d84c40500c12403078030308032500078101c0321071080008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 619648066 1250 619646816 619646893
    0x603020a020f0a0f060b0a0911070c0e0603280c0b0304050c121504060207060e1b060a050414040243030c030e04180503070b0f06030709020a02 63
    0xa2802000780e485241c20b8114040100001d0681039081d04c0c2190303c00f10215184004a0004203c02c109600009540d820010603802e0b400071403004090651292044e81c0c0301c03503110546150310010850b622038266001100b012441c04e540721600c0c1d00f50340c480d00368080008959542100031038540d40f2041100388007105000800c0400c1c4880f20055005564440c510b681c0190400d965007000004941c8144508010605000c0c294044404403a0802010b00c00c1c4406966599591514042554192120440301c0c2d040b502e00801203070601251a40c1e02c030b0601d802c00c49034007030144254008a902a6003000148200080c0d42241000300c2c1c120b2600130348900140185881070b6140d22000710140490401d080700082d08201d402c0d1050b0b03050320b03010074000c501d000490001d14169080f0401101100c03015801c01100200524516210304034425180d141c1c9070003240402429195964903800c0b11100303102e041d00030750140c1400c40c454412505880320f4440743c0d1049494103e00d0010019041300d2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 619649316 1250 619648066 619648087
    0x11100203070b010905090a03030b03030706050408071106090612090705040509060f09010917090a08011104060e0a030201020c01080a060b030a0605270105041a0303190909090308010b0c16060302 85
    0x42c21030051582d0704083c84179140650a940c0c80340284100102459926440481c00703403010000d80300c0300e550100f01044681400d08241c186600700c0340702140c4031000c040c841e824608000c400d40d91560b03000390000d420681c110380604001c4400a000c1e8049106209001803196541d0050f18045c1c90101c000d40124201070880740a2000d004007610510f07030602071181d000501040d5801c3c14101140503040d03c2e06c02405c0052201142c540c460b04141d0700303282e111441c1010000040003110b80c241c03100946c00168000b4000304003414130010380503803c410103000d199405400c02e50380c44140b0074000038403a6140c0941c115aa002a03640210701a070f103130018400790421506503842025815032040030100000817034030309828140900d81c0035503190380241000112040040700218030003401d8907100c01040b01c242004601c0ca43c0280001000640d0024040da5684180e080154140c1c0d54107060340e0821020800591108000510511400c1e071208035000701d03100b250019203034541c2c01680d610740b40e06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 619650566 1250 619649316 619649333
    0x30e21300c0a1704080a08071806020714040501050d0807140f01050f010902030f01051c0204060e040c0e0403050a030c05090d03080a06080312040f03030b0303030103060209090a271110020307 84
    0x190a120f14500c81024000429188016101001e8851911304810b41d1458002c44050f206000482c43c0d0300b01903440401c01c10340205400041d1101c0700300040a0b4008402040700ba500d0070703c6443c4e04108030b03910b0600031441c06802010b03164081c1c132501c1c03003204a00d04074a1410080c1e2402c9807207039559005201030030251001260041668181c10b50443c14a504ca82590000600c03d0506c02c0550b4118464070316001044c070040c1640042041006550b1500250309110044500b04d4102e03492800c00700702110403800c078034050750f09a0740d50350500300c00a50a8000381225130782c031400c0c8203040c011204140d86208003840c05500c13179a40d807030803410482e406409486d01c07a00540129041802400204208400c0307070340d4090b41140401420a03030310b040540007004044034a41d01400008004018084030b60004c0c01021019102e20742a80c0d5040d003820211040c0244084c0c01089441c0c030820700e010903a1424240074040c2c18100543c107025400603841c00c546c843d06101503000856004148407424 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 619651816 1250 619650566 619650587
    0x10f0806150906240f0d0c03090b0c130b030c1b010204052803080412120305010509181204150801080703030219050f0706030e21300c0a 60
    0x500e01040403200e00c1c400500c0c907a0004007180c0c066401c824421400c407030b4003045000c0f551440c0210b1640c40c1400b07035640e040c40c5d116464502c109410010312440061191250507010341e00110f03074110645a5190581c400c0c0c1c0050301c86401040300c880b01180854280300218000e050401145a44501c00c1e0006158525401803112641c0d2052100b0002922001c03007120008900e0000b0000c0384892003401071f0390102d07540015180750070100b00420306050115070300510b80c0c05040c0a086c0300900040484c01c0e41d4007406682d030001f0214002c00c050003001042c0880700d48640040c2c0e91000769104c4031130119000b0307030310020003541840d0048190ba07030400d10311809480741101814001c2d0460301c0213941e440b0503002141072010020004010f0050034007001040b00820b00940307032800d0b41d40800601030308000039079841c0c80c0241851b04a0001d1514111882600c0105610f410170b074038468000b002c00c26161624000303190724125405104285c0c00d0b02c502c00c85541614907110252440001c02c2c04100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 619653066 1250 619651816 619651831
    0x8090304050a18092003192d0501090b04140a0804060516122c03030403030804150e031207030209030d0e0d06090615060918020d0605090f0a391403010f0806 69
    0x281d9440e00089160300e0390524000d60803000e2816480010940380b07508c0141c01001800651a00c2c0c50101002084400107004d913020f8008805808544036085880b030700b829000070b007070b002c003040104055030054001d060706070f00451225069120580700e08011140602c0540000340015000c0e00340d00710007444e0f2080d05404000b100c030500d944800803230350317900c50750101505026404002504201d064841e03003901d4403805109200500c1c10f503214a6490304030003c4641820b140500081c801072092080d0380da070500c001c000f07042d09801801c05803100c030040c0000301e420100c0c410300a00032414600522040521411000440f0310039405400803203409500714804004401a0130402010f400102c80291000410010b9440e00d181000344002d200641c44190440440e004001007160410341081c4a0000070f14184003030500307500300300c2c408001c01c14107666502444441142c0e00104800b41780390803100d4100804400c0102a220843d50026440302c40c040d0304842d400d0109201c1070009540205c00e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 619654316 1250 619653066 619653103
    0x18070b0a05040e060a05030d0921050a031202190c0204060803090d48080606030d031508120c0f010207150504060b060a020a0308090304050a18092003 66
    0x52900300425901c514454a8400301c01080032503500d0351a8003400004110042c00c4a40b4440c00b80f40c080c01d8019103106011039584025254841b0f81a03130000c100402d94440060180c0d0041e0f954107551804000c14a012055400d0204003403002440008000403209600c803000038402501c104410340783c03039400401041e0000e2042516948801d2140011036610802c80112a409004861101c2565064441c5152003604480c0900000e40d1920084480e481815961103515039810342d664000545400e9050341c000d01034491414804c2e8814810742c601103209025503680d40203403a14299562120b01e02207003001403066804041000030003801e11203d0001c0d0f0408280740c40d200050707022142064074190701c1d0300005041110030f51001400b07020040c03203151075603140b00e0020740d00d03117070a1402c4001c65000ca000c140506c2c000400e5800304d4100624141006050140000a80401254903c00692900d421800040001b8031202a0001c140d8440c1d440110200c1014a4281041c01a449841c1c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 619655566 1250 619654316 619654327
    0x60309110a0806012c010b03010e150a1e03060e0607021506030604021e030d120c090305062a12250f11071205010614060a050a0f110618070b 62
    0xb18049081811540304448114120f004000b00c00c000000940780920b04405500011454482d0100a58103943c004078004041e60b680c0c070500d40d881507404042d5944040040307810000b0b0040340104405215071781d152412155941c4c1d48000690f00d8051040341c564005104000c81c0680c1000326001400d081c0c0c08555460401801103038413048041c2002c0e018050100101c28410003900500440d40d10140884550045100700202044d1845480f080c0c01800e000445a6461007a40b01e207081c3e03038005020786401d4495080400d8a51102007421841680062910071904140d80c0a070a0341e14200d482c954040c904943c10001d0011084500810764848510303011940f07500507a2002c1d650900c0c00d11074046081c5140d120701c1e214140e841034a0b00030b0301003005020050103400601c101d9903149030054070610148108191805031a400c0790000300c05115180307015103d80e115406503211810441c00b1001e0841c0b105041c20422690841e00d02c103038501031a0843d40c104501da00800303400301c5041c00c2a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 619656816 1250 619655566 619655579
    0xa051803040f0b0304031e0c14010204050a12020a0302030706030902030105010f24110706030f0e0304030314030c07081605300309030d14090c0d020609041a0a060309110a 75
    0x54940e80035580300380c3c40c0440010100350003400156001c400c2540d80004001c81c3d04802010745039280c1d02100c0038203c6010250710365205000351030943d08002c0428441d2070610000c6480300d50080800e80e800b5801c081d000000d0386050200c0e070003500035550003041d452454018142501d006900841c0e5418107400e00304017686030b0010f6100e1040306980d210b2108102c4c9d41c0c089809240c40c9104c0001070081d601c0c002121a00f65000080d41103640f9024003100c8514034626407a40118070000d030100f00c1201001a00c0c0308844015580306500d482c007075003002d01984840343c01d508500040713540c080c00815250140001045480051a0007600b0704d00011641c034925059681d2000c3c648000700c20100c0400e02213007041c0180c9134440e4003040d080286105c50071445000c040c090f00c1407082e6006034410070020b81400c00741c1070750164014080d03a00c0c00c81c110041c0001042040d0100602c401d50300c2d44503400780d8460b1130b41c10061040d40d0780425200d20702e040c204038442110850b14400c41e00c2c000c041014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 619658066 1250 619656816 619656839
    0xc0e0c04050f01050d150f0801050a0605030616050d0c050d0506030a2315043023090d060c110a0c060305060a0803030f2514090a09050a05180304 64
    0x2803081c070b0103503141e00315410100c02400403204980d407000564007010404a1f1300f01c0180b4111010301000340a5500c0f100307601d0044030a140602505908001c1c0090b101c030035042101c0c03401407202d01c1c04618098000044e1001c540420100314001140014144c0c4030500074021640c00c204110041d01c07220640b59145901c0005201c1000c0c0882c1900c0d86400da451003c0c0018070000303041540203255450140392450255841003040b02c5d10300101b40095124042641e071070b5840071850f4881268902c2242000d00810340000f0807050781381c1d010006d1420320740320507050811040c407030300002c9401030f0341d00d901400d10a1000c00f0006c099002100407030208001150110450f003480c2000145a1240e20201c1c0050006401002152000005100c400b000042c070807842070740c2d02c4c002550801e0360403694400b901c08041e000400102018004200e444140723000b4010100700821502850750742e41440c0e4142c0e8003c6804010550362881080304041c40a00101344400c3d42e28041c5280600b00908041d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 619659316 1250 619658066 619658089
    0x806130320010f091a07020303011e050d0c0e070e010507021908150603070f0503062701110414010903080301120503120f04050d020601141504120c0e0c0405 69
    0x20480500100c20358841140804640400c0d041c00030302826039010940e00107042e0b03a22040320404540018540380c8034101d007295010342070300c0d406549564600795844c85500d00b40490703100c85c80480c503c0000c1035640c0300ea0f1039040d40d01c80e4202c660072526041011000788002080c507814001c101041450756a0311404a48116604442e03a5606030141482d000111101d5041380701a4400c505240510003501c4e4590b40c41413000310b0860710242e0f114072480ca41620706102c2e0942507072090000c104c000401000703203080100b000c00c2d5214900b00709101242910411580790328800000142070100c800d00800c51484980203082440d8002d00d1940c415140340700c1480f445079031081132600581000020700071500c078481800100c94840c01c04684d00114040240c034121520f103d40002c6c4580c0a001081160490b042030414052000e81e030014054032504c10b113010502000200f1011a40428103580c109240e40a600e0417440141000c002c40c50300c5a002e88922040b010900c803c11455588a10b18003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 619660566 1250 619659316 619659323
    0x30f0c0b030c07021203040803031e10030f030c110a06120e0c01051e09210d08092e0606020106050108090c030c04022104050f010c26060102030c070f03020a080613 72
    0x6000c440b0941d0300e0447c01542c02040140c0400001c0c00402c140c140034401d80303008420300020103a101c5041c2c044045100f4132000306003000c4482c0c0b1501090181c400741d05440d0141c00703010311661850002548000441d0045c40210b64060821071705540e00740304981048814400038001d0611990000e4254012081011800482041100c03804040c62082c0e5052040207040345201e40001005c0107080c1000440680f018402c00359291000c9101e461014007800810001e424540b0841c0d035007180703032440c110043e200c0640003610350340f00d441d26104900081c100340c1d000003252030030300c03000400500010f4541a103540c02152002003e50b000300798445078840440300143e580a5440c245000e1405440b5220f407440440710811040c0040412655002220b07480208054075103c002a0341c1010b2076060b10034a0440d40c441401e40d00c0c01c0c607030860382000050040300d0130701010102c4540f60150369040088107040e080c00400850814908050103404510040c140610700340d44408000e840d62031014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 619661816 1250 619660566 619660579
    0x6040305211909030203040b0f07110907080103020f06040e0c1e13091d010c02340b09012f0607301803020c0f03010c0807030506060d06030f0c0b030c0702 68
    0x502058000c201f250010100303444069152080c000780119660480781040c0c07102e4401d10903440c0c4030320b0320fa40010b00c201202d88400010340d003140c007072001c050310807103285401c450204400710714001d00d039018910549120030302507503541440000f160011190064541021000e2081902c8120105421000e45600c8200003524101c11164503404543c290b480a036194030306190400400e034040780e4a00403c007281d0101c0c0d038041e00c0b941481e41442d617002031004a143c140c04140081c4910b00f0051844050501d04221800c4412288608181c0409000042100e00710003c10030304d0414400a5481401e5050020485102060407619650001c0c1810503801451401041c1503060b64040e40100300c0d24540d8008120342407501030359560700c032461544036036140a94104a0700c0c0500442031841100c1d6110070083d21408d00075000b80c1000303440c0c2c2c1d50190041c041c401000c2c51070711502005500902e100041d6080340d051144624140b50800001c10104200f0000b012000004542003da41903030300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 619663066 1250 619661816 619661831
    0xf010903020607111807020a1406070c030e041116060b061903150e07030e07090b010c020904031b1104050f091b04111306090f050a0501031d060403052119 68
    0x20060483d031003051804841e11806d10040c1e135400103004815601c02c0c0620350300c0360200740816584d141300316140c0d000140005405000280b150381c0402444802800209584804030039088040e0040e6080c9100c60a05039801030520949000d5480038604c01d450f90741c90314004451080d040c041e9404900d05140e20750080106035003c06480340c0040034280d221092a050480008014104810001d150751048920104802d0751350300c541042c0300390503115454400c00590a0004c5440010002d405004c41c010303083c4054a010401a000c0e280f040d10001c0710030304641c1c03c00c0101c1c0c3c0050006034204030700720204006003400254a42501d45a040d071011454034000005014000c0562000400a00814240f00301d012000e9514242e50443d180c0103200c64541c090110204d02500c90382c0d903c144100e104100b554040d80c0518401506600301220481e0030741d840d41d03c1d1810035502140000c43c0000c0c81e460088a45002c0703202c030200614201c00c282010348000c14107065520110440c9681c07000e2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 619664316 1250 619663066 619663069
    0x604050408120708010f0602160e091f1b08130201110a021801030203191709040914060f0603030a02030702090c0909090304091a0d1103070504090606050f01090302060711 75
    0x20303550078501c80c00642d449440c0145000b80401400c0c8120f4551003031b0030b0710100300d442c004115104080903000c80070303d443d4038106c040100c940014050001b24001d1328550a03c680c0c620300c00c4485026410300200380c241030f4039003030b03040035032961951800c100040b02807011180c8017154030f10809409103401020015055401410300554070760095000c03c20103140401c40e241401a5412603000300c0903540707000b054042c20f15540340d4694005080d2220340c42010400c5030000003500748940d0280000030707420507a60f501e4100345d001d59030f400718a900140400445141480c400b170340c010010340c080c504006018102a540e8000c030070b002449000c4510024850f0044101074030114880101100c0150a00380c601503100d60107401210301050038100402a001240103110042400103000841059129280d08241d80f030f030703110b2095141c00b500c000041c8680e501c2c082c5000c5180a2400003a505150804010681c402003c1c490306104100800b00f0240c0d59040a64103910b4010629000c1d900c108030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 619665566 1250 619664316 619664333
    0xe040816031206080c040b0301020304020616080708032802090d0f0602070203070b0315010f0e01080406140916050414070c080403230c0a050603011806080604032102090906040504 79
    0x210b80c0b250385040c000082e01c1d4030024600700f150000381c07020041c018440b400d05090740310844010303401c42410800c2e05001000d664030f1400880c0107100c0740341800110394440340c40764415220340c0e111452820072079203154210b80e114011804249c10440c1343c44c0c2c0e241b0114405c01030360180502440700791310307481c400c4c080785030104c52102c0c0c1d00030300382c42545840701c0100c4c0b50340c0c1090b5200e030012250300481e003803154020141601c420220b529a961500800703001109d001900800842c0c246480e01030915002c075410003210301039806100548142449103100c2845420f169101ca4401e40c10144441452008001c4240d042910b070700c1c0001540394641412a0181700b0f6901c010300e017803600f54558494003801c449100340340d000c0c2010b5400d01c08004040000c4520700e8061103603c28400c10040142d4956058443c1d04e004580b0302c08a185a0744490341414031108490a402281daa03040c82c070842460078020520040b0341c1a4114180501200030508000c0c00901c91805035035108085420b00c1100c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 619666816 1250 619665566 619665587
    0x6011e03021203130603020f120720010509101104120512030924090601090209032a010f0801060c0807021c060f0b0102070302010c0605150a060809070e04081603 71
    0xb80c5070414100d0104846692980010804e03402e5004241c00485d0b2644240202c0390503c18030400b8a007003030300c6038118030344103d000b030a08400e210402c045a654640c0488111140c03c5800d000015645843c40304c8504121118508034010707403402207c07030070090000c000c3d6400c0d9505400c1050341881d007071601c9841c0c8031004590407050040401000340101000075440020700000160030f0b004aa002c46485103804141c03943e007000e800130001445044030503800f41118440003400c84070346100b84610b17146c03510800d1000d48440d4258840a08007035800010103071882c4040d01e0140760942c90a0002003480b180b5400081203c0320000d080400d541c0c071103000902c41c9004141d01c2107030326000c5c03400e00024803d06072140081e60821544114a41c008158842102e8068440108582c4a03035034031801018011b145003040c0c3c405000ca445183c0755050391001805503902c400e00f950500403940f030301e071128a41c0076091000c100010000095803a4003901c040140030000c0c00c14a01451505031810301c01d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 619668066 1250 619666816 619666819
    0x40510050c12012903160207090e0613260403120804030c11010203040902030c0d0c050406200114010305030d050115140a020705060a0c0204140408070210020321010305060609010806011e0302 84
    0x210034014410300114800d0341b03940964084510b81a03072644000151000450b0124480d0454800105980881700409400501c1280d5815448114072105558501e040301d240c0110580418141704221000c48a00f130300d141503060200304d50ae000e5500070b0450200c00c20040406c185000000d00603402001a2006003482d040706545078a80b9040c500000c0d000182c3c0e60085a040070038002840c0c2c050011201a18400c1e07403404100715840d2840700d144d480148244940d0743d0703644050038040d500a441d25000e988500017950f911102d0398070310010f91b4011780019410140c80e1100d00a02900424500c600c411f40384119a01d0b0056403500340d0610301d40398012504400700240514840e07170b00c03031506070280b80b08407401c11078541c00781074070041c230f5200300c500030011b42d8100014800340c41c06101500700705035148112440c0900502ca107204259000c2a80c0382d1403003602c8014410048140841ca51042c02911840007039072402c40d90640e9558103119440c018564010400040a0052615400f40d0340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 619669316 1250 619668066 619668149
    0x1081b030c2203030f1209030e10110303090703300305091603080d42090c170a0b010e0906040b06070f1205040807050f18040510050c1201 61
    0x540c0e044c00303041402c44040c02030004581e0703007820f41c2c1d00c00640300c1d212486805980e8201c03019580b03003d02056607526500c1ca410b100b90703c0855420307020308100441c8030319100c40160440c640345103006068010403082032280d400304140e40d06101c5c1540d40f441c101a087c20701c2d010501c1d03195403081d981020300300100e046103450305000100600000078028072340107400020400c880c5030302035041c40d440401410a0502c15410048104a00040b00f0300d080700c01c45900b03602414036030b0300c025603070441c1c42ba5603c20340480e0300384120403081c0c2d0039031050035846000401c0c1030240354006070000704060150070300148203242140114441d502c072517012004161024116650311002800c000d8040e40220408948d91381c0d40c00490302d6098401c906540403100544000d1101608000400041403090040b80d90088445801c404188a5100103035001d42c0c0a90301030070b6590305e200c80800585400a15840410030100110403080f0b11528006045074504d06008240013a09811554041c407022200c0ac074082 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 619670566 1250 619669316 619669319
    0xf140d0f020d0c030804150212090f0715081f0f03061a0102150a090317070c020406060f05040308162109080c010503010b0a090503190201081b030c22 66
    0x5402203211490030640d80c00300d90815241d14070440710103003100e500034000744550021900180380300c586001c0303101c11050094140408000c6082c00c02100301d64000345540291280704851409001c4c41e8080c000410741e50410300c200d0301c07019010310390152400000640415800285401039442c08011380842c0102109440d0380381000c9000c0c10b10200d2087c225503420061850540c00050200c0006142101201c1e00396542c08202c4001c0c00900b806800340035284100707210328054241174603c00c0040d5100d03a00c610010b4010b0108031150b5800103802d03c00d400114060054100003604c1c1100c2e80f04404c02d64540f146402a41c611640600050141c0c031001c3c0700c03a5040a000c91000d900c9002030392307401d4916580307072444d80d5a030219510240c0426001c200500c84e6801102c01002e99044c58207080b030b94559184013182c070f800154115118a00c1c1c04109001c215a032141c4401e03005030240748a50301c80c2d194050001c0f61031101070300301c905002d070014040d00091002d07812560a03041101102101c903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 619671816 1250 619670566 619670593
    0xb15010c14031c05070c0b130c120506091204150215070507051203060d02010305070e0d0501060614040815041506150e100f0305090709151502070806040f14 69
    0xf03801c110341c48030a50304000b08071040c440c22403081d01e200326040e03038402e8074003400381d01c07142000b401c003820040b800e10712a070020380403d8030040004010105a40800002803080c10880d080030005010701420350800c1c0d41547c600e0320b054054605a41a004040181e514202000c1c1d24000100c0c6940c0c0e5802516410001403940020192212030301a00546643e500084070101d89031008546041d400145c0712400340142d4807951149520000d941070400e10080c0c1080050f00d1486040e03001c5485a4650409004aa600c02c0d00c0284011019220310708150170280000d880c0d075060300c031402529445c071002a0521848141040c0c2051020380d0401c40c2544401403e4041c00716543c0719400b1841c5501f407101c00781070100d00640c003521540c2e01c5030044018840210090000548000e260f44541240407501c4041d900c03800c50300f4034001d41e604041c20300d00030700303c52034407640b91201d025504200d904014a940c04142c0c07a83c000c0d0301004d400811540b0345803c00d4507640c0319680f12154800c481000861 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 619673066 1250 619671816 619671823
    0x12030905011812020f030d1a041a0307080703020619050f030c04030209010f03030e09090304170a0204061401121808040e04031713031d06070b01210b15010c14 70
    0x700c50182105583c03d26140405a80d11801074404452590040090360700400859000240c68408014510080c4003140002070a44641d451200101c607a001e41d100082e140230021130f0001d007088809046c01500d560000780d50342c0550404d100040d000c040740c2d541c0007880341003143c05819011382d5464403400c0c460102c3c03900342c0043c00200c0c02950740c01c0010400200780298a0304407541640c564601c49807010034881d9010001d00001e24a200a22000c2000780b10342034807280078180701e030050480380c510b40108030a4410b1940100f080417401440000540d80c40615100403003619280130410550740074109280c170f00d007418050866034000c20086424034807500d450b80198005d075561400040440581d0444000070b40b1054203180d24505800c00207030007114184142842040154120001000450810b80c4480d008a545603440c80040c441100348501800c1103401000c00361110351010756400c501000c1c050040096188121102e14550b8402d0659400156014403019450403405080540c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 619674316 1250 619673066 619673111
    0x1306080901050f010e01140f130f18120c0c030c0f0e1602100e07360b0d030c08190201050a0b0d080f090109092307030b030a1203090501 60
    0x20954200350100b10000c07000940c0d541600c04402805c800b9034a0b2160301c10102c13071025907540c3c0020b1705d42c500d6041c0c0c0e62260802c41c002182d803000866040742d2081e003841116000e05142c41c061009a02100120301100c0c0c80c2a0240c020341440f600d031410900300190703181610351008004038401040850000f00025030310007221003c85881e00725880361048070300c0d0200395018420060f84903194602c0305020039088401907000c0c1e10152515107886034000100302c00c1100035407200106011410000c540581021081d03014011010040c0c0000e280008101a010400c003030304201c02180600c081c010804200c80300500e014a20044d010078078100603010704011101d6158a52a0182c000118200101540b1081da48403000c140b8000c80c01e07240c1002038000f106410b040060014002c9040f1015200d45d040d550480600420f140706c1c158241504844010003560405003442c010a03920345002442c0307000d0560108a60400e100301d00003c5004040b000da000c2c00a40c00e0880030100003441307500c540c6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 619675566 1250 619674316 619674331
    0x602090a06030e0c010513080703080408060609131203060b0a110607050c060406050a060803040e041704050d111c0b011508160c020102011107052410060c0503130608 73
    0xc0c500d03a0380c80142d00300c40c426000c450064200b4445106658422002001400d561038004c0752071903110021249403800c0c0e504100c0340d410000405011144041140b594007840c101c46140f02c40c5040508a103518203030702e20003440d11200c0301806142c14041e81008014050050b203403925400380600050015401100d40b0925010300d1020a042600c100111400d0004680c028012030300e031941c4683c01060000c26411400b5918040030415050500040c0002d01d1014050150b0781001c0c2001e08680903c454400c0301c03c501007000300442d4031130440383c10341181c0010080c1c10760840440419041d400d110844910b00040c080304900f0001ca90b5199810b03142240c01e030010804581c0415aa043e10540365411904407000300345000320722a10041c60b00501c10f100100b000190300c070302c084050b0014501201e06820900b04061040042000c841e42d10800400ca02e2403410000f031004080d25081c0209010840115841c90500604000721103884a49081c5c0d184100d47e0380d04001c2141e83d00391100f8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 619676816 1250 619675566 619675579
    0x203190e09070306120b0612030a021b010201060f0b03060f12010608100b0102072106050f4c0b030a05190603050705010c031e03020309010e0109110f060d09060209 72
    0x24581c2c1d0302c60b21888003581c02c2e4200b0521660800d8598101c0060024203803030380903031301c5212041217000c184090004408250000c11181c1400a1201000441d1902c403d0442e1300d4008104190742c3c1e00c22400d4221100043c207140d583e00c454020403142c5040035141a00003c400245000308141580524100c82c848000d0f94030308011240c801e01600d05001003280140d00031802400812440c03000600d4500700024101441051690b50000f0b4510072507006c190324040f0010045e40080003085c4582070105914610740c00003182c88001031447c20390745e84100900c1074601c440818005404401c02901a6400c400c0c2ca91030aa951400a00011034014001188220706160b00015034051181520760040240180505220045640d000d440b18290300300b21b41000c0306400e668100c3c44050102c8a83d540160740e07464210800c600b92246c0030013180c5544c0c940490341e004a812460220b040741c104940d80c403038680c130500015480b400f401d200c05407294070304201e4000304100c0d5030007412440000e6840 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 619678066 1250 619676816 619676821
    0xa09140708100b09040b010b0922020910020d02070e2806030201140f0403060b0402160309030b010803120606090414010608010e13050a02040b040e1203091c02070b0a0203190e09 78
    0xe2102030001a50b0082403c20f038400103202300b0b2194030141c002a0405030000240c00101e030306041441c0c07142549c01d80f410b0360000c0c840c0c5450510f071540300d43d00c50550009154440141900968440e01441109040310341240442c02c104c00071a8040e611103101d100380180d000318040500e00908007407004030701240c0540c00c243c0001c00994207640da10304540d101c0d2800c080c03454840401511301c002d9201d601c41c0d400c000d403c0d00d02105001210206010340e50380300a060035482d16188e425810b8010b4007a0b5030041c0b1001307019480621307550340d128006444040e15140220045005031140f104140038802092001007845548640f1260481d01d0180141c00702e9165000e803140c480e40641006082a00b000d4204005800c2c41c1c0c200282484000e0070014000c000e006aa6003440d18041d40700010365000004d001d141780c8208407245686c4580048000340c1028800c0284d0756203000c3c448e2441d00e29000c0b4000042500910030345035440c0078090602894003900200410140b200503501d03119035111800b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 619679316 1250 619678066 619678069
    0x91a01020a0206120c070b090d0f02030c0304141503010b120c041212090509090106080f0d0804140f1b0315042307090603030e1807080a09140708100b 66
    0x78000e8001da00070701040d24111183c1380382c01c5250001089800755070002c00a0000090050705442d10650020010b03107060a401c0350000c0483c21854040011580b05002109100c40c1c0842154200c4401e604031000540d40000828564900d07440c0c1511003200103c00084c810725500c1c0248034a003c100044030031a07440301c0050f001401b60f07000d800c040c480ca00030340800042608001b2544846242017041543d9074800004141c50021616074015035154a01081040c004100e809038001c4118003415003003010300401003400c04010805001051117620442ca00036050141c1c800300c0d014081a22480c400780c040c0d505442c1c060b610740303c3c081d01c14503010103c8c814244807900e009560000603000700752b00c04510840c0302040b180340b503407a6005001c40000c595801e80f02e07600c010343c406d494070240740124070b0411801181b0080c0c907410008070300b0200081283c0c003410b2950b111400c0040080c5020980c01e06905503441008204018880e100020821200000d010080d552880c8414003030001d4000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 619680566 1250 619679316 619679323
    0x6070b041707120806120106080304092a0f1e1d040207051f1e06050a0b18010c08040e09060a051b03150418080d06090501060f2007091a0102 62
    0x11805003c550480c41040811480b0310001d64020f40b0042080704241542018603003103032026401031401e51f000103001c001003100ca01400780d00e000d40c00300b0040c144176401a4961500c1074401c1d800c0c10800c0d40501d10140074010341701c1404d114500062040c43c00000c17500034100f03043c01d50954070300190502c5030840c2403600303000b02e6450320f9200002d40803012030510051100e40121400d180c60035240e80359101c1d60440c610b9415084542d44602085c0700e440d0405010400005420148070038004100440d018254850820640c01c003c3ca000314403140c65040c4100d030350080307400628000d4219410b204104400042d50b07030080e00c220108000301d4407608543d25180740d0003c0b00700c0d0900e100380700052010610102c00d40303143c0c20140001c44e1001070a01c40c503000346500e0700200c44411001c80c00f1403480020b440307540050b01c0d6a0500304042d50526102601d0110200d82910801c00e03100b69088030315050410303004a40001c08120795400381c5a007081c1000d04035001d10350003440c0410140811561000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 619681816 1250 619680566 619680577
    0x417010b060a0f030b01120905070e060301020a08070507020118060c2a03020607080c010e0f100c0504030809030106090501090f050a0614060c03040e1e070f09150201060506070b0417 80
    0x15103c500000311640782c01d40242114006290500590b04100d410125213030041d901958443c6000c2c013080d60400c5080540c400c0d01a084502982c814001c07170041ca80c00c04e03803da41008031070405c41d88030400781c801200c010141c0300a500080300e40110001c0d900f40c010800c2c2d14064420205441d02c1104080002085459034440000d020400c540400260500c00c0080049500405800f0320f8045c250600e142540e40d00040d8030070a6002d03000252041c003090045a900805200040c030125140c0d41e0014240e005902000e000c01100041060490707409510100c0180280d1001340020760751002500018a06090309001c0c80d03042000040b1f01004a200341c105541841010342c00c4110304106110f400c1c1c000c40355810a510013004040b400740100e00a042c0f11304c8904101001103111203120382d1801c03d01900b00801d00403600c3c8140c030f909800400c0c03001915440d1006004040710514128050070b0f1643c4096003014001503400180a402402c0b503102328000c07041040b90b2600d00040b2080e51081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 619683066 1250 619681816 619681837
    0x10813120309080d06080607090f060512070c12020102040f080106050d0f030207030b13020a1403070311010216030c0812070f150e030d0c0e030f07050d0303110417010b06 75
    0x402248014a500a502c11000503010303241c0c00b030a003810300c480e040448046401c568242e40c007200401107a168480e88020180041b455549803640c42c040018145004105582c090300503a4000605024450107101c80e8550700006407601900035850082c0c002d5010707004240c0040301e08100811004414000c080481d070003c0c3c1300c20305120094451080344200900c044085020b00c0e6000004100301300146405904403400820b010007061040000d6500d00e54410000003052401c64043c9070f40116014080740d030420300303078038800050000403824995841c000c1d2001c100d4100300402403082400111040e01c059100b20b40b0130b000030840518440c003031b0050041075010800a294000b619040f2040ca14810400010480003450304100307003540c20404062481030ba8440c4240c4860364072840b10940359605030050f102168094603420344a61250040324007030465404800d081610aa000c140e41c004520400c40d262626095000941c0420038a4081c40e9030811802c010390340f91000c1124400102c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 619684316 1250 619683066 619683083
    0x2010e0a060b120714091302030c090702030f0a20010203100605070507031a09010b090606070f170301060f030b0625111011011404260405030714010813 67
    0x2503075940806403403110701c42c07038002c04034440908a8510421441002d0f004640c00aa2400700007414072544910013000d0241342070b04011882d0240c0c40114601001c420140c4010750f89507034005080c0c4c59403141c49c0c01150844000a5028030345a0f00c03c41c81c14901d011062284044845005400e090f8001610f00050200703126208112040c0204010701c4000c0c4035106462030160340342c81e084c2c01e82c031a0201c8100307401904000c000d100d1001307105241e03003000c0c119800c142c0c504041d00464800c0c005c404008200c0c9910103584d405010b00c40c4044103038a00385c1b022140c0e6940e100c3c0001012040014402c0300801c0c1403500c2c0302050f281c01810382c0c3c0019212802102c48000c89000d050750380181400c00c1d0351802411020100300d45490311481000c11070780d180c8c041540340c00c1c1103841c00c42c1c02256220030151004001e210014005140c40341c1c0c82c00c04003002c2c0340c01c1442088180000c0c400c0f640300396810b1150b000001040382d94004070010750b10098841010f00d0b40d0b1040054030349425424020814070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 619685566 1250 619684316 619684333
    0x5030a091e26010e0111070209061e10030207020904050c01111b011b06060b030114031506040507020f060f19020901211404050c10020a0b0f220c06020c0102010e 71
    0x12010746440b58060214002103000035605010302d0855003101c03005010032000068040070740c1031040ea6690090426a040b415600d4006100a143c0315519040b81c4030302080c3c0ca03100402840380e0141d56000b41c000300300030440d092070700d006a96919038490307650202d9140402000c5c02d0102184101d80201076001300da2040f5500001154070301e10981d08648240000d0241101243d01441520701400e840f0380b8407596035041c40b441d54416400c4000c1c02c5e11030f82c03003024400f8140c0782c14071003c0d801c00d4050b45c001c00c05ea02e80210984c2821444484403c0e030b4820700c010480c10780c491140390350241016617020020004000d08280c00e0344030700032405020980b15800b2821041c949401480f17030101a03040060306895480700d010680100ba1400d5842e41d0011002c00b01c103240a40362100c05074600d000500c0924200e55440880c0000202000d00e6518030000003514041185107038a0b0741d030719a4030903038260325a614000300480018000c6a0051113500501ca103a5401442507001d5219600002c04260 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 619686816 1250 619685566 619685609
    0x20d08070e06030a29120102040605040b0d1b03050a0501050f061903060b0c030403060509030325020a02100f0305090c130513051e010b01081003030e030a05030a091e 73
    0xa40c0060188888103517109298218020400d10390048000b441c0624040c09090404019140080e008002c5059204020400c841e03034020045a00700c4108040807a04c40c90783e4075200005211180004201540c1035007c0e0b209158160b0107070b0b00c242c2c003120b0100b0650340c950040c0b0544160080e40c0a070491000c0009045c82e07000100b201d0724203510361901040c5c20340c803101e50a05c540c102103460425544040b40c1401005094015503a200d80c40c4c4000b541946840721500036a03c80324010741901c0e0f01d20804032a040b038070900c06da00d15150080e00c07400d460150440000c1030824803030842d2002a1421000c6441c810300880c2c105203d17000103001c3c011a102109221000b800050249201c0c1e080f40d10019001407401d003c800098210090410600c112881456094441590050781000309000401058180d003a508038156501481d10380c0592440d00e01284c138207440404007420703a1001080d030300d5403103034002542d2041d0340805403000040900c175490902d0705006800b40e901504646e03094078914 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 619688066 1250 619686816 619686829
    0x60c03121103190e07120311011107080a09080111040504051312050a090f0b0a09150c1401140405061614040519030804180b0f0a0506031b1603020d08070e 68
    0x250103c6110002e84d1010103020f013868403100c0d50090f11128020321030141415042520088560b02d003100070b001c1040503031450138992081c1c0200805c4440089810140141700e40c21410141014100030004a5101180c0d50f400d0381061103524440e07414900000c5584006056400da43d070340c0040d010704051746003c010b82c2c254128000040030410f480300005001107100c81620700911107500090398584107001c0081540f030f0282c02001c009460358052a0718150302c4003800d6500e84c0c001c960f01e9402d451803502e0b6805800b15851040142c02004140002d00401252041c010f8078000c000110058401809076600340006100c0c01e041c1009100800c40b0f0f01f45a002891306205c06441000340f60b480b59141450b54003da044110620118072030041000428031402143d13000448813011042e002030000703440400c1070b0180c94040d0a02002107136010b00343d4020504078058a02e5180d854040d0f060300d00c0d80c0311540c414254018400c44002149803405194114007940c440e80c0e845110910714000c0c0040e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 619689316 1250 619688066 619688101
    0x20f071e17100b15030109270f0308070e0d140f07060909051503060a051b0316030b030316030c1a1e04150f0b0909120928060c03121103 60
    0x30881011803400d040300c403404d001140600428040090714800f0b19202d803803c06036403a07005010b800c80c08001404545030005036401e0701e50528095059a85d9000119080c001d8101c1c3c8641000801e003982040040342440745540d10314201c1100c2c2070500c405007159841c0c0c05445400081000b18405102c0140240c000c80d52040e03101c1e510018120300a40468600401120f45900080d9900148080c0a00307403407640d0621148011070b5410750030101e03c610021642c0303a44040506075190b089488540b020310035600203400300e903081e9958214609010b0829044481c00f2214016a00303030801d4000b800c1d08055024070b804240d41b40400985d5041c41501c0b02e40900241c414014103c02e888401e100d500558550f42492400440e0004a00040c020051000f610440c40360308500e40c000840d02b21303002603c84d1000122000d4513004001080310580b1281c81103900e003098484040403507110780100760f40b07040b1407103940c0792050f9000522898045402c4420408250001000821301040203000d1210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 619690566 1250 619689316 619689319
    0x11090a09020c0f031c0f0b01081504060e1905060a080a080c070b0f0c0105161b0309080d08060a09150b180904060b01020f060105030d050703020f071e17100b 69
    0x10340040e904003d16180d90402821250304907451a0202003503641c5008142d41d0720400c0d0028080580c2c50800a804100c00909480900040103054410740d60307982c0040c0c0041075500c42c10750850030300d600c0000113121613841203181c003402c18000c10783c00d084c1894804101e80906c2c1c0a02003103012927840c040c20358403080d0303000480c1c0b0a0420100f036008249000704005425070400658a01c62132417002e0079582c00070031698454042d146412501d5030464802c20f1500c0c24100c1400700c0301d00038501940c485803150450b444070300c2604040c200c4c2c0b5411150150140350211841c00c40a595486a032050301c00802e000300f0219960711040041d0b100400143c942d100e020400d640b01c00680002041030510201c4082d030314191102c04040c0b2658051000d00d20b41d688400140038a0340c1000003103070f40c0e00c003100b00da10704109000600c902032510902114002d44100700959691955031290415510722100d403044600c04c40c0038002460880c07880078107a560f200310000c1c1100344ca11600d11002009400b8169 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 619691816 1250 619690566 619690573
    0x2d05030a032f070c0f1d06030d0e1002031e040518070c08030601050415080a0506040612021c0503030411010212030f06010804110303040308130e061302030402040f1d0111090a09020c 80
    0x11440100110f81750b4090000780443e081d4040a42101540403100a844c45019412100c070039841c0962081c0c0c020b2a416040c1e0701200c025002100807442e40c4602c00032200c010030070302c03a21074074107040600500481ea030460f80c00c9a0403441e40080441d00e84103031180c10100c0c980f8200d0700e000407034101c06503501c10b4050400c0c81c24269a0109101d603052180c0220001600c0c0004000303c41207107100e82e40c1c021000b43c508009450900e10400d04420a10b68041e1250394010100108043d001480008207a881829039481e0b040c2454100c06285007244014054000c0c9840c1d101c0c00c8004a0a60f8409c0e0404001d140701d50300d4031300041d0303110301d8040c005980e55100a680c00e100ca44082008200840c420101280e032a1541800c100040d031460300040c00c80c4003100309000b82542c1d0045004010034242500585e41d4031584005402414600302001c101030912011b0755010394811544a510055940240b0240c03556101c51003c51003400307102e680c406a401001e1000f80348a501030140c105464045 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 619693066 1250 619691816 619691819
    0x105100602100903200f01050a0e07051306050d0b0403080609221401020406050a09080f0d080a0f060f030605130c060f020f0709052e032d05030a032f070c 68
    0xe1140c505c0510366090250f44072080c01c0c140c0385800d11906034809941e5004121803034401c00c0d01a182e000f1841350610681080340c1040074400700d54051001080020a00c00515800b403614600c48103044505601158203440000d245007042c00d0141c0c800c008091200c405400d9200104030145107100e02a641c9403541a10540311b59802d10050000c0c002075294147c030740b81080e1009160b0200c6401c0800300c1c0d0480c00d05200509400554001054140c0c1040c001942e61481400300400f00c40d433032000d903581440400035501070007400c0c44003a24001d481c14009582c414044140d400892140100030800202d402c04c4120f21905016440000314415a07250f0f502d038501139450031180740c2000e03030410740c0c0d6801e222007415184401007500604825114920301c1d407806d184140006480041e224507014407055078107081814841180c981c20107040040300c03945040540d030341d030000c0301c0790000b02c1d107400e20041c04144200e4004c0741801d00d44030900149100c6801401d43c50b00034440845082221100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 619694316 1250 619693066 619693097
    0x4020a1203050714060105040c020309060d050c0d060e151c0206030a09050115050118082e0f151208040504090302031608070c0905060603150a0f12050105100602100903 74
    0x80804c401c20b140c0010180c6506007400c00c8101c1c1e04030020501954810070412905440c0e460545980d401d018400082547d10440d1040e81c40c070a00c500c0100051420801061680400640078045c4142c2c0f182e91041285803418007a2119417110100b1030b074110141a080140381020085a004613851030208048500ba80c4444c2135400f0305411844844004c0014450b9590000c5940d42c0f00745400301e0302c605149882007207503d4540112413108020710988907841d44410908240340130300c400752001c106504145000703600030410401c00101c46184a640000c603078068035007110300940c00440141c0303014500b8041200403e0510001c805601060003a8100b052203546090b0281d4007030112196030b4686458000b148060580000c01410700c0e01d01405515160f0b68103599100c119202c0e2460044426000a0245925640070841c405002800460f00c1804000225207952140f402888181c842c100650358030122030086c0070060b07120511543c00142a03801002c9924081c1c00d0010724205005c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 619695566 1250 619694316 619694333
    0xf0c060c0905130501090e0115060c1704140a050a272301142403100317070623042a06030b010f03110a11070b0703030e0d03020304020a12030507 64
    0x5449000f69075140010011480d01e0b018041d41510108000c00c082190000c441507802190f000300d50070050b040300510100810561680320103e152503120f5265503544041005044090013824000c40c1b070800009000d00f00310001c8019640c00401490b4241c044400701800802d40305800302d042a25044e80c2c00c00d80d8400c24041c0a20310080c1800030142d81412142551143e41114041c09040c44000151601080c2141445100d0b41d91400a981c0e40344d5101d042e04400c829040540320b02c03500100300004913400002004c1440c420320b410f000c00300c100880250980000004650110121030001c3c1c00160b103451460406800002a01c07250042a0b054844004054000001003130380e806440d40b0f19038100c00000c03a50207481c9014401c9510000125400380200517807c42400320301c0900809078502444060041d00c86000c5041c1c87d02c64905006019000c844410030303031802a81114180d051003070003120300c216005821040740c0792420115907228408450150308000c4c040c00300c1c40021b8400d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 619696816 1250 619695566 619695589
    0x10302091005120114060406050901020322060e0d150504050703061505040b061305040c02010b12100501060207141c05151807180c180f06030b010f0c060c0905 70
    0x240d440b43e031902c0c0300d4441801d83c420113030481507000d4500900c1190701d0b6104011903003035980383d1921a403a12029070050b07186000c1c055034040c8502000c0100207440c4c03070300302d009000c07904035944000d10b15230100140300e190000058083e2088114510a002c42005504010340192040c8110f03440c603646c03603e88100700c607500f002880d5410b1400c0301c10403041c80c02d40121002910201c40e29032a14848201048145100d441514000d50726848040c20b10b40c002c2d800050301a80140004d60290301d4507516640f0b0b040c0380080348030410b00e040000700ba81c520000350320701960544500c401e0380d100c1c040708122850328a90300c0d100800001103c40343c0040c03824002418800b05044820007941840c00307903003041c2ca1144400c1c20446d4825801040940090200f00c070255603d034400140c001c486401c12500c107071046050b044801501c3c1c100084840c0680640421a01c0c6507404002240305c82e0f00440d4660849030307920f0300080005100c3e401040c42d40c0d00c0501103515904004c01c0f190b030381e103001c83c5004200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 619698066 1250 619696816 619696849
    0x50703020d0302060714040608060d0204020c0703060501091103060901060503090304030614070207080c031002070507051f110a030807030c091a070b01092310030f0b07180503100b01030209 83
    0x301030140c0550002c100d500b803800706d07003c2c2e5400e250522400620040c0020086031140129003030b16020354607aa411905420314404c00c3d1380c181c0303480c0d01f001d00190400b0b125901c021494030605a0b00a5004015240510f8006015059076407030308204444070b42000c1c00040c95130000300000000070b211489030311108582c580002c1c03110326055501a09150241c0c4c4407075104c0d00011a18102d594012503182c03608a070803040140c441e0303c9400c0c9245400003580088d9000000960801e0180710b403580004250380440d41c65100822038030500949415029000602041c1024086410320f402a0004107841f40300c0e1500140341a03032640520201038184014541c084400144481407001514015024000350340c2c080c000301812050242c0d880e501000080708104181d001702d40110f4601d003140000b1a042140d400104e016820056495a0259401004182c50b6507000180c0d042e01c403044022554020046c1041c40c0e07507000b81d41d0283c000940041d040540c20084460301e50703940701000071504070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 619699316 1250 619698066 619698073
    0xa060e01054b0a0605041a04030203010f14090a0c090504330606090e040602090d0804060504170d080609090f03030c0301030606050603090307030c031419020712031b050703020d0302 80
    0x50401044442d0810b01a01da80030300c0c2c4074481403140076006012035088910030b040b0901119000c014011003809039400c0298154204142c400e80304140d03401c0081d910f915084600035179122642c416584845012000304418008102040000741c1f031740c806d550090040b4000c104410f5560320114001d5410080708104155000c504844900c0ea40308030f00c041c0c40c00c1c2c204808090b00f008401e203178283c8000c000400007600084c4680c02a1a00c511044606500480d0f00b522039455040c05041c50300a80682e8203c00e56900040780741400002c1d00222030200d0f0b46a2648548a1000340999202d005002c580c81d80300b2071a158800c0700081008610458401640c0e0703480c2e504529052041e9000390740000c0c8103a0091043c003800740e50100803141181d500d41001d2a10340081e240556110001100806d28880f0100d904042c280031480400e003100040d9094440e40f544034240c02c1004e43c41c07000301500050707074800121204000d071410800351500a204a90340555a0360010303d4500030700c00308400581 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 619700566 1250 619699316 619699429
    0x6251a040c0e070207140909120301090c030b04020a05120901020c07090b09250f0311041805010603050c09150c0115090b0306010e0a021612030b03060a060e0105 71
    0x240c02d01005400211510241038101e103032881d590b040c4044480c11521940308400860f1001504000d154403c2e4501100140c903503955100400081000da08004c1c0400d0419583c003c05252910869640000d05d480b02800c251501580031120305004004885942d4200170700040c001e010001c0400034010b01102241e501100c1e4244014808044d2016400381c0703094510081b812190404194100c201e4502050f50749050601100030b40040c005d41100c02000040c04100f4404c07265584001109071003007400f60742d907103036030880407204210740b4031101107002c2c001e400301d82c038210b24502404e840d40c4000a0400e00000c09640c21184a8008404048200c0a04124040081c002c01d100f4410440140403e589000710130030f051100189420b1949034001844210628481c4603840380e25003040124603e4000100040e00604480503028802e2294400003070302e02250380201c0c1d040d1861668401451b074a040103000c5040400728082180130000405c21680780b000341c0b03000070a040500d5242c015407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 619701816 1250 619700566 619700579
    0x90e041115090a0e0f0c160605010b0a031b091202010e03010f0519140a05041a04030801170604020f010503070c1703191505010f020f150a0b06251a040c 67
    0x9480d80028000c00543c000c0000031034001d00f285606c1001040f01560b20039080701840604841040010020b91428001060b810103601c081c3c40303030f040192420800b00250700700e10a800c0303c9000803170000074a5861700780030300c104041c06110302ca4418144030610507803010000342503d1541455110880e92001007141d4002c040d90104000001c200c2c081200412165144015500040c00d0045160701c404c0843d080003042c15009030483c240405903000390078945001480713600300784200702e11801c1508600404910228080c1c3c0203c0c0c1c0108503a010b8540c800066405800041661050211511959000ca50800b650032003d0002030500c2d0344e01c0ca03103443c410f54400d4030031700340080b0645413002d420905a82110120103545d42402c21800407a040310049260030709c9107182c2440c3c0e0145c3c0032403200102501c00354900500d85060b00344a41c1c04070360213102003070042c00340750200c5014030749044800106618121111a015080032000b403001c5100300c0b40d031081e0a8504071030f000f194030010400ea = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 619703066 1250 619701816 619701829
    0x21b0303060a14131e150f03030e060d0c020a05070f0b03132607021e061b24160509011707050f0406020307050d081905090a02030d0206010f0501030c090e04111509 72
    0x7806c10140801c00020309160102401c1c0d0013502000303061110503081c400b001c0c1d5901050f2480100e514005100300c4554050007500c8040345c44040303880740300d10b1a02041c0032030103098240680d8030000c030a07415a903450540d107070201e02544040e200160034154a07000c0e217030b00c1354902901611000c3c802e5541e900900c14010071161052a0ba0104240d034035140c0b038960390318001c550800d4000c40d4510f80c4030310031400c403904003602200c243c14010000b4140690300d4019102052040410200c030909102088400341c4483c412140f03102c1c00a8003130701701c08100072200e0501a8000080d80350890a2072441d840c0d100302e0f03505c07540182015a20200d61341003040400c101030300703c6140a00e8240c29a003808031301004215140100c2140c0079480c0d6000401d0b0140800500403000e030004d04a4454000c1c1c03003c046e458030310a002d412652407881c0740214541d4001e00855407403c0d10381d51400071040c64410235411000010304101c3c1c0300c1400090031a0703a43da030310b00e02c0152a400713004425503556011040060 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 619704316 1250 619703066 619703081
    0x31611030706091706070804140111130f2408042111011a220209090a140106030c0206040209060612040305030108011d0c0f0a0b03040501021b0303060a14131e 70
    0x1385030740800300700121700380d026061079007013903100b6030601c5280d0085001c107024045440c1d242420010201c2c00e000403c00e901310050456031402098110300d03440c1c41e0301a4040e8000074144850b0321a41c0a401070051240217513507480b0340503494030910302c41540a0200d9108084c0c00b003000042c280c401e03a4031500c81c00c0c480c05124000c9641c080c2ca801040c04081480b403814841c400c42030b400e0f01e45000c131522031150100c4200c860003c10360b000710314283d54071f10014400da2030818040421a000450403030300902c03072101111500e8001b49030300e0b0b131150300304412804000c1c03085402690500c80e103410441c1300e941c00d038007852003a15403e4403503040200003801c54000b20743e00700c40c0d041100c3c16a01d02c8000401c401c20110010f442c2c1404402191020034600603180c1c1c804504854000108020300c8010750103081008100d641200b02c5d20b50315000c03250360780070945205501a44c00f580800c182c040041412490840c0545413002c0050682c02020488003a020707980d41000e0400281030306010140724281 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 619705566 1250 619704316 619704359
    0x406150e091011090409050304090c0206040305070b060406090903020f0d0e15091203130302011206080c041e090b090606010503011a09060409110703120e03161103070609 75
    0x1046181c4000c019507a80e4038000a03201441c1d45001e546100d50203002118802c0314080c100780520704051030101d50f6940280319211040d4031b002c04c4001400e1000c21f81074056609076032005c0c2000c283d46c84801c074402002d4005940150b45040010b80024a4001c4101050203900941990300700d04c00320301d0a0200c1140c031f65041003e403041705807495031075100d40a201488441e107180c0300d040050104074400702042481030303e0301c03010810012143d00c2da5150301c00d80740b0070b03602d40d03800154550100341036550794018558180c202d07809072001c0742840c2c1c2c040952810601045102c03803c03190a10011181540016200442803108001c540b41040103c19003000080c030f01240b55601d812806c0402ca200021711401d40b0800155002c21035449500340d60140c1042d05040001078ac40f0340704c243d103540c021407080303001c9030012151543d07034030462140e003503000511341c059850105070003442d5916902c805011642422510031911081d2010060400900143d032220760f001c41c104004c244003035450f1058039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 619706816 1250 619705566 619705589
    0x60314060c09011b05010b0604080609250902030727050a050d0b04020d080c1507030e0703110d081306020606120102130308032e060906031103011418040615 69
    0xba40036640600c2030159400c60540da50b04c41111407030070318090040c0208880d07110001040221b045c420124075a809007a022040303074070445070034030b00f003e00d02c5c03408081ca11544000e0b00f0401c02c0302c480303030000c543c0068103142611714540c1140d6180b51f140b2071907420003001c0190100601c82401c1101003140030306400c0b902c0c450124a1a0385040034404e005200030300031041404500700708801c100540303640d034101c50142c1c1c2c40c03000341c0711b042d0601a004403080d900080c142181c000d0345100110303460098170b401c081b642114103c01d4003445480040c05a0444041d01c00f0803480c1c1030f07107503020030107405044141d001e0082410260b081101c0410201d64481c0745920400031841c4882924140d5011207034480c0c0c0311034503655110701007001d08803135403e00c0c5052180407040441c2d002c20700c0e0a620540e410344c0c9510340810303201c0e441281155845404052802e104200610001006079552501c1e24001131220130910140c41c10580f21400c2501c040b2100c548860000094400008408001c0d00c1ca12400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 619708066 1250 619706816 619706827
    0x1a01050313080a05070506070507060b0904020a03141e07150918230403020c13150b0c01060503030a0815060a020c0112022521090b0904020409060314060c 68
    0x141da03400c11851100801e0700344000f840100e01801001079035030058020042c1c800620b01080050240d500c00300044030180c1c0b420001c0c130000e2070305040302d07402907070003400c0b0381c0c0401c0c15a521800f4411003d00041c0710b030b01c51024400c03070a140781404a020304d20b403000600740341442c00c40c080108240d030301c3e211810300c43d600806000b01e41c8000030003d0725102d4900f001c80c4103003855a40035412a031150918061401080400c17041c0350b00010800c44400040c0d0b000001c0441c4422200c080350180102c40c4442c48c5c1c51030040000b1001007020704110390740b02c0c00011b00140d40340300017851580800d85080200b2194007c100386015400918040900b045d50706034641540341c00025104c0302140b6199040c003074a1590704040900b20780c1a107c0c041c1040e80d0310038010741c000c04c0320b0040340c0c0c1d4904102c54450288406440607a00c480400b0510a100e4550064640c10800d030251143c00c818800e07500242d00348070008503000780b4011b46000394055428500c0042441920904088000f002c0e004e240c5010440c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 619709316 1250 619708066 619708081
    0x509040206070b0a02070b040629010207030209101d25050f0310090606030f110703091512050a02070302150115030f060e0403020c1c080a080411131a010503 69
    0x1141c00c082d50001403d1103603640c0504030002401055800307010103e85000f00300401c581ca0780324081c19099804400e6209070540401030a1900e9100500c2c01031300502420801420b00c15101034114548a10940f82c0036101d005400b2402000180c0c1401c880344134085c404212400030b000080c01103242d422900c0700d03a084101a081d03100780501c0c1400644008006a800010f60310b10031b01030260140c060040715a9080010007030a500024110054a8030000346502c000b001c0440e090113906450741c00d03000345018005580c0b203000881d81030900ca0300030104045510341c1d1040d00d01c2684072120041e190403035801c0082c501072907001d054550382000001800601c0a1146001c0440380c6032801281c004981d52428000d003280364001d040c80b0701c1d11006e01c420190041940ea8080b00240e0b00c0481c040a444d40f48050b001c130303005000c4e040800030030904140d9030ac110f52141c0d102c0c0c00340111400d01400100850f04040041030300b900480d58440da6aa10f0400d00c0c8150702c0e1190007441d146041d428000c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 619710566 1250 619709316 619709329
    0x16080c04033e01030b0901120303020a020f060405070e0610090b0c030c01090c1403061b03100302100807030c14180a05060d060f12081801020712051605090402 70
    0x20180c0b459485042010001c00d00103261072001050548141c0105004004030302c200215500e0a404a41400c0d10031000381020144035040320103034403803007000c901261810360080d400109041c045000ba070a030072021600400c441d5004070b104600800c2d03994944100300101d085c01615a078401e408450020310400c3d4451414030580e01000c040541d9684000d820074030718860080081c14035420f2110240031321214680c1c0c4011070f00450f010300282c541010400d03490720400c0f039500300785070032805044c034044101101440c0e0000410b1307007034004036441e80c00140041c2c03800105140050081c200704206564580218414000a402e181c442201c40c070460504500030307071070b400031440321001284045130744000101c4010180540007e54480105801c00c1c040c0600c0d010701d8120500e4000001f8910714087d16510001e9040f032803031410a020598003140703020b103845106045100d00310b004545006150700c4e03456481d01c90402000110603074103241244c888030794002c0d4480d800c01001c0001684854 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 619711816 1250 619710566 619710569
    0x140603040b060a081b100201060623040b04081b040203071b050304031407210c0302040e0f0f0123011d180604030f0e03210d06080a0b16080c04 63
    0x4584160195503880200f90f111440350b001010704c0c82040032000004c4d00a242d4400045015104032980302001c10040c0d0985a2601c1001f00040301180c1400d422404150035441d1440040c41d82c0c1d251030342c1e45514240c2a04241c010b403291780c1107817412404403203d5450a0103144400d0320305608500d04010007501c112a000c8003082c003c100314001404002003070003120050355101c0c0000f0000581c000d459540c0704030b903000e01684582d0003600c501e041080c000748800210340c407607103d9049a0540d400d200103030240000c0d80c480e600c04d480d4100042001070000b41440060f0100011708201120042120801d082212010220754540140403071162401d000654281910606606131075606440c504200c206a113011107000b00400d0008250707203d0220409541c003540c4204d860441a800c143d101d220400c103120400c007800d0380540c03071004404003400b007200d0280070006099070b4802255003170230844103084039144034800400087d81c404610f5081c40080300d14003043c451500300c115000c0c1d80304a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 619713066 1250 619711816 619711823
    0x1b2105030904380102071a0301050d110405040b0615040b0307180f0305031902010b101d03010218040501080a03021b0d0f0c0f1a040504020a0e19030201080114060304 73
    0xc4409880d01c00e1400f04141550440da414000e148000040c005041511042d51090043c020084005800d0b0078401035070002500c5c002c034840c61a407030314041200d000c03140b0074100c644660641003e0b1380c56440d881000e22840c001d002c01c1d0b00d14a004420003043d9862201d030740402c203d06020501400b40300c1d0b0281e0398040705606024403850114130102c80880c547d5401212181030b0164003008021001c0040d200890100c07004d50704a1200d0442039003a1400f600c011500105500f407040400313441100c8061403502e50043e02c0056a0f0028082801ea80c040d600d100301e5240c43c68400101d81c20144245401420340c1006020b204e82d4942c1c0c02902d40104005500d52407011041080d025038801c8060390380c0c0c0d0340c0f1a01e0710740c03044031034a85044c460305036120364440e548200d1000904144440d000380c100c0103801114a16041c1040b04100080d040800d2003810020181000d05407a00e407103244600303c8852400040e02c1c3c034030398400100001c005810403240c9668003112a0b02a484410641c0d4101b43d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 619714316 1250 619713066 619713071
    0x1092004030b13080a0f120621060e0d020f0f030703020a030e1f0c02040b090c120c09040207050703060b0301060b030112020f03060c04050405180a0b0a091b2105030904 74
    0x10b030f180e10019910707010342c0094038598000030b15080d1141c00245c41000c65000d0380f104040b00c01c0d20b103070741d5084668511541e4913482c90000f42c075206a611489510704584181400507980469402d210316050444070004007583c02502588200701d020045200f001e540003009628000590b40e0007500d40c0c0007208000e00303002c01d48400041c50f86d00c0106826954034291b0741c00c0c83e00b10000c900101030303c2c01404181d02481c6000b5041415040101ca02d620524449011900e03102c00d0800301400300c400105000c220700001e10840c00146d0310b038001820071a02850041410504600307146088545151080e480b981c50040200544000c0200340c9044851421140d01e01d8482400404c100050074803040d42e040c003402d0100001c004580001d081520004d035020002541ca03403142c102111070b074101c404001c1d032203e04c01c40c00081150030003660104100c10086070600003591090711100e4030300c40060940b090840148090703140c10300030030002c1d45544111f90b00d07807155468581e102e10584442602030394 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 619715566 1250 619714316 619714321
    0xc0611070509160f0201060e0708012c0c090a030609050717070f05040e030903012a03060509060d0507081f0c230c07030206040305030c0d050a0801090b0a0e0a0501092004030b 77
    0x45c003c0d0b0210008114016a0310068540f0040040c42e10700240540200031080d811320f0b0080230f68a000c0e90000045116130707400e25854410340d481c0260498066140d010b03d40d1440071000030390900840c1d494901c28001098558213156000c0040001016540d0300c1d6131080700c040101032661600c0304110f8100740c8000130550b048900c61402d40c403a5001c00f81d015801c1c0007246021807910344054848018110101d030305125002d0b41101680c40e00c0c840c9691000d405404910103145c29551003c42d10710544c01c59a01c40c0e92943c23118241103e182100070b0b400300038241012041404c1c00b0390138500c20503141c88140280341c102030844801445292000703002d00400c00200d801410018000a03507001420141c540343d40e403404540d01da00003041d0303c056000f03030840154910f000344152800301c0e100da250843c0b0f9a083c04420801084402030443c1c1c420840c2c24001000d510ac11300050207010016404551981403007890026075650300701001c4081c05c09004014044544d05c1900c094030351202c8010100d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 619716816 1250 619715566 619715597
    0x10506090a030b150a0b070209012d0e0f0106080601171801180516050603180a02090703230705040612060503070e09010605090622090c061107050916 66
    0x41d0103420081c025010b0340180040d0481c000f0201c042c40070222603001d0b10b241c81d0000401140207a480080d04420340398014402e0441051501030407071004046030300f440381601128400507540e42e12200031042048148280c00382490501070250103035040005060a1240008141c4500c141244c0d4006205902059082141001c0500c100d0080300081c8550020b5645042c1e0f80d02440000711500e10480d80d00f081c1449807031000b0401c43d44010955425031346d4a5510b06001c880103502007009005000304000140c1d654071071280a500e040e54000340c84400120f01202ca08900ca100e454900003400c20012015440411103094420301d162110b01c41c994170a030000a0210354101ca607050050b0b42012542038070441e5068800c1c03c69800a0050694542c14400950b6041d40c1454010358480fa000400a05016034801080301407180000d06501c01e440c0c003402c2e00fa090700080d000403e01c000c500c01c480d204108480c040d040485d40032455040010340c0c910803022141c0c0040c103000580300c500110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 619718066 1250 619716816 619716829
    0x306130c0c0516060801090e0c060d0603060207060f0f0e0d030c02211e030105370b03100e1302010c26040f090c230c100f0b120601050609 61
    0x2540e8007008070f0744400c01e480b42502c01195640603e000148146000003a68007590040d80302003c3d059000e407144215480611030305a000c0d5100102c065154500040002c1c11840140780450040000141440320a000c2c102907401404d00084014108015981010b0002c10301072200001410001562804050240c5c00c1c800540c0c1c0c81009020a2844070507040440700060a000c1d101c0c6085a03403103140c03824141c24500081c010329400000e0000094007400107052034221000c8811080d08040528034955188900c0c20340103a50350010100901c114035000700050000351001015851092800c08440d1200d00e1f48214083d040100500e640420311040e03003010030380250400d010000d4800140300c058041c1c1c0c424812100e201100079000a8480c6451250310001c03402c0755544810885403000c1d0350f905001e2902c0c5458410740030000d0b60350340c610400c200200e0750a20302c03021540c0401e0600c50310884d0100640c00e409118014207155401202084403410f40308101e58050316014900d010509 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 619719316 1250 619718066 619718087
    0x1602015108010f0f0243060b2e080705190e04180209060904030c08160b010f032a08030406030f06050f0607060c0201110a080603060a02190806150a0f030e030306130c 73
    0x81c0390714504006d205200c0f0540104442c11026140750b11601c0d090f40341010441d0380303131009004609040c00f0204150740300d02c98031504070b0507900d8243d017040001b62044240305e88025914000c11b401d4000d0f0030041c02d141c0101030300c14070044c8242d0025078445d0045810241c004004030711807900140003504040c090b61140e0a03c0d50491031254031114045a11074080000d82019a03414801900000f0003a45518110064960000b070707802203802410300805121b102d10b820916074260340c040115510401b003010300001c10065070080344400c03210640c0000c1740c009030001c0f405280300010001050f04c900d005c462109a0003100015501c7c1810310490040014220441881d400007400020499118481600540003101a20901c2d1a8180c402003280309046041c5100348814400240442c050b0460aa1000c40581a10030815802421100c1ca50050450201040c0503541865009074148101c0140c00c2142005600d14100300c4002034000700c881103451390720380c4c8403805403688600c00c009021 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 619720566 1250 619719316 619719427
    0x3020c0a0609080403050610061407020301060e070f120207050a0308070201020d020d020406120c02280b0c13060507080301030b040f05061602015108010f0f02 70
    0x200001e50303d406003003948540702c01c1d102445684085181c403200d918082c0100e600d20b44640d03214040443e94114180c204a10507070b4503540c0c5440009020410310600ca05c01c0505e56113403ca03640035550080e120034030101f0300ca0540c0c0e2051014100140f00080d60340862380c0c050628441136901d40000724003a10403c07036400300301400401c074a00180078130f401500691700e05032241c800d40ca03c4d00c8424400c95000190200040c1d01c074461a00480d5041e50380d41c1088100d4640d10011030080303485030204400c1c1540e91038221540024088a41c0100d50041400303070420346009440c200c9140c8a840c0640010301000d07051012090204e03040006520590003003950100560341640380141c2800c0c1d011005950480140d4203204500001100c12000c9421440c1c0b0f2401d00d6888500c02100741c94640e8001343c025140010744e59210256140300341d5580010400b01001180d540c5003100e0882c00d440304128803680d418014055003505c06142d80d010a0020b68101405030300074909542d1034113041c0c0d20071900 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 619721816 1250 619720566 619720571
    0x130305130b18012a06050c040509040507060206010e040b010b130503010f05060a09020c100f020f040f0501090b030f180c060c0c09100302100c06200306091605090103020c0a06 77
    0x11140b1000e05084000001000d07200c07655144068985000d0465040c80a0051003080c06080400076009610884d00140d940e0040d90900d0340750b00c04103006845c2a1820b0b1156440b2210800c2103175070411244c0d002d45101031070810741c0c1c00c140d95002d41d03981d418096260500d1010400040001000301c07450001c10005009100350007001142c0ca00610083d903a0703500074110504041030881c814001c4030154150380005080325003245411034000e140d008401c5d00010b40800c650048044000081c0c4060090036a074210904d20f80030014010602030b0380210b600c0e400510801803820000c1d00d1840e807044000300c1d1444c460b0a0241c8250a0240144c010380d4880004641c00c3d140200005182412600030b0341e280141e910384245110b851b10581c80000e621001d54070305c11040511880841e14061302c0f418000c1180000f121b02041302200c024003030184000e0100401c1203925040c8420740c1c21002e0745058a2851040c1c07030000348180308010030541031540000d21001d0f802c00802400b215190814400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 619723066 1250 619721816 619721827
    0x114090315070f0201110a05180402070f12090e270c1908070f050306070f03062309060d120e03120a0507050706110309150903151806130305130b 64
    0x30f09000b11621000c1c005601c2d018401d496404000111046025152541070800100d8261070b244130f10b406102e10382045d02407141e0400102d10104189050f88a4800e04c6501190203100400c1c00c90b080d800003151026820a01c8401c0d9002c0f1a200110b66441040c4030b41100d00d2a0080d20700310005a034030390000e424400c994040c200d02800300040e01c6ca8082983c0c0c005030b4440142510252a0113031540c903030822404203004c0b074080ca00f040b980f55500d050100b05141e464070180104002034503860140c401c000007403604e40ca400c44480754015802c85486190040c0e03501c032084a041d014030400c05228001c00400f09a540401910006018580d81156118000c0700c00030b0203604503000845151281078408100903000e00c1010b103802c887c81c0015400e1072814001c1281001881c0141462102c042003405801c1c2c1301840600c0c0515802c0c030b1500600d0174004200c015002480f0b014114036002041400b11415161240280043d0146411622841040071969800495501c5410005c900051 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 619724316 1250 619723066 619723081
    0x50109050a14010c08010f090b0d0c0b09041107172a010c020c0307080c21010f0c0e0330090904050a062910030b031501180b0114090315 60
    0x20760b1468034032160080c0040300c500041550034070002c0c055800c2452a02805000411550340b080b505858000c140189000b680e44a80c0500c105682243c0030340100081d80c0032140c1420701480c0c50b2090520765051429183e5254111009940e0400e2140000c0028054000d148003414100000d1010381c2c4c40880c034140d0134580c0d802040c201d8000809401103078402c40381460003003400c50403030b000c100241054074200030822005680c030052100d6058442100e03030700c000b20240304044201015080000c0d178000715660252403a02400c8400d0300c203502048031081e540100c2c400300d01545d07038031181000d5441c00d08142d0300002d008020700103801484160400c400c3c0800000c0c0c44a82c280655010401240f4145c04c0b40303202c001c19000a82515a1844e01c52070320f00744803406003a00003262400144c4151020000307414401c1e100c80ca0f20100c4c5800006024913450140341d40440e0030210350401c2107981a0700041c00c41c0070a41450a001c65002c10708c3e1401d61018030108078400200c8044106600c0d0169 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 619725566 1250 619724316 619724333
    0xd020d0e0c04020c060406091e030f030b0301020a02070326030709061205040f1214030c0a021209101413060c141612031701060302250c12050109050a 66
    0x401228030800940d2007042c14203100722071010414202a103415030b207a850303030b80182080301c07000c88000b0b10340502110403241c0c0c095809402c80c801e40e02d0700070018004100406039100401305d288282d00c1000480d4425800103000c1c011213a028079a0203070f501c40c020703440350600840d5440e808c0310071000040160301907100c40003100b510215210030f180b65240c00b40500c22141c00f00e50040c06060503801c00b10209042c540400428032261520806c040c46541603500d0640064400d81620403010030460350782c079014000b0820319a140c02165007071a0300306001400507002120400c0c144612725248502d050748001c122841407288a041c0103001e6949c00d4024007a9046842c29540403158401e5a0520b8030003045001c090f2141c2002c19064a09140700740702035000007103044083c010707071000504480c51410302c1d0900801281e180180ca03a2000314501541c0c0700c0620002101c4030300352000c01e0004501d1030a1078195142c000c400d500004181c9446d50040a481002030708500c51014034bc7d04111112 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 619726816 1250 619725566 619725581
    0x20f01020d05011508090303010308071b0620030309060c13031403090f040b09010e0a0906150602010501082a0d02032e0225170a03090c1401120b060d020d 68
    0x155004c034a42009040440c1c52080075a41c0d14429002040100081200c40c1d0152030300c10b009403802c0f2040c0340003480011a412150303004501003800540c010360010b81d0807601c6400170300800055032461030544421a16160020312182c1d10040c0410341e021881c10340c15401000e150b005008003e01240503d00c0355981d00440b0035035201f40b120030140110340c1807a0080211241010708030554a9003000d0800680100041140c40c4490703031021510007003005070295054443e0b440b60341201c020b0030044000d00b55981600072180361b5001d610b00d1110b150341c4a4078603014010b0020300e102d88140c5000002c2c8100c0014001960520030b000c607250114080711003c00015400c6441002d40004111944041e809988031a02008004840c20742d141944121000000da102d403112169591640803a0030741600720800c0003001070340c0d40400c5010083c80c100600042c0c400da04001800d00b44400c0000c000c4201092001d00045e02d65141e40e072242c894006455004010620030354403462030514800c001c10b0803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 619728066 1250 619726816 619726829
    0x150c0e09071215030201050a080421080a180f030c050a06050708160e150f0405040203010e091006120231020c1b1f0905060a0c230319020f01020d0501 66
    0x1c01010b801c19440c18440f2404482d03060b1030341c42c106404c0300300c103a4405000510580d00b07080005140d0340c18000401c42c1145104581d00c41884c9410320351a81000c9507244880300c400c030f10301d0074441004507940c2d0211441290b4546020080e02c5103a140560030000b030a1030040005050200b84805683c0240504d8800c44030b03c55407400c10307c5840700c22542c072341c40900b05903000894400c1c0c6010b4030b000b150050451103500e41084c0c1c5400e0350354022400300d038001d9010500c2250b00d241805001d407000d0010440303001c2880700505c015400c01c2c0c2100d8a6000e20700c0020f2180f032418000c136101503061005482104481e941190811244500a502a51088001e8030550140e040e20490030700103121004103510000d412101201c195150008070f01d41c03d02da04d8002e0000100c8001507941e10b00c030040082c05550b0355403c05081c80307498828119100c03840440d15040d00ca80286102076000400e44031010703078003240e0524002d41407809070300f0542c0c10380358071030305500000708524141040d801c030078101c070074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 619729316 1250 619728066 619728071
    0x90a0906060813110d08040e0708061504050a060507060f050c0901030e0102130603150e1e0109020a0c03050912071e0510020a08030411190807050d150c0e090712 71
    0x2c83c1d40503c4900f00c80f00d80001e0110b8825992400035041a01c042c19215105030a21031400703440b60700b03001060000301c8000c40000c0908003001900d0510000c100c1c60346200d1141503007013a0a200008041150900031401000170100b142020300891b50005100300400d04030810190030410a00484c1c0e60201002074003103400c0440c07041305007c1c144200c605091100480d251a80e013041822006070030030400403a1060440360300803e050350700300c1f80d4600401144200c08a140203920303084100e080b050b444030124070300c1400001c00c8980c004140301151036241c54019602c0304480c0c0060751545240280440922556201042a2910b071085a046054400700c0004241d9260f082140c552045000000160428207400340014042e00c083c580052003007004080790503003003000c188007071065407803042c4101d0f9960b4104079a44051080c000509000d9900d0800190b0310b032903680d508500f42c00740c003501c0ca47c1c4448525819100343c07030301026040018640062800d20100040c100350810700206051031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 619730566 1250 619729316 619729321
    0x6090c020c040b061213020a08031b1c050909091002070f050f160308250303021306091413020403061404060b0d171b01060801060f0914010b0a05090a09060608 70
    0x2c1c01c80c0030b503202c21740c51002424036035868002e2650908003040003260001c4000c1d20114205106002801e00c030145401c0d81d0404845c01d901035460422054041003440842c032400e02030056102c401c86070f00903001c0d104103400d40c9803104018505100340c40c014928034800303d04ca204125541000072046402641240c0030501c002030310326200c0410303284100c80a4400720b41080040d0701c0201030041541c030301d03110074900c4400010704140050062001c0700065400038000360143c0240f940c0300d02034242460302c62023090900c407503810890f4190284601c10241e250001145400c3c940440b00655070028007807002803011045035000c007800340d030704071086420034201240c0b50070643c50b4a401650011206000c02010940784400c0303600210a5256900000441c2004034009004030380050091030000601e00d4904004003008024540021550030b0804049002d00c400110b02c0724155013000350520381e501c0c8042019147da20850000e50b8203d14044400034441040d87d00c503104992168983c103a040d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 619731816 1250 619730566 619730569
    0x1203080105120a0308070512100501031406060d020f07120305010302030d110d0509010c051e0d02010231170a110103020c0a030807020307080310080c030a120804030306090c020c040b 80
    0x1070a0482841016440583c00f400464070440100d90003040c01e04280789000a4084160170709103040f0746103243d081c49041c0820a80d607162081401521a003801040c00c4d090040c000342c203a1052140c3c0c00591030b000308841e441960018102c40642e88c0c001e140300b0792052585c8014000e0b040910091344240280a091840e450013807940c4000d0701110320140084091240c2d003601c00c0d4000e05189410004024400c0c00018410031007030200c0040101c03a419a6900d840d501440c08601018010459005000c1040071040400c00030721394440b4120010150401c04407400c400d0501648649480700ca41481d070f80003840042250503c80303009155007a00c07117800d03100660980c0700e4034001c4032856200c040c40c800881e01c201e0445812044520550f0701d040c107641c685802d40d0f00186c80c4614030420040040104a40400c00d42d4500b8100b58040c2200b02c00030380b03821070048205c05622041c40b00104c0045c6c00c0510991001028003c1384030100000000868000e40c0c90840100b054003442ca000105801d6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 619733066 1250 619731816 619731829
    0x91406120d1b0f05151006090501051902030927010504180f03122c0c0604032d03030b1806060d09020d0f0f12211a09011203080105 58
    0xa404103502c881032503803501030707030040c6124040381c0c2540c00e505141c107000001441071103c03003400654600201000e04000e1100d4032601c001d584410103000220404002a98120046e43d140c442040c5454513000350b14042a803e51040c0c100c41680444100306490a03100810f845192410030022600c02c030f6078a44041c07004071007400f01c0e00c150340700280350341c50000781d081f0b070b08001030300c0c400d25092101104c83e04585d0152542c1250704031040d008500c2580e5441c0070150745904040c0490000e0141241c1712000c119148100d00006e003c100c031507004186a011442a658281c4462214405108105090082c010300c1d025400c0c620910344030050038107046002c2d103040c5c00303860020705042c500032600040030010458210126005150a0a04008245080030422805000310745c00e2807403820300c0c6402043d61801c000642c045c0b02080056070f0340c0e03d8141c040e14054800c920350002d0010044109518405036203c592030340324180d02c00108048c58280c0c2c20003603840c07080d11030700d01030707620754007002103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 619734316 1250 619733066 619733083
    0xd030606080411010c080f0403200603160c0503040306020a0315061b0f06090b040b010803030708041119080c01020f030403080a03020717070818010e0108160909140612 74
    0x142103680440c021640c00440e880c40700f28141011300f03103000d180d580d00340c06800c08900b040c0c8a0388003060800c207010307449061102014007410b40980d0540c4000c0011154000130344005904001202c50b0740aa5000e20070070700c0d1841c0c002d011aa281e036070300c0c5801c0010354008008400028208080e0301094100aa0740f40180c88030382e01d40034202c03e030046d551842061080780548100c50061452400b0400f00c0c403486178a1400381d4034002d1580f5050070203800700c0f907040e401460250b2040081003001640252900c2d0020b07407260079031086d41400b00000303040b0a100b0780f4900720720310990000034040800080c550340c40202a026200324860300c0301074039140d0003070b480041d1580030104000c6020b030303102e5402080340b41e100d01500305004030039504441c900e8124400440750b440c2c000400403e4072003c0b8552000d13501091904054103004400000c14800014282d214441b003c00300a01e07005001d118500e01a1841c00e5040040314860020840188000e4428600036103078240c0c600203a1601003980748 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 619735566 1250 619734316 619734329
    0x31b020a0215160507050109050a0609050904080705030a0e040e030a120b03250e06150d0911030109060516080723040e01140406050418060509190b0403020d0306 71
    0xd40011540a012000c0300d82c0103441c00070780c82005040c494070310b09582282c00500601c000d080840c03c0c08005807591025820035445100785000401c0200c6c2e01c01707104026a64203039280c2c0ca00d62a68034182d466801001030003029400081603a8500a030b0103a030103901160300316410b0040850b1812040d407a842000f00703140010341c494116400072204c90b08100c02c142009401c0342c0e40119517103080341c40b03204480140043e5140245d810030010411503492038110744110352181c1460107000726900188500148910505d454401400912118020b180315401e00980284400da03050b2500c0e1000700307002c64840007071700c083c0c400500c1e88074800e249003441071049840f600354440600701481c8444141950548000c10108000b05080d80403d820038001e05c000c0d58500c020044910420040d10095040310307000b503290183d00003843c100303d64968019908910001440d0b1200494581010030200c6004079400288003a08208103403450801d10442c040c1d429243c1d9440041c008505542440c800e50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 619736816 1250 619735566 619735573
    0x120a110a051b0a0f0b04120203091f090515040317180108090a120f0f0c0510110705071203080f062b2f09220c08010204120201031b02 59
    0x1c500000b240030034102501d98100442e101c1035010341d25040d181050781c40448059198406100030840e40040442c41e11040c0e00280d0700300641c800102c0c0e00380c2c0650a29141e0403226420028015004210000107003402414200c0013505000b480211540720f1700c812a2101101d25000b40d00c1e0f480c1c01c056034000c8801894031044440803000440f041100607103500403e0281380504000141e803500c00400d80311090310344810305448640301800740c0003402d400000744510084c1000004402180c00300f40d041809100040400045808110364011510010900d00c0340682c04210f80e00c0003045040224443e0b603801c2040c0d40c40104c00100e16600f0f0301e5040d00100a03001346031150f1180b002c0d00c40c03000300065415049149a4850300317101070300e02080b83c158112032000380b15245001450ba0600840a03103e0100e1400e00b010b2050007003c0d8000241001c1c44045414001c111032440c0010080c80c00800a5454a4807814804400c40a0400881c0428a003075204540d000480e50300210400d01038010703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 619738066 1250 619736816 619736827
    0x60e030d18050603071115010509130209040b09010e01020d020c070605040308070b06061215120f0712020102010e03070501050601091d04150b0a080f0f070e0109150308120a110a05 79
    0x1803210640000e0105130a02c5400401b41200000030025488509a40111a07400c0e52510050054817207014201841039414032000d4005a11a950b1b1a42c00541c05080d90240d82d0307900c52101e0041040e42c810083c19400015190844400c50f00a00302102d05001540c4000340c0e01c0300d080d10240700d2444001c8c04240180324a1000c5400703480b0441d0f21940140c011880d105620243c58981442110350039000701c0050001081418403e82000d50394500300d0091920141e005c80c1e042c3c0d1044180300d400300180d9141042400c6904c00e41160101c121500304694030b0310034518045000e8041250203e000442520b000506c0900c4a1400c1c02c00d00300f2640094425142c1d0703100c41446821210817542c40300d031141030b40c020340d440741e0b280c00d0000c19040000e02501141107400c2800c110403d544940c40f617018080034002c440045800c641103a6041d080007501c80c003a800d608100480f6640041c180d980c02017030500c0d00e440a00040b505c2500b01e16010452001c1c0002c2070350705800f40b0101303140091014400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 619739316 1250 619738066 619738069
    0xc03090d050a0c020612181b0f0a05040203090f0c0f0906040b040e06100801050924131505091e060112020f150702090f0402010203090d060f0501060e030d1805 70
    0x2d0442c29014a840b2110303956940104003698007808803041040540c101b0010b01c3c4600d104049840b007241405400c82c2c110410158210ba49000951441900c00180e1170030313540d5803d182c0c4030042001070400e54680c5400b140f00b076120031408410218501030000b40880515110341d0180041200818040560f00c859041c40000c00c040142c103504aa900d801010300b4201c00c0258501c070f071001c0341312a005242440429400d41d44054000f00150f03000c498400c0c280304074400482507003510312460000c0b42e07a410b80b503039000c11003c41c0c3c050200b84107400003110044241e000709101d55111421101149180b000c14010000f051901e4a419000701005225038003448485e160840c1c00200484191404040001c0c51110000c5824460140c0080d049045042c2880300603885600c1e481d200c4007a15241c1c0001c5d450b8030404604034410b82000e00d00104001e00c6078000740010b4182e031420855903840e2076000e881c1c40c0c07050f0500c0d4440e02c0f0700e41c0c2000406100c0c00640c03003900041c44030012642d14010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 619740566 1250 619739316 619739327
    0x608011a030703020c01060b031902070f03050319060306140105060304050c100e0312040e010b04030302030a0c03030212100f1a1c0605090a091505090a2006040e0109050c03090d 78
    0x200303039504040d005c000310b002c0004d003401040c1c0074040180c0d0355035413410305c241030ac00035504004480c03004500601413100030516524042c241d864250070801d80e00ea940d0b80c0000b000d81d55106840d0202890035202000b40030107035011740300c01c1d481d0701c0f4142c150380d80f510b08215050004540050003a8007109166007103080080705110351100170b04042d4a10580800041e05058000d40c0c01603040c3c10100d4100a400c004010860041103081c2403e8605420b50310025160f10420310745605029400116204044c801d82c1201d1501c1c00342000400300d41051400380d01c6040d40351140500351080e403403000c50b5a007112003030390002c002c01410440ca098020701441000340c646042c1c1d00703034090340e41c10001110380b40c0e00310a07840340c020030b080040c1300140d92070300d11481e03a00350300f007540c10038540760400020101c000381d40e985168000c0a40700c400da402c00d4080d808903414050740c90300154003280018400c03210600032416261085802c0c825644d850318220818001152880070a80c44103810f008124001d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 619741816 1250 619740566 619740571
    0x60601110a021e0604030605061e0306070315030c140f090112031224080106060302070201091e0803210112020306073c021618180203060c0c070608011a03 68
    0x281581030303038002c5400041443d0806e078015074040341c0301c10070001246081c06000a0498010003418aa0945c28000c40c2e13070f905000f0880d4003850b64071385c0000c1c820610140b010004640c895a25201940c540c036200b41e021030a2182103018441c42c01a070066440c02550035416144015003440d42140e107504d0494002c410303003d2140a8582c0c41304254000840001c14100e100315907901c40c9412403030b000c45070742100e14a500100815106000200048c2e80c058429021911802010700e0010f40e4110715022842c1c213503002000a200004e01005149a8138100f01d45202c0d4960340d5002d161390369100e6500500d0364050003507040e045000002d50321401500c051142d141500001d00e0f00180003422024008001851242c40301e0000801e83c480d15810002c0352070088030107c424000340c1c07401071540c8000c0600240200c105896624aa0307141103c3d00040c0b4540350010700302c4040f800c240701e00c001d007984a0314030700900c2d0007032820125200d40651340301c070b0480710140e102130031142200c1d0b401e003070a4101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 619743066 1250 619741816 619741849
    0x2090f150a050a0513090e0d0314010b09041e1a03070305070e1812040302120f120a1101050c0c01060e010b0d0504062c060106090f090e03091305010503060601110a02 73
    0x18880e442c80d4051054803170010303003140040000c030782c600b104d0360b240f52481c0381d0b880d0340401d402c2803810300c11101c1042c0e21a045813035280595803030b01c00840000d40605408040c00914000c61114000c03400505e801c0000c103656254032540d0703401c5030300060548508160002038400c2e4400442040910b03c0c50118980c803ca04021103c0041e0075001c1d103506080d030480d07200030345c800082414015841c06516241619a20600910074a5280c001c101c0e2503401404407019010000b040200d00c0358040c044c049080102c8000030049492701c681008042c3d0481451031540758a8010041002c441902d070700d9050b9258594524200319480056001601c0028000c40310141c4401d100e82151809642c8075568079400c545500581030b5503202180b5014050b4010010441214010007030075510180047c20780359220300c0400c442408000803491407045000450b0000c000f02d00084281d001e0b640f00034165235003281544c56540765003004541d54480307031000604503003183c9118801480c0c400040c840240b076 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 619744316 1250 619743066 619743077
    0x80a110306060d0b13020405041a0f090714120a0f0c0c0f05070f14010f081303050d02043605012301120e010e1603170309030f0d02090f150a050a 64
    0x1003000b017220400e1180501c0038058011405003d28a406e000f21110040c082c00baa00c181c40c003440004021904000703029024a6507a00480d140784e00c00c0081180c07c90015180c16502c50b40c045081c0100f500858415402e41d2410365003440b48a04d500845580680310b6460460000e09038071000b1204040410460340d92203500340004440014003943c0d00100101c0a41e5540410308000140c0902603002061007009030403030401c51040300c3c9960141100ea014900252201c0c5009071030802442036030080c01d0814003245402411510040f420500c03054032072824a08242000c1000c010360f0028081c0500c0407510060005101c0960199103042000500d004d109101c00952850102c8600b000311040a9440f00b0003514070f107008104000e8031408140464100c903246856400054201441c0c4040807140000800d508110810a40c0d181d0a0b0f00300d1b915984100c1103aa420007940100880c0d400703616800400515850318a80840c581e6001031b00740f9240443e020f8080750154481078240081c4139 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 619745566 1250 619744316 619744331
    0x3030203120903041a0a081305070605092116170d030f1418070e0903030a090f0c450e070306050910110a0507020f0114030a0c080a110306060d 63
    0x5a841c46180000302444c175140c0e413000d8500f0014001d120003041440000e03040e94580001030000901c04088a12607d050364a815103940010740884d151607644804448a1914194010000ca03452600e12a01c203400800669500302c080c030500c0d00515a0340b900d8200307004410907035010344c004106202d020320000558585a500d06441113800b1340d0041e0445c5a000c40c610004841002000701824040d501ca2a0607e000c1c05003d5803840001c0c01040714640320768041c000c120101c000007a07000e500812806849440c0c4071828017a01e61203940140c00d03d40d0b07410040301901903400c0c00b60130016103516410700e60901c0300e0b10409081c012a981c10750b4807c600c00080811032500c541c0b401001c0b50406095106010224002aa1030603003091000340001c10a25024075040400c85034002d9054030312500c102207000050300d843c007590800c032080c070500204202c5149007a03807051240310255210f40703031151500c460032800c44d21411000f280e031420420210b01a0325240018107a102c207107040109185 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 619746816 1250 619745566 619745579
    0xd0c1d160516080c07030c0b0f1b0a02130905100e06061e2e030c17040602040b0c0d0305072c0409020a06090e0c13030b04021201330303020312090304 66
    0x1035000f040990f800390410f140600810511f8190704004011808106041c007080f480301c7d00c154812400038603452000862000042c00c0d0134444001e080b50018800060107440c1c1d1054006850101c60840f110300504000b031449178580d10900c2e0b000032218009001d07070b580d40803d1010000e004403116546000841f0f05d0101a03a8040d0840c84008002407145c42c1444d921203412105100d5403000000d05003040304844400d030b84101a070181c03228507045a907031500c0c8c0d405c21000a100e5600081c0048400040f112207400c4000b075100c800c1211550b080000390b4451004803187c2d903030030500016108240161420301c0040044004d4040d178002c000040881250b03000502e90803207540300d030006c140300420400642000e0304025510100628002c0d140c42034012103d1900a810300000f00000f1144000c242075485001032206044503000080000c41b1000525861491622074032120344040c40c80c2040d03402009224510450354540c00031070911412404d009043c9600070850502e512081c040010bd0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 619748066 1250 619746816 619746833
    0xe0d0201030902030601260303010803161103030f040512061623041d0f010302030a03120209040e0102031506070b06010c03022e0b01020d0905130207020d0c1d160516 73
    0x800031003824020400030319207d109402d040c0445581550000d00c0100110000030003100c01511400c80303c0c0b8042000c03071810740c1e151040500e0303482d054480842d8405042801c50700410035510100d0b040c903900c041401e40309030303a000129103005c0040c80703241160701d4041c002c03480c1105090094101403082114a0103014541e0842d61083c43e401010b034818009200c1004c0b1442e411404040c08080c40c1d40c1907130042591400d00c604000c040204a10302c05100e010580d0540d096514010320a1000450115006010790000d5a644081b1581152899070600d0240201c622041c0d2004110269980f0800103540405213018241c1c2503000c0c035000c407580c113401a81299025456400f50058034a500001101161034200140d41954000102403e0254000c00d8840c100d4030200ca211900060320a4460301138040c203000250050001c07803880b0304114003005c0e420160350b1a80018101003460301a0046020b0098804040c04c500c8658a0000107100b0720003881c40c80420f51f94459a0075255584100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 619749316 1250 619748066 619748069
    0x9060705010209040608150f04030e10030e0d030207032304031401090b010f0b0316180605090f0a05090411010509091e0106030501080304090f090605191b0e0d0201030902030601 78
    0xc081c0d42c0000c48400b07a00d4a40b007480d0262080c0c03c01040a440741c0485026000c0c0007608400340504190002001c05115503101002c56501070144580e0600740f0390098064550009041d450340a180401070510744a0710030303500e03203d030142d03254400030080200c0c101a031164404407400c104001c01020000c250022a0744146400d00400000d4146035424950418031060300604070064408408020043c0f0301e8050340d4000040c0911501c2c1c070401c840041e5003001c0350540d030654440d516000090126040805040611030685d01a00686021410402000b80600500e5404440c110200e80070440b400340000c948407041c10014945990000001c0f418041161007000000d04286a8103800502c108114018203840c00c2c2800b91f541480042c0351030b805035001c1c5c02c800307a42e03e40100c00130f070308a034001e0352101e508041e040145003051781c08618640003070707000050b2042c2400009001b242c04840c0b41c01422005030b445140165290040104400c1c1d010000d07810141c46010031000746c0e406200460 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 619750566 1250 619749316 619749323
    0x1c14070903120806060a08060f030d090e0c0301080d0503040602040b120103050f1f0c0e040903050306010f020d021507170f01090c0207031a180706090f12030c0314090607 75
    0x2001451442d124020000440c90001004540e5050091035200c0a0640780c1404607420000c3c2599500d1020651000f425801142c1c5071094906162000f50042422010b0f40c040100d00442d907075483d02c10011502c020310480d81c0320b92080301d040b100c1c4d41c86a8090341e0400e00c200b801502d400c3d030710311281a4981052000394139010002004004006040207419001e00306940a84000b903840c4402c40312608900190002d1143c40360010503d45228100c241d1003008000c000300902c980320709000701140c00071550340d40071502c9a80d64100981c0005038070300c0c0038402c0da402010510042d41000300c507540050b01c1c480c14171001c1d2035103581d12040001224454180040b56201c250301d8010140c055540441c0c4a030155001860180301007840310399030800c0b90016012080003510342c8002505141d44050190441d07000c0c08902151296000d010b01080b00d000c0d9072803403003013502e462020109400380381c0014081303510324284000203409000721180c411512a0380324106039000d0082107080d0320188085 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 619751816 1250 619750566 619750577
    0x110405040e1f1d010b0d0206030603100e06060307050d05101104090c120b15032a1303020f060a050d0e120c010501030b0901050f0c0d02091c0302070602030f1c1407 72
    0x18900c01c3c80030001a90544a100083c060b9084c441d002c00c00e2507910300f42c0a8080d443c0040021034980302000100400000510b0411018581065641c4c66403000d8401522038014204001807518200c1243c0c00c1d400e400001030301c282000381c601c03100240380c91380c449942440c6c1032100081348504c2e0320942c02000501c0d00c52105822044004000312000d420f549442000d884299940c3c0607060001d40e030303000da03060246141c0c10700c2c1c004480110041200c4248001400007441400c8000281541c00481344292a2901d403601a1801c0004034040d400701500050420f01691071110700ca504518802d0f030000782070314240c003030210a100c0706a0008622403c42e03910b0714010401c00507201071a42c0d011241c000200242d0a2800b5405106000030381000030500d4003281c0030184101031760450b1314440006191700e45c1c0c42c80c1d207403030035101078640e2000703030058001c40d00001403083c004801c8506140c0070303000311885d000902d10740401840c907100340205242d940302007903c02100c000072a00e010780e0702500c60 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 619753066 1250 619751816 619751831
    0x318060c030e010203010f05060c010b0409050f0d031a21100c02100c050702090a0b04090f020f040b010e150d020d02130909080a0809031603031e110405040e1f 70
    0x81d00355000c44a01d092030760701c10801003141520b030aa14070705488088030840d503101081914140905041030030702d903000b85410707040c0080080c0083e040a0512a00003910710380c8071a41e4080d000c4030003a038217221146130381c11801d03d02480d0100f083c0c0445000320204a40200144003014070f0700450142c4001655602d20241c3c00c09078040000042d0000d14840501c601140920700800500400d00028000c0c026440412981d4825401c640d202138400351040002c0265818142d02da2491400d06900400300d44c164445181071600816030b42c0711040c0c44818020446906014500d17215a480c2e40040d48184072208404412740000c2c000107540381405601c4194050603404455155071000c0c1c440b900d04010200045c2101e405e40c4c142441c0c90401c4d40c13040c1da4003041303241140700f6205500c00c981600d2a400d810543c00d50b0200c08244000e483c0d8081751041d80780701c04211024008034694640007400104281d18098000511800620041c3c8840034002c3e2040c1d6150b800311030005080302e480345403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 619754316 1250 619753066 619753091
    0x203040801060b2d0d021303030e0904020a151b0501062c0c03040201090305160905150105040b0906090306130203061621180c0f0602030a02120a031806 67
    0x51500a4140409100e2a2a0103030780150b804c641058502c10041c100011640f03e905420b10a0300c60101c0041c5081d5650080c6c41101c910010050000310049405030f99521070a0a001b0421481264040d104d41c100600341101c2005001049000308100000011540c11402c00345a004003042d121b4030010903507078181098112054581c40c448080059111044800c041d03001c0c16050b0000c04030041c40e0303940e40700c40c001200d1449854001a04c28854541b18040b94010031030040c0443e00c00500c02c01044d02c5900907428146800f002e991300094042c002404002c001c1c41c028058058002c0100d80b1345045007010a0a002d011102c10301e541f8a04810380007981014440240e2140b40803128100401c600e01005d13100d140000c1c200b003503085242c40918801240b0780e1014034561191404110400024948501c4441c294003034260103003100c580000d21135000000740d0750008a281c01030240710284104402c0c064211640741410503403605070b16040c00d0102d400d02444507004400c08100030b154580b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 619755566 1250 619754316 619754321
    0x4020c01060f05100f14070f080307030c020f030405090a0b0a0612050c0301050d2307090c030e0705092208030c030a140c030a09080d02221d13020117070203040801 72
    0x340700e24016a0100444d005140c0e221034045450017031400c3c007403010700c80c0c00c2514641c0d00a1041c01800d0f58801c96000d0284101c0801442c482c1d9003903582401035131180d49049071544025103224285600500c0184000c0c5081d07034099038015407a20000030885d0340c420000360310040940c0312201141190000140200c0d00e4050b650f884528014500d256516141c040346600c03888110160100c0651244490242c0b10052a8030802414108072002d007603c40c00b0350b000500117a42d0310f5011a241041c0f0510b605004a00d68044400042c406112a5141489104142c2000400b0704c40c40108180040004140c0340155000b15402058240c482c941517810303504540f1065902804907560104100412a20a040f60303880000b0000c0801d0074200d500c0c00042034061721109014050010580c030240a1004d0b5000c800401b000a03e45061340d5034607045e80c081c00d041642d0301c01e03909001e03000469050400ca00304480038418034118448480501035010480300a807400700050300000b4007082000c0090 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 619756816 1250 619755566 619755569
    0x190302030615150903030c010606030b120a08030106050c0a1202030307090b1207032301080c090c122d150f0301230a0e0f061006030902030c090603030904020c01060f 73
    0x400c001484800c40390001000a0783d055100d8105190000d114056a102442682d5804030060001d0160075104d001c090040c042201515000316041c3c00c0b6641c841c00002414402035402000407407569081c100201d4050b030003420412441e00c148004c000c0010240c0205083d20580d40d030295071281010714004081441c9a402003407440010700c4041c61040096500b290094407034140010341150548146200c44d4194002541ca8000e59000041084000c11a1405050201e0381c0010a0380d0f0400340171a81e02420083e1384070680c90000043e010401907018410341a0303d4500e0a45510041c40340c110050000c55110a050100d2944003455040c04220b42460480c214028041006200342c02203101c0d54140030102140c40000108100e2410781d0b011281d01c3e0030440c01e507000540f0510f01d269a41d2801c0d10450b0244410540c00a01c551180c4501c05c100c0b03031f000b00030f4503a4681e8074040000005025146a62500042000da005a03403688020311031045840300225084e4540300c2ca02d0b1407074020303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 619758066 1250 619756816 619756831
    0x305031c020708090d0c050303131a0408060f0405100f02090102071719020d0602040b0a2604060c090b0414040509060c030c16060f050a051303050a050f091903020306 73
    0x50001c1c000081034401514040d80c402c1d100c5a107280f0075402c05280b5205a42d007c10f40602000800201405075101c400e4103490713110030700351941004c00e01c1008030b0744240d100d404003681110b80880c07a40e40c1800101c80d00203019004032004101c2c2241c90200b103448400d1504245540081c04407410f580501020b002480c00b4005020000325006250380c8800417010315011f06507000480004650395100e800c4601c58001400715251030305c410f603444807680803400340d00125030810020324100024440a1550f50300705500c4070a680c0b075581d14040075284a08503042805514000464503140c0172028100a00120032000c00e0100d50b50141303c1180c030081d02c0d0940940100c42046614a4140c040300d80081c0100440f540c3c1d190102c2e0a0880001c00c3d03140100a075080080c0d103000c00384c06070801809000011001c1103140c440300400420000d0442c0001e010440a0208800040c001e601a02d03401d003a2104035840c000d405000102d401d841d241e00841459038030202441982020440a40e00000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 619759316 1250 619758066 619758071
    0x1b03050606010f0e01050a1704080306130606140f0d1406151303080a020703050105070302071403030601020a0206090f06030103051e0609150a060302040e100f02070f0204050705040f0305031c 84
    0x15000f10050524801d40c1d10103040c130500050744180d15209040249241d010484004007c2c2064a8066402c2c0d005a0350244a0100140280615600e41c826001183d102d925820342c070740300b80502040c140e0400d9080da4488102409004030803242030041032260300d00e906100f20980391510800c060b00003582712850038224244803000e0b42e0841d19800500f0349400580480e1501e0002a04a191280581000b4815420b20040c0190f00f80c264001e8003156103d141e000d0107079140311035000d60740d020031104d43d0700503446240410050705103070000f00188280909500d004607c2d482c00326019501c20380c021101503001141c000010b83d094840d04000c4802180030b010b4a0501d919613070f07618500e03858a02e000740400c1020031080106503000d28010340d40944144052156201400d4495030001e04000d43c440c1003480200d90300c84184200c1d410310754028580503920f0415003e20004001c01007507903051160070040801e0100380320207403900941c800d0b130055503a881840d80111000c2d4075041f000b0b04250 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 619760566 1250 619759316 619759337
    0x90d030f0206070c0201170a11040e04030207050f01022109030d0e040e01060501051c180f0b0108061902250803150d0b0a0506031c030b01230a0f020a1b0305060601 72
    0xb030f40410987c07041d04100303036451801d458864986c1c0c010030400c0c100c074000500005000410b101e0a1802a01c20b030300075000d0341c04096403101485034a2800b4105240140c20820251001c03041e48046600c81c4482401c0183c1050310404c0444d01d0051001e041034003240b0741c154500c41a1805000f00344411549100901c41c4e185488000390183c0180384c0014000a4030607006900709001d0307440001da903100034400424400d0181001040821304500c00e60b90b910003d00081645400011901c2c00780c05001c0f6403690145200711010002d4102d83d2000c10040c00d00340d20840303060013030b8038119915400b4006240e540e0800d0310903140c2071050204074600948403548240041102d10143c41c0e4041c032206e0002c84c1c1556038000180c10010740d9041214910325a41f0080300c0c13287d0551101d0903040c82a203500e030500f1039400003d0f42050035240780d803018040402100040c6031141d00c02c114070580c0ba0040300c1806540d41c0d6440f038562803801d40c1d0520090020030030418803c04004e01c640000e0b081c20004d0300c12 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 619761816 1250 619760566 619760569
    0x515041a04051c080d060f05010305100503030f13030611041814160e0d03080a180f0204150905090c090718031e021215060330090d030f0206070c02 65
    0x10b09402811030006451250f100c1c140414801211200344245800704034490300c800c150b0b030b26580c00b4044c1a00003450000019410b4224810050903503000800450501400150340030741039118102c40306143c07181000020005442d8042c0c4030604c168519001c1e10b6504180d401c03034081f1100e946000120f414080004920040194043e41040440010b840c1d000030304282030b10286880c0c1c0c1041d41140c4149000b10505520007071850151903542001c1c0030010480210301e09180f500031b0050204030f2010303404401890a6405616044044c1294440f8960380300b486c00100c07001180c0c800780d50741006603882120310344800304540c44400c508200100842c050541e0040c6012404020140308044003a00e8900780110100000c03658000c00d4910382840d01303821551142e050120f007166245080c800f05410785804034040f401c01b07681030400a81104c25104001c200c040c0010301c0d105001c0c0c1004011743c40e4a81c55580c440e098004d0303d485c89401c030704900091821500410030410410082101e2005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 619763066 1250 619761816 619761829
    0xc03010c05040f0302130e100c0f0905010206180c0303030108030705070506040b030a09140a030302130e062d060d0207110402090307090f020c0102030f090d0305150402030703060515041a0405 84
    0x5aa406580e03c464980040b006c4000500d4616125980c0c2d1103900700300e5282c1d904d5a040b4007000d070055501d04c0e20300c901d82403003595803c00314016140581c10900006000107034070b4084528519582084a4000161002090866200b81c01c040c281e50400541c01091150420a28000308030903241a845c0a00d4214208102e020251081c42c0590700e0329800010301c40c0103003036480720591420030340302140c0c0c1c40c0c07034040c0003540701c008110000c0d0b84c1c840000034030011103602a0300c11140a0801e0074181d00c00302401c50f010030340600c403070200044651100d90640342e10014040c05840700b800141d5a443c0c50500b106120850b600607446030303004010130180c1c0e4401140d00ca0885081a601040f501d04c0246e5280c040d025065821300c144d8070100411540103002c840e01c41c012800e000c20380ba0000d0f16800102d06441c001c8800d05059991940c002916051550003590710601c2e5140001d107068480e80041e00d110b1840410301d074104404501486004038407080f10310b4000c05460f4051616181c4000300d4007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 619764316 1250 619763066 619763069
    0x50f041217040b09030c04050c0a0c2405071107032f0d230102131401050702040c020102090406080a0f0b070c0c03050709051e15210c03010c05040f 65
    0x105464034060401c000d41c094880085800000201d901d460700d480660f00c9a420400400344a8402e26000708a6070074640b2030709000b0441040b226281c040c070514181c80526503898200c40d005000f0314140301c5c6100c1188440e0800011400205103801c1a072030052062040d80882509900921400c200144418206154114403d6010740251800e03000c200303800c00d105051b164100881001131802c210f400c03540c011115940ea100700e4803406803000c140703080780216401d100381b00d900000207103c1242010900c100041e4145080380c80d03c40c00760701140035074070420740080150703402145c40452441d0500603034000c0d20303451000340754601e059242d008511407040c0c8050040d4040c1008600d05501c5500c00d40c4140c3e8112104042070765480c68050b950388000d04c503506110b0f14040c0420301c0d01e6686645010102407203c24584251243c2d01541070740e1002c421510f60114413506001641680c002803034035170807000000b60410f2048102403500707603401e0301d89807010004100300030b10100c0c00c107000020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 619765566 1250 619764316 619764329
    0x201140a0e0304050316050a1203050304020f040b060c0106060905010f020703060b010c02150706050c0309030306090705160c030c0602030403080a0e0315090102090a0504020a0f03051e011d07050f04 87
    0x1860851200d0024114482d0703402a0307406008880502c10000d0034084000102d07181511082c08c0b055135004c40c01c10311070a400008000440c1000803038007520f408004000011001000000e00780e14282c001603d40e84110702e92582039450b0182040a1508684501c0c010082828035a0306411440802529019640030003403e250b612034501110b64421460b041c0d101d40d01906480a045060b0031034420350308105021141070741854002041c0e8065002541e0058094030011821170705d45008110705107400070000410080300340610f00380e0344d907050004041f282c011102d443c1c92a08500703220f420000282c0040c010341d80201f1041000814140071241c0f00d500d240361003001015408000303400d04900a02d07100081c00b00740c0501400180650007010801404c44a50340201e54a6003440207070702811070341d9004996441d07440c00e04a40240c1089a10000b50300241da104900c0c8242d007125041c003a0008100404008083c2c1000703040c014040e40c0000d070b54140142411100900b86080d4440d500070107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 619766816 1250 619765566 619765571
    0x4150b0418020103200f070c0b0a0914030a2109080f0304061809050f090c0a0602030406030b011b050606210a02060a031d100b0f09040b04080c0706030f0b010201140a 73
    0x805001708003407000641d030300442066910742000180b104260040350701660740c10401940000c596200070100c4400409580740d80403232525202100c1c441115418625405020742c012080002c2c00d4445010706c004030307044004040d041c0d502002081500d00e0340207040181d00520890804034000400d80e401c903049803408800541e20410f2101d68048030380d104403040781c280700a001d0605101e000461145456408035104401c00f0410010195082e1117400c0141c0c20030481880020300c06d4019440290040c10a280b820101070400340110800000640711500410300b44a128a400c03543c124a900301050100c8801c03c400c1c52894891880c200300a1003450000b403101d500500940101c030032041103020101e01c00010001c0d150700d84000101c00418203192840c130b04018135000c5103070b0400e0040a04544442d03a03480d40c400841150290003520030f00c600340098545200100030702406400d039540d02056200e01c10904106880010461b1415a4100b413513640c006036034601800d41c403e8641740e01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 619768066 1250 619766816 619766831
    0x50d0e060c0d1103010f171e0a060b0d030903060f02040f0905060405010506130b1c020d0e0c012102160f080d0f0c05180f0406081501080106081209030705040504150b0418020103 78
    0x80340c5002029123901103c3d00e45071f8050483e01d8008280803903a14094801406864480030822510072003080d0010301050b040003080c408220258425050b0b00e400350340040c0b07003984500f442e82030150998003005580b40c8880c108101802d00e4040d0a004010a0f03441c9414180d008902c480428810b00521100e12000f29140c2d90300d0628014940d849100013030110b603901007486041c000f5101901942d5500d100362164503c4c65445070044003021514864118030040c0b0314902d0b9006503000221701100c0170881c4241e000450818601c0da1301c000e11418050b5030701d107010141d440640c4c01c00c0d40c0240d40149040c4040e560140c1083c01c465501c1e0f80d041110700204154400036441620054026420501d44600851580f2000a12003c43c000400b0181c000b81c1c0c1e079581392426a2098024583d4640000d180016911003002c00341140c011700030705480c100d64680c0042821200c00315802d4030316510070701140c0d0048916104140108400381c60a100e040c940303040071200003000c00030090416564026 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 619769316 1250 619768066 619768109
    0x90b0a0302040902070605060f1002030901140c0304060809071409040213090c080706030509010c2102040801050f18010b0109060c0606080a0f03021615050d0e060c0d1103010f 77
    0x40300c010308000c038821911707010300d800c2290042004540031801040c0c500b242e03c643e45051109510403580f95401149480f0502c8011155a41c03105d12000000c541480360800032101400a032001c0e0443d50350304810741c03402d000350601c3d06100394040d10031801512401403554407014425640260140e588a0018481c00011002440c1c0d5034006050454111004295410041030103c00c07240c281d5418801925914071550032507030340d0200700020500d0000c1c00840b44426889582d80400700000041c01c040d5120f00250a5480c11515009424405d104000341070956103e1140f101090100030003e015158001074068045030081c2c8007400001050340302013055942003a005840c40f6825500c5051991801136420550120220098060304c00004811042c4444803000c544404103c51410701d0020000c1c0c0d21035010000382d010781519482c03400d10060b41003020b0740c0506076120206503036041030b562031412100d0501000c41854002c00042014492500000055031030301700500380407000e41d09 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 619770566 1250 619769316 619769321
    0xb0102100c0201020d0b0906060301170a1b030c1d011a070611091804050703020607020a090c121a150a05090d0c05100801030203060f0402031e03030a06050d03090b0a03 74
    0xa4500034141032100310750540340e040d0064a050001c0150601889800408202d2035081c1101c030190040003e01c0104004100000301d10884444007055a0200b94a600d505071041503c184c1e5603200708104a0400411142225500080501510150201e400c1100040d44840184602c10a000d1b80050340c2e4030707908008080b03400083e88207000f008030b106503070b040c040540c00904a00e889441134440c0040c030804c0540745103110355803280c0031f400301300d0450703082145a40000d8800d0341c000495580105101c0464071450000b0b40c41750321000f100300d04d010720a00541d00030343c144000382104110f41400c9030b02d544601e860914441c0048603114640312508607142e0286c03040d00e0ba071110000f130b0703548103000c05204040309840060341d6029000b8400304003501d440c6402c0c0300094041d0b00c16000550940702000e010358100e48000c00741c0d112003c0440700051100c91860b00d0944981000042c001009002d01c142c0f4010101990401038965094070042e001d1000c602c01c0800c01000014050b0a05d842a07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 619771816 1250 619770566 619770583
    0xf020d0809060d0e0601050102010209060a0c031404080a051b220f0507050c0d0f0c0305090a080609030c07050a05150a18031212050606090f220207030f051c0b0102 72
    0x6045180c4441c100b0440101911307128501000d28015800041820f5206008036803880744040d000310320f0005903240403140143c20450640030050680c3c08980e9540c04400244001d0504800070303c540003803802c1680c140040c641040141008044441200c0c0d11a41e4500c1c02c201100c2e440399082c0c405694285014202082850b010641740008001c05d0a0b0000c0c06040b102c40c00c18126103981d0848282501c02c209140c0d13028003c81d44441d40f8800080c07140c8000c0202e0600680a000c4050b52412901e04d4031500f0380382000c094002003403040700364038100040780003004102c9002d11039511303010102d0700f1003002041c40c1d0a500800584800401d00425807032110805100c0441c5001d039407818450301e651008010703600001c01146102a4515050040a0080000070691807a101c00c0000300071041032070500305074000301044205a8030014099082d018459050400359440309146002049409503030103000900009204505010548a412401da090301c0a0001400c162400043c2e1400104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 619773066 1250 619771816 619771819
    0x30c0314071d030d110715050f0f0d0911120a1e0c120b0604050702030315010302252a080307030309140d1106011208120406140c04050117040f020d0809 67
    0x22811848071300c65100041c12074801d07100c01036030705580d103d071512400500d0301c0c49202c0015070700340051801040c1400040c080700451040301403030010b402680c0400c0e9000214162010360001036810564180424000b0103880358001030646005160b40d8080b03c041a800e40140005c1d450306c2103400c02c140440d07034030060400d020814030172620ba80382c40c00314071034122412802070f030410300851075560001003502d0160000c2c0031b4203080301d01074100441c020b401229103202c10300f03540089500d08070103020048841ca8007466803d0202a0100b003180d204207030041041002d42c01c0a24100100d10001c415503080039418600465501c0e5181001143d1811582d400c4070305000d01c072a14a0041d810409042054082c41d042d41c10603070362040b892003558450751028001500030403030030342c000e03e071050b002d0341c801e10843d40010454504140702c80480402c4400e100307003082c002802e024030760b0014400948107411034241803603454541d880c07188107080f0745c2000380201d400b0300d0008100080c0c58140d40380305c4d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 619774316 1250 619773066 619773073
    0xc0604240912080c1606080f0603032a010e0303091b0a030606081005090d0e011103040e010303090f0503210a02071703180a0521030405030a0b07030c0314071d03 71
    0x18a040900f0107038409801c182c01403007850000c50385551400da45508a8000d51114403883d40e4400e034003041100028100c0b03034140400c221408810300204008680e01c0c001000d0f04862103000000d590071910b030440041c0c07840e4414010007880c100b0025201e40c0f216a1010807c401000e10b0700459290581c40d0401005141000004905800700040850014540030802e1116443e841c0d006a150100040150002074041200004550146440c6a00001d206046914140d81d410081e00211400c3e0411000a00b804504200080f522081040641070840240070241d500302e0283c0703814a140c0562178510480880c2c0038070f01c90b00030f000c2e680080998070380b602c03035280d0000c09a80e242d9002d14a8048003000d0780740c0f06000e40c104210540306607180502140d0048007051407101080000e10340600583c4800c0101085d2600c040c0002c04680d4451095405a814400d40103402e8881d00c5030f482c000c01d4030b005041c03004c0300f1084595942040b40c13420b280404101485819490700000b9110640512 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 619775566 1250 619774316 619774349
    0x60f0207051e041d12131518080114011202040b1905120303093004091a03240702030409180302060903031603051914010501020c06042409 61
    0x801012101145001110b00f04024654125101c0441010325019242ca0344501c40310410090b01400a0949510406031548016a0b495187d0014074641c11003400140b911182840c41d2a03150703007090080e00300e20009011300800c400b904210900f052145540c000c0091456409640f21a40500c42c03d42c0080d00480d002c03404070180c040c91200341c4c8681400b079140c0414483c5082c070302200383c030b00800c2d03044007030014014041900141c400044c40c2400294007170b8040e4440035452080240f00421100c02c010445034900b0000c01c1207412580001d40c084c0d0014540500340108266046c03c480035440c401020341e80304c0b503008a1650050790403401d2481e103030908181211042003500306011703101c2e44c2111041e0751100c80706912400242c1c1c4d2444c4110503c1703003d036803440c000e03040703107600035942c2d07001c00101d210f0880324109494090704c40a01c02c8207008010320681d41e0611084500b45d009807511498a440e0054801c40c0c051250030f110300942140c401c401c14bd9100d000d03010010016400000b0440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 619776816 1250 619775566 619775599
    0x14090604021b0708070605040e13061b02010915061202040507050c010c0e030c010203070b0a020315040216120516200a0816061b14250303020f01050f01060f020705 72
    0x9080500a6130b20600c59003000044851044040710147d5034119598102c544403d14043c04680700d105085070850740b6074400300301c594002a009660005c030b650005c210315286081208070741c80e007035003228001410a0400c2c083c620b030303500e40320076015130565000900e503481040495580c0901e2150b00038650802c044080820307030000c1000f02d01c071011030a0380c040f50030a0006a030f607032241e080000d01901c000f40006444000c0e41d405194040a004403412180ca400c000060480c0d0080b00d400c0c1ca0048485242d005100c03800c04044480503850405605e0034070300000c103180510414500511110f04400c2c3c034a03030312a0501141a44200141c08004d0641e1100103040d2a1980c44447c03114101601d03400085492290504a1140140c0404002e0040960311941c01c4508580a20111849070340c8036240c000411103503c1c01e4503410682032109950079803a009003000021183c10700d50340e0408d403e101c0483d54500029044441606220036124601603099051104aa000540c40301d820040161030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 619778066 1250 619776816 619776823
    0x9180b010302010c020d050d09030b0916030f060207150e010c081506090d0507060302072a032a030b0702010e031317070807080705011209050a020f0103090204050a09120914090604021b 81
    0x30340b03115044920060343c48420301c0340c1e101035007410712010610590dc03c04c00720711201c075030700c40141c09940b000d40340c29015290034101100320402d40c8001681c400c1c45400c0b0304420701c40c4081180442c642504582490304400003500c000c51a82803107440c00040748a01aa40c0031240f000d2154071074161410340745e54560240094100c48003d54a90741610700c00c500404401101407458190325814841e914150b4960228640d03d00101030282c01c4004035415100860034104402188510581015464185002425681e42c040540c1045c0e006005500003003207000c241000351a2045000d28416002c29405450800140d21505540c040c80318041010780000c03400105803103080e02d0b404140d01110103840b08407100c2c2080a0003541008880034010726104045ea004580c0501d0041201c18254002401300e440944041e11120b0795280108100a031504103d81007020508060502d546004061400014410819480361618400254603592240d060710954441d20665000c81541c16020542c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 619779316 1250 619778066 619778069
    0x130e01150e0d0308010e070e04020c0c03010e01090206040302060a0207030b2a030c370804060b090903030c09030307120819020a0f0c170c030409180b010302010c020d050d09 76
    0x740364044103400714100150314141855065549a03900d80ca081c006648000c0701903d900200720507040a026a50790314000341c1540c01811000c0d1000044102c10942141e0341202c0b83e503d264103002040001d6600c84041c3c0c1c08981c2c054901d81e40d50001c844040341003001582005110384100d80038071820214a1104a5070740a4511055000c115125500c8019010403912a181d000003040150310020030380188807400310143d008010000304070b4048080442c00420400c002407580b200300824450720707002e804010b6409070794154071410400c180548a01c002410210315141c0040c201440b40c0f003c0003198242a08120340024008a0b0200117102c8102502c0281440011b0328000000364444c0c0308450305500760707499940b02912044415296004180e50503610b40d00c2918001100d400030303c0080403000000c001855032281051410360443c3c0b114800c10340c0408502c4051340010f66030402150550323809003024507100900c0c1c070014945840d18400200540241440d00001e2a08500141c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 619780566 1250 619779316 619779359
    0xe040905060f0406140c0315031c030c1421090a021302070614060a091802030d021e07031214090a0305030d0c030b030c0d0302030c060f01060e09040b0408130e01 71
    0x84040100e0300d841c00422006d840440a042d0208017003015150001c1d03150390700f100c01405480340ba41d400e142c2404c40080c004d00c80303c0800e0f100e8101703078560741c0c0c84030240040004403024103041009103000c5000e116a00c0c014020016040804550072a4040040e000c0c000e9004021402440b00e4410520180d00002c0086440c5401d11034003e13000d1000d01c001c2c510802019044104940c540030b1044041c129604154400c0045003543c00f01688040c4510418001c00fa001008110b58a881d044064200201e1549403a0803500f0705000041610100202c1e800c0f02c1c2c41d0440b940c0c00038a2a0940c644240b02e24143c4c00b501580c1e00108100e0084042d1030444001601000750007000501901660641508294107800c165034a03840352901194103000b2034043d00c11241804000340d40503151071025a070b10141c2d803100030010481ca50380221015444c10044d1901e0880d4101962034a04c02c6a024000902d0500045440302c079407994507036600d00401c114480300d103095a403801c1c00e1003100030300a600ca = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 619781816 1250 619780566 619780571
    0xc0c0c0e07050f07061d150c1804020d0903080c030115141c05010f0504090b240306010e0103120c05061506130f0509010b040f0303050904090c0308090901060e0a060e040905060f0406 80
    0x1b00d4045001250404007544c8070507118101e03941d058204c1d18281c1c440c0d55070610b5190001e521541c070b6203d51000d8940c0b036001640004801d44141800350415000406600c01b4403001c00051202950421011500725114286140c0b0204c080d040301045000c0c69001114040c1010301c1d48446140c981c212504850003402c01201890710350040c041915015540908100f64003c0031425100f5044041c442404405800c003030a5182400000d0412800382d10203036100d000d84005005104240301701d8028000c0505040303480a4180e503c1c0c9485180090250316200141c01c0b00780c0c03141e00c80500326400b145052801e0411552102d11000c9072440074000c09014000c044000300704195080c00f22400e403000002000021807039503404503890f40c08000401c1c2c009403038090010004030002541d00c0a944590310302503c0e401b80d2400c0c010301d00320582c040005c00646e4030886e0019100d080455041d107216140805000030104085400362030b4003500248a40700e0401045214040c0b41806030007144104404e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 619783066 1250 619781816 619781861
    0x2030f0c1611131508060702010212061c080c030a08180604021504030803250314160201061707081e1b040e0a030e040c0c0c0e07050f0706 61
    0x4100c00e0090381100e14103080000d4160300031441c040d030b0840080300014811007070036200011460590300710740703015108604201e0003400034007401e01a040e80301c9641c0c03000310b0412014054448000c3c40160140340034071415041101c40300420024519035940007005c19035507000310005a9507a5101c0200340c0c000400d00b42c0070904000b0448001d21440c0c003071000500003a21590200001c000c2d0928000810205c1008000009504000914480c00c0c0c0d024040f41962902240c40d01d036104504800b404251410349100075500d44e130a2041e4221100c42000d419502c000d43e0281d0043c0040d42150400050400005401d4000020004140c80c1c2e5034003680d01c101b080c010b01165031a040c1c2049181030308007582c4085083c0468000005c0148000c1c07001c60305861401909040044040c1d05078002580701099610500b03050045100d4140c0606c0c20100210807529081c03001c0100380503022902e040b401c0800c603228880d805540d44161030290441da00c0c801ca15090300102280030304411000b01c44081c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 619784172 1106 619783066 619783081
    0x8090304030f060906050a05091506042910080103050706081e040f0605091204090b040b090f16030c021c0201020f13050a09050705070b07030b1302030f 67
    0x3001404e24540c0c10154141d940c001c0031410750074240f0040c080200c0001401c10f0300d640c00d05141c00741d01c3d1a1403002030050010741500c545140d180c50541b26049046a000300c803800c1c0e08807010940707500d26060999000c882484007130240d030000842008032600803030000380d1011007620f0580200080b0460501a01c0e801c1d82c081d203c42c0809c903c44820004503108043d0083d60072001456803006d10410b6203482d10990085c0c910082e19a00300d417010b40c40d40e401172011900b00070409801c52408080c3c08244003421203008001e003080c118504144c6001c0e11440b810344010b035014004640103810307841e608c558208045030031507508228044401c030300c01e00a090203901a80954400781c0ca450200680c1c46201d4200d00d61080ca031000b8080c065810004581450f81d001460301016a80d042c41034000380900da00007a000743c0d491840c000b4201c40342d0b0003103200f203640ca2082c080d41d441c0c120 = true := by decide +kernel

theorem cover : BRFrame.Cov 619604316 619784172 := by
  have h0 := BRFrame.cov_init 619604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 619604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 619604316 ≤ n) (h2 : n < 619784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
