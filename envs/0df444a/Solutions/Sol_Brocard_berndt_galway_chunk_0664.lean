-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0664
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:00:31.743983+00:00
-- url     : https://prove2.me/submissions/8116bfb8-df32-4e65-8cb7-ce0d28ea3be7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 119244604 ≤ n < 119424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 119245854 1250 119244604 119244611
    0x1050102070e040813031509210507031101020d0e061801020a02210f070506060907090501050a0e0406050307081005130f020f01121b14030c030103140c030307030e01030c0c0201080c0a03 82
    0x16041404601d0704009440b002480700c4c48c9082009a10041d9029030310b0356684561050304142e4070604991082d50182450340000442d035140500910450160924081ca0040400c00d14030020030064001d400a0680c440110f00c440030311401c0b4462106c49038050791000c0a081d4002c94a1a494408201c4041b07607203003800140c1043d4800d6a01c10541101e0035008501002100d142040b20700d40c00c03500d145001e42149060000181051041180070018000d4800c0348030040c1e80c40c0d0304103202905020f029141803550b80c0403282c1e601c10182050702c24031801c0c20001041c685001c0300303804d91150460f1209c04940d030507409021001002034580390400264440360101141140504203042869445401040449803401001c00401c40c121800e07018041007840704488500060b42d0640341c120817842c088142e0600c00318980a840550b2540600011a0407030a050300100b0302030ba007400070303201440450301c00b0008454000f01490000d011810900119234071028800160020000904000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 119247104 1250 119245854 119245859
    0xf0403090509071e1e0e0301060f061715030c090406020702100f020c060f09010e0117040303050a11070b0a02160b010e01050a0b040b040308132c01050102070e040813 73
    0x1610410084403910081200c0700203801031110704600c420510403045c0742156280b140300c041c10441c450070b9640c08042011800d0550469035084d03200304010300d800b00c0e034191a10f5031080003410030b05000b141b40390034070344200009901c1c4800034000c680380c900043c0644000780c101810001440c2020b001560340513804e010a400580312100016444d0005131103002c1841d00c20311009203031000e01550302c1d000c2c000502c02c0c1c1d09420215005d960ba601003d0a05843c0142c84000407241c02e0314141107400390900c54400e202c1496016400703540107015910050210b0150025a08624170030520000c065000c04000035071800010303800341440151407000e14000840300c1c0c54000040030207801440182a020004110510303040031684003c0c8004503100b41060300e0044003030440d0203203100240440e40005411443c1c5a421807120b406041d845804c80503e81c05801040000f00c0521b20429240458000108943d8000113a00d02160f4410551b400156526a1068129040000d500f0100004680301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 119248354 1250 119247104 119247109
    0x106020a021e1e03100b010206060d1b030803060102010c0531051e04150326210a0b01110a060906020d020c030d1b0504030605040c08060a0b040e150f04030905 70
    0x20040d410b4250004000f03500044100341c1000b1000c00803010051038804c0207120740c7d03000704615a006808444400302a805804c1541c426418500020b00c10418902e021041200e2000514040c00c0280e00820400000d20000d8915200d41031004c100b40e036031520f40302d400c01403542d4042c6003d42144d10400c0309990751000310303c00002c490326022000d6403d40c41e014060405d072103a052000a401c481c1c0c0d0004d455038445d507580c49051300105d90417054800e818800592440c084405e60351800300701c50b404411031500441c44010545484800508000038508550300c500c003013104c443c0010000e0040002d1954132000100044036040b103042d42c003440a484042c0f0188041c2000c1450074000d15a500740740c9181c0400c655500700307035a500c0b941d04202e001403513500406a41c00e40e43e126500182c0d68403141050004000035078012100d5200340400c1059007007130b0350400e141c202c006031030901031304188022a86d10342c164a12402e50000c42040050400c100c030501c0a5003250182c18a00f02540e11a4003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 119249604 1250 119248354 119248369
    0x180b011e1511071d062e0c0515060f030703030e0d050c04090c030c0b0a080703050c07060507021608070b090f0a1802040e010512060c0a1103120108010509060106020a021e 75
    0x4000f41e111102804d1032040d05005812aa001c541141c1801a80c2c0c84c400060100844911040b030320600070307a40c002000c50080c4800180d03540c12204984e20110020004d051200040380c40714028480d20305881c600e410001080000d41e076254a495013070380005414030070908900ca0007940e09202da48100c4104d6241c91298080707250007103220400107419410b0861400702c0070fa101000751481040b03006040c0b03501c0a900c5400503a14600401c032500e4120a4001c0c40c0034465001d440603160400b800101a00020052658440c00c40e542c050659900103d90b1075518920510455074004c100d102c496240000b1052a0300070001c1420b00304d56103400d501002c0c003400e09010032800d0f0b4002414000100c0400a5600400d0101c80b06d01c130b0103400180d02622264040c2c07030320803100c401188660384140a0340803002c02c1c00e81c0b41c0490351602001500d50001107000c0c403881d1119460701c800306040c0040400d020b810f94000e07030003d003541c14995007403220079480b1150308181c58121203040740c2140d5503080f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 119250854 1250 119249604 119249609
    0xa06080705040b0d1d03040f14041e060603110a08130609140c0f090403020c010c05010b101d0415030f0302030909010803090102010501050901050f040905010f180b011e151107 77
    0x18005a0807495454040305442c2819085041e03606c10302c806c00541c484540c0482c02e80713030880101900b503040040840c002e05526144003020740b40c008102410b22110340d1103002201c0b00ca5500b40030b0806a40c00c100b1080c410800c00b280000ca01100040040303c1c1942002a414861000010081031316101c4003102550079040c0001508004807805040c54204040100c8040840720f40c036107400c20355400f9503145240031105040c48142602e02e0f05021083d40180c190010140000c50b0499220708020300103d202c40046800098041a0f50702c0c504041c440ca01c80b03140031060702c00042c4d0440e01d07122520448060114214441005003020941f00e0340d107103a000b00000c02c02540c44584008c000380c00d6441c140c214030b004000c103400402c699611189001e0504605a8001a100c441400c085001d0b040c2003400c25880d07418083c034440c9000e02941c0c0c0709510350080c01d404140b41d0301c915103203000740010482c0442e0a15034040c18020300a031000390b0142c40b0b0b018100309980c14030742c08005003050b020b43d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 119252104 1250 119250854 119250877
    0x10050d150603030f0f0203270a05030d2309010503040f110a060807020f060f0a0f0f050c0403020a0902040302180601110a0b0a0606050f0d0207020a1d1509060a06080705040b 76
    0x201504072070b130760403d8500c241d0b11000e0018500b80a544504882080d040040c0d856582408503440f84181d21000c08410281001406491802d84004005400c0c003481602d10f00c00c941c88080540142d081d081c090340c82c01d0105070744072486d5480d952100c2c4021680c0100c1964070600329101090140e0394a0041801441c0b1512034482e2860310030000780c18040002c1020260307400038800c000207240c854528a0344820ba48000241d524000910701004003d22704030710b4015854038060240103554a4042c00440340b00726912042c07182c8400c0703110141d00991100940003621203920f40458850107045c3c0d9401101858039a9002d024008403925044c54203100350b64100f10b18091000009082c06200042c240038180140303404480b400c0840d03c0e114144000030030a6010a901046540799140c141c02007440440121084000c05032a820000301901c02000507600b120b5403a0b91802c106002503c40d40008041c109501d161100540f0300c120001e02030010060104000305000700d44801811420081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 119253354 1250 119252104 119252117
    0x601030623040201090302060c01091401060f0803040303050405010503190c080a0b18010513060e0a15050d021e0a0b0a0c1a04150c021006080f010b0910050d15060303 73
    0x1c2140301c030a48280103054484608002c02002d42d03003040d43d800407694156401d954601001c03084030b0040c14002c800400b41d629028115500c03050541102050310285164441c4180c0d46040c030742d0703a9214a11000700441d1042c0420442ca6000741c0107141e12580400008002c2400f09001800f29a1003e4040d0302007400801880782c200c00b648961750700d001042c1e8002281c01001a8010301ca24014820f5601c50303c90303c4078041d0303401c403a600712800034141d25100f030b8850306210a07902c1c0035040304500c070301109480c28000106460141924070407607401514000910114401100d0103000e500300b0250000607002c0000b41c00c0501d030005058256107666030508425480ca0f0122484c42941d52020359401000140004a060411710f0084d01c1f81b0076000194105c40c0700c000383d051a081d85040c0c903580d03151140000b89600b0200b030056102c2102c00c02002010340d09400c129070200242e403581d4203a2140c010502040c01c2030302117681240d014882465891107c04072003020389225800c1100081ca0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 119254604 1250 119253354 119253371
    0x5060a031a06030108030913020c0f03030a050a0204050a0501050a02070b0313020f032b09030c0905010303020c01030e030f0a0302042c07020105090c0108070e04051014012606011106010306 83
    0x100c40520141d00031003110464915450852143d036640078400f0003034461070b40c001200304142c0c5940d04464040701c550742944e0317041401c40d03240b03602d9410844c0d01e044618201000102801e02030320031142681c074010009002c50741041c0045070309405c240042e40070340c030942c0e002082c2d8440302000355128003490200165908000d2042c07058640f54503d000e030003640f00620f54560898080c0c4155000c2c00c0e2540401c4c02c1202c100740c11501d4440b141d00103003101003040f0001c07481100e1900194162400780d0211106c81c00444011012118908400611380e0020700c500303e440b00d0003400601103c80c2038034001d03040c9501c80030b01003011012291024482c00f0a1040d805001000382d000130307402103460000700660f181150b000c6403502440e104007810442604006000c1c0d034000c06056809c404050010415460f000b00b103000c00720494002d4140851600b04151704643c841c0d00c1c0c204500103a001001c2c2c0000341816299101e8002800f06410310002483c05182144104004c40c0203600481010410b1103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 119255854 1250 119254604 119254631
    0x10f060902030105060d111b010c1b020d1b0e01090b100801140d08070812070306080c0102031b010b18060405010b04030209040b0601031d0c100203041809050705060a03 74
    0x544039801226218014001089903035a540b0035102c401820040100707018444040301d01c00da2059071041c082c070781043c694004142c90150701100441e58039803201e111078403050442c01c80141180100952010107000d4610001e290051011070003200030a01e00e118503107607910007040d008241c0184004030313075a0122150f94a004100803480d10348038240300d02c003541808804160354059203511801814030500384000c010300482140d0040b0b810005894440c10b0400100350300c03030800d0300e02c000043e00301900401e803000301007100b0b019403038142c001f54640102c141405143c003211090083c0c041d51303181a02002c949610b00d0008019041000e5940d00d89070020030041240c40680214110b80ba003844188016107450184981060300a0b610071055520200100c000e06a0300c40e149802c004030801c011080d201c000b42e2015132440855a0000c54002c0c4041283d503400313030748201c1c1b00301550703004250340d4103141ea80710108490003a01510354880d100d13008510181c2c40308912400003a60f9419000f000c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 119257104 1250 119255854 119255861
    0x8070e09060f0f0c0c03090607151505060901030504050708030c03070b1311040203060d0c0b07141501050909030d020a0e0909010b010801091e09080406120c08070c02180108010f 78
    0x18258002d669050402d14002056850000c0110300c07400c4000880079881042002a1003030040c0042c0300640d40d0425241078075070100d028042103040c0e41440c003156042d000d90881402650f101401aa06084032140110003a00000c0d005507818010b810011860500a00c0100448540c03900215500c40c80d51a2984030400001d04112341c1c120298801c5000825000317034030080010480707000d0303169201c120014554001d200c000800d07c80104000003110108a405130030824001c1401d25810302070704040c00c0e2204a1100080c4111a0400c0140010310b09a0152600140048110390030b03e080c2c01181e004a0380880c4007100441c501c440c414840c0d00d00140020391140c400002404105403590020300045e1042c001c000f0460b0f20780d07401038440344100080f04c8a040184000780142081c9050080b81f0340d009018180005403e81e41700d071340b03030001d074014130f10741c01761a0786c03058610796880004541d1030340c0031001264481140e464101a07805007d80c403a000e030030400c0c00055032a001281d40002c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 119258354 1250 119257104 119257111
    0x5030306010f0e0904030507060b0a0929060304061503080307030204150c0203060411030c040609060302010e01090b030118021204030201060f05041104140111061603050a020c1e0708070e0906 84
    0x4203c4014080c640c19250340700c009410650604129881c1c400915100c000381404150090b00441d21400000303841c4501d810440c4290118032142c0b02da209941311542c80807506000c101d03000700c404c10200d40050255403001281404001e0028000b90b1a6038401b40d080d401075030508002a0045400c4c0000014004070351050841030810224000060780400e0329084001d201400031411800002f044d510300f4405540074140040c41007050310f031114200d1000300704174001a4001003121040329603a5005038410380a4480d90315099085030728040d020050040000c5900285503000e01800c409046800e02eaa805640710f40c002180c07180c20544032494982c29580100d100d142000d107900d40c82541141254142ca041c8901200d0484a00c00140c486410381803d11082c0e21502c0c08020902090204220088200c3c2d07505118503118504040203070f0083c4021100260001c42901c11900b00c4001c1c2c0c542900d032460290382c940350341c0d10111400e25010380d11101130609083c0800c80c1040040c0019a0b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 119259604 1250 119258354 119258357
    0x5030412110d0503310b040c0503070603020d050a0504020607060b0a050619030e03190e0f03060403020609010e01090c12020a05060d0603111f1115160e0f130914060405030306010f 79
    0xd001d40341e102c0f17101c8000200f03540a080341821101041c180442091f010003e09000740c111503029030b40d640024000d5100280d038040c0c103890000428504995400fa9601494009040504024060300c480009091410045d0350280c10031100140030b40f1800d0140000c80390461607818501090540642034400141094072550403c0010f08519043c0600b82046000c0d00d140800d04c403968400404c03140020320803441d030b1520410080108140d4001066072107030008400901ca0b084a140c0ca4a080e2000c200c0c005151402038881402041202508040c03a10300081003003210603910001b00c2c0b000e074000b803942c203a51510741000b8424070448500189854405880b40c1c12170001344110703c0c084240e1320300f99000700305246001d503441c80b00811825510850405800040381050300c24090030000360075a4402007403050401c41c2952500e0410030025a1024110300340364145101c1c80f90007031144d8441121590064031a0540b801c0c0108159482240714400466407414038000250100310440725450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 119260854 1250 119259604 119259661
    0xd050c070317011a1b0f01061e0503060403030c03020d0c1227020609010210020c070e0105011e080705070605010e0414070b041e030f03080402090903040605030412110d0503 76
    0x802113080390441c1d0607400840c4035194580181101c05441030040e40301d034252600c54406146100001035112804480007100300a0500b95180c40e5080703240c20900c00c40b0b915030091000030340824000e4000c42048101c600c0c0c010319001c84a06881d04840c03881780f40364009001c4100881450013541700300020820005620ba40c0c0074150600000a12150342000380181c1d004540b501c0d05074001c0140404056841c0000c4d5101c0005409441d6203850600c00c89070340040c0240001800c1d4020740c103120003c03042180c5000c00407040c24081e1544c841c00342844042000801c01c000200c4e51900c9254040d002c1c070391350005242408d0602d0f01c88220568840101307034000380401c00a0343e2126044030211500035a4254035004c00f01e0750085080000c3e440941410000004a0308143d40107078128030440c800c842160480d203500c1600c5507039005900400740460400c00100b4082008803c8403000c612052a15000404001c1c1455007054250b00c1010013081c404020b02030812544010603c040c1001207514 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 119262104 1250 119260854 119260859
    0x510020c03090f04150902071214191808070e010b040806041e06050702060901050f1003020105030a0e010e07090f02310503030a0f030e060403050f0c030d050c07031701 74
    0x15a280d1107040481c41c4200a100343e061070985440c0c004040200b61350020700c0403130781e403581100044c0d0700100f8121003060881d0a0108400d0203800c126400385080e5003014100140c0700c010703a004402e801440401d000e0324075544803041105801c0031015000e140c000d410710354940b2010140ca00c2d8182c1106c0c034114010b0209000348000040c1d481c1e0700980018050038295141c119480c4075a0041c0000360840f42802c0410403065000210b0500511078040200302c0343d51803901100c0111401d803009240114035000400141d8801c00c00341d500192003c800003000280e07041c599084803050700149010b6001444100204c00030381c841c040c402484000705500e001384036000b90a282c0b02c0034045100007900340c2000d5840826121004000d01000342c1104d03030f41e0507000c0f800751548c0418805140002e04114602201c6031000c00d03024000c55041d04d81d242400030f4080458013582041e030121207584401d01c85036810760a1801080c0c003821040a94035a900c549060040c005118211031144010b07500004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 119263354 1250 119262104 119262127
    0x1e0512070602120424051c0204031118010506070311071e06050301030c050105071505010602031b030403020306070c1407031109070f0206060f0402130902030a14041104020d0b030a03020a051002 85
    0x1000003212030f417124961407241c800410340d458015101c10194050507880307110341444c603590050090300d000340084060b1000c1c10040180c50308824042c5140029580c0c010013140c20100041d002c01480380c248040342c0d1240140451411175203600c400c00148000640b4018480e58000e0403019010500c0c12034030b50360640d10340441d1580b55101c0d250411000040d07030800d0200103c500208038500400038851941d58040081d5240c001c0c100c0030b99454043c2c20158800c01000080300d0860390f018001e85015a02d400b41a40c440c08602000c0d1100b2a854103110800041441140301031881220000b00c01242034041c015400e40c02401d590500c00c400c2c3c3c0c0c004240f1340002c0c42d20750000f0308449030483e1070700d113201190290003200300111406a0b9005c0104090071160082d5101c2e0006803400c0100840d509049840400e0585014180c1c40000c10904018241130b001007000002412000c100030340420007191428000344415001a00256088402c1000c248010b00c041d07080c1890550810070311608 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 119264604 1250 119263354 119263379
    0x1b1e03040609111f0e011b0b060102060c0a0e06030604110c0304152c0102010e120309280f0c050a080307020118080c0409110901080307050c18011e05120706021204 72
    0x1041c81c28000744070700031641a8030446401490381c0301050010011f5405245c21301c48041c082d11418058000c06001450700681b110a46102d06020b950b040703804c000f03810600000f9400544080d0f00161140308183c500a0741c840100f43d07511280c002141d55a2516494905040703500c01410100001c4207540b1107919002071101041e05115a01012480c51080040c1d0040c000b007400d0300b065010f82001483d5001800016500c6060000256460000b00c030014522150a5a911707100107098807078040e003c14000445420300a1041030400d01258548000a00d400ca1070b50003104217905c0051410115684030030940d52680d868a4404012400d0040c00c2d51070300200d01d074480c00703156075040c01000c5c81a12112400c000c1c102030103401d4996119800961a031748541c10a850a00c1000c2d03104038035043c02810542d410030100960805a424104800900003003006900c0200943c404041800d40d40c1340441880b0308a104c0c001d101b900e00e4603201a040015080c0f90704d541d264180701c200b040d2098001d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 119265854 1250 119264604 119264659
    0x30a021606081608090a0b01141804080f070501060801020313110306040804060e0109030209070206010e07080601020304050f040902130203091203040503030f1003080d02211b1e0304060911 83
    0x400c0c0d00130b951031303483c0e0a03e401d0b0704186c041e00c242483c000004000c0c2d0a44100425400f0690301c04d0700058000c3c421440c103282c00e071030082c4412420490320204084980140507010300c031703d00100b2b210707645070b0240e400e81c1c00984030075044404130401c40301044880680400c004205038090f12aa1610b0f86404400740211300c9190244030b0b8600c480d0f0a160f01c00c03906000610344c01006200c490600c42d600940d0303041c6c00d00800680400602c04590810f000c0c030100780c41440164020742c9450306103400c4c084524080841d03075421a8036100c0b079800682c0d402810480c8400030040060b160b07d8480d490b50320b401c5100c000401d03020340800501c00030500c040220395021400c20f00a101544a810740c000000c40e481e0310280840d80085040344400c9029001890300070840040c07049101501442c5054a50003a01d4004004c00d107101705661302d100c0700b4040c22100021028040d031001e05181209502d40c0704980840f41c4503618600d2004114442c10b0202c80110180d802034404090451000040981003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 119267104 1250 119265854 119265857
    0x60e03010c1d0604120f0209060102031327021b0706090509010e04020607020607150506011106270a08090901080316080c07150f09140a090518030a0216060816 70
    0x940e02d8400c1e1106012a8000c14000708031030400019400c001e00d00035a03c100c101e100c3c600040108410b5840041500c0000010304d40308000c00d0701e00b2602094210342c0f600e5040e410000a040c0105019282c07000d00b250090690200103c00c0640c0745075410f140140d0058001d01c08504018016500d9404c012030656070790001d01502500c541c000119a40202e101c000c0d844400015101d04012303181d441c8010f010701e1403006000ba81c80d481b005440c4903024540c1074060344c1c41a00003c04680c81001042030410482400c41c1c217001540c984281040c2e600300c41550141000500300030030703013443c2c05c4042c0105017034005076080c02c03503403a43c0b6001138102d10405412040702003008880180700380041c0000f0314141e42d8161042030b214002074641100c00b1350942c0840c10f000c1000424500c260500292036130000e10b00d426a5050801480c000d00d40608010341103843e0b0000c100e4040410001003503890300c150010310390710010420a0785902c0690700710078200400d1205104110000035142c0c0074201e242d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 119268354 1250 119267104 119267147
    0x131b0f0e090124060306140906040c0e0a12020102060a0b010c030507030e040207031205160f03091403040905011701020702060409020703121d10020f12060105130e01060e03010c 78
    0x140400540508120700c001051404076640703c410000140c01c0800868441d6107083c0403140e6a14145411641c481410301c0e08441140000764261400390300c000c0a441e1300e0b0610400c00b00010011980c0c19810b6001a28404801d0492405540e0104400d60340050307016002e1022901240c0000c01a9148140090920201207011403c15000f00640341d44035070068811910b5800d1414006d042445100c44d00c810146080042440d4040da215120030585007a1600c600d0303100070b181b0880c0203051500c020b43e0160f018151550f000740d810300040005000442010495505000b02140f1002c2e00b1201c5416a078410462900103884180603501103503546007006881c4c0006003000d40e040161341c404c1410710361a050340803032404019000000020010021140041c801003440d20403480340030074810000c41c2c2030100820382c0e018003108550003003040c5002820202c2a44c1d03038500245281d04000035091944005110490780300411900c02c1e141280280326500110201420090340c0a07007500c0240300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 119269604 1250 119268354 119268361
    0x218030303042022050109060902031512030c1e0f06011a030703020c160311010c02010c02040903020c0303032e05010c060e1c0206060418080301060809100203131b0f0e 74
    0x254107101c0007440c03111900c64401c061019805400400e007d00850303215501e441004540014507100342c4c1d01c5400750000350301170000c0050801004800c440e980490603c800c000e80c81c0c64000c00c1c0040030703003a107004c42020307189814400390704d0510045013200115070384010b00402c405041c0c1c41181c0b120034502091705a41e40c4508004a01911402c00e41c61041e00c079a0015002c45c1140d040541c040702d010301c030005601da09090044442066460002e800507075180e01c050050f141a80c4500c640510a00441c0e074070503010030200381550001c41e4080515000d643c40f84414402407900d946034110b1035201d00285900f05400070f015445c00610190031181d544d01d00c00f0390080e0410081041d040841904901c044811030001d545403403c44110f4000d0717007001c5280c0e207072521901c44135194a9020441034290380c00c0060450303e83c8401842510280b244840310080f440702c42c0f008500882080c91000900340d01383c28401c2c11100340b48409244040300307007003c1000030454003c6c2810f85040c52604459a00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 119270854 1250 119269604 119269609
    0x40303021809040b0603060a0218190e100905010902070201081528031407060207050111030702150405030c1203161103070905010611010603051b0112050403020102180303030420 78
    0x1400c5803030a5400500c200184414050244c1e0180d1040c007044080700c59540d28054000281c0c0620300110380c13480803100400410b8541080765100782c03150386418650390713941c1c0d40d0a282241e03001c0d210039040c691030500078001048076005182c003500c8012010b40c41c1c404560300080c504003005020041500c400041000540e444058010326480c05948408000303011404012052002d440215501102c4514514008601007032100858078a84c020300901c516000c01960588030082ca490154041040700800503039807880b0354100b04109a04541d199400e050605280001001d0058030698040100605401d0004121080f1039815040d141440c103513403400010302503201f242c86505005034000440d044029611081c101e80c11030303880d50040e004d0319031200d00702d0340b0038040941340707400c04640500007140040e840b4550384410f00d40341840746805410b50341224400d403411030040c4d400082c0742a08005070341030b2002e1000100c02840c503604080d510381c1180038001580c89100d49540183d40d8966 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 119272104 1250 119270854 119270887
    0x20a09081b0a140d060f020901020d0215010e07050c060712050603061009020c070905191b0210020a110a0b040c0b0903070504050a090213050702060c07081c02090a091406090f04030302 81
    0x20b98010801d01c07001c0d541b10200700180d04801d076514014481c192907030308054400107419051180102c0d201803542d00380300c00002d40000c01422072042c07141c02c01c15070015840800442e4458010365550701602804190407106a0300060146c0d44258894001d0110654542c0031202c103c0d1b01c1944016555000c032481e40341004803980c4000082d41ca400200000c2010b02400800c009103e5401001a240007141c1f14000c44c40300c0d070114005900c8082c0095052480303500a203d0031245042407150000114400fa01e8001c0e9113108950401c500c0003400b040000c0c4086081c09805070f00340e40c0c3e05200c40080401d554503080e114151056441e00c0108041c2644c2e42d1009504a80161001001c01b039102e50010203840b05035000e03401807255000194021030590192010268801c01c01481c0c90300d1350007883e00c03080e41c031885003132115400c003c5408150380c1c6074880e5000785038a181c0802c00380f50508421740e244000400ca14000e111003020042c482c4004c6103c246d0165050a0050311641800c1001010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 119273354 1250 119272104 119272129
    0xf0b0f1207080304060c02090c0309150601180312030e0606030309131401030f0c0608070e01080402010908010e0d08060a0302010503130305070b0112061a01020c0d0213020a09081b0a14 81
    0x9400002000f045c610b50100c03109003040c5c000e49400503d0740701c000700141c052004440500c00c03030700108054421000c0d404601904140c05241c15115829003a0780c0c495964a903900032a804e0101c1840d052400d5003500841580b14180005041c2c40e25207140401d4980c4500d490071445404950b40f5600800c0e44c0d0380c45600710388120310158a540d80c480c50403c10640c4c2c25030303040d070b11864800c0001400078410182c0314801c136290341c0c031801d08500b0400103480d03850000c2c100b00e050115001012420f21000d10640300038184000040c007080b000a030703001d40681d401426031401402c2c1c44100b4009030342c1003401c41c0d4202c2a5040d0b14034040f00715003400c4030316001e50b0100a00100140c0000204e00e1006030007100700314000c02c010400c040f055200445242d08082d1041d000d604220282840ca2400352184000075001800100c0f04d180010100d008981c00000c0d91008140c10300320600103080c041215458103914220105d541104a40029512045a1140246d43d0b101034031071070202d071145030150f110b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 119274604 1250 119273354 119273369
    0x90f100509040f0f06060e0102151509061c0c140613032a030302010204050a23060d02070507090501030302071d0f060a0509040b0a15030308060d020103230603010f0b0f1207 76
    0x645c503140d2600410300465040040d00510849010740c59003800c51100e03c0c0114000001400501c61070024050701d901e000f0407559010f40100c01203108496190340200340c1612440340303408801d04100c03801490402c42c0c0c2e840c80c01405c080c44400e1603c512040c05100b0381c0d820455441d981d40f070f80208003685804180540743d64080b40f40c0c0001c100358054018100352001180d500c0f1069442e200b124044040e070201c20160400f020b9030322030540c10b11500400c0c0150584402603d07003221074848034904005a0300083d05a980e070b1004200b03042d8144020000341c60b014195440707484411441080201c07010b001c080344000c5e48008250181e0b11072512030020b280c003908507002407500341040156103200b1120400c084c1e0074040501c22901c0591404000d8907895103e2501c15141d04040c00401c3d401d440d000c03418150395640e6054405007041c04034903140b180a0380b00c5a00d10b4200145030030f542c0804c945400c50b40c00e04400d1003050360b500410b511401015180c40405409140d500c620382001c4e40e00240 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 119275854 1250 119274604 119274611
    0x206040b101208070c1a0d0b01121109090702030901050d2301030b0901050108120a03050a0207170a020c0102010b010e090916090b011103041d09030705070b090f100509040f0f 77
    0x2e04010028014002043c000c1100c041d0321a5505094200d00e17080e0700d00b407540c04404101d0000b4044070755001c10701d4218103142c43e00c10300780d6010a04c0100d078204010f14a9150010800080c2031401085650b4088404d00c0603504002541c40040c1c42401803410790f07a01180c82d43d441d2841080c8240c24650f401c0811595084a075a480c1860b042401064541c0c41c0c280d400c080011899040010b2600703540302e101620f0614112400104034002d00e0f002e4008840580c08000310400308010504044145c1d614141c030726525450034101a00d841e1185440d40c1c15a4100b032403180307083c3e812035444c1304c4a000070303165442e09646041482d420882c184082d408201c2112202282100c2c0d203912504003020f082c0c0b60205141585000c031962402544154100d642c0d4405c410008169843c4141b904400d00b803003128100189991020f04190150b04034030014100846e1441c1ca51510105040040c0002d4540048607643c83c41d0041a40c030660b036101e03005607112024002a200943d1003150004c1c006503040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 119277104 1250 119275854 119275889
    0xa15030e06040b160e0915130603060c0f1b1e02030a031e03090506010506160602040e0a06120302060411030a0c0f0504050f13110f091906150206040b10 67
    0x9411034802a2640d10389004410342501500d40100100c0301000401030006c9403d0f540d03244d0a80a8065086055800c030322100c00d40c82d02d48086014001c05503200d080003040000c20418002c002c8580c09106004010400300d90142010a01c0500440300d03400c003d2a6180320758058030719901c820311340e500a4252241e448407009250b44800310000150812000303030718074030b00d0103011420740c2c008240181940d000400104010718002c4d004103620806501364040d50841c685411003242c00a60003c00500850010441d81403118480c14025004c100c20600324030f180c40d10020742c0c0d0303003000340001d000030080100307070303640355400c002002015074001342c8802e611383c403400c4200a910b03041c460130b401175040c800454210b2a0041c00c0303034800c540c0c144009030302082c640c55400d840d40403808003d40044004900c84010744814505501c43c03008000825010148000104215005036002c840c0c40020490f603145115030100c2d940c0d4215402040d240000d440305415002070f401c03160705c074148150700c2e00e401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 119278354 1250 119277104 119277113
    0x5040507170a060e01050d02061207091a09030c120606040b011806020c040507020d020d0c0c030606060c05070f0b090f03010212090a0b0105040606050f130b0412110a050a15030e0604 80
    0x90b009462207015820505e0341e980041c0500a255100c000f50301c03400503c1a04c110038000f01420390702c080e0600e401e2101380d507140c03169044004e800002e44c0300400c00145080316400d0401503403034009030030703980042c182c1501c5a40c55140c9101903c00b40c421500c61007203c0c09684100c1d10f10300b04400030794280702c20035652080a5511100044014051810100011545400421075076510302d01078019200300e410313418084907101b100010803152124003039000f00c00301d100d9200b4000038110a460318105001681001c5140400580c805010740d0700d500401d002030b590440075607510f42d009681c0c2142251800340082e0184c0910000d142000000d8001c00882020006040e04a1801001000c030030b80d0321003007070100380c86d01c40c06004042642040584458505000181295080c0700d01c1d01d001c160f01d503208002d09070f000b0303404480c92454951110b0280140d40d100ba0701c0306041120010f141d5403610b808034411035814820755000a405407a6980543d002e500203490342038484c1c00340d502526261a2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 119279604 1250 119278354 119278361
    0x403080c0c1f0e070e130222020304061409060417070201020102070b0a02040f0b04080601060c11090f1006030510030303020903030d02031e070e130e0c060c0d08060a030c05040507170a 81
    0x460a607500c039138000061070902403d1401d003d20000c14507101c00742c1c800d03024020380e01ca10700c403550200f00f101c110407001480301e44080c2d4081c0788182d4010500094a10301c40340210710103040e291850304081c0c00c3c4000500707011114180241021801900e480440c00183d00a014011000e002e1040ca03a003001005080343d4028419207071000c500e00340ca5619030403044c0d01c80c0524040c00c91075911441c018400c0c2d41c0210700f5980003512031580c1104180e40071000c01c0071480705032070518944904d90140012a07001c102054064901d40ca0100300303d140c85541042ca08030030b0b1101030f0505500241d824000e0701c09200b1144030340710400342036541c1e0624603441e80c40405034024603402ca803804d0b00440d80fa10702c5018280f16119005207901a814502d0081070020700020f50301c02d11a00c1400740d00d92711074a481025220858290025000e8007251181c090310592008000c14402c403070b110310520000e401606500c060b00d02c05d4800103080c2e0b440e054261103c2d070b400d034124010504a241004003844040c3c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 119280854 1250 119279604 119279621
    0x9050106080d05040609030605040606051003050106030c030b03060c03070c05071811030405060402090c090a080c030d0306080d0302071106030c09040605040b010c06091514100e0403080c0c1f 84
    0x2000c0700c1c2c0d21649414200c9290045015900000340b032040100081090b0b40c000d641c11070302a00d030001d1080e5503880000c620195800c40136000c01c1e01c030001041071540620030400c480f00c05003030601401c2100d5001070b0300da0000901280309402c002c03001c00c49151084140c6404250b100d81250000e0b5141c0051511081c0f038200031000c1c01c0e040410700c50300c4411a1060324003c80c2d02000600540c1c03a00d50812454490080c0301810011061200c48115034403100c0d02d10050001740003400c1c44207640414141400c0010f2881001d1504084080201703842c00144050100140c1c40d0040c1c86000034540150800328402c00c40d80e101201109100e1030f404210001c1c000100102d40404c10b555481c004c0c04280c400310b400c0c090104891103425170114000d6044210000d1040740c010340030309407000b216022612407800f004000d444844c00c0044200606d030840001d400041e4800480d4501541c004098413001024032441800100b25120b07002c2c0100008da1b0340c2c195600d07000c044c0c16000d01c1802c00600411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 119282104 1250 119280854 119280869
    0x304030b150a0e060f040f0501060f09051509060f090d080406080906010e0610090509010603050f07020304030807060b030115150e0607050a02010f140403200306090a02101209050106 80
    0x250206554541800e140b001c452114102d0015036460004100c0e00c00c114820340303900151102e200002c3d0200611506001e00103a8035165a032440c0c001000741000c0c00707500098000e8150040e0129195603000903a202080201d031040d9403240c0c0845d110301c8a0140071185600090807140c51003c01c28a000500161202941e03101c041d40e95544486036140001e100300038001c2c4085011400a0410b10750402e1000881c0c01c01400b05959040840c140381c0e4242d10140002c1e41e100188040120002000380d000b50301440110f0400342140c0b2450303038510410400405641c1c0d154200c5d03c0c103032020740210202c2c1403180c040144060341e641c010054494071a181400185110f030342e180251a2003070941da111600b1200621041038a9401552212040305600c418480036100134080000c1e03190040015522608129403440500b00018000e04103c003c42da10a802c810100040d1200000b00d8000c41034044a00341c2542e0600380043e01d8900801c0d20249900382000d4184003480b205401000c211002c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 119283354 1250 119282104 119282131
    0x40510020105100b0c070305031201150c080307200d020c01020d03151205010209120307260d0506040605030307030215070203030c0703081b070b041a010803090409140304030b 77
    0x42504900b00d92003100c25091844002405000c2c0d00d4003040907048545040040305d45581e100c3c5c543c1c4d8a19080b50721a10210540324006008004084105200203109414403d11141040ea20407400340801808481003000402ca11030440c880e074903940b501e2550706015a450f4404602d0002c0d220300c9030503a2a4058440d030340c1c2c003102c0345120f4420410720000761500c0c48e50072030420801c038014032040c0d07800f9501503409100d035404036030f00d003900030382e607000854003c554900c0c0e00d1802d1503034108640c4034620125890354040e00100c95100440b40340ea0580503002965540d40300c00030700103080d10340196030107202c003041071000c040e00001d5041d0554003400d64071003d5500d00000b03da90f4401200c030342d61000d20622115001a0003000300725008040c00c81902007201400310008804d8000b4042580d0780b5110303800784024404a0700045030364850b68400144903606186e107460b0ba0303224901106002e0360380d605c0b4031400d00460354040407110340c2c202e043d660307100d60300e0504105104098600504c04040b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 119284604 1250 119283354 119283379
    0x506040c140102030a0c0206070c0b070501111204080901020708101e0501050d0f050c091312080106022503020402030a09030915081b09030d18050303090d0b06130509030405 76
    0x866095500c000380503030003903242c8020b4803030446c4c0602a2000403604a0700500c040d100007200a10060301800d001d001441d1196194185107003034800e108210103009104110b5001d1506022100903442900940c0319aa40c0c0380b1040102e01d090306035840041c0720700503018a0540307041b054011411246482268003420840c21210100300e610a114459100400c8800000050400442402ea69002d03005440044a100c0e011490040d01141e8060405819000580820071080c5921848003480d1030301c261950b042c40c4c4041d41c0d80020091040307030305042504040800c900c0f04d184d100030b0b44e400b4105640368104000641c0107401403a904801048400d1400305041e041c080038013602d500240e6405001d44c176142c00d01400c020f0601d10a41003078004000d5010356450130407021540741140d0380d410040340d0045290341010906c0ba04094429001085544c100d5a05e4046c50480c5e15000b180400b01c0d91a00800070308080d51a1140e07541c072500f4441001180c04010024004480302514001e81014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 119285854 1250 119284604 119284619
    0x151703130b1b0c1003050408190206040204140702060403081512011409030703171302040c0e10021f02030907030f150b090c0318100207110f0301060e0c0a1403040506040c 75
    0xe0304610003580124400d510380f13440521a80010340c0041c01004018035000c016405100311710790320700c68800581e000c0f005100442c1014414818001c00c0210440400d04000350001e44650010f41701504100c1d003030000c901d400f1040385500010f4900240841c40c82518141d405019280c106842d60305c40c852440003c44418020040720580c0f5895910212002400300030030000307080241c1561601d15a0804040043c0c40b58414101c0340700e425200c9a82d1003008400b00301c184002c800c106170854020300342d40c0c1c00b40342c1003018080e07015038603032400f50f240e681d01c000a601d40001940090300b428200a000400e002001c450075281400008003400250144800d0140344e00c0c05480712070301c40208000160413000f0083c020780e210541c40703040d1841400c840d81e01e00c040c1d802101041d10078030000012240e45150440890081031803c0e0001c0c0091854207101c48007403003004200800d0480e0004d4808950340c410001c54141c014004030315600c070704007800c080761ba480045401f03c64003c0d010b070300400c2c0720 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 119287104 1250 119285854 119285863
    0x70315050114130207080702090103062412080706091217010501030209010c0201031e050c04081b100c03170106050a0e03070803040b0706090203100e10151703130b1b 73
    0x2e4501401181091800c001c044000f54081c01c020384401c1010f120560040c0d45140b50340b03008500580002c920560b884007504c0c07aa584044004a5030303001d40c0070030805002105941210385400403641d581380d507039074144000909003c400051415a076445181c10040d00034440c540c0090721302c1c0008103640c1c0c84130010b500324803d41002c58003003800c1e1544d540041d842074101c41b825030f040380d036210050072520313035801d060f6407081e64600c0f42510082800d001c0f20408000030004030482c601108141141800030031150542040c6103c01c00c6440d46048083c58020001304808200c5504510020341c0c0d243c0d0020701e1a004043c465000445d0224120524a000552601902c680b50040c43c0741500c1d00740d501c8020750000c501103c4007070f200c003550030240e501444038002407800021301143d0000c01074801400c0140b40c00b000816140b520000c0302c0d010072094140030030f41e90452440c4024444809103e071960190040c05480300c02a8180822000440d8020f081c100745038105142c0d500100e001000e07181d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 119288354 1250 119287104 119287139
    0x207090902030c100201020c01060f08160e0f0702070803030709030c0b070c171207050102121806070e13020a0c0b06030109110402090f031b1e0f01080709080703150501 74
    0x1a8028a0860f0840c034084245a080d0100f0340001861b0140c2500700b80e0039207406511500800311440010090701c00c091000e4034514410035200c00c00c071820b00b01c0c80120000042c00528a40607900006031842e8000c004241c081e2220301c0490761070f480c0c101001416907800380004c9401c00032a110019142c03807138a0549407813a0380715900c00051810b00e17440c002030404158019490b8070441c1641d090380001c24005040c620300440c0003507514810507658194041001e4603a0411151107d000c0c08040701c045503880d00400c2c94944102c081c0c910a00040300b85034243c9080c00020b1000658054854022514920140c443d0107558065030f42d4034100742c00c840951401074515451500307030403680c0c9002c0c2c2c01401c100f280105801d280225000c046032900108110014043e65240245010f40c90702d41d2040c00c10302c005104400006203848041400424182003450602507000007285215000b0070302200941010340844800540d6802c02002085050300407404003803803c0000b06242c00c04503c0c4919 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 119289604 1250 119288354 119288359
    0x1030507080f060f15030103050609030901050409022a0d11060601120b060d0207080408070803090109051c05011a040f14040219080625080f063604030207090902 71
    0x405954160100582403001040c560707110810081300318099032001c11411000d000441441d440758110b141041ca0808054001e0b50298030074414019181c0e403100c01c450580750340c014007507101c008403040b5081f00c0c04000e6085407001c80101045901d08400102407404402c25500c2ca400b14107840596030b242c00341a15424000340035002040f0031181d040e0466541c400c0003600300d52030400540400c4c412600414811584440c00103010000c01d0740401c40400904050005980307040f0940b800070f80b0072580740c42000e01030303220300440d0320301c00c203420b020403400f960800001c3c0003036100c40c5610719541d40c01e6100766124514104507007520818501c110190302102e90104010307600c45408002000f054030354054203c2d0407d11010680c65800d202c0540103c5100407061164040160701c00d8040a40d41c00300c0c0d040145010810032103e0a419009070840310680d20507051840c216103e4265081039445c4050040340d183c0700300441d140110010380b15034001c2d825110050303101d88025047d5802940080d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 119290854 1250 119289604 119289617
    0x5070f020115060915020a1b030c0f15030519110a0f0903021e0d0812040b090303101a0405090c030f0c03010b0f09060c01051005030d02010e030d0f1410090b01030507 73
    0x1015044504000803440170074012076030310001583c0c074447c0c4a4001c035100a01840032000810400414903140c0c000b90841c5103240340602c1c10308522007218408038001034209611500410101800c00c01c10b08528020350000f405031004d07400f40d480e2207a2201c910480050303030f00035404038041c1c03041c02414280c0394004c00e0100364128a40d0351855414059001c250f00101c1d03240c00a00044000300100780740c0e159007480b0429868103003440144050020b1060510390030400400c070340d4015540018054401c0741d95400c0c445080b02d03d28802c140100e41025402503141c8041c000184a00806103101d000d5800c0009115660200a120503000138480c504290105200c003482001108000d41450000644010f0030010800c1116003944c10564810089241c120701c1030006007018020945100c007240001c0c00343c04080c4040d25a20321403801600401c0d076031664070005001c0c1a40080c900700c10751880010250814140c88601d040c04c0d441035224042c0303441100d041c0c55001380941c52150000d034580c4c6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 119292104 1250 119290854 119290859
    0x1006061b0f060b040209060d0c030c0e010507060e120f090a0f0302010503010b0f0d020301030b0a050a1a0105030c040f080601061101090210050c0a020a170c040e0309061b0105070f0201150609 84
    0x60050030b500b8050f5a4819028400d40764030391141c80141204440c0c0c3c02c13002c0b580c039003c05000b90484010074072040c1040700b075091414880e40c00c4002c5500199020380b0000348541200081400d007140407424000500e40011002c1d00d030b82040d8050000742c5002c48504001568907244c0d1403c400035840000d001c00c0c0e051004021903449080503085a035412000145440c030b00c612814201c0c0c2c4241c10071a101051481405074518141c41841c4c0d010780001010001851101031394812021412000b904005002002602c042405000c0d42c0c000c103c0c070040158095255061a0380b206800d0080300f001880444044201500500442081c282c0141c00107890110440b02110340b80d0142d6070030f007000d01c6005004001a00c1d0000c0c1c00c4014244003e041d0024140300011500307014862054a1042c1d0034500c0c5020702003000300494162400803101a591a00100c1c4490010342c0c00046690f5154038240420241507001041118140410780c020044000c08209124940c50036004110000b0000f0506 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 119293354 1250 119292104 119292113
    0x50d030503091f09061802030c04020702010e0604030f050d180501030e030903062d0105151621080c030f07030f0603051605090108030705030904051302031006061b0f 73
    0x3150898898030070345442254030064440440703501c0341c2020001c1e661354940d005200c02c43c0b088001d448000001d54041200940000340e81d0b2410a854620455000544408582c095446080e980e48003420302512103a80e070600c4110313590003240540f000c0c01103405006038244980309441030f0580866600c6659820100110b0040c6a05100c48085100402400046a5080000511500c4404103550384142001d026030030031500e140004202c81c0a400050190b55140d100c2c103005001002c0c0c0807900d521031039847c00005222520054400019004010b400c3c0200034549200c4a2154480031031607250002c04060500c0211008880c0386c0c072200c08075080d14440c0d000030018408401001c00c0c2e403610782d1035031401c00c27030342d001410490503003250300700031030305003256001d00400011f0007641c20001c0580700c082c0c907403140400c460b12607592600051036070b0103440307000d40d151a0042c0489030291205604c0b140200b0240c0182c001003030b122032081c0303503200100c280d201d06158070100c2c0d80c070420380c2640c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 119294604 1250 119293354 119293357
    0x120609042a05040515040c020a020105032a040f0e13020f1003020f0c07031e08031807181d01060602030702090c0928050114030402130f150504050c04050d0305 70
    0xc0480e246003110300004050f6254004d00b0b001e02102059503400c86a007200f0481118184110003056400544042d800f5130b030480d059a1740900118401407800f0300900c0341004981001b8415130320100e0110740402c815071b400c0600403d0f142c041d41c1306d81c042c0c6c484038055140426035000003584a40b070f800c035808480c10b16401c0401b0f0400503080150030004805054042601309420b0040380350302c03a040170428003281c0d025203502d030b03283c034841382002c0c118a4a0785442480001d00161700c0060411100ca1407103400c0007840300408602c01050300c030f88070254000000e048039240f000e200d54054507154609407010b108001c100e50464004519261442d401d102403408020484034001800b8003c0b02d0081d141d00c1003868491f0000082002c03414450304110b90890321642040c0d04101d0400000d81e5101c1e4240c0c00c0341c1c0c2094040b0341e000403400c4001040340280180c05010000c140c140b451034220180680c40c5041030b20003c5806000690703d542d401c4003640950300c1000d03405042c0c00030300c41c0420f01400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 119295854 1250 119294604 119294663
    0xf0b040b0702031509010b13020a0203160c050603040b06040e0d0509010315030501090b0f0a0e030301090207020d050a08040801060b31122603060a0308090102010b090405010212060904 81
    0x80540c0d04000e044018042c144038100c507041c4040c7d444000501ca54689032545242e4103120441c1181441c2440500941d00c2c040ca1421000101c0c908101c1c2003881102001c1400610740101101e540e46018903000d0744005054641a0003581480c441d4482c440001c54030101401032a500c4c1420a207030100110082c081c074021290014004c0b840100100e1400e004400500740140000c52032410100c060100c4010010451003040e0319010400502840c04030031a411600401e00158032030515000103103841401820003007042c800c008501082001c0040940216100c3c0d5000704403160303949074180c80b1840380302d190200828050202c0040380c00310f6900e20070400c8100c1e6543c00500c0c0c4500043c40381c0c0c0301d080c0c03059680002c2140b0b2815480e0280740d03900a40fa2608142e02e086003451000f00d20503280710301009040ba600403a03c613500740d00c03d43c0100707000100144815000d0403c0d0078014000c0d0b00c401081c176000031003280040e80c83e003444603401340103682c010031842c40d50070641b13044011080d054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 119297104 1250 119295854 119295859
    0x5060703051b03090a050f0316030c06140a06060e010e0307030204151503020706151d0c0f0a05040801060501020304061205090109080c01020d140106090e060d08070c0e010f0b040b0702 81
    0x81d2031820b01218000590b100e004001e0041200b4800d5081c81c901c1e14510500b881e00b1a8403c128091102c040c01491440142e81402c1420802000c0c1c0b81040c041c101a0f56600c00201c0070781d0401405800b2608120221122510740304030781000341004440a0001901d16a015804160100014141540320150b40007803002c88108503074a8200e0080201d04d5410031400103a00032030944144166031259040356034420b110748030200c0c0351114102d05003481c0d003881015103108000140b14808140215048481c00303420455503850603650141c030642150144449541ca010390208165000008850668a8a8442a00c19501c00c88c8010142c4001426510300c3e549030417400c00081c1c440c070003a04d5014036890015072205040c2c00e00320b0840c1e10744441c40485101d21001004001c1d0400540750035519187c080d04c10b00d0381c1d084042a40c241f2011801000310000043d69005c0c01400703d01d03001901c4240600060590b03a80c542442100d02901800885803401c0200308090300c1080010101039101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 119298354 1250 119297104 119297131
    0x809070b0a2601060206041505070c1203060f060f02120f0f0a0504030204020a0c060b01020a0b0c0a02070f080715030c0e13150803040807090203090705010813120e120102070506070305 81
    0x2c601000300d0210a901c0040582d100d80280001c0007130042448241c1c0003812010080da20703141300c00501440d0b00b20005016096060003642c14503119406c17200207048600e5000030142d5948070700134904a005503001d03006006800c000b0301c400d003221302143c203005d080010040c03c054810000c4205a4041403503882801010800000143c880d4006031030105030700c0e20f403842151054140340d401e035070725070702c2d42070464000a04400014898441d59600000e41a02840d1101c41041c0c09a1400060303401048a4141c0e880000403854000614502503e2030b0910782080f4500b06030040d400da948a032500004543ca480c200c06943c107021400181034800c162010030514910500314111144507045a10550000201800044401c00c034100040000301001c41c507601c0c0104149071100401c1c000d407810450524007040d8446050030100050541022800b01403956040002c2c01001000445500851000110f030404407810300c00d90b811a50003501501540da030b01c0780d0440040030b00802c2d00410240 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 119299604 1250 119298354 119298407
    0xa1707080f0606040c170a180f05011b08070203040608041703100305070b0708030a0203070507051009030f0912030e120a060603111c111f030c0809070b0a 68
    0x101000710140041444000c0c1429007005400e010603650b28a240605100f07980000030340c2c0070004a03413640c1c4213008440015070300a0003454062900030f80040034100a140d8010601440010341c070900c203c0307103c1064000102a0410140c641d14804c0b80c0030300150708103100802425003e1102c0c690b1003071181c44842c07080100c2150b90341386030b0016a43c0240045040000388100a020424440580750211602d82408515035407184076100061011071010b8012000c41d2850307020310240c80c0c0880c0d00809440b04903002d03408200081800c0d02040d0001090301081107145030149046006a507110074482003120041e40b0191002101201015000520b81d90030220f185030038032590000741d2044c00b0214001d880d50a08200307000100400b2841218048480341e51410740c0180da0382503a070301040440c00748400c0303400200301007100da014000340d88107105045181503140c0c3c08003c100c104d0b03860300d0409449004040c3d50b101c81d540541074a1600401001030341c43d000e90310708802012000c1400c9000c01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 119300854 1250 119299604 119299619
    0x60a150602150c0d090308040c0603060f030201050d0b0405040f0c0b04120605060111030a020a05010f02030601270902071109131203090804050409080c07080a020a0b030606090a0303111009020a1707 87
    0x5c00c1a602540081d10303c40900c41040401c400c010010211031030140600c5090203003162484060b840028180200000d860b01c0c191225005601840b00042c0100003a15144c10001d584003502c0d14101c8946141000200340d4030300c032209850640b4402100d018101c026a650003008100c0500b8170341c10f02c10021030040c000c2c0e00030002003401c18201d6014000380082c52514a0940f1101c6400000d25030043c01001540d99200b500341c0c0b000300361044036045603443c00e46844c0c003000c4990805105540001440c1c02071250b09111002140da0030b803944a0259202211080000c04040c001440101009455905248a03402c9201c00074000c0b14031610f020750ba48006000c4030100c1400b12013510340072401e40703074a002c2070044c28001c2103a10050402c5413069070005084600300d000b200343c0c101000c0081030f40ca845080a032409100c02520320225944c8031704024102c0041100390030710724400c8508082e0a101c0305e00840880720340c0900354000060400000803544030321480c6904491044800004048 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 119302104 1250 119300854 119300861
    0xf090d060b0103060807080303060105220902090f0f0d0602090406050402192616030b0613180902130e010b310219030f0e030c060a150602150c0d 64
    0x25215000005074441c61500150030381c0c85950095a441c2c00401c0e080243c0c290120403258030000074030b00b9965580e00305100c0802c80e003c200200601078881310380440c05221a0b0300400700010f00f150726500383c110140c20014026882020560402480c1c501000003d05607000340801050003003021406548500c0454103d8205400e1a041ea80202911004080d000880405020440b10f203184810b44034903540c03030041001412441081030003103000f912481c4a50312542c1c1c80c1710014541a5184010005d0411404850054009900480048002d101114420554081c3c1d018000d19003440054040c00300902200e170682456540320300f0006525030312907020a02980000040d598800030781c8020809140070120b01508162040084401e40c1180c1402e10404407010300d0080f64410140047d0000f40035280800b400ba0720000c90b09003e41400850b00c984603402a14080100b07100383c0c090300c030b64065940b2170440035800c201c5644400345600700010b540001c650060b1441d0142c03106a0701c044 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 119303354 1250 119302104 119302129
    0xe1909060f0207030c020a0801061505070c051f080c1e03060a050414040b0a0c080604091106040f05030c0d0305071707080406090303020c0405010807270e031c020a090603020f09 78
    0x117110308540004c51070315044000141140100030440d440c20320b01702d100000c50b61002c580174440c0105a40302003100c0ba900c442e002c0c11000d070508929040320307040d000d00d00c400304a04002007900c650025920b051010140c0342599001c81c0060b0120100426440280e03202130042074000701e042c480800c4a0b25030380902d080269103c1c0f5140b04a14107030070941130514026040400c060b040c1251081c42e40da0005330141c100c501100d002810302c2c0f0514101203600d01029003280c00c40004900000c6c49422000010103ca50170b80c1501c000103c00001c2054224401e24011702040050100c58046243c418840c070034072200d0045185000000d0b115145c80b03030080c0c0e02590014445040910070194140454191142d007518188500c4d41070201150700d0b04800c0c05000030704109440060030480031020f00e4002481c41c00420401c0c0b4500541c1079880340e0140c0690300b00c0c00742e17136404000b40352414401c07240419030a030341d207803030142c20200d04401030750010700e41c030040c07940030f00c200700f06651201c0d811401e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 119304604 1250 119303354 119303357
    0xf060106050703030f05100608010e0c04090c230c010e070b072402040b0a1409031002032d010807080f06070c0311100b090901020a020703020607031e05030106090e1909060f020703 79
    0x104914181c0009c0207820b05070030a909014100041c010103d0480083d05d0503502c90f04000303d100d11030440c0441d00e2240e001031000180c900802d031805030481301c0e0001c0909244d81002071050400300d01d0140d564200728411040c1d485401c100b4a03011503071410341c520000381d004a500c4a4140300c03810f02400e980003a0002402024005100c6a0207a006080c00d60141c6408d003415003816200b000090325422908080103030250008006121080c3c07000c561452000c2c003c11060514846c1c2403150403002c3d00b401a00128400e045000c64207401c00a40458901511002402160380c1c42c0422100c424809404400f130000f10742c1340440040b400d0014000801d011800042c061b81c01c2420011500f6001d0214043c2e40d20401c250191594003160340001d032034050f180180d6443c80c0d4a411500c61800540c9440705001d0340c02d0180200e58003070001d40c100c403220368030114060f407a920380e003985038002d4446407400407040780304030051b0400f5080303603000c0c1d8040c400020b81015074094141c1a607104140c100d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 119305854 1250 119304604 119304631
    0x201060815090613050c0d080f0705010e070e040803070f141803010c050405060f0f040806010e09010b04270516080d03062903130606090b040e0f060106050703030f05 73
    0x80b02c0842082856401108803130024620144e58807103039150310380041da15008400d8040c2d01c006001003c400c8600d01c0007040ca2065031a015400c00a00030503072100c640c1c0503401003900c0050700720780904000c2d01607034010056518645038200d0503110441030094410034030040c4101e0b01111844600640381c03602c41280f4018610100c03400305421105182107000901001b480284099255502519010891100107551304e84140c682c02c1030034015030303201c1641c6210380e4001040000058019501901c0480024000182440c0c10803080e200030541a04580d0080c41000306584032098000811a006600380d0f2180400d1a0303010b250035141d9001111940d00c500d03071452809500d8800e803001071001c81184007a01c9542c0743c00c0780c00d019920b0202043d0300300210200c0c4802030307032945c00310803a6800300c02003148503070302c3c50044080c0c078901040d02d11483c58401034000b0800301150284280400102502c1c80340c1c01e00105840517081000300703034201960b070003207002110031621510b4000c402c10020030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 119307104 1250 119305854 119305861
    0x290310050612071b03020d0f110d020321190209010e030106090507020c03061512150103050106060806030c10080c0702090906040b010b04060c26030a0509061008120a0201060815 78
    0x64403100c008400184e80e0340c040101d0001003540801c0803080ea520915014040340b2941c00d040f907842c3d00d40d141c69465806420511100781713030004001e000300800c48045500e840e00031030100c81010001c843e0f002005207108030805210416038000e2074200c1c1e0505100c1021110340d808642190129088a0b40982e9643c1c02d1028a58041160320b0503c5e408400402107450401c0104101c0207540301c16a01413071075401c0c08400420107010310317500c041035020f81408a603581d0400034080c1a89110300408208050040ba07003505010803c5104141c000e016583c074030141140898254500904100764140c09202880059440c2502580101100c1000380403609142c207000da50803070b06038800880e1a42c20070040050903001942c0301c40c1184c000b59420300c50b080220a025a0140382000d1102c0030500200308220755060750300103401285540c3c00c4512075039407040b04859072100d0f806548515400015071042c1c56460400800708180c8602c000f0543c1d61f070b900c0c000d61409107032011441901c0d1480040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 119308354 1250 119307104 119307107
    0x31302040f0e07031b03022206050f0f010f0504080a030804110303032a0d0203090a150203010501021e03090901060804030210090803190b0307060c0c29031005061207 73
    0xa0284040002070704101080d000d80d8420750722241c602c8001c207012441020700290303500280119000f0754026211454040c2036400f0400c0011a095801301024600704010407142420300d5480041035002c0d0040c9054101200150f480c1481c224140c405c05c1300c20000810006418082c1401aa100b600d581c041400d0502c0d0101c4540034240c020350182d0f00500c1000210145c600070800312910700040c43c070400c00191420440c900c580700078145954000802e0102841b0005048001b07a4018540c260880c00e01000b024180d1000f0f03c2624016480120417907035002d2008125040c50021404483c80c0240d0240482c3d144182680808040341200341008140764040c040381e0009011190200521417082e40c41e201d081c00050a0811124038200c1c1004403c94198008545200d0007811211b90030b90703a40000b000a186080b0455981009075400038000320030000152401c0507221030000e001500f26281d200c6508014104541500114800185a01c540000b424500c001003d4040c003403170102c80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 119309604 1250 119308354 119308361
    0x31209030c0914040210170f0f1003081c0204030b01141903020319020d0204050f1806010506030a110f0403030504090605060a0e1009080f06070e0a0b0706090c090203130204 76
    0x4009189800c00c81c0c03000c901c0c49203807503061388241d04803803884070500031000480b12480924041d82c4407400520038407641018a00d0036910940c4501000c40a035070700c40090450400440c0310003040200c0500040d0311100e0041c1c62500b092040398001410183e40384c0b030f00000c15034281d10008144c2c0d02c01c1c081c1e4015042c540c05c600b20a084c00211030741d20f5440d690100f40d45405400803800c1800c0f06c1134984c01155148080c240400350000d0050145040c0070148030205481682c903821044805508002080c4011441c98102c80004100500b0744d40c0b4141070a000d000c500e02400301b241d0702005601181c115000181c4040c1d4040e5a4030354980d400c04029500301c1d1003030303002030380f080d9814000c810540743c0c4510148000c80081da09480c1c170203079942c0f050716000f103650003524403400703580c444c061006030005800b072180c141075aa0030524003101e001d20000f00311900a00104217010040380021540c550060480141709014103c100381d80c88030448120b8006407000e44442c2001c150407405e5141601 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 119310854 1250 119309604 119309609
    0x20a030605010c0c0501080a060e090105090d020a11060f19021f02160f02030c0d1b0504050108070303052d0703120b1c06061e0305160302011413031209030c 69
    0x2c0c10f0403980c0d030b19195603104134100d210341d6042001c000000740501c0100d402c40c10042105a100002c20705221040c0d9002e85400c0342d219245100e0340c2c821500040c800212290481d401c43d24111020420605110349644172080d2884001d05c10400003140329100a40d004070802e696010303100c0305281c03442e1030f0304110141c0900c2d4041801400211842c0881c1c000b298a030545c424109160440b8510110f03040040c00300c08030f80e202095112890610408502c242e41c00300640c900a8122601ca400300070460f0428020000554018142440001d000d50010115564985504002c0c0b07950b8840b030107411008004200050140810b40c80b00301a0444412030300c800c20725006109905040d00031031400449400e403110154218800c0000b8808981c2c0f005020b090b103d10036820b490421500070030321413040e1108031424802d11302400c503203011070741c00e00050344c0c1d050395104000810080c50030700c40d0300032010340c210440c0d1058000001510306501ea15034100c19460f407290302441c50811086a50a0b44d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 119312104 1250 119310854 119310857
    0x60c030c1c1103070b0a020901020c0a15080609010602030a0507050c04060f08010f0c020d0c03110a141203041703180607030f15080d0804230a0b09031305090c0706050109020a03060501 81
    0x50100c04001103034241171591041c0506d0005859410b6400100e00d0b0001c4920b0440d0043c280d40400b04a002c1d1b500c0803004c5803851900c0d080b100c2e4480c0d000340280740000344502c0e0016002844070b030034001c1c030900007410f5880c0a00d044034441c040540c00038084603065400384401100307030003040110720401e0003000114105044100143c241101020351900c1420031a0005c005010f21040200340c06030306820038440c034082c12079015032540c0c54940d03620304a401112406204203144100700c0c0032210122445039902103040c10700300004070402005600301502d01030106480240310904100c0c2000603900c00c0b0030a65021500030b800c0050a401c9401c1d0b580c60f0407200204030b03030502c40d044000070f00d544005a2480c0c4030141c0d50321800c00244007100c010385000709421118120542030360001d1881c4110303000e81003200075034480d1032031942d03070340b01e01c0480e00002080d114081040f80303400c00d500e42d484103450058600e0724240c1d0341c5180031988240c00500465602095202c2946d038584980b9025100030b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 119313354 1250 119312104 119312107
    0x102070c050f0102070320031603030c1e051f0612050715030204080708030c01291311071505061203250f030804050c0f0609060c030c1c1103 62
    0x15034403128801032603805400d005042c1107001202c641d1007000600f009503004209050103411840c80c00d100114051400c43c4248544130402691340c0383d810311178048030b0340354440e8140c035021562503803150351891a0103c031b810054085603010903c20320103102c078412038140c0f400c030000c444400c40003110b90030340200c00030408058440c00041c60010700c541c04c2e04d1402500020300c40001000302c019115a401042c0d0360300400c54001a0008000003410008103040c0080c00750084020791118412010321340c0c0400040c290303100818038145200041440240c2c034601160207030b5100c0c58003015511890040344c0b01c0500c5001014044c41c64072034184c0152007114140c0303c007107a020626a0300d0150303551000c824020101d0034841c2c000c400300241030041c2d12000c140e840c3c0240d820f028020300b1046038280c2c0d16015040080c215031a01c0c041e1030366920702c0100b0107818032504905014850700040e0400306688030030400400c1251042000040030b07a1400784ad1800241d4194000700703c10011405620075910 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 119314604 1250 119313354 119313367
    0xa08130305250c0b2703010f06060c03030509032a0f010c0e120705010c03050c0c0a0b0703030e060c1602030a0c080105160206040809010804150501080706020d05180d08041814090102 80
    0x140c2c2400503000355245c54002d4003e505280000307004006107803c84a09900d000c0c0d001034070a82128602c44250302075201040b69a03159484c4d140c072841540640e00c0b03180b202c002c50640e0190143c1c5506800d8010340116100c0301e98018803142191056005040801c80c03c003200c00c1540341038600c81d8050400e40000c0d01c0c0c110301d481e002918205c01e2001c000d05226011070403070f801e40c60070041070702c0c0e0241c010406180c2950b2000b1005450740104c1054002900304001c1d111a14400146103001c0c49010344100c1c03800600455040e03085460000403a81030007802020b00c0841c0208503a4005014410700028aa05203107a0101a1101c1c1100e50029504500d0801c00410355840584554880a0802e007200796291724189048440320909140340516080010606400c00250030781a10310030340032100e03181d1215805031583c0c0102401040302401c0b03040c0001e1217040c14401d6103c220311440c80b080c1040e8a904403e01800c0e1002c59030701119a030f85103451018003100c1100c42c0c0200d003080c021444d011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 119315854 1250 119314604 119314627
    0x91002130b0f0f1c050a05040f1209050a091b17061005040305010507020d030c0215041103010b030a0501050601020607170a0c18290a08130305250c0b 66
    0x2851164800141002c0351408034410700c18100d848a903c40745505640b02104140c40d012000001c031508981440c2c000001c102c00300318031601d400f8941103a8103d880034031030ba6030070221028510102d400c2080160b40002d59444420081000d445498008a424204204030703100b06c1004508400c00c04c080d43c45180c810200ca51882078000c0c00c161403a41012611442c10380f2248269031000707000c1d603e000d0421480a03800b03c1d408080d20040c1d54280200a0400300407a0344426550324440c0340300180c0c010400084a841508a141d05d01400210b031041c0f80c2c900007810000064001d0b94140d45039010400a036038140611948100c040c2800c0032249161010072040000003031004003016581c054051646020701581641e0300c82c0207140c502003940b24040c06611031b14101041217040044207184226104901c241c5240314119910b40310184c0d102508603649980911007a014080100a4201e0b2141002800d201e40c031000340d6080203c010300e00c2d0209101c81c195015084401040c0035411064 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 119317104 1250 119315854 119315887
    0x301060f1a09090c07020301140a1406030d051803010615090303020c0901140f0109091505090a0e032d03070519020106030201050f0703110307030f020f01020c0c060703051201060305091002 83
    0x84e0340900e200b07444440c00e01c003103030041000c00e640100190311642001a290310981110304034009140c0030454540721201416a90f0401d02d041c4c8010403c103100c41e030880d8149034000681510020300114070903903280c13000b00441075510003003800100d100b42c0500038550100b00e18004102c06030741d410120740c50505c0e440a0401031410040c480c8114010300300590b889000d01c070010301042001007060001f4049250043c20f081d2142c2801080c8100020b41382602034816506c81c6101c80c2c018501e0450382d42858100d0341004a8541e10520114102416002a0750040c41c030800e000e840380356466044104280c104844020400210381c100901400141d0340542901c041204080d15581c641107103242c195030f0b05c10600002203540c40040350300000d060340301140300340440707450702510540320900000c41c0c20f0b8442c060301241d01c0e80c04629002000c3c00d0071001040f443d406446c0103810182d850001c007100c414280d00110000352180240320000d80c09200322134100001c42801c605e00008040541c848 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 119318354 1250 119317104 119317111
    0x6040b0c0f0d0c061a030f010b18040f080309030408061504060b0c0d1101061802040e0612190623070206010503031e030403050c03040305070f05040504050a061a0301060f1a0909 78
    0x18541754600d40b111007410744030152400c400202615140c64000303125038024500c4100c030a2080130041c0f15104008010910070340035680042d4100c45007115512160038603400500419a039100400000030782031024010b545c0100304000000e0000081c0c101000240c840d2a0170180302200100901b4041c0d4000064004803002281401c0d000b07498403406060040900d030303204420b0344204003811907051044d54010400d984125003030740c10548030507050145401d69401c1491155008200d50700c101c4d005401c102c003481c0e01c0381c0c03030104034010250385a8000301d019040050300182e02c442440002c1e41c0601116014000580045040c175805844088101c00c0c40c90850450a00000104041c1403141040b9503c21110300101c03544d490f41c91030712664848a5210796006a04072000200300744c038003805514001d03904940100300d11001901d40f02c008041082e5211070036000c0c1d104801d040c5c0c5081c0207031802400003828080035186016400300e11240c200a43c00700340e100c1084488215950b50810b10780 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 119319604 1250 119318354 119318363
    0xb030307061505150403060e01050613050a09081206010f030c0c030e03070902040e0115091505090a050306010b0711030109030f1404030501020310080d18061101020906040b0c0f0d0c 80
    0x42c41000c218034000c0002243c0c21040e00700d03c1511006080b000ca0700d000f0000c0380d12680c000c00020b802c0421032403c0706c10640d81c4661182c015500b41c00d140740e064001540205041e00d0001c4c243c0e080795a004141e0b44010320100300f19207441c4c1001900c2d0f07007142c0361001c0100c842c101401010004040201010603030040107050016014546100c0c3c0c504001c0707200a081200c004554903501c8003c001c102074000d2203036000000003140280b401a105100c00e2080780c0030000321500c1c0302c000c060f0944060300103480c007a82000d40181c1c0099036079804c016280c001e05c480841207a543e000d038100400f900040364103c0780207a041800c0721001039030002c02682656214500513030140794916010565220b640c0c005403056001000b4895400c242d03100c42d80440715200c0407503068603860001a40c82c1c81d0f000c202f45c041e41080f01000c003d03507809814041035092014000500e000350520004482d50000d40001e0b17504140401c07400c04800d01001044984240100201091001a50005c011140a000041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 119320854 1250 119319604 119319611
    0x308090d03020307050a0b0603160e070305090a0f030504050118030503040302120f0f1b010f020606060c011113210f06021305041a0114130b180607060f0f0b03030706 73
    0x105041c401d0094403480c0e0b0b8080d0541d8a03111113402c10b44001f4005a81e102c1c480d0003541e1501c4030f01e100300003100c8221090641104025526080c09800600008004000328040e01c0e5007840010509445030140c0ea00c00e0712065180c0741130100040040394036110703020b45010300c2a000e01c0480c0d000000d46040f2030741100c2a1441c0b68000f04003078103000e440a801c004502c203003034903007001441c003140f10407038070b00da10452080105048004541d400d401d101010b025800c001c0c0860f166081c818010405c1c1320300c400c00415200f03001010064190311207001c290360000d86a07002e004a424403441c15a05910000d0511800d0007552200003407480b03030f0400246401c1c0e00040f02c15144110300410303402450020030801c9104460072412032a1509070340c040340080d500018074980c0140440035189c40c580400002d00e10141080c550341e1103139101c565191195408400c80d0ba0307140d69500f00034200b02c2d204880100341c0e1455680c603842070f103c00708100301c0c015041205504d22030710004183c640741904a0b0011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 119322104 1250 119320854 119320879
    0x515030c04030804080703020126040b0c1b0c03010b03010902090f0403090306020307030209030c01030213030b091c0522060c0b180102190e0d030c1b0801020d06080d09030809 77
    0x2212948160382c80100910004540080c1402c00410b010741103178000c1e00c032660220400e1038000f0000085034050381c5401d03800320210b0007003607162558030380c44050801e0407480d03d00040026130311031014800824007030384003059083c90350070203000e144162407040d0300034040b031865640003840032a0000c2c02069494009000039040c184070311880801550840b03400c560341d080425008002c1d51002031924000d103e40f45041c0740d19482842100c11a110020011100c3c60039070b03403a0303444650b000d00403402c02d10620030003000711040c4495410104260382c490b26507401004182a84616101101108032401000100002a00b0040c55004c0f2a44034200603050344d00c00380344d01c003018156000001650304c007003812880c0c0319092400b00c220005d2920782c91450305450080000c024103188004000031a2440c288000501d070001104007450982c0d001000c1c1502c0302c50b41d0b8226000388502180a40d00c4880800c20344105102c82140d44080746441034581e03003942c54020241c45451541790040340c000186 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 119323354 1250 119322104 119322121
    0x30f07051305060a082d060d02060702040e011b02010c080f0a0f06080c181b09010512090706080117120c07051302040801050c03040b071b08071b0f051503 68
    0x100050100100f5281e207030313210a54000e165040845042d0101c1c031080565140d003244154000300140f0b0000803244559550ba41404000c940150040385c2200741031100d0b000583c3c0364000e00c041580b0110000950884522880354400101d03011142964036088005800c160300c0380205a011160031028000307622000d00da00020721855119403045403803d180070412982c042203400800c001260308040800d0b806040302d1040c2e00503160300415a100700308500c250310542000d402241c01c1410142c0c207000c0820a520743c0000110b0f44981c039074000340e805014071034200c112075000d00018a80390b401d105880c481c05503107480c116224002000f01107003258541804019040140c60041c00a40c8000c0300513140758043d4000c0c3c0141d10700c82d400d000004102c0e504a02c141cbc1d109540004000b2400e031141d600035030304c5407030081c503055800007000301f281d01045d81c00700140348040c0700e1042402d1403107a142c20b820006000d0703009040c020f519547c08100c0baa0319a0701002c5c0029071000700907613036102c0070503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 119324604 1250 119323354 119323387
    0x30504020d0210020c190e0112030507210210020c06130204020d0204080106090e010b010f030213031e030f0207060c0b1005041d12031308090f0411130b030f0705 71
    0x70001d5000c18a0074142c02001d50100e40d07a5441e10007510205102000901500d5140407203000b04156081e58800400c40848001c0f14124407a0003030524078684252610303455048500900c10508540e0080c0c054408207604209201410020900850404503448001030b150440076044080310842980c10400355619036045604204c3c4040c1304650f1143c2d0b4800003170103440940b00b8616101c1c0380404000c045c01042c0a450300c0e4603016580ca41003000c425100360300941010f84404c1c0c00341e035082404000a0f000440442d04072610604070301c80300c0f40c18a002400b403503408030b03900308541014404102c601d03044610079544a07403201003000b06946900fa02c1c1c070711035000d91180d0380c05801c0241000a94034842d0344480c2141ca03000035101000d0540030300802c1e034441680c608080c40322000e01c5102260740200078100345540104022440c081c02d000040545445181c00781c0350010000380c1030410b00030310004000810030b05001906500d00390604503418200140307000144a400103561801c40700092 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 119325854 1250 119324604 119324629
    0x702060f1905151f020708060906061005040902070606181514030c090f010f06050f0406050c010906060303120e06010302030a0209180718110319020a020c130504020102071509030303050402 83
    0x2480c2404c154840b65140300c080301c80324803c0d009030140308008a1385c8800811841e2160035098014040d0391501c90900001c001e80a0062003000742c14400490034650500003001d005006410202d070260900d00c680e9400c0c0b0480c002007031101d10b00a031010180d0706042c0030000300c403010303030f0170501d00500c81010a04140c1c00700384a951000b2184c04120082c881010018160740b10000f42110b225155031050b5840c0c481c0700b9299a00d883d080c00200034803031044008020001c80c4200110b07141d40e030307590b5000c282d805035001100400c0c46100514600480b522401c2d004a840768010300e00c9501d035401181c0c80f0b01006101038000d045410010745100030b503200c091681e0995104a600c0725551300e500384049209140d4400da02030a140c102803041e0459402e5034000c40d4a4110740d0542c001950410b8000d5008544140545c01030714240685559102841058001d40500104944c03500348002800c1c244543c00c010801d00e03c0c40c1140000d107a1100404003541d40c1428002100d80390b90002800455090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 119327104 1250 119325854 119325859
    0x5030601030605160f02070e190c02010507030b01050f03060f0d0212060610030902060901031a0604030503070b0f1e0408070f0809040b03030a12020f0915030702060f190515 76
    0x2040008100a00d562010f8441c400c038041c08111070140f42c2c0103c480c3d6468000c01801a4080c1200b444403446d00720182d0740140310414406144200c0500c61001d844015100d840580d555100b041143c5030580600341c84164240380c502d1070040040f40e028090301001d041e2600074101400b03046100c0d203c9110283d11560002c010440c1c07082e250641c1d0b507403107800300d8982d4003601c49102920f4400707000e4090302411350340c001c20312410544c80c070004500030200780d0700354042281e45075a503c0c0f90ba110b080040018501920180d555071105003400c0e00b840038003404d01010180f8690800c2180d03a29408103500000383c80d814810240c5560400d0b07a214005c000c4094809030001c00043c00700001000103060008c0c00703440500020110004054507405901d0441c1c000c5042501d5411903200395900602400b01c800c50924142030001c80030468840343c0700c0d40003880d88000028441c0044e0100922039001d40e00340504081403502c00d08001000e04031802d101031207601e4a01040b003c12490a07607140900d4003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 119328354 1250 119327104 119327113
    0xe1603020c010e12040f08060705030105060a02010603021207050306160e100210050f0103120804080d02130e0403020706091202060406030b0112050f070908190b0c0d0501030506100b07030906030c090503 89
    0x1003418540c2191701c5842801820480c0ca200010841c40116899100316503d45076141141e00c4d10040c03103115072080003182c085560b14400030006986401141c04a029228014240181008141883c040f00030313024409240c951b15a420801b94807010b110781c2e050098503d20312517030f00480140c0c40d013074101031a200c6103420039003000305080c49250454120327030241201440302e4015440a403510700f426200a0201030040012810206158004000311311408e001c000328156240b40201100c9800e4800714016082080c04001c060f0b0b00c422000c0280104081351210300b42244d0015000d0701c07561060400781601c1e0580c0610316070040e6101d0300c010295183c00c0c45680361020390100d10800c00c03984030000c10407946020400010000f10711004144078084d008800307806403a20705110f01c0003410034503808401c0155400c3d81807280604c9000b94840c01c001d00c1d950809074844048400540c008009129040c46000003099200e0148012107d05003000900b8803a2041c3c00c440d0410070b40c112a406106 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 119329604 1250 119328354 119328373
    0x150c0f08030c031006030e06040b100305030f0702040c080c0a030c110d091a120f0402040608250b0703020a0b0615040b07051005013f03180e1603020c010e 68
    0x641d8005510884c4840c030800c140544865007602110390005100103241e001c900040c001400340c01545400c270f031600ca098501d60f981c81e0b6410340780d540b0202e0303000c0182a000c1614800c604041c050908010114103281c44c01d0300d8801185011400794444600c200b41c0c0b0785052001e802e002d0004c904d002e5403240c017510500601204040c2500b800c5220340c80181810001201143d000003045d0340c01c2c000070301c11102240d210054446010030000d007050b80d01c550f03244400540d4003410803111200886402450343c2160b02501c2c1d58581201e542c0c000c0009000800c40440001e5012406400c0154821410340b02a10f65102007070b840e0038106a0302e10140c40005011845940200140c00c203a40701d503044503010040280700000b541c2c9c0c20300c40d40c0717004c030140003400d15103c2c40300314201e00070319880007150326002440d0305400f500e043c40182603000c101c0c000c0d25030703182c406114059405004000480102810039a106548494500c000c4408040e80071424001e121000e40251100090400880343e13100e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 119330854 1250 119329604 119329621
    0xc080a031d0609151c02040501050a030905010e07030b010e010e0705070b1005031207061803050717091306061b0809240703020606121c0507020d02040501140f0a150c0f0803 76
    0xa00c842a80c0c40c0310500a805c412596486008a0303082c0c8606948441c102000720303900342c0182c0441d150854a075500e51080852001040091200440c0908404c1e40c141d4501000020f060270183c22190340c4042078130070000041d03003010032555107651003000d88189507034822202929051a0300b066a05004064083d883c01e0312040152844d81d02035034041242926400692503030200014005002c10420300c1a6408107101c2d0b1201c4480c2c407201010130303152400c40e10000300844542406483c446642c4c007001d10080f81e10031105500b031480c65041d1130040c5103079240c048190007401d405900c2980c45003101940d10944004026040c40c150b03107443d845000e0b0340340c080e4490340112200750227800d1a0a02000c0180700041950940140030407a50208145000888a5900440c0e081c1d8000c1038035414900103842e6842514001c01d04402c0b402c4084d64900c040050100740c0e2088244901c2c0ca01c0c20034005500c0325002101100b555060000580c582880d040c0c40544440c08041c005010200402030b166 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 119332104 1250 119330854 119330857
    0x191b0305030310240f0212040902040303080a020306151305030f0124180b0604080d080105031b06040506090f0a030302010510120b0a0b0114160c080a031d060915 71
    0x1a00c2401e0310a02d00c54a0f0f00c0030188022600e041e64502040701e8404c45140e501801e01c0b00c4e0804d82c148191f5005c0321440481440a44c000d82c0000f170030030f900240402c00d041e4004141034009100c40c00a52441c18940006040c09026143c07104040303000040c00741c020280a0701601c000c10020302641c500c00c000c01280c134002c22400740710400040718058176200c24100c8902c001d0541c5d01c005c21802c44041c070005071800802c5c810501c6500800104001305280e41d003085415640b091503517554415605090506041100c200e848104103600348955000720f9417403a00b52015a8001c0e038445490303590f0500000c415031214411190032140b81d171004414594103403c5a803003400d02c062201e503895550005104801c0e0800c0d005440c40d407000c030206e00305c466182c108000290301450040c10315111a40d002c0d03441e900501041400e041c044814100b0084030354042d01c01442070303e020300804502c944021f02100344500006041420032012031110743c0d19682540c02c2c0702400360490072103100303403103001c48207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 119333354 1250 119332104 119332111
    0x612020f0109081b150a02030a350403020d03050105010e0d0f1703090d0e0603150a0306021801030b03010c050a081b0d060501080f24030a0b0f16020105060102191b03050303 76
    0x240001185400e170b420b0404200c0340003007102d50045240203d440c0c0103d990018200360208801080c034649020074501890b030800010300811100800e041c989000303490444403038204c800345420000104501d0380c0102004202d00c40507907103a41020141d01d41030400141e107120052030015101d84013440362488001961040944030200d6064002c540c2d0291413045000d06041d51011301040029426200c0e0f00e5203402940001c0c24400235141c41e90b031140c01b680c2100b040b0031840701440350055059a4107000b40018901c0c19402004045210340e401001e42c400c40c801c9405200325800481c80c00791201000ea00389402c4a52004d8650315411400300c0540114801c480c0000c1c0300300e01041b0075400341030086020301d4102000207001b100505800c0d00340400d10300c07402d0303141c040c4500900201f1180f401e42d80c0700311000360810156107800014421000c4480850008581c5007200300441c50341c00041d41c424445002c2c00704220240d1914000c5031030201c80780705646024500d0000000c000001028600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 119334604 1250 119333354 119333359
    0xb01091e170c032503110d050f0102132c06120f0c01090b031e131a0906010605040f0e0c09100207050406090902010806062d0703020106090612020f0109081b 69
    0x1105150901c02182c2002c40985600c102ca03004441040003800a41b0091800364014201c2d038101101c94480f9820500100c500329041c0e500000c009d24041502880d48016000382840101181a1006180044515862000000c4d80c0000103d802541c4102003080203521050441d50b40c00c610019031034803081012551404900301c15008283d1521080541f4030940c000b9400e08000c585480d5604210750b00603140c20000c81c0d0820401000c140290b5401c0c1c81e200c81c0324240160b504000c03d4841c50408143d00101c20480140414410710b0840301c202c0c000c86608010078125038944080000d9644100d460b000c1d44040503110341c01078140c01080308021030300704031403c0109582d1011030b00c0941c2c020750f4000b400920000700081d405c0c07038094040c0c07032140b000f08101c140360480906040e6500c0103003800c00ba8003030701c08207400041540c2406504082e21020000703005052400e190b5818994031140c00030b200d00c5520341003940b280d210342d400c00001d1030303e42c0894441c0402150403a20100c01d03074200a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 119335854 1250 119334604 119334613
    0xb030c04030507050109080d03090201050d230603030c0601060f140406110c060f070f062c060a0204060c080306010c1502040303030f02040302010806010503040c12240b01091e170c03 80
    0x41c007980586d020004480224000d0002040e02003030460040050440032814064144821200c01081e071107003541520010b412101c1089a640c0c0e40300b075844001341924400d910030030000f084050702045003030455046081c080d005a00800d4103a59000032602c10140401c00400c0018619a100f1401c4081e10012400e8645818200c01030200350301c03e05a014010200070803c040c0040e9110300310303134030305800384500042004440c0d1402d032401040c40030140145401c9448040f503030b00140519504010015811480c0c2881e110380541034510082e0050b200d00804030007d4a0b5034050180441d25503404510000346101d02c0089070b00035046800103800080c600300c0b9540341d06145200b147c05498058450400030f81e640c400451301036000500483da50f0700801c8000031009502042825443d1090f00c07504e80748410610b0301010360308070019440a55091220050007a42c208101070140c0e10703d54240304040e8010107992603030880701d6002450318034040000f07400b526000f260040380403101f101510b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 119337104 1250 119335854 119335859
    0x603050601020d05031b0d02280c1e020d0c08011506170a090201120924021801030203060103061a0a1e020601121e0605060913030c020405040203070b030c04030507 72
    0x480e40c5a448003e2800814402c04c00700d01d0061107000b4203041c2071300c101002c600d802000003640042c3d03007050044d1820001c2c100480c1c60148080b04460101000c01c0c540448051100e4603051822007070040c03c1340c2111445480b003029925801002c4d41425084180c0d50405640c42d00b0a9000b019a40c071000d64800102002103401c0e0300c030750003c00900b030403803070403036956110082c0703160040c05c0d4441e080781840301c1100406031400c110700494804501078003500300b0b08135403180d02d40a40b0000b0100c000c202071040120641c10310341c2400c00b601c860380030305e0010703182d5843c40f006a0041800340c0041000c0c0c4036080241400041000050006072103d03a03458082103150348581c9441b00c292104d06001da0021001840f13000c1100054000c464014200f601d1001e003124419010030081c51000d59503d500e030000c000b114181015126040044103080c4040340155031001801d800100704000e01c5591240e0201d011366404004420181c24a99007050703172802c0002070300e0600e51042c07100b04d483c1e00402e00300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 119338354 1250 119337104 119337107
    0xc0c0103180209060f030a0f200d0206121506180f090609150d1202010b01020721080c010912020303040b060411030412030e01050106050408070503010501240201020705010203100603050601 83
    0x203210540b54040e1030f0142d0390321400200018450800807181c2c1600c2104000e20220701a0352154401c0c500948080c1410320b03501c054a220317000e5a0a6003401605030045080060b2900c1045880b040a50f1120550f55151013a50700c1000100d5403a06134010310108428101e22444403003070070702803412a0850050034800040c0302c04035004445455100007010001030400700c1c0000d9000c204d403801800d400303400788155254154650400352000050b903561000301140e580402c90107001e01a0361220b51140512801e181d0880350414500400220010130854846602500102d81d0a6882110b03000402c0041000a66a402c211001c1e0390883c203003030100d10300d410a84a0350545107400300f1443d2640e5030310f80f03c44501c69a20f180f010101b5564842400d11240284200e50203080c0c140e803260707610f0b81307807403072040c5040445c0d003010b4843d900d0000100407848a11490050000e100c070000d054031400200180d00900070440c010702294000400c1200040480340315505a0345581c81c104080c4e20349000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 119339604 1250 119338354 119338391
    0x3180c0602101805060c0f090a0311010e0108241201020a050a080f0403021e0f010e0709061a0306040b03190605250e1219050f2104060e04020f0c0c0103 67
    0x100588240c1100c40400d11b80c181c4440203162400c1801c0b030032480c20420501082c030120440d0300c01c1d10044805200e0302100e40c1e00c4160701400131400d182c604000d0601c0340c3c22080381150070041d11007503408545007400b1901d03000030900d54840074000031500c80c42621000b07441e6a100c4c80100b800103264000180c01c501d840c44016000f5034040e030003481000c0010501c1b40d00c1c8040c258140d070142c4035482c0a82c140c81c40034041c0c1c0300341c00b0101000d40441d5281c009200e00303942c06a04030204100e440e02c01d00070090041c1041d2a4010000c9402041d82101c05011a0611640844502245003070703582ca90180f01c9141c00030b0780581c1d0f4411013030101c600c0050b0f40c00300326210840200000b1321598240707001480c6c80200b00c50340c45a22016a4440034001c901e044803181c0006d802c03601c9030003480401d2030307500060004070400610039400e1020b2203c0b00c6209a0745114500031242448540a0b030080356484035070544000a03903e0400303e589400c143e5141d5650385400e81d4850001e810a0700c1014040d03500c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 119340854 1250 119339604 119339651
    0x80c060a081f03140f0d05160f020a0b0d050709050f0607020409170408061e0103051f1b020c030f012706020702031603061104050d0303180c060210 65
    0x1c0c0c0310803450301c0702080042e210710901416103107000002030202c0825522200f0300411020b800040c0b05044c00701207002c1c14500342a0003002070240900001592920103504440455400b030003040300e88030340f0302c0094212041034000c088504d0012850030060142644440e014107034a407034a1011a54420030410159442c1c0840340e00100c007400480014203040e00302c5d60038144109107844d6840f00895169410750400d600900482d40300d082444030741806100d21800715101041440c41c1581551102a91564003c0c0040c51521809805450415040d8484009008540c1c6608180c2d041404000d603103d01e40c0ca01a032103401202c80d2144686414400e05404585640c200d600715440720000c0160000e07800c4049e540150200001b40060340c2c20300003d03103a9240e48101c00c515034114100306040784c80302801c00744034180400040c0f102da55001003406149900d441d010500804c00641c9810115100100500340b0707100100201e40a40c01160015a18903c40801c0100c10322803201c0c0e15428071601c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 119342104 1250 119340854 119340857
    0x60d1503030e030d0f03090501110f04030b1e0c131d01030203060a06140607020f0a0905041203050c03040f05010b1002010e1b0f06090a270c08040506150d05060a06080c060a 76
    0x60003000c0429000e600500701c50341c008c03400010030031550301090700d0a80c0521000c00001400203024410010305010f821f0b0040220021096402c0741010741f0005003502503c414081c8001180004083c42041c401c0c0001e804954056803101e07403440080c44c0c200342e0030300080b4841d01503940004c2105c0309c01d1043e041252100409401000b40e070340140a00e581c0714a000703070b03001800000c4c2d000c400d0311103400c000c00501c0600e20000d414a0242402078a00c040c1c581e05c10105401c180901c008110280c0581c0d40143d003140400c0d003803541500d00580140b441003000c903003007000103000e0410542c041d805400910000070036540c419036450310780d816042e01c032f01d41c80b43d20000b44220300d86142070001c0640100310700945048d02d42071b282c04c0401e00c0350a402c0c3c14241d00281c640fa0410328000749010b00c070014801c504001c0003504050344c036551501c000900021540c0d034030303880001e201d0342c0b032900040c0c2ca150040300707482c2d503810f040c101040500403d020313080391485400d0000165041010031540c005459 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 119343354 1250 119342104 119342117
    0x8060f030718020c031303050d020a05060402010e060706050f1008070f090c0e0a0b0a170708240d050102091207050114030604060506180a060527060d1503030e030d 72
    0x105070b00009040e182102080b2500c0d400e000150115070100010507118001c030340404211843c5181031071600800c03050329001c640000040030300180000990942055090910b054003c0100300450198090b8883c003034112410321040c80300380086600741c2d60060180060741d045950300d402a04c0d0f9103240c14458148100b07440703041000130740d02c2c41d03022401803401d500c3c0400d2440e1a190020702108000e03004481c2e9141e0003e01040c0700c07608024143d00781e00031000c204619140400c070180080340000d000511340341c0002201540300b801907900c405e4902e0010840001c2896a04040b07000390007218403503000b04058032005080c0e9100041c100100c0314160345d004040d1240307240903d61a00054580380d0000c3d00d41102141b030341d43e418050300101884140808140320b010080100100890703100505000d01000488411968107804031407490308280e40c070710860146008245140706601a4040303080ca001044040103e51030ba01000302e030b000e5a00c114140040c00b08142d10303090405c4c1c0045c00f1800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 119344604 1250 119343354 119343359
    0xc180f11070b040c080607081608060a090f14010b091525061107080a030f0e1e070905010f0f060201050709090b0d12050903160f03020f060c07030606030308060f0307 73
    0x6032100b100f036100b842000c0c40e01085a440c0486031910405503880c0000c10094030401c0f100002d06044488269103501e03296103181410408201140854000d2840b520380701e0fa900c0846092035007060003e030b0000c090410742d03581d54581741156078000e4030310140315101d0f146c000f05501410505580c107608244c444a080b4049525040401d0101e0400c01c0324504d44034102c40c0d20401c0307000081c00313440340601c0c001ea03600c0300121001011203038900c800c46040e6184c0905040d5000d13000401841c17052081684000c91410300b02c10610b8440395030300900c0c215080000210f10000741c130501d00100c0309007480030302a480d100c0307078180d0907241c08407182e800180d10100c0812001141e60841c5e13442000150510080391869210501c039600075801010100d040040c1c0200c00b801e041010306141c0301340c258444507a900301849041d091900d484040c7c0f1130301c0780880408041d0b4070001125121b0880340111303104903503640380c408082c280c1072105402080b0f54100103103c508200c100303001e0030030006002d4020300c0e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 119345854 1250 119344604 119344613
    0xc0e0114191403071d16021506010302030901150801150501050414091003120c0b0106020a17090301060f0303090305060c0405090406050403050904020a0305090f030406090e04020301090c180f1107 86
    0x11011004242c0c54410a280020842c0c040320303840301800032900742d028041c1340c1800303641b101d444540030000466101844101c1c0c2d440103040300c150801800d00c0d02580d00d44403d00482c2c050302108541c05040510752400107950f000543c8034802000e083d014180303500744e8402c010f41c5e44e401a84540300c7c440c1801d5020400514021021541c001040d0481c0c1e00102c4c1c03252103000c0b011030640c6140000c40c8180da040d40038400002640c03401000c40c1c1c80100807022440d602c1d41810104000702c00e01031a40405d4410483c0d0f005e400c018041c0014203107045449a40b42002094080f0034401034425025130000302c0c100902c07100c110b500f03661000d0a1042c1b207440f555a0342004010060041d4104002813104081c6507440e0300007850004003640d400318160400400840c02c2c84180078010005910070070080006580158401d41203c5144210160381ea541d07001007800b40c84900d03002012080f070304002141c00640e50422420b074003c00c80c1c041201c00608a4540229045100306088008050040c100080d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 119347104 1250 119345854 119345879
    0x509130204020d021803070902090315040204090b070f0305071407080309010902040f09140102090307050d140a1208240d02131517010612020105030a02070c0e011419 73
    0x52000e0801454082800a818126042419942ca40c4c00501240b00724911b000c010060181045c00000c610b0590050700007562101201500201000b9980000e0705564495001986583c0c00107001c102510b030400004003103160001c0c4130000703c0c1c40c28003c01c200310301c512460903002a1031004d01d49000040d448450154100030a001310300d64031403035070900503280c50050521800b08045d01050346026817a01c4440c106803e0f04001c01688180450051030703400140036001c030b801c00c2e42d1012040e4a0341c01c1100c0403030440107585c034051140108050403c020300c107822005540d2681e40b42d0b043d8998940051743d10740703403008504945844550382401c500d0608841d0000038401060003281c09070340d000341015a018126030020701010100c0c1013008144601421200c06c40443c000c009040c20056604608405e003c4064104035010000411141003503045840d540d03041100003500564912255080c241d0034024a00d00304c4083c0303800c144508100402d0b05405a40c2000c00301400e0414620030b026 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 119348354 1250 119347104 119347141
    0x2090405100603030f091a03060d140a052109090f070201090609080405040506060c030d0506010521040201110106060518010201021308150606030402031c09090c0c0204060b040509 79
    0x14010102001d100310418802d04000354030a8450840b001020407024140d10035691145070303e018256101400170050b4070403241d0200080301c40561b4580703c2d0400c1200e450000c0300403442840740b1100d0b038062003000078041103e03030084412800d40a0440c1104040d030f009100c101e6401c880f030400880c1540428003a81c0d40d0001c0c0318030001416580c140c84543c2903414810b0180e515400006d0300b40f10500b4940900d60707001b10240c401c2460070010701c0c550b5a0700e100304282c50b280d8981d104d003c1089688198126212000d80e8400c100010340c0486150302046416103049000c10a644203543e038542c4103020320700032031b00f16445660400807045e8101c0100c83d690030401e07046541c200308000000d11104c04003806003004500400030300c0c410240b804280350015249604c1358005100300001a074000070000200c0d00c0d040500b100a85074100203850159068000150365810030301e44a0319030b588240408480d0b17000320380a0181a03a02c1086141d80d1085009141d00301903032800107500d811030304040a80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 119349604 1250 119348354 119348363
    0x90908030a05070e1302040806091606140d0504061409120a080c0403020603090706180f0302010e010306031e0524010303050a020a08130519060207050409060e0114070f0309050a020904 81
    0x100135500340009030409a603c180426516030100e000c0c45911000c008966214502400030030703401c00410140b0700003040d240f244a0411110014800c0946d40140030307580d000b030304d10900b842181000d16240e0050709102c01828802814080080c03206600020315044c408540080d9602e808141c0300115145e50004080324006c1307108000c0040140c40b51801036101d001454080c06038030b03042c005c0013031050751014040990031a6032241445a100c0c41c2e9600d50461744d0908114156210410050340075102076807003d00b1507001000c20700340074103003241d801c032829105909917400d031120b420944160a12800c55441410705120040c030009004000404036201c560044440d4215540e5070001140d010f01303410034404070041d200f00510305000481002c64001000710150050414000a40e5007002e07201d00ea10454443c00201c080c00709582c06060428a008000e00144082041d034040740e403c2518030314009103403d130a44156601c24422001d00c80d0b0700c5000307462513000383c2c0c00b0090107082c00391081d103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 119350854 1250 119349604 119349617
    0xb0d0902040209130509150402090708061c03020c0a0b1c090203030c03130302090105010f0816110303040602030f060904081e04230301050709080a0213110f03010906090908030a0507 80
    0x10b50761350302da2100c41c44101004042913914040007040d050013014000c02031034403240404c0c8401030b075491600942c483d00074588104540d0300c450008881003450142c01101d1600d03034042c0c3d400d040c0d0105040c201401c1c15262004155540c40580c41540701d44080b50303040004480002612651035000000720a00040449003840320005100d41994001d4680201c2c0e81c018450403c00c6040064655004003000d00304448030454082000d000c44600070010107801c40e0040d4040b100c41c2c040c40c800d00150003c90104c0e074503442e1900d0120003d40c001e5139086c0d80c103156100003071024503050048600c40c030303804070398241802010188054013400d80d10300410b4a01c030a0102090a103c1081d240d60305602cdd504001004034280024542100c0024210302e042080400e01842081e00c00244c02c01065815540382011181c07202a0100504041440c0814a140004c0c020480e400d03001c05503050341d00c5540200403660341d410032401141c0d0082c0c80100610740500c0001c203400031960105502203030900f05403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 119352104 1250 119350854 119350867
    0x14190506180901060c0f030f090803270d05100209010c0b0c1c0204060905061b06070503010f061706090414060a0c081b04120507091104030b09070b0d09020402 70
    0x6005030070150340c15680c18219094103189160040800380141003070308105100102944411451941c901c402034103200f0090f040607100c912030720401001301151070a4135120b080e00c0d101d400081440c911984065640000c01020525002d201185103d41c040c006000960400e04800080c0d000320442e94180b14400c0010f07004034544d03200d040e03c1030004050359640c480700b407000c219114244d041c2807203400b44180400d0014913046280502501c0080b00c00b82e445c0e00d4084c8843e03411801c3c031810006076000d408240003c054100c00a541aa44d203030300360042c1d0300d072910012580380c0360140820252000761000300c2c080b8100000300301d4025008051b8800500f100c85121450880107a4030b4640c4240e8814683c00e00c1948505160f4101510030303118603c0c0c120f0b10070300c2840c42c0110b01580c0e40c0400d03042010b100f0800308101080041c001010180801c008100107403030590802c0c4800c0e20305159141c0044c1ca10380022841c901500c02020310a8285066003001c280184102070080340c100740c1c01c0012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 119353354 1250 119352104 119352109
    0x4121707051b03011505060414040209040603050601030215120f040327140901030503040303030b0a030b070e011101021207030b01111902031509250308031e01050604141905 76
    0x1096400b15089a0a030210071100e00f49421a0210007420700412590201030216503140e8044400300c8131110b680c0743d8100d42081c0054024480c100031164030601d030900000800c00f021070702a049034021070340164800b880e810b4100203446250f0904242e8190500000c10464032405600d4220340245006111480141c0002e214107008480341d42d004101020104034421805502200c188410b0fa00b8440e69491655465a41d01441c00001c1c24951604005401074031407904240003545c105941c50010300706180c001e806490146442c40c0059078080354000c4555050007202d03d40d11811204608035958985c0440c0102400c06415041164080c03826150010401282c441e106080d140a550620b09104051504040a05034490007042074108030780081d002c074490140e0002000314004c10140300b02c64892004150308014002800881030040382c8040f11110110f2801041c6641d1650b600d5030100203860003031f449000d103021a01040c80b101400c2c0b10a415000d81d0740c0c01c04a003074950700d4400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 119354604 1250 119353354 119353363
    0x70210110d02070e18031204080c030a050915160f150e0304050a0608070507030c0614040303050a0e0105100501031109042901030605010e04050601020c1507170412170705 75
    0x400e0001070303100c1c0f0002e10036802c3c02451680c112008043c0402044aa1031056480740034004040c9078501c1c5507400902400145021201004004015299164500c4e50b001d04550010150580621804d00c0003032882c07000402100c204600310141d005500c0b0f9180c2c2c42001e4012004000c566481540207403105504207401607040c151014809961a01d0500e4103200c0801641e03401070341001344000900640d2508402140e24181d00b6160a0f0445030860a00b1070260100b070100c1e0102c640c1140806c800c2c580d01d64007481c040c1b01c20220600860303420450103420780d501078402c10852607240c00d04004560180d448508131000071032400d4140104180001c00701d42224080105d200d41c1c80041d1051300c1c2c0c081c049810650002d0804100341414000002c04003015a8082c601170381d511804208240e000300208410f00d50010540b11103058030040401040e00004412611858401c014410780041c90341600c050300c107003607840140303041291070303101c0030428100b40d0b10080c10781000030f00e001c80e10a01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 119355854 1250 119354604 119354623
    0x4050a120905090a05040b13170f1b0105090c0118080118020a0918120302070204050a0209040c0207051008071407051f021911070f080a0c0b070807021011 68
    0x8650401d16450541448044000100b0b040f4074117103844108000a51844000d40d003200c941111032020040e0b034030f400e14407103100b56404101c04401040002100c2620070050080581584241c60b4601e2038600306030a032041690b010b29030360402b400211803548248020310404801034115400981d030f0700040b0342110004c02c0c8544c00000041145820b600300381d0103010040601c084200260b4184035001c224006500314000d00e14040d2018106600d8400e07019140140c3d0000c04c2088242860316111009500500c01217001b9810060f4a030a094008076081040300c01c05000346075103907462542128003e1004160381c0034466000f0f200c3c20f40440080103440350a10403402000c0811036011400102c0a0003909520f8403401008081000a0850b004a00d041c4003400e1441c1c4001720013030203509068540d007094041c4144040c00080b072200028407211103601400410701d0441d00c4040340e000c03d104543c0041e010041c10000000107040021090210441520b4410039880e12041190f00705a00c11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 119357104 1250 119355854 119355857
    0x1611040f060e040618051b060f0c0d020c270405030c190201030b09272a10030606140d06150e0a05030c1e040e03040305030307090509010513020304050a12 68
    0x40c001c03c8100402803003844600c1001d0384001416040c207558840c0d94030310413040400001c00d900c9480a054582c103054443c4450f071030162640b00c0b00360780c240540d51002465001d0052240302800c040c40d0030038452140c1e004040c0d504d0a6100d110070710101c4000c00c0b01030320840303251004120320000c03254181300c40041c01c6d1641d001d00030b050400b800010150340081403001e10880f0150103210907202003a45281080f0b00580080045144903541c141c1011078000349106c074510524001c0e807030004c419018101d90f19044420582c01d1840610880c04c4402a001c0da001080301005075407804886180500ba5220042d500412840c3e103c8650000120940c6256000f040e0b0364080c1c030305146003aa104c840076103c140c00402d0035032009000902850400280305818038400d410a000c07503121a00141011a04d4000300d9644560740c0ca4030560760340c0304840e030b400081c140c2c0a000c203180c904102c110741202d600801d07142c03900d05500ca540000358000382c02201c0038850328500380c00091850444a24a4403103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 119358354 1250 119357104 119357129
    0x70e010f030b0606120a0c030b04051003031e0f11030f0d02030a0507140d02070507030b0907290d0506032a0406050102030c071a07051501090b061611040f06 69
    0x4614045500b818054181e910541c414000050454000000301d980103205540c0882c51214001058004100328616140c0050401c3d0800c800400000c880d14101da05ca80d43c0e007a260b0002d4854845281c0c00c00001e500028240450356508a110b40d0311100c0c0740c03d50f0001c1c0c91901d51a425102101d501810300e84803480d4001c0100030304142c05100d07980c0d100070303107081001421051100001c09445020490310700d45901190900c1849420070408000e1a4000341c1c03074500e414840c0501f6070b903840c07920600b60180302d08002c0101d000b0889120a2905810b444c0060900b00c01d580040b0141c030303000301107507014490f4080c894003a076030594560013102d20701c00943c2c012142d41401d00c0280d0303170035800c0f050643d8130400030012901000a080d40031148036000e80f5642101c1000111050320800301c0240261203202d000e403030741c1c41403841c59904a4044481c08c001c0c0215141c180802800703040180665260410200c20100e0700c0b241d580307840f001c0700510006041e020041e10004071a451742018403400c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 119359604 1250 119358354 119358359
    0x10c0306030c08010b0904140c0d0503030a05011203020601151704060c080907030b010308030703060b21060d02060316230c0d08010308160809090f100f0b120405070e010f 75
    0x648a0b0b920060071002000f413201c00f16460100720760780401b810050001710a040740c460710f800144003411040c840180b8211054065040643d941d40042e03c1044d0b00d90320b4903000242804030224075252042d0700d9005000141e280c0380080e15403020060440007808040c40d801e468901c040c0303000c84d100e9403040500186141c000c0c04010040c4000901107400743d800440284013051410a5844c1103d600c00740165130307681c0d0500110080e1660303500c031074a401404241d04860780d540100e8211800c6180b07640d05c1703450351a0300400884d251152070182d0016030400110304090403a100c0c00d1203100c0c1a041825a8010020180380c078203d5514a1a0151030701143c9030316844000e01000d54a07038010719040a0b50350450315006d00354445c00c40d84111100c00c0ca00c070201004901c0040d2891032000070034900c40c501e040c4080340010b250440f041803913402c0081c0d02058041c2540014021340d8100ca25007400c00d00400c0960784500e02c050800d440c18440e80c400000c0820708510114083e01402d4203500b20030b403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 119360854 1250 119359604 119359613
    0x40e0c12010e060307030f0c050d080c1623040e030a050706061e060c17040e07020607020607080a1104030c0b09030d050703020c010503060d0204050f090c041427010c030603 76
    0x90301a04450542c515072010f00c035a41da0f00140103401e40742c1041000301805040e1509110051060307006980250f03084101c03005021010000e042c0207000c003401d4a03000d540d000c054040b60301f0240100a038407468000042c1d03808103030349840a100f46c40a480005c41400b1544540c0c91b60b00001180c10006600051210420070f01340142030040112004506844181d20400800c4072554040c1c81d080104c810303c11002c1c00000b007042c2c92508400d41c2074036640d40c0c80d80c100940042040301c10074090b00c151b4010695451001070058071480140d503616025440301c504407000740c00c2c2c1080d1481078a03018000072001c5200341ca00b41d0020300c008003200b0341ea03a170028185401c02400001d0341060000900800e070110350086040e810080007440c0040d41d03030b6a8003000807840d09044c200a5040b615000400881143c082801c40c0504041c10072100142118001c11043d660030390b80d80303204044000085040c018404448500341c22039032107201400301c01106040d00711001000b180d00000d031500020004e01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 119362104 1250 119360854 119360887
    0x616060b0d0b150d020d0212120301080a12050324010e090a09030206070f08070e0402040b070b0a0605060403050312041103100b3c040209031501031109040c09050c040e0c 75
    0xc0f2044e66540d40920701c0350005111991401c0010340104100101c20a50704401d000803003442c4c240c03850280c2c695031198407180d41c84841c0b517003c60711350b045c2d6aa0741a01c18066000e82c0c2c03040452081703000d80140481e04d40034100c1903032418030b4144500300c034103ea001e5480d6522948100140040024403c0c04c60500a1408038050007040074404111540112580e10514955000060341002c40004840c00c0c0420020322603948049074841d00401d408080103000e1104600504d503060080c0310840e220303c10480903114511006140342d004001e41c10001911400f40340d403041c02510000c244d80c101d03801090402c0c001100b1907071040e60b145c650501d903140a96080110500203943d0041c04280011244001f11041d40d081c1201c164507001301215a49640445641502c00b03002e80304052000482516200002c3c042100e49043c44601c8403042d01780050114400ca4000c50201b49003498050110300424003e050758103611020000815110042490517016007111100aa0307681225030149001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 119363354 1250 119362104 119362141
    0x1a09031c020604060203070c15020c06150d060510050603090303090607141b070335090f0d1704031a070206010e0c090a0e010f03200616060b0d0b 64
    0x120000114000d003416400203885070b220b944984010794a4507102000c0d15030500d0407031300800c0c8040ba4a904108145550040c1c90707010450030031a9055100d0342c60108070821010005030b00050782402280c081015074101c40d801143c1e500b41d640459403114089040c69004036482c8019030301c00018055600ba08000683d80200a0724021464030040010a20b070ba21800f01d280b510744c103400c403618071644c81c107009100086034072200d100244000a100000042404803050007a4100e2a40200140501208980040400a0246000c1c5903124100188041c001206548043c2d460401c3e1010000c500014405180140d400110305100e480100c540b50b4002081001190000c0004010b0000c2c0b20321031079004120804080c1e1101058000300d10781e0401503100c48850041c5100002d40c08112200350002e0301d02440e810300c0e0300680c100e51007a0546034441d840380c01000c1000f12101c171000300324000045a1080601082c09001d19001551030070200034207031100e11441f41440310307071494407600c1601e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 119364604 1250 119363354 119363383
    0xb0c010608121806090414160e151911010e03030a0507110601030b0703020d09120905030a0b010501080604180c0501090504090309030b06060c0a1a0c090904020f0a1a0903 75
    0x15065822800c0c6507101d402041d018099840803417210901d41c0c55410021020525080c411542d1610300070b0840c11452009110001c5107200340865560300789080c2c00c0703a0704102c000310780b0b00d051000c0d000307001c19000c201c40e5541044980e0740b035181602000e000300405249000011503e9091070118001282c50140845061003070100c41c40100e90008191141166004041c00010341d40707114043e000703803003000300c100b0207185010390150411002c0344c4003201c0d9a030681e5542120a4440d014503684800000024100e142141d0040003103612a03a090350748004054804038a848111144c801014110203040380d00803202c2d4001c0c08156400200c044c0108030446080c841030949840183c03003120107000c05008141a0f400154941d01c81400300c0e0700f120b59110031510500d0b42e0341490302c01180048506c03002154107401152410213910151844000700402010701c58580381d00704005d2601d40e4051035041502e140000490b007100039039400240890144580e6500800c2c0100350a000004c241d010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 119365854 1250 119364604 119364607
    0x20a0606090b0f10050f0c0f07090e030d090c03060f0506040b060a091a090907050c120301061707021509070501030f090506060603040611070609050d08010608071202040b0c01060812 80
    0x19a15074070f020031082c105a0640366104c19183e0020116854800c07043d03100a03101c0005100d0592083c002480811041c1080584000a448044c00b100707440080001c004503904c00c0c0005070b0045d25030781c000c442c410300c100c0421444503076036603c160a0f540c44880440c211035032181009032504141c0900c0c2001c410407544036203880c4294901500d441100c1c09040440300382c0070400703011000c3c07020442d216000020945065403420340001404ca50254100d42607500401c0b03c012950445c00c02038906036001912010000ba00941c2545c110f80300080c0501c04521070f07034621060004040c0e2600e8004c0206901030b0907400d040000140039109008000c6000a07d4a181a00407a07004101c442d008001156403503079035100c0341009405850170001c0c061480e800060b03045c2c1005583d80c491040c142c0b154090350b94801031046c00f585c040d88244919030105030135000003a00e2610070400c0d40703e8213840490060809448004440c0182c020800010707407699100c6051068001c1040048501030030b003203815 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 119367104 1250 119365854 119365871
    0xb10050409213009140304031704080709111603081005011d090403020a080a0201090b0c07050703020906180c040f0f06050711010c02030102031509090a03020c0d170406020a060609 79
    0x1000f462403201420384480804000084450580001400070382154501d000e10202c1c0d215191264040d110803034240c4100100325100220b164250380458500310302a0203941d1a014014000c1c0100a9044003084001c104001c1e20100d02901000446d02035902c1d4101d03440c20786400c1d088031080b17030419414402c40314150984d402c010300c9902c9243c2c00694040380d140d03d980c41c2c142d140c0682005c000304960004652100300c1c40c0d055100442c3c0c140600c918103100d4640c0440051280304082c0b000d81190001001070002d8180600d00c180c000030050110344940c4402000402c0ca0035068504508040d8009000c01040010150038030180101106600c1c4007441c14602030030a1250700c4005004010b622070010880c0e00800f00301174180d402400a41d9246000110085065140c05410340300e41c42c80008141340b000001004a1003503415001040300084040810000d0019144200c0d19074010013800c07400c042d111300141004140c03580003031032081d1940ca400ca00f550500c0d0017560700d0624000c8103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 119368354 1250 119367104 119367137
    0x15030601350a080a080609070f0c1b050406060815010906170406060b03010905160504050a06050c0f030a11010b0d0803040303090c090c090303080619030b1005040921 73
    0x1461600c0c1101d00358200d0070001c14600a041c510400400780c00036001050340c1d04040d400c04896849003400b1141c0544aa98841c400c0c0d075481d40a0300700304001a1840b456100003103124140038032640d000030200d009e41d507071000020103582c0360360059000038041c8018440c0c814140c1c0ca1340e0400755403d0a2600201c1d08102c2c004100b00381d0800f6820841101501140c24080160301120151040401d003c0d507039a180c0c01118003502d000c4d05c0c00e002c4240d41401c070324482071060081c0c6060301d10003007451884500c5c0003000c0720b01e500000806a260b004407510a00c20340300c01c00080c48036429580314a80540b07180603800f82120a4a01c0d018010101042e403040061600c40407a42e00c11b500d0b0400051280c03540c106003004142d00c0d01b000d50600c1c40c16a074072200681022114049912036034810384c0aa859906011314641c41c403803034a0707400309003c07400e2000550b8a00030540c8400400c0700103418940d0340c80020190b402e1780d90250f45c80100c110b165070918519403005284950304d810001107081ca40c146 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 119369604 1250 119368354 119368409
    0x60c0c0e040209040b131203090312050c030106050d0609061413060612020a050c06190c03140601030e030708040b070b01080d120e0106050603160207170d03050709050915030601 78
    0x100506140700c01d070014522070710b00400001141e407c250003020700d414090003d00100150b85050303010840380c1c1c0786205401528010280709036021a0b901e4216480c0200c103585542100c03000681c16521404c020600210900c50200144001c15416640041c01001d0000d090408011000c0c841e040c04414040329400c94144c1072640000300005a40b10000c2404503540d0250181414143c02404140b003601819140d005402ca6030114042010809100e03080e000c4a0f081d0344000f0001e250305000480a6010b40d2258075072841d203806603454040a0380d40e52070f490380103800401c540480402e04400707029454541601402c8a0b0703004000d029013255000d085500300f680d406581d41d0310383c2c440903182c101c20340001c002000003610041d124100708803640310a0f4030200158005100380706d400552140940c0301b07001d88081031300c0075040201c035244c4105c5c00303010010901c01c00d0042d0300d0800a8035032160300d6464070982c1580b0b5076420070a24001003500301401030b4440381002c41b26a4480d00c2d1412002d070f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 119370854 1250 119369604 119369611
    0x30105010e130513051b0906060c010603080d0c0207050a08031c0f0903030902030c0a030206070f0819030b0a050a0501050d05340311031e07020f07060c0c0e040209 72
    0x30115010488070300001c180541000a0030003a80c00c1c401840504d844d69980041001d124400340c81c208003015500c0144075000000e01540f1661030004505281441402085c1d40302e464800824156100d446100b101e502041c5051421a519143e410f200b81e41408064042c080c21151441391500c1d155425949000e441c1001c619462501e441c0007414100d03510070101050300c10002e200121403410054020480c45800b0307402800364080c040498074000384003801381da0f4003c03d098100102034031000c0c0110100541203c0600c401c0044c0f100b001c0380070032041c9140700341d42e60120340f200070101401450b10840e40101d0081d44c0041007400346a8000d01a95a121001032001030342c0c0da0b0b0082403920418a00c407001d0301660401400d03842c404805040d00441c11155107044c4200310720042c12203135502c02181c0e040320441c1103001810144da6805525034201c625481250b400c0c0110700d000d1030400055a00c50000305490f1046001044031041c90480104166a4192150b01c3c043d0003080320f9007c000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 119372104 1250 119370854 119370857
    0x506040c0503120f1b10020a0806040b0907050f09210d030b100507050705040504060b090c180103020724020a090e0402030a0305071b0807051f0c0201030507020309131a100503010501 80
    0x10907440c07070700540c0d50441c403281c1c1c21085c1201c1c1081e880000074030003580030024540c009200e440000d03401c0e08150081c0d09030200b019002d5410b03584c40301c108942e01c0d08007036444251213004001c0211141e40380e04510701c4044540a40600104224824a10f0100c8561804043c1410300c1080c180070390b581000402a02e03200c1c105280d40311210302e8114100100c68000a51044c60001800f05101c081e50020108090035202202c403916100039601d590300580d102c8074509504a11403443d254425001340c522117100303508800c03400020b40c581c01010102071010520342d0381d000c100000701643c0321101c80000e10415816084a0509401003521400c81c00b0002d402d00200003450300c1082507108000c1c0e001440036421141e00c54072000480d482d0b00b6035108032481036248640142a40c0e103c181c0d010b059400940b10146035a51540c01500034000041505007035000a110a00190300d0342d000800300d42080303000c0000c14025010401030906604141c0e20b0081c480116122000c40c0c01c80103d074151b0f5401d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 119373354 1250 119372104 119372107
    0x3070207260a03180906080303060f06040f09110904020d0b041808041502030c0d09060833040204180203040215030702060a0e0111190806120a02090618040506040c0503120f 76
    0x813049000800006170b000840c12440c100700000d0000000c0003450003804201c4440c01030116003800c20440b27000d203028040c038140003030b4000c110b80a020342c0000081c0305020002c5050040b0075001a040741c00250801d842161114401d032214900ba2003590ba9030702d400381845140303510300c0c0c640034510700940c01000d442e03004086648070514000c00983d040044004105d5960807500f0400400d000d80e644501c0c00840c00c01d0380030401c08080c00922441d411070300c20070031211942007070340c0b0316502a000f00940d800a50811020940060201d1b6000344600c81c1c26000d6a64141807041c003911012206031281001000d00902603004d5021400c2a00035641c45d03008541050f500c0802401404c034202d41448481c00029081d0b46155202c2075142e0702921034684010301d5032002c050003403489a4040807401d5030050001c0b04010b150103601603030003031030242110f90200c1d0141c48219418109960944155110307008000400c002c41c11000c02903d03081d8080e09141c11f54103c030804c1c40c001c0c0f074603424540c1c50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 119374604 1250 119373354 119373377
    0xf0513020c0106240302030c071b09050106030b03060a0203010302090f15091003030e0109030201020706050c0703140a0b090c0603071407020907030501050a06090308120402011403070207260a03 85
    0x450360140c82148807084000c1080340e6440d226000740750036040d045400303c070080c10400151030003031007940c1c81140d840c41d0b11403508404d55034440018820300440c801c00d40e250280894414924800e041c080d0545171030010303101446d42e00f0075280010062840f03d81d5401080144016199501116003101405090040944034000c014100001e03003542aa00070000804118030751383c10842020807a8021340f034034058115500c00440f905000c07400080e02507400108208030703d5106000600c0070202d0103094600d101e88035510400c1c0782400201000040d80001034050500540380b00a5411406040061454401c40804a8454040103042400b130110001c05115200d20800494500550081003000c01d803401c5039000e40186401c2c000d040c042c6603c8540072594501940c598000e990b0031900413400c000c214640c500724460000e2080307040061500c4e118a0b10244c61002e10b00440035a00034000f0725040c040c900b210348410340b0b0b0440c00c040728200c1c0c03441e6080740400c812a00782e405160ac1080840b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 119375854 1250 119374604 119374639
    0xa0201030519022205030105090a080a110106030602090108010803030106080a0b0a0b030a0501090b10140f040308040e0f07091202010e031e01060f0f0e01090911040905031b06010f05 80
    0xb10498544490360380000340c0c0d450b10f0016042c031800c4c2060114030400e80241c40b00241802c8542c00c68600d029548104550408614803d001c5c00d422102c51401c42c41016000070b015003501c840307500c111181ca4001c240c00039150380000350301c4e0140450000035801d640c50090010143c54004c0c10801c401951075110031390640b20286110054005080947d50b00c0c1010641480100024480c80c03010380d240200e090010f20f002a900b05403540250b075400810110800b00725415030003405c01016519040200100080400d006800149500c010071042490f054041500c81d20000300304604100d0341440a0003082c03042214520b02540a10f00000d428148401092030407000c1c0303006119107496042006c1140c541500000300381d40c1400030034010303280e60340c030358080300c0c0864026251144100740042c041c010f0386038084c00710140182d0301d440410140c003010504480c0414826640c50304001003401600e01c0c4840d0443c0c4101c60349004040e1507240260880c124034603405072a10420741900c1050082 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 119377104 1250 119375854 119375881
    0xd110307050405190c02071a0310170f07080313030b040f060f0e0705060c030a181e05010206100810110705030309060402100504050d0f03210606021902030a02010305 73
    0x4103000b400401050030200080040c6803510021410705a042c28100c40d00e507803010440c4021510310340c07110700c0d07040e07c085203041950300000c11103407032502d03020b40004000031400c1c10105036003100000761003600f88041d4680d041040c1904100c0355540104441d1050701814441001100d810100045080d25240790141801011000240410b400c107008980645a10b9001402a41403901110451a44c490601c6800d008041241e0a00d410070f00010104d540180041c0b8407100210582080c2291a90392403400048906c014400c81e41c482d090034000c4c2d503010040240c20910b4040c91001d10b03850100d2296a1b04c0001e4092005191a001c4c0c0759100c4445030240d0342c0c0b50b075004095030b40701d103006030110341c0c0d50300102e030107a1182d46104007554665000710b08031000c4e00c1c4081d1203010520a20340300d5901c11072184404400700601c40201c010207240650329090404225203010a01d180ba2a400901d41006480c3c500940400c050400c40141d400044088010390f0a090204455a0b03149248652 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 119378354 1250 119377104 119377109
    0x5060c0d0b09070210060e0c030103060c140d020403030807080f04141603050a0201170108060f04020f190f08011a090c070b0a1e0603120e0604090e0f0106090b0d110307 74
    0x841100d00a001e00c83d84c02269070411400028001c00c000d40d9030b8a00001181c3c000e544128020f4001c10051010603800d80010b08118041c4c201001c8400c2e01002140c0e159205000000344240e001c1014001c05501c42021608030b0001c1c54040410700b010350f008400e5040285c8010410f00350b40c00c500e111404148090f02c208514180e02d10a100e9890400b141c8402c802d09040380000c23686030f092140b08240c0002e550584003203c000f400319640d01b403130355201c034400980181c0c4e01070880842c107501e03950360380c03100c05244507004d0704d01d002145070401c2a035200d05030b5000050305905010130300040e460295050313000e03480125507881d02511a480200880e10800c0c20290403111000100205110190400109031014601000822001c0d0b01d00c0e00403a0101d000c0104000000360903951218030030801c880440900400d080d180a90f20781d1483d04550355070007000d801c1d0b0462200440700810a108030700c010000c142040c00380308104400a0a038503031400c40149817030701101651140c0d0701d080000300301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 119379604 1250 119378354 119378359
    0x1b070b0a0201090c050303030112030f020c06030a021801020111180d0f081b01020906030c03100e01080a020111030a08011503060312030f0b0415230a061106090a05060c0d0b 76
    0x40d14004484000c1c00f90a180384282c4560318508000100c5090000459048501d0350302454843c0c40685e40c11583d41d81c0c805581c001b1840f45640d004640c1d0740d0391f4000c5006105150300140d13150340c440e40164134144040c40160669150000151042100800f21031030002c03920007a04090020f1400030304410002d01c00900301e034610103406000c000c0140000c1c1242d0b800c1001c080070b2a0b2a03040c0032802d0744202070220390091028004181103c1c2c0c0703000959000340d031a00c032810a96841d000048400c560076401040c4039804100c0400079940c101d080111440d91300f4003d10300d8480c040d10007420032541845103030391504040d806401040e110b940494060b550044601145c0d01ca28600100949101ca1107070030443e1070b00c803100c00585480e105a0180c04100d08114105034540540c0464000c030310060640d604640c0900510503940300d055003009800b0f03544841d145140055040b514181c8000c100300074030f50041e04680003041c00000c4460384151003616a0740d8800c0700c0300c12600030f0109441d41c140c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 119380854 1250 119379604 119379607
    0x60906160c24020325060f0605130b0a1401140d090c09020c0c04150305060f150d0c0b0a05040305010e061906050f060a03020909041a0703020a02031b070b 68
    0x4040014050082040360882d2491949107407000000d8000d01019410100c00b41c0e0041050340841c0a4110321080e8107032002c1c074a114041c0c0c441e1200405d035040300c100400c1c070320b9890000f4001407a203584034000b41402c0365070420000040501041a1010b00d008000402200c115002c5090b803044001d42550300c15150312a4490001c0340ca0380014006003c0100c61901c41c151003c40c503070401d0301c00d864000d8220b40041c0005811281408010080940c208880e00401c1a0200100d08200800c502078490100124000e1600705172a82003e800041e40a101c0c2016102a07000b0070285071030382065614407140f07995a0005a0019951845668002001942010000b03601c50138003055040c0305502e428095600d681001075075501300c031803501401c0d5000303540304100300709802d0040283c008000c0c20300703005103000804000a0ac07408400c8030111250701514810704065070403540d5003078008140e8141541490450813010f501c0313026040880c85c0500440c1d140c01503010080210400500e1102d9245 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 119382104 1250 119380854 119380897
    0x1d10050a1d07050109051c0f0516030b0906010b07021305071206090b0f0301051605070f0b0f0702010c09261c02030d060f050303190203040806100e0901090c05060906 73
    0x40d03842d11224071856000c111000c00008482c18460781841e0040c00252401c031500d2001d03a6440028107000005482034404d10386401c0b24035202c241b4000c00f40d809016085058604401c0071407a009050300080c440c50400e000301e4005803140340640302d415205000210340e590f219803044580d554801c026001180c100000020540500c1e0300922860605684000030100c2c104141402d80b0020b403542044202c68454000289110780082e1807158400c400082d45111a9100e180b500c0f030054843d5044480040c0500802c9030302482488407004450600803809485d005408890303140d03c4c000fa501c490711001451207910010700c007400808c14011070600881080c010000e42d04d0304910110142c040c503140c40441c0c10b1500c415184102d5500070019407415107206ca0200705020034410075404c1d40301c01c0c032002c10810410f00c1800c1c030441301c4c0f80c000c03d0040d26152000170041c0d000342c203213a11a4548421031010503c03044566007510b1702502c180d950341e9028404150188100c00820740c10b043c04040e072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 119383354 1250 119382104 119382161
    0x40e37020c10020d0b0405060f0105070602070501020c16060305040305040612020d0e0106170705091503150c13140d03270e040b16020303070c02040b0303031303031d10050a 76
    0x4e804441d150180410085000c107041c401140c10548001e0341c420181881c403201d541c8244010321456104040c09410704a030f0b0354907036003640c1001d003e01402c0d030030010800c400404a0740c030f80f00003008a480d0034007107400d10743c6010b0100d22481c01b0ba035080128021030b19401d40d040390100c0d1035010001d01c3c10002800c60410b0036000303281c41d006e0303846080346c81074900780e44140004010341900d80007801210240c41d10802601c458000c04210364060280c06501200481f10030b034001d22940115a03255656030551301070500f0f061203508454900402c01543c54400e031260b1400c0c0359103070b0b0b05081141988909041d201c0e40300114000c2c469484085600204a111586010501035482850030380c5594403035080d002040b0100c0c3d10385400603070040c0001001944900e4060f001d1a001400000d81094071070702081c19540103c5081c2c68541c1c440000070101503051140d113004450303100714041307403c400102d40c03503c0d5112510b610744903a0300c42c4080313441a4100d51280d096000b111002d5242c5000b25403a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 119384604 1250 119383354 119383357
    0x7051201050118121218210f02090708040210091d070210020f0405030106140102060c03040609060c02030a110c010905091008010513050106090b0901090504031e05040e37020c1002 79
    0x18500042e078a045010001481803030324006543d006d2a0503030460080c10200901f00c4803605050700e0300c0e4802c0b2401030141c0c882d0004640030303595507680c0040c1c0c1e103450300502c52041d124038020410800d5080041003a02c6005172041d45241209600c40038070b4550b01c4040b450b080c3c00c1d4002d8541d40f4400603800c0c40a03113484c070060088a409030003e07c40b950f0b07aa49601611401780301e9490140e0000380c0040d12030301d0918019580030348206000a4080035a4845204488050019402581c000120740c00906d1300b044441583c00d50301402001c076543d1000000b4154022407042074021000d840110f00380016000e001030160800c2c0008000c03c0ca0440740711800214030000c20f0300d8075445d0440100700144540502c00002d00d010b803110700d40343d1801c440f00c00184030040c4241c042060800c1c00c0c0410a290300308103504941144d403000d0304c80303003018010a041080a0550603036050b4400e00803501d1596000c44040c0e5082d200c85e103182405c1e0700c10202019101e0042014003900404001c0c5c2004400c0b81d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 119385854 1250 119384604 119384633
    0x303010909020906030609030901080a0e010507050919051e032b1106070912110a0e060406060908150627040308070804030c0b27030a03050705120105011812 69
    0x94181d8501c0d2103090605441d001b0603182d0300040d410030403072070b001540180340b941c5e040003c2d60000550740c24401c29460841e00241c3d502c50000d9000a90f040d40b501d03242c010711040c82c0d00a04100c107001c0c5030000160340c200e060750f0140c1600444000008a507502402280303449010014090310004850b450b490303203504500b51000104054007040a04036800180d83c3d03110b40841c4d26007140850620706040041c1c0039080701160060b04952041c41c030342c0c594210b004c00403d1101508804c03030a0140030031094a00e1a0050010000e4188041210040004035014008010342144107240c841e0804540481c20030a544508140d01c1c481c2d00c10400c0c1c003110380c1403165000750b40780301d0b0640f6800700c01c41d0a02015100900004da000f02814041000c0750001508100b0707064030011001250480a072440e48030101c008201d81010603132444040d0035005a591152036860322a00d001c6c00702c0206040803074103014450412500c203030400d01e00040554810007408680900042104251401901c2d2905c000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 119387104 1250 119385854 119385859
    0x10f0510020a050607050f0403150c090504020711061617070b25030e031902010212130c0317040909050c0301060608010b0d0e01110c0d0905010816110c03030301090902 74
    0x64055540350780301245480e0096840700103450540c0340c080702180c107a0001400005442410000000014461047c4001100c60440b000c02c208004080c040c00001203580410b010700d00401c00704000946030b80544481090445400c3c0d2038039408000840c0a2442c0d800003048031450003840a118942e00018101c0e042c4a12501c0c82c0b00c2c2d550f000042c02103510360782e14000bd4190f05072001015030207500000c607204550b2040313901f09040380c401d0a0402d00c65040b1100540d40c0010300701d81c03c40b9002c0a0703035800310315441028940b4589680b00303500070000d40701c05802a0b000301c10f071542c050030100c201c50003090131a00034420261130b414043d40300d0700070080d154400d6107401000030b002401048100c2c100ca100d500d4050400000e10000300c05011242010080780d5604d0483c003104130924409014001140c50081803503c1071050b02400c408034641206050101c0d407010000303449c40d09038200381181001c1c544040e900c146801840c0ca04404044c0c0070368140008000403e00c44055484400380074002c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 119388354 1250 119387104 119387119
    0x8030a03050a0f1e0b0d030e0121231f05060c0f0a08030108010b0405150d02031f0509070e06101d09042d080409150801020301090209010e18070f030e0303010f05 71
    0x4a04000d03d211b50074a008003c94031201c641c940c198002e441400c40444032901902e0391000d008040c50442d00c840d044010701d05a046507404040d191840103503482503d160540105a40250f1074200340e0b1194413869200e401c0005d0312810b448003c1c482c1880c0d40c08510106d91000c00c8600e08094a03403c240250b003000c1d0319001e0507031054a01406600d00030040c44100c1034407e40d4130800d000303c9100c2e540d01a070705032066100e60070356100102003866200e050004001050f0415901d4a0f04010003940001c181e102250248081644c54000085401445080000c4000d600304c1c0d81c075482d102030404090340000740404100c01e0102c10740301003180c014040b1944024107600400840ca4446010002c2c01c00c0809001c284100c10113644003076142c000120381e020189540714900c03400e99200340c10020406802145110240d42c1110003600001070444800c01007040c039440c0c840394a400104420100501c0098000050340280d000c07016a10790903040d6540c0c0e686500940c81c021a052003581d004031075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 119389604 1250 119388354 119388371
    0x3070305180a0b0f060609060d0c0f020607050415031b0c050f03210606090303070f0b060d0201080f0604020405060705010203010305121e0315090403020c1003050108030a03050a0f1e 80
    0x4074a4403042c035808041c078032107900c403504683c2484000414480c0c001004000d80c110340c0d5210005850164001a400301c1c40c0402c5410040c01c01e40c04258403030555005000740b20240d80c0110586041d9010a800c80c596032000340d108030060b03e00c0803030031101c01088262440085a2200c00345e07003424020800c503401c4e024001c00c031343d94901c07030401c0110f02408401038070100100c1d08000c068202c2c07030080a0a0418111400007030859101d044200d900000c00132645c0200a00305c20000d51103042160b810f06880c03c20340029001000092a18884a40240010b0460750341d03a410364000d0100580600d40b108014034205000b0349c02800252402c0c0b0901800c40707900c5105030201c1300c04020341e4074085002504c00c6442202900050300f8802c500c041010a10041d4a840a5541c8954042e0b402840c0052955090120080500101d002014100300040c088000000200c901c0d220851030300240035034820150390010b09840030100c00c01810300c941201c1040303540c1031030046082d064204024510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 119390854 1250 119389604 119389651
    0x1308030702040c090f12060e15040b090a020105030604090c0305060a021201080d09120501020702041b0e0306090601060e030c040213060807020a02130903110708070602010e030405030a080a0504030803070305 91
    0x4c0d00340c45101c01402c1d54001c28000020315280c0303503848901c1200d0101d402443c002040c6c0c2445011401c24410660b100d082000340880c039040303030b41c0052191010341040540d40d0002001444000d00c294041d50316403100000304040c11501c03500841c2c02000380c41c80e504004002c1c078003950004130b080c180b0724030704d000100e00000007040b410413030981d6807903440e50149884034590341d80c29001e900f580c055501b4454035000d0f0306da50041c1401c50f0b1044407000c940d240d0180700984803a0021800d14025400380c400c01405100010f1740b641500c0c800e08000510490300400286000b00c4000350036002400402c5146040000840c0c1314140c070b809031240080c660780c07842e0890f52868010b0019500160301c0319561065201503000300580c60082ca80200480001d2041900e41425540071031603507030110a0412890703a0a12a041d00c000003a00658640b504d03000010759116281c66010b084003100081c0030744400d02440484004540c8181d815031240341c1034601400070842100c0100d10a00220071001c0740c0c2c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 119392104 1250 119390854 119390867
    0x120f1014060f121009030e01030c0201020901080c09060c010f0b01081608240415030b060a0e0604230103050705150325090b0c0a0c080105040807060903051308030702040c 75
    0x24400549110b080108500c1046440d000d04420607005010b400c68203100d14015000d643c0d40c2d903009031905e07009104c1084c00101100e203070000d84800c591040c0040840e0340c2c2c3c0b10300c2a641012648034410744445080700080d06a2181c03c81d00200342d0b1811410800c001d0310350704440302a0000b626548c0b41aa682d03800c450680000307500c25400250080000b80c800c140400b1454144546691656903140606001c2811121035400010420b90020307010001c006882d824213520a41c10f44084007403902d041110b48071004050011845107454440c00148080000591010252420400c06080d40d45e8140541c4528841c010385008000802d40209009520360460340a44860030300c40c0b58400d00010310240c00070b44815040c2c108007007800300145510351030020b040c1013003030500a000c000c0c07400c1c42c008002e0141648003e1a82c1d0601042001040b802401da0b0003807904810b000ca590500761404480364440e044c4003041228101038082203a1500001400881d803090381e04000f50707010b544050b10790 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 119393354 1250 119392104 119392111
    0x3020906040c0c0b040611030403031b0e060904050910140f07020303150103051008030415030501170703121206030602030612010525020f1903020d080403080105010e120f1014 77
    0xc00c060340d50543c001030301c0500c2180e10500a01000400070388140e01c0c0946544140d4041d000203489083d40202d8400076000ea50401c0300600b0144428582c19011030054010418030324820765079800010b42e190000c2c400c0d0041605286030401448621544243e04400252516949154814006a07a56000204070703030003a10a40c0b5406407103003d07540114080e04e002003081001c0c01c1d50f104000f4004c0c00800203030010b4051402d50b107040d8201c522004048400507440300100e9005800c14255400300400c850080c0c0390070029100060102840c103507640c8529044112845240c44000014001c60b54043c50003002d0072100c10044844010f00079090742c030241d641243c60443d2002c58516425200140c1c1455540c5005540c1c91040e0003994508082603d1085940010710003001e80415038148176181040c0d145007407900b40e43c141500c0081c01c071a014007506043c4140144140c0065031002c040c810000c0440c2d0443d01d10798140010a43c80b8030347d00c182c40d8800b605040d8540c048084481900c4e20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 119394604 1250 119393354 119393357
    0x80f060a03150b09040303051501050f040b0c070305030a020d031404050607030c02191109010b040602060a0f0e0609011e0b0d0b101a0306101b11030319030603020906040c 75
    0x10050640d16480140710a8810042c407081e81e44008441548031210094440d40c02a240014241760140c11001100451108641044400c12441c000c1c0a202400d90f0150381c14509519181c485407040706140000c20313003019100f032001042401002da03000031410b5480c00d040e80e051001100203006100d0201041d1802005600240c2c002403410344640d0005680c01c0551044603100c0d004140d07140360a0000b5a01511000c40720120f03803019040c034200fa140103124078412145000e28000c4002d40310030025150640441c0c80b052030002c4852280c00210b000d642c181d0039110903007448a00d650003011501c00c2c0012400c05264020030662003489020541c1c80d0203001c40440078a9582c545d074111400814a455118105801280641c070042c2e5101203142034204881d0749041c80c2d010800e21002081c128810000c007040094620190703403240303070140b030750016114851811000000741140500b40403003204200ba40340710704107158140c01000c01c8078000d59a60340c00b0307100d19003030000b99000c40ca042c50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 119395854 1250 119394604 119394619
    0xc080c1e010618020304030f031a150304050105090a1509020a09110306030105010f0503030a03110f13081b100513030b0703060518070504062106030b070201150806160314040f03080f06 81
    0x40d20034080d4000383d404414182b0500c9141600304005840715840d00019030208031b0201c104820001e0034030465800000c040c0042c001401d850355115520701d80100c541c90f889444080c50401c54440d049020b01810b01e0010502018100f040e980780645c0040711482d102e0340c01c0c8800090940d06a401d91000c4d9023015000d5403903c000700c001580600240318002041040070001965090100f00103001c0d540001c00c0c500300400c9c0380070b5403540340c02c11640041420601c05001080c050343c4080144100d03004d503040080c0c551904000c0d1009100c01340d40b000d40329107403103400c0141c903075031503400784099400c1102d05c2d8003c641c507046180d5035941d0464070000400e104000500205014094050210a5075000da980c105440c1d00780006442155008842c07212407031091003521902805800d081c120008403005051b8039200003195140d0f4050100c203c4203211000c030003491407080d0040101410110207209140c242458580250010703298203400043c045000301d001c0003d40d00320140100001441c0c0c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 119397104 1250 119395854 119395877
    0x2150909310c0603110d02070c05010f030b030d0e01030b0306010e0714030405060601050702060c0a03050904060b0c250918030305010b0a0804020126180c040c0c080c1e01061802030403 81
    0x50b4003c100c41241401d00200a2000300400d0f5107e0005002980c420300703c400b0768614042c0054a0403038410f00450504d418039203d00d107951000115255810701616000c0aa03d00c5500103030001c00d41c240169030140101400880c0e0440c00d028000d0040f4041e03030b81c20000c3c0804c5408542280401d440040c540d402c2440450490f610400140128600060000d03191500800c00640740100890f411400b282c004920040640342c18890341d0001c0c581030400901d00740040c0780c02030311640e15003800f0203501001d92500c02c1000e00c1c4131202c0007601c807a240403c00a00d082d42c40b1036213a20b0715141200084d042c000041a400240410340d481298251901304940e11140d0041d83d110910b840c1c007641903901400706008201c2c441c10b41500544440c5903611006006c1c440c0f090624a99010341c90140303082c4025010183d6001c3c500c5d012071034204c0f4005446400c141c2116052400c2c60f14100496500f009544014450640c4014200ca080c00403104100c68494a200140d0004440107400304003980c610 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 119398354 1250 119397104 119397107
    0x18010f0309030c11121e0c15071203020c07060201050103060b01020f1e01090819020d03020c0309040f0f020c150601021c050c01060b0c01020a11070e010302150909310c06 75
    0x4104d240c440201101d280b110104c102c3da00d407030092101140c00f5990113210b000981e01c18800f6a0300f41009407100a84507114403262070440c8500c01c801003a60403100c00029003180f082d815500c0c20b100e6101620091503079148000e0103090700380000d803122407a1507017011140d8000600f011001c1c9120001d0314a880000031340964500e005000710300a9521648110009503400004002c28014490b020201b4101d040c03000345000b521061140c180352040003100d03000e20000042d03d072400300c11540869800020500710026140c1c2912142031107002040c011103024010621005400e400caa4042480c1d40d4a07004a03540e4040e0064020f24262882d00d880e500c0f4400e100406a02c170082c8000306a40d0360311200c1400a500400214500743d502040083c041580116440c8041d20100002d0110509103030f14140103031818440288580341c9030480004120072402034544584000745040e44e14900600c003140b1401f10208104800c002c075070807042240b00748010f00f1a40b190411560402103092400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 119399604 1250 119398354 119398373
    0x15050309030c07030327080c0d0804051002070e090c09070804020609090405100c03020405060904020922020909060301090506070e0f030609031e1e070602070818010f0309030c 77
    0xe00d120a00041100e0a04203004020201c0103500c00d0381c841c042d01c171840c00c0102101c001041400d8126180540c10007552100091954900c042201d40b034030340c00003902c1c05000e81e04c2181c0c401500500c000e46401c0010790040707080310442e4020781640c03640c0d54480d001c65464400010400b0b40c44660310012a10030f502c10114968094800344c40d880c40c10f190b403c00251a0681194200c43d10f40c054114410150103074000da001070a00c50a05504090811001a103e405003203803090140360b001c08c04107403070b965401d40d031103040070f804000300b881d000541203600181d0f1242c0bd001d4050410003002c5010b0707003014407612202d240c101016050b640c0300c8040881d04000350b4400641e0280c0c00d0b20140380e0300e9600b44582d60140c0496401960785800910451480c07185141580045d14070511090031444000e000154101c00c0c0f95404581d9001d05150043c024025808042d1880c8004500101403540c541c42581020300240c94403001c4004402048056885402d4001c00148213000ba07803000540403203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 119400854 1250 119399604 119399611
    0x4120f030912060504050d17010e09011e0209100906080415060512150105040506010203070f081201170c03060c040b03430e0a03080307020f030409020405011701150503 74
    0x1400365040c5a8039184020b14a80c15002074504035910401c0c0010848108864101e0701d0103420041c007002d0400a02401d00314051264507540e64410300000e1444400f9840040030000c1440901024980b01244600071b400851306280100340755000c082c0c4813801000d0b4001128095901c0204540d0b4581d1103038a00380313a40050b680d4a43d21070318041441d0b0381b03001c6030f10104d54080d001406c0c1e0f544031440c000ba25079410303400140542e02e010240100307a40e010040725016a00a80104044886441c218904e0b21850000d01e06030a4400004100030341c40501600740b0400010880303100c00c21010407d500c0d200d05440d0402650b40c00c004c02c11840b003618010316030040041e010404558072800c00804104608100d9561800e000000020030310110712804410780c0c41c40c90500d0f03c5a0009020644000041c000039003400004000144518130822800d203058100780c0070f9a448a0340d50341c400d0041e42260150501007981540602c0300094441c0185040f605940ca4891150b001e91a080d15250b0025 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 119402104 1250 119400854 119400857
    0x30c120309080406110f01060b0a030f23040f020d030e04150506031603020403080301090b1054060e030a05031b030d02030108060f0703020c0c0f0d0b0108060106030b01020304120f03 80
    0x4403e01c111061b401c2c487c0b0f8008101d174010681c0d841d00781d40310003421035440b6003620f4009882d04605c500c06156a5161170b804940e640c0d1004038607102c0c1d0a040102e0b0900c03141c025031106280091030109176008006030341283c0160b0303003440754483c072004407495000c43e80a255000301042c40010111014442110751186440c02c006113019204c0e11349842540c0241c00c40c54505072180100c01e05400d000840c500b00b18641d00c4d14400c1c20303041006000000c512000030040f04104031403050441c00c28000d910070389080d400d06102c0b80131540c02d0074010a0202d88280740104500842d1100d00d070074041000b4044a0303000000c5d6190000034585a121045288134040b960f05c800d0140030343c80c2691b84010340c040c14041d4000c0c806403401c4002103c42c540b0043c00c5008060042c40500039421000502184001040300c0000030000384070080385600340e1002000e05601c0074a400080c0c06540420303124140c42447d501401030301540d20042e41d60348664800c1e081c00314080d40408012480f0301d0042c40c0c01501c42d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 119403354 1250 119402104 119402113
    0xb0601051c02220b071502180303071505180307080a09050a081b010504050f040b040f1a0307050a0608040303050604020409020d051f0f0e13080403030c12030908040611 74
    0x10724800d00c04981002040c48103c0410005540c054100c4141d80c0c0300900440c00503070700d0130000d40d41e400081441c0d04c100424003500460080e00300a40c9052900c0180400750480361140c01d06c0c14002d10040500ca0400c92140c58240813550303c030602d0028005209680c8011450a802d0340c1c0e81c4511a44865809010005e101038045659075a52440314002c00c070202c010140d4030740300c0c019800200300b00b0a075141406000c0008000a44070300c04005540c15045500203803202e421000314018048420400c940c50345031a101050030325041046c40c840072026011100c200f520384013400b050780204e0081d0701c0850b82100c00200028420b4001d40c0c0d0040b00608013600f0705a69503e400d0a98001e840030300d08890303c400410082020700901c0b49280822800040c20303131807400200c0c03070300811070f40543c0c0d000355020030019850103844200402610740c0b04201a41c1c031942e9040003006407003885004c55086060b120000e600c00d20074080c254055400c83e031080c0c42c09240c00000c3d158520480001e01c1103028 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 119404604 1250 119403354 119403397
    0x1020a0f060e070f03060c2c0a090f020d0609061208030a061e0303020c010f051801030b0a080715050304051005070e03060703020a0e0301021303030c03180f1703070b060105 76
    0x2010b20103c00203000902c03812001900f0361a000090f5403400c8486020004a81100c200e15011980c00341702c0090710b11007089403041d20001051203014a038000d42c1c6940d0810020b1102c080b015070040910b0070310084c0800500303840b0800d9400f511128462807241000303190080020800c5d542c01903402003200c4400041769642c8030b001172110206007428a901c50328454042050580500c10600304c43c03400d1800003142c2c96080d5000d0114082c025030070070300d40120f0118243e181d00a5124460108009011842480d03448550541d600aa801644202d40800c4010546103009000303613801507501c41c0203003c942000810040080c400100f8103420007807030343c55000b0161002e0041c94014840760f030b00965610380d280000b07403003007200f0300e180340c040d0b03104124000c14000ea81c1468015a507251400c800c082c1170343c1c02d04498110011608110015003c03400203240c2c60000c4070303001107406528099819088061066031240204a0042c1541d40003900199566202e01e000b1303c40418044191800880d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 119405854 1250 119404604 119404631
    0x50103022d03061c02210304050604170d021b06091507050a0303050705120c09060c1009060c140d05091002040f0302130c0210020703020307080706050403090509010501020a0f06 78
    0x10500320640a0000001c1030280c0340c04c2200103041000b4001401400108095000c6080c2210210300c0e40551003500703182455084081c0308580091000806681d00c8548490003c1304040d00700051200038840e44400000e01800841c15080100002c90040005a01a420b001c0e855000303450792684400700c040d2201c000707403024015142c0e81d8040d100403c41c0c40481c2c41c0c0031303085500140c0000240f000501c000b0b5a000141e91406621a10b40381e0300d03d444041e02c1d00410114000c44046084a0241c0c07032450888900725801042c565004030400d0000094485003560041d1022245042c505070030401a1040c503c240c2013103402c035242d0701c2214400040300318200126046500904034506001808106514102d0900e14040506020130031998031010340117980c2c1c99614002402c0f56802080030301c2454000d005840f41c068015003116610f00342840e251001b07110445085010640f011804581400c011a41d00c0c180c0c0c034182c0003041d01900b940c854281d0038031184012168651981c00520004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 119407104 1250 119405854 119405917
    0x30c0213061403121602120c03030301150212040f0509060d0c090c02010e0d0c02090403020c0901060e10030b0a05061303060204030609020306180615130606180501020c06030105010302 81
    0x90881d4082e64010401c0750040506254010161441c41c3c081445083c80c2d030040143d42c40d01e02c65045034010180320104880f0303410409841d40d815814080803000040c4920840780c19121200b25a0135100340e42c0305d140801546001d5130007444224200c81100b8403180c00c16018054100300b0041009441c2080f0742d07100c62060403180c01819443d916444601085a024011400d054400c6000341030035009401e0000c0c0a601e5040000e4400c0c01d0100128003850300a100c2004840409000c0c0c00c1c0f590785510014050003800c2a00c1340c050301c0d0000b4152a080c2c82440f45101ea08801824030b40c07854070340002c200040e0402c90928074401805000000010458402800198402c40011071f45840900400d818810b00070079000c4040018562011454408200581d100041d0600c03280610f500a010038070b101d003520b0921021a280c660040b5406030416416031100f80501e8480c0c40260300c2d03e00490b111410b080000350000e200380014880c0f0b6000350088c080034041000700c0c100c103590071001d030030a2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 119408354 1250 119407104 119407109
    0x8090f1002040609050a050607020613030b0f250914011b0b060307051804030804031403040303061406040b0412021203120402040b04020c0d03091104090c0e0f13030c021306 76
    0x2039034006000c20040c0c2e001840603000b400e088620b03d403c289002c01045091041d018000d103d118000703100003250245402107400346402080d04c05061610301140c4500d10001e403044031040101c0b10780348210280051607000c1a504944d9105405894a440203003288070800c0401d0500104151101641001d40c0f4655402c6014800d94581400c1070380034142404502d400150042030b080d16840000e48440c1038043d00240d15152004056480341021510000c01404e40b0030301d040e0020903c41450784c5034108070291004840c1410003041c40400300402407056110704041d081d028001000149040e140340d0101c03900280401c501800d100c0426421640034541079684144138a0901c007c0d8140b178401d41ca22001c2c181c07411481d1401074240d0704d40d034042d0340b0002c0d00ac0548a00840080040414520110b0b141c058801d000b400080d01c3c141e100e0608c1740c0610000c17011064001249600802a100c0c0119842c031105440000301d0f460450304031100d03104c1aa0081c5100451140440e05446032400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 119409604 1250 119408354 119408383
    0x40605132f04031a0402060a11010209090414070611071413021209010c02010603030e06031905070c02040b3a05060a09060e060408031f03050d081e010b0304020108090f 74
    0x2642e90443c9480c2d072201e071210101c20101c060301810000181c6170942142d09010700303414109079860311002c240e0302a11400c07880542000f13a4100380310030060030301680000b00003103100752500701e5180e00044401c2103600b00401075651018004101c0070824000300c003281c00c4007a0445900800c400505000e80e0b00140081911080c040200004c0d030200384545282c200740c42c80244482e6107035482c0208220f0035030b16818400c0b440000820040c114240d4000030007544c02909000c80c2c44c08440160120710740e801d080e40181c3c1490410b210f64600307000e001c0c08445141c1075400001001d4450841b0342c2c450000318091010304118440c0100702c0c100000c3d03101b00c406440100d01040d41c3e1902c50280c03070f4075080e0981254403080500000030303030784420380c1c0d800b420300b05a0054680380480381d00382000301d85e4005800340c010341009901240c8d1160559110301a04144d40d104800a040404245c1009100311500c412007400410010340c4a44100c5800a03000000c132402e00c0c2600c01442d0070007110411128 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 119410854 1250 119409604 119409607
    0xe100311071101020f0304050109060302032a0901300506011106040521130501030e0102040b0403060204030c0f060e04050c0702190512010605030601090e1207060207050606040605132f 81
    0x41d825a13041040a000485040c0514241480c2c440040c10740700a9004810074140c01000003a2103121107020481d640c0800303010713420f1620001000314030395032105c804c0300c1c0024000c00d0700f00505051441401c0b0400700440e5500400301c2c940e8800c000418000e07100710f04010043d500030041400400c0300d14011802130000c0d0080e604101c1c2002032804000e01c9070a40c80c4000e221122011401007401c1f012104207081c0801c1040d094028540244540d4008446810011401000b444441d0b4040c005592042d1005480301352100580480300c0e940d0300c0384c000020b50642000895007041d4110503008030180072800c2c00d054182e40020402c038903560f03803000f078505c144d032007084280b0346009022600030101008101031404c0402182d20341005001c4c141d5410348a800c2400c80fa1420440041240144001c654650001e0b1031324201035402964107803280e11036000450002d16140c420740003124801402600241d00079a41c0a02600c4110f000c0203a4100041c58000381e02200745403664407000181d8041e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 119412104 1250 119410854 119410883
    0x102040f030b060f040e030d0504081303060515040603050a080a03020405150c1b010c0f140f0703060b0f06030a0f0b03030406020a050f0d05030c0d0b10030605030f060402010e10031107 81
    0xc1904120a1288600c4c06d00107601070b00c103408011207400c1c400d410808190355a035402c140c0d1640c42980400506040401d10003c01e000b95584158001d28100241d0510b6162880801042c0c803003e0001500682004081c0307000101000010080d59a1380d08016040999a50009801c00740002400c00764920000d030190007a07000340304003035036810b0114410440c1405000001d000e25800ca10080c00f215002e0f22078400c2c480b03841900c102c046008003c80700c0d041c1d1041c61003610f8004602c002c03180d036410f00e04050010319040001561004024118508599401f40400068014500940d421541e608400c1200761000c0c40288050001c1d0340040c440d0307600902e0242d10b018500407031122240c001920410311340d43e1140c00c9a4000c1d504407206520b8121030001c80300104214140f590b03100044070340e030500864054210a048500803401c1e00d105003444c0d055982c031b510382110002d00003003203003d00000c6454010380482c0344003071034a4002501298540d02d03502907400b02d0025244a080d400a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 119413354 1250 119412104 119412109
    0xc080402100c050d120f02160b010614090103020a1206060201061802030c1e040e041a0123010f0201060b040b07050715140304030e090f09011104080c040e0102040f030b06 75
    0x207400c80d80010b071808a0900c01c4030b4070740319120f81241d9614020070410b8000c42d0800c074510741000903044042070045568203800d24071400c204200c80790480343c04d401030f000000c0d1703580501d004140c2c0e80d0301c1c044060b240010b400f00440081d0301c2104407005111300e070718031079135545204d2003624064603468000080300b078206481c20103020005190140124010030411540035506001d5414504400c1441c690f10510b0326002169401207400000410042100300030a12101ca003000051540103040040281d880742c581460900f210840e80090400740c0b2540203035944211125464480d5520000805a03110460449907a0155014240095002c00d0041c140102401440d00504110007141c1c880040060003030011442181e180c0c0c000f0001000250505003d142c1c0f210f0700000040010146180c24600403101d0030080e580100c04d903182856800044890340210b905a8050340010048101c4401c1000007418050500020a5400f03020014542402c2c541c401c01452040c203001034985000c074103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 119414604 1250 119413354 119413369
    0x50c0d120506061c050a020c030a03140f01030f030c02061b1b09090a030819140a060f050109030f081e04090c020303010315020a020f160503010b0324100302040c080402 74
    0x8551045100304a21000100a049036841c07407081104c010a0644d80c0c0c540340c100a0142104070a8035000c00180c803040668154465032225004203031101d801d0301e80098001c1c510030240002481000010003520100e4051408072080c01e10040800b485e2200b41604a401231180340524152035110980c402114003072030004080c40802a41d1003003d80c03a003e01401e039109007602028040c031088070702055803801e144085080307003540220140021140c940102602440c00c48402400c01d290803c013040900fa070400712400c8500507074401e4461405c6446005442c60302803002ca0700d01d007040000001c010303240d40c02e096403012940710aa481c1d51400010310700b540c0000d50340c0c0085410402c0180002074100d220389071401d002c2100141c80e0510b1040c264500341008900c1071403442a14100d214105014140200f03070380f000c0d8001e000c1c002d80c4500741942ea60b400300e10003a5078401c1e0506180750b00013246059900c41224000e1605032075807500030600b00c0710b8003111180041e980342d04000075420b040e403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 119415854 1250 119414604 119414611
    0x30b01020708150f0903070c0b09310c02210a080c030601090303050a111608010c020102030f04060903140c01050709170705010e0604032307081c080601050c0d1205 72
    0x140940403d219050881150040081403108800322240103e07500860801c01e844071551300615000c51151203203400d0305550400040c1c1c0c0d12400484c80000c07802c0382d110b040444218514080002c1005400c04141c0c05000207104e0403046215103442e041401d40f0300501c00380120400d00c001ca40c1c0d580940d4000308a280700411003140e0303002c1041030080307607680030360582c0459405180c0261a4000c0c0c400c119070244140c0f554810511a03d4a10b142441c048640901100ea00c80001c111009502c2002e81c2030740030840b881c02441078520002400709203241c000c440501d2203813502c9203103031a010100c1103d9400c00b40a980107690f48004005586030400d046501500810007843c0c40742d041c604a256985405010f01030400010108901c3c158490303070b00f610f02440d0f00c840103144941021460080441c550409101d0358802c1351000600d140c404110035150b4403c445a00050001040003540c10a0000c0d054904000c3c2c1044900e02c20402804441c01890301546c4681100c030841c10250144e40f00076 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 119417104 1250 119415854 119415869
    0xe0c01050a0e150f0a0f020f0706020a08090301110403030513060903052d030d0f0c0305100e06011205040317250809070b0a0f0207140a0302090a0b10030b010207 71
    0x4211021115402480d007000d050001c0f200c4814411001c0701840a81c003d800f01d5a69442012a06004854004507020314600c469803c50b410301e01000901550b0300c02c144a9000035800141052001c1007120009021400d4040d001281003545041a01c3c00760740298425070020340c000c21a07200200307135013013045e00500061404d04007050454450980304e20614441e544000410740d00e6140724003498800c0807240e20ba8009481d160620b840500d4007410300d0203120811186812198404c0d64064401c5c1030080d00003041d20b803c0300342001003155941c0c07005040241448083d00034400300d41070a008051043d803003030745c3c1d0307611078008401c02e04070b4020045c0003071f003400c0401d244003a13002e800b80345609a030140d1480d0042868a4420405007004299000f4604c521000203090b50381c3c9810a0301c03a468405c86070708454140c0d0b0b850b03521040c46000d92b2482030784144000820000741c5864890726420200b021b80004000a4201c0000c0704a181680d9400109803238000e1035066603014441c1381c2c000d0445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 119418354 1250 119417104 119417107
    0x308070c0e0705180307030b1006110d0203160501020f03010902090f09011a070317040f0b10030c0306022b0c1706090403031e1104090606020a0b010b16060f0e0c0105 73
    0x10400900180641c1250494079140e8440c4d00c1c0950343d0030055a03000b140c004101030442d041c04102003200040b94000c840205071215040301c10150002480100310100f40e025608020902c080d00c0041c0d400c0d68000e860541d02801901c6440200100940c000c01c0b45110050f0740d248120b0030300100610f07400e0028442d5010740010032002166030f00c10382802c4a50f030390f056a280d1580c903040c4ca046203502c031001c40c0c03042036200704000c000b10f11105188407802000c07100250f6076803074007072462440310340801409440c2415080001622a401410201050341111003821071100b06810b941d01800b07603c180c1d1070361900d00022025170440031421108891400d81c240394907080000c100c94101c0540014100741da5840c0c0c4520390610024154500e031410781e07007440b42011680c903402c0310381c006008407110316251020000c2e82c00d000084500075180c0c40a1400301503880c00101c500c1d02d030400001c0010030b48550f5040c40c0041d85602ca000b000703492507807000449000707040c03916140c02c0461030014140f020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 119419604 1250 119418354 119418361
    0x71a1f08010905070e061503180f0a03090506070812070e010e0103090f0f080705060a06091b02061f08031c05010519140102010b04050a05040312150524040308070c0e 73
    0x301141103420f41d405d285141d6455101c002c040341e002c401081f01030100318004401d110159083c140c0d10407a43c0991400c440204c4100c504841d00c036110240020080b40c10f5000c2013041c0e0030000b000d4504280076010150034281000c0d49541101c1e07084079464002032484035408029a00081d03904582c81080c0380801140d04c1039a5001c400346180c1d28041e05601c42c100040003081618012503044a038080c2c150340142c2000c24100c030203415140034804556041402c0c00f18086803100c05120303641c41c41d03070041803540c40340b001c00030001e12500d8051070340320003400c0c020452071000c000801300700620420f00c00301c041c3e18010740012900d06801180c864003000d00720302000480d01240c3c40030380c0e540502e6142c10f601c01000507401011103410070b80d0440c2c14181000007020b0907510962003136009443c0c00c400d11450310345074812a8107000c00344220042e14442405641002c050060042c08164000481c03691300104482c4e05410560040341c0b20b0302c2c0010b41170304021000212500800d1032070110011800d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 119420854 1250 119419604 119419613
    0x609070b0406030905030403060c2607080612150c0a0e0a050303091210091103060a0e0601060f1101020304081c020708120a09020406060e0102010c0c0506060105071a1f080109 77
    0x8030701e1091004140d162503034102807150900465008560100d81040742400d0424060100d68110035078004606066070f10b10350344007203128140c1c4550307a9540d4401d080d03511a8200305004024107404035542c0301e60250400310180000741a4002c1400460040e2034100c05000101a941120407050090150010401151320008161102600103d694286070400c19184500d081d41d50214400c903e0b0030071001ca0180061070380c1510190b41c060301a00c03042e90b00c40c55090181e40349440c1c03140607940b2020041100500c41e15044010011624001c01d1030081c40003081c0c2643c0080e01c09131100500043d20341e2003c01001d154480c00078840f001541802c505884222032401010007008105d804040000d07403c80465000c034031000c0c0e005208200031502c80100800d101295580940550710b440310400c802405001036041c20369000004020640d5a0001101c0c9a000148115002081051950717048400c0d1000a486441e01d0036040d241242401c00d82160725002e0b40c004590382e40350200040118 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 119422104 1250 119420854 119420857
    0x406060306030b06210709140601020303060109090c0219060605241e0904140610110a1713120507060f020607080601111002040302041a060403120507020a0311030609070b 75
    0x120045a0071440b035003110b0703041d0343c80d10f0030821762180e14021200701040c03000c465480000305401d58409080283d80e05c00040e81d8a1000740c3d01d6a01040c1100420804800d061304807081f44c1400344107660307100d43c5840c0720f03076200040514200d40b91034950301c0c18031450601a859400321000541a009540202865401c00d80300711101917454014403150245100700b1141103074886240580100503a0f4404003640c0c0403104144e46040c451082c2c24440300d489441405140e448404040c058041c5200a56441d03041104a130f260840403803080c030000f15000d49581460000b81a8003220241d8155689040c0303080600a8001d40240094007181c44140c0ea40051555849901420086419164000103079008031020b081c5580b244242e0400c41100340030f540180048910940e401c0c0718065640340c51704203014030311a040c1c2e00301d0380520040002c1113a03010b094890154a00f04245070140d0ba40102e004110313150001c0d40c000c3e40320001160942810440e21384c0c0b01c00d0360301c0604405410980031040b217 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 119423354 1250 119422104 119422111
    0x80a0c0810020a14280309030905150d2417070b12010e1905010f0e060f03031903020405030601090c0807020d080106050f041d07020d03060501050d09060b03011a0406060306030b 78
    0x70010201c1e0030308405d5641c8100741d9138101c520300880c241c5000c0541c000e002e0491070804400284101e840010581400400419644908403c0b00c1c03c14041c450880014114007401da800d000c141d40c62a40d03244c0c4040000409800c0c050034039415080c0c8460290b01e00701f0302d41e001d410f002c2020085030303019100c030300318840c1510020001892262210b40b202c1480c00182c0381c0300600d4910b08400003e410306000301c010f0031105c400c9150481035070b44c08208000102e4003d5100d405800402402d40a62100041d03a5200368180c02c006082c01e4864001c40c2c5010f001360080340d249540c07200c8980101b90850aa035034402249c1c801814100a4200001d102e40d8040c4030700c005119000c1143e122040030304090754007402c51020044d02044021464405030a0160b038000c016020310484122001d110b4003a000c00d882d01038448928010440d400b400040100c0c0606903013042d07448001c0200e81d40c00380200750040c1e210b110201c81982c4003400700011102158031513001e16103000c9041000420300304540d5130 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 119424460 1106 119423354 119423387
    0x40302340e010e040b2707031104020306030c090a180c210302030909061c030305180705090c030a020702190e010603020a0804110a080a0c0810020a 65
    0x28080e42801040b018540a10020300072400841c1025001080e18120800d03400043c5800000b1888446d002906504841010803d00c81141d0701c1754560300703045800718a036045c1200083e50f90170707800b10064040d0100f0000101003824943c07160340a280c442c280c42500c81d89914049200000c00d000705060000c07200f41030400300743c0d018054000c0310707490b400451800d1120390801684103c024102503000500c0840c400d10120620741754121544a500d01080320b08000f0707200004400010440716165001c031208100644d03c0c80c000d181c000c1610300105a07a52a20466240a44551103000e5080050820980700d50b04034409071000701c900403100149940d882e09004c400b640700d40c03586040000c0506020501050b10003070308582413003004104803140f6950710019800c1116280c3c080e10b81109001003001102014041e52411800000c4210b182891001029110303404030350b400b05 = true := by decide +kernel

theorem cover : BRFrame.Cov 119244604 119424460 := by
  have h0 := BRFrame.cov_init 119244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 119244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 119244604 ≤ n) (h2 : n < 119424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
