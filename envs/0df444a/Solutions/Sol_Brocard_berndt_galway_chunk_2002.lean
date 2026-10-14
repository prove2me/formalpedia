-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2002
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:25:36.17543+00:00
-- url     : https://prove2.me/submissions/93a32d8a-4744-4071-b445-4ecfff7d79d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 359892086 ≤ n < 360071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 359893336 1250 359892086 359892103
    0x100207060905031828301b090902031903052b140f01170c09010909291501032304051207050318012001060e0c18040e030d020403060518 60
    0x1401e40b0740c4611b050f0401e031071703284507565050b04020b085080a03121001c1c80b000030001c2e4804c80308440802c2c1c403810007501d900c05903009484142d24014401c0c001d0780c0d00140310b1503551800002540070f20a03d1400b1180d0707018424024218420410410880d541108a807a04d90518624100a94100d0150f80c80c6131520542d076040c15824440c0050000c501c1e400940e2481e98462001c880000100c503010500004090780000a11981c03200d01d00208500c86c0d003103c03008000a6a007049a4102d11880d104085d4060808102c8120000d10040940d0094001405400d48156a0f004815403e10013034407000702241d049585001d01009260b15003500000d490110b604072000394202030031031810410340711650070614107200c8401c011005402c460225440440802c80c00450f0181c5005058001d060010384131400b1f0361801c2c0702c00111800c000a000c012610b042ba0046140d1490850040c01c501c05d0107002e0301c04a00000d000700510003da0000d03030089a900078952190603444014a442c0e4004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 359894586 1250 359893336 359893399
    0x40e0601270b0409060501090501051b0a06020304110111010c12090602040b0c25120209070c02040203070504051806060720100f201002070609050318 66
    0x50104950354441d40590030750441090541e016014102040304400344281e020701e41c88240098180080045401a040104400e003000060141800700203400350140220780a5000000d82d200380c01e10004108180d00190082411582c078202401c106042002260801340410250800145070213014841e8007401409562b03660304910403200c00b01d014040941055804907000d010104860718014000c080390541c600041c159949981c0e04ca06810149410b00c45210901c1c01080040c2c4200045500c042e0364101c0b810b0007160340344a070540340103909890180d0064400700070008040e4100e401030003921004c480e2031906505000c0c10181803038040fa501c9400c000180b054070009090b00c803426620203a940000c0c5031007140400420400103243d80d0003800503a2400c160004541c02441411009210603604a0b000c1004c0b00d815a5400e4040b003641e590350381c006190028088658010a00ca640c0401600c3e519102041e130582401090010310348510140c0c0d00380d8041c0c608144032501601072 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 359895836 1250 359894586 359894609
    0xa061503031e050a21050408030f0f0403140906070b010816080309060a03020903030706050c13170d030c2007140d03020703030f0302070804034e090b0a080f1513020d0209090901020702011404 84
    0x1103018200c0e13b19000300020681280050041c80001a602141c3c640a010301e4002041103039951109070602000036070090300700e03820420005103161280c20031206c041c0e00d0341c10091b0380c44c024031010034618890400d015000358076050901c20815081e000510080b11490a860016502c03800540b28001442046811513400020354410013400b1340c010401c40c2a15041507650404a51000440c40d1140c4081c680e098200c004248003408036031080c44602c10b0107030f807a54034480703003503602070b64070709490001905200c1903555080c08944260101d98800d540b04c4d2003241c4480e40d03031400461001da07450301c200c2d40300c444840080007d214100945100c00d52500b0182c070091654800d81035280030400f0020400480d43c01c00b00300c288818000b004242402c1d42c4000d15840d00450340c1080a2028181c84070030080d08400d240d1a07a9a00040a0100300010005a43c1c400300e000c800c000f84110030a50f034203c0e48a80c100407071460194007620110b4002e0f01e460584843d0b102c402e17401881980100c900501c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 359897086 1250 359895836 359895857
    0xb01020d0521090a1a040201081b121b1308060906040c09150512030a140a0f080a0219020312100f03060902030a061503031e050a21050408030f0f0403 66
    0x90b6141503650015065420750307090036102e44030410550b242e034009004001c03c81c002c0c40211b50303001540960100300745503100021916902c408a01d84181d0040d25801c10480d00400c00c1c902902d00e160104050b0b0240c400c0e41c031510310600144198403486442c28901070500015100d6401240491103a903001504018550902c020302c00200714001304c0c1c103c0c0b08428400800e01d41c880b02d011517604040c1310001d54072500040030050640030341d1b801c42041064240710b80326080341c015401e05680c43c1241001c01d00383d0f8036512290028014010040072031419407052030700c0780c2d401000070b00c40b90141070b02041041d907d51003020707544071907485141046c00e0b1036070007000030070003641c85016001c0c801010360b8148040d03500c070f4106640300c0542086225920003000c1003050b030040c0c0b1150200d42d0403180d101c1c545004c450054403e020b120407000a0184d070314070500c0d0a0300c3c4800b1201d00c4040c10b8204001d02e04260070709140ea03070070485281c0e030500c0c0d0301c00110b00d02c5260103500c02d01c0b89a140e41d0b6a01c140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 359898336 1250 359897086 359897137
    0x20903071806080d08060f150a03091119060207080a0519050102070f050601050a06080609070f1412190e2517030d05060109030b150d05010f0b01020d05 67
    0x50361031030000364425075a1080440c2040091003010740440e034581c0c4501701400e001082140f1a20125a1319100350840416420381d0700c60710083e03480d10380c400c1c280003413144200d00b00358a092400074183d07580181403040d9014400b500d401c894060b0b5240b13600322100213888a050654807003000c0e1005d000ba9100a2004410704505030740ca8502912a900245c00c5c112a9903901d103510b18420390071a9035800080040c1b1990070403034100002400b01c1d1a0580c062308052000c1242c1d01d40c050003050402c207000d1302c0c3c541994090400c0030301072801a0445555904407030a0380c07014600035100e00300701105d070303031215181d1044030b018402c145203c68010389002c1c10b40200c40c0e611441f0444800c1c40c81d015a400000d80380096081c0d290f00e00c11030304081c540d164a2035407580c08031240103003000e041c40b480c0c05007800441c001c80c02c26903200c102031004ca50800c00da400011000307070084c00003c029600301540c18241c01d620382c000c02c83c803e10a03001c6410100014030700380d440c1c2c0191610f03030b0300e02140c014880a94 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 359899586 1250 359898336 359898359
    0xa020c0d110409080903060907031e0f02240c1c091d07030e10020301210c120602070803090c0a050405070e1302160317010905070c080c07080609160902090307 70
    0xca44c42030104602d4807131a040803a09004d0200c0b03c084941c1c01018040040c009251fa040d03042d642d201c01c0c4110800d00c1569005601d0106c0c0002900442041d00b404010201d16040c10f0003203e00104078903114840d605a9543d1408400c0c5200842c00314040c3e000c94043c01041d603482034810300c0011300c4038131195860055445c00c004100100b019103844500c4103003c030601c001c0003100107465003d80d99605094409440094200b00e0010b144116080d0401180c85c4002c46001d0b02ca5403c0202a961511304180010740a0401b01801c2a40e0010074001c00c1c3d075000480c400514825078031310151595900401048503000c03030b10300c1c01103003050b00704808500c1d07d101c2d118501d41480100500b8014010200701007a6a40c20048020903410650fa80c0e0300c8503410451801000042c1d01484185080d40d8014a5891800b4004200160200b01c00c8030b0f103007080c002c00c0b02500c3c102c0200c80d0706140c41c40613603554503d91240c40c02900c170940030100780ca2810b4001c58800b200302900502c070091a0010004030b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 359900836 1250 359899586 359899601
    0x406120807050c0a170c030c0d033902120f030a0c0c08010c0305010f0b0403030c080924030105010e01110606090910050106080403030b0409030914030709110a020c0d1104 75
    0x40d0b60003021156a080e5540f00140f1000e00142141ea40104186960355407614a1004072030744213600c5856003c0300e96036030003110304003035a1500e000251740c016130040d0340c0d010b00b051201030424140307a09200503000c0c40303407883e5165038000c803000c450300e0080c2d500b510780f50080e1909500c2183c208002400c43c0ca0300545c039000303115108110781020316640e100950300315801060b144002030b2722940104081c034004001400504045280d15140074610341d0f01405007642c4d200010428400030924400507a14000c00e0402c05250481d864500e0801503102080d071b034002d005290200d030b02c000d102c91361548982d0303000e400f9001310303c003c003965140c80040150b0814018104142e52143c08440342d102900c1e40105402410b0382d4542d0b005a0815240240075a03000822080c00365240900307a20110b40d20042d0b100807a900320440e21800104c3c1d4022034100345568202c0b0500ca8140420120340ca00240020024140607a00340c0720404a054204071700040d15140280070540000d299000614140d804102c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 359902086 1250 359900836 359900843
    0xc020a1e080105040605090705060c0303160903120e01020706091a2a0d0e010314060d0213021303020906040e0a080903030d0e0d080108031c2f0301030507050406120807 74
    0xc00541e554160039003583c00445040303400c1901d66082c4550920704000060280030308840c410304000390740105c0703035480c0001001420f00908888070304101c1405009284007464024110140e2140a913402070710741e102e8043c489006103e15280001c643d40b14240540540d07110b40f159500110780ea10800d06150030081b0b515016041103118070003240f01031566000701d586100c014000744000280050044002e0442d418103250a0800038601c80700103540c81070380068202d80c80c0d00c40c0d20550000c141d000c100c000e10f00b00c0c810720002e4035003001006008107074100d81c07080b2050003d91741c038041844141c83d985c1072a11403d40c000180c1e000000c94000c050000701c0d01c042c0c200e030309020041c4e503144203443c0c0707803a07a550440d0886591109650350184035079015000b4140114500012021450142d911000c42e600c0309940d1000050041c010380c1d40d0350801e201c85d20303c443c0701c1a00d400700c036019150310070b110490381403181c03800026150800380100340480304c456906080c140400d4131002d83e25400440201e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 359903336 1250 359902086 359902139
    0x11061915120b15061c0216050607030b09151c0b0907051c08090d080f2a0a0302060601050a02070b03070503060a08011109090606120a020d0b0904020a05040c18180c0c020a 75
    0x4124601d44001f00c010031074010001003415003012200541100c41e0161030714084e40d8103074208407240041000902019005985840d03604e0030b0180200c205541d51040200700840320b00031702c080c1480000d078030016114104c0e1001e00c050352074082c1d60f8194581090050001500b0f000300b5200c0d01d004080071009030300482c00c41e40b81051010001d661940001c01035032200200c010214100c0c241c2014881c440a6030b140184091185505d001e0b5841c00700500740c5040200020780c01100c54030920910004141c02c40c1b442c0d8403801c00080151190f00b00720380c014007850170850005400401401010f031b442d003401345410301d8248410203020803240010038a982103501040110310742e14076841168842e6001c0c001c01a241c12000c241001683e01c8240d940f445200c1c03100500003d40c0d40d03d51070780c0c00c681c422200003481d10340e08a01a03d000070000d6150800000e00c0c00c0004100c010800b00181c2c4482c80c09040000c0144e484046d2520074290303001a4118014500511401510050b409034542155035603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 359904586 1250 359903336 359903347
    0xe13170d021204150e15150901030f02030607080717070e0913170c06190b0907052212060b1207120c0611061915120b15061c02 56
    0x162001c1c0d80c04450080c0d5a44840010001070056902144008012004050205209440056a480750802c180410060f81e45c800f05c1e00c460300380d2804c98074401003e0b000044c47c0da0f40303051009041041d1401a8000d025040c0001c00b1240724100c05c034807400c42602d49000c084401e00551409400050407a001e220780c02d500c0340d00c2030fa99200079a115107004000308210011a00e001e003010614910218840081482084600700b404100745a0200c0348400712a01d24090020b0500a4150740176044d40210b0300c175083c010507550280081a2600d03000c10f982007207940d4048541c0d0501100c0c4071380c0c01c2c00c036085a05a0001800c4d60000c030040e801c010040c900881020800710b00b1320710650300c141a8a442c028000303040002c03d24900000b1700603410000701c00480c601c4400c1d00c803000108184100000c81503e020100d4081d4081c000d0700384c40d081411400c640320140c00750b0b110141d42d03040d40c254051400003650504001022420a08041c0003039040c920b040a603a054003106454402c03016401707000c07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 359905836 1250 359904586 359904607
    0x708071b020a03150e011a15180d03050703080c0301060801050906040e030307020a060614090105060310030f23010b100c0312020706090210020304050a150e0907050d060e1317 77
    0x210648440c801c42e400040c00c005c801042400c4450100340707039058001a041e001d901e81d8494806150001000c0ca07402c3e0345200d039101500b1248111b4040d2503101c0c0c0301d020040140f5921001400c4014403d449004458952401c020a14002449880001100e400050110f410640e16094102c0009000840c80c041d40c1c410190458008564620050f4001a50300060041c103004000c000c017520b030136440e401c40302c1c880032900d0f11005008150040f01e00002241503070002d112180010341d000b0039101500480c5181c01c542d50b000c0c542102c0340610040030325100c0840107219178207032242e00810320070244080140a03901e101c0c021200f9014000c0c4104a600c0702251030000f080490711030400020040181e06c1004010041044a80115802808244056200c112442c0140d41d03001d10700c1a6162801441240c0c4602a40d10241d0007894460502040c070360000701170316a00200805c10b0000d6610b82d1011000403404407021224030340c0c607820f05808035020000746068100200ca49520344000c4a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 359907086 1250 359905836 359905853
    0x30909010801240f1e090c120f140414030706090f0201140a0203031f09020706060302031c020307060216050f06010e06100203070b06030705040e010609050708071b020a03 75
    0x2444051180d44603021000200020111201403c81c1c0080c000242c900b09410812440114042d80180e5024021141583c50803101c0200080960540c1840000220701000b001c1d403400c2c1484050103401c0010100441a00b4003403082a02881084441c00c3c3d0341c1c540302d000d40e2481000544c506404100320302d0011400394024258414040c4c2c7e13148464000501c001440105c0600501c00c003960240250159942d002c01169080741b0700e04142c250385517480611010140c1a42d01450599100180c49020444180c100c04212402141503524001c02c1140c500045082a0f005e040160020072000000420590151040083c040d82a00020b00030b079075107525005130700b1034500c400d03844600108040040c0c0804991b001d481591502541c40d5100c1c1c0180d940e000d402c6000709502340d00e000140b0240c5003042110003c00f001001070191850f20b1440074000c002900880b0f4189041c100062582030292490300e006200c15940c030000400494407101100c16904001c80c1e005880074800004501c202 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 359908336 1250 359907086 359907089
    0xe0d0c0f0605120615040513052707060c1a0f04060e0102040f0b070501090c08150a0606050d090314190905060a0806091e07090501030b030604031d0f04060303030207120e2103090901 80
    0x140c00274003400c0c90800414801c41c0c88054100d20030840000c1c80780c3d54000304011084440320709040c0392082c003038a000250360b0408100005c070031200c001040b04409a02010b54041d0380210800c000219020802500780d1041c1e00844000f49a003040c2007100d8205e10b40200081e48c051000022156a903070388480d8140843d520409141d07001b0300100032411031448004d40c2080021000f0403540380f030504041c1050003440d0f460102d9958a200f40f605040c002e21110f64000080320006560f601d12004401c507503121100c0210000300185c001140e03e0802c4c04c116461560f16454a0b0400d41e01c030002c02502480040903190345d002000c501d0707404034910710841405084030f0b448031800282080001011550440e40c0c03188a0351168080c0404603400c28247c409001241800d003a10b1a440c0010864030b41059a030310340c100380750032800402c0c1640769018040c054131806400348035110a080c21500c2405102c00301e580894480c220142480c0c0c0f8816184c09082c02c1c50540e070400b034070030001460100c0309 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 359909586 1250 359908336 359908369
    0x2120d0b0433050109030828111204050a0b070f06020a080a0e030a0c080d09050303040c09060e07090608040c05040216060605120a02100e0d0c0f06051206150405 71
    0x80c0031020581030310329030250900740c1e00d02d412201d507494040020034400483c4805803240b20001401010003002e40000900b50100700c0c0043c42500301071100801c100d4083c1c3d00080e0381d00905806100380c940080486040b1040284103482017801c01810258036442808101c5001000301000e20010b652400079040610050f10f0f514040c0c0b51540c0c802003990f460480445040d0001c0201c4100070390081c4002c1081ca40244c600ca4451019281140c0205520200078005110200401040140240030703a41a1104144144526680c1d0140903140c0e031070a0310205c01140148006210040c81382113080d501c50700500802079031070381d950040340c202c0e40329070f00030748120f4085844001444500d00481d0001c0c401955026a2113003c0d590090300c4548046000740300e0445c49444060303e03481044001c440d8200100400992445458900f40b0100c49220305017030140000000140c090040007a5440c1d0b071105060080c0b96641d00042203058140d01241108103e01400040b5007610703001c5480c0e0840ca027 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 359910836 1250 359909586 359909621
    0x3007080f010b0a050d0b060310110705010e0706170c0904020a050904050f13021207030b1003110306040f330c02190f08030c0708131502060702120d0b04 67
    0x105411829100b038004124022212100100711688a40c500148100d030040400f0340c498072a0790010703040980d4178504030202400c103201303e00c03042804e40041c00030320b02c038034000c010746510300c100d058403581644500d6010400000345000c040303017201200d541c080034020b80c407450911030b81d00090480e00441c1e0402c0010b000411984100e040130320800d600640040b5000c01d05107840d440740c403050200e00d08004d005284680190041e003004201200203140d110750202e400e85400068044840c88600c816a0404100710944509003404035070f85000f550000a22038003141c0c0340d114080210035400c80d0f5809403c8641d1002444110302c000d495800c41c0d00c10001c02c002e003079a80024908001030b284030894070941001e400c0012850484140e08540c01a00d10f601c03681c0700c000751344c01c500a00034041e1082d000020080103803565401943c00390350130729100d40c59000c100c840403641c5240448408016a21541944d003085c039a0802070034680c9a40f80e070108110320b4800116040e01d0040440400d00e10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 359912086 1250 359910836 359910853
    0x25050d0204080610050118080714060403020301060603090b0a090b180a02030d05040f0e060d0222020d1b0f08071b08120105040606181503020c15040b15300708 70
    0x1079102d8240c140b1f000540d0804403256082280450310b94145e84211b8007888460301c13001c203003038032060160740042d80c0044c0200b0013245c3e25500500649404c2ea0101c466500366000104a001280325601c042a003013030381498955100031b0441c0c1260510241d884051140c0302607100140d07801c00c0010f0fa440040e90341c02c0d03125031801800e0020f081d150303004480c101122008001c41a110048080d40e0141c04840b40c0305007888034010341312070384281020301555a000040190044941c0d402900980f903d90382c03a004850540c20040300e00703221840100700094121004581d115104614100c40907201e00c040d40300d0040c0d2591046101c5d4024800305d28900000741c010800c034a4584100e43c0204a64101a90402071440301d80d621000c03a400340c04602e44005010b0301501d4483d5040c0e5100d803210300210317508036210004000349113804941c22101140190000b600801ca114010300e0300c960003500c45d007407a070324402c1c1c035800000c42c8668034250700140f074040102429003045540c00502c000e0000d40100e4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 359913336 1250 359912086 359912089
    0xd0c020a1b0b090d0303110d1512030e1002070b070308060a060f0c081303080c01050a0b0418060902181609060503100b071a010b1225050d020408061005 67
    0x50032141c80510410829802048812059811a0015035080341d0001c032103000343c6402d0307000788001448003502d1b15001c81d288c511000c40758032560048140c9891040100da84880c5501440d0b402d00c1e0050002d0710306008140305041c0282140c0707612403d401a80c2e0f04907111080d1030311030b030404030703043c0c0c0080d440742d0600995040030703c5100081e2000746080e45a00d088400050018000c42c1c10051040300005404a50002d200c00c0d0324015607409200c1b607640e162680382d00f6004c0c1c04289c5024280300e00d040f4041c00c02d45031600c240180380503ca20b2030003e403405a220b40009220040c030a0741c101c4444e8890000e461100f1000d10300c6845455a190001d012a580050480000e50010418040c04205004c07420401e03103a00c908450180620f542e5542c201d18100305d9000903025886130000202002241c030380c0740000584200000c149015603565035994801e2400e1100b101e022100c1402c0a544006803442100204250650340c5805840d00390394004051500030111801d0503401031910302404035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 359914586 1250 359913336 359913353
    0xe0c06210c030702030901110c030d030e0c010e030714040b040212041703060904121b0302010204090c09030b04020f12060901050a0b01050a0e010509030a15050412050f0403170d0c020a 81
    0x4140060b04501d0100000782d920300c60794108074140010050b0031001950204034032202080007070140c42e09100c038500c0c0540a4030641e000003600d80122288628a5403040544140e41600100204089032800184100084a04440365001916418286060b0300c0c1c9000410700603c001d00c450308945000e0424401480341120080d40d10314042080c0403041d6110954941c000703410081703040800c0c42800060fa00fa280309070341c8860104001900109040e010741c05442228142c440500014095240440d5007000c1d50200a042c103807424003040c054144000b403071010707c134060140c41c04581c035040c01c0c902d01001140e030840d00b07a440b00200080004540030b40405400c0a08043d0709042d5042c0000c2c05503102c41001e1810000c000c5200d0a0700d40d810056080d0094019600920b015219140100580300803034050b10a40030800c403402c50b143c414000c5500041903a0384c05800e05046588401e010388105402c086142002c6c07020210000c4640308000200e4007540007800140b50500d0b00000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 359915836 1250 359914586 359914591
    0x30e0f4804020d021b0c0907050903280c1205100e0c040c021009030206010e07081012050304030c1d01050a08030d0905010204150f03050a18060e0c0621 67
    0x600c46060345442000e00d104030000c005984226005602d03082e0000c181402401000c16002810760700f1010800c2d07042c0c02064410340c084069031400401da594000981da5403048040b65078243e4441c40a149491150b00c4c201c94a81d81e0383c0780c5c0c051600641e5100e001c03034550715800520a1750f000c40511020003c01304221741d1030300c0c440300041c092210b81d07216907a04d803070a206040d07009540321401008040d00c00c1c010b5204100f000c1700100190111420b000f560380400340142c0703034400103060104490900907940d0611500c0300c543c01034405410101c08182c000da40d26000c54040c03006210100028000180c010060b140c00741c000c540711140882d16103080714041c0d002501541c034030072060003041e80100c102c1d2491030b802280803818400d1803400c2d40c02449107a214006010001aa80c007615600400c0c24420103a166000e02c100d4031841e021000b164180c8044202046070355403a00e001a0072078220805d80301240301510010320401001c03484aa108203484801c0d00c200395151101250059031158 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 359917086 1250 359915836 359915923
    0x6070c09150f05060a0207231e0a17030405030109240608030d0b06040506040801020316050a1b0213050703020d11040305030306040504080f04080102090f0103090210030e0f 76
    0x51055180600c20708100d502409801d0180710300103111000ca46c0208210801011075002506004016405441c81403403a981424810700c134019182c810740213825000d80c0c0500000705080040751901c440702c0130400380c2c03814220060106120020341e955007031080080160081c03984443c880703822180141d50031a03481ca4119140c0c5040020701c034451000003500c51000620030300084118100c40050110f01460f4001035200c500001e0100c5d852506402445c018200070304622041040103409a92074000c0080c1c0400140601c4107050010b5070460040d402607002400c1c4040c0c26a1110600f015580f0489000c2c0100350000388a600722130b01441103454076900c4865843c10076066540720754485c0320262140f03100310344a030003081c1842040c0086841460000c3d200c26900c5e0b030390b055102c1c003075001750510310302c642001040c9203419400fa0080c64074240c0d000b0000000481009800e0380100501c04014040b48030b200848601c1a2040000605048a030440b500c840300e1f081c00d46044800e242001720 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 359918336 1250 359917086 359917121
    0x270c090d050f150903130605030601020307080d0605090c0f0901050706180c030c0501090f0504090318031214040506090d140a03080613060803180303070b0c030402030d030b01020a11030c06070c09 86
    0x406c1004588120758080d10890300c0c1081c3c1d0390f00c074000101d01e1401420343c094410200040c0744a004d080b5580404102d400594141e0129650b400300305400380540c0400d0030710303e8400c00649060358071490003060302500c0f80c28001060040d0f41e10b10401c0c8042c86034221000103c4600c14003d0010150380d00c0c00a1809190000f21030313040000d0b00a508413a88640c1e4000d64607100c20b6410507001d82caa40c3c00031000d8503851881603a40742000e0041040c1e040c039910200f1b40c0b0126402007424071030121002d0b100080c0c00740b441c1146101c1400351031a408001a1114101c0084a500940c01444401c103003900a660300b1009040c4032003080404096584900c3c2d0341807421307804218051010040d15a440c014044854080c2c40400c042401c1d4800c001008008028400800c1076002d060405940124006c1e4110f83c030018101005800316070045640701c2c0542d020380204800507401082d0800040f1010303043d5800800054049541034202e20b101711015049024107103c1c00c64503200754045242140c105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 359919586 1250 359918336 359918347
    0x3010c020d08041a04050d120902100c06110c0312130b070c0c150503150a0e0a150305030d0c0f080c0306012a11270c090d050f150903 59
    0x307555000501480001d00c00380c407002905201c0c14002120000b03c1d80d5542d501540341500e00079031200c84c00c08800e008203021030481c40c9416502e01c6494040c55002c2d01c00d02a00c61941e034142c030420b400e00b800b110342585819040ca4101465000381440c030700944021b581f54081c0500c0c0d4000010018405400304d10519400e00110715160381c0d00c0d0b0032807450f06280780340040e02d0525070b4548409401c00c07182070400002c09034115a00070002d5104280340c510f6130a060b80c1d80000c00c48640100d109480d00c405030f400208101c0106640401699031026007003f00480d540d0751001c1c15078120440c04101a0340c1c071403030404043c2d0050b1441780d0189881c84e11500038a0003903000596800050070883c10094141c1c41a200071400320304072200030040081e144201300452405c90b8002545c2841d03075024099401250385da01c0c01003854240090f41d410014046a69241d01507880307500545641e41e40802080c60342000703e40b0900a541c41e40e480c0c5005880003015205800000400240c07168000360310070001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 359920836 1250 359919586 359919611
    0x17060714091e130e070b0f0f03090c120102181002030c07151b08030a0207020112140402042007080a020114010e09120f0a0c050c3001020f1207090b03130507050301 72
    0x103e40c0151b0b09034010940e20355080d0090306003103004100300301ca2015000000d220244100103581d040040c01110b01124191900d90424282d008003403c0804420252100311420310b04041000f200e14898411a42041824082c0628040c05588100e025200c29024110010340c00941d10a0055206500310351700c9850380c3c0d5a55561000400c1058259408907007507086a00c01c490070541080d139600c0a00294000e282480c44a00c02642d080f44034601c0c0002800c0444003481d58203030408440c1c10140d0a00c11135807518043da902462044045559030703142d505980e00d402d800e003800780248003000341180c907000400034a071811520f910788070071009004031a005408102203400b4680e00d8600152f184d542c510b807617443c0105600c092a48080342c40c035920050f86032842074060300805000c4007000603035480c15080c201d104480c1e0000c1400b00c1007040780303c5207207859803d0b60810750707608e0103820700f079603580d441c210503002500c1c0b05860211104001c403d00c0030130001c01010f401c080b4004c00001c03c0406 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 359922086 1250 359920836 359920843
    0x2011407030b0d0212010e010c0f0e0906030f0312010303020c01020304050a03021e031209011713030503090f1606020f06010521010204031505090717060714091e130e 73
    0xe05100c10103449600400054880c80440380003142d0140829001d007019500080c06024075410a03c4158a00240d60920718420041c003031583c41e4580380c1d00710f501019810b10100d0840105129058030031150b005071040c00c2000207140c5901c1281d081242541503250003800c00d09603100c0c140c110340c020311003403009507200c8200000312a4121144a14409046c040c92507440140070903540c940182124a040c1c401c1e014024400ca840903070b200d41c0b0000101e100d604480300c01f55040491051000a0400080c0c040c400854201c900201203501051019580c1407a04000d4801402008142e8908011181d01003160900031101e80c1c018182d55030410000c1601c13000c80b415040548001c0c090f0700081c9003401e60465001c1c40c0c0041d03401c03000041410074500a80005c5da200d01d518429490001040546220103000d03400b9408043c0c0010b031262101180c0c4032002e40754082100c00200701c2030346585e030713101060710a00100502003d1307100700510030030003d8040e1105810139a820221611000d05020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 359923336 1250 359922086 359922091
    0x9010806070915110106060801050109080102030103052805070602070608070e090604020f0418050f010f06020a080a090b0c1005070504060512070516060608012711030c0a0609080c01020114 83
    0x840302d00d024026a9070b011030318104c020b00510129441c1a8000c80c10581c040143c174107903902a2901088607684400c40c03400c034130017403202502542024039810310021a010101440301c12040c1c200d10101c00d107881c0c59042102a512100141e400036908203c7c285d0046074603035124280d03081c072071442818a400310304040303401801e00344115400614540c071a49400d09850180221015030324624482034400d000a2605450f0600ca07588103074000183e40d05040310344000d07918a41d001e481c209429580d0000507030890752520f801c0c0080d0303110124100750004003500f03052803410001c110f61007100c0f450f4011100d0140400f01001410041408400d4008e82110722140524541401039958040b040300d0601803480064072503142000790030203024483d08050103a4502e10300822800780b03200d042d0515402c0d100501c5101000c03100c003460104040114041070410081c0548200c8182034000880c10030340c80e00f01e4804110108405d0040030380401090801c3c200a0008000c00d0641440c07110500500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 359924586 1250 359923336 359923349
    0x61006020c0d1506060201020702041d0304060302031b030403050702131b08090102160c0608010602070501120218100c0c050907080c031801020706060503061506180d020904050a02090108060709 85
    0xe0b00381d101c003000022100f10035032601c0c80000f0040c90741c4651009000c1d6102d208142e11032410803d410740300c0100044416965007000d00210b1401d80b8003601076019400050580c00b4040ca0600001c42c0e0584803002148039601c680d0b2526910702c4a031042045800410f03204076681450214012803a1148500b51850500350342042c3e000c80da200c860190281c800e038501071404070260107d610401c08101c800606a03511a00c0b821090780e2180d03022603071440a8071409000641141c1c0481000000303030f0050a15040b2604684014407030070000c40d0324080c400300024000303103200e400c14007400903100120016020858001d1a20b0504a0005207444030182851410120003c0850001c0c210100b06025103403901c0029529440d0314100764004003003610689000380640b02c00030380700b400b800f240c0e1004403800518550070503035410b0b05450502c440b20041034003c5a16a440b2015a49404d81035202c2c3d03200710000c0580e4061441406828107040e03200b40104e074803584c1407008590b0080d840320165401c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 359925836 1250 359924586 359924599
    0x3c03060705090f19030c1a070f03030b28050603040503250c0f0f090e121c061e080a030207060c03050f031603240308030402060c07060903020102061006020c 69
    0x198400290308020f101a071958040001981420310a10281c50358003203c1c003c80c0140c1a0ba80d5401c0000c026000c884920090032000300501c800080b800382040400038001c1c40d00140d11280c0304082194101c1003000d9001d2404100080315104584d5114080507113019070f282419030800343d5071142e0b203000e01e0148485a0083c516001c06004000c400d03440020382100c2d00d0410181e69280801e40004580541d602c040f0603440c0200b40b01c4101d005100240a0750402001c008040000e000d45076000542d2441101c01160074031020042d040c0a0703500074015220300000f40a403051821035500c0c40729484801250010103010f03000c02d4000c01c00004507469030502c00001805403804944a1050310b00c001c82c030380b40201c00e200c8145501122408003804a40b420003420343c103081404035240801e240303020380e0103a040301400059070b15409150024030240c025803c041b0502550b030704100d41070f000900002c082c00001c00541d0303410444d080d0000320244004c18010306108000b5190015111401d00030b01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 359927086 1250 359925836 359925847
    0x10603030822120c060606031802090403030209030318041808030a0e010f110d060e0c1804230a061410030c020a080316020f03040e060d060b3c03060705 67
    0x142c82290461002d50b200c5020003002c0f8215802804e0480b602a064032060300d024804a2218064070849050050341d0184004001c4580d080005440c00240200c04154080c40b0442c1141c500700050f00030703104c1400c41d907040c0c03041407030900c07044803100610710f0131922000030144d010640d104102c9070441403400020030000c10961845025094000c8000f04442c580402c01503034601e40c101078440b441c560b000070301c88103075103554075402000e00b9640208101c20400c9850160b0596003500181c44001520105016440e05c2076440d03e4010b10140c1020760318800e0410142c20320754402c07a0f014001c1e0090054034000180b010840082000c00c001d020f240c0e503040d1021850b4020080c40b030150f0f0740910401e42e28034104400e00c1c00c0c018035445170b201600c69035160100040c00030040d43c0540d00029801c40d45655541308001c1d44091129003910781640da4aa5104141c98580c248401c2034100300010003041c8611120140f40d4411040c0c02d005112000e89500ca00d60340402c3e03091f08a221480c01c41e8440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 359928336 1250 359927086 359927131
    0x150c090a1a0906120103140a110f0d0b04060507110a030504050402071a01081f02070b04170403050a0302030a0f0216060e0a0f08010b0411130315020f1c0c020106030308 74
    0x244510030815502580204080442018041e14036040c0c1c0c1c4249405520a141f1680303241c0d5640c480c1000804190107040301d00410b0510082191070f500e40100014513003c0b5585034082080c9007654291422902d803000c2182450b08040220240303041c100c0100b54040460300d0092041c003480c000e8a00c5250001049004d00a100c4110740c0f403040000e0281020f1359450708115682c049000340e04c400d16030401140000f5609070701c00d40d205150881c07003046140d41c1d565903106104030720202c50301451005001c04004642c0401184449503c0703a0002c55070385a1005002e840da01c1d540c40c40c0021940411000600640480268000c4643c507040254403401da420004190107080d402c0381e55081003250000517070450540000b400e9000035102000548201107034251f41c0d11031880e664641c55820710080002408089090480ba0304002c001030406003191040441507200600c0f5040d41040101e61200000d0a4800c034440303002c0b03a0008109070f0b4613569001d84464402007501460016440e07405072035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 359929586 1250 359928336 359928389
    0x40905070e040e0a050d05161203060314030d0501350f0a0c0f0b03040f0f022e080f0108070e06190620150a0c0e03010608150c090a 58
    0x503075030020400d03c01120300408560390b54110040542d80c51003810300d080c1c2180c0c098800c4456820605c140ca1801c013015440c2d40101030007180f4103000300341d44c59000102003441c1d00f501008981c060006113650b840a000076405aa2040c0c01103040380503c88441010300a5032080350b02807150815040442c2d0803620b48044c02c00c000d80d40552002c0c00394891039020046095005010f48d030100100300708140c0c4078080802c0c2408103c1d0020510348441c0e040c080030900b1172100c1d92606200800340300213105004150140a0b10a611150103011480e022140c050b41258030941d202d00b00c1403040c403c83d1724001119035100180d104180c44200d004011170850380341c00d800145401c5403041003024603545c6540050a00d1410018201242070b00e144100103401e01003000c600c0031300034016040c0c40c1e8840c0d03d0080c0080040c0c5000200b8450701c0000c0000795203080c0207250080a4240160140c03501c138440544420800030000042c0ca90208400c80a80c4e03580e0034204141c800d0311311a60b00100d1a070804011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 359930836 1250 359929586 359929607
    0x405070c0516170703050a1b0b040b0319110421060203070519020708070515071407080f150c03100b040f26060103110f04020301090515100504090507 66
    0x3800b8841041c01c0000501c0c02030400c6a41c001c1c0c3c2040c0354203211600750745030070070f03408001e00300c3d00024109400305009910030320544160b00c1308128065641c4004243c1644198010f42c002000441005040c0c039050034a0350700c101c8440010300c4900c4013490460310a01c10b84c02024041031042044600d4000c5010300d10081c03c1e0320400440d034a040103030000d080340c1c0041d036400c080b08461041e00f503c001c1c4041344c00001c032140790004116080c100002c02845c03001150303d01062000070700446001c078014041864800240707501070900c49043c107509a00307154000c04400c4156000f00320400d941440044910f907c080100c0072903440751141c10740030b04d0703d030b0342340e400070443c3e04001c80e01207522040d514284080300d903940060354040f107100c4a04200c01450030920f0000750000c500410205501000700e5201850041174100740b41300d10f1001800302d801c01e800c002442d907581c9003007103040c12911590840120080791500252000c500c0010014441e9000d4080100d40b9400480c0c80315018a000f001c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 359932086 1250 359930836 359930843
    0xa060f12050925092409020d2a08010f0b0306090705160311060a0e0606040e01020412050a170702030a1e0b130b0703060503120705070b07200a0506090405070c 70
    0x15104100740c610301000001801003101a614150085510581d8000d150780080c43c0c07008600d120a1600089000a4114800a000d0961034074100c101400001c5089c029206507844501c05441c00418010320b00c140507000500d14030764183c410300004404009a9600050445501010713a50700c460072105c82c00307040040b81c00c0c0340c000c4460790704054020074283c89114130001140e01c10f80d180646441503900752407840300c0a400c001c010036941c2c00c203500b00c0c804082d80d038000540380c2503694680d03d8040f0040101078482c1d41110391407004002c00c142c0d00b51109000c5405150a2030b07110740010343c94040c0303848024100f40065408907010428401d8000815030094403513542031905220150881d030401d0004c40c0c407440c0940002d2182c1e030103071140305c0580e00081c0c0100102c518110710b1010903402040243c50500c02e52400081c0c00c4550340081ca481031090264007410019200302861080c04191620300c610f206010030700c016107525064460074101103402040d281c6498900755881046c2c4c04015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 359933336 1250 359932086 359932123
    0xc0607080d060b04181e0905070312050901080c0c0616030902090c0706050f01080d2601060f12090203030313060b0904080a11010e121b16050a060f120509 68
    0x41c403140300341c01390003110501448445500700365081001101d803d0302e4036030702e6000c41d03500d0121803944075881407400c14414000c03662019125211104140e0504512000045000403461655644000e00075007000c07683ca00030b8141040c1510154a0344401866017171500003c100d10b4644074400d0700050082500944030b00300c41d061045500c1d481e9800200c00742e03000c81c02c3c070300030443c480c9a1100381030480300c020b000303400a0515404210342000580c0700c1020106004040704410040d0340000d10300a1030f00d038455021040780318030082e2000d0f1240412541e43c51030810020050707103001c4200c0c2c1d40001503011050b40943d4510b0260014282c2c141c82d07640141240c7d0801c0200480c80000741000031681d100c01da66038444169807401d0b5018207201c040e01d50003818050b1105080740b0051301c401c034100a030903004050095200c03450180400140c5807075480100d810080c5050210f070104c00307015140381055080358900e001401a408401905000c00d0b910000101d01c0c060501c00f86102880a4440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 359934586 1250 359933336 359933339
    0xc03120d0b1c06060e010501051303020907020f010e0715020303160e40020403020307030209070302210a060f050102060714190c0c0602060f04031d09191a030c0607080d06 75
    0x3c1c0c00504407030181115000100d8004100c43d0300030001c1e200b0040da2800d400d00f8260071a42802041c540103084c001c150301c942c0200d002045070078080d2510320a81c5400a02d1520720300003403828141903003240803040d90002c02c01e101541003194445008001c0904150010080c0800480c8460441c00710b041200c0d40340c401d031510310540744001c64445511030200030221032135002165089100700c0c8002981070344407100410050030540d038015440a03403810700509015440074405041c5403054403080c0314515a404100c0035010f288545005007120181a07011541480b0003c0c1da21007002d0200b07801d00030030b82c08044412458008032020500e1b0282900692403019002070503000b6072200495110003040c6011602d2072002411500c0f82c000401c0506842d180e40d1401c0da40000c0000007410014804402d1200c0b64907180d60482c050704d12180d40c440c5442000704018122609410000c0c039100360844130042d02e03030300042c0540c9442c0c0d044501690726003043c80c0143c070b144500c02504400d00d0a0010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 359935836 1250 359934586 359934593
    0x40b060906300a0f060b0405130f020f0c0303071b120c1416030c080d0f110c0a270b09071103120106020f070b1e0d02071505090c03120d0b1c 62
    0x54803165403100e07018403105480d2194061b1600030f50041c0da4000800d540701a400440c942c00c0070558050400005107040d025072101c07040d66003c10084040baa1000080c0034035a41e0020f001009114182034540d020101661400c1f440c90303240342d6420400105000c3c1000340802020b8500d940030140040741c0b070b145050114000c40c20b00601c0251200b00c1c5001703000031070032008119503900c540c0b942d40c1c1581307a103401e610640c0c01c044580f2103029544039824000c03080751142c0ca4428064211000d186060443d05048100381100400048800508208990185888030068281c001000342407051403800580515807841c010100404000000c400c0001012034000c540360903040304100648244c10b071070744001d001c00d22620340c004c400c14140d4a034144034140701002030708174500103490140c505551900e80d0101a0354481c204d04a5a90310304c1408007020040040d2240c500c41030703014001002c1d10804584080c081d6000e42c443d000d8540041d07000300d0340c0d07051061040507458031010340a40c100d0308 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 359937086 1250 359935836 359935841
    0x60806060a08060103110105070302030d020d0510050d0b180a0501110a11191209180b040518030f03070306050a18050703090f060e0327040b060906300a 67
    0xe03606801441030240c0842c0349840440c045060743d03040460a4901c2c080e4400440d41382d4404001901103000500c0302c01ca402e4168001080581c003019008a40341c01c5c60502c100302142c03564402c520498208211400103621b04501e264421581043c00b40740e01c1e00e0361540c0d420b108428000038210351a1412185114581f0009014140151341c0c88a4045013003c44031366440c9400c40e28400303080300410205c400204100e61100401540d4600188080c0d5a641401c0d8925080c902c89050240c039410509a11309140c4a031903845103690401e011180e001d41d003095103d2191a241080d010000400a094107020b07401800c001c020181416403055030f2a01c10402d4199400d4114112074200804a45124404d000f40f282d007035008401c03810014074542e0391100516071318074400c015004c280007031041445510030544000c06403804402003130081c50108011140150503040c80b518051110f01440d846100580301025030000404241a40102d07056442d1925580b071215487c00e054104807a00f041178 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 359938336 1250 359937086 359937091
    0x13030302071e030c140303190c050d051c05181c1b08040b1804020406020307020f03070e042907030e1e030f13080a081c060e04060e01020d060806 64
    0x201070400d50741c0c8070600044040b040c0310191254183c0030052110aa120294100300034000b0101d9140ca0b80c100160005400104034850110742075450250030b01c030007032140076181e0034540b0702140b910100c8615030b051800c100025280302030303842e4000744404d11031400c483c0301038405e00106d5100c0d03848005c6010000d0110341c55000003485120f004500e0310007a86802c0203007540800d580f81010b00340301614801d90400110181003441c03c0c020070b2a00e031540d10040014000341c0e8091683c58045005000403c100c020005029078041c00d030400200329402c0c4074179003050380040003101d11484c070600d0070b4007410a20481e5000e03090b00024810600e41690048e500390591030240d500810300d0b890400d090b14040c056070042c540040181c22684000035004001500b030303000c145090140c0b600c182078580541e40e00200c40c140741c0050200c000c1e20140702004440c1003005800c0c46502e0401010511380b103030140000b041a503c4001d180c800384401e4041d1800c41141200401c4003a41d208a690740c0c4071800d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 359939586 1250 359938336 359938349
    0x2a0b04030f031d010c02091e01140415080a1101020a0602030f010f0509130602160c03140106081603061821030c030b010518150a02030c06060d0506040b06061303030207 74
    0x1d24007640c010140700001000b20f00058543d0f10364002c4a40910800b50b0004094090054031640078003003030a00712880311b01a03e1541400641000c640c010701c01161411409100706c1a03089008000c440d100140c03005a840d070165038100020590030050340384c01c29061000703007818004405c1080085400e10041c0c121103c1d242c81d1420540d81c3e10500a4007801510003050950041b908200407030041e070018801290480302200240b41c0385d440f6412140095001113400350b0080c1d83e01d0b56040e5003402050040c160800141100003601203001441103040d200080c280394490300d840c0004101c03800c08140c0181c0001845180b003c0b0b50300308948044017010020007080c82c1c001805c0b5660f11034070940000b401c041c4c481721714100810004c12071409900c0003840d80450305a071a02e94101c005005000f11196a800840e00e840400b01464103220b4028101401851041040408141c0004443e50040e030890608411a03c805000c94590f10419840b2011903486107000030401d54002540d100700c801c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 359940836 1250 359939586 359939597
    0xe19060b09040203030d0504150e06180f03030115030b0405090f060f06130b040605030a080703080106020313271a13060b1e0c070909021c2a0b04030f03 67
    0x11a801000215072054401a405610512820030226050b40c40315030010300950001c90000318003650070050790501f0f20203032032030742040303091219164498025401c07402c101000b800c0e2001004da100b1740d9074001445110700001c1d001201109550181d40030405a003400f900510451901c1d60050359980c0410020860600c03c01000540b080d80200c9114005c5400406851b0840010b101d00005000c04890781644035649240010b2265030030000040054070800c600c81d100c0b0154140900100d105074071100554104020000d0f18400e015901c0e01030750b16448000f09294140440d100e9030701d001e01ca6070405546809078042c0e012150b521701c1505035400f1549400705220318824142951011701c00d61695107030500000001c041940e0804000e80c4c10600307030074180f45c4000c00f994940740c3c07145d2086107165500d90f210b5095060030381e20100307425007030a20f82c40180c440d9525040300728051015440c086406084924030b5064062052000742884a03001d6143c64503420a05610444410114081070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 359942086 1250 359940836 359940851
    0x3021003060b0f2b06030b090a110d030c050706050316140f0a020a0f0602120a020309060609090703060e100b1503010302090703020904140a0e0a0b0612010e1906 71
    0x14800d00448094404401640b82030204400d010390168204d00000c014101c0b40c105210301c1c00c4080c41d000d10a0303c0c0f04000100300149141000c4008020160800c1c0c01d607084030103031602242030790142490321042507400314100315160504541600503160001c009014014000802c198440c019600405100340214100d442d041d0040c9c641c0c0f0b503004005074094206005400c6890719100107814000d455006443c0c0404581d1340780c0e504400000b4007200c400d0343c04100d12030081503c3c10b00c0c40e8000704040046141d410051030642d59801b00400c0746104801d0030001035014030042c04190021903112000780b11303940350302d2000b98071810340c030b0401350801c1d2030300c40c001a440c5004001000c07403644007100c49185900316020f00a030060000d10003001d25400f041000f140d80c07906c0c803691000800c08440d014060511140707071000e0b2001a09102c8090340f011070104c001c0761290f50020703000441220840b0b55001200c0e80366024123008009408603008900c1101d40e100e061f52001110701c1d114000401800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 359943336 1250 359942086 359942119
    0x905010e091618090207031211160302030f0a0e040c0503010f090e011d100b0a14061602061b0606030703110603040c03050d0302040e060a06021510030f0c0302 70
    0x5030020111030340d000c0e0025012408010424203004900d242034907007001d0350940188403010360034440c2d100300341d081d500140c680f0603d070f440032010b0302003d040304041c010303124505040589809031010905400104442c031000b0103000f002190758546400b044c40d41c541c65204c9019004801600c02a80a05d080ca1280884070784268112416541130b9121284801d0a021460005106425030102c45650302c015a04004d03221000350006000c11400070400c15040c0f4010200b40c41c2000c89480c068940300809000110000c141e00144078010350700c2d140c4800c072541c2d040c0c00c148550400607400c102e00060b982c000301e2001124058444141c001c8416586442e0180b507525985880050304049013901044020306c4c1103402150854010300362400c13119101c2d210703141002c00074a204004643c3c0090100720002038200c00960041003150450035251500c0d40107515200c0d0520410741c10810003001443d9010100071240195070005a84042c510451501a640001038001640300705004080352900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 359944586 1250 359943336 359943347
    0x4112b110d02010503160e0d08041d04051009290103020a12030c02150c0129010504050604060e060d29030a11100507080d02041d011a0d021204060903090501 69
    0x9140c0d041c0e41d403a10350760f201810f601d038140b40c4441d11020022400040680340e030b620010808c05070f02440382d0320b81d03452625501c7d81c161010009526140c01200c1c0802c80418400320b440c000540004401040e00d03c01c52918880052104190f503980c6100400c182c03076180b04420314141a02d1003510100151911243c8120116000c00c6c5c00038005080b901c03c00006080c030031420180307400c18058460034046001c2550b030945181c00864402c1940301c00106506a0341d10340c3c4d0311085142802c0451402e401c200200e03078184943d0080c103040c0200159114055128002103540c486140c8100b04611b10404418810042c151b0307a0b007501706416603071030014514001ca04602c02030b611403190480251254103001000c3c61961040041c04810300564000c03c1c0260010401c00d41d501000603520b80c03d09c85121075910714000d0300d95036200080700600c0500720203d080c01d01c030180c590b5804e8503074200884500292145c1c4550003040342504041c0f1042180d26000701141a1007903c8071200c66403144d004594 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 359945836 1250 359944586 359944609
    0x30421030e180a09020a05040e06101509031e14030702030c041404060f020d0c0207050a09020c070905090c13020901081807060c020a080d0503040b010608060904112b11 74
    0x544034042010a103c89000e074030684c0410305c0680502d24181c1e544000a007210741c080843c10345034008004101800d60450040000f425019800345010007075001c000b4556000c90100400f580784a00724217584c00007150058035955031091800741280d80a003c26500c80c1c1010004038001d100340a4210141d00d000d0003810b035541000c40c1ca00031280d80301c2d214a005402c40b011040c40d030365400c0140c61503503200c1d805000100c0c0c0c0580c0042620f1454103003480714802440e404540d150348140720500c4e41c4040401e000c000c03a072109001140c42d80750407c841d420085000466a40001e071030410600020941d0041c05640000340c98407016582c07801c2100c92a04007415900700a0b8000520134011140a40c0f0051542800584105900c980b112142c0d440c1c020b01040c4140400c001104000c104100542e106014081ca898480b00c50b003000b80c0072400107400640010248e6401381400e015a4807080e1241c00080d014550004e01c1620080700d00740d803814903030000e0720f407101c041c2d100c1c160030b0400c1d420124 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 359947086 1250 359945836 359945869
    0x403050a090501030506010c0b1e090106030c0902070b1f080601240306141e06030903030609071704030f2102091903020f012708010b180708040b09030421030e 70
    0x50124410749c0c1d5005014000900c0c1c044441d00f810080c42860224464841c480d891800000403400c0c15401c1484001c0103a50090078190300401a540000e403452400301d40181d18200364004501481d10300e000c090038103030401ca84900c22440001018089001d03e2926440e06100030300c441020854100d0544000f80200401d0305045000042c90f82070012003c00d030010444e0a0300105070b03104001036695402510107143e203900200c1885003529000c8500c0e50024234600340000150010043c1c00f40024000b44060144803100310030350740c02405542c1306818600c40081000c01c007000300e50b140c0000e420581c0d9090180140314080c01011152100d694141d076002454400c600b90450011a12100c20800c0070680d4201c0085010450501070400700140044000204181224400707003c145280d071143c102c04001e9446c00c2c40340d450307000100c1c42d0308507812840c06d070200d940f2081d0107403a40c4529440b0901881d0009c5208448000315005143e00510036901c90707051128190400510110126800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 359948336 1250 359947086 359947097
    0x80f040f080307050903030403050705100c0b1b070b040b07080c0c061503070e0406050714030c1b0102040f1e0602070e01091505090c0c0c1507140a0203060403050a09050103050601 79
    0x204086a07a00000d540c0c0500240f07001c0349401d10100120741940c0107a80f0031146540521410b11040c5058017001d9075400c05803070016108091030300c90003010358010b44509030042d140311000c0201e0360030804850720b1942000c5e1421650134180303051351300e40b40103c65260006119202040c10160142e0807100664446401883ca40e03c43c034810020300000707096030a903d403240da040080c03982e070883c2189104070f02401c4000b1700362615036005001d4000e19011080e0381d43c3c0410800001c040420f09444610b07090300750103c02c196400d01e8071402840303980c00030340380518848400200203202003800d80d0711014801d47d280b14513179036280590390b907003541c041c030280343d00d0403401030050b01e40d80d5200c0a150900241f904040c196a60040307019070a003a81c2ca581140c80c00038820080800c02c111402c200c11054520001c40c8140c039240d90b0250242960040c04151000080821500104038a00e0020340003000e81c4d07158182480e002e0019404a00c1c0380f0007188040b05c00099960003031150034032400040c0c6a6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 359949586 1250 359948336 359948363
    0xf060903040e1005031c0f0906090b03100b03191d120a0c06020d0204060f020a020a0b0c0a05031209060a060b0304060e030d050907090f02030411061e030702030a080f04 74
    0x603214a6000201204510380e0741400001e12170343c0411103841c8040856403d00001101e500004288100c58250301c0700340214980c042100790f62103000342080b501c50f1105941c4079101c40c009904941c04a0b07100322003640c0c000c0700f4080d060010303410184401002000410a105040e0032401c0311054412351251560424072020b20702c181540010610f16915213024414030016640f024104d8020068000b0b140c0d034080b4060001f41d030442c0c00205a0180c5000510682120313a002a408107064011060b20132808201140300c2803040000070443c590180544c0c2d2216408090081c07040c4003210f020f0214130840c4041910581144503000545100800d80c0741307507580d0364a07a000a082c03007031980b0041e8441000b14074404401ca218103030089041d000a13003075042c40c01c0c0d0102c040c2c420301907000050301d01c10424080080c1c0d901484070f6401c801a50059241c044032000e0344c03a81c221940b001c0c02c0209000040207107055000c801001d0f03941058850082c1d40d107404401c40500001210020882400c4600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 359950836 1250 359949586 359949599
    0x302011a1f0c02180a060609240e0a030b0f060405060907020604020105030601170403120c030e07031209050a1202030d082221020a060b031606110a020d0f0201020f06090304 76
    0x400c0b80c03226001030429090302c40d07041c0241604250440d048107007582d42e0fa401b4451140c0c404501001040710244d0540c06030325445c285200b08140081c90700600001c00e10458140c0c68410903440115044000c841080c41c10030890300b41c805c81107d484c5d01c5281b030300000442600e060000c1c940215401e500500c00c0341d40f03903401540c0c8c96002422681c148410b80003c0500071510740ba030180300758441e40d00ea98101c03100210103400d8038401d0205500b810708008034048424000a500d104980d0020300e50100c1e41d15100007039600f181d16411143e0081742c50100400e007102d18040b91401d03c4e01c240c0031135010b1243d290048075031350700c10f440180710523503140e080007620180080c0117045140200c0741070b401c0039881460891006002d0706280050f030810050700b03050000501c0b40c00044034058004e403010510301f031003203c1c070119107000d00014011448400510002c0400044402a42c0901800700494003030428000c01c18207040c04900500c02c004400300c1103d004100750f401a401c3c40010340c1850304140 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 359952086 1250 359950836 359950847
    0x412030c030e0409080a0f02010b1e0d1a0405121201061110020a0e0a0f0b0703050f09040216061506300f1b09060207030b0c070f0302011a1f 62
    0x11400c1d000c02c420800d4031085999948110b4074a01e03c035030f90f0b00fa610304120001620806c0403164103000e692502041d01a1a16410448290610450f54a110b4035000400080341c01c028410090f06024601144900010012003494001d81c0150708803410205021840110f0f44a07804400c83c8441c3c881c401001443e01814254800c0c410b01e0b02501d20030900d001d0b041007260442556031000480044003a10b03c0e080c200102c00107002c403150050041c80c20300885c0038244c841c50100808000c0001081040080c1c0130702500c1071064002d0044d03540f0400c4a60711640100380704000d4850520b803520401ca8024001041c0086803601e07201c40d05c03c4007003a170f100b210300d0002000a0701003811411600d00c4400ea43e10076006d80b030913008030020380a0b80070003c0c400e800491803081e0092000c40081842270f1a00051100102e980c41100d00d4800d50f141d2090352001c0c0a8120000c05140030103290808041c0c041d04011000018003040c004070041ccd02041010011058440c0c0c0c059003018521803402c541300f035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 359953336 1250 359952086 359952107
    0xb0c1903020a0c170d14010e0f0903070609030e1017040303180c03210f021510030506070305070e040b010c080705120706050103020a1a2713020c12041203 68
    0x90800b10403c1405445482400d442c0c0e103040c0d18140030004904080c0582403086901c20015615201803a6060451a1228120143c014542c00c80d4240000303c0c2998200111018503a00210600640c0c015240241040c0e02c1e02a007140314a00600b100341019102d4654480110701c8150344075107640f03c1e0303101039001b041e85201210b80013800341a860007040006c814880258400d901903012003d2045410a451158003807030420042c03046000109258005025141a4903200341700da0251141c060b05005018154002407460041004000041342c060384420702c500d0300c5440301c0041b511110104011120b91162042c00b05d0342242145000c507008002501d07080d449042100d01044150040100d030342c000e11b10807500c0f15100c80c014004c504081e01468003c04e072075400c2d000031f56200302c2d5100f0386001e046603000c000b042c0c0c5e4100c00c1d61070031800d038142180380d00a00300483e6141c4c00f1040302c02941c0200c5958140e03101d003080d24411810140d080720100c1e80b0303909040309140c00c0c0380c3d01100d001c00003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 359954586 1250 359953336 359953357
    0x1902030a020d0201050d18020f120d080c04031217010509060a09150e16110c060d0218040c0f020c0909031909090f1a180a020706270b0c190302 63
    0xe0202144207011b900c22401e500d020091480344940e080c1c41001001e003010b9050b00d0141800d0700d00d09000d50381c00074444007000200e041032189580c8041d4810b284d0b0145a0018100050f0052202c0d0129004004020118140103106415a8850040c414410025209203402c5403110f402040b0420680e072119514944481d481010665520007016207500300b5500e9642d0940a0081a909650002c1030039600340c5811000d0400e03280c98000041d507901800b5020398405800182050900d8402040722500c000010070030000140091402081340c00c10200c904d0141c86200062038051502000251103030b000c01d40110b180c202e001c0410048000498819010320040d04004101c0844d203010320702c401c0ea1700f40c074001001c0b24542031400d071488581c01040d0158030800c0c1002c060b030180792566035101300001805a5110b2051030040b0007000c1082030000001040c610040203201e40b0404049194019508020701c0e84038680044c44500c100c0703d0303050305142c580c401207002c40d01a801a0081c02035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 359955836 1250 359954586 359954597
    0x81303062a05250b190c0504060e0f0301060b0c0c01050c03220305030f0a0f030504030e04051509040f0201031407081303050c1c03150503060a02070606080313081902030a020d0201 79
    0x249030000f21a40c01500c0304075582c2030950708000160000e8029480e03c43c84d0044203010042034000c0c0907001e880b40d800b40c40304112005c2d8100300c65480c0c0c0c988800c092400035008012280d5107407902189078000180c0c42c0b40601075540c3d4407802e03611800689401030b0411020711b1074882c041d4240309159034504031035181e0043d1840e0000c0480c0090001e0011450031071382c0656595030b1020020041b5401007942c01c1854540000d20020a0344500e02c46010002a230340014280c40704518080182862000940d005072203808200820940a100180551003030304c01340026220492040b1801408542e0000003503641000030341984e00c40d10020903194001d0818600e0214901030184c02c00d91184030040000201280c4095016418410040c1c4d02818442048025051900107900d40001405640c080707500411003600b0f0040980c01a001000f0210480c0e58a0249885008000d00c01d0b1180d841c25005038001c030084012070301d0f0b00e094400d038014040c01311100769908009424440d59402da04018 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 359957086 1250 359955836 359955877
    0x203010e07090e100c170703060f030807060501080105010b120709090516140c0703060b0f0409050f01061d07030c03090c060207030510090b06120a081303062a05 71
    0x90240714410252003000c4003c141498003c1c00f107450400e113071440b01252072521621a80c0b0641c040c03d0190040d08002d0311412030380b29a4811001350046810400c1c1d40352943c14000100142400240002c4c0d104480c18451031380c2e00d81800d0f0894400b44145030b0f10761030420840b10103610617400c4940c4400107080c440749180d15040c40408991045030718030585e060060b039000075103400c401d1280d203000b0300b84142841d150200c019113894a009200040020381c640c80380c40255a80d039400600707c130202400070080025242085a55400740c03030255174065181c1900440c0d00390664890001e043d50021640c000b039102c40204038028946110038070105a582c0003110700152034000b01000030401c5600400466056003800c5040412840300d8103101490052030380b0014520003025540701408407030590030181034038484c03030903c3d841400c010694540091204650f400045905080e02d01070350003000740c2d046140901c5045400300c1510580b01108100764044141708400403c5c4a80c0d004102081c0328 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 359958336 1250 359957086 359957111
    0x51905161e140c071e080105100605091003061d0718030c030308060d021513060513031101020f07090f230105040203151e0405061f080a1103070f0e101b020301 70
    0x8445d18807900e003800500003800c0182207401d0041d0340c2c10880c82c9104044040c03400301e016083d8400c007900030707008840914003014014000d5010a00400909a074005066040030781d0b0003041c00202d54507401304004140d007220003400b521420301580c0c7e121120288050640c0c60984402c00b00504041c1c1c003034005450000182c80749d08401caa0b04403410300441d11415040502808040650418000c1000510000084c50030301c000400440b1741080d80a00c100d4002c1d40100d042400c41e410b1039060303115031880002c03034506542c0300405803010b125080125010020f108a2400e150340180c10111104100500491420743e0085400c81c0203100308482e108804404030301811a8440001d000e403d94010100d0b40341080c1c0143d41c0e018408880189480a0407801018032b0b400d40c007101c900b08800c4200046481105601c070032140b4a04040c0285c5914101c007009054048080391040025660080c01c11107080103090a10700c0c4000da02d80004031034024030180e15030b05926009a03410f40d210207038403018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 359959586 1250 359958336 359958359
    0xb010b1b1b1504091a0f0f01050409020714060405030c010c0801150f030b04060303020105040b0a061208070609021c05070b190305090c06040b070b06030703080d051905161e140c07 79
    0x18a074030708100882e80d014101c108503500c141c01ca003542c003c00135001201f656aa000c0112010354000d072000580784c011078141402c11f101400081c1079544604001c1c0000e0120000291082082d00c1000b0b00000021080499020100388514000d400340a105103540c240640c1d0701501c0e001070380ca40016070800d16400242920704c40d074402d6015135980d40902050047d0f0740c66956000010010910003d482e00845040c111540c03e8080d110240225162041121039003105104903002000c00000b02030340e07145413705010340a8204c60350320031007100050940c599001d40341401d40d40d1a00c900d246900741d10503805000014051910f901034000c401e0a01c2c0d440d1400b800c00361182c000103035146c00c2a464030045401002c0c0c95070b44258411201080004c04400407101140700040012510380c0329501c02a1400782d400390201d1042c0d081208003d10300708064503a201d0004941e603011032103604d0509101d00324513080707030000000301e12031040e0720000c1502005000c65000c05088405850fa9081d80c02c49 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 359960836 1250 359959586 359959601
    0xc01030209181e190b030f0703080f0708030c09120a03050306100e0a03030504050a090207051b18151309020f060913020c03070212151807030b010b1b1b150409 70
    0x180d282c40c150f03001c14204d15a1080200b0400d0550003003e01501d50302009550302c0d03103440010900d100000c4c80c04540303043d40b0252000580d024042ea0b40701c0c00d00200c03050060300940400c0303002e080d500e03c4010004c5000a0780e4481d064040d00c0343c6196464100c14040601d002d0b07142e03407007801001c1c84200e405855200301c8500440c00303580c580d074480b406c0c1000c0100161040e4840d400d81801440400c0125002140700d6000c030721154845007221a5010104041151540101851003100000c221206003100c00c440d0748994101d40d440000540d0b07040801c11504484406500001421000c0c2d07200e080c944024024408001c00f49007018080c506000300380c0e808421000c140d90404a510030440c20105900340380303176451101510460307201c002e11050440004180c290f604c4d460b00e503401d4014009001e058003458200050f811250703190b800c24005680074110703010000d00d43e8000380b50300340303004219140340c003005140421101480d8820028407007440d8040380300302141084005003d010030f1180c0c08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 359962086 1250 359960836 359960851
    0x90a02040506070c2610020d09051501090b06040e010e13201908060f2205010b0915010804030503040302160608040311010b01050412050102041a03090c01030209181e 73
    0x2e090a0802181c01440c408151301e1000340b03410350310080f81c0185c0c040f86060f0031b00301005d8016100d2007114040301c054100138102600714000c0f1100d1160740d420000c043c5050300e20b90f030030a00082511300d040c0441403140c1d01c517185194883c4001806a540403c0105e6084640307120003d611100d143c607210b0702d050713810742070115076841100350281c1c504004005080e00701038480d01400117480c00410580710b2800900240c4503e441000107454040d203000740e040020030160031100300300500d1500368004c0034008580c0344144100c400007000104c0010049482c003406075280c10042c0ca982d503081d035040c0c1028000701c1c150300559802e002d1502c03032a290030000340000d0b0f440d01060306090802a14080e00780c40d88101603410072084901998112085800b1502e00d4064040c0c00402c030304203140280981d4100d640d101105c0010b041200711480040d5016551080641d250207071381c040154101d10488024640003001700c0b0161002c0c00d03040b5001a4003586400c1c02c8082d8a0458000201a0700d00b1503604 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 359963336 1250 359962086 359962103
    0x607090506120c3105180402010804050a06060612050c040302030c101103030403410a0c080307021e0604030206060607020402070f06022505070b0f0c0703150b100e090a0204050607 79
    0xe42c2c0f032400c035104c0000307140030b440c512101c148500c04865200c80c0140080d05114141c008070301005800c10032040020b402c02c0040264a4a03000010310071444001288101410130022560030100282180c048075401801441d1210504c403d0000403144007940b0b03410310612042c48416084107100031441a031090351008070000f82c1d48090200c0b40c0ce80c00354140c1003074844440e03e414581c1e481c0c842821710f00d41c40c12182c41d031341e0705101116284882e1600405401d400b0050080040d00082c0e4181100048c4104612032308869982a41d00c3c0070480340640162310044c0400d000d800c251004184007030001d400989440d581d9200c01160f0301c81054110356007075000449100513030000390f03055040d032080038440014070201c0d01c800703035207081303c0c0190102008009803010640103400200c0350031403020b0068408080d07807411b08a004000e1500381d00701c646d04090044000380b9207246103691094135926150565640002030041c84200100444041135081101040d607680d03100150112501c1500c42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 359964586 1250 359963336 359963407
    0x80702151003061d03210f160e030309040e07030507150207270207030903060f061404050601021e03070203010c1119031b06020304120309030c0f1a09030c0607090506120c 75
    0x30b0321902d08020f00c0c2e100b00e41d00c0101806400d010001d0b01e010150020300c9e03e6020402100e0000341584100c010445e4454038240000d48a080045042011a80144151824140d44243e101503070a10a01840016000f07003070148130251a000c0804400403159084103050301820171706d002241d1000e032040d03002c540b1012041040211a003d00c0e400400200c1d01032010928110a0005851a045420b48100c1c0c950000408a920030400d140c0605212001410b01100c00c142e0a6200d0b40000420b80c0a5420200b0744030032140100080701407010603000a02d1460400098114002030860044007046009a081c18a1034020460310381e4042c060362005950707041c24a8140d050080c540175203400d0500f00b201e041c002ca508902c3c650785503500b1031034400309401c20f4503103214040030007003540c2018030308501800103d401c000050181240a0b100721340d91034880340c0083c0c4201d0501d102c0c1aa004004000e01041c070702c0c00b0034120340c02c46283c8161307504041c60105072009001a801d000e840c040300303104130b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 359965836 1250 359964586 359964637
    0x1701060602030c0c06160503040f1d01050108130606090519180c030b100306090807020906010309111002010b03070b090a0b091c020105090d03080702151003061d03 72
    0x9100000c0031036000451809680b010110389804c0e00b000da00c1c0c0308180101c0c0c206812a840c10501000590080640765256102c0020444624660080d4a180444402c0c0c8103010300c00e1010803410303110148c481144558603900100b600e507a1540d030480303400d500e400c80060200e1046c0901409a5204000ca02c41440d0810099040721092401d9102d16228140804d01040c4520100c40569070030040100c16a9520300100707002c4402648014412403815200606004c200405840014801c0310108450749030a801101901c4440402424421030098500120700d080039490101145031300020a107890108002800c0100c1a40000721200b030000b0500024640410881d02034418141210708000e424000309039156a078005e91440c84d2035120227002507a000c0c5043d00c80d6044020f298402c4c0c140c503450700800d2110705a070b002d00548500540c0038100072103888260b104030444001c40c0c52203446c5440d50405809078010340f02c00f206202c0b0b00990304220510080641e20940d00710400c0701d41c409103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 359967086 1250 359965836 359965841
    0x70b0411121605100c050d08061819020309070306050903070528060207020604031203060911120f040614010905041505010b09040c09090603150e06040206040603180803011701 77
    0x11507025076030800702c080d032a054429000c000c203407070f0256001c09545034251015100504030140141c00c5100d0009003800c0b642c1d00c0500140700395001d81e100440c2c1d071244031820503039800c103030f0354210030304080c010080301503c20740c1c081c56014200d0404c59190a42d26211003044400a807600866130300f00090440a004042000c2040200d03040314544081803c01e038850140e003440300f8020035064001403508251360301c00302a5005950031030040d1b80c940c5c10071100034004103500e08c1741518450903d1500240e14210758141c80380f08005194042555951807103d203802040144210b9151343da6040c540f0a6407a8504080d002e400030032400101c07401c01c3c1c20240700091103140c00c0459541884010300c4074800a0043c1e1381c45400564000c1615042420705403078150850300301407201c07803074a0f41c0001400101c00f0b00525a003e8080208406d4500c84000d03500d0b03510450f0080e4000740c04100802c621403003544911007540314a82c03154001074240e6104145a40b0aa2155508440341000c03070038004001e2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 359968336 1250 359967086 359967109
    0x2d110f0607020d03050d1e05040c080721052404031d0a050409031707030906050c07030804150209030a030903050c0315011a09100915050306090f040206070b0411 71
    0x44485a0804045038005207103d8001440142006000706481c030360303a003098008481c4100f01320007504404140b20461801408115001e4464101c001d900046a55000c9041d200b80e40d00500c0c07040212601c0c852440300c0161540d003c8481c3e1160301c8181030348038180500318907020805942d40c401c078106802c0c002c0149034100d186111060501d001510540e8410015004480060b03401080381c2d2407034141501c16208070b020351002c4c00101410025010f40c19881490240c2c800e100811076921410010005800f0300a0010b0119084501140115550000c0c803019a01c0003d005440d01e441c075808281044000d50088002c034540c05024010000c0900040c1d80711081500180f903048400c03580001000700c10f00c20031000d000481501c0800390301203c1103408100c0090940d0355a9800c2e001c0c010010001842410361a096881e041c030f03221841001101d0044000a100800c15180ca045030b90041d51702400803680f200003000308a0010b036000303101501c02c0340030f0141200660200340c24007029a4a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 359969586 1250 359968336 359968339
    0x140a0302041e0f050405040f06050c0406090b03010e04030525080316020102030405060a0c030603080c060106110a050d03050601260f010602011503060b0609060711010320072d110f 79
    0x8182e0280260f401c140303109401c80e042110301013101c0d2901e0130002946404181c0207040d00c0c6c1404208072400d02c0c0f010080c4101c44031a541d903943d0a9a0b42d41036074080c0030070302840783c4a4800001040110b0320801c040c20b822000c010005500400541d0304000090901070101c0d4880008001c01c800c641080900751510002400203600d90715141d60360320703220340b0000c00124a460340c446002404901c00d80c0315001540d40048416030b0388000074451a0385142c240701396000106801003d901c22403021400501e03041d4480c008214070103d604054010b07080003000c00d4100311b8012501003a1080c040400c0b008542c4425208445043c8903d4951004005811180c19a130610b40325000304105541400f0441e6086040001d103504802e001074003920501c01c0e001c0c0c1c441004034064052080000b000240b04109890801c4648992068110714000128072000b0401302800300b0cc003c07801850200b01c10702c200700b0310b8460606c01407a20f5085c0e4554dc940070307500004c0e8480b1014550500800410130090b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 359970836 1250 359969586 359969639
    0x9161203120513030c0510020c15090f1011120a02070203070e0705070b09100c1701050a0302060414012c180606030c0a142113030519140a030204 64
    0x1c049450301c40360003041c18010f0400c9011708100042c01400d000549145440d01d405640d541c20402c01c8a03601c42c89030800e0550005400080780c0034010001718051035410110162a480c2110210b00b8000c055852044806000401c0340f2083c090090401030303c521201030b001038603103941d801854600403141d001540070b90100340500c00d0498100b0289d6961a50020002d00155a070040407414905a00440d11039a400d0a0351905155003001140400d61444494500710f40e072b0311800c101080c00140301c040e4110000300414080703403603140003024002c00b0604011a441022030103500110358a02c0844940040410314884185010820381402450001801106081070400a1030030712010702080d90420000950058460280b100700c081000e0050000361144246070b48941c0c2080b00030341210300c0340000d0000482004408105e1a181c0c2c1c3c040c1e440b1424151020b074620344484141002206001c610601270f0144060799005281c0d8401564000d40c030b881c075005210b038074014008810a29441c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 359972086 1250 359970836 359970841
    0xd080603030409020901020307080d06051507021f0c021011100b060906030601021011031006050304030e01030e1203041a01150503040308041103010c080117031809091612031205 78
    0x190000282c90980d52196030040c4d07140b2035000140e10b10300c80c40030018130544021550150ba0441580400e08860301035440302d25004d00765010410f58455100001d620044503410301c40d040401c540100c035410158180308000d0b14290300050300038440540c103a40000c0e120354088154100074031401050034205401400408401d90000d4180d01580703400ca0701520010001800aa00c2001600102c91805501704600c01d8030f040400001d42c000c40329064048030440d00001c0c1d180c402d0301107034402d5403d81d40314078810f2550b03001180500003281d0510304e1441240c194500f80c02402c0000c50095200f403003c13401c00c0000070280e4510600503800b800d4003640012060f5030542d007080407641d205a051611581590f618900b2040c40000a050580c0641c6050200040700390480f0380c25050b194100740d5024011400b05109aa0344251242e00c0c0481003010100c00c0c460511005250b0464244001c2c2c0b0b15070000741810420040c100e41c020924a2846050b40081c5034000c1c00803600040645002c2c013561 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 359973336 1250 359972086 359972089
    0x1b021309021c031e050f04080a0c050a0b090907020f12121003021e01031806020315150f0702031516080105030a0b010618051507020a14100c0c050a030f050d0806 71
    0x43c418200c00b49003080001c104624140326004498032100c040406d15243e035102c2c224203550f010a034038200c41801c00d200012880c0c0c6010304d1448211503440d600c26183c035880c00d040c820003410282600003503225070b04c2c12803035400b018015400c9144503405c2071503e034020400100c1d0807003400740003d400c0200d503070700501c0580c99800e500300c00c43c0090b040c6061030039040c6004078003c01454804000e8071a00e00c1c28a030820046800035409103008864480f548202c507030400c202d400b050b00307800500c1c1c1810030039410f0813000e04000c0c140d9030340002d05403032010140c0c04614945103012a0244e0320240380084034125180c0003008240540025001011a190960380380205450f040c0240014800c0841d80314072040c2d240d03d5070901070500a0515084180003c0c0e200d07029070031102c012449440602004100e03458280003070b10f04454000c0c034098134044014030a13145214445026218805c80390008201511140303d0000154414800489411600c2c05c1103410400c01495650400200d803040c40282d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 359974586 1250 359973336 359973347
    0x10210818191208071a01032a0f14030307020a08010204051311090108091e0607020f15060609190303020312250f11060f090d05030709061b021309021c03 67
    0x182036000728455952003030b0b400c0081914481705180041d66840500100030008280c004807503d03a000c0031040da03880005420b0807944840f034041c1c001c0304800d80b801006001c07052240c600355240041c0649142c40008d80120720301c12060382016449a400040c1049075003409100c002c411082d03100c080164106103c510a81b0780310340490796040107898804980989414405003030480e600341583c11584101420203170310741c05c0494000c2c000d40a07508103011b0a40000c030b400d49089002da20f13002405d0b1b50350000c00c102d6801880071280c0291510f222805804a1140114090743c0690001c50b1500d640321440f60740d101000780802044001201e1008410300e03200d050700442c0d031070760900e8000040c4414045030355051411b00882a407154a041c00074501c2c080311070500801910007940d400e00000d48042d101440300303644120004a42e0f82080007034510030100c032810b240307000c00048244421500082e0800d940c1300c9200e90b1455650034501e04514125161044040c0901040c91450032652409483d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 359975836 1250 359974586 359974619
    0x10b0a12111003060e19061d0f090c100e10141c0b0a03060b090708071d0613030b07030e2d0a0b010b040602060108061021081819 57
    0x10540b00840c01d030300a010790011805002681020412403400800b1103180e0106840e0f00c4414502d05000440c1c02c0c09650120355a05c0343d400140078554581003100c980c0080c0051101105000300380035006213a54184007000314200a940d0681000b41200c01c00c843d0344603610f4503c00b840114000041d03522031000560301c0d0039603091842c04505c801b005031f2401a0840f00c044c5580400320f00702c04010000c6692107408a504182c5003403442c0c1d600c0b03060954089005540d05408124030078004000680c0c12001111407460240c00d0600f41803502d4410159140d094004a54a031042010031480316451b216001456503041c0092521a1a030f111201c140802040504070100b05500310340d1108504001003800c4a500c10444c140c0b940c2d440220010b650031030b009040042c020540000f405001c0000c00c0780c05075202d0b0010010040c600716022134450540107440c054502e01c54503540101d6102c0f00600192400d404000040032100010010030f107090040d00300450011100500c140c0c1e88400340b016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 359977086 1250 359975836 359975839
    0x809160618092c010b040e010e0606060901090515070818013207080408070608040515090c010c0201180e10060203031603091b08161212120e030309010b0a1211 70
    0x360b0f0305510107601d0240c816034000d9904141002082108000154069100d01003048203130361003600c4090404c800e620982804a00207226801e061096143c4165860f5164081a049074980b00c00d41c0e5440505400a40f00c001c0b950f000c101070b1802558100780841c100c0c01250031580280c1c1601d20898861100e118a90b4400000c08101c50307080003a00e40440c0c0c00350030298100c0d0749041c0c1e0350000030f16110b0115000c0b80d07940a084c0d07076454620100e080d075501410b4a0340103000b0b07941c4045c004540d1b00c2c035000d2080c0e042200100168420f0318030f04140001038a04400a242c061030141c00d072220600c0103030708c0142150710400400c00d214248488001b0301070031030314003c14403002c5c905010464611700e58103180d0541c2010000900183c00103076882c40d0035002030110f1366889ea81c00318401c120700d8000e00a4800002d25401d00ca410348212000310b041d032564640040d0740100c9050481ca0350308220340d4010366030740d5401044528a00004043c0044c4088041d0107001100c0340ea074502c48040515159 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 359978336 1250 359977086 359977151
    0x30a0629030606041805090c01080c04050f0d0629010906080109020d0939080c01030c0201060906080303010f090507020d180b030f1611030a080916061809 68
    0x340c1e80e0740d1103004407401031841710a10301c10003480c1d0354040014081030322a16818130900031402120350182e000c6510401c0b01c40c5090741072518107000e100304625018410f0340d12007405050180042d5061049020a01d04c414401509400c0e00150030441c124081c0d005050144180c4104106a40041e9550544281c100301584a50b00d032a1034030080c041c0360400400410254501110010800700da80f0789800c2000220458010310140440171500c050080c0400ba41121550300701c194066046826058001d20002800954a4044004940c0581c0040500780c0001004010070903600181e500a003801038801c000b01e0601d424065a120354030051603003481201201040e04c2148c84103207a000704110160140d81e8503001400303840000c3c0464201c107403503070680301d5681264421940d1014086898009516001c035000f070a58000c0001880522544218154030b08040c9a201800780100100c0d00c50300707481d14034800c05c15444d4010790841541145041d03a074041080100612201154002484 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 359979586 1250 359978336 359978341
    0x20f04050f03070305240a060b030408031812040501140909010e041a070801260705041104031502090a0e0903070201030203040501140c09040606260603100e03030a062903 75
    0x101e403d1002690010b0114080d02070030128503603000c2582d9006090702218112980e540c06800022100d59008002d00750710107100140015141c035000716003000034218105403007840450598030b4001222030001c03003850b011408105658200303480e00c4c145181c100460341001c844c440854443d030414030a4818003c0c4402c041401d2180c2d440510381c40c00b280f03251808051400c41000350240d80288111044503e40c0c085444803528001d40e000188030140d0050300301140782504100c05080c00f0344002e1005034041100100181040805004c0c4404202015031100911010032800250b10341c042d203217962401c0204201028040304880c00580d09080042e12a01c0300e082a5004081d24000403803a0b034442c200344075041202c8005864462070480d0700703104990302c620084a2003400110001098040e1207894040e50b10b03103c44884d03000c20054220344545141c444110203a490500a07120290000800e12403605407500a48010745000300800c07407090800098061030482384501c01a132510040007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 359980836 1250 359979586 359979589
    0x40501051c03050c10060512240601170f0402010305060a06091e0e0f161805060a1403150901120b07030c0306080f1606021218040906051e0a020f04050f 67
    0x5688604040034212070070030000c2500317800240a203004561103058500e51000d02408001030208aa11025039814035840e0f10344804c50102c0b0020b882c2c0b40c1841039080780254500c00f05034100d407140f5150105421903007000d000240032600080e01c514000d200b461001d10040303800c003104004603802842c5800f0704001e61440e0360f5203c403560f04000c1c480b202400c140484640d0b081001e83c001d03808a1002d452101c1072940a996421807099104003001c0d0b902400c000c43d1038180e001d00210303d500d0a103028003404000c1c810341a50f000315550559801c02150040950420720406030240007030407440c0b01c07003010584604141d070400038035603010107071604013040040b88640c11510003443c02104442c4e00107000700c1c040340c80d154601646040c0356901d05000805900c00590000221080029649444079502014840c849001c003450740154981110500040340b5100b5144a80004014103c0c161f2940d00caa125000000c4c140040042c01406102801e1b40c40b0300407142190011070b4400382681c403040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 359982086 1250 359980836 359980847
    0xa140103021b0a0615140d020310062624090a02032a0a0605030c0d1b031410030308161209050c09010807030b040602030a091506080c040501051c03 65
    0x70801c0600c0c00003400941403040001140c04485216541c103010025451101703817002c0c0074903c1004900120806a04a5420002190040c090010301a102511070404c5614285c48096000800342c032480c0d4406855000e4050501b01e031140a02c010748144d05544c8402a0a400e094202c04c1d80740c0200804100c48020410441c480c0719409001d8581c20140200360f8130103480502050480e80129130020707521854213842c15415210a030311400c0c21600c5290130303204d854000c00c84e0714200c0e995918014440e85c941c9c0c94000d001c1c9926a8020942081107010b40b00000c20140410240400c048000c2c4006600419510350005002528031712280847c40c3c119800b40c40d8071840c0c0c68161900b90014103100011403d07030780040341910545c00a983e03d1601941c1c45116100c09032101101d02d001c0b40015402e60000d503001614001d01003034045c41d07510f400c0d13810120007005501c050707990081048450000c0c024100c1c00e4000b10f504104640c506808661040036032134a40344074500d60090141014080c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 359983336 1250 359982086 359982097
    0x1107020301060b04090e03031303031107050a050705100e0d02060f07021c02190b0313032a030e03010b010c02040c020109080409050613090317100b120a05090c0a14010302 75
    0x6000b0b00082e0b544111541c404d500c00c0c0135540d001c1c0d080007800c0854080c0041145e00611403040035030b4441407207840440080c03151502d03c90310311504000c1040860020044014502d00034009410540d10300700c00c00c541e440f5042444000d0204440c0515026658080d261009903019649103507540541c0041402c14419000000d600c42101010002604094486010a03d101b540c041c0c64040030a41900c1c2c1e1105144640d00c0c80000030030024078461001e002c01c41510f07229003041d820748102c2c940068446040d0002c400e6804511080d01c01c00c3c50b0b03020600e000181e0301a0f000300607000172040020002c407a000720190107580ca6850f5035800c85e00c00d6111207403480d0803603c902c2c6c45a0b210103102006c0d00b0180c0300e0314458001e14100178000034640c4100400c0c543e15450303001c0e40c071110a40c070f4070034403000034060a81d2042c0c002e0000b4642984600404a011841311301039854500804048201d4102403d0782c0c04ca80c0c408454040941c4503481c0c05004e031036210000d03900360800d2500490191054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 359984586 1250 359983336 359983339
    0x206070e150a09050415030203060c0708040b03150a090c05090118080618010e0115090f0902190503011805030a05030c0d06030b160e0619031107110a1710110702 71
    0x34900410030341c045540010341d0000c0310148202d1a4201038546c450266000283d81a0080070104207000820001400254410041305040c1541c41d9408240c076002100c09030b041000b04600f0140c0f601d01282404050304070a0f800b0030085c2c0d040c0b0700003019030042d42450741c18080d0429600c1101c0d000d461014000b407091000700d4180380344c000f0b1a10003031408200011140d43c2010321080c910907042c02404640000600598402840e040312071020f003464900300b5204964073b4003a4005a1141e80420404075a0601007809640c0382105050841e1180304080e01c1440c4100404d200050f00030ac1140d801d4082864070700c1d22910303046c110f00c6040c404e5400c1d01004500c2c0040c004100014110903610462007401c0c0301b524130082d0b50302640d0180c540d0500b1903104504000100301841c25069100300304c4039038070340010b441180c0c0c040c0c0c13085a4070081003622503a40100d680800c500e80392800380c018021000c02060500300010005136218044195000c030252074082c4c1d4080d0b00100015100354940 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 359985836 1250 359984586 359984629
    0x1202010203090411071b051c0213050f060f0307240207170105070e010f0212031009060e0108121c05041e0b0117010e061f0e0109060509060d030206070e 67
    0x20391a07491107095103c4030044502d0b4100205814001d00865030a10031203101500380c0c2203042d01c122311301800008550301243d00422009010407906107620525102e4081c8486440c0c0508040c8100400501c2e00306105200f54429201408080410500d5411b1034400103c0e1100b4080c14481c140d0400380141c1100032240410070440d8105c100540000d0b015409a845081c0d08828240044800322038280040b005a8400242c980342d807645074005541c40601c0c0b0001903500c50b01c03000d0210903141641c2c020412501c1d0791005010045050000c1c1e9405992502e01526020088045007400d5500307401010b503030f0795280006428001c403014100018800000413082c2d52040f071a020b0b11826003030242105030780840c1030517041c10805200ea000c0e41c440010040c10140e845100740f004851014881103002400c1c0f0800107495003640008901a050080c000301e0f40c1402e11090100c45a1f004040510900c040540680400e4001c242250010030302d03d0f2818841400b000410000d03071045250704070040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 359987086 1250 359985836 359985851
    0x406020702130f05010504060506160303060503030f040810092003280309050102060108211303261207231803190309050907020703020307090c08091612020102030904 73
    0x30310b20782c000490142070000402281e62603406010449009006054003c1c3d030402c00c241754140c4001100303d91034440d240200744151100082419504501c601c034201510100d818006290184041c980a6890440c20003c00c5220f8440c0c41605808400c42610660710040505035031321309000f00020040740005da07024241a0718035a0714001224041500040c8130710340c0c003151543c07010601c036040300c1c0301c2e1000700001001e0308d45280182e10441c00a11248c40f080016001210311091000d00450003180400b094041c614003400c100458a003d04034105c1c81040407100120b040012960444a18500102d40d50b500d407041000d8000403c030110188000416a0356500c030010000380c0217000c00b502a04c1e00925410950340300c403c2030800080104900350410310150404800007540300c21584122032007240d481e00440e0401c0d0b481c1e00701150540d03e421441c07030165000329a050b00030051900410305032a04100e60107414805014611038010003031003040c29a8401c01c00d41e41d0080c0018000c0282c0f4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 359988336 1250 359987086 359987119
    0x3110304110306060130092916050f0c1005010b0a090b07020303090108091011181e04020d0204050a14011b0b011a2a0c04020a05120406020702 63
    0x1c1600154038400e1003944000b88443d4429224060000380108000c6a002007051161850f05c001e0450780e561140c2c0d034102400807500c14015625000035039230141404c840322022207803001d01c00828a400e02900c2084140c0e03000d41c810202c40440e2100b840c99a290b60000c0001424074240c960450085418400041001d018002c010410500a80c44442d006a518074401d41c0d5802440000b0307515400a0200d60180c0d4051907005078001001c40a5401d0b04020320800700450b6000030700c2030320a030300c0880c50113004840c0d000940b120300021201c25104480200d03000e40414031104251b40282d402144022080d1020f405445c06008002d00e140f800030780300c0785c05450401030500d10034005442c03008071034900712080c035a20140c19009144640c0603800d041c244910b00c0100140c2241040c0100004a54400c04000a050741180214550494110080074030b16041e1424000342c840c0740304100b02c8501c075800c801124503c19003210b44074420b5440341010402030041c40340180d00f012a0030b410b102038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 359989586 1250 359988336 359988353
    0x41e021b07050307060e0d030306150909110403260d0e0f15010308120601020a0c08160e16110f070b0301030308092d0703061503020a08150105060a03110304 69
    0x90120340084070381c52980d0b40d04041c0e486050b17128050100e51151030004282c1018804442081e000c1d00340400c0844d640c140208603075120301a884c0c005082048207100c01c9015028200b14000c900800a0406081d5280c80b500a01541421160119100700000b0014048400d4600f4010441410400c104c100f11105031030760108040c0c1807090103841d0003803406040d03200240e030507641c11401c105d00340102064404d407803000c05807815040d44150074480c0001190030f8008000b402100025201442a100c00070841c10301c0d9803c80c00c0d8042c034110030415a101081da4406a00f8850b180c036151121280d54450306200c9034810440f442d004030500802e0300140e20009504a038802d655081c2d45d40d1360075060948881c04400311703c050a030a10320a030b4101d4001024146042220780c25201000e0342c1c2c2c4e88001c2101c0c1e4103000320b144242d80e02c10030029450111040d2004000381c401030300c404088101c0c104d4200c032050103240d119020200c0c2c9400740c1e40c813a9101041440c0c456598965038142800d0501c2c6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 359990836 1250 359989586 359989627
    0x140f0103060f0c27030b0903070606050901080a0201180b040902070201030b0405040305032206020c07060906031118010e040507030509011406030c0603130506013c0e061c0b040b061806041e02 84
    0x2b442420048001014240f54050300c0c1228003810140140d201c0580c0110703a41910908102c01c031f04807202c1c021543c40320a40061005000000005a0343c0042d48005000e0b070310012802072040d4a80010000031070303040012668814a448003c2c0500401040000100c030180394026003c5407000c2400c002c960400100b200a072043c0380c4910603480d5a549086040d1603070fa01c403031020305505200410b03001c812041c2090b1034240c1414907800c0608958007180480d41c00303d48240000e0b403100e003400640d5100303100d02132341c524806c1d403620070500c1d2140200b590380d400030500038002c02c00040010b400b2001e8070200e0345110b41c084191380e550750b51000c0030811035003144c842030b101d198414400485040c01c440ca110400d480c82c0410050603103010240c1d9440c52004014a4025458031201c0c44c04c20211105d14290780d20604140741c09050500b401c61541200074031786402080400080d1031020380c0a0715441c1d000c00100c902090459100b4404041580c41a0710f01c0c078410700204003807018502800c079022 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 359992086 1250 359990836 359990843
    0x40b1f0306020706020304031e0f05030c0c0307060b0109090608031206190e0f0a050f060d03050412050102030f01080102040515030a18080a02100606120f140f0103060f0c27030b090307 81
    0x401141d81300300f0f5240503100000500d8081007684034550100c1d8052f401659006c0c0d40d60320300d582020250000c030350030351744070a800b110a59952a5680725641c0c00c110f0100140280c0c950800c000c41c1800b00e5a941d0f0300c2541d480c80600041440000d11076600c20302c0000c5d4121813004010201503031021030344e0300a901507542380c2403082044001044128a481624802e108425200c8401e8841409105543e08900e00907030070050100000715947c49043d41711303441035200710001a500c2c40c103041300011403581a0851aa070781d004100030403a0760344d071202c0c40c5034100102140c07a135641c8581d0039040c01014031603a101e4800790480020002d0064403005014900d081c0c1d001e80c0d04104000f001001250b20785d00400700810880c030365980803160954410019080d100d0000100c0003207010b0084107800b01110400400b0b15080014410400140111240d01c20b02c000e0074088c02c03c00d0070020b026400c01d001c0f11502a07200301c0c052203001d691012b0080007140c0200544802d41004402542c49500400083c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 359993336 1250 359992086 359992097
    0x11e02070c032112090f12140f0c010501150e091009090803010519050a0b07020102010905031801140313080711100206090c09040c03030507080c010c0509010e0603040b1f030602070602030403 84
    0x41310602403a0142c0300c51550300001140c4403405a6860baa2200d80001c007100c1000f005840c070840e100d09060052400020300c2e011f040d01e850721f41242c0d90035180143c002092814207541004541500903080100f2072008550000c41580d0f0b2040e03118140a0b0359000708007040c141001d407000e100b0160001d5041e544107030b501d030f00040d46034401c03819401c07980c1c403030141c0240c80d000c0200304860a030800361007424414800410491960f403541c900e1a00b0005291810088441c00321b0035540e000b00805000003000034400b811868085204807642d082a04d002c2e140c03500016204080100036402c4c0c040840e07008114610540018000030342c0d0f44001c44000c3c1661140c0140c61840d45003004206108580c00300200b100141140d4085840e50415070301100c40240501105400180a02500d001d0500c00d81e1560386400d9248001000a41d5012103030340903110400901c40412480850355a0021190501c0725401c4071041c1d0107090840154030242c08648049440d1042044c01d800441c019402990340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 359994586 1250 359993336 359993357
    0x1212010b0a050c1b0f0f210c0402070b070e010906020c091005030102030a060e061909110909090a0b0703020405090a09030e031603060b030708030706050709051f030e011e02070c0321 80
    0x5000e00d07500501b10499101d00c001d400581c0f00e01a19150114800d1400c054034045411000030a050340c021040458141859600b08441c603544a13040359503000e400d2901c100c2440c50004040d4581c50051750701e0303001b9101c840019901501031110b2200801025008541d41c1c075121118000800480c00380342003581210003c10711504c1c0c88902e02404000040d40c0340805460a100340c0000d1261292940c90200180981c6109070307a004442442807650030b001d0a8200b00610301010844002080c0406062050000b48600d40710400c60315403081c15480004ac10034180c6c2400e81d815000c1a20300d40e8103103d040c210307100042030552060100d03441b59505215075255441059124800350080c000c059101380b00c00c60100d186504040e80049050500f8034070320391140081000044a489900b007440c540c140d01403184c40c4d240c410785404802c07401c0208400688400103046540205840d4144190041014014412808c00d084019944880d5200c15054885c0d54200280700030342c05907012440300c810 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 359995836 1250 359994586 359994589
    0xc12030e0d23011a2707021c091202090603100507020f07050a0501020c090c090303040603020910090b0d1d07031112030403020604120302011b02010506031212010b0a050c1b0f 77
    0x1a00e6030801d442c50034955003440240902a0f002d45e06500401c03c68422005010100c00c0003020324014200c60340a0507494020201c200c4030b92070f2040442e41041000e0404100c2400c14854140703d10350304135160b494648407080000e00d0601c40c0207100c80524034140500003040e400046d03040002c5c0400c0282c501242d500c40030081c0403078030b512401c2d015130004404c00c8c449151458903541d00c44041e003100e070b0030800031a0120b032035a009508101e000c04d900049203205490f08100c0341c1506a00781c9464081c0a051408661160280b0100c80b4041501e0b104101030140c5e80f0030251911804000890340807580c0d03810012076100584d04118022020021440401c01c0003100712002e0340c0c3c003c1c2c08289802d10f4032030099401c035407a0001350115540e0307400665801c102c0c0924142110b5940c0d0011070113040c070b0010141480d20410451520660400101a864941024240c1100c2e01d45a1260b21030300038020a6410303205900001c003040c0101d140704100304e03120090030095600d0584951041201040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 359997086 1250 359995836 359995841
    0x5090c030c042304080403050304080d14031003030e0607051204090e0304230a0b0307090e0c1204060e010e0a06020301030303050609071220070c05090c03040c12030e0d2301 76
    0x208031501007100750f0110020f1500e022001c03038106100318501480c01d55641c80e40c034215000758205040b0358000030499408994071040000d2400d18400c02546941800882141455018440142405083c0000402c10f6469100740e690284e0030500782e4102e2800103041c0c102ca41d0050003001c84a07480d060121003a080000b068a05072030340200f1038090314500d03014034040a02101001c69002c445810045880a01207001d14010155a11807095150601c051014040001801d60180c24014010740c00c580030310203030702c0f40c01035002080003641041c000320140c09041d40c41580c00d024414490b41504205e015402541224020394040100f03440b958100020008181c0e110000621060b0507042d851440342e21054070318810500041440783c1d01180d5105a80104205a0320b00c980b0100c100404d041402145500c031464a1040b4610301e032030b68807008400e0030381c0070b03110f84000a0b6189a0825000d40b2080240610040000388080c901d41380943e00080d003072103045120103132000072039135509050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 359998336 1250 359997086 359997101
    0x3031608040330020c060610020c0a170c040603050a05010f0603020d14072c0f0417070f06020f0d140906010611120a030c0f0509030709050a0f05090c030c04 69
    0x43e503d100d0602107030710f10280681c010404509009254100c102400100c9100500d8815018000792034103252443c00c001450341c410200905540082c10742c1005d659403c0500400c0e5941038244030007030303449880524544184410a160010715003803011050060004d1840101c601c5500207121844e0b11215850540b1040c0c80001c2d084000b015a80c0009119400141203168041007100e1065542c3d000902c40705101c000e0f112000321040c50207007040c0103482c0c00c03180c1c0420940584040360405642d506013121101a030007007a0070700811070400b008911815110515003114055458620409400d0b5580c2d0040d818110000e10702004000185c101180291203105001b0141560360f281010030385420952801c8500c181c02000c520140c1d000e658800750000c10385c1603070005440160354001604003030b0f6082c100814000c0078004805950780025403401038440b21000410180c507608403203809442d090038146030701403c200400852080000c2c0ea800540f03c110100c1d03a660340c522080c0310481782c51 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 359999586 1250 359998336 359998343
    0x1214030a0f0804020111010c110f060f15130f1e09030e0f01020a0b0a1d072414030a090b010603021305090c070206041502010c09080d080a0b0a080303160804 69
    0x2a8103a900c11980501040b950190040c1800149040b5400da5242140c0158031030303070042005d00e041c10b4040c2c1c50800c60107042d440da28008107058284a00240d466460003400482415820b01405000d40c0b0740914001d48029401010700003600005007035805000b502030307040801d841d0b08508044901e0702e8024095000d4043c0c4802441500e200d080c4074044e00c001007042c0c107600c0388502c1500024401c25496200e40c02042c00002c1c4410041c0054420b034201c10044080c2e41e0114005104030002076001c00c1400b10780d0f280d902c4100700c50342420faa038602c40b101070b10980d20000c03040100041940d0082c01c9aa8400c401001540c0c2e00c0d19002e50803800b90300c2504180d004000c5007809182000d0f000240c000f06000d0105051414507400115607900030381000c0405803040c220502180e809016826030040c071402c16500d1a414800101d545510b03050308401000403140c0841c0300c103003030340e84620440003000d002c1201040c4c981a060752390b5401502c034012800112044503403014407030000345005a60 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 360000836 1250 359999586 359999597
    0x60602100912031d070b0d05010806060a1e05060d15080303330603191107170d0605060c151003020f060a030b0613030308060a0f050d15061214030a 65
    0x803018007103005040301c4602d041c052541404c02805641c00300f04190090100174502c594424140104c1e0b000e548041c0c1c01028964040404e010840d681e0803041c00507142140070034020b115259100c0c64020740c50b80c0c413980c0c0000e0002034400c2152034070f0300443e54000032000303c00a695566510035569120880300005800d0741306038410020581c0c4030300f0702c403811551800d0b488040070000c0026481c0c0d00c00daa411511111000441c45804401c0c00369030340700010300e51224200400c2c3c1d1503070003c040070906242855031002501c0307000c1e8401640044040d00c00504065145d4015108030765403013001400300d9025501d6080010800e2888004404c26644d001d400100742c0e102443c14000c25810403900324040c141c503030a141d01507407640b0015110300c00300b50384008c540c9444c41c1005407035800e0103400c440c0034400054091120391880c482d00001c0f51001d41b01e016520f560750070400080c0b0202e582031080b56040803400503102c0d111a451219523401500031151080300c2c0c2d00350301d0782e07841003150780800301e03c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 360002086 1250 360000836 360000863
    0xf02030a0e041b0314090307030c060b120f0106091401051c0c0b030c0415021902010e030a0f050d09050118050f04020d02130303020d0203120402090907180606021009 73
    0x2031103581c0100400c1c0e000790001c11240c02c2810070014070042003c81e100003d079030310140c0300d00c4214600f41c190400c10340350143d4684a1580c074003d103140901c1c000a81950340b1a140b00c030164031078170b030f10101e42240305c01503401c0740b4100342c8407502800680c030490f0581800d15a000010071401006107040b41d8000b0f1580c0352038440912014800c0d54403440030760380c00103501c90000d11110044011407050514465450f070b100d040130350451040d600c0740201d104540c01450750810040360385026800054090074840c01c4400801c0c0028680900080020f28031a14a40301508100000550141c1c80c469625070000b490303142d40044804100792100250072565085040000b400c001500d02d451080181c000347c0340c5007039400c1d14010b1b60700c100b00051110054403410414594140402c410840883c40035520302603012000b8092041e0203040640f14242002c003051925600300907850081c4107062001d10300c501c0c0c1404520090109105440c050300400107800040000c9125600c00580d01179034080905 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 360003336 1250 360002086 360002107
    0x6092006040509041e060603030822111c0302030702041b0f11030f0705030706050703020405031f0e2a01170a0209010c06060f090b0415050d150515030d0f0203 70
    0x108080c1094855a0300b01e400707214085e8075040c0300700b640c50040f0000329041c0e141d460024060b42008103424103076040c5840301781c04109800c0750180e28641113449030500101590000b001007070580100b01c81044900c0d440c204040d00400a862554002c641c01c100d080c050303c00340c203241c0c50108070100000c3c104c641369031011801800030b111145901802c0700d04100038440c3e50580e642c46404162515800070500e0403c0140a008840e03002e0441e14040d030501d0315240119a07644103411982e00512440020600c010b078455102e911020342140032101040b444029068603601d01c070031004448846102d4000d41035006020300f408201d90545240c1c01c40d91183c00c070310000d42100700d40306d04118440d078081d40860810b0003900c019046600e00034001d1890718420000300c401141d0b01d240030314100403450510306088001c03401140d109450745141c1c44028500301c10003540040c00d03e04e00da441d101c01d00040c81032680440841e40d809404481d1800701c1a0400c5e1510035084801d070b00181d10400c2100c194 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 360004586 1250 360003336 360003349
    0xf0f060923090c030d030204091802031b040f0515030d0201021c090f0c09050603010e01090503030106030c05040e040b04020f01020a0c170f010609020a03060608130201081e04060920060405 83
    0x4026020240c41e03c00c001c00c3c0000303042140742c034140c0340000c1d000302e000e00401220b441200c640c24511160303010403e07101c0d40425201c1c1c07803031007a80c0071001d42030584d100c4a0f1030b6031300041c0c000001a541004607281c03010503449071040c20f02d00c8030f00034842c10940c91111801403003150011500e00c2c0713482621103031005111000e072494801c00ca40d2103054164840014070081c91582c054021040041194503000c4e052608590040044103c6c80e810161014045400402101d044d00c4103480d022855606030401a2080e100310790000300a801034030100001c0c4040074a405000ea88225642000c81c1400d000490380c03801c0c406405040d4500c408010408520880e42010f02e1a10070000c2d1044001012041c500f107401c00e0340b01d840000d030006104415a0350500c104400b0300b00500306080182000100d014030382240d11700081c14050700c40086100c1a5098605440d018403a000044040c035151501102420121204480d900c03010403030341d070841040d41c11400d0700d00c1000d404941000e10f00b0041240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 360005836 1250 360004586 360004591
    0x10813150914010c020d0c02011d0d020a080d030f060506180f0409030206060f180f1b0c0a02040e0105060f040b0d0f0506010f06030b0d0809130f0f060923 68
    0x3215a24100c810015108400314410b101501c000050142484040603003080e11100071001001085101800142c0c1c000003085203015030741c04090140380a83c4042500d1040700c481c081d6100300e14800c002450740d40000c1d001c2000e0078942d0103000c24120703c40001c0988015000e034991241302841500c0d1460700000001c0032406004100c0c15242c0200c5011a08941416500307030f0060b08040200065401c140030b01c1c1d0741c0f00314180c0b80c0019200030003012901c85140039010148070306400000c117005402900054107611380c820711051360ac40690000755a40c001208003240075600300002130b089850107102e5a8415040900303084011003c0344200001804160141075005018408050101e003601c0c914080c0d40c2e10517001050a541000400c1c454510180d01c80801c1505001050711039803178101c20580040d600040a64454800a000508450f807040383c04025524086001d8988a415044504840c2e2000c5040001549444441e4260741c461445452050008120003c0d4440d80031302099 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 360007086 1250 360005836 360005873
    0x304050f190c0510300b0f18040503071502091002070f0909020a080712141c05030402060706050702161a070321050c07021206091e19051b010813 64
    0x417420ba104070104200041c4078a00b502400d2600baa00105031141c500c1004010101103c28a80000407800090b415009103408200740304e07011008541003040030000d0f03840c0c03541d0140c03000074005050a41c0310001d41120003281c0c4503110f03090340041254004036040302954102901d2010380c900700300c2c140b4003501e440711081382c2042c051940050031903000d00009019000c000d460303900040355030501c8580c071065000c0314030143c0c00501c004041e090080c0b003001c1c210708150405030b8692340d072400054068010030f05d01400035801d08041010640c1e011840300000c0c1005441a24090f4480114844201c011a00d02401480c1000780c100401c6c06400c030242d00e92021405090a14000ba08860690342d054501180540c8081202001c40c50841e045054001c1a01c008102c03502e800b061103599854502c8960241e031003204041c0c06400400c0c8030024088664071003a03541140d0602d410341d9a80c08a0080c0b2003403455060300ca030040d600c180c802500418031640c8030f5094542d641c4915903c40360001c14103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 360008336 1250 360007086 360007097
    0x70509060c010204120b070521060d1505040311030c03031503070b07050106051512180106080d1e0512071b0b250509101101060b0304050f190c0510 65
    0xe0310a001c00340003d201400750109261000002403a0940ca800700203048182440310920a0f0a0002482c02c2c242c3e980c280d00d280b030040c2540b5a40007290a40107201c0003d020100a00480803414240e40c0145005034800c0d6101c5021600d0584040c0c0c882c001d0510900403500204080b40d0b0f0644803910162203c01d004040e94201aa1031003000c440f540904811207071a5102c0c94200031500c3c1807030700304210300e11100d0a030f4a0980c80b480608603d80d0f0062007071440c202e2070002850b180009500c820003825070041280d0300003562100107008882d0000980525042c40c000e00560507100b00181c416a0b01d8450210a00b07440d003017811b540900240c64401e50003498040480017258242d0071040c0110011412400c00c01c3c0100400c0300030080180c000000e22204028107032894440901c90813a0b1034180c61b26203110601c0031012030141c000796000307503d401e00200c2488140310011400b84403c604000841e41c02e0302c5032480d080601c0c0448800a001c41805030020080c0342030000704515403005910f4031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 360009586 1250 360008336 360008347
    0x81f0b06040b04080f0c0f010905040c031b0207051f171305120d0b010309030203031504020405030102041e0806042102160609180207150b150c0d0e060a0807050906 72
    0x95450743e0010751041c65254000e031461500d80d4000d0001d21502070003902c0c4440c1c0c0300c0c44070001070300c03204641c0318440c09580d486045a035607031700c04e900564143c02082d00080100041240c02076468000380902c9128075400d54a10418420002114000500b10b443e0488a80442ca10381920110000d055961303216141e480800014800c0c40840c01290780c0c8007459480c1c4024024606c215003461a02078141171502c200100400c0d00002076942c8040400040b845a00c1618042406805a07501080e0558008100841e03064102868280c0c510a5800030200c00341c1d4a068480d80c80105841c0501a0107029034500b648449031801101c0004160045440d40540d40080c0c0e441170000d5030010340020b902c9142401407880048001d00d22214010003582062155210346404560584e86103503020307aa000a0010ba0320b030681c80800c140c25250843d62144249403c20b070b22a0003519400c0d000030000c036030400b01031a0072802c0c0c415040447d512442241d4610f0b07001e0fa619445400740c1540983e05221 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 360010836 1250 360009586 360009599
    0xd091e05100c081201060309030801080f1c03090203070f090b1c030f030216050c090a020a050412020f0904030815040903050a08060f1914040603200a210309081f0b0604 74
    0x1036139000380241d41c0d00041e4040705085c01000040180c1000c940c5c9d400000e0a04285103000454201d0320800d030340014110110840154010149404000d4040c080c039200060340102c0041154202c03886a00d050000100384410441c0641040c0e2444820800d459044008288201032045010b0708500f00180342c020803110890480f0300750711003200c09600a42070f041c01c50406040494000d803804105504151142d00040c01c40e00032800383c6415105e0010310a0305540d12099a086005c0740504a00e0b90f07401c09080052035040e04841500306014422100091800c25124540c00150036a171564101102900101d80c0304001400c031a500c95040c2844004a07500c089a40741059503d80327004164078548424400c0c00103003181464411880c0000400108002015400e40d00c0319103018041e20147d4900061200c1d00c40c1d80040069555015450101408a86849040728001d032112a102540d9041c2c1c15030313440c48095182140e0381281c54803500d0900d03640055001ba4001022075081c03540300d20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 360012086 1250 360010836 360010867
    0x1e030d020a120c150228020303060a14060706140a0b030a020901050405060f030d020102091206040b0403050d112a010b01121503020d050a0c06020f0a12050c0d091e05100c08 76
    0x9002c2180341c91030401001c006d00c1b82c403001190110b40095030452400b0b0380040c01e40340c403502c14040c001034032008082242d599031040324440c9501800402c90300c00d000700d036140841011260250300900d081a40c0303190346800280480c038541d006101d00040c2e820b280502c000f416006c0c0a140e04a461290a08450381d0300340408810040386d640010384aa2134441040f000c01c6003040c81e44456004041484041120352113900c2d0311a0309414450b0b41c9000d0340d40310a000309004400fa002000c00400c20740045030404071081080300060704584d038240b0800360014201c400807210240410320203408034013503c0d82a0441c41340c0c40315880b849110b00342d80380c021074001d020114007114290000c691003410020681102d601400351480188030b00000d198040f80e956100c2e003009413241026503010481c091003074048400b4041d080701661440c01071400d01800e0b03600c0e58014a00741c6482d51810304440d400890000084440c014048410b82e0b080a00940b4644094076003034982c032400308800c0c0c5070b010303403007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 360013336 1250 360012086 360012097
    0xf150314040b061e18060324240109090c0302040305070b19020a0b060105033111030c0105040b0a0c0c121e050d0f0207051e030d020a120c1502 63
    0x1075002c60b8452030114100310460309566284010711812000c1400d02d074840406080c4a49003004070011036417540c0d0700083c80c082c400380c80f0008454864141401400740c440c410360007071564402d2159015013084c00f4404000200130282e00041d96504200050241c1707800c451070480c41070034014640b540701d0715818280315554001d801c0701d1301c00188880017202c0c0c501304201c18043c1c520140044000503034465040c0c1c0e9015100310704000c3c0c0440811014007105030040d90505940d800043e0401c0181d10411411a9817023055541201081802c03440b4203000c00d41116440050b0742e860b240030b041c0a604a5542c10a41e40c440803c840042d1400005001081c0c8202a05203c0804603010b890752500024800240220104280c103100e42e2200285000540f01c0e0300b101d040c2801010143e0f680e40c00c0b40391050562040d94020034046d08100d080301c2c3da1504001c00710741501528465010700500ba6030791550030500400c3c440300810555003152060a440c042c01d4402c85075068820500c00714101660000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 360014586 1250 360013336 360013343
    0xf14070608010f060f120504020f041b020601061107030803190c0908010b030a030c020418060c0e090f01030b0c0307020f010609060e10150c020303130305070f080102040f15031404 79
    0x1d000600c2a01c24003c4040c0081c07141c3d2070503941e240d80301e103401448800c1c80200740200c541c03590302050840d0344d038255503c803604024004004810602010a506890000b80c0314098050b04002180c2c09210b81c2d4031441e80d03020b04c030080440f5455039561022981c4001c00d0001c05c8011030035800e8411145001e0400d41c83c205a543c02213603070800d00c80b5801c688410306068031a9009081d2032000039085075a080e100740e011600002c00c003001c22039001d281d00c82c02000038009850528244540c503000000d91407000b405840c000c00c02c0c1c1e03840d200c1c1a80c0801c00c2c0000ba00210801c030005001120080043d40c3c0244030303105446520410320700d182d007584c4007031304160f030600d450b12004d01801c1e500007600b40d071108581c0b80480d00320b4a880310a518040321102c0305010402201042425074504008556030725191001c03280506582c0c0c01c04689804032800350020014981c840081d00c14014000d403003d648481c2059418540742c02d509100c2040c001003658107043c0c4403e030784d0700c80c020603603101c0740314502 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 360015836 1250 360014586 360014597
    0xc0308030601083114070e1803040315200c0706080703090f030e0f06031617191e020307020c01030b0102030a08190209031c0f05090d0f140706 63
    0x400c1c0001402414004203031258a0031043c52a0b500d29001c8104448a0399408011090415450a20000d042408441c8000318425094000350505001500d14030949000b40c078440e001e00c00c3d2030000c0d03d0f48281c0c4009400c51004026043c01881d0550090b044500c1510001d801d00e29100030451180d000341320080800e8212900030400c064011945981c0040c0d186002c000d40c510664982c240c0920416024003040b0005100007441d8464400c408051040104065142e1a010a040c900104021216400035106c00301903c80d03080301d802e00c0c40c00390700690080d085003009142e07172500410600c4941000015150314400c105c42c9a8030055006a1060b030142102c80c407600000750640d0446041c0b68110741c001c010980005030b0001005402201f02c0d8481120364039a25442c0010340545419640d0500640e94981c1c6481c0c02252170840f16022a15000080d0b50840030a0751280158800b0f541c000003012000400990820005000c04d44500a20032814168829080c900782c0309801a02c04141d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 360017086 1250 360015836 360015841
    0x70e01150f14071b17010e0c0406050a090e2812051306080c0c03040b03070320040510120c1d0303030c0f1303080a030204180902061608070c030803 65
    0x107901c1241880307110602c2c1007200c003034011106803855074410309802500c5641c441d80c030b80070001e22440103400208200041009140c5000405600170203178544100740390310a021101d0311a04003802031504540008000034805803074248124050600b13035104031800e0107210416502e030602d40280c00180b50741c1031141080c1171500d192482400740781101800a2002c10700401d00080a11560b41c0305450041c07034982400d0305c40140d0f0701050300418140038164040030901052481a89000d540f14607260395040c001c013140c146004001d081501840512040108001c0c041070422200071448d54074645031440481da40c40070702c241190701c02e0b81184001802d0320500d41c0b140c882c20281d030000d450210050f514600340008501c00a102d000c000c0003081c90b011800401441004500070002c0d600b01e80120394590240b580100258441e014120745981c0411040b45d00c0d80b0248122113004c0e50183c0003503c1e0011031002826018010501141c0303610b01080240e000841140c0d468008601c210341d06034a03030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 360018336 1250 360017086 360017129
    0x130603020301050f040b070e1804060e0d030c0e040506130f0c0e01021b04050c130801330603020d061a04080f06070c290906091204031a09070e01 64
    0x100c0740a000d50301200524000c0c000801c9034051801d410145508009052100c2c400101e011102c1c9d143e003c075a09030003030042005201e0160072007000f0f00c81020588040d4600c1403030aa0440b13541000704d0380014914000003203981002c0d440a42c001d80001c0500200c00020258002901d1284605102c001e85803452000f42640014020001d6035090015016080c900c1c6500c0c80c03c1c2800b02c850500c5130361210013007000c500d9007004447d0242c0c07201c07000b0006207483c0c4a030607001e48200300428031000e502030300743d03441c0b0761845403c841a02c40c040b00740c490780361812404502942044103003580346a520b200004481543e402c1003080c4551800b160b40d1a03034500024030381044150ae9084031035400460400c52040e03440f004000149601440e01c2c10743c02156811103090450201d8881070070080704050081e198800610584100e0304842204d400b03480102000d07e407030045204c01004502000c074400c42c1000000f0042d41e11114003001c51b01407956070807400881c003000f83c2c03001d4407003207030f640000d09903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 360019586 1250 360018336 360018341
    0x13080c010e0115120209060904060e060f0403090e040b07080c040519030204050601110307030f02100c1e050408070e04050c0306040f0605100f0501050703020703050718050a06060527130603020301 86
    0x81132840402e040101d01ca0f00030416040004151901c2034a1900000b81000b440c0d612102c0c814408200300e454500e440000c040071990103440c00d40104054200009038940022a440d1182d036111000707842c01c0c0c07a03000c020f540c00c10010346000b00841e01488080764580b144034840c0f094115041038101d01500d1030050208541000e03041d80e04005804600d030511540c008222381c0115410700e440104421003910407030612008aa01040300c0341071405050074194058421410a100c215030301000203035420059482d48039510502c1c02940168800b0000740700c010719850790103406113042d00d07203545424000a0400c0c1e0201c90031101c2c001440c6506050100f14403405078800702c0741c9548206541003140d500c1c00051184982d03030420000003410700c02c2502c00d1041400865100b070488500c1901c5a0385100e09000c440b04a2952516040c001024a54a805038804403040e0342c44552410010024403048030540c140c0d8200754403040101c444903519000014600504540c80020319135042d407040609 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 360020836 1250 360019586 360019589
    0x30a1403073b0f0d032318010e0103090b01061b0803070809070f030c050d0303021b0105240d1b08070f0f080c010e21010e010902030c031513080c010e0115 68
    0xa00ea00f4900c0d07006915050440304065426050a18000704250390102200050350890358031020080340d621300c03a1002c0804052040401d0b05d9030300100a12400440440e600b030f00006d01568031440c0100700031801424500c220300c103a081035840504113600c0703040310743e441a84d01c0e0700003c11000405c0340101d010f020201c0a8070207000c480f40c4451031910381003038001450040074030950740801c444080501948c1101c0c00200e118058140b4014606240c60080078215041500720314505660031103141800c1030010001c60003400042d241e07829481d59441e40d0b4900700c46803001000118045084801000294010f001c1000014003071818a5000c4c98072003201e038022101a8013041e8290340c1aa0032222140d6519410365505030341e4200120814075107048011080d4107035103889001c004d42c41c0c2c190410154603009074202d40d02078500200b0705503100098502d4003281c4552402050b60703081c203504c0d400f117900d0150100d241080c6001010a00b10380c8000c9101d2500e0395604660196403020140e00d50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 360022086 1250 360020836 360020839
    0xe0c040317030108120d0e150402031e1507020f06040605070e0d03170403020c0a09050a0608210306040b12060406051012080702041b20030a1403073b 66
    0x5042d549813065195031440c2c0003003417a5410340041010034400170291701c46a40c4658550440d0f81c1001c016040540e030071802e690507030184c0a5083c86a10320440300c40c03486c1d10720381c0e050f0003040b0320213400641c5112084080c0c907490850082e0b0000c000d03100008c10403140500c7c0035440c009018200b103803003c1e103080201706c00240560483e1a40e400804d8128003211035020107600c1d1a0b1f80e175a80c0703150481c2001001d2658a078850701071000494510340c0341c2d000510808020100300103407504d5604099441100b0781e1040c41226070301c00c3d901100c0030200302440e0002d0300904003048480130000042c400b00d00c1c942e03e108441d0722050400c41404200c0c0521600720480c0c1e103043c02d90b0750030b00c0c07100c4108a240d9840078280c01400550340045440da54440696071146035200b0501c500c02180c0205441564012400d6102d00701505c0844010080121400411140c0f2403501a200340350500d10306801c01007060050140001c034086040c540c00018245550140085d0080c01c4c01c0c03801d04030756001c04000c545 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 360023336 1250 360022086 360022133
    0xc030607050d39110109050304060c0f0f0f11040501150c03021e0607090602010b0d030c02040b10050a0909090503030402150409090305070204060902030f0609060a0e0c0403 76
    0x455000800c4a003410304a04010030881003880c59282500b2442c81810000002105030f00d28883d110710010700145816512015000355503203c0509075464003001800540080000708215809812741d1b8124031b05c030300550078900b01e030358403002c82ea41e00c219000d54025403144071440400204007645d107034105044508100742d50400d2400c0c039005000c040d0070401e20a0501c1c0950606008218503120001032142c40850901044041a00d608040d00c171400131840c083c001041c00340c018042c2c1603120f00c0240c61103080c0801500d00b01d03041000550266042651402507a041b9120b038070025810462548650b0b5035215608001000149030382d01c000e83c4a8034004801c80021404030803a504140c044403c414280344041c00d4071480d220701e030300c481c2c4510b18015801c0c0030160072034080c01005000b00c3d13041200d20350320580b8070240d04c412a108107003400190001101031400c0181140c1020020300007040305900e07141e403904c4010701502c00684911010400b00200304401c0b619120300b102c0b51004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 360024586 1250 360023336 360023341
    0x1005010918050703060b06070c0909021c110427050c0f030d02070b0a1710062c0411040b2d09100305070e0a06080a0507090b0417010b04110c0c0306 65
    0x1e00c1d80f910740c1c5010040c1019120132084186984d9003058030240340d001100e4007840c41c0da4000c0f40c4010300c5400d0b012402080011809007040c001d4030510000d8541003030314101855507880070000201a103103840c4032509c0441400c4e001c04424080c2d1003040c03621401c005e00800d03142c0c5041107018032100600038425070000d594080b0a69001c6040012214101049030f1180c041c00c409039140c4649500548602420204004620102140b0102228017584403000d140007010b05042004100d0900700c6005002d842c2c1c50300140c00c195104a40e085d5071034043c6418540c4844260340182d1100c6c2c99144d900d2601c405260f011121500018041200c0d41e416920b0664810301203082b001c00600581c05140d52140000c0c0d0241c022400004108801000344440d1030715480c0c0545144016030b0075110580c41e040c00a603c6501440211099400820781141018078210028000b5084401500c056540710260741c249500c0f24052001c200c2c2d000c0040301d4803100c00d04103080c900445c6568591099010805 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 360025836 1250 360024586 360024593
    0x21905101a0609041107050d0504141801030308090a201206150d050f0a1203050f06030c10140a090503240c0304020103091a15032413051005010918 65
    0x807100001801d136400b0030319640310390f0351607030a000d642e0b00940b030750144403107000c08554044010070960755080c00a2075001040c030f0610488655010b00c514400c4010700042c004207028284bc20b9001080108a608a400c2540d441c0106050124902104004d01d01482140e02e0003110206a940d5994010402d600d060350a400b40310030714050085c0114030340d0103c0402e1020601640390040030401c2280c178400000c3c034110072014044d44030000040d01e0a404039500b038501c60b08413801200000d000300014040c1c03804010401c007408492a0920803001c0b40e40c20800141c1000d810345120a84940040c05c1c90081410304140f2403144509460642c05041c4c04034001008030203400500c0141c521340c480e9540c1c40142c004255801020300341141015104040c4282c540c10341c0d10518004180d9032000c0200e100f40340c0d40e02144003c02c420080191070100d01c168942a01c2503000c1410300840782d003641c560301c5060070501055124120141c8a60051240c0f04103800307802001c8039525200e00b02500180c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 360027086 1250 360025836 360025849
    0xa06021c021b012106060f090e04020109090c11071502010c02370203060f1f03031b0f0c030503030103110a0b1b07050a0b0310050405090d0f021905101a 67
    0x70141414040c0809555060f180f41c1340000020000a0f281085403a482e00b20103005c00c036000d0149400901047d00c0400d00480c1c16400310701450b41030716001c580d10309210000c805020500700f86d004000790000079444c0303008100290402860069800407a14204500090079609000c440f50159030220903580c200001c10b10943c141ca04611251045660417110090f100c2203103c01c005c0c0d40340c4500001d101c19889000702190045c1e15042c20310001e002918414a00b0040030722001e0b01003104e00d41001d58421740c414041403481d01c01c1080e8140c4a010b0b40d074146040f0120b070030644640d0700200c014003c02008425482c0c00500480c0d60010301483d01000d0f070318500c01d620a003269210700c0804060300031800c006203005400000c0020a10680b50301040c03900d80c00864581b0541c404801c0000340605051040500882a04018100703800d41610161a18010f0810702d80440c4500031070604113400b80c604007405a485100a0700c40003914002c8034050340e401d10f610083c04506403a5001255a600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 360028336 1250 360027086 360027133
    0x90e0603061014010203190e1809030403170c010608030c0607020615060c01060e0a1e0204050a15091a070209070215011404180c1806030c030b060f0a06021c02 70
    0x200c040f0203000c1d640000407030440c06a4101e00c4488007260110000441d04003044c103401042c2910210449074151904002440781550084c100b50410401031021444c00d005507402d40403100c0c003403031400441020b010308586096000700210381021a40c1020500c0c148a415004a41407000300460300b08a8804642440d4a001c002d01ca40c400042d2040060300130342201c4010510700e80406c90a02c6c1481a0030003500d0745007148180d407041030042070080c0c0911720079542550000340c42a5442424000c9050b0420400002001401019240090101d205c00e03036800e200c00811041c640ca40c0340710310622002c1c0e14003078020000d41d00842e00384281d107076a03041141d0441c1c540d40c19410101d100d400204005007601c140c84a0041c2654847c0801c1c4021280018200d0714400146040360400c0e48104003100c82e6408010f000b8400c5801c01c10120b400c1c3e0100a400038402041c59074080340040c0006d161600b00c1d448603026030080d00110040070700d00c00b00a102690140007a210640360300d01141d500c88201c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 360029586 1250 360028336 360028349
    0x10623040608090a05011a0a0902120c0922060306060b0a140d14011203080601180b030703020d141816121703040b06040501050a08300406090e06030610 67
    0x710070001c0e84425003040000030150f0000000c01c80007e820380640405041981c869000b00c510314800902c5042610848055200030a88005907841d951000c0c51544c5c445100103038000908444c2c11922440c044402500f0051180002219495486c0c81010385600f42e1005441c07070710070300003001481c0d00040d081c2948441c0e004890f41e039180c6030039001c0007810802c201c424050505800410340c01204103c81d43c03994025221000256650300046135100e03d0803060701c00301032150900700070701c012103030165030020482c0c1005820010343c0403154040b00e071154495900c1841c0c1c00180507102404803428841c18512101401d4a00e1094208000c054124410442c1c05c903d20340d2041c0500c644881e2101c17822140380c410559070f00782401c25038103135001918014800c41c90880005100d291855040b4110381440020b08a546030304014114011003030100d8001c1c0342d00f104058001d00c0d0054004001034442d03526400c4030141401da0000c60301c04021700380e0340250721000a000202c0c1040202000f120385 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 360030836 1250 360029586 360029597
    0xa0e03030a0b040b060f030628030b060307211202010609020a03020a0306080d140d110a020313050a030b0708130c0f0801060b0408030910030b040f061e06050301060302090301110c03030106230406 86
    0x440d54036103441c2270780c10b07010410510782c4081c0881000b001e040128003450040701101d010030340350b0209800151500d64800302392035a015481c4001540c03004101800c0220340000101c0c0c5640f0b02d402010f80e44041c8144002a50000302d25080e0741e0948580d41c0030b044800e0041240300c10303c20000e081a0629152500c0e180c5010401c19251202904114846014203021545170004104060341d25009041842c500446080c1c0216041c04c11000c1030040303a412036102242c0d6141d00e10150b610034800340c035071064508450f132080081a450040c1c10010a810308603401100c0c50101203608440440c0c200e140d0005040104008001002040d502504400c807010b041c0700807407481c03c0d0b005006011101c3e401504111086904d01c2c00f0394410000c5616851040c10103491350346080d40c218030240200d00104600340700601c0042d100703a0103046d090001a00004613a81a007214410780d4204200030100c5600000040c00f03003e9004820b0200356082240241c000400d00b580300407140114003c0008002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 360032086 1250 360030836 360030859
    0x90c01050d0e0106030b10080105130f03030902030f0d3018140a02120a03080109240306050105100c0807030825020705030c030a03080105090a0e03030a0b040b060f0306 74
    0x40c0558802e0242c01e151074000c1000303555915290b015804104c0e402c4425080400d0009165401070142500c24920070a58086040c000e0f90b9205440c1c1c480482a0205075585216400507201004000c04465020008014001c480c501c0104a500200803041e90901085188281c0040d07400000030701c0b07849407001080c2c06600c3d03110034640c2d8401d22405406102032000e007000d08080400c2103080280241c1c0c1324505010305807d8280c0e10008400e000f400a1a604010480745400c1d80c0300030090012942940310038105440d00c1d1802c000182c0080e03807544d82d1040100702c14036200411a00078460b41c01e12140c10421620340e4a07440c0150000038040c0701c0800c0c0002c0048a96104540240c0104191050100321214000317690348070501070740e0302a10070403402c00344510380094458a0396a241d56441e42d603030f00304802e00c2036441010380040c4200340c5405070580c3c045014006180318801d10710f4000f81510308ae104020503106c581032107030301440040106902c2c80507048200d0398000d4007a9900441403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 360033336 1250 360032086 360032107
    0x40c0e0d020409053901030501030b060909010216033f02090a150f0807031506200a0b090606060a0f0c020a0510030212010806151002030922050f090c0105 68
    0x2100c0d16030003071683c001d110803401c2240001001178004407103112004685600c100041d030840f0b0081c00050040740314400004c015181c0b000305542d002000c00b0016003841e01103045485c1d040b000e107038101c020902054042c1801ca8000d40559040030380c0b400940c0041d10020411608000c902030101907082d0005526841615004103210090880800c42d46c1d403505448002009001c40c0340001d0700044245002c035400350312074003c50700d8541102c295604075a107407000546481c169011100035000000c0b100290441080c0900101a80204038240c0316103459014281041c2005001130300c902c005000d030700c002d5580b1803903581e106485400d01d05d20314007190000800c581501d601003a4401c04120101007415810b4002d00a001001b000b09002d40e41c85000b4162134003802c443c90314050004d074510200c145000d4030100105501d13401643e1911003c4804034401c0d011021030080030000700c00408000d0b50700d51040f507510205040622500c0d00304014080e454400030040c1c6410847d002c24280c840 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 360034586 1250 360033336 360033343
    0x30905030307050c060f010315020c0703080d140108012304021309061b110c0411070602030405071401050a0905100302040816030521070611120411040c0e0d02040905 73
    0x458100045903140d00e00300400810540c001d4070804418014400820405201040e19606907030303006140340c90100f50028000000d40004888c000188504000000030442c880000c1000d00d9580b032021507a003580400600043c20180d1041c4226131420810070022055070000100c4040b1280340c00a0790b0b1101d00004100701040300c050805180342510510410089a000400070103d040018070310b6011404282c07441080c04e034001926030001c4990f44510f141603400340d0005400d038201542020419203c170701c01c80c0c10845048a196004d01014000380c5004030516400039000d10b070403071030407106840041182840380701d940c0c0908111700031a054036000707030152400b0308200d40c100d401141c0c00c074580d82100303142c0e807206942c5401007920031442500d03551111044200c2c0b000040340b40007030039aa03250080c501d840c64101142010301c4482c201e21141d2a6450040c1c0c06a602c41d8020303c514030401044600c1e45a40310144a4100890802a180e0045011207190122400200000f40d414150308 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 360035836 1250 360034586 360034601
    0x12040206040b1207030509030703080f06031c03020c1b0609010305281a010f08010b0702030a20040b03062802090d0b0406060b0a0503180109050d2c180703 68
    0x1880c003000f0985061000010001c039100c0c003002d5405001c50344800420584a100d103041c081c00080f07440000a40d000c403125003a503000040602140c43c40365031140f04109542440c9031105c0080c0e00040c110281850030400900c031006d0380e0040c52040140c04002891900c20b85510f1414103480300d0010304099003200e1070b601c40e0000003000301c0380c296007240300703800410700c3d00402203c10000f04003146403544501c0426805103515210b9031a140d08206480c2d0058000304003c9925225480749500010070a0113220040c08441e0a50000c1103142c108010986440140d014001d80c00036080000348da50684165402d88541d4004442660002c0c0181d000b074412003024940110105103e8400c0080c021840c500c181d020300b02c10802d503600c45a0450f6248620410345001030000c0c80401d095500c5240d22106402c440c5d0700000c1da03541c80381c4d1020309080d184201080414814015400c0008405001c50a004018000010a400e800d800035070780140c011140744402c050309000800841c080ea10862 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 360037086 1250 360035836 360035849
    0x90108071202041d0f07081803190915020f07120f0203061006020f0a050a111807120605030f07031b0e09010902010f0c050d050d02040b070c060314010b1204020604 72
    0x1035455407a51000c1201300a242c0e03841c540c0d40d01550005100b8003500e4a007a008003c1c0b40d1303420600d905d9440d03490304605042c014688090200b005515565040701c40391110b0f03058507071034110140f417805d0340020174050702214a6081d904140d9070021000004610442981d491000ca40c401c6204e501708603600300b50b50800207405119440038003501c007002c2d200c0324044a042d503003140c0607004c102c040d0545804900300028515071194800c040050100002e41003411805041c119205401c006012031180f4140e84d4800412400c280c0c0c0d0750004564007500000e4042600180402200e160b0590f5031881c10740f00141c04e08000c071744551491410301100c1c01c02000054442c1100e400e0403031406000786a1428100c2c0031426007805a1200b502400000c40403a130444043d203240134041c0002e6586512604114030025400c20021864150391000f810060b401000714260303046c1807800c05401c82d502d03d484902d01c26841401040f03000002000c55081e6000400003420680342c620120b050f5003d56000030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 360038336 1250 360037086 360037091
    0x3020c16030803100609030b0412140d06030b010501050a02030d0e0111040305250506070b04110307030f1a010509010317120a090203011a0f0603090a02120601080606150901080712 79
    0x30500035550080d60044c00d6000e907056006a5491086d80d4540051100800c0a284500000d01081200390002c1d000c42d214141191281e0000c1d007644495030102007018030842d640c4c0000d03c2401000210180580b03801c2c00c1103403428501e160040d40d07a0140c8550014202d86072848030402442c01e41000c0c8103400100c40164850b9100c1c64030759280c1c2e803540b050300720700d002c203d40501c1031001744600402101d1000c0c00151800c1c10b0741e01c80c1003030000c000b00b040d1226503010f104903150392010850f11000714082e07244001004520710b020071160710301030f080c85407010603070300140505d684241c0c0380c9045030351240e0340740d2046291001880c240d0094100a044600e8540304014010560740c00018180c2d00c200c000b0400c8640c040c01d07054000846c00141d031341100c3e0b4180511264100f00c0000d5802c03442200403101c06c40300c940d00140c00041da6001068031900000b0040251034420400603400c40400c03101e0301c0040b000c0f0300780800603005400b801810041400040b4641d680222409060021107201c02d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 360039586 1250 360038336 360038339
    0x90a092109170c09040b070806030c011202031b16020f030a0507060503040f150204061205070801062703061d01090b06151306091505120c030621070e150d0303020c16 73
    0x88200420207c440c1008604a100010464035012441c283c502c1b00503190f1900808040c40e0480003908014840304400d6203420380500903518010141504101c0320000016000c1184140500440009040ca002e60f014000c03034400580e02041e03174ac090310003502d0907640b250740394104014070400e00d8034094841c5c0020801285031214039002441998001c0d10340c000d485809010300e0084031400c84071000001c1000d00148140740c810080494030a0120290700c46503001c000c0c02d2001010540c2c02107038034640c4c41d28005541d0011100c030300c804045050080160800316192913810f2000100700b0340c440e40700002c2c0907080340e0024080d0f0744c2c07000c280f06020300300720f45070031000e805000e850040d48547c900d18001740800305d214104664154540307840300b00954481e016802600d400c00b8111a40c40b8003540741151880703070100030611440c000000102000c5251107403540b01b099015014103a80701d0040714419098503001071030700c00140d0600c3c00694501c000c800c0d550819010b203d600095041c1c0d00070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 360040836 1250 360039586 360039593
    0x211902030741120c070e010e04020a0b07030516290f0c09011b050102160b0109050a05060d030c0c0b07061b031b0c03020c090a092109170c0904 63
    0xa54504401c041ca08690b401090200d101c028081061020071154020340482d42280d02d200090034445502104440c1e000b601c0c0d05d11400003000903000300490003000d00c108400d40c40d001e0110801402c0c4055182d00d000c1180d10b005140344500c108c4041c01800c602180801c109801850319001e44501440e15480302c0c2c420004a1001800d6a142c0c4800c0d11940100d00c40e9404041280d00400701615030b50943c450360320002d12180300c80d9105172140d541c01e10200003003011314048000340358803d4100710001d6040c9010503088401c007505030107810303140004004103525810118140560107040500d81c4d03e200386001c88040c0d4039900704a02100002c0707001d904202046e041296850a200a4408142c91b00b4004074111030804c500c03100e11008500001b00c215018904140d044d501078419609421a0840070030708290b02030300c41109041d500d04100043c4514802440454880c000204054840d84900103100300b40c40e00071361714500041010310b07900c41030030003440e4807004015040314400c0c83d0904 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 360042086 1250 360040836 360040883
    0x40b0d0207061a010c240606321b010e01020c03180904110603190504151a0108010513140403030e07060e0a090f2003092119020307 58
    0x90101e840310f041510000c0580342c5440d414940140c103139102034804c030b0750f40c46403020030a40700b020307100301d80240b805100b803800c03e8051207014028644035007150080c1d0740c5a0207200c0102c9040f04541e402e02000010050b8802003c840c002605048075004c0c920410030300078010300001400c0c501e42d620001d6126000c2901002404400d440d10001034103405042d8180f020a070b0b021540203086260407042721685103880341c081c5400044607404a40c04075580c1800c0c004844050328107840b9001501010003a0340c5150051800c00c000b4005494440388403400060400031041c06031354450110000c0e00c1d071920000b6071008a40c80450310940c2034504007810060000d101490300e902c500c3c0612b0b00e0100f03000780119800c0d041404040c04a9080030320341400d010003404030081d0040d400c0e46500327541c400c0c00703419944d00ca4a5031401103182e5480c20501562440c00c81c683e810700c0e403d021032050b2086405801826030b013031074100d241e00d2429008060404c0b4214810500000d0071151328800400c2c1407910315 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 360043336 1250 360042086 360042097
    0x304061b031d0303060303040303081f12061109010c03030b0103021606021b0a0312050403110609071e0b09040506040b1c02030d2c03100c050d0c05040305120708040b0d02 75
    0x42c0012500d811100c0034140e12880102d46a5030150f0041000b0030019105a8009500c0140e60403c0440304c40180031000e501c00103070b440b500100389184032110a0000e28428a92540d6000134040e1600c0122400a03142c081201409002d042d92080d40f0b00c0e159000e501150750050000314254003030489031404400a4100350281042803248480c40c12040c070380014244502034141d1103030083e01081d0043c3c14090031001f0000c40400c843e802148801f0102080241d00400000d4098502c090a14419819400007414007080ca04203d10b420485100000125404084103540101e6a82c1c3c404010070701070305508003000d40090843c403510161032081501203081c94070840641b0303030031400848202c80c8120b0100141c1c0151444a9076074144140a14442000410140a03540c416403841f4a001c02c482420f0360001c082a800a15803010740010311400407222740b00c6c00d00074146402c58032182d54402c49840d034680415030000c0c0c00c90500c107502054900030044210150313075400300c81c0c0c03001001e504074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 360044586 1250 360043336 360043361
    0x10815060d0c0c05120906250210021f0507141b120a080a151202040b1228210311070f020910081b0f120a0203060901050f0c0304061b03 60
    0x82d4004045e051180c1021111120030080402d81441660503003070103041c0c2c452012503240700c01c40031040c1c01070310303001841d541580302c540282890b96140241d030044984080d551864103443e00c020480420380044502c1d060030281e420b20340d00c0d0f6040c0c443c000c228035080d00c03400303840f841783c0001d60401d1640700740100400301407940c41d08034584a0365007207010f40c0d900710b0105800c0002e03114240442c40c000e0403070a4040740000d001140210b101e0002c42c4c40740c0190b800380001a042031011403ca00005c1c0c5024200000350b0300000410403040e260880c5001c58030002c5005400682c1e59804480c0c0f2030b4201a60130650f6021281d560410b510380314400000054049001748581400640d03411042d50305402140e4458000d030000340d1820301204100c0114000b115404032002c0c26401d0b280e1074881c02480d00800450042010401034010146055002040d00c41039a042000f0000880c0032007041303c0d0844446000c01c1d4880d00d80c2d14140000c4c3c08030303003c00070380410400c081114035903250300280c002d00c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 360045836 1250 360044586 360044593
    0xa0b0103021f050304060e1606090f1703030a0b1809070609090506031015090f0f05010e13030e1c1a0703060f0e07090b0a05090f090105010815060d0c0c05 68
    0x40024180810700380c0b21180c6004914140005004145103820210014680d081a201c0c0810110f80320381d8508081c0e00600002400c01e2800c2c0319080241c402c0e000580328070301900d5400c42e245d0101c650350380b20091440030403070303100d00124095440385c880a14000141038407400c0c1038a001490560b07070310003c0c8555400107504d1030001580102034815540202405005070403140c2c0001642070282c188d010714035141c00c1040700001340e800b03202d00c558902d0240c0c030030010035010400090700042d00c4040e0050000b0007201c00c2800500c0c011484034100306581801c0000d40c4001e44000a54200c1c0e041100e41d030000501d40d5050108452a140308483d0b45402c02d4881c0d02e51141041101200d4003030160b0b55400d02c00a009109000d40007450f5913102070f0340e00e03000038030903100d400c07058168100ad04881c0104002051641061620b2030000f101441c094030080c90540c5440c00003030004070060250b544001b150095004140c40d05001c44c2c13400c000d03040d800e2041050201d07000f080d070150800180d40c00d00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 360047086 1250 360045836 360045859
    0x40216050f03130f180c050f0703020a02093108040302060a0c0506180706051c021201060201060608040b0402300d14030f07050d06050a030803040219180c09080a0b010302 75
    0x10b200d0a50030064400c0c1081d1034171905825001000180350400a15061010500c881000e40c1e02540080000c2d6100f580a400c3c41042841801aa10409000c2d036a491b542d10040131482400c1900c0922040c0c452240071017051210700b0325032040e101c1d0744c002a411810004400c00300710340001040b6200c6126808071546a50307000da008551404c0803000039003503084213004100c84c5220348007915250700d0062a400016441c0744035201240e01c03410360b240b494058640100511502031080303800900c45414110014a8503a40e008908040144002d01c1202d9005d92003039049070000706581c88013140c1c104e040c46050011a8607030707241281a046400600d0020107a0b2038502c0207c2964040c205502c0004507030340f604102512550882c0166804242d50345400060554400708410000c50255010030340d40c1c06d260051010b02c3e803450100364002042244100041c580c8408951074150941c400010707540b616090850f15655564810f882030310402a034541803140030003049040364030890380c051502 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 360048336 1250 360047086 360047099
    0x212130806070314100506090d1403030112150e07060503041e08031b0c19020303071a07030e0307021f120e0d02250501080601030f020a02010506010909060b030105040216050f0313 79
    0xa412409096004801030103208c03010705080003d660054411000700c07580000c0040c01a00e180c0090340b01c00d14489003c4003120900110300003240c00c0501581003401001040410507542d49014840da80400c0b03c000700203801e0140b100424980d184101d0440344041c601803d201400d80c205403590382c5541400483c5100410b89442124200440744000e00045092401d010070030040d0031701d043e40c15020400c03078440080c034803040072209111192265122810941c2000342200d00001c1d248195074000c200410242c0c0d20f03a5121071040c0702d2441419110104004210b075010403105402483d281000040f84001d04e01003280310702450316600b100c1c02210620304010701c044040e041803001005080e420301107540318107091944910181400308184080041e5403040781e100744c03c14801030750f461091001c07545c1d11600c18001802080350134411541001e050500c54801803107124801c95000500e03110020358201c1e00400c658100003524100c49885000396225400303030603e015490303459000460304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 360049586 1250 360048336 360048361
    0xa0309030309050d110f01050403050a0308070e0906180919030207051c0803151c2001030c0e0d020f0301110d1b090b0c0f06100609150212130806070314 67
    0x103541e00172812201c1a000700c0700340650804902c005074100b220412000c00030440c00c102e52052079110f60ba810a9030b01e030917003000703180344224040c03944211080c0c4144440e0356108003100c1025140354801c00019107801c2503203850034048140c1c40d40e030885000350500c00c2c5a000724007042211301c152106000c0d14010f5121021140c1030150051249109001040005102c020645040c08002d42945840303040400d91036486160850b08441a290b0005469844105250b0070342600b0400e007424004150413090250045c00f210654501912074007441005558034201d06280100d0003900800c14000f07405011149540b000c1e5003c0610b60900c0d0354403000b61204d41d0401c0c00c1012a903103400c443c50818a05200d154008103801c035083c4542e090500911206000c881e01402802c1070a50040d481c001018000c0d00c80c582c04140300601c026145083c8980108401d0080000c4400541c2e076211040d401180d011055008061180308410070458034a030550700000c1c80c110825201030309540c070f07261403002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 360050836 1250 360049586 360049609
    0x3080a020403021f020316080406170606180a0302100906260606070317070905010201111611031e01090c080a1101030f09020d05012f030c0a030e0a030903030905 71
    0x104502c80e82414001300c0707140c084149000300c1a105a9203030016104004015421520054a02d994006410000980c1105100c410100100c0c032440c4a860118002080c078050301660501d000040304280c43d080d41c03500154030241d42d0080928080958202e002400e02d01a1701030791012801e42034200c0c0300c4020303610480603014107029101903165542c2d0140304091308000002c03000d200c0c80d203a02c0d000c40076003050f015126000507690340c900c061406000a0954000080502800408100001c400581500c0741d0740c015030801119040210310201003031501c0030752144a1a082481c01806012030010f40000b50b82074043d880100c100390311000c4807601c590318084000c20000346040c400140c5c0d406600440503e600c0040009040d000d1070700402d004902e00c120495883c3d40d1000c1504000c41e03261a00a007000b00c00302011130420491195075101d100140124410410104580807424880e422800c80d210020083d20a9000585806032044540307000c100c0200366011008038841c242a1916003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 360052086 1250 360050836 360050839
    0xf0c200c04020c03040608131212060909150507110709180b0109051b0c06060111160806060406080106062a020409080304021806030706030905160b041502070501080f060321040303080a02040302 85
    0x2404032001041e2558413094610101803511510002a6070303a040c030644c2c034628000c515007032143b2908900c0504540000f840c03441800f20210305d00507410000200c3c003094074803408000564102403002d0041c1c1c6c80c0d04030002040d904030350001288800e540c1c2c03c40c502900c29005154040e002d0140c669143e8001c1d98584210b603800480000d443d503108d1f55840d414801d2107802e403510094640c8403591081c0040d04182181c0d0b000703500340111400d16200e1400240304130002000050b08200f8000c00d2801c4540d0103d0910002c08000107c408d0000d0402e01e200d03078010002c008a5030189445549a00201c4041c0d209114a014100d01c8071301d50b031101481081d005020708072071824814140d000b0a440501915030340f15003e10315040640c1003017020041c00c0d6441100c0d0710341d450300140f0076480b141540e1000c11504140f9007004140d801c24459900002e41108686003551a00007003440c200b03e50001c1c1494070440d07100400b42d4400000200107690183c1d0f40e47d0803d640300c0f44800180c3c416440000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 360053336 1250 360052086 360052103
    0xf0105150904031e0306050102190809150c0a1202010b0a03030e060c01020f040806060a0f0302090417070c0303030b0a05010201150e1b030907090f0c200c04020c0304060813 76
    0x10003616040020550161103414802c110414401461090500e442021004240d0701c030b038148031b02e6804000f4240d030712208010507100305140340d45000f501c5c0100042540200e0a007030340751000c110b6080075140c00c501c1321000c94000920030b00704140100b4109100c0005075203021904211030508141c00800d40b0303090384032110070260a100340412a0b100c4c8924030803655081c400c0d50354a0318050028070082c0200740040c14941450740c2000804500e6920080580c28143c104000507100c400342c0981c8150000300300c0291140b1480003c015109406000b03200c0c9503400c001008141d0503034095883c0c0c4405076061010a80c4543c016400c0311100c2074640c000861988042103898210324420341c0c080b101d000340d5920030409903146029a0002c0ea504803c0790482d200c14042000c16200c0c1034600d410040c0d0a10006501c410b0281038101c504010001e800c444008072030810707204019845800344050011903640c0710008029880340c219014160019052001140c2000881c00f880707595290459a0b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 360054586 1250 360053336 360053371
    0xb04021602090c091c110d110103050408040902030403020d350402010201020c0d020708210a0f0e0d030905040c02010c1e030b10020105041b081f02070803040c080f0105 74
    0xc10114200040003004040410028800c0c035032911959919100c2220803018501740c00c9142441210301e82c0b4000500440c0c1051002c004125140c401511544082c00c001030365441d20b08040485220740d4001426082c000003e000c03c2540c0091094101c284954440025592020682d040e0340c10341e8148200c2501281e94285403108404503044c1c002e80305000051403c4071170300c125030a024204202c81c0c056004071004114400d41840b00510380100307220540f6074a225400f5000160103180041e07c10841d0420b07028040a00410440011000c0286103080704112890020008410b0740110341c0100e0501c5024910540140282542c1441584501400b100a084040c94440081c460441015200c400d07100490316504d000e0f1758501ca841d40003040b41d14090424030243c14200d040d00700035011440007002520400b1464445034880c081c0c07680c02107500007030964068011128013425406c400014042044004001c1d0400c60b00c0400c02d988100e0001100c540c200c5000329040319102480050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 360055836 1250 360054586 360054589
    0x20a0203090105030a2004090f15140420091503060a05061c09030e010e10020d0c05070905010b190203030705030f0405010e1005060f0607150c2a060b04021602 70
    0x185500c54903941c5c00007440c50080300a084d080c0041c2d6015030a00000040c1481508a43d010300caa0a41740b00030b05100882001400080030b00c114840c1105102c28031000c45c1d040c0c0e903660006021038403411180520342d43c505040c024141e101d10a00c030b20a031400711046c45040714030070a80c1d00c201002003904200030316000500c403003680310010b501c102607004505002d5902c5103100d1100318038000e03550030780c1202038400090a0490f40b580d030f540c03042040540702c00c2015400581194000c985103056508400245005490848540c0000d03484030300300000403800b0090038020700289252401038000b040720200050b40c40344010744074000080c0c1c003040050510911920f46030b80185c8501700000742c0031a115001401c003101c1552f401407450b220001c6c0006458400d43c005003858040340d0301c516200301541c0307100b0796404040e95031014586404203c00240d0103914500281d0244c0d680c900c0382c080c07006030700d0121505481d6046603040d2074515a58400e080c2032080c0c824544032030400c0192180e03980c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 360057086 1250 360055836 360055847
    0x1091409070c06050103080307030b180402040c05090d080a0810060207030813090c2f06150a050d0606030b0c0a0e040e240402090906040c0911091e0301050703020a02030901 76
    0x1041c140c2031186000c85100000c0c03040c480d407030086024451842d16810074940060603140c8401c5010720030b00000f06021410700c080c049140c0c02580c11900084c01c036002607070030365039401010149540646107440e0b040074070111800910420760903503075442203980c40743c02d10501c5150900480e401680300380e4091000803407000090000c41c024038042880c083c1daa45022064500303082e140030000704141d016005440010070401c0181540074040c450040c0d090029070342c0c501d0020700d40055023201d0a460071050700d031210120058035010307046172850381050a151008c2c081d64401140d420128000150818402c8010303907191070f480d07075a4480030080401c02c100c01b425000014000c24051000301c480c0d82a079401c41c0030b8150311b030b4645100030303854940104440d11700014401e9101382c02280070000058800043d0310181c43d003060740052009060400701440c2e0203005421342d0400d03e0100c00304d40018000c0402038500c84114020300055071500f0046099002d14000300000d64030512281c0d4256002c0d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 360058336 1250 360057086 360057091
    0xa14041205040321020c0109080a031232071407020909010e06010602151b03010b0f0906030a090b090d05031803091903030f0e0a090b130c0e0a0501091409 68
    0x2407078030340c0c1090384079254008990424070121980d01e120110031068142c0502541000c1042400c1480780540382c2420151240d0004000408200965091002e40c81d0180d00c0058200300c0d450319030030108000c9000c40d1007a150380540950b03c3c541000010b02c5180314581502101d05007140702810445154244112144041d000c84015503c60054010289040200a002b000c80354002e290300003030450040d040c0c001c090a00115810b24500102103072000e40e0840c0d044070082c980280c2d84629141c90328295000b13000030705038080000000d014180c10260030407900503000700c40800c0280c40315000690b840d0444c1c400d41c130200710b09000042103040e0b04401c44030221600000e6a04d001217410010b00c580242070b00c021401c4881050510502d170384810f06201d914454103092940382103190020b070100c1030381d214241034291961550600d6882d2050305e61148904224140510107480d0805840203190700c0140d8041c480321a000100f03913100701039640032510707520302e4480700b00d00310400e020060000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 360059586 1250 360058336 360058373
    0x50112061d04080702120c0a1a03010512030c03070b011508090606010e120f0a030206061903020405040807060207052a010816090e070e0f0409150504022101020d050a1404 75
    0x80c010720380542c46d6191500b80192104018041d01e1403003404011801420b40c1007404003075403066910b001c030780c80c035002c990546000311040d1034801c8501e007401d8903611408100000e10301002c00c0080401ca0070b01d9140b4140e80210810764660450420300b20380c40001203c02c0c0401c1d601c40c2c0045641075000701d800f4005560054404c0d031b40000d20643c580c5c50b0100aa0314a8070640c009a00b0000349541448110741141040741c92601c440c20079008819043c0c294000a44103580d50004102002200d50845045a40c891015901c81c0000d04050761903e1500d801406126171010010103880c101c0a545035000a058545240a80b10302091130b841e07a22034941841803100d6044003140b10405040b08a104100640e60402c0f000300650030720407040c440d03101e918096801d01d1035550014454a0321410400f00c108400101076940d070002449a040c80c0e01c2024110340b40099206400034190000d02540400d4401404240c0310900b02008454079154080520090701012400160040e0b10031040c0180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 360060836 1250 360059586 360059603
    0x180302211b0309030105070903020a06080c090a0b0c0105060901060c110609210f070b03161e03020a030b0d020f01261302010f030c20030705030c0106050112061d04 72
    0x80c000414480004401155209684045416480b41c5406d008165000b02d40e854400c000ea45107070701051b0560880e018281c1408603920000d0400d030104400d56001c03800080109401a0303460b1803840d00d90f0f2080e60b509413954200750004826040c80c07902541203d0301c2c2d03503176192010030319203c42d082d506e032907445564002030420080c2c01964800300c1c2080d1844c0c1270340c850303809400c03400c000310b1601c06680c0c5020042d41041c441040705403c0c1030250b07980721074401c00c644510452440c0860361909070400002d0325050340c8140400c0d0316810750240260b416262020001036020400708003491900c000001d5001c1648003174800194400c1e100003503200080b65510500d0720f03040c1c202012018007284c0c0c9041d904c3d1380e102584250f60380103002c203a4048407130400304004100c500b8003c1500001103501d00c400001c0f09580b4001703d908004440e1065049001d480d01c81d541c14004138003070a00e03441001d002a100021441400302548100000c850000c42c030215a2101d184100c00341c544000e0003503c4404 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 360062086 1250 360060836 360060847
    0xb03063c030c03070b121003020d030e120601090507030b01031a01030902061e0a2a03031a03060108010c030c0203040b03070318050f010504021507031d0a03080f07030318030221 78
    0x210100a0080504290542c3c551213a0360381b491842d21501c010610040c0c400c0100d000c00c00750b110400424405030b014075180d100d0041407008a074440e400d4690b80d01e001d06c1280c000042602c1142d11460156030103030341c144540c0031094011820ba40640088c4400209034640190042d030007a0311032410300d032010b010142800c006c0305c06203ca541c0f185503221580b0200080340214a940a50b4019413150701c20080d40384140e5400d01c4100802c90894020141035640030390401d04000d800e10f450400f000142101c0466031a0446140601015201040800d0520542181d11800407045d034003030352009a01d09081d40d5032008201c000c2d0510181101e00c0c0311400c1e4400c0003091043c0040c40c1122860030000c01c490401d0700c140800801c1404c1c00d142032810a01408001a40c0880502801c910544080e20440b00100005c3c502e0030480d400108050000210603642d103003010040c11a00f40692400c00422940c200c9080007090030f81401401a0001881791024088481c42001038200140c0d1540c01e01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 360063336 1250 360062086 360062089
    0x90c08061002070e241008040212030c010e03040815010302032a0411120a150b0c1615080a050c0f1305040203070203040311041a1002030d060b03063c030c 68
    0x40e0b0040c0c610f140b50082c2031744c59201105038901104200c207001d6409045072100510000e08182c0003420083c418407811307200c0081401700700b007a2541c02441c10700800c264810120596580e40c000d1140303c2860007484441e40790114008216812030f85c01401400304003003401c18400d05c3d5000140700d0781300610480c022002c00d0f2280c2c030035007218181200029039204034040650783c050340014603a00c402c6041035102c60110000c0c08000c0304586050300d034a81c0b1600348010003420080c02050b05040420f42e0343e4001400030302d049001d038020320b264507000310548816000c2400d50b00304950003121014100105000354440c0e200610303145050300100881c01e611030000801382c1e441a41d0340b2006a1000c681031084c000405d58141401200720b508100100b0b62042a90402d100a91900d1203100040e0320160007a000780700f21070040101d510101f11045d124180b15101d074209030f0324280101d074040caa900c05084100020321645046803548000801340f200c9591000b0918600b03a0303018040d811007503a45 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 360064586 1250 360063336 360063359
    0x604080a0c0b0f15030c0a1e18020702120d0e010e030f0d020303060a0522050c040b070303050717040c36020406020f0a120305130f140106090c0806100207 68
    0x203480c0c996050011070810090b0416801090706072188250081040e8206c40d994000c2d40e5011039500081588419120100c0c1701034010f6036034003428400351503000707440300f40790340da03000b1b08440d482201d04200d00b80511003151703522055000c14901094a0010344c0c04290b000b00d003a10b00c0c00d10024100c50841026140e21820000a58040d4001d40c0c00403050003410310f41100c0c950013070300d8162012810401002c80102801407105a101c83c8660350b10049030924151004640242c040d94046035603d4a191400400501c0d085802d200040c81c02c0035820504d260724200d0034002d5411968142160703040c6208081603050082c0180d442c2600b858821038200045a43c00c88101848100162078510b8140080d06280b0100a500e03903c0e000016410300044401100182d07178080c5140004460340d42e04240c8c0203201681c54090318000b583e085180420030004425411800c0000080c000d03a950b03070702c0c01e6041c2d07107140311000c011500c9030f00081c6660501d8000005180140c1c4110b800c035941e1420030041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 360065836 1250 360064586 360064591
    0xe0a0e150115022b0504050a030f030e090114040e011b02071e0e0f2701051b0408030906091804030c121701150e0316050405060904050604080a0c0b 65
    0x1008120300c00100240411035102100e1501c0b14006441c015a044201049410300070520403800c40c945403a0408517481130090320041c3c040509010203142d140d003041070408090480440014696124140d05818420500b9040340e080030403050791481c9100420000e030001c00e102440940d6a82d10f001402e4400c1c1c48021000320300354001e000c0e400d050103400d507112a840c1c035900100c460703440e404104403071420822645c04040080d0700311964135030902d440c05c0d00b144030b00300350311070303102500b60302020001035005901030100c20b2080d1075690030307128460a10b80110b1054181542060000700c40c941040002042c12200c011301640032080150101100d01c0c1c021388056002904400c1c080003001341e01c840c40c0036419100d0411230b650200b58046070708100014000c141c05a8582441c0c203030303218090041e021500400034250f0350720700c25285007469021818881c0074455420074000c90b5542c2080c0c003d5900a0390488098001c41e40c4079146c6142c10360024010504000c002820351011401c400701c40b90 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 360067086 1250 360065836 360065863
    0x90301111c05010b16034410211109010b031b0304051c03020c0106091e140f041e080a080906091f020d0905070f06080c040e0a0e 57
    0x5405100310381c0010403038030160040c4008039000c104180d0407030314415002400580c5403421991840281d16240920943c050f0450300350b9a04120500406a0300c1440c900554108030b00c03041b0968810700800ea00e038100b8810319009140b0000a090001e40e000d5512400310b0003491401c41407201c143c04074111038001da01c144441305c0f0100600520b03000f5542135403910007492044a0543c245a00c459884003824181a40d00d4900d4810341e01c1c215000b5015107a000c1243c0000304080b5079078030744040103003110440d0801c1d8554640802c05107604c1c28865180c0c0180365061444060383c13a41c4100c81051005030003926840301200c00c03070250350b08071600d0039105441041140d07200d25901c00b026008a0000d40711030030a4201f801004013096001417011480520b400c10181170718801d0102800a1040c00300c2c00c00c0041c00d05241606000c0b000801c0001c80780040300200006507900760031120f5070815180006d040e50100403c00c80c002000c952035800110310724001803050502c4040c203242c20081c44180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 360068336 1250 360067086 360067117
    0x30203150615190507140a14070b0a0e04091e0c060816020a02010819060806040c1409130201030609090f060c080c0a031508061806070201090f03030209030111 70
    0xc00c6030300b09045a010002c04490080d0b0900c2e005a1100e60403444034140b00b4200040071404005000c1015403a010300e8a207401902c007131309554141101e0b4080c065418100c50310407120009241201501240d480c42040c2d0703980345402c10288100400b0f054846000e850039810000280d030700854401c10107809a00c13888000c03560f5441d042000e050000002c02d803031891050144c12464190b0003040d1890700c10340c24a04203c03281d4980c0d081f146441c202c55070190700c07180784c1034010a0043c0000741c400e0080d4003605c0c1c0f84400300c4d80d40c2e42c03c0e080020f5440585070040110808181841488d418050540380b0505000c16416198189003040341c1e880901a94440102003038803091100c14801e0b604252020703e00000e0a1a00030111030480c8114940c0c441090b42e02c0b8200d52602c01d00042c008064005141901d503182070005070b0310002101c817100506640070703003404217031258014400d29502c2030344070500b41c0c0508880c0d00e042e00290001c210041d010354980a42d9a0b030440480300a15001a007500030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 360069586 1250 360068336 360068341
    0x3031306030b031204050d1502181509031f0608060f04060b01110d050705011407050c1c0804020405190905100c0c0b06040b060408030304060b0103050601171501020703020315 77
    0x1c05407542e941d6064000e4016030103000d540c9a08808a505a984c241da0308040909249004056900d01c03120151080744041501404000501d0003441141001c450280c51220110300c0140c4c40c1c80340d612110b03415880303400c0b09244840f00f2a034002501c600c48000007130385981d910009080a00c01c44041042000b008104020081284a800030008081c070303054089941010003250b40d941c02c0c0c001c21050007804910001001002d402c181c0c0044043e8043c01b419040140010301140c01507416502b0314018080d41c507066201140c2d2844440146030f4901c4007584494082c4070003080050061421a0501100c84805890314007903c1c0c800d42c1f00c2ca00038018101d0040c81c070021a1a030649200410642d80748080110700d011144507003000c402c41d0006804004207000401a2140e80d01082d060700011040000b071140d0380e0302070011082c082c3c03030900195885e130004449401702c4003800b2a0f034131004400307e0641550821038011a14060040711443d50b100c2d00064680b504803860383c003240040c13108 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 360070836 1250 360069586 360069599
    0x703030f0809010507140c2a040e0f06040308190509060105010807030b0d02060a0507020a03031d090906041b08070902030a0f060602031209120c010507020d0e030705090411030313 79
    0x2500d0340022140000c104c641030140c40141111604104404c4001c00496580c05280060004845084101c0040110032080301180c00d9100d8010b0a03891081c0c5c40c100384c5842d40c40010885589007400304000e000c0a6446a500b41c55415018214401842c010510900e00c0056481558043c41e060302c000d00c0d05604d80381c001400c6c520020941010076040644080047d2184002c45440c60f50440d0300a03150451400e0894a50081d200302070b5000e4000f440002c14550860711038044940d1082050307008285070018012a1001900c90030b1460784140d0000740425003480416850041e000681000030b0b9450303520500e001420340101400030f90000500c04088074500c110b80c01341c80c2002e000d00c0320910346000030791240190805203108065250003d03d05c40424401c561018041c540000d44034070810244034028102102e442016104e80c1281e106054010040941808401030040ca481410b0506100400c00c0240084503041034400981c119aa02440504000030800303144110440c500903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 360071942 1106 360070836 360070847
    0x34060b040c03230c1207110123040f02150f09030c1905010507080c060c0c150402130e0c03010504060b0102160f09020906091504050a0b030f06041d0703030f 69
    0x400b0405401e0300091f0080200c0c032500002c1200d101060a03050005618000c2c400c45032030351100103800106c801c500340030594800b40400420040007800c038a4a904140e000c400d03116408184e58542d03041c1044080c03500c6c20102c070301c00d51050081140c0412680c0e54044d5504202c4001035180600c44450304980754501a441140c1d038603c0c20560034249030f00b15041041c2070b401801503031150651020500d501442d0000d00d0088680e4902402d8402086203000d601881d010b1100c0130070203580e01780700d694460b85c011301c8041000303c0c0c44000242424000d9158100001629905000c4401004020001d4a00f41000181d42d208030342c0028015018136500640c0c800d100680019070503401c80080c0041741d0095408103170b03031900e480c0844214042212002900031440c2c00041644c50b15801c1100c01d100801002c51101c1c02c1410214101b0216400c29000700da1031030404c104865004 = true := by decide +kernel

theorem cover : BRFrame.Cov 359892086 360071942 := by
  have h0 := BRFrame.cov_init 359892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 359892086 ≤ n) (h2 : n < 360071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
