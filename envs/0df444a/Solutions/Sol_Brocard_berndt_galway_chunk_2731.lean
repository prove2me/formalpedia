-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2731
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:34:41.714781+00:00
-- url     : https://prove2.me/submissions/11a7ade6-6723-4568-916f-3c60cd358bed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 491007194 ≤ n < 491187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 491008444 1250 491007194 491007229
    0x3021003020c03210f0106081314011b02070f030c05040e01021b0d0306061422050307060c0b0c040e0a09170d092003030a0e040f0c02030c06071706 65
    0x1802d46408146400c2d035014200350800820019203008540f0b1540c0d000e550300607800280681c3c99410041e007c3d04a0200808401d416040d110020040000e60340c1415420741c2c03860001c3c443c0e0385200d5054400c03001c641860b60300510460400080348074902250344122a008801c4003c000d01304810b10014014038502d850003507400700145040840d103441108160040035020781011916400010107880c4a64031032801c201c0c0b15a031080e20503000000b1200f8103040c0024818403440b0038140491072558640c000c80d80f50103803100c001509500140070742003085c0310b02c01c6080250303902180c4009078050382c00f5074410790460310001107201031154031015600380a102c9000105690b02c2c9101003030b40c003114600c40101d44503c3c0c0c580801c146040c9130b042914408141005208014010a69034004c820b07150b82001112205000681c4595100048030b01c041e90b000d1021003040309001e9074076400001d800b81e080c41101d000600c11849407440d420340c2030a400c032107006502c500303040000100c070350340d020324 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 491009694 1250 491008444 491008447
    0x605121005090108071a19030b040b03240c0f04060f0201020705010504060207060f0506030d0339090b031003060902061b1c02120d090311010633090302100302 70
    0x10791a61408581402003001c0c2d001801e13035904003680e0741c032660a400d4551040c4003003400458800300c01c0070407241078441a031600040d449c525100060103400d07400300380d0782c041c000c00401d00d49059400c540d504518026206014007a01c502c0340d445442d00c94024035115441c41031005119540c820400382070020020310006d4286580f81d11800c0c21a4070030b903000c83d442e80e400200c5004002e61400307945003010039100304105501c0c10401103516010304100500c00c040e40c07070304610100d02c5038107000440640240120f8440d2480038000940100e0a246d406001c1000c000c4000707407100c1e5000850707100741c4141034200011841c5560700d9004c0d011050040b64802010b001c00084401800d0150609004101c010004880d0004403000c0c10100d0004800854000c3d00d80300d4050741d50a41203507114001110006107450740c03810201c81c090307107101c047c000315424090002070360021201610901c0c1c05051006540d0380360f04403400c0d100d0301030f00140301c082400541d041001d40f0b04100c2d00500d0306881d00b0051f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 491010944 1250 491009694 491009699
    0x70314070f060201090210082412010207060510050d03020304060c030e130605120102090f0603250c0203150403121505042906070512030718080a1b06051210 69
    0x1103104480700d4010b0320050307548042d200c1c15898140c0da8006032440070708080c12103085c0785070941c042c081c0c0b0554902c11000b0b1520000104c1e2101510b10754824a5400210744484507490020f011b000161600c04d080365240d0004203040c41c0500c0303074107074903545030b0000c500d004d1510400b69480700440c2016020310400a0000810361105418007000200c0d1010001c0c1150610b000c06c0340c0400f014400b05820b03841445030b40c0003922400114410003508590160320790344c440e030684c0792000e00f26030608194961035403c1e04600740c014199004861088041c0c0355110751403104c501e40c45908480160000f00c1110303020190465580c8150f07184105180a0956a603d52001c182902d0034800d1416900d001015461004070845440184102c0304413a807600d0407000391648d0b561041c1d1f01c1c00e0030f4149171b0000007007410a80100a0201403e02d80381c0d40c4503c80b5600d000c0320792110170214040d145050110006444c0c101485982020380e6000e485075400c00f128504040c07110b2030020050b00b190503a180c0007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 491012194 1250 491010944 491010959
    0x1621020a03081e0c0307111201020a110607081302040b040e0613140d05070813051e0108060d0305270d050319020a030c02010309060221071404030507031407 69
    0x44010350300541c01a50350300e15110200403c420070a0b10711034080010b000980803154084102c604854002000c1d080d0350882200007030881094403030b6699503610025100d09243d40266004e510540070b041502c940d6a511401a9000c0740d048070655440140445480010b10b0990b11003200458003030800206052201e0816103094426156241e820401044220400000d00e0400c0c9901604601030081c401d200d0001501c2c80c0a2400014060032000c0794a40c0110422400f1074000d29000f01031520032040d44044141c295825100b9500290000000985a05042000c1c90800b036040c0d0719185005c000c04259500d03140744500ca55041d804070300748000740783c1e98001410182030141014594801c100444e8000b0320307542150300d03025034201285c030602098000100810541e02820f011507002580e240c6600240b0505c030091181c01001c2e02c80051445101840c0d03031013480c0c02e40b140703141d100345a080840140968800140554080e0784c0c180000f600c900485260314107850b04441c5015203c045 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 491013444 1250 491012194 491012209
    0x60a0504060212040813060c0f030804150f1b051303060b0d230601050108091c090915061202121803090a080f0601050a180c350108162102 61
    0x20195045c000101d4074140200308004204010941c074140701003816440c1e9542c1010f03256045010301407161500000301840a002e03500014a5042c040c200001c1540300e042c3c00c001c1100c01c03000c00f0a00803c44004000c14000d034211001003504a1010842d10320307594860f0080c00b914024a900032403800040400a1a07a2005407a121985000810342d900c1c0b03009123901d04070f0705034051070410620030184080c1c40b002160f9504801900703061003504c0700c41117609075140b000c0c0340c0c002c80a4501d0142d5210499160117143d02c1560380c250b43d0210550303804400c140c00d07801407000f0b552040d210040454544a80c080f510611300c0c041c1000d8a040245071000501800310300e502012258101c03400019404806100e10307405031808440f1041c0240c00e00c00c1814220004000c3c1d1603805544580f40c0d000c031801088400340d90000400004004c0c44048500d0320401c40e9613845440c2c0041d0b0500104502d1000b0440f0815000c0000f50300b4501850058500c1c07804118841d051440d0401e40009c101580b14610b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 491014694 1250 491013444 491013451
    0x190f120b0913021914040e03070305070b130b0a021c060b0d051f0e01030b0105180402100c0c060203040f120b0c03071b03170906060f060a030f05010e1b0c060a0504060212 75
    0x452405101740d1005200030741e01304c0541c80a4540082100ea40000d800c041030b10141c540250407a48140c1c5c5103002d18010440d07000c00030f0001012201045500c01c8940c0041103109241404456030369078503180304050300e03050b0240e2101400280880701d01c3c0c0300300d944180e61010304020b004001a84003044c00303c42c0700c5a90460403604500710014000d00011450382401443c064580400084800c8000c040114014000070712480d903080e0880700c410301c200000045280c00c080743c0c1c1c0042c1ea031001c010b941c070762191103401c2d001c4003140c10000c1d444040f1418011010340101a010342503842000f0b0031040d40c00100a00d09010201c804464420b04294400c3c041e68842d89981041610400c202c011901c4010120703001640098100101c0361241e403620103144000f07607055512150036200580140480c0907040010f546040c000080c0040c40c0c10100f802048540e201c044040040000103200740b00e1200c05101603031028001c20700040442c1d1083d60b102e40104c60050401c1105a171580496005a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 491015944 1250 491014694 491014709
    0x1a1605010606020f030702060f0d0906050c19020303011805061201110702010813150209060702090a05060108010812040509060609041404020f0307061b08190f120b09130219 76
    0x14038081c002d850f010029844000c0002004509003505540015510312a03c20320981111001c18404001c01507a000f10300500d80c800414042c40c9020440d010060b041580c1511040032a070341750401036800803003142c0c1038400150b2080366101c0d225001c8005440b029041c075400034185a881d1041c0207080c070803101c04602010515a6509203400010088580a080380c405401c40350440000652984000102140c2141c005601d5800c8480003d090f80140032000c3d42240d07080c001c22000d40d000782c2c4120310402003604e581100341d072203a0406030f03240490400340300400f0b4104000d01c1a0300c3c0001e080c2c2e0307016000804140c0350108550214090310110021b2422850300d40060008501e0309801a080c0b0724801d50043c281c051070204024601d410044081c80c80a406042c44011b015088085508001c00107500317818000031000010017011017401c1d01d81c0043e04211982c0e0f4040e4560083c103581e00b8004000b46482d403501c2e804074001c04035164040742d01a4403800b143d1469180020701d4402061341 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 491017194 1250 491015944 491015951
    0x41b030b07050703140301080c010c110d0507030c06030b0102190206042409060e010c080706020f04060203040e1e01150309050d11100608030304170c0307080715050c03011a160501 79
    0x751a005c0c0c5000c20094100c55020014401408000340c00289008180001d00c1d258048000300e00380b0382c10040c04118400d4029008205203801d200000500008407846480c2034400e507544c1d404128221000c0a40c5180182c003c4206000030003c0c41700003880c000c0c0018802c80c40c1c5070350b90300402c1d0b01030843e0301e0701c0540c02441d0240c401c400340c00c140701100a00745410701c10501c08040000a01c00450103000802e9900d02107004014041c80e40d040d90006080595220350356515600060340d20b403c10310072100b9104d50385000440c9074080840c031010080e002d440f04860f80e42070914004d0a1101d08850004240d1344202c1080071980400c441c100320300154942c1c2010b03643c4074100c1ea08203038002c0c050301841d42c2800d40410807541e00000701c80d4803d800c90101e030100c1d096408400d080388140301040101e0311000c42d40d80f040c002c400c0000d0085600c1203c904125001021b0b81f101035680445011a0ba00070034401000202d0440c104400130085000000b441c1c0149041c00150720701d0085419074050f1365 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 491018444 1250 491017194 491017207
    0x30d030e06090f070603020c0a060204080309191404020c0a150b131406220e010510090b0a1401020a0506090f061b1818071106060a060206041b030b0705 67
    0xc14855180c01001c100c02034070030703000704450305503480210384141001c06600142d010100701040c8420003140358800425507a45035602c80d015034a4102c1d07110144079002207071071000b8043c880c440c0030003194030030110150218a03d10401c03000350410800e25185025100da1900049e542040c40c20640480141c00229039903018240248034070401c0d4415901c1d0300c0c000190f62230004601ca00c543c030140071952905000b803862000500007070024a4525010f0404104071004032040d04964407508101c045050740540da07220100c1030f01c01d00c40e031194111002020a000d03000c030089091451a90600440340041d00030b544240c60203000f258112038580048940030b61840c424494180c1100c031407024103000980c004420000c0d4404e00303541105038038052040c0000b80d00d401c05d440d1002c41c501e071001079081c60301d1140540011004800c80c040740c0160300024a00703142488610b0241c1c0d00550041080d6a11680c0c1c04c1da040c0030503007069054082c03040c400400a580c90030002d02c20303019030303884030748844 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 491019694 1250 491018444 491018471
    0x9210302010e01020a08010e040201020705130f20030f07051c05060f01080610111002030906060114131419180506030606060703030f0b03010609091707031b11030d03 73
    0x40031100b8001d500c3e40104844200700d03610108407070554030802d02e08500d41d15a80f00503880c0c407050354025500715004d01802d085400041c0d01240381039a07180c5091100580710b405080c0c00c98100c020341440c4035000d1000c02c803824034a459071030b40034403282440e40c50600070f6000780300001c0b10740030809003040d2a807041022a013080c0403401c80d000c10a00301118070342800c50028411211844200081200003009450300c0c40b41000728600303a1007034031030455a0b4284032005a886003030031078425001c0ba071301c110044881c056600490303401807681e180c2031410609166221044147c0050100c0d84030000024000507030b070540c52140e0042c0003e20f20401c125200215110965800816a41c400d4002d031007017008680b900c008403042940d041c038000481201100840740100540700b0b959802d580f918070080380c062800d0340240e01d503600a10f0f030007521760800c1d603c4001e10711809000900043c1700404118100111411804115214006040c01203440401003071a10070112666400241c40d140c0707074007411 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 491020944 1250 491019694 491019701
    0x50301240504020405060f0d150e2d06040f0e070602060612191101020a0501060e0106030f0608031b10020a03020711060702031b0418060204030b01230d02010921030201 74
    0x1410141c0b03082d41454500310005116024000e00b03031000c0100060814000500c41d40316201c031540c0341c0c2000c45825100d484c49206403200f10b40c0d14070110b21040c26842030a034030403844011030f000301c14a8901d41e50ba0900340806090503808040704142c40301b604840e41c2000740900005428180d008000390320b40041040070328403c2c007403508540d420010110340c05010003082e4204c1e03250059100c2c1081e2801000407450b1120054000d06594030304940420020000b00c42c09049540582c1d051000514004032242100c40600c90700313445074000c000048603643e0041e4101480000034003518541401003110364140d80c0000007107400643e00050403020000c80e034a00c01c40c600d00075500c05c6c1c00c100e090b80c0402da943c800c42e143e07019004019044e0919a41e03640d04400108020070b84940300140c000d0ad040006900140010bd030102c021400100c1c245156601d4250310b1401c8854510b1140c1c1d1000c180a041010742c0400da040180300400440d0741e40401c3c04000241001291801c020022414001e084 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 491022194 1250 491020944 491020949
    0x2015090d090312080c07060c120f0204060c0b131407030618030c020121020408010b091303090909030302091c05010c0e06270301092f100503070905030124 68
    0x7804400c440510115244000a0404079031034100700300307252030301c0340d05840601407800020000c9040040d144c226542c00710281da0000da01c020107001032110422100280d000d18003446000411010801001c01c0c001050b007600100c118149540d150407548500307103c800111a03026403540030003002c00420a0900c1034011410240903031880d000059a001080d480f041c51020b410000e4410716810b010304c001c0c0c482d142e0242425811599160384110b070501804090341c26a10806000000603102200307140103100c115031540d0b41d08045814082d6100082c4007011003981003583c2031004c002282c685507003001316502c070541c400a04c255a883d003203082d01c07503103100300b402c0cc80e06500030006915102d080d42c103641030000304200603420725101c4068100440c4034580c1d0541c01d040d100030602405415104180d1010001c01c200c840e0071120715034182110a4149401c00100c801011180c0d03c07503009560070401c5c520b8910f42035581c4400184c00e660901151580031458a0120460749007412040c000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 491023444 1250 491022194 491022197
    0x206010602011109010503180f0114010803120705070501090203070f050907020c0609040b0d0813170a0312090201110601081c0e0d0201080c12010b030420102015090d 73
    0x29580c1001c1d521036003400b4030b41300710741442800300c00b080c081c03210505880c139019501c404a072a8540c4210070b0a01030318000d000100201c1200c030000c41d0300d0602101b1240d041181a80380d14a6482d004030407a001d43c03260100341c03455565400e86d0300050354184180401000780b46045c0743c41608203c10040501d40161422042d5844125003940d142c9888081d500042402c5400181d045456408200c0202100130000e041141c00190341111003a204220742c182c40044042074050707054003004903910350315024050701048207202c09001f081456080741031140d00c1032500d04e5540e0000d8256078600002070300b2026094001c9000c0b62040c00780c034002a91402802e1408143c20074242c0042540700e04c00aa0290411138804005502030346004200d0f0300e0803200803210011036a58050f8580341d80c205075811a421301e4105034440d600420540361a156102c018951071454004a0301601d0603440030034201c000b10141c090400907000103200c600c040003c6200150198030703041c001e042c244944501c4240 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 491024694 1250 491023444 491023451
    0x4080c040e03070308160c1505090d050a02060112060b0603040f06201b07050d030c02010201180b1515130e09030c07060311190f0201050c040b16060207020619020601060201 76
    0xb80429844241e00c1d42007882c806c560156502040b9044a640c07118410161030901c00840c0030400c07114a40c400c9101c0c440f0002510810a148201102d0fa40301c0d5038100300060703204100500c45100c690181c0103007280306101c0001c03a00d8489010505d590011182525002d11030307103d0b41c1c2482102e005203014603584214407901280041000c0800f405050100c2447c4100032140d0181c0c07040c100412070240800602504c2200d03014640100750190480c8101d0055003000c0d031145800c210924410303002640200c224189549614141c50740111802c51117030312180f080c100d88468200e00000706002555403080410b003d0814687d5900c1502c064500507032540304001850081310b0100e1700e0016075480e40340c0031070500f400004140b02c0b4002c00c4640394a032070004411426003a0445126007403d103458000b441181c0c2c900d0030603d401d02443c1306036250320404000711244011001c45181c40d10381f0801c0300500701001d94000c00c04982208450500c0581001542d00c501c80d010048907004000c144005d2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 491025944 1250 491024694 491024707
    0x201081b070f15060b0d0e033604060906081203060d0818100309030f090510030213090906050910111801120c03060504110c0307240204080c040e03 65
    0x26203451144100140074910240304480410032507040040c1d0b10b0140200510600783c640c0b10038681580121211890307103290403040c441c903141c00310079240c6642106401f03c0340780e5400d2004a40081606a10001600c1c5c11809414156140d106100150401c02c1c400180700303042800e001d1a0800007160000b941e102482084100e40c0c0703000d45140803a0340004065102c4100720b180b020350514041e0314503480410001a107030301130b625510004006001c0e9807020810004010700b901c02050078010142c0060440c00306844a900a80041051880c00140c1c03140309a83c500e0000215030b414001110303000d40711028442c1c542d02c2040501c81a0f0711424040010700b024903140d480c1485040f01b03449000c0c000c0541026542e000b102100111090f0707442c03e010094038140010024030703941c010948500e1902850f8200202d00e042503039101c2940c0301c0194035284030790b00ca004421745031621400342034640d0b001c080c443c1d100500160008109920040200340e805204210688444901c40c00d0680d0040c00341 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 491027194 1250 491025944 491025991
    0x7030218010c020f19030f0b0708011710150503030d060807050105030106050319020705060a06090c0c050703060f020c030f0706050f060f09061f090e06090403080c0306010215040f020108 82
    0x8500860417540d0b200081c40100c04590b20148507400985108400345030700040c40301150718584141403d03590030703c46070380b5030380c03101c06066442444211a900180841c23034902c4459004000801c810007004c881d440c1e8481c0005e10f150f0145c15858102d646503d0700b0000c1c9841000460090102402c00e42e05541c1491802440c031700006048840c0031400c6a524640e200055040764503440e0040c043e03922500c0c000b00c074580a00114421444114584180c40d0007861003101c2140501c1e502070301030022540fa40d2a0480a0b009081c003e246240d820060300401038020001000c0c0b02c00c00701e107082e0310707204241041003c0b00c0340203190200d01c010100401403c1c1d550700802d544004411520b0b25201d454400c0420702400001d58090b40d940948209400019007045542088030301d2000310303200e165601810701040a01c2680d004010600c0100814080d428a074080c560080c018412610722001c064440004501705031815244a2080841ca4041d543c1c85003590354040d8110300300b841c448044004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 491028444 1250 491027194 491027209
    0x11805030d0507030e1002090a0509010b0310090203010602030703200a20090613020d0605040218040b18070c11040204030c06020f0703030e01050703030b03010204030819020d09141807030218010c02 87
    0x84003002c99000581c9070451f49c8120030440640800345c40c0c64080d6850786010151035109542c95842c005000d503000401c0ba040c0d008880c140c07030143d8083c42c01c007081650161504242c16140070b10700b54402d8100c90802108010317180090740a40388500c0b0b407a444102c40d404500d07410781250b010b00c41407010802c4a444401d2501480561460300580d6101100d0891001b441d07a0782046130300c2400058140313400542140707149040b4208903410400b0b903190340104039280602003602401a031032040060b100c0c1c3d02910640d200345004003008020f0b80e200700c001070704990040e0011031310742d01c564805005130b9504203d5000240c03044401403420904644002d00f55910800416040210006505003094429000368070074000140096480356201c5c030b00781001e6000000b168403450441d0006220f440c1c030001e52040d00c00002e440309030005007000051282c0389400c90031203400c043d01d0090038900440208000c1d100c0c0440b607800603181d003c1c0c0100c044c1c010203d490000d04000c04030801d500940d03204139 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 491029694 1250 491028444 491028463
    0x30706051623031b0c0a030314090a08010e1006030f1b030807060203010311030d022107020d1520030a05040f02091302100c0c05040216050604030c11040614040c02011805030d0507030e 81
    0x20002511008072750740e4074052044600c0c6540080c1c00e10030000d00b0007015000400c040080c481525212651050160221070107484003504008010075542e01084500c1e130094141c50310000000b4901d81c03a40c50343c1c0e4841c1d01170301c0121b6015900100405c140403e200a0000c5000b048005c0c014005d2444c200030360f141d054000420043d240391010050a01c04442181c041c958041c104100308038040c01c10484019001c44840410742c200702038001102081204030f440300c1689100c02e429030302c40f41d03420001880c00400071607800040e00c0c00080569540300100e8480d03441e11000c082400c20034414450250b10640040c01801040303115200054548215035013030350b106480050700e0b410302505580c5000e084441c082c100340244c80900c400d166002400c80e500c40e006078000e0080c101a41d01f40401c403641845000a000c07104900030701d00c0c1c54140c000c0b05800c82c2900c0007241d0600c00480511081d1062401256070703520006142c03203056941d001c1c0c69400901402c08100c00f001a84c91342c0d8840880a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 491030944 1250 491029694 491029697
    0x30f110f060d1d0d050c0c01181205030702090c070606052b08040b070302070603060506041a090a0806070e1804050a0b0a1506050315030706051623031b0c0a0303 71
    0x50f40c01021410030754038014454009070301241d08812481c1c1c030280440d0b02801c6040d20038050140550115401030a09041c0c01d00945c03404a5164941560003074402c00100040b1070a00040044001590f11640362074000c12200300303040d42d5100f403443d0900c04c8540030340c0214002d400344012250340000000000c0c84407145c0022903801040c1034a0981d0f40740c411504180013018010922100389580018500e050310200d440c1003003210f40342d50410150b40194450300340c1007240c2c035504c03038400d10040c3c01030450300b100a8040c040d410380300d03651141083c03070840e800400a424a030b04505103180074080010b00b01c00d240d201c0c3d4100d0405441d107039214152500301501150700c0002140c9190040d901c6100420300c6440280c0d2020b03280c0400904a03442078aa40720b140007020340040c0d29240104907902296169202c080c07800040340c5090303454003480441a2513136905030b00000c400100b840d2180c80c0c40103100e00559070b13130170717100c0d01d40540c1c2c8076600e0004186500c0361039458030342c0e20ba8204480659405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 491032194 1250 491030944 491030951
    0x17010e15010504090504081e031311061308030a09090504211e081008063c0f07111507030f0219020c040537020f0301030f110f060d 58
    0x5030010b0b5034502c580c1d401381a459207000200000d111052000e0b00301049603055040011081d8000c2c0c24581c0015114980209120070506000845c40440e41c00032050151070142000c488800240d10b1007015031204c9115000021201e822580c08107102016210280c0100014205900c400c100c1d42c02d8911b18400c200c140c445600c40c1c00d800381040380e21070815140241886031900380010b10085041e5400d0f09000078a4101040b01c107408103655214507507a10050302c50816804406100355104091b21030001c01550740b070548140e030400128861410340d503101029041401008290705541c2300003c50070341001c0e00440e11001d404002d1604a8010704d80482e42451402c0c0d00b1000744561001c01c60841e80c0b03a140550840c0c1c0208040001c07160840d410480d40c0c1c0e65110340940e00700c032444100310b695003001c110388841c500304541e070841007006500141024050b41c8041643c0d4000c0e0070545400307501070001001c01c1804040a02030b0041900c6000c40c2503000000302e0313420b01800f2011100301e0784 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 491033444 1250 491032194 491032231
    0x613031e0c12060222090b1f0c150e0102040f1a0d05070e0d060c030c0813080f07050609070314010c05070204020c10060b0a0305060a03020d02090a020c070f0617010e 73
    0x40e103806803a0000040e2507401c40d04c05941d80190345580c070500c2241c54840c10054a101a03180520312400da0302e01d82300b082032210040f014216440c01510a00712000c0c85503c4001140740d00900ca86104000141c0005030f90b0303410100012481095540404c4007042038031141d000010010303080d6003401148140110301512000c0050f90506043c2121030b40005030180350344188007154026180390074107a02c04101c030543d54002115100c01c200e6a423107075010b0040c2d0f43c1c40003808000080a00300d21001405041410b80e07581d81d824003030b0a07a50020701f94044207003401400500201c11516142c580d008206100610b00058070754060260041d1046902040c140101c1d241841020301d02040200308004c0c1c0c0f500ca4800d00c410383c1001d400100003920703040c001921401c010228000340c0b600105090003a0100303508212410780c00070820060b850302400ba01360344a06c1001480043d2075082c52900d0a6800c1c000014103924a250b6888200725210004200114540c05401d42002c8910610091000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 491034694 1250 491033444 491033453
    0x20307020414070806090121031413061101060e0f0c0c010f29090a2c0d1116031101030b03070f050901050123090a050613031e0c12 58
    0x121680a90001d00b441101d08002c5903940800f407048000d626451542d844003014424844824022510040280d11810a02081480c06001e201d40701e4902241810461003294a1503080281c56030305086400b0001e20409411240c0d0030404980c40f8020844541b0b09080458000009070610035442e01c50300100c3c3c0301c030760224119055541d0220082c0220444180d181c00203103004e240b030520007001c8607115140d1020313a0605041a030380041443d500e50b285e180000009203d0385004e40300c555016900c01d03851202c00f0b40c8034042028543c0142c40c8022000b04060100c4c2c0d203c82c0ca88459801803404261517222851500d41036a4006016895031841c910060f40203041010300386600d403282400c0010041d60a8070f02000b641e8041d6410101640c0e103900540b0300c0c60103201e20703980000d102c51b2042c5805200310080c3c03021940c000c2410148642c2c480100e40759900c0420b038410758948a00041c420300032011b81c0c0d95a001032488a08500400340e40310101c18000d2400780020421f0702000010501 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 491035944 1250 491034694 491034697
    0xe1603170c030c06060913030903020f04020405190503011d06070e15180406120317090a0c1202011806091a090a06050703090801020a0503180f0d0504050a0b031e070203 74
    0xc2007035086950f15802c11103120ba560008680c260302c12115800020049519461a011440d61580384d4000c124210360030801501521801c081d0000e81c02e00000440355158449a523880c5a940303001181d440c02d00c0103041c00d68041060000010038242c0b002c03202441c002441c0c2d90700200d28500003003142440e00004044840e034006551502c08003250413480d480e00303500c8401562201302ea081103940d60760b10a11000c9409028040c0c0840da190844484c00506c59202c95889030b0720005803040340f0311941d28110540c3d440e4000d0416440580342440441d41c101c5e9480c0300309000026041170b42c6142080c000c01080c01d502422400c5aa0403803620481c10444050341c03070584e0010480c01100e601c5060042c5250401c4d002540044c502a0f0000341980c03046c405c03150440d507556565481c603682c4400b0529142581100340c0028411030305080b0340d021040c043c9900c007030344955441ea621441c040400c81080c8080d00401e07501c4c10200f05004420028106100c0f001c0f0b10b00d020f040f00c650b100300c41681503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 491037194 1250 491035944 491035957
    0x140d0e06160201020a150606020c09150909190c030303052a0f07060501060c020102060a060b090d03020f01240608151c0506040602190c0201090e28050601030e160317 73
    0x541241b40e518000c9203590000b000f0b50340d00f54201c840310031428041001c5034006a88444052801249007201d600708140b02031b50110414088940c10a200c041d00301c01032824a10075039003010100002d00030135a160150b99005004141e02242644008642e0403468140c200030942d000d600182e0280e01a000030292408250040800c0010b503a581e40050005040c500c0224014028800015200e108a100e190103640c002017020b03052550791001d001c0c0c06849036a055080d40300b40f448021003d20240103031002001d5450513207440741041c0c00d00760140b074619081603080c48403076810410001400f0030000502c0c10200c1c0d069a2070702800f100002003813800381000d0201d00420041000784a85600105090642c401d1f00c1d080c0301004400483d8040800380c0000c0c00640d40100410502041c4901e00350003a1410380303045500e10480000040709110740f03262281031900d40702042400d40c3c2621545c2c1500400c00007030600c1070010f5100c200400818000201224039080032030340c0e103c51460a6445 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 491038444 1250 491037194 491037203
    0x1140609180f0304030201020f0f060402010e0d060509250503030706090c050a1716080d08040809030d03060801050c030105130e011803030e0f0715030f1503140d0e06160201020a 78
    0x10a61400c2c4419450340c0c02400164050702c540b20032080302100002e035200300c0030820360150855803501e500440301301081400841c0d0022003820303e1400318406104850294017008000c04070b80d156103582a650100711080c1078400d01180100f0441a2008401c0310b288a078031440001d140c1159141203440150650082a007000042e413000c03030b24140b9460b07054090503201044404000e10900ca40100e10018020410139821000030740345054050a1a41e400030301c00c01d03035103040c00442c4000c0380c81c000500e400c4100280d1101c808000d82d01d000c0c4200ea800078480e400030340c51581882c0108100a100c451501103059494500c0311800300b080d44020a5290364070f035803000514003400e008000e03014008075070429005040d40a2100315000450b582142ca214151001098240744241e000f859404034031350300720b510b60010503e40702c0204d01c44405544100582c0303081000c40d215291402c903001c0d00403400d011030010401995a1580151004400492042d43c05040c6500c0102c0c10075110701070042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 491039694 1250 491038444 491038453
    0xf2309060409110d05090c0d0b1009051f0f0506041e05040c030203061903170c0a0c06031b080915091501091d0a0807110619020106090c020114060918 66
    0x1010b40b074801d001006080142a130500283d164850805d4440d901303292151303480750b07818130301e41c0c000b4820703c85140c0e01c000b0041d21400110b40d640800300503190100d480035024000f03002910011214001000301414020314014001c604201c04500c4510540c0120036544002010000a0489085038074025000240003441070752a60800540070350000d603a101d2150b01103150340350a440384c0480c4c0c40100e0fa040565140d48031505840501365a0100d0503401d01809100003040200740ca85e501d00c8010440c0365800600c090062140517403620415100302d080103010414060181800070309200740e80125800444613032a64180c2c80c3c0741c201010040344188004100008034106a94040c104c3c2c2c05c60b440c4104c441100c405449034540001c408000c00b40c0f001417000d500071403100450600c06400c0900528038107841d00f4a1084404030044c4280c0041c1c3d11400300780f14500310f13400b602c480c1011070b0000f8081c3c164005046403403200d005101c1400780c101000002c00848043c1e9800b04d82007984415103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 491040944 1250 491039694 491039711
    0xf11090a0b07020a031b06140909010303080a0e15090114070207090f0f0e1608030a140d0e030d02090415030209040303200d02040f050a0e01090902180112030f2309060409 75
    0x3000090712030710985010606800380d001054208804480f240278005280803500d80c255941035512a001400c41c550155a448881070203410030446418140500b403100f12071031900e82c0315035003075800001d14429840c0e02c00081c0008240c00142490503030f0802c000105400314200200f1000740091000300c80101c1c00c0c4042102c4181700440c0d02010000304c0c1f01003c0d005500c6082c05540c03031080001d050000f614481b10f0760820b81c561005402c589002500c04280100e0000b1040c0c59500058103044580d50b0006036034102c0e107014410003003c2c0407640b44610388030f49190000380c041c1400034000740a058960081006080c02042001d00702403448002c00c0d01d0320b071080311220080d04140200411f6122450010a9520303101c0b9480c4d00b11581d0f41c80211180e801e007070102000d006185022030f048a8200d148040c012881d9402e28080c0540c0044651010020b0400070603680c000e40100c03085c000c00840348080e480c0c11100c00e822aa081d0301490b982d031264000840c03024030950703200328115403910456 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 491042194 1250 491040944 491040983
    0x1f03090c0b0c010c0e1c0503040b030f0a050a050103031d0d020a0801140f04050a0206220e0f1302010801141c03052d040e0402130905010f11090a0b07020a03 69
    0xa0001d080c180b6000704032461000c0015030b1004040000141d0015019000e80342c91b01c1110201e08000e407140050340d0400c1c0d03445200301039503002901c0c0c00510003940c50030017a00201a201c1c070380c2c0c00000040280425451510041c00d80ca6040083d03142d00000890030541c55142d500c110606694060040201543d0f1585114001c0c03020700740e444031010890003c148540209070403540035a4210018003000b011035404c00246c0d5100c0c1181060180582c2c103240c40038080007084c01d000300090459081039107001441c08612100040080506040705030038800541d9100205906482d070141030615074078440701c0061060300c400018107144041c5810000101a03102020344208000c3c08006801590020f840c0d808110440c0540520310700300b84406c00015018400080c3c006002411141e0a6000c0c0b401400076260b45c29800c1c1d40c142c1d1aa4032a003030068040c42030424510030411440d062006401c0000e40c03043c010b200304c608046d00451103405655403070f000c0800031584105000c3e0a04001c030403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 491043444 1250 491042194 491042197
    0x304020f033c01060b161a1303080604181b092301060c050607120f29040908040e0601050c060f06010f0903051c110a0b040209090307021f03090c0b 65
    0x103a282c5045a509440000340390500a603000e030f880c229121401e010090503803121010b00c00a003590f0381c403010000005030559a48509000b00340841c1304030000c1000d820007a00118014205c2c1d4041e919205680407801003002800c5251980503000b0070400746551407000e0b0008440c0c0010404a103001800c8101240d0f02d0000700300d203415040548101d80e6502800c0d54603903521400074000d5004403001034000c0d44200d035440c10304031002c07a0004100d282c0c21a19000c5510a1818406046980c403030100f1000080e0204001494100d8080c00000120f564600d1079005905c50784038980100008151031b80e000300103450603140c01d4000c0f030325580f030800c0f10b52140c0078090b580e0601107500c0b00309480b0403502c10703901041540d40000c001c2034041d041aa40e1948819084d035840d040020007a512041d1840c00d003c08039a1764015060000c1a0810340104082c254002d030048156910400c00d050040e02d43c9401c0843c042c603401d076040d0f070301c14441000342d0140074001d000810140d07080f5004100c08401d0f00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 491044694 1250 491043444 491043523
    0x60905040e0607020a080c0a0c08010e0708061302061602090f07080f0403051602180702010c08060f150d1103010f0e060d1e0807140703051507050304020f03 69
    0x320144441903040c07880d603031503403030a031000c03401a04040400004510048020300242c0c1c0031508540040e01c182e02c55181621480d00403101c1a51209028101d50004002100180c107071400076000c68141610300700b42c490b000c003000900030200459010f0802c0b00c1905814030168010301043c507585001520040c40907030413a021008100d004020904207203461020750700c07d550507152030b4549a101e140c1d40c08003003010b107002c991007a03d00101c02c00c1e0041541c074950041060741c001140140c2200c2001d0041c401c000c104c1402141b442100c0360305036580ea020f0080704100001e40c02e41d14210b440001d13010b4002c5d6500d182640100200014801c030404000d08100e885d1100b030040320340c64650800c0301384032000c3e1020b881d03030b0b84079442d002c04090ba045203081802e205030503503464140300341e0318a80f280d1000f081d0041340d900f010004000b44207007804542012400d89054041c03618164001070140d000140003e4003501c200c0c0408151030720200801c0c0c82000164103400705101d4407200d18401300600b04c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 491045944 1250 491044694 491044699
    0x70507050f0a0305120406021605060919080f031015080402090f1b0d020c07090501030b0c03010305030f0901030906180309080d09030209070c02150301090617030901180906060905 79
    0x2034030410040d0700104002100d250b05594461405500d001c4840602e60b000d4001c3d20030541c20001000d1542c10083c0c407580c800c2c07003140985401d02d8800002030a04914182c0c1049039445100300782c0c0003400741402c030b0704103080040400c3c0d107079158454450101100b035045280300b208480c1150104a03040015035201b02d108480d0b04c142030f925144c00002480c419a10814244044803807200481d034510046d100011041f8001810010303400070840c03030848590b102403101e90703a1b10010b20521150400040d40503506039400c516551445d942c0d40d946c4d220310500e4803481c82e408207080c1da20381e1280c2c00081c55103401070414000c040042d03403060980b22603400201c010409110340012a80c0010407c081c021245440341c001c483d1a42d000c3c8212620000c20480c104500b1003003c2006030f59090f41c407510040340009254883d8104110f140880d82d560b040a0641d0380101c16164001c80c0000444840180038648076440d609a021601005081a08290340c61802e0420201e21651300105410899404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 491047194 1250 491045944 491045953
    0x1906021306051c0c0e0a1d07020d08040b04080f0a0f0e1009090f090807050703031803020d1203110301080f150103080a0c080d05010e07080f010e06010f1707050705 72
    0x1140c50544891080d075900010700f40e018103ca034200e0141d5800a101c040b00340c03c0001515400800041803140c0c00e4000304101451008100740c003600000f201980a50507000902540214a03c080d218500041c4028240c1040701d000408010b08e00c8251244207120000603500d460301e040c0081d010800030f50361100056032441821147c0d19101c0115140c000d05900c0c0c0020550500070208050316140d40d48808064481440000144000004207900d038054006413040301e06502e0b00500741001c2ea0414209000016002e00c0540d40b0031762a01c100551207094039604041d001016030203820b4002d245040d1000c0400002074010000c07403030040300100308064038505c01c4006080d441c2c5100038000503218100520050359054014801c0e45405070280c3c107118100020034086000b6124242c20201900002c8020700c0300e100e030400344154108c1040c5007107042660400f00c00b10608900204124108180e074440704d4503160085d200b400300503400c01550b145500d41101c002d0010ba004010417105c9119 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 491048444 1250 491047194 491047199
    0x90414060f010e0a09021e041d010b0f0307030c1b03020c1503091c120603030e0406150c0b10051e010f080106091214010f0504050610051f0219060213 66
    0x20840342c00c401e0030b0300203040744c1c4c00742d0500b03100c90000d4000e03954200c00008100d410080b8101e2000241c801001e903001c0d0041c0800588440b42d260b0700040e07120744c40b605028004102d9001e070890949610800c14503000031000c03900c1004840200e200c41c0c4034001c08200e00302ca0702c1850303804036040d11168170941d201040e50f140300241c01c220f031008132038080c17250300088800040017081d0b50420180c07824528210302c000081d10884c104841107a8000c9011a520071400481d6040501800c00208449940c04c3c241003400400908a1551000018030400d200f0000503000c4079480b405002800020b4002c00100112004034080081e00141e02404100c0c4900180c08041c81006124162811b90b034607102c1441c0740c032080c5490300d901014125443c889991308d0460400c001d208081c1c2c414806240441d40b810541000c504200c4050413058140d11800003d015680740d207040c40152880042c41c0010214003100200d040c681601c00c410311400f03414410409000241d009080c0c03102c03101714816545070303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 491049694 1250 491048444 491048447
    0x40609081b1c020c0f01021606020d030f02040b121b040303031a030c0a0b070309170307110105040b1b0f011e06090b09040303020d0f020a020a030801050406060c02090c090414060f01 80
    0x610710b01201c801030744400b0151040c1d080180c4988169070041c01151484000080050074003601504002c0c010f070b110301c002c000b940d03034140945102c04486140440c40c0604100340c210091041c05030b048094450b0101040420000395010648072088151044c3c4440c0c49203401000790070f0814405030740e40d0308a19904118900031841c02044c1c54000c2809051a10700303864030180d500f009000f541031103c901000981070080d01c04c5035048482240c0910303950001403a001d01c0e098016401070741000340600c42130288030401e07022202c0034160848050f4480001c007510300c2c07622803801c1c00c4070100c0d424121408001035400783e12106d91a40d0140c00d0044545440c001b02c1110100f20400c0d51104d000c00110780401d020b60b0040c10402c4c402100401e8000080c1c500c4420b030fa10000034100180d0004500b4014158071440c4203000d000210740070b000851604a004000d82c05005002c1c1c440c440788400301701c028103030004031000900c001c0d00c00d2001408a0180000ca298100e40c01400707a441e0750408030196 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 491050944 1250 491049694 491049733
    0x1020d150f0e180102070804060f110a0b060d05100608070501080a0506060f160f080901181211240310090506090c18091008010c1b0803040609081b 65
    0x71030401e402c03804160349802000d4086020b00204a11a560800124021032006c10051000d4581364440c005424130780d03c8020b0403103ca08491003e039410013000000010b202c082a55080f0601b100c040213450800c2c203204c4d080080310381d02003074101e1803d040011500008501103089807000d0f2180c1e001c030b50711041c0341402c2c0d540480d410f960281040002002003418100a0a40d880503402d85203582d00303542e52012010320100780e0681d00c522020880101310740e40584000d01140d40b59950700350081c03500680840400a00c0c50040c1040700d1008075030015102d2403001c1680c0c14003250406105c850030003808000d80e000340e905400701c1d00c480d0004114540540507103402468080d103d140c03d543e032200910000e8005c5814203048000b0002501d02035507450306100d001c1d00c101c51234000490f1070201900d08545840b021503040c403002018800140544204820500f50410341340b9a07640d580d440c01100404000500500c0c9240108545803081d0500c0c01d180d002413407240841d041e1303400c1c900c45104e26 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 491052194 1250 491050944 491050949
    0x10080d090b03070c0305090904240b0a030f06020f030a0209040c1e1409030d02010e070905270c15092809020c01180b24130506030a0501020d150f 64
    0x81c000c0800105803901c1c46902112000350081c03811508208400c0005000741d01c082e1001e50b00280c442e240d4402402c441d0400100c40c592a40702044103400030804100680c41601c0042d041500d684402c505001440d01150014040c2c0004155603240102001c4001e42180264a0080e454080b00040c03050048002c2c280002052802c8212911920340440e1454171981841c10041414015030700310f51030420840c2c040304074580004c200c404021014515080680e400800e05da4103100c14031801c90486100f410610440c1c03d40c3d442c1d500d42c43c060162408111070040c5800410014820700b548404101030010254110f0720301e282c40400400031040581d2441c0041100c2132841020801069030398010b208040002001058000001c82140c8004500d60400e4032029440d20400c01d0400240b6400c041c0250f082c10701320389030b1103500d020400c000004958400d500b80c1d82c8000c200103030740801c4001a1076512030003e47d0742c1e0040e403401d00043d1000d0310300d03034003800b1001c80040707101c80100d2042006d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 491053444 1250 491052194 491052209
    0x1d0d090b1207090b0c01023007050c0f06131b060206061009050d08091005071e03031503080c01140112110105070f06060512060f070e0a0e10080d09 65
    0x910018035107400058402a02400a010088900241044444d13002d040c0d41e070322801c00141ca0b44030074414074803000440b903400840c002000c4001d21402c10303a01401c0384c01c2090341c94080d4a4a291440c000d02c2c0940c5048108054854001044111000c1c584802001445094020000320b0b1300415074103040058000c810243e0448400262203090490b5a080c0300341c0c0e20701d480e55003240e131500130a28107181805c0988a800300021121070508000c10402c0500d03255150440c41e0020507120541c01044101446001d10300340c52690f000d02d4170a070000c1901101240c00c0300101e03550ba240c840c0495104403410b4910b54200409014280340c94850305040351004028210300c00150364503190100700340194030381401018040c804c0441c0354603018001c0a4896600054504d05100400c184082c0628000329070354132080c108055010500141500b1180781d0905070040408200042d036408007640010000c01c50706410068451013600c0b0407400c588081c42501d00c0760f1082c42c401c0350281d60f00d000d40107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 491054694 1250 491053444 491053447
    0x102032701050f040b0403020a0f06090515190e010806011103041707080d0f081b1e091903060b0102070608010303050f04120305030613200d09061d0d090b 68
    0x42981500d04480d044000c0c0c140761062828482060004568006400c4030b0101c0c44041424000c50501000540180142e20400b60b141c0e4a0b05000901005240c0240f6011b000d5000010201101c42c0c0d00795250aa11200303003000c01f400b0303084020042c0021080c40c600141c0d003a00810f0065000300c20b42c03614000504060344c07a003410320300c076040301c040c05050f01c20342c600c01c41d00c000074950400e10000110900564919141c20944440240081c1d07015000500d0030090f080000c07060703641c001c01c0341c419582d9403600c0c520701040c0407114242070094481098010200383c0c05004c1d0810500b14610650b40704180411a80c05140c00481e5507000307034001c42020418140040c00801e00400150015003402c0300d04500d0191284407043d1391442d018411808100080140b11035460012140c0d002200760840400582c0340e2010440f03050106508580c50626001680340300c160041e4024007011904004140200101c81e9943c0000380015142180b442c01400c2c17405c000341d44518030b40821a0007840a86 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 491055944 1250 491054694 491054737
    0x90e0907050402071a0c210705030601030b040605090a090c120215070512040306021b0c0307150c0c0e06030706030b0d061a0301111b01090f08030c0c100c0e010203 72
    0x2c001d500112003a05e21403100d4220418081c1c1001d169441503041c00041c0ea00c81c00401440c645850030f0800c07080c165003150081100e410742c05002d595001d4000d10340413442c09a65004a0020282604200d070082c1c0c0320001c00a59500d59082603801078070640d1038202860745c444a03c1881909044000d500c00da401c00d0841100710403c024014417030048054849440707441c409004c0c1ea900941c0111344031500400c80c0c3c940c5580040319200402108006002c81104202c0020b8480b04580034044e64140c400d80d000407654464004403400d15030207049140d080303407940000c182c081c01c1129818401d200703005010424610034051980c01e15005000c00e480740341940c0e81e003405407040700c0400b42d98412814017101d9569007401400c4021141901c0c082c1e52710301480c2c15031011031365001c0d450080d0381000640d82c001100d0b04e0606c2d0200786c12500c003680300c0d02c4084c0400524441c0014095181c420036070450a03002003a032090348040d4003a10f401d800025041d00583c7c81e07000300080c3c80c04901503031415 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 491057194 1250 491055944 491055949
    0x609131b091a0414030312070827070618090e010605100f05070f02010c06020a230f03162f010b0d0506060121180b010e2202010507020405040b07090e090705 69
    0x13558000783d00400752070810f40032030042840c0c00e00803200100022280005d0141405c050f40d41d180f06082d40203143c00390059050b0241d41d0358501c902c03c0008100c0940b10b56040550203d8034000940700000007400152800106140030b0051400340c1403142a0080e4a640c41a0007405c0654240c501c68440c1410043c10303032039401d0305140303203001a414810140041d00c005605480203202c03000c0c4588501201591141040b02003110010f241c00300c8440c00c015000c20380d580d00040c1c9a12003485400020b00d410600f0003110100344686029600081c0c00d032400102d0395281200d04592a6800c000300003210341c400400c1105c080d0144003400a0700020041f8110f54401d210046003600d0300000c540c0b6503030440e403c0004031001306901e50300e1a450031902d1810000c200303000314014a030241200c545401d060110b25401c1c1c0100079080401d1041504c0311046902503015941141c3c1c005104202920740b0782040d008207802240e80354000342c11160301260040c061940c6900032403092004010803401c0109 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 491058444 1250 491057194 491057219
    0x1207020f2e05220302070f06080a0b030c180619060903030e03010c0c0201030b010207032306010905040506061210050a0605040b01020703050d030f1811010810050904020609131b091a04 81
    0x5043d411809200c9020807091610202d10006103e40e59400250b880c0111240e822903000600880c400d400600c00350215559009032003001003540b0740f00ec0300d5900c80c840058400400f0380581c040018040700001402604003109008580c025140c00d000d46200c84105400c03503214000f0100418500b1440c240503510a6200500411060046521040d01c9403102e83c81c150322007e5612070384031007410725465048107102c07403801020b03804400e00c10350905550351078441c1c030000d1125006a115074107911030307c803082043c01c10203000c0180410480c142101c069001c0c00c028000c640c040c0742000d503a0403003544000f8401040300e8000025241103415540114060403825032014441034440b20f0b01500030800d55001043c0900c50705401464080240014108450051119800d41d1452004110a855500351154070546c100c0d6001c1d0b44954580000e18040c0321350a02405080c0b602d80d42c51352140e8012a40c441068031a01d512403041d64071410613030740b900882c1c0b0b41d0704000014001008207110410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 491059694 1250 491058444 491058511
    0x60112020304060b09090102090a08010204030b06040209030307060f0f051e01061b2901051e0d0201111c231e120403090603060504111207020f2e05 65
    0x1c01013020503206000401c1c03007505594140899600007043d007810b01e001c214410007004c1c500025400c03e03255495520030250010401405160000350311642954180105c0b00150383c026000c00c00f0a200c500080b004250141010180918110105a08003400310025120340e140038501d00081e820000c0480b0410400f8000480601d1a000700e4030001c0d1b170380d12a910060300310035000517084101000140d075105060703107c14090707080740450030207080180350b183c11074460a032403140134480c1c10710040b622041c42906940c924010708a100303038021490340c0200e581a07041c2d03540d15018000c20b0080007075100d1200401591007400c00048400324464160aa080a04140700a0a2402800c813401c0c0100701103400720001508413409004294140c40341002070b20301901c041001d403842e15140c1d51103106504204480d40500030004180910801240e0035115800007a0745c03400c803014031600007900b0401c08000b00014244102d005079141442824840c2c640410411045242504d60303454881200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 491060944 1250 491059694 491059703
    0x3050702031e0a300225080d050702060706090b060f09150d0c08030415030c0203040510080402190603020d0e0c01090b130305031801021009050705010323040503070b0f060112020304 80
    0x80c4003940c500c441c44044c400b50f51401d500980740405802690041042c90343d1070744582c0480d5600c1c184407464000500c502421960706005039261001d00000f0f40c0760044007401880503040400031401c10610000345030003200b06481000b00300c80f0b02d1081100142040300c400c3d4070401d81c18100c00c0145000b079090030348070f4042c4607030031012600c4a00c40303803d40e48960452403c02c45812002d2180c1a0305201d80c002003095840035504140c14000011b01a001000c00c20f01000342400c0030134190755039824040080c00186070030b070014994035034000d0046e420987c10189030740c1c80d080c0034620440000c109079030310315416524001800c1c04c140c540704035508140f074007230080544c0641c00302c0094420801004041c2114041c520b10310f04000c002880e0a01107030382c6c0140c55040c1401c444c001307480000c50009480f000d00340802d03c0000f04240701039100040c8100c040d002c491a007840f0038854080010144680284d152001d03564503000317109410305040d01c00c0ca0000b10a0488502040d1080d809503801512a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 491062194 1250 491060944 491060993
    0x1706220209040b04050c090102060108060402100e0102100f0b04180c0e0415050702060f011226160c030b09030304170f160b0a1b0903081e040303050702031e0a 70
    0x590000c13404640c01102d0010019100080d00811981c04120160043c28280001c00b4649815408a00b8820b2015610b07810711440d207621303c0440e8002c1c0119840c81c800340b4400c00580800d03c2100000e4880d012100b40101e1402e0000c1d1040c0018665502c0e0b000c0d0407240c1c902e40c0f10b180c1845030064010042c415204150583d1607984090030600849024030721950080c021030402848141c580d6030180c0c4085156030800501c280090094241c3c03205e040c88210166a80030000060310809210f05981c0d42c2018008a4400040000c048042c80949028144c038000c00e50710180c05035681d12081c0d4016050041c030300c14843c1d4030460840248069508a003200f41450111901401e20100485044440d1a5440200904180701d80300300b0b1038000c0049000000c00040110161041ea9640409440f000c030001c1e02017018141401b0140d110f00c40101c0390307940c1e00d07980d0800801540101c003080f8071070b004056481d440505500c50b90328041ea1290054680703a0519a909010340c6000b801a5881080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 491063444 1250 491062194 491062211
    0x3120a09020a0e01060207060e130b030c0d06140901020a1e090902030a050f06090114150705030a0c050c0d080301050904020d020301050a0c0305010503060c0304260a170622020904 79
    0x40741e030303040e00040c0f1405114100035410410041c0c01c001c19034206030100100c05c0c0c0032600c103980b104045940b810001c03600240c8030403c5d0010a0610500e45a40e40d042503050249500304909a4801da10202110000300c01c40d49584c8900303800d030700c00c10010b000040d44e08241006600340307059005c05141c2941c10201d04160380c0d031003000144c0c6c008803000e400550b41e8104104041f5041070f1580d42c000700480e058605c56040c691142c41740a44068080c0c0220453390200c414140d401040b02c016641280c100e9455030001140240240f0200c4d0048070a400b8490bc451102d0400c0910036018580c40410030f42103070300b050188050700c54001c100380da116226207220005a142885031502443c2c030500f01241a01200002030306550301170740628000da100d84208070780345545105498100d035203c0750301d200c03c0030240d1030000c1980070030030901840c240002d5642c41340b0303802041703c00f80307041080c2c10f00340b41d5903600c0c1c01c000d0f032038511480a1083c000403120a0403cac50050b401010103074001400002c0303100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 491064694 1250 491063444 491063449
    0x403020a06270e0106020c0d211407050708151005130f1410120b04080a050d05010f051509100509040e06040609111c020405060103090206070b070908010207020303120a0902 76
    0x11103a62007800f210503524014400c095040c071480c0c0c803080c42601c0c2c1d11000ea5181d9100c03007600845924003020200300c6010a081248100c6005190038141201c240d2180703198204107441d0620740c450000300707205950007444230038020800d852080c1448007611062901d424103000084182407000c0340c0c40f0b60340344d4042d03000040070f104000707110b4004404a221840d2804850302740f44d0b51504412003c190802d5824000766038001c8043e80158007200c1a44c850054500666039401500d101e41303c0d80b420180081007005034254084102c407421a202d02d040b030308020340b1805c248501e441154000303a2040002046a014000403e0341550103080040c00c0c01302203c41c64104402034038101e840503250642d40c010720010941c02c2c1015401113400b6030640f25880794454103c03105040c028040c5d0744520029009030f002e54000054590041c00d1150b850400f4a0040080301c0216004400714004140c0410048070502c246d641c02c5a01030000d41c42c00120020940b24160010f001e40e0015490705412801038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 491065944 1250 491064694 491064767
    0x15030616230f0a02100b0301020f03190b060a031a04020414120304081e011a03061902091503040b0f07210f090510060e0f0606070510111e0403020a06 66
    0x81c1c566014045c0d60284041030300640c2d403420046886030f03005008030240ea06140c0210b0f40c1081090092220130801040503501800350400c02e5640250041100d0002640503040302d00c10394031041e41410000e00302d40400089019900901400346150b902d01451414429101d841b004520320031070342003641d144456481c10b001075040c0101c0032204004200b100c1742c00d00603240c40d1250412011010280714002c80d0340d41e40000c0150454516540c8070080440450707044400080014001d51104414442120b019a0090320120f5007035007400000340b500c074581c510300f500410742541d8400c0001801340d140005000c180e101c0960466480d0782034150424540300b81880d16101c1e60260440210114040d01100ca8035400304004800c24420400270200c085441039000c14100d6501d070305c600d40350900c4c1d890f200c003d0740035004403840d10b4204039915410802400380f60030301a014402402c40300b21400341a006501c8000c0d040f10807550140209401801c201440c1c1910b160355502d9a00074143c0304030340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 491067194 1250 491065944 491065957
    0xc0b180918011803022103190608011b080f0c090103090507080610050a090c020c2101050f15150307030903020a12050315011e03021e0315030616230f 66
    0x30f000096100c0c1056014082d03103000000130310010001e034001025012843c400103001401080700101003481800031a480600602030740d030000c100b115403100303c0d600341741c121000d40ca022503800000a80085046181c0d03034400d02c01516040c3c03d1104410055000d4142c07503004450038010200c02003080c00c0c0c208030140c41000c80d035644001d290702d44014015181d020340c01c82054030b400c04160602e015000540c0030086071094030205076504480c082c3c0380f0550002100b0240c42d5007400d09110340104507125090089000514008042d50300800304160708c4001c40c10b0404448052000413039090103584807050060280c01640c03040c2683d81d545642400907031000102251002c02403004440c1e4100a08250701820300b4440658000a1807004110b03101d90415401c25400181102c3c0810718030b039054001e9501004002d849003043c0c01c54031030340081088118041c0c2305084c000380152450000d01d5214803003548840303041034000341144008040882030521060000c04c001c0100243c44c1004086 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 491068444 1250 491067194 491067221
    0x3080928270e061e010f0e040f06151715011406070b07030e1528020c0f010614010c020a1a040506070305120f100e0a0608030c0a0c0b18091801 63
    0x1038130b000100410110b482c92801194400c2810060283d08440303d00e25003540c214052070307086580c1d54035280d0140c0440c580c00038240343c1001c2d01030103400740c090341060643c3e41c00000c4107900105100d0307455446c00704081c000c12a43e07500c001000312070340781c1c2c1802c1507078240a8541d5103404500c0d12a5511184140d80100c0000c1da103022a20051800b0f20200720310105c0303008a103000782091040b9180c441d15a036007110194481c0e030206400b138981030f811144000c038081c0c1034405a001180d80d060003440244030f006204004d02001c800c0540c8143e103600060b9600916802c1c030b0a09100300c002c183d200d0000070203080c980c104804102940c030a0003500d43d0f58030943d034066075886a401c125440501c09050b00c000ba040c0c0c1c000f4054804222211030382500e8408191017902c1c0c0e500100c0901401456120351580d00000604e403200d91000b08940d028103000719034034000c142e6a00c68040e460700c2412400b8040801c4446401d080d03180100099401c940f003250100d2040884034802821101c41c0303150309a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 491069694 1250 491068444 491068453
    0xa060c1205090105060d060f14070c02010809030f03010b0c070f120516140f0f0603070f020d02030a02100902010c0222060902030f07111603080928270e 67
    0x122240507001d07141d030000c1158000d00007420840701003080301d001041c005080d541c07140000841c0c800d140c0c0c00b800c03400c03600c40159200341c1052200035068604590301a1b0002d035158002400301c0e40700004980314070100042040c0345070300c0e010030b541d03035038104403440c80c041d010740000010201103d10045003e00200351026040480c0307880c01c20b00e0040940e500004124803028200654820b0b500004035511050783c40403039184800b000030b94991801e2241035030000c03012040c46041b03580662010409811602112400303020044180d990340030f80c44034000141e04c4041c4ca8140038000382c000d031800c1c0348181081403480c003840e40010b000504500f40d4021000d04812805034040761402500001e1294600440c59070401400b180e410303900060216091240c1402003000c4080100f0030811001907504164103441e850b0b1034601240c0e0310003030807103202c0c1c4480d0815010f005034419403480c0d8038440e281284602032030442d0782440d101c0e444c1003800c42e0300007854804500c072444c1c0c001c150f81e4400030300140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 491070944 1250 491069694 491069717
    0x50702010203180a020108010513060302040608030711030a11040f18050a060b0406120605100b07080a09050f0d060b0f0a080105090610080307032114070225170a060c 73
    0x101c094151a08002d003d68000114080540d07000071110341919015074003079501d00385103a44803024092591000707400902c0d100000807451804070181c02c4c4070340700d035000c2c0804000b00c0c01003580d075444200c0050210b800c1d4146281103881d00350300c80c20058024500c04035400d00300c1414211a108149000d0310b940d0014000318040000324810003d010404560170040f050500c1c0f62003008000e0200002d19042c0d1307400c00b041012846d44503000c020108503091650f203825030318000c800c5402c08034030203020a841c0800400e0781d117021100c000c4440d80142c00b80c0d101850686501c406032102090300380c1c0103440480c0000498841c0042c0300c026082c0000041854140b10308002d151020082102e40140e0b20000e084c081a20080101c640d40b0707805107491540d018083c9070101072004400b00103a80b052511001d405001c001c0c00900348642c4441d001d403040c0390343e861220604101450381c45900380804104c24002d0f0b4010680104c5074107060b000701c1c0c075181403d5440d10100d6035940900740c00316400c0140f1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 491072194 1250 491070944 491070961
    0x2031f0b0a02060f0115030207020d0c030c140d02130b0a0e090109030908030901020309061c0504060902010f0201050402031c091a030118060602060c030402060c1e0d08010e06061c050702010203 85
    0x442ea006100024011003640c50640410008841b4030b0707180c41010b4001071030800395030751084d85500050f04215606246036480c03070b06178081407491141c540700500300002000030b880e00040388103105401034100e036091740354600d614005101a0300d0161b03010500d01d8002c940c204101000f41d1080c4051000064000c440707040c05003000030035501c80d080301e40c42080362403d142da001c004c5e99001007003600c807191108603281c0c0c0315104452150309000c070146880c04200c01e118850b0003986109000f80c98004006001000407402e82d0750484010b5055071104402902140700c1a114030441219842c200704410744a402c0e582e040043d402c010340ca0200003000520105d07200c0098a11040c1c01820f04025142c50f15030080e4481000900075005000040006801d5403a008100c482001d0310702c0650b400640400007420b510a075820040e041c030300c15260401d8115000740030305810796040d20405030a0350740b481c007040b001ccc0d03122910180e41300d8840140030324410418040c2d2406040c55070005a02c0345880c610 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 491073444 1250 491072194 491072203
    0x903020c01181401032720031912030b03031606110a1710180c0305012723010303020601030302120406170a150602100e010203100902031f0b0a02 64
    0x10840058580e90204000300003490220f840b40342400e090200f01850209108495818500300010220110710303034540402c00e260070301c00c24008411302c003861001c00c40403d1603924201d94559800b50701203614144040785055000c07500b002e03424500071904000c4c26010904603000004100340203584c0151089c20021607000ba20039655600740b040f41400c80c904001090729401383d4400c0d50104541000c1140888861108000380940e0041600021001d0040200500f00075100ca40001d01d002d00200d01c4011501c082da0810302d103004070b140e105090000700c0f001001480c02d084094280420ba0401180c400b11b80e650007507002e6009045658510b080190800d002c04404040b0700004110074803503c1c0d04250040314810300480100d00c69035071506070100800b03002c007480d00d1440c40f4038000a00503500080f11203102012010600010464034805800e0b408140d0f8284010401d20005001c1c0c00c0c4694051a2300c0178901d050b1820000703030360b196006240340381e400104140700c001614041442c1c0421 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 491074694 1250 491073444 491073467
    0x9030a210c08030412032003190209150d0209120d0f02031c050921040503070807140607060605061c0506030601030b1305070b0307020604150e0c040f0f0903020c01 72
    0x1050040c0a0781507403038441c5444003d2008246141100c0c412101d6482035003c0d00351518950000036050418550561194004076000c00031504a51903200440f0300e079000365440c03e100a40b000304c07a5200d120341c045d030f1500410300035071300643c4c00d202018451f540c800010802e40d0815014200000c02a4401440c5203d00122003040d0760080080700314a54280c00c10a003107031040c19000501307880b8004000d041c190110740311171401500c0200e001d40c10007050014030448804904a42c04555650b40c0640c482c40c2c60710480020100000f041c65042c04c2c0380e030041206c184500c034001011a00c82e80010134036040000720800034610000800a842d503c1d02c215a0804000c0300205400d40c5169110080c071744000f045074069550141584081140c10066600500703442e10900703440703141001c0000e542e203400f1601600c0490040d01820f900d0300f0a44501517403290780401401402941d0001d001c060641d0030380d40c001c0e065036100076081c0e000780382c40340c803200301c3c80f075405840e007003206100051000f401030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 491075944 1250 491074694 491074697
    0x71103160e010b03072f0d0e01020c090f010e070c05010e24060d060b0d020604170c1207090b01090e07030b091f1503021b0c0307170606130209030a21 66
    0x400903c440030f60080300316001c1002407070614210130800c10b02c1d00035034005601044018850305101c7ea005941150041c07107021000c1e421102c80c019800d0030400514415141d0101003000170005005656423800d406601c51580c1c02d004020040b241e950b642156410002e5001580044c400d10410001403041c100031800401c0015606050000000d0102000c889000b8203066a444d07481e4405e8891410220105030010012038403203550700b680c0300300605a13180092842c00f80044407085803a00e40c0003203004143c44030003010000e080c04500320003405c1d80f01c1c0d000c0c1846800840081c5020307103c54890300c01c030829900490012410414048a003c0c0a02552000e10f24100c064114015015081003192190300e120000130f542404203400900c260000481c2d012816500c3c0000102c0025905101c0c1c5000d80841b0f4030700c1d0750744d0014140e5959214102d591b6402000200d501c42c54108007180c1d21000b48040107140001032000285004407140003110f085450000d040c030b170014024103042c08140c15 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 491077194 1250 491075944 491075947
    0x220b0306010e0d03030b1503043305060f0d030f0206010b09061806160f120503040f230709061a0711060f0405030a2d0b0c071103160e010b 61
    0x348002070325240391810480c1c00740411041c50340500d0b1090300b104070080c10150001e40c050340c9800c0201503540c8200d07801d407180120101385800040d1014415004103900c04846070212016200302e102401000d0041c0c4e5210909480c603090036503c80080094852098890140b9001d400c0e01c080e007003201c140c2c0104180b03542484041c2b4240c540030100e450861600007103a4102220a001030440c1c01440c850b079035820320005060080000c800c09030010580100086003a4021085003101c4520084400800312011510410002460161080c828500d403600c1c4101c2c020b40d8009075441c2c5441c2d0f9125031275454850000b0030007000e01850941d40c0002c8006c5480c5061169103c02c902a18880c5181380a01c80c0050f00d441004041016a009045c0c01003ea401c04004c5050003042000240400c00010615422b261481080c0c007080e4640301c1d0740b05505000c55510507111402c2a002100195100800b05410840a43c0c043c44540c54010b80c05400a041a0810040b4006003805030013401c1880320 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 491078444 1250 491077194 491077201
    0x10c030b09100b041a160503310e0601020a1505061003060e0c030606070c0801020d0605060307090b0a020708010e0709203406050a05071d0d03020f03220b03 69
    0x25a10200d03020b03181005c1401d004084241c40e21031142c403806411607986004403004a0820501200a142d0540031620210291581003e4501d800d013103403061180c1111643d4040000c250b02028065002c0814010388820420b83c0d00c0f06c800c0c401484e440c0e281c20031b64600c1041001d00d410003291800110134a0200011420070010a03104180941603030301100d80800000c1d281c0d941e41e81281c001039880440350300240c2d40c49094a01030f41000c01811160b41c180303c0701054070b051010589208480581d28040341904e09200440c0d20b900003900b0794210b0140700000700305903d09000d01d411181c0300307200900e00345142c0141101102d00030104514850f000341c404060141c0b40f00d003582c00c0c7c8100700d86040f880504c0000f9003910010000e0111006d01c901c2c047d24000c1c805e07581e00c4107118a03950003040c010307640c1d2607070120b84400ba080303841e0055a80740440d040d120708007001169003a0744a401124101c119007030b01c007403840c2c1110000e0761005040100e0303081030100310320240000700301c0400e0060031802c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 491079694 1250 491078444 491078459
    0x9060709081603020418050a05160b0a0e01080406061a180d03021b0303070606060c020f01140a030902030703020402043008030109021e0c030a1107050f150903010c030b0910 76
    0xb00d042c40003038402d64440d22050124024511041070041e40541152000780803031078400d849685800c0c0e4145420700440d80019080d540101300c802d40b40d01a540c00102c0c0b030000c2c0066807141c40140050315072554840000c500403008005280d05000c072010042c1d250020880100d025080030607a050040414902400000c3e800241c01184500d8242020202003c0040403900d1070043c1c840c0034100c03a082c078100280654101500000311802a0361285809001c0401512a400180c014903d4031200700543c82c440d511a5000c44002031008040c0d4074007aa4980009042c1c2c0c20a806c2518060810182c01031021036003404000c01240c8003684a5055510341c40b038420501051141030717140f503000a00c0342e00c2c8010303200d4008213890414040f580c0718a400310120351344e5003040f01c440700400c0f0401c0003d8440f100015110084130300092440c0c1d0504211400c0c44081002031030700c0311890100780700d400c7d0160340078025003140b10300c01e0340e0000b03e9000c0340d010003660801c094680d2421b02c1c0c0c40c0c03106000381d1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 491080944 1250 491079694 491079733
    0x1020c0304030219210f05150403022b26090606090112020306010e0604290a0801140c09061c1a0609030d050c12040e07020114010b0403021302120906070908 69
    0x84400041e0745d003c900b0505008500c21600d8200514a000da103103403040307113902e03507006500542c0207500319800c0350201500101082205c1a80c0401424a070528000d650300c20400541c5603148403032442d918181183c400000c984054540424a410400811451f405c0c1a00d0050040071100c4030040e03510a65008a40c40703203810302030243c1e09a2140e00282d01c0752138070341120503c21098440803201c2d0003528041c80010100240f194880d40e044000081c440c0d205000f4441c4900660700044001c0e01c1340400704203d948200042c64002e90140310a103d100f408051580c02c00030000c5001c5507080b0540c90901c03182d40306400300d07071003100b042c010f42200c0c2d280001d5011840c2900d082c02c2b0396601c03203280c00c9494038550607100400040c00203000b02d0340d1650002a5406000c3c0c940007849401440702605440a03001d0068603030902d02031000b04090320780580c04022950410000614081c503845590070051022a050203890b4032060034803150f254486413540050900b174001e0142c509014804d072089 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 491082194 1250 491080944 491080979
    0x3050f151f1206020405090a0608100c020613170408070f15082a1c06150210020d1d010b0f060f0d110f120907050117161101020c0304030219 62
    0x2074100c4100154100050f80d8111000740c000141a030310b8620300300a20704007411450103101c01e01e00410b01c10444031001d502425005100503000360616685440b07011213644800081503c3c1020315685440c01c0118000062014000000240c03202c24100300c110040340300c1c103a12003001c103402940102d4400c1d5001202da17420454401c07008071a07600c5005c44612820702034400c40507610780022200000100d2410710700e071072a0450000c1c444c0640e290815604005101c1869000d60007501049082044503401000c6000c00c032a000142c4415141b1b401d0f01c00c00c4807648010a40e0344d54034043d043c5141c01e011301d0220300c80403100c01c0d1030702c00c51003450b04140c002c0a086100c16622008045800d41c40101600d102030141d020154407a0f00c614211502240180c2e81d81c125405070200c042450f510450103007042c1603503440343d0089525400c0e20705d60070384c101c0d100d40340400a05070708450180758280020002c1021240c02540c0f0f0b6811070041100c004440c081c04480001500420001d030406000d01c1ca11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 491083444 1250 491082194 491082209
    0x120412022505130e0303011d1e0f0403051201060f1106160f0207081912020d08060f18070908010e01060f121e0b0f070c111903050f151f 60
    0x240100c00b40700d000040c04c0d0003038904d0b056000c00300010030710520003000a045881d0001c10202c5584400c1c0c0600b8225144003e4103006030000e0000500c1d2540c801d00264200303100745043c503d03201303648128400c0c0340310a030028070000311103100145410307070b00c403245180399140d003005031405003000005894904c03400071202c01840b1941001c4041c4900038051140106208000d0380c4084e000740060202015044a044512512000c101074002e44001070200140c0929110015191100381c100284403811240d4507038480310801c0c0c000143c2c1c6d80d0300b003014040c0079541c40d9541c445040584d40c50941d00d50b040070495682c58040104040c20010034140c040358101d005102d00b02d129410294444420503000c807601c050762807010000c000c503c00c0024851401005580794036140c0d000c04913105500c03440c01805810800007200030601d00340c08202101c503055504100740a035281d03105400d140701a844c105052300040c03191010f010011b60081ea1041e850211010310310301c480d000200303c420900036011f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 491084694 1250 491083444 491083459
    0xc021003020408060f06011407031b02040609020c0115080a02240c030a0509040b010302040b1e0405040c0201090c1502030406050c0102090a03060504030201060b090d0611120412022505 81
    0x120440d0080d81164003400300c18003681d0f0549414000003031140d0040c1e80c02c0340064540002041c141c1d01c040c054510255050f42d40c44070307100c0100403860344181c0c00401a07030b009a484000241103100c0388000e1445c4e00b4031070000718044450034000001e2860b40d90081100d900001c003d0801a51052840456072128001c00c42c01c1c0c08805140506901441c01d46611074440003912644094009010b0550f0f50300c212418050407a0110046083c3d0003980b06901c280441801101400e01440340508203154422109a00307182c0c6e6000080e080d1031002c4150300150355140c0340082485042c5203100c01401c443e2b40340e400c0d1140f16210095680c031a61241d03000300200402c01a80c0152f0030340407107a070a800201a05c0710251070b401e00c40018042070314210050744c0b0305800052080345001c1a513250280060590400c480d041e154100909003401844040900c10403445c1210040c85201034016806411452080c001c03004020349801900d0403101000c02d442c0d0a15400d51050707045c00380c10b4800a03a0b110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 491085944 1250 491084694 491084719
    0x306050a05010e2b0b0115170103150e120717040501020d080a06080a06050702010509010615050a020712051515030705280e070e0a0b03010b131a0406120506010c02 72
    0x6007600038131040c11560f40c4000b2500b26051004981d15541694621403884280d00c103c20b03c10b440040c00410310600401c1010010000b003900e00080d980d0f041692403000c02c02903400081141072021166a100c03c000000c039605042c000710000444020440c440041e2425080c036001079a241c0c00b091400c03040008483c00110200d800b40c00080c0140742c00350490302848000c1c503200c8041c100454100b001907207008000340708554140240c1c003c40d018080d40e40706400ba080300c01c031066800104100250722981e480001c42103111107809030118090300c003030f20103212007001c0000038100282059038044c0e0645c001003450f42e40402c520045840c00c684151400002000340c0e01800000588229081c0c0315200000b1451001d1503d0341c0305081954841c0100c10100c401c22040700e00d14040c1c00040b4405000600880504038020030082d140300341e80b030300c1c1c00e59584110091609040d40480b2450f50200c1e04200c404d400c101d0b0b0140741c90440b0340601942c07400d500000c00640c00580064415510f08101 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 491087194 1250 491085944 491085979
    0xb0a0e0c0d0f0902010305090607120507020712050309090c04211103100b011e0504031509080c0309090c0414042c07180509060f0c090418030306050a05010e 69
    0x100d8880c540001000d0000e070b900d800d0b15030014107032400140d000c070f0304090011b200800c0c04103020744101c40070345946449044440c1060001c00000701014107502c11183e011031070b1300001004000300c0740706c0d40045a41e140c0e01005e00c00c5210015200c040d03203007010b00c403d020388140440d0b070400c00382150206407620101810700c07250911000041701e4043c000c00c02c172201011a1904a8000d1000030b0300c420a4101003c2d6803051042c13403d0017407000045081c4400c1c030001e907010b043c0c811024541000410300b00c1d01e5889880c1035510290300c2c04840d0380006000d101e1810401d1116500005a2013074900342854442440404c4410a1002e0301c140d650b1030f020b0441c2c51812500d0180000c9440500005001101c61169945d5203401003441400d0084100c040305a454040c880c07240d8041c0c03014184580b82c1429801203000041c00411140070280030005a0343c5461040c03400b2012a140358000e51089030a000c1c0494030b064000d03d0080b00e51a00074000d40c0d0700701d203000c880203005884050516040f03002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 491088444 1250 491087194 491087197
    0x91c05030c13090911100e2808070b0304030807051603050a09030c0b04031703040201022d010207030e040b1912020a030609081e0c1207020301230106030f0b0a0e0c 72
    0x30840f283d51400c511141407212801e1465185070080d46d0009100407400f2040d90381c101c01d4401d1681c8840035058034904600d030710300c04000000101d115484210f4890074418100f4609030000e42c001603000c02000107156115801a07000700d80d03414401d241130180901c81455200003c07010b418405d0005101d000e4038400c050352740055402030030030120b13242c8495011103da4043e1005455081d00e40c5607015024209204030381c010340c0e0580080000c18012001500c65622081912404100c0a501c28114843c04c2c001001554402d43c0d5544450354001c0070042103a9030300c003285000754400d03031504154540046510f0142c5842c034041c0d0a0805481c400220f0740721698200801c6a8100b000003820024010b021b0241c1850048031860055000e004844a9024143c0030462a901c00e83d14880e050308800024640c590000e8008500d0713201c2c0c0d929106025402101200382042070100401000340d01d03100f459909140c804040c007003110103000140305200c040c05400c80d1246280046400b5418000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 491089694 1250 491088444 491088449
    0xb2101020c21070f05150709140303090d290702070302270a0209040b0d05030c01061a090f0103020906190210060806180114160806060a08040b0a0608011103091c05030c13 75
    0x7100ca03075207001f080003801d420703ca10903402985c5004044164500e004002e03103040c200e02500c1380d07004000303d455240b450485400310700812005901d08640320031403410714500c28000b680050601c0d61451041c410168001d0804019039100044035000c80c10610700c0795030700040d20b001d01589903501c4030300043c024403581c3c3c4050f90081155440100b00107011024140c040c4901000f0402d4a030b41d520085a02d04140383d964072452400c102c0010180752002030300115202c103240c014181401d0f5000710f10668840c0202510841c1c01101280801d80d041101c802d030008039a40c248400c41c60085010703920140600071044a2000580303040002d00c0c01d600c100c0c00c108ca0303d0055011410005e0502c0d49050300b16020000003051000003690364100402211240c4403e541d0751500ca554a840390100188040c000400c50340e00c0384000103120304240a1410301c040c0079201503940c0d080580d42c05207004000d1000352030b15140400010300068000050b03d80c000752000e1940d580d14640b0030790151129564 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 491090944 1250 491089694 491089723
    0x3090b06012a0c0b12010305070504020c12031b070f051209011205060f0d150506010f0c02090414030a02030a030b0a15080406020403060f0614030708030d0b2101020c21070f05 77
    0x3040c034161098501c18858100ea02030b00c00e07107910a40350ae003448168400c00e00b00b094540c1c851140702850300c415100a540c002d18945480f103000c0b0344900031000c81d601c080c0081c0c1d5071f00b4000401e10305002060203c0c2d0302c3c42c420800f403640341600400010307202500005ca6991000c4c0da41e0300040306034070fa031940030070001e1000741800c0c545c134120300e88481c8686001100210244c81c28000841550040862944490303c0b502d407070701e92014681c2007000c2c1d4a070080c0304071600b2030301404c0c1d00e4519400b000034104800044e0080c54481c2c0c000040141110b05880e55144690b90f036101c20061302282c0d810403904a40640741c100655030319401c100010b44100d51005001d645001c1070041a18071a5000d1030a45a4082d224281001c0c54420035694010274020304110745c00c10415018910840d0340805040c003000b500c20040526404c18102c0020a01d40c000540c0e42d40008a035404901c044c842c2c000450200d10102900e82074102003402e641c011440d00600703504d8075692200510408101008450264 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 491092194 1250 491090944 491090947
    0x902040e0a0b0426030115020a170d0b040501051003091e0c0e0a0911040b040e010f0c09120503040302040507030b04090f150b0f0f0109050a0603090b06012a0c0b 71
    0xd1520b050708607403c403401e0381c20a2140400310320350070b54600c0c60242d8480d8241c0c1d0604590a0070480901c040b01d08400c1c4c402e40c07041b03810301e60000710300101c0011140c1c1c00030207440e00c8d41c010481c450301395154400b080f0712031441c200c01031100d5a101d01281c0c040d501185400642039406103048036011032070641d482d0a021803410b10100704920304a8001c1900e640700d100881c1911a009441c1c11b0b0f50f0f003400001c010f07542c640360b003440e41d0400e03a100e1089132100620100d09800701203900c40c01c40303408000c8403510b9034a490918004607040b1410300d00401e10001200ca0100450b100c49841c2c5c007560000030720a0392a1004208817500c0780c0c10046a489000348208074401c0c45e0715021104000c1c0010480e0034480324228141040c1c540d1245440303030007020341419150369082007009031012221005d24180f2202040104103903ca140c0000094081d54a0010396000d5078202900c0101c4011b01b40d504002030040031000582c1000740390100141d0300c5188810980a514051440b244160007400700c0303800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 491093444 1250 491092194 491092213
    0x12031e020a021816030b01020309120c0607030306090e0c01020607030c030f0c0c020f0306011d060d0b18070902070312020c10050c0d060e100315110a1e0206040b01090902040e 77
    0x28800021070003110314404d0521030704021201034081e180c00c40d02c42c60142e0002d1007543e0140c1045200000c01060a00503910350b81a484005540f80c0c01c98682900003940d02e0b8010700414659108880152000c0002800c550380da1a0000b507541c41c0043c1b0801c100b6480301c60890b2001e009802c980700c94001c800042c85000307010000144044280e003801e038400d2440390780b4102e090a0101d4068182c860581c0c0d00000f1421821201c80c080380c02034031a0b90002e0b140101400428065907066000300c035440703003603440740d980000050f14010454020600c02e40c41003084100007034000e84c2e0001441d00300c1e103000d600e8000c0740c408203082548080000c0310701400d00d400c00c0007080004000301040071404804008a5440e03444c810003c6204880c2191030007545c1c94280081b0710b0325150418000d94000300450343e00d0041c0c1070307011160401141c2d603020854510149001d903c05540e45802191184004c120718640b130380300c4401003801071060000141e540d07420380007903403520740044002c40c42c41011a200d0381c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 491094694 1250 491093444 491093479
    0x1e0f04060507030f08061c020102120d0626211303110a08010e0c0d0203031b07030308010e06150c0109060617160b0304020108131203140112031e020a02 67
    0x7400124103d0000d035192113008400750160010754004c410281040030596800f51061111400848043c0d040d0b12890320712904001103e001081902c90b51800440e113035150a81d0241083c05c5c84041d80070581c4055480c00c0a281c0010350110b80305c1d0800d045110014010007505040e20a01c1304800140000b01408030034041e0700e010140380f4990503103a00314803030b0303440d584030303080310300c420f40c103a5054102d0405a600740c41c001e081c035000140000d00752441d240440100314800f45079245090410b800c00401002450380040b1418010640302601c142c51f441d1850001e118821011500e0240b41c4000c10302e910480c0c803d500caa2081d40d44000d0401042d515000d80807505048050000c07040d100340301556244101d6a03000030b04079800d0101075802c5464640c015940344a00500c178400740180074012002041340807511f090b02203a82d440015080903000c81840c6240703816081909a4104464a4000283d01c042905804162001000550210000704900785283ca01010f5841103131600110402c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 491095944 1250 491094694 491094697
    0x3050f010b011d0f0d170c0601060f05190f091d040510060602030d0f020d0203190b120c19080601170c04050f040b040501090501051303140306061e0f040605 69
    0x243c860380c11030b45258400746041a0a040010340211503500d00c1030392814007581c4019410301c1078440110b594070500d41c0c03511039000300c00c500300c0940c020401000b00382d4000c415000300032203918045240941202e02d100800380440c0070603040000e142055040140b0480c0520050100480b0113005980c8100d2240d4000d03c041ea400c2d91507014000100c60184d003144510fa048035031540280d400d00f9041100500201800c200c24900940c0030800b900b0900c6151000314031400088070402d0b0010303a080341c1c480864a00d5201940600803d4070303250315070400001e10444100003200e500a240132902c1e0744060074515640941840d12a040000c40e89540d51110382a050310b0500c1103e40400c1d810307080005441013aa54011448520408240803980f42024682d01a0181c4000b04c2c041e5a41d42d200c0e42140c000b01c034100d52825111240d00101a031260399141c41941207100c5ca400c6042c800b0024107584108a109100041444110201820701e10b0a80b10003003107040205848550b030711000741c110b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 491097194 1250 491095944 491095961
    0x618130201110102041d0c0a090b0a0207030507090515041127090408040302031209210a0b01030803011e1d040c03080a020328020a02011209020a0308090a0b0703171003050f01 77
    0x400c98100001f901d003c0001094131404c110981c1c1300b2104510b4462211641d91004d0758134400c5000d00340010001c11000c200050081410500010382407500740689078003622942510742c4201c1c1407490303511210714020292244d21a5104d0315402100c0382e42c200c1c0c490590141d0000e904100c80d041000180800c9202400480f03000f0340a4507400c0001014105441c030901d1819684455140b483e2040c0036031480b0501099080f00c41100c0b140c1e8441d4aa1541c0340d1826841220907080010040c0a810fa0010041040c2c188050011003024140800800003008002c0c12440e00e17010000040d043c0002100c40e41d0081d5085840c0ba40d4460100c1c130025205e52041410b03007001d20741d01218604081d02d01c034801c03040c0085540545510304c5d480d8011560701400090303032400d03a5281d0342d180d4090313507403419140002c6214654041e9a5581c28040c40441c0200703502c483d00b407120911900c030100e6004441e4204007000c0a42001c5141d851500602254440341c101500f940f1824000c07500440d0154002c814 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 491098444 1250 491097194 491097239
    0x509070314030c0616090e09011a010201150b070c0b1204030824090a020405100c0506010f030317191e0b120d120902030d0215061813020111010204 65
    0x24161001e100d5540b40f0540782000441c0e484000022460b00d55000301038039507001032401c1545e4a40e1000d4042180d40b0a6426820782d954031100500e610040d0184980714007030030700090003001050700d84010210420720401d408484001b59900c00c200c00d01c184500500b005040c1c040d150340e0710046000d06d44904071001c034081208540800c02014515201006441081d0880d078124504070052101b440030107006a59490b40a03c800b00b1540e40b40c2d800c06134481c2281d900c0700e141c0d410382d050040c9060010307801180e01c0c1c07c13909801c0c4040303627002003081c400311040100381c0781c6074450180c140000c0000980c1c1010440c0b0b0302d001d143c0314081c1e90450411510102905101c0608544204980c2d5840c070403040d45160700c500521000e043c0102c00540b1b0280c0707048000030300b42c80700e60082410301026203c0100140c00c0100180b04425030074150302e07000039080e0b5002c07400c003954103000361143c000039058564a28040c907001046a11a481c800c1d80350511000941d04c071580c8150888807071540410300c15 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 491099694 1250 491098444 491098463
    0x170108030f030106050d091e02090f06030a080703050909010b043f06090203070323030304020f092a040609050301090b0703090510050118050a0902010206010501200105090703 77
    0x94041000001d9030114031094407080c1c03450f460000c0035036890340b001d0755038092191100c04076804581c2c0c1c101d0417030400101100c45000e403c507900c1006000701c0010300109041174104180245628001620200aa80600119541c2c00c040c1001d40c0e039400fa006d8a541e000302050000709544c00d4410103041140c404041e0060703a11010b0410001e82c191043d00740400181c900d000301c0305007044100c010742c4036020300c0d800500c2c0711154010a0034003066400070349104048142e252040300c0d444410243c8800c14901941c210704240e40000d840c08900c071078151145142c4408661250140c10400d06403071a4000c01550320307a1294001102500706200300b00115919030000100c50606004094559501c6422407078180d0302c1c2442507000745103400302030311240b08205001405100a00c5071394003030140303004c0d400c506491901103101a07071401040c40010703030f00700508000180d03000286181502d0702400c04855400110110a40500001c02074113519030a040030f1140200000c100c1000b641c0c003c840c0c1c20f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 491100944 1250 491099694 491099699
    0x2503060e01141909080c0303060f010c031e09080118120507020a0902030a0b0d080903011b0f030b04020c030d0b09070e090f090c0d0303050f0f090304050409021503071701 75
    0x190300b00d40e01688101c01c0000107000141d1982e002004005403076aa040000801c008541c550b042070f40c0080c13244243c586d10001c14840d0900e401049003030000c0091803d6145d460450307034002c0040194000b4020345102036200745032414000c10b02c2c04080c15911000f04040800c1104581d0f0003101c018040d9038140d01210341c100070502c2403089500040e0040c00070112146030484101c02903100800b1948074551f501c0710040155500a0f01c4240c0c01c2c0030340d40e800e444030440020103086138a501c611030980c50701d407090b40e5445c070381010700144c4e04480c6007000207a03c0044004240640f0880c842c0071154000001c5843e6481c60310f9014464491b400e541911703040e5a203213015104081d000c803040380d21a518400084031000041d030b200d6440350a01080e11082207010003c51030340034103440c040700825100c0f030410849410307641e409507004c20004407510680c1800c500190312445a8003465010751b480d80c16840542d1035005154115140122407941e40740790020004201154410b50b1045451190f03000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 491102194 1250 491100944 491100971
    0x703170d0c050f1b1c08010f081f090f140709050f010f0b0a030212040c05030c19090c020703020604090e0f0a0c0e0a140108010203180304031211250306 67
    0x2e4492040d4920381c0f0324507114410a00e2603250802002000c0584600c10842c0012107000048080c0d40ca21a01c0e0310740194181440d00001c540c82e9004036849a000303880c540035444030380101e5141030b41149000596802c2c1402c0c1400404a000c034003038034545582c8da0b0340d40d01c1c4c0000607900f000c840744001c04205584035140d030b14020800c20712961241e8100d08406010121040005188003c0d0030709005250812480480420110403038045d1007510f0201e0042143d401e05001a000440c0b04a50441240c900b80d030f030309041418540a805501c6580b040c45041d4a8001c12808000c0c45e0000c2001d601d8036030340d1082d803028017104e1392262114021402d4215000c24001032040686070b0000c198824642044550004028010300088149455030003d0003264102c41d8503d0107080c9079000540d607813401109120281c0c99590200d0300302e40c4204010000f0803204084580c04130400d141a10001500401c005c1c54208400885c9400c115130b0002e0803a5510203404480440744035200502141150400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 491103444 1250 491102194 491102197
    0x8161221060315020318010908040f140117060319050109030306051909020d1107030804230c0402030c190f0906030c0219050f15010302181603020c0703170d0c05 71
    0x2000f040b08001860008043c441c0d0740140d540070000f40074a240040201d1641800d50b6200041610f00325000101409403072000b039400c03800703041c17070f640c21480084406000912544015509800308420a00400c0150780c040c4961740b00c039010300101141c981c2850518500a00c0b507074004402281c40c0000c001110f082031450b209100c032200009049441c681050000079500010300c400c581d0b5503940c211010f100250001c1d001040c0241e8030241c0910b00b61402101c09894420180010003031142c0344c00325100d000901040d9038809540141c1c880d181c1c070501040354007840859a003074400707000c082c0200e2540310749851464822079135070000413a0358001c00d400300c40b00c5c50300c2580140c0042d15070500481c68001e01540c1c892142089a004243e415429400d0014600502ca1f6204441c8010001d5107054000c02c018820400c0c1c1101c4a8184003d2601291011400c19024150046507002c083d0001f802f01400070b40c4c0212055002c81080700d07051000d90b1241c2c4010b11081e107030004841e4414880c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 491104694 1250 491103444 491103449
    0x30a0b011106040605040204110a050d1a0d06090204020409062912061c020406090b030c03070e01121104060b0307080a0b01020d122003091b0a030816122106 69
    0x180c4243d0311142c8070100642801807050780c000780c40f050110880715440000b403800c0b104641d640760f165440d0000c0003054810840511070041d6000b042900c0d0f56545c24412090f1a40c00303031001a850040b8030116020740a56072200d0681071a00c4800906000e032080149020091180360743d803002c1100d0f40514903805400070340200f001e1440d00050081c103080c060340007601d40b0f4011100b03c071101d03540040c05507000d5805c0f50090540b160845602400e0030481280d107180e0071000b8107802814164244016041442141d090441c82d10341c00c0240310451098046681029006108036a2945c3c11417526900542c0c0443c000740180c0c0000e145e0640c184100b2140c41130590140203144003128045440812200c0c84411742965950900e00b8440c03070310b4524071661040030f03a107a268940140218144000610f5007811044d11401c00640c1c2d0780c4000c0308c5010340e40e1260b011519034040c08035549804c0448940101031840004003d00c20507044030101d000003a8641c1e0180c00f414030519041c0c26139040c0d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 491105944 1250 491104694 491104727
    0x1e0d0b090f010b0304080c0c040e1006060c080304030f0c1704030209070c02240c0601080106030b060111120315030a0606030b090a03020c091503160302031507121d030a0302030a0b01 80
    0x10b04c0890005200c0700000c0c41350040020032a0020303038001d800202102d941c039151540d240d1040a51900201ca0b5005540003865a414180603818081c0c948910502c001400101000010511040303220f02400e210402103030801040c070060203030601e00788656030050009a2091083da0009010640301e6000c04007110b9014190401c0403014004003441c03c05108090519080f0602034014070720020001c0314020180760b07001007000c510703505000103030b4940941001e0420000c0034404590a6000134185940b42d52b24032203a689070f0f503001000714411000c01980780c0c54014140400c0c284040c036082641564000c3e0b59021094030380e0000580d07240341654000700580c00030030100e516458240b18040d070011420800301c842542c1e083c00203042100700440c001404d942e1202c00c2c415400c0030002034806080541c4182c1c031030b003080c8030040d001085600300b136007000340c860350003031500845850702032171180c000000c8a48404000070007074080d4008036038070303c40c1902d804540f51403584940d01194901c0a40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 491107194 1250 491105944 491105947
    0x604110901031e090b060a0b190c170a030e07090b0109030b100f08100c0302070b0423010507020109030e04050106200c060714010b0103060308030c1e0d0b090f010b 72
    0x50401580545100181060038440840055403480100d001c0c1c009a00d2290840713203010324014042018061280e0040c658145089c8010740c0c200c06804100f84100c019410600d000424503d421601e48500d0344c1c20105125021070041c0b507860b0103400585d0061030f01015208007a446054802c1102c00200e1600c0c0052240c40c1e003000130440e8045041d820000003030b5010502d5445800740722140c4240e40c03000416500c2001343c0b1080c9119440f4510100c0003c3c6810b610303042c0c2e02d4039074003103c5001920180c043c0301c090309000d10101500e844003185c0c01081009001a143c050f2020b4020440d515060300440c120000354171540c6028820700c1c1c16240c01e0788801c3e001c4490303210600d03819440e50b90441c4252203082c95680c610b42e6000040c0031007038410b001d45050304442d809000e00350368003c2003041c1818140101403000810078070a807940019204451500e030a580a2800580d10915070300303410903400010144101300c52500700e0b49491806444c0309002ea29404120a01c81009128031480c2280 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 491108444 1250 491107194 491107207
    0x4020405090a0503180402040f080d1403060a06051b011a0a080604080a0f05040306020403050d030f1a01051305120a170c03090f060d050709030507080304180b0418050312060411 78
    0x3c424405100030103001c6d10040c14144c8501c0c0691009407103401c1f11032950320008800c20728580c007404805104410303840007415800d214000c100411000d010702c0c0140107006c078402c00c69039020612100b90b44164802441642051016101d82560740071040340909240743c00400c41a0340007888030701499000241910748141074a0844241c14601c4013441000810071000001c140540050800382d8066006007150460061014048840e41c840700045141003500b07609861520907035400e4254001c0c24056030343e840c50203a451040755183c0182d40d011025109040004c3c0002a080410303620803540c0340c00c8031007000201446030141c030865541c19402000301c0f50650174440000343c02c03500094540c0c1e0802240d550118242e50040300c10728000358080100f0414040700700002d0000300913480c050740c6800d082100c5401741621050b140b2407010b071580307620101c60b02c446d48454180d0500c0401010009201d1034203640381d62001005548011004011400c1440c00c1d10800c7d0710303150f050354100d16041b0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 491109694 1250 491108444 491108467
    0xe100509040219091a16020616060f1a010f0e060408010f050a0f0605091513020307030e151e04050c030102030412110705100c060e0f0d09090b0603011a0f07080304020405090a0503 79
    0xd106c007a040340c01010900c5035030000d20002d4240315520344104804201215070710034210031516540d40e0b002000300a120001000c2c1d0b00050070a00c2d0030217916102c10315540c024042405445264007982d4150b180c801810148403ca60115004242d0003005010030300307818562030140c90207030080c00c1c0d110705648042600c00700d00f00300032011000058018418205035801140c2203800454210000c00c0d00c400c16418245001d0124540000581400000900b0a2000c90300684010640a42d408900c1c5000c20300f03200c000c0221880014009001755501c0c030701884e1000f44031020220704c0c03002c1209280125260380c40418240e05565001d099006110207040c070407255069529000c3e14095601c4604842481040c84a1f200c8401820004c01c00e59801c1d020050182505901c540c0003645090b81c08495592280116811243d6079407180a80d00c50b820886855481480404481c8820004a100400c01c60a024510490080f2020442646c1c0c120120746c03903024200c1c0041c4582c104010000392034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 491110944 1250 491109694 491109727
    0xb090604171501030c0e090d08190207020301052d070c060f020d05280212040f051507030506040e061302061803121305010c030e100509040219091a 65
    0x9059000032107402c0d4401ca011010402c000ba0403d070340860010354144007801c040c260190b04802484010442d0440c41c1400820035100600180280600c2117840042c20029406440e00702d03030010000c0103541040d440c404d540141852140020300c00e40104024800e00c0c003075a50f0b10a48060301e8520259410f039603a031004043c05104401c03195401e00c1030840710300c142d00c00c0034424180e4a0103140090b01d025186504400344922403000207004000b4142c2c070418954600e41c01681c048484c1d8003025041c507005003080e000c0203003c035010044504110501394181c101c107014040070b440070040001c2404c035440e00c40b4000c6604a00030341143c41542c0050804100928641480080240d2000844c40000b418082d1110310210600004034414442480e9002c4000060000f4205003101a60760350340a0302c130086001d442c51142c100810f02d0a0b00030700840072142c098500030021542c03150f9000c84044505094aa40c00024500303201c04550a03020b032020110541c40200c0305030620f00e000042c06103e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 491112194 1250 491110944 491110979
    0x5060123130801090b06041805070329070206150d0f0f05010e030c0c0301060510090b0a0e0d08120903031b0c0c0909060108060705040e0a18021c020102070b090604 72
    0x4881030001c0042c205000b8818005142d2198007020b00d642401400c000a031101020015062500740104d000018030000d540030451b640030500a80f045030084941110040c1009a50403021103a42000406507011a00d01e201d251f407800c0c80e8198001701d170203020112807500401031490348483c00c1d9001180601c4407104000d0b1050001048001500b9911402c64011980003005684190305200d0645421302a18014003c262810703000d108401c5801003005040c0d104040700d4882c0082d01081d603502c10615111f41d044003411610846007140b070411203a030310850803600c4904004002ca0080740000c400c0f680607440e010b41c0032203065513010740000c0fa9803000540041d41d00c02ca40e40e4150076110010b189104220143c00f070002980740012250822100034089001c006082006102c009107002c5c2864225440c04000200c0c103500c0844414007920514020750701154420398034240407481d80e91100014400e0f820744102c1c5655000035081780c000d2030029980034800380400c2c00b43d107654140d503141c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 491113444 1250 491112194 491112217
    0x92402030408040e1512100e01020901050318030403021c06051602030315030f07090914070e0f07030e0f0d0f0e030703060b0a12050a0b0619030b07140d060905060123 73
    0xb1709100e5000074030800f55500041100c0e004801400c40510142c0701e10018903001c0c800030341c5461400c10000700f00e0311005105030540304056a00a42407001003003545c02035940035143c48407202030380303660601480035540122642420301c0009085401c2d1071200c0400a550f0350000d500303607201e5603600da2085031004240c80d00362040b10002c006450302000044000c2c030030003400050b040b0250403e60740c00c03420042164281d51001c030080000510f01116168003850250031702030700340c6481404502500d20244411a5171050144103024014081910b1810318850313110603210750f01da00803e4070248a51405079a050300308400400108085070019040008002e1480000b582c550060070340000c6591010b030b6503a80b01c14800c07810060030405068001070704540c128440c1c1741140e03164200a0381400001c281c291860003080249000301100c5407c8202c02d101281c8070102c1018a800802c01d170321542544904201c0850400e50103428083c0246200c0103440031440303c040d200d07030100c1e44964002803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 491114694 1250 491113444 491113471
    0x11e0503060328031b05030703120e0307030f080717010902030709080604080403050601060503060904020d020402040b0a03020903073c0306060e06090109020f041206090204092402030408040e 84
    0x25046003180701c4030318241e4a00303145490f04003103003002080611000c070039161581500c005400422400800e407407a10b9850b01c1c00d11812000099018003270b0821f440f007600e480c0300c0130503402e040541041e40b424280c841a520300d9a240e0790400101c80d0517903800205119400c1c52001841482c1081c0c008507030000050a00d01003550b510500246003c1085030b003610007010115040c0700301b01d8240000e03801846136251050035801c01100182c01c1e541c0140c0020b02c1100000300143c00c40d1a0394040c0c1c2c00030300b0003040c0d003a10782d040f1139070140107503009100d040e02c40e000307508010480100c21010071184520140c048111645e101e0036807410015005940c04d03020010140010025200c0e0042c44003134400204a04420304021040c0b01701c002c1c042e003020303000380d00520a040f0585560000d45049441030884003103604100d0030070100030022018065007041c2010740c00c0051080e03050984001c4032402c0107029880015644020032400140c5000303002c0ca0b000c0108004a04680c02d0740c9400000114022 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 491115944 1250 491114694 491114713
    0x7260a05091c0506040507090c080c0a030b0604060309050601090e03070f110603010b040e0f0106020c0609060714030c06011401050a0305151002010b030d03091203020f04031704050f011e05030603 86
    0x201035040081001c4034213600200400c0104038090020800404420005000142141c07902901441000303013900a0402c010500780001c0b8030a802070901d8032805443c0b142c1d580d4907104014080c0481050941d154401c8000018841c03085208000d00d11380e40d00c1c0030b142030860994075031140b46940c900c151440d0141044002c0c00e660b80744020750080006210044e03440e403170030068070070b07a1230000e0011101600d180f0040200035004510100030f000f0468000e580d404600b070004d111400340030700c003500a00c4414040d4101c00c000000608a0600c03820840c0c81581c2d0b69442c0e808080419141c1600080c8103100d0400218003075003100390400d01c101500214550a0b10120700140c2d4484030820040c2c0d10b48140001d0750030140281082c11066180c14406985a07449403030a0141c00d0309500100355000541c00d0801506005850140d43e01c0100d080c0030b41c081c0400c004454120b40070b141e10861095012401d90360007451020400030300c003901d08180031203080e400d40b281d0300b004101e141c040c0140c5142 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 491117194 1250 491115944 491115979
    0x30224030a2304050d140d0524061e0703030e010e102007110a24020d03052203120914070e09100e01110a030207260a0509 54
    0x10310710072840d01c100050340003034503100b0302451400c0745026030500c5048420b010209001017001d0480c3c60090801603caa41030f540342c081184116904071030040d1034102070100701007480f603002480701a204051408480b01c0301c100321152140b6030303040c00c0c0c0303940007418000c40c00c0402000d424014000c0c10b00281d22010407440900f551140c041144c040e40000c5401d9803042c43c1481370310122040c010200c60714030110104c0c2e0314948103a00000d4a40b0700454042c1c001c0303550b20013951000c3c02c5084a0464806600f0541c03100c42c09200c14840c0160113010000d4000078820701c00c41c1d21030106217034220f1040810590b01e8231041c607a44001c0c0c0c1080681d013a050303000d0849018507ca5148581035a0b04010a80c1d12140c0c00c0041c030350040070740030340054148110450001103a4464181c02500081d1b01030102c54118010881c0c50324600c806640860800c0e03065030158007030312105018502c0142c05650020a09450300665002c041100c01d06000c00c0002c18443c03000b80c540d80c240079085082c43c40e070b1100d0303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 491118444 1250 491117194 491117197
    0x3030b0303071a0406050a0b030a0204090f080403050a03030b030a0c0308030a0603141b09070206070f12060b0301180608060c0a0e04050c0919030507050108190c0e030c0118030224 79
    0x70800f22078000d42400100312040c890382e648101c2c00001003007050780410010782c651800400c081d10413900e9407040707020f014005d480c0c5030007035074410000796456980f80f404545030059608182c0200380303081c00d1034006041c0440c207a0585680704005088003800d40d81c590009420282030644426135525001c40000c040880907d404040d140040040c110b580c0b0309208100121440d050203950240d041c089100e0300000c01c01c2d0420060308150741a8082030104888a000c4c90000c803440c1e42c1002000141030000b44019030607504101d030403940304140c000c42e20041e01c00f980f2400082c0d80c4101c0018a0702c032420406003211403458940880c00041c0000001c003920410b40d0713031400d00b550001d1090181d190801c2c6191400c4070207141211083d1070341d110340d5101d00840c0b281c103061182600c00100e03089040c40d20b5030040c03121140100280d100842d0020507003c284400140a032248a101c0340c51907020703020b429034004c403008651080074116070034030400308550256003011802c043c00d5500031048600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 491119694 1250 491118444 491118473
    0x50a051905040906140a26150615031e090304090f0506010806120c010311190f08070203071e03020f030d0510091a010804080c010911030d05130303030b030307 70
    0x141d4150321182030aa02000315480c1ea80400580419610303c803001d51110190f400031aa03010b4141d0002400c02d0301c000304950b4003141000d02c5800b0380701150501c80c580e0250b0500802040d900301c154030313503228200911440305136100b800580055400c61035510000d01210f610405440503207060039034800c4441c0503199840b1030441c5598649080012550703008440590001c0222402c100d038080700445992a40d01503001740341015282c03099000568200030448152223900081c0c5103508080d65802014200140d546d04006503440c004158030764400011748014941124036101000c2080f2401004040380c030394106c040d8020f1a200052034407092001d01485803106001041078500140c20034011066504020320951502140b08152400d800c0304011076002030030681015100c600740310880380a0b5884111107982814044410894181d004030040e43c03051f0300321009108410700a80d40341c00f4080d5908418440184200301187c801c1c0c00a02d5202005800e5900d03080035a2222613500a00e030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 491120944 1250 491119694 491119697
    0xc060c030c0c033f0705011b08060a0e09070f0803120a1e021b030c0705091503190c18020a110106060906030b0609030105041113110307050a0519 64
    0x104032180d4110040c8806514520210007130309001224001c4508030007030301040d849035581c1d0071940c43d0060007629000c0781c42d02c804608007900e80000d0f1400e517010308204552082c1c4240c602091500d8203016074049070082e400140080320560410f94030700002c160041c81025a44100c250000d11090030407200005001c0740380255540b024035042d40c0998060242002c0c1e10103140414000a4000b60719060301c58981850003d82d40310966001200d03540c0c145044a891404001102c2c41d9034140060a502282d13001d6a0810301592900345c8180404504060aa0990001083e046a90141c1e402001c2882d109074a4522450340b51000d00c0d99280202100d500aa98000303800c00b0314070f070070080148403040c8200003030280a04111004058244511a0006041d19401c4219081d6521010345c0c40c290005002085645410f040c80690600103a40030b80c041d0540e115011030240c0c55001d8200481d40f100c0d2500c0c515200c2400032079150348500141010040c040c400a82040c0d20442c0e62400c44042c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 491122194 1250 491120944 491120947
    0x80d06060206090303040c0b1b0715022407110a0f0b0121050706050309070b030c031f12020f06041e050306072a020613032f031504050c060c03 63
    0x18030001030300c0c0c54000b5080c24507a51050007000002850030300020203640d004a01540c03154800007050940c0c6050021500041c02040b034041138140701110191a0b42015608588551451002d003048143c07285032103503141d05c944000616214052403003280c1d201c0348401155040da2141d141d016032114601d00894210500c8001080500c000240203030000b65095103202154846035105076650030b00b4403409062000c04000a400d10209101d61401094070941c83c0b90b0740e01d081e284050199200310b4200c0b51000d0710380488481e10900f001c58000343d0350307100004824130405400f0484903003103220703038a03034010010000811026603800c098453300000c1d01d018514175040600309420300030b000301010b00f040b20342c03600c000d06441c010a000c443e45607a04e03039402032058980007141040c4a001003c0444265108000013017102608541c0c0c03d07070121802c50b0300a80124800001e0902e001441158990702224020f144500450100740e04284100d0031a4a42d403000008174200d9000400d58403a160070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 491123444 1250 491122194 491122199
    0x705090c1c0c082203180902130503070f06090b2503080612160b0d0e011b11030301030f06150f060c0203010b090708040b0901110409020406030b040504150c030207080d06 75
    0x7008443c3d44c2e00080c3c40e4072003110003003500b0031440c58000c2051010b0200300d02407002c1000c9624048000001e4101104290b5031840c641003030500140d114424903000e881100300001300d450580045070241c070501d55034030384c540f440d000001c4801e8000502d0b11242d030100c460000301d800d0107010484a154402d45541c10940360080070803071000018041c06043c4e40000303074110b2120032040d11801c1507840d090320542d00d844524000c3c100500c108407800340c0035840d01803c035600403088210075007048280c3d5200c4c061300581c2022691070b030000307207c003c0040c461f03d0700800014000d0780000e0070400b150280101c810350348180d1041c1d284030b281e0003c00032840741400c1c241503050038010011102004da8039049071b42084a4024000340c030040020b4802d840c04d20204104800079004103540c00c0c1d45109190725a13441d20042c200a501902ca00c2d000709161680000711402c3c68081e0038070980e002298000c59079515003401c4081d00e000c220800030540d00300000e200084201c00941070401e84a4030008180e0b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 491124694 1250 491123444 491123447
    0x106050a0905032e0902150c0a06140402030d020a15021b301309052d010509011502100c05070204060b0706051b0703050703030b091303020705040207050705090c1c0c 73
    0x20b00d603246525051708040444000d03807a03803042d0280400c040c0d1034144c4d454104074803030340c200450032800802d12403d28128a49111110413064081c1f0300031001d455080c0325000b416a83d820051400921000029551031146c00b81540500200d50071520440c252440d403141c5d140c20a685c900e801241030b045001161032002803281e0340e2004181c0c03a4a1603141c480c0c0b50000c41c00306015803003070b0912540c6074000100702d1004001c902943c9007000d20ba81700d69901603001e12003e4031003409864050803c06e4000111074100017043c00881a20380c01a0001011505440d800b40401d10307192414003108000e80001030701c85110b00b00c001d19140c1841c81c1c491616150241c19983d014040e20400700c02d4110f00e020748104a03048175039a41c0d2604041d40d5820480c9026406804414500f40d40f058042c0d003007001110b00412580105c902c29030030788590540382c0c0e08200403070240385d1015102d9030102e80c1c10b1220303040071040e864022800201c0c1c5420041c181001c80aa008100003a00505803103914184419 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 491125944 1250 491124694 491124763
    0x209070801060305221101090b040602060f06010f20030c0f011b08190e01110d050a0e0106080a0204110d05090a0b01050f0609090a141005031b03060106050a090503 72
    0x2214805000e043d4031a0991503020f140120014000c0c50912191002d0380e8020582c080c0209a01842244c660b4be40d040302949611080755a41d01c0004043d00007111503102e524500320001c40c585450842c1c40385c40c800d5050890f00c0003044204ca110030031410302110403c0007030300680c0c01c20100100c0c10341d40030307008140d007030310800c2c8804c045c03044940502011217403e40807d0000c00d085400003440c180005034a5002d443c50740c10f100002c0c0d100183c11004900e10381c01240c895003400302d0610000c07084a42d4542256000d03c078000544d000120840014a080d400035030b010405642c065041601500c0c1e00011510b00755020304155125041d00001c1088941c9000c0c01018210b401001000c00a400306030309118000400d4400c0d04140c0c00a0000962070703120302c6044500f030b02c007007242d803a14031402c4594401c1401214801e201d0700507a226400c00451480300f0104024000d81111f0f4603000007503031300d078020002600500400310380200f1107843c100f00149241c99004c6040c23402041c0c041c5400c580 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 491127194 1250 491125944 491125951
    0xa06170106080c0d0501142d060a060e0402040e010b04031403030601050706180f1104060e160806031203130b01060806010c0210050f0309151815040f0209070801060305 74
    0x5641040c204100456000c1a40c900c1c0c01801d0744c3c40014084030f894081e00601e0150307041c8103000940710910002c06030301074684003003c441e0750007003140e8a8400500d90004004881045d8014404182403020500c29141c030801c0500c050005400c2a071680280c9032200801d8008590030305003c078040007485180310000341c8583d4040080c500d07605003080020124803d5050142c20705407111043c0401c42d07510f4520306e0b070141c3c00c0130302c103201c0d0406440d2500803440103104151140381881c03000f01d994180311398254050919443d129188030b40e90441911740150007800c00d07a06000382c03001c1445c61048bd0006500c6100201d4000c1c11040042c600b00d0b24070074040e001601002100400c004c1d00b0398100c000071180940403648440741c0c40104d14100d40300d229400307900c2d04c440800300501014090025006000d041c00c1100c90115a8a100c0390407041c0076852100d803980e030320204001d84148060000250801c7c021040700f95840d4117a0003223203a200c4290b401a0004802000400071980d1510a8540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 491128444 1250 491127194 491127239
    0x50601080112020607210e0103060803160212070b030103030305160f02061f0503030c01021e0f16030e04020f09010306060509060d020313170d200d020706140a06 71
    0x3554100302c20503185401107440280280700014094040c00300007440300fa45400e1840b1124005549507400401c03056802c0d80741c60205c0d041a40c00f055003034004c000c0c0c3d00483d00c05660380010003090340030407401d488400e1000380701c0c1c0200c0b2404189601d03240c00960103907000c0e8801051505041244403021076030401401c01b0840b00b440e000010342d45c0841c1c420b410442c1d1030300d10040015a6480f04602c0550380d40100c0e4540300014420242c0361064001c0c0142c1c8846460066203642c081200c882e540c07180100072069294104100049440c04580c09191640a03182c041e50b11156a004581240c3c04043c41007600400400e41c80b01d9580d03d405410060941482d0003030504965401140280c0030790410403600f5038001c80007420041d01c00964480d12034001c095651401c44c640b20000b581e40c410440d00708150b080c42c11007401e0341c890394072051810102031000c1d40790004590541000b500658401c44080d41c441d502400f0407401035810b80d0249020000c0006d44901c2d10032540e2000384840107024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 491129694 1250 491128444 491128457
    0x402071b0b040e07110c0901060905030610060e1513060306050f0a061d010c0c09020c150106050a0309050c1509040f1401090e070308030a05150103090b0114010c06021c050601 77
    0x114000d03c0d07002e4960410345500f40060480400b061075400c1003808046107401156a000016030142e10101e507000715a410303002c0d03a190780c8952038030150740c04441c0603201c049120f8200d00c0c5028246050303032060285200782c0b4030b400c06040310198018000e05a002500113622184144001e16100003262800c0c2000c464408140c0e01c0e050f4094100524140365400c044082c001312041640100c505c90f0b401c0c0d41c8880c0003800c2c03a8461640c3e900a421003001203480d480742c908504c5e102c00a0285241c10f071042c64403814181518001c04501500401c402100c42d03005000e804540c60b105d280d0b4034204d18078420109030312030200e81c09004c00c440244181e948943c0c01c20617140600940440e4160541d90f07030540210394400d550044500d80141c03a440100034240000800071507011a07440640120b90701c50703840e52080040001103058442c00791002d000498640010400c040c001500c80d40480418140301d8086d40807074032a80200d0300000c0104411000c812004100d940d0766110300c40d8016824240b81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 491130944 1250 491129694 491129699
    0x91e01140a060e0906011817030703020c09040b1b30070504030b010e060d050d090e3d1508060405060d0b070e04020702040606030c080601091503050402040b0402071b0b04 75
    0x618890809006541844507d045866601c2d010310501000b0f01044c5201b082007840e9038840035580e5102d41c1c000e80040c000c0d0340040000b032070900c4815010300e400030142001030302d4040304d0425018a03400d00401d00703a41040303070b001b46c1d44101c40c10a005694803408442c1052244020303820300c000c004d14820030001c040005000292451040703605452402c000c1c02e15a0780c80c000441c0e65003525000c0501988103031502031902c580e010800303a060740d1a4a04c800a0b58690490303c501034110761070100002c1066120b8455035208894a2041c2c201c1280e810515407a1340e0802d503003441c00410940400521003900f000020b04003801095004001502c2913415400c03961a8021000406003803101004440c050400a40d0354a0b015035041d103800502c1040030316074800016008107c030541c01c9022540d404000781096006441040c00c07548511151401020a41c41c01c0b0001d00c070040040b64442d60390a41121240c88920203003460394481c142003d11304840050300304036401e03030b070344030b20140070040209 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 491132194 1250 491130944 491130949
    0xd020706200f1608010b0406030b0c0a091e0e0903040302030a030f030f020f030a0b0111250b03040305041e27090b04080a0e01030b0f091e01140a060e 66
    0x805403492503508581401d20740001c0d1075050480038400031205129100d2681030000145510b4000c880048000700b02408120050005a500910028051905c20f00004803070310707500030003418203454624040071100c0e198138940e00041000148501d0048402109210421059031070a40020700c1c8001107042c649194006561258a003400404000c0b03821880c0207401e010b50051805038044010941d00c40b00030041d80394480d001214080e04450510016600a50080c04265a024048009040b0031100780c080507807a9032120b0803035103c0140c804400903044251001640c0220310a9a48607035a61800110342c0313409a5040300d2483c00720021030100148200b149843c86251003403d01061030429012903040100103010001e041640600e0401c01040311600041819580d5519502d207020005401102140d0181c804103400000c8500c0c2c0848a18210010903402a520461101c0c10402c8603507142e03419900b039115914980c0d1105020a00380f505014000c003500c0e00e460000207183d4000c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 491133444 1250 491132194 491132207
    0xa12020103020f0c010203070e150304021807050705030309070603050108070b070b061216031211070e180d030507080c12150613032010140c1e0c030d020706 69
    0x38107250b8002440e11000c0c0040c4207461a882022000f1500c91518610103001d040c0281e0f030382d030b1207045d00490501c2c0880c0c50500752402580c005e000d41da04031100f205402006200a45090b051003000c1c842900025010030045218000a102509141d4034210f0050709850301a041404940c00c80c0c041408100d04850a54407015000b60058940d602c5440c0412207061500300d00350141e000700b00f07090300c20008000041c012079201c1e0b01441c40c9154010412500c140c28503800205542182038200300d0464081000c1e50041c0c0140071524480700d81520913031416009461b15408251240c2c2084070b181d8224070740c2c60f440102d11060514092590040140d030038401024441c5170501c2c41d0071140e00351174900a03600c1c0d401100742c00020440d101d0400c40c0201e44801d4200f1151582246150303120f0402007a0b030409980240c4465040180f0f400d200012030f0042c800f034190a1180c200f03084041940c0800d007550140f40b80001d0318045040c0c1c2e0502d0b0401042401143c1990300c02c2804105460b030000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 491134694 1250 491133444 491133479
    0xb060405070815045703091104380d02010c0c0308030a1512020901052e030c080a0b010212130f0e090f0d0e06091207060e040b0a 57
    0x21000c0c0c44101c5128000b60041000840451721010110303014000c1d4803a0b407600030b6450345841c1140f4254440c3d003880150400e212050340c9100441c4d01c0081040f2030107500810840c0c1c1c0b10741a00c5420034090400700703040b035810001d080703081d41d8401903000c129040c80c0a074000c00000c016050f507064048401051404a440314001e042202800ca62000d001007034404e18041e6503c414030395964188140c800000d01707c0301c0c0b24041c80d03681030400000ea050224008808540d405014400c140c0e280c00d007000400d03007001805100400c041c0c04c4410400f07001550345d0342413103840c0d10b001622900c602e00c010070040b001002ca034202c91a14040f6802e0f03030380000305a80900c42010300550744580d90084c0820a41d800d0388648014444003d000c00c1d6030802c1c9501c248a030006400301c4107001d07190702900360345140300c2180c90046106502500c02505004004207420750000c1d2000c1c811a400c01e0765145070000c2c0390300420010f1b42c124003a00162525005034000e9010495440302e0043c1055000c2c100e403145903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 491135944 1250 491134694 491134711
    0x1318090803040b0705070f050106170604050a03030e0304150801180510090b040b180601170103170a0311030a1409010605010905060a090509040b07090b0a0503160e0d0309030b0604050708 82
    0x8034006580f0170310030411294090340c452100626201246050f44c0a880c1c4d40c05440a8100111442030b0007001c001215845550010b00600c08100c403602c00f42c00400e1020511050b90104100200d03c0c03400e110200303640710205070b40310303c0c10f585000c02c0c0072030300046e116508044606050900160007009410501507600b140c80028010340d9000018000300349080c00d954010f900d902c80c00f036441d20b0f2800c0b0240308010a80703540e4006541004000c00e1080c09003c000d01d54541d0000c4d140c0e0010742c20000d08550490750400048220003e0515607503900100c51400f10f80f0b0f1078444032024a503490701101d801c41e0707804000340803690034800040d009036442d01689000d040301190b0008594803030304105009010281c6409042d00b403034241010f84400446800b00451004900003401c0e1a4600845422003181d1f80e0382811510340c244000c0b40080c2c0344480c04104249030700d228141d61385480030084140d100b070f03c2e1441c18030301c1c502e04401c50440052525101e9843d24080000075a0002c1c092580020305 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 491137194 1250 491135944 491135963
    0x2b05031e060105210a1109061e0405090a0209030c06040510031e1103090115060f1112190908030a0203030c0309070909081209010501151112131809080304 68
    0x1ca400403101ca0003021807429016114559075800ca90211540131300410107514140b26000e400141e035280c1d4495103e1341074002c80c0400c01520428240d03880f1000c9141781044443c03a050760345000442c000800c4e503070395580c0e680c002080070003440c082140b080c84140640b006402c0910f0400001d4118001085407001e05031036013034026201d04014209028120446001c001a020481451685400441b038103101580b9150700b000b492240c00340702c2d01c01c440281d990344410541c5240100c0307200381420440b81040c8600848480c0060400000e821113520720074444200082000c00205201c505a1181655400c10040000000e81c0402242d50005c1601480c079a00c0d00c0c2d01c0724040c074060495011007002032038100007030300b04203282c1c0090641198044084055840c3c250845e400c070740d401e1088811a00b01003883c60780440c050b80f5000400c40c405026110341075861140002540e00ca803104c0c002c0784a84000c18405004485a60850190b00c20b0301040f069109640f0156244400340025011511 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 491138444 1250 491137194 491137201
    0x1080a0c05130303020304051306120204180209040506070905061e0702060c0303010e070314070c02010f05070f080c012a05070c0801021b061815090f2b05031e 70
    0x3a01c01c640c0108520440e2051450756414000d4480e041401034074418024540e403407142c1c0425014a20580310b0356404c01b50f00344415804c0100401c0c0c404134140d1801c1404cd0400302581e02e8490042c0700d58000c4010b0030a031720300304100910001503a08981e01c00c1205001144070b0324482e07911903081e403c0420b034080c0d0359015400050000c0c0aa0764140d005480f0000002c10511303c0803135500d000f004261010301840e200480d50302d903050701c203c0c0c0400008a000319000007543c841c0b003855003000603d0509515091030342c3c49000340510030600554030380b1000a00314181032070034407425501c903146a03a2080c0d200203c5000120752080c117480303c0e040040100740703142801002d40d031340c200414101c8021591010030425106402c052050003420500a400c00603111045a038011840c015030722000d800c802d0382d0341c00c004824800107041c00e0b28901c9034008041e0000b10070403c1c242560a8920b9020307080303542c2942c076214501a42402c100b0040244240400ca00c0c281892403086d50440c03445089954 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 491139694 1250 491138444 491138447
    0x7200307120c0501080109020a1707030e01020408010b09070206010510050309010f020c060a0f0b0310020706090c06051909030b0103290703150e0c0924270108040201080a0c 76
    0x222a8001d80c03400100440e95004020034000302c08100c420a0305c90b560141c1e0381d409018228014400c0714008120244014065400303001000740d8400c140303003030014107000c01a020900320b030442c0e00501c100384c0d0760792806c1c542c914140a01d2580300400e40300500d050740c1040c01280616120b940a8000e04c01c0200c04100c1682e020b411103074081d00319081c2103454034100c000040d59444103480e05031041e07240c8031051030502d0700b85c0164011172602030028410404e002001d10001d60200000703503000350380c1d4844800084c50a02203040280321998030180c813010028403203582e0200100c06030061104100e010000038591000b44c0d411079402042464224200207403a0300d0005261003400d40f54010340d0100107031540c06500c405c082c40d050603210720607141c50b4103440700030340d00a96050003914018856800140340202542201c2460080031800035a40c0c840c400b50f080d0480412420044554034064508001d05403910f20003000c01d21f0001c60074107007500060f12103100544900b40d407503281c400355043d05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 491140944 1250 491139694 491139703
    0x30c071e0b040b25020d0e0a120f20100807110703050d17060d12050d091a160c08030901110f0301030c590403020105060402072003 58
    0x140c01041d40324961030186400c9090800031a50001d4941ca00078103509850107081c100001e058040d0000c080700c5038444c8007940d000c080c80c4840360b031211510a0100e81c0d01005054403c8283c402c0f820148540344501c1c0400c2c1000340f81c490800c480200d01240b416990701c0c0300c214940102141040b807038039240d9800840720070014180310403407403081103000003c215001804d2080d64100d079445d18008a40f4800601110f501581c9140d4840d016000807000b03e07040384210502900b1030b0420034a0a14004222801d5520062040d1800c00c41101c1c030800010030540c842d6402880c0c8075030740e40d0501050f130300079015488078500a030800201000203500c00e6825400b881c10742c2c0c0b0050100e80c803030295a01d03140c40d030703402400704545907901c0080c00908444401c088040c400c56a05024800040008030f40c110304251240c505850090100548020001070410b1000c4420804140c040307031070b00d4200a8207440f40940702c103001e9481040041e02240d0110035498008080500c6201c9000e201e00019150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 491142194 1250 491140944 491141003
    0x40302030d0c11060c151e090705041803020a0b0402030705040f091a010b3007020f060c0a2010230603031e090103110d020a0311030c07 60
    0x188501e00001071803079003102e280680c951156101000c01104403050202c140582022821240e0080b081b4940300394020203100e90060202c80706121400300b0300110361900c102500e41071000d4001010920450401e030146405040c040101d00441c4009550001d54a01c1c0042c8050003480a44021400b156024800074004020080c13003800705402ca4041d5034000d021544049951140642d07642055030a400c4030141240d0310103010300e0400c041c02a0100402e6509810004ca01030050480b0004140055a0030700540b9213034003d1260a80401516203818409042d84800c2c07402400740e001400c1d400b4000384400d4003c010f40440c80340c0494030382c500d0704040b034211604450400007240c4404414a062840c0b40640055459046d2959002c2c1a100d00c9541c008040308240702207120f0344480b00c000205001c130303010f240008000d10701d90740707804445d0400b20029a10503000901c031617920368980070308110f0a468841d41495800e00c401610f056105207200140f02d404901c00560407440f01c1c2424401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 491143444 1250 491142194 491142199
    0x50103051e100e09010605010f050c0c04060e04060c1103040510051306180e0103080a050702010c05160f0e0c16150504050102040f0e041a130f0818150d050a02040302 73
    0xc0d500381445094200c000b54066401c2c0d4901c02c0300001e0b44140140114811100182c450b0034002030400011200750b404003a681c2124030510050300d0450300c5511030b4030003c0c0704941a40701c2600306490604180c071a0203850301e04011081080300494003001c000c070340444104580307651210380080c906031410301400c101380c03000c10070300200000d01a07081022013041c8200c0c1c0740301c1a802c607290034441c880c0250a01018002d00c1d8140000400e042c0200d0041070018014102100c0d884210381c1c0e0140b8090b6158402181c0c880e4a8200f000225010213121001d0b02c5407a00d41c01c0c95140050845d5160b02502100300841c600b100c00e01c0d41802540240403010f20520002030180d403416060850103540148a0702c20010a40e241c000b6141c130300c886172680500d5120720a012040010640d0000702500642840320640f220104d140015051041d2030100ea849940c4160b214041840c600748014888500c15006421603080003450309484000c4546a81e50000001a1620384070203c00c000d0055400c000d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 491144694 1250 491143444 491143501
    0x10f03060b0c010e250909060e06041209150e041d030f0405030606040216020f060c240702030703020709270308100b0415050d0209030703140c011805010305 69
    0x90782c002040d00640c9402c0700507001c949280d00080d50381440303009007940c5e0000700c2e8913003081032050880c25001060301300e000d4071740402d1038403e00b96400e0409605031401c440a10003844011001d0380c100f0080001032420f010350804500002c0002f03405488191146d603c55a9207440400007aa8807140c0101e00032003400031642c41e100401c1440c2050f41c081c0c09154824410800041e8407842c1a000b00e0b0404100e0700148002c94034aa820b010900c80e100942c244d0154081c4004803811504101c039610065000b8400448109814045001081c0140080045400030810100440d0b000038a8200321015010001450044081500782841d0390150300c9090340c1c902c200007002c0c59400075095018504202911151558401c2d02030103502c40c506c190f589100b41c84012b8910315009074041d19841f030040354054900f95402c030001c1d05100b00c9810880300301d85007a44910758004100311411410310282460828900c3e18804d2111002480c1308143c100740e1224001062420050054070410031914001c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 491145944 1250 491144694 491144707
    0x60705120108191e0b13060e120318010908040b070b07020c10030b0102010603080c300301030215070c080607030e0307020a050415150503060112050f06010f03060b 72
    0x5006038444500c8084084003040085030340400031030380e2002c01c050890750641241c61075031303a005100d54401524124900074140303207002c01d410891481c0300d12003624044280c0510382c50b010003221340101000203c1e07840004e801050b6042201203c4c0c0149000d907000c003034210176510480c05098590342c010820344011a00080801001001d8500c0c0740c8141e00401c03403a03482d0f4004a90f2021048030342c81c0d100320020468505135009500c03d05221a040c4000318021b0340b2070711010065070003c00000010360201e012410704a041001510000f04c4d110360503000c0407202104440c0f24001800068030030f1460141e0008030054084c1140d03800703680203d0355200c665540000d42e4a616045825001080c10304d0703c20901e021021007124030f56507008000d400580d04000920004000c008201e01008106040110303a070399010722501294615a61a0383c0d0321310f4150001403100c0d500801489031942003005014203c00300b02c100681c0f0440a2030184840e85c421138044001d400b045c3d009864900001940 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 491147194 1250 491145944 491145947
    0x12070317070201030c11070501080c0c1b01110303130b0a0f0c0809060c0f03011a040305030d02071203050402090402010c0201050d0903081f060912050705121f0204080c061b0607 78
    0x41c04200303000740c030100502041c200043d1080c4610014801064000da0028816507000b5036025400c0b51011403603500302140c00c003c0c0e0b0f00c2d05140100784c40c040409840e041070150780c800b1074812400f0a01008d0760450400d90b030881c0e244403000400034810340400340041d0b840e00031503200e445440c1c48032002748000c1654400c0a004d035001511105403d000701800208461030310012901c11481210040d881c603842c1c2100d1001c008202904000d000c44100070010114100300007410220f00e03002d4005960360454600138082c043d80092030018541480300300805a652262000e6010740c0a00700920031256030310049803640f103032000500720f007490050b02d03c052580c4004214452000314240d00080300c0344800d075403054031141c420000010700ca50350034880019110400c3c00c245204008841d00e850311240020380d680c0708401c0c0708500364807101640b0309100645c00c21500359000c002e000c43ca400c1c10301c10346c00d4980ba5440541c90040200154600e45889040540b00b01a400b142c00e032400c0741010700c030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 491148444 1250 491147194 491147197
    0x1030f0c05090406090e0307081e041e05010918020304170d090c080a0f031121030916030305090103020a090e0103030305071106070215041b0801051b030c030612070317 74
    0x300c02d014520304000071034209200d03c21b4518171640040110b007070229580ea55a07181e40001c11102e60094a0080709540c0350084000c1c00c09080c0290100c040c041ea800700b9019501100d911450401421390010408400c1070020048611070701e038009a44c95845041002c106c100e4610070212441c400646031903c0c00c0036901540394680324000d6405103a81d9586e056580e80110907010b03044480341c510542c00030b07000d2686480402401410f035a40c61110a407000804a19002e8580301074100004000044e84180801d840030121150030700e10150940e00d00801c0d601441440c1814564000340141c48035001d12110401000008032480056840740340c010090907007a124400400c0781c51a1030b50ba00c605c00706081d0311640d80c42d802400d403000d08110500340810041c00c180e070144240301072407440340401d041c10000785c4144000800d8504008001030614071134a40ca0f4006181d051040c0600b0344003000850b90484012901c14001022052819090100c641d1005003041c81341ca2004015660100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 491149694 1250 491148444 491148457
    0x141606020d060801050c0909090715080f0106050a09030b1b0d0c021219030c0e0319141203060d0c080f0607090f060e041508010e030705010501060e0307120201030f0c05 74
    0x40741402010303078a102c450300340d0301e0030f4825181c2650284810061b03400c0815140e51b00ca00c0c40411280d081c3d5551403200c3c0018180341c100b50001340b414040190603140124618010507071841c0c03a515040c0701d600000c0030b4180354000200b9100000d030201d51142c120303807072220a242c0c0c000034180e82c5e208103e00345d030004d11400503c10007500980c8000306e0404819400c0c0d50101d280d100100249050b001000c4005084003030b801c1090000180704011152004c000a004050b540c0d0300f940c0303610034282440c011215100260000b030744d114015850202111030240c1c1c2d001041503483d40300724121072900c0300c42c00015400c046258820754036a0344d0f6212001842d075014555a888075044c4039250b00c2c1c4040c0944c070a0007040080345d601d9015443c2818140c0c800114600c00941350010aa15001000c4c00c1d034120303848002d09035202181c000240003086c41502d005040b1418a10100030386280820341310043d81c070840304202045400e51040da4000d8001c000304c0385000804000482d005080a00a80c1110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 491150944 1250 491149694 491149717
    0x2304060501050604050a0b07080732031918050909030a0e0a030b070806040b0603012709050a0b0a0917030103030e010c05071a0c011d06150105090114160602 69
    0x100001078241084003c1360103403903010304010460f81c104800a2440e520907003044614000801c0500c0100c0e0821034400d461740707900a403100c1000b00b8242d4100d00d0f003071381c07100307940c4190010000403602002948044c2c6000c85541401d14405107009081100a08940c0c05640c000302d00c0c00270840743d81c0012000342540200b80d25414544400d06040c00034030701617800700502e61074030f103800304403658000c039203040d07000c1c1c00208045640b852045c08194260001c0c3e03c0300305100c0c084c050f40d084113040804603000e22190000200000d80d100c1c1c642c981d40705804a000750a80c0000b81c0801c9038405243c011103060b540144c1c42d2030b2136622900c064080c40d402440180c0c00240c1c4e80502c003515611421130f0042aa4224000300300490070441e14800c048070030801c02035501c000300103608101000b030086103100c005044100a05c44820100141003a2009003200400c0c104014200401d130307004401c0d5100705c04286132200d07042e0f06444c83c2c501c02d072284184a03130414850160020401c189a0001c111500c0c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 491152194 1250 491150944 491150951
    0x90c0f02060112020102060f090c190f0504020f0f090d2109090c1d03030912060109050f07120209120a3009150203040e0a06091a031e01230406 63
    0x94441c0f080e04899440402401a0000c0000c1071a03035101515080d0481c3c01541902c03181c1800034005000e00c9140c99901500c1000b01e2810008280d414010000410703050302c0c1540380c0105d00d441c00743c252188844000702c0d040042460380c029250301990302e0000d64030500b4026a841d141001c14070103280800e022000480e11075010400b0381079401690030021064640d29a0344810075641c081120780c00031031940611091011407040c0d40d9801c18a8410036000c00a403030b0300d50505003410140c660040000e62441100d20900c0220741d4010101c06034043e40b91001602c400d02600040c00406100a00c1406445805071603014070203106d00019400300c0b0303440800e82480c440000181c900b0300c190002400b04000941c20004281c01c03120b0740300c642c1d00e10300c1900e1420340c8510307035a14003a506030740031174480d9a608000d011311031a901c6480030300c01c000c0d84d03100084079001d00045e40d1180b450f2840741d0000d04000c00032a0b10542500440e800103540d65000c0084680e0b0709a400c0000c1701124155115400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 491153444 1250 491152194 491152199
    0x801052418090a14011202061215220e0a0c0303050304030314180f06130b0a0603060203010806010303091a090d060906050c0a02010b04270312051303032004050f0a090c0f020601 78
    0x800750100c03039440d60140c08c450822440b400c1a403210f200c0149210113510403200191110f0b03449811034800c040100c064200c5605040e91020100c8a0381c245c69005030348210322880215855a0503076048070340c18a4019642d80d1b85141c03c90180c40c0c0c810762001c031003e80d0340502040d1000c0c0802c8603091001401110b1503030602e01d04440e1748010130356685184586002c0480049503100c2c0300f0b59880306c6460004548640d40e90780b4001203a1003680001099000348006000705640948000010311180c44140082d100c901c492240340e11445121600ca0907500444408100c0103411042146420030400c000c607242c10000401d41e98000c411a00041d407034001000c020740f401e031092500c0d0440c075658620403560185450074001d00e1801080d4240310b05c000758100542c0640c01071911924002843c0c0d5040d241901c3d02500f0f40713503140e01ea0706000d20b02c030480d1a0111030f0401a02d00300e510031600307505034580c1e01000c01c0c2413030000e40181e46440d0501032029031054011030041c18005007642100c0ad00d0b039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 491154694 1250 491153444 491153459
    0x240903090518040b06010c110306011205100510060f02010902100504050415080c100203130f1d240a05090a0e0d17040803061507030903030801052418090a1401 70
    0x26000c0303c0050200b80348030040303045035106400c4482c04510a1000000810031940000d01d071032001d030300041a82c0c8120011008000301032041514107844118240018207040d400d492a100250003004200131568000542852003508400740e03042d0080c0c01324018003004280204960f10038020140514101603001d0280320a003015441240c03405409040e83d2090001003008008c00d2440c00e008620044c082d085400c509180d04000070311030403085600c000d10302400d240c0820100c0c600e0340c0413102e0920404c070b000100a4600c4000c0c5a8002c2841c003900212400030703c0c00750701030b0400c640100c00030081055404c070f142e0000c0781000504046820020040c48200c1c5d210f840c00c000301030b0741071a00d40428001303004107010f1900040010114010001c131056400940e07085001d041c0c0002d41182e00c2003082c59088001c0c540540400d0341c000f1424052590301044030303800300e0a01c4014180010360101d81c0b003400900140100c100402d043c405040400410000d0000a000911444148400000c012 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 491155944 1250 491154694 491154739
    0xb1513050f01060906080406020f0c031209150f060f03030d0f02130801110a0c1a0a0b01030c0206090312040804050904120201050106030c090510020f0d0f180302010c2409030905 78
    0x1902103a1b140509543c45642d1440650000c401c070710003c5209102c034a900000030720150144c45030400d2414014074004441030325241001c8021100301116405110b144103031042e840703512a00541c0c9407070822003900c002c6441c40c8500072240426514000092422406a800401ca0190140c0c98132840305d4030b842c03c035401c0300d156560202903a030080052103020b501426940021078002c3d079054500145c29035042d40f2950044405d021282e9407464050460b60f01071041211608661004002d2482c003102034695038858607828001c80f0020000107030030441160200c40203400041c200c10218142460010039881d0300c1c00981c000f40d42024008030f8800d20a200340101c8ea081030395010159450013003170192401c20f0703004d10340c218081c840d403c058140c4c081003640701030348082d500c01c600c01d00c0349500241409000008030a00d092a40d0003040540e07400854101c081750404000d280625040e1101c1d034441c0d80407040d04041600f800ca941e0306040d0014618812150240c035000c0704100840500080b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 491157194 1250 491155944 491155949
    0x13140109110a0e0105010c0602070203150f130309060e03100c08071103030c1801111509120403020306040204051e0c070c06050a12020c0102040b0f0a0906020d020a0b1513050f010609 80
    0xf850040001000750350300c01c12040d409180074074801031402d0202d40101c2d0600c01d0811810700018603286c1441140d0324000c280584c0004d11030106603129445641c000c20f0802c0c1d030301c0380200b00501450002c840d40c4d8140504040b00080c14020400702c41c0300240076000900031100c1c1c90204500304c0c0d0303c1c5584003000c02107a210b03042010206240403083c01d90308560a1074169098100080d040030302043c1c1d4410060103074a9400c102d0381e4052442c2084641d0b01e050820300c2188000c050500007000181c8001404030b130040e50403500030410350b4940103a030900c0b41441135401208100e0f0000d02550f02058070040c0b400e14040e034840703e01540c88420a80702480f41011840001d2039a0840d141d400c603450307000c1c05001e80c0c02c0f00058506545c0752008625500620820170280b1320000d0644403103604290124010400c50000d0144a484040040d4031103014000c05002001040c0004915458404002c14424402425015107080f034410110040c14111080c40302e00a07980c0000ca42d41d806400d1143c02c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 491158444 1250 491157194 491157209
    0x504060f05090313180e0114060415050306130503070f030302030627160203040b0c0c120d2007210311160b09060403080f0d06051f050313140109110a 66
    0x74a5450040c0313200c00a050b0312042800c41b1360700e50388511030400078000c02c03245080d9401e1b800341d036080c9101013004584640804103018848001704000d1901c0c0412195440351440000d0803a500e003038140203045114007200101800c2070184010101601580554005c82c010703a2007002c5c01c0008415641560001e10850140d01c20030701c0002c038002100283c107200741410b88180e074200750355090f200700c450300702c06041c803010303080f10090090f181460121600d8200e442c00003054000c0c10602c0203040c00c20995004c8040340215103603050310b950100440402000030149032865001e15000325100c80565000c21400240c00c05e01341e142c11800012a02d621040440b0030484030f07171500703d0803d6030b94000036480d900070300203000010106403160050503902d039102044a0b6641022071000d01250440d812280c4108515070103007101d041c00f045d640c410f0b00094246540d0b07a8440f1411600c244100341c0d0000d05983e1400e500558140301900f000f5100c41c0302d1800d03c00f441d06100700304844400f40340134112 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 491159694 1250 491158444 491158477
    0xc050409140c0f0a02010f2f25061407080a18030f0e03010e0a05060103050f070f0b0705030d0e0f010605031504030315030804080601050108070f080f0c0c010504060f050903 76
    0x850158001c001c1c13490840c1030000040c1007c4400d03821061700d0291940035481c1000d11800200b075095044040a80900038200f00c0c81d21b02115141c11007552030741d140050440e48a03080d401003185a901012500c801c80710110365074a8460001009080200c40091289080c260220200d80031400c5940c210707030381511140707151805017130b048a0710b00c50100e91540c19034a4900e48202d8540c14003c0400b514013480152500c0e42c1541010740c40d0580700c582149161340502801c110b01011500200705552140400703035036071607140c1132a40c0345020701c3c0030070b00340d0601d052031111b0401400144002651607600c000d101f0320365114105130b00c80f01c0b000b401c0024607454000040006c0c0c8a03500a003119a02002103101e01038507902c0f01121508241c1011070a82d0290005200c07a60f0450380c2c4039404403244c5000c0d104441c00480040c1009400381c034810b828101030000c176000900399015220341e840d8504c001c011628007820f01002a0441d10389501c00c280c0f5100204000601c088101e5000700494480d20703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 491160944 1250 491159694 491159707
    0x309030a02061e0d09030f02120d050403030b09070201090b06220207050717070801060f0b0720060c03190503010509010b0703120501030f020a1e06030510030203010c050409140c 78
    0x125603214031600c0c0c030403580c3d48840b01440318143d00074110103a016030000920f0005441c4c060402240d010001080d980222810094249007000b180d207080c85034140860325455518080e0050a84c140c0e059520406480400c040d0950550080f2030160040810311200c0d00c843c0b0900c080c105c0c0301c200000909952200001101810f50010030a00d48200d040740c28541c3c1c1c840030284d081048203440d200540110328100140e0600340150005000d81c664440c171441c6c540b06503503541c0c1c030031100020215600c201d12855500d108481c1c81034620030190615030344c0e40c10088120b40300c0d4844051a804410340d220f01d0f4107104c3c031440c03e4a0607688050040781099080032400e1811350001c1d041101000108a400c400000084c02101c0c021445100f0820146140307204000711410300313401011054808044c11100c11011003a40c0e011a50a410b000a454545030a0140c102c501c89c1c001075099801c1c0b006482d11198032038020011134640890802c80d96248540700088490141d80c80e128101090214 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 491162194 1250 491160944 491160949
    0xb0415050f07092c0103080d140c0d09031e121401060c0201080901020d060e07110610051e03010e03030603070807060507080922060815130b27010903110309030a02 72
    0x138010094054441a4203a0aa8040507801c0090b00125904040800c540141c041c41e0700808d9128500003101c81114905401000010f006410000203c9a11100341e902498061021b12601c5025010071513309101e60348040d04218226000044251403c400b1540c0d20300169049030503282255075100182020750011503a00c003014202c64841d5508100c242e005645520400c0024440e20b1407248907490301320000340001c645410300050300d03041042045454124003045000380c41007141c0e10034000045050300c082d00d8042250300754240d031900d00d0400222000101462003a00e0840494a505895410b0710b916017600713105640104900740038400000b001034006d08201c1e903000d001d6007001d0743c440301d10900085100f10283d0f120b542c1c44000744002364081c0700720301e0303c0b6083c003410100c0703801c0c200b0983c489007200080c0980610355a2000c42d9001c280d002610b41400a0710028294449100303c000c0d0003045a2a81100400d41c425984101c00d030f400f0050f0342e1900c0c0003e0250205000c0f6809 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 491163444 1250 491162194 491162219
    0x80c03060607170301030c0e0c070218090304030b0f1605070c0b0a0c12030507020106061418060c1506010e010c150902210c090105040605031c0c0b0415050f0709 71
    0x1000c94403580ca20074042d412035000f2010310300841c05116980030682c07a1011700414140d02520143d80c0307800c208044005615130200c4142c00d5008610511840c2e6102c021007801d501403030f0402440351008006210700c4c1c00000000700d0050550701130402d02ea083c03009050b030703103813145480050040c3c000c240e007000765504080142c25501040e05041d20f034510b140d500c00011100d0310000c174012079511014007880c5c2d50f0901c81c060181c16103003008409440b045228200038010351601041c00b0100f4641120182c40d00700944150726000400c980c001300851040582101003241d44600044400e030081600758840c0402081c82c07600201813224504020004401a06050700c0580e00b0010540c01c10310035581c0035a81c2d61003508440054140100c003002000165101070380061710440c240f00c42070190ba6008100d03100b01c461030660001c0001860f2000761103122128001a21001122081100f400343c0c41c081040340e0003e02c1c400308030b1641c4400141c50181d00641d20100095841c20702804105d4031100c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 491164694 1250 491163444 491163457
    0x1090c050a0c15110a02010c1206051809010603060504080c0f0a0c05040c0e0a0b0c01060f080705101404090b0103050702010c140a0210020d1d070503032b06032001080c030606 77
    0x80d00460710302800c001010ba00c0d840540d8940060707550300922320940b0341c042c0141c555280e0700c0e9001d02c80c1f83c2c904400103e035520316086080e01005002c0c0814007008096200e14002c582c8414103000323901c1c003401c0280f030302d400000c10345200e8040c80310107100f00f10303000c60038032215030b402080c044c011810107013480024101c104841c802c0c820060305c68021550f408032004000c001c1d12260a81c0d85454004290955046901403104c030004030740107001907000840c01301d040e200c05444540483c0c400000846807840001540c4400120001e001304801d04070f90401a101002a2028461070b10307888012400c85601c1000b02c2e00089680c0c3c0310f44038508564005240402d150300c101c03903002600030342d0001280c1c815a9060020780d0b641c0a1034440441c0c035001d036000340f8841c1c1e001e0a405c44c43e10010a03128850303044c0b48011403525642040c48148440c0e41c120a5142070482000615160701c0c2c080200d51101c0d0800c101c20001c0400003c00d588100308191190301e044a82d00d003192120014409940c001c0d2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 491165944 1250 491164694 491164733
    0x1e050402041415120c09040b0601090308040e01050108060d050703030e031216050c0604140906010311131a09010c0803090c0d0312110f07030f0504050d060501090c050a0c 75
    0x700e80314800c40c0d18000d032203400750110781d29480d282154a020030009110a0130300c0ca016402c84555940c0743d40e03030300c001150300a8001e80e2106040e6590701c0102d515170441d07000100351020110340884e071801c0b00f02404e8143c1d64203881d500500e0311604d003042070b0045901c000500a41c004501440060711901c801104400060304894080400c0044036500f07030041d106020313001801c0121101400030811040f2100a01562030a28250400851082000c03151054502400c0c44c000400d00c589d1107680102000c076401c0200e141c4901604810003100386141c494005a4226429448010704c0c0c1c070002c5a021750b03016182d140b076000b081e40d10400c50340c00c000c04003a05409090b40c18200b030703100c00d011180b801d031099403040802c2c0490150103088031742c0c41c003260303c01040500001c43d24081010481e964160981403458130310030041403c5486110305d40010390071404a005c813808001554016605983c0c88000a01000c00450740072241c0340141c0d2891000100587c5040300812000c482c0d40e014640368 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 491167194 1250 491165944 491165951
    0x10320150f071101050c0d030504110901081b100c03080c211602030301030b0601050c1e0307110409030804020909010902040219120b130f061707080d031e05040204 72
    0x10080c0d1895500504038441d2603040000b8020200710044144064905003400c02c942080c1c1140741c040e07074420300a12420141551032020078244000b800e4807007000c0340005c00e43c040c0c030340c0c4480750b00e0b88550005124410346032440303c51041034680900501c0004541783e079064466070094a040300c80500142c0094400c080420000082c0d585001420400420396850b4400341d080c00d900c0100441d036100b1150045400a000500c0044e1a03450b940d504000240307003003501d64055440341030611050003a02e444110200c1c0c803540c01c441011001c0c0440d40d000f04101c69480c001c8809000650b01407440040000301c1c904002001450302e0030401e90482d8001c0c000166404865010400b2a4090030b040820b01d009001100d42117680450040b0624503501d1091010300011008250103001d065a00d48020b51160280c2440c0705007a44691300802001461403400c20401c41199107440319406200303654094401070b01d4469000c0d0241c08a0750020b0744e11451440c0d1800c7e8060300400c4c010344200e038042e44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 491168444 1250 491167194 491167219
    0x6230c0712150209090c030919032003040806071103040312030b09180604030e0f0a030813150f0309060b030303040c0f061704022b0308090d0503010320 67
    0x102048240081e20301d20a40500e04400c60400c1202c450310150404102c6004015840440d2900a01c054221203c0f001e0f85032261142405581094034900c00c0c5121252140340d043c0915501c2110303081c212401a0104c400c190310800b4083d00d0f8400c601a4940c181e110601149140d0701c02c040245169220100307030380c10701e5240d0f075540945074000f0041000007601c64508003007a00d40302103101c0d04006561f011000e104418041c0549400000780301909001d999281c26a181d110812000c1c03c2c808001c02000d511178070b07450700c49450b4000c13010310301c541942c0640209070b11654034911001c0700240e0304c9086040c2c1000204401030881c942040341d05907100c1c042d604041c2c81c1040614091489031034100324450070700805a43c0d45101d540500200003038030101040f00350719035070119000b540690301c62002100d1146c80b4071455540802400c00c28030b0001d41c4505041d07020a0850160150000741d50006030002c00413a541c1c002800050100340120410401f8003080404107502e819002e80a102d1210 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 491169694 1250 491168444 491168467
    0xa051b010915050901030b18070f05040807060306180216150f0c0806011409010f0509040b1513150906050a1812020f0301140c070c030816060c08010623 67
    0xc0e2440d141011980108003180c0345d40e01030141010102003601e003030700c1c03c2c8552103110540640c05804903060090340d100080e4110310440454002c0c003a5502112031980da100d2006004059a100311148400810b0005608004500807a441c1e400b00d00e01940f46089682c4904000540600c00000040e5485015114507501809003039400740d056101c960051500350300151170f4102d038035645415079030704200c000c40b01d030382062030140100c03400c0c500aa100c00004e00400c00030051402025445802d5604051130609000000c0040040a20030207201f1540c41c0080c0401003d00801c141c0850003034403092001c1c40c810805004040218039000c40400822520103141890a8000b00383c500c02a1802c070080d41803035522003840d25410b03030007007001070850000252200d001420500085000045010504c1302c4401080d0145401c40c0d00203598160203810070445400e01501161550700388140d082c81d41d030060030014102d078007544a410528002c41404950300c15001000440c0c030105011070507062 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 491170944 1250 491169694 491169719
    0xc07020a050108091009060b3307031404080102070c0f030809011409121e15070e060708040f050a0503031e0d11030f07090806090c04050a0914060103060b01020a051b0109 75
    0x4e401f4140008002405409005000303240309503031716006000400c40180180c140070011040101008130703903212a01860215850f203803400060b140204007150225050006600519102d442207442c44a85551500c0000d1410300310320020b04001c400b400340c40c1ca15405540b00e41c4410b400402400d01d01002480008c0407a0b00e2620103880e0f65203c40951980e00c05071624495000950100815004e0b000120316801084020b10600400111038103900c15620f540b8140d4001d582c1c42180f0603103440d01d806120200f160705204072846205880d00014050501000322030700c241d850b520041034602103800d03e02c3c07d548a4000903c05907601e421002c2003501400145000b040030014140036810810070041602c410f0341c108030305c20b402c03020610440d0400068890a004000d035030105c0c940e55140c402000401d440100030b004440c880781c00d4107003000e000c10002e05a038490b800400000c9100801261b54034866900244154003040b148205041482414401030304140361000c2c045864880c1c0c01c401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 491172194 1250 491170944 491170961
    0x60109080d021b0301022805120703020a17010302060a0305090c061c0e2b030f020a030207031101051b0702060d090510050c120c0904091b05090c07020a0501080910 72
    0x58116640100e51500301034019080d4240441c02507042045003540701da8680840b001e2660240c200c0c0090714041401413003030340c840d0b800f018100f51082c5030140b0080c01035884038040d0000210304ec5064100c0e00810507100f8160b0390054110790070925600019801410080c00355081886141206d103555590f40c070080c003a4802040825800e1503d0000f1401074072000007d02c9801d401c480144040e03640d0001c03c0a10410368442c20b408008080c010a400900744076205181e02c0b400002c2400c0c0c80e54250b002404031521944c1c541e80005503079014503003240c0081c0c4209400310700715941d0004585080d4003400c541c034001402c442c0f400800d00654000c41e0b600c2d8004650942101c18000000c0c502441006c0e80829480030861500172044c0322601150750040030300d1f20740c450100707003c480c5441e158803444140c0e90101c41c1d003502c10744049600440d03c0c13862003142d00ca01900c07000a1140c00910003a5290a5800360919400034282401521078080040005a99225000141d0461040c0e400344128 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 491173444 1250 491172194 491172197
    0x3150c0405041505150a0513062d0503180c06030a0603120f0206070c050a02031618020c0c010503061833010207050922050c040e1212060109080d 64
    0x5840e4501000e20080e507000b12650420041d10340380421094032003401504400e140103101310b0f90b8080002003034895001c0c2d0340030701c1c601020342540440c00030381000c80c0c1d1790240094a120a1003421000c2088116030b2080400c900140e41440072034000d02a040c0441034440011051303441c800001b401043c0203030170480d410f00d565034a42ca820018841c0d4001a102e0501e000e00d00240001c80e0500003a540740006401c1d1020025000414028410140301da10042580101900d0100400102c440d0a010940c0654520005075520360441100541700f06c40d0712a0541c0050700d0380750f802c032005680c940c0004103800d40140d1044d0000041c4099141d01d14400c140500003000044a406144001a00108454503940c4400102c000090381c000030102d0449170100d80024080d0707500e81c07901c2ca0151489c0241d0031120b295070b607010b0401c280410700848142c410755003080249034a54010760344c0c14006500c10340c150000c002d002d4100380e00c1e016155010f4818148a110540c0e04d0300c3d00b62501028200510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 491174694 1250 491173444 491173447
    0x7030b0c03060114030f06010e0a0504020c1b100929040305212b06080a030909050717180a021201020a0e09010b0a030f0b040203090618011112040203150c 68
    0x200b150703088901e404c5a4080c800d260f904500e130000c540a003c3c1009050316043c800010920319240d0742c0c1345104400741c50042e01c02d64880b042104055a00c2c03000d840300c20116003101890070200c2c1407440054580f40c00070b5a078042c0d03217440c0a10710903201040e503402c004541000385000c2d540c050064020001035100f0f20060040c164810086e1a5184100050040241003041011001643d13054401c2812001554031400303221188c0807103000f04102da10583d07007401a40d40301c5045c150010202c501f02e403030589080c4215500c0201c11504191030356040103c071903080e408110108090254020212214022200ca420103071300001c042288151003031100d6900040c5d007480c0d82e6440041600d117154261601000c550401c03ca84c07807503000e07407904c540c101a500c41007102140c803075410018800b14054021940c900300210040d031500780444445d1a408669110085090300500c14401104071411503181041003102d03008100d00030241003603034544140b032544610f007100d5008043c000c3c0850b0f141c7c203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 491175944 1250 491174694 491174701
    0x40204090f12081f031112100207020a1a070f140625020d050a1206030c0e060901120308062211040602100b031015231518090907030b0c03 61
    0x60080e40f00400000049080f035401c05010701a50008030150b80e0700c18140e40c05200c2080200d64840d203c46407000c818800d15803a81c2d44030443c6c0d030007484968000d45892101544552020a0212000807160400310040042d000411f00d0740c52182e2455229203e0201420381d05090f1a2a050056800264104142c03180050240c940000c00543c00c0040c0007600949480103400780450044045070300a0007400400300c8004460f0794440c0d400303550700400803a540b545900201c8c034140e4044440500070040b840001c1115034400c00321071122607060b6204040340d6036100a0180b090600c801203511007403291070002d0700006501550b248038004180071a1681d1920900a20306000c20b24000d032890301e88100d000c0c05403004a8108001d41380c01001042d800e2048a40408483d05503210f214405151aa4007128021103940034036103000441d403440b16103a10460410b4603215000e03440403a600c2040c101d48460905412095020170820240c0740056070b6034175030040d01042220000350310700002040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 491177194 1250 491175944 491175947
    0x1050403050d1b0c2c06030d03050a1e020d0c05040f0308070804030609140d0509030304170a0203030c0c01030c0e06030a090201050c01090b180307050318040f02040e06041407020d0305040204090f12 87
    0xa60758446040c0600305c1d400c01c1e00110392224a500c6454082503154000507855030060741168405040009500f02840500c8285400030f4210000100b903c0781016010100070744900140c8007030b50203103440c2c540c030185180c0c0d034403103294014402124108814000000030403007502c18050801d006494880103084012442c605104905000004ac01010312042d9001c0c2c600105a6090f2446441102d900040f0800300c90300c1e1001c1080001d500d4030001a40003481980412800044442a00d091110908403007055641030403908006410071801d00020704000d1494200e010864010305202d45804001d90316942512000c50041c1d41c1140307807005001380c901505074107420380810003000c0c5050003151364502ea01da100316110210900c12134090010b140e556607014002241421404550322031780c03183c18070144441112424031075840c001c40d4610f0390382c9a9089600c038402c9a4080c0041c1110080180c00a01c0050003d0303070410b40c0d44100000242d811120700306c0580c05030302ea540300100c1c401c10 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 491178444 1250 491177194 491177249
    0x90c060302030108030d051e010b0415050405180a09020621010803030f0f0714030106031a01030605090a0f0b060a0503180a030c15020d050f0a060501050403050d1b0c 73
    0x8154101441040100020400441602c2d01d00c0c071407800128a9484255098030309012070300983c60341c0800c5100029413201c00d01d00400803034104072540700311900c1d00c00040e07503580641e00c941c0350810304042c0c100080f400c2e03c8013590341c00a0180030024817402d460700030841c40d40184100c0d405015410408000c040c036030303801003030040815900551031841c01042c81d00b203400b000b8100303124181800b0045011b550003450b8078465580c0740300840d9240d40c3d65a100402404a51000c0309400b0745011945285502ca0300a07442130301d9015102004a40f00c0070b01c130000074103840801501c482e40e03601060140b0355441c0010708500d185507a40c1607c0b400d0450181390390b8802010a504140c0c051300c4100e0010b50005a11b1581c283c0005005d5560311414403c08080e11495404a120301d2500c0c1c00c201c502d0107110b1140b4001c05402004110a13a1900019200361140303010160069006a18507180d40380304500a82c0044d04940080407400352071b54070901000c001e40c003e4050200180c0000002c10034901 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 491179694 1250 491178444 491178449
    0x60d0f1401091101030e07120206090102100c050a0e030607080103200301020d050f180a0321050a06140a0b09040902190602030315040c0f030e0304170a0b0a0b01050a030e0a06020409090c 82
    0x10003a01d40a45001c540b421403023003e00d0000d009900203d448800e0b40e0003402141c0c41d544038081d080c003849a0300c12004003268440000760307004c41c09800c1548918240000d0091040c01c1641f5480340741d90a6450315810030250790000c60355199008503401039900c080c005004000d00e100c0740490203040501044070360b1180280911817084013410421508440083d480c2c0c0307243c3d050300740300c45014034204e5004101c60300d09030003c0703c0509110501100e064503a000c40111920b410a80003800d0602c1c0c01c02151303030503a1040d481e640f40240701203030745887d20b039104041d03ca04c0100700e11604490180690307400e4200d9800760001da0404003c109400d081c400d003601850604032010050800351110141c28603245e240381c041010f0742c8000f00c0b11074003402c1044802a10130604007510450400030341e41d540c0c22170307170308201c0f80507032020081076a42080d40110390100354141c40c0e0b1030401d000d00404900401d030711810760141d03104004d0082d021400502c000d00c0680440c02000c10b04030311b241800418a0141e6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 491180944 1250 491179694 491179721
    0x311090f3d0806251409010207030b130507050108100e100302120f12042301030603060e0f010b06090321131517040506070e040605060f070515060d0f140109110103 72
    0xc0d504c40e46000e44c84208600f110016502a40d01d40100000403031030074405800040500580c1c109000291081c440c0b8403901a10440c11a4056138655004640348401900c0c0c000055030080024000443e1040700c0d01d9004550400d001040c5640380c001a0811000f00c0710360b26560420f10f000b00d0040c10500c40b02c14a071092008051402d80b81180b8812000002d586d4480442100340420b1603e80c443d4100900440d0005800e1155890b20481607031039850302e505001c020362900d0003c8600341412001e0700c400c2d0394000c015041c602881050910301d010000802820320104010150f66562654150b102601c4169002c0c010115a11406000406904e41c4d21046460440801001507000140d065210040749044042a1920804103005c1c02c400e8105641c0554082a04502400c030f41c80a0031109000e841122100d4122407000b100b180c2c410344206401554111240020078405280103030b15034031514121001c40410107040c0c1c211644554212200a0501200c070829070303041c0260745659890 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 491182194 1250 491180944 491181001
    0x7170108060c0f070c08010203220503070b0711030d060e0a050f060118030b0c090108060d030804020915030f0c030f01020c0c0415050603010311090f3d0806 69
    0x108818959038400c002c0ca941c42d088000106200d40036000c1080c0c0d0b03007065021100049450f106c0400381e01070b4000306c0d6210301e404c10904954221499940c007400c0401d4200015610304282510703042d000c20030040000003400703d400e8078000310020400040031940d400f1140000c906040c03645c041e1914402914400340c040c20302c000c1c0300b0030041c240f80b20ba4011a0900301540303081c4562030006001d54081d48041e080d1031018041111000201c001040003201c240d8800700e050341c8140402c03140d2100b080c006000100341d41c00003001030030f2070b182c1150001090307092051402942d100103484d0401180381903103160410707613000d0103030b08007080003d610300c014400175401d18808490342c0b60b4411240120074801e40e1142c08109641140c48803810140c100a04055a00d42e1642001e821481c640794019000d400610b0000b00c10384414903416020341d4100100c0c9001b846401060303d448406a400c0074150455103158080e07021b0400030301d00040110034058203d03032904e1180d45060411408000070103061 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 491183444 1250 491182194 491182199
    0x90d0606031a15100e040908130f0e0c030c0d0504050109170a0e01050702060705010c020a11041503060e070f090e060603070602030a11070f06030f0e0d09050f06190305071701 77
    0xa401180381d000f00083d00c0030b52444003100b400311032094001713024079005458800c4003824010700400800415200c010402c0695a89a4500580e04514425100494086070208543d117014030700454011043e0f00040341041400901c5100b150301c1681c003121035030754a00c07948003000705010b0700c001201414a48682401c4042c0380c080d04074581001c1c203074100700e400540402150b031200b0a0760b00c02c9811000030444080345940180d0350b91010740060312001c008040300100351a040c0a9050071040c500f085941462540e500e40014060b9201c141c0c410707004080d00882c01c10b0310702c4100030061040c0140031030711001c01081c0c1400c02c00068910341c081d4101080900c201c17a0000103e0f442c080961034110a410100300002d8100b5510350481d07130807148001c40004841e42d040e0401303a400011200104107909400750710342d64482da07511800011510100003004070b0300e0601501400b003040940903d142410b82000d0550448100140f0710110b030f0f40e038044c00421a40305291044610306070020031000e50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 491184694 1250 491183444 491183461
    0x21501051f1101050a060302010915020d20010c02160e01140f0d0615061103032a0903060c0d0507080c0d0213180911040207020f060a05090d0606031a 66
    0x90040100110140c40610301020052080342c107100c050702100020003d90801c0390100303020b420785200686c000740c603800300807a141d0000880b02c80104c40315002080080c015070001ea4013000c00b0503024800c0000c140c43d20344007100a000c0c50b07606a590380d0203002105800c0c1055004106c0d107402601010b001580140901000007004010820040728000d0f8508546400a40401c106000c010b000382c2c1000490382e00d1807a032680c02c0c02a514180c880c05406d4995141c0d040d03403800203d9803c3c6001301082101548404000000006010041400c924080940d80803a1420030207507035000c0820340c0056041060070480c4140781d0004c1c0b540c82e2088039810140b41a59550143e140c0d42000e81c0e44c0003a1094070810700c00b04110051035500c41e00c44003450603c0490008021f10703030040d6000328400003803946916080c821613151a81c028000c0c1525044202440215040b601c4000b05002e030400c0442403035603d0208120a442c4106800300c1d00c141145842c1c0d4100719040341e000780e0706440806200c8641d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 491185944 1250 491184694 491184709
    0x20c0a0b0711040b0a080f06071b0201020d0f031b0206040c0f0602070b090a1d0f07021c2601080d02010e0d050d052e2d150c0615050102150105 63
    0x5002c02c841c0800d4140341c40000402e07003200c0e136220076058450101e20f18580a0007281e0644030b03003410340b10144440c4030501c00b440003140182c1c000740103070440a242c00c0e5140c02000c404245203a5131400050b10a25040015104c46806070503c1c05a0b000a08200c108012014800c020740002c0110310580c03881c0c2000a0350322600c0d40103a01541c8000f0030906070b9600c6150702c85004006665846007082d80c140001c2070525015108549103903806000685041c0c000141c01144003110a04007911044100301190040340640400441c0914601c0c090300c95030340c411030b45003c0d04140000e0114a6440100a421511780d9060783c2c80a400c40140103400941290558400b07500250001c10180d803030b01c4c80e0042d20344038108004094602443c083e8015418142d08034181c4955001e0b40381481404214128582c00030580b05503221200e4030700f030200342c4a041e203a03003602c42d490801203820020750b6240b0f400c1c1c8001401030100e020403c03204008540e4100220340c903440f0059070240c2301e03504040214444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 491187050 1106 491185944 491185973
    0x105010e0406050307090b0109080607050a0216120f110a09051906141c080703020102070606091b0e060702150301090b1f030513080a020c0a0b07 64
    0x150309080c801c84080d03c100400424840d4944207407070703002d00510030210741081003036400000c40a40800081d07002c0d4905803100350700c8004446000f46006400c880c0e4031641d070301c12141004043c00d89100300c060305400180c9603081100a0800c41404902d0501854200e00140c1000407501115404107010b55400100c20305c0034180003040310160340c43d40c040e481c1500050985550705261100d0111032009500c100d10100c1d16031501c070004503802401059000d42d4000900608120840c82000042c25000c1410400a000248032100c0c2d500151400e03000e10aa1055056150341c03140705864403030380c0c000c5c48a505022540b040000e550402c2c17007038410850030070414041500d8101d440c2950010b19100e206c0629030549811409058080c2030480405407038049100032851f0200203003040c0354603030000c04082442606000d400c809035400509075500501c030020001c0ca070400080c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 491007194 491187050 := by
  have h0 := BRFrame.cov_init 491007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 491007194 ≤ n) (h2 : n < 491187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
