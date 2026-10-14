-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2566
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:05:19.034931+00:00
-- url     : https://prove2.me/submissions/52db101a-237d-49b3-9f6b-15bc24df6969

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 461330935 ≤ n < 461510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 461332185 1250 461330935 461330939
    0x203101a0904080403020f0d05032106010810090c020f030c07030b09030c0d120e0d020d090b0903060c1809040312060e06010206060907180315060e06010203070b0c040f03140106 78
    0x10303044400b9900074001d00000d110900050400900590081c8001810790b01c000500da5101840c0d640003440301101e2100900b00022111000c0c1846900800242003071000c514040358404148101c40c80342c46142a241c0c0c09405000d4000d0200010203041c9c80145d0f07a60304250610990b84003800d2104483c6d401c1c42c03800050b01040048140c510b404001005014642100c0c1403c445107950b0042418265944041407002c0520810099414001c0d940181090300c00b030342d1001d030003441c4075805010020340400c01f8001658004c205150b002040e070340010340381c2c0039020701c0c109481e1085110942111843c41800305040e040413180c01c0141c1800000d001d0307141c4402c084101200700361069809a401000454201d1821281c0c0740d5002109180020700034580b940c159042552590058039040d400219078401000b4034010b036400703440c400011f44554100303500000d42e244142080a0443c03185400860310481c1058100d500809901c54404199600e0342007110300c41c840800314400c603620340140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 461333435 1250 461332185 461332189
    0x60807150207050603040303110f0313050c10020a03080a0e06010602071502190b0a200a02060609060a1509081006170d140c030d02030709060f0c08250203101a 70
    0x260b003081d600040c1c103a070304648071541c1c15005080c0554401d20090000d0042d07a036240d82c1000036510030030500c0045602c20a09083c450300b04040801024051032507204000b00d403540000d030201c256a41442c1084280e551a48024002e062038041c1e160140541d8000184c01680020200152401108400d00781c5091540503a95115265243c4031516085810380b80403644051002d5444090a4400305064040d0000d06a8000d41c0b88504c0c1c038110b00100f07456515560400213954030035000d407409a00d5090a80000c0c0b43c0c1d0070144642d182c901c102c4d075140e00400d4030035002c000052070010212038509540c481280043c0001d40215041d42030205401203600000185d0803001c1115038a50a0182c800c011454440c4e90200301480300c1c0344000c01a0000445451008610641c220383d0f5201c0581d0506000070b00d20581c1c40300300410000850440004140d500b412500c0d0740c500c40400c091192861044018038280852001e503040c0915820808658090b801010012030045400b050010030303401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 461334685 1250 461333435 461333443
    0xa09030c061e0507031e0201020406090e040b04080f12070c0201110d09060f03060810050402030d0c20120604120206070201290409020a170714090a110c010608071502 73
    0x60501280760340d0788007140e070b114096002407500340c1c081d140140d58a0071a03042c55030040141d40d8000c0060b9800901001300070f034842c02000280c804c00c0000d1841d42401c0c0c95207110700602401c090560ba0300003412640403400c400403220b620904030b12905040c41e10f190043c00c0c011035500260701280c0d11030022520742030049100600c3c0c003040e8442038411800c0210465403402c0410410090550311400400d8000003007101c8407080440500100b41c0345000c0c41410b0404910a82d2030040c4416000140000340e00b840c041190848217071450035290400d8000604100c01036842c29081d4081c1d60140424003d00d2a502017050f01e440d001ca81c825154007000702d00702d4180c660340a01044420f6582100c29201d5402e030000c078423001b0b0020403010800d03000241e0401080d4448600c010076507000c40d1b0707070f944140503810040c904628401800c0380341001003000c094004000040b45551034000030008a070107010340b51150241002044017030780315418650344a4882c0500c514440c0007401940e0028170000e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 461335935 1250 461334685 461334707
    0x3010b010e09040f05010f1814070503070b0f0706050906071e02100515030115091802060405130e0d090512030301050307150302280305060d02030705011209080a09030c06 75
    0x2e00000b01507030b1a03403140300c90f441c070703509080700c0d155203600080d554415180107140c2d42100821030903040d01c016250201002407024a4030015070805001001242d4001c1844030440d0813401125503a1518008540c0d1030348981540246039074a4001407058050740000c1d50352081c0e50584445101480e6480c10148140c3d401c4c00000041e0b100903045d510340f05560700400d40018241c240c4103424034400002a0a481200681e003107800c150410408c0308064a014800d16041d405010f00034000ea2170300410400e104601500b40180006504004016495808503010440d64001d89442c40c110035002003148541d445040c0c440c81c80308901d20000e113004421a41203800040042c4159454505040e104501500b8242c0038168240328802100d040741c003081e40f00c0d031120124001c4905800070080c088450240c005405405200050001a10000f0703040c42524400d00f0f051400b003027640306460203080ba98100a04900e00800e058400542007202601175070320900c51400705a44a2034101d494145807 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 461337185 1250 461335935 461335939
    0x5070914030a02030714010c0b0906060901240c030c231b2b0b070206070f2c030106051f110a0803060d02011710090c110c090a14130203010b010e 64
    0x39000411200f85040c2c5080340d1180d06052848e411300041e1a0703484002c404941e4240c1c5500004104030b028600752150314054441c01807010640d402e02484003164a0007000f100d814050181883d4040c54003405c40304020b254001960501080c01c1ea062500b50071000500001500c10a401401005030300303000d540c22094081d05000c461200803125041002921405110303a40c90340c020b401c0031801d44140315116038095002405103081842009040d896030052560800c00300400f150f04419400210395031410b00d40c04c124240750050f070000f03801460f040d40000e41c00010400480292245194091032904298503016410160344a9568460f4201e08000b0440201080025000c1c548207400307005031070040c509143d034220344031200c800264094130396144095001004100c0440f050044040008c418648141301419024000d940c0d10000745815200b02c61403000200d4032080c96001c61600c07405400300c0011410810050700900310541e0040c0d000f542804491501e41d4001c2c00116100500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 461338435 1250 461337185 461337193
    0x308130e240429040e0d050702010e0108090a0204091506080f0d0509011704030201180b040c0b130611030c01230f0f040303020a020f07090b010e0a0303020c0d080d05070914030a0203 80
    0x260b1003000c20300e0240c0740d10f11944581da440c0002c000c1c0104000040e928103003515a81d42d034254600001d401710043e400414100000d04080004800303012403507000c19a41a40c0204035100149030156000d407040e00181e046c1c07868002e0000e5140e01c0041c100d210000c48000341e030b02c1107a0f2008101c485214102020f40411244040b24002e00004034000b50303c54007900c0001140008072662515550250b4402c3d00c1c18101c8400307000900c064100070100501716044014580004140d0302c00c4030364054803170002806501400112642402d004880f11041403030001c0040c840780c5c0e682000300381e03d007a5154138001e40150000300100e0610001d203003d1401b08880d500d0075034490b90210040c2d48414107050850160010300f40765010204108400380c03140c040007050802128000500c01d5100b11051840360111200400119070040380c03403201e2510994204140603100d041091f054030900b40c40d101c16900d8041040030b0998020359110640b040c80e08007480221b00603081680c1c403480018085e505400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 461339685 1250 461338435 461338481
    0x2160f0b042304141608010e06010e03010b060f03041b2405070b09061b0315090402060f0a02010501050f06070b010e1506031306050705040602070308130e2404 70
    0x204403040d894034200c1c410080c0c0414200c0208040d940009440c10f044d0400406015505400030300c460303120801c9140500b040c0d03243c4251040c000402802d8641800114151319006460a411804001c0809085a030b80c404032404164410303401201d083c0d90125800141416120007020000102d64440d007208100e8220041200001c90900e42c0701010f10204001070400030f81440d404c1032003000303048040c2a26180c01c2030300110340310801a062030206010401c016418615000c002d5200400b034680c0c0b071481c0d5407840407403250f00c00c0a110180b001000725852210982c1508080c1c180c50b41912100ca42c00219018801c2c0303030241c00c00c0200541e02c103200600510b5040072010303a0180c62400c013a02c0c103200c01404901554015911520204d10001403d024810346020b001d402121a1410780e141500d4408000c6d240d111901004040e81000030380c0c124251141c000440161960885006550a112030100652085105070942910003801d00d41890319082c0314009600e40030301c03200d80204c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 461340935 1250 461339685 461339699
    0xa0b0409050a0216030c0210170c03060d17030610080c03040303050a0b0a06030f06050d08030f07051902150c030714160c180e06040f06150302030d02160f0b04 70
    0x11074001c141400c550750a00c146070315111640d1000c074a440c000e880300c1000d402c0d42d0050100e240320380000c1c00c0078030864103441d0301c1c222500c8038501c0c1d10094070012140c0b00c0d2140b600244161000e83d03005080155800c0f400c1011500c201c2c011805510200c5074005011100c01c0f01340c0d49000110b4078000e00c20f0007480040c005c81d0207500b203654410005100090480946030000c0c040c09115000380c00001d0342e400f207484030480c65210704005010105c52405030000c02c1d0350360902c2c0384401011690031421090110b55000d0081c401e0313612982152148135080c81c2058002907440d405000720640c5841280045039080800c0002c903409010b150340d9084010b060805a03038002d62186286111140d81c08480e00c020407103440e103000151100094103000260701c8101142a00d0030032900e076807035070045810b12000501c00006c400c4588ea2140c3d0200f501d05505608044401c1242e001135098002e404042e5816075011440f8500e40f00101d1090303101917183c48508003805082d0040d4131009104200c01c0c8911 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 461342185 1250 461340935 461340941
    0x3004060504060902030607030c0912020607081c050a0c030b01140a0c02121203070906090f051c0510060513090f0212030c0708030d0e0115091112010b180a0b0409 71
    0x1400b078032010601c120141c0c046480d0290464426000139520040c45000791340c0191800010020035640340a0104550002880c0e4401c44100608403500003e015104400a141d0060311780541c9504120910307041d56201c024002111000000a1404010317210560046280824094814001a003031440441094030070b9a86001d0991744010105a1000f03801020801c0c05080e1071451000c41d1079040c8060040e0041d5081d0704000c0c1070056211040c080003094040000444504507522600075002175005201c02103000307805400c600500d4018100603210340c02040032240c040d9481040ea1403100c444404994800200400034607452052502529087e0b4080d140340142d941501d203801d034500c10452410685034000ea03110f0700003058890086569210f03d002c0c00ea2028001c1c010501d0625501c52504001d000f842c00203039036940c031280c0750f03203c4609603501c2920340380402c0035a5131119200500c0b0741101065234045c0900381035200650602c044440c0803600104105e508041c00c100001002d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 461343435 1250 461342185 461342191
    0x5091e070903020d060204030618030f0302032706041b081c0e06040905101205190804051009170a0c0603050705120f04020a080105061e1504030830040605 68
    0x10408010780100140c0c1d00c000b56440d001340309080040c2d407140b8603d8100281e03940003100e0380c1a40380c0c9034032440120360000400b82d80c1c1412890b005075203541d80003481d03208854508041e001c4c4032403180c04056006000958a0196000345540c40068132900100903910b20180600c00007504117140c00094042d44010390100c105031401e00185684000e40031800a400507440048815114003d1140f504402038001c2c003c0c081d03111041c0a91740c201d4480303a942d02c1c01414200d450300344c0009000300b030100d0442900e018180042a031200b0200e9400c0007082d21a5a0080e1002e00c0d84540c90a04041030004000030210b40c0b01c40c00a04062034144150000ccc04000d0030320301030207010000e4007003042604054070320822000c040320350181024014032100700c0042d003254005a1400303040c019a582e4090900c0f0702c940e04034110b0710700c2508034030104003201e07500d01d00b105078410040b07408410804010042c04042101e0300300001c0074a541050308001c080303014000e0120f0054140407502064558005130340c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 461344685 1250 461343435 461343437
    0x503040503040e160806090708040b10180e0609010c0206190e010f02042103021c0c06020301060c02031009080703031d1e0717030f071406010305030702010905091e07 73
    0xb040680c0c0394031030b20b00c090b01251001840d540c900d800c81c000c0c5802410403a0413280640d028046441c003070b14013500e000c50140000d0400364585000540c0d101c8110828006041c04c1140111048403854500780900101c4d10110014001c0c440000c901800c14440c0c480098810780c02004c040d02d4005e217441016801c0b00c070866020303848101c1c5c130a140009001c0e000d29048000c40050fa6140341181c1003a03100a220385e00007840e0780f8403041c100841c3e400140684800700e500c0c071008070113001c404107440f00c0c51499001004a07002000000c0c500e82c00802282119000fa425244240c50030003a00017200d500040041004406214610110b8465804404103140e05008008044044042075207060021a0141c08507003984908000c819800c0c84035034000c0905144940c080b61746401c0d603503200e0191030041c06079180301051443c2440b12248180540d112020140c1e040780d6102d040c415104e6000440503408101c1c84200010181090b00382c580c0305511000f0701e079041d9010b0707481d82110400003030002d80c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 461345935 1250 461344685 461344687
    0x20a021513210b070509130c020102070c0905070806060a091505071e0309080705060f0702181e010b0306030d031139010b0117071808010509012004060503040503 71
    0x21a070303000d01e520060b80240c25200704540301480381c606510750000060a1008010080c400200b11742c4420741d03c0c844020b0a500c0105240d41d400030128024062040050903485d0b4004001460180e168031003401000b00b80e850107a10703903441c0180141c82c450030046800007050311500b040301000c0328500445005980c0f40292030040252138030000c1030444d900c840d583e4030341e41c030004040541140b404801400311502401d8190726080001b102030003100000c150740500041e5201c119a12601c135204021990203040c0850308020b800551000384200c8a20034500400c2c0000c03801c1011a02a80e01c1143e00600400d038074007500c2800c40241001e00c10b0050040300510025800d08000041640c085143c03109016401c98001708803290035072505590340040c9d15007400700c09166402090101c0c14105d410007101c40341c80d070000032100708505074404141c1d40700d80344020812034410b42045002d0010b000090104606c05c0181d114210381071500791110b0f41c410401006580d00a10165034014020f00c142c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 461347185 1250 461345935 461345939
    0x1315051801090905040503120a15051e060f0a020c040b0a051002070320010e04090b0408030c0c011407080901060501270902040b04031202011104121110020d02010c020a021513 77
    0x40f805030361069a088a15030004a468041c614004004541c0041800400d100ea032080e640c8403031038000e01c1d008082c041c801202480105c95005121078040c8c0748080e190982c2d032070384c030000d0a940f0b400500c4500d00501900b21140840e18050113a03c000910051001980320728103000c0003210783c409800b0360b041d401560400804074500a80c0041c05504c000c00354042c0d000c2000004001354800c04160340b19600d041c5200021481c40452141c6c050361012140d90f607034807103500c54040c50080b48010580c0c0d40c00d0000038401c03614260041400381038241c072818110784644a9042c2a641d250042a0004000c0035815626524885c03909034807208060f44060501e0300c4800c2102641c1c0320350020569114006020001c008a100b002079403c00148001c00100928110784402c51040344034803094520011011418489248005140444000c0c0692490b201071100651580c0c10411804090352900e003102c0c40c0700380049491803415600604580310301503840e07240c94583d04961410183c0400c00030300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 461348435 1250 461347185 461347199
    0xd11070906030b06060304050a0f050606030d02070e01050108090a05062802191202070c0e040219060801090b06040803070b0108062d1305120c010b0402091e1311131505180109 77
    0x80c0c0824ac038000d80240030545490f81c01d0600d01041515564210342c00981d042002e008c90a00c90b50658000b40381c5151251168080c41e031405000380000340c06409030398103100c092200130440c040030b54240c1000400c0000f04200d010100d0160328100414511944003a848152061114640b03140402600505000e4142c840303681e19585038000351f0081c0b0507c0280400d5240c100e14401040d100c80303610b200c2c56030070b00000801540c018420a0302d015103ea44225080d5640d000382c602410040d0122922100395042103400c0301800c1c46403054501489000c9560900c49140641c41450020010401c0d00c401c0389c1406c08041005007440510a80f000c80c54001400c03c0c090140840020b0220307545401c241c81c0c0b440d08640003108104d1045104000c01c81040e242e0321800c82c40b41d480001110321018030013011542c07034102400d075a0403152a0840c481d04a02031f69002d000d0b68000342107a842c2184e00c4901000988480344103181c0410b000b40824803011007442c0e05998100c070185018800c03580d80300a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 461349685 1250 461348435 461348453
    0x9031207053a1e1817031e0c070c0803030702070311041d0a0606052205150a150e0901240509100507030e03070e0a0218030d11070906030b06060304050a 67
    0x481510140b0200403248400e9441340038070090f1072044c08800c03245160550300d0384d0b1224a5030300352800341203001c40040c40f111600071074241e0190740201c0040c101d240401130480750360b01c1180c0483c0c42480c000d601140308e0400109681c4680d005030000c020042c2075440d0f41c40405d0a4408181c0e0240e2a5407103540c0003c0900300c3c000b080306441c0c004000542c854a00300d4243c0f6416040540540840b10b20095500411140c0e5072190b8403942d4001016126020130500b8124521101c0390403c2d80585c00160500e1003602c1c480d07180d2000c1c0c0c2c0c1c038906098000304103c00c01c0001c5c425100410100c80b0707805420505207900701e0741000c1d9400c00524011451021501c8038600e81d081c1ca011a10116541b0149500700241007405d41c401c41c0589030a60800c242000c0c61390010b041c0c10002540440e401c070801c0c40701c000e212042e40c001402c40e0304291454000a1400c280c04e640c12140d8055003c000503100c46502410042c0d9900c0214070189594000610495820050043e1241e10988566034040b81c4048 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 461350935 1250 461349685 461349701
    0x110301090809120a03020a11040f09081c0b0306010b0906070c060815030a05120a030617030c0f030a0f0323090c040c1404230909031207053a 62
    0xc1070031525480035404201104a103480340c010150044001480000d070f010404c540d1440d8000420742440090f01d001c600107180302201421454500b04400d0b05100c3d1900290001035031080071586d80390b81e0400405c0030b0710100007400340c1581c070010040c0b180b1228003002d003000307540c003030103e50508283c4d07155400c14516550020012800b20010f0201c2e0f1300760031203035051281c000d800601140129948042e0b07240701240035100c1c00c107408129201303000e02c0794111030000c10840403161855108150303130644961102e02c40d10380503c9080d40310b6564550201c01d87e44411055290400302802502080d4064414080d0340d0709440700d1016039038105107405049500440d506401002500c008000b8407080f030743c100c600e4070144040d800c0303921541140717a401c44098a40f148001c2110a20003001003920700070403046640c4c468120810441360200000180078030680e060001c0c965078840440c103880c2449214410201090b43c55501c9940c0b0400352000107107840c00035a40b580d4036605000328801c0300d80c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 461352185 1250 461350935 461350943
    0x80a18060309050c0d120311130608060f0d080a1107090504061406011404090b0a171b01090e0408030603072412061202151204111008010303140711030109 68
    0x50b011140500c0001c00c0340c09625541501c140780380310800c1d285c1003030308014021507104141e2a00034400d0851242410380c0c01d03c0c8402c038294030002e0780756503010740030140c11203520707000303c500740c501c25200e192101001c0ba1460304140e000d841c2c5010707224100c1d1650b0050a00001078402e40354000340b4106940b01c0c55120701e0281d030740040e030001c007004415405a0050a1981000320032442050131003008000c80b0111804100005080e580e04400b0a234021815803007105403940a07414591150303800714080c8103442480000241d580707103010041d90440040e00400030000f4440c800a800108403400440d0049030003012241140d9403000c9010702e9244120a591a5250707041401480300d400007451050800038544c107000b01800c1c14880622140d01c00d8020744a0386c00300702012014a80c0b14100c0d400001605540e02d140d06d051b0810340c001440207469a4021160344800114441c0f0611800703040e640d05582d0300c070405c41e22246010301c5811220060360204500701709840c0740e6a0910070561b0507485 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 461353435 1250 461352185 461352191
    0xb04152327011b06111308060c1c09020f1f1101050c0f0307050f03090a11030a020f0108060a08070e0106030b240708041205010b12150103080a180603 66
    0x920006040700c0003038560301000709400046449401da07041a2408400e841080d21003011501c9800d196001d0310146420803a40640010070300c01d040901320b83c08003610360f058201c407560703102d030700c0841510701ca82650400c0c02d10841d8804084d03062190403030058607000901e0750160002c12800900300711690380b40c902c0034183c4419456165504044003c04002c80c1d000200190b15040c80202c1d014802c1e40000c01001300c000001890741c50003042611203080000c01410b0301d920b400262280d81c1c410360036041c0c516040500e0f40c08a9440c000903040c4440d9030107090013600c15090001507842c0c01015121703550102c5c4028001ca4a030504104400c010544004c1c0100e10354941000030f0200c07a1400c0f8294020302e03032a800800079680c20005140e0381d280c80d071201551012207041c41c02e21805070ba0000812540c80115040c01e01005400002140d03800b22507a007480e00021007581d950388103048080d41140702000041000c252944c001c2c180195090426402d440c041041c008a0f07a1101e03003000b40480d035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 461354685 1250 461353435 461353447
    0xf1005100c050106050a03030207030b0c1b070602070918201c06060512060c0d0204090e01050702071e0b030a09020402030f010602070510170910050112020f06040b041523 75
    0x2c404d000c0da4004107003c2e1a20300c2c0603030568800035240d01e66408090854a070b000b0206002455800840704c54030a107860303404a8031030040b4640c0d180c01c041e104220040c410500082405c0c5524840c074102c54044031201e66010b2000c0c5e6032807240004500d141c01c0b0124150905881e0b9841e0000998060604442038240015062030184120744050300403d01514808000a1010000003040790b00a0341102083d920381c105401901e019125176002800f88505081c01c200241205400c003500a507165005e0365802c075200d0b04405541c5100801e940092600e1040403c42000244001e60b0043c60768100421240d00c150007003412380e4410b1b15a04034601100300100300466060103000c020b410112141035945006e00802009a600c948000035004110300c0820b02101c4100703c1401a14000302c001e000d00d40c0d50300c060840607419440e06a01a0103940c1014803549005000c030344c15600224607071070030700b42813603299011003031802c4800050001c050384d000d001ca0442c14982d003569807480403956442c0c07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 461355935 1250 461354685 461354693
    0x60b18182e0302031504141c031803090909030207051c02130c09030b060f0d03031e02120703050606042718020109150504090e0d20060f1005100c 64
    0x1c0e84280741100c00020500081c4016075001c80c2d0502c01e86440250203d0136160303070501154100c040084005a482014143d41400c5071000760010a403450b1748003040640301c4c02119040030b103079a250040014a6401090000110540c0001d90040c003d10403507181030785a00205100b0111107081ca40654044003c1c04c045240444d8445949140071805200717100c0d1011001e070442c2c0490000a1035218004005081901c0381c11030f1000c01c0a0007005c494017899181000703001440051815440340038a103190344a008150700859400389140850580c2595401c0300c224020301c40503101940c070074002c1000248961104c40c0c1d000842d201c09022065030b00310111080c0c2210300d0005840889144000e44401503a00510b859044460806201020001408040351a0301c616000300c41101d01c0c7c100d0040001034005002225920326890f19090402c1f0061524141d07001c00341d40862f154441c00c0050302010041c2c14294100d00035409819134652100c00180310b154107080c8110002c1c050b0b902000c240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 461357185 1250 461355935 461355991
    0xf012f030405040f1d0d050d090212060a1d1f0c0915050c01050a05040f060b040f020a1d0901150f0c0f0f0c15140702030f240a060b1818 60
    0x903881c036074001c6c142041c920b14050300c3d5000b2002034500580d5a0404402503440c0c05180c00726000c100e0702a00c10342d150075620640141500c140282001ca400b0039000e04400b40055103494990701a40302c021400c05456194000d050b5100d040c6040094280e00006d0903a0204513100c8016001e4448a40b581e400352003060031140018001e260140c01e01081c440802e9141c6446441e80d44c0041021505080c030501103401750400b0890503100714400500d104241d0f0303201e144c0200003010f031600d04641c03141080030003030300c85400e000d101d08060100301070306452802440d0100c1d404846080c041103d1019460707a070028480c13024203846484200d461201000310414008000d4001d0000c9003011800713175040280081c1989550f06201d10000415032b0540d40c0410130001182241402c47d8210300da80890490b11580f0040d1071250908140c01145c141d10b450300444055070340c40c400107810300911040d138580000b6410306d144e411507a20034580040c075010a0b0b00c02d01c00da584860a004102c040900743d001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 461358435 1250 461357185 461357231
    0x70b0705241302010302090a05060309030c101a011b050610180c051912020313050d03022106041409030309070e04020f012001020403050a020f012f030405040f 70
    0x102481d010800740098000d102c00500360286801611900c14901095920015801a640c0424044104104100b000005080d0103c00b0802d541a12035842400b0041c0e58294880900301186844040f0080d4803d50300c20140e1282c600b28100b0310140f5031100c6060100581d61041c0b4824014000e12198a040c481070040480005042161001d1140010091b001e6440b01c2400a1501400b03141c1d860f00c101c3c0c45c20f0140c200f070a411507803400d002c480d00002c4c500c941c0c41203955014030ba0100c00c110b80a4800e80741c0040c1da8501d803075140c0b0a40515001a440010040d5038865515009152040f0b1910405480b0340803580045640c2e060002c1030740c5c40d12041d98002a40800b5540801006840e15040c00307010240a00740399640c01b118401482200b1447c00340340610f5031021070000144000000ca40b243c440c000d0362590002407a0000455400034503075404c160003030141c81400c85a0401448a0f0903101e01c0740c1c11799003050f84800000b01a5010008401d01c142d84404000111080e800c1c80404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 461359685 1250 461358435 461358493
    0xf17040609050d0203070b0a02070f0b04031a010e01090b0d050f0a0203101a0d0204180b060a0f06020309090403050c07060e040c05040501120e0102040f2603040501120b03070b0705 79
    0x1822983c1d42d002954403121401441100400402c0c40c501044c02042414050600d00c4021a0021703268001118140c0080c40140c86048441c0c00c1d0750b94000801420303d041c0e551030382c03500c40c040c1c2c03c0001c400c001d001b810344150703002034001300081d010841c10f012202d00c454980020f44003405050040528006da00c90520501915008604010754403120460013294003d0f203400380c200c0900d000090080401b004440880042510300c501004602c603502489800d048400380d64082e1141c4290b281c0030180c0c0103d00c0540c2c03003007051510900d009251550301074800e2a180d40740020400055050143c280c0c011070114035645001c090030b14283c024002812818030b4154245490b210000b0412071045110400c59a50b401c91000d000000f0340483d030140005039000e0381c0385507580300c1560320341c0014002800541c0e4040c4002d04200004800c031403ca03030050f035540040c40f040d502c1c42300c024610b8101d80c40c3d03d071154410004403503207200b0240c401e80340214060302003603108889030b002403401e50f60146 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 461360935 1250 461359685 461359699
    0x31a04031428050a050a030e0c0619081e01051903120314090a0203060610030603120518030a050c120c0d060e16121415010305010e190f0f0f1704060905 67
    0x44c01e950b50000c10340398220128038000c0ba01450400c0e01504117060450364a03041100014041441c0c5c1c544c8172016071000072030b980d1411071365030741c072011f941d00100030f91a114901d240c80042280c0c1c50708007070100c20603040d1540d0011143d03503a074650200100c80c0f1490b402080c2c03100b405840c040402580207a0164640000c3c1000e00415030001e078071030000070003413403091320341d115521a628401c2d80a03501560b40720824010110300b0030070140040e0050f0184010155112010300640d04002c0ba0b41008a0360100060164511003000c000070340c803c41000c68a2803043c003404001c9561004450b00249004010009411105e207900b10704110345010400010219a4410440003554982d4000c0c1c1941148804401600d00c46006044c44c22000785410304c2d01364480044140807065000d64000c1110b0401c503500b80d010700d4083c0190003002080500b4540c103883c10180800c090007000c81c8218441d80e01c4031605950b603034480d001b010003103445001290021034103014250704610003102800f011a440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 461362185 1250 461360935 461360947
    0x90a0602010b1c0812070c0b0f06090108011506081306060b0904050c07080d05040c12030e0909070f050d032102070c050604052808030d1b09031a0403142805 69
    0xd0000e200f03401040420903015030009441c5440741501019080d4000040d20302400c10b4404509c00341016500700e442113804200001c0c07031a805200b40b00e4601c101c81c011555052a00d4404ea510000041a50500c01e50300106070340001c00a2140d64058860003d400c1c0d100d001c1301060008544008080481d101c00411000d00400c0c000c0081d80c04104d440000495103540b54a4625050451a4072020042c9550040c1a0415400280328441a40240e51040c101c1e134507081d400d69140c0e15486111106504820103010f64180080104140c0b8007074202369081075044548001e51305012682904038617800b02c3d2000c2088007407001d501c01090201e42c054141410b00d40010f109080c0140101280b486810303c9158294102001d840100303096400d581c0c40e00400484080031380403800c911a0000c00311040001014007480d00300c01601d810150034446243c03009404070282c040608103030207200c0382c480e600c04c030700f0f0305031005000b02002902c078601c8808410b840500507481c81c640c3c44040c00707010700c22 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 461363435 1250 461362185 461362193
    0x15050102190b0406110f0315060a0f180f0b0a020d050702090109091b08010222060e061813020a020f01050c0f1809090607020f060601020a080906090a0602010b1c 71
    0x78007840290005000b1209460b10f1810b00020044050a0041038401064800340250400d001d544a0504410a680c40500c9181040303583e1040da005200800c11551494030001d1281d00443e001d4210908031050064580006034a0150701c0d500c42c110302c1800040c07501d80d15034148000461050141480c0f0b05110301036000600c0781c1c105014010a444d2b4400414091140404444001f8050700200d4007850307403121040c0307002c1e6000402c0f0801b000700c903c8000342c10b40f22902482c01101c021b0b0b80c0d100e91142c00319080000c10350082e4500f0340e000f003400c2595101c40c2e82e0b00f034401d880c4c1c0c51280001031391000c4c00b03d0081c6c1010008100300545d13915100821108910100c21541c2803c41d582643c1d98403144841c090041e0aca900c9203131500070f42000c0402c102c440740043c1d09406140d0b19000c80d040d01002d0801180e48200c200c51560040c0c002d05002800508074034090401214001d04050800d654000428200c0da480c0e4420401070703444007e220002d041c60b4100132a11002c41035440640a11911 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 461364685 1250 461363435 461363473
    0xe01030c09020c06160507060e06010501030b0f0303070f1511191106011e0e0f0103050120191e03050f070c0c030821040510050f060d030f02071815050102 68
    0xc0840c0c5d485603480142d980b80e200b4402c45603c0ba51142042102115034032003180e03215001d000d0030340420718001e411055450081c140d0114000c00400031031600001c1d6480446511030400708503500e82d540c000080341041d960040c01da41543d81403409482c0c4402813017244444a40c0091102480191800010a903101080c00c42c1914848980c50035420540003007106000040d40c001052401c0360350070300100c0045000c0b402d04070381c0180028000705424400341e013400300000c074000020700e904110070324000400e000c41d55510801400c14034000b8055080516840700714024000009641d401000388646800c5685070300050286030034003680190b540d800c041036010340805081703400e01044505030b5100710f07109002000c1c500b284070340c1d031810f107450100c4d55104400c00a00d410b0b400c00000802005660401f5841140028407034080440c1070348007903600400032800c540460141140100e03003c0e580025980c00c0512200c000907008004501400d6010902c0d000355045400000140010484c003007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 461365935 1250 461364685 461364691
    0x18090b0a060e06121002041e050a0b031503070f0305030a0f0306120803090f07080a17210615191106010503030301230d030302030609100b1614070e01030c09020c06 72
    0x40c1d08002000010b500c0d1500c0d0604804140017030a00000d008100030303000d02c408400d01205003047d00d01c481d40315810418a01c1c11405203054080c030600026005a000004092130040b029090b81d070ba4940307035455030401d40250b0708140c941c0d906c005020036885078003d07090344103a07000f071504100c00350401043d0f0002400f0210042c043c0600400482d501d02d00c1030203600c0000841a049881640d56008066141c0000300c07001c2d04e41061030032141c0c80d444900000c0307030002502504605c0300c01f10030a15010031f005001e41483d404c0b402c40103c049110000600070310b4040900007410240260489000300800058020840342c0d03042000104030703540f000026a410354201691600720503560150509000c506020100c2c0d110a0303500c07008041c540c040c3d0044ac010041079598541503038825509051181d01d80c49a40c000403002c001d014541c0c1c1040410125503071040c00030000c0860080c44051900286401c100345045001004008020b4260a040010004008254100710345003070340d01c3d2620300003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 461367185 1250 461365935 461365939
    0x50a23010f1701060e0403020703050d02010b03030d0914010c08060a05060412030c03170f010e2d09030702130203090c1905100908010c0e011101020708030a020703050418090b0a060e06 81
    0x50b82515100b03100a4010700080c00d5881c4003104d1038601810020358400d00c500c0240c61501540c0440e40401d41b06000ba840c1481c00540210303c3e00da49800890010300ea0650b00382d645040350324110300c800c1800c2c02051044d0069680360455410031000300544180b556220a229001c00c000030450003001000d0341d419550141000c8002c80c0103404c4c00d4540a00d4901503005804a590400510b4294049210f0507901c2194800210f42c2d101c0c6102141c08400c548441c00e604030744104240d000c0c804da0140c80d403141c1a042680d0500400da0b011130000301d603200c0034650b001d4000c000c0000078501000301c1504403c1c1180d00d014810121004014220114001c460040000a120100c154000c05d80c0340c0051603100c008121160418100904c210003001c00c80e0300207041c0d0414078081c0e403014000d84200740d0308203da40c1d146480755502d800007940486801c6081c00028040020700801e200722120b505402c451002c1101c0b25146005004100f0040000d204d107403070b14405010042d0385503c070f02d80c03158003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 461368435 1250 461367185 461367209
    0x16140d1205040602040515190305040b190e0318030c04090f0611121302010f020606010522211208040b060d06090210020a0c0b040e070f09030501050a23010f 69
    0x42c03801d10740060311541c0c1000390861000003080705460441d00080880c81d507c601c00d0b2424201c03251044054581c242d80151000072840007041d00c050300d40b000a1001c1590380c0c0c00182c111000b125443c15a00004034401c00d5518004000d100f5050078440c40200311021582040881503d50b42c035000000c00b22400b4184690310a0300120040502049a16031120011464200d00c2c00e00e01d0000c0b429503414080703002580c8200110b0b4101e00008050740174090507190503050030690365440c413580e52509841c000c504000c000004a1035074205108481c07041050300e04002d40c0c9141002030b014410740240c030081150100802020a0100c66031941204084903060302d04c110318200301024142c00c0c0300203135110440c1070600c500d0540004618520500c9604c0e24011580d640301450000e004922840143d68202000107608030701c595403031442010681852150140c0b82d0301e409085880c00c442d02a02261354140030401c001120400840100000c10050403c4d814890351403100c40740e611403075900c040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 461369685 1250 461368435 461368441
    0xc01150b04050301060b360a030807020f090f150415120b01080a11011103120c04050117060f091e0f0a05011e030204020a030603080705010c11070807030201121116140d1205 76
    0xb07480d04191210310390081c91030111279100e0074140016400300c0030881c81180d0f030801c003903e581480101148a8251103009035210355035042c1d003075009904081c034103a0099031a0440744980c4007807690070020300203044c50112031012500c0c0031040024181c01424950f0301c942c1040b0006682c0d1815021480310a281c292401c0509001c1c40f0700e5402034042ca110041071110402480071100310140040710b10999507040b28107a210170211000a041e82d095400080c400301c0e002c0c650506050b2140c001030300401c1d83c424048a0f01d181e002c9401c082d12400b0141e4030000030301072105030318000c460161070981c005007006000445588082c4806210080c000e54002c208000014042c2d03000c08001c64029503144da40c2c1881c1c1c40d09078001c0549980c01c60208108481100640500281c0c42c030540c1d2400c4000c045681c210340041d03545c503c20704034a0f04d0180d16510403030840302840d030103418445961400c0303484080d07036172405c184e20440402c0c40b030002d40e1054a00100c0d03168880c4240407040c115070b0700018961 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 461370935 1250 461369685 461369767
    0xf0d0f0602180607120806180c070f08030f0f070f0f0f11010603080c010609051b09030c041802011715060d0212010303081f0501090306020c01150b04050301060b 71
    0x440c000c002c69100c0030118140d0280700d820b40c40d443d21900c6581c0c9282040d69080700700070f40c44142d03181c080030813191540001c0b0020058002401a40c0c05203008440c82456903941120701e900032075884000c01d400c5018060703600c1e004014240c001c80642003c807546007001c5001000c0622101402080101701c09040c050359010310318506658043d00d000b40b011589900b45440360754415a0080e1042d0320f001c00010300719045101d80350182000f2a6001848039202d0019029900150300940c0d060081440c001025a103d01c1280c00424127904600c000185078000585410403143c48083c0c502c01c40360402c42080b03844012590726203802c4880903283c00d2000116802801030040c104445107510001100345034008500385d10070340e80010042202c0040c489180740042d0103100321408540441c0b4207000260103a0040d04045404000014407403102ca525403440c424954070241903d80001028002810b01303003e00310181120b80015441c14440c0c10420800d2034060201c1c0c2d41c0326080901d902d601e2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 461372185 1250 461370935 461370967
    0x100921030b0a0b1305030a110910051306090e060709050d0503070f0c240219020117010306020301170f0c0d0c3b060d021201180803060f0d0f0602 64
    0x1240014240b08911500d540d001012a406004034007888619000e00245900d000202c4000060303110000522047d42c4c0020301c0000e40000d0155103a240300802d010038141c9407a9000040b000980d60301003003051a22441e641100d404103d800495040801009585c54200304541c0448500361341c00195200641800780c2107000e80d20000b40003045007030303078402880400c2d008882902c860354040244103c080840303140c84a10104882c0150b00207991408400307410429080c02503006040440306910f114807482100d4000340c03c210b074400d5000c00140700c101c00d440c0e58426a140510000e21422480002a175550070840d0902845019182c901404008402500308010030f200905240d81541200941040f2078038240c10f029a5008090070080c40a8100d1405006480c0030f8a0400c0742c2100360280003610020b203200035160f64030f51480400d5a40d03821000300c103281c001d0f0385c0e0540700e00704581040748402160380356903c100d14804150010071007c04802d00200e41c4032100594543e4000048044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 461373435 1250 461372185 461372201
    0x60903080606161b090906140606030f0114060d18121803020d02031204030506071b08030711120406030501050a0e190c0207090509150a18030e0604030c061110092103 73
    0x1c544c20701c0e4951b4100702c0e00ea0402d4a1101c540c00c0480700b6940c401003808031074001100e4025141801100400c20320f00c05803500720080c2400392900d0300e40303407500d0b82e40c80948a040c0154650502c402081e141441418034003180e0400080c1303401020f00901c0b1090003009042c0d40000f0f841071035801814001c5550402c04200201d05a440302600d541d6603081070f5456031001c49a08010910320058640000b490408417440d0300c0d40105402d043d9201e900d0110740390380a00020007054841c030411040904254000b50005085070b94022800d5810041480110190355009100b002e041c2c0041c00400d09140c1407203111080d46820015855201210403442d1000319484810301301c1c136200501640b1000420034180841010300b0342c1100b9210098118100c034444120701c0701150283c1800000079104140c840100e42008200904203516034543c500c400c01c06504c03440201c1d4034a445512211020300078900d844c1d4a841c4100301810b03031600c07200500c0c010500b40c00f998040650791000031500035441a40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 461374685 1250 461373435 461373449
    0xd030e0109170a08010503150f0423030d150e040f03030b0616120f0207051003021903150902130b0328020d0b030f0c2704060903080606161b 62
    0x10714102c031001d02c006551110b0440c1c000030300d803138001250604000a03411002144040702c1030141d80c603403000c080100009001114660201120410104070702ca0a08820002c120b01071540d50340040042000c6a9241800800d81d507102c0340d00b0403c0000802c5050381c49034001d152614814080d06e400c800801103100550792203035002c18940c15542c0c2075003604034400e106124038841514552419035114030204001030060740034400511090030f10352030074020001142030140c20304681c0e9144841000c0722040d901d001a5541041d20240d040f90390083c002400c00640c11231600c0c04003000b80808244501910701c070340c00700001041030748029021006100c1c103019002d40400d40c1d00d00307030308010b9030041040060310fa0a02d04500303090700e00468881410030200c801028203018900034411a030315481d91000c001c8090072800d0100c41c2c840030b10f280c8228400c0c580050408094600580358180240005000c0c0e107040c00a43c4242070504141c0300c210350000d02c0d81c904410500c4401d103410070260410740d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 461375935 1250 461374685 461374703
    0x4020325080307030f080a0b030c010509041103180c01050c0304050f010e100801030201140a080a0e011805030301061404050f0d020307080a0c091406090c090a05100f03050702030a020d030e0109 85
    0x409055110324040c03170001c03080d0354040140e02d5640248080d50f4045a21030783c1500031000c1c4c518150b002c0c2d0014040d0b21070281c0007207904071108620910b00c1d002158000f04055140d03c280d00d1464051100103502542401c00070704049083e41d15560324021809034500404800d115000f0700e078041c4100c45c12501e4000e120b01548003001ca00240142d200780706c204c0c003044100d6229403542d141c001c2680c2401040703641d18101035440f514003001401d03620112604555864103405503642c0b9902001b090345000304011540c0e545011001007040c0c88128094007220002d100504c6103507100c1000c1403407000c0484d2406860b00660001070700700311056000c005584241c4c4001c0c420006810310302c000319955801c0804c01c10451000c80120700c8030485403d50303c400c81d8400174907042c0080c0013400e41210082c04100d000e60300d40b00483c142061403500c2501041c0700c2c00d202ca0301550305000d1280c0c82201c9201440c14210303440d101942c0d92074668100c0e000d042d1103c0450020490943c018003040760800b841c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 461377185 1250 461375935 461375947
    0x6060f030c0d0605040c0e0d021c050601140306010303090501200607020106051e06030103140a080a030209040f1a01050f12010b070209070f08040b150910090b09040203250803 77
    0x203600c071540b066105001450908a0002d514035041c46074518100c02c0392240c012040469041140b07101006800700da00000d00c0140d0754441941c0040d41c0640d6210b40000d040650403c5039441d40c00e0104010705200c1e9118000500020794451041c0040740d00038204400c00c001c860440e0001d0182d42c0344482181e1040700d00b004020350b4150005000c4840c10788403440400fa00441da05010300311300c1c00140e00318108000400000b5101d03c0000c8220309088140c591452155440e03c900d90300103207480b00003e4000c190180649801d10070031210601c001d00c1000010b40080400010400d4401618144280401c14000498968046a03218800c8058044072580c54241c07114003600305080c180d000321501e60024044600034854800181c07829105c500070360b503940d0350b2001540001008030700401a0050b006c4070988034600003d01800112b841d055000d401c006e4150111045070074402c4c4101502c41c00d10000d42c40100c0c00d1004040c3c041014030000e08810390030300c0d082c000c40c0d10a40c014800060a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 461378435 1250 461377185 461377201
    0x1a0717070807060c0807090504060e18030412050303100b030402090105060313020a0312081b160309030503070605090c04141807030b07050316032319090605040221060103030806060f03 81
    0x2600c5000252070341f0076510380300e20a05c17084070103900666402040400c00708160554160700320007407410302c0b402c503881c0039204c041c111502407100d241282c07690310110501003400501c8021101a1400d03821990030b40c0b500d500083d11550040c42054003901001000c143c5440750303504030b1401290058200381401d03070750f450310a44c0c48034228503e20024402c000401c1003014112130000e007c3d90300403612810100003007800300c4240003140c0d0840901141b0000000020401d1000c1e2282d680149000a45440c00c01103030783c100b5001005080c841c61030000d1f42c210001ca051845600107403192035200444403002c03a0fa608d0002075030405003890501804200c046c0d40d0103c0194800d0303402000c06080020411020341c160344140f46100250415941094880c544070416123a00c500c5604c11a1080381e030b04c40200b07040b200c0c840c07010b4404940702d000f000150304080d180c1b07045440d0742c605005445103142141946407041030000908010761a07020900d90764426040c0d0700d00c91030b8041016a00d040c4201 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 461379685 1250 461378435 461378447
    0x20408070806011e050a0e060d1202160f1a0306030a0506190c0306030c0b0a12020c0c03010b0603010f050d030e040c05180906030d050f071502041a0717070807060c 72
    0x708029203d50134200b840c000c0900010071000300c42002c0c141d95465804c180b0084020300d00204540e4004884207681400300c2c00c0e098854107101d1030b6030058250f040101c45040f404e03100541186200a6003440108114500c8074011216900203448561302d988920000a04048032100d02501ca4032400c0c091000c1c080041846e0075110040050402608002c19010f03410b440c2e140c4405400241070b4032081001a507440d00401e0350345618a0045214140b11401204980040d5151003031a48101032000c0a41000d202d1045000c1d002c41e000e80c1950324021046461034014000c07940a804803000b910200b5005d107044645484c0d00a006009004030034400600e2a0840381d5002d12a0340c050685030a1402c3c400600340c047c00300030300541441c8a030014240d82c0c5900100700719085030801c1281e200840e5455940e0399003517140000c090707a282d01d004441e004503200f503480058035070004c0141400085180880c00c881500d1080c401e501d6031110300f03200c0414090900c000d0281d905041007030b14013681c401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 461380935 1250 461379685 461379689
    0xc050c030708091804020a050d1a07050409060b03130609031211070c060f0c02011d090a0c0e0303030c0a0c110607050a060f02070203280515090c011b120302040807080601 75
    0x280c0e50a62800c1c205400401300903041d1806904041c54485c1440982000051049000c0c0110448011f00791109507070180c1940450350980042c0012070180041c08a0307029a40041c9103001c7d0060031030805905d2048440c1d01e5504c0145000e646600070700401d80609068410941d2900c0704001c0d98802d03114496030b962011400311600954001e000c502030740108001c0d00d81d49541d030765500c41c0240d194015156a9a034081c04c00600360520545a0300b5591001100e10401181102144144061030081c01100305144030f103104c4e4005204105610b1803600560760704089a14280c2c202401c1c504081e00102c00c000e030550740002c1c0000c1c0020030310400040400c602d1f8410320003041004a440e0740d4208078010352030000d6241d006242c3c11040200011104e6407244600c0d645c4500500c10b0340d03111440c0204503141d1150780c045a10401005400c00d00a81740354040c01c1c01c120581020060080010b1001944024060004050944c081501c40d40c1924040c0c0007080c101c4620139100e105407944e030b030070034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 461382185 1250 461380935 461380939
    0x11d01031104121a13020f0a0b0406051309090503030a050703141f0801022a030c0d17010f05010f050307210e060a09020a0501050f0c01020403030e030c030610090c050c03070809 78
    0x4c4d0503c1d42912004041c07207840340c6000001030149009603400c00640803004441d26500014032540071580740507543c002d1000740010f8a03119504e900400000090200950059106618103410113000c902c0100407241d105462040008580d0364180c004d80050030440c8119200360b03000e504100c0c82c1c1e00a401440501340818a503862902c0d42c0d180d0740750a130300c20380c152001030186a14507010001518000d10520100000a40b410500081e40302498061000b560700c0004180b8140740c0c40508804d51218090198552042d80041c00d10340060178000900728480d00304000080001e50b4240b195149130003c03544080070140e006003102800c0d003e003600e404015014000c15002c2100c04200c0e01c100c0d02c5035079006e0964043d6906e0700e001585d103908800c2c146940c4030005c000303071401143c00703100030f0024500c683c0320f0307030703c05ca184800303043c07174103490250443c001e0b440794050140306298196588211002d1074004180c42d195480300b00c8850003003052034134540c440803403501c08014505c8040e020810003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 461383435 1250 461382185 461382203
    0x9050615120d02070b0703030605060d1e02030601020c0d020301231b13050904020307120b0f07020606010e1005070206033d0614091f080a0209011d0103110412 70
    0x40216a03944a02d541d07841800035038048903003004042070102c06005880c0c0a4240001ea80e9500c01c007140813a481458010b00440c0d0301c0810903410366068120498034028070340214118503112001030f584440a6066034401e5003004042801c43d9001d40180c1241c4058800080030328803032501c5800344410580b119010042039884201b460b0070f00302c040e203c20440f00e485da00b09103442e200500417002000f400698140c01a9140447c441081011008010740f054804281d5031900c10140348103518054003460441d0030450520000340c0c0d0000c500ca90807041181c07041e0311020740c1e4000351040d00c00d44800940041c03004c070400c617045003102a41400c0513040e032020000e030a42841100b41080c2070a881c004a94140300040c40164841d24003003405400021f156494400180d00151400f001d00000206031140d0b003080d0400e082c4e100e50544d40103030350400258200b030031007000038121341d00a901e012507811810040e00110ba2081e0480c1d096407224514991790340d82c0340c1c0d046205002c5001025580040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 461384685 1250 461383435 461383459
    0x62102090117120a180b0702270f0601030f0c050702040608030301060c11030a2414100902030903130806011401050310050909010b04051e13230109050615 68
    0x10341c840c815040000302030083c2044860864001140d500100424010004001152000d400c407410090010300009214039460302460300c104080d05c52400e000c9101c0528006070545000700d601400703600328603115281105561103d0040300146840003036000c2c0503040400d030843c9250010300920a01d07009803418030882d602c9140039a41da01c8280705890008429986036004038040c034159001c40c01c0001c0944a640641c1e48510040d0106001d41c00c203d120442d000682c0780070144a100343e0034041a002c4019440c000746806041c3c1700b0f61080440c81500040042d003449028422905000c1d2800010030515444412590b40c40009024282c0300402501504000e50b000784141e900c140410049140f40303508000c240661110302031b09400301d03507488808400c13465441e80944d230321400c1d440d0b504215806065418491555000c1d10380303039002081024a40102d020000500c54000203080e1034031b080c9525600380390050040c04005880b17030103400244003131410b98400c0c400075044116500840c8503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 461385935 1250 461384685 461384699
    0xa2417190305120406060803030c0406120b06160201021f0c0807170601110a051c0f0e030304030807080f0412140303090a030e01050f03090705042901030f0621020901 73
    0x18030140054003161052114a60041e03052428991082c4200e0010994a030b0b41c07031507245150070a0b50744403c003040c0802d0501c1070350707400461034440b14441c40301800040e0103400416428030840000d2100c41700700404003419a402000140c0140d030200848812a00c0e07260720520013030540038000000540c3d0f01c00424441d80c413415403400c5503800040c407044582ca6003c010740b4100c0344810074404a004056200d400319905202011a411051044884082071000000c01e2800c8036031409041c460340e0410a9100c1d20300100369019a580700100641d10b5146040c8004140a04201c2e4025204001400b0881c030031181c4510008900c50380049244201c041c2c0960380f40d000440f04440070b40c1c03000e442d040100707201c1c681c03c52000318181001f03480c000d501902040e096000312500740a59008000402280c2858854890100300094054030709417030000a2100701d0b518004410b04140e1140700e0f2039180302c0d03280e000e84024500500c40c080c40c21005d00d200a0030b280c5600c1c060f4866018200001051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 461387185 1250 461385935 461385973
    0xc0103050127020307031b020607180303021b01030902060d060e06010c02090a1a0402070b011502030f0f03072a0605060a29120106021e010b090a2417 66
    0x80c48624000b0300c004100505540000d42000300008100f60b02e5400000042810746628a00351440c0d901519261a0034500a4404c81619840c40709a5259150820200c1e502003400d00c00310b007200480ca030092086c40d0049014010484010350312101c0060030a28000181e84450221243c902c0906100e070754507001034816007515000a90000400b50000300d0403c8582d11900303014030f94903143c1c40b014030a072000c10102d801c83c000454030380c0b48450041c04501206034040c0c02c2e0388c0091004510741401000c4011060041541c10001660f010001c102d0041c068040c000c16002d68000c503250401041d501241d6031210382400f510310b645000b012850ba030810045010a69024102d10486008442c000900031201054280070b00d810521030b101c6d001282103082070080c5030781d40c02030000f21070130a8500e0040d2004031b80143c4980c07402010f600c0d15151081020341c0400c1c85c0e40001051426201000a00d5099150010800d2030920b40403e281300d2100346034001e18844011109a800100b15035062 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 461388435 1250 461387185 461387219
    0xc060108060a0b062508190801080a050c0910080d2c0102120d0906021305011713030c030309150203090708030708090402160507030f0204141009050a1d0c01030501 72
    0x8513904200c0809110784051155031164051240709140f4992a251981c46404c001c4d450707241c5030707c16504801d11aa0188090f409484090042e00c4143e010744d0710a9600c82c103003035400c2e0050744502e0000f84a1080d4900c05001041d0400644001e94541e6400810800c0f688010360b00140200c1c14a1044003450701240f840510181c00500d1040c151200007065900b168142270f0700c240d228000203000855030700190940301000d010340d64151713041200141603030703861041048002d0044c00800c00807105288030900082d41608041140081e2410110003401d8070620252840303034100c80075540c0380c2142d030007548100224000d44480c1516030340c82c1071b00d900c0744d840080e0240c41d043c0502a80c0c0c2c030f45540200000d8804484281080980340e0300d8904111850b4070540e0320840e1b007036140042d414540501c030500b05000300860842d1811584002c4000e180e4090300c40050b40d2080050b8089109070300000e05081203c0500070940e004030f6650ba40c40985400150020b400c01000040e5000032480c2c81390 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 461389685 1250 461388435 461388439
    0xa06020a20101a0a0806100e040f171b0c09070207180f09021909051303020d08151504050406060e0d0303090807080d0f0b09091b0a0b0c060108060a0b 66
    0x30034a106000640d001d007007009688180d40308518a083d0050341c60842a0f402025420003400062402c1600009000c03401d82c461605800d41e0b80070080011305c1e134400d10300456401820030b1130035162032009204a00841c00c44000e004411018403141c03450000e040c03e031400040b60b10300c4650703807082d0b0100d80301e003218440c0c20700d02003a5807112600e07d241030700040141480038000203840740040e000a1900400c95000e0020141c82d00424070205030940900daa01c1080c0c010b00740d00b0300e00141c0c1c0080d40c071035a500140341041402c0c0301150302c00050506015001000030500010042c0c0701c0031013800d96000d48226482949040b6000641d9406040001e10300c00005144640750b1030070b1348080e409813400d0081140c55403010031090b40020321283c05407030402420b020019401c20034040b030384201c41582000380e1069248400700f05a40c60001a00340d0490690003040a030145080041010400b00c0d8205030070b24040030500c500144c600098141c12502410304803150354031100340c1c9508482180c00120307 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 461390935 1250 461389685 461389693
    0x20c06072a030c0603060f060c030e130c200d0c121e0e0f0a0e06040905071802030f010603090b0f041a010b090a0603020f030412110a06020a20 63
    0x401045240d40800901001400000104490403140ca40c07a0380700d50300700310f0f40070706800340502010358144075041c0a03154444803902644e082c070f4009000750382540310080c2040026201d00f42c80380c0b0b440d140c10054803030841c01407107a00d03c0c0b4000903042c41140b24071b4020b03542c600b031804041503600107800845900240c07540342001196482c1c1c2241c01810055071001d1106403100b01000c9c10f4200d0070520a02645d80d00d029101c21858200308800303400285240c4207000703030342e4140164100818a41c0e088031080310005400d0401740f8000b4203100b520391050009a11400140303200d82141d030001e42c40742c2e40003800f400d55a038a03014190210380c1d0700580a8441400403000689000c404442d031500035010700b1071401100d80000c5c1d4804603420036004000c80c0c040106041d501400c1010b1040c01804113401c0550600401d0459144035010082010b003015241a045403145401400800c41484104098642c100c44505008010b54848241480003403660b40b01034181e140003244600114054074050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 461392185 1250 461390935 461390947
    0x2010b01180e070c0b1e010501051309021b0109151d0712080904052a09011d0d0f0b19050f13060e0d021b04020a0c03141201170d020c06 60
    0x24080400c0b00524400504c1040140107000c1102954541d100b51501c0040300780c1030b0a10000d2002c0060182e001c9414060103000f141c03002c1250030010002e0b102000030050f187c140a0038a00d6240412810940055203480070301004d01c284c1800303a4100034205642032044a80d10b01c889030100300130002c80c05041c0c00c01d00d82841a402c2c2c41c081c82480c240900041418014201c0000d801c552090351074441c030801501540340c11411000c0750f07403450041d034001681042d000c0400600b00030190750ba98045118507031403a903080c0c1d881c840c0c00c594654000d680903141c04000d01e80442c0c4000c00795102211480f0603143e00010400c0c07400760382e1240318181c010704405d0b00c1e00c11043c161128030003130445406072513182115024808009280c0c1c150369680c0200341c01c0c2c0303006140211902c02c000c01180a00e0042028440b0160012002e40d5500e905103041d419074150065803038a107004011301d1903d900040c40c0006181c00c4400341c9202c101403060203907040c500315a082a1382d1002c00900c00ca4000c0021b000f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 461393435 1250 461392185 461392199
    0x10b0a14090406050a08030c0c040501051005030a02040816060e0f060901080a091e06061e0b0c01060509180606031b0d020a090e0607020d11030f03091e01060602010b0118 75
    0x2901c28200080c00100b041503e600009500b070b20280c011005603880802d8040721024100100d07a1019801e4400300915414035000c1010700c031802400c4d201b40300000020548050490703044030024105d020680e00405a9030001c480303401c4042c03041c400024000daa08698901d400b104243c6550002408949815103040054401040080c4007140c01c82c0d0710700c25030001c0340c02c00c0940720003d0f98000c8550010105483c200341141c00c903400030840300384065000049080010859000d4400040c15691982510340c0414050700080d049a5003201500082c440c146042c0c240d840140071080303080d542c8585d81c0c1002e041e611030403070b84900c20700380142c0451409818181400c1c20b40754000b0740101c90303e1391658a8102507030007007130710350540d07901030070400c01455818071011400c0100707031030140c1c0f1080e0340400042c0c3e00c0c00741e00d2200d02a054004080341c0300b05010080000743c2c01448400f9410101403140745030007042c0360311504001d5420410404441d6120f4031010a520510f19130f040c482e142440301c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 461394685 1250 461393435 461393437
    0x6101706040e0a05011e11040f1413140106120b0a03080d0227030f06090a021c020316031b0f030f0c170303061c120c0c050406031505010b0a14 63
    0x5210b0402d402072080750400b04001b030203429624980c6448100e203551910030060120344841440300c40c0e4800a10003409054480e802010444224000c540a440c1010b030004058088208143c010300b8500030704d6801202c19410014100c1d1059200c00c83c0c44105028a40c007501c29078400290b0028402d4401e10004109502404c803030070f2001f1005083c14010858501c03101010500b030160780190200da803946180030000a8280504174004d030416080c61000903a0314000340e08000e104c0c4a4241e0403a20382d090480f4000360b203580080c111004580310850304441e01c0c5041c001500c6070310041d0254440481c0700090030701154264822084040d2868907501541c1d012a0310403075254100c11030004540b10440c0033f807030030414090f001d995241844c10400c9142c0c0b84040350f40c3c580c07071280c6000d200452500c80c060b4a44e120b0034140140e01110501e001505100290000b9501524012002c420701098030003680c690074841c10100302d1030b41c807102c2c5444d05006480c010000110304011403604124800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 461395935 1250 461394685 461394701
    0xa0308070513080c0f010e0a2c0106080a05090c010c020415050303040303051b011802060c0c090a02040509010e0906011502031306050703021b0f06070201050706140610170604 77
    0x894441e052194460001c81d110780035500039030090b400000c04c0095881c211120301003420f82424819090103250001c540c4c041c04910500750030300c1c482000c01d56099580d00160350b8044010350349000c2c0e9078440c400a010510300390782907404585000d00182c0c078081e002401400d1940140c40c1e206000c11700f9820040a00501112010014005100019103440400c054000340d442611391340d445944210f1000300e030820051180d00e550f81004145000d1180d0050340d03044040e010340c0d506607292061517aa40c5410040c8070915000038000040000002c003070f5029109440044400030304903607880918920300716003a00e54181540250004200c60700c0000c6000c000c540850040d42d0404100e044554811200c031362064010900c006056820103074188404030480c44c0e90407000d104842c0050100301d040780e072005628060200094820103580c041c0c0182c500d101e40c0180c09101486408035524486041a20628040c4117403000300b8202a025202002d6041e0f0134188201041e6100001c1101400080d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 461397185 1250 461395935 461395937
    0x5090c09210a15142d010608062d0118030b011508060607200102120309070501030605011e0e060f0a030c0806031219090e100504050f090a030807 64
    0x161468400401c10307021500c0307890440320060030446510781007141d0807802d114107035411545001070038180925880c484030380114940443c000c9942d8010141c224104442c8054030408050074000100c041e40110050b102e040d0995244940c40000f0304000380004004041030180034440b51144901e51042d0b840e81807081c1d04001003906141d680e00c0e0b1401c07070030b000e8220008d079000b02d0160440741504542c0140d00310707805a40141c0b9100c00e0b901c404a01e034403240200c4900030113204010000740c5c400c0000500051000c00c020741d50f030510110b89591100c41d4820140440e05200300000c40390302904109006040d44104600c207003a610404440740c0c00c002580907441082401500810311180001d411480e032592000610107403e490003800184008000500c030f5885050f52003049403041e010784006600c00c0303881d40101d4002d904250340d100070315041810000141c0341003040320031045d0350341c40032900b064070100402c0d1580020041c040303008807a20580c95029103c1035000070300ca4661070740d200c51a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 461398435 1250 461397185 461397199
    0x19050603130f0c0303020102210708040201030e07090e070302041406061608120c07020102060c0405030d0e060c0109080334080403023409060e0c0309101401061805090c09 75
    0x10307500c0030f084000c0c035001900140c1d0701007051a100c5029565510071004891443c4050b1316000348003d204900007840241056180c0b401c0140700c28081000c880503160030003041c0688200204402d0b030340c03851031001380e22407030a10116403880341c1c50711403507409048060119483c0410402c4150b01680f1200c1d0200c82122080000101c00f003e495003090060070701d103080c0c2d60303100c2890000a00e04a0041c0c60401128000c01040003260ba001417101c014007001e080c4480791148160000f540da000303c20280300c0d95400c004564040125441c010740c81f5088030094203e80780c0d5401d12091708081e01403286030b2603406000345050340c20b024100c26540180710f403048480c0000074a00500e014400200e440324005800082c810954804040c0200500b04000703041010604c1c007400e5000414001d0032a080202e000800300700c1d00e400612045001e440d031030b0410701c0b00a941c28004410ba1200344111030000b112428100794401074400b002040718030081c0544540d8070303406140a1349074031080c03602c0c4e03210701 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 461399685 1250 461398435 461398463
    0x5120f01050406050405011d06190605030304060329030730050d0e06070510051008150f0c1314010e040f020301090b0108040302070b03062b021905060313 68
    0x401d001d09840340384900004036081c205450720609503440031075900120085000040391401c8000b9609038402155144811a07980d04906000280500d4108c21303014003002038013040564141d0440c00c4203040c0d201c842410060b01074506081498a40c00e8642d05410444081200c903c4026000d034040b82202e507105100c4290390402c103c203c031010702c1142c45821040e91030300c0721604200b0b0002140030599010f80b41026580d66103880f2100c40c00c03408001580c600c00300300d03400c90420051000d49a081e04880c002d421000c03840103082c002302c82e0319200e650490300282c2c2e45103800301034030520300e0b100703092054030343c113105201c160071460b401801c0c1000140500000d041d540d6000d10007041003100307001aa03e50420300785000b620355008480d41844209018000042d5001608100700c072500001c43e82c40727480b458001080f07441000500d140d45048820a1883c0054912113030200501c00c85241c061807001200880b40265248134640c1d00500501c001112801a611403410701c52003840581d00400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 461400935 1250 461399685 461399713
    0x1090b01360b040f0606122003091203040503090f060408030345012a11010b0904030e0a05120d2304080601090f1a120a061b02100b0a0512 61
    0x3d400d13180e03014091901d07a0401c001d41c0d40c0140c06481090103021040c050300c0d403100e02242241c01d8070081a42d00c4240080055414030044c80f40c1c1c190800c0542110360b580c1003e041c0996650055241103114802500b000001d03031610b0000c88040b50900e07000b860945d555100301d4001103104880c403043e0010705040030400355a101c0440d00041050344c10061407001344032001030842d0a80c2c0007842c08040d041c00f41f00c0c1422603003108140b442403107182c40603400b041c01c00303400e0140000361005c542141511003840201a040715150807103440980d20702d1160340d5607004101496000d01c070001c85139004003501882e42c0780b040c45649030f03030394403119210842480f040310002c459006d03501026441d002640144500c1e0070794010902c0d07070202030f074081c0003460110050f00c0d401c0d03105070f0041d03104600211003102151410b1107840311107900980c0410010040c0503413811070743d40c40f010804c01402a1705071802c40d07107120701c40c4424259003d07003401849410039040c000c1d00c0082010342c1034036200c2c51641004c05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 461402185 1250 461400935 461400941
    0x81b0420131701052a04030f080c0d031505040c020a050a141902060301060522063b150408010216030906030e06150d0b0901090b01360b04 61
    0xc018201e8101d84182d00d400d200c0400d4901118114480d64107010500001400c0c61818007041d01503150f20b0801c42c840361a43e100795102e640c1c8014581740010400c90140451800034216a09500003a0341003010448822021111703822003030f1407080301207841032051341090b030b00c05c0d2010600e0340102c40000300a81c031114584841100116001e204441c0349060801042c41005505213400782041c103000826030024005000c1401141e080244c01b2480200d4840d06943c1000025520341041c0401d0303445150003040c00d0300300c084515403003607440303284001c2d1390044040d084081c1c10240401c2c0240c1d000c4041002c0c1c03001c1501e489006031804d01001c54010401c0c401040101442020a00d0080311480c2c0500031110561001d0241850160800442c0380045070041d441058000102c110f96501c0001550f00a401000540384103904001c20885d28015402884024002c1007506400d82c2c0e0381c0c504460302d1485420f0840081c80200850b527900d4052031400020120380d5902050381c00d482e9000c1811 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 461403435 1250 461402185 461402197
    0x131503060512060403030b010801081f0609090501090506010605040509010b0c030f0a020a05070b030f0f040501151e050607120f02010f0908090907110a030e0310021210081b0420 78
    0x2d03811800900c0b041581621580d0814a407e0070810150341c0f42000051b141c02c021809041d50700761031003280f56908202d51025000e0700144038100606180c1d41440d5000340540c1508075514410751002060480c0070304d00b80c0782200e00050811034141e0070f0000d40c444030341009103004c03045e1105020214018000e4005000034a0050307004003200096420050b00d0001240d018000d1520100f082c06040560b100240783c1c481d0541e020003a45407198600640100702007180301c0308501107254080703200350713840c41d44001082001030090406034903a01003200358810034000400c3c4490394840c40144ca4020031904a49850302c0c000041c0070160b8004005c04e652460790212100000065640960725288080300c0d04984a407804014183d5021a141da8035143c0c50703406003c1c042c103c0705070b642135501004003140400b9400e00542d22000c80c485503076003694081e55100b10701031307081d00007140422001440d040b09400b404030340f078000c440d60380c1400000d0030058902d8100030615004148200800c0d001016 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 461404685 1250 461403435 461403469
    0xc0a12091a040618080d1a06030907090501080c180403170c0307080a0c0e0f04020706020c060415021306030509010e010603050f0d0c0203060a0c12051f0602031315030605 75
    0x11441c034052400ca012a41034140d4a00c135000008103800100702000e054901e03074407404000142500707440000031740e58009003048903482103002017003141c1c0c200d02141441c121000c03c0b20078002c82e601c0e0000941c403640516407158000d06500d0b2601060420490100c1d00103010742400c0301c800400d000c400e030240303d00316010f44065400200744903650790f01c01216540540c60000c20403030f40010300c100a181c00c0d4003022451003940c503405003203581d44d500c0d070481e015942d01201c219943c0762000821500c9120884054414103040c84082a803240e49000325043d10840400e035850050900c942600201000303012a90150b682d1444056514000d208480145004100030200404220707000c0d89444207540c03e000400401c99514801614001003043d0048041b0b00081601920818221000d490364a040d804507820401402340356148141407111020404128004168071110300780d03664482d0a03000440507a0b02901003090012041c1c8601e01904146800700c0c007969504001200d02140320f00c100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 461405935 1250 461404685 461404733
    0x18010906053106050a0e1510080703030912030e040903080f010b07030c020907110d05040302011d01080a1a0d030306050a08070303080703180c0902210c0a1209 70
    0x8003200c68820740d0030304400c82401d2601d0101031490b141141260300440000c1c1140e03182d00204564404503000104d01402c00ca048070070003614130304044444082643e4481001040307241c0070540c000c0114200c8213598050b00c1d412041450460228003070180300710198100405440e102c91030750341d980038661a00d4000d507568405070030070030562022490181d2000ca006242004001300003a0064443d1102503011202c1c41c1540e50b90403815100c0f03100810b80f07440f483c0101500000c010b60090081c100790f034000c0e80c0303490240400310081d0040c0c0025030081c0e40411020400280c061811f600100d450701c1850400a070300c02d4115000c076050116011044022903201e0310f0500c96410b00c04100801440c00c003008190a17441c5071005040b4407800782042c000c140e21b0f2210405112104945d445401c0d502c00803480031160382c0c900140083d04061030350042120301903002c01074095800000b03401484c11100c090b2070146400015142001d60303146501c0f0042d214441080412075900c442c4501003441014a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 461407185 1250 461405935 461405941
    0x92503170310090e07060c170c030a03050f01120f0201091e06020c0901050906011107151110060b04090c09050a060306060215040b160201021603051306020606030a06051801090605 79
    0x9144040b95000742c82d206241510000c141c0c02d00140b000101d800508008004c034010f401d0081d0058412100425440d80c0003a0040d48007070000300501009210b540e04018039220000c99010a80c8284640160890b80060103000b0a0040d080c00c0c0e081481410140d518030b90b101031031514940300b0f2020005610413140108251a010b001020400e0021614841d01d98180780005026800141000341000720400d0702c404240802c00104001c0c001501354840e4040440340002d0503011a21030120041c0100250940004c60600400040e0341d0040c2401e03080504200780c4000500c0380310079450412802c0c040006080d10340c40b00560203811103907004500c2a0070981b0103031400d107503402c0c03014091804404100100d074050f640203400900340e40d413040100b950000101e029014032201c40c841880310200340400c01d5045801040700b036402c0e40c0b06d003580380d513500b40a80e102e18084030002d4060f0881d10031000019007903440b141c0e01a4840821850301c1c40e90248940c00c45d01508800c4a065988800b8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 461408435 1250 461407185 461407201
    0x60506180f090c040504080d02030403020a0b04080301030204230402010806030717100e03130506090f061602040507090e13020114030a060311060306010e040e0705040e100c05030925031703 83
    0x600c0b0f040a0540d0140424141643c80c0c02d400e04c034455840b586140d0100c00304003014800d01811810700c0d001070600303420b0b0416061600a951007032200f02e00ca14030f89224080080c1408000200c8450710346810030071035590f500151206040201150361600401501054403c0308180050340d8a40203c02008611a0500c440d002c0b20310f0007114030215071081c8001e0715007401c440300a900b642c400740e900719114881c040100c0c0d84090203020300f5601c0900419502121107100e0914400180221024865038a80b19010386441036940280f49882e2116000180d4003400b445150300c0c10b0b8410714004603025904480d00c1d400e60003e49403103050544902042090140079000d41044002c2181c0603481c50610390000b816260410400900468580e00641d2001100b8400d2000500c8042d00600c00b280000c1d4401e521040180099800c0d149800f07440000984100266481a4003210003000c0c0950b08003040143c2c00c080000320880076001c21000b10000781d0000c50780710010300c040f40581d00e0b4107181203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 461409685 1250 461408435 461408443
    0x6070c06111309240b210a0e010b0f010f11160815090114180f0111040302031c0e1507050d03020d0b0d03050421080a020c090c120103060506180f09 65
    0x144205004a14890340d502c100591801a401ca40d04111748980d14005122a0700101009250144a0410482c2000880c1400c0e420402860304000300130045032940030104045108050301c03d0303002608500e0855011406541d03004103001e03400c401c541c1d130300400e002d0001090895402440c40d6403c40c041d4070003400b12901c03995800ca4583c00090196004c6003403032550040c0c00030b00001d0010041044a41002002c1c44a40028518240284410585071611210300c1e4800d11040380a8450080c4444240310f40c03a1524076846626a81c0c02c0380c0211902c1000303416110040c0c8441e40700e4003001148d0005608201c03802403507450b42c90241c1c8640483c032181d404c49404289007806031002d001603900103a400000c8905681034203411070308402c2e0352001402e003203c41901c001c00300c02000500581c0c003030300055191440c0c4000c64084c14165aa01e280329443e0051581c607500d0029510018400140070b03410040d40498040e00341c400d0401200d40d0904140e4081c1c0d00d00024010040a1011410080c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 461410935 1250 461409685 461409701
    0x3070c08061302041107172a060a2a03091208131407030209040c03110a08070909020103020d05041203050619120c0b13050a061106070c06111309 64
    0x500901840e1920005040ca0b440707098030000d11813070399281c000360340003824802e88030060381140c2945055640700d0350220141d80304481d903400c0010406900302130031034400d56542d480c40d070480180c1016101c1e1552840589604807065070604045292801403044d641e6126902d01b01030754000ca0310b02031a050100b2001030840c141000c11100c00108041c0da904600c60410042c3d105205c00700c00c4488801d202e040403030917000294001020018841030009105040055a002c1d0b86000c090b01c50780410081d04040c28070585d510354001c0d0508009900c00e9034082002c007801814050301e41803009500c007040320400c0324100d9100b081070304c0303100940d036062103810307802242960980b40100300c0d90342c0002c459516100d100380e225910742449040080c208100c000600134800c40a8403140340040043d880e0505004140c0507040b0603d0000344a48103c42383c102c62218003000d8041500c940b03d044034560300c4c0d0b41d401d80d03507a511941081c448064040040003003090012050040a05121120b401d4501ea4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 461412185 1250 461410935 461410949
    0x20103150b07150f020a03140603010605131e0e0a150b0d1b0503010e0d030c020303070f18030816030210060b0301211b061b120c1a01030503070c 64
    0x210030a00240074900304481500c1d41107181611000300101034440900b00c80425000c003e4000b1460701d103100c1c3c042c1c00a111141907040f51043d6a81e454091508852240c41050f0340404900c100c0414400c2c9603005403d409040070364540320307400036042c4205845960140d8556071340940300c0d42c0e061101340001d8406000034a44140300030284800014007a4100210107040c1e40d144035140091041401d24900013072101a00070f1003203aa0044040303448110320340e82480440d080410fa903005900c00b0040340e200303900c161980c0c0e2259112080172910412080e10b0049131030313004074001c40482d030040d014280b900780102860b00c200860380f80007410f00200d1490109100c0c11b00d1070a000c0c816500060700d06660207020328400381d50013070040c032040b8041d4000141c00030800c3c4000402103005094a0415103d560f100e06e1110803820741610201100e18001600100c0400040400c1a101e410100d100d0b0f4050750144402c400f0b010b980239002c0714280c0c0b00b25860303800091141c003084201c500c0c0800070901 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 461413435 1250 461412185 461412221
    0x4030b13031e1d01030b090403051207020a020d142b02010c1d10050f190912020108060103050702030c10021815190c060c090806150d080c1c030603020103 68
    0x2e900c00280c0004038443c1d2021909010f6000401c080c0d120350300c83c04d03d03d4030040102c0d07030300d003418200641503501086992101c0a00000010051800003848000e02903001e001d050900c074081d03c0d2150030804441744041c3c14050405030401050303110311908000d90a401420100051001000e4211140b00b00c00805200c0d220000c40d400c1403107200d00b0110003900b42c030011541c0c0311014003120f0900c6403883c0e5400d4407101040542c013110252010030132403044c5444d00b20f03050362074180d0310b200089641c034000e001942d038000246080d44243c1140d5000b01c0680102d80c10021000340c0d040c2040544010044915030200d1300700da01a0300c07603070a035140b000251010000c0d03c0c0340000040c440d03c60307980c1a425402024003a080031511412a0b0030049070031000402c0310030151803008000300c0562050720780621550000c1741e00c00300151000160300c507000700780311488009555005035a4001181842d0180900d000c0398902019102e10106801c589541c0001d1440c250310000d400c440440c03104822481d8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 461414685 1250 461413435 461413487
    0xc03010608070509090304050306070c0b010605030124051c0b1f0203040314030913201603082d04030206100b041205070b0408151608010e090304030b1303 68
    0x16021849906656050722400c3c13181c0d46541c0301a00e18810741d0b11494151151200300074440768030806250744240300b0320640040303980e10242101d56000038020000014110b03034034545156209201032600c0003650400a04200e0441000312002c803002804803081c540301c41408180d440c04908070b0741d1209406090781503261080900079501d00031400001c01c4030900c8090800b003414100107880140d1801080300d8102c0c0020080f010107003840309114450340d05032110454000180da000c1d5513803e40881449481000182c0b401c68001070060040706890070042104a1035102c41e4024805604041e0924915070405140003458400007d11003c070740c00070500140803015082c0308881c1100c0620501200c46042800c2040c01d081030b550104180200009000883c9903000c556101d000007079030096905659032108542c1211010288400012100c40052148000c8480e035181c000707403040202d80c00d20382c6175500d1500e880c00540d071506070020728240b000300705a40f000245850703600764030203912402 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 461415935 1250 461414685 461414699
    0x30b07030e0c0a120b090124090f0905030901050915041205070e071d03031c050a110903060402010c0f0b092d072903010b090102070501050f0412062c0c030106 70
    0x5001d03108010b020308174207400306040c45000d4110720a020982c0c01400f058079141c0201c011441da0612910040c0c6040c1041240200007920a40c100d15802601a500d015045c40045800f80c1c00401150b602a03000c0002485036404c40700504060105000403003070307168441c00e2a616041070360344000c1441045004106583da03003c000003001064041807984a2414000000d04500400d640d005045400d42c1450f41560b0590300f2203030107204c0c204002c1041841a03030900891b07210710303d43c094050384420301280c019482945142c40590080c9007001190b6802d41c1c985003808070540d000985644400c40c1104640a05032a40300e502c80e00b065250134900d1101c1c18107407940c1b4070340b103082562840d00c0f5401d054500300ca024020329100141c0500e07501e603150340c4590000c1e0803044401b0700500c2040e8022596500441c00c6912b10030308400418145850a030440d0040d103400c070400c0302c2c02d5403a5040c1c0100d40c1c020040c06d29445c6003c10f440c00390143d81c0754240380b42a201700403049c402d03810018204032039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 461417185 1250 461415935 461415959
    0xa092108030c0909040515070f05031501021212070806040216260a031a01170a0902011e0815040c170a0213060203040603052505070309030b07030e0c0a 67
    0x400e0340000010380729520303018030039400d0042c05070707140d04100d1142c2040100003000c01c200c02d400d042040c01402c0350711040b504443e0003036181d06981c0400c50400c0840c40520110442602840052040b1010390140e030031461340b80e4201010724446000c001c000e205681c0d03040060030f0351015054a08600300800100c1e010003c091014010302141d6140c0e034245500034030385008009180954681a640715181000100204148085400844040600d401c90b66120320002142c20105010704000e036294119000024050494200d040c42014035403038010180b44680b060807910310707488807a020700e400b4460000306500110704a100e42d103003541c0d03c26020342000784da0b8044078000000544c142c0d16840e03903500a02c41c24036901900a6640000201c20382d0000c0100f09480d029034041c082500d820516080800c45540400c0302c860380c00c0e1160b10194814805080c40d280603281010f615613598680f0512024280e902a0000c1e0316203007c01e46150b410000d640014030140c07071403804103180052900c14 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 461418435 1250 461417185 461417249
    0x110a080412050609031c1503080c0a0501110a020303012303070312020f0d1202160f0f1a04030e0d0303152402150f04230a021003180303150f0b0a09 65
    0x906da546071500c809032221051001c2c082c550200e0344583ea09110602c4030380c0d80000e910200c07215070030051941c030f04480100035200003022607001141140d003014402460241d20340c020b442004040070441510fa038003005a440250300550b0303081000242804001e08145001e0400c07511a0303c2111901803080e40030640d01c0f80c2800c00000141c80344201034480c00300c0307084030802500012020310705400380b0a0f07014988007058440c04241207102103656542c0c0f1056001c4402601143c080302042050b42003200751050b00622903e40001c0401d4070400d154001d107241d40000341c42e1018122a45941381440b8403602d0440a82d000400f5074140000c20030440307160007040607241003001e0012404005a0f0758103565030481450f08807101c1180d00303034003a03070310f040c982c605074481c61307840c404104058002e1040c03004184158651403242c505c140c4054000d0180b5108110024803c0c0c01c0024a40c42803420510203000901001c40e9100713903840006004a45982107004002890500740940d0b4401d000d8000c2c3d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 461419685 1250 461418435 461418487
    0x300903071515180e010c09081209130e0d0e121b0307080f0115050d02090a0e0709090305040812120415020904060b0d0c0f020c01110a08041205060903 66
    0xb10b00000e0390099003814801e500a00740848040020341403108560019640540c0f410020800408a50030840e1482590303c9004403941003101c40c0c0c00e5003003000c001440d010501820075420016590440400c549411804081c80d4120102e0350034656401440c0e0807451100311141031001003a460a140c503440403079544030700050600108034050318284200760017845150240c03030512142c0c074003040c080c050743c04c240f203440100c040b000710701464080d612000441c2c0240002005550300a4180e00803c4400398a54041c800c00c2c200007092040d90281e50788041c8a070b52001c5d00c50303140c800c07840d03d0000c17501c1080f20b40600500111712100c950080c50b55100f500300046101c00350190b140316000748140c5204c01d80080c100140420082200c2c03004110f00150000c04024071101000d04a90003400e071180c0c400160817460f03801c0b0156110f0020500d40072100c40544000c43d0300703903841601c1a441540100086020085180306014051260507809040540a180b81000e995000146e1031a40c0201c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 461420935 1250 461419685 461419691
    0x40c050903190f02090106091701020a1205070915090305060f060f0d03110d030603030e041a041e020301170d08010303090308030415050103061d0c0609153009030715 73
    0x160a0000031091180c03c150050b00451142d40c440000402403000c500402000c00d40d018900d600b680c505100b12444003125a80380940511524103400280c88043c108404002c44024045000300202101ca9a00e900c0350311100e80e080d18610f00142440d600600c0141391201c0c030700801c900d40d10303100011124a0130498445c095456245402c0d0b603144e901e00c10f0505184a00080f24070100c2e055409501600d0186c0c4412190803000030070002a180e11000d08402e01404841d9039585007080d0308240c8a40f00341c4448500c101c406001c0040407038109070705c070b902c208400c813404003c540c0042c480007040d0381051070101d89543c19601c000d002101c00c0c0c071000740764403000000039084c08a00c4840e4000582140c600f17010550352070600e40701500c66045004c08080340c040a0f00c10990380001c070703c10000c0c1c0c0a03000c1c6081030840000c0080da030001310313085164076204022014064202e0a4007180740c05614000c90040c0243d181215102c0d10000c0052102da801040618013084910b0140061852011404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 461422185 1250 461420935 461420983
    0x2070513090b1503120301030b150301020304110603100306020d09140304150804110405090a021002010b1e0f090a0f0605010509132c0303090c0402030c25020618040c050903 76
    0x101707290040000740d41242140c084000b00070081381c040400c0c09407840400c2141440e8162081500f00c2c84162001059405100b04540310340c10114059a0300c08170584807604200c1e5640c07181c4040c3e910103022030b80025655501001000100800b00e11250007150045082c41e043c0205296130310070300030704641803204640000b0104400d0401402035002d01410a00480c2005001c0565031240340030201d11036080088440030362481486044040a001400c003070b0206400f40a002444589100e03254000c82c002d041c00a5513260740c0c07480da0107107030f0b903104c0040e183c281d500804084441c2c9820250402000b00280c02640d946c1000e000c91246218400040590101111030480020103d40c040d548103032040c018520ba41c0030001c1c501c1038030b00ba8281c1d440f44240900300b20403440110b03034008420005103c0500029241302c8a159a81d0070008410207801c02da40019656812502c41c900b0b002e100d49900003181d040c41c2c052008225000d0401034207040150340000c0e10307548102c41d04120030300c1d070303040b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 461423435 1250 461422185 461422189
    0x816061704170408060402010e03030a0c03051303062a08010605030103080c28020901090908042601020f0913060620010b13150b0403020d03051605070602070513090b15 74
    0x2105014002c0e62020790360380c0d641c0381000c81d15040200c0d4141e02003000c0301c0030158281000302c210b5410b83e04030340d10520a480c440e5411780b066040120b10012800c0340c00350100c000b034a548500043c0070b0a01500c0c5802e0301402620b44181040e0000b40700070070440c0e0004020031500101070341d054036844401c0036101c2d01e4418440f1301c0c140e890304645c01c01c641e0142100c620440422410b0405600076100309080daa00d400f944026100c40d11001042da8004001c10007031203040c0c0700000c43d002d0fa84d40e0b03034010f0305400000503402da811940001d44010000a0103404a2800c16250b00030b0188034041803003083e1608102514503640100002944003403c4600c000900d820f62141c050000c004041c2510305005084240040c01200c034150350f140e1400c000403580c03140c1c03501540e08907070f401131002c813032110283e0b01115150401c90051450450740da80340800510148407020160000c4c2c0c1c0101519445d084c104514001001d088403003691a0071007407800314045151042d8444010320642040c0f02034400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 461424685 1250 461423435 461423453
    0x1606020a0c0611031c02250f081b010c090e0a0e0d0e0301020918100b120c1305090406050415060b04050f15040e090114090a021210020f040816061704 66
    0x415904601414001c4000341000e078080c0c035441e03100c1202d48444076922072040482e00322061008d0710305011b000404000454920080035840c1220140300700440ba4140c5c03040c01e44010f052040e01090b41d58200f81b20440740540002e5005403401410701c010100e4044042d100c4d40900000010041c1010000d00c960b1000d4040394600f0034003400d40c0c0040341c4400c0e03001d032400105482c860603d1600c980300085540058094a0408000080c91040c03611045540102c2e588040702c454010000140000344550b20160003520070342c065000070401d441c1500d404440c180c5030341c184049441c9012400e21010004070151001e46006507402071032031f540f81c00080c002980c0710704d5440042c0000180850780b05000c4108034080c000c400c009002030440d01c200744550f1304041b07c0c0d01c0d800e9840241d01d80050701d4a80c924400c032500c004140c5a03201000a4144203a80c0034007000610b20100080800130500c0400c003200310720242c00d8400c00040c1c10a0801844400f10880c64441507080d0808107061140540c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 461425935 1250 461424685 461424697
    0xf0408041503050a0606080103120c020f040603050604060b0121020f160f0618020603061309021009080c060301270204080715030f0603051f020906030106021606020a0c061103 77
    0x10480d0303601d880e0080300401500c0101c5404a44506019001400c039000343c04c4076059036401490851080c41129044988208400301070b80d11511240840d002e6494521409000c0c6000c0c1c4060034a9180c1401e0038002d44420500960411455107001009565131034101034456108810260740c03007540c0340c401d0559000d000c0303d03d03031000f01101034007007007024038052109068800c0d01c0920072a000303410408150b4920910103500108204002a4070b0f2a0030791203030505540c1c0d0080000c040c01c4a402184008450b83c00b08408a11210700c14812490708108a83d0300c1c1004890640c9950305100c9412804903650495a01d645110781b6140462550b540566000c1c004c0710044074001ca41da051141d440c00c07089000d042c04a031030440306040d06501ea001d05002e481c1c010004080c40040003a8507a2940c0402040da21700b150300344000c401d541d0382c0000440c000e02440d0700921700e80e8451240380c0e80388410750380a03205644c00b00c82c62030001201494030008a4a050411044003000980e0050840c4074003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 461427185 1250 461425935 461425949
    0x70806070f031d060601021c0806010e0102030c01060b090f04020301080a02101e12051302030a080d0f02071a0106020313090b0a031211100b010e040906021c09290f040804 75
    0x501d8169072003e00008215104080990896441a0f610003003030007034621400b6080c0000d07108000241003035004c2c140c15480b406040c8101c0345041441c40900c4d00f1a50340d501b286010384400101c4a51600d0801a115a20703601101d04501e55403411029503501c00d01018000d000d40c14404c2192071031030161221003885030070144400c1e4a10502400140501c8440040c06541850f00f0042400740400f01d60600310168090002e051040c01a2074100085d04650380c0341500f80e8032070750000e50190f59070010740089031280c03c40090401c1079110002d0041c0d0160006811940305021201d01505e114050604030340d920000020400c100d000814103036007050308081c001080708171103002015880340c0316203044800315083d0703040c144501110809844083c401140010b001c2420715260f4981039110b9181e062150301c0051600c88a580b01c1072030800d05480b005140d90b507451004007400004814100e841a8280e001c8122100090030b11840b414090300030000700c0e40040024003080380c42e10444002d0444 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 461428435 1250 461427185 461427221
    0xf011409150714030c1608031c020f0f040536060604090203040503071202030324032b080708040f0b0601030b0406090603031106090715050f0426070806070f03 70
    0x1003010010f56941c4079500c0d030b500c1761107019049a8000b40d200103440948402501941c50602c40704100442d030001100e54072241d07a800c0002c1201b0318000c2c40100345904a0881190b20b0341e2900082040c481c0898822000c078203013070f100100d1150580041c4000340010b12440100649610703000c80c6980c062078110b00c10302880001408180407001014003405171061036112030600700118100e889001c151900b15000740c240c95403114400100c2d030700c0704102101900b119401e0303a0310810340907030101c060f440c0710442c5070310000140038540c0035072200e17882100c0e400c10340c0e41c80c285039855000d49403200034003405041d11a80403400aa200e074000c0c0056800c000d106001150b1281d448800400881c402203002c40c0c401021441001800300302907204030030610161610920344009041485a611085401c1000420200c69040c410300d019002406e052072180350500e07040c030a0b80360000055100c01c2c640340e00002c8108403000740060002c0e0b101700170745040840f01e03c0b0000150003515580c1c11840c10148 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 461429685 1250 461428435 461428463
    0x702010f09030813050306060a0b0d0c02150a0509071a070809030c091f0614031f15020d1d0916030b030304030f1a070f081003140604020f0114091507 66
    0x64139680e003809a0703a04405441072600c0f601c0c10000721040f00e10420300b003440107028003035990040350321003103500301d03203005031a11200131078400002c6020440d0ba0b10032103599003050110041013000f0309000b0f000c1000781c00d007450441300c0040100d40544500100000d0002131005126142803110800382c400c003600e82462410420124030440700001848112407035450350000c1c2c2e8a108401c0309003111040d20000d0324640b5503100d07900315070041c040c408159000d6500e00050f02d440ca0001c80404c14215030107003440044440b40200081c1c2c8440413480c044140441e0b801c7c04c2e0760340c2103519070424001c28410040b6103404009030044e0100d2090740b549808041030000520007034178141124030703100d801c003003c8100b44640610400f910a071901400208050b03010014a80a00b86c019088103150200102165880e641c80380c003102d107186500b00d82d07000300061108605102c07801c01000b0609003001c3c40c4c61701000424040c1030103581030751071040c81c61516101421003850101d40e03140341c200d103a0070f01d052 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 461430935 1250 461429685 461429707
    0xc0306020f0409020310090b1e060c01020c0a05100b09190e01060504090303090c17030d0e0a0606090b0112020f0901051c0510031502130308031e0106111c050702010f090308 76
    0x8114418200410b0a0235900221840e0080b00d0808000e03809090b5450207442006010041c0c104004032980d540d4200140621480100b080d0388203a03200d40000c000b120710100d651001d46103030b5030035140100c0c2100c00703000c0f04000b09600c0081d41104880700180100d0403540943c0580032035441650031920304000d4a0038160300d600b0440001e40074500320004681d4960401c000220740f520305004076082440400b1000d99150049143d1806020480c4d24200080d10b54800b1036006600051646030740d5103e0408558000409100300c030810b141c210300300440c20421800c0781c40b6030714400307040150028090741900d00900314070042c0c1c241344000700590720381500901c200308400d000a807400b20b88004030092580c40da000b210780c007105003140d0030103491440d5542c01641d04090003112920345085040c503a01d200c02c0941c90b0003484d090380d41150025840c00114100b04807803070090003241820711084030701d54000302282c21b0680c3c2864070411901221a08403898400781d00010510000007034000c881d8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 461432185 1250 461430935 461430961
    0x507030311030118050f0405070b0f0f041d13030e040b06120a2f0d0504030e04050c0a0e01110d11030c0d0806040c030513060b0a050d1b0f030c0306020f04090203 71
    0x1011024010003441d150340030004510081268002c08c2070707204004c144400070a61001d05103002c81d2048240c1068000c0c001d40002e40c11541103d402c03400300c1d50201380d601c04001c4e1441e070080318041c1c4c0a4010011910010003509082c03103000d01898941000b1103036034840c00700300ea40c5e50389803220040d010306080c1840c1c00508405494000d80341d0710240390010100840074440c0850b02031045e0980b409514002d61805081c006105074148840347d00c1e0305c9600d440740d0045c14460a0040c07180c030303981c451000c0c000c1c1080b41c100c0740040c100220b11156801c031140004460f00c031110325050110201030454410361440c812019100d20300c0c0540d2040c40071103138100f40d43c00c0c00f91303100f101c0600c88200302c0d10044084460031030311628200b8080903c100800e005500c074400400c03000c0c044c000e40390f80728004180940c000103411180d500400904440583c24804030f140604071039244e580302c2c2499170303c9201d0241030700c1c040500b035990300140c814403502e001c0d411a002040100410b548904d4840020180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 461433435 1250 461432185 461432219
    0x507051002220605041a0d0c08160507050703060e4e092b0f06060506031003171204050a03030606020102130b07080708030f1603110a05070303110301 66
    0x2441d851040d001c030440c0d0b41c44064150b810039600c07141801d14006441022400c0c0720034144415408022842075552140582c07810f003039041d00c407030340c580c10207085030311180503201c1c0a00c04004090090f00002000400d08c5000c4980141001c181c042c1c070080218142011038105203c400300040c84d01803130703810701e8105040e02c48000300403c5801410516980152803150013030341260780c04104594451816000242c6050040301110900000603015070280046c0404282c4910304c0881411080000f07134001c8002402c01610810b0540c10548040e4208030020b0000a005155449480b00c0e0742c4014410755503064541c1812100d43c1c00c00d0f080140d11810f07140ca09800007414201c010a075030b8014000c03201446c01c2448031110315460324140300d0310f039004007600b101c3c2c0140030044000031446a001860044901050001c21070500c980c440d20a02c403041d4903134084c94144401e0310040144c5d44203032400b254890074103d43d2070703e8510f0103c0091040640180c191007002c000840c0341651a150036031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 461434685 1250 461433435 461433457
    0x20f0c060f270a0e0a0c02010b0a06030911060f091216030f030c0602030a0b010e0d0c0b0d0e0d0203031608090307170c060403030f1d0a031824030605042a0507051002 73
    0x2244a2001038108d090720003107001290402a0703808204a00c501c00d602556400d8042c05004c40c43c000b01200291003984803154203158004003085418aa1800c00784602d00045601c0c010300c1010341444200512014520014205180e40c2c103981017030500680c034007120194000e00031556441e20104a800404020005500003a60700035140b01c1824036515202095400c140e21203c41d519204401585910448649640584401e241c420314402004069400c500a030041c40e200d142c00607000c060410380f00381c24401c200b410030a100141c01f000c0100c81c12a904003031100743e01441150070360365a10a001d9051400e100d139101300002c0c0b56042c0c1c054070300d406d6500d90034070000c15508510407410091400401c426001910001c0000e13028000142c00c0f48080c80d81c0b1000140c1d00d0803c086441c00001008808038658880c28a6150785841000c001e85021101040812200b8009168480c0040792000342e0899020725001424020001d4400f159800300403110000341d044024030280d0003840c20b4003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 461435935 1250 461434685 461434691
    0x3060501090e0c06031b0705070e100f0b09310b0303090a090e010b030628050c090f01031b0c12050307021b040912020f0c060f270a0e0a 60
    0x200712403a142c05001c076040301c01001483e40b80440b50400c0900d90001c0c3c1801141141811411b8241100c0009171000303e0240e409030489624104001c031220300c000b00218010001e0400034840072004454890a81c0c00c42c08100b52250b88010100b07090707046800001040c640180c8a40d0041402040e01000035084810103016011542c8140766480c06104201644840359800a0126413034136400058460161030001c1003284148010a041c400107039050b402c1480080942641403403220120018044400700400562402550500483c06032450240c030841e8050080c81d0395a210780c0100c02c2d51400650a48514402400040d01c0403500904c00ca0b407100b51042041d1303040c0c0c0502c0540380700e000143c000c0d14401c00301c10102c6141012207a800d69200d50765414842c08140d040c0c940b0207844840d50014200c001c0f4040c01c481c603101c01d80e401c1c2071244404100c0d4000c0c28030180c054801400015820000407001c000788070110701342c901034030380d088445640c001030990700078800d140c0207003c409020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 461437185 1250 461435935 461435939
    0x220209240d050f1b0f09060a030f05070608100501171e0a090c05100c03050f121501170105032a090a0b0a0f05090613090f060f0c050301030b1b0c12030103060501 71
    0x1038113111a11400e41caa2240c03284035094414149410341581c001d20082040311181e031280d984503841c1200c5402500c0319031005600340241608a038545070440e407005030404205207041d0009241d942c080311400c440351b0707010021400465035011109c2c0200e01e01c00702c1e0800c0340f4280070f14500a11b00300c0300565400700e00351000101820540d1160141e940d40741d07182100c926654400307649030740c0810f500c021101306c00c0042070074440c01d40e140b00740144224020800d40c919a4800103001035840e01c6803030100030346080104500d82d0000b5542c00428a003181c2c0010021107000ba11168804154980380c000007d02c2c1081180301c181d40c000104000e007140c40c08611504d50b03003112914140c82c050750f0307003080f00c020201b62180340c01064030241c0003010b0008212225281d4586641c01d80c0705800300e13052030b1203c00542c180c0750540184140c800d41032800713600319851a10748228042010b0400110241a41e1800c041c0400080031200d4180520301100c00414450001d041250704c02d10055541c50710388000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 461438435 1250 461437185 461437213
    0x609090a051e1009111303030302030103030e0f010915090503060910060e1012020409060c0810080102070b16030902330f0901270b03220209240d050f 66
    0xb142d8022003460500e110004e0605041d0b4000300040503480200807010300500e00d2855444110b40b0280d4031940d000361700d952643c0340262243c50400740e11442003090301000141d607680204060119144400304025901d030b03042c41030740d4252043d00000c2d0940141020003884c078200142c1c0c8003004101d08410445942c0c0e94002c00f8490300203480c041c581c05030001e0304200140138450103240c8240001d20000d580c0c0b006a8480f000c0715210083c810109020b41d08020f0110b0000400c4c0006244031802540362000f103030303100c15044034000c0696100c4003200c030230b410580344a988a110038950181a00c0c000403540440184ca03074030302404100f91282c00c0c204104481220744241c491031252a07498074100900b10006403282d0902600c001012031940608410301c5d50400640c1e07005107104283d09a4a080445040d480c29407a4000940d441c403241c0704590060b00c400591540c850035405400c446c03500480303064042c1c14030500d059648505214032440c140503000c02d103070083d41c2c2000c04a41030ba07803000320 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 461439685 1250 461438435 461438491
    0x213091a0f180c040f17010b0901080a020909030f03090313060201140406020c0c030105072102120105101b03080f090604022b080d020a020d0e09010909020609090a05 73
    0x41103a80101c480320110b0030392070480c44903981000102d00c00070305254460f1503820900b0308076840341442008428a80d04040400e00c0f52441130501541c00070060760401080320b641c5c120510000740245e0400d130000c9d44800c2c00b03206803911544001e00f100d90700e0500840b000d40d603402040c002c3e24210903241c80042e025005220301c03606c000c42c00003041c450340d9540d25030b00000e400920a4140e14041e00e29060700e140d40038845c2510030403071612083c40a4a416502103119168030b002d150340c0610400c41c1c5003001c03102c6207951b411103004440c0e00d0769a00ea150350803501100820b0700300c944040000405001c15401040c042e105505151003041160794881ca1117560305410351340603400000c1500c07102c0b81111038081492032504103904042c2d42445580d1b40c1c0409520042582020396400300d441ca01c0729078140070f1010362841500d4603582030900400000d0a1803010300c9108a40c0b0fa4840140c0d04545411090303ca00f880000e120f20308603e003180c3c018000d040d08070f90b00c28904048650410038041440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 461440935 1250 461439685 461439709
    0x13020307030605060402070b04050327031c090b070309030b280f0902120102030a0c0f020d0807030f090516060f0903020d0c0f090b03010b010c0503090907030213091a 73
    0x20024180c040c50341d02c400b002800c1c042c0c00f10342c12540030000b10000c94902c2d03131842e020b01e2080d00210b0761101d0a03410111221004500102c650342c002040300d0580d030b00010480c40b054101c602400d042a407103903081c2d500b1a81540841074041c008140744045c190001c1c21242140e00802c030b4000c40f03544850170401310500b1069a0180c076489900c030401c0c12a99540801c090740c82c200c0000074000010b4001804c0d041050b00640d036503a400100304080d0490b1405400ba041d805802c001c010382e40d8001019407108202844d81d000c0168000c006009517210341c00542d0b1030140c8090400000100303040103905e0300b40001c4e071404034410141d400034a0a209181c0142c0076002540c1b0b0f107801c02d0440e0b0030400c8014402206480000d0f04040100e80d05080080f0507001784049a000240120007401381400d40d946c524045040c49104410305012030404411605503401c04c0325050b4450703594401c280d0082c050901c0010000762030101c081200000b0741d000c955619010828075809010040030059142c5401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 461442185 1250 461440935 461440939
    0xc070b181203071b021c060e07080f190804050a0902070c060e180901110310060905062701020a1e060f021e03130218060f030d02030306010e0303070c0306141302 71
    0x7801c4108284000a13a8200140700030016801c4030a0120740211000c04413a00740c40c1c8643d0f0700c2400701603850400000c0b00501000028110f49444140382940707440d541541c50f00c099001c00410003c00120100300d40190000515011859031540310440003500b003480101d1351403403258004210030b4003549241045107002001c0130361b0403008081240050380d000d04542c00940d21445c8003201d0407400c81c017a500c00c125080c412a07a42d454008020030002c9030364030250180718200824803c060780d004449403050341d100c0c001a602d41c29a00101e02c1e080c007541004d4030301626840000c1e80210003900080c4042e00401041c03001c0d56641c1041400c91184030342000f10002084504e18010320107070051a0320011180740401c50b22010b4000c100517802e12419040d10380da01c501009010b1800b124124007946041e0000c0910351001e4901941c0d17844040c04240c140040182d141c1c03403d54040007254005a40815a4007042d55280b0b0b211010b40302c079400003502e00c2007580004064081c0f40541780c00103500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 461443435 1250 461442185 461442197
    0xc02041b0f02070e0606071104020301030807021f050a1d091602070905010b09010f140c0307060e0a030c06150515190507030f0305062d03101808030c070b18120307 72
    0x40c0c00c0402c03140c0c7d4003241017115544401c082d0080700b56a180f02941c000c2d40205041603541c808e03031042142c141402484a002d600d120005c95000781e50080071b4031084a01c03820040042822290004208000e40a94581c07224815040140c14080e00034082d0307a810081d001c848055490b03d90b41c07000c5e1202401490000c0d6000e2048030003641c440c51104848402c1410000000c20040c154200c0c0781e8002000c103030566000203441004c114091255400d440d1204d00070b845030b82516074004060518466003d49082d481d00d80e1001e030060380c076130740900070040181102910700209542c0c02c1035401107400300100c1041b80369084601c5000f0411a000d003545130741c0781101c0c40007401c0194014540030b802c031501b003800c8440040000260744142181440e60620150840e0011410146440c946050803150035003001c000241c07201d41b2200131540342c2ea2007a0a45c0d140d0356446020000d600800d08003429000f4160180324007038242181140308101c0007021740d00c4a03003c200d80314119100a4039030b0300020312 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 461444685 1250 461443435 461443441
    0x30d0203040816030201020c0c0405040809040911040e0a0606150c03050c070f030b04020f01091202060304021203070b1009200310090203102606160c02041b0f02070e 73
    0x4455402140c0c8907224072500c41c1006815181039140070b9005000320051707980041d0340e500141c410011400c3e4880103c9081c0140e28080d62809a24000c0300c0300715000e1078580700e0807c100b181b2861404151000903004000322445031440c0d603a581104201070315600e00d0040d01107520031991546149001850300c48004030b101e85ea80c01c80701680715030040030303182c0603500001c5050303a6110360000003140503514098950510b4010031031410410700801d4103020000c02c00304103024014441404290b01107940940b00d40d2a8008206402c0c1c43d00b81c07141490000050000030044d4003041d05011360340007100904070548804a140440d0043d5140c0c04403603030002d8041402ca241c0400441d8010317181208004900e907141044420780e0001e13941d1441c0c1021141d0203004070035070310602c0c503c003551404681405611101c3c0c0c3ca074980d04040c2045443c2202060a0b401060280c403054034a1680a4810005507180200d108207041c01901c0b0304001a01105400d0700c11840020794038181e54000a080490352 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 461445935 1250 461444685 461444707
    0x1806051e060901050a090f0306060e280225050a0327170a020406240e0f0607021c060507110f0c0f030f06010f0503070b03010f1a0d1e0e010e03 63
    0x24101120302c0c401c12451407000314401f0900e00e1604011441081c01065041c203081c1d0314425940c0017070280180f80c044c5048000c04400d6460441980c1c0405240181d40d5a900480c1d10803031400840410110104010480700700540019024001c80c000d5841c8601c4220645281c00c02171100c6012207805140f104050100401880380c1d00000394582044035441b111b142d000c1000e07256150320929840070104c00191102070300a040c0e009010040c940310040e20701c0c6000140e544a2248030f018045c60011030300f80c04648500b07000f560900a0607192040d12060307494480050a01280d5400002d401014145000d103000500540c02103020001b07010034511724028030241c07049410607a5810b01c0b521344020000c2400f4041d80b80a00007483c0700e01d2007141071500781032070f01c840f039440f0b07000201c2d04000400c41421004913500507904910100c00d10b0070751030414141c140c0105845810164130705003101030341e0101131410000c2c002883c10b05010200041c20203508072000d070301e01e0803540d810403c011441e079 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 461447185 1250 461445935 461445937
    0xc01020309030c0d2303071b052503020a031203060f0b0d0b0a051305040819080612070303020624061903050606040609060507050f151b0f0a0f03061806051e06090105 73
    0x11401e18240c2300075049407400b1030451500100541c0c094000405500b84880c281c1c0a810709a241d00f2800c0c1c01e43e610b10f0740802c1c44081944000b1300f0f1590a4800c8124043c882d40020000b041078081d00c102c02038a40d03040c1c043c1039201c018682c1c4000d24006840c0c009003440c00841088680050080d110300001d11413120290000801c11175811b503040203107410f40380903140c82500121407aa2100c0191078007100b8400e811411100c548041e91007a0010800070780c1c00541280d004024441921204030b0441d80740c0b030a807400d461681d621000c0443d14940d005a1020314000345012a0340500480d241d100602200e40b00302c0c05540005103482105119490080b4002d101d050321601c11140030800a03c0e46900340000d40729081c08409204040c01414002028000c0002e00080c2484d40f400b0510811103120344145007501e01030180d03002507031000c54041d0f88580020102c0c244100c05401d40d00f4142c10003440c541c011075200d078016100e9040c40300c0700150710310351000020b401e007031800461100654503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 461448435 1250 461447185 461447191
    0x3030e0106030c0b071406040506180c09040b1603060e0106270909050d0f020a12032306210601120203031b1605010f0909020309030c01020309030c0d2303 68
    0x1856488050010000d00010b00c04401040855181c80c2c841d9403900e020184803501049a5481c1e074804414000403031030125002d03420003101a0884000021082c6050802c8801c01ea001e034401c000c0800c100c10300401169189c070030706e4140b44c10111050089405e5045442d03e0140108c50700c50940107101d0640103c540f5225625200102c1c611b0b07241d00f034111400e240460304000841a11076901c241080402c0101c40e030300480c0c50408c1d542c0c514507980001d41e180395800c0701820700501c14448244c41806640301d00f1560903140303074641403001d4000a6000781d444c140c40b85c6018401000c021405c0d00302955508841d40013180c041c00041c1d00e4a41640241000414283d0345030000304444040c050784102c200311640554405440400c4d0418203010351070400d0ba0040d410310079117049486071a0762065806080d107600c000016181d0b180c1315041d920758001c184190300b0706d610000a02c0054680000580148010401118910900c92100f162040001c0300d000380c10500d4101c82001a1202e4005194 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 461449685 1250 461448435 461448461
    0x10207080d02131212030504030c0506041208010902121308121608010902030601020d030e010f0c09030c0f1220060d0b0a051c030809010b0303310f030303 68
    0x814014140c0322140d80d07a01101c40c0c0040300d90700041d0005051400b00361980288800a111804003c40740c40e000c618085038811a010150b0f6900044c04060151810340601904401150b9041c5414940281103200c00040c08011807454000040d5100590007190140c1d0f902c003d40e44ea01c0d2b101e80c040e0312810745400a08940f408000d1228101e2460303050003081c4200580c048608010340320820140c0300f5901030b0424298139004004021280e40c0020300e1f0f611181d40c5203800145181580b50250060034201c0818074580e0410b04d100b00070381d0740225000c050b6405180942e0100350b90340c02c2405600c51512030140c0c49e8080200940c0407402185185540c2100b0f03010242c072003980800011810b920248ae1582000e50b288a032115500b4041c0018024000654100144081d000d0a1030040e0200134030007000c210041000404200f02234006217403441c4040d040b60b0311985054100da1009800c00703510381102140b5010180441c41411324201281c0071105040c2c1d4080c1143c8048001d0709004143c52 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 461450935 1250 461449685 461449687
    0x150509060607290c1e032502030a030b0607020d12140a0309060f271b060522050607020427120e01051309021e0309010c090e0907090e0102 61
    0x400452201a14030501d00700480c0d0b0311155810b050801180c40101500000c10b00c02c00f440344034400d03414158a00085090400060b490303558280008090f01f55540079041c0200c00e12111042c07003034002000d08104549905c0520850721580c091280c0741c000c001c4045d520107990f1120002181803900e00402c401c0562400c1a0400070346c031440c80342da511480f01000040e40d15016038080c000c0c170340700c0c03013002e03440301071090080b000203203115200c507400f8030f0072405418030140014040112031b140b5803454043c45101c1224850741d54001411341d81000c01e5410315140f5400034600c680901c0240c030000d49070010541801c0c0b80594080c400200710314409074017058007901a03200501c9044600c0082e540c40342810603004020080010582c1c109500c1103070500009000c9080040a500e01501c10703600403140050300c03840c1010b100079140000e02d841800c0e04400100380517403241e040d000825800d0301a11160000c0b560340d103624007c0c60044407060556006110203204100c00c0790030519501844074005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 461452185 1250 461450935 461450947
    0x801061d0f062806120c0f0e030c040e0c04060503160902160209040b070f0201020c0703060b0301060e010909060501230f0a080d080405161203030b0a030f0f02030c041505090606 78
    0x41c00d8140741425811600c4480a0040040c00e03488000b05001c038000205c00d00606508600c058807020900c00700000f4464042950400c64074200401414a1401030003480750906100005481300003100a007805103041000100c1c0f6401e0005200451407400360241d01381d18a04030314980250842c0046031280c074400c1100201603070f210007545d0f009600940c12000c0c1824100409024014210800d900350390041c404c0c0a027848000c18bd40c0f0807070742c00200115204026100090042c4555084007000b41040320001c95915002d5001403800d0b4400d0b101000207981306c1d1009200c03509108804c0d0344402c0011a01271142c1000070f0b0090700c043c000341c40400318503103c5800700d081003416019040017840b110104414440200b04188282000c01142c11440381050000d851251440b0f40107002e041d100d0610382d5040e110000d0038001180c014180c0c1d460144a854000815101c01c50705900c60310850041ea41c083ca0b0510a89921a4110441e000b60502d07000601c1080c003c01000264044014007803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 461453435 1250 461452185 461452219
    0xa0c090f0603020a0816170405031b0715090515090406091a01030b090708072706090501030b0306070503011e03081206091503120903011b090801061d0f06 68
    0x18120240016460240c1c8820200e03000600d4008000c10011540c214a00b01b5940c482e0820303100350496103180c02001250307841e400d0852942c0310340d01d03940883d03407840590304544d00008030b42c08066414039003044542d60190b560407204507425010701a84501c481030000840c1e41c1d41c1d001003860900c0540003084040d0784110190441e0a402080d054200d00c0700c01c032411035031741441414010700084407001e42d94209958010302c1000024105014403800184d00703900c40c050340c04451441d6416001100b506a22207600074260111031181502290400b40c2c0c1c082c1a1501056551040025a0342c650440c3e10303003003c0c20650f2890f003030414520307c00184080080382d5180010010480001c096007142d06241c014800d015500402c00c0e0451074000d00319142d41d60300030408803140616401820740715010b4000081c01848031520403010707480004140d070310b10b54101043c5821140050020000143d82d00000301e4804074030321180b940c900503100001c1010f0b0b0003611031504064060306280046402c184 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 461454685 1250 461453435 461453459
    0x15030501020913090b0f1806100e0705030735041a130b0412030e030d0f0b100525020904080403051c0f0f11070306020405040516080a0c09 61
    0x41510141d4000a500445003098400d0303849518901e1000c02000001e0380f81d070490319801a010740303040500c104c08100181030040001000a0b80d40c004c0e18401d042c050580303181d0480034440c01e06d15801000c00240f9150040007560f1003010142c4401c803004da101140c401640f0301c00501e0b00e419171464041465100c14010030284680e01c550100701c030b00c4e5800d4040f6060844010301c06840c2d50400710004d00094078019410b41c10a520401546000310300700c400340c01901000d04554018030012903a8003410703e05401c00e0790400380010003040704269030b10038003a141c81000078840c045502000007580e000c00b6906420a0711002692407008046158001809240140ca051382d010304041001e0050110500040c40c1ca116070480c26082e030f048020024200d000d1b0011903005005200001640c4907016007141c4110003480d030141e60070700340c80c1d16042c002908036000d40c1e4001da1610f070000e5181e0544403841d4100c80d410f1348801034140e9404a03150040d00880d01c00d0b00405c1141c8000041c0090342007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 461455935 1250 461454685 461454689
    0xc0d02040f0c050304060605220e0a39060e0105030a060503030a020a0c0608040c050d110907020f01230c030a090f0b010501030b04110d1d0a1103071e090902030115 72
    0x1aa40f90b541e801d042c01d0a009540c80b035004244100b240c4070204651001281400d030100c0300b0420085804540031031483e090802128020340050030511004640081c1d1003640c80030894281c1001250014003585c0d142040041d00548011849095410312070b0341c0218040c5a0100c034030240810304a44410102e030030750b0012605003016034846030b0f55204200c140038501002d002186803202407441e01e622401c5808509200d83e90003480d030a8050b1080c04440d40e00414aa607000d0a04503190411030380003503560300c1c80d0a0130203095180c07101540c40c0d50610401015860690310041c0030503110a0241c40c85a44050081034610380d4506140e00001c600f40110f40343c090081a000282c1d44c900030000d41a1021040314900c110720b0840c0015140581e0402e840901c41d810000081c0c100c5401d0305184075050484002145114800340e0500300b0055021681c0144011ba042c0ca919903680c0cc0d00005a11040705a88100000ca51080c410f90390a035102c41c100c1c5000900204092096540b217421102d415 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 461457185 1250 461455935 461455937
    0x3070311212401050409020702030f01060b18090609040212150403020307030e0102061b0d06030b0a020c070614030f070c02090a06050438040212160206060405090c0d02040f0c 77
    0x3800410298030041c03141c0500303000354840b4003030740c407030200c40000c0c4030380b04601510390301d10780c04208601552003c202c900000d400c010001c100c016111030140001e90000400307000c2d00121110080141d081551044d8001c0e00040c0c1500400e8850307034200f150001110780510214850000c40c1003018581040f928015802074024513500c18440c180180090581ca0807241558070200c1400003c1e000c111811a040c0380030341b2450b49401242010030b000e000b855201402c0100da04041c03144880650f802000081100e00494012941d210010740c3c00a0004241d03a40c183c40600001d490031021004890b03000e001031400441c0f4400e55800a49010700646030243c80b941d561505210604161044601101000704150095400c88001340e48048404140054a42c0031400103851911550199580488141510917440c6000f48900f492412801c403900d0040c4a40e0340420440d0600307201e0760b070041034580041c041c5403540305d052015054151a00726001585d400034410000114407a1240e01d00c02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 461458435 1250 461457185 461457247
    0x70f0303020a020d0809191401060810061e1203050d050705030a060e062d0d14150105090a09030c0503160c050a06051c02040504140a2003070311 64
    0x2e100024078100381160101c040c840608181b118050000540a560090105050841580d9444c00d01c043c56804e11103107030b07298203110002c00d08103400710317042c49007081c2032070200551669500c203004001855a110081412002e00900c070046540e83e40d080424000d007001071800f280c00d418101200d01c12200000002d4001c414820024014060b900040180050b01e408500340b000004031008036a08644409414a5200304256104540142e580d08001000600a03007201c0c117184a00c290042e8282405000c0c045500c40f101e0344840c0f0050503920041d1225242d9900c2c0d2940000500c1c489100ba01440400c149d000e0000f0402c20080024807400282030340041c85514141548024030b40085124480b100814808164844144c0fa408082407080c600003444408140000340b140741c05c02c0e40c0050504201c5641e6142420038a03009910300a01004030010f08000302c00e02032a440360f4103140100c1000451140c07803117600829a5043c2c00c00b00c940c83c09698809000744860020749101084070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 461459685 1250 461458435 461458447
    0xf140f040e060f030105012d080709020307110313052709070f090b06070b190906020415052d0408070e1b0a170a111b010b0301060609030b0a02070f030302 68
    0x40034a80e00c0d203d000306034000d01240d41065048200305d500e0329103052001d034140080d4081c0300c099041c080c00405680d005d4074544c41d190342162029601c125101d4003c04c10071044081e29003000401c5a0a94038052400c02101c0c0c200320420143d2512029003418010089240c0160041c114074118020502c0360010103e0310b1a04040407882c68240d441050860315104006a4a4480c5402c603484680d002490b034065540707618100c0404e422284904582c0b9103441d4203c001c00c0069402071041d80c1001c90310303050f50300310004100ca151141031100d081002e103416008800f01c00d0000c3c0b0b510341d00000c1411034189a21030250314607002103a0300c449038541600050001481074540c9401140300c001c0c161510780383e03108030040c0c940150140030311000e071021030001c2e0003100345500000d03c00402c2c2442d5a62600d100307d40c40554141200341d41020b52804456141034901440742004580072912084000c40c510348031640454001800015126000c020003000510300d840b00a550511944006851310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 461460935 1250 461459685 461459689
    0xa060905091c0c030e0405060d0503070503041e060f121d06040b010b04080a0f1a09010903020d08190e0102040b07080a080903030c071202010905061302041103070f140f040e06 77
    0x4440010810188064415020f01003075225800000d49035040d40d020070141c8030303440410b21180c0384041c090114000441d10720700b0440080010b1049400300201070b8442ca0f11502e40202940541c8034580108540c1c40303400040368001c0000c04040c0403010340c00078400e002c0401c08140503040310040c0e216504500d00300000c01181608841c090100c000600b030074281400f0480d552900035407405850070100d500500708002c4020020010301c11103050361001c41c100610482e0203402d080c0400c4000d070003568002c01405108900140c840c06840380d00840070f0b0702041030070000300f009030700c0305a99540800004c2604a11103006011907031217884400c0d541e411089006024080260031140c20b500100280a41c24070210260354640342c011012116107502100d0a0b8014216584010070358024482040411030700b4001e115091402600c0030310601d039100c9483d0171144000c07120030010542c910741c240b103200c0c4158003401d00840d40c103020b1490513010321400d5030f42d5000f035880348000c0c91340031041100c24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 461462185 1250 461460935 461460973
    0x1a04090e0a05030a05250809010e030a0804050132030906011403070312032306031002130b0a021f0c0e0402090109230409290f0a02030a06090509 64
    0x2501002400c0354180301ea50740c070303100e2090130041e10400101040039074600241400200e51060741d5003501c1400107441c500303540715030003000d04030b4049030311440401c0d842c0c200459803041d5150301160751880c043c10000151f614451081c0800007c103c44001a2100c24404100012000c01101c0c40ca031240760104d4468078140c4160454056400c4641f8500d929450018101080d281d000211100d8a0840a4204d00400b120307021000c210020f41e002c803c0944ea41466540a15000d4040d01e458202c00d4519200703a10074400106019992201e0410541481c000500242038030f034410f4400c4161920071618000c01540341001156946407040011302d6003100b40b0300000d40043c2c60a41c1010700000c0040c00004440c8035070000d011600c10759000e8021015410280224020420020b69400c2d00b000c404002413031000b00d0f03a0251048056000414400d0700c944a0b100c041c5003445039039265000c000c040c2d0405483d038600f05480754401708a0140a00806100f400168001c04680510304201212 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 461463435 1250 461462185 461462201
    0x90f180f0f0606031501030b071202280516020f1c061505012a2306041b120807020a09060b03100e0114060711221a281a0409 55
    0x110754044041c4d540100c0d910b4440c0f86c1165040403941e032081d42c4a0005861601010a01050a5100041d192042d04011404011440d092042c045203840b4001d815252441541024903054a5010703002d0010300c1c00002008044c40040c02c403000f20303a09140e01c40141000400202c904030b48881c01e0340b07000b80e902d4001200400c02440c00d840d03400618600c401c2d42041400c15444800700107a00c0301e060000700100a45d80307003040e20500b0070188940080c5a26420203542c110350140c03180e4080c50b2108100614078060f14200d542c014401311031a55a00740030340c80b00301e0490300040007200c001a5100d070351080e88020702104100c81e54074500002071442e543d0345600300940034420200103105140c0420b01e60b040007a4103075501035a1707040700e00340071103c00309002900b68068076044c1f111521990a1003440b21042007100c050003000800d0070105015840d81d84a241c00401c1700001c08141641c8800403c4905d044130007070780c502e40d261075040b03e542045100300c01c403984002804201e1645a441010701c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 461464685 1250 461463435 461463439
    0x60e01060f08041208100b1309110903030f0a030608100501090c110618010f0507020d02070807080a02011407051005090706180b0309030d0903020a0308090c090f180f0f0606 76
    0x31061505580d02d0070315905059060041000000008071b1203480e100400f0040e148450303507251246048032003200d01c45098040d0701440e5040000031070390380c0c1c80740301a111502d40003405181440040c0500035610703000080808100b68071080002003a02050014188941d682400415158182040b140c286c0e5408000802040301d201c20400082d40301260894200014050f040025407207084003074058200c60444580142c605014049102c0c3c001600d0740d04104c2d19029190318660b0740c00090303201c072030350b10405030340345c00400c0710400640c41810a4208140005e07215801c1c4407041c1c490300d00e080703a0010829001a6100148220307a0000c201403c0100400c0c60031010071400d18580c050001060301c00c11035503800110100e885038505100341c4011140315041037003e81030f1401c0081da6014400c0040e00420580d0003c01c01c940b4000c40d1903c07418901800030700564555660030880e11074000c004054108100740c12020348042805421402c0038000300508900c074407084c0007800c1002c0645180c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 461465935 1250 461464685 461464697
    0x130e030702011d09040204110d0203180d360902030f0114030106060210020306060c0a03020307060507030c0e0d02120111040e0c0c0d121407030c020f03091e13060e01060f 75
    0x10f100f03a50303040140d0317481075041c0c801003400040e004020711680902c1c10040e144e58000b000f040214000d012074411403a01c540704582c061702c07003458162400d094140810380d1841a4003001c0c141c201c164405402c3c0c032400ca81c954582e0326603419080301241c01c280c0d5241c0b1025101c00c010450442644000c612804048000300080e92510001079640d4500410840c1c40e541c011000500c507a90b004161015464510305071070b00790740b5074039000b503c0794004001151551314101c041095035100784030300c8064441644034100100410410002e509080c2ca030f0072648901c205103240400d20003030146600d10044035819603103a034101286400d850f88000c5c0046a0361105210041070001c0028003000000c40c2070401e40d0000f60009000009425900d0100002102c0c10081c0081c00c0e038154041080300d40700e9030a0707031940003100404030303240c2c42030b007050b03076030180c5c414440400c0307a4900c40160040e0f9000903d050030310020405654141c0d080c580c040c02540c0302c10030040010981000d00c11150b90560f1522f0703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 461467185 1250 461465935 461465987
    0xa02030d0c0e010f0804020a150206090114040231020f13080a0c05192619032102090405010605090913030c080708070212010f061220130e03070201 65
    0x3e007100704c0d4040c0401000410004102036403168403030324016001001d01e9288129035803d0203541da98042e0744025030b44d03180c04140c00130303000089616030180da40185513200540910402030f0005505a5035543c081000903603000144150b48010001c800344c80d01d07079a8841c02182c01d0a40c0c8000300d94001c0390f00d9000340c82504001400e2411140958904981800321440106111070030010680c0150242100f001c4501c400c0308a50000e1b0000d00c2c8101080399544110403403000841640c2c44070080c0450701010b001404107480d030130302400f8040c03490b00040c20303c0c10001c0002d064640a900c04004201c0018081e141410030303010b07071a4410105404040d4105aa59000388000c0788610040c241040200321300003003010303000440351001d8000304203e8050360b0250800d4000d10102449045e19440d0200011f001214811030a031700503000440d03001d409400c00c00404503c10214083e039400710701d03030034460150310301c900c01c4d5110380485c440110388a401f81d1001616000c95904011840703a611455 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 461468435 1250 461467185 461467187
    0x6040816080d051504061520010b0a030c0306050c0a0206040206070f240b0102010b03120a0e03030a0c1505040f12050d090b0420092202060a02030d0c0e01 68
    0x4031000a003004059a15941080c1441c040300c0c091103084070b10142c00c000074405107841c04182c40c1e0400404940400c281d40c1c0e164010407000e0f0300840340402151822015a2013407048003004c84c500050840041002000840003540144541c0c0080700c0c18044a00f091040c0501441010780c0124102000c519180c92100040e640c4d102c010070003440703220b0001c1e120040021102c88000251f90103140c0d42600304400f0311102100c5481005002c0c82d91400c0d448015661050040c00100c0e88080c1c054a50100c200e01d01c03c2d8180d01c5481d420041c0300c0058614102918204020301c015040d40e600d000c441e48591030040c1e809410340b02e400d1449400c040030300012441110703e400c401343c0e04c01c06008a030040c5140c0ae0360f250140d186d541341d07a1032500959205000003a25028883c0b845001c2c000011034020001c01c10b07654800140d150094254400244108041c14a0003c11481150840d4040c0e1555001802d15802001c0e00d4005030408550141842080c1c0110384902005080001c1c142e00c100c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 461469685 1250 461468435 461468437
    0x6180b0c0913050108010905010e0304050a050d0f1e0c091401180f0f150509100b0c0a0f060212070903050318010e060a020c011706090c0318070e0711060408 69
    0xc0c42000400020110348070741d034950a4540c80161040c0600540da0745291007402000034903810745032542000c251201410001c41140c0c00d07620000c080d140d81a0401041c0040c5004450040780d005106944200100d1410810403481811207041c074001d0703501510300700c080d12607903502c0705010b0f60803c141d80103c0c1c802c801100c0c0c19100030070031140300003000c44050b5001d0004002d080d030780f544c0b6200c81295118101d03003049071403111004d41c60400f1541d51007885402c4104960101c0002c080150038458180548002c00804c80179104071140900151102d0414100c0003100305c8000d03500289030100d150400c3c004650160700b40c01c024a240d441e41d03c4803506e9100b01314010503440007008200300c55a004d007090410f005000b0380310039280d03070018130043c1d0f59007018506140030440229801c080310320000c01c40b92082c10064604041510f80c2110381d070780c81d0005000c901001c8101540000220020451070340101036484600d000c0342042880540500c03151100000190443c404110100314400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 461470935 1250 461469685 461469691
    0x14030112060209130504141b0607060e122a030712030b0d0c090f05010e07140f0d051e060319121103070503040e060f0d0609022b06180b 60
    0xc0242c3d807524100d0004220401014001401c14540018401800400360360002100c0760541140c0d042d52200c0d030001d03d0036031202d95150348100208038020014026800418001c21030700100c5140081101d2102d031550401d210036200f01075a51503000c21084001d409e01c00c106004c002071491f0107103d44a40700c122410810401c00e0549840c6602c0b0242c40340c090044800f500076070640286a265510070020389518040f00500900305800824000c2c0020344841c01200710b034654001460000c489000960000b080e2011640410700c80d1802c042d201d4000c2c0c80c0b140c0c1030a400d508152320226400103090703078050304a80c040d5010030f2b0000c1c0d1552038240301ea09416000144440c000e20582e1080740c99034415043e423080c0c0c0c00040b40b54070802c2000005403054418011034180207583d0300b0203101001c90305013a02a400307190307001e00e9000b1481c01d60002e6001400a0140c041030301070324404090030070110100380b40c034204480100c0c003444104c1c030030082c25020302c1710488080525620340260044020b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 461472185 1250 461470935 461470943
    0x3150907050a0e09070510021c03140c36090a0603060e07080105060f010c030302030603010e0123130c06140c012a020708030a0f03200a14030112 64
    0x1101140011408028800041000a10001c42103072078030000302c0a5142550050210f02c04e11034007160602c0c01034042c56101b9041d41c0144001003070011200c3d100c03140c90100f8000e066a0311071400c0002490f0014034400d140807070b00f030707507443c0c0406000a41074801064220024548002d00c0c4811011610050091a20885044883c3d454860305207000300319030f43c801000b4500d401404004954040b6481040b140303503400030003c45e60384005014080210b140c4050021300703803050740c4000038041d5000e035401c4030014000003062b50016400c03500b1901c40700501d210284401c120b0f56010220040046c3c0d210001401040900c181903a4000721002ca0b070046005012125007000d040e010000240c4101c1e1421a00078050130f9011020307007809010349002c90080300c2681e0200544540002014011562440015480c1415417001102c41b20b00040e402e00400d03445004100b0680d580e0488c8880d42031074507000c15583c2e4010780c00545418010100d80b0101d9005100400203800d814440c0801ca40e08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 461473435 1250 461472185 461472223
    0x706050406030b0f0301090b180307150203073c09030206090405090a0c0f15031b0e01020f160e090d0503040206070c050d03080109050709050913060908040e0601020d0e03 75
    0x1120b4006100302c2c4c54140344c990550319109400c010320820402c80c5004124200c4c0520741552420111901c81c414074030098107600c104011020441303c25401181e00c60910714080385055a40030404c2e0404010048608240c1403c006801d400500c2c2e80b10900340241c103040940d031403451607011588500075520441e1017070342c0e00e000003a0980010300102d04c41690210304105e205071102e0203803030440740c20f0180d2400d40e01046260710036680280708048142a07481030108840d140d001d400c40d140d00302d03040c00904500030801c4864000704104223848902225500001449041c0301000d004690000d100c0b130956806100c500c42565007213000c80c1d41240c0c05890702c81d0340e601c031810043c9400d6019406650002c1d6514208800d00d5802300e00b050581d02072107024852a100e00000712515412400380070f0384100c809003c2503520a01d4440030000034482d40c40070071008001d840d00303000d0b47c0155014100007000641003151a60341807201c50b171640c80d2420702e4001d400100011941e60a03103a40f00d0040002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 461474685 1250 461473435 461473451
    0x121a010905131107150f06030213050402061603050d0507050901091401020313080a05010b0609030d110114040b04050d0804030906080601110d020705190501020a0b18060f040b09070605040603 84
    0x20940000701c0b0202d0f5241c44a40d5010759151100b04045002e192071480d62802c2403108441c01d490084008698009100c1d00f403000b8000200b90041c0009481203900140400c502e103041c01da01210f0303002e03840c040d40b40c00741c40e020b052265100b80d07070f40102044100a010480310142c6d81e000780c0d180d41030b0b4032910904410103e507c070050b441c7d845656aa44c0c1d0050a8107800030b01c0207070025803864007610900c024040b00c4140428040c080c0076146c04541e05070080401e00c21418800c41d40f0140000072400086001c000c24000c44041c80c10565099550340318a00c1000140202080940c0365408a840c1205151030642c80042c00003407507004200070480014080345150388030b840d0f4000c00d060941b054840000c60044042e64512042c4502400748a140a500c064041d641c0ba440d412584181c001d00000e603843e82d10003c90041c020b20300380c881410080d101440f03034000c002451003000113035a860018206418001c110600040003010703107600c50101400300c2c99000040d00c048954500b07020ad0019 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 461475935 1250 461474685 461474719
    0x1612030608010b102a080d0e100624090306020403060e0d0c0302060114120d03020a0f05180d0c0b0a0903110301051510030e0f01022104030905010e04020c010507121a010905 76
    0x1ca0f4882c00a004c0d0403021070320348010b9405502c4808c00c02c07200c104441d04000d001c4004016209103204e0b10301c060b200309098421010140194001c560032618012031000d841fa501c08040fa0060380007501c00c10741d140c42c1210001010401c00b0000300c06410030300342e141740c03d070703030003540c580341400350741612480206440340e282c4881d050401a030a032603040e0750807140500340050003500111450b60000d14110240b0081c54024011509010940101e4070307034540032041840310301400301c981110031020100000400e5840680a0070340c2070103640d19000c0f90351030343c101521100907001c1c4251099240a0601c80030408205000300e5041c4250f03140801c91800e880c01f035006007541810210350707003d0580d07403090000041d401441090700401038548a441c00ba10340130000702045070000c0c04144005070031f2107251f0040c031313540e0301e050310080002d072a048454900c103081d43c0040c0e030010007240e41540044112102030060200c0703407580c2011044481078510000740032103000d110b024060a29405000300f50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 461477185 1250 461475935 461476007
    0xf0102060f0a1e0c0e0102060c041805150a08070f0e011d04140f0106211a090a1401050403110c0d020108100306060b0304052e021612030608010b10 65
    0x30f0040d41004c201034040004c02030240c00c62007100340c4c0103000f200002001500d01806441c1035a0b8451401903003800403d070307080020500034105407010200c0340f0400105503904031940010704040c41c0600007283c5448440b00c2840d5082e0401c001c4150100010701245040e403c001004c080342156102940c1c43d5030a0003a2588112080d13001c846c0680144c0304419001504140c048507100c4540030100c10010004007034070554190007c00d00a903a082e04280292001e81c141e801c81650400c1e00c07100354040d6100c4d0b911164481001c040340e5140c4041000341034005621006218503200075080300e421440009039520030b002c200a040c0810500408c0341c030004414030a0146a20150400441707444401c4218507800c00c07101200e2911803c01c90725240c040c055074050645126141c0694440709002808001e904000203c072002507240000310041110f15102d00c01d03a00d910f441c00120241002596402c0d10001511540600031070080d01050942c00f281c24075000081c01100140720350301449071080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 461478435 1250 461477185 461477231
    0x2011d0a0317180306090a03081005041e0e0c03070618170708100e12030c0705101e0902090c0309150a0b040509160501050a051608090f0102060f0a 65
    0x1001e0206902455007002c100610b1a0f4000035821a00c00c1c42e48003c2603039a00c001c58a152040d045001031400003405200750b40e800c04040c50b108541c241d122804602107230004c10000800c203120b0303c1c40303a401d13620b80e2142c3c91142d03000c50040c100358120500483c0e600c1413944070f22020000079165001060324007554045c0900300388000c000c01a281c01102603580d4129001e5410f89006901088d40b040146200720360444100c0300240010b080c6518074007101d03410040a04002003010000c0c600028810b0281c05507d0190704000503642070074401c0f02807038408004026038070b5854203000601607558403080562017030320340d40d01e26629940c1405c00d9041c0803920031804c0724136200b8414840c04102c030b500800362090023030b01c0800407075441210481d070740d21102a2030312030107884540500c003952080b070080c80340c80034a0403d03d00e0001080c90911080030f42501c1507030241004242c0541501d0301d08081c0c1d080c0c11003440107040b50300302940f080340c0c02000940f803050030656a0980d013806d94401500002c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 461479685 1250 461478435 461478443
    0x50939070f062d05070e18010e01151d010215070e010e04060509160e120a0210090b040b1606060314151b0c010b0303130906050103060302011d0a03 65
    0x103114040307441d10400c0070000a2003114554140035485034203150050a99070024854070340c44030700c1c001000001d401048007810304000c10121068400080c0c5418491100b22800b00d01c0120007507140800404030348106802200b5400062f04848940640c8144840a510340450110b90000c074101c0c0142d00d00344d22000c2e2180c40100c04410003c00d10b401004a5012f84020b8980c40c80c040115070410080b42c565000f4640d1002650000c1003c00304001030154800a031070401600703d02403a800101e03009118003900d440366100d10325200031401d107045c00100200c5c0c1070400c010740c0781c00d03d408113041d8040c81c00340010041002c070b2141c2c41140050400110984c100e541040703010303283d08168004d080e900702189403510509000c11081410281c1580c400c1c880410a020103804200c1680555071040161017801c0d07480700c0d1070f50a251340c00d000920324014440741b02510a0f14040110042c0c84240d4899418140307088410030142c0d820030036070044018441c0451075900780f9040025030f50078143d08050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 461480935 1250 461479685 461479687
    0x17150405010803120114100e0111030d1a19050d08041802030901141614092e020a0302031e0d050103030f09120f170c06040c0f050939 59
    0x41c5039080840203107080c4d034244030302201c96a02d440700d030000003443c0d41c101900000140d001d5483c1901c0b43c6140c29408005260512110b40e40d62107080c0303150007000406403429500c002c880381c00343c00140d030faa01c04a000e0f40e6100103410000f4041b003a0350f03a01e12031140101480380c40c94040041000c02c03100540920032155400c607919410380030003500100e400c4075146d840d1480380011803009030b0034144aa110825000b045a03101d000c1111000200102c826114000340b0102c52036564a482c58006074003c0b25280400e1170307100c503009031071340e58500300c160941d0000038100c004030307074040222043d8422250900c903490310700d0809404603200c1c8110311045145018004001c042d41b2940031403142000e580c1d52840b01e03440c0c1000c40d284002000c0b00401580ea040d080e240003640701c400001c3c214800d035003030b80d05114014080c42d080400844049a00703444019061002d165030303a01c3c03800684021744075504507282040c00c0410500d0f074407206401d0003169111207002000f1000420080e01c01484040b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 461482185 1250 461480935 461480939
    0x121e01030f020a1d0117010b0301060b0307140c0c010c0804030605100602010c0203040e01091104050d150c0f020303130c080708010906060b031303080c04030b0c030f0a05071715040501 81
    0xc0074001d03500d01e80c00c0344160341c1d10600007002e450102429100000d06602d000300ea910b420b000302111104d95030b50001c1e43d5282c0201418030b640071700c140001000c658000035a01e28094200404110b03004d42500d202c5401805091102d400002d0018041042030030303d036036618054201030300c150045600050651f03040c5400c2203024010032100f43d0403900507400034007103414002d00503a260300030380c0900ca86111105004002c0d024454008403103070700c00c218029182039203920109a04d0300c6054070948048950032042c0b4054040b038415803150303042c03502e800150f880c40410001c0d124880a046c5007074409070004400b0502814000240060512900329180c842e9601d8030303a8080c1980b0103040d60814070f4117030001910003882d01240e2041c07840031070038170703e045103035a0584450101078120541ca003c144804400200d2a120040c0240440c044182e180d2825080f461114407000701002c2d240340c1403006018074503400c02c1620390a0316924030600b5059031018041501305d9034000c4a954014204800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 461483435 1250 461482185 461482193
    0x70602030a061814101505030c0708030c03042d0602070212061504200702060319090f02120a0809041107050102221e17160e010f050a0506121e0103 65
    0x10040c0c00c9480c1c1100c0c002680d81e01c05e5640b0901040c0d00c21894000034840b500b0300400d1245000f5a4017904c400ea066041404c203865844444d0030850b1661a0007100000b44400e010231407480106502152084010300145004e02c1e9101e141c1c4404000d05454012881200b19503c41080d582c1c16a4510112007640c5441455900c048129807461401186003078087c1d0542c01c01009904400c40783c1c661058585901c503800d00c0216803000300030720b445204040c40004414514013941e490640240071910074800c4e5801049004c1075414511800c0768000807014001420f41d8055031042d503422a00001c0175180c06800032903d01c2001e0b00100203510004481c9a40c01020441021903071100111001c6c85860301d41c0c0031621242541c0b50551a44c122100704108483e600081e81e42400c06400d43c1c09542c034010001c0103001071130f040400c80c03168010040c03000300b10b11081040148000c448183d44070381b0308400b054a51054108815884071644005038890170b2003c1c007500b4261801f500120b0b03540e585e0078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 461484685 1250 461483435 461483441
    0x1b0204140705031f05031504141209100203180105210c030f0603070e0a020a0903080d050103112707020304031703090c090c18150a020c03010c1103070602030a0618 72
    0xc4410320321001e520303110200041d044101c000e456000e030081c10b1041c509038094002d101d000340102c0314a4400d00c408100ca100902c03110b615542b02102e41034441c003030403040000192031015190b0031503000784210407405460b0000c1906142d02800c0c02c42d600c15000c12080c001c4603804980d40c2100951809200d081c07a4800e005500c100640072000303c044e00c2d540c0c101a1220791700e2045040200083c1c01095120845078014401fa40607030604d0814030355a541c072846150004054004840c1c2e40380010410b022340d007240a81421012940003110480390320b0079640c640300c56204044a54518000202c81c18000c04c1190061600701c0c01d10000c03d40c3d840c04028155204950300c03071a0f0702516103d20b045060201c18a070045448100807401c1002e900702c043c1040c4040810681d00840403ca07490290540600a210054403640075101e88a4240281401d441c100a1604100114980b4200f00014080141d841c8554818805030350b0f034a50102403c027034040c6803c5000400d03140c0c1400d6100e100994 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 461485935 1250 461484685 461484691
    0xe150109060e1311310f0c051b0c03030f040303030b03030f0933090109050a030206032e090605100e060a05070807080301080d021c1b020414070503 65
    0x1050a01c0700d42d0721001050741c0307540e0a540c0100100d2950700c5140029201818088076210003411005100315804810520004181c001d03100d0340301003060000c14011503010350440c105451800b807000003205000100b10380309181c1e00c2085d5800206401540c81c1c010301c4444c8140b84014200ea40780c1200d01c500c080658000e102c2140824589502c0c503245050210580303c025141e0102d25080080000c02d200c2c2001c40261400d24051035010240641c03051064528800031401c9010f6864011500c009080c00145400182c414081088200700607512502220b5100c846818403000d03c0301e002c619100c10701070000e00c42841e04150040850792075020741c0301c80c040710021034050307a5880c000c2700c054130003825401c0c00a8106074200600e0700d089002d80c0c02402c0d418803801c0707094501401900c4058050b0402e0300301d280160084d038001444079a0402001032010496500d400c0400074109000e001e0401d02032a034114181d080c0c40d6807082d551550311403c211446c1c2141552a07182c0000000d1041e0720807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 461487185 1250 461485935 461485949
    0x405010c021c080301060f180501030c110d09050a06030b0303161b03030503040b0106181e0b0d060f061115180a0308071b0807081305030703030c0302102d0e1501 71
    0x41d005602c3e207d8821f904003040107585101400c0d005060400440141c0098800e06041c0100c94440c40d00078a803c1000c2c224580c0c0980d42d142034641040308100c180b4516038080e84c2090700b4007034640303090396001c003c4032001024031020204981040c42d000310f06242400d203080c21106054000030903d5044401144140e200b60010072561307882e0b24041d81e1180c0e4030420901c004890220500200e0f0a0025840241d868039030404091a034405d203030b0b00164004001034603400e41702c180801403158000052009000030303045c00803044018089199440320700c038440300c81400081c00480c29803881003030700c000c200480f1802d4900c0340c030641c14080c210200580f51040024210010210100001c0d62400c4003a90300038802440d2032181c1e01c4034403598124000c0c4951a46010000103080e980c10400180114070135103603001421802d00b00603080100c45a6282403844c00e1503540032a040c1c001c0c1130b11101d2003d443e580c02c40c0c515454107090050400007008042c40c4544100d2501203c5800d00c11341c101d5500c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 461488435 1250 461487185 461487197
    0x406020a0218090a120504080313080c040908160303020904050c090907090609030305031f0f030b010b0301030c06110f01060906030b0a02070c15050d050112060e120405010c021c08030106 82
    0x34980c60b902c200c0390112400416500401d032020005041801001c0000c4168540a424182c4405015082d81d201000b03040013002240341c1041703812414858641511004c4904210494241e201d1008512420b50241c02840310003002078201070099058418498015008020324a0030002c8a69242e0000007928840e17618000040d40c4a03120303411300c1003901d41556414030706a1131503034150740c20703003016000c085401507030000401c12503811340400004005008803240100e00d1420b001c4800300b010381000403262170400040c404242e4011000007224901d2a001301ca03000c5480d0800d08000034004082265402c00700b00140103102a049501a280194403410250303c42c0c5803484e00b00d2203030308801400720f0000d03035003040548040c0e640c00310031202c4c0e07062103860140c00c0c0d48103030103d4000360030004907030207d201080144100b600c250340e50140000700620310300f214405000418001ca10413035042010b80300080c821910b0b882c0c24150245802250f42002078142e1030000d4154000340240c0000400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 461489685 1250 461488435 461488459
    0x260d05070219060e04020a09241209050d05090d020d060506040f020721110106080303070f17010509150402070f0302010e030711010e04110c0d1d0303040b16080406020a02 75
    0x2a80100c0b44111041a101d41000707104407030900011750080158941400b61820380000c0500d1030045440e08911402c428050032864003e02801d840e50040440120038901a81c04001078800615403c800c401e5062090b2144210b8000400b056142034000703420442910800f420410340740c10580c040d8108480a10442e244d401c00c00c0201e0180303c2c006807001000941d0002030501b500b8032428044410301d01602000005482c20b42511784d19030140c01e45900000821001b40c1d840015420302c2d000a1622800d500c041c408000759401c01030003a80d200e0101040810400460300030510000d01014000f0340d114000d80c2414400d29801242c00c0d0059424000d104000084c0802200c5021794803110020402c80300e0030045942048242080341c21954500008034a0504840a040c074040d0000040034180c2464600801480070354030640c2c402c0c00c4200070207100303680110a031026540002903440e11806000ca40b01c00244809101070100b80001601007088c507404620092640d0003640d400000d05 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 461490935 1250 461489685 461489719
    0xd0e09220501062306030c0d02040b030705030a0b010903021327140d08060a03030507050123060a0f08070608060303090a06022103070e0d0c0f06050c0f1204260d050702 74
    0x4051306603602d9000780c040001458a01c0d900c400f41112207843c3c1001804d19480c1c9c910861907500c01e5800b8004520084100703c40b400c1c650040c41e085500a00e0030b4003005255901042c034103160344000422042d11800402008498400c90000c6140110051080790130542040d0245a207800d4480c2c015000361500c100000f07014480b107500400c1c000d404180090300d51388003250386400c0403000b161155216107078050740101802c0041c001e40208040300300c00d4149141000800c04507035019911103031005600b00001c8902082c034001b2240340b1308246059039618000213046100e454a6658002c250f00c20200720789a00251018010707409412946141d540e589052907140012512100020030301030f168001824a1800403c1a034450000c3d040480e80352900c4900203109500850002400402c61010201080180852200e8400042c1c90303140204061034500d48030324081d8801804894581c43d100e410000001c100c241038650075034601c1100742600030200d40c07090700d0a074800c00c0200c0a6074029 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 461492185 1250 461490935 461490989
    0x112050c0913081e0403110108070804230309040c0503090609120a12140103050d031a0f010c0f0803010816050609011d030109020a090516020d0e0922050106 69
    0x29800301102003541020b26610703030301e644d030001107144041014002c50500c2d40d2040300280000e54802c4180e20800c2d41150001000039500030314031000c100d452000c1c0404942851881948110881e0119050243c40c0c1c030803074075520910480740e4120786000301c461005584040514029000e07102501c0d06600ca8075500c2c1d541e641c002440a0000c04200a4440c0042c018103180c03003200000400400c914040c201480c800f0305003644185c5150300803101140c0c40a60600c0b4085420781c0301a80c1260881003c00416905080503100c20305026814004c54140030705041d00c00226a809842295a5a1075200e4180c503903000136060401c10300342ca14081303a90301e80305064070b124000683d1071413440058800355000c1216814143c94140d50b03640f44903401f50712001c035400c0203414031290111710760038605190009100030304c00c0b00c011500b1a0441c600199800446030750b42880c225043d00c0d150b12190f03c1d921200441c0c10364010740502032151003080080640090302103030010343c808012514448880e200d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 461493435 1250 461492185 461492191
    0x150421020708060a15031e02040b1e0409030309050d0f020601170c0d0611040902040f0801110a031109041e0c08060a050420030c030f010504020f070f060e060112050c09 74
    0x8941c10400c0000e60210060341710740c0c0d00c3c030b08018400c00190354030345401e01050030741801400c0b200386100b4043e042d0b06003401120303644d400c01d6403c041181000c00d0143c1041c561041950b215031385403002c4c1018103200f030b04078003503003508401a2580c94212250142c4844072158020000d800b680f000045c005014002c010001c1900f003015100789280e4004019180703148880031100305d5a03900980c0500440f980107080074080814006990301e0a01115842c1c4401d030ba4002540d9a0610340c00281c0382c802001504d2102c00300e03040c0424402e84002c11030030316001c4d01c401d0380c0c0c0280c84c2c954200661002c010010704140000300041260a440e894210f072150b800729081034101003581020401d504043c0e0061040720318848030007052004050712581554401c0e076444640101c00320a010b03106c00711038100307801400b044504515140c10f4401c60741e424018082c0183c0100107006204c021700030b041c2c100c0c0c02441046400d80d02c00d90385030079501035100040541916079100e0501301e003003d400c00000e0940 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 461494685 1250 461493435 461493449
    0x71e05100504031d0316060203040618031a0c070b0c090906010e091b040801050106030e070f050a0924090213090908090d0c08060115030f05040309030b091504210207 73
    0x8040b40501d01d8180485130508021901441444003144410b0002401540646001e0f800fa40c2d0381c41c0f03480307001070034071905084110440c20511000c0000850b0f000a4640385510f40b00c4021081c1d42d11140c001150040040c0034150340c80070030800882d121428002d18040e41c049078070700a29141c00004654030300c0501c070040e811542d2040806d450701c3c0314183c4000c4e00c20500c52040c0c0303043d845155180c2521400c7c3c0c00000425114240e20007c800e080c0701c0d0708040e160840d10b118881d46040005600035042c0e109014150b607503208814118014500e010102c110004031000c1c01568845014000794041c000c6d100c20301d0090071011906880b1801200003081e044030603c0d0400d2050010841c048690303e0086074298071096002441210500c2100c1c0203018894955221007141072000c0e090b650444c4110029502d404100400240c02908500640350007074100740c00359413215415490025102011020b08404404107c10044030380f610503c039040c02640d032140181c0d081801c2c0e964000b5401909 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 461495935 1250 461494685 461494697
    0x60e03120a05100e0c0706090c0311091905061f020c041d10020a0c0b070809060c03220c050a03061b02060928020607120306050f0a05040b0402071e0510050403 70
    0x113503a0301061016000701100c00d0b054900b02070740e5036000442d002c80c00112100c3d08041800c02c140111b6800c1c11110382016143d1915034580011400000c030b803808168403000c1e6940d07000c90000d446d003040f8503810604942c6840c2c4a0000d0000c069034560a03004000e104a0900000e07192008805403a0013403600500010086840ca011010000c0d400c0b1060004c100040003c82802051000050500591107600c44102904002e01c0e00750038a28000e140451041040090029100e907400001d8084038101d80c5070800402a4604040c0c0550320390b000c168080e1101c08040240009544000d025020380121060700c0034000c003099807280c404940011080e003010a1848841005086031f00ca0911440e000c0399103040c4a43c0007403c2900304034425202540c5a03020b002400f0b40603c18103020b05412540342903403003030382d9000540074450b42c014240143c1d152a000489038440d50140c0b9892640822240ca441c120050341c0001c0304903504003034642e4414441001c0c1c1507010780c844d041c0916015aa05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 461497185 1250 461495935 461495939
    0x19050910050d270302061609031b1802040611010b210309180f090c06032412010b090c030c030414150c1305011707080601020a060e03120a0510 63
    0x40d903640c1c1101501802d40c6458074821080c200d903490b9410350062090105090000260030001d1400384001c1c100703650007a5840c6043c921907000000300c81208c2e84000896030700103407406450b0070401c496001d501c4aa001500810b0000b5068010308180d65095880000e004901c00d641c90980c2c1074441c195422008003990b800f1040000c0802c02d14440c2400b0840f4034050342c0c00301060100d9080783c4948492003000f0180300040952580c100d8000303a00c0d0b401070400200400c00103000d840094400d90300c100c40c82503c02d103c501c0004140c00441401030000c00c00070452814140a0941915a1840703000e9000005500710070f4207055a00900b082c50416065544503074038524440502c0c405000e103441051000042c0f01c200c091110f11520242204517221056650440300d28022030700214103008040c00c40c1e00c4943e040b204c01039408451072614044036220200142d08080305404098001070030025036200b8030307500000802034001003490b0340b9070503500c100440381110001c0e6400c2041c44600e00782 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 461498435 1250 461497185 461497187
    0x501050601112803090308040b0a11060915150a08030309160e0103060218210d0f360e010816060c0204050c1c090203060a0e030a0f02030403060e0319050910 69
    0x150316089100e070600d180c5c51038aa8032404900d07086644a030070b010074000b604440c855400007402e003801d00070710004c080c40e0902041150301c8405401e00c0c03500048800f40061040344a41404800003140504103240a94855200d15180d90044a01d240984290103a60001d0000598500c00700d52aa84d8050b145034295035504000e035203d241c600c0004030b600c0041040c0381e07845c2e141d00c460800031580e00e810202c0340056414104400303c0002c0040c0302003010036990081e00302d020b9049071800c0301d07000e208030070f5600641511501c005200b5640d06241d498040b4115004081c0c550680b080003046078000241043d82c0d640000c3e00703018031000902140c020100508003a040742c1c1d00b010034070030760606041c14020031401031a14512106646502e500a0340103600b803e014190304007045090078010807541030007441e664407820848204100545a50300c1c3c03014401d0003660702560384500241b00c0f98104408550340c940284021000420120030084042da000b503080b909160000f03412001003078a0030318 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 461499685 1250 461498435 461498503
    0x17030c1510090c02060a0b03060105030309040902150403080721050703030c0212370e1009030b0f06011d100e0a09061220030c06030a0209040603050105060111 70
    0xc44403a15100504020448201a0283c3c42c18002103500401c0c0d503260201c910802d0358840d4450600980112700140807985000c4111010540262808685042c0d144041006131903040b42d09124850042004410450500000c1c44070f070303028066150b503205018494052080d840d40e45e074800314000300b001a0000780250064140c08400d40182d0300319400000300d02040f50f1060303452000042040310f1084810519020740c1d4114251710a89020412060001810352400420041d1203a0380f42e1681d00d041320b104600020185522503803484040c100300c540211035602c295035042c04038010001d0260f0f403210001c00c1103034040c00109035481000c020501501c65080ba500d01300d40001074244003244181080c000c4030020084070341c046c0880780460030b0064119801090511082442d6445c100060360b0024205e00c04074000c450241c0c1da602c41d0004000284101c49420750041d0a049000041c0201980840d00c0b5030070a807a08044000000f040c1e03515480d0301194a2140519403810705240c001c201 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 461500935 1250 461499685 461499691
    0x70f120902030a29010503030301140d0f0803040c060e032d030c030408010b0d050705010315030b0f15010e0d0f1a04200604080c0f01090504021317030c15 68
    0x8500150054032a00400d0030104125001e481d000200c100114000c003448001030010001d510ba03240070341d41000000382c1c9910061042d014186000303414982596181d049045013141c2c0100031500e8188540303054501074004450030b603280504030b040002c0c698003450516200000080261495582d1240280c0c030307030000d80d1900d4903608041c01e0258040c8404000403c21040208010b58850786800101c42c2501c56510005004071000ca01010010b000040d002040d2003003400c01183e40c087c010780c4601c00001990003d004401c0c0c443c02e100d4400c021a0800740250076680425040d10014001503c40364084940030390080000041d41002c42c510701080366160384207824003080011115800750201d1800d84065515859a4540300160041a482d04a118000b030710346604003482d2650084e11800c0c2034a000f030041054201029003030380f01e40c40780c0c00540001041151a07075200710710710403a84030341c1c080c0c81c012401e10400a0081c440000545180c1c0c100c0038010034001443c1050210454406 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 461502185 1250 461500935 461500967
    0x3080f150621011a070303021c0606030f050610050d05060a0e0f2d010b090a0314010903020606040204030210050a110a06050f06010305040b07031a090702010b0a0e070f 74
    0x501803024465a408006014200100e41c0301a5035242c00010b80c1c9039410107900c41584074501154440c40680c118040e42c45268050400684a00f5007400142810940304031014440b0b290050220341c06400d50b0002e004480521002c01c455981c00090100c46134915a84201041c0d050120800c908000d420442d4098009021950305c1c56892690000340c1c0ca0658900c0410325180040200501100c044240114400c60000200e06c1d0f4480200721400e40600036406600310001c0c0310711a0b619801600401140e002812826948412001034000e02e00544101d0060107000c001c508549464000d0760140c98000300035141c40703c4004030a5410303a1160201105000010344d2f485106001409040c441c54020344021801c0e14200c0d090010740d020050406040c18500000d010120305a001415070144031030800092040603451805000d0400348099940300303030100b0030070540390740c1074004d18810b1000f40c0f510040d8035210740d00010a50350883d989000100e089403103601162140c600c3c2c551304800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 461503435 1250 461502185 461502211
    0x8031602060705061e0f0105010512040204090b041511031006030509100f020703200a1b08161a0f180f03010c030c0206070f020c060306011412100501090303080f 71
    0x4a40c3d0303281c1401c404a0300c50300600300502c81e0b44010034036040d10341d9008640c4400029258100030028140c1c0c0070345451180545040310024007107440345e40c44038030441c3d00880000301620f003603c0d180034405100c41c040d82d801c90402030040c400407034480540f8090310340725200c2c6007024203050084000300401007400030984030340f038010042c1c81800c1c4122500c40c2035075900581d4031117150402804800b448070000500e0384111602c41d51990300030500ca440b03141d2110075541d4090304840700b000140040e4018117050f000705c0042c04000303480740300070307100301c0b8080558020024170070180300496000301079400130b0b06c0380104103429041e190444143c0011400078004640c1030048404607086840001000c00403a46c0c1d01e0700d0040250301086400c3d072204003480c0144441c5982400252a411a25a400d019407000310100d01030740e0007a072814504041101810340c403114140300c101c40c091300598071a450610680e4000c80d05511800f032a1f000d8035095244d00b0500e460347c003003d030041c0400070311421050301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 461504685 1250 461503435 461503447
    0x11070f0b0d06080a200a1412160b07062306040f0605191d060315070309060c080f06040b060d091e0506160c171b070810050606090d08030c132408010803160206 70
    0x1c540048100030f0001c5829071515500503281004c220703003491802000c5c0d050702071101d41e0484dc1503c07240c1d5002c1c009440c003090f080c0720405510050900d82d048264092030310264400410200c54091045171012400c03040040048801101100702c107889054041c2c00c4107a48040030700280c00103e07008500c51400046105a5403035520442c0d205e201803800154000040c02810507a50f140e00e908284210f900300001466800055424810011901c1030180c4174042c180c00d01c48501405c4601c1403081304501c0b144902490802d80702d0408031008014401000344100c003441c0b10b40d0901051903400500c441a02d04a402c0f490040e800c910742030300401c4180e00350300b0f851a10034031004000713004c1040202400c0203087c4030042910342c000d183d1400b91741c003804201071301c0d960224030035000d40c0c0000c041c07907890f2121111404035204003250a00085a000d200192003032507940304092440b501d5882e0045420084400c81d0241790038881c803c110ba02c03e22401082803c001403a401040c401052146048 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 461505935 1250 461504685 461504713
    0xf010b19110a0305030702060f06011d010507060f0203071403070504050906060c0106090204181e0b06190c060b031b01050c011d0a0311070f0b0d06080a200a1412 71
    0x150b107052003100002c00100074440116010410320342c00910704a440c090500d80300d00002d114015125904d504094111454001640074004545030300740c0241060102c0c4101c082c100010f90300607540750000895203c4800503100a000999008806035590145090314040400143d00b00c003511071030740650f0400c0444c0040d002481500300504801001580311032505c65901b112218000c007920260f410081d030402101c00c0703041b800c803c8404200d40020040c0b4900040b43e0703a8045e003070b118030b07a4100d0021102e4007181c019041802d8144641000c0c010044000141a00c0390050807000345111900e94440481d503000d0b00c06001149021000081d12030302401c41140c144c0c030071488000168010340d840c1c4c018554445c0041c001e04c05100700a0000c546414150750300180c1500c1a640084000300380302c2d1011840d508840d00a00e082800c45904025500700102450882490006101c0040199031800c1c28001c00040c00c64000d074565030150407481c1c090000760a440028130000d40100c4888844030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 461507185 1250 461505935 461505943
    0x7080f060103060905090c0f1c20030f010f0f02091c020114130e0915010909030318051f06080a030503060f1804032624030102031306050f010b1911 65
    0x21840341d0020601f82c107074002400800a824441640241e00414014174094280c484c10401c540d40000c0041400310380101e6200010203506003994140030301003010309030070700c1500310100e05008043c040080417032a2444804130300c00c121140f500901146540302240c0c12081c1c20080c0c050060402e860003148005411035290300480c08a4100134103104180481c182d1405034650020041d0001c20740e82d00c4c01c80070140c0e442414841e09a62603291001d42c02094802d030809809008660561000c122042c030704503484043c283c0410307030014410b1070f684a51900c140101c00441c1c1113200039000406d05620211440e0344010500354201d48590000c2200e502d80d221100c2800592110440c0f09040a250043c000208180e5034441c211100a40802c0c244403001c8240d00840c03251000c5201240304000e451840740c0700502103505510100400201316002d007118444541728500410503540c2d07002c00c640034070200f03001d2440344800c18072107460001c6018491000078502410004004401203420f1450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 461508435 1250 461507185 461507191
    0x31b1203051e0d060e0108120702150f040e15010306150f18060905150c19030c060c030506030705010201021608092b02011b030f120209030307080c060c0307080f060103060905 77
    0x4d0b03991204020030011280030a005d0281000034003a02c08200c1408002c90240020117440386039410308260030005040101d0740d5000c61030484a440e0399550030818001c1c0350498601000c3c601c0941c00102030b611034480c84065480d90302d501d943c94441c084048030204402c0343c002080c8500803604d0704020900300c1e03071080106825950280c0391814201403044410400710741c850f5655041c826103e400c1c0c0080b40024220b144c2c0d0081500c4006541411501e8081140c400380c00c4d00d141c280b045039580c2d450740240d80724030800d40840f00c20766a40c5004900300d01c01c41c074400160042c13071210350740098084e0700140800380c001000110b1032800903155425030308000c1c2061448001004207e070455800005401004e160400c01125404090b1006003c1c40a285108030410880100e940d1041d403040c2d045c0c41d00ca03240078044070740740c001c00e20380b6039110381c441c417220110340c400c8800052520842004880c4104015510210241c0703c006c5141e00e00032010b4070142c18940c60b07203804a003c00d054071421348 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 461509685 1250 461508435 461508457
    0x1506040221072c0d060b121605061c180b341709420106020a060207020a030f060f0b03010507020a0f0512070b01031b1203051e 56
    0x80c150520600c083d04085640e4a44960080c2200030f0090940710450100403100c0203460815408034940340c040000d100c5541d4031907011f45810b2403500b102c43d000901c02c00006145402c00c11280c0c58004105c012700a0750000f1443d0b00800c60080c40b17010035508000c0f130035a5080c51002c60b0403d2640e0303071b00f074142044030328801e081e01c00100c01d011002c40300c000c500a06202842e546030423807820802030107410001310492030702c003000010461401d4108002d01206c03402190800f60908070546892213401151002032451441803100301c0b00501001125040303940d540c00070303c042c008540c1d4540c0079400006090740d01a041ca6000408203540d41c00d10205903104541c00129405c3c0c825044040342d205507403042c0030740c3c500360800003c20340000f403d1740242c1d04900b05603082c028514240d45450300740c488001d29640042104010031442e016124140c0e0f00c5044024174085503000c282c02c11b08214841c3c05a010400391400c03021a004a00800a1244200011114080f02005135006030b011085001e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 461510791 1106 461509685 461509747
    0x51c02031f080304090f020909010314030705070611010f0618150302030a1b120203070e0403020c040507110114010b04140a0e040c0501030c0507020315060402 70
    0x40c0c24074000740c0703000c0303034554544001d161650024840e01080320305000d080c2d221514039000b5a00c2003007024151903181e80c65500c81c0e0030720840250b584551303800100310304000310b002444038501070619600d8a03510500d82c401c2c03c3c0c1c01c40b00d6a180d40e030302c05403800e8010300003468944212140800f11186c04030ba00e482d502805240c40d8900da200039450300c6440f000c01e0802c8514030005012480c02d907051107015583d0a115448030404520095064210320018810700640c0041190070074064030448811110300800319007140c40543d20071020a4640c1c0e81c200c000c04090203000280900f011003840c0c075515080c0c911216006600a88a07001c5020404ac01c80303441e110101002000c003c2181926070426080501c07403242d05014032030010f410b018105416500903012107040a5024000300003070444451900a60b100140500354029000c000c2a8407100b0955820300b50001c00c02c03004 = true := by decide +kernel

theorem cover : BRFrame.Cov 461330935 461510791 := by
  have h0 := BRFrame.cov_init 461330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 461330935 ≤ n) (h2 : n < 461510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
