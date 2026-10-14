-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0363
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:25:51.796499+00:00
-- url     : https://prove2.me/submissions/db792d8a-d931-4b7e-91f5-6067acc03fb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 65107916 ≤ n < 65287772 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 65109166 1250 65107916 65107919
    0x809130b010e1020010507020f03030405060109050a0e031b07081209120c0d110a092a020c040212160c021806012c03160f0902090402190f0216060801 66
    0x10320200069540c00a03082c50080c456240c85801d10710081904410300d20b1b9120f06c01d21503200c0c0c0500130072810031030744405549540b61945401d651030f441032148110180d520000102c0701c0c01994080d1840d4408c05040c1c9a6680110f4140c000041c41240042624018848009283d40e40000e0000c40494900d14507070900a07158100900d00501705d600840c1805901c0c4408070340e030b9400c4000504203100b0400b10784120803010038001c83c000540c100310101498210001c41405040c0340d903114000c00d42c08410f0908440b000e040707081c0b82d5801c3c4e085400c1400810066100020300360264402d010075003860350f83d00712480003251100780224000e904844204c8082510100c658141940b0400c10305240348070000519071443c203e400c8400c2030743c6400701c5400145141c80c0510105010404410101c3c00e09400e0141907030340c0c1d007440d103d001d0038964009541500d58a554066030f03150100102034020030156002c015043c5040c504210005000d035405500f1424001d003510780a03103095030303540c1900c0d0b03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 65110416 1250 65109166 65109169
    0xf140415030905150108070305060a020f070f0f0c0b040311030102040e2e03080703020d02010e030f0a090504060909020307170a02010806011205070302040612020403050307031b060501030809130b010e 88
    0x410000b0400d4509014048403401181c0c1d108500c0b0340203094540090400500d181003540c01c00d880a0b05244002d030040155031003481101040d06c0000340c02420715030001005107401402903581140040810798041c1d00001c03820388c0b4901900403203015602220344d480c44202003500300d100f24000da0889507145004030302e100c070404c10080d283e00740300540c0d04a400d900c00c0d111840044540d00440b001140010318104155040c0048005001c05000030300400302080c0c8695141c1c050000321103209100800e00641c103034480d8038003100420000d882000740a80b41c1c0303c8076010704900d6070b059000344901c80c400513a9200100821500c661214098038100c00550300449803c44003070051410015070368610781c00f2400503c03d2501405071910011382e11890203a025010540c0c406100140c18410311040022442c08022501056491b2401d50140f0108183c001181035010070081c00c01890701d000807040000200040402c51000c0310543c0d1046528110441514943c1c1d104900160a14042c0b039142d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 65111666 1250 65110416 65110421
    0x8030d0203040804080708031333020102090a080c010e0d0b0a0c0903061d0d050f1822020307080606040518090f010f140a2c0705060a0f14041503 64
    0x810f110348085031815075225042842c0036000d40042d00c0c43d8000003002c074072107007a9007040b100401102403180400007001d04002080191524540c1e41e83c3c11518101501074400c0d07045409000300200514540e5840d110a180d070762060031411408105011500c40f0303180342903a0b180b002550300100208560751924154806490118041014002e51400210014000380141e000540e42c040202c0c10550f010000546002081410001070004c2048452006d2003003204640181040780b40722400300310341902146403d91032160720094240311031442c140d000320f107400540c02030141d541c903e0300503215071080240c075114a01c82c013940320358101c500e00c1105103813407036040d40075010409a404c84011220713980d0a41c1c0c45400d0001030103581d4041e40d107144800380d480503080040c002080050744640851078003007008503500709400442c0c0743c00e0b00304003580800c035003006010081c2805494100b40d1801510035601c444007000441c0c43d2a100f11102804601943d041300c441411003c0c0d4040c00180a800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 65112916 1250 65111666 65111671
    0x9060406110c060301030b040c0b1c020304020d0b010602160e07050418110f040303170f040f0f061a010f0f1409120706110f010c1e020f0d110f010608030d0203 70
    0x200760080a40c0c0380d44942c1c0d0440554001c50040c015850701d441c161518003a9008990400d82d4401010300c500502c4030b004010030710303416024100050380d0b0b444c0e90000600b00e440808004010b408658000f01d00f0303990110341d03054a0b00c081c1000c00c003010b81302c0518104202044070800c00283c0280030401118074034400c00741390005108400070b50004040d0a4001940c45407035451000e21001908004141d48003210341d584130036494027040d45c2d00b0107200c18464000081d0000c4c010482c1404108203000b580c9500040081d8008002c1001c0d20503140400340c00c103041403019000c6200034106107996402000890790a034141da8541c3d0400c00c1c0d1800c00c00301074102c01202c2c1c0d007002d8880e2591400301c90401c0402c000d0b01940e1150081021600700c0c80745440d044494281d41ca9042016800000381c102104507000d140080c600946030720784030812460041007a105481e6881001e0808040b2a007107079007a902c04412209035901002c202c0425402c2c1c9400e40704500c8694410081000350340740380e40c007958 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 65114166 1250 65112916 65112947
    0xa110d09031b210206011404020705031210050f060310180f0e010209030d2606040f05070c030e0a081203060409080c01020301050913030e09060604172109060406 71
    0x5148000140d181200c52801e0b04540e419050340c195240e2110b03040f45240510140d10003400190b042c44881c8180d00c50101c400747c02260041040c0041001c140b0680d00702105105a96043e46882550703840c07804000d10841d4000e41c0c4802120419017820800c5071b01c00d40611151030f500900d4601c0ca5002c10314201c0509100f03550714440314032640041d0203038108142c1c00c600056200c20741c500c205410884806840001e10240000c098298890100904e1641030510710480305691040c01003000340c500f801c5603c20b8245498100008603800c0900c01e042d150180d138803140300c051080c0503c0501111406100d096070302c070180c04050350380080c0c025944500040d00110f031000c41a80c501d000360300f0500300040c069401200520040c10714444044e4800303902c4c2054803030003841c4d441c068401404401644d02545082c4009917103a141c8004580003000501d5906050250142c80c0b03584610409100540c40103021a207124410f0104050f0f0300c040340c00420251030580341c510181c071702180d450444c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 65115416 1250 65114166 65114177
    0xc0f0501061203030f061415090d02090a02071202061e06030a0804031202010e0a0b070507020f090a020a18051c17040902030601020c09042d02040c0c02090a110d0903 73
    0x4200c881042225122035880380c0c40105d04040b184d5180b03420740340c00c0d400186c030801c00004804059034400306045012041d80002c01d6a6035040000301c0e1980101160107908034903040244160200c2903801000090b0084c0b41c10341880c5840c84003281c40798000c3c0c4404100042c056008010300d02419039043e0040300040885001d07904c182d8441e041c0e60015070003a52051107200c1d02490a940a016484103000d0a1020300401360166943d00e18500000c2c0449040050110305a03085403502942420314100c01403600c0d15a14041c15404084d503c40d5907010000740f0600c0340b2131044031034480150b00362840105190507201c5207080009a000301083e0a80c0c580e450700d01e80e00103440c4801d006001402c444803000d681c038035005d00064a0080c4000000d4021406401000041105142002c031240d07603002401c00c0c10594200c01c4800c0e001c00c101c000e540a86040c10301c00101d604007061981c0d00b4400e03a2444081d03a9005180d10480c4c0000c0c1d000d03056204208480192001ca66012500b8644030342480c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 65116666 1250 65115416 65115419
    0x90d0609060506150903060106110c03010e0f0d03060305030708090d0c060801030309060206040510020a02161409090d08070c02060c1902010305180a0f0f051203010e0a0203070c0f050106 82
    0x1180252100c0c500d00751401582d45050003d603040c0406800c0f10342c1c503216100f6182c000c120000c00d03500c0205126800400c8002c3d121180d00003018810041c0c400e00080081c002d14014400c0151101c400441e00400e900c5240b9203906890300a0181c4400c494102c0040c42c00c2400648030350300a0b0b80440040c50b840580046000001001006031501070801ca6a80c880c1a43c198640605200210b81000e815903004804110000300c00080e001080b4801941c0581c45000b80c00c4164a440b4101054030342040309030390049000c468081207220001c6080b070300241aa11038291090b2604a100748071000150b95000003100c40e4018000341007500c1c4050002d03883c1c028121501070800b0041c131880d55031b4120b2015660195030b8180603554200c0348141c41440f05415142c0310a55404000000510f02e244c60340041c07007400441c0309103038030f001e1304481503036141890a0a0816103a00034010344d502e5007103c601142202d0498400c3d03c1c407512480d112582981c2c16a21900c866000d000d00c125440d640310ae00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 65117916 1250 65116666 65116673
    0x1a0a0302090a0f0504061a070215040803040603020909070c03021504020f0a031110050415080915010f031202030711010e030f0f010b1305090d120608030403031d0d020f0402090d 78
    0x150b40d002864103c580d4440d190402003048140ca40c16400441500c404451402c40c406440c1c0c12114003c0d412a80c030381111525568212190040340e121017211f0002080000344190550000c141c0c0103000c0391148002e648107501503030074032883c400140050348000ea440300071101d500c54054125000405190000000c0b0002a41807400c54208550100c0304c032880390010700301101141807075125400e01e136090a0a1034241800c19120365260001c011030301c40400d00e00c807814091040c210710101190403a070f40e110b00c4042c5100f5260b120441e42070b1428403400107001e00c044252070045030301400d1030107485601401100c013001035901046d49405403210000c4444010060034035002c0c1c0e100d00210b04c46200c1802c110708510075600c140000c0381080108285042c1c003248590240f0500d08000d02d03021602c0890100601c01500003070814480004c5c04000c1c140c0250098210160203c00101c2d05007a030428030400840c107007c005d400c100c2041d02100340386000c0c1c014114205001d0481c10640c0c0d00f030746 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 65119166 1250 65117916 65117929
    0x60f0302040f0909060c0e060306010c020d02030f06012d12050312040620090604090903051605060105090711060403030b0f0409080408010507050403081c0e060910151a0a030209 78
    0x80c07143c0d010395510b0690340c0400c98036000d4500141001d09100c460440600302040540c03100510382e90410044240e414119694000904401600030f01101c14040808020b182e882e0320078021802ea00100b1012000481074400000b03c0001640007403140c0d030b5282540c101c40510030143c0807a03590005020902006100a640d10300ca50301512001c104910f4000c240d10f8102c2860002c5a0104230400428116440d541d00b202c088441300d43d40040d411816050450350740c01000c1c10600400c01810152082c030000040040c180d030011103000d960313511102c10581c4c88030a10b00002805070424800a1301007030107584210900d1102038042c10b0710380301000c00a0102e405101d400c0b64032020128091018603001d00c2415880320079070138218501811521010200e019601c61000041c106000b42d020401060b080b19940b129800202c5d841d40c18202d1070151140404c03020a07404602d4024000b00c4d52040ca000f8004031042c140407212030420110a0100c107905c4241c0072024950200300c800402e4503600d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 65120416 1250 65119166 65119169
    0x1c09060f120c170703060506041503020c0703052103070e09060a0f060320030601170a020706050c07060c080c120c0412051011072a0b0c0a020a05090702030301060f0302040f 76
    0x40e5120140740700e01e10b03c1d0840c6844090544010946040310070301c11515060200c1d070036103041c9042c400d05444090001c0340648140d0340f5108290040316400001c03c40000707145040b4914207003040c40325517109503021180d0301046803048005445082c00f0481400e00110035a0009000740c40c07080f80781c3d100d48500e00101c0c25540002c0000390307520044108490880030040d02001c1c0303140000d01e103090200000b0134a0078100d000d0328a1540f49000726145000d01d80c12110b5240e40a02d05008030702c1c09440e903994130340094100b9502541000c0310a0041132050719080d03c1600c4006001d41030003603204141c1003800c001080b80710804410080840d84a07820110f019049201d080103114800f50083c003002600c01c440031400003980140410800203400c0d0945140303101078061103901c98011398944651514442d4480700c40c2c0440018403250114022945412050080c1d440600315a520428001650070489006005800038401030020303c0c811407504132242d041d480e001d418903841c2d512805003421103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 65121666 1250 65120416 65120441
    0x5010602070e100312050a0c06090803010501030f050424060302030111041a030c0a050c030d0f051f080316050a08040b04060908030705121c061203021c09060f12 71
    0x74041c20000c50100b1640c0c55800419842c50660302842c503600e075107142c0500b080764414000c001c60703903d000c1886504c80d04142e6800610a1191040c1030516501547c020f016890000342009190729281c0900c0c0280b1340540c1d030280c0241482148503100000407040b0b0001e5a0f401520b40600001582d824050900d0f411300300d90340071f90b40b20b1030300c00c0381001d480c0e5505107243c0408060080021040c01c010566034800c181d0304240355171f450385000e4503040d0300c01c0d81000b1042a18060f2b142c5005280c039030102d841210281001d0020000154080035030b25030512504105a208005030b422095080310301d281600d100d401103030320300106035450b1002900f241c0c110302d0322914042400c0040317640c000c0a1030024100500910701e08a625240e003500c580c1c54005032116428001041c0403088203060038002101006001080099110040910407513005941035005200c3e804070542461869248000c40014946800320540e2600100351050300184e0209030a11202e4440001014964014602c40610 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 65122916 1250 65121666 65121673
    0x60f13050a08190207030b2d1812040e0402040908041505070c091109151b01090501060e0112060c05090603070e010f0519051312080703030b010e0a0302210105010602 73
    0x43c8041003410340307a184071440210f60050a0410204280150b419001541e040c02c9540300f2175160f005642d58240e800b1164001300ba100c0c00c1140c0d211404641c216802010340a81d10411608034489000c1d0245000c4c55581305a12002b180c018541070340030409091142d0052424103075078003a0300d6107824410f4500c0b8045940040d8110402015441200207440e05080030000680e4015003203269001d4250315a006840e401c0a12410320301c1034090320034451034041040f08207610b01c0181c074040c080e034890840d4150b00303058012403140f41c0e03c01654140d85540b244840141800c0d12640041c00c4402250300910900f00705a8a6603221070000b1481134445840c0d0b854996401e4000510740c5002e81900407c024040c4003814060b60562040c5415030003600c3d0981d04c58001900010a00d119640006003445070130b41d1a8007000500c0c0050501d29000385c0b410040112a140191820f848207050b065004c0f00c1410184018981022800312246194121200c5050079038001400c50b0002e07000b150140c2d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 65124166 1250 65122916 65122927
    0x7270c020a1103011401030b0603070911120a021602060a03060302090a02031806040b1f0506070302010e120405010905150d0905010608010c0302090f0103051905010605131502060f13050a08 83
    0x41c0c4003600b10000140d000300b0030086081d031310207405070341808010009032400c2c0c0170443c10799041202c20003908607100100031a9803040c80e000041e500c029069103000d204140010040301607072007607600c1c2a940e100301175500000b41d8204807a990200010905050707403050f005c8007680b030f04c4d0070702481004101c60041e500d050604103559844c8500340f0a0016a010108010002ea28030314a41d4102c81c04601c003daa58010ba41d0506200c059a0080d07a006800407420f03009056054010454520034041510000c12000c281e8000600c201d00dd4680425103405041203282401080c00b80c201c032009807200d007050305000182043d60319610b0252510382d1614020b02107208207200790240219941800c51502007584041100000d81080c568103065403600060203420b08040241d640070580403040180b503844910180c0103402c14101d01040703100000d0086a281a05280303000d20711a00d40007451141d4602000240e00c2d2402054805d80c232152100100024808202c07429010744158003441c1c846 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 65125416 1250 65124166 65124173
    0x40608041a04051e070b0f030f0708040f0b0c0d02070606090e0a0b0c0901020705100c0b1b03041403040816050f06130308030901090f0b0402101107270c020a 69
    0x40c0301c41801a00c81030061410300c00041c40024080c07649000b18040300c100040300396252820205a6400211203c0000602c060498600402140320b540c8400d40c14a03a0f480d51603049640800894005001c2c2d010b88045202056650403001d80c000c00d840c1c0c580740390503120518101030341c202c21001c5601c40c0c1c46207814009090680220341c000140140140103507641c1e602c48094080002d880200c00c1813000518a0803a4030030f102520150402a101c416002041d503801050900c0e41e1a0540b50412000c0c003203070740f100c2080804040710800030202825500d89440e2140940c0301404801d1a5200030000001c5102081c4024141c0740044440d050125141006000403030034031815251041c5c0081001507905510405007900b502d40102200b0345a40d22081d005006200000024045403101c01520041010101c3c82500c510b01c241e6080d007040d11000c5065808943d03007104846584c006c1e00040c0030402455680d180307100030000952034109924000c080817100760100071001a00424180703001d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 65126666 1250 65125416 65125433
    0x30601060201020f07030509060702092505040605070201120b0306010b040305060108030301030305072d0c150305091c020312070e0a080705060a08060402120106020609010e010506031902010c060204060804 90
    0x101401e000a501c0c013001d980021009100e039520007800d014020030f0042c000c0d211f52054803030542e80540720705450308017031641c22003140a008658204d540d0100c0b095485038030801c00c0e81c04070b54807921224100136141d80151801004400b910090039514a400d480565080001034000e001e54045941d84a0440c10b150381401016000107000364010001000000d5102c2c089076807441d001640d00c5040c04048083d03031a0540880d481d0103000c0403002404091140d0f05002c0d204455482110302d03141504c402c400c0d016100308a81480898009400d0207911002d0448541a04445481500c1c40c04064240d01003240c401922908001800321425179000d0414401041c0074042500042c00c1640c6000300052007032003051b811204000090010650a03195901604c01d4004c600c1403904c1c1940c0c5414009650f41422902003510358200301900640da64188229401204054041d004900d2240c082101080d180c9400324100304c010300c00741020420383d00c0035201400556603000c0d054203003803e00e800c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 65127916 1250 65126666 65126669
    0xe040b04140406200301030c060e09130b070c0204020c1617060c0d020f0c010e07090e030723030304030201050415111914070c090f091203050c09040e03030402030601 73
    0xe41c6494440602900a440202e510a80c844004245594145401030419842e0300031400340c00404400070082025007620a81a94104c0c1d0b80d5100d010a05002c0025208051b552a13011840b440d00e6040414040700350540e204103582802c1c030b10044a640410102e0740b00241c084069003000c1e0181c41402d0400c80008010f00b034540c0c860f0003280c00440c10f80e480c0c0320058000d0f9808140019a03c001c050550182c40020140f0b126043c0c0310140d09604602915003801e000c0568001d0390790108901c0303c00e100e40300c4001b0700340e00107500b401c1c1181c0e6480000c13500d8151503c1c0340e00d0680c09503a04000c0400046202d903209500100311400c2600d003c50541d0307000071b413001400e800d190f03c0401082c5148103a1b041c6a00100c20004020815103003070f683c00710f00007681d51444000240700414402241e41031030403105480341c2008003c205200c40701c2207500403000101442c407581d00f00366005210b60406600005801c1c074540c90060400f001074101ca900d9240504984c00101c104400d51405100060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 65129166 1250 65127916 65127919
    0x6150506070201120209010e0a060c1101020f0307020d020f060c0f0c0603190504110406080c0f03070e01030803040311010f090201020610060801120f060501141906020a0602030606090a060e040b 85
    0x38200709050780060800b80003c0004c1442d5030740810000394982c07052600303086040000c3d1101d607010f41c4540008107000e01011301502d40a1910840b0f600551000070b10340540e90110f0040c0d0304001866003045217184805000f80d900c014030310008401036540000030185010080014130036900c0c610100d6050582c84000d241c4510700c1442080466100d8003104440641c2d6294000f03016900da01c1d040c141c08869950103074002c0e10f411804270303030718400180d52070542d07004451851019681600b00f5a032865280108025a6110401040001e180b80f015540082c0b20707003030000342c0801101007142100c400f921070f0903000362103031001410355805103c43d5412544600420325403134100b00700900509030601c114040100c111001100380402000f8a4840d2948000207005559542810320600c0c520702203050302c02c0c45440200e00100c0c030b8403415401240c0c203e4014101100507603c41d00003d4100400054001000304980000d075598204998040d0490741c90b102100a01c074000d10007214241202c09 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 65130416 1250 65129166 65129179
    0x10060302011b061404050f1b0d12021906020301061706030d050f0c0f0a0c0501021f0c09030506090d080603010908030a05040602040509010b1c05160e010318061505 72
    0x1440940d900400200c1140c0b000782c280c1c8220703110352400b1802080c09401400003543c451080c801000b001045540b00d00d01020300300e40f0240180784410805c804045c034155441417001407081c0004400c070440c80b0401d1400c1c0150342000004500c0202400034401086501c0c0b03a00000500030103820002144d09045145607080c402d140c00c0e400f1aa0350b001d00200001400707804108005201014002c032480482e61600b50b60108080d10442d66079041d5103034003181c00400008001c00c141d440000d09807450f0500345405248001900300040041a01c0c2210b074007004140c0d03a0200118034108a42c1e40600101001410328041034a40244041c03c041c0203944240d061030741d43c2c0e01244002c001da0382c000421500004140e00c951030801c0080c42564403964001c0030401c000581c503030254010300181604004140317450900c035020030b030403103c04a40c00c08003090009203855840d4491520103254000c181000604250420b0130300940004a5504440322911000315501c40b88030032126600500c4161900c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 65131666 1250 65130416 65130419
    0x5070c03020a060515120f100e030301090e070e01060806090702010b03071a0904060303090e0c0909130c080601090b01120908030705071b03030503161d040f0209211006 74
    0x79110014408040d108607154804122402444d100c174402202008050400c00421990000c0c0ca0f150503000c00491405041d290b110b40103101c0c054400305a00390b1020354950380c20034040200604107040240540d100750903020803030006c41b015071400390080761204421450000100004a10700800c500116414031401e0a15910300003000c2058a0701440840c0910300c009921841da07000300d8007130940c8182403c0c1e0001c1410b41046001c0152001d1111000460f62000d184082d1446004a084d0300b1442c2440041c4e8021000303040000c415100300c0c03d040850395503000d800c1c42c00c1000c4e00043c0b8060394035000d146407903170040e510705038160f000c0205011818107074a8060281c040100f081090020008000f0204a070700c3c10660f0b41c054406a00701503003038172400c004080f60070840e00c1400f035441d0004015004c40c080c8001092241c1c402c282e03204403100000a00010780010980700c04095003d100121403a56020a08100a400d00142c0031587c03685200742841d290035040003504079460501e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 65132916 1250 65131666 65131673
    0x19090509180d230d05010312050c07030b1302040501170d02010e10020304020102120a050403030306050603040f020f03330f1504090807060c09050301060603060e04140c030a030507030305070c 84
    0x500b10074204560408540c81c03200301c200300e814400c08481d580441900000c88003d07203034140c0d10181c180c070b000708660040c10740038180503160f5104d9090184107130340c0f0428007000028200c07681c4d07950204a107455014a59015404501610005c0c3c00110601d20340305111042e446040001a141c00404d01c02480303181440003a0b2074903920700c0388006403100d800000081c10f590081003010070351543c0c0d059059542c007109000614980142c00103d0010b0304100c1c0010300c3d450294143d030301954210a10701c0c00300c01c840c2c1c20415024040402e13160180207001161040201c0c804154860003010001000a0840e139080d090040000800b540154a03a03402846074110964241c01c028401c107031000038800e2028280303200d4a003c0e20100400550500999002c01c0f540b055600b001c03114150002e2050310f484403000d5080c0e9900b405901c0c07000c01e441e0001404509130b01080300f00c8000c0d0000f43e07402181c0381c41c080303070400e094200c050700496400541c500401d6030600c01c1c107074002905e24058994450b60794 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 65134166 1250 65132916 65132923
    0x1090506241c0b01030309050a0b12070c030e060c1b03070806040308100b0d020904060509060303070201050f07021f020f0106030f0213110d14060303040317030a021909050918 77
    0x305a402940c2da948800a040d1002c84203041403600012103009540c0c0d2441c0c028400f03980d5010f21802191812400503019448500303440802001c20207924103540c40e0402201c0c10b084030001a810030080c101c0c14191902c070800181084001d103005060301621107400804400308404030a80664001e9004000300c19001c284660004d0b0b1500d802c48040c0c0f120400c01440c0400740e001410802c4000803264041d41d01940180f41c6a24182c0b400d020075a030300c600308149503d0031142c0d6509500100f16610056128500400c07001caa014849410010075401188006c030384080310503400c03241c0088004030183c041200f036150200400c000e100725030860751080d460760740c80d007002402002100c1d00d00c0b004024a0b0064045040016149500c4500c0e1845581c00b80440222031801c0c0f00c0c40102080203401e0110423981947d401440540c941305d0380c1e943c00f480f00e50000781241d10140d4244850441445e00d41010401d80d030391b079910b401c1c2850821081100c403000162811130488019100c1c2c40b031000011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 65135416 1250 65134166 65134231
    0x1704080f1b0601090c022401180f110702011202090a180f1b2615180403080f060d030c080c0a210908060c0f070f0605040501090506 58
    0x34042507444102040010400e40c08406044055018620001c55508543d0b1701c0b058144a079a82120803000d002860ba03418070740301822004500b440400140441e02040402080402104000041c1c01440001a2084032001041c444882d5000150344040d0740c0c0c040741781548214625030852502c1d0b405d20024048081e68403803201d401e00241919456040030f640301d031030601443c120500200791a610108480221200e1420100d6080034400700841e15541c0e010002c10400512008a0703124404102e00c030316814104103034001110460ba514003c0240c201d1340c0164401d49810b6254101704203034070400d0344000c0080303011b0390600c180c2302d02007030b8071494065000e504414860381c1c8501d07040d83e040c141881100302824041c55207030010392a8004100c1001c1f481110303507030140015152240140c07100401e0303070100211542484940782920b4000010280280b04144410480760303107a8441d400e5680848042c0c03811395448000105125003408000d81c024024480491000d410035210b040700c0001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 65136666 1250 65135416 65135437
    0x10e12160201121d0c01021002090d080904110a0c11060a0e12030c010911030705010806150a050415020f0705090618090111030f010f0e070906080619080d170408 71
    0x4803600b5000d40c0560354440030b0703004d030320700c9a500c03d0703e140e08010750340e0703a021191041c011710501c00000c45804041c400d844030301d00d00900c45040164586c079081c40d00c1c2c0000641980c056074590300c15410130079040c000c2042ca5002d88400840801ca414040d02c114201d000490103428200464800701c0d0340001c01c061100801c9901144083d0b0b502c20542ca1805200c004898a41ca0030f5560002c2c0a210044083c9040c8210225040d40d0349805c0111120f007010b8070a503030802c01d060710b5202d00d14603400107080e100140c8d140c401c2c00c0aa80b01030704d6884a074840d400c900960000c200b910610581404200d015010a54082c0f401e401c000740400c1c840343e0205054200020b040b000300381c0c0d0110070f400080c1c2c160307016a1090f440342440781c500c1d44603040038403400d211661014000038100d099030481d07074840c0303400341c0700e81d0540c500d0703c070302500c0c85031005110b564415117203410310400ca900c03101544040d0160304000c00b813502c081080036101020012003034075000900c1040000240c01c510498841c1e502 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 65137916 1250 65136666 65136677
    0x6041a011d06120c0306010602010207060e01060506040b0a050c1615090612020c01092a06090b0708030405010b300a020f040e07091b0e060a0806040c020a0206030405010e12160201 79
    0x59803c05401e000c0050000c9a05024580000414907415000b4000090160744100054901c004c41c8600700c558910030340790025014002000001c506034080c000104032421300074a000441c9a141e4249400079045200800130104144914100d51000540014181c1046450941008009460718040004140c11240c000508420307c610079002818a00c1d44985154164581c0c038075807001401d07800856908002d1404da0004010b03101e940d00c4000c40e495100f42500c0d10002e03031180240d41d07000900c1609c00e5034854101440030707240c60b140422a0489400c0d4a50003409500c40f01156200c64001c801150b4031012104002d030f52101144414001c044a00052150002c0c00050038400c455000f410f0032413400c0d9108401c030142031500c0c1c1d11007a03203030340340e00d0700420707131f20801645014552142d0000340d00700e4001031240c01d0551029501c0b41450040324803102c91540000c4813603004460845450f5140e0302040c551070010041049940030580d030f01418600c1e82c5c0f0001c4078880d080c11000e410001b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 65139166 1250 65137916 65137939
    0x20306220f0e010b10080f0705030c0702030f0f010c0905060d240602030903010b0a0326042d06091d1315090b06010504120605041406041a011d06 64
    0x15055100781d00905280c1810710070b07031000c002d14038000d03c00c0e0b00803140150303030004d00094843c2c4210403291040b541c2084108454485400c100c40f00c1d000105401d290742d000300081c10242c1e41c1000361000b024080c10050038080d04072480c440c20340b0f65003113000003845500e1005000e20b41c3ca403c10742b424407040000c000b031514190038101456040540300c45500c0490501c1c00300780c09901000900b10000d09800a1144503e0303d800e2081130962440003420800d02411500103900740c040c0724900c035202001304281402c0d2a41c20240c0e180102c0e40c0c503003020102005410036440c60300c0180000510660600002d001c0c0380c001520403101c61007200515129216000540030000d00d0b0340304412541010341b01300d0a5031580901c3c070041920080c03c0d11101006000070b03503d58410000c4a040e50000070721103914a100b80d40701d8000d400040c0088443c2460702c20414500704040001078480e42c020703209004400d02e4020038001c0400e040c0c000801c80200c02e4030180d51840941081e81e0440404d170740088403007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 65140416 1250 65139166 65139229
    0xc06090f060504030225140103090204090506010f030203010506090c0f0a030603080d0f0b19060e06040b03100608090303040c060c1104091416050a030807031403010306050118020306 80
    0x101100100500c4140b605060000f0f0690020340741e000103c1854000d05a40034030080d00c0d81101c814424a007111404034501d1416510a27003003824030742d20141001c00c1c04102a5036040c00c0541c2600540605011070300b08000b507160074000c00d9001076003a00d10610900b014108160f0350300c0342144d00010142d00103a043c6500d486a40f1a60003580c224021949440110488030047c1400700040c9074001e0400107040c076146401e03403003140003048030103401c4030191030410140c5002c000c0c0300300382d540310000780000a907410700300008500c900095203d0704d000b54240394000d40f2a503c00341400206500c140104400a080e28500310207444032810034060300051403030022207451200000c0c41e0441d00b07200b4408100440b40b0122941880960b080e12100c0420703802400005000c2e12580380c3c080043c0c901040481e070064024100303640603143c0003081110710707004e904199200703a00031511280d0340c000402400451600818584050401c29495420400c000030204550090111900d128610201908 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 65141666 1250 65140416 65140433
    0xf1c0503040b0a091b14010305090c010804260415080c040b07021c0501020c0a0c050f010212030714070b15010503040506070305060102030c010e16050102060108071206020f03090610090605010c0609 87
    0x850583c603c0c0b04a41c140c030f030040c1d00c1001340701441071b40c0868100004590345903000701d05e440c1d5010040e905c8080b81c1c0d9130350b210307440c0f5001d1008403030703681c65442e0130004c0d1040da102c0c000f00094403050a8540d81031000755002004440000c4c011005004140f00074801c55070140c04130750b08290101c400c407410100f4210184d40941f0905801400340d0302c000b42034a03100c94080b4041307040c0c60040764041c2d0055907507018480444902e5002c14010380000b42440c2d00d609040000d541c000c0c42c50325101c0070b64800505856501d034000141601e804c9200c10401c41c00b014026084c01c1c1842c428078080c1d0450900c3d0791599079401028001d80c0a054590380040d0a6034070070419240030b0040d0100a001d500380302c000107500ca000900344102c5021a69402046550001036224120340e110002041d00502d45100e252312004802c0d0b04030785d469020000b041c5d01c14400c1c40958054901c0034082d0800342000e00c0c8a081c0d52a1036840b01da16942040400c100c82c0c1e8100b000100b00a4106901003211220340c0b41c04201d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 65142916 1250 65141666 65141693
    0x2100e031c170a0e121804051008190606060906050d0b0d290a0504021008100302060307030b0102010b010903020f01030f020c16060807031b0c060e0f1c0503040b0a09 73
    0x52203a5102c0c1084031040040e0002e00340305003540305440780020101c0c9060224031403210412a40030201100341070900349a0310a0394400b0240f00c2c522207442c2c441084a041518030f0319007001b0003564185031818401c0034403a21000708614108868a185001c02c00b0f4224041c0b00e0381c1160742d59480840e00d400b0703100c054900c0003140d413141c0714400c01500b01c501c400d4580d610260380c00e00b02c070754880060f801c4602841818007464008101c580c030320a508600b12011100207090195011421100000588500b40a94080e5507262408075910b84100002030031100c01c40009130400807050810000758603985514416884286000b0958200d404468006441402c282d044248100d160046060b1003040602d001e44610769101704254840c028202d0960740e000c004440401d4040720320443c40d030b004003072070001d0360300c18140410b01c1c00106016500306881148044500d0b001100c0303005030090894044030009403241009030541c1400c2d142d070a2410002040d82c00150360b01c448010a01002802104 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 65144166 1250 65142916 65142947
    0x21309050a0807081902070609050f060313030c050d090611031e03060f0d1202061e010b0306010c0503031e0105040c050306040f11040315050a09030203090906010e0a080a02100e031c 80
    0x240c0090300241e0082d960305441c0301f230324001004241e012440380380600c80d892007110f00501090540d181c44120850040e1756040803000c0c45034031501000000d400b40301140070b0724483d40303600c0f003030078609403002d4420081c0b5a80d0704840d410410100a828051030040742020423005441500d0f66071740008a000700184160b040d5100800c1c280b039104100c43e11a842d1380e41d034529402d50f600c031b480d46035030103804210301d1204200c0c40d01840c0046c028000b400014591118052400b05039039252500c0d003904543c4248d070010266008a0032050301054402c5281c1e0061000740e40c200803112100c48020060302000c0c086600c200d8607524112607103070064004403211808425140e40d0f0310b9892071304a00441c00510380101003403c18000035031a1780988915664290141c002d11b180281c81009c101c01101d00402c014144031110446640d5900ca11040c4400b03000040020316810a413401000300c60300200c81c030401080440249500d054801080314200600b0408544040b540e500e0421348100328008080d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 65145416 1250 65144166 65144197
    0x30d11061503013309050103050706050c010f0501083004032009090f0c030a0b0109051b043c05060a02010906020a09050f01020d0503071107120b04021309050a080708 73
    0x1080b00b6000d01d584980e40d0313004000100c0300d665180c000318292402440302803d40c6e0482c58042000c14000c0b002400328044000000070321000d0050f414085820a811226850b0311414112444e20f400a00c2e0b01c0421500a05a910510001d104100c1d144a02c1c0001000805816400743c446020380310f04600c188001008601070b03240c9a9869030780c030a510780c1203120347e11030f01c05844020300780030682000454102d007180360b10340e00f88101c09002e8240542000f5610090101c6041032246950182000d00038490001d0300c0510400b84101d624200500b040194040171022404005020b42c8848200c503030a58800b900c03090f1841042c3e00410002401810a600014000118035406408001942e00407150b1000c0c480b010070049030b540b03014425003c0858010130102e082c15004510f034603440d9101c4011104007a40b50841c0d2492880c039010200d4030100d100080c030003103140204401c01201c3d502d2208019000c8180c50f0f41e07589600000016202110004060091000540446001841c0151031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 65146666 1250 65145416 65145461
    0x90f02070302060112031d0607050a08130504060e0a0e0f011b0f0f0206060f060d14010302090c190c060219080a05070509150a02011e02040302030d1106150301 70
    0x50010354011241280107008080c004100d0840100440c16120342561f100040c40c1c203200d0384200f0030130541c01c6843e4410380a00c5280001802041424400c9110b1220103441e6141b80c020030410f00788076004140705500380b103010700c402500204a141d0000c0381e510041502c264a00c201420198a001d1045695003810900a026450141c10340082e41482d941c501054007001d0b42103516a40c1400c43c400140c2049021503501c0c90f01c00d180c441024402881ca034607080b40700c0c200e00f0488045d80c449179400400e0074010010740c1380c801081d65000e40e110410615240010500c0300070364885c09407035000e011650400c0002d212543e81614840c80d40b00f0a0f0812503200f1038400f50800b8011561151041c0c00e040c0000c3d585032050b0700707aa452503030280500480080700c910b024056000080d001d011907580310b032480c94804002a5034411054100001030b615402c50050606001949003000180010020301c0f12035140e0005560f0761010105892040300a06000001d002d0a0360341108102500f51440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 65147916 1250 65146666 65146691
    0x1b0d080c010c09060f0c0f05120d0f06060c0209070807050d02030406020d110c0a020d021f0507060b04150303050d1b030b030601080c0a050909010f020426120415020709 74
    0x401925032a068490745a901c3c4c1c1c485048880840071200310300010314040004001900c40b5011404040c40740c0c050b0392140a41009102460300614182c500c001d46400d09480c2041461260601510591515410324105074000c1035481c1e2010349050304114900c8001680c242c49102912550031440d041035540c0e00b0241043c0300030350810303103041540c00d00c2d001001450180700000c96682c03d0f50740002e080c449450360200002c4061070101681c1014042c0110712120030444a440001c0d2555100c058a80c100ca00706002118121200c0500803454152722a08030280c0c1582582140c0e450718282e680e48500201c03080150405810b40e00e154000255140c03030007078043e040681e80301002e0b800c8642e0343e80d0756481c1c1e03980c2d088a20b607000e40010700358400f0b02860415800c0e0641c06084000041950590541e0840403a8080e0340800043e02440c0d1650b03444220400380024034507003080090001c02c0c40c513608031065225501c40c1e4141c0d2441e107600f8404e00f500900c8840300420014000f08440004500e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 65149166 1250 65147916 65147921
    0x30603050d030b03120c0a080a170f01031707080d060b030a15050d080901021c050d060e0f1501090803160c0608040b071209120c030809010e1b0d080c01 67
    0x46030a0301400c007031541820310a119100703103038900500901c000c2c003040c8081e0075568030400e88a03006004080200c80803a0240d0014051201c0030b0380c0d040c5040f408601c2030244584098400014400b041004001149610b0f800815580380e24011a42c1e6490703514007244a0320850200011860910000007486c0301608080c41c0300e140304007018806017824406103440c600c121300403036900c43d414269010200310701d00054038104c1c6041c0100e44165000e410015402134010110000045d000a00703c3d2400b062405448010005000480b245003850703132405100368001000c9103400e076062584a459170f0310801030700b4000d0442c0d009076540c1d03200504c500709030010f00b00d01c20342d030302000f409000410f544601d02852040d90800070003c4c079030b00c0c3d499048610400d0301c5c2d81200b5a0303440b0144600070444805e4400d21411054640802c010180d00e0042c0c00c9000050000145034900f4107403680010010074545440308a80c55800049480b000000d061035180e250090010800820b40000391901503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 65150416 1250 65149166 65149169
    0x70f06060608070c020109030602030c13090f14012402030d060602011a0910030303090623040203010e0106080a1712010f060e030105060112020306030a060c0c0b090f030a0f03060906060306 83
    0x3541ca07698143e0b5180b000b40c90100303240300024005164840f0400100300650f001d1500204811541d45c40d0400e0119401541801600110500d6a03122210800301c202031003052030301041c002d812091585860b000071035550200d80d2401e100300c80c047e000e040c55442401200d51540b44c4034400c00c002c50700d07044002d000309552411921034001c0074000b07507040d1402c42034903032003242c0040086142d1811603404401a0070310340320407103170140c40b0684242e14841c0c4d40180103c2c244402981f00e000d2825004241c00d513210311307800000d16450300c0b030181b01c0f440d03010480010310307900242c2c04c50780e1800b030116003d42c600c140c2c02504404250700c0008100c4551030305010741140d1595587c1d602d040c1c01201050300300d42d0140c50b103601040001c000c80050119030b4014550021008094030b00b110201d44441c0d040e80c08040000001604040c820310400440b4145250000219001050043c04d0040002d0b6203200d00d103030450a00c41260040c1c000d07144280c101c40041c0600030420b101a40d6126009009010103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 65151666 1250 65150416 65150429
    0x1806030b07030f271a0103051207030504080105010e0403170c03070e030705090c031e150d030e0409030e10110d03021605070803070c080309010212030901020412050606010908160501030b06070f0606 87
    0x12005d88021003c0c40881e418180d0740c001024003c0440180340c8001150302a40d8200c080c00b02c188030014000c1401e1003118002c21050700000f9203498146002400900203100b08019000000140083d2030800001e4a43c40381c154104007075140801400280741c50440d900190340b1880000c00c12413000100d00240d07000e5160f6a060038000c1107100c042001c0c07080221501e4901c1c2810401d4440c0c44e1500e5036104684c0e50007801c01d00c12415201c0045820303610107480c00d40c0071034043c010000c41030500030140c02e0000120f182a40000c80d0f444045c80c1c6500d0014403c100701174000c07900e0300c000990040c3c180ca1856100c1c0031a044103587e51103c580341c1d048800709503a244c06020000503244808411180c940c6416409000e0000810700203400d00d070409440c0711001d40d400d00000c0341200f114807004400c0c90007040200300707d150070300004101c40e0080d00305404d16000788032403a04203080c1003200310543c0c2090a000c0b0b10810038401158050103903000252244540503066414400b0b01d51109081e98003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 65152916 1250 65151666 65151683
    0x10902040b01020703170307050d0c0306031e03050f2203110a0608010b03040b09010e1b030601090605010504140d080304030e0411030903040902130302060f03011806030b07030f27 79
    0x800341c1c01aa12034002c2d10003d00003240c0030948110a101c000011035012840d400d069051040f03c4181c001281d220383c02000201e030340c80105000f80110100306c0e1030000303030301842089022502d5030000d01a0080c45015441c5a002041d0b0100d50488415421240316483c016442c6866480c18085c0304824a001014001c40c908400890100d100e00f1a40d81030b244120b1607107245890300c0d40ca40b06401c000801800055588103001c04c015041402001c10f0070014541904100802008150030300da030683c41003d2a0703107420f030b0030051b80e43c02c401514201c801000503043d545074a01c01140d0040090b901c010f040420020030030041640040c82e41080c1c01d0291001c0003040c6903480e42c050079101c00e8132880c200f640144400c2090f106030382c00411100e600e001c6486c1c1c02c142c0e40d50205509400c071000180d07141d84084018001e003c69032024003901c420100e018404030349151200481f0100c058881400c064440c0c2e44000d80f260941c212500c1800a1040d4148a005195645031116174036a011911100c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 65154166 1250 65152916 65152931
    0xc021204150518191403120a120f24090204060f0c0503040f030b090d020c031b0411030907031406060105090d06021303060b1206090d0e1206040302030909090a05071a070204020c01090204 82
    0x2d0000d410100d1f00901803070325240ca101908113580b00300d030081300303043c034187c80391030244c2003101a000d04600b000e5000d41d21051842c00411985980748150000d0a1661052208120150340141d001e00031010314100052166001d04080f820f62090f50412051141006400010132015644a40c030a140741c0b42a00e0b6901c100010403a10b52140482d000d5040c0d001040342c0c0e03880611209203100001e002080001c000400c0f2659a40ca034204031740d5401103801c0060308000744010306581c000e0120608002d070009150000028005d4068040002d0181d0721161600e800c0041703507411640714000003160712020907a68074186000d0402800d415005518182c0984000c80c00000d2050180040320060030818240d50411034120f801c230000e4a41c840e40d94070840301002000d0107482c2c05a4083d40c0035503a5100c004042c404d502c240a0a4140c0c140e00141d8040d020a101094101c10f0710301500e043c8000fa140c5000c80c1e107440c020703140c019501c94130001c0c1c2c1c07280815056014000030b501c20f86041c003560 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 65155416 1250 65154166 65154169
    0x60708040b0a1d0a050103150806040f0308130503070f0303020c19030f0309020d06090606051f0e060405060d0b010e030d1701060302090d08030a0908030a0c0212041505181914 77
    0x29080c001c082c6400004c9104188683d60090b04503031070320803114007109001ca030f075600490b182c02d1080d03802b0354510808040e11801d05600c0850300d5440f16560030b10f49202005659031960764814800040c20b10545a4001410103109030112510040040121000c8014554105608000200c412004038904030360000400740280140802d254008110f0225611241c65071000381018003000c030382c0c65564410101d00e503507400f600d8500d03012319070740044410341c0c20300c402400c40e5801d10071251054505001c00c000c0380d03039044111000e00e01e9036a400b013207261900006841c0b0429502c001640b40c02003005101e03000381d110070002c0c0302c2d1018001c8980a6682c5520a41c124458940c400e5002125540d80c0c4001c240f9003401140c001d000c0d81c40c00200424284c41d65406a007040d42da1016482d1980b40ca090b030703107904118100007a8100c0780910320b424035080a41a00005002c6104140702000c14500e135988030306551642c040c0000350403864252421104101c0e031070058091000410301c00801000503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 65156666 1250 65155416 65155457
    0x2060f0105060a030b060702151306090506030c1e0c01020705070e01080c06070302160e0604050708060f0d02030307050d0206011806030b0105010e0d2001030e0a0209010b030402060708040b0a 84
    0x40701d038003421852502001c203004030f000d440020111600401d0800071040140ca60300810600801c00c10111900d031901c1e50000c1003582126400340c01002118802840300d0b5071400d046a400004102e2400d681c0c0101300c0000300d6070184540000c03d035070000316020900120640090a1451081c400e036002e403030321801a416106000e0003186000d90000c12800081d0800328014150386005e401160300310090000015101c0513260000b408401103202440907509240c01440d42150300350801944600e801808030f10b95490095005201e4032000023000159142482220b4407150884150f841d40008a04080d5072031b8800e10800780498070316503131b41b00356180a00c40d01c1d00342e84d80000802050b0b482d04004550000301d405400342e1010303802040340c000802000602c0215251810000c6c0c0c0003410300d001408a07040030f03205100d40c0e0400c005050041ea960070000d07040d240c40020854598a4500114800740900b81c0c0041481d08001800714070754611070040c0401941c0c80c4c0e500d1a02c00c000b1b5400c050b1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 65157916 1250 65156666 65156669
    0x8181206010603110f030a09060c0e1509040b06030f060a050d03020a11040605060d0504020108070c0506040807030c020a09090b0a021810050c0318041d03030403140712080702060f01 80
    0x16821400050001c40e00c00e40204413140e01070344a0300e0070003100343c2d000f0101d0391040c0d44140030503036201c07030f510100030f018003401e09040c14500f8500403900c40403001c52810012008240c801e003d0004881c0030315925a070110400381b002030041c646904e060200f003207103c0c1007a070365188940d81020700001c0602d400ca1a540100d0f80c1640a8403480c00160b6460090110303840c031650384a07440e14400700c0d041d02d45201034004d150080a0200d4682000d000141048202070007503003c12000c4514130b00412400a28076411070742c03044844e0f556000d1420115900c0b803006000960142501800250f510b4541c1c00c000640e60040182521390b46404828070100d1180303034400714500421410444080c9051f2207281d00045050800e01c0c90004e01981d0107041d5803014803922201207801040f11243e042070b200d50701c2d02c051001410107154082c010104d80c0d80c04002d100408000700d0850642400000d401500d82c02c95005d0b42d250f00070790441030007a00c0620308440190042c424400019804501c402c00c0a0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 65159166 1250 65157916 65157949
    0x60e0d020a15091203020d0f060b040501050705030f030f0411010512060d0f0203010e0d0905031506060f0d0f06080607020607080112020a17030c1e0d1d0405040818 72
    0x61003295940b000e00300b50760849084a035078030ba0814000c201d0030740325480c45620507030f00113075a030070450221000c0714001c148072000a4030b0304506003d40c2c000c0500300c0e0203540b400d0030140c4c1c0b107007020300d0010328600c100c101c09040d1090104c1401003441450071101d009521540d0f0340c4000b1820700004451a00900c429111000404004202a41000b00c000054907000340c00c490721410994011034296034600f0340e01180c66020900382c402590340015400c0c00f5010031000340c803419841d0034021030804800b0b07000034480c07075000601500902040d000c4900c089500034044c004002c14121000007840c0900c41c84105001d14000a840c0d0b0b1300c0820401d103d8182c90711043c140d42d0805440e504030601050007240c1100440c1400f00d090f01d1104907002e400c1920030010f60b41c0e2180f1518660806203004196421034242000b500d00b80c0c040481d02c9812110795281000c1084000900c882503203004020341030708645868244028409070700010403100c00058a020741010414084c41501982a0f8489 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 65160416 1250 65159166 65159173
    0x210050f040602090f0301151401081003060e070312020304050a1e030b06010201090c09050117060f0105060a030615180b04030309090b03030c0f0309041a010503040311010e1504060e0d02 82
    0x200060081d5016007020240640760003610717488500400d0031180c8034040320381d081170317407500400c5412080a44d46e80c20038028038062240e418450741c80840d081d0310b80001050142c9920f03c00c1c0040c502000004000c642280254001d80b40403803002c0e481c0d0f0b005d4005c4501a5000100101e42103520860081c2c251100c040c0400342c00c2d245845040760500c024207014119521640c20001041c40b2150b001c010301449100041c140d49040e54000702d018805602a00942114040005c4108030741032841c1100d009941a941d40c904d116011401031490390410144040c19180c1c501201e544a8084403520f24040c116450403502d80d080d81c00705000b1031100070001031070300c0d40921014225803c00030300702c1c0003c0d08503800c028000c02c043e030030300312109052a80d035030010440c603400349814001d160007903003c01c8503000d00c1048000003d010703100041c006000d2044c0607075000b02492095001211401045080c0c85040400d294000d01b4003800f603509541039820f01219043c401c9001c0f0300100c072120181c008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 65161666 1250 65160416 65160421
    0x607080703080405070f090204080705010e0112150f0303080a050702010e0a02011d03070e0406140103020a0b0a020f06090a02031621050c04050a2307050301170f12040302010210050f 80
    0x120b541c141c0007031046585000d59030000480c0c054031900c55014100759000035850310700300f551048c5041c0032940124100301d00e40c1d0000105076000407040385883e00424000c81c100c174124451907071036103840d8403000590300714038000014142d11010b19409032034074203810300031030b118004100d00f03030ba100340184035164100344000001076010309040a01959240c20241000c0e00440001f4140403c1303038001103040b1000741c10001001500d10442c2070100700c00c5120380d129419500803602002003400303280146800081d00d443ca040c020081c1c0303640402c0071000c407041458181420341e150400d04404034040d10035541450b240701c0204102100b6501d42c12070b45031811041c088500d024550b50390381510603015203601480d00340c070b49000350f0303110b015030800205003061b1604550f4076903185e0808440c51100900d0a20020503800000c80b0b0454120900d5001070500d66100030b07061a44040204c3c0303035403140e4100e401c1c8001c070160103801164000d030255002c800c11034181005644c000c982070240c14130300500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 65162916 1250 65161666 65161673
    0xc01051803031f0f030812011a04090c051306031a040501140d0f0501050403090e06120c0112060503070f09150602031c0207023a020310050411090c04031106070807 72
    0x2c42d14002d40c05458000c07406035607442500d002013820340003683d11820000c2c00303a02800d960481c2c03900401628542c800010040e10001209005500034540c4150f10340900808003841941941c0e009100350302d034240025968007028006040384c85100c2600d01c4c214912050502d024844d142c12582150310b5080260f10303900130002200b04c0b40c50100d8882a10201c4480464824811140300303501c00d4440da04004d04000c1036a41e035500081181e4030512542c096144210004600c4820400083c03d040044043e801324600203821341e42c02281e007511400d0300000d00341903504405002c03144112000c01c0b1038074202d049404400340c1401003402581c010080c0c10b600104151289401041e818801030130f00159500007140401070190b0310131408444421300184c10401070080540c106200ba81890301482070740840e84441103442002d0303007a079481e00001c00307001036080b000c51010300040c12624940740800140410350050700080d2004200708039441c025081002c121110b0380d40000780581443c0141d607 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 65164166 1250 65162916 65162941
    0x20703050711011b050c03010b1507120504120c051302030405060c070f0618030908011b0e0d080a08041407140607050c0604060908060f0f060d060204080d050c0105180303 75
    0x20b0305810003281042031203060384020107105540b40700341d0150013200112020103081d9400c4540c2c840c0300701c3c01d140340310004112740c0c0b0894174540c1e4852101c03020106a40b000382c60070f0089503c000c080032020a905010401c01a5030303402540c504686a05030307041c8031101c1c001240000c840040040e4090301c0416046132142025080b0144a000300700841c210315074528050350014000030f524000012007041c10503400588200c05008544003c2001d146100f0000c0c804034a40f40d084000d001101426042035120032860340304040c0c0020f94190380d80030000c0020503000c1c08840070750707140613080f01c4080d18840100d540011100d0041007180c501c2900c9003044050750140d04101c5241c801ea54200c0050784908011b84020610b5440d102da40310325160555042c80c4004080c041041c01c244200714074800c070840301c0350300050107840071611801c0619180000f44a00c1e002202640b0600f0400310040d503000c0d0043c00341e07085140c001e1265407074900000c2204c6c1030800300b140d0290010b100041382d102c00407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 65165416 1250 65164166 65164193
    0x3020f12010b040c080f07020a080f0f0c19140f030a050d090b0906011d06100309020102030f13150e030c0f0a120c0602010e030307020d080406091e02010e040207030507 74
    0x840001540407501c1d4001004c4402c00c6000b43d0228403981c0404c280048001c0140341d2011136400501100702042d584e021291003085600c851065000c079006100b907445030262400c0101c0ca404562070000b0a0300100514070011004492070345141200728003d100101d42c100e400f8000b10020741c2007281d078000980315a0050503a0301c2040741e0715401c03440420046c81655008400310400f4080070b50501066a2a50f0800c1c010b040c642ca5401007440f40030303265501000240714840ca400140c695081c40100e055114140546002440100d08038900042c0326081c007007120100300209000000c0d408080d07608904144102d64503402010005842d820107501c41b01829500600b004203c580b00d440c0d29160f01401c100c161000b0710652400c1c000e4a409204600e0420003201c021420341c501f203480256541194a03c8404009020000c00c0422505411130300600354082e0380c82c0c0e8980f5002111104401007040141d00050184101e03101720b05051080300c4210f90150f81e5540350a42c00d403203010b07009010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 65166666 1250 65165416 65165449
    0xc090e0601080705090d061409150f0601090f0905090d030b03030702041a0307060507050f011b030905032b0606030c05092b0803070e090f04060e0703050102040f030303050f0103020f 80
    0xb00040d0801e0b0f55801040340595110341f0001a0041a2905002c01900010080c0c80740340e12000b8002b007a00c1219200035882100d400d8200d02c40e5403a074004840300c01c410b41c004d00f14441424004108143d050304070328803410615040340c2c044414000200c0c1911220403000303805402c10440310025090a4105054020b900c44075141e464001d50082481d0050300d911030000114042813138001c12100380b106198200c03400d0003c0c400c03150340159400761114811200c1c42403540d144004400c211080c000d1311050705800c20303a0003000c061f0071940c1707190a2080c02800c80040c50008041492806845024000149a9a494100300748a024000c103d000300242c81d4a005507003c60210510105100152940c03090107501c2c0c60b424400c401501280b0300c8ae02c224411100d080030040d4120b424403a59510030f8011a022403c90b400c61301d883c0c00d118181d007000d0030550000802055481c61185000c007140d200e617a0400c600e54442410042d02007007808025031000184034501000d10f001080051605030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 65167916 1250 65166666 65166677
    0x50405011b030b09010b090a0e0415060605030906090706050a030c05070f0303090203190b0604230702160501030b1503190204120c350c090406020c010c090e06010807 73
    0x14201d00701e04010074034401c1d0400a0b840302d030708904505000110a0040004500301803c09001c240014219010340c003c2c00c28038104880040c062048003103801c2c04850303000c0010420039480c1c0100030800d070700448411a40c2e100e61004106103140c0022502c0454402e6501c0384c0c1848000074049001e4004c00c2108000c129083c000200070866400c0200f50444c400d403130000709164a4810300d402c000c3e205001d698103189045005000c44d030605007039640320908a07400582c00061601c2020803c0c81c8815103411512000200b140721500044c00707000c8100440340328104250749000450a0b2200d11036202d821110310108000485180300256400002104d2007018002c0080b2010040ba0441d0b44511881800030848000b4008101400c00c0502045481d00b981c0100f0a440c024020701d894240b030528028455503114080018020662a01001040740d9410700f09414031802079001098680c031194a0200c1130146a0300a1200a00312842b59844000c241e60300401034464002c010490000d025 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 65169166 1250 65167916 65167931
    0x1303080601140408120304050106060903050a02010305060604080a0f03030513020a050d051c030c0914061b01110d05010305010c0806030d0f02070302060706051b0418050603010e07030b07020607081905040501 91
    0x2040c801c4e030708175820403442140c503890903042503130945c0d9071a031240041c4500d1103c1480810000324256100a40a0801090a80755103000c14078521030b50f40a100c080c05980f8410040084504038540c2c0d00b4080d9400740429111090411074103280410000c0d4000c401483c2048181440d0300020742c80390141c1c0980d84101c414905036003070401c40f10b042d800043d43d20401049290b4010200c0405443c10900e48003100d44c04001080151282100c00c0803071642e22040c140618000b5085003000211078801c1d1034441c4202c60413070000d440203010031907013542044d07204160580300d008410310412004006200100881178195410800442d085045004802010016894000c0203025051143d100000d4030702c1c01c07001c589909a24408103c254000400c801c0084001907610b002600e140da0f00001100c0e100c0400007401018400320320503060245210000902100d000e00c5440b6105540030388004e60b0300c80348202e549490817101203191282440d405da030356110350303401540d101d80304900001e4500c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 65170416 1250 65169166 65169179
    0xb06040509010e0415050601080a0902030c0a1e08010b010c12030b06161101030b01020309060a031d060711030c060106080910060f05040b01030e12030403140309060f13030806011404 80
    0x49500743c10100200e09010280020813104001441c40c500030b01700204540e080070030000340b0300301000e404e41c08030039101c0c0315040c195a0144a80e10101d40300800c640c14090382c908400d8402c880039050405105800c000c00a400390040c000c00030400c105a40e80350300d05181da81e5000644420000080c1010350f00d1008900c41c0c1c4400000348494034200014030084441483c10304090703c0303140c290b80d0416003030910320800350760000207507080200f04442940d03d902140303404800820544242124042103210400344c0b440c404151140202001d40d10844d480618000d0640d480c402d481040c40344d61f0200004200f081e06c900743c926041460a410780d10043c1407900200d06907045500305107186250b42030100854a0140304e44442e01c1402c2c2018065003200303540f42c030784a40781c804c68210708040c0000001c01b054494811126404070340004070f5100c0c200903041940d10601110112030701034800c00412491044022032081142d0b141d501e0342000d0380c0720b04c01100c810100320140000c1d280b00b4030020406 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 65171666 1250 65170416 65170429
    0x18060206060d03141c020d0c0e09010e2e08010b03030a05071101140c010608010b030f06150a0305070e0f220f111c021c050d030c0c1a0403080114130b060405 69
    0x345c034070b82c0c0580c03070750300034002c280448215400000601c09015245080e40d120804018111000c0340d0b00650a941d8095400d080d03010050b12180d50a0b100c1d9000c3c040c000140242c1c0c80649070a03d00812428501b0810305560f44180c900010114006202c0c4c0400201d4041001360030000614100704038015104054150750051500b04040b65190081440340307a800340b0503540b240354120020401c0178160858541c441002420035041450380c03010000305074a404400a0045070b00004840040c0c2c0d8600d4407102e002d8080d95035800c41880344010500004000420304050140758120001182195652440c1817000f243c085415084074101c229655840e0300488080104981248862895a104001c40072101040650f840c04500c03030200e001c00c400041640603c0e1003810b0004010a80d06400c4d03420948068001b05113005244c0d00b00b00c1c3c803a100d101d0760301940c801d455442c0d090340ca17094812407a0039584025a049100361042e501a0101a00f0442c10f5800c0984500d103000c1e11171010600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 65172916 1250 65171666 65171707
    0x100b060f0d140903032403010912020304030b01080705060901030b0a180902010909051302010822030504080606150d0917030f090d0c0b010b0702130c18060206060d0314 74
    0x5201c0c1d80e81d22080780661907600075a42c0260590041d41c40c40c034001d054a00b00194610248980c460326441d64103203a1800d500c4209110740000e0000c0089405090080d034a42c403901003290b19410900002503032081c0044c0304c209655004100740c0c02d150028004500400c000c0c8031580c0d01035400b2100013820003400050302800c010701000400c04000302d0001510588231a400304203850f1501c401c102400d10254040100712341d091800c0c0700c0d80e41b1403943d1100007080380c00f0301445e0014004c028008168010000b4421116040140d41c042d903500710401c1000340c0d906818021090080200c03c014241300e40c0081c00729032040d8003050b060380c0004401025500120341840340e000244007030010b20401004075090301600c91074205000d00300e550b9950031090b41841030a17140030020078131800719235a0800000140040e654100203180d544000202840d02200b9004441c002e01900031031003900c0402c071725200e540c014104000e041c000d42e800701ea05003050020b40715000c0084c0422603143e504079081c0f49 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 65174166 1250 65172916 65172937
    0x221101050c10050a0605030c0f09041106120c07060614210a0c0305010c080112050705010e040b030102121503010c05090d0206070b090c040b04020a0f08180d05070611040602100b060f 80
    0x5e6103818202414900b0940a0590b403042d90b1050f8400f4460781e403d10002c3d0b119901648000c4000694004920a40500c00000800001d43d408200c00c00c0f1040300a031603000c0c000c000501c03d60307556514601900c41d2048c02107402200c0310513500010781c2c44140215a101000c0c08440f200d1005441e20381070080103810444c3c0030707510340120b21400c946c05035205016140c0ca80005980b4090355440b15590301e85846998103100590849005542d0b0300e0b072010503030840180080d550740c1c14401850b0710303c00c0100d82040743c0da001d0107903da0907405e05208103081d9905a40b55540b510400c00c0401034412402da20480e40110104078200001c2c00e40c1403a1402401e2090013407284201110421003628582c40d66680200d00c107001240c12154401785d161401400d904015000b40c40344c00c00740f404a448111070080603c200240402120b0f403210003092000d0041c1c404120030071051a0035035003403007280b1034003005a02c09040070382ea01d04254050051074100400c0d50f8036013000c503050024690001c0b207104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 65175416 1250 65174166 65174171
    0xf1209050d03110c1002100b01090b04030501050f1501121109060a050c010612020d02040b011223100e1b04090c0507050c030706090b0c0a02130203221101050c10050a 73
    0x100030000708400c0c04e05100c222103120f1441d0405d074000b50760b0703a00643c40307641003502c81d1214030030790740140501006004c484010035503450310303802c10300c0c0031740710a44120001e881003500040c0d880030714003000307186a84141c0d41e40003440c1c481c003203c4001d13004a01d103444100300d040004020ba55104c00050000703d4035034460b151201008500e5508541080d4003541007038684480c4100181c1e51f501071040460341c100c1e0000ba460700c19400403145080f0694003c045545820010014024140c002c130b5a10308403402d03141c1460f51154038880004103035100302000e07246040c0110316240880c00b00580c602210310082c0b410191740c1c180b00c0d0195008409804d02260001900c0818403605000400c00840144c004001042c6082002041080e651103004031141e400300b0742c0c940014083c0111082150020039090120021002407002580140d6038400c0321040c0e8102051049121314101d081079800c071b110100b44529038801956260700c90729100c5440d018081100c0c08030b034103038802c0c80c0c095109140b00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 65176666 1250 65175416 65175437
    0x1306170a0311070602030a030c03020705102c030304060b031029040c08060114070803040503031f0806040b0a0b0d110301060609051e0414070c0b0109090f1209050d03 73
    0x15240450341802e002c9260000c500c24440da9400004444240c0318a2070700198000340748004400074010180001c20a0144801041030600213801900c01c004801c205100b5200383c01d900340c07444607220448100d140e001800000c0200380715038065040e001014017079804244460808100725412104203920003031904407201380e5200c0c0040030b100000d0080c3d404100000503140d01400e14a0010081810040442c806a02a0542c41d05603a842548409100d40340d0034589452900c1c2c0e0001c40e101c0f2a5101a80e00c01d080c00d01c280c0071607000321402e10000d0a42e58985440da03982d2640300034910b00700e00783ca54903210311036241c001102e00343d20f00030300c003038808034685038101400e485403035002074100903100c1c106000c0e55036030204000b01180e840e2001c0001090f50070205003e0600b10020101000a40b0200f00403603802c4071003904000c1c81429403030f0080c4c4e00c941046044481c5164082d15001c0741a4921300003034006a2602c440d08220306140b11301595650009520740041f800460004040240 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 65177916 1250 65176666 65176673
    0x121109040516060e0108040b07110706090e07180308030601030b0a1d06121b040f14010f08030a0e060702030f0d0e030606030a0201021203070509030d1e0201050c0301051306170a 78
    0xc0902801c0f6614110702e0740420040000d211a4010b0000740003000e07040041203515000e007941000c00c46040040c3d94000d540c0d00b41c064045c2000b07110703c809000d0300d040054070a900c15003c00c2c00784103840b2148071045046448900b003607040105154140340e920007001d492652081d0f0300342d0081424a000400e201280c039442440c07841c000c0d00c29405004030407112718001c6c002148414040603001c1e040c45840b1841c1c000903026100020031049441d00c1c107002d480310115124562410398203c140c1142060f0f580764411a0f40388660407425001504402081840307207894401052994001012500d40c280410340850910190340f94442c00b0852110440055003018400d4562040003100a02141c5100b600041d4030703400c140d40c075001e04210000003c5c044902602c10b440f070364880941201d00742e500541e0040c1071490001181c44480305401c010b000000e01c1400341c1c510510800c1013840c01c69180406000f500050390490000d038a403104c401050032020190321201c1d02c0507040041608a440e0704 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 65179166 1250 65177916 65177953
    0xf0302030c04090b220218100605040602070614120109020409060b250f06060b07061425020703060f02040f05062122050706030e0102131211090405 65
    0x12050186040038501008900400300a540c00442c5007240d90000070060f4800366080404031009521954607504400300d01c7c01c03400c4e540d00c03d0320404171100f40151544e000380c6550040388202d10040e4008882400110710501030b443e0041040c0691a090a14040c00034401d83e100b608642a51079020904102c03198590040300020080780000340c0ca0407428503020320020f80c9401444620302c4001d8003480821805241c52898540c200004100c0c0c1900c2d2141c41010764406107058171018200442c050014150135401405591400080340c5600100050442078108982038101907000318507000000c541700340542d5903a4010700600581e83d070300300700e07020301e00380c1160700700342e00403901402108480301d0040d044005003003420030144925030711010200751440000020700b00b01c407400c940400170090002410006d640b51034906000341109030804500700c0c0200d00e16142043e0008900300f00b01801e102c42141080d0156010180d140301c0031004c140f80c5002982c045038075511500300c2030783e07880a14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 65180416 1250 65179166 65179183
    0xc0d030e0c010f0504050904030e090903030601020c0f0102190501110412020a060206130f02060403060606021b030f0d0c050c0324090c0d060c120e0a020a140d080a020c0a0f030203 79
    0xd0070420f81c44103c802008081380250f001b582c0c0500e00c3c0201060605006503540d26100f00014070900c008d18100300003a80f83c4e002a2440390140c416221201c0e000d03c0e100c11076264140040e401002d007000da0595181900d1003040d820344541d50786503114080c001010000740081e014a02c0c880c0302880030791051021180003940040d045401071814000c0341409038080005068011601f62030342051400000c042d8820b59100070111880c204001400c0c98000c941c203500ea00c0c8101100d80324030084402c0c1501c408420380c3c1401c6641004800b00340c0c00340100d924a130014080d600711480100322070040791a080c11030394500101140f81800740f042c1d0035046101ea9000360350a01521085000d60040784054902007001801c841c0c0311358070340012502c1408802c0d0003242c1d000c020b205070340f001c1d02c01039118400c00c1c0c2d080c0d010784c06d1250080b40000c80ca83d060164214068049800e600e09602c410310581c20595502d02140698201075501d0743d951348101e006400c40301d00c14503002d403461042500d0078121 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 65181666 1250 65180416 65180419
    0xe0102121201060815040219030b0d0210260103080304051c0804020d0807050706080114010915030513050304090c0f020607020a0212070905010806150612011203050c0d030e0c 77
    0x400c1401090707401080824111002410203904a8481202c04150400d1140c1c40f40e411510209801c980f907501d012402c030600a807902d007002249000d40901074100c0e451240070f9040740c0c00b408940b561520036100d45d408220200c40c404001000d0400f51600c484081c0e2095803541000700c2030000703000f030610410710100681e4054008004c002c403c09042600000e00103446080c004542d101441090000c68440c2a8000d0079904004d417141e40187c14080203000e110806414041c44440d99402014885c0c10b64606448550309034280d21030440c05404020070502144c80c9030181d000c00604104040e00141450b2000441c0018040c44000c04100c45200940c0842d4408414040490340100d00c4841060f0141c0c6e01c00030491100c2d80b41c2d0310f031241607802110b065203420b0000809070303408545c3d603010b48003039000d9034403482c10bc00412030f0500550020390000060540104140d0f00800080021244070b41001400c050241406500b41240ca03000000483d03122040c0e007802207010320501090580 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 65182916 1250 65181666 65181703
    0x109051509060c0304061d060a0b030307030504180204030203061e06040b0d030f0e030f0c0a080303040320150a0f1413030806030c03010c0207060905010302070f02060a1e0e0102 78
    0x10001d03201540c0d40d002514605028000101080601c101d1307801216000e10000d091104984051070055541c150460789181070030301d0f20010001d00e180100403104101d41540d5170500b05820046502860742c041c0c4a51030000e40d0070031000006845c00c3c0100d910071111050384c0541d03521100b030b44220840300200124071a503c0c00c8503400e450790b141c40544241603090314000164070140c01c401c0d21030010625066606200f402005107088e080020ba00d0b83d108016282c5845096603661015a28002a10010042081802501c56260707251032147d0850f08044112502180c800d40e9116071204192420383c0020740b9003403d030160160710302580302e9a0400e041000d01c0c41c07400141c030704a0071641d904d00904000c04040400c8169070108151307500114010000c2000420140c0069941c128501c120700200f800c40c140003806600034030950321041d40100c031907207200c40d40354200019a0300c000c4403d030a02c400c92101d0480c40741045242205000180c64090510300c10038000f92a114040034589041030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 65184166 1250 65182916 65182921
    0x915050109060501050d020703090f081608070501091e09020a1106090c0f01052b021201120203030403030e03150906180102180411120702010f1a09062202070501090515 74
    0x176800320031142d500000882c0140c071140c02c2c1c07908884140c410780c0500d04114210101103030389403002c600e20341d0550214025102181ea50340c03600751942054481e290215035070020800044110702c0e46a04a82034105099482540301c01c901002ca800101003d000112400000d01100100b00541508001044018000d6403e070200040c80100341032040f84c10441d000c90490742d14032040c04200044011100300710740302c000611008000b5000b200c1c010245900e15400090a01c046003034080e455078001e00a549058250348003540c036401000403554052240341260074100c130703018002c180595040400b4101c941029180c070060001c1c0d030001d5160a0b4810481c103001e4100101002e46161001d95010500c40c100c880b115107280204040d0061240700e202c10001d407541e0650002000c001542c2e000c02c02c3d4410440501c00d40c40c00315203003582260810010a51a24041c039000d07106d0340407507186a00c2c2e40c050108100590700058402c98441e9140c8a240040040c18412001101220740c80c405161 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 65185416 1250 65184166 65184169
    0x30b010813111305010803180a060801062a060e10060b04030b100305060405010e1501050d142503050c010503040804030609020f0603010e07020d0203030714030a0e0109150501090605 80
    0x407000c03003401890350368001d00302d10158403042030840740c00e03508603c01c000560392090125101c2d4414036590342e400071209803d841c10700d068500e0303400780c44040d9034202050313092001c1603c84191003411845002c5426030341c003500c01214814541e030248280e8002c69154504d134405480c10000003210024642095821700c5501480001c3e1000c0700d411000c03015040d02c0790840d960900103982c10140180c01100104030612034150005c29607400110115a807090240e24410440e800038020554001c071103811800c003198016006003580800c07841560140740034900b62141d45442001140503540080e80b041080c00030520210404c42c4082c28554914a03050340d40c24110b01c147e0100400260743d4840c200d0540d159681000014000500301540d41e5864110f42064880121000300062260072130b9480c20320b101000762405034841e51036a0141c10f90150a024440e0801400280c22a40c0c805041000502c24001e101d0804c4c000e0302c85900344032800c840001940c0c8143c0003041e44508102d4204a00d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 65186666 1250 65185416 65185441
    0x5010f05030c0103110c1912050a1205060a05030610290412060908030c0711030109020303090f060d060b0a080114010816031407020309010e0f0906010c0807050d02010b01030b0108 79
    0x80082440d000605c54020f0039130900f20b014400e4804564480d82c4403000303141e40d40a02020b0094043d1020313510080d00494100d89a100d07508881c3c0000703c1c8140c1230b4461240a0300055000100100006581901e5202192601c4022a01542502c1940104001d0322029059100f83d5030115004032010041a510004a510891003a500c1c5003242d81c1d10740c0144009a40000482a40101d50075640d0920020005075a081240c042e500c075941001c800426241c140315442d01c1c0c42d40a00a142040340c810100002002200c01039500a8400c21584c4103000c1d45201c1c10f030142400a0446407070f001c107000010b10081c016081074444030030b100c00c000016a0822101daa100000302002540175800d164210081e00140381120309444050040c400d00d00d402102500300898280c1c3e0300c00c005441c403801c01004800f07107000141c11140b171f01c0120300c3c01e501c0740010b0a0018040d0340f115203029031990714146001d402c9400d010041c0d40d2600d042540b036905000da00e64010342441d1003250780c203151f06515030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 65187916 1250 65186666 65186683
    0x6030f080a021204181a0f0405070302041a071205040305030d1e09030806040b06040308070807020103140907030209010504020a08070e1f080a06080a0305030115020304090e0c010305010f0503 84
    0xc20440840d00328803142c402c000a5158103015001142c440b540c1c2c0d03440c0b034008a00c0c4080c55075510304009100c4003218104a103444a0f900081404841c211240c0920008090191181c81019004c0201040c00f07060f0302e217105030201603c0c144607561101403c1401c0b029560426520801c20704004c10404100d001050740c4c004d4244150000b90756184403501000d01661030401c06103d41058282c0080c5500029003522a100a030780621900710800204000b5104500004004007414842c007408250404040c062992060400040448101000683d056001c80344d41c0c0c610f60158130103000718280900d40354018103080c5c0c3c00b0750425405200c0034008040040c060001c04c0a01c442c1d608059460030702c20f180b940d401c0340760f201801c40b10302402440306004480e000302c0c841c00d01c5400203502000141a510080d050b5480604503400c20b48000e030841031710280171003148801d1002050203030040c8600c402a44408d03006007800c2c1c0c91400094252041603100f96000038803000100400e40700403e0350031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 65189166 1250 65187916 65187923
    0xe01090f110d0210031d1204090e07030b0117150c03010905130b18010b0a121b030c14030d020c010219170307020106030213021c092310060906030f 65
    0x40031603000720085518030400102c040d61041001c060b0485940e01544140b001506c11180c84910076a405007084e0754080c0e0a03101288510200020002c02415900c410880204030050b59203080e030300e40314501d100340280c00c54940005015002e0041c7c041c00c10918400c0c4810f50580700e018a86800309030b0b404d0005201d40b024250302e5100080700321800300c41d1405030550020300b04002d424810218826088040c04a079415031070841040198030701421154101c0c5c00b00b805886d00c00c80c0341d5840e10300c0f003190700300703440801d45584c0800300001e40f01c1c038060006440086942c105c20b1081030205071a0003000503800040d9044061540340f40d0744c1c00300340c03100310018400c0341c610380840d203203072560b4038100405040c0d2183c207010080c03041c0c0e40d81c1900a43c0c204c0340211001c42c0258990981e220403482030240790320150504401128102500c0c2e000100040e006049518080000b03040d0090300383c0c4c100d0310001c21900140180794031040503110303180182c860344408012603800c40c1d607581e8a40c0202a00603 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 65190416 1250 65189166 65189183
    0xc060506010219050c011403090a11060d0603030302070b060906090403110a0c03060507080f07080a090609080a080105040e030c0a02090a02091801032d060e030f16060e01090f 77
    0x3451079000b0030450024114a05120402161034200503031115090030303903180010054020000c8042000c410790f40a001c010340a4030740c04245030342d8a5807135000340445503080700c4103001000320011a44501d100942c001c0c3c601507581e04151401c05415100105454803c05444007442141c2e03c60b22001d591007a40750400c54a0b00409461440c901030f4006002446000340b04004002c001094100f03d0003401c040d11010240d44075000140c004c101d00310340e0140094001800640d1307502098012001c46c0d4003400c00050f11510f00cae00c400d8080c0c2d200b40c081102061040380100140d0a10b0f229104509140308042c606040c43d503030a207500c1e1002507a02a100385410004603010304401c0c0d0480c0c0311040010240391000c0d0102c030000c440b90000344020340704848460b51400c0c144098915204106000307038602c982031109980da840042110782c2c6091040e200500010106851180c000d04820850a480c400c94106615000c801e48540415000d03030750341060152800070304100070482c035955003c0841d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 65191666 1250 65190416 65190421
    0xa050c0a020d180909060608010609050f1f030f080c07050a0b1c06080706020a050c03010b3303010609090f0207021503090a05010216061805030307030c1205070216080705010c0605 79
    0x8a0601c00c4203600404c0c04949013241400401c2610340c48403045642c0c40c0001d00076199110800e50807110212141c5294000c524005142020384104252042d0000f80190102a880740c0300c80d0300c0280720744001c075084080024100010380d4200103043c01800200e8244024509240f0340940c030340940b00400c240f10459501401001c01030f500581c0107050044119800240c1d030b030000940d2852000c0c800e03103a5019074075038406c0b2800e0600603c1c0004102034003618851094240b00e510b00d54000082003407980844140c0988076103400c005500034000c66841021027400d141c10721048882c22800c040050380704029210042e01c0b03114034040c8101020b82d070341d5281d80e5800c180350b00f4080c030800d004180d5440010801d0703010240c0140d5810440c0501d00c20400720002c0c140c0981030344100c0c04007030f110b588180700043c8003510a0300828800212803411390505100d0400c108250344060302d00c0009030300030803070b814002e0692440c41030051000400a1181c240b8200020340350303000d0200b0260016469400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 65192916 1250 65191666 65191697
    0x240108010b0f1e041806060e100f05060d18060c02250603020306031009060207140c030604142401030b10060f0302090406030506070804120c0b0c090f0d0501050a050c0a020d 76
    0xc20ba00c0461040c03121112038070a8139086c00180010b01405d0f800a084a0200d002c031200c40c0b0f8980c00b61a00c07880394800d003500b008204401c58000e441d04890301c40e02e5100c1410f080c80120b14002c0da8500c64500451a010200b0011742404160301d200c000030420308481c0c0824003e50304540085a4040c280182d40e6182c180103e800d00c0700010340d014040342420401001c000040d402401024020405030070424030351005191640a803d40e01d642c035900c140041408500e03a402c10030318542d9440f0490304c9070040d000c464008444207100c0c1d1102030030804010001c1c8060104041d40c00098020105a1941401342c060aa1181c140c100d104150780803440240a8445600c242e000e0f58100048401500d4556001000000c04440c1240d03010382d420305101401e0700a0418144241d400044070b1469136985c4e030792144940103190044e9003d045030342c5004150b225001112001c5003d43d001007280e1401d00303120815290054034003a01c84500300624000e1690104031110040405d01c0c24110200311000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 65194166 1250 65192916 65192921
    0x207110f01182d150f03020708030601210c081512070b0a09030b0c0c010606050301150503090703020a06080f010501020a080304080304031817060a0c050403020d0302240108010b0f1e04 81
    0x10704603401e20782c801e80c1c0400c000d0410000403058130201d0f510140c044091a0085050b8095418024442d0b00280301050241d805a048400d5145e05104c4200b070800300001004241d0f401c1c0d121500108401100348006002c3c040c40c1c1d880c04030419034540d401189040e0a00b59160124801c502004c140410b510009078801c1c24000010f5070003060100c0181004030040d500d07a400011042210741c0303480e0000131401e0085040d0f9040344c0c900d03404d080d88005182425113035944003c040c2d44603805000000310042c0e0780d00700c144001d0071160345d4549061802c24103d02e29010706070441d0307040d9889000c02d000016107203006ca0f80e2282c1d0103890307203403242c8403842c068424055501c0310300d2500a8811021a035003182052001e004501c01c000c47e492502ca540d001030484600e15018400110100428805400d1010909008501c20710440e100c0c05000100c108600440c0285410031900030302c0100000c1c00c00f4050461038040803620810640203840000d030280e60640c0e80d00700e1404446420340355907550703136 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 65195416 1250 65194166 65194229
    0x9040f120e040f0b09060909030306060702040e0a0812010803071e030c0c0303050306040606050c0601090c180b0403020a0503010b01020d030c1b1a070203030408090d0609060207110f0118 82
    0x1901c00d105031103c010103840540200c02256010740b08180015125280c9040041c0c0a4000c240245d844e5440d41000d000b140c2e40400400da8000b5125a034180c41c4100800a1010b540c0c040d0308066280e003000c0f51785e49140c000c10b0340000c4142e070003440704a000c680102c1e00e0009001907800da8a01055442c9010340394122040d0000c0c1c80461221400014103070450011445103000b101c00300056529035105440501070502d44000d2544214014080003280f41c0c04a03220b02c042e4100401d050b00d030a20f642041c9805500b00c0d200008001c1070410460800715882c0c005443c084000f4442032041c071000070344d103600480340035007010303101c80580e140d8901802081d821000e1019136000c1c1841181000d0f8119540355003034030b025094072170008070240d03c0441524040d0340c5c031980b881d103070480300d0080240030708443d001512210703a04e0700e407100024039510050100c03910604d441030241410504120310a0700000450381400440a0f40d40c02c0d0b11140f4500301d0070341b150761088812004000e040100c0d6040e10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 65196666 1250 65195416 65195419
    0xb0a08040213020a0c1209120809210d0201140106120b0418050102070c0501030c02070306050405191211010506010c020d290f090c01080406020d0912090f0509040f120e 74
    0x1c0c45400036174004c0d80b40342e91034020032034001280311441c021078881d4180d2280751068188850701c203000424150003001d64610040580003411020031044940001f952000e1005a01544a80c0649034081c02401110501071200700069803400c00050981428600e24240c07841d035a0060000942d5180e0040009910240100005242c6460028001e5121443c252045442004002400e40c07090250003034180140d400790641c0c614641d42d120180070058022034107030041d02c101356088031525404980541c000c07010440100e02e51440079080011510040107564184010003d150343c0083d00065800e5069031900e0403070074503003000000140503c0b44900c11211005d1590900c4600c0e0361a2805511303019181007a648684108627590b41c0f085080d80e0204585000040114207142e02a003094100c4003004100754001da80e40c48100d035004040e040116034204028820a800701d001d0703001030b01d419200b018803400d0946920b04c07449008a4005c0050b00f501e1a0746494078803980d8800b0340d20a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 65197916 1250 65196666 65196671
    0x509090a0f0501140f0f0303070305070503040e071707110d0c020a05040c090510080105030613031709031c110f03100b0408150924070e0603160212040b0a08040213 72
    0x2100e0f058260581d58a0040318400c03c1c1c400f01000e01c1b4680003010307400e0240018011454145659001d9076183c00469095521740401c0c08001070110601704042d11940460750340703820740a031915841c51101d402801c50805c000704494101c041480000c1d0800919105043c086401011440000c0802c81140c0015400a0821a4250440741c10124280c180c460031114079007c400c41d00070403070304000244541585540044089440080d0504c00a14824040c1c40e02c103140c000c00350401440f102c006d80d80066258400a070140c0c1820040641411814040303209001c14040301031b101040d4085d000550400c18000804a203489174100d202c04001c004410001c0d443e15590800749482d5080448260460380100340004c00c8400c0210300d245200a07d003014004150f020030321030006000080080092015400130b040c45652740b44041d6100f4010f480e5603140c10604004003e0074625032000d1078140c002e0a20003070040210010580e50001e4562920138102e54450000462140e00300d1400c0210a1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 65199166 1250 65197916 65197919
    0xc030a0305130810020301140904150504020a0b1602090a0b03030415031404050c0910051c050106090f0902040b22020a090506040b03060117100506070807050601080f0705010504060509090a0f0501 86
    0x15030a4001d0347c12106143d0700c0d0f000c007000300700600c81c0404080342c0040c542c3c0c5c03110150a8201005078032040d0010f0010303107007219240c1c0b40d280340e42072948040b094069400b0386034608021440c1c01c0605580c49803c428042c405064650040381d6a809a80910b0780c410310341910018145101380d2201c55419002600146182407506001d5104c20041100c20300443c00300c1c0000e03070b60b60084d520030011518040d02c549803480303a41c0c0c3c00a07000044654111219503c0700d80005000c036041c080e00c000b900000600250004691040004a462008607940980780c0f0201c0f20038040846880b176058544c15500c003581d5000044400c503540191508030780d6203c0008100861003151f184080c40c80f922007a01c031008900040c480c0305070002000c8950039000c1c440c03000240080d0038400702500e60544168001c600b80b040c1740d551203041820980020600340c1c02207480b584040c80400814006010070309005150a040c920001c1051041c400361600030b402040124600114640c04598040340b610320070030455 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 65200416 1250 65199166 65199193
    0x14010b0301111e0a0905040e0c130b04230403110115030b010e0603010605240d020706050609130c0303030b01050c01050a0209040c0509030a0b0c040902030403050306120c030a03051308 81
    0x107801110103c2c0c04078884030a42e2a90502041c2184c601041d01e0300d805c0c00305454642000050325100200e40c2c2e25009030401030056481e00d0001d000c01c070910850100ea40400d8000f40000c850703990b1480d01c065049840d1042085d4145299581c02682501e441d1608260042d00d280c0541300010450a16043c0c4040020502204045481c10390b410883d1a011640b10703501007600b60f0310180075450380500080b58040405041c0032018084410200c52103090810f000581c1e0201c2c2c11812054404036160700400486203441c2e000c156002c0d40300d8071b419043c1c103015110300e20310380b116001c02010716a032450981c00d41e0b8062825910070a119000a100901d405110a0301942003021800c2c055401c00113500c208500840c2940d00d00300001d402080000202d85540d10010006064080d41140420001c03c2850242c00290b100c0e40c002d80300e184c0d590a1a030b0a001c1014280e1881c0f042c5038101c1080300344142d4002c0750b280c109503007601d4402c0c2c0b2610700300000202c11105500c10034075442032038190240d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 65201666 1250 65200416 65200451
    0x302030d050a0515130e06090d03060f0b16020f040f09050c062d04030f0b090606060304020f0103050703021306090302030c0a0605030106030e0c12060a0b030f0a14010b0301 76
    0x519041031414031090b1115007001064400c16074a01352011040340c1070710005d04100f8000d4220802455010481000900f003441c10404259603405090b0408800c0c0c0c5001074250203842c008160550155003038a150100180c0d0500070040c031030391200450b0b440700c4155541c030380e05c002602c0070040040180819043e911402020307609801c0b45c40b40140010705900340341500986121031101090007a0046c40300580e00c40c0c0c18a0604450702402c42480b012001c01c0013904480c03101d03841030a14a00900b0500300041c6020002010540714101c00c004010060300c074090708012500003801e0100301901c030810164081e02400c61205140704a204c0300082e01d0fa071100d01a011240241c0944110a940c1c00901070151417501404001c5070b820801040441c0c400d13440702041070001c03001d03905015020380018568403080a80c0030481d611503428408c0300c150074451100042000c0f4001d04904103100340258aa00c85001c000e0144180120100c900050a4009010428005008011005c14402a03800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 65202916 1250 65201666 65201677
    0x4081e0f0304020a090204080c21030c0a030806030c0f0607060603290a0c050405012d0e010206180d120608100c0f020114040209040f0506090c10020a0c0905130c03030203 75
    0x81380c0911a0001201c0025100321825034030300e90090064410840240280780b50400c00c82e000036450041401c2c02c0c2203045c03000e0494240020046d0255000a0600a20740706002d441148681c1120310305815941d200f9a14501c41d44040d214607880781c5050400100800c0d8562002d8006a04c0c2e040041243c3da0310140c0e1820120460255a06515a540000d08841c135018141e008528204010f03c0b0542c011001c50712241600e440e0601e0b600c22640743e00d91445a03103c1d0b1640402ca084030480311a60301800080d0f846500c44829600c540070138a40706903600054941d00003804101000c040d0400d545030080005001100c04683c10030820301c221381c00601d410b160080004074951800e00f11181706010711889022188890040c0b40c0b256000c0100c0c18402410458898140c00d218000040e018041c0320322502802c0e01a00c044800902801080038030312958200710b40080006c0c40c009140700c91400140c6034030441c000703030503926640d031500c0c600032071a000fa1650703201d4500001050b500000818 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 65204166 1250 65202916 65202919
    0xb030607030605010f05030c092103190809060709090b060408030408030c0115030c0501030c050706050f06031006030c0e04030c050f07140402030114010e061306080406050f070804081e0f030402 85
    0x11815082c100112118081a48c48403100902000559401c3c60140c030071403a440c550003082c080103140d003800540380d81c3c0440700c140c005903a041c0d40107515942080034981e00c156040090301080c5080080180100840e000f0032491545e181401c01a030788480c4282d8014040500890781e41d02d4450344025540c4c0c00140e00041c1541c200040b4001903010302166404403640000000398513414480103501900c407640410707040040501540700402e80c18061140614506000300c80c55042800601d824404034600f20003d441c00c1800c101b00049003082d2241c00c8516540141209403100e19044610f80703500140a80603100c1c803a900721038254003040501c22245480280301180841d0000d00c42640024070540c581c4100d80b00f013036a40c0e94051a00c2260b031201c018100ba00d00504400140305004641d009100000d80e441c003000b040040d40d1081d0b40d00408052168411842d0200d40208a113600a00080a118000c600d0489010811020001600c048007005490f82d075440d200048603001101d099 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 65205416 1250 65204166 65204177
    0xd060f050a0303140705100908071203020a020c0d080c16091b050901030f0608010501090e16080a1e080a08071b08030121020909010209010f020d050d0f0b03060703060501 75
    0xc4a140c501107107001c40358103498180580380b078040703c0320654100050a036250301402048510100b44c80c86500c80c540e1090540782d84820355810240e0484c00340c10384400c10b05104100b5558030b0364001494006c409012075520040c9003c0d8502110035000d95030301c56038980300740c2001d9020b000c035a0510005840102e42c0c02c020340350403821546440004054030300e003ca0070400406105500c25048280d000c11201e0300441d189030340d080b15600710356090b844181c0c0c40ba0303542d44ca00140101400b429079a003d9138800c078010a070810030380b992158030125008016a181002c0701c0e49403800d84001d001000c2d00601040d484040400c4090981c1c94100d0f1040c0000c0e03d5044400c4c00100344584141315a82c02c202d0a03405c5a08080000000405444910000b101d600310071000595481c40e1151292815200243e00c0c0c1100c1c3c400540f0703e161003104101907400030300d4100340d5103030b200050b1080d64103c014081030054010880d10010002d9100c4144c142c0140010012461340581100d0b080380c002380d841 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 65206666 1250 65205416 65205419
    0xf071d2419020d050a0e061c0203150103060b0909060111030c060609010806040c0b090a1802090a050d05030702040507050702030f0d08090111030408130b0d050a0f020403081903060b0d060f 83
    0x490f11840c3c0086000046541403003125481c6100700000039103403001038281b44c03905138942d00d001c46012048400b0705074203400100708226113040d61a00b10350701c0400c0c00e040c07200a084c0701042c46079001e050410ba005042ca20b00003070f5030347e01c50403031030001c0f1101c03205a80e9503614813100b043c0c850304101c40c0680101281000003c040300c0009280b0b00c00d5802c01c08400003d8244202001c09501c0080160742c0600c5c0b028010a80d51842140c50b03403504500300780142e507440715109201540541c1e078045803054040d4404807001c10004001c503840954103c400080a607100701e07064400b80100a4080d41520a107014039003040310000324000c0d00020b0381c603440031315603030521807500781c4507011f0000841700d00600100e4002581440600030382c00e10a4164103005482d490401402d411104810440e40d403100113112841713409102c1d24501d40c603014803c1d0303d41403c5481d81005841a0440c0d04003240240c0d26521110784242c0c80040a03000301d04046582d40d02c1c000020000d030803107010306810003058030300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 65207916 1250 65206666 65206717
    0xc030c2103040f030e060d0615180e0406020f0d0203090f010501080d0e03030c1c0905030c090103081c061e05030105070c020d06060b071a0f071d24 65
    0x200d0051204880006460356a075680c5084100001800460038080851041368465540030050220348041c100000344003850280c03001d210359000d816600a0010095484e08203c2000c1050b0050f40c20005030403c90391550b10380700c40248680f000710900040040741020b00d002030f035001180100700e600c04130744110501c0c0005034202d070820b1050900c158441c1512000207406084c20341d41c940d900405a90502d1002c61060b4189991150340314002c100e800501003d00d03030440c503410041c0c81e0a9000f0245100d100d80418252081030102400001010807510310420813143d145011030010a03003072110550390402e045420034482c1d000702c110769014201080a0905114451090005558244403c1c0140d004c0c440300040040041d5001c548944005c1500c00c41c410080070381c103100354581a00d1100c10200b0603c01c500c05040d007001280900f040c4040143d21129114001c2840c144170300c5c00602141c0000e01c0d0100410014224800c2d00706144e0880c0b0045000d801004242d54048001004408 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 65209166 1250 65207916 65207953
    0xa020d030c031205091f021903050103050f0703050c1203070203070602060105130209060304030810120503130819150605030601120c08120a12110d091101030207020d06020306150c030c 81
    0x440c03085c182d6002c84084e4020036003402c900d903480c40010000520f0180780800c0401640358002c58100440e8445004108000d03080020062203641840946503140c00d542d11183c54010840c2c400384210001c040c0105145814012108400c0e0300404490319996505070107034856900340300300c52150355845141800484940200c512666004000614644d640c0d5401d44800344094882c0d01011762241004c1a40d4041c100300e140d02074021030040d80c882d511040a00485d4149030800c000f0b0390441480f6000c580c204901017814241d2140720100001403a00c6094003c01c1a5403042e5458401c08000181c5102c403440444030241c0902c20354010140c603500c0c200da441980903080c05d2131a0b41003000401035403151070400c0e0302c50180d800214542158078101a00c9400c848001459965210413620401403a060b1500c54106c003800e0550404400780c0015118017005040503050540000000700b195940600601032500f4a520701034464001c0d001c8192740c3e030800c0c3e040d2622171041c00028141c1a031100d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 65210416 1250 65209166 65209171
    0xb071103160b1003050f0703050c10020c3f07320310020d02030f0106020c030d03020c03130b0403060c09030f0602090d0b191802031c020a020d030c031205 68
    0x402010114115952800381a0b4000c200301050300049501000143c1c062048078900c1c100311008003401c500390305016091041c04402e89201e14000c4006600c1c440c0c01142e502c0500508031342e03040d1112400000440108032440c4480a103d000c9640e003010440c01c1e01c07100032118100c10480309a280c8814405428124103d000700c20300e00d841d00c038500c0c0500805030740c8041d120050159028031154181440907038000c1c0000b4090070307401108200b43d101103900610f0043c1842d10082400100c0034004c030703460307000780300300358003019000580702c00c1000c8108200c0302007010040700d03508415540c00605c1c0781508107000440300c660620040c0d01c543c52082410005482c2c0190030818a54600d1b92280029407000c1401a0400c1083c241000070030b26000c9241e01c90591100e01407501061800f0f104116030401030907004114a1000031005030f10000f40c0c41d18500e201c440201d00411003400c0507860310800300802580030b9040454902055403011525020900c2600c1d0348410250860201080d641c04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 65211666 1250 65210416 65210437
    0x105120618010f0f020702010e0406051e032803120510050d020315010b090f011b020105070c0b0a0507030f0f0c0303020a03110c0705030f1501060311160b071103 71
    0xc4011038451404410785030150000100001160b400029401d070640f05541e1030400c011390f000c11140195608512411741801d01164100902801c1000155070340220242c6480706030740ca42c819007020f88042103152402100c02400014918200d1055040071203400000c40c0022601c98007503403001c0540c010705004038281d40f00c02e41c09038104800c0c0814049115020380c1d06104913514030b0038854010700d02c98040d00c4c01ca602c46540b542400144020000f010511604010f928840d440c1881440e00052092903070920b45103503550003505040300480101d40006200010005240c00b0300f5800000500180d442a100c04100e0078050301e0641d04400b01d800c80d4004103031103d8450300002e00c2540206003000740c40c14000354607080c0040b1720703405422a050005041d409808144100c0c5010400c0e100ca03c072800c40244446d090815900d80001018481e04041c540c45400d040481041e910958900c054403006801e074000c0103046c8070122000c165011800f188003c00700c220755400100031102c2a421 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 65212916 1250 65211666 65211673
    0x109060812030727150809010c020c0102060c130e09010e0c1f08070504150908011b1b02010c060e0a0215040f061209061107050c0415090506010c060c020f06010512 72
    0x1006451000101c15051383c109040200072400c00050754a04111504980e190303150751812840c074a003142c036155000c2081d0761060701d403034a26aa00013a080e502061540c56aa2112400c54001c00e0004140e0001d6050002440412034020b505512202e55107022208030342484000d50700f0b0210324a00c00c200c548003104d0303800c1c00755030310780c0a800c83c80c1d0012490710b80646400da496511180c60b17840440e0b0b80000075510b00040203802001d001e1401c600c1c400b2040103440300017001e8044c118141c00d40d2144070096a1041c284196030080080248080d0481c505202e03401184203000d8070341c0b80c0704c00d04911480707159121b02e0403500011700b80c0e82610304408401d4003031410098240c601e002c40410030707481d140c1c445150030001860307801440d0a00715002e44058035003059240107814400040e401901aa1800c0134441503942440c00300011a01000310009140d12400e0040b00d031301e260003001818203030412006c0d0720f00960001e00000704006000548082307988500030031150711180501202a6031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 65214166 1250 65212916 65212937
    0x150c0301060e0616050d0207030302210301030212030d06060801170a03050904151805091e0c01030209061e18030604080316020a0b0c030a05010504020c060411040e01020301090608120307 82
    0x103100e4014284080380048002c5464916a9a5851b0440c040d4003080140c000880c10010580c041013400e10f0401e2260341100c0c04042c802c203080a9020520000c0d00c9286002115800001c0c14000c440340b07408003110030f110260b280d03100942451800e00c6605900c0407406003800046d940030440003003e690550f80c040c5010444c8003004040e006240c80c000c20a40010400a000200440350b003485940302940800d181c50082811401d2044406500031130a036280d078904190340b4040385078882ea0000342401a01d42d9203820114210f40500120320300301e030140d540e121621000183c041c201100c09441c00242400921083c15140c01c41940c00906910050020600c108100316200ba206011441144c2e00440592070712800400141d86120448100109101280c3d038140585805050142d4055150843c0e01526560361480144050080300c91900032840540d141e1708043e0a0280c141d009640703c1d41c5aa8030308004008501c82e0f0103041c4100064000350720550300c10740e84140450f07280c160485c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 65215416 1250 65214166 65214169
    0x103030305060310020c0a02030115080d0c06020c03030a0b04050106021501030f03030902280b0a2019060501050a0f05130203070519110d0921060b040c02150c0301060e 74
    0xc01c4082c0155525015003848000c0b2505548081e11480d5001d4005011070a00c41c010306084502c0c1003035005c010f101181d804c2c004031000041c0c1c21141038042c9405d102d582040d040500086c0038200c10b01500e40000002e200b0b42c0300240c2c01549040201f11010800b60b60795141c2a40d030b0f507040e10350f080c0448170700d1401000072903640109a201d0302d000e414041746060301170b400950303e041c0c4841071004403540c040007100c04000c56030f40d002c00380511a85440c0707045031389580a0504511142550100308a1482800000750180300410305480003545a0022200a16040d4090142401018050a030710701000488860740d120040032640f002e0900940380094841c000302030350009210100340b140400140000900403803a1007503255541c3e0394284042d0780400700c5800e060404080b28200480b4000c1408070542c03903081125682d060303a000010524080c50200f01800111044503800b0b403038507500107602030b00820102d040464940d00d0b20200d590b200318602e0b49020a000350710015541c5820301006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 65216666 1250 65215416 65215421
    0x7020703080d0608060705030a05010f0b1218071502100c2c090408070201030f0510060f0915020303010503070909050a0b04021201060f090c05040e06060f19080103030f030e0601030303 81
    0x2d45a840c6400301d21540c55607041494100c0540750307000050000820030000212920420f4050729000b02c00d0020356207042c01c00d8040e40148cc050078440003e0101003a0b03a07110403039480b0768945a52060fa128540d581d07010b0341c0928024070403e80035000340056010118a070f449800b084521a8841100c1411010301c0c4110214107203e600f40300060980421000741c4c0c82501c4c20b03209500c0307a60820342d2081640300040684200e21100b07003640d4189424040100b00740100b09082d2201c0d8608007401c810f107680122550340059002c200e8414410410020742e5a005c40110306842e82501140c0080b503540501000700e07000580050100e07004848658005941c0703e0394a80c0040c0000c0040d901c41001c1c0c10f40030b00b10b90301342d44141c043e2400c0301000c100c07403103041c01011005521400c11504103031406509120050300148018401e04000071164008403110040e245202c45142c000345104c80828405801858280419004210318484004590348030340900c014035141403029251a910350b9509401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 65217916 1250 65216666 65216677
    0x7060c0b01260102040b1b150408030a0b0d060501140d050703031b021306030203060a0b0609060306061303030216170309130e0102070c0e0a050c0a0f020106090c020a0213050702070308 81
    0x1c0b50040714010b030000400900181018001d030901d01c2c0c0e9141c15030310107114407107025612110079411880307041c045a01d125850b507500680045c2120340d41da590503080b8005185030381d031043d8010482d00910701400066403005040c1d8610308100900703407a03007108001000d000c141d0014a1548681030038400648200045594080340080d03543c0880fa0950005808800f400185400c15681c0c11041055250800903540c021810000c10460180300c0c0c4049000b03807103805615030240c100080842c2450b00c840048400c0c1a45055804250b2520ba00c0c00a4460b071113060b501100101e8840046000441030480920445030700b8020741c54108180140b00c0c80c21001406088195540d031128403601c0c2c001e00060928511500880c80d00b04d0420114922004002d829401c07500d241504003c500d00300001151131200180c100030b541900c40040c100d0141c03440e41c12aa45d40c0f8140032a083c40285c001480103078061003151045604410300101204980003100d044005a100000030030104081000410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 65219166 1250 65217916 65217959
    0xf060d0917040611120a021b061e030f010801020f07020108070e030f0d02070902040e22020a1d0a0c08060f0d0605070c1e0c06030e03090d110307060c0b01 68
    0x8010340c56401c1c0d031150380d0030540c06240070a485007556014030b64140b001c0c2403440b0340f2518550070441c40000c000d50b2043c4103003c84a254800110101c40342d40c45100340c900d01080199400d80700c02551207000000d8105462020840c0442800400c0007070707060007510f0507918403c5400341021415001161700c4030f00030f85410b040c0700501001400b162020310440742d06058010041425411203c00203141030015402408580d10500c02407258a40120380660031030100322846445003c0e00c0075902c4031450100000754004800303800010705d900c004031b51146c224800303900b64400d03a0754000700c45c06481202d00014001510700f0005501441d0100382a5207040c0060500040000340f6561641200c1060341c4040218000310780640800c0484c6008000940030740045656130302a6640c2c0c0d441401e05405030006058949511f24401c580c04c0060707070900c800c02800c011481032181810f40c50749001a4503140603018013440400c5031801804c1141c0565030254044070507030b183c0039050700d000205000b200e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 65220416 1250 65219166 65219183
    0xd0809011209031d0f060406030506011b03080727151803050c030c030a0308010e04060902060a031517100f0e1c09090501062007080709020304020f0f060d09 69
    0x30019900c181c49110041071082d29400342d00744000410581506080506174803d04000c10b040403a600e07000c1c01e440c2140e03a41e040106450b1180b80050311054000115000b03c9094060050b040c5a03000200902508454864a0b0030302c80f80d514820749203400e101d214819064611080219240f00209155103d14500e4070880195aa80c05800c40d03e0380c0c0e81c0147c0d055400070051460302d180600481c2c0d0160411001002800f00e1170703902074000c001c144550050007030901c0014050007201c1d0405100c4950003040d180da2040641400b03002082d00302450860a401e40c4000700e10030075491032148030546d1352001402200601240c4a02404040300400c43c12074595142d228022400c00024000d00740840c40ca4000150342440240030060549c40390001c54244001080881e801403e02d0070000070200250310001007031007045242c0700180e484580c0c1c1d8441c03800b0000c0c21155981c00b41d80114401c6840e0b50350201d590003080350303010120301d00690105d410480325140c901c05603c00040c0078400c440706c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 65221666 1250 65220416 65220437
    0xb090124031107150b0d120305150406080d020c1c0813031403040905070c1a0405070320130603020f060c12120601031b02030306060a030e010501120302070807050d080901 75
    0x102c0b00d0070f4014001c100d8141280d941d000843c40503502590080d00c0094807403000d09911750310391100180329135012805165031800800d0201003d81d03603031003810b5406002406102d41e649440d9a0340c40400c44410010301840f0381102c00c51078640312169800f01c41403034081e01c204407070302c807a4040c0e4491f030a171545440c0f102e04000006004024000044030640001e15102c9141c50340890644000030088410400e0000105000690170006605541c01c12541c229203503403945002450701041f500003415406541c18540041440202800030000d01034a001d050400503418034410b40d00705000083d44440e81180032019400c000002e401000748500c1100c201c03514400040103103a00c500d080040c03c00d0000100101d81d40c02d4018401800081c40389500403c0c0000c000079120b01002c0e0840d84103200010b181e01e012842034210745011540e25008003c0c65a580780244c41c403c41c846000c40241c0200d100004503140702040e4407003201d201802356040442d841ea11202c00b50f02010380301c1d05001c05e0402 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 65222916 1250 65221666 65221691
    0x20d230702040608010506010f09080a030c081b1e030c0601050103050603071203020105100806040c140a0509010803071208130609021f0c05060a090f06050402040b0312030106030b09012403 83
    0xc3d840c010082013000090074180240010019070b2070058003401d202c0e401030204102240040c1b900b20498040c174041e031a500051520100c40d108900c130016401066120200007070f14045290401022a40422609018003003403650312400748005000c4190881c0004014a5000303420a0354401d034024240c4100ea40c9843d84c8984601c0d804c0c4050380143c3d0344904005103041001c039080c025010103001807003d4a80f135602c15280519501890000b5412400255400d03183c040c02e0f0000b410703006108421660711240d58591301e810102c0b050707030440750201c9211040c86c05a640d040c02514142042007000e00c042d21440b001e0014004220b070000c95940c20342880448540030548118150f9641415403951400c240c2d2800501030480d802080c50894220001248a201ea84010341d1180002c2a00d98403800090010000c1f20062505401901a01c69007a00710200550580c0c405172810406030440000f4465541c209010300840c103034021104e4003600d1441c100b0309045104034500800c07030039101070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 65224166 1250 65222916 65222921
    0x509150a020306030c040902030604030c0615060809010c09030f0b040201050f0d0e0d05090f0d020307080601170609010606090308031008070b0c01290607081204030905090601020d23070204 83
    0x69030051425408428882e49203000d0000b007504810445082c007952205400094030f034003010b000201480b0010400100f0401150009a5100240d020102d5040d90b80d4034007034204401120010407079441e2200144075a4040c03404001502d4000c0400d40d01c0700f44e90b81d50034201c000094026814810140005102031182b40010907040b140880013294410b540300c1c055180014250101041c00010f01082c241a00e60042200d4800400c440800c512603903030000c00c0c01c0c045650443c0d42c59008060021075400070401420100000d40c0d01156929511f4130021402c807142c0f4059100041d010050070804980031101464025200020604038150356100f0380b803a04e80160f001808090002c110740300310500a12803074512a1a18140c00085602c40c868407801550160000e031194802140140900890b42e0039a000610601c006010038101070078003070004156442401d200300c1c0d407200018080e510205101710381d41442c1d21004001000c50701c0803007440c1c030303004080c400d0090244002c2e4050794403030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 65225416 1250 65224166 65224171
    0x5010603060302010e030d0509040b0a09050403020106030308010f030507060503040302010b04090302160f05060d15030f0b0a0e0a05060601030b121009030314040503041406040e04060e0106091806050915 89
    0x103880000d1030354554070000d071090200c001001c0c42a00041d4010802c40e401400b25421310b80c0403a0000741c041e60b034100240d04c6c00500c1d0080411546007004010030540c055110205482c003948580441c0d1380d80e0b1a6100c07404c0c082d8007000700150000305040007100c0c06000a1030300b0a102c0c1c0004641328080401180c201d815150040d001030307008070014880c1c800c060b40d60308041d00c6221150b5000d0390a050100d4003510a0030207031035401c1e9075103141028428140300f50001950740500c0000c1c3d030b403c03181011002a0000c2d202e02510300e10b04155555048000180c5000b21944071015010039650034005400078014100b55580007120802204c0010105110b41c61421100190009402d940c2e820010100c40d202064a00f0201c030810520000c984000203071800c580d80c07401001c00085400b004100345008039403003c0240300c0400244410003046802451064011000800c5480c0d034401409003580c2034030542c4203080300300a0414010458039042076a101108404840324100c408201c1e1070016001c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 65226666 1250 65225416 65225429
    0x1030c050d0e060411060403020f06070606180f110322020f030304060804050f0c030604151b02031b0303130b0603150c040f060801050603190b060a020c0a050904050a020d14010501 79
    0x483c040100300904803400d00701501c8141c034114101400d560104917000c00d41c5541030f206481c0864401c003040100d07040000900702c48420304041e80715903080c000140900750355400f41a4100400c00c03600c0c10016045d24402c25105081d5010303203000a66090a4516450050780c100640c1501d80104c0d8400700003c00c010700543d61101034624080c107107242070030111480d0502d107400c001d100200316940055110f42164100c12001e2102c08a04230220090032100c0904410b141070b501080103003500880070b02020359100e5811910901144140ca480307100884590000d54a840340d0040840c501800082c1d10600250445080c0008000ca81ea803900003261011088400020107000b011404081d46004180e10b05003400300394100000030b440c2d400001c080300c01c207100c1c0c082c80702c07901101a0010030414601500d116555410782d1002915690904c031000d0154584400c001800d04081d07078010320172900b15001d00101c002c0d039030030091035a0003110f09813480202c410380817250344000e114642c0207024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 65227916 1250 65226666 65226673
    0xf01170106090509100f02040608040206030c0c1203070f020115090f0e0304030b011505040503030a110a020904050120040305071509180c09050d0c031205070b0109061e06090501030c050d0e 83
    0x60b440080030030b40340c0b1800a1b072101c500510042040e15080130b03589030043e50440d0400d8480c0c0d981b581851355030180b8010000d15115046240004c111010011401104a6654000310302c00161050b400c0e9007852460380e0034034079017a004118000d41d552056065800c5035401085903043c2a801914680060b00140c0d07040c0310803c0100300c140c0c071565a231900c20466041041c2414503140002c2e440740903560100d0700f8810040300054000304180100340c0c0c40c65004003261100c0c00c0c1400d00038000c0101100c05101c144661000909c1312520750141d60480358007a00400e42c49060134051782da00f5841c8000305081c0241300001103004c56001000701041c2e0108080018440901c00004102c80301c150b001c10300641c414920100030445403105c01d01669000400e44542e8405c07032a04488078440c80501900d20044100040340d03a03012900800200c1c0c6041108590384421003070f540548040c94440ca80100f4001701c010485940a030300a841c11105e1404c0c03503410945000c030a130054441c1502e02060581 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 65229166 1250 65227916 65227933
    0x3011104080c1f0203040b0d0207060203070c02040501080c0a03080d110a03090204050c03040b0a1d0a0506090c0a0b0d0f02070204060602010516050c0307020402090d020d0302150703050f01170106090509 89
    0x201480c8085501c803050003c0a04058207110182d100e00c070750300a55440c00c200244116504000b41c0441d540d042d0720160442d62450882d074001c3c1408154507040348128148400010903e400007040c14507003400400c991011851030780d800314030703510949140ca0181d8442114200030910200a40300c0c2d0526601c020920740e116204100407220000c04d100407040040c024440418007900b6500d40c8819001d80000b840c410703004625065080445410700b2511079840c00707808002003c18007901904c0d40f88129240c09894004008218026018842040005000442481d00380c5e400c50300ca104071104005160660540108098902580210b0050303034540b414048010601504211a04414a0550300300719406041580303070310421002034072454000c900c140e0741c0c1c0e070f0f069582845c186d40101048030044080c90043d440710210320300c0060f0403034103400083d4003230f00078094a8806d0f840f10300480381a80c2801e01d2006260241899480550340c0c89801207820885445164040c0300e900c8010006078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 65230416 1250 65229166 65229169
    0x312041109071e05030f01090f090506010b12060402070218041a0c0a0f021b102106150311040e070c050a0c1404020708030609040206070c0f060806010305070c03050903011104080c 79
    0x80820710a03100030020100100189070b005a440c0d11f056035600480882c82d5840c03498200080d0144a4000d0000d010751070000607104000001003a9403546c1c145111641e9a03040c003000200d02075818003070b4202c41c007914403042411030750b10450380c042d105034264010f401a0081c0d4044001c03080b110782c40c00c0d04e13000599411076600850300b02d04030880d510040c0200a0405e1080000303080807c89540601d418070402c2400301c0c0910072600101c91008550388400181d6081080a00a103200310580070021681d052800e61090240c0c02400c401c0e10491442c0c80c3c5865000c0c09003203401005042045020181c0200003001444104003450042074030b00303ca28100b280c1d5071000f01c1241140303842503104014050000b9507400c150790744200115403c01840c0d45d1400131803414070500e0002820713880b8582021075006a12101182520200e40e192601655040c1c015003c40380c00b5175581001c5003280203e240001d00c600000d1072041c001070300100d17004540c13085290790360b04517412560312a001007082114a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 65231666 1250 65230416 65230457
    0x1b0c010806031b12191101080c04030c0e07110a030c0203160806011401140703020304090b1210110c011a10030501032a030804140a0512031204110907 66
    0x1100d0300b20050000640c00d552010804842c4108281c02070340750510758080f00f10148100b800800c20100c061a49002030310303240c00034810240c1110b0214084401240c003d8040005460075240e21242c400300c600e04001da08188840300409650800c03485240510709418284207001c0c50724031a454a01c0b00c2050b6204043c04c1044041d45141501d5a03400c0810400c0000200d44e81190b00c041ea00d808603c0000c00100c806a108a0300e58a00640c00210b03002096030000007001210544c8104100b10040d14081100c0d440d041200702c403041d404a501695002c5a0780e01c0580c0c1000c801200900d042ca40301425401d4403102c0c0b5080c0a40034401c04400c1c4c06081c491104032404c00f1610b0204402d604550354010002c50f521486440c808201c40520b01c5c2031032208040003d1a0030200c9076840b6565504110700342121294554024443c803000000c490415400c24154920707290095420861000843e5011402c0140140d0700b0342d4142d4001040c43d1941c0c0c207298016581680c03040201c42951004a08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 65232916 1250 65231666 65231671
    0x140d02040b0702040e06061008060301060806011205010b010206130b0601020a0213020d06050339030601090203010501021b0a06050a030b18040203150421050c12040906080f0c090c1b0c0108 83
    0x58540101b420000b05d551003114640c0e1514a5042030b44280d280d40c00860700604007600700390700e240b041000100d00b80459412150382e8034483c0c00240596010071004903100c0320700b924603003c094445c0d5501400640306045442e80000184125540010203400040000d4541e1410561041d40001c6003d0405114010391016050035030040440280c1505181c007030040d1180b03440c2c1c4109001708918001502d07140e010301e520000a04490761540c41c0c81551000b540207206580c05440362075400c1c80c0122440584500096000b858075044914240090311194494514601015a640700d640e0342c0d40d41d07001da0428042003041c14540036142503c141031400b15110f11f111401c400320030400000654000c40300e81104500c400941d00340c1400c0300c06480031b00500b0341060340350050440c41a406040c01c00600100e03840c00d07400b44078155450003110b442d00810303041c071075650700519070310840e0341068010700c2c2d08680601c4140b4038040c034041b08000203032402d20140155406c045408074440da4444a44c0b078 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 65234166 1250 65232916 65232941
    0x109050102070311040902060d0c020304140d0b0106030e0109050102070c06030b010903050309360f06010c11120307080a0504091d030d050604060515091002060c030403140d02040b070204 82
    0x740b01400c6480b210035540380a04124469034955503c00f00310b4072241d00b40d4088131802c00b0300344104a0003a20203500ca80082c084c1409034102d160669215103003d005102c1d42c0b64000320040c807140d00703081044000d059502820286c03507494082c401c002807801d200400340c26000d0701c1143c0c00b05007045d800806480b1549441303410041240c0c810310214102004a5a01210450340000000301c6410407401c1750705c044841440c01c06495542c14602400120018866014804105026900c920042d21012080c10300640b4082c100414000341e400c181c0100420011522308880c1803205a6882102d00d9100151090000d10041400c0000c007480c1d0244c0c0281110321810b007000040c400b403081d0351b0f0b805080d01e441211621003001c5585501c55600082c060000034142e028403160384090804258001800d00f40034900141c0100706030752000c21080d010303044600d201441d60700c840c1c4080b50440c01d442c084080349403040240d80b0f003407500c520052000300b15188082d911201c42c0e004100132210440d5002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 65235416 1250 65234166 65234173
    0x8030a09080105090106301a0402040f110a030e0309061c06060e090403030c0903080c03070317100618080303010f0503101401050d08040e0915130305030106120b0306150109050102 79
    0x2030114100d59103041e028001f0b6050705121226568168000c0e084240308050700132101a003c6a0300c68000308603041c800c90081e1400d1091102000341101103440000c2c071654101c2041c400001554826000032450900140c1200c3c14020702c0000140e280c2c0c08030480031042090699045462145801040d004110f1410910043c1c0b043c800070500d040f00080c40107040541c0c455010f039403c0c1c000e12038440590b4003c460a501c82c101145d21960304e501c41c91080d008240301080b0345218007144080c0c2403054000803030f1a40883c1c1390070000e95200030b02d83c1c0c00034030110b074460f0042a16081000914001d0207032117540c030040303480c2409041c04d1400800320042c8003400d00c1d01c1232400c0085406070a044840582c2c07208440c01d440d042400544c0501e030425041e860100303043c40400840020742100c080d2440c0030302215a103440161f05900c5449202c0100400c601b1300c010403440d03000303120340d04008182e0800424011403601c000780c01d14008480582c1c440f144a0f80d032174480e50b841031105001d050280010b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 65236666 1250 65235416 65235419
    0x60717070c05060106110102070f0804140a150503090a0803040303050103110102010c0207053a02010923090604020c0604050703060501060e010c080f070804031103060a02030103031d01020708030a09080105090106 93
    0x405403203c0c070500034032003441003503050340480b04c8096048600b200e80199a94041e19101d103049801e83d8400d205101010786800101c102c54645000c01004891501903000c0d500000460141c0b115003004201180700d01605240802003403c0800842c031481c441d42d00040d41c7d46c1545080b40b50a0400c0f105c01e8110380c1361140e0380e642550001a64020350f107048481c807581d21741d031303650303004158502c801403644508034449500c1055640351032b0005403a100b42c1f50624519101d02807802030802c80ca08081d403004942000c0840c030305001c030740f503604a0b80180015203030001f00c1300001d03e44a4147e404640603401382c0b00400921415100300c2c1d0242c41c0360300d82681500c410070002046420914405480500001202800000408101c814031940401030684132952030812103186030b1950701e124020700415002420102c1315208403816030368146c4440d00c0100b52003680310107a006807004c0343d043d88600c01002c80c030f00d01d042000e40800c08641d51214030700c3d41000120307401d4a102400311440c60703040440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 65237916 1250 65236666 65236673
    0x501090617070c1e1109011202010c06021612020f010f051b03101a0301060908061b0306041e0c090f0308040611010f18050c01020c061c090203060717070c 68
    0x380941081c800d20306000c0702059814100406a044079016441c0740d1311036810800c1040c0500e400719088030403544894035a07030701d8003003410030711482e0002030024071f08402550005450340c1c09004800381d0000c90505060142c0e0741d0744c110070b01c094000c00169020444001e0701c0070003401101000d0001c2e290a0000c0d0400c2d50407500005015501000c5111000c000901d2030031240d242c0400803d0360444842040c10080f01c00d995a074000e0003042d002401030032003c1014140051498098501c0d01855000010411001081a040606580e9100d92519110080d007410080d807507400020004e0001803000e42d18101a022441c02c3d40240d10160912a003000880c5006040c0c80441e0b0080c00c290b5502070f005094140108084200c14903160b1521081200011260305032041240c400c400302c40220900300016640c50001008559101000f000107540c444840350101b40568401c9001142040d034a50002c0d0416a04a0320240040c583c1c034050b481e1001680705468003c2a6800c0003105031440e0749 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 65239166 1250 65237916 65237957
    0xb060f0a060c082503110307030504050d080c060702060106031a1003020306030a061803110c030c061c09060b090601080705030703051005030604030c050c1207031b0e090705010906 79
    0xc156014490042044003d00a10100311032400300042001d80030144086012400d50390340b258194005220b00d00c40071840c4800004940700b0300c6d0581c442c58200340c6854108140e49000c01012100b0074030034000845502d000f04480740c01074249130080d180d00e48c10004010308450405081d080b9000c402001c42072140c4a403003420301051410710b40036a480c0d6a483c00319242204d400c400400f030a24210300c0c0343c0e001c84121080c010091003903907000c0340114107525440d66981e10100703243e850341011269418600d0300400400201c102141c401072060201c0a11204880400c44141c0d03030713030b505c41c40801e84a107020b040407944280709003080c50355810003160003000c1d030200401100501d03a80b080031030560010242100001c040090031201c05240501d4014a05501070a00710344c18802d402c0604243c6c0b070000380b40300456040c00c00034200c140c511303114100026400c046e21610800c078110080350742c040c1340500911441607000140000e030310708000141060141d600107402c0100c02200074002c1d440c00c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 65240416 1250 65239166 65239169
    0x20a03060f09080a02031e0414010f140c0307050c060c060106141201120b070e0d0b0c190f0e03010903120914031c0b0a0602060403110a0c0e01030b060f0a 68
    0x140d0407200c844880010506118003030100c0d0400f190302c2d0b61003035001000342800308000da90019600040a00c0e00c0f020700585c0244016001151400c40030740d44282025150301e58a45060105941d10400c6245154051440e410141c0c000062410501c50104a140582642912014507000f0010b540c2516042d060003135004118801c550700c5140c10301d07079060314811511101e20384403a5a4809001d00c132044000c4084981e54410800110603c0c004c2148891900000d480941d41d2519617461500300103000b000d500b60348000340074907100040010940d2440750181e46500303203610b0098074050202102c41d80f030a84241e042091002c0040c1c2c0c00103c220040b160f60f503011885070018a41840e11030740304081683c0c1488007144000190288840540c0804540750041085d0358285040c81940802c034044d050142c0c0c00b55010800082c45080b120300d11650000c02c5e2801007103d981c0d040d05400f1035034031070420303c44100c005009101d801c441d00e80d00302d401101c1110880300e01d9404586d80c44c025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 65241666 1250 65240416 65240423
    0xb010e040c0b07030504080303010e0708100e06010c0309230910060c020f01030b0d060501050f09010b0f0a090317120601020102071505060402090607060917030f01090b0109091407030b0607020a03 86
    0x1251103c00c040c001c0040c0c03009840b0380c409503078880d0b03141c40d00e020441c04226008000202c540000c1780d03410780b04d00c0d94803055031020500d80045503234050065a00c050810021020015000310004070951001c000b40a007a003540e52100034070003007400304121080c01500d90030a144205604200d07440d0041c54004040d581034817400754022003d40160700400d42641a60b400072083c00c1314000f007006a50040e816123404840217060240400c090001c254024010540012010007030b03150080c1400010f010781d0b18040c9840300c0915100e59882d403040440c034075212110000898159651845011784590000c400e100860070020b19403035211480134001d00842005a480000c20060f403034ad501120b82803180580810ba640000340780c03513002040317100000d8031007411841c0c01c0344106410380d00320381c01101a000ba10380c060b421300103004000c002c070140041c1413000e1380d000010902d0342c40c0244035003126121074030303842072612550203410340700311680080c03003003508000200c01a40e403104650182c0e5007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 65242916 1250 65241666 65241689
    0x190303030b06160f030c0602120604060902091e0604230a050103141807090c020a05060604090201051b0102070209090607080610120b0a0306110a090905130f17040603090b010e040c 79
    0x34182402d03504d01b01c05180c098902400000c039403041c85d204054142c0140425202001955900c00c4a64220701680291769807220f0a0801d1454980d8128504010000010700e01c900e07150baa8500c0c0c402c10040c000400f600200c0030510b0b08182c0c0b03858041c55006081c20300f0248002812021030340841072000341241c202d0300d0000703044580c001c0c04009880103000b01d4402000284842c00000e941c1d50348017842190305104000026407582031600400c0d02165040c0c4840d4102402040031250149125032006620b640c02d00074a805a40e0f4000382901807881c030801b906d082d0401c807100030052540202002e0140070002202c6a0407a0300080f103050a0b00c80c00ca000400e500741d2800550000c4842c0d10181c02c5e00d0a10005090040604000785034420f495240ea105485d910001c0f80140da00484078004501c0c0e80a00c2d00c00440c82039000121040e11400061408100080d5146d030b0582040c1c100f640080c0d615000c220802081c404010f024200b4034054081501c3c00e5514003190384003e0240c10703204030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 65244166 1250 65242916 65242943
    0xb09151002071505072108040f06110a050d14040b130f0c06020f15091b06090a090b010e060306030703060e070305010f020a0e0609100e0f190303030b0616 68
    0x2403003030000e540540500a10340c01d854010f080c1c0144a50821441568451b0a08980390750300c400d0140a10040c10060716513920700c0c1d440751a990030700b89500d2010350b0580d4032009520421441c55006050641203503e880341c940b00514035440c00c5440207030080d0020002e0b1010311000c2800044600d900000e000416078194400d40303440b6001c402c44481c024210781910302c000c600380390040f41419448848a0440b00d10b00f450040011034408113403040001c5821169000c0d40c10328503900f81c00340004019201c1c92074031100c2d40104840300c8487d40501040c0d5950342041380f8640e44a4641044100304440701411810b0500c0041e4544009210081559581d20750ba50b01d5600c081c00b030300c002160044001c0204800c4c85d48600040e41c1300603058000a0303075644000c0d4042c5080300940300c1d050b0303001d0800a00d410140f01d085e108c41080500d05544513448400a2069541d81180100005180407000100614500d800360990f035440029500c519030520684010b031080106461050740c01220800700131 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 65245416 1250 65244166 65244199
    0x6041505130209090309030d090b03040f030e12070501020f070b090f0102071d040b07081312030608011a030c0f100c060f05090d080f1504021308010203010f03060b0915 74
    0x1081d9050000d41010501c004c00840d683c021000d0f00240c1026001e45150005045041f2000c180500031b500300c87c0c406202140104140c50203070010140709080071030308005034000240001c182c071010f4038196800180305008659042c4806600403000000a041041c140002025039004816490b8015141c8a8901c44681e100300205c5004001c000200054044081044404207104550030340b49e0202040100b840140300b08500c0d03100d01f14005c54140400000d03683e080c10f41000042d0b4404060725140f020507040000c2c82000c1580c5012154940c0c007031001405d05007420320801c0c0f40d82c4608810100002c41340c80c1d01c5824511024145004c420365012850308034000c3c0743c04100c0d0042246082c00704816808001800740c031041094880b40d64542c0c80c4020101c9101040300d8068903480301d081c004c541e03400e268000d00b007181d00e1078102403045030f1900720460032038000f40e218076080588803900b041480100d102d8084a0714040d200e262803898910b004e100340e480f03a111b545010f0004c9441b00d2100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 65246666 1250 65245416 65245441
    0x9021801110114011205010b0618060901020109050d03021809070e01050a05041208030f1f091a0d030f08070504030804181b03020301171c0521090303160206041505 72
    0x4590990b02ca0704403540c69a040304940790703011704121050740c0303041d1140c2c0316494164180c906d24080c81e0070741c100202210092144d2a04003e0701941550340b950091130000d1418007007110b0181855500584844141d0380103405030b80309500031307070203070100005201100d540b1410744041d041d03003800c0007940c4124060040710307284940c2c0d001d0380c404461442c000040001d030320001c1d0301a03000d9040b05807550302c0c3c4110b40440080410701c02103902d60070747c0c0100a00b4241d90012012605020102000c00440c040451b00e8010200421400030b0415101782049a8100382e000340c0090203442e002d42094203543c0e821100f0b20460190344442c0b03205080720503011403290402200102d42074040100300f010001c01070083c0d002801990204400ca40e58030f0203090300000d004410074a284041040b001e80c900c0203507066401f001840e042c00109034603090600040005040c081e0350000001c5641e0300d4056070308002c41190314501301c1150088420b200100d80880c1c1e1426440791440d1000403d6200c1d1004500b0303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 65247916 1250 65246666 65246681
    0x706080103080307051e070c03021302030f150301111b070b0a020607080a0b061305010e060c120304110306010621060834030507050a05030109020109090203060612010b070201020106090218011101 86
    0x300c0b590001f00c48040040301c1002104032031083d03400c071844500c4c00941109a0004a9411040c1c11070030340000c1c1000c0701038001d45401300c1c2c00f03000068502c034222400e101c958002d1980302030b010400c5900d014200341c1000058010000d01000600340451034070000d480d044081d01071420003c00d038000c566034101a0344000c41248004016550b00c01c540861a1060050f91080c140850020340b00c8070558102101140d000c80c03c0c0d200601100b44c400e0480403910740000e031041c1c07040c40c002d034031481c007a49080040e640a00255180d000251541070f841e941d104e88136804241045040020070440600005039243c42c5182007268118070101c1030318101a8544000001c419018100c0400006d102010500006032101070380c0740c1d64815101c0c000e041c01c0e01c4a80c4402400142e80c80010011a000f41e80030b1608401c0040a141ca001c04100801c5100d1000b80c014001e43d110000d007180466030244074113401840400da0035400c02000200b2400710515404a10b81801340030792094001100c20341c0280c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 65249166 1250 65247916 65247967
    0x1050a030b210a032a0b0907030b01030f1218030b09100f060e0a0b03070315060b07060c0f0c051b060d020307031509020414010516050f0f070608010308030705 70
    0x54001c2e21400c6200d0340ca907030700785080c0c0c0030441c0040c075001c00d09603404210952240400e04000040084e59408418980080500a25000d84800400069841c51100d8000d40c098814000300082c0e40c01c142c0880041018000d0611a201c1100c0c45100345003904082140d0b0010068a403aa94050042d4107080f059540c9220003840d043c005d01300c1004990000c0140c50707113000b461902d59901030620040303400c07100c5404d605922280082001a46104200f503103032001800c0030804035500d4070001d105800041080b155151074809940003503612161b08041c01080e031504d400e1210058603115201c90344000d2460b86500103409540094885004582d5098810f980171990307032418642c0200189500320206d01c512210403000151114240259030949100120a000d403102d80801035460703034803916040f0a444205900000030400500c144410712001d54090829054800c3c2014100390441d00041d003030114000042c4045080d28050302d5119a582c18160383e9074403004c2d0319000c1c0091071031192 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 65250416 1250 65249166 65249209
    0xa080309090f07050c250605070f1412040e060f0108060901050603091501170613030906030b040e011803032d1a090c071511071106040b0d02030f01050a030201050a030b 74
    0x100703009440803d0f013640031009a001a140c1d5500c40008907480e1140d2740015180d00025004100811329900c406070f40306d404441140c40a00e052081099150082e900c1100040400801c000300d500780307000a201049001d00e080d511030300d00340001408141e818080c06002c0c0c4070120000f1886a010802070601c003460400c83d900035a900c0ba008680c4144c035660405103405090042a9942000021000c2945e49a20745603651070074008118001c101107000c1c1c541c440c1c1c4030440001c02100038405d000e90040d0306003c02d010f034891814050181d403415a8202da80701019003110000d80250002c4140d021034482d400f0441101e01540300000b4046103408580c0f0000c29014410880d01c0000140001480f078246880703144481d0311910100c5042400d1500b02200401c40480002c1e11504c0c0c494014100404040c10035031110f0120045820040302140e04941c0001440422031803c10707101d005200c21140d40311147c0c11540000c0260084a1205092644580545500c0c0d5960040010340e0103c07007808 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 65251666 1250 65250416 65250433
    0x910020403210305040201021b1503010e0609061504090b0d060203090304031e020d0f03140c0c0a0e0408160609020301230708010506160302010e0a0f020a080309090f07050c 76
    0x750b00281c2d10403460385808500c003191a001406030040c2d038807498058000d02960070340a40c0603100f44840300250f65000d480300003206240058003002c0c60191400c2c0036a8551440c01b0700030301100800180945214088241e5656064a045800c0b58184c5090800106a416000d000b040b8240d07403664008102c40d002004202465900101420407a0b0145080410198a902e25800c40660b142c2c80030b5003101d03031080c0d0600450318a01c58008100e2107803520120001d26040401d00c4c1740c02c810501c07071803500b244201c03d0591610030200006040110400d076600e050603a901e00281c81821203a0589032010400f080501c0f000382d020f80f141c15000b0b4003c2c04240800c0d07a141a82c07421f50107203011603210f80c50214813140c0c4244810390594501034a00d03494850464a01051400a140200c08542d00c41d11810b4041d4428003a0480e41482840707040b200d00740920401c401c5447e15040107130194818802407606540c0c0e19030903604000745090350038150300c5c0c07004101d4007442180c5c840c40007441100c69 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 65252916 1250 65251666 65251673
    0x403030e09180304060503180a03020f100e0601060e0a0803070501090605010e0601020705011b06110a030c0503220201170f100f0b090f0d140706030609060b0d050910020403 76
    0x1114103080800c4410301816603030708840316011440400010180d41c4240024404036015500640d00304040340428040101d4415140b458440490000c800680041c50003d100050800000b8001030000c2d0b014011120321201d035560b124414801c00041100030800d0000c5030b141c1d510b2040203040e02c14196569013180d824264007900003480112100761504e000020b2802900c0302d4507000b80380503405031880a182074011642010901e13916003c140307000b11000d001884e588603151b0303888009401d03540c442500c002c024049561980700001404400c0080041c80071945851141c0090484000042000c1500040391600c004000fa4240c110802c8207000a9001c0141c1c5144100490f840d03841807244c81e4451400000d14600c02c0c251b4070308081c8403000d02c80c5400180e140c0760320400390074950310711910384036010310b0000440310341e547ea04010003c1c06155814003840000d803d80b81410b1000390b242070b2034801180f05000c1d80c4500c090341e8401244028000b07001c00043c1d050034400541d142d40d168207 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 65254166 1250 65252916 65252927
    0xf060f06070c0807090c050702041a0a030c0810090f0b07051207031b0e0121140f19060f0e1504060b04170706080f0c07021c0605090a0503030c1e040303 67
    0xf815140303104e83c94002070401c1c0b02d0700442e4040882c42d56000c0c00c22059500740030140030003c00e41444020000c02c01d00b8140c85510300b18000314001e901c5206168035100712182031204614181c2e48540c280350304040880d0010810b41c03083c0f0b50000c0100c54a82d50705104641341d009100010003201040000c0c40482685030300070701c035210355040c515070100500c803205442c500c80861410340814140000d100195240110020b420100c0e2000890700704044030006107440d40841703044060180c0c0006118401a0030b4800140f841980c3d0001c0090071304104442c8180368651140d070b0100d5800400152100303c2d401e10241459101a00500901da100d50160501da04503024120242d415030400e0100f08c0030004448044a01a844843d42e50b01c80820011000c64020062003c46c10b0400a1030010780b078190810441690007001071701d03000e0322440e1070010307a4005820308142c0e42c8085c4492010540100407240c010f03d502c0d851696800c65080d0340d10a01c0b24081c00040d0f20031740820000300745134002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 65255416 1250 65254166 65254169
    0x1603030506031501030c0909140607080103030909020a1202090f03060108100e011116030c08030709091812030c0e0306090114010501090b0a0e0607020d0f03020c0105120f060f06070c 80
    0x8030b003515416440001d0f04091858240302c013611414440c0c1007041a00041d500000c4114021211000030030756200c181e03850b200040c1c45400001d8100c000400034180c1c000e60304006804a408207524002e400740c0002d041000c0c03007200a1245500281c002c0d902d5076007021104d413249000d03041d508150382d14400c842d00e03010a040d25400e40303420420800c1242006100d0a0981544940c04c41c2c02c049454a1030390000c88200c00440c184a00024048013141e200301c0034500c00c010941d5107681140c1800107810a0307030220956003000e1120a000d0100080d10142030383c82d0140c286c68000351a00d0880c2d0100e624664200e000f94140c00bc100c14442d590506400190341151030300c1d0f0700c8040da40d0760030044070004823034030555200600a2104603100ca00c2903201d0819041b00500242c1080160340004541c3d080ea000111f070b00a00341c1c40c00c60101034040c810582c201a090070000c4c100103c0500b0940d107400e00030882480024181c00203034070750303035800584c180075080a814a0780740c526a02e0f00441c0d0720b906 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 65256666 1250 65255416 65255419
    0x1401050402030c010905012307081b0c06120403080c040b0a0302090307080606030703030804030e04020c21090d150e0a050304080106080a03052b1a0a090203040203061b1603030506 79
    0x281034603c4641e5009100070821540c041c0c1d01c00c0e904804e0500d00c4070300709201211400c0101002c201500104032608064010311458a01c1e041d503119402e4889490401d038072090b01e015005c1400030310713070030f64140d65429449609410702d80104d40c2d4544215105210b5030700031a105074004500741c9011a0302d40e001c0d0060010540c100e0341056118595690746280844140b9403513802400140300080c821107105400c288a81080810301240000007020f98204506031201a4405401c155250b59000041320b04002e103903440030b24000d640c202098243c240300501a11030303090300c0c0c5446082030580d44110550840380c41641c084c0d00103032508a84031b40c400d00c070305146503003030100108070200041070360080d055154072074624140b0f400d2000c007103d07603201400b644558954441c5042c0c5480c2c40c020358034a1080544c04506040f2101d0400c030302180c40e40c01034000c19205204000060300e0018042c1d8002c4511101d9071196402c400182c1d14038445d104001d0303c0d0316002010f4404043d010b8000901a200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 65257916 1250 65256666 65256673
    0x5090a0e090a030c0f0b04030e01032003060118030206030a1b022a0f09090102030a140105030a260705010c0306080105070801030b07020708010e0303061f0f08060d140105040203 78
    0x40e500080345920300241c8101d0910341103412840006070007807a20b03c2100d80315503190303251241e280d01c46804102040742c0541c0881c040710411010f40d0b0341446405960012140c54032200300c8103000054003400001d02c810f0501c450305611580c1e040c060944040115401018980d0701e20305841c0c1400603160611039000203402c43c41d0f40728000c0740046502683d504a41c12250414001a0800041345034105c40d42c90b000300c9580d040c10b08540390050024400c0310400c00140c0e81c1d0a041a00300c048600e0215010210381e041001400940d0b404030b04000f02c039801c1121540f0700b1202031210310300b64211070710b0000890800101c2000704a0f040d08081a4000b180d103080103c20341d5956100d01f620f008580fa080042c0e01c0c8e00c010f200040903442c02c280c1002c014411a41403e4586000c9806c54051900c04641903001004100c09031401442c008280022203100f40354100c52071102400c1000c071103000c50184101240006c1c1e09071140d0104490b1035400100e200b42c3c001404c140315000b80010b5030140e02a01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 65259166 1250 65257916 65257919
    0x109030b09010b1206010b0706020d020f0703020c1c02030606040507050415021005070c151a060d020d0608030901090b0f0d110c0d0305060d031b080a02060709050103111c060902030705090a 83
    0x20310220b00345041f24004c0c00c00c02c1c504082e40d1341d000c0007980000101c84600d5802e0113506d02c1c99209001600000344260002c01d100c0d00f0315030404c0b1240880c02e1043d0419582ca0a074a00140c50100d112504404141c03000b040a448a040581d594000c5e90800d0386448102030398441115800540d0204541c40550b0400051302c40c208110b0380035101240151100c4c036690420b0310b09a096510104070b101c1e0b03510a03032141c01e5420b000a4003c1c5d0200240c010169008180820510028400c050040210000640c6040c034000000b0b0094a0240709400103090041240300300c0181da24100c0d89152040c41e0f041101590990101801d0740144264404606c50f01002c4002d0074003c0c07280c6401030400521040840015650407a00d5012211503114102c5a8038030210010b40010041e110a441039005040e02d4942402c00400c8240c256000c541090b00f400703c3c1b03583e4141d16000710b601c01c80c07140407400882240940400e0140103154048001c0900c00010840c0f80340d4044040d0400c1031044403000f0546 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 65260416 1250 65259166 65259199
    0x5070c08010e33011203020705030d0e1e090601080907180903081003110415030b0c0712020c0f1509030a08270f04150f030809090906090703030e0109030b09010b 71
    0x10300061031112002c0d51001484605c1c441c02e601c04141e03100f44101c907207658658003c64200702800c072020010516229407402d0525107101c1e01450220003c0c403280c18070009d01c0005912a5000e8030711414018003501084482c1403e001c0310003c2e007020000401010140070030440141000d08088e0b00007a1200c002c10840241c0340d9400c41241e030002d440c2c800c074036039201c00c00c002442070b210307140506440000000001408001c07140d01c107422010030302d0303160011402c0070842500701900b15011504400804686a95019044001c2c21400c0d500e055802804001c01e000ca40302d11108590306201e140468800c10070342078001c0a081442c003040e0b05941c00e4200d6034800080502c844c03594000c190103101c4000342059404000d1350b184108100c1e02859854259051820140e00152036628001403115428281342c0c0a441e0003c00200c024103903403a0000d5201d8a0f514a80070040c20020303140304c1031580c0ea1044412a000d50f0b044801c0040d40c0c02c20040341c900915055a440780600112307034000210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 65261666 1250 65260416 65260483
    0xa090503060f04120201021303080a03050c04120609020109052206080d05190504031e02010905060c1902041b0305041403031e070c0606031a090601120305070c08010e 73
    0x1440c066210b21030300d500c0e2591540c40f62491480c0c40d0b000c565003800300344916486d0307465000007180030b01842c6a41d0311284600809603032000f0462902c1c0c0307904000810030600181c20141c0e1058001d040090480b41c1480120f9011a076907008541c0a85521203201a60b15a0702c0c42c1418000040c004201d015074a07039000d900c9056562600740450800d10001c00d41c1c000f22405030680070030621307119161540703d541c1c481c0103040703508801c500c4001d14180c84045581103184000a49000c071051824000c940e40c4c92551440e121005218800060308160110340301d540000303004a13a2440b080401c0c0002e00f000030002e060448054039000240c0200c6040000c010084901a207030044802d81511030b801c3c00f4400500c0054070000c10000030042d84808500248540000346201c1d90310b140c800c07c1c3d0005540302d048c002512003820364111a0042203058004040248160b615050072512000e07079082610b480d45056015406d5542441042804d402e030125015203400326001814031241c8550b42c11484 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 65262916 1250 65261666 65261671
    0x40507030c0c020913050d020a0302070602120403060f060b0d090c090213050d08120106171005100e010e0904050a0b070806211c110705030c0f0d0f0501020c030a09050306 75
    0x30905402c41c0300098280180300c583c0c40b030300e1040c900800c05002e9540302d1903c40c034030722060016081001940d08040d410f00240004103200c0c030040000e96170070300031074000d07220303500c0010f1015960710401c503004201b0b500014000d0007801e1601d07446d0134440ea0554098403102408450300007a0701c0c3c0100d8240054801c0d200c41c4480312000c0e84108e0306010510030b88207803810043d00c1d81c4106000484801d50f0aa80c01800f03040541c0e16080d140781003207091034103200003521354011030242000a0181d91180d121101d001940c5140900c0318918070001030f640b0704440c88070380740c02440c21070400c0700780440000d00d0400148280800141580d410304c04550100e42920503540c0302c0303031b03200242c4240d07209078040e1450302082d581902d060f0421040e01c82a4403c01d45861404254101c2440c190000309120150003000b00b41d003c0c050440f0503000044821001c24665442000d41160781d5042c4284094504a100e5104000715603445a0b02c0c80a996034106082c0032000860080c0081468140455a1130 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 65264166 1250 65262916 65262941
    0xe0106030804060210140c03090703060903170c120a0b120f030a1701030c050d060b060c010501060809030717030907080303010b032703030f09190b010503120c0706210609020904050703 81
    0x503191600c2c08041052381c0090040c1d4400d110b00d400c0031003c41d1b1381d0304c51580c03654407075111808424070020802020341801801000d400310280005603452003d10700c0d0700e50150440c1d00020b00c694102001960441d900755201d4460301c10303440c1990070342d64000014200c00c0e11613101e0b44504842001120740602c42400000c0841b44003190411180c01c2503c0540010381c030a200200340245c601f408a0181d40042c041042d46030744420040008582208280781c20038482406140f8150b0f0648821102e07512566034441d900400100140c0014014005000a030400c1e4082d40d9881d41d540051004940068071081b5445140c03960792620b4061401900700d0082a1002442c2035075101c9a040c0414240149500000c0c000c501c10074130102250154805c11034403410602c1119410081814074242c000d0b400584045010880681107203030004170170341102c03014600525041d01c0c002c0301c0700c8520400e95125548a08201d800b00705226550040c3c20240d1065a00300115641c0010890070341c1e42900804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 65265416 1250 65264166 65264201
    0x906150e0a060f12120504030206030a0c0f03050c0a210203040305120a061a07030c08040609080c120715050c1c0e0a0303140f1b0303042001020d03020d0e0106030804060210 76
    0xb0300020304020039036140144141003090406580c1e27000300c0d1315684221581c8003901d40d1100c004080580207440401141c002c0d2030100818600740314900c820b407054103416001c2c40380c1c000c1e01000a4421248201010003000c80c255280e00300b82c60050b051380c0140c0011211b900805000031420740c402e100300707411186c001c00c40c1c81c4100d03039203815094940d101000540401c203540c001c010200d6114002440180859610360b00c43c603280c0300d6a141071100e0010418400c0d05185140c44000d0320000e00007091f2010b181030300c4105168030030251500c2c4622240d0f40400d00a184546010b5104a504000d01d16000d49507622100c401000308564450709001c000c0109021988070b03525507032100060076078283d504914501d000e052191421107810324820001c03030f60340008200300402000303078125200e45070961a0341d1a000910310000c1d4440c200090711908040e4003085c4050005101c0d00509646081d490003007150503160708000d03840350b01600407000036114800310b0b1000c0000740e00c1211000602c070685c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 65266666 1250 65265416 65265449
    0x2100c0b0a02160c0314010f0209090711100501080c0a0e1b0f0c010203100f0e0405030f030c04030f030c0204050c0a020a020d03020c031501050f0103020702010509040906150e0a060f 80
    0xc0d000200c0007400c0d0043d40440e10700056101c41004040d41c018240c00c0315841c414085142036400c0b2005202140b401841b5485d4540ca484060b140c2008207810b05820000c1c444080524002e0b2007410442081e04010000400e4400031840390044071702590540726441d2600010f102e180410380f02c400d42c40203191003005c0629109805004a1b00c0d00300312091a22a00100381400d980040d00c10103c005502c400401c50305d0042d05800c0010012000820dc551902c1d4035440d84900070103050010a801c004000380d0f0200d510001c80300916488103503000801101c3c100244460320b2200200d010781d207000302049032041840c0c10b450700704905500500307281c4110341c00c1c402c0140541c40210301354816803824007100e07078041c0120103007040d00307540c020f580f50301d00f00800140180004840b4181441009841d0150b40e0100454558180c1039401050200c4949006002041e05403041220940c81000c0494801011490a40140c001a50601c55035444500051090100d441845094641d1102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 65267916 1250 65266666 65266681
    0x1060228020d0816050c0a050f1e04020403060c0e01030c0201050108120c210307020114010b040306020306030a0204020406110f010b03060103030f050d110912010b130f0603080a020a02100c0b 84
    0x881041161180300250b050135021310310b042003200e094000302d896030448040390085e420280c0310303a4000c01e03003110b110b980d24080303e01050070000c101c0c0d00c510810100711200e03605a240da40480b0001d5500400420401c3d500c403400400034607105074100d000a04200c0501c224910501480741641c54620142c40300c084c40d8600310006a1010b1109a406e00500361001c10322101280301c0c0320328100e110001d1395a460180740080c219610b44038200d103a200100010703c5141b0740382051387c0951b070b4032080041e969103500000a240030f1b08103c0081d4085e000181c0441d01c1790b408401c5000116403041150720301603800b0303070181c280c4088203101c5070141c0c030905c010400b0030b201e11003011706083c841c24103074130740055900303020305580054071880d00a107000a40110f0030b081a44540b4030400c0b0000013081407281d0500043c03220410741455607883c0d03481e01c0604a1990301c81d4010401540d02c40324a55840040c42c9010307446c2c1c01c1504e8141e10480d00d01d440d81d10520300481e22100700720790203e030030305c070607a82d112 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 65269166 1250 65267916 65267929
    0x6040504050d030209010c0c0609060207090203040804060804050a060f02090a050607020f010e01350a020309070303030b04020918010e0612100504061b1d04110706020a1b06050106022802 82
    0x2485c4a041000c520741000220303801060342c0c0050195981c81003d00c40c100303800039162411a50111468910420401010800d10000d4800b580c11616000106072a10308203e07150962070326001c0d11480c03424040514041803640100602007041d1207440d80b881ea03440c101703c45d50140c0f4602039040b200207a000c0ca01e03903124003040e14000714141045020042c1810320103c0f500700510580c01000403100c0c0f40f89500c05221702c819407090385500158038514041004a4486665110040074142c83d0310a00e000d42d80c1e660141c0710041030107003041c414501da028080f1000c0303c00f03100f900d281100c01c1c00401c2ca2414910540307814510010010700360007048592840c010f040007030080e81d00c0fa80c1c410040c80070b014280000c07100c4050ba03540c4c04280301450f41040075082c1c2e00c06e070b4540c07103249454281018004c040c1c080d540c5494001e0801615030052440541d50b0f0342441d80f1050b5001c1100080a00b08407661380414142c5032305600b1501d260000212591501c0b5420020724000525043e00c17100514144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 65270416 1250 65269166 65269177
    0x4050d020409050a0614062e031b020601050a0b03040812041b090903020f1b130f0903020304060e0d020105030105061b06090c0315010e0c030702010209061602010806040504050d0302 80
    0x2030710000b0022110b4a409040900640e4221140c0392110058513602908044507074000004580c981e42050700d031151440c0b00f000c8103404903801d002c81000c40110ba8005c2c2c1c840d41c0c21030858040075805104000f8000d40350402405007a20408682c5c06c0842c0410100044da4455540310f17075800c1c41c01d1507180c1c0c40f00c6c2c1d0303a00052007102c4150718041010340004105028400501e4003d001003010442850040e0510717a801540c030145070b000440d002d2100300c1e0031941c2e4042d00c00548001844104018040c0301401e54503060800150500b41940c00701603000005004450066852500e0b0410303010400009074003803140a8005403081c4014482c030315102000381803103c1c4040000800005840d9640d04041341205d03200c1c8281c2142c072042409040c00e02021a4aa910141c404090360508180081d0414050a01071740008080700040b0528002d60480c3c2d03501c20010807050725840c0200c10b1418130520460201e001807103401c081601420719010300303400395611201a14080380c20030003c400a4024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 65271666 1250 65270416 65270419
    0x303010305031c180c0e0f06010e010507020612070c020a0906050a0b0f091003020d0f020705060c0c0f0a050105011508100506090406090906020d0e0a050c01180e160206010504060b04050d02 83
    0x10341d0280c03480d60300d20031406404e881c803440c0d400c54a00d01e04004a111001d00400704040d03000303000c0402c0080da9001c0b040d00c1403583c00b400e00310348405107800811454019074a0084894070f519050045603034100003000511442250000742282d00d90801c8015584203100b600d40203020000140700d07641140002c2c00704208a0040329051815030070000f11a500c2c10448a00400e60028000344114000d00500034890100c0c00254508003565890380d03a600b10081c880c202c1e0180105125078041402d0107000b15000c0003a007103940c0e50109081c0a4001c00d400e1240c0c0607039032600c3ca00c011816000d01085481489000206041c00f49014284400741d401040c005600c981d41e000e021854184500c51070300114002d1100680b900300c0580c01d91b0455512600b00a22a448078041c05c0004400040d03110410f8820b103821800c00007095400c0c1141c01c56078002c1084003d8003810410012140710030308000120b594222507950740e803001804115219401900ea80d0f441c1084280b1041c1400303103029082920 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 65272916 1250 65271666 65271671
    0x41a0318030315040605010201060602100b06040f08010507030507091202040905100903050d0506011b08070804120f02040b1903060509070308220b090609010e010309050303070903050f0303010305031c 88
    0xc5008281194030445400e00181c0d03810310021880e003040d1103248043c001c02c0c00208445400c054020b9903980c110350208000a458280b44d10345074407440140d80003404481940441070b901c1e583c6060203841c0231a41c02c00020314080000c0d002c548141d1032002140c0d40c1d5030300b080c1c403034526409003c094007542a090b02d0a101d00c0e1810182e5009510a0382070f203500907950540c80d01034100c100010760740068806810031000240c20b00f10000c161403da078410b170740080c00316900e002c2490303c1903060007982c0c030404548082c606600c3c18810b02943e81106144216020001405504104054590308443c12001050b12003c14000640a60f001030f410540c1d40b411200d4203503481c2d60b0001700364003052039501507405031200400c003840396481010161000d414468140f80042010070b000d070150707001c0340741000064002d89407164003139804528120381210580e9030324940000d026003541c44921044840b84a1029682c00d081c0000c0300b5030f0306030780d03001001d98501280f440000d403100d00340c82d501c0382c2d4855 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 65274166 1250 65272916 65272951
    0x131811070c05040b1807020c0a140105040501180305030f04031a0702060a0c110a030201270827090c0316050c030409090c08070e0109060611060c0a0302070c030b04020306060105041a03 81
    0x110071917002c3d032040700240c0c02002c4001800c002c0c070042031600d600088054507450218045a0381100030b030741c20340e002840c082d10110704c08400044d0380c000e91791003d0070340c0c000001c031002004070400c0184103490050103510580010003411107549003040b100c101c0183c01040100d12100321a410400e4120081e2410202880702c00f44014205815040c2c2140541c1d911041c904004944901d0110352039092806c0315820381c069241c1084510030541400718034442507892800c81a20b440d1701022000c03002d0682c030554900350f22010040e5009032a0298182c240d0591443d0340352055040b650b011030044041e40c01c1914144590000e0829100111221007010402050000d0200414400ad20300c01c554100d1551404a510044070740b070b900000200200d10446a25510001804503000341019990aa1320950550110024012030a0040080120f81000010300a5507070280340580d00842c00e655040c0c0fa03490065a2500c12440340544082c20045490701100f030010180d40c4c403901e003154641b0b921 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 65275416 1250 65274166 65274199
    0x30a150e01051e10080a1b0b07030c020a1211040f111801090b03040305070b0a1d0102092b12020a0c2411070b090303131811070c05040b 60
    0x1204200c40743c3c081c18049800310b269505506014940040552625400003810000f6440c0c5075145660050324810a46804214140c0e00d0201480100b01450310581c07254064a00101400a102c5d000d0384104070602000c10307240d03420240e0b1008654028002c3c8082c80b07194080c000070782014aa4004150307542c0c1c60520881032418011315441c95210200303c4400950b200140040401d43c100d901c002c03c00b0300411001a4221045844040d088210012560f4402c01040081c0c0a07145816800480c040c11801c03011070150041d003078041c81201c00402d078140400b1001c0414080010f200d411201324032202000c0740d0581c100300030103400d510640c4c0403003840340ca54880d50301e00c680c01681c084100d614180c520141c59010b004502007145458403110802c1e00c10190380e41c40c9401a00e416500001d107181441d03404004a40c000c00c480304120b03c0f03407540c1e100028a1101e00303c10035110306007401a4078042000c0c0c481101c4003983c1c40014903e00c241003505000c018042140d00a41101030408003e0b202c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 65276666 1250 65275416 65275421
    0xf1d040203070801210305070b042d03030b0613030201110307081303230d0f020a0f03050301080607030219030f0e07030c05010e0105030f010e0c071401060501030c02060402030a150e01 81
    0x70300340d143c95000c0254540b1128250130511960b4591715040802c0000000980c028115101ca6401001c409500c1d190380c00e18226102080681c2c0e00364007403000b01100c41d0003151051107502d60090314100600c0001c4028010b682c4502c440b00d020300f14404009000544c01540100d42c1040420126814001c1550720901550f1062042004d5841004001c00070040c0070f1409803082006001c2c04010200040700315542c2e020350315102c105100000384407040c1d0382c2c400c000c1c02e00601c1d04038562020015031810050f0143d44280511405070058100240e600d60003030007101d44910550300200c1030b00070000012402400d520307031f4100406884a003182100f4108000600245004610303607610315140c60005458042c071008507a05101d0140300300003007410680100e9044603c60307040c02003107941e8030491540c0c5100d1a14020000e0110800140710b802055010009540f02030301c0801400ca1080401da0307480904031802980350b4056010000043e243e00f44404c003091103104041103496909161900703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 65277916 1250 65276666 65276671
    0x2061005060c1018020405060f0a090b040e06040b06010f230a0507051005011e05090c0c120c060f0a0e060711010b0402070302030310090c02070b07020f04140612060105010f1d040203 80
    0x4e1411400c5000309603c1c00d8403517550045000ca071040402030002010580d2840c040c86840d0200f5a1604140019122900812100900d40381655800e00c2c0601d021501c04006440ca180059020b041000c0c45500642c00f59540e420b01003e840c5411038003007503008150b888816020200b000c1407002c41c00040341040b6403004428540801b04142d07043c11340b10003850174603c41c01d000c0d5101c510400c0009890b40460140c005400600f22aa26450b45420510384207007807403110a4210b0001c0e0101c003102c000308500307024181c0c442164601d604c0318841d20013916481e20040c3d43e142c11140214680c04c0c0140b008108031000b000c0046804d0b46010001002ca0b00440d40030380141c0c00000400c8035003502c4880d11000b5140c41141040f0810040900030b503604d006010b140410400058120155500c10168032140c000003030061020311040c3c80f106061100513103c0760b01401c01d030886500c50007004204617041e0346060307603400e41c01841080103e606142190710014000364054681e080c50302e86000862 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 65279166 1250 65277916 65277941
    0xc03280f0210030c030e06100504020c010b0a0e010602060601050702011b020f100537050711030604060207050f010605100509060403051203070207060311040311130515030d02061005060c10 83
    0x90844001d80001d8143d417a0f540f20148071f03400020401c101769500b140d0607001c2e10707000d40e8010782715042c0039015401003030001040361f80903401e03002c0002d18820f815040e90585080e6400c0c0e901d01c1d183d44006440500030340305c009010542140401046178447ca000e410030a000402c0000801041e01c0852642c0c0154003003000010030001c0c0201540324841c41c0c60403200b207030f2304484100d07a0303811405041c9000d1842409040000010341c04091005202044100c000001e06960b400d040910302240213500c001801c8455024a030002c07152a4018820784044070000b81c108807105018100484843d4842c07052598080014403022010400800404501c4143c481c00700756a0b00780307810042d00c0d02442c1d81c880401c160400c540c200c01c40d51150242c0301101d41c01505c0088500b0800001141010b040903200c0000f4a4881000742035886201000c400402c03d43c2a14140f85100808980700c95045031103c0710000d41030410045400c050700180340c814031100554013004000810032099420505c08034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 65280416 1250 65279166 65279171
    0x120c0908011410060f020703060e060604060902090f0913060e010501050906060a050a050702042307031b0215060109050d08040602010609060e06010e040b0307030309080c03280f021003 81
    0x2030100200901c600751004400c0d846075002e500d04124044411411405003004000c90182091840c900800c0344201450744940240241030706071012541d038280860341a0300c124200500010030b1a094401c41e0714005026004014045c0f1300000e0000604003d0042c9e442d6582d20b0502c07034003051043c170500c0c801c0d4649100105d400c0d4580410450810005444148070b100104034421990f40c00808581340c012580c14000d8480030b403800010024044031507003001c1003120400d04401c000100e01907034400c4100791420090408020302c0d6a500314901c000000140e0702c0f900f9240c00d03d000c80040141d10182c145051001e141d2101c011a0401c400d2070b07003c42d10781a001c18144602c03502130203040b000e0919075404001c11031514804c2100c51001034051814003c02d0170306031070683c6854021440000000c2c0c01c0b51a87d1303a680c82c000300950390a00c40c0f580325000303110171074010740380c0804c601c14005a40d42c0380012002072032842078206070102d8800c5a500c5d04041103400140c650041c414070b0902581c400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 65281666 1250 65280416 65280419
    0xd090506180309010c03081b0703030212071d09060402070c300b0f0601020a080a05040503070e0103030203030402061605060f0a05160915030e0106090e0f011103040b0601120c09 78
    0x290300792020810142050340090001481c6039a00c4010401400c4e050300d803d140b941c5030500710300e0911300301424030030f80400c0009520b41031580540043c4440c44055010400320355807101c08a42c42c28002e00300300d029405c290301114140c034260518540022000b0030040c075040b80c1d6074500c20a5001035220700303820f1401000c0b0010307106d503024102c0300030111052043c0c02080a07982d940c01e0010018104000c800814001c1419648200054000c245d07105120075510500c0b2880680103030414450903101c0e20400201282400b074020a480c100c0e40d040d002107066855642c2088407503080301035a600180c0b01c01c114900401c06c200407480c0901030540d4141c81c94200041c444007902e1000b0b04403200700018800030496194802d08201c202c0f00c03c0c000365081612081c034214050202c595030b40c0f0066003044c8022601c03405a034000b8190701c00003000c68130a50601007010f800c0c0c6108100c0e444000b9024000580425500c8500310b511550516011802c04c40710f69520b0f00b15104c008446000407042e003070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 65282916 1250 65281666 65281681
    0xa0309051003051902030a0209030703050606030d030e1207020105070605010306020a0801120215030705090301050c0c070602060714070213050f01031506030b060409021203070503190311070303050403050d090506 93
    0x80041c0c0c40c115071806000e9071810400010b1011562201e40b4180707503000000a01c0d000b43c1e40e058a0304028010141e1300c141b96242403259803401c0650358a4403a00035542c0d2507080710701038030800c1520911000945a0009000310f28411074000c06800d030f042c04400c1010f2000141207104090195100703000040c0c5820340958005d2000e0016000041c664103040d00c00d10260f036600c4100c101d607480340240280d86c0e40c1c401c00c2c110b90350302484c81440d8056003003205021003010303136802500028041030126107407035071340c3e4100300c0c0c1c1c6400685261001c51443c069110f00307031a5003030042070210b001078490403c8842d00000380b0308444040f144900000d01d035800600c01c000700c10002201242e1004001d1102c07604684031440d617000d003e01030521079aa0341036a0310864a03260412900c0c080f014050340e8403002c0500340a0707140c0d444805004000c030915010300007801e02030b11840783d003002e030207654a080001700d40c1c1c15801020040c1045d01403040034084600305148501602d480701d445031000d4005420102c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 65284166 1250 65282916 65282929
    0x4170406110c010f08041104241410200a0812150906010212070204151508060307060e0d06060503060c18030105010605031b070206070c140f130c050405030a030905 72
    0xd01d800c3c1081182848600b685a0010403180c01c141c01400140d40c0c05030340070008004040310b0711113008600c00c00c1c4404038001400c0d00d04204a800101c9030b20710a240c82000c102001d40850190000305051400030340c1e8032500702c100012120f00c840304480c4500c10702e441d002969080100285003a0031690200105041032010150100106455031402b80c00d042c0000307074403800e602c82e01091101c0040740c110b0555450b03801000703001154030241c40d01070780c0750301444078940044070010010502d95404681142800980c0c141110320039520014240f528404001c5d4911100702c051f40c03d01d459440100d4203903030500c8503074020380c0d0102c2c0303295544034985001b400224030481c0161203079150800401800d03810404495114102c95580c02060f005009412014020100e02039000080440d0017400c00800d404442e0a8408281310b0038010b81500d801c0101c1e01001b9456160044ea1a4080c010307002e009070000312800506090160416445001080c0740181c4001c003a000110107203010401810300c803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 65285416 1250 65284166 65284183
    0xc0a0b061801080705011421270316060b04060e07020709060b040303110307060c0e0f04092102010608030c01060e0708010320010c0209100e070f02070302090417040611 74
    0x200000d01030b0741c582426a5182c041034460b40d03040c4005c800d0250440c3c80c64000712001d1540b4044079045080341040a80300b420700490b441e5408615001043c03c0d959001034120484040359070040d8640907049552050801e0a4541103032000c0c1c0320004044250f4590240074082c2c0008010132a5610381400020324000703c1d17902990f0080d1501c00f09020308514a400ca9007980d405003804004d440c0ca03000740758690b200300080900743d0340c07411140b02902980721040250343c41d01120214902002041000101e90300e94a0042420440314103011401c11070310111100307540e4034000018a281e545803900d043d6886075409203160b075074941d0b040c810000000e0840790804681d14084040d50304554a90580903e000d41c11101015110901c0c1c815a2103402e6400c6543e80c0900360207000c1c10400c1c81c03008a68003034000c118402404000041e00d641c45480c44403113541c5554018030303008e032954080c420b126030090001d80d000e01040c03e0b4100c0c0c60960340000d2000704083da0b00c5d6103a641075032030750034204041c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 65286666 1250 65285416 65285449
    0x20a0f080a0b0306040807051204080102071502120a0b030c0307060c0606090b13050411040207110a0504111b0f0a030203120c03040b01171f060303030b060306090c030405030c0a0b06 80
    0x40c86240d002503100051066071165006c030606a45440505080345440d076070140340c080b04c80000502040920040d00a86651482000200c203034132000c0c0884000d0b4040c1920002041140f200001e0349184e80d90030107281004041e040d01d1940300c588003c03e04040c5680c0284011680b004010710030040d41d44070340001440002020013211014100250343c0b265031040d03e0788101e03194000304083c49100b2603149210340d40240110342e512203e1a025010030f080b031694610411165100003011f0510b405608007900400d114989007402070007085115481021494080d88540d1404508404c0108000400140280c00550312175240022000ca283e1004010240404092060000040c4a84042419120260072107031300d10007051b6016181c400d1105c00c60b60314000305090034244800340da1010060702d00070364050020006001c24005180301c182c81158106411100083d00c4e03640c001c0c00b80d03801903c540207803460645400f91179481c1147c24901075999500810521102e49451204521032205 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 65287772 1106 65286666 65286671
    0x30b0402100206010b0d020a05040504020f090307120b0a0f0b100f09080105010305030a030207170705100e0f1c02100609050a0b1206010603090804030204020a0f080a 73
    0x25a026030180c9901c0e6040c021082c400315245058035003400589103000310408141c0300942c040464031040200601c404900b0781e90741e0004240c1c90404450040c0c99484020801d41402629405015500e04852511002584a50703c0e5076100c0b82058001500341b41d48001080542060803071700d0340c050040c4004001c07540e04000026011000c0d41d64152101e03803181500f5007218400c0c00f0180132a84103011208500703102e500241000342c0b107a5203800268184103e0580035401c400001c0303134140c028000340800b0050920404040080510041101c5020407200684401303078070340e000e401100100c081042c1d81c0d0080011000e00380c0524002c02440360348288600c000c00054481c0c031240ea0800e4440d141d0b43c82c259882e860545070701c0001c1d18407039280c0502540244031700a001c4440078000e02c030003c05641c035880545030b503041030380f0307803103081132204a00801d0f03480001d024081452 = true := by decide +kernel

theorem cover : BRFrame.Cov 65107916 65287772 := by
  have h0 := BRFrame.cov_init 65107916
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65107916 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 65107916 ≤ n) (h2 : n < 65287772) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
