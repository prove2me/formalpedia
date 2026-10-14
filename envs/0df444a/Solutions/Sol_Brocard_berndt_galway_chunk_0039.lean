-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0039
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:30:40.086722+00:00
-- url     : https://prove2.me/submissions/6b8b9602-8c9d-424b-8eac-020802b4d2ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 6834539 ≤ n < 7014395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 6835789 1250 6834539 6834551
    0xc180f0504170a020f1b130e030a050d0204030611090f010f051804060302030d0305010312080103020d0201080a02220810050405070501081008010203091e0c10120b130605040b0102030307020a030c020103 89
    0x95a1070900a00c0d118002c02c0640500c0310841d18103080c031603101c7c0011154030400c0000c030b6803070155440c1e0003400d12007405c0020000b010321644085405840240d80c118800304181f9851303d140488507400458128090510107421780c0056000c1d0707000c041b00040740e0b11083d140c20301c00f04965421000d601c100542c000d1781c4440200240c0c50030403a00c000506ea980b0b0000f040d5041d42004080340c80200841da042121031001071006032584400c00b1049036080c00c1541d00c0e0f40325451044041c0c000c09514030a40c002010b4510242000400c4071021550a641a2941024079400381c81c20b4400458000d0120380c4521010441c0b940304607903d69000d49201c0c0d543c0364840e2100010b5003664419111036410f541305140d03102d500c1c034003c00204d0300c131420000105030b400f20348004078118503c100403c2050141103d104001c0c0c0840390403400d25004010315400c00e100e507405800c001002d842c010540078506d040a0b1110320b500020469000d08111780080540d0341032941c04450b540e445807000c0381007545800d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 6837039 1250 6835789 6835813
    0xb060d05010e070201063305250312060b0304080306030109050a030302040807050904050a0321021309050106030204080601120312050702010b090901051902070602070c180f0504170a02 81
    0x845481d010b41902d80400c11941888180203080d5802900403581119114064441c40603404085450400c0382d80c07010103114415080c184c1f00c60054403581b9175840c0d603054100d45100c1080341131752003651103078480b0b11415442e6607040c01150740138020780c01042d108101060105440074007030f60740f1070002400454441d0007035550b2030400c00301c1c103000c03404643c01046c244080001444110040c0100303681200c03843c0340035220307181d0b248210740780030301400007048400400311b010070042d82c40000c02a00c150350307551550082003503c003454465a0503c52910001041c510321a000304c078100c0300d10344011300700c513420087e044000340d081c038600b1000d01c950300007281044400350140c00d1154040c1d40002401c8641c01090001700007001746a40000e0745040100402c88039403034001c20801c0e42c0800016180d40c80b45c5003c03c020b1081410240007210007034000541c03c50603034510b80c0055550b800a00c0203466071401c5034151203050b9801801d401c0c95151941104140c180036005404240c4112402c55500d5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 6838289 1250 6837039 6837041
    0x306060a0507290a0c02030304030507060504050c0a15020705040c0212030903040f03080304110d020108130503070807050105060102100c120b0616030806040b010507050a02010f09090e0102040302100305060d02040b060d 96
    0x9000da03940c0c3c40c50b90200450f5001c40d00c211051101d043c00070398a03600e00780d54000c019202c0c1000081c1629038400c040707000c3c00002c2211001c41000580070101140e12062140b260f0125584000d0041c41801404a801d04050180f0403410845400030241d02c042c1400900c85904002c080c0c4a151105101c0000c0407420081881d00450040b01a075035241450300703020390f0101080610038096a0f89416010050f6400f4861030342c001103018544689191900d4424150b1080780c40c0901442c20115144040c8441903001a01a0001743c080701c85000702e0310b4581c425900d04d43c0b029804142840c1d52080e003590b030b0743c020b00c50301c0800600349403800da2071140341401c1e000c10500a60000c1c041004208040c1058825032000c0740d03007403c10790b0816040e03030b032243d564184d14034009041050711616010001d004104c00c0c000350602002c01c0c0096480090814000c0d04548000d238071031042c015980300440c2c080d1041900500300a080e00002d51525001c0c040644003040b2082d40104007084580494442 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 6839539 1250 6838289 6838343
    0xf150f0f070309090203100509070504090e060f06030d020a030516020d050a02090a020909180307080301120b0705030c031f050d0803180609070306050402040603060c0f080c0306060a0507 82
    0x504840035403140c0c0e00d03050040c200c1000d504020081803042040c80340c21000040882c0445501301d500d282c440d65182002c507082d0059903c04c0d442c49090004010f603104000c0b91241c03081d076401d00b50040c1661000308040e503900301c0340359020142c4c0248418001207803040005000c00e416090076842d8072a04c07640864048c8032203080586044d08001400c8086280282d42950014001581541001010300c0040c03041c1d04003500340c028908151512072000d140610548500320f40048034a40c9960390f480b404281c503d4141c1c800c0b1228080480050a203500a80680b0700407000000d0381d500719950f88050071280c00003080b04101000c038080e40041e00d81d0740c00e408030010314803030860300e6124101340410f146004450241c1500c00d40040040001c01440019003404a03030700714402044948407400441d00401030354101400300742c01d2282150100ba048844803107500c0030781d07032180c104c0e41d540c02540f1814001502d102e50721050401c29000424030840c064098a400f0380c00d180440d0303804c070440c8198841 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 6840789 1250 6839539 6839557
    0x61d07170702100c081e0402030c12030a08070f0c02040b0d12030605090907030201080403080a0902060406030218090405060610020f0610080d020106030b01030311010f1a030c030703020f150f 84
    0x100550100159010740e001c0d130014400c042c249042181401824111030084100303080c0030b44224840010306540d410040840180b00142c0300f13001c00c40300d11040c0c60b205da1142103070502240c84000800e0038113105025454160b1510303501d00e0442c1074203a081002802071030201990086414400c013001c01c1c102c2030503503a802703216140055802d14003414003025000007089084070740c1101e43c0400260341c02100540d4880da03d4944000141d440c0c480329001886a8500a500302c2e50104010038810b400d50300403c440c200560011044521000800040703500c107c0b40240326800801c04508141004480011074006900640380d40812485140c2d14006003210070b18554102c0c0c131020400e180050024080a8241d48001e20450b030441d00c490105a4040c440101040071403000d81c81d10807070030341c800d024103a094001408a50796200e072003804c4031580d0804a12900030001d03c1002440d0001e002c5080340c2d8003805052000c0301410412050703540d070502c00e841c0b03024100411144003c8200060540306 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 6842039 1250 6840789 6840793
    0x5010f020c010e030c06010b030705041d010e0c07020a03031b051b120609030a200109030207060801140a05090402011107030305040911040b0d0f02090402040b04030213061d07170702 80
    0x3040c80a075050940780c881c00c80c0348043d00100b105002c50358012420031305681d040070009950f6200c80404507420312441d48035803040081596101c03020809541c0240c12140300150341031440d01c075001545c00500c550000250300c030003c504100002401003400d0f01e41a058800380c041c844685440d018248520b02280d0401c81d80c4e1440f0111951a100d5880001007590500030502441c040f10700300d503284203050060b02030040314000404964440040291003400c484001d000d0328505140196840d84540503050200f500180085184502c207084084008401008281202e1a1106100c0c807480f020f0001d90400c80b120101540f41c40c020000c40b03008610942d1031f07594841c50840401c044860050044040d0383c0200b01c2001120402e10541d04024010040001c040b907514080000900c2a6841301c5d40050022034002a145401c0c00940200c80c0261801203004652009034000c41e020fa014108403a403c8200e0722030007542881c91941e0102d15814140c419074203440c4554103200048801134010303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 6843289 1250 6842039 6842047
    0x60f03060902030d08130b1306020a020f010b060901050d09110301020c0604060e03030103030c0213060e0a0f0605040203010602060403051b01020f0705010c0906020705010c030302120403090303020601060504050604050603090a05010f02 103
    0x1030070f0400c80e000580b0350a01d41a405814020706105070350011100c06445041250b010480c6454490540c216042c3c2c448821940c031186c89401a407210901e0b00c00500399440c2640c100c2641c24050210340220005948580c500410440000004c10540714281d420510901d207808444c0c5003480142114030004006140524051030a14151041c102030251a40c205100400000743c1100300c080100b90b048412400c03420756200910b006250ba41d100c400f0505d251010321180315082d501504510031480401d1004986680a100680c8000c0c0300c0d000c010703071001c000a40460710960144c26100300c40120700c06050301030424182a6040071000c0103100c4030008080701089000d1103403256141540c1081f8030411b02c5d00c00007035203a8489105081c1803184104a000c1054443d82c110388460003007480201440c18036080c01070400103035003c1200588540c4002143d00e6010b40c0a0707030125070008107090725081c104028440079030406410500603220700e04620001450a005041c41c0b072440290041e11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 6844539 1250 6843289 6843293
    0x801020405030d050c0307060203040f0c030c050f0102071409130f0602030601030506040b0108040204020f040e04080901090f0e0604090215180307090e030f07020a0506040905010603060905070518010201060f030609 94
    0x600200382c0c140c00620130100800300042001000b5510103d810010050f125a6a0700b4840c1103581d04220043c00c10701068000710410241c11304d1078041e03e1041d40c01e036071030138800300043e40e453710107001d4482e9004000b8030074503032440c00304a100e902042000e094007244481e5a101e00b28292040c0302107404075004002c0003906c0d64584207269100310100e4081c1301d101200c03000a48900b202800213400f503600041d440d050005040221030082c2006e1540c1c101f94602401d1100c1c2942201082c80e0000e00c40350000110170701d2083e540c03c00c1c0d51014505030300070380f1498100002030510441c1281c1041c22440010300c4401c00c00040c12007080d2065000001c000003404041c103001c110740148194070701d4010344c29811807000080d14090920002141c2c0d4841090001405084044d0700041d40603100180101e030030707503407900050b0480320140c134140515a110701502068560403140440003038400c3c004405407150001c07894400d0403060000080c3e480c0ca6200f000c1400b212a001a61640d03210070356030382 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 6845789 1250 6844539 6844543
    0xc020d0b010501020c0616030804030e0d06061701060f33020f0106080102030c07080d0f0204060f030516050a0309030e09010b09011b031704050f060f04031803081902010e010204080102040503 84
    0x400100d044400d03d247c01d410f400b07124600407011001500b000b18800006041500500840c1e00d00d0781c00403c0c1026210491030701340007405490240d03050142c0740c082841042c2c041400b83c40103441d4a403002e1450181442c408040e07845012000f4503406400c0d10035800c042c081e050040c1640c03600c0398058074460801020050940c0d0a56100d0304d101c0c0e104000308145240c070780e410f4418032540207108668074580340c0b88038000f410401c107000e1400d0748002000211039030000c045a0461056481c14405559440e160010b501e45080c800d001140302017041b6008688240e018130782d000d01c41d080014141001c5004036000340800d03002882240b000140c20202076030840c403038411940394000c0140e00d01e00715a03070042c120404107003115516171a050210301040024000000744080960445034140f50200c600c104c0e8000603107054001c03d00b50300300e00e10507061a002103c107580d00010300364030340403003030341f42d40c042d000c08040e03410441d56910540640c1100170300051006001140016880d00c0c00e00301014 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 6847039 1250 6845789 6845803
    0x51c02030d0f05180f060105060901030908040914010b030103080f0d020c0a03020c01030f02040803160c0e040c05040b06030402090c0c0a0503030103080307080108031303060c050918010611010b0306010905070c020d0b01050102 99
    0x21800e03510425240c4d01c07000b0001b900d0f5054a0080ea005907c07007241d1801170300500300c0c1500c02850020003080c081034000c0c00354004580380c0380d40081442070340d9803201e800000d80700038003002c1c00c1c0507000c00007045c1c40e103e498001e10b07100720074680051030480340381c003514104030003200210010381089042d02c0c1e0541e070601500c130741581065001c52505103040c200507501d1081350160f5404aa07806146818802c0c4500181c000741082d50221025107443c2ca00140044494001e06204501d0120008018103020342a80d01c610350141001515885000313020b82180c02c4101c548000d440361241d41c80010304180091030007103110301c00b10303910b90a040c2009090f0460503046403002d03038402e01c41c04e5003040071065410222a00140c00254544581000b02c0700c901c204d21601d42c0281034091600c1140346034218041c100c40c0c203940c920000c48031781c211240c03c1e0752050541c2d03070b8141d00540051100304c21a034041034010000381001c032040401c0750f0100d40d4400d19040107a40a03080d980c0104080c1d41c042c0910 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 6848289 1250 6847039 6847081
    0x3060302130b1c080f0d050a06060c08090118050a06110f010e0303010603050901110406020f01050907140603060321040608100f03080307090f09091707051c02030d0f05 74
    0x1805114101e0703010485000490f0902c41080c101e2000d8001030041c2d48044034448928090034559600c0c00c038468a01404080c2c4074410030516043e80011868440c613010344419601080851070214598011203a040c41340450f030042c8044c484001501d96102003620008210540324104607041c682489418607868261603251039041c40e003074140034640442101e054134801d0400141c60b8603080241d60040c2003018201c5d03000000024042101da07000500c00e04580b4a4000a118a645116100751240354610410006455103000039030720f49050307009180e000c40d02608955009000d54454007600c094092060034000b00014180700c001c0e445810a58001c420b030782040b03441407600e034000c2e44405a81c0310141c0110004030104660301d105004200091442114088005c3d0b25001c1c000010140c80c14112201e03000e000180d0958042c4500340c0303102c20b400c240a45480e05641d00f0003950910141d1050003140003c000ac0e40c3d8401c2c0e44c0c1701e41d920001700d2040c001075a00d000c0512840703c6001c0341c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 6849539 1250 6848289 6848291
    0x6060509070905010c030215040309080d1106060103020f09270a060810052e06020106050d1101050c031201180c03020315010e010203040e090d08060d03020703021e030303070306030213 81
    0x400001c0ea410448120840d01c0c207103400401d520060808a007010b2100320703110481c1e950a0301b80300515034000110310660f0850010354441c4110807000b5281503404481c4458681c11070b40c00540d031903010380d0240803004401d00e0524500206500041e4001070409595408240082d0610300c01c8600c00c42820b40c00016404104061428210305039620030038401c9004010361110009548803040170b01203000c0300c80240c020742e0301e03840e141959010640d041c01448015880c0c800001120b2500c00c1001d14083e811401c13011101a07642d004551550005411244030300c0b040050049141411345030300e00070102c4096501c60860700403241000d8408582d100d0b400c041c018401d2118504c4621000c0180d0380c03090800e41c0560701c40400503400c7d4041d60340102c803160720702020081141350100b100502c408840d03844030300f103036144401c000a414010340094016481030380c05200500304070321929076010308000c43c41c907000c1e83c0b03800181c550340c0300700e0b40c810019440d2107040085048c0700101c1744940e00c11103c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 6850789 1250 6849539 6849541
    0x1605070b0703090902031003050105090606010f0201060f030b0a0b060304060b0415050f040b0a0801020c070305010b01020f060115050f0415080a0b0d02010c06020d1b0e01050a050d02070302070b0a0c06060509 91
    0x28020308440b154044c03220309a0740000404c0d186118030000b0746c011035000e13009005a2500c00c000a40b9458215a00c0c0c5c042041b011241c1100f80c8184200c00036648098824001c6a04544590000f0007000b010b0005a99640c8241d0089581d09005584150b10a00d00840d08500f1102800280c4041410001c40d0100c882e4080c42907613100c4e00350106090081d6000240c42a000000924401d81c550000249510000e481254041c000c02c501007a207000d134000740000341e05100120f95032002c2c0340f10005550000e400500404010800d92140180d142c5032660910040303c1c071603020740c1d000e640401c0300d8a5460504035074082d00070131403d9001030300a5040020940000218100345003030f210081c1000b525140039400c06c00545d0507500705100301c0c40104100c1d024086501c0310206002189000318003403030715150309903100d44100d614400c00756450f6801c06d010308211002a400c030450072400d40c06030513000f08598003000f0241080004c1669207051404960501c0d4044031029040940035004400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 6852039 1250 6850789 6850793
    0x6020601060e100c320c0603070804050703080a0f020c03070b090105070503070f0503040302090901020f1e070b0910060504090c0605090a080102030a050403110c010f0f050706021605070b07 83
    0x1c81c001d002882e0985407411a04200c510449101d10601c9008100d000001602c00315a1080d03407404d20015040c2c803610300503600c0091595030f540d524034101035001c2ca04000003010325209003903840d0441e102e14211010151640c0e550503141e0843c80446000402d00320503010388643c1044283d290755402e5003d010400d080104640341131240c0f441e401e0500c100040e510302008000c00440300200c0e0807199400700300700d1928040f034480d0f2141c070099108045e5840800c44080f018406c5400c205901c20360390f860700058160600303085c480c880c56450ba03130070305001c500d01107907148040314441c1301c221000d407050a004866200c01c0302c0c1d090308828080c03898101c3d84000108900700c103000b62020b506100343c46c0d40304080040c001c0c245c160040c04155001000340842d51015402a034003442c800d4a85010071150704130b1250390340080455550000d03040c4882180818021414880c981c0c1d40c7e480c10300d01c2d00380d507500c40009903807080c1c1c004252880e404204505205080c812140a0454500031070b103441d141e6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 6853289 1250 6852039 6852047
    0xb09060915100e030708010615020d080f04060f020c010c0f02030c0618010603020a030807020a0504050f04060504020402130e041109041502030a06050a09020d050c090604060c05030903010509030d060602060106 92
    0x11034056000342c0041d010454900d000302d01d9280303582c3c002402c6540c15900e8008190103490355204148039607402c40d00d039980752800071420b0145030845503034042e89a42c031010381411542c000350040e11055071b140c040c098001d03480d000030074601e0844400030410313681c62070000300030307480040d17410382150002d01c4880b04980340414070303e8210204222035942d80c0d08401070280146000d92000394040b04803d000810441c2d041c000c0d0519034002c035001380c0e82c19554000c1c00140d910842d07002c42d04154040005000540a0340901c0c2c001d07001803c0141003d008164000007000c681e0441b0000d60aa03404010411180194001d190042503459409605243c0d4030100039007600c40310804000d4001c00056161402ca521410040030020000d449096072150004002d500c1a10f918010a04220004400c43d4034181141c17074044000d040076180c686041012142c2e90741c003043c11101400304116200300b82d41c0902866001305c0225002d107945550b004909070403a50154000c405540240004000c0300b40c00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 6854539 1250 6853289 6853321
    0x150108030d150509040c0305060f010506070609031701080705120109030c0b090c030d0e0102060601090501080a0b011202040303050a020f0a0b0115020a0507060206070e03030301030b060607080c0106090b090609 92
    0x81c100301103070b91900382580c001003840b26001942c000071248204000e00445640c2c80040700e01820503281143c071780a0000280101c01d004903504917004211410000d40349501604505009280131300b850b60410000384000482039010390410350080c03109100500d084c500c2e07062080301c498000c20101c201540d0180103803031035050140030409040e00050001d1000d01451501e00001415a015a0080d0002410400070040c404d030051288000240265000b03205c0318050340d8058681100a5980d0078561010f001c001101034100300c1c0000041d4405400c0380042d1000d503103e500c0b616126200490005c1c90564080f182805943c0007081d034a010039900d95100f1705444d17404002e60728205101109034030740007034134100500c2071043c0f003800241c490b80401c00c2802903183d95611240c4610b40020155030380000e0201074030010008010540515281c1c005042c494401c0c01c615080000080c60203003103c03643e40c400000305442d0004040f0504d88890159030090f000c590300381030b030304182d040b0782c2c40688 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 6855789 1250 6854539 6854557
    0x50109140a050609030319050304030306060206132012010501080105100311010c11030307050f0c0103020703050d020901020a0c090609050606070302030706050a0f090302030c070602070e0c0a03020d02030c03060315010803 97
    0x281c9015252400d101f140d4a95800980d0781804510124005040d07a0088a081d03000a01d00f600103d5660301c040383d81030003540604c07c15854505142c990032561034098519a4240c0201c45004045440e07140c1a540a0f20708080009111f600d858409804e58200500c502020050f0700401d0002420207024214020340c01c0c40e16040005032403920764603200507140f03402c1c0c0c10310011440f40c0c100b08000800038420a43c42d41643c20b00c3c034107407006600340d0290307000c0180840e100317101c42e088403541540034040c3d0b1441481102c82d5030f41c0540300c180405600341c004120740341d12040140840f404038001c064225005543c4039140c544240c9009407a4000c585004082a4480d008104c500329290059125040f10341420040000c0c1d52030041c0d905d50041071006c0c007501601000090701c0c1c1c00490030500319583c3d00f00f040e00030303500c0a9458156070310000420781810390a00c1340d0344041a680c80514402c8103013a6085a580c108001014038041e2070088460b0005001001071102d134074007100b40d5006407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 6857039 1250 6855789 6855799
    0x8040f0303020304050a020d12030609020c100b130507110d020c0d06050406060806090304030311030403020f090406020f270301050601020714040b030607020105040c0e06010905130212040606050109140a05 90
    0x1444901c0d0181c1000340101b4003035842000d440c50f0405200000040c00c0c1c2d100510345080050070ba846441105a01440c444c0700b100ba005089244814481d98215404035040100072095840c0620052021600d0540d0b441000481000c20740c85515010400462801150f0000701280e244110005071007072000840203002603250004141080095003000003c0c18200003900d40e945410322002d40c1e240c1191105400140700740c1480c0709402008011241600d8014000807008100401485040c2c02c0c043c20444090b5030801c02000d951618070301600401c0704418000c0c41811300000488001c422080c0d00500c0303a40350600348501030780c0026600003200d03840c0001c442181c140b0b00004000300880c1202c150940103100800400c5a41940050321841c03040300607910781e90f00e813200d0b0050b4000442d42d040c04104862001d00451400c10100400e42e21419000742c0341c030301e17105c1d00d1140c0d0341c400395800c0b1600d507140c10081c041581c100c0c204030007400c115500f014850980200007900c281c903600c5014061 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 6858289 1250 6857039 6857041
    0xa02190209010b090d0f1b0609050a05060307110d02070e0105010f171009050a0b01090807080304060810090e060601080108030a020304090207020a05060a0e030c0607030806190807060809010c08040f03030203 91
    0xb42e11140b00506900c0c1e00f06006c4554070a50f030800c110f041d2400c0411a481c40307114070002c035489000710000000e484001d0804075180d8242024010240e10103170400c001e100140003403000003039040100000c44402075001d001001d24107002d100c440081038100c42c0c1400003011100d00c0c2a50320842da03900100c0c02e012518200d440c0c1c0c00d9840501505074120ba181c90b400c0100300018800030ba0004003c9403401e0342e8405149a80d01c11381c985802c09070082408640041004000451050314801e400c01c0e015210680b000c0d513a03c1c48502281d48184100b0794a4006900300810307507070842e14060040201c0c0b4003642c600301c070f5000000d40340d01c55402007200896012038088155200d501c40380b8007908000d4481c030354910080c04007400c1196848055842881048000c082d64140042900c0300c69a142d103600340551249010450510a800c4035044505046003000400c10403c12180000b040c041c4c485c0c4005090080d041402e48035120310540030b00500c00d0500001900f494280d88065805180042c1c032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 6859539 1250 6858289 6858307
    0xf03050705090604030605010e060402040b04060f05090a090902040c09080705120a05030307020f010b03030403020d030507051615020f1501060807050405030607050a02102009040603020d05030a02190209010b 91
    0x3442c0104a030a54021401040101c00c101441e8059070580c3d51507490701c0764507960308041000741d125030301401801d0101804100706203405100c820f07504851509010f42020b44440100c0c6805010b82e201c007803d9520781200d4025800c0c144656907180d940c2c0e1030504180d60034000110303030761006807041c2c90007281c801005e074100304014090540069032001c150782c2d40e070520350402907a1b02044200004203501e04111710200d0f01d400000c54040f81d9000d404035010f801e40fa1026074140d003000d8000d5403640100315200903003502d110100009040e01540c0b0750507101400000918011030480381091036030002e000e00b082c031414501800e0440d400d91404c403800c1e41c1d030b107041268140215486290036201d45803e102c800d58009000d02914162a42210561862080c0e40800d9944100d07020100d003010390704207800c0d03207200001031124203400784c0080342d007d03035035408112188450f0b02c05803150382000c581c61400310341c14400e405080c035000b114010707122090f4000a400c4001880352049100000070a504 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 6860789 1250 6859539 6859547
    0xc03020a050a030e0909010203041e0501020705010527010908090f12060903070314030601080411040e10090b010b0c060a05040303090203100e0607030e100c09030804080106061706010f030507 84
    0x9880340d009090b1501000c40d40790107442000805002481600c2c483e0000d002d00005100b5a031250b81c0103094400001c5c1d60050300e10090b0103820080c1e03942d540800a00b004a0307030900400e4040ca460303124410405140c20110042072620b0620700a941c1d0614140f803012030300c03030b41c1030351924107045590b4003201c400c00b000202c0c0400380072614809401044204039030007030040085c1074964082e459150150602c4103500b41c491200f141c19601103182c810110740810720142140070030107c0500b00080d00703241c500005281007181e2803030481454a0b85c02c1281003209040750140188445c002013400c14684080711911050000c0860158941c2c803800901072600c29005020003070f40107030a0302c107200268103000c4040c05c0360f002959030510a2002007000d40e4442c0c4500c3c1031021030040540600000407403a1030252442d00102010459440b80101c081140f601c010070041542900020302e003841e24030042c1440703000001214801000b10308120151f60000c5030300003035210614000840340d0300e09000f61 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 6862039 1250 6860789 6860803
    0x80d060302100201020a02010b010c051f020c01020409090210020c06031f030b09010b1e01020705040f02040504020a051201090212040b1306020c030c0601080604020102030712030605060711100e060306010c0302 92
    0x40d60224941419000b030603019030003052100c45690082c010000ca013801510015000c00f8020302950010000360700b91030071100c045010001e800005442c0150822946080e600140c102c0810183c0c0c0362010300842c9090035030800445c40c10f0002d0306504090000044280c0001041c03004002043e01b20700b44444c0240b1403907009150311040e001c0640c108600054002c2030f83e03070107441c00781c400c0e441110310742044103e002c040c50300160300078100c01c1e08080a00c070241540c2d103200c0b042942c0a1201081941c6c072400035045000d81d03595816120400502908601d8030103074454004180b0410450a9440070200310030390180c0c00c2450180c80c1d85449111100300c0c00c1c05000605018404503008a21000100c001d000e03040d8500c00300c46280e6243c4110a031504016540240941e004000e20800610010001310f1001610305002985940d544042005580400400c0301c4c403c140f09002e00755860908050248020507152240c440340e062408150703280b20150106061080070000d410426200708050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 6863289 1250 6862039 6862043
    0xc07030203040315050103230705010302090105040e04110112050105030a140313090518030306030d080919060903030e010c090b090301060902070602040303020606010c030207060f050412030206010e06060403030804080d0603 98
    0x249204c1c0103c1402000500c028001200e1318900d000001106000b40650b80c408402c1c403e029120f03107482d04006400075403000000c103062117014400016004140c40c01544101e014091029040c8010400100301c0d1595402c1c070300301c07185030000600440c4c0300041d18a19050303000d00e43d00382e40c55015000354507500815078803880010400401080c86c41181d00a00e0159030f0410340340d840c3c0031501c0040c40e101c0c0400c03030302c964140d0300103051824003a20808501d0b4100300f08000390780148502c4c0c3c80505078400c2c80c1c0b0303090b5602510f4452301d500300356040c450724900c00c42c043e00030003101d0184240207020a01070310034140d040101048400b00c9070740039400b260080c6400c2408543d40c001d980703821000b03500680700c180c0150080f140055102d500a583c981c1e06d6941c103a0283c61281d0421005031000f0100081083c100301007404003242914207181044076041c066002810b56600d00549594402c0c0010212405440c0a002c10000a900590221f81196112012076121624144a400100466400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 6864539 1250 6863289 6863303
    0x3080307030e0609010c090906030305161a0403050a020c01030501030b06040504030e04020d06050a0806060d12020715020102030406060b040b0d110706150305010b0d080307031802040606030b030c1203030c070302030403 96
    0x38072004c41e5055000000800380c60316081c1d0529910842d4a085403e58403010340402c1c02001440155060030381000095440307118203081c0c501041003c594120310440d0114081040003603154801901000089180c50007447d0502c80c1c0c1d03055071f6030f400302228042c1500740281e4803000410105030055042218066000c1c000710340300c0320402e00020181400b40300c1d180c00307244034a0b40031440e442d000c10b210f48100805813404031841643d954920100c912415980700318003c0c2c81004c80c450442c2c3c0703c602c0304005243d00250b202d0402e0300b4240700300c03252a0b0003003060702d0042104000e6002c01070203a41c25000060000035400120004441440c411214020b205902d0042601403e9099500c81f80c15280140004c00ca9646d0100c1400800320b2400e201505910381807001603030144c0f00760007204a10a440a40d41114503a60740420b09035407894110601080c0c540e8a0514242000c101d52400da400031540303200c0c00c002140f2201d48900c0058490038100c5030005040c400c0c90f0081040303030000e41c0e1180c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 6865789 1250 6864539 6864541
    0x61403072703021503010602070605070f08030a0501030506060307080c041d0609010203040c080c0105120a151404110708030105040b010507050a06020d0f0e06010e10051c0b0f040b0103080307030e06 87
    0x103031034410782407280000c0f0b105201c00c00a0036960304d040026a0b0694140e44c00805e9103905108054405400c90302040350320700750301002180090810350246002d084030200119044d411460020b003441d500500590081c2d0140d5410400c0c40800116000c6001041d24006a8604050340317990784102c507540306c40014440e5000b4000c0c050015802548280e002d00d18a003202515500c0654850010088845c0060340a000e903000d0740c4940c51085410824500c8005026045048105201c001550040000b2800814070004505081c02a01001100700404520f412410740c0c58241900042c0a440d00441c2d5840d101c1c00c0381e900450071604030700d0300001160000203240c44d00301c1c0a980b01c501d00c1c41d0580e0404000d164a0b003954083c40c610b81602c24050040c0c0c1e82084d10740c0561003801090316907040c1c02c109000509485014080301a0b56100b105852a0000750808014010015103a001468490070802020030300e20444a41581e42c0035050a60725221200102e0141c01d03012a05049401190 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 6867039 1250 6865789 6865847
    0x3050c0906010207060c031404080a0309090501060203090901030f0501020702060706061d011214010605060c010b03010c0e13020705032107020c030303011a0306040204090207030f03060902030106140307 89
    0x118601040811540c24255a441000498442500e40b041c0408100100d030204000780c000c56044030210560142542400d90752a2000c1c03034048095025000701d5500c0c1c07406c2c400880d075030260301e002d4946400118a42081c0401044040d40144409031120130100ca0140400200703404132184560010562a103e01c44c50030040d00030542c507c1204510003000485403102942201c0442c103c90314240403031006c0b402501c949203058610301101126540e104404101e0b581c404002d400031110410002540d03080c6801810308541180c041c050a21081c010b079850550b880400315090b03515002c101584600305854414914012004030740494911101e10340802038101c4600c1e03118200f56070031609007554103000d15803a840280201c060420410003201c4520440100640d08240068001460107070754600280882c2c102d0310003200052545203281c3c109551600881d405010f4802d07045165515143c0081c0034101c111b042ca081040d004000039104d1405051109040fa001908c040d01140c0f2003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 6868289 1250 6867039 6867043
    0x16060519020105010b0304020d0f05030408070303030b090c040b0d0908120f0a0b0f0409020321090a080705010807030b1906020601060f09030506070804080d0f0204090b0910050108090309030303010305 88
    0x1000c0c600c02498100190385011481402054100c0340151081132441e00c072034003030003c044040c002c15140350315508124000294100024402017a00034068081035085240080944003150013030b61007003c0240a000c207020038403040342c0484007010304499850071281c2d0008050000c001c005442d4a10100b82002c6000c1912a554400e0f4010030888500b43d640c1c2c00c1200c103e41403603c105402140f030755888401170901c1e034817650700d241c002806c9034002e4003080f20803407440340d41103418035a500c0085100da02a0070702030079040281071140090400e160034440000e014080051102c130825445000c1090940c58802c031341046000d0001404544940314800a960303041300b88541000924540c4800c40200e1003011040203072a881405802c0985448608440581001c1c000b618600c40400615919031001d118500711010003860268a65240504103400c40c0c64403c041030045580304108006d00305020141c605440007401c0c200b1207502c800b001036196000d0200d0b943d0709480300100100500c100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 6869539 1250 6868289 6868297
    0xa0501090b1e0109020c0304050913030e0d03050a1803230618030405040b040221040506010504060803090103050a0b0a060c02091012080702040902090103030509100f020a080705160605 81
    0x18248410080d161040301002c1504450001400e18410b58010700c00710860f40c004040c0c480c000b404407414113850b040060203200782612100300c072003c0413110104061708100c86680d125000c0b41c103441448203548020301188100682c0600b00002c085510441c0000384142c1405145c02c5002166050018903c80d04880c040044418151090800003031112100142a55040411801035401c251404007448003810401c001c40c0c8e8029000c1c004500d40e1945601d1402c00340030105003210150405003403040c24690181c00050140e030a00c001400b03d13241c000300b25002e10b00280b800144958030980080010703c45680342c10f0388080b4107000050015407140407000c899008039501c0c500c940340d003000040d01d24024407030401290b14019404000c106440007510030300380003500103d035044003940002c02c2940243c000b01c0215401040d01d20860402240e24100411903040c40440610788150103566103143c980700a2140314005210002c1102c1404440103c1811075034000145807601800740041d04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 6870789 1250 6869539 6869543
    0xb0f03040308010b03090a030302030402030a2f030d09030b0403090806090106061e14070f1a01060810060912050106090c050405030d091404020c0a0507060e0301060503070506030c0703020f0a050109 87
    0x103801c2c4004246031030700380216805164640028503d00c0e9155405074065000100207903814007680010340046103607110100f08680c4081400701071030450300c82c09544034218000b840d000f540b012030440a8580c02c0340100d0305030303900119981d11507611440c0450b00c3c0300b2250082c080c280074230303018044411015006a01510901c4e100e07401020003201d03461441d1642c082d54100007948080301c5003c2050715100400582e402101c485140d84546d490301600642c4030107003d010a10408010810382e03600c806100d07042005805035820706860803900a201c508540141c0e0f4040c86d4514200f4100078095022200401250105000fa603000c4030f00505644c00600c40c041c001c0c0100d8070000240c074070405c4c80c2c5040e504501d00501501c64240207210082d0060f40e9074060300c1c07081d11402d0001c80e130100002c1e0020040303030780c40364207014610080c10309540c01c9601c120f010385d1000c2010b010307aa40c1d80c000d0326880100b01f145581c1340c400303078103040340741412107041300c09140582001c620500c44190040c412181c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 6872039 1250 6870789 6870797
    0x30d030518031201170a08180405010b070c030215070209010905061c0503030712020d050f0a0b180c0d090b0415050c03010b0703030c050d0606030608011d060a090c0b0f030403 77
    0x2031103040464a911a4980800381e02c2030003c018000d82c0000c0c544408026110360480302c54103039a594840841e4411000428000d448800b032001038549402501d01400820010605000300303039445035080c0880d800000e00c0b40213000914801406d031002900c040c0c075001005c2d04841e594030304003d4001c01054482d540180400c0c1d998880a001c43d44405030919448002103103583da550a0854001c02e1a460f0114041c0d001c110324641c0143c58000c02c0e000e485100c21428003130802c05003aa0444980c403001e60302909072400141b50003400b00c2900703580003202040d403e50701d040545600000b0014208020600e0f0b003040240001d021403e0b42d084800844140100a152030709440802c4600092192596010040111800203031107031b002107180c81420304281e4140300100c003010088d181c0c80c0d0041000241c0c0d0303401c10820b4480c05d004070000d12000d8184a0824800000c5094440100404c100300080d1160020070820407a043e02100600300f4000c1562a980342518811142d80f040d64103030b0000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 6873289 1250 6872039 6872071
    0xa0509030901170c070606030303050601080109060803090103020313020901030b010602010b01090e070c020a21020310090201050301030b1e04060b011706130911090a02070b07030606050405040b0609030d0305 91
    0x60002003203908900050b100c2c00001807161035006480c80380108640c3c50a1418010100010000d0103508013461107a00c000c107a500d400c0300014107540d8168440a6183d08000c0c0420191502100f1140c20210a1801503503c7d960b180310a142403141800007904007608400000500400030141410b03203000b079000388a011004001102c0a41c291300034a00050002c402003a8850301590140d0081031018001d142116a506896070759010007900680348840d962400d5001c503d014410302c402c034885010104a000031940008140d400140002800300d00b500c2c0110f0541c41104001300005500203201f0742051400d89000b001400040300c03103d0102e080f07410040c484082e140c401d241b1400014012166098402c115440601100c503003d0302c0640034002c100d019500c6010072036101e001d14400c00b42c0d440ca018135110f042c07241c0040a12040500e041070510070707654400103d40c11101c00f1100031661004580016861340b1451000782d51600c104d42041c4503107505034000314424503200550101c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 6874539 1250 6873289 6873301
    0x2030705150c0414040e0d0801050a0504060b090909070305010203070507020a0905190b0d05150603070e0f040f0201030b04050708040b01060507050a060e0f0303040f050118030f0f02030d11030a05 86
    0xc0da41a50b0603401003006100074014140b42d056a00103180b0002c20210340c45182800460a10b69028600c1001801040c0140949d080c0312408000806003540c082003900d00d81007800d80180a10305000748580c810002040c1e04180c2008031801440d00308008655a003030200d0b0261040c0d03c002c0049000d40d42d10440000da4050611810340303e19600754610b8024603421002c100101041c0c1481c6070320031910480354000c25820813070b4400380115854038203c04d043c142c00305071800c078240e0310813010040d5100400c150000f4015006810550112100b405840f030391006a01500340092362541180c038103410002540d9010214500440c0500b0301c80f08a44d0f03e84a04851522480c070001c1c11540c4544081c40005400b540300e00105502a000d0380d85203a05082080d007035501c2a00c00365404011040d5500c140f010078461104008015030390f1006412076580d0103031503114103000c02c0080c031209200d02c1d01000c1c0244200d4154002c104000c015801c6030444418140d001540c091070010310b01000101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 6875789 1250 6874539 6874573
    0x307060e0607020904032f010e010603030c0f170309010504020f0102190b060a05100809070f030c050918030307020d0201050a060506070210030e0102070c060305090a03140a050c070602030705 84
    0x1000d08010740310074501100e5400b801003082000d0800c070100b004071a455040502401d400d03040803844820414400c0c2c80d0360141c142560381c2184480c07a00e074507240d420000a504800d05a10159106821040704c03000d500b0901e03000c040c4902c0c455902c9500102300079580760194821392140e80b0855070140e02c85894401282d036402c1c40310300c5040e00310507454000f022a911001d402e43c4044018101d81c05d00c0d1b1903501180c007007400d00494202203044a42030140e401000d2003100c000d4040185400049461500c0f0040d007030131548109030260725120b01085000110b500d0100003880d0340c0701240d07524204048000c1d0342d0600403405038019444d00300441c10303a20303081c000c4000f143c2c0300400130390802c400c5400700000c01402a640106055442e1607031100c01d1002c1c00944041800b4004004102e0315010015081d60401055801030b504500312004c002500400f041d840410070162094880c04c15207402e4075113100706141c280039841034500004035154000f005040091184068030007004030a0303040720b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 6877039 1250 6875789 6875807
    0x50606040302371d041e020d020303121008010902010503010905040201121b090e010b030103030315030f061a030c030d08060307030206070f0302010c02030f04050f040906020309010b09011202060706050421030506030706 96
    0x410105001c100c2e0702d00c4402c0c6c01810740b40070340020b11500515242c1d0780003902d5030f03104003908181d8000100800002070b002c44440001010b42100a12500109074002803440c8814003600c0d881070f961340041000d592084550321020510680100711341c070081e1001c81d4040800d03000540022b902c4210100d00c4104a0285504135071320a807103e41540d0842d41d09070007034425000e440c1215013514800101145041410f4008207001340400520513100a0a88d410912102034250003544030f0300e2890915200000c041341284103914202c0c141e5100c2c540000d050211aa0001c0c3d400080400c1c03180501510411071000c82e4800d070000c01180892441c01d980f01c0c011656070540300c0b031051004011b181072469800c009031000620000780360105c5d643d03840c200d070020780b02ca41362070390f48050000782828915429405030010b000140116180c5600103442c6104015000b0720342900e60f000305d030400c80d01e0004014052100400d00d550700410080042c0103080031282c9030320034401c01c940042c855001e04250 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 6878289 1250 6877039 6877043
    0x10306050a1802120f120c01060b04030201020303060d02030f0f0312010608010312050a09050904110306070206010b041202030a0221060606030c030403030b130f020a12050606040302371d04 83
    0x2e8880084560204880341c00708080051041c012000102c1002c030041c4100f4005800b01560329031104802ea04450856985410100c90340c20100000d001603a000002d9a80c021021145070406905500c007103401c1003900050350001e0b105880b400d40c842c01002c030203001d40c0c0c0ba8044442c034040c1e0b030703649085904050038030011341100c038003420034003449200704018120f011250502e4003d071981c0d6000b1980c0f1080440e8240c4044000c020004064601445401d070818241c0c4014065541010400350b50b5100780d100b184502c500e40c5c12080115181400741100d0181c00601011600320740031444200000084800401409404001415841c180e820380f40100c0c540030901e0700316950ba65082e4024a10003804644c03001c80180c01c107100c441c0c640658070003174880300340c096111140f2410143c1955081042100c0442c2000d041100d0b9840e00350a0318112070b0129420340031041440104036810407000d1440c8245103001301c2d0582e0b50120324100104480001112108250030341883d00d002c40425100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 6879539 1250 6878289 6878321
    0x91b0414040b0a020909040b0118050f0105061602030d110f0f0a11030c0d03020f010b03011107060c090306020304050304060905030303100e070504080307050705011103040e0606070c0803030906010306050a 90
    0x4580807900c1455259031103564910f0061404e44607600040001c03130121400c4407801c40280041c002001c2400362001c2001814006200030304084041c062845014004e25004240c0850f042d90102c00720503520204c16000f4080d20b94009910b80003d000d12098485039000340300301020404841d500217004450741c1000c03070180c200c5c9915655490b1058419024056051040ea1000c40e04c5586104003045513030302c070b46c0045c000c4000900e0b440342920011285117220340d15080c64400c0107140e10040320f6003694080c5001070303080610117007921000c103e500050207292000c01040b00700007001004100b0b0380c0300c5440316a001d0743c0c2e030010140e60748000c4960000b0b2a0309490100440c04040c1c00c0700b90801c4c1a410b08504198890403450303d180c102c0a02034074158800c0004020658104400c2ca00584003000954a401e04040444100c0c100203800d241c010030380012088203015403803034104041c003006c000380d030341d42c0c1030038100556103001c207010544019141038003041d004840784c0300c1c40f0300424031080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 6880789 1250 6879539 6879541
    0xf0901030203190e01090b0106020a0209010e070311070305120105060315130204080f01020405040612050d0807020c0d050102030f06060c070501030e0a020a060908060739050105091b0414 82
    0x10045001e50006890301d605036010001c00805400c840c05603910b0443c940c0000100540c0354104502d030640185d0007881550054000c003005038a910385490b05445008180301c0940d00d48103404c0b00101440c28403144000ca01007001c4c410142d002000f09034001104c4bd0b00d44540c0d80f988200034251100352000c42d03c01c140c5280a03178060400000b0b116008070301d01c40047c20300703542740301c0075052444160401c032091354005004d0209141900c502e40c040e0590150000540545640c0c0075582c0499a04510510030b12900248141d07108110300340340001c0241c4141950381c41031808a010350802d507880c0a40000c0c0740c0000342c150a0641c191410710b58510000c000c2d1910b06401540180903426031024203004000785880541c0700c1000040003000191b40380c9581c103103041c2c40581007007400f900210400624403e0030f20462281d01d10352042c007102401c02620080c02070f464600004002c080101694200401c000c0320200100318411201030919901400e101100200000c40d181840c5010300710004078 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 6882039 1250 6880789 6880807
    0x1103010506091306030204020d0204170a02090402120f070e090f0a030207120c0e130201090e090304060e01020c03010501090f0b03010209150304081204050a03030c05030702070303110a061406010201110f 89
    0x208035090303d0b12500340d001503030303070303100e0700424241e03400280d07207181464000808008140c0451480040281c00c00094110070241341d002556242d80078002030300c11078081c0741c09151100140440450f107004d04e400c0300d140c2d075900d5401100903141100c415045018440f00c1c0860301c1004202140001e5065000d000702c50f0410005d2200c8101402003035074609113034680421800d00c108142801445c1036401070201600c42c0c03000414002440d000b0035586602c443c107100d0340000020a61341515003600b00f0600c036001540040745001280d040169056082900015001d01d640d80310100700354025605000e1060303540c0506081c0d20940d24887c0e040303d91801c1510410404070091a0064400c5809510308007d550340728143d003805640550340354001c00400e0080542510521000c1032181c1052415451b11182c003940b01c1e03501e84009018001841504c446502003406228403441e4815400c2003038014100010850601c121586030166280c100644000d04a46050b06c154000e00031280f441d1040705 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 6883289 1250 6882039 6882049
    0x9030c0201050f041707050f030d0e040b150a0806040b060702010518030703050307030302040603200702010c0302010e01020705010e0c03030c030409020904060b0a0206040c05040b013005070909110301050609 91
    0xf031803100c2c0d503000052202160580101d6028181410a0b4004020550509080000c174081820006229500a00c46015126040004090f90440c21200018503143c0c0d20003040d91429407988083d20041d0003c0c6841e180c54101c607156000b42d0702660b041007240100400d105083c4900113002e404500280128800c901d52f9400b20541c1e0a40603042e116034a41c0c1c0ea440515540203d4400c5002c240c01044c04d203c01945882081d0b160311121401c04150034100d402c0320950704c5110400303070421188005400500d4000d42040303d00c1400c00008550781c1c00e4904020340200489160f07005140610070308a110f5182c0001900d18004050024500d06840c10302c040c00254000080e02c1e801c141c0320140003c0b002e55600180c500f002094000c0c100c00d03d0f0525141081d032010343c20040c861481d007001c0060b41c0c0da001507201401c2c03200601c400302c6401d40108003038241c1e00007450511a45d0400e01000245684030050008603003d0318401c0c814003030409400034542c0002d02856801c00410711007000f251500e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 6884539 1250 6883289 6883297
    0x906010b03061e0f060301030c0303080f04020a0501080405011512030806030303090705010c0f05010603030305010501260a020f0c030d1d0a050a02060304080706060b0a0f030501030203030711060d020a0c0204050a09030c020105 99
    0x1000785004ca181032901c1c00b03d803060300241c0c07042c0d449c20705100041050640008841d640518403481d080018038055000850026107070081c1410060034070b000404002d0258024407115210120b10385013a80d072040580300c10346408008070002821100480c07400c2c200001902e02812070b10000c0d080c0d290400c0300442d0020321059040e21144282c841c0e1700d022503c20721440020f58025034012400b0f60401c070002d40101c90303001d80b440c2102c90403081d2103412102600303141d030042e120311400350380c65032140c104030018020f500f100c12050000040c2d00b09000707049e601c100c00b54041180c0032203039601c6210340c3d5622102a50030103040c54204510480052400d24020f541c0140700b40c801500f8480c043d12518121071945c1c20001828000150714030080d9085007204000d100c5614051016606550100e5128040d211000701400c1500700c80540d02e6849106032402c40794a04001c544a41c0c107000f0040140d400100e0a038000c0b85440042240b961944c0030f40c0380320703a4054440021f0401c0300d0f0300450f400e0340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 6885789 1250 6884539 6884599
    0x5031f0c090909110906010509010804030f020f01060b030f010b03040c030201030c031103091605040908090d03030902060f031906030209040209060604170c030f011401060e01020102130306050906010b0306 90
    0x180c02400842c0890151140d0a0710900841c02c01c164002400144280301030080c00700e0b4144032003401a802d16030b0340160404e0344940c3c149002802001d15103000ea1800100800c41e900c1c550a00360045111a4414051071007000c501c0d01b2102c0c66640d0f0084100c80703100c01d5501800c003031099a41480513501079049400074081071b107030000b1000300c03002081b4600c0d0819244410301c1d40080c050b02e25250300313400c6203001600045070100204515683d071040b0500c03441290078096420032121006050090b80442c00c10380d00540b5490350f405042918aa4650084030010666410510f2500500e5460310030303001aa64003a0070304180740c13502e40800548d0035000706046e5200c0803c11002c00c00008055261200510303a600070410094040e08150420b4070710034414615a01d000c104040f1001c1d11141181190641d09080b6410341741100101d01910481030880100444040000208a4264400c40c8a42c3c449005c2c0d0306541d03210011884a03200645000303501241c5941c08101300038030000d907408024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 6887039 1250 6885789 6885797
    0x50601050c0a080927040201020d02030a0507140a05030408060702070618030f020d02060406030209040b0906090106050309120a0504090f0504230114090303040c0905060d081b100c020705031f0c 85
    0x24220120040505d1100f2000e40302007505074240400c5503010061076041c21100d001440c2042e00c510340007480c80c018118003401403c028410f400c100d01052014580341d0360800103507607565884462882c0d0700c0d04207464180c0140710303005d00003906a114101025058440881c6041031500d0b680714804820a498800c3c2e80c0b000c240400f850050769840010002403856031405600c42c000e2100b08000c0360310040e14035005d280e90f80c1c1004110b0340c800300003d040d146542441e40d12600d45121091070b180c0414544403114400081481d100c81d089800b41c000c07035100100034042c401061940d00c041c0c440984000303214900982c07240e5180603500c2c04100c104030352140001404c03406d40c11038584070b004c140e0340603003035800000502040c001d030840760b40301404290105210b40d003051008600012404070003d405040c01040650030303c0110b03002c1200503603000c803c550000024101e204024403104000501520403440001094280450009454100c0c4000444d0130300d4020040405005d018001200f00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 6888289 1250 6887039 6887059
    0x1050109180b0a03030e04060501050705030304020d05031611210c01050c0f06040605040308010b0403240207120905240d0b030a080406030902040c050301210c0f090906050601050c0a0809 82
    0xf80c0711032203000000d50199076484d40e0b045162062004841c80b40c1c11075410048104a010302181000048981203641540c40c10345c3c2c1714150801900350b0145106400b0000c81c0a0402c00a10244401d40d01140908603001c03510503d585903140e601e00c442d06200803154000408903800d5600071009861254002d4040d1040d0000000d00036061102c111b8048401642c0e035014401415031110310580542400100c492401c2d042d61140a04c1c0c92440b0340c080400001481c45400044054055543c5645c0c45001120b442044035005803a0703400c180240c0e03008071392580c012400038180d0b8030050110095602180e00e81101c940c044000742c80c06540d099054450740c0c1e0604005108140207200a08043e9000541c1d914584100025035a10551141c02c019041c001031004100c610b4001040100c2d407080759079000304a180c89201c2c1c82d42c07170740030540030036648600007140748460b00512650b920808042200c2d546950040d41d060081005040d4240d0080c400e280018140b40d009117040380c0c00500780e10300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 6889539 1250 6888289 6888311
    0x70c090902010804200402040f08010e010903080a09030509090c0705060702010b010c0b0a02071703010f0902040302060409020706200a0801050a081c020106050d0303020703030b03070b0306040f110a0e010f05030105010918 97
    0x180c2e8823540c0072800000f6058800c01ca015802c0c0b00303d46e01070308070100a2004c40081d49008105200281203403030220303600c1c1e0340441014018801c46a402c4400b4113004185d14218051040c940c0001e181502c090103000b0000c0c003014070600c2003d03952035058541d030799039012036101c0340c5110000410314070459500300078044c0032503140c030501c0300c0b0f40c64208802ca6980d814654007403c0a0b016a20048400d4010300c01400140e64880660b01036403008bc00051701c0780034030b0825602400f003201c43c0100025100f1464902c0c004408001d10a40f40c0f9500c8507109640d03140284142041140701c3c92a00e0340050144100c015468650055241542d00c00031034115243c2d0001400344562500480101c0e5000134201c04041e00760007101ea000c58120b0103441000d1034401400410b22000740100e200d0750744c507071148840d80c559512052404110300c9410341c403960620400340c01d480010a946000c61281204614098400c0341200d040c1c8106a58104440b0710b0100da00180307001940700720690075141e203103c0003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 6890789 1250 6889539 6889541
    0x20a020405010e041406010602030306010305041505010f0501030608031603050c1e0d091403070302010302090d0602031306050c070807080a0e030d03050a050907030f0f020f09010902070c0909020108042004 90
    0x40078000390f04a02c001401c162030104507203004001c1d44070540d0409001000080d40120540394400e00a08000c036041ea80c41c641181400540c070000c0e1504c500c2e15001260241c503c024001c15540207880402074291642d460588c7e80c001c0440d0781c1c04520030400100d00280c841e1014000a008071002c0300c0705100480c43c0b4102c11140541c18465a03880883da942c00558800c048200802c0c170742140f4100100114003007601c43d0321602000c1d05042e0005034601c01915072070032052615070485001c40d103e0801c200f40703500818014006890b411704060118000001800c03c546620354132041440c900346859030f50036529045a41c0140a1010881c030310109034400340100408051165400240d40ca002c203500c800301d0710003401c2041030f03074014082400069191035085101580080600c0c801c20800c0c400030300c084215040094104681a0000070318903120b801030402e40d849510381c001c58a40340d0300c010382103840640d0068005060800842c02049004403406210804002041d0020010270040b80c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 6892039 1250 6890789 6890791
    0x3090206030a0b01030506040b03060708070207170f0c120303040b0912030106050304030f03050105010c0204020d020f070f1707030e060d0f02030907030204060807060f080a060503011506300c020a020405 89
    0x88900fa1152803e040c0c640e458400d55034400c0044404224219221000c642c2d22400107281405000144001c12106030080003034030000c040042d080c1d100c00302d030b40a500b5113076200c3c00c00d450200d1141800890407850100c00011000700060000c605580e1191203003a000c1c0f601924242d01801100da22484d60060b04000358041d00103501c4566890800b031800414991421041004151038800140a184c7c1e01c20034041e00c95030110390141c0c4408002c079802d07000b0310810200c0310783d0303500c006076072003c0000580004a02600941160781507075951041140c07144254000180056481c2c01c1c942c08a1404601511040c038107004009409100700e0140c3d4121f90060b28845241c0d0f10001c0200114689401010040d10000c0003a2100629095016000600c144140c40501089400003140411160f111000800c3c000740240308000000614140d60104c81c0201d00000b0441961a184007240d10140c048422580c0030118410000d8070019008000400c1084c0841c05091050b8001d80d80321301030f007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 6893289 1250 6892039 6892051
    0x312050a0504030806090903040b1810020c01170108120a0c0b0c03010512070b120601180e040605090109020a03020f0a05062a06070206070c0c080102070501060501030507030b0d0f02010309020603 86
    0x81e480c109400d0140c40b080f00184002c1c0f00314200b404103e50007030084107840c100c46183e0083d86c1c4840144459440068091b09419040859038550f004d080c1d90000d1000754545c002c0c1c03195982c0d014068080d925660742400f40d90002d03444803101d80d0010407240000c3c891500c0c10300c0e10000001d402e80c0d50307514010050b5a14000d200001c0014081071a000070300840c1c6041110007491100e10700070f01660705000721005441407108103000240d20f40d00905038040c0080e03422400e25030b03540e2a40305110030f10f0020389081d58510b02c6d11740010b074409014400c2600c4107400070140492a03246600300245401c5901c0030580041c0c14000014243d29601c0203820380019590300c1a002c8041c80b451001d07a90340048080d22681d000b1070901860075004942c1c95080281440c146120b002c8500341455042c0d6644e022228562001581c041031081c194040819103500366802c0c002520740100c00c40a550151034a558800310303211034440001c031840c82100312148181000300d000c80700740d000032710660400ca4203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 6894539 1250 6893289 6893291
    0x60c020606040b0604080c06032703070308100302090f040c09020403050304080c010507020d0605071b06020310060e2b170d060504020301030b13030c05031b100203040308060d0312050a 81
    0x41c4000c51400d805184601001503c00500305450300050640d14140e090381e4038007032840000420f08081d1408043c960088016400f80c039541a1868055600d42c0088415000680380101142540c034514a00c40c0c1101c0e001171400300a602ca0040100201c00090303c111000c1c042c0400002d0040a03500180c001540103101843d00c40e8a410440c80c04d200c0c89803440e41c10058200301d8580140d5401902485031a00000009401e035180d010036120b5100b0281d01d6005805041d0003a410880f00d50011485001e50000b84c0d0343d200d54680081d10410840c6040e5540301040d10b0b50244036005074074002c104401d0170100c40605c050305440360450115002c08180f0f000000041244115800e40182d100400d0150380861841d891030311021600c400c0a041054013003030040050b000c0c1032150200c1c40405811600352542c070b01c0200e90440c288441c0d1940e0810710700a60003801208680d610907244103e416032101007103070340d469082091800d210507003103040c4a00c1e0310000d0b43d10461441501d02c0398252000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 6895789 1250 6894539 6894541
    0x21002030a080108071a0c010207020a121a0105010f03020d0b090403020607020706050c0304050607020d0b150a08010506061803070801020304030306051f09030210030f050405010203040611180607020607060c0206 93
    0x1c0003411103605030080c4c00c0c00c0d4004070007006003800c0382e41d010401110319083d01e42c403080401d4100780a8401c0d01070180d0301c040358940c040384410200049a14043c85940b003528217150131070003452041024403d007804901c3d106800d182c9140079400618480096040004a078101400019070b150f00c00d0750280c005a0019080080f043c0d0100607020207080715003813650030f20140454041d07581c03007503009041c003803080801c0324070441d142c3d1614010750701e500c0303c00040a850a040311090311244001c03058419500c09600003082117040c49500d00402c400351070213290201035503105400c0341669040c5501840354040001d48440c0a202841c0128420742d0041403c900d0607040140c104070305800e4a03044031361940510017003500038071311004036503060750111b000c000c40a50584c010104012080007050400c4204410441c0650095104921842c002c010342ca030720f405044054016042a000c100083c4003480d43c6603d00030b00030f07052040c8000c013401c2c41c4c60680e66484081e6110a1803400241e4010301c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 6897039 1250 6895789 6895807
    0x801050405250b030402061308031b010c0903080301090207080c0d020309010f14030a0c0306050307030309030c0e04080a050304050a02042a020f07060e0d05150103060b030102030403050901030e010902100203 91
    0x488000780358800040988422410503034003d0b0755100c0600000e01c10100016a00c21409480060400500005050300d84a8684d8040510300ca000c034000f2042c00e510702505414541c2c000c0d07030303130806894210541a08580c01c03d18100000e5100d5030041c4c0d16036000f4801c04444000c10480c2c61600110703903000c4c6403280c80203030000d00f000207582c01d030358140440e5100c5005810304180a6036409000f10f40040b8080609410a6004006581005426003c2c4540105c1071581080204007140d00c00c3d0402c910007075a410344041002002d5600615031001045404c80c0c90340b05401568005000e0000e40703a094407194002000c41d885078030a0801c8041070f40b20440980701c14001080349105900281000c00000d80c882920798044d80943d201384960270304444a180c0380c84047e142d00c240c3c000200c0b00000606c859495080c1001d01c400c603143d80c1000705a400e54141030094030f02031036254480b81d041942e014015409042542ca14402640d0f0b68803d01c00940c0c0c030030f0076021440d540b81e000f5694a00a83c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 6898289 1250 6897039 6897073
    0xa0c02211b030f04031104020901081603090c0b0a0806090702070509150a0e0106020d0e010206071b020a0e010f0801020f040e07050705010609020c100902031903180e1e060d0b100801050405 83
    0x1c46c68840d6105105c0c0c0c581b2a42c0180e074082d03001c4001c07803098400c012860b2041d00106420100601000250750b40441c09020500080900060756150a8026520401080040f0a0465480c001a009810200503a050042138940c00408000f007240704040c0d4080030034441c2c003841e4421504552801c004202203074050040300d02214544c0342503806001039100103551010040c264204100c11202e0349014101c6188009511641c01003504100507070341c111b400e01411081c01401e01d07188250368005003c00051080705c4020410079203043c14030703140955180010070007e000c1c600b844010881c1d07900050f021b00c01d4802811440c440141c5034001e029030b542c0390541d90700ca60a00e00e442c02d15001c0c09a5800624020580c1014010000d659400e1500701c51120400c484c0307410201880700d002c1000c2c0400500319101c2c6800d4182009880c142c414810040350f41551026040072030306d108130340811819846240c1c40404001c0141c6103a035511985803c555041b00c05aa990704070740740d02c1c41c0300018 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 6899539 1250 6898289 6898313
    0x3060507020c0108040b0702070314060a060602030408060f0a0204092a090b0415020f060403090e0703050408030a0902010203040b0409050124020d050306040b040903080a0c02211b030f0403 83
    0x901d00c0100b14022912001a000c1e503c05040940380056120000f07412520070059400556032050b010701008442425a03940c0e180d00740c6491140394200350012070348510010545080780d0719200101000e40315210352001040c00584030760030b41d5408120114141c04d43d40189001ca4045514881c4000b0301c0c0e070311003001343d61003103500d9040102e030f103a040103501544802d0703030240c4040070801420902040b20a80c034220307480910380f0303003400b1329000c0100341a08918540c08903031002c04008401c0d551103074200c0440d6011a40240130040500c040364800c45141d104284403403040c01128035180d1641c00866454100c0d134000c80c5d415881c0c1005004241c816003a90081c2140502003658454480d64080e4582c2d40750a40c00042103000f100155595460750802c804e41a0042d000304241002414000d14110045807080e0360341c0d09203842004235a03c0041d020810251074201080340c43c00f42801c081080d409100421440c4640d000b40d128032034000c2c40141541552040015a9103217546000000148 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 6900789 1250 6899539 6899551
    0x10f020a0e040213050a080f06010b07020a03030e0109050a08030901020c06040b120406180606031a010e130305071a060a09020c0c040e160305010506010e0f100c03140a0504030605 79
    0x401802400000c680081090318540c80c100c0780035031a010650b51a0240c030085501295114200d20400100d8400110f0200c0010818000f40c4041380c2c1c0350500005184191900290803010614040010034410341c000e000c001414513014541e140c1c6ca90003e045100181c129a040c0e8100080b0441c4c15030301040500d441c1107084d03543c5401d06203021480d5103180604030303c0700010185100080c04000180e800004a5804281820030300b1401d0309000006041c240030403212602d510340c4503a01c0d9001d40300e0041c108c0d0001c8100b10290382e1040351943d11166864011011700c041444201c0004590703840703034a034040c4034420b44907a07803808108204621455901030101c40348100404103030118081060400c01d241910081039000038000d00c58a420b4911001c1e40210600d84000f004010040d0845405908241e854001440c140c400b08280d100994481d01d600401c078030080fa2401d4051807241558600a0920300c0c40704c1c100004156441e0700401c0c00000185e000a000d00c03c010301031240c1c9400803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 6902039 1250 6900789 6900791
    0x90303090f0a0b04171306030203010f0506070c0504020c01110d090b070c0803011509030501180204050606090105030105131409060406110a0c1b0902070606080d0f020303070507020102010b060705030309010f 91
    0x184180e16110314003080944090420034506031640300c0e0741c05c07000441d20080151210300f407065541c1d003c018000d400038080c0c10040f050342000040c0700d20342103090310044c83d0000010840d43c0e103040c00b044002e43c000c2d600b071802135480b4100b03000e20352050f402410ba0b07580300c1d62001c00e1004881c58284107504009148400f40803261022a001c2a402019607041d6485408400311803003804009607000138060344000d203150b0800c1c1105008125841e11360030524400ea40501841d2194010041d030760007104140d80c0024407d000401c403520b0000110004440076480014400600c021900703120718046801c5030140d4000f105000422156110380e0055840c0ca9140034280390300040003c1c8140a0005e000d0016803036105542020076615401e28001d2413148801c6503035480301d241640140407a489020306901807200203000f1540520f01291105019901551035980c1b4080300380c030240c20840c0140d0466680301c420030300c036442d074000404d80180030340021510b900c1c2404c04c7e1400c0d90203040003001d0035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 6903289 1250 6902039 6902053
    0x6050703050f16050409060603140603070b0d1109030610030302060702060f010b0705070b04090c030b0906010c03121107030c050c100503070c060b03060a090302120a09030f02040f05090303090f 85
    0x240499201158200c1c2c010079508252142c10f0000b1602030095402c000c1070f0f945010b00000307140d078142d07200c00d48110446140e410143d90340007c0544640b904c2c4114802d40604000c200020040c60f0302081607005001201030800c1001000b0074036051085411103500d08216401f8424550100034141c2d03c503040384024005031611100a0414400610804d00d00100218528040180601c101000783c042c214800351529070750724400c005080e4044040c40403d00d09240343c00d460502c010740c50301c90a010b0b1188500034456650441d40400d0030041c001070305030707204480d10300138080100602c0074a00954410110000501300b441c20300c0c10010840d8481c078001c030444501240c01a041e203134001ea4600b4001c1501d009418540c001d800f104880356414000c29007000700c0d0760103d42c0f025840c10f01aa00701c3e009981e600c0034140c0c01d031059620100102d182883e0410000d001175182d0810148040c1000c211508928011003c4c2c6509407544d246a800100401c144104200114010000200010840 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 6904539 1250 6903289 6903301
    0x20102070b0a0515060307020a0f03031505011106060f13050106050d0513020a05010807020c031c140c062d1311011d10020a0b010b07110d1203090201090b04030602070605070305 78
    0x26182e001410178010790020000610080c001c0c05000580d9401c210000304100442c81d0080040c10500f001407140b0200c8000070846501c5091204c640302210001030a05480f160100080b07524ad5001d21a4004224401c03401000030ba406503078000c2c1303000d8464507108d0f603c0b41015426500c00414500003034909a042d0b0340944d495000440884000f0b0130203c4d03107a280c03a00102d003459207492605400d4424003a030121301702c105243c01e41c00510f50b40e9565480881180790b22509115851004031658018801301d4840c079a01e40c1c07201c681e520510072825082d41c40e030f403045200c100c1c200d80003825520090070103c188a031401d51400e031f000d030918103280d00c5203108440c222540507002c81d9074002c05100c03e00003030841c000c001d0304005a41160401910350380d11801d2170303115446007400b10707110b41513420b11950f6401c16540c0c202c9101c2e03120a000380440c042c54012801001100390607030410a40ca030000071101c40700c20051029600a03240943e940160341052001d0b904040d142d04105442c000400c00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 6905789 1250 6904539 6904561
    0x3020a020a020411040803040b04090b09070903140a0b0906040203100203010b07030e030c03010e0d02010c0201050c0906071a07020705010809060103080708030406091a0f060d03050a030e01150303020102070b0a05 93
    0x18070650440e0000303061000e14481d5a220300450300300d041e49200004000c600020b0340c001810407161002010f004107103800d41030103120b4805a4828020a104943c240f001809140c100c41e00a8051002c85900890356107405140c100150f03040742c4203400c1403061102754101840745018985602c031095245525001c141c0707900e40300e82c15020741004014910351034580d030103000d03041000c14014020b0100341c25090f480c544034141c03c00c00c00050741c6030946e000c1c0b86c00d0060048078416a40500b031395090007480401d1001550004408540c401840b2515509040400704424020ba480da401011030a08040c000341581c0350180440006034481801000000e01d41c50446190399404242e10f80c0341c1d00e8510780000a0811910010302800100001040c521003c6605a2040e01030400d40b0360f003078640d08140f1410350a1684080d00050302005203811550082c2c002004c43e001110001860014010100d90041059002100141d4001071448180000d518042da08482c600504000034282034081007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 6907039 1250 6905789 6905803
    0x180c0103020a030204080f0105060111010b01020a06020703020f01150f060806060313080409050708060f01031407031d0a050f07060504080304030f02010507140c03010509010c050d050c0c150601020d03020a02 91
    0x681015000200385041034031a4042e10000c007444400c880a00b80e45036041406031004407002e6000071804501400245014055803040100680150280744c2940c4c5408020798000542501075100e0380c01e6507091042c0900c01d210081c1070354100d011081d801c108030301ca030f0f150059004904203c0482c0c18800c1c681d440c0c2d002c498125900301040207110009203405401c5020b207038000107810345480208060207400200040c480c40d422103012007002441d10055040f01e4004848039962002400010b140c2c0b4080d0b4030114008100307181c1c00008940041c50145803150f4403800f103d1743c7e00b100c1040104202c0401c0403c0151080741030083c1414102003900c0e0303803401a840301601560364404e6010644e4021011250040d81008190301d6030000002d4895a4004d070380901c500942c689000199084c0041c8200001002180d6885c0c1c603001d90031b034180020308000b40c100d0250f01402c01035071300c101c0d10030010248080703c21071903041645072a82c006402e00b0160700c1c6080606004012082025601003414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 6908289 1250 6907039 6907063
    0xc010e0a0b03090715020a1110080a0b060d020f090a1409070507030e0a03060b03060106020610030f060605090f0403080708130b070905100201060f050613060c03030e0d090e18 77
    0x142d031a55290203680349803400a601440000030020720052246030301080306500d80b40520302d402d14920030358043c0080e0090a084600010b40000c0c00314200c0001900301030440c08c80140981d0401c02d2a4081000300e0344410040c0048110024548240f1304022004030001c2003814172000648000001017070060200500d0082001400038540d010103004290800144002038103507a1102e44a18152000307003444442c01e482842040000a8107510010b0302501c13450340103020a40142c80c1d41d48501040351801c2c0c0031502d040d181d42010230b99449140d003862280762000b07403060b10f500b41810050055903002d000c22040014460800860300e00030741103040104d40c0304004031011b6580390300448480c181600034550102030b0448800781c5aa054000340286c40000030380d04207403951801001454410f01124006502140c801080f070301d8001e000108245000b424045104204000b402e82020307005456100414001e5106101050320f64014683c00440e00c2181040040034038105c076610038140e0700e5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 6909539 1250 6908289 6908309
    0x80d02060408070f050a03050405011701050a0603090201090504050403052503080c0702190306020a02010608060114060a02030f0c0102070303060501030e0705040c110109060506010806060a0503071b0b0901060303020c010e0a 98
    0x10030400c02645021030f180e01c41d0007001b510f036400f0702e5207801441c660281c0310f200e00013458030105002144003155128100d950060161101a10f00300040d0081c10000005030305201400c440010252900c0c002ca500c164841e0b540c00d51303207043d2814003400c50031610040c503018581c4000340c840000c0d0441d030400e800071103c951658650150748002441900d41111203080050040d000204015940d009000f2074000c607002801581c3d200c0f1031103a030b0703a6800d101d00c070052040800e00003c0c506003900141080c05040c070680c0d181c0800000c0c1e5000aa10aa10295950b03500282910525a062041704054171007440c051011b02da040d56a61398908031400b420b84221790784c04200f40c1d010301485254000104003802400742819072704142c001000c00b280d2040c045040c060004070340c1d03e000702c111104004142c990b0388c150703210320303030100c4083c0c03100844400f11130041100c1c01b0110788003105103441100c440c00042800e5042d0f2400034100b00121003003034180700e0401710340001c503598912070300c00b51055100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 6910789 1250 6909539 6909547
    0x6030a02070206070f03091401141e04030507090b0906090411040e10050a05060612070e060706090f02150f07080904090206040617070203120a0510051009060306080d02060408 77
    0x1106800a01c1031440003940103000040b4101046400000c80d90070758001c1c1c40c0c51001e0350351204802c40000308540658005282140050076075164074020304908041420301408082110020724030691041c0c0003960039910002042103468800d0050503c2010140c6041c00c181c100b100100e52030020140c0001c0400c0700c401c4c03030500c1c203441d40e40c448800f050a003c103c0303000100c00c0c0014001010305a070001245401c000000b005400c0110880e404403400c00300c240c1469440100c00c45840c0d010f01c600360f070320460400841c00400c18a008e003081c1603005024a107001d029610402414540c01030104105400500c52000c044080710700b40e48550307400103101940e404110b00018001e0015101c02076100074003150208000340d00210800c00813030a41c550020a840b100c80c266a01d0080c00c3c0c01c51001c6c0707103510010b5040d145030f8000f81e0300310050001c400f84490300e80740000c400c04070203000800011074038002041010390500450000340240d0029001181c82110000d40302c03a0002c0000d0a40300d0006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 6912039 1250 6910789 6910801
    0x11401090b0d02040c090509010b09010507080a02070b0d050108060609040512070303090602040906051017070309050309040518010f06030503040b0307090315050f07030b01020a0210090305060a050402041107110603 94
    0x81c003144943d00038810840d00c0b6400001034030484035070145a0207114001d00106040c401d50003141c180b0711051b11881d0901484d9a200724883d4880c0e0301010450148190004848010901405000311003010100703c541c1008483e5107000300042c0141c2c494a44402480f000c81c01c0422510081554085034668400c21030405401400380800f0040003a440010b00190228141c1d0281080e41d2040390050154a21100111850b00c1d86000c04020400101e02240d001c500079440307051001d10940c00c1c6d9051844290004c1c0440310200c448010f0845c0c0b40d000d04001103420f2180d10a8004240030400181d419902c910340e40740030701d0007148690b00000001c10a094001c0943c28021588a00030310307440048141c02801512054a40c501e815000c4c202040301e080c082e0003032081840c410f900800c41040e040c2c00304005000c940380100148540c0c400c2c00310200701c05008044c4104010680401c20341040c1c410b10003290298651902c441406115800005d110300840e4142e20204903070846d141e480710 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 6913289 1250 6912039 6912049
    0x70807030f0e070f08060606030f0105040510031a0103020307060504030507091512120905060c0c010c030e0d05010905070b040b0a050c011b17010f0f090203090f0604080714011401090b 81
    0x2c20780d445400d1107450000100c0094480c440030075140080b0070f0711a5615024140f04050200b0754145420015140040c0881c0c1020790045a10401000303500c9040c6a49031500c0b0f4206d9268007049000320341000c010b10650904010354070003050146815450700340b640e00c1d0242c4916076170040d0300a96480d510522031000400c2881e501a120040708000303004030510f0107407c4041007a000c1008102480300010366032408000399105c4520b2800039040e24611000110782c0c054096000f2414080021070030a0f40d519502c41041c1101d10a03000028000400e050041c5820b0041d40300800e031348410032083c4000314200090358040020350030280c0e1541c0010703524a0142640300c0074007400020f0383ca908199a940202d405169400c0e046800d91640d80b41c101d04013058403d40110560b07503950104c10412040240d0040d03074031100e2101600c4c8040761402e082420050280c4041c3c81040010448005101c10680b0f0300b0146061807000700059907120329041541081403040c80c000c4e503620f02680c0003d40354 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 6914539 1250 6913289 6913301
    0x108130206090d2301060e01051503090106170708061312080c040801050c04051309030203090607170406090608090304030f02090403020a051006090c020f1005040206120106050702040e06070807030f 87
    0x1000c1359645020001c028425a00c803c1c00200801ca0340c2041c100040150310004002e043c1e45020b09a154903484502e40f03025207600182c98448035640c1c035600005c06100f8014003450030380c141c3c0c1c00f40a0040ca0182c0007440c1000190104280f000340103e450300040420901000c40d490508042e00300e40d98068504000303010f55445140d0710b5080c042002118240384000f802030314011210542e940803160002c6045812205004003d688100301403400ca00c0d007070010340f8520b40305c1c0f843c4181d031404000c6445810b42159000c1c2011034018441480551342042c1c50940c003031080390041d81424555190111103e4005d50085e01a00c1c219003c14181842804000412500300703003164601e20500e006000202610302c0b4540c44a864804011002d51001c545100d0140300079000f4500600d8000d840d100410001e841203034000b4040104501c202c200100e400e0080100e6203855440745558010700c0141c1c0c0428240410a402210400c4802d40c2c100c003c094000410340341c0065045c1c074001c009802866 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 6915789 1250 6914539 6914543
    0xf010306050702031b0a03110a0b150609150306040b010c0503030a0c1202180a050a0b1801020106030b010b03010e0c030405100b040f0603050717011407050706060f0303030e0c0108130206090d 84
    0x116004154050100010000b49691190b88c1e1500034034603580c0c480380c42c0c1261a400421910780d090209000002d190050440a40010100c0d8504007029000400728170340704042c0c030b0404a01004001c03032850b1034400c541c4220001c1c200002042c84555650b40caa12005142800c3c0d1540d410320b80600c503210f00c3d81101d0b616940c2804566440e000c40c551181301440008845c415100a0801308a17030600202010441c7c0340782c800e131402d00005250310000088001400c904641d0382c9c13000003002c034036000a2240203000122019540c0c3d41003c44400407804001c01ea07440c3c0d03240410070b010014000140310302c80380c04920400641c0321486170024010700000d4001c0340d0018189240413090020201c1e02c007084910141c004240030481c40800ea003070701d0040b00c4034031b1240708600000301c1d01c5006400801070b181c8660720005100f905d400c20700c40309088039001507001a135a1120307009c0c070400410210200e100d007400c0c00c81c1c071031600d0b009101e04014900402400b80d5000300300743d180c41d21030038200d03035001d6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 6917039 1250 6915789 6915817
    0x20a02031002070609080d1d0102090307120512040f0608011508070305041407090e010506030c010c021201060e010605180102070305060106111606111006030209040b09030d0905031b0102030f01030605070203 91
    0x11902039518005460520706506284d41400c0b480c023014807052003110310303085000e40079154840c81c1c44044000c0c418003c41c103a0f081e000704840840c4080300c40c401800a401c442c8001101e0030b00b450030042c551001608a0840c1002e514074810006400c0610b0a41c0a44940b501040c155503601d0314100c4500c085010100707611402901041d40803440e08400c04864504000300310513903661041550366031103444168007156100740c400c400b500b804001c0541540d0000004100a83d44104070200000240d202e2000100b000c81c5000324a00280c00c0450156400d2006107010b500303584a10340c60f901c0620880c07050100c141402501c0d10020b20680e03400140d904078103403141c2d69400000d40040507490502045014086440d00302d226107116101c00e5070740251150f00142d940703a072216003005000d80400c1c11440b091042600300e507290b00411244c0d0b44188c005d1074503440b80701141410a4249400c800c0e059005108001031407500c0021a411203810034000314041c3c6800e1416420743c4540100c0b00858 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 6918289 1250 6917039 6917047
    0x60102010912050307020c040908040306110c06040b0709050102010207050c0603090c03070b09040509060405060408030408070f0f020405090706080406090804081005190b01020c010e010207120b0a050601020a0203100207060908 99
    0x110f83c000001d103203c1d00301ea400741c0301607a10700800c000c1161819a00101401020700043c404514642d01c5441c0003a00001d0080c07030000b01d00d02a0746030100448003115101a0ba4042010040c2c0c8008440001c02e002c2c002541042c0d02550b480d07480d4001c110f005400f03101c001c40029aa11020000394020100180682c5e95003a03c0d0505a8801c0d8411800301d07004e141048003094151000080c100d216640107005040c01c0e0b2201d80d55000307507038806001654046414880700b40854011140703428114400c20b9010003130005441840f06030341d4001c04515040d0401c41e4100011500008143e0740943d0203680010482c0042c50040124052900414040d218424421203464002d0340400d004a14041e0700f55a00fa49100e40c0710141c0b48032162450058004440e01d08195000e00365100c002601401640c003007a4403070848007105000c01b88246c4101c80c41006224038119503100300e41e0011000e01c0940b0002840342c02090781e811b8402d002d540b8480d400200801032094560182d20103a03803020340c80d692 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 6919539 1250 6918289 6918323
    0x140a020309040501050a0305060403030b0109090f020a020c010305070903110402120c04080c0409020a050609030703052d0106060e12010605041514010c020a09020c0109060f0507090803040503030301030b0601020109 94
    0x80c0380c0001c03072418003a62500740041528a0100041d50441351312000601160740d131646c0440c042e0407130080c1281888941c00c00881e864440780100650a80d400c20010f0f141c201002c0000e291000070601d59062504e043e040c40300d42544818001c044d00c1d0040d180e442c01d6001100480d00070720821042e00041c8580905000101001500800031290100100c803044020401000300f02d40041000961025007240c0070885403d11801402500c0d2008064480d0a82d0780e88400d418486044650f0b00b03500c0c0014280c4540c1c402103080814402544002000a6428140c002d82101e1010f48034510801800309420b0402c44d0941204000e4603001e04103200e94080045031211200c841d00480a0f1a84024161030484d441150648101e58000306600001403034100860020740c40800b08421954882c0038001c003090302401016100424040001202e140c5504020f000322656001081c46400c1003008101640d1300106030f906480c1c0000d08007c0c684c445c000140d00410b40c0c50b0005210301940d400441d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 6920789 1250 6919539 6919543
    0xc010509060a110d0f0b10050918060a03030c020a030c0602060f01080607020703080f040801061409010e04110918060403020a030905010203090d12051308010e010b040203040b060d03140a02 83
    0x20080c0ea6010071614640c841441240c16a064a010300c0b0b980e00341880f508440540c0c640101d841084011400034410543da00030a0020180d4013180000c10b10005840700c10313003042a03a1111598101304e41d40c170242041000115900028400075003040391480b80001555603900c074080c010b41d03110b003140a4055407400041e4590f94110380fa5020101c5a0b000068080c1010500f24480d08541e40901080d03801d66442d203d09030407000c902c84c010b14080c00302280c030746070034821032024142c02181120b05601603c100a00c8100c1604180303000300246043c04001281701c1380c0c07444450b00485005100350349550784403c0403485c001d106a40b511a400502c01410f4020030012065030003540c07045000e81c1c480c1c00690f920f105401c6a2038200c20030a18500c0840d0182160001c81d920504e881403511032410121448402d45400c40000d90f59602019658031800b4491681140025a0203505525081e103880c804044024115801031103035501c10010144100c14520985010904454a070034145500039 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 6922039 1250 6920789 6920791
    0x60114030f07020d0314061011030406051b01060812091309080a020708060c0a0305040515010303110712030509060c01110c01060608010b0903030a050a1101020a050a021005010b04141201020c0105 86
    0x1c0d025020300138400c3c451610a00600c0d456130020300c0401000e441c3c0000340214016000188030030046e0720704a40070071f500700f8401000103008955410303031105aa1584070083c00e000750111580342c0e01d0101d040041c1003000c103110460b941a42c0c03c0907143c64543c0d020845503000703e200c0800c001d01c0c00400004211008010306001d4803680c0c226001c080d180c00045940d02e4040e60004042c0c8014410207071002e2103604455442442202503401da00000d1528406c0700c0c000380c00440106580890b20707a60798074100b01380c20003440d81000c0603e2001c02c6480241c024801d40701510300a030800180940d52550941105501942d000c800d20b40d1248080c00481c000c03c0e42d40111400200320b03030000600d581482040c0c461180c2d000300074528002c000d01081c0c2e26a40501c8100c4140001c10380e01038000c1c40e082c809001c14100315200d03580d440c521002e0090403c0381c4420010026441c0a0042c0b01c1c91250340d003958162000c0c100c010903ea040000000c06850004580004d191f000180e040c000d00d80640104d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 6923289 1250 6922039 6922051
    0x803070306031407031106180d030e0907050406050403020f0d050607030b10030e06070c020a0f060207030303060501020d020d0f03090b01080304060f0f08060d0c05060c060f0112020109030803060114030f 89
    0x103088a880d81550f9035140c4030b082c07001070151a81c1c510004501d00d000402032000e400b00041d1516a1803804e000701d1440f0351200c1c4280c020810036468191141042089203610030361038506149803070300f0248050101e010311700001e40030704402400803a0f50b45549034a45540c5801c401101c3d19854043c40082c00f41800c4a45580a501e0781080500e041707010313000d903803070b00c80000c0d002d0009541c5001c0101c50705918520140d0b80800508000a00190b4a006140107070449a01904a07103046050107415208a5440181150b1041a1343c040240c3c1c0810083c919010610301a0f009541c2d850086000d03044c591f20141403184201c000040f8900000000c00031244135440e440a007103186803050310000780703100025001c42c0103400021130f14a0080d110076a42e501c10100d44808c951107802184c0760360066440b41c10258030840c20f00c416140707440911801841f841481c144000c005900007800088036100003891140d012010984aa0080d07038410074800b03848113400c0e147d1400c0c1554249148099800c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 6924539 1250 6923289 6923303
    0x17010e010e12040e09010207021e030606150706050405010e0f0705040606030203010f03060504020315150901080309181308070305070308070302030115110f0d020f0c09011401120207080307030603 86
    0x288032101c1001003002681000c4080e8410f00b400d151804055100d81d0040001105560811a000c01651022502d00701e403413040740700c90807000b0000145440d00402410341407164103006601c04d10056460116203940d584240c0109842d100c9140280c0900414038242d4a00d02a60302c1d0f001c6920400144c18044402c100c6091000940e10003056003248401c0c000d511501c22044028800f080060300126001480a01164a40d140841d400404110103131440c03400c40b8440806842c0501e44410900e02410302d61001c2c51802e2441d1001442c000c80d18003d60601e01c00550004504049803909440c00d503400003050ba40d20501864014015400b041080340890543c9001c0703007080d071013407080d0790590307501007409480d60001000548140c5008002c1c8066440341c02c6480c0c41040051129200c0140c1c590000e00044880c2480242813800f0150803501503042040100842410040a0031000c1c500b030800e500000750300b510a20184c0300b800343c00f1b80300d054000700b4880100d50685c42001147d000c4d40c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 6925789 1250 6924539 6924551
    0x3010609021603051605010603060605040e0105010608070e030f03030108010e16060207090911130501140102010e0601051005040f08060f070f0804030f050702150d0b240d0617010e01 80
    0x180c200e01504801800000e01e0320300d00000203004000030030f03401000b41c2c1e5105031003040703030741e080c0c00d50f402c0e0303041110084d484c1c0c002004282014002c54514a040300c0c0207020540c10908020020300b8020311220030460b900000b40502c1e00d0902c40329440c600c1000907240d0b42d40e112241e003400781c18035200c000d0075449103031880d146109444005a094510a030b0250100f17038902a644006040d0008098801c0bc404209800d803035907411404129100000901040f2581751000f0135100311f9040035903e040d64107005011070427450100d8854155601141c01c645200a0383c40103c1d0070b8003a54100c2003c2c06006500884c005100051191060505070b240c50038582e101603044442d4404582d001021945443c0401c2c0041d000b15821498006640341980c1058515000a904c209960740300c0c07090b100d80041c10303022087d560b000e034a12444041c1c80c01801442d000e01c1a07001d0980c0481c0302103100d0004901380450f4513a170340122000b044111030303643e003410900140da8000c100100340310301c203586017523 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 6927039 1250 6925789 6925799
    0x3060504021c030f080a021b010b0306060f060304020405091903090801060501050a05070308190f05090c0a1503020d0f0f05060f010f020c06030604020c010c090e060d0804090b0406150e030106 84
    0x2155580040c3c0e4565500c1a020168000907202000d020308084105030f0240036139801c0c03020407103100803117030900f20001c1100301d020424181040300c040c00d114080c8003c04c0d44004d0b503845007404c80c2e40141d8186c40020391580d4565861342042041180341c1e0f1039603c01d400c0c0c6414198400b40c8501030310301405c02084256070b02c0005503211310980500c1e1000c0340c4103000c0b0b680807070f0040b8481540b01506411000880c01d108542d1700403a5510307900031410540d80c0091005065040228215000c1e040d81c0e564034490038001380100a49400340400308240d00002e003000c0508160300101074210a1000a2048580c403010030f00140004803100c41c000d2f10460709c5030a4540c4510b503061a0791400741c01500426000314140416a400205070030341080e0200003041c002c820901c0b4051148405907580c880b041d04100000c0503654001d030101c0d200d545100c1e404001300b02d880c03003100c049802d8007900240e18800000840c01400d076a0703102d0040420004014607805030080032500b16460120020040a0303122 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 6928289 1250 6927039 6927079
    0x1401030506090601030209180703090b060406030c030b0903090423060108040b0601030903021207060608070b0f030a0f090212010501061214070809161206110a17060f0303040306050402 81
    0x88800e50b61110101012030810350080d401024054005407088100300c030a00c85c40702404a02740e400e140004e680395a19400d200d9450700303283d000380080f542804001d00e19260324001c508503010180664040c100803c01f900b01c20012105290400352090004400407030074841440d000000fa45150244000050b4882d0b2044082900ca030340d22209200707480c1c8605004400900300e81d2002c4040d4403400282c1c500e00c00540c0040c09516108007004100075051156207404c00a40d40d03c2010041010700038941e114902c1e40c2a2980300c1a0a540080d0030809091841c000d80b0607014081d41044500c2004c1c0301c40403043d08228180c81d51a120f0328a03003a400b055850485a000c4004009507440c0d002040085114401d0250030040060464418610001e40310302041120341c0044004a4090403040400500d40515903511083c403c0d00d41c144240040081c100c15034503420041d01000d003400041440d96201e44c4032404c0c0340050200e80d160780e12864081c004020503141a4460200b01d0082c0d01c201400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 6929539 1250 6928289 6928291
    0x3010507090308090607050102030405060a0b0a030819200105010e0106110304030803130507120209010e0c0d0c0908010906020304020f0d020a0603090c0522060602010b010f110102041e14010305 85
    0x120340c0c0d8801c1e5103403a43d1941041c60704280f2545902c1345c2d0410449003c01c1d02400511300447c0a4000b0303001a0030015410030895182092950180240000c100003140d440416551028180c900b03022609820381422210f90b1414014010a0310000c41c0c0c0740b05091056000e075040e500320850a220300d0742c0f00c13501642c000d03c0741c0303419654951003044140001001c100246401c0300c40035441e0b0900134030b1907803000d040c8a100e400c08a046440401d0010642ca480b0071440d004142c182860000703800d00000600180c8120a07042e91070903220000c15103020310031644d00004042a400801c1000c1c85032511304d019510680d42648610042c1003440c0561030843c001c100c480d58003c120300c040e02e15050058000d800c16001c10349000030000400541a1544241c05e1040030005074503144c0013a00b00c060340300b29003094101d0307002c6a00d00081d01040d81d811201d0038a8a400e9814100c1e550302000b40003501a2207560810081e4265a03d0700c120a201222128000e540a94000e0340754001001c00440440b48 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 6930789 1250 6929539 6929551
    0x2011409070512030417060405010b0603040201090303030506010c02060309010f0b0a050616060609020a080405100903080c070c08010c0504031202010e0601050402070204021e090a0f0f030305030c0d06091406030105 94
    0x1040208002c0e0b0301d0030b060310990782000c810581c0d0405646d0f04c0c3d44906410002d540c100e03140c00880070001041030030f125010548900f180c0311429421b040d00000c040118a001c01424165924040b4005a0040761842900d03a0300801007680c03440c1c007250309406403280e1500fa2040c43d0500c2800055860021202015204058803c5081a0355155041c07101ca04c00c0d542078800b5035503180041808541c40c0001c020a080c16218201c00b410240307400340c9800c1814923904100c1c6d245c5400200020350100340250803850303038a1001e0300d03406035042120002035107610444030b079841c0c410582d21140e04070018008480c02401800741150b0f0400059007a0b0340b130090021441c4d0415801404145041d60107089001c6c0042c000504143c103903143c00014200c2c1c0074500307210305404500b1305510301c0d0204924001d004c4140d80030b0f0419180841405102c516804010705210010000600e50340c13848042d030740c2d1008500c50038081550744e040c01000038101000f0034641100c0712030015134581814050f15005071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 6932039 1250 6930789 6930793
    0x30f03071212151503090b0c0f1b01150b030108031c06030204020d0f0e010605090406020705010b0d08070512040b07030c02010203090607030e0a12030f0807092402011409 75
    0x1036540c0e07407400d0401d14800074005000c03400c4400b016025540c03048090b00543e0707946140c1403908164090250400c42c584031001c1600f03000c070701000641040401d0344c100048600890312441014070306015401840810320b03c240c60089006050300e41500304001a100c00207200b240785443d10107a041a1109020710843c0d6070003005144510700d80740f02100340c2100c19090008030035860f80d0002d0140d07400b903140c40b04025101c0a801c0649131241c858510f488130154001c200907817401e8081103c40c9070050015080030307800f00e000d005120080d0006594042c1c024400c8050100d43c1c41e00c0751a07030300884820340300c500c1001d07881000074000d40c0c00c603400c0d03e41c0901250704080c0d042e03030b0441e84100b54101c03c80c1103001c01e01001a0540b14240604083c80c440c0c0c40c0c5400240005050191050003940098002c0e0420019038011030381000e07204d100301034281381c030401c1aa9850001d54455510b5071008079510000b00d02420305503045144106041d945500034480c0c6c8190a81c90600901c1c00d0710400559 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 6933289 1250 6932039 6932047
    0x7080a0f02150103030e010f031806020306040e03040e0108060a02030106140a03060e090304050312070c050d0c03020913050115030b01180f0203100303090602030307120504080903060c0a0905030f03 87
    0x8a00600000d0991086441168101c410b003668529042c1c40a9008502141096100300e080303680081d1054181180d503e070400c4040f6804440b03d64101c1e8941024042c1c40c0c2c000042959519290031000c1524089000c8940d200d03a1541c0340e0907558800d1080b21290301480d00071130f0300100f441c000c40c1d04170760031075544980d444400420700c8200d40c040c820307110a01d43c0e58200040d04003081c088040c441c04108003c0c54980c3e20b0b200515044c07841e20054040f1440d000c0001c80c001502240761141900d1054491942d44080e41c42c04655210142c0c001a5005020301308200711508520f16030103e06110704003e0003c6c416030798402c40c1442c55408018080c0742408014008884d5007440384203070030001d460120f0b4480c014007030301049900580c0c0c0700c00503183c0d180c414814140c20a075110000c0a680c07000b985149007000c001040d00110300110308045e5298008203040c042004140c0d920090000c0075100c8904241c0d14100c2d0a5100c0185100480c20322a4006803500c0d010503203502c0d14025070041c600d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 6934539 1250 6933289 6933307
    0x70311060f060f01050a0203130e09070603020301080d03050910020309010c0e09040201090501030b01031d0609060c04061b03050405030d030b04050106090e0406090c0e040305031506040302010512041104020c01020702040e030708 100
    0x1d150016004901141304c1270140050040414020200914600300740c8505030602103110f508080c3d09030070803400d0500410040011910000709054910311920380012176440340c0c03051a04040804104800b00790001c020b00c1822041035001c1c00e21001a91240040703a1942000c0c000c1841080314080d000c180154002c000c1c80d40030703400000d0744403014500042c83c0081c2c030280f07841d030246101c4001016032002d8100004080c017040341c01e41040c00d8100240c1818a0150000c0c12608000001460038400c18070b1002018020010f440280400900b59440c0c483c0c0590000c000f4523500e04110301c114144400042c910740503082d181d06540410781651507542e10741c0c07586c40290003900012914103c0d4100000f4042e400082c140703000d10305c265142075a904100e4068a20ba0407003910b070a10502080004000503038115084a00240a01d4099580340d615810160040e00020111351b8005000088100580350194002c181d080c0c4222401c0108500c180071b40307956402903900041c10745204002040b030b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 6935789 1250 6934539 6934547
    0x6050f011d1009050915031216150203040201090509010b070f050703020a060203030a0506031207030c0507050301020a030e070e0402150c0f010f06090506010e01080106030c02030c03070311060f060f01 88
    0x4240058441c15020748000c0002007403564906491410000300c40305014000c1e4904090003d41011100040c0d03290340d03c1e2070001a0b1645e010324007850b1b64840000d8410380e00441c40034103400c0550003002080712200040c84a001a4ac811a4200c0c0020501c0c00089001c0c40c21081c06d505840247c4801402d001c0700c1e0b07607842d540060110060b00c079407181e5080080140e45101a04010b407400e907003c4e5840341031040c25501654000303020f40340f00ba040440b420066000c900c09581490350503181100c452901824071504080264104a0301075000042c01101d641e0503810060b04024101c0844403150740d58032001c5041340080d00e000f940006400c0d0b05034031000066001c1c0c903207007000d14140c1c0c0d00d201c0311451503404c417441e800500030a252101810003000382c10b4420103910400a0030091100300b00e02d0002032030554140a40c4003415661501030b100d172442002622980c0e80010100da0341c2e600c1030f00700980383d0281608003452603c03800b00069003607c1c5402c1000d00544002d0450303203030410b02c0340c0151 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 6937039 1250 6935789 6935807
    0x30311060f1506090603010602030403170c0a0303020307030e0703080306030706030e0601090207020613030303050f01050d02090a0c0212030c0c0601080a05031206181e07050c06040b040206120703050703060906050f01 95
    0x80c1e4807507424002540f9031783d1008001d40c001c240c59002103903118a0b52074404201c242115500000400500100100700000300341707455125030502c2c00603601c3e580c0150541c0101000d11000f501c41c0308402c0b000c01002050402907001b03007401c070111604d02d5900e520860a86008003c00c00070f07034000f14010480c0c5032050b0003400130148000c0c0164204003458180001c0602e103580150b00081c0c50b0800d1140705c05214802c1809004103030b410080444040e0041406144080d040181482d030b030300384050007a882844075400c0b00b242c55915030b45c2c0e0706140c2c2086003246c01070b10310044940103079000051000c1001540c4070880340e10501460034180c80c64011a510342d00200b4554000800c1d5004c0d03484983c0a5501030302c540c60700038403446000e10401c41c6000601d8010914030134864200140001a040020300680c0700d58805d139a40101d0343c40c0c5c4040303102409001c49a85e00801c60f0010b018881c2d415411003403040c681035508104090303845840105880c140d201c0c00c1d07080f02c404440c168403544510025 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 6938289 1250 6937039 6937081
    0x901091205010e03030703090201090b0307080f0604060f06080411010201050103020102070312120204082104050109181103040311061509041209030503130302030712050304060507140a0b01030311060f 88
    0x3e10b215401c80729a00310f82c82125494000ba90310407a100866802c021650003501d051010749046240081d0080c00c40d040c06080345200700709040004450365100e0308070402402165110903507060341c0c0d0303001814051003507808540c443c19441d4640207552052013154100ca805a0042242d1451034aa00008001ca411504d04102c80f000e030325844c50001e400100700822042001b0034000b001d02c3c4025545007000c1c44281c806070801c1008001d2681e201424030190703080802107081203022584a0750050840030a000c1090707101004000500d43c0180105000404074003c1d030b100c5a4404602c000c030350440d004c82ca0740c4080303c00041004210100e0b035046c2c0303001c00c0382401c18480380c5039100c41e4a190485d007202d81440512400074821424140300a0009091418868161034555500c49850340602e000c1c610070810b000c02c0090a100f007a41c0c0d0142040248000c0e900c11f00e0190800d40110f80003408241c020030302c60707259010015000030b001c13445030489800314482900d8040540420302c00c03039501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 6939539 1250 6938289 6938291
    0xb06090406090209010b07030f230a0302120c19020f06040b040201110a0803100906030804090e07090f0501060806030303040201020c0906130509010e01150b0d0209060f0307020106030201110102090109120501 91
    0x1002c005072110421030b0302810041c90840c0d291011494000c0010500805070341c100b040079100c01c0514885090550303c881180c110060b1074080075401100240a1140e0310000181b5160910881c41d140700300422480c00f000707500c2c503a00c01c23031007406981c1c68055010414555000000250100b00350a410a410030705c1458040b8007010201c040b14a041c4042c4070aaa00c5400001400f0310a00300290410003000155414071046245d5212005036009510451440343d0300d8110500040906110307680c00703000009003c0241ca100030a40d00000c000c240175460206d20020302051480c50004140c03881541e05a0050991140d050140030b40f120002c2c0c00150408286140400740d10418052036200f0200040006004810850709600b92581d010400500e0900d41d8414882c4030301800807030700015229580942d0340c01c00c010108500344240212074201880100c03e20140c203506401c0700044034000d07a58104110305413a0800d08130710524107a5404200030366000c0144420a007000d048160103000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 6940789 1250 6939539 6939551
    0xa06091401050906060306070306080606190e18121204060b0406090f1505010813030509060f0c0a02040b060408030a140c0102070b071e050901120603051209010e030a0b06090406 78
    0x42500b59181a900015140c2000c002c100260504200380d90b07100c0364038076091003d02d251400c1d6035140c040180030a0301686942610b82c00754460020041300410300f00700008017600d4241c114056000c1d521418900a004102c00d4114012481d4180d4103424404c21041906855560780c074402030015600e221303003054944800142c01181407141d07103516955140003041c954456609401c1070803451304190305020310301e030521040342d20030082072404a40c54145956140c20050019810f0f00400302003812030540002c440c0200000030400000b00361083d00d05101303403c81c074402c102c4207020b14007420144d54010b02000c003c582c41011001e034203d03890a8454034082c0041c1100d82a68060320003a66220300410500c420300c2d0b0b0150900b640120805428821404603a070020300c240709070000e90741000340708803031010b540f103159012800440e400400c8542c1c5941e440350250054101e51411404030703c0c40081c024090601080b00300c100780d8860411b880591b121400c2004400e000b60080e02d02d25a144 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 6942039 1250 6940789 6940823
    0x30b0c030106090f0e0117151906080105010b160f0f03030c02010b030606030d0e0109030f060507091401020a060902030309030d03060f0803040503121b01050406020403020f03010207030f1b06020d0504020a0608090a0609 96
    0x203d40b98080c888027050161708038818006503065410705e80c400790b0f40307130b140000404c00303030030a03a040d0b0b100c100448007103d020103c2418a5902014810300252140500d903500704201070309940100e01d11115034009200314800c0e4820141c43d40300469000b905508208403009005101da5201c418107481410314032403481c0c41f0f03240c290526285070402c944050765a41800140358008842000030b00d181c070030f2072281c2001d50340000e403910316840d401400103440340c0c8250115a000d02c00c2d19424840641220042d090b000360007000741c40184150707000602c040c080400c5c01900802210150380c4003600910055005401601160380055030754038101c00d80d00b0624084907003e000f600c0c003440c090400561141e04500400c00c0032100e5450661282c0c0c81044103000082e00704a588480000c0d50905403000e4080403084001c0c0342807554000d105c01c0c800641c3c4464425103a00c003a000350f000752903419890b078440310f00340e502e48400d44804041e68002d1051000181e0141c02c4001c903a8030500405402c00224 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 6943289 1250 6942039 6942073
    0x17100f03060c02010b030a03050f0306060d0c1e02030403081207050c0d0f030b0105030105090f04050c03150f0903070503030a0b0102010b120109060b040203010b040e040c030b0c030106090f0e0117 86
    0x5030400c460300c03a160303141c1c144256070901552425882c1200600154203241da00505140301d8203541200061001c00010410ba40c0c100903228090581e020602000030280c4005049084d030403440c1d0000700141e40380003d0940f001040e20300f5a40d0200d80c5504d02904600b500c104900001d110104004081040170034006003400a041c50f0a0300b030b26014030441800c83c0c0903054a1602030140d04100041c0010030283d994090a41e03000100c00c510078800e070b112030800364141000d801c07560341c0510403101e01d54196103411110a105038a201e8400da22512548115601c9100d94440a44680d10a00125000072410b910500f4184e5050000042e4803403520301044010310b410b980007000d41d549640400500503180202c039074a0808460841c990741c14261000d59a0045000d00442101250001410001c7c0981c6020103540c0001c0006140d190002803000d00303910034021980002c0c260303080000c0a8549040369020b4039083c4108450316030030404641605000c00300c00f8103440c800e00d8601d05040c411 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 6944539 1250 6943289 6943319
    0xf0c020d0c120303060902030c0415230403020f030307020105091905130b030c0411030109240305030405011d0d030503040602120f06041503050606060c07030b0702010b0a06030902011710 82
    0x1c18401d05103a0b5072402c000c1c0c2110300d60f5000c8020f40e801001001010b000038811541500c0400035003400340070031000d00302c13415030083e18040c0603071002e0b200f84144a140c4030042d00440b03100b01c0d280750030381402c8414541c403030050b613000901098080c454448a8980403115000700c8a001c020020b0117503540000580d6510030141d40c503480c941e01c1d090404941024427000d0f81c0b2010a84081c0051010690309101610052048501c2d440e42d42e02c0c058044101c2500100c0383c040000030b2040c0c420385a0a000b070700d07540140b11b000d01103000c000b1102e400f02000c002c00c04c5081c000601d4082e004895881c19212544014400c84903190b08102408210200c00445d50241001c2840c0c0942c0e481e040d01800104c401d42e80010b00005400c2008000103100001c000e9800501910800c1e125040401c0d854941285034000500b014064402c100e01c0070750540c0701c04034108040380d041001d1075484206070101c0b802454042c0c00206d980c40982184d8504204130f0350130010035001030790055540c080980702da4003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 6945789 1250 6944539 6944549
    0x40c14070c0f05030a020d060f020706020f09010201050708010e01031214120709080f100e0309030706030b04050105060304030c030f090510021e0606091302030a0204050408030f010906060f0c020d0c 87
    0x1092000c144482d5018002c480054442030740140101411900003441c00d0b01078400042656440c0c0e0b400c010b81001744d8060740ca01641c451b00c150744420319101b45162a402040b034490044d031034440007814043c806e141c024100c80c02880c88580070f9080d40c071805003440c5950303584018859000c1056000c00e4401c3c00400d2141c0c8030340c80c0007203541848080240608081da02000d401e510405035403582b92800b0030801d9207400b14620015822002075050b60840c090400f0342507041c010207900190407501030700200c845900842d001c0001c0e030b8850301044610301040d1005000144225203040c002405440b808884c10001c0c10000c000039036400005d400c50414050880040c1c00c2001200b124180d0721108108041018024090340c0c0ba2450101d91141e0008164100540b10a004642991002d002c008071a5401034420311080c6014100600319600c02c2c0d400e0000d031084030000290580c01c91040c401a501640c7d208001402500022507403580010300607a031144101808400280094020100501c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 6947039 1250 6945789 6945803
    0x6030405010f0507020102090307050f03070b0a020607020c030106060e0d11040507020a1b0e0f070c060203010e090f0d05030a0b03100e010902090714030c0c011508160501030614040c1407 82
    0xc042c018030109441c005482d141c01e43e03005200c425015500800c004058a1080c0e4280050350300100c00a40f4086551f44101d8182d1030000340c03254540c6e03010600901c950119001c4903201c0d40054203041c22035075148214000103419402c0c0b140b5924200e401000c0c0e10380510300c10319059030800002400c40f4800d44807000541e001c0308082040200c24000b81c00c0015420501c0ea580303c2c500b0344909003100300140030103240c0c07240f0b100140b541c2c0d000352400780c40c42e0b4028204544a603110341039400c0078002584c9610040c413500b50811000c200001d02d107190080c0c0d83d030300c15003103803540c60034940070b414101e041e281d060040d4507411001d824148254141045160004960342c0100d00600448080141a401c1001548142b4502940c242c0040f2a003050103584200c0c4e07075912401c2010f0041c00b01c00b45003420001e400900188800000949196908050700c0c4c060389030740d07950015002c41d540b911508400c07141c0511800c07403d28041e03004501081d070340e042034039115000525900d043c1e4002c28041341e0360 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 6948289 1250 6947039 6947051
    0x102030c1203010503100603080301030609050a0f050c010e04290102030c0604050601030303050f090a030804060603020d0c0801050a0608060a02090406030c0603061401030506030a11040b0d05010204080607050a050a1206050603040501 102
    0x26190411104403194151b072410000c843c2991a0042d1510050201514503030700d51b103d000820004004200c20f140d00141c1c03210039500d461800c0c545450003003507083d002038207070f030980241031815100310b00400d21306542d11101181c0450001d0544404002c05d07038194001844616541981448080d1040340316001415040d070440c54003030111803004d0f0484804c0304007542080051070000550342c0c421601030800443e1a40e440c60024040c16041c1c1000b03411007080400e240410032403d0a1030240ca9801000340080c0c4c5e11032030850b0441e1018450301259522000104400a4007039009203010103014202298651b12070b119108550155070004d80001c0d0341e170500300081611171180c074051201c01d1a00b8001400c0200000e0740d501c4450101418280800403101d1141c0d85d190321901041d00040c00307105900c080ca04101c1c2c001e4005109400e0540034110000e0541d0380f05000719018644203450b4581880c1c03210104036014101039640e0041107275a200c000c2104e170382d410090b40c0301f18400e02c004551 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 6949539 1250 6948289 6948299
    0x30a0315060e03030301060e060913090201020105060613060c0206041a0406030c050906120a0b030d030906140c1b01020408100207060b0a05010909090501061701021201060c0201090b03060102030c120301 89
    0x204200da6001808001000c4640c9445030b40c003200f00c0e4115411071902c1c2c0b00b81c0381d074403001415070300c9200e03ca242d01c0385841020b442c002009410004209000b60020086595014180700d0b0324811605012104007850006000c4030b03000c0d141c2d90400074000b41007682825118071980c200d0700010010080c42d044045410000d49134107000300780f840c00c640d14050341011811000710316a40503841018426900940000d0b48210080d845600c103950000e0403a20748085210f00940140040f86003a604a4284072421003004200300d4520300400c0d04504a9140280e0301040680b50482c1205070406550200000141d00d0001c029000412440d8100143d5920242c03500c2e2044520075202180103044c603900800043ea0021030100c12101c3c19000400c4404061070610b00400d81c9030003d804450030b81200e003500310030540c06807003510750803801480340781d8885a05858040e00c1003402130004000c094240540d500000103103030882010b004407410805442c152505080c1c405031319a482035004401040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 6950789 1250 6949539 6949571
    0xd050703120c030f0c05030702030105010b0d110f03010608130b0411040608010e06041101090302090a06050a051806040c2006071202090105160f0c03050304090507030507120b03030903030a03 84
    0x8680c80e00e003802e07511202c003940c0181c001020b18034104d0602152001400601901340100c03000c0e0381d40107000300401e685031071b46900150030000c0481205d61800b52210039040700081140c1060407111655410345c0e1901c2d00859501e40d00802c0e541c100b4070b041e00c00c6000070351040e4331700d801130b4030800341d0f074480401d12001d2004840e01d40c1d2000070260705200b001c0540382404101d10350007a8010051040c2058014010380d048100d0398002900b15401c00204400d414844d400982610001c445400700300356142d0420a91031060f100800c54506458042489450940d00c901320120441c100006034420207402d8107174071006620300680340d420103403c003e125548139030203010000c40703040e00f1820005001c000814038003412944d0442e41c143d0b4242e550601c5a035800c07000c00143e000891800d819124903245850b900607202d24141e0030305101c04104401c0c0a400f0b01407044180d692900501d8800d400381e180584840455180c0500040100d1202610240300a00745000f140d00c0c0071921928034a0004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 6952039 1250 6950789 6950813
    0x20a03030510030b0403080405010e070803031005040506130203090a081803010c020f0a0204020319050106020a05010e0604020f0409020d080f070c0506040308030103030809010f060303080103051902060901110307020d050703 98
    0x910754014840a00001360a5aa1160841d40514004800b6521460b209004010b8107180201c0b91140e000c0014010600000451150b0322000101b04420f83c0c80c024041951000d0b41c18a5010b513142080c880624187e074043c60344441000c2c121040d1000d00e032a00310803980900181c0508041d5a00140010304003401030402c04d00c1140700804d0300d000780e241c2c20790300ca01141100900c616000004a00b0300000b44d0015403e41111a50411055030340320350180d5166010744049604c0d5003800b95050358030101140c1d4504c615009000714a07400d07000c10801005002c07180c0103c0c2c2c02500a8500c0000c2280c4201030310460792031802e400d6031010b01d4140a00c0781a40daa0180d40314030002c01051000621240982e8110390741400c0c0800c00382c5500501c02d0141007903501000c1c90624040000007819030210b100ca048070f010f5002d40d00030261824184290001251002e03401c40010884281c82d944039100e448214091201600d00f0101c1650010ba103a10000f007080e503072680042001d1080c018094248 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 6953289 1250 6952039 6952051
    0x3040b090601030309050d05010b03010c0503010602070905090a020f0103020d0c080612030403020f0402030615030903040906060e100e040b090a0f0b010804030903120504030501090b010e0901090302030f090a080a03020a030305 99
    0x81c1010361450b60000c0501800d8018079000d81c0c0c43d101805c04100b03094005001484c00140240942d00d019403004010f40c109109200042c866040006580145445824061070802c000340087d11025002c0c0104206004081810544d003040355500b040d12902c111a0400f800b40d917042d070380d41400d0040001880419042034083c3c0c1041000b0401a510301c0e004030075100c42030f680075072259113480c009440700c11486240b4003100c400004002184601000602c1603c1c0768000c01c100240c0c4a85088079403642c1c4881e0250450054811046114040c48020303030360b10340c000d101062913204000812150702040c2c074007030881a01c42e0029140714003d8000d03108010001e10740800c4601d065200244040d0341440098a54100204280115441081140c010750741001c001c2c0400c2c01985001c0e0b500d00424401c01070702e8400680071600c5180180114500190164010741c140001c80415150580c04403a41942c0a40e0b880d0380001c1081084c03141d020f00390f0098000d440821201d040180c295a07000300350b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 6954539 1250 6953289 6953293
    0x9050f120304140a02090106030504150b010203070f05070803070303150b03070c110d0f08070201080f060102070e100305010603030203180103060302090a020a030b06031303090803071a040503120a0203040b09 91
    0x34400440010280d0b903000b074001c0110500e00d100401c1e0340307051440e40d500103500f000c2c1d140000b103005501a00894040c03403098448130480341008050104844601da0b100b4016001005244007042151400e80c000c24001d0b4103503800742e03a6980c0201d01d194005c4404070f001c20303140c0ca800541c2d16403509002d80280150700c501131540c07038034100c000c105d20622080103101c4042c2031010b422545414a40294856001100344e100d010701c0d0511030410b2308944012800512450002002c01e00c828a143e4080c04041e0010101035003803480784903028900034211400c0c175090343c0c0c0000101300240101c00003103000c2c1e0083c42c1e0300c10300002464482117141040c0ca052605001080005840d0395035140c6c1e0003822070b00d0060f1203d4041a04030082c0460070300007035000401009001d400c0c4106001c04041034800e80b510030f0021341d1110695160300070104050035050700d940c0a0f030340104034003a519034818410b4040d07a1805405904072000302d001036891000385540841000204841104090703000010240 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 6955789 1250 6954539 6954553
    0x1202031c0e0103050903030606070f030318060902030d020703050c01050703140a0c0308090606060906070201030f0f02040501020d110d110a0501050903030610032906090901080c0103051006020c062a0109050f 91
    0x102d1309c10b21820b81c00801c20541180d000c030516119901103070000170320070314014441c1d0b11800e141e0090139078098181c0c80382c010340002d004140d0000581c07600f140c0c1c3c030102800c2e80030184001902c43d500240016014000c3c984840040710007030b0001010340d001d482d241c0c1006004a400c00030f15804c0000d000b249554007907010701181d88d982a0a07a000060100c030b816644061510040303010b0041040e04041c03017410503050741d0280203030f90090415200c082c1d08807078a041c4042c0c0d040307481000390555071003d41c10040042c0700c111321038601407294040d0941100c0c6140c2e00b1740d840600310340040b41d41c0107181e0404070a016079494441803000c130303400003071405000c00303000340319203400c505810f144501c420b58103d91402240d440d05020703958040401440c80c8007660703542954503112144030b0702c080c2c006803620f80080c010b000810340e080140d0b1100c0e030040032501114030034407a09500455104801c1800c807609981c1c480710a01c0001c140c0741000300003013980e000381e240c010700c0d105092003540c1c2941c00c100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 6957039 1250 6955789 6955801
    0x50a0803030703051803030f10080f07090f020a0e060f0f030a050403020606060415080702010b041d01050a02120106050309100f09050601061125030804030f0312151202031c0e010305090303 83
    0x542c0c0d04800032300790f0b107a900d403038000310044001d00c01d9002100d580a10483d000b181200400c3d554100c501050301070204180f03200e8540d0072486641142c20100740c540741c2c07125850500d03034003030102480e03003c01da1481c2001154050201c2d4008442c802001c0b82c59404002c03c2680c1404160f41025042d10030710704203828220900d402442d28404034042212560001c4d8445200b500f0840000101420402202c40783e4907040d0f0204807041a0004030350f0904010a0107a945031084903600003c00f0b026940ca039007002c0040340c8a5002034a0b0780454030407007800189c40020781c0b0581003110804000020b900313050b850316078200941680b03c3c43c00c1c00680101d18031496008100700304810b0031124141481911803146000f8008503800140c04044040780c00b00c00c1141e112790070b40380103000c1d03102c0d01f200c80320312007a0b0f1061307541114007107800c1d01c508c1d0340402103c3c0c40c00541c40c405c1c600c01004d40e440120756601c003504400d002c091001c005541ca0301089a5940c16105440d001000300c2d003c1d500e145412 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 6958289 1250 6957039 6957043
    0xf08010605010915080702120a0302040617060d03080901060902040b0c0d081005040b0a09110a18031a0402040e06160f02010905120a0908010608030901030e0c030c19050a08030307030518 82
    0xe0f6113800740800e810019006600c00e1040440040443c802c01c0e4950303600040007002904940a88004950241c61840b010746002e030300548107120007045140c058600c0d81d000c491a1170083c001c8100c88d929004003003208004e0340040c2020f0320702c1501c065124225021903925020b0046408002e225a010500501301d00010444040d2202520003244540264000c100b108030a980481041c07032401c0340c080150000342c0018031080d145669950f078848000c2c11074840b011824400100400456440c1c000c420002e1811160300a0006000094458114107414205003040361201802c0c2c900c14240041d003900403035102c11200c25031000b0085104165659075407030030f00c6040d02c0a0032002088002c5001d12400104024041c0c2200038848150785407a15035480c1c0000c81003d000c2810b14200c40640140000c0e81250700c00c0050042880c0745188003807050f20103e8030107031000f815403890041440e45424450900a145070381c0103569a18100b20002d00321200541600005480301c40001c071a4100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 6959539 1250 6958289 6958319
    0x30a0f0c0c020a030b06060d11071a01150f050409020a020a0215070f020d0519030c1703070e04051902040303020643090e010e09010c050c030a0311040509010f080106050109 76
    0x20100d405d4071103031036680c002003040c01082c0724140518204411910480708182c0602501d5114881542140042c50f20050445209010754049c0070480120150528481d10011503c40c4250070418506a204e44005081c0e90000300b00d007025902000c0300c0d60071418010441d00c05007000342c0c20700342030079070a039034808000d030681e01c1c082d2061058440d614140b10b000d000c00120164007a201e1900c40d12036140c090940303c0c41d0300c1c080e512980d12594002035001e8250460380f18141c0c99851000200d02c810410000b041c001d031200f4550850b99200080d80c0c2c1c034a200510245009400404d4640b4100742c1458007101c00d01c95003602c0441020040030841101d80f8094603031110083c04884035400351004641d814900d51000d0b942003070410000809000b0b03000c00c0c6001c0d0700c40034024401c1d40700014043d83e0911424051100da40e008200001505100c0d9014100d840322040b815842c20355120700180103140b00382c01c25192400d2180003088190024070820000780802c0c20f01c04c0c501403500c2c2101c2035001c9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 6960789 1250 6959539 6959543
    0x2070504020c0c0406030f052b081306050c13050303040f03020d03030e010203010608010e0702060601020c010e030307050607020c10080105030706030506040f050702010f0e070b03040f080c03030a0f0c0c020a03 92
    0x18021424082c000000d22620355001000782041120641c0c900f02090401d01d88076094843e80a50b46c584100c8240c80c0034414642440071560000d06405010b08441140340106800701c005401c51520000942d01d00070305024607401c00c02561544c0d5900038883c0c40350b03910361055102ea07104201c00c004510b2079103002d5080302d8046541280442c0385040aa01828005140c0080e03541f00000101f40176400c42c14250580728001409041a0342d07000090340d460b181542d04c980542d00100408800703620907a001039400c400603095074201407560761740d03900d40081955010090b0f0418105194607082404044804000902e4609051352502c2d0200391070fa41c0d14041d01d8201901c0310005496031300c3c1ca8102e07480c07609840034208911712308031300c0080c020150040720300180380c00c05460b01035020000406c0c405070ba8800740103038555103950ba6800000b40c0400400c03a40d07000280300c604401e1006201641c072840003e540800c0a104826404041307a92500b4030a0a2145681c595405621100f0016095a03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 6962039 1250 6960789 6960791
    0x10608060a030c0602060a06050105090d0212120c0106140108040c120201030902030d030501050418080f0705070317030603070914160306050301020706021b0a020105071203090804030308070908010c02070504 91
    0xa11024041080c1200c40d410140580040e0f007400500341c0d0b800035105115114009040103441d403207600444e450b00c5200802c55010000072032060241c58031403c102c492801d0700d003c480c01041046481840c0740c1041d10084016503662004101d06a07541e40400114107003481c0404441c40d080d918600000c040d0f005031019444c044484d0310841e400303907100d00c01a94000f8100d5154103207541c00140541001d000b5240600d09280243c4201a000c004800005174812082420008a0700d000d0391503800020b010364803882945000008100420345952109080310200d41d6240382081c00e0525120b45580700340c0880c2e00e0305400351010b010f030380c00032500020000c07060040e0145016045024208036000151306510005609081100613801812841100c041031552200300da074540352240604603010f40407500800103540024842031410350403400c0c0d03040004160400392580191600142c2003100490104814050040d402c00b01c00c5008010a400900c0b084445d220000d44884140c0f062500075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 6963289 1250 6962039 6962041
    0x9010c05030f10050904060b0a050102030a020a0f0f020603040305040e070c17090102070801050106030902011d03060705030a0207080d020a030528020a02010204050d080918070801150e0d080405011412010608 91
    0xf0007000380c6100040c54001d105c0b99140c2010f0802000030400c002140b44158060071002a6950021054803800081a0050700082d1043d4444426040000604032840e2004100d110300580c0c3e20006140650f02907542c80c0e4980c1d0030940d03500c85808014017600c040c49900411240000d0b0145000c80c1c000c0c10350403001b038640c510080140d03c2c20b00c03240c002c10915400c00002180265050b44610744050003640c50b1140c0003901101c05e5540e040743e0f655103030190410400504803038054401181c200d11000c0700103207011a20b46401c41030760040840e80b1175140c1c00003080801030390b16014080e0449c2d411030318490384031007540012401824690440303900315004035800d0141c6000b9819100201400780c08840b19070340910303080d44c0030350041030002d100c0c0010010306132200d80c425100038400d81a5441e100c48a0f424161008140c1c4038182a070420002501c01c0c0e01010b031250548041c00314801c21302c49440d14140720000d13042120000c100445420144005181441000354060444203542030035002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 6964539 1250 6963289 6963301
    0x306060913060306050601020d0311030a05040f0b0106080105010809011a011103040509041a0702070b030406090206090303130e07020a050c1002010e1f0b0109080d0f0302041703040302040509010c05030f 89
    0x781c00781c10003800c41ca20700c1c103240003050102d2500024407400c026400d50b170424080c404103404a0300c07248802c444480c418000034000c4440743d8001d0360014010360402d107400b06203580e41c4080c400c1c240c0220002030300010040055582204000b50030890000007806038220804240c0060346034000c0d904cac1000240380d11100440000d0040b42c0c050400907042003414135050402111910b031001000b2000e160700b0b030018075454404130340d00090305e41e9040218607580b00c0d07440d5140030304040f00099038428420444010599401c00041100c0c107003040c200ca901a05c5c100391404144c0e4010038800940d04030209080018030045a10101401c048a6034030310211707040400ca00600340408442001d203c1d02e541038041010f0422801b00c0c1c1405110f00780040401d002c0110b07001500792186119a9200c4121a09900d001c6d0f1950030203240d540c070380103041030765a100e00b0b9100c1d080c008501000c1d4000203018415400c0c5409480d500c546014024845a8000c0c200100f49200081171400b00500d64008196 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 6965789 1250 6964539 6964549
    0x3050d0b06090a031a0a1b05070615060f1815030e03040b030103030203030f0a090201050301092310030203010b060a1b060605030105070509040c0801030201020706050904090203070305010e0601090204050603060609 94
    0x1800c0d020142212410644a18010742440310351402d07a16052050300021b50f2851046c060207440034140007034000c0428690b20207071001e40061008544407a1070f0010b100b030005000110300001d2131141c0d40c154200d00d8204c8050702d1400a448207080200f0b4400c0c007802402203540c1c3c0a80f001196240001d43d00c03402130000750443c0960b411940c18200300000001c00d00d075002000c3c501561030144803400907200c8480c60403c884010000a022030800d2004200c6007800c0c4c0c2c410b0000c01090441c00840002d40320096078134240031902484a0340103114140300f9410240324015400c8000c3c2d460514080e1414400307400700710400c2c400385845c60000d68070000c00000f608010000c00004d4028091405c00b20009440c9400c40c440721070203645010200d00f40c0500c81c0b191241200d40680190203402d081040c00c8680da0f004100c40da4020340c4802140005880402c1444021070003103000040f85000211610304000e01070f8070031080c05006000500c0650b54038000c4903045001141c005075038140500c0490 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 6967039 1250 6965789 6965797
    0x904240e03091507020a0b07020909010605030706030e010b030601032111030414010207030516090b01021b040c03061a0301030606051f080406090f050601141903020906060f07080409050106030903050d0b06 90
    0xc0d0000c803000170002e001031040015110341e0380b088074120310ae59103030460346080300c0c0c0b54420503034542d0000c8400c201c01e6010740c1c4821150419031002207142095500400d181c03540a03481240c0c80d06808541d407001c0c10301400300d940803110b1454646440b09960080503660b024038051024a0401607444100b260300800c030710b10007103512100303031591400f00940546900e2a10b02c00c8150003800c085103608198400b0400080341300340c01a00e0b110580c60b20742440014030100c1400c5003455924140410b241002c005c240d80050008000107a40f90305514080060b04c40300d500840c0039010b4004480100240000c01d4000b84c01a031070000d00302e82cbc032820444003a050b1104054001c0300d900361a60240030011813201c0c103840005100e04054540f44c014444452182402c1640c803868200381480107203401604150860350080c06542058104916041ca99001010840b040305000500f08881d071800d01070035004040e2420200308801c5070f5140540a031098404d0407000c10f0707a424036076410381d98a105403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 6968289 1250 6967039 6967043
    0x14060a0c1403250213090204180602090307050102060709061103120c0702040b01080106140d060302060c0601030c0602060103020d0311070306020406021f0513020111010b0904240e03091507 83
    0x10000655460101e6450381c2c010780819060b40500c0d0a4810003480c41d00f0501d8000d0b038040c282481e0602c0300400c001c0203081e5a50100e0b0f00035190400c5040d40c0c405035010046440c0a4080142e880142200300340c5017a050354446419504031104000f541034001102c4000c68140c0d04201441d0350243c8040d60a5110309040708043c42c2d07143c401d1200790b89085001c2c00519100303560411141003240e00548420500b407041d000044d046107401e0f5800862040589106044c0520200741c040d00d81e070009429402003000441070b83d100e80010814400320f100301c0c60003003071707640040d00184d4156004100806800b80c0064144002c0c01035000304c0d00c404105290046400a10464032507869120080d200d040d050012000000c080c402610b05d40d246100703084c002e5a54102003000030300e8584c01510305c0360342e007841700740b0035541d868215140e81c40b21251a032050388900c64515860149a48544001d509100c4a0908500e405030340441080000304413204160104c4110440b0f0041580751415481130b0300300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 6969539 1250 6968289 6968303
    0x905060a0c120c0204050901060e0a0e070503191709060d091a0705041511070302040c050403060501090207020a0e0609150d0f0503090f15090103020306040b030105090607020d050414060a0c 83
    0x190600940d031004904500d24800c03101401b507515100303100390a80700135000d240c3c0d0001e00f81c00801d0003e030701540200c0310030038040b041d5030102d030f0b603100000d080002c040b81c907800b1825400410341c100108410307000303605245040050308214a0750086002800350b4100c14400941e05c814030f02c00d001c400030556001c1400962820302c41d161005004005402511400e56034104801d42514094041c03056503214403101002000b18524540800c005440d0b49071103042841402c000200101d501409603134040c3c0014039015a50f48076a01c140302c0f4042090340040400945c079001c0c4041d036581c0c00202ea40220303414030358030304410791400000d06010039141c00600e101129041070040050110203456941c5c0c040703d03440702c2040b102d014862a40c44024803024080ca0803c0440345940c002d6000d160016005840000d0b4110001c002c2403c68005881c02e44007a0300c05010001a9036040140c440500160301d061070600b0b1912007040c031f098405000252161700c0100d9041140c611541052914a8018803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 6970789 1250 6969539 6969563
    0x105041505180616050408100903020c0a0605030412050f0d050105040b010203030601020307031b121d0f0a05010c1401140403080108070e01050603040501110c1501080105070905060a0c 81
    0x2034180345121122000008031414071002954440301600849030010340341c0c0151095640b0494030214400d00c00302e0007000c2c08000d000200f210311081040600d6002a0000020040d003a810003a2801103000400c601c82c0d6640c020522060340d00c1000c0e2030f0444da0152140c10b10700d186030402c0e0341c14050300d410307204100c4001c40c010340014442c2d045181291001d03034081242102201c0120f03180d2004858490141e80b0030450782c00040d1140e6240300403000001c00c0c1c1c0f00320420503603660700200d050b64010400a18001003c0c000182e40464859070700d1022154100c2205142001c960100c14a103e12410300c4070304c404103421300000000003805208903034001c10110030900320007110398074142c4094000a42c8080085035250000070000140c50080c00444407071381c6072000700b2030031754402803040700d0035506e822884840c8844075024003441c80e211006030039a0340105401d840c29540507803106a4982c185014080c1d0345400071914400d580065400c551f07100343c3c0364000d03034640301201001400681450 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 6972039 1250 6970789 6970793
    0x4050a020405090a0902090f0403020f030a0512070c030909020708040506030f01030c12020f1002030706050f0105030d030908070201050f07080301090903080c03040506061002010908040e04061b09050f040608010504 94
    0x25008000b40c0d01d089940c0442501c0e032080e200100c615001c4025000f40c451004070386180d28042c103582d1311910034811922404500c0c032110741140c015140381c0010600102d14191030460081c1029801030032407900c0040f4004a8500a00d1650203100d121f0090350300288190034480b282c0101c80182c480584243e40c0c03410b0a50100200107400d12064488060740e4101098803101e00da07000911540043c00c007400c3c074811004000480980701501c230150b20080000c400015000d00032079100341c0c01c1c07076801040e43d894002414203059151a0304170805103003001b0140040e00034400d40d80d003c0c2d028070b0500d8031140400c1d550301d40c900c90b43c0005018500c0210000603080c055800c641d074981d100b90b803a984e4a8445002c03a103481c2c002603800508a4211074001032150902545103240d42295200100d50030340320f900e0b8010310b0341c007e402140380f15071036200b0002031054a010700706007045071103008000055010f4004001404500a40780b04264080d80d480c0581c0c0d8580048019100941c020821810b0038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 6973289 1250 6972039 6972041
    0x518070f060201060e0103080304170405040903030504021f02151f0308030402040c08090303070c020f0a030b01050306010605070b010b0f04090c0819060f14030102070606080a351804050a 82
    0x1d1140c000158207010300030032a004180080f504076688100b40380d00b107032565514186d9218803006840e2480c0070600000800795201e000e0404076502a490019040c2003d005025580d1588003a841103125140e03410b0a000790b00040d180051641c4040590107a100c3e804070f00110b40394500c000300007200c001404001c1c003034070500440c019407003282c04002d220110b01041d03d5403001128404031580003400020641c40c00740c440c0e040814401020308626400d5500003801500d00c4d90801e40d0402a00030040c403540c02e0400c2503c2c05403c06044c4039081c1425075441050a41c014000c10444040c0414602803140c030340780640b801f600701d08006012285c88040000e00180b03085602200c0107681121a003891020380c070a103002d8506500403018810b0070205551405180c0c0601543c15641c01c01041005c1161482014080d14402002c3e110001150400da032400d0f0030441400d0a83c0b003000b0f07a07034605202c51004112200c0c5003030740440d100c181900c0c60007403000080f0722041c0c00c2418034013041850240303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 6974539 1250 6973289 6973319
    0x209030717100501050102060103020105070308040201090e0a0603020420032403011118040c0212090607080c060103120203030601020606090718060306050a080303060a0302060304020316060e120606030d03051807 93
    0x2e6014104aa60703650401240c1c0c0c0c1a081c440070f0b000c180204036840110b840f41e904a98803c1c01810060f42c070540c0c0d1a402c481d01c0404a5400c06029540e240174000c602d0b150140000c0001c01982c1e400e15045262923001c0944005801c0080e031181402c0102001540d41c048002e012800070700030014015140c40d800d20300d52209080a40c85000024400c03c00e05c1c06200e011a01000c540c02001c544074010751042c00342d0720501d0341d20ba016005102c0c1c000000d509900504040c000c0a010b8200c0b5451482c0403a50500d2188100c0155041401040050799000842035800401169410102d0311502e0041c2c1d14182418440219603040070401314955030141c201c030046607010746801d0380550761003100707980702d004c1510002d5000411503030401c09450b00c00040c6401034001400d80d04060480360080d00110b055500100200e080e1520402d080c0c44d00c0819103d180c0d03a100041c2c00f481c9003410010b0785030390301020381006051780c880206400e0310001c051501e03600445801c640341684c40311a01224100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 6975789 1250 6974539 6974563
    0x4030c02040b0d0c06051303050a05010c020115080d0807030e030a030b0306010503070305101104050901081b060301060203030609041b080a0c0b040501050a03020a0e09011404050a0b01020d030209030717 89
    0x400c0c000c0c2d0100d281810303141e20821030341003000c0d030702010b0400b43c00f1212030b40a50f402c800000800d2001001040c0e0605c502c02c00107115000008a0180b41c0c0d10103425580c2160340038202030079180302000320311008a5980403040080c90b101034541d462000643c0100a5156840068480420308401698056110011040d01201104d140fa80d83c3c0302010388c1c0c0d59890100410b607030000e200061584e096900021340c2242c88080c080d042646034404600a001c0076400380b4250350000501061280c52081d0401126100780c0300781d865503041070400b1350790f072002821031802495140005410710081c1c050b0210f00036408000c0e501d0881d0703941b01203030703480f0a94101a100d10076010320001d03449840404860450708103868280c1070002c2c0c0365040d40203410605648051004002f800f51403641c0300313480e0324064800c845003d10b0001100041c0002c07a100141000265403810343c4c15092a030300000ca07003104e960207103409640c5182e001c2c0800d0508856a00c40070303402da11029502c0154102168100c0822 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 6977039 1250 6975789 6975791
    0xf06010806060c100506120d020625080c090f0307090c180608070c0311060f0405010e0601050a090b040605060301080a0312060609060302030915091f15050f01021504030c0204 77
    0x144414040040e81d01c10100c148250750b00c0003065031501a45034100c2036114000801f4240b40c3d1580700140760812015040c0a001600002e0400500a0760a0164015105c07039164142c15641e403010007401510002d403035922240c90100e040000746c0d071810020900c540014068441301ca47c1c6004060240148024000c082101c901071080492002035602d8100c44a5607100202616034107016a012605110b0036000c000b04000007408040c420401c00d401500c7d030b82581091444c0a00f403c5084540c0c9030000102504144010446a0b6031081d00c0030613183c0c2c0103400545036500a000800400071503000c07d4004a0110000682400200324010514001d880e1241151894902c400484c1c507075000b51004234000d000d05014851207503001d158001024021a030b680080113100d8422807800b00d500f2a2541d0000300340500701401e02c01c410350300c0002400144201c0c070f801801c01154001c9070103114000e140c41010111241e20030800001003041805140361981803906004001c0000d14509038029 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 6978289 1250 6977039 6977041
    0x601020607030513061a10030e030a030b0d060e0a0b0f070806040510170a0303180807080f0c01090c0602011508060c09151201030501050f060607061a060a05040905060402030103030c03030207030311030f060108 92
    0x11f501070b00a0b4544000d10303401a40c50104140c00c00c1d401440303240b6055422180b402840130016002d44185403282c8a00d6006103e010f076076150642c2007036001000c1440c0d92524400b171190f50b82c0c001c0250b030b8200c88112004121035403415210780c00b0710401e0f0310104540d104200c0c0c071f0f00c2c070140100e0071101c16400796400b0700c02008990039a40c401e03180e482004140c400204480004240b141d00a481c2c929202c00c00f0618200345da181013801c0da036070054207680c0b00c1118401040030540902c00d41041c64504250f800e100c92612949545400d0000c0100154030400a03081d071a6503121030b50003000d401d03242e2109403541c04500307880038241001d0000311071a600c0c20b80800c8040c0001c5c50328511415008254910b00702e52980c038503018143c400c028285040b20038402401c1c075921032000d4601040242d4076240c0783c528220b6201c0940700003030140340c0158030400040c8082544a88052080d80e058200980d03103a0080c60101c00070816900200084d0b0780200c07e000144002d0951980504002d0381c40c0059 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 6979539 1250 6978289 6978319
    0x3060907050607030302070c0512010509011d0c01050306040207080a11070b0712050c0a02030105091005010504050903040e100807090603020f01020d0905040c020a17120f0601020607030513061a 85
    0x9a00101d0181c90b901450502c200f000081c400d400800d400b41c840c1d4080d600083c5e80c0d40204d0181c03440043d24a44994481c030810400072401d219112411a50216a0440344030610712261210381108602c0c0c104040003000403201d8807690115181c1561240328255100c08503107005050301b15041400d00700e4050040d0005280c030b90101035034075481d0400c001c2c41c80c2404584055989600210f10782c01c01c2e010307136200403026a4007881800c2c0b0400342c0102070701188204000b50802c03200148c01c4031744140e103402e080c082003007000001d44007501c425004445031510782d6801210343c0050b9500c0340301c0500c40d08101103141e100d650400d804692080e00d08c008140c3c842c1e00160384440b4244222030005180c80010051807505400c400350250300c500550b000c52000c0d807907100a03000c201030b501c4100f542c005889030101d2900c005099103c401c0400603107641c2031040c0000d40701d140146c980b000705602d40c03011a41282e28820740e0307040a03034411001c11144111b00185105c040c518070035548a10040708403180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 6980789 1250 6979539 6979543
    0xc0219081c140307030f060b03010504060803120c0306061204050a020108010e0708070513030203030f03010e01050303040b0a08060a15031b03020703090306050406090b0f0604050112030c02010f022a030609 90
    0x100081c03607031100626442404500c403540e4000504c0c200403d074990703141060401080c0700750000740c09140c120795a2981054184000c3d18540e07400409564000c1044507905408042d8140d00011004041d1fa903d40321a0700280c07403406004c5810090036680c1041c0810044000384d41000340d4400e8960600c07a80e42d54a034410906012079001d800709110f2000600528800c00080c00c0d0099004540580141c4a40210f4a0341e040413040c4519210004018082c013488204014014101280110320302410205070080a0148403900020b0040100c045511995103c90b00c1000c0c00085180d07228207400d221000700030300341d4035002e01640c60103668440000c501c40d00031191102c1d00b648811019907c1c640d01d5000415008000b9150303207540d282d080c80011005a8418005c0071016010000b50500d501000f003182da06071700410007007a812081c400000e40200d06582e14030b8090030401b180c40190385090703003020b90404c803804506440a2200e01807035114888441d1080095080f107a13540d03103407001e5603 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 6982039 1250 6980789 6980833
    0x1209060c03010806060d03020304081b0f030303060310110405040e030d05010e060307030f060612031107080606090a02090a03050607020307060b090f0c0c0f1603051011030114010c021908 82
    0x800c1580201c0000783c42420100701b2030309418420b204980c9090f5a4003107542c103001d400d8020411980e02c19202d0681850103400090000340c0444c05149181413640000e55a01185101c1c0c85140b0386489116030004614000c2c2d40090401800c240070783c0c224001c255449502c403100440005280900100300107500b820382c1c6d8441c00d800f038002e0040500f5078841e540c20b051a800708031100c0751205000f0803080c0008041d03031895403283e03c0700c098528084002a04280c2d21340c11903129940900c0420100383e0320b810f100d580066203c036005a603840c0200104c0d9001006420103002440303030130180440300c0d034008001c00c005401500200200444881009680c0b2011b82d5403002c0a0301107804100c00f83c84d074900a00b0031005090480782100030103180c181c28000c6c40b4087c2c445010f89500c0c2001880b0007808030719101140c0e50000c020181c840c691310b001d40d000600400b0100302d2103042511442c0d01231610700101c0d03600100f207422102c0c0c08000f501c400140c21f0150407000d005124100ca1103001080b410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 6983289 1250 6982039 6982049
    0x90111070e0a020c0115150207090507050a0c050102070209010b031006030b0f0906010c050a0b0a0f18080307030902040203040803150d030e040504030e06070c141009050607060905031209060c0301 86
    0x11007540c44181070720020303401c0b0156001c0c45550360501280301d540403148520040c42850074450199402000290402c001907001d028224208020090560b41c007400712010780c020ba003031109000000c1d041a90080c00740c004029040000e07a000491b51603805406184501a600101c2e0386c0162035200c03c80035245010139940c2c1140c50900380010320b00e80b00721015401841858030365404c4000c0d856107880c2050307005060340d43c5010001400f010552034058044c6440c0d031404103004482ca88100707a040352103103800c09842c00030044086641980700303400c8010056002041551241014185045503a109030703001ea0f82c04088000c1800d0a0074000c900300c010703540688440010700d800000f80000b8050060048042016600c14041295a09005084618010088110b003179080c15a0740b10a24070403255036206080042c0341c4202d003075001501c40195902500d010313071103007a5031034400003416011000502c20301010070b82e032241c0319071840014492666002151126103e0341e484400c0c903c028018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 6984539 1250 6983289 6983309
    0xd030b06030a050c0c07060e130902010507020909030c070f080705010206010302130b04090b040f03080903341202031801050301030c0b03070e0a0602070612111e09040c030209011107 80
    0x564045156440243d000c0913007652613190074240f00d609820403500d5088034000c0744130910035880c039042401111900b40c40f500400c000300c604980000c0e000340a15a0000e1017079402000080c1c50140500944031040244070858419030740310756614078119910301a800c141c2c070804100251640c0300040d8181202d13009441354012079070a8460324040d208004106070042d803544c403c04001450103018601c203138000c1450f01a1800c852900811a5002030861310360b82e40300b88043c10078900a2040c0a000c048403843c841c01d0f8000d0210601d144d4100e010025050082d40040310490940101c000c200100c052541c0f0603400b4511720055405000030700020f04201010041130150900000086401010340d04050030400c8440000802901c0079411040041c1c100c080c040221039004090b0101c03501c0003c1043c4542403510360402c04078050300e6034103800308150459804141007a042160f40d5032401030024070402001c6440034020b035201c5080240040c0d100d03031005003003c0c000306181040e1007000d40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 6985789 1250 6984539 6984541
    0x5010f050d05120a05030114040b030c0d0f02030709140106030603030c03031109040f0c0207080f0c010c1a04120806040207020901030204020307050d2a02070e0408030705041e080d030b0603 83
    0x10302044000300340d0215028410300c06400e80c0c80034200f0180c10184c140d5540c0564960501f0071400241807103182050055007000c0f05507480d40e030040744204040009552401c0c59591138200010591102e04000e5010700895002103450006a0080228980c0d060003800e0141d0740c0728800c8045900394840900000c56030031141000030310a80205544690020040c0e0a01c8051000034003154942d8503100e249541c0c51000c40b407819014010321005250f0b10024080074590700583c161640ca01142036810000011f50369000c000d0101c03414030203061100319020030f81c50a80382c01c00c1109901e10070300002c80c2c116400203c01b840e0a008450009501412642c1c1e03503440c0d40c1c2448003035003000c6c00810620006206a600b0500284500011440581d01022280c9410078000e42c60064140b949021034001c40f40c10b005081d40184140d403c25440640350381c0da0b5494010888480c0103a4202c2d0512201d0301c09001040001030280f0416a4000300c25075080f8248100c007a0103c44140b9a00343d0400c800348 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 6987039 1250 6985789 6985799
    0x30c030503190221010902090a150306030506040b01030201020c0906060a1202090d030206010e0112020603040b060315040302010506011202130b0d180308040314120f040201030f0c0c060f05010f 85
    0x1501440d0481c0c1c11003400741840c80b04401a03016600800150072803901c11240840f041d0501e0702581d40101070a04046184c298184041054080b060103280b1000500c4c00c13104a5840c401c0c0c0c080c000071038102c3c003502c1003400c1519090150361003e11044c1c0c018450002071002500e0300700e2000740107020041c0401c4c90700204a005561507000c400403600c45d41c0c1c0c00c1c03110b5075240e103c030300d0803403030b02c511983c0a0480d40d03050500034521110181c1050044042800346000180c441c44222600250054207806d159030302d810020b4074042220b0b0000f009000b054041c00101030b0150803860054000f43c03910008010103464100c101c0c000e640c250011854403101c100803140c203020040c801c501da41031020801d44603042220205406000048001980c00b804002c18144c0c800d98030700307040071052076680ca451444628034100700c2001e0f102c2880502c480011404581c00b070b9000c0902000d0100040c440740701c6000380a8240f01d10103c080e1200760074521081100d501c0351144030305a6140000b8098021b0500e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 6988289 1250 6987039 6987047
    0x120403110109050f0106030c0e040302190804051c02040b0301090816080c01020a020c01080705040303020a030815030604050d030b03030301050d0b09030408030c07210b040303020313140c0f01020604030c03 90
    0x6800d01503500c0d542c80009501198050240d0b50001201d0000411140c0c0356140000d40340383c0c0c03984102d28414129051100203903000c5207803d030419803010aa5107011715400c10518510a0398011903006410b10340c0d901e080407203148803545060084808024031400e200c18142600c5a00307000a20b481001c021083c4041c1c110a0316a0340940180482030914107e1000b840c01c9a1042401d40d015a10a02c40440d0940c1d2040c4015031009443c541541054a5603502139540c1c20000001401d010000000030380c109044802030140100080850f040c0c0d040900b0400e17200c042905100c400207080032101c07205400c0020403a1b040710b0700500341c031118181c40d0b04d0318200c098024003480e8581c0010440000c1c242c0d020005002e029140b2005071020500e0140d0041c8409181c18103001c220600f1a07008000c6400c0c080c407a54065050304000d40d03070341c2c1c42c1501200c0c520344d40e540040007071a1944000000d04000030313402114000994401da5400050001039965460864005000844480580c400a441 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 6989539 1250 6988289 6988307
    0x5090901031209050402030f0105030705100207060305070c0503070309060207120f08070203010212040c0f05041a040b010e03010c030609060b030103240b0d08030702070b0903030d0e0a0501060605130605120403 92
    0x24501d4004851a220703130004090340c1c02661420080075040c0c0041c0031900c2e00380030b00c500500013110002e9005440c0f90b00a5100c44d100d2050400b8590340d8400116541c0c002c4402d640703500ea0210a880e6101c1e014070380649020441d009080c0103120381180841d4010350f0401ca1303607955400180044441480c1e40e1204403c0d030182b138040381c16540074800303040341201c0305401070700030f51085680c0384031035027420b00d82c088500d01035000d14403440c10103400700c03c0034080642e405108002920042703400c803035840059528400030141c3c2e641543c82c14014007a459407550110040e44c004000c02c0c4115599411001d01c07902007800040d200c1014005c01c41c900103815000a0080320380300b6008503031603610000292601820400a03181c0001c00810084550341c107110031030140032041c0d10305040051a00c080799403801425844800150703a01c0240d41510030400c00f46400c01c0d8024001c0c0409501d80708002c200b41c10541c049105400a030f02e010442c64090002e903001106410080042a903690700e0840340454 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 6990789 1250 6989539 6989573
    0x7020705040b1305010e09010506010203130501031802060a050c0f0c0604180603060203040305090f030105070e060d1b18090b0108070c02060705011a1206010302090f0907080d0e01030c0509090103 86
    0x2210188068210f4420f024007402400501460386e821301c2c005c2655070039568020150340c1113400401c001c2400d243e0062910742510428600007902d6150616150001e000a9001035400400401e9022080d82d02000a180c82c02c02d040c10340710a5003c01c2c0e400366855035014482980200c0611041c88281c9001c2030f40c900d44040010013041803a038075152101240c0c0b041d030b010f40000e40005400e000604100c81000c500780000e9000b048249080c2c1c0f401000d0140e0141880d00c00e0000080c0310300450601d80040590f8001404104543c5003046005440c0100484455800406402002484011350b1241c0304080c413042c3c407984425070f00e40400316507401c03100d04101d034080010b1000c0310105d02e003449031031100d8220041c2e504070030b0100c0e401c0000d006010030b40307007045501213030040c001038444102c3c47d900071110000d410181d45400e0100c2e82040345540000c00c0c144500843c64424a030b114030890328480342a2030400100601c24411142803140000d225005662140100002162030400007200301e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 6992039 1250 6990789 6990799
    0x1e06041502010603020108061207060f0309020a081506030609030a05130305030a03090204050901090f02060a051209160f060c35070209060301180f051204030f05010506040507020705040b 82
    0x551550031a5105012402032500143e549510510442d608040c600742c1100c01190a240f22120540344666242d40710f018071002c000f00c0c108484d054500a800280c11940e0003052030500030b4441820940c0c1c0c80e001e450054203119020b0201d40c25040100e4954002d88a14000e1450240c542000740d03080d0b0721038407119000260302040000407a80500160000342c2c0c0a81e00408e0302c0c201ea00401083d104084c0c080e5051380d1601c0000000944862a0682c41550580340e00740c07540690307041503030b1500a03000440d504002c1304007000080200031601e41c80c0d0202107940d0380222a102d00d0052980c07031aa001e041c0215103240394070004100e00f805482070400a1540700611100d000f20754400c5038041d01e075200500030001c41c80108514100c015140d004c0b4080c0d00070416a0b0f2041112103809001d007034094801030000c161b000500c0307070520408100390108000c03940d64542d2482c10b156107012002c4107442c154a00404601c0c0d51609000f0760b80904525802000d62604000800004201c048049070b402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 6993289 1250 6992039 6992047
    0x20a0306020406121109010207091a040203091e01050601080705070c0f120201021902060313060e011a09060a031212020c0706050c0f01020403081804020c010f050105010f05091e06 79
    0x54400d000400c00340125903241d11000080044444c1a41c5c1d41c5800000005000d0000d4000c0da60700203081011540170860208030b91602d031969030b550080768000c0541141c000000c000164000142103050520300d03ca107490800c1c40f0403103903800c85509441c501c0c00038070b2a1000c50207161192000e000c040e4019400c203e040b0743c0c0c40c0c907060406480c0d1ba000e15940f11030500020207641e01400101c1a0740050240e00c91108000cae400200140302c0103201820a2049022050a0141c203900c0b016800014074001c11a4481e03641052a2f0500c103000314520640d00e1200044030f6003400c81410b000c9076402400c044880100074003d40d5400d00c262401001d0540c00e204840c680d00c01003041c10300400039619441d540b0180321040074107200000070f02ca003190380104001c00001360100c0840b08404c1c40102641841104400028064894400c49415035820801c0121020381c0365400941258402d8035105501d490428094800780280c01500d0303440300301c2c0344400148801c4881d1200c03d030000148003901c0c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 6994539 1250 6993289 6993293
    0xe04030309020105090a090c09050105070803010b07050f0708010203010515090306070302030603010f05041a010b04060e150c0a0c0807080c06030402090702070f060201021e0403050c0103090503090a09050f0a1116020a03 96
    0xe0320000ea0300040d02c19481d02300c80307202141c02045050280c4001e1804910340a01511100007922062140307040380030000502c2018410107100c0d1100c40b020072810345241980e5003100c6400307034100b8043c0398401c282000e0b102d468501d15404a50440c40042c02404880c1c0e40c802d4141c0081d00018003958244d501d856020b2106c05862056500c5207110301c101400110780403100300c4a1110507003103040e41c0c0004000070b201701504407a15201c58542107a1440143c41813407194009801411110070301803050503150000c00846035205070660310040c0484130714079a2414120350303c070002e51985810020410104000d402d008904a502c529640121600c80c0d54401641210304800d502100040c0d6021869800402d01a07130001c181074120b030881414241107881d8541c0b1180f15400c014140b44c0da0700e42900401c0418070a503906490001d101c4034840ea40d400810340a01000c84440440741c0f007800c00602812064401c250b41c40a00055407030510101c0400e00d803002d040c1c0d034070590b8080c15a040c0000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 6995789 1250 6994539 6994549
    0x7090513050601110d08010311040905120c03190509030c030102210a02040302030f06040c0e0712020a09050405070507030206060603010b09060a05120c04030506090706020d031a040c08040510060e0403030902010509 94
    0xb07001766507a0781e030009589075062526440c5241c4054034132075403c00c00c10102150300000c00b00300003100c80019581e0b420303203488030620f5132192001800176040382d16401c204068129024100c1e00c40107506442d01c1c590001c0c201404c078803035150440f8089003074503800d44403544000c0010781e004c80d80391001403600e070b200d4000070320b0710403481c000e19290307440304080100300140050450010254032090b40d9450030308a0001e422a02290004682d41d54041203445881344506030600080a000e0400c0000341400000200213900c81c080503000751040c43c0100f902800c001d02281d04940d0412502c80c10095484200405640a0042c0b1820080f0902c40388840241600d1000c0c0035003e0350b400c15944501d50701d050380c1052030040c990602d80d000302e00100101d41e004038054a41c180c05142c0010b0802d900041290b83c0c882910915400c1854410074440c01c542186c040350003180250112481002940302d541d00b0744905000d4100c64050003070210b0002400b9801c03038102107205040190a100c41785011130 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 6997039 1250 6995789 6995803
    0x203090303070b100b03070c081c06082a03060402040b0d050601091a0f030c040f0e07150e150906030709030803040605070906020c0303040302150906030108030a03050709051305060111 81
    0x380d1810045820704c070510281004a100134690001014158a801c0501818400c104280640701c21000198580420983c0101200b0240740c69000c10446449151140e9900e4810f6151100310000407541461208072403039602508400400400a82d526513083c4009807182d0b00300e4175002110307927003030300001401449444c5c040d0000301d80001d96400420780c0c56501b41d200d020010302400c0003081145c0705071000724090602100a582c085006403403421000001c2508100e0180680500c83d400f0a83c08801c4004600101303880c0d480d00030103003c160030001309403040811004029400c00c9000d030142003000281d54054690f041c141209656a111000b0700d6100701d44c00c542c09907860081001083d001004000a802d2a200400780b814400c400300b030352032040780000b9104843c14400200b0320807945003200d4a0300c002429030b545070750b551511035030f50303802000715200801c0c200300000b2074180c8111489003c6803401006500b04200c0c2d41d000500400c0013400b4141000a800d0055404e900204100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 6998289 1250 6997039 6997043
    0xa021c05090103140606030703050414010207030c02030106050a150f050d0509030903010c05091507170c0303010801050105010203090a0e09070f061710030203030403080307020a0507030b0108060f04030203040b0a020309030307 99
    0x19541d64242503000500b2610030022802c4400001c070240800d580b070340000d50741c0c0328010b410002010f444608104d4022010200044910341c00042c0b8041090342c417018501c2914800c1c1c009000150b1103004110480c0307424001c0c01403112180c1d2044101c01e20a90f0805181e0308181440792402c44018040e0742034805c111064030090340001070084031400c0c00d01c241c200c00b5809252641c00e001b4043e0024581d844410050741c22810082949414840ae040c80000249406003200f5660421050304035100d070801d10405845518000000a0650012044030700300c250085c42d401c049400d00100b4003280310040d140e21440e100d4a400800e0301145c9807001c0c00500300e01c0d229001840f00702190307940d502500404001022004950810058a0000130b40701070303d03032002d02103440360b40e5180103d28008200102428502c5010000424000740e00f0549050b601804d058400c1035488121300f442041c000c1c0d82c01001030303108201c10405d0100402c0541410034481c4140c9191044000000c2d213103400030201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 6999539 1250 6998289 6998297
    0x605150403050f01050903040909020a050303030a15080105040b130f020d060e0d0201060b07030509031501030606140301020307021b0609060d0c031b0203070b0a0e100608010506010c02090402060a021c 88
    0x105000b0b22074104140300480c41003800901041c0391484041c1c1d100d010f14400c4150044c0c4030448007003190388030030181002d03003c007800702c80d224905003040740c018000b14024020075042c02440031541c1d58060245a00c280d810041d000724548030000c42d17510700d036400182540c084540c45284001641c54030703203503000755010303003000325407240c04041d00e03420030071101e0205065a00d044d00c2089203902c00f200f03540c0f0361a0941482ca803580d040c01c01280c10000c10300c4076450b50016050000c41000070b1940f02c54140c2c3e100e420500d400303441030010705081340300640319a8003503030141c00710f4585c1d00000500b1740c00c0300c17502510340d9050407107800c0413483e190800324600384a9170b10f50a181940d213138103200b03002c3c2c0d40e08903034103403036203900d41e100003030b45078802c40c140503050b88140b10004da02c22a42e074006215154446080300c01c00c05103442054003c00c160300502c0869400c0902140c601d601c9110030403a002c3d0010103000c1191525802c100c0d15a0080c1811000d40c000c0d8000c4055041520f4112014030b411034807 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 7000789 1250 6999539 6999547
    0x50a09120306060c0f0501020c070f0602100902011d0f13090b07020a02060f09040b130504030e0103060b0904020c0c030304081609060b0a0e03010b09100905090f060712060515 77
    0xa02205160032416000040500d052020001c4540c4002c0d03103080c494015042c07030018012420480c0c064429030071800128490403a0004002080d00c2585003142c4c41682500d0341003280d100d4401c1900d10f0320034040e000481c4a03c000500e1448001c034181100001417104440c0360300c0c0c0c000f10310b40e003047d400003c4817142e5410102c41030151583e1070030740c00001840074250400303965001940070300406045140225000c5810b40c0c2b2a25184c0c080448107000400c140441c541d41c0007401c0140104580440000c0d040000c91100395001c1d0003460262545001b0260a012214081c48000e401904010031240320b8450140d80c1d41d2001d0009001801d98140580071f8002c4001c01d0840e510f486501c600e80b5985400381c10020f01710040151040402c00d85041e683c0b400600c0e0019014008440b100b9501500380410b0100424407804400c04440a202003440255079401c00c1640301c81300e02401c50b41940003000050026440340c3c040821039851205e0001c1c0c071030380b5200440c1c03280840b80c1403902103d0b0002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 7002039 1250 7000789 7000793
    0xb040f0204030606050a2402010e03040e0a0e0a020616050c0406030507150503160c030e15030108010c05040506030705030c04030c060206042d0809010203040902030a0504110d0f2004050a09 83
    0x10040e44c014041c107480b46050945010016101c003003101c420003001802d14003072640400c1c402c0d001104000003c42c04c5984071a104d140b49108003400303581405034503103056a040300e180d40210b00c0b1000250010700729408c1c942005555864001222811107490003801c1d001c0c1d04a41e01c07403141101840c0240010852203050505403804245460084010f1200500801c034102180e442d14904400981c600080300c0804c0340f80070b641d2003044000642e40803003000940c203400c2c070713000c2c019604950040c8000e01c161000c180d4195100d2103503004050304000108001001d440c0104010354204011040c0c1603c3c1c40d660341c850b01440c0340d054014500581110050009001070500003003140f407480700040d9401c0000c5d4a00107080c1c017205500411106020070b0f48406607000b44241c800900081c442956685004207a00700140400c840856003443d400d480300f11581040c108082e0020b42c0701400080b01d00f41522021604154003102030000c01d450310000e4015100c900450380035908070080416011114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 7003289 1250 7002039 7002041
    0xc070c08150408090d1203050403020105010b120f06031c090503010510080a06051807030501060810020301080706030f060513140105030c060703050708090d120f02010209010f03020d0b040f02040306 87
    0x35404403806a204200745640d1500303403224203801c1544103144540ea4070215010403144088000044d01041d16a00d01c10301c2c258060708041e202d54400e900070081a80c95a03200c0310345019088441207aaa0741e9400101d618040d10312180e001080203040307503100c00001d910381c01040201c220303080000fa42e04204004a050074042c1682004019200d0700c001c0e402c100c0c0559945800300c0e0003401007511400401c1030028003485200314003040c0000d07206480e40700c0c100079000e8040d5101e2100b05104401c0c0c01942d0741c00d140700340ca05941030704000d0714519280c100210042c2c88451110108203945200018803039480424401040344215400300302c00184d601014241141603100034003e400c0f0a0001d0010fa0f284805c0b103903030540c9410615158842c030300300100c4034040d0f4450507401a40a560b0b2500b4420050501860060f05a40e800488803406030100e0903405490002404505000c0384a560340f07000790041c000a0080071000507010341034000003002d49045807c0b00401a0f40000c0c00e000744001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 7004539 1250 7003289 7003313
    0x5060103052802060a03050a060e090f07051008011203120203010f05030d0306030302030405011805040e01020702031006050a0513020c0105010608010501030c05040b0306120708060903190c150509070902030c07 92
    0x18440c0c22100d000c0d0b4a4020031454841d81200e4004c1642d80d4000a006500552048002c2d1a0643c89468946400303e02d44c1d44d95810b171540b2041512a40000050501e043c080700440c0101c150307140042a440c020b0f2030710342025140f100b1402d20181c1590680e42d003000d131010f140200440d030510305075207140c0300c00d15003440c0c1410300c03500805041100074000b00c0c1d00001120b0407600286407a40c480c862901041a05280540110342c2c441d00303090308117116080c150050308820b030084055031100d400d6110140308a4a01f40304560b00010014001c009038540300030306000040c3c0c0d2810152034000c89403445402c540c002d03004800410000c800604c641d590510811f843c44940d81040ba243c02d0600210b5442804014034141c0314070f40406881d4a540b2081c400c1c0d00040c8407100468805050500526849820142c0231001c2401c200f4829110188030b11102e562854121001a0300356030100110806814020000381c4107104541d00080c04d00c00510007588038170160a83c1544880c0d0314500030040b585 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 7005789 1250 7004539 7004593
    0x3060b0a020a080c030c0f03090315010e0601030518060f0108060901060608130813060c0201080a050c0304030f09120302240f010605070f170d0609020a0210020d090506010305 77
    0x4018080032210035000918284480d4114544540704c0c0415070200d032661095200c82e0fa954003940d072030240407200c000080c02d0030503070442c240d03074407076003008002e800000d801d105102000c00744d44046580d55029500881d00607520340c8101031281030000c1c81914201090312400402d0400754010403000c9418424507400007901c1000b44901464510010b02c070302809419106441801ca0f0b0440800ca2583d08403045090070b00190140d00e030340c0c2c031005816658020401e90201e0a039500044080f462881018800d2584015160443e11a82c034100c3d900302d40c81c80400144058540b0100b88000204880c1070a10b00c84c1e4000c1212601c481003000c0250011841c40b210a088002441003003101000c0e220305540c3c9134544981c81d5110b0303003014150100310040c003400c0c83c1920004a03880d1080e850043c8102c001c8100140100d0760707100c10120480c40b03207024000040e0484880021011a6600107000440c0180d00c0452061040d0b121603040c4102a4030481d12944140ca0455900e800c10f0442c508250b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 7007039 1250 7005789 7005809
    0x20105010e070c02010806030f0f060a0b0307030309060f03090203070807060e030303070f080406021c020a030e0f060109090606080304151205060102030307050304232107020a03060507090b07080a0306 88
    0x3082070b0078040e00d4500c4522000f0b040c031a4600000e85203807020040d032104401c0340300460309140070f0800c50a46910b07043d01c500711000d0822481302c07110308000504070121380d895501c1082d40c82c42c000c030446254a130110402c041544511901d005654200000b6000e44050b00150100c00c0c0707003910251105250005082c042e800a00410030f40b50340050003c000081241810541580c1d2460804000e125040b50703480f07400d001c244101194065603001c0c08609801362000c0001030185215195200101100020305a004100501030903a00743c0104a140e4401c1c2d101240ba651512001429600180c01900c1603d00001506003020303440300340d107045480240c50030800d900300a00001d40b00d1000510060501c0710000c00f050420440c2660314070280708086000155070807240086840301294a001481c040044400410104032079044924155006201780e04d00d5145da96400c0180c44010702c004107000c89000300240c007110300740081c030025120f81c0c90580c0da04404040642241e09a401c980841 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 7008289 1250 7007039 7007041
    0x1a0a0605011d0402160605040506040b0108010516030209030a020303040902070c050d03050d090206070219300f0c05031209030607030501050607020405060a08030f03010312141207020705060c030307020105010e 92
    0xb51030110103411950600351400342e0b407901c801c410090b0700c038400540200800d180008000a000c00850702c2801184034040c1c9000300d0745c0c0c4440f00d81c2a0350b030540d045801c50f00c2d0726007280301d80c9010b40e00610040d40094180e85e0414031032b400007805d603013240e400000c4d9a0f07000501c103c104104400f11034042e1000311548151005142c4004105000d9801d5562050380d481140200390750703802d000c0e6840d0320f0303000700aa196941003400a4402c0c3e0070074420b0201942d40d50202d054104885000342c030308a804441400703240907007601c44040506050b00f09490301c0e554400d000ca22620b0912076411921401c08855586008000030315180500041401040600c0c0ca030040c030266030740314200c031039440e012100400e0340d4941c80000742030741880754000466440700058010596a0210285048a01960100320910960310060720201c0178502401000082001040c0846000607a00c42e0410352901c101c80041b9100c101040c460b90083c50024a0b030341c804802c0004250b82402003501400d11020360042c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 7009539 1250 7008289 7008317
    0xc0c03020d0507030302040b0a030b01020f010501060c0305030618070801080c0604030b062206090c110c010806010f030b061308010513030e040911040510030201110f07060302030c071a0a060501 85
    0x50364540807103601084000103103e01814481d0301951301800751000f080340e4030250b4250240080c102c1c81c036014054016a04244140712040c49018100c440f80e03104c441c002125603804454a0b4801800250711000120ba10920382c40400506803180c00e041d120442c1550504080c246000c80240c109440b815040000f07100080d81d44a0513074100740305070341c14800c25910006003100010625449406140b0b0f0003c0061b1050300b81d042000b628040d500e03921400448080e880e921007170b0a02002e804200c140020403015440f440d09041aa8070600d00000d1840e8180002205503000340081410660305001c01d000d541002e11a49402c00c44a008031556000d103690080c0542c98440c5140340300326500c4508400740a4040c9254071107060041040043e46005004541c3c02c1c00795000690004000135440d410500700019070601d0700c10200010072050b450718608501960000b8960301b00340d502071000c04001501010140c480c050745d103410302200c0c506580c42d102240e20340e51046040285013205010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 7010789 1250 7009539 7009543
    0x6080f01050907230d03080601030f090b04020904030c0506040c03030f1d0103020903030c0105190605062704060513050405010507030605180c040b04120b010b030717060f030307030e03010c0c0302 86
    0x3c21110084070460b81e03541080540e91511020003010b07134200c809050100d080692142c406446150244ca0030040d0503a0744941c4c0c4d0031148100c0000f00002403c80211300549018040503503c60b02c079250517551f1411981c2ca032402d0250a40f02110360390300c0548203004054010100151904052404554050313400080080400030800c00c64181540010784403465101402161000f000d510f0081c811400d104d070301000007900300e0028a0741189000e001280b40c3c9030030412120019000c0750b40907021400d115905a041201d82042a030107035031640700103642e856008580114420317940e4002000d28040c1402e0f801d42c0d000800c484c2c20589400410301441d0380b045103c800600c142c40f80000c69036a0a105c03888680b0854000344030400011a0020f410140413000343d41661003809002401d0b40e070740f14086201e02098a150b40030520302000e10007803000d202501d81c0d0040000f010305150b041c3d5007010a04550002c00e0580c0045c403c91106101400d0074040c0c007030046014035200701c0840d502c0c0c1f4029 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 7012039 1250 7010789 7010803
    0x60f0102190203011b0509030d050c0d08061306030506041203050106050f07110303160606141e010c170c0f0a02031203131e02030c09040b0c0703030e0102040906080f010509 76
    0x901489019090103540b42507000e102c0c0d03005190b1102c441741a211101030301640040201038403034414400006542d91048054603000c40d01100207104a0408600685548600500c01030700036030404800c0c030320491580241d01c0198021006007485040608207040304d0a4a00786c98400d0604000042084c20f40c4401222101c02208010700e407114204d28010400c49101c00c0c0042e818440440e005c120780100b00b68110445104000c20000760b03664a80c00d421f1301900841c0700d42d101e0080054403000e0b040c0700582001d0702905240c030203e298020b035200425082c015940c20b801c0e000c086850310440b00c0400083d00c140e41200000e00e50080320b540003940c4c070407000b60f070401804400b001003866114058810341d6500c0d44413032a40c40481d003200c911203883c0741444003a48a84103a025100ca5800c1c6804110300a035081405d03401da9940c2c00340c0d4510903602104003202059543d900b01c60b00500f080c800790014014906001c81c0e0107140c602010700d80000024403080d164501400e012040744001106 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 7013289 1250 7012039 7012063
    0xa0c0503070e01020a0c03050c0a080105070c080703020c18010503070608090d0c0201090b07030302032203090504020f070f060c02070b0a050301140a08010903020d020106120803040204090c031203050f060f0102 92
    0x8400c8040c070500c0100d0a18182c5c0c4001803c2c1c91380880080100a4003042007850f0754820795921000c20340e94400d02c0c0c00d07a00f041d107448000c03171030105103440414807007002840c4450090040301e040da18041c1c0403484d4280b200b0303131a0701510903d0005101c649814050b00c002086580f074401400d0034000040703a2903210381703580c010600c603100c0c2c00da80441e40140d031400000e03c08280f403542c540382d0038180500030390300031291040c14030101403445465442481c1007020543e003542c2c4910b04682403006000c000d50000d01007003d040e105000d18800200c01c4020341e88504e01c2610b01140100e00300002070b02d029440d81045080030004d12039100c42c254820240c078116030070780c2c0c8043c242c105000082181e00443d50448610744d401c0c09100028180c0010742100425441e030b008001040c1d40350385a0130380b40400f101c002c003103040c00c00210b0701503d030a401664016000e405010742e440da581c0d44d0880c2c0e02206092800c0869103620411010507011303031f485603105006441043e0403a01100001707460b11603038012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 7014395 1106 7013289 7013297
    0xa09050a030302030a0c05010608070618080102120a05040309090509032116030b060c1c12060e010320030f150a02040e0f0403020a050604080706050a0c050307 70
    0x10303007201c0d01075000d5414078031001011100400701010940b007942d203981001c00d42200a0020381c004102c25112a441200758110040100c820303544030455030303441404520903000c040c000e456446a4014030010781952140350075100c0b510b440e00310643c02e070318080c10030113070f950000000c00c0c1403240c030030301c100c0129070201010846044c2100d500048031041c408240c3d0340d07070090b00a521241c4c07004040c5814440208042c6281c116000320080d070b80c48145030a8111285c200c0c620080c000d0502d00148005170070501c01400a034010310004096202c0b039802c50f101440c1d000601d66810000505988e03190549645507641c441e200f50f020880d201190011880a070711a200319002c49010302126500b51f03850000101160000603c1a001e5000e10014600090f20522800388110704c20890b068a075a8603040c404204c400003000024803e10705641c0d01c06503a0007100f902c0c0d0048952074 = true := by decide +kernel

theorem cover : BRFrame.Cov 6834539 7014395 := by
  have h0 := BRFrame.cov_init 6834539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6834539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 6834539 ≤ n) (h2 : n < 7014395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
