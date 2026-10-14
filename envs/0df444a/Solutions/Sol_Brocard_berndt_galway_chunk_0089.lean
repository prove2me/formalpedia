-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0089
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:46:19.92919+00:00
-- url     : https://prove2.me/submissions/94d776e9-618e-4894-b52d-8a7d26bc0ef6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 15827344 ≤ n < 16007200 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 15828594 1250 15827344 15827363
    0x402030702070b1c0b03060601050306010518042c070b0f0703030b04020301090501080f0d080403030b120d1206051c020405090a061a0f030309030a060e0a08070b070e061303060b010903 81
    0x4e1010860812210030301c0710861929602c85503504002c40e180b0b12507441a1615491615242c00440c1c1560041200080b8218140301703e900640d0b4500078040c809107000b140300101d00c00004002034541c0c0d00b00310041990702c8204204044410101a1007603d40e03002c03545515281281001d80151040e91041c940c0b0034400800424660000e0340071a060342c0c40b0000310f03a135009501d0402c9580d0f9034038606100202c0d04210000740086e1181e0004071034107101401d0782c2040c80c0300d60300c09807400d20485d40c642d01003400300c05400400b8034648140d5009001c1142c034070400005040c0c42103000894000080c1c0642c2d02c0b000011103400c01000100b09596002504115886211307031229071528442d202c5030301c240c00201514840345000410382c0c410000003000381c9120965559203074028201c00d003900703505014100301200801c9401c80a0003a040c0510740300101c41c80d03c45030003802c111007017221600c0b4241c01e220b400b60003c0103c48020940340d0101000403003c00d0340f00180e5000340594002810482e2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 15829844 1250 15828594 15828607
    0xa0803010b070c050a06020a110411030a0902090a0b090f04050304080604050304150309021305060120030408060f13030e030106030c0b09010f09080a020d2108100b04030c050402030702070b 83
    0x541500400b185401503408800b482c1d03c40040192200c90341c41048016400b910181c40454100c0c110129008001000000c0020802e000d03800c0c075810445804841ca43c0d42d021b04001e605220b41200c0e170204d44001e0400c42002c0d0341c40084c000c01c802030161504458410002810050100101e48c0500f01c02e0003100c030300745000c0c5000e40e52070388240600ea180f400f000310010a60340c000e01070407007070690003051107402101000140380100401000c079410440718240d00d6909260800310f444142000201840da9941412155441c028000e4007008034658803a0170011082201c134078000802e0b605242208562584100080c05080d030b540000d041d00f648013200081c8001018004d00a852082e00c402e2a03000e01040300b42c0c2d0300d6040d445003020740e03001501e0001c01490301d0410294482d11510203180040000041041e40341c0144011070041490101405002020405e1000040242404892170a42180d41d210340b031003030b28401c8a00458020010980e12402803100d1005051000b00c803a85511 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 15831094 1250 15829844 15829859
    0x18020d050f07090203190209031002030a02070b15150d0e060f01090507080403020c120307060603050a022409010c03021e0d1103040e010e0c130905010e060301090507030308090a080301 81
    0x24420184041c0341d218100000840405034000daa1254400905010501d4600b4420034003a500003c4895498081c42a100c0c404940e988060b5000e0740d000d6000580b40d07076035031404034031001015100e1168007110b61020169940d03042546c4150300d0800c800f8544501b80c803081030010346406140707a00c0c1c500070102000348803004245054121065800c0c2401a51036540c0140ca4454041c2d402800580001040031001c0c02c0103081710b01e01d07802c1102100c1c9082669100c0320100c40040c0c004a03010740003410800150720380142e00741e030100c3c1d052403018003038040300013040f085101d8070314070a040c0b203010020790040c035000388080b510702462900c042d1600395021120540f0f400c00c1d000144007003042c3c2c1e5400402c004000003a0741c250740b0a143c03010304990a00b1760303480001d80002c00605c802d000030000004905091003400c0300516604c0c4010507071f94100240b210000100030840760290b8540014440031038400192401200c0e0142046582d544519050700e081180852000d031256200200000e40740 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 15832344 1250 15831094 15831103
    0x2007080409060b071109040b06010f171003020f010203031302040b0109081615050906030c0d0e0d090305070b0c0307020f040b0301021b0c031c0509010e04050106030f050901020c030a0318020d05 85
    0x1620820f5248000200d05d810449850401e840c0523100108800018003954040d108085001205080c5444111002c588a540e80e00080f60000041032040c02c04104500341050313401c041003000d0000e18110b00d400314604042d09a0041c010f881142c0318850a142d6900468208000e042d10b801510f00b00ca003640302409000c0d030184150502d22407410708920381507225030103807054130100600d0702e1302d940c9030a82c03061490b800000c0480c0d0569601c443d070440d00c0c4010010780c46601420f031500d4a90900d141010b43c140312040d40f291140100c104140050302c3d001004a40070964110344900d25071000501040c010a21390a03100d0301580b0001c1d40109628112540c40a0040030404903100032405506068030b4450186414100c5164400c41185060144028094002061400c0111024410001000d8403030030b9000034042035030340c09000070107402401b8107944520380d48025494644148e6101d41c2e81e201c0c014509041580d01d1102c440040c51041190404640041c080c070180011400d00b95200c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 15833594 1250 15832344 15832357
    0xd060506090a02040617091510060201060803130b0a031e0902030606030a02010203091509040204090b0910030506060105070f020904210305070c0b27010b040f2007080409060b 77
    0x1100114000b411450550086070140d0ba01580d800d080b401e12210303d0a01c04002420303103a40c034000d0b00340201034100702030f184074400c22140000c0034800b450250040c1c2111800d801c000c01d15003081144084542c01c0404280032603800825040e501c500600045005200e503141c411f00d2801002103149011034590004403602c3d00031025109603454000816a44000e00440280540c00912041c065031410700140585520505109884c1039400c8000504903805078001609165a604064001d420082a102da2040c040d40480d8501419500d945640700c00040c40305041000004603d020000130454413400141d0141c44500700e41003a18210780f18655100c0c903402e940140d041400240c510a008040c0150301d0340c1c480503010920b1307480f5080c445200501403c00c0f0301c483c00103051701402d14150017a41010003070000a0750007902081000351004c03c80098001800e10720700f080340c00e40f00e0101c100c42c15160082503549404501e8210020700840e80b01207034586ca0304e01d0014034800080f000f0a00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 15834844 1250 15833594 15833599
    0x91005040b0906090a05040201050408030304050105010303030c0806013f020309010c0903080d020a0e030604110a0503070303120c0c080409020703080c041401080405030405030106030c03020405100b25020d060506 93
    0x31000400d09025002d0700032141ca0394841c0350301c2c003c999071001a0b44981e400500602d001d07485c01e84c03100c0e030f110300e90f030300559084450b60340d40c0004005060341403141c954800754524200115060650009004001c0030740f03401d40035440000c0c504c3c5050110800ba8418850015840100515403c2084029081210303181003c1d400c103402d80402c58412019002500da12000c07407800c2c60090407a60307009400c0311801c0e030180110200c003088a603400300315151049108405000a02d4501d40a10272180510303441140039500030700c400d0002a40040e684185054042c10001c0c0f10900d00c402140d01441010014209200028010651034a10b8006021283c002d031a140002d4544448034140b80c45640310703211010419240c060f0340c562080e000b4070380090052040302d040984890000307084400e243e1045403407c96800040046082602882d9849420401c00200440c54542050014031410166405a040b1184511940742441c00391032000c0360060800710410500380b034800010726094074400d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 15836094 1250 15834844 15834851
    0x20c0706030c1209020a030204020d0c0e06030c04121e030f030b06071502072f0f06090a03030c060204080106090504030314010602030414120f060709090504020306070f050909100504 80
    0xe02034003030b00442c0300302210355690310240080420f54400400c0d03c1e20080703900440700c550000160ba142d001030309140c080d404e00000c103c07007007000190285e1160145c0d035000d0070060007003022501c220415201207802402c20b22064a0051a0140c4206800c4400c80b0100f5005840142855030001c40045880000d440800026250500b04019401100c200801710041104500491a01c41d0050301805104440c02850125010f8a1140d012488500c44840c40040d8009105503d082034601d06000d4041c0c80c1e45107450312890104015030200d000142c284a42003a2072000c010603941180e0042c400301008005158441c0501c10181c01c09403030580c0028100301042e580f070a5900c151604131045500210300c0c181c07410810348070340641c6001403640688205810640c00100b80710a08954100303d000e8081403408880140100406070800d0b0495843e000c10800182c40c0000c05980002c502d050054103071080c01000c031290310955408640014020003844a8458034034124020341d54200e8051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 15837344 1250 15836094 15836099
    0x20a080907030c0312020c1e030c0108010b03040201050c03070602071109160e01120204081203181204050103020f1b06010305010507110c040905010605060310080d050304050a1b05030a0501020c07 86
    0x1141d852103a800060070800b880c210800014681e43e0a8520312041e50059030300115a081c00920944050500f0003840c0224140c40c500a1805010b0350b0b8014000b42042041c55061240d16042c50000400c02070621000150b01c03200d1402c1002a03c03c2c0c03a6016406541c3c80e2043d150400c0040c00c0c508240b03001c0c5600e8800b08a110b50300d0313201803040b442590b803282c02030030001004469507030030790380c541900c954200004161b050041c0000303035400c65054149507880c2007445515025040c030a41c052080e03040039940d8a01d260344501200c0031100c00f480e001d40c6803110384a460145200300c0174504403c01d0542003890200c10007240d5541200e00035402040740d0390390340d03000f501c035031914900d43c0030190000031491030709140075405442800d02880c00092183c0d160b030007060781d41d882170360f000403020f0700d808080060800411061110040741e25001741942041c0e40c03510b030b590381c282d5401050b8480b4001c405860101d1105030700c1c000d00006003103541d80310990512500070350006c0010809806a054007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 15838594 1250 15837344 15837361
    0x120f030807050f03060d02060d020c0c0a0501020309010504120303060e0f06030c0913030c0512040e1f05010c030c050f010f0f0e190b09010b03010903120e010501141002031b01020a08 80
    0x151883c0c00c46200c4a14999600e820800503020100304040f0f80c44003043c880200920054409808a1003611008145a01004040000d85000b95200c07038119801000410540c0c2d0b40141a01d00303d546603a8400034a540d9460180d0261402e03400444030b204a120401603903180d19070716503010304403c4d0103451426141c1c4042c0000e640b02210096034403200203903c240000d00c02c0c0500c4170308500a0065071070701a0403940a0505038400d5004e02c0c6540d40710fa090207600145103400c482150a50301c044041d261030040042c000e00d80485000d014082e107400c100081c00000c0c000c850640744100001c1091010103102c1c1c0004100310300ca078610a9140412640f2904000601b80039071002001c03068803621400c1d0344106440c40002d002801d01e54a800f51204c42e074030309000300d0b845188130303407692030101d82e5584081045445d10840884144c2c1403c004025602083c40011507465095408000105801c0310580c6942318410040d942003003c0c410390000319906502030700d4031030380d155603119141e101d40f0403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 15839844 1250 15838594 15838597
    0x50a060302060406050903100c1e03020a0e06030604150303020d091d01050402030408070c06080406050a1823160e01080601030510020702010e030d0f0305010801090305180604120f03080705 83
    0xc001e402c40800c11060001a004002801d106200202111840350f01e500546082d15041c040c1c3c1c0d0017090a000611200403070020300f1650040b000d1404504029121800405d00c0744c000c060140200000000b0890b552101c0d0081c0d05840c5070391500e5460641c0e03d10b0025994400b0911032400681307107420110f141c2012703a401c0000b80d08481243d00e0181d0814007008025400900102d134a4901040728200044550b00c11100801050326007400c945000d040200c203840c4001c00d0702c7c010604c1e000380070314140d1448064540700790f00308201c020507041c00c0d2915000200a0b19850105103d0403c0201c005030310b80d061b2000752900300c00290100c0c0d0f613550034195103600a0000400e6a0403020701c0540102d1a980a4000c10380140750a14840e02e4040c046820304a43c0401000000c0d0320a4000c201d0303a4060060f9030041c80d6581c0204071b1511641c40c020030728041c05101c40c1104a1920401c4034950315030b400d440140c10031005a401c2d080807480c02c0380d000c0e61303810822000f00d0222400940c2da14000ea0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 15841094 1250 15839844 15839849
    0x2c1f09020112020306010504030f0308010303020c0103051e0702101401090c080403020a1401090f050c0906030f071a0d02030c070309080a02010c080c2802030c060408030f0c120a0302030109050a06 86
    0x8540c16122500e001c16003000c4d4000038070050400006000010100703c500000c414a40e00949401d5540c0d4198100242001030360340c4098145402c100c10b01070300c105140801c103142103951040070902e4854071402c9040000607803101110307600381a07a4603100130302002200c0c1210082c0d00300304442d4400c8102583d41e500d08650240245e009018031102060150300700c3e0440ae450100006040390050307642215824050b4030a80e1141c0c41010b4021003401d05151003600020101c00920720024040a050b47d90300840c0500801c4c041400c0311451048204001e840d10345e074188009645078a8904400040b54002400503000296a40340004240c0d00100346985a0b54042e942c500495090381c5452100b03070300c001c031101114844c60003084c030001117030890f8117968180c07140303a02d560754090f004061400b1411804103101c1c90080008015a42c40041103414200546002039140c0d50200c42071400d26810507c0e262400c44000f0341c00c610b50b40e040d8022341c10f0f901c0ca10300402081d154003e41a003110500d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 15842344 1250 15841094 15841097
    0x1e0f0f03030112030c0510050414150601030c030204030606060c050714030601090209030f0a03030609060905060603220c0306020a030e19020618060408010504030e06070c0303032c1f090201 83
    0x8200510210102441101d00140a1705001003070607840c0c1d0b00c55280040340c0a180b54550b64a000780130800051460480e02c0402c1d007130080c0000c10304980498000d030320281c0003c0c14103680b1181c4c003441c84c0c06030301070300e00840c2c00c42810015a9a1010058200c1c00e00c11411111405104404205040288280c0d1740013080076004203501ea0810510000a40c414010b690b858842c2c09401140145c007040000d046522a58020907600c0c60904234105980ca50b4200c2d251250805003041034a0f26180266039110342c58076a6070a071440d00c00784000f20072a02442c00b40071440052404824002c15800520014100e91350401c108032010611645545000010bca600c0c1000d84210000d8030f844400303410203138420b5040240b54a01c2c100005c905a201e640708071401c3e5150f0041005240d0001c815260504068800c645021b0190f92112803200182c04010249a41c6116103104010581140c41c14600700d20200340e00e4030700e0060070695500d03100080640701c4070494500c17405403e1741d0140d0030103194103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 15843594 1250 15842344 15842347
    0x80c190e04080f040801020a030e1204211b0617060109060c0f08040909050717070b040b0a030204050904050a061a010215180304030c030308010902070b0610030902031e0f0f03 77
    0xd42d40c540386142e0205584001020091002007500344081c4001c0c10751420644000404a0303680e44048d0902d0301c060650300c0801d00c01d001c10480e0000f44280140e899014000ca000030740b1107482c4c4511174465401c54401010100c3e1030110f81070fa00f15010001445507100e40500c942e4681004640c06040350003202c000440144030380000904c01422407140c0d911403900709017400e4480c90081c04881c0410030554071a8000241001f1170300c0030035298100b000141014000b00c1d030604041d050188102c1c8114580d20720000381814110f8441d81c1568050100100141c000341070504107655264031070032081c0c1e030b43d83c42e000014188014540c854494400180c0160142c940c0300004070040040051002c401403031a003070402104902030000348003840c03103800d1366000705041d401c000f070641c0300503003005090391320400190003c980890a00b07603011104480403544035800795001c078090007005000030342520607140c3c06c00015210140a969101028040b10399405400d10320740d03522076402003c0b51841c2c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 15844844 1250 15843594 15843601
    0x16050105071a0702150108011104060f03060306090606050f01020a1104020a11060a090506070905030703020609030c04090b07030c03140103060e15040803010608070c020a0501080a09060204080c190e 87
    0x92005054402d0046014031403211200324681c102d080102c99000060300001010710803035509652042c05000d01034002c118180076020000c3d00791049009506c1803080b40c1191415140c03194010714080c540c020000c0c4101c0b842c0745400f0f000341200e4000c0511400e10000460a1540700044044104d1340001b42c1c2e00d844501202400001d41c8004010410800c0000c0d002840400401409018880114000404000d5418800c0c20808040d003010b0800c0318200d410082da0303400080702004c1d20b80403030f0181d9564604000281c42c0030075031940c40e078125040c9420038050182001d0418403d026a4509101041101d00118100e940440c40d0038842d180c0c0314010b00210b0703030070752010300c100c1140f108a40300203290060130250340000b15411528010000014040d00d81c1c411240307500302010b41408050f00409500103081d85144e8010f0078100b04602c4001078011000e0782003594101e42012085580e5611029941d0311086801f11081c0247c802003420281d07020b03c0714a007404c42e014442c80352400e48 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 15846094 1250 15844844 15844847
    0xf01020711030d090513021315080f0906071d030a1506060c0c030b130f050106030c06050a02060414070b040815070c0c031202030d06090b090105010807050a03090204021902030d060503160501 84
    0x180392003010707402d0782031004461008c42c210703a01018003124807444d040c1203200074000f04070a80003071100c80d0110415041c01700380000020206d41041d56410300c283c800d4109201d440116026200b03d40d41485000b00100a0080c610356080800ea5065024400c0c0c5071204c000303882079211000000d040354070585080006c5500c40307240c1508003a440d110440000803a80701c81020320040641950503035941c1000b0010800c144025000a0685080c4a410641c40142c007a4507484001c00c0600001140e161800d2865010f110f605d015000d41c800141e1100c3e140c001050b0382e0054811011b200030300d0040411045401ba00b0450b0030954405141100a81180c0d0f4840200f401d4000d08025480244650030b4282104e000740b00c06414084000a092042c2c0f00400c030a02c401a840181800089002d22055075440030840d8504a980d040104514a05d031010a001f031180101000d0802d81911241d20070b80d078048020100098400d0040c400162940300301601d90a02c0011010603d848000c100142d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 15847344 1250 15846094 15846109
    0x70b070501020706020301030b01090c090e0708090a02060a030221060d080d0605040504110102100b0a1202010c060c0503070f03230403030f050c030703110702090c090a03050f01020711030d0905 85
    0xa124800141c02c0c41e43c030340c0d9004241e0b042a0421298240c601c4010301980c0440d111b007040c4c4400d5881c011241a140c03070a007480d18680500314504005e581d40005a11110420840307210300d41c05010103640f024003402c01002508180e003854604039041030390b0420100c0124941e4040c6800608071900f01140343c0d650141c0768000050780d081240c07210400a40d03a03480b0b2182510440c0904407a14004800350002400d003411803914081c0c0d1450800c0020140c1c0754688544180d50102c003424403c0c240b10f00041c1d41d003100c4020018001030809030007584481d03022018500442c01901c81c07003c8001c810038180e0070398801400c2581206500103800d0400c0c0d00c044051a0454000d040c001802d94046c400041a64401ca4500810a9000081c089025032511840c40440040c90300d45082c44510340c0000c040c048060042c1c41c1424002c251803450b0ba5036840158000c56100c403c50b100c0f403c00e011013a02070341180505035132020030340388504204e040c085248521903440d640c4a40c2d46d5401c140c01c00042 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 15848594 1250 15847344 15847357
    0x2031006080105060901031d061311030610090e0316080c070e040308070503070306050319050d05040f03060b010e030d0e0f01030501031211030d060b03010302040e1f02030606130312120501050102070b 88
    0x15040380401c1c2310503480302070203894083d10036444007910410250810010220b03400c2c0c1d0203802503100f8402c2112500e40c442301d400589400402c04501c8911541c00d09180d409421000d03011000e43d28150420084124028100340b000c4c4c0c03040e9101299180c002e1100c00740201c0d0040d010412031400103843d180320b000150b42c803c0e10b5050015202e5180d001003487e0100070003024410400300382d22a0306210042094020400203841c03c5840c20303040011540c040304240c03000400050300c07002c10300303220382c040d030503a60038114041d0032140358603d480401482100400b0020340224a900f401d000e465200303003d118180c0c1d030008410080d194005008071070400206c3d08920a900090201f44041c0b00907000c0d0000400e007841440c0d40380d50460040104580c9400b007012400d520295482001194600d403070b90764102170b2000180c4a907140130200d2514821920b103000000080c3d0000700800020035042d4800c0d00c001d0780c5160f01c2181c0c14030b0f880d048a8007801542c0c0075900a1404101d1580c144009080c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 15849844 1250 15848594 15848621
    0x4030503041401060b0d020a030e010b010e1203070204050f070905030102030403090e0403020708030315120106050a060c03030e0105010b0408010f06050312070201090b040f05130203070813050c0a0303030203100608010506090103 100
    0xe04d15624034a0000e40d8001100340395146800241d410b0446905005e10780e0940d00d0103000304205107031040040c121120000b0624081c2e91580c45500569606100380c41d0060f8011304144003c0c40c0601d080d049040045131a003000c01c283c5100403c081c10144262846180e2580300c00c00100c0c04c10000300c0f076882e8010300480c01c5125100c03021030380035400c3c0b01460203807541c80e400c2c040c0d80c1e0801041003144002544401c00340da240c1a01009159506480c0800f200d080e414110340c1d01c000340c14118007410682e8250600c6608180002410741c1440c4010411910250001c005542d040c0b400e01c000d4030418401c180d410350080030321040682d40310004181451050406200850b03548041c030500d900107911205500307020040822050600300e103582c140f0700380480210b00d145002c0002800b0714401821041c61021154054400c03c9802c10000302040e03801020320701c0050f900c0c500140690701c22540d0540c0b500714071000046090168036440c0c1600c20040529042803645801100104903900c540603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 15851094 1250 15849844 15849851
    0x100b0109031e050d020c0111060c04031103100c090509010611060106080703020c010501030606080d020f070b0a09030209130c0506070302061b16050f01060b030c160606050a0b0304050d020604030503041401 90
    0xd001039030400c040c0610a8135a0003900c110441240050b0400d4142c8611050a4100108004041e0303149021039040d01d0780b0100b240d541c0d11182011920380341000c0403240d2a07074603103100b000c3c80e150010001400c486044611481ca0f81c2c0300c10046851101d0320346001c13020f80c0b1060050194501032090190f10100310f19005080c1010701102c1c900b502c40a910541d0348503a0b40100380711000c4244040000d00d0358070b00051404d40040a0f2066032000b00b0311a0b0495800c02065111810b441041e821001310380003080782145082100301000d100c00d59a4046a02c105103c0340015242071103010307110b40c0f98054000c0c200c0b9030f80d04c40003502140074502034a807140c031041000280c213401c103030300e42400c00b40500001c1080ea10002202d50031181103800450b0742d200c05004020300d41400300100c984030703aa06852088142090300e0940042c14260304015809654040c001c995801c034503024600c034900400403a200e42950880580c5c403100c003a100600001e0040000402007503010002001d102d40070800013 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 15852344 1250 15851094 15851153
    0x60607111203090409080705060115020304030b0403090e01060201020a02010b010207140d0f051c020c0f0904080d09060c0e01120216020603100f0b0c06060102010c091206020d020417100b010903 85
    0x50171580461022264104089141005c2c001c04100403800f4081c04c1e1407000415481d8400607540b0f0185200c002c2038103242d00001010035101d900c802008001e0811502d409507112075000e4080d42241c20084019841e107044503013550700c0050244215201c01780300c180203070300740c1080c800084005d1320192040000052080001001041652400aa202c00c41140300980e0400207080c420301014103031103035040032100001ca81c0e40ba010355400c00e50062040380d440844090f00c40c040c100b443c0e80034000d1850450300d0b1f0826a046880c0d440036207006d980701e480f2901903070360300005c070300640c0b4004140d0030700540b8520050402a00a6821803020545094110355031740d03c000c45406c2c15003014082020100314070302c0d150820051b00f03404c80300900091000c0210404003c08550642c0700d4140300044051800c010b000a503412240050b070f412806550b215103890070341d072114180e485c3c040b840c0e03c80c4e45007800b40e0407524410b4032038048059441254403403030b40c1c80e041e10280c804403400c5990019084c55 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 15853594 1250 15852344 15852349
    0x60816030e070605120c041a07050a020306040501060f090501080303010b07020604030b0703060315090f0b070e04090506010806101410090b07030905040b0f0303070b070908031605010506060711120309 88
    0x30443d40d55002d503a1076080d503604003103882c0074280840c62034050101b0f2098001c0020024a890a001c01032625011542032003464419203040194041c000c41041c4414400190404006d03a2071a00b400189d0950303030801c40381203a409103d82681500184018051100103038010144140000d00440c1040d4581d01c03204807110060361000d011a0390b6280400411680818455011402c50800c104000701c1c0c0e2200200091711200003032459442c0d60000700b2450040d00084270314200580f04104a0780c2c6c43c602541e40710401e00239900c80d4030800d0000713003660082510410507140080c01024400c016241071021000040b05040c0034481c410b5000315803412180c2c081c100650095403200c510074944018082281d4080d10b04070700a800030201c059040c2c500004461259a01c1002c9003030940d01c600049601c0d4015801441482c0070010f00074015a9034030300c400b201140294001c2006444560810410b0300c10030200511060364800c81541c0ca24141211900081194040d28a041e502500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 15854844 1250 15853594 15853603
    0x4110915030105040614060304030e04110703020307050618070b0304030302040306020f0d0f020c03040b03060303070605010605030a050703060302010e06071104050703020a0206060301060506040302130605090a0b0316060816030e 100
    0x4041002000c0400100124507190003080002e08128034002d40034500c40000c681103100c0100003505000d100840039185854a170b00c4414541054450103031902c200e80307030094076a481010256014402d12001c45c40c2d0011000c294038010844c04010451141f40c41c00401041d00010010380500d9402d100c00030120300c09000500404c0c001a82041d03076082d125100ca0f0845041014000c4087e04c140711000e0803002c000300302c405490070010a1a1207a6500b00024a144601800140050304140002443c650071034090350040b482c48406101c10b581d0b40c44201c0407507503a0310019000421a42e03507640c031800c00720024244540a54901101c1e20202c0d804181038030700684a040c0082d9002403005038556062103190f4010794201c000740070f110319000c005900d90044d400003038420b44680b0000c83d18402c00d5072081004000c00303000d400302450800302d0080105505607040e0701a006442c00c1e84031140344220034030f040d00c00302d442d00240e40e2174500b001c14004008200d91018150f84040300038481b0800c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 15856094 1250 15854844 15854869
    0x3040603060e010806430f02060903030619150512010e04020d0609081603080117030405030604061e09060501180507080a020307030603020d120908030c030d090305220303110a11041109 81
    0x21206c544070501080d000f04014042c102a00840d04040b051010151000c022282c102404540d45016984d121031412100c00b41c0d548821504400394050040042d00310000c0c0014a03aa507806a01580ea2101301d10710403101240c00a6001421519440024109601c1000380900801c103103400d1400c0303c0022000c41401c000305074003062004c1c00410006043c104070f4a103c03110311024508142c074100109540d6000500014a031a4803400e889050b40c8282d280500c02e00030b00c80c424041e1002d81c1c02e0500040500f8040c0c500000b1415800c00000344107405070707900403000d5039140b00056848088000003034002400c130008054860a000015030b40d40c29000282a0064842d007603c0410030002603d144610341c03185080fa00300340300f800c03a400404026140048001040481c0728481460205c5052084007100500c40f0200241500144050801403003a6403103078495040030400000e010342c6d10103500000900c01351485051806509281e0131080200d8a0340405504014031240055540c03540301 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 15857344 1250 15856094 15856201
    0x50c0a03030515010c0c0b0c03070503030c190c030509040902130603060b090a0903091203020c0406090e010501050118090b0307080f1b01050306090106030b0118060203040603060e010806 82
    0x19001d03c00d10040340d024846851009003480388031103103155250b0004810034030509080c41c030049041012420180300b00c4d0000f503409002d45c2c0d620301e002800d0265540011600c00c5140002d514007106c000d024171050f121550b0141c5031182003205802c1040083d12109204a0304049500b1315403030707551380c20301400c8040c5100d07400204100c07812006100b101c0740300802a50f0941d0070403480e60042504171225105581c0c460400d800128440c3c1000d03480d040e40c4c4131030550054a03185001606144a0303012014071030100009200030790340d4400442d4002510100701445806075a008c0040c00303031960140a04400140981e02401d90300c943c41ea04209001d501204035800690703030141410100d10324194080401d0814a0841c1805e00206170383d0703c814003407201810350342c1100ea06240e026581074602a07000e6100c4a001c1a2500002074680d04a4850080880d0a1040c0842e0440110f13164038140da10120003480982e032021200d00011030400c643c1070005004404850700042100700005808454 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 15858594 1250 15857344 15857351
    0x30c08010b04050c120402090901020405090c0901020609010b0a21060f0207020907020105010308120702150a02041a03040f06180b0903130905060d0b18030706050a0506030d020309060a050c0a0303 86
    0xa61051006a510040c1341d080d80207420420140c241500250300ca030843e130150351140040d40c0d202c2405009110b41c4d00301d181d008991204001c8046480303001400074480030ba0964450f0f4483c960314a0981b811041000d0303101401a106000140703102e0000c040c0010180080fa40403503650301d9440c12907160001042c0c0711a000580b04040d81130526559820455910003000b0641c03554942c1001e43c043c0b58444402d00082d1b802040d01584200310a00845080c029a0a10390415200b001e00960161050442188403a58500610b02c030203411b4034411500200d130040071544c0c55070751200400d607002414214144405407640883d00c11164548070304020340095607580000000400d00d40f4007a4040751842d420039082046030b481e10070b2602c0c02194030041c420004d884c0c0782c64003013014500c3c41c8004900d20003c034540c4140942d58200e07034016041458104801d807140d00c20b041c0c44040d04140000564820002c2542ca400c05000500a10800d842e0045c103118a03100494100700b0210400d0b00007d48 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 15859844 1250 15858594 15858611
    0x604081c050a0606180f060302030a11120613090c03060c02070b070c06021203071d0105040b0a03020403110f01020a03050306010210060305060a060e2406090604120506010902072a030c0801 83
    0x10480340425084542808813101e61b898014403640310b80c1c0354003c080800d500880491080700c111340129040c1c216904800d070f121140500b45484200742100d48500c640d14618821042503545e21407006c0140d084801c4855003421610341c007001e480d103d601841188560080080c220203000f001e4454a845410b41c021418032b8003800030f00d081039946205003103a50800a014050381c1200458403200b416a43c0c800d8065586801039419000d02d6024500110000444a400f580d05a00500a491240310f180540703503204018418a8000300607602c1c00b50b8840701300c0b0341c0400c0c0600082d5901050510440c0c0042480b00cac0d03400c055680310340c01260035034009401e0005004440c05480e0250a201d00440c545150103203514507486038801c003081030350347c80b00401c0c0c0c3c20392507a5003100c910303a10260100d903540b41e0f5258003500203002100283c0741401014000b06845480c0e000710b800290b0046460f48108081000801740c0c0c0e080700391111001142c1c00c40000c0002d4600c0cc1ca84010416400001745074403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 15861094 1250 15859844 15859847
    0x50c03150a05010f0e1302010309060c2001020a1403150d0803160c080a0e0f0d0c17060f0a0b060c0f0303070e030703020907030c0c080c010b01120203090604081c050a0606 75
    0x2d0041c1c228054212001d401445040a01410168000d88401495407180c54600050380248405000a003225013407010200f601c6422590410b211a00c0864242e180302c00c6902d82400c1340a0b11168a000480f4000f400c80c00381010400307980c0102d24a0901d00540030b42e00001001c4003052407085580c0b40c80401084200140c468042c406008641010751015034550341d420110b208030b000200500c005810b00032180c4d16401200d051044014000c941c01e40b409043c020381c052100e01c11002800e40c04518003000703801c041605802400d02d07007602d07040c0d42c4a11114070090142032410641051050244014041c410040e0801604884c40079580d0f82c00c10101c000e101a03000d102050180c1d0201e03900f0001030300e43c1038109501a909181c0092501c0d04001d08407881e003100d050107004d500340484c66014409040d448000407030780036250150b0035140d001d03600e81a40022142c1c40d40a8101c0800178000c9411000182601d2075008800c210224100d5009001c84006841c049041603803044140b1099 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 15862344 1250 15861094 15861101
    0x2040506011107050105030c040509180c0105040e0402060d0b090a050106020f030406170c070c030606080712050604021e0301020403030309110603010308030703020d02041a0307090b090d0f050c03150a 88
    0x44003840c1c039810550162642d035a50709102c3c81154100040000010499005101601c000d802c0c010032801090800e80c0c02c0c41a80101c00201046e9401410a0580b49600442c11034080b40c40c0b005070305c40207642ea1f40810005411074000000c0c559155004c2d501d43c0c0e030b0f032820201c0c45486000d100013025410030000034a031008403020500c1c10340c0104824001560810906110b1850a440c120f11681d24841144424041d10340000c004951504021080122a40040701a981c02004603440c0642c0d032500c181e0311015004c805400b9811600c04a800f60809008007040000f0800c25051580c402102003802c80c1d015900a4002a68803590402045043c000c041003035a000c0743c4190840d4110340303c20340c1c07038400a0107580925078001021002c10005030162001886140b0240032a4034003c0702c074200039403048035500001130021f03001151601282d07040d110000340140c8010481d424a079282181c080d0038803003c0c1d400c1e1103514410304640d9420015100075003844c186a5415007401d06188054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 15863594 1250 15862344 15862351
    0xf05010e0102090d020906040605030d1710050d030804060908031303030f020c0304060809161d060409050705010309060b09040302030c0f0309030c0d03110105010b0a0212090d030305060a0b0403050a020405 90
    0x950b40100b00068240c0e8030611000041901114041c04940380d0740d00040081080394800758040c00740b0241c10a000350890703015044c04921000014040d80d4003141c54428400901849500807100407585020912982c0c0655000b84601d100103481a0070340c60381d60310f0350400c84459940582610ba00c00c1007650500960b00b0394440d0740e0066041414174800700d500e0703000d40d0013880c003040f58408c002003200701700b00a072807030700404003445c042c13925112500720489800985030540f100400002203180341c10301c1c6c4101842c40d81c0010103401d040e81464011005403400c01010341d240c0c2c2d03c03881c00380d80d280d881c41c02031070065219800650b07481c802840494100424a584021182c000344031110b040c1e107000c034443c640c4285c11140ca100310013080c0703030a1b1400608900464200e600e07100011400c0d6a04100618a8046030f03000c648036000d442c0400c504070302c100101160440d00780e09140000030700a41207142c20010040240030f00ca511a2000f102d29002a0300503101070380300c80000c009508240c800d4981 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 15864844 1250 15863594 15863621
    0x20d020111090d0312140a0e060702070e06040204081504110a030506010b16050a050a0308060303070317060102150a050601090504060605070f05010f110c0d050406020d030f06030f0f0501 82
    0x2001c0800c0750426140e010b52652940140c041e1088402094403840d801402c8200c090401c01c40c2c0b10030840c51241c074040c100c5190310510300c0d1a00e1102080000a00305c0d00c03403070683d4010f00342c4504100b1040c5800c64041c002c0c60700250248400300d18540144041000c3c1600900205035910742030400c8e0361060004016a8044d030004034003800814804103045056404034131046035650f5240300344414922a03800050001e01aa1040e00100400820303441031403030003a03840c2c150780e80f660000c050300c0740b140180040c0418142c84c03589a210041c45c0c0c50395408007050058a0350b06850962030303d0910303802c40f4109201030380d03581080640d40e040100300e0094202900c003003161b9402c00e0800b41041c4504040949546058944078041084c02d410540e035001c03804800b0f00c802c85800b14220001e400006000c1901d000e40d072140100b4510440c240c2742100c42c190300603c0348a0821109a005013030644900201545505021021403075540084601500c43c056051400070282003890858080500182 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 15866094 1250 15864844 15864851
    0x110c0d030e16060c0b0f01031a040c2301090504020315040b0d05060709170102040e13020f04020a020d030f02070b01030b09030705030f0c1605030606010509031507030509060106030605010c0f0302150109020a020d0201 95
    0x1c0072070403025005d503140119009c06090f075203a900307003d0754040c041d07840040c00c0f02c041810000300912001140c00c60f928280c9030031403407035107c0041006a00044940f881c1c11148100416114078007900072000d8020003519049001c0d00c207031115801c00404071003e02c00724140001c104500250301e104500300095040c000c40c2000d0401958885c1c1030009850014009980f40c0c51100303641da01c801030044c8150040045564a45c880c20107034451000504400209207855440b800c4030043d030007240c50880d44503802c000143c1c00c0d40d580341c0c899140a000601240b10510125001031020002001c045c0c0041c030004c1d0b10b40003102d51491414964003400501e00502e808104000c4d01d0004002d40c01000034200300340c5034111040031a260122400300c551845108405208500d50917500403400307881c3e00da050f6402a130300e03075800303074240e401078420765000458000d034000124802801454045200c0d106030f90801d0406001900c81c0b0b28203030040d21925900082d1014a907404115224071807c1500090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 15867344 1250 15866094 15866099
    0xf02030903060103030e06160c0f0b040302060d0504031b03020a141c11160f0f0b030f060105030601030204030b1e0709060c020d020105210109110c0d030e16060c0b0f01 74
    0x6502d0700010b00c801001d2251200d600b04955075440c00340d88258802c1081c6040700020360a2100784216140706d01c8580d461100c0e000301d040ba50030007c41d4156600a4100c5140554104401000340b000902c15820080c2503c8848a8104030f039814008c16802540101107010481c140562440d10b10001c99102d5800007034420101036001503136045482083c00c180308000e120950382030402021302c4d1030b2001480300b10808120310704482001c030283c840b0b03103c0507a4555100d400041c1d84d48416201010815541400101258407641c021a8006010314026007000d03179035a03480b4a600801d60f5a5003142c070f8aa9003120340300b2189403200d5401503480c502040728915002c40980b224207a400068080e41c03205581034156400b4201302d480206044803507a8904410a070f820700312401c2030182c100c103182410b820307034030500b4072000f511100d91000c0080c24035065550000d4004000c2041912554010326104624050760a02880000c0c0415100c400d481c003036a240c010f00300c100050402c0400c09828005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 15868594 1250 15867344 15867349
    0xc010e01020a030e0f03010e0f06070512150409020901060809010b01090f1a071703010303021c050307031d120a031404050a030c0c080102071a0603010501030305030a020d060503100204060f020309 86
    0x5060810f03425080c5079121801070804201d642c0c43d00300720720ba0158201081c2c0052003a0009050350030786241e030107030380d4551507140d82201d0380c0c07040d9030101810f000420082940001e00d9400c00c0c24080004000043c2c4500035800705011302026031081c00030810074400c110170004203001d05086082c0c2481d129060303c1c1012401c2007016080e028a1580003007480c5101142518441100e9920383c0104840100d405c4404990400340d02c2400205d0060048940140d4510300e45003003a10015800d403242811039a549900700d008001c42e69007401e00071a178088070000200107012183c0c0706440009055950405100058195101c42403030824810f0468100004154041030114800b50b0528086155280f58282000010102d1704114100d5100241940800010b502d00080302e00800c3c1c038800d015501d00e01094201c400c02d01c00034000c43c800b000000d20002456004220050300d407480051850340320300100c0d02d0104030071f00c072442103640040d0600c80950400c1c0480e40d80341d62407004603d0008444003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 15869844 1250 15868594 15868603
    0xa06020304030f2109060905030705010902031203041101030f0902040608010c0e0a080601060804030903050706080105040f020903120f04090501091a10020c06030a06030b070810120c0311010c02090901060302030c010e0102 97
    0x1300c580c0d05654400c404400c0040c107400580c82d554100084988901c0c0909140e03008108d01c8400724803a10540c0e4841d200c1904010943e8402d580215009800381081001940904038809982d402c1b140d175038203242e0042c3d58502c40c910140c00440f000087e00649101c3c00f421902d0b81e820b03214483c07090b82008111000c40000c04c00d05464040c07a1000c0b40d0340300e82c68160ba44405a41004246015480001c1007056003c0c58050403554100c07000c2c0018500340700e404080340308500710640c154100d031086051000c502c00c010185005e45030216454180d0303800b0001c0031103400380c201410190302c65880c90707140c5085100d080740501084900308104042044003a5880800c02c003800d01842e030100028107800e001e80e100400441e0851001c90341860035600090221004445000b081664030302c000c100c9181d444a0340300030790340c0694503a100d07170f0a41e10f8041c50300d002d004000d0304002540b88035100503121501a140951f510200108440d03055104142c203000d500e0912074100b08a40760506810381e03001a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 15871094 1250 15869844 15869897
    0xf01091d07120c0f09020304060b0631170705040e06060307030f0804090f020a030e0c01020a0308150d1a160503010b09010c02040c0c0605010803091f030e0a06020304030f 75
    0x30502e140b0048910700240740041c1c90b4401402d00040d64400070315070085800542c812480f981040028000d42c404010303603401144d03036610750804106c000c0f441c0c61804071441000000401c92440005a642d184440403d180304564100b64104101c108041c0c00c1502944c402c0c4000d001c0981000d16200c404680c0d5038030f0710f01c0083c1c81401140f2401c0c0c10300980c44d080f1009020040c90901000c035030303259100042d5002d1030241000a10700002d41050b000045402c0c585840141d01400301c0e400786440c1219141c2d40980a00d910340c1080b402241c1d0b0740e4444072254140391088040d90340c1c250400545060f101030040c0581c1955001c0030f66034940660190072a030655091500e101c1e110700c04680102c410501c40b080080d0131520703040d074441c0130784d4000301c210380e46612440b130501040e07807101c05050312400b42a034100d8000c4500070b040c1c2d4961503045000c804040c114038000072442d4141c22130390b24000152505682d001d42c0001400249039000018161080700c070705005040c0805804d00360f41c03042440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 15872344 1250 15871094 15871109
    0x1200a030905030a0504031109010308040b07020301020910090501020d050f030103031b06290607080f0313170301060f0206070e0405070c06020c160509090606010f0c02090f01091d07 80
    0x910894800d009a0014090030b03042001c99499010441020300707507078001c2c041910841901c0100001510b041083e55040e207601007007290916241003000c01031504a8141241d241d502848012039980b01e40b0110782b91102c441d40d80121f294079100002e424041205128070400800b01310240507a1078070f80403241165032618100071100d4030341c1900108840004001020b035030a2099185000000300042c800040014500ca00041c402600304200c41c46031780070041480d801440038148280c800c1e0090b41d440b01d42030408011940c46603036020181c000c1402602c68503140400180800c0d58889034800d03500c5801c0c0010100d81c2044000900a0018640c0491103030b5101c2e400519000d12400e0002d030840d502c10001e5455005440545071a682c48005181c64094010000580c610703100c49018002c400c02000f42c03030301b600c50318011158010070030540c02c244411041c2c00c41c0181c40300310000744100c80d00042403c203541817004010a8450414002103c00c0300414507a00000c0082007110465800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 15873594 1250 15872344 15872347
    0x20a030c1212020c06010302100c0f080c030f040305010c03140c030402090406110a03020405040b03060c030f090a140a140d050f130312110601051c0201030b0102010e06070207050108090120 83
    0x788001203034003070040202c40e1409400820000b1031481d00142c0075058903c01c5416004102c40e076542240d810f030301c4040280c58103c44542400204520b04021310350310356802c003524a071030703007207944081140d21a900c101c91981d1350710700032240c0c140d1500c0b60001c41702420800064138204520340c03804600000d080a4402c0703c580000c2000c000041d44000c07007201060184a4840c00107610240003900544160782c01141002c152240ba40750106001d03200c0c06207181481d0550311900b0b03044000f840b0081c0f09608920400311440c01041e415840152002284401045400c2140c940042d0500b07080f51040c01a0740900012559207800c84180d94074442810385081d124880c2c04140b007034003903480d40040c0551000758400c0c1480303a401441600d1001f06a011260541d9030340050104864200281ca29941c1503c020a00158440e07001b04814080520000c5000d09605c6521800d04500344c0b40c01c40580d01200c82040f00c1e5802c5000726a001d5030ba030008009141e400004a41c280360b00f03040038441c0440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 15874844 1250 15873594 15873623
    0xc0f0903101506120b03060c0703030e1906140103020303030a0e0a0b0f091603050c0105030606070b01090e0d0516030807111506010e060c070e0a1806020403020f01020a030c 76
    0x24100311020034405112400d01140e000d4100030708107104940201800291440302001d0490784c41d00607400f44041c05002884140d8540225070415040990b0450406132108080020748104100204d0243c0c0341701d00817540701c8044d01e403d0084640303250b601d5050f00704520041000d40d0300032084c0c9c1d50100c0726143c007262200782d40341c04038100f0941030b6000707001c01e200500340000f84000c0a025480b964440040f074554036140341144062910910004185501034806407150794070400203150009000f800140c103011061307440c0c0652080903045400c980d0303503070600448540010080d01040c00740e42e00308545070801c0b40450f01480c00c2d07a528041c051050030b10200394034510801001d884140104151044800c10294084003500d082d940340d0b0004018014068182c503121044a01880400008215a9250500c2e103881e20034000c00107082940e0f141c40308600c4103e6080d02013031940c800d2200685ea541584100500c458130707020064110744c08040c2e001c1c0002d40110b4031a02d041d07041082c170041c440 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 15876094 1250 15874844 15874849
    0x402030a1104090504260301030206070c080102070302010e10020906160f0506100518010501020319020715020102030f070305040c09200a0807140c03041205070504020301030803010f0803030c0f09 86
    0x515105024504006000070300c83e03030310b60310403030181c6d1007000085c110340c003c0e40351032031051480c0325040401e007400c20041005141140080039103d200700c2c2000306150b5038200d40c80c02c90300305080550150351240c000081601042c4a50a4003880e0411b08604000c6070340003080807401a400414076200c0000b20500038030407040b0400c4c0010758007204076021843e10030100180294680308480c06505001208550341e160816081c6c1603a00680c001c50900480015030000f441c181210002035006841012840403034801d114100c0c0030840e000940e490500190307000c1c10010040c40003081610340010f100002d002d1407004030071244400701c0420700940c082d0240c114015141c4180d003d02c000010180701203038100316900d2080d103d98691216840c40d08100708030314030811011100c1500100018042c545140003413207407031030041013206c400540b0707480410101d80c02030b003040e20003d030048010810180824481c0001d440710002541c00d6040c180350b10b0001d801414600d500410003c110081140c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 15877344 1250 15876094 15876101
    0x609030a03020d060b0a09030c060201061202130b0901060203040305190f02060309030d0501030b0105040b030d09051c05010e01020c0601150c08030c0d0501030303050601030e060f0403051e04180605010c020109050402030a 97
    0x40c90305d61092a614401068040c000e035a040c441240e00035110040050a180103115450032106c0d464400041070b000c030380c01c0081154100800c0d078645980e90001a640d51141c1c0b2a00e80a0320315900215a100d085003429407510b1811004020072003c0d41400000144000c424014510380c107480054031f903150300300c0d91070450280b502100c0340039203048000414030100c039800b1812900240c0341080707111244403c4c50344070b1400b1844003006c1507820008002c1d83c03c200800d0b6940b450a6446001c9001e0959540c500b0f481c201a01c0d13044030380d00071a13404130185080c0085030060009040074241c91040a102030302c1c500815001600842c130100019003403000d00c0085442c2001040c2c0100803540e100c1c50090000c0c107042d0707901c074006031410f0340596280c070000a1250140011000c040388a07580d6035402c03580c1303038004c40080700d603100800e548800740895140a8006400c4443d006009007031003040d103d0844217158002c0e410488414503400150360001460419100240d502681c6ca50710700110b0303000b5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 15878594 1250 15877344 15877349
    0xc050c0609031306030203071d030c040e0a02040b06040303091509030213090b0c070206040312031103070c02090a1e1d030c07090b0a08030a030504031b110406080609030a03020d06 79
    0x240c05204100700301c040c0040300904240701076880900005840c0c140c110300f203010482d5110041440303107045005451460840440c00000141141c100d00c40c01d8000c10152030100c2d522001a80c019408101103203070500880e594030605031a0349007031510b561001428019140708100401d03c00980d2200c5040c4150b10f441d01964025051075044480c03030001030010300c01e151042d14070009140c04145011481000c03104480d400402d6141410708645072800b00a40240159081c15a03031501e06a194003200d014520600c0c0b0b648405000c1c2440d1b0042c0303e0791070700080070b01920303500e4100800b040308030708121426126806100062000b0f01120030007a802d10301115503000b07100c0031800b00104034000074418255400740c1000c2c00170120103828004280b0341801400c7e01600180202d280142c825031000754090702a01c1e14003d41c08101d1403030300c1c0f4561604425641e5101d15000039146041c6030090000801030100140000d02d011031005480c1d004e803414a40802d030300000c08003805075298118402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 15879844 1250 15878594 15878617
    0x30902041b02030304050c061602010e0406030b010e04050601060807050403060e070503070807090612030206040201080406020403080a050c3901020a080a050c0f07050109140402160302010b0f090c0a030c05 90
    0x4000d900318000b955030f07001200c0403191441554050390b4a4100034041d2844004012082c000074032a5500542d000075030364548642003950384000101140c042000c890017882c902c01800340505190a00c01d0a010058103c1000c3c82042400d000781a540309049908482c1c000301c0001c2d41010b0442c04234180307040c503803085505100d00070f008a200b40303022803c20100c1e442c1160401203039030b44500212902440200c003902603080300c400500507500641400780e000d071180030b0040c6040d44075500ca02c000d410201c1842d001440114408840c3c075800c2291000c00700b80d48a207155803c83c1d03d03500300144151089400e000345503000c050503482c1d00070002920401e0748890f0454840300b0340d0600400340e40140902d50300611841070301038100341d40420007009441c2d060307454070b260505042c0a51030201442d0754250b0042e03820000d1005884100300200f0000e4030a500104005001038100480c000c00007621902c141c46080620000100e00400c031203214141c5d040110302c4000d81c00060b1560701400c0040e24 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 15881094 1250 15879844 15879881
    0x90c03060703150602060405030a03020903070306090b01060305010519060f02010b04092001050406021c050c010509060a0f06050901170307020a06180605041503090203030d09030804022e03090204 86
    0x40c0181d0150006840c3c0a00a80c501d20b60ba0354603002240d0712030040c0d4000e4142d401c01c108952601740b00750024140c0342c40c0541260700a40c0d0320b503104000c035241503105840d40e00d1020014410b15034940520b5004200450350300009088000303a88448034514851402441240b42507010528001e410403c4507490003802044101160304000c1d40c0e84949428105d10080e00c490304000c258041d409540030346e202d55008140d21061440c804172122002070340c410520a0034030011841031024000c0c0c80c030454034080940b840d420290500d60a17600c030034003100d0656080c03035030502c06d54503000c50060440d1020381080b0454001c6000150843c80381d404065003245c0ca10318040380b01500b0880c080039500303403880d0700898150b075507000300c03824015070086040b1300560b034540044581c07107a0000780d00365000a080e01d00e4084000d01c1c1078202e03a10394004601048200c0104015840c1c2140c005842c8100b43c810114008274544000800045205005080c143c0d40c50b1120103544603940560344210f032540d0001d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 15882344 1250 15881094 15881101
    0x2100504110a181d10110706240602010216021e2d0303032419060903060608010905030304020108090c090703020d05100506030604020c0c03031303030210110d05090c0306 75
    0x10440b407443c444144001504003240500d04040200851601504000c0a81040c3e203040300c241c03024114030410190042c400344100d40206800f841049125801020641d01ca00103114107000b0a06040c0d00c60350a6920500880070141405100c0e5a440b917411281f05000a0400241000203c40c0c01a90f51304417102602204d44070400b035009034010461060710342d081040740d9040590303d1000311307115168422402c91400011201000455006400030194010307074005a01081030030496078403080016400c0402002031103468421a005400c901e0020300000b011600c40b203559201c0a00002c2c100019076001413201c0c0014041000f04000007441c08826050040c40100a5000540c8075824a4a400045940130b281d030145101100c002401082c150354034241044003d4018a003014058000c0000c80b00c140d0360240001c00d80e00714550030051202d8110b04000340741030300905070040c400303203080c1c00c1c0560303c07030004140e90703002000e081c010400f6034414001c242400c1285900766014030407801071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 15883594 1250 15882344 15882359
    0x2100908030601120e0703140a1a010f0602070e01050909070e0a02030708090a020d0602031302030601030803100b0a2309040903030b09070e01080408090a0b12040b10050102100504110a 81
    0x4500920003661070850b4000c0302e411079070840d5801840443d05078021b9004000080004044604c1c0321041c409840000285440704000d000101640c04070b04100c19005108400703c9a8520f07014201610061182074200988560840c00600540d4462054880024082c0008005a602030070b69101240780341d0500e050072601941080c2c5010010a0101300012143c400014103550959001040b9202c0006144c843c90700a51020340b10800311082080800c0142e102082980d0096119549003541e900c0c00610100113140182c0180901e01800c00032141580da00c61902e0340101800d201c002880030001b14110030601c100460035411600b0045900203050b01a4001d016001d02a100500c469860f40c0e001c49503400351000942c0800d030081c1c04140414006409010348080c00391040c141240c030f541c400d9100380c0010401070a0395000000300420850820101500a058031048145407400c2a0010b51a065140044003000380d903000001d090000c035089503041010301030315101c1c02ca0b850b10913 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 15884844 1250 15883594 15883597
    0x912040f08010f02121b040518040b0603010c0207060503060d0c060c0210020d0f08060a0f0e0405010c020d09060302030a0f0e0a02040e030f160c03081206010201050612030301090c02100908 83
    0x903807005519119a0b58a02e421900868407000d60740d001c0034500c0d9070380480e02c04002000b4840c0910002d003d00012402c1c0c0ca070b64040c5825440161102c82003843c103894140b0070300718014400c0d40241d040004800345141c00240d104155440e608280361a0369900000c42c0e641d1400040240811880040005010b80c000c07680f18803090080d500c04c40115003000d016662007040a03543d100007505500850b1200c2d108454540d009500100000f0041d950752045056095154000c005054614414002001030034404c0d40c042c041d081c005040280880390f005005590684600000d01d40c00100207681d40e0407a510154401c03100038402c00a0b01c0d828401280c0d28811707840200d000e42e20b00032400540b090000281d9410815080388145846002109401240f90100b42103404000ba0b1402100180040001d070443c01140140d400d40340c54024002402c0d02c002030704d124041e07170f440003101141d83c82c084212410350b58000b202103a030060b8114100d203030143d0084218041072610780301d02d00b0440d2050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 15886094 1250 15884844 15884849
    0xb040201080702120301091109030601060e01090806060f0909010212011413060b03060d050f0a0b04060501090903020d032d020705070501020304150e010e090f040309121a0912040f 79
    0xa94007101a41c5100c400ea0b51450300320081d0300316007010310040000e4446070300300001c40c0e40844240c03030400d040f0700040791400c1000c2e08120041441d000480c150755901131800d40c001c1c0801c1c0c0050115041010114141c01040040c1c036020b110f0900001c0d013112400d40483d015821288050006580c0d54015805501190411244203400c03a180c078501d803111500452094031045029285540c55035800c00c10000c100035001c640301c0c024a554010941018000c0f69202801102e840500789080d00e855422250160040400e00345484244000300340e00003100700f0000d107507050000305d601403c4140401031112a00100d43d410401e0710341c00f407108954000e8403000d8424000c650810b5220001a0780b28001c50043c5c900604004c440100442d03c54103d070813003201c0c103040816041c54140d02143d0209005c480e5138000d108600309000805500c020b90b43c006014030768a00304510065030711b00c031003c0941c19109001c6206031000c44c80ca81e03c144013038590821080702059940380c0c2c40a401001c0c2c80c0d2403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 15887344 1250 15886094 15886097
    0x30501050301050603030705060c03040201021c0c0302010f0504050613080d0e0c0913120f1404120209010e06010903060209060c0303041b0614030103061805070b0d0f02040305030901050d0e0106030b040201 90
    0x400840e03c0d50900000b51806076a02c00040d0029690301e4410ad01c1d203420040081c0d0441c410301c200d07020742ca80802401034101000341c0c1e5404c07900007141806405d50300c0039035074400858900010080460001b2581c15048000d06084004100c01d80c104000c01e405202100d0716034503e044280d000d45c200004901446081c00d481c0352025030b45442c02a10b072000303545400b03441303880340b22003840000b07104481c503800180440c2007031031100d6151400c43d40c66800507042040020301da080c0202c10351030401b0085d8010644020b441b04146040c10000f8400001c0d440010711440c0c0106441a00741e07104815500301b0f5220004507a100e01e401c1c04c0010101c0200d510508802c24140c10118403644911422a01c48104081e071504e141d1035075032040c0007840d20103240740050111020207800500180700000c010074054450b1603c880e00304140344111108a2402440350f40704210400028101000f0f132500c00300b00b400c100b41c4444414020101400a40c5a800002e518004000c410001085850390065000703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 15888594 1250 15887344 15887351
    0x4060906021c0501120f1209080706090806090f1002070203030c060703050421050a050304020111060403030507020c1e010305071709100c0e090103110312040e150a06080114060405030d030501050301 87
    0x2c801c0175100c0c6907004c0d40d01420f048141c04044000c60f00300046204005458a0070740651a40e980c1c1e85401e0643e00c2d0081800039080050400028104012440e0065030b0280034054002140e51030300e81c1e52025045422100c1c0e0041104000d6540c07c0c41a50218082001a03801d9407502840c0140200700032103044401003100b50240b10544030104903498803c6064549a2034100d078600142e032680c000810813410000c0c40f414608803240281b01042c0214880e403004074440c10181c20282c04c1c02d0400360200d000f0b02d1100d1140f00b0006c200300746400b01e0002800d00080d6074803030103001c039080403040c40110a098450b006200420300000344c03d001201c4081000c02032240d40000c110358003c0a0ba9003a60711400e21001400858041c0c00001c121450041c11600f603105d01d02d0200b00242c02c1a440000c1041100d070801010180341c2c24a003841c50012244010a40c2c2408009000018180584088054020780190080d01c500d41120003506005048540c3c0b86000c200c018060402401418003950a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 15889844 1250 15888594 15888599
    0x30105030f06071d040608031812010b0607060f020c0d090614040b0318010b0d050c150c030a050307090306060801020a030b0109050607021c0c0e0f0106020304060905010804060906021c0501 83
    0x40b40b054014252580e8a100c1e0450300d00c0c03401d0641c032a051502d58015965000019030f84c1003000282130007040b903220f14501146613010031a16011703818503030391103904241d8268020703a43c500032140100d9010100052140115003034900a001c0c40e94810820b106026201c040e454002c0c01400450b4036550350704d80036440b8104068514011842210340010003403022840403c2014985081c0d01410030000a150b4003a0001600303002000806890303c0e08650a0300d100307400c00d1281c81000c2e00070b41545515000c00c120071180d40c0d124a0403e103082000103c00709558520900008008540042d070500c1050f4440c0c071454001d41c4035060b038501107490f00420440c1c0d9401200c1740c0e81111030040040741000d800c1d4081c00500f940003400429002d0000070028000b0340000b00c80c50182202402030700340ca140c40107090281410680148056600a1004000c4c07075a20101c00d100380c400a1a080d0b04a865620380407003d0410345000402041c004150300290340a440c01031000480003072000c0c04170b640d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 15891094 1250 15889844 15889873
    0x1120506091606110c0301020a09030506130503070201050703090806010e0114010815060f0f0f0405030601060c0206071101050d06141c0b0a05100305010903032009101101020705010e0303010503 85
    0x70010620503456050b144100f12080c060200f01d03144605000956184105e120006400ca0b8400845800410482182401885000c00015621011000b080d06000b480ba8640d190fa90103001c800070b0410000149500800d4410840780004101001c101d07480c80d41c4aa00400001b01c0c01d000f400718002d01101c0003003240d0302c10071101d8002c0c5180802d500e1000307075090502c800d503440000003400300641001083c41146031705c0010304819280b82d9040ea2654180b400309810540180e000c1c90402000002d243d0260341e800003260341c160350003003aa4020506210068805018241c07040384003030700c1c0500010300c411029150314221181107a1108020100f44403070500a584c9210152001c01100c0020341c590340150700264110900c0780c0b0072000305549070388090a60740d204008800098460b0003003422105d2003103000c1ca4100e000c2e440541440d0b281c801040180402031003a00811013500c1c0d80400c035031001c1d8101d680454001000f8001c03000b41d130132129981e5200780301d194064484c00341c1c07038040300c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 15892344 1250 15891094 15891103
    0xe0f03031e0604231b07050f0705030714100905030604030e010906050a0801300c0503070e09060406050711070e0f0901060303170604110a02010c030501230607050c090112050609 78
    0x30900c0070080411141c10081e0301d520000411908640c1505c03058086500901006019403911580c010814005074054890600c13140d03511036800f81d4080602031045520302d110445015006881241005620751400ca070540501d90045800d8042c0200780424141c5c0599585020b6100380c9400c0085666920300f142c0c2840749001c100009039800703005000b888000c80502a0501003481ca00c80922070405001158020007a8116404840d41c1800c00482c00c00703009100041c40c2c00c114042da6032420303c1c40e0540303c0b54014001040c203039442d4005003180d4096102912554000f10803551019205c0303022640e00d080aa039842d03410380c40754001400614050280c0d1080d25410750780e0b01a2240065990b078010540501071136403094485120142d0b10801c08040c1224103100d5001281e0380d2100a00503007203038010703001500c41c9000c1280c55003101220400010b00b481003501c0d882c2e51a80242806403e2004844142d40e0018484d0000140003143c44841c042c1140204240c07995500c400301e005555 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 15893594 1250 15892344 15892361
    0x70e1e030a0605041103030a051207050702060f070606170d08010b0711150403170405040b0a05010e01140708030c0319020403050a020d0203030706060f0f0509100302040e0f03031e0604 81
    0x6034081d4040d07400041c110380015030014403800144640708451000030313083d0340221401034005440400c0401c0b40805080e4130542260150504030300e8505182c001c034040c1d1294440880401400041450400c00d541d4080c00041403000e03c0a40c4c400c08820780b040d03ca820080e00748000901c2c0000104000b000303081240c400c160b0090745201d038950542c051041d500600700c03e4008040c410b2000001040b801070102e2031211303d8092072079442e810182040129170140f2003190103600402000e01083c0d820102d09240d0f51802d0074101c1c803036030825041100f24401d9801c02450071401105020580005101442c0030700c0c1e140040f494100c650000040480c000d51001400302e5021161040c0541400003c41003001d00280035a480d00c103598664209071b5200768841d02043e1540c00c0300b0000000100c0202c8007410044030408030034146202851480c001c24040640f00c0c540d1607052010158040001ca01c10500d04426a600d034030341a00d044441d11807054202400c000c901c03001401c11b1a00c1d03c00e1003007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 15894844 1250 15893594 15893599
    0x1a030f030c0c0a120f02060c01050a0f11070c060509060c0304030f020405010b25020d1a07020d02150f1f0b0304021c0f060b0102100e0606031509030703050906040e070e1e 75
    0x180750419241d004041c604045d060f600050200b01d01450001c003030150501c07030921854082840741c90518000704840b120411820000c1041c4503a90025101c03c002008580780391800e070340c44841c81030001c1d60f14401c40c200900e0610002600004200301e41007012480b5008035401c00036680d0341c0f002580c140c418503107412000d41c02740300241c119a490a00f40e061560016210030024030a0381c0e6005255a00c085181c814000d6482c10407001c990704001e0b11085c042944050140c6c0455444106051107015086c07508010b4050000340c860800180c0c4055400045c403901c2302060f0352039091025551003510b040e806200440340149a10007203003101820035070700031300ea0051201c041e2111030091494051860444c0600c0364004040f440d58020010020607030005840281010010035241144480c02404140d80030801c02ca50600d0200a031035035140c150030701d40e41d214500000107403a841160802410b0100c1502440b10040c2c2c408951034000605581315640302480d249019209810b80d00d9465 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 15896094 1250 15894844 15894869
    0x120406110703021903020a0204060801050a0c030b0105090108090c0405070f0212040b040b0706150f060e03060f040f030507081314091909080c01060e07020d1407061a030f030c0c0a 79
    0x13100e0140c2141118a085e0107481a1003824019034006400d4800d554040c2100ba1744400c01e0180d0220301e48038a0310071500c2070608000e1130b480d200000c2c0460080c2d413501d40c14081041c002034856401803105441d80c8000400070400381c907080340054500e01c11101c610005201c2d42580a4002c3e9400c0c044800791688154418203061400c1805650796011741c41c03c440883e16051010103149440c480c04d0003401314200740c82100c80c180f0500070820085044401e100b86e000c00c06020358a031003408840c1d040703500010301c60034101407400c040d00d90384242c1d540100504000038108019080c002d140c5000e0b64038103094000034400040c10000500020344d02000103100840d2544180c04659000c100e55500c6030904070300f072040c0306903d60308507006a0f100e8071351100c9030800c1200c0c00e0380c140105802810203060074030035014144005400d41c001c44000402003991001c001900b012640c00301058880f000f03048407012481a09196269005800c4d04812445041d002c3d40d81441d09801c1101034404001040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 15897344 1250 15896094 15896113
    0x902130e010e0a0f1a07050403060507020a1401020309010b0105071709031203010806010f0602150f06180108060406060806070203030f060402090306090f010c090b0f0a03020c06040b01080c040606020a0605070e0612040611070302 100
    0x1100422001ccc0448040d44039000044000500d841c03140700c035654130760000688901d8010010341c25252000e920034100a810000200000e0025010385001040c00702201e40350204040401e250541c000003048102a000c800060341440002d074890603200c010504901203070b0354041c140d80d200301413543c40242e0609440014113002603041150b0b400000103085040b500884201d40441e04003e0300000015003098003044148016070052400901558000b42014907021f50000d441e80009000034205140040c0400c0050b03440d501541c100e400000c0642e056400d060881c41d6540c3c07100b202c0441c2c03550138060381c10000d50140803401c040300d04400d40140341c4601d10141040da580440b0000041c990300f44101c000c480c0c1e042010a00c20303440341c001488154100312501d840d03c60413515281c45281441030070300c0784590100742d2000a40d84110085415100d880c81074400da0349140c502e0b50016070205091080a04103e10307140601d0199008122201c40e80305400d10503c505403000c2c000d41d00200f8036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 15898594 1250 15897344 15897353
    0x50705180a09020a11010606020f060c070f06020c010e1221040c0f080d140301060c110307170307022103040509100b030106050901020c03010902130e010e0a0f1a07050403 75
    0x1400000500d035071502900c401d1204201c0c1c0060020500041c1d210a020126038001d101d45400f811150005010a5030b419410f255180c400910141d01c0740300202c2c0340b0003084400011540003a500150554030f5421882c500b138002c00c50201e0401c010310400c8804643d800101048815141098688107044400d8005036510503d024200319000c0c96210000600c90415080181c058801d441c09800d4515030007500806850304141c20003d154030030001001156008180e440300b480d80b201c40d00304140807000019081050700e92050f0740c00300d004c16100e203040201100505049100311a030f5100d412284900394242c0c240300c0300c4401c40b984208420f11070b81c0340000d942d5511200e01c03925501100d80750300c480407042d04203030f0000000c00c001180c6400d6540c0c041c011000345802c142c00801034440c454001541c401e030140502c981850b92201884803009080d0001d02e101d08180048840d00c4c4102c3c9403012403207003502c809840c04071b120107903541e620182c050a58041c100940d0743d54141419030300c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 15899844 1250 15898594 15898627
    0x30b0a0e070c021503090c010f080f060111030c0105011e0905100909020a12080904060605030609060f030102040909080403021908060705090d1406040b06060f0706091109010e07090504050705 84
    0x1a0b0b400000b800b480c1e541300580b00b0040d8460003898014200c001c501d000058900a8081e64a201b0b2044e91b90030448071105039a0419031011013440e103101d4074042c1e0074200b4214420440c0306540d65084c10008200101c5003007a44005400c42c0443d80510365690745500122070041e12860214150840304200252003500410307180c9000030b20054034280d9400c0000c40010b5000400c583c8044007149224062800c0c0c407079803000381902d040407443d6203084400104403541c0200464840d02c011031205000362403d41c156405000e03010783c01c0107804441d04003e0fa0503005071000300d1150848036018030103e14a51000021501000b008141584540a00313684a4001501c03082d0455103940e0618007243c030300306040c03141c002100c0180107181004e041c126068a002000c040c0141c904100c440c8850001c0303011141d440d0b401c00800188c440051074401c001892401c4010fa22050b258004104012281c080900443c01512444041980c9005002c10703200120740942c0455414040103410141124 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 15901094 1250 15899844 15899867
    0x603040204050717090f06060a0324060f090e010c03021201120503070c03060b190b07020910080604120807030c08040204020304020d020405070c03110703051e01020403050706050703030b0a0e07 85
    0x80400342880118440350281c40105c075034241c0b5500424800c11121428040381da003114050300c43c1207480781151030f0019040c18030b004403c1d0001322103e080900c0c400c030394818005044005400443c2991b80c02c20b207006040d104c04a50915441d02c009602814024402c03258811036000e0703050b006a2901c1d941d0b8015140d855425245400308001120000c0c042d0322061002c1c520584001414940701410301556414004000340d021384d4083c0c00b40900902e910070340c0c9890340c0c104d492000c15030358141c20206026959020310410b21401c414441000314034604804511059030b00e98119686106d0200c040c0d403180c2002001041b900e001040241c00e164004560143c0041c140c2e212044055021600f00c810840300c0100180c00107030b02c0010954000125204009180010400c09065407180d6854242c075801140ca140d840c6504c010103071100703406980c002d540000030750380380e6941da0134081c2c1982d22402048001901d4980728a01a140040010050b40c01c90300203a009039650303420554080c0c02c8103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 15902344 1250 15901094 15901097
    0x1060f03020418050a050a0903020304090207050708071d090c011409010507021003021308010506090a090c0b0d060609050d0f02010e0f090a02040303170f040308040f0209040606080c0f06030402040507 88
    0x1c01c40420b07966401c3d040315001d21030b001d0000520303141542401c0103c40300500240f41590401c0000b9010070b9001042e1000d4400f030140c0169100c40398a049454050598820850b601078040005000380c420516109a001d136003484030440d070303503510362945c031921501207880c00b1540b4460a01740c10303541034019140411040c14403c1c5040102c0d000180503600381c04200f00001d800061001e4641c0f101560000100017a5001384204d0a01d8000103003c10001090029866a035801000c20301c1041004100103001e0b050806035654001e0030003030080d100c0c9014410120300504000569810416130062000b60000c48500e04182903500449592801101ca01d0307108807903070082107469886000031805a95038035030040c0d0311451481c010301988640c00d903500f000b56074101044005036100c84000e038000c0c1d0603d00540305903160310b407407208500300002c00794125003004100b1041001c3d44d8000f200361505801281d4082d40c3c14420440b128695100041d0800c60900100780141425000039070404100d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 15903594 1250 15902344 15902347
    0xb010b0723060105030d0c03020a020d020a050d080307030507080f071101060f060c0501050603010c09120201020a06020a020303090601080309060a050d020903010207051507170f180601060216120b01060f0302 91
    0x1c084041c0205000703034070106641082004010518003040392484404083c103221a510300a074070044c1d21282d0700e60019010300820081c0004640e540e035003e0020b071800911200d200900350500b0f2041e038104031418800310340744c4400b0451040c02081c840b407242c160100c218100e039031420401c445881e85056085410364035148045101102d07100d1a0018045e02d6860b21a25401d6081c05829500c028080c540a80d00d45801c0b070400710f030300814810650700e0b150518510f500c258030040780b030064102c0740a840e0f28400315100f030802d81e0101c0218050801c2f4801c42e0030998840d50320b16141d10aa0040940c8000100500c8611600a201618040880d41001410030b00b0034004203003a030341702e00400c41d09500880002d00207000c048800580101c2d040c6480f402c0500170001031103011030003405207070010780b044c0e000030044425100d000b54240f540e030043d6041c550350342d0310282d510000c81c00181818085080081402440c2400600131190429404242d5910349102910400360400410040540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 15904844 1250 15903594 15903623
    0x1030209030c1c03080a06060c02010f02030408060709080c0406180f060503030a03050912090102030a08041b0806092505011b0c15110d08160905041503021c0b010b07 73
    0x4808414244902e64100f0140e01c00c00180b40c01071210a0080400741660f1500030140b081662002280c100503034203003030802c0c07403154001e002c1c1d186005650050a2074031070070080201e5958044000c0046801c0c81007111142000401004240d400c60301407210840d85d021035460074120150000007542e048010000f0319580c030350021074216400b0300750a001080d11003007802210030b010070800d000e501c07a0f01c000c1803c0441c1c400c0000c1d00c0340300d11360f60001003003940c0c001301d014480030700410001303d181111001a010381d81c0d5003032925000c0440320044580121810184a44058141c0042045c1416145040036042000561f8215207074032840ca2a49200040800001c2c4801011009070140c000c1b1050865007400700100041081c1c85002d1290304854914940f041d04401c81d0368000703c55031580d000c51044c1401c1119034840b5640f041d58481e0600401025080c0b5950f15042501c0c001e960b000f0710046403c40314000881c3c10800207298441e07900040110500c4100035100441c46101907000004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 15906094 1250 15904844 15904849
    0x103022d070c030b0402010806011701050105250f110105090d0b0a02040803130504050c040e0a05060102010f0207060504021e06030103060c020102070c031a0603071a130503070803071b0302090601030209030c 91
    0x5000d42c00444480c0f1302d42040c4010366801040c0e85610076030920f420302c5645042c0d1010070780348a061081c2814400003041d070102c230124090403840c802001c44c21712419240d060801c1040354004600694022607440b40400040d48103c0895490040140605c003019000e81e848407110f100c003c206511480d8240300c0410903c20600040100762000450000198104001c02c021078102a16428140b202080200040710700000d00c9640302000311000039150b0380d001e005074007404a1010064019100240c130074200102540210f004a00071740720000d800c581c00c400c0411038045450b030142d0240041c40108001070058000100d04000d501c0050b06054203a034400c0c02c1203115402c1141c1580100e400304200b404540c6d8001c1d400481200204402403410046451900f162903814a400d24000f031401c207038111070340c2c849005000180840744030700c0e03841c00d42c6500d07900951021509007440d00036100052030002d07011426281c00500c1c0000944400c00154004d5006100c099003602400c9a05002d65 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 15907344 1250 15906094 15906113
    0x1317070b0f160c090606020c09061009030b0c0c0606030a0314030403050403021503011403010b060406030c02030c06010e09060a0b06090d03030f05090c030f19030804020a0306050a1a0103022d07 85
    0xa52103020324583d01d0341080c0c1414241d8a941d0080c80c11540098241015030799001840f58002d03e0030f45241501203405c40c400c541001064102604000800c018040030380c03104d400500d0000da40ca4182d44142d200c28003015100c1000e02000f070002a00105600c128001e03540046801600c40c1c1045480c06940f40d02142510080326001c240c041d4020004208150060b1120392451500320000c2000811640024074a070181d4054507040540d116080c0e40481d00810484200031442401c480f80c0d980d59400980240c281280c0300005030045501140d5031202e80d00a039080050b00800316810214074600740800e041d0340c034000b0342c10103807902001c044441d4103201c0c2e14018036000e0040c100e404168000e03d0309d44800800c010f096544021a4203140d003401181402e12580c0c18640720a0390345440c0001b80709050140c0001d4462464041484000a0954085202c2c210f03070418041d0740313a00b10340c0150100d0003070000c29210041481040c0c21140c501d00c3c44c00c0c8503800e404034007501300890380d203407100398 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 15908594 1250 15907344 15907387
    0x6140c070306060e0601030c090905060607080705060601020c060a020604080f0f0d05010806060a0302030a02040905010b090f06101e0804050708010f05061c05030a0f02100e031317070b0f 82
    0x2c040c1d981c1c40511907000382040030366020302c007800c041c07240e403004d00401050000b4070300c240150141d45401241480c0e485200b02c844254105111584540d02400c0041e200c48060725414054880d800503407030b16091030001d5031140f10b0642c018040039507454650b41c81a0f402080301181c0c2880801044040362120303005461000c030b2410000806606004c2e11914240707028001e1b51090b14882010001a90b0029003108400d50503540855080414640130340900140040150700075060340800440071072484882e486a2000c845280c0410300001c415a840550285e041180400b041c3c40d2140c00381c001d80d6680d40061040b01150745250b9181c00380c0b400c5070a000041544180c591701845210304d4110724001c0000c5001c84c12069100403541c855541c0e10400640341c2c240102103811440700f45c024890280782c060200410f0108000d10251682c4035441078000302c072103603403410010a01c10306c1003004c403681030903800050940034100740201440760040c0440c041d0b0340408000288103500801500c800303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 15909844 1250 15908594 15908603
    0xe15150a0203070b0702030306060703110102090d05150a090f02040b01110303010b0a0806060a0207150e06030109050402100824030a0c080c0a08150f13061d0c01030504050706140c0703 81
    0xf2108030a2421155480e8043c005d041154014000e01c19036a407804100c80c0c5c0f00d941401d005080382c0d80581e40c2c5001e4002d4184a40d404007c10360b44105100020821000030f0034808200c149075940d001725001110784003e4042e01280c0403141c85801800c1c10f51000b0480a01414074840c0d20203810703040c40c0f555009800803540a000400e05071041500000941c0d00820115050307400d210040340002d641e01551303ca484003c0000551254000b8020302c061080342d41e01502c0f2507540d40c0c64150103005484140c0382280110b080d0038040080503c550300e0503001e9800d407110b520720041e2400d0389a00450400720026494040c01c4503400020351040045002400494040e28803103440c0c42c20040132985940c82000320b40c200ca0740110202840300c00c0d566002c1400002010781e501c520080111803020340d10300038201894a815002e00f01000c043c0c80c030309900d65a045407001c10440004400b684d1054400400a911441090200c02d01030400d87c0c80c150b000d4480c29041080010400341390943c660720a81c3d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 15911094 1250 15909844 15909847
    0x501031110111c02070f031703100b0f030411041a010f020f010204080f06010b1c020706060b1602040614010c060b040209031915060e13060e0a24060e15150a0203 71
    0x103541e4041c8161700080604503541745181f45103450702c030711000c446010160102070001c0001e859452442e0030f50060140181c40c40d440f00c1194410711443c1e4410346041e24a500b200d03420403804c1c80d260144407041002480d60300c0c0d08a1000005598030f01000300e80c40c055005006084c01c40360f0003440608010107800000340b07940d02c0380e4480c003405d01c1011382104c04440020007140c0c1102204240c942c0014421410040e943d11240c1041d5004100b00e8008a040c01c9000030001c1e0310840b51001c0740900c0b03008440810401f40da580b103806130200440d0f020b0740460000402400850300641c004280240003600140c07500c0e81003c00a420010340c5958920022a04034401e0140b01c10703030b00c2080030a80401c00c00c01c400750410010900348600241001059010f41c2c1c041c03001c2244035000a00750f02807070011203607046868545104032030613078251310f00f0b20404200c90710465101402120115444290340c2ca41c20346034205880884d18042115542050071940401d0318484140001d02000d6515401746 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 15912344 1250 15911094 15911143
    0x5010518010504030c12090302040903080a1a0d060f02070209040503030103110a060e061c0203090703030e0a030206040e040c03050d05071203050403090b0703030b03031308060a050103111011 84
    0x2404840002100c450389030b1400c41007000003604900d10300b6465801c030508034041d07850303c1000c403000407890708029002420400d80004154100742018020000740806100160005003401e10f0720809180c1c15038041c0da52546200821415070050354108140040545000d1045c0c0200340340d0201602d003100c4075480000104203115060000e1084030070704551034400c07a4a4200d0007840804081c018a1244400048804903a903070881001e444550114096440f843c210018540f40c03040e911059000c038110b00807540b0945010104182a01c0e4010004d0b400d140c1080030290a8040c01070003100d40601c2e5001c0071010800c00c102540501d00e1b00da0740d443e40c41c51780e4070f0305959100709c0d1f548030400d0504000500000a0700304244006a54040700755036100c11050800b200944550f8000c95050301002503c55032030117086050000b6541c92800b140e4a588a0b0308010b000c4807400d11020300410303103900180c0d5251400b500403100140591901440607120001103500740300380c094101140900342c0c15079 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 15913594 1250 15912344 15912361
    0x1c06050d0f12050306030606040533180903040b030414060112030306080a0c0501050309010f0515041d03160c050402030f0901050601050a0c0b041a0106090e01050a270204050d050105 80
    0x80030404820b0f460705904606204010a90f201c001904083c8920707281d00c00140d080409140707e144800c2c0305807100d6025011031110030b2420308812621030081e010040801007450312040450300400d0303040f00640c5001e1401c90744040c1c640004c2e10440c3c00c289900a900100c0c1000c0002c0c6010780021584034a5100041ca80a811950b03a0f61204a1507002844071a000c10500314018007224802e0814550726500d07411214010680d07562185d82c802d02d4401440010882c040175046405010758080042000307080c2d01040d44004104410041c0d0300030000038615088800100032200c0c410700d01c80712525100c2c000078080e6003003110810b4081d1000c0d400c11400400c240103130f6800000a003003480c034289002800a05c0500c510740301401c0640741d9004a010007070310700b0210708a0004401c6804042d61030b03d100426103401c0d441007403032004d9138800104803441c042d181102240d032849200003001003c50300c00c01c114500107803940e858640c05e00001031503403100c0001b00b6031184210000101450541c08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 15914844 1250 15913594 15913613
    0x114010305150f010c0309230301050a050405120d090c0b09011403010602070b0715020417010b010f05030a050403020c03010515040608030304020105033706210203031c06050d0f 78
    0x400b00d4070003000c0d040000369200c0d001180d004100a1038100341c1c11406042c01d07681c10815a0000303014046c1017164181d12000e5804821545108034004e0080345c541086900a0718400d84e00a481500f250707131080c409070000b0004144000b54981c010603000c00310b40720305800b411190301254110200140240300da6a002014010102c7c0401c0316030700303650514400035940c1c0b4080c02480c4000c800013031100c1c00e124080e24410000313200c1d09419542c4a8460715044884450119603290543c02c0048180c081d40c05416000b02c00d0140796600f82c25945c8244201000c0e04014000740d0950080c41200e03d0192001e0103024030076940006400350302580381003030000301c0702c1661213441c1c00e030000c3c41480300603039010086a800603108003914461260700c600101d01c21082d1501c0c0c12444a0b006644000100e007904040708032040615103103254501c07a0182340700210140b030001d6140c1c00030880b400320a0007400c1c68200710603102c400000c1c42d035121b00125400182440c4255440d038000090b04007003040c2c40b007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 15916094 1250 15914844 15914851
    0x6080609070303090501050702040b03031815030f0402060306010e03150610030e06040822180e0a1104020a02010905030403050105010f080d02070e0613021201050f01030207050a0f0203150114010305 87
    0x14001c10303001d480c60f10003d0a4000500410317040090014800003076503940c0d080880c94800007020b80f90780c4d0400f07045505c0c1022030702d00b0160080c4d500740000880f003501d4000340c030b2040790005148590b1b40d03120b5007088119840200158140a0488084c0040c0d0701c080103042440050740d00030249900b001c00400004250f46107040c010981412000e020b800300c040761031600207a10404450f221800480d03120340040030783c41514446000d104001640c0e250b80f0441e4402202840010868606d6000348142c881c110b0920160540d68082640d01c032504086d80100012503141c800090001202d5031030b5421540f0079401900d8503916040180001020000e8080040240000038180701000c280e01a407203007002d03c941110458000000740458903000c507031007101c0b00301210441d41d80c403103010700e0b840c01c0c4400c5c05034600a00d100e41010f41594028401c80e01c1d400c1d0040c0081c2034401080c2e075aa0700104401c1c0c801c0f078050140e1000f2a0008204880d842d0181070b0051130415444140c070001421030301c009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 15917344 1250 15916094 15916111
    0x60603050c04050307030b040507030b090a030f05120402010c02060f1b0708011407030203100b04030f03020609061b250b0a05100f15030e031303020312030f01060c03020a08030109060806 82
    0x420040100e968001924021668440c7c0da840141c1d956060890401c0c403694030141c02680450300300074070400007280c8802039510a4540440d000c40109040300d00b4001c801c06039601e00f04940108005d58010800c3d500103e00c000e20a038074181258004092980008417580e51098503050800c80f0344605000c000090122440200802d401049001c16106005030488007410303400404114142001100d11001d45240b03100c10307607241c0d502c0c43c20703603182c2034031503015801801010301040c42e14801041040c01030720300e842515050780000741c9549035680704007144d2031250401e1035001100402071201c021400e002e04481a0a440e00081030820380ba00101035140c00311100e1424813511406144140507500b400150f0a08174141190550003030805040c58504c503c000300308550042040c03c20305003607900c2a019103000d08071086030040076010507181c109040d030040e00148080741c420040404018000e10481d291469640c40c0c024944c1d00c2a0080095241c4800051160500030400345030850303001c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 15918594 1250 15917344 15917347
    0x409050a0b01020307020907050c01110901121a060a02010906180506090a050303160e1221042d030b0c03040b0601020a0302060a0b1201020c0c04050106020f030a030b0d060f060603050c 81
    0x1070000079103034480c00c10020300c21800c2e04003203088548034100b0344041c059280000c200b00082d140c40703401c0e160415095580000c01c0c001c5250200b41c4076004102c045000790004030b1a01c20503000b0007119812140240b0210f650b10000c000111784e1074020005442010f1004841d000d20b203092842c10180c008104801550041640e180010400811241d0049440c00c404001200740581181c1040081000c1b035888945282c0002c40e00101007202c0300b80d10440c41c0034010404403a143c0440350300992148024813030a20300c4841d01421103203032030f0380b80410001055200a07183d03a1242d04403081542e501040070703008800c00042001038401190401024001801840181d0707030000c0d0b54400060030b9036104da84030710203411a9220301840d44c0080c0d032031400a41d2108540c45082d5658003008503000c0c030490074240006902030010844081a100c0d22000d1031604200c40800e4000c0d100c0d21009a4002000002e440045011071041c002a00a0f041001c00d41a140401c01015104082c0021a03440c0c070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 15919844 1250 15918594 15918611
    0xc0206100302011b0204050403080f0a0b0a0306050916060e0a0e190c020c030a0305030a0506010c0b0109050c090402070305030901060906080d031e020a2703150b0307080d02030409050a 81
    0x8281400840e0390900c0e00c3c10861490083c8500140304c0356100030b4120b4201018030040581001002d4070482c0050000300581d0f0b83c102d02582030302c0c0b554042a1700040941300178000304516404c00c5500c030090b441159840c8034281c083c100c40243c1c640c421400510900907901f000c2c904140705000514203040c12101ca410305000d1840391070900404802070316614581c10703c034103009003d81c03968071400030305481a003130b020700b0050501c0c1e0040b145c62502d64035210000741039601603060f8074401500903100300401e81c00d24030044010301000c3e001d042d5140e02802400115925030004004651103507854603282c0c2044400036003981c0300c035085000190305203601071182c00c9002490168400c1d49203004259000a80303110782000400b10780782007840c2d00004407038121300c2c1c01c980b001c00030100c0c11041140d4107510f4801c002e20130700c003400b004049102d419441940003907140c00500c0711580040c1582d0029980303034101d51070180c03110301c0d050142c0c00101d410400241036202d000d510114440382803020300c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 15921094 1250 15919844 15919861
    0x40602091c03080901061a070201020f030301090e010b030d0c0f030306050d030c1101031109060a090e0c0903070806070906030b01020c0909100c02030f030402011803050a06050103110303070c031101050d140702010c0206 96
    0x88041007e401214408615041568800c1014142c08245c10054994950711482c002024041440b9607030102d40c2401c269050710700740022a0044410750759148101e0f42955030300d15803050104401582016101e59000c1682e50b1042c0074440032521985800c00c0710041403900060341a00084140d061620b0000421084102402240d03c64501110f041d1340d07440305c512007640c00151540042c0c2c2200424002c00150010b40c000502180500b03c04031001196501842650b4820440d0940c6c0000c0b640c22040052500035049410b4070001401a200c05c108200081007054004480786402680326428501c504030840c81000110201e5101440c5441140c6001155500c8080d000a04201c4962139401d1401c0380084c940d0007543d40207081d16a09809402d1001c09001c081c0070a80e50300c500640c02c0d03410307490000209e500c0c260f40500283d91303070b42c5580c030b626441284103c0b40c1c0c3c1c1401010007001c44a0f0707103a0310441c1c0017100d00380c0161700c4e50304140d04000d003150001d104070000c2d54464410300c00d400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 15922344 1250 15921094 15921119
    0x120114090415020c060406090204050c0a0e10090e0406050a110906030c0307020106050307061701050406030b04061d0a03031a090906130303090209010b090f100507030305040602091c0308090106 85
    0x5400050040500102c10750940091041e103d40105600659042c4800c104858010001c001d00843c1d05000a440f0400c407524240b140e00a22404034426142c2c9021031f04100e00d10103429040340c2084190191780f80c0b0580b00d008403c0702c0481d020f0b6a901e04001c006841c40c0328002c0c010408103a640d0810029501196540c0300103440c500c41201c0200000308081e00c00d40000001c0c1c035018042e1a83c0c240d58a1028240985100d03021117941071401c00030405040911840702100d400520054003038507540c449200401c0e40205140b5021919468000c09800070403c0c8103416200c0c2d500014000d1443c4401d42062440480c2240319604100512180000000344990032102c231051080d0144100d1609038000c000d2180025005407440c800003034803100e40b20103001607034400d032041d00e001c000030f8003001070758058a020440818014880100403a1080d8400c0e9401441800700528081c4940b0014409500e5020441025500144200105a4841030258010244178000e105190801c02600500d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 15923594 1250 15922344 15922351
    0x606030b010e0409140304060203040e0705130302060702030124090b090708061203071703010806090106080d031d16030201110102070f02010e04150806010f1202060403031b06020a0512011409 84
    0x442d00c884044040c440031000556a800f02c5034106d903504c40e40d442c0043d4598100d4460321019881000008583c1409501190500a454a480f506d01415a400c100c001d0b0003800d030580c0c15650b00e02820301c1c01101d905034044611034104403212100d1800104c3e0302078950301c00711940035064003070900801d2034000300140d8001804607190402100105502d0740340d0700032008054620a40e101c1c01a4101882d0340086040e00c3c0e245041c0c2d036090351005030140c2a00c02c9c911030b8040d00d0f0311909082d82090b01c2540010100d00c00307903060080340800c6403450351910090a004004112694004004640c0c00c80000c100200100e0300941c1044001c9e1603801c02100c01c900080d0502c00c641200b0115a5250b40c01020091803110301c030900d05442d80d0217255220000d0003079014044014070042044100312440d640b00b01d5004101c18545425541c04803080010341a050002d0149500c21070006a40c0340080c000d0340d249945d9042d00c0c2c9481045100111006034002c03103014420613040390300c0741c8404e011140d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 15924844 1250 15923594 15923599
    0x3010b1c0803041718010e091006050c0a02040e15060a03080a0f0c0501050702010606020606040603050303010b07030302090d12091502030a110f0706080109060b0903030301060f02010603080304060f0606030b010e 93
    0x120ba41d11403d10140d8100340003150a031581c000500081ca54283c01000b194503c000c2c0c1e10104809481400e00002c1a800e44090b959500d00c448208040362052000304006e4011000b1ba6a400b659076000c5016984400d11000480e040700900d00c02c1c083e89590305543c8458100c403414140c3e465031b210080740c2d10401042004001907400615138070790044009011482d40940200054541010000d0080c8100c3c000c1000500840d40403c0d4240303072a01a501c02ea98010001d145940d00e04804525130b688000c01c11028141c090120b1050303541c40c0040400d08a02030202c40030700303035400c002c010144040e039000b0800c1907010907680d8200c50350000c00e99244815a0402c42c04880544580c00d15041404042031414402e0f45008503d0300d81c445640350498106920a10025480720f02035492400741111040d0964024001001000d101f42002c420f6910907000000b00d840d140d03214451143c0c4100e80035a4050b40303c020301010b18210344113003c001c041b1445d08102ca2060000004d00c3c00e503002c1c1c0b810780b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 15926094 1250 15924844 15924847
    0x20304120e01050a0e01021524041b0c1506060216050604030b010306150305030409020c0f15060d140601060305070f020705150706020c1506030f0616080405030c06010b0903010b1c08 80
    0x3903499000700600c02e041030030382d0b523010503c1c9410907520300d034503003031071100c10303100615500802d01401c2601580003800c21030031100c0b0541c5000305003204c0711046110306441d1070010444140b000300d02031040401402c0030b0b0780542024820900000211001036006501600003004204046188081d82905580e400f140100705081c1151240101c000c032170f00301918a010024000805c0d003416801882c00355100b405913030002e0341e100c8041d82c94402d1084040741032210880068143e02d082513a070140c9912806048a04818841c003032440c06400760002008a40d44805100c506608440d000000800078402800c019080c040418100d19410268031800c1801041010400101e50150f5030520410011508501000c0e02c0c180c80501c002e4030310500a024518000f8558540820890b21443c90031204075000104007100303c44258009000380d5044c0030900440c540c0d50000c0c000c50340280b00444015071030f42841c0e4101821a00d00401c0715100b4035140403112007056a03006420f04d5550401b150f207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 15927344 1250 15926094 15926117
    0xf11010302190302090a12110108040302030c030307090303090510120e100e01020a080c040b160618030c0311190609080c07030b09010f0b0105090d02040b060c01020304120e01050a 79
    0x1a406402403150307000d5240603121046181541c1070313024006091045070b2501c1403a41e0390400c0c8000c03803548000540071410303215584400d540283d1005800c01c0c402d10481e490b203c401c0c54a54116041914090300280001d4410004d050b808050600030f00390846542c032000f424144040c0c02114100c8a180405e5120b400d102140ca1041c403245220070290710301440840100041c5500035401961010045038007400459030303a100c1c20082d5070544200b08281032030201b04264905c0c00b0150304d4021120a520707850071000c52103440144104451090700c0e00c030040da005240203031010080c19070104441e4002095440d18007180b2811800709a00004002032016650904e40964803600d000c685d1944502c5100004115078100d00310f00c118210002000221200e41c0b000e81039881704044c80780010340502500280d8a001640713285403074401030000904c030715107101055080d0800000302d1001d960110802090000203d1400f40c402001d20342070a4420500740060150b024282c00c10b0204589903842 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 15928594 1250 15927344 15927347
    0x30f061012061e0918080306060f1204060f02030714070503040801060807090c05070206070605090a060c03020901020f010501050a0b03070207050301020d0207020415050603130206070803040b0105100c0f1101 91
    0x90751408841a0418803649403941261030010b001a0385000300344002900002d403800b4a0f20a45a042c1140244241c040d00d090310356a09903007000d850507034000c204011500c3e03400043c0300208846444034100c1407041c501401c2c20011620040010f4005030300400c1004001c0e82c0c1300c41400b000c0a0321450359500e8180a041135403440c095900300456543c0b8240c4040b40702c810003c1c034141122500701c07007800f61041c840f00864290041420081d000384c0184210740000710580c005551001000c421200d1100040e00c0e03a07000e54011054900101c1d90000ba40c84195034180140285000b901000344995450301001c54402c4e03a0500c900ca090b1400840410a25882801142e00a0038020002e544424406012000031751001750103d106070300e40006406072840d68503030002100c81c0104194110350f114130442058808850003240d214100f041554002803215000c0e6014038002d0900322455810041480181c0064039606014050060f0100d4001a00c903000c000e031039035010b80d548440303100c1e5500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 15929844 1250 15928594 15928607
    0x6090103020f16030207030b09010e03030106030b13090309170721030c050706020610060e03060402190e0c041a0304081804090203030a0c03031508030d020f090607050106051005030f0610 82
    0x182040e40e1024144052560001b0311800780c03805198041001c1e11449001400c941c51a40e140c60030781c1003400108883c1d03029501c21000c43c8006002292003012080000003210404d1008030045420b81a0920140045544098130800d0982c018584070b82081000250010300d648000b81c4070010503030074000c05200c2d40340040c540d5480001c03500ea8079120300c0080d44500086604920385858094002a494130400041c5401d11024000d0091925241c00740b0181c03086c2e401c00c0915400c0200c000180415442c02d2040c41608042a8540ca4a0800c0c0b0040340e40400c081525040c070b18107000340b10100300030008440280203040d03d548251899240803c000c4e0031402c401031340c103020102d44604c1003600702e180707050350502c41e5030200702440c40c401c506242c000140c050000d07203500501001c0d45803101a802002a154428500c0c0c1c03e0044200c009159a4440401180c450351141d00401503030604003078210b0000d41d68144a41140b4101c03188608828006065600c600011762210150602542 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 15931094 1250 15929844 15929857
    0xc03060a05030d0903020103050c0a08130302120d020304020a0b030910090c0902070303020903010b10020703150b10020f060f07050f03070905060d0c110a03140c0f01061403060a090206090103020f 86
    0xb01900d198070f03078112028192110700d03c4142c2c04030703040400041250202d0000c07030b61520002d4548103155150150000484111550102d0561084032000c2c0d84000034507004d8585d44401d180c0241c1e813807400780b0602041010b154011681110140188004d488000c1600c9070b045581a100050941c0b081c1000c842001e9543d10610185200050440c00c3c142d050f001090442c10540081c00001c1c00103040c024540300f0141490b0060300150380500020b14156414100c5100555000c03440702004400642c0c1050300e070364002e0150b403084440740c544103001d0040a40c000d00d400d40070191442c08500250207032261070503940c1d1007030340000041c441d81c0c01400d101d0b000d401b0162100d03454458201c0d045008140c0104604085502e624040850081c00110038028650650b03170740d01203009031110b40c01243c00202905c00c450180c04410b001c0c10909125070801026540250b0b07a004220301c080c1410504080c2240d00543c4c1002c48440c05616140101c030307070f0f40e0307003c0c6001a82c4140e032219801183c011030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 15932344 1250 15931094 15931099
    0x3041802040302100e01030e0601030209072706020a030908070605030402060c01090609060218090c1b0a1203050103031205070903020108100b0c0a05060c0705070e060d0f050723090c03060a05 84
    0x10103005113815072000341d1a4000500380c0341085a412404003d60b0b450ba42407000950007015080002c400c584611004c0e10044628600c001c8401c269a40c0040342c0d001c0ca40105005a1101c0e10310b00505034002c0c5510001c10544018141e00d0f810244003c080b440000c0c0040e004a20004405905000940c0540c80594021072304202000c1c562404a029500401403140031001440d0443c015140500e109070240f001f0080103441c0004085155142e04020b03040066240240300d0ba040200c0c00303026801c04c9019a950b4000b9256040d464058000c1010445107480c107850902002043d941040142c003e4030340900b8400040d59505081a00c040d00307035040320007100000b248400802c0c000250686c8200d100e82c0664505a80c1c14058031000d018006015150781c2c444c1c0c3c4100030180e013910603d5000000030745808400b580a032a400918a5045011030301d690044400308140e00c1035600c0841c089a41c4e844008240308080d0004007142c2000d012405240c0d40000425669038400440c0c40050401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 15933594 1250 15932344 15932359
    0xf020d140c03010e160509060f06030108030d0f06080303070809030c0d0302040e0601020a020918010605090c0c0c0901080a031404030606030506070201060b04120f020409050102181203070503041802040302 90
    0x800c00580d441c0c0500c24045806503090400860302c200001c107290401003001400c1803401842c3c074003000a000005082250401e090307020404640d100c13440194041c0103c007004541e00c0c84082107000c00c49040c2c07080307840d50030301e420800d000070781c030210807640c11a01d2880c005d0007503126118541d007544191062841d541c4545521059015010b401030011150342e0f202c149016a070315001640c580311404c070300942c002075040000d090b8020100701030a4560242c0d00018025440b180451603200c4d058608116a010100301030003441402c0029404084082d181b40c211549040c006940d20354843c00000c4c1803041e546c00d110450090f40040d40c0007950000800e008059607401c00a840e50404d44d680c00041d400c21001040c0380308100d003164219034070700b540000b000540c0c5d216402640c80000089a1280e222100000424002d0024000900d62911038049041d820810000342c82080c1c0450852900300780585004a08044151012a482c0300900b101c038840110300e1000030710460b04020340c070560b03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 15934844 1250 15933594 15933623
    0xc07110315011d010803040608040f050f190b09012702010c050601030803190501030206041203030b0a03081305011701062f0105060109090b090604020901030603050109080a02060c07050a0f020d 85
    0x10050f5280c8685801240d503c0903601c07000015285d128600609020038801e101150028019646440080303001e1b600760381820a038140c005060014201001843c0d1040008040030b0004042110fa00102d2031002006000c0250300314110031440400c84040c40c980c040991800c3d640a640030042c0e203036018007603a50320b68680c503011086e07810a445003680c02c41024100c0c22290f07007a00c2507905076900200802e0405280071048001170400610440030140c4441c15810141c131340c80f803500042c601c5003480549500510201034000d5900d07a0104c2e04210140094801c0004090141410f44c0c03007d28045150107801c00084140c5154218821054030046401c00006401984801d000307000980c0c2d447c19150391207103a103040d546a1780e643c03075022009a020410902c2e050f4000c01d04100c0c103040120700c56540b1788a00e400c50300d041b5416201000005622201c1a0f0f041c80302c15403003011150b031542080c1850b00c50503501c1d01199801401c038603410032600155941c00811182d51a84111820813040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 15936094 1250 15934844 15934859
    0x31b1201050924010308030105040c051207020a060c0e06090409030306080307030c020307050904031205070311040b03160302040305061b0910180603050712050a020702060f041403060c0711031501 86
    0x214030600742483d2010341d1202007800d1000c410038100c4c1d0300f0410460540c0d08003801c0000038807030161164180305042020700f040d11450100e85d8840c4165801800042c6040e00700700080c1e80d401440441001b1601c0e40c3c3c11120343e2040c0945000a070259400901240700e03280c2034000f045140c020b07e58512010417403404040d807040174101410b2003030f4180c2d009145c0d500700f0f1050b85002550000d0104549503110301d8440416880b89502184900c0e000c100d8141a50b035034201c2c4e0f401900040e8041d407002040040f601003806024101503120b1038114641455900c80c0ca031611405084440c0c5100b14600c540c1400c4541e03030a0311803011000340845422400e801000d851511440844c1d81d2105102d0000607119000e07100d124468281c9803a10703c41d880856440c3d00007044010014241c0343c0d42400000301680704c1070058a031280204001a9072103040075160913200754404001c610a40c050b0f403c018001070200156a41076520003018008120100700007820640000342c0403003144000d000021707043c0d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 15937344 1250 15936094 15936103
    0x109021801090c05070b040212161d06090c091302070c0b03010501030b0f01020c12030706020a02030301061e050423040f06051305160807020f070e010501110c031b12010509 76
    0x300d4a1100030041104500010351340c50082c03200c05840d40c0d90b41e10000b00542041511043e5079110082500d60800440300c044d0340740324003038001113030919000303040e00c00c10500060066041841102e44004511b0481000e0070a0b10400c0d90b86400748840404000e441129a01600c0341d00f948280d2802051f52100e8102c0c00d2900244aa1800641412000710807410075440440340404103034003524020b2403440c180040d048040300851303102e2200300000c2c004a600341c40a0506c5103a168040c540d25450200000d080024180310365100c4060b5404555a0f1a08041110112454442c010128401e500c0400140c83d0654100c035400505000e06500c0d00551070f071201003500e204403945c041d529003064004c0121142101d0028540b84403e5160b0082806181540d921520503c1101c621120551340343d03003481142e40c8150300c0103019000522032917030000754102a0352090801815001c1c114000240d44800c0035014820305040185010302d41e8680e8011a00e40d112240b009100a040020303071907658 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 15938594 1250 15937344 15937349
    0x5010209040506010c02090a0510050405090a02030f0d1205060103020903030c060103050706050c06010b030604021603030e060a0203161103090d08040f080f07030312150b070311010b130e0109021801 87
    0x1280b0b00000151150700600d01400c8032600680554202da64a091480c01404c01400c401c0c1d801c491280009219500c2e8001c803840b0b000c60304050300803a411441418603220f840070b41e4413a41c1c0c00815201c00d540384d0002815502031342191011420707484d41e00c0182c009215120074582c060000003070444d03070100005451030490307208004807003205658040459841c020300b01c500d207160300000010001c031900d101c051604031100a0005140000f5800c1026900f0300200048000c29100d00c142101e4000520440d6440a20010294594a0b12038481080340d035041a400051040145008522420410607603140c1040a046c10859100a003802c1c030b0701e908a80303c0ca40c0818030302c41740498120300c081010541502008000c10aa82c110b0f981a22400a04406200c1a60341c6145400180d03041030000c80007003103e24103840d034480b250b0500401d046010420a449681800380a001603290001284101500500000388001122400601400840b20301039808908a24141691180c0d007118504 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 15939844 1250 15938594 15938599
    0x604091b090803040b0705010b180f01050907050d0c09030c08030408011803021207031e0e0301050a05061e0d0c140a06020a020d030c08090907080a0b090408030417040801050405010209 81
    0x200152a8804840107115070107248280e4100b808108003420703060000e4210703a03100d200045403072081040820007800d00c01907000b002115840c10312000e10501040c6c1c81c05440c083d00c0c4000140340c0580090901c0c40b0310102050707003d03a2a010505d4103407281418070061030703012118000003079580e10170942e290410300403c021540b90500d00070702d40303074070741e500752101030b4150040c05100320000400c843c1034101c01d03015818002800c01c200074803d17410b04607100f06400da846038941d80000c20285404c4a100910203105d0f2444e1a013807002c0345e50707980503c0340d100b1525002a405400c0741d001165032243c010034000c0880d110303200040b50a004200640f00032403016240c03c5070081e030381c5400f02e0303071303030b00c0941001c0d401800000803075000c43d01c651100a40140505c10191400450101013000c00d101120000001480c94003403240d0842d6a0280403d86042180c0c3d0080f01e0400e9240d007189407002a000074840002d20010b203013020036100a480c020301c1140d000b00001e1400c0d041850103980b1802c81c052 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 15941094 1250 15939844 15939881
    0xe130b100203040815060907030b030a0501020c060f0106080411040c0c060e010c110307030e0603060a030b0a050a05090c0a0b091801030309080607030e06040303090201021609090c0b040518100302060409 89
    0x90310417180d00224070504000380781000c96200e0750b405a000780310503540b02e03405015044c2c024001c248240002c00c0c81c044034100074100ca00c0c1607203040c960310368103800503410402807100f0703c03000c80c1410500c4881803034116800142010192000d0720036400d01d0400808281c100380d406c0d00381a0065221000c50300e4a515149221440301102545038801c03400001d022070031319a00c40140c1c0c11700001850b40140c2c00740c40022a1078903900c4040c544002192030301d4040b0740b02d504004250010380101030700071840c0401450700c1d9002c0000106a080207004141d8031540100f103800541c0d4400d1101a04900554010201540c42e0704004008022501034441c15100d440b0101d0754461082c41103860412104018151a0312555402c901030912081c0c10380c1144214a42e60068999100849004103102d41c00020b655403149080e0070884403e90004420910601042040c3c0e1035056948201d401604480c2409990346000c085000b850f41d00301a4105c6d0f0b001c20080750240d03081d8030445001c01e040343d500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 15942344 1250 15941094 15941113
    0x10050108010912030e0c090c0903010608070503030a0c06090209011811030f01031b0e0907030c08030a0801120807080a0c110405090c0d1401091217070e130b1002030408 74
    0x300e082e504012001042040300b4800e04100c00e100740e1184c400d0074845001d0300c441c800d41c0300001d0011780094a50020710301c0f0008800145280c01d105000c001d04ca450041c10600e1314140003e40c983c0502c020200c140b1034a5080c1c1e0003003203a503502c490421750b8000c21a010550711201100804044c02d500d81105500d000080b202d4444c0c5401501d10035001c1d2848103400c1e0b0308503603401d9901c0324003680500e180b0091b141c0100720007840980c500e1240030440001c00d034003451805e02079035090540d88031180f035030000c2010b0300c5015800f18440d4155502141030003c402003a1a18800301c0c410540f000d0100ca401040030704c840c1b50b00c010642685801000455001040d44082204480f0203a520700030b241c1c41090046002d050103e140700d0035034002c881c0441160165200c4030b080d0f461610b400c461100b06c4244851880c2d401c21481c00309400c005100d03002625200c407000d040030628001003072003444110030100f0071035800e03040b0100001000d801d02c004400700380000703540c9411134003a0303081d40d0240e294003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 15943594 1250 15942344 15942359
    0xd060506091806131a01030b0601180b040b07020102100609020a110c0f130603050601030c0602010c0f0203030c130302030a11090a0b030a020d1a0903040e150d03030c0302090a08100501 81
    0x101c80101c1502c0c0060300f0b06440d480c991209121184004444401c4c41081c0d480307119040b441c0040c0254021807040c0f0403440c004000603c1c02000e0707160508012100c6006001c260290702c00d039000d903801c80000658075170305d900040c0d00d01312034003280ba600141440800f00c2c01c0401034019061a0b1150303101d050401858103070750360700c960b10b600e403a941003500018203010514118181c444280b411700d400154141c3c59484190920030300340c209450703410510000b00305141c0e091040d10a88a114502413400c21000c0000a4803444040e0100185150110b650900c03215520f100100039035004040f0b40d07800c012843d0140100c1a81c00d80c0130b10540c084400289404618040c842c4461801409170144444c3c5a080104000804209513031150303580b00c1c90000500208411401110280c00443d11649031190384031076042e00038507a0f072501155031105079251f1100807003844004e07858140800d0305d503240c9400307e000303004400c40c203075000c40406000140300801280d0690740c5d582c401c806101c182c1c0c03074800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 15944844 1250 15943594 15943621
    0x30408010c1b020d11040f0c0905150a080414030f0a03090218070c02010302030c040504050f15010309020a0302060c100c0c050c0a050f12010906050403050325020318030c0d06050609 80
    0xb0065005041a16010000f9643e03540c0d06000040062000440c108507104000448035900e0081d000b00d44800b005015500d400700b4120072003507111040c1da00c2d090705120010714102e000781c00181200103284c0c405c0b0700719070309009803001c20242000158540307000d250000c0143c171008000782d02440840c0e04442c003810b4148246440f94007581c450f201c10310802d500460003544002c0007140340103810320002c112603645001d100d00480e510745a004150810200007041c9400c20070030f1382e060510301010360f801070b254070742c411040b6034040320b029484818001101e42006030321904d40803c01d02c1d0141502c00c581d000400d604855000310115110001c0318010b000c01c0000c68010694003074006004020245820000e1076181c2120310004a503a0070142d680c2400d80320140c5d81140400c9011081003048074a06021241000c1c030f400603c003c40700c859801031348900ca41440340c02441c440c80008440340d01c041002c0040c4510140c451071900d00542080380041c40143e4095200d40001c03c00324a2a105542 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 15946094 1250 15944844 15944897
    0xe161e0b031501020a02030d02010c081f0504090807050a032708070504020702030a06050a1409011b1b0503040801090b0105010815040507091e0f080a050304090506010908030408010c 80
    0x809403564490240800802c800007030528118031030a610040162070a12800c91010301540000c11006248400508440c00c01010f0012103007005a111609820084610b41101c005450000311284a414036010311310520784041d1503449210084410541c1c03140c407640700c001d05901e46800f90b080040c0400c0400d041442002240d6104000c24466860294010100907100a0445004e440a955444151601140c04c40b03449035440030708143c2d04000d054510390040f411070082000d0001e65281d2603801c418242d401c01000207105500303041050b049101135030660030404681c2ca031a40c40c22464003070f149102d0101d48031820f0200004055005c2c200b100d009508595010001152220511004180c001d203d4410001961800a0034403c601c60510301c0248074201e4441c182e003480c005004000c42a800304c11142c0c00840c011011501c08810398054442081001c0b47c241c945c1c1d80100d446112540001c2018040060000303800d4005610000e0141803540350403c074107000031840c2541ca103912 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 15947344 1250 15946094 15946109
    0x30d08010b131701020c0c09011215180602130e04020901060804030905040606050a0e0a06050f0d0e030f0a0311190f09080f0709060b07050c12010e161e 67
    0x8800601c011000d8001900c21090700d401d14035501c035501c8250360b080c5400f03031521600303d0b580041c181103142c03002d02610180040c25564400b0035454600e0104030045540b40290040c8000c0c0d910714160b034440d802001c16402142e03500c285980c46810280020b601c10190131002c1d074011900003a490380c040c44c0552003075400074081c143c240c0c42d00805a07110b9000034011410402204404507603950390784904006858a5032310719484420240c005003007440c0881e901c07482200d103080c00708001c2ea8071004440580d800396a4041c1c44140c0002110050003588020103907900010a44806000d0100d000c1e262101c590307a400d200d1030790400164900340c0304200e40c1c02c02c1e4030311002c0c110100c64003c0701518005485407521100b0740c1c0d51840d1042c2070900c60251131203543c0100b00e04000080c8503010f0917000d8032511300520324000103a0313201903948007051403203030240900e440300d10210b820079031140b00780010b003100750703001029100d0080000032500d000d40141e08500c100e0740903104081300312000640b8001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 15948594 1250 15947344 15947357
    0x51e040c0b0d141012020607080c0712061d0c040f020702090106030506190612020c0c031c030b01050c030901030e07210312050f060111070506130602121608030604020d05091b030d 79
    0x217a4007440b1031944105070a0320114810080a4a008030400c4000001d00c100248a240c06d00e803032400c40d0035190030f560303207a164000310032140c0405103001c00e0f244441881110001290400c441031000a400342020296020303000e1000000c0c05a00740c2c00140c4582c5088440d500b00d2442e0400d44107481465019580005103060401019600b00d5401004a0400c020440d0408002440028500004021312040c00148546550907450305030045000030102405d006060804541c1070070340d28050300e01010b04143d203e020440d40c4031000d01851026103200100703c1c840c580b4a050500d42008078240c110005406003000c15100000362007a00d01407582d4035141d030b16030b4884d81d00446070400007014040703060003440400251580c984d4010034102c4241b108911500e03180c00750290a00c3c5d00041051900034041014100000d4180801444542d026030b60070703103a48a003400708000323020710058984402c0c90300342802641000002c014035142c2001012003268505c610605486212911000001c50718 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 15949844 1250 15948594 15948629
    0x705010807050a08040f0209040609020a05030106030302030d150e130506010509040b0402040b010210020a180806060a09050a180305121005030d050304020d08030f0108060604051e040c0b0d1410 85
    0x4074407130680d08280180014211010150001440c016083d541192080c2e0b868420300e00314100401010010034040300200701c05480d540300607480b407045d02080d464082c1d03202000c05841c2c80c2d81c2d40c0300f00903001402c26281c681c40c00800d204a0190500400c2d1828840e20307000240d40e10380484807600c20b81e849002c1310181d031515400d00014100075440c0d0b5056004403111384681240c14800380044101c503940d0340c5d6122043d1b80b840c425203101600400701c00c1d0001810071141f42c47c0d803110001110195000081d46958211010f4000d100500410300c03440120500c2006155010000e001a65070072440c101c0580c4640d14082d0000744103220742034040d00a1140c1a40b418040c4001d036074800c1c00030b0a40c0c400b0100955031107050740c1c070480d80600d4218640d8014400d2041c100310003580000241c03000c200c03505140580c004e250000c100301c800da822072000041e08000d54030819200920840b128079840e2001000448040d0038a8a01c1c000b050911400107440360440303410744002c50720040b080c0141c021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 15951094 1250 15949844 15949847
    0x10605010c11010306091503021905030a0803070905091e060907020c060901030b090405030301061407030203090d020d0203010903030507030e03040506040e0402060f07050106060f020a05070519080f0f0705010807050a 95
    0xa0490000c41c141580c4174000a1110054041c00d40100c606882c040c1c11541944100000f40e03c02c5e90201c4144c080d6a8400d005a4600190301c0e01443e030002c0080752240d0b80c03030707030304440c110340540105400003c00b5061020303200030320080d41c0d500001421078034001d5940c0c80610416240031120b400040e4401c80e10007046003042401840d800f6018500031426480c400c02251020206480845031540b00000401040e9404281480c00904a61059140020340d440085d62405041280b51003001c12424517000c42d61403040c07036610140d0260003442800011b050240c0201022140040420300307208201e01c0c035002c04404c88040d640c0c000c160508003410104203008401d4024412a00510b0801c622914180036a01402d0414070500c00480d90f10305000c0010a07400a00709440e041d58070900e0383c0c1e0b00141011480300c003901c0040e22040e8010b0008502000111010f510003007982c0108151000c000c5008114620410048003c61380c0a070b03039801c01101e880c80100d1b8610700090080c1304155046 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 15952344 1250 15951094 15951113
    0x1020706050a050c030403150b030303010308040b030a060e0901050403080606040501020601210f0b040611120f070e100801080d080403050313030507060507020d030e010507121107170318010605010c 87
    0x542d60703482e041c1d003001110075010b8a180e2041e0420b540c0b444c9020b2071a0071854550281b2350f9128070940c055402e40d45141c1e80c403040343c000c501442c604000b02200003000345140341c0c00300000b0300503d1302000070b5041041640e4006c043c01d0310194006090750000500783d08003041100c0803200182d00501c141d80c03824511400300d0301c0c407a02d6240d0008201d440701021a10032498944118002e4520f1030807400c6ca468510102d85000200c5000800e0a020200c9070f510400c83c6c10b5889110342070740c06a0340d91030707540403150b90710a01441540004e0001e00c440c00c0d29400098036068484500c21a4503451801d413003928440404c9600a0000d203040001581c405095181c001c4e800d40301e802c04606201e0103564101c10384404603110801603001030b455503901da601d4011080c11681c1d80c4020403443c00c000750000d12542600c1c0a01c000a9120003080c03400480d03600840e0355003034220004110f504510078408240303910a80b0000150800703e05214210701041c8141d0044903016101c0c4034000c2011794948056 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 15953594 1250 15952344 15952357
    0x310060b0d020315030a0302030409050a05010510030b0301090b0a0f231303020a0203030d050702060709030213180203010c050406080709051806010203070b010f052803030c051e010911040b0102070605 88
    0x40c400491141030704d600e00b00700d9100c689100f5005151100d003800700400480300c0040c030a00383e00f41030000422a0340c55841000a40040354a00882e0350f4004034046030260065482c002d1041380160108040030302d050b4441916107034080070a211400b41039009958400480042141c04201c200110700140072001030030411768070034016100c09441c1500044e046030403c241e406443d589a00401c00c1055051160300c2d40600703207003000800c10341182c0110340f01e130314150301d0301004a50303410054000150910404a007168020024415440c10381c1005140360040e02c00d101c04504a41c010038001d0b1b0040c00325100791103000c1c100c190425000007000b0000003010781818107600041040101056280d404540039003070303085081030128034100c14030282e01c82c410480c64001010700c80d002c10b540c0301e1604170800c4a415242418204035581013841c03d084d40d1300a019a200d040c0300340c1c00341c8031006412104034207002c0e110414100c40b03c0b80a02060701c8084070424010781080c9010703c9117501600180c0403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 15954844 1250 15953594 15953611
    0x5031e09100e030403031e020703060c030e07030606030c05150f031302040903080f0c0c0c040c05090a0f05011209020f0118080109030e09010602150a0f090807110310060b0d0203 78
    0x1c51403452402802203070340c0c000032000d03503800014060041c150000c10740b203800701c080c4d0501d5080c80342601000351a1406800000c2049840300d01050b0401e1281d04094920365041c0c0a46180c4c503038070f01e0003c004005c0f40c44116603101d400301e400109840c02d00d01410500d1000c14041d840e100540200c00e00e19800102001b0404e8800c141da8000358030342d84201010b051090704c580c0c007541006a600421490000d10405840004110b4404c003003401140060040d00141c2e004141100e078002c1c2650b00f80100012103402c00c0d03070700000090403200072190302e048510030b03213071403114400d0152079409503010800e01130f400c43c10f601050303809544a415034094482c420404900300c90303100c0350f105095030007282c2c0540c0044c0c801807038001c072840c01d040214014265800100070781501c0315000b8800c070034000d0407405025941c07036042e100021142c020340300d42c40d4085841951451a4a0a100703203142194001c1c0c024070814002c03403848a10b51003401e080c0c030055031500e03003003500040b00040650b100910541 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 15956094 1250 15954844 15954853
    0x604090f142403030f120402130516030605010f0905010e010909020a03060e060a0302030d05160b0f041103070605030109090804080304060203030f0a0606140c1609060503010c05031e09 81
    0xc21051601112a01410301140d119001c2610840421031000301e0031240b52294004001d00080c0b4280c0000320f5403106020140e01b07415640e0341c0005003100a481d13000f0710505083c0b004000b803542c140400ca0020803d81d84040003c5900d42c1c0c01121800c20308010300f00812125503042c0701d10760082c80d00100c40c07801454a0040c040e201e01148060b038129040c208007190304c0361014021920301c2e40e0b4407075228200340c901c8102c0c586583c000942c0d501101203094141300c4001a40c0048070006684c1c0f81d84280c0000c5200c0701c5045c040041f0004143c1164181e0b0b0003500160b00744818503000c21800115405991081e086900b4440b91100401c0045011598041e08000020340c42d101840608010020307900599101e10309240003c1009400409640c00c103407400300103000c03442d00702c4100c801490f80007030201d2300c40d402c98103514a810b0501b40744100ba096840710001d080c010380e03080f442c01e66909500900451800c242c05865902040d01c810f00760400325103243d01003a001401c41640282803c0c2202c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 15957344 1250 15956094 15956111
    0x12060402130902031009020c151803030103030207050a080105040510020901030212090607030605090103080d0c09090513060606140301031424010e01050d0f140c121005090106050604090f 82
    0xc1071009081c1d485154410b4000c420000300750302e0b0500c044d000f050300c5282075240c2000038101607202c101550541d08103180c140701041403c0031503403400c60400d48007012265a56180e0a010350340c1c804038801e45105204c480b80100c4c4001d0113000d49805030351321000601d0821701c045403100c080e4000358210b904150b42844a0b4100490301ca0520f401845c88601425007801c004c035005042d04d050340c02550045440348010000582c503030040b1400003035001000240c4000c000300845042883c0c2c0c2c4094051814881844024000d0260500c840da204140810400390f2340c0d10140c0b140c000030080f05518550034001000401c030030364000c982c41c0305a4410b0b96444082901c0d0066a48040070240320121804001800800070b07003410f8038003400d400c5459103410035050317a80716007040814800620540c8000c0c6601c649010400484983e800003e0040900f01190f00341c40355110010ba403800c000c0c908240204503070500c10720030882510f901510b25840c00d41018080c002034841c00307055015180d03844081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 15958594 1250 15957344 15957367
    0x140f07121e02300105070e01050403080306040b040903030506010815010903020906030a060204080304080714100c05100f0e010f060b070807030203040b04090c02061501091202030a060203040821010302010512060402 94
    0x20b0500303c51044850652400a03401c0d0751308641c0001c095100b0300010800000c206e0781c002c4241c1d800c0301d0b80a001c0b80e96a03030b0b5078408500988110100550400c0c00c00401404068240e0400345c40b0b04800c2ea6a42c0c441d541d1058450b800c5c601d0320304c11901007100c400c024009410401400303580140042c0844807164501d5a07110100d0748198001a131682020400f40806041849460002c0004180042c0f0703449150b0300244c078800c1c404141505203c00e4007070711010031405101104801e180b04c101088100c142d074004d08003038074862003030300c007154681450050307a10340610418054425034540103080c00400d036a0407402c3d6002c590b0550a5103c01d000c001030180701400240b000e40440c41b4041000c81c0c1d41c0002903d441809032880b451084207010100407a44e0060550044501000c2d400c09064079600102e410005100300140217030340008100403c4c80802802008150154210403944d1031500700f000588a100f80002070015000300001114101e00e05007698000d0343c014401458503404156 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 15959844 1250 15958594 15958639
    0x9060f01020a0519030212040b0d020706090506070201050a1d0309060c150112060c031802150c01140f0c03040f02090a0b090f10080a0c0902030c0403140f07121e02 72
    0x2d4513000c80d44401c070000c00300742c2e062105510005000c040242898100302c103e00711805294100d810245d40443c4020038000340b80c000740310142e0404240c480a00700406c0090107484115031400d00765043c018803801c440c112018140c004c01c0403801460402038504104100c56001080c100070764420b58403c0c014211200a04034001c1440c41c50041740c1006c01e19111b8184c3c0e074021424800c0c1490601e40741b501c0d12040ea41e441d00c0340d6044416100c41284a400f1a03480e000307a80103003040d50719040306442e03a5400d00080501900003001004402d40d1201009184d5120841c0c0003006050040241c3c0014100001c10a4028280c0603000c9440c1d03400030003241540700d0803280340c00380c110810240403410910780341d05805881c01a001e09040625a1100c4030140064401c071030155a00100003100440341000b0380c0d02a41c4c0c803002c2c4801c148002c19007280d0b62501c0e01c0c2c1c0704401c1c0c001c00c94005088601102d0b06856180d00c40b01003070300343c6d1707440c6500512181e4091050f600030094244000c0200507101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 15961094 1250 15959844 15959863
    0x608160903020913030e01030506181f06030b030c0301050402061210051005030609060108090a02010810050301050c13050307050109090e010902061c050606070201022107080a12150509060f01020a05 87
    0x80c0b4072108806045c0205808188001c19040c1403500042c0142034441c50b04030070821440704010406521075508461200340c120700c4408200b00b50300c3c8049501070707268000e0fa2803190220300b110020321510080500b00c40c2c059078002e5004000b00950a4064840c40c40345500039000c04064800343c0e69407002c2054010505022800100c0000c1004002c0c90a19480c3c3e400c04c0c1c081c42c3c21040e9140003841c0035032310b03048007a019040c000b104000900400c0c1000365030019017001f400030711450820250b00811904403408d6004484030610300442d40e810001152801c03584141c0d21300c215245490b1080e0f004140744600707507016540702c2c20404e001d600d82c803008029480c855114000d20041c0316460604a540203800310f0312600c010000b060160303a0000d566800d031a041e1510010b10700b480411520a4402e6540003090410041003031090241c000941003801640041305101d403180c42d84c2e9810b0590054041d00758895070b0880451100d003041100d80e140d402d03040c01101e8011060382c507403034130309512030303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 15962344 1250 15961094 15961111
    0x110d03030504020420030703020c030c160302030f010c05040b070f0b041103070807050d020111070807060804031707090b0906091507020a06080c070204050705160501060608090706081609030209 85
    0x84080c8011030905120381c1c2d18003010360b1401c45c1202040b0404082d584000340502040640100e90302401a038140f0885844410000848504e95103c03001c8010b04400ea1006a21a02600710105800441809101100401a52440c0ca003a09121000c10107030004a8156842075403180700c480090400e2406a006138020803081c0c080c40c141e2010103113030100e1500044d07801d421100c0f007001140c80d0010f4030540187d090900010748008485064580baa056001e61014401c03076000140c003541080c10b460095001e50b80d0742100010010401c0b684c02426036020700003402c00c0d1810403411003500007501c0c4d034200c01000240303810840c800140f408142c4d031442d562401070008082045140024029000300814182103001703141c00900e0320aa0300030400c002e4080c5445a001503546d0b80b0420481d09554008a134000321456a81007080c000c1000d8041c84020804820200c0c0c426400007892408030340c00340e03903144446c0e40d40d03104840710713031003045945820320040c903c01000507903601881ca44140d910 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 15963594 1250 15962344 15962351
    0x6070309050c01030e060604110c0d0c02040c0314130303060f06110709050f010308030c070f030806030c01050408070b0c0f010c2303060901050609030c040204060c0203060a1103060904110d0303 85
    0x1581495402c2030b02490400d41403610380b1a00c2001040081542c030390000044800068040310800c40f0390b010312509058510728004d1004040c2000d81002ca00c102030b600950b01013280c88175100d801d40440e05100126400041103c001446884081281540c428460301e4003003181c541d2040510356072195038015a0200b480281e0382c40038003c08000410051000240c144528106500e001c0d64202041c0006003034590700200003025084420211144a41d1100019504818070700b13006140c020705882a521034025030035503204941c401d038141c1c1e0550311107a001e004040d1409030700c00c1d0039a001c581940c030140035030202960000001e10812036140c0741d5865480b05041c9960413048188020a030402a12809000b484804c2c1c4642c0c0150f0306641058410030303903070038003d40000e291444a80205601500004020a0f9158480c01300ca07030b03881c070a070112407050300e07195248802c0d105041c080e0542c002c0240001421481c001c108645c029004406025103e44000c000c02c00d0951405002d030040391700d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 15964844 1250 15963594 15963611
    0x207091a1201060e06010c031403010603020304111e0d020a0b0d020301080f07061202031306050411030c010e06030a090201050c010e060f0c07030801030204020a0302040b04091d06010e0621060703 86
    0x10101c0c0c020349140651002000800d051020103000240003a119504010f0000100010940150a210f0015003d111859200e6a4640004000c2d50040f90200e8a056402075900d40f43d0030700c04070541a8101e50004014448030031b5092081c15045036100307a80c0050401000034074114038000420246410200260b680e60410700000c1c80c0800c1c0741a84180741e4441d0030304001d0760b5402868031545000188c3e01590b41d40368440307101c4c0c0320f952083c0c0c0070741164503050038001000000f4105104201003a4161405284202c006464000711502415040002000001c6030703114554081e600a9105041041c24050001e20701401c5800c505007070310466110005106040c0180800113900c0038181c0f005a240c04019540101072500600c0020b0040b83c002c10003050302c0f4004d0f015a0040d000701d201d203a403503d40e42d80520011307041001d10080b000c0b44141c1c0c80d84035200040742940c1a1001d0040c0c480094840f4000d0012400e580c5d6003020180511400159034080c0030f101c0c848c0604003581d0003041464 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 15966094 1250 15964844 15964849
    0x40807060612030807051b011b121104050d08070512070b1003050307030809100f0605090709081f09080304050d08010602010501080d08100506040f030b010506030105150304030207091a 81
    0x4201d40c000c924280c00280901002981c4104241e52001c035910b011921590582c068403014914103040061a5080c90100e590751141590440709100c5660703079034001d801034094100122805102030310380100c801c1106114030304000c04d102401c0c40c0b05070501440d00c000c48e150603040c980c9414076031080d0100059010140904503a240390828000302d00411010310f1995505d50728411050014284400c4100150100c40c05101010540548180c24841d68029007404c5008040c07034001d03140b050a03000b020a580c10b2190b40500e09464002004001007508400c0c131003074125182074036002582e100c04008001420080181d40540c2c13154000300307001240c905000c2c0100e030050308507004583c034100040101c8040001c010b0042240c0c1d0070005041e444100004103080080d0708415002040002c001444d2503603644003a088a0040300c51903c07170b0362240b0400007588820703c03031968040c900071404500c600c2450300443e0480d00c2401100d9000b40d407a10794900344c1d40c2c4840e8480e4813401c0390154000c1c90 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 15967344 1250 15966094 15966101
    0x50a0506190605040b06090409030e060c010c080a02070c060c060609020708090103050603060c0d0e03040e100528050f060c06040c0501020f0c1005030403050409060f050a080d020601090b0607020904080706 90
    0x10030f0201c6050060034982c0380800d201c2d0084101d050b110790b464408a000303060060907003a8107194080d05881d035641002d095a17020b418a45d01300c800090504000074001c044074800d03620b034070760b106010169461a0020031690090120026a0340655401000406456510040c144c0a114a04540d00c5401060002d01142e41c0102142d010390020310030041c59909410482c0c8510712404000141078211604079851070140f50000300c09220030000740100903512a900000b02c500484110318607404111650481c0700e0003400110b0b000d01903103818030441c54522079000c960180a4a100e041a030311101d55441c180058070705407400210050b040c4200d5a043c0415200148890010480c1c0364000c00400c0703000c02120f48060801402001040030503100c2d6044400808011000b401002c1d21228000200c0c4010f100391845403040719030004402c007000ca01c07262200000e030040d0500742e1070440050003034803840c640c56030b01c28400c001200059454002d00e0b030096001c1d102c1a9152013591034075400300c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 15968594 1250 15967344 15967349
    0x302010b09070f090e1b030907080f030f04061b05010f0902130204050607080307030b060307020105091603050d0807020106090c0903140106050d1113111903020301060912050a05061906 81
    0x200000f1400a41401e41c204040d68101c0300f1400c2501007603a500260103110840c184c0010b618508004140005143c0005035041511409000e40d0600d684000c40d0b40c2c1d03640f20382811840568000d000820441e03002d44c1001c000d4103008800a4001c41c5250344050071102c00da031800380d0240e80c0c0c03982c0d401507041101c05440300114500d0218070301428076000407040c0c024040020043d020000c00a0005880f0b6007000e0b480d00c03006003040307480b41403000010340601000c81d4009514401c001c0f00e03003100d1103040800e4040b030381c1000282c219890851000c80f428100104034009540d01c0c3c03500080c20b9400c0b0702c82e02000d045559504d00c041425403810100c124860000701c201030b81428424000d43d540d01c00d0040b902d0b0f40c40003802d400600c811002c0f03640134200204200d440d519214400c50a294040001c0454060003030759800300d42c40300c1800360103c0c0400e0181d4000a50200030500a00d09001c0040c8a82c40c059012280032001303e603100d0b49450300132110f00e40c21200c11310f040c1090382001d0056501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 15969844 1250 15968594 15968597
    0x21091b0303040609050f040f0504050f0c06030f04110f030f0102040e06192105060c09010e0409030906260702030c10090203060402010e0409140f0c0901030209040308040c120302010b0907 82
    0x2c0c207441c0000042c445826400344610501c030207485248241c1d1b82d80e1007104502041201803000340b5080c2059070701c445141903280d1090260406c114120b18180007280d1144070303c0404090175031182d494002c8041803100c070b07444e08864040480711043d07404020311040954454009641c40d400c05032500403106000c4c007000d01403114908901c02568250700d1100c1610a0f51107800000840003219100e4241241d00190280c000c4205100800040d00028400d605003030700c0c1d0103040e05a0380d0900044401d868000340026812050900100e40310306002c9520420300b40741708004049090540c0780d144400c2c0d4000015a0000440d00042c000031f014030003018031000010098803020f500401e80310400100001d04000d8280d20360403042c0d0305c1c0d511131440640c020140d0820765a800d4003640d41c2d640d007001d10409a104042140c1c09518019030514140c0c1c1d8080d0250380191a240c0d000d459904015104545050f442035002c100700071040000154580a0ba00124848507100140503280c43d001e4120700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 15971094 1250 15969844 15969847
    0x213080604020a06030c0c0c0e0106090e1e09030d1a010e0303040b09010c0204020c030a03090311030a020a08030601030b09090705010801060f0f0e0406050402040308030103020405090715030221091b0303 89
    0x50ba80300c400035821103146050114000c60001421140a04e6008004001100c422000b1440709c0045088038103039101a01e9607400c0359200c000c00c4904150443c1d204a0300e07030032000c0e45c42e0b5000d20054080d4005248208507402d142001c0c019809031100d502c00d00d0341e8003060703141c00c482135179005a6500b0103d030280c1c059482c1c00d090216010356031152440c1f00c2e05000f07070540b44104545843c3d044401403100041600d8840200c504001c0107070860100940002e0540320220340700d014040200c42507001c0c3c0750000c00c825415a0b840c40e00c540c0004180750b040c56a40e051080c41d41c3c03104406944161348040140001d6800c040001d0001074060b01305800f040014041d80c4081038002009900203000f5061900040d01c00740b0010b0041e041c40c0d00619000342c00800c0010420151601545c1a613200700c40070f0080e039507040e1300faa5a5140b180304620003107940751038000e1454041c4c1c0c004c001210240340800c11100720030001c50b02c43e00c0291140070080d44144081d03e04025882c034080c0e03503048110082c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 15972344 1250 15971094 15971101
    0x4080c10181d010e160f020a060c0e0312040f030b060d06050403020d030c081308070507030507080d0e040203060109050613050303120405010c090315020f0c060c0a091409040b041e0602130806 84
    0x280c868000005500500408421b03c240301d0b13000b00908000254403800612810010070740051098040700c4841e802440340700d14040340322000905030703000c0c6d6a401402041403440c64030f0300ca41014024003000e81101c40501c090010511764041c272072281e0b00a4004200d41c8000c0300c0014104c90a000e076100c02c00181c031081c80030254001c0b59440107160421185600d038846c0382089410142d046d44000c2c03062042001c00141ea40c404248110b0b00003658841207010030f000e000303000503480101c0c0c1540c0003810300701c3e042c8040d14006015040024401040403180d580360350210349142e00c00c28043c2c11400304c20003013104200c02401600c01b00d069900c0c0403410545140d403204012006120250840c0e900032462194200e13040d0103407a5800300201c00c590b614100355401c1320855200342959800110086804160441c608d50862112103000c0e15100c0700380c4d203d8890310100300b405003046900d1a10000803002c1200d4031980308845501410005980e4031a521141001c2c07101580041c6460b00000b081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 15973594 1250 15972344 15972361
    0xd0503040f060f150f0f050a290c0102040806190213030303020a0302071a040b070206010f03290a05010e07020118060906060e010303050307030b040204080c10181d010e 74
    0x14a100e80750300ca90301141030302d51146440701400130443c90062404401000062151203800280304032104031351900021a210020f00c072040003140590300c9000002c1a0411815902411001007030a544c80f0940c1018003181c88107099034440e501100480d440321051001048810f10400c0010b02c02071400c42c68020a03c000c25802c01e0f0740c0c80003506240d40855640d161500940454072000c0d44500907031150000d01e1405000000c0c00e1b40e05807155000c1c503000030107441c000918207050301e40038000c50f95450310b10313a40e4980e1144c0d1400303008100304000240c4148502104021030141c28400302c00302d034640c18040901c803610740081004003103a04014442d60b91306900400c1e0b012481d001540403401d039080341000e8001c1e14443d40b10b1225400920000014954403401031070213000c0c56601802a00620300800c4285d002d82d009491281e0440300c0380d21418900b844011508111034100500ca0b102d000c030819415a4182d480107040680040100070b114400d00740d03144c05062800c2c40f403c50790070204070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 15974844 1250 15973594 15973613
    0x30902090f0403110304030f060509010b01140703050d020301060309030f020309180c04030f0b0405010513020609040914190605010f0b03160504030f030309060b0d0201080c1612030504050d050304 86
    0x807026003204610104003854031504c0ca03070200c4441d20003200c0c1e82e1580d905c0e00024204c19240141e40c050f2a12022402c000c5040c001c0d000614016910000036009003042550035a210000890511404003c0080c190403240080c0d0700078500c40d20005440c0b101e0b03080243c40907d00804443c11500100702c140100c0c2d88650b1b5440000503114020443c940da083c01c0c01c8800d00c21500040c008020400b404c004000d801e007c040d00c00d07403140000340b200f5101c0040c07485850100c0d035030096010741e003030180000a040c264002d0595902a40703001105c45446a03841d420706c2018008403145440d0060b1401c1400701d00d018080c0109038121100c0d000618101d0b104030503001c0603201400700380c0034200e041d150034804e4003920003850300801c030b40d585141185000303002005140000c0325000d08002d010030542c1303000039184500359010b0b194104107503240c0164084c2c40d4000d821020031519062000c0012601d6480c041200200949002078079091a051841c0781008802800003000010810400001e1102c2c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 15976094 1250 15974844 15974851
    0x10603030f0e04020f0d051e0702030304030f02010b040501060504050316080703020418051609050c0304050c101701030506040501060b040305030712120f05100b09180c09030d050d060603090209 85
    0x180c100c1d10a601180000c3c0030b072042ca01c1a0400b82c00101c3c0910300164140c0c49540581d03049410b601309074034003194501ea41c0c00c0454140300507800034000140070030300550200700079005510000620304d544200040450f43c0a8110000041000c0381c244018102080f051000e0030045403815511481d00501c5aa5a001400020301594803840702d2000d001499140c80c1c1c14561201c180e81450f040d0341c0781c50312010b00c5445941411820200850008414002201d000342d41040140580c1d0300310009210101c0581c2190f1801c10184602450040590a88140c0a184140d003d00130031300705418041d0949002d0341180c0d120310320410041001600001c02c440f0560351040380104450f06480081e02c8030b9170310580d409100e41c14881d00c011000342903800b40d889660b448038142d98050f100c0c0060402405004616030f0403800310100c0c44090260b1410060b03026000c03050b45807820f180300c1c01080c00c0c00110328600740071400c0820600c040b41e48500420300030f80070782d2404020b41d034881c0c2c00042c040c84015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 15977344 1250 15976094 15976097
    0x50c0d14030d09030f0905101404120506040209090705030703120e0603090c090901060513150306110c010608031e1b120d0b06070203070605031e0406050f0702010603030f 75
    0x40114420005003404580100c50820140da4441c407499001c1c070058219210304400054168888040c80e50050789040306a86c00901459800c0d407015005a810714003001402c502d41001388000200320b1007181ea4540701c5481000941400c0c00c1a1040c4014240085c1001d05d16820505041c00103403070000d40001207079000b0007580000c03007511405a41d42c40942d10700c0c0350444000010445001c04c001920040407400790b9145000303a4a080d852801c07286503005007075121040d0042c00c400070809030419505100900c0985010702e41e255500310031500d141a2207041d002001c070303d00c90400400e100b880000c16410015610b0a0016610300150300c82256500c5645000400c00a04400307030b4071400032170400d22404861090b0300003214900103401c0704083d40c221508110780c41c8a941800c0c0700703860351942d016000341861428020280c0320780d00010040c0d10006810074180110300a40358425020b24015100002c50341400c1c0708030201280002d0200d001d5a060440400000313a00c002100580e1095 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 15978594 1250 15977344 15977359
    0xb030c100f030204080109030503070818030313060f09060b09010807080606060d0902090c1c02071505070c0611070b07020102090a03020103110c07080f0609070602030717040b030403020a02011b050c 87
    0x50707000394004e000315007207024190b18002d00b03141010b4001d00214011040c036124441c0996030b240d44503540040c041e04004403500188003250350f48808240c0a03003010301c103580118000820101c2c141c1140c8000c401a20790719107801540c0b400d410407221460150102d40f000d80001802c0c0a14183c1e0351a02615460080c0b000080e14442c414142d81320004050380101502c2e690304041034008444d812024403001080a41035003606105003a100325504958840540d000c0081c484140c00c0080c40021f10038814040c87d0a89200020442e04c02d0400d151404000b0544400080c00d000c103149000901d05000e42e80704105041c0c0310780d42c0749251402c881d070900c5c1c04136480f8508451078025001d86c0c2850705440c40b50f45d2010801e83d10200c2c9070300c5501150300c00c40317500e075031840b6056541e200f0300d00c106000b42c1c204000c61303c0440d0700c0b02c06642d00b090220100e01c1c0340594810720650f20350301c2101c080e0016003102020004545c0d1110010000c1e900500d0080000000340e03c1c2d09456000c25800248a29174 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 15979844 1250 15978594 15978617
    0x40b0105190306050406050405010e0c0a03060c030e0a05072c0a0506030f030a020303010e0601050702010903080c070b04030308160e031506040908160c0801050c0d090c050a0f090b030c10 82
    0x3210700c84009503034844002d0003281811701d0aa00540000c0d40c003222113509103a00c42b40309182c0000e094008850042500404901e9034803540014402142d1007800c040d1071b200c0f00011440104031301d0128034800c070000c020340307460f03d5440d8035803901026216881010034040c01d5800c0d11501101c507000501d02100280303a40b10140042e20341100c0059401040c0030102d1aa12543c0e00800550f0403270b002204122001e64540d80111414400c950b002030200d41505818000325100b40042c003100342c1303008101d07204181c91703030303501c481c01e8006034070450002d0412000c010013080e0f80143c0c440e081e096400d24002a2100000203a1900768503900e8520800a480004415603500d401c5142c80035082618a0342e5600d04158907202c000b0b00e01da00741c3d582d036075214000070900350520505220b80a8a4081070821f031165030100003078018560300340c840481c2e4003c08a226555400c4080c010f105160084410a28106408095031a20720b19544603400141c0041c0350303900c1d252090f4213000c07a81c1c030708141c2800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 15981094 1250 15979844 15979879
    0x20607050d020d1b0c0203070801050606071203060816060314060102210d0e0102070c0e0f01170a0209011403190807060b010903050a200d03090302010509030a05060f011d040b0105 79
    0x401188204c0c80180c030104a2110250001034112110f4002d80541d4001c6450f104090300782c80040d51201c2c2c01140402c04000842c220440d1f581000c052442c0100700d203a6614013592401041c070703510000d00403094074100184e44c0c0610510700070140c8104694004d14085001079255940300259591b030030740c80031442c0c0e524070b40401110300811811000b0890000d41e844014001d41000b0022103800054184c0480c004907035071009845468164003e2090740c0c03c2241307480801c0c0c03041c07481200034851145524016914100b116000e04008440c84400d0301841e42010b103041c118182c6e540c01000c0a9012001041d00c09007265402d031f40018021034885c100c10012205030410343c2c0054194044c0004140400c62044500800c2020801c1202c0200b0901010459101403000300180441e403400390800065001d04013415003010000d0039980480d800c0e4a40d03509154044852403c14810301c0d0061010032021940c0504c1c080c00001c02030000d00c2c117550355480c1c0740418010b681c0700705441298000c034035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 15982344 1250 15981094 15981101
    0x61f030605060d060503160f09020703050705010222060507150209011b050307060605010305010b030610050d15030506010602010912083d0b1303030309080c01090c0e0106020607050d020d 82
    0x8100c00b500056407810384100b0100102414000d0074031a0140c2a040120b414403448100306440003c0c60318002a45030240c0d5500030f41c0011030480030300405002620104d00c080c0b000d0003e1020402c0e0000181a400286101c01821904603400380030060025601085901c85012550302540c4001642d40d0307506001662082d012045044d0003462a4900604101d0040080c280040c803801e0244030072516500150140c843c02d01a160300b020007030000505034074008442c0d840c004090300f07005152071500c01c0709405176100c005000c0199942004200300f04903080200d140148011710081016a500d5682c0c4a562100b040b0201c04102181020501104034900c4428101804203003240c00c69035820740341c07088048130101c08a1406100c51000580c00750400450b201240c0f40013080340200e0030755400b40c0003440092810707211500e050004071056031003481481641d5020760410041c440c5019012419001c0580100782190801d00a0003030031500312099403c0003141100c00f507107500fa18072690008 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 15983594 1250 15982344 15982349
    0x706050c0d0c0228090b06030105061804110c0307030212090105030609070207090f0b03191101030207110303070b0103050607030b1806060c010f0506040e0a110d0c0b0a02010203060109050108061f0306 88
    0x1490001000007582488109244c822104410801e00c000d000000030041c845c0424400c4e55040340701004840d21070180c910188102c0e28004100144200b0040e1007074030b4540213000085c80c02c2e0700000e4a0828540c04120030f545050a1352807051404424200003041c0f03010140080c0c0c01011401c010590980c02405207001414441508004a070401c3d035010010348110303a4020300901070314216240750401d00301602042500310360301c80f01503001400110001e502a24081e14000440038070000c40b540c040c8001d19025000b4441c0f1066941542880c03414018060880d80c20f051a00300d45400d161200b64003031104a01a005c503c130a03550b0800811414424401e030f10405500c2c110000d00003400c2644446e00405c42910100885041410216035601c0703103010182024606000f8018549080500913030311600c52540303c0c601aa807103600f20829005000c500c000750b5008010041d0a59105040500410007480c01902070308000c1d02040c0d1002040707080c6403140300d111510290341c0c1d000e81c000000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 15984844 1250 15983594 15983629
    0x2040207170a030207060e0f0d0e01030b12010903030c080f010b0702040b090a150503010c0e04150e04030801030b060a030f02010c03030b0d03090f0e0106080c13030602070605090706050c0d0c02 85
    0x169901c2d1220000c0003036000301700c121580c0b49002c0380110400000244203004101000007030210030413600c2305940d14008a4402e41c101519804076040355150380307408841040301400003064000c12460080e0584030000b03668020082403008201140581c104250f04551010964071f68401c03c6002040181c4400035003550000d030401c2c10b100c0d2000b020b074030040e5810241844107036003c1c0c4604c01c2501740d03104000d180e000942c030055401e007903107459071050300300200b02d9190528450742c170b41034018000000c44050300402c2e041c0d0010024060700c44840b5178050b804031004010700e0304581d1083d01c0041042c00190402c84c40890314002c150096001c084c621034000c0c07a118010449103030003400e0002d1401640c2c00d14502c5030707001039000d41d8140054141c50a03520b400595545802c4900c03200d811070100c1c11015001d413140040401c40c14401044154040ca4010a0030b1505c0f20f00c0c0380c82e02249038000800c01c041000000f06ca46408202140b01e02c44d5498002903032281800090222815860341c900c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 15986094 1250 15984844 15984847
    0xc0803030601020601050105131e0801060b0a0905010309021c03090e010f0302030c0a060806011407150207030f081501031a06030a051012020108040312021605071403010908070204020717 82
    0x55444400009903114400c241c0c00c40780b09070b072100b00454070790082d090300c2000c040c1210750901092402010000d0035184c020b01c0714101715921680d960950f0080d80c4400c000140005800d40c540c0d40c403418210290200382014428000d05502003407a65014421801c0b8060103078000004046c4a101c8c0e140003821b0b85d179501c0d00c0310350f151082c4440030091440b0880c400d124800206504d802c1652421080703941e1a01c400314281e803140c00550300d407841440e191502c101d0400004000940d100d0303607440d1484d101400140c44101c02d24002e0a0341480e17490100030300c84a1010824020300860141d1000310003840c021811080c81c0141c0a54032484191031540320002004120030a9000c0d41b20f01e21800300c4441600d181680c030320b0114454464502c01900282c1e0413000980428010724041c51000703401c083c014030346108644002c03ca1441050121090b80010341c080115400440c0c051140d810114001c000e0038549a48106480c86803020003402241c0101344030b010f01c10401d0349914070343c0d503c0c070040c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 15987344 1250 15986094 15986099
    0xb04180506030f0f0705010207060306030804031e0f030207061403090601090b030a08120402090615070b0709031e050f0708030301090c0203090d1b0b0a0e190f030501051006020a03140306030106030c 87
    0xe521741da0f00d800b400b070040c4284400010041e10071300402084a41050f080c1e842c050441d2070b0601c103d80315a5401000304e8243c184034000a00029a0303004160090307001c0c15a02c0d050182c001c003900c2003440c2c0b03204000380a000b0310800480100d04141117850018002a19108840119003441846500900780034804110700f600200d0346074180303119600c00c8540c00000d544010401007180d81c1c402540a2018040c80504001058000703640c2e00b10119040041c019544d0b940c80000040d038070b424030658000081500000c001d4200300c90142c0014000140c41e0160034011415a40e010500c03607082441e807900400146640280b02300c440410028005180d485860709285413006600c0403429640059200c0000e00e4140c09800d0f22429490f0b0380c1c0c0d54103100e4154040000301c8807608031000c44401c1041000420760105c125000c0250f10650001c14149480c0fa0514404001580310034159003000c1122b0000a5000b00400f44001028100c0c40d02c2e9261400407900404c40c68000030702082c40128003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 15988594 1250 15987344 15987373
    0x30e041514010c0506040b0a1b0e03010b010f1d120f0601080c0102010203070503060918010c0c0b0906040201020304030311030d0c05040503011b21180f0302070b04180506030f 77
    0x220000d540c2a8034081c0300761400c0400455169005001c040d00581207100440d00060222145641000b810344000c201100d4842c000303500041c080c100c0c0004a1088014121103007801e0040c442010802d082400d1074810a0320007408410001c1041d200400e11889032070910340d86c0d48008900840d0041c1202c02141c0030014040d80c2e01420f004240700341c403421001c03041640c414000c49105640790f42d1418155180d4100340120f102d00a0228603001c031301200208030f004000d115009000e8150364401c00e11071280d00380345440c080e0150a01050b600319000304400750360000111740441e5814540429a40151080300d4114050130350100c0080707042001403104103900c074000e03105a64046000f0800b550021484c04440c51016103000c021072807101c0c0c0c5075036001841901e01c5845490a802041400d040c001d60034080685500840b629009401c0ca40d003032650402c82540034243c0751040d545400d080420041400c210406035507442c0e41c5031000200c8985007400120524030001040f42c0c055503c4102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 15989844 1250 15988594 15988631
    0x30501140108070614030402010c02030a03050310050405010305030304020f0a1a0403020a1d060103110d020304080403060513030804023105040b07140f1806040f06030606030c080a09030e04 83
    0x801180c0200c0140042000d000110300501114000d0329078000841031418680c42d540c00c001c000b41d040c8095601580c01607103080c802c00217400d00c40c0e0303101c1d543ea1806146520003d219500864003a519040050000520010880b0b400c2901103613a06103581c40407000481c0383c02183c206410082070301c581c010030f4004990140064a108640d81d11403107813140042d20f848400302c04811200c004442c0801c2c29940258000e80301c60480c0d0b234030586062440000e650a980c0140c0c3c1c12900e80c00f00140c1041400300324410950840e01401410903805083d440003461250007800c060321803840c080c1c1c503582390300c095805501a038030808090301e440c948403001000145012a41980c40e1403003c00003402c540d205481d03003542100142629810905681c241101c181c00c0f0100c03203c06024031904000f695034030711005d00b004040301c0002014072400d05600905a030065403001d02414102203a04a00b950448107082d84085407074070008a5500e0790404403600c070400451150050315103035a62000866150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 15991094 1250 15989844 15989861
    0x304060209130501061e0804030c051c050301090b04060608010905060f040f0b0f03010b031e010b040612120203211308030c04030b1602060408030a02040b040905010305160503060a0b010201090c030501 88
    0x106d13040007001314103a0711040d1000624000c00059451400500020b01440316511054000d004841802ca05007401090b02100c0400700e002148010004000d2004103010b1402c3d03182c001c0c6d030b0a1203450300d00030014140101c1806070500ca151500001030351500e590004a6000a0007032040c41780032000710f8076000418070340c040240175140400803140039040501503421113880c040c000f416507007070030000801071452001c01f0301d02c2552130306000d9007a0743d00c80c000e01002d030a100010749465030341d525003400380c4007501c4071007800d5400912240071000d060f00c08032030011190010070305080d07549281c108100c2c1002e88000f41400c2c404000e00448030031010141c0706a0344510030390480c9440d08a094000c04410190803001a48a000024002003111020b540c00403407108025040540740c0b030140640d81c000d03420803441d071ba83e0b40004100f0b20130100100580d03105880c0e41d1041d010f0600c0d01103a00c4040082604213101e0b240d1604002c207074400d501c4202c056422003900011152a0324086011b4594138 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 15992344 1250 15991094 15991097
    0x203070314130804050418020301140105100809030301050103110c1006080c0102031e07030c080409050a0c050c070504051302090a0e060c0a050a080403050f070b091c080606030406020913050106 85
    0x80300040d80554000e005100b4590300f0400c80d0f401e0500e007008000107071040c00c2c07400e40341d51450745000340180c134240a03009008210744166019036040c5018840d0302c05180001070100700d071910a02c200101c0100071a81911000e180116a40d214643c0d0812207100d614114411803140b01c0c0344d04055849035000500b911120019505030544d0310004981d6402001c40c5900c550f102c0c405c0f16508604258000c0114510a041c2408181d0320b44c2c41303001064009507c0302480b20348450030082c002100b8401e94282d902070b03040140c01c1101d014565981d4888902034203000700c4e9620701091030014a030070f01008a545c02000d803409813406084d100c02400d440413825406100740404603030500600010341c0c03c49a8907599450501c145220304039042d0601600541c180003042101c0b0305021802c01c0104095030140300200300c0e605040e41c41c149410201c0365148500c40c0c248001106140c0d0260250780c101c501107811907126101c60030040300910483c02010762020881900214000c00c9030842412035196 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 15993594 1250 15992344 15992381
    0x615080613060303020601090b1c0312052203110c040905010209040b09042d080a030b010e0a0518100b1201030506060904020d0b0901090c12020f040c020705060a05070602030703 78
    0x40407252001d580403800020056009107006004522190f8050003104400411003020303035900c0782e4004040403480805030f0008582d90b801900c1090f8900406410074910608040e80c80c0743c0c030815400c9174286040c02010007034030005107c0803050420860350100e100910401c01d4110a240c003a0003035000a0a03180210705014660440e8a4107200b1984182c1d002210100c804a81d0f0222a822401510141f40340345503000841d40400c030f03220060044050691000100c0d00c900f40005894105600b820714402d1200d0361043c00716484070071081c125201146440100d680300c1e44450085003c80d82c00206582c50007064200c45e00f503901000d1412640200144c03113040d1100001d102440703000311006900005450403210014044640541e8000c00d000000101e8507003030343e07510900d02401d60005000c0c0ea9010000010f6140203011820000d204407010880e0042143c0065100c0d50640310302c034410080802c0f500140303402031049454107580010215600d02d402c1b80041c0c01003a20489070300b04000b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 15994844 1250 15993594 15993619
    0x6060c0b010b0301050a060f1215030605061e0409020a1205031b010203040c060c08090405090d1103090a050111031303050d09060302070b06040506180c030403020f150411010306150806 81
    0x10604103d9050300c402400c1c030030485041c00c9003034402d56040c6070f40d0400c20000d01a802440010340c0310b94903c02c0f804404d0350032481d00c2e6080105c00da440203000d091064455a10500d0507440406060749140c100b40c0e80805d0034400da0000502e00e201d582d20090f6120054044842000000700003403204090000c9040300c00d03807940c003040e4200d010844005003240c41440041c00390a0060454907181c44c400e111440c60204240c0104040d10001da0318a49203074018041c08018075000840701c1ea1003c0c5000046044c8880c4034001100c1e48000c0c86558140806101c00f581e81c142c090040310b000600000206048943e00d1410381e5a4150441d41038001034801c00340400c00d1031003402100c0c081c03600b0100045a5460310400c02000301005488076910940c0100c1c1103001cad204c0766000300c1c4240d0684000302d8591600d4100a8100201581d10707100a8225441d030248a031080c4140b9034001c1d800081c3d0714100c00000c0010f03001024550451422100700341060309015900c101828030500d01a140b8008242 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 15996094 1250 15994844 15994859
    0x9060c020a0503030a020d1d070f0501050901051603030608030c030702031501080a030806130f0b090f10060e0102011401030b040314030c0f0c01020904060303090e060d1208070905030106060c0b01 86
    0x790003540050150300200080b50b028401c94003d000100b072640c00008082d10f03183e11007c03130100c1820720b542e069001801d04102407160900e401004040a00b0300314035003400440000d005100d2000c440341e01c02900e80100041c94440c3c0c1c4818003034102c19080301d6640148210441e640d4000a8080781f082c402d40c0c0c2d581d0501c0c43d028920a0480b0b43c83e00c001c0891030260303038003130b15a0500100555000b401504061050f10110b00951014603104100050915000000d012140800070000b0703401075010b0040c41810003400601c1c200b180e205240400c1200d003c100101d0140c040003100b4042412018004010b01c44191041401140300791605410042c600481c40d03481d000c01c4840032704d6418203000150041882c800108241090700000610741040d25000800711891600103a00040b24207905000205000d0029a0480021102c11004560b203980c1c0802c3c413040781e24103004100101c0086010140a00b072800081d11000300240300403512580001c00001001c5016614140c10100014480 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 15997344 1250 15996094 15996103
    0x1811011b030807020f06010b07060605040605030703020d05030909010b0d0e0109110d1a150109080f0c040209061b01020309010b040912110312010e060a09021c0509010b1309060c02 79
    0x40c180c03100d503811608400c0d2402d84a40000401650640c0181e590b08042075805000d03007406010a02803254850302c0c20b0424000316419900003034001d603d001024003ea80d4002903881c1260760456100800a6a514020303055001360503034190000444000480c1c586044d00c00340480f410010010881e41c406861594280c8040c040e0103043c0c0e441c9424041380500b8683c81c1105900d00403c801c010822441e800f140d1220003c440020399898030300a440442d682c406006801440c41c1030051900960011001d510b078a05011040c0c0301b01c1e8002080986500c41d0420b4540340e20546403a50080c03000245110301035807044440d00350a510340040c4805500e801d01c038800d55560410481c1070318002900d4244d64010086e5485003440c4028000b0300344180104420300d02810a900c500300c00c82c141a414407104080ca070b000000d04034014080310b4005c9080c00b4415081980218022800c0d032a1041003a0040001c09106a08400e15489060074414945c008200c0e1520900c0204450843c40900b03c4e01c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 15998594 1250 15997344 15997367
    0xc1603030806040b0a0b090a0b03090a0302070602030c06070806041b080108060c1204020603060f0a12020a050a03082208010603060b0f0301050105010504030807061b0206040213020405030d12020409181101 90
    0xb04a445c0c18840600d005015001039038020304140102034480c0c1d80944180c00464114026070b0085031180e04241d410f01a00c0000c080c2e5000035400c0440f418600c035240c44c001070425041182c0c9030300085490303413503070010841d0300300c07040301100b070001551002400c4030390902031002184a14408110f10340c6000088400420004403110780075181d40d030800040d43e00c06170419510440904828a090b03950f8003120004000c001c40844040946206201c80c0300c100740d1000d0b20807d03042c181080031505105c120303030f4104010342054038441e01b0107103900141c84c03440e00245565032030031138084100007041d80f0a4040380380881c0c600e143d040301241054240e60003402a1800103000b400100002000c2d00003400005201d10004550a10025440448a8502c40b800b03001a4484014402503040c10201c164078280000c0d015407809081c6004660780d24030145004c000c00804032503107042030400c1da0503035010702004141404140e00d00e0000304c2e4130b00c400400c1580c0e0582c01e483c503491503602a070b941106 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 15999844 1250 15998594 15998599
    0x140601080a020405040f06020f0a031a0d03030b030a060c030204090f02040503070302010c0606081506010e01030501030c141504080f0d0201020309070b07020607020a18180203030714030c1603030806040b 89
    0x300c1016582c00d000282c00098021152501c50200d40700c00240c942c00076218142200d5442501c9084024004042d22403007a43c01710041c90072103c42c02d05464180f4000080da400d0309000c500b12902d4400b02c1d203091000000a403e442c500780e0b0f1140140c0d459002031080360b0030103405100390f18404504178200c2c45688501d6074503900030407082005500500d071241d8014060f0400044155640d03c60906018071004d95007000c000320070401c0615a000004139841110030720381002158159034070a6010341d4117002d450046504186440811361390001c20310a44441548010b440b141c0e140403981d035460040c080700c080c0d4010b00076101e040510510990780304040140051003420300d8450f841625510541041c0d030090020001c8601503100d414008004041d0340801c1c0c0320007001010640c5c102e40e0710050301101044142880d00140e90000f091703070070301500401e5100170060100011440d5220b9144c1c900824022103811003a280c011000501c01c503070094540c0303101c0743d840500304000c4841d40341002d075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 16001094 1250 15999844 15999853
    0x608070503030d2f030103030f0809070501120b03070906050f0907020c011409121f020406050708130302030615090709060c150209031902040c08010b22030b040b0414060108 76
    0x150000d05504207100d1140700031004004403128401c00d02020300c04031361030a9800710000c0104109540940d201c9000c0d8468500f00c4040d041ca00c099545640c4507110fa81d042004400380300420030f94680c0100300c2e162009081b142c0c4140d55803540c102a025034400e141c850403d02460044034103101031424031500780390f80980b0140180c8401501c0c442ca010303d148414000612950a1a807540c004000200303919100402409800d424520031400c028011000c0d007500504c410065240c2205c10340c0e24017640071186c5515424016030640003181d2603400070b075140c030441c000d006d401d040c60300f409503950109460303562050b91680c46c1075030388150318407a020001b540c03441d0820216107030440900320a10080405840d06c0c010034002071808400800980055401c00c0d50042149800e11030710942c0303800c41c00d01ea191036251038440d002c203008803000a00107010724000e0520b070030211a1300c0d0340610390004111120b4103081c1401500c0310350445080b5111410a00500708114000441034100c0d1504002030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 16002344 1250 16001094 16001107
    0x7020117040c09020304150510081b041103010b03070810051c0201020f060a0209041803090e04050109021e03151b0f0c01050103050a030210090f020906130c030f060807050303 77
    0x4640d4880028010364003000c0c00500803810300501d000540c0501d00a0500c5104c05030313100c80b10b01c201c40000d0071414a03072200035400c100560000c02c40850a180c0c01e82c00c2c1075106c1d42040440c1c00751041102450144100100115401c0c1c0c100010394000c0c0169078806d480756898240105074980b940c00b503aa0710107000340b001c030840420481980b0b8914410310684251040c00407a13507281c2802602c002d9021500441c650820b4107241c401d20071201c100c91b075030343c04101c03043d02e018000c0c5801d4054120003403460710004050220035040800c2855002d8a001030a6032450701c018001c2e021242c10341c0c4640104403118802014098034103000f02c4014190a0184050300e030030354080d500c03202517507003044800d00c51029905001c0c86064001d40c00fa0019000a1b50946002810015090220381c11240b8090700704000c521492030020843c0d074151a00c003a2611000c1c0007484081c20f025903a100300c3e041403800c0722169407680002072200804001403003040e0316003c20729182c00306401000e800d0707481480710 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 16003594 1250 16002344 16002377
    0x1203060503070506180405040b1501081902090d05030408210a1d031e03030703140f070309020604050d030c1e020607080a0c020d03030606021506030a0609020406050d0f02031002070201 81
    0x1780f1a481c0100112200c0c00000d04c00306081e510221006d550705510442005443d95401440340780c01402468149214502810b441c19800d01c0c1c080e4496506501150a00035a191414241501c40d0031034110b944842ea03504903907650b004869010302220305085a06041c82c1058002c1d10300a1076141c8849000b151100d0540114200380040075500d03106112000300344101c202004140503495a024581d2440e02c00e4028040d00c4a20701040345e00d078002d604012580d0706a03464180c006025260203e81d4005500001e00300d070146401080e07204c0c041010b0f80d010550400841c0310624455030701d40b0b4168864802b0180c00f02d0700703600040c1d0004800c115000000c2d010800901104016080903510b40b05d00e50003041e603207807240008401090341e40b0703803e10a158040104c7c228040c0fa10741c207184140307003034008aa100d07418a08024201c945036000e010440d0703a070360481005004041c01c006c08445c7d890900300c048800d05d190a0f802405003c00301d1810455600848010a806850b004000c0c11003c96 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 16004844 1250 16003594 16003597
    0xb0a050d020910050a0e09010507020d0807050d021908090d03060f03080306040e010608031c060321090504020a090509150619030905030a03050403021623010c020402070507031203060503070506 85
    0x142c4207443e03124420116032990740c581c0ea00e024280b92030100c4144d10b8aa41c40b0703030031940d010380b1050070b562140c082c0001c2e80303902501c00d55010859180c016120f00305201390030042e024180660f154106520f6941d0012607001450500c035140507000c8601301c1195180a404540407802030401181d003070701013407020a6280000315001400603000140c100e0112890a08582442d003151041c1d410001d20040403603042d2000000f42e11070030408010369071840e0303103c0b09880110301044003034100314107603880901c3c002e411400041102038000c3d0b50328410301c80000c00303689140c0601441203020342d02003011040c90400780c01145801618280c9014070240e1004c1005000f482d00d04200b50f06c51600500250003840509000251a1000301e010f0401d460040c0c2031007141402040340004103030042203000300d001e158000301100000000070071298030004071861600700c10080e4000c1d0001421104109000812100322401510002c0c01b150b5103010407002d89829220b09981644400d009026034a803120 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 16006094 1250 16004844 16004851
    0x50705040b0708130e06150c06010504050408070203070e070908030301051011190303060f05010206060f09090a0b040c0303180b09040506010e040e01050402090a14180304030209010b04090b0a050d0209 88
    0x4440601380b4260807113052610510350400703503210318910148800f41c1441c2c01e000380304021021405040200d201807507076407481d052240c0c0b8400d82c0c031080484c060003001e100b04d908450f00030f002d03682c01d02e840381c11003050300106903078000003e034207081d000424550101c1a207060b40c0004102d07601480d200101117502480d202c06d4608140100c42c15400345002e070441e5000b505e84240c0340072031014a0302412500910250340800d065400100c00c01100b0750300d80d03018000e03500e8100e859a0464641c502c0c20751130a0128500106800007060901c82030000c42d07401c07101200e101e0754800c50540503038002c614914180d0311481d480e001c020310450040d407420390049075001506240401040380e0200001e07040c0d134031116000c9600e07550340c8140f10030b40c20201565507001c1c1c0480818003032140e45809400c81440700401c00d201d0b1580c82c2c1c0d03014659800c1071046400440e0014417a10440d40c448503242c2c080e0740284503107518507150014088075400d0101d83e000880398020129440007116400380711a03028000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 16007200 1106 16006094 16006103
    0x6020c010e1c0510020a02150105010903030206040308072a03110303071d030703120203030a0b09100311010207080d090504200301030f0f0c17060a050705040b07 71
    0xc1d0881d000c2c411110710307080100a071410514104400080e00c0f040880c0001b41d0700c204c00d54001011101a5210090100b1a03642d980040d182d140c0c07140320060142e04004d0008000c68004c20724264005400d00b0b0150301c40c503030030303185803080003882c40e916902c2c04004015000b03142c0e00903103285004020000452031030402160140490704121781041c6003d00158000e501a14140142001035900c4541407001040b0141c01030340726001203d00c0c001080c50003145000c140780464002c0d018003a0300c1c2c1e090340714a0031512004d9012807509030450640c402e100000400d90410881c08000511699520a00c01e00b080100810b4612044c3c2c1000301000030005008050401421681100c3d801030342e03052a0042440d048403003007c50000076105000100000410301072460342c801e9040c05040680303000780d48800c10802140c00585214000550501c014060200c1e880000d0426502a = true := by decide +kernel

theorem cover : BRFrame.Cov 15827344 16007200 := by
  have h0 := BRFrame.cov_init 15827344
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15827344 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 15827344 ≤ n) (h2 : n < 16007200) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
