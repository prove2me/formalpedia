-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5195
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:03:29.361114+00:00
-- url     : https://prove2.me/submissions/471745bd-0dd7-4d94-a614-3ea623197d19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 934172661 ≤ n < 934352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 934173911 1250 934172661 934172671
    0xa0506120106020d1e03020c0f160503070e01051503090a0507030f03020c0405010e0a0902010215131e03020a0312090c080607030c020c03030901050c07030b0c12090d170a0e06 77
    0x80c1000c0c010492240e041000e1040b40d038503460f018604d0a9108001192520210000c00c141600410203600d0072408010038242424228100d82503400250800c0000031103034010341b03010340101d060205022040b8060903040701d0014210311001e0441940d445529000517000b02d07003600440f035640d80820340401486c8051801030354503542101e01441c019240c10b0b07004c0202400359060000410103000a401010740c00b01c0800c0022400900c50720040707040c03215003109002d0280f81c080c1804110104034881c000035900ca2050344400360f1450130703c030040490702c4a00400582c03001c0d444200091084190039814a00c1d04408901c40c4001d503101303070100f042500702c0b031002d80c02002000300d6541e15001700fa04821150001d041d840d0500e00110740c07a8411131400d6130610a0008400b00b20380c1c0200081d80003141c0100c42a949414031307083c50140c0c1d611a4110318495411030300452480c540101d021416001c150301d40880403554003070103601c442c03002400f0a040d60381c0c60300e01151500382402140d01c68 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 934175161 1250 934173911 934173937
    0x7030503100308120a0e06061e01021005180c06042301050c0303090105041e11090603030c0d0309020a0501030506010c03030b030129040f09020a0e1f1e1509050603060a0506 76
    0x1605e4040b10707075411101c2ca06c06000d2940e02180600402d0b864035842030801941d090103601e240c600078401030740341901c51080865107614240c1000208101c54521580040c40201924031220840f070421056000f94002d0b50500c0004000c201380300c2e11800c039015409601030402034200075103200860700b03580003111201c003140d4560040004122104c1807801c0442000c2c0445490034403282c42c0c8da003843c603000700860b000d12903200110f1510b0380c0410640b4900650002214000c0c5585c90004025100d0740c04120b0094260650102c3d4640c0240550b5104031010b958007002210941c50032800b40c1244100d40c2e0705950b0780c400700750845503501d0400c1c5d890a00d0340e030782d0800007025078184400ca80e4144540020249440c589400581c0c500d41d68000302c40c0021103043c074039200c0c002c5600c400042c1c004240c038440c604000004900c0e0492000700c110305107150440700c0980c0c1c0e84243d40f003900103a4842c14000340301a00c06200515080000c0c5412942c0a4005521a40c0341c0012603000c0d4040c440010003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 934176411 1250 934175161 934175197
    0xc0f03020303060a1a1204060e0609160b03010e0f070c14031e090a0b030a0b0a030b061207050a05060706020c010204141c0321090b040c15020f0307030503100308 71
    0x84c1843e8052200503c1ca00d1440010070070180c90354242d50007911008080c00d510300c40031605001c1b198101c4010402c1036401c0d03600074182036404907503809084007c030303800d8120580005002c00b82c440a6070704079806a5154980c44e611103080d0404c00600408070810300c11522907120102d1624019440300130030810056580702800c0000c1500060a1203c0c0e01941c101049039241980b6543c5110003280d00c0080b42c3c5440391038503403164000c0d107140114103810501e001350020500c0088004140a13010036030f5000300407480311145945844a50040582110200b02c04110a080a10040410f0780c0204801410301d6290b0480e00d007603a02c02c0c1e0001800205005000300031340380199000f817440741c0280d07015071424001e96000c0c8c250a41c1600202c940300007200c0600702401260802a4515448024005186040d01d0120600c18150040100880e00c1c03070088465540001864040c0084800c011400c08900303a60459803944000c00702100c106c0e24100020000b003280340940024441c1c0165141 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 934177661 1250 934176411 934176421
    0x14070b0403080603101104060819110301141002120d0f0608010905120a0c0204050604020c0f011d19060c0e120c03120906120402040204170f010e030703080106030c0c0f03020303 78
    0x850945090388070a20395280c210b540c3e4000000b1422242180c0840c108082c42d2b6584128441942d01078104401041d41020f0644150191030001541aa0755460101189903001d0043c0801e040e0740e00c51503030141e48224100c0003d040c6203000b4104e4010f00040101d000c0340c00c001240d06641c507682c880300090703440d0101a805c00a091084801d603940d0000d06904000601e040100310a51070315020b40660f50310404903105480c1c0d901101d0702c82c40b01d8000c4a6903002007007000d500820008690000c02c0e15070000380c03000e00e0740115488140d10032441e2901440b020640f9103000610740e0a011000703114540102504549400030110826070101010f44048503125007458204016001d10164520f010040c0e005280d40702d10540b1448401002d4101580e9140d07c0805c000340b280303401c00001039040208011342c0c40d40c0061b003400c030071927800d000b441040080d01000b50b59005540c00100802d10342d400511030140320703910000c00d00c1c0c080d1424458000144c0c40310341d132a8101110a800507080081006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 934178911 1250 934177661 934177663
    0x3030c0b1602030a0f02101b18050d24060f080f0c09011701060503011805011d0604120318031d01090f211406010503070608060a0614070b0403080603 66
    0x9a030100060907081d03250108a403009440f845403440314420b0106260010035950710030854031003c0c3d40c20150812400c0c21482ca0b0b45040c00320004864005410206120856022089901c04444014201c1441820140d40344c0c0c03142e00c0c2d043e42e489a0002c1c065560041d01000b030190078007d1688070318081086081c052003901700003a5207206545a48000d66003801901e61100700c81c111184c04080e158201c075142060340c0944010352115a240d070030310213041c1c5d000030035003480000c1500c250002c03c060007444124040c2003a25540c940d0342600581c000802140001c00d00c40c50307041c01498009030480e60101d80c42081000081c0590000314541d849944812142e608540c040c042401e0005405c1d1500f0315081a982c580e000e07505039001440080519450f6003442410195804005071540e140203510042e5100400d1050600c28800c08400241143c0681411405806c1c0507004440d890708040d8143e8a890311a0001410624100107502c040740c00d60080380d02441c8a41c0d0f8100050410300109 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 934180161 1250 934178911 934178933
    0x140a02040608100e071b17090f0f0a09020c33060915060d0f060b0d05074d010c0807050c03030f0705130f030501140412030509010f0603030c 62
    0x103e03850300340e003490038030025001e207801c0707948a881490020b07502c0601411050307a48400d50f4004010801c8201d241816080b644080d000005041d03c0c0a422030000f50100008a00c0c0032034101d801c031074122001d0140c0840c0b074004180c2c05603214100c2d020710a9001081903d072000c04482540001860411404040d413076820070b4105004403554501810b0890344030250000d0623403014841c2c05e0008401d11114010707008000002943c5204004582da2000e088181d640301428042d8600d181000080c1114003400512081e40440e0b25007024061508000040c14101c281440c50000261145032501071902038480301512040400420b00c00d82e01180a8814180903002009001c1e060203c214003a8001003583e80c01841c041040925440304c480c1621184901c1e40021b5000c5a4038a000c00c11a00c400158401c0f00d00c034900030001d0740c01c4502403ea00c1c40c41078400400078031002d5004105c2c18400e4000a4100900c2400080d650f000c2100b03510807940c0c2688200c000c00c06151035201801180009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 934181411 1250 934180161 934180171
    0x1030606090515120c0d2102031309020f0409020d1d0607020d0e18130506100513020a0210061e1e03140a020d060b120106050102031c140a02040608 65
    0x1040c0810f04007448602422800301141a0103428010491400e4107800c21031a0001c410183c03a1001800031410003404100e81041a42c1c1d034101c2e404042c900051001003120550178003160141c81e580e0420010070069440410a2288203030140710100f0003d8407403004000350f140ba01f00c00151921000c00b0800340d0181561450325540020080050b0950045416168010b00d890b2680400440b240098000c01e815410311180344840c50401010040d000e42c410b40c818001d10440314541d48000400d6110340d440d0080d143c0044030042c401e10592400d401801c0d1401c1c660042da0302083e4100d0f800030460b940317944002c0f845644c0184000d600150140c030b42000c2c21051005800315400c100c0c0440006900d0301c802030604500302501e02c0c1489c002c1c419900c009900421b03c0030b5410b010f042001c090007400010500c181c5500300804281c0d241403054104a620680142d030404505403851840c0005c1031207805112511050011304024031722008521806480900580312410840014188100202 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 934182661 1250 934181411 934181429
    0xb0c0d0e070b030105300328021207050c09040606050a3305070602160c08030c10110403061b020c0d0b0115120c1e2d02030408100501030606 62
    0x805000c2d40000604481c1503170400da50211341c0200d044e480010020001c2d030079a484000019448110540220060a070240554246409540715101d12885250300b000c80310096801140c5c150034a184030009408207502820a81e00b441d10b240c00441d582c000d04035011504c40e13980d00014401e03845c040a03a0b1000d8a85501d110f000711403c04008809980c41201501d581d000d4290400381492180c0210fa01c950350010056441da15502c041602c001a04803045415264030400450160400006d40c0d040c0d000180c000c003d0401c404103c83e0040015000c408054201000040041074145c040d0000207034202c01484410703004074000034202400c500340d691140c4e1034511610049841c0805d0705064844040e034042515981440603244000240034400d0102c2c113091500d00344c00c0d000400341c030940c0d003640c0070341d03407910f80c0050129400507444140c2040c501c007030f01500319a0b481c91902a040c00d241d50048a10300303a210b02c02c891800d12412803501c0200e0f180d50050003086454014031005001004d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 934183911 1250 934182661 934182673
    0xb04020118080c040e03070221010507110309090907080f03030412020a02010f1d0a03062003090a0f080c010e10111e031b03010617090c0a1509030b0c0d0e 68
    0x2e481c0c9030b150300e8920b180c180f0541c2c440d1100004208103000b20345d0900d41c01041d0b0600340b08a04401c81001102d0751803084603500c0d0030000b41116000300c204080035101c1e10099072504440c401080b01451016003201070034443c2d500042803400d0200484815541e40324000d42d120b1a081c604482010304c0380c00b5010440d0400940f60300142d0f040107080d902180b4500304194440d484d4042c1000c0c803200c1c460707200d501480f082070010034029580d00600318440340418041710031501c0001c1080502c81510082119800180c4601c003041e081c3d1102e03c100d5204210103850300910f440701c0c034292012141810000c2e0410301d03000303032098954412200c552900d40c001d903082c1348002100e4107411544e04844038984100000050114031001e01d03940710541e0f00950903489585a180c01410038600c074052030042c0c0746840204c0e04018000a0700728004100500c111011800c4c81c003e001c40c0c2c03442c0e47c3d0a0003884902c403000b20008849140140c0b19071140b05240791101d4051242000761401d8036551007181e0400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 934185161 1250 934183911 934183919
    0x10c02010212090f0a031409090115021c0912030c081209060112200420030a0c0c020d06092d11100e01110c150405090c03070c02010305130501090b04020118 69
    0x4a200e190058250507c1c01c1c40c101c1d000340000c000d2007200a050340c03000119001180e0280c00c110f02014140450b4200c1e40d42040742043c81000c01540684d880100b003402408200b8000180340000801e071091810203518146d0347d54120140d0450765000035040380407808c0082e50740b81040814010700c2650964410380798162a04440036241d092500301503055080c10b41c400e130b110364001105e450806483c5a20444001d5002c2803180c0050b40d00301d001034203290440c0152403244110083c12a0000c000b0120341e005691100000c0c03114103012541c066460010050380c0d600d0b0714410380e80c4c80701da00780206100010b1030b01410602440508522403800b540101033f015500041080c0005801e0074130f40340b50403048411910700030400410660001040300020440c081c1e000151044550940e564101341e151401c0c01003c41c0002c03288000042c0e501c06009000d9032094104035042030700b240c0c07030800c0b1050700d03150b060075645416801c2da500c0034103005010443d40c1c0301c48000110300d0507000c00242c0c1814 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 934186411 1250 934185161 934185163
    0xb0f090c0f03061c12020706050a1205040501090f08030415090b0412110a0503040e060103020a1b0804050a0e04120302130e18030a0c061109101101060503010c02010212090f 76
    0x290100c6039a0754100072000941d203803a0621851101c400113240701070040110b140c41c48080790620340d120014003500d480051058007a50640d00c008441d030b00c0703101224206a2000c00101402001650700b1340d00c0303494600c0480c584000c0030703000c1d43c001c4090039524686801d01491314107101c007801d0b06c107904c0c00c401c1e407000c00e115541a581142d0b0020441050808a60003150000c0c52401b80006c24080c0007650b808000e0000000c1085030b0400c0061841951600019801ca0140c0070000c000b10f002c008183c0d080301b01c40041c40011a2258010038242529a00810407840c11034002407003c0720240c0c180b0050140c5002e250001d20445d19040d40307843e008034000c18a860041c4a400c90035a0140d02058001d032035408180100511002243d17218000941c00409500484005031aa1468030038001a045200c2080383d00008018002c1240c0a002e0a0200c7d601321401d82c400034255683c50010130290750038000d0020b41645a4000741e200c41500d82002103030351010300401920345c0314080e460044c1e00c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 934187661 1250 934186411 934186417
    0x1b0c060e03070b152805040b090705070b0c0f0f0702030c0409170c0a1505010f0e0702030a080a0b100306051c0f02011448120a0903020a090b0f090c 65
    0x2011181036502030340c150108017411818a11002c02113514081c04108002c3c0003450300464408031400d101500c140002c0c41080c1b50150b600e8000200c0230000c3c4008203900d04209038000e0641441d461620642000c1031015400907400407503042c0b40010807105614040090501e02c400440d402c1062620a40d03449034440c90a403072074400704001043e03601c90030b04103000115660b030b0403400c5d548003e050800c1240007401c01340103050b03004031800c40c0415102d0792a07203000e104484030340096260011400003034500140c01000020003d0f01c0e274059600c4c6131100c0c4c030a03040e011440c1c4c90118800b800d0074100484002c0721200c41030030784804d0f040c3c5000300e1401c00c0c611038502d4081c07c01507071000d52096845824441e0b600540c6c001c140360300c000e0400781304a10001c019521403c2c071141d820400041c01c3c07070410040e41c00300003013030340325054115800144034020f003c40a01420010340159980d030215840324519030008000c40d40d1082501c03114204030714821940c04046684414a00d407500305181c140c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 934188911 1250 934187661 934187671
    0x406050a062411010603080f0903120a081f080a060e0f0d0509060d090209240f1806031606030e0705010203070b0106030f0902090a0c110d0e040f1b0c060e03070b 71
    0x1403000708511a10f40070b502c8403000d13682040e005a5500c211246040342ca40c08680b0b500d009100f079a141440c1840c43c0300544100d0030080d55061655101e105902110080c08a40007280246408000900d4070003000715005e0075104080201d0014501c480741070401410040510301b9800890300d00c4025540f0400300d640d102c02c200c8080352500d000c550780400034030740c140700250005044002e00088110008603c07124090050b00002002c66000034070480c40c44d58400d094200040c0c5a0002d407104604134007a0b44007c014044464044514400000a100f00e81c40746010a40d50341c501060908148641400f030802800214034200c9c4c03596580300944014815101010b5a45002402024a5400580c600303a0000c005410317a007803000c40e010040141c49614801f0034056140140d17000d0010854026040180c0c5903d41c050f0440400c0c0070207003071058070300d619141da60740c070712684500f030b00d0958400100b4030350b915003c3d00000d02d052002c80307500c0010084694000d115020000e0560744045600c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 934190161 1250 934188911 934188917
    0x21c050f09120d0f0606080f070903020d020d0f02030d180f06020607050318010606210e03030c070201020a0609110a090b0906100e04060b03100e190518060406050a0624 74
    0xc0041e03950f90401421045162072056040c40000640280d1101695005016031a04a411a00e8040080c0d074000000d1100940003108440204090705e00544000011400f0707112008407460103a00090400000e00c85590104030030308603440c017010440000c070b409080000172007040242080d002a5582030010041801c100340000000c03042d091481c1c2085e104440329000b400030030b17102c490181082c4a40c440d52807500050404008400c482070182020802001024520b16100d5040300b031020350104006a05510990702c189000074441d208181800b40540f4140c0d0303450102c1d0301004042c2e0300d00da00c50303048181022034a0069a56040c14560003800444503040e1300440c20400391240380b10145540c0d4041d140000004560280c880194407070008040711351545520754141091221065030001030051492032021380c8200c003a030003550000601c03070519440c1c8612146c0c552401800301c07801c5401ba41c460b024000e541c0505e01030100a0842d20740d10b4190381e2071034403000c010710310300458003010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 934191411 1250 934190161 934190167
    0xf040b0702030415020102190215150604030f0b04050c0607350a0f0210020f031902040806040807030912020f10050d020403030905190f1e09021c050f0912 68
    0x7402041198014007054007860030a421150002c1d00075000711034400c11003013602000c0703104548082000900c1c00c580ca007442d8144d89400440c4a0002490030800d608a08100400b03c04100c1500c0e00e00780c0705101d4a03003442b1134a003d25009080c8101c00c2d8015028540500201c00010800c41420a03440104030400c11441c0403131182d81201d00709a01c0c140c0b050f1000040315002c00c0d41c00522440749000795001c8501012400139880300724803540303902c507040a20a0011410090380040702410f5041180805810203455045c0c0c141410825a003c4883c020001020410160018885d000804030850412000d0b0347c20b40200d9000310305107610500c2202c60351280f444850240d0107a400c500c0c1c5825085490f240c40385405080c031842c6010b00b5209155220415a01c507a45c800240195880d0304d100014003072904140c0000c03a204400341c00942c01d050031001c035908405101a00071640ca50204030480c0f00641a1002280d4015029920341c44080007001007c001c0014038000c5c280301034107055a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 934192661 1250 934191411 934191421
    0x307050709060f17011d0c0109050a18020c0f0303090a03090801060e010603020d14011e0905101701020f130312030902030d2f03040303090f2304020d050109021308060f040b 76
    0x401000c00c004604d12440b440d4405c106c900f40000740b1022629405e80320000d5a540760010403880007030b54400e15042d146c40e01d00c8501c8003985900034104128015003207a14008008500707a041d6001210400041ea005079609404c1c0350780729111100806554008001050070036541500d4034405018090505400107440c92249986034002500c000100c2c407040c1c032a5851f000032258224240b00c529407591158000405c2c8642103128079802842d80180300400c243c5003840151500c540710808000c0343d5424446103040300d0210000341360403404010072130000d84c1585404128880140e100c401010320709040600142c6001910103805d901a00b424240c85440702d02e81c000f210072001e1407681c410341500044090450000c050400d8900c03e40728190400c0d1240c00103104043e4074410030380381401075040e42e0011064400300032813030000a40050311701141c41c0b080000f0341d41300303030b006000859000500800840c5203550a20241c02c034000649803e04024281103500340000d800501454031240c0031174 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 934193911 1250 934192661 934192663
    0xf04080705010c0201050703270b13080a08070f02011503060506060c0a080306040b090f0a1d03030403020a030e012c0406030b0901050406110301050619020313080307050709060f17 79
    0x1808194014028880303c100c01030001d02922054440e10042800c101072031603440c0708039001e09090164030700c060b9880745281d101d15010400107440a10b4180091a0710300109030440005d0520001c40e89494000e410020780091508240425017401c6914054200240e80c03104261072013240d40120f001f16240e1950400150984189010100326224590070b6204001c000c502071031052104950411440054205010440704d0898900a00f40b000340c0000e041189250311100b801c0407a5004825480240c040d568034643c41903500b5005a070104011030101603000c3c2e21503d01000c00c1c44c0032481e800042c101c2e04003004000c2010740c58010b81d2200868161100e0f40588000c40d00200c40518a042030700520340200002e071030954100b030402c00d01d00c652008406c210307030407150b0242c42540fa000c02c001c4042c00301c9801000070011400300304107500c68540c0802e9070320068150344024694409052504a25100c0c140d404640d0701c1d0306140081101280400b901400c5528980c90300940e800c0d810101c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 934195161 1250 934193911 934193917
    0x80c1e03010603260301030201050a0810120b090d05041208091206040f11010c1205030402221d0d020a0b0901200c1e0c150705071d010605040605030f0408 68
    0x1038156191034000018000f942c3c002e52603212280f604504940c03003240c903002c3c051009001c01380c04500d08120150442c1c0c803496000750b0005803000100701081d00ca000c91038401084090130b440c8000c0b45401d000c840b03030003070140d201082041e003070072842c041c50160064440701c40d03000041d12a0001149003291354a450703842d0380b0b04001d040c00b07643e25882c1130716040a43c0c240112080d44d408150000118095000c1c3d60050b08113500b0919002401c5148a412100b592004100300c0e00545501c00442018851310141c0c0c06030089440c0100d15a2440b5031034032450b01020803664003550014602d1001d01c1d030042800700040360000780c29940744c0c0d205003803c2e01500d2000f441c0d004000c80e0040c0603421945e44006010014228400c1d44d05000c19040c1c0103078003021044445469801c240145140f0389041180201008101840d190410807030f0b0303c0707040c2415001d501099013521310380348225800b500b40d8049400740030b40d8282036080c28100180182140401003201a0300c003620804a01845028015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 934196411 1250 934195161 934195219
    0x1090b041e060306030b36010e0c0108010b03060d261809190c02071809020f01080c0a03051b21060a1802031f0602070618080c 56
    0x81540d2155100c1c841d8501c240c01da8610300e403040007548003240c9140b003802008112600054010141d442d882d17042c03210031310b04824480502d941680d02c3c8207030b00d0000300001c141202060002032148500d002031030038065240312441c10441c1c1c040042c0084e440301402e403a000001600c022000001e40d18200c00c403442e1807a11003a845425a0b5030007008011075005001440031b040102005283d1041800b610050035604000da402040b02000c400c8001980400040841c920407610351076a03039200070a059403078400e480e103844e884007000815810000c010282c2c1c3c0c402841c110400d4a001c000c502c034580640c12180d420142c41d91b010a0505c48102504103803000c1c00000541d43d2440100703800700940300c600c1030082c0e803240400010b045107440c80c1a81e0888910040b0007001c04003000707170783d00258001020300fa00c1c0300c000200c0b0845151408152006409290020300c8002d061110140c450b52003040320700c2e1021041002886010710200e000001e140d010b071040c942054601842d00150294080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 934197661 1250 934196411 934196429
    0x70b030a0221011e0524090406060806040e030406050711150d0510050102010209010c0609021801030b040507090c050406081503060c09120a0201170c1c090b060102010603020f0f0109 80
    0x4104450039101d042443c101d4080ca603a81d858180e1000e030074440b61456201c0c0c81e90010148507401328280984422848001c0c0d41810300c0e1425581314005411603100d0f03041340d000200d82600b0804035082901c101070301e44254000450406140c81c0000b0141d01c01e00c10000c0140410382c191621903200c03025140084031104080940351040b80008800a0070201e59280480100000c0081c41e9401071007129841c0b4010b030344045c1382c000251200c1015101609003240c0052010820161090f44014118041c5210301c41518060425081041c54140e29802804d841d500d4a0040c1094035044002c41b000c0707921600f402e4205580e8460907100070700704040401e4141c00b648c000c11405002e100300506020314119001100b00c00400f603020f40c0c03030010b5000240840c8940c11100e02e140c0d010790741a40d12840c6030109a02d42580442c030404854a0003012420003621050503c08000c4d8440445620a40038402003022625640000380000c00310f8126500411151030b400702c0e42d0b481060358102034001d1007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 934198911 1250 934197661 934197697
    0x4030c03080c12120601030c170c0a1404060917190f08070218070906050f0f090a080d0f0f030e070545011d010b13090c0206010f17070b030a02 63
    0x2440b11405801c17500035000a00d0541074082c40350045c00380c1c04891001418822455440e060307624030391351144020000b803003400f82084c04186000801440906080e5641d15942480c203138126250201200c4030001641040c0540082149aa14914441c1c0c3c3c004642985c42007260801c2c3c4a584076141000e500b01a15024010b01404000b10280c002c08003566110b4685694550881c0c04d4001d0076a2100381c035104100e0007500036507441c05802d0880000740b5071410341f81e0f110700c0246003030b070102c1d000c401240040d0224004240c0064465519540c282800d02c50a02c2290502d915240203016941c401c44240d600d09010307012080000203440100c503520307503032002900c801e100e0086400418500d01c0d201c520010070480070620b80c3d02c00850580405054507420045034866940002c0d0030504480c5411f200000d49a02900030b5103280440c0c0e802400c119410641d07106203078030644e045280b200c809104034110f20400022079004460b00c607031050b61240c0f60303c060138001c0d03c500214010118205 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 934200161 1250 934198911 934198927
    0xd0938072009090d02030315040b090108060a0b0406031e0804051302030405011d030d0905030d0501140103051012172802150708070c020d150209040e0304030c03080c12 74
    0x21840e1070744031141164190059510414003a54402d015111480142c2003440800d4081c1003400107050348050040010a60803a510003150424000348e0001c8800d81c007a4050008030262031007840c590900c20344040c00f1a60a64664100620900f07100c23084030245811860140310b44041030b640604001010510700100c5041d80001941045d1000da40c15460110101c030030368094003c1c025981c1000001c7c0d400c0091008002c2c0003810303040010ba074940400c004207035201180c1d208140c00f030007002a4040811007440001400c48000130884072210080303000621040e5400c07100c02c110191703c40b00c0e116140343d0a0850f101b0600890b200d1232a6003c5800c1004081c3e21280400802c0080725821544040120806c1e0070f03601c101680d00d40b01180d000c10128105a00c03406a152105002030301d400d51002440c1d0b103980200b6200d0000a8000c0d41c0481c3c180001c2c5480c2c082d620700c9020990045013054110b450f41c1c0800c80caa8800101800b60000d100340e03103a0350500600211340c0410002c42d40760090 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 934201411 1250 934200161 934200203
    0x2011e021f090c091808130504050f0108150712180c030302030901021002090d030c02040e0f0d020c24030402120714010324061412090d093807 63
    0x25000115180908450003162800c541d200360030144090800c4402110300c0d986406030346d540000e040c3d0031075034411080410a40c407280646c80c0140300000820103250702d0000060705092282d007180550840c3c100900000701d521017100050003620700c000184007141c0c030405400c2d07e8a50880140000031100c0c000045c9600440900310290003038080d10a0000c1c0d4401d880100e1080489051740007110750f010b180031a11071205c030310306644007600c0080c4024118524a10b000023140c0180c0e40d65000e40d01420125905215081c03014105883c890030300409000100d411400700c94040c5400c2c20044009429944d510b00987d40c42c100000c255a0700b151503844079590191046686400701c2e00300500c0e10310b1014488076044d4407445d800b440030384039405e1480845490b00314481120590409028000d41c0a051803034280c003d0b21807400800301c0c881000009420541513a000a0354115500e400b85564440007090601048000080c01101000101e1142ca54044d482c0058480824102d070f00040b01a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 934202661 1250 934201411 934201421
    0x31f030c060e011803030507060f020d0b030d051312050a0f080a0315030b0601030f02190e1203040f1a04091d1b0f092a0d0606030902011e021f 63
    0x441a96280b44800e003030001950a0440b5040343c3c04c54071a403541c1040803d10500103050a0361117020b0100d8200c91180c1084180e80010506062a90341c4d00040706540c90100101e81540240e4144a4100703d440241e4800141e11031085c4400c0c851940003503020000d05200803081e00741d0041d070760b124644260404d0303030b03194208442c800b010a01c2c0808000200c020700c0090740c202c83d48410001d03119940e48004401400701140811202d270380921104142041d801510719a46203140c0d10040c82190362010800c0083c800711480026400400042c458101550750300d8041d0707407001500301800070b001c2c2044040da102c0c1d640301e462154581501c240c443d40610942400804040c42100c211500740d071817a02204404c6003142d90f000c270281c0317172010150420002031540251b0190350364140980e85681c4584840040110140c042d50015640000c1c10b564031801018140c1c6184c00c10004045500281410f01101c04002d0000d050142c0700580910801030700c042c0c0b80d0188810301d20480b4012040c0701401d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 934203911 1250 934202661 934202669
    0xc01050405071a04030b1603060f08030a030b0609030a2003010c030c0f0809030a030b0406090504081b0303040c051c0f03180b190f0903330b03060408031f030c 70
    0x3c0114000304a5040d094103030740c1901c3d0000540b168030380301d0f070f00702590001c421200b20080c0358455400240c180041007813140240386c00d030041c550b29100a00010201c83c29202817600c548014840c0340c0140d2000a40f40310441e510480d402d240e00c4811105800350340620464035450f60900c281d07c120303180d040d04a01c1a10604e030700c6105400c144c005003958107050885100080f51310500c240106c0922071380082020003006040005c030070352501b000078261402210151200030000401c5204582d0358008a92030a2150b4013079811030a145e0380754400d0fa00d0a02c1058810b0102e1200c50301c081d007c1c8000a900c640e401090180e0943c92450302410442a0718080c2030f624100038000a4400030800232105c5118243c0805030001711610400d40c0d5605012003004104003003460048001421410300446151070a0180c0383c0351a80e104100441d88038904410440c1401c2090400c0341d9200052410340107030303106000c15107940d0f65080c401020141001028552003409100105011604000100750703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 934205161 1250 934203911 934203929
    0x50c1005010b0a121b03050c120405070e0115140d060b12040b100f0b0d06080d0e03071418060411071103060708060130020c100c030b0a1a0c0105040507 67
    0xa01207010262040303c104ca030800101001010000c580d161091f0303c030544c88110301e00c0442c1064880c1d801d88605002c220382c1116140d0000d0400d00941c185502c51500411132007000d5544a80c0c3c2500c0181241e03003800300707040442000701b504903041c410b0b504108c028180910210340c40380a14a00044c6580d01520162602411000424002e1001c074001d10150f41c403a10703403040712070310300310b8110603c0c0d0004084a41e151b90340d10010500c0340e403c0c080407142c6426070303030f84e1b80400150104050030311001d64007800e21084010919030064440d452036443d03585400540100c81d82e202c41c082400751415100b02c040714040000c0d030340308104648a41090080056088503095a00c0601c182c540300b50a807007084c0466101e84409444d003042c0c0f001c3c85010b1035075640c0b81c000c1d4000d410f03900c400d9802c55440324015400403000700d0b41c0014240b00305081e02205290a02c1003c1194020900100b083e0041c0341007440c002c00700c040c010300b180044a2203550403030002c00513480c0504143e0f844030824043d030070710 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 934206411 1250 934205161 934205177
    0x111c0f090b0903120c0a051509070f06120f0f05090a031b0201090513090f031110061a0702010207080a0b09160305060a0c0c05120a030b0303041203050c1005010b0a 72
    0x4500711035802e84a107480082c00030543c04940329000c0310300340c000c21800c1502d0f00c03420004000141052041d614440c0301c0c01d00d0b9200034202151941d080502d03581142500000305a81080810340c0b01800f000d000750303600c41c002003026801c4025006801844500240d9074101014851100700004441211500982d6a2000c051b40b40841d6004012101c0010f40051420282171100c3d04d000508e220072485a1400040d01490355642c0c000c44c0c00c04e9060560120300801c201c400780c20300a0115803492280044c0801109050205218580c64010341103403c0e0b540103d422411a4020017413407018003051701c00c03298516514600928640000c4820101d5805450310071481e20340341c0001c090680350300002a2500303913110700d80b5000410b40c0b42003110401032000986004228140000c050390750000080030346d00c203a59480030341070303d5540780340a00030343c001c01082040c0203030f10300000070080d8149400e0380da88015040311860800031076281c4a12600c1c1000008030341d00880c00401c4c0c600000e03123441c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 934207661 1250 934206411 934206419
    0x20a061d0a0305120f070605070203070b0a050906040305030601031508160509040507030807060209132f0d0507020f06090c2b060b01050d02160b06030c010c03111c0f09 74
    0x1c10004144001050f43d406201000044007000001c0c05a4452019055040071281c4e150701e02035075016540000542c00004403c410701403041d05140d8840000c541c1400349051108416986081c000c2c00070341000004004190142e100741c0264401c13100440a991006d5140d22500351102e6514908080072034131303a40b00103890308200f44524415078101d00901002403854840380407aa000c0c0c0da0031079040d9400c0081401540e0368800c0700311400b103e40741c00240c054495880d40000c0c04102c641158a007080c0801c2118118010b0890340010182e200c0407501c0c0d1540041a841d240c4c180b0545102130040320104403055400240032582c51004440041e48076060b4260700c8034098031982c44050102200d20f26401050a503001280805010300d400e03132800c00c04070f1000049070044001040c08104540542e0188210f4010198100a045020b04481d0081d0300019010041086008003484425190000d00725414007504042d4401c0444007072103081d145000600100591180c0d40100f800210042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 934208911 1250 934207661 934207669
    0x5010810050709090509160b12012702130f270b0d08130302042415080f041103060c28020316050a0206040b030708070e180c07020a061d 60
    0x42c051259901d5241d140380c00c003a6840d001d00740080c01c0c40000c0c803030303010070554541d20309001c1c5005000811000b902c44003078041d0b00d80c20403810f03881205841d100e804444406a440c220700795008450071001655038010350509038006e00d4681c41070b8600c2d14000b0707000551042091000c08403243d5a40e003211b5074231704c500b0601c003115407121009804ca41c40000c2c1000003017120005240307000006004042056481e0700150580c2e07007103541e50003007041081821440340c0c01000ca0304054980100a0f201144017100c0c01031100c3c1c0018500c6009142100c0800c0c00d000a01c030300090b0764200a410b998007458000844c0005900044001c180802010561414482c1d80030502401c1c5000d030303001d90301c2d00c810a090b200340a9601541980d4501801c11502c0050390b40c100108001e20f802d089940c0c0700e240110000d41000c900800c61800c0c002c040c810982d1546c1d81414403527000321010480c050307944075540c1c14281340c060003900940040d52100085441900b0810382c0c03601d888440c04107581c4040c004180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 934210161 1250 934208911 934208921
    0x60209100f090e06030102071212110c0c090615070303051602010509071503020408030301031b060807080c0714010203070801090b0a291e0301030506130b0f04030e0a0905010810 78
    0x65000403002c4030144100c402c10420142c2140c0020005800c001309502e4241e4641840039a000c08aa180110b011403000c8074000c0c81a03020550304642d050003000942580c84140320400701c0e104002c0100050401e54800082c08000d10808080300d403112814a0054001c090030349190f01a05044064925034030b03c1401924031680e4410090000d99140c48070584403069120244400c0c10740a21000c51520000c00c0036500031800f4002214925000c4820540c40c1034954111904000b510350803c844d0a411000540e0045201c0d080c0d65611443c1d4141000f641c0214445410194000420310100543c81034606050b01e50020003000003464000400485d03001d240f1a0025501000c846941c580800b03443d030503010400000340034680f800005020815200d401c40507038a8401c080014000c1c0502040403651015284580203d422403640351422030340b00081102401c1d084000004040611484c0c00c40327655003001d003011030310686400c2c50b04098102402840c410f84140c845d007041e40e600b03a0081d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 934211411 1250 934210161 934210187
    0x1090509130209061c08072a12050102040b03041a060102010b0f01050903010b0d0f060e01090f08161707170a17040c1e05010224060118090906020910 66
    0x10303505190516400e201400900901d201e074040900c00b00854205c15100d142c443c03451080c070806503159414580013400f600c1c15003000c0c0c04000c1c00715103d10f0200c50a40f10005488000e2008252003007940380c0540a0b103c0c603045003c9801c0b000c030901c010061903c4c41015420a1224003a805a891400481c200c800c405c071781c40c2e84031803408040d0142d54000d03402028403a0700500080b40c1c07984600041f40d519810b0007030403a0840d48828951051090601c600000c42c00148001d00140003107445040c4a41400310020700f100e440001c040c2c01d0f10160100300c8600540c0401c0311410351800c180b40440ca90051201514400600e040c0216450400d204840c400170740340e120f0a011114222405000280c010b00841e4042c0092038086000308490f0104243c40e0081d00f48080f44030f00f00400242450400c41d0a40c410600b4a4008003615142070a20386d4460360030719201c0c0004504d0840c80300096550b50040051619001c040f030b041c071050740c005085c40c1006841540b80c103045c911003101d418a078600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 934212661 1250 934211411 934211431
    0xc0a0804090c0f171b0d0608030a021501030c05010503090118062f030c0c0a0602070609140c010f0f050d0f0609150b0304120e09150108180606091e09010b01090509 72
    0x20004200c40d5000b0300d45404449640742e01d46c100f95042d203000d001c5541980043c10240e00110358100380d10350400c04104606114041d0400c90351655542c1508074140c5d010b0709051207008000a28621000d60099040d00101041d2000102c3c55080140040100f00c04410340342d6504a208268200d460000004032001c0b04ac40c2d500e596203020561100d50084031070404103020f03c45103480810b140f800039024860088000065070440340c54070760460101401502801c2e0040d01c041da003141e07084100c4c81c03400030b29414010a03a00030400304440c544541119040035900d414403418404540364072210030f468441c00704100401c2151264002d01a0600c5400748025041000400007009034074a4010f0048034209011403000034000105c074814111103003180c4c071030071403211000356a0001002307420803440b92901d08101031040c80c0da6103500000300042d001c1c112040124502404452002c5c0070100340d003600034550305040b05a940600644078160740010000c820108091400c000c01c6401507400710 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 934213911 1250 934212661 934212707
    0x1503030304060906020c12131508070305040c05030d080108100902031b0604050604030605060123070f0c0b0c060124090302041815090314041a0c0a0804090c0f 70
    0x26403044083d003026901142c00d0350302840b080140e01000c0005050040c09088902d03106d184046402c096013400c3d03401482c48000f103218125aa581100701241c101d1120301d07000c1590f580e9030900011154483e0301c407942600c41e0962100e503080d403007000741c1c0c141c03080300c070a0320905072510100009440030b02001942c56017008020700e028041542e44a800b040000d0486800d02d69500006000d94000d43e0090b070301d0603140e20401c403066900c03001e407a9031100480e200c045c50460b06e581e102d0a5000b0520010042d91362a0260b4003400541c174103c100409115220a5490780200d011075115103081c45020090001c3c820590004500c03024a043c1340e2a103a9900b861551071a02008098104000342e034081038140c08040b07003c03800955180c07005090215000c10258554500101680355100c64800303135000c10310092004914054209101708040c00c8020b440700c080207651414080207d2008243c5017000400041550460300702c00e0f100c203c2e44d2a10030400c5459582582c0d015006c24101340e40003140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 934215161 1250 934213911 934213913
    0x30a2703090e07021906140f150f060c010504050705241e280f05030c0a0309150513141501170a0204050c1e0c0303010e13060c090602061503030304 65
    0x21401d403c3c3e102420f0310440e0504021880300148080c10080c003a00c01c60b89030f880d41005590341c001c103507422042000b2074450629089070390441c0501e8130501c41d0302c98001a01994119500c8400392003a0802c440002c0206091519000d44c3d2140584941800340a0180d44000b00e0141c4141c40640c81c440c000d20240342041c0740c651130290240301401510084410302c1088403c0510380c820f1440740b0347d04000c0c030740101070300a0050200310108506200308001003041041486848050fa1420a264200460f01800902d4000d030b50618694603000d0715440c01c010018120840c0440300f840900800c07107003810380700c481806510342e030351440080c0c1c0c400d034a040100b00b04071810301c000c044043c58800340d03402400703964001030994600348c0b14200580d070301080d0f05180019191010540001000b441481c2c050040e03407498030b07400144107600380c059490002070902c00c4419a42d4040d11792021041140340c014081c003400680280c020000107202b0000051191048441e503402e551000400071421940c60b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 934216411 1250 934215161 934215179
    0x91c050105010e0420010903050a03021e010c021b030304030b0c040302040c05030c070209090c0a060801140d0c060807230c060901060819060608010507050316031a0d06060b030a270309 81
    0x443c03034041e1b0410001c4d20700040801c000340300b6081c145100358040e09110b40000920080240c17881200c1c48203915000381214081d0300040c4002080c26405100048101800002810350086c0e520191402d52100708101c0065508001041920310071130b400c0100140300c2c5001c44c2c050208540014071003000300300c1d010262421215082d8844920380840d642d100490000c5191001c0551000002caa001d2006214a03400b40396030461b0188183c0f0101c10300400c60302e6141e02c01c0e07000d1107a1424040c07090003098003544514881e140e40301141c001e08c610250320b415414030540c406500481180200c00200314041018001c98044480040044c07096521100890b0341455080400300d81003648e84000080e200020b0080a00c10821038807469180d2070b01c001320500040051641d0000c00d45003288400c50842100000041c40b1010313990030a000c4943c2c80c0150090030345800000407004003008008070715416800081882920f4a00c00c1c140c007005040c216004140010000c01090406030140a8280 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 934217661 1250 934216411 934216463
    0x8040204200a050912151605040b0712031a03030414030f0601060801030209011d0a1a03060f180a0c0905060616080307141e0d02091c050105010e04 65
    0x307885002412162000114402075501ca4024640860008a0f0500c0d451500b8017295414440400181c01e0320140c05200040c02c00c4000d00007011480c0903031420000ba88110305850242000c0c009690740c50545040020381e4100b8000004002400d00c20b24040318000000c03064000d0707002600441c103150030404860380000c401c28a40b034241c41503045d011000d00c01001140e0081110f51581da00c0340d410f60042c4003075444140c00191002c6810319003415000c1140301c00320792000c0f00c518000381c03140780d404440582060100d80650b05214400902c024040100039060185a40c0b000070704139800b0340051551102c2d0803d8014022130307040c08080000c500590411544040000e100ca440c02e6002d0504043d0750342c1c14602581c81400220401040707070f400101890301c0ba038030305503100c1c2084500e10070201e540e02c28110030040504040794002c0c000d07000350113480e005280240341180c10080d039441c0e01204124440300340c445600b44400090000307650000301d030146820172400c1c04a0f107403024445071050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 934218911 1250 934217661 934217681
    0x30706050c1212180a050705100c08070501050a200708071103060403080402010f05031612061d060406060908030d0905031e03040b24150d1104060f090608040204 71
    0x100508070784011110300b620061a030340001e104080781504003110700700e803290300025200d042e03603200141100119000046020440740c04690301d007130800c2350110480d80b00500080051000748007140c51000c1003010f40182d403040a81407010810168214820720114401c1007003120300c0401003102c040401d0f00040140169401600214042d1000202092030a03008460a400081d40788007884219070b403000303844094101518240b811824510302d18941c00d03480d00010800e1209003441c0014074107650300414010170206900842c0c3e54503480c100c104040e02281c0552003503107013050202e861401003d140c404d0f2a4000020b43c14002e050380940c00804518030180c80328802070048032103407141e0b8280c5096a0000009864890506207401281c2c40f0024000c02d8001c82d50192a8840001c400c800d0700501808882e0940581c036070540c024020312520a4141421341080440404040c84c0c100600c1115102d40d2800d9800034080e10890340202203005810006224201107800344c9000d4114020013 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 934220161 1250 934218911 934218913
    0x180f091c110c10020a05070f0312080a0e01180209090105010b090111160b0403020414010302131109100c0201230d0b0117040b01050f12030702060a0c0510021e0702030706050c 77
    0xd81c2008009201c0d4506a00100f0060f800202d8503410420181701700401400c0d0220524001c0e4115520584510500c005000800000c880050700120380f80d0413103405010303c00c00800c40d00e500c04a0042400300a100c0c103a0240c0c0c0004041030b92030005200b068100d0ba22100c1da107040a2000c401115880c004081002d014419102d6054220480c03500010050140206095444e86540306001c15503080080020309001d2002c0100056190728911001140b904480080d80c03811076149000c2a0084101b00740d007150308000341030306003a04501c800d20840c0c00dd88070b001c0782244803400040e1010f20082403074100002400350401c5c030356054100040301074050403d103034403038009040e403484608121029511050b600004018034140350010b50350040c4155070700c2c0340c00700310f0b942c8440e5203115402000380500c0c40010400b0781203200300c0501e00d515a0101c02d032a03054100c3c2242001a4200300c0e203641404d060680320325219955103048510241d8042e0251000500d801d006403080c0d0424500c2c054030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 934221411 1250 934220161 934220173
    0x902060c070f140d0c1a0c03031303031103090d0c061e0f1d06010b13030503041706011502060a05041407170f030313060504020f180f091c11 62
    0x406030610442019103001202d10414620380462100828504900d550159409002c00001300b07410b4201c00d801c0d207403850f036042d1110803a041c01445e03501c50041880d01e1404080180f06000710211181c1006500a99040c800c03d5107401007007070240b105480d00c28640d80942040350286024203110001c09018006c0090300d9031107490285802d980c820310360001907542d158691940f5101d8400d1580105da4004100292441030921582d18103060142e903449a00201c0c07400412940c0c0c06000000d5036000c401c1d81d4455603140f44509082c00001da013802c05000d01400803a0300780307031542443d03039405103a4020040d80d00c0d0910040010030000c0d10030303260201c0c2510105031034a001c010305801803024064860545281c042d0031410050105c141c01c4998100704280420302010075004201c17140c0209001860f5121480081c01541e881c2d0700d4dc0d5000b009200294250003c403114180c8940651480c1030403550351403d040d40c80e03211058811800680900c0800c0ca1140b10f602c90310704480c1c6040880b98 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 934222661 1250 934221411 934221427
    0x2181e041b030f170a140d0b041b090816030201050702010201200721050f13090606260103170d06030c0b0a110a030f0324030602090a1d0703090206 65
    0x40c00700407a0800d99280180000d14000c000b041d40c001d55080061124250034060000d80080001c0c2d81d241d0100c0a40d04046241054484594040d00700c1d11002031003000407008495800030542c070321f110041c1c08942140c4000541c8a0040f66200ca80f001c0341c1c40b400355050440c0d0040d1603507004010b0a0381159a01c5c58070300000060420b21030b585804030360741151140f200c1c2c5400b030a000c1007244280c12100c203694016100d60340207425100d00303140140c1c40c540c40c1c1c480160000f03c0d603466540003403012410000009803032a0045041c4554150081d038081c4510304000c1041c0c840c50080c0310007414a5115101d00307905c4500725018014044107890086101c69584e1603030f03405603030280c0182d400408001290031045400540500440320141c014210b1103500c0e0310041c0c00d41e40c01030f06a005041d228150032054848000d184040c007050a608041d040d074490410000a422207140640140d41000021421040c079007403456404d1000b10342d4682c6a520f81004a0240c41c2c00c21089030000000e2240c41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 934223911 1250 934222661 934222703
    0x1c1e0504030504260703170f0f1b03091e040b03011d0c1507020904150f090203010c090b1e161109060604030210080c0c0d0c02181e04 59
    0x54051400395680c15100c80c10200b40d1204060800c00b013a04045020820f25514900440c0c1e840842c3c1c1c200710b040610700000314213a03002d0706c01c2c0f200c0240c020f0000108a071190080070080c0004000d680c034a001c6020100d803c840d03991188d482c41c164040030010104030701d00d407060006983d9910242022078000c41820102c0e0070344005d103903081d02d20085100b0005944408214040144104031420303485003801d05552002c520032890b01078010035022000409012000d026200105a600410440011103214140c020000d0241c100d11a5082c880781d274009038402c0c6a0203003507070f440310070740351500400d84c09010500f0700c200a0b010a40405014201074082040f44040440b40103240c00040050054100041c80e10010a45441080148000c0c40541c4494401f9060003815060440040c0c4814040c246079000d0740300c40c4030a503c1050601010190b02c400305050700f6200b50b1f01030b045054003001402003480100c8900040e94100141e000c0d404c03c2c0c8560f00303604240101003482d401906e007502c00b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 934225161 1250 934223911 934223921
    0xb0a0e0c032d031603030f14191a0102031b0111130f0902040e220b1603060b0901140d1401270b10140c1c141c1e 50
    0x20000480504803015041118844241001010070740030f585081140350002c40f000f45482e40240c2010f68481c0704001d2041603a1188282d443e1b07003101c102c0645024032520310a40c018043c10900d581c20305d8854580352030424120384c101501600510b0800710b41100c240703c0d403650043e0500480d0340300d4207001c2207000820020154482003c18400005003003246101c0d41c003070309a020f0801c1a02c1000100074040c500444c01d40c00001c0c01544092048240c0001000040c980101500c1e0007004014020303041e01c04020f072800703030b1001d40381440300e92780c0c40d081c220f0203005208480e801b007200c803001c80d040b04501900400c01190040400600f030b00210340303045007400c000d07004104440e0f41003250040c1c8030b280288080d102c00503200c0c00d2240741d5030440801c03e4101211449018006207840e61080c5410241c1920061291242120080d00c00d041004820f51000c4003010301144202c0d0320721a481444500f22514036a00003405000b040b0307403180e0700b002480e58041d0710701c180c007201c504207a40c0c0b243e87c091 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 934226411 1250 934225161 934225183
    0xa09140c09160c060c031d0607050307030506180702030c150f0403050c030d020c0d03060b0a1e11300c060c18100906120905060c031302060408071a070b0a0e0c03 71
    0x8002201024607400300060540c5c587c00040301e5001c142080b04031540701c2d0407a54810700c140b4004c02d15480300c0e030224844090341070000317440d402c2d140101f00001d0360020103043c11400301c0045a1580140501e1020301041c166144e140805032480010b0100380680700030a00013441004aa01d80301031420040220382224440c1c0e07215070403800caa0007003036625002c0c48004c3d02141030201c0c84c20603291409440207208841408010050a41c011640c40c012080441c50045c0344d01030350301c2c00c1804030601c03c0c04c0300d004200c0540a0300e055055100305181e04203480d80461440c0092032581c8903100c6200c80d41e0842c1b460100b5460090400d42240c0e295130380040066501c41e101e0075841ca0a00b8000b0f03100c44040d000103003003d45409151004600001090354100f5516100d40d5500c0d150b0500e2400741c0c0e0300c07412003c0e4100030006070019154800203901403c44251480044500c11415103c08070781c8a0200090244521030340850407401c1194850544000e004007211200b445501c007107403c084500035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 934227661 1250 934226411 934226417
    0x5070806070e030601091b0c0201030618050f0f01210609020d060c030509120a180909050f010b0904030504150903120e011d0102330a09140c09160c060c 67
    0x852407846050410045015010195051064031045202d4080c0003521600807c20811405401025a40298007110103010030a00701004d000114a24a001e00001c0e070340c4044424410000925140130000340301e0607601c4001555144082c0ba20317402e082d07442c00460540300c0c5540c545011006954582d91007603018429400403075894a81040501103aa0080c400c0181d50041030115408584582c03c40301584854103140d40705009200c20581c1100c501d410010b0800d260203404e20a00500289040060703036180c0007030241d41945001d12040b00000d540c0140400e0041c131003031210601c2004441280070f058a80f08210345d80c1c0b600d51406102c000740c0c01102140d00e20b000840a542e000003410903d01d90507030030180388c04552000035902c0c0300350508800c6a250101071081044002c542c0d05010101c3e10041c0c0c44076040501015004280441d41100c2c0c210500640d00014500803442e0340f03408000804451903651090f1003110410740f00c542e40380800900048110002302580b06041403c0d0040c0c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 934228911 1250 934227661 934227677
    0x19060221040302010f060b030610030e0f0a0b2404110903060c18091603050c04081614010309111302160f030e030313150c050303160806150909040507080607 69
    0xb0402074216000d0400601c80c4604054043c8040e001c001d0841380c00c582c4c10707540c11070035041c0740310128020244604041198050b4401d08044e1070300004401102c940544014a03864403040031505102c030010801e0f0034000d441b07410840341f5140c650f0004403008641000940b4000e90440020300b00f46048550302503400010410007000360b44600307494100281503640e86194145028625108018000759504060701c1e1000a244107400c03809440050145074200da500c100101011041080b00740030b54110f6452281d030142082d846800354488a80c0c00814035040c0d85585000d0000c2e00d80070501900d2001c0e000c02200d0520540c800b01100c050b4041c2d0350300081d40e1410300e4010f101020541c6621b00c01d07030041c00701041c1d03045d007041007904517810310841c41e94a81c0550402d8a004900c91009017840c00088100485200d000700105d1307011070a5a140c031401c3c2d80d42c404028a40c80c44000820040009020010450130458001a0402e010300211194542e60f884058a00001124280d000074148 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 934230161 1250 934228911 934228913
    0xb030a1b0507020603060405060d0812014104110403140d030e150402010c0b340207030816060509032106150901200a0309050607051906022104 63
    0x40303280c44945500c0d803409924090040c0c00050490001070401881550342d40042101c658490300f00e403e00c281d1245000c1d80326007082d105542c46807000d00c6000c0f6140040c082d0b00700900000d8032410300000140d030250500045440320700d0242000d510030b00350040e5680e103100148032500f40142c0019803144507800d0030020700a603041d08061003055a44103050608059045800010031791100040c824114624075980e0b03800121210307200114040d00340348500d800e2045e00c03404146000620072040d0390013003460b0040c0818040a80210a007080140c014483c2440050102c10003040380400c2400d00500080040d00c0390400c9410070b41c0c810100b44c3c00000c03081201d02000704413584000c90b43c400c81085151130008500449003c219158039103a000440071801c8c1e000385403515213a5011801702c500b0940c0100c400d652040000da007600030847c011800600c61402c001260290b0ba4860044d01c1ca9159817032003c1042c0f002240c1c201ca0443d0280b05009540195000c1c024a0aa004500d20b545e4145 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 934231411 1250 934230161 934230191
    0xf062c010b090c0910021c11010b1504060e06091201050609071e0f030207151a03071809080d0c02010f11070f020907050403230115060f03150b030a 65
    0x968401e4030300501d65001042012458001600c0c2c1010040d50030f0003440902c010102d003801030040900c0e840005020034402c40f0b5522800404011500000800c031340e0600300c00304080c1c40d9000880c1e10042c10100400e010641c0b140c40700010300c0b44c0c080e02d02420070b0765900015144c9055070780308001907035640c0e0801500f4506020015005001030820501d101c0328400e000c43d00f02e940350300010610a0100f5103000300c1e44242c0c102c61030725404c000d44030b00300e4802161540c040c1401000c0704400040300b20642d455442c02150400855a6a0b101c800b03141c1c12001c0480c000c0d15001500b0344003200d051145c445201c0850240000c1c3d06103035800000c1901281c14200e04807a5181506101c4900900c00030b00020510031601d45c1064040310401c520340d80b00c8038121020b101e6070308010442c900c64115008150800c00e001980080341a00a200d48041c102010600d008640b00c0d28000407100d548204126009170b22010702180610000a400c9403210700f075030400da00986000c1c01c403c0d5a0340105003001a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 934232661 1250 934231411 934231421
    0xa0c030605100e0603070e2107050411070b040c1a030105010f03020f07030c2a0305010506030f0a0b1e150f01050f31060f1106130f062c01 61
    0x402102d101d40314807014540288009081810603004a8000021449550003503a04002c107500051054130841c030411f508140c18440742004015038441c4040c0445c49150a004200790b04402c160313101d08100752510b070317100e10ba403000e4415a1038020980b004943d408484150341c5000444078040340c0d89500d068001131881c107130306050004242c410720040000b0b2503001d0031518582d0700340c0307821001c945450402c204a40d220707a450303400910601c1c10303150b040c003048170a80c0708480c0200000c000b1940c03441d09141d00c8001d400240000c0e230700200000c42c0000e01d003000803174010058552000d078403840280c00b28410b8a003961207107030a40d5455290072031031908840d0741014640a2130003d0410301060f6000851303000302c0c0007002007280d102e6002c071021408403119820758002c0410105050382d82d500301909e001305400d10400082d0406201d210460f02c000b038101c0c0101d40300c1200c189158542c1d29a2886407030942c004a60498607001740c40d0347c04815081050580039180f40c01140840624551400c5903 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 934233911 1250 934232661 934232669
    0x8010608070c0b0c030910020a1106011403060609090102130e040b06010903030813020d020d110a090509030d02071a27191113020703120501060201051302060a0908060a0c0306 77
    0x1c05580b0600001c3c0030081826085440041c0d0591242c644503525401e00e2500f4107240b140c0340c40840c400300000d43c00103000066199510a40b4030a903201d65028058200300e0040e241c042d40300d040400c0c0d05060801590354800c2c9400001410030701141c01d0201c060086910122802003440280010300c01c41c004500d030406c009080084a040c95a03030094650311000f4188102d006440e170f040015034136103096a074400b80d0b0081288002c4001c901e841c160001c84403400e58050b4450700720100d03150a01e03102c3d09002d0012a8029810074804401e00f0000c0d60200703004407189004001231244070541010114006c444e0040c049032817484050107012114514a8085415440350343c002c118500f147d0b40f00050340b60030051032549002c10308080303042d0080d0ba042c804051840002c2074801c1c180c0c845c183c8110306d0341500050003c2d90b41e80e0701c1282640c009030307142c1e10058020340c140c00c01450000000c0041d1542401e18040980c0d40c0c41509050070001c0b100e81224940302e1856a0300320f5458860322010b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 934235161 1250 934233911 934233917
    0x106051005030f040b150a0e0108120f040509070905060d0c08060105090a1206110a230a120e160308301303021e0f0c09070e1504080d0801060807 64
    0x141c50f04150520600c3c10281014015460b00320101c1c43c4158000c5a04415000281078040c1917035490441000000003482a1101c90003a4400c41920340000340c222003010056030760240c141420402008407108000c1c22a0040c01052100012107450705030103020720f180da8520004881146113409003850700c0060503c0d04200040259101560300c0940c080c040d00c0703104a016100c441c3c00d2401c0e0005241c0c1041043c00300001085070780403242d018005c103203824001038907408614807480781c0a25a018100d10701002c0750b11445080c4d9800c00503030085025a1460045852400381c803d6112502c60413508140e0b1000800119103444c0300300702c16210300c00b03240b100502e1207288040c4101d460144000d0444d4944510114806c81450300c04c21100c184c00490060550594100e040d941b41c0c0c40f100c24581c4071042c01000d0f080c0310185010040c252142c800c5480b150440d4150804221600c91003000500301801e042c040426904020403504030441540d0b00d56200c0d95041000140c00d81a004102100f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 934236411 1250 934235161 934235167
    0x4060e07080a060b0d0b060d1410080313050909151f0e06030606090c22031b0812070f05340320010c050d020d110606030a08090d0804080106051005 65
    0xd0300144002c948071703600c3d24140014030314041000a11580701c0c0055a0400c9800d0942e4002d2540500603000d0044d40000100780300680d689558680340c0c0603000a0210415400360300300101e0030314131030481d800381072082680d0b0000a0412000103007181a110b4429003150294030911058044032100c0181010544a40203803801d10002695000c006103604d0081407040d012920310598075041d1031070020070030708290901d2240c1445190313200c4036100c00c1d80c0882600a0700c10001c64880c061200355541d50001d40801110121a007801380c3c007291044900900344802400810000c0c01010030706501e841c60041c00019101010b655a846041c2c01d03a2101d07038003141040007a404003861800269800316141c0840e0188006a48524840d17001600500802413074403c40c2d540428842d112150380e03120003d0342c0751401c40c1d456545404035241509580059000c10100b034200c00907200a00d401805031000641581c3d4034002d940142e4001840341e0b4680405004a1824000f98040d8900624100341 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 934237661 1250 934236411 934236419
    0xf080f0a0305130830070b070503100e0c030103051e06010519080f0114070c08270d030230070209070201021e030609070f02061501030b04060e07080a06 67
    0x612000c1400e0010107000300000c0c424100704000780c080c2d0081c00715406485200800707980c0d1044040c076417200c400c812030300741c1c101d6141e000c20281540c0a054100c9503885003503880c094280c809500140048400c4a45002c000500c0c03044c002040b80304c0d90342d40081d5600c0c0e5140d1310b8000d290034201c0882700450741100100d814545c40024800d41100c1085610780001304440c0e075407689035007280d00141e400b801014011550004150044002030a8020a44400780c2d82e03071608503040c0d02c0900d03004020760400c2085910480b1244110b04110b00b0f43c04207010300385200000101400c100ba074045025030042010100c42c42140301868000c403640e0307501581d4001c030b000c00d92501485076400080c42207583c6004150100d00c00d46c10380707922454034010b04000c00b1010a8110207600129012403050800d400040c0703800e031023603084400903039007500141316a44a0060303084042d503450300300303c1c10117690b803c200e80c00e6602c86c0214001005c050800450600307103080000d0201c8001042da091050030090200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 934238911 1250 934237661 934237663
    0x90f0f0305030f090406030804090921141305030703050a171312030215010609170d050927180610060e060703020a0f29060901140126010f080f 63
    0xa002207010101e03e95181c00c0140000e000b00442c4e04054182c0d100414040345102e91a400050b4160091a4003181c0080b08138080f51841c0f10508410001000011040d07030303140149000d410641c0201e8140c1e41c0781c1c0d03194000b1a01d000c41c150f000b40c400d940083e0100040c4610b051281e990b20014480d0f0626155018000403405801407203200b01c0e41d14a00d0207041451710030b00500008481c21244002c1c02c3d40d59050041613409030380945540c0c610014020b2007950380010300514000304c9920303031a050003052410842c1054442511020405441c2c40384060180000026485041684200c2c40c4100404018a00c2c00c00700801008002d010502c0a0241c540c0000480024204c00ca401c1688e480741841c040341041900c40006000f41d0310b105100e010001d89002c58000300341414030b2000100c518a00e545c1c00750350181c84164011b0a03100051109d00414840c0e680c44003010705200d80c02d45004111010080c1901042030000d0f485400180000807040750b0305001405400000c1521001c910f40c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 934240161 1250 934238911 934238917
    0xf050a0e060318011a01110309130b060d02030f040c0806041a09120c0a1115030a0203040222060306050106020a0206030a150b12070306121a07020319090f0f030503 72
    0x1281c440c00000c00002c035050005858200c1c0540400c009114841000011805c8250107801c0640860111900e03420840400415940c110030700074108420340c00e01c1c2c0b0110008002c462221500300004000d0884005401e0004500640c1ea0703100006d100d29140c1414844290b994020074240e4001074140408108203080b900503c1c0804202030710540c540ca89414074088a0b5a80c1102403000461840c0d15040c2c08504416440d006000056030701c6040b01c20440c1d1240b04200f0000003400500214115442540c060b507130140c40504461071141400700b07681100c06101085850f62a00c5001c24000c100103809030900416003400200540304655000a035140002001006095a1b480c4002894803510400c40b00a20742140f0099035601641d040a0340f00808884410100e42080e074001210641d910300e4102003038004010403400f83d29810801c102060103801c1104500c8140240d0308640f0312030402c0802c52a064a5003802103150050081c40070358039500c540c031105804007041010503004411 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 934241411 1250 934240161 934240187
    0x703030e0304080a050303010f09060e010b0906120c091002010b010e01030b0d080f0309070605090a0504020c070b031e0a0b181305060c1210051315080a0309060f050a 73
    0x4045404040002400d10790b02840c2c0c80040207208038480b81e0280b00000c401141039981640c207494030903440754080000c0d50018815120b8240118004120485158015140008000304400d103003810503000007003030741020350342c250038210300244175400c0e45003200c01c1004450301070000703102e060f01c1c81001034100b00f0ba018500e4103154032506040310302d90306e4584c09400c0d9644a52120340705c0440302403030700740c640044506804512603504081041400786c002c0d41c0640a004240000c0700e410a02400007039088020f0b00d0206101d40d0401003a5442c10030040e51240d1514190703480403466802c1100c4090304041d0440c5449481c0594080072503d0f15844900341e8501068000c42c00e45660003554914071120710b014000340210818020144942002003c050b04000d44400d010b480303059001040340700070310940e5032001c0a004150f66020b10350b0804c000714100c201c2c03100b0106507a241d54908003500b6210803400204084802e115940c0c004505640d0000c00e4600541814100d00021300b403802401c2c9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 934242661 1250 934241411 934241417
    0x120e06010b04120f0204050a27020901051201020d0504030315060503100306201201030204050c0c100b04020d02220b160b0a020c030c071518121106210610050703 71
    0x1c05092002145008490175400b8004111a15100102c4001004d0400c50058159202d800f52800d400881c50000c0441d6002420841e01ea4030700000c100f8000c05a20280403155000d00940000325201c0c0300b450f1285000303803400f09030055104e0013202c00303200e10b8114406006052045c00711008490704288252580010009402421180303c403880890f808401030041000040b078000c829205c40c8000e048a1086e034062001e03840c1c000001c10540256103045085910841c2141d01c07918141d00a0b02e0380400c040d100502d400045180003099070300c581c8202500000401141c011030301040785100041c600c02c0c081e81d0038840c5031485101c01c0700400102500e030703521b0708012541100c003660490380410b2040b0704a0b6992528155869143d4180e03118052500c00e032032440d00882070050658003400e070345402c074040840342003a4002c1944a050034050703500ca60000c11000e0b050311041c004000c0c852002071000031240c540c000110803040c0c000c0c0600d025038032000d120004190072409503800c0c154542 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 934243911 1250 934242661 934242689
    0x40f03150207050d12140609041b08030c1b01050c03071502090603161205090c0409080403080307020601080705010201200711061305041409071710020a120e06010b04 73
    0x40d810320301074007640101030320901800700c02c03da10a400c80645428030102040610100d980400d816800e0340b021298150001c0050000a0000364419a444da401d00d8543d04c01000c01e031120300c240c1c6160007e80e10418183d100311061a6040c0826000b48090102440d25903d0010710000c06c54903030290f804010500001142008405021038042d00c584030740203056140c5030310b851280012641032918124004c205845c1e82801004114000e8902c509100e10081800c0e081c0300c4140070050004003810303503016030180408000030b220200218000c2031650300620b0039505007409076041051a500c80d0b03055a141100c9030f0100e4500d05c01058030b141d1003041d031580302c010a040c00d101c805180f508455028200284104030220100c1c0c81001303549041d20104012203814900c41503891040d0340140d155880a03400300001003004662064031840030090320002011480f6100c10307170304202c1c5c200000c29001d0848410320415445840b00800c0240014042c1d5403406c00304566030700c254000c07840141001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 934245161 1250 934243911 934243943
    0x1f050d02160309170105040201050339040503190b0a0e1603061a19051c060c032703080c0c030c161707060827240705040f03 55
    0x140d8180d400a4803400700030039824200745002800c0c51000d020b9400c05081112a50000e01014440e05110b554180c449074916141e05116220001c00e4448164840500043d03407c0340c1d10031038100c0382d0800308424256481d00d08010806007085140303000310544403408000103004c80d0303401140c2a00035000c188001181c0c040b0805050801c8944450302c081c00c2e02140001042103000d9000460304c03c045413654507680c1c0114100002e00707042c144415141400c41c04244901e240c5900758000d142c080c03200d4542013074100c2d0b03644400d4070790b00803e50010075a10ba85c1560401901a0000c1c13140040ba40c80360369040d826640505800c1e00508106400340d400f01f074400c0207030310410031248007107440c1381190346400e07126078083e9400f019030040400c00341c240182000310340000a000c00590310b00d92a22441541d440c102101c94580341c1e00c000351081c1036140079280b01c000074400846002e100d00ca0b502070154500300c0030100b4402c060030300c80c10003201f0041045a9403410f6828001c0c0d03940111007028070160 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 934246411 1250 934245161 934245187
    0x303150305031b0705040b0f090622020403050105060108061f09080a0818180f100302100e18160809100618060b03130f1a13050c1f05 59
    0x290300300401074403000407403d440d200d000a4120611181c1c00403a0302c0305880300705000c203440403001e110350031003054991501035113020030210368408009007202040c40c49001e0300c4400c501c615101c03140c0081d80042c09006025080c00760303e0744280c080c285028641804004101212905140c420140030413204000546104c0da01c0b0030b006140c900c2c2140c005020a042003419507100b40e4000340d4000721365001002c582028041e1106003c954200da070341e2030ba40c142000706100402407100c011041d00e0080400141c0d503500c04c120780800c8998448249581c0801403050740c07111010508214078030f404c1000b123101545005a564042a031810010a440e0b19403010718008010010b00300c40f0382044000709140d070000d0f250f00306072002404c0c207000599039910200da09210079210b010307201c804140d91001003800f10380a1524a0b03c20010020008200242c2031010380c821380e08600e10718154221907007030220401500c50510070440d0092086030b0307500e00394040d6414410b0354506014020407100d01c0018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 934247661 1250 934246411 934246451
    0x807092108030a0e0705090105030717120a08011e1a1608030103050607081f0515090907030609111812190f1709010e19051503040b0609130303 63
    0x1d4071009030358070307070800c0d410307010141201101203038803446140d030001502d28010707090701d0480300040e02a00c01c450801e0312030200480c0114042e1250320981c40c0c01802e42d08094018001c030842c555400301c840d410700d013801c5403028542032090000d0307410b4072042c00f03020341004032080f40c0c5800d0070305907a541c48040d050902e0f041d2154405025030b580070000009001000c04c829101c0d8260395105201d43c1c0d10100e5504428240a1400d4242105640188594141800c542e40c84d004030400503030410f4280701c00100035100c2102d100000949400e003c0001c0c0642c0c1c09241c4c4041980c2c42d149003084c4801e07a951a240b501202c0180c1310706e8951001c1840c24605014100200307001c80c202060070021400c00d0704d0714000b50304c002c50700606001d100107202410001501c01d00c64050703540e060000d41c007004000c0c0c4101c1500c645884c0d20440c490029070359a078840084190241c0d049040d03140d203850704141c4a180002071010780225125001c002c1210740c00b072420410b241d4141400200c04040c0210100091 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 934248911 1250 934247661 934247663
    0xa09150c031e020415020a03230f3103080f03070519030509190b0411030321160201090512030a02040e010b18040606090623070f0b060108070921 64
    0x42d140b8049803900c0d40c0982c0051007035889611015159602008080b41c2e00c20441e44060000b59500d66100507055900040e0880c1c40640c1c15403d0038140030006100c0542d20440501c5821400441041178401c1480910301140c4400c003000304089196449440880c4600b8025449034840000002d007813501500948030395003c003a41003d074000b001c6c10081c004090035250b000641c850340c0c0070340e0550744411001c4114241d07c00c910541c20b8889580f0000b42c0c01e4400001e40c0d15001c00d2150740e1842074006c1c505c4c2c545070940401d503143c5007020501c110040b801001d140d81164180502c8101203a40001c400d544d81c0b90000315180d50780e5881e620034000340216008001121002c07400003d50350380440203080310b680e50810141c040d640b9502080125920362040102049000000300b08080c022407580c03203620004440485140b5584010410650200e10f0444132051104804014003021034400795020500b820181c41c5401d0419018200840510400d9036001681044560501d0003051141c085 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 934250161 1250 934248911 934248941
    0x109050607110d0624140f300d1b030215040302071203080f150f130e060709060f0e010203160302160e01141c0809011707050d050a09150c03 62
    0x150f090754140b42c5111590f40d020380ca9000c0c03d03240118006101400c0d94101100c0207140d03019240c42c0700c041c0003210103654101d1402074140e48200c4075400d00715102c0130400c2102c4014109c1486400d101528400300c200c50712131785400030418040002d8000500d06401100b14034a841c03d43d403a1715040b0300e44840c0360000444a040c0c80281c20805812590050213141d807900304602e00d507184c1040c3c0c85140403240186030b001c5000114031005042c200201c03200c040d031450000c1450310703800e50348500d00300c026603600c030001d442800c0401009a105015141904051400300460071110000030340c1c1c2c0c05102c600201582c1d11640316001c050007001085101c85141840c07060099a0b01400e441111003441040c640703c015030031100c2c641c94603102c0d0341a80d0194840c10103829486446848a5030465540e641c1880021143d00144c082015401c030b10400c01603a405544052000d407075019100d010700020b0320b460910403154000750700d200e0440c2407035440803c00600e100300340008070054020b40041e003c0b1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 934251411 1250 934250161 934250171
    0xa0f060e100f1512021032030603060606031003110a15020606150a090b09030f060a0b1f0e040f0f020d091e08040e07030b0907050a0e0109050607110d06 67
    0x14044007030f00641800010b001c1004600c0b69102e040e41c0703000031290b8000350f1101c3c0d00c18442c3c50302c502030f050346e0201808030500c0b04043c01244045440c0140658011440e410021003002083c0c5010007144d40d0200c07080d180c603411410707c40001000c0c140107020080040403040030326031164807041103810041610300810f0502c5440104041e41b2050140d910900496a104400307860342140030455141400c0d6594244205150903070807a0341d41c0200c1c0320f40b5814001c4403182580560100106030007800000400500b4848410801c9081180071080310010310503040d141071230316080000044030480564010400c60703118403880004000c651181950b0318800319130800300041d241d0020000a100d6000810704001a8249440241040c000280003400c100300c1403005100058005400025905012408240d0f0100041150f041110701000060001c52403402080e07010405640b411428204001c0c1c50b8106408a61a482003600241120310050350200c01c0d40c4410510701700300f98105204100d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 934252661 1250 934251411 934251431
    0x3718121a010e060310061a091305010305030a031505090601201207020112051302130b04020a030f0b01090b0a1b020a0902041a040f090513020a03060605040e0a0f060e10 74
    0x82d6691050300c803140280301e42d410307030800c5100030b20030082075800108441c09900701700b01000441350310124020340c20000301840a0340128540c06003c1c081c1d031150380615240c4400c940024200c81e00070900c0840d22510180400c46500c45000303940c1c02030b40a20f00194203d80c00751219030b10914644070802ca91040f400d10504a0203500090169503101340d0381e401050f090940e0305025603c06072585c1c660104401d8035417005140420121008540e442000700322905548005030490b04504100b20200e5141c000d406610701c1e07203104100e42c1100908001d00e0641c20301070610103501400d035488040c001d120b030315100360306000b41d002c0c07902d50740c000c000254031506c2e01469006500903219128810b1011903509808800e03407400d48040d900742030411001540381038800d0018000c0540342c0c0c1810b02d6505801341c0561a414000c0c40510701441c1c02183d56480e0900303100403110a0f0500781d003180c000130882c5000828007006004000e40100001c1000e900303202c0c034242000d455094030f9401e140b40a006039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 934253911 1250 934252661 934252679
    0x501050a052116020f1203060a0f180609090302280203061303030513050d1d0402030a0c1103131502030c0d02010e0c090610030f023718121a01 63
    0xf40f140c4034602c0c641c440081810003d83e65003445401c1400c01c1c1e0011050348280001c1d074000385500940042c00000015a60701e480d13005400180c01168044001d4251580c08280354043d5000520a00808000ba00315070f450003900da10040c08003102c0b10f8250240405075204415183c01c01030740040c01d0f00c14500313051208090300d03480c04078210046070915000403041c0c00003200290b10300b90000003811012140c00000c039249190032400e0440a4528009046140c5540c40034510420b403e200002e40701c41d24807409084515110031041c11540100082004c1c110312206030001c44401003031800346101803071000d07421341c050b1003c074261920a41c0d4080c601c140e815000703982d0001c42e48042d130b000c2c000883d00b4050300341c10840e0b00780e40118554403e409943c0c40b07a4003600303e001da4400d005050147c0c0d03843d0484190090044c40f6403102000e200512640841c400c10080100c4604000d41c0b003030b410035030300307087c00c14544203000000f4200000e05084c030285a165041c0c0209813a505503281d03854001c0d030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 934255161 1250 934253911 934253977
    0xc1e050c1203120105040207050d0f0915020a05060108070b0702010e060d230a0603030f0806040e12040f080a12050a0c06050406020703031a010206060f15070b011802090a0501050a05 80
    0x40e00383c0407507200001414209403085843c0290020003909610140c203d003554005401301c5250100510000300090014042e4600c00d1020681d50142c10152607500b0500c0c9800410780203140550401e020400c410110300b0219003801c3d6080c200133460711401c10001d140c0d0301a1518603220306060000c0d01f000c407443c402c030052104600c400080ca40b900c2d440e441f0f9080b5911400000c0200713400240015405014401c40d0340c1c00440148081540030103101031605103840540d0000250f80c0204081c8481000d094481000c0c1c4070003402003003d84510707200c08105c502c50340d1a407018080002200c041142c417404641c10419003010043c004c40c20107160007802075000781400d6001034900200314030380068540c0b1512018205034002e04241c0c590504100c1c00034503000e04280c0c40900c0306241c455100c140c03405890180d01400c0002e02942c9000082607070f8429050f40c1b4860b540c070400c6400d16a6540c01c4544081c3c4000b031034480d031926080302080e5064403541c00503021601d01d10340520a650400d000c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 934256411 1250 934255161 934255177
    0x81816051e092d07032906040504110d06090e0f01090812040813030302030405010813020a03120302090904060b010305060907090303030c050c0f0a020f061c020a05130801050103120c1e050c1203 85
    0xc491440f0b50001505030a41b5007034464140e102804000400070b030324140d00110025a9800d4a15281070300c1c40c80342d902201c580d40d002100b445d4886050b0031522805004007024000d403507009109c5004540c0d644074862181403c259500e0740305401140501a80f0400d54001e0b0400040780b81c1100c6d207a007000795803600300348600303400158104d001618182e0308080348100703075a000d0444202c00b421682d40d440c0320106240c2741020540d013440940101c0d598030311042d000c0e0307005100018100e00404001003c0d20802091280959180010300c440140d008800c1411280c2514001840c110000c204644a200da008800a1880f40f002e0440a80d080071890444280c0708440d95000310a8100611140340038805024000000022065100e5401c6400034220300c5145c1c0342a6141600440f4992482c4020303401074081a0354480051080000c0fa081c4041c00e10f6181c01d00c40140750f066620390032060903466505200d803182202840c1040f4040000e419002001000c42d0744001b86000d140c0e07580e8120800c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 934257661 1250 934256411 934256441
    0xa08030306030d0504060e0d06200304020406080a02030d050703090b0415030b10020309011d0603091b010509090402011805040c050903120403050a03081816051e092d0703 75
    0x44241603c41c0203104441c1102d05540312074208013598003c00030b80701503d0805480300c6d600c03401d2002c030320030041880c3d060805203000300740d4a904150040c03100312002a000044141e2080862102594000543c0d610403215881c02c40d80e1144a45012141ca407542c0e03004010182001c178010400000e040658140e09070659801c00980d8a40400c000002c47c1105140d009a0800c1041c030065510859020783c900c91051b5943d1481c8100c40080780040d4012602c2e51625004020082c0080b0724450300780c000c031002460400e0520f403c0c03000007079032032a015000a041c00031544280702c0780650181c0070b40041100400030040243c1c0c2503c0603106030f02581c000e0f8864040e1411407010011380c0c00644056a400c60000d037404001550306035680c00000e00148044803486000c86000c403420055034504051a00e554149585402e0074456426280c8020020410103856002e1990701e4240b005640544292020400140220403c40c5800d2080c0c040e6048c01c540d00301088502c0750542c119203240b4142007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 934258911 1250 934257661 934257673
    0x30f0602030603160311121e0a2001050405133b060f0703020a0c0807380601051602030a0c0f0e01270612050c0111010606050d09110a0803030603 64
    0x145613107403070f60490f000040951030144c1c007076086030501d11202d41c00c0c42c88500480729400241008058140c001d040d08136081c0d441104640d082086108480a04000e01c0c2ca812081c10015800078000e4065402098011007241202d00040d042c01e8000030000181c034807088660614142e8140c03102100f01045a0071202003c0c280000718400140c51440b0b1400c0c0f8951000e140c44102088010750310400d0a101081504015000402c80c44002486214820701c000c0356107041213900c48221103a1001e542030061185282180e2600c9005001680040c003482d11555410034098002600000c00801079054426203800c40200f018001401040ea48040700048032656070700541104900f0034051144003141d0a089000c00d000d0070f800a00300321180d0b14002c20001d884005008031510021800d640301d50166032480351a5810601201c4209100b400038042e25003000400b41c00c03482802d40403055076655911000030300c400c1260140c45550010200030b01d05aa071441183d07260800d54000b4801c0c0115 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 934260161 1250 934258911 934258933
    0x120905030f2d0f07060f0305060405090a0209220b0f16091208090d1119120f080d1b1205060108060607300909020c061f030f0602030603 60
    0x80c1a141030400d404010b00140c5041800c0c0c2242a140d00115200c1d200e02c100c00b205a4800b401800c0141000e5600c0804030481084001d00b5900050b10700c7c2d018501d44401d001d0509000700b076440045806807603001160b02c85003590b240a402240c480c0303903a004064070718001c00548105050144020f054401515200c9070040201291100001030205155440401c6286200c03d8180e1103d8000c4031100d0800b244d24020980c0e40d0035141d011901801b4140340010305181041c442d141c201403c0340d000031700600342200c00c8040400d0b2031018085402c2000c000c3d04000011046910452442005101c04c84000172404200e010280d00c0001007400315070540100a15881803a01c1824169501c10301a156101803013103a40c080501074070052134403414034880c030090a5202c444c00d1485000160b0201e200344c00189491a541c01208402d801045508000c4500142d426040782600390f110b040c05003081342840315550a640010954849162010144091980030b907120700b02c25003d9540720003207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 934261411 1250 934260161 934260163
    0xa090203010e070f0e040822052701170c03030a05090a0605030f1b09040e1e120406110a0c0b0409050901020903070e10050405040b042a05060702010c120905030f 71
    0x4240120a03013030304104810482c80340d804420681042c040d0b503000c1d180148802856080d406252040e400906004104129038148042103000d00c0c02d412000310308030030b03820400700f4140302d0610543c49080303000304040611940910049041c00402400c5036614a103104001d05540c00100c1d500348281641080050708500507800c583c41205030500f00340309030356060380c00c03c05504080d048840c195402e11629074103480714401c4802c4001210006c0128003100f90f401800140702c0d03942d8100d030350480f103500d010385c01400d0150340070394000d81071290400c1c0e4200d0380d45162140f07803400605a105550400903004004500510039203180b050103104aa8404021a00741e108100181d81c0582c0003d00c10020300d0001203100c0e401c06031040c00c032455250f1314800101580c1040d503042e14407000c1c04040c0002c0002420b044001542400c503450040440d000401200240038402c50b4003a100004040c41168895920701c20040c0e400300c4515281c48002100800c036144a0081c58000c1c8507030072040c007003004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 934262661 1250 934261411 934261423
    0xc030e2808061b0d09030c060513050c180f0402030a0b010f060e010e010f0e120a03170a050f0708090a0c0b0904060902040807050d0501180302100f0b010801050105030415050a090203010e 82
    0x1071803c500703615180351444180020802e0354403d0301005a4400b9120004185000c0c840c0200200900300b80406101c0c10001c1c14100d0072000b0900c203100041441d281e14003042c0a00f94000f074100800000d03030b6114000304e410442520b000030715000040001045e801c450900d088165400c0d9a201d0030030317942d41c90042d10320312000c075030b49030200ba00003030f03c08861480707081800300c02003000c1c000030040c1e000320190901c0c0c010301130b8044012443c19003036111480e03801605660710002020081c03125060400c030509001c0d40261a010130021140d00003001178800300407281d4103d501020800e8000d50750000010190804d16425101c0c07400c0200016502515001303450517280d4080240484902d00f108100c1e0f8005020f100311042c0d501d40380850303080c42000150000c080d000c0e8010b049584441c407141412102c90001d241001407034079603031a0650364003d100605480081c20420303070301d490302d0510034402032108120740100c0b818802081411410354010f104002d02c00d030001c0c4102404408580d4540c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 934263911 1250 934262661 934262701
    0x6150f0609120b06040f060b0a080a052a0f0301060929031512070605031e01060c0f0618110103110316051b010f1d0d0c030e280806 58
    0x148038044030a01044082600131341000d8002d1001801c16055a50320003911a60b610680c0c2840c00410044401904800c1081d4481050801040540f40903040d0300403144036100c180740c42e96042649050304031020f10845400030106180191a5a51141c1c0140309618902800071805c1c500c094901c494202550281814680c2040b1282140d0351240260309141080d17024903071040c85081b5805240380c3c1440b100300030780442e94131079549141491040c9020040c2411020008020500401041d03a012401e0140345138480c0ca032405c80c41c850300780500a401e1100c9200300c88211100c402d410010340b419450003054081e02c06000c2d6500f09036104580d8001100d080da40e0041d80311002c00c125100703c1c010a160041003103130039200070382c0b501f4040c00c441e1702004003921580d85404c80d0f01d1842600c1c110301100540840200b41c0313000d02d04030080024084600080034000c04408100c10340e43c81da803030002e050604961a01c44801d01d1000742c4407100c031501c524140760103200701044a5000c00402442c0b40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 934265161 1250 934263911 934263929
    0x9050c0423181312090f08030a2c130b030f0f1209030c15070b190b04020403030509041a13050613090f030507060b0604081f05060a1403030706150f0609 67
    0x100c0d0035446248488003507030700d50030800401117400329202c0d500301e048901a00e210300003141c65080040000e00003508903120b100a503c2803c1045280f030316134120b41503100909072080e0304500f2401c2d110034040c04081070a268540129424041085000200018442003030700c22507501d00c0c04148500b00c2071081028183d01034201e0710074204241030006802c0240c0043c0111a07162540580340d10f81c2d10b4809603590386802c203074102030f64100030581c040c031010071078100c508610707262455602606030712034483c019004d01e881711010680404081d82040940c02c4c00b0f4041004c1c1002300c40030780e0052070100c614610402d1010044006940944a507420060380114000018180b82d00c00355901d4111a01c22102152610340740150381c1c4402025200900f40c800082802d16041c0c42c6e10181404200c0308000c0309444e00c010040c56030b5600a03180c0807290b40f0150040100d2002000c00e05620500c800a00340c1d0741080b0100c0e14210740002c0e5101260b52030000f54201c0b075211031301200c40084900c41c100031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 934266411 1250 934265161 934265191
    0x303060f0f142803030908030a05160309090e070501080a0c0509010804150c080f1e01140103112206020a030c060203091c11010b010309080409050c042318 68
    0x2c0003030605045002201c0c000c3c00c1140702c660601841404010016001c1c03220b030030b140b07000c10426402600c581c001c3c04510001d1800c00c8031004008103540a00d0703c0c40303100f1640c81014003003890301034a100c0c400b400c04c4900038400a28441950303680d034060ba07c126400502d00d40c0008010304100c0c0320302c203081e1090b95141071512042c100110399120029100740c5900b4107010b480c07404804548107150914040d070300d4080780d604c0c06a10421200310002d03d01041400320842e8001c025203d030700c000c0c1c19581e1904901e5400c3c0c040c040100c00400313000c1183c00018400140c00c20504500b40010400d100300485441121750312164200e8645d03901d010000c0105110303c954600159a42c1c000d90340c0418a41e08030b81e42c680c400b480c0160303002d400c200040041401406800d840744400e000b44000002c081c20140040301c0c040d81d401001d48200d114488001c1c0d582c07030202d1f40341401c00c421100104407000652148112840000b4050024080d07911701c14038000c602001d00b26071800c0c05900c210316001c04c1d400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 934267661 1250 934266411 934266419
    0xf06150908030d0c0516052a0901030b0a0213170705030f031c020906031335030a060b1b0706090b12070306120b150307032310090f0303060f0f 63
    0x4043e0144d4030140c420301c441881007024140e02ea201d40041140100020000a5843c481c0040c080003040a1800c05144610a0f1200d5403146407901d41102e50101c0c101c1d10a9944040503002070140341458070b0101c84a070000101707256004d00f889190f101c00c10a5859030b960350010955280011004d044058000340700300e260a5021411030002410000d0000d484c0c841500000790156000301c44850b40d4598049103801407041c20307070b03100d0040030b42860081d0036070f00300c1c5800030141e14165030b40403d0b4200000000d0641191a0030110041c400080400d40301d410494506031070201c0400c42c81035a01c42d03500d00140c450311418141303044601048072940f070003661408181c00c6c010014018800c0c10344031480000e882e02c0000c501c0c50114003078070000d200c40c101000860303810001421401e1095100a1050010814405941c81400c84041c0040c1c003000c0289484c5091054980030081c0c00c924000500c07083c0400a491410754a201e82d0b001c0000944031604c0c0b280c03226460103000b10040f00342c00148 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 934268911 1250 934267661 934267687
    0x7081c080109150b0d02120c030903040308070f020406121502040e1501090509181203060108130c1d070816120b03010b090a060f06030b0607020d030c060f0615090803 73
    0x220003610400070001c4075540300c00180586170301140c140041e1a0340059011781c1103030031614480e00072046802040c83d504000008503500c1c025800080c00010f030000c0d00104010421040324001ca80c0508207104540d900d0007000301d0b285201106503100b10020180001d40403481c800c88003550511414882d154940f03c100c00e00c16a5214032003418094400800f0440c1d507280c0348280c0c4a400c40e080c400000b442c09404441c2041c0c00384030403c401c0e000034000d02920342c2c0c0200880d40d210780350102d440e050900ca42007490814075103900090f140b00422010402c0b8007001c2ea155442003030380b51140e040326180d0004045200c04014542c1000815022590030720880c0341c0c201c080590707001400851401c00003000545001400d85500303640542c0c0d207104000214a00001030300808441c20100aa07102980c04a00709105004000303106d00b00303401c044010903000c0ea07080920a9006402044110421080f1f60010503940c020890921a09170b0452402c0340315103004000e0345c615901442c2821511a404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 934270161 1250 934268911 934268921
    0x40e040b0a1d0d02100203010e01050f0a0f08032505060a11090a0f170303040b0105090406111204030e0604060504090c110a0b040b010e0c0703120e0304060207081c080109 75
    0x81034416403118000c9040341ca1802c41c0040210241003c1e0250040458001e0b150241031300c500e8960b9401480100a203648181916044850560312212518448000506201b41a400c5005034030511a008240360100002805c20400b5480c9520101400f10982076046500580000d0441c1d105600013030400b91690042d078284401c00d05418104004203001662281c4243c20859000050042c1040f036040764410742c0b1062075090014600d5400c1907100d2543c41c80050180c2801104001c0c04a020040660302088042c00305030650390710740b5811008030502910507502980000c80c02d030007440c894a4440105c40031540d4030340301d052916207017002000c0a000c605000c84203202007804403001c00c61060002c000f881c2d1040c600e14845141900c0c03c0e000c84130040e040b110011001008100e2100c1e07008046954035900740c24078480000009040b03c010f4440f02c40503400b280004140041c100742c0000d04001602c1c0e000c8151400000142041c018030b040074000c8000280c004001009014210343c84 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 934271411 1250 934270161 934270171
    0x70509041b1202131104170616030b030604140a08030403080f010801180b130b0c0c0d030203190209030a020a0f0e0901020a020616140a05190207050f0112061703041703040e040b 78
    0x103035003810f80d00c0e44121314801c450001100d01348c00020030004030380c1c412030112005081600b0200f00c2c1012820220380d654000a0000344282d041351407003001d840d8200001e13401d0660183c0110360305e01e0035180c010300f8400251500d02c43c02800100100d03200c201806400030303642e590502100860916107502c034440e10094200e05e05564a140381c20003043d00e250005220b01214550903a4901000624030300e000c03e00040300f005c042c0b0600520160249018030704a0f613002c1c4800c0540c542c1310b801c00280c1803600c0687c00a60180118030000b90155019204604807030641d2002c2c0041e6a440c0002400e034461200d1040040e048440081d400b04100b8941c041c0b2440c00340f0307001181012a64030180c040c2c0c010000306011680c04201c41c049031440082c07440b50480d562002d020351a1401000ca141c2c6040064006d05114400d83c079032071080b07025403283c00103100f181d40c4892006c0508500944070350050040ca03001004240701c1d50f102da400002290105e94121221120f66551034480b10b4601d030010341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 934272661 1250 934271411 934271441
    0x1f0e010c14010501030b040b010603110d0c030e0f0c01090602060c160f080c0114130f0b0a020702030a080d061a0d0c1b0506010e010801090b060909070509041b120213 73
    0x1140c07006010003482801c1c00380d40700d40d0002c01c90382400d050503e15584141e2003070702010700703004030410b06d071241c1d00a41c3c40c8420801000b003800840a00305401400403504401c07490b11503100482e00d21140040c018800c000b00ba00c07041540390315110102d8546d24119030780c110300c0ca0300304080c4901c0b045141141c0c004500481c0100b410300d0403981e80c801c8a51146c0702c2880c0980d11340498000c051a441e141310f8015580c0d0080000000246e91880018000c500c0c0107018928040006008030300c40c4c1e0111048641e0040079130302e00751580c6c03400500a4011408110190b85030400c046074a6024070071000001d810591441e0038001060743c2803018010b000f80301401c000c026490400f042d4016a01d024402d0302c103c0261540d9030400c2010304110390b05a10050302a0305008810307010528001c42c4640290090f00c8110a5981300e0b00128681111680540e42103840e1004200a110f07001e071005d4070070f0b8890400c8038402d035070f0b420b40c07101c00b510310150182d40242c038001070070840441c1b40d00504198403012 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 934273911 1250 934272661 934272683
    0x130204081609110304020d060504030e0a0602100b33070206041202030c15250b07050a11010207020105030a0911100201091401021305101e030603021f0e010c 69
    0x54203103081c100182405a01022503050601281500d4007400c0c0e03544500300c1500d41036152030b0b00055100000810040e003881c0d0745401140605109840d00100c2c900089e00b001180b540d9400c00035594007040c40c040700344501d4440c59050314500278841200041d18480310410070143c1002d038100e452091080a0040715080050800680b100380150000382544c007000701c0c6200c200d005250401901914442c13140c1403071030920340c8044004003524000321301e01d01c0a08a8000c84031202240708042c41c4050000c00440302000040c81e44040100b48160907980d40122440e404151107090f40241c8400a010032020b00004e038034800d480c0e00120159004e0107891141d0601c00c030118046100c5110f07400c0041c0d44440b24141440341040401a059044030300840c50454584012248500640a0380741f0640d0b1030010b85440358403c158110621821050341f07070845c2801140a0000c00040c40101d0051400c0b80007803c64840b074010b076881c01c04003510f0b00e8050f1f00c2010011a02c100301030b84103d03000710440d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 934275161 1250 934273911 934273919
    0x31b020d080c0913090209102601060503060a0203100b032802161101030c0507050a060903050c07230105120f0c0f0c0601260d030b010c0501150603050a0606020c130204 74
    0x140c01034a800d00b113903000000c8811140c014044400001007500ca0002d041000402c44504161000d0001400500040129a040040b0720703000d02074961006078548510014040c0501e1141d008601640c510074441c03800700d0307a4020481090104440705c00c038041d01110f040002c40b4081081290b810b205d0280180b40c401e5100d54031840130f00e110740545001188040414003940c0501c103481e50360456040050601030a0b5460070f50715414000020032498540000d04105801034082d03800754404e0b0001d498005403291016070031400c1a141c4c420700346403160309040d02d95000310201c0e1918900386664400c19644e15681011665019005c0c81c001c03e4100004201d00585a000e0308402c0c1c104409462070b54900b2a0b0100341401c0f10950549082c0e88a6201e15941030000311018210b03042d0901290341440880140d0301c5211541c00a44103500b405402100c055004c140314082c0c6441d0340f8100803e0b1101c00070704048682c240100e2000d640400200d40300c500d8200e9021800c1d43c6072003005480d141d10307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 934276411 1250 934275161 934275169
    0x9100306080d0c03020d03090c03060f020909041410050606180609031b13020f0301062d021c020f070302150403120f020705010e0a06120f020f0a031b020d080c09 71
    0x140002020000c3c034500c600350704041e41844250b420030110700c1c003401441d4140e190442c003a1500d100c000c140503500e03681080e420701c054050711f00c3d8140c01484170805241c11f04042040b111100802e003810300412002e544420598407840e0300071100500742d00d08000c2403010800c1c500e0400754180f94092814040404030741c0e010080c0c1e40e80701c81c13504203580d40d8000540a010521040785600c410041c010301c0120049041c07181a00c1c1100ca4620b44100301a07144640440e4003400303002c030660701d071000080149140d034000840c040c000346541c841400030342c25818126201c10f001c0d50403110715044620100050f01d420f50740e00c40c080c1090070640d8901035980c3e40304900503010b1000400401c40708000c43c040c0e2901031181100414003030a0101f10058190001880d4450383e000d0718007801030b01002e0703500345400755002c641c0004123440704542d80e5107400a4400070b40c200010a10010307040400550450011070404440c54a95800400c20318100b1901580e41e281c0041802442c050244a4039140780d1b6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 934277661 1250 934276411 934276423
    0x20a05030d030c0e03061b0d060b0a030203010311010c02030613150906050106020f06191116052d03030103030309150c0f0f021507050d11030103060501090617030910030608 76
    0x4207602e002641c100340301006060610703803580407032107030708240b080045550714503145201c2c039100070107840d64406c0000000380081c07e240e0031440000401007440702c5000e40550046050b01c1c09661035004108800b8011110901d0380080203400d500080089441d60030704000c441201403291582001d1441c0e442c945c2c00417100084401e0380c0d540d4890004100300c0c1e405010a241001e03075007000e04064607040707a10003d00e020403c29424140d42c0d81d10320502c008844816540c200c0c2c08054140201074050034060b2707640c001e40c01c3d0014281c0701c5800010324450b44042424601041c14050340c00e50b80780d9103007031700141b0012000307a0713240350701c104410204401c0e449030b4000c8403500e0325030f18101058400010011a0030403105001d5600045d2114100e40303591140b16440851854455131700d220f04940e590207015048910300d0322180201c008820020740740c002c14103a80c4110420004240d491814a64000f030841c0010103a4004000218090811418240702058503040c0403079071701d0380e41710140c1c0307454 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 934278911 1250 934277661 934277683
    0x312031d1c350a05070206133e0f040c09030809060f04060807080c090d14030c0d1e14160c05100e030c09061003051e01030302070e070f0c0b04020a0503 67
    0x40ca0b2407080081c02200c038070070980c2041d0b40e840100700e0351500c5910104400c0c038151300688240c146401c0302128588291052100400b0040703100e0280358000c400c01d13181b50304049503a00c1900f0545070b035002c50900307104140c51071100b90380c1e0000151464403240d07a541d00114000e50802800c1141c1106000c0f940d0007403009115640d94000507182034540140300c9400a0112651102d08202c024841c0c1d4032002c0350a0b031950000c80030b0004401c05e055052031881103681000ca00d0042c2000340c6011a00041546c00002c440f06021058401345030046408208007203000b1860303e000d05c01400d00a902c00d9190500303d101d01c240540042e01d600000d01d00003808210705c0f00040d607580b403078034681c2000c0c400810511005e4500040b6800d00b040082c031156403803855402010394640005405c1400c5082542c041504a00040c03510b5849042c02512090385000b07a228015034032010844051080080c607a98600702ea031a12484105a911f4400d115006030003643e008182500201c0c840d541840510490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 934280161 1250 934278911 934279007
    0x2d0e120a02030414011b1e1b0315090b0f041403070b01051804031b080405090c030108151302060a0c0b0117190503031f0312031d1c 58
    0x1451920507071007841c9800502d13240c1000310300c00c0881001014a0368544000384c0c4841405000c000703441c8810007680302c690380a400400c051100340708a80c0300e54849000e490180a1400720f10b00818080010b80310f030702c80c00030302807021100021107509005601b290405d10130480c115029072000a41d0389180c01613801982c20f800b4590040125141810b0072480000d12424212418a8030780c03009020088004070102d5070038103400e000810441c1080840d00038210040c809003a81c05c0441c03000c14a0f0304240a140d10318402d11200702e60001d50340404c144640620b000d4407400880d1a400d0084e141c010b580318109010800201c080007a40f411881d034041c00c03030021040b1149500c0d001c2289441000d420380581e0b070500d00c5c10080412004400c507940040120859201e01040c007402c066044402e60024200004203940350110740d6168100c0b04075074141801049071180d640c8800d60310764019111591119003554034000c2c50a005900f060a0500b030313141035065601100ca5000025240c9420100b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 934281411 1250 934280161 934280167
    0xa1502150a0c0f0f0801090b010507020d200303070f020f040f14090c0105070308040602030c0f0a02010c02100501060807030504081b01020c0709060648062d0e120a0203 74
    0x5860303010110280da88184d140074600b003c074080d40070f003038204180640c070f1140341c07203180d4040c0c4c03a40600d044400440d4040e001d110030070850306004611000d07112100802c80c8055034280b00d20314000064808a03504040000d0404070654200082c3c44221400d11b038001c2e48445e8512104d9a1a1080400030f40750040c0c00c1d2120b1400c020714605100080005e541884014405c503400b02e54403c100d1030b0301c29803202d001a80c0e83c80d42c440c00d81c402d01505003000241d00c8006001043c03a50706400c8608054011f07002c54a52914516880050340c400740a42130008981200084449100e904080d400600a60189150010002c1d01880403803650302524003903034000400396804601000007600411703007482d080180c0340c1003040041c00303004025903200c01ca2850035440000040d41c1241c00c03030b0120301082c1194000da103040c0486150f007804c003c00c0d9166480d012038044240181588202085c102862205001e90b40f520543c004140703c0d0500aaa403241c05244071413105558010034007170105400940d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 934282661 1250 934281411 934281431
    0x5341202010e0f010e0d08041502030705210c0703120e070b130803090105091e040536250b07140d0207030f080703120f0f060b090a1502150a 62
    0x124214400103003040d03c1e0314117442401c2c21440400c045807413000320303d8510343c07580b41c2d401c1c400384041c00d403c48034450314030000901c2815900324008101d0b4000f401c891842c00c4419120104240004881c01d402007101041031000091040c005400c949200c01000184c2e02071520700d051500c10183c200e05000300f0300103248641407041c4640c8000070600344000350718113081000000c105014034040140100d0a0211004440c01c0c2d02409000202c0d02030700402031480c181c4910ba800400c00706e40303001c183e01d40207032031a0a03202c0200c80d209001d8490009251000b0705141c985141d00480b010404451001c8201103450000300006000300c902900d0f103008011011801c160602204560071020343d48a00300c1040040c004091066001d50040c00c030b140c0b5100c80b4203003510f400f20b20090000405180c118103030000c2e1a594026103003a59540800c00c003035a15000042110310400300700780d44c45038820380c041002e51510880002c90203c1072042d549200d020710009102e07038000f41e80d41d18880b600d60301620 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 934283911 1250 934282661 934282663
    0xc03121107030507030201300518010903020d0516080708072a0317041502010906050604140a02030405070302100806040507140a110f0703050102070b01050105341202010e 75
    0xc40926456405410001e2855459664030b2005102c020305205124040304807164280c8040e00b1181789581c0150244600310122500501044545610100c18030415425280051041e0f8003036950680041010281c44402501d164020018035898101d04984900024030b0203006085114401d0715056150303166494101c191480e10704140a0741c01050340c41a20388101002a0011241c110100c0c11403035015845500c0c01d481190403d81c81d00d502007074802c0615034150b0004c44e4503405200b08000c1e54490344104020717500c42e0b4040c3c0740c1016092004c90b80719a01d550003150064403540894040782d9690740480c8880f00000086000b040c0c10b0001c2200300e040a009030380c1c4c008058989140c41943d1160306201500442c40318000f08031110100b42c0d0380c5102003080b51000c400701d0048502e441d44d645000c03400b0394880c2030304980c0c020105c0300000e41c0354090000d031400f294074143d024804141c2892423031038240f012111a444400103070120070200382d4591081d071102265034004170303c1c0311070f8681071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 934285161 1250 934283911 934283927
    0x70c05160602101b090303030902011701031202060c03060a0b13050a0303080a0501060822062403050106080d1713060603080307030b030c010e0d03090314012f03060d08070c0312 78
    0x1614461340401604410380d580680c14609496142c1800154040d00b400100c80980128042284481d400700011081c030000060100c7c100106500f2181c45655040f0b03260713407a000c00e40e1040c3e000100c90390207002c00c3c0e0f20304015004d07154540d00140d004c03540c0d41001881903005c17584150003003945c40d000e20469034800d000d1280507001c21300340844642000a80144c031492070481480c0e001d141000301104200707070798000d501901c1d901070b0707140c500c000c2c0483d86000000540c03104a40035840d0a9000442050224880c0c030307200348070346944a0710022080c454400075401468491150341c02d000b1800094030364895100514000c51031640c40c1c0c5031510015007155a070808451007070303201200c5201640c1c0e01c52810018408107071401c00f0040020310303042e10740590a800080c07000039200d10010b1600815030103400c0001d5550f22011003680309840c010010031607041c00501402e400c00026480d81800500c1d02130707140c4a5a1603074a060b02c940c4a1401c0e42d140360300b007103c0010381400c038006282d50040e24 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 934286411 1250 934285161 934285181
    0x100e060d060f1803140412080702061c05060a0602060105090a05180118060b010e1e0a0902300106080c1602120d02010b06040f0e041703180d03090b070c0516060210 72
    0x1d486d18050805d04000c0b5006600c0400a024800004e1004c0464a50303100303031030798036200c1c2500c1c046070888000100050b1004950850140325089070008040d840002c090b1704a80c4040c0034480c0c1c0f40c5586a060010300f2005000384500143d40d110f801800e18240310741150002050140c0105558601d0031000351540702c0c08107410405000d54501056940b104544e02c5100071024404040c1c641c0c402043d403c43c5c266010351840c40c40820980600c030381d0014400c0940b040500c07000385c01c00d0041d00d2841c44070030030300038640000c101c00000780c000583d40004000e0384c5101c64901d11000540c0c0e00090328a04c070b00c01070351003c1e0003079004d84d030055070240600051401c0442c7c4007400c15080048d9807510101c0e5210302142511004049014406000080309040b00784000b116030340d2400502c04a0541903c80d0b6020903841800540c0d003070913101344907058040c2c0c0c0c41403841c80302e03849039041210054011007042d11107020703a66085c541d015008001000415458000c3e0803103110299001307044030402c5034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 934287661 1250 934286411 934286447
    0xb0703050a06060806040903440108060f0405010b060c03070b070306060507020411070b010b0310060f08070f0210020c070f050a1415040e0a060e100e060d060f1803 72
    0x1c1844030130b40214505920107406e8074001141c09550a080ba0a409800d09203401c80280c2c40d01d00e008081078000015894420482c8440c2c9032101d02e00522400170240b1409000350494008202d801000718078490b0860300500000c41e1120781c41c80001d2481d80b2004c0740d0500d40d0302c0041e01c101003010981c0c105d540842941030400260345060405400c2f403084c044005d100703503541c03d082c40c0c1035249202950358603500003060516640e10741c50402e2066000f562600003240710b80900040c000d11130b21a02c1d56601081d6a440e071540c403002801c2e40c4035040000c1c80015401041100c1c0d90781401440a400c858040d80f005103074003447d105c0880b8000e06560401400381d25034031014010b42c80e10030384008207070703070309a58601c07180d10109018282e0340240c1d0082c0c2e4842c9038280034071000034107a0b0040300540701079844070001911030000e40ea034141d0140c400c00303101c001c02d600040d0700ba21b08800c8200c00c0500171040400c0e03205188c21101e0032103e51300d6091600c3c501c41d804540500da0700000c24005000010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 934288911 1250 934287661 934287671
    0x1103240604050405030f1c050a140901110d0203070e120c15070b160504080a0f0209010b070f02040f2c06100e060906040e0f101802010e101b0b0703050a 67
    0x1840352601c911814120190030580051800400110403220540b00300b0a01f07003c1101d03041910000c40649014503100c0c2c010701c0e000700440e030341c0c00307042c442e45040d800d074560894901440401d9000103904024024070a0058580d101440d58603032500802500c000711014001740100c150400402602c01d000c184a640b0f000c0c040003000a29080e0810341006060103015120b030501d020889552195400600360360249a2130b11040090310200d103d103da200300c846110a030713280d58423409103026803800580092901d0102401505041c0d01502c0d4041c2051070114034590091a050700000301382014030296203605809800d100b0b018041c00c0c0e0082d51035034141c500c40c0d1034002c05015102001e8005031050800e0700219586540381c4e030041e01e1980038601656179207a6600c040584030381000c5034500d0300034100030f21421105800007118400d5076050316808140c2031050b0034031411502540c0f46000384032a1156548080c031568115090403031040c0044511f03894020001400d899002d006d00200320b00700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 934290161 1250 934288911 934288913
    0x9011a1507020a05150d0c03020f09130f1a03010b041103240d051b010302090d0f1103030f04090c050304020d0809132f070308040f11032406040504 65
    0xd0116030031411040c800041d10340d8201d000068840c22694002980700082d02d07141c440e0200c0003009010480c161000c100250400b00d901a0142d1090121050156000f003003140781624140c003030b040c65611118400078450000303c00300401c89400440d04540c5e40c10002d00003500d031809020b0b4521f8604256410300000b0481d030807a044a02000c4c00420300915111584400301100d1440980e01f81c4004002c03443c009508d0400c59101d8100d2646100300d060b41c5079040400794080d0003282c03a078403005850004444001d4846e031750300b2110300800b15404401d0141407840b0b42e40400280c07520140700e200880d40d0f1803a00b42c0d100c4c1224000c010507000c0c04414010031001d07948403500c50380080c0d000161640d41c0d0007224001990130000c4012100c10500c0c00d07402d05000004a191640e5510b440d01f4040303081c09211444289a0040000060001d2500d60008000404407030307031224440e03c80d8400f1001c002d0340702d000034200f0030100d0320500c0180b014401d0140c03440d1010340e02604008159001c00c0b050500d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 934291411 1250 934290161 934290169
    0xf0f0504060b0909151005030403030b0d051209030319020f10110304030c021f0e031e0304171501030302010c1713120e120715050a0c110117040b09011a 67
    0x160f01100d03407199a89400017003007070107250a407101e094001001000060720194019100750030941e0140c0029181000301240d0342480c8000e241d141d60450004c010b403a000c1d05000300c090b40402243d41d01404140403020744802203010740f401c0164990003a05920710710501881c540700c00300c081000d03068141042c00070110708090032284c215070140362022000b11180049400003031074200c962484111100e00c4007003580d00411a081060045003980d0116400300c1c00d04403043c10004100300b443d00704200400900f07203004480b6401103405410783d8042c0810805030400030300c09900a4015075118200c08000702e5004d16100003c440c0c1c80d00d442c160f802c10004040c60441d1042004117020780498091114a0040c02140c130394040c0180b0b07049030103501c240aa500d0300701c00c0c0b06e0b8030a20702c56524106000390090054030124030b41c0b030fa50703240310704090384800140b14018402241400803040290f00d1400c03003649072034499400b5030b60394802820280c582d03600311070400c0e00701e40c2c681c0d50724111041207a407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 934292661 1250 934291411 934291417
    0x50709060e0904030c020d3516020f0a060e0a050a0608370e0d0c02010f21050106030e0d0306120b06060906161103070f0b031f0f0f0504060b 62
    0x15094600701da49a4444c13a0030f41d968071007034a019500c00c221080030010803071890101c00e42c0c201c289440c0c5502c507c02e8078484602e4814407000e045820b005100300360000c0341307a8005207d13a034001800940c510100c0301c0480c00c0003c4a4110600080b8031181d90760803401d00200c480010042565055003561500034020054000038141c182c9018040100e502e6441445442c042c8001e0022182130407400003100c3c000007013110dc040c14031103000d20900301d2045030007500c418181c55010b0f151a070840c1c00380081110445403403000c0c0360080d00710b10800340700b008007882541d01070200d903103000440001c42d45c450303032511400c6020303202054101681071140e1400850000141c035408841e0b407180e9204d580c0081c0440c018903030016001280800c991721494a542c003860032050050004000142c86003043c0758492240c0c0c0107202031080c43d280d042000030303070180085500115000301c0480c615440d401400018071154422815901f0740c250a002140d00c036401071005010458040222525000045041780 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 934293911 1250 934292661 934292687
    0x1401051f03030f021e03092403040213231509190f02070215041a0a090e15090c0307030f0e0a0f020303160f06050a1a060d0914030a0305070906 63
    0x402200300d43c50340c441c0204521200115050703041501c500003144003c1e96a0042c0b006248542c0c25012400303000a500c448203180d600541001a01e5036640f5001d0200c00403c8807001c1113019a00d16084440da060070030101800c09050503c1c6155003403000001d0045e07a41102a00d100d010014140465125540e10f01c2080c0900130002140c0e400e14415000002e000f207000c003a4110010800c0c0e82c0d52071002c180100300b55202200c00c41b5080c190400c44400d28065a8130b4400840c005140c10300946c050000066070000402c0e00300404107007800c0101d03d241105590103441070f01e020040c4102a41c1500030305120707100080041000d2544c0c04405a61010031100141c001100d0404050070b54509000300d5845e80c610020aa0005a40740b4004190398605c1a0a4401c14a014007040320400345000b41c2d030300c4041e00044100100c61f030404000d1190301c06402d61212035030718905403000a0075140c10b10103590210300079644511114202038141c5030020301030000c0040f6004103014854100c2e00340c004003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 934295161 1250 934293911 934293917
    0x91a1f120513230f15151302070302010501030b06030a050a0b090a0c24030606080402121c050714160b0c010f0207081c1a040504050c04091401051f0303 67
    0x1d0b4403a202c0b500400d8101d0400504480e840c41400c24600c0c2c020b41629840036641002c582040b4403040e541522404418146202d0a06440205103411503002940290360401001c0003400c0c000c0b10440d000300d84c081e6600700c002d81d460b10010018403400f0448194490b4041c0e002e856002099a102a21090664001440300c8000000f14458039420008011910350203035840030800e84400840007141460510008440008032104003418401c0c007850b42140d200b500c8800103612241e00301714000d0051042002d080c81525040c040141056401c4404030020707442c3d441e40c03207050382007100c0002031001017140f03a40d10008ac080d8070200146441000c4403004610a03440c1c001150042d40500841d8801c105180e0000c100c680074080c050000300700d5000303000500285400c400c0440340960341c4403d0716085440120903c4100350038076402559116201d03800303603070700500200001000c6601016054810700a160821440701200b44500d9801103c806880401d04030441107d001b00c4299000003020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 934296411 1250 934295161 934295171
    0x1a01050c010e150f090127022b020a0504060b0a0c050a050604030e1306081009020111030a03060512011a0103020714060f0a0b0f13050c04091a1f12 65
    0x40c440302907000d80c9a40210005440380103484a581a0321070328283c1d540000c42d0003003008941504030502c2540c2071940da90010681e003103018982c00c5181c02a1100c180e8005808041c604484c5d21003c410698004d0303620841c405902c0d007030051003000f0529030819400b17145054010f01100d08114207039907035181c040c54043d0b40d0f002240b9003d420320400802c0108280b0654050000305500b12a541420040a0710307012010086000d40e407041d11054403480e8400d8000c0d081910045002d40c011110a6006060240d118a070f02c070000c62959210201840c002555040d0901a900d8804603074460115040c000740a801d80b076076000094412010f42450600d58005400c41c1000703543c1281500c1c2003082c800b41e034040c0c034000301c040c086600b0884041101e9072600c0c00f000d100e45022111826000800b40500b10140b0725140300380020030004d024a922204144400076005285019001c031001031100c1d00201803090a060061103400c2841c00e910120001004001d03c5034411006129080c03d030f00c02145d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 934297661 1250 934296411 934296427
    0x1a06180103142e11190306050f040c0e0f0103060b0f0d11120705031e1501030b04180602070c050a140310020f090d0606080114100807081c031d01090201121a0105 71
    0x4203200d1404854843d5859071401684650144c7c8002c08840702960507600b000c8010081008a80640c7c0400021490000241d50301d0304001008005251040c107000580302c2c0ca0b403020a01c5030f0485440d102005d0b00001d2440a20303000c9020390010480084019811700200d902c0e81020300354010007903410804040005040b03c0f180105010078210178a100a001d818440d552a480e4100c642610b40440d040c00440485424980702da4000b0440702e045003034400702999180c10103907008070000c1d1072981d180702c03010410759143d809290084c10700f030035013110034400801414286102c0e95944410503106000b01d182e419000700444004000c226209a410f01181c9045070041c0415084189598a050fa000b4104114a04680d010f01b07504041407105580d1610060791754070141c0502140c6800070600e18200850300010313611041014180460a0324101d07a49201c1c1000345402042e040e0346403070f48034080d940c100b412180c128280349024800c560010140b03001040750301c00154100000014880 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 934298911 1250 934297661 934297691
    0x9202703010b040906051005090624130602070612020a0507080c0a150f05010b0a050a0c0c0302090a0c1d010906050904062412091a06180103142e 64
    0x40024000510130080794440381003030002840101c0d00c01580c0784103403401068900d002494288940e0004200049020600c1a111f000140d01030b80c010034400c06010400d19a00c1c40100c0300d0250280b41d00501409282180c001d200a10721503d540c60684100100d0400e66840000ca074031003a0410035855640240758184c518005103140050540d41c9640310399a200031564210703401014000c50140880e0343c8504003c40e45e4818000a100403034010083c1c04c1b1145d010b10750b41040c09028203401c10340550780307401041c1e031504200d85c007801c859603a1f5490f031210354100c410043c0c41071101d0307005d4403190b0804c000070b029480207010b5207003840404641544203558035081907014100d06c40c142d20ba9044031060500e20035000d4003509003c20280d030b10180900b2814400c04544541008010841c011410741020000c071000d0900c0d80c200b1400307015a90120b00010703495002710320031a16808102c0758028081d0800d0f81220006d25440c010304900c6118411030700c4082c3c4000c0d505000000c1e9080c14a03500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 934300161 1250 934298911 934298921
    0x1602030c01050c040618080c0d1728020a050a03120b03030f180108041104020a03091e060509031218160609030201020123070809010f02040920270301 66
    0x320550b08040400c407061112401420890384c0365110602a664030100c022200000c07401111500c0e84454403000c002d20b04082c0019440d80140c82c0301c1e107040718074680f89e0f00c00d60110320301c120216003003007011b40039201c0b1502022107100d15101400c003080b03599541a448402e44100070701000312a4840c50720300f0815030312a41d80e0780801002c4036a64040d0464085e8150080e914903034070701030303448541d850075406580c0980c440e50740030381018500c00f020001c01c802900003501030020143e5481d1074100080700003402d211202c801c006141d86100c60341c90450300340c50000300001450b82090049094603201039000d150480a5082318050181c08091440d24282900e00c01d09050710300000c0004405400c00018401e890007a4001d00881c0d01c0c5104c20158842d506d003034203295001d9880020f5505100700d00250f00b00c0d80402c008299001d0080120069030455000004006d40d00c00e42c0391f0514080092001400c2c40510700e550600b050344415940d028041490304050320714a1004041e9640c0a44c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 934301411 1250 934300161 934300177
    0x60507020f010c0c0c1a040b0c0a0c0303080907090c0e06210403050a1407020607020906010e090c0d06080c01020303040f030522140103060e010909060605030a0b06011412160203 78
    0xc10070503881c882d000f407014040312025140f141c2c60150100301c186c1d40c1825500f20314070140d1400c1c42c1c6450101765400641c00043d08910501840c1c0011001a00c07245110b0000d44c026901c0350007606081c40010700708002c681c81002040d10300308030503100340c5d000840000c850701d00304c40f42902c4401030b4803043c16000c002071042e594002150100300805400c00b000c0c10305030a45958460192011004460492241c200003941c043e405110040052525078030003a4401c4c0107141421034a601c1c800030480d905404e0b1910315805102003100c16102019105507001840c8040c020a048154440080d40382e22014001030120918480c1c400c05060060048604030211008098003198006190064035185400b403042095642e250040280d80300b4080c0e602a00c8100303001400d00d03442c100000340146040001203803034540700c9900203126030b01405005880c40c054000003256141200004013015076482ca0380a00f0ac07010310890022039181c2d500c1541c8175688000d46240d41041043c01d07441c3d4007030000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 934302661 1250 934301411 934301413
    0x210021804090b0f070905030a0209190501060f030b030703170a0215070207090e16140411120f010501050429070605130b060105071e02040207020a030305091c02010804060507020f 79
    0x34001d010001e103500c209200d2012840504005e4641c0e5000b00c807540310034400c2940c10b501029209015103006842c283d00909030180c18204000035031a6503050307c809034480800b140070305201e030b0301e4280c00d03003d409880c0c4400c5029000b40ca086550f10064000340008410064038080307020500c4900811a00c600701998240d01851458880b00c000d5540403d0b0180454150030030a01000310400041c0701c00680c180780d40c4000803181442174804a00c01c414864550040c2c45906850f0300803104001010148420300e00c1000514060251a80c006010b03844179040040c03c01c800c10808030140342190f44121047c1011a40b041020308203600d0780220074016009515000610030f0b04081010304022142c03043c50441041c1da610360041d20075008030003020b419076502441c2400703080305003401d240c00e01c0c1c4010300c01400c001c0700e42c0204030340080c00d400843c041000028040d000d490240741070f241c001c05c02a480503046001e680005c2030540b010380010001c0703031524040344056000303102800400008030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 934303911 1250 934302661 934302671
    0x708071d0c0d091e021516020103050702012315090c0415090302090108010207050d02030c0c0906030f030c06070306050a05131509050a0c030f05090601030b0a060f2c070210021804 79
    0x240b0102c1d801345190104a1080a035020082c00120742d03002a10001504120004200e42c02d5400543c00342500510b20802c41d50784e102c00003501d2212409202030034035000b208203554a025031400d0b0b1080c030071944151107210705004002c14120349008542c143c6803c40320741c040d03a42051724240d402142c5034000a40c418400340000c500780314154054900c0602403012641804156401a84c0fa8030810b43c190b421500580440421070038440d42d2940c00c0040501160b8079164020714107070541c3c0082e418040d1a070440f000b880825079141c001c64000c0c0c40102c840c0c106052402d0001a8405180303103203250980e07100d1207010241e134140e08141000b0407007075000384503e1401d41d003000010301079041241c01191034800700d075141c4641841521311072603040b0001c064590071a1290100d41074018044021252140c3c000f04680340c01564040040502103a48200303e14200c4911a41c013110400b0f425111251804004046030300113110646072154002c0160703501c078441c18404084a6840e0901d41283c181 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 934305161 1250 934303911 934303943
    0x206100b1b1018411507020a0507080d090e060f03010c02160f05030d112407080726060f09040b0414070f05060a0903060e0708071d0c0d09 61
    0x1020006070310340706070300c1200c200c01c040a80c030198220400a410598503100116240301c000658074002000100c0d04a8104e04c0d6088854121005c0032a49080180c0080c0854420030004202c0760700902110005008440a40c0f100180500200d00c2810080458040412002d4a40208400c0d16040c058000c0c4000c0d054000040d5403001b000d4404005c102c0902e030300040d02c00402c50880c098550007405000b049203908822218141c48442503c0107020780300261004416820122030007401240031261907207001100a40f5621009054100f4014880d00c00352600d4030003102c00001141e09403a071042c03922410080b800c000000c1d000b040d0403c01c4030040c0802c2c4240000918403c0b4803520840c60242141d4450540342d010303511801c0d070070a040b00028030141c1ba05101411602134240351007098079560f6113402d000e5414592203020b60742c01c108000e00c601a824031206c8040c05d81d4940182116480c206900759100b8020a20520000049006031910035103803c060186a00300174003604035180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 934306411 1250 934305161 934305191
    0x4060e03070606030c060e01050f07050304050a27231503030c0f0106060c020a151b0305030a0b0a050a17210d0f06140108060d02090c09010206100b1b10 67
    0x41d40019606000c02c5c810004007a8407038a500135041c08180d550b0783c2420341000d030310003185c0c000c814102c0d040d01045c44040349a4a4100c1064014490300707102d0089002d42c91016000b0418020301914164104040445112032922078407071152200d040e110324070f0707070b4040002c1c0042c0c80d20481103626000025107040c011a0014070051292003140007004000c0d6964416507441030741050007500030004900800402d4092030f22100840c4036400c1030461a03000f06c40000240610719411008560048203200083d40e003441030502c0c8040560f040b172100b600300300000b8082001407248405000412113140a081030a1020441400585880102e42299982c2842c0f8a420605000202f07030b240c0514100070300010b000c2e51040b905001a85070143c18501d004440b4000000c2202d900705418001d070100589504010510803400a000355450b480508002030038035201030010603038125040003c1c003403002c190741111a0080c00784000003004031020001f605000b07011940d44081846c2c004040b042d540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 934307661 1250 934306411 934306421
    0x1d0d080d090606080a0506010b0c07030507060c0302060f09120913050a2a0e0f0409240b0405010b180a030611070b09061003111c11090705120c0304060e030706 70
    0x80308501c140550f40e240c0c20b0059841080f9007010382254010001080707030850510040c05c206882400b070b110516102e032140bd1400b01594480400035102e036982105050b414010103070012100b00c004181410043c1d03199a65140d00d00020003030080020b0060000e80e81d03800d9640e2018407000b0f0601c00741c905010850010700c001c140540c1c0c9403070302c900c0e40c01d0460f582e15140300d09101c950b240d900c40c6007082c60501600741100341c0066001550782c81400003240d03180b412a40150421f41d41c0d21600000242c0e40b01c241c036040004c0c28007550a000041c400d0069030b5054a100c10301c0c066a0391000c0c2010000105407071810307480034108601c0d0a80d1192006d1310100200348645c06103040e640e00d0b4861010103a500e03101100c660307403c4c120b1203005000007070408900405181c001851030010b001c0c050215069810703218002c452070000c1078988155800c00c0850305a01c10001d007031403420165441308608410200800c207208c0288000001801c12a40c0e80c0485030340d840b208100c94841e491482e0040043c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 934308911 1250 934307661 934307663
    0xc0914010512010326030c0313021c050f100902130c03020f1602030d2c0301060f0801020304151b18090c080f0907050105160c0503030a0f0e010c031d0d080d09 70
    0x68441c415217840c42c030040044900808446071150f180d99900d012100d1810000c4008036441480c0d00300100101514510f800e040500070350107040c16010305180280351040c05215000740c182000000d40c090380c0d0f440c008062451210310080380c0e000586904400910840d01c50f8140c000b0b010500465507646552040f0741a8802d4003101c51100c0940e80913280c8a901b02d920a4a01c09601048079070554459140301002c117003c0c002068803030300c406030071480070590313002001d0b1694003100300300a0000c0c0001d929002014100d04200c0c0107802442c101207400c441c2002c5c800d001d4480040b10311000402c03103000080c4203c65042215001038803005012403c181e41105000c0711880c0400d82000c804a040030841314161070f41464101804204040c4108802d01070b2440310140c003001a0984045c0010171500c819695000c00c280f01c80e80c00984402203061143e810000134208030b60000e900281030b14084100c60b80c03101c0c0c0d14102080065200540c40d030004000110102d01807941c0050794011a0500f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 934310161 1250 934308911 934308953
    0x60406050d0f15200c0c120a030e0d0804170a050601030305091306060504140f271806010b07020f030a080d0e060c0d051f06170a0c09140105120103 65
    0xd00510f11030401d0343d00b106154900030007040440b12500d00b00c00003c0c00c001d05000103a0b003414283c080024102030150911042c070ba08841194810154400d140d02c0640d0380c22030f050f440c00c071a503442d02d080a000e1070003210600c404c01c0222040004041184104c4594480c007168101d60b124038008103241c101c14219030250980552000303150b030050040c4816506141c1d55181424501a9902c41c0610580746042d00640101d1110505854162010748032042c1120842e1035000340ca65525482c6000505410302c80d208405031000040010410904503000400303581d480d08841e00000d0804103000740c07680c2e41841014680c008102090000c0c0c10b41c1c0c0b560480402c1121040c52070540c0b1001e0407214414082c0b010469080b5481c2d1a0344072607000040c074105c8010400024401040d002d14541010005c00c1c1c55001c900e1140c2550f504140e440b0003082814042c041a4100c054003418243c040c81000d5032405a26600d90f0340b045040ea100c810320840d003007150b0b50b50b905000c03015444c843e01400e58 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 934311411 1250 934310161 934310183
    0x516090c030617060c030a09060218121c080a022203020a06030903141e04080a1e081902010e01021c0c03050103021c050316031125030803060406050d0f 67
    0x150703e021690050001509000751503d951914a280da50703610003010412600d503181e041d1004625203102410f0b100d90880600e00709428074038108080300810b5401c3c801194440e41030700c070040c0000c1c4410403002d1442d041100007502c1c0c0d140d001c1e0180c040e21f40311031455801d945541c40d84811110302501242c2c001e0361141c9400340c4825046003918123080e000f4011668002d00c40380760410b400b00601c081c0320000c602503800c2e07003c82c4010070b072a80240d104465680c04140381c2024800000c021080d5542984c030b844003040384070350f100186802280003107000640342c085101d04c07046c004c0d00328900b03004411000310f40c1c8031080291440240c030f40c0c050b1056002e14224040c2c28060081c4035241c1601d40050a0780350800d030f90034001200010058040f41c440c042404005000801da00d01d21709814482e859008402e00349030700540ca49103040c4002a10880f030307001c44520203400c5d040842c0503a03410540c04d664941d1a4004a0080d10b0158880e94100007a11004814000c1002903600782a100c0c8400c804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 934312661 1250 934311411 934311419
    0x70206070f121d09090705030a050d11010207020109090f0b0a060203070b0c0429160804080c0306010b09062b0212010b0301030c05040509160b040f061403060108040516090c0306 78
    0x150860403141c2c4120107103c4600c1003552441d0180c00c0c242d11600a00071610b040781c031600803034284840a40300310781d690b000c40c6d84103824039044200d400703071200c0c484002c6003020380c10b40000701a200380d40700b074071039140d03403405144091032094004402a03000075100e051001d1381e03400000e540340d11580f42580d220707818802285001c03448900702d800b10303140c900c246001121440c0901d03203205001034041c0c00142c0100442d085a40003c0303009022640503124050300c592400812a080c59103e20301180f2070f0b0000001809180c03500404e0b1240c2200990707803142c64140075500d065040d0501482100341013010000110350701d805030001c104400c0b045507007480990b66500e11003c00d010a000003071003c01e140c1c100b0f00150900e0b071b201c2c907440b07030505c0c0031640b025864400d90342c1c5100f00f41e04140c4100c0c0e00094188003c407800901b02000709814a01155000d10700c90421509000c0681040e0400c118140442c4c00d0110170011031021102e5175049505d0b1030b680d20700740401001920b0300e6601007824010009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 934313911 1250 934312661 934312667
    0xa0507080139050706050112060f020901020a060b0307120b0703060e190510180603050c0f060403080f09060c0c011416260d0501030b010e160f05070206070f12 70
    0x210ba50075482d010b0b030811803200c80300911a00c2ca04a000000c1060500580c1c002c60703001e008080c000c20704018410303803000b598141081071700c490110880000340100302c4804540d0b4001070140941d80c0101000408281e101b00181c20119150300218400d141c4d404101d00b0310141d003034050300808040e241003025941da1120f81c002d103071003140c20a0007190300301c400000b15001c942005500803400c03000c2d000e100d91034207000b5075844041104001c00542d600030610800000f042031800f01107044400510b0ba41841002810912450000a1110304049005a6440d040c2d4080d130319100801081561906402d000300e030380d20a0130901a9002070f03140c09002005515070002c0700c03003690025010500740c43c0d5139140d0079420428280f0351014402c1a1301e100e01c5086407200a001810301035000421079515504024240380c5040c0c0101591203070070702c00e000c4d1100000840d00e15800c003905080030302c1074082c0c1c0c00391a00c0c00340304000f0750003038800540c00040040a08100c3c60a82c86180c5229030301c00da080040f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 934315161 1250 934313911 934313951
    0x902042705091207030c061107170f0711040906141506040b0904020a0903080a0f020c121c0c0f3207090e0a12020303090d030e070e180a05070801 64
    0x5a00b103820425078865030b008118000c00c8010700908003440e05622681e1110100c0b0280100d10414241c00300e41d4130708010522156003d805940000c1e2418000c254500d50014410508000c100808019044816455a401002600707400400410076140380d448a0a000e6104441d4881130280d60171031701070785182440594058502d60030440c2e0a00900d40f081c40001d41c00a107081d81070061500c030010009801000420149683e40c0d1600300e11fa04100307001e4549849200340c244103248050301803078003080005940764108009001006264a5504140c481e9041a03101a00081140f0683d00910004800703100407003030354aa2101600450310012600102d440e030f044003071900890400c01ca4943c05070440340365040400240d40b2a131029a0328140542d9408a0340c40158002108004088105004599045e42581011300021004000007529181d55002d40300d0400244c00c041991041030712003554209407100112080b543d01f50401070b58544451148929542c2081c1c0c000114100324508 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 934316411 1250 934315161 934315171
    0xa021302070312020702033903060124120903030b01080603060f0c03190e0f07170631051b270403020312040f11060f031b040902042705 60
    0xd10450810f5002c800019500641c0d00381e80c144505210780145000d0381c030710f18654110740300d010807442c41d2040c40740300352881d1425030340d109810480c0100701081980204151580c01c0001980010794500b034246d41841007001d202d8040e520b81441d0004050301580701110748402600c40c0040c682e1480c040503601c0d44221409030102c003240011606054142002e15041340e600d50b83c4515800c2030303a100c0300484d044c40703981d5082980310528031b4074105000d0104201419400d410442c03800a1010426507542020380a100e103031900400c1074440042000d061510424200f46c100403805079801c1803980c90769040d040b81d40289100302215620300e44801e501502c40c00010081100c041651115249030b00c0c01001601540800c000d4241e840380500c4000348036900c43e8020152003070803800c088182d0555400721500a10b42003080300d21004009065950100d0704160040b6074600034104208a802117511031590725002180105150361400c0340c81074104031108003014403500d041c100c41d09581003910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 934317661 1250 934316411 934316417
    0x7080901060b1c090201030f02220923090a020901060f1806020d030e070302190812090105190e090a0b09090c0604121a010311030f070503070b16140a0213020703 71
    0x81003c0300012584c00c100d8501707005040007e8000d000e2460203051340e00c0301001c01580c64001d006c0c4007001c42c902d041c04d0084c00a201c0c0c1081058500d03d03050104030070405c1c2014a4180e0000081c5444404100d0200309c0355000d400d5200c103507901d11024050311802e2101c20045500030b456441003501210070704086480300d41c000c264418030030100f54018150517031601340300d005400000c00961111142c00100c02c46803c1e640300e2540c58046080e042030701000392101c52503020840c12032103a0b446025516128010546100208010302090b5400d81512000a400001010810001d0145980300604482e001d40340004280d90382c904c5681c95030548103090381c2c454401d01c0140b00396401c0b00d0411046a2141400185000d40c501e0340402c003540903881129134519030700c078180c003900702400031032800030329080103012150030000000e80301d1089000d00d602c07405000c102c1c00301100025005c1400d80d41c114452058841d012400541c40f00c1c4040d5060b4092403030483c0c03005401140c3d10840c0c0c000d40d0156 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 934318911 1250 934317661 934317697
    0x5040209070f0e010f1103031f0b0708181c060f0c0806090a020a1101060b0a0f08060a05130b19030c0e1e100b0d050609060a030c0504020a1707080901060b 68
    0x600155030605e0b0783c04611040040003039003c0c1c04200100019402016418a03101400c058100b6560b04854150400c1b10154014014000000c080b1801d0301c06140300000f00400c5001c051010072038000c1000b9441d0303034201c5407100c11018030115611028403002802814043c501d40c1520568045000b40c90a98110780300d0030019441c4541d903400390140c03010604d402d52a440d8680a82801d55080d600024080d503000200c0c202c407139420281c04d28810020b1304041405103000700018070104002c6c8581070140c2c2c243c50000d14454210fa1095107110b1000301f410901480300310750340103402e0a0380000c88074941c1d4044086011440700200511030080031141c208000c01c7d03503130768603003022000e4002011440d04031808503000c50001c0150500d003c0001d000961032401c41c00b04410003801a02c0e03180124201039051010852540c1982d0503500d0603200076988084984080b1494003000317060b444c128080a0920164503400100c040c010000342c0000d2109680301c1040342d07a140700d010401c1075070035118 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 934320161 1250 934318911 934318937
    0x721120c0504060816020a0b01031b2103111204080f24040f020319151b0e010c1703040b0108060a0209180a110c010e102003090c060d05040209070f 65
    0x45440101c41e40220302c187c034481030b00d90713488852100b420307002196039041c0c01d60010506058004148002c198402c101c03d41040b400b078810007040d5500c3c501400f085519020000200d80c20442d003803812940c01e1640c0d1380c070b580c0c0c0c500060315450444c0c03d40c0040e02420000a5288d2807020b801121314008403100407486d103a40c2e072205c0c00440303a85012030301401000d407051180740c01079544800749400b0302d90148240001c901c47c54102ca144034441170101c01c8400c1e4610b00c441d03110a800324950ba0a00b80182c1c43c508600f0820b038050407100b071128006a0000400c0108901c0c003400c0d80c1280d1800045840d192105603a4100307a0082c00750742904408118480c42c812003080d5403542e040310844030001901c4520302061525a072024081e110540e454450300365455a0410031a0a480414203040014030071104101100340600c9540d0500800301101080c22480180581c0ca100c0e540140a1555000c0d00e402c1c58000d030008490992145034508001040c0c58003483c2140d002e00c030140d40360b0101540d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 934321411 1250 934320161 934320181
    0x1b270204141002120f030f1b370c021302031306091e061d030c071a1b1014060904080307020a020306010f17071a0721120c05040608 58
    0xb42141d544214440d074460301d20121551001001d00c400c000565071360342c4c58200340381140c2807405412480054800300c0301e001d60080000548044100607009601d49900d05441591381003075041d1f03000030300044400044403d581000903014814400d03200d001c0e005420101c600101d000c1194402d5039244600401800a0392640c03110b01001d108100a0041c00762410b0203c0d81c80d004201c00701e424540d01c0d10680d10000c2e03268000c8100e8004140150301e080b0703905880680b90444c600c42d101000307290700d060817580386e0b021046c1c60048113110301c400d00348110007910a541701c2c03088610300c8600303180c400703190084420240c6245c41084040e0070b480054490b43d8801c59180d0008207603100b1402a1403000c4010f94003071000a0003001c0d00484150190304040e5a8900d101d09414455060341c00800204002c3c3c0c401241070280310503aaa200d600c0f0340980c2070003500034500c1c80560240b044503c008804054010180d44202156240204100070300c11740180d030701d0b202c0c0340a05004200024001124290707 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 934322661 1250 934321411 934321429
    0x30d02090a0905090a051b03030412020319030801091b020c0919021b010c081b0a09210c060e06040b070807060204240f0c020d1b27020414 61
    0x200903001d8903200340d030758094208030748090b40c007184280c1001c01000c2c2405020002c031205203d051121003240313052000025a41d01c6141304a4485003108460401907542c10b10094003504000c804046072a030080c0340042c5010024012109002d00d4528030581101564a09203602c00741d030b07002462180d1401f07003004400b0340001e180000704800d4814021400006001421900c81d181d601400c2e0003014001080c02d4450780c5070401e040041e0301e410400305020000f90200e2405101203035641d580c20003031081b180d40201da0400c101c410f07006409800303403003650258a10b445000d42d00c21820f00d5100d031011199111080003070750b40300c0c0382031000b482012181c800400c400c6109240e41031502007035941d0030044c0d811540c01808074032508407803960010b070706da00c0c118503002c01d81c48c0801c0003d48144010f801c0c080387c5030029018107103043e40f4000f002070480c003120300d4007804461030407003e9440c911600544e446071300d010112603420f050b841e510303030040c005e44056454810741e020341c20a81c3e40a00107207403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 934323911 1250 934322661 934322677
    0x4050d03050318030f13120c030f060e1b1c0803071407140106031b08030703030b0d020a0b04090f14040611040f1d0105120607050306031608071511030d02 68
    0x7034081c10b1507045003c82000100208110160215201c0075440b0388804100030940c40541000c0b440c1034a900020840c01491050b26031002d8107d000b22001e0034072030001c0c0880d00c182803c0d40f00d0701101564581d240801201508800c07180e0030100d200045581c44022928a4005c0500005001040c0720724040c41070180c444003040741e45403d20b000d54581c2e200741c01660041e8286a551807000780280280138610050000d03c00300708100151078210429034074401c0b0302024081503568102d8204551f0307070045040c0314580040242d10705035180d41800701e06503c24800c3c0d4004510700030200e1181c010500681441c20640c0e200000c00b50f81e2031f120301c0c000c2d01c1720b8114400080b500f000702182440601c0300890151800000d1b8041000342c2200d10000c814060304220301c1825440101020b4041c0015003941c0b240003031401d1500e070788810300400e190081c0c0d1000030f80c17401407450307000c00e15040000741001202c09015100401e8490b01070180e8003076050020324101a0420801c81d60b4807035031900103015103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 934325161 1250 934323911 934323931
    0x1c0602271f1d0406030b0a050105180a0908040b03070f020d17010e0a020c060901050103120302030412110102040b0f070203011a011e09051e03010608060601120e10020f1e04050d030503 81
    0x1500880003d007210403641046822140803020f0019028952041a014082c2520021074484146480642c8010b00508800c25580c880c0311990801c0f400c6001d40d030040101d0382545450f0b041116000d4690ba035210f05100051003003c040c8020039108102c480d00c900b02015018600d07908084003110400300003407460f00400d400308201c0740040d42c10050f4901c18000c0380000140b40d4154640300c10000c241c10100400c250040c41404042010300c1a003091200c203509241501213005201c4a000e03016a602c602400f200c0400c02820b80507695000306581e9200320000c000940100f54070356094010901c0090005012540da504400c00181744800e8a400c00d0400451032595100000c0349020290014081c0d13444140d9050840d00b000d00505001d0145440604000c2c80c010f4002400d1b4008400503142050325a212080d1a40301031201000401c45149c095695140041500c040d81c1d100040c2040b0031404520b803010ba56150406075070903908001c20058022540c0d4a04071582c3e0400307801c000070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 934326411 1250 934325161 934325207
    0x506070b060415081b15090f0103110433020303070c0303090501330501020c0f0a210524040b0403110d02011506020a020f1c0602271f 59
    0xa01292511a00041001000424080a845c80041d40743c504a04d1010b0166107002001d02c20182d21005582e403c4500b561150042810140101d003c0c004506003190300b4400000e01090880c44406100c0400e0360003000d114282c140702c442c00b030f0241d503800303140070050b0000e1000c141038030700c98400d02122170b01074580400d5030401ea07100d2508541c07181311088192030081c801c00c0e07031410482005a62895191341c404140600c0c0c01d0020b511034214060080c441c0c0365081c610721640c0d4450000c074005e0072241000e15040322288610200710b420310b80c01034a1510904010440d0100740f030045201c540c0414100200b95103907980c8441240c03501800c01c8041c001540c60315481c400e810400c1c41e0038241d0702d500208a51081403041701320449139070000c60031900941004805601c3e43c44005603203010513101510301a44181442c2da509404030401441e05000080e00302869000b040040d0950a66aa080c9500050b030010402c40e05204030703501c01c0303807900129180c3c80c00340503100c1d400c0303030300503404080704 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 934327661 1250 934326411 934326431
    0x30103031b0c1d074e0225050705150f031e0a062403061203030e15012115090305220303090306110f04230402040506070b0604 56
    0x65200c4031038104803804081c0c440c04460f20f0440039422134102000e418810032404005207440d0b07085400e1422062141c1860a003c01c190510200d040c200c14000300408041c0408400003d010b54082d80116034902110b54110010491805c200f005095110000b8032100c3e03c2c00007802500c0301442a48080280b00b480b1406000804100961081c0042504140e1900d860300d05180301c25805001841c0040c0b0f0410280140e0701d850813403140f0052103100c0e2440ca60803540c400c030090318080c0c111155110000d0030000405400d17070402d083d0445c8030016510308031800d01d80c0e030300018401d21842200010009001d420a107840d4811014035000e8820b0617525071884070504141c40c184a800c0700084c10000b543d948003130a5884d210003000121514283d80d0b455901e005000c0601800060a025540c0c500d403088003100303500301c40b0158a120b00054486e03030b68521448840280390040b81c21402000031280311840c0610031102a078600400140c1840b42d02e132502803419000801c02071300b060f6110410f03c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 934328911 1250 934327661 934327673
    0x3090302070f1509080303070f0309020f040e03071502030c03010501120e011d0105010503011b0807020715051b01111b0118120f0e0d0b060d0c081c050c03030103031b 73
    0x1601814050340083e8107080d049200910550302039000c01c0c0a030f003041c01401b604907405107080c854040c8070301d0045040303500da0002030031041c08139250b10751140c600859005103080101c00f40800600508540030300b0980091010180d1108480c03102442c44108014082d540c090740f102022140d40020000c0e08102080d6000d08650420035020310a464800c0d503074141c007101340151809040158000c0c030082ca1880c44800300c41201d4041c1000b030050540c00951010310800120303006081c914a000c0d2460005540501a644404d085105010322042802c1c140c1505000d04000c2c441d13104103007407074094040207010707192821040000c629500d4401000380c0c00456000c2920040c022102c010a2342c07040403010b041e10150303190750014441c002032094600d584d0480300c001d600740c0041c50700d00e0aa64034000943c0903104420002e201811404011500d0540000e4100300e26206442c0307662030525000c000e0b212805050030049080d401080180002480b07105030f0000c15902e0400820010465941c0c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 934330161 1250 934328911 934328939
    0x206012709122c0d02010809390405070e04020c2a030613030903060504110409050708300c0a02150c0111040503061b1603200102190309030207 63
    0x9001800c072101000003a568641c9290024000c1c40c0c2c0c1c0380070b03e4004400301c0d1030a440c45401905104003480003c21400c024030100d8500074040c02da00000448540e81140d1352115029500001d014601d4040c800d030506114a44c000c1a454950098680641c0100006544110004040ca000304e8181d03511200c0c2001001d00e00808035101100441c0b0050241441c01000500c1020440c44590390840403036044416241681d421a00115440e503a509114104d00224042280c22030320f000400024403d01041e51403d8900c01802d5452032000b0719020714204101002a0b410001c00721142c0400204035001000395092800c00d0300c080c84555000180b481b00010b010020300d0b1000908001c1d485028400c465001c6083c900c0c45082504103030200b96903a0005221001209862038154410141a4103654a08904600241010039145001030210321040c034071004003c0381c1c0d10b03088405103060080c2e403040405041040f42d51050128100c000c0c0944240c158150b000b001c0d00400c441c3c014800d9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 934331411 1250 934330161 934330193
    0x605090606030a1d070e010504050717041202241503060108030a080603070b0a08071403040c03030c02010201140a020c07092f13090e0c01020a0b0c130f0f080d0206012709 75
    0x84030b01c040d0700d0704052006864ac000d042004122017200c1135189080c0c4421160782080d0401414151041c0701c40059180214200107041501c940c4038004040003c450711652282c03503800d4001c6002c84e40c800605940704020b00800d01c2541007448900a0700f88034803007840d8000340003012569410740d180c405000503400b0204480018040ca010805803d80243c0005002d010100040740f45280035141d9562141403408001c0030040c203105a03600f03683c07003500030321007405180d60060406d00b41046260002d41c003403107210003e8040c48a00045d10f081d03910070b14594078048404050240d104c5080a14401400c0044400d060030500100e08a0204400540050b110100d0002402c081d0400f07090300e040001c40c0d60f141154418695100012503240740c15402030813a02549854500c4a040150444943d4000b40511901da8400044c0c24062580702c0c01191601005c4c0c442d80d682c1204101c1c1ca4107001d0041b041700340902548015488010300d490300e0725000791900000d0000d1666903040c0204d400b044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 934332661 1250 934331411 934331429
    0x20c0306190216060c0f0c0c06080a0f0518100b061210030b150f030a020d11120f0a030807090f0302011409040c1d01032904090c03150605090606030a1d07 68
    0x3950410058100c6d204000c1495603040090380e44c12241d442205c13030b201c1c602540e41005002804116245142c0c0c000c80d180541c86076040c40549031420092061070101c415084851040c01c02c20340055581c3e100d10703018001c01030a000c3c60416480c809039004000680540c50102c5001c20000220b020b000000c0e0103045170750301c10b80102c03001c00200252840e02c0c60450344640c0083c0b00d04001a6203d03c00b034001103034050b100342281c4c2d00400c00210b0586400030b07107280c5401307a40c1004d0038680001c1184201ca80c440e8886003d1600c900380102c46041d214000e0103000032102a091015600441044414000c103440061034020040003080a136a1039910340000301e80380c0e4444410122848e450050054020b20301004803403481181114581002e83c1005a1401408540e00c11a112500040080754002c0100030500d1380d00c0c500860421000301c00000e41904d8103001258500e8110b801c01d0103400c00511243c1541c44800d145001840c10b074020300c000070414070f040d02c0b401d2070901c608002010054 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 934333911 1250 934332661 934332671
    0x140d050705161401030f1d0709050106090609030809061e0307091401020c15040b0301031505011505040902030621101410120611040e0610020c030619021606 69
    0x1141c40303442c000c0d80721403104040c02020418004020700c03c9051204440074038010034400b0608003070900030484015807000f04911175082c500c0001c1c002881008403481003900b0070042c0c0c0d0340d5208407038040e01d5002e440300242420304100085203001c0041d000f480380041c4641e1070701286e02d0307801e02c0742c81981903640d402810100400c1800d035040b100301d0008000300c00008600c3c40d51100000e490ba441000320740d101d01d94078482c1c7c0d1403860341c0e2400c0d034010b400a00e0720240d480d40c4134100340513245112a80a0706850515001041c249183e94140e801200715842d5282014289a01c102c007a4000410340c58200046d41d50704140480c1c2e01031403040b003000d0007000d410040360b6007240c03405481203d602d101481c01003401b4014284c40007155201120802c40d02c0140c00c1d1610b10700000175190360b03280b40c40d1010010902150711007c50203a240180401c65030703540d0080e9450016a150ba2034140b04680c10b4110100041c2403481c200c90780324405070701c0040145009038100480801c80d8402e03000fa2029aa10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 934335161 1250 934333911 934333913
    0x6031506040906050f0a0e16170a1b020a0b0c0c0f010f060f09020306030703120216080c1008040b010b0307050d0e01150b1204020d0c030203010c080402031213030f140d0507 76
    0x1040d0104010755051b1411a00c25090180d2040e020030301030584a1001d412424020400c5d1054030f0311407a181501c400c00c00c150038034280d404090044c02410311501c02c0028403200f000c40c000a50807000991020003c22a0761720505001003e420600d400001c602541c500005100002c0c4282d512154070008009420350070b21384a24180b4043c0d4100d540024410414419140d4000071000201e9912200440312050840801c07401c2444007070800203400d0315203501140302c000208074600480010355040d9100030f0140000c07106960241c2d00507001985181c0184181d00ca20700096601c140c06080c060300d03002d401d0400f0720446018081408060b5503034001004c10b40111039400005201ca440e8140c00c11011b94803071094031801810081c400d0410002c01004c201c1014404001942c00800820055440c00f0000d031410750b04940491003802141c40315030b0700340001e07001e0300c4500f403844c0c4d00b10b0045411a51521511180510280c030342400c100c00220358048104122280c003031240c1d803400c0d01d600782 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 934336411 1250 934335161 934335169
    0x70b040302010b04290121052202010806010f1e0905091303120213180209130e0c24030925271407020c01020c04060b0403020603150604090605 63
    0x40c0018413485641480c2d1032041d0b0080b142d41c4034001e03441c0c100107041c030b170440040140d6668054044c2c00d010004410503804801c50b05602191081081c3c48071071055070f900c407003020125403500c1d200a021074880400309800d03501c20ba2400c074030700405042042400341d10a4000340b440e80e010140c08000381d8096070512150400b011025003000f040f441075481305110385d0300030380b0228071500e04403501c81c1e01040149045c0c10104207480200254801c1c0c3e28a42a0b0444800203075000130200f900614240300d07042018403141c4510703551038041201038003040c07050000b00b080140c0d903c0e051290191440e00d19840d5020760800075030180d202c2034000e01807444840f451000d4030548a40019000700400001c0101c81c01c0c4410901502d5035a0104441007070000d05000020000004900c0b811702101082100c0b040d000100d40e904600c00342c0031168803030060410013094036031a020302008010180000c20060508802031508190741d90000859400b00030040703040d5030801e602c115407543d2200340c10806820 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 934337661 1250 934336411 934336421
    0x303020111040644090105070c050c0d0f060c0807020607030207051e1603121215060f200a0b1f032a0b030603070b03041109070e0303070b04030201 65
    0x948402541020f1816401030b210f903118010f60f141004000c4080d00c0e60034040ca4400451020448000c01d16641c58100d40d102c0f4030040310103100940c80c140c0814215801141c000c1c80680e4450000d06e1020300d64000d12030342d4030000301d04031050a10352145e01c000404501811528a00c5a6101e140318a0070040080c50000043e02c084141441002400301280021901e6280a203621166001074007005c100c9170f00c1c001e51102c3d8600300490200c4d0120401c00310301c04014550480303942c0c151502201100e05011030b541501d80f000f01408122040045a02951034001510101c0c204440707090340b030810801d0782d0f07500800161900c0d0462581d44081100c0e94401541002400c9000000c8202d03110180c0800c26940c013001d41a500c0322402e00595205c0d40384040c1c10000e11000303101d00c0c2c5559200341d4015420a0314500e200707004056001c02c9404508003600e1056812081c1c0b4151031800c00e01b40320030710700054900700800008880b10354190300c00300001d00384c0c0d0b44601581a890700d01030500070b003110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 934338911 1250 934337661 934337681
    0x90f020a0201060e0408090f010516061407050a020a060f06051932010e060408070906140609220f020304030216080c0310051504051306140103020d0f05071e03030201 73
    0xf0304c41d441803101103100b0500b42d0b810203006070f51640c000d800080041c4c1c1c0d58082c0780495100f084120b6000c04c00c00c440ca802c550b4020703c00078801191034540040907903150080b074044400580c4005440b0000c00c0381c2d600b0031651846a480d00140c200c8c2c840c4003095001100310030003080801c40c08002c0118512030040d580c1842d07a8a1149001c008441d2044540300441c800c1c2c4604203c00c0c09480d01c3c0c0b0f035850404813401081e542044401c0d199440d00d00e00c004e04040d100b103d40e5807021006150700c03800c100341215241e0b100180b01c0441c10300700c6130300c00c142442d10b940014246662000b258501d8140c0344002e5014070b000f0380003410391691401d4a4004118150854030240d0800c0d107184030641c0f0002400a0900c118080100d09582d500b000c58510340414203034281c2c0306050106106208400544403214607002e00000e00c980c204103461100c3c1d10100707110003508041440c4805010524001504c0d04151003002a28005a51000400c0013425031240000103983c408504008160b02482071000034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 934340161 1250 934338911 934338929
    0x1b110d0c020a0312111903020609070b090910030501062d151103070203010501030b04140105060607151806020d15150c2a090509191407090f020a020106 67
    0x489100ea010403490226444010000c942040c1c0a031016401804880505c183c4441242c41e078402140005948651803101540075014010200d259003602141120695001e9039055180901c0d0300b05120030258024a4950054007010010000603800c0c00381b40001d111480074a058008810a9103405040390020b06d0a5400c50000400c140500c103400820301e005c1c5400e19031003403049006a241127100c0e107000294103529100c004400c11050205030390055000c0e040801c003100d00281c40c04d00b00c0704240d410b154080c005001c0f56002803081c400e5001c50400710200400e0364a862303c07038501c01c086005401c0725503d0300482c0b03000c0b0041140c0f0651051122409070074440f14508039242001d5580002e007403023044800008030060200c21100c1035540d10720803007109000007205240503524815809000d070300b18240008100300c4a00083c60b10303c140503034107050a50401e40e907070b0380070a4803004602d10a103014082c0c000400c016140b049030b1524200d40c1016035a0000f400000382100d07042d800c04104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 934341411 1250 934340161 934340177
    0x307030e0c090f0c040302041b0e0303030907121a07030507030f02040b0403080d020f0d020c0106050409080910120608070e0a09081b03040b1b0c120d030f1b110d 71
    0x140e0342c035100540c2e04084103030a804400d8844248007001c520560300060f402070b040c100850209071499101288848403030b036900e403500302904105620392209507004110740d885a407040c031007003850380c00d400c4116100d28000c2007031644180740980014000c90f95440400e03a640c04110050780c15001d80a41409680c10440c6840c0c1094107810340780c040c0e8000134000c400007103411840700781d195040341c0c001c03003c551102d03032204108880f201c00b0394884480b9030b141d5420540c0014460078140102b01805510890b02400c00c52010280b04120208080b03040402483e614580089107051113868050700c40030700071740075603070502d82080340841e00500b100e800c1d28034181070000843c15801c180d0388c001504150301c040c1e22480f02c4616195001c0d6400c0704028030000a4030880f220b0b406164005884905002c1c3e8018480401c200182c04000c1405440103420209407040c142d486548101009062000b00240d6100610860303000b4220281c1c2050214607090042c6040f11410408062039256504e03103060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 934342661 1250 934341411 934341433
    0x1020307020706030506060912061506031303081302040c0203040905010b09060a05070602071e020f092203090b12071701060c020d23160b09031b030a170307030e 71
    0x9a42c24407031040f01e0400d80d5500c007003510381c0e441302c0850b8803010300140745003e5070307407041ca6144d180e01c1c1c159524900c4800d01c0702e071945641018026030748038144003104215421801c0d141642e0341140202400d502c8000080c004005030f44500c00c150340c1c00100da00540c1c545080c00d46403400c540043c0c01c00d10074044e05000004c02950b03400220340440105240840d224846441e040000e0b010f6004014040d004031002001c9420700e04401040c0301d402142c01800c006a010140085180c05444e4583c103850f1000111030600e2100c01c0c0070500300d11918200b0b00c596230700d903030605042c1c114007034081004500784103001900da44000b070081d035901c44441000c56549003c0d0050110040543c0090003003075501400c80501503210001c080d070710040c40b1401100400d028503c0e0f01c0d02c00039102020b615040c00c030080f80542861007610028180074005001d0500c803c17586402c6c885000100543c54400c0344038001c0041c0281c8011480180b0010043d03849041101e006810b513624910b400169600411080d9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 934343911 1250 934342661 934342663
    0xf2406030f02010513030c062c03060f090a141c14031303090519050a06090308160f17190e06070b0601020c190306050a140414011b0c11030102030702 66
    0xc6241e030b40c2420403550300c09003002c01000d100029403024021403c44400014100d030098806821441c01d81404001c80450b080c885140e100306006040d0164840000a50505059903805400006003811105841250b6403000d1300101502c1c180c1c2a0b40d000500385032074510140180b10b120743c1007030905010514620a83c200e644c000285030074442114401d81009240c000c803130485c0502405842c0c54000c58400440000401c000c0c411750380140d401480015103148100000404d0b80d42c404001480c0c03d084101c0c071404940d603044150b6449804030020b4002540b40d40c00442544200c0c800304c0d07102c228401d0103c10020452907140d0900c0680001c0030015a070300c108440f00c171a4481b840081a45034680100e2514008206030f0f40c1280c4400007440b00404400c28080480303104903c140910354846155000341c1d084102081010b29122010400042400d003041c0070f40421400005000c0c011042c1c180ca140b02c2409000300130031000c140341d20500c11403441800d0034000680096203941801b203002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 934345161 1250 934343911 934343933
    0x140604050d0b060607060534050a05090406050d0b0a05131e0c0810060317040522020913020301050108090a050309040b06120a0212090712060207020d0f240603 70
    0x80614076442e00090040d40c3d24410f644085802c0407080120f1714013981d10503c4440012459140700e40600c0c4480d031004400201803d80d076109607121070800d0748a0000f600c0f0341d04030343c807000d0307006890b04404591510341c24400302e000d5001d04901102424403191000840d1030107401400304000d01e0710b81102040e40d074408140359103c10b104600c40001c01e03040011520a45401100850040c0844103615100b10342041c000d4a00130225104c076052912100840e0f071055105040d00940c40013905e0120f1020606a00e0802c3c00210016191213050781c006241c010044c3d5000c0802a808170060280e540d1128901d540084101c0080c21038031000d07160395540c1d00441103500c2c81241c882e1004119622143c040c3c4800442c0088482d909003008a0704401a4001402200204c8075410000303206040006202d01103036080d002c1600840e0b103548846c40694044401a40c201103802d01d0080050a00b803010445680200c54481c0c0380da4840c84046100d000300c0c41d060b5038080c14600280b01184241d40341c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 934346411 1250 934345161 934345163
    0x10b030304051203120a1b0810090c05040b0304060c0f0e0a050f0301060504020f090315100603110423040f020909012d0e0709092a020102040b0a09140604050d 70
    0x100c0d54401d9035103c5052840c8115424540d070812044240864000c550b00040254040d9105040040c40d140781c045580c564103e90420040003540800c020851160784105d20f41d141d285400d0b46030540b5040002c0395079006550861340c081d0b89003100c02c4c0c5941d101c0140003003106146444542c809903c4006030b5511018000c5070312a480c10041c00c2d0311a5025444500280320141040d0744070000c10f1246041a004a00f81e28061702a05002d000c18528128090b8426050703050261141c6050500071002868841842d5204000801c03001c1000d0426407401c2c00c00d40011003c02c04940f40d80d40c1404141c0d80050169011140180001c4a05070f8540321007905540d200d10a0011602511a5101da80e042640725141d441ea2400d1000c01c21010001c181c034881d81e4580c84480c20159104940b004450036105021600503501030710808400c030824440e00c0c608081e100250415403a69244521948800c01c00d40200e1040003041041007249998a031018102b12030356803c2a1a080110300d0741454807030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 934347661 1250 934346411 934346419
    0x813061409041e0903120605010e01120903170103060e1e030a080415050c1801020d050706090f140706020f07060926070e01050f0906150f04030605100314010b03030405 74
    0x1d1030f030512103083e43c98003507481e41c44001030080c07410908014103124002e10401601600304080071a40d540201040010b03200e0680d140c0f0403101400015500034040418114208030518030000041c0c250040c510f4041e43c050140020b841500720303015440e1158003010328603480300e04000f041c0126000310a80e00f100b082818030440940d6075150007001e080c0d0010800c2d803030314a8070003403050021b10703100038202802021010780740081150005984d1040701c00b025000140042140c640041c841d608103112061288100e201c0d40c1e0000d44d5510105c60001303600354843e61003120200708243e41000403490012542c40680769072410054001c0641ca414010348035012804060300d400c04240c100d8a8140000000644a00303a44800b42908080790031b00c02c01303218040400c00300040d40391003900b090203600c0c014100d04213810406400071594200c5064000d54074401d00002020075000d018481c0714900c880c205075441410740c900640c2141c48a40500056890f142401042ea00c0010846003a560111 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 934348911 1250 934347661 934347671
    0x172505060723010c021218130f0903020606180103210908010204143c190801050402090c0324040603080c0a0209091b06030c070f081306140904 63
    0x10400010801510030380103010b9001d192402258001980f14407014100c99090394003103400b20500708154081c2d004596446418030f0101d45032894075040450f8012000d00022541d01c0e0507034612022034114280660243e001002000264940740d40740c01c0c1c0b01180f0351000130182d41180c450404160b4284029181e40d901a0760364034001d4007170180e0000511800000395500c9444004a1021100d500302e01c5000d40c45c6c2d504001b101d00d039828010003500f403c05402613803031004000294000299906030715040351141010180421b80c02d4105805003011000204803400c140c4144855000d00801c54208410300b841441041040c01d070a035898006030389030340c0c0124a104000034000300319941c0000c2400c4400207000710b5094010500c544010b000311540401640c4204c1c02c192940e401124200744560001d884503860300c6c094010b160003070320b91700131a81000801d0341c0c2c0c0f8407080400c1d082a40c80381c0c00829a0b1050196a510302006824249402100f03960904181e01e014001c103240f19108030744030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 934350161 1250 934348911 934348913
    0x80a02030711070b041a0301150315170a1e030f080702031216030b0604051c0f0c0f0801110a0f0804031e0e0a4a011725050607 56
    0x18140442201c411a001c3c0d5007050390ba038200b60010750041c45080401c415600780390039007030303400e4041e0b0703040760100303500f0303071042c200d03d01e012801010380e000d094490901091001ca20389104513220309460401d0002441e0808190818900c08000b201e07a6903510b1032a6240000025400304003402402e416090054048d166100d050f42107006031101c08501f10000c404100b40e10341462003000100d0456102044911040403d04c40d90b44242e01490360400840d1154400d03c00103100240840c0380a8440200220041c1c0e41c1c003c05c2c21583d074401c1810010038a01800412000c1c030442c00c08403045400d0600c2d08412081c06480506004034400c28130001800060504d4001c40c0324041c40910541a00300100d2820409080d0006a5400074019810800c020541c98076a00c0ca40922042007108866201091943c13134202c0c29018207008415040050002580b20b0815900e0b8041c05488640d14085440098128602000d9102918440b20880045040400c0c2c5540c1c078001d607001503400941d500d100d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 934351411 1250 934350161 934350167
    0x61e0307020a0818091305070b0a140a180f030203060403050d23160914310906050f060f0609010309020a0e04032304060c060e010c09080c01050a080a020307 69
    0x400c10081d140f95400140c4134201e0241031040b01e1020000c80f0003003140c1c1c0782c9050881902d0120718008026500c110011311017500f401001d030403900c80500e0821036000528070b00c0e0032203401c480c6450000ca05903030407140740c4514030b850510260030100c00c24100f031459900002e54840f40588082c040c03100000d4034242ca04c0040c4c02c486440c881203020b40d20360903880b02d01c4241e1042d0458503210f0441c00700d0400e0f0719040c4501210b03411187c070603030390494500c4180c041202c0d042030b0344907908503503103070742103614686050701e1501132010017806002424400d5410400c3c1036070300041503a010440c985d801c00001c0d550f212801d40550f0310591b4503d0312030202d040160300a200075000a5880011700c0c8001805501005040344128400d9449a000380b400000340308905061039000c5180b81c0c814401031150512644246000a004102c0840d44208401c045421142041101d00c0090700340c48003404440d404000c003130341030042840e0080ca4050007050040400c14041c0a84c0310b81a000004900d940d44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 934352517 1106 934351411 934351423
    0x6031302030628052a0d0c0c621603050705030d020d051e1302010311090901120303050f04020d060f150906090b061e030702 55
    0x11120f600c1030040c000c000d242a103500c1208850181301050007584050781383e035001855a64829910542041d036034400310300001d120719843d0220025030b5a2600c02c6801400e0700040644450030040500340040b0f2130003240c40c81610509841844118800fa41c00f03503d4020003502e52050700307401a11081c05101701000005000a00c1e00c1c0c0881d0180e001402080d210340b0075240b410300b008101c0740803600100d052410702a5a2020400c0242604403c29800190f146c1c106d082450040640c803811a0b0840b00241010348030400c010300a030a82040d600c1e007002c020b143d01c0f075640e114103803107030301d48420401a00024140700204000031032102c2d04501807a000750418903030206649605c0301400005000e15451640d6003070f1a45e4440003058014090407483d040031402034501109a401d503940841403030310528082104142c3c164101c500703000c0f00491584029140d903034614041c0d003018 = true := by decide +kernel

theorem cover : BRFrame.Cov 934172661 934352517 := by
  have h0 := BRFrame.cov_init 934172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 934172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 934172661 ≤ n) (h2 : n < 934352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
