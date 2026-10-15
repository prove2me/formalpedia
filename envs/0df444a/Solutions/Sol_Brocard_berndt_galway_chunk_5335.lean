-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5335
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:31:56.810998+00:00
-- url     : https://prove2.me/submissions/5d19c9b7-f3c7-44e1-a3fd-04b2d15add85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 959352517 ≤ n < 959532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 959353767 1250 959352517 959352547
    0x11030a05010b040c090b18040608060f04050d2a080f1810020f070e04150603060b18070906120e01060b0406080604020913090f1424040f03050a0203 65
    0x9026140d41c0d55614200d04079103080d000342d076600815803408000c1d81342800c0c070640b40e61082000202c5040d24201c1d00f090241c486820030001071600c0f0b01a25603a140c0341140c103a8044c001c03a411603290007412004c400d0039010f9031160102040d41d0b450340040b050010b440540c80548e107039090307070603040a100000501c0c0c45075000780062000507210300000380c02c0e0004d0020b4528a5110342c019900710784103600010500003840070440740b41e241c40c007182c0d4842d401c054000c00d191a00b2000b103142400804400d002003600700f25008401034506101407900d00000c1c202441c0c00303540c3d08001907070f0075a0030000c8a205003004146104140300006545501c4900142140d205600c8107200030008502004400c3e0095136180c0d000030143ca0652810300aa400102002c240324104c500003039660364007100f4015030000807400c4a9100144041040da402d22250756050407009980c4030b1035140c0303041d0081b00f95034904580603d91060000142000c0780d0f409950b250005e00d640d5007103100900805485680c0d60b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 959355017 1250 959353767 959353783
    0xf0d1103070e0f030106032f0a0e180a0b01050d0302250815070c060e1005010b0d0b030c0d062013060909020a090e06040f020304060b0108010806040803010608041103 73
    0x1600c6003030741110601c050140c0020703240701d103500c680d1400b0000c02c0440c8407d0f4450619190700c0c041c0d10180e43d14200d003045107001a000702502702c2a90480401e0201d00300003014002c07456141c2800001c068484030a50310001d103100100795403152001000b43d420400d080801c90b034402c0c019602046114101000e04c0d841170f541c21000c0280920042148842c2406040800a0442030301920346ca024900a00102031241004080e00d42e9070030310186100f07043c881d00300c0ca581010002d0103d569550314a01c215005001540381d860b20f00240540d4920300000c201881d5180036210000000c211744500d001001c2018441002e4030f40c28880000d8911880010000d05030101c114000090601200804180c00d50b046017103468410015028915040f144000885550040048455951001080113001900d11031011580084140407c000c0c50703030014800e00200b030340d5031030281c0c1ea01c0082e80d5503600c01340c402402040c01000103100d01446100b103d5801400b60342c104450500401c00b007031800c02c3c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 959356267 1250 959355017 959355031
    0x810120809040c05130b03280504060e030c0c060c0102070f0303090302010c0f0e040f1d07031b050904060c14030a021e041a1b030a050408060705040b0f0d1103 70
    0x600e024245010f02c900d103166529807030b009051030f020f403074104901c206a008a6900000c0030000413800000302c107041c40c01500103211281e00800f500c41764405070500f41c90884800d42003003410a400300000064421140c20b00004101d1048050300b8400c0c42e5000b8001001d01c0d540070031040c00800c211505040700c0d240301e980d0000b00c50a040c10001d00f1034145030440344c10480f0441001c00c0740340d408914104854002c80c0c001903a8104c402c10b100061200311400120f070108c0c0c00c0091070790340010800000716401408030500302d0000d51130401c00c841140c01802e0740b081d400008035011405039808403400014500f03009240700780070100f00e00c090704100ca5510303015400082140c1904409030854145110004200342054102041e002c400301003032000402c50341000c03034240030010542c8008080102c1c8241078a5544003c52801041948207000f242c4a511600b8041039410307208900306d5048500c40d80e2410705024811209842c0d80e80030415a0703143ca078442c6402c9800c240340d500154020300c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 959357517 1250 959356267 959356283
    0x9040b04030e0301110405060a090306060b1209061314010e0601140f010e061b15010e070f020c01050a030509031b010b040c0c0b010e0720070608091b01081012 70
    0x10340391a00a01e0411080c10310750099051070141a50040c240c0d0980e01519130840c2d4260f00d903c46141c0842d4000d40e6940f0180c0454244180002c1400c0914002c100e48102c4060310749031507407405c2129994400668852001205013042031000c280c98140d00780503501c103a0004201a100c0900c40780c5040b0007a00049108000541c180e09603150044410640000c00e003041c102100901c0c002603d80d0003900265100320358900044480c0c00000c0c0705c8050301c4215a4044800ca51f100c1d0b03580070080320103c41140209040c29103010303079140002003c0c107000700b0581d20185803400c8404118040c110140500c41c481c403003440302054502400700e10141c0710f0074280000880245643c00c00c010f864501903684148880c001c100c101141c15005040d05403050360384092081d807076800044500040018501c049a000400d140700b1066000c0782010444c0c1903036540081f50344035400a99210710f01d2040e82001d0441c041003194083d4010105103502441c2900c0c010803260b0360302141400f00340d4a100840b00c202c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 959358767 1250 959357517 959357521
    0x15480f0c0303060a0801231e0408090103360809130c03150501050405152107020d050325050912030d0f06051e031014150103020c071208070209040b 65
    0x306104810300c0c0209481d00003807192035500c00e004002020403003020742d0307e0703500400001c8000341924800c0140b640c042000340050715007400c1a007180d030020b814141c0003d041c100c0d220a00101440303211034103044e00458201049030000d10020500b00e100c0120784017041400022481c0d600e9140c5144811700060380891410703a40b150090441e0070900d0030120a401880041c40140d03481004d9805456041d502d2126264017503081900c5801904a0402550706008442c00941c9081c41c40c0c5020341002d4003220003008035041c061352680400c50314807000c8000d400324030034450744941e140e155520250801a103060440700c041080038400c9100029243d00000e05000004240e120318000500c84200801c04032b801c0c140006c0d464468603400c0c0030340180380f088105540c1d400740000c1543c100c03071410820040d4807403000510300c020201d400c44403d90710028210b915500a0080b0b600c0004040064551142003e0090010410740da500f50f410310f20501200700161903425404d80502d0090140c3e0f1114 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 959360017 1250 959358767 959358769
    0x9041505010e0115140c03070f060b01050403030813380f0c070305071713080f01110306102f1c1205071115480f0c030306 54
    0xd1101a40004a40030341440108420b1850b2200700d6031880e45442d107440221890390030100c1c42d00810400c5c0159020000d40394003001803c40c10800e04503c17a5005120342411000150342500851102402003825500004c54603030780d014411440a200e1000d1448100024011000c0704001c0543d10105003c0c00c40d4120304000583c104660040b00d00440310f0700341c035111348101e41e03c1c050401c0080a200010072002e003046135020b5441850f02c0100e07001911414008413200091030180310300000c40c0034010040446840600905040c18651841d40346151140c1040c00f4800c0b003810b040804010112200d0161441d00e00c50813401410074200d40185041c3c0180ca5504001c0b6415807070203000c00078000381980316006004941d2985502074006910741d0303212400e070707544e07505035446c00258000c540418102c81e0f50207031011300401a5114288100c00d80c81c5036204884d841081c1001000b0000207601c144040c1103108409040404035500d04021440c0101d05032074100890715280364102000f04105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 959361267 1250 959360017 959360021
    0x102180906031e030d0c050d0c020a0b060f030c1203091009060c0602031503030705070806011703030f1b270a03080d0b0102010b1507300507050c090415 67
    0x214090403621644203050020000c1d543d030341c1c00300018a42c0e03c07802c0c1c2c29105108061081d50252240f03600c1c14000c10555200082c5554041e00c0703040c003560701d0603d01c0005148000303481080c0c42d91000c04400580c0340d0004100c00036400510041e41840307845c1d400301881e100e403041400441c041000450f281d0580104024000c1d00c200f807000100304040300304200382c42d8006245202590404001a502e45a08180821201000f00d03d00c0d0103100004020003048400283e090444400318203440321a40c807070310041c030141030030040e0390356550051000c00c0007000c4072407086130040010b070413100b5411461840c104a54101007981c2841c05920a07072214510035005d840c07541d41e407080f0351170214542141d1f45c4080b58080d2012400c00150364054580040e4001d61103801164801040950303010003182c0c048205038445e41d41150620bc2490100c00c020725601c032054090087c0b4000c9004003008080c0c01c503002d13042000156214490050810b0007a00c0e0011194051405805680301d00c42c1a007202c002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 959362517 1250 959361267 959361307
    0x30c060c031404032a03230408030a050d0f050c03070207060819180501050a0b011e02061f03021e01180806070c0303060f0b0a090f12080c031b0102 65
    0x505050201c0c03004151442d001e070b00d40c01039050030304440305108151182c90004240014400e14801401c070715050540000200c0065083c02c5074040c0403450300385941b1014003840c401e000c0541d00078800803075031a000d180644298000340400144211a1501d0001651026610b030f00e041003001082c0700d0600c1d0705018450240003903003018000350801000404064945042e4030742503641c1c0700b0510561142c06880c1c05001e82d0800300034481d90610a01c454007e03d07444204a020503040314062190a5032a0260b41e42c04038660040c0c19999103103111211a440f81c40592002c2c0002204044010fa0703c40f8030030103030782c607401c2c0c2d51491070700c01c4000250002c0301ca05242d0b461702d650400100001c2a00180c2580d001d0414903000d69014041d01c3e06030050f104541103104004020400420000c0c1044054260b090503076680e00002c6546104c18a201a501c1c0990b06011031740c0305105002c240e010300100549044902103c1c50403402003040d00319a4282da01c042c4040c1d40010f8000c0c05600d034400151 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 959363767 1250 959362517 959362541
    0x7021b15090d0f03320d0f0e06180a020904120c0c240314180a0506090c1f1710150f03110a0e0415030f0b01051914040e0712030c06 58
    0x111400880903151001c50b85c5814001000001c001040760281c078080e00b01e900c00002440341480b04440b12007400d42c0310501102c040000c0b2522150104100788001403407002c494000d0592505c588990703c03803600001c6106424000d01007400090310004542d184a400100844481c5164004602d2040e015031102e10000034200750504100320b04000600850302d0308540c1c0d14040700c015003150300c0c2c0f40e0b05101e110702026116010f00c0c001c201e071302c000218004803135200450b00d0407a064255098540c451184409610000e44000d00c0d23040100d90140c0341c00c0d0003c00c424a080f8116584001401d00b09040803403000008994a00c42e43c0d00316054000e0401300c0c55440d04141c1008100000140803c06c062085c40c8615202c0d12031300800c114980801c4040c640040d40000c0140c00390400c49012a000e00c5101e003c2e401c50046482c1801018840105940f0941109000d404640041001a0180d42e6011806004054000503081c83c11010751980900c25107401c00f414045003030040495004404031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 959365017 1250 959363767 959363807
    0x60a0302030f16050f030316030221120f040c121707050309011805030a1e02310c14090103110a020a030909051003030c05031309090b07021b15090d0f03 67
    0x20559646c1c08426034100d070380c9224a20b1080809420204d2920039447da0110009900c40d000c00c15081d1b003c8003d02594290000c20a12502c80c0721010007480001ca40140c0000344032102401980450742c5013141860242e581d01400382c40c4006800980d5000c100c0441c0c0300d51001480c42ca00e56000205030b40003101010030380700000e2502001c80d4551212504c010124070b9912195813503110006883c078002900a00203880b410000c800002c144107100598188104140e4031030030840c2c4070780c0103a14034034000f951035400072040303484100c0254004c48092030602d5120500009141d030b841000d0103001100da40203107030000e00c505000e0301a0405d6000144e5042c1000e0030411095004281c0da41129410b1801ca40341c4189403c1050440c000c01c500308811208003400080c0c4480c4640150020324040c0c52290040d440d041000d80e03581030311074140002c0c0a900d40d001e405034548411a20b02001e180170340c0c01d00c0d1062003000600f01035080e0404031280780d210214101170590014000d14000315080e50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 959366267 1250 959365017 959365039
    0xc050a081602060c0c07090204030302010509062202010f11010504110a0b0309070605031e09010b0901080102090a0b030c07020409051e06010608010506072109030b070309020612060a0302030f1605 86
    0xc02910354034004d00010440400040c0551000e01c204201001490448001c640304c64403458001d01804003603c603203a00d8440d40340894500b904d00304110501d03000c0303c8180c0900c0b581035401035614220f10b41c054428081c1c100c004e0221001c00f0302585116a11425804254100c00010010704210940064060b46001e00400c41c0900001408001b614900d04040380c9a560321078200c1445007207050456035180802042c0140e05605400003089010110b9101d1016a00c400b0340394201e0003407690300340d4031904aa40070015400010011500494104240e0789020350340c1e0041800c3d20580f08013124140e2003616100b125074504070420550040c00e00140c495545088070041810106005051080400003400d004001203440b038004490300040071082c6582c0d203000058032030700780c91000791440310b41c0c940080c50f102c6c401e1045024255000b001e46042c0070f03601490049000c00180350382c0c0c02540020307001c03016940422502d00c00c6088540200312a610b02d43e816816261254803290158000100e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 959367517 1250 959366267 959366311
    0x10091203050f0d053312070803040b03070f0e0904021e060c030403060f060608040b0601120c0509030d0203030714070c12080c0f06040c0306022b09030206010f060804081308010c050a08 81
    0x6441d04d84202c04a915a0580ba201c1072140e04147e03041d4000c0715a4800010002070902442000e10304c5014140c80da0318107a4042a015203081d1802940940e0040c41c84c000240145040c000b80b055000a030382004940c4001d00011030f03050781c02010700c0103484e88045030410030414036003d401038040c21070b48144600b44c58004043d01b1904047c2c8001d0007100b41c000000c240b81d1003440d000200404480e03080c0b00c07110300b640d40904264016890a03009000d209002c200e50360000040b0381c09801c3c03640d9445400641c41d0145500343d00106002c0720410100100094250036001400043c94054980c1981d100d1180c2605440d0012090f00f8010340d800c02d104010110b002580769804072a006803001d69519015603603100d490f003e0550344225154a041c412074114170f941e2200a850b0f22940840e03141c0d1b600c0d09503a408851092023010009120000090006880c1030080e041c504030794083d81d0540b9455440c070342d0941c0c00c29000000018404900319040950040c0b1560704074920809510420f04014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 959368767 1250 959367517 959367601
    0x812130e090c04060b072f12010b0a09050114010206010e06120a0204020a081e06010503061203070218010513020f041502030c0601030305090a060509100f090b2710091203050f0d05 79
    0x40e0f032900c14230481c000b410304034038290001200102c1c014030340c2281680ba00c458100514003030040c1c1c1c401c031003051071500140d400080d05605980c0400f0b820703044c6a0b518020400310b4486c1980c01c082601480c2e94040c01038441d80003078042e101e00303600d4192681c5800ca1815420700d0302500f030600c44d02190414400d02d0f1760448122500914180c80c400c5236108091040703407861060100c000c1d0005d15280001100700034a200c1e160598008440d20b0911003503d08c0000241e008040703a400703002d0401c010030448400001520300c201000c1d8010741c1e041000790702d021410504268002c1d004184002030515881c5005901500504400d040071810701e0260741c08200000c04040b00c80c014040c80340001040b0501800e800d0008003452003d06076242d9100e0b5807003040010703901c81c4480b2007400700c43e458154540107464240c130f162a03643d403c4a192902c88248600c070030b0100c0640a000381001080d40c1c1c1250386004288101c070b540b00102d018149800d07440035500402d000c544400c14480b010700010300000d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 959370017 1250 959368767 959368853
    0x10e0319080f210612071a03060103140a060906150e0910080109080c37060609020414010e0603150f0609030f070812130e090c04060b07 60
    0x100d2450301c941c0100c8002e0000d1250700c0300f9034603041c4000d80d00c6001d00303c036000e224800c100c02e4a0400c2c0741c41c85410403954800e520f0151015504a030848403901401c000d019560042c1d0524010074403030701190580c2400d200030348000f401035840d003000b07001140c014081c110050103520f00340030301c01070241e0006250440301006070b8483e2040d40301007904800c00300300b240f01800030701c0300070031441d4401d1900481d03581c8003000110450017080040901c26415042451070001c207070044207886e0644a20500d4580003220045450039929580480ea0908520207040600b600c00400701c03c031595400098581021010801d1181c601001003111005240501600d9540242c400240000d1041c001802e5400b4185815425110b440d252050002000a1760300444806200b611421020303a0101d508903c40c0400e098040c0d05020820880c0304040011682c4c0980c40400780e42c55420401c000234241c03407055008440844d000b10340301040c031007040788549600c0c0c2040161a8080c3c02c1c040354014910034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 959371267 1250 959370017 959370023
    0x123100e220215031501080f013605151e0102120702030f121b0102030412110a05070603051b03012103050d1104181e1518020306010e0319 61
    0x35280707002c544403070058124050a518800e0740344c2c9010700c0d02e0054864075401c580d0028030200041006000c1c0f1020040c1682c440196175018540c2a05855545030ba0660707000030b01d0071540d180d04060201d03601c40c0602800004c1c126038100c001501c02c02041102100346541d0000808544280680e000541a8140160800d8450311401b1034000a41028841100003000c0d0041540155080c0301c008c00034034403003003001c04846460983c2d000f12402c03070200302c40c02088041c400c1c0754160700500819010170511103400442d003200390140e54060030004141d03c08000b00c0e0b01c0d0800e0013803d0f224101820280e010f07000360b450456142203071454055142c6441c0c2d0200340040b48070241407610440c12540e81d4192614244000d0080000200c9154010b100e4040008680140032038120224040ca00c00744009001d07003000b801c2c1c1c07a01014010070103181002d00980e41c00000141d0800031000e1800005001400140c99180c800009840c001004070968441e40017000d81c450403903806038840350b003950 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 959372517 1250 959371267 959371321
    0x106050d2301180905010e06010306060602070605030403030207060f02160605091219021213031127060109091a0405060109030f0303240b0d060509010f060c050123100e 74
    0x43e41e07035100030041c4400c1d9005042c95090410b49a500d200004289040321320402c401c2241d140d452a080740c65510b680100000690208041004203110380c000c0e1000e10300840703000401d071040715002c4049074003241d0a0102500f81c0c100c4401030105130301ca560341c400360b02070150003400b65a40902003640309c0e405070391540c162108003500304d6610812120b044581c4c14014290364010800400c420341005104c2210702d00311001c1c00c3c0fa514280b020105051680550a001c10180e405044040c036940081200741001550369000440c03410501651903c2c52010000079030043e00c44050000b0350300c0042845041c425640740802c00103000030818080c0c1a0146000a01500c03128800108a01c001c02c0f640c10542c05000003160400f1254018415150140c9082140a548405020407120300344a43e900c018081c0e0001c00000c3d000790400300c6058854000060f100360340444216900c04040321004075800702004101842000c0b5401101902d9104881e00f8a403038220401e068021181c582028001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 959373767 1250 959372517 959372549
    0x7080403172d1b030a0902090c0c060108010b0f0105160c0b12060411071b08030d1e0c050d0905010204090525030504020a050f01020f010504110a170a080717030106050d2301 76
    0x216aa0b4011b460259000301281d00f40d00344078103600300ca9040180340d80d405010701030000460303880c14494802c07035080c050a85807868080340015203450b000001a11204240010844005054041c1800162100301102925031244003d0007840140060849001d82d142140c408241400c0c0015079030344503805200c0308545c100034900b118241e42a94400141c511000c41c030002510890340000b1558840d61900b94001000c0391005415100340540704001704d0402c00c410003117030080c1d07048a49020b00400015141c00d545113050000c031081190b0750130306071004490301c078182a010341c1403000d90307140c51a00780114202500040c0c401c00311403203180e2144a40700c1039a04564000c0c0130450000c01504005c005074600b07030501403a9804c409412902c14180c3c2c0b68042800420320007560748a8516200400103507480741d60b00f40c003d038006501078502d84054070344503500f5400e10300210f01800159603016164400d0b200d87c0001e85100c44003c100c1d20b040001c103409503a1008400e107045810b0800994016 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 959375017 1250 959373767 959373781
    0x9050606070b15040b040b0d080a0e0a140a0e0712020702040b10090806090703230a050709060503102703260912030f07080403172d1b03 60
    0x70310800703000a0041c0795490422200507401150701811903820b036405d005043d403d50801041ba501c1c076034402c2d48a0307032000300034000c1000b090140200c400c5074100240000303603410000d54038520a9005441d8510b46080c0010319082c030306502002059070307594210a5061101c805410790000e035040c1031096501050b02c000791740d0f65400c9603a9804003d444c0c05510811500c0040c00843d041c003d4050320301c00d00011500700340c80090724004030303904102440c02e0038602811507501c0d2641c1000e0804a4841c0f2110800825418091b12004100507000060303010300d490141402c140e07060f07200201103850069031a2290030320488801d07041d80750460f01d20b044401482c041c0c85034403410f41c1c0054a055011b4002551904001c003050142c20320104650070079194841080852204455888080390b00304080341640d4090304000da0880c0c4a4101540d1002d030340803441d800406e048078241c6144800c00170103881c004041d0b8901911742c080203084811480d1a60140001c00c001c03140310070600da8004000f85ca0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 959376267 1250 959375017 959375029
    0x61e06072a1814090d2316050c01021b101403010f05090a0b0f100504150302041403070b041a040305030a0801170f15270706020124090506 61
    0x140200c0341080004941c94540400503507200a400200880c60000c40c07421981501403e144628121401030440303500c052400c560740001707044929030300644507a507442c454542d4000340508508001803c4e40c22042030034124a0f20254000e881d040d500240007410401c44000e81c44951100705540d0305902850340b02046994140c0d0541c0c0b00206240400040781410b8031110003411a40c00b11038070301d0152560a10001219100401c03543d1220350498085294200940413001c43c04907420600d00f0195616021074230f08103c0d40006000039400501446102c0c002c0b108050418820703402406a0390030f0440880c103d224034059006c0b07001d00010300c15800b003c00c40403070b03000d194820b05803074450440c5400580841002c3c00b501401c182010702070780030007100180b50031001c070341180104a030b0760780002402c4040d9005045e9400c04040c022104448440082c3e06494090f00440100b40052402e031000342141c000070844030420b00d00510a4609000c0a9900d1059980380c800000d8640c40314030000741 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 959377517 1250 959376267 959376323
    0x50c1e0406031101020d0302030c030a18080a020703140d021b0a0305100605091e07030525021f020a020c120114040309050103050c0f03070c1104060e061e0607 70
    0x10340942886404020806050b400161406081c0c085440300c0d001d41005800385c0c0011604003680304001d2000400e0310045420010452400303800c4080c110b4040e446581c0c2d29401008040050307403060f2003c104001c5414401c040744494000a4494000386100003519a441c10f50800d132803420304074215616946660603c0b000355402804c44a000b094141d042024000c1445404d00c15642c0b140040e102e00d1100006c039071001c849000405040da5080401e600421010381131000852490806226074800e8098850405031242c004140745904031031126100711542011140c0c0034010b0140100b9950001601440001d04a03002c0103290021070507a401064103800087c40001e00005100c14107802c8540b07402541c40a07a420301071503a85400c203400a100d820614034140c00100000350303103184641c1d2415181c500c02c840382c0142400613800941519925000644c2000c03603101030240c507141540c10300031500c681803805075001c074036840010901d00031010064440000078241580c2da011030b842441c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 959378767 1250 959377517 959377519
    0x40903090f091d0f2503020a0323191e050706090f05030a0c030807030e041a1c1a071107060c02031005040c091d2b0c050c1e 55
    0x51201d03546100100c003600303600580d072441c0c101c03a184424000f8004203100b807548551100800e54800c03da8415191201c541c0c84170b03010b1002440021005a541180010055000f0011004612035607031f4000304510080000364510b0380401c04203c412081d0a0300c000495800c000f020500d048803020f945203082c013614005280f40101d410218102d034104501400f9030300744003141224180c4a2061503a0b842d4103038800382c003210150b403041001510750781c014446a4030134681105160702140c0443e050b05c2040850851046405105202e58101030155680d800c0e40507000502074911521500691114110603159038070056000541050041c2d03044550310410101321064141d40322402416404501c81c03c034400e003d01c01c0e1034000320446019990155420000e0301100900d0421401c000b03000c81800d815205c80c02d1040500140c43c00c2c02100004c030040b0002220f100c4070071010f0301c3c046040103580d41c01d110300c1c00002404a600012108003944054800d500074880540c4030782c0340105101145 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 959380017 1250 959378767 959378789
    0x24030308060d1e0506090607050307050d020a0c02181509010f1a0c0307290412030507020c0d06020918090606010c150c020a0302060a060621200304020913050a0204090309 75
    0x2d01000f00008845100c0c9002001f03890840d100e070b50048405210586203140003c03000d100080d40c614641d40207141415090030041c0c08055180c0c08200703805038182520242e0415501005050741e2071b00704542c01c02c48103c594801079030500b2a190106105030203800b40f5075192140c9841c0c00d180740d8088031540840541180c2d2600d503107240480780c0d90f50107a50070900103100980c01503103102038002980141d07407080c038542c501c54900d04c2c2100109002801c1600b1485500d10020003620b0389032480012074051840941c2d640d0b40c03502401140c02c40c42203203910b0402038100300002c00c40c4c0400d486400080034039043c1c5152000d420803912040b0f01036003040000d45459052182e03541c000418083c207521903000e481c01680c070b500c0402e04540c40740c800c40c400b040d000081188a030882810b040e038503142c0300c40009039044404001d08241d2481d6400b507601424000280003c0d40307000c1c200700d90712510031440c07601c4000342c40d0741d065100e800b00c02009000e1520341c1e06031010103000b40300e15805002c0107521 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 959381267 1250 959380017 959380073
    0x6090f080414030c01031e2703051b07050a03030e0d02060307030207110f01090b030a0608030c0303010f050f0f0d06060b03070201290105030721020d24030308060d 72
    0x714607801d0090402d89100f44182d00e100c1d100c5500900905c880c4034542031140d541e035512103035804050700280040c548815505804d400d502c10008140d5503184e4005d0f40e03100e880d221020b4152071160b45c629075055955201c19401c00460303032a4420034081d43d9252411440e000c010801150740b540d24410004c0d803140700841000042a031650141141c0c500915403100c41e8001c43c814041101819002d8600050120700300344803a0903004011034002c584030500107491980c1e14506401c58004031619038060704000010000744160011a41c00780c00d048540c0104c20042c0e000291400500342441c500a014820b64241440465881a0f0044c210361040e10780d02c0c504098000d009211244083d41100c6030908041d41007280c90603d40003501043e11000e1554940c11019101d4800e2916280080404028640d070744040380c1c0041c0800d80508040461034414029440c0e0010388052600c4c0c400c42d002c0c40d004c00110398491b036403070781008050f078070010aa5528240b00900082184003040c4403a88490 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 959382517 1250 959381267 959381279
    0xe03070f2d030f180f260a0609020909070e0a090303021b0d0306080109020604140d0c060504030209010b0c1c02100914120c0c0405060117130b010b0a0c06090f0804 72
    0x250020100595035441c000041c40c031a10030a6030100f40a00d00403c0d4600c030f03050021b91b801070024a045866080403803403040089589a10b044001001140c601c0d0b00c1d50000021410300385102a003006000740070b40440c03030504851518025004101c01c0c882a25039480f8410325000364101c403190f011504c4502c1c01000d001980350364980200740c074140000d1030301d000020803110601ca5a5242540101614581441c00f698546104440c024040c4d00c040d40119010010f10403900c135500400d800d840b801d80329460360042104071070051707001c82008081001303c201812000300b4242c248281200d40d1542c5840c841001303c2c82e0489603003c1c4000c0a140c94117030010b000c0b800e04651304800d401c00131100009403c4c21006d01070300a04d800c030080c44c0e01003c0310100034034180e08444d5200c1810300d0320440480f504007230481940415182d1600803003602155005105500300040d02406c0070754501c40ca400c800d84402030803910b4130f40000e0f000f950340c1c034460020410300340882034200b80c01100301515035840322 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 959383767 1250 959382517 959382527
    0x2030313060f05070b0c031e010306050a0c0e0127150504050420030c1e210f06061209010204090e030a17010608060607060603240e03070f2d03 63
    0x40544030118481c070414003080c501c5202110301207588039004011a85070407580341c400c1e0704040c6c5411410700741032023040720340148241c0b428006c500070300c0040b5103420134030120411200d010500404102017807007034120598202d2400707840085800342c09000e80c024024403180c40c0303140b030300648040403220240303900a41d03024000d041921000ca804002052240f03040c0207034001c0300203050000180a00000308104001c4020b0421540039240c032071540c40107410400c03a0b9612440144007400e40408003213964103001841c080d4001742042912105042400000e44580150001c1410144103000010781032034007901a80d00401d141203047c040c00c44140185526500325544040000f034504082008103007200641c541202c0240d240c614007500e403801801401da00c03120056a10944444001000442040258421211078520100781c1c00f411a51482581d04020b040c0381158024440c0e40049883c00c0e0766200e20b0f80d4400c2200307160080018a48200300c600d8800602c00c207801c040d4020900d5001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 959385017 1250 959383767 959383769
    0x40b060408010e0f030301030c1503020f0406030f181e0320030702030f01060e1801141008070602071d0603150106021e06040f0b07021204091b0f171302030313 70
    0x3001034810303481303902d11000da4901091101824400d00010100700302d4032070f00c8280c01e10312014500545041e0f22040ba0011541c055400180040d50b516003891210505110b40600c051005100001008894403248000d5a6113500420b030744140c4003000b401c00d4015140c5403880209940d019802c1c1e5041907203180c0b6500b14910590080c016101002e40302c04040c401c80d02a41c00070707020b03440c0580b00c01030307100741a038801c0e03940e12100c1d0358524581781c40443c4404e0480c40f9a541803030355043c890911142c0c030300b00011580100c0075980940820700040e410042d6040380b50303d820380c000610703a880900192a05c01007206004845241e00d0000c85c4003a800315100300d06000ca050b6041c070110203560195610441141c024220300d5950020000049050712141d0300702401c0d00c1111000710b0102da102210ba8001c0d440000c41d540d1f18402400d01500024044000321400c1c10303c00c0d000c41e9211030180c131010b26800c61949103d05800000c0c2070001d00304c40c5201b074540240031280c8601001910061364145 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 959386267 1250 959385017 959385041
    0x40809130e060f061c1b170c0a091103011206110a05120f0c0307080a0204080304090605090a0c05031305031606050a062408090f190b011d01060806040b06040801 71
    0x2060340004c0c09824505030019400e4405106054944002c1e1a001c90200881d00e0700d000100c02403000141c41845400520074102180c0007400410310b00c4000c105101c406d0341c2c40202482e04040d500c584420355007090382c0c1181c0d1101c3c00b000d1508410f282440050400702d50026061002103110920603500801803c910340501000300896200d5805101c0c0f081000c0f18103c041c10020800980310340d104900380d54002c10021405030525880e2807207181180c0091700845043c0c0da440008004a15081e4806d58214203d64000c200302d40f00303400f000b800380c40001c00305040b410361524001d0403c0000c1080710828004c040d21000024a0340c0f80c250003811058400e101d915040200c0807501020780c0615000d4040c10f03264007106d14800e5181a24001d000034580c0406004207a40341e1519031060001460060b400c200404841815240050079007e060704000306c0c02d0300440c4020301081e6000345040c1540d0550501103401d5a9500c00076010302050340280780c11000100703000580040542114003a030311 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 959387517 1250 959386267 959386291
    0x103110604050a05042c2a010f050705150f06030c0a050609040c230a110705010e1309020a030c080712050c190f030b0f011508040809130e06 62
    0x1085040040c540a02d000d0b40b9840541d0400c104200d1800d944a44003a01081c9115070b149580724a504150007001c2040c01d4090300080b880641510340746480701400d2500000342d41c038101a800008002c0c400000b07082060010004c2e02d102404401c21044000ba1000810060345162908000380320031800d0340c17503c1c00f901c11000d00c074260345403103d0b074002918000350484c4d051338032100401000d4241c80a000c800e00c513550281c0d400304c2e00e112801c00e200d040c0702000507613641c0e80315034011f103005900038141071361340c0042c803040c499a03034090050b0002c8402200d8000681446803441e200400b4038820080d40248200000400c0080d00c51a07070003204d4020094881d4160766600c3d00c090f603800640000c280790410506940c0b145040e030310038242c10316140c5103080f40c152155034058841429400595610090070704016103a528102c02901514543d030a41d00808081c0388068030502010b4002441144007262450480c1c0700d107140224143c1021905005034804081d54940b141801e84660480d08 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 959388767 1250 959387517 959387543
    0x90606080309092a0408060f0105030a0b1f080d090504180305090603100e070302070203120a23090a030b04061805030a05160b181608031e070b0702060103 68
    0x11038040180c0705031400207808991180da40302c030040010322001d402111030018040340c0301040c82e004400b400103402010b000b00b82c24203040b00907429012050380100d00c2035009051000000c0d101105403600030111000d004410042007500e030818900a4008038400e2085118188086610101c2c030401c452090303500b0440c0300c1c0c5900c80d96045001038000a030100b0310811000215007040304c02541c0c411102104c001b50251070b44210701c0024815240540001e0b00402c408013503250a0000a905e003401c0004145482d046980c0a0500406403840043c1d609808903d1105401c0000c1100c40c02e110040103a55155100d103440003215802b503400b59440752405030b2481c41e0940000807410400d40010045003040c032541401c42c1c40e54090566480014009248000003481e0024400d000da4400c55140c034a410014580724900b01d400c1c00448480e5000d21010441014003004032204071034102c0c00003501c1000c00c0c44000b058468400f0080103089084100000c040c0e0208045050301d1188092005d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 959390017 1250 959388767 959388779
    0x9030304170a12020c010914191206050a0603030c03110c090901020a140427020702091801360c0e040605011701020c07050d140a030914012f12030a090606 68
    0x117030754140005002c20801d0100380700c2400340e03002084100070000d1100c8040100303000840b103070715011740c4070100d4034101102000c10026180a41e0380c1c005181007040010381e185417001010007118413405000e011050040110170700c41400300c00c046120142c005189402c000030f80c24000d40c44581400c002030305c81d1303a42c0307400ca02000c011682280c1030214002c20800141d0480d00c1a400c3c01c989004901d41d00700005401a00c600510754458540c884600b100c0103182c1007001d0a460f4050500000b061500b0880c0c1c155076105c83c0203070704008003602e5a0443c940c46207031101d900031990300501040201d0504000420a55030003060507160740802241407415981e0307404c0c1c240d0060326440005034118400501050503c1c5400500c55030150a181800c01d2203a0855800c010a0440680c00150024414490303584d00601d0810040d4080c603042040c40200717907460700010380342c1c0d020071020200107001d20084041044292103244851219590302c2c10503540304030051401c01002c54890b070401c0130010b20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 959391267 1250 959390017 959390023
    0x303110a0c17071e0302060a1101051306050a02070b0114121615020a1a07030b12010c1407021807030b0901060906021e210d020a080a0b091b09030304170a1202 70
    0x302d81c040186203010030304640c01c2011f56003296440c1c0003005031042465071604c0090040300d0194292078941d001000c0c0a04140085c0c942c010100f0b01c1d060700401183d800604180a10ba044a01544040084840d81000520008180038914925110707034009607403250200c1040c281110b480e00c1994106a402c01c5060340ca844680401820b160707902464903001c0c41c610307050664000740e9450001107074401c80f00040ca81d050381d80e400c0c0d041070b9555448000344c25045140611202c1115185906144040d4000344202d0300d80300c03544007410f0310742012584040c0641c00403c00880c0080c080c0c0c18a68440c0d0004101440d54071449d0700620510041000010380b8140d0520034440040140403900c90035041130120008008000ca60800308020381c4810100c00c1c070180555541e01c2c3c1e9840e0300b505103500384800750350140380030714030071412541440189244c3d618000102c010034035140d92240d00050000b41103007e503600400302d00c83c1240e5028140c020200701e80000a104001030140800e4010007265 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 959392517 1250 959391267 959391299
    0x91a03030706020702010e090f04060b011b1103100e160b16020d111003021308010606090302011409091501110f251d010807060203070305040303110a0c1707 69
    0x142503041040403201103580b580050100d5401818002601c00016022a0300c440c812648015000075a1301404200314481c0241074440209184c00707020101c0513624855180305112004200407441e20b6404000c0d2030078058028082d2000b00e08102d00911005543c2c0c880403d0452a100d80fa154000402d030107000400755113020138088148024949203a0a000b225803c4990a40c0d04c002c41000340300e01d030341c0d405e2a000c14134100da950240c1c441038501c220b40560318964100c1d180e0b0781d04111041c000c9540c131001100440b6024030700a03800000381a4042c100c0e00c6400340030b58000035414100800308644c211142c22240302a6103042a48038001c030899200d03000541c05000c50b82040103401d10b20320300e11040510001e461030101c0c1b609982c4000340b00c6801c484005400040d460030004020390341043c05100010405c0340080e40c500b80050750010310a00c503a000c000c091040300d541241248034104800419107074081c018114090300c981c1032203c841c4884196041c1c0d4491035602003100390b040c2d00c40e29 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 959393767 1250 959392517 959392519
    0x70b090306070309031b1509050d030b0619030b06190201140c0918180f070303020f210f1b010603110301021201030b0402040b10080103030f0f08180304080a0c091a 72
    0x2030307016031b002c80e0030040114000fa10802080302405066031406e104800e405d0b4421401000540d14041e00034080e2841c1f144040c0c03007100d0500080c110042d000c0700011401d550b910340000c0d002503000004850740075843d0840545c202050040d61180c0e0150b1280718000c030410050640303335644552130602c17403148200c1d081c0c10600d14a002520058110300082d0808100f00d00350701111200c50742280351002c0d244054090742c1c42500104141501440201c00c254144009030208030b1510014030100c076042040c0c018081d8002442007030745060001599405111f0000d0504a4103030b0402c8c45028000d01d02040e1488051146c51300c080e8030b014422900c140042420100541c2c0c615116002010360042082e60480e4039250103000690740e0301410100b01035503845521352075046003401000c546000352910240054a42c50300f020540200c0c219074829891014800e0704ca482844690442c011640700102074801e0088d40780801c601004284e0a4a0f007400040181440b004403164030200303185805 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 959395017 1250 959393767 959393777
    0xb0a08191a04050a2f3c09010e04030207030b040f021e0306060f0a0504021b1203070f022107140304081b0303160f06180308070f02010c1e11070b09030607030903 71
    0x492a00e0030200c0711990940e0400b8903034800c03120100720a0300c08800103800c6941518112000c46e401c2d2400c070814038090191442c00000310314280d6006540d031b07081404054100200d000020b004c11016160321000c42c1e81c00390032114242d440030900d01c24101c001103c607100b40240c4000800c0d50030000d107194543c41c0700600d82c078040c81c03030300090000039070201400c0c582403c014452440c004404101a80008142d803400c1c07582d034600802d000f404401a0245002150003040c0f200c0002907070084c54003076000c65043c40c02da9802c0c031440c103006111a0441001640d002c0032400049181002c182100308614615411b03100300c034404200350b141d205003440c0c503200304400705610380406d11030403601c0ca1852060340c001a0720750084040d650308070200302c011400a409881080f040d59400194070148201c140000e0020558002010345090211020902e00a41651001002610490003807800803a02c106654800c0e84810b025801a800396920b28060b11070034010400080c420b21800036074a400d944c40e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 959396267 1250 959395017 959395103
    0x20d02030d020d090c0f0e070903051203070e12010b0f0a0315020307020f1f0b1e060d0f090c0e1b0703051810030b040b0a08191a04050a 60
    0x206000a40000d0240d407425581c1c2c22403800000c6241e000d01c800346c000d4000d000382c0145001050000c40340014950020064020310420008000113840c40d00d2980c254581510384c1d07600081214468224030940c0e600940000c401c404204065106050542e0242d8000d0f0411001d201444a50045840024810402c5241044400f54030b580503507000038440c41a142d030f02c541007003000c0c03610b002039880250910040b010808060300a1041c406042d074140c6500604046400c100710300bd541c000c407032a026084c0001c10501d03141155101000d0040f50701810002d202e50348c00c11807803007200c60217a043c8040700071000c0751382801d41005141001200304107151038200c10f40c0d411913245d0081541400001161000b20348150b440b0b5140000b04642603500103600c0d100f0714100f01c2512404030100703025515210003846018030100780c0040d8004a5040b4840e02c11380b51503d0b051031004102c000da40c03c1d80c41420301c8208400825460b0525000750310525611400c071110180c1c10030010700c1500c0d0000300080b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 959397517 1250 959396267 959396287
    0x510020d091a070c0305061906050105090904030e06042c06030d122703031a030a060b03031603020a15110901030518060109091b0e010b16050d090312020d0203 70
    0x16260003008802c003441410005240d94104802c0c3c91a082250035400c10f4041240c003206000307095458030291078040c1309132845c100c000b91031481444841e0340942e05040002d0f00341170092240740704000004d4541c5a489503500098401041e8a40d006030707610120b48000b400038481c0c1c201b034901401004001e8040040602425100c2030705848100380710030380301c01c200203060303000702c0e5403802200003115210402d007008c0c038005045a90010b95480c0c0c1e20988408060070b500c00003180e004095020b0700014100382c10100003441c0d400f40c000211041c042d510302241c105a4081030506041d48114404122088034004400550f064940040086407080c000d0b105190310a40140fa00f00c04484032020894800d03c010700d0920400b40c2128070055200c140740810010602c05545010403070f801d085007007a040c940c0034a10f2a006100d1802e01d00b8010035400045440d400d000610194414115200c0c61502d17200940f070614980b005941c101100d03c00c07680050300114801106c81e681d64091071a02d05002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 959398767 1250 959397517 959397539
    0xb12070e0a0f02040e01050324150a09020d090201180e0a18020a0b27060702040213080d120e0d02060402090709030c08010504051903021209010302220510020d09 71
    0x80c1a403507250344034400085014034900c010070181000c12a02c1c40b0540c10001450b00c1e041c04002c201202284a004d25140c6172606042d1640040e94010000039842880c40003561100d03280e00300854043c40005e0034440d00c161648410560fa10030b03281c1d03410152030f0708810354401c2070b0380c440c481500c221030001805004141d401042c2c200b07080017000c0c03c0301582c0d4008c1943c140f111b80110590700c03000030b00d00e410024030a6803607587c03000179524005c45d0340c034410100300f49000d080340013405141c000c192040c1120f014240c04024102e82c6040301c0c5141060803004158080d200400d80f05a842d00c05080040d26000c03c0b80c03261301000d60000c00850302c3e42c2c0d0a0041c024401060030081060f018004000102480c024400816800c800440c0a0905017002800c081000c000c1c181035400d00d98400c4000790f000b18010191812400440e40c40b01c0030000103030080d101c0c40451299841619528404000030442138009132001960102225000807805036691451a4510f40115403250750401c22101c5003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 959400017 1250 959398767 959398771
    0x1801020706020a110d080706050103050105150a030b0a1b030606170105101119030c050607080105130c210e100506010e0d05190302030a1404060c030503060307170706030b12070e 78
    0x64211100110240c132900161f41180800700d9a0a80301ea00401c14003009009060b000402e540d2814400d001c818005083c401c481e01c03005069468050010300d0b03184480e800703150201c1d10301803004c103100c0310003200800520750750055034007169908003490600c00602e1001030594402a100d154115200f00c000d407500740660226000034441c41001605c220000818040040c0c03181c0c58144030070032540350480c00d10500070041c0040040c0c2030300420040d542c068990500340300d29003000400c0d090b40b12080310007850025400f400385d00840c0309203e6074682580411b8288080310103680740345508400a07015100207499040c002080100d150980e864114098003115205404950010010110300318510100d0310781035025800205002c04503c2c2c00001116480100c00131503803900e824240c011700f00c41000840507041020120005071283c0f41004076030003a00f510401585480c45201c0c4090f07031106039012380f01c0040e05202c0c40b000517040c00300b0b881504681c80d0024000c42e60501403e00b46040340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 959401267 1250 959400017 959400019
    0x3060d02040c0c0309080102030601051e0909040f061b020c28090920100c05150a0c03060e06060d090305041809061d0604020f060d020408031801020706020a11 70
    0x90408000140e54034800c0d6104040641c581d500c0241c96414050050349060740306800c240d00400030044140c2c0d0003c11030300c034040c0451811011440c2d4103181001e138006c4030a1a500302c01d690b01400144006d9255410016111b0b041c140706016885040c2200b01d100c251558025920020001c501464504085091840400b15140c400e110b80503590103200c0065206980441e956007514040c8096007442100b04c00000c84040c030801d682102282a848012003010704002e4056185000c02c8014406a045901140ba43c0c0310700b03041c8400060010510102040301080c034106000071401410001725114030307001455141001c034481c2e0414050202c0f2001202004001c00c00894800b1148510742401950b0043c000341700500c82c5040b00444203600c01e4442d10302c0c82600920400070000a48960159058807144c1603c03860310003280d00c0b806581070200b94103001050108100704000050100c10300031003400c1c5402100200107a0b2900c00d84e00910005803c180d22200101c1d44010000d002e082d8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 959402517 1250 959401267 959401279
    0x105030903070b0a230c03070e0d080d0506030f150103080c120d0605011d0904060c09090f0506040606050a091e0504020705010519060503071206141806091209060306 73
    0x1540d44004603003c0450340100c0b041e44c1c44480210503c140601865074000020742c0e85d00e10b0074a80615056400000c1c03242c01003080c1c03849041c00a840344502084080d40c0300341031a46400c04200c0701000b400003103a03564064441c0d404089512000002ca201070032241c00902c0229908644070031b40140d20020400005204180f030100305904e0326030042a070183c00704000200d09040100050400d080501c100c07003108602660b03402640d0b551880742f904039502010008031390584002c02d07a590080365005940143c5800364607402003456810075407099008560800842e40c4403042034a0ba4003417120617600094021105100c03034440c21081c01c45c40308480e40d49030780ca241d803000010282c1e805420201c0301c594554007400038402c03000d001480070100001040c0411818600429503804440c400d01640740704e240e10400902002d40c0c131412610030b00703c00701d003620300d4000207054408860714006101d5104982c0014102500454401003882c00c220302c40703107003030b428004100b1150000307810554414 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 959403767 1250 959402517 959402527
    0x10623030f0a0c090f020a050d0f060305061f0803120c0c0c0a15031b14181f080c0a09060f11070f060e06040b030a05041b0e01050906100e0105030903 66
    0x41c500304aa044590320030b500c4010300e50304003c3c1800a8407100054004003600501071200980d400c4416501290200c51300015a6820442402e0180441754805042801032032305002604021404055540440626004469070b949003956540d202d0696251b4001014a0204aa40d8240d400a045600040d0200c1e465140300c100044d8210040342d02c10410034075004a078422482d0513008002404845840c0c083c440398008070701401d52400c01c50000442440040c081441140000e00708100280241c00803545a80d02d508480a0f02c0d000020100880e0242c00050000e0740e0700001c0320801e403055078803a0303080d81c03030708a09440b661443c031081c1301808150b0900640c0f5000400c000c00090140740010300d1024a02400a0005071012911500408007003009104000400c0100d0ba004202e0190000d2586c0d540d04011142003200490301d0600801d906000505911030066281a00d00465040311241c0724031040000c1c80072118100f10100342440c058400540c004c01c091750340100d0b0402981d11300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 959405017 1250 959403767 959403793
    0x903131d060d020a0803041d060d15050714071b1203050d09030302120907150203090312030a020403050f071404090f02040b0609270601050a02071401120203090105061201062303 78
    0x142c7c00541203ca4180d249401600325000000943c44d00181c0658000300f15121382d1300d6004420001a110058403911000440d050512542203d01282810002503440d01141e01c0c00c56004041516183d40c0314030b41d40c81c003040a84c61400c0c81c0c0e42c03096046d00c0755490310301c040780c1c06005440310001c00d078245a8288620b1214007511000c0521814000010b0601d0706d091411144078169581080800c640c000e007c1d202070754400141c1d482c2070794451201d05850b03565490808004e0f10a5410080190260702400550b1120000d100401d0b22000c11000102c0700d850818082141d106117809030010a034110084c0260600303904c00280c6d0070024000d50b01d0036108001040010a8402c0b8100054041000d4a000903544039059500f050003464044d2030b0901395407001355203400070f004001400001c410454440d80c0a0f00040418030b4030010190b441c2d2410f00400fa000304811108140201c0690612450400040c810941a19041070356060000c206485090340c8008000c40c540c2c040c41510180010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 959406267 1250 959405017 959405023
    0x12030c080d05040605010b030702030a030e3c21160b090a050601080111030601261510030b0a0b090a080106030501051e13020105030402030102120903131d060d020a08 73
    0x1460600700004501401c29191203000c5030381c1644600711019003801888000ca43c040b0454030088103510f00403030072022842c403642c01c2003ca41d00d0412014441d04401c1e5091140a0310340c0952039112415005e1074080040950b11002c0403450b00e10743c0524064000b03014007035580030381205008000c03121240c1c480c07a645d01c00d0300e11050741d404900d82d0026031800100310702003004030301404441000740720782019500c0d0031a840c0800342c9001d05219100c403400c03821040240d156908681400c5480041d1708001d215413840c5105080c0c840c5c02034504a5100d0380080c0a4042c03101094406411000c1c4c440ca03004c500d6889411034041d156124094220001d903291090040350701071070182c000041d46003442020302603034110700034000e46200d03490300420550111004594501940a0820550381ea5492000a009220b2041c0c0500d4148021040c040c0d003100010241c06400041e040402d03525440e40e241640c007106003c52a00e00780321050025909080c031600c0301c604c151025254103075443d143d1905600b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 959407517 1250 959406267 959406277
    0x1e0909040302030d0605032116061a0a050126090a02031b012a08090114070b01060e0d11040207050f0d024219090b1f0f12030c08 57
    0x1005a00c0030510040d15115886100011b00d0120b0003424503451541c40820f9265180d0395800d400640440c0665040f800400c02c0c441142e030090007002050001d0700c021030301201c004081c601542c0c0c145404940b55020703083c04400e0803c901000c00c5210740b10300382c07854107800c0104441041e0048100160042c4c03020449407502c0d410680c14030801c07408040006044801d500c40417a00300001c042c000c02c0e03411140001c1c2c2c0400e074022a440e40e4070078034280161503890b1060b40f41042c80ca000200b0b035040c03080b0550b085068440e01d5075083c600d105a0380401040708414640a8803880301170196039400d20340b40d401401120312520a4404d09060956507908010210340c4d03201c0903810142035110b01200c84282c810080716900444c408049085101110303d80100d517441883d954884040340d2040b140400d14070203a0204042441114690701d08400c011509542c920340c00d0b0a02d20340d000c1410100c00180c020340d8003406031201c0c1b032071401c803445403030040d101c100f5414041401c018001094645000744 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 959408767 1250 959407517 959407523
    0x20c2806060905040f0f14071d09060103021c0501060e01030f2f09040c1703040611011109040c12020a0210050f04050c060a0302070506010905011e0333060e0910111e090904 76
    0xc0b0052700c00d0640e55160a004083e00121f401c030200510044e52900200041c10b860340ca03040021a0544ca031082c01800b01d504803a4038400d8400000081008003108100020f00c50310582c3c1008171030000b0500c6c00d4a40d09070f2034101011a107000d403080d050444050354418011402044500e541d400c6a8610550060110515400001e8244006a0051001c010513404d400081002058201e0344a42c0c500402c0200761103a40c489164200d070038865081410b03403025141e800c56a0b05000307407029503510903a440c0c04820318189000200e0362503580d10128482ca8021019044024842c02005841da1200c0b64080c00c0c140d0030700022020800401a0f140a0140ca440000e195410403c801441303c20a21a8500520102005200068401c4104030400964005101c00700200841d500080f5000d584400b442c1460100006088074a00c119240035000391015202821070312582d850541c3e841403400b446207202080f034580c26440c40e074030b100742c16016050708030300300030640c00010705089050b5802c1d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 959410017 1250 959408767 959408789
    0x1406010f051002010209270f04031205130c0b033102010c140a05060f25030e01021e0702011107030c030305030709120c150f02060a020c2806060905040f0f1407 70
    0x1803424060300001d442e0700252141d40030349280c501650024041aa4548100c8245031503801186241904904030782965900615040ced0f641d4840300d4400380390f0811a0003c0c000c07500021038600c00005400d40700031500b500802d4002e1610343d50019104648a030404581c1849801c010308503562007072091031052482140540010300b03040c0d44c0b400c1c5010b0702501c15100325440843c40341c0708503420088081d0b214140e0401280f8034507480c50050090207103a05507000c08407240000c0c40d2030003648000f041e801d40700362600e8501181122400d995503d0342e001c000d122240401081c00481d00410196070f020340d503490503c1105440e0b01040440e0080c6450441d13816002e40410b0010052282201c2c074100903524080346081c070a0100299610300241ca81607c83d540011140040d071070a00081d81c42c02210440050740074405420b0807032550303040074180c0301985030080101711441c40e80074032405160840c403428102d038550389074040c40500c1c00008465451030312a40001c10300c02801a24014201c0f0890 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 959411267 1250 959410017 959410069
    0x203161b0f090c0e03060703050417070510110c07060806060d061202040f021e1b15150d02090a05151e01030501090b0a03030c080c0102161406010f051002010209 71
    0x1803800f0b8a0f4003030907240c184500203d110000b52400182d0b2030b889600c0c0c0c6004a00c0ba03c50b07040203040e02c45118088207260384005042802d020001402c9011004c3c6181c0c2049000d07681c1803100c0da907000e4403800b24000e40200300c04201440c49004a21382006006110303d1030020040039100c101d0b4125800341c400310420540b00425440c0c11701c03403801c00c0c100130f010944c90200d18491040040f490030414034001a4089001d000341d640785280110b0411144089030b4a4030f00c49400868001d1048807200c05251490020412a04040d05e90015869015010b6981501c40c0c001c0a00035203030050865040c8042030f80c02c1c1d46a90303241c44070307202d000390420b661142c07040f082c4000509a070320580210740c0c81d504101110f011034030380400180c102ca4051401242040151521a049101d240c0706c51700c03e50300105241140c9280d411006248500c60303020007852a10701024540ca505091144c1c0c06a0748020b50104040e00341044d013141002c02c2031000602c1c0c686c6c01400a0f04104640004404c00860030305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 959412517 1250 959411267 959411279
    0x100806100c020f100c020402040611060106031b260a020d150b0f0f13030b060a0e190e0a0602040e01091d030f070c031401141005010203161b0f 63
    0x20303540003200207807500c1100319840790041001d4000301c4410302d0144545140e484040d6110712243e50b05190300074010743d071300c5a035413400a0003003214100403402801988000582d40340640f06114012030200c000202217900c607201500c006640040d4030a0703c501107450107a80d001d240d0b650a00c141760640d801a200c0d003001c0451401c8540c0000e0072540184c12903414010711141405451604104808150750b844000041510500503100f50f403180114881003c81001441c582c0144240c4007900d195118503a03400503180da9074001e0301c0380c1111381082d440305031641c003154110088240e00c1004030307013030500603680e6801242e1080c0d12200c14070080500600c000d06c001c1c00344204080240d01000010308403c64201d80340e1280c03019180030300300c000070f0ba0002c100010551400842d0840c4424851240003600180a08800000d031103c0144460019031000004044075040e1b0304182d009600344111340101e07910266503014165042c0c10300c2c84986055165100010014180004010305040e02d441 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 959413767 1250 959412517 959412529
    0x121608011a0a031203110415080c09090f06060417010e070503070b04090b0d0b0f16035117150f0a1b05070b150904080a050405100806 59
    0xc51000024080c46141c0059a9030b850300c044140d0360090745400426000e141c00750000c00c103480d18060300d2400418001218044c07128852810400c54541e02100d6940790101e140c0780c45080c8001d6440450040800c7e1100004000d541d40000e01920013843c00d40c85e403002ea902e8a555403100305043e074444201d15000041800080000d15051b002481501c3c00d101c00110b03180154040d403442580d8501800d2101c0d03540300700700102c660300400c07a5110b9040c400280000141c04407221080d05039500c4c12102c03164440d124071480c00340260070b40794044507000240c0a40444c00340d80200004021000522409006592811030190700e03103201049501c0c1800c00c6154844400710420745030481c5403403072003c110804070154020300444501055945580c0799000a00b5040c0410400b001030180040031a81c00c4001000301d94000c0788040010b0f03446114646810816851464101802401140024441d4409801310001900b0003d0070700707072036402080009e04402e154000140300c80c4240101e500b411 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 959415017 1250 959413767 959413781
    0x60e1e12190c0b13050d0c1509091802011b060e0f21040807170102070c0902090f03030412030503070c2114270102030405090c0c0f06040c0905040212160801 69
    0x298000c6820010750301400c401c225000d1192a029803004180c4001f0000e8500301d01d00503020490800803c0d00388243d0042501000d40580700d00e1520313103501100e03003110b280c18201e0560f41c165214910703075540d61440d41030b00380c44400c100c400740c0e160011894180002e210030921051284024104209461650098080c070403c0780207141c2001c20090041c0d06020803d801640c403070440340d01c084c40c0030030342d0507009101b0200301a0509020310302c04601c60129070010001644111440d0721742032400c1c1c0805841e80315074844d40c006460201200800640a40b024641c080d0041c18150406500c507142c4109541084100760000340e402400c0c41180c0d41c1003aa89800d8802d4240c0c42030070030031400500320792110350f103016200108004801c408aa07108004881c05003802520821043c24441d02503590742e00580c078000400e008424410191210000f0000d110310b401860100c0f030740b8038112a610081c1000f5000380e0b0000344000c40b6074550001084100500c2c1c510640521080d440c103502d4900f11050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 959416267 1250 959415017 959415029
    0x9181109130215070b070c050706092102030a08181c0f140705040606030e0c010807080c0d020906030f071d0a0e0a021908090106060e1e12190c 63
    0x1100d050001c0d401030202103248881d41035601501c01100e00d650144903000e42c00e4001c02498081080001840c0e0100c0784007801d40c8141c04842c00a070306c54105440d00043c500500c40300641c03903021030368041c100170f03084550709001800381c500c000c45607241d95016070f009100191028404803c076586d9810111242036280d5503030891241c02e9111030761071404c018401c02d00500400710381140c80720704000a000141c000e0600600c00c201d01541d0302c5003d0040c00d240c40840c0031074018001000d160394000c1c0d048070f20802d42c41c0d07a03011450f81c41188110145d00305d104441c000d613a084c06280d61a03105c05000b50300514900022054a00d04840f0003800c1564110449290001e030403040481e40d2141c0044005444040b455034005561b4014410001e0150840600f46016041100c19800350090303500d6003d05580c0e0000e00c90a521440242e400402070451284c0128040d00071880b911750b185540c070b684110050607840310090401c003c5241405088180980001c60b407240300800009000c1c0c40300400d9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 959417517 1250 959416267 959416279
    0x106120603080405040b011125080c0a050d0f0206040b0903061315090203120403120807030e0a02040e0a1a010501200d0327050303060411090a0506090406091811 71
    0x4156620b6103054012841858000ea0300c1d917203400c48980c0a5034620004a054004403014010304100300c0259143c4011045135103140030300c0101c2d0b0654040b4808202e903030040c00302c800042c40c01c4244040a02610016a0914807100d800801651500010f10050003502802d03603c1d0410b81040606000011b4140e400002592a0080009200c058a0703a0941513a18002901e442240003203401c0481902030350318602c50001d80407041003c1401400d200030380555a005540d039400700d0a1b0200c900c00a071311071aa40c001d070400001032800742c0104a480098105503500380e0159590100741c8034007201000c41003102c0d01e00602c10f559000683d054010050710550017000640c6443c1a201c4202e40c0f0740c0020113482c0d08a46d0500807048030b015404040944085000e00c1c86030030450b8803500b09449942c4154101018031110f034002c0350503a80722260050110006526080070000503a10980c02075401c9502c1c0d000000341c10303c4500c124013509080f00d402c8d40400c0c0c1281391040c0d800c0540c0810030301c594 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 959418767 1250 959417517 959417519
    0x52506030e150a1503060f05071b030c0609111f0813200d0b0403030605010e0a030b16020f0a03050904060e0921071e1406161d030a080301061206 64
    0x1840b8055090300200350600c0080d01030742061004e120507460750009071919007440e4180300c003200300e0780c8903601c200201c4da20003030038013201c1801d1142070070f0a000250000380b1506084003c181c0583c40381148a1107074084001800100000c10010b048400d03c4000320300020742054907250f007250120380c6c000508480c0710300001715030380d4030140482c804c00c00c4880304642d481c0b4a401da0b1903c00c408100c184d0485408001e030310f000c0ca0001c010705024051580003c0d04d18178801c2c02c908104c2d0311581640c0c0d00c4004588180e40e01441ea4003000c06190580c02144504221183d05003401d1000ba0880f1703000c1d41d40c05a0b600044010300044d28515032200b000c1401c0c400030010580c0010a8021003030442e00c10314072440c040c001c0c4800031703401002805880302c1d510b40c0a40200c04015400c01510307504c42c03c071644580401041d000d440301c41c212841c4003144501c0c18110403951258429040340c0b2440102209080403090100e03180c00c008220840d07a41c40000010300c02d558100308200340d020300d064414000c031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 959420017 1250 959418767 959418793
    0xc04052206080313060509060c0303101e031203020307020111030712110403110105070602070204050f090f060c090d0203150108010507120c0203180103140406050114180c07052506030e 81
    0x44e2100d071143c0c504020340442d41804076a40c201c00c072032503c0300d0b082c2269101d003084030b00c20f00b0728a0f0910440410620041c614200c014444803540d0407a900075115100300000c800d0b040c2d002e90300c000c0c014002c40d582c078900327401c954510202a40c024040c80d0f9400d0301032030317000720101c0454055240b8001e1180c0140800c10018a5441e508409040d0a00e419a1240011f28240d806030042e03843c025481070508042210107101c0b41714040c460f4064074200e411042c810001c031519132105485c0200002000c01c40041c0354280790301d4580982d44098211540700c05807056400d5039181c280c00108031039461302c0500215540c8061505942030400e042080a800440c0c0040e680f031044510304c40c80c8840c0307002380daa0075038000e91040d142e031070b1080410080d510313040ca8500000d090074007074141070303009110308145517040081e0303007400c203541181a9060907106d1040c0d41c0d006408c9001d049540c1d00c00c0c0550600c0000302c1c0500f4000d41e9011b03040f455010303801c090000c0d040e0740c012601092982c0c03041c4000c130a8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 959421267 1250 959420017 959420047
    0xb03030a051b071502070e150103200a0c1a062110150305070b03070f140712030902040501120c030807050c1002060f06060f0d091119031a09030d050c040522060803 72
    0x1908d034090a00140e40344c03003254105010303c0d0100d8002890740011400c00c0f200ca400608a03e01148100d07544101c6030161021803010ba9030940f03072250440c4840038441840300640c00e6540d203a00514003161408070b2100400fa09a9040c0100c44102c0c1c1c0700b4000800800c0340400005000e041c2000200b8214034020800903e210204103c484c00c10041d444202c40403645035080342d1349180c10030b448008000300070402401038071340410101c1c0110b00d881c2c0006508109407003541d4900fa803015241c82d0075071440c1c0b80c000c0243c001d000c1c1952035000c1c14007840c000d50707074180000800114039005440e00d880c007041900100e502c001c1c80030f402030100700045481011640c003215194000d1540005034100c0c04c0c1051075250030415020b640005c0c0b41c000030b403050720901ca00502145d115203455440400c3c008010300102a0507202c0241a500034803040b005070007281c020355030114420010b41e0405554038006090180305100103496514000800032125400b40100005804e150f00203501e4401800030240c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 959422517 1250 959421267 959421301
    0x21b1002030103030f08150d0b07081005010f11070e0f010e0f0c07120e1302040807050303090306040201080a0b13020301060f020109110d0f0b0c090109090b03030a051b071502070e 79
    0xc1001b00c00000d22004c800603080314820201801d00740ca060389600c1c0c414003100045d250000860300350000103a1100550702c2d1401503a10607500d00c04c04840006c0250723140a56000078250900820002050f100342e207030715052003004800c0a0b840d50354900310440c1d4502c174024110070201440d020802c8165032002007100d81055120301c009555000b2400c02300c643c42140d0b01d242d075004000f045032524850b0641c0280082d265000300383c4225a030766404040d030764030408a0042d00340d0403550005000d90300802c00940d100d0300c21240440c090600c48000f40c01c103031800704800d000c20b501000502c603066201503201d007440c00c6d50008000d800008c0c1c80b24001c01c1d94001c001032007410300191038003c01c43c2d10081d000744d15a01181c100100d050040440c62150009506640000e805901c0002ca5494a0103890280480030300610314050540303404586540c00305580c140d29410740441c140150078108403002c02424440942455203421110090030700a855000142e1078504505103e040b1044003500300d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 959423767 1250 959422517 959422547
    0x150207031b0b540a05090a0c11160f050d0f02120c0904111008070e0103020a0903150c08130b06060c070806010e060a2124021b100203010303 62
    0xc0d020f607900d0103c050324010803101c00b45104000280705800c903412812403c0590108036511456103840d0390901850521922800e6030010180740811442c1c080c981c03086a0105103445c0a0401100d5001e42034a019070100d248030361060005400c10405100070586400341004442d0704035480015124141400d10408000c1c3c407820620680301103041d0100a003107040030b0090110952481c05003400101d01e41d00f00b20040c003442c050b00440031414450444241700c0c2c1d60f583c4440310715003019801107000f03400c20ec040c5420700864075004400b282841c40207400c0c040140358007089200c42c808008140200203040d2002c103065074103045001800911040c0d61154003510442d8642d503c1880040c074044080c2e00c0030342c0e1402581c001245026203803038032600c155001c2d15841d84890703940100d410520075200700110000e184015050008030980c0b00405c000c0c0a00c00d100e00d590805100000480e40055101c0c03000c2098101402d030880b00a10042040d140c0c2a5400c60031507241d40c4003d48840c180303440207 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 959425017 1250 959423767 959423797
    0x605061b1605030a0312021c09140604260d0204090507120c090308030a1b050c1501050d0809011101060611100902010c0212010f1a0f12070519150207031b0b 69
    0x11031b880c00380e503041c2c42110015090070300001c000704007844001c02c480e20054807407801c0d000c0380c00005100061090b0080758401c0d9102d1200705085940c03449140403540a440c00c4408000b1030211300c80c580040c1002e030000f02000900b034203051502070300c2500aaa44402c60340d040040b01206207030004120401c40303800c1604190b41c1d550310100c150081104500c030300000002c040300601c0442d8840084c4c50303184e48550072280e001341c45c000d038030021400900c0380542c000700c2c041490740000c07400809000d0666040c1000c240c203d0000c0b81850a4900c80c2e000380d00000c41402030010102420464800c0e01111080d0810a655007a00001c1a03401a283d01902800d15402c000c141030209501c076481003d00104101300d0388620421200150202c40b61640c4a03089800e035000d081e10b418401c0049141c1942c0c000d00c6428501014031010500f00070038800038045440000401d4042100001410100d981c00750040c1420b41c40c0040901d240c02540e24603405503d007091149103864411200b40c45120004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 959426267 1250 959425017 959425037
    0x3010b0f090109020a090f03060e120403171b0703110a170d0804080403061424010206070e04061703030103030f02120901180305012a0c11130605061b1605030a03 71
    0x19030751036025a200c141c840d012001f00106014842e40002d403810040f2080d20141020011150350314007542c000030b481d81d1610308491609405100092245c0000040c140c010424024401c1e4207002c0561700a41d0b9410040c59503200524007584008060070b003070380d13000c0340c58100d50031060b03518120700b04160300f03011070100800d05000e041c0088c2e40003141d01000c14000345c080740d02050020b440c00d44000c49800c0034080300406000401d140c100002906034002c002e90750310b00d002211000010b020490304650707550300c0850035500712881c101665038140c009598951451800801214803a0482c42c01c40d0003a082d2110354040b4801281c91031042480c0c00f4a00d200e100b42050206070040e44010095803a0100454003449a03d0002c03c1150001403544801c1c0080b04068135000000f10f0000c1c5240c1c00d55199411900d480014848580419500007690035120340124034680c0c8010342c11400a8102195501c0c1e02000f040348840114405040156052424010a0399082c1d1980000c040c0120294 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 959427517 1250 959426267 959426287
    0x3020405070216150e0a0308030604090804050a09061502030a090b09010207090e0d020d0906020c090a0f0507021c140d0f0b06190201050135100c03020903010b0f09010902 75
    0xc20306041c0107101c074018903e54668030713110200d1101c003901021402c0b14089441d1840d005105108a80c0c0200e040b51441d41d50b001000010a0744d9003088aa40c403040c0000b00d12a16407403215000b0340705544000591900740303108034040b40940c0011004642c01046040f801540c08070796402250a40b41d150b5444160041c0140e0400f08903801081c4158075110342055140b2001485070103001c039540179501d04e400004e404544901c1d007401042c001d64000c2080e99118101010820fa020034080c0000a0544203050b1100540e20180ca100c0e0050b4414130150501981c501d00e80e004d070b40700b2410440c003002c9019020003c503001d8844590744030343d07580020744003c0100742c000c140010001069659100703440207800d200420b9a00e0340e6001586004004280e80629000105040032119840f400c600300500641519050000c0750710200d000301c0240800760100c82c0900e42c1043c14544001d40c880911106040c2100d00c1110010f20a8840b001040110f840f000030113415602c00d0b450159540c5a482 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 959428767 1250 959427517 959427523
    0xc040b0f13020f2107080708131e0605010611010e0a080306010314010b0d15210206130603051605070f0b0a09050a06061a211005060c0708060a15030204050702 70
    0x3581c900111400540c0c441c6800b03000d0810941d0301214900312540d80c0300d820341140c6c021000c0303d200c1c01050f07003100440d030b15660074244048540c2c46480341c41403070b96016040e02c15080c40321604580301034540d8010302525401054040000412000805c200040300303071b10030781d101e110410180c000f003000000300340107920035001761041c00302440303040e482c0b5690340c0c4e40510654031110031484124640094101c00e1609140000102c40030701c010124080c001b0035a2071008141d041e0100c0e0b001004000340b01c10b41e0311000c3c0303200040c41039840001380d5142542000a00c24000b80d00d8070f04010040101d50300240c8000100e0010345d0300b28228940c6aa9298100300c000d00c03100101a1a510802116004000258000600390b46154100d07800c0c46541c060101c6260265041c603044010300d48404070101d8141040066000001c00f062118041c0d4560114a642d44401e9502d0340d9034109580a2211101c204203032504106800420003494082c03840300c041c6030b800d5000083c452611540031a40c0a0301c20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 959430017 1250 959428767 959428777
    0x1b0c031e030a21092001030e152701050702101e0e03090307080309040606141e040e0103050a1202070b090f1219030807020610031b08030d0204080c040b0f1302 70
    0x140200130791880350a0140901584003c0c101200c13400c07840186a5500c240212036240300504018600310146251015a03150000c20600092003600c00185900101c01d0480c214182c0d00c0d400042c46003082e0030300a041c441581d070451821418000030000019540604d80c841070310800001075040400c40407030342107104010710307194580700e41000070500100110003807030628800c071010014280e80e5a400c0e1100f41e00c000416890141c00d00c0103d4104204c06000400b02d202c00d41205d280c1512025001484076081c0c10945071a48102c100104200b50340d155500041c69074001082147d15024100049210f0659107078025948400e1180440e00c3c1c0b0500752a5001c510300640da02d41207299000140e03a0780380c1000f500090b0245020510082c00812424024080322100003a00d60841d01d803901004101221081d502c1680040002c0b410310034000340184949804015907624070384800c80749400102000c080c812454000310354216038548440e041400307400d4481041c04c0013145800340003801a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 959431267 1250 959430017 959430077
    0x9211a06150c0d200312040309091d01230739021c03120b120703140c011e1b1b050901060503040b0a111b0c031e030a 52
    0x40071940701c1000001080025003490141d81c2c4c0100311090310320711807100801d05100c04c4a13400c00c000c4040901c00c203010060307102d400303410005c00c640d40d503a68040449224001c940740031502052100101e280078052602035041e0307499500d07c3c041d50070780282d1200901504000520060140315083d0083d00d04003c00c2d202c3c1400e686038041c20b450304045105154000080344151484d00410400040105c0c0200e03003907805a440401800040c02140010f10105c00c0b01a48004240030ad5600341008012803405503200e070b03110026042ea070301d01140c035010740d15603068148100a42031007101540d0302800c0d6100710076460308001d00b000300301c0d06d00c402c02c020031006000c1d1424a0030240500784030418103422500e00b919014583c0e80d03180c00884032400140c5000306000c043c0f02c08940d41e01d00c1c40e0002243d181d02c02c602c0e240b90880c06054001034000f1002940364581080892245500e000d00507054249011040c0c021111152210343d80c90f480364031903600c240128840d01108401404230f00f9680c0c919 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 959432517 1250 959431267 959431309
    0x30415021206090a14400201030207020409060e0a06050603010c0c060c050f030403020109021c1a0702010b04150e010503210f04090903020c041d1b0312070309211a06 73
    0x4008028040c0f2903030454802c01c8140d00c480040002c9003079406d400e4200300039100344080c400301c0c650046011354030064041c0d03407246c0c89000e2200442d01601c240d401801c0d00030018030042070107141210945800a01441c0b10341d02d456030407220f0581008001010a1b071259000609901c154815203c5000e0305128082645000c8100810143c0540c013448940b40200d40d06400c1c81c0140031124000d005081000740080b400c10a006154004206030030382000460001042e102c4500c1c001c00c0c11110540071002d21150749282c100000110480920f000d09030542c050250300c054400788014420b403c0d00a5a4a0039000609031096900d41e002e403005080c800d80240064059814000e54425014070864422468440301e034030800d050200d25051104000c014107184002400040130055044e80150b400d4000e51020303003007a01258006205080c4607480300032150381401d900244400c1441c92014032010b0122000c40407a00c0c0000ca1800c2d61002c00d1904901c0ea2150089503881e050100759940e962 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 959433767 1250 959432517 959432521
    0xf060806012903060604121106030a02090406080705010219030c0c150e0307030201140a091706040302120a2a060f1e060e0114010c0b010b030415021206090a14 70
    0x198940c82c1c0c0d04114038811403403040750504003032100d144419115254802e404000c02c010107c02c03401100c4200e401034001402c42c082840202d5107541c0219840c05100f54000381281c2940303424860000900402d400074540746007813400203035032034a00c0e50608241e40055111842090b118520060a859002c07070b0038885255074803103a5001006400007040841d00316a0768403824200010f0810440750141d6610420302c50030407400c0044d80c042401c8204202842c0e0010402500c520f0400140c801940010591441e160400a003404481c01c0d000e00420b01c20400f40000f2503101801407a40300aa684224090f5140d0320220700702c6149074802000d2901b00700c28070503086c4d03540e0711044030042c50300784440301ca2003014030583c102c864500403540c201980600501c14003400d9524082c0055041c180080030341c0c0c0c2c9841d4a07029070400da01c00100c000d8000100410011040b000306403181d401001542003400b01c80301c0360100d4400134003450084103840001284004d10b5002880d00303041c1c120a0740100c3c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 959435017 1250 959433767 959433779
    0x2105071e020c03371b1d0601180b2101050105130b031305010903020709050c12240a03080711010c050d0305071202211f17030409050705090a0e0c0a030f06080601 71
    0x44005174658002049640c200084c5480040f2a001580071000e11209000d90700d50f4010b568034034600440c64501e40c0203000c041017214035003004041030340001c110f0442d1000c40b00c40c1a400f10708160881c0c0d04104082c841455501100d41e1100181d9503050b110b103840ba0f03902440c0d80844150160007905960030040c0c15014107401048120503600d00706020b0003650f68051300c011661242c8810b00710895076400000e04c010400242c0c01180c914800d0304180f0b0414840c0004880031402e410990b030700c3e240000c00300100294400e5040003842d0a0810303600524042c0c03500c0c0c1d102c0101c40c0382c0c14103140d1608002201d6034814003007084910b0f00e41358110b484805001c006026170b007521244a170181d01035800f00c1c1c0390007035000549a03914001550303040440e050041640010549115112040c402884040740d00e2010b806110b01c01c036655500e00d40c5038000681009103c0e0340030341c00014031500e9a4113000303004085e2011212100d90034100854101e04208090008101e20752003100c1a003d03840002c9a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 959436267 1250 959435017 959435033
    0xc140d0b220f0e123018010c180506030901090204180b0105042a050f040617240103020f0c03040312021e0d2105071e020c0337 56
    0x10746890b0201007125200ca00300950f40c41c0da100340c9000540310140803148010011800340d00b1281d2000b0f20003031442d442e541c4028010350040d2909100c4140d54180600510424404c4a40305070b420b02d0070001908030250344114450650007642d010b0400000020840344094020b00d12950340584104540c901d4200d20b0b41e960704d001901115030060043c0001100e00d07050040e00048411f441001b1140d010940445441058000280c028400180085940401d82e600544018006a03c1e10510000407150311b4100b0344000f042c2c1c014005000d0880c45810f80c90145201c4000001e080040c0e0f03400301400d810031140a030400400c0c1500c00010f011080200281e18440f4203031850302200c4110510200c040716001d4241800c5080303501200c4044c444034484c1e1100250103804d4030708040f0104484030036406444045810002190005141c410800d01c40440f01c081411148082c00c2e11082000004e502c3e4051240c400c0c07203c1c840038007404149000743e650007040ba51442040d1054104500c1d01140c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 959437517 1250 959436267 959436281
    0x32a0c1401150321090b16150c050918130b090f0a080702180f1b0c0f2107050601050409031103040e060405101d0c040807030b04060c140d0b22 63
    0x4c000c2c03200c0d10003205075005144450070354400c00029410b1000c0b00d440c20311102c840300015608040450300e246a0847c0c64855a004a8801d6a845a0300d58004050040d5600c160000c0c0e5414440f100030084251190400c21043e00c0e403024014203035455610300c6910b00621550f02c42c40d00d014031300310700041040c1140240f5410b032082e5645100000700342941d49450340300305d90014409514000007032100c0129030501c00150290400142400d05411100c0c0c40c000601207400103a6000d083c074071329a12020000000e40520380190307a45003402d181d940d940c4407101885840e000319111003141003003500840c40c0c0c00150700b0000c1100d44940d0f0311280c2c0c20072000142d0368540100d05d024045640e241c07040d0200c6082e140d034142d400b1924095101110103218000380f094410b441d0602010030410801e0015800841c0507145141b25418a4103150041f202c8165010052040c0407030180c06460206040d29403481d1402c10000d042c2803400c001c50701a012644030040f2412564010f00604506540a05 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 959438767 1250 959437517 959437553
    0x120f03351003050709020a020118140606030105060d020f0307090c050a0f031104120c05041802030f06040b13060f020406090620031c020c030a032a0c14011503 70
    0x26035141c54407140c0035628070a501002e8200e40114106115414641d0000d0030703000340e54800000c04d40300c0f020340c1d6042c088008800f101c1da080448100308940200f00212500500220000c0109017082000101401300145009004440d018150a06a60700b0301c90700c401170030101070520180c1d071403070802451a80f055042101091070301056450f5284030744100c0e003150307209803020740c5401d0501201007503c01c0e008a084520f05c15080e0041200d4071f40780210312a5507103d207020700946065104060410381100451140340c2e21104c04c100200c2d140600e81034100c0c520b00314020049180e0b045c500c002d0700242c1218480c060000074002940c0340d0100102085070829680c80c85e0100c1c905000003171200d0100c034080303074a90080c81080c01d10305502c1c041540000c41e4840040c900204200c00c0c90030758122180c0c60000c01d43c0c0d800000080b0721141d4100d4403176a180c55012644007550100903103844010307100544044105041c0e500d10a800b548030303152620349124410045c0307640340b034004103003e4030745410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 959440017 1250 959438767 959438867
    0x501050f0c04030309141306092013300b010e07082403030d0e03040e06030f0a03081e09070501030c0509010203090f01031b050301080106050901120f03 67
    0x11041c0c0c0d00360007580c0036a5455910804c01c0791503c6070700c03020500e0041d00c80e680404031104691041e00e8a1280500524003c2d5001c19003004c5131990000401001c86103d40341482080003000701140d0f040e041e000e540e4400c0c0401100342c560300f1402c003400c81c0750b420030704108020003040f400e2200d030650407812616a042c02c0407065642c4042100c4003842541e038403601c0b50b001c00506030360002d0000000d0f01c6110140859082c00142202502611071443e02e121080e00006020b11082c5801840160b01000c1a0000c0880c0c6a0100c0c5a940e00c0900500103010440001302240103800745081c418101100b014420000d801c0064250f52a01614031542d404030340303000e0342c0e00445030080041da0000c1350160051801c03d0902030601000d40b0301306100301c0c10160346c2d030f103c1600900e032619288520001d554519440c1d42c10a0889030031520141c1183d8400e0380701000401c003600042070b0017422261f112b07511910030072040c5002d03552000030005448684801111014803140042e442c0e54203100d2456507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 959441267 1250 959440017 959440021
    0xc060601030c0e010c03020c041a0f0105040509010e0c070b01033207060804050a0606080303070923190312030b010e1e10050d0c05120a1e0b04020904090501050f 71
    0x540031100c0e0302c450341c4042600d541c0070301101d40c002e200c90385030720b40240107584043c0903002c00141254105180560038030b843e00f40ca1881804c04081c3c0041ca000f007030038128a072034209400101001d8052003807001c0c6002c268000381003192580d0540340810382c0121484800c1d6168680b07a10522040c1068684400c0c03600c007452110407503140c0ea02080c102060240c1321207402c1000031109051300400a40b485c1c4600302d0041c0001350740b44070750001080548051a03c0b82400c080060a20034164800d02d082c0c040c0d9080040704a0703843c12020402c0ba000c6a220520010040360080f000c10b080c0c1c00036144179202000703110416055001031109400980c2e07003c901407203043c10003001d414032881000800c907481151394118140641c01c42d00320700440c1411401d080400b0507030310580b088103075140300043c008a0199500e078881001d0036000f9241e14020b00108134810403640381c030241c481740d17405815108d01c4490300d540c03690b81c1241c1350f005002c1c00501041ca140c1c201507018000a42c2c0c0130711601d0071a40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 959442517 1250 959441267 959441269
    0x1d0d0305040213110c0709050708400b040b07030e1c0f091e03150c0807031112010906171504020d17072a0803040504050705070b0a020c0606 62
    0x458244126030043c00b09240f820200c0c0c0c80001080031000380f102600e4100045070752035000b082400003c042d005804a454034101c00010540b00c00905500da090700503000c01400344048011819136940070f0440e490351003500c1c3d281046030b40030a45000e0803001151041c4014000c0c000c019070710800700350b00d0502490700b41c1d02c151951101a055104407000c2c00300c030700a00883c4110412090b1401c64903000d1145a1110400c20351100c7ca000d4044641141d80320400c20419408507001030302584200c00c005110307410b80050041d1a000b441a005c03d556000703d055200031100c00e8880241070103030184d1040da1124600c0303009054074010800c001101465272035608034009200b10322001a010410b0080c2c0b115824420718581945041311401071064180a2110102c00078000300c0f4010500c0000d00420348003040140d01001081c1a5600c0250344203100000300003085504031002560300143c5076403a10802c450b14021800002d0014a0a90900484100b1500640f640480c6941a40e0721510740b40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 959443767 1250 959442517 959442521
    0xc15021c02031c020901030603020913060b10081302013b060313060513061107060c03050108030403140106050607052505330c070306060b030c04031b091d0d03 70
    0x1a8a034819082108442140f000ca64001d401000707410b04020403650307200d5001034004241141d40d40c8a265034031032450103015447c02101885401039820440d0381c402c10400034440400180344821a03060490300d102164458088150307a11070100480e114014444105868810865070b035845416445071552588e1a00b842164040c03486400420345103900d0b0398641c405480e000341200c803680303607103007914000c601c95028a503039000445c1007032a543c58461610108644505846908051904005010f9070300000102d50070307690420038001c4120301c09080a03000d0241034000079088040071aaa60030030000103945003a480100041800034001d403601500c45003c82d1041c81d070720100c042c3c020300745160700b09506202c4007000900d114071621355410903c0301d64484985400658045042003080c440302d44200300203402c1c603e8070306140d4100900c0f410264051404042c2c0241011128403100c004032007869401459200d40910980382c4500c6880344401c44000481030f94002c0502c0170184610034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 959445017 1250 959443767 959443777
    0x9061404020f03010501080a151d0f01140f0f1005130605030603030d0e0f1605040e030c0d08101521051b1303060e07091404050312040c15021c0203 65
    0x60301d42c14250b0703103804011154140040c0031494060340d194040d0590b003c0007440340024000c1040215100c0c02d02c25a4201c8281d1700528403424402c0f4000140401c1c912420314075401a0101e40c4039101c0301d00480041c110914041046d83e00541500c2e501d910f01d50403501901c200c81c01d9001101550740e80c2d91041e5881c2c801100c042d60b054000f0001c45040e284158000003024040c0b10885038030441040310145480716030b854429992038032032020001340c5818003a140304840342601460400907100d804a5032111410418003d10a03100005000d460f5094080320042c00c4052604e404402014405003001c0c01160282d21803614420f000440240c0343d015190040c000d02a264a0045140202a841d40c2003816110040d81e079018000002c00c0c0f01c5d003e981c04041d4428040d148041c0340003008030440b41071000c00030400181904100200d030010080e50050158116003800301e507180d141c6420a0110364010b210f83c03010107102c451034543e00190383c60310058041c820802d101c8004500f030ba564014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 959446267 1250 959445017 959445037
    0xa050103060b1008220b101802041a090f0303040e040b0f07171906060e0a0f12060504030c140102030f0108071527060206071404030206070209091002040906140402 72
    0x700001044000e40d1061210880050017840f842549050b5505e00e40d1181054034a000600c00142c03083c07260440009403880654000300046140624200200c4003001f00004001401240420311903680d86403001249002e110040030f40f03585d41c0d150320001140a10a4800b551044030403030010326412001011a0700403003480d15030713840fa80c4400d1504021004011f0046008552045280507045680d00414001d019540c03101c00000010405200c1204104d070b1000302c4041c0410001c0004450b40a80380c0a0030360080c801044554642c101620301c01200d40c0c00030240703111956110154001035020b103010744c02000c28400966a200e507003d945109078000c00b5191065441c042c000c03540200c1e041c00a00100c0f64015140180701107428100c03000c5540f0550260b0002d070100004140d11a03c084203805c50028103070300302030454011804a000b450300c02405011440c010848407441080000203860403001c09558450311110040080c1100340301f08240c015140300c1613945464103000341c8100380c2ca = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 959447517 1250 959446267 959446277
    0x103060f1109060a02010f0501080f1536030310180b030d03020a170c1201060903030e04090503070b041b0e0411041113060e101e05030705090303030a050103060b10 72
    0x20b002d80c01c128541e4000b014a10656603180d00c00f840680e841e000d540d00030304104c070251001010300c2c0851130070300c00c2000554001c00c4050b070070070040f44031206290742d1000ca068040312030400c41c011040c0c0f8100c1242e201e42c2062101200f008041843c1c041e280d0251024010b50003120030885444805894086540e0380c0c0c10f812140004000d984298060104000d03540740400b418814080121041c0c80306680080d00040d00044400d050001030159600401d414940004090b2454030300818400c8040e507500e01c0b03030381c82c1e44490050140130025244566049113400507981403074a4117201d04040b586a1209406078502c00140120900e000d40e4405e0790044640d0410740d400c4010080100b1642a400480d95407e000801c0c1500ea040307450400340907030351204001b59823194104402515052074000c02c212040840031000741d10300c0481c080314070b46410001d4694503090300990303031409000302c803d8040c4400300030404440b0300c0d5005070341268003821041107040b55120a10040410b5100e204010070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 959448767 1250 959447517 959447527
    0xa0c180f020a0906140d0504151b080f07030e16140316030602030606040b1b150402061b0309060d0506091f060c03021906050f0a020a020705090604020403020907080103060f11 77
    0x42e0081c0c52030720090100b01781080c540708900380358608640317040d50309442031031803401da030140c40030300b40b04541000d035013840e42c3d40e010602d44200400ba10001403109007400800404a8110b5020350480b24a4035880c009680320010074500a441001d0140300358000ba911008034031246080104447d1200b0354100c2110081034116100c1e500a944081c02d26074004ca010000041c03548042009844c05200074a10080a07800d04605586401903004d10008202d2528082c0001030740d030241106c141c482c0c0040c04000c5034602540700350460091a0600fa046840061480c1030101985e00c480d114040440300d0b00000d441c0d0300406144201410f141c07240040312000c0130b020b02342c0503080b104c41d01c80c460b20454444100ca12034249103407034000d03012140d0030b89030028070106400032400c00c0d9102150010847c10301d1405040203560707202621070070340614110310208905465a030121006190080c0c09060141001c1d81c000703107082824441501d85902d4160480c4030011a405400e8626400c07071100c904003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 959450017 1250 959448767 959448779
    0xc0531020412030c020612040f1403030c0a0309020d050303100303120207232a040c110706110f060f1008030a0e0907031b020606030f030705120c0a0c180f020a09 71
    0x40783c15010140c1c1e004005000034041102c409240b1f40c880c522900003208180b44c4c42c80d202446015031440507130781c0e8005008222035200c0307070742c10b9a0300c0314124030b03011591000f14008256162942c0202800c80e000c0002081005e4504540c5001202e10950b00e00f200d03400d0144540003203018007040248a00401883c0000c0042380118200c01c415542068a00711700c9038070a036900c003076910b5405410111098250210340d18051240901016640c1060100302205000183d143e5215008100a1040e55114424501420030401d42d10b0b00728002218118146001d5076114000708807102d8100403042c51010800718008001e0340d003065070b0350300c4003000c0118003010400d07180c0e00101400105035403600b03082c8220b0340352180c10704015030940241c01d0906120091605140036403a000807a40e0017002983e0000d0f400096030070348074104000d10f1342c882c8101e031800e50500c1c1d0740c18006824000282d0340800d503101a1400780c12060140d0000700f00803007001805006a000700c4080c6008190105010000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 959451267 1250 959450017 959450027
    0x170903040909140604050a0c0608190f0b040e07080106050109060203120a1113060305060a0819080721021e0c010c03090909081309020c12070c053102041203 69
    0xb84910903c02c81c1848407019428a1600500702e03025107055101582c2881408058007514000d41528031700300d466840c040c44400c00d0200485084280d03a81da03466540c0748448550b105420440004100740483e940060f010b0703a8542c0c1070701491050b5480d1080c00100e0f90300a2003100111090390700a18181705010003000c514150003821014415254848001809045c0b802484115015121031281030b0806000900b1510020301c00c80c0641d00200c410b0005410001d00b1450080d851412824599131506d049503e900a404e401041c0c81d4003c1d103100c03003c0e640f01701003003007040041d8203e41c8411780d041c07040c1d00d0701c50140041e045c081d00188940300095224180861001e8001d00302a00b0b200d55981d2000229030351100140e071035001c049240c6041c5c0c000301517100010003036040107606103a030042c0c0c000d803a11035542c2e90000c141030014072001041030040c444002070600415402c40300c84076144100074281e48240c02c51442c041034030640c420260b18800e507170590703541c120a06410780c0c0e40d95050760 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 959452517 1250 959451267 959451281
    0xa0e070305070c021203030403020606010806030a060b06040b040806041412180102070317090109080106080d0c030912060209030105130c14040207061b2c090a180605071709030409 79
    0x420120b5007061026885d158001707180344e03a010006660b24642414001d040400c06007420341005611001d1141c583d500007400d50300036403c0400001c0d0074000000140d0503208950001d20080c10106001484502c04a4228131560140d110385c8000307034010424548880e11144003601c2c03c6d40c00d02480c4c04000005000262500040c01115141912034032100796901c0c942c980007a40900001d000c11040d6803007880003008042e6007000b03101950812600740d840f5546c40c400c0c1420031481c54015014948075807010001405466040b034034000f500c3c140f0348065404103042034000c3d03003040085810852901801980107412a038a20547e40c02c05928032030102c50f00d08203d900680900422020540c240f00300454035000c00a00340c0302c0c0340201c0020b81030100f4810790207543c80c0501108140102d02c203800c1c80462104032503914499030380410301c1c0004d04084111200c0ba001c6809288208461070f40600d000b11a00c0d128001d05020f402800382016208507040c0301d080e0018441008030400701d0700010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 959453767 1250 959452517 959452531
    0x3d092705062e180b0a0e06070f0f020f01110c131e14090a0c090b04110a020a0b0606040302030a06111b1f4508040509060a0e070305 58
    0x400b002e1031a04a51000440501100c082008107003a0080080c0c000400c0d44002c481d0003440e0b1546454690480014000c84003214144039070104000c0b8035640740d4040b9030790b155029607464040300700c90408000701c86d145e040403405000301e003541800940c05401d1201c500c50100e0700414140c081002802840c030a0059161500b517114843d902614003114888030f03048008090018039001c03000307808401804058019400f54101002c90b4010924810340c0209460180d40086041c1075020701090007841007618a03420300328003080b0582ea02d0750210701c4801c200c0c090340119015441d40300800c40d80b4800d500c002549540301c41411300029915030001ca01d0092030140c02c80c01e120807070314040c2a04880c039604a5042e08030f00c0749481c0443c00b840e5290781d030681245040120594019840d0842226800004600000481024422610000c81c0d40f04c0c440c010522204101c3e03180741010b8985c000e401001d12840300140000c80b60309040c407480046421100d00002203071108030741a0300801d03026007a9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 959455017 1250 959453767 959453779
    0x81503011404032c1c030e060f030420030601150c06090312060923100801090503030a0e0705010e060928180b03071e1d0901180507053d09270506 64
    0xf8a1f0b00e542c1c0c080502480300f00c64519550b01d1401c3d251048110030b40e000301c4260070414041107401510005130560541e00d50354560f0300450306210040c1c41e00c1c6c006c11802000d1505100f00b031800c140d03000c02d8880e1200d0310700500f40603030342d10f81382410180ea0410042619a16190302c98503448003401c0d0b0016001a01d20305420480340d103c15146096031050760065034a6407001040c840d564210384916801d03088030001400050303040400080c12640a01740c403600c91400428140269926500340e080d80c848148455010488840708207002d0b01e40034401d140c0c200c0c044c0c0c1020900c9001d41d01911040e03860081c060030a250800815101c44a101403514520b0f1122010204240f206401c1c0310311103140348004070107989070024142b825240c280000c00e0301442080c1010b000102e0000c4c0500c103459089501c41904c000900c54074070205500603c0b620b01f944152000501c13002032884020780140c043c1e59240d00709884a01d54825140034000c0915451125a184038856100f0303408240c02084c01802 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 959456267 1250 959455017 959455037
    0x70f0512040305241f151806080103150c0e120d0e060c030f160b09011406030309030715050706061401170f012102270610081503011404032c1c03 64
    0x80295890032144c00101040701040c1204100000e1f08400c0d0040c403062400020540c1165641d45617581c4d40c00703510440d55221640010743d00d006514207038920340068105119032180550482d03071044a40b88100106200c18850b500c14246202203810040300e40c4025072411120f0141c0c90040c2c1e00154a050040c00c45183e2400007450805015020710b0404001183c694004008004210030250205110781d00421010005d510003013214400c80b40b5400305142c0304500c45001780c449219a17400241218070304900859030190741c02008000003800c0c0c4e135481c0900d10f82e60959641d0742050b22141c2c0c94140c0040104518115034030454008405480440d000000c03a501140943e50346900a01050240703562001d0030600c1e144085901000413100100003074402d041c080c0c1a00d0020b01900c041098191054040d03440940000d10b080c17500e000c80107001d19290038010090300300003001003410440111052000911400d0700404000300420281060400c0c0304480c0e40500c10200132030034002c0c8450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 959457517 1250 959456267 959456279
    0x50d0302070b030412301a04060611060a1413020a0b0a020c100e0607140a080f0a1e0504170c04060909020117040b0c070f0512040305241f 61
    0xd075001d0b0b0b20a0311064681c0c003070180c0241c0721420401c115071002d40c4804208450004285e61b05018903210140050040b41590a06684c0303007a03079403000d410505001001038280d50058001107851a00c4095680c0f0741c031388040007400d907181184c501800200c118080307a036a071000740303540c01b0786803000b050107207481c0d95540e0264040d0094414500036030013054400e00a402e001020075513240540c80d18082d008200c20004249004e201b9014000195042d40d0a09100d0200b01e800d044a410080494070303a100214003540075030122088c4400651a041d044100484007455900703c002d01c0d403200c600705803c110407843c04078000d1504c5000c500c1040840384494560f481804080e19500d034021620804030300000d04504092440c03a6803104d404403c0101144031311003100c3e000b90011800c2c564410450412000001e02400301402c0f5010302002451400c44d1031000b00103da02c1a401e540d8034161440000305021000c0305034442e0982480d0010b0040d800c00d040c0c3c0002e03101c15010400110b40c40341 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 959458767 1250 959457517 959457539
    0x2091306050103120f0c05060c0c011d160e01180506190b0901090b040e01060f0c1703190506030d030e01110d0f180c0302150f0d0501030c080a030801050d030207 71
    0x3c0d2003619458100024801c0c40390340702c0c40c0c608072001107003000c4400c51210340d00c055940b10001c0010a0b108400b00c0c01d105d00c0c0600790880012100a4a54420685188045291100c882c002c01d45408089600700080d111440240c0c50704881c0a80e1030400c107000b16442c0e040c00740c40b0041c09654460713901b041040c20300540e40b0652780038203003100c15191540d039130100260210520740c00c590101c0390203000812925417904403881c1554218a452001030064642c00d0700e607403411040040c02224075116000b41552074038065072040c400511920045015091540304a410585500d90590401080741c030300c040c020b8010180e40040c0d03000000d01c0d04003a103915401500807090400c1c00e06d0300d4040b0641c0407500390140301002c0440000340703a44400940d0f290042402c07207200c0240103c0325075140c0840369401301c003582c0594141101403aa84c4c2c600700e08210040c8001d0100b1200d03a604888d010440420000f944072559615031158500359090400700580401108011411071048440c0031070802414 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 959460017 1250 959458767 959458769
    0x2b0815060706061e1a0c0a12020609010f0c0f030515032e050613090c05130e010501140d150e0a141b0a090e07080f0703110f06030103020913060501 65
    0xd640000c2d0082c10a000714200000c259000114620000000c2c00328150400f902010740130440b171890381d90b405c0e42180c6818081d6401d800780014841128402c15a078002c01c8452140740900c0003040709202d107800d140c040740e1808101c000051182203900038202e01980c00701e50050340c90f135440314403000003100191414003c500c0c462400902403c8003070088100001000e8100801c803001d20103494180003140e0350410104245410a85890303900e030a11a8003011440688000303442c8003080048070f41d15a024040c806424030540d8600300001030346401c03902040c2c03504400103085041e603000b1a00da440b030061441602d240040da036400c080013100310402000e0302c5a840380c3e8420a0b14020040618213004070a4090241c12000e00d41c943c01c10703941c011460007034074800480003a503d1943d403103052418410b80c200d41c2c004c0c0f281240030700400d0710000f812800c4920a0400100c4c3c41180401d01c45551480200f05411520900041c4010310382401c0f129488520b455400c00340c0c016a48a0b041a42c1023 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 959461267 1250 959460017 959460023
    0x301050609030a0c1d0604060b070308041a0c0702121c0509120303040c030506070203090922301b020108041b03210c20120105090d022b08150607 64
    0x9109044540d03011754510654020412502000301900d05085983c1612400c40024204204100014100003008041400948100030441a5031400c0d004080c80e0364006001a8801c2c0c090000c084121840080c038080340f4000303040d0490b620039540800f82c1c9c258003c54200c90b071060a2016500a0781c100700060b500c02c078001d8a00d05031441c60750030001c2c10b003a4050300480464004010b1110a034503020303100c98010707004404407400001d80c0c070b00c0c41d1802003944000a001001c800315a08107205502c540b03071031504c0704081004429030a4034050381c04858a6951a030401c81c218900005980500030346a0301c58043d0368203c490281000d8083c0c80d825031034004030b0b201041d440080808201040300e901010000d0308040c0400740340c41e01c400300071400041812200d0041701408402350348842120b040f080c83c41100902203401c2091100d07860301c1c11207100000601c070b010b00d11540d008141c840e0700c1c5031864101e040d8400501017081101c100d603005012402d5502d40644100a40d161000280030180c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 959462517 1250 959461267 959461289
    0x1536060f02090f0a12231c0315050d1b080607020a0c0b180d020402090d03090527010e070507140a0203010501060305090d200a05070312030c050301050609030a0c 71
    0x200b2404108200f400c00f00b0781c3d40660990b220910050704150145200c10b908000400503075404003c0407086045110581a0380d0b010307002c09030303001000070401c29050f0301c02030f00d05001381e501c81c00640d00e003400a4418950301c400302c40c0d0140003142c103425400708403421f040c41d0001032030384450820340303083c0701600c2d07040040e030100d440103040c0440c040100025081501d20a403921480b0740d5815844002040c500f44944490304440003150348960441d0f03840305014102d068841042e0501800c1c03200079120703041c0564041480d01a00d180820000b1070310507142d0704074503456400c0c88050381107090010440d2041c00810080c080110b0f0780340b0405036600f100c0c90000c205240703042c814582543c1c01030340700109143c2410305010100d08045201d0511007d9842c0c454000503001c00d80d41da050068600140c4540607807003800040c8a00840d07110b040c4d0b03018400075171914019940071002ca600f4400d500d00080c8003480140040d140c100300400642d98010300311002c02a0540300d40307a1002041c2d01c90781080d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 959463767 1250 959462517 959462527
    0x9060815010e010f150c0c1202030f0a17130807120624050607050c04110403022403010302010e1807031a0a080307121701030f1536060f02 61
    0x1694540361240501101a245402c5500d01125000da03840540900c04145407144c1900702031070b10039005030b1000d9030007442d008403242c0c0c1c0711100040c040a03903a00b6802405030340d01444264000285245000da030085100c4626408044240429000101c0e001c911040c0d201c0c00250500081242c44080d01240203041c0000149242071422145810700031080a505c684181c004010500000c50446805480481e41d8005130b152550500d2054003506500910300084581d090b280b007400b40080e6442911440940c40301d0f031410704488542c030300d40c00196400400051006510404089001e0780015250440240800300640d0300c060085030707540c00191b961103c014008120b001090320380b41040d81d010b11046c0c1803480103a220311404001800e00144594414241032145504806407100807055200a5850b0701d441c0c102d00f8201002980c9003400d05104051485c614850f40003d8841090701a603000300561800b03003003042022103600224032081c08040450340d58020304640c004d640e98010707591 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 959465017 1250 959463767 959463793
    0xa030b0c0c070b0408011d060601020c01121d0a05060f04240f09030e0906011716020a080d020a0f0302030c16081c0506120d02100b04061505030601081b040608040507090608 76
    0x50107c014038400e13481789052201c280d8010440b500141000e10b018607c0d0b81441c0304500c094a5024600d07070f8a0b0401c00004000ca0710b0201d03c1464807407080341500c0161300c80c244c52001c1c808041d0b41c0508001c00c0841042d032204000d0340c541b104422806e01c081460000940114115543d2500543c0820703010300071070002e031416200c0b00b40d0085090030101d0203180760a800c5035041034010041500601001c0500e104903008106c41da0503203030300044c500d0f5102402250b64019404c1201c002001c6018408000303403441c001d00aa034803590100600d0b074142590703001d80701d040988083c07003500c00c0d41c4100001040c0e14110820314086046884020805040c0242446121480400e45240f903420982d902c400465002c5011240c00000c2c001c00f007440301d24400010024074680c1d01203400725240c0c0700541007030368101000e90f00c5a4007d894254240e0b0751141507a06a81350320366007000b803004c200010701c001c81c014907200b40c21030f015400700e03500c06d034640503040b080302c61640061031141d1002c2442200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 959466267 1250 959465017 959465051
    0x30803041101030c0219020a030f1a0a060303050711040f0203090106180203060616030e030a03030e0118151d010f020304021003062103020f060f0709050a030b0c0c070b040801 77
    0x74905080c0380400901d060070800075101d4400715a070a039800101000502903581d6140010301454011180400070980c500e070600e9400007100c4044031500d0103000080c032a290351b01c115400c0380d40548a46250042c280d035003103500744c500c0c00300710b5016503603407200d604500e0b031480a18811114400000b07800e500b04032845008a01c21901003004900400410056850341d1040d240300c000310050340c1c1d403008031918090320001c0c149050307107402d03202d0801002d041c140d154001403826040b49000700103004800100520320081080003030312040420410341e003084019440345d40038200f02c4031030f1002541c14140c0c40e400d4800e10300302c032580e440e004000c1c0302c04d5141500c007291a00c1d010342001c01116103014084000d00d0003802406140241160200d41403600911950b00e050360f03500300b6500c03a45403040b4604000c00f0191800d00c00180303c7c10001c2102d003010051141642c0d040146c1d43c1581d83c640010503469070144011642c140200c00d400a0410000740180003d001500000314440c4074400140311 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 959467517 1250 959466267 959466293
    0xf0e070906061704020d060522030302070c05030a03080c09010c020d050303040203160f050108062b0b060402071110050705062e050d020d020f18010801110c25090603080304 76
    0x400f0501c08800c0c40b005a50314001c1c40c50080c0c0c81940401c899a0300d0b5800145032031407600480214642134403000802d641540280a03103842250490b40c001e40751010b05944690629000b40451800030214416045540c054070580c00149082c2049103003da011508040120400303d55030b51021003400110b240c2401210703640564658402c1d03045142150840011000d4451310303042c021204081641a2212aa41d01d000c8990310008514600b206150503071145000c1003d6031480f01e01c10103d509440c060007100c50403078101000e080100101000c10025808211f0b051040c4103082010000281050200c54807400030043c40ccd001511140c807420210581041500040000072202407000750786081d1054001038043e00c0002c90745440b88040b0b020404802e00751a13005101d6196010105030b1400d006040e07a10040081c41503120030b8403160b4050142d00e003040a59080803d0301c0d655051003040d09210b9008507844088296960030500b03044440d1b80d04241c8a50000004001c00c3c084014031b408 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 959468767 1250 959467517 959467547
    0x3010303020309130e1f0e01090f152a03050c0928031a010e0603070b03011401030902030f0d030e0f150a02460203040b0c070518090f0f030405040f0e07090606 70
    0x2c400d0741040d032b0381e819910b2800c043c010803130710036846d1041d4403549560040c162403076a001da010581d1440921000c2c0400e802640c240045c0c24100000c8486c0310798000e540070076001410207000000402611165007101c00c48416440108610010200c1c400b200380c107020000d80c03058000c403035040c21440d2a258100401140c0642d02040040241c407444608a81c112220320300b07550b00218001004a000d8014a04082d62500c100600c00d060120040755840c440e80c915102004500e003000c1c4015160006a400e40c29070303802140354185d0798040b00c1c000307076030003007803801d00602d00725501000082c4801078240104800406051300f0300030310910001d01c4a08010070000c600c0b60300f034032a4000c1d52442140580c00e045407020440c10441d0030100b001c9009000014200c1c0155400e1540541c80120121840e0390740d44140243c4c1d611b54400400c1c5c0050030003561001d14585824802400041c242900b1008070981c0d640c0c400c00c00c0a40148003840150407c2000450f401c0d03d0810b0040900d0005002e0f8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 959470017 1250 959468767 959468771
    0x2115020307030522020d12030e0f030415030b060a03020a120504030e09130b1503031204320309012114090f030f0d0b0d0807030903150203010303020309130e1f0e01 72
    0x1100142c0e40703100c3e101c40c0e5142d00c08032800887c40c200004030701501c014a0160f1162056141c0c0200741c55001c4054802c1d1501300040e0454281041c100f2400e0b1406000d6040e000402000507000442c440e80050031074005504220120340d010442c1c0d54211761041350107400251141150b04014034008429a0f0021180c03543c001c82030300a5140d010301d0100c0134280c0b0000ea08003502042a82c1c4050058a0180c0302400000c45c0170325090809109640c0140d020318070881c030409060f80d11841e5550800b20883d0064000d5040096000064403107100c003010880440746c420300c0c05015414640070340c0481c0c3c40c442d0010000d42c1056800c06250881805488a00b81c0082c041d0348400d040070302c141c81491090309000b052400181000c10406100018003510001001509805054210401e001102c0c440e1804d00001e0000c0c44c654412800f080c00010016001003200c240f080c0360a40c5601100368142a0000300042c6d01c1c0310081c6480044518144117070040803034407104500d9803090794044c042590007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 959471267 1250 959470017 959470081
    0x603040f05150f06010c0c050604090510050a061d0a090906020a1403060d11060d0507080103030e030607051602040e0706180f0f0e09070503240a0621150203070305 72
    0xf50200c015004080c035040041c0e20007651306001040c1000001000080c182550300c83c0c1780c2d14440042c100880e20340b26181130720280000c082c1000c0484104560540e42da100d103040c0c00f108101c815a090f80d00066101c0e51000c404035841085204562f1010f200b03a00051b0349048e0414041c02d05c0c580ca00784000c4005050007088269140d0880300340d40c041c3c0c40890890001803040000c0d0050182d4001119840e14000410035403c0d00020b495068a010780c868095201104003056600d49040b02c641b400507400380007008085021403030300c0185038402000420080031000c0c05a203821010351001000940d04801404161803102200020b03008840c0361141581c14103607034925a80442c40361011030034422002840980381130001034040d103002002e445881e04000303400c0c00031326940301846603d8400c0c040800d50762a414402d000c102c13452056181ea401344100004d40d00502c4146c4103640001031074045024035510740c0b00031807040c0700580700010079090603940520604550264103400d80c1154403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 959472517 1250 959471267 959471281
    0xf0108010f05010c0807050d0906122007061d010606030e060c0a111606181d060f03010b04020f130e1306021b0d0c03020c010e0d0809030c0603040f0515 67
    0x401039410a0130700364442c020314075001c54240709030480501940102c0000c00901ca9221145804458890f03030361480419080980c0411640d041071109486408441940413200201000d0b0400728025107001507842d10001c3c1850311122005c800810a035504c40381405a550148030b04c140b54107040c0001e00c00c0746010385401d1854400c0607259014004150750117034440c003041054071100c00310102e0100095607074007400703490b03403842e070b41808118911f00c0300201768100c0d00c400965220340303020590000c686804041c0b140d103091080c42d2a03055500c0303c00310304d0280c40781d000030071004074101d9040365540d1481603582003903801c50300001100c01c00071050100c2221800318088040341c211030010390311181101e28a2440b4000c55600020303000707005058100c2e6030055040a9203502036001e035060548110700444082d203940f05d0007580001c1d40301d20440401c960b41c002d03107907a040c05402c607072148400b0307000900c464004640c00c650301480042034034200700d401d00500340b101c0c030b02d800180a40d0901da1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 959473767 1250 959472517 959472539
    0x20f1b03070e04060915060602012306150408030f03061903080319060504050a090605450703120f0804030c142d0c0f01091505090315060f010801 64
    0x8450b20b080b110240d404a002c0c00800d52201001d00e511591980031119400044d0002e00303000e2203048059460200d20301d4807011205403900640100c01c110108659980003000300000621801100f808000c0c070000c02d00a03000c1004182c00d080708000fa540342e02e400c0c1c04000382000e5801d1000c40d492007100b0b0400000d00c44405981d000300440d1401c1122030300c800740040051403140e1000f5403043c00c200512039442501e51000505901501080c80241d0744c02100c12a00c0e1407100d001c1c8000118104920010f105070181229420252203c4414015003038848a203400040c3c3c000390349c41c1902444008106812410807250500340d0306007101545410f89000d0301280900c98090280c07040c817580701e440324409201115001c070380c05901c60111400003800d80c04504170080300e003c00303208003c180d0b0010b180c0f40f6011204604140c1d200c0c22005c0c02c00c01e21850f070382d0300c0218078070030b00c030061008080d5983c040c42080308110100340c07500c1c0c0303525082081041c069020341c0054107100c20390005000410f249 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 959475017 1250 959473767 959473769
    0x909010b0a031506020c0a1d010e09010b1801140f030706030903170114030714151b0d0e041a030d0309140d0f0909020702010c03050c03130906050103050c030702071a19020f1b0307 79
    0x30908ac4015665100d20040c003402c02003884030751143c0068401c1c40303510b81100015042c1c0d1f0420050f03501242d15041400319100c1c006503425415409501c04001c05e40c480e4000d16a074500c68a8140c0c84013040b400800d0480c43c080e0040b01c02c1d035410305000603042c00c00308100002050407800c41400c20340b1485c04200d250756550f05c01c0c140607800207421084d1070120b420600415103c80e089444425800717100038a0044c9004885102e41d0038010007041d04908000d2452072040d00401402c0b28020218050700240305150013103441450a0f41d0b040c81d10700c0c00340680030b19110140c0300c0440e040c49548000740481126005110214414441000980d07486802e59602541c10b003851070362411150030306440d60003001c00e00301c80a48504004601c051f0389030071500844030b01781c905001d1920307a00b0664516010445a500040e8403000b010442a407402807810341504410311254079154000c0d52440c00030721000741c01c002590020b03040080307c04040102c00070302c0b1103440c20114140b100c280000c1d115425 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 959476267 1250 959475017 959475029
    0x2060c010209045a0f0606030908030f0405011112040204060e07080601120e030c0c09161e090929220b040e01021201090b060909010b0a031506020c0a1d01 68
    0x3059040020076582c10780300510301c80741640a04c00c41006905000585110988a081142012400104140203018201c0d40e107501122407800c6580c3c200300c000321054020019166592240c04980d000040040180001c030120010b0700030914050050009480469200c030070307409109410080810391203401d16801c25000d2800c81010501641c50802402140034429454000004d10000011001075010202081914140340da9034544c070640490070221100c600100300c0c0103d40109900b400744501c040741e44142000030b03a5031349480d0b10b9011130302d05c0050394006610703c021a50b03c2d42c6081d0003001e1420022a1044200c0c003950140403800e25001c0802410b940e15800c00740200c1e40c1c1c50f00422040980200210349901c242c000341c0d425a0001e100c0c0c125000e21308500e200d2030b03040810494a241c00c024011070b0041c0d1034030f201e4090b83d038041c0101c00c08260345d4841d41c0c646018500341074002070510ba8018401c04c0001c0c07042013690b2180c0d620101044c080c0c510300f0941d0122103265141101c0d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 959477517 1250 959476267 959476361
    0xe010608040b06030a051902031014060118030b040b0f100b1801200a03090801110912100509030423030c0918030a0207060813020d080a030902060c01020904 69
    0x503843c0100e841c105a0403c0140b050041c1c039803c034000120000604c41e0342d03000f28100c920306295408100c00300c0711454000000c00403050001100c41d4003800d07580010a04484007510384540eaa26071190010f810365040f2840c200000a02c002c85680c0c4102c5030300139688100308000d59141c22803040191050b051445490010400c03c41c030540e0084119090702a001401040068443c0c52020b0b02d401292104601080c40700703070040380c0c2c00d03414401c81308943d4141c5140f07441d1102c400200f0200c1c0c940c0c0850000d0b035200d013915041c1001c00e50700405c0c3c000c22401009584441c101f4440e803044104c51014580e00040108001c402a81c2c00030302e92015000546510365903484000d81c08040e20440d07562341c0702ca44400121385908503400144001120390540e50440c090f1507011640603031511482c0d000c0d6000c05c030715080c078020844440c002d10301801079050024000b980d41d40070035a1071b04040c001d8041a540403401043d541400e00503c4e4000420444421081562500800e110745801164180f400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 959478767 1250 959477517 959477521
    0x41410030b100806011203030509060106170c16060b0406090b011205040203010204030210080402100507050a060b0f040e031201050a08100207031202070b04020102070503030f0924040806040c0e010608040b 90
    0xb0342c00e0010300c00a000000252032681da101c01c0d90080d58400420110002031500c0002400080b001c9030850583e001c956034001c1340321100406610f181e10281c040a0031540c200000c03015500071003904146144074030744c0850a081e09404010407603010381d0010100900b091500311147e03034002d484480350010401d0003c3c01e5251400428020301450304004e400c10128007034116440d4001d00541e1040f4400c0714445629000c0c4401194140200c0d08014001ea0204d281d80b00054600c1d00305000107500548407166101605001400755948880100d8040e040015074100302d01c0c90301103a5002d028252440f600075032801818560701c012245c24403d2031030b0b02284d44001c151261052503508048032005545400084c02d01803007084040d00c0482c00751043c10000110b905000c010380f00200c4240d8101400c0074003100922000800c1060840080c1500303084560b05401e01c0c40c0035001034010400203100034949032800300e1009043d9041040710340d15010040200551109503950300c0750388483c20b00419 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 959480017 1250 959478767 959478781
    0x60310181b0e0408030405010c0c08090d031e05040906080601141207030614090c010215060103090302031201151103040503030d021c0606080a0b0a0806040b090a1a010302041410030b 80
    0x1e860250001c244110151041c0018483d00c400594095030040000300215055104244c600305807858004010307440c1804030b100b0070714000300520105802410301142405404c50104e00c402680388c4a0008a0f4020130103220f0034001d0712541e00070740fa400c0000d1070154100031200041c56000c6641c548501407034440c800c000e28080c00500000c45c3d10580612600323000c4840443c405074112440d40c0300784602a11040300d58030000d01c4128255401c8080300c034648074203004401801ca11803060341544001c02c410907440c105485428002d01d020342900115007141c100c002c04424400061034072561051001740416600402107808543d565807006035039500e015400880751428015001035a0b180c03680000b8041d8001c41958801c40ca4220104442c40e201010018000710900820590340e00c03076000540012841550301d608600c1150840e08080580e58911615001000c0074104000c0c501c00100110304240c000c080e400500100c1c046c56170724260b580907081c3c464500c8064000c910702c0b0041159 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 959481267 1250 959480017 959480063
    0x60905151e040507111902010e0301020a0e1509030a0b0412020624040f0207030906030b060c0709050717040c060e090108061b0c0d091805090709020f04170606031018 73
    0x80c4d2401d05e81952000c0343c1c92446100d15158a020aa0114403010303020003131171406100300c600e02130032500c45200300203d0b20705000c0d0303c5404c0003107003c5c040d80412814103d43c1e010070003540c056209629140c001d191516181c0342c0303911203203000c0055500070410b0100c140b03002d6030041c00c20b030712001c11101c0c0c80d05010001409484001d06004480303100040c0345042c541d10013810070540d005602e0503c880168001404400d21a9994500d92500110070502021b42103802941c0c01900c1444d00200c1400b04011480308008240c1c2e04440803240303214100013068104d035601050b550120f442c03050300d6252480c0e06032a10001011710315613098502421082c2c50801e420f54413000c015404481c10074038220f201614441d03040c0180c9032401400c9032440e11641240c01103d128000d808041d140f5a4680b10103c4040d4101c030400c00ca008200303010105e5104080b0702d10300008007280c0001e007030301c4c10a80c081c1400c00c601c08580d114260709102040740712030040d0f22009030b92a0322a07824980a0f4100710080e032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 959482517 1250 959481267 959481287
    0x703080316020a0f0b09060c1c02070204022802070605090d030c02120d0207420e040c0f08150102210d020c0708071e120510060905151e040507 63
    0x2000c1881a11298280540340d131005d4860b0490004640103030300d0703a0001c8030450180450401800c2d00c0e60140800581c600d801900007140f01410250515810f44520000e2251403024000d82120003020242c0040e03040100303100400c242e00f0080c0ca030080c03080100d400000c80c008c0207801c0c00301c611130b0181152191946180c00360b6800c0181c940c52200060001e4985800e44100812101c04584058080425800041c05d00c0444c0c1c41c48498611b10380c03012454901918841c0040c00000d9400c2100794640b8060001c1d16019542c40b01c2081d4506000541090000b5109940d410700390101941070380d0700014604170848030820356900008800300d01300024414842060000e43c00480c00070741615000400c00b058032014000ea40f40c10341c58062882c91000005841004072400075401c1041d0920091107500490040e415621031407410514241074030100d80c01262032682e01c40070030110300386103500d030070300d040c01100e45240c81001003c0c01000601c56030112440f036076413030340414a100e0091a17091 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 959483767 1250 959482517 959482523
    0x5131205120c0306121903081906080d0f0305040510111b0f1e0715030204031b0302210604020910080a0807020103060e131103010e120304050c030703080316020a 71
    0x20701c0b45082480382074550010b0302c28074041c00c0307200103150080030045098000030540e0700703203038000c0d45681d201140c2c249000b4000380101c500f00401c136030b1840814058880503111102c02803401c0507503032000500380d2510a004800705031821052000096022486040d02411034001040c40b014030b042d401c1c103e1081c40303080c281c10302c403c420640203820081b4046a2001c0102c003560a42480500300c440b071084030181084298206020a001800c3c81100e0140d0500541c41c0044c185510303965003100c0c02c02c4507048484800e104010410446c07800900e14503141d01d143d1b0454810040900d0096aa1480030b0f10091081c2d102d580081c3c800b040d00b0000b58020b042a00417180c000d0020b05088805030300001007a8000b0f410a0000306035905580c0245004020140c1e101e924911142c035050203c0078403080c540d5140d500c540540e800c2110800056210f90143c0700d0440d544d09252030950324204485682d075000b900320400400c04114000180ca80c4112003918000081c40401401c9003045e600010003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 959485017 1250 959483767 959483797
    0x40b0f2a0f07060b0f1503040f0503041502010b040b0a12020922300c0b0a1401062f030f13030b0a0b09060409051905071701020c1005131205 62
    0x20b03105008032500894202e42040c1d41a0410305812010b1008034050035040c00c0300180d0070008540000d01000315601424042c2059908042d00d41100817003a91072506041e0050f910b41d0404d00d0940f505101c7d400740e00c0c4007114000c3c121490042402c0c2d42c2c03c2c00802c0644200064400038449040a0b10f10700c20201102c0d0046008500311f00c0d02250804402c2040c0800b00c075600090040b0035403c141c580e8400001e6224071a440d156591900010900101451401921005100300c141c82060300980605800d48504051544030000c640c220170000d03c0a40301015800d22051440c02d020040740c3c01907070485500390780e40c82404220703903416030b0350703807005040d014090100120540681e0201c0b520081c122030941d40c507144c0904003c02d07100180c4020305607400c03090036186400c040d01c20608032944074005858820395541c00040165090b941e0080090b50002001c55007401c2c280010f2001a4000c00104000d0409a0070307440c000104020080445c0d08000d100318407540684c0030303101800d10115a0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 959486267 1250 959485017 959485027
    0x7030b0103150e07140306060421020d0326010312031d070603020a03050a0c02100203100302030f060405010c110705040b010c0501050a0b030d050903031207090509070305040b0f2a0f 80
    0x29030300004000315803140005030000582c90001e01d45c0d400302e0340101c80040c04035081c2810007404e52400a440060f8140000b01304e10200300503183c203412141090b00036165104102502e64a100d07485210000d1138000c1310b19580103100046038a03854015912407403a00103110320b131a510701903a80848543c641400e201d1f841000518135810340007401c800030140e900b0300268a546400e101550181204600541c21968200013800c55079405550300110f020f084003070641e62a00400d05000b001d86440a250304a0010401405001d00454564111a00c1c100c0701400019803c651500c94a000701c42c4141d07240c10149107540c1c03007001e40200264002c0c00030001e600f04641010000c20562040e18020700610980000b500e00070000d444441c5009030281d45400d41d410180710140000408940c1403041700100420b064580415480c45080d05071400146400c02d82480c4408400040030382e01c5c200020400c00141a0040055607a06012409901c100590b0032004003828090130072005a020000301d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 959487517 1250 959486267 959486279
    0x915170c03010c0504030206180f10020f0d0c02010819060f1e0501080105030c0d0204061d070315032310020f0a080c0405060712020709110405010f110607030b010315 73
    0x1009546180c0c118020002c1004009098075140150f120180d401075080c014001c0c052000c441d904c0046500401205460039040e001901540c0c54400500040c1c0c0602d5521198000801003540342c00154104280e541c0c2c80c80c0d0008000c9800200a4601045404030210f2144a55000100a4200b0fa003008814541340c104001e0100d03038607445065528103c0c02c00055039400349800a058803806400b51800369181c2c000c0c8440b0210a08040b6081640c4850000d0040c0d1200792000c582c4c102015051002c0c02c4c0908024180c820f08246401c00044200341000011003030f20741181c202a4041c425040d4100d038448071030409507585101c00c030f090300010f10182a0a10746004000061040d1603021f81525600d1900b55540a2400380c582c000c602040341038041080032040960040c000d1045846c00e9407140c44030070030344002070a289080c80c80400c080c001503802c5841005405c5240c070f404194403401d881c1d455955032001c2c2c240740c14142da8044c18491648079400c13401e15502151010152195105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 959488767 1250 959487517 959487523
    0x130b0d0f060b031b1819090201020c09010801050f0901020307090303030c1b08030916150e030a1e061a01020a110315040b0403090506162d14071509091517 68
    0x2c03003182d05c01d0042000f001007208560590b0b90107100da9044081c00c0d81060401413004107025503059040d80b0510703001c88640d54940b00f01c140130f000ca10b000840e9070b0a203440c0160407040003134882d048590051041203100c551201003142103a4061601154000e10680f060303030307080c0c00d142c1007030000500c00801d10b003440390600045009252000440c1d001c1c94a1140300420b00c03c440c00341e4041480c0d01009400400d00c501c840c3d5049903402401d50b60011010368a06141140307000300400c0c4048484030b8042441041e11509103200c80300c1c8841803c050314440000d48440410100906035010b40c05007595a450400004644921b07076080780b4028201402c140400e41ca04031012000181080070200b110300313001c0c1c103a40031600664601d11440070b03503aa9400d44c00c40c0304142aa00790480350300d03220500d0200b81d840718456009602d88104e8907480f2031082c1c04c00c00150043d0002e803006202c07079a08240d1044940b801c903140e03264006a1412041c1d055004d0440540c04041041c01d00a103c91000f5004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 959490017 1250 959488767 959488813
    0xc010207060903141303023a03020705040c080403080c1603020604050706090e01120503090904080a020c0103110f03060a08061f06080615131a0405130b0d0f060b03 72
    0x1d0300e8144c003011003011300c00f07000d10540a00d50548802c6210400044c104820002e06101c1084c6070140c0403129102d8410040c950024a00c140c0c7d01c0c40c0e5840c00c20b04d80c062091501502090380c091082e05007804000e030014402400080401000c40d00007109000f911065801456928000132081c0e000e600780295100c0301a18140c5d224002c0c61400500a405460390b4030032034420140140d00c9070f282c19030300840031032521010307916800304128490340350f40d581c015544103070300c01c014841d03c0d03414642c0000d1034003010400c203906161a040001c0150042d0f4401d8a442241111100e0361b43d50710100030415040040e4020007682c800d0105012004040c80c0c10b006038400f01d069101d44035a51440201c03050001030b22440d400044600040c0010200c15009102c0c9205041b0031031107055540082c440c165180c44448030542c04046028001454065032000c150003101400348901c820000000b000c1c0310000e0001025005000300341000c024054006076032040009090303446070007000700034401032500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 959491267 1250 959490017 959490023
    0x9030b16090b031f08370c062705031f060e04060b15090d0f06150312020f0c1509010c0f05030405040c0f08270a0809030d050f03070302070201050c0102070609 70
    0x181c00400700c1c11180006049042c003400c02c4a031550310412466030414661400783e801b0720300d5a40790725600800c4607942c401000741001d98903080c411120707540c01002e010140396516040452650100a6036030001030350042a050103c081192400c3d646200006240d20307030104220b0244201007006208207a8030804c00792406685d8108082c009200100240c810001000e52200c04100000c000c01c0d0171402d40c0d0180f52051800150030b20824041500114981d8402c85070341106003d402d4105a0501c003201c500c016100051051400220005100141404401c112184003044d150342503889600d4082000d83c00150000e108841130030000c0d2640d015000d1a4056420244003043c42c5118036203c0c058000c60765030b05055503c52041a0003012034029070420f41c5d00f03480281c0c6440768002d02904401511440480382ea50501e01d0a150500300d03404444401c4c002c040c02103514002c001b50850b540b0441503c0c006940b51610301c010384840c000e4034240e00ba13030b42c4007041480400c40554040380403140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 959492517 1250 959491267 959491321
    0x606070f0b18150a240b0f09120604020a140a0b030c0f04080312130f14010b060a0201150806010303020303070e010c0c18200a030b06090405070c1209030b16090b03 72
    0x502050030003018002030171a03c1d020798407500b080060162090280c9402c04090a1142c900700f80e160000b46082447e05d0740070010340002041c08118642025810010030071a105410701e4010303400004c0c0048600e20a0036100303c80000080c1031200355408646118001300001ca40311912804402c1c0c0d04d0300070402090071101030310041051100d14074203d071449a40300008004c040c070903070313900b207800c0c21480140d1600b503407600782c40042550362101408903081681d00000d01040000708418a040d071031b5101c0e00d845c1d04250b00500101354044100c3e03610138071500300b18041e80300600048404441200d4054582d4000f0403001c510304554401405416280c00c0c4103108880c0c144d1441d0150002442c09521050300030407100c0d001500030341200747d200e00002d00c40c50529283c5404101620001c40382840010240e00e400c004015a0810080c1101514a0b18501641c00d41e81c2c2c0b4031458401601d0f891010b0000072103450aa4030612600000d00300c100c91082e02c900b010100002400d00c04d02c88400050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 959493767 1250 959492517 959492531
    0x30506010e240d0b09190f02031b070f170d1104080616140d0606020d020d09090911090c03180a0b01030b0408091302040f05030c0a0b090a03051609050606070f0b18150a 74
    0x581c1f20f000b40c07030140002c20744c01c3d0307a8400141400a210744c00a401159450080b5046002191150000343d07481c00d00c80a130aa620a036041e0041c0c200c569010006d800d50905100c00d206514000030581d40c01082d40021440e1455420030649100c001d207428203141c0000082c001c81001c009801c22021a50941c00700c502d40d4644110170b0383c80f1174070b40c420007000628100c820400070b8541e821260001d40100060300540c81c3e42c0c0701080c1030803000c4400784400000002070002e4071410f107100e01d030a1404c04026280802040d0740ba1400d08106210283c400c5040501040901c01d0a404659112000030259203030010308000d10310194200703201d00d09010110441c00a440d0402003016108010014290800a41080c070806116049000079680003002c030b000100014108101c071038002051074085912140c94641c4910030340d41d0080c55240034140901c030050008400d0ba0301c00c0f02031580b080050826640e112000b0b14030340720500000f2003031b00c2041084444941c1c10781000b8041e50031040181328038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 959495017 1250 959493767 959493791
    0xb030a0b0a0b0109091a0108180105040807050d09030c03110103020f072d080f0d06050604080606090a020405030c0904021f0c0b0604050108060f040201090306020a030506010e240d0b0919 82
    0xc500d46c04800044008040201c0595846104410340c0101c54400c0c100502e8a803481071030845d00210b83c100e4403403600068050500c00c0421604200202d103117882380200d411076882c150340d8859844024101c0060a810800980c0a42c042d20621411004429110b0003130741407800e000362444540814030714507050050b0714000e15000643c003c82c4c21000c6240b8081410444500d6035000c00c1c4880b0b25141d8131500480c3c01ea0300d040c0100b0092141c400100403d04041082021454002d003e80348043d1041204204949000c540c1100c0c5040448002101769640d0000c1804010148801d0705010008101aa070a035000f4803c0810680a0424902c0c6651a1000d0104139402802500140d9100301c00180354031a07024001e40e4824810b151910303096a407070740c0c1c800c02c0c1c0e00a031a2581c0031a0311141080701d2968001f010b070000c51402c86100d11401c0c0d0800e98040b440201e1030b0b0b000c0c944d800c0007030007214070b940f507821058082c0000761240d80185010100700e0882604040c42d80290350030100200a4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 959496267 1250 959495017 959495021
    0xd090b0411090f1b0c12040b0703030e2a031609060602060603150f04030c0503030c0903160515220306200307080f13060606120b01020a0809040b030a0b0a0b010909 72
    0x402c0400826102c0313030500d21040b4940c540c0110702081d07150b10030b6614041c180103640002e0801002c1d1001141d44a1140b45406802e4518018255000307910021107100009000f40c090100c40c1100300341600c0351000038012a050072401929a42c0c248044400041d007141a540504111040c039030a540d500d4540740d0415480300c190344d0100b0b1500301c814020503d41d40c00e1100071a0800c1c828101480661400d82d80c4a0960300f08551139100d500300450b401c4940d04041c0322400305500010044000b0b40d041c540041d00c2c032041216001c01443d8007044049402c403c040412408240080d40c140c002656464035101400d07201508510150400c141c8040e410504011b482c0501c1d45034441803525641d0260505034803c005101d0811240314540d1007010524602c2100e01070200b60741c1e20300040c8003280500055030360078101c19045501491409010501c944207443d41391804490202d000d545520000c0d1602e80d820744042c151000c80d00500074811f1155101d004801400c1e269583d4256842c920042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 959497517 1250 959496267 959496271
    0x51b03040e0619120804032009150a0314160e0c030112020d02100815010f1b0204091203020901180510030b0433150203040303050d090b0411090f 64
    0x318001078000412200c0c6070000c1ea64036800044031030044680e907144241010241d0407042a50980e01c006018014000c01155881410780601c20b40c55000c080384000c50000140140302c14861290f1043c2c50a541d40c3c2e5038141c100450300b10b20014440b03001c440201e030300d4101d16100c918840c00000000590105614000c1c1d00c50f140c0c40c0a9181160701e0704080d02403c002c46801242c0c0401001e26485c0180d0342c1c1034194200c0c1c0c080d552003503803a14004130368541244031102c09038103000b07682d075800080c40d80c804005c1064001803000000388841c14804035000e41b01a400060080303a5903000c1d000b42690541c003802034008243da521038078144404503003036034191f280116070f00126616481d116041c000d41010382884000f41c0009102c015480c61440f00501e2001c8400c600290320058000003000034404030050040151400300380c03640036101944e603218074413000f03091060220b0840d088207829407094140c0e036009050f440682c682440c01c52483c245a855091090f000032000c519003c0f1140030030f0f4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 959498767 1250 959497517 959497529
    0x30606050d02070203070b03090a020a1403072d06021506010c12051c0606171f060c1b0609091b02060105310b10030b030c040f0f0903051b0304 63
    0x40d203030520074402507000c1d600100c3c1c2682c141c0f061403000181c045030000114400c10b000c1010b000c03c40400d07c10000c008034194024480e800391030744c41036200c0e40d0100d00d0b00704807002c110303244840e00c0c0c00841001ca000c00882d910070004d0100900004e0080d0007003104200780e15520f5518506540d410015100d203241002d000c4c000030b292181005565000f80010841d440a07039045040c20120301e036494040d244a034018000048507030203c442e810700d0440300139030003e8840304440c008010071030304900c08000501c00c0c4001c004207851402e06111040d0120101d505800200009130745e2203600141940c43c007440b036049918505010034000b106110f4504218201c240c0c007904007a440c0c40c0400940c40d1240410300800410064030084005003401500c602c080940804a90070486030200000b401c15589036805041c02c1000c00c1d003c076500800c0400a040044900040305c0d062510b041005045000b03002c0d034a20300d056040c0c414513070030801800c0c000385c03401d0954a45040c41d041c001e0f12400b80740700300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 959500017 1250 959498767 959498777
    0x6071a0c0a2003071416140307060305130f14010f0b090c0703020706030b0102030903060a1d0303221a090f0f12030606070201031512050c120318010219140d030606 72
    0x1010001e814814509041c0c0700e07820441b60b40107180032400303c403124107611604c810035040d250760700e05040510507800103000b40d0600700564641840b1060016140e2103004100307a0840c3c511174200402c0b01003c0e181c00103c00020000c96400b410390b04028941002c2852090058100003002565040d049800b489c2d4168007a001c018a0b11100794060080083d00e28103601085c442c28806440c20018244264000c7c08049621441341c01400070329840b0364441480c9400c2001017100010782140100e80041d40544004803181e503500708455903c1c101d202c1a202e1540e1001405107203400002d14031080e0382490191501075141c24080d5640700030780340043e0340411007400010b201d032500310040c1507024010704011854801c0040c40101c9501c90b03420007003030301c080d001d10341c414000204411000c0e444266112511303e00105030460341d038068010301c282c05048000b01d43d69181d10070700c00d02d608034425152020070035140d403600c1450600d1050841d121841380310301040b8514802e024002c00c480541e164 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 959501267 1250 959500017 959500027
    0xa14120a1107021e060417060a1803080f040303091a0f0c030112020d05030403051915140402040b040f0216110415030b04080412060b0f03060609010506071a0c0a2003 73
    0x266005134103082c030b18158445001d01001510140040701c444d51902188064032080c506502183e0448030300c0d46019070000620a800e1002a170815146134001400741a04444c0e41d4940c0380842c064140e102d0010841d0390401101c42140503180311080c02101c21034896a080d40d40c0c08100500c0340401d00c9007443e0200e0120900c00503040c426814006140184266440c040d102e0f202c141c60030301c0c40740100f21101d5a080070176051050390041580c4c030361020542800b685680e0091f0381002e86019001911a60303580e00c94150b20b40e22580a030480c081c810700107540b659164007004e21405000d64060b901240b40304600c5960345004d02ca0208000300d14288243c0e11401d5444560344030b0340c001d0088640e000100004140e624200d24401003161088002095030507520b82485010011100b515000740c0c0004107008160b03544188041c1035800aa404944400c0c503410b0403001030850210380c0c0c452020380c02c14024420b00c0b0000505c5484d101d910754480c000c100c6000e041c03180004803400c4515401c2440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 959502517 1250 959501267 959501299
    0x7170c09040b2107170a030807030b03010f090605060a12200109090501080a210c020105090f06040f080607050313060506010c080d05010f15140a14120a110702 70
    0x400207504100c041d12100c85100e007070203c5001600003444001040d0720000040080b1420003c2506004241ca40038060100281e80c02030101440a400a800d0544420010503991803d60000f90070f1450b504040c0b061150074103008000300010b0350b0103401402c112f500815108081d8031030022056008a0380490000c00020b1030316440c501c400c01a0401c03112070b034000b13000030460080134041d00c0721401404038010145410104080c6000742c001c54083c01c102c09140c0720703130014001070305640c082c203000d0390f291500c1000885400c1b8000000358000008100070031040c5c01c28a4550a8500c640201c840355210902c0c00d94090204a440203400d00943e5880d00004a458001c00e41040060500c0307000e070021642c590561340c120a0003410001e548200400c01c0040701031580000384050344882c0d03a04024034800914001d265418206080b07000544210700c14468412204810a66095a51103165581104900000c107482011309075050102c4401044040c000710b4030383d154020405400300814030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 959503767 1250 959502517 959502521
    0x100308090609010e09040302031c0624140d0603110603040803010b0f1204061b2f10151505130e27010f240303121b0807170c0904 57
    0x1482c85041114006070204280c8540401c0b9003e944645c024680701d248a01c8080481c0507072002c0c502c6618100502044a0b404101c03006402c144e10010501001030b2005041e100c07450300c11107a100800d00002c1440c035541081d070212042d80c1c441ca119549043c1410100202c0340001d43d4068046d0f0810001000803194540041405c101a038802c1410030540c2102c0b07400031402141c0585103191039443e100c184141d0310030344180b51040c40c142101c0d26840c00301c000300c440b1501c1c0c1e0041481d01020b20420b0720fa80042150b026400b008640620400e02a00139005001e0b80601c1602100c41c44000003001c4980100240c43c240104104210702c0a45400c02030340d640d29019043c4103045184144028140f13070540001c01d01d001750400082840c3e000a2010740449a403040c0c01440301d8003d2024840448040a0400480e03406103002d150b84421110180010040d42c0d80c0501c00504101c54480c01903000f100c814410440c0e91521300c3e003a00481501483c45604480540070600300f0403a0107446c2c076250f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 959505017 1250 959503767 959503777
    0xf01060605030f070e1807110d210212040503040303020d030c050313080d24090b0f06070c0b07050109062703142104050f1b0f131a091003080906 64
    0x42c60601c0d60500d10078040391034610201005070030301d21b400c010800701903001881420300d143d03100010003c2400c03001008180c000740c4408400081001c0e0301035000c008054040e1001c0c0d181102080b00d881c10513150a65076540288000c40141c014416194441ca0191041d5000c803c1c41d625558956038919150015113543d20358100e400c82c1c0207101200c41d460a40c4611003034a0440440400e0000d81c0749007a0000d4000c96110840701c80c1800304200d901d4840382c0400902a800307544d031544421342441c040d010011140c02803550a81c001c14124140f00c01504407100160181e03008110003502c2d24000203411495154031000781c065045040700003441b8104600f0080008002d25080c801c0c038190214541180074800c07151f05009005200c00e01000303128413010f004007600140100707510200640c1c21201451b65403803203243d641c840c50f001d03074443c0101100d240d01003800400200404e48060b00004d110090002d01940d4080000390803000c44a02c1d800c103981e048080d8501703180801040004680c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 959506267 1250 959505017 959505031
    0x1b180108060a0816050109080307030c110d0212060f0615090111031c02070b090c0a031e0b1815101710090b011406040308030a2a030e0f01060605030f 66
    0x200a1000440f180103100804040840480d4004101e2924000410482550b0040c01c02500100920000250803803d0b00e07041a6002a400009060940009004441039840070b0741020210145104514010406c188203190740c00d88502a0380751001804020020400d1142c008001000400d482d58004d805c004011180b020450745017408441c3c81c100070f030446c0780f0764880d03a540100782c610030080d4400c0c000d5840002130000703000003002d02c400070f024599144806404900141d00000140c448400c400492540028540e265402c04092000d40b0765009141410117004d424512072124080c0c00724035015948500c038000305103051000017403607031000346400e02c1c440c401c4030706a01e00f40b06580566a080c500442048034070358904403500c16841c40e41501a4031425042000b400010000c4007500c0c0c000c004202c0001e600320760390b4102e1601501042400340b000907100300c01000254160040c4c0c44281f4040199031145410301d0800c3d090b42ca1134010349020500a00002c0d03020072021301c103a80c1c040740f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 959507517 1250 959506267 959506279
    0x10c11041b0c020427030c050c0402040617360a051501032a0905070e150903012a0305091204080c1c15050a1e02031b18010806 56
    0x102008000580004071100000b10b20141e950106514040c0709a001c440b00c0d00303c030840021441c800314580704e40700a01c01028800c000b013150080c420100800018030a0107041195100e40750140a04101441c02c421b50300b0021010014000b120031507090034407800c1c003641c2041c07100fa41d000a03403a072070305034a513501191049140c501d01003001042044907240d681c0c04c0700711a65065052a400744004050b0403020540c042c1c0000c42028000600781007101d8450900260940350900c0886010020300f030155448049011005580c102a00007019104400c070020001440409069640900000041c075a06107420003400b0400740260001b80c0d200c20894190b61440701615113030386a41e08143c0000000758071505040c4001d085c44010707481c039a4024240c548a0f02019519081e50304000070044446580381d0010a1424102d900a80c250750140c641420300d00ea0b03004c0181009410032140c0707070490100360a90040c02101c010494501c20109000b4040785040900103441c920000b42a86070011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 959508767 1250 959507517 959507531
    0x201020c04020c1f0b041506020a030c170c0c090108010903081b04050d030206010602120f0a030e031b0307060c210b01050f0c061b040620010e01060e0103150209010c1104 75
    0xc13204460891080c10300110010311118040203100480d4141400c0c01c0c22402240b03028040c06400058411030a58189081012a1032501d00305c104d00301c03400d440024220010403400c410503008510354008000030b50301982243ea80344901400e0b1856a2005000b0034251030124010608090801002000c440c40040c902540c83d0041002c0c100804070650043c2c12550050006550600010503a610b004050a00f03001c05d071501202984240c895000906545d21603011104000b44180c922000d910058116488110034000340c4a520400c000c4401c2ca1501e94090a00c0d809244029020503041c58280342c4030190400040c010700055003071030305020b002d201c08100018070704000c0035821105005080786050484260011000744031283e140484240000e011056100410540e00ca654040702c500c1c3d0801c04006a006081c100848403c41d420800007041202412843c0f6040380d101e04072800300711f650400c0100403400b40702000f41c00940100580c07408910300c019445030701704000380000707584 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 959510017 1250 959508767 959508793
    0xa03030e190605130b0a0e0d02010212161403190804240f05090d02032b0204080304151e2604060507110604020d02061b16050f04090201020c04020c 65
    0x440d0442d4444000258002095042074074100701d40d41c000e05101c101d9905100366613001034200c180094256000f4003102041c20103582c0300704116400d803588562a2a51201200041b01c03030003881c4d40080d030702510403c0c040d8a0f84140002110758210240341400340d40107084404881040300640190340c5507450030140004031054481c1c11880000d00744002500d03501058600c800d852005200349800d0700045030005810f40c001c02200c04910003c2c018180301604074100300701c50702003c048413100510108011900410000042c0240c42181014003401c1920303010072140205184201d042242c07810382c4041c6607a00603100c07003e00000c4650803200b51070422601c1c5030294402c560580340a500c0340180a2500e13003000c80c4d0b06115141030054080d038501500419022072003884001d0242d03500184060141180b0299820411414001d960440804480040301e200207030049900c10480101400741c986000d01c1113164665040e0041e025a00c1d9403410400250024140c0194070b000d07514802c164 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 959511267 1250 959510017 959510059
    0x10503060429240306040f17040306050f060a051507080a090909060f0c03111218070f06091d060d03140f1b06100317090406060c03080705090a03030e 66
    0x1c644072008180144002c8100302110714259803c80f140203411800511000c182d1101c110003001d0b0b08000f00e12200482d0f44c2903c60306216990003d09111300d8081405000703505003086a00404c8101c0b00303492240d46420401000040d0030710021710340300c000c0200700d00080294010b0000c2c0b001c142000e0070803a59821a81040e244840b80c2180c50b00d548840d50034601d40d45105003901c0b1102d5140801c1320102d9050700202c580315000c91842d1040494001503800020042d2100300c0705600c105031546680d9821416140d41400c1c0154004180848000315619042d0000102030b2200c001045105403207090601001c42c0c0e41d000c00b40c041121401040c0b4000c06808018180900b8042c41d0603a00c41450b40f2040702c002020072142d9070f64100d83c003400b1003901079940718026281c209007441c0c05102c0d820300903109481040c101035082414410001a010b401103a1040d401d03000b521007162654035030740225264811300d035076150b01038a003690074070100348509008004654081c00915100744400d40e02c0c81 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 959512517 1250 959511267 959511271
    0x14101101090f0b0a11030c040b071b0b03092103010302010c0507030506010b1b12071b090507030506030d09082d010527030403030e010509180901051e010503060429 72
    0x1812500070f0107022004016100340e5500b1342c80c9103d1a82142020410714005210b01d00c00c2c1000280c012807a0710510000d03080e07544091609103181c2c0005540c41e07036501110380040700e40800d9401821041040c106004003280b8002142031000c40c55a13003943d0056074640c0f0000415076241c810810040001041002814041c0400000c07980e00d030070b504407614005111403c07800040e0340081204043d01e410a8003a100c0d03041c3d03c0702030280f07490080030040281c00056401011011b003402d040c05951601540601c0c0076040950507a080ca00408200f0f440282044c400d008155005c0002020b15500079540c08111060980c52001200c1e070808403182901d40c142d52500200510031510032001841c82c01202018440e040514209403960714041c0560440000c880e0600000203040101551790345103800ca081000303500d6075040e081502010f80241021902d5803540202c0810203010408182040e0381251303c01802008590748a60303030440d03500000311900b001030b05e21303031070703480e425070795800414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 959513767 1250 959512517 959512523
    0x120f020d0905100b0f0d06200403290f0a020901050f04091410080c01080c0405030a0501200403150f020403290a02180f0a0b0f1314101101090f 63
    0x1101003e40c200e504950f410585184128002418031800f600d89104120b0010340126000030746030242500d0f0300d50007110445004c042c900009021081100303002c0845000485009021001c0c13502940705c402c503420958802100f15200c1c000500314420a0300209079284061401d5030410551281c4400341d904280c0088400d1a00d404a171210742c0740e0b4080c025840b07400e0100400c80b05150140264540144041c040d04000d54100040c0040001101f114014480502141c215011605055000b406661160000c1042c0d400d490740ca0440c1071070540d015650400420a1000b01050401005015540c21080748039024080000801c020b82001e8030400245071801808083c0c4171600b0080c07400003406990007920600c0110980c190000a0385170b001e00580c0d640a18410800009442c650f0550101c194458002509139841f26040f014002841c400002c841e80307592124400a00240e2030320070f09400079010751108030361074400c4081e580101c030340d10b000041d0349c0380c2c41d2034400c2240030303000d002e07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 959515017 1250 959513767 959513773
    0x405121612030c0801140109051017010501031104180f0903081506070c05090402011e022b0212160803180d020d231303030c1b0501120f020d0905 64
    0x40041c0040d20040d410305090500c0c0400500445500c05814404180218114035500b00070106a5034050344441d0081c12004042201c0302844035401011800039150424031005040f00000b200d500034040c5110702d44004072a5801c2605048092103500b40c0ca10074400140d0300c41d809401000181d200f8084032500036900c50480c0e141c043d00b018079000e601c0305c038030f8041c040c10007140c0301042c440d007a01019200300700d8031040140c40720300040b60540140ba00f0316000301107202c040c1502d40d400040ea00f02e281101c2554680e1100c8030000310400c0c031b05040c032400158018550009510304e07441d00400e8840c0d07001940d2400030800c1c1d120b00712250070403110548450489540403084550400c01040d00e02400d00c000c01140341000c0000b0890640da210078146104120b614080981500040d540050400048040170030380e01e09005001d590514003d070303514042030500d84102680c500d000e5040d170b0411703111403001b050080c0715035000380070014102403499824858200d4000c0c15000c2c0c9030825000e0303001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 959516267 1250 959515017 959515057
    0x30507020108010609030b010b0f090a06022503050309040207170a0207061b121d0306040b06090c0309030429180f0f03061602210c010c0f0e0405040512 67
    0x140102c01d060b00803000348401d9150800005d035a03c6540390545070381c564090344601c076250400c5428050141c503142c0c428072103000458169400681d9812080503030740b4000d43c007000c200646000046a01000e40f00760020003a000881c01e141c1c000b00340d528440d800044445010040940c6a03800098071800142c2080004001c002c0d4402c022050000c5403c8031400e02400c503035108140010340e200c418050010701c00c081074821805100940314828050b040c2e0703686103041e00c1c004101c21070450741c4a100c0d14100c808145021071200540784294003840c011454581403040210300c0b031051005413095014148035a0962103142c1c0050400c0c044608010700c3e60313400c150300b004401502e0140460140300a00308094080e075000a82a80102011341031160706517040c43d04908110704d1044c84c0b000c18142441801000b10f0710b100405c04414014000c0080e0003030001c0c1100d079010512074410000b192202100624a001d40c4501e030840d1180c0c00326244044088501034003500500241040d0018001c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 959517517 1250 959516267 959516269
    0xf0301121b0914100b09040c09050616140c09070e031014060a080c0d0303050a110a02030a0905092e170d020f0a0206250f0602040302041503172503050702 68
    0x2082d03a0000300c0c085030004c206060120008650040307182c01881140c4500d03210b0302c00e07405840e141c1d02401e80030301480e95484500040041c12503140400711030301040409602410761002c95030a0328420001d0007000d00380c484260489040c1400340805505009480c580f5003115124400c6e0711034005d4400450000d468140c0400c64030f0101c60b801858075400c1141d1402696070750000d0070080750785c14200001e054858060120041c550556040401e0348001380f5020129000000741c00c4802d2a0359800c4250783c2ca402c02c0c0040500c094a102149422407560150380120302004003d034414039096141819560300000c001c01000c081c0e00c3d9000350040d11040420507030600910740800701a800a01114815501050003481480402100000c1d12080c80740407024002800e0a8142c00a1342108045402c0c148a00290701c24401244902e03d0900b08081c0300030103c8001049a802206104031084107072000412a4444400741984489407501001650003840151200c00d02950704d032502d802440c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 959518767 1250 959517517 959517551
    0xb0306160e0a0b0904090302070801111b0d0203160f050d051917040f020307080d18061e03051e0a0c031410030305090105090d060f0609020f0301121b09 67
    0x1440d500684040c2c0c800e100c15008402207950f20a002c1d240000d407030000707090803800c00c611500206a507508150b400595082c20704041c10b0309444000800c0f00c0045200702d0655140c00010074000540c00c00c0c8215071404030541e030110030a0340030f07600503010040c8aa42d018240301004030a04c004c03603008518100c0086900c100381d42805168149503048104405102108540043c4010304120300000001d0440d1810300c1000001c0c2103603c01c4401c45e03075402a0181c40c211030300112011b02100590b0005540e0701c24034642ca0210302080304600e204039441000c4000e8031009181101503249001145a1504841e210501c5010303010400203201c4070b0410020300342c4034000d0b4102e102c01c005405001c0d02c4846a11504112640340c24101e59440741200141d41c1c40c06229a20340e8400c1241d02c1d504140002900541e0a260040b201001026180d403050800ca002c0c030551150400018001440703200b0400034020301040c001c1095010042b84149400903215107908040c14032a12a00c64500390070040c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 959520017 1250 959518767 959518787
    0x30906060b0c07030308180a020f061e031501030c17150307081605100212031e09150c0a090311150a020a12020a02130515040f020a09092703030b030616 67
    0x129800c00c1c550720740b03c4e040359548c0d860004040c3c49621784800400d030945c0d942c3d04803500e180d01248a0f00350b012041c2d040711b00c540c000f19041d001402c43c584010000b03621a204c0e0004100480d195001450740300ba1440d5032541c0e005040c3c000e04107004002400d80c0ea010400c040041400c240140115a5004c8001116840d2071344030300c0c040e400104147d2451030300410115401c01644031030685a50369a4804044100e50240030001102240c040c0320041fa0013064040e554588c44004004607103480c0e03690310300c51054855100000380401c0b810700c005100b59005040c00b0303100600300d1120300030494405800d5404a8100c1c4090f03805440c0103010029030410041c102202d41c0090201e0f85226008102d8002c05c001000d41180c1d82d901c0001e14040d11002c0306012444040c104011006002c41c21400951010b03d1820100f04c110310b001134414054020044000d0401200c11145d04503040d01c20280c455410085042c1a1520742000d52900c00700302d141c2c03041080f040b107010410200900a0190018 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 959521267 1250 959520017 959520031
    0x9020919180c170a120c03020d180501050a02010e03040609260604030806180a020408011107110f150f040504050109090c031e0c0801050105040506120d030906060b0c07030308 77
    0x14a070050040303094124403004995050800300d1008060012240c2019100714004240b0004115140302d0385500010034643c482c482d808603803011200c45026076281c0c2c0f080e06c541580c00c0d00088140100d51040300641000b5249000105904401c00745850440d001038000f1400507548940c10021300400f91114007461154a101035075038200986c0c25525103600030b00280a100f08540490500d0701c92581c28151603030202c01d40c40c03540c01c0c000840301c082d40c014443d04d000d640c2005158401c104440d001c9481c616440310301c620079400301400b0b02068003425080b00c1c1c2e1212005004031004080600200040050740030850b5450b07061400f00411504180c008400c010f15100d55080003400c80c2215209480e0000b0b80240c500b116220306041070f10300386100520703101920703000150000e815080f03181650802c0b00c0c00c0c400c50340d84501740000f108040201020a92202c10043c1c203d0b80280d00c4817044034041c4e280450700390340f03501000c491580195221a21a48a11004c10916510101c2c1c20380140d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 959522517 1250 959521267 959521301
    0x2901030b09040507122f090717061002010e03031302040c0e0607060b13240e04020a03030f020c0d0f0b07050306060904020d1404032607170a09020919 66
    0x3865150103035102c056002e01d03401c4c400d14140700320901130f0b54011850b2098040003060406c00c040d180030201c815030905c0460180451102003401d0b135000e449440803034040407030460540d0795010f0801c1010501034200005555940940901c02cac40148000c52168042d00e03040d042008135403042c803080ba41696100820040161043e019955583d81110100c58214401003408220400000c0454000c2880f00720031034a0882d641c0c007511183c0144140420702040b1030074116580e40300307000042008407002940001c0c514014000240a81503c03a00b04400d8811036207072032410008114484403105040c2c606e1500050034400b001f600014003603221030a450240c3c03c42c1410804a80503000700624184201d0700881da88200d010254800c4517010b504144102041c1403038180906209540d51003680040b00c060921003070201103580d030b0ba0180b1a95035032800b00545014600345401005020043d0007501da001c01c00c050fa442162540c0541c54201040e4100d000c0100428100e0b81101c001040802d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 959523767 1250 959522517 959522521
    0xe0f121f1a01050c100c030e07090605011e03150608012402100207080708280507030909050618100801060609080a0f020a03051504021017192901030b09 67
    0x10700900c8071900000401e00742251580200303c111400c0105551400003080e00d001240b4103c5941178108441c40410390741641c2010ba1240039801c181c6841d40183c80c0450704c0051100c41001d10600300c9146800f991900044810610103445030212503940407100041c0080014441c100c404800ea1050f00000e184002c400c140303040d406510703042413800a1101c0395002c1403071818416840c00b21808950f1264010383e640c01d089200e41c0c1110300402088040d1030180310300c154858058011201c205030180c603a18282d5142a400d400a064010724050700a64607442c0c0e01c0550201c0109240503000316202c0c501c1c4541000d10040c03c6694039030240d4104101008100880040450b100138280d411420000d00c80f0014000310301e48000580c030045c101d100e0001440d0074100007a03a0280102e2080762040d41049a49004481d60480070040c4034840c0c49070b44c0441c042001c04050094030000940e004920a08284c00401411402c0d00c1000c070381e00304646102c0003d40c0d0501c100444500100c1c5c2c61a558 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 959525017 1250 959523767 959523791
    0x501141c0c2a03031508240903030c0d0b0d150b0907050a1d01180b0717040810050405120c0a150501180203040804150c0212061302010e0f121f 63
    0x1682d41e401000e8281591901d02c900741841ca0800040a400000200c0700d829244001106450841c401011503102081b0041030458002004881c002d183d000b04072410b0202e005a0003000388040b003000c603400300e102c40840d0006402d80215044041d4543d42c006441c02004c010300041d00c50041041040100c01c22403007490b00d800c000203a00c0d02902c1d048040720300c02c1c5400144c4000c541172a0302e40c4081c203d1100005c2c1c02e07103994000c2001c030303100b8450956250f03403041400c1c0c00c6000e2401503014682152178003030740900c0341d50300c071a500c54082d4080760720310358007804008241d038025255042c25410208052081c040b0b140040b0380c181a000c2e0082019600d0000c8090700004602780b400021900040441c0900c031004040c7c0740503000010104074580c0c030384a40a4502d00c0e461104034059420590071418403003004c159580b00d5034030519440703140c030880d80c011078014107213800856001854112818145d115580e8881070a16208010080b510212031507580e20510792450b0074996050180c11551 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 959526267 1250 959525017 959525087
    0x160905100518040b012a020603100801110306010f0c23031b030a0e010f09091b1e08060f0a030804081e010501050a1a120901060f0f0506040501141c0c 66
    0x46d01031081d0400c03036445d041d4030440046461064020f5401400481840445501424000102e81c0880e0080000c5158a0381c0b9203080d0004076040750124682c0d0b09254880b902844ca001d202030f100c3c04201000181540c0d180b81e1062848010009039070011403400420b510310340c1403105085040d40114102109a24010211000c0703003800c6d4104400c170909100914027506a4402400900000f40700013082da2030b0310403601941e40842030018406414000003626003070021003040046644440c00d50342d84a0a0100c401d12440042c1e4001d103068034000017259001001d40080c0400601400900c204a00d00d80b600380344540042010381d14050040020b5511300c6440c104441a11583c1c5044000b08020407030f6600440b600c00400c0d1501c001013028444040d40140d0030b44018040b541e00e110303110316900b550340846018494014a0400040c0301e60f40c081e0201039007508108209918000c4142c00120345000200700010020383c64a2800c08026003118110a15522410240c4840990940303600e80c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 959527517 1250 959526267 959526287
    0x1204082a04020a020a05010903170c0a021b0a0506040f03030305181522050c0a0603062706081014010b0c06071202040807030c09050f0f160905100518040b01 69
    0x7200e5a4009001d04159000f84541c810181c0c00030300801c200b18650402405a107030243d1454165104c4e180081d07110305144007580d103100c240c0d500800d1034140d0743c109018040c100c0d103c5140d0000a801c400107203691110300404c040c060342074000b0300f504d240d454041d0a80c0d9010b8041e01c00303101e0149602e8840c240c001444071903c00b21401441040d2155503c1c1d52100c43c01521440d06508815264400d0000014140ba248001550300c0d905055a07081c0031421540c69000e161050241d4508150040c442c6074001d600c3d92041100000701e1329602c503802850700011410031925035454450010282c0d045132242c9004009540c203541c909280720460680b1540f00074060028000300325240f90000c1c0c2981e0564020b000c000302150421354407402c08032103030001da204600d805810000020362403082d43c4401402205c26903141d080d01d843c0c0d08005a02104101a264200700100d9000a0561395100c001d80e10290340351244c42d036800194407190f01002034244d01034040c0341840200002c3d40d9002d11400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 959528767 1250 959527517 959527519
    0xb06010e0d0305030c0715090c2408040809100f0305010b210a1407210603050c010f121103151f03091b031406101412010e1204082a 58
    0x1381e50b139542041040c814003514002030201104403040c0d0107080515405100818099038680d00040d0f45e45030f14685039607240c2820f04480000c001c40c1400315002d400c0301a04144580551800c04150320045620034826000b0700001400100e8200b41081c0c061184501501200b81e90340d140c025100760240503500e131064240c42031003043c00010b10700e02155011070b410340741e9660010100d040903040105040d02031400705426812000180305401000d1207000c0440c1e81c010003800d0402c04079001924404034064003e818400c0f541c460001c812494820301000003c1d5200f00354490034025050101c40080d10043c0c0d004001c00140000c8801d1160141180c00f0954034011800c90040c1c9010340488a503a00381d02a0a82c030408003004000294512300c00880c03048044502e01d907038544044980c80c2441c401c410401160f090034400e20308110b1041540c1041901c000701d51b03500940559890030031075903162449104042018014600d0038040302d0b141e102100461002d90a02c807216000c00c485a001032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 959530017 1250 959528767 959528777
    0x200a090e1e06030c150c01060e010e0411060d05040507060f03020a080c130e0907030215190507020607053004050f0f031c030509070b120402040b030c0d0606030b06010e0d03 76
    0xa10302d80e80c200441c88541c0d50143c02d81302030610307404100089170030001124185500303221010442245e9400c0260407680c0c41c00c0350030301075102d6842e202c8240000984164210342c0c1080180084d003a98000c880c0074602c250000c020003813500304001e020000e090324400805004000c1140099440210f40f608000b42c5c00d009603417528089e03d82c4103d8180d5034003140035510382d5800c000800c4008510102100d009541e1113032009085542100503101e08050f41c1d00089404046a480c00d110b40b02510712688064146840c0c9002d588510b4680500214945644042c0e8110b000000d580a040c00400d5084000c0e120305050414001402c07150710802c20a0141d01c0380d10310141a607404008075920f0140044965543b444400001000f4140446105806d4400c1c00c000244000b201400c842d65505420700040c41a01c480c1c1c20440980119107078181d05101e10a0b1207191030b0384107040c03190064812000081d03114035515103100340c030b18010461070500c01e001001c00805e44501c1c0c2400002d542c14685 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 959531267 1250 959530017 959530021
    0x108040204110c0109060e010c020a030f08061305010b0702040e03130e1003142107031d1f05070c050906150f1e0d140712020904200a090e1e 62
    0x8030b8040ea00800d40c501c503580d82044210014008161b0002109030080300081c00f16941904d03040c0e0751064a200001c00080c000106026034601c40c1d14a00c1e00844014280e5440c1e40304858801e0580300c0a80003c1545440014030404611705440740240c1c014082c40607500300082d83c810141402154031407035208074120400a204485038000342405181c0c000c102c1000780e031285002d0faa6543c000403090032a0500f80034410303150540c20042d2906240d05a485c0400f040c424100000100501d00c0880d810801c48050a0009400500d100c0c000c01001e5466644803012400c0c200d924040b194400d600480391041440b500d516910222004140703a20311071990b400c100c0500704007a00c0b038090a48404003611180340007060071100105a03219020304284000054400a4500f1400c165107000204101c100541e035404000d402078105244001c10000d0034510382c2c1102e0001008014400c0000b11000800b141134682229641c0c02034148c3c0d1011410616003016a111031280856198400c2c3e085040 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 959532374 1107 959531267 959531291
    0x607020a03110604240902090c0a0905060913050606071209090501150815032404050f0a080f09040b0319140f100b030307020a0e070206060d020108040204 68
    0x6250172410210115140c95146441407000522612500e003071016070740e46400144116401215030b665030200420090040d03480b60080340c4140b000348901d101a40700d4031007a50241402e9000010507443c0c01001070304601034003000802a903000003805085650000c1c4072404c0b100302c0041030000b0703600d408420340c000703102001c030300f00084010000443e510100166141e40010180a41e0416000b070b06404090040c182031004c4281c0301c82c0b040c401040010059204010f41007409006052640d40e40e80031641318001075151103800101e1607542a43e5542e002c00c1034180028219024090704802084958500c401d00b030701c8105c8903822802d034865000c2000b00c8540404409043c8001c90544407400900107030285c036815110070310580b80113031980042d043c00f502c0e454580d2151450410340082c5002c00c001d1a5601a080b400c14440050b41c10501c0340b50099811200403440d000044 = true := by decide +kernel

theorem cover : BRFrame.Cov 959352517 959532374 := by
  have h0 := BRFrame.cov_init 959352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 959352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 959352517 ≤ n) (h2 : n < 959532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
