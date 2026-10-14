-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2810
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:48:45.231721+00:00
-- url     : https://prove2.me/submissions/c2bff3b6-6a60-4577-a59e-044fd64b7bcb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 505215827 ≤ n < 505395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 505217077 1250 505215827 505215839
    0x70203011b2c0d0302010b0312070209060f030f07060906080105060307050a08060a0510080402120a0503030a0c181221022a060a1205250516050f0706020c100207 71
    0x60310b40e096802640640000100c1c00c0042c004030602002140582d448200c0d00c55140b4060060000008000c040c151400342254002620813500030515441841c02c808000c0c19a00c0801c034101048111404486090751107020190a4000030300c5407400050002c800400c0c2400c190060340e000742e1098403202d0410080c2c0320305881208006061075004824100001542d80d2800c030030403440c41c0c584e1905110b600702801400034180320000c4081c06940501001000946c00204580d07000030038410028800c88015421141d40e0801c80c28070303400e10920322000c00c021440c0301150b180d5521807120300310141803a500c090406000c2c00800405a04182c0a80100100162000c003203c17040d00d5200c50507031503120014540741c0184401e0300002c3e040c442450407030f0300e5904c1216003010010080a05c1021b1a1101c44401c0c4400015501040b9001c02e1503121400a8071404503d0341d44042a51003405604110580d14091132049400500c50121444001c2c14424000380486080e43c0c09040f09605204c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 505218327 1250 505217077 505217117
    0x30b07031a10121112060d021f0c023601030201020717010e060c03040515060904150905060106020c0301061d01090510150c0b07181401090306050408070203011b 71
    0x3040720207001c44000f200039004200c2c40381c40c850300801c2c0b4155840340d14160010040c070348000d044034040ca4900d120480540c2d40c20b42d00400082035803041200c00001810f007201c02c0200d81100940011000e80340300c0b2040003051103902c1c5001500e5021910003000c0312440b4084000f8800a07025801c4620b06014040388642480d8800140c0b2001103820103951400340c1c6031000c03c80d00c1a605080100502c81005014044c280d42d09010001c400d40a0411800042c4440c06c0607000602121004208403a001d01036003003041c02d26040700a4852030b6950307140280d142d81032844110320951801c3c901003040682002003074111300c3c1400301401350340e080c03807151070041402808103034048060040c0001c40388886960340d0700034442c5030b1380c0c40100d41c91880d1010f5002c03030180248041c401d10744140c0407820b8445842c0b00031031303203613444032110032800000690b4201082c1d00060308850421003040300340b00c00c0d0b0008240e0940700b50020000c001c00343c240b808240392209030b2000025034642001200002c05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 505219577 1250 505218327 505218349
    0x14010311180406050601020c030a11065719020d0203070305070e1501021f060f090902270a050a0b0a0602010f060e15060d0906060e01030b07031a 64
    0x280c50303000c120003207080700310002008450440d07200b52102e041180650f4103100c0c4402d030300d02c00d4000b4190400305030b88900c4c00c24080040386001c0d01c0007007411549580e40041c44103500441509000c0003813404070402180c2c007100c141c2c0d000703503208074803006440d0090340c680c40300c0c4808100040d000034a890707a6508211102004203988c0026001c1094000d6581841035400940c8100c0050543c2c600c0d002d40d6458000b00100032151418001c11100c2440e600030402c845d038007403c07680706181482030b25805801010603800c0902c45040f40e2070085180412079008000303040c002c40300d40c0b001d0341c1240110269103161903032046d004903030100803035200e110f5900002e410074440c0f1130101da484044c4010072030f0305105074442c0d4010b0b9100c210041400701d592081c44042c00407032400364058549804100d8130b000c40c58501c2400380f400001c0d4040d0310400765005111883d8840c40500c00656192824034001100303000903034181d00000d0200360014024400c403070582e111040046101041401000381c00d03855 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 505220827 1250 505219577 505219579
    0x90402040f02040f03030201050901050147220501211b050d1802090c0703050c1002040e010e0f0c03040305070b10091a090f060616030302030411010314010311 70
    0x44026080c0c07070300d019001400182946920380d2010902e1403e0080c2034400c00761503040c1a034035000060050f070b40425840602130710380c1401003040d018020301d042d144461410036803590b00c955060b00e0a4041646004001c400708204105614440b050034143c0d1040c0e0511802c2e0100b20754010f1090700c03008494954024120414000a12540200b201481d001c0c1066079640000d00010340300054042500c280341c0040030b036920383c080b400e1069000c2040300d140a0600c0c10001d001064460402d882a4126109409514107449522030b80e0390015000e07410600030810444401c1c000461a14130720000107100c1c1800342d4030808642c581061800841c0d101030825800c00c9802c105440c08102103100c800e014180c040c4250800d50320700f540308401c032040d8900c4001030042c4848117a01644e2208400c80d0032000c1c4581c4440030751100741c0051124450b40d032191a4145803030ba039020a05406038055441640290340c2084c421a42200440032030340c480501a80b42e080000c010310224243d004c2d11500448 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 505222077 1250 505220827 505220831
    0x6030c0a03200310091d1209060702030106260d1b020402070b071d0301020a05070b09070302100503010e060a03050d0f02010612080c0c1005160c150e040e0c0d0209040204 75
    0x2645010740a200d0348203c4e807480c180700e2881d00410540005106031100b03050002c00036203a4000c40300030345864613441c410500300d0907008078007294280c0d5920215540254024002c00c0b0080d40e13040c2c0b080707181c6201520340503059014906850080404240761f0203100c11035603500384200c244034000c01e244800c124160b81147d07092006d400081e1030b210589001e03100701c1d1501e940d044490302c440d941443ea40c0010500a034011311070840c44c55000010383d0400d0350300050132841036440b01400c1c1e1911180354806540303c42444000d40c54160028020f6040c2c9919990505290392000280325115520348001031040d80051810b80c0010320800441030031040078130020950642c0da140d0340c2c8400c202c041d0203603142200000d002c00c1c5c0840401503996642030643e5480420040c40001402d02e000f80140e652012110101c642c1c20004040136890251031a6808018000109a401081c86401c68042805903141c01201c05038804001054070b04028010001ca072080d02e15401d00c8580340340a0300407600030b5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 505223327 1250 505222077 505222121
    0x10306031211100e0319020c010c03030f1b0804150507080103060c090f06020c1e15030406113610231209100504050a200307090b0a0506030c0a03 64
    0x1030f6580103011120304e07128020340d20b844000c4800c80d21740104032054010356000030540354040c4d070000203c07001c00d9090b041c001690b000c8800001e015040185a00c0c00440c0d000e0200c80b1aaa0070031381d079a009074043d00341c205240010341d405500315282506c0c4000424040001000024169002041c51112900d0480b802d966921b07009040008640c12000268100c0f0041c1e50b11803d018050b0010310f42e090210f0b8980320b105a02207410700070703550f5800850510000000d41403040a400135003a4407d064000c80d568900461010203281a001084a10701001050001060000004404132902c01071a1031012078121400b0740310151940d000203951444610700000b00b40580d07000c1c20141e03002034862b4410340b500c010560304149a0140c001820b6107000140000f0900004003c804990b001d00c02c0000030345201c04c11958900b854a6060741440340c45d601040c410420381117007c00020548801c00d080f80c88008110850004a9680c80e1140c804c0c4044d54039140f19412041090305d000244a00003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 505224577 1250 505223327 505223353
    0x8070201020c09070f12050f01050d02150a05090f063612010c0906022109010302070602030a0f11180409080405120105090d210533030c010306031211 66
    0x41c51040740c403040850040310040710420380001b039140c1c1110880030f007000b003443e15410100700d509040c06014050b4030807403400011903c8000b0043d0364680e403c4d041c00e4540440301d100410560001000c0e90252a1110756480541402400e580c940000081da403c1416228580924203d04080d244403200404901d180c5071030300c0d030300360065410107140700204405404810143c8000641d600c00030841d030200c40924034004881410864406540c0e444a50b01c0320390781d00480c080d0080b4030001e00001d10010600808c6481c1e5071014500d922a02014082010a185d1621140c06160f80c9002c1d0038032040140600d034680f035404010114418440e180c00c1075101ea02003070f19140801c880c400386039075a409002c1d1601d010011103180824a02e040b4208110b1048030004c1588580c4021070951b85500100d41100c0700b50140b8444681e40300c01640041040000b000503940c036807000140a801005500402c9521a0255101390b9030484442492420030280c11a1207498100040b02079008961054400d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 505225827 1250 505224577 505224589
    0x9260111040803031b1b030304060b01020d05030a0f14130311030a0e0607050109141605150403031125030c0e0906011a070f0b07020f011406100c0b130308010e060d08070201020c 78
    0x1080c100b500441e164034161418402f1200381141c414150761010251043c1c195110085036440800c560300415100a070740d4400b4085c009203480c81d1600301018007008080103422600f42ea1083c02503941011600c8101070840d01d80c890229200001104031103401501d00703040005144491103403000151400d9180c5a040d00c1d00542c84082019801178003280d03040041600c4464094101120012180300606014004612989c44000e05004c1d03c5840700044030414404400c0100707080c0030a841489203000d0119a60b0790a01040398210000380e80032856245200104e841410320000a20b0141d0078182000d61156004640c1d5117a01420020f600c0000d0507010780c82c181500c02c05140b107160408000103400c0c4940c52050000a03071412032a05803904010b01295000341040c0c4401821018040c03085501603c07003400607008070750038030070302c8a026002c28180c10914000e983e98042a40c882c9022090070303505076501a48502002c4140d404220681c006140d02c5d0300c14011641c030504030300b0200741 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 505227077 1250 505225827 505225867
    0x3060403080f0c0f091318030906030f020c100e030f0f0a080108010b0306150a03082101060c0f08030a0f09050f0609030a02070b0a09260111040803031b 67
    0x2001524100030702482502c0800c0c500d4018610310000b80c103050002c000d10a56001d2444254130405002e2100e01d075459256120325040d4a50701000c1c4254015410054100c2129100c1c48001030f00e00f80c940540940c051098030131105102000e070228146404684000e8920403550310f005000400c02c076000e42d80c07614000d00031001a20021512114074030800380250030168001a156410400d40f07403401c0e074011610326800010010706080030644c41c40803c00c40d02d00340e080100241000166080c441c140c081c0040042d007030300000145580c0c0c907510115120800c9403801401f50958116103400912200041c540c840c9180600060660045604100740e500c0d5a41c1980c494000d004d104840c0d0358144052a4409500780c0154a44004e803140255111054402e10445074008900081028407a41c3c074007006000c1494280ca000b0b000c442c4036820900e00c4400e0380d807030750302c3c2c5010754482d00c0e031410075070703044580c1079014500319500e601d151140c0390107440e03101c05500c8003004601d112002c02e64040e2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 505228327 1250 505227077 505227083
    0x30213060b0406030b040f0209180408160f02040e031204171309020c010f020c070513020c070806100f030c0605180a060905090108060c0a14040504090809280504110702030604 77
    0x4620000704d0f00c02c6c0022603840842c1e10111500402102c080e0ba19691045000007240c0301050100355580e080040703c074003071840f248840c0707103091701c2c03990612030362550102c84240210703001c00240c41d81c000349554074400c540b80016800240000a80418a0242c040b8a20003010300d500b490074a161080b10300c491076a400c01000c159020400c0003102100b40f00da402800d04a03601103161103488200c0694030b2549204031441004035065080080304160141c94041c0c0c804000c40d206d068403080241d442d10021204e0114895007032400040c5140c501c03059201722500804a80c19150611400300c44692103000c00241102e103400c8455665158a88a4001000c0603601e00c2646418607081150000060f44075000c42c7d032110b414400086030a0f4129030900711103042840140c5040800219980603980c001030b4818a00304c00f2a05001c015001405040b1048417292400004110000901a090000343c0100311039601c0c1030100317041c90fa10941c001041e88004a00302505a03001030f00c2d19504540403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 505229577 1250 505228327 505228331
    0xc050705030d0324141e060706061503050609060405090f0d05041e03021507020d140616021506060a02070801020d0e28061d100509061807030213060b040603 69
    0x4440407078a2980b2564604c3c0014a07007940441c03a100d26038030640b010f0405240b03e52508141004510134034400041004c00107810b8688607482801e011008005620501c400040b8100c1e810010718841d202c1c16105401c02012180c07076440300b20901c0020034000300a804640704194400c03850100820405442c0070280e61003c1d96541811000a007802d0340c1c02040d92140d100190900c0141e6035040b1000781100c038066001d84600d502c0c000144001c10381c00303010b040d83c1000d584071641d80c5004035100c0e01c40c2481190b200701c40304c0c2d0001c00320ba842c0c0d040d0f107191103002c150602044007898007000501e1a40081c0c0704132038400e902c500c5118226407080604040041e9900c40d00c2c00d60380014058200f03c03081401c0003d5680148800c000510394020100400c0709944042c000e0400821030003a40e00c401541d01180c21080c03045a4200c000d000c2035034024642c0c410400000c03007010000400704100310401700681201880c503400d00190440048001049907180e140c007041003951340b8090302c0101015980 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 505230827 1250 505229577 505229591
    0x408090d0b180a0b1501050912010203043e0f04151802131401120906020304150c020c1302041203081e010b07030507150609060f0e1302010c050705030d03 68
    0xd10b81e500100c021541064200014800c0841c00350781030f036540503140e22100b0302c8070b402110040b5034610403108020341c81054010002a1440d056020314800c0c0d11a040300c0c070f8800034541d0807180410f81d0490358030f07802488041c084442d52030fa01e40103210f07480107803503030120954101c006400d450703210441001ca080801820801c00445c2005826080f2400300110721700032264000c001d18030703854010745070300e081c1e4001c840c14140d118004200c21401a5442001008920301c5c202001c1d500c00e84054512814041100020000620403604544960f800a12441c010320042c00300c2d01c0302c0308441c1e141c159402c3c040000c00b124190a00000e041c4070f550390000c24034090416076901840d0010007211841880010720004840008441030113401d4203280c0c0d1074044502d410020036560000802d02941081c200207034840180e0400c070243c440900c0c00e02d031010f0f190998120508021544800707010404c00f03c500141d4062540304034000e016806846410303444034042807a0994403902000000e039201a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 505232077 1250 505230827 505230841
    0xd0201141801080c130e040c08100b01030e0d020d0c03091d09100b010e010e030f01140108070519060507020a08030304030512010608090a02150c01090503041a040612050408090d0b 79
    0x4181c59000130404001800c040e14610000b640b82c50318040c0c0203400d6000004a404d005124807090b00808e020b80866204800448840018004405c4520b000c2070070840202c1e005003001c40d801c0480f060381d80c004c1c0310a1400001c21103541074110360607400c0c031241c0c010210714118044110406510213814070111820700341e131290700e09600710f0342c40d0148a28010000440340c0c0c0c440c0c0351112450013481c02d000c901000d10700103800e002c0a8042404c02d5031801e4400d4000650900c4480d0480351142d056402d0980d5490900c4007003156a400200c44880e8032109001c084d000343d0191190900141a0b66005929540e4180c071310713401a5001d43c0032401c003089000c3c44c0c0f40d207400c020f809040719142190450501d001400e585c0c160032a0000c0c40b81d88035002a552600c601c400b03030f61411020710f00901101215040568507540300d40104403034107800c0c00000c00740d2017018003201c040300d107907541c0c1503030002da10440c410040001800c1100c25000c04c1140c4201a41e9840c1c1c2d5032012401f0701c11100260601c80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 505233327 1250 505232077 505232087
    0x306040603050307122601030b04021309050a11030321100f030615050a140108070e040c11120903030d0c0509061c050603010e34080d0f0302090604050d0201141801 72
    0x2088004003080403034000741e18094030b6005411250700565141c212b480b00e2000480058440c150710800c1c03454100740100b0b002001440c407030800c1c02000a0040c145002c000c4c5a01c82c4905203182c0051101b100080041e90859600c040c0d12203100c10040c440d01d500da80004181c440c945c1d006450307298458081603214600149514001c00044584900d490300d441c2c2456403246901c0089414401408000b5469130f001ea03d01c0003d03454000c03c104100144c140001e82200010b01624000e0302c69a501d01119031126004c45290700c0c00140214102074181009202a00c1c1000c002c03420400c09210140e0151200b1000c1c10044903d029101d0202c140c0010744002c41d08000d040301d01c02e80c1001e1a03a1001040403076400c0d0014400802298111003683d0079103400008a07890302c0300000c0c904000a0942d0003c50555441083d40c1d560200043e1004401c4099000d071301c2d9031a51200b8204030400c1a4603282070080100c51042c1010051030161804050a90b08041003403409942c3c0d05030380e0790f0306603409 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 505234577 1250 505233327 505233347
    0xd110c010b030d0f0e0112020c0f10231e0109020702040e07050f1318120f11060a1e060602010e16210816030207150e090c030604060305030712 63
    0x1c0d4003c3c40d0300c40e4000401481300418a003840148070b001c4400c105c56074071483c0941290404580c09654888121081c56524104042508028014981d600714005100c0c014181d061162071400100904294482211000c004d0885004900000030f405848002c443d81180201014000180c4a00743c41c014001034444001501c5095040500140041c1c0c0d10303004000760070b10f425102079840010010921000301303401142404a1400b4001c641c0800842200030900900305507210705810b90000010b4a090075a401c171482e181e00084002050280180d1240c0700080506440001304003010130308008403007441e0071190050351183c0c640003190404115480801141e00942421146400340c18209450280d6400c204103030b9000303c080600c4444415942c20f003640811078030b9107901501d030280d0354215a1003a880b904013030711001200603005494041c0e105001825a001caa9904100f0039840c2c1d10080800303a000b0394842010000c58410809002c02038410000f0b50301e40656800098070b14444 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 505235827 1250 505234577 505234579
    0x30b011215171501090507090504180c08072d0306091101020f0706050304061a030613020906100206062b0305030a0f0207020105123403050601050327030d110c010b 72
    0x200e074012064040c00b800403d4110790032008006031944510404880c001c540e0362003107500c0303401c2500340d035141c1d21241003100000740b080d4484100d86540303290b050f4a13160140b01e00521b8113280401c242c0d10702c2e01140071941d030210544160000035180e0f603880d8215000b27103d0949040c110082c1c0c80500e5601000150540500134009044c0280361050062030741c8001403004200c01d40b20b0402811400010001c0401020000e064480616124100c030340c40d25400c110591185d00c0341400303c5c81604002c0c0745081c03d840c80750b0123400c0a603030f60002d100b2050070f082003181800000080c41e1240800040e213211280e48170f03564441c0e0701e003042c90105040da81c41d410045405031040241c10b00503a0010700322002d00304818400c0ca0266242c90340c003d1899440c0a400300801c030940c5040c0b03400d20315040d110f0711061560300d04118988401004403800c0c04101d40380c44810b5030a031410034404280070381c220f40261000007200e00c0d0110002550007514011070000312031100125003840080c500303015182e00d03000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 505237077 1250 505235827 505235833
    0x240501090936020301240b09061e03070212092d130c1706300102071103100606051c0605060f0a09080f1506060c0715170108030a030b01121517 63
    0x2101d030450340e113503c400784a81e0221040000711141035845042c00e682ca0300b511180d001d922002b25010340b000d1984100c880400500501c40c0b00000d00e10885c0545080000113001440d00c0c1c20903020058224040880112075500003d280380419500c2e8030640c400880154000b003042c0c41c01c0364000d060a0803982a08007007142201c07c001c4241c507010f0801d203517214003501c0b2a0391000c074540072065440c0810848080c0d07500028401e0148440842e0200101c0300c00d40446050118082140c000c44ad154052200041c00400c21000c00d82400243d100d40107900b0440000c0c11582d40b4001001a0701040d0003a4510001142684016406c43c502900038141c0801900b0390400880e485501d62800072035584050040b00c0118070140c40703800544250301d1041c0d00706c03840e9640392210700c03540200c40106600001d41074080e10b6a012082c190345812034161380011410130101c1042600130340f1036401c103c0e041004000c90a10016000c2c081c2944c44c04c0e146a112000b50304184c01142d003a0211a40191154 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 505238327 1250 505237077 505237121
    0x3031606020a110a21120c0509130b01140f2208060601050c0a020d0c05032b021603020d060b0d08030603010605041404020111120706240501090936020301 68
    0x1604072843c8101000b03400000004540100e881179030382d200e064104000c11440c07d40c05610075034002006120680301250b195401000102e000405d48000003031080c001501e144a0043c2c4c281e121380504101d800b010304460421b2040c001c00c2315410181c55407080e0303803d5403401c10041c14030140241c541212083c600381d4a070062000c01c0c9561210001d5009004004c07a01591090103040341a150203401c0082c207450380142010805911080042c03100800c0c540c030362801740d444070300010b0507a107803005114070b006290340b0f59001c0154102c0e4540042c0c0702c0341d45411189079107030b80700b120a941d62403003150380c2602d03420003205040c01c503a00c0360405401b43d40303000d4040189000d480c20903544a13609185c9800e5584038a40401d0a0000082101c00b10b60f0000c908003041020503003100004950740c41c90900d02c000b104042c0300c81100c1b14400c190102d40c40400c20300100a4a4010141c0d81d1081071f07020034141c0b008410982802d1542d40f102c80c1c0301c0391401801c0114602806211442844603112009036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 505239577 1250 505238327 505238333
    0xb1503060108070e060f0c16051c1407120c150309020603060d0203010f0f020405010e0603010b040b0f091c060b0d02030c0d11061602090a0905190203031606020a110a 73
    0x462014010206204244d0301d078402980e10901100d442e003500c0002141c0310f2541c0320459564070a600340694100c44c16600216003400c043e411002c030750b0300b402c08a1160912544a07500015006040410303540920354000c10950400701081d062541700d64040502185050203200b0b02d6980e01100100b01820485c007400560741d48000d0b01d400440031541111079003103e00c006401000f2202c05ca03164141886907107688503040b640a001151801e0725060030307600000b4108405840300b4020b81d00c1071402030105018070940240581101d808403803026140180e43c0d0001080910071a00090301050200501010080356024000004000b9a02e5000380e4800c1d500203a120102110458010300c4035800c1300c010310400650b4080d880001a28590762030f180313100c0e60560360460b11016401080350802003605001c0c10301c6810030b40381d008400b610000003141c51450340d1000b0034609a074944000e01001055980700d48458038002d10034507006a0359103603084040c0207425818280c09186e00151041d0000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 505240827 1250 505239577 505239587
    0xc0d02010e030a050703030908010c05030c0f092e09080307020109030212150108010c08180304031709030d020106090608030702300303011203140921010608100b15030601 75
    0x11960908114200c40e07a03190220b031808803581e2000d030082c80340d0b210020a00d9000010f41e010707551120000d00c200d500e0407070280c5a511041d00c00c0d139508001000740e80c3c1c014887c00301030003c0081c018800e6881d0110f020052000e0404241c04289665045c000016055003100c0c40030000c0500401541c1861815000030b840301019101c0603018245003418210440d40601c048942045e080340c0000c3d05584803081c0300d00030041c000c0d807140410040400306001c41510300f20751507010700c2d540085180500759a144413240030030012182c440413041c00300401981d024460507102c0e40c403940c0000742c5039140074546420b0b10b0880e4403601c551f402c1002001d015840c2c20a030300c80c48031140c107600c00f00340214034409185c0a107207460080c898007001c400070038040940c1107a001c105004c0c1c1d541280301d41655802604c00e12601508503444124840314910881c01701d249100c15909070300c00010f030565147d19250900000e10301030245a0303076a10084006141c00128140e00145100c0e035681035240820010b81 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 505242077 1250 505240827 505240849
    0xd1401060225090e010e0c060304020a15050d02030705030708060a15141e0c330403170a0b190305060c030903040f12060e011e180c080d09080c 63
    0x1071030b401e410b8007004090a4141807030009108010042041d00a081030260080c440e070002da401078000c00280c10824600081500d002c0c0b50000d101113581d6240c00d202150302d45c82d840d600001d100090090380854840b62000c7c0d442034019499031a901d25140310001e2070034030014051885289640c0051110411351982260304044509140034142040386a02c0c201c0d0080521000040c0c14504d0001c0c940341c2100c000d04442680103080313030070034003030310011410f1702281c0d40c1107041010304446040264000032181e2030304503000342003d00d07020003800607420b0b0858045429581c4030362500c0b2820707154144012903851100075454a482c506003591f070381c00c3c0c44820290215888980110100d08441d90610841d4003c0058401c08100241e4644010041001140c825180d0625050b030641d04c808040c05103031010010020031700b200301160300c0300c40010414000c0100445242c000c1c6c91000484201c8004050a68480240703140c03a42d2034130003486a5500c0d0000c01d159084403121822948070307002204 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 505243327 1250 505242077 505242103
    0x9080714090906010b030703200c03040608073f05010905190207080702012d02010507120b090c03070509040e0c0948030a0921020a140a1203020d14010602 68
    0x21070241c02110272001041ca403040e80c50002c00c0000b40007007107420000010000c0f9001600e401e00695140b581c1174a09010004141520780c161081c0000503403401c640c1c0c5603110303034101540c1c0380d83c0020000c91320855600340c2003615504c0d520424804480c0c01041003c01d0354210080661400d03036036582d0f61080307014200c4028144006460050b0028061307514041066120400d05540d805220400034040c0c030b000d41e40140805c0b403103030a03410f480c0d04500070854580000f814090940d25180c26040c100d90004200c04e041040c1403164017125990b9000d00c02250070500c1c0188151fa1080e070400580400181c02d4410b01d61050040740200d90070542d4240704075601c2e00d002180c00c01140d64480d0034801c1c024008104040000400510242503440000b0707040c0aa0010010b0105a809110f0f8408200c100880540c0c0040c03030380c20004954144c0c024541d0b80410685013444059910f02843c0d220340c0a200f408079130040744a001c0345507144101010080e900303890b501c481d4500040a5240c0003001d50807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 505244577 1250 505243327 505243331
    0xc180506130e0c1e130f05030a112206151110050c070f050d0207090626070806090a0605160e0609040e0613020a080706140a09080714090906010b030703 67
    0xa943d003081c81044c0e4529074003d251402c1c2c81201003282030403d038020100d101c4543d10032940410b517810300e01e40341001d940d006001440303d0803503911a034510502590711070340c1c000d83c030280e84240850135100020701200c1c0c500001ca02035041245050b40c100c0c121040e4400c0048604560001e4800059800c1c100b062144001031075486010420401e403107a6500a44081d81c3c00b9000c10422900080c1501558400d5080e2581652917091181c1134940a204072040c1903800c428202c041ca110488020b012517425003199038103603507103042c0d0b810040c00b21292002c81d00950700d268203100d1240170b40707540004a0095407050401c40240608804012451a0f000368008500b810403a2243d90000e40a44070000c02c85180c0e01d441848862024481401280100054240010b0f026400111002500c1c036644038402c1d90800806085c0c4542c0102c600c1c017040101c2c4000000b1508070500c030810290255500701840d016601007400100c0381c1c040c05004c5c0f590701c41c0004106a1094106907900500d15281c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 505245827 1250 505244577 505244581
    0x702030a0c030c0f200933040e01051f060f03020307170a051906030b0c07170a020604020a081506060309030904060905070e010903050d0315090c180506130e 69
    0x4103c4003c01d00510080c000c0c18244a050f0500c10102c00c2200b0b552800f018541800c550f403c203006481d80165110844514625000c081d81074031000d405540c020b12448940c405000800002c0503500080d4103101e181c4d40d0340043c4906e00c00254081d100604070800042c01c00c40c5030203002020b14403200500400c05d40e0100100e00e91611908a1082c2c840c203203420300c4401d00300130040100402d8181e400c04408081280130919104240c0100b204a80e000b8030301c01903564525001541d130383e01c000c0c0204c464003152040c5180203848480581709115096000b40354a140c58414843c0044850b00541110703444240301e1201004802c1466500c624103403141c90710b030341b2100b0181d861400344010840e40142061400310302c1a410380e11040c8160100c0c0c0d04d980c07402400d0b400548002d00a408050456049036299041060181c0c10440c0341e46d202707030090400b203a03880c11968200e804510061000402c80020304840b082010360950103000210744162410840f403010401c032440781d200c4c0da5010300480340 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 505247077 1250 505245827 505245833
    0x6090f06030f09050d020c36040807020d060504020f040204080d0f03020d020a030f0b2707050d05090c040501062c040603020a0f0f0602012003060a051c050f03030702030a0c 76
    0x10180f01c90741d00004407540741c50720b180702944800491144c070f0f004045030b40444100200c0701103904062103090b030400100d0004401c0043c4400c034010403c2d140004200280e0700140c4425001000650103440009001c0c1481d01c100038050070403038440e07440b40d40180028012107501103421140c50400781040c804040301d1a90540c040d004000151034941e10119450401d5030f095001881210b0710f80c82e08105480030b070020898001c80d43c92504076022080c10110ba280c100c0c0c4406645c10004034101242098085d184000645004403881400d54002c08445e2051342880d001d12070162140d401c003d918503c003031046441d035641c05500c40085001c0c120704010241c4a540c841c0c406190050590b0044d0340d01c41c454440d00c03403a180311341c0c0e01e002e01684000500c544103124031081144d070201404508c100d1001407480d560005081d1076031254210a00040c15510200021040c0701c00008400441c0410300b00309003000c2c1e00f0144150743d40c200304200090542e020040b120300c41034071304003c89044144d003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 505248327 1250 505247077 505247081
    0x1170312012c15030105010510022d01020403030c0201171501120f050a050103051c08363009010c031202030901020909130b010b1c020d0b0a06090f06030f 68
    0x309981000d0b06020b080c05070301840e50400000c4480b042d002406140d9858050001c1e00c1104841c02006800032070081100b031600c1e10000d00d84c6aa864800c08508004801030307801c9074099801103000c681c01c003240f00119600031520121081d07509400f4035503132400081d1703040d040c80a20f0311a030400000040015207100690b101502401400004000c1303031401d500c3c0d010081c4420f001c1035555108400c2c50412044c0410041c0c18010510b070f031103801300d44407450340d01608244440742d05170015581640081c2c1c40c50000e1980c00841190000742110b080140700721021610301d440f080f149c00030045c100c20030302c04a201280c2c4649130030701e03124280c80300a040490702d0f01d0100c2e00e10f01d459800082409040380054001c3d01d0000c0084030f158640340c0718075500f0401b15480304401031807200107500402c4000d0854019040c22034940041c5020100d010061400305c0e88807030f81400d00b255944d21900340c207040285041015240c0c904143c1c51072820501d40304468020380c801d0408054442503101e0b00c04c00030b5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 505249577 1250 505248327 505248389
    0x30415032307030507110f06041a07020d03090c09020d050402040609150b0702041508060604112a030f0409050f060319111f36030305070203071703030117031201 71
    0x1d01f515038031803280c0b10301515004190b46c107440c0240c800300d2041c01c10042c8409580500f4280c0c0040116101024080d0050520100292410ba40d40c29001600b039070140010038180505140005040c54607204200845001c0e400c41d040c101c1c500b860701075030707504154400801d84d014811055204c0041d440014081c010301d21841e00d5110480304005400800080e0190158800300c07414452020a03680c0001d00b4020b038151100c4401011807045050440c0c0750300400b841001c40c0542e40703000060060208583c2c0580d00403201d90f90b5800070070141c5250003190350381242c001ca024102d103483c031101c02e0411001e80200a0034084d5045010140c1e80c1e0f03075a541100d080a0a0010038084404010260250285282e00e80f04142c0001d910030035203403541146803020030f00d00c0781c1c08201d50964404840c50340203688202d8140c400d8000c04200852803194000c00c1210080c0215901e604001440101103011041040c1d142c1c014090294003c1e0090138150541d91002e103174145581a41000218917151 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 505250827 1250 505249577 505249607
    0x9150305031c0c0507021c0c031e05010b030601030210050c1504060b09070306060516080c010e0304150f1d01020a061506030b0a0b071112030415032307030507 70
    0xb41881c598a03404100581d0300c001c40c0c01c01c01030340d10301c0c0754141d0302803003a00320003507005403d001d11450b0b800900d030403500e0035409642040139042d00d03960b03094042c40709413400c1c030081c0c2e204103104402c1003006d015200704620181d01420b115455507012440d4006d02202d60342c203008010035600c0d44107404104190528200700454400e0741810304100009208600b4414080c14845001903c458020f009007070840700340e0769646142503030178051203840300307003180c1d04a4034000d0030050b0644070242400f90345c0c1144800c1c0051692145404400849121144418001d0210101040c40900d400001401e5010011281c050080904400403420000340701e600a010390b1805d016441c0c0816424040b030140e410644003000214a000700f040341e84d034040d10501c0e510b507404004c403500103507103032032124091341014140d031919050b40d0a1803800c5400c00d401c01d0324900864a581d40f9460b1780340c0984c43c040200036401c030201c400c45240c0808100001030150741415101c50201d105188160a40c1034040d030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 505252077 1250 505250827 505250833
    0x11031314010615110118080c2401050301050718060e0103090b0a1d010b090604180c061e0f05120405210904060602030f03180c0402070501051f0b0409150305 69
    0xd01d03850b180d00402104120b203c000b80381d00380d10103035130b040500c208003207030249108035001d40500380d45070011540f22107501c80d203d000341c1c505e00740002079800c600005540092810280381d810034050608590005009808200100c3e071040122003004951809071800c0313161014030405201c0042e0050440824000e045a12490402c0180703403031a0301000c40f1800c403800705484100c00c440d840d800c0c0c9030003680c241e505c6a591000302e8031a20f8142c1c0b01c0b0000700e032001c0304420341040c192104031500450740c7c440808074402012482d024280c1400714400008141406210075a1443c400bd10b24042c002c07400d988030890302e020800f801020000502a02a60b1403d0003401ca960920a51950440c06a0034096400c0c00b00102e0510b0010040c0d900080013030160505650b1034100d035946007582100302d8502ca000c4c0c880d00029030707101c42c0000c02c012030080001080703d09116601d0350354203c07008001c00740351034448014460031340a1000c490488003c4200400c0c0d03000058070040c0d1406490380001e0080c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 505253327 1250 505252077 505252079
    0x30c15020a180605121e01080607020c1509041a03070b12161707030b1507031e020736060e0c030115030c0203090a06031b03110313140106 61
    0x159550000c0c02041c4460303035800c2020100200020301080d00c2d00030b150108509000c9501d141100410490f8852182d6070103525140030218407076a41d0400b80c1111007030360080c6080140e42e0740c0410006003682e0040e0307001802c0240309049003465000e103d04480c8103980b00d030383c0a4003100302ca1000c403100c1000101640c034899560a0115060f501003031704a40c800030036200044c030399590503501b80c064008a03101c48640c1001244079501c0d84200402003418150b4802c0e4084058841c1d01a50b4820b00b654005103546402a080180070031000c0c442a03889074080e0510006401c1d8049011310440c2d40c3c05000000260141c001c032083d2458001c030781803014034a044454130920711a00550201c2d03444080703a211030f03210103d56000300d01c001d000e4080c02a541108641c00540700f907000140c407407942d2054030309026004d00090380c444226070103180004e44a120070f2900d80c071008170b204003103c42c40c18100002c90840c4200101c50200a2007006165515540807090082c65034074507112040e2240200205 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 505254577 1250 505253327 505253363
    0x80703081305120c01061a1e0f0a05040f08031809070e061314090c09011202120f04030e0d0b060f0303120c030a0606140306040b010912050309040f0b100c030c 70
    0x15811204083e07800d50b003000e00010380f0917110141866415881e449041c9440e407056918045403501618001b80040104109c080322030f4a4070240200000a40c0c58541c1d41d0314007080708040d40c14541044299420406c0403003801c850000e507142c030300710302a80d12100390340d102417081c1c60f40d00c84e0f12140e40c0c003c4000958410622030b001605810344140300340000040700304806120b40604210b800b0507841c034003000044015801050140614079006038054540340e5081c0100d40c0802054038542c1c0388851000901c0f04158009403c141c20301c40a6621024416144e11040c0101e00040d04450207203410040c0381060391004e10884816110000c01c142450400d0600700090340c1c0104c43c080030300e501e03251001c03805901c02c9280b0002178107415070107820750300d810040100030f1100c001951306001c1c0681000414604070309a094525016001440d250341102c0140420398005c000800c25039464806208510360303c05031f07003180c401c81d17502e002e401541980c40d0581d00c0825141020700300003145030700f440c08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 505255827 1250 505254577 505254613
    0x71b020f060412060c1806050c070f12110402030c0d02090a050402030c0c0c030309150d20040303021b0a03030c080f0328090302120a03021b2107080703081305 70
    0xc542c401c134010804400220700464248914000303995015000b000100000391044c070242000e0001e900070707124010b030350f190f40712005107140e802040003041101819080c010304003050014010300343c605502c0c61600055403d01817003407524844446078049042151f6480354880315010b0a4090021543c0e41440c1042040b40c1c0c1150f144007074140b082070384121740f0781000700980d4071350352001d080550050180b00fa038814a0300040d8500e800d1503a00d01c41c0e0513088072103d0000110155661400f6a1141507080007800d000a51108c02011000b80f40c2c40140394a40102550880e5014682007101c1034003490140014800c811846044400100500c10f01c118850070181d40c0040d40c04041c2c8031111403581000940f003030b41c01301a015811020710f9281100740300c1c009002e00c203907500d4014684400c0c00140800050b91003165600d982c40310311400d00d081c82810040a000360100b103141c2c02c000c05959042d806d8801c50000904002086010800c001c00d0025000031090b4044150761801348102c4801076 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 505257077 1250 505255827 505255859
    0x4030f080c0a120e0a3804020904030c15020c010f0b0d06050903040f090b010e0906030d0f11160503061f1203091203020c03011b170414120301050414071b020f0604 72
    0x95099201b041c0301d0200c3c4007032402c0c0d1124003c40c03014007866602c51b020482c1c20b41000380150140106440c1c480c00290081c550b28200801e80c0e140127807070783c1c100e480250071100803a440040c41450003044c00403076626652212106036202d034003c1070640e80c00c21807c0c214012a0302000b2101d000d04000300340e0105640052142d500282d17a03075880c409400080014400081d030f006a0140c00c000c080c030402c44e110783d89c1000c9046007824409e90350f80b00a4441417a1588070b1400100f82c0008040c240013030b1a00307001468001c490b100c0d404001c0c1d4561104800c62100f6482002444030810a00c3c100f018011054280102904c00c00d82c1c0010705242030203910b032a14203032194480e500e400c41c5c400c1c5d80900a02001c030310f0383c019a03a1240180c880003140c41405030181055940181c82e107a580c1d0207150070449014202d150f511440e4aa5243c081400151245990040070f654124ae04000b190b540c060a0707110300d615107848010100010f4008102a262031420307480d04482c0000c0c0124040c000d4400c540c1c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 505258327 1250 505257077 505257113
    0x6020405010f08010608151203070501020d05060a060909020d0f1a030c150d050901090501020a0c050f0d21060503190c050418020613051804030f080c0a120e0a 70
    0x440108030300108440c3c0e0042405404045418540800c6c0c02d0802e080400340750320000b42000c06a03881d8552420310310f41000800310341d56900040c484540c1c80050041c160060410f031342c40000c00f800c00c000500607580e1030040c401702c143d0104214004d0921034000f6041e1403070041f0204120300c04200c0c0583e01d5001039580303901903c41e02954005a00317000d00085c1016031187d8546d1300b4021002c03210400f0b01030281c001c0c00e00791b4803051508089030081c4028010400a5107411309002441d2900705d040c0000083c1c000d2840d0051542d411050340c20149509030043c2c0c20900c58060210a001c000040030079801c0150180700340341c206075031090f20320b45051903140101a1001d029540f04100f2059038962342014802035480303a108001410010041c040c00c9400d5011220526200d5001c21010360400750000d04003c80d801c01c0c8400c1c140c10003098000841c242c030740701c0c9282c03401c071044076414440c03105101c0422519000400d680c1080e5800040c0721131500083d2541070302c1500f405648918402c03085 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 505259577 1250 505258327 505258337
    0x304052103040302010b1504060e010309080f0901080c0304030e0906181501030e12070609020d060504060f0518071503060b16021809070b0f09060a02010e01060603092604050a030602040501 83
    0x111100e00d490703241010380da47c180e045d09152504005003190448801c3e03030480c0c107254403600d40000242d052005040000c050300041e0340c0702c0e901400014680080030700140c40c1c1b20020810701000c2a481980c080940070140c500840300e41740c140c007007840e158039201c02d84100741040b018000500843c203a400040c420903a424400c90705882400e6481d500c62112200c100380040140000240700b03078100b030240710b00003406610741006a03160b10007a900d0032202241c40076500c40c001c5a19550318850355800c5600540300308042080c03040320641c1c84010307003d44a91001803142d1400040d03c00c1d00418054816600007075214a40014007003500540850304074420340f5a001e902402d40444000e407807080c20040300400880b89842100c402552045850918012003002a030314143c4a060090a5001c2e1b103034000100e86203110512800c40b51581c010104142c00c0c0413424001c50008220000c13001d803025030100580301d485089425030300c1554061900800708100000c14406141d0240003158000e81724 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 505260827 1250 505259577 505259591
    0x510080a0501050a05090f06040219091809051b130914060c0c06070c03182606060609010e0a05030703030c120302090a090c090503013b12030405210304030201 70
    0x20488014130a000d40d03a0072100020005602903800c2003000e410074805080145803071008200248601040c071082004500c4c0107100304078840d10201d00980c00f10564038100201c441d540d550540b21007660f40d083e911084407c400c2e031601c1d0340d0004409180070b441c1000304200400343ca4520721465045449a80c58069500090410200b60701112001c107005406004940d50341041a00d007181d91180580030040001e6003072036a440c2d03814200c80600360041c80040b03c048160420110b46801040608490f0030410500c000c5841e003005840459409090201040070003002040280e40c960340080c0c0c0c903110b9103400005054000030800400e90241524070071010244200381c059201305400c05400c2109200c04020050442d40f01ca100300c050303880c013458800d0761840000d080d90910205009003442400c042c01c1324039007070010b842c402a4040110b00400c40d244414545400100c00a110700d03120010004040045c2401102c50811203024591130380e4000014420342d5410484003100990305c1c1c029 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 505262077 1250 505260827 505260829
    0x405010f12062705011a2d0607031e030903020316030c080a23040f0311040f0e010507090515030a0207050f0a0803061314040303020c01020c01020c101103100510090510080a050105 79
    0xe81b21200a003d00304001c44005002100101c450200905507115120140e0b08156030b28203004006087c0242d40d203202007032170324420003842e41e2025100014503191900050010750044140c911144c0c04a034140f403a4001400c0070303140c0c041941001426000005019100e494210450700444000d40c0605110140310703644800f2a481903025a401c00d019200003000000d0b00d450103030f407440f14050030124500312402e81403c03c1e02c440390382101c03c2e079443c0c00801205660222001c4014a02120140543c1202282d10b08180c84060710300c03601c0c927400003901030500c02d081000503814000072044170120282810018a42e0b0401d4940c0c601c240402c04642d8128000c40c000c0c9110b0100300341d6112010307243c0e90340907002903000c400d0307004582d5001d1142008000007840980324a40e801002f0380744858280c0108401c41d05440100710749803401340180030b036428401a080098500a651001c4030401c481403e03075a0721a02d500c00c50f0700803016481b25000603403025400b8051454100f0601c550b0340c84030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 505263327 1250 505262077 505262111
    0xf1b011a0108040c0302091302061305011112160302011e020702010e06181e0d15051806010b0906040f06030b030706141c150f03050c0405010f1206270501 68
    0xd10f01600711941e441c000c0c800f601d000c02c4070540082c0d000a8803944200903034041216a04404031039440360707081d2a0100000e507000392010304800708541c040c0040c1c0d110302e0448a400c0c0200c0e2280c0e052031260301b100108050003540508d50b01110020300d40541c40c00011454080c1d40440d400301e00050306003000400905200013035035403492201c07410b40c81d032904500600004007070600c098440c07800072000340b403003540310000c00b0504140104980314506200010b007000b0b6a20142408104d04012003200e4250b02c00801c01c43d055800302004103035500344410006185000d40c0e0041081380503a40b034002040da41640c0400040c403800d134103440e180355a9510030386000080748a4540b020804010b05030b2040c94121880d0f132105411100001e0b505008002c0407403a080580090845c0141c0000520900404005801e008401106c090100c0d40c10a150321074566024403401f0400c841e4004140c0400041d9040710b075405e030840f0010010f1b4000e400010440218541d01a2421b510740b03a000c5100500c81 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 505264577 1250 505263327 505263331
    0x12040f0906180c18060306091107020f1005042103020c0301090510110708030412081b04031401021204060c03061202090609060a03050d031a03031e0f1b011a0108 71
    0x240c0e82c2e81207040c54254007101808000e001c2504001508181020401c04e00b208078024100c2950000340050601d00c50004541100c05081c06140041c01040c00590b07415410000d0a5015101c0e180865803580701910fa9000750f422030200050300c2e409544910200303d02e0110701d98040d40c00c4401c100a404140743c01c0ba0010038010f00345130071081e540c140000d50798014000740340c0551030003403615001342c4424243d40c0050b40d00725000c00d030440f405480c85510a0000f50440541e23880300c1e0352034103c03803587d0359180304610000348007510000e041e00c80b1030f0303080d0305450054030344030002ca15030b152034a0030200900143e800703280408e1a0041c0891541c0c05680e240c1c44082d80034080c2008e40e00c0b030310208800103034028492a40000c00d4103001c00020418491030740381000c507440125851514200c4d0154802030504018040d61003405031640d02070380c200700c000c20420800201d41c0d03036003031503800d124940c41001480b00c090000f40103200e44500c0154400509528468008400a80000e004490494007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 505265827 1250 505264577 505264589
    0x4151704050c120708070305010212010e010b070312091407060906020f0606240f070611090d1b17030339030a1d1b0f2d0312040f0906 59
    0x6540c2c441e00d4140100200c1e08000120221440140d8600300145056101e410442c0d80c2d9401041c0061070001003004540036101c50075a01d41c03558140309014280d401442005170421810325140000c0242c0ca034000c4140e140c010407030020480c1c810b4000c540d1088948140c00000f00b07034035000100644042b4240010b10072400180c241501c0e01010445801d0b005007018550305818441d080040c61907800808149030b0001074680c641c1940d05000f402c070b07503043d011002d40500c00c2004507469170341d0081c814182d543c4461170a036a400340c41c403008803017401500405101c1c007441c110003440140c004007440c40b81060346640a071040c0c8011031101c04040340101301e40c00f64042da812070301442d44d40001d580e005d8129440040e0030000740328014a264a6807078190b1a90b005010b1115403c01442070f50b00d0b00040c2035880c1c007201550352000ca0380000490341004540200210380700400340504410982104004045541020a88468100d85c1d4800d00c10381f0a0000721070000103401403540680340407541 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 505267077 1250 505265827 505265833
    0x30c07110609030c0f040e16030c1215020313171b0c060f18030111070302060a050c031f05040f0b030f0f0d1d040903110d091203051c020415170405 65
    0x3a601c144100512411401740d4401d407203c1c0071101c0340c0e80c10018070686150255440c600103142d030410000580b040c2d080100c2403c108401d17600030488087e640310030342c241000c006a680d40c442442c070348842d025840c024200d17440f000001005401000c00b0f443c8418000b01c4903481c4814107100d0aa4440d81c0d01001e80c0c0201d8203008002e036410605c1c000d13000081c14403246443d01054600003908580203002c0c184121100410080145941040740c0e984c80380d0410000c0041741407880c082441030100501103802050b002c054086a070a5120b0700c18024070002d0000d001500c1c240080c0c3d40a0142d240300f0724000e01c00d88582c40f04013400000d440481003e99001703010105011003040f9100c180c0424003110401c1a0010200aa1120311644180328081e5440c2d80b07403014406440b90411b0410b000b503404001e50254180f21602d0768000f82c0030310030392605185a03a8541140c4a6860010744030803045004d2010500241e920341240c5501c1201005607112540b052490102000400040e140504070364 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 505268327 1250 505267077 505267093
    0x19061208070219181b020703080d0b19030614010b07120327030f0518060c0705090411010206070f0f0c141b0a05011103070f06060506030c0711060903 66
    0x103424000240405030002c1c0c55581d0400c0c2c0c2d80c5514041c1c0340350ba03000f40b040407071210b4402030740080340c45170b102010f4107190920b81c000b6801c0310085d9a080c1e03034040900b412500041c5c2c080009000c1d404240207000140103910780320740c400eaa0b40d104a1403131005544003814003140b101003250900110b4140c40c02016a2410f2181940712000311024401520303051591340c50304030907150b80446910460800051458100c03581506c0c008101c492200890814020b06010380e000c0c1c03240d886035a90380150f01380c594544030690f0f84a081e2030144039902c4150044a4501480148860146802c0d4410001e8003210300c0380e00e64a200300e601d008007000c800001400d0000d103808241c4140c603203090143c0038920b0300c0046442c891006041586200d060402550700303c0509042d4103150101c0c00040000b420700204910014080d15124418400000c000301d91103c05542044070980c0894054280030b003100f070303c80c6000c2c5468042c1e0303444a0810303245100c400400f56500d1601108032082901c0113000b0344405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 505269577 1250 505268327 505268333
    0x50c030304140307081206010207051c062708040305061b19020a06110a03060b0a08180a170a081f12020d06020a0306180507090b0c160806190612 64
    0x941450180001c5800f0070443c07100070811100240c03440f5400c00c91000c1d1281401310005e8a88051548000c0c003c00004c410701508400c124818030586810541c0401d4203011003404600702d17058250f0328201c003201206024240300285003c5d100342c070b00c1002110603a440b0546a80c1a01c014803840c07441c0d0440030404e840003681c041103040c460891500440d550310b0815a00d50341030b10700c41d00040c0160400030500d0407070a0340c1030055800800d607141901e4904286003600414081c0c0007480020706101d2400142c407030344410044d50696942058204c07050518205000100d948483c00d0710001590907000f041c041926041c4886980c0c070a103694840851803c030703000c1400c540145090341d1020410f01e070200850391078002411013074503a94000070014284911114150b506020800314285070200b0400039276048550182560380d259205a190003410442515000412819a000c0c11481d030340040c00600010f24203000e540740e080031a0400183c000b418080b1011841920383d050140d80c0130b0004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 505270827 1250 505269577 505269593
    0x12030f110c040c020c1e04060614120717130c06080603150703090609060501090e0d08071808160801060b0a02100203100e0f160801030b0f06030102042112050c030304 73
    0x10f0100e5900540c3c2441e1000d60000c0e0700c0c481c0c0384615400708011604420031914040c8100c002802160030042c90100c5000e511403018042d000007540139504c80d03000300e9040c0f409071110041900c04070200160500e407400d00703041300110305c0c00c08840341c41d4070f2800860698043c030141c070300c00c0070041d00030700d0714400ac2000610706840140081092654030030940b404900103005811606020307420201d06949003140e03100482d403015900c1d18080d00301c0e07500076054a52140c80759401c0025450300007a4442c0c800d80c4d04620300c3c5580d0006020340f04007100225000d2101450004960200000b0008142c0c0e80d84c1321005072142c0b440032070058104540c44002c50425a000d580c010f00c003000f60b02c00c9140c860b000d40101d880c042e04d81500000d0303140d0810070030080c00c8241701d00e03143c864544603180e03500d10742c2e440980c45000b5104551401045e000168181c6096054400400031300d003550803480340c10395810420501c410004e461036041030340100c99860080f0100c55400141900a61844d6500c2c0c48120b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 505272077 1250 505270827 505270841
    0xc02011b0b070f20070806010801020301060804060504060612050d032f0d061a030901050106050708070f1502131d0411060c070806041505180607120209090112030f110c04 75
    0x144141098214154211200b200982d03500030130041041d94208616075240503c144d001448680c0100018040c0c241c1c000303402500a503200501188940722450624054405504000c0500400840038000c0c04000641d60300611a02d0b2000c00842303440060181c0781e09070b54152401103002d0301c50009070205e583d0005207800d0314030140c0054a19103a5040c10694894400341c1c0c440b06002006200075034a00303220b406c0c01010382d810002c0c40c0c0b641541d140d041342d0143d6034000c1c0424003041e4642041c440342100700c030307000f00420310110340e00e1207140e005803044040390145441070251103001c1c014083c0d035050010b02840d0041394644c5251240e40400c170056105004540d99030080640015194408000f498021032003408068110a103160307001c811541c0052004840c0c6080301d8014800e580081800754203c80e06107885100402e80000c0d0201030711906040681005035900001a040080801c4804a900c01d940e48100b07008143c1c01240c420080708042151608043e030000001d1600341d20a41e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 505273327 1250 505272077 505272107
    0x60c07081f0b030d0219020307150306080613020a0306050a0921021011030105040c0203070507080601180c0c021c020604091d0d140a1707020a021903080d0b0a080304060c02011b0b07 80
    0x1400c85882e40d40c070101e000d2b208840c43c40403a85810302808168402d0000030b90010b035400580804000c60340000c0c07804205480054802595100401e61500003908803503451504403c2800e001e40e4070b10400d0380d0915802082000601404c9c1815507007a0350b5010f140b802601021405003035034240810400207001000c8250b00754402008041d0000301d040c40b0510060810601034000388d8900900c105401a42c1e118104010340307400341e150409034011017100c0c01260107803540b600d00155141700c1008200184030107580302e60080740010310740200e034008116210020740188209440c5c101d040b690f6854000d0800c0c0852504d0001600352140c1a020b000408094038107022803c082c0000c9440c0e80030f0548032880107802800707041c2e095080c1202104070200001c0c258811062660b2980c1c609801440b040292443d154480c0c0510f6641c2c04d14514040e001c4001502c1d643c0b9903a07407001d4483d01c50081e08902150034541da034080c2300c030b200b1030610b00240c01101c040c032030741e86518003142c401105912403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 505274577 1250 505273327 505273333
    0x105090d080a11061602010c110a0b0903090a0e041e0f110f060301060e0f010f020d200d08070e0402030610110f1c17090309060c07081f0b030d02190203 67
    0x100c0003243c00c202075030007011000040a19140804402403d4410b0b20548809000c080401311108680004a0280c0300d604004e03000640c0d180c04144500b584100200d40d90300c000e0b845030125003280c44501e4180947e226101030f000000203010a00d900b10300c3c0000280c1214a50b04072000400c840d4103031982c0480c0f00510b6640c1c000c0d10b140004425800a80001d4000744001c528414a803e0400604e04012001d00748046100304031200296208200341c2a00204070b4000036480c14031002031106000d59040384143d804003807024000a20315201110082d00081482648808504052080320301400020f81081c0031500c0c8950b0644020060a03c400303980e204440302c2e200501c0d024000260b0b20740c10014680c4034006075400090440340040d801e407640920240c03e1240408000046035030b04902038030000e483d5200600d0300c504100080c3c0c001e1a542c02400420002068aa100550300034000308080007408038003824199110450381500d00540e02420341901103011400041e00810b2004040b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 505275827 1250 505274577 505274597
    0x1a040504150303111b0d08070f08032a03040803190f0507120b090105010e0a03050609030a090b0a1205060301090f0503030402011b1e1707030e01030b0105090d080a 72
    0xc202180c018021424441c00540c0d010700400d540200c01d03070480b58489004050746400682c8511100b80c000550503c180d5204408108018403042039038442900406035000001160400c4030341540119600510400f140c0c2001d019000100003840c9110190382e021402c6580300d50340d000b2070750b00180c001400c081300c10454886058880c010381207035842841c004075031420561000b13000f80c0345c5c8000144000d4140302002002e51545810641100c0b000d10b8081035032031603200400c2c03d0309801c1d08041c00900540341000a5564004001c00003481e0903940d00d86490343d281101c0603c1c0c01aaa08400013500d02c00c60300d111425190005a04418020300005041040d80d40c1ca920888540400f100c0d9030304040708104c29983c01520090070740d6004403c002e035001d482c0d40c410178115104030b00e601c00d0340362001e40a41481004040580b002a803840c403030b0b0380c400072801c02030700d00143c1e14029400241030030510705031540b007401550301e07815019210210745420361b51048030a030000180d040c100f001d03400e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 505277077 1250 505275827 505275829
    0x203070519020703031202040e040f0f021e0108010b043f03031d010501050307060305070c020a0e092104060507060e0111040e0f040807031b080d0f0e0c0a1a0405 71
    0x45401c48a9420341c00030807055242d8030b805071000d003803c080710030424414001000302e9002c0d541c0380d65000d540326403000002c0c030003460082c9800c900c03080080d4000d20460f0510080f00a174041305014544240c039407030102d80e0b80e0f40800665201d54000c041144921102103d0032a62169815112088034005128410550030030841c02500303108043d40044d40f200c410344120000c40d8480040b076529213009010540c1000040382c0e41c0c006d00d1051008240e9500001010b142c4510030f4862955401480054007503902d1164044c19241942c03101c50b940102d680114414450000e03400c9a01e2025907500d0601c0c2c6020004d86558101d44010f490303030341e142e41056088200a1007074510301d110445400303840314148008821110760080c181356003c500034090201081c040c00c29203503d00d5042c640b1440b07a8038100301c1165150703001e09008100807000304003544205038a4201c401c00c180c2c4800208464960004010342d12010320800c03e0b000031024506011340013035541411006507020b00301c540b130310b90340340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 505278327 1250 505277077 505277107
    0x60d0818011e0522061b0303060b0301090608010c020a02031e10050f070f022118030a060f0b01021504020402031b040807030c0503030a1403090a0510140c0a02030d02030705 76
    0x15000420025207240501c030b032680030480407002d203400440700360b04003000502041b4481240741040d45480c0042030425200fa04898040e11402c4556900c0356501d1940310003405080c081c0044650038800c1c1946480c0c40064682891500200142215964a034690f500c0351980180303c0150b0103440784060180c0020b0050070702440c00c1c44036280d1103140c0440014851185d861105007150012507907460000392000251918134691001140d43d0340c4900002c008030001c0b0040745415001da041c80d02c041c02000d0303000c1030941840002c28008500004012a160a005202540000c078818089009410160702941c2d100182c00e0b040b45440844c002e90303a00c5501716a0100c40c40d40c0c454082030040140481814000300b41c2034000310b00301500d0034805030000b0000290048030103c00700000e8100c800170002d40030203503000001d5801414521040002030888000004d0f550030f9408041401c4640c0e43c0c088666643c4a9800b86007001380388a0071802070351000d00391070100402880740385806503481c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 505279577 1250 505278327 505278377
    0x1e140f03060f04020f1e040b06280905030d0207090e0c09040c0503161503110f07060f0e060106080a0c09050927030316030906140906070305060d081801 67
    0xa0308014941e03e0184100520344882c00e5650340150303078020002010217030f05951070b0300200d4221400f148401561700425183e000300e0001c5030a0361402d0001c4591452101005003c1c501c0d50780d07542c041241c840041c16510780707444d0007d40042c1d000803003c00c622000c076401203000c40c1c56002074811036650b02c400030300305500c00e40e4103850002c03112500700810329042000401b03942d4800ea401145038600030072001424600d200c41e00500d0744407a21b041e4032080001c2100c0345103000305140d503140c6155040c034600502548402081c0c00d1b01e4260307001d406680015205040b44c80d16034950a465844c1050f90000e019a80d00490a00c0301090303010840d6a03551420620075420004050b1403d61700c500120f0b01008951040c1580341c1080050007d58840149505d020340c06904001c26110000c2c83c20800420103d4441d0780240c45020034002882404a0014090f80044c0c0e414026503d0303840410044040265004052081c20001882c407507099440300c1120090505280c1403e0b070364007000600703050b14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 505280827 1250 505279577 505279591
    0x1060503030a052a0706050a111501050d05100617010b0402090607080708070609080c011505010906230703020102070b010e07050313020616061b090e041b17070f1e140f0306 76
    0x403d5240c02e0309c2d4841c0407030755029030f100002e1045140703811102d40c00c40030600a260103104144001400c2c018100504612a0710b690810045c2e9581c0d0500c9107480314441510002c15420a0310010440c41c0c1402961351091008040601c0e00b552550f59a0040d4402c900480703100c40280603410125840d07102d55480c6d00e00400c1900c0c0d0785d100745d02c5100e00312800c61400c000c1e01c82d400c50040c40a82d03030100624044d9100b500b030500e02030090303003801d075000c5044510310300150300001118800c0550640151600c14030598000540f0707601c0e0b48009481e00012281d907070000d8070501c001a510a0b05c003400350207031380c0042c10107868221050242c4540c034100e20b506a0f0069144d10b0b8100030b900034141c00c00e01b100b8403864101960303410210021400361018202400445500341803c01e58104861010000d1180c400111007030392000001a0700c030380c41445030711404641c40c0c000040c61030000390791550010000070140e200a051082454400d00f140d140c003600075068030280d40c020344042040c10b0181e40303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 505282077 1250 505280827 505280837
    0x307180b040b03010911010f030b090907060224130c18060f0803090603131b0e01060905010f021e0705210d0c030801090b24030901060503030a052a0706 67
    0x14120a0109442e5100762441c0aa8944881d43d40842c40c07141401c148940300b440c042d80c504074041400c8000d45540c0c0b04107944202c5003028050220000100d910483d4031580a031078007080c081520310904008d1500c508500e184410003e803902d50250704030050903105054405050f42c1b03e130541001c88036500c2c8140e17001d80da03e5806200301540041210024075200008500d00030b8003c011402d039000103000d5030b441481070000c0000b0428003401007a220302800c0c1c04504465a2050200c0f400c2c01e080c1300c1c1e84082508400c02144551252400c03542e15180f54000348500c103010081c03074800d50854031040c80c26008800010800d5550f900d1581e030381c41da040300c3c1c0c400d803504a011130501f42003058107004184406404c00b407001a80141e01e003030440b4050100040c1b00380345100428030316038130711340c503540c00c1c0c2420180c50490104207000b441c0194090b030b00800226450f041896130f203111b001c04c03420100304240240043c80c164501e9001128040410000c0702200c0034038160300c5d00752283c101c100459 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 505283327 1250 505282077 505282091
    0xf0402060f121f0f030311011b120c030b060702210303010b070c050f0906100c050607091d0f0c16060608010c1209080304080901052a0d020708060105010e030718 71
    0x318404001101401c04115090703ca14604450f44113841c01c2c034400181031010007a91010014420750041d03510b1540c0b80d8005e03d001081c00d400a0282121100440380c031440d00042c141407a10920030542c407404050b00139407501041da020801060203023440710040941c0302c840d6501c40c9405002660007801c070610003d03100c140070f18103c03100e0030094021030300900e484018500203554401d0034640040060751304107a9840922070859089039044000380c00c51180c41c00780501c950784512003108407020039400000f448010f42c007207044840240c2c1c0c1c00f600d00325035401152680800c40006d10030b0828007181e0b8850f1018a54660054444030380c091912650b56100742c0ea2030381e800060710601c00780b04900030022503041307039240100e9010180002e40001d40c0403035802c60903405042120b4030143c2e21208090400d42075002034681d02d049034410400c0b8068401c05108043c0001045019101003001600c013580c245401120400110301c40395500d80706d2100c0000c0d00002c1d14012a0240314410800b2a01d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 505284577 1250 505283327 505283341
    0x301060902030f01060c0302071d01030b0c070b15180a060e0c0c07120821010819050c04110403080c0705091602060a0914070806040506060a05090f0402060f12 70
    0x444580e4026064140104100070f0030182081886041d115513051512440900c0d06041b132810f061500311340c8607040212610311401d218078500c00c2c120391142484214665075140380303410601555400800106c1c800d0b01144024445d001480740b0804090701c080400010009079900e00c00003518000782e0941e41c2e00b07040c0700b100c1c103400304d10f0341c800c00340c0c40030030b2500360f1030440c0700da035090a44112101295603242d00010081d40408a036004905221030b100058814150f0102c2c8920070312a144191041da4141c59200c00c209000c10708054200000d400e444c424030061001600c0b14084081784524100000300025100ea4050302c40b40c544100100f0103503052009200c401007024140203180880c42103940c181c90750000e40c00d64032070840200840d8084803072800081e0500034500b541800e0103070280106041400280c0d6600c102e020304101c901544804087c0b01e955005030080c2e0780c01c103911000081c840e00c00d102ca107581051020341803d1a0500f03940c3c201c240c2d078006000d8039050305d03c0c820603c208 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 505285827 1250 505284577 505284581
    0x30c0a06110f010605030706110c040c17011e0504020d020d0c05040915051e040605060c150c0705060103080a0c081306080a1e0c020c0607060b090906060d030c02040f1a0301 76
    0x442c1070b95002002036508003000a50707518880c2c481c04013080480b141c110421b00040c005141c01400180040c440c007108040050004110b0000074440c2a18807000043e0840000f40740b44a0754030722400000c1010708141c1480b01a50100550340f41c615001c10406050b070525100b40c0403031581680e00c4c951a9810070388140107450b030111140040c03c0c036080d4103101c0c0c0e036038080c0c0d1030341d584a1444030300020b0303c0d41c0300104c0c0140842d54420381c1d0203240894601c0a203900403681322085401c911100d48141c1c0c0d480d41c000340a004000b0040c0c2a50f112500520010f50440024008a501824403190115590780c502e580c075805140d015603408902d24081201755040908540c1100c0d50300c00c2404410107886101c0c0728501401c440300700c0d554582090040441c020302c0400705952002c0c0c0125500d10403400d10601170400007e4140c0501e80c00b1000402d1a280881c0c082d004201c0240081c84551680c0c070100c0360704403403040980e4031940d50741500058200ca0f2083d03003046d03e0074400040e4240700320010942 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 505287077 1250 505285827 505285843
    0x3051207030f110a0c0303050d06090e19030c140a030906031a040506010e030105250c03050f0f1b0f010b0a080a0219030506100302100e060d0b030c0a0611 68
    0x119054103010381000030340c1094104000701c50710314190765486040600030707140607003914001d49101200d01003c4141070703021004000b5203030380c00f80500400741e5804000f0211041070b11141c4e610707000040c55150050521260000440c06460800550503464451014901280507803001c4c550201e00b120f002c06411101d400c000b818142020010b10341e81e00001e900340c8500b04c0e041c42c03080d66078000003191607004111209031900054002c000c0e51609409420f0f0080c843c0076103092a502c82c58640303140340d00c105c61450340b45030b05036603503070904102e05451051a00810001800b01d8070a009200c1000d04140c80d00200d01c5070140200494003160000508440c940212580200050b4500344400000040c510b204a6070613900e0b072104c550403401e40d80301010b0319000140a409542c041c0a42c2104510804c0c00340e9000b11202002c0d40b121240a81c3c00034040320b05203030045014040180110415403145090040c00b400355001d01d05917000180080800b0740000e004030b00580b103400000c19040006d28 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 505288327 1250 505287077 505287103
    0x60e0103060e0708151512041e0804140d060207050a12182c01170c010918180b0a0f050c040302090c130e0f090d1403070e03030c07060302040305 64
    0x541c840c2000b05000300b60a038000c0001012060080241c241d0303491380e0070381c1c0c80d104444d802d08544034070b0404241c81007c9415603055401100e000d111b101e200001000d580c0880380d000710341510381454140183c020403642690a81c0c0a2140c90400010803442d00040084520540151032046460300e09085900d00c80d2001d0740c00c02c0199958000340c05510f21401c01500c0e048846603a0440099a01c00010b07014200f40d04c8020411500010f140c14464440b00342212607031050f617005010322401152020b0035031203000100c4d0406681d00b1071008960b4407851809009140c00a40c80005131150185000203540100042e0707560b125101c196182d40c03041c181c0003c0c1030322020707142a00d141c000868861004d000d140c3c01090020340043c214041b91610401003000300c100c5900c5180c401092803810000311210b1005028080903240ca9500c124030804a0700b031413001c00307825a1201c66045950340e8008200581503c01003141c01c40c0040c1c208111002011039980240c6d80718210302e0b0290a05014401c81 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 505289577 1250 505288327 505288349
    0x210020f060c0a080f060a060c02030304030212160902180108071707080604060902090d03050313050607020c010806010810170f0f07152a151a0f0307050102100c0e060301060e010306 80
    0xc406c040d40d45420745001c49035186005080300110b400040c0c05e610440c0e100a50040c1c0320710130aa00c0d902e010078441c0701c062840340075070321440e86c1c3c44c3d0031001e038442c0c902e003078903c1180e80d86030a502358003900125811403c5072401804208040c903404185050603500c030300100c1d4441d01000054a400d000c4c032005440c4c0715105600b0711804034081000e14402e00300040a01401000048204880340059610240c01c101140c50718204040007a480392006d00e22180003d100b5400604954015243c160150345804414240c003840d00d040580100c104402e400040d0188034464944d02c0c004008410743c40c4444809001e506180508400d400001d802540040c00040e040030211301c190201c01907400280c40d641100044205e1521005134003500c0300300d1560602d060000801806c00550f4501084410340c0e001a100500f0010990f4800c05841003038016440313030b030340c02c0a0003000d50082802d07000c1e182094415081c0704000180550002d0308040002401c5c8401d0a8403903030300d405204001c00401e624 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 505290827 1250 505289577 505289581
    0x140f010e0108211806130f0e0103050a02010e030c04020a020717010924090602030a050403090b03011a2d0304060f1a190b040f17070608040210020f060c0a080f 70
    0x1c14145000b501c2d04840c0e41e040104800c0e100c542c0d04001311064140c0208600c1d6500a0305840f941081d00b0b03030040030f9803a410b40300040b881324000031007103040e6a0040000d1010307640d07a03401104c00c801104512038041c0280c0d000e110043d12180060076000507190003a01071103050a0040d02c004031290140380039681800320250105e0803903911084204030500c20320200c0144c3d0f411440260249000007000980300004011a0480d0799000902540c4280e0304d00c00140d030380d41485400d5000038020740c12058455840365062424040050126420410b03803510480a080e000c94201c100351101c02401080000803c07080103114814840c01c0703021100308210301c030100501c0030701c0e5848410035540100d00c1c0801e203c0c40141004542e20040030f092101668a03900c4004085c94005103108140317100d0b00d040721440e986000030801d07005403802680e414156035a55000c0142c1030309140300030350a50041c0c68241907507090038400c061281e1440c15800d640e8039001c6100410f4058001e180d40390040b45002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 505292077 1250 505290827 505290853
    0x112150504030e091008060406050a0c0207030b0105240409050627060111010219021f1802090c071a1e0402010801031b05060712030b0105070305030a050703140f010e0108 75
    0x1c01c4541041c0e402544c140d0369690704000c0004203402c0207141d48280c2c810442004015040755100b11522801403007500004002a0b07603850440c007009001c107072010014859400c009000c000c0c1400850760b000f180b9503030801d0840e00f641c0650043c1301019120130403c46241040001c2c20050142001900e514080b480200c50f8000005061181006280c43c4011030421094060702c814241c07801320100b1403c04d03a20080d5461a00031800005c00d868024000032801e80761003401040c64030401c0c210b61129840e42088160701300100144039034201805220080780041d0f070303602000c074403505209000c4d08140300e40c81c645240c4201c4149801d0380c074104100043c1d0f031021800d0b044230b51203450040c009030150782d0201051502e4000540000703011071540140459100044640155520200054080000110346611540501030082101080400c01000d5103601c156400445803900040c1e00c011480e0180040c0c809450300b10006003514014400f00c84844801070040040b1001819440741c42a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 505293327 1250 505292077 505292087
    0xe0303151507060b041409071a130504111207090306140c09090403091703031006050306030d05070305040902071a0a0507020a060e160f031a0c0706021e03011215050403 74
    0x200010a040c0d101c641200858445800003021b82056a810204500c1c00700300c4155035961520a68441509201040c6100e100c0b000031601801c425001459013241072400b4000500f510800104520808000217125210000f120034017480c002c2c2c0d242c41d030a80c5142809130540340c1d0001c44041c000519400d10072003181c036804540f040201650788000c96030b214103080c2c3d41c484540c1e2104204004105000050b860044001c511556500130404a441d498034001c84035408121000c1c1d406a00860b95100082d001d6800342c0078003072080c070303000389401c0e100c07a20003050342c2105408803250700b9804c54480e01a542c40818070303403107a0229001c0140c0c3c504000c0095445500c500060441692601c024061040c1030018514140b1302c2540c0c0003405d9621089501041103502c4195415001c0341100c80020881c1c0003181d0040c1020780425003004029114040207501620352038500540218070994501102c030086c500030019407118801c4541d083c1032242c62034203604008002c1d113181508010010b0342007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 505294577 1250 505293327 505293337
    0xa150221250b01170f06010501080c03040606090f0b040b0d080901050d0b0622080604030906050307020c090712141e040c1a0a091203080f0a0204090e03031515 70
    0x15a9214500c0341564011a48004000001800b40c12000001140d43c659140700502e82c812448111041c2e220519440758840d20700380500c074001406000401ca00c03141c0c260207541c2240c02504000380f615952140c1904594030100d282e0741803511a10114600c0c9014494400e94490540340881450090794038900c40d441071031182414010049500c084030640e581c4900301c0188080c043e0f0784c1e40c40a56903942c202c100d03940c00b070070050400100c0c007041680022031168061030b85504d603c0949410300740d090351150001003000003144192041c0c43e1440e40c40c155880d0082c00707030361101ca07003e0000e0712910003928904038071558101011006c3c050805c0782020329010070848000e0000382d03500c2c3e81c68481c107220856800b450481c00405182e00b124031311400144821170f226202e040d04141c0e18200b011130001190000f1300410a1500054004201c60702c540d640100c00d200010b107056100c07184034084075100701c01c6d040a50b2020003004a444001c4140c204212412150b812247d140c10321410503038803403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 505295827 1250 505294577 505294597
    0x60f0703021810030b03070f030b1f0905362401050f010c0507060305010518040206030f060f1903060b06070f030318060f0b04050c0a0c1e020a150221 66
    0x40c60340800c1055101754481045010b0040507210010742e0f8881d5440c0c2002140400e580e00c0e81c081c0302040c038100d207072402c004c034141e92119046542858140002c0081100500101a03400040c0900c02c03101d800e1549001522050021a842d0282c14000c01c0d01d00000e01c608446074101040c501d000500e0786020443c11188216049100900860010bd885544c6584010064400d400000c682543c050304164107035041a2100802580507a00c01e00d050b0f0002e4a020390000c00401c04242400220041298040e2014001002e655025004520320550f0100342d80c1d8071000c2d900c41482000b40e180122408140119a00c0c0d045c0081503d80806024010000400341540d0705a1070705204030340302d01c41e05d030f02e81c102c0010426002c7e01118000030b0010030314603d10452502c0c0005040f1b00da80d000351581d400c0e95503145461004c243da610245441000140300c21180f4242140c070050f51201d10002c00f80c50011520000c0050b004801792806640d281c2c0b41050040d440706000da51095501a2041002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 505297077 1250 505295827 505295839
    0x22505150d0905030a020a060b0102010209210c0a080d120c020d0c0c050901631503020108090304030206030403050901030b04110c1209100c021908060f07030218 71
    0x201c0240100c008044014004080f8000403404110f42c0340c020131040c0c000c50180400303200c0686200012401c034805e40310280d40c003414a03402107540e00d40c0d10064101c1c3c0d42808049944402d21940084c2012913150302410195008000100d195035112400c82c512079040c2100f4130100700440800b07503ea41368401003d040146031880c040500c03901e0740f0010003d220203002840395503103441411401c1d103941100015038404411400c1c0112440d41184402101229019180070b00a00250f03195000585a9110400c901347c110049144642c131800b04800510b6503481080d40c6184009401c42c58014a2242c56030824817041000da201d00003120351082c1c0c1440e00790740c0c618a080c0141c0c0240070140c40780d030b081858101c8105c55600000001d01464108008860021602e480041a64840e4071580380e00260301519440115001d03510f9425914401002c0d9000715109082001c10322a450f0301c100c220b40d00010038040303807007000011190003161600e015454207500c4802d1000741c8801201c4a80907030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 505298327 1250 505297077 505297087
    0xa1b11040e0a0b090c0423071206080303010f03050c0d080f031b13091109031002130302090a0203071b1a07111b03010c050a020601140a03020d0302250515 68
    0x1440501c002c010503a8005030340e01c8281440e401455984614110701e0b03028038a0000154001d030241400c0b4140030940e010180d801c1c0c0c2d99120101c80b40e941900d015007001da21044c001c0382c07043d814000766001e0400300275510b000c03a00c1c1d800c1491404185200c5280100d90380c0c220100440c00b00030890700c0342c0c20380e80180c42d600c0c1c840b101ca002c1120304820751060a4200420184120543c800510f03003140c0000c81c041c0b110480030800c0d49041d02c0348000c0c1350342c19403203044004421805500a80902400224a1f003002c5990360041043c4030022900340c440f41e58000f040200c440d41040f0000d82c070900b068640c42c0607880f90383d42e04074200c100000c00408006c5141c0014080ca11030aa0030740d00c0441d400a9490210f0000600145030b68140e141e14440d50800d0580744040d1300c240155488500954014807443c0d1a00341c03440250032840d00880c0d04016204004005602d80c4038001d10324500c0f030f5006040401c03c0003880314604008204010380100d6504042005540b008900c24800008687c131580d10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 505299577 1250 505298327 505298351
    0x21207050304170c010905030c010903060906020d090804230d021e03011a030111031003141204030c06030506040b0a051c1a09161a090f0306010b0a1b1104 68
    0x1805281c2c40b503907000c0b1403c0741907080c103800030440d20350707005080e00d40104040e196000c043d250f00b61001c0280c00209003001c104046400f5070030440895000305001850b243c0707545e800001369280c0075010385060a0005003080756089504400c81804401d05040580003e64400101d841c01d084074042d100b550511880c11400d114443c00d40c5000c24018020002c1000d4040130034031011490a83c14825440e001c8034014505091044a20640300301140742219800e550b0382140b6026600c80e450702621a8086810759016104003d01c00385020b0030a021805107040d000409403503008080d1800345080c41003451183d25241c0d0000240c0703800b00c03580036a8035194040d8900c0020989401f83c403882e06440a40d540e418444807050180c40b54506541c00c0034040601c014450000d4400e403201c0c1d06001010b440120f075028054200d0550040c980d481c1440d60400081c03401000780c02400c00840700140c8a0300554020300c500210900700440071400c68115141c02d094508011031403070165845140b18002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 505300827 1250 505299577 505299583
    0xa06020d0b0424050d0213020705190b1503030a021c0215040b01050a050916180b0d050106091202010c120903020612060108072a03020f0f0c041b02120705 68
    0x112024104109060b20005071080388060061001001c03100f521000c1440e0802c20124402c1c070745c000d0070901100780407000800080d480790509483c240125003908000e41a81200d170404507000e441d01c694541040f07400c0707068502e038035000148250301c2007114241030760f00442d52900d4018015000d00d80c044444a0580c10920142120303044a00c0786810042007100c4015014160b0350b06403800c00041d500c174000e000030101c00341d40aa200e00550403201c0000c612452444c2450400108130000e8a6175034a000d003041d810140c480b0400c01c0d15100140000d0f540301100f14005c20b10b0001b10601f0307500e9900040c042203e091000b80c50f0701d120790500d00026001e43e070030000540d8058517080da544054400c0320100003003600e1050000b0000c40219070468491440986100c070300241440f411078400c038076074039a001c240303500301c0940c0900841d00207083d00501c05440700720303000f501500700002d0810400040b641503049031801510380c1407400301d80690020329007003201030460740301d0350721106403c00c603107 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 505302077 1250 505300827 505300841
    0xd0506300c100c0b0906041a06030c0904030c0302010506011418041b08150a0308090d03020c120a02190b0a051615021218060c0702040f06060503100609080a06020d 72
    0x1420000b421042081264450b00e091010380c0250004c886507250546810b0311241d003940d01802c8065040301e8400c00744c610012454118100804a50004d5112801304a9401048030113601203049170100301c0c18140c081c0a21540f100003440c0008210707041e4200711485010304d1641d80000b0520400c0721040e52100d40c00010062110043c149001c0041000140319600886034003070b150101c1c40442145040c290113400580303a200c4c00c00d41c01c101505080c0400c000c2903034001e6013148240b012000d04c1d5146e11000c901c400c94010b0241c49011000e0040c45804100b1002d01c070002909d240040080030030100954001d05801d10704607a641300d0b401c0c00150400154080901180034038010610440003560082c21201403544940703000d580c6007010171819000c0c001412150750400d00001d80380c104803400400041384000d01c0000c020368400e4440c03048070140e42080300030500000c144044031300002d003150010a01890b001c16000d051002c17158803220200710047c410754011418102d801000c0e08a04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 505303327 1250 505302077 505302079
    0x51c0b1e0a1809140616080a0b09010305101409030a0305090a0512030a0605010f0e01180e0a0209090606031b030a020c061612090b0c0c07050a08030d0506300c 70
    0x102d445520b51440c0c1c0000c0c4440c1d401194541d4154070f5031012004042450b500c074800ca6542003070301c2511940c1c00d440c030740e200030131038921655035015900306030ba200c410781806180100000c04800f0b00d5000010103d80b1b036151103112811018003000b0b030380380c1e00204640700c5001c0742c07030013203055180d15034018a01020410b000702140140117a0342d2041c115035001e035200da0340c2c0c2481842040c0d9038000550b403242d50460b0180004000281900140d4001c6030381c824403c40010203002c20755550304240c00e1902c021717908048044d0700040c04205c98030307211450940140307003290b0700b5155080c168011040c250000c482d03a0611309010001505c1a15280d055445030300301c40003074035030711314124000c030000700b000000d0000482ca05884031080080c0718410f00c07600c5503000c01d001c3c5040c1c8a6600b0030b0030b42d411000c000b122074805c28074045581c2d03c0781c0d5101d40060400c44020b40c1c0300d26034503035680c0a58000414242c056003104aa0f2044000490f0201070035103030046c0303100203030322908909a080007407040b101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 505304577 1250 505303327 505303349
    0x21e071a130c150309080d050f01150c0b0c2101051809030319021314010221310e0a1413200307080a0510020a021c020f0a03051c0b1e0a 60
    0xc3c1c150002e5500724a101e00449d00000e030382d9a1b00c50714090303541000603045000003080c441c40200003d229420407500040401d00882c242081c00035030494407888a0b24501692600b54010001d5080a901c08680c100018000b510340340340c8541013039900d020081c58a040102d0700c020506d0001002d80c101d038040109016020304044e103501c0d0302491203800112160040c07080300c2d400b110440d041d00c016130198083c4000d9624100c251041c0c80c48004807145050f180032102c080b10046141e030b010140e00180411845880245006450b8500b150b0302c04442000c0780c84c1000c100b10030003100e4100546c842e0341c04000e48508518455000300400e2900c4000343c1c05118003000402c4c0d5640006041502600c144200c1d0141e100c00700d00356069014400840c1c000d83d004800109882030140b0442200312840e00c1160410f0854150151400d01056001c2d030118030006100403112040c5203c032001d090310707280d0a020a143c0d900c0483c80ca03915859400100505c4c030a21004540d8600080100406104000e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 505305827 1250 505304577 505304587
    0xa08121902070606150f1d0a0503010504050d0f02030405011704111002030301080d0923220501060e180a020c0a0501050103050309030706180306021e071a130c15030908 74
    0x800001000180985400031548644d840101c5101b4500b41007a480d10b5a80c4074040c04150092040d10f0580c41c0030503a1021100e1800700c0c564409100d02d6121380d025200074000c0c01c03000b000c094101080c140c909021904204014005030340c205800241a511600d80c5020320360315070800c2003503c1080e4000541c0409a0416000d4145d0b001019505991501059811302414a642550841c600b4800d014045001e940045903600d620180320030081c07806824130210031603205903864015851501240c0342c0b50746d50010701c04203134040c201e030b00c2e01e12064801b0b5403002003207544c1c580c41c0c02c002425610f807103800007103076440c41405004d021030007948880241701c0303940c40346820b03a240d4010320101130282c440d09100051541c8105442d5172070704861089107140b103042d0385030000030303500c504030080c0103400c1d405514400740c10043c02005035602800320b0710741050700d1702c05488803540088d140d1070004100324400d0020807444000c1008440840301001381c1000c0300036081e0080e00c40359a016041c0d81002c07407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 505307077 1250 505305827 505305833
    0x2040f060503060601050c0a120509030a121202030c030f090c12010b13022503090e130606080c010f05090301180f05010b030307031b05120a020a0b06030a0812190207 73
    0x22801d840c0c040b8151402650740b900110769600030604070060592120900101081c40301074070541030076180c034066140500079004603280c51400101101c2d0803070311106842c0466445140100c0400718035100390300e54141041c10300c6640c00080c1114010f43c80010200d0b01c54601000740341e0142038083c5c0500a0401181c40d29402820761841035400b401d1268000301401159208840451386001d04070107200b0f04179500440c1182c800e0b10200c090019012010402c2440e40c139034544104580386961580203528540081130380c5180d03015400035071100b5240c14581ea0003d4481030441c0b0319140c040d0f1924001000240900140c5408924202051410f4818028006680b5680030b008400911401490509065883c411400e018000910f0055125410181c4070b42821000c0d001d90100c41e41114001131800680d4408e60544025030710100c01c4904000007400c195a005004038064142c08410341c442030260300c100150a2a00c201c20780c0054002c54602c06150a802980c0c0030031521400703507103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 505308327 1250 505307077 505307081
    0x1107090204090e011506050d0b060d02030a0c020109020306061c0c0e061914010c050312191808030c0a02100e1e0c13020a14031303081605180a0302040f 67
    0x4042c540c1c0d514109066461101c005005007842004030480440700c1c0c51822034100d429400021f41100d281b82c441e0448401c03a03940001a094150840e20010307924180f00c42c105089840101054080d0390600190a000d41d801003506503011a0640d4014070880e01c1c10b800c0480d40e0070b0040020300700061040003043d99600400e205100d40e1050b03c02c018403816030412201c0b0200e49100e90b540d1a4201c080b00c9855502c1400c0c02145103100f40100c034205030f120716201c50079140444488a030140b1035040201440a00d00445030005250041e41400c5111601c4503149880001c00385050381e10002299400c49100b00105070309190b070210100490140c130150140c0324045030010b698408c100903a003000c089404100c0d060640c200901e5000c10206049649001c1e4012140800512080e0a5184202070900d0000c61103040584140c0f0815082c0b440c1c003405682c8080c08410140001c084041c0d402c07600102119a8010714201039200590788100160500e11240c1000350003d0400c0503c00000c1415 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 505309577 1250 505308327 505308329
    0x5060108070b13060509010c0203030a2d090311011b03020601031205120a0e1c080f1b030a0b031e011a190605090f0405040c2c161107090204 62
    0x3400c1980c00039603840c290200d15004002c45403800c0400c80d4000c0002500460040c171094006050000e0032040e030741c00180c11500406400d001241c8800c6042c0502c2d0030300003000d445240310307001c03000c2640002c400c000c059000030f020040c08203503483d40101c1e4583c040e2001d1b48104900c883c00407400406441c1c000d4407200280b10494a4200003140c2d04501e9026500707584000002d20841764030b65079080b540d94083c0c00b200c034040249005466000c8100091510a00121141922213001d18144020015210000104050785000440100200c0c1c0c1042074100d0f504074071300364408584d00784400b001a0804404504405c201c0706002150350716404d040d005620200c1a044030550500c40c0d4209001040d11410061904203c1200c4180700d054096800703400300500c080c156803880d08448012408880007647c4c1034031408040c0c0010000025200e0105c400045104503c03103250f400d400d07040000c5071001e400c241c04d281074800100395081c4a208641030054215040700c6029035180c811400030b600c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 505310827 1250 505309577 505309589
    0x10050703080f1315091205091e0a0611030c190204050a050606030c0c150106020a0203062d060102240907080f1b1c0c15080f06040c0e040504050601 65
    0x50301c001803019140903100c1d0302c54100701030503201a01c40303565403608020300385070100380d2642e550050380d012814503640d01c0c00e6106070f500c03600c3da5844030350108038840f01c0811080300d1801001503441c07540d0f1035000116040f5000da0500f00000d6a500c60440d045014007283e0070300c54401c401604400da440b14040141490080c3e8080041c1d845000011090320401c03503009400040c10004100000e591400601142c0ca8440590703046a0307000c40a0150703080700386d00200060b489a8103070010b40c070b400c4c00129000500c00031014071807840c2c2c3d181806d0b0b54031045420300000c6d00c0000007130440e90007402040001a00398000305001d5503450800102c2110030b4030304680301d214607400810350303640c0003c030080081d41d120001c0c40110a204009640030845607180c0d80c000b00046110000b030200c803d10a00301c10320a007480401207007481100b4404156042040c010443c890060100100549204907003110b0103039400300d01028480300554000c2112005103412a18080411003401408103400c2e0684031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 505312077 1250 505310827 505310837
    0xc05030103110f0d0b0a020c07180507081302010e0d1a0f010501140d0c091502010507030f05010b09040908160b0610050f1b16030510150f031e0210050703 68
    0x41c8a42c180420b502808000c90740003c031081031034012030649903000ba4403080240d0094034082e02c81c2403840c01d000c2103511110b02d200900010700e2481000d40201a072140d45c51901a080b443c000901c800c8058616600ac3d050081c8000d0040b82516410002d4540942181140481801094500118074022180100040000e0740089070b01d40c45100f65104045c41d07030a140d410482100d204034003c1014000000600003042d03000241500c81c415881004111900002880d281603034024069500744ea8000105500d03141c010310000c0031100540780c005406840000d40c03076100c0d00e00f0300d0540c400d2003102d900c1108080d400d601000b00070103420340f20b05419206e40b4100010a0001c1e1424000c0070019160140144240e02400b11440703052504100c0c17202c01c4542d2500c9102a444a211190300156075640200c2441001c240310790086040102458843c000303964500203000000400ea4000200202c0f0702c031140490280014600d850070a8006044446810b00c5400182c0f980c0d128040c2100454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 505313327 1250 505312077 505312103
    0x30702040e0609070303050306180f15090105090f0a06240306210b0702071e0504050601022e0b060f130f080706030546050103051b01050d0c05030103 66
    0x1c07a0104085004000800040400b103007540d505860350381005081035000b0b000c1e080e500700340001062855004d0386500650343c089080480e06840c03800d5254070164080c50b0008010011500c41701c41c001c0d8003000500d050882511f0b103120071001360a10394016070034600d10b070100c1c5150400c4103041f01d22040054508000f02c55503142c2c00c0641c10700114660017025815a00c0350003069000c0091a401642c1e4410703101c0d200d4556640050a51820403101c2001041450520281c142403142542096090005100c0105003e510003018402580040c580c580b403161107044080d074079045000030301402090a1380b00c01301c1e00d0007081e09400038542d1100040200000081d0009c80c5011001a100c464001d408140d06000302600502070285c02c2454210350561404c1c00c82d0048003104d481900380c1c401c43c114400f644e481d1160b080320341c8250341643c1480d140041000800024121000b0076802c0040340e00900d8038401a02c1500a1900442140d400c19640301c0400d580400198183c078404c2c0b112075000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 505314577 1250 505313327 505313351
    0x31e030a0e0601050f1203040905010b13050306190c0201060b07050d02160b0405011d04020c07050a0b09010207030605130213050a0f020f18040b0301150815060307030f150203070203070204 83
    0x82d5800703114864001842d020020b500f418402c1110307041062904c1260b28191303071250140100c40090f0301002f81d8a40200f124040c01c4840919500100400c60007000c09040801c02c0d18148004880f541420726928080001041d0003034103d03030018542c0c01603250721a100c41c2030160311038424801640043c0124100c030281982c1c40308150003916001081c25041c40d00300401510400101503100b0803002d0203100a0125a58030300007062005002000b40c80094500018440103540c1c1e5044080c01d15030500c000703082660b0000c1d040d01100e8000c00045529140e042d081e50780391402c0c40001e90444024016045811032075000780380900740c105010401110919608022030103010381445074503a04102c00001c1e0754244601080a080060000a03400c580600081c2103d0360850420115030307084004004220061018043c000803c0c03c02e4942071603c0000a0380300c83d4580030046c130034031038052100240182d01560110380103010318115900d04144201a69a400045040f071240d42040d011b0540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 505315827 1250 505314577 505314583
    0x305041a04030903122a020307051509041a030d02030c0706140304120909021b070b070503120417030403031a030a0b06040c02191a15010c080309031e030a0e 69
    0x31480c0c0643d41c4481e4a4107642e52507414810040f040d4040000b044e04040700c00340005101e0600b0312501c080c010100009206141c02c1055a5002c503124104e00c0e5000c4034100c03125012166140812240014584241424414608a003004080e014400c40030120001600080200ba005e1850800c85040e265548012a0b1007010768102c3d20201400348085800240000c003801828500c42c180a501d107a1180b0700403040f40c200580301c0d4161403007508107580c04c200611000b0042c010788003550b0318040f1207840b015a00c0c4540c8203844e00c0b690b080d600040922843c4c100e082001202e0004031641c138140790170003c028081140305800c070000451a00023903481c000403140c2c1c040c4c0d8040700c1031099a5420003044001c084500c81e9100b94003841c03440c00600051030058090152150741000b0700b41210390000180b01d50018400d0310401c402c4000310400e80e0300038502103e401c3d40300d6443e80e6251383c3d00707a450307080d40100c149800088191a10340003024076a403016511501c41c56004100090046a00b55a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 505317077 1250 505315827 505315831
    0x60c081e070f030e150903041e030c05060f0f070503040501030509060f0109150816060807050403031403040c090504301407061b0504081207050d031d010c0305041a 72
    0x800302d2920540340401d54041e0300018902c0c1d4101e0141e500403240e4800c05004030704110b40d40c40c1c05401c0010140000c400346c62466400ca2400100d10014a04594805041c601a03028813072180700007141007007240b80e00b002120700a6079502d8a0a4480c946440e0035a03494200d400740074046410b0a0004c0c1d4072600c00101c2902c64003040c1c12100b141e901e8910058010803a60f01d50f9206200340120224040000b00004481c42041d64010600c681c03400d0b0000701161000f07080b02d020044204010800b00340c3c0000420320200325820016aa0b45076490101120509640300303400d190b041c2000c000500006503070940401c03280041240200903003a08480840144451500101c0d000c94280075680320718401401d1503074484e1400140031030b50000094065058140204006003001809210030001480300c9140b480c00c803209541007280d02c0e038039961134000c02d010101c1015600c01c64100b59841c40d52803048850200c00081003903800c4000c0003000341504580903500c80c0754040882d000c144100f100a8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 505318327 1250 505317077 505317091
    0x1b0108040f1709180a06061806110307020a0603021e031e180a240614010509031501060c1a0609010b13030c06080402040f050705041203020109060c081e 67
    0x1004079401d5031800d003582020018440041020300210344161941d821a25054003052900b0001d0b24044a090042c1c5159030004400c00980800d9004080e625150010648006080015001d418810a40c2c658024803401a5000c084c800b00060995016401808080507204440c1c104045a0003100f615100c255050030325148230086c154030030040003a02d9a08031410358031020014001403104c91910100d000f09075006025100116440904603440646040300c0d60710601042d403a00c48406803184012014a060000000700c054090b40d0901101a2a0181c1c4c100d540407540c68060040801c2d903100d00860314030060941341d1b8000c2002c0c81c415842707590018109011a8284180e05145400030726035030b1200c900801000c000204106481d030090615075a0303504803071034a401040107a60620310506081484c0c202440041e070741c00001c4906843d018004009120f50a19080380101034061014010916000c9641a100d520201c128080d056400c48204d40000340000380081c80c0c0e0980b411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 505319577 1250 505318327 505318343
    0x2070b0a09030914180108031b0a0b0403032301060203190c0506060d14030406020c040f0c0206270105011e0803040b04050d0c030f031215030206040e1b04081b010804 73
    0x10000c4c0c1a8200003144601c502400720507000442803601410543c00b030f00800700a800102d980760340c40f02c540750144c4c120003440d03000f019100216100c0b08200c481c0940040d04050b05e82e01030858030f042c1c043d0a08643c0c2003911504c00d0960756100002e40b41c2c1c000450182d0718068014014064900c1401c203008040d4021000c0e0031a519440304011405c0140b41d400c44420180c1807002081c0d038414009040144010740181c1002130b5038404000844000000c0306101e00c0c07418000e40d81e42c5034002020b0390310401489401900703400b40c0c81e03054105c0030120b82d160419030a11001107204803d5503030f0201a003029240b400000c5031100c1c03203245c0300d0190f801040400b00d8244010000381c0f0b8030007030049015008100001c42651691a8400c2410381c060741600480e10209140c500d046061080c046072000d000c9240003410704507030008040303114500c54180c01075240000b088414070458141d40e010f0140113041030350746a850b840b15889507e0700414002025280040030407a5000703035411132045602a00d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 505320827 1250 505319577 505319579
    0x3020c01110d170907030213060e0112050d030b1903060e0606030d0f050711040207060203060109090c140d0f1829010618091d0f0f0a03081b0d02070b0a090309 70
    0x12042c050f010003403c181c0a8030a0b01d0300000581c80d01400d6440c440900d4001260160505003000880a410fa016040c003070580401803001c01e074049040071103140203140200d822503100c000180e45a4208103090406002160f000041154550041e0340d52018641510711075551a8101500c490760400e0190101d29084100318240340b00b03400800c1c900d03104034501c0c1d0400c0c0c0c098001c5001c90b000b95034100d6070380e5400001c0c48903668001c101c0ba001081907a1040c0a00000894010400b40001c100e0f00343c506004255402c0440c0c19401c805441e4072480400c01c100c406080c220b16400110500641d80c1405008a00c038400385e9840300811000c00207403910000303074607008084680d5440910f525448001e0320703d02103a0041540542d08160000d40000410744805d00020303401d04054520401c141c1c0d0015000503507803100801d40541c0203030503050002e0160384c0e51641007400307044440d40b001802400503568400c0344840d03002e0000c650052030351640329a1122001c50445101c040094046000800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 505322077 1250 505320827 505320857
    0xb0a0608150702071707090603030e130b0f01031503140c1912030e1212041d24060f03040602070c05040506030c040c170406020406140a0c0f031b03020c01110d 70
    0x1c5c2c030076100649508803100030b903440b4520b108440e0250070407070000707000d40a06129481c02102001c0d480010503420007a00202e00d00145080e00026043c0c0c0c181529084107201ca01f006d020000019a000644041c429660140301c5071101c02103001140b0621850640342c0310400381020000c03d540001110314400840d81c0c90a507200c6400c4140c4503486504c1080300c40f03501206000c11640720070402c0380142c4035030804038202c07000400e81151038002c041d008208034480c51641d181c0c10124940105998010900c0e81c04612107115085110643c2c09000040c0010440b0070780c0100301190150051480f0030352114104000d0783c07030a0300c6103589540304a012540d98903041c0e01900007920f00e801c1000c404181d0141c02000000f081310103541d07241d4007040800241d038100810b510034421604101c1d02c6d050b03010707070b020700720024448001c0d2103c0c04030f007015400c15015940c40b1000c1402100304a040b081c00d448d000b55110440200c2d180060000011a020b4100004aa0b2038003000c030f0b01d07030708140c407100e00e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 505323327 1250 505322077 505322099
    0xe1e10090e0a0f11160c0b1e030604090b040c0608151e1f08040b1006081911120a0e010b0616020d0819081b22030b0a060815070207 58
    0x41c024403030f8aa89203504c00c0000201802840030f104090321115191105040080e1100155481030346100342c1080003805488555841d4442c80c000b00713285e81d8a81d04c036280850028005151b0080064001d601440117000700c0140030307000c95101ea96891640d9585500c004551040005c402d5000114800d008500030b0741d0100e03034241128081c1c090030200c81d0704201e001e80c10318040c0d0500003042d180001e10041c4103008011075402070500b5192648245407400c01403440d10010304400640d640303100d40e18100036040d000382903582d03c4489030300d0702d079200f0036510100000144c4203c2030b8113240c10b091400f001d106000d501c12120b00141086c0c2082c8400881c1c00112140030400c07640100ea0031408000189a50080c1a14a150340f0381e2011003031170300c500504010809001600040e2441003011200c0500d50201c44a05080302001e07074104000c403030340c4e00300c6c5c00045d0002800c070182401000808003456106504a56070001113500f494029030b00a81e00000a80e000e0f80140c10010013884900800b03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 505324577 1250 505323327 505323341
    0xb091504090506010f0317031b0a0c0c0b0a030b041a041e0e0105040c080a02090105042d020901030f09020603040206030c0408120315061c0c0e1e10090e0a 68
    0x58400300301e0404641d521030624800340c0190640144d030000038000d01c1348850384801c2c0b2143d14100d441c51410416038040001c07103c4244000400000200004500c1c4a151401c08485d4001c4410701c020380c4500075501c82e50004881c81d00042d00d405030f0310f8900e18060142200c1041c1c0a5544520805c542090002500b203070f01e400c40d80e0185450a00340c0d080f03050300c200d06201e080540000356a082c01e1614003805801030380704803403550040107180c015903518610641191000c030b400142c2114000e0f0001c0781d8000c01c014445c64503040c500c610f00309076155002418032070002d030b86c100583c5c04ca0203071000850305d00c0704001e50030680070b200203030050419100851300300110080441c181552020010b150845c51007480d074407018044280451070341c2140c015880440120344280c1019070782003041070322540c40004203c0086e150742d51498024068905400140f00c05480f40b54200c5842d280f11b0340d0240340742030f0301d0301a41c825034242003854418810350f01911241c0071000780648820034444058100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 505325827 1250 505324577 505324579
    0x200909061b0306120708070303140316082203090608091b040b040618092003030306010c02040e15010810020a0f0c080d0203090f070b1804050910020705030c100b0915 73
    0x2134190302114402c10018500144208001000c2c014114070340142510414020303005420801c0c014080c02140389074411908400c245090394007541c0b8004500707800c8041d61302c1d0000107200c680c01081816407000310038095603401d1f15401e0091315072024480e681c00034900094210340500c4d00100b003501d8030b81c101d40c5000c400184003140b003175103a030207014000c5e082c0d052000ba400d95400008041010389200741d042c0c09101ca0710040c0b0120044003107a1244801024581040480d252200465845902050180205000b00d40c15484c20b48150048407a013801000b1041c03182b509684400c0340c06002702c0f003410301c29039500c0942045d07107001030f5810b0f08070072001c4840d40d1003440600016400e03840a148502c0310940188588601507a881e420010349030824603685504211518420540100050704100190307030004882c2d88611041741020407141e020a0724038000160711040c04000009011551b4015003a07e007005540701c0001e0403514040240f41d0429884c0d13000403c0139010850490704100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 505327077 1250 505325827 505325839
    0x30714032e0f06050c0f0d09031401090c0803220b040611011b0e1017160504090e01060806100602060c160f05010c23160f200909061b0306 61
    0x74550540b4140940b040e0000000910049451102c44034100142e1148001040c0600f60008085030020601c45007400054400304845540900c021803d5100107842504403002c2c001f0741da12004031075281d90080c40e100400f180010404140126403c641100311148091054039180c9003d0050361541c0046600060b203551b1558440b1600015600c2c0c40061811f51780e41d0756181440c00e0400c100d06903010222001c01044e080c2801180300c14a4040b45c201d4440c3e00e4404165004d02d20440c0d40341305070340150410a041040125210340d0541215040d210114203070344507035450f5a1b0201c1210130600c0748800581c0b1040205494407004401010881020308200107166090b40b2a0303008180ba082c0100d03580d03036442d5044400982e100054118040c00e850001c031443e003944140140f035001d04444980300c005d200c402a01002008203242c0105a480a00e0840d407402c2c1c0c9800c1d0009404d9240c0b11400b44c0711002c0040ca2070340000c590700d44100c1c1c0c1c0c209003031a440c0e54008900b00d290002040190004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 505328327 1250 505327077 505327079
    0x50408060106020309010314100314011815140712020717031905220b06060405120304090c11100c020f0709020903010e1f180c030305030714032e 64
    0x1810310919010b03040540055546040d0300000404a9441c140341480040500c001c0c02884005140c08030200d940016018540b954231090360750042c1405100000c0494130052010100318010214500c030012070766081001c224460200b1003819002c0390203100155825099618044040e4003030000d0b503000c0c00011002144407003500000e80e0040c1c07020801a00900c201e0001c02c040382c054164411000d0340141c206c1c0240004603c0008000d40e8000d04913415803000514030785854054400405000b07000d018802d004000d4035440c1e0f0312600030030743d0040c00e1400740c1071711901800c40202c80c4d0f0007100080c41c007808000010340082920741c5484007180188001c1d64542003007080f400d806005e01000050303a800d04c4070101401c6800b0114141407a42101003618a111030881c003280000354440300100c0c2e80c1240142c01d41006030401d600034420901b010b8003109040d400710165204656030b80344d00600c0206907030802d846000c00c40300c100384d49010310b20b005e0314031031100c0d800c50410303c10301c1c1080295 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 505329577 1250 505328327 505328339
    0x308070c09140406060501090b040302150d06030804090f0614131407020304081902030a0b07030e031204030f0c02061803031b0114010608040506060418050d080a0609020306030303010909030504 85
    0x9100c0109007007010b400c04a00740000c1c00860700c103e00051009082c414207030b034600940341078a40518800a4031802d00050840c051002072800c840301402118410448262030380380c540c4458120340030781c1c0d41072490904803c00481c0503120b40410b817540d00100d8a8034002c007070104032101c40284928040d69454601207813040c800411014050700386500555201c5050078461031800030240d6605444503105440c400150310f000c41c010150070b802c51602d40d00d80d070780d00c50305402410401c264484a4840090584100341c02c1945290103644030380d80d009030300d044000080f00c6681d901c2801035406082001000340440e01804108500100074050340c1c1481404615503040301a26007071010725944070000d121004c100c0081290150406091407059810981c4030305e07030351b41c80c01002640281d5a8071020014000c4020030309803540d600c2012104c0200c0203003001441c3d1a41500c03035492035814140c001c00c07500d005000f40e030711420000e0010340c2503a1800f10801d0103060504425800d0240c208008242 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 505330827 1250 505329577 505329581
    0x1401090f0e2a0319082a06010e0703090c1e090e0303090613050309092502010b0102070503010c0e150f040801091502071101081f09050603010c050a08010308070c09 72
    0x90b000d80310024040e004002c01001e08401030104038038441d0700b0182c4803249a02100d00c501c000c0c16002141d80703848961403000c025240007070701205038203003d2488040503034030700002d0114140c0390b0a200340100e5450341c503000e90507100740500042440d14008410300c0301d10641003150f08003140b110180c5c48020360715015001128424030344100d00307420010801407490303002c0040e907800c0164101005160b54540d210075442e401010005440b4424000c01b08441c1c19200205481202d48104101e034001c148a0001c1c1c003d01c182c694540c054004e1040000e01d520381840340c5940341ea942d884600c0c0012940042062800c441c3d00446107450b000d01c14092480e003664050000351503100c000003040b503450704080c605050014085100b490040260400040407143d168001c4a02030800340515140c61102c1400d41404c0c1080011800d010580022031041c0d9801c190300482081c0c00820042c03082a20480f51032280c1c03078a1030045802c01c1d00410003e4240001440c80c075000d00f13141c2c96402c0d200c0c014030342 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 505332077 1250 505330827 505330843
    0xc080f0a090306060803070c0e190203131703070504030b1f030515060f0f01030903030906051302011106010312051806030103110117040b0c0c030706051609091401090f0e 75
    0xc001060301c901442007000d50302c540c10140c9040d000540c02d0009603a03465115280c02e001c1d04401e20440e0740420918142c07014000005c2c180710000359107e207081d1550301450800c2c02d41c156050112990040c0c4442c1c4070004407801307440559074080c645425911603c0c941c041c05401e060300b04075280110050450710221001c0910301c90000fa016082141c40184945a40036003414440e0820801c003d4843c0c3c2c440b07024038900c1c4420f08005c0707a50441400c0039802030032280700180000b410241004040c82500c07140804043c401d88601584c0b4221548550759030509000080810300046040440240142d01901c00f410b45030000c680600f64040c0404c555420a80c412100310501d401e903250150f03084034040ba2003c0040840710340600d01501c03000da9400010300301c203902d00000904107108003801c0c421600038a40002092180d400c0c10182c45c2e00d010711441e5902c1c001001c0c00004500d0b03851b940100301040d46801c10329103550342412a1040106000401a603e00f6074644c10f6504115050050603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 505333327 1250 505332077 505332097
    0x6070c1b03030504080f010507020a0f05100e031c050f0a0b0a0f0b1c020c06061e04021206010e0604060e01080c0d0f1a0a03020105040b0c12030a020c01140c03070c080f 74
    0xd91140e20f411105d80c0b4000c460700301064243d0505081001241d40040e0b0000341c03039003080800c4034518107800c200c4d041510485c550850b441c18960700c0e4041704c5c0000010100c0c54074040803000c500303030040301540031500241d9408500050315404160311201680050719441801011280e007955901914800008a46d010a8004602203150703032840c2640c40ea0202000704403041585451040000c0d20349901000307141707600c100b6890140000d0303180a62090507158801400455071250f8030341100741000c03030448465000810122040e081030621a0a44045600316110900c44d1640640152160040140007500c1c00340b00744101c4030311102502490380480d1070350313400182c8640001001c41d9151643c06000f0301400a410b800c00060f41e020007242c00702c69907144c00e0350b25100704103c1641000c070082c8050440810100c24050101e01c5a8000d003071100c2c0060081104090070410445000812200b8640140701880001c82c200d0280a4104d803d0b44500d4102c0d10b05003c5410303645d40703600040008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 505334577 1250 505333327 505333337
    0x4060608010605060f031618060305010f061103030703090f0f0b150301061508060604030204020f0d051b0f03100305010615080f15100e04020409091a01050306070c1b0303 75
    0x41003001402e00c00c10029000030703140705180200c81ca503a809a13100c050701058090030180701c103400c0e2920607110500e800c1d030384240703055101d9a180001806080700313005400e113844012200003800b0740190a103540754050307080a1030550740c41ca24180d0080c15403500965851a82514030000222204c0c0c4411103280b080402c2400d43c1000040844980181541903010303030714262003030003910f02c90700d41e090b40c081d010300d020902a9102030215009004540c0025027050001c100c0040327104c01078014001140303601904100300d41d200400003030b12401d00e000d8009401810868843d104505000541e40034031511440601d80303550343d403003c1c00c4401551192604c11025008501c0390f540c0807aa007030300074034151000000c40c20600250300256140481c2c007446078551801040e202c90003072010712070b4000000d000f1911241c0d00c80c1c412000e4100c00c40220f43e140140441c1604040040c18064180d48000e80101220340e241d203010b88035801c00840c140c0f520303032810580300140c400038814400514820303a10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 505335827 1250 505334577 505334579
    0xa0c08160b09010e0309040903091208031b09060d020307030e1b0f01080105101b140c011b030906030f020705070b07140d020d030906021b0a020a050319060203040515040606 76
    0x101e4a000c1201905014841c0d0400b03880c00d0318103400100b65820036804840c0000c5400c824502a10386000592140c2102142c0d0300051041c4951200a1885034030f90180d4129411005454100c15100d2000016404030742480007461600d0a41d02465109403641000105181c0a0240c24a088d1081c20220246c881c034200b61005410050100d003e00b60782030030314000b0b40d41841c1c0021b4403012090080b40402070940b42d00a103003400c04000085440d0094040c0c2810561000c40a0700c0c2c80352000c0d61408149400c03074444410f0002c00f241c0362441d401d651085903041c1840300440140c80c1003007058000319024001100400d10034071459005080e44a0016a00c11051525401e07a22003480c807030040340c00406108172101d03000f040000d88001a40fa000030341d1b00d42490500d00a000345860502d0303130f4a29403c03002070b5400c001103507540785000b2101040e60344c0d5120101030b6203910102100c10000c0303a110071140015459006590014420f4065864030b058170006141c07070450488060700d4003074071100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 505337077 1250 505335827 505335833
    0x30503070b01180b031f091b0617150d031e0e280308070606030b010b030402040e0715140408120d1401050d020d0c0e1906050402090f060a0c0816 64
    0x3042183c6400c00c1c3c080c00200c0710140000c0e11303107004486a00c5050441559030390811020f90081c9290f41e0311400c0f50310120b1024054101005440c060400842ea275104905000d8040720603142c45940003080960041a0040500c0385280950740b0450034041d44142c0c034040c0142070b00100108040c190b450038401e408000400c01e103111405180150320058030550b8440131404100c0340162174125079056614002464988012b002d280e1002e07001c41c04900022840c10111001980168004c035410300807980403180341d584820311403088040307140805004c4030409000394903001e8000748611071070b800c0a58808266040084451407510132071000901418034528510400340d00c0d400307824023a011076052001103241c082c1d0080029100c1c9902030b21300742c204084520303034101a084206801c1e003a400d080000c041c1e01c811b4141054002401c0c00801b01e1241810310a070b40410b00010204c2403400c03850014000b00ba405030030070f00c1c1006054100803000c50300b10001821100100c03034080403100b02c942 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 505338327 1250 505337077 505337099
    0xa0801020d0b1f0219030c060507090306381201020d090512070302030906090303090a0303030e010b0102011808031e090d09151d01200109020120060a0213030503070b01 74
    0x5100c0361205010f600160031550f0020380e504d5200541c42c20100d040003e41006c0d40d49509072007004100c2424881003100050f4407402c10800c8a01c24601844444020310581e520510000d0b00d158425440240d4420361151140016148400c0070308040e42492018060a007641d0100b542e45850382c1d11650300a041040030481b025114814880305403e004581e0b8009403607100300204940704c0c00021841764540e039800c0c0221003281c0001401a01590b607246005006060b0a0213010036a52804003406060750046c0603d6001030b401d200c100d0181c0159070f541810030b410251003105020694040c880500c08503500d0140229000c3c1c0c001d0400949034030009094105541000c013800766008210070a00c0d41144100001076140341c07184008000803401200e256405000140000416072403641d04c814040d4040940340e8000c3c1d80780a120030400784250a2882c2000d0400d16039440300002500b2070920b036001c0c1080032190000000400d40d2511001c6c0b554014000940d0f01119900041114a49007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 505339577 1250 505338327 505338349
    0x30d030b01270e13030f0e040b13240f03060e03091206040507140904020d11041508060f07020303241201140a1b080a18120207080604020f0f0a0801020d0b 68
    0x110131041400750a0365000b003410940300381142c01d00511480c810100d0750780e07410452007174034043c16014044500310220701c0900f050f551080401c1c0351203910365140c0e400842000041e06d6401c0c60555040c4d00d556982001481203c0300d2101394001484800255510605e1504907501080028440c034241070a080d410641540d001c00414440c0003240d40c115142c0250740e0f6030103034044903415103140107410510030a010020b201544039240849102210200000200070b0394100f004651a99035440ea413004245000d840000140e401800001c01d0200321886511007034a650110703010700800c0c1808070b0108083c1040c0010030ba5140c51100c42140320030b1108603880445501e0500002c0810424803030170200c1c1e921910b080000c841c3c005403412803aa000421080103080d1003405000241c1440740c00d05030f103204218014041d05100084e05000001c14601442d00140003142d04a11030003040308a0900e03804480c7c02135014100000c940c4001c0c4007030a6080038114000c15410390700c1040000d000c0e20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 505340827 1250 505339577 505339591
    0x3030f150102070509060f040e031c0b180f040804051f120c05030c071e0f0c12030905040209040f14010f0b070503030106180b0a05071e02030d030b01270e 68
    0x98020031880c1d0f100e9000d56003010040e03d060501f01c1c424400324000e091884603086d12480006441030300c140c2141440f03500200c440320704109902d0108104400e406105558402001d070394400724400d251103203503040d0040c0c0b190903501d151a55941c0410005011411460704480c040c0c800c3c007072201d4004e024120341005141d0104200504100b010f04140405889004002400b048140070804404118014121081d040d101d12940626060030195584401202c441ca0500d1000800d818541807520b60282d054480c590700c00d00b440700780030080d00403010701e42d4465194030518602403002e105030109c0c01e10b91405440550f0416500c030480d0b00056100201c0c0d0b990801080000c6075011041c2d0781501c1451500702200703041400e40c0031200d055034001103c00e0308005040c092468011000b8140d140c803441031000605002c4005106040d00550042d40541200405503602e6100e0303407000c070030380f40141008242d040640300000c1070301030030f280c103060380400401d0705003c00d540000c800e81e0f01041e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 505342077 1250 505340827 505340833
    0x503011803050904020c0105010f03021801181e0c12051005090a0504210305090106050105030c09010c05160f080f0309030304120507050909030d150b09060f04030503030f150102 78
    0x10340c40d100240440e11140c003a08225010901d906165a0350301110703280c141040091000d541c695070400e1440c0503c2c0f008034400c3c9401c1e503269a910b103000050078100c41340c0141659124000702d800f0806031003210301d4049100e42e000706011000000344902c1d40c81c00c0207551810607521a2b84059011241d024140c2010075107404c4d402c009940e00c0c40030581d07002c45008008202070b1924541b00705e40c41c0072404440310458644940d40c42c5d141c5e06510403882008070300e000340186691384005540c0c41c40117482441c90580100f01c2d94411303501030303030701a000c4500c1001281c145c403400b100046100ea0b003940000d0120502903200300600c031002c10001c0742200304440510702c1d107046000000d80e01e01c5903100307403c40303030100070400c0040c001c09001010080c80081c181034120b00d0840c1100b0b0301c3c2d6118800041c07000389081c801311028901c00722a001540c92420b1003e2800e00090200070098014680d00f060920b010080440010000e00c05540114401007121030740f410070040074420425401c150790304542c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 505343327 1250 505342077 505342091
    0x120f02030c1c060305030f0a0801091512140f0f010605030c0105030112060b0d03081e061513210309091806090f020a060801050a090e0c0603060a0306050a090b01050301 74
    0x1460460841e04100c4816410301c02884041600c2d02c0a04219800a04940004640540750035940b000070100e010480e41c40203441d0f070b00c410044040301c06c501b400c900041072040c018064100c401061159150283d06031024003001218480c1c500414041c00e250031317421003016811081c4003401544054001100503090080124000800c3c03804140b141c4810380c1081c09002003800705551141141d070501400542107070308103090160600500740d801201e1030015142c0400c401914900f05070040c0c5000f010302c244444034001508554001c4e03c0c003494402940350001805900c0e083c2524564410248160040300d00c505005d4042c01943c0c1c0000c80305428440203c86041c003007050494881c4c3d00a000043c0000e131030401503081800603500030342220764950080f44a54014100c0341c125002120311000d103030389a15941090300c2d0b21000b08490344d440b5042c0c8500610b442806154450806011104c6803541e83e20303424151402a03c001c03040b1980c65845d1000c1c4424054000c1c054541540284200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 505344577 1250 505343327 505343341
    0x130b09041a130c09080102030103031806110a08091813050705120304062303150301050a14060d140604080a140406080f150301090c052e050f0712120f0203 68
    0x240320b2210b80100401d5882014000341802414003201500c00e660085444e5a102e29010749040140004034642c030860b0740c00026514488ca80525444100001805141d41c1d295207825950704003040040d4890780b001c0c8403120045590034528031400820701c080100047e0360410344c0c00c0042d680c001c24068a000e100300250628000122412036240d0301d04120b01e0080000c0d2450134a00d42040b00c0140680001070084132801c0c4045881c0c034010860003002291200e2025030304542204100314000794410001079000c1c580b101c80e8460703043c0140c01e0719800101322000c041c2814030444048500304008240100c51035030200c4054200c060084d0170901e00782c03c160001d0905003008143d249001c02c0d80000608228000c981b4002c0c4100140007800074184c0d600c0e003020044080e020b52030184105620340480101201d00d0a215001e4600c0700040501c4841c40807211588181d42d100000d40040100c000050a1150684134015040d41d41064204121603003006070360b03070745242c00302c207600510510401c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 505345827 1250 505344577 505344589
    0x62b0b010305090a0803100b0a111c0c0b0a0204050d0c06020f070303120c030e0d0f1202090a0e070c151e090507060c020a0f120b0c040602060406020708130b09041a 72
    0x104d40c000340c250303459985401d50721210050a0300b0070741e09094040380804041d500407012001c129000001d03541c208212032803800d0401140e00081d4000342e5485042c0010503003410855400410b0180702519003501c176804102c441e034a0740003c031900f80f881d030010403801d98140180010080501e01415201c1c5c40d54900420030002c0506c4040030903500e400b607140700350280e8820b182c48010342c2c0580e0a040103202c03024002c03214868405000c18882e03440185003200d140300304c50702628002d003000300d6203041170f00d40044403800501c1c0000b0b02256410310008948605800113401c140c1c524080761144109a620800c1580050400c40c0603081254140000300040f5581041d19418580f4807582070035400040c4032280b19606c80454150310b0003020601c10804101c1000c124080c802c840c4158942070f00c040594802c0b0300c2144010b030008000700d40003a600782c0003001c0781402420b00e41e003484101c0d03014040e1800203a000b15041e2400060300c0180d0708180c01503445002003594804400c4483c01d011800d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 505347077 1250 505345827 505345843
    0xf0114060405251e0201021c0b060d020304110a0806040b06191e08060106020f0d0309150213080607020a0f0212120a051305121b062b0b01030509 64
    0x1c481e948802c001010054100a0382d0880c010079410400c00008040c0082c003104c145103402c685580007440b00c0c00f04140140200c50300240180c507808142610041040010b10b6000700780d603404501001000000700103400035500030360080c0340c00c050400a02c402c0040d81022540304d001c094112070f0400c0045000d00c03205550145044d0b81110310039164195072040302e01e0503000740c01c5800c288500762560845820300c1c40183c40c0c030041202d02590300c611059a848250307242c16500b9510451504820038800d42000300b0180c4a0701e01b400c106501c3c00311460603078000410061280324102e00070041200304100d1180c014400d400982a020610b865006074903a010201034083d10303141e15000075418042048400c0c40d14003480d119110030030800001e01d1030303114a00c8200241144c031404a55460a4500c00980380f80810041140c0305040c2c15180301003400841c09a8040c5061241c0c0f20b680c80c00c0c9202090396040d80305480020060713580034004482e02090800c0c10945401c08000c68520006400c00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 505348327 1250 505347077 505347079
    0x40503010b0a230f040f05090c06090a060e01050412030806010e0411041202060705031308120a051206120102030a06051207051027060507050d02011a0411040e180f011406 75
    0x1030b40040d00b503c0801d50a55010005540081c0390295868030040b896202c2d50140c42079500b51400b60002d0001c010071802850b000d03a030300012160003001024080c420f00484001c060511078141551160700c0011501c2c000c8040d0b01040191003048455a403027104c1403240d0804940030000c40400d83d070846101e004501aa4013200c03010510f11080d503035680240d0f84440d5101080340d65454291042540580c0d07130b8400c80303040c0d01c2807a258405040d894000d8911004036030381c80500307000c0e00703807060347c0002400b41ca085d40081c0e01e1103011344c0701d0001380015845407002d0b40700030a004d89880188000f0412010700d2900a40144009008a0340c9540301d02c500700b4039500c1c040c3c0481e000c0300f0b8540d4078144040c5030080c1410030b0400002d81650000041e040b4640510140c0c1c60040107084181c1c20707a0082c440110340807030205c80524681ca8144e10102c0c3c5402c4202e141c500f0940c40c0d9445440d130b0038003603455844206c404504601d4200d810010900414101c200074414100c03078014528a2030000f40540e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 505349577 1250 505348327 505348379
    0xa170f07060f1b0213060e150303070627060c0905030f0703060203190c031b110604021002030706020c2b211803110106060207180903090e0705040503010b0a 69
    0x111103802040580c504003d0b070001c2032010f46500001141d8014601d5200d0721084591103000a4601c0315030841c104451f1001a0246103071140c0d90340c42500400310408440b60740e0060350700800500c04802065010188214400550580344100203032007913015601407440b135400018400319851010902030101c4e90300010250300c0342c48140000b940a0302c0280080d80891528088004030766043c1c110324445102d00b258000100c1401c80203d40880c42000203031a0303a40240042401800c16101c15110401181b06503030a00140e6610700003642e20500319001d00d5840340c16243c0408003107909100e84040b01100e9929051111301014140d0701d0380c071740d100409040e20550903100d0b007055007080d0744010020345c3c400c0d00015545009801c2450200811589601e0004089a1035000080761000e0f10380f020840c61381c203401e2007481c00203007089803411001c120200e0300028400c48920760f110700502c09601c4070368070303141008181401c44041e08005840f0351252601045046080c030b204a41d661600044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 505350827 1250 505349577 505349597
    0xf1c17060103020f0f03040201090906030203060f0a0b0a0f0e0106081b0d090b090a0b0f070228060c0809060714030403110a290c031b03070306050a170f07060f 70
    0x1a0024050010744c0046141e0004061459030b0f4814011031049200341c03240800e060b1a640058201d9045000094055100b200802c2500540740c3c812984044803000200d204003000021481e04105648050f20b010f90b001014441d40c0901c0345c00d2030140c03503035181c099032914047c6e0f904007054038558004030f03001c1000036001c19608465000718490742c3d0480000301d2a41081c0d08415503d0140d03620580d20300755114049107800725440c0411340584c030340d68001c0040c00c000a810b41d2a404200d00f507003444001907281800060458011904000c2481d00e0700c1c0c160b40303451030400d42424001017005080180100700e4820720408941603e4000b501481c05c000700040c508441817401280c441c0140103240c011040595901c50b102d503543c841c1c000e42c04400c0c01500d44090603001400b0641d0b100da1030041c3d6107007004807981140c2c050f544c440d110740340100e22941c0c2c40300820800d070080e4001e00901d050103000c03036a1040080004451241c1082d00a1540c1481c00400408081048010f4020001c0c9511 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 505352077 1250 505350827 505350829
    0x17030a1d0306040804090b0411030106030213090504050a020114090928060e0117120421060504060504020f0d02220b040e070815220204110304050f1c1706 68
    0x3116041144054112112070901342040c01e42608140701d110119814501e1441d0907061500a00c8802041c80e22442d0a60b404d101c001c0c0e001c0d4000da803100001207582080084e2070a142c1c014203001d14000e102400c07220074180001800143d088043c001020000c0017101000e07103400c1041e6920101e06001c80d10030203200c00d02031039003410445800d00350504144001c1041840e03001518100c415140d1403075482030007082ca00740c5a480551603905401c40c24803080090394031022684145104034203100b00c000c1101d54481088603001d403801d9803441e03520700400c421800d100d0000145400121222544036070140e00145070754045008540244880d20f649400740c880603040f10902980080091080e824803513030351342d901d203094483c3c0a6184205241c025050201c907403403070b0280140c0d0b02c1054004002d4143c4800782808800101c0c1c00668643c020030180304000085d6004070b208a01901000020140040c9024020400200004540c480a0201079000ba04120810b038040000350502d9942c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 505353327 1250 505352077 505352117
    0x1e04140603190c110a03030e160e01090f06170c09450109030c15050702030f07051002270907021e12030115140a090909050709180c17030a 61
    0x11804e20058840c00a08004058040d0040b81c3d000200307004584440c19600014001c00045110f050705c2800090014082c08040e500b140003500c00e04607000c664582e482c4004002c2c2d508440c0d01039940d4101090b444454600200626044035191519081110780086146140960b035003558000740100649100d640542e04e03400001d00007113900070440349504d8100603166003c2c041d411a01d030744e4151945c64140d01c0c240700d5640504100d034011400c241c2d1008003141c203075220f00000e59041c468424605826050340c00101003001c544650759441c007103140880c0e2a4100d40882c1c0c42d104114900030404c1141e80010640c2c503a202c0c0841c1c80010903000401c050400011034101c1d00c00060010000c1040c82500c40c644201d4459075403140d10410619080b0320781402441502c03000112078081c10803510301399812905105001e2400e37038102647d103030a4502110701c40d0210380801060340d0b03901018020b0b480c03135003001440040380c0c2d0140d14500d40c140d691a441541c01c00000c0c00702900309180030070448 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 505354577 1250 505353327 505353347
    0x705130503070902090103050903030112150603050d050c0d020d210b06030106020609060a110712020f010f1a0a0f29120a0b03030c0a0b0702031e04140603190c 70
    0x181c161140c054030350100e080a58010081c503030109060801003215441d001007100d0407210803041034500780c481350362802000d58441040300059921a800070012400034464040070b0061920390f59650551030340103a040c124848103203c15074004010400c1000c1e082075804400062146140b00d5000c46408400010525003d0207a040b180100010840725000282d180c0503200c040d0840e019656100010815104045200d5039403210074011200000d442040c2c0d046040214016a60010b020310403160071214403a03541801c543d02c0300200d03c0e10600044007501200b505a031844219802c203c2508101f09292003001c414803038a843cbd1a0000b0b0503003d185c4040015a51640c0d6580e02028070413000c41419113441c8a0203250a181c0c140c01e150000483d01001c2c5490042c01d40c000c00c40d1904071840c00d0003000b5100b540401c1022441400844171800112511144180d445500709803011806120884100d40960020001d2205219145d52481016072020402240d4004296821100c030b40740 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 505355827 1250 505354577 505354579
    0x106230f01050c390405360703050a0204060f031505130b090a02040e010c02031b0312071710030b060f0a0815090f060103170702060403020901090b0906012a020d1704150207030b07051305 82
    0x152048c044100080032805032038407402140c0a0000d1600da00507a800f07081288401000c080d002c5118007030050326508043c3d40451500c110580c808541d84403014210401c9a86070541d4100548140c21881c0a2003a645614031000081081035a544000303076803071217a000080c000844130f50030501604020412211501d04080e50301030075007071001000e0443d444031050306d20030041d03010009158403000750641040b00c0d0848202c640c0fa4589000348607681d80e040c00f0f499088134000d0004105040200150b1039011101090050b8603c2d01803030300740c00e04500907000809030b0090780041010599a82001400c1444810f0455962500f0300c0020f00d01d01c0b49a1009400c050702400025900c030003a03101d50001c400c10744042107642e0320304c2c004507a092010341c0b410410140d545601c2281c60f8030307082001d542030710213425146079981c41e40701d5418025010059800b401c80004051080b280b1165002c61441c08c64001441c91504664a0f4000d42030000c10381000c020022402140d8a10344000400003407034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 505357077 1250 505355827 505355833
    0xa03150609110403061404020d0f0204060b04080309040e0f061807080d2006071209020102070503010218100906050d1e06080106230f01050c39040536 66
    0x182458400b25507812600c000e03180c55150103038181d2010090381d45288226801400b1002264081e5150b0710050f800900c246c0e0466a55200403076050440c8000f8400b6050460056494400d018204015504145000c00041d00884248485602c3c0003c58580204a002409800b0300402661501e0308006501071042c6d4811500d01c07500250300400c0808540f201c030070710b00e040e0740b0b04034000c640d541c030056410b440014400c88034000103000c0ca030b21500c040b910500c10355100565601c002801d80c1c02090401d848440709400b03c0c102c2c0c1c9060b040b0881507007040d04020749080d162140c094007901480307205001d1203440c1c80828012080d40500c2d0304501c829004100865500c5192050092085001c1c0c0e410958070010b0951b82011590701d10518070074010034594045610b08011510b541004031140250301c207419011140c4030641321001c0c0c544100960f041c3c1112010090100c031444c007034001c28000d038642021f211000e401d62024212807014000f00c40609030030714114003104400340580f04180c1c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 505358327 1250 505357077 505357091
    0x60702060c0d090501031b0c0222050c030a0507090e04021c150608070b0403080d020f0f0315010806090906060d03090f240203090a120305090a15030c0e0a03150609 72
    0xd900301d43c0300001d5030b800b07903410408484000303528006046281185c401245524190f00014600400803105510039a21120041c0d1244510340d401e96509580f6581c0b908800f00420054a1040c41515400300007481c1221402d40303080c0300c00700140350252002c0c1c0525844c0ea80204102001c40500502d1a401075086189500c400410310040244e030140d000e950250040c00201d9006100c10348050302d41069007545480c107005444030080d48550381812139001d05000c010300e00c1541c840550700c1026400341509142c03030304000042040c0700c01000d25105201070014411001d00c0012000e61208007602c00490ba0011414140c0d900001980000c00304092028046014020001c0001c81c0c040ca101d00c204160492001c180d860f40900841d56420000b00c2400300010f00c02c10300c1100000e4002c0c2413980c03400725480c000c41e00000103a0001c0c4032990140c180002015414480c000c08440c803072908141c6126010b00241624180344000361140c2c6030720704c001d10b070f0b210140d211034003c0c407590310200581c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 505359577 1250 505358327 505358353
    0x339061c0218031204170c0d120201051f0504020a020f0d0c0b060a030203121c09060c02190803012606130b011a0301060c030309050d0801090f060311060702060c 71
    0x40d40c0007400c0040c00342c5904918007210304000034142481034149002c0c9003000d0820000001000540494071218411030000c011982c4403065004c00603406210b010799440c83c0078202909541c1e02914800301c05806454040030782d2050790015007514411070380035a81c1c0b01c6101080b440c0c81c0c1061081001d500582950008442e000074418109900c070782d0040185598001c10010140364900c80603400d0303004000c140001040740b00003018542c0f91a520a0000d402601c0d5a02c12030b80c40d50030803102c941ea204882c0d0702c160b40400018820303144810889501d40001d50350b40c0007a00061044140802c041c0f02d21143c00d2f040351142001a40c050f104999440c0b8206030b080f00840441c8109545480741c08001144011051144140398441100000e01d503901e481c07003c030796441030124260201035980f841400050014090600700038442d03511090154140301911085a50024103000054075202c410000103009040802082d541107179180c0d00c80d002400411414450684040600c1c09401000502 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 505360827 1250 505359577 505359581
    0xc020102160e1f260f0f0601060909051501030e031204060b0a050312071b080609060105040b030114040f0804050a060306090522151d010207020339061c 67
    0xc1020b2164142d0a43c1042082e010040b00c0d61340103943e01c0c000800d00505000701340100304108644040121005996104501414254003100000e00d541000004124466100d40c900000e0007100d8810401420018103010040c200b000607581803640310803c4410390201032041c0e4041c0a4001e07002a040c0c0303414034040009010f0500b08600c1103188241c042410f00f800070b41c08103141d040c20900d500d86809074844c19501c104490044404840101c4003080b141024042c240c019108180148840d5062108000a40f0024814135000340c0c90a61980380e40b10200c64801d4100303412115804000d486410310032200c0c401c54005580202104000065013030703160340a101150072048003004180c82e900300c03a452242103000780c504031900c40b2680c00045003002c044074803a4080b80100158200d92401c0c104961341d405481c07042d03640d501043d03180c1903040a20180e640802a0a401c2007040314800f5281d45000c03000450504011186584d03410a8036004110307880101060043c0c03e65200d01c10203c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 505362077 1250 505360827 505360831
    0x5090301060b040b0708250305090a08120f031909030c110402162406090c023f0706140618061018050414100b130302010c020102160e 59
    0x2020350710341100010380d030741d88030300b5141034600b84010b5503d4800992240328054000142c4520752884808100d00010302540d4a500013a2080e15091745501000c030400c403045000b6800340305607030407001d0421035402c150780440e45c15a24035013003e0f0b22500c031128054103001104026805c03207444c0400007400e0640021400b05510701c5000c161582c4a941c205103c242c0c0144106c00c0210400000c1a4000440d01c003d00e0040740e48035407541018442021403501668090341c17142003825501c10700111100c0e17041c0b0085400a03405583c40004400444481e128400c40d008410300014400200030030b810b06000481d0b07421794019105001100c3c451050501002090707031414818240c88180990b03800c500300703142c3d114042c020406c0f07009410383c490a0710081c80c4c0310781e43d0815025411021840c0d1341e881c4502a080a0310341801c0300c0302e141042604007035000f55006414003000c1803042d03074114600e4034085425a40e0a02c2c000c0002651440141e02c1e0102251280c96001c200c1d150118a165038800c03114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 505363327 1250 505362077 505362079
    0x60b090405061015090e150d0b190b0a0302040510090204080d030c020109111c0b09030d0c0503090601050613260709090c0311030f060a050f0a0b010206071d100509 72
    0x81c120b680e40c0644003940740c0800e02100110705e458904003d200b180424007603002d2401c0d811880403884c80b40010350007140c0c00e001100d050f20214103004031141d80185030700350040c00780c0301000b10003642c400084d55800d40d440000c1c466a242d40c0081c23250960300008000421342d40b5025500c2e80d4407000303196100c00000b04401c0002c0d02d0800341844203481409069103540d080041d001c1c8102d0380b0800e110f46a58941d80d40e01c1180b6030041a5000102c0103c42688650007003005540c403448800125425a401d0006072404c0010600a000c4a60008101141124000c40d41e41d0f42e90041c00880034007000300d560101b49005200809445083e841c101c3c003140e09105001034801c150b40741c20865080310680d94003d480450080d00910005940303102d80481514003d0845903c9290400464070300324040380c517030050036151003e01c03074140140d0500b2608545240002c0c84051500c000013961404018010310400080f00c84407007022190b460144840d54010b404000403165421000d481680076003040303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 505364577 1250 505363327 505363351
    0x1e06030b010503131b1e0305060601050909130f210207091a1203040801021c0509030f0f0a0c050f0d091509030311010e060f061f1b060b09040506 64
    0x4100541c8144103c1e0b209090401c2c44200c0440e0540740c4600d40030103018006031606201c1d0020800ba5240c0400c5141d442000d01c144650504510b015030401c0e00180101d0306015013071007010b00742e1b6510100e5960041910400c480c1c00c1d545800c140028401030704024003181d56a0782030340d00018940c0c10400f044c2c0c41603021101d04950b69141041220410500082c090300d00c98107042c81c61800f07400724580c02d00c8050403a801d15898450a072f08a0b40708a0004981c100301510600e170044882c021158481315120185050a1031800950030600c02d0801c803101c0c1e05000202d5017209030144481000e000d800c8400c468030b0380e00c0c4125035503555003a03400344008120b86080000b41c1109500c440c0640c003a00b0360300c2d0b4413240d2440d80d069442ca844409100fa01e95281c0c0017000300c04d0000c0000e41c0c41804808000d00103800d286040c00721135880041c512811502004000054942001a1040b4245440d05200da1150720741040402480c19902c000c0c1d0248083c0d0501007030100000303074180100040040707 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 505365827 1250 505364577 505364591
    0xb031f1205060708070e120c04052e0b0406030903120912031d0d080603070e0f04030e1c1b030203030315040b1f03020a030f091208090120070c1e0603 66
    0xc2a03031302c02e40c1103c03007030005403030444d01180340d003040751100c06102d000c0000c40e401104803200090030780d030341200c0255240c5030b94896052030740203480d40807260700b0120b89440e04541c1005112040d034410384c000e0b002031648406c0443c04042c400c1c01c5000400d4000c2604105032441894030550011928112900190034030070500b020300c103404500a15040c0100c01004101d41e4480207aa0307180700101a10341c140941c82000600e01d1002090501c40c1883c3c1e003040e0381c507152078580a03100d904a8001d050140c10b1b500e41e012140c408000c82101d035250403505043d5000c590285600300d5103030a410007501030002006104044040350b41032510144120b0702444202c1c402d60500c1444290110154880c0300011401a007603401303640100315402880c41c01090710105064038200f40c07810710390100c070310351140440b8842207644108200c0d04841103e00a00038204a2200011340c020010742da000703024000107601040000640851005182e0b01d43c1d0540780b055047d08002c8418064450b0f000401c1c14601 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 505367077 1250 505365827 505365841
    0x3070509010c020d03500f0406030e0610080d0c05010e01020408010209180f04080a0302072004060f0f03140a1a0f1302060f07050703020a0b0c0c0406030c0b031f120506 74
    0x111065004401140d21290750301140300c40081000b84800041ba0038408124a4448420b484014006032100d80c40100322510740b01c881500c0c002005103842d010b04503009050102441c00701c2d000203403c00c513113040b406807922401c1c0240144103c040c45010f40d03200050006042c036041d0040c2146030000c071844880300000700d0302d41c0440b080885203040400d0a1400081c005801c64000d00408e84c583e107070040c10003c290391450910030740c103d03d01860403a0742c08042141d1500e80980e40203403002027480000d0a02d4030142c0c1418404501004044401c4580070041c1c0542c03c1000e01d043d65000b0420400340707107211000703080c0a2410749591080305031460004611000c8030250080703156020b40090710303084003455545403907000705000711030034054100000050f81c2c580301d4280141c000810801e80e62004d220a5928059039a8007080c0501e09000040000c110100546822950a84172442e0350baa80c40d06c43c2840c6c01014a9400d5800180100100d490354078903000402c41441182100d00385c1d12000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 505368327 1250 505367077 505367147
    0x150917010c050307140903010f02122406070201020f010c090812030403020a0b13020904081b01060302210f010603240b0a0b0903012d0606050f03070509010c020d03 72
    0x416540c082038080001c070f690584036465201e1148580103174036042c12038940009081d038a1600360a0a21500880d60813a40c1140c0d03048280c10045c21a14000d07498004a03402c2c0c0b00e103a013410401d218510104452055900078002c40710a20320010017000b509080d400060000d00e500e0240090b18891144007050b070701d440340c0499010742d81640040901a480340c2d240d95440c040202000d40a030031880c042d2006886580032280100d01c100030281d25414000780c40c41e400e510341d078030001d5030740c0c1007070410405a201c4101400c01070340d03512080741c01100b0582d0302c0e919180444008550561074450000107006400c076000700040d90901a4041c42104950b42318251041c2c50700c203e40c0080d030520100a0140d0490040240540203000458003044142c00b140202e88402c4010a15002e025106404c40810344505005042c2b0f42c1841c509000f903410b118095808020055001e000f0002403031861030780200c9001c4240740c2c0c003c040c60504081440c0081080c040704071003c880200703a074003018a1139501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 505369577 1250 505368327 505368341
    0x90b070e100e04050601030204080a06050103140a0b01050d060204120809040f05061c03020f010f05091606020a0308040615060f141806090d020a080610051009050904050715091701 79
    0x40d50302c4169aa8401c41000028580a0050ba040c0344d802c1000080f0102d050000303112444c01303000e0004403503156082960301280034460501e0140c01001c034001c0002c03081401c090640300141e800e040510098502000248229040003c0300f06281d1804010071410b4801071005030401d55040c044200300680750801c1e80c005942c82540030510500b004000c402c540721140e0401e000c5d02c126031740f400780304043d2405c5450172507407410a15100d00400004c4982004680740c000ca40d0f240074021700b458600000e44030010000028200284c0340b000c40c041c0304d60340e0001003481d003600c003010140907940e18000d0881b1600c00e1001020601a8942c06d55010b01001035034400c0c0b0040050705107461300d05040100691149203c00d42c040c581440010158403124031031b0024054000040241d42020000c045400040b03901c96445a0103110714048900e0303028205000b212425581b5002c151560712f416070402840c0d4110b41109081781c072440308095400034801e02129500c0c515461f82d03c07d90b404103800c2c0c070340b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 505370827 1250 505369577 505369609
    0x7051b01021b010c031806050d0b0906011b0c05031b0102010b010815042a020304080f07180b031906020406030c02070e041e121e080907030308090c04090b070e 70
    0x507042c4207a007294080d80543c5049840303803078140e50b21040a9030b21000076641e0b1b0407845c006580414071a0041c40340c0e1084070394524040b9010b01c01c40c5802000200080c82d070b104114a4200035281c80410400745c02c100e4000b40c0700007406d6030080580068014980d8240b29a01030042d0f087c42001d016550051783d42c240500e80350301d040304912040d2011300000d0000403030f40d0003104c81d08200003585504a2048805044081d0f40a559140e1a069526140041108541c000c60f008040104a41c0c5440c14441d24090240ca01c0440c00c00d015000107810070365400306001e00d188840203650104400340c2d0040c02510081e0310100043c10701c2c01c0c0700302e075101e4a03805600c0f002c04200001c103021420b050b001d1400c01c0d602c001d81080c0f803035413a0f03100191f040071810000b021442e0400c1004100000259965003122240b800ca0303101c1c501551281d5940c41d151001a0606c035004010035039500f130502c410038039800007500c24400400c0710b113004c00040404592003400a140074120100c1882c240f08100b0f0001d030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 505372077 1250 505370827 505370863
    0xc090b072307081b040c02060c090114071505010e07050c0307110a08100903020705010e010215061c0f060c020c09150d0606080c0a09110d090c0b07051b0102 69
    0x1031a00311541652002080c101c1e2846081d200007031954080240b409021032036140706038007440754130502040d00e2052034a00c003590071a50402946d400352000f9036050f03100034604054450381c3c1002000d03c40c41600c0b80030303201f9040100c0c03900b0300c0d01050f00405d0490301d10301607007240c55885404c1202e65003e9102004040e4008001e400042250003070703403041100008212222950392445214a0710f02d42002030709205d62110f0040c03043c550144250760085c4001e00b0415860a4200700003900d074560b852540c0c01100c00880410807540b00c2109101040190300c008102001e40f40c100f001d00d0800801080301d040d030608102e1050301c0c4c03000c11307400d05558025280c040561540b04c08440e010000540842c2c00c42e00604020703000c19000c3c060722008142090103003442482c2c1c1c1c401d02c0600c1100c0e4000c1049181001c1c903684072842d0503402c0720a400c21078a400a4400300782d06c1c20403000034490b031103036012680200c4c0c24028804040344080034ad41c081101c5800d190304803001a0b03110704008000301d00c004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 505373327 1250 505372077 505372103
    0x1b1701020c210904020f19211103040212072c0a0605090408030a02070501050f010302030114072102070f032f061303030b030604030e12033c0a030c090b07 68
    0x1c141070300640110503806d00c5060800000c1c20544140f161440f52120000f0340300304034003c2420860402820340400f51100740420b5000010070341032840058002401040c502202070200c0c18148880c0c40079000d800700000780c0c4d504001c1c58113442c201000c824258840240089019151103100d860700303d640c05000c81c1e140340d441d611011100e0300020038801d8290340070064100040d03000e20540307200704c403840311440301541940140341c2100e0344092101080b90303104c01032220068005103119196000e91004051007080c06a06201074028854001c1584d00c0c3c0240034410150003c5412200c0c808000c1101d0001041e074540988040c0141280d0303849800c28408502029981195103141c3d50203800d0106000e20b804020928141c8111816030000d80244100c00d054507003c20204106010000114140b02c02e003290030030f00004400b100b1130031f80d011030a45012600c01c2d41e540042c21f1096100c00d91034030721101026010b00446500b9000103500751401007121000c14054410503508000101c043c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 505374577 1250 505373327 505373329
    0x190305100308071b0e01030c05180a05151906020c15160309170604020a08030c15040311030c150105100f03050613020d140a020a08041b1701020c2109 66
    0x1070344601c3c8290349914030991144038021054030601e0003021000410140c0d5895800d03d40620380c22500803902c290034461900c90456141007403103812914201c000245601c98501024000152689454000b201c8983e4100340800140883d0120754071502556511140d500421003100c1e901422802950000d002d106001c0000044040b807030340c441d00309441440c0c1c6886030703140703441d0120419003550b44c804401c02c003c5003809150700d0300500440009505002841401548070b800c004e24035410031060a0004042c5440340e08155128042181560360301c0d0380072449c0c15101d120f909520b0708441031400001031031b0f040440c40c5890b9030b05255101e800390706203080200c0c090701c005051705a11548540380501d80303c045100030201c0148034440080d0400218901c1d01e0503a0000f000004080e2040c0010907020343c000039400e501c20752101209180030031940d250510881030343c0040d1a2030500e900d01c0d1100c08415801002a69134003011a803048100c0f02500c1481c0c3c5643c1030040492105005075162 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 505375827 1250 505374577 505374593
    0x40507020c061207030f0504061d07140d0f02040e06040c0b0f0d0c02010617011a0409020a0302060a02010e0106060906110703111c08030406090b3402010b0a0305031903051003 77
    0x55801c0c45c01060880310204180207550064400b0742d00203640e02a41004603840e8801c83d0110000703000540849458810011301002003045480e004011a1820030104500c04c02c40d04682d13a0f009004206020310b00342032541d241801c90b41164652172000020405170103403000e44800c3c032810400c461a04040b1031b0030802400261203600e0556480d04804500b0000c010703840c003194840b0000010303840c0f003480044000d919982d01034500070b6217456001c40240e21080380820581e42c047d21001d42d1034215040490050100b00d289010381d520f000404108541c6c0b186a0a085508568840108007800001d0136260503403840f000f45028103c0c2060307100346c204101c84c800300080da19208002240a03868010707195000321750484403542e48840740c200b0008801841d07a081203601500390380f4200d5140b04a812401d070907040c0d04040801e824240c80041c07003500000c1580030041c0c0401800d82d0b0380c0c1703440380d0380b03800070a141202810140c4001c81030303500c40d00c5124440e14150f095031143c14559150048 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 505377077 1250 505375827 505375831
    0x31203060b1b0a0209090d030b041b030e0a08190e0f010e040e0f0a051510030b010504020f0d090605160f0c080901090308030106081012020d110f100509040507020c0612 74
    0x280d82d01540c00d03c180565500e0404a210b08000005007041a0340400010708031510903011a120300c0c41e14044802042d62a03441105500c820309002406820301c0c0583d902d40104060001c082031000144100f1055800314144816038a40d119801030248640410169049031070400f400180b440c0c90740e94851a1030382200a8a0102000381c51844010303c0c0114141120341d0742c161841d5000004e9245601c01c40741113242e114000c08441c0b441541990b41e400444641882583e1050f07401056404190255204640800110300e03410401d407060b030b1030910041c0404489101700c00e2400015000494000c602c403c500d061196503407200740751940d480e02c1540d0000c0b03540b28100004c0240210002c0c83c2180218080c000f0b903159000e040c50946e01d040040102900400d642e120141052001078035158121080140c1c03003421100c6008610001c140c0c1810710009141e88030400c1002d070302d19140c01c500184003191090714240700d41c1c0da40600036655004501d003040d4000604000315000d01e044144265 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 505378327 1250 505377077 505377127
    0x120414150910030e160e04080310170d02060604020309030a1d0604122f040f0e1f0b0a060c03120e0a1a09160909150c09031203060b 58
    0xd04111550703020411110014061030042607131519184503802d4208900143c1690202c4000401410184c110100d103402400003030030300d01d02001040d0145072a80039080600542040d44910307640d00d10410756100c94111189000d03024480115440e4101402103e01c11b2442e10f004504cbc00d00224800c68001d4041302c00408130f4038124000c2d07800d075502d040040000348545280050065824101202c50407101010016070580304100514142032030440d0104190044400040076a40c101061024200280c44500640103e0f000030307030041c2c20a0070b00190240d8440e0200500e000907020b02001c282c00780500c1d0017080344500b0b60340000c1c1c13280d013108084d03020007240410542c0410b60810300d0510703200c1c4100d6040f00d0b10140d41030103424102019030b001400c0d800030415161025048090710910f0700500c2e206a884900d6107080c82483c0300990840d01300410f04002040071000000e0003010103010860703c000c0301a81c40c0000e03d109000f16019140c130501d40e40d2402103070030101245a200e6611078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 505379577 1250 505378327 505378369
    0x16050a03090204020c01020304021521130b09010e10020405060f070804090203070c0b060409020d08340c050a030b3402150709080703060c0201020405030604030c0302120414 76
    0x1100141c8440c000341840f40301c02d0001503100d08043c4100111400d1100404078035060500020180c02451421648a1540340700360141030380703c2418540d1403370100b41000c0d04200c41a01401040d0358154041c0d04129110030070344120300d1600780054183d1180744a601d500000071302030740241e011081c006144140c4a40150307441c20750303501905000e07130300304a0b00c80e03001c10700a10320f01c801d001c3c01c42803056200700e00f150b08000461040d0300158541568a0000e0b111050104000302242003039400c00300c045500103800a2815003101320419450b4601c01c003200c0791042500005a0741c1020503400041c0d9900858022042d40c404e030703d44081400a07a80b002d40d040c52600c881c4184000c803650305400354200d9001d0601410902d9110101c910064001c4003004440c0c3e40420030120081103100a40303038400d00218140c262600101e000e0b00a54000a906002e400140001c050700b002080701c0f910703c240c00342c9080100743d05402d511030095200e1400050303e0b2003510388a41c60010180c51701c101c03000d174030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 505380827 1250 505379577 505379591
    0xa02090303070507060c150509060a05060102101a030f03030403090b090409210e0609131e06060512010f1a21010b070b150d0308040618030306060f030516050a03 71
    0x1406103400005d50000b000f2880201404062000c200c904055203080c0510600850800700c4e0010358030a401042541c2d49503898010032150781c400c0c0318080005600142c1403242c50003c92700300c06480700340c850aa1113441189800c060700500030050328810f5030140c41d0f150075203140030210100c0364042c090b80d680c040d41c0c9030160f50000d6211a41c5408901c0740d0625080e0150b01d05030041c0c542c0700c00c030103c50b208032410710481c9915564110506030041179171401146515440a0441014441074030071a0701504000010034100e51001c0504611a24000907440c81d980c0c4920101d03003c1c0710350080305400e44076070686803440401d10000b481c402c84402d441d60005102942e00d0582d051083c1c00400f00340500040c24814050314415450704041152074400e034800300a80042c0302907107184002010b001440f000501805500d82c80204602500404c581c1100c0007450020000c003102d00800e00450014825088468032911403180b0032a0310184140c0302da10054016600c91708000c01650070140c0701c00c0b03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 505382077 1250 505380827 505380833
    0xa110c1c0804030204090b06040b01090308031b1308010207020310060f03080a0203070c180c02011b030902121504061a030c042c071a1602210a0f02030c0a0506030a0209030307 77
    0x6c80e080216024004104140c2014800c020640320f1b050a00e50410030041d1040c8003080c90b590440b5041280c0700c0211180c030340556604070342c45c010f159121466446428000640060640040446078800c0b030035621100903005503002128994010302103c1914120305000103480e9000038010481075004980c2840302c0b982c0c1b409500f1201d9080010801740172451405941402d01070071030385110382d000a10820002c8900e103518516490381803410141c440381c0790015900c030341c0080c01e0030300d600c58143d0f039646600000c083c41820081d1801c65086280201c10106590501d009402420b401406000c007800b20008020240c13402514050620031004100352412520812030034030054a08050803800d0300d0102c02001021000c40e4140140b8020070401079009804014081c11640c100ea111640903000c0031980e01000540e001c0150320f100d0b042490003405404100b2140c1d0510890803200e10b40140f50921000200c40d00c00c07182c01c018244041120980680c02801d9540740c00350481c0d0501885c1c0d2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 505383327 1250 505382077 505382081
    0xd0504060b0d030f0206091212180304080a020a0e0601080a1a1903060c0206070206070f1724010f0c06051b040f15210f06030c0b0a110c1c0804030204 66
    0x44100c001c107040562013000180c05014050340304203400042c119105000710800c659101b00c80c054481c0c400303c10001a505c2140d80c001241150444003140e031240e0b2903031881c2c0d950302000502070303218200710500000c48000c13601100d031241d40107079140400354550000f0381c0d02402040350001d400080c5036010034a161100300034003444d20000310300e4418261550611030110798002c0c142104540041c41000011500000c146170003410500c2c2c140040030381d011084410010301c0704c4440c3c1440b0082d042c01000d40040000051603080f81c003600790303044400e034019a0352250711a50b05c404240303200940ca002c900140c0c0502e500c190300310f003040072500328850b5040d55503001e90080b22107140b40c0391062100741a11005100c0c1e4603080e05140f018070000c0c985141c0c4250010075605210390300c1d000071866440700341c1c01003c01144d000740e2221045440e0707902042c02d50840580c600c00140081d205608c0903d0000320840e03101000b520007600c85500b000030110524514100342d4a4440400001005031214 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 505384577 1250 505383327 505383349
    0x60a0e060307211a0a1202060c0f03040b04030201030e010519150e010602060f1506030103240e1b03031602101e020321040222060807030b01031b03080d0504060b 71
    0x11000001e020003400b03801840d01800c032044d860182c3d11040c01800211007000c800c144564040710704c551100c00b6080f91601d0b01d032a1481900343c0780000b2034000781e04030840001c1d0081d05d00c00d80301072040b080014162801c0b20401c41c1c07040c205510011050a4010040d400b1001482e468414402083c0d01d82ca03007144c00300d81c01e80c03022006078002c01c00c006450002a0004d90072070410324142850000b10400160b036408180005008101c407800d942284a01051030520102800355050050036207145d030f440d0310b80200c000000d88401c80300703a038071445103408011500403c01840c241210348601f9000c1c4030000c0314040101e020302196090016403440b220111040d6000c643d0300030b50355200a00c404074408080601d5100069010740d00b404010713500c800703404031084202e81003454092852108500901040d46c0044054004c100010007404144122281a41e0180c0c0c4620b49600103204034400240352844040d012200c28883c0800782040d40d000143c0060081d940402d50161410014012240b6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 505385827 1250 505384577 505384637
    0x140117030c0102030c030a110304052a0405100510030b060412050a050610080c0603090a030e041803110f06060d08130b030a0507080f0903040603090c0f0b1206060a0e060307 76
    0x1c0704201c7c3c08a0b413802044004030400c1c041508504140d929a560740b00ca180d000039848a2102d16240c45000003410400901c000034805d200c2d50900103020140c428890040e2030080302d07158071040c541030090160301c11084010f8122441d1034642a400d801c81d0704034010445250064102c80c2000c0782e01040400d005180038040301b51454548102c0c01d16081601801d24001c0e1000e00400c0040c2c3c0001c2038691940c4d0b054140005102d0210002034010140345801c0c0d28a062a50206400d059121020b12001c0f11004110ba4202010583c150340c0ca110440b05240d103d0801c1c1043c0001405e40e0003d0010800c441c0d180004180e19102c1008c900d0b08121844a01e103070f5124200700681c3d80c441240743d00300b42c00d5003041c101c906201400d0340d284d11a0380100c40a0540300c4651104000728640024000e02100140c1190991242e243c216654821500b101c6896403200120307040b03143c1402201c10701466615200035140210303081c44001c0c0c10041902040c080ca01504807429804183e00c2420360302 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 505387077 1250 505385827 505385851
    0x1e051b0c1507230f0714010c030c050c03060106120e0106081f14070c1a0114060f09030604470a15060e041505100804021c051f140117030c010203 64
    0x25680d04e000d80350860560181088a02480441329940d170000c0038910526014945120703500c840342016850b1030055501c641d0984150300000034419402010042c154504030700510500703201d440b140b8269030050042100582014120100408a0700022007a119803c0008a100d400c51034001c24144c80442c0d008000c6400c0c3c1003030004108000402d0b44801000e03e5640c40154100403074040c804100d8810340303000f040c002504142c83e1046c2e1040d680001c40c010b08640a5140c145400d42c0032102c25094078100a0340c2c1e101d2080d030b40c0c01440319907542241080c4484506890090813401000d0b0240108400356940e03020404c4140c1042d10360300240c2030945070300c0307504408a0140821241c43c955201341d0042d403480d0a00855075480100b02083d0410300d84130003191034034000a82240c3d054101e0840c86d8001759008020040040307031401860b0301040e840c110b814141200ea0056031089030302030020085443c011b000c01c4d4951946850b800e09818112030408013401ea2a500b280d10540b40c060b5100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 505388327 1250 505387077 505387093
    0x30105090c12160509060f0403020f0312090409110607140601050103150e040804120c06030f14040212070f0321020304030507060f1e051b0c150723 65
    0x8100311200581000c58101407501c1d10030410018803035040d02a00340d2010f0021a01d0001e0350510410907a81076103c020002980c1d600314102e010382d580e22a10080303002d00712100c849451444e0202c0c2602d050111410400d182921441c2000028505140c0498500c200014000c00c507485074005050a00c1c413a4810308070000703540c5401c03031a01c1c030143d000354101800d01015202840c001d00c4580111400784c240d641c1e5907211407608164600413070700701d0300100d42d209442c04188102c4180240855503143c40c04c02251910400e0710003600c420034001c0754000c04100c0850010300700420400041c01500341a9007480383c4031103918085a225900030388841000c0d002840d801e00103680d80ca1001c40b070b0703400114a000d1031035179501d0b181c0845100b05401c0c001030b080131a4156004441e0841c0442c061110802c0e441000e460250803038014800c40d4041101e40604074514500000b1201050940100042c180020050f014200d551041400710781442d1388180184040d03489200403000080c2400241120b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 505389577 1250 505388327 505388329
    0x603150b12010c0509040e0f03030907060f0c21090b03091b03060f16020f1006031a06090c0d021306091802130b030702031c020319050108070608090f060705030105 72
    0x401d8064001281a407400c001405455048000c80f800004280e4000ca01540389021850030300d0361288a410307250100100b042501400890f190007a14502d032a00c2c0f04409106200310b0b040d20b004030000f0520103c1a860440298200c800d050200503249080d000094a810b0034003015002a40d81c0c0005502000c100070660544490700c82c1c00c60000c0d0003c1c48a440c0900040c0b01101c0c02034008210844503001440d080c5100b07204062000100d03204a50365540c3c8500c00b80000c00c1188415103007046000220020040500700c0c550007810000d00071391954039498641000c82c0e02107020044216401c01403022031081c4150200001c0240b40c43c1d15101c145015124440d60300c403001c000c100b252042014810301400c42c81c447c425200b006010988964440100343e14502c84c4041c01d4010004031505d80c20902500d400031445014140e1240c880058449101000d030b600a00030780507540c10040b403d2100900c1900816800303502c91084030303180b40c08011524204041503030f040300040c1d030000050000e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 505390827 1250 505389577 505389589
    0x3030e0c03010908070618080408030301030b01170d03020c0a0c0f0801051b04033e0102070501020c0105181c0602041e031e03030f0c05070c0602010608100f0603150b 73
    0x200030001c1c1c000707000c01005039035103203c6445a6100203104998030f076500c1ca050541c01d015030950725400480e040d6503d848a00555803038209100031142965003030002b080e030f48410030701c02113480c1c9240000d0048080c4030780d00f034010350400030708205548500e042190106403000c0b40b0340028070601c2001450326003403289550a40d030340103141e04980b221420f0b4404800750808201c8040740d0f003111000880c140d543e00004078a958068401a88031220b50200303551160110100c012040246c0071280c0d01c0d42c1d9074006a072a01505030315140411010310840d0091842440c1507516544010000710815080000c1c0c184030442c4000140c07150741d804a0706018814804444140c400c564500c0c401000e4a5a940c46214940003010581550403034420b5000f01760207a00192912481300c4ca050042014401c0000d19070340164102380d81080f80710000184060043c401d031f03415181c40d607000d4410b074400501024060501195410038281d520000000032500c01030b510300c1200c2242c540450305200000810034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 505392077 1250 505390827 505390843
    0x60a051b0f1b011e0b1314060906010f09060516020402070f0302070e04080a030e0f010e0c0109090606050306090408070b15180c0405120304050901060504030209090102040e0106030209030a0f03030e 87
    0x812a0f2400b410100713603155a40944d80e105102c41c034049500300d02e800c00f00c0c181850560150200ca410b01e0a181000209094007038450f400c2692902d0107a583d1100440e044c00060065102150070790030b0034008544520000c21070001e900c007282002d03001d50b070b0105049030702800c025242105603c00300410180e051040c4001801000a1030758142442e480b1003001c1d1141d0f601610a059884172503420420090088080ba040782d54001c101c00c4079094000381d290b20080803980d00090440c03002203004010b038420034059652603a203a80c01d550703444046c00080c0902074401e840f4a901804a00001110341c0e220a21401c000d401040509141805000200d00c4c03245d8201864500f0ba010044503840b0076060791f013118001c542009981c82203018141c1184034981145411068190021035569000801041141e10030b689503592a558062907501700c1c0524002d0005107403089004100b442d1003500600800c080040680304184050340d00c4002d90000c102c03089010a86611090640b90320500000d5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 505393327 1250 505392077 505392127
    0x608070b21041e03020c040501090b0117450312010510020d0305060a08060c04080c030f1207230f010b040212041509150e011b02060a051b0f 62
    0x265090606541d0768600010301c1c0c14108015048118100c103045c401c12400c62000001781081205503159080031018102030035940780410201c9038207921021400c5800b40c8070f24a44d4252202c81c01a103051045400407003401c15008146058501079418032410217481c03038a40700343c0255a00c02c034284116000d150143e010324403031040c0c00710b0000c1568001c1400080c0c11b01ca072030002140d946410000329031140640000f81075100d001c0400c800c07004901300034010f403000d00b001c481c005e0440804042d60381c1e4000700e00d00e07030542011448149002c0701c90050b08140d44940d41d08800c01c031180c2c1d1038904549054480a81d10360014080f40342d00d6800b8402c00b1064070040c0c4080d803808a9120224010040140c0010444a928203103030b82c6200907076203d4520b8540c44821800386440c81c444400140a5112144144e54a01f1000c01400040d400c10702c060038040307401500903603880d0b5001c0340040c28020034038a04121200b0b1034001c00f045074030040802c0035141c600203803216005900500c2c8444580458 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 505394577 1250 505393327 505393387
    0x50c0403080a12180c0f0e190b0102010b040c17010906141203120103080a08090304030f0201050307020120070c08030a050910050c06040f1e0b06130608070b 69
    0x1480410740400c125007200c0503500300b10510300f0300308656800074900b040603200804c0e1443d0001017004103a0041c1030884110b02e9698201545580000350360807001c4d20b40344400154002456000080c98011542c5291b05000014100500c14080f80c00d854040c035607440007a440c94208107110101d4002c2c680940701c00710040080d01c3c14046181c8030104042d0310b1610030007038002c1164403c0000c0045803a000000b100d8842c06594a2803e10b020307800085401c00440d4106001a0110800000344c0d4101c9130080b00b4500c08e02c1080d001034030142e0000e0030f500215525225113035a09844000c0304020031250003e01962081e43e8104407041c0540360300143c0c1c260300100490000c06078004162282400106e03010b06102d15101000e483ca84100c99240f613541c0188800c010034000034407090540a030040c00c54844e0890091104504141800c0c00280020f50b203001080050610300e0f251411030581030700029201e903d4002c0301d807404c44d0039440707038442a4001905805502c144c00d110b4015015507440c0d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 505395683 1106 505394577 505394579
    0xf030a030314010618060c080c0a05030307030e030414010509030f060115030b0f090118020702060705030702030d02280809120c030111041415070803070206010603050c04 75
    0x44081c2c01c0c0c004400002e4454082c10182680c0510042007000c1c080c102801601c3e2801900c400751383d044001c4c000c204c400703002000540906402400255147c0c80c0c1004001c06560408100c010360303810500c000c000c40c100700a1001740c5900f00b400c09544843c81e802c0845d1a080f441c0c807458529100b24000050101c000000c05850105103540522060741503005100725150401c8101c0c0d08912614010008152050050740c070b10f10701d2800144c500303041900051030fa50012002900d8039080042c640c000c6180801c0902c0c03039820b0500140103510407545c0b06030703070356442800c5c0d101c5110518907044040108820490700010801000b10005003640c0d01c0503680d0f452034103400c034000d628051009640540c1700041d2011155207030100c840781c64510040c4405004020204003012000344059400904150045d40c41220316500801a641c5004d000906130392000c1d141d1801d1a40800c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 505215827 505395683 := by
  have h0 := BRFrame.cov_init 505215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 505215827 ≤ n) (h2 : n < 505395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
