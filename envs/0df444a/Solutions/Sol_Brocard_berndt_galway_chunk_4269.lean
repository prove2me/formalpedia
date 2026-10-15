-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4269
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:04:09.909988+00:00
-- url     : https://prove2.me/submissions/a44d498e-3b30-4659-b90c-5a6f5e1cab38

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 767625899 ≤ n < 767805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 767627149 1250 767625899 767625907
    0xf1503020915102a0c06051b070623030112030c06020921010f02030f010605130f030308060901080309030d1817010203090d020a170f072004060b0f0403060b010203 72
    0x8208180c004080781400300781d44d00b1070328003c801d094a01184140c103403208551a24019107405541500502820082050018003a107210310003945c46200019042d084a52a5035900e00003041000c0c2141c1002215007192540240b09120206417810b035024254800d80c5203c80c2d035021b0754503125550049aa464091100c2d900039079558000d81926180c03002d91492100100095900312454a2031003003145105000f031007810700100c4c2649064070700303070b040c61551400200f1a45603640919070180111a01030303500402007543c400003082c020042500d0452303040e600d80c0b600685a00841c030403140c141d48000b000c110543e100c0c07890b400241440c01c02400d0f0340da031a4000c42d001c001c811b4051010710303900001030110a4108221141d1301c0201413020b003e083c01c07d40d40c0e0080b0403640c180340001000d40450004800c0081104403402070758040d5000310012000c0004501c0e82c5c86501c455889140340030000150b0150705000c0f00c0619900d01b100514040c00c5940b842c0003004071410550451000380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 767628399 1250 767627149 767627191
    0xc100c05010911040f0c0206010308091503090a0318060e0d1e0f020f010e010f081e07020c030c040501140402070614100e010b090108010312210f0f15030209 69
    0x846000b0800340980f80d003110b454804802d204c29501d010614103000751a180540004544c049140c505403540001229542c440b84000112101c00607003551040d070100109100b4034810015046283c01e210f40c0f05c44002501c50200800400c2c0c592241ea40481c01803250000c00c1d01c0c102c49100c0040d4818510070540b4040316a038204901c1c602833045854845c030070340c00700079407510b00c081c03030100542442c04210000c03070302c00003c140910f422100414403440d10085802000020110341141d1080c0210481a28203080000c1d5110510045a0700038021035990380600d00f840d01840d030503a00740e0740e104202070541b1000d00009500840d0169920341c0d0300c0050502c0008016860b42c068040a01190b40b610300b008444130040b041a44000c03911042041a040c00d82d0300305002c581165003092107800c10050001d801d442060a8001a058640a104151150341a99802003040d4051010104802c0c4a21b65550048403400a00c100940f030005504100600c0d00000e001d41c07080c0410900358140f0141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 767629649 1250 767628399 767628401
    0x411090a140a02040303030f0501060c0b090109020d0b0628120302070e010b1b06280b121b0a0302060f0f07140615040504030905090907030b011403070b04080c100c0501 74
    0x1550600b2800b500050200107040d454090500122444082004036516040e00a04143ca595400420250700f0400080402030207600040d005600502812407140c9030f8600030440c180c0884210b0f210794427009492a46801841d404000c0a040242e0004801d0405212521901c0f81d018114210301c2102d60106030300300034000c0a03000304083d208080d04c0e44003c008000c502ca1079001810003e074403480410400d2040e40001146a4450f2100800c8280c0d650240001800303446207200d07080b005000c00340500341d034001040d248a00008124503148010700c010071004601a11019620110502c920114078015500400c03198080010781440d200046c1c1c0d410007240030001074048180c0004003004041610083d00306071400c400c075420048c51400b690094a1000c0d5405828040c15061000650101e400c0010b2406190450350300825581d485042154100c603010b41203009000c0e585000a41c6e01c080b000351401c0c1d4503003401400c2100303c06814041c840b580d054040d01004984100e60011a5007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 767630899 1250 767629649 767629651
    0xc100204090606030b0303030403020d0c1a090d09090b0a0302060d0b09010b0d0c210c0e1c020f10090b180d060f1103190b12031207020606090411090a14 67
    0x1099000c41d040345032000140c21582405c020074002d030020070401000a0340402c81c01d10301d07a082d0520340000e4255051503c0b1001c0c440b03226005e01c1c00d414090160042c0001602c0d01108010354444420300e480d024240c0649416400c0903800000c100303401d000500d002d2018110f091030704a000a00002c61000103400001c0c20781c0610542c0c1030024054095504074010803c1e1004241071a03009201800414102c1a48550b0b20f44943d036030303400034450202c4c801c1c0031541d8032000080410364840c500d030700f00e0a8a49038026080780f24600400403083c0500308015240310050342910340c01d004500d0b1580d444000c2c0e02c1095401140f94502510042c1c2c0d5841055038071140f03024800000301801d1260a0108071111403480300c0040f402481041106840d40025881d25102c0c4800404e00c00c96040104081d034544903d6a1900d02011480c40c420782c03034079144984130b502503908071122910360384103101201609480141610061002610703050400e214002c0e00303d802e550000444405e1001c6908000304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 767632149 1250 767630899 767630909
    0x106030b0109152607050a0f0f09140c1b03030a02030708070810090207080409020c06160e01090510020307020d14100608060f04031704081911060c0c100204 69
    0x2040d44014070000c240c034402e10008a9004041038a92814201007003400c813002c184c2804100c12048015154504c1440321000400014080c48103032074690301805028003060003004400d00c1400b80004030081d0600584040c0d043ca01b00040303694440714084200e9500c032801c00041543c00e40205140714000300000c510503c92020016103904200c40b0003007807154003521402c00c1040c0541801030f040200d0203a042110488480103030f5820072450203241e513001e0740e4810a40320780301003150b079002040403501601c50f035031a5020810480d150300c006e42d003441003441440d000030040c0c2814081e03811300a231500942105401200d003410100e900042d00000020700403a03a2b2042c20020407011181048085e02504c0604001c1c0811401c0218056403000010001035115a00c880801e05150054151209070b240e104071030031092901d030510340003a03071200c18961034844920344498044c034410131100c4074181c10507024081a8450901c450780c9600f0190001d00d282c095005090020080c901c001c00c000c0c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 767633399 1250 767632149 767632163
    0x307030e0405060f0a0b0a1403040c030302071a0f0d0605041d0706090320010c0c03030503010323060712110c060411041b180f030f0b060f0303070204020c0f010603 72
    0x10104014041520b40142006019003c80640d52020742d40d107030685030075501c00c1e03054180c44901d812021034040040603401c000d9690000248070522a42280d1502580e00a03021168003d695508130340c5442c5044d10071100c262424130015111070700b40c000910808007449000b0503056241e90010b01190710205407a441148103000c1d40390000d405220000007008641007541800d860b50300c42e4482002c000004003456180c05201c01c050ba0b01442e03060b600c058101c4c3d5a044220703107074030f8040c0040e4000e0009884002c00d2041c003907843c1c540248411040392280c4090007103074560359025034848548112000c091501c0d4044181e400d04e03404090000141203070300a01c4c440c24203042003613166501c0003800303006a04100340e02e184da00008000500150991030444807181c10b118202048540a80140d4600c0c4801407001050020100300c05503454011441140c0c15200c410400c0192400801c0c6260907420078007680015103002d034081c0440040e52000c1e106e0141010300031508403845a04102d8500c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 767634649 1250 767633399 767633417
    0x50721020405160f030b04110301060c14010507091e050616022e0c03300509010605401b03020c060f0a0f053d030b06030f030703 57
    0x903241074010302d0f410030040400e40550149081c0001c1c4041007149a0b001415101c1086024645440e882165480c00b2401c50548035611020014603081e00d109098411142c4400c2e07005049106119080c01449940c48031980c2a24003131030fa004c40d60245400d0f8036002c0820f00d000540d512048001d2a060b1440c04034120551500d10410070b40d0781a03a00c64044c46100030110a47c00d000f400720482e00d00700b180c180280900e08a1804462605031000440b025054080c82c0765402400000405107001e05450148542e6a80d0200b05007200c20130301c41c00c0d0b40400626450681140b442d0200308045c80e80304100c95080400018030107030804807542000c402ea42e9500c3e6052021880e00c440c02070082ea504d0250300d01103074044019075900d800b90102c5e0004130094085800c00c551944020700003000d8080034025880e00941203050495030b0100b10300403a091000302c0110120b08034078410f045071800b0b001046982940c0703900842440003004182c1511a2150100c5600d40030405011082d1280d41c40482c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 767635899 1250 767634649 767634653
    0x110d0e03071406180d05030f03040c06052a010917031b040b07120c020d060c090602070e0a050a06050901120c241107090e1e061b07050721 61
    0x29200035a03010805480081502140c81c3d40c90800b00c4081e00500c4c41e003400760365081c1c0c00107144410801001002c52100040d00b0000c0321824014622440c0140c90b0340c03c800c2d0341c038003041da01c1e03215002c2440c070b0705c0c034054241d421900030102e8400410190340b00000350b800f0b203a54412801d404039034540c9540d02c1c0c1c040100020041007445007140700d203010203500d007071514260003003400e401410401040690083c802c0d91140d84036400901c04d0a0b001883c1e01240303c40d6003894030007003e070000c0e0b11001500c840000300c3c0c041c5c0001030600440c4d081e4114a03642e503440161175801440050203031400c035500e58600080d10303641e417221940a012000b0b005200c980c21031030702c18060200e562005482100c3ca5850b980b40c40010042075141801504000700707044c0340300558034208905904440440c9240c42d11134540c0700400201c40d01d107003c100700e29154448a0501742a40c2c1c1c9003c94005218174512030800100c00303140006444c8180c841d00071115072680b2001d0304510b02c081d00190fa401e40c600c0100c0501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 767637149 1250 767635899 767635903
    0x1b0e041103011b0c15020d0902030625030902060f0a1d180c07020a050a0f090b030601030f08160b18011d070b090a050907030e0d0905030a02040507110d0e03 69
    0x980044100c008101080003003c00041c0441100030050074450701c50910400d002d0301d0f10f41544000c241740800c541d60b1103038925400041c04030030010380c040c0c0325280020300f100c076000103400510081c1c00014940100700441c1213002c0c000c04101260004030074803d44440d0b4401c3c0d0090160030002d51500550700084182a11f0f01c143c0030a4894072881520854014100c4006070268100c2c002c0340c400c2e90348040e24008180d0a500e5544456080460943c0005414140c034107400181c0f280f20b0400d21600c20b803c4d04240c2c2c0c5240038040542070142c0e5401000000e02248020026950092643c02c0b44800c01d4aa42d410064110750f800d0447d5000f2230b03002c030130010a10a4087d0b590081d0310b00a01408010115955080781e401140c036030140014400da15592036140c10350003048001c1c000d004c94944200010b0151009903242c4905d4440c41c1e82a403500c40c000c00c100b60030f48002600a00c00700c003c580802000e040042e05850a00c4100e00c030560202c50188400e100450258403040721a0901c201454 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 767638399 1250 767637149 767637173
    0x1b04050d0b1b070f06020c0a150209010311070b010506160b01091a03010920040204170c180906041704053c0307261006050f011103070308041b0e04 65
    0x1040d0b00c040180c5000140c0c04406044080d420810068441e05000a441d04c3c00020080261034403904e200e41a842609030340080c980d0180a903020701008540e1500482c01740a9441c000305000241d20051095040034000f07014003140ca5890882d031000706855800c0001c4082c0c0048401d1030311340c60040c1544041035202c244e40a000e41c02080b86241540395000401590b1100080304400a989401c0c1655180c0541380034201441e2064a56040f202450f0703a22024803840c1c600902d000d80c02040c040315010304152007581040082c14580d5219543c1c5005000b00e5040c96018207020300010880e9140e40404811018860142401c56903a200034034007120105020078549542c0c4400b5071030140c0300451018100d424003218156042c074a010f0a4004421588208a5030300c154020181241250381141040f80c1307090700c21a82070410a0011070b040806407415504c0c40c3d0080280d040041c0c070030160302e030348540140c0003c100d41d42c1e10541300410141d561301c04602c40d11000c06010038010100707014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 767639649 1250 767638399 767638441
    0x4050f070510050d050c130b18030a051c0912240615080a14160f05091e030a081902010501051c081b01050a09030e01030903081b04050d0b 61
    0xb075500309801480042507403140d0340c405004191500c01082c526651501551190003640f044403030100c1d00d03101e10400580207000c40022000001c0b54005c4c43e810003140c0c070307200f254004000d000c200b0080c50309060424000c034559402c1080c0c1c9800010500e14900a6024552103289440810079040251400c12201e03000001002d919203c0c0812080701c140c407080f02609680c0c01c1c00344a55903a02c403420000c0500c2c81c2209866002141048400f0400d00ca0564280c0f0b040e8032041080c46d1400800c4071203004212020790004042c0c0c1c100d148011542c02d034441d00f240000c0880340000c0c41952002c0d9542c00c001c2c14024414141096107410b07603020b011b44c502402060f55031a0648014105112032803225090142240c08000b07400c013010404030741e152141c062440006d0080381484ca09260051a43c9003095000801c440b803104443d40c0300f401a1141150035607220160f81d2250440c4004a00c10710720354411400c2c080000164945803101c009030309501600340d0b10079500d401d000100810034201d030301c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 767640899 1250 767639649 767639659
    0x902030c090c0d0b030a0803010905070206010e040507050f04020c0f07170a0c06030c021006151115070e030f011104031106070b04030e0d020306090604060c0e1e1804050f0705 77
    0x2c004644039400e065985602e109400828010700b1000428241030250340094807501c4000300100d00d070000c1c1e800c451f006081700c0d4201d0b116680d984540344078121056500629a0300040d108024030710702202504072030800140014039020500f20514900b0000018116164000c84807c00a1007584119408036082140161480d2040707940ea0a00000e1070380140402e069885d103107074005074400c00180c0c1d40c00d02c4d200001c000c61a110034121000312422414040014021130454841400101c0c1d69a244c0040445110864075081c000b5511080513428054141c8140351481e00804401d0041d0342e411114402c0c2e16641d0b0b411400c100007403101501c040d90040c10100014000103031080101c0340d0191309807900d451016507550000300d4406014901030744c035101e05000d10034800d0020940500841c4245020015241c0080e401e5411000c0d6011843d800020540d030403455508c0204003203440900108a04008015104140c561700011b84007a101540700203012030750f80c50100301140c007410b03003120 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 767642149 1250 767640899 767640901
    0x4030305040b13050a06081b3c22060f020a06090204060905090f0c0915010c1e0f03080106050f030414070b03240f0a061409130902030c09 61
    0xa01400c54440c5105054403848001511910460f20480c00c00241c500241200c07946950f400004100440a64040d0340c40511230129a502d0217244040301c0f000003003126036418200b4265122090075441c052480b000240c116021404100d5130001084c0c90004c0306002e07031410100c000103290824094101c003080c40281b44590100d941c00041d1010066441080811044c0306d0b4404035010f40800d80c480402c1c03d0402081c02001a000b0518007141ea184404445080a0030401c101d8210700503500522a101549091462940b241e20928140c50055000b289104000f5210002030720040009590410000b4004d0f8101756101403050f0041c40a4079020703042810365503105a00b4413000d000142590030201388407441c0c8000384030180080c52688182900c034070b009035820510440c10000c111102150240b610003e150144c0003400d0000080c00d246501410041c0070703200312001000720440e034501400090b11954802d2584017814105050215070181c041c0305061402007491286449805124 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 767643399 1250 767642149 767642153
    0x61f09031e0b0606180d06060513060302010f031503050d1806090506040b070f0b0f09070b190e120f0d0906020604050a031d04050c0304051504030207050f1519140403 73
    0x410b803076800c101c0c1250800d985100034108003c0b802c4c10f03d03035070070340181c05801440d0500c2400c0d4004000c8500c1941c1c0c0d102c10400d61450001220750b03030b0100a000c42d445041030f41c0c0341c1d03200798001c804a140003c0401112501d9495040c9446400c00d400d0380080d140c1e4140d03140b500c1d58801c1000c010300b02c1c2d06262102c642828006283c6010f1030003102c0c0c0c2e150010900c03c0a216003192007000858010b81318103d2402c5c9800450401ca4045580e88858401d03a07500041c003443e82021107884401d2410501c2003150303140760482e14010b1109400354072401c14007860580d000140800d007a990120f40040c90781080001c0d001d8482d6040760302803404d5400c01001c10011583c04651b2118069243c60000011009144009401700001c12a00e410900d0b00c0104100e8000c9407009500550040307040b18091043c11400202001d000c44000300107030045038042045052101d0500c5149100074540300f910b06001461060b11341107505c1a5459100038940251100e401005d4001071807118041d45150a05603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 767644649 1250 767643399 767643413
    0x30e100801060c02010c120804020a050d0206070828080928061509062606062110050901050a1512150b1914041503030503061f09031e 59
    0x140b08100a01c0002080e01085a00c54080784440b01c0d8055003c40c41d07404403010041803901c048408a0154031051404101840c24120540c2265802007503107242282c0c560b2032603d40d40064501c00d684640340d42d0344080c0b03203887c0b541030148459659180e101d40d2400d201d080740b8004c0000030724420a506880c2401e41548a82100c55802d41c003c0004900c5800041c11847d42c003d4030ba04c038491140c9001c5021810390003842140c0004026041a42200c166560403d91902d0341030b81d0103036200340041180a02c4c011109000c0400b0800b54041d00c001c0590713100c804d02620011074030000136075074510411100091300d10034000100a4120b00c68890360404500d4040e071494020080c1c680040e03031480481016098200509501020f400000c3c41d0152004101948415008049000f091103d1031500c83c1054451014028154003c041c00b591460310155010783c005424030b6000013480041c2d9942d10300c100e12050310311001e942d03405c0741107203181400082e0022401040882c42c01010155004c1000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 767645899 1250 767644649 767644651
    0x5160b1c02090a0801061e0806060108011206060f0f32010c0f05150403120209100c03020102072307050105030907150c060e07170c1315051507030e1008 67
    0x244010041c0da42c55404006903418080d940800482d40c00c010b404a6030180070210060b000300502c0800c0340b401e480e005440d4a40a0403160a40011000d07030041000d9113802c50181406800385800144145c0c44442e03c901d041017503080105c40f00021034040012400e0a107000a82c00c1d800e02c105815482042c4100c00401040d888041c1084230001c842e01c18050030094500000d81c2c41800c031000c1d0f030f0310010a408280021038050300841d0320703c027071131b00c090f07509008480356080000e0501500c4020140140c5950000c000300f9002c5640c20f0140d10002a80d68412900b00b1843e10303000940b003110485414070700421798204a04001044c421f1154030100000c0801c15501050141082884d001d07008a60380506058054046401d00048241c500301c0802c3c03110986000303008001208690b00c0b01140d0714007003030010581000c400840d520f01c0e8480d5511000511006010b2401c1e801e5803880040d280400d003851640c4900700024041d8105030f04981c01c801449019220102c0c00c0c900b614000e856564 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 767647149 1250 767645899 767645947
    0xf0c0a06022d0708012a02070e240d060902091e01050f060f0f0702030724181805160e0d03050a021207060b0a09200702030c09010305160b 61
    0x4241e0b03030704112a500512146000d801d03800300802041c0d18103601c608011080340120354041294036184000544045a54403c2d540643e107200c0058139404606402c0300e0b0b00d01448811030300320b481c06030040c0d91034880b1960814090a0041000c46041c01040341c41a805403079010840604181c0c0424042445202c90440340c08407818070100001c44003007200d62260300345c40040d00354000303111812410240050503990b4001c1d0103d4540e03030f45940307002c54584007600ba1000c2002001d506004030340e105504400c58030055101c040920b542c1c6184521094401c0c03109812100d880c0c00c10081c1001c00e100310340050545510b440700034200b090010170020755a0070009002c1120000354021000d00800ca210349013102148d605c1e40e640c0c030300c2c2031500c020907013542401c4c440c410a042c0041c4803449400740039002200340240d400f20401d5094041d03426441400100e0701070240300e20740e0f406941d46800c0d8034005d502076005000c1d6000036141d001001002c1d60070a013404001030041c100021319040007208405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 767648399 1250 767647149 767647213
    0xa031d040914010c0306180b0609060a09031208061e0d08040801061403060403050714030909190c1e0c17070302010203100f1203121503050c01020f0105011208070c080f0c0a0602 78
    0x1800790744c00300c1c00c9c1d0300c260314480d40c004100048c1582c1035a400030801046a00a10351001e150701060005ca407102005c1e6640c0b54804540100c074803410204121007840c154005166903d42031b819924000c0b15042a40502c00503550b80c03038104070703007100358903154101c60086010b030070305141c00c3c0d902812901034a01e000d042c107074041130390395005001001180c0307200c40010700c00e400c2881c04078420221040817030800016607040030040004180200e1021a500030080b4141c240f003030340d8001c01c44112004242c152400400c041c0500341101c1c106008000040c0690300250742c2e89000700c9610032840c0950b0001c5e07014100740c1c40401c201c060310b00301c25500319411310300151255011490324000e8075101b903000303010f000024000020040000b5140414400a800390307410b0b0105050210b080340e50912a4921030780c080c4c51540c001440c2e041c0240b1146200d43d40b4520016100c9030403500e45003010386a501030741e0003215000105d2504080f0440105042d200030000b051241010324110740803400740c08440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 767649649 1250 767648399 767648411
    0x50c0d020a0c0e100b040b07060c0e13051509040605040c0506030108030307030216021206010306050c120c030603010e071202010e0429010e151b030c0a031d040914010c030618 77
    0x4034284c3c0c4001310060419402d17054449455021094140d84012000c079011413800c4c0001d005140520381d16580280b004104002c5207081d0748071003028100042041c804041621080401076844c6040c241c015401303940c0c0062245080c2ca01503100c030003941c200c244600ea0600040103421000400c507980464540b4025032160719100301b2980b16561944004e5220a8000030300da52a0400600c0c64100c0340108030501c096207d8000d0b202052241c80c40c003008039401800082d0712602050021508003801a000241c1d5400f89041e4074180384803038004038551800d10500c28150769124000ca01a0311080310f0811200980c1c2d0a001406840164614600d80a140da00b0343c16a01442183d41c1c507480c00381150300145124013007000951b101910345400d4080700b80e100034044500000340c9006180b02d07002884c4c0306045403025100e0301c8101c1400c10105040b040b0b066074686690252a1001e44150760300c80460340030841075820754a503c003040c01050315010080004001c8526000c0b00100a5100080e807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 767650899 1250 767649649 767649661
    0x80a050a020a020d0311010b0a060507032a0503030f0604020906161b0b12130b060118030503070c0806090c0108011a07201f080103060e011506050c0d020a0c0e 70
    0x7015402c2c9000303540700650030030000c14160000401c07003108681d18000c10170144144200700c0b4458050090000150b01403041d04002400f03210300c0351808400c06075140c030003480c3c04000c40c0410b0641804640035000842400b51031080b094981d1740100c000c4505506000c000c0020034036900811002c1a0000085034072102488842500c10407a142041003900700c10f910f558401000d58000c0c80d038a22004d00080008042c1a14040040680d541c0329003c03480c942c41d42001142c50b1464a000d440c00c241c50b400c030000003d40b00f0402002850301c580140c900c16441e0241060a1010040c254411508066016000340c1ea0009000d4190303000c00a4503041c4100c001c42e1100b0710b00400c00b0081011124154081c410f2100d8100508081802c03610080b5200414460441c15403100c1c8a420225400500510005140b900441d1600302040000512703c12807400003a90102154803c1000c10000506040c110006001035000442140020120144c0c540e8603804801c4d110310502d06c0d13640214020a80c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 767652149 1250 767650899 767650903
    0x12050403032003070908031c0c18120606090b0d060203090109020306040501060e011a0301060e0619080105152104030917070603140f190b130510050d080a050a02 71
    0x310300c005840801c038100c522250460a5000b50b4444005ca0135146001800d05070001c101c90908181891040d10304181112040c0500007010010043c080e40c541d003409000b40100c05c0e1801000c00820f00070030402c0f20b040c02c0b404ca40d00b5400810800c0c1c00c1407800000340c1c0300e4042110320709602c50001070340c958a41c0c0300745004001c1c0074002036242c0154402d00c410301030705411030415103810480480e030700d903070300c190003080e0540710108821645400d1004021050207111100206a00175194031702d802204181031900b840510700c1c40d00440e8042d8010300242c10503c0d10449801907101107a03242000104041c603041440c801150803003080031002808141c4920908001070055010b9141c0e14400c100340141c40d4202e90003003e0004c1d03d00071616209030400440c15004100a6025101703d40760368085408484000c110b100030540c54031917189590725807400c200080040c0003000a958140350030003100402c0da550200303105032100071213000407441c080111a43d504142c1010350392181410410781c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 767653399 1250 767652149 767652161
    0x50a0c03140d02030604110a0c2a0314010605040e07030206160803011823060d030917070302030f01050f07050d060b031312020a11060a050c19140a031205040303 71
    0x7440c04400030903a0310403008107402450003510119000e0040c00d030b61910200140c0204404400090b402034000e40224040b40c803178107622440040c91040c1d02044d2254980b001b100795104503080d0011a0408000100030311030b01d0003819044030140504a03c0214070b550743d13651400064480c03c40041e0680e1040d5050f41010041c80c0c2c0001b0039034480d80d6482041c4030f131294441200341c1d01703802c1052500340c2c1c0d0051102c410400380c0c034040c416003d440b44010b100200300070250032024041c4002c804201e1242135021500201d1440c0e004280c214207510606042c03800007000b40e081c0781e04100502014550343c0800d50b07800107203403038801c1e100c4a4190a0001a0007d64041e401280d400002c2c028481c01903d01000c0c000e0003415a1202c416104804a940d1030702c07854050610340000400888519000000305810740e06840c0c11f9082443d81d03081c080c280340d880c03d0a103025001100c3c07400d042040c1c188940610648442c0036100101050f100945402000441c7c400c0d4103650302c1c0000d003054001d50103c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 767654649 1250 767653399 767653427
    0x602061504020c0f03030615030412050d091b061101140c0f0d090f02090903090f12030403210f0207180b120a03030e07050d171e030c040f0603060501050a0c03 70
    0x101c03203c81c410710440d0317220740c0306452035402590b030003146c0009260031b24205ca000301c2d801241400c2c04203407a54120b078076400014503d40015240c41400000c610810300350300522500300030016843c0e1502c64003819280140c012031202e0707414241c998408842c0c11406550100200005c10b64030321801c401180c1c9486154080440035190003034a10900c0783d41905021014030a03101401541c0358039420075601e006414903e903000c24101102c54482c02e001480d20030310b00c0711600312410b0680b01d0f030399442d1307000051580d49034400d8820004400c0300c1e031142a41d4600c542074000350640c242000780401e07800401c40c1340c002019032501c102c05034030303129021840504c41d800400c1c0c6424140711b02d0000c02514440032007040300e108035500401c0c0ca103410030380d1400c41503119101d208040a102000c0501c0d410800d000301038980360b007210252003a42c1000852140040480c0c0e1942ca605180c440c1302d20b50b07000d4015408041c5804e506118a90700b02041300c0d1110036500b0300d0180c0c0b12040c5070441d80340100c0066 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 767655899 1250 767654649 767654653
    0x50d0201020703020a0e070f110307230f0f0c01030b030714030a0b0c1305010311071b050a0e0f0702060f0f0a0e0d0306030c051014280504030614010602061504020c 72
    0x1400b640b1b11030840c0c01602c6c1d41c1d40e0080001e0100501b10f070030b4449207500001c660407c1000790b000903d59408600280e00700200042034110b1103014a0414000301698071854003c00714104c001d03901400300181703c44090070100008032441021964031002805804480401e601d0742c58166030741007100313071307400ca1f4814060341d070b1031600c072500c40242c0d0010224020a410786d108040703082c1d8000d0040301400300c2151040c40c00c0c20119250341e0481c0c803070b42040c008202e416140200c0d240d21600d03014406003501400d400c40f1410641422120050000c01c04000c40d040b003004e2010341d1412404446d04420918020102619041d1120300206100c05600e411407003914816481d094254105404490103000c47c410044c0e594002d10440484d02c1d0003a0300010104149000700381c0c03101002c0c01d4100200c2c0e100010600040302c1c2c4c0542c2081070540400420b5002c241041005018018004a2940300b11066443d5240820296960501030000001382c1405021344a01342c54a0b41a19001d10300001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 767657149 1250 767655899 767655919
    0xa050915250e0907080c0d020d061e0e010e0103021804050c1f0306081605150403051219030e2d060f042310090204090f060c0f18050d020102070302 65
    0x100a422203640d0b042d0300d03006070706075000500d180b030252030410300c038200c0c080c01ca030700c3d008014411400035401a42ca604003169206008520304010509100440708100203004a4a040804c80c44010005910aa400e07031829001403005855540040560b050083c3c02c000d40c03034643e880c10034101003071458010782080a00b01000c107900248406080034601d503880411007517441c4d101c02522141d58080030800e1450340070040006003030005101c000001610380300e9007003540b2a0354036410300ca04a40021f000e81000318001502e8082d140303500201d00d0303880c102001561440600ca58850031038645a503c020103040d003030b80082444036101c1e0780b46600402682e006c1c0c03801070820103041c85c02759003d0300d04943c682d0311175141820021030500c00212050081000c1a81881e0b0400944080e680807604103849900300000038004501c0c680781148120301c0030450782e0410310300500840d10310742c4a50400006181c0004206000030294041da60142d500180070074203400182e14000d401e62009411440c508 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 767658399 1250 767657149 767657221
    0xb0c0726010221070507110f01020a0c0e04051207020907030b040e010c18330e130b09090106050109090908090607030914010509101b0507120201080a050915 69
    0xc2d0f9000000c140d01c03000b90203850b5000c048800c1e0007a03a030020100d17695152605100d18004201d03800c2140b0510403aa801001542c80c8043c9166030b40c00001701980f100180000c001c401e004000042403400d81c12030034081039400007070a68601900e208189980c6100c8082251034941011140313144d404000e000d200c10100c0010550030040c0b000401700100030300041444c00440030700d520721520000308042030b05480c800c04a03000090103244028488006010166034903044011888481180b00024003900010240880303c08020410281645000418006613800c020410180d6102007400201c05440e840c002517503100e0350032010f03403190f00482c010b010194080c0c084015a1200d142c1d00c40001050340040d9010b000304802ca59004144100d03140e010740c85080d8524694040c0745000182d200c20707031241400d011594112a80860303d4200781025941c000c0f8909821440c1c00700c081200b0b00c0c00c0304905444810840c200410400d10310045000c44070341000c4a210082c802c4079100c5544540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 767659649 1250 767658399 767658427
    0x10f1b05070512030702041b0f180801051e070801240203072a120b061c0228050306010b070303020304170c06100803030702100c090816050405010b0c07260102 70
    0x1b02d00c56401c101d000103450022a00a030445040b603141e0f43d4010f2034448042e102408100b242e03000360005203600044c41c0c2e6090240b140200700e9400902c0590b101146000f035a003000030070440c03d02c00740c440100304044150001146900c00194808040c0340c1002c1c2c12070a40c81440e001426030480300344080b6460910080b070010919604141103e00d650b2943c56000c0401c1003440a0000d02c0c148000031118209103155802c5090b0310140342c0c048a4040c2d001a62088801402c2e80d0701644007030100c4460481c1e1340701c000183c54100d004001c20340c50040d842c000b40c07107a46001000c054010000c0303402c00c4a0001b01c410720100c00d08581d6154800b0445c8203503a11000c4440c4800045d1030701c0001101d56000c0205c82c064107065002c3d1035102140b456050141100801d800100300c0e0b20040020040f1085c0080294448841c080f2201c451400c4100400e40c5c2060708940d810507003c100590802c3c2e000102c003001c032010100242e100310600714203150404c2891200811950000407041000054 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 767660899 1250 767659649 767659657
    0x3111c02101202370807033c29060a021e150c03010b09092d16050309100b0105160f2f01031e06060206040c05010f1b0507051203 57
    0x40c0d500c403003a6540300c0c10004c44043c903180c034541021524502c04905020b00c030b5008081c0e206200124518030108500f14000c0b4040310540300700880d0840882048000b0880c020740301d00040360001380030b1403041400c42c0481e0300780c43c900c01c034410500040d0f0600e23924006d12211003880609801c0d0156042c030f52248589910901081e000c5429101000071180d00900d410380c1d050b0741d40d504401d4100403072001800a2040094a00184d100e1140412020264502104c101d007007841c0f200c13038549003070190342028202009414907091007014420060200740c00140d003420030054080101d01c0c1d9506100580d4180b066034140e99904404a680394240702464420382030b450711601ca1180d40f18541c140031041c503114242c1c2c0408280741c0442e891020b41c0300340c008036000b890707161891416031a401743c0401201c02d41c0c2c0c494005a0031600c02c20040c0114000314400400c030a0804008410a42400038a500c1180c290710040c6110203407400103100c001c0104001030800540011888001c24100c5552500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 767662149 1250 767660899 767660947
    0xf011104030b070915270b0705120403030c0b180d03050103051005040c0603150f0f050108090a0b180a0203060a0204170703050d050717030a020403111c02101202 71
    0x40c2e00204003200d00c04d50341c40049501240c0b4441c00030b046490100d401c110b08074a01007494040a40500903602031101c11340042980d1880700d40c3c0c07000365191044c20807a83d003103a49006c0c00300707001c00c1001c40d401c5041c650f80d059100002940d140d90b902014041406105c3c416280b0703100780341f120580590958482c5040c0d900900c1251584a24602038600341d0308100c074020300185440d102040414029000480d101504503802c0703a5140c0c980eaa440035806030795000046d640d40503501006556045983d030b64005661002a0426009545a500d0340c85c0d03010b00fa4904940c00c1c48200314221005006050100703500505030b070742c1c03401d00e602c2c484081c1d01700d406100d03581e200b0003002d00603a40d40004e9044c12264807402401c2e040101190507a100e802021040d45c068291b0480c3c40c1100849900440c0f2420324401c0041e1218210b0070003081d0310301413007182c0d4092a003c0541107c1000d09403005801d5903030403a05d0320701c030070070155080301d1420794010450030030381c0040b41c1c0d00d406035100901d00c1c80141c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 767663399 1250 767662149 767662163
    0x603060d0503042714270c0d05010b040506012a14011514060a0804110a031e0302011d0c0409050f030a090315110a03020901050403020603010603090b0f06011409030f01110403 77
    0x203801304203c0891701c9030030746220b00c40e0306181a80e8400380000c0c0000d40112a01e180540d84101c0036500480d0500c1c50a01c0101c3e004d03503490f10120f01c2e03440c00344501904040c00703182c81076101c070040c04032003820012034003440c02d440500100d680400000070400011603032007800038010b000b00340c49008181c0300c490284544000c201181125030b8100340c400e43d0010166592a00010f44441c0c440240c046074107810103400140750b060100c00306001e4448480155038484001ca044d0806040c020b007114441c0134102121290351182028905001a00342c03100f0f1000c803000200c201e01803900510740b1040c028007207030314003000c01c1c0005016000381c81304080f28019a07070003500702540300d040000c441400c0208184d140c41407000660031440b81e8054428080c040c10300314070f016283d4000038003e8109900c0302d0700290b01e03080312004025081511507041000510f00d50614107001c80080c22a200008407070380c074200c000c2030400e0a0b03a01040310300707280748050700204a03030410010072071010b41c00b601081d9140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 767664649 1250 767663399 767663411
    0x503040506070f0f0509030a050a0309030507080a0c0504020a09050a2304090507060c0c08010617011d0303010b0d0b10020607200601140111010c02010f0f0b0603060d05030427 77
    0x40c0c022804451a00d0413541c54100030100385509490a4003c405d0441e0140b14115500c000520100a04c00385170707000742c4504281e0b92540c90325074501551604119140d810100d2004002050f85d0800802c0c1d4100311005600c0d000928012a181c0b025584099400f158500f000202c1411b006030740b50040107080110b600a41d40d107020b004c180d54201d0001456a80040380800c0340034850048628a00c2c03090540d4840640d4500e5030b0b6080d5141a0480e81300398a5840d01d40c50054000d200700b040c070303c00046580040000710b43d115626408144101154120001081948a0003503030203140101030003020584018850000259103040454000022031000d904c1d10640f10400c0300d03203041036045200100103aa082440b1310304920b002a52140c1448000c041e5068101000c0c09171880030161340c4d0000509124803104c2a081d0b07079501844c0500d20b854032000030f040303850321021a41d1203841900c94030840000b0b85001841d621460340288800568610080805004002d5146100e15003400034400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 767665899 1250 767664649 767664661
    0x160809131a0f090103060b060717040f081911040e010603080d1d07090b040f0c0305040b060a0f05040203220302210c0a0b06060d0c020309041b050a1110020a0503040506 74
    0x10ba012900e402036800101680100300003051074200342c6c5a194060700d8241083c4540e03943c000000181c8540c842c0400d0045000d011160705070030600000c100e207100078200403102d51903c41403040d00304005030038204a2104420b098450b9001091b58000c000000c003c203c0d0b5030b062082041d041140300d015103500b80002840806960078000780c400d54080050b2a409141600b40320050803001070644c0c2043c0c40d051510102071081c4074414480310140c0700410980303071600e00b0841051000303203050b00c5050404420b10135a0210f075540d4040ea402503a00599135240c416006c102d0a403203524829011100e400e0740c200309903010440440340300c5a40c4003000243c5281c41034040130700945440c1b007131643c82800400041003c503c0c425800503c0a0505c52801a0156000c020b40d140b60a1980150380005440c1c1d215081c64400c00e204282d503100110b0841c1e941d4140240a403041000d110200281e940c204c0e081c010080c44850751101d4003043c11982d503240c0740c42c09400b0b0740086a06032207500425000900f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 767667149 1250 767665899 767665909
    0x9050603100f0b06040308120604020a1b050a0f0507060e0d0f0201050714060c1803010203040309030210031b11010e0601081905070504020c010209090a060506160809131a 75
    0x1015100040140902103009a10300000b40b8003998142155501c40003856030903252100104003450146201c280e40c3c04e041030011021a1018003058001d80c410004101d42c542c0c004110070800ba41c4d01002419034195092081c609455a4400703455801c02d41d90f41001c20200045078070880d40305032160644003501300704100c42c215801001a0664448146000c01980700d80020449a44100505134031780c211200b5a5246c0141210b10401a02000500e0070841070214409400140c0c00c030001c2d0319518103560010300403511440002c0c0211000025500b44c640240c012060180b00510358040d014030710701c4010590300d04014115040c1d4038101c9504007140020404606a429803002001c3c2402c0190001191080c030710829500c40c00798041c04951aa194002071454014150003da29288180104449100b010346200705032841c2800030400d43d01c1366000d8275403403500c40c0440e00e4004200e0800180328841c910005070300406181000c10b42510b158060038060000f03c401034501001281400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 767668399 1250 767667149 767667151
    0xf0309030312060d0c06020d180b0a0302030702100e070e1f0e0c04030206030a051512060a05040c03020306091006061b1104090c030f12090b12040201140c0f01060905 73
    0x650141c00400072400e105103828103070341d0412005441e08280c240713a81c40d03140e5018055080100140c07c46a51101e50070750140300750400030608030203070792541d2500c02600c08911a011400080c550003000041c2000d000348100c0c440c14440b00d005114104050000d06d4942d0098003880c03007050010404216007940b0306071103030042e000c210784026800382810054110064010411040c0701c0c002c000100042e00c2d0040950301502c44100041344074140103803003241c0c280f03500101a010310400b20504515280000d44150403490880300000c20f51038600b07118900c00003d40019405104120510482900c0001c007c1c1101003841000c122180d1200411510442c1420079243d01e1003007080a82e010401242036000c2c4040020030000e40a481980c41900d9001164070940c2c1c807801c0c5c96014800d22600d91122505041ca03480c0c280d040604050100030a4010342d0030702061080f001c40081c0031a4043c007a6021311140c0200701c00c1d151380f810566295a020301180e903040035400d00c100002c40c80c5150140e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 767669649 1250 767668399 767668417
    0x1701150e160305100b1305040c1704030804110d0b16050315011103120f0403090b12070c050c130e0c030a020105070f0606150903050c10050f0a0e130e0f03 68
    0x11140c800c1c11104100e020b050040c10f00045068540d00c0007410802c040020036100c81c407642c200240610b032400b00000c64011540d01b0701400701c840e10418200343c408069940c099814288211903032201e0820701103c0fa2402040c075000f50345d48100105100117604180c2c03183c4100d0360203501c1c1000e000022242d9000655a04040942c0f1120806042d03000303881c0140040344210440303042200d140201c005008054403081c0d1000703045000c1c001415031200ca0f80303000c1e00e00c1090080c80c20074040700e81c00078248020441d00030851120b00e0700007048001e0040180840004044040c8500540f411000030040600026214420001031903500e080118501080b10380507140c150078104d80d81c9a070100804554000c541d05551110042095094800c00c44450400b540c4c0e000d000d075045250032071814205c04081d52054a0106d114110254404103c403154604e01123410348900c2c042d881960418280e10100b07034080303002c20200008103c10781c0700103002c1d0424411128500c0c006041d40e42c59104040304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 767670899 1250 767669649 767669671
    0x10c030e03040b160c0e0403090911030a020d020909090d1b0f03031104091404140309030718060302060f0d061a030a09140f010e2104031b1701150e 65
    0x42000740703d24a034040d00f401484005a07519014040d5505007408840f80c01c02d491a6039620240070606500114000c0074060f0300c3c00c00c024400f50790004400600000303141a00140e0001031721a004031040e0196080c404001d4001100e070308028020035107407800307108101c000030382c4610081c14088000c98044a62500419003035030306006624110080c09103201c645a60600800000540c24607510851800c0014608042c104d4205440c1c42070001185e0303000d85925a0050118040317990f004a118411204001c0582034145032204901002d0301e0664000380d4004404140003129141c49070090811506412080101d03d84035400140010105000f104542c0b005000145030301045038080f101c45070081c61803da00c4100c00b058071f481c000481d03000c401265100c502081c40554100a1000081942c0001c5e00442ca020501001c82d030043d84400380c180c0a609554540c198148104030340508181c003950490317050a0308c070b0716001e032000941d0710021134131805001801b120241c1e041030054403400c3e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 767672149 1250 767670899 767670907
    0x20d0903020d0c080f0109030206061e0f0415080f0d031509150b0307050c061503030a030906060b0c16120201170402010212130801060e0601091806050a0e09010c030e03 74
    0x81c40519001c5140864183c008a40003081441040020780d1880380000001b0956510500e402409e00304003400d054000e8940005241c0c0007554842e0368080070a0a481a00c1c1382c0340c43d400040c0281c490075100f00403800c141140400c8000c404500400640e9120f001c031680081e901d1001c6040352200700a202c000d01c0c01381340c00e000d44106034221003900c088110340310310a00e03103c114081d0140d00540340718020803070000d0142c04160040c031079070307500130003e490700c0c180da944682c0402d4480c41066503020406a03100070500c1002410b81c030150117000c0d1581c0c100d45a40f01c0340d5000341e6401800807400c40c0000b04e1140014408003003010f40c441c5590694452041021404404081c02d1010704101e055006410f070440c040400c800190403964140c3c001c10030041d240501c07147c215920380d0045040942c8079402c00510307980085501e0120780b02000d4a4289080004000008150340c0d00314030750110014100184c5c20341c001c2072250003040c0b040c008203d08421000b054007102c4030906014450f400c140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 767673399 1250 767672149 767672153
    0x3b0606010c0312050a0c080609091f09200315130201030c1e0503010f0501090b090d0c0e0702010504030e011e05031e180105010b03070c02040b1f0f0807020d0903 71
    0x860741e01851290410030040d9414801c2842602d9040b0b0700004800e030744c2c0320318076641075000c1a4140c01034001d460002c0107007003001042e900d45c004100450032030300190140541c2500da95000c80b1a15801180303800c206491000c14400070b40d13010381c06920a21400007000c04d0900c1c2144020700600e990003c080310501c495005402410b50340c03400c801408002d44141c84007142d00c01703201d0071407012640c8007540e80d03041002d40100142650840d904110348114181b142e0710881046442d110001c8681d044040f80d00d24103110402100e801c10003055078408280582c0a03015004103005610070345070010012041d100448403135101c140701c0c1108010a185081c0d445028000640e0002d00701403010b00240c03401ea8280c42d54050594600d0819440040076444d040e20a02c0348034003500d8000f10103491814111070060001d00c050070040e2040741d43e08180c0b0480e9541c0343c0c2c141c500100b81c0501d402c14101c080c0001e0302851150220381d0128071a140011001d61003c43c0741940014141c88400c0424190307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 767674649 1250 767673399 767673407
    0x51e15150f03180625141206100309020604030b040f0c06111c121a030f0307060c05041805060604120b0609070905101b0203030f1806070f020913063b060601 69
    0x3a181c00000c2c4800907410381b90024a24004000e421640c4404240c1410b080b01484644040c1e85172005c10149403140c0f101c0142d45400848085a404c0010440103840c0e5081000c5c2c04e1200003002407007210b90040009900790440e212401c64035003101a41d105014481400c01c0da0420340d401a800a03510395080c60800c83c0c1c65200c2804107040f1b1a41c2d448218011002c2443e181c030081c0000000d600200d45d20081024902a1002046040c40c0150030103113030481500c000403480d40345407aa6520b601c0001c403540c42d14400e40b0010315030702441c907044902d507080124004006071092030191100ad0001081240140a130f001100d0024102a2100c0000e0004681e00000d03c220320ba84142c90500510140c0c3d0200301404040c14503240c200d94407800c3c8003400c024401070300d55880c0940800d00c0540046000000c00450564042e11024010f0741d5941154035640070114004003a0f074a4141c004070074030511100005106540d0081c1d03010000c0044a11111292201c044485540000c00060320780d446 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 767675899 1250 767674649 767674711
    0x1308330610020a12050702031e03041203020f0a0b190e0c010c0512040f0f080f0304030b0a1d012304051e0a0b010b0d051e15150f031806 60
    0x41d8410b480a28401c0d80e5401c009003440c400700e6000940106141013549018414030001c070724040316100e008240c20b0020343d20ba00540c80b880034021821078410050500034020209030090700d00507151315020600d0004924007050301c41c5142c1001201440c01c0c1043e02d8411107000100f100d00078041d00007418011104103c103540121070a000c2da42418540400000150003d81a2a10390016882c01e01c2d07505880d50b45143c0c8885034540c00b4444e014001d1202108032010750750032007001c4001d6915a01020301400131180c062a144e24500c0d020b150110041d4414400005176281a0f0035101e6051032010300d024060350081d007503401c90b6007594035140d0b4404038898a45485800d40340b0f0080e660701d030032046c030500b64400380140740c0001e2180c221030024420b032944100c0d0603c1141e00e50203401c2510749003500041002030440703031942c8e4012180c2e46240020004034101c908659070f5180c60001c02000303400655500200d00708417a001000c07001c000c40c21034803414003110249544442501c2e564503500c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 767677149 1250 767675899 767675929
    0x60103020423041505090a080a031a12010b030607020d081504110703021b0d080304031116030c0905060402041a0306041b0804140303011a090613083306 67
    0x2c070441c4900c2e00c60b2094030814031450154040c3c40350018119190415948010003801a6070000d56250002401ca0421b031040c0403203e25001800150080d42c101d0000d00400f81c0603440054400004200b46054100082182050713090703900d0b07a162498280d0380c455641e001040481c54180003d007490207440e5008400c48401880071800300500341c0b03014840e030b02160043d00160010200c1d011b0600c90304005000500c0f0076601d0794190320450311207a20ba80000341c4001e040000220b00421500c504011100f9541011a0035145240c4e581c5424114030031240326058800d0305100010707400d03282a100390b0f01114042c131440001d00400540d00162540000c1100b60300ca9603401c40307195110140410071380300d032100303440309804d07420a403c1145114460045540c0c25610800042c480c800700c0f200c907854032401c5442d03001d07244c940c0302c1c0c001101805280501c0100d41280b4800140180e000210359620721120066400241c1c84041c0c00742c162030720442d00400f001a05800b1030b625040c00711100c0d030410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 767678399 1250 767677149 767677181
    0xf05010f02031506070c0f0f0911040e04120e0307080a050609010605061e040e0c03040515040309051012020f090111010c050f090402071401060617060927010606091410020601030204 80
    0x6c2d4680401008001c06a0890a15103815100611245e02907116a100d03414015040e241820300e0094410030407540103000030000702510340d00c681c0701402400248400e0000800340c601482d25200c7c203544c5c0e0912402d040e1024410071011034180c0f68103100e00710a60300301400180c03500e000a4003000c890070748035007045410030b4101b1000804070311403103c1c00c0c041c550700403202da942d0500d41002841c01040510049141c040b48080c0000030b070700204c4071000c80c0da003030720507411300c14403060103a8906100da2100610701d400041d1169914038910300910448409803180405c90700300401d00c5003207070303400d01c008408180c0c05c00400491400030006040506001040503151410f29a40d9107081d142600c507104490307440c0d19050140603007040d180dc50042003550750904a1521400081d0308500140465480c4014900010001081c02d444610840d001c1c000030b0020554607000140f6a02c0d0703501c50f411b1100800b40a2046924004a00c0d6002c0703080c42d0b006200322b07400c503002c000089c400070740803840c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 767679649 1250 767678399 767678423
    0x906060409050f160603060b0a0905040b06160506040302060f101e050415090b0409110607080f03040b09060117031e1606090c05030a15020c070905040f05010f0203150607 75
    0x41000c000c068652180c0415130510a4580f04002d81640d07103680004c05203030400d014a00140e80d01c03513014070840e001201c01003207060b100c1001c42e43c103105521002020280341c001c07500c1480000a42c26020720b00c203a0031070340181e41d0703204094903a85060300d000c00d490030600e20130450320398101d20060f044045a0110316840e651040000c04590398030030f0b2110380c0802e003071007000190400d20032100c4640707040c2e506120343c060300e40d80c00c640100e14400007403050601145581c240500d0105850300302044440712035803420641403462681030200c41c0301a4610a000001c2200c2c20140810400e0384040070055040420340e80070f00c03520354940707001954111400d2145a2100c01d150018610403805a0000036003071032181040090040182c020034003030f5001511f07540002b01842c3c00801d541c01c40f05001070b101c211768441141808903940c01240458140b0042c4000c0c02031000848620700c1c4104001c002d0400300341c1e0001c0c2079000440e4850000317404081c4c100c8007402c000e4010b019052196401040d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 767680899 1250 767679649 767679673
    0x4170403120c210201140702010b030c090907031a0907050117040b040201121e0509121c020708030103230f19030c08040e070215091b03010e0601031514090606040905 73
    0x8004040080c200146c1d102c220040820820800781500404644028441e9890440201e95070324840c05a15000300c8000000603070003c4140a00f80c05141d0144284807592100d43c41d4001c0c0c07080c180c814454501030300d00300045660003944801d0f02c041d0b020500130403559a503243e800d6802c0d001442a414000440314001c42144c49100d0340010b01d0102c2400d0310b5100c9500481011508014001101d950141c84076101d1620000c080e42c400400780760300d071000005810300810281c050114020001c11000c07002000301304800400c80c3c011595840d00344c0120070095040c43d50341d80c034070258000301e8100060a10345d151004a8190450340030707007400006e400160341e55410580c0240d00001d00382c40508c041c4500d083c2d06101d42c520407841b42492107403c2c00c01314076050319040d030280c01039440c92020b41b100328507072001e40020080089100a44e0807540c0d590900c00300072001401041480d80c50301059150170b0120140041c05420600002c0c20746075100814000148142d00087e9800e1150040540c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 767682149 1250 767680899 767680943
    0x507020904061b11070b091f030209010f08040b041202150f090601061701120609081909050a0305030412210e01030f0b061c022104170403120c 63
    0x10241d449500d002a1902c03520000d0a420183c642d409000c000e0aa41441c07900d01000482c0d50665107009900c69840314054002070034031100c2103500801c1d1180415442416030107a01070302941c002078a8403400400d40032000c440d0203030f08480040a6a80c0500441e010910020b1704a4403007104e401140c5100d046d40e246c610340c0500c100d403543c2e41c1d540707100200501c80d0400c0c03090701d0060029080040100600f40e5181418040c1402110940c0802d0400401030000d035030040e10243c1d401c40c540d207a0300c80340c9400d01480580141e8081d000300348190030005046c04d018805200b180e070403201440c203090620b008015416540c0d04180e40380310400000c540700905800c1c0c00c1c1010041c80c1c0740c11540700d060758005801c2d01d4070b01a050100780e280010248441d02c07444211100407a80c00e4409200c065407200031030090280c04401e440b02088039104520045000c1c070054020f034001c0c8c4449134072444c02c1508510b1841180001802d4030204c41c10b403803166008103c100e03601c1d44140301d45010300c8104100c0c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 767683399 1250 767682149 767682151
    0x6090204150807031103030a1205090307140c030124051c08040f0303030c1e0c051501080309130b0d080c01061505091e060901050a1413030b0109050106090909020105070209 76
    0x1641e507008004101304100803480708514604080e800385040141404000d00300b4803004d44510307917480d220000642c0220051003198a071561140192141401c0950400d950742c040e005554080c0d031910b040107140c1450704083c0105c002200090302d80c0f060926062080e903402400c1400c100a102211180005032140040c2010b054880c85181a039465420000c094a160710350380c40500c0380c00c3c0e04d001002e4a20b4010a262000c850a0024800310f503440c0491600c4040c1c2024480d00072101c00204080e40d0200041c0717002c902c21562907516000c0070060130111401c1401296000f40c44162000c000381c007070f0000e050210b09404c00007542c1c1d40d440071841e255006009442002030710006070b0030542c1c40c05860031585204004116141c07600741c2008200a032003038840172410700c6000704d10050384c03901c02c0031070001c0003980111203030b240c1075105480034488007075020440300c05456800201d00c01425100f107034102c1ea40f543e82e032000300b0b2130502c0c144001e000c0c40743d041e81002010030086001d43c9580c8007032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 767684649 1250 767683399 767683409
    0x906060a03080d11130e0f01170309120c2d0103021c0c020a060903030501170a0b1801020405030a05030c070b03070507081e1c0c020d0e0f010c020d0c0303090b0301080a0609020415 79
    0x1091b07030380c036000088000511050b08801d4100030004103884a07200008252043c0c06c1003a62000b080d0042240c2d2145803480140b9150b5000307a64104002041c40b03070a41007580c00341d00b0701606900407844401074099004102602c001c4103a9107a881a00c0100b80c0c100d41060303030850050320100c0090f034440005a403000706041e00401d444d01c3c010015140c40381c0c07011654003008005402c0c4514141da94203801600913104c03200c002c4803201e049159140c294111401010018100d0720805258900152240c1244d02c1184007400742c003c3c0000ca003000c9504036441040141d442c03520b82550f559036642e03103810011508480103c014040e500c0c00d500300c1c2c0249008440c0584042d03901e10f99090390320545000c030b1040320441d0004051805400d0300a80700c1c035010442118803c01400281004035581c440405000c0d50100030030b01d9090503c42400611426207000e55140e42196445d0040d42203d40300c2032141c43c0d25584800440e5010425079405004a5480240085804429150300304080b15068001e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 767685899 1250 767684649 767684669
    0x21807180806070f1407060506210f1002210a090b0c13082a040b04240e06280506030702030d060f030b060d0303140705030906060a03080d1113 63
    0x20f0020440c1c02c540c00305156400c5103040a610301070780e01c3c440b02e82d02401c0d200912041c0c881d0b000c2001c56588500781e2294101c5400c0282189040c51210741c2c0d034003e070298100c464010007850024110350350086500204415101d1074501c50091841092424001c040c40c106c1a0b0b5180d129000500407646580180c1100b0690384e100d1300300300e560310f040345150780c812181a07100f03144406149611a200c00c0c0b6620680680054540018000c1009481407a200e55030040c6403128a90151702442e8144105030301011169029607210142007403c01400d86455a2009401c030200d00040004010313441102d8003401850f041c5035840c00855080c0d002500d0400c056000070517018440c01c401d11980c0007c01c3c03200c0d000b1000a15684070b61f00701010150480d4000c940c002200c50a06000f0b1300121408000c07442c1c801e0aa02d442e52004065070010388580301c183c0119008100e40385441440001a690001402840c0c00844031300b40707000b000a002c0290880030b0901c0860203c07100e6140080041044100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 767687149 1250 767685899 767685901
    0xd05061b0c010603121101091101050c0c04060605270a15020c09070806040f0b060910051608091201020c06070503060a0503120403030f0219022b060c020f0a021807180806 75
    0x40030340310100000c11400303640e142219107008140e4610214554a81c01cbc2401d50f0303a0780c0c40307141c03007420422510b0308503800904042340015140d03400b01c014401c1a0408040000f103018100c80d55a480c0132800e00950301c075010070070030301c641d04010380041d001d40907a004807810301202c040810801042101c0c0c110104203000d04208945c01e0500039102d40d441a910200103252030040010110302138519400e00980309424001710003805101194030815268201400030030743c2c0c0c504003a29a1151000300d010380c0e2602e44280d440701050082c4c40040d01420090000c540c2d03000000c40d01600700800c019417040c0d040c040010192030a01080800d10281ca2000340d49600f10304000c2c104089018424045510801c900302070030100d04c114184055040b42d0403061070b21900318088240c182c00e001c01d001440d58405800c200001c540c00260b01d502d140c0c00b95041e034001140295103520b121800650000f140b42443c07113005841400a41d4070003040e0038000f1a8100da42c6d003280307010b00c5540005041d40d00c840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 767688399 1250 767687149 767687183
    0xa090506181e0a080306010216270c050315150c0102030405150c0301060c0c05041b02010b190e0603011107030207032006040e13050d0c0b060d05061b0c010603 70
    0x100040070484240c1c2075100b20b40035014070a603510820000302405503034010010074a103a1080c080c03204800982c200c00c00025131191644c00f5003007603824a581109003a60341940a03032425000303c0d026017249480729400d690b504822580d61350030401110b5446440040c03602c00c0488000094420b49004000060703d900d001e01c0c18600c0c1020300d0441d040f00b50070380001c1020342c0781d80c501100e055600c14a01100c4410440c941910450b140d50801680141091110000004000109008021280c2c000c2c0502e80d003003418410110a0080b45c400d40e50071002d0244071a44074120342c0e5401050190000a002c1d031007100c1c4031681c0c2c10106080340140c101d01020401e002d007020b004060881d050f820aa030322000d9800003101403089100304550f00303040000040ba13000559845201058100c02903410b02c2031441030041c01000304010880f03004a60101107a5a82428041d4498031036008000304002e40303800b0800740c2c1401c0c0980194410440c00c00051130410002e0140c00000c3d48a9801030503080400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 767689649 1250 767688399 767688403
    0x40f02040801021c020c070b0c0a05120a08071418030a0b0f060a0608010617090f0d020706030f0b0f010503064902030c150d05040507090c14040e0a09050618 69
    0x303014001e0801780103002078040c440011071003104403051500681d039551394800a00c0d040002200b40079100780134981d8a4008508524000e090b0902c0b0b0303036035828055492200658800d1780c1141c3c51484228284074500f6014120340c1612600d500090484284541c5686c0d0310720307014011107402025080034806e000d414180380c0b480b440a0082030520a91a6041040050044041d81504400880c4100c04a68400e20a208401603241084155041c400b00c0b850f02035903524141c841c0740d00007440e03d2501c401c003407007038428650300c031900501c69a81d0607031010044802c1d410192000f984130000541d810b1610300c400c0e401d611b103c01c0c15101650a80b002800701c0700581040040f4103c0460101e5141005a8000c81d00003a03641c022201c0544403045030351240744a00440080c050784e2880c1500f40001d0003030005d031030411101d0081052000340003100080380c00d00304900a640c41d4140a00c01400848540b850b92644404031080001e824811501c1e04c0d4504041503034a0701d0100d01042d0f0b400382035241 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 767690899 1250 767689649 767689687
    0x2f0c0303012301050c0a1e050d03050f3d05030714010314070806090c0c0d0c020910050a170a060612020301060b1e18271b040e0402040f0204080102 65
    0x42400c02c2801c0850081d0042d8946005a0340188440300d02c05c0d21042900107201f031600c000350440112140384200c140301800900040c0e41401085409000260804246004050407000e00055080812840d580d400d50011692588100c0c151140b20b00400c07140c400f0000400107107000204551460182d00001d4210703004001c595910348134500070400d031144c01c0420700781c02c14010b9402c0d134816920300f62040e010b401014054543d600805107406640c070340c801c2001c642e042c0221110319154070b5050507012404175034464141c1114a03007400f04051540d9030300042c607850182d010381d520440345985100c100c0c1c1064201c101c241c0c80c0360007c481503080c01d03c5084040d001455080380340882e080c509007040c400b08100304003c00d40004d40744400958245072104101c070041c042e80451003c84812040310200310540308005807020000032441e8444484080da46005128482e250030300b03041c200402190001c10030ba8000d6103414056040b0380e41e600c0107000400c40c1200040e210301c190f00f44d624030001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 767692149 1250 767690899 767690969
    0x120f0b1c0326010b0a0908070605040e01050a0312050d140c04060f030b01120c030902040509012009010503220506041407080c18040c080714010e042f0c030301 70
    0xc2c4182c2c0064009884000c060644018080b4262203605096003142c40c480b958201c0d00850060782c0000400907000b401502c03d43c0e9001c0e00420160ba00ca40a01021510601c009010204101710918803d409000181b1224012582c0402d244102c15000c001c2c61a05031035000203084001000c01c01c1d00c1d802000c14407a5001450140061030a000c002000c55400300504030841c6d0707a84807283e540070b001e9481211490f43c0176005201914201d9480c0c1e0003444101d040090000c414200400f4880c140300c104c0340304c203c0c140c440a0031900c402c06003110b90502c00c105128808010050500821020131149110328030810380c0d52034a44c08121a58101003155000240719800f901c021078183c1c0ea41660801100e03110841100c403944d950038004022580e59201c022240541d4030081003c198410f000780c0802401c0c1c8648681c04501401c0c0822210300d004c1a4074000e03d14030344400303403c0c1c04002c2c600d0500c00312440142007803803c810650440d8030070f038481d80803292101203081d942d90b810540354140c48 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 767693399 1250 767692149 767692187
    0x4050708120702281a16060b150a08160302041d0702190c0e1f09141008060a090203121810020111160c091128120f0b1c03 54
    0x2460030700141c000782c01a00420401912650f805071440e0100410f85070315000040d445a03d01185050803401020208d00d0300d8054803c00c0c201300c0e0480c000408032a01c4020596910340340f6560000c807048038025000ca01010117808100010743c100b042c030054250701c0a802d6038040342d410a01006440d045809030201014800c0c0004540440c43c046000c800729685032969803044c0c1e981c030400303a060b100060b40b4440440c2c10341d000491644c00d06e0348507c0c80610304002080d0343d903c4500b1070104401c00d42c4622032170740d840341d000241d44803440e800401c00e82e4406002c80e030001c48490001100f642107220708040850410303a050308c051509100c2101003044900080000340103045200303074203100e2011901c0011100081d080304000210b469140148451502001251800612851160312500c00c42060901c041041e440c241d518140046c410f0f5080d49890785030300459080c10029004110541c402c40b5035540e04c00d03007181c440c43c5042142080c44040c03640a500c0c107103009001401d69a070302d46540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 767694649 1250 767693399 767693449
    0x40908180916121104030f03170408070602090f041a0307243b2814010c20120604030c0305030a02130603060501140708090103020304050708120702 65
    0xc2c00c04040d02a402848600d44400844591900304010705038200344080c1d85607000500106101514680c0c01c443d40c4260b8403034260800030b00314000c12007001c0c1d80203031564104000310800a2490341c000c009800000e00155250440c0f5000501201c888801e4054179a0320007010342d4545c03606101c0d1002070000702800405000e2101e6134401a28007a41488051194110000e2082030100d496612922124030031010561184010100b030603900d070010502905d10307078415441410f82481c03045440c0d0b011141c18201140f400302042d083c06032407010907050221011a260204112403103100003a1207520700d42c04a003603400140100d1003010b09420001da001302040c003000070360013000c0c1c0c00b604e909031a00b035860b521201ca44400a00c11001c885c0c181040540c00082c02c580c060704107070101e40098948410003d2806c4024040780304080004100410400c10784966600a5001d160440d005408855449131980c02c0d540c5803410711003000c01c02d207401180900c21803400c0180030304082c1c512944a00e00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 767695899 1250 767694649 767694661
    0xd0b090f040204050403200c011403191a0d081801110c0108060103021605070302100903050717160e0109060b07200f031603020307080c03030a0f09050409081809 71
    0x3825805800244219181d6000c5024107200314010310203280010080502c503c0d1221000d9075501e40c0811031408902e0031641d40b0740004000b400c0e240b10b07000901c6800141c190b80d1a454004140b503c00c590b8130810450481c06a6846510340304000c2e91041c401141d84e048401d085010356586900e010b41080f4441c051040c0d6980049030110b1115170a0a041c82c4a483c1c042c01030740a030242e0501c3d1038200c1034165010b01408400110102201c2c02942d041300d11a141910403107072611280405401580101c4081280015061303680001f600314005036010841c03026a001c0c0c44100c25031240020100074001030150f116148203410041020550817851b00005a68035900c0440d00d560000d0521080f0802448607241c03268101b04101005040d50401c0300c852000c44030195450000342e000c0c1c407800d0808191601d000a51080b00840203008600f00803142008450200e0300780f100c402000041000001c460322107006e03862a00c0e100d503000a454100c00900c49040501c030401161242c1007000038044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 767697149 1250 767695899 767695921
    0xb040510031b1701290307031403040b031f09091101030c0c12030903080a05071709120a030603050d0f0f0e0303040e010311100206010b1603020c13020d0b09 69
    0xc0302e50000c9980403403201004520086926903002400e80c02c1035103d203448560040d4854034030340450700090390500b4560a0384451640d41511015050381c004c070014004114040c410070000380072070b001c8038540342c3c4558070206103800c21383d9019014030a44440785803681511701440c000d0002e1620800259900742c4a43c1044c101c075a040d2410715940740c943d484080c7c030070400002d4190300600703407407001d590002380107006000c4554150000f076003d80c080b50709080c03a4001c0d80d0240c00c090b5200c4c1608105505012041100900f43c051503216032020030060341d160360060411b000c8640c0740094002d2450514904000d4120b001c20100308510b071800b1003603900010001c1d5032489a150501c141826607020a1031440f0b07980008001c00c00280000080184c80724401d107000c0390540d2150050b0390046d50907030740c520003805920b40600b01402030807000840c0201070394005001c0d2040303035416984a4042419190402c1480800710f400149a201e014014080e8040100c8140c90820f114136104c6031802c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 767698399 1250 767697149 767697181
    0x60403030503060d020a03080904061a03150315040501090308090a0b010608090f0a0609060e06010315020307030f0903080108121c0b030102070516033f03230a0b0405 73
    0xc003403000102c081006510303801500c0044582c040e0007510702d0b6469040a0318650010145540726908000010440d068000394112005078010141030864640900b030030300e40c002c0c500b800341e010b106421000590941480146009500440001403010000d040080400c28000c210300019809410100300161401000504440061405041c2d070b456080c400d604010850111041a210314040c02c010320402d6801100043d2092504006c1a860440e0180d00c3d10000d20020741840001c6200c8000c2c040c0c55001554051001e1400041c441a840c2c8040100c9401c050160001400d003001440102e5040110580c0c10b01800002c0d400c00178040c00c10004d000a01c46e011141544076041303c0c03c15182501501d41d0701d90700038150742913203880038958400c941c058442030700d003000f0401c0f0b40140980004150000e4441407004000420111481034010100c1d90307030000201561045907d60b07041038940c20681c00c10500304545201d0521085240665810711041c5105030f213008140b1202030383e005022 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 767699649 1250 767698399 767698403
    0x21e13022802210c06060d0506011503060b120a0b30010207231912030917310819080d060909260313020319050309090c09060403 57
    0x6210507908100d0a020010304201c0c80c444032200786050302d90340342028050b40b0816a0888402c0ea0b04c920401040c0804400061301c99080000140040714403080d20407409070103401d010a0095480c0c0036400c03582e100d0350408100c1021041400340e01007550103022000c610442e14a100c0110300258588401840444a0003103104100d070f80f200281c1c02e4040d920b4054000e6803c0c60030305074411112014414545903c5c81320301644400921241103c85a40705941d0000c04031300c600302404500385c0081c0040d05007a210146162464482e901924005103e1485030003c01d032403504600c0300490186d20400385103590314104c20401d0000440000307544050740801e426100903130641d800e0654030b5110792030001202904008002c10040381c42c1d00a010b02902c1500c820407881182000c4048801c0340341700d800c038404d200300045a0300c5240310000c0c0603510700042c140d4402158460720f00f4034040c070302d00301258076400115000b94645000f8501942c4406090b5180e8940010800000d507180700354000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 767700899 1250 767699649 767699707
    0x15060301090b0316120302070e09060f040f2111010504170313060e0c0907210b01020708060f010815011d0a1d0106032109030f02040207021e1302 64
    0x403200159404100c3d1800c2c2c82103081030020101d84808070a05d00c800d00020680162185c0d82001036041c0c91304406910401d4800081e1038070341c8907404100d04296014205880085001043c00702145201c03240415010400309185920380b02c142000c3d12145c0701e41f4000a160b45031104201c0400c41010020885504901c05c513603495039800a40e000c10139064001a155a20740825408032003000103090b0b5138103004035895105a503030310701e08030307201a61018900d44440f40000640f010700825000f8512114050050301d2000d5140d8420038642501140c54003140f840000c0100b083d400c040c0408000c040d07011845010075030500c41c0748001070b0f02071125560800d07000000100c1841c200d500c2894004e4401100007001031481d50086c0c0a401540001d48044215004152a049405903040d1003046140c80d2040b01c517182d5102e90905148040081e03030000c1d000c0018a006a07642171055052001e540b20300b04d0001801000d02c100d5080500307220802e1841000609181801c101500d064400700041c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 767702149 1250 767700899 767700911
    0x20703020c15040803031303140c0d0e061e07020a0501030c09060e0d0c0e07080612070909060f09080d0b010903030519031b0f0305060a0e04080309010207080f0706051506030109 78
    0x1c0c0b00c0d0941d00c201d9100c44454000441804400500042d0701101d082c000e5403122440040070f6504c0b2000d11607a4030040003540300640c0b0340300c4140200400380d41600300500c11400c1020f45400c09004607245d01c070340310b600e9000040000442c94010401d1020b0304003840d003045408062000070304840c7c05030081505102d0b075840110300c02c0c1d4030400d1001c0d00300e500440d01216259110b9640d1f805d114292816404500d01d80d0011320305052001d40c0700360903032114008020702490b0000d094020980e81c43c06a8406894450780d08550301310340a8100828801c0e240c00f591145108569011519000003550400059441c01c001080d40002030f03508281607425006009070712000194024040c851881c038061080d0f81c455500c046d01b120b508030038400320351428002c40e1307030b8101041500300d094002e4101c0c41c00382c80042008030f2003190166602c85184400186004100d440d210312540054803c555104e0300060f00754100300c03241c004c0703d030040c54041c140007950000800246131800140500d0300c030541da0307103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 767703399 1250 767702149 767702179
    0x181008241306020403050d0e09161b03021023010e09060610210f0b041b030510030b09030a09050402030411130f0e01060501080603030315012303100e0109020703020c 73
    0x340c104d4000799444422034042d805481006400300c00441c192903c03c00042c000110001c0c0241040e00760802d050391140e0818120f28050900761856980517411441201e400780349502e900e00c04c2a40d2100300d440f0842c0a030344030203200c1c1d0070200160072204031401c0080c240440313030000142d0301e07802035401c42f0240b4441d40e00242c01ca62102d062290344075020044660809001c00e554426601500c22000a00c00f456a08061000380c40d0600d45c95540d400800b410008003030300c26440a6040005e4900d6281320702d82c2e81e240d489603040107843c0d141072500002143d013850b41d0010f41c40381c001c200580d029821440d090315400141c440170600130b402414250715405441885600c01d01000c0500c0070104202c000041034a80240700368082ca43c04217141202141c51403030004140c9106e2061a812920040800b400441e0401504241c1c4103d5264451200c0031052441c0c2c007941c0300e10803210614801d145480441c0b200742106a00c0300a1983c030401054001c2a800b0480c0d031000d180540c4c3d13201a01e0041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 767704649 1250 767703399 767703401
    0x5061f0819140103140d051c021902010b03060f0403020c010305150a0303090302040c090e0415110a020607030506120714030316050d020c0f09070e181008241306 71
    0xc4000150002d1400c022008040d100040c014142d90183d03070790003400600c00101560710008003d900011400500c00401c40c1e00e80c0904004400301c4c0504058201171201425810030304021500c200035075101e6078440b545082c20004180d0203c400040380c3c100d410140c42c0603454071404480103042540b40e800060501d840880018140300020b401d640b4455600c0c10300500051490100702c2c462030402c44944c9510b4070420703150060312142415607d03591201d5803044802e850304c2c40c0042d0102c0e20350950948410b2428060004200e458014005525028100504880000b024140300e00007000840c3e0707100c100065042e050300c0c03200b07204076580301e5108002071850089410301c850301450120f4030802c0060104900818231210f4080328962100d00041001e151850000903403c80b0004c0c0014001501ca04c0300703400750000c0a403000b403c0c0484440c4c82c5070313201c03400c0310404070542c81c8003002c11503d83c0410402c4021a40014101d41010842c040304800d40070207000ca036002c00c20140400148046 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 767705899 1250 767704649 767704681
    0x71403070308091c141608030310150c0515090d0c110112111605070b0406020a0b060f09010f1a09090103030f02030f04060905010e030328140c030c0105061f08 70
    0xc14840c21600b080c00b83c0076986c3c0c024500002404000c142e01c0010388100010540307005030b003030408580c6142c8c14030450f805141c00c070002d00340420030f1030004400405c2d0240803ca45a029500d28001686802d14400d46007462505e0300d40c04120701004150f000c03401408902c4e940200900c1c1c1040441c81d00e400720800751008402040c0b407240b00090561041501000c2001f620788680700365607145a80724042c164600070352142e1030143c0c000041060005401c403e001e94840700c002d215201c0e469002e070100d00c07044000d8100180a28500e4030502c40144007104d203014044494103658581b0007544041046088180700050520070405c1990180c14028001d944182000021164440b82e95920090070441c0368458180032800d52030400e245406c021085030380c0310803140c55444900303007200d071000c03010340324001d000c030401c5200400d919411100800401ca920f04010007140c45007800306074070707084482c0607000c00d1003103071340c000704409070880340c03030a5902152242404402a62842241140406 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 767707149 1250 767705899 767705903
    0x8060d1104090c08010b03010522030c4101060609140f0306070507020a0b030103200a0801090506090106270c050d020a180e09030d1109040608071403070308091c 71
    0x483c2500071640c000c056001e50a03d030320450080c80992a0318000302d03026019030010b0710141e0700803401e07640824014900c1d620160300c100c10800341d540d0f0203081c000744401d48440c0c191a40030940491504403800c0850070207009095802044580e00d41800900302100301e101ea81c00c0c401002c42d01134041d549220074032403034084c00740035a03d440c50185002030980d8404d18041303106141c80780f00441d00c240d801c426a070607241c3c450344101c3c1207040e0700030b04d00c040f91b125414135a0040384210701160b4400f083c0245001548076100900807030078003030780c02825111301e0b40001520800000d82e6900807a81c0e0440da20440b4110600020864141e803c111828810400c80c41c1038580002048440c40768010b8440c243c034100f03140c0c0d94500d203850b82400400c0e08020380b00041c0542c800c0c020905440c0c201c4d0301c001c03416081d005051345404246c50204042d101164802c07802a000100e00f002454034650f001420381d00220060a030340c0d415552101554060b81e2241070083c00c071140d580002e000500071407040c0035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 767708399 1250 767707149 767707163
    0xa3c05041e050903090136080d0212160f030e15031e190c0903020405010312020d09080604030507020d0611090411070506041b0b0c0601031208060d110409 68
    0x50140c1d204440984000c806102041d280500142c803601010003507500500c8143d49080c4090754103500c2d01601d00e80d1a0049168060040c03410305061684140c807002401c2c00f50190642c0425003230301a04126504042c8400349a0800460040302c0711610500e019907402400b02e211842c1e035040c119418007400c1034480d0054000a0311314a200c04402c0614170541204494a40390b078510a0000040780e803d540058101601e0321441c1d1001156402c500e01d08241d80ca00000000d42e60780004090324003e0340256880065030307400400c4243d0611114509509504007803003d981340c110440da407020010006010044081101c4003103550f0011280c01164100710140611521722908080e030381c1c041c511240c03065141030702080b104001c0c0010b41700b031141c0260140009a81c0d41e205e0070500d407540e01d4024403c02c111140821080300341c1010704003801010b4003c003541c1d8107500c0c1004c4090280714408007808110400c0051503641c6c1d58038490903541c4a60801c40309184880810301814850100070824 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 767709649 1250 767708399 767708411
    0xf0204090c080105130c1d060f04200406020d1b06110d0c02010f0b011d12010b1309030e0604080d0c060b03031210090b010c030c0510090b04020a3c0504 67
    0x100d0540904100c14501400c2e004560550314000047c1e000b284c200844ca560b40d2000c000340c81c500e410030f040385c1c0e180d42c00303040814064240e914440500902c031506c1035131680c002c1018001a1750401c0400400f00031410119070b0007015051b0400b82c9000403d009100d16140c006040c0625100420785040003a0306100340040c00355030314003074060b183c2d06500e10300551901c54504000d42c0700e203c9901c0060440d224440f43c0040c03480620074114110708000d4450740d21032100052a44074410100400e10401d10300148804c0d4900c5c006000220800c1d0303181c8940801d000611240704003084070f070100041820a80072456151502c1d001034030107400c1003945070102060f80c40d181000c510549120b1405500460111038840201908882080e080d80d0300083c0070250090010f4051703003a01d0581ba001c0c0c030441e55000e46040060095408610044400c441410240011424011450000b030308070030fa81e54000079100041d0300d404000f00465600d106100c0d2000d00d103404266200003000c1c00025200b4480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 767710899 1250 767709649 767709661
    0x60102120f180312040e0c040e0c0403050c04020703050910120219020106080109240920040e01141f0905090705130e030d021b0a051609090f0204090c080105 69
    0x50304402044040c020b600361604400346808651301440e0002036241ca41090b09089400740c0c02c040007000310104407420000414814481c6000314810704070380d071040b13a44034210702d041420032708070741c1615000340d0040c09404002604441910388021080d02c0440440e4410002168007074600c15035131103e144001800b0300e461480d55458030f0300c0038041d0001d20031075542d1400e86088030710185000e031032518214a01c441340c00d60001307000440c030309201012510603135a843d0716618808561089008440d010070300320060070f2501a0105404502c3c3c001c00904c000380f10355054829008241035445850800700c00150b0181075566000b034414020204018900074001940c0c543c40c0d4090244903131071181041c1400c0310315010f04808030840324069401c0914000c0050040e404c4540c06001a10006808440b449020010801d0f024040d40090002d0401d0510081420751160401c00d41a4140045078012448082a121400c3ea040e070780050351250908011150a041390440b846a50916050002c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 767712149 1250 767710899 767710927
    0x207060504111009080d050a02120f04140603100b030c0c0304030c050315010b04051915080403030f061a03070203041205070303140a020c1e130608010e210306010212 73
    0x1c192200782e4203028990f459000903030380701d04140f03d070070f85941c4924514241140f00f103024007070350301c01401100d500607183c0c030346504550400d00405203a0a4040303801c1012003070f025150804020180d54403891814900d026400c114424001d15004520000c0031407540c4440c0c0e8100e403c400743c182e0a480d2a13589a2800e1544100144100c5110b4401c0060580b808240100c1050407140d00c2c5c519246858a0601480a0440001130b1542c00c42c900c504002007040108940315030030b410550b298005880c141ca4080c00b00c6544000c1c02100900e4840284020310f103d5680200705032400c2140340d201d94491408920b1482280c00040c0c0320b40b601e4101c5020040c00084a1058030303c40d45404490100050000019001e0102c44d0300060303120b07088164803418072004503070018080c04140c50250600101007900ca2104d0582c3d03180c0a5680c04c41040041e00078401d003888495620060405200c4010701c81024100e803151500003424000b01146c140c0e8002c10107890540c8203541540c0e02c40a403224020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 767713399 1250 767712149 767712173
    0x1a04020f0408060741042607060f1409100f080601052803060e0c070614010506030403110304050918060604060f12030314040507030507120f150207060504 68
    0xb4284902c00101e180140240620080310071003424900140704201040089152036110f003000e118003d009003901c080c2e462005001614040546920042d82c3d450680f400d2402c00250301c0071030b04441c0082c44565808402074107034074035500d0403070f150031400c098078100e0380b146003940c1c1c1d40a103100301c01c05a1581c009503054003107040d544521503da07455074015500d034451500030391342914500f540e03240032141c00c01c02c0c4012141c2c50302d400984036803900101c1611100503118000c3c1c00030082100030400c040d600450308005c0070200214825450700d808100c44c1d00020300000c0c10b00821089030b1844e0b01e820000d540003400010b1403d001800d21040e0520b0710b504010421100d03020751400100b203800d0600941c0c1c2242e1064420354519440c0c014240800e28485030101c04060f11000d42c039025a40080340240981d000b10083d0002900e0352070074600e0701d2055400380f030f030705520295400c0120b00d140f410031000360b420010010135114203440250091041c0080185424644000d11084c04017104043d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 767714649 1250 767713399 767713409
    0x2d020601031712040212030c06040b0117150c09060c0105040c03021305090726120316020d0219060902090718083405120105190911041a04020f04 64
    0x50310242d055401c0288a20450009035008031501c1c0101d001401d00f020201c6000b5000c005132414604090f401900f810707816101501c3c035822445c01805000d40003030304800382802400040190540ac00e254451049005040d040004804251901c00d612998120380c02c0d05540f8008216034501440c00380c0e0f50031094081a03004c2c040c1c3d800740003035507002c910856000e1600b85000b407003020304d85044a84c4c0305c1560308035520303c0d8000101241011204008046105410f80700050300c80c070f0040c02440708101d561100504550201001c003800c5900410030b840000200ca280400011107810000b010700800c050080d001a48002002303e400d5001019000540d40c92a06011250762401b419035103602c8021018201b6509080c07c1d106003680302c003d08a00e5403180c041c1a4611750f59000035032104450781c12140d00e039445400304210b0481e0302010500a42e03d4a404104170b80f01d0387c80e040341406058020358059541d5907500700e1000030b000c1c10340b02000d0001b00155a241f02607a07000f220b94000340f0030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 767715899 1250 767714649 767714663
    0x1b0d050a0302010f051e04170408010218100e0d03050c070e0c0706240509040611041203030b03010606080f0a0f0f06090e0109110d030c05011505030c031204062d02060103 75
    0x443c500316452110b00700c64642909007146c00342c8440d20b94022082d0b1607800d12013406010040001c243e08280003030080740300b44000e00004506180c2c1440100c441030141003003042902c009011655071403a0198507030719010314205860380c03481d240d0680b5240c01c6811903030a4801d414208003610842500811030070780700e00b40c2071262002558140640e07480e940c0315000385000099060040d82441d0408592290282c1c501007484a881400340c4c04540c0580c1006240c0c4804a11000074103805015003c0303050030580c002c0001d14900b083c02011110b01030700020000103410081501d15403281c1002c030500b214100100111441745a94100802c814800d02401e241011108a020395040c407422088680007440000c0f650183d03030400126664140b0120184410416083c020070780911030b0551044010f40c040c0308003070429040618140f1000074540c8280e100d006039060100040058038110b445034204281881c20003030380056114040340c024402c020031f141345888507075800220036040720b014800c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 767717149 1250 767715899 767715901
    0x1505040b04140d0219030212030403020a03233c1c06080319021f050109050112031d0109080a050307060b0915090a090816020301050601050901021b0d050a0302010f05 73
    0x580b20783c44100700321001c1c0c050380007510000d40a10211034a45030761417180c410f8410b0744403400e40160803a0002d0b281600140e200d003201030105604031407560442803401c8442240782250103420507552040782007905009010050150b41e080c0c100700340366054514180c0600c0140c114882801158211440c03428480c091441c080301c0b40c0c20103208950a83d0007840c041e41c5004100b03041c1c0366020030b60028950841c031440048207100c08018180340c140e40c0756000081400c2d45800b030950203503101078000201c9500451450030000703402c9020f00c412510f07558174048503000c25200580703000030306034092a000d00400e80c03100d0410001200400500384034038020081e031088074045c07098402c0110340c030410254180b100c0003460b01d003171102e82d070340f041d80004007003044401c6588640850300540f00140c1e60050704540041145003e0086e194401000e00c0c0003402d180003440000c1d51400080360094404911045071b0b46541c40707007468440c0c1c0b95000070031100e48020700d2030001d00a010f04882d0705201d80c0380c94 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 767718399 1250 767717149 767717183
    0x709021c0e1f0e0c1903150605040f110a11030f0409050405070f030b07050711041a040b060306060f180402070302061f0b0301060e13180524040b041505040b04 70
    0x4802c1114142c1c07100f0040c0582e400010031700200c003070900280c0c210703801c81e1800040003814600704e4540c01c826034203000c11068a42800d1006440001004d0304d220750070594050800d610900a8407100185031800703d1103a810b0040e058114071074015141010b4200103008500032805800c191300072480f038000c5896165a42500e90780303403500340c08010014401d10001c10404c6200380040c020302c80c081c03090100b4421000380081c045402c9502c8058032010f00c007070000d00c0c03407a00c0d100c1c60b101d41c0b009864881c0307503240410008409100b44a170b80e0801100108184185150700644610b5000000d4011990350015007000b9644041c210740190028101200c11080e00d0400d941c0783c0c04880c10300074070500b540d081000c155085243c40d000a5000007210900000f001000d00500320f4100031400240f400c20801d06019050809840c24031040e001e41c01485e041c8041c40b544010341c00303500b01c40030351440d84032442e0011031810f103020040c40040c10b020600052000300446903004520803004400f00c20114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 767719649 1250 767718399 767718401
    0x10c0c1a01080604080a0306150806091f060323100503060112050c0d051f0e0c01090f050402371b32010e07080c030a050709021c0e1f 59
    0x240602c0e40c2c5034110b48085000594000098106034405040101e100c1d80c0364a001454440c02c00784c031000107403000c400d100e114141201d155402180611044d42d0401e110403000812108170b1046101301965904621a24841d185001c2c0004051500281c513a0511402905844c021130092920a000c0c84000160142850340d81c0d1501c6a03000001d48012103500c0300304420035480003c00c0d00c0314010840c101d1020401c1c0c2440151100085000013990303500051100e1800d80100400c41c10321100c0201801180c1c0005055000c4880483e40565249a84800303d00500f005c40d54086101880501e004e00d05c2c800c8040300500c00441ba1303600c0180d8038a082607080718a00c982d8000d0559600369040070b42070a4205124110420003000403502c90000a001a0844402004000e56074120310420b1006103001e001c0030b086100120001d180c44810b680b0703265207619a070b21440e07503020b070f00080ca04500d0a01701038420025000100800000c7d020030070f025103904400341d11a840380c43c019030a202684d03032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 767720899 1250 767719649 767719651
    0x1031103090a020d0f0204050f1501090605030c03070302040f03080a1b03051902010b15071101020304030201022e0219020607051624050403020d080105090c0d15030203010c0c1a 78
    0xa108010a9418a143c084c00b8620713005004c00d44070144414a007601685803401349501500076030042007071510308481840b4404201d03e14030b03410000a1041000701d01e9005058980020b030a0303c00e103940e81c84c1c4600941c0248501e500c11421368031280000010b1100d018041d100c545843d88540f0140b1000140e20543c0002e0060000e000c0344e0240105c1e51002c0c800d09405a50a10a00000034404080c00005001160024290711078550008000307040281c0041c2546114070203000550620b401c5a00103920b0303c00c41c1001c6000804046103030104042982c440300c022000d0080c08560307580d092000d09540f480c0609120004d031046502040986204100b07c0721503105290800c240030050b6503410f50908108134494500c01c613000c2c0c007003152491500c5124052842500207241030405c40e503018240c554140d001c3d40c1300d02890020003c2c0c0c0c11000b0200c80141c0003404001a4100300b1440c4c41501300e0154001a41640ca000042100d85030008460864140541e401601d0400c501c1e4035540f82c590 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 767722149 1250 767720899 767720911
    0xd0f03060e130f0c14030f0a0206160c0e07080403030534020102040e1602061302030c012601030c14060405030706030b1f0807171b1e030c070201031103 67
    0x58032600003402190826115441c140c8a040d01e10f0241c841c5440d90303110200c0981184081c0c0402039130906043c58200700140d803140141000e0300f030800700c035000243c07580030700e420b0b100c0003405132280e4104008400082c00050010385042c25424140840020215074080700c08a001c203151102040d4505042406003048902c0074901d4031072104000ca9414240d540003424030107564082c4401b0541110440019125a2280007030000c0c803c41c410009103003250180c001b41c0b90440483c140400b680b400304182181003030a00b45444140f0341c100c1ca0071200e451182009440088900020040042000300d03141110f44010b4400714216000040040504c0341d480b0f0b09038194080042081420700941204035801002441c40d00b0064108051003000220007812800181c0307940d04001006411030590302c40380c060001c03200301c1c900d0b26580440d8800f070084034482448001246101e040c103001808260b0f04101103034825101d0800b4918104603030491f0b4401c0740440e0520011100c0c1f6406101a280300d86 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 767723399 1250 767722149 767722169
    0x51605010c0f02060f130b0901080c03071d12031801020f16090e01090c03030e04140103020d060e19030e181b07080f0a0503040201080a0c0c0803060604030c080d0f0306 74
    0x100440d400c100b01c0768440408042d031130710184a83c0a483d103006d2400d4006004600c070702d0b1381c0e4000c01c20006111800c000c01ca00403481c4140f05114005034000c034500b0100400000481400030103030001030348200000310b108198800090a81840181c604d107803035880381c003a002c442400700365440c89511506840601d03035803000c0c070980810816141c3d4006c0c107402c4210200014517400c080c0c0740c19030b001004ea04207601080070304080040504091142001d01e14650483e55825415540040d40c507244511003c0d002c00d4071400040416401800b403504007420713000600c000c2c1000ca00e406469501540b070854401d0fa01006d040c00c4005000050394854550070207181404001c1e114506d41c180c2003002c080e02c1c090000d1000551b040b03c25001421519a90745071143c0724a410300c001401110002d201080a80c10020f081d40300380d03004145000c8483d4032400e950f480b80e54810104400340107541c0064040d8000f640002241c5101141409031013041d80c0d02c8a5214501110903070a45449104400301c003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 767724649 1250 767723399 767723423
    0x316080d051608030c031005060414060a090e1302040f0207210c060203040b0609090f060c0a030207050303010b04240206040f021305190f0b03032a010207051605010c 73
    0x164071a400501940d001d1900740402100c05807240c61281e0003c4030102c000f030100109000d45480100c41e044014141215118079090401200340101d0030569100c60003080c005ca42080b085007d403100401070113101c0d114000504c1c00c01000b504c0d0705440031080e40101d2038901c000f10401c50500840d03101c1c2e50019000f1419110b2149403040c50710480d003080040007143c2804200181d040c0c001140100c4c040d440e4600306003805810061003110117400112154403901110002d0500032441a600007400f0205546038480b245040d00a0311560600900e41d002c0000003003045140140034100356030f815020504c0c0c0c00c036041d24068041080902c078101580c401d5000a000950600d54285040d1018004c05121100000d402c41078031030986003a03200c045009082c1d010100b40303116002040444010034860600104042030710380c8502541c0c038113410482c40c4000e030044036031035030819a1084a40215501e05003410b1481d2030700c0c011014011600c180c079200168540c4034603c0002c0c00d0f0703005860341d505 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 767725899 1250 767724649 767724673
    0xf14090606070203100903031409030a2304030212011b0503010b070209130b0406090311150a2a2604030e0d03180e0604060b04080703110406090203070509031608 71
    0x1181d00b041c50200d900d4428903502c80019038544c02007180302c81c4641c8011901e9103010b803000302c0a400081c00c4400a900600c161460613a00c000103921140014811100076000a10500d0b15031040f6003000e9000b000c441580740c2030000c158000c000d03a4404120000703010300072140071116840300784150b0031083e40c00d1007844058078111440a4004c0c66100b100400d081207543c440d004100110703010f65003240d07920646000d0581240103000500079a201501d280608107041101c081000f81c01140d015582d0035070843c89040540c0b58030350900d9554001d000c0b455002c0801040f030201ea060640c400c040401c080400315594510b0795015640c90f484400348440c8080a1200300c0384140019000c00c444603100c0b16001c500ea2010710b024154202c00c032050740c070b070800500050755110340c0811b20000c4204000c1040311008181c180c2070301da01c0309a11440001c100c00040150515400c1400160703c000140482a40c00c20014000d0b600305500351815003181000f60990354689202d0708056401050607040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 767727149 1250 767725899 767725909
    0x10606050c1c030207170306040b0303160611040807150e0604051503040c03021f0809060f040201050703090e0106030905010e010908041404020c0106060c140715080901180503040f140906 82
    0x700c02c01d003481c00504000b02da40ba203108070381d9110351061080c0c20000c203000c41420180034800c1741d090241c00952070b21943c0742c10400e6541d48a58060300c0b45d580c5510040340005802e0440c1e00900342c1400f11400076403200358480c031000000a504001c82c0f482d900c205543c0c00c1503000e45003101da00421442a1040d8142c211840d540001d20468050206c0c0201100590f45c045106008104540f4032804050a20030003406680d4041c1a0191551003003040007644025168010f500680c280381c0f003030b1101c00703600d420341c0c00d1500c40d040b00325280b04072000400d04e02d506070b00bc0302103a40501c00a004661401d01d0f80c4e8202c4074110f01c0548600c008000a00100c105481610002c0101920040c80c040498140a0854120f44c20072400208411480d80902206031460603803000e0081c0a445050700d001c0c0d26051900c0c00a02640a0020706000101d0100c42175001700c20758080141d0007a4030035454900706460b82e01c5406140ca1920900d407002c5190411030881074240700c000b803c80d01e41d91716403004003c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 767728399 1250 767727149 767727193
    0xf03080403140f071e091505010f0c140606010f030213210f0b0403091d0601032a02210c0a060f06030f0605270309010f021606020f010606050c 63
    0x248561041189000c03070748104200000050000c6910360211042c03503040c5d1492900c907036001510460400425590960144010000321082403c003401114500303402501c120250000c05007130b00041812800d1120004244141302e120240d840740c2100203908400c0d0102d0042c0403203046501c080000500c98090440d040d10307124a0500300c2c00716004600d50300c03441040002401102c6c0502c00d1800c0c0010960051501e034064110095030310010b0f5056034602200d980018002c0c0e04050b00e0307000303c58041c1301d500c3c0444d4040e4004404000741040c03011002c1d507500a002c10f1411501c20307255101004403003980030303200300b00c078600c016100c94000d0f40c4800000e0b02d03040d01c401c0c5103503070303614800030024005540581c040b61041d940495580f401e02201d0300d46c02e4582c45080f0001c466040d101920550120071142100700c242000000395040d140100d01e0290074a141c0084c243c2891000300e10140c00141400908042000070310010351101e038200c480d4020410303116a1607210203004001103c4c100200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 767729649 1250 767728399 767728433
    0x51e06250c17090a06020304050a0b0a0813080409060b07031707020a0b0612010510060f0509060322020a080f06241011030301140907140904230a02130f03080403 71
    0xb0780d0801900d800000e002d9a2103a2010002d6400003404100c14140400c0c108010403240d1740f45400e24100d1071015100d114011706d404a8403080c0c2d40343d9000c0000702c0b002d440190418030703400c010050700d40041c0710700366020490960200d113041c14244010040c252045110b41c1c0b50764040c041e00f401c0c5644403044c00001400041c0e0290100c03814807035021092007002d100d1459100c2152445140100c0603016040d0f4807203000420204211200f1103131502c0040b250402d44440c5203212507140c1d02001600c0303e42805001b03600c10014003000400c0e0300300040c519a041441e109035041c98807807060384412107070900e00141280c01400b501120364640040c035200d14100c0c504140d0315080b0201d215a0840d442600850b5000020143d21046801c041e80038075405440c40c1810f0300c000303410143c465001e01490185902c581c0e01c0e10341d007803802d00c05400384000c03a4000e902501403604001d40715030040e4225180a61450300030031000614400740d0140281140c1d00000101e03d8107013551600c10383d100c498818 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 767730899 1250 767729649 767729693
    0xf0409061806030c14030a02190f12050601061b0213020306120c0307030807151823061b12041103010c1713030e0910140303040303020316051e06250c 66
    0x11090158903274140044401d1042c42c0440281030170304d22000066002c50b0001d001081407040c10b50001540010b2150544036107080640309460707200c036001d070b5020300c0c980c009400082ca9410348461020039005140204411612000b08940c416616651180203600e040d138158030081d01080456240c100038401d160045511402c40c1c1c0c290107804069540e0406403104500d40321030104103100c035040e0110401d801d0103661004032800c4002d166a900e002900d410000a094174000130043d80f840c0c04c03250341e0210500d00441519003801c106007011142e5440c140a5400c22009c100b0040c03046074003441c0403008040400c03071034454034100034054644480031824411030100c611070799540d00c502c562041c0621100441010300381044850155001e11445000784e000784410700009402000b6282c002000c08804030303003040c01e4200035240503041d02400041e500e100c40000d03886080030440034451610204100342c03280c15041d50840c0e000c100c0b03c980e0001020750804500045401043c1101d12800c910 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 767732149 1250 767730899 767730913
    0x10903121e021b061602010f211535012711030106061223070210061a0904051812040317161203020f0409061806030c1403 54
    0x14a0316409600c014809015a0240c0200003407181c400da0104400481603425509041c4100f05800d010541c1c0031001f4140001c0c400307900c1005100361846030120750f014855103061102051148002c001100d8402c0d0174148030a00411a541001c61900000206160a0311409040b481401c0404040a60100039549414100102d4680b00450200c54074100408041c0c0454600c0c2094940c542060194044d9040c4002000203540114003001121034044020131702c1c9540e901e80c44d5440440300000c41c0d1050411080c000c0c0e81e6800100303810002c85100c0100015078590b211034450210b00c0800c6d0300303150340030442d80760242016004185c00c4000d0154000c0c002d14200c0e015410111a6800c00038401c0002c42c080060000700c01e81d00060301c00707150301d440c5408a803a540a00800200101411500c0079105003035199100e681140c075100401d90580d52240c0d102c1c1c0c01c80703015184074440c0141c0304211411606845c1410b01c210300443e03501c49010800c80e40f400c3c1034030390302c418126952680340c0a202 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 767733399 1250 767732149 767732177
    0x60809070b041d0f0103030f0f0302120108072c040204380f09040818030703170a0f020c0d030e0406050402040902030a0501060f23210603060a090201090312 69
    0x1c40030300003034400030000d10042200c0800f41c0c0c4001600510301300413007040c6401040070039088200041ba50015181111111140440070340c081e20403090034580d440444c0c000010800300100d0110b055810000c0301006218882c84214503c0c1400038010302501a101c01050040c80c265000d003419207214214140c003900784403190030b00312115141810b21584100b403001b030360740741c442c4004007510421240342c50f06043c583c444451038041e407032004810200082810390a07030703800c0000d08c0045520502c0801e811b0456001e1800c1c0d900b1000c41400803450040860003003134004110740800201c007030191711140c0f0b580d840c12607042c50405003a6801a54a0001203459240d03800100041d0040304409690790420003068011118160710075020400004102d6400a51220142040a0a0714035095696a60844c15202c91107500c41d6484141700191012a808407510000340c810fa43c01c070700b42c40e016990880074030305171a04070400a0022302400d805100140740354281c20503403041c0c3d14100300c950a0003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 767734649 1250 767733399 767733419
    0x130f05060f01090605180118020f0f0c07060305040812220302070315050f15011704060c03060501020f1515030706021c0c1505091c030e060604051006080907 69
    0x25101d00c1d20000001005001c00c5029000d51002860240c900000e5110071441540e07411034180110210310220f150f850381d01d052690146c0d4020b0b20300070041076680c0d8040300f04880c42d40c44021548418020130000141d05406403141c0c034811500070703601074a400d030f00340780c0b180c1c5442c4001d007a02c003501441e545000c03103d500d1668807005030b84a5002442000d08504003050711701c1d00c44000c80b03101820017081254002c990000143c2182c0300305c0e0005012050b020040c0c440781c40d52850040d081d00303200100020b11035907420440341c401098a04000447e1504012612041540f00b91016540204482142060442e1082c1d45c40401c0b1854141d61b91b22040002e400d0200302d502c41070059200480e50302c2070302111064002e10742c420382403403100d242d25070790760400d440c0c2e4031110031031895540d40c0007851031501800000342c1d190a034820300019800c903010150082c10b203010703528020702c02d100004a0a00b4180710300d44c0507440b01800420800d00e0600c04540000b00200f408926004030306001802c1c01103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 767735899 1250 767734649 767734651
    0xf07090305071203230a110f01151820070c0b0d0203190501140603040303090b040b0a0c11030306090c040b1216030209010906180509040b15011106130f0506 69
    0xe109a400c3c0301c9140b4103000388000300110031400d18480d600124010741580300d0865001c10003600780b047c0c0c842203069400c0c3c108850310301804980d508200b0201c54411030b0315114401da400342001d001441440d241000101d410064400c1401101c915014843c052090050700c492803042d400170440c3c40d221890140705411041c0d40700d490980210070701c100c0c2043c2003510320402c03201400800c02d56143c00388580d01c14a6442d5460301500d4000007180506100b0b0f04001441900f28a1f02403c6042502e0006280300d41180c0d1106814903000740800902d02c07840030702c080e030002c40d8021070442c0c9940c410072440650141280800c91010000010081c2012010f4250104484004500d518205ca03c00c0e0803044006142005c240c4104102d1565a070814230f00c50548240e17160000310700d00464403022071618150841a480043c030003c000400c503120318030368490000d0304a18401300c0c0c2064019a50500700316080380198000303c000401d00650031409510041c01008040031000720ba807600c60901e18 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 767737149 1250 767735899 767735909
    0x41502090301110a08010512071a0c030307201b04020306010e100e01031b0f030e2401150c0503070b0c0904050109091101021c23030115110102120f0709030507 70
    0x408a070001044d5004481d40e070061000341c5100117140301024000d51641e08a0048405140324441c0900c440160241591462034030001226500d0070103450107045540c0315034230191210034015a0300c46a4a0115858906900024000041030448000c0002a400040c102410030001d01c4d881d05556440c00e40c1041941c0c03a81d03c0d240d038030111090004043e80d50100048880035480070102c0c04032a800308080d402c4545624000800500e003040d51800c20f01d0722503004003d543d0359009000140364043c0f280c2c0c1200e00d00d044102c00c840b00c460301036500511204010300182c1040c4036070004a030400c05901c0e40b10582c1554185402e03080c20014040f034000380c00240c03145a852039a00108460004902c1320404240001c2c1040309030071031030a444030035820240041019000b1440890500c400c007a401c81c1452000440e2a507850b95182600d0003c10b00c2800d0006a9035602150300030018421100c0662400c844051940e541d00700032028440b02a05ca482007107084040000401d800b8003072107010740 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 767738399 1250 767737149 767737181
    0x50409051915060501051204080d0605030f010f0e0706020705060a03022208061b0409090804030524010b090d03081306050405010e0d0513031707050f0703060c080609041502090301 79
    0x300c410205000c8890903000761703051220070004140c0204c0d400e011980d010b07510181e07450b528121042050b020b000c4980c0145c1c0c051240405d001e19100041d00005802101034004002c8070390b007824000e40e034200718420000941c2042d4010710183c1000b000401c10000c550030050718000c42c04c0404640b144000080050144500c1d4051012030024408913800c14100801c4100c1038005107100341c01481148116004591f0783c00c10803041000c0345080e140215001419a030a00f8903141d1000c007174405011021004e038a0b0341c0e0020900003503041c00c2e1021072402a1000c11126826076050f9442c61018200c0c014145681480c40e00203055405154440d5101d4800070401d09044140300d442e00c40c0781040101440024080c2a0200c0205020042240c0d0407a092203070a1800c000490440e00c00d541c80605070b8000d40c4c2c08180ca01d4400100241107a106450401c075183c1c04500840716890300703a407903d6000d0380c080045008038944690140b0035007142040140340500d0880001d017100c81d807000701036100c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 767739649 1250 767738399 767738423
    0x1c081e03131104021c0203090f01020f03010501081605071101030609020c07080c0406030209130204090c2d140910090614090901021606051909050a140d090504090519 73
    0x2400c1c02d4000312a100a42c0c0550502666201031a0b0070503c01c00a842c40341e07800700008040c09020008065101c0b4014002c49d554aa401c814000f554024040c09011884c04000f06020143d0948040c091495035030381d4170309020703c82d82c81481160784804520b040585130640403489682d80c0c4014522078010720001c004452074101c08274141400300740c0c0e2500c600d20b060700c01c001584400d1101580001c80a0b50440d000401c0c0c8009001850220001b41400c2d003030b405d002c10f00105c3d60800172030280ca6031a05200381d0422030301625568006010390507171445c00c010500d0706070030200c0781a600822003a06081d1130341e403144448411a06c559001e2241400b40d01d0110f80c0c1c609200340d01ca60031901c02c40080d440e00c80d011030903c8a4498040e00109001d90301c000213441801c02800f5014041d41c071003c2804005014200075036506005001500c2d0b0000a0742441c0100307400090035110a0020344412117030b980303400100300003440c0c01c07401030b101ca0052036000038488410845d802e0105102c2d040c04070031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 767740899 1250 767739649 767739653
    0x15090a03081803040e0405030f1c0e06190b030c0907030f0b030d0905010f050c010603030c0b0901090201200115080f1002070b1506070506160e1c081e0313 68
    0x32204042c1050810042000b41807a1003400402210262400395101c00165115480c2c0180b0314410f002c410010074001049501940350608601650741d109031a0500800b103004a0841d150b800070b4480f45940001d203204d9800e0100250841d0901c2c140c0201035900c41d00c03942d8041007003980200c4540000941c0d074452082440714601c20180a00303015001010606466500034060803080e019072414400800703070b0304124901c204d0461701d050441800902415a8920303000c1e100440102d81100c440d5000d070001034504a051081d0460960160355415001d01851422071080342c10520b503038000d54a91001700d840c0340c098620a0010686440200010071740a01d21a080c074080079803d0b070059004100c4140420010100b25800c90760b50792098800780744800010314540701d200303c01803980c0501070400034102b0041c040c114100e0103646554040b41c2c201010800c0c00c80001c007280d4085540000858080b44500000d0025a0301e064118401d078901c8240c101c400e134008581a84000201d00d83d5502 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 767742149 1250 767740899 767740907
    0xd0507030509072c0c0f071104110c0d12090c0815060603250e09160912030207140303041703090103062102010e01031104031a0c0a020d080915090a03 66
    0x401400583c002c00707402001400d5021102d040c0e00c4801c404116040040f0f542c1c04c00b508101c0d039043c00c18004150747c50310035150035030042444010040c445e82c500001c09840744881c2003150000607110001c2d1412918411f030a071445143e00c00c2c040c1a0541e074030b000d28001200307400d82c0320151080380000d040c0920311185400c0c4002c2d004042602506c070900c10700600c010b050381c0400c080d100d038190310603900030010f004651620400081540c417191903403d00001c4281200c040e102d42001da580c48001d01c0c1ca49103c4a0a1184100c0090040c0d204140410140c496100e5032038444c403000742501d15081c1e0702c0e0b004c11080600d816074410703c2d03000004e000c4051b61301341c452603004100700e5030300c210b11214840b0582080300485c2d4000e41070181500c104035007030b03100703a200c40800c04181c04010381b00c40d02c9003800d1041d0f600b24020141c12011103008507900b01441400e94401176456802131400281000c0102c42900c0c0240020a19200b1480b8540c1e00f90303000f440f114483c65509004152940940c20010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 767743399 1250 767742149 767742163
    0x90c030b0a09020a120215040e07120209010207140604080102070c080f0c1819021803100e0607180504320105011b03090504020403030e09010b030c031603020d0507030509 75
    0x3501d6a4604860303900142c852000c0c010494490f001d40c0c0b044980e2034008100003210f07000080900000c000b401280b000750104650b0b008440c030303586800c0107003d5002054100c0c4200146ca5026a1040804100942c140c48210f1101c58000c0c20440c1090741c2c40180c82e003681c000c49400c0725148107685041c854100d081001d03500c0b0b8416030004190b40e0b0051000310f50f4658000f01000d00c034841e0741001503400e000301351a56104881100c421552503001640f038285209845078075520a0203a01011400c3c15614000e1403204003403407000d0f01460700e401030140c1d02c01f04c000145c5030002c0c5442400090503030700d0b803042808100c4c44139000c140100302da40f142171410413441d45150140180c14018000c1ea41c0c010090604004840402d0b410039845080548482c1000e51200340d106000050120416604c050305010145043d280700b21a641c0b00c030041e092502085a0340c0762a8403091000824070461400610400103031418014030780039603030121009440303044440902094a07281480603400b0201f040e6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 767744649 1250 767743399 767743411
    0x80d1a04020a050c2103181f0b01020706050708030c070f0614011d091e0102090a0f081519020708070210030926160201031b0915050315100210090c030b 67
    0x485e4003000740341110440c07400040c0a01c030780c46100c0030001c7c4003108100400010311319080380340401d8007001c2070345201030121a4103032030045c0192030000458502030300a960b520b69001c0c0005040d96071b00b041014941d00001c400381ca02c003607440c060002054040c491814008038041103c44950b050403040700340d09449a03805100040c0f24810000e8051002c9100c51080140201c440c0051200c9840c440c00390180380e01040d44404090b50018001000038100c4c0215007030b2009455003144442c01184050310200c85180005a09030b910542d0202c280d80140010b601c100c000030700f00201a00815010340911410b000880d03035035902c0c0406e01500350003042104d090f010710801c0d00b914540c030048850040f1195038044422041707544085a010b60412842001007a102c00303112038511a0040c4046c00358841e00103558a09441c40c000d181c400d800320380c4500d491090300c89580000714180b14401c0000105501140031340c0c07200f45c042c00a28012160030f18081e03400c2c040801c1c290b06000d400d802c40034100d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 767745899 1250 767744649 767744683
    0x2090103141c02060610111f0c020601030332180a0b0406120506030705030303090d0e0907200114101802040f0e0703140a02070b13080d1a04020a050c 66
    0x5a0745890303000072800d41c00602911b103582c440b290440140c4655010600c810000d01515000401d107206441c01490840c009107400e104045116000380d0300d075a030a00000c1c00161209503640520001030907583e03803c284400c02c0ca1007602c034031004010750f900104055488125488070300308107031428015510141c05099065841d03e803804c44050203404002c1c0144114540b01c4000801558081c060b0a009080103400c1e01e40c0c038540040c0071921000407045c500e000c95800680e0305041d0400a51b8a4408d5101303403240b0100d030400d410340b01c140803c005081000741d921611445000e484800300e403802141850405a0103504110b040c124041d5002c01c01100b50741706000400400d0700c0203c0b41011203c4101400a080e102c1c08001c80c0500030308900d4079115000d071014800141c0380c6a008151f0796001e420b04600d5a1101619554980300401010700001c40612050b621035296910040e50f40d1884400d480103400c130b803004074040c1d070804400013000c203a0204803d881d514062103071590100d00e2800c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 767747149 1250 767745899 767745943
    0x90303020d022a030f0106032f180a20032a0703030209060421150507020d03020c010e160e0c030408041a0f18010306061b0b130209010314 61
    0x4a4445152110f51900c0b07081c3c4000074000c4a075072024490100c1d0090110001c0c00010384a040c40c01180c02e0001c40c640021070041c900040901000c5494040e43c80b0040114010009645c41c1013a140b6029010903201e80e540c1000c411038030100411310086401d01260039403a8603003090401040b02c01000c0305c101d48880210810201b80d8803508560346250b043c140141c8413041c1201043c69400740f0b8007c1200408110030640140b5240761080c0c000368031079281091141c828007148019a58203898007000742c5c4c4500e0f4500040390180c5c01405268451314000a0303440c0d480d07140340385003101038010226481c8000009000190000b000a5031101c0711000312461410280e89240b224803640c07040b503039040c03a140121440c00311881c040b5603121000040c100d441300210900390280d078600901181c040380c901140029034074050f40c507034049807800c801081c0710b0030320395122411502801001c2c4503d00c080d0344102801a41e40c90b5502d40030714003e000284c00d05000c481100c3c1b810008400c4881000382d041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 767748399 1250 767747149 767747173
    0x6010c0b040b0406150807090605060405011205090327040b1005030703020309030f040b0d0e0d1407020a1d04060b0a050d12020a05030c0307020a09200f07080703090303020d02 77
    0x42690002c1c2d02c51900111962141032840081542c0c181100030980300302e80018007000006a810240c9466060400c05035946801b0400d140c07143d88515400702c0d082d104651f00140d107903402541d101521800b030f00e150220b41e40c1c40c0449640c421020004188092001000310b080522461555030000c0ea2401041a440d40c800fa01034000200171000709900000001c001d00b10500039500c020040c0b01a85807034949450190450382c1041600312900b5180001007403910310002100d076818aa40c3d22000c0395140031060241d5682d010709003d80c0c1208000724000f5810004e0519102c0c014000e08900815080c1450f050003580d4101c407480740f08000c40038042c0286c0e0749000240c80d400b50302c582c40d100d092400d08026801c107a0b8040002e807060201088003542410301100809c0e680b84220341c007121054850004400711008200c88040c01c402c03510b29001c0a180850040400201e00040c0a0909400b5036507505254440c83c03085001951b107103070400405030108040500c581c0c0314005004c0541c290 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 767749649 1250 767748399 767748413
    0xf1b0206121033031e0b0d020a0f17070b27150d0e0105010b07020d051504060207060f0506103c0801050a0803070f060b040c03060302030606010c 64
    0x400800510207111804074202c0e66010180c40d000b0001c903015904440b20281183c044070060011400c1d0000aa22169105a10170711440c11084410a03070014000028124030700100020b100003a002100c013600d00002d41c1c0e81e4a00d24004040a01d10100100d007000200c440000b018290580070b41c1c0900d20500c071a400700c0c0156402e0b9002c0300c046103c81c03805031034481e5507003510510103500905c003060561a0005014014400440305140510241c601180c0207422200241b280c6900848184040b000610381821301e0400c0314060710440300000015040070074914401d0b141145c00700e0b400140384041012502884980302e01114040200b1318000003c14122a20919107100b0030078412041c12920300001100710010340500458040600700e81c00c2d4811410080c46500045032400000141c1c13890502e003ca03058900c030202441c00c07c009076a400710030010411003143c01030384801d0079440c10f031141d02c0740441104039aa40454180d10b1030040c141404400380c10705041101c4440300300c0102d044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 767750899 1250 767749649 767749657
    0xc0c0715260604021e18041b17090313180516120b03100905010e06090f07030303110415030b0907080c040b1c05130c0b0a0e0607110901060f1b0206 65
    0x2007a90b01603902e00317038080743c8210300d000710882c400e0000c0b01085408000c00c020181c1c200070f00003a141013154416200c400c0b05400d101000000c002107194401e070741c409960f54180da4103c507a1038112428990341918040c06806c2d82c0d003184040003e0080b11001c2c003a40c81c0222908880208a040d440c941c40307500c02071a000882c070034000e0890303d81c0844a500e072020081d1007001d2038010002c002c00b540d01d01d00301d4081d001e40c40c01121644607440209501003000301e0341d071040b00719803002403400d00c2c0f5641e07017034010f0030200c7c812480c40f6109010006901c4003512814107000300d1682d0016082d0719000400500200203070005081100b0002008400f04a0008030b400362148031407034039101c5200c4440315401d10011136140500c5811301c000d12070f405480540d00c11429100c6c001607450b01c1e8403000f0140403402407001d40343c0050340e04203200885050080043c00300c907002d210340100004109011416103030b001ea01040015405032218030707040c3e60050842c0f0401880000310020030740290000340c000c1c06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 767752149 1250 767750899 767750911
    0x41b050f012303130b0a05011203080406090506010902040306050f0106050a30050403090911090d0f050105070f09050103020c0c0f012006220b010e0c0c071526 70
    0x1280401d01c9801d03400e201070400c001032000402c9992841c001001110013415070008984070003140b800300e105032445000e071a050311200e02411565020700d440c1215080780107802950300c59a100301c3c00700401c00500120b4082c0c0042140543d44d40c5ca5441e0031001c5520003007100010908690051103a00e034000c0c102c40c8107906500d4080410340802c00d4540a0a03d01d9203c0d0191004520006801074201c2d0031482c8218040e03215003440c113a0381c8001106464503d41c40b040126000c000320800d41c50718000c2c407154240603804480300c90007250380341800c4440030780711079001c24007500005403400c0e8440b0f00300e40902400e00e425400c007810002602e984440e00002280305000e2400c80c400980d100e5092101301c0c0011012449844d200b400140c0d407501c0b815200c100202c4200c08243c2c00c003102d4007450b00440e81c0e002c124000c0a03881d06c103011104040c090030460440340704025074000d01d9001c21100025140c0d42900354242e078080750380a8949000c007a0b406840c5642c6c0700041540d11552094140c0c084 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 767753399 1250 767752149 767752157
    0x1180905090f07090b01080705180d06091e121106010e0a0b10030f0f0225060b060c0c0f090c0d0509070b0c010b0a08060903090f03070f0e041b050f01 66
    0x10700d9411019080c02041481d4150038410042c0002d514a0710344c0042c400e805003030f211101d1903203400d6000c45039481400100c880210710702d80c13034a0403030801e12902110b103401a02d00180d900c450743c0d2707800c40f4080c0342c1c00c170700155070303c68025881841200c400e141626512400c008616421440d01291121814130400511004120005511102c3c2c2d42113185184070040c1084500300d440d107c00780040000c0345090040b2071a11008013000d00faa44204c03001035000602035410106070b25030511405550b03031800c95400381c40d00350448032612528090021540b4003c0170381101401a014070080d0031003000b00c103200720071560520221141000403100000e81c4c0c00c030080f41580d00c00c24414548540d070746c0300d240d0620700000c540d0024070041d44840c1080100304c405172495030382c2e40e504030358640d8103a5110300c158208118085a51401d40e81c40009501c000e401e94204907681c07410000c3d24282d40d1f000410014881d010042007004122203080a41d0150520203006401e0402003a0400342c0340780705034140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 767754649 1250 767753399 767753401
    0x140106020a031b02060403080703090f24090f090b0f03030310030b1015030c1803030e0103090606030605010305011407180509191b09060305010b0730030b0f01180905 73
    0x140300300b030040300340300e80c0240c01e49a8487d40e901d4a003c0d254010300007a0002070700e0100200b83c000b40b005840084850a40e80c5a03091100d1580d0850882d40d025450820f00c06e40d010b0019541850b408407030002e0660340701c0061042030600034400c3d40d001900b81c0d54401e4004000b0014489000c00c6800d00390b0b038100307405280c140d0f03801d80007501c1a08150407020050842d040056016079068220442221080e900c440310302660009100c48a026400700030042142c01c03011005a510076800007140900900d008200b00e0f659844d0035040790420f80080c0c88070b9464a23403003040e000c03400e00000d8000703800c1d203000b00400390350300400203405001d802428407803461100894407060820074150030780000104104840f00c610001044c50f0f0000d12102c0c40030581c05500090b015020307218244c1201c0c1d510304014501001c59031138508103aa4032001a03481c81e410016200c81c201640d45038220040a9203000170600c03002c000b005407244000c14034904018418407004461040910148102e5034802c8000ca01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 767755899 1250 767754649 767754677
    0x6050a171005130309050603091c021906050105030111120f07170a0b150406120e0a0b040b06040506060702010c0f060b181b03010f0b0a090902030a05060301140106020a03 75
    0x4141d401c9240c0d00c511802c00d824050381c003503c04103020003d0b203c0e40700c004038166940305010480c08101e446500c04e402a040c0b01080c2100101069400c4c00c0610590300c80c2d802d05050044810720003034060381c48541c1c5500511081c10244601004100612035a81c14194001c070031b01243c070402801c0c4000c4e0074015000c50402d078020110b6074821401040006400d2810420600040c9040270b4032510821840140308441c84076501110300313070741240da01d254040139050300310310241c5030443c0800000e11540314010046602140303030701c0c0140d2040d0310010890420408103c207032000502400d1064000300460b40060381c001c80507102c41daa1113805481e2810080c00d0000c0144415120700390440c41e452032500d042e50030301c0341e00380c402d601c1e0b6000131800840141401040e80401d0080b01550640040c0c21311010100308040c20a183e0300345054810b01e511140c0c50416a0810780304014507580b2401030141602d400c0c041d0840480c00a210000b5a62401000070340c3d0b0b411020000d0306005070421800a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 767757149 1250 767755899 767755903
    0x60b2205040920011704060213060e0a090911030d0909050703141f05030706020d081806040f06090c0905180a0507050d08070f031710080d080702030d06091e06050a17 73
    0xc100c0d0354031482048511b801e040c1000030f0740c4840381c801703599052a600071441d68016204406180d1000e0072120800782844514401082c13940015910488220700368103080d5005c00281c01a02001e6642021003803a050140c020780b0b0020380150b050504000c030421303026134001182c1d5031001003480d04030081000a1809140d5907055007040340c05000b480008152540c00044a00101405030b0724100b075aa00c40d5226540210f0303d40350400d190b0005c4011a010800e000031800781036000d00345c00140e1880ca41e40c0e40da00308650342c1c0071038261521030003008595450844203c03030303035920325000d807548450035941c00d43c41c0e61643c06454400d101801005041c04035100c10b46041c00d500425120802042c0e044c05000e02004146060401003500000349a1000c20700806045501060042025422021045d281400014030b08001c51005000d40180c458050065600070102040009192a0302c02c01080400044200340088182404400c104648420603005d04490baa80e055031000b402c0104814 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 767758399 1250 767757149 767757167
    0xb010819061d100501062a06020918130218040c061d060f1201050a1a18091501031a090a020904150308040509070c0809090a060b220504092001 63
    0x2402d214443c1041c3d00c01c1100d50103617060307484540b034195014400000150f00c1d010013040707c520316110300020b0303800a000380e000fa2000310002019201034008103034007180361101c1221403840c6200c00341c0329403065041602c603004200409001310059841c01e900c03900c001c44214800e01c010080481070280454040501651450740000c000070350340d03c48010082500e030050f603409600a1002000081e80349080c0c0405011144041d09400040071410141d08031900481c0701d0514240451800c1c0c449a0f54850400e0701c85c0a05004030781d03686450a00050840310440108840301404001c2200681d80b141e000d10b0f4041d5803c80f01590fa19100c2c0b01203400341400003c0605415003030000403041215203005072050f80c40a6510841d281c0d9500c0088a5047c0710f10300140518404000003c420b0038151150b1340d101c41e15442c0421003503a11000e1058a81c46120741c6800c2d10b0201d548120745040c0620f050b40140012603044c4254080c60311804825542564545a41460403021050302d90260841c6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 767759649 1250 767758399 767758451
    0xf051e0c0304080c0a06090e010306020703090504020f03400c0b0a0903110301050c04051903020a140f0405100e0411031009120201050c0f0c15130b01081906 69
    0x10700c0c0c60301e6580e640640d84245600c96544038103541c900c00b10300360384200c020508440c040307071a0101d04c1e440d64035503100940c040d940a81c1007200d550070102e4030b510b560008080140308204015540e15049990b070000b14644401c0400d010101d0708029020348440c08542c644001c0c4444c50001c2c540c442c03401e5007010059502030f001203100450180f0303000d40c2103148030741200d0007070580761000030200040508139001162105042e4609210511290500d08070801c03131607620180707034122107849800040d840c200700c0e4440802d442d141e5107851800d04091a103a041500286c0b010f20660400700c40e11b03400950745000703480c0c6c2c2c14003c40008050000c16643c075180b80c403000d415148600d110302b80020140c82290401d40791685100440024244148070b41445074456080c0181000c0070350701c000d066a80900f0340510740b40709691108022690f280e524600408408544c402c0c82a05481e0800b03213084141c1c455a140e41018050401c5c9403080401d1001d800c2c1e004100003650111b801804184401127150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 767760899 1250 767759649 767759653
    0xf01050c0313080601080d03150b161401021c0e0322030c0f0e0f0f01061b080409020c011131030b0f0703110901200312190b010f051e0c 60
    0x143c003c4000c1a0f0a058440200540d0345000e0700e6030041c3c094034001c004064148494903010403050380701300d024004006030a0040d5005a000d9100d010b061011401d180340e05950014403032504400429074040ca99140d54024418002c4a8000c581c03680070320205c0076152448c03010290100d91505207000c01442e4408044100f20ba00c4103000c1d42400c0e800d001c9d070762141d41e04030f02007880340d00e09075491031262000300341040c800c0e170a00204079103900c1c882c5611281643c0b00401c880010780c0d52400707000a4134241d00d0050710f03522500600385c255018414444811102000f400c1203008032000382d00300514075131500d84013991046684540410305540082c0c20344803900140110440041c1901303025494035681440301c034400000c695130318420803540c180030810040c01c00c91201c0485881c10102d8603580152424001c120b100c02030741441c121040199800c1c0d8010b95802416580b0400380c1e032010a190030341403041c51990242840c8504101e59007030000c0201c0c0c2c440001c440743c040313541c0f40f0901d0003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 767762149 1250 767760899 767760937
    0x9150307031b051810030e07300c09020306030c090103050114010e01050a09112a0f0610090203060d050d030f0b09040804061d0d11040f0b0f01050c03 66
    0x300240b8040700141c1c400710801e0090410148030702c2c1030b00c500c0b003141003000800511403010402100d40c001e0060040c0340d100d40d00320403084001c1c040d250003000c00c100358100a10900b4070014560300c100a1540e00c82e0b0128034070313402145002d88840261924250300603500c1e224100020b00d050303900910342c1e500105040c0044208203064001c504800001c03603154045907294401824000424042d00d41c101c0750511081184400d26000072204a805110f11440c0605440020b035014410302c04c17000f6250a00484c0d0a4684020004045440b004d28050a50790401142e01c070360252543c800c04100d1600440428407907175a07000f00702003903a4003004881e901051440044c01030070000d10441c450616101140c0040d0624128030341c0310701da1089150303103402d05101090703460000f4662503045024080b6034545003512440490508140107890a1320606030803800c2000703490b440c141c5110b040d03043c1800a110340e161a20884404102400c2094031490621550b03440d60081e41425a016a0244 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 767763399 1250 767762149 767762161
    0x1e020f030a090311040b0609011803050114011d060f0d0213060906080f01140403080711030a05040306111309051b041e170703060902011b03021c0c030e06091503 71
    0x102c0382d4030442e449090143c842001c0f860801c011501030790b01040d00502c0404c0030b06215841000c075800f0000c0c2c100050410a6140d071151030071140c403900340981820484c00144141100459640c400300042e103407208840c030344500440d001004074515240110320031440d50007150b840c1041c00c24468031001003040303032950380e0720000042d01e00380c859988079004161018945140c18000e030412010f214000c3c204070380b00c0356012250041c0080c81e0380b04002d042511241001024002090111929030380c17a45c5039415030034600c003101d01003a00d100200c1020011a4610882c9550030405c486080d0b00010b00d941d40e265051000b0010308040400300c1d8030019002c60342020441030021155a000f61400c0e410340c0780c15485041d0502d210316440315610000301040002c400340c200b14042803040c54a00b1107200b1090708400b18460080c070880150b003018108080f4043d0300360f880700c0440c0c1d662a042c0003112035034030042d1004000884081c001c92002400c946180c83c1c400007982040a60016070744d40345458 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 767764649 1250 767763399 767763407
    0x1103090a110d0f02060c1609020901120911010c060b061b0106060906050706050903040905090d0f02060115050306120a0b04030806010e1e210a0201020c0301020a1e020f030a 76
    0x82482191010740819069180d4102540c200510607480b4040c074030011415000c10035a03030030012180000d4407600b02c00090014441c1840c0c1c009003c40303240943c4500100c030000d0640d0640400d860703015882c150b4820b0125140c01030341c800c1c03e07100303003422100d045483c00c291340a0300440c0e09450300540000303010080c101c030059540c0c5103100110020420552119000c54152032944502000a001409907101141203984010740182c230b0074003100d1805a84540301c2c421b03140c045421150b40c0d000104500706054115036a0540054130303101030710442d810301c50000782104104160008025003c00022100d440c1c46000003607c543c060b048411420451170700d212501000c460407400142c074100071621650243d981c61440ea000240000d5080c50340c40c03a04402d10300d1015641d80e208050b408584c61104403e240c1440c908200c0300030b0b0491280314000a85090a2a01881c1c02a0720420981c02c440754010140c502c0809a56a0049400d150140880c609001080445880d0100150200e500e60304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 767765899 1250 767764649 767764663
    0x180f050909010b030715111203090c030d12020a020f0712030f02060714070809040e010c230306090702030705120d06053304120b0406180507060c06110309 68
    0x4803641100c6903101d401c400d0036912030700701c800d41642c001341e024000a02210b034a5800b9549514081c41045240c4049a1801c1c200c07001d5145000000024401c00381402e1141900c0c520040e0001d0070306910b50040101a2403600751914180c81d40030403003d80f046d200f8441500c00b01407030012602d40070f480b6071101c030201c0511503045020402080140e0700181c00070500f00c0c440d92690700e8004140b007a080e941000b03a030080000b1100d00100308061161941d81e80706107a40c5101940000903400404440a0900403247c05400c5034561140c45408080c110602282e5003c823080d50310140035100d403d4264554018000010014065100100c00e03495051020303000004074030a0a202c995500d100340074140e000900070b62040c009405495054141042040c20280002d8200070702c1c250352540780001201815070200c86800c0311030107101c00c3c0006405070001002813024003150600c1d00c2d54455903103600c0c601c6194140032502800d8000e02c401a07010b0341c10035445241d4243e403890604541511181 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 767767149 1250 767765899 767765909
    0x1706040608011e0606020d2c10021e01140606070303060e0408070c170d030c231206061606111c15080f0d1b0c0303020d080f07050f0a180f 61
    0x1ca080d100040c9075100086140da50819078403440c1c040c2c0c0e201081081038041800d1070841028031008c4065041d11841c004100c00b008550260200e0300b031940030030f10303106207c40700b940c1142c0c140701c3d14803c1080101c85680e000502180c0046d41c1d44003604d410703070103407000c3d41c841d44000ca003000400080c80907060080c55210302c10801c3d22561a250510000c9510002e84030302e4180d40085402c01c82140030364000040391040c0d0511122211a0780c0c1904c0704080ea203c0b165010075408902007185a100305420360700036070200c03080c5003406450600103038003056111001d05403544502d020418001c26408841300066090014174030048001c0a40029146407020001c2010a01c20002011100850414040b030303c101e003d083d040c5c1c04c185049981e02c12a01149290011483d01000051000110301c8001c510035006441c3e04c02d030034400070344480303401400001c811018400b00301c00e06501408441c042541494001d0b101c503508101182d03c010400404080b01c1200c2070040341915480c566101250 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 767768399 1250 767767149 767767151
    0xf0906020c06071b0605210c032d0a1401050a0506091c0c0312080604050906060d0203070503010501031a07091a0f070c08010b04150518040311030d0c1d011706040608011e 75
    0x1400e00b0042c46000d80d41200d030302c1c104100034400b29511140880ca120398020a4501c841a101d80340c00c204ada0380764055031032101d442c2c1e490902100300200708103214014401228258980c41ca0680400d40c984909983c01c0d10455880d9a0000e2040c948201c80340841c0e045610f440c007880c0c0fa890140034030710008054001040050780020810310b007030f0103464801d1000c0310141410351180310070310400d445582c0c802ca0b494012200c0129075914244140c600a60141250744d29007018054505030300c3c0e00c0945024100181c2d01002e016180021000f441c1c1c4014841d419540d034000c601c4c0000380c6000d4200001d21130002850001000401500541c020400407102040b4440381080c1d21580c1c02814800c0302d8008040c0300c10740d11400c1019180c644d0140c002c1c107154120600c800c0065081d9440601d2070420380e603551100001c2d1980c80748448007039130401c0c0ca400e0340070280d02c000a030244024518101507100c0140025049407240c0c1c02842c000c0100700c4c020701440c0b08070305800c018071503030801d02400c3d2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 767769649 1250 767768399 767768437
    0x20f04230a330507080309010504020f091e060607062f04050f0d050f07080105040308280515030a0812060303040308180a150e010f0906020c06071b0605 67
    0xb220103078802c40c0103003207028141410141e0070108115242a0740441c1c0050210520102000c100803600075485040403c00002d018138107881040403030003411441501400c220300c1080450703404030708000c901d0458001229816036403100003800611402c00b0003007505081001d02a40403400503c00c02513031515482d41001c011981e004000c540c001ea104450b4003801c1e02c1e02d1201d030b50510500fa20542e030700603015502c0e00f422603414249804090382c020b50040e0343d118108414103500012864220300100c015905007002000c20341802d100d901c81c5040c20b01d0765070380444c0d42400b0580140c3c20403200501034805001541c00c0100d400e40025070207003071389024440087d04600e008002c45007943c0e44050002c1c140180c086c15039940840110007aa0030011007074010a252600e190341c1c1c041c010841c0c2c0c0b038a5100804100040c041440002c900c814800d810009101d181c0e00410400079a4809650b51510b5a8003401c040300050004e03401010400c400b5800440c00d554008001c003900c0096408259032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 767770899 1250 767769649 767769659
    0x1c1b0215071107051e0402070f1203110307031a041104050120060c130e0c0301060f030b010815010c06020c0f0d1b1104020d1a010f11060703020f04230a 67
    0xc00700d0380c0c000e214010307001082c0500840ca480740500c00c4010b08007405d140000a02804501240c0c00450195507a400e020300c240300700910140325100450035441c082c4030001d010340d00c01205000107001c40040c1610740200a1a41268000c4801c2040c4002c0040c1305440758004038610b2540a4041c550000ba82100e4a00980d21560319528004d604040240220ba8808003d0401c07030304a18800014400240d5000460200c00c4404500500300060100c4d92545004400b80440300301d80d14a105041c10a51602140d1ba004600c2660041440b0903030442c54071000c0040b11a10f41505008100303a201240c6060004800110b452208080d442110001c20280105403661008035550b0070420035445020b6000075006500c040103c0c0c00504098200303140b00e2299810b031a03203d164100c5a04a1002c180c2a660b480601040c0b01103942c10060800300340c410ac01341d22400014142014140c000441d03603140d041510031900100030141c1c0c50360040e00003043d03003406892501c00300d41c450b182142000c62 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 767772149 1250 767770899 767770907
    0x10f0b04030807060e030712080a0b041802060306040f090c14010504080c151204050a030e100909020a0225240503060d06180b18030903031c1b021507 66
    0xc256078200c96450b080c0030190f52148042d290700040507a9602041c4100c40004001441c810307003010858440b11905d185c1401d181080b654113402681c41541002e011107104052448448031585e01940c442ea501d5a030700b00800c020b808124413509006140c80304071018083c40c109181c082d64090740525101d00401d07001100d184c003c6002c0d050340340d007280940c000703913203030014000404005c042059801c103071b11001c0c0032500201c121800d440641142217203004140e802080d5801c82c0000722205101c10441460040049081d4080e1015165001500b41c401c0740c020000d500c05050215050380c07102c1e410502d0304400d09030300e1041405060020310940c0700c203a01c552440a5100340d56a0b22030440e0f0300d0208109400e104008150b030072a40d980008110041140041e90005000b810500d03802d00f4800c5100450440716602c40109400500c28800c0fa90f50200072204940b64010065141c038a9074500380e070040170003030340b0b000c0c003070549014032815642c020a503544443c00115000f140c607682da800590b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 767773399 1250 767772149 767772157
    0x902122809260c24010e100b031f06050c03040306050a020702060403150b0d0f0201050a2a030e090405030403080d0b031902010f08061003091502030c090a0801060e13021215010f0b 79
    0x103481c01303011001804507424200640b60b00c04401482c465003640e4070040c00100c3da0050f5240a044138845008001c03184141c440103000b45814a4070340d2900803040070fa140c407801a400018480d0307032540081219801c081e01680e41c3c0720740041159540c0c682d21302d04484032265131200c2c00100b9041c210104020300e4a980640da03010380090159000d0f0000d40c1c011241b562280e0a20824031000d0524100301040030b54400d4004190001000d040344d03080d040152420060011041c481c107151400c101c005100441901c00301e03540003000c03a440c0c0c4c0780300c02c01901802058061031703058400c004040444c02035080aa952603030013a01c1d1100116a020011241284119031003500305802080c114201c911a40c020136007035002d0b2107881003e2485200789420390784140d91410003034002203101a031516011010344010102c0800030044c162408030450740d1131a0090054500c000d964000d2800d54070384903521904e42c50008241c805803500903a115184034020300843e0f00b601b11041010840d101c4000840d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 767774649 1250 767773399 767773453
    0x1f020d050304020d030c031b030206062d190e0a0b040e010c0e060d0b04060b09040c0203030708041506032909070302011d040905070902122809260c 65
    0x400e0680046171001c4d6007105142008030104419021107050070000703e030b071811080d131003a0f0103410fa90611400f0000d1401c2e4100c2d003240300c00e401518001c94441c08980c81c201c9075034247e45029403034002c0c2d80c0721401c12072154000341d000e021a4082040107080d41d4004020700d078049900304001d010050f052422070b100e003606200483e10000a0301e0b618075010b0040c210302c14868502003220a002008602510440d510000d130006d4007080b8a00145414002d0503a00c241e00c1c07000794114644030740f006206d454040c0003d01500003001ca0030764003884a810120203150401036040d01804102800940f1300c910701000512400c020000c5011074802044140450350140d4401c1004a03001d29448008407040d002240d1041e50351000c400003860500080b0010a8841070050b11a05006801e80c03082200a140030001d02c101450003481d04107000d481c4403007001c6030b040000d41c90b102c0d02d8070341c1007201c454a58042056910141d10603000b4407100030460780c05800150b6042102d1002020a8019403d400b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 767775899 1250 767774649 767774659
    0x106020f1b031e150a18022412010305010c0203031003140a12020a1203050c070605060d21180513200414030f07061b150c12050609061e0f1f020d05030402 68
    0x40c0405071922640c234405007100120b0004005400c00840303000ca6001d0200d040c0c01022100040080c40028800c40719054064005145149090f010346940b0010038007004200082d854585680c3d80300c100301070030820f540842040b00c001c0510304040e540d15444101106d2691910180d80c00591190040d80d0041206440706420100e00d0341e684000781000402071500310542c20001c20105a411660104100708210008009859903100801c80000030030150541085030340100001e03250b880c100402d41d038400d10001000100040c0e000f4092001044a0034074200c089030101c0c0312100706088040d505c01c00c8089400c0409144909070325140c20f80b0410020568180d81d5641400d61000702800552003680840904442907008500321148140c913040096010010020051080d210701c3c3d40100c41101c02005525000340001c07c80355004e00c030101c0307007050000d129400361500c8007070200258005010126800ea00856100e80c48000c1284800521404520411203030084003203900440d00030380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 767777149 1250 767775899 767775941
    0x91404060f17150703051009110301090e0102120c04060f1b0809030304080d0c020907020a0506060402340314071730040501050106020f1b031e150a 65
    0x80001150304901d69149294007511800e12074074440c3d03000440c070440c01528001210b080c403150302c000c0820075821982411b803405030030501c0d01d101da0050740c2c115088680080742d8198502c581c1800b9002c0d610000c01029041014855036040d02c001410030341c0c800b580c440c4506400c2410460300000050a40300c50258100c0100c8040340c00400241200e6501600300c0b85002e0340c2c0c15203589801c01d80c040e6007001540704103c100c1140340010fa0150012010300c0200900c1c500d139220720361945c2c00500b59511655000890558074801c521072408550207010501018040c06139000c1e400f95184801140003d440c0f00580e20103a6040c8181c459250b00407041070125074007403c00c501c45500041051480001e0000c0f100501001a07d0444813040141c881240c1c500706440c0c0642501c0042c1c001c10103640124606107014000001c8582000c2440d500c03000040c8800400305e81480709500506140710041018001086000a24160b5122140c555440c55640321090141100c0d828460340500c074080340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 767778399 1250 767777149 767777159
    0x1e2901030221060106030f0c030e03030f180d050d0e0d050403080703030f06080102091302040501300c2304061d040b0402040f06120506060403170712091404060f 71
    0xc8045041825a01c101401c220040d02d00d43e26124099106500103070f164030305d10314500441d000300003014429003010f1107450382403010f1641b01c0c0401410310381e4070b0003070100050006503000641d0307608030025030a40700c40404c0c2010041c80f940c0076100c9066554200540c1c05a02c01d000964241c00354203030340c0c525041a00f140c0c2e4402c1644e0007e4015020942c43d00300540d00070300907203e90302c01000404001a56941401d003400703a414010030f0702640c0a441403000300101d9070841462a1600401d043c01c8100c4040903900c0420a40f5083c0d180845c240b0300314449107181c2c0c00c01c4078000724411040244250720340996508490f0b2246d40140400201d2180703420302c1c03d040501d202e00c10050300600118a418611003c5030880e046544010003034840a0001c01101e50003040b242c40c000011803081c0568a41000403c0d201e21452000924000f04001010501c190150030f9910f81a0301c112000c0c90310b0300b0440000c0952040707005c0c01289402d41b00c40d1719103034642480741d47d04440e00c1c407007040f1480b07180c6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 767779649 1250 767778399 767778409
    0x10b12070518041b111c050c010e1504021f0f2006161202030606040b0922020306041d2508010906050f01050d03120b0604031e29010302 60
    0x1c48020901021107080b075000607074403405900d01806649405804071020520010424511a0440b50543c0c2100040704220040d81014440840040c00d000b41c0d01c48041c48418010100c280045000707001d40300808001141c5080e202e40198021118801682d1030405884c02c18410182000081800f85544004050103440451900d465150300400c5241e00d21850504000b021119542d14035240300c20844d0003070708805018006500c40c0c0d0218114500200410010b214a001c1d001c1075403c0420040c0f02c603622182902840031000d001255486c9002c64111701039042541ca1510a40c00d03c005501030441442000101012500003064642452528100c0040000080030301d031103c80d51300446d14280902905058a10460b400202494140442c17101081b060300400e2003003184e00c003148040fa501c40c0b081007034500c400c1030000e9200d8000300027503098407555000400b20403a50840d1160b44607801d046414450190395403201c54016500000c4001d12114200c400314656103005001500300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 767780899 1250 767779649 767779657
    0x17030114010519031a030303090d0207060c0b0f0c1e0c011811090c041518050907021c05090a120501050a0b030d05090d021c030e06040311010807030f0c0f0305010b120705 75
    0x30905ca981d22055450007003030465000311000c181d20741c170040c0965911681044403200601003850000e900e06120740d540304140001601e81d504030707001800401e420300103840c100c40582090607445010082c91515004513a0080040c0003100e5280401150b94000741d4448031030f000c0e90084108040c400c0c58803c10a01d03000c054813207030708440144000300d0101024841e41404001584030040250300d5108009100c03405600003601800f07202d003d0004d469000180c1188031a06110581c224805046048465018001c1c1d03c03640103030010f40001d8400350b25850303151001d005800a208950707400400406960502c2c140303d4069014034460142103102740b000d044c08600013800032403035490342d4000803a101d04841d20403204c4e00410401408043d004404d45028480032346005040c0307851078a0349003c29505100b600c0c18403000d84000382c1d5081c403c2c0d204c0c0401c10582c3c24108038061518100800b0705a941d40007901081c5040c0001c01d0320410341050300c0c0c001c0311142412030603030b44040701100c0b1600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 767782149 1250 767780899 767780921
    0xa051005011805100c02041503121b020310050a0c031514010201200901020601060c08090f0111101b02010b102001060303020c041802030d0e010c1703011401051903 72
    0x2d0400000b180036610300250740020415503840c0300f01e81c9014010001110f0034186010b014405d904810000201c07000381c2071640140d642030180208400c44e1410504035003801c4005d5150107480c06943c42c03402c071940036501408541408011850021505030210b610218074460b0002c04c3d00001c1004e0b101d10511202101c0713041c40003082d04280e10450302c00043d208180c5250768200810149100d5a040000900410171460000107120690700e45d000719210314000c0a002c0c09400020f140240d0140d001186070100740b0049070960404281d1440c014003400c11041e0742e080948466081d100d02c140111421048010503540050029007400d840c2ca1058009070014409469810303061000b00380702d10710045002c1c3d001b50240f00b0381482000101e074004481c5100350b4052200040258400017049074224007281881d070400603042006880307000452100403c00c11030088a0412040322601440c1200c00c0d1020080c60300c4100c40065640b8001c00c4034483d26800c9509441c00c219219401c09981c00b4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 767783399 1250 767782149 767782187
    0x5030a14070230030c0702010e0612010302092e090615120b011b03110d050c06070e011803110f03030a1b1a01080a0209010b0c0a150216050a05060a05100501 69
    0x41400310304043ca94208644440740c60001041643c250358019015000c0c1b4075048550514200d0100c40c2d2020850b0b043c000a80520480e2000918146210f101101860380d2030400d07003401a40145002c40750b08080c01180d95a5040c8840051501810101d11342a1006138580354144030101060b01c00030311228029034100309407030760030750030042a01c0d5860156500071b5480300303049021084414230348044403e0303c200300b00081141d2120302e103010075503c1d08040075140001b0580c05c400012a07034a14142c0e4011802d801e501c20000070040010050b41480e2001c0e903031a1201c898004c100f50b1280202003035003003c40c0244d0492081e001c410742c020541c062281e00684d540e41403440c2411000d0600760001c0b01ca541c00740100401303520f4030203845401041c02d01c50035440d1001c184246074403080d643d503008098100c05240002c01c001c854042d101d00c90900100303107080039507e08106650386040703501941c4500400b00429002c25050180902c600700701900b000742185040c2c01120045584c0322102582 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 767784649 1250 767783399 767783473
    0xf0501051309020f060f03072a02060a0e06130e06120a0b07090b070605150f060d0c0306090203041a070f020715110d120c021b0105031008060705030a140702 69
    0x241d603903070b0046d000c0e854400050589a25140710068804800c4461030188100b0070f82e0703008200c998812107604c2d21941640c40d5a2140f90101c2d0564908440e1911681c2c000004a1042421501c040c00102221091900c440c0f16850321401d00903410b05114111041d600801d28010114a828009903000440c9141402415540d1410460380303421141c0111041a103840c148110580442d040364031540e4211040301c1426010000592181305098101042c02d44810341041c09034000d510000c01095100c1381556039180600d003900e528059644520b00303603220741d804205c4051103038800c04002c140e507800500c1014200082c2400751984001400304011186240b10030043c401e22000140780416165101c2055152540d10b055603991858002103610207401042c3c5140c50f074030408281c40003030824503581c3e103540700c0c00492120030350002203c5209510610030307425030140046104450303640c2e040000300429503001d800c1080c00d8a5680041c0e004020800c818800f070029180c1141e0071f10040610 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 767785899 1250 767784649 767784679
    0x403110603131403030105010801080c010f030c0918052a090904020d02131b030e03030c0d0e071401080a020306091b09100e04060e1b0a2a02040f050105130902 70
    0x60280c41c42d80c803c007a040031004100070f5800c0307d00e09015141e440c0181407000e00a070f00017000d40440b03800c100c08058407420014a8103000b110300a000d4480500c0010000604403440d501404050703c82e03600792250341899125802d41030451001d100c1d181030040e443c281d940030130041c100d0ba0240060340d0000c85050303070000507994030b400c1080003007641e02c2c08900410100128464000c4106603030040c1343c104010900442800300440342d012100c180e0080d200e101d1240080c000307090300060301c6e446120760400421000041e44042180740d0090f6107144150355001c410b64160f01060f01c45540164034038010485200c1c80781018160451403008403810030003900c0016940103441104c00c00400c0e551390b00d840c001d09041c01801c015264a0000c10b03014100500700203c402200303001e003c2c40c1c00010500003000d500c03400450402d820001d008005200100d0703020150070300e06a408030700c07031441e02c2e281100918040c010a4121400140304808050903075201101030202490100d0b4008001c81680d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 767787149 1250 767785899 767785913
    0x307120e07090614090105010201020a201c0801080f0a12050a0c080d02040e0a0603030f080405101407020c0406030b0a0b060c0703060e06070810062a030e0411040311060313 76
    0x1041e12503d000c2c840d113440c00c144222907a043e04030300d046900400040c2c110f1500300612441c0c2e1f01090281300941d00074601030300d00780004a613540850780405000f0460b02036200c1121070588000c02c09480001041c0c40d070459880e003100000411408540360b01c540c030b903405407028200421031424205100c5001d607940e000c1503880486800b001c0c41d030118040c00240909404190f0180721150104220ba007161000f605009621041c0c208004003040050f0070031206100081022824100038000508041c080e0184424226650001842062025a503d1401e40101401c40e030b003020b4140c2150301c5071301035540a80049051690046000c00c11720351255020844003000390f00076100080d1020344009180e0030714401600c3e95003044000c0042c81710a0102202c5001202c07d6418141c06003101c00b05401200450044050882a0881125400c0c0b6410550614042c80c00b01e03030411260311501c0490303805014a000140c1080e040210100c1c1e94104080295000030303110390222115845940c96103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 767788399 1250 767787149 767787161
    0x210060b0c1203040b0c1b01020315131a060a020106080609010903030e06040308010608271606051c0c14070f050d0f050d050a0b060d0501080c060307120e0709 70
    0x421003480000c0c01c14001081441962884900c0c4002c00c0e1450500f500c1c0d00c2200207014020000007071001030030750a01030404c62050a4907010341c00964803403402d4846003000d000351401590188260b4000e0000c0c03803d980c4145100c401072601000d6224941000384042d50700640806404e41d035a8420204404104004661142c2241030002c21035401074034000701655a034000b007404903406030040c400001c0d0007001150542e101890681c601d41c3e0392200030b001320a002600c00d0028035070245101640d28000c03070400c40e84a04800802d2106a507003400715058440d01d08956450758030007112140804054000628024091914440d50300c114290303410fa651000c602212440c1e0485510700802100713000c1c00b0707030032400c50034039120038602c841d80a4030030f22403c0c52076041542e072540001c20300c0400394803030449008058000c40c0c0700e109280346107006041c01c0c0284c0180d4860b01071a207000749498030440c2d2007203078030f56036a02003400940302c42d030301919907401c01060078002c244002c40c0f05c0d40030344a01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 767789649 1250 767788399 767788409
    0x20c03180f120f010e0d0f03270302010902010e1009030305030406060e09070911030708011809140102091c173a0b0405061f0504090e0a0c14030d030c021006 69
    0x2608488180103200c3c0d00311000c1a41740300e103d42010040101050300b00d0b09030a00341416013008246110300750300011708140303c111a050000d90409d03060080c168150302989a0768401c1e01c60b1000e00e80c3c22030420290300450743c1000d000580d8000f046c00000d1244015540040c80360070042041c94403200070107050001141c00a0b80c0360300504007000305075290301a00721480700c0045414914148a54002c0014405000f007802030100311240d4150744c036039544140f2645801115004003142e034811881c1c042d500c2104180e03c12a9812004a24500c0e03828042e080d9a80c0440241142100ca0320001c82940203203a00e036084200d402081c00a180300344100c0b020100c03023585010307405c0c0e80d11090a000c58010002e014021440d140400c035168840260030201100d040032404100c08000c40d0458092186403c0383c2d2a203800c202c0d180e2507410000400d5103c0e28070030b8480002c0107440e6006011b900306409002d942c540c1c0041d00c40d0700b05030b00a038000643e03421144103481e40308043e5106241650850703488 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 767790899 1250 767789649 767789653
    0xf0905130207170703030b031009120c050a0c4a041a10091a01081b1c0506040605100c080a14120703060f060c0803060f09240103020c03180f12 63
    0x2c41f20103280901107400d1040b81000c00304094034070b0340c6070460031808160b0030074148080300030303600d0078841c08021180e07203075911009200840b62100d8801c0c00203a4650f02d4034050180708032401c640b20f1400c0100c0b10300d80c04180d2028400314102042901c0010000d8025140c2c0300b15405c000b204080c020004602c20320040400107402c614000300c103000c4031201140140284a12350004001344e0b0701907001038000c010030b240741d0602c91150340140040d2040344025054200f05041700d80325048039810640c0320b8030f4115002c01c01e241d66a0140002c80c40307a402003c0c001485111501c0000e400400035140d00451480d1800180344005941c405a074000003000604610b443c00f000038807503160081c01c014040c035500102420380f40c000041c05117040d640c00140550008400a203690326480301482400c0001404485e150802c0c4417429822040d0020b40780111240c0004004994060300071035056001040046242413040407501303c0002500c8007840d031108444048100700d44e9012b145080d03480c41180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 767792149 1250 767790899 767790911
    0x209010b0702130504330212060f0a0302010c06020304080d0e010203101401090302040911040c090f0f050d06200d06050f0a03081e130f05010f090513020717070303 72
    0x104a0b40f034107001400400a4100703810807001a0b40c180c0400070380d2490000010302c01e0740541100700c2903003c0b21040403030380348042803040e41960200d5045019030030954030400141c03840424040f03583c106010180c0807030340030001140059015402941c4c064000c560007030030045028113100603550310100700c3e4142c0c0c0d008018482c2c0e00317100465a400409211981e1044080d1110010f000c01e41103200c0a44900d507541e07240e2080c011011210080e410000348108259900d108000c1c206030180d0140d0210900360080c0491b10044084064041e15002448003600100a0303444c00060300c030700500bc4204200c0e403601560040d0910025010901400c40007141140c103140c140020311070f01403007561280005440c02c03c08540c01008651000e02d04032440c914080341d203503402d4054466040f54013903810304c0110008544010300c1320301c81550800d03071350044510003105084130801428007925030f0040c102e401e206101030b4207600912580e0322520f0240c42200e03910101207015007200b0b40a40c042500c4203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 767793399 1250 767792149 767792153
    0x10f0605131e031e0b060105070204090f120809030f091c0501090825021305040c03050a061406040e07090b0109053d1d37080729070209010b07 63
    0x250502c41c1c8104c0101220046285442d05508050098011414406c00245a805540702d5400600b10281c011071140404c450514041c6070014100613100f0000d000c8402150b860700e0080102c403849024410310b20b081a01c008104141c0142548803003541000500d10b190000d03e082c051408001e0280c0005900c8004030310f6100403010a0428460fa0340300086c42e0100144d6541c600d00450032941d034400100382e9a0792a21709404c10840d00064010b2140603526010040303e41c01400480181941c90913403600e6150500080d00d402002c1c18000740c10045041c06801000c0d0320001c40100305142c00304046580308007060f000a941c0c6c0d00c41802e00a928070420341d1030140c03000d0500d95107000001c03541c15060384030000c1c0b43c22810f40c40e41541c00c80e80895180c10b66031b050300002c1000203491145040e0310425a1130085281e4824210200244140f40003c0950010900c10101d41d034900700030b51080280007a41c0b45040422402814200052045801686840c6c01d6540030313050381c0d851155030f10390314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 767794649 1250 767793399 767793413
    0xa1b1101060611060f060a0b0403050a0312090521040510170f040f0f0c0506160201031103010513050912040b031009090c060309060b030f0c09010905010f0605131e03 73
    0x9504100c05204082c80c610035100b0000610300d17400085510b0500c59506c0380c000103621003c50703501060704504041008002d0050106164140c03610035100e141601041c5054013040d207a00390009450354003c0b58154402c40c551404600c4c0c3c240ca1003040c186407a488500240507454100d55101c00210460340c1c00b07040d4044507501035000081c006000382d091070541c3d261007900e01d80c060000c1c840003102e4010341c104002c4c40f0260010306001130000380c0380c1c40e0140c034441d9031480c2d41d441a80000d050501011510384207100701c0781a100301403c00c1c65100300250705103026040c003400340f40e0700d8406c40d10869803540d45440a4009850909085640d80c10a4401312042c40c0c8030340c200e007001618000c00400043c032003039007460882d4200d04000c00e0200d80c504203080106503000215405014000d04d85825450204480800a0b0111071001540c1d032a008a10100c1d6000d006d101480c418485060190a01440c060011142004400b0b40c406842d481a020032200c210080c02d10140d80800620406c401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 767795899 1250 767794649 767794661
    0x6090a05120a03110c032109030303070302190f0203220b0c031315020a11180c191805040b03070f060f0305060301090f1e0602120105010f0503090d080a1b1101 70
    0x1d20006190b26190580000d441c1e07075005010807510011ba61f850309218a42d641a50502400102035a444e46401c01e1301501a40c081407115003101c80c0c040390040071a00441e2021001a9a40d0040d41002c48900707441d0112000d04440500c0b000342c551700043c100e40c06400401d00000b446019540351200151015440e010030341084a0700c1c000480241c181d29800240c015a03690802d00140c1f01560315000b184402521924020f90002e00c0d50030420082003810041440c6040c4511040d4460b403d0308017140c41303042c2d900010040d108803c40410032031030705400550103848000c05035a0101d40d100079076040340c1a01c2d40a4030100710700c0514014056018030405a02c048250000d020210807aa01d0401c0c1c000e51103002000b00701c0c2c00303001c0710302100003c5690403480c0d40702e0000c40d910020340c0704406c504c00003440703643d0010b1002c2040d038000d07038454820b40c0d000d030103050000e14098901000a80740f640d802000d0f4400135980b80c00e540031484d01c02c048040d1030701c003e0f01c42541410700d07242c0d01420b4540c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 767797149 1250 767795899 767795927
    0xf080a0b061512041a07020703020108071403040623040f0c050d0f060e0106090212100501110a060203060609091e010b0309120702040f0c02070f0e070e06090a05120a03 74
    0x403002e0000c61090141044443d04032114907202801d0f5524034001c1005043c01800a13000c0702d024003080b549036000038a08007502d000341c0720384031320741c0e41e400080310242d6038441000181c42007400418001a800e400600310f041d05001c140682044481d80c18042e041c0858047d110001a88098801c1c0070040d080c40000c4c0070151a0302c1102e030311a8680d0354540e98680401071074550348040400140400390701500151824036825941d4010f650400f24500100395054120343e04502c400040d41d40c01101c01480c80c1a1200c0a045c1c01c0c000c03a2140c00094000400b0160490000c103c0a103003a40c0c2d80c560300e8070a074100b030506540455206a01040404140c03c220701400c0c0030410300140400000b60104e43c0000c4a4402c4e60b140d00070300c0420003a195140e44203004030306000c002e44110360003052150648001013444043e0b50780e01c0102041d81482500d20202150304c00e0300310407403420080300900070040701a1403c80d455941d00003062100245900071400c0c1e4120001080405500c030304540c000c03103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 767798399 1250 767797149 767797159
    0xd0909060503030f030c0a021f0608010b030c100c0321050702061305060112030207030203011505100e010f08060f03060c0a0e010203090f0904021f0e0f04020313110a0f080a0b06 78
    0x10f203020b81551a60710001e00035441c1b02c4070209209600500c208041010350851003a06109600d030103040c10b02512842c01200842d500704818856207003000034402000d84d1000f80070281e0b10820f81d4041e03a50b41c4240c0400d2781003001c100710108001465900030340104801034800291441c060b00028100080500790140780c0c6416100c80e404140001801d0b815100c40b918000041c404d01d140c00c6c0e18020b560b5200a4165007099880c601d180150300d955004c80c0c6064400501850f41010122010b45601c130110b400b05c1c0c0c003451034110b1284111841640701e5409403c1407520260600083d1400c08219109400b486d170000e990f8a0300f980c44000c1c104212002e00007141000d803074100155840007401d000b180252000800102035550300484c9134100e01071a094036040c2c51030720f24001c15001242a13041e025007180c131080000b509051007280c2c410501001e012a402c0000e85d591030303c19080322541a4000b512800c0803ca266492a000005104080003010a555030345410302c0303642e80040c4158407613 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 767799649 1250 767798399 767798407
    0x1510090b0f041a071709041e0905070b03100918021201050103050106050d0503040b0a0c08030f0103030f08040b1302010905120105010e0907030b130206190c05060a05130f02120d090906050303 84
    0x5c0e4860a80f43c100280104945440b6001e00020070028103d02d001c602401c0031800c1c500c00103403969401003a00030300a005480c445a20780c4614500c80c8000d5901c042050b041040c1044242d2850740110381c840035807001d000e101c0d0780e543c0004e2207072007903140311049a954039401001085002d12800d001480142c0b04d1840401064640944074081d91044a000c0ca80004000142c0c900c81c10301405ca07030b688114450303100d040191a054605000740004c40100740091146084640500318035881294008041c03030095440040009800607100740c101c0c1800448400407a0b1076442603003443c0d0751120785000050380e600d8183c01003028013002d010f00e00c15410008060000c2049a84001d90140090b80b51a82181403880401c4147c490390300162007000100683c00300d8590300000e02030740c050040c0d040b0384091f10b0701c1903030004a03501030318107210042500e5501d0002409011000c0405800204207020b1a4418034025080406688070030300000c045d44403c0c040038000e84504005440c0c25801075040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 767800899 1250 767799649 767799653
    0x51203070f080a0605180a02070f050d020123060409020d02100215101401140403061a01261b040305060c0403150603230a020d030305060f01081510090b0f041a07 71
    0x2c81e06c0081c405103420400340700040c9440003560122510180e01114400e882480b40c18481d85410b00c00c4105ca0055003010780c08aa444c44c0d4240c0020024000a8410280d845003020000100f00c9100120307040b40d59040000301680d02d94149010300000754000d02065458000d800501c2038000b0300760100f090201c007050140341054001011020380a0030101d8846940c0001d01c005030240b5840180040d042c21010549002c505024451031102a2581c1300c41e003102019402c010741e409030012103040341090010386415940c81d400d0000841c803030030213460140c50780c40303882c20580c2c1116481486800001d041081101003c1c11f0321000000c61f07002c06c80030342190745607945442c8030081c1c11183d90400d140761000340c0062182100c81eaa005080e00c0c1c0015003454040c01800d0700325110303403140880244d45c0c0200e50041e101035204400b031070303403040d1800811010850704c018059000800c00060748030118141c9900b00040c40003495054045403140e180c0440854010b03565184108220024464000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 767802149 1250 767800899 767800909
    0x7030c02030c10110c010c050909180c15250c050a0b031603060806070c020909010b06090603040609050d08100f0503030901230d0b10020c031009051203070f080a0605 73
    0x125103d51540401c1801381000500d80502a2440c50440b65203800241c588154010008020100c401d4501143d607949040554030020388096120295400142c0c41408524085900c9040401c071449414144111000c3c0c1c1400c6441d864224034415004031204d9082c0300202c03030024000c200c1119503c0c2d526090014405050001820b0410050101550f070b1055174044c2c0c0014001c0e0002c1803c9441c0ca14003d48001c2204500c940164081e00151021071001032040c0603c0c0071442c4040d0880d0720b40341c0c41c10309121003580001d101b914069610451840080c105100b401a600d2050340c0c0d001c500d0406d61111001001c3c141e0040c000f10b40f8500040125481c040191400341200b400c00f00300303171207107604800b803803400450344401e20b410000f403010300a41069120341400c031015610b41d552000304650699407074086a00c0d59078141d11600140035160141e40081c4050741c0f080302a2898a201550042040d410030f031100b40104140c0f522044a01d5844002c00790710020307122040c04458030300b0000c90 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 767803399 1250 767802149 767802163
    0x50c060a0912030e10050d0609060506040302090406110f0d0b030106060c0206090a0b04090e0115080c090406060f030f15050103021c030207050d1101090801090c1502010e060702010507030c02030c 86
    0x2d0350034203aa500385400d040c012014515501000360901714428820b0390f004006034000740b40c80802a01d00003000c06c06050500c83d0409131400034000901e841e040d60200040340400910031104103440d40d81c940300a0807100050800d041c2c501050310345a146802c4444199401c2c0f21015000b03a140070030030040703a544248102e1200f90191010f0b81e468400c440803030400f50311a0004600c1d004000b80000e01c0c6000d580c4640e030200710b200001c01a00001c000d400700901c681d841840c0140d40905071f51115480c05280050308507100d440000f640c0e0b50b54206961403541154019998240110342050a10010180c800803807106648100815070559001030088440c000500021001090b540d00400d0f008011803005403000408000698040e49010401c1c1140c250340640022050320000400c040d05004407404103038002c0c1c60900c014100b490b1102e4103140400311030215900c58200c0c0010030024081c840c05041503900105061508500207020303034180f44402c0c811584108419043d403403002c2059 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 767804649 1250 767803399 767803409
    0xc14120105060901020f011d0f0703080d0b270709080a0b0408030c13080304030512030c0d021c0903031a030c0d0809010903150e0d080403051909090f0504050c060a09 73
    0x115114500c8500403450a800700f80001c46d158601000032511007880450148018050070880c0d5842c00c403809000e03102c1c6142c3c800208032001c144070290028455802884500002401e0b00341881070481481d407420b0704d41025802042d60307401c24426242c0d80310781080003518540005000d002d001d5135481d4248030700107001411070040480402c3d00455030404880803a03102c105141581901ca1355100e441c0e41c400d00c401c641c140302d9291658000300b503800c00d0720700ca501481000c82c1400443e202c103030083d6011181c05c865181401108140c8034404e88281c004090099400156a00d01405000107601d10750101e54413170b0f400704100c20031079a2200c10700c1010315803100c1440d40350a641001030b41c00c410b1607007000b8000c1801050307440c0041c1c1c05034049141e1000e501c040310a000d00d124000d0307602c0d82e02a41c0150005408200d101c2010949117420481440c46180800e10990364007000c1e0100c0c0c0007030400c203003643d0700e070803e0005111040018001003e001c0ba011480c00e00101409881e0110a202d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 767805755 1106 767804649 767804659
    0x50c0102040803043b09101b11160504020708040f03140d1404120c0e01090e010506090c040e1320120f033702010c14120105 55
    0xc0c245c03002c002e0020b00f032149902d400e03081d500300000740104918400e580c10406d200c25030b885501d1b00ea402d188101c18000181200080c031203180c020020b511948043d050f00034542c0d1030b25a00080710fa0445005075917021030318003618140596844400010010a0000180040380941604003c0c001e800d403281585040310070b80304030400312290180c2003002d000c180180031007004038481980c016011503401c15a07641c400d804e4064240c210641158503241c000c6034140c000d014094020303004540c01007036442c0c10785141c5501d00542c070070205422400c0c00032500c119400c2801c942d8450300803402600a2810b5848000c03504640107a090103100319041000d00201d02081c01100903900c50099440e00e20400909441000305040c00080d00008102151003004d00004d1482402829000420f040130b4015001c0d0586204940170382006804001207020160826400382c1524001c8074 = true := by decide +kernel

theorem cover : BRFrame.Cov 767625899 767805755 := by
  have h0 := BRFrame.cov_init 767625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 767625899 ≤ n) (h2 : n < 767805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
