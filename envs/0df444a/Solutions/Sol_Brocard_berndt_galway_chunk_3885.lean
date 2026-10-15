-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3885
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:57:19.990837+00:00
-- url     : https://prove2.me/submissions/b067b684-68bb-4b54-8fab-cf0a35f1565e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 698561151 ≤ n < 698741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 698562401 1250 698561151 698561173
    0x9030804030c050c0a03120e0301140604200412031106040506060f04060b0d0501090c080c09010e210a02030d03150308130e0702070e0604020a1b0302031e07170408 72
    0x20781840720b42600440481d02c00500110000e44d2080c0c198004a4418583c8030b40d000f20f0300d41041807403504510460091150b00e4400505060500c0c000345024807883e251903e80e019400304124600c1000640c99040d81d80300d03201c40e0064400c01152004a001a44040e0b0407005800041a03c0d401190710001500d03064550104101081c0c014007502640150b40383c400180749103942000f0510803256090104040d0b2500400900300e03203281038000d05110354036040040d50300c011403c441e00320109003845c100400484020442208486c0e80c8012002002c1800c50306640300080c000002034801c4040f218041162582203060750807084016102511603002400014080000742c03242280760511440031a41e941d89482198005071281000350b0010300050103101e01c4950302d10b60101040e2801d61620074002d00c0113111500c2109030b1144481803550400400d81b0030f108980314101c0d00d548085002c03c0310026948580c0c0080011600040070040e003074403e03040c110684080301d00c42c0740500b50070015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 698563651 1250 698562401 698562407
    0x61b030807030e031204021f020718060b16200a0608090a02040903110607030212061201060b0a1d030f250f0f1403011505012604240903080403 63
    0xc00380004080c9a241d1107400c40010080028003920000210818680d013082e005200200040c0c2c05505038985420384800140b80d00050104215070030f5201180c00040c0140025000307240301c2e0003004000f40009914840000703504913040f9040c0c01038520002e03183c19410900801c500382c1c006560002420789041040c81d01a00c081680440344030142d6000fa515680081c003191004d0700c04401064280f0004e00c10040300300605503000300e0b0782c1011440e2800302d100390006c0140c0244500e202d42d14140d8402e440b00003e4201030000c00030345a510740c031240281c10290805000324070f40b00708418281c0c05a02c0c1d5150000700d000c000403414024042101d4441d2101a00307102103841e1b508040308458000070000d0381d0405280007800c0800c00990f08a0425090359207003010500418883c0e0b05004807071401001081c151400c442c42420099000c005528a28690a075186070018016456208102c01e0003100d4000d54081000c00200303005440a0102c01011135041071805800200040002800a40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 698564901 1250 698563651 698563667
    0x3060605030d3f2a030207030e0607060e060108060603010b01021911030a0f0303020a08061f0305090c0d060902040e0d1413050409052107080d0f15080a0c061b03 71
    0xd500c2000da2003d014094001e40e0300351401221001320b0075003601e031240903411092140c01800e240030b5250002e551401000743c1d07421441d40b4810200050070303200300040d503400300f00b820103035200750354443d0380d45d00d0800d4071a5021250280a9401c0401651240d03101160886207080398403030902c100c6c81c0f00c0d100e20881e41c011b40d0015402d8414a4550000306401611410340b1750701c6580c015985034a1440d0080001d031000d41160f0003549904c0200c5a80201520003034401c018624000416503900080d107894004d103840b009400c4a9908196402e016043d08002011070090f681445214094514103541d1111941e40100141911121800300c601170401014031020202c2d000aa403030b2600005001c40b00144da04994075404076141850010801d0340074030303070025000b030f0807810b0482a446a000c1885103030034503210b00e55104c90300094000c22380c8c4041c040404082c400580192035442003952000b2444068507581c3e40d0380d100155852161090310107051104054981e080c18540c0c0035141c0e00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 698566151 1250 698564901 698564987
    0x10e0408040308040e010f0509010311041e090f060e030a090b0a03020f0d1508010b060a0e210607230706050601020c090c07031d0120030c0703060605030d 68
    0x2640c1004004041488100580081c181406a5008a501d0810081f400f042d85911090103210f10100401c080348100140c1d01e00f2030303020784000c40c07050003034501d07400d40f640360ba186140598030f024440420300031540c0145010a2140008105042d0803da80c42c0c0c0d61f01800c1694800210f03400c074180712004144000e44074510941c00c0c09030408813036401d02132a03a040740c03e001d000c45545003c8801d1200703600c01440d00401e0f590303000f004421001004640d19120f200a00f0381030040c0c1010548080d1210001c252030000b01426603000b0b00c824001312070326000b0a4030281c0c00030b9802d40f45046d51482d549403440c520088901c0b074a240010715502d41000d8a0300411850550041510070f0000e51114171a07607102c3c0c2ca500680541d101c1d03142c40c0207041000f03034607003002d00360507046500302d003d9810600003c1e1030f0009071540071642c1180d0141601c0c0d4070070745004071560300500f2400810420b081e00140c06680044040d82e540030352000c800c0355451070518210303101c6400c0c81c002140080b039605201600b2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 698567401 1250 698566151 698566163
    0x30e0a02030705011110050a090510091104020c030c0a1212050c030106141b16270207020d0501020f1209150f090f010908030a060e0f01030605070c0510090c0b04030803010e04 77
    0x48940c0d1b035152085440894050026540740e00e404020807800340001e80c031001400030104510b44aa807600e402ca0004408458000c40e800a00c0284030102081075030542014402102c840c0f038881d2a180464208106001c0b0100f000040403201e020302c41d005452050391000003040c02c50b880c01e04100d8800388200b50703c40701e1040030031071096202552070040310b80c82503035001480030a180403190002c502c02984030316000030040c0e91020007000446415211201809000f58480d6500d00000d82290307004d00000b401c1d03610003e00e00d8202c0d02c00c2c0014040a0700c2c01080c41e00c981e0344002c1c1103610344440c18480e4090107401400100f4110801140c2a04110b44404959000464070426400c6861030041522103050200821488a500d40a44809021051542c603440e013080c0d0460414603506000c010019910703a000a07242a1040d0700c01410300350807070129080c0c034003050340c0580140b00441d030a41d041082e001c004502491080c0c2110100d9920021103803647e0300e46040d0a41c0f1241c040c20880f04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 698568651 1250 698567401 698567413
    0x100b070b070327020a090c0905040c14070c090b011b02010f020f120c0706021f0b0d0b010b0a080c091c050708010903020303010806160c080306190605070201030e0a020307050111 78
    0x50302c0b403c0700301000940c502410005140b0710600401c0508449a80b080341030b64100b01e8418401984410a001140c0040e5400710744203011b031009030b5044010080079448034101140c40741c18000c030f0365031500840307100e40410450a055800111000140000d8400c24150702c24240c42c015482446160340b402e00e1841540c003000005140307035081038a0428041c030400c01c045024858003801b1302040340100414001000208244841081e600c010f058031942c2165460742c882200b511425400031205a211003414919070311000c032100300d03404c480d000000082c4020001001c0151150881da03105100406401c143c5903003855400c10b85c0d8100000700c9640c01122400111890240a04e14699104c0d4000d140c0340d40c141402a8600040200380c5045403500603600c00c0f0180c0c0085c074040045030010380c0315540c0d696a0f0041660a03242086082e1259031081e400120b03290700801a040c0c491007643d051001c4100345201940e40c3d200785201a42c10b40080004010640c081e44250003020580016070714 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 698569901 1250 698568651 698568671
    0x606070c030b1f05030f06070503100b07031e080c091e06031e0903040e0c180a06020303160504030b070320070b060a05010302121909050a0614100b070b0703 69
    0x40710300f5030340c0009102d110f02143c441c061034950420003520003907005003000d4056580d01e640d0b88a0141991041c8240000492501c18860001801400c4226545955501c0c0c0f0b02e0014441c1590048481d490103424408c1c1a6841c4148101406400c218038003d0400c2c2e042000c00c9015200c915071601c50140c0d204000b0780a407140d4020310b02c41c3e0103654030a0880d20205c50302e140c81160040140302c1c00e403c00c1100780300c0004180d81c2681c0100942e08201e80310036008903030b004d00516018401c1d9100110070700008500758000000d502c905040d603240c01021803a81025211030041b801b00404004081c40054015407095122500b07203800d104440c3d44440101075030f041c2c2a4801c100554a0200d0081080711900340a904070006040a1808514091081d43e1322259280090050040c3d003004181d40d0085480ba41c01240000b504841500c0d61201c503460f01030700810303044a15116407034140001410100000740700004071a600a2914078080f141c0c0e58414490000400c075000303040d503a4104070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 698571151 1250 698569901 698569913
    0xf0c0c07051207210203010e0613031d090405070612020901050d0b0a030f0845030f03130f090c0c030305041703070806011413050904050106030501020c0a1e0b0606070c03 75
    0x600c0c400d244e15840f02140c20f42c0d006143c00e41e0503040c0c00400c603500840a1020550360006956401a014a07102c0e0b48100da004007030f6001c101026116501068000500080c820081048421100c0715282c00007111400d01001d000d034061b07003c80b9800315009010b80301c00d40d02160001907412a000385011031036a142d80e586188030f00503410640c0c0807a8089411210043c90300800c07040350254050100300400f01c0c0d100b882e00d40c000e203000440350300340b07401000905440070040c2c051000400001d0744e880340302c00640e100b0000a20f202e00c000807c06180c000451010622074104482c409544041d0034140a8400760003400000c0c0040b515030f12a80306194084041d04041c5008101959540c00c0b9030a14000050407981015901c0410003001c004140c3c520b001d0319a07000803128156181e9900e03a9860501d41e0040c0040e80c0302422650000031600c803032010210f8841c444e54803801d000504204049910000e0994000b13004011804400202e038882c80e10f08080d1071180d04c25400880c10540f690380321 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 698572401 1250 698571151 698571179
    0x503070b1b0a0c090e071a0d0902060d0b0103051305030301060f0210090b0a390210050403031d0a05060c0904021b06180307151d0111030f0c0c07051207 67
    0x382d5040f11020001c0c44203071401d006114000740c000008090103070400e246c8860a9001003031003c0c1d4240c0c00120b02d100c0300d01c3c42d0000880c0a400402198648050318200b4014101c548081400603203008001920f1042e409001075003560440000c5040d43c0c24400207030784040c608400d0001b980704203100400c4205441c02103001e0f55114100784200c81c103100341030400340d943e20301c1c503003080035100e28010101620407410b0351100071031342c80d024603e100340000690408904840d01c1c04914180010401030540607081a4003414001c0c0114503e030009140b07164595150100003401c54005101046034441000d020b4400303c000200014644058100310560045010020078007980081d0204025207400155a40031000000702940c5030404941d2080c441c0c004085010300001d070385900d41c10a003600021801e4010b0310b114000c00c5203016036401d109503500b00302d910401c5080020300140c0c01103100400c3c6c5051550b014002c040716401c00d8100402194000c07101000d600c1201800101b01c1006022 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 698573651 1250 698572401 698572403
    0x70810090b0906130602030606120114010f020f03030a090305160c081b0312030a0b030a0507050415060f11010f0f06090614031e0316050c0a0f0503070b1b0a 69
    0x5510030346140c4499644801020032450750841d034100078011004801c480041c540c81100140d6030350f680d0740011300034003a580181012400400010840c1c9000511400d0b184a00340c80e045100b000c11881282e80f20b46140c00f5510319041480814200346403a08405102c5100c4d04089040042c41d00324200030203035540003612040942c4500300882101800b00c061a50180010886c2c0c41d00c1c40c00c04243d0b078182d1562228a180000000900d03620010391044006103001401c0d20380c030402c0b80c20300740e0351210f941c0078480c4a1860108881c285003206021074040f10320503186d4810140280c1011b5038404400201d101043d502d0b0600300c1e00000c4140302c3c40004203c0440300040c41c9041c4402c10041754400d1b0041081100328403443e8004e603400185544d46038020f12a14440701003150385190460040340540c0e103039051428800d0080260229024842401c15940890016540d88812249010600c28290113812a02c02800034000d150018010b003180e2001c94151043d040400f030b0300d1b04040641c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 698574901 1250 698573651 698573683
    0x60b0d021203030f0c0307170c070507180f0b090106030519050915090703030206011e030c0905040b060409020a060c0212060106080603210d0e0a0b01090e0721020904050708 76
    0x82080402c00d13000821300c0e003190040d04000c0c214500000050804044a448084543c0036800000c0e441060041154842a03016040d95107030b95a07480984040000b44106841040c244a02c48840d003d480c400c4290340c500041c03910006900c0d180083e0000d19000e00b014802503258203a02075007607090302402c0e024164030001072107100d4030700802c10302902d0090039080c0590010310040010a50001328903041d1401c000c0103c802c140e5a42c0101a424150381c4010495034001c20001969001c55000c0381c443e90244091060642c0e40070104003c8501001b002035001c0385d04c8034280025031045c0f0900941610240944041c0c4810000e500c0c5428000d03444000010b80c90740c10000541814000c140c0ca801c0400004143c003000500003036503d00801c038001c0010756540f480500e2842e41000070400707540e00440d0000c1ca81d40c503628020080c1c21007400000e894032074400c0c0011400121900e030f40d0b07090000c40d41400650415800c02580ca4800741003a200c0c1e120f04540810403140c18440c4481d0710450740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 698576151 1250 698574901 698574907
    0x5060d0b040c060f02010b030604140736021306030f2703020c01050c0a080702060d0f0f06060e150f0c030c0102030601090609030302150a1b03090b090a0f060b0d021203 74
    0x2100601000480703013400c08590401c0320200c280d4a0000b03120b80c119600c000c0c1040b50941d401c050301e10704041984110713000c815946480c6045200d0b400520100c046100114064110000d66582a4407416159514024040303204100c1b1511a034080e451007140a1004221131440030050561041c3d410000080501010f0a50040640400940c0010300d001e00b80700741800a5010840d0720707407a090f80082c0480c03000154480840d6a82022901c40ca01e250034104441682052a84020700f2500c01c0030240518180c004540e02e80901e41e04203803014024103441003076442e04040c0107181c010b0201c0d04040201403000707080010045c00035101030f003000e0340010303101c1c94000d00040a0800950040c81403004044042c80402c1e0301041c02820100d41c0710304000c0944903030151000400a80140d29030013400242c028951950641040b541d00d4003440703d11072640c0703903c10070581ba42d01f08200108807900303281d4424000380d0180c000c50400f0074001c08280e4008400d80201301141c0720200c898030300317402c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 698577401 1250 698576151 698576159
    0x3050109050703060506181503040311070609180908040503030301121b06051b1c09061d010c0210140f1b0604031409042c060a09020a0905060d0b040c 66
    0x14454070b64051032034642070001618080204030940314840c0ca22109076a44480b0426903198101c40700c0844188003012035481c81c107420010300b044400742c10118039000d10403000684a00c48d81d1840152210508980c83d07030150603c0354401401d031004100c50380c000a010001d0341d940c0c02e0002d14001d054041c5012085403851910000c000203005094031103000e20001882420b61020580351201c01000e0f00004c00540344a405250006910348250404e02d0300c2700a901d2030340d215540500321000c90315161051400c030241080e042407004030312030008407040c20810161800709420780b00003445061010706200308000900560b8040c0c0000d0101890000d010440709101220800d14441d1388800f815031424280d80042103c0e00b40f004500e034440001c02d6066140c1d40d0b960081440c00c040540b10080703400402c50450307400c0115030322810035018000005040002d68010603c805038014450700003e4144900c8500621010b8907041e00312241c0042003001880c030310380140c01036000b01c1400d2030311494 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 698578651 1250 698577401 698577419
    0x2040501120204060e0409020d050f0d0f0203031b0f1e07113312190e0703030e042703020a0b0604090305070f0602210609010f26070801020a030501 65
    0x190407a034120040c030410041103c158440fa5082c0700c20310480300442c0143c1c5030700004000301d026003400351050082070000605c05100241107046000c02c1c0d12503502d402d4080005036140d000480300c0d210b11111102400100c041210024107140c400012210709002c034552502d0b0b0cc43d000310241598490002a106040c014030b0754183d807076000105d451525849010754641000300340c03901050180502d1a200300f0400046505030b850300c40012081684d685040800d5240100080c980003c02c90728003009090400004105a000d076501500c5031b1042035185d41c1408003c02c907062004050004a456210310f03261612031908400b80681d0080c1118500ea040000c0c0e03a04010740300f10321980c903100c8040002a04107003030341c0318150000002d41c900241c80c100321010f0312a02c01111780100011300c01420b0a06d48407d2640205002e0303071809aaa070321000000303508105800380c1030010524410b11000c0c1180540354050380c02a100130b03540015564400182644c000b07010031000319890f203005210402c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 698579901 1250 698578651 698578667
    0x3010b0f070831060e010e01090b0c0a1e0506070503041a010b0d06060503010f060c1b0e01090e010b01051215030618010506090112030f02070e0103080307020607020c0901050d0f1502040501 83
    0x807409950380c0218a4650045c1c18680d0f26584a418008005401100341c1c2c00780c0702101c014403042d5190303562590707040c96464540da02c0300350859041d102c08002210a0003a65421000d090707006006000944400809440a420042c001c031107601c00300103072031440c03650442036038001d00b03034100c3c2d0503180c11000f60068251a50350b008001002420b000420100140411000440b07030542000449000c1505081c1803848400c00e9400404605d0040000d00f5140800c1c524100c40c000c0204202000c1400d10306401d8480090100303001071820301268418030000e422498101c3c0b8480340e1202582d0310a004682030031422103c4001d0406c4c505901c0c090742c1820300885520120440c3e00051647c107001740024910482031010f001c003c0c94901d5a4450b600800c030101c06000e00184003101903a40b890301d450580d100f01c9130782c801401201c01258074079000195580c00100010a43d001e968280018885244c44a0009a0300724040c140d07004042800d1181c00c1c01200b05000001d650b0714103060014040310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 698581151 1250 698579901 698579977
    0xc070c030c140d020913030908010c02030a14030c03060f030c041b030606080108030d051915090b01020a0b2208070b0105030111120a050604110d0605041107050303010b0f0708 77
    0x3c0503030540000160740d02c640c80d9500c11003825246001101c02e040848407020940c000e6400d41d844c01e0344401010360000050301c1e51405650301c01c2c1007284004030044250200b5124800307816400e101180309450b100005000e41e1038040d044a00004960000a040d1649040301c40c06142c4482a000121603142c0030380c1c40a02120b0a21140310352602021554900c9498084000c0a41c0e0300045012940d5094580000ca4280300003404141000504501d02c9001840b60100072071030040b079040c03030703500105010115541080c901100c43e40e40d020881d188204520383c004c0804619446103000810300c0c00544031050280707040701c0c1190304000c1498211140c075000068100307028000580b0008080e4401c5a000e4182d0101154580b0303010046006440c500101d80000d8902103019401603074103510420864104607001e001c0480201402c0f440c4d0320407404050510340040005003c0e5800b1040103289140710624814030b41200d684660445070014050110707148250b450400c03d0f00f11a03503410b0504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 698582401 1250 698581151 698581159
    0xc0c24121803071a07030e06010f05240a0c0213020d0608060a060305061501170106020a06050a11160507030c03150b1903021908010c200a0209040b0c070c030c14 71
    0x81c0f6961104500780300b04810500003121110001014184640c004100d2003100c01c1c01c440380c650b110008030706140701e140540b070b000f00303500e003000d210340c200d00210f0030100a44030512618004100c0c10403540c80d005220b05903008060301091006d09052480140110301c40000005451410b01d41e0300d034240000175025907000303030a1070020300c081071012403850b030082c03005a0202c15040314400140c503e03139200e80c41101c28850002c000103ca47c1c01185016159204600410190391031440e02801c0b501c100c40101d0240400380607101c0c01b00481000c601c00399000340116090340303640703075100c0c400500b8607002201c8201c0c5484c0030f207410301482c0c080e06079001003c550060351140401c40076030300c90603940f001900c290000d2068112490350074054202914440000b4040051403c07c0600b0040308015420b0485c10081016040084040340308941203500504440d110748403900d0344200317030780041d24428000401f0415071001446008406008503ca0085155150b2810000074070703582c82000d2942c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 698583651 1250 698582401 698582407
    0x2070c091103130f060609090318030510090c09020c0d02160b1204030c120201023a0b06130602070302010e04090c0512010b06180a0b0c0c24121803 65
    0x490760718207040e26484280081140c01c0d603091400c004504880880002c0c00b4189410000b0a6000540c2c101d284510f000e40c41e41c100f044c0005640000030340791840083d2060304280085135207120640c10906504c0e024045902259407102480400c80c1d000d011544481e81c041d01206100c5034052201c1001d000d0324041540c102031607ca10107070302d840349030190f0a0700113180b000581058082c0412a2880350801c5080c40d46511140c0c01900235030180703d007074018102c49448101c2e11110301d819039442012032043c0d00003454115001001401c24400c030603502c444140325117030070410515441402048141c0c010071080d031070b50002502501810504034069810140700c0800300b0300000354001180c0c8140c40b00d9500015240c1102e004210301c0e60480c0d400503001031350030a40c0d0140c03c0781c85001c1c0422038003501e0301513660303410f14a688100320000c03540e0f40020000905516001c03c21900c5840c204907034680404940540c0c088541c805126421a10241c000b40041d1001032100f41d641c0704490f1005610b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 698584901 1250 698583651 698583671
    0x81507200703030e04110304030e0f0609030a0f03030615210203010b0909040303060504090b0a0609020306030a060911041103100603060501050f0310050a0e090115060f180b04080102070c09 83
    0x6141c88181c040941402180401c00c0150f03155540842d40512860380f105450341844e1038000c0402d40190755140c07090341f400c0e2011840d840d20300d08031040c0c814000c1c018510b401d01581c440350b064062807002d40c00e055550b540029100304018900c5a000c429940e003d426819000c05003400400152000760214810320040c01082e80d02c2d41120018001101d2540300c40c0d4680c54101d02401c50b03500129080390a0107940707010080941109406880918001e000590f110b01a6500700d00040f20400c0e45640702c0440310000c0380c059400001098020030384a80814001400700b4203a40c84d6803050200d41000000300000e0000042d6200085c0009290034044036107001e00003840ca001f041c2c0c0c101c401207400404031b9550150707030010360000c02c000350001303410555600382c0e0012424201d420f007100c0d500307004044400da545072060900785c4459444941d41c0a03175150084030140250454001c840c0d404030b0021411050b060040c000510b400000540d83d00e01500c0c040310000e1780380c1c0c032000c205030511030450 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 698586151 1250 698584901 698584903
    0x3090d02060606041707090c020f070531020f12010602190b0118020702120136030806061204060e1009080d1e060303020d03110c1f020408150720 64
    0x2800c031414013840540030500188030310304008290f40035103074823890300180081c15600032601016814001042d140040d580310203006080b4086c43c0c6068180000380c1a207010b003003140c1054074034912030200042c140900350500d054950710454404c604581d0840042020590411041e0008109072800113004c264507601d08044071818094203442210219401c03001d40f549606482c08140c001b021200b00c0301000050600806601054800b20240082c009942082c8004c5042c05510700d51045203020030a900c0480d01204080c005039403000c420094040411080d0032481c0c00b40c1d0040c500028942d481040b01850540381d6541d00011500f0560481c02151020086e6000046040030209107075085400140d190300c100c00e503c042c2039141040120505500250821940b072850324100440e6060014050703c501504044010903407240300348147c045e514400031240815840005070515071154203050074291042d84481c007004504c802c0241c901e900c260b034803110915070740340b510211a040340e4403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 698587401 1250 698586151 698586157
    0x10b09090a0e0c0303040e01060801150f0c030509210c0102010c05040e060303040b0c010c08071b061508030c0102120604050f010317072406050906010504031e02100503090d02060606 80
    0x11181c56507841e041c10b1180d21050003030405640b4020196030340c6a0f200d40c0c2c0124469030a01070078000409040c000b150040f00c2142444030100f8a481e146409410b900c4102c5201e6401c0c4401c0702088414005581e4640310000c0801c4a0142c0c9400c0d000ca0300608403004d85402282c0c1541c504580c1000c0485c0002c2d40c00004490a80e58030400d2800c0c190340e5140843d15502c070b01da1011000750800a48030000c1c41066109104090080d1340c1e801d070329110407204a44500c00c082d240d00d02c00310283c584034005000396210300403401e120803010f10420380e10600142140c2291102c9000d50b500098001c1101c40220f14059102808540c20401e50410040300588070350305000084c120002c140d107044808060405a4808030381c441d421a0070b5049469060100c0440300354881841400c0a5000c035041c94101c2c5458441c10041c0d445504213880c0d526854100034294016041c14640006a400580c5030001c2d82c85021503252211541c03801c20303100d01c910304186072008100b15007021051010581d103071802c07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 698588651 1250 698587401 698587411
    0x18020a0e04110906091c0804080c0d020105181906050904050f04050a021216030303062c15010c0501061d1e0105150d0c021f051006030c090f0b0909010b0909 69
    0x4903a49680355017022a80481005070060502c200002820041180800040041e034860109440c00b280e80710081c49981c20000b20f0080c00308100b4001c12800b02e5841c6280100c85100910b407c019038400382c0031000c5000a50407080000348001811180350901c0c1c041c00350003108120304036a4a14190320382d9a25000b80050007886002030342d0b0020541c00c03042040d03050384c0e003000542ea2800307696441d0140081405100700803a544804000c41c0050400c40c0421a40350071020f400031655030f075050f14016590908500b54184443c243c500e8021070001d2090b00043c10802c08010640807844012508284d030051910031003644a00c003050b40350141d41e5540c0e044400603074070342e803c0124520740d81840e030003031240e04032400d4540703040718800e146d000400b6180340540490140c05441d15021000c180c400848103140d0120140c0d504014041c03080d8008900448549814049191681100040c82d05603500441c0640350109411000d898048003e5004021504125203803112440c040fa07406000205 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 698589901 1250 698588651 698588659
    0xf0d0507050a08030a020405040e030a0e091e0c030108120406021b010c0b0a06140a0609051009030816170a2f01111c060e0a1518020a0e041109 63
    0x58400c0800c401000916060365200c62010380360300e02002d10100070340140c0f107458030446c14a01000c0002130003208881c241c5429907a0311106030100c40611034200b5015060490703a5080041c1403a900c032841c0040d9010b0750b01c103207425a0325490b140004d4035184502004400000d810041080f84540009070042e240e8a40310200700601070860040c0c4446c000003501901c08450344c400c000b00a0010b0344650f0a550300180c201b0b803240902000e104082403d8010600419400c1320144100d15100d141b1000304425468081243c1c0d440355501402e81c0c00881e0702d80c0c0c4c12110860400100031f80300340015003100c054078880381005e940d010000c10f07030070b81c0c82150340140c100e9000c120369031003118003141e224148000081c020248400400d2216900050407240300d2407842c1210107030811b00b401644101e0305000512484c03a101c48080030003c01803014040f00441038001d00150340b00c40310400211f40d0703000341710040c3c403001108005000070307000c036200c244507600c1d02c801095001741d074000381d070301c6150251 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 698591151 1250 698589901 698589907
    0xb1f05060a0807031d0312070509060d02030a02071a0403091e06110a0501020301230603010605030f07270302040f060b0a1b05060c07050721062406200f0d05 69
    0x1600364000d02a101217010241c507101540c2a078000b00200900c007035064564001c100350b072020b00450752400342a10303c45e0b211604100f0003950f810300e90003458108503c840014a03010040c1d48180540b0046e0307810121840c07000c01004103150b00044403800a1201d403200e4202100d06c07404040f189516030060b031081c4500001d0880d000b0700f0400c43c00042c168004001c5503296155014134540809d0014044c00304002c035840304610341080e100f564101c070300548860342140c803440200010141d008080a00f0444000d11401d0303180d0841040202180b4455100c5070710030b0541c018001522104400707003e6243c1485801c104d500c03250800c4664082d0f2920b040c0d8425591078000c6030304140d040e4000f404d98800c550038402c5090a0700c004013015071041040b030300780b47e40d114010031035480d041c0240b03691400e15800d8107021501030b8100038220303140c41c03464500d8103000c074045420b100d040ba088000000c004501c0500200c5011130880f8268050100070290803090b00d9101e40e961010701018800c1200c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 698592401 1250 698591151 698591161
    0x20310050405100f021902031c0b060c0d09031217010b0c15010801020309011b020c060f09040219030c1106061e0306280b240d02070b1f05060a08 64
    0x6101d40062a0a01403080c410004c88040b958040e40040d840c10206c0d100040c028076007940000f044a02092540070440703145c0d2021000d52005159a80160360041d9041001000380d003010b1225074040c1d00b5685500c1c03405419800c08018070100c118800c420b211202001400e2254a5507050707045542c4050705a81e0341c0a180750341800c020a0403176220102d030310580003060101040d005103205500b01d41c000c20180b100b030041a80b007d101055144056000312950000d1410318200610380181c0b030b00c540524060202010504992181d0800081c092400c504010441e078180602291810300d450410345040d8507000c060741300c1d0800b62449116003454400e101c0390681c462250030741444000c0079280d444c036180a40590000c2c100605202d0303c03d903080d400350f0028803440398007032012014052002d02c509088a000b10b120202e1842c12251100b480200100007040c002890501d128040800250a040a50f010b0300985000d58040c0e000c0806400d00c11a10340314103444101c20a45840f0445d5101d03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 698593651 1250 698592401 698592403
    0x6070305011d1506210a1e0c0302040b040323010605060904050907080706020303041406010e04030e01030908130815011a07032303150a03030e010f020709140106110a020310050405 79
    0x26594059822035130104144078211080d41821401e5103072051195215a02d50160800711212031650304580144107284070707001000740e0302030710f20540c0342e00f40185070035140c007203015640d005580200d84000c0781051541d1a02061440c0300503035000100280a8241000005500f9005d0855030f98043c903514800254008010032800000700b034240c0c16245031940b141e0009481e0741c000c440a5070042d8140c5e2080c11051070025009040381c8406144074001d0702ca0755021603115440d550319a04140d10768550101090840c8010a0700040301c5c001268030924100c0318606043d680303030034001e40340000001040b140403c0b0271041700700042e10305400c2c1c1e035900c90b107004c1c2c816021052503994801141d03054982d6200e66240154020480c203517840200b1034090080040b00c440c0780c00020700090140080190b25405117032448010704890041c0d07900c0c030303403920701e11070440700502d82030801e40700550010401a500020050064051440640032035100c94006c039070703100424007034400d00e15543c60014040c440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 698594901 1250 698593651 698593681
    0x8150405181b0a36020318061006050705010e0610090f0b061b0f010608030d0605100917030c03030a0207061125170c0d0e010c1a060102120c0f06070305011d 69
    0x2c01041039042c05100c81d40700c002904101e1f4151443c2802031490710041c000000d50034480c0e002d045900c00c6140c142031045800e07070000041142c041d92244419640c7c42c20070f125082c42901d25540b008001c41c0340040d00c0d01a6590003c0d4070086615040c110455912910102c454046024503121039613403869592a203041e22424110005510b0b00c4d0012552880200c01410786240c0480f0038001c180c2c4800c100a02150340142002c041548500204120051442d8402d100320444064034142881d40c0b41c034904541c003c0b940514070b2640003950404111a030703c600300079a41d07404c0400f401c01941c0c11035270200390107480c000ea025000c43c140a804000e6007001e020101001c1821750364841200b00102d0351b03542124403201d0301241d141e20002c0c40d55403142025100c8983c01034800302d146030b9080342906216001814041c114020042c0d004c901c00044c000a01c045e0809200038140741601542c550b0030720002a002d03200b018182401008140c503c050040d14445481c01c007c0c4440c3c0ba0800c102c0c412107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 698596151 1250 698594901 698594969
    0x70e0702070e04121d0d0b04020609041103010f0f05031b1c06140108010e100906060803030f0a06060302040b090906010e0909010b1507050d08150405181b0a 69
    0xb080c0108110801200807001c00c1e04200700e4030b444902c000c0d400d080913175448001c0001c40c0c015025510610200307400303200d00da812500241481d440d0040140100d41a00c2c00c0040d0310340c0111000004004141c07a112491009000c41480240d2050a100c00241c80d848403095541080b0300d20003640c01e2599541105103010a500708024408848a1410601400110000d40c0310500550000101181d06000340401002400040e1119559000450b0010004184280e27206540c440000c11555010401103005205800300c0701250b02d0005400c0c8141c0c6c1c040d401040415005020420140e00510300f03803001c0301021600c0e11420f40d540300040740d003500b1080b20203034440054014416140d406502c0b5141c02e080c165003645030355454180010319031045034401085c9901681c0302c9094540b041115541080d034035124000c1c500002c4000505035502a100031001c20590840c05c0c5d60741c0410800c6140b444207071005906208403800c00520002d01c1480781102c2c603a913002d00310111482803001d140d080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 698597401 1250 698596151 698596169
    0x60f09090f0b040e0d05040b070501060503030a02011401141003050c120c1321060903090e0a140f0f07080703020f04030c03050c1e1c05030712020d050a02070e070207 73
    0x2407510240405401c030200c500340160716101414540d100007007140d41881255444140c6442d02e4150102ca107035001c42e009440a55031031401162581e010300040407500c1c0b540c2d001091a400131680900c003440306a1084520b80c40000f20b00d4000d0300c40907040344c0500d089080002c1c0a03a64116071900358410018402ca42c00b42e80406c00603045c6221000e01100c0464842002e0202c4d1948000d9440521500f482041000c0c02c03522036001500c29008101428480d262200940e540c0744031115102d181692418a00d03174649a00c801c001c1240100c0300c0c1e100030840500d004a04220603070b981c411030060072550411181800280782c59029070101c85072084c4100b6800d58407035031307410309148103400d50100300c0e028020600400d01c6032800f000c2d0307514484504200c4500b805049800c01c40703030140c3c1400800b61851042c0400020800502c00390410038060340380f003030410104071402410000a41d41079070501809201c024056540051a001510308401e42e850081d140c50700103034a0401e20b64000c03806 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 698598651 1250 698597401 698597411
    0x80a0612051006062d0c05070e01090c09051f0207050a06080406151518030206030c0d0e19020d050a060c12060501020a0f0318080d02010209090f040c060f0909 70
    0x104200001c0b0007204415450080001644031142100d09107410240901c1d0300d064500f011402c00000041e20618298608080e0300d400300b103984060410386640d1140c3e01e0904204010401a201c50107842c0c0c5400b95071410603002e44c10f04000490a2559001400380411542c124601143c000c124400160000a09841c0060b546007801042074408440441d16a8100100c0112001e4014601c00a072440d0040c90280000a08800c6030682b031891100c2004480c421000000350300c40b00c0041d40150070380d0340290f6035003188001c0f000680da006040075540e0351010000540600c4d850030154010b0398121050b00c00002d150409a1802030051030152801d031400103a020343c144c2041602520348254807040c41226911001a03864004a42c0041c01038152004400c000900c500141c07200302c280119800c4100b6100c890b418a0300a0040d600700c0581e60000d80030360b1a24290b0711081d03102400c0b1054000714030301a51003c00c10f240e68070a46041c0150040c1144ca094010340c44034001e00b007107040801c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 698599901 1250 698598651 698598653
    0x12050f0c031b0c0a05100501030f170421030813082d0a110d0f0206010e0c07050109111c02060921010f2021070302090904060b18040b07080a0612 64
    0x1303280c1c0d20f000301c110740074424003011050f0b2248078040c0e0750403a60844040d41c10b24490707468030908a004510310a00760801080040386100899862040042228a00811502841ca400350603a03c002c2d00b00c481c0c44040980c440c0014010301e04a414003c066030400b00f039940d000c2250b480010b01d0a038003440c20b040200d030703280303c166020204881116165049804050030baa00a582800451208074010b81010340144180441c0200040c0c00543c04541a031800c00d007034a07010308480050008560209040301c4048151520782c0d003403408030b6a85045009442d04e194002800c910480340d066008044c070a02c1810300036818400d03042460307040300023031261502e201c1c0d600d0001c0c203240007408164905c09005210800f4901d05440b038200c605c0c0c407e1800308080d00e410224100000388601d082540800184906132561104540240d110f9140407960408540410000480e500d6104584c41400d40030400881c40900c052604500c107400c104e2115101c40d108400035255a0300061900d40c52900404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 698601151 1250 698599901 698599903
    0x40e120c0106120803040209040f020607060603060614030304090e15090109020901060509010503070804080f070b06040f0b0a12060219022427030c0d0c0312050f0c031b0c 75
    0x52050220002040425214625084000fa1000014111090a20001d03005003481c8050b1500079014030869440a01140c4c0090701d1640300283c101c6034140c80d84410400c01406001d600040d110031110040c0c891100e50100780d03a801544070b014031560b1075510443c0180000d0040c3c2119611000032400030385000517503d400703030280044c200c2c010358118000040692140d01926507c4905030b440d41d1441d101d04c0021190070101078030a44029004028962846601700000c21800740b0900c1102082c2c0b41c13802c104021107000c020b403034039080e05001c0a6080c0d039403003c17404000d882080300ca802408440e4106140240903d078052100743c0007040900f16100e40000b503a06096140141d080304c1e103114007062200040d403e40c2c1500e81c10740d14660030484094540210a401d0001e0701c212401e1401c40f0f84d00d10300c0c0086080000e0003141d0080415000d05070f2084000c0701590070382800348410300f00f41403602c5007800c0062011040400110118040408a030b03d07007900a42c00c405116101d2440b15005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 698602401 1250 698601151 698601157
    0x1a060a020313090207030e0d0303060b031303030b0d0206030103150204051005190c020f2403012c01080c0607140111040f0e2401170f0727060e040e12 66
    0x3200b0840400c000094003601c00d00843d29055403543e01e40d032104031910188454108030140880525890310000f044102d1b419015510600b1038003590307490b1255505001c2d04984416540e42e0060640e228030401588894048a04490b03000120685038003103070350700d40300030f00440d0040c82c2d10401440080310202d6100300038040303d4a0002600c03060f4540003500742d03075400003404000e401106500d151030251408d4000a0111202007070745904011460110716400d60090b0885030752040441c1d0340031551441d50714854a20205600751042c2035041031031443d695086001c00c51303c20b0341c001881c2000c1091030f120ba01c050541c070714024008c0c1d2201c00c0c0510300c1234015000b400000d08003080001840c1140c0030240d40114202e956a09030488003c141da5241120b0350f00c8503060100910500301e18203004401c162040c0c20100b481003c908040301c0007408000000c0340c41c140012481451880040007480e031004940d802e040000c1103c0d0706c040880d010b05400890010749015201300102440084001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 698603651 1250 698602401 698602417
    0x60201060303084204060e010f0b210408160c080c010c170d060e040503070510020901170a061e031a0c0f0c0307120309060f0605030a02041a060a0203 66
    0x40c20002e9451044042e081d10036410200c40a0400d07450010550403082c810618251115141403204510000424141e40466220500c83c814440c0108600c02ca26010303003029042d200700441c50407100bc2800307403148070b51400720a4503c0032840807030100311150007103034100d0400b122034055540060524001c110564880d140c198082c0c900402c020390f219034a8500d80540c00703840e490401c5145640b5010f25004071109603002b580e240390102d02707900010030891040e0700c40c200850b03858105260550034042e100030000e80031401881016030744c1e03801044a41500392008000d030304507503681c0d00e5031014080c1a1712001c0031203442032500c10761048106c031100984e030085aa10030010031f200b580c3c5168031b00403652001c001d0001d1012503c0c3c04002c9000b01840032100c0300b200d0802815072038001c9038001100d00030011035982d21080d0200006405100c526080c040c46c1045881e00e4800400d0301d4918001c0002d00c00c40c3d0300c0c0b111407081c1c40c456003400c0c0c41ca48040c084648410030040080c0d41d990005003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 698604901 1250 698603651 698603657
    0x1030b041b210615081b030a0203120301090614060301050409020409060204060903050c03060f0c07080918010e0f070e1207030b0c0306092a1c0f0213050306040b0c071407060201060303 81
    0x20a01a00140e0070303a0f240c11105114000c080f00e0541d040c8209200c0e07030381001b040c0d050040f4101e0402591703040015410404d0700d80325980e9654501260700c1d084500c44c0c1c0c40b225050b404c801210f4400d954180a0b41d04403602660b000c120300303019100090082c0310060008020301d2003c130300800e032181e100d90b01205a070320580440782214010810150f81d0481100c1c490900c0e0302190000d0b403004100341c00703009858403030b5600d1402d0441040020785943d0329190780c038102d985440c004102d030702c0349a100d242d00000100c90350070581c108aa00240f1111051030043e000f42c40d210960315203100200302d4100115081403440042c0e080240c03075107480d03a100341d84080c13203111480d003c41c101a8181521110388a550048a00e0f5070300350008a92a941002540801100c03484c64a1505001035005440d078081c08143d0040c1e403912018840706c510b211a03080706021794480c0081000042c8118140d6400c104416000c0d0b44400b0145072290045034500b8180c0a00d0003000c038006001c980541110b000c1e0f038400c3e2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 698606151 1250 698604901 698604911
    0xf02070e091608062a09040c110106351510050402070f0302150f060928060f0603060303020c041104030c030f02010e040b0108060d0305040f0b0d0c02030301030b041b2106 75
    0x20000d00c1c107170341c4039403500c1300441080110b1850352401758029107600360503084c400d454400703404030b203407c403403103070707202105440c9901001c4090000705051800b04400150300001c0682d16485000d1303a510303903071610941d00345043c4080341e05c81302002e07080c00c004c00d8000e00a40d0703075050902d420f50070300c404840e084015216900380d601c0d00500244e646403150381c05040d040740c0340d580d039002c01c402a1006803110000310850360901000082e004485070605c03c507027002080d101d2501850304045440ea40c005400c2601d820300c1400040d50101e810150300c1001c03140400e9400d02103550b80302521895000070066459000c0001c204083e04d62003040c218001d03203c60f070002d604081800b055030141d0540d28005012000040c503285458440ba85969020f86419401e1076203450940f888074051b50896000720301d0104140c00e00084500521456a1051002c3c1d400c1d9455580c820030400c81c0035000410550040460102c0d04401400c103800030402c001d440344400c80d00c4400070380400000755054400074202 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 698607401 1250 698606151 698606191
    0x90209070c02030a03030507121a030c15180604080703120e0306010605030703091b0b09090a0c020316050307020603070c0221100c0201141f060f02070e09160806 71
    0x2000581040750b00a4040c2150700c001d5901100107100c010f090500340710b51390a01e03555901c03607441190740d01030a6007080c08642c400e5030700700351800468107040f52082003c180035090703030b5a040c5c00727640b01c40345400a1000401c40c4800012154003407038000c0e80c2c5a00c01c07941c00000340409281021110301380354880200107416001030580701c0000740910800b05404001040442d4403a030712030140c01d0300a204000000105c030300400f00384400c0d64403001440c0004600304450780791004081e82c000f02511001c2050948080d000f075124011010380d030f840002490300b00c006110703050080b501055801010740c1e50341e203047c00001c0d1049030380388000d9000714146100214000800d00e5426900c0c81e58200030808551805007200240c000004400219500c80c8400d880b0003d035910410300900a101495447e4100901c040f14a42c100d0b60042c01007081d45242440760360780220b8400244d540c1c8107140855551014142460109640c080b02c08a2401000c00540700c0804218140640142c1c10b48420b81166 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 698608651 1250 698607401 698607407
    0xd080705160b0403020303040501120e1501090f1401050f031e0607030f140609090102070503031501170c1921091e2a120c03050106060f1d120a0609020907 68
    0x584c003000b50990b004200a105544c062010720004800064010401da601a25204e003041d15400030003a040c013028006020a00481c00b900d809000005420000044460b00412640106204075405208048102c2c100ca403000c6c0142ca540194031980e411950b8610115950f1703580d0106d8031000024504020b528001f003060050042600614041c0d079225129902008901c03070026040c40065907080240e200020014805584140d4102c03c045603500c004c100050801d0b1410b0404100101d2480704000034500030400781e1b070711200d83d00e6420070014114001a642d81d0084814000005100000c1403c0010707184c0000144900c2600006812103145040c4070407858071840041c11030912010000c1c036204200d5006207099005c071440c8121607550071118218100301813040d02c0c0c5c0c0204400502c28010240289401040c07540b5104486100950004200100e020b46c2c4080c50800c00100746c4050f59035002c4a00c102c00c404068403035010041c80d0a8008220013542240a000f00000107186940 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 698609901 1250 698608651 698608657
    0x9010303050919180b0a0f0308070308040204060e0103082106030a0305090f0405180f060f040b150603090a1b270f150302010e030c031b0d080705160b 66
    0x40c0c5a2241d07418510040300b00031003031400803059028a20000781c00540249100c100e0703104001d00040c000354a103019024080b4030300854010484e207001401042002580307200c102c0740c586c0d80601e400201a1640d20008000c0d1145a00a900c00014000048140035500004140803a404031004030f6403c6060602074402030200c41c61545a0410303a542e40100303000f90020140d1b50802040c8440702d8402c10001001c0301d90070b4900c0400d03100c4500c800061200200301030500b00248000900342443d01541d00382c80310341e00400090082415502256500d103180000c2507400c80001d103226141e1514141c0d00b036507a4098a8103454032104041e6800001c1e460441400c15102d105200740f2103a00c481c41c281108108220500589039603940114038202901d2107040e1414010405061a0038a5400010035000ba00b10340148039401100c48034855a0b000100d42e0f400c400c44842c1c41d10440c018000207000c182907142c014011040c001800020841d010030f108020a0041c840d0003051a20750301c00b940c40e40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 698611151 1250 698609901 698609903
    0x1501060206071805061b0607020610080a0f02040902040b130c1b020f040504050f121e1809060105070b041a0c07030801090203151c03080a021e09010201090804170705090103 76
    0x1c1583c44103001c1424580d00078403407582e401642601a0a2048400d85803000c2202c0c003200680214090041c0c2c2c910000700340340140b603030000030020f800503920b88410120340140020310407669106104215121504450301c2403000816404203002d1702402c0342c01810300c15100b000090304902829446107480c41170340c140c181d0080c1c1044481c0f05d84000784801031401803c1a1a1441940c40c1c840d44514204007900c1c9108420600c1c80d29844424107910b1b50700114102c14446880500c854115040901c88200004008841420682e00c41381d0040c1d6040c1304032800901000c404901b00814810b6130b006040071000380d00105021580d480c1400c51603409825801800506030b50010050000c158000c0c0da0022400c1340300c840183e403110000b0318020a00e4942c40c3ca00d4101c2c07080c2d681810b800c10881984203440e00d806520340701c1074102803c11500399040c00301c0010380204004506d41d10035480400c0860b84040c09959694866004000e000d0b0000d4008007288201c2c04081000d084c42c0d40518126 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 698612401 1250 698611151 698611187
    0x302070c030519290c070606120c09050a0209030616050c030a030501080c04020301080604030807021e0f070e090d12110c070e060118150c023d080610090503150106020607 75
    0xc1e121620845d030310350320402c0240c51280d114100491040300c111314005c01c1c188124070000c1200c0c50400c102c1c2c1541c0c4010f0800b0320540c07040c45680c243d0748021402d580c2c00101049000b880942c7d0b8a8103076581d001d51000c074901440301084100a031034040d444141610450070072508020590810001a440240142d040c550050008600060f01a100c0290081d00e10700540c0d510b49001348e0042c102101d0749811881a80c0f1071006052106000c2c4030b00c002601500700001102d240c1101c1190751800d0715504042041049619840301024942c04000e15420400c1c1d06643d0300941611a592150b0a01131104424051004240d076503010340039442000b0813400d603078048540b400200318000d5842c00721f424140011503c0800040e614840500901d1f13010705641c82800c0781c2d4090580b0504030144c403c0910f028aa00201d00c25a007101e00c1c03962000007183e13034911415241e10304484200b45a80042e405100301e00000c4250100e4400f0302e4140d6040703500300d998131340d02d042c1c00300c0360b000030030781038001e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 698613651 1250 698612401 698612483
    0x18140106080a0222090305210c040512120c01091515050f0105070506040302070f080705031203090a0c0b0a030c03021c0c1b05010911100206070302070c030519 70
    0x60038410298652450b104c050340c603108a810130400182d42e6140c008030001940020401e110864547e4003803803206000d031403151680b6091101024510135402074a100d28043c000d2860540c40400c00380044420501025840f01c0c0c5804100d4080d14150604841c04400b00500d05a107582602c03401b0020046000d000c0c48035441c2006000080e81880344c15030410004216080c08100100401c502a0784254010500d083c6040711009000d4050342060308260800c2d10204960307603002407a03000c40c03032190b80314039030b81c1e00c540004070305d0885c030458000d01040c0c034a07800141c002c00e02e9000c0c00000a281e282440401c0c0070f18403c5080b40b10b0044142216101d4040071411411264008259a0010b0074541c40362031516240000011010f14112410f81d116a248004c00c188074188c03030590301e016608104207100004000e515800c0052110040540c0800e042080c4803640d90f90030003c6421a0035034203000c0e02612201c10215203518140d03281014481d1501c00c00440c080b8404680501a0036502 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 698614901 1250 698613651 698613653
    0x21f08010e0f042402070c0e0a060b0f2a010911010c122f03030414011e0c02070510020f0609030c0d03151a0a08090105010608040b040f0618140106080a 67
    0x15100f560400801480b035141071380c800100d0b00c684001d11549000c4c00038207001902d4450160078215004240701e0704141003420170000d0501c00e00a5034101d420360703080c5944031202c00442c1d0014a64112446c490001c1c2c4624081030b070003040d4002c490040c060300c10051004818001507070003400e1008003c180c102049101907a161151a090b84a062600005000441056491400800e00c5132007003400d07800000601080003a07070780c0016810010740000b440402c2450540109813a083c5102645681d2210841d0340218801d203d148041e1030b000b00002c810002d249002562165016070283c0c4600c0f404020400d152800002d071101424042c0041c520600d9102044015180c651080c08102c0c00c00c0c400403902a004540c0000d0390152840c5894866603000c0005044d0342e0040c000500b1a49080010310089910008071540280c100180a1198540b450b1031400c0000700340c40901928a065507030340d2202e000001030503045d8000d01e16600060792a00b5400d08985042c07040180c03540c0b1411800c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 698616151 1250 698614901 698614913
    0x7060c0f02010f0b090c0c2b02070801060e160203040923060f0306070f050c01020a0305190203040507090b0d02090f091608071401092102120c0102070b09030a021f08010e0f04 77
    0x7c100314150103544500006170814030720115400416203842d204056040c0c801a41040030718010000c07040248541407034a01043e403442005842c02441c00d800701c0d090300f1590f000f0001c6400404424000b008103d0100c1014030000017a8401344c0d88034206000803d81c0b5203080c0302c10103006030000300a4402034a0700003090342c01c0a00100750405110040c011003121170420300c0a80102010f50320007003181e280c54442e1040d4a02c3c0c854440d004c0920501c24080868000074000050790602c110001c0d400c0c809200040c012444d15100035805001d0804128070762b035034107100c2405910024111120551440d1242c041004d090240e100154000c002c100520a8040c1290301440e1040c1812038050351105034452200310030700c07403503c1a402c05107104011810043c818103040c01611010301442105000001d44822103071151850383c0d000841c1c856843d40d4140280c00315107600824810081491400500d441d91400d000900445c1c03d25000180003980e05c03511602c1440c3c0700da401d240c0c607640d941d10a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 698617401 1250 698616151 698616157
    0x1051e09160905010e07050a050901052a0106080f15150f060d1b03020a0e040506010905030d02010b03060c04060c03050c0709060b0304060b0402040b0d020f07060c0f02010f0b090c 79
    0x8554244290418075004488460000c006400031040102d115810801e480c000301c13801800700401c0000070002c000702d80398010300342c502110091808039514540c90301080e10f40711003c2c10041540100500c4190031110540c420f10072550310340300b902d02014480100540b203280559a981d181022440014030100c18640032800d40132005001c0c13078107d0265004140280c02100003070355055500d012080000e0400b410110004c1054501940741240820004010407110b01215024a40720004102161700624040d0b000c2c01c80070b000c07504880c54051009010348015404580a8000c6034045560114020704580681e181515a446184800e9804480c2640203500c9500130b4002c1f2940810380400d07500500e8001c003034402d00b035600c0c0d04180c00d0000c12a0600100c02d80b14500c100400c00c0000c440005a60284005140c01600c44c0c06020b508011840342c503a0040116240c59261505150040e040740054030031503008018040003000a14101c0d01c803100ba09030b200c41020001101942c0700e40007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 698618651 1250 698617401 698617411
    0x2030c04090f110a20030304151a03011506080c180123130e0708091f270b133309081c02040e062704031e0201051e 51
    0x200052845501c0e400152541013084d04a0000304070605510400c4214001c01102040ca40051895070600c4c3d902d1070340511902c00070000454036844194044601803581003640b0b50050002d1208503400000d02c000415980601400300d9a00f42c08118131003c3c0c0010780f0b0200710f0480e2540141f202d61001900d42c3c0d05e0f0400209042d000b5040881c000c0f00e001c40140c103d105405c1d00b82440281403814016643ea0020199010444501d0030005001c0b80003030404448402d2081d881c10800c00041042c01400380c01e0300140c4140344108404403021100c102c2e120a49016a68458403921034074951600c0502904014241854251285141c140c0380d500e114030603082020b0070980c600300705000b40103489140100b500d2081011a1112000c0c826802c1c124050051f170380c04500c2c0c0340c2058601241c2c9103000d4101c0c6c0c06541d0084100340c551007080c4800d45400b028031207800c400d1400d403070003c10001c04040100400c0704450b0707085140307600502815010300040e5000c0b440003100c050343e040300351200130b007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 698619901 1250 698618651 698618681
    0x834030612021309021c0807061410061409120c030c01050a12020f040e270c0102190204060b03010f030c050429030327091e07050304050c040612021302030c0409 71
    0x41b48907146e80c0720010f80c0d07181c10311444c0705c42d888071068113041e021110301042c0100150030900400c0448014007444405032515030071309080001d44402c5a0f00303a4050f0075050742d00903503507115144c2002800114100344841c21422a0018242c00c0300441d0203006240d17030700c008128600100700c055804c42c1c02030f00c400c02e40009514186a030314451460400010b0314000c5920303500ca00c0c1e0f0b9501e9a04020b10800e00031801000700350078055940000e55580d450b01d0508501180480000110341d5950001c0d0000c0542072800794995031101002ca6101000740b104a508400e03411000501d414140248100400600810901c000c80c0d050460000b6002c011707071070307454002007024118100c85000740034250740380b0000000403207164100340300417007901404083c4e5001d240386441a03036560081c00e03a41d00c102d2503e0000d03102c0e196032405601e000080d82c0c103180d0044c20081d010480c0d41a4551a0a0045c0210381700410620503a0484003207110030340700d481500004200a001100702c0782c1082000c110080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 698621151 1250 698619901 698619919
    0x207090203130f0609060b06031b0304050a0b040c17011401060318060c030605090a1107030c030207150503092413031e08010f060302120601083403061202130902 71
    0x241c1c0740b12030f0003507941e0122040b941d2000060244540d41c401c0704040401985e10b9451414100990340944440041c0704100c0a40040081d08001040c00b10241c1a544880610348505003481c1011680d41580500559500c0c8520f6003400c0d40414040c1000e800030704144000107908044082b00a40100141a04820f14500011001482030301c03e03103600c5902c903540010294101800c100075880c020b0b0402c01c0c40360800000030300c61200e880448403d03035418248900a04024507041c0d0030500568007008080c503044482c4d050312500800158429040c14083e50040600c2d82c0348008500da043d203204640a01c02800110702c56000b41c51181c110740207041108500c0703000c5921103000c80c5000503800008525400401c59400003902c94000b81400d420f00790f08015003850b41c00c10740c000080002c1d042054120100e44d100794440712590b074001c48a400c5003243c0c804d010080e003421101d440c03208000b9160030b200084c00200340420004580e401030921803500c4841c420351010700441d10317050ba480f081003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 698622401 1250 698621151 698621153
    0x20904021207080c010e0a3f03170603060f150102100513020111060106020a260c01090201090503150115050c060907080c0a03260405121c0f020709020313 68
    0x402210b001085240c0043c031403402d600c00010305050000340c030640141100c0030244203841d81740c010f0030344c10058042c403100201e2288040c40140201c0e298184e4a02c09100024414903511088000c10b08407512110034490311202c0615682d40030031104107180d50411f0012440003203504011010721141481121100301208040004491050701c400180c210040f0412007107580290503407280b1b4580c2c3d8080d03d8190306d040ea010391500c840c10001000c0260200240d20b0b0001100b86184800d00c1e0341d00c00076255803240f40c44d01c0c000c040c038200036404107440b100000303400d24001502701e11540c01078101031074a03440c1080000405c4a07410b00c1c0c0c0107001d82070006200c0c088003049182d10400185004214103403600f05080c0c1400182c100b250f009400b4540c00340302042140c500e80c07010b03102c000c0e0b8103003036541ea40102c0d099901a035001154441c05400c8600014003000440d034a401888800d03400898240035015140a9011044540940c2003200704004510b03440e0302550f48400711a0200c1020002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 698623651 1250 698622401 698622403
    0x11202030a2a120c0621020702043c020301061413051f081e130c1a070614010302210c0303121608010506181c08070210080c070209040212 61
    0xb49030004007030221001c01a805102541550000900322401c003021200c030001850318210740c40c1030a6010481d000a159001c54542e80c0c00010381446001407510b130561134101c0d603400b40c18056065035085180a008024001003803007140e0403164103442d10103070400710710041c114541050080d18000b000f18800081c01e610741008000984030b149444d2002c8420b2848091300c5090050410000907605074001c1d44803c1c14440c0840e0084403144814001544030b01c0c104110503910f0300260b09952900c00c52902a05400b006407051511514050141008d02d0000008841c0248030103580940c07a010f90440c030036011180d62008801070000d407169040043c01103859548181c03105004150711404000c58004030642151450000346420480d551402c400243d040c0648600a280840d01c0300f0405401c0e0f42e4903e1f02c516404400081000488060418190726048001c060f801065203180214045100f03840c40c5200d2240b03c18014200f10140d002e00c42007500090080740c204420489010007480 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 698624901 1250 698623651 698623733
    0x2a0e100309060e010b13050702060c07051c0503060102010b041404060203060a09110a0e18060402030703021b0102040602060f010f09050601050c01021c150b030f0702070506040e0708011202030a 85
    0x1244000483c5c460484404e201d4954032040c04003da00e490f04051000302c640c041035081c0c12800038001640c8a45070b900348182400324840841a00111150300b08110781d4100307010314400e0809800070042040d00400344000c0c0d640303e04400c202a18840001400a152035020b1a080040904103d1070b1948800c04541242d6100b03400d0500d1400102c1c40350313881c0380d009025416200085e114510840195400d0344041030024001038070490300400010b00740782c803d034181c0b1400c101a55040058a08610305c2d64000e40c8a40282001405034000150b4100500c884030b034101c1b5003180e9804419464142d43c1170041601508031030400004202c040e0104209001030b2110440c0808a1490400d5000c09941241d184e41c01c0d039811028000410445160b042c025694000b44120285220b0303034545800300c0c01e215080e0021903008a0108011580410246120303219100c3ea072103541e016601c80011072840c401390400254940d202c0314051001500211354540e189169440c030001410b914114140010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 698626151 1250 698624901 698624921
    0x151d0d080f030c090a090e1b36220f030e0d060b12010c0c080c16031b050103050c0409020a18090902180402030601120f05030406032a0e10030906 64
    0x801c021511580c0e83c0760405d0035000a0241c414104002c035080d05c01e45403904a0901c448420903408205c00300d29031902c0c059801d00d00c44051141c5148015000000c1c49080c0071340d4102c0703800503010002101d01c1c0c140c6202c41080e145c000d44940036004580c4d9441032844146004404000b204010b50440d600e8070b03503851000c1031040c0700c00b280807107140062200341e0043d004120240c0e0b041c1090044c2041d001048034603169004000103588100c0006224039206196411184c00540c5032800018040400308094018000f5800e04016541d1800114207481083c1c841c1c1510140400003000f000c80e9990013460400741d1030500c0c08504070080da41611150080d403200300741ca038462501c10214544241c12a070613080340c808020300c03400e1580200781d9a0405000780310025041018000500810b80c080420705907000044030381d1389031607620040140200e000001645c0600b00c602e100c50b9a800c00c80000560520750701c603540b030840d6408010b00488007003069401e140e079a210309804560507010b002c4140d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 698627401 1250 698626151 698626171
    0xf1b0212031003051b10080402150d0e03030114030607020a110907031409010b1003060b22030602340f061d010204030f0b0105060f070201030c03020d020307020106151d0d080f03 78
    0x4511480203006d804140d0b07405c0031040142810410006075100316000c0c4100080da914145c1b1111482d4a0000038105100c01041e40d100100000421070481c042e80c4840503001da003a0355913503d0f00f91f0180c1e0b076a018460002c000d003080c0c1d40005403c1c11301e40d0440d588485079190203d00d0a01c507016090041170155601440c5945031098040c0c18100308062502400c0b003803402300403e9250002220f4503004a080440c0e503440040d40001c6c0c030a110b81e412002958000a04643d5125200240100804400301140d0140030052440c408003401c0c0e000d023001c0503000741c5034192590299031584010f04a0414030f20041c012041c1043d55520240b02400245228820740320b08024030381003030b00b100b10707050384014403e8004102e0100040e5040c000e407042d030f075420709001c100c0068548054000c0e00404c00b004102c64808003c000d4041e9054110100715000f03100c10141c10454400b08a80f85a2021801008014440307204030043c01c0040c09160034a000c0c2100d6410a0038404003070080385d00035900480700e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 698628651 1250 698627401 698627443
    0x60206040f1a04050604020411040b16030915080906060411030a0e0f0f01021b030901140c0703021e0406050301020901051e0409022704060f140a08010f0f1b021203100305 75
    0x45041270310840c1082403070740f03010604283c038160300c816051003602c40a800101c11700c03652038100740c00390001c41d024095260900302c1102ca541c400505800045608803410301c0384001154403414203102c0e00303003464548140365286543d51484000500b00c494103030402803141e0352400138440d42c00d01404d01030320300302000035a480401c1c0803000c0c02c2c040d014005138400d030001c101802c0c2c542e0300440070b60001c05441c0d28481c0c6400c28040550b042c000b581d400a500802d910072003d60083c540352145020b580300701c0d000c128160700c03403081c5801c0f4054100001c0c04100108a80c140c1550440308801c1100d112006c2d903840c086e200e0040b04260b03000301c8042c0700c0500e9000c02001640e0b20090b050b90040c1400c3d5410413000d4901600e680300b400842c4104048920406002800784e1903200d808005010b03544004d1204000c1c0c4200c00c4d0041c20300056011740c0c589859524405178001143d070300e2000101e0740c0140b5140301300b40350034100f42e8009420040c100c41c0000340000051000c0c00803403d440b94190785210 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 698629901 1250 698628651 698628653
    0x20a0c0302060a050603060f0c09040f0c020f3004030203031b120f0d0b0f03070f080c09040f020411130905071403041a091005090c19060206040f1a04050604 69
    0x4500700380544103c1c400d0381070504000094400003034280d03105240c481510b603207032101810481d407445081030341600b103814000302d02e00c3d8005c140c019405e1003000d41c1c00c852001c002030b814070303885507452441100c000d40c1d82070a03603082c162030250407203403880680e802070f05d02a030366030029286500a040c070082801d117080c09941040014401507142110300b000d110302e840f9801c2c16a0215200710f1710185800d07030390f404281c101e030b8450000e00a0002c8015007142c602544803e10070000318001c0c4107040721441051060384560520721015806641c0c450f415a0f1400c40c1603007008080c0514025094035501c0500880c03031030303c049441e0b10f0000c10754904001138034108664000c19416480907040d1120004209202c00594507000f10707002403010110010f0242c07204403a06041c05180ca900207506410041801383d900740101e030303442c01e55104541200c189802801d01c54092580c2d40710b0400540c01c184000780108001041c440c034050b20450f18070b901c00e05120703142c030114401034806407015401941000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 698631151 1250 698629901 698629903
    0x15042303160c0605041a0a0306082d0d210b0904120f360b07030908070f05090121020913030e1c03050f12090d0f0c120c020d0501020a0c0302 62
    0x5001c0c0a035444e10501d441d040900c1016003603041c2c02604024800000c11003240382c881c0d440440605084020380708143ea241807580000c2d4032800f00c80020f0b042d40c4810311200400000c82940c40c1d5456101c03202100b404280401c000c024000c040d020741510381071400d80c96034070612404d20036441140040301e1303c00c42542c01040d00188240300d20602c00109010075041d00303050000203080c0c85c1d209030340c02d009414144601e410010350303001d42460540071818078101900483c0150a882821084031049a613441121080c50058810f40303401072400d00060101604000072049981d001000003848200d8950202d14180012221503000d0a0100e9915082650021001c80002c004440201d407030209000f841d4426a55401c0050a0000014801d2620300480c0f058400304c09110300782c9400c41c50328814141e21400d5030400e0b440052440c41d260900c9d14024401c010025030401d2040c0024510240d041da402d4003040310a0741c1c4031000e40100d0b0001202400240015102c40e9580143e120043ca03000e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 698632401 1250 698631151 698631173
    0x3304150507020a210204020d0c08060904020a0b0a03090807030c02030c040501080d0c02121c08090303010b090402181009052b0303020f120114010f021504230316 71
    0x840030403108001c1a0050390b00e4202040569603184000b441e031009154007504410145a402500240041250100740903507a018580ca6a0651100340b440d9803803c041040400d81200c000354442c040c0c61052000c192000090800300e441070400054040e5a9120340e240c03508803001c00c40009882c2d0203800210709081c80401c410b19400c1d076041c000d950600700d00da40c0b1a007100340c01c07404000c1ca640c021020756890b9003000351030000c03c50581e5181e81694101e41000c030403540c406408110313850040740500c0800001c03030b4120380c1e100609501b000c846030208406075011755045409039040000780305e00e40d541e041c1c0b449031402e06e0352210703015649000244661001c2c5040807400042c000c0303a04044c9013003041c04207038003198946001641c0b80b817a40c601d101e0303900480c1008070346000540d00120307150340b81e424001c0e030002c02600d5403602402103420480c1e60301c00c11034640d100740c00400042400030701407110803100c0d95450000744044201c0720407041e1854100c0500f403941c2080c02040413080c00414030784 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 698633651 1250 698632401 698632439
    0x30a05070f0c0b1312030f0e040f020c010906060e070518061b0f0d020f03040b1e040f0e0c0910200d020106090b06030606120a0b040c051201233304 65
    0xa02c0d40e920242d06c0141c15245180105002d12040110340c00c800e40e1142e011102800c003c0d1401c40d20742d640c0b401c2d4103000300401c41040f54400e02d410309c0440d00130740054106115101e030750354552900410f40e800c40c0c07003c4401000240c0022084c0400180081c15a0f800001c0740f415100425001541c904c01e1450607040b1903004041d50400c03042c240690b0004000c17101941c0c1e010040ba036a445a040c00e61582040001340303d109014082404600204201c03202411079148034029243c030344507100d240015204a00100c1d034000b8040c5802d440050141c00030038032400c0c0c529101075204460703200c400d09205003824a8001030b50750704004d200d104000d100c0c9482e801d005880c202e0843ca4940c000c2441b610552443c070640c000c540001450f0070040f84c001c07080c4004003400c10302c0441e451300d0000e4519008a0304c10100c2c0e00d10a4000300303610390b107840595031190b44020401c2802c401178041c0030848000d918406000f0805003102040c40d1500e4080c00e4880d47e010200d9581d5a2500382c1c0701c00c5600441390 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 698634901 1250 698633651 698633669
    0x3020c01090f1403070911030906060108010b1b010f0c182301081504060312031803080604020f07020910050a0603060503120a0302120f2403030a05070f0c0b13 70
    0x8000d1124040c0c0c0c0311500c00f0b4070000f1007108a02c072410360001c0c0ca8107010350310940c28581801c0c0314880800b0700c071020b180520024006c95880d621540300655000601340910b00c107004082c0000202205504180c0c4445080034000242c1a403144440740c007581c2824079800d0200b85000c0d00c3d13414201212401c80010200c505000842d070500040c01c4d2005440c8840460401610001207185100055084104100020000c10044e60b03039203008601296100001c0303000c070745441c058445284031900c5c000c1071a60b05540380d40c0c1540d04e1000b000001d401c00c00781c004002600344600c400503100c040b50035011301048020780000c1c510346001c0000c424426000072041500308141001b050300c0c00510307904030240307243e0000d49806a840c070440003030288030044981617015201b0301601144081041f8020300820303084680300c2190354050702a0703103440ea03080d0b0313059402000075540091050014202d0390748629086500d190007901c4500303070902550000c1d8486034000590350706940c1c680e072107800103010303d030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 698636151 1250 698634901 698634917
    0xc0c0e01050a211407080319110d12180503040f171915020f0d0914032d130602060f070e030307030c0c050409080405040e032a190302060403020c01 65
    0x203c0e0301c0300511403030240103007003810444980445400511840018080c10021252224941146040f1034081e00c15984041090805440050100440c03100c2803202c681e128100c201d07112100140041003409600000b405180d0343c0100024028802000108065994106d2090070440d58003440c400c1e120013041507601c242c602512241c0d08410b104c9120f90043c5407500c0852401030700f0800380c8102035043d40903400014403958201303840d900072214540145001162031522035241590f0744661020000449000d0203000d1501018100300c400300c00814140c81c0c22310111900c025a40381141d0014805a0032440070002a041280b1605520403641d142154869021501090b140c1c42480f401070104541807503e1410702585002c0d00000303040c0504200038800d12030410108942042c0a403600c0340b070400c43c4c00c01e10080c2c00025550918510344046090018070103030146108203880b50149103008008800800d032410210b00c0740c2181c0203402400c2c0c0b41c901032a0080c203014003031001e21f060020301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 698637401 1250 698636151 698636189
    0x8030304121e0311130e070807050a0e0f0604050402030c0a0e0f10030c03090215090109081b011d041a090f09030315030109080a020d0206070c02060702100c0c0e01050a 74
    0xca581a10100e58240040c00120002030510503105c1c024004da01e85a01000008030031303000c2240188140c0d0030f41d0318100640c0380d021040341d091003400d1014001980c084114151032407c9000e0650803e0014043c03450295114007240a0741c1044803d40d030000000b113203001c000c1d80c20540185040300202c3d2414014515400081d6020000e001e941c4200f40e540c00416010034001d5000e200c003150010b042c84074400b40444020030301d40c0000c0ea0035002607000d00c00040c010100103164010002c01c0c0106146481428004440c6650750400b0424000d100c5401c401c0c05440702e10074480800e02c4100354500c081080418802c40b01000743c0340000c200c00c0f0304100051b01c000031003500c1e04080480f2507041d42e0303540100080e003d00500710015003502000140744601da80c0005003903030302803001d03007e840720703079882c81000c0c1c0e58000c1c40d9201a40080080000200601d4083e0105c0c04d084210f00380308041c00c500791503102010711103422030619030414400511840c50160f0424004266501400c410310010f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 698638651 1250 698637401 698637437
    0x1903050102131415090409050106091a0406080714060706020a0c120f0e151b03030702240412030e0613020102060a0917030c0405180114181f08070803030412 69
    0x4103030441500c44d9000309070003e040d5210782290031a5a0040700901045441d800c0e00c600820502a0760800b5580301810140303141000e01542e411550000054424103103030003e411141102104030951000f800c0140c24002061840034290180a650f540034880c6154684102d044900c0da03140007c1c8840c041108840c1c1e030307000350a604c21040030750f00303804580c0c05210300f22954002c0303841c0c5082d8401d106031000040140003001e58800d1403075a003141c1d400124000c481c404980c24038088842550782e040000c02090102c142c02c0404548c5250026052198500440c104903041c0d60303024050228402c2e0700c0c250743c0d04000b110307080845040c0400904102d582c0c0c9454500d5010807901c403000d00440007038030f40f030b48020030b130317401428041d2407022001c0f41c8408024280750309002d11181102c1110400445060070303401c1e4802d8800c441284040f0361030300d604030407803000d4880111180a04003400403c0e00300c000c1c0007074001001d2080080d5120b00b8240303840d54103400d42941400400100c0400c0b40a8041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 698639901 1250 698638651 698638669
    0x60c03090615011b200405010317071109192a0309140102040303090f0b0307050f030402030a02060d0c03052a032a0a020d030c08011419030501021314 66
    0x601e44014984181d001030050300c0402c05582c166030b50350420441c40040c000e1060718101030381d221040408209860f642084100c4074203000140000126000c074103a81c00b40c05000317010203404cc40c215500c8000207800180789040803120300400f408019105101407000703014408003d2011149803e44100c40410000d4840004c1100400c2684510381d801c28818610800480c84400324003c2d07507a03503146c0c2000780c000016842640b00d02d210a00340028542229000d0300c0c01092a41e40c0c403894681d1350306405a440d00064816a81405041074030300040e82c03807000401210111a00200e820503480202808031500107010043c4a05100d04507103000c10001c40806101302c035030080307584035112070190a0900e0021120401c0803017000c075140e0400e402103c0035200c0c1c00c42550803100034094002c021026212110040804075188100600c181c100401c00001c0c2910b024241940000c4107481307000c0701b400799900c01d039000c3c0d41c006200482800d081c3c0021000c0d0412250401c1e08080c81404035205076 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 698641151 1250 698639901 698639911
    0x30b01031b050a09090e0703031d0105030f09030c06150a080f0627060c120a020921030706110702010207050901030807061e09030e010201270803040206070c0e0702060c030906 77
    0xc0003803c0c280250207211000c0c00340101c03e0b8100012421403402c1e90380c46800d8003064020a904528080c0315188030700c47c800704554181d46850840d2280c84009036080009000d80340c1a0000380300204074034008200e9544103200a40c0b0b0b181210300d9034418009000025007140c101604800521752421700d0004d2443d81140f03004011aa564010721240d40d1781164660280a0900404082c00005603441010300000707003807501a10b035540c480502150032841044610740d00002c110801c0c0d41d550740b01040700d541100b806d6003524500900303035548400b00e589010010801400c040303002015560f0410400000d800c05450386107155066803509030141c02540c2000b00304903101c80c18142c4801e414022090030b0b94440c542030002c1e541c2c528010f4032119155107002d00542c40d151404214010b00d03031080108c062940b03000c8901c200540c0301e0810741c1e13000800030380e000013040042d03400144065848800400c0762030004d40c0c49050440009082ca81d02030017140c840281030091004101c00803840b1a080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 698642401 1250 698641151 698641157
    0x1e06060406090e060d0209070513091b1808030f07050f070b030a0b030a140f06071d011206050604031a01120b0601080403140a020f0c030a0305071203091b06030b01031b 74
    0x1644c2e1040050001003506000075005068441440031a64100001e00309290b42039144101d20b60311055640d049410001c4c40354040c00b44000c4151780c00380100c60f06100112401c02d5224402d032030302c03100351440d40a40f5800e2450b4000207026424050306001803401d5014000c00b5144061603c00081c40c00c0c0030203011070300c04607555600ba00e0b041d035003046614100f951000c102a1221704160303900d52200d5a50f0301c0402c4601070f02000400702d500c51207020a256803004e25403018124041d004441c0c02e801004851400380c1c0c0c030900402d081d958440680000c51080e400ca202c24540d4042020314800b040e0300209503125000c50482c0003c10158040358422002c1c44c20746000e80d22030034219040901c510306240781040004a4440d4968042040300c00d0041820841d10501d0041c1c05142d0b41d0032610401400251090100d400010811107001580320310074500812040c9244d1100844032a00c41002081c0802c003035010883d854160082010302d03142400e04000034141c0c408864004400300c0465020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 698643651 1250 698642401 698642429
    0x1050f0d140a0516020606090a09170414031614040203070302120412020d0507050615060c010f0207020a09051006030b0613080615060301060512041a1e0606040609 72
    0x304840e03a408085580c00340d01618225003400346004004180640320151a104100000d514460000070000c5c000c10b0041c2030600280d450b48190070040030120b40455841408004841b0b8244202014001030021000c0848110001c002010720740355205c41075901020724000d00b08134840001c0400104e041c1c03b590056075a50390b1070b030200c1c001d102e800040c25081c0ca04501b0700013448081d100208146060303800700c5003800454203040d205401904402800e90380030744e0020348039010704900b0048154001d44070b40c1c241078152020314290b40b40700720707107802459002c00e40340c041d89044480c4d08010b00d07280c0420480390800720551441a00180110001c0c903442d409218100d48804007191480446140c90400751511284540e8442d00143d4505501c0c0d55654600e8040d864840c04490480e00307240c6589207440d40110342e0140e0240000c2040d2400359100b190310518840301811031f481800c104c4500c030000384403113945000200300900820f0080c00d050105012181d0002003407000c1e581c08112080e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 698644901 1250 698643651 698643667
    0x121501170c1c0f030804050d0918180807080d050c07020d06050714040b07140105071d01090f0602010212100f030f06020c011104080d020307120804050f070f050a1401050f 75
    0x34407042d103080700800c0345065100d142c06140d4044c803a00e002d14441c1c0251240c00000400031103d912450180d02d092540c40303102c020100e02c0c5940851703009200740c40c0301540c1c0d0000d078646644075040150207035481140050200304031071052180307550201880d42010704000164010642d058005400202071a40c1c40e008100028040c91103c0da00220b10561aa991a01c940c0d80c40c4581d0001c0070b0842d040d8115108030380400d6418002c2501c0781085994104081400028868000b491104294103002420b0404125071500c1c0510001400e943d800141c0d82e00040b00d0a0349400c00010444060222609401d100c41c1c101a0f050030116038002210740b0700704d101030801100a100e24011f01c24250b1900e509091f00c0c0600101410031903400d5429541e83d8004514141d84a00c80c103000201203c407600380c0020024001c802407508540980c003102c148510070580c0074135109a90b0426026403003030540c100100d241011640b4041c02802c8400a103c0841d240080d10703900980c070300c0310307000100410880 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 698646151 1250 698644901 698644939
    0x40b070318030f11120703080c030c030f100911090108100321050f0c010506130e070302011407020a030302010e0709020f04140312070b01170f070e15121501170c 71
    0x801c00b200c20301c043d900b4400170701d11442c01c80d5200400c01c401080002c2c001800d18001102074034032460b9042c00c114510b6480e04401d4004800091400d010701844100100c2c0b0381c0518410300e02d02c209114281c5558028900000d00280001864060b0b000b504041c1840041d8510075420f2505d0194510300d981904070560a03607150003140b06500016101051001c4d813860305400050084100f6240c10403c0052708031814107490314189010340c00d038880b400070801944031f0030000242909c0c981c103290806007264002200000141c1c8280e005079101c40035001e6a05083c40704000404221100310314000c60744c00007002d5400741d0711989a442d881d4103d041e801c1d4030140200400144030140550fa60f40b030710320308500d0340642030040e00180d101c10380211000000000d032846020408000801040b4508200c0d9180144c00404581601490504019083d11000783d440e542200030b07000340420590303d1840310410b55059101030400e81103c4061011080041030000c4030103030a1b06d46584814800f1000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 698647401 1250 698646151 698646167
    0x51c0e030a06090c1e0b030411120a030905060a081302030a020a0603021305040c0e04090c0f080a110303161104090b13061125020310060b03040b070318030f 69
    0x4a50036004003040841007010a034000c0f145035105000001e44d0540725100c0c05210000070320400c130f901001400902c00000740d10003559204e48074001c2d943c4044030748001f087d00f02107001400c600d00d81c00701c074010b01016001003000015000c00d59000c4d0030512090001080000c0107030100c146130030b50000010954900348284100f242e006444065481d0f62084001c0003580002c1c20b40c01c0c1000c028202045524240c09050700c41d490303e603107000310408900308200c002d00e442ea40440740d085081c0e00010701484c0101020b0003c22603c0041c15905660381844564030000651044c03190b001005118000280038040c1400310380c1024032400305001080108008240c40d060150000c1200400c00040c0c0b0801d0408031140f0380f0440303050003080d404200c41003141c0174100701452046100c0000c0d0b59140c1c00d01c224060501e0000342203a05488807016400201c0d10203810645441d5000000c00c4140204d00001c6504183c15207020011202c0140d94404806c85400b001410420035002c2426518407070b0b806 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 698648651 1250 698647401 698647427
    0x30f06111b15010b0708090a170706030b1512340e0406032004061e030308090c060403030c020111010e100f0509030301051215040303020405040b030a051c 68
    0x1460740c40784108180312508509401c00d80803445405064126800000c1100c1e048035180c510305400d24170035603034a20041c0c100400c0143c11058668000403504108454801400f2041024040150800c00000e094a00e10030b030460050003113030814100d858010088070b21800c1c44c141c0144480d01e50021074840c0380d840401d80c40340f0143e568040c0b0f49899500800c03401c080816200c0340d00b0780c6582009e20017aa4140d2001501021100780e880c41c0c50320b41c280c1c000b188120018030001b0303c2030f00d541c0101040380110480340b810824558080c820580c121203030503041050341c40100f01c40c0d03c001d00050160700c03c5002c000c04010030715451500f164050a9441241e480c01c00c024405510100d00c06940c95a0b40112020030130304011000c42d81900031f100e400e004a1303c000103035255a00304014040421401c10002c003ca10600301c07103032441149100d2040c0194030030b580141c0c0c1c0d286420100415038003001e003a14402e4100004240004000145d5141031b9000183c8004003842c0000c0166002030044034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 698649901 1250 698648651 698648681
    0x3050304020324060901050108090604290a0203010e1008060118020910080604291c080a0206071d030303070c06060909080d15060c032102040b0d060e0c04030f06 71
    0x441c03104010040c0040720310030602a05d60041913a43c4a0045a01503402c3ea000c218a41102c0c02050101d80481c103074400034002c106000070020810110701ca2941c0d41198101c0000342c0c04801480003010f19010641c1000d0040c400102103402c04e0201d907100c1d501846943c2c03180324442c0000d805114150140c03543e0b03a000800034460746441030406001c541c82118418400c80c90500035000100d41001d005503142c45085e2201c00750310354901800001112a2140780d40c80300c051202c0c1000484507401446507140c580c2c0501041c4c00c100b5000f40ca4806000c8211031300900c0b4607071154083c2c500005403a44040d00b450001340700740182c04d01100030040c43e08401c0a141c1020900c6060140c80d000801d210701091400b0883ca801c890f5491403405807a0003200002820810b804022a102e25000058801142410440d03004128904c100302e0344103078400f01030034030089070302c3c8035000c21445103200500b035190310742001d481e1028040034a48117501000b07001402841900051156907400f5a11940c1014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 698651151 1250 698649901 698649943
    0x106030609260c10110702030604050a0b060411030a1a030313030201110a0b0606070503090a030f031805060415030e0102070606150e09060405150a06050430030503040203 75
    0x400c1c4030300506000c8403141c2908084120b440e90748000c4070304a40b10000b9050141618843c14900d1901400516042c01803401c400d1000a015070b905002072406581320344002c0c08104214a842c42c2442c6c0c000306914841c9182081b04203071140c02c0303411a544103842c2000020402c000c00d082c0700d0791786084003c040e003610011565000c1c08480680210542e8002d88903c1d1424621305403042ea61a810078000b800138808102059003030425001400283d44148141d030b007003808520214680001c2a40207449000301244010241034010040302008420412070301d840e242014042486882188125059031026050305034a05200e03502041d049141e0400a66865070341c0d043c1500a01014011001e2540b41c103114107816602400c0c600d0100071019054180c01d5035950100001008010803e0031100181c1c05020120b54400c50650054265501c4441e200c40c18044040e056140d034415103a040d400c1220b6200040c1154400000c4641e030500d800c3d46e50fa510762000ca820883c0c9003248004041140c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 698652401 1250 698651151 698651153
    0x60606050307020106140307120f050d0314220b1b030c0a020f0a030909091103061f0504090323040807080a02041109010503040f020109180905010c0810090c020106030609 75
    0x8000254001c81050f40284145a02c0b900c01d080440c54045e52294550b00141042003c004070a04180b10301d8000d0000328850102d03500c885052164180b81200042d40e20602c0c00c000308aa804140c1d0130911030b138900c00070181c0c0c00107044141d602c0d00d1000380092140800140c1001000c0c3c41006480044540040d12418440300c1c101d85904958032080142c021940300b182a0400000e00240c61501690760320b00722860900d030a0028411814180c4115401e02d03554100c58400300b01550041c0c5020f505c200150842640d21400302009822052143c0d0410f642c62000c268016400611102c0c81c10400c0b9440d00b05405664003403049034402c00141c0250900040c0074035001c116000f6070341c001c0d60184807510740b4a0107031003070340315103001e0a011a0003440802d0103c0c006a80114682c0c0c41810400c4419881d11b05503440c51840815040b006c07502c4040b200d081010130b0007420205451400c0a2415040558504c00100034900464040d5a982c83c0141e25840c805d411190045030401410090540d403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 698653651 1250 698652401 698652407
    0x71803050604032307060506090a020307090b030903070602040815010b0309031206131b020d050306010503010303050904140c251a070212030709081e1b011202030c0403020a0b0903061b07060606 85
    0x8c0f41c440b4410021440000d05410460080f28440c0c015651580515820061101443c0e00082c0201d64144414803d08002585c1480180098901d4030700808130310803107103065001900142c1001d04450310a0041c031009110000580b207103980025840c8015035982d101198062a1200c003540040303040680b081b0030b4034001c046002004110764207682c0480c50040060f9000d1205030f03091030001d0010401000031900c514007400c60a00d0041020640810320100701407900da0a1700d10446e804000a0785007203900c42c4035040d17051721110292802a50400b52209041901d115a00080082d405400158020b100713111029000c031154211a03182c1c00c1ca1000104940072900901070507100c1d200780c0009510040100c25201601e40380100a107160b94a00381c7c424602c040388031814062030600700804a000ea001035842010320300c0d249a06ca51030b500400c240068560b010062103d41004560305d6500c000c00c3c00caa009942c4290380d045003418400c1c01543e44a60030014162030300c0d00740d022400c0ca0f8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 698654901 1250 698653651 698653661
    0x5070b0c0a0210060608060f0402211e0405030318030f190f030b090a0f0e100f050f040b1b07051005090606190e181507180305060403230706 62
    0x1081d0708603140d001c3c0c039400c000c00b21901d44c091480407802d14000951b107481c20420710341402c0130150001d802d00001101414042c0091a8260346450103242046000c03c0d842c1a90300c1e031002c414288003800c0c1040e45541d83c903480040c2c52544000114580c3d6482c000040040302c226009004805507940361080c04c10724600c2c2080712150004441900d40d94116200340200d20b8002c07401011490161110085900280700d0340104603040c5413190544100782406114103905810702c7c4601240218040c0700301421104014403540007214504240000700d05d881005550000311061111590900b4250881071405040b00040181c03040501c0aa20341e81c1e40d42007680141c6403402100da00c1d41314003040095410303e05103010343d13809182404000c994484070390550072100d0b0410109030503400c204e481d410510900c0030440c1c900411018000c10030350007010501c00d403102c00d0b6540c10540c115551075851f00000b50029082107501c0000d10a4448100d03c030f01780842c40b0840c11a903410079494001d0143c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 698656151 1250 698654901 698654917
    0x20d0f0302011a10020d0e0a050406170f0706090b1624051503030d0917040305060403020c0409021503190203090c010201061202030307030f0c06050a050a2a0507020105070b0c 77
    0x24042d80b0f01088142412440c0e519491155000380c221294264001c480c8540140714441e0701105401c40014140c807a84200300207041034021138190041224145468160492400740d05079004210401170700354050004010303105a600d403a5500c10058140d982d003110096400781c00709551040101c1d40c4102020005a40c1c1c003008400d01669403030001e54611041d1120080f50560420460f140c0d41d10350791780c40400d00600c44c4007500c0410103020003000d482d80050300111503980c020710900041c0341d010007030094102c108440078007200e5125800725030520001440b403149054007002191203031181c01c0142d54000300240d411516454100d003600d50340e260240445006d0f51810a01142d01c404100d070844d042c2d0b4010b0029403800b4a16075084071003010960042d810000035030340b0b4400182c45801418043e019685c008a41418600760100889881010000c2090215039a154800c1c08840d04c202e00c0069500f00240c4508240c00142c44601c01c440b0004d100e0004841040f005007081d0700641044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 698657401 1250 698656151 698656181
    0xf22080409060f0305010e06010311152119180f050c030f1c09030b0606070c080109030302031b12070e0f060d1a15070204110d1503111806060304020d0f030201 70
    0x4c4e47c01001c1464544c03100380400350142d158a0410103032410082181d4203e4600054640c0c6481a030f2502950413100f10141900702d81c034881d06000740751a80010824505407403250420507070050801400307003003095103001042c0b4042c140e80035040c0300c01800100020640517040c1da029280b1a01c40c1500c40300c448000e0010300a110b4040d000d42c1c0d10402501064030790000e1501f0103502c80c1c000708a41d45d00001021100f4606003200401c04210078040c208145210313031009a101d0074075250030304c010000320b118094400c40030300844001c800d5000302540c02c420242001c0141003c160003060501c2000351000303400941c0041d00c0c4019101c00d0b4044581e04c0038040301104a00b0401007009192100f54400314080f11060092101618159200100c0b42383e01461941c6003044c03a80c0d0000c180d442402d9009900d4290000c100244405804100101503040b140e107a01a5000ca030742c04842e070030140c900e80c000c00b4080300180842d256440400d05484e00900f40711282c0c039080c034009000c0c20403070304802c4907 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 698658651 1250 698657401 698657411
    0x30809030408060408180307060507060516052a030a02150906010f210f050f010b01030509073c060f0f05030c090a05040c03140f22080409060f030501 66
    0x118440100940342940e140001408035910b03261203021680c0c000805680c011901907136141c0b0035580400070b5000500342c0c3e0315099103880c403600b4040222000203050046858080b48050105070f40042140d02d40a10030b03039800810202c071400c202552f1490091000c5510000446249164000400c1e403200420400429280c0d954114103c1d1199000e20070300303605403440c6000344001424070140c20813000410b4946020490070b51102c4902030303032119042d034407600010f801109500081c0907042c145002802e0501950518038800d59a5050510034000791440d031011410901b941104150000c00c4440c240e4503050800d40c041404004091003200c0c04180b0000e081e110b40340c0258490f0301000d0141d03c0f42415996005500303400ea500c00441594803505003540820b56545511455490071403d5800144043c0c580780104c80d8424040e25504140c43c1c16800c02c10401c0090b40c0c01481d00b94200c4040c0c0c203040c014134050b003c0303003e02d410130003690b41413050100f2410034425184003264013850003400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 698659901 1250 698658651 698658661
    0x90f0603132306130b07050325090e13170d0219050306030601080a02060a1b0f0308240906060703050706060e10120b0117070f14090603062a0d180308 66
    0x44d005071000802010300303900c0800141001c1c010b1001e5507100d00a010408545100700c10945650849603140390046285440e0038008007500c0c11400307521003c1803601c00c0c0240b001d071308ca9100400041e02c40c0080c0c0180050100c9400040b80c046d161120304c2023200e199102c400c802d010308607801c219102e41c021300c60b1000004103c84d00090038480380307401034107451510040c240211031041101c050306000d0302032005c21f080003420444044040718000d6490601c40d08051a0094074681031003c0f400d14600c04d12188100b030b5441c0c5840c00d403c602d044a005a4420551406940c01d00400a01600341ca160401c0050453b80d1046400d224841000f03d90720700f036464802000702c603100444d018055400c940c0040c0030b901201c81b6000c01000e0f0040407516400d954040d60194411150004070404810521355501400e12400c01d40d00170004a02138900c1c0d16111a2145611034902410350000d80034a20420340050302c0001ca410341e809618040c0300e0700d007030b40354008851028001c04a00003007050b00096 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 698661151 1250 698659901 698659921
    0x50414150f04140403021b01090302031009050c090109020403050c0402030c07111518030706110303040602130f06020d020f010216240606081902090f0603132306 71
    0x9485645840c048a100404110521040300c1803201001d070025550301d40800f400400ca0b107401e10441c800e82c014800300464104d00024100c5132000e05e03050040031a8203100507513000c1408104001054000a96011749003005881c00301420315031600a07107a8000401c401e0b13104c3c1c004100340e9000343d0031aa0130100c8103042c40201d11044424115451051042100042c10100e149080e214000c1000c60952000c50252446a101c0a0308050340408001100d885003401d02c080401003c05050600d0840031030f00d802c42d240e05c0000d0005010a0340001d404074480c014260350303009008003c00c1300c0b485903240e0303170003035540e003114540100540309174107072405481014021145040c2801140c08080409643c031014601103404003102440010301211060b0b100b6441004020900e40c0e58000090030000380c03001107200d140510500d01d81c0100300002e5551246640c24038040415a40503689580f1903000c4840741c60119001040b080c10204400500b44000e000141050100e00c01d44801e5110010030b8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 698662401 1250 698661151 698661191
    0x50601021f33150804060504021302031504140702031905040305100c0201052401030b030c090703060501090801050114120a0209040516080106080d050a0c0c0609030b090d140901020a0803010f0504 86
    0x1800001c0304e1100103000260141c02a030f810910141c0030b0401115680055401e0744c0040307075503e0110014528104007403402d4003e10080024042c0b0010587c20f00220080d101d2241031720074280e4003402071011040c1440b420450700110b0700441075410801d992800175001d0041010701c40015802c00000c5060441003070b207440c805600030100d1540c41da4000d0011b60150449250341589409060f140a9050300d9100429104400f1907030005005420400007601201d03407608110440d0f817415005100b600c0e1003201c5001004022030340c08000d10b210ba400e080c645200c01e0f8000390007000800a100c01c0090004661148061400c030204106894003519400c1364420b1041026a500000514038075600980082c05552481c1c507180503200c21035144c1e0043d822403a8800f80001c0e0541c5402c00500c400c4a8030180c1240005010340f5009031811801080002540d5908684050014812485d0f81c02001a0f0a20660280c00c858403580d4819101205000314441c00c0d029508290126021445260785 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 698663651 1250 698662401 698662439
    0x30c0717030432070611030f0d14130b010302090c1c0f06120b150406080319030f020405030c0f0a18050a0c0e01090b030c090405150310050601021f33 66
    0x203200403445c002044840803034190708403009000c10040e040e40504040c00404030814854800b20703032103282407400740c41400c00030221076004042480060010303108500941c1101d4040f01ca0100e0742d05c8040340d200c0a40f01c1d03985400043e101e03030090005190b1700c5400c15444000d494801300202ca5a9502525400c0540000200342004800004500e20340600041d065004040e04c00a030031a1141c07407031440d5030b0001c2101c440d41170550080f5411980d250041d01d10740f6411800c254146403404002c256200322280c450361050002c2e00d5603002a4407492003610042c0004200c4604039600d842050340188410340f241b01131941822851403076a409030300c04d01d0100ca810394583e40854a090b140d09542c0d000505240240b4a007005200525641c82c002c8034080c1495000300006002c071703601018a00703100c8907160101c03d0b0030304040020030381c0c002c1040c001d01c41d280c40c90110181500000c0d140140030400c1c6e80c1003e40300c2c00c020011400d601601492280f40c0d640300c1a803640d61600d00c0b43d07503101c40f5410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 698664901 1250 698663651 698663653
    0xa1b020a06060b031009020c0102131806060516020603090f010f09030e0a030b060d030311070c050f220f020405150a0f0810090e1906050603010c0e06030c0717030432 73
    0x301b0416080341e6030003008045010000103090030070908039030f030440d02c0d070b07030300000220520503070100c5542010302c1160700608150804524041d0104030010f00780801101c0a0b00c10807000c40000c1c2c04000501c644441400340900821200c071001d14540d0040c40920b20030350000d1a00d075100c1415092441e034100c08e413600110190ba041c0d84042c1001084a45110110101511403400511060610010f4901c0c0d9109400d0482101e04140501210051802c1d2041c401d62105811088013108114030720b56020790600d01044104200d060345000c0d10555201c281c1041c0e102465410405004001d4002d000c0c80d135071102c6d07070880d401d0412240b2140c195032042500b041803604200003085170380251003007200c40c0183c80400c1003200040c80c1155400000b901c0d8603449038204102e602d800c0c4a00d0800c80f0050030111403858645003c5803507408020b1081000344400154001801b0381074054400640140d11042da40b480c2c01c0c60180928450301020421545441d510b202012102100201003036143c04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 698666151 1250 698664901 698664931
    0x51c0509060909090a0c0305070608071d01080705040e0f043c060912020609010b01020102040f0e09120309030705151501031d032704140f0a1b020a06060b03 69
    0x4000c0050703802c4040d101d0016480745e4219840040c0c12000d2800003540100c000e0f0603400c0c9010805041284010070942c200201c0145442d1075180c407051003030b9620b9080c6400744850342c820409480504c40c03900148202c29810080041c3d4103803141c0d14511561103590041d801600d0920b0000074028400d441d10000140c1030310031240c800302000d400180a0140802280c2004580c940b00da21450b0350b100740c40181c002a0070450442c8090040c102410300a20013103150901e051210802d2041c60b0080307851010801c408929091400c1001070303c1d00f0007958031943d4a003003c49501c0e0b540d901400d400c4a0900a040a880000560301c0e20244548400f1031034140742c80d42c4200442c0145140314003410704001e40e041403c1f001508101a0100c03081c403000c5401320b40c40104802103045100e45465200c2c034140301c24800150045005190000a980b1b107403c1c96450715042d4402819406400d908101c01401828841690003c3d4a00816004038400c01840780c5601900c0c005110854031200121040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 698667401 1250 698666151 698666167
    0x30207050a06091104050103030809070f2303010608060925060e04050421050d0f15180e06150913110609030f0d020a030807080106120b04090609051c050906 69
    0x1504004485407013101c0030382084082400040449100382c0083e80012100800c000e440c0c00100404c00c00303004081080c82501e403900048801002c42d0503985d40701490501c48209080d1800d401c090060010381c0e05490680c541402d026a84041da65403010402c640b031844504000078031000700c000c2c2c4005541c3c2181d40c0400340180300c06054041d0003260121a182800702d02260b0004059900006568131540d0720b680c2400240d05580403420720700341d440c0c60800001508151849890b088800096405c2c184600b01e4150030002c0c286200300c0311140c040c640400c030050000c149080c1c402003045a14480340e8072107449030410480104002130900381406010512440c000340074003818107008049407001c844004810b0700300070b0004032010169008c8410402050f41001050f40d03c901d0515150006615189008110b5141601d81000041d61404000d4841c1c40341d401c2580c046401070010b21501000c2c5c600703541e99198405210b501410255007a40c0c1c018800c030203c4031450341c000c2c5001e043c0030003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 698668651 1250 698667401 698667413
    0x50a090203060120010606270312180b09120604020310050907170c01020c011b030c030e030d0c020901090606050304060515030f0105010e0c0301150e061e1801030207050a 75
    0x20203456141403042c031502d460342d41d96424913a680596000e03000401c45c0c87c0f40120103024100750b0844181404403586080b200840d0300c00f2100b04583d001007a01100d28880c1178180d8608004800c0480d4007100c90b41c000c14031800c07031001800d4001b003d03035800412240c15000a5107441c0280e03030017507154010411000046c21290003482c0c0100c0c441d401d82d0401952034094411410082c02204c490760021200502c2968062040c910200c80c00e00b0700c0d0300101c240800c040c000103e0319800400b8840c86401c060103145c41440c2d80c096240c0d010f0104d40f15001c81a401601e820110f0310200d00c01c1d0004000414220300b180075141c102c540c41d80b0340030300390707101c07030b6101d2000e070100802c07c1c031140782e00f0031580340103603403c109205014145000004440d4101103c1c10702d002002462111a6081000100000301c1d03003440319206038401c3d240c08420f60028200041c1207114220201c404803600c60b0082650210f6070000f041c0c01000100004407809501c030040d000ea00540300c2c003402541283c0648800704003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 698669901 1250 698668651 698668657
    0x109080c04051504060e01030213050c120c090406080a06150b0702130f0203040b04060506010203040302060a1d0a15030e0109080a0c08280f0c020307060e0f090a020a020d0306050a0902 81
    0x162403441005005401000b01301107a005500c1549034030201c00040003941885020145482c60a55082c4558070b058840c1410030710900c10b142a18203000d400242c400101c0509803003451200400c00c1c0302056841483c0c0355280c03c080004d440f0180342401440303403448116104812260038071085403c0542076020440752004c4900c46641d400d0f11212094031185d5075200445c459440344c1080d580504040c00d024040f00d02c024841c0303055500c1000284096514a415220801440c4c03601440d04103a10001c1c8007454140144982c03c03803480d200100b0f03510304030841004924065a030402420311205119400d8a66070340002e0500712042000c0c040b10351240030a02c1030a4042c0680c186400c40310f044022051040c0f41400041b214003038141464164030018820045407613107000090311020f5000a034403000d45110342003d0100540007402e81d5150740040d0b180e0424002e10300040c62411040400c0a5403040d44034200601070740d40d0440079240680304803401e881000d002c0c3c0b1100703030415221000070341c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 698671151 1250 698669901 698669911
    0x4030326220507031509050f0a0c1202030309040c05091c0f0201052208011506020c01171506030c1e0715202101090216020904061407020c0a050109080c0405 69
    0x1003d248804004503200382283d40f20369208010010702d03406036042c55410090400000c070901d80180c1c484c580491341c00403441c0c0070f4854100c1d10401c400d0003480001d21b0b600c104141070790406e09041c0040c1a0a030004060700702c00e00c1c2543c24008220441041c03500e600740482000708050910130420002d54400e134080c14403e01c2000001070841145840000c0781c0413558000501607440d80661901e2500c08220a001850b560004203003400c0340d54006030142040c0403000489103100c2d03000940f0004084020412100c4c080c0a20b0360702d007030502da9480030303500001000720020b0340f40e03030142102e81c00c2e0400c032011300e03802c441c810701070200401150340070f01140703092000c820385681e1203881d40d000b80d440100761f9528190005042d14032030b14401942c0d80c270168460400140f051004840d104081c84400650650403141e201881da0340d0316041000301b484130f4800c0f080f0a05d100070000881d40004004c0b450b128203c0c4c58004055454004440100c9039028100842e00209400e40882c24640c014a07048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 698672401 1250 698671151 698671153
    0xd0f0503040806090c0a0603050c0315040b210d020604050a0b0405011103010902030907090b0a141302040b04170307030e1e0301020307090e011a220308040303262205 73
    0x16900d81c0001e1401e8025650304a04c0d80224844031410300d0145c11010080c17602d801d05010b00d140100d944141800b006100b685400c11400d540380d0325030759580c464081c900e0000e1122280410301c400300d506440c03100c032100049100364210140700900002d440c5c0d01c515131140041c8006c10300d6640300d402c0e01c80c3c003130000c03a1a9901d4a050f0f0701d1603090707803024502a10780b0200040e140d203172181074503240056075400a4140c615001c1c01c00460340f10348580d401561011401580c000100e04041950625405600351019101007808100c2041c200000c1003101d4104940c1440501c082c2d200369100d1259001c002c02040a0091062540c1080f00380c1c149102c0003a8140749801038080d022a0070ba90046600900140c282c00c0144281c1400d050224090118001003010628840d070200c271091243c4010205071200d4020041d25140b682d004071006103a0061456454954900e400b800710381079030741101c03503041e5015450101c0115030b9401c2403194001007001c500259184068240002c0000019a02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 698673651 1250 698672401 698672407
    0xc070e22050a02041b0818060c070314030c090307091a04110c1501090c1718071d04030e010c020a14043b0609061f1d06090c090d0f0503 60
    0x140c4d41d140b00c4e0921071100180e00071955406504003c0255200403d10501c808000c0910800f9480000d4a03da0054080724880e41e582c25070300b8252410409a034000407020400001c02c100001e090000d4600384c0c0040e8222111103488004131015180c250b2500c402051150809055030300d02038100041c3e00100e448051300c0d0100c030440306401d0598960400485141d014010055000700d446030a039114541d19103107103040b90448008003001405441d025081c0940c805980303001b00140200340003040d4421213419012504130040211507070480d4160f001c11107625070040e095006a41c00d501640c0d0003805114090708041075090828203c2d9400c2d9003003076980d102c164156644d50840b11000d8000c030707407004103113082884420f0785185240c04414070b80c0280d000c0c0031401c0e00000709a90450403c030131a00700403c240e58a03a10452a641c1704003c08811106042d84045210180e107000d01c0041c0c038190095610070203813449070700c181282c498100c010280728001040d0a0020144803038070038802d0300c0c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 698674901 1250 698673651 698673653
    0x601150e01031a0d031107061b021915080411120a020d11060c010605030d140a0e0319030314060a05011205040602070b010b1206041b080405010608120c070e22050a 72
    0x1c4e0b420152901140070800e442c6001480703800c200070718001403c0d10b1910b180d0016500340526805007035080002e0146281091f2440310310105039038040070f41078038003402c5114045294001d01c41003068506603496172400d41c5989850030708500c0100880c5004005140c00703140d59081c080d00c2c0300e06080139540c042c0070f00c01040c903c3c0e4480b00107110340840000041140c905103010141061030340078014041c400700024a40180e1038100599200800310b05202c00c5101000020030705050540c031441020001581d40c6008141d0543d00541c0c0f1503d201c040ca421560740e40003404003202d510700640e804a081141c107560028801d03008a0f0340140700392405818514199200c206019083c0c000020700840801c0074080c0d0703000380700300740d5000c8021501841080c0b460f1103040d0402c03207040c89c220700b0880140e002506211094020300010201081110741988510f0650b082036000180501e1082c028010700190f10f4201d060094003c0d03241c5450340031060380043c0c12101e003450409003100c0500904680c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 698676151 1250 698674901 698674909
    0x60105041e091509230c0304030201020903031303050c030d02281208040302060a150501050c0319030e07080a05070e071707020d030e0d080c0d090506010305030a020601150e01031a 79
    0x2a00ca082c441c1c1500d503c241c14415110240d80c0d01c4000415031552600c2402040068158125005050290041c1d03032601c450808034007a21034010142d8041c031000410048440301100d0346411240140280ca400801420415450380c00828040005900a02140c060810000303c100c91165030800b4007407441c54660b035200d1418142945820129000b02c0c01c0000785601488900d07400f1200120070042d11964640791341d0718022900a05040001c04945081410000c00403101120000d48060b08030a580181c02000741034102103c008c1c9000e50000000d41c08000515003609540c028040c01d101030400301144220341d001021001000482ca11214400c000a0710a074010b804c0c2d5409881c18000100016041d030742e03a401c81c80f6190b880504c0e822001584415001d4100c20345400d46a540c480001c0c1442c05003000d16030140803030103524000420000700000030000349403e03800380c55250f80e0321030007080100000c050032004079004184c2c40034503612a9105c019050102054110940480000f01e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 698677401 1250 698676151 698676161
    0x30e0a060203090f06070207030803060f04020d0b030d020d0206041218030516050609010519051905071103010b031203040215030f0601030b040c0f181a1b06060105041e09 75
    0x548a1070350000a01203180810722aa0091004e0b80e03008241908028200a544007080d02c03000d0041036000c4040384095403000825a44100010001d5482d000b0841c0d09a00614605940d2482445804800c000d103072f00128900340c2502c0c03160040c0c41e107a602d80c0c9822903581d241e10116020400704002c030345004070080044c030001d0b5004900402c0300d08030f040c8800c1003c0107a6003140d44500d9040c00800c0301e03681d0003011a500c1c2010b00c03186040c401a50340040da618003540004402c031404151143c0b034115444000360002d24020540d1030180c600c4275040c10b0032194010308460701a00081344e0081c038400704100440d00144040c0801805d0010402013405541065400c0d034044900710052246070369240c025044203290840341002035070400340c006001020224042020721124041c5002078000000c00c04000b0b001c80070400703103052103001003c0880c0d0f0000d1150680e803074410701600c0d00c4150001e003070391041c0010b0b19402e1030141469070010305144080605003400c20603800115180c1580d0040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 698678651 1250 698677401 698677403
    0x20c0f06011a21090307050f0712031116120c090213030b041e0c0620030a030e01061703030130020f03031315090e1504020c0a1b09050c1801050307030e0a 68
    0xd0b40e2181b4541c0b901c1402c010082d00c403c9003592107408c091003100303d20054543c0b250b82c141461a041d908964480d810600c0708181045a510000c20000d00c0b11010546100847d20496003c8001502d41035450100d025900141a4080e0b81000500006410340c950036003050090000b10354901c03403802e4a101c8040e082c1000c036940c01011904002440d00045444c02d1f610130841600c0400340400422a5a03004182d81079080503114484003507504c1c000e602802c054134990034103072a900780d40710f400c5540c0d0f842841000c22061000b2840c07002881094400d0883c1c2ca03810040504901c526000c100a071503510000640c5408100044400c601c1c00303012072001400072003254482145a01d6003c0c1041d90554000a4801c020700100081d400000d00c0750700c1400021200141ca404035402c1c038505e080040d85004117403030700303940c400c240c4150f1002c090402c64080301d800303100c127969048840ba020b00135a034901c8820b07000c1c1c0c007040f44158000c002455000c000d5250014034031045040441ca01165980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 698679901 1250 698678651 698678653
    0x114010309110f2821033212060a05180c07020f0916111603120c0b151c080306040b060d0f020304050105100312050a120609020c0f06011a2109 63
    0x2004000d802c01205a00110740380c0382455005480170b50b10050a4a01d0000076a01411034040b07200c100c0c3c503001011020540301c003128654a40c01c1c48044c246074900c0a550251146800b1400001e0520303081d880d007002641e1080c648032540d110b080d9808001d07080502c00700d078032800d4680c80301059100d981d4064413a507091114075440900e00c1e44050074003120006641255080204041c02c8404002e0385241141d0f8450450150072000e24011038080c0d0043c4001440c0c900c5101c03c0c0250001c0541c40208450000c65102c06012a580861400e4503000c0750001e110703200600000340c0318a01940592031202001c3c1009190814001d089070444405407840d104080d0b000c024041801024800d20340d01580c0034000d11803290440d00c5107180207844048a50401500040c0a01a04c2c07154500d515419541d242c1441456103a0340d81e94042d4000a400c0840c5114000040d000d040000807030034101e40200f0040303110300590040c6100b06a00c079141036040c3e01480c0642a510301c8003460300e6485415040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 698681151 1250 698679901 698679979
    0xc060402040b040204120201050f0903030301030b07091d0f0406060807081b0406050109030210030b0405040b04050d030b0604090e07030f0b010315050103020603061e0d05060114010309110f 83
    0x1204001c1264075503402180211303c1070005000d941490100303a18000d409003413454841c0321910100c40300d4401c00801c0380c1c141c0000300c000030800c2010a0b085005018948540210710b0311507601e00401c1c000508248009412400862181102c807840190002c1c013031140803034055140c1604500d001d145520480c5903501045039883d2800200b00d102001d0b00d0116000d014032460000020310106e150f00000e0302c224040019220024001d03844003107008405030040c482c914183c18040e8110b141168181e0301c0b409081886059641709210348201094002c01c160304050400751240010704682d443c41c4000d1064100c044003007840748440d5186140702d85c00d00c185640c11840e0010300c03000300f200781702c440c81d007820014001642d0740c0066076400603007690340c000b141c4000c41e641d2030b030404071210340303600300798840150b00512801180b644d0589450745818411400c00c80e0044040f20b889000242031000b001000c1e2066140038020061400300091580803000042c001030328034007600c19031442ea101c40c40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 698682401 1250 698681151 698681153
    0x1511090a03202706130e0a060b060304020904173c0301030f0201180504050702060a05060a1d09072301090b070819120e012702011e02070b0c0604 64
    0x1d011100311903015143c141441c8003030461620311a00d1542c1e11008989148006503807903c40b0720425800c0160008240190844582c2490716404142030588480342002c101840f141800c004881c002d960103041075010340d0f11900c9442c0030125421040c510340380300700704030005d00d55040d200400141540f00701c02c10206510144c1d1081241b0340200c00700b090b006200400202d51a400e000300825028204000800d400300e0f403c48100e00c0c503821207035000e46040d0a06c080d05a001034071a100f00c0011344104100e803201410000520290720400e45a406040d510f08440300018910715040080c110403a914151070b8806c08288580340201d070311082500c105a01071669111070900000d120b40c0366030a10309031107500c0700b9229100b00f50241203d40d140c1c0541068692040001241c04180d0b030000b000020300e12018103002c0d0000711052030078014070a070040a00b20645083c1240198140c48d0300201504000307801030610f100c1c580340d00950142100024220400714010101914000d01420003460a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 698683651 1250 698682401 698682443
    0x60807050a0e0103030203040b0a0e12031309020f04120204020415020307060f0614062b090510020406020d080405010e07060c03030c0c02130f1104030605071106041511090a03 77
    0x3540c2c0c88100e0080d141001040441e4010080f50150784500608a603600c801e004103407203400e60300445980042c6001f4401c1c128242c00b001809110480c4519040c00079500d80c80715040e4000c415005407460380c100020002c0710300c01c25048110903c080c20242c00c05039550024685081448035003c003503000003030104100140e6214145010b1083c5004102d100d05100000300d24010312541c00d8003900000840d0300b0010804080b6182403003000000402c50340400c50f00101824690000721a2031086108485000d070a500070340301543c41c0350380107040b4802d01b0340c012250701602810030f407140d5589003c4022541001c0c044040034000e103481c0c071445c0320314500d0300800700c3d003220100c5401c205540e000100103070f4800601c2c04c1440c0262101140140041d81e6100003800e40b2007441400010010b0f0003c2005035030307002140f24000d40e4503030701841403038602c0c229118181142d005010252034800e4100540d495400307028020000186c41d400d254810020840f40070300d54005569450b074032010700c51000a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 698684901 1250 698683651 698683669
    0x905060a05100e0a3b01030f0206211f06050301121113090b33061c0207050c04060b07080313060b040c0306080c0303040609150e030d0804020108061c0605061306080705 74
    0x1745908600009624580396403440800c141d070002d01c98540001d0b5480812a4844e00c0004043e200c4921541810242007141072001041c00c0783d8154000404000380c82c41c00786080e0384c12901c98600e10160842c460751002c290743c80800060b41d2045450112038000354561142403800c91041c016400c460a03c0c290341880c4070710081000f501d14021160044544403000310241d801e010599186445100407011702d08115060300a10a101b071011480c0c02c05e0020005048180780001c0d1010800141c8802c0a25998400c0c460f000d010702a0030000f08041c5005080034804550082c000041c5100e00d8078001800d840000f0001d100003902c500342401580000c1c42030340100002140110310345490a8400703070139440c5a10842d0942468021120481c0d80502c00d41c4248040040965070f4031522032201821944044d90141c0c005072181c0d0008070700e420449a055200c070071014085040418075900e04e00a04001003066070440d4244494180900207030142801400343c1501034050780d401c0c04148450a4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 698686151 1250 698684901 698684999
    0x4060e0109090b030a150204050d0b01051e150c0109020a090207140c0f01032c0604030f020313030f030c0b0c0913050618131b0905060a05100e0a 64
    0x340303020081072191303900203035070032091707621084850f4190100111300c03009000d141d220507041800d140c8041c003003085043d007441c1611009c403480682d03a9580300c0c0c000d4415190040290300f2402003c5000e215003e03240240c141100340c100007148811469000c90340a440a51007166a40c0c0c0205c4c40c00104201250f83d10808106840241703c4219800002070700781030303142a81814956900303000d5648500400b4089102410010040003900c501c20304642d660504903030a900013216030b0700e144102c40c40881294204105110413421090464990420044102c10200c044c0103070140480c00050800c1300c1140f15036100d02c025512401900240880762100d080c60000c0940342c8410866a555131a156028024507440e81414556a02c3d020503500d403500b0704041c0c660740c00b41d031f52280c0c0d143c10b11541e8420b84014440c10712494072114148080d4800502540c0e034441c080b4842d03003102500c68841c00c216003a000300300c00102c03650342d001c440710031281c100c035040102010544803007103441c3c40c0e40700e2140d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 698687401 1250 698686151 698686169
    0x81e0a030c170c130f0b030f010801090f020105180a0f180212221502031e1303050f040506071a0f01080a030311091003060501020706170a0902120304060e0109 70
    0xb01c102030b030140301d50300e4000344409040c180120b07144a008103042c000c5405040c1002c0f00140f030646564259010750803c07501c42000c88803c200126000b203060145401c0c2540c014a102d0200f000c03070340152056000180d0a01c103000b080207820900342e582c1405a001400c0c1c030800c400d145404c14180700f004075410104c40b080304c0d00400c9459025900f82e603505030300c01e9104c3c000000c00da8034000c030b4080150070050080c1580c64840b941a02c10201640218080d02c0e01030071540c0c800c007070703600920400c9074100c50320400c203028242100007003030207003004280c2c0c6074030540a94038060f01c800000d503454100d55410b80344076400c100d09080080c4861411500803c1c101110f441c95894121481d6039101101d800408154444c112071060445034825200e40c0c050040030520188030945000780100301510030540103205111001502c0c5014054070300b044030884d4400c1c0c0c2c00c0c0d5184402c017805071001d0b00c401c076000641d580007600d9140c0184047c1018040c075548a54a6441110004205c441290001e1000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 698688651 1250 698687401 698687417
    0x30b0402070b0f0928080a170408091f020a02090714130f05040207080d09020a0302130516080601091e03080a080a150b04210203030d06090f09031407081e0a030c 71
    0x3400d40c0040440f17078902e500c80c0503690f440209000444000003220442c2da48082c0b0304041c0020081142c1c0a840f00d040c05441042c02c0340011381c04c07400c55904108050001d600042c000c04054100460042d62042050504000c540308224141c100c0d6030003280a290804d041e61400d00070741c00d00440d0b1100400040310154109815034807030000038401c810003c1e01295035020008215221003998200558005000041000d9a68100e4000e007030103c50486611111005509540c1e00403c0c1d00c1e401104181d403010921401c10b00300817240028038400c01a40c1e0310f25580080043d8012009150382a11540c40502d681072900d010020340303401d001d501290460131041800a02c00110642d0200c0b4525060200e0303506204540301701c1800031010207905400001404403102205811030300445104480c20050007491548080440e010300c2c40040c00606008460307044c01e00741c0e03405054494061030f905403403e00790172204003500441e20711803070980c0d1000c01c1a10440b41c051066030014500e0b4104040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 698689901 1250 698688651 698688703
    0x605060c0d020601140f091b0a030e010b01080720031603020c09071106071209050706020c0a0b030105100f1b0c061403040512030c090a180b0307060e01030b0402070b0f09 75
    0x80c4200500c038501c1d00462000300024041d42c0c10300001c08e0f89006902445e51317200d40605000b000750224082c640699030810075404020751240703c0607489410b2954641d00c0b10350700519602c090401c961000000c91009000181c404d000403001380c02207d100fa001001e071318640a0908c006c20078002c094806000d00c03c600c6c01d03410000840d40b00d5100f85580340004a2184600c880070092001441c00b60280c0f1844102282080c1c0008048498a0040f02c000306d1850741ca1040b40c680d484240a01e58008140d103004801a034010030050320741403460304046c00c054010340080d5034116a1b0b000103842c0664401c204101c1e8580140d9031040d0301c0d0140c041d0a00e0341c41d064132590f03a10b43c00040000640e102c0080082e11103245641510101a402000100725540e500d0040b48080c40e8045080c001c146484045162480c001405204440c1c031903d410000309102401580100321070301000703030020b80800688001031b074100c581d91b20406900c86540940e04202640310b151000100e19000c5085200c5200300d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 698691151 1250 698689901 698689909
    0x1050f091528111b06100503031801021e030d0b01080f04110621010806060a030f060b0d060f0c030515180604020c0106060f030c1407030c05010605060c0d02060114 72
    0x15105640c2140d6240e24640c006420344010400d0b060f4518403031102007000307400c8114094074010380d0f907011401c03a0b03815221050345180c40c408a2240aa00d03034001c21403042c40b1854445103200c24407050050724109520b4601c074088203c80700c0c40070a0190400035000c00150365510440036912400c0c40c0115052900320b201c0c0b40c01c4600030f0401341850380c1a101c42049541c91034104c443e100700108074030083c15041c000b024101d0a0030b00904180c0c0c000c03a00041c00600b82012280c00b104d070080b80c0030020001d00d850b044003c010a645a54014220904040205d407980c0102043c5000f21030000501401f001001022103c015080c030010020644405c2415620310040c80310343ea65860402c03807142c0312070001030000c0c450b01912004035400c0060000754650081602c000c4c10a0a44003807054051042d070444281c400442c200c4010314090100034003082c410403201d10168841e0000054164444000682a803c040358002895001005514a06a040c081d05006200d00c081440c03200500900017 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 698692401 1250 698691151 698691181
    0x6070c12030c0834181205151305031209060612060a020f13030c031205070309210209010e01091a0307061107090603050604020a2102060d0207020301050f0915 70
    0x8580c00410b40035a0601da10000c041d0700400010090740c1000d1040c418080c01304800b5170021030350103401c3c0c000003805000070500e91040e40d600c80040d00c3c0700c1d01e100d080c1c02c5150b90081c0907110444030a1b0703e00400140100024149445041007010b040d2500d0040c0514207040100940e000d001c0c0030000c0540704000064a036040350800c1400358640344209000c80d200d010382c0d07541001e0034501d400f00000740507590b400e00090340d01509080b00d0041c194582618a849200c1004001440708541004140c038922a500500c0e0865524184141000c0d0009a0407440a030001d031200311030140104404420341c85801c2d0740c803403690203060503001d2150000b51038108511610040c88400469000c0310308040c4810070103004100303000c101e5140c0341d0600b03d0380c4013002c8600728040c1c0031080005c19041800d2004c20301000003c80884141e00840d42801050380000c02c4195031039809103e5600160380c03e0245d5072081c0c69055404106140181250b86000b1114218640d010026401d010030500d03074400d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 698693651 1250 698692401 698692411
    0x1020a0308090a0b010e060a060203070308040221030304210e03071e081005010812030103020d14011506021b0a0608150a05040207030c12030e0703022106070c12030c08 74
    0xa0199a440d0340840707040814203800180013186200000c180d000d24814001e000d10000d40717441220a484940603a0b132841042070142c0480d02c4100000e0041c13034001d001b40c1607149582288200746418011051940c1c2082d82c00300d800c1d02518403400000c8800c1d0201c00c116041600e060000003480710302094451105020b190311424030328000744245080751348140024414002225080703102c8180c102e000f44001e000c1d0090701d0040c4000b403841310380c2d0403095034140c9070014071814000c212565400390503481e2214034040d135502c800001d0002590700400304000c005603000746c05440814945184032040e801f800038416542031509016580d482151554401401c09540c503034403042c000043c1c0810303166405641e02600000c1c2c1e910030164804040088540b007a0741a03800b90b03402403001d41c183c490f030100c00f1b800baa2081c441003015150070310742e0311f024020007401d5000c101c008440645c1060000c03240350020900d000c0d052420000902d481c41c900400510f802c201081c18508000c12000d40a00f03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 698694901 1250 698693651 698693657
    0x111120d0203060d1a04030905040207020a09091104021b0f0a1211072301030f0b0303030604090201110105091c03062105010209090a0f0c02070506030403180b0d15050f01020a03 78
    0x1001907071135150fa04401d2134981d0003002d2441c0102d107103200031009100c111811000540d0341d10300010f8505080c000e072940d69138020400e0403041d0501c0282d500170600c11100b03a6440340305c007130001055119407009020038a50241e550604817143c1508919001c0301400e41f082641c0b1140310100402c110301a5400310071858980000003a040e403004601c2e00840d90070480040c1c80070441d4103184000391a44210449003a00c05100c410034900208040f46c05080e4401d070143c000f0400143c2170b1801d588225151071050516030a0607601d01c0649084031411159983c01d82d00188500d103000706140343d044000989860244615401c10400060a0080c070322518020742102c0d174400e08100c0c0c2901500d92806001c2e082e0030061400740d500202400c1900403040d81107181208001b241880031070100240ca60141c015485e540722550104c4001590440e03020100c01c1c4140046090000c07800104041c02e07068030007040d000b4143e502900d005049074062407107901c0b0951440310998021581c0034500350141 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 698696151 1250 698694901 698694907
    0x6090c120322090b0d020306040213060308130302010305101a090d050f060411030712080d061a0d061d060d031b21050a050f0a0e0d05010b0111120d02 66
    0x150300540746004418140541c6080b03902c2a1049400595200048580c0300c3d20601c04c60390140c0c14040103c0744110040d402d608000000307405130524000e22583c800c5480c000041082c1d50307449500494010328840c40400070a202c04109541e410b016880e0001c03185241c5480f41494159220b03007201410380394026800307003c1000300e115a5001e142d443d541d508507003a200c0881040c501e03035444140440b001c0b0780c481451924040c9509002802d401660f03016010a00480038035100c1d0013030360f041140e10015041d00d4070000304540b1400c03400c2854290300700e00f4050b150382d400c07801d541c2560310f6500485496045918250004401b500c8101d0300410280c42202000013182002c40d552144000d0207650410000003142c02c202c25074503000c060380039030a02a0407403104040c0407240d0340b1984500d40d0003d0002e00800700ca010004006025001d5241848100c040060b0302140c000c1440000540301030b55142840c1c9825600030039500e0ba0012908060542c007411013112410038010700c81100b104c59804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 698697401 1250 698696151 698696179
    0x40b0c040e0112030c020d061509050c0d020904060f061d090c07030513051f080f100329070801080c0307062a0b100f0f0303090501122a0f0206090c 65
    0xc0e017140d440498014041d6644032015080c418050036280c00e040e42c203000074920000e0107800c1c41c485c1901602441e2046442c058565100310080e400900e0a143e0141c0d40c1d00c000a00032a500084000420083d03c8401500d40315407894000d0348001601503000e440a00104a1010003032011900100da1600341244c80f200b601d550a0031006868120607000884c09000703010040020b084103100c40b0311917540c0d100075035894080311611201a80c3c400e02c4101e80c1c100a10028561503015102c40c484080710704156894500b85486a40c411307aa40c2c00801c003800014016142c05000c403954409050b001030400502d0072500501104010b12007409000420103445041a0200c12500403036412503103080743e0f81450040c1001442c2140701382561244101d8000803c481c5c40142c140442e60145c03681400c0928050054414a4214030b03107680d101d5807090404055000060800c3e0010321103221584241201440584600e04415014055500007070402c0403d40c00001d881203081000c1c3c0b01c41038003100b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 698698651 1250 698697401 698697407
    0x60c24241c050a14100b0f0d14100605040b090402012f010e0610050a182022060e0d020d170c0109110a1d07140c06040b0c040e011203 59
    0x210344008209004070044002403120002c0300c080407410a1041d101003211703141a00b0200d50300000c60a030010b80010134020b26242004100c0400c03406000c04092407000d600c0e2a9040c41d12a988901c2282d80d1010b00f80540d003064861404080f80c2590032007030b5030030f043c0c001030200d00c0c025520131262400545070b252120703e44100d000030700159800030311442401e6142951504030841ea0070400c0c4458010019052400c4c0760303264205d0700001041d0407020300e000b030180041d11a6000100300b0070400701407515010940d1004080c035420030210303080d0003604005440d0a41d0850ba100708200955203511a4071992096242c02800b9411074107054122800c1c9080c01c800b11000c440300e0000c21020500050a83c019004025858800e40c03c5420303005040b010401c0043c424028800640c11460034190348034046021141c101c0a9410200b01001040e00004501d9110503000102c0f9000441800100b10382c0724101d5802410718005607003400e0602205003280d5805100b50a80e1040107215038080c180 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 698699901 1250 698698651 698698699
    0x4030e04020f070611040b0a1103120f06091026011103010e0a2007022e090e0a09110607080418020711010f080105010e060c2424 57
    0x101400c19511559100740d41c00c82a0010082a1119402d0028010360104c045045030150360025031300a0a00c0c041800840b103d40e40c06c181261148010071252801e240d081ca480da1185031400327440314003841c2040501044140c0030301140c0844080303110620640340000144c0c528a0001d0415885991040c11084e000d0002c026291072404400400480c500c4408244544601d05003042071260b2003190741e44940d82d643c00d107000c01614109110a00052a001542264030f41310f0402e011080c001c00c240741d9004a001101401c0403404500081000b08075031203616501403902300b03042004904c191250404c500071350107420710911001541008028941c0c0649014168410890085ca010b14600070002d6105840544145100c2c1c101d002d1150300c0b90000025501d102c0c0c0d0303844803907480c2c08015281c0c035805d001c6140d8401c000740500d6512031010000f41c101104840240b0014a058050890600002800000c0c0000b125200e84d01c00c050040e94860005100307a4403141e05000800c1800c000e03138 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 698701151 1250 698699901 698699927
    0xf03060f0b100e0a0312030b0102120906160f05010e030a02010e060f0f070516050709140601120203060301060509360a0305130b0715060f03020901030215090a1d012c0403 75
    0x100b41b01807000302c1c0980c15440080c1d10b07082a0211042c03c80e41e102841500e003c2c00c0119680002c0411100c0783c2c80c1c0002010100301c2c1c0c8200302d41048140b1550b1400d0960302d07081c9580e00c250384040395807014503030309004803192036042d03401a01150400000c881d1b54040001c20280e00c0108280106900702d21440c12944045100c0c5480d00801801e441c11940310300b03441c403414590605020501c500205c03002c1e0b1090140030140c455480e41a05400544069000104895855541c4101c00512074550000141c45001440b0480c1101e1404030400e04400d5072a50440010100e0039401440183d0001240040e864041c28101d481e168004401800fa4403181c000103d0141e010075070001308180c0c8a07100d840007501c01814405140c5031440c61140002134803000e540305507204010800f609101c00c014244184040040740b9040074400400c03100202c80e0f00060701400d040c6948a00e5852056556014210a9060200a103803101203507a480e0b180344031410380145464085000c250040012044e0b036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 698702401 1250 698701151 698701163
    0x2030f070c0e0408090907030b01020c1e04090303091a090303220c030807060b0303030c091903020a12061b08060f0307230f0d0c030f030e030105010f03060f0b100e0a03 74
    0x1501c3d040c5080c25080d003000c84045d0054031880c0106032028064000c0c281d0009040c0e000304100701d540f00070045082024400400144804440b100c01901d55000c2c2340800c03402a180810384c8040c072301d00048003014072000744034004890b030140840b911010040b02d0f002104424031040c0c940c1d1240b00b22240c03800c03003000100140c41c00c640003c2001442c0000e4050140030700c4080145940d00130905840f03101c01c640f50060090104014566450590458845511b40c928040320040d2650701040381100e03660400d139207650400218208004250185001c10404140ca038000c0100c0948047c02e9101c0c00f6280380d100341683c1043c54042c3d10100320505c000d080c8495030150030a60702c18079512005540c820706001c0d000a012200352420a4904400c03515400520f648900b860b40d101c4580d200343c00c8004500304001c000c4e4000e1143e41c01d0145034080c0541d9610300c1200c0349945000c00c100c8580c0f006101d6414184a05001c040d518061a902910840e01b0400b6900081400007980c0703032441d0b04000c0003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 698703651 1250 698702401 698702429
    0x312040f020306060d0c150306080a240c0507230111040501110307020603040b0c0708070503090a1d06361006091802090d02120105061309020102030f070c 68
    0x28444010040040315000350159a82520352209102c0c034200e0310301d406848998030810402c083c42417070000107281c40b0309140010350203407101c180c1030070802085000c2e1008444103100903800301940c034243e2502c000c000c1d403c1043c01444800500f40e800303540e0000e040401c040213102c08801d041000300d000070901d00d0003080303101e42d580b80f03804454001380182400115240464034640c40c00004a910f540c1e0011f22990455035660369001928000418904140c0c8080c80b81e10000395025004e8a0310510890103540c42d20500020700690042d9a44203901071413400e032031034032040c030502000c50f008107040d0f5268055420040d00022090103090f6801619444000740e5240d03404455000c81c05502046440041103950b82412030f00c0f64054012802d42119032a021600c0b02c213035a006010405020708880098000d0741c000070041803a81c1c10800c100d9441e481008600e2802038440c0d0240d02030500100014403050300001e55900885000c00c008000c00144081844101c2c8035000091a000400c03a04e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 698704901 1250 698703651 698703653
    0x31203060e0601020c011b1a0702030c0c0901150305100b130905010501030e1e240f010618050f0402070203120d0e0c150d0e01051021120c05031204 65
    0x20041000e0300c140880d61802001141c819880852a40f0103180140d40310094042e140901c010350120f4200211000260351002e0b00344003100c8a0910302c110f0064024603212020780a0060801d20b00580040c45950041c00501c1281780c05210415044450b01d07001503140c0c0c5034502203010b10308903041f1188480000c01c074086144204004c030010f90b07410358414440740e60794000640545094403048140e64003d1480c508066046503082c1007000000d0049500c190000e891420084080c4011002c42c01a62810029403019400203035004180924000f220000541d80c0b540722a001401851f100324070349181d5a60541d5a80c041e1044075400400b0348266000010401020f9408020f90400d49414800d0740004808041182004640b018000500e0820402a5080164005156200c4060b91904140e504610910800b031080d05490f440355074183c02c0105e6200b5494000f4036400340204807400034030010b00c020110080034146030a083ca00c4104070303c0c01a0030350080c040304641c480b91001c1040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 698706151 1250 698704901 698704907
    0x40209240405090709140606040e090c10030c0807022a040f0218010912020d110118140a090501080c010804030c0f03170a0b0315060105040816031202030a140a090312 73
    0x1300315000c2e0041001203c4d600031900030413190444880b82c3c0a28148000c11001040000b120380c041c048905032084240b140000035181e0141c0003840000950f43c00e45801103039000500a900040c10b030000b4580c91202ea204900c40c41541c001d2004800c0002103544440d44441d0880c0008140010096488c1c4480310350005505100000b0301e40001c002100028040c819a210301e06280c0d0094040100385906459214008640303408180c10000e541c904441c0c44a080c2507141e01030452000c6002c0f103d1103940070400c1412040c0c1050101c41e1910004001c40d590009001491103000e01301001035644909060f43d01c0503400b80042e203015000a02082010780c468100d52130030140603c4000359132110102d54003101c09064540b40c05600ca584410303807903044403141c50303441581450850320b0251220349550400505003021a50b90986540030b00800c6070386905d07856100c00c03910066017424052140240602c0c14902540d801030400506d03058100c1c440e80c215809541c03c1030f81880004410b440003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 698707401 1250 698706151 698706163
    0x1620070b0a1e090e06010507021305093307050906040308090108160219020f040603031214270a080309160801110a12090b0112050601050904020924040509 68
    0xc9800100110644075002400e014100c00c03103a10390740c3d0103040b07504005405150301c1002d0320142c1030010500c840c400581da01d03400c401c0407218070000803401e424414200b52070038009105160000300c1020546220000704040701a002035411500e00070380d03e48030020b8449104420045c1d03003000001402006104103080242403e88003a6a0044607503144011506001e0600a0364001038126006c0c401d8400c40d120f03000c00109000401c0a0180041200003a040b68190b6004501160000d103441040c140184194910310203180e14a03045480d01100c4e0b1440c1212180f610701c1c4824405002c8034000c44100725071860300307134050003159603405c200301420b83e22510f51508030180c5421000100d89000c06002d48459644203101c0e07942004d1042c030b403d55071002560a113103501a905e0303014174040b90075036690600810410040040c0001c4e80d08010b0f081c20016040980038181c0c041c00d020060300d4551407640d2100448440340d10340701058100c80404041c00c0412540b190400052260316035000c180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 698708651 1250 698707401 698707417
    0xf080c07031a0c030411010e04150303180305032b090c0302130e071413061e1d01090b0d0c0e181606050a0c0b0a02031503061620070b 59
    0x803074056028600702d482840714100e91056101401340081000101c03001c154161059050402550402000f800709044649980a409695424000400c1172541025031402c4200c46501c00c401c0060964035038641c0c0e032107042400802c00500840d0a248115281c00e480c518029107042031000c01118105001d54420b1800300b42c0c41010180026101c0c01000d10035400d20207043c0e40607115080c0f0f051561490344141e140c80700d800c122080c082480340c00e4144a42c44c0a0314004a000c104078074030f040b112035440e039250040d05c004800000020074021440303d149044503500007005c5640b00d4000c0109000b00c0910710001c0a6207002ea40c041486d055101801d48200e02044541020b501d15030340303155a4505900c01c60850640e040f1003445254450303401042030b6801c80c1418440d0200c195100d8400b44001c07900d4a401960100a020103140b040d00c22414034101240141014207202000d8406c0302082c00c06401401a01c8800f51900701c1d400c404100c52980b0700c400c0e80c1d4174540c3d86000c00381c16070010030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 698709901 1250 698708651 698708663
    0xb01021b3a031115060415030602041d1803030a02071e1a070f090e0703110c0319050403030215100906180f140f0c091c050f03030c160f080c0703 64
    0x1070b01c103110810020312480041d40c004c0c001c0301a030319500b040c440244002c0035440070703104044002001003821400140300038490400340f1184600d00e002d819441c09806080c0b403098140d401000f0080942c000150394100010500040c3c1d03814032407618400701240300c9480309100c0c1c607000c2100306011115101a043d05850303801215640d448210460780c141e200740081c00030801c00c600c00d02c10044014a540c0d409612418001041c460107000e0341e11a40040c07100410940c23002858480740140354100310180403a42c1055801c0506555005c1e440c0c0806040e600c0c074514071200058070031900d00b1082c030014000850308018a541302c0002c2e1615405060904000605080038031059640d0f504c1000d0005403656600c954988512102c2c094503480a484108044000d104030f69480c0d07544110440300c10415000c4403d0b440a81c40c1042c244450024014456002401000f000003194800c40f900701d0101100031141c02000d140c1200012030b401310280003140003181036220b501c0001621010749028a03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 698711151 1250 698709901 698709917
    0xc08090406090c11071a0a0309110406121131140a0903030612020a0b0a02010e120a23030a020702030f0d0e151c051302100f030b01021b3a03 62
    0x201d010200b140c190b41c100300b0100810003010440e1f40c4654000011503109a089000c412038090001e003d654198010a48503a40c0c0b082000401a40307a290b10740784070090701c07002501d070803080002840301e440756500b0b41524400c010102e0414403603032101b0210702c1030031942401070411000c01002416410003c50119143c000302055080c1d1030b107070040c5c0d9030b41d008020104150401d0310b16112600401104c02c1550b40b9010084404001448000404040f46d000c050710b680e1070720801840700d4924400c1301e441c4240695828042040c0b002143c2d4000b0070000c000d6a90f080c40c0c40440d1420710a50715598241c01030096800300f0a40c801c00505c0007050855200a071a55951a164540d2107608083c01071171800003e1500000c07a10f400a40d8002c41ca400698294182900402d1084440540c00400950402ca40305001901481605a40b000a1004200c003450104440c1d07021000307117032611b02c41d106c2c41c1038140780310317066001148a81e00c010400c84240204407014102001e6030000450101e00c01c6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 698712401 1250 698711151 698711159
    0x18091e0609010c1b03050906040b04080604150207020904170408011d0c010f020c040b0609030a1b060c0b0c0705070503030f0d0515060d0902011e08040c050904030c08090406090c1107 80
    0x80401c2010074404c0455092a0010341e907040c2c2d50f65010180c203c0c0c20172400e000000d60190814083c000401c213050240c40780d40382614103041e10804400c031101901f84180b00d41005610b070003020a6020b0b07489140c1000552621000c100e131030049511161f055804c2c90001215420386030b49107050020350800f200d1000c0492001941c55180303c825400042c4d101c84880d0946240035008044140c43c080d01c814a0903000101007402d00481500c10341d0810704402c00184090382600501005058600d0700d10340c00013032599210004c01002c0c003c4608180701059410070b0100034001d20000313000040850756901a50850f50101303811054035610380524040000d1940490961801c1c042a001000075141845462503500240f45a02c016070411102141c0d504010342d0701a10805848000e8940749001e240070300d06400074503441d41150340038036906020702c00025005101c0c07000080e0701c240100c4d1910701817070209000f8501507005985480c1480c1480030f1964100c1280c141c0c0c0d01440b001c0d00c042d1912 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 698713651 1250 698712401 698712407
    0xf0408070f050a060f120f020d0b1f0507030c02040216050a1a13061a060301091e0221070311030106050d0c0206061e010c06052d0618091e0609010c 65
    0x3041c862130000c10ba0381101c40c3c0007140b1982d20a106036000d0300000441000c80d508102c120380215038000d124607600c010b90310003454101c030032402c04030420482c2c0d20003645501300245240146070004003032080703418010086651350740581e49010f10420840c2c2d1001e01c00d0400d640e8940b940071080d42d042494082c22261724904c112000d00c201403000507480b01550301d603580e070000c00c6e180034080c1e240180c0010a40c02955940c006500a00e4505000b10b030600c02c90f8490400300909412403001980304200c500180d003c900340124400000c12103542850342c80100a4010340031404088505020001c0041281070b0410003406040c030750f01104000c110681d11080c2d03520b0a042d031700d103607000d04800c00c0c55100600c00002040321550602d03204d010702119075684015944213946000e01d0702c68941da24841401041c04075900b800704071560248a0510780042800008224590b08000440d0360004010007020852201101d480c0d0180180500807101040c2d2900c60507655008294201000580341d148 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 698714901 1250 698713651 698713669
    0x4063903080c09010f0f0c051b0109060206010f09022104060911100c0204020309030903100608010b0303160605061f03050117120322050706080901140405060604110f0408070f05 78
    0x803068603607090400102d1703415a100040d900600c81044191041400082c0050240c004400a00035154601c141c01100140c510728032900010115803040c001001808500b082c1c40040f42e0400d2401682c030104140992502100100040d490340302d040184001c1050707551104800900400024070a640120104102d013104001c0e048001224200c1e81005072919500542c0c00c1100d80341100e2511610001007410305024030928078500f942c6080410503454280640703088100118013a503c2c2494804200c48000d00c0148043c000340e640c3c00000c0c805407a035107091204842c1e10000000082800c10009000c1c0c50240100c20a074030842c2038542da2950005000005041d0031b0740104c2c2165101b45040e4002401007006101c9c03240b04414107008220144141c01c05003116a4800711036184c0b4a1409084d41c50410709507901c550440200030115001149031034015604680103d00260405041400350045003481c02c41c2035800580010034031400200305007186d48440d1200039140d0381c0c108010003c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 698716151 1250 698714901 698714917
    0x150118050910110d060f1511060a0e0c090c03040c0501080112110d020a0b040608100b1c1e0609050105030307050d14040b0a03140a06080304063903080c 67
    0x7034055040d4a9030072042d03402c1030f0700400d040c0c000e003424141e04204180c10f50340698094070490042c00b9043c08507000b1030307040401c1d00d0081d08005035240301c2c60300803035603e800040c01d05d1441d6940340d6950202440603c031407074402c0001420b080850400100c3d031320b43c0b58019602111031001c07004002500794080c0304218100e454483d5120904c5c2100c0d15210558614080c0d919800110061301e100160344608a1001402c030000c40c0c02c0e150b904240010307007c6070001c0c6c4201c449402c2e0390010041b082e64041110725120401088950954110b1880400340507940541421090300443e88812251551300c813100312201c0e02001e001e41d9036101b0516450b03204051001c1c000c0d03082126081121805628407124400103850414500790741c0d080150031540089007150f002030388030100000281c0e01203030225000821114108491891300c510642d40c0c0c402e91140c00280070082d621600e44410140451800940c1802c074030450b04030460b4454040350140b44102c020901450200f882e84c05984241c46d094 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 698717401 1250 698716151 698716153
    0x201050408091513030f02030601080c13020a020f0105161205040c03020f0d0501051003060b09091b0102030403020a03050c10050f070803060f211c020c0906121501180509 75
    0x84840c0742e00b031000c28110349120501008040182e5108660200c80c802d00031405031400d0340380440b06104242c280310040e4042c9100c0d40c41180304130203503501c90444204a5114050040e0b841469040507070414043c040c1c40506546403208111030098a1a540e80060901c4e41e034040c0b811607505611f8003111003d482c040c20300100c4000905c01030910b02c0002403842002080c58003482816501c4909507001101c9051001002800800c10040c035030042002d03013182107404000c076107002003129a88000c1000c0d0f4500d0540d0680c480c0d101c5900910440c0c001e560084d0010480c9504c2c1e00700b65a90300380a540715030045114001171151203200340281e1f404222500d17040c3c0c0c40c00d115616035103a01c2d080900000d6100d40140f008807541c1d601c845050039481d480c0007042091002c2c040c115401c048080125560100c116035640902d00d81c00303c2c1030b9165420840300d03071505858240c0032504514101c0c2d40c0003914840d03004086887c000301001c0342c2c12103204000c030f02040c08440001c00d040d500d090f6440ca00b2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 698718651 1250 698717401 698717407
    0x9060e011802040b04030c0503060121020f0f0a0603021b2b030b091e0601021c030504051e03030f091f09060b03031303050c09010e0f070903151b0201050408 69
    0x740701107000c440070002944070150803c0d071240400c0c000c41e8400d91088641d10152501000381c1c0c1410322540e80140204500040c072821080a071851030041c0842c000d11901200004044c290713103290801c042190003410350f4036080c4e01c400c0007a0003580705884840c400941c50b25024604500060034664882004449011426240c500c0265414900e210710041c1904d4440c00340040c1c03142240c07144150703400184181100e0701c88203400030300080a0001c9045400c80c00c048981c01c802d1016a18055145180010311941c560a1403800c1080040903402c00300b0b0b0711502681285000009503000749a1034407a400e664031031840031580c0b440704402241034451960019a0701040a92203813041c2806600041484190080041d00307581c01b1082050403408009020b20501c20104034001701c5460981d07a070103455050000e007071040e0364001d002400340120b0800084080c0d1058240d64011a40090340008203a45a07254002a020320441c200b0498464002d00718081c4c4140102800b0b5a080240c1c0d40c9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 698719901 1250 698718651 698718659
    0x150e06061c0807060608100c030e06010e0112031205040c0509161d030f1002030106030b1503040204020a200d08160f080612160e06120705013e0709060e01 68
    0xc0b9500724081c01c2d200242e5a0100141c0c154040c4800d1000f040080800030301180325a601500302c07183d566810015502100051207002d21000160741034403070f48942c490708185285000c40c1c590745000d000c3c4040c2ca0401013440100b0a03440180010b560044030a0392069880301c500f0b07650500d06c403410707000003880301d40031031214500e00e00d80c090000e0340541030707802210301c9190051615001240b00d045803540000104006035241c81002c201002c1103075038203a5141904100100c40c000500b01a00c166400502000414091b41c3c940081c0610301c440c0c0c410180410310001c1e180e00c0da040300c000200c0c400900040084244900140c0c1124242c0c503542d03822420000d003111401c40051400303030032518903074520101c24810450004589000480008a40d0a25035218074064010f40842d0246290800401015802107456800e40302c0c28640f40152052a0407608000141843c661b01e0043c104072030802d8511740c002c008506803030144120380f001d130b83d41c034038543c200e40307003403140000c5200c032840140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 698721151 1250 698719901 698719913
    0x50906120a1e050d0c050f030708040317070209090105091e03030708100807031b06030c050a0c030e0d0308041101080702120c16080f0d0e060306060306030703150e06061c 75
    0x10064421a0404581042643e540392900c40c034180710781e01040d404814281000b0040002164085c00704c0050741c100b0340700d5a41d0b008140140d02000b0038542c0d80c641d030124412840b5094890907030b0010240c5281f0308050701d00b03074002c0c4400c1e03540c0405400f840d880a00c43c2d2804c8903403507114000c0380000318075686d50204101c50015000d0190b00c4101840d800001e000d080c00c2202e640a9406007000020161502c0e180c013100d2043c5070710010074503042c045151000d40c1c01c0000d5850911a40c100703030b1f00800c0755280403255500e21003906503101e84c40d101884d05056118641e54440c620070701583c154520043d00555110604641400c0180c0c4180c001881110403400948403400b144130460343e20800655411000c0d00c801c0d04404006c1d48100d40b4070450080030031a024400f030b041c0c01d204160010440c04603610b448000c00d05030245400002007842601c1c1000400c00650300f080007482100b04584800015003c0080107050078805d090104440b8503040071000c2e2100b148903487c0c100e21007680c1c1c0310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 698722401 1250 698721151 698721173
    0x206030a0902121f05090c0a061101020c1506130b030601051512011401020d08010308040501030506060c0d03060f05120d0806060706090c09110316110703060603060204050906120a 79
    0x302e81045140c0e40c0c80e50715040c00c00c010791090280200076003142d081c4c41108400c071040205007002951005d0a01c200940713a072107140f0142c0e41d03540340040018000c81c102c103029114003514024035203d03c0d1644000030500240b0719001c0e801c100c6130701010004680c6140c0c141d804400c49158590400d400410051a244050512030b001c0900814280a2a00c04260004100342e11803201040800031051496138103028100a410840c1400c40b2554116151005103020b00c5c000c0d1810306607a003002c609107503220b41c14ac9440300301020442d0a4005070311030040192240384105a0844d60444007c0b5283c60320081e880c1c1a0039010300100080018154225488a07019041c00d030821810000d41001c01c4a174010041c4450080d440a107186142090410440d2800b4128003008041441400304191061445a04c040210f203070070f1785580c0f0b40000540c2043c00d642d100425030740c5419400410405a43c000c0c004a5034115444c48107543c514081c4044030052240c040c040c1d4002c0c00200303001440708652 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 698723651 1250 698722401 698722403
    0x50a090504020d020309070e040f0f080d02030a1a150f07030302070209090c09070c0f241a10032c01150617010f050a03170f071a01120206030a09 64
    0x218002403aa03810100d030481c1d1000400c44800e80e000010401d0b2500b080207400001c298003400348402c1c0c03510b03880b01711191204520007820004000f108030248209501607e1000c88814011980c9003081e1f00d22900801103c0303416000c1078001940032a040c079041c40181da001c11f04c980c40c070b413900b844070721542d4165200280450501d60309128080150311703140d00746440384c441a0010501c440006040042c1d0100061030102003010118600000a00103142071118980c007081b88038060500c804100c9403003c041d4882d0b1901d07403604d01105054500c0c520800d000f10400d44981600c0d04208400300e0686558000c0c65915042c000c2c0c8403035a0319031400b44506454240400000c100c220308110007150304113988503c00140403890014921903030a441c081c01469410440040c261900740400d014000b03a10011340b0038180c1048940c02c0743c0708030b0201c5031501d45128040b0fa032070926140c20200c0c10700311103000f0813000b01a00040741c804c40b860808039000c2c0d002080542143e40b10342c904006481e280328 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 698724901 1250 698723651 698723657
    0x31603050c0304031704090b150a03052502010b0f06040b1c061206051f03051c17010e090f0f0303130807020a0b22050d03030c020f1006061b0c06050a 66
    0x80080840d88540820650700c03145d04003941d40714581500d44d815229200c4016104c0c002c86840400c00503045821907144145905001c180d550752081040c501d21056808403207410f0351046102242c0b07a043d84a118a034004540383ca03145500f000503c82c060003180140282036104000800c2c40c942e605140803010f41000e030001c5542c81c1c8580e503a503800361083c001180c20036241c2c01408100e5000c488800d00601c2c2101c580b82d1002c0c83d41c0c5525989100702c1e4050090303418140d1a039143e0728031171f200b0350b030403402a551b00030402c0d40d4410880304541c1046508064034054910a0003c6c0140411518112a2920021815074a070010b02e5400b5209030b40d02102d603484108181d02c010f844100c000d4006201141c1403d0710b9804840c00241103400d11841080041810b2038184155540d1580ba0b440082c0c00d40340003d030265040c40264940b003c10608000d00f0b02c94200311144803d06a0130510a403031490b615071002501c0e0f984111110002d1880050824810000611049120360050421000c940c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 698726151 1250 698724901 698724907
    0x1030b0d120504051002011802130b060301262e02070b090a05010b01020c1e1914040b04050702030901080a06050a031b0e010317210708060102010e031603050c03 71
    0x41e0321a00800540960507012400109003004185800310400c03c8401050009029541d841021212080f03c000d400034030070010118140d402c10f03440ea1028000900191110742d59503110501c042c0981d40010042085410709200c0d0900b01c0c1c8003050081218520b01d1010725440c840303021100d900201c003030480c1e03045582400b1131004034940296860241c680e400140c1032040d0340d420010300b074800d680006415035100c0e0030030b0295503c5119118410441d2403400c5400e034075205c00042c14044000544151a000110002c04c200f442d151502c045401c04450810015013880280000e444049503080c1c0036800c184404c10f103c5d4043d144c9640c1c090300360700000511907100ca001079100c0301650400c0d60b00501d800003201603001c6841c6c07048068620710440415561440c1d8a500b1450364060320000482070200b0710f00c0082048040c00314060783c0841c0f00d05210f01d03009400520702c400031a0203c0c0150300301040020740800210445405484604841482c41d44546041c0d134143d0001743c00d0340b1948820 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 698727401 1250 698726151 698726153
    0xc0303040f021f0e0108010e101202040608070323010603020603010509070908160302031b0901060507051504140c010305040803070c03021e0114150307182408120c070501030b0d 78
    0x80040f83d010b02950f0349a211900920200040040105030031007030703152102e48203106116400201500c100c94947e80802c01030859071000c03c010b807070030f5400302146105014010041003d400d42480c555a80f010036151090300c003000c603900383c0c0c2240c840603401000400050209040100c01c25622181500788160100c0d80c07160028034000e40300e0340b0443c00f001c803c038051045280500c0419048401c60100c10700e110250400901481418801c044c18000700042d058200300d018010455000c50800440d0160318090a21840e095243e46030f00c021f6010312034411419600038880c56003d16005042c071415542c402c13201703a421005004041e001d510074401da1074010070000d0603e0990315454030001c1001c07040b096484092520150018604900858803400707241c80000f0074200f15130303c50820080020144050f90700038001c501c60489116500c400d107002d0440548034040884820100b150b40d200c10110b82c040c2540a0188000ca01e41c02c075071001c02166100b82c020400707c40008002400304906 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 698728651 1250 698727401 698727439
    0x70e01090f1407031d01060509070f020a06020a021b04141b0d1d010b03061b071119050f061305040b032b080610080a05090717010203060405010b0c0303040f02 70
    0x800c40300303c00040d07211a8225030501c504403003500341002400003481098200310015000400c02400713102004000014003928500c200040f01b14950407090840d603034107816400940300c0c012050196807070824500307015005c3c1050301ca02d4001d0349844903000c0640d1074035803600c4200c3c201c1c1400500e2441c002d12101600b400a072007005109103680b400ca42009621022003402d45244180c040c5c0b0a8102504008003000301d001864000d42c2d40201160341c8012515044000c02244003181e50040400e418080e0b00e110038030468030036180200d42510918902204000c620312403150b034903810b180c0350b000400207410290040700d555a00101a20408540c41c0c009a50840e00086030b100c1c1d42e841d6010041460350040c5c42c1a8000340c05550300c8129000c80740003c3d0011201512450380079a50340000792001ea0701b484000090080c0038031030006606844122400f0350003e0703500030311903031134000009a4035404404480c0e82c02d03482c4001d9400d55070f850f200c0e02441d80070044e043e80c00160a4128102c6404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 698729901 1250 698728651 698728691
    0xa050a020f0408012a021f0e0304080102130b030606040306090f1e03030f050903070602450103020f122e240e011206051f02100b0a170304050d120f02070e01090f 71
    0x1a0050004ee201d0740800c00000100c401c82d40802640c00c4200144005074075040101c1c1d098a80002011882046620f0020010200304138064007062000c0c4640e807a000000d06880c0010780280c0d42400304103802021001121070035110b040c0583c1c000c01c1500000b030300b03e8028159111103d45021000701b007110720003400b58800b80c2c14071810a01c0d83d011070507806014008006000c030070310b0300310305240c0c0344600440c02c0e100f484a0030140f5101000060300e511030080012012520f1240c0403001116010351030900e8031007601444010501d82890500d94000420110440c50100d41d0740504d04810100150303403462448900400d0715858100100302c0391201028400c1110510002e92034103c03003150000d0401c107440001d50007650a002882100361307a000103410a82d118906141c90007922810818650311541e8406a0490072032800403050207200415030034003680c0e170b4588548100d80041d0882e120743d43c0f401810008007161006008330302c11a0b003c44100b402d1408002480342401e400009070314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 698731151 1250 698729901 698729909
    0x140114040905010e07050a060c03050d0b03010e010e010b1002150c1b010501060c020405070c02011e030b150306030c01020f030d02030a091b060906170a050a020f0408012a021f0e0304 80
    0x85c3c0102c00400440c200380151000401c0e0320f1070702c0581c20020b903a00425a101d4540c0c0d00e090b16407286040c009995080d0b0000043c2949034000300000050a07803101d0182c6a850354940c41a41d81e20a200042da001040007041d034078454280c0000c80e61200a02001504124030f00038800342c2e83c0540003c045400d1140302c0c041e10441d25100c2e51000a88100000d40c1c0c8002c10003804c00100b00c1284006036001035200b45419070040d0701000c00e02012908800812015003006c1d031051895520810104000d8011406520140c0544160030400c07030041e0b98a020a15420103d64010000f040b0190407903405550444079044000c503407040301380c44152041c02c088074410b4002101d118104013580d00030f401440240818100b07032000c01c2d2007203040c03403100c280200414800384d00e42c0002495619654100e500c5001050000c60b1500c1e1112007490080c50600a00315400030700031004000408104c9148841d40b40703a0b80200075171004a01581c0020010072100c0300400d807274082000c800070042c00640098 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 698732401 1250 698731151 698731153
    0x7030314040c091a030613082101080f0607080a0f110c01020a08090d09030201030e19080a020c010806281701020a1b030c17191d0301140114040905010e 67
    0x41810800e0744030844035507100d0b188100194107132001c2551004507819910403400d070480002c501181c01d1501092061051958548880921b28200e03100c88142c5641a50200c0c0100c03a1a124000030443da190010380e0750001050000c00000c4d41030145070054803a800d907440002c9a14545540d42d01d0442d000003080060a0750042200c4a6055100f4580c2c1c1d03008024100404402c40c14020261a00e501400301904254494581502a450400c940d8101500c0c000713840687d110103003006912904484103210050060f0030400c1d45662090795440c0c010f50f80109140f000070002c0244c035144a510340055203407604014030020b4080f810314040d021340f031070342e8001590f0b460f1101c00c01002c0355071488030b20090001e00305012010a500800004459a000c280c102c0384800301a4100d0300c0d401000c0001d030030080581484034500c2e03840f4048000c0d40c1d01303000240d000890f402c1c080601743d032001104000e44a03604c800401680c00c1c036102074160580090400203c0012580f20310382910580343c1c61201c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 698733651 1250 698732401 698732423
    0x3070602161406010308270a0b0406080739060e07051c0807060b130e0c041116080d0b03060108010501171507030b01050d0c03060515090a09020703031404 68
    0x2803002c1001000c0d12040d80750041c0c5004d6046550300441d50040103041035506100300017070072202d98262002024a0170091040002c1c0d030b5150340140c82c0754800c0c020400001c40d941c000c180458010000184050b1a410805401b040542c108038125110440d81c420600200015807000c183c107485071030026903000020707108840c100010301c0001618420750808042411841d1004641408156100f440e40b044000c42e1001101001032445803240c00400c40e05e03850803406d10b1004000090809074204213443c103001651200d9011007540c016401520040622027840c800000c2c5814001d21841c00849000211995008042403500000741c100d40000d07951200140310300c640381c201c00d41d403400622004000c12040640e984002010180a000915407540f0f0365001c281e0281c003e46c1e411280740c0301c041106100b0444001d0241c2140d101c0c040c000d03a001c080142810081070b044400300304004d4002c5a00c1864980403500a5120440a40c1090341d01e115490202c020041d03c41d002d94000c0b100600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 698734901 1250 698733651 698733653
    0x1103040b0610020f0309042445050603030d02070c0e0c030c0403110f0d06020910110a290c072f01050c0114190e06040206070b090307060216 62
    0x40902c003112a0740075035202c0c858070382c1d0f01c410010483d29102020354021410802c00c0c4500c01e00014a682900101c0804410100b091a444100248280540c0c240c0c54a102091645500c040741c001440c21080c440000c034030080c00c0c40d550040c940107074002c0e0450340342045c8a40000c04907082080210f41c00403441c00100b14243c2d05095032908a09104110761660a10b50942081c2e442248002400c9400b4648442c2c0c442d80d9043c100000c000015003e104144e80d42e1610000a5004040861082c20612066405140302e6940300f807040e404000106203015050700c5505000204c000700134034481d0303603201e81d94156510b8500503010300d400801c899152400c0c2c4c030308029038810b440e02400304610300600e2016440c000e0361115103030600030300b456a03644190009050141240d201c980304c04040c003100344490340c4d081c0302182d2040c2d840ca40c010440c4600e01100161191415500a940010184000004101c480d142241c101e00494212450304c00681d0301d01003a6000980e0803400d081c04401500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 698736151 1250 698734901 698734909
    0x111070807121103010209211207140f0d02060c1c02070311061302130c11011401050102070b12010611150412030e0105100603020d0603020a030c030201021c09090f1103040b06 77
    0x14041900303c000b035042144103008903001c00d02354407429507a0f0b0064800d02121560510100e03001c001004080356880410341040816038a140d240040c0c1c910900c05800303000d1401041c101c00302029039001c0c254035180c11500c0c3c00b4a801c20321090400004200310001d550840e440100040c078825141c100a414220162a080c0200108690081c180302e03400040140c0c1c810091241088020070b000440c405010741c11a1220b031810a241c420b58a4100507020100e0040700d0141202c000741d00702c600c941d0301e50569000b58011007010085030184080148a054000d43d4201d204141045c1104d40300d2424809100a130344080c0c0c0d042d59004061000c016a195045c0602a204c0410038020700c16428441502403100c0c0141c800c02c420103902280d0b0080c1c2103e103801c10f500840d0001d011201041d02c07410a503031685400e02c8100d000d0720a140c06048183e0040403403a00703440040d200d0141451800840001a03d03e003510610b1169413140200c07548400c6001942c011070041d400c0d280146000e42c284 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 698737401 1250 698736151 698736173
    0x10c030807390b06061603050703030902180f060114190509090a05240d0f17071505091c0806061306030b03070602030405210f0d120b0d0809011107080712 68
    0x100340180d1081081c41034003505d003014128a1b07036040c900284e503000c0740d050803001042d90220003540540490142301c1e4040704d507100345008c0d08044410404ac1d447e11801565000d031a0b00b450303100c80e2828400d144000c03280110481683c001420b00d203190a6019001814180080b80d0b044502950f038024088000c2e0080c203031003c4440326039440d5a25041280019569000d0360100a05840c20194242c08104480890b2100c00300500561500c41d030092a110485440c928060002980340c100001da0340040028500000a03d04403c2d03000e00502920444031040010f20396500444200714580c81c41c01e0000c01c002c0180b43d240c1c3c0c00500d82150100300b509280b80c13940140c0842d401480709000c180d1300c240419003103101d407400818074a8421130010341807a00f6488031288a00409607984511500008a071140b41c01c6c81b5030401c0361000c1c642c20004840071170340c405050054240034000703895000c1c43c3c0203001c80c3c06620445a009a80380c02907031400350301d03800003807191150524020401c0850a00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 698738651 1250 698737401 698737411
    0x140f010602071d07030f0f09110a0f0302010c050109120306050310050f1612020309150115020304030305070614070f0f0305060f10090f06031a010c030807390b 70
    0x1501c0c2d59841c094003116600d000c80c240c1d03a00040c00c4004034050b14000e9104085050103e481032045110880e40300000344012001680c00e20110704c801441880c2c89400c18068822021110b900b290950b00110303220702c0c1c203c104844941d80c44803100c0205140384400003060466903808038001c1c1c08c080c18141086a4410190001800c207401c0c46400c40c08216080d40c0f20900b0341c00505291400c4600700c505451301e444040880d0320000521078041c030085805861040c203500342c50001d0f41e0340c0300d004c0914040004200c0040c0c10600c02800021b2044004114980c0280c0010406604004080380b00041c262105408182e000f44190354040c6c005040302155001030400704002d2403c40082000c43c20b0001000d403042c0c07010302e64000300702e000d048880080d01185000300c8000d92600d0b405401084c081b01030009030b52100c0d054070503070b612840b0510241036150381c40c41d00170340301d14205582c0c12a410650301030800e40a8920041c084c0014607400300781e1102c5144800306641c40c02d06900c00440549 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 698739901 1250 698738651 698738653
    0x13091a0d020f090606090612010f082407090b0a08010306051005031b150301090c020c0607031b230312100b04060815040e010b01020607030614060c0c04140f010602 72
    0x303000e0140e560800d07045001141a28440450f9032180c000500c42d03c01c020a0356800080890701c054a0f041b40d01c4100d05907180100003400300b035201c0030b04550b02d03c540003500174004183e5404036000310804070380c0d58003d60302e0705107103807080e0311541d001003140c1000e03440d040064008001001030007058003449800c4800c0c4405030700004d040101094031441507450000b040c0c2c82c201071440341c2d0340702d864000965141a100058881d40c440c450329015204928080300140704117040b014441c505041114a8079038140ca6000106080d00018003e0030604101611650f45181c142c60b03505c01c04c803e20752260701d10071740955958140f100d0a0352201202078035288881241100c1484200e140d23008840075282c3c0390030413000a549414000001c4010079640e160000c0c142800790444402c150040303c81110242c003a075000b44c0e10182d04404540c41031040180c1108151415401400c0440003044203d10060a54048680440218040e00c825560055036002203408100d032407524079440d2070140403584 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 698741007 1106 698739901 698739919
    0x30f1203060810110c07120b06060322060b03120714030c120705070305070e161d010c0f1b0f0f0e220f0c14040522050313091a 56
    0x7d45d007125680d0b007032000300d0628540442980d20902101c250060201c40d44428803140710700703419007610308a40d90069002030f41c40c20b009180e9a1520b58501300d5943c4070518000340c446c0781d801d589035060780051107203030043c03400803c1a0480c0050440b400342c46142506006040028070340c0700038603500c0741010003e4003956541d1003500c00c0b0f08a44401ca120660700070295132080004180c5a42c0c0580e824900b40158020016010f405009002001000e0050758401903007102c4200f0000c21510700d030000f00811006030340140054501c60103a2100c445c58a203254034000c4014003880640c140d038205c402e209011084030943c600c2d40240c0400c8030380381c80b030801070352804840c042c600703081340b15204c0c0520381d05140c003a0764003d08582003040111480d6100e05100035940703540031078541c0003c1080c02044641440d181010300501328000907858111004c0f044004400c01100c0e004281503 = true := by decide +kernel

theorem cover : BRFrame.Cov 698561151 698741007 := by
  have h0 := BRFrame.cov_init 698561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 698561151 ≤ n) (h2 : n < 698741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
