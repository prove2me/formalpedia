-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4233
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:57:29.695827+00:00
-- url     : https://prove2.me/submissions/87c80400-9aec-45ff-98cd-f6fcf13fb575

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 761151079 ≤ n < 761330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 761152329 1250 761151079 761151089
    0xe0f131410050a030f1104054204020d0f02030703020c070614031902210a1104031a04081c061d1014220507080907030305121312020c0307 61
    0x14844141000b0204160b41002e000c007904500c1449294020880385100080c410072010f0011302a50506400c08006041c2000b03060090305403260b0100728a0018155503250701e11460110500340c1115001d002c000c0d44851104085540c541c04000c0d141aa2800214040c000544d40142c1c0d40052041c4142000001e400c0803081200b4030300a10300c0c4180d00800d0340d80014050010301d8151002e0302c1080c009101d40346100481e040e01d00d000c607120300c14241e80948944c125110074071002102c0d41a00107188581d0000403c000040c64052001d0030380b01d0348181c0d001e4440c241c02d51609000c200d490b0380410000707503003484940e00d800003403001c1d1072000c00c1c1009440440102c24003e042000c840e020751019805030400d42c0306055041c905954440c4848243d14103000700a00c51082c07402842405814211a28400300d520b0102040000c413002a1314400c0380c0d0140ea580e41000d400064a03100724801030940c41c070305078500400a001c15071940e40440c0111454005010b400d24140c01c0c50309000b507075444 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 761153579 1250 761152329 761152351
    0xf060304080306040f0612050708070b0f040b0c0c09010f052b02220603050c0406080703080418090c06030504150b030706120609021219020f09010e0f1314 68
    0x1480009407241007a2a0402004c480100d407601000401000030001039100e114038100c007222038000e0140102d0740401783c0340c102d0b00b600c0801c1d4441038100c00030b2141e6500c840c8803050400007000f0004c20000500030001e540f0094482980b50803000511785102030300a0040086000c204002514154511030444000d000c880e1642100c0000a6403801410034000782c040e400700d00c54209000b100d00c0c405c6400c40601c00c41080760a0712424480c1d56010701d002802c2c0220702d80b041c082010880080c0d041c4c202c907803101c0803d1401d07080c454074152005840080040c0952140a5900010011050762019008503600081c8902d0a402e0000c0e950400e45840c6221710701e441500041b82d01c0108800c802d40b109800d2600b00200441140340c01428079a02c6034034550700c0800c010a1220380902c50f240940035686203100154403840c0118103e1042030700004000340108802c080b50350062015050104005040300c5213294142c010a03030034100d88150b4524196135245100700480768100b0290012051a2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 761154829 1250 761153579 761153581
    0x905070c030507020f041d01061d010321090b040b09011808120a050909070c12080708011a07020d061d0309181911070201030516020601032301090804050f0603 70
    0x1805841d51065100190082045c910402d050780c0340d03a00002170700700c0458502041c41d00202c81c403034000d0000e40108807031001928030141c0200e10791078091341039a4102910a0b1401c400c418004140c02c0d50031810b0051210504000520403030413070240c002083d2400d011650395a95100040c40d1740c03915460a0740b80d00c421030060020b4100025601852800c0ca40c030365540e130030f1800096605014030b6404a500c0f003542010030483c15071010501c0c00d4203110b10140c00b4a2001e208083d122000d04540c0c140014800a004200c02c10282c016402c1c544418548a0300d000301e030307801244d0300490515082d105d0589440301100a090140702c4600c1d402001c3c07010311b0070104101d00142442030410f00c6205d20071f9500d0701054005009480d03c010b41d4000403002c102520214040c40e20b1500140c2c0141c3c00300f0300d0b08002502ea1081008102218555540500700a03030842c0ea88410301c5920481e440c80b00030941d01e921502c00800d21038406a580114003242d111480c00c01002540000e01c1d1441d03010720000c0c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 761156079 1250 761154829 761154833
    0x50106180e0a0b0709030f06020d0c0c0f230307050c01091401050702061b070e07030c0c1e0305130b041703040302060d20160204150503100f0608160905070c 69
    0x400d0300410349500c07083d80303c031984800c1812a4001103030b410140080110b5821030f0704200c2264011300c2140c50090082c05103910101c41074543da2740030240609801d048296820000d0090411980f40e06041032500304003410b95620f45186810941d400c5616030301a1406000540e0000428002441c82d490b1088007610303403100003413203400b131304034000c1c040d40010a2496003d101401d101805d4809141194201940d13100c5040441c1301c2a24120082803030128040c8a5a00c0340491403a590780103030712105a151154007034180c00610ba0002e604000003800702042c580703c0c004000c1c00901089142c0d544035414440d03180400310b5081c142d07000582c030400040005840c3d40301940c083d807048040c0014164801c1042c3d100301d8040184a5000410003d02c69036500891080d41074614021f9804000d10320040086108041da24019a070340b56003e0010349203e414203400c002c03808811000042401a07490008a1810005080500c404840404103004031103140c4a120340c003080a15014a2409032a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 761157329 1250 761156079 761156083
    0xc1f020711090115110a140601061b20040f0c0f020c030115060c140105010905010e06092a0904230a1b0e0105162307080c06031e04050106180e 63
    0x1d0042041840840f90442aa0782d17414171007446019004101c003c10200e183c1d4290761540c10034020200426602590f00d6803407400b12505810180c2e1042092598070010249204528a6059455803154071b45c3c05512014200d030246101c035591a0322080e1403a0100000642000e480c14891406a07242400e00110351103120411402c603401406c04955203405402c040d1019046414402043c0d803e00c3d0000802980c6503010078100c42401400c0d0403141c4071241004146101600c2a40c2e8803404030007030b0880d8041340c81c01035149084101d540703450a41c2c0000810184c5030395803841804500c0b080d104000c03d0402000c85584442d003914104500400000400140d00c81c0c58404001c00c6030341000440c0c0c0340d025908881c004d14141404009403101391500071a03176005850b000d1100d000c034643c0c800038032100140c0c110036a9820b034050002070b800842032201c19080104494500b4444000300a03d6104445000e07000c3c40c000d800109106040c800c4460b1b803c29608100911a40381141c80300900c800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 761158579 1250 761157329 761157359
    0x10c030f180611120c03070908010c0207150c200108060a031a0615030907050a140a03080702150309010b1c02030d0c0302030f04121a070c080c1f0207110901 69
    0x40300c0342c001450480e40c4002c03180c40c0540e601d12405891a4410300281019a0002d14800c4119079510404180c5a42d41c203400e0f1510054150050303070200c07400b0301c008101841e54080d629014505052116110b45400c0d12000030b101400100d1286445001c0b05568880700503944100c1c107490505034203256540d81c02c141e05119071081160380c0e803070b0080b0b42580d907151081e40c03014144039203d03516810045082c1e0b49501c40c1d48070349480352004090015144905030351440c4040c000901c00c054079851611454083c5c0d000c15409c0741d10070300d24240c040341b0313640c0c040245000340810000021840c0608040c032101f01e2425100f0000c0d4081e4086150050340c0c00240d00224400a241041001c001850260720b940500192181801008030300482d03c41417260503000214054000c3ea44c0d81c0a00768801e403060002030702c07100300144840c0107541c0030580315401040b100f4103a0080b00c600e000300b04054000302101d02d0394214050780000e400424424011000d1080d001e00b1200c1c03400552401c0599128080e0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 761159829 1250 761158579 761158583
    0xf14030303070e18071e11190f0203030a0503010f0801090c140a3c06140f0d09151a060d0e0705030d090e1602150a020714010c030f18 59
    0x2c82c1c1007002c1c010b440d9080c1940d284590184d0034040d500b08444090507002d41d03000444400c8600c500d1042c08a07100e03418141c1c840d01590041d018210014180d41012080104c2c02d454580d441e03c500801600c0420040001c00c1c2c040c0d0b10140c076541800b44003900c2560503400380506a0400c60460b0204800030070030b50440c0d803160444c00070203480700c0100d121000d13182d000d03e0800709500c0c83d0070000c2e80c81d044006041c0034401c41e5620010704caa110360f01c400b44240150340008201681c0c0b0208010b0f1400107090044110003140c0c00c0180d101c10090580d03040322011075100c44089900003600c0d100d4001c90400400c000c44000c40407141601154207070041a818030040b986903911611800018000c0358041c2c00c0c00b4003554407584403d080034140340028407650a045504500141c283c405842c030000390040907038080c00407468000c141621090018141042d225030030071010000899108042955211100010030941c0c9400800380480c2d1403440e80711506404e200004501100c40304c04042d1590f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 761161079 1250 761159829 761159837
    0x20a050d050a1b03052a0601050621090109060f1a04020d0b060c0f0c0109030503120c091009030b070207050609040906020415082502060412110a0c0f1403030307 71
    0x548800c440030b50070078821160f50780303e01d40390005143d400401806902c0c25a44601004141d40820100c0d04482c41c0c0d156589400000c014040d1f03191a400810000e0401481241d0b41a007440c491900070000340c0d00b0400c16990345404000300310b82c90145013010b40111804001c81b600341102c1c0820080340c025500c0c41a60300140602e00c80c40340341d0099001d400040d16140c1c549103c42c2c0794960303904106250305403c0c4034142c4101c480b5032041030284245e07617101010314207080303c8000c840102200a01f00c0350300c0010501010441d40c82d00c40100401c640300f6601e080850b403550030460705c0795001911840441d00000f20601180c1c403540c003122001d0a080d00c0000b008a000c3c188440240140c0d0407d030810030b4000001d40503103500002050081e90711003030032042416080254500d00400c00c40d50382c05600a90300103404104010301c04031006115042100440d01c0c59a103490810302120001c0314400280501072084100d8000c8200c0a480740c10f040764100ca8855001035030700e0000405600c208 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 761162329 1250 761161079 761161087
    0x80606040b490f03030915050c22050d02010c050109050307030c0b0106050403241401080a15150e0a0b1905040c021b010c05030f12010e07020a050d05 66
    0x65142d5201c000b401c0d426034070804a030094104104181c285840c00c0845080300b80e00c1c241044001110501e0820503405480701d001c031600c03943e0a0b0054000000f00303445a182a00304294400c0190241e41d00c14018404034954540f2541000b504850a29031001072001c81c5040511168881c00030307400442d902420801d03041c071050f14141c0e01401262100403c140000705000003016040514201401c0c850035404206a07203888040311207000320310014000382e1441c803600895910701d200f040900104454081150109041c8189010380207034803a0042ea400313608035109104422552300504080300005002035001c3d032040840000c00e0340203a03000703117254802160b15540944e21020340408043c01c00941d44446c004e4844545503e0720445020358141514080c0c0d591001c1001100c100c1821b0244841061200046860040200007151180300c03c004010003c000440600841c01c1c12400b13801c406d60502c0c07041a031101e8054148010f5520202c04400000d00c0403442c645503507903502c2c026440b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 761163579 1250 761162329 761162351
    0x20316050906061e040f24020d05070f05060f1009090b0c0c0f0a0c051305070c1113090f02031c090e0a06050607050d091e050d03171e060a08060604 65
    0x4a0b40484e0601e0010040000c1c0004e07401c281480c801d011901c08203504070b01c9040c50072000921401c0344a044005030080c007901ca03421401040038200d00c60280c000419002000e0395a10701e491416100e0810315035a902c10490f004450081c01c201038080c05509001c6031210b80e03200203200c1c1014024008044004c145240e180d4010041c5400542504c01183e1107600b00c2d04103031b0b1600b0402e01600c1d000700364542d040c440201c0c00d4080c1902a1107181d0391007503040303c503403500261b4411054070745034049500703019101c0e8915035001e0040300d10302444100702020f0051040604e01030304100c048424801c101d0070070450315001604081100c02001070800c0980d200000100145031a801440c3d2002d000b1845034148480000c0074145d2603400d46902c012142c1b503411200d5506543d10700c0019042d50082c051005041040040e44624824104005000080e442a00d036403001201c1d120645a145507840c204995071408150f0071001c00d0b240042c4040c01e00c84e00644859000700105c0c003850b01c4101c1250 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 761164829 1250 761163579 761163607
    0x6041202030c0718150803071b050a0e01171516020c0d030f0905150702040209131113061b060b0a0509090f100e0a02130f020403080702031605090606 66
    0x803080342c00003a141115211942e04000c1110061a0350aa924101e003002c009103c603a401420390300d60000550510000b43e68080300c0c011290fa65400d918512200014541c841c00c5040001c1c225903c1c1000c02c1d98100401d40c81d078503465144440c01030740202c49040aa58610460a41095222650b502c0703410100001b80d14002c10600c1084d0807010314640041419407244001d45201e02664034200c00a684000300144540b00020300401075000700032500040c036140d8002d190100011707020903610b0a4400c4110110341c5507505c030b981d006000203180f040c0071500b85a2070020700100d0818013036800d2024601049600300800080106075148009082c50381e41c01041001400e0003440003560b40340c40c0c2601d94071803001043c40200e502c219845010070030141d000d144400d100440041c001071f0143c2d000c004848001d6503112038066a40c1030710b645000700600007880a503010301140c5640303002c644185881e10450440c0b14505107484c08040c000e603600c0390744460308064200c40300c507150421646888 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 761166079 1250 761164829 761164837
    0xc040803040b07031d030d180e011d01080304141003090b0901021803030909071407080d06030b130b070f0203090a090911151c0635010903020604120203 67
    0x441184404500091807141c81c0c0003d01c842803003942e031900c240d10f01d0300c60655076507001544164580c129141f00c03064640305000800d00e82590b000c0b03600080d59204e2503600c07201000c0e00590707000066148c2039650000d40d070100d1401003d80d0001180340c1841c100420b4080e000c46640d40b80310300311120083c2c1c00340740701e9000b0545a9400c8454075806041c401940c038001e40c010f0000058040c4000403030314951402005449155002506001d50f641d200358088032003d00c40c4e040e1a5404005000c01004a07444802410701408ac00342d00060041c1182804000120024410021505801949c0c03001401402c48550440c10908001c86003090040c002e9065000d0240c01030b0300070034001800104925640c01880c0420702600441d0000c10046081c4904100000c400440301401008001060802c10000c24400071000b00001501c50701c9030000b12006240664a00000b03080c200320b1080c00c0c85084e12181010403202c020409804580e030041e40b139280c0244080c1c103036244400d980104034000d10440b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 761167329 1250 761166079 761166089
    0x3050903180402280c0c1a0f03060102071d0907051f030b0310140a0f0c0c03080408040506030915180a020919091208070207051c0204200a110a0201080f0c04 69
    0xf40209164030130010021124820156003201c40d0340700014135402c000f201e10300e0321880455020f00e481e46810a400c59a40f0140000341107201d420340026416281642a00e01201801034110003420540842807410005030001e80c0705004031101011848400d45001003010b984d41070110301680c1e0000001e0801503441c6c8149460790404040d05203d100c1c0c0c0c040c02d442031780c45030390400130b512440c00200211284604003070003080594000d900442d000d541c655900610488030701c1c2c5481c2c0c490010410f990030585203070038035910003200c200f22001403c5400340e10104400d526901c1103101440c080c0c0e1141e040e40d0190207850b1071008107403c0710343e00300419403e0343c03016028444d00040d45400c07984a07032856407040c006455440403415482c03001c50300d07600f04d820007042c03089541410502600d1078400c0d100200d902c20b50b600c0d0007603c00c0b03d540081641403510004c1c0c1d90707100c90080340003614400006505800360381280301e131240142c0c0c119000d66049560405a40910365669000001038840c070307084 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 761168579 1250 761167329 761167387
    0x30f030605090a090b0916031704031205070b070807050a030c050d060f0302010f050306030c09070c02030d0921120f0c060905030a031103040b1b04050409080a03050903180402 77
    0x300410f5802c00e40120b20118841d80e0486440d642e0b91400c1034442003080c8142c081102d14010130004202c0002d90b24400080c0c2200c6c140c60180c0e80e544915150801500c0c08000ca60003150745028441d66200d40e13a84404241440d1103c0e1070003510040141c40f84003d12418107965100401000c0e101d10255117071059852400c0200390740b900c002c03480c2848940b10481c0082d81c4800c0e013040b401d01c0b4a099a021b500050014568450740d81d0800c40105002400c000030840710400c1d500150341c04002d4030030048101d4442000b81360409070302e0921901c801542450319203a846210f40041c246c4c4258038521880c928281c00c61601d4080f04448403000c01ca000342601d41004011000d014001c001801c5012460310100042c14404444403094002103074054030141607000084d5204a500d05618445c1544032030345890300341c0b1800018101d90803110b0130b07121600e01007590300c415501740c454180c21407041001141004503d1740010500500b040340140101e0700403d004501c24484a4508012100005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 761169829 1250 761168579 761168581
    0x1005100b07140f07030519080906031f080d020c04050414240703090b1902040f060206041a06030a0f0201140c01090201020124051e0d081306080c07030f03060509 71
    0x2800814400712140c504498003d5161600d807070000051514102c035405030152203059081155100d0741400c2100c19503010200304005206580c03610000c2d8403c51251085200d40c3c5012456410851070300e400000607603000f044240401c075000155014030900849007c6640d54486c64414804080b45069900d10301c00d000581c8982c1c104842485c00514644000700703482c2e030718118210146c03500c04102400c10361981d800700329040c030b0300c0803800c44020282402518040d5980154091541d00d6480480141c021601340070800c0803001c000c50101241c040d10301c4907400e0079070009456001c0ea0070014012540940d607001164007030804085801c1c2010266921a6180101d1501a0281050480c0154a0071101c6850610030400191070040910014804541004240140003004d064903801048000300c0074040b0342d4560f898002e2042c800c904c640e4450186a40c1e0041e0208290401d07400e01c0180c004100d40344d21000d080da45466007524140184c011103640030b4000301800c1c2c100070b4211040030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 761171079 1250 761169829 761169833
    0x1811031b1303050d05040602160312050915040602030901030b450115020d0305010e0a0b24070b10050102030d110c1509070e01051011070902391005100b07 68
    0x15011b0012074209400ba03400c43c6103800c400c800c14030914000200030a09403440240c025208030003805408001402950683d00a041d003c01c40b900319070700110040c1c1c800104030425581c0350040520f20081034074040810300d061070364046115103041203e00c1c0841e59500c800104e40c100107070f410318802c4e03500e00106a947c482010070a02606030101b840903100c0d05514070b050328420310985040350f400b102c600e01c45444008105015140c000a802e81c0042049072080748034800c15580c0d00000051110180d0b52805450403a010344001445040e059901c208100881e03600482214016080303c60300180c02c0d80700e031031408420701541c002d0003400c0c840c2910b00d1101d87c50000c083c90068065900322001c440c1d8440d10b016610500340a06900007204038940e032221030140740b40303441540400003070f01c56082c1c4440d2885d089030890803080a0f20440b81c00c00044044030102111480905203c184212008501d1816920240101c418035825034a000007564040300c1880d02006c0c101c505501a903c1c440c0b8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 761172329 1250 761171079 761171087
    0x5010b07030801060503090706030b061308071719080703120504030e0102011a0a0308070203011407020a1a060f0906030c130506030615090711010b0a1811031b1303050d 74
    0x9140407000b04404400201d01c440c050020380e44140307800002082d020782002000c5010f08810405640c1205085c0074480100d8850b140381000340c0103d0000341400b62038079111a40ac00702e030140170b6095400040c05606440075280980c0100d03500410710301d5a90750545011a0740d42e08609055000c545014248010954070002e01910100264028008d9030b09021880100000b1815102c1c0c0c05200d65400b0000550303002d01410311180021700015454100d550401c41818040700e011005070000341e21902000300a24411900b0004044032524500e020400301d0200b01c65601018072440d62100080d0fa203541c20880e090003024090201c0c50201d440c0f101000c0a050141d450611900a100000e101250303603e4104042003001005440b042d1075003442a03c08186203494200b1954030b81c01c0c0c0c044241c503000d0200e4018500081c12680d00b0400100e00740031600c0d11079803003001810400034032401c2c00b201040e0140d82c5000243d81075a48040c2c10810104070200d034001001c0b4010494401c00740350300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 761173579 1250 761172329 761172337
    0x506181915030501050a0807180e0a03080118020f04060c05100c0504090b0f010c0f0c0306060b0304021801081b01050408070905041a040f031b140d020d03150303030e070905010b 78
    0x30741c1c40c24400c90b43c9520400c40310140a0050340c01c1c81c3c7c40510100400800c9440000649540c20300000701072480946c001d0030000c644005070042050721004000e200c20442e8650803100c14180304605082c103524110005124900c103410800000c20a20b4003440011f00c1400040e0341650001c00c890824568046d14540180c85200c03030b400c0c5010300404c428205840c8004042c001695114112680c40c0c1c0c0b00000007441a00079910f0340c40c034003000b00029030305120b21406040c4244105440740350510400c000070803620207000f0720110030001001856000216684004a510703a4070b022085030303100403107650203142d218100510072804000fa101002e580701d680254050420324182084c031450f074400504068030002e02c0081d0001040020034401c8d00c0c00800c06d01b1403e4540301421146c0c48000030006095171104882c0c11040a06141d29010084000c0e2059a800d0900c010303461211071182820350b510003d030906454200707140303030100c0512851010741000042008070356190721300c04000ba00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 761174829 1250 761173579 761173619
    0x918070f0f1e0e0f0d171309090c091811090604110318010c3009050d020c1003111c110c070e13020d02041d0a05240105061819 56
    0xd10b0000d1304d0001d040102503860351035040300345c0ba000b034164001000110b40c060031041d41103140220012036844818050284410b010300480d80c1014200940001103d60410901501380c628901440010f41280d80c0d1184600084550b600c880d52a03401140150100070401c1006d2a000410403064001000001a1450f50b28008005180100d030f0299050b803002041c10003c081e6420030248a5000b184084402c44080c0402050440041c1d455501e060300c0074440301c015070440590012282060078802c14503500c0307454140440800340a01200c0f92089000080c00c40c4012022940802400d80000c210b03540c0352410140d0310510f040e0380b41c1d101c403264016a80e8a25038070002c0350749100703519036506801c0d4005001d81000003151b400c2200400c0ca200301808541c48011064031010301c107000005189000700007030640035018a059045851600c010380800c07030355140050046440c3c0d4000e039440d0000f4442090916084000041c84241c0043c1c1c0701c0d000c00c03044c85408135208400c0980f075202c02ca = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 761176079 1250 761174829 761174839
    0x6040b04380301020c03270d0302030d0b0a2108070f03020709062907050c030102180f0d121d1f030b030a1e1109010305030918070f0f1e0e 61
    0x201c1100109401c4c2e00c1014221182ca6106102c40424510b81da000303809490101c0c0c1c124820b403000007001c40e0605102240680250304041041640300305140940064028100d40b403030a41410a00080200081c03e2516010b80b10003506000800c24514115403e29400130300c070103190349142c54000c0d84c5048601a183e007940c186540060724a401c901c0b54444002d0007040501000852041c504c9150869041950b0b144141d81d45400203490038401080384140024000c007101e541c810921841d400610031031405400034101c48000304000c40b21b45c440100c0113191025842403ca01a8182981d6003000d0690160b40141d0501d40800c040f02d0412000b411910180810005241015186e00ca9114060588200300440d06400b05181e030b01c02c4000b510942101140b034252401203645818242c00490300d44d80700050a0840d40340c5242d00c0c01c42100c80700c6c0501d81603d4a15001420220a0650401884400001444081d00a403400170754081091955a2024104240146005820341141c0d02034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 761177329 1250 761176079 761176181
    0xb040807150e03060f090a06140a0605010806031213032f01020f0706110106080307080403051c0c02040c051204060501051509010c120915031b051206040b04 69
    0xa6802008601840180100070f8811359032002d600681680d0300a094002e42d014840d0040001907052080e41e11042c43e182007a04a440c014003401d01700c50f00b580290707041c054100b0422000e50b40c006122017103540d03071504e03e036150001d0340c1c003104940700c407600000c01550441d00c00c143c1084120408000b81c003c599444542441603100580e00d40e180207544505d9600140820711429008014101111b000c11000207440e964032406142940c10459048130b001400050030400d1000412900c0383c0d200d08020300700010b002d1186d01401070146800700138044d980f240f4000549031f00683c2070380c0103004219a52907061901d450200c1c0140024040c5a01c920030038110150b80d004108155801c12806071600d02c070061954603a0210300d03e009000c6001c010f40c900d00411200c0c0c03404004004036050392800302e0040c11904000c2d018600034260407081100a0241c0d06c101d19203100a02e401c80800c0da0300080148042d008103000c1e20700c2c0100c01c0a40d002a000c1c821910281c0911a4255a02c000350340d114 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 761178579 1250 761177329 761177369
    0x20307150c1709030a12022703030d060b0c01200d0c0504050901094104050109020612090601080118030503062409031005130b07120501061d041515090b040807 70
    0x80b4081c6200c1040c03408040b8100c0e408c5224064282d0200e100000c0480303003001c5400ca06802512040d030040440e010b008245144801310900811558100010550303042800019103084c1901583c49106000c0c0d88400040011901440171074018003406040042e0a607110400b00c8058282401ca80d00c0303600c00360000c0382c0e207031100b03a941402e10013a882c0d64030300102000300142c618140240050341c06540e282d081400503514030004013010444200c500d0a145001e03000c9c541030450582c04000b059050403a900d0354000c03900303a80302c041581828080e840352030304001702d0707200c0904d602082604614408440040041d0300d0190130440c90440440f03c034145d034070f60714205a843c203490300903516441c548203000060405018580c0a03169290240064940f041d4440507584c0c01c0c0c1c40358000c2607032050161741c054141c00c41405540e009480c20312020b0035201c4050030f00e0509205001e204070806007211080381c81040020f00400c040c1d403866454035120421262a0480c80c030584000030700f4100e410395 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 761179829 1250 761178579 761178581
    0x201051b1624020309010c06020409140601020f0f07030609080d060810060b09090a0209030a120c0b06011718030c0a0b01080601050a0b0a0f1202120402030c01020307150c1709030a12 80
    0x1000302d5a60145042c01c50080064031080c00c1464200c84440e000d220100340c042c0203102c0c5901503110321b841c1100c5410180f0000e4100508141384070651340224040c1c42911720001385042c101c03548440c000031145d44604181d032040c0204007201050600780600002e1540000655040790740302e0000c100080f5940d46120042c0344103000c552a006405680000c403686038070b501070700e034041c0050107507035495021340d68880003040c00c0c1495030042114060080b061100c104c002540c41030003030030143c405e65842600c00043c0107005148848184205508503070080003402910903280c00e800458a400341140342c00508640c09008241c07881c81246d00000c1c0c1854000341e120112550980040e02e0301d40e030a9070459414015a6142c0e0511200b844000800e044030310003003610f8040d644d00070005081c540704040c1428000d4880700e04550007848500045012a003030601031600d50040061604440034059515180f0a51440c8c03003000510200006148040001d042c4420305a966080c07041103801460 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 761181079 1250 761179829 761179889
    0xc10030605010c14190c0812070515040203160605030f060316230a090c020f0607020c040504140a0b01090b06040608040f15181401180201051b16 64
    0x1038000740f006a6a0004039910a03524200159081d00340e030080c070941600703404c04600e1400f040300c080f4850035003080980c0d030034081d1702e81c2c40c100761012514101c03050b159a583c1d1044a201090003544c1000458215078041003014012034141d1000314200d5038403000600240c10480b030703600d044100c410000c1c1a80c0713030218191402c03038450602d00c1000341c20440080703110078240c04584081c40c01d00180921a5070380181302d10080106a801203007008415a00a0403c0b926003c0031540c0e502440a1004c0d02d500410360307042c140780c26640040d29584900385105003002c500d62103895809140141c005214425032070a06030703480e801c1d041c04603500c0d000601400c0c0c402c610584001500c10b0f004200001c0304840700381c01040c05145089401d030285882d02c01183c0c0d07440c9480a41040c10070300b50003003002d41c2c0000485200c2d0103000b0407400e44203640d0100d1044148400a040040001303003c0c0302c1c2d072400c2d0880c1d010794022000f202c0007600d03c2001240d003c20309000c0c04000341000c0020a0710002600082 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 761182329 1250 761181079 761181089
    0x21206120601060503040515010324060308091e060703020606190b0307110f0f0d0f08090a060e0a060c021605060c0c01030c090b0d02131d01050d020a030b090c100306 73
    0x249a140e2808400300c2c4c440d00098011161801088080313124560041095400b03140581813203014414117106520960314503031440c0040301d01700081000410703145e009961100340d0549031180103c0b030300741d00400d0624030049400d610140100d201e070709150303000640500c141025108003c80d844a030036000c400c0040d80c8144030f0101c00c10800140700c20300c10f00c50507172410055400c031040440001816404e04451020f007250952001e11484120380c0c2c001c5c05015450030505002d00c6074141000b0a9840c1c4a4010014081d40d403160340150a07450104030051480b50403c0c0108450501c069000b034030f414103011710000b030032200040070516240c01c10484d9500405480140050045100150702804101021009001601500045888440303004020580031300c2c0c001603485404410440c5c6101c0240c0107518000c0f0440500d105d00c10381c061800d8107541c411200b40c00d501c0b600e88000b5a103404141c00041220b402c140502010031400034000c01e2501040740e5440700c848220b50104d088804074410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 761183579 1250 761182329 761182333
    0x30708150103121d0d0201030615080a060906080a0f29040203010f0b1014040512010e0f0c090703021e040303020616081005060f0408060c030414030a200709050a02120612 75
    0x1400080f49409103004c01117510604000c103401d03580d4401011000103040900c0c0100e64203e00b0400545964810170001d4600a40c08000382401d1444113540d030a50b43c0300c01080c16000c0005481840030307900d43c6490071440c01b01ea181d21500b424107200c5418000303031002c07030107507090505101201d413160090043c0d04802400383c02500500c0f5a0072102d141080707074260034070714042101185a4903450310000c40d0580d00000420607801c200078880ca401100c01d80c00d90741c1d8209440201d000e6843d01021508180c0c149800b6880710b00b00d100c21185402c0b41809008802c0c0c0c00100001010340105003144500684410100101c2d108901034a00c1881250315805544140b0380c18019407500402900d8102c86201c059810a81c681c1506490100165412a034110020080004000b20b0009042c0c05c2c0d0aa03002440c01c0507404200501445081d402d2019120103080880080041c108003280050013050024410360a00590004c001d40c01644c1801c1c048441100060300c60400d50000d090203181c1c100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 761184829 1250 761183579 761183627
    0xb0a0e0a030f1e021207050a050901050607080a11011a1e09190b03011d1207080301090903030902090a0b01090f050f2e09090c1d01050903070815010312 67
    0x1e00c81c43c9520442086500c01a40b001c03140002d61541c40e901c20185099500902c10103081000308803441e003a9601c0284a80012070050106843d91800d940c0c1c0607520000c0d0580311482e0110035108a076940e0100601366107458515403400d02030050342c4440075401c1e22001460035040750302d400c0c4441c5440040340c00c85040c4010444600c1100c15140c1e0b03901d02904006004008180002d0a4840401e80745401101244c07031054000000d0019461212002d003c2c5894048240d580e058240814410302240342d903122058014180603401030341106a00078401e510626000c0c2c0120000c000303011f9042c3c00a00220000702c1c04800801e09001034540c001c2114078003505e000e00b080100341c0303400c2c0307a544035032814041031555100704080440380e11800d4852841b00c43c101f440c900c3c2212140c0f101441000814400d01500500d14030350248800820b10b806541ea60138500800d01e850142d031302101030b0740b0507248c401100c69040c90109040c1c9120740d800301800030721341104403401c0d814854a280341500d001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 761186079 1250 761184829 761184833
    0x140a03030c0e010302092d04090507030210050c0a0f1703090f0c060a080109050403180b25030804030c1b080307050c060316030915110705101808030901020d060b0a0e0a030f 76
    0x141f042c0c80d00004030a01c0000302140300082800d4400030b080c1150030781e11091081c8110f1810b600e40c01300c19032680c600182803000b00c0003016503801600d10090040303e8040030b42070601108c07100000c7c1501d00202c81d01d80c2c034144011200d40c1c0b4400017000e45014026159120490b00d403140c01c8540c028019501c01c41640d003031086480040034042e1044040c0f058400301c4200c0001c004034a013008040c0c404030a62118000c4801c0418014802b854440b00c465040080c40026000701c42590425054904a4a952034501d03004541c000400da101100a00b01320303000811160002c02007418038031910545d10040da100090025a000c181c0c0d81a0b0416140d08502000600c00d50000710740c0c600880940204100c0d490400c000ca6035080c04c1c0741c981000008441c020f10000f002282c04d04814100b04002d004440c1558030750040c92003500800d160b0001010034079035a800d40644018000844040090b556502840c51079540060031880209680d100d8041ca10b24111000740e0460b0b4021040307c80144241e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 761187329 1250 761186079 761186119
    0x12032703070501062706260c0901170712032003090402030c030f090c0303040501050a0507120e0109090b010807050d1517010f020c0d0c140a03030c0e01030209 70
    0x2649001509100c28001e80c03001c82c0e003d000c0c120042400c40d00e400781151042814108050707401ca031482c0c0441c1080c008001c55140e10300811154507024071482c8052080c05105403c040c941c034512070b40001c4000000c20706a804c589048405040d103c200d03202c01d0341c2e030f6801c80303200300680300060003081d00145040c50748445c21850380ca014003050141e80c40d000300c2d6000502240c1090301d502070f498201004014172550608004c64018a45038000c0110210040c0000ea0381d11441c020715040181c0420000131071b40c050400d56550740d90210144041c6026240014080c0d010014003900107a0040800640c000d92481004614181a501c68440d582d4040702a50f182c3d000001901846941c0e00c07070303110441041040c040142080b040f4036605d044c6d0090b0381d00d0a440e052030101501510401080400c12000111045003009505041c400d6000034103001000940602003015107000d0350710420101680b590101e08542441d4444a001c100504011402c03401140140f9400007a904107900c0c0319154 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 761188579 1250 761187329 761187391
    0xa05160e06072d03020723100e01050922052a09011101020315040e0114060d02120a03030209090109050402033013090c080c0d1a0d0b07021203 63
    0x1000a210528040c0e01c1c8040f41d0f2909100c0241c00507003180f0418008120200b181e114420100c842c031058080c040030000b1180b807008200b15003442884801040030b640583c0a992040744020000d0000c6440b00a2504400c04000c0002100300e18100020300141c91a08051860f48143d84458002500e00c00420345c6036480400036a041c001007a02d004c816a00900056100d01441654000c3c000400424031041c4c80240c0000003541c3d06040c0f6101c0044011100c407a8024030850744100c82d4441e50000c552806ca1503525420607005585001c020701d60550024038600c03038281c0d000c0102e80e0b40ca6009000320340c1c003918002d51580040f07039000081001c411078018443c246c0d0051b2034071200020b0341601e840e03010b403c640b040002084002c01407000d0b68070030403110a44d00e00b40f116403031810744500303c09442524100483d8541d1995400203203280710041300d0080310050901d01d803e50b428202014090000c0b155280144104c118981e000c00002050324060812351800300944105103046441e2115 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 761189829 1250 761188579 761188613
    0x30a02010b131e0b1c200901060219110d0c030b0c120103061a0901080d090902031003030c0c051021060605090d03170a0501060f030608030909060f04050a05160e0607 73
    0x1029003981062411101c01780c9051842916419041070b440c2d20410000c020880700c2d140300d1031a1030010021560081a10604401001604406008030385011080310f130001c01c0054005c680c440700201008a02c1a03d00207890141141c10265540e24004180301e10404882d4500d80003003400400000d025038100c884425040580b400711080110041400c0610036030150000e41d000e14540c061041c3c0003021030b0081c1c00410420761451600303180d00e00200009110083c10400c28110003401d000c1c1c0100b0680c00f8040003051110440c40011006089002d001070b440c00585200ca44c408840303e1610407041201c00c5070700c441d400c0045083c10082d00b14640802a400e0048010700440248240c40403240729a08003180000c0d0f950401030024003200c44801c4400500d40341040034000140008152074000b4001c0b141c0d0344a60380c5050128105001d00b02c1c0c219041400d003824845014820b4000a01c40d103c0b41101400c0c02d6048003040700c00d00d801840154100e18208034100103c1c19400305000100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 761191079 1250 761189829 761189839
    0x2091c030203161401141509010515090114030a0204060906020a02150904200a08010f0e0f280c030b0429120a050c0321031512030a02010b131e0b 64
    0x40c40e5050342500751146c500d4030801d034000070002c005000c15008070200c036004091f21001d115604010100d0b01040407011024490300303020440c0c1d0000d80c4074200d195040245c0c01600760320380c00e010420002070f410500841000c210313051004200700e4400079001c6125a00140b03038084000707000700e41001a178000c5488a070800d881c0e0311001440310042c0f40704000c6103055018a980d4070040d1500401c110300c10303001002025510038003005100f503c65241c40c0c00444984078269151a926650860060980702c1c21409001c404286401409540d01c100a015000d8605100c241680400c05c000c550740310341c0e80ca03408805c800e034080d007125105945194040d40038190354041d07001c00342c041d0320b000c01c50031086071070780d1010104003501c0c01c00b031001d00ea080142d13000b041000050f0601192080c0801042075104141c0343c0342000680c6d0343c0c422a100d580303501c84183ca42d41c0000420003400303480141940790152002c1c038010408500d03030b842902c0140340c51220118026000000040c003601000b00e41d15444 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 761192329 1250 761191079 761191103
    0x601031b0305101a0414060405090705030901092012010b0d0311071e18050f0a020903070f0b0d05130f021c06020d0b0108060d020a09090206070605040602091c03020316 74
    0x1c800b044c2c40d60031340290076205481e00d803450035400c0500d019018044034010041480704000548620100982004070b0b8145103440703030798080b8014010644d09030f000c0d050003250001003821007d182c0e40d0344e40c441800d84070340001d0b805400d9000d003a0741c0b605404580085901540e10301007842210354120140c031100540740002d03501c80490880341206a003002d940310380c80380c041045990302c1c1551044504c0030303c001d2000d45404983c1030172145d0014460f031b0b0040d40005d0034003041c0d5410721995000e404180c007001205d5440721407942141d000340d506002204d01e030074007088200110450012402c0e501262104070060309a080c05502c3c00080b007005c006200d10960100000e00da8000752102d203503010000107413030308000001480350201800a9024001038001c90340542c4901c03c0720400d440308040c0c0030400c1e00c81440031401d2441121000740c03605203000c06020400000750000c01c2040e40c110f503610000030384900c0202c0081d0712440b0041c0580d1081010815800c0c42020002100703001d07284070149 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 761193579 1250 761192329 761192339
    0x503061617160f030e060a24060f030b01020604020a030303020f0f0c0a0c121106030705211e010e1906080a0b01180204120605090c130b03060601031b030510 69
    0x2a07010103036480710b54040d4041003005040d51000303e1078543c085034601484001200b00c0745036118003000e00014540e81d1116905481c94549031f1325409140014409130380356541d0748400500d85c1c0340600034040020304190310015207610001c2c0e00c031f000c0c0c0e03001050340e07118500d198ec0a80c002c1d0300004003032206070340900030035078025a00c50281880f15111001740481f05c4061400316032040454101d081c5140100f440360700455443d95461a0080d804d030340341940c0b520f450030f05850070301840d20100c442d4201d52050500301e00c0340c0710106016200001c0b07075210000c4050304c600f6035000701b4081c0c081c0c030b1241080000c0701e040d84880c0040c100103202000007602c070340700d44441d400c009808600b074030b034403014000410240e050b0082001c08000010011400c0c2410036240302150b51481e440507140380c0c3c0391070101b60032541c1400501321140004194601c501ca440e0210741c041c2240884042c03086c0656000507109500a02a02d03c0d054005001c01100c4266000250f00420018103480c685074000310020030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 761194829 1250 761193579 761193617
    0x41e0b1609050a140a0e091020040303110706020606060a030929040b0c0f0405040207060b09011502070e072c0627060403170d020f0315040f0605030616 67
    0x405014000c0781c41981d10540030911115a142e6400446e60724422001c100100b0004500700c81e07408014000450340d03009806441c0289115201480004203001800004064000c525407186030014400d45200655800d02607882e01c2c4121600340c1c000004001e185003c1e482a0302c0703818164814402d0405410802c0a000c5551010b06000d1342030a01002c140f01c03d01140b40c00b0725030301006040c4000d00d442d443c503041c04003d00035841035501440d00421385200b009402d4000030035241001d414501d4030341c3e44802c00d01c1070210080c04a00035000d000b10208024a0b0641950f00c00c45490f04d4001c0d026500e11400041071441d0101a100e55880740c10400c40c0c0d58440c0000c7ca88505040c8a2090b440010b00703100c075034034900c0c10045200d401c1c101301c2000040d494040c030f00c02c0e01491030003250722607170503a0450000c0e00c03c0f82180c96085000008016100e401d030070360101121300c1034074108102e03404e1002420440d0894000d055255020000081d08419408001400740c5c200d8900110310021a0361544 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 761196079 1250 761194829 761194849
    0xf0602072102012d0e13051009020d1d010902010807090b09060c01090b1503070e011a1c0c08100611100e010902090103111f0503010e0726041e0b160905 67
    0x150600b01c21034481c0346c11050341c00d540241076810021030501c44c000c0955000c89110b1401c20715008108201c4001b8285d0014000e40b64441501c44881d825a520354000d0204900c12030101e248100492006440780d4038500079910510201d074070702801001003200d140c20818658019649a04500f40090308101280340101c500c07400c08010100c1c1a402c040c24184182c2041c10450025001007100e00780030142018080d0448000a640d414140701000017141c8401e240e40440b8103101001c00c00c5540a1409031192030449044a40301d03854241c21209560951800802035120010101804a46500c003c0000c0039030301c000a60032140340d011038140c1409a20958407031200c500398000c03900f052618404e02d4030040d0040c0c2c1025140120140140c0018020f031b040090b946000682680d0040e0460128404c426001c00003c41416603030050303507002110120380c4910500418140305030308500d8920320503031259889010342e660242103002c0805001d048005c01007841400911520342c9130002d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 761197329 1250 761196079 761196167
    0x302130305031b0d030e0303130303060b030f0108010614060910120609150504180b040c050901170705010912110409080301030308010305010e06010609120501090c0f060207210201 79
    0x16409900c0804400c0d0600039403200c1c4c0001d040c14980205800714010041302e40c48800b407000d0613902071041c2000c0b8010812900824103a03040002400450656442094100e6003280d00a00c441500e800124000c40e07101442150040f005020509140c0740185184031074446a2404644400c1069034220640380d4952000003000d603580c43e001ca0485490b40f0b00c001809050b20103100b000821100a02c104841c0c0001411401023500400c00300700b6036120200003000003e00c190b00700e5854400b00ca000d0030000c03a540c06548128200050301c0d500500c0c1c101e04580c03081000301001d00c05601c4041008001c10400c1d83d2041c0c0d81c40c0c130f45000034010000b560185000390b540010542c11882c1641c21159400b13044199540010010072681d90310032201000d40300d50307480d004560005450900e001d024031882c024503640450b080492201c500c00a5a022103c096080f107042959032000080c0d8004059000b00c1e40c3d5407c101c601b009035025030300c25900e40303080308101070300202c40d101080c101f0750b8503c003e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 761198579 1250 761197329 761197357
    0x12030c080a0e150c061632070809010f090b030a110c0a140610030b0703020c010e0a06150501090308030c0f0408120711030c0901030b060d0203060f1e0c040501030213030503 76
    0x52410b08000c10030645d64050210020b0541117082c0307038030152100c14401c0c2e0000805001c110030480c041c440b1f9558440e45001450003a880720781902d04594184c00c607986260019040e00c0402c81d00c0d902c40d01404040320551801a8590344400349148082d16a6542d10440340a04104800d48540b042000c24040c034002c3d03465039007007100010541e04081014100125000d8072407400c0c0082950440340caa04051641001030ba01e680e1154101d01500110030348003c0c5004d10710702d84081c400e054000a43e8401c1c0070309000031181d151801912520114080074000c4942030000070400b035100c80c02420300212194078542032603aa00099440d1003500410740341951130100b01d180410480000703078422410304a0240620721010b82c04101c158005100252031040e88801060881e1294840d81140b150090b007078412f245005c480e001441401038450060400038051020b186441c0d42c0c03070590080311a10b807403074903040c60000114041e400440d12414200c002c46400400504200000c001c9000c46c0d642c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 761199829 1250 761198579 761198587
    0xe121902041d300f090d0f06050411150c071202061902100b040606020a020411040f1413050702060711030d051f0b0901050403140111041d0112030c080a0e15 69
    0x34080f103a4200d01003010640c60040c080a220b4022110603160080015101c1c101251128240101d010070b41d0000035113a98030340030a1105008940b120b000403000103640c2c8003c030b04102502c50610340704000200e003a94000840c20700c1501062100450000d0009010a0400c0c1006103da8484000c0310080d5016a00403904040d01540c00e00801e00c03520001c03038003040310900d89071003e134131350203030500092080340c0d01c2c9a01e00660480605450140a1400c113042d0100d131610f11a1004404282c00d091045180985603000c10900d4043e40b40301e0001640944180d0321600700649100340c0603510548640014003102c03128100038410075218a0140e011071083c2e044880c941c100c865583c0d0420841200d082005800b1031340c20004607000c50754400203104040c0c100700707402c90041c0310f0114070002d07100000400240c140040c00758a1800000035013492071603607035281c0a01c08501036050050110701c5d810182d20205003903c0113010381d034820b4208843c103120406c0c0010000f203100100341c500704101007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 761201079 1250 761199829 761199883
    0x40e0c03091506060d0209240904060b0c070b030c0708210a0e03042106020301260a050709090206090d2f03071406070b01060e121902041d 61
    0x300842c422003030540c4410781c00c03c4000300f509481013203200c04c0010b0b00041d44c0d080a807600690251440b0040b2034143c00a134000d001d510041d030001105512903030409001080c2c084464007180c0c9502001c1d0020862646030113034951407604002c008004d4074405120350300110f202080101104041c2044001d5404039203511180c1010010301001d1380289061b1603940406030020882d03040d1481011082138409007894103d4100303400690080c01c241c00440002003c0440604010626101d0030010300c1102882c41203ea0b070f0071440c40e01820545c0640343c01c00560901da4091a0010b0010f00351a1034030b1f00744404611800a1818129107110140c114080b01015160710b46040c103010711103802c3da0240c0080000ea441d032850085104404041160035903e030796020499005607444483e00140c1d41c0d4881028095170f059100b450300a030003c2020600c880c101140000d800c141c03110307050428280d01e0b001e10000f051042201401301c04522000f51800d0b00c00c000031031004034000c00d450700c000403034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 761202329 1250 761201079 761201083
    0x13020c0c0406090218120a14030309071a070b06060c031305030c01030218190f120501060b0304050d120e150a06050901030b07030c030b0a06030e011a06120408040e0c0309 75
    0x350f803100102900c140810031403024800200d8500c04400c8401249441e00d0625443c240038110034002d1107220a00310301e01c0c0b0407001001071071140614000341c480c1581e941a00c080701c00e104c1c0200103400c0380100310043c0000d00e450100340d00540c01610117814116440031051860b0311481c1c80e04415010300c40100000e10b0304000aa098540070320f029401d1044450008007071421007480c861140811071501301d00380c0b0329401da80d0010700920494642c51680c5100030b0740292200b5005036000d50030414007142128a03842140c1c02258040300506511990004c200c03202000400d0b60902680c4540781e410b0300740020400811240440040c403043c606050b0401c1040f50b00c13981c05640074003c24001000469003071480207500c085541400700e0703220040b000450040846032a017a80c001408600883c2d0070398183c0c082030144448000800800ca00b640c0c0f0801c0c8107641c41845a40a0010800640304071801b00d42c05c2d030170505c10400e140c1419140e903d0342c144201c040300c1c0d0101100300841000b002c2d10f02 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 761203579 1250 761202329 761202341
    0xc0506061e04020c0c1908060a090b0c0901090515091309170319110405011d0f0f060408070303050702090114100c0f0c0303020303100e060d030e13020c0c04 69
    0x4100d0394805002145140160850801d4201d244a20b50100d0503002d00c14050001c4021074074018052440129010121030b0402640e0041030318a100b4440024400001da1080b2880d01d9084440c3c1d0f0490740c0c0b50034812a26510094401d410032240400000f03560b100c184d40c1d07141030071b05564402c0e246d589a6042c089540504000d8103241810000d0354008510328841c07100034001c100c11815500c0c2d4400460b42c50410f082a28500010302e84510210300066440242003a0f55090b641c00d040303c1d01440540c5580304003005200e900c13040c0805000c401d454000541400c0c04806007007941010360710710b00d09007040b40950003030780424400904442103181003448180940088001d2074840385105000c240e04403a5650040d00b07000f200c034580c000b44452240c041c0c0c045540070308694a82900c0f8a0002e480750402d844c520801000000080385002610a03814030842020304a200c411200782c03021101c00311800c1100c0c0d00150184500300e1011014001072461028060040104d4200c1105000440760 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 761204829 1250 761203579 761203591
    0x42d0c030e0109080a0804020117040515180c010810030b100317041505090604270c1706040c110307060b0a05060f071202100c02060103050613050604030f021c0c0506 73
    0x450003403440300040348607050b1207603031103d89041b40f26a41d031403006a6402c2c1d410059004000702d07034000c200070094001401c2040c5118101c5440154586132603086407a04d041d41a2031564004c88088000c65105071031342c42c2c1c441c0c1d00152240882c2d56a0701c03101c0c20000269031281d40440c0c0560248148000d0303503207094142e110048094a068a811089030a00302c10401031010400002140c001c26902c000031f40700a4400c01a846650788440303110400842d4a2101081c0a5030500240c0002c2a0040100040d0b00369400065034503540c41808000080c005500702e02c05100799054545940b08003000a0716040380f0030030b000180c444501c3c0810028100c690702c101d205500c204011081041030005035407800b944803058000740403528500340c1c10404200c2c00795100c02d140039801150658000b0701c0381d040341e008500f80d503100c2d112480108001010980e01902d680e020002040c002403040b040c00310103100074410b580d41c000080409614070003081818900150b40103441006200c024040c458000c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 761206079 1250 761204829 761204831
    0xc0a09151508010b030408070213050f090c0f1912051006080c13090f05030d240608070f09030b13060f09150207030c0c09090b0114030c042d0c030e01 66
    0xa803220300528800d01409030300132400b4080701141c1040083d0b4261026554024800078228158010440007040100c0300c0c0c0282100540204150010210303840c01519006400d407840c40c50000140304002101d90021103030400e0030000055141015040360a040c0e119802030841c2808414107181603500782e410a190a40260304856060b03525040030b03240304000b6200100b091111810100b054040108010b401c90000003040c5004500c103a00068007400e50340c2d6034002c01180520000401e95140c0549400b09036544003140b6114041c8540b1004003051b8a13102c1080e1b9226a99056505419114480e030017111200c5141003003105c1c0607020106100d407501b04800d0343c49844001d81d0840700d00f4281c030450740c0002d00e041410321899041e0701c810342201d02d0070201e5640d4010540140341508094606030341c001c002180605401c650744050940081c001c004000265040000030701840d107400d207508801202d03480d901240010ba50340c1001c4528000101d040d490340014003556078141c05d002842e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 761207329 1250 761206079 761206109
    0x912070801240509040f03120606050c0f0304050901121b06030504061803120c350c0f3a060806070509010212030a020705070b0310050a0b0d0e0c0a0915 67
    0x662111210b40340d000350400c80310a106c06144c00c00381d504030803c001648109051003c00b042240d005001030003c040514212011109011040b603140c0c0585c2c09280d521120311401001017450f40c227904105113000c0c5e0440c400000f0214036040112082c1e0340400c0109448104100c14404903200f00d11441c46028000b2500c0030469400929599440204030221584d070f8640c030642c20720900b412a504e080051180c082c5403600303803c02c0b011007940001c02c601d40c01024000b884441c50101903031424142131001a09010f01c1110380b00b820445401c8004d40365611206058802c941d081c0c602c0b4000c005900300103410b40c2040d03c1c1c1400c000d0010050002d01004100301801c59034000307842801100086034050710f94a903080b041c1c019224010002c0d140344180361010515440d0000114021143c900104009594820074401c0d00c20320b511420351b1004007403129000c54200d98100e000003c2662007039030075191140c0001484032075550803030f504051750354a03600541e03004d19032110003a0161002d84104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 761208579 1250 761207329 761207339
    0x50325090c1211040f0602060f0a0213060c02040207080703030e070b031b03040c03050a21030c0c080c010b13090201091d070c03111219030b01020c0402091207080124 73
    0x1182c0b1a06180d00020703640320040031094001d40f0076980981342884c49032060f00e81e540e8001b541c41c4826a400c0100500020119a104189200b162942c0300e0f86a1100301043c81c101c2d040d200d41ca0440010307a040768080101600040c0c01c0030080c03c0152294800040000400040518001c0180c008004e40c0001b001444905a070980c0c0b501007000e0f00c110325594030b9a0300c1c68030729040d003081da000801741e02c513508410040000407008041c0040b2900c40000c081c0800140440540301c1080400000c10540c1e102c50303001c40e500f9002880e800000d0030000c10141c1242002c81c2c400d0301c0803040d20404941d21401c4008640c1d2000c003c00c01800d801080c0c0c040750024000340518050040c01460030300400407180c07002c040c010b0025052600020058800e10341807030202c84001d5026881204032401540d4001038114000c2c0b10301b0156241c11313030040c51031558503803d00c40258000e00200d03510030800e506c1c104030200b0402a01c2c003c3c14102001040407903040c268211803052150701e8144c0c840c010841440 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 761209829 1250 761208579 761208587
    0xc0309140a23010b09151c020609130e0f07050a0f1d071e0206060a0e0f2a0c0a052b030507031d0d0807050406050315040204050325090c 60
    0x880b9010030301c1454180d40280881d28014856a005070750001007120800440702203079100c203580400240e940403114201d010000791168200c41c4000e40c0060148951003507801c1a0b07101d01480b050941c0c0004640c80f04144003481d000417984180c0c40c80c1d029030414001402c009071020010900c02d100801035906040c0c500c050354500807a0301c0d03549010b1000299240c0e1292009801120144a00c2c01410035600f00003900ca8108660507030059001410008100b030841105900c26001c0e40c0c9072102a84520b80e2000d4400400c04031511045d29441b12110047c0b1180c0c0100000d910401c01401c80d6801440d025080c84020039141c1c604144001481d003500711226044100141c1c54580043c1a907100e4906078000c1a41a02c0d00e030b88503004000040b90307210f000170710040440d00754482d0314490340c071200100d82c0e81c0316030702811001034014004a0205030703405400c500340340d00052000d4200f0380c0b01e202092400070982103140d4480d424210944084009000c0000a41400717801400708901c1e5041c064 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 761211079 1250 761209829 761209853
    0x30f02070503121e04141908060402010e01021e1605030c010c0b0606040306091410180b27060a0507090506030705130f1d1e0f0c0c010c0309140a 64
    0x110800d50005500541e41c2d50024140000b09442983c860303c8030340b101c84000d041001108413034007450650500d40d1024181c1f14846003158508001006165640d0b801110080c0c503000c1901e0551040e1a12540030311040380c864241c21404e03e00504c1240340741d2b10540304c020b5013a4042030190700300c0c0f0104000c1ea41d21080e050402a00540e00c801d01d80c03202c50124a0511407503002074036040c54001c0340410081042c1489195200710070031145c25406032408032089030802e4890b0b0907032801e0056290001841600c00c03590110946107650b00100c01c032458030703005000f840c0a00a66802840801c980c04546108607500841d044c54400d804500341070104030b562001415013030a202d4046036003c2c130001c50003480b03000b411000300765052a640d60490b419082c1c110710340074843c0020340d100003003071004202d40e500300040000c40443e1180e1034842130020040d00c00303040c46604000400c40c40b0480307402401484810045560002100f00c941e091440c06181c20124410b155004006201e012450101821b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 761212329 1250 761211079 761211103
    0x60c0c1c0512070309050603160e10051b0705060c01050103050d08190b03010e0d0504060e040e0606010e060721140a02060a0203090705030f060609010b03070807050306040f051003030f02070503 85
    0xb00c1d030b46440505040c1c0340519a0352215038070050010400c1060032400c1480c0c40c4401c03140d20b40880c002c18840400c22460100001500051400e000060140001124410340228208256038000d9141c1000ca00150f12081c00c0c660581e4444004004000c2d042003042c50342403003480c200c10300d410241e44407a049408800104101501c036030945070f41e42c3e403c0d07000c005820460400c40d07541054140010b07101e508a407003800c001c14203089400c3c0300d508041c02480d00f0408000040c04280d501d417001521090250202d00e60042414000c110029046451a400ca90b003030071108410004c038000014003400702600d032001205028080c030244240c000a0b0790350880c0c41000301680380c0e51060b0410780f40c4000380d4401ca40c07500c640f03809900500b5011449500400c4244c1d24200c480c0e0f2030b5010040a4071041d101c800000c0c0c46107001400081c0704001441c0c1046d4020300c08560300158000003803d946003550386003441c4c9400242003040640181d0f522551745c2d007a0000d01900c0d85030000080d104d070522501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 761213579 1250 761212329 761212363
    0x3042102031c051803120f0106020123090a080301030602040e010506190e01110318030d0e0d1203060905011805090d0c080304140102030106020703110307141e060c0c1c05 75
    0x702d132461142003030b41300c01c2c5090310007125102e121591503080310640030703031300c0a00c18105000081162841805428031229013640d002000000104030a490200020207403145c1f030080611200c0010002e10003180294003d400160700d4508100c00510382d208103901c0540f08400820914410194102c800a165074050528012240000005850003a90700c8005002c80c00700241d070881f1280a03010203d07d4400540c100e410004011205032845058401b0b5290301c5403200664100140c07000100c6001d00c0400c0c0b07004183d15a607400341c0b2003654800e130080b95903203070101c3c401d0306510140d203c0c0381c1c1e1000c0300c5c40007001954240780d401740081c903d00700003a0070b4101c000b000030280001d03000113044480481c4000c654035a0f442d440292240014002210000b0004402004601d0000344c06815183c1c55000e12060b01c00c60800c1040181c0d04010f004103c9901c1500d02ca81a03031008007134080c00c05d600010346400850b01c000c00440911030303105900080078034900c54002c80c0307001600340300340c26107520 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 761214829 1250 761213579 761213581
    0x110f070f08070504090c0504090c0b0f040e0606070305190311070c0602011406090105011b05030730120c030902040c030b13180206090d0b0915251404090203042102031c05 75
    0x3c09010744180341d02f10326400d40e00003820003d4500703014018421120103040401c156107901041042c14812080090700050041c400d1203000c0090b0f201000b03080070b89003070000c0c03003100852080075039401c00c15003600d69008070350341088035a40a0081000300c1101e60302c051000d20b0a600080c000000601030181003203034000c90500c0d040720760b80c581441b0b5074122049903114002485e140641c0d0107881d000021900008410200c000703005440040c1d26401c0c2e8a804180c08074000808000b881d00c400c01d1420541c03141287c0303000d6142c034410030014a000344c1e00801c0d1907402c803040c40300e07000c041d1000f408020f00c0e04201c8520b584800e1240c2d0f0543e94121419580c07415000c0010711075032031003400a800d5426110511460760000140180ba011500700d24407100e60390600d9410480090044040150050052060001d44100150300c00703490841c0c051424103032600a0507040740c20440b0102e0310084080d00035424041c0b85079401089100900c0114601000c20314040070f24020840c01451481d2100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 761216079 1250 761214829 761214833
    0x140307090b0403050a2303090d0c090912030605062d04030b0709031106030f061201200d0605030a12030b06091e04050108120a110f070f08070504090c050409 69
    0x90610010001288081c0c1c030b4039100c0c1881c584130700c00140f00300c1d01d0b06014508103a4941c00030041000301805103005e1403d0503030765010300c0307602143c580d8126850040400080b440311028824502103c0c081c00c0f0401c001d41601d2400380407079181d9080248508801c0c00020940d04850038100c1c0444000858040c1140704407a10f41e9044c091508001d128030384150402191a034801c0400d4100c9010b03040441c40211002c0c103100040c48280c0e4070b041c0c3c420004001070f0080c104120042410b65100c0b0002031400c01d03048800c09414050301c0d1100c1c9a4100290070030700c200c1e00e40105405480c2c110b000d003038461515a02c000841d0503611840040c1034403a031088550b50b4a4405480020340064000803040ca80300a2016400b0040720409204034500000452a02000140b06036044411505a440c054414a05030745040c0c2c64003e4500c0b511038042e00c550320050600001e401000491614200b00b420146010f040c43c51035000180501e103030045800110302c9001e80e4508030340d01a03600107805c0b00a8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 761217329 1250 761216079 761216087
    0x140906070611160f05010501090908030106050901120c0f0e0306160c05100f022805041a07020a0f05030721020616052b0c0b0f1f03050703060605010206040201140307 73
    0x20108100000182007059000d008140f0b1101020501c11750080100742e0f2290304101c22100c6103d405007810070180010300000e40a0801860f0303600301410100c240b80425405c0c4416107488117202400103800c098a545c20075003084100800b0981280071305142d01d0107906501e00c4901200c0314408110b0024150420302c03a041c0100d06807480f0000e020b0142074000f5001d40080d41c4130400c81c40c0b590381403402c801c4071008025580b00071189240e0b50580780500c3d282840030003205903914400d020004212160041c2c0c1d030b034a8840010000d070b1120003600740c80c0804050401c00254056000c060145d003251040081d00c132075560545504132801e58881c5114035641c440d42452a2004065114265110340da07110541908040010310526400da03e5034540801c41d01c402008400402d6004c80002241da0720086000c41540042081c20740124204988800050443d0a900544603a00000030030b105005640c060b00b00a4134003030005200d01d003000d50000786135184030b04160b940010040049010a846 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 761218579 1250 761217329 761217337
    0x1911040e0405010621050a061a0603040b0f13030e090a14071119020a0b0d020705030a0c0b011401080604090c08010f02180306240105090d0b07140906070611 69
    0x10040d210039500d02407424600812040c02164000450340c410800c00d4140001ca0301d440980c0030000c0c2002c0d200301ea0321a4013400700c00e9914646d5881d01c3c0b1100001d511400050340c4074500850380ca52003410490400030b829400a000c00089100a44250021175007005042461200c192480c10b401d42c0d65144d82c45c006c101103101141d0f83c2c080c40062111036544500c84400030b0032480d003651980004484009802120008029003003103115504000000440000c0c0c86030901500c005440d02205503a0907080d0351141d642d49000c500710000000034044c0000c02680508602d055414143e0820740010700400c800070070340d900ca26181d03141041000380751b4891800500614009000c10386c0c4400799175020f500000b9002560781c40707d00034070301030749800a03817580200590718a1201204408001200c20086001650305114042151014640b0b40240c0c0a20460050301280309a04001900400c20f08600d00c8540401500703000c0b200300d40d580c41080f505556030207800001c0c080071041d501d20a81c05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 761219829 1250 761218579 761218589
    0x90602030f0603100e25030f0312050915040f020a03052d0102040501080105062811010c0809060a0b0307080a0b07140f1c0b040501080d0f0206191104 66
    0x10021040c00441e68020a8603801035008509841d030910356042024100d030040031894580ba40304241c40c100c011300055080f4a50740d9050510090103489848524a120003038000300d001441240242c1102000c5216240e005028240a0b0905507507400c02c068501d170300548003519444a280d0b0380411075075080d000030000d5900006858004492075411440c403112500401e861117441220345502c06410300c01c40d010741e84144c4681200380d00789414003030203030000c2140759951800254400d51446580490394010a002d64075070042c0085402c555080d62007800084041c000154144070401c0742c041b076441c2e84114940d5000540c074140000092a00d81554402c15050080c0f20110040c01012116640315610945600c6400301e0f0f20000c841040c803584400c4601c03081d0a00c048040c56902d1510300100488403407011030307541a61800030b004c4072000e9000d800f02d648010014001c01b03401200d20085604540040c140070314180211904000320a0b480560055482c640140c4085600381540c0c0505 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 761221079 1250 761219829 761219831
    0x152220030706030506191203082a0426060403050903031209010506280b030a1103070e1e060301090c0c1b0f15051207030b040f0911040509030f030a0906 67
    0x82d694240c082e0050800b51441c9006200080f14a02d008682d10a4101154402c00e5102e40002041e1000c5501460140c5040c01012220f05c50400c29100916104035a50102d102a07035941e160910020864200324200c41d601214010603c00c4102d0100d196584607405007001c0f81e81b50b800b240084e04500c1000c2d0314001103032031803050000300441580300500c18a01991140e60648110420021082460002c491581030340072080c00024a104041c5030001c3c4240c0303021441c00800702581da07198001711041400a03c0c00d0320310410500c0c1c6039088219008050340681c6829040e00041415844140140f0044c5522210381280c82c3c3d104030299182c140d044040402168019841d02c0f0907041a403107450010301c540500400c040040307940d00707940364007241c84892903c98494554483d505000300604241951181c40904544880c0a59021403802c0300d8001156140c0f880e21510110303c5c14500c074000c0b4907200070071540d600004216a01d00280c80c09042d200d50311240048090f03c21010018180d07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 761222329 1250 761221079 761221093
    0x30612030d0e0a0605060316060f030b0a140a0b09060405010c0f0203070e10240309060e060901090b010b0436021204110904110d051e15222003 63
    0x1c441c000ca81d028600d4401c030400d02840c6c03034900030136548043c6021000d41c00000c01004001250241681080008550501050f062203800025541401c0d81d0b004080b10707901c04282d40038601d80401090040e20307404c007855061694640103d0403030f0007940203e505009030b0810b403000f40315414480c07994880c0d00504803002940c6507001e2090700c003000d0300c1d602c00201700b40e403001c03407003807200d5001c0724450880d644121080355000314100c014009d040340a840e225503d904e4101c007820103200092141c03c0003400810102214a000740f06800142e10917100c5030801d0000703020f5020302004c90348199588603070111211801c0c600c082140020b084001122902c0040c00824104400b400540300c1d038002d140c03850000f60f030b800a1184c0d994044400800c1d1030740e48640320b007582c506171502c02101800384045400140306e4070000305075807219000c58082603005200c01d03d000201103115640c00b410401044079041d4005031401000a900b0b4030003403828101a00c0112101d041c0c02c0d422021002c0101154a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 761223579 1250 761222329 761222351
    0x5010e0706020c19050d0b0a0207051c1106010e1b1204030c0606060806010816020705120705121606201005092109040c0509030f01050f0a11030612030d 67
    0x184070740481c1c9560252008006403042a913804a041c41160009040e02d400c2d4601547c3e56007500400a00e1500c0c070307540c00d00241c1d02290081282070240e419000c4680300003802c0c104060300110f08010000099444400180112841c0219280d00700000c809200d44e158400340368441c40d0301170340b0710f0501410340030001c02c810b055000344120446030149508100d12502c0e50003c45008c40d00b1204c1a001c15840008104d0160a50038001c10844041c411384070a261140000750303d06104060000c00d9a01240091040d0300c2d0070300c800000646120000d10481202c0b0f10f140c0105150343c403a40040c00441100f4045008a00110400d020000002e8a0074080911303404c4c8010310b030a440142c40752280452900700c0c030310f1090300030840040300b0800c503060a10398003c01020303107900d845003010400b0500c0070311341c280c40c108074000c26511108004501450049028812000d00601d0700000134101300c8002039020034101100e030401780c1607461528401d01000c00c1842c0d4030800b11450340c131074600450014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 761224829 1250 761223579 761223583
    0xf0412050a12030c020a020114040801060b0c1603030c1b050a030f0308060a05030c040f0609021b1b0906010c0c031b0515130b07030318150c0801060f050705010e070602 74
    0x418402c12041040880d0507100710f0032110409181030142e40011400706c0958040e480b18558082c178002c040746003944440301c007400d4410503400b1401c050804984010032040922150304400c02c0542d00000080ca180c41c010283c14080c40040c0c0511252090301540c1401aa9450041c20b80502280c00659580c54010303420742d00c8103016000261520301085152a141c43e1241c1102c600078002c10ba00244101040300800c0303101800301c0030071741c1c80d180042c101d4454009064a101001d02010440d00110411411700c140000400c40501c1c1c0405002829640c0091080d00904207181218040b50145031410450480e900094208425050000c000d19075550750541908c5050740c1c0d80160354681c3d1198111801802c0c2008041d6652080c1070209900030405405120301070729010409801881d034103c0b440d004044141c80c004143e01d58800c16003801d000e080e41e81d031200c0c68060201d61403e04000e045074049201704041010020307080c070500109400c50310b5503122030010340360010360f2002c1c069 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 761226079 1250 761224829 761224843
    0x1b0705150a02010f0b091f090c03060303090906050d08030c280e0102031204120c080a030218011815022508060105030619111b010902130c140f041205 66
    0x1d4019070a20a01c075891032050301614101c00300c080c00000d5030740c48029500c201485122a0b00894900b0900c0c0014140c0d01d502804a00a4032520000746560031405c00504c102140d8000c600901d0a11500304010740703501d41c0c1c48403081d030440c80c920348031384070180007090501c20620160080c07a52a8520710704a5400c001c0810340011035202c02541074840401680c40c0d0042d05000c40140103000b0024000c6087e607144003040c0704084c42c02080151440d41c4040740c1d60095200c46000942c080b40c641e01d8800c140050002e00c0c071090900d901c00410602050011030014000c05d0462100b407400c10322002d0027017000d4520381f03000030244410b55030000c0c1c0c6103010202074424945036200301400000c990502268003400303a14090a001d10b842c910542200140c2626240041e8488040056150080b00122010700c4141503e0000c144540c543c0100003101c1e40c4613100d01c01c11890300054411254001140011911380400f200d0789071603240d081c50750540500d50046c49007500680c1e84c4001c001c004501c0c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 761227329 1250 761226079 761226097
    0x110303010b0d0b06182718070305060403050307020610030f1101120f050402031b03030301090c12050403050a410d110d27020609030f030c010603150e031b070515 71
    0xc02002c20b40e41300c5001000035846104511503c1b11001c0760b0100c038100a1030003034400100449401c940c1e0780d5286450490300301e5003a4006603000c4140030460354148846a00200038003803030901141192124004c0603e400802016000010202c0b1120303405140360032a188a000010030040c4041c40d401406040122012442805a00440c03100f16200d00003540d000140034000b1800d6a090a04860040404111600a00952000b81c2c0c0c070440140c09114401c2d80720b0354a8075140c09120700701400700b9a05003644074061007001c0e951290b045100c8111300b024031024410081c011000400d40d105d9118802c0c13210751207402c0080c4148050806c500401565184401c1080060081c1e01c007000001440c0b0000032800310078158602c050310b020000b90000c0d1000a05459000c50750f405520300d568080c1c0d0100000e0703512540300700107100740c030716841e9000e02c00d0400030300006104c0729529850381b01e031040c2695400c4800f074800002050800c820b0b405004050701c1d1051319103400d00e2512141d0801512 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 761228579 1250 761227329 761227339
    0xf021002220e040c1e051c0308090f0303390301150908060711010f2f12060108130501020d0921140a0c1a04060c110303010b0d0b0618 59
    0x2411008a503103192056801401c0e4410280c20280c3c40381504600c44a40d810114403004041095900c5587c3c03544505078100201820751010720703010300646030080000b4a290003400c1c00e0f420180012007125400f40e040d0072801e8000c03420000700b0386100c3c4809101e4122403030380143e41c0c1d0724420010041d0b0607a224014a0b11400c0c02a990403a07044a5134040c1c403603a0b41061000c9a021806064003d41552405c0004560039600e54400c0040384c0024050101d4007108008480040c41c01481c8042d1251282c003590740b9091074581a070402100203050b403410000700c1800290350113141600405076903407200095603240c0c02c0354141d00140c40c0c14007042c3d51110750402a13414054400c0100c6040400c0e54403908101204e4101902140d08651603d6041c00301b00d1900000040c420b606051070401d036141034014a04260500341e044900204890782480800f02c42070700d018500100b503904440b10008044d503903643e284283c8002d0000507208075008000031074485100301220480540c42c000a5078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 761229829 1250 761228579 761228647
    0x10e120301060216080d0c1a04050703030909111b0a020907031406040e1c030608150411010c20061e18040b060d0b0612011526070f021002 61
    0x1e084c160340c40c07070b00c40d40125600c142c564400503070280305419107040c01252a400400c41c08401d001880000321400c445540081c40700340304243d0401020f0000e0580321a0402c464880201d881c00c084c03190706000c51b00c1c1500340e03411010300c280420541c55003541c0030f000280380303044c0810040c01501700005600b0880c2c01c0900016400c0c240b9115010182820b8401807440303188207040034000c0b80d80322054004060b2a4000031408903000c11110344060891101c20f0326a150a0800b0801d0090401c1481d0400c50074030700030f034040744261101c0c120701c154a81182030900d01410000b00d580c400c2d2103c0c2500c01800c1c03a4800000c4076000040c000800040f1001300c59001c0364000c200440c0c0b241c900c1140c2c01030050200200c4008103510031314011201621481c0317020003400c6a805450400d900c01005101c80f82d14150030300e40d1180700840900c244240c82c03e410540c882030381188510081c00344003081003160540948510810002c0000c8603031403002c5503581c00c4402c0d219000d812010b82c542120003044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 761231079 1250 761229829 761229853
    0x8090706050a17090708030f0d1107081c15091428020a110604060903090e070530010b030106030e07052407243b010e1203010602 57
    0x1811924816420b58030840003c1900c10f800002c2e001c050203c004d580300e40c1c1000300700000c04100903c406803080c20070544450342c3c4141002a00c0041800070007280c000e010110000d01001c054a5509074041d2024000003a0780f160b0070001c045003024140c40c1101d0f4400011904280e0b80b1600c00020710480c07401450340d84003580c4002d4034441c8000480082c580c0d9000c041c030117169015100202c05c0d890000320003402e05292500d4180240d4042e580e040c1d95440781800c042e000f4000360001e10706e400d1b4000c807500d00040003901a02035204d440100741414400072003000360641100c20f0480402840107550f507100c421102868109000d600c010a280200c00d00710220002000d10840300010041e13a0a490404075242c0041c0c41041c0c00c04c1c0e480300a202490020380f940e001e00e00303400c03500e680c402005164407069078155922a110a907503054100710382c28101c10400c60306000ba400d0101081f441c014040d40450046c04030b003041c20b02c907000380c00400d000d504a000c010f5040328981d90888944001d11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 761232329 1250 761231079 761231087
    0x1090504031e09051c06020309061f0b0702150d02180f1912020d050f0f01201e040b0705030d0506040c0c12051905120108160902030405011b08090706 66
    0x25102c10004a8000b000400c11850800c0001d85011059541070b000141c541d41d0f12001e9802c1a50950302980000d001c0280f4440c00f80071070b481d1442c103010b2001c9a14501100039200e44903614010303001e41c040d5002c0010000790042280d440844400c4115540ca410122640071082c0080490f032050038081d1002c0004d1910301170b4083c000740d203d040d2000b0b0034903201c4044105105c01c0402c903040300c40318807104040340b010301022081c1e8403400c4c06812160520203209003124900c3c4c5070b541c00c4003056440308822040d18800d55085c410802e5603a22401c0408290003414011070303009902d8100000f40d03070010000d0210140083c42c2d090074007840310b601c4803020031080da0854841d2030001500b1480540201e0100201e004001115040c000d140203102801c40c004c501c841e000000218100180400d00a10510b12490040c1030210290004042c10755403012080a24851b42102907000700200c4d080c08420350288103414100b01c100840076071812800340645008031000179443c015844002226030203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 761233579 1250 761232329 761232377
    0xb0f0603031e0a23092101020325020604030f0305040c080d0f120615080c070203071d090106150c020103151d13050a03120b030d03020408010f02070206040302270109050403 76
    0x111880c804e081c0301760002844082000e0500840043c0c0403000880b075280428401503004030300a000c00040c2e0341c200380001085840501c940804c5500030810800400e51213501030400312000e103030214041d12241402d4108041d144c0003c05940201c02d0050560394110b484000440d1807900e070142c040d25120360607401c85030188546024800c444598a44442c0b08003c0d00e60300150b810000b500340300c5d45070040380c5801e50700e0f0171103040041000016101030701d500d02d101e940305102c24024403849090900005042e65100820010701140e04540c1c41103a0080c0c122624880b13048881090b0150f4800b10103081004d00314210a50b016004081500d00d200344001d4801160400010040010250b4080316078841d4188005901961282011035640e070500c4074964180c403540c0d015880358100701038242159160b85091100714030401881c001601c46205680440307404461043c0c9003100c2003150061283d06046180d100c2c1d501c0000854030212940c4002c2c0102e003e96583c1c032a40b03c64003010404802 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 761234829 1250 761233579 761233637
    0x40611010605090109021e0304050705040f020307140904060914070306060801030b0705071103480d030e031f0605010924020c03030f0c15040b0f0603031e0a 69
    0x244600040c05945c103950000c000403210901e44200c0c0b0301c80540d10300215082941c084940ba001120104511320300b41c02500160b5603001011865400d0014019090f03d12210101100040104070800c00d5500d0398841c10051180e070310148003159190440749007000d411620040480d180030070100c0c8142c400d01c03529041e02c1d8411000308580c0c0702c10105840702d40003410201c5023411000500074498400b032004094070004010409088403800520055400d41640303c03651580504803861202c444440952148800a60384800c0d05c5040c3d00301203400d4035000b0902c503014868031012051401545500304000da42d110400c200f403940707a200440d62090fa5118a07581842c02551500c0c1e039005401032100b52541c640111084425501c0c042800d5410150400c4090758011038008400401401030000c80001c960542629140654403000303101c1001d40014680c0034030500207003d60b10104220752034a6210481004150900c0d0300c512060744c031603000000021014808003c1a40c40c1100040320a5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 761236079 1250 761234829 761234839
    0xc0607200102131502120d021c020708030a0605100e01030915090c060215060f06090d0501060f181103043801090b040902010e010309080412080306242a0f03040611010605 75
    0x580030040485c0650810101514527001450071a164000c242c8010401940304526464032031809803500b0045640c00e0707000c24041e403600d10041034016840708183d10401e02c24280092480c0d0f1509210101d5a8200c45030119245000d04103020b201403140100e048403e603908994440031508d40310724480070260340d15600403040c0e81030b0703825515102000d41000c0c039000d00070104000d01134695030309507001580400103a5060a4003407007040091203a0704812a01c19005201c10700040301000d40910000b000030344480c6440101405900390802c201503501098801e009650080f640f0016a000087c0f0407102c0c450701d0702c00103552608160048100d00c5405864582e0440750050040d07014190180e81110507010400020178908041011814414013400c40c158a130b00d003c400780810b00d00341405c10066140303088280c1c54001d48200840e504502c1001d1480860000e00c45442948046a601c0f50392600403010801403810001016104607540da50b12800700300d1252102a007210307000d011340c0d6001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 761237329 1250 761236079 761236087
    0x130f05090c04270e1c0e01020105010e0c090a0b0d02030708090a11151b0d080709030809060703050403020904030e040605010e2407020303190201110c060720010213150212 75
    0x3643d02c600418024169450300890502103400b500307402c019030742e4040480c103042070b20b01c910760690041411408080a000810241d414107002c2446180010640c241010000034507510b01d48421441c0c000824110001030f40f40c1c4030003d4008081d40044403420001201d020003d0300060307001901240e80e5070840742c038001490305101400703003080c14170f034040b00a10020802100c0030000700034113030488461000500700206140308000c0044101420400802030391490600202d09403408840212800700c41050b0f44400d1403070700740d810b40503c1e8406540404641c04010034540c110035024003c1c002100c04001c030070703150401921401522540243c0003000918374501e5001b45003261080036502101d113904041741940000d256a009450a0355207805850f4420001c0f502400b4482425100301d4045003040d43c0c1c10380041d91024010801410000600804041070f50084250106461038000a640c0c40019075400c80f0300c203d0368805c0c991000e0700d1142144000c0c0c408503000d100301001040c0300e490 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 761238579 1250 761237329 761237369
    0x91c021e01051e0423030d09080d0f09030c0b120106051e03040f0209010b0c06070203042403140108150a140609100506040303031a040e07060c08130f05090c04 70
    0x80b122124011a11a40b0400000c91462491807261025a83c000141e07a6468105d80c241030400302118a03100c00c0c00000a07013404480030100d204a0210b2041c41c04101c0031895100444040c2c101d9400a03080c005840310102d4400440b00040030035000c180150501a42e0341c2004464600c260220f452180c0e02c100b07202c1903c420314000a54005003d5911007060122940000e07030104001c0e803101503d62000548a0b144500a0080f242e1000c010700265041900c0d00055544100c20b0900d2000030032002c0385000c404500039401f032502c90f0004031048000c0e603100c45108c1d0b07941507a188401c165401d01c10020700c0c041407034014290000500d41514a084e2240d038140044014054103180201002040202c0ca07511004094402907000c1e6070003150480361036040c1042c12004200303040c00389050031507003004040006510300403600c484c503000b811007020b070401603c1c60050000d8005000754131003001814034031890b03542c0309803070086a1445850300d800d11410038034400d42c03180346500440f09421550b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 761239829 1250 761238579 761238607
    0x905030c0306070516060b03010c0503100909020d02010c081b251409130f030e09010e0402010f08072303040201030513150506010e03150f060d0b0105060c03091c021e0105 75
    0x445c0034070804021076404150301c006400d407000300051000080e004000c2081c031240780501d61004001183c4108070b0442d0310340218000707041000d03020741441802c441210070083c000c2d04440a100c0e429a462503591342908580f41c80c3c4140c2c40e0120b0403915407101d0b44121000340e1518904451001e5000c0c05155816800d1100c4100003c1c200c1080b5404e00c1c00c0e030f0010450840d916407003d8460741d20010400141000c1001c945010b07041841020410800c120051f40c0003040c0840701055420a040c2695907848100c480380c400121499480743c6031060720204040c50009140124400d80b001c1c40140d450b226000c180f01c030002d50140100002c04c6000f00c1c1c01102e1352005402100c1031500040c10030a40000c2440c0240742d519041ca103c0c2403004020240500000141d08110203d03008809225103464000c1e1009040c0601032284c0c000107002000454108216055042c020b440500f20500c0c400e56154181185801070380103045040c5032002c50b910846204420160503100c0b00c0c01c00c205a2103102c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 761241079 1250 761239829 761239867
    0x212091e03030a0c050d0c030c0b150a030503040f0e04080406050a03140c0d110903030403030810051f0f030b100e010e09091b06040f1707150905030c03060705 70
    0xc002450403560411003500d00384010035881c1e0302034462401c50200c51900310326009801c0c0010702040354001203800080d80c0428920038540d0844505266500e403024902090a0390401843c0d1000c0b40e500c00008101020001d0702c1101e140340c845582c00c503961096610f0500084900a001c0c0c0c0040005001c0c030b50250026180c1e40c00c842c50002198030069000460040094030406092030000c0b034000040e291601410f00c1a05080e11583c2c1000380d5080880e42c0c85c02603000040520042100040310100e451841c00000c0c0402030404c85074007040d42105c64003000c4c2819050010b40c0042062410501a00520b41c04900182c0f150040d801036510441d003180c042c030030550400c9140c00c0301d91101c3e5503400400e401100c105018180c0c605640e504c1c001156140e00010380502c07020301c0104011140308401c40704070f130418480c9156000c00e14080d6418a041500407540040038044007921007944031881000b5a101642102c0008950404056982d2412581007000980401018030b559109007280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 761242329 1250 761241079 761241109
    0x19020904020304060207120c080306060c1009080334080604090204090809030c09012928140c07060e031002040306052d0606130302030a030806030d021209 68
    0x50801426400040680c1d100b5602500d026802148020600c020003c0c40c0001014030704001800c404507030b480e0142800024465032181c00c01007000c001d082c40134001c600c40f005c4186000c0100303901600d00300c0e456410607a042d11010607030403a0350008000100c81005e140d0746543d18104244000c3d2812685440d0007002207811036280d42001d030050b00c80f8040c1c0300405203c0e007041921040890141464054900080c5104110f03039030040040d090542c22035680f120100c1c001f042000c00020aa40c0b4a200740c44418224401507110800100b042e00e05078000c11070b00345e44100c0030b4841b6144400440c041c880109200303800c481800c020460154001b02c000749805025200b840101020400881e04983d00586142c3e80710305c10000d046042c035400c005601d031200804a184a140f4480b2084070800428490240e030300015580d00c4400400c25a500865000701124086901032800504200e41a0f8a4a000b4803c03114900006800410070740315080d11502c1c80350134140642c0404c0359801004040d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 761243579 1250 761242329 761242331
    0x7050c060a020915070b0106030e0a0206090d02222a0e040903020c0402041706060316030803060f2106092e060f060503010f06081605031008061314060601020619 71
    0x4d08403058183c08060040c01d4011003c100841d850031901170305491805100089542000703e06c0c80041e03039140c0c02d4a0400c4c070b0035162851460340301e1020030000d8101072011013406130030210f1800b10300320641259074072140d034407415645203081a801103541c90065114074082142034035070a81c541400d9020100d128001d20458100c1c5c100340011034100c0e403103500700308100102c0c064204004d1008000e00c80d003142c1c00340e0003815075601c01c1420107500d42040c007005010140000100e01180da0f40c402001c0480300081c42980c0d401c4c000400d621011104804140560003414001480300002148480000171491028204074000000d000e00650307440000689007603032130f040132481e5082d601860300980000c1d11280da89505103c884a0440d00715800310003001100010807031200e815900d1070090070590b0510700c0d103c1d154803820585600454201c3c1002d0b120700010040c00c1107074151004a45401180c48411200c1c400b0082900d0f42c80850303416025130b10920114a14515052120b140840c803118 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 761244829 1250 761243579 761243599
    0x260d0c110f06031005030106051002120309070b13140d120e04091a0105130203010f050409061b03020d0b03033405010e0303040c060528111603060507050c060a0209 72
    0x40000d410f82c1060328030103d021880b031001c1c081428248220300140501b1154401812a5050300a41e80c1141d906440200784011012681d041c000f00315000140404030360f01a00d80c9c4c000e022a4155500c98407a00800c0114400725800909000d0140750481d90858401002540a410b0503110040581201604580e03181800c3c40032441003c51101c90042c0c401d9081d68a51528040001c4910700c41210300c02184104010811420b110310b805048074000d0b0b401044004441c2014802000642c1c561030040a1141318030031032580c142c0c020580b802d24590200040401602850b5903805441c0401e00c0089001c50700405100309446110300c00803428041d520748001907500e02e42903c00103544000c1e10350011040c0010041e0102c03508c4080c182c0f500d0500d085c4038203040c0c0d42440d1545c10051001050001c0f000300740c038070f00c42d0003801c03450981d0748221010003140840d0306001c1d004a1006460710303132a1002241509224408458111010034014071860b142c565487c002980078090759680000130130 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 761246079 1250 761244829 761244859
    0x1908060303070c090504211b0809060d0b0901090603030210111303140d0e01020a1211010608060114040b01021f0204230306150d032007260d0c11 64
    0x10460303001814210134089107904040c60b000d03d4104400c3c071507189215a8242a2008540c807501c0804045040d0340701d4200e075085410708940ca44201250550000d500040d01c0d03410245a4200460300e2a00740e0314030486070f0341e0700c04880031a54680002001a00501c101d9a950b098980002c20400a080c0b10313189002d14900340305401000c640d000311640f18240d5030156030b0480034841f014a02c07855040440080d016040002c2d00c60010010050800343d207003c0450140d44680103100903544171000822141ea143c00101e5554002441101c0751000c03070a460094a04180c0202c12000c20107030001c10702220b10703425003500d10446c40954000944d0912002038210241d80c14a50243c50300c20400d48520b10b11828103051120040003992103e822802c850b03642c3c1c03190450050700a07014505040780b095950791103400e10000c9c003007802e0240318200c00821803145074103107503104420541c1e4191a0100344454180c5400c0d940d00d1a502090905100f40d01060210512803030060f0002c162000010303800e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 761247329 1250 761246079 761246093
    0xa110307080d090906050103050f07110a0804090e070b071e0305070c030f02040e0a03020c0f03030d0606020303010e07080f0601030f0e0706111002031b1b0a12090b190806030307 78
    0x19556000103e0070319041000d4452480f80a0103000d003842d040c002c902d0950721248800074050514070400142c0803080b98030700301c00e010381900f03542e000d18204e5640d40e440329240090820380000d036a06001d4098005070030342c16101100c081991000c03c58403240b4003038012000c1c0c00304000d0150240b005c10810540021000c0500c04080c5110780f00320001d00f0414010300c801c80e0b84081c00e03c41d00b58172007006000440c1d0005800c0300c0c0100d048a0002111220002080c114020741300e0703042480782044804141c1035004405941a20b00e40c4082c54a1035881001c109c404040651711510600b4424001c60019442074020306118030481a0108025500d2840f151404151b98030100c0003585030302c1036660810062201e190070003074030340e015400c4d82815400036901c1980c1e40c2e654440d040b0000b03101100744a54441e00102400e1200585001c2d005509044000d2007506100c40d000951710070022400440310800d4820310703039100c43d9424000d1201c40042e80c2c0d8940c00340032903074144018440d50f40001c0e0b003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 761248579 1250 761247329 761247343
    0x10c0212060a0203190209030c04020901030b040e060612161e1706010f080309010e091806010b07122a170a02030c1002030106080a051b0f070309080304080a11030708 73
    0xb25034401a92854401c0c81d040039062030030124440680100038100d5141c0d40011941c0003114216001a540c4038580c0040c0c0060682e0740314a40c010b070501104445a940c045a903a108540584010708080c00c0f00003025110800c1034026105c1401072030081c880c1002e802c100350015941c4007c0c4460380ba85810703007002d503061402103822140d0700860060000096500903c0c0c004c04d00e80300118140800000003800c1071b5440071010b0b026000b510300290030340940828a01003e0740500039105d19585440900440d5801500103850303006841500c02c4010384139809105401d040c04404051010b5084a0080c1c06040914107846d00700c400541845198141c0d00101038030769044c0c0085907601a400600b42c20080079940c003d01661060004106071a00401007561245080a00040d070b0780e00c48001503190781e5103145100703c4810105070300043d1306204c402015a24060785449a8182d6542642c0e641da01c1940690109904400d120b4000220b1505400c140040000c040d5000c060300ea0401030301e0038107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 761249829 1250 761248579 761248591
    0x7020406090914011a19050a2606010302010801050d020414010b0702040e0d0906200703111221090111190c06030911010e19090203070f0503040f02010c021206 70
    0xd03803602d04204225014643c00e0003076282c00001e210613036401a40007855222030750b5590007a4080311a2955500c860b41c0c544018140003011000c020352103116101c03205042060356806241e100003004c4102c28001030003412a5816034800019a00b01410311200c2411302000703c0c0c005403101c0700c0c090038000700402d1038080c2c140d60560a403a03034403600401040c1c0d03d010069901c9904031a400b000300e60b600c80c40c10401d0f40c0240c01c2c20750121035400380040d008203200703c2451140c000c5950100400000004d42803140300d0407160788a6949485801984a2030840d52201c180e40560039030b598079420100c050544c004c414105600707040ba0f81c03a1400d0038016880c0000c40403040c5030f1a604100f101070081c9001810281c5400c00210303480303903100c952446000c554030341030014218203075041d5924011290910102e00da8164a0250f551607130307102942064426001090000f02002c0409106006072032140342c10000d0b5844003a03190700156641581078100341c2e04106c0600020f0510102040040d00900e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 761251079 1250 761249829 761249831
    0x20c0708072120091812090306010b0c2b1202030603100b12030c010c08090a08030606030a0b04021903060b09060409020f04080a2f10080703022a0c060403150207020102030702040609 80
    0x480705c0b01c6140c201a450360102040603800c0c00308202c140c90000c0c0303041c10350b500c2550441e5503d030002111031800060501040d2040000515824206034244a0011400080d1114507040e8112030450080c0c5c0412205260583c1c0042030700d00c80081d4940114017100380161909854803154014541158020944242c0036074480c039021074031030340c8182c2c0d05900c0319812020700040354556070f980b62944170141c00035104003004000700b0000401544040a810350040c41159554200c2c1426060000c0014110b4041ba282c4100000d00c00705d00c0003142d5001100424031403a26003008078485c002d4210508100d110349090101198482c4104001c01c86103000b0303066500c2604d0110007030022150042401095180c046003031503400d07112110801c3d64125142004440781d990703d0341c01c400074050200d007030a01c0803960316441c012600003450801c2d040803c04c00d4940c020004001d10055100d988030040450700c2c1a0b000e42a20011640600881441441030300c0c03504c10903400040c2540c405402000e466 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 761252329 1250 761251079 761251111
    0x302070509090607050a08091e2409030f07140607052709070c03020a0209130302010b0a05180702070306060e010603050601031104151101020c070807212009 69
    0x5181c04407101e50300ca00240010311480c508410018194000c041c1040f062200030b40100d4140c48091104212010b0b000840c940d8070101c0340511540e0342c0810461044540c101e28040e6482205814080d100f214118000c5190019010907048954455981600e06184070120000600001d001031030242069030b41d29911400b20f0340d901c00c402c1004141c401803009200c4030341d00325501c0b40e41603940c6c0810181020705c61423155040c142d0400001c3c1500a5002003a1400c01610750f15139101001640e000781d000300001e070100c00c1030042010060251a9002c1024080800d0520502d98080d5110741188141c80307140d5603e030381d01d90a90b0742d0780e0041080c069030440180900ea505104956005209203410302040c000d16600d80103e110703c0c062038881419000080c0c000f28010181e240c0c03800b1090008564400b0700da15900d884440e14000c5200c680141140010102c0d00c80c00695401c0c0c1c0d40300418120034820380d840840ca0100c4100341c40c0ea030302101401c460030780d0300c1c800f081d0720079003008081d141c0d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 761253579 1250 761252329 761252339
    0x20a170f270102180a231309051f0b0108043f021b3007031505060316030302060f0a0609180302070611070e070c02060a09050a06030519051f03030207 66
    0xf08000d508581510070341d007003400848811b400090141c0307040076194500700ca40c4e14040c003800303000000006020303845074070080c10505001c20703180555002d18180801080c02c001d8011100c44000307441c042c00036194002413804103202404442d200e103080704a00ea02000c0121070103080c031041140c944025070402d5606410181c111080e0403a098030840d0340c4020445000c00d80030080613070420b1450900c1c0c100b1442452030504100311000385400100010000c00f6001c0100084e180440703000e8080c5c0a081c240c0e00b0070250406848090344e03403507000f40c42a592000003200380c14500500c018009501c2c1c1000044a10451089103024200241040300ea612941400b03403a003074240d03004904101302c46041030b890540124402d01642c0c07100291541944501e002241c0b01079030240040d502c1080024201c5e4042d0300007050000b242c200361001d0803260b0303440ca426400c03100c0480d058900d81d17081c040e41400d10398055206a6105610090050500114100b445081100c07908110050f0340302d8401840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 761254829 1250 761253579 761253589
    0x504031205041e2303030304060906060909080408070b0309060a0903031107030c030908030307020a060b0609061303120203070c0905060a0e07050a18120201120b030105040303020a170f27010218 85
    0x45038100c4d0146403c840012100800d07501e10005101405c03056540c14270004000031a0801401461807a00501070014641003601c2150b02500c6440030603c103045000440840310b1094030302c0303080610098042941c031001c20101400680034100e080503030b50481a00d902c0f03402c802500c0f00600a031f9810544405a00c1c0140228035541c1140c03280c0c3d0702c10710421040e00c1d40022a222318940c0b144011074084030b00700110b803040c02522110b07903006201103819440c0100c9407050200f280d010300400040801c0d489410790300ca100d0400003030440b051030b11045c04070060035042583c06c8280540581480c90703550070062021035050301d43d50005100090035500e12680500c40d0980a0145841c407060285001d280d21003042c08800d0082c18001c00700781213126440c040d0300007086031401034002e00251800d0f2800034020b600c203001510100301808000c3c01e03007918400c0781500c503161850040020741c41e2104c000e02017980d95400041c0b880c0c44640c00044801c02800a4422021a59040015040380b803003040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 761256079 1250 761254829 761254859
    0xf0705030405130504050c0d080a030c020c03010203091f1119210c020705010e0904060513080a0801181a090a0b0a140111030304030e0114091804210504031205041e 72
    0x24448d1181d15481c6000c540c80d01c085a1010a00303040c0041c0300c15504074107900b000c40010a89034907510101c02c01c00f5400c8046426105100d010300380074003600d032000400c0f04440d0076440008514105010030304e490121107074401100e44c4203007045d00108040c08003003105000c404c40f51441494072494109043c9404001c070304007030300e001d0030001c2012414101052050000800c00b030000e5032130302c01081502da0b43d5101c0300c03003a9802403403180c0d40f840d41c40e901505020080c4968085d0000a8a01981131500b520640b000903003070845110504401c2c004011420790064491819941e540d800c100e8a903603100480c000802000004514281050001400c4520b08441002294100b00104400260f2141e0b100040c1003090030b0100751200380f03416540b010b008050b03400381c0180841d583d04080301842c00d2307950f20461003114582c0c1103250441c0c0b810301c60400002000c01140c1c040c0424030000704071b6038030495012203528025003421354a213031964070414002c01c1c040ca49070030800c0910004002030b001c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 761257329 1250 761256079 761256103
    0x11d101d061c0216020918060a06031509020303040513090c15020d180f030b0a0506010201180323041712090a05091e09010c0e0f060f070503040513050405 68
    0x140d4203200b00070307041d12108886040c080200e00d42c0001d0808003010310840b002121600030305a140680b4050064098404040300f00380e015215a40000300400d1940c010a4186c90388a6203e201c1c6003158511000508018101245e250206100100c1c80344c03100e070940310304900141c83c082004119820214044105a0410814816144c0d40300380c109800042c1095034058a03d03011084924040796014510300d83d40222222244d00540081845020400f16018a000500c2008203131550750069003201c00710440742d081c4000e409400c0340840c1c0521410f42d2585149403100700020421410400541d1083e0080d1500c20f0041c110045961000c1105a9051941641c01482c250021300051b104200c9889080c0c81000041c00183c0543c0540101c800254440c001c0c48600c1c0c141500642c2c040c064940e4218009003040c01c0480705031415140001c400030340648210310742030941488803440d41c00b22105680d244030070007000820392102450507421940000000580d0300b483d1608500342000714501c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 761258579 1250 761257329 761257339
    0x10141317030a0903231005010608150a1e0302060c0a1506030b01170a0606080d0f14120c22051203090102060a0e010b03120a03060e0108030702011d101d 67
    0x1482c0450b508403107004107498109124060004040c41c11143d0003400300b0307041c0c5060091035400300c0000c41580095040c1c1e91180c03120b240e2541c0b02810708103040d406900d5140e22904000c800c1150288101441402102c407510350400c42d0b49940200d152648042d070380640aa04c598515802e2042240d0725220440b0554014007419103191155250b01c074042c000c03070750b40b54022200c01c4811002003014161903540071500340b2007541c1c2c030b8a8a40d250b0890410703c501003044038010844a5201e400c80f480030200115109060022070b0b121182c646100070414070024008101140400b00c3c2903601c55016124164094000c0e4100300601c11280ca8002096080d6030040c0450047c1e85e030003048282e1700110300000056140f903454102c0d4050051110510f8150040720303005005204010000c2139009030131b480c01e00c00d0b590348804e52581500240321784030342a0400c0c0445001036100b0400f51410321070103141d608800c11190005820414510707072140100c2d25550b03240100e640d403003044074065507045074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 761259829 1250 761258579 761258587
    0x9040b10080f0715020d021506400207080717210105040f0b1f0e2e05030403080103120c20040f0501080304122102030a08090601060c021014131703 65
    0x98065602d88061000c886415140c4000038043d4496660b480c4082e500304100554140c000d406402c40710300c0d0b000030f10340c100c002042c0a2b009105540201c582040d8040b040501d400c209464043d03000c0d203288000000c0c00703c100404070a030341d01d1070072000400c2c0300c9803413420807949424100b01c102d9946003440c611103030812400740c0e900d036201102d400552000e80040311001c003c0b6841160b0030000400310f5944440c0101c101039250102c90891840b0106028500c0c20998400d030050703501f0302086078028001b441f48001800040c4a01840c64101a0075003000300d00f20f066030780e03044a01c00480020346c04c08150320b080c2000070700c0c2c1800b5200e815a07910368208919414200b01e01d07128481c50090035842c540314011a810000101c9214a12081003404020813403c0f0380802912030b8018080807000a60503008621115000305440b4101d403a141ca840129200d141d091020b0400c01d00c01c5102404440a1004c1d26040074400900d64012404007407040d6500f4501107402030100325040c42c155500500c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 761261079 1250 761259829 761259853
    0x806030a02102706030b0924060c15070305250f0507020a1205070314010213050114070b07020706030c03021602060c03040f060804110d0209040b10080f071502 70
    0x600034400e5012450f0004055519442c074011143da51000c120070880c50f2072001540a905600c090300c003000407612207009803250190340d80c0c00c1c2c4040d03a0702466010b600c6e04d807030040e07e442e13001020403045803010744003261610001005000d1084440c030001c03945903010400e807521034500100c4022003c1100701d0719081c41903802405182c000386c10300f0a10031b0004901056584800200008000c00a000788901c4024900103031215000e110485404400314486900e0390018000d903000080f0419840302520315140c01101c64203600c08001d80b40e94010403416000c83c80f000d600307500c43d80c5660020841d40f1324101340142124400c1100d6400c040c0305101050a080040f41c407001d005404540352516004154022070443c41703075522004d07951119900004201c1d41280c200361080740168450100e552203d002c0c45180410000000d5208001c0b400080000d01001615600321203154285045151115041480c0000c5e40d44d00102d0341c0d220b464208039044460107240b400c034400d071003d4401e4103c0c503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 761262329 1250 761261079 761261089
    0x90606050c060a1107020301020705031b0a113604030f18050d050304080303101d09030304021513030609050c010201060b04060327060c1101051902160f030f0806030a02 74
    0x2c0d080300b5506480700c031080101c505504c103544225030014000c55031100a4a8801d03541d60007000e9040c0e107080b845001408012012030180300c5c140e04000c0b82c54000d94170b03104103c0d51031060650032001d0000da00442540102440d83e1010200250010b05034508140c01d01901e140100300c40901040440c6000c091841d6000320729104450b001d0303d5501c1d5501407490400d095010b640c001200038030010080006090900242c80c00b1184010030220303120f01404501740500e041154040d8140d80104003003001400c03c0c426443c0050009000d040c10019511500c0c25187c1040e442500d9a688546650b81401020300c404070580209000030018140b424100e0002c0e409140b20380300a269503800c9102e600030f286d001c030307070900e81400d03030241c118030318900d4554000c184440c2c0c1c0400140c8045219800d040c3e0510855009074016084040075411040a80c00a503100038545c9200c900c558140700000b54400c001203e25511a84030700c0700a81034480010300300d032002000745100e03074021010311000da114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 761263579 1250 761262329 761262331
    0x8061906030b060d02030f150904030503150406050a18061e0b0a030e0a03050a11060601050f09010c0507030303091e02150904150e0702070509062b06060e01090606050c06 75
    0xc541404104444a18000380ca180505003a800d815400001041106160701c01c400c0c0c03003068031405817104901c104041c4281c0c2441181c00901044042011500c1040baa04808060980003400494499210004a0081d2140e54010a01c14000801300c0a0011641c01840007030003500b00000c00d0851a50b042d207410354910b20031044a00700000b41e0501884c4290000d032280c0142c0c40448614280502d0000c0440c0d01c00061640001e22400307159074107000114601f809944160740e41030908007111021015680001606810712042c4000600003074028404840158003d40300010020054201241c1c0a90819204403081800d59800c42c01659044601d03801040e0009002c2d4440b1b40000104005054820007904111851540001e03041840c1900a2246800c0c0c0d00751540c095072002403025101e400e61b40c0e143e00c08011950091414072059a4480782c0300c1a2001002503011503c031142103500a4104101c00c0311843c00600c01907107a405900014510f072b203801480c0079072400045441c3c1da0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 761264829 1250 761263579 761263589
    0x170109080a1b0602120403080a2d0e120306040b0a0807030818060d0b040e1b10021608012304030c02040911101e08060d14100e01050601080619 63
    0x103907001000780b103901c2c100b0440400e83c400d40465880244480c0c0884600048034100e0002d8080c0780040c0014813075004050741d80310109501c50f120203100d1075640440c1e00301102c1e480d45030758030040364a10150811800b440094203502c950b0f5203007420f105000c00d039955504641e0140036012002c10103a1000a04c281c02c40f03402505441c0c80e4070301e100381c69040303000ca034401350383c4200c001c1002e800c150780035480070a10060496081081d00304c0d0342212510b9003e00020400f02d85c40308a00804c10741040901c1010b49a8144142c8243c401190300706550b145c0c40b40c200c1040341c5e40d601340c40d030750208038459030001c41c401c24042914145040c3d40d005080649811000f070149849102507420005c1c0c541e0140f03400500102284200302e03117600004c21100091104400312061b040a03050a03600880006010b480050581c0c0520321803503e070250710a60010003103080b44100140205951564495891107082250021403103007007103400180004006041e2620400c00382e00c410718203246243c02001155 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 761266079 1250 761264829 761264837
    0x3080d021312030513091a0622030b040c0b04150e03010902060307050d050a0501030f02100c0b0a06060f020111190905060d150e06031e0322170109080a 67
    0x40e40941c10240c0005040c0e005400c0681814103a00406400c02d0250101d00c40e205240e94080c0c2d42c8082c000203507451103803091020620300e0151000ba003050380007025040c1d1440c00001100221a121460425159100f40d0314034080100380020800c0500016008086800080f4107150600e120324480030740024036a0207000e841e00b0200000e807400c1d00328918064000b00816241e15202001030b11075400802c1020005140c0f200041e554903c82c42254180c035007000100400d5800c55003070106048400c4005d00521818070003510020f1140030718540f280100754001b1540501d0440064102140600e401043d0790400d001215651000f01c142c84c0003018014038072140f00c01155041e611604c0c1c81d01300c00d0300940d001030b5a1246006c3c58000040801c0f4103009100c01c0795a6030700c9092101026520306501d5000150b1000540c860101c03030104465800042e240361203003520403100d600196a0b0b183c820700e240700c2400c01140c4843c0a1440040740c0c080003c0c001d4440c141d41d0108180301c0e01118600348 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 761267329 1250 761266079 761266087
    0x70507020a17010f110a0f020f0705310c110f0d051305030105040501020903160e1515180109061b15060302130209130b030a02040506011b0f150603080d02 68
    0x120000b5003100c001895011405c02ca80c0440f64048541c17a48525040c41c0405c84001c0560715451000844858180c0c0900c06090f0441c03c040410003480c01e2880e030300c50301d201144c400c90140303c0496020803804404d2480042d582c2e61002c80a081000d5103541501d468002801c001d604c0c04c0702180400c038488aa01e048c1e5a914000145103980c41520f8000e141c0642c0380c46e040004101c2c0541c01041004800c904030f0760103614668080e0007100711406003250541900300460f100300c1c0b0300c074404140303000000e22102280f6070380100c101858002248598240100308003210665800c2145200607101c140342503903840104602c0c980e004035444900500c040c5c210320701d00c8810101c1d580500055940244041c1d01821010f0a0714080c0d00825401446214610004031480f07040d40f054186080d00038010b00110166038007040000d040080c4618140214032498180c1c990000700303049091481440f125149840e079082c10640010112a9000103d282030320900108952400340c0d82000500e10000d80d035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 761268579 1250 761267329 761267369
    0xa06031518032a032c03030a050c070914040213020c0318120a0c0303020d081003060b010e090a02070515060108130c120309051f050306041d061e070507020a 69
    0xa0000700390700040c64144251100801c00d903001c40c3c1e105003d4244001046210010000c90201e800c0700145590706074001c001d48c22070103003d04058240845194280c81c212943c035481c940c2994145000039850314003c00c208030440c038007089034142c0c3c604551411810041d01090b0903a59109480480300290452055405265110300c2960352010108041d10503003202450410505441800300b00c0250240101c00056988200c01851217502e003160302800ba680b03551104001800b84070f8055040110607481c4240755110002910b00494502d0401a901c55841c02c0044c2854a10341b00311814142c400207001042ea131005504d07410008403040c1ca111403005150070ba02d04000c941c0001c4445901c0c2130b481091540000800d411030b0000e4170402d80c1e9007006511100004089100800072550a10101c0d080e4141707944100c04152461501e250803080e000700051401000b2501d01d03916032102c07414036540c0c6e140c02160b20341080d09802c0542c180039283d4002109404140241003141c400c42c040b1104c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 761269829 1250 761268579 761268617
    0x418060302040609051608040c0e0a0e0d0f0e030c090a050603030d051608091f020d020f28110d0305040602120906090708071a030408070b0a0603151803 67
    0x100840c0c0c01801000804d40ea15001805810111a03050b41d2040801c0c0380d03a02a4000c030a00c1d482660320043d03243c6c03030361b06064006d41141030281010080c181e0369204d40e075640350104461003d400107900d810541d940c004000038240d50f198048a40650001a5052165115183c0b86034000c4042d00000c01c0d0b5941d0503002c00d00d140100c0001950f12810081441080841322002540324000f640e550150b9075901042e95980e000c6528401200500840e5001c0403198180c4c041c1c504250656005880c1210342c495910494005040b010940150f400c2c0355441034901c822642c10f800c40303038202510071240d10703800e8540360651042c0c601c06040e01c0d48c00040c01c0051076811a41d0f242c600a250468030300b4101011075448404607401410f0744a016004a584a00066550111102d2504c286500703d41e25003c2c04098002a01c00c032034904c02401142c1c0068007a14001d480f54401c04400a0f0b41403440c02d18038040b4400200c07402c1030038680400414140d0741040300c19056901420101401e0b0010b145080c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 761271079 1250 761269829 761269841
    0xc0a02210a1103061602030a030b301605031f2003040210110709090212030a0203030a050703021801050a0e150c011a0109061b20120a080418 62
    0x40450181d00303503810401000d040c03500412841a000c07a1a07035502d18203050b40039405941420f0160b17005004890449200f0741105a510300003600c888810103803411811000e021a1140e90f09006040c091941e000c3c0d030410115214444441200720b12518100201e41c030790f1180c0742031250100107002da000c0f030501180c0080078403841c24429004085194000706009402c255001c92140601c0c0c601c00604074030400030744220f1100704019242c02e500d460071402c000d000d04c0b0812a041007503c43d034400c0000c41417003e000740780850340246561b0300d4480700c55821100010903230003d16105005014a00c5002c0c0e43c00b00c0c40d00030070f080c120765941c0140c0c020b80e98089081031090b803183c0341070787d402d804c4940680a0055040c84000134461602d00c2041d8008040c000c124007800103070407a104214061082c2104140c480e641e480329882c196094a91044080f2041084080c102c060000742150f800d101008040c80a9001d0103040080740e59518800f03a03214510412031000000c100d481c581c0040c59002d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 761272329 1250 761271079 761271139
    0x31205040b031608070e0915120d02060709060f050403031b020409080a12020c03070204021b0313030c170709050c0c06010311010e0604060e1003020c011409070801020c0a02 76
    0x100e51a4074003002041c3c01542075009140000c0c003010003044c0b000d400b4030764803181240c000b08100d406a0310440c03131161810400200c254800300c42180051120000d01c03030040400c8241d8081d003514503050708007426041566000348204031032200c1120b60240c3c0542900c1c196545460070807004030401480d0740b50070a040340701940c480d160404ea2020468814003e14a190158950302450b40a4240400032070160102c00d0740306810420003000146030540c001c19080b100141c1d05400720781a403400c5480c40d0051000f5030b040b84145602801417000b800c0210b401458080311000742018008401c60f241c150f80c1c40790f00b80c49511a0045040300e41c0d4181642c60405a48007121b82660352420400d0500c43c03105c00042c0802d104090344255400c01c48221819160b40d922000720703842c2804107111a002e1503d07880c0c0304050703080c411081c5615003070080f525413107015205601da6040c0380c0921402c1800c0384c0d218081580c41001004000c02d408035084180d0f43d0100c1e410340d040c01701603006022809c0d0600c10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 761273579 1250 761272329 761272349
    0x1505030402150c010905060709060c151103010f062309150f070503040906060e090705030a02040b0309010f1b0225170a0c0803161410020c1e1603120504 67
    0x4000101c0f58154171001003e401a000c41d01e1544401c04e003924850307001c0c000e4000103011085004041078200b15001d03180c2e0030f44203000454140c050720441c1260003e800100300300c581502c003000b056920212074140c01042100039248011201d04002a5101d4040d130035000d070092034032103807a02d03c2c020203071203468402c07014045d950203c17413501e107841c1d520602981d001d071460948089001c038130031032a240c1c4500c0050302c510b03075640340d90328107413290342004041c5d0f99810307000c010106091148002a50090001740000300705407120381e000000740c0c0c507990310341400201d203200b00341080f035400510740020700302002a19000045070110081124010740220a410800450030094098001000708180d802400e040380060b848090151310303032060081c803052000d14040968040f80c1d014844c4003601100c03404031080704c0c1070080400c003aa000540380320042d8100c86400c4440800203c81026102100c10141c8411426280b500e10109100e02015008540310480501540d018008030b802130b007400740b8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 761274829 1250 761273579 761273587
    0x30c09241009080f211b070b0301180b030309060d0b060703020a02150408030406030e0102070b012709150e0a1e06060902031005120a0602220e01150503040215 70
    0x503028000300a507100b80324040c0f140c0031442e0001e00c4003094042c0c280c07035484010029400651780b16031458002141c0104c440c81c00c81c283e40229041009550014074000c034202d5241d40c9482042001ca81607841c040901508051951503641c1c0c0100446e98900c20448913191aa019601010028401d194100d504180005088814581c00003402e45e07007207200710f64000f40e00040c4400c4040341e008511468045a00910040c13250303d00a13044224a00c031030304001402d01960f501d075a07a4120086e8402c001c400c2d0b00001d10580858048001054451100b038103000c3c2c80f0300c07a6a81d0000382d080360f620314002503540c0c5030180ca15805005e0040d0458204200c5081c00388044880c18400c40d092030103ca03034070300e895000200641c0074020340b44640e01d06c8400990309490003007404001e900c5c00c02510010b02521102c000000d9091010304603610320400740d9003582882c6096041008055089041080e981d60010803903824030719030980c5031082074074106031031740c0b07907480803503884074004111481916001c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 761276079 1250 761274829 761274859
    0x1e0309020d1e080319050603030c070510110a03030b040b040c090b180907020d0201052d04051213080c1c08072102010e0c0109211103160311030c0924 66
    0x81c02c2a06000d0702e110040044c3c1e00e80c081019640d110f0120ac070215508041020021450071380d40d1041d4100c500d00300030480000d050105410825540d2045000c81c0c5d50740c07004110350900d0310501c0e84180c4250790070010040130000250510107580710314800410001020800c800e0100c8031400d1a16020341442c0150400407000380d03e803202d0350380400040d07180000191880c82030b5950001c42030841040c0b550242242c50a07003009140c010070a0380d0500c0b411110034913102c1142e004042031071a40901c0b8440f181420341c01d504250344214081d03c40c2d905181503100301342036181030314981a0720030381e460303038031140761414042400306c0c0300b03002420003d1103980001164064014142e294178540558007600c901000540e81d41001d0b02540c505507035482540c00c10f0303d064158009840c0d000e40748482c0c07241034140000c1c0c030340480d0401d684144d0000160410400c03c40d040f00d803000305800c0b8098881c0d2580c882c045a510000280b040c0540014149004810880203124686039240900700d00c55840c00f40c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 761277329 1250 761276079 761276101
    0x13171318050c04270b030303011e090e0c100908030d0b0f03010504050c040f0605302a010c050604081305041b111c1e0309020d1e0803 59
    0x100c00040206410000001e1444039a03074100c0e0151107214500c0d900c0d008003110001c4083e5041d40c0c0c0c0c050410b9583e90544078503038040007e1402480c0c0c100c42000f1400035510a54101400ca5000f110098109400301d1000c1c41c0119003070100d0502940c41242c226154481140c0f04072907a4403030710950000064120080469400074421060b0944400358440200401d040c01c8a4003114047d140342c03c45c0c90003500350714294210a540c0200414041078107034070f13000010340007600560001d5180393b16070b030f6a40c51441c2e1020911400b00c03150001e840040b48441c1d40341120002211050b00c0004485600340140e0300075440c00d0300c5a81c00c5000c0300e06030b1a162420055681c0a4030080c040200420400240381c500342c02005000b030300040320b03c071000301c5402060f80d843c0020003071982c1c14040c0c40c07241a0455040f100360f040c1482d0076a14600300e410702095001c5841a4600620105400c4c1030820700135803a80703c54101040e0340a00c0098280b80f03031403405288030321680c1d4024041c02000003440504801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 761278579 1250 761277329 761277359
    0x3201501050f0f04020a11010e0325030206061020070303030e0d17130b04050307120f050702150c0a061410051e0a0315091a131713 58
    0x91046114410303621102007004003481d80c016240d0140d909000c1d807040742080d801400d8100072a003403c000041c3e200800301d0a44a180c499070070660303c0494504000c00794802c400004a4200794107542e000482e4a0094540c1c82c0204413900501118a10002d040d1085100541443c0d0350000c8400b00c03c164900f041c3c4a2815101c1a4000390401c5650210503401040c0d0002691b15502e541c003411408280b00d600f4048020b108168514801e1218404134220300c034440d100714880d80c061a503071b4050346031441d01c9050300d0038a18104800840100a20b580240c11580c03a2a0100e5184403100d90043c401c40d000d10495520b40c8881c043d50125008024494100c1903000c1d0b0005c1d148015540e44690000071030380d481c85410307880201010403000386d440c4c00d41644000350025041c000b03855183e0700e1303c030803048500d038a2402aa9440e4603035001e0000d02c0307003039440840c1005003080c43e6051060b10840b00d40b50307565002d80744d03000c0b441902e050f03e88000200e43e8100b0403d2901c656081d9600c20a0202200d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 761279829 1250 761278579 761278603
    0x1030b0a23070809100204151b02040912170c0417010e0f0a03030f0b06250f0b061c2301150b0c1509070909082208070b1309090320 58
    0x883c03c5c01d1503044a07914002c0e035003070b520f20300343c5042c64010500702203480b40c1c656848030b900500030b80c42030005620b80e4085c40030050b005a00603d00309150745001408401412494541103011105101c01c00031050111412506000700c1040302822240c00e003401803080c609091054802c0e9655109046030104100008900036201001300ca041440ba400954004a5803154000750801400d008141400c5c0060b001c40341d45585400600c4181d55040d400c11607034503042d91813540c248104040e92400c401c03980000321156004006100156072542c04045141030740600e62240d0081c5660381080c2540300348502d4a64040f01004903584400004103a03000c150034140a015940020f030b01c00d500c1102c101d000d100200000c002c418a0101c0c00030084c03074001c0040b64180c804004503402500c0341c2114141195980e010203c1151901403083d07c0c0c540742e94052030b10f4200500813420500c04003030b2424102c956080011820030f90324502140c03c105030b4649040070103544c0642c40e00581e000240400030f00c07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 761281079 1250 761279829 761279833
    0x403032d0f06080a02060a12020a18080c030a0311280c0e07050327011a120a0809130207022d010c0f120219061b050301030b0a23070809 60
    0x75038080c0081c1c0b0100c1c01203a1282c0d205281c00c8006050000080c0308400c1c05281141a01c14101d0040045e680700c0402003000641c405910007960788a410f9a4000341019001080c011505c817020a4544001c507002a00740490800c1244110307030280080c180d0030070b55504108114180c0080781d1f680103460748054a80b010201d0000c200f281d807081c10782d80100c000751180c031705583e40d80007001004502c0783d41c42051515082c4000c20201d00074010b003461a0701c102c103400104401402402896102103045441543c03042c0100b102240d550f4084544d4a03500b40e90814106080d0300c81400a4818131030002d402100b4403c1e400001010111101c45801102d22900504101c0c0030045860740c0303260030003404202103200b102c0001307403410000050000c3e0a0055070700c4150003503641d09607421413241c00d960040d10381840c1011900074404a460008060030b101d820365045840e4210702900050201840fa07aa50b609002030200380d0fa20090180010b807510251450807403001000100d06989000d118 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 761282329 1250 761281079 761281091
    0x609051b03101404020d1d16060f0e04060f06050d05060301140f06121212060303070c0e0408071b061e0806011b0b0702070f060306120204050403032d 66
    0x8103001100e005050442201d40802e0034000d00d81c0c40e008001004590103030382000700140d41040c07801034140841302e003440140100c0b480c01c5500d08000f1004100c0c00c10441c0c081060142d00d4200510b440383c41c00d640b4041110224038000b00c1c0080c180c030b4010f407150508001000070b5156210f0002c00020310820010301c501d40b00c000c00e05081e1640e510221075403d101d44001160500c800e244542d02007401018400d0059283d5111400c00884c9855017540405c00201200c40044081ea22074114a00340c00070351400c130090f143c21143c5601409240c2120744400c022405103d2500309880c200c80d009511402803800341c424440060305144640c102042c400c003003142142c000303221300545603003c03501c4030300036595600300440760050211040312000c02c28595050200f550500c0340d034441e800c19002850400c0c00e0403a4a030614a041d40000201030900f0f00a00880d0b11003d40c40040682c140c1d40420306880d40c5c5030a501400c494130300b00c00802c0e00c6a15041564032503107030041c141c00c1084001c0101d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 761283579 1250 761282329 761282371
    0x50402010f1d04020d1d28050604060c020f03130f050301090f06020c010f02070807030206010e07050a18050607060c08011e0b0f12040b1005100e10030609060905 71
    0x30712040009491140710303181c0700030384550910b038004001700ea05154002460b00d0001040d00c20450200750400282d60040040402d5994840041901c0900304410031841040341ea0b100b43c2c0d80c05004100422103925048880c6416008200030700e10104c12a00780da464440700440180303c41000e1107546400102c00340c000a031401d041c0318052049030801c035440440034142d1983ca01031360107160310901941d646c8502007401030091015021651041018030358074500c40c14002c0c980711040c0c00408043c4803800500c6003940d000000c9841c01d04a80c2003000703070380e40b541004a118994541c005030304042c00040b000704000707840e8000741641b90b4549821020f81d032190900c2d2010001401c007824a10068882849480910406080c006000c03050b100d140071601d5504110112090320101d6400340d9000510102d40c0404110b80d0103000b040d601c1680410301840018071045040400b04e014262000d507410303e00d8442d41200c0c0261000080500c0b01c95500c0700002e00900d000c0398240201030a0060b40c2d20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 761284829 1250 761283579 761283587
    0x507090515042d020918072001060f08060a050c0306030d0e0f040603120e0904020f0405180708032505030a051803060f0601020c030114180106080f01050402010f 71
    0x20041550304802140c1d05152024080144001d0100d1207403401030460581150948000900e000d0a05410242e1242c90b030b5028800300888200030b400c07046ca0440d040161003603200c03c184502c010180e0424030f25121300c0e04414018411600508a407100911007c0340c00321740042e40500a03603843d5000c0107680e407a0041101213000907113030340d0344c1074010001c000c807541d01c07070704507845a00001020090a01c0400000900701e401d03541c0300302c545144a034203c0c0b01c1e150708000148042441034448041c1c03841c180d40080c0300340302e40301c403c28410317503841c0c000c03c0e815208980849000e00d03004084402c50741d15012195a41d0300f10300c038030587c1c1102024000502c0346845806c5210194860700441c01e05109081c1074943ea0070080568040c3c0020031210045a902000614002d002c11440381d1010704021000a0414800025440c000d0381060036031142209040001e40c1e02406140f81c500600c80d403021000c0c0036155a902c0b4200502c115041007200250650219000e18400d032078200015015401c152 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 761286079 1250 761284829 761284831
    0x60f0307060905060a090e0103061b020606010806090711010f290a1710090602070b010611060a05070c05070f06080f04030503070c110607060903230f090301021b0a05070905 76
    0x500000d48034001040036040a0028058803403032401c06c580c415454615020843d5000d031300507905203460b04176035298011101d46140007081244040c002d640340007000688003100242c0118042c0e0b183c040014030f420b200300b04501400c0a6040240040300311500364001821800d0280c10b001d000036840300300d410500f101c410501d000058507150026161070031402c5100010100c0403c58000d5079400440c2041c1c40c864006480c2c4070b020016196949400d0142c40408141c0102092058008040690040000c0c0c42580300b50b12100c08100c582e100720044800c0009043c0003080382c8280d51000c50200c61a5440382d00395142c48d543d559407940c48110542a0b418259005000b0034010800b141d81984034191644c101e6014809c1150707030220800c0486d01030360125400743e40310341c0d4a0002c601090b6120f03d9801ca17494042c2100300c01c080c1c071900301403e244101800080c40b0100000c0c1c42c0d4254800f9015240e131042c11403962811105400c0107542c0b00c46001ca8100c442d4064a4800310744280c4a121749 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 761287329 1250 761286079 761286089
    0xd0f02130f0801060317090409020607061505040506010c110406180e060a0b0604090c0e10050d0515151c0203070f030b04020a0c230f101a092404060b03060f0307 71
    0x10714101200408210480c7c0c0189031058002d030312240e01e200580c0760a0000d09800b4890b280008940d031710b00004a00178002c903040030740320302d04101c2405826a44503c800302429000b80341d45003c0108900043c00130b00343d550000e10043d02d181d243d150340203140e601c0000038004003015540c6681c4c03880c8940c0301f111111005540e001000b42b0080c894a2041c0e4410b0a03030f02c04904200345c000b20200b0004085159002180000a4001801d1801000d4901850b9046040e040199210490308000904005001303100b50554000100d04507107811540110f014513142c0e1404115a64140408024080341c1c0411701130000c24101000542c0d103080138401c60391030110565a120a890b01070740e4251007140c00720581780c6039070510010241d1008007400181c844114890042c2800080d08030760000743c4410000f80241d403000007020703c210f070b152101c206501000b035500d00244600b410781d981c04400800c2c00c0f010b800c60f180a0010032031111a0300154001e50381103c09038018440310303041581d02c440d60301079 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 761288579 1250 761287329 761287343
    0x2040f060e0c030705070b0a0501031b05060d0e0115060e090c0301030c150e030724020604051b0109090f0504031403070c061d0114010f150e01050d0f02130f08010603 73
    0x280c060a031200c00f55400012902d4540c2c50118a52031309211400191814940a03a881e80100f04000700d102c5020b82c003040c0a81c10000701440c0c0380004500707000b090f03400190f140e08c84403411541c100a6103c030302c603a401d5200c07400c4015110302000302502191110f441c05243d6410124600d03079002c034240d9040b29130041e1034258071030030a0002c0d4803040c02282c0f14010f1080c0c40020038415036040c81004040d240450020070342c0c0d0003410640c01c0c86002c508145041d500440180004601e0214008481014802c2900c074110000d100480740451a035001081c10361426401b0720707150071680c00090045009a50f6840c59841d816080c01c4144816540c281c00b04030700c50104030003c0d005420049490941c0070000744a1001800400c0c00c0d1038a0810441c0c01c00f903800d0051015801003403040001d8420a190340300e10710f510303a10150041c001c40750700d54140b140c00300c1d2000c41d5001a40000d284d460f01c40101303545480c0c2d08050f8880301005802100000c44013001c003c00d00b018144140d000f00ea4004031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 761289829 1250 761288579 761288581
    0x30b012619110103060e0a0b0f040902010903110f0307031103060c0a1211160302010204091103042406030c170c030f03090904050a140f0d0207121410050a020702040f060e 75
    0x80c1e0842c2e90b2801c0e10b401418103464150028039420a5100c082c4039090500d00440c00741c082404004003020f110b0041031085103041991030160746e114000c80141d9034400323560610740103908000341e000c2e00c038114100d41c9032003540008010030243c20495000c1c0703a801d500311040360316122107100b881d01031245920001503408040605d00c941582108070302014075200301c0d28146500726100d0358484218401c1d00540e4000508100d21070702449020f070070030031010030b150650400340d84084040744d115156455000c011f104000807855940d1140000b140c0c0080e18950850741c0b0314504840c01c025182500b028050103040c0300a5007000b00d0348000300e0250b0009149044500b804010340b4400161003582c1300d10030441c041e4006403400905e016122801d5008240004100308918602000d440220046401c040c504200103c1c81d416580c0c0070307a6006403215170352942c4040851500700d14000c1300d6030241c104418000564a00d90003880154025502400302d200e500101c3c0090b2155845081d0250000d14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 761291079 1250 761289829 761289833
    0x30c1c0804022d1e090c032a0c240a0e0607030e120408072603040e04030309060c1e0206090303041b0803030c04050a06170a0c09030b012619 62
    0x10a949036504000a081144289010219070f6800c0211105000c0c45140c0061011905d490000c11364007000c00302c0c0803461498011807901a80c00a103a10fa04651405541808402207035020790b100107007440d082761034002101903800340701225643d0008080290001060038900c40e07000f03840d20348600c10010b08040c1c0f1035100850040010b00a414828015040401a001c5011340100000d0200e13900924a09062240751141140300d514a016005400c0001e0341007884040155004c441c0b0608402e840c0d07030303103509040c1c010b404078030b0b0300038440e524003403100490942003a61070308042d24850a800700c071401c90310183da8440741070310083d00716441840010001107091410302c590b0185a1054482c0a50340c034091851500182c600b105030700ea001c60305110900701801048024510745c5414282550350303460380701180c1c50141c40c800f442500e8581a2215900500c000001542d102d00e031031483e0341c0d580c0707411808404032402d54050b080000c1c64106106000040d5880a6903440d44111406402d907 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 761292329 1250 761291079 761291119
    0x20c0a0b16030909180b091b1512040b01140a0e1b0d0c090305160e010302090c040b0a0809010c0f170402041107031106010e070203040e041e1104050a060f0b09060c030c1c080402 78
    0x222500090018100310f41c0e120480218070050103240300b440cc4903c00d5041c5828140d50f181d805000c580a003a84900411010b003a1440c00b9801c0305d8452040c0245200019880030580b08a10304407400314100307034045401c1039010301003501300c90207035068905131550005c046000c0041072140051501380c1e0310061000d0310700f40c52074603002580704031490703c1c155550042c0e141c1e030380203145d203080429908030800c0440b660a004041c04c5200c1c91038401c800045542019208a91191510108603c150006411521240c0c0500c03800e8200c4200c9a40f2130000d403030b008020706000c03004101140140d00001031540e58140c20507000e806503802842c24681451001d00c0b000000070000d03582c0c3c000c0c01e4005080007161040b84c94205015142c03400b418090802808160b400c003a00c3c200c1c40a140880810200c611540c1c648107030342d44540140d94819803400011071501070b586001555000020b604403e56100062208401103186501060190060010b807040d44007124065040207040d0705102c400190 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 761293579 1250 761292329 761292349
    0x803070308090c1f091508070e120102031501030608061302150412030c1406150d050c04061d0a06031a28020307020c0a0b16030909180b091b 62
    0x10002c00c03103039040f0000300040c0840c6200300344104010720103402c0d0750116070f00803000720203801d452041c0c10444403085401003008000a21807020001800003c60351a0b941d14620510421020000d6450f820030194201030740d900000c3c440c1c0400e1802000080c00c11001c42c01c548650580d20000c10414569024040c0401200c3c4089141c00b10402010916941480106091074005c1d81d0310390020030a0f19048070300b0481c0390010340c41503000f40104010f400d968101802d41e00020780e5600040405480d00382e141604001c1900d0f03000f41407030404100e141c0c03580b040900f0400200c2c1c0f40c0d905622281c079404125580d900000d880d540030712100c0c00f013103003c900d80a03401020b90341030000807068000070124820105101d0141d155000024070003c10b504010801042408403000083d884c40c1414401c441e01c500c0d001b08031031204107110a801d050041c003181005128101c0d042c041c0300040300c80b08200c102542800ca038041070840c00314803000c600240b191101001a40c501c40d031444c0f0342e020440030b02c0f0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 761294829 1250 761293579 761293591
    0xc0e040f06090b04021302071211031e03060103270609020f0409050c1212030619050a0801090302010c03060b0913020c0a06090b091606030b060706020f0c0c0603010803070308 77
    0x1606403a04002459520941c01014000c1d0380f0b404407401d051042000b51000e4003003110800d801400303c2d0011800100f480c032100040e6003408150003d03403010303480c1580603c1140d03202d14034040d40c1850204040c04002d42c0315440c241d80400100f881c903074040e070021400400d002d4000c2c005076107040029191740e0280001c540004e002c08504140b01c4006000e4844900d411122a0401610b4039014103210310420034156100c800360050740c0e06800000182d000040015200c1c0c0200c0342d50340c160100a280070070180c80040d08001e07480c0d4448000c80e000e000c03071210880045d80781880c0340401c28440d10840099540348801580780c039114404000d10441011003c648065003040400d040c500c0810600300c0243c443c041c04600c868480c14510300071003000b0300d0740c2d40c56040580c681d42e44101144070f5000f0b440090070002502c07000000890194010000000d010702c1c400680003c0c10b0700194081e00410070700f942201c920398020402c0c0300c40350100b07101c2d090385584188032060003e4003c50149900107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 761296079 1250 761294829 761294843
    0xf12030601050405090a1d0601150c06020702090106090623031f0b13051914010513151116180b130204030605060a06020c010c0209070e0a062a0c0e04 66
    0x68131900040c40648040d604101c0c2d10b07580741d40d50685c41040c641011031030724441c005810700e58500b10318541000c81501520382041301c0310030554108a00fa5041c0c610301500035100c0c0400350f84428026000503041c3c080c0d007020842c2034900d602d04005d03c12214810b90a1a5415411a140c0544088103011005121a1081d03414500412040342030b60241c2600c2003018103c0d207003140381c1030274010b40503010038100c001c3c0a40e48030140581d50070002d87e0591540c084c6821503035040340e2079010b1030070905608000c5001d884031030210543d41d0322065a00c5000c0d04002591742c0741c02d2600e81c0c080c0c0e414051040da50001d801d00c060010484c225400a00c0514001e001908000c04592011080340d002c0d4004650081d901d2080c400241040c0d140600500054001803c0380c020440001c1e02a05100c0d100038440c41c25000050b0000d80700b109140985140684a1480303a83c03107420103403440d1200802c6605101e0101d030200e030004d1141543c540059080b101d5081d0640c1800c0c1e0741e504000000303200762151 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 761297329 1250 761296079 761296087
    0x140712080a0207140106050103060803040506031b0c073b06060d0b03061e061e040c0e0607051b0105070b010b090105070c181820120a0b04050f0f1203060105 69
    0x41440c0001808079944504000119241001f00140880d0001c1e00249495801400300303120726240c400480e60007242c580ca0800307482c130304500d400c001c40c0302da06188846401213090006021401e1110070440903038608121302c80ba510300700d070308520443e0030343c1b9051000c201ca00411788900b003020080c15000340724540440d03a865040c0100c6e00d403201c01e03603035201c506500752041c41d8081d664045003a04008112140d0a0940e0000400c1c81110303101d00102e48034555480540c3d04031401800421a02d45001c1d0480d40c03610414100030340c0765803041c10b60044004440b041c5581561082e0100d95071550701031303c00031070782e42441c028881c1d980294400c20305102c4108001400b2414180511000f0103400868000c03da02c000110410307201403049041e2903003d550000700016810f0400401c043d245a0791a000d0007110303038005540c0e42c070b030f4000131010f42c002c00780fa4805104004000d00d11842c010021640030014458616540c1c3d011541c4030348280c0c01509081d800d40c00110000d5401040c149081420 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 761298579 1250 761297329 761297333
    0x61c06090905060604050a0507050f0f0702041404050f062206090c080d110c060d0e0c040501091d061317070203030d0c12060305070519030b0a0c140712080a0207 71
    0x484001c418265803c1c0e22010404c2031a00e028002d10b03511902d030400c1407056042003400940b05004000011078199008100441101001402d55401e260010f000f402001c151040406014005480a4405014101c4025140c1c000040ca640c05141c05d110360381c076813000c034001800501d1003010044691580b00d0a0300c6020a14142c0c128003e44001c002501261031100f0026090049085500c5260b801c205180c24840c0c0d02d01307090751074070f800d414004680090400c04041c2421489681181e010b49884008030b1209403903800054000c0c4964103901c02101c1d00400c0e966a40000c41c4c00003c03004070600e840c0b00041000d60400f030702c0c110000003a0f06000995000a0564004042c542005039071040216070f403a0707001203c60000003418600300f020030b040d81c40e00c80d11140940505400b401900b048035156810740e080d0000295007098402c2001e00344001020090302c0d000c0c05040c0021801d01202001c40e44910803190041d5104044032000f03108a030042d102d1b03400080441004e00d40c2840341c3c01c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 761299829 1250 761298579 761298581
    0x7052112070605071808060c07140105040c081006030c12050316110f180411190905090706171308160f1509030801140d080403050309090114061c0609 66
    0x14501d489507001241d14540050024030030712004161019502d0381c29410001c1031404582c540e000100b07411102d0b42c54140c0c0c00d0902c2401101c49101001e986071508000602104003040000c2c1d68101c03080e00c01c42103a8000400c19982d25002c0030b00b0f0094000e070100007010a071480d2054580c4101c05903400c140b0950345000c600c800b4200c013030b50031040c8a0100030151400400210240d80c00b150703421001a80c00c1c3c180014400d00800040a0301440007000070bd030b82d01c40c01c461106250414101c0d5800307440d12201c0002c1d103015160034203a4803400001140d00c600810101d00000c078a103004a9007680e0740e076140404541006400c0e0b0f048401081551941d000442208170641d0003030140c40d0590350940703000404401090440d040b06480d2460000010342c3c0b240c2910b04490000b4282c82e0742001e00b10010b68803814040c2e008192044c00100002006400700262510302c0741151903aa10360b98030b06100c00500401c100880d072000040084c86004405100f012207034182c10040010160f44541440c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 761301079 1250 761299829 761299837
    0x3020a080f0705062d0a06050303040b070c05011b060207021503130203070503011a0909030903060717060301020f0f0d150602010902030c12070501081308040b04061107052112 77
    0x20010703203000600001401410490943c0203040303c000742508500c03c000c800e1407440e0303008454114096202c0855075081040e000000604001030503250344075560301620007640d00c2510112602400b07110b0000e42d40d07009000407034248605c14171078950444107654250003540060412a40305c00116071f080d10442020002e544901450211148050070398010107181c5040c940c44140300760b040c40f099082c0680e036400032194038201610f1b01a40d0707445030701e0918254004c80c2c00c0c4581521400d0104282d450b1b0050920b8900c0c41100403012030341c0c440728185402c0c2d10842e07040201405040180e549071840f010700902c2941c107000b82c0010030b400e44816003414852030f41c2c0001c0c0140c0d1a400001c06500d403d0040b1075000c07000310703550311034540b0881440c0d0300c420142c4074890500c003409000464540d03007014070740b041766402511140da890b1500170303101c1075030814040c00002070041200480c8429000400006461000702082800d10124550240a0706100111a16801500c103510340120604000d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 761302329 1250 761301079 761301097
    0x10080709091d010e06060f0f150316090609031a130c0602061504090c0e071103041e090903140c0f032d0310090902040b190e011a1603020a08 62
    0xb99202000c0c1502142502c040c01e240994640014060004658030f00101c40056241600ea0300c060192800000e1800a0724000d10701d038420001040000b881071001d0091680c5a2503100e10202d99100e8008072a1550b0a001c001e2600c001800d1107403a5410001c0384607440715203101039a10070b04240e69000c11840361903102d400980c0c0301d00d060110200001075038101d49078041d5410031288a868440e098444218851044d10030300c50f50200d50054442d020402c9210f040034101c90f030b0b07240c0da0f21600c480c0301c0e082801040380000c814008142010b850090000c201e07050b6580740504070550a0901c0e081d40501419201c85c49080320380c01020074184040c000c075039408110700c1902241c0d481e40d040307502e41c2c0f5162800e030f280041040003208068040494240c8100200009507841d042c40454002c0000d9816030b03074020515260103100d0480c50358020140ca01060307000c810307030342d0b260018182c0c404001011a0b03013070000c0c03111000c02d1020014082d80360b806841128001002a100c0c00c03200d41c403500341 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 761303579 1250 761302329 761302361
    0x1030303050a11070206090402040b130e010e042310060807080d0c260918070e010e010906050906070602030f1f03020901120203010b040216150b1008070909 69
    0x4105064062060641c803210840090080c10008030210250307100f00304009121b28400f0420000740e440f1503049d03401800c244004c1617540c00e4484030404000741d0910405010030388590004c6681c00c0642e98044c0266406508100c0e000d04070022a1029110b2101a5040f0310882c41d41c006401c405001c2c000040c003d84020340402820586413a050a0840d44c212040c0701180a00c140011009103504400307002c2800058003e415222030b41e8403520407505580d13800341c03065007541000c18502c0344540c02003038651a00d00110102c00015151052516000c41c0410005041040b440c0d010f600100601c40c0c000302010b02d049500d9840900b2030700240c4403007542101d080200440c00303802100c3c0380a00200b54800b05c541a1555000a50042050003900ca0241d40e071f0081004540f401d4104103a003110040043d511070400448901400c203203807400752070191a000d021142c00b84940302c2c00e8400500a0700403106131a00103001d50340c01c0b8020f0300c0070301000008078000641d04550310604400d0340b440a4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 761304829 1250 761303579 761303581
    0x30f030e03120c0609123403030506040507080c0412021203070303061716140d050708010f2d0203040c080106060825020a02040b0604050402070c0504270204051518 72
    0x24107450604e000b003d010042d8801c040d00031001b404070090b0b03101908107140603506180460300150b40c0c2c0d4900b8044001c180e048001441c10036400d90003051159000f55020802075403190303021a1341d040181c0b94100951001c2006205c0c03c0d1103c208450380700d00141001c80c4520000e8509440c6620000040d40025a03800d81440081074228a06080c00010402440300000441400043d80c8061186c07004000c0980b403524800c2d01e031048640c0d1119000f038152101d865a80c81c41c24080d01c2132000b54588580350035120240d441340140e070142e5803e15520741861000744070310480300a6001400030f581c40d240c40540010300322024012003000e40f1071982c541d4800d041002c01c000003c2e030074103a82c0b502d009a0403102110990300241c1e982903142c040b20301141f94603040e00411000e02c01c1e9002103400a000250000034000c114203400304464041e60b00f0403010341d0380840d142444108000c901d0003000c180d0042c00251601d5001150041130321002100c0d26910310000a503c080302e640070703841d400e40d050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 761306079 1250 761304829 761304847
    0x2301120b041e141608010e130605090c010206070f0801030f020414070522030308130c090c03060311010201020a05121f060c0209070212390a1106090901030f030e0312 73
    0x4460303a90080d42c02101d241c13442c0c0003408007820300070050145800080a860001c0e0917001c13109290760900b504280c0420260400b41c3c9181d8591003403100c1c15002d0301c91071000c910310504c00c00b00c242699030740390b8515056074215a03a102003a50302c0039003a82d01a855607130070490381c011f8280070b5000d60074030f40f80ca03503407212007250402d45008010011000180c1812040020a400c01041580081c000e01611041e0a251030000708408098100404191400726022401c81e0181d120406490180546c811340045503801203080c0c2c4aa040c1400000f0002d000f00310031480324a01d03c50300300d00c40514000b0b140210036250141c0e08040e80c8040b0009034058810825402e0681025421280d10320240c02c1003001288601424071030310740500ca18024040091203c45070b440c141c041300160000150031070481260b826660341218290a681da980c0d0301d810454540f40000031034142523005048024141c2c43c54580411701d1244031410b5041c03010031071040e245030350700f072110324113a2050707049241c0c65095203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 761307329 1250 761306079 761306111
    0x91401090b0d0f0b090a210e0a14011d100503010509060406231906020f240105040207020319080c0120090f180f012301120b041e 57
    0x8407400c0d80110b140c0002c400115040311400300403180c0081e4804001e03156030410707034a003020000010705002c00750b00c80ca00094010307010018010703403240d581130082100d080400592014038401c809210301c90340c000b840294020a8180c03800c52903112007181030b00c10480480c600c00d02c40b00a04001420000050003685405105550000f10564007044200c0c1010000d400448001b10107890305808415040c83c0346d560880704d80780001d9121000c80e0304a0b91079a000e590b03041e21160803100d6015000c400d10503112071402c40140074403e81002000350f407170f0a041c04000d5220310001c1ea0903009a012504030141100b05804a00f03210fa03080325543e900703590f07c01e07085518001c102d000c00103406074000c444c0300c0707c5401c2d90500b4004603400200300358800001020300e40300d00401003550305042c1c10000c020712501d068a040b168030000700480c0000003400403911910b65880d59010400d0750382c101c1420485680700b04110080540001410308a10408000e02d240c10b02e0320301d550940700d0004c1d003584288 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 761308579 1250 761307329 761307341
    0x20a081c05070507030e010e0a1710050601050c0c012d0f02010b0315010504050a02070203100207120806061b01060b0c010b0307150518130908090907180e0c0409140109 74
    0x120b16056084c0800c0f958020840e1162003d8203040000c490030541c42559070303d4034030001304000c82c1100c402581c884002611101d0f41d26107072280d5881c20340000d03da54054822100402c050344060019800c443c030042d00e441401149045000101e4401005040504110411030703240c03e07100d2028010500714028250f0702d03110803590094014140c0071014045140300181901e000b06d40c04925079032145a088000d000c1c443c4080d40c50300c5452a41c610b540040d034014030324030b80a01005114072940e180c007690354590595040d900400308015500c42800c203a080004803030320000c0042100b030780d1010b00b200d40e03411007000c035101030350b41e900f0119044c501009034400500700d0704807070180000400c40151040c0911902c0c0d180b90400300f42c6444642c0d031980078400301c0c040486000c207c010110308010840e5048150b10301e025040c103034042220f05005480454500c0b100f40002f00600d41000c519412624001d45210301c190000e22020610b04042c0c00b500008045c4140c00b142d06616110798501a0b0701 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 761309829 1250 761308579 761308591
    0x60e090604150506030a141f0b03010303080103020103020318120409061e2106022106010c020627090106020115090b032e05181e1903020a081c05 64
    0x3140c103403202c0d0264810010101283c000f2100d06489a42d0161020040e04801038001102e8507180100102c80510000c076881d0042c8128920391840d031284003288141c8001e02001c2d020036140401000151300c0b070340045911030b00080c0c28080481500030180d1810304a9000e500310f0320701c04074052101c50413500c606402013000d42864504186003683c8044405c3c0540160030b100d080385580700c00023032042020000660340c0540215561a20358054025199450081c540b0b412800c034042085907205400b4010050f4004220030701d440ca81c0860315425503080300ca8400504c2411440a0141c4d60b0203080c80e000700304540011502c040740d000e142c120843e0680003280310501d000f0a010b20394400050403108018203940d4014890300819000700101c0700d400c0ca60200600701405c11002c1c46c64514000321605045084842c2c000d44640c54446000500011886c241d10400380881c0c440c0743e0520141d10030703001c0c0c01900c0c0c444540e6185c020203903010315041036200e14403031504141100341d0301c5141c1d4814 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 761311079 1250 761309829 761309831
    0x80d050a0f15051e1008040203030c03032505070213180803161e1b0311010f0b120a0b160c05060406050402031204050d1103071814060111070e091501060e090604 71
    0x5404d200051039020076070000c40402c5141c2c40081c085407420400c071003094a20000716a100c0c50440741100e2484c1752094071010362900c3c480407255140c003800c01d0780e03141c50b0300801d6803100e148903039101d0009001c21844206041c0c50f020400010840d848029409001500c5100b01d420882e404083c0c0b0444154041c450b0000403410001d48403907100905620898449244207480903043c24222002408134858005030351030501507142403400785c3d0080b40000307001c0e256080d8015010a8a686030002d90794060304004a80b40003807150742c1b40f02c0306030500c03240900f080f00369451180c03582c40c5081e40458040303803115501c005102c19842d0410400f00000402c03c803d924141c14000401c3d404140c0250050449070a0001d09006503000d00400c0c000d0100420354200e0740b5a103034031a40160440c00ca9040c50145414003190716544285041c01181c00300380d006042191130075664400070040109403505502030784a94415801042107003d0083c04141c1d90782000605c0d00b41001020380014111034860f03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 761312329 1250 761311079 761311129
    0x31303200609060a05030703060e15040e030a020a080906040f180608030307052203080f1c0203011202090a06030b18060f0907060c030903120f1209080d050a0f1505 72
    0x2541d50781e01210b141c13080b2481c1003030b102c0d21464001d80c0507000580120003a28905070401003400703241c050080c0b40800494040c4004a41c079600c060f00c9110705810400141c00040c0c2e10808688010020f000c81c04c005850720b440c281d650030400303015600c030741c0040c0c0e00040c42288035854810039001d890080c2031407030301545c918140b00c003001d0300724420260003505581820400000041341d8007201401960441040c6649100c1150150156402000c02c82035204c1102d0120000c0c0d022842900d042c1c030300c4494040c41182c4260204001854018441443c1c0340d26101c0c0840004c1480c00c100c0e020700301d01d0302d000e991074020011090802d2001840d401c10041e28808004048100240034403c071487ca003013140301c9103480d0a0803074483d88181c102401c0c04100c1c0080d12807540d44482c0180044ea500d0303580c0c0e00b0750414280b0a6003078030080c1d030300030f41003800c24440b01c00d000b62030341e118503085040081c002032480c00c86040d600c180c03903072404c02610b0480c400c0c1d0100b189040405054a9465100c1ea040070b00d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 761313579 1250 761312329 761312347
    0x12020120030a0318051b0a090501080a0201032409090b070c020d0206031e2d0408070312091212050612030d0b0f13060510050a08180313032006 63
    0x150703004809882c4100f54031030040240380c4d1812249484226009019224107008002c6d6060900303c00003102401103244401c005120101441014141c40020015080b50089600110054003215011300d41e5400400040c03061072803002c542c078004011100c00840c0c904202c0c00c0601254400400240511034126a00c00c01a6120445146041e5044070420f0302d0340c8402d05102d540048440990a40c45400020702c2a50006c00300d41412080309035400400b28004001240b80c0c20b1000d031002080c09009000c1c441c006406507115440071540c100b000505681c440d01c3e0821191000c2c08400003050301006c01c24101039403401b41660040e03080d100c0580341200146c1e0309540c0d228020102c40c1c0d196841e003071403032589c0e11a60660b943c4080280300d20f22050040500d10010045071045600c290810740d211038486000f80c040c0c035590075440c1c90f1450560359004140703c00685000ca510500e0004101c040110007094000d20b02840c010403059012802050981003c0d03110513600500c64001800030300e02d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 761314829 1250 761313579 761313583
    0x81c140307050a0c08090a030602030405100b150c1507030f0e190f02040b090f010918030f03051315060e06030115150c02150702030114010303081f090612020120 71
    0x1c40500318030342201844d020782070003150350045440c1194800384044c000014000700e6000b80d4003590041080d20029007610064004843c0281c04181d0864134640c040001004100050582c0140100a550b802c4001c08a43c4d03990308812280f060100399180c2d0105007003001803041d40e0006451000600c40e100480c80f032540f000080b020002c086c244407207034003003c54646030012526200d0152175003030f29003072141010f00079042c2405074840c0c840c030740041400843c8191040a61003909500c4101060000c810110040d003030003000c25070900000c94051313001946a00b4990342524540c540011103608009485c401d042e00034040611a80c1050790280c2c00c001030000d800e040b03852205403422080b848410540e481d4a400d080a94004801c0403030303107510b04003440105462407081780204448030201203560401d02d0280005030020301c1d413100181d408a94072032481c6400b007130b030320203c4240e550340c0001c50192030341c0c2d4000548070b4075069006011942c00603409104200c80d02c120380b14084200c44510703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 761316079 1250 761314829 761314837
    0x91d010e10090c0e16021519020a0509030f061f0b040902130b0a030603060c0c0c050f0102030f13080d050309060c07020418110a0b1e0306040204081c14030705 70
    0x1400071951000701104008040c00c4090040c1014040100f032031400c0a003ca0404c0c40c9665204054022500c00507408404032084510803203840e00b0091903070643c540c8020007908401c2d00b82007407010401c00e583d120b41d020070800600d46111002848a89400074070803180d1249614003050181c203502083c000c2a0312030003514240c0e03176034820060b1146c3c0341c3c000c680c00c0f614080d403020541905c0083c21103005ca03450f400000941e80070764000d0005804454007141c104222000180a00c41c9081c420f120a2400c50a58862120144116401c0c500c010b4021040d85c2d000e0034030100102201001000907440500c07000513000f100707042c00383c11450110420342e2030f03480040c95040a5440003c600e4115a10b99112020854100c10354520109452404481007104151001d01c1a41000e0300041e11003042c0b01101e100d820794008170300242c229080043d5003904041e103103e038003680902000c10000d608226060b204044a501280d014100d4100900200c09448103d65125410810403a49681001c111 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 761317329 1250 761316079 761316103
    0x1605030c090a090c0803030a15060c170f180a06030b0a210c060e03011a060d05060d02060f19080420011e050904110a0215100302030601091d010e 64
    0x12500c0d95034002c41c0001000e10302c1004201c0c00324494042910300002003d980b003541c20500c10407118086e040c1d400751308401d6108506c00144110300f0240040d0380b2048501580d41d9095205080210400022405400041c10314407203561080014500d8601050344000510b074600301000355080900c04100340e480035000300c1e99580c4e01a09056440c0c1100580d6088807904500001021510f03444020455135540c101d4602c01d600340000c04c5000041008a4910404018044c6107041c2c552003454026010051980b64004000050200944c462000500126106032913440e6540210058800b00d05025881c00080041e04420031000415000200241c1c030106030b82d4072102d8140f400101d9501c004600360440080072581e002460030b070008041c0c1180001141c00703102d60481c1e046951140c0c01a0400600107902c000c516816a5001c5180380d034001000300d813101205500e030b401281c9081400e034030090f00310360ba80501c42c28802c2c2d04c0c1030701880100d96900901040d0f030481001503450883c0c0344c0c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 761318579 1250 761317329 761317339
    0xc0314030c04030f240f0b030c06270301140108060109150909060e07082d100b01050c1f180b070807020f0106080c1801060f0c08090913051605030c 65
    0x90350030b000a41080035620504c10b0170030b02d0f880201562081c0609500301c1194001405c14101040b58a000301d04a08200c1011f05080d0600b4010188d000c824003d04592091500c406005e607212a00c080c0100d0201d010306023003400180d49000e02c064a40b000581c003416a0501e041e95074a01d08101e034810400300c1e2064900440c13070000c40d090280007050000880b0701e4a114241d0000b407003400209040001c00e0b80454a5085a0078903108a02e940300000255002c9400482002d40900842e82c0944190941807424904201b00c081184c0e140410300074907403200c41103001c50070041d04914081c0c1394503001c94003003100314154103a98101012501501141c2402501000501440c1c0308100d140910041c5030000e000155a80c0405a12051081800ba0050800070ba0201da80003c6011460403a0002d82d110b8103c44500c95045601c40e56031307407003151443d004000d80340680e9560780c40c0c103004900e07100035040f8003400d9192407442e120803002500401ba00191040209690120700d00038206d0040e9a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 761319829 1250 761318579 761318603
    0x403060507050d0216020f010212090d0c0b22060c0b13152f030907030f15020d051005120a110a030b0c0d0510030c06050703020c030d0c0314030c0403 66
    0x1050b5524010b0140282070588045a46880203856881c8104114002d8501c007003550b00307034001244c03182100c2c1c00e164505082000340381e640f0f06104182c005050301400c0d0030f120054845020010035808282620040d00d00700240316508a48010020020005802d00c1802e0641c180e98038031003044020070030303800350040e04054010301c221410b81d41c1102211000030816116080f030209035041960004000c10030300a420000d181702400101c034003030389440004004984c50342c0c0e2004810803908a0444030340440940b40d2480e0800340c00541131215034500040350a01d04120944100c0107607910540c0709001d00083d005040801040d00f03000c2d107401c0640300c0b50107442c6401240c164009603000a003004040010070000302c17141005010450014400ad000700c2d04c60725800521203805010103004165403050400c1510f0103080207189003031203170050303c211300390507000030342400030003500c500c003203190b50400204240d4071074040340b0406184081c043c00e504001c540c1e1462401140001400c0d112450 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 761321079 1250 761319829 761319841
    0x1008010b0c1608070e0604061a0705011b080403020d020a030f1b0f050303060901081b10030f060b040503010c0504141507051b090f0f0c03130203060a05071107080304030605 76
    0x44812441d0081c2d25040e902c0455907001c03003682c0c681c034034801c40d140b18800c003010818502d02801890120382c03007080d0302c0010026103084440294801031045500c1d641c1c52a40b40700c00f030318151001c0b11079082501e900b0303100e20381402c0103802d05006a80f424110340051101c01c001a8004c0b4441d40341c000280303480d40a000d07600584c0c403107001c425000904500304900605080010020045218440470342c1c0064035640d0f6106015a41c50b5a99404000b03102c07010765014140c141424a9480041146004201e08606054a90460303801da00810400340d80000c06010a041c2400388050000e05842c3c810301d01b600e85480e00c40490501c00900707200d0304542d0504000058883c050754401030300034040c1c6502d020003207a40c00c406014102214083d41c2c869001450706000441501e204040680841001e0350f2001c500c0700d01c991005107007000c0d014207605040c015131010400e1510800420388001240d0801d0000a0300c180d22a09090b01e0542c480c0e0001d00c20b0007004000d440459501c0030700459a500ca030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 761322329 1250 761321079 761321083
    0x106021c0f11100b01140c030717070813060305181f0e060a05040c090504081e040801140405150405120d0b04050702010f0608030f041403101b0e1008010b0c 69
    0xa05440b03001c03031007500920f80b180900c5a00220610300d003600c1c0d002c00c181c07405602000a001c2c104d030407000e640082c000580454041d4030360288014899606901d0034141d40c0d80c040d2240c01c41c0001d00308d441074240d000e021b03468040c450903030003614103600c4481411840d0b04150351888000e2002003880c000b1844050a1079042d000b089010b00b010080e58914503201590000901045500b03130740f036200c00c082c006010386480c81014029600f0100f298603001c1c401c0d0030303041c0d01801c841501110010070400014444020321503c82100b030488604449070809080c0b240c40c00f80d0300d541c00145d1361040e600344800110300141d8442ca10070b502106130b455600c03a8407031600070650812615009400c200c01c0246040d419131203c40c204100460401c012502d55121a9030b0b07025001c6c42030a500410070050081440b82c4000004c04031000301100d049080c403a80384020303101c003821604900c40904040c0301c050b6400c49840c0c5020b102c01e4912803075100300f07000020940c140c184950108c1000001d81c07402e400c141 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 761323579 1250 761322329 761322347
    0xf0b041710020c0a110a03080409090f05030c0c19060215040f02211605010206060409060902040f020306272d0f0709052d01091701060302090106021c0f 67
    0x110000310345500c903a4508544913881c0250448140c0800c8141030024581410440103030382d0003000d8542020f0078106a00001c090000c0146d4039441154004000507038100b0080c99003540c50703c00317010400a03185c00e1156244880d6000d9a88902c901020b02c05254006485140402c6603c0041c1107500c4074100390405100c2c1d074401030f40000c07050001080c8080d4000e40030022a1041c07084681d400c0c150006070318a40314070700602c0e00581101c0082003aa03d455040b19071040d01414002a02120320760002c1d04070350302041d0f00c0c0103958020040240902d45146025207445c040400a018180301000706000440300500d101400d1199040c2ca202c0c8a100f040c1c0c010501c40006960441d609085e80f1445000c0022695100001c3c0380607400305960401c95100c040c020054401c0700c2c2004030030181d508100d80e00b1a40a0304000d0003140c0011030b44040b081d2182c1808840c8000a0184d0940c010b000c210a0160014420340d803108844043c55060001b403021850010b251590b4007c40d406011101009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 761324829 1250 761323579 761323603
    0x4030c080c01110711030a1208070921110105031b0d0204050603040b06040b0a030201120c140712020c010804020f0f040f0c120629030a06150807090f0b0417 69
    0x8a0403c030750310740c040d04500070318043d4010721034201d60250400405985603210742d401004860301d2007a01d0501070080c00c40c1604200c03030703081404031252a81d408051801001115166410403654010103201c03014540100104007840e02a140d468983d0262508010000081020ba140014202d540c49126810303034006e00fa0040910750340e8101414115030100c0300303540e443c5c4924504950121140707008070307000341182d5068407207020304480600a207009120455000c402e0002002c030a1500802450060185c14480cbc001002405440c001c02442d010380001014180038290042c031000d031b510806140c40c20001101e800a14614030b80c00704018100d0540c99000302c2d03081074100001203820022030350131021303c860104074081d41d0740d00d0300203042c0100c010800c0c0072030f40c01c8164424106c0e050041d07034444100e1a01260b071998612131b500023040324060b0540022034030018401d901d41d0184006004100310801001404c6c2440c0070a1b0140c4114460b8440c460410448400040c1040c0038a020000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 761326079 1250 761324829 761324831
    0x4020310110904050c130603112b1b320a03060e0906040f0201110703020303160303050f040507140f060f0306150307080f071709030d061d04030c080c01 67
    0x495500003041c40e07040014414401c0b428900041d40e448011010346580c81c4013a858480c1c1246000001c1d0002c00075090700035000707001008500c900c40711400060780d40b1804001c141210342d50000701d8030308948102d6488606c1c811030101d0207000c158080821a048078180c03035201d1703500c040d840c54004a080305d4490040884070200e40314080740d8259006108650401c014210103545400d2650f4a0380780855008145200d00b04400015500c150440380c003130000ba81c2212085502d81c3c00203807541d000310303904421400754a45480101a0305025598011444a000a07214101582c6c3e840d200c8085001d09002c0d81c81c850362411491f40c33028125445101c0107000c0e907644101d0222a61030617403007182c286010f1032819041c00380603203940701168440c003400e0780d500615484800108681d06000b41113842080b0001501c902041ca200b60b1040c003c244900055907242d4010010106482140e4821240c0c01c040c00290081c4118074a05141d0260349850030400703050300c0f40381c0a0079a0007203243c2c80e0029 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 761327329 1250 761326079 761326091
    0xf04030e012003130905040f0f14010228081308030a06050a030c170d1e0c0506150103060b0a02101d0a0809040b0904080a030b011e17070504060f0804020310 69
    0x39020203c0100741e0549030b11078803182c0b02d40325000c80d415504181d900600c080144007640b03012036409149000e503148503075464441c44c400c0c12605820390b001444d841c03c0c80c0b0214000c550350b020900f0b55912110300203007441d40c20741c50020f5981407280c01210002d030980b440000000d0341c003603240d44140044c190040900c3d0301c07282c890900c0d018001e030300d028884a0075850708001c601e440c00003505c49060011941c03050a00c0e20360111130000401c040041c03005100030f41d1301810018005203e5203100c0c00ca07c5c030500100d41140303030004090f10417036401422030740004c22400d5186940412083c681d0541c2000c0483d504509207110440c1040740446c0c9201e9010710502c0500b00110705c401401e9203d0111000d1020350104010091400020344e0010701c1241c042128401c0b0a000f900040c046100c14100700d0340300c5a010a00e03000001c0d800c481d1800042c1d92803040e81c3c05000700301d101a00310704c1d41d2424600b040d003000009059085003040c09414014898000b40440d03500f04104a07510130154024445 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 761328579 1250 761327329 761327387
    0x20d0603080918010b03010b180d060906050c040b0f0306190f14030d0504031103150a06030b010b0c0607270b0a021b01020c041e020f09180f04030e01 66
    0xc50b0828181c10b03100364242c0300000e41580078845a507069178102d08103207186900c4e0640358001c0d03038000d102946400000c0400c10800e50742d11400340310703e11f0046801084455040c6001c004880c001401030010101c284010f001e404502400d84607400700740b4901c00e80c0c82d128a0700080d440c900b0340f1250740315081401404a203522000940004440c50400d1240da2401c0c060101138136040080c0d0b40c3c00004405000400202e06030440002c0040c602800b903416001d04c1780030f1400d402d107041f149254510b850302800c1040002c070340322080c010f0115404050411080361a016250500a0401800c00c43d0744c2038184488604407208000c2800240c8462104a90ba0345100340c00c1d0708010341c0c450150007140b4040300b02c01d14039042c108610b20140e016290b041070f5001000001c2c41c2d280341108507822010782c00b00c21480c2d00d1000300628681ca02145407240d03002020001650f01020413080480c0810052006044040c0d01d40354006034141070643c0305c4c028030f100498000f1001030304008a04c0001000b400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 761329829 1250 761328579 761328593
    0x301021c090b010e1501120f0c020102181504030204150e0415050717070305090a021305150d080304020402160206070b01060806010507210e030313050a0f050f13020d0603 75
    0x521881095202560f80c1d03144e0405900160803200c00118110f40c00044102e98031400100d10201d800a40000f2001500c40c0034104880c4410b0001c005070398001004110070405150310450f2060440e1032001c0385416240e500c1b0130303010724440207000d04d40320641981c0501069130168054121070600304c20718981030401d2280c60390140c0da40070f0540e2928001c50b1400d807013040440c012000400c0c400380c20392200c0701c0860060a00030a1b8100c81d00a0007024401a0b950840001d46101b4224000c01ca42c01c01902d588517618118180520a010700f05044001500880540341d2083c0c0440e070040c5c444241c1c621840440c6070001c002940702800141090402006800d8181a40c40d10703500c185856460400640b144c0c0310f40c10f4050035800030800c40c40010b4000c4006407221030518075151586140c00c8000c03a1450f088800c01c1c5a100d01710510511042c140882c01100a1900ba5005070645150902080003030f04440e4855020b980d00640350341c0084001c0d0110364007440b6051007001421f640b424406 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 761330935 1106 761329829 761329841
    0xd050d0c05090d0b04060b03070308040e0c0406020d0804030905040501030503120603011e0b1306030c29041e08030a0e211c020f030d021801020703030203090d020301021c 75
    0xc50548c0f021f00c50640110701c103040b10b43c0c650b810251a078001140044c01c805c0c105600740030401040340c0c000380500e0072040e00d0628021648480c1821248401a50841604903007080000020800004000d120303503090480d074084640c4500040600303881808120148050348006a15480c04459200001d5000d005046001c2c803041041240c2c10348040d0b502c00e07220040b004101304070100c08116640f00400c1c03440740c10b8403202080b82c82080301d8080d80c02404400c20051400440315900313245000081d108100c101c0c0c2d2646182d001c014110341d503140d8240e002d000600c1e42034070004507000e00700d207035040084090014000c0005518002520302203030042107102d40318980c81440004d000404d409040444096903600f100e2078090075840038100101d04540c80700104102107a40801602e0714004122107590140c40c0c5030001034003a00440b01c85030900950071007100c0550000754041 = true := by decide +kernel

theorem cover : BRFrame.Cov 761151079 761330935 := by
  have h0 := BRFrame.cov_init 761151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 761151079 ≤ n) (h2 : n < 761330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
