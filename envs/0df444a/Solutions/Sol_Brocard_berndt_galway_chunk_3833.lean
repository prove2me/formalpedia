-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3833
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:49:03.098081+00:00
-- url     : https://prove2.me/submissions/b57ef8d4-ee08-4ab9-a89d-9d22cd093657

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 689208633 ≤ n < 689388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 689209883 1250 689208633 689208643
    0x50709030803060603070306080d0f120b0607080c0723040b1e19030c0b030613090308010b181207080c01020a0f1202150a0f1a0d03050d09080c011d 65
    0x302a01240040000a0031070401c40003e582100281c80c0005d4656900c0c1816810143c1c4284003000044c1850700d403544465101c0594485104102c0b8100484441d80000a191744078040d03004000b403030045007480306d9080c103028100040a80c0c82c9a2000d46d1040340700065115114000746c0d20a03860710b10103841500f4582c0d141e07103200c0c1c842c00c8500300c3c420076001005a5910b5044020166414000000c8005614100008001c283d4036840b541c681c02d191080280d04503805201000781880c0120180120703a03c42c8403541100c0440203400d036901244802540c0c82c40b15450701c60f07040000700d1040f40321807a0002d141801ca4400005071345002882d60700481e22000d42c0d036405041292040d20540104a514049402016003401141c2200700810840b80140c40b0445141154940d214521b2503080c00a0262111140c144800c0101220040e400211100e082c540007804010010aa07244030700c00c42c0d07200c2090300750005441500c40160b00d403498082c00d220f240c000d100d00d0220040c40780103240010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 689211133 1250 689209883 689209889
    0x19080408060112021f0903080319090c051c0b010905060a0b12040c09110f0322140c150a0c0203070914100f0f03110414070c0b07080702070611030d05010b0d050709 72
    0x501c04a01518584400d03101d600301032b280d8041c0800b42046a0b400b9001441043c1c0d03103030722643d8150921840d2100300440030f03000451000b00203502c500240001460f2418207819030700c0201000420340c5800010520b04042c0707070800c240b42c110010b26841002080d001c440c0c46944981c002c0b00a10b40c440e0b0b483d200703441009c45070480001081c03044948885500002c1c1d0390000082e06407410350818040c03148100d8000000507541c418540c9850320301e0100601208400003801e40351b03600c15281a0411120b2403085421140c20854803505440455405004c03203c000d1000e580244268202c00c0e40e2004900001e94101843c295038060008101c03034241c8801007200c003048041c0304918071b5500c882010f5103a50b001302d58016610201e0162070040c4203030040c010030107603841520014207850052040300d8060300d000c05000222003040501703580000c51364141c56031450030518240d4827240b90f82c0795024061803620140e00f81000464660071160150141340d6899800f842070751520a01a40c625140740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 689212383 1250 689211133 689211137
    0x6090602100e0c04050f04110904080d18080319060f03020603041b030213020c06070e10050a0306181b030c020303010e09160308270319080408060112021f 68
    0x100500280206502c826000101c490641c3e5990040000050848a04071a00040c50100300c09000038801030300c0c0c02400e60042070720150218100303900c4520550151030070428003a03844201040c0c10011000880c0811a444400c4503203904182c444689555038400070b41d4140351038810700040e1490540d04400c2100d8014120616544803501d4000044041c4030990030030255192001005881d003038160901c00da0480e10058841071201400c0d41000800b400c41001c00003c0070440c583c27951021201175610740e260900c42c0d0b466180842c190f0150129900c48900e00c080907216440203003480d00001c0418401c454104c1803042e550206070100c50060070400d0043e0f20600050010340307110303c4025005030200080f10900c81000b500c0500c0480c154200325010700c0041616200203007215034041802c1c05658201042e80e191001080e560307850707001d02c0600b02400e5002e00d020f004441c012200a04a141d0130783d140c40d80c48030305218211030b1040c0f040f4007900034016490318000c050b40c80188229115 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 689213633 1250 689212383 689212393
    0x20901111212060604030c09051909150c020109080310080d0914010c0201120203130c09060605090f04020c0706020f0d051c0c030e030a0903050705090603120a1b061506090602 77
    0x9404200802c042c0100070fa60058410000800410000f00b4001c00500314240e0200302c40c41d1180d0400d2560820a2258a555041030400d400041c0c0e200206840c5080ca50390002c0c101030364403000c9015215000014105030b00c00001e02481081c03960280d0709445a82084035203242e04035000700c580d10f110340f10340500c44284100440c001d41c410610f8a0038140145441d1100380101c0000e48101c2e801907601003404c2000092050400c20700d4902c01d002030242500c1080300320700d0140080c000744208501c0920905841101024643d66a81943d04504c802c00031200855100d00000e5a40c0032103c107596844e200f0801c8944255214604480400c1e1242c1500003604400d50b0300c210183c12030006490505896041c0124030210802c003801d5103900941c3c031000d07510302e1802c2150400b5681d4101c1c5004040c11000c1080540b40060802e500510300803141e540d549400f18121100200400c110180c07070750802411080c489250850390550080c1c03001c042005075100340949088030603104440c056081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 689214883 1250 689213633 689213647
    0x1030f1503140d1706012c0103050702070f0603110c0a030206070228030c060f0e0106030213020703080105090c0405130c120903020606012d050406110a0c090f0912030209011112 78
    0xd0f21402c01c1d082407040c100f98000e4030144001401620403852200c2e11f40003c0d00c0500d03859a03260090300c0d001005400600000740c1011030050350030b03d56001c5d64043c96260210341d50103040c01c3c41202c242a1901c01503840340b98070b600e030003900e40340c059918030010320803001030040f00100074031018003440da0314a0200c0d49151aa40666504455003010b0b12416600c0b850032108003801d00503140c0070804000001580c7d81144104170030458004121900240305200c101c0019030800c1d05241916421074429090742d803070406e00c001a100daa08541d41141e81e00803500d80c0500b042c9c1007110b220711145c8560112088031012141200d4980f140503005901c4017021800c2540034a00c290080c14901c3c0206498096007407840d11051030500c810b5002800000342045425404001320740c40c107142401800030815503484221100e03030340c0c1c0545600355a5400d204140d080141d40070005465205000c800f0101305640060001e41000a540c4d01150212000c210035002c0480c01480040f00049004d041c000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 689216133 1250 689214883 689214917
    0x170601030b0a020906250f440c0f01060902030717090d030f0e06040b06030d02061303030c0504030605240a06050f070201021501090e011a030a020f01030f1503140d 72
    0x4a4200031603946c02e80054400803d039005003440c800390050411041301002103003548044500b0b54024031020204454010f00c0640f03c81d150f1010300d500c2090b880c3c46070a4005042d04204400010042c9903103442800100c596113500614401c4443c0d807203910087d035402d0307080c00000d40c0880d01c0c8181c941114140b0180c1501a46c0318080c4041c001100194882100c1e40107860040300780c030181c440d0902c00c000c00c8860710701000101840b414520141159081003808224502e10840009080c5626040340a0707011784587c083d10300841e0000d106003c9401d01030480c41a4040d403005000c4c050103903100005c403034105144020202d81255440a2410036008203007100c3d41c1085d1400c078118014150034013810700356000d440d8060001040d00151441da4001c202d821228512035911100210080050030f50340c003c22004107094040c0e50315a0b40700322003001280201503102c0381c0200f252030041401e99640c0c1c144a0a4140d038440e9001213040708840030440e070b0b100b11030010f200c00100440316000c4050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 689217383 1250 689216133 689216167
    0xa06050d050c0f0403030201020912070e011413050c13061b020f0604120b0f070813020d030926010b150712030b03030a0f030c0f05030718170601030b0a020906 70
    0x282c003880303041c18031000d825000c5a02ca07900a400507034012822042174600980e001c1d22841d006001000d43c1843d003e56220755001c14420822074030425903042c807035074464145000000c01220010803451800c007001c0003890b000006125450300c0f50303031000301300540101d100740a550210300360b02d411240b4030360810503d56500d043c819000070381840005058805d5043c001070044c8039a251280a15210440e40703c0500010300300e80420500005001e0900b001010202015030142e82e0a081c0a07038600b0191210700c215441009460300c140b5080401c240c90809514402640750028001c01320f183d4100417000c07000264010b050f980400c4484000f540441525044c0c041509001c5001f00800703000034116040400c2020106902480c1365400e02d60610448a074018103017000300d401800d180f0001d1003800300801800510611070302d2018071105d1080010003c003111003d03850305941030241113448540c00c0c41304803240c03c6070300d010810081f098001d0f5031700d40340d02130115420503a00403101c5072a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 689218633 1250 689217383 689217391
    0x30a052d01050f0f0f060d060209120f0c120304080601050f0d05010504060f0506041b0807020c06040b040e0c030c0f0a2001050103110d111203040f0801050603010501050a06050d05 79
    0x2000a035200c16281036080c0030b1584106140e043e0003210b071624180840c103d080003441c100b01c010008082103000c0c3d49507030f40e188220390486c4005807144402c4e804510841600d020380da01a100e0201000c03c0c00b880040c02c1c1060740d20540c7c0a4070328030292450503640e40070354014210540c2051005112604122500c07141e0b4400c000c02c1c040300e00c501d81d05d4003400c41f482a541a50700c0e6498054a18259529004141d00a501903c0401c004002c0042c0003018041103400d035001c0284031004200200d20800090707812501c0200740c1c0d07589954400340072801e540703e84207001401c910040001e04000003401901d2080030103052451400e85d001c40ca001302a48000360b09400e200341e000041d0f0043c641606003940901c401c00000405504501b031803050740c540704110780e2103070000405840001e000c031500b03030841d40c0058619854042c02c075880c0e1815806640c0042100e000c03d005c00040c040e8054001d5801102d00703030f0003003015980f55428086500c42c1c6006e4a0086002009070350705078800d85d4080f540c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 689219883 1250 689218633 689218693
    0x210030614120a08130812040501020a0f06020c0304120605060102070303300f0e070b03370207080d05060906090c0a0903020a120501060b09090c03070c020604030b15030a05 76
    0x500100380c4c0c2e5054aa8020600f13419003c50403c506009850741040444040341c28542010f051502e0000000e5564003609002080103151070400c00c10048690150f92902c1251804d484e1501e071509030031218000c850304165611814080480c025500119041055a80513501c08940c5100c000012040b5070300e00c2740c140da02102a83c05684554040d1084640c00c220481c0301040c840b030955100c5142c010588c0268529000400600c0041580900d00880f098901540394129a0310700f80c1c002e00f000d001d6010384040368000160a03082003118802006608031b5680200a0303504c41c0018080d20079011180f09411149603004079400110b050054031103c070840c5020300d15980c50b80d0210348101600c0d03100c40405401e1000f6801000820b0050300042d1285154540c1003010b6100000c04201021b064a003070030200101248002d40316001c0e5503800c42d0007030010b660b640d58a1500c203805210440d220f02c801580a81003c007a40b1340451904020754001008000c1c00303100c011070f008440b15913181d10712 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 689221133 1250 689219883 689219893
    0x130614150114090d0c150e0102030a18080331031a0405010b12011b08040206180d1a061201020313110a0801050a1a190e04080f16021003061412 63
    0x70960388944c0003090240c820781540d94a141b13445001d100300c0f58400a00c009102100d0306d030700001c1c2d90000030b0f52842040d41c5410904102142c3d000c1d041c079286a0002246070000007554101d181030425503101e000c25502d0300d0004e40702220130400d801c030000e010080405203490201083c0180d02040b458000d8001d5000007030049000e4001410003d03030031070f00d02c01e0b45d46130340c00d24407405c40382c4014940100150a1140c1d051400d940015011f11500510b6100690001c2c00401c554441c010311310041c030f074803014190b02d180781c10300050380e03018003107481c01d10445810301c0003444142c06000b9a401110b120304600c100700700e9640d40c2e54000380d080c492150010030303a01c000114444240101d0303000e071004100001740160140baa0f51940f8041c00c2d07426028108400007414800201a044000c031100c407290f035007083e103880ca081c00d03151140d4540c05804520106039901c20720740c080c11180506208440140e11407002c21400c0e401e940719032040b1091125000702c0e0109038201414400e400300c000200f641c3c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 689222383 1250 689221133 689221147
    0x11404030b15060c0d0e04110301030204020f12042001050913091104090804031703090d050a0203190206090c0a0f030602030603010f02130e01062a0c0509130614150114 74
    0x143c09030000340c0d2840d0554000b000c140030307554003c0e00c0c4910700041500c00317100c3c104032900d4a0840c1d1006200090041d80d00141904500c144d0f1415034490350030f1000000b40508050416021200440510401c40000032400310110340c040d031b0845544260140040a0000656600300002d200349030702603400034610b5040443c90750b00e611411480314429041d103902e5a09509028030109446594a92280000c00078062aa180083c000600140d6441c04c190380d440010710481c00c5005080e4800240e42041d00d55020301600071a03c1e511996040c02140c145442c44410081c200350700788600c1200180d491421710204d03403076400450384004040d0001c9046209500880700706e0f8005141420541c0c0c0b0390b68241311454200761120b004040e203281114050b044140145514110003001000300c0c0107202c2203804010183c0d030754070010600201114080d16000d01c0d0f203101042420380072281d2510f80380811250000e9500070034000c0c607413011210030307080708800190f5082c50042c0700801181400e000b04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 689223633 1250 689222383 689222389
    0xf0614130b03012d02070812040c03170301061706010f030207020105042c0703090c12261e19140c010f0c031802031b0a03151505011404030b15 63
    0x604110510242c5201804c034002d8005600040c51684d440241d0340100500d40224205c0700944096620704141c0040a45545c0741c204003950747ca40c0020601d612007030120518086040103141201e40707a40307231005004070244505003440000c907502c9004c02c12210142c84094440c0c1d0142485901c181003084c80c1984941d0780e0200340070b90324109030444050240e400a1071000d0251a90888020708007440903104954565040121034004c010300c0c141e41c280c03000b051200050f14010a4030003800d0059883d034200030040c0d00350f40840307403180003030864039408907a01c0181000c8421500c0801944543d41c03141d180101d90410420030706c8000740d1030500088074003050038443d445c00319400f0300000901000700c10014060380d041c064a0340b030758203e4090141c0541c501060500c0110719203811030798004241c034005100144c058001400340e048801c9068500e103c2036000350424003002c1c2654a0b0303c4d643c7d82c011181210b40040601a01c10140420030000d1905102c035500600d0f60840c0615a00d185404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 689224883 1250 689223633 689223641
    0x406090926131401030e210706090204020d0f05130f1b080f0105071815081b0a0306030203060105121c091706100803040f050d05101e0f0614130b0301 66
    0x40b03c51880c42440030300105613054030070b8070ba07004003d0025101600104d401c01c1d0400342c8500f24007601c2071700000c040c01080718a61004141a50081046454514052916004000d1810260b43c03140c905400309007001620354088140e5603010540741c0003035000d980c4410540d00c804400d100640d02e481c0b0089080c120900010300341d142400700014103460180d40043c20b00707080d0380040d02c00e884040310a00038a0546070512008002c981404101902c036056000f040c62584803c5101c821404964a0b03030999040d00a203003101e008400712041a6250800c001200020502d000d8440e808500d17046903840066035407440b029103c0c144522280d948034407201900710205081802e41d0440000c010b40355003909071000c09007807400010b40c1810304080400030141014001d161003801c81850001c208072042100411010b52030005001d00c1d031300d028000802d1a800c0480f41c0e031142c1001600c510408951240004980b01c10040c0b0b0600b1104c142403200e810380400c0310b11491a190307641c940c0252402d0007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 689226133 1250 689224883 689224889
    0x303021b031c05072109020d0206160b06031209120a02090117010518030a0509040219030902011b020d0206070807210311070c03020f061b0606040609092613 69
    0xa400c40c04014030208110032580c1c000c01c41000d0061602c2d02040d15401c040d2085c94214240000094034000d50001802000d00c00200a50001d4001030110180c800d41c688411000d00c54205542c889e150b1008240d103982816185a1040b04240700056443c5044203c0001003c203410030354001e0051074010901d03c840036000780c2d48140e44106e0641c4500424070031103a000925108010666240114007602c070300c00c502c800d50421402103901003080d03946a0494043c400384040030b0303e088407100d9019000c0d201b501c600340d0226030040104006c0342c01200030700d884180d00038050201040f80307508101e060b4004400c03d80342d000d81400404001034000000300500d500c04256201e000103d20303001015a0014901f00c150a2000d10250000035034000760340c42070700d6040351401c00c00c0c4510b402192290150542c8031454183c210480802514003244860103100c0c140c1c0c040c008a03458114101c2554202c2c07600406a43c009401c0c814818085036414000c3c900c8011800d00c0d00300c80f90041100212030b90 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 689227383 1250 689226133 689226157
    0x1c031407030203030f0c120129071103010617150417030708010305120c1b010507050604080703080a0b010e0409020406050a0806180d091404020d0c080f071b0303021b03 74
    0x5c0c441e40c4001c9130f54081e0300484091000e0300d040801500200212018469111200352a074036000c0014039481d903010307034101c6017603031141c481085042c02c030514002006858040e510700071001c10041440c1c040340c3c01d11211600140b611148412170392901080c01002500d0900321411100908070080740203500540e01039031000c0407541103003000340c01e205c901e540700c040c0e00c1d20030400c1411104c1c001c540e41c003031405004004803000803c0c1380166801d1140c41c8004006000320300070002046020f00141191034000c4c2e60f000c0b400d50300d0002510842c0e031a40452401f1a1a0507103801051400740c000a007070600c0540007088140e91400440c041e540917800448003a00400104480d0700c1c00410b01080444240c0d00400c00c13080c0340500a860980d00340152205038031156640107840d01c450701203e0740d4400701c1c801003100640800e001824801d01342c0f0403003200400600490322035807040f00001d20f0800b4aa031180356101140c0d030b0a1300250b010242401d04c000319040724029180091020300205041a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 689228633 1250 689227383 689227387
    0x105091518030d0c0f050c220c090609030204020d0605040507050a1d180903070b0f01290301140a091d06010906080604020103020703110a08090a090b1c031407030203 73
    0x40500c022420494540e1500030707404102040340c069441030051010343d400602401441145040c5641011f85089a0329000440c0a003a41c8402d400010038402500c41c0b440200300d41c00c1449011505220070344507070b01c0090551503041c40545800d90050400400c002c0000030300d81c0d500d10208056507070885d071900200e90b010540030481500101d85007203013025017003d102e5a414000025040050381000341e5081452840091710312501007045030b500941060f16032005180000540680340401d028040d458842c450100d48580c5140b17801c812000e0030121614256800d101101c440f010a018215500c2100f40c8400258101c0a104030100c030301030600840c100110b03044c511490308006030b101010141ca040e40400bc10000860036a4025509280260b507500c001c0c1000c48080000c5040540f440c05003035020810803003400000c1095071001c5d10b0204a660b5141e032100300711000700e00c14640110003041841c1841444c1d0854044562090038040500b1101050b00c660540010100b00c02580c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 689229883 1250 689228633 689228647
    0x13050a12030b09011a0a020a14010b010906031e0506031f2a0203030a0b1f09060207090e0a0807051f050a06050916030c140a0306170d09031101050915 66
    0x3041c001c1d102c910307506440b21807040d40b42c904040c0b07240c0b2900d00c2c078074850713080401c6610429200740003810301c09400014a040b13100d00c0310542802002c080c0f8000703001c0349244900040d01406800355405000c04c0701804c83ca043c0c2201a90b1028080040c11950306024000d240310300c110040c01c0d040070b011641c54000401c42046103600050340c00c0d28a0b044040501004400c1040e0703800400c40342c4c0014401c0011500881200118914007001404030b014050541492840c01e075003ca481da0407610b4690807142101c6c0e0b510420402c0744c06006025103580c012804800106080078000c0c00c280384124204d40046403a031040b2490190322550718035000d62648180007030034503103000702c00190500700ca400c6090309000009030a8008048484404e05841d240e002c140c040c0520100c01c45000554210355030f1707000400b0024000c002c0e0703014503084414611036001814400003058846416151908000e150441d181c9048801c40301503403078100071040102039482e0721901c0b071305c400803086075200c40d0726400713 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 689231133 1250 689229883 689229887
    0x4060602100f090c21020405041217100308130f0f06021605100c11041b090909080a050f0d1503021c0804050d02030307120207030c06080609010e13050a12 68
    0x74200180c2c24418104406000850902d401220031207260004101026800d192500c5150114601c0a54490715000411042c44030713918403841c28180340d94500500e114105408030803a402510760b10104550807074244009100c2d00024070302c1092000d080c44081e990f8215025483c1401d401c805520030601d0f004105483d0100403a50101c51003008500304c49040201140c070400c4110004000c00201c0c0203480f09200f13030441e1027904000094014890841002a0a800090f028150b8400030741505c20024910500c0d100d0207821a40c010401c80c940140300c04101c2d0705803c80041410405d00402050082816034400c2400000d40c4124018404d1b2440c010811401052120790700703104400ca520200003094a811281514411580c0701e0410803e40046031075402624401000031811490381c4541a40000300b40701200d1207070f0301134480070b0b4452004880c6a202544c600760001c0b000d070010b02a0ba0300c40310b0f01030b6000711845000c81112002e0b846261818185030015030710040b141528861040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 689232383 1250 689231133 689231141
    0xb0904030e0a24030504060b100302090f06130e0709081615020d2a021302030609010b040320181608010501020a02010c080f070c0305150f06060307030e0c0406060210 73
    0x1c4100750298049280b025043d001400e80c0007004400c2544e61000130b010000c466000d100644809030400d803a01c24009005002075120290303240c07241201b44050200d524005044a102c0380c0002c040791201407a0240303a88000c000613040d0760501c03140c501c000c82e5810007080341d0814600e03a00030f80f45400f403402d81c8242203c028003041c0341c1107410a4a5684a5075009540903200c0042d1175001025200c08402e80170b40c01e039416000030b601100f180013100c003888a03500918002d200c11038a40c4010b0b41e81e000314403054403841c44014401e0742c2042c41c113001c100050f40b00c8144480043c00312002502d01307503e41d0300001012500b032444d003401c00e515010910b40c440a0349000d01000e00080054540310f8001801d000f0700c0d41c6000b40845800075041c3c2404103e001540c04e1558400400900240c8a00d086525802015a40c40f07100304420000380341200c41c108035038040c100103080649103803103480c021405400c8061100b1528031036031100d001140c0b650f1059900400c040d070f0150104003883e080d00020340e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 689233633 1250 689232383 689232389
    0x702030313031b0806040b0702120f071104140c130f0602030c060f1e0a06080d0c260d0c030e060a14060d240b0a03140105071106190b0904030e0a 64
    0xc00710002c0144010400040c40c50b0300147c11a41c403c9141d074a50104070311300074050700714030800391004ca486500c0c0c2e1162005031a0262250000d0312030581c4100a101c103d038824001034510422500220b00322140ca040109501d00500340315008c0c46880c0c1c29540c1402d0a82c0e800500140d00019000912500c00c0c454540c1000303604004201505025108000070440c0328011002250342c00c0100349440110f9000c28000d0417580240c0b64484a4130300040c200b044c0300d103825a09440c14521010302a03080c401350301c8050410baa052410030106081000007488503012060a0603a5138605100c03d0404001c0c1c980b146058440214880714a40062016220003800071402003d01410000000e103100080e240c2c0720300b011a40501810045591744007602d02450510f0b04450aa000401484010b4206d00d02a00300d00e0300900c11a2100c940450308201500038007a49a04800f02081d1110312070081230780305000304175010824207540000a1482c0c0010380302140841e41040445040e400c0c69800e203c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 689234883 1250 689233633 689233673
    0x705031602040f0506030c060903010e011406010207150504060c0203160b0310090207021c0f0f0501150602030a020c060c0a17070203060112080304030f051c0b1903050a060f02070203031303 83
    0x4c00c1c01c14002290369240da03101103074414940440c2c1070210780c409501614400003120020f01403414501c1e04003400c00816070b0002e0041c0984040800c1001c44154801c4000ea4170f5650070385041d14000f011260025103070070403a03040c064511211fa0307500c5d000103900050186503d001d952801c10f001c011038156215885003c1d2140140310307100c0075980320248802c46620510315101c54002c10714080d54510000342d00242561041e80e0a4000e000055025084d010303074200215481c651201c0043c5e0360384c0540182d1000581c40038040c0c0c000303410b200e005007a2100c02c10301200c0c001c50f0700d43e503501310842c1034040c41143d060000c150300c2c2c150328003000454010040c06030b07401c02c1c00f1000d4403500d6541c4002070024091100300042c118188d480b40080303803035011001e031480b858042c004003041c02620560f0800c4d8840c3c0d4800f00300c00301202d4054080307000c8aa0040c01090882199075651002d003c0941140d11825824083c41c005620184001c010100d07100c514602445d085203020444010b800141041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 689236133 1250 689234883 689234891
    0x80a14150f22050a02120708090105130f1407052101050105270405030d0507080a050601140a080606040f0e040c09060308090f04112b1a01050a050705031602040f 71
    0x85080b8002c264840100040180460269146030301300300607100b6040c4464154146504100d4642d40c0700340914014040b4000903c00e80d114844c40e85088200880040c0c41501191181c000080f82c1000110f60080b0390800d807240e0b15503030780004100c1d406030401c4004030104c1304031440c0800c84c00e20a690242c2000c469103e040d080c05910303c41080e0a1000389030610781c1002c00b16082c04820001d071060151808018004d911300000700512654080e01c145601c0c90074000030400d20741c0188800900e8003481461a41000e07030000c401c4554000c042c20f155040701c02000082100500200030101410030041c5210f0b88bc2020300d050720407150550700c015174a0b4600041800022011000c036061440c0c02c81e00065820b00b0b180000d002000341802030780c03d1300b000007400b6020144640c0741c82007044029412062001d5a0250207096075400318841e510440c0032664549550701400240c04610a9031502070b007030240300c2d61940c1c62b6600c80070140c010802400074880440c0703818040c081001010078cc0601c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 689237383 1250 689236133 689236159
    0x306050f0f13030903302a03140307030603050f01060f1512090c140306060310050702031b1606020309090403030b06071a0106020d0503010f06080a14150f 68
    0x802001e070007600841401c100700040c90141840340000e07038007460300a24508903809100c00a810f804040a03411404c0038154880040424000c400c0303940d51000d104000d00100015030201c10b0549048901141805107880c60240c550361058041e501c609182d40f0001092410350078070f1898060a014004d01503810700e1814070201042e8004001103a42260001d21680c00311744040e62041e421044118100c1d01e402050010302000f08000707412102042415160410008241501e41204a5500350541d118903000074000c83d96900050b8000315070700c10fa80c02c3c0a00c2d201041a142c0d000310039560103521116283c60039100c00f00f8050300030034260005501d0490030101140294400a1024043c140d980a601080341c4a200855468680c842e0030320f44020300104001202813030030b0050720014411350503444402030140c02128141c500041c4807010203880e004c01280d00c6070004281d20f01e1551503107040300c190316091140902a8822038001080301d8107105c140a10030369000d109511840020100c6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 689238633 1250 689237383 689237401
    0x1110a110907090e072d08010b070501060b07030503010f15021b0f0d050a060b0105120a050606090a0303200106060509090a0603080a05130b042114060c040306050f 72
    0x100c80d004009458990031690b8500064400301259070010a00d408a0000c01c8000340d030251490144600303a00c85070318102c03070302041214078455215540d8003042070b0b54014810101040c0251401c244200000b2803072903203422594903107401c03d01f0114045540400180050528119020081d05a9186038103200090090003552210004142070403800e480081c100d564940c882c082c0105580540501e00440c07039807130300d103036a41000d040949000c0d251080c40101984907a007102c0d0031500d074040380750310b903203d00e400140104402b81116501142c100401e0b8815110098020b00a40c084e84640210b01e9203800520105540000030300000e900d021014080542c20400341c031060700094624407515030b2240c1c0110300074140c41d00301900810700411100b05d141d0340000117110043c02100400c09443d96104e5002d09070056000b800b0f407a00d00e0010815003c1b42131504080b0650207a031a28000750100890030342000c10503140d04541c10000a0305000b80f212500915400c40e825034a4100301d4941305440b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 689239883 1250 689238633 689238653
    0xc0203090117092d1b030c01050a0516060c020609011e150f08010509100e060a1e06030b0105030c010c120804020a17010605120a030905121e01020901110a 68
    0x625100c0c1c80038008111502020044048000141c008400d0314201550b03401c655159070030070140c030f075110b014100950308070160329110b00305c80c2c080c0007040b0144c01d110065900d9040b64000004114040c04840c2802480a00240581d40160f41c0080e03403c140520007414031400810408040c0e05280340070104401e01c01030303861440d60006001900c2c0c403400c0300f00c0b0251803080d80f05c480d51601a4002007403000d01984254080d4a1032000c441d80e6814204400040c0c1e6420081030550b030300031500003540d0980980149600c284110b0448040d0090b01c03000c4002c075561500251280608000113200350b050402200c0c0404500342003041041e03182d80e0321700002c0c07030b549114281001040d41c00b25045454030b0b02110b000c0c00d8680200410800621052402084240318080c03065001e1000c0519104002c44c401019a4060f82c1c0c0000b21401c0100f404110099082c05200502c1840707d02800c40b400c071080741d0410031500e000540e585028000050141d40c05030724042040d00440031b418000380074440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 689241133 1250 689239883 689239907
    0xf130f051818010605060705060114031603081b011d101404290a050403260a05040c09020703020102130503011104090b1c0510110c0703170f040e0405010c02030901 72
    0x8040030350600b000003903405010950700c0035402071004202807003082000710300d1301e050314460310008060700c244008055441020710f0b12a56013040105007031020071650f0740140961002002c1c411504d11b09038400700e003114181d80008032600784455004440b000103004502c04000b100300c007409058904a032054542038050301c0101503900b4a0f0000c08031594810747d20741d00140004002c0501e10b00b4000410242c0b108403030441c001089940c104042000f0207001c402000d20708400c0c40c0c8a036580d180142c00a242c05001074501085030800024000200e000800d00c180c800d500250711424040084d505000c01070704002d01c240d040001103d015460101583c0c11140201c8002c00c10081c0390307020428400006010f02c842c009802050028030400150401e003251010754100445141445031008901032001007041d69000028204041402888951400780e0410351180c500a0100404400d40d8803607404014600e120004000911400384541c00040305907001440c03500e0708202c0020300602e481c0e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 689242383 1250 689241133 689241151
    0xf060105040b0a080a09061b020c01030516230c010b031902010e010f0e04090b061c020a0506070309260f060f040803040f0c06050309010608071404110f130f0518 71
    0x9041885c1ea0b00f01a050541007002003102c041c206045401c0d081310341c0c520b40d01503c248030300e601315544240300f0a80305104022409a03003010145040301c2518000c0c03812000c03011401d466144220012009100905040c000000c14a00c240141422321071105c41101d401c036a03010008000d81d8001c05030b0104c08400340380003565141d15950030385101c0018400d260f0000e141c084a08108040c0540e102c1c000c840466955418035030241841321042c0e42c0d03a0000350054030f1160b0820450030280040c03c0043d01c6801c1500400340c030ba052044002501c41855a0190f0b9820045503000034180f0106c5810702c00c1c803020b0300251811807542580c0c000c01610041618000000107001e0100c00c840010900f9401030903860b8103581d40c0002000750700203079038913100380d46042707800500400d0000b614821901a2b5800412100c01e160801c4002c3c505000f090b4603500c2c00300202000a41101c0c000c2c81c11a9034140c0d0029842d05040902170f1587c80c540125004403a21174001a940d01e03007075a00799000142c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 689243633 1250 689242383 689242397
    0x30616030e1213140d150e2401050f03060106141c0207030906120207020d060b01030204050d1a0705181203041d160915080603240f060105040b0a 64
    0x901003645089540711811500a002188902c044003a40d40d00c0f03011520424005203c94a100c4c0401000075400040105043c9024541981c0544290000050b2142c4002a1009120760f0440840c20060300701894012070b4a11005000d580342440e5520b02c07000f01580101a29810310340c01074694120308103e102c068402141e101450b141400305140c0351580c0710310035915090a440c010b465981a800703520081408401385c1c1c507004149200740c1e08a40d800804008500303e8540343e09006141e980d81240c1015000c20000c1a591502c068504115114203035182500800100030462043e000c1c001d502006010460300d410011603072a038000f00750702115004040800300c003c0c01c0c0781d80304940c00b41e01c80b1030507588171020001c40700900b01d118005a241000c04141201e000b2240440c1c140204103980e0040010344421a10401c44641d21400280c00c6840c10700e00a00300030301c8a2403540c4000540514001080424880f03020010740100c02800d00c18205400c1a001d15944d00410261794204020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 689244883 1250 689243633 689243651
    0x310090312180204060e0610020f0a0f02180412030b0f010801140a15022521050709020304060c0f080f011503150b04150206012907050d0e0a0503061603 67
    0x1000329452801607000740200001546d0b039150310301c0c40c403040342c000c3c1c4511008240110f00301d0000c80c0c6019060b4480003e008840c695070303a000e4001c20180c03801d0ba00300c0300c1c0301c0d0905619015034881502075801161511a101d0030a200101034480300040305001394107030392018145076000804c142c1565032260750f01c48001c101c3c1c40070607109000c50340440303c020050100d003146ca42c0c010030454013080600c910740d42046a20500c0c90302100d500c0c8a010001d921030300d8038503500c5020308903c58081d0f120350141d400490f6107443e44d034140c1e002624280d0701c0310341d100c4010003001d0700034076a204407480c6410b0004c3c2901d0030007890040035505108a4074040d06400c0c0a408030351181e8040103500d003a40540080c05516020115a960860300882e0000602c3c045c40503086400055070a04a60120100c0c44107481100400c1c4414031740754141d25000c0170180300e40000641c040c000400b07100710b1a074551540042d107404110410030280e07c054001d400c032071b0030b00a8098848001c50140030380c504000c00c0c1096 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 689246133 1250 689244883 689244911
    0x20100c060f150812130512030f0703090f1509030305180306190606050f042c070e10030605010c0206070519060f0507030507021f0f0e0c0310090312 65
    0x440741102506182c50225820081000b9028020580f5024000c0381c0c2c4e015a100f514040c01d101d21520000c0500c62458104040d18018486500c034280c150242c900f000040c458443c0329401402c0100d0200c0d500d00802e00900030000144802401200c0042d04048291b68000e06048254000981080f80001e484084568038100710000c0c00f41c0a41120076516001040155895005071995806801c014002992900c20810340e5922032078040d0302850a45031000040800114402c0302094800580c00c4c20400031408052510490b0341d600d5566101604d4402c01c50074002c4c50714580c0c2032500c0e00701705200340c4e680100c2d800c0c1a40d0b07054460070343d210110700340b0b0b503e000c016101c1c0c1c0e0707040c4881e00e996100304042600451a0010010700034415078440580690a030381c0203e82c1100141c2c003502810046468902400a081044a600042500d42580c1a006031a080301044025510021104000382820005025400341b03544081206082d00d0f50010003501d855807070507031203035120f181c2846500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 689247383 1250 689246133 689246141
    0x40605061c060f0b03030903120705011e0b01020c0613050105031504061508070914210f010b01080105101b060605100c020315010b0f0a1b03090320100c06 68
    0x2580d1020311280d4141c241c541031002c0d054a450640910b410100300711950b0800109460110300d00a000c1c100e52681c030400b020154002070800d40b01076407260f0207002d14400711340300814a141381e41004100410f00d03c1c00a49404043c83c146802180c04111140618840355061800e886c400d2070200c1c0e4a489041c1040341001e6000c0c081c50303000b071411200180f0324080501d000e9041c8020380f204c0100d503450820981c2c4030641445420303070b15403e60480310312038034201e0020241c030701c1d0801941c00c40b4540d580c0d029143c440c41c0240e480c1182e65510000d0703c69a0000c10305401008100c0752600741000244008061426045444450f6261811040c2c2007081503005800608800780ca00c06030110320f040010030b07811980800f81d000740642c800e2200e0192410303200c41d040e9110701912602e4450b00409000c9140d02418460040002601107503180c0c03660703580d29070807a500a030b54802c0050700754208044c0e1121507001c02c252812940e101c245468a607011020034000860030008020040c1c2d0506501034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 689248633 1250 689247383 689247409
    0x2040803040807030c0b030f060108070c0f0c060306091b050c190f020427080c0a140d02010c09060c020f040b041401060809010212010e09070f3b04060506 68
    0x1408040741c0800d1102d0000340c500c0440c2d02440103140071590b164201d052030b03c03060300c03012000d11100f4006035243d402081d84541000305460300c1c0c151580992100c081c15014040111640c4c288844100300081d0b15000d41d6001c1c1040120030404010200c06c01c601162482c100501842800b0038100041c100c02e00142c0059140394007807004140301c07840c20301e0340c0c0c00c0c0a030b000b01d2040c3e29098040070307000302c100d01a07e854000a0341070074000e00340d0b4855252a4016074580d6400c3d108061250001548460803200d54090407001888a40800e4501a003034410707450f0041d0401103603185c204891944150a60541e81c4c043e604405c89883e428046405040e81503003940e0032900303010044031140101e03507080741215119a1004501e44074409010b00380e118010407080ba08003101c0040c0b00c14501c0201d43c0c0e030480708202c2207511207960303403e00c00c0382855980d0100706030b00004614001c0d04240001c4062012804010421146003201d0300446500c802410261016544078006000c54560660700250 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 689249883 1250 689248633 689248649
    0x201020a0c0806010302040c08070e2404061805040e0601090507053603060112060b180405060a05010e010608010e0601020f0f0c15030108070b030912030f04030f020a03090b0a030204 80
    0x85251039410b4aa5103c0081c40304030301481c60044805c04417441815034600680d00da40e90100c2031001c42e0200710b00700c2c449903102550b007406800c02d00b402c0748001000b8801800e07207031544c4104041c0e2034200d8050340c0e01e0b84d1065001e80c0c1025040f0a4107040402d0247c156440702e500050b10780c4981100325002d00600d040708005400803000e50600c041c00e1008070620b068011a00a4400740c04400c5c191121401c2c840c14030014000c200c008000303003d0350420303031101401800b4004601500940101180000e58060b80c2a400507814408840c81501900c1c1c00340240b0140c2d08020352614200602074081489140c01ea8804900401c078160305c2404000141b078404400c40722841d00910209844461100c25a031080301c1000d4aa1500712010702503904992241c2d028282181c44c1058580d00d640c030042640b400b50085000d41e0003101c13030b25409140207450545005a00f458103180280c85400080c2c2120150351101d01c43c035000980c08212482075503200c0300e00d15120003c41200341e010703020360f401c0700b11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 689251133 1250 689249883 689249903
    0x7080a0f0e0405130b1f0909020d05190512090907030c0e090c0a0207051f0f050d1109041811010e120307050606010806060a1b08091201060e060a0807120201020a 71
    0x14a0b0746000840762844d40603942d01003240c0c40380880e4400c41e264001d0746160200000c4420010921241c2c08000319a0001c0c127032100054a80e80e0300350801d0b9054084400f6580107100c2d03041440000c22184484021012841c3d00d80540c90000510b1001c00030402802c00d600c501303a4961480c413030b4090050400f00030300030295509100740742c0003003508115501401489000c0b40001c541c901003621100c146c0000c034001c403900c024048103c0c1d11841156010040c01410420b25803002024400c1611409640750003a0b11013134210704020540307412400c0210445e0040280e1004030f031140741d070640c4201e000d0034081c101c090b01d08045034004800b0b601c140c8940c040031507004148000400c04a205070000d07a16000b07182c1e104000c0101500459200c0e500064074480c00303205414981d21554421030240c5035950404010f400003c00c1500440d114008a0351910402c000d0100340d000140e420200c1180c01044050412459035a1034040c1d11a4000901c2d80b11020b2040d079001340194500355401c211146 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 689252383 1250 689251133 689251141
    0x60f0406031e060b0312030c0d110c16090605012010091104151d07050702060c010f050609011206110d020a1e05071e15050a0605041107080a0f0e0405 66
    0x10102c20045054882900b052101d50f4140340100301e5a40c0c5428262000e070460701d0300d010140301600004014003503140d844d44281c80c0c11807804050040411080020305000c2400e613281018404141d201d0070003582886810702040c0c1e00294148032003104552000c040503000b0707105a250210700710003100c02a142c008208144100360074108500b03642903a00780f101c142c81a86514030110381d44544001c0c804000c84040c001c8a81c0c142454203e8030500c0d02a00388103564000030300300d070710868404015039503624100000004d00c2c01650b41c090b10440f03890810b903140c403800304a1007a0300031004181554465030400d10410711070030b44224445000c021515101e03159005080b0401132003410340f04040d0101030008440c03107402190000d950201040e80004180046201d001c618084116040020314036600403da070300340304081c443e0290180104469183c0320030310084401201e81010004408c000c9203000c502100d044443d140c400c0d02d05602003c003880c01c114ad15094503065140c0c4281031500740 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 689253633 1250 689252383 689252423
    0x1303020622120f0f21030509011415010c080f0d0204240207260111030612010b03030a0e010504030c0f15230f0408061815070206060f040603 62
    0x902002076501850503041c549030102071801d2142041c00034150010100c0c000c00050103252140f03c520b00c01d0382c01c0c3c140418003150080860060300d10000c0001c0d0b44008016084200f405415002000d050160215007428800045035298010380c01b81406414202d401c100000c110485101c1c41c0c908070000d031640000380310311019502c1441140103c062082158050000c48503010741145140c0c0c0080880c81d103032114060842c0008180e8031388001c0b410b00b0652036071200b80283e2121042c01c42a440c4e49140035010025400300b5400d20b4416a85451038000359610b00000b12a074401c250b04020000207901e0340125203a00c516040240440204a030004151a03d0480c035002d80340d0304441d41c03a0011610504590f41c1460100e02e070710500c54a41c0703019200f0005401026088034064480d89019169210070745425010346804414200400c4500c51078041400180b8484095035009541410701c03100003940c401010f0000ca1140030030000b00032051341c42ea070124004541c0140007010f02200900c02c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 689254883 1250 689253633 689253667
    0xf1e0f0522080d090b030417070602030405010c18062109021e040b0105030606070209071206060e030c030a150f020409110a4a040908030406150501050a0513030206 72
    0xb06800d40c42500440c210550103003581406a5144100243c110b54651f00c0d00d40c50180c03243e010301f1401008201e20400300799680015489980544000b1403152041d100050818a26031680200103881200c03e10110750b0080b065080012aa07103400c00e01c01c3c115085400a01580c0302c02544403000401c549070f1540c0b060b02d01c0b0a004c1b02101c1c1009803109032401502e50f440207c40c40399002104000886c014644252503c2d0050303424035041c4048500c503150700d0115400b94000703101048503008402c0551408000011542c4810740c042c2030400303440e50399100c1034406002c10380f0281e42c80d000010220401d65060301c0040c840c1c60805e00c54401e50780400160390b40114192800550f1901018040c0b5050480c5101042070004150102c1d1900441d1440d0790300e01d440c0c00310242e410014542125a1700c0d4011b600f080780c0a41c030030766030303070b00342480e00c1011a144c0d140c500c5101c88160b1000c01c0180e07002000e41b10001000c3c107015540c1c0310428844007070450540c000039409000465a00e02880301d81c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 689256133 1250 689254883 689254889
    0x9040606080d110111040f050603090111160b010b07080316231b07030c090213080d0509011107031a0c070506010e10080a0c14030f1c0f1e0f0522 64
    0x30408140300c485000070301d11440c00b500c4c074210803c7c2800c002c181401002160b120a40d80c0c00041c900c2c28080001139151f01005004002d1645e88015006010441107004e00405407540018502001681d03100d0b41400010807080c86054000e010809490251500d0f201222002086103041c29a03512010300c250017464059083c83c0340c0d588690000040010304a00f0f03282c00500c4d020b40035240c55100e50203980300f40c2840d441d0544042e40000c0c1080200901c0d034481c0690f844041c1c850b40b001e0001028074005451130002c951101d00100086002c01d2034907a03000148412100c1107503102d00102d00c403440750340c0380100a0301c5503c000194950425207401d0113088040c10940600d507442603256a99207103030201a01030006458100448a00d401107414a00380203000c0c0c504c1074003200301680c2084480301c070110680f2482c01ca05600103600c0003500103081224200107031207800c4c0440c00d480d20700701c002481e42404041e18013a10100c4c011416503140c80b89140520652881c030f4070030200c42c21201c0c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 689257383 1250 689256133 689256167
    0xa0c0b0609040213050a06180b010e0604030b240d050f100905070519050d03030b132309031e0c060106090b0304110a0515130b0a020c09040606080d 65
    0x24000c102180307490710509000b140c00038164540001c46501c1840207100250001c40042d0751450300140d4921484003459104c004840e0000700100d03210000342c0500842e4aa042c801c24003003201b0700005588a00c5035401c068004140903c12001c0703180c0120700305a9141866000c0d451402e18820000e00042d10302c0c0f4200d10205403460200d0a00c011001d8072405000203001e50456002401036007800c00000030300703141303080c0c050242c5a039860200741451101c070426000261581909240c0b0b041c151900c04040026500400080e9400c40d446200e194602c5030030403160090360003140c0703006010000c0e54428061400305c0c001e41240010480003e40c00310003040e0003070003990000070b00315008074000ea0884105281184c40c40d501c03a13840b1000c2c40460178903254000070100c004136490302d81c100003030028801c620341c695684d581e50704c1441d039440c0f59910220300030f9070401c450b5105542c0030840403041c2d00165030071481c6840340d2914001400c840d81060b511803055210071107441e81d004841540c0500c4032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 689258633 1250 689257383 689257403
    0x6020c0d03060506130905040c050409121d1309140f0106180b0108040311031314040f15050d1401050a1407030c020a1202010209030715020d05031b03060607080a0c 72
    0x18001c0c03080d54010815112014641780308100060f000d1900241e620a03c901c003440d607402c0d21032000608031041280c0540d50341034034000304402a5000210b600d46158140103600356065140300103921a20300010305a034032900d42140134208450007843c0c50040100c041510146045240b80b0b80c001d010300e218480002c035000d000e207041e8030b1561003018600c08e0180d440c41015660f0791415203e55400d061481010b1100704040c1c150302c01e42c022041c01400310050118003000701101040240e51002070a5840b040c5011502c10254504450182c1103400c1621103071280c40181c1410812300c03501581c07100c400e5080500b0230014004a900885000ca40d01014020304d44640604400301c5411510203005680b24501002c04612256080c000c1a466840058540f102071301c0401d007002090703480a05003002e125820000c4a03018041500304050f903103000d40c112b103450450030201820800310722011080000200e41c2170340b584070486158030b420000c40742d80d460b558200141900b002180a40b102403803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 689259883 1250 689258633 689258639
    0x1306110709060308070b0402130c090501090603021201151b0b0601080c040f12082503110c0a150509030706050c0105060f0315180f03040f0e041e0c0306020c0d0306 72
    0x1d51003080e0550ba0020700c60f5041411980c1c4000941c03801034000e0740c2c0859807804d103101c000c0d643d004000d11040d981d0303251403030b9901c0c09001400c01a282d4103c503084c0350060000c15800d60404440e54111080b010820010760225801a01c01000c0c0c1c000807c4a9100c03013000b5014080540c50b10303401070800f0b81c0c1d4a1940c0d900e501340c10510b0b020700d0050441c2034440e004100140e0700e60302c00400b0a0b9000f00e100c00c3c0f51210041c10501c8810182c10f0900c0100d00162800b01819040041310300e490010f04043c2c40c0080709040060101c5201d40103900e50714840d0340030200d0365803044083e2114040301600715452076072100c5000d06203802c15a44070ba410341c200320000c0d00034240342c62a0b07811044080c004000c03420b00d00740351040c090401007008980310003c0d25040080d640c100001e044900140000d580e48500340b04280e0030090782c0741c0203201250b14080504c0002411800e030081403a038100c100c10406007203480d020340ca0000300d6001406080c00030641d00c00c95500450741d41d0701d9a00a8a0421409135 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 689261133 1250 689259883 689259899
    0x905040c02210a0807080606090904030305150906010c02061e0a020703060b0a060c03050306180a0221090a0f062d1a060f0c01090b04030503041211060c0f13061107 72
    0x104000d90303e00040d003504086604d0380d0049403130790741180c0010300c042d0030714500901041161408440540c0040d45030300c14420140781a440c140c0c220203003178901c038807185040b00000e4007003242d000c0024050540080c0c00c500000f24002c10080840c2d10102e21561900e1040c4020b5541c40d241c0001c0e00c06a01c0c0003205502841c2c000c00c580201c074095140c132805000c941e00e003603845030801051b0642000651240156112022100ea842140420307001070301c80301c1c14114142e0907094050600d101860060521040c1c010001e60442d2656001030540620055480d1000182c0203010040d440c810485c0b11003a5a5526048201203480e074106082020004001c03480c0342440304225516003000040000d44541c1e90038800030280b040d010000410398102956569000c0901200d0540c00510040b050004000c80400e21400601682c42d01580c46060702c060252a2040500031402d10038001400303a940000250541d000d014401ea851058190f450a014048041118004025010305040464020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 689262383 1250 689261133 689261137
    0xe10060504030b07030e0133050909060402090402030703050f0307030807030b10140913060905060a06080c13080f0a0308090a080d02070c030b01090608060f0603030a08070905040c0221 81
    0x81d0003c54002c03103500c0b4403005a000307208441600d81d8954841c040c54605100c0300c6401001c4144c00c980130079244082e120f03001c02801060308428400e50385403043c407038900000604290416011a141145911140700281c03902e8030310751005005010300f03078440d940000c020014001e040d000b502c9160b095590610100c0c2150040b0303c07915800036603184c8241145100d2490031b0041810030894500e041e10500c0041e007837002514040c03400e5a01c40300e041c06a204240610340d0044419140c5503003480c14080c1c0030f0104800204030207120440401c072146000c40e074100040003004644140e4a4140401410b1a01d03544000800d41c0070a1b61403002c52004840050b00031a00b0382c000304130710b00304100020081e0180d4000e140a039070b140140c5030040081002820f1681c000c00c85488005511883d00720350b0b908180300148001c1c50821480e04004c256200401254180c108911742085c40b5a1004da060b280703111550003150f0001e141c040400c58241d000585144011142d050b050030450740d05007883d83d54 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 689263633 1250 689262383 689262389
    0x507120603030c0320070f0302130903080708040507182306101d060301080a060e1207021009090c050a1e1e0201020915040303030b0a0806060121060e10060504 70
    0x454492030440800d00c6848601c00025442c541e035800f102c28030240c07a1a1100c02c2c1c100660544087c1c1b41002103240c030003540000b00101180600c8074440a44015000c040c1c000d003030405021881c400203042050512991002d001c4107622024403100501c08840280005012500760312084c50400c403010740d05800003440384c0002440d503240305a40c1070080f01c4501540410300c02d28015840ca4010580c1d40314065130113004840004c001da406035081c43c00039030f50341d44003146048c7c102c561588050618407084880030341c0c060310507010340d50200b04121100a065488102c9180c40c04101d2a41150f2280050010305180e9032004170400c41480d5510000300c1c000d2038003010441821038104c02c0d0f5100300212065101c980001828105210046511103461001800030040c00290500825806100d6805416400c2d030b00000c2c410f05244c03c140d91224050002818041c5800c01001c40c00320613402c0314007003a07071704005000d1103580d00000e00122006950504405150309000304001c1c2c4110255411 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 689264883 1250 689263633 689263637
    0x200a031214120f0f0f310203120301080129040b030a08040b0301031202060702151009150603110c030403030c020a0306021b06060a0803031b0c0a06050712060303 71
    0x44039a4a801500d51112440704001c0000301800103444000038400400c0c440c802507243d500c10f82c64119030400010f4002407000301d11103d000c09205404e50481140c9404405042c66170280c040165082c941c0d003c10108000d62500c580c1d08030142e10001c48000e107040790b2701d00c80240a449000114100c800400e603006074008440980450158a081d42081c082c414000c0c1c107843c2d03c081a510b41201c03e0b40117800c100c901e12400801042004a011510b00c490320851015100d01c1c04c080c0e000948841c41e201005003500080c9010516058249456000404810320700300554841c091901100501e030344511004640380c204c00210011032281203540c1ea01860000c0c514090841c0d40035148a0080036003607800a44048012000a40030f10080c0a11030080c40213540309803000c0b840b6442d000d002000d9134001c56130150100030202002090b6500704070000c0342c14044040304840c1c11040e0140e030f400d481c428829510b03041c081c000c5035800f4038001c8006507580041c0e01040c0300c4000554080e8400140 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 689266133 1250 689264883 689264903
    0x303020a110a0b0d091104140423070f2903160903120827030d020906070c540b2701050315061c05030304200a03 50
    0x80c541d00a00c00680c50080c4415503160b2201ea40a140781c001d11222503015a60f188000c2c10305c001000341c40804003080b1402c2c0000084054941a404030180c002420750070314050101801c20302500440c00d0340581070840300342513502c40816000d404148564118449550f0703480b407040303280001204001e61310380c0d800340c0b450b154070300001001d0100030388030810406061004070000f00300522007104428a03036102001e40c244000c0c585286002603818148108040e03600051031000401034030100303e801500140c64030158004035aa901c5250340c000c0809001480120f20505400880490046801c6041400701030071078405409065005005511402c107981c0b0300c0c80002001c03040512440482d00101e2541040c08c04100c05401d2100d1129130082c03801d07a0303501c03580c00309043c50f401880d048005101000c82110103403c850700152505014008c5400c2c04910743e00c1e00c1d481c4048065000007200d60703c0c6080d080201c6401e01501112007003480da180b0301e05151400707215160550f904119009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 689267383 1250 689266133 689266153
    0x30c0b12011a070b010303170a0524011403040f05150903250c0806090d02010213050f010917100608031309150503060c0c0d05070c1e090e0a0c090204030302 69
    0x48a2002c8844405501c004000b5000024a0440760078004e61094407681d402303000e1001c4401d40b86070300411064103c0d10380030070846814007514030a000c404004014000101800f00126002c2104150100c0840c000205200030407124000d40b05040e40240e041d6192240085601500104141e0b08403202e940305000c10700c0c00c00f412100714152807518254070041c80181e999424120020303540700b0348040c4c02c4941001001d03102400ba200c24138119200840ca442d8200c00440101d90709800f50074003451401c1c01c1032150b64050240324024190441a00b4003044076224100e655a4000e10200f043c02d0a086000a454000000340d03a83c800140070350030b80c00740c18485c20034001c00c0b60b41442c510200034040700044c0c50700d042c031090340a181404500c035510500d41c10028540222104840704018007000320340d0200301a00312190030340391152005120305a04803401e041e10342c142d40041d82020700e07041002440350400610004802d2165070399101040d0745100c40b40032402184006005a084035a109d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 689268633 1250 689267383 689267399
    0x1f02061f05010521161107061e020102120f0a0c0f02100c120e07080115030804030f050307080c0c0306101a03101203051c0203070e0402070f0219030c0b1201 69
    0x28080c1000c424412040780032035000d8540f810740c000e543c1c41c0403550321045e101290703942c0005d84414a101500c02001094a00302c0000e004410a00ca0740341c0f00000c179050310358036920070340445c1d500c03030b6000078200d07900e003000c0740d4949078200240d0b1b170b003c54a880e0607110100680035402c3c03140b41341400d4000e403810301070300341c2035001a0071100c0d915420400007120001e45d200b541e2240e80c40c0101d03010024000b45051412440c2140d010490680310010307224810000a0004130486081d690305c034000000c00350035480c1251840c000c280000700304610100d107500783c000c00000d60038a0b44030210700711000c0b600ca501000e4028040e500070743c1000350b08800100d0018100c1e00045030456850701c190304100da5151032191604c2e845100440005d100040c13546e44000038800249800f0340c010400310302c3e41c141202d0141c006282d11120500468001c04d138841445802800900e02e1030b000380c502043e88072004054400e00085020450b940c0c42000008507440031030805851103403c00c10080710303a43e401c00c005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 689269883 1250 689268633 689268637
    0x3060f0612010905060915060901120212070308070602030a1a09131511040602061005060306010804021809010516030501030c0e0c0c0318041109030a140c1f02061f050105 75
    0x100c0720240d900c5000d51000541d08020036071050200c01d0107131850469102002120701005401d140c03190f9903540044c001903c0b04048150300c0d0b030341240c0d0452204400101076003040c10760b50020707041440101d901c005004aa40080d4416010080108056402141681306100e1580e00060700a00c0c03031400940c203102c000b503808044a0194101d081009903592081040d1403503440211440315012a04004c503d404221050b0003800081e21403015a05020220300e107400001e0407181002003800216007952948000f06959485250f2040040d14110500c41e018205c10b85042ca08a00c80e44080d60341c03e48a40710b40e0f41600d91140551543e07a00d010084214288007400084010408003c009030b4034800304020140300035500d4040030408513000130001140d1419190140d0f0500401514600b507402188501c0e41c51362020020310385600d136403580d80c03518001034007864001d10700200c500035804010301c2c0d240302c0d980d0aa0841d4059642d02c25412000000c1c600355a42071003040d2009c0c000e640c09980 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 689271133 1250 689269883 689269909
    0x4120305060907091e1206140919080d020c030703080f010f08031602012006040209011d130c17010b04050a1b05070312060608070801211511040308041403060f06 71
    0x24140d00525120060f0710a2003e40100442e87c00740d031109100c440c045103126490b8041e009601418940351003c0000d1078a10f580030b801481840001060112080c1c42e0b41654040d6811008490300c4000c1c030301e40a01405400c1c0c03042050840c9050000440d0380c91001c0340403d83d03480e100698200070a040010061001c00703a003c0741401045070303203028040325425800c0740c0106d4200c000e150034201401440030b00070b0182c105e85042d00b0760a03003002c0d018941c00b2506800614242e9060540c502d03070f0400818504590b0800d01222a28480700000004150841030407400100c8003080b00740c540364415012902d030b15001982e03510031107404000d0140140040c0882901078103105040001c4c0d0400c4e4002c0382c0300d0307400c440301042000c0140070000e039002e080d10b4050f111707074100d0100461452850b0301039402950001030a00f009080a00b1003000d03070790440e0303082c00d091440b19500c0d1034030391510400d282c1007030052801c484402c41c0840b41c2d92400162050282510300844a103640300c0000f80142103400d86 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 689272383 1250 689271133 689271179
    0x3120902060c1608011103011e0306020310060306140a0303081905070c12080420150a02030c1006050904110607020d0602180114040b1b01050412030506090709 70
    0x4840940c44490050111940d0798014100364000300020366140800c9030801d420681c1b4001c44002c41140c50004c40e030540c0c8202440c0c0051854440080503580500c1d00b00800c0d20740044144248101c0c1040d10105840c020b0320184602510390094906071243d031714070585d01c07509400040020078040c0c810582c005540c2c100641210410855610640d10250341070000941482d400c0d409201d05186c80d0328070062a860049a44d003850748988541140d4030740e156a0801d801804039640781e46840c406030200a04510345038881506510181d161303040b0651000c020700a00340f824102a070345200b120140c0d0b0008006030001c9d116603d400c1d1081d140081040c0d00802d0421005025070380b00066030058901c1140c0260392805009081c0a407a02d410002c541444070710301000031b1080482080c1c80944452448058846908512103003220300d03841c068021035440d05c810302043c4000220690b1102403079072801d11050700d900d010301c841080219031180014140c044140440f88507030f482142d10000d20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 689273633 1250 689272383 689272391
    0x30a060e0c030a02160f05070501140c1c0c02040e07080d0f0807120b060d050601030e0307050a0f02042309011b020d120f1505030606010905030618070f0305030a02060c0f070312 78
    0x3a540e114240041c2c42003521f055000740410001c540c1e102c09a40300105101030198105668603208990b07503000030810b1404521803059252040c2e10540d01c0381c9445800a0003840514003803180b06880301542c0c020703200a03004e441031000f40540901c5803800300103000d82d604c00d01030b80c3d041c2d41211601c0d558039880d10440e440e12f400c03002551700c8001404c490181e54800048034240307400050129810040302400c2c9030000d1103172101041c0c01003032246c2250b401c50503c400981c031510018008252401420f8519101c110190205640d0400d8031031044a082c002041441400e681c00b0001303a48607070702140141e1203842446461442400314904140407104041240c85600140780c041c0d4411200c0c0c5080c05018070000c20151804018441e003040084c02c0c160b0100b820039012a880c1c2d107005210212044c1c000101c0403030410200311a80041c094810341001042d100d1510540742da004250440c01803180d036000c00d0280c1141c10459603210a03e10016141500075a4180c618131040c0761004032003965 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 689274883 1250 689273633 689273677
    0xc0905040c03120305071806090605071704030c0303030e070f060e12070605090f0405040b0f09030405090708190b060307120213031406011406090d020d02030d05030a060e0c030a02 79
    0x1c0c24860f42451091500d010400d4900300100134448801c00720300141004841b801045426040f076029000d540700b40c03030899038880c15810320345002510308800e805203440008001007800411507015068911030364041c40b800920b9020b07266501454054013183c499920004c014650290f20717410848503028005c0d99613000350150840c00c0c103043e0790201d4041140001c5400140c42d09910107840d55004a42c108158142515580503e0320002d1001002c0d020358801710300341c014200251402800014020305e01c40c40d003498020460701d420f440682000200304010200d4401a008111918001070710351070459a40440455603800c400600191169003003044803c4500c88140ea0300145008020000e07081c0c0703806107650302e051816840403654000701c0300a02d000d030380c511048889039407003140c106140100e00e00006035070a02d100002581442088040411141c00001075489202625001c001069584001c4803442104036100c2074065003c0001510102550380501200c803c80c1e02c04103003c1913 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 689276133 1250 689274883 689274893
    0xc040b040f0e070f0501140f0c070806090a020108090a0b0c0d0209041b0206070801080c0f06040803070b06030705010e131a15041809021c03050d1a0307090203040c0905040c03 77
    0x8110380c1c0104882c0c11154003840b0b0b0720b5030880010010b040c20320b008202c0c0002c0762684c0c181c900074031243c6d05c072108c3c002680e0440b4860402049015008070b0080d00c0d96030a01c40b152079a210f54014080b804120100b002542a1001007410704130590410203c009a90300c5812820250340205036411010344c0c2402644207036155482004110008000e101922400301c280182c1703803480080030b5a080058140050000410118011654040039580540b906505a001502c01e00407030f003040885100224007841800700d0700d40850702940d01503003078803507054684004550803440d065416030800a402d600c00c5201c0721075441480b0100c41e48202d03100d07d100c60800109604140070006018800100301072000c110125504080d03807840420030400d40e401c603030115582c0c004521720983da500e1010891001d040c05442220b0317407501440c0080041d01280c0300441c80307029081c45180e02910521401142100e000d00c2240d0140b0f0b08903403d040014078090b0000083d04c00100100c5e4482e00b40080080051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 689277383 1250 689276133 689276141
    0x60103110c06150409021c080f1206040b060a02121602060a083301121d010f050a14011a040503030d05070f020d09090c03020702030f030306130e0c040b040f 69
    0x11144002a01c0a800c1000b40804a0f0800e100240d1046141403d408010f80d80c4000340c04d030803030103103041c0500241c203401e20550b03d014468016810710000220344016542181405100e000c04a40822444810105000560240c181c6c0c01e005039101c441c69140c0c01d20041c002c2d10092035085150641c108996001c11400d0b00104c4021000c90401d40521a50f0140d2108811100d00545400100d01c40814070200b50407580c0c03054207041c41003651058160410541241d52000340003280f554103041c0094400d4001c000c0741c1c01d0340c03480a01d030002064803200c690041c12050401200b1408260342030040d00d030000784040803a01e00880d010000001c140d1814005404924a00800041c0d140391841000c0d0a80c01c419030328100310b40000070800030b52500202420280c8001d000001203454401030241d00070301c501c0303030065031511504065038801c20000004510031001540d45040c50f28041c01400d090318034260b240f400e039400251714080c09003080c0c1c0c0940280c180c004e20108010300440b102401716 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 689278633 1250 689277383 689277397
    0x50709020a082d07052703012007110607170304020a060c0f0311070e0a020415140706051e0901060504061e0306180b090309090a1a0906010311 63
    0x86600410260000c680018200b5801085019040c2d030405041101c6149001c6542054803076030030081c04189194402c0042c0c660150144800f41301031541000024461490346285903c1b079800c11001200c0c2d040041c0d20040400c040c26070640c00c100c0c2c030340e5901100c3c0081c1d01440f03410000030300c44040131943c1059200b172401e485400d03055807030406005201202d07946420920512000002030b40004030505102d144482c0c01d0320382001c1400803e11804c3c200900c581c05010070038907140c180120030409030f00520885006607400c1500404028080d2464046032100c00749a420601c044800b00350250802e50b132100d03480c000d0040e1140b407400c075014904416030302c25050f0780d9601001c0c00035080038818a4081e15034040c0c0d00324110000c003030f4203035441e8132400002c14154480b280340f04102c0900c8070341c501d1141d119000c240c0030318082e209035603660030809c6600c8c4100f80c01c4020600c0d8003508e1051459182441d1000e480c400d070300b02e051183c08071002d041c0904140d9611150b08641001c0d80180c009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 689279883 1250 689278633 689278649
    0x5120406030605011d0d0c0b07141b210111030115140f040909020a0b070b09070e01120809220f05060f2d060d0c020f06040803011707030507 62
    0x4450901030018101ca14507042907040c0b01030b030725142c0b011640b4052000da00d544200c6640c0f40c0d50a15107440301c01141c641d4010074004202049000401a01808800c00317441c244045840811070b02802c0d4100b10003a0610741c0c0c008000b8030907507040d0007802c00f131010401881c0300040f41802415025180a43c000d900848000c200d4103861104c4a910907078000c085411408a1820010007180d07c070f80f1031103203110b8088415903074841401192180f00400c4000c20218048685801795400c010006950884052899000c1d400d0081003020400324814182c86040203030b408899450b594100342644003035002a404269190701600301c1e80780c1903c400f140c682d03800e404180040e441034960283d8602501081c4110060050388015403100c008010344d00751041103810304480e041701440c60688890708241d4000c0d00000309a0a044280c0d045510b05415580c01c817140515100c10180d101c03201034500800281081004004a407814608450403030910301c1a80da1142d41d981d9080e141c0b90781b170703404661 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 689281133 1250 689279883 689279887
    0x614041a090c100819060f060f0e1c0c0f140405060f03070609060311070809010f09030813031103030c0c120c0306010905010906081609021e0a1706010309050c09090a0512 75
    0x1854198075a000c454174000c1c0c582c103110a03070416042106e00e80303240c044c1c00304018407107540464852091b01028800b10024120b080342201215a42c3c44240541005854052402c44001a1200c480c0d1005040f5a6051480110324103c102000080e000107002c0c594042d9060b030400701e00d40d609000d040c00130440340c2c030b4500c5100d04c0c2c28009000d83d407036115940040c01090000d8408155000c003241c1b880d60003440c080100056500c0141c1c0c0406160304044e05181000c5010b0343c172008070207030700d20690b4001c0641404201c440030803d40d4034851214004510340140032001c0c1c15080c203103070084a402c08a0180c2c1c40401c5508040391602000f40d001c0240c01d5182d00c01003040c40c0080c416000601104005010741421702080c1c42c0040080c0c4c4a501d0203690300182c00c0c20080f1100d034039000c0c119122144a940c9090b190001046911407054800ca48018a00030a4840d800f0f4480c410700343ea8000054142e00710b44408104200e007004290a0060180c05100030004070144030464030f5004240c0072503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 689282383 1250 689281133 689281141
    0x3120f1e070c030e0a060503061201150b0a0801091107061109031902040e0304030b0f13020d080d0507030e0d200a290f130303060807120614041a090c1008 68
    0x810056191040b07502178142c40a007407040c0c41c1c6c4142103e5201030103450060418a01c1c00700f5900412050007400b580528240000c10071a40c85030042401c5051651010b5103662210750450444607903020b20300388076204000c002d00090480d000503010f4441d040f141d81c10031201101080c2402461140000c0002019000c1030451400d03104180401070040011418542550f036107140301c0102a0103100700b04013000000e8489045030541201c40395003c1e024140b2100c0600c0c1c10842500301c0740c220b401c1c041c140b40007d4916442845400c40b009840d40c010104e50705d84110070348081c0100d084204444c01018110b07070075803004200d8203012a100ea507810403400c01c0780007000300c0e1035040c4080380074039012401406008107c2d9914190041d040b207044004640ba140341c282d00a003c10361024015003d41c201c00149001a9018000c410380542c0341442581440a483c45900d102110010500040c5082030303a040c3c0b203168081d503030245044049403d9401600001141c02e0b4008400000142e0098100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 689283633 1250 689282383 689282387
    0x150f060f08010e0c01020d1112130819200d020603040c06090b0a08011a120a0605030708031c0908161212090302070b2a01060609060203120f1e070c03 66
    0x20345142d03100e00c0041e00494a82000003921501000b6001e0100101300c000703583c40c080c0034829980500d03161103560780d4601032610f2400c60303512944281000f5004041410002c44c1c00301c0800907400340d0dc060066042e040c0c07800441d5001d5200b40d138450304080712180002c0103031200300080d80202e015200e00b416661a140d001440c034078480d00225100b440070b002c81d51255811032070590545884901c0544c0c800003d100d42c83e102c0c082c070381c0c843e4540c031000018450b810296a11a005a58054058810030368903209507903500d10032006800344000c009206000c64000c2640520231061040b00ca05141451000f56600d2904c400e0304c05403042e003403051104a940d50480c1c2c0c04020b208440b42d051010700400c1c1c8002c0c0d19031106201c1d004908030005040c99800152900700e06455258080d01d42c100180810114020160b5014081c003040c603061003c9011400002994002010300c0c20b021565901d0010600b003503000a13000180041260710340000d1040c0b5585010300c03894040e03480c65181e074454180 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 689284883 1250 689283633 689283641
    0xb160605010b130b030a0902060a0e010206130302150a090c03030f0305102702130e090c04060f171c26060f0409050f0f06011502010b01050304150f060f0801 69
    0xa0400d600d0420100e0201c10b8078246040c02c8800c02c1102c3e07a1242d81b50300c0128080d0004c004000d47c0400d0028021071a1a00070080c03203082402a421201c003580c2d04000b40301d00810340314004d005a886006a0b25141c1e084030f56903070b4804003030240816800c4440e134820a0220582e042140851082081c03024100d5041c440d03142c2c81980107180e05404c0d880c2c221850800b05030136048120354042040644100c0209404440d4900b01c0c4103101c074001c0d039584407807041c42e00b8241c4000d0a1401464031512042c41c180c000d58050341c2160340010012403a101004940d420780c4803540503036010b03028811035100e41c0b00800f159039003029201c40d128884001071503088604024403802294054605025850b1138503030003409881415103000641043e18140f03c1e10301268504035414502c10591908452030000c02c406040b2080922070034035800603441c0036402c1e9040c0480303190024609000040126590402400004001610004484802203503030130903100e142d04000d5880703407072110401000f1801d110b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 689286133 1250 689284883 689284889
    0x21060e030c0d17060d0609111e04050901090b221209060e0a030506010b0703090e070302040e0a140402010503060d140c10030b0303090f19060206040b090a0b0705030703060b16060501 80
    0x183e101801c0c6030407000030300d02d00910240503040d980d40d90500700400160740750108190350020b00d54110515000c00c10780c10030748640350060040e802c117004689184014001c880005500c084014980d071b440421004100024404104a50403074020400104d000444610110b100aa4809243d1414a88044c10704549010f149004c0d219080c020008180e0101e00e19046d948d84000060340c903101410202c8400c45290403507040040d0000910803581d0b01580100100c5403100c00c140c1580c6d8411641400302d075406e0403030b0004811003100180041d0300c41c3c0025070740040c3c010304a80b000499521007c102e988040101c2082c0d80c003406058009282401c40b0900b002d2a500c1e0520000c502400400d407207001e141d5405001e2500c1d1400450702d5602c060b5010000422651142c10325903a66030000d60f100b00580d0140c0f072000c1e4070004a030920002180c4000c035a81c0141d007031822a246c98404950715480100035004042c1d1b03628000c174284a041d0000d140d4505480323035020244201e800c010302242c0043e8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 689287383 1250 689286133 689286167
    0x305070e0a0611030904150f0b2b0f0c0309050f01110906070c080a0305040302011404151422051f0f050a210f0c0201050121060e030c0d 60
    0x154200c2065072803080d01010b80e030440c50600182075000b80f48a00d54040c2c0905182c0c01400d00b205626a4825034030024111481005202c40041e9990007a4490b4860b10904240480071420b0141102124054100c209007008078005540c15003084c3c3d240440d00328001081c006a180d88905052240800c408044410510020448030b10301d9100501d0031310845540c00d011b01d10200315a418411280341d004018000384085d030b10601680d00d0010626400b40c08201d002c21801c120150340d00b450f001c203071000d40300c040303010300c0c20035001c840e081d1188036282010100b06681007142c07484003003013100402801c414135200982d000d0309000420120756081c9120f12944420712144200042c0e11514013003600b03886040095607801c04003401c42d0b5200c4098034075071205018681d00d98141c0401d5119806440c54540d00300010041c080089090365828400d00800c06c0c01c0301e1014442d80c01441c0c0d10300415100b03d0000811200b00d0403420b0a40d080700d03041c0c401c2c0d40c02c00040c0117000c541114503003044404074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 689288633 1250 689287383 689287397
    0x212070b0906071b0f02180c030921030f06130c02010f0f051303050c1216050c0f0f151314100201091a1504290102030723071802040501030507 63
    0x150b005001c2ca080c060300090580d0a6a135917142c103545480a88400346402c1d031a003003010b8a081103040c601d56000780c41c0780c0401d115414408040840130560007480c8045014054555220005c0000618501610090303002d0349030001303201e01070710612031072000c448960004505907944c00400c0d801c5440600040c40290308090070842e00107603071100c00c1a030543c142400c51706c62903007101d090b240610303840000841c030b10005207036401c44685100095807180f0400c11184450032032400e005d60a08a0340143d604082d0401d0b0780500d5117000d80301d540d814015031214a00b0205102d0b641882100c2c3c9a00207080075101403003001c102c0c20040314036591a441070000340000e00c6181c1e02d001d0140c40001141d50010440c40114401d14501d8140c02020b40340100700380807000041006030b0000c1d000802001c140032800c00d00000c50750001c0259900d0350303000002d4030070383e04040142e01510b106090b00e8082901440f10b0100320680c29400e0b0540c06103011200503107a6040ca80003408903040540308805024503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 689289883 1250 689288633 689288657
    0x507053406031b0e300106080c090601021b0103050a0e0a0807021c0f03030906090212070e090d080c0c0a0b01060302070204180b070e1c05150105041104060f0212070b090607 76
    0x584c05c0184412040070850070407484016000000303000904030b840065420408005402d580001d00c1c656214012205115503440b0740c40103a03a243d07900700445041e080400800c24a940c000ea002d16400301c0d010340c1c08070f859019800c1050412a00d101c003151a002c0121b4082c0c198101030858210712041c80811203940c03501901da6034005a0130f00c1d001002c146d22810344c070b004c014650b000085910b9000c0d140e002d02c2400c059010b0745880b05409007005001c4454001490700c0400660014201031a0b140c02c00161100540039001c1d90090a031003500748502041c110000d23101e030316414002c00059070011380f90006441000250350001540554149140c4040c3d400b0511808900d500321501d0b0031b101c100c40f03001c08c0c0440c001c0b14004900c031200c03a6a81c0c680c54188070011940c203541c4c41000220300000d03a202c4040000b107803da40410aa290004d20040c0640c6000350103600c43d000460048403031203000a018503920344d120302000c80321391284105010101e50200002c0f0b80001c040d007002803101c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 689291133 1250 689289883 689289889
    0xf060109090305190504090218090c03100303141b060405010608010501030c060e04090204020f0d05090f07050d0302030d0624030c080a091110031b0507053406031b0e 73
    0x503202c1c411310b40c00d07031400d607125003d0241040f80e009000b082402c2d0340714000c540110000303d090001c1c5a01500c5032800185130780b001101102d02c01c9842d18941000e65003562801c45a91581402c000c6101e0001c1180f00700647d0801d080354003d0b1402002452030745882d141180c01d55280f540a0310003681440010310020715102d00e803005440c1d45103003481c0002803c600240240211070030217500b20784001002442c2140e0207009019080710044140a962900d40d01c081d911200d81c802d03003941b50060746050110307240c8128150f0405009104807410074424a55039812254a64030180840c00b41a02441c0e864004640c035512482203803d08001c105800c6e5806040c0c2d50b00200595011903840c600f02341006040760408000c100d02800e0380c01524010240a0020843d103892a00c0034613949060598480c4144210b8000550140c094000c60103000460410541a080e010b4000e00804407111501c15000422000602c42340d0b5010690180c2080078400030300080480408010449041c003403262 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 689292383 1250 689291133 689291137
    0xf0a0305030c030c0d0e0d27030b060d1205041a0a0801060e040e07031a010e0c18010905030a051b030d020a080a0918060914190c090503010e0f060109090305 69
    0x44020038110396a03554401081c02244078981040340c45c6407414a286089010000303485c0000d0480f51190600e444400c54284141c00710617252092114a886090001401040743c00380c000101030001140d0300368070b0b650409425404d42c03100e00060b0000c5001c011490b0b0b0261180290034503829258505001c114000f441c645050041c0e5003813050b0040070710310f030352500d5000e107005a0003402550301c00303900c1345041c02508050b04904030f0a10742c00d40001c100d042403d0b804034040c5000d040c690749401c1d07034050900d01c6450b01400c420305000450a0009068505010f4154403e118002070008256040030380e20314900d4811082c1d001ea0701000050a444e50009183e40c1000c3d00605003640b01ca600b85c8007103800540940090b0710b441244101040c40ea00c06070030044c10746644080600540060000025000401b2110342a040461205070300036080d140e440700000d60a07503d0280171290b1640302083c02e4695580c10952141e106805c4035640780c0c414070105000d0200c081c000d1102280300d0310f00600394 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 689293633 1250 689292383 689292391
    0x9010902010e272e03050d03020313030c060b04020d0203060102070e090d051e0a020d080a02070c180b120309030f032a03090d060603110414130809060c0604050f0a030503 75
    0x54465003010500c0c4105041e40c4c0c1944d0b00846034075092000011201507854020b0344400c440507c03407040e0260b40c4600034001d40b80301e1981d10022601c0c2540d00c0c0c5080b507010505003030554421350b58004d003c1460700c90f800100003200f000c3e9800360f6070741803082c00249490b4142d40078000c00103600e801d000904030f002c40e04000703181c410714066403901200d011250780c44c486840540e40c0e1a0b80050b52400054010581944060003900c46984a9584000601c180d12811400501010510780e091288003150281102d010088850000f001c40124010a01c082192440c5020b55400032400201b9490300308074289402c4032420155040c15503084803000f024070712080000250b00b00c032403002c840c044d042060340c1c90100011b041c030280c01038509200000340f045010a41e00d011809034503110504050141d50803c212003000c140705965041180107072000c10744e03c100c80b456010420030701243c2e104c0d4054042490090b004e007400c2e04051a01c00d181c0100e040c1d0198041d000060303140c4c0860b810009032544 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 689294883 1250 689293633 689293699
    0xf030a030e0d1a010e04020a0e190c0c0b01032f030c10170109050403110c010c060e07120b010e0105011b020d1713060f03060e04060f0e030309010902010e 68
    0x420282e0340b43c0614000c030300319448110410740c00d000191030700c1000140780c040c900035a05d2918080e00c0f200301c2040000100c0384400003140c144855200d02d1060b40c0700c00300380992450f05090012065460a801c0310f801c0c1d000752003140c40c144241d0741d0380c109481c0356000039030103162030750001503103d010a440704814000184582084250240d020380501e0000c003a190306420403064075a1555000d90090009a0b0285d00042050600c22061400012013101014050311180340c80070715039503800c01900401d801c0d401940245000051000c140c4595a081d061050106d40c9056040040c84c0303a1500050307100604009522012096094404600d0b050007038040c0c0303900f800710301e1038140309006540d00c0400e0506124000760740710703074100c4038400302041e1032050340c0e43c800081041d0800c03400d0350a14003031103001c07840140202c0c0000d10264840703540708040200200340149103215003411500200d907024000e03515540c0c42c800b10b680c4000100e038038150817140c62100d808000401074800101d0360f50701c2e003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 689296133 1250 689294883 689294899
    0x3020f0a082d190609050a0803160801050f061e0c07030503041e030f080d0204050d03050d051005210a0507031506121e15020a0216090614060703050c01060608060f030a030e 76
    0x170074010140511420703950440c0c8559600c4c140301c00542c86440e802104e41000401d12400496140351010101503400d0008060b2030038040c450300d0840f00b441d660240500320802c108601a80071100740100341c011402140599240c514203e04c451844851a00780307640340050900078070008d440c0f00d41c2490075036000ba4100d81c4405080038600d00034451608500d910803220400782d07041641c80300c02081101c0910030280415195201d01141c0e0f48928001c2e00c0e808240e4804100c0e494100e00c1640340c003540035504403092010301ea159030782050701680003507612000003201300d408510705000e8a0001c0c0050020780c104c050407034540da1103002c40054141424014600b02c8000d00050503501210081c103840304659441040b6800303540d902c3d2a642a203418100301a000840090511400381203944a40e070b1005290750000400495600c001821000d000c4103010414208009102c1d55001d0301c102e4030740314201d0500d01c00300240100c8007082c581c4241e100603d02c60000750b00c212107690115003134400c60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 689297383 1250 689296133 689296151
    0x1103060604230a12050f061b2101030b1b0721170f1005030f0705040b0112050106020c010806040b0109031101050f0c031b0d080103020f0a082d1906 65
    0x82c400c2e2601085070310074003402000c0f80c00f0f01001040301c290340c841d90442c0e60b45505044c40c651108070480d484400e1380c078210440c10b8028603401c001c06881d51a141e00200c90209162000485d81e800c0e041580c00c924510304024107070b1340150b0a13554100c80c0c21b41c010305081440d9103600d10002f40e44682c501040300341000000c400e0240c411aa41403860440314001407034044006961807a04940d5806480d607840000145414041511158105543d01030b0915509040511009e0240308024a0402c10300030007078a55100948a481d01074002039024141211990b8001044000042e044038412407405440a4a5a800585c2041200c0d44900b030040d90390340c408010b1318039029030606819401000079244401c080040010301c4004110840210120b13026800b081d902d1038040480400709020340018405464400c0800c6410000240440b080c50748650340386049c1200320b1040a9500e07200003c6600681d00c001e0a8816000307410000c1070404500d840b1030080c0034071070401038441555006a8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 689298633 1250 689297383 689297429
    0x91109130c1211060c011a04060b0318030702030d02030901021216031413080a12080907120807081b070803030705040e0a0b0301050c03010618030c03120c020910030201031103060604 80
    0x401c003d0000a0070301c0e448081c01c40c440c50280002c890701d42c401e1004000000300924180c85a18152140c82c030b017960a56441010807103550280040440e602e1009100d11f00069408212070030240b419079020b1920746041e84006490080d28450f1404403000c00d01100c40300d8013801005000168040c900401d0b100c1601c620111540308248143c41c8001480b0300100e0b0b01c11000030801e2003907100f030350910021101528203c5035400c00ba200104075820501040240c02402501d0307844042c0208205450500c1b07503590140d01c1e0740038011507008120a1502911414402d00a000081c142c900240d803943c545450010094860790060100d8101810003017040000198007080756154080d00030401401e203004000440d420902c038010009180d400520104448001020100c071741c00b0000c1c512090450b510465900c00e44a40f0000f0001c00102c1040565159a0240e004600c81d4410001766402c5000040c1603d0400b007108070180402c00500c511a01d0b00c1003107501722880100c0751f01494864900b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 689299883 1250 689298633 689298653
    0x2a17070f120b120f0708100501030f0f06111201060f0e03061602070f0609051009082109191d0603060721060b030109060824100801091109130c12 64
    0x9030b60014401c4410481c1c04083c00504a411b9a00c550304685220f034840c0c02c01010746100b40001014501002c0310040002d01401c0707480061703880380030046520402804a802244c200000d070918207003072203004100403a0400200d500c54481403800007804c103101008a55142e8000e09082104010500c0d0510120310901200003e070004a00240c000c5548443c0108412040d0241512541104108400c07160080702e611003281c031801d02802200a08640d21200c40c1c001c81000c10f03000404001040035555503100d0303510341610158810302164200244840242814113000c041608600d080c80f90319940042c120742c2c071410313500e031030030006001c1d55040804441c0d890405c02c500342410030210b501048003001d141642c01c2070344104542d981c0c5104036503407a40014551440f00c1d4214290061081022101ea41d0100c0c1b0b2440d100c0c0c109603162903003400c44050a8090700c0740603051014892902c0c0102145070070821400c03907050750b00c82e151074003494150944207061107000128141400c009003400f03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 689301133 1250 689299883 689299909
    0x2150a12020f090102070503060f2a0c1b0105090d11061204030c211205070905030a0f061a0907080601030f0603080309070807060e042a17070f120b 65
    0x4800d5446201102d042c0640390044503145015009080021900d8280002c10502c00c46d2200b104200589604250040c4402035803640c0b5000c3c5225620441c02e649000003c05090700c0c000001c0c0b0282e400880c102120142901509042240802c01309600c0ea40303022948000c1600990300c69407000e080c1001a1a500c642003106040c40c8200f001c1100345070300f181070038601d1307402220020701783d14a55214032190310000c0744860210351800e040b00c1c0510007680c80b00da840111402c0030050142c40b1303030000c0c2c54010301403406ca0306084c00100c18410010507000d9601144084440e11400c154090000703a003603503008202904000d84200090090381c860703081100b1010040c0000c010b0b0340c1d128101400c00d54800c5540c90103902c2070140c0040c4d81c00000840c001110b02c1a0364035603848020314100805001c140714000ca1240a481c2c03034042007441c03040780e1907905046031640b0003008400135036200041c038024111004d101d1030b0707420194403a400441001800104c0c00d4005608240324001824401d0441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 689302383 1250 689301133 689301167
    0x3060d021804050106080316122705030708010b010509060315090709030201020606010207061e17090a0c080c090109020706090b01260a020a06080c0408060a0b120a02150a 75
    0x400306502546901d06450081d40148003e10030142c58801140e501c2c0b0800c60603180900c010b1840744042010b000140c84254554030301401103034003d210207855105540341e1006450b400c1c410400080c40c082146030002c0601c0e0000b880560310000003c0e01901440004d50f000f0080000000e0682071f5041c0841c9480c0401040d0300800d042c030040003820b120b5035010490162080102195840d0b000003090004c491160f50765481c15543c005034000340104000c910014400840c2c0886014105500501d110301d007008000c200300d0040342002e841d00c04643d401004035400c170300702000e01c41e01c8064041d0b040d60b950b0b440250340c070b02686c80d10b44000c0503013680160981d44941d00210703401031034a01d030340010713074021543d041070828054040b6100d03028454000e5016641c0b41040140600070100da503409030850803500e041540d104070450030414225072512040d42c0d2407070b0740d140a140034614a088081040000d103120506030740440c41d94248091960725005000c101d100c044c91240b81c00348201a458 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 689303633 1250 689302383 689302399
    0x4060e1816091a0421050c060c100906090201080c0307020312040c0e071211090a15110d0e030d030506030d1404080a080c010c030b1c0f0b0408120a1b0503060d02 71
    0x8881d01183c02d8105004410035000c19a820b50600c103140321801030015088005082d0101d445005c22040b03074000078089505001e0388150300c051003104d2180c2d00c1074078040c10340407886420602c001441c1c0080180018030317020050090241c006e600100351521891016180c01907a119403c02d284103110131303800780500c0024001007040041e403142250091841e0198180912004521103030094042c118029801c40c0340301c02c040062180f006403004070300b0858105040c00c9807041c45070f2410041c4400010f00400c84644030025141010043c0c29580c5000f46800c0065040171000251141c00000501040001f01183c400800c6502c9e8122030051181a0031121840c0083c58815030641000d14040c0c020b503e441e680840241c000d00500e16480802802c051074030313103031a104027550b810320901138840382424926000001c005000d214000e9000340d11480d21003805c44a1000120f4004040317010050410344041d2540141e05078040c0c95900d00d060a235100e5403040d001c038840c0503001b0f0000e5840101c2c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 689304883 1250 689303633 689303669
    0xb0703030f0c0201020c100b040905010e071403150106080402210106090b15070201180e04110321040909060b0301020a05041d13080901111204060e181609 68
    0x552101e84000518241030020b00c114100c1a4202e0040280b0300c00c468210401c10990388906510550070f00700c0043c000250704259442d020b0860ba1101d2040e07005502c90340c414020311031041900500284224010111780d000300131400f50440040c82810244000f81020804643c1c8441800c0981c40380c02d10001005269203203074501815081c4070342040c0606d4010307101158281007144011030720344c0f072026628191460b80111a4a07a00c0350a030700ca100261180400c44803141c0c100306000c1c40c0900116119518030404160a0120040315803000e00300d039280366a410011002078030111004000009000d8205040c200041c1458180c60b941c15440000e45a004c2034109002c0c000303581c45034000c0d14810208240b041c961860664094455200e01182c0c2c030000f030780b05c07001841c060740185021031180c01401103881c54000c2e207420f100100300001c1018008a41e10500d10f401d018401c5511140580040481041824001d091880480805090048194024002d19009111140c04c4002c4805 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 689306133 1250 689304883 689304887
    0xc070201140d2a08091506030f030a170f13061a0301091203110c190305210a0507170a020304020406051507060c090305030a0c060b060d150b0705190305040b0703 71
    0x196503280c041248000d80942c3e10710752055600700d100702020002070614a45c454444022541c0c02401a41d2501c94001d07803503000303801030000d441da4074030320744441d02102c003075150581c41c100006042d038180c000740408201c000f00c0c520780780c1505c40b6004100080d4102d07074180b460078181ca038a4112a0550701b02300040301001044010204900c101d50b80401051000803a900d055118141d40c2040d550302121102c0c41c004a201100c0c0001c61190804518201381142d01d9100322a128020b01043d140060400060714100c1c003072283e21402500c0e00c9101c7d14600c1c13000304542c00010700320061302540440042c0440d110b551018002c1e12004108803054001509140e48035441150116002428084250350b5140a01d9101c0c055a1380f00c0080e40c2007941038081110b9080040a00b0740b403558542c00030b41400c0c0c59480040c141250040c0d0003140721200d00340b408481541c182e126111404c420000d100108501140c04060300c0a480340040c89401d26080495a0780030741c0d040007204d40800034480c001c040e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 689307383 1250 689306133 689306171
    0xa18170d120b0a0b1b030909070807020307150c020708121b0c0306250804120c1110051312020d0210020111030a0e0c030c090c0c0715080613050c070201140d 69
    0x1469403145c40303ea2014811140d6107902606404c1c0b81c0103004000420115800b400303140d43d10059501c1100d04020031074603184200c1e241100c02c0580300d0740d00c0d081e84004a905002c044040c0c45050018040105650b24000681c843c2c136035180070b00c004c43c4001407562081440902ca5144001b0200d41480c146903c202840c1c811100ba1545141000c16561094502580159100d13a40019240318020011101034030f40e4041010210740c5420706a1142045580b0740d01c074002d00100302c0c0d8413076496104540c9920ba2541c05070300500c0104440e09141001a610840d80f840c0c03a40e8142c0f01142c18028002d000d074090903030606540745202000c001c10078009151350040b40d007415410111210a040941450b440ea03c1d08aa25604180e4200005486120000040010410714000c41d0101c13507907000344110886442076840c0000706070106003d510300e80000d68499890b00c24004201d9410884111035541c403403214000e040c4480f04290305044119035041d500c2c2504030510511454204401c0c4600c2c003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 689308633 1250 689307383 689307397
    0xe1503010e0d05090a0905270705030604032d120c0908060109090213240e0f150d0b100815130209060409061d010e0c01050405240a18170d120b0a0b 65
    0x20070aa51003032350344800e001030514116040600900714544454400711624070a140c098910707442904140341c20f140000ca19000c0c240c601e551816248030000c0c07000d00c156542d17541044100300c1c40705003d02811b4008911a411121007540c0007e64070200d2000c1076200e00c498042c4948545410300d0003112134151401602400e02e8518036592843c4c1b03848445032006000e0740c1c03071881d416004000840c0d03040841900400c2d07000003001e96041242595812100c43c808a0340c1e0142c0c085095010003e101003081700781e08145004244020a1030315400fa20f54503a155017000e4480d040f820045001c070b880e40c0d07000140440d04403400b44400c40c0030f17060300e066285410740650955840c02c07442112030340010841c1807002c2e030b05a441d28a400e00c0e09081212204040c05039030400c80304080143d42c6c5418400007003070401d01075110803000110b905001a030201d510751000c1200d21107514021403404001c1450786140c0198206000800b1032003403101d0060440002080d0400b03100400411010714800c054030070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 689309883 1250 689308633 689308681
    0x203011506180e07020c04090203031b1612030203071b0b071208070206010b04052202030f070e0a180c03150803130504060b03040b130c0e1503010e0d05090a0905 71
    0x79243d80e5202e982016802240d0550040e08039603000754103403505400c00e004e140c1c0000d00300c3c2e040805941110008021401e10000c540d440f21504051582c4005400c000400c0c20501d0b29641c0500c5803030203904d9106126000340396a00344078081e50340c84112540070014002c060480c540322078030761408040f54000f40d0464000320700120005038185100140706410780740103803d060b00b8180b40100f4014013a403014105045881c0080316400c0c0403a551002e184292080c090f8850a410014000752102034540030080c040e00c91010140000c2042c0034140d00c90f010035120002d0000c02e030780b8049008081c0c1c2040d0b100380c40c03580d240025911034000040c00001c01000c0a44c0d0701c255071002000102e40140c4120f015030b400c140001004110b100c04d0965002d03903240d41c2841039201aa8482c0b1440d05250000c0349070754200c0040c44203004140d030458010941c150000c2250141e81442195205441c44a0343e08004000555031016100e6010b414001c064044c402c1c0810b00702080604600d441c3d00c505655 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 689311133 1250 689309883 689309927
    0x105040b0718080c0f030111030a02090909010207120503040320100c0305011401030b0d060f0917070c1703070c0e0f0c070b01090b0a030f050706080a0605011403040203011506 77
    0x100304004582d0030001c440345030f401441148000814041c0c1142017244066144d56650741078500311600700011486503500700c10040c2d507240c803c4200080140d0142c00d0340480c1e0b10500070940010701440c645081c0100c541811070310f0760784918080710602c40c00d500c0031100003c00d407081081300d84001011010003419030810710482c14410303812401c40b04248210f0aa0780c1001716004c13000e50003640403a03000342020b8000b46440f02640c03182c00954410b52035001506640c0c87c040300600100c840300d85a050b44000c0d9041c50110705848408640360369024588009403035044c0c07200112010400c840181d54802150019180e0b1141a849600002c550845071081c00c4800200030003406821510f0150740010985101d900300946100100f01205520350080d000c0310001c00407440c86c45114140b10300c0380300288a410f040c40802000424007034a103040040c01c10744188826a00300c081d901e0440c4560010710303200c1e2f480d400064054101714076880e441d1041c1d14004201c003640400900340554501500340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 689312383 1250 689311133 689311157
    0x130906090303180b04060914060709090f0605060702090709080a0309080705061309360201270e040203190c0e07181e03021504060305060603060a06110f0105040b07 72
    0x90f0000300c0210340245200060b500040c0012a2075000043c6903000307590701c02d60044000845072811800781c03110f1002c41c07521001000820064001c881c540d000307102c0e040c0507051902001c60518020024000d20503030500c00012445403003201000d0003031042108541c0e510b104e44c00c2c046d11200030f0707004104c05401120404103403801c1500c212245105103004810307486182001410090840005540122000c036035680f084642915011040b040001c50030b00d801000740c8000340c00510000d961203440d140200c02200d05040e0b00d10254122030000c0180c0e2001d644134030000c4e003083c1c0404a2407905c2115140800107000d0020303c04004d45103103c071001c0154883c004103403040e0f0304650b2020303001e04183c0c0d818003d038903140912840121488084042c074540340c3c1c1c0050001060701d0b00c894007155001c00d0070440f580c2d1502855030489000ea808070700c0c604040d4086a40d10109004440c00d0101d255010f00c0165010031607049800d24201c000c11090904d8640031013184801d0741c00300001a1914801 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 689313633 1250 689312383 689312411
    0x2010e0322120f08070c030c0f080d090803190c0204050f101d0403110a0f03021b1e090711010c02100b060c150910150317030405030f09130906090303 66
    0x4641081d030061080c103c5811290385090307599201030f0b4101d485559540e00040010242007a00d00603100380a092280203040020b041d1404482030718040802c52500d00070095410003004652a414009084000c985140e03081500c82038800320009420510380420004000c0480d400e01d0b0060440c040c102409640d143e010403061000036044800120340400030a0001e4012500081504000003d407107a074200d41c0c90341f0110510700c25080d000b503005080203100c2014070040300e00300007008484031144180c60008601c0303428114109580600660000310f9020350160045502910350000240080c541c00f480c020b49503040d84a1a0780d2080c245041c42c8558a00036007580c105a103540020010415000e50050802e48090440403050203a8241402004090701400e904910b128190b041202c1c07840c41d03c02c602540102d8102c407580c80900501c8002080401264510b001c16418075482e01d9464000419043e412452804080c2c9001600c20403c6986c3d0060000302c0d010352001c00030440c01e0105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 689314883 1250 689313633 689313659
    0xa1403131101210b1807081006091a0c0f120c190b0f07031e0e0c010206010e0f06010203090405070804110406050604031401021213050715120b0102010e0322 69
    0x80c1043d400003507019180e1030030103500500c0752100050100608203c04004018510001c1d14401c0018074090304022424030004203810042c1051b140103031115203002414011160406009901c1400c002900484040c00304002c0c2501c04413842a0b980180c990518902e140c3c0c00512441854000c0404040202c81c602d41c1c0c0c1840343d074201240b40015516000d55940c907050041c051003d01d6943c000400042030383e01040b0501581d64040024001074500603149800500b540460441d840b203c010300150740034110702500311140780232192880d151000180c2c11401105150382c0c02c0743c0351600700406030740d0110406000b90f02405005140b014440c090205442141c00341f142c002c14200020000560304000000c120019900018145050200152034540007a1060101c19051842d140c2c00d00c8000c0c04141c00400303a1410b9201801118003010782803007a9003d6a5400680c1d415170340c24141d000390045d031640c442d41c0e07050360f6990ba4032100b00b10f4100d070100c82c81c4400c00091b14020a070514030000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 689316133 1250 689314883 689314907
    0x3030e0309150c01060b181305090d0f0203041508070e0d02220207020301022a060f040201080903121f142404170114061c02060a1403131101 62
    0xb12142d642411856152580d020200b55180f0350369602c00040d030140014040d010841c4100101b0941c08008000c0201412080e92017038402c42c41c1006024042c4400201d2182541090400c0080b12150350000d0b0704500aa5000c5500403428406444105510052141c464101c948135111840d810005000301e9800415009412248514021714000c119001820844040590161501040b54046030a982118a9902c245085499403860f100010021204440d0040004080b14646802900220700c40030304042c2c1402030300f502084207860140101c0d01c605c803003004420014240023034205812000c4000b40b0402203d040710205e4401411075003626000b200805100b41c0c0200c06000c1c050a80784c1c01004da8100204120014441e00c0490714505a002c5000c00041e44001d04412854030210041a2910801040c0c106600112000d202c8401464042d243c1c1e070b0f00d03201c103001d0a44850140d0801104809008010031201ca41d401c0501c0e51102e00c03408000c25603c80b01001550030f442480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 689317383 1250 689316133 689316139
    0x1150c0203150a09140303010302030d0809030306010e2d15070c0e0901021903050f1510080612010e1e0d0207090b0f0405010b1911030904020d0615080403030e0309 72
    0x21181541103800d8070010b400110f00000040c43c82c100381d6403241039150811400d40c15810100040040d89001e00492816030039900308500703c0d01c0d150f0121500d03807000070030082c10310034001c02002a68940a480700c0e003a9080310203031145541d4101c4805131451031066014403504400c13600c40c106503481e4003582d401d958054111074480c2d0411010141090000f42203403900c1d9030a2000301026041150f03000c05010b841c0d06d0011300303401c2c5010b0305840d8040080001215890a12441c400394440c04000e000c00e0b1542d2414550640f19107001a18690444080c05103135802c0803000c52401c10003240308038082d15044406814030318510001d54075101c080080c080940c0180c0170400026040741c00442e02d02c080207104030030284542c8006411207800f0303040904080e601003401341042460703030320b10004400503013401254800740c40301d039664903c14065014000d640124402a84908507082000178142d51890104100911400201007640449065000a00381030262034440c0700441102c004102c05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 689318633 1250 689317383 689317393
    0xf010b090105040e0c130e010e0610050f070c05040e010c0201150f060804050f030301090b0f090408030a110423010912030f14090d05030a0e010207050a0504050c04170601150c0203 79
    0x42c84240c583d000050a1100d03170300080190404440c0c3c00d2590f400134040781805441c580d41010a19501c400000f080c2e280038502c2040d1002910f40c000b4141c82900c2e03c02401e2543d21307101c85c601a501051540d0040f0f8005003407141680311000b040d0000b0020700d51a40c001c00081048520340030032149a440340210b04c00240409000052080c01c0b02503020740103c08864840510060003403a5a200360b0080390171070742e00c0400c64040d1900d244e400b100b19004a036031102e40d00f0b0075143c043d15032101810b0507003c10fa448815660038117800040c0c5004002d0702c03d03449102c590302c0070500710b007050385158580024019000401c4400c0c9070352560072519055030720709d610034140c0c403825214039009a0030804403010510646045a507110800c03010301d0b01c41d1016648030560f200019040143e4100c0d41815074101a80901050f22000c103024101c030380c111400f0655840360340c00303006144116080380c1e00c00100d034103c0c3c00f0401070000302c80c1c0c100c078540b40807500603140140f411200b140e54204000d5140e007003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 689319883 1250 689318633 689318639
    0x2101506050f0c0703110f060a0e06030604060801060e0726070302160203240c09060304060b011b200f100c060e030c0f0105010501031b03020a03090b0f0f010b09010504 74
    0x401d1001d40301202d03412070030910348640d0b040784618100441c3c0c0100c885c851510103040d11340c01c1211501c483c8900c2526010b00b0090019009401d4030200392605000c1c4174003000250f42c43e034403900440c00a108a00080007a1a2035007400d0b03001c0b10003120300c800030656003030a69010450300c122201092648003400a503d0726007860890182d40070661190220060310300707a0015a0303042c0103d032144008a6108481200c076490301d03c440310b80040040c400c4000138060300c00d1a48480e021a6030250744010002608003000e40140c03511103030001001c00f00f011083c0014204061b5104400510401c004513052812058003041440f1000e650496000108010700300c048500403500060030720300c42c90f000f00b005580c06001605e1600062189041b40c0d100004108500d0002e2044a002d01028a170034821003d0000c482141c800ca0310164804156001604030f143c030380310354080c40d00319600c1172944541d0700306045400900042a1002c85003040c451000061480c58082220740352081a100d16040c149 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 689321133 1250 689319883 689319887
    0x30506040303110403150209030c0307060e0108060414330604050405060d060513020906040b03070308030405030d0204061e0801270e0a030305090d020606060d05190c0f02101506 78
    0x3e56400a04600005200c0400080d4540c600010b407120f030000c005813030385100350805d803a04946500e036078000d0308404000e020959000e120300c484e005c400e00303100320941c5940000c20010002481c41e04d0740303800307400180410b0811000c030500c201040c507407000380c540d10b5101240143c2699401c2c05a4064000c120410441c201900007a81c0404d000300080d81500254484105442c401c841c00c1007121440d4246404520340409030b82d8010206450401c080304d07004001c07039590b00e510701025103d00c6011000a041103010030845408030003000e800e5403940e90300c0c0c101525140b4006002221800268103c0340b1071482101c050b07040b140210401202100d0101e16000d0050590702e0108400d03446d12051007030704e0000c0010140c854860755000031185805801c6908000e07184051a0842d00210144541e40e504d10054511003c50410300092940343c40d01c1c1048451181980b5200d440e040085000c045500a14800c1148219800b9103035090b140d8800a400c07a40c004601d005030302c08080e0244582c034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 689322383 1250 689321133 689321141
    0x170c0a021e01021e0d030f150303020607030e06040224040f290a020a06200f070611071109060f100207030b090316120c080d05010305071d1303020c0a06120c0207030506040303 77
    0x44903034900042d5500b400e203c40041c5c112560016409640300d402437100541c1c0c5841303500141302203000608111308040d4005201130b01200700e6882207941d400448000e450303100b4100c4000340021000c1d41209982d41d0545060712203c42036594248602d00c0601004c5a1214111a0740d0b0015501038840c007a0342c2c1d51010000c0c0890b240724981c10001c2e0034030f4072001d0428002002c0603050504000e03107551440c600007007030f560320000742c0340c0c0d03140e090107a43d002680d29096012100012541c0c14440d968a01c046041940e61500740d581c4484100710940300d40b50046200403d80340212a1510190340310b0718055524411148842c2a61081000150100b02518100305113000d46290238a609200b03515800e82035000609110b6020381d0b514010410804c08115400c004d040c2c80080c0480c3c200c2d003109030100d0010003005150940d40480700d0b00b04141c405e00003a01012002011a00440d031540802400880c040e1402a0142d1405200201d00c60000503040c2c1120b611600602d5503548980d01240a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 689323633 1250 689322383 689322401
    0x50d0b0c0c100e1603020109060c060b0618040518150c04080a0c0915030f02061b01050703020706140c0304120c21120504170c0a021e01021e0d03 64
    0xc1001405040d0000c8001d0040c0790781071001c00d1000c1401c44490b06502c0c10590014400582406052402c00041c1d030004000c0044039464200641032840900b07004000d003552070441e690040b400a61242502500b2524101c0b08401f92820040c2e40c0e209a8216500c0303d80801c03060300c1358400d4005d42e801210030905282d0040784444050b00f800c1e078032000140340c441080d00403182c8004160040c0a0071000b480781456100d4900c00e000070403440d5031251224007e00b894080d01901c00018120126a03032100002c1e0300b005514000c00040c5800e00c801030003504800c00482d0b4880c01d20750b6803860b804c144100340f4000d800c80c6403040d2460700c03142c0c0c84c83c1b10040004659800e0064104840c4041038180340003601c1d2105400c001c030f075068400301005201131200700300e0744640d5240c4828030000c9000a540950308010f0351000507510b40d80c001220345030134140140298001c1903422003000e00f003920340d581d4010345001c0e000c40c0d0b101e41c0d0300c60480703840b9a031008200b1290341c007601c5440d130040d100750000424 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 689324883 1250 689323633 689323651
    0x50d05070806040f0b0f0c0a050c0c101e05190302090d0c06053601030e0c09090703020333070c0f060501180606080c091c12021501050d0b 61
    0x30340d1803014600740001158166560007034030100000b400010002c0560090740c0d00b100018a07e40759658041a0003011143c404008020601c102d006104000d01009031000600703001091101c120010300d0a03040b4020700c2034641c1800d05240f1000d000e40141d03041402180c80e0440440041c043c120000e410452240740d1028141000754045052544104007a040b60b0395500c0d1ba42082e81d4062222001000080700e200055050a14140355043d01d80c07020008246404500d204918080c58034041600d04000d5000003014148003442000280707850441c0c1c8250160350540d59034041a442d110040e190700e00da0750b0b241d09400c5e40c24000b01c40c0095403180c0c4038104950040d81d1134803030119030501040100d400c01d51b60401480821580504040c500004050500c50070782424002014244040d0030201d461801280c1c00c4060390f140c0e25443c0d07030007a0010303d83c05240401d0170944901e8043c11007001c003501400d0041c5a461070f008020070306a42002d45000303140b040d0395a0b81c45203403a00600d1902 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 689326133 1250 689324883 689324893
    0x324060607051b1518041a061b061506120907080f16091806050615070f111002101505030d090e060105070b04030e030a0203060709031506030b0c03040503040506070b0106080a15050d05 81
    0xd1180c0d560f0001d040348100c0403801100300c0d104075043c503161400250482600c84540010914180e581c6400c84210410f80300301d50340034ed04d4150b1850f140030001c2e0040b402c0340c0252810020304020014412000344e5001c2d0148104a40d9410014219a2015011a0802000e1140c4404030f08650001600700402500d0b60f504608840320140103030704032101c201c60b1408000d500d40248035410700700e0340100303200701c55071031009400c0c01010303660b8051a4003110025440e003020b540700c100705003070301002080c025040d103403d118403201c01894a5064020001c041c44903501260f02940f0030402d83e0b90381640580b9581d095151501c0540d5070300c000418466141c070426610b07e005032402d011043c011400b0742c680400780d6003186000c00d00305800c0c1c0e010b40c1c60b030742c0391907130802c085800141556041210b40031501d0762611241019801e52050ba00450f03001080060601d0421600c0d9030911304880c1540e58402c407a0310361416a40985400c0351910008030317140d217000c0c02a494103400f45e110561050040b15 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 689327383 1250 689326133 689326181
    0xc01050a1806030f05090f03180111070303030e100b0307060c08130803031005060c0d030b0114070c06030513110f060c06010806150324060607051b151804 68
    0x2120031012504002e001a4440114088444060140ca0340124076440a444083d421202c00356490181c0003441005005000c0034801d164010b00300c800802484000395440c5903101d0030080e010708034500211401d0b1060607200c1c402c8003c684905521150000c0240a9091801070107c03102d4002c1b04007600e041c807041260b000c421000944d00380080410101858403890900b03650087e04a565009038010401002080d180300ba0108030360b4890610783c1000030761b00c0103240048890350300380e46030311142c0800050000140718110f0344203411078400b903800303022a03900c083d1803201861002000401c0300c000e0061783d107110728080300700030040117000d0461400d0080b1400040e2030b0070420ba1058440d9000f610510540c11700341512288100e000350f00410320160500017010140c04400711402d454030040300800d07540c0d07881200302c640c2d03c3c2e044011200007401c200010b41101fa4108019441a4048000790001421080664001032020f6105001041003a0180809420b04242d200c400d01440b80c124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 689328633 1250 689327383 689327417
    0x10b0f03071b0c090b030d0c0605040f1a09190b18160e061509060315030111070302010e07090e070504090c0306090b0a0b06030609160905040c0f200c01050a 69
    0x101440d40c0078000f5207036aa4580304800382141e0200702014040d4000051811100741c0048240031050b41c0710350001116a118141200000c044a100a04181a0f1405071400c03082c4d02d1b00709401154844107407100304443d55a0136015409c1a00018510660400001e80364840b0200c40c00a848240090b1072140d80019a600703080c500b00c0c3c104000d006114401d00c00b032401d050310b68001600004081d1850401c0204c0081d0035408001d14449410041e82c0e4841096202904250610340c55840b90300d460f2129490301074044d003170781d100c0c024a502c114140010360141c0c40c0620803051901c031001d4100d041c10142803001400e10000251a529085d0304004001690340c8103002c04c150007109040814201907074550306880c1c407a038415200307110602c280b0609507504a48d50b50815100004103582c800c13541d0303003070700c0c0008127138030041d401440c01c1c0c420044507400c0312a10f0544e4600d0b664210905003040403010200740c0303c0d030402086e075202c5102220154080d0000300400e001904000281151000079 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 689329883 1250 689328633 689328677
    0x1d03010b100203040614092407080d090201080f06090112140601080105010e070c080f030a090b070926120306131503170a0f0e061b15010509010b0f0307 67
    0x152001a88001380030080c05034005801c100500d004a0781e5480c4c80744900004001114029003010040b60840c0c120040b10301039400c986d082075116101c00c0d122184000090002e02c80060140d001c06c00403c001101c0c001c540c03800c10300c61100144144010390900c205990340001490003103480ea04944110a1407400c01c004407070080101d14008035034be60420600c4440f081018222100740030f0801220b8002031002000e0740c0070b8100301d41a11b9180e940d1010700502900c08a007020f42440c0c4000300b0301c00000d0340002a04252581d50891003058420300042410549010a2280315030300442e2422001403a0503008580106000300702c400d2175903100146004440501e6440203050b145403600300700308840c04191000d804100e00240c2d04240d40480050500740c0d05814520030007903001440e540e16503400042d990078400700460f0035040e000f1054020f541d654609600c0340508500b900025803480c1c8102c501e81680c1000c0c00f40c500b00f95011016001d140c00280c040b90070710103080001e0f007107004207200c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 689331133 1250 689329883 689329909
    0x807080f1320010320182209060b19031104020f0424050304150e12070507050f03070b1602010c0f081308010c0c1b090213080601060f1d03010b 63
    0x202d0a8400c149003400542214035400c5c0806080b006003802070f0040400d0000c0da805c0505d00c0c181503070038861620000741c141030034140d40350054629203110f0138a82060703800701010310310440042001000c04010080c000101d01c0348032240500102c001e0000507810302c60391075a0750300a40b0140c2413801d600b882d409140c201d90002400550540701c02c101100d140488040d8000325420403915604164441c040040c4802c0c420481700c40d00c03607180000c15001085200c1c10459091100741c0c58100501d081502c540784c0d8407540d441075400c6444c2034541e140224184084035100e81869140811121180c2003003840c2031800c0c0e051000c54105900400c0c1c3c51440170074014070803003030380d03554070b0700c0600035400c4215a0700021001e030300d41802403031220b811581010100d03400c052400d62500c0c65402e0301903940140d07009003049a0011a9900c00d00701200c00305c0b800d03940d04409075a004d80e220030040f40d602ca018094003001803a40084101d03003100610320810060f10150010442c22031503c003141e0000c903e15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 689332383 1250 689331133 689331173
    0x70501020f07051014040309050108101505040501020f0106140108070905030d0c03080f0105030c060f0f130501020d02030c0606040b03160803031005041b180905011e060807080f13 79
    0x12000500c80311a881010240d0104105d42031050905441c01028181c0a00680b0b060109203400f040d00c40c0130005072617000b80b00714010190b05514041c1c00802d02d80003441650b016100300604608000c90600403c0240d0300f0750700f4009160f100000044445841c09000f002c18860210408242030b2014840d0300401201901c509405020a01e001090020000c000e410100400001440340c0c0d600800d06031070410080300c65030344400b00701240e05180d00c02d0f54028002803a000138030501d403144400340481140d80980949548241115050742c4a200d0344241c0240e940141000881c10320303081d0303c4451703240c001404540309006084581540540307d500802d08684c408801c004400300040460342c003500003914203220a981c10b8000e4409403580740407403404c1c0041111040c10300c00c02800040001c1416040600203969181804581900c04000451a1611715000480d105024103c5507008000944d540030032a44c0301c0099550341040a00a100e45c8946908800082604d242050104448072 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 689333633 1250 689332383 689332393
    0xc0602010203070906030527011e050709050613060309140d031e1418161502060a0e03071719050904060e01080307080d1e0905010e061902070501020f0705 68
    0x60b07003c4c1641100d5070001003014209400c1001da14000c1c50703a0f0300340d251144009031011761603040450241c1405015003080304c100c0b590140c0002203942181d40281d850381c83c2c8254446d11002441071600c2100c0c1c1c0074540d580603401c1081060310944c00a881c250242c1c6000708500c100c0d1592604100480b020740d80045d48595001c1140100d030200c403402109416410042840c0c217a40390303c0d1900340140f070350303050501012100740408001d100d1004002d0620901c40c2605499003100b812040000d0307103d10051181c030000402c03610f40c0d80302d04002241d04600850503c18556664410902e070000c0010880d4401d10610385074104084009001c4138a58442c551547c5c40c03002031004480260b884540b80c00503003401000b030342c0c50100841da103045d0031004807030303030303910240e1045011303001e00c2c01e400c9034003131100a41b5030060300280d000c4080688100003e02480b401d05c52400c3c0d41da403050b0380c4440c000c440b20104840024030366005042942c4a0b07030001d41022001a4001c1203500111000c0d9031035001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 689334883 1250 689333633 689333641
    0x904050c040b06090a05060d021605030c10090308040f021306080a11060703092303060403050c0f0c09010b07050111300f0a09140a11040c020712110d0c0602010203 72
    0x240c0180001c040b002e440e29410030300200009145c0c44024031038903006400000c0c0c40c4001c500e09404840c1903a24460201a05500a1803c144e907a40501d246000c10300503040054007000705400f4121250f1340503a98103101d034513640ca8418a90b0640c00049074001790a200c0200e000c0c1a501a05004180c1c0307030003401441240703082030031a018030000202d205180410207240040d4000d55041d00780c510076448005000700d8180607003040030102652560620504003084209a48503000300040404282075a41c0103c0400c40702e03607602000826554440c4002006200c0e03c68018007601416002d14008a450312100415510a901800351030300c030a0f07502d8101d642c1d07021048800c4040d901140584844610300600e940d0706806c030140940c21fa007500c40380f2030006c1c010300948010000c840501903900005c0b451038510008030342c0683c04c500882c10080b4215015001041580860b202030103400800b020300da07168030080b80810207803540080260170800202c2e980a0112000e0844c54000590700c0c14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 689336133 1250 689334883 689334889
    0x90307031b0803041d040510020f07020406090c0e092d0f071416020a0503100b030c0102030a020c04050604090f0b1f080d11031e070b06030a080a0e0105090904050c 72
    0x1c0580c00c4461141d1003003008102c0c04080818a0031103040e01500d0702d040340c94510b02a4140020b412074004e00c2400071603600b040545240091a04c240b08441c200201030f640c49000003641d03120078a41c0041401482c0c103140606124075859030002019008104035481a1b0142a41254060100810004820404c11001c4181c02160341107070150904503041c1146511003101e03803181102030300c01088500107100c00c42d2501e146000180c800101500d0070b0002da4681007008000c0400c60910a1003411016a06940040216200303c1240d0340640141c4460100b840301074a0090304040c0c005a40e00440e40100e10040a8001d0030742c0b0400242200d0304013130002100c09100d20000c4505448003000c2000200c0d00061650540003403800d16121441040900b00d085018862110402c40380080807078440044800041a666124003410011900e5074024541d4410050034000c20901c4108030092905005841070464614145485850680c54101054980714180d508907403a900c000d01c0380e00a4a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 689337383 1250 689336133 689336183
    0x306060c05032d0c011a040b0a060c03030906020a050d1407050a03050c070b09030d0c17040b072309040501140117090f1603050105070c120e01020307060204030c0e0c1e03070509030703 81
    0x300c1200d048c0844021280061004080c601c14a07041c480001c41030340426010740c010300302c400d80064085450303401e03c0c00c0c0500302d0b50058540b44004da1510b1050f0b8140d0300c06000360f40c047d031040d9036601d0500141c064150000c01002d0610311844006015840c00181c0ba0180184914042d0b0090354840500001080075035020204100a000c00034402941d000d460100300c03540f0542203400c4503000c0d20344980603030300d6006c098601403e070300c40d02c4048682c1101d010020000040300b07480400040c1c1c1d903400300d914907081145006000542c0a5901400c1721182c074102d81d000740f1a40c06079a01c4920181505251102c60100b240030790710390a07010003c2c84001c0c4280c83d070001050405420008007a0345101104a20118440030b0202000100d0080e074802c105640700103070f10503801c40d034036500c0f8240140c1d810114818040c1c840c40c460005104038801d08145c8040f0130091210f46495100400302c40d075150001820300080003018030040c0d40c035907010000d400085014070150146107200350303c10401c2c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 689338633 1250 689337383 689337431
    0x1509180c080f0f07080a09050f06011505090618030f010f0b0a06170606180d05150c04030503040509060d0b1504240e1308030411010306060c05032d0c01 67
    0x8102200030018040983c80349158001420303e003401c0e1076503416421200609a003040030f03003140301c0c520280800110000f07825040e1503d11600300402120408211a5440360080d0950000c001784070140c817441da810b01e0900507410060544050642d081c099a0850354003500300e2303001030303280c6502010034105030000720090a0545050301074980d1400b0074440160001c0d00c1c00c0e00411000400341500b00c0d00400500468078010032a00340e0f05150300704980e40791130000744002450f03c5003001c50800c510344001c54007166401b40c0a503040c107191001f003002c4400001e200b1608841020351920003e0850100310344221580b074911b00d00f288280b8244811910401c20319460759580005494190000750358250031103552034080c021a81c0c9a0880c0a00400b2900c00103001d504044184020070049140c083e14625003070ba000c020b41030740da000c2240d040303039101c0000d4081c2d002000142c0b40380346104da1400c01c0e090800b885410100010100c0302c0c440c2d00104400d800c0f87d40d0754040c0d031076880c4822014010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 689339883 1250 689338633 689338651
    0x130b0a0f0b04020304030203070b0604150e09070e1314160602150603010b010e0d080408011122030320070f090204260d0c051c0e0108090d091509180c08 67
    0x42d845c05540107542c91090402c00392550940c20000f50144e51650405808801c43c20644954192b0319440c0000003482540c5036001c40c0107003800031481401d420510f40c420103060340032814050540e101d0041d04032024241c0d240310b0080c50034075050802a13200000041180f58014122485d0540002c1c4e02d0b00000741c42c041c8139904004441c40c3c80c5c0c0e4480240c4c0311760701d03044035001081006441c103d0028480c5500502d119402c0c82c2c41c0ea00080b0030480a0001e04501c459503034101c0c2094841c585180c08540130043c04200c0d03001041b00b2454901d28071511003004002100c864075265494420b1490b4140d1214020320740014060007601c0b007044004580c050400a41e806803a2441625a2144c4200303150000304034940c80c1d10821310070100142c89620012a001c00050481044000c214820340010b09000c94001701c0412100d41000640d003079650f0199031294142c03814030031218800c0c031241c0301450400c0071659001c50f0001c031402c02241c280d01c4030040016a03000c5220090f10312003004014020f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 689341133 1250 689339883 689339887
    0x130506010b0702190e180120040f080102040b180f18011802032a070819080903160311030903010510060944030c1b0f031203130b0a0f0b0402 62
    0x4210700400485d07980224200410030040c1c0b800c03002060040a89245034440084403009003040f4940c2034005005444031086000807094031200b1840c01e0348103034070552000f002c040088948410308100303503008080e0010b0904050442c03443c00548102d00402d1041100100000100403049502d03604181c4112540b4095043d4030300f410000c2944103030560702060440b504c0c03440e0300303070500310b01e085810075940111855200e40203c028000c40d01c91401415010420748000700c3c410b001c00000b039555008086841180e0300310b8955044446405803d00d10300c00380b00c24090707a106a0340a000b445e2284031442010b40d030340b901d0220b000703192400365481911160b081151242e02d42420481000c85681d141c1642482c50f0070305e041d040341815070420100c085003c0892451140380b000318080105405055440c58a507101804015030400f10b0905141d140e402094903007030f0307500c90310301450344000c6070408020000400c1e118500c1003101180d0a0300542c3d6038065000c2c180007144101c192046040c1c40441c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 689342383 1250 689341133 689341139
    0x3040b07230409020d0608061302100801030209150111010c05070b1602060103030503150a090f05011406040e19020c0d1e05030a150503030d090c0801140708130506010b070219 77
    0xc076441c440c03805000c40c5142c001600c403035190715039000704008241c4803088078042d103441c04040700d0314502640c2c00ca1081002c0b00c1c188070b605204001450513240c00400441c4030303443d0f0140703a0b1007008078003041c0d034140003000c00c0e040142c1e01d007849191002116078640c41c0e540c101c249044038000300000c059101200d4103030b000c40b0741d1640c00205241034131307410700b4015525100c04200c604140d00da80300345644020b8090002c20a0381198009000d08400d02d04103001503600c428914000c2561507411641140c4c1c28041008095220b1183c150041c565030350044034191500030900581e07201c4010058650311000214040350390189070f138841d004c580c074509001d04584820080080c44090400f01c6203584503101c80c070000303a40c424407000400004040300d644420403921080034013400001230300c10b41d036200350010f0440d0741070140300030f002d240807280359032561440420b0b2402000a4018000e4034180d03640c080c0000d4040003094060408500001d442d11840e104000f0404030012800380100445d500030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 689343633 1250 689342383 689342447
    0x3120304050a0f030c05030703030204091406011d01050d060e040201090b0909041101050d0507021b0d0c03170d06120b070309050d0f1101150602010c02030301030803011a0702040203040b07 83
    0x1158070300f83d1204000a50325102d0804569260118901914601002070b40d042015050342c01401211140d242c24018404901c9a08180d4a400c641950100301c4020039107001c40b050480d18502101d05051031820500c0b40070500c0200d41c1c181d004901c0c0b1003218001d12003550b030061031800090003101300640c42c141038040403841500c400b40c070080c000903140342d12a045a0044095400141807520100454540500c0003540c0e00094072840311403c81d4012604e045040c24102c1c000c40075004a003000c103d0b0b10f10742c4c641c0d48200e400607a0041c068070501c4a0500d002e41d80c01900300802d41c02c07040041c0000c40741081c0088050140100f0141464005600c0009038042402207034100ca07814454180b09550301f00b0303030320b03200032080c00440c651a0034810350403d151581d80e00159905940208800910100145d0f0340b0720080c003000c1e0801e0400d10040041407805c10411100a6001303a4550a07c80c1c26030119040e604151002c07074502050404000030f1903402020a03441780b05091046905000032140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 689344883 1250 689343633 689343643
    0x306021b071a0a03021204030c11060906191b0605060907080112020f040f0606020106030b013302010612080d0b0913110f090408070b0f19020a0c1b03020312030405 72
    0xc402c03030401000c00d900e00007034041d43c140d40c868280d0b1040181c20707143c51b00c0d008020741c40003542140c1e0490f003040c50103010304042c003ea643c1c0442c041c00451a05035021449440715500c400c0d030104100b12140591002d04901c42c1c44510b85202c0d0002117000c0c18a0002c010400780c008005104000e44030004011f099400c1c84814841a01030f00c916601c4000c10002c10b000d8003030745100160241c188440010525815406036040724040d0a40b1241662509804d070944102c0d01c102d0903184400c08140c5200101c46040c041142c25540000a0302c541d0b07400018a0044103040d09a50550011910500b006002e00811005210031a050070301840c10cc00e04021b030499480d8003401080c03240c0d40c42c1c8040c0e12911030b107c0413100014640000c902e8030b480c048103194440302c801c4912031442004107004842070512a40140000f04241e04002209400300009400c4035050800300203200c4402c401003034250014401e945d188040804019045005251500030100107088000b03204100b00030128001241d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 689346133 1250 689344883 689344919
    0x9030e01030504051204080c0a080a03020c1210090c0501021e030a0c03051204081c05070206010e0a14070201020c16030c0e061503130b01090506010e1017010306021b07 74
    0x20001183e4460b420014502150a00110848180000e0225529400081d01900032604440e07101250392200307203080c1c88000d407503002000740c0d001100c1c480c45403400c026004015920f04085440d90b0140d003200d001910b499040660310301011742c60610407940c2c103026200705030040312043d40416950801c1199203102c0d2069410400c40c60716911810584110111042034402504002d0b0740c0c20a400e210b60b240d4808e00288150780340c07a01c0c8041e010742a60080c14440c4c04c2d5500585041e80ca400794201d1400402084040d085580e02039403070819484056990041d80039a00058603000400c505074034182e44403002c140401c0709036a04100060000c00080140e440712201070350702d6114100414205d440c01122a80c40210101c100201100c071007606002540c040c480755012030b642e0b05465011a2002e81d00140080d03001c807407040d160309082848800301c1c1c950345441c00c1d071404481f43c850101c400c2a0001c86402e0340008240d144010401c840f08034260180c400340c40401d03d058013106903010020 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 689347383 1250 689346133 689346137
    0xd080f130b0c120f0418050a14040804060f35090304030804090c090e0705030402010806120a020114090d0b06120102250609020402181306230f0d0803150409030e01 72
    0x1007664001d09104d0540d0010142148105503070ba0101040401402084600c0d52015140c1074500c2d405d503105540740e502071600060464501418074100301c0e00c0e402840d00100c14000142d481700441e4402c400c000d051810198003214110711064085800030b0405011102140d0042c0b00510114111302d089800321000c241e000901900c0d4104107540040307241e071190f803000744a2020800100e030814000d510843c0b00340d03a0900b4a60340d01e01081181e4211640c148225407022001e000154080c09404a8001c0342d03a40d501d05024640000662007414401e04a0b020519407091000e08d05080300f03002205280079008ad07040c0300d01d03100c8485408290400c2e1108015507403070f291060140f1580100c500d00c1c3c002c3c0040d540c482142c00c0b2024440078080a0718011b8402146c1004490a0b40c0718090503286250f0911049192500d6000883c9501c01c00c16a03000c0c42c3d45404143c0350703555120344074a491060001030348030300d0180c5144000540e20010710f03018074100031181000a500102101d4540b90034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 689348633 1250 689347383 689347387
    0x1030b130b0d020d0b1504020f040e191e050c0301060e060f0f030c030402100810170f03160506011508011502100c0203040503070f03020d08090d080f130b0c12 70
    0x2140025600c070074004006904500d20442050505c90350030f501c0c61003040c040d50b109502204940c18041203100d112000b454410052009100f80c014102e115a0419a01c0c070b12072030310981100100040700c040d21000c248800500c4240c2143e1843c50245503400547c2c004514103642c9003500c040d090140300d11016104800c0013903030100c4500e080080c5c0e4a4590009141354483c43c100542088560013943c05034440c100b500d036146012849000114070a07032090307001c50711691600326400d02c400da841364031807400d0255484c0e5602c040400c1000d041c0d102e08500084410b8231140c1001414180183c03c5555401e0304407040d050107a030070146560458081c2d000c0c200781203620000490a114009498420003030401e0599004294004098801d031179048003665030003540d80c025480041000e10000350000c0fa070035840380104d0f0b0400c000e421401c0d000f80117a15010f80f5550740c410f182e802842c040300030100100f1075480728420030141c040604180025a803424089950103a601c59039500022521580 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 689349883 1250 689348633 689348651
    0x1110301150c080a0e210d1407051e010b18010603050c0a0c021c0b04030f0807110705040b03030c07060315170c1207050a0e0a0509030301120807020103060f03060b0f01030b13 77
    0x800b00c0c4e01501b4207504480d00380044001420546503d10300f1074400028441e190b00c4960805170724102c0d441c0035804402809980c5001074491200c0070303c5500802c0a5503203580104454540307401942940e0390446204583d503061050150403070b00017030071074041403900740401c01090703401500d041401ca404541003020740311951050001d00c03440841c010600e40035002800205031704041d800a41d14200d03203407840c6990306e5034001c031141e5100407100c25403580b00c0801002242450791115004900280543e890090440071072464020994810000030340e8911242c0038a50308243d83e0308c09020301c00b41c5280c070101400e0542d40d4405c3c50580c40d03446460070321014092181d04000e010000c1401600301564290303074131294820208200c031141019410303c000a02140d07400300841e4180c9102111180c01e00190b138071049000e8110b0202213060560b01d039404103012500140703090085126030310108890800b40c05100c2c03800001b140d042d050500741020368500303603540e521508082c040b00b01e0000b05038003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 689351133 1250 689349883 689349889
    0xf060f1815050406120605090d0207030f050f060118060e0c07110f03061303080a0507050f03040c08011503050f1605060a020a020d0303050403080c070b070e030a0501110301150c080a0e 81
    0x396660002d5401842c10400240003038034090500075540c0241c10401099030790800385500c904440800d58016003020100b40005142c008021085a0055044500c15000500990f14003102030300180c00710281d071101036500003541d0240102134960b0401244041c00c080012074414010080c005000000806441e001600c41d003502010809000b82211003a081c404207072503400340c1b010340035000103000300300207002454103026050103404150790b45c030300c0c0200c1803551604541002d002110450300c0b02c480091490824011100a460341d010358240e090301e1441c24601c0c040660315880e08540011a0b00910500740e1005002100c0040d107040b99101c4201c10200d0400304c5d2500c0c000c2d030200866101301c0605606038402445903200384c4414500d038503083c1040d0120f01428800424403090307103001502e00f6114046c00c004089025003161003014090351035900799408030710800d129900120042100648440e41105201c00609001d142001562111846481030b04680c01c00d00003014025500d5032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 689352383 1250 689351133 689351171
    0x2010c051611181e011d06011101051f0801051005010f0e060708090a050a1203030207030314040b100b0f09040209150c011a1f11030f0d0f060f18 64
    0x40b00030301d400d0340100c0000222035800c000b61880c100010300d0301c908000012003c00441d059441c1c1c20f240400c81c1c02901403030034140c40000d000904000c0849014040c00909010722801104202000700c0700c0c04688200640301c10103548101c3c410b0b030401e020b20102400d0804502c0540381c0078039200b51000a81601900e108a54510241d000400081c60509021841c4040c2c440e14404482c005106580d41080100c1c442007401500a00c81400c003c40c00041d010398000c02d066032080c1000705440c0408006445560303c01c48058812000e08400c0220340018a44803601811b0b42c0300c0c3e0309003401c81c00070785508a0b001d000c1100f4000c981c0002d96180d65558804c00089119046100c41d642c0ca4101d4941c03400790000c418141443c1444902d5040946000380901014403070343da004140e10804040c00311444855007051004600007007104041d00400f84004000556000c03070080b51020bc1c55145038103c2d40241d20440081e410400203000c41480e8400b600b202401c110b4000c0b40904030100c0e4800742d2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 689353633 1250 689352383 689352413
    0x201f0201390203030106080106180f06020c01030c0908030702220203070f020d0c0809040b0d061b1b0b0106270306051f0b0406140708070c1502010c0516 67
    0x101c14103103103141c80c1c0704414510400c0c41e40d010780d18503058440c1c210180e80c3e900003800f60380d0204d800b150040c015144641c1c41c000381c80d804612903c1d00c1580d150b00c00e105601d142e03001000140c2000441c4900d6503050b00402401490f03d180414225241040da1a00d234001c03100d0007807007240541e48950352041c2080f106210b01145810855a07400c0c030202c050b01d0146c040d80f1400150180b108000034a9018109819041d900820264a40404e00b010400205910545594490058100c42000c200d491007021045c0d6005049045946030800000c0c201c0402c00070b0701041c4030800091f00001800120503a4112007441c101007900300340c2006442200062140090602c0c40305c01000000e100700c603040a40503118440c88000d10440e051585c182054050060158125080000700240380c4154a40007011000560141c1050155504c0f00324540c803190098072503115801c0d003400b001d01c007a01c41403603584c800d000030400180f804602030b28074002c0600180c50751558140700800c2c00942d0301c0b44844 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 689354883 1250 689353633 689353661
    0x3050c040c1e0818030f07020409081626030c0a05030915040b010f090b0f06090310050c090411280504090f06140f010e0d060b060313201f0201 63
    0x10503408200300500614040b6490349603180c1058241e511104d0100480b02001189004145041026002d00002e070000b00c2040750002410419038880b44041c5004684140c400c52582c0e0001c0c0c00b502c1c400003040600f420781c03031441c1020010b00c14198410000c42d00c1480c018284036849584a52240d400c2c07003120800c0080c1482c2c41b030b0030042000b04040c03e06042e02c266180c104419500e03405e00070b04940c40c0c2c2c11882d07001410b6503c240310600e4840301400c41220001c0071a800e40c412140a1015101d0640314010400800328030031601e0718050140103014040e9440160401c01002d00700e81b85d0071040c40c05d180e2100003400401180500c06c40c200c03005400d5100d0240142004600d80720300a101c980b0410341d40e0342001540081a151800c14218595816034070701a81841d060100003007101c44650403212113a542c40b010300a9211030300510700c070343d41c00001c0444c03406641c108418010a055104604810041100c850a07580d00000c80f11700307000c000c0301068005070380728240d004240780302140d55 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 689356133 1250 689354883 689354927
    0x206150639100e0d030b0120010b03120d06050108060904080a03090609031e0809100e070503010e0d2a060504060902090a1a0406030302031e190804140703050c040c 72
    0x101c280241c1103062864000f00480e00c1104808204504032503a61141c540040c3c00d2030a84d40d84441c840c94102c0c18669a500005580f95a8800091400205c00482030f010321001c40c59115000403481000020242800c040800745802000100c40300170041000304002c1d000308a02c01301922990020303101983c4064104422481800c01070124042c04e03450160148081034014001803003043c00c00d00840c0c030800104582503c1d440c0400c0504001c242d00041071084810028a13030754240510901c980704403002e40007410115400810f46154084070700c2c1001c510000d4825121180290421069048400090a0385840c58aa0046c0009000280d88250528148114400240d1000080484c4d540400e0500b60f40c400c01c0c08190b0b1000d01c07000d005a0414001d0092103454010f00c4030b411810003030f0f49803a00b812190103940070300f210594200000e94600070403042105a940403c21200300c0c41c014404285507030b80e801c1e03075003144a000d54000c9403191a54034855011340c03044450341d004018454 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 689357383 1250 689356133 689356153
    0x140c0604060806040b04060b0928260106080309041e110901030b010311040e092a0913200a0906090b030c0108070806011b080a0206150639 61
    0x3041d41c441691a603214500e04803c0d80c05c24170b400d03ca841e046540f240f1440e420022120304003d0020030301d40c0119022213000a03180c0c0c2c200c08100081010b490030105191400000241801560841d5943c6e0041c6a140c031505000c040c0c400415244000021680815110400070044c0e89040400201c00c68031403c21442514006c00d110103400744003001e1b60204869550400114261140cad0084154041c03003c00c420f00c0303640740c1104c040f50301019400448520050304400f06003d145890507240340d04040c8000002c0e94600100501c1d00400080d00d80041d42c11180c071142985d031510240480b24444070040e400f0140c54500803500140302540d4100034883c1d4580c2e41501030f20044001c0340c480d0140311200d018541c000d50907a070042e43e4664809403590344200040d4bc10740f60104401c05802d001000a500003500c4a0040042c210700d5030192680c0e08141d498500d4505a02c101c6902c541400d01c40c0e64041c036203081d0651584a40c0f00125460b0b004110800c0300418a00091501d02c4d0203002441 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 689358633 1250 689357383 689357387
    0xf2a030f0106060206070518100e15301503010f0e0f0d0504230f0d030f11060c09190506030424050709060804020315070f08100f03140c060406 63
    0xd0302119491380a480c40303075450b00340c101e030244502440107090820358100c0d05082c1c204000c400803407241c01e003404400c01d000345000407014148034042c607031a10070015140b2101c1d441d000b10751070140e500a110350260100c905450030890fa00500e05d05540858800070030080e078094004a0140144850070011464880760080d200c0100c500000f210348141c1074040c146030310520448045400d0b1013a0b03c0f03202c5140e0b42000c400440c00700342d2103a100807050f10a401d81c1c1c0c2c5130000d2135a6148651600d42030807000010180c00640500d6403248107400038010081408003c2d021100609803c0f10111240e101403004003050007036035040aa0002004400c0204003d850f0400d40f680402c0f81200f880741104c82d81d003d03829594101d0b04e5034000350000c00308000842c0103516030380d040f51001341900c0f4952116007400d103100303000302c0300d01000441c00420082d2454200c144590415580c1104c240b00d0b5041004580012219100090040a00d00d4102800000504c0801a045401045182c0d510794031540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 689359883 1250 689358633 689358641
    0xa051005070b0c070203150702030d1d0d0201091e21020d020709060302010c0f0f050d051b160e090a060e070302180610050d0605040e03030403110f2a030f01 69
    0x7110b00700500301c0800c000070455070943d941644e0080c01050785036048010f0700c40282001d00301c001903220901c4440c000c62140d0190500142002c45261205600c90a0841c50085a26100310070b5900d01100341001c5202a9100b5609034403a0b00350700740c0e1011502d4103d4400102c411491343e600888412090f41c180e000c126807844c802c19908503221251220300b544101e40103032000034040b404100d40280004c881c6040110305602a00710941c042000b0303280c1900b84010250380d40c0c00240006084060110404400301c404880d00b002480c181c1e0703000111408045460091305852114100001c607080d508104020310660300050a0007201c0451048035602c207560702040348500b49483d0207404070190001040e00c9030724004c140d049a0f05880c1005c1c1d4007603222940c400f14180d00c403a800314190321117025098603100708400a5a40b8a05070a005141c00d2a0f0f0711a2211508080c2c200c2203030074800030b200001c3d08210508100344a00b00c1d5030140e88569200101c0750503000300d0814400703c690640c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 689361133 1250 689359883 689359897
    0x723030114030d0c030e040b0d060c14040e0112020d080c0a02030607050f0d0507121a040525050d1503080c010c1b080d5f060a051005 59
    0x5084500041d5010107031100c2e5824414000a03a40060074004244610340c081c0a42401610005800b44810045154107064001c2650307401d03100c0810700c2d46640d0100704a201c007080e000c0068203160401851488451317040c85441072411415079007405554402101d81c400541c071a5440756508083c24135943c6400407680b050380f003401000001102240944203c400303c08117080c06500e0101d00c850702d80300411010b0710318010000c03031441c1d4026052443c840c8525607518110f440482d03022580400c0240c0f40010900c140340b1079622030030303d185a00840c603c0c00c9a581420000e0300c500c0c0500030b034030051407240440300c00c140c100758002050086460080a490220600a10400020810555081008105900300c260302c0c03c01040101d1040c02c081c0866821402004c110844d0310300d040d094106155032841c0b207220503007402d0f040740c0740d80c49541c800a2018400e180502810744002d000c84002e111104040b20b1009800030f10203aa8026444002d80340080c00c0c003210310180d00c00101140c0040c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 689362383 1250 689361133 689361149
    0x309070e01080d08010501110c042c0d0509090414010c09031101080610050904020f040f1d06010c0f14070e060414040f12020f060a020d0f0b0d0b07230301 68
    0x200d01c450001c281000000d0f85612448996440e042c011640140d1910144c5a04d014611950a00740c0d6140034840b00c01c10500103207041d58581400c0d00540e8003410b0310030522540061070384143c940d045025105154000c40d602003003540c0300c1c103000c01304031101d01a8909a51038440c0001501d90440404c10580b401001c000111185500040da402c001c00d45800d0342c4581c44a0f200004544100018600088045e1016042c01e001410221070368001d50400e4091890703000080c001014441c817040301d11240840507800e40d040c0100040c0c0040b5000401412507030f5040c1d410401e2105d03698446820030810301c101c1da10141d4078441d40350401e00c1910074038400c0341005c4041540c074282d41480c601841d04504001042e030b03002d64884d40203000c40e071401000d44c043d60085a682000c20300c80580700b0070342c0c2071700035a80b4418090034104688400c0200c42c03405241101e100400e40300c2e50084100c4603440100c41915131907940341074500b00c41d102d50398292000101d000d00a040b2001002e5030484d00c600c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 689363633 1250 689362383 689362409
    0x40b0310050f09010506160804030c051f0801060509010c0f0303141305070e04022409130203090303130602090a030305190c050327060a0804050721060f0b06030907 72
    0x440c00c214402d1030300500103500054940040c0404d10f8940010440700e0194150a803d410003940d900c3c42c290804d038000c1c2c94461070040200f0050070491072240345404098000590754411503409444110103004d0101041710205142c43c0f640d000c1c2d030f41441030a80100041d1240b8141d4600203000d458001002141c400103500481c0705044040100200244e2003c051b1420a0400e841c0d5032007084001c2050342d00c99402050384103854001c00403400044c18105920b60340d0181d2006200f5032041c1e0175408040540f042040042d4000040252034200c00f0040c8130800f400c201d17040500182c041e00080380c1e40124004d00000070550840002d1100302041160505050890101550744c0800010058241d40081100081d0480a50441a40509109034915581c0810404100d8039042540c0c0d00b404030310740d4424130080c0102001464010308005080d5aa0095423481d05848183c3c0c030800140030313070740380c0042c3c03604022243c0103191080b40c0030f81150784a00d00056115501c9280d4070440c0803a1840c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 689364883 1250 689363633 689363639
    0x40f020a0902070b0a0617030a180b0c0f250b0306220c020c0405060a180e01090f110307080309010c080415020321011a0304050a0b070305060307170a080c0a08040b0310 74
    0x44030411f601d41a070114040c0d42041e062440a40b41c1030821283c4071003e19170010003040d40b40e11400500040202e03100103100849010071150324000021400b20104032407e070710308000080c190200300603210701c03c100584030b80b07518001c900d2900301110304045a010703008d254252440c80b41c1c4070f0b0016003016421a800d00715540f0038801181e00076540243c0000c92498203100030001d602c04081c1011040400044140c0203e00075400c540c0d0210042751002c00c2c40800c40d05014061200081e0003c04802070b2003420b1420010342d9880c42040403440c10710800106400a00045206850003403120300c5041d0710000c08600000d40700c0e03003e4042c1c4c0203049410442818100c40270000103040c3e070b290000c1201010005042c803800d6810013003040321680700d444943c5001401d11000b45000300040c0c0c602160604181c0c04050a1850302e4106140d000c601c980c0312400414001060000039410080080d5103040c01d002d182d0030111402c038050440300b000a00014014400d000551241a502d03855031341c40c3c1c0d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 689366133 1250 689364883 689364899
    0x1407090203190b12070b04030b01211106071b09050c041401210c030501050f041109120f0d0225081b031e0a0b0a050f040f020a0902070b0a06 62
    0x640302e02868a41c2e100c10805400d045501402241d20001c140c2c80e0340c5900189143d1808030140c00000c07504c80b01003400c008000c0881c88650241c0071124100c401030100806ca59402c94101b0f40190030081c007402c18840c0d64407100f045500840e0006100c0100c4800c10325503100e4400c0b18400c110340300749032000280b840e044c0d400548060b508030540c48010904504c004403030710003408040707044070035400e0708088001d1410311699501c48843d031004502c561510040001d042000310000740941e06000c04200513500ca171088912540c01100e54842003030554080070f2800034180c119030020f00c2141c1c21002002e8000840e444500918030341030185804206e08900208183d11030700409134040e140c0700c2007450454080c000c6100002c0c04803000324003082080c00c4c0301e5451030065036040d08100000010701928000481d8803034420a01480319040c103000c81d400b600e400403c09060b1801e1030060100315550302c40003100030710750418259100c010394140179408400c01d4688805041c608000050001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 689367383 1250 689366133 689366137
    0x3050f0c04090c0303140d1406010e010905060a1407020607030c0c15050912100507030e0f011104030f0f02150307020d090b180f040e0303010f0b0408030a0f180314070902 75
    0x5603ca10100b078800d00e1603500303403000b9900000910038803509010101140b00302d03100c0d8002d008021040401c160910320005071041803c00141030400109403818005625080215518049c4920f021030ba241d015414a03682d070302401034000e5010000140c00b80600d60702004011201c1d0068103501e000c169038803507403400201c144074220085074040c06903d581d07140c00c680d00c640c458101e405a45481044070100c03011100210b4011010907a104411a513401c020000d034951694880e00803c0200499128451a40600d01c001011620000041d008105829900600482d0f018007034400000d118800c40605810072181075005200da6a40740d00a50310429844084031a4024640d140c000e181c18041160b0165070016600140c800c9040c00c0c050300c0390300c0340c0c1400b0802400599100d50509c403551903c02e8069110442840040c8404d0121030008401c40e41d4820003414280c0b10700550802c103480c52900306042e005114030450f0b001090103008000c00c483c000512081e41d1034103440c1d4854804034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 689368633 1250 689367383 689367401
    0x105040302070302101b030807120203102603070f1a15011b0f05101b09120c170d0305060103090c050907023a05070203032d0403050f0c04 61
    0x1680114010800b40c00d05000148041c001444c1240340940000040c950020401c84107c00040c5600c081001481c2d226840c0d411203c2d80c50803d40c81c5090203180c00040705000e00582d40c90259205003120380050405201510060000070380f0748506d51741c03c0c144076000000341d0030b44640300703806090300702200e01440d981e100b050001c410300c1c4a00d42ca2001103807001e04010544203280241c4e895040401e12001c000d07a1002e100c1c2c0f00400036804000100c4e4141e40e4240f295410f040c15130301030700300d41c00d4010080c0d009480b84c4000c1465140814100700700303041c1090b405401019003101e10f048e010a00032030000c103203443c0e1fa102403000da00c5000044040700c86140c4060188240c110f024030440c074041000c035030007145510403510080c001510505034121f02c05403185012100b8141003d09250807616202d4010180c2882401d1103910340110f522442640e120241c056080c20b001c142c5c80441050801042940c14140c0e52210340713a1030000d98804411082d00058450700070000c00c1843c09000701091 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 689369883 1250 689368633 689368637
    0xe0907020d1206090608100609060302030303040303111c0221070c170c0618010b0616150912090501080f0610110c09040c15022d01060806090c09010801050403 70
    0x1a000201e802252030501e5000710700e071800e4898200285207515402084040e04460003e00004c004103400b12046a150358040c91350300d401c000f810400341c0d80110660354400e03054200420354108240c1000181d10810340d80c410b054148002c03200c980202031b405030015024070b240c20327200f4803181c01080c40f00e03040071283d4600082004803014001174402e583c3d80c022825010750103040c040f20f41e03409820510101c884640c060f48644800d00703076410902640b0381c0041c0c00e40b81c581c07800c0684543d105400100758005040d0506d150451810b0341e5a03a400300710440c1c2c009a1440080002e890010070365851031080d54005401f0705d0115010000021115000f854000e166040c1100f9180c0141c1c0e0310a0003854003611340c00754070800902c039140c24030f0041c420362044010996aa080c01c1c41c1940448240301c0d0f90045600c06c15843e01d07000061608000804440f000c480c88401580901750302500311a00480e00c01d000750303c144442d4000000d0b0f0001900812640d10301a40e0302c030040d42d82210300c2107a010300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 689371133 1250 689369883 689369893
    0x70c171209070810021c0507170c390a08180306090a020d03090b03040c090c050313020108060a0f03060e07120804060c0201030b0409050d030b0a1406031f0603060302010e090702 78
    0x40140d90741c01459903410711030003940c141c905601c6d180125101190340c9808540c60ba0768080208140c3c80c030700d0b50720240c3d45915604010381000404070503455130952411505200c0034072020300b181034400340d101a40f068101c5106150624020548ea0440b02d180b0500040718502c004080c603010507018403900a0100402040b100ca40801079404401c0c0c400780d0520054480120300201c45500131485a40541c40c510109881d10300c00034101c072603085030142000000c1c01842207c0d0b149400c0d083c80950246071070072250700c803800000c5c2c0c0e00c0031550000800e5000300000208010103904560f00c5840a082900c400c40d40c0d4a5030500c9281c8039010080180703200300030600009028184071581d440c018540010300c0414440400c007144c100d2601030b10f0950083e08401070040d07040c055030200890640c1c0317140c041c603d440e050510344103100040c2c5200c0e4502000040017048508002c8140030f15410342c48041a54034a400b46c000c2185001c02e03800241c014840400b9801c00c100350a00850042d80148 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 689372383 1250 689371133 689371153
    0x20405030303180f0f120d0617010903080f060d0f05100911040606020c010903030f0323041b1401050f070b16020c0301020307090902160c08010b011209050a0b070c1712090708 77
    0x418140d00420320003042076560000440c0b841e1019492107a0200209d0000130611705070b041c0035011920003090811030180c2e680402c4044d46401182c041803903071120566011403845d00e411401c0401c041c0071924603c0c540842c040510940c02c0411410070401e0f6000c00c02c1c56203070f001c02c0340c441c00307581c4840c0c0c082100704800b000024420005640c02611703900e000502d50f600b401c1030203c058220340c0603d4014a000d403d1000b40030303508518810138150310300d110807200e107091480c0348189100b007801414080c01044c0c1f06000c1d0400c0e0300320f80b040c41c1c2c00515100e40e842c1440c42c50080c40540700c0c0c11030052041e15122280e5003014801c032400f40d0011f03241c008005203004803900c0a90710010481c108400840c07040800216801030306005480317002d00105009601b4400105000c0c2607117034180210382055110340128034045140c0d81c030160064141140c1d41c0d503480c429030b660050000c0050076031213410b01e44160001d8050241c241250480403960036600e0f1045804d0382d5840c00d005604003904295581c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 689373633 1250 689372383 689372413
    0x11041e0b040b030c101806050703030b09011a0c01020f03042301051e0606131401180509060d03090e0c0301060e0613140a0b0d0509191203020904020405030303180f0f 73
    0x50a40c140041c50071b83d290006510365002e8a45580d40000f01243c804220481055014020500604000e403a00c0115615000203030a901d40680c0f0301da80c0041002500710b107202029012603481144907410107580e0304203441e07d845540240d20354189400820030070b41071014010300903e0b003d010144202c00d40d80010451154188801402096200c0003c001c54411040c8a00c006801495008504994030340090005003c0c10384030012165040c1030751400748119503458542d19000101641c0c030b500c50840c580740030349030303030328183c2049009104001c05c000e0088a0040218140c40301c0b0356604880340d400030188805400707003030000c42e0f852038a50f00600040c0c0051041c10105030300185440300d102e0b510400590b40b544089000a4420f468404000da80a402c0024100d06029075181046080b125251032180d1400f00c50028205600040c038203680b903403240c041e01d02500008098a5590921801c043ca0038106440588118090260b0407801b0314004111107a02c2d041040190221105010786 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 689374883 1250 689373633 689373649
    0x73005070611160c091805250b07060605190311090c0d0e0105160906080a020c0c0405090114010e060f04020f160b09060a0b01091211041e0b040b030c 66
    0xc020b201c000c040c800b0300c20030740700d000452008078081c01c8400d4145003403140240c15500c409926443e4024600f19820014000068040b9075444030206c001002c401c4c0354549484140320791003c0048500400e550040c0102ea07442042110300484d628081c007404000c451520701068030014001e412120b510540b0b5007000700c0702d25400b080e481c2c0901d00d040381c0034074a00f08440d50150092600ea66450030000ea003e02c0005102c041340c1c050400301006490300100500110004000702d00c569004644000808010000c0c08003241c0300500c00c1c41503103400034003c1c1c020b004c0d200a82000b200120700000e00b4070001695180111400780c00f00e0f880e22030402c1840047d501810766070803142c40c00c102d5040343c1c60065540c1e840070f034490204040e80e03041428145103840c0018012580044c5460082c00241c1e030008440c0b003c80f05000748403540c444480c00c2c403203220030f0120411504181010b8500c610780e81110381700200e00a01110400801941c00b082c40119500c0d41012501588039031019060362404c021 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 689376133 1250 689374883 689374901
    0x12105040f060204091a06130320060724090b0106200304060f12020310030b180d09080d0203090f092a0a1710030b15060730050706 58
    0xe04451200318030394403142284d1040c0e0019500304d544000c82d081821140740e10080183d800c0f02d0a5007801c0d04c8407c9580018054400100000c44030400000078100301c850104450f070000300000c0c0c56229a080010aa0070280101810020300b00d040c81440500d500c52858130076003210761807500703038240301041e02c07400103250110301054a00e06840813040e2082001304050480e039030b5010303110f0051a101806c48400700c8001c480040c01070040210100408038140200d9410084521880d01c41d1810041000c0400c240600030b8040d96020300513082d0046180030072104d00c00e08442034683d90820403600c900400f0b0740c1c50317444480c9400ca243c043c44c1008144c1c0d0808108100c4806072020b10f000d80e40569a8090104101e002c0801d4095035640c010000700c215040b030000501380b5241c0703814500ca034401140002070040015502281c02c2002400201d8843c11002d0460b5503601018240003030300d4141307400c3d0304680000d0310070146031184085c5c0c2002003000030364403424202440c03641d81401030f110001d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 689377383 1250 689376133 689376143
    0x20031e0a020706110a021c02090708040503030402040c210504020a0f0614180d0506012c130602041a040f09060602030403060c0507020919050703020313020108060d02220b01210504 79
    0x1030305d44050396441c0c2e02d0300d085941d02c42c600341103043d42d1f01c140254450003c001e0001d225150041201260000c01100c0e8069411a800504558000c07025100402c00d50701d0a201030300441621440c0c40e140ba4803480c0107500032115464240d5980500c01e140b0b4280340161000601940c04e44001c42e07110348041d0004034050394440701340d1000880440c2c0541c5a40105032025800f81e001000109070090345041002c600c41020007089c1f2001e1500d06080c00054802c1d101002c21402c1002840242d0f1f060350086c00350520314144018415101d83c0b000e070010b001d0658600c0030a140003071841d401d407295404a4140383c02650900e03145840b40d200501c0f10b05c2084091008c100070b4003005aa81d401041e1080c4000c1b1100c100400c17024480004403080280403109044c410014055110140c801044c1580c0d07091a024807640e03103000220300c8103229100000c2d04007002c40911140384810388580500c07490840400c00503c81c0b040011902900d5488292019807070288014401c84444d4008a42c041c0c010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 689378633 1250 689377383 689377393
    0x90d0f080d241a03010b071b0f05031219050d06030c060503070e10051b190b0613090309092a021b040204051f20031e0a02070611 57
    0x45400700141d070502c42c101c9940c810406460300c2d44402002d4000083d11108843d04201501000240c00c03a01c0180106810301e040413a4090411007007140f4030394540b03210800c1200c129601c2e8030404040f11540a13040c0301c0e0048010034450001700009655a0b0350050140c8204020488802d950307650200c2d9850744011748400c0040041004154a41c1c02844541e80d526541c1c86e18280080104501440e154400d1710010700e00007445900c001994800c5c5044510020700000300e584040c81d00205a820ba00c01c004c51403110030600a084580900c12070090700c6500c3c101680800180403202d0800004000c500030010034401d01c80142c1c051036440700740c409015a80155250500540707404c810403040182e11022004114020866514003841026281541018180800210540800c1519110602d8842144582980f0500d4003219014681c483d611030030505402c4561603600c0f4401959600d460f2043c0000048030000881703010030030a902808031f103414200d0450f500c004406480100b40f03d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 689379883 1250 689378633 689378647
    0xa12140a1d06100e0106110c040e0f190b06060a1d010e18090106060203091f09051503040218190510050a0906080601080a0309090f15080f070902090d0f08 68
    0x304210060080f20707100d8149842038034000c55588642d0f0305800c0a01089480624051030075800541e1110b004021240410311002042e0752901d00b10401d00d5800c42845400c2255a10089014a2041d0b41d40200203040031030303a84105100041c45015000c0c0001945212202d60b40304810a024003c86014901781d4154250080040d5420825024941440c9111814408412024400c0c0e0b0018219400510309201085c400143da107040c1400e807040c0030405601d801c0020740b0800104000c5c2c04018904030301d0750103000384001607800c122401c0b8020740f800100004080a035000d114131131450b501e4505030004006200001821001d080004070100000e00461280d035045011400343c4002c00e00001c2d440c0c50149520b24058060f4800d034080e4001d040e40d0300c00300764405c181a0030b1711000f00001c181c80ac60b880384580205a890f0f50b4150a403040d88010440d0a004102c0071040b15022040321801038807501c0d15401c038031991484590100c1003c00600c005000c0031080124107010345403490900c84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 689381133 1250 689379883 689379941
    0x20706111b070518090a0614091504080304021c0b01090b191a13120f03110d12150803220b0c030a110a15020a12140a 52
    0x4600088004806004507000d068010620142041041050018101640303041e012842658000c00d213240b0b12a80f50002034001901007120392000303640701c0401c00c045000c1e102162007904050700d400300207000320b1040d25410040b00c88068000c1d508a02e40c20301e0b6465580c20081c0d82d427003961414103103002c94003c0e4030218411614050003400c589074085409a24031040004100400079160803c2e02201810300025005d498120031200c034003040c05542d9440d080350022004003d078070590f041d000c40360028041040c890b1201000074401d071900003007130550795401501c98000760034800000b0b140320500005184a034004002c1c003c80e40348041c801d44e03118804079056501c407050a80001091a10940c901499407901d8001003503a072400b1030424404000b410303240d100d40d0344958100008461103924084060161403611544a16100f01c20400e10324204040d4000240340d10116000a920142009842c010010440340e9041c0180f1140c2c1e40442000080180c1884144008240b956444500c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 689382383 1250 689381133 689381141
    0xb0c030712090c0501091e15051611101e0f2109020f010c0f030e0a0506031303031a011205090a0b011e05040b0612041403070303060e10050603070c0204020706 70
    0x79001e03c03000e4904508000024102440c96441501d1004031100c81d0624080140034440540d40c3e151644050501070100440b028041d011142020f0f002d200041d4041100d5811190341010042c0c40c81107404051b10015290b003019030005190f40349013018884101c40c0b0030400c1c44501025420728183c0710f481034aa2003050882640814500b41c2d44154450640c6070026409401c0b40092a00c0703031100f11169038080305407260b40002010302880c24420310661303a4410300700c00501030150800e52689002c80f000161303081c8241c82070f40401d140c540c5101c0d400810300c004003480401a180c01020180b5605564002d240045c858100d9024075031607140010360014a103070003800a0020035000303e40c0c1c0c030480311100c10540e0246100c0c2e86084815800358841c98151101a52030f0f003d000c801d91340701c0c113150500701000d401210282c000029807008242e010361140c0d0903a16131807011405075a800e05030f045112010f0240c0347c4e010205200080a42e8803400c20700c0c0c0000e1020b0005804d0908a075500c400f03032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 689383633 1250 689382383 689382401
    0xf110f030a0507060b060f040e04050712050607090e090a0b0a0f0612050f0d081609031b0807080f030f0a030e01180203300d23060306010605070b0c030712 68
    0x400020343d03034044c415540101901d40d24222000c1c2c1c82c0500c0211003014502c12031243c048100160340003d824010244404030040c800603a44034142c0419103020b0740c03103a01c2140e400011800c2c0c400041840450f185006100d02c441d00c0052092406544442225020080140c5103503030703d45480e0072406100d0b001c0d89005080400300c41540d0351040c5041801c100c11091404075076481302c0d942440c1300354400a020b0304034299004c1d80e015607010582c122a00c040640000e4050711445490003c0c16150020300c0040740c1c2070105442c2481d807210f01c240d884111204244100364400d000200032004c0b008001d19a4100070b04000411540039644142960000403280300b10000d8046c0031015402c080c090114070700a000c0c64440d10b40ea007101290650102c0c0c80c480e003000e0401255040d0280341e650301040e888e4108040c582c0c0c44a01602d884030103214101c0b0301500034003d041c0009110b5020782e00f03680009922500110312640d80e0507142215800050080301040513100d2803000d00c144900c84d003216 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 689384883 1250 689383633 689383637
    0xc0c01180b01050a0b0a051c0f0921050405060a1107080f06040317040213020306180906040c0e090304060c0f08030709080f150c0912031303150203070f110f030a 71
    0x70562408040060755030f42d69000129860041000b0540075900000310342440000740011000d0081c0d0140d40002869602d80030050540b070441418203210518804d02583c080c201c2c41a4100100414221000c0c0254400c054000d10140659402c2d54042c020301024802e501c0110f5103141c0d035a1040b0f52070703d043d00c031a03100c1540003901400181a40030302c020100e00303503154141c1980c1c10254003040440740030310300b11540380741c1c04800306500359150105542d481c2480001c4e0300c55414940b0241c1d4a0f80b02c140c07000c40301a142c80d00d00080700c00f40617002f01c0c816442c09001d94185403410380d007920702c1d07084000e00700c3e140c04a8040341000124954081c42c01994641e40d44e8a1681c20704034003601d00300064a804802d81d2010084880541207441c007294000300340c4100f240ca5100040c003040c030030800d2080c45050b0f808045191402c0b8101c01c0915000c40b07008401003940580c81c104088102d11054a550001404824407200d10501521960040c041845c085a43c5642d183c0c5040d411504401d0800c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 689386133 1250 689384883 689384903
    0x310092405060306160e150d06141e090103060f0603021002010e1509070918050d020d03051b03040303051f08070303090503011406010807021606081905040b0c0c0118 73
    0x5440c02c04200d400d80c00700441c114080c0170241240d010300744030b40c00f4224a10035109134424000e001031603c16120f00800c40d42092100c240c030750400180001240000ca8001c2012940640350f03c442c1690046108001801170001642540c40714406000541034100c9120f4a980001005031100807050045900c1c80c1d00004410000c1c1c0f17142401c124050707030748000a507099018021040800304584e4100e40390000c001882c6060f1440071411083c41c42c601034041c3c014241d800c00d1007a000305542c01460410740e401c000781d59441940c80c000c4c02c1100d1282a00c80b00600029001a010f40d00107504610b1301c259a1182c5800c404940f9151100c1d40c0002071550070642d010400c15401405400c0130b800102c000f4850000300030240308004030002c0c01d81e810072036a180490b40c114020b20100120742082062003c00b181c45800203019000c0c10303962042e100b900c0342810400400c0074460603001c1c0f50301c15901109070300c54404c8003185400506056002e95030b29040d01000b80d1035207800c1c030312f428419480d00b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 689387383 1250 689386133 689386141
    0xa08060616240b0307080c060c0106211a010f120f0b0c130e09061b040b0a03020a0e010318110a0b04090f0e030307020d0f05070812091b0310092405 65
    0x5000c3c1c401440d062402907002e51018070030303090041000c500d074003c241d5400342c540740d1400410340500b010303511090500c0d140108400e001d400c0d800c07900012900031300b50b95030808000103001942d11802d04c102468087d924205101d100020310040300301e14000d20707441d20b240d03030551200e19107460140c031504004c05000481c40170f42da081c00c01c0c2500400c00031410701030501d84840d510751107060050290303400b00c12411620f0100000312081c3c074040c080045115442e0750030000098020341c408192000411b90f031081303181c0550302c640588071192a02e10f907418144c00c503642d01c4802000d0200c00b2154860500d007000b00f05100b00402400080c5002400801d5000350314038148101c50807054070100c0c0341c00400400c800700d900001e611010762098544146940d002e42c0b0200c07268090898010644000029502d035001d40101244d4007501004080c0e51380a42e04003c07014003814083c42e01d83d010b421103054040c1510705a4840f1117500d00403011010290002d10b007502012403220606014180e4a074140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 689388489 1106 689387383 689387453
    0x10c030509310b240715020409020d140106090f12060b04020d0b0f0a350a05070f0b030f01050d1506060e0301050901020a08060616 58
    0x942d250449440142c042c0a95441140c810a5850750f01c0c568148115001c000f11440d48101610b840d4003a070307604041d8000300790210140c0c2e40c01c0c000040e1481c1c00c0c0c0014484840c030004005094030050210303481210303068200e8004c00c5280030007132003441a04004ca0090301c60700c0ba40300c0502d44d82850a02c0203031118101c040d81260001c1200303920442a904900003e03041140c0709242ca140032410701c00090040c2c03089240d101000c11104140f024501d5841c22407050301161440c01c8114031034032901c0c2541007581183c099010030010440c25070201e00e10740280012203192440d6040180c10788038050018014241700341182c02e0b50303d04020036410b201c0c000030303079455091060b15510360001c0d00d044c2c201c100141c02542044000b039402c030018401c07501c0c02c5101c0d03142c02c141c0b6102d580510645420010012040d82d1030500c10801044802841002440315850329107600041c44d802 = true := by decide +kernel

theorem cover : BRFrame.Cov 689208633 689388489 := by
  have h0 := BRFrame.cov_init 689208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 689208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 689208633 ≤ n) (h2 : n < 689388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
