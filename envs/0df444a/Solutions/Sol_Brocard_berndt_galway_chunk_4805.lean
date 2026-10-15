-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4805
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:47:19.705847+00:00
-- url     : https://prove2.me/submissions/98ee3d85-a847-4187-a900-a7e6d102d702

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 864028776 ≤ n < 864208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 864030026 1250 864028776 864028811
    0xd08011508040f05011a10090308030a050430090909030c06051018020733020304020f0306130606050f011e230c01050f040f120e04021615 61
    0x8a2929240c40000c0c0d507203e25110004440c9600054400e42c0f821580203003214016184100342001161142c42240c10000304a07040c0010307000080003c0b400b400072416080701a08040e810070312034690303020303d030b00d1000b40562050440055070980c20a02010b130b4540e65006801031014080041c0244002082901d0150842c024510024a86642c0d10000b4444074146000d180190002400103400000c0c155103001c041d4004034800d444105030307101490405c007030501e60380c40e440c038005400300140503010480360003e41000300141c0c0c01044108201308903540c2401660310800c00c04100c3d04095880f030609000702d40c0540c00960055591300c49a4045030303005408166141d201d05480000040e200b02c0880b2200b04601c1036601c12110749080e1104070b15042c001d8003030300c2c410b44001c000c1e41c0c1c2e807100c900c0712056084d01c001d030600030089150350118000c0303041a00040030900300311030303007a502001060403030380090303542800400c00f584108200301c000c01a16100135039820040c0460710151401510 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 864031276 1250 864030026 864030059
    0x31a060f040b100f03061a0c011b080c160b01030b04060606140909090a0503160605101203080601020c0604090c030b061216110105010905250801060c030c05030a03020c0d0801 77
    0x504c41c0e1069800030451094025201030828480e602d050b80e8a4810061300030f4000100a104d65400d0442c1145100c00e81580c041070103070b490351903100e2501c900101c450310707a100400680e4404c1042c080782001c914080e039410700940c8149050301c40d80c5000c0c204001180ca40380c200508005400c018021442c8103002900e100c0b400444500450f0380711807c0403803800c400c01500801c1404046411035548801001c18044940141c901b80a0356603082c03403203901480e980c0034484480c0440000d1402081c0300388019036003c5c0040c011a02840c00410004030b640d003090b84501025500c1e034001070100d603814090704001c2042074410070708001250214a40c003810040105500818802201c032807144101d00d42c0d82e080038400001c00441d43c460743c83c00080c00044403012003881080111448418480d014a600d40c031080d40c840c6403503400c00504641200c45020103408100d9661429000301d0420301c0141108034907501d0043e40d80b00401c0a00742405201a42c110038000380c00c0042244214002900d107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 864032526 1250 864031276 864031309
    0x18160b04050f0a0e010b070302150403300f020414043303080307050a09060e09040b1801021602240403021302360303071119031a060f040b 61
    0x40030b014190100fa00300a095000340000c0b000c032400000d510b15240002e01300c0d24000e9003a5060701041e03000e1f40f02001402d03180100050201d103040351aa5525940031170401c1600070b00922102c8000b01d03441d090300c0000c100340c0d402940c00501084084180c540004800d02e040d601031041c20301c04002c0b8031b0b0017083d800c480d064003848031007001c00a07425044205d0240d80d00c064400d03147c0c10900c800400540140700350802080e0001000b04901c2d02400ca050905a0024080c458581e5159503008003220046c0004400380880803c219845500b070020f418030400d940a4451000f0480c01000781003102c6052100d012042d039a810418401001304031025a030b01902d4401140060030045c600a02c02d60360164405655503541001e000c01d401d4100740d464001441e00c10100d0310382c404040e00c910400d88010480c0722030a03000b40581c01d00d405544a18100694120f041542d80c0d16501c0d00700504001d1100105400740420110b8546500c0403500a10162020081113a00002080c070051500c003405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 864033776 1250 864032526 864032539
    0x241e0e040f0203031e090a060c1e020a12060f0c0302040b0a0309050a06020c030d1a060a0324060206090d1b080706090804090204051806090601200618160b0405 70
    0x800640d00c04200301c9658245d884001c141d02610180c00300007581005040034031446000000140d1240320741500c2c040f240e0004002010313202c005000b00c10822068800300d030444032028000803401c0c501422010000d020701000f05046c10440301180403242d003803590384145407050005001241e14601911201c03021814000ba844403207041c810b2400d40344c800000c00b003034000540c02c4411240400600341c02100c1c6d11084c0000400c3e400403600074001001040c0c0c12010030700007509050b2017a0041106484038542880c4680500c0e10002c081e41103d41014003d80d200c02d0a0251a98040240c0309110300b40e440c0003140c080c1e80400380c0903540c00004028020703100c00b150810078006640d04c407042c1c543d03005952039680c0d0f503030303001d01070103500a4030402d40b09124a540002e44c101d0007045080c0b15050040501c0300c03e41c0c40300c0054a0790b034500031041d1018a01da03001850131000c02c1000358001c28450b110b4030641c141c00e0300c02074985410025041c880954851007040082030b0402a241a0f800c21034a1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 864035026 1250 864033776 864033803
    0x60906031a04030207120804050f010e0f060d06080f071a030702100203090309100207080c0d0807060e0f0109061505122a03010f06030b060a1401050d241e0e04 70
    0xc85c0f5151442c0c21081c0381c0103480001a04001c18040100111002030320240c82ca410000015a01001e05489061304035a080c40400d15a00e4001c0052111440c40e900009696403074610707d510b803807606203500850f544a94814000007102052021039448001c401a18520b0080802034503420002190304e071080d004070216405103414425200c040c036018107488507a03824000020b40e45c0e5924032078010b07907002c5c40d2248503aa0500c0b80c1c18100d11178002800625000c07507580d8800c0103088a0b4803580240c041c40da40c042a1070340038011044481d00900380841c11460700013110010500e168003031440740c861603104e414107032000b0030000030a06e91440300d00c0c080d038041c0000c00b200050b070044441e4135500c0d145c0d055982c021650701c02c1095030700600b51200c0030f030340d090180003490050740a0010704020a1048148941c4502c00a10341e5803131010340800c120105460303944090b9540c0c5441c07107501c54031400030b100801d400c0780181121400d00520302c0305589000003a00c40761001070070103049441240381 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 864036276 1250 864035026 864035033
    0xc051c02091503160e07020109170d0b0a080c04180510050403111f0606020a05150a090c06050a0e0f30070b1b1b010e0307050402031801060906031a04 66
    0x3402c40040060156078480d0742211300f00d00008128003480060020000206680502c14440c00c005a640302038403203100e15542c0b0988031a03403c03020500d14900c0d1030b05000741c202e444228006004050f0318000b01000710044041000b603601a000d401b03011540f44803507a0101e0350000e105102d030b450700d0b40c0000d031035104c500302143c89480c0c0700b901511511818034041c003500090240b201100180110400403d1388071801240ca814005201a08641c802c001c1042e05030f42039190190400d501c1500060040d425648144404106521100c01f146000c114205c0e4944c100a0007040c40500700c0d032a0302c0c40400d1900048981071180200515500c000c0c112500c22000703940c62891018410f01145ca0a0b5603512003501d007503010154003c080c080f21200c82c001903100181501200300003421040d48808404011500341800182140c3d140c4580200001c05480c1c6100540c02202000b0800d00d0304624410200d082d035090b0390042252602d0030f5410004130b002e040d0028034480c1d5490009007542c9542c00d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 864037526 1250 864036276 864036301
    0x9070c150906051825030b0c130f030302060609010810092d14030a170c0d05010602061f0806010501030b030709111207110c15070f0b040c051c0209 65
    0x60000384460f103000103004408207801100c048031000f82c0b0445000c038407113145d9110120443c048407103011229020038400942283d949562040c828020642006408280241c3d040031641c85900c1c11182d036001480ac0c1030b41401841d512071025604540c0b55490321148540c0c03000001020311034185d9918005040042c95030301078107032845034401300d0b0740844110030710070210700e03012005c503425200c050002c4125140031094a07403022440e240c000503900400890315020200910b40c003851402040f050b200c4510a00c2a140640895401130619180481c0044c2244182a003c0c0041c009d003040108002c00d000500c40e41911001e1a0102d44107500501281c03401406410588400d4240010140f0100f1560f01408030243c1d402c0d580d0100d601d84440948681c00452022007040e00204110401303030406c8400b5010700c0d403920004601d0710300307152258051840108001c40c0c01180d40c00a002c01d000c07403030b1400380240c981101e005030414554424010030004410000b0b02030f8070010b00003842160303d40c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 864038776 1250 864037526 864037541
    0xc060d090615090e0f0606010f090302120601081e030d020904110d0f0b0a0501020a030c0c0b0c060a110307050304030311070f0305030a0c021f020c121c050609070c15 73
    0x103400e0080103030005865688000500a03d01030b1494803c0c05601000000f407540786111101000e045d413911101d00444003507103074120314000e2040304003000005841d05c0c4505c00c0000307400c2c3c000e08042d5041048060403c8089a00c4048200c5003041503040d06c240441241c15445048400595400d13903040400c002d0b050340386050b0b0031002c010450303003180c155035003040b0a14440e0032004c100010f5400204640852540102401030740b01f00d1118001900407440010258080c4640f880856560101e000c0181c2c0300107107000707031030f0820030502c0703807040e5940111a01000a50703120360562501c810010294000140068109030300c420781015245c031400101c45030150000325104401c501420090120342c000e50309000d14518152841021b03d2000c9407103042d1440f04030140c148c0d9240495050042c0d00540c9459000d0b0050251031040034400030021701d44088611549151040e44041f040211000100001e00035a1079004100f09554031210030001681e0141201c9031008000d4151030040001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 864040026 1250 864038776 864038783
    0x906170a0e0708071a1908061201021306080903280306053001061a13170705180c0d0c0302070c061e050c0312130503040f03061b020c060d09 62
    0x780c02c03000c0b411000114004055603c10300040010070f403001d01c00481485801070502d5025040d88030302042511540c02c180c5c00420007401860030074102c811082c22640006159440380b901d4950400c030702504400501d41c08403426000d14101290111000300145058503c0042a4915044551554003035806540030300707000b825101c0f41140010b81e400d50556000c000c49505070480091840c1410140251000e41d4240c1400c6403003c12615180005500a8003082c010440e6101c800b1030300f500d021141e00c29110b090001441800c1c44c001c00c1c40204130503062031624850b020010030050155140481d6403088807a00005110f0703450344000c500a020702000240820b03490780001038580d03030104009940044040c0c2d12090203004002c15602c0384280342e4031030060740090001000a03c104c00030a0b030b200d180c0b4200901070322001d0b030302c2d2750441d4041d40100f2603a080c80c42c070030b10900141303102d1100e0f580e1035890108000728040c0360281d035600741c40f5950f61040d60002003050084615070020b40d5100d50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 864041276 1250 864040026 864040033
    0x30513030c05070801090303050a060503160902090f0409111c0c060c03030f0e0604050123010b0c150a0c08060d03051c06170a0210020312150604120b090606010906170a0e 75
    0x60300c7c50018007405098503c0200c103414540042524138000c0f81c90403000c1138170b903543c03109107141c0b003071000c040e4101d201102d50102c08180703181039544950181d851183c0c41903401c0c6440d070340c10200f0403074102103601d86001c0a0420b8800c036400030b074580c41305030305440c00f40c01c000e0558552890b04801400c10701d4481000c03141000c141000441e40000c41d24050f81c468002071006015000c04000301d0103000306030303a400181600c01004440401e9000717000da0000c1c1001c2d1000384241c1e8000a00d1401c080da802a00c06581c0c442200203e9441404c40303801c074004a504c94405407041c0c500428a01503400c0308440c000c01710218001c5202103600c10300007064a114422030743c18100c510300303881c0c5c100132400768012005080d440b0b803c1c0c0d10100882d4499450441e50401a44801104078007041100d40032503000b8a0802011030303204107102d54061000c0c400c9580e5480c03407402e45002402e051015000d01d040c80b182c0030060020316004240d010303d1220303000c030241c0c0d07a036034000a0344045c150640460740c0501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 864042526 1250 864041276 864041291
    0x6150c0109210f0f1d0a03050706051b0c0d150902030f0f070f0e0c0f040f0308071101231e07030f0f05030402010219061415030d030513030c05070801 66
    0x7100d60034180b441410364840500942c1e10f18019954401e4004094000400b49143c0036902c0c002d0050340001c20300c0c040c10860509407240d072a189868240c0d001240416800700701840008000300401002c25616000303000008007034800709514607201c6100508819102103421408110b41d40b10503034a070740060444003c01c0000c0c22140c0c0360012030704640e2080c001c80c54003182c9403890190100489210750400d0b00690f9854403801c1c03042e0032209500141c0a410800001d141c20103003a9030000d5401900c0c0690355441d079203001749042d00c110b40514140448010341004403c0340502da0032201603003010703071940d824040c61200790842280180c51451140401d0740e100380760b80070341007a8942107280c651007406c900c20f41d03007940d450200711802801a480040c0811000c145061640006131240d9030116000890081d0340c1e007101011900200505c002009040d040c0c641000b10801c03400f1981030800c0b56017025260320300703c0b00d012000501030110880d03121040003010011540184441c000801c0843e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 864043776 1250 864042526 864042563
    0x70210210527060402060f0f0d020430080c07180b04060f030b0610090902070f05160b040b0702011403150a050906060a0305190c080108120306150c0109 67
    0x41c101901c1c18000e503540a41401c05010120144910750003103a0001c1c1001d41e196401c1240940c0090024100128240802c2c0104001003016208840002e040544c5070b5050000e6854401e8000c00c1031000e410380800070302c0145035664500c00003188c104840c20b5952440c81c0045240100070b40c0010701d0394030a0b042c03800000320583c1c40342480190480e0280190390707451950384000c1665000103000754100b4404118646840445503194060a00b030950502d0b81c0c0380100b004070b0f00058810b0383d901028a00140c1041810300201e0244854400d00d20b10080c146a14904c5600540c05140110040014084103580c0203040c00c211621041701100d559280c8500000e45c2c1c2c4d1000d0036a2030181500c60380c01b1405162480115104d0f00d00a042c0fa81401039403941100a44405001410148554032056240c43d50305d00400050750455200d100042d49803d0382d0902d0241903564030f5000e9041401404240e0b95105031582d048107032074085c6502c0c2c41c0080b01d02401411040001020211071004942d0107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 864045026 1250 864043776 864043781
    0x4020c12030a3602010e040908120903040f03080702060d1e15140103050a0605120102071502130312120f0501051804031b050705091005100201020901020307021021 72
    0x103003082d80810300034500c44102c120400600c0d820104201c141060003000300340c42043ea0303a00c480340145403142074a50704401180c111001c2c000c00352104040015091400110000602c2c0c106049800642c9018a8000360324100525804020030100002503958103545d03680c03003a51240c05640c85d003000f801d08011400300e02e0344c5035824031030b0001c0d08081c2032200f280031031200c0d80c003100d4400c00da403844406490011030090000514108a0300c0d90340c1e0000c9020f48899110081c035944403000146c0c2c890b40c0741442c80d1104800401c216209004004500907414049000c20840740d110500030700200d41e61a0070307030f084010900340030752440c500900302d500c044c2c003a0440b5048500580360b01d4446400003181d83c540c1402100c000e40450380040400c0c51011401c030403464850700400a440c00b042e2240b0000341403010556041508407101c2c04240700a14010b42e030a01041e40500085180065140020b03480f401003107030103072003041000c038452120380c091100c0c100102c0e8180d25a0501500c07000a8a00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 864046276 1250 864045026 864045031
    0x509071701050f04021c1a0604060e0c0703030c09090509150f070e09192a020f0a031b020310060825031403070b04030806150304120e04020c1203 64
    0x1080c0600c00500100940306218450140c103610111003003941e0303503809105008100303040301d90030500720b0b06500300451802c0466025610f100d10b0340d107565041c91400c00c0152101074001a4180c4206001e0106050854085a41403076160038046a000c000100544943e002c030b50040b180c160501c02006429080803d81d00300c0300701e903105070720095200c0c20f400c100450340460340c0b000400c000c1300c0611824075140e0811503001c1c04541209074818071040481c01500d13909100580021603190008684070341c50000f43c060316030b551008009031002d00500640d200c103c030703078090280018240c8244c42c1d03141070005025100e0f00a01200c0c56200f034620981c0081400340300305d40290040780c1c0e07050904400b640302003075010800741a501c040c3e420364458022400380c00344503a00b54402000390200240d01140c80c0c0344540e0094882c443c0925005040c40041441b0390ba10f00f003414401c00400c0700141034484a000259400e03d046494140140d0100d4002e1251a07440700041c4202a80c044603500c7c2d4070011132 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 864047526 1250 864046276 864046289
    0x7050703121a01180803040f0503070504050712020a0e2d01140a080901020409060e0f010803160b18031902160b190e0d12020f061510030f050907 64
    0x41c5000501107882040390440b604116000c2c0c0074540740d07034441d0310030010340c0a03600d09680003c050320741e104103080c83d40e4090780c004012402841c82c00c12041c5401d110313040003064207a505200d5407034507c1c80240b0b00d4001002d421403942c1d0110b1081d2540703115210380d01e030500000e0443d03603955420000e000c242c40322103691243d00c0500307000c0840595204003081c11001c0181800c00c0e0404055060542e000c00006000384199036080c440060742d038030640107a80040c20300c07081d801040d050a80c101c60a040341600030100c260b00c10800040308240c8149104110380d0000d801d0039a544607202220780d4544080142d00345440081742c1840451508519400741040c2d9808858903031229481d61b180b2100c0e42c0c459074000200603c503440c242c2400780d000428668551900000c5003818100140c0005910401641c40a1660b2040050b0b581c04029103040c0b0704000000b4289407030a900807800425510008500580c101d1405411060094104000d0b410840c1d07000c0c4038526191300030940d2042c443c420300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 864048776 1250 864047526 864047537
    0x6180503030d1b03140c0a030e06040c08060c04060e040e100504050d0e0913030e03030f0f031509060f01030f020f07050d0f0801080c150904180b0c130519050907050703 74
    0xc3c0c180c54081c0c881d0b152000c2a41603a070a49036213914400301c042d00711b40c0040c0e013495242c5480100c447d005003c114805d0344159020300049040003a42c52400e04018089904600e00b007000340b0480d030301f0a0171141c40b103104403800321742507042c0410b09060160403803040185a040c00140400c104c1d0200b20100c00074096641c641c82909a40c0400005920540f03106a50900d42409203002c40e01c60080450118000f808691904140040c119002e9114142e8600802070201c1401001041c000d540000c414003203031500030600700034000405650400d84598107245d540d00c040024070240d03805995400185501c1c090300c83d03205013460ba8585403d12507030000641b0362602c0d400c0d04c500414210381030b50790003402040c02880302000c4c003425007155400c0785c400000610210040356202d018915900425591040d411100c0b441c040301121005409100e000600f803000f2900303080b2800b40c1e00d0485a04946a03200c80c107800321051a1041e8a03044540c00c420818108480a50000c000b4128544655103a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 864050026 1250 864048776 864048821
    0x120f050105030c10050919080604030807021203220203010b0409200405040c0911040b0d020a030605010e0612040809180429130203120307030911030105060a06180503030d 75
    0x70000c440c010710440b0408103409004105c002d003040700303d40c2c24612520447e02d180e07030380b5183c100e80f6003001194210f0001e030004040010517035060083e00e240201c40c2c800b06045d0b040030034444d01c0030702c4510303140142604030071101000c1d5a030940102c2c14000300a8020480703511141850550031041d0760301c030500049007840740307985403c240c818544680c1d000000d07144071500703128140006d00310b00100500003030001c1c070020540a840100902c10342e40c00010050303403080810809002d59600340d201e281403101611594001d52200c030304450440e0841d8900342001e580c2c5240c40e141d2806100101c82d04440b0b03003000c0c6c1d51300b5094410f1a078080d501a88009419010300c001c801c50445680415951004400c3c000c1101c0c00c6800d80c3c040c4945100070141d844c041f1801c81044826081103c00500203901c4503000c0052020540c28601d10500980c002d05c03040c581003001c210100001c0c41f41508010440400c0c21050400140e2a40a480000c05680c0d0b2a42c080341b900c0c0c0a4100d2176a10195886254038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 864051276 1250 864050026 864050029
    0x6090605041b050f181f081f060516060e0a0b0a0b1003050c0c0f0105060f04060f06081f031b0e060a030b15210715020a0210120f050105030c 62
    0x26401081201e541d107625007011104c1107042030f0410150701801284008400466548078009001c68001504038844001894400104820000f4194a10700d00500305040f81804510340c01e0000d44a17a030400542d507070b0907401905146c1d840090058240380c5020b101a1002801080743c80905018400280e05a19602841400c941107001c3c002e6002c151015410340302c5000b80c000030f502211060080307003001007030403a160400a40322000e0031540d546104102c0c2d18644000300091350715040d501004038900f00300c64500c40d11001d000300000c1c0844400041e000c03000180c50600c5039034404600007200ca50364503108045411409410020b1a03007048081100410705202c0d84c41404020102c400b09032440e2103a00711504040c044120040700308043c1c807200d40304d051a000c00f00c408510103802d845141581c890403e25036403c03049826902d0000256800c3c1c1c0090b89100c44d42d011a121031032804001401d0b0741d459000c81950000c0c9042250000400f850381d40000d04907203043d011750341308030906e10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 864052526 1250 864051276 864051311
    0x207080f030403060c0212220e0a0b1c0f020f0607020607080319020a05070201030506040e1b09130528120f031113170712080c070806150d0c090609060504 68
    0x4120703c0030300800340322000f010100c9031308d203842400d06a1121015607407034107224040e030441250728030081d5403036100003600b50502d40d000d403100303080c1401250280e1203d680d840314074904400c4040e07c00c0b0020000005250348200480d42202c1e8014203459a410081c50300c031045400c111002176071188060360f8090190220f000722800c00455a68031031403c662070f4010b45c01003d0160106c0d40155032080e007480b0301d17942089507804100b55001c142d00030b0b0324000100403070b03a4002420f035920040c468040400158001035a03030306009101c03640d40c4c0c18440e81e1801510410514a020303000314003074001d403507060f900150007d422103229513042c40802e1100c01082a28402c008001369000060141044840c401c1c412034600d0003610070564041c2c5580c3d90900349500c9540a0645043c01d00041c0c0c140300c2001000158000c0011902070496881c00e1031b560210b6409060400c2d0040f4041806a01080b40b01c08007000034001992003004050b481c1c40c8144020300584c000c0e1030045150042d1000b142c00d010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 864053776 1250 864052526 864052543
    0x4030c170f0f0a0927061d06240a08150108220f0615050a0e0f13050c1f020f010b0907180e0a140f0609070f0207080f030403060c02 58
    0x1240107524040a100040c04190f014181ca50200014010041030290b89140740c08401040904601d051581e0034420100b121510f500c035501d210048840403c9045802040303690100e000c42e075a602210078106030241e16402c81c180503094440000d10144010740001c4014000c00e000c01036010003c5a0380015110303041c0075075020940940803000d10401007450700c5000c0c0080d1007048540701c242c0541d6103610544041e0030b28030740b20a015400c1400241003001010000704400c4515410707900308100d0701900c2d5580500042842e26010180d03406224041002c80e501c42c202400825505100c090032000130505041c6007001405403060b5a1b91080c1e050003415028500100b030300d5000d48418038180c400454030080710011003045840020509204502c1d90f00c14042c5aa0119000031411034079100340034010045c412504610081c4512503c074030f140260312414030705200c4002d2102250903850400c144d4400d030a03a10401c3d041701c002c0d404c048054030460f031003660244403460784200700360303164030b0074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 864055026 1250 864053776 864053797
    0x61e0c0e0f0102070e04080c06060d1109280603060e0106050f0f04110d09051c020309040e0708122d071209051032070b0901110304030c17 61
    0x51049040c0c0c41c9880d901209110320140119640036582e00a52821194119420f80302c0d44000718501562120500429600030b0303046a0010041403a035580004080425000f41d0051056200142c01030b0300d149440207030314254250203c41914001030100c050038003800204c0c1c003181020000c2181d01414010981610001880c18410210b00d2081c801c2981010b03403070380c0e40300d03458607200f0300441c2a0000070060742c91580030100b892205030612900c0c02190340110301507001c900420a07206540030040e10700c0c040303044a02094141540c220145041340c6a0080001070051003144203042c800b030002440e1030580c02d40f4440c6590040c1442118440042002401a100030001c00c4000307204013145140c2c1d40d4240c2848052562158007080340d403082c3d42c02c04004580c445803010a20b00307030f41c0c0311804071741148008600c490b00000718290260181800082c0030781e403800046000c0c20300a40103020341000181701e054403031070f00e402c2c020f008910f141000c0e10080f000084039001c2c07081c0038044540c544074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 864056276 1250 864055026 864055037
    0x140313140f0402070611280512010b0306030c0306072c090112151509050a06050303090111030405030d05250b06010e03150c1308011b0507030c0807061e0c 68
    0x40035000c2c00007a622a100490700b06a98246920310b201c20303100a00304c05c06c60303c080044011103900c4a402528160301d05402404010700c4001c10035109404080d0540b9110502d440d1607031110b10100b0304d0100515001c503810b0103602d080122180d800581035040321a001c02c80c501000044941c0f103050383d0701c0107250760408912401449405071405840514910566040b101004524104011280010109802840a218108000c0200340101030f0031030010941000900c1c07130030700013960781d10a004885d1b041c02004c507004401c03d80c060096500400000d41950403d0b690b21400411983c00780c00f030102c10019194018070358858040c10307410100c0d40803501051703588400005403050b241c402050380d8103224003582100824149042d85005244a11040d9141c132801ca9080380e10301d4194209981d541c1c58002c035414007000e07258511001490608100b561000b42d401d084943d9070032518082c00c0344900007803031002c00c80f1643c0841d101c0b0300741c2c68030300c4007072910703400000300350380310300d00b16100089 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 864057526 1250 864056276 864056299
    0x20d0f05130b03330907050a020616090e090c0114030910021e071101080601020d0503061306050d12030501060302040e041506091805071e17030714031314 68
    0x4040303400650308403018a10b080141804c2042da81c6030100d40d5900c079030306281812001ca0450400f41c000981013041810040e080c00604000207680e204014030b8000f0811400704000442801003400e0005411103030140380d4146000d035200e40e0791700c41e106111400650951300d41002413144000350780c000c1003180701400030701401c41c00240103904808440845854244003d14412190000418816129079502081001740304000b40c00c101c40240785505541000440c101d04176400717400c132507116408440200745d0100020501005003c59040303580c010346441402000c4c001c1e00d0781c4040906186030303030030702907680c8811007101070380a24801c0001014480001c2000107100300b0940aa0540c080d00c00104540d48440810644070340a050f464002d45c100010400c0c08070501020014165002d1519000d440c1e0740c45500c0f421400f071080700c0744010321061303020318031000b03204030340000d50089080ca801c102507014051302e80d44442da0100d40010741b2403002448544005c21014000c0000302103a0602 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 864058776 1250 864057526 864057539
    0x3040308180103020904090f03030f0515040905030c010603050a1407051e0f130e120909041b080312090d090807090207020402071a060901140307090b030a05010606020d0f0513 77
    0x30140501160606400f8042500710361114070518402c680030301920007523241e182c2406012a4402c640c4011000e040c4800c001d160410b87d0311004d00440241e41c0010782a042c0d09150381980600031a035400c950070282c00005000f40000c03d0a141802601c000c19413000740c40c4115a1865a4411241c006110000160003a28440d07840c503210384001d4816001800010000b41c680c000c001d4641100598404021200000c2000068a000100c3e6141d41c030f40303404000002c00c074100003003000b05000752150a16290f401a410098001d0005604880c0c403403800d185050480700c011100f8800b548640790400c07200c00c2c411001d443c102c91491010b411900d04003519400a5404550280e820130303000c02031400021900b00f0301c1c2803c0e0346510400700f0581488030400c0b1400e401a40220704581038950940b026a8011898400b01c4048000c00280c283c4400701085c1040c90100010b00154a01400024015000301c0c1e020303100c810303607139420160310080c0d0800e542501586004214240c036660060124 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 864060026 1250 864058776 864058807
    0x20717070f020d14330108060a09021305340915090e0109090c0506071703062808210706020306011e0306030317040b042409140c0303040308 62
    0x4580142c0d8040030351070301c0c2070780503152120a4003407440030b0b070041300c04005107811402c849503d012582d5007007005c1c1d450004816903a6030007400038290300303541d4514041150755203400c050b007203042c440d8280928078040303212201c0550f80751251152130752154098200c010000c0d4203140100b5490b00d486d066103050803998500c1d610200a00e000348502c2c0007020a09a01107020ba900a0200c3d00c80800c011200e40703440f080c43c50065100302c1c00f80c0300c14406180001c00342c5200745070809203841ea403070301c980c1c0e02e00c00600003a0300c042c0c0f2004c604200350681c002050190000c0000e89034080d00300c07924400131001c60005107141c60000c812946050003e900002c42a400035500250145089100d28002c449000400040000f810f00401e5640e0f808000301074125003449003040341300c42c5005041c03074207403100907800710000c10042940c0b407801a09002152081c015036a1070f91040810000391840d498108000b03070340d5a144102c54442c0880c94602460000200c800340c9510440301030400f06004096000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 864061276 1250 864060026 864060049
    0x507021e0603131b2601020406050a0c15051503010e06070512040f0b1017070605040e0406110412110402090f0d0f02041a010f0906080106051e0a0201020717070f02 72
    0x9038000101c404c1c0c0204819121110041e01d076164507a880c0e08142138078010010709070b0046841c0742e40184000c00000b500b01040da1840380e040d05089548442d1450803d15071041420b5071102d09140206009421020702101c4400d040180d00812611113130259503036440c1c004907130580001e0070820100b1380c0342c5400b40c1e806070001d00c100ca01110165181c0c0d9001450b540c1156981c100d0059030004000f00c0021810a695100d6041e001d0440c80d401c043c8021700601c224002c034010394801102050400c80340c0c1d4895403880000244040c2ca5030340314071520240031001a01030356840604144000f482c07509208640404200604003000d511501091010020717203c2000d9485440c0240c040000d6240c6008890040b000070b006801c0c00c2c1d8000f4005050030384103448050401c2241c44051080c140c0100784181541c9150070310a44596202002c4601780319690381548030400b01280c03404000d03405401500b1803070b128561038600c001444015184901030f002c00a051150201604809800d08010008 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 864062526 1250 864061276 864061283
    0x1050609120d121a0a05090714130305010b0307031e170304030302210103020904030822031d0102150609040c120609120c030c150f0e060106020d1b0b070c080703020d080a06031109130f030507021e060313 89
    0x13c1d25140d0960310711545da001100c05402103500003611140c0680d03500c20040030075000c000c1602003941190003003800508010001401d014034200481c819100c4a40c20340d1000d0102102002c8081c09460018601002181043c040f13040c100c210001d1580003050049506502010400d883e0b0345420170021811000350040c0c550341803401022a0b0480141e00b41700030b0600910001c21010000d251804981c4003403ea0642046211f8600300300080d440601500e050f900302c4142075005520440000041c000c80c084e081c0300501d005985502040c0205480b41202d03402e40039501c801060620648030a483e01030048d0340e40f54124a55000903416020b19a00401c040c80d1201c0d1504099803084400d600003039042e03026070301105030b05200035803180d04154001426142031010605d10b036105544480c080c4c0e01c01d489900c100c80056040041c0740f1340548000d030000469652241c03d0709018000d40d1280b0350030381c022503d040c002c0700c0a80080f00001c400104c0584641e1031590f40f103d070400000c0403c074044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 864063776 1250 864062526 864062543
    0x90d0f030e0a061805060306010f110106050d0f150e0d030c091a0d06151b110a060f020d02031201050609120d121a0a05090714130305010b0307031e 65
    0x20740d860340c4008201400c59034403800e1080000b00c5601850b500158460381c4600420400c202c0107036807180d41c1d8116168603003000480c4031600ca03402c0e0f025000c5c5401454220700c0200c1c3c44001c1c00910103c40d0105402040700e818058141068001510442044602694004064101c0c07817440f99102000041d41454a070a190b516000c154004101c500d011707400410001c0394900d05041c0d280b003007200810b094000c04a0352444600702810301682c0340025090300d48108001c038180001c148600c8507061009110750401602c48402601a8070140d020000621610752a032901d140000100c40c00414a11491039440e883c20b4200102c0e07078004420301e60072a0600800e080700450070007800001030443d071180b030703541128000064100c0780ba03014051052410f254454015495101c00001660426a070740c00c116034807548255440e15062607200315002d000203050007150b89140c00e2005591007440280440ca00860800d07a60f982c02c5d020241c40c1e003c40d0b458191000e100b48402503085442081d58 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 864065026 1250 864063776 864063797
    0x30c0312120207030c0b0a09111e190602150420012d0210022d270a0602031c0f0609091a0f150405060f120c0411090d0f03 54
    0x1450607a000b40f40110040344003001c080e0100012404411383c41209036a00300400c400700d8031951020710301900800d0183c1c003000b4134100b402000c4600a050b00c1d9028211003420801d07904050740b000418480c8000500030b001a2481c800e0307225000c2405660084900b0300d00140390380811444201c40404241441800703803242d130100050085003541c083c101c20752002c0300d5160460103401c1c8004000c0c07100d00c0a1040001c008006207110400540b1152103c0700c051000f48581e01d0005403007904060f9140f40400c281085440700501c0900500010a42d003030105565140c0090780d4130b005080c030011160303000c911114001c4030310750b001170003100c50311401040b52582c1d402c14070211000f0520584810140c42c44c03507100d5102c0e40003541e0304001c2c1411301002900c0c0500848049a1109040c40e2040b912240404c0581d80c1d5080c3d0300c0003408004086501c2c4000e40c42080b1360b1010100405800f40c1c1c182442613030900e15500542c1c803070900c050807000c400e0150b580d4036034200750148400c074180020501d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 864066276 1250 864065026 864065057
    0x50a060203220b0403030b010e01090e060411070506010501020111090616020319050304051f050409020921030903010b0f010e010e190605070507050409030f230c1e07030c0312 77
    0x110702c11490144215107168101401c00809a900f003455180c14030041c5084954a80d07031004000c000c031100004590703856251000000d0181803403010001d0002000b146110034040e001c01c08a0403180d00360000c00c088150b0100d00301d8640902e1080c10343c0300d001403104d625928420301c40c0d0110039200506403100304100c2d10690818000c050340070340d8142d2000c00c0500113420541c1c0e42240c0140980006140c0068521004009110300e02a07074081e150041084003603910348004002c80c0d060b0340346545941c44e540c01001d036540d0b002450788074481e42c20121000468100000d52941c0d21006030740d1080c0c40d0078441d00545900004814a40c1c00105084581034071050040b1800f01038080c0b9600c09540e10523b04010b444c0c036105401c200d2140f450040801d00180c0c016807420360000d00ba00b00345038140480c03400c8068a1104810428071100f001485051000b400300d000030b000580c0050a48440a50038030701990340e030700b6000041990200210900108602d40b0a407840c8800d80e2401c0300080101c1074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 864067526 1250 864066276 864066331
    0x140a120609052a040501050a1203050d060302180403020105250e06070813080f032502180718090b03120906300c0306030709020c0708060c0415080103050a060203 71
    0xa194050308800c40c0f50740c55524240c000c0d20700410084403500390789400c080c200d000c0c0c4408039100600b840707000201640c90340750580014008617001000c01c1000b000807043d904140c3c3d030844046006520340700004001c80c0648040b0303c012483e0b80f00c0c0c000c0282000c50296070240c1c12806a90f40a9400c2c0510400034901000a06c141d1802e0b0406002542c9420b40c1c162512864502600080d0002e214200c031040203c1840c03040ea800c42505900d1002160010030003c1154803041d45080c0d401d1401c001c240c51308205210080030426501c2503a40382d81d0300c5000119403c0e19402903058010101200074000c410010f460352420007000e0030314050b5802d05d6000403040c1d003091510b401625140050a0100c082c0700c081d400503054050310310b58600000000d440760094014110304550104001800103001c1100c900a030007600c0072201d940c10100b00e6020710390060300c5041103440070070311100802d621a589480c102ca501c000100102ca09a554050184d0402480f081012158620740340400a10303a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 864068776 1250 864067526 864067573
    0x706050a0603050f06070503220609061b03090506010504051e1602010c05030f18240402100e0105070b220f021002071401080a02090a030c140a12060905 67
    0x1000001d5003441c501d016424800085079181558004d4010000b84a80103001c4951120f0032002e02d010032860401d500700c0300d480c1715001411a519004a40040114a03403000318040d10041204030301000440045041d6020003900130300f607410200041003039081507041540c11140030082c03e19504070413810600421400c5a4084640c143d86512040c150380a00ca02501d010030f510300303a8518602030f0741ca4040d4140c098080d20002040001c01c00101000780080084405814500d118407040b84418610b41d150942d800da1007001c4a00342070740c1c0c050140940d00b0302d120060310707001c2c2402402d840c2d030550a04014510080e00007401500b007a06a00801d061491a1040c0403516404906006102a920060180600795880200140310500a00e010010350700e00c24642018a584c40040a2019000b116045500200c0d500b80101c1080401c2d03103d4030030703980c4820445030412140020401009424450952403046100444020541c075420590905000b01c00310b5170003400300e00401e070002480 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 864070026 1250 864068776 864068791
    0x20a03211404170301031e0317011203112b030f020d05150d030905040f02280f031b030216051f0b061c0e1c03360303020f070605 57
    0x10710100820050100c1c11040440700c2102a1421981559a03048990840c0007612016100034685141003600c100090051a0321244014a195a40e10210390030000c0b9010124040b0b80f0151040c500d246001441825000700e41c00824102403012410103000c83e100c141c1c200805880d078102c040765003164002070221044401c000165850b104800e001c08a4160f48141c0c490000500304c10003082e4005010b5058440440380040d041c1c212031416002441080c0c2c05200b030400c11044815190340c000744030b40701106030f910350030f0522841c280224111621084101c41200c0c0000d05840100c1c0701e6400740038401e4880c10703032006a05080c0c0b0740c0d1786014417044000000c00c504000011050206014111403000240c031158100310048060601d40d4803600d984040e0720340d031011840307108d000c100f0007140d9903904003103510414408624000c001e022001d80503880f00520702a6242c01c4c161028071031041d0909022454012049590700300c000c3d500544568520039030500130324012402ca031084901071100b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 864071276 1250 864070026 864070061
    0x19020f03070e0d020d021e0a03050105010914041e0303090614250e0f04020403080a1115010e0403030f020903300405150903031603030b010e060a020a0321 68
    0x40070320005080741c071010748a902a0501d1610140140c442c0c1500d610460790450395051070303102168a00c1000705002c1e444a50005035684000b050180c190b022a0680c0c1441c3c006000090f6a48440f10044005580080038451035841074042c0700380074011551114070914001c81d1018150f1503090541e5403191304030341410148814020702060086003640d0b501c2820608441e1071300040c0303000c1c068130362900603a400342050400141c40340d9034990448000d03581c007002c07541e00e440001c4401042041c50529010303032031007600c0c0010008072a05c102103040340c001642c600c4150f622580c08501804000d10141c1280c0d8013400140035950342844407500b001d461203c070400d54240d403460206108181a070003100004d04102c02d00042e110300d40340c0a142c4081c00350a9590300d03540c10110f460344c030800c601c22103401342c02c81c189410194150015070100d0003d03640c410001100c00100701180c0310b01c91200c00560f104a0a5100013030150035010007030b026181501192103040d2020700143c401101641e0001f02 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 864072526 1250 864071276 864071281
    0x6041409011d070f0605030c190f080a1b0c0203010e01181a060604170a050303190e1225120f1119060911150901020d08060f01030519020f03 62
    0x140b0320400d284484500505000d841d21014000c0e620040c02094200200000010b0300c28a403030040f1515454800b140355010400920010400018043c0c07100000300d0103030100c2c07411200ca000d003d90300d5840703082e2a095402d0049054031400b04201c0101d805540320820517040440c280314910901c01a040c9100d419400f61500180d00c2c4040003200494071691014070035a03803200415101507440981204d1800240d40360a41e02e0301001e4600280a4400081080541c4e402d0010081040017928402e01c050104000c1c1c558071803042c03412080c1002005e0214140d01c00c91095264026072800d842d21080e49540d0700c817066200354000c5c20301c0c007041311066450181c44d40110000b6501c0051070103000c8580e12401e044818104110021781640d894220000901c00301c0d01020a005500509500011540f80a1384410340c0000c01d445000d8021010030031001c03130048003211f2180c5001044816403820000056006260180c0701801e6a4410302030140088424402045100340c0840c1503512031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 864073776 1250 864072526 864072551
    0xb0106020c040b0d11060a02030423010905100225080109061416021207111c0308010803181302040b0a02010203040215210c0d06060305040210090803070b0604140901 73
    0x183da040d803016021303c04000390640401c4c082809205d42c1c00007101c1e0b1640d074000e100344c22440c5015075045050305504c201d0b0150b185407803105d40008000c40a0302d0b6582e03900d42d15000c10400c540e040e880100543c10895102250441c4295550545003170003060f02c3d034041e1100701207421507149440850300070303035244c170121031500d00e202c802540201a603201c0f4504885924000351504600d50004084960104c0c807181003100080702d00c500140043d01a018040d04135204a109844400064001c50007140011446030008001c03623074181c04c00f20400c110100503030140134030808403103814040c040d07081c880414203503540802011021466800580c4a042c07500401170a800003111007031030300108108550034110760781c241209201940034036140699580800c043e10b07206903d034945025141c0607000c00d8441d00f40d40100c2c025030013913828144520b00c0c01404e4400c2c1c001401382c00c0703c0e6072080c07011400203215a0000c03503003c0009003010480041c1722005070b682c0c00e000e1781c102c40d699440301c08000b0b18 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 864075026 1250 864073776 864073781
    0x30504150504061e091e03020d080705040e0c0306040e030c0307150e03040315050f1504020c0703151d0601050315100902030a1b03111b0c090c0c101518090b0106020c04 74
    0x7402c0d0540031b40303030b9005201d80d0080c0da07686c4410f43c41801e1040f1040001d28290145090710014046108518618038121001840c1640112802803045140c52a1030085201c0081610310301100c50005524065464443c078851b07008040514400b44d031201f482180809050001d00700031841642c24071400040880a44203407200104a41140d115100030046000078a0409901000302a0360041e92101100500c40c18600c96400181c0b030b0303a40801001040d90025484100304000c8221100c0c4680c00d00c05140d038035100e003803040c140c1c5540700d40d49201c01062707803031490303500189406a10081c4c550340703040700c0c0141d030000c454140b0119900c40d0849004c0224000500c1ca240b21403604003e200d0701c60040d2086400f0308400e00318603c0e80e0441034043c0f0700301081103044404000b0b10000e124501058800505d50005100040902074816200b8600c1c1d114001c10480c0c0401c2201c01c0552814080d50b03110690030102182656902ca40407000825448041e1501a02d07095000e0036600d004401170005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 864076276 1250 864075026 864075053
    0x2503020f061302010309261309090b0a0e10050103111e130c050706090605100506040e0403140405130501050a060c05060408070f0c080c0102060601030504150504061e09 74
    0x80c0c1d802480c02c00c0314240054600ba8000c07542400d0001e881009418500d07070f00588404200c02000340828440c42038540031000d4440014980980035995403298001410b1303451900d0010000d14070480413840c3c030b2002d6000842c9842458089074003025046005509542085e070040e1144804201d03480000e0803c2441803204843c40d0101048494100740445c50303030181141c030110300c640c3d0380054401c0c907403251085850312030f0060024080420b2900307100009146c1070301d000ba074041c1802000a0f03941050800e035030031240c107000c030f6142c1035889413002d03655003400e240350100c0003004003c00f10340b90340c80700044003611011880000e00380d8180003d01600344101d400c14005e002041035141d0000d080000c50503400350780b020800703460f03101a1400c00076400901900410518a0320004144010006003032001c17007009900b180c00ca83c950744015011a50305039000750020007504032010014130725810464010340708207000500030900f618843d0405101e6004402842d454585500a11040118a91 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 864077526 1250 864076276 864076303
    0x2090321041a032406040810060e0601140f0c0c0901030308040302153d030b0f0c090a090c0e13020423010c02010f050403060204030b060907030e21250302 68
    0x2807941c1410202105560744c18101c0d04501c159800315903405031140020707a001080000d00700c0d914800f0310201e51015014500404014555030000a141d81d84100400c000d8a140307d02c070b182c80e0021b030001c2401140d100071680c020500c01c40182c55079588612034000d000398003e81c1d03a0b40c01818280780003810040b840d4038500c01c280d0f0107018000803000c100001c1d120600f407901401018105001e1404020f0100e481ea080e5101003003500005025009130300034070502d0401000c0100c0c1c0e50313440c105070036802001c91064200700001d10600090306644e01000c0880302500301591040911000200721742c45580403820001c0e008541000000c20050103010704e03071058049a8900f2180c540020000380e00305038040c0c1006003042c0201d410301d01640072100903680200c4259500d82d12400d0aa40511040c0c4ea5540109071201c0020851807081c0718000e0b41b000303c80040d0802e030308108507103280e510180018040400c010810750150021001030480081c1581482d140f4a4905041c0039091001704c6080300d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 864078776 1250 864077526 864077579
    0x13060605060a0e0f12120a140a0f0f03050c0d0f0207050d12113103061107030e04140109391b120f030f020703090f080a0c03060209032104 61
    0x801100b0101b9244500c2c404489801c0c0c440c11350341e030308503050303030584c0129650440c00040e800c640f15806944200c0d10100390302d07250044203010800b1012200e00301c0700401c40c0207042c002c1c03140030074450b008480d40003d80e8502609100003902c8840c05d10110041d0140403800b80707526082c00388094015080d40c40341c081149402c00c1c03541600b1100240ca118000d1001c002d104905114003095905040003031a0801d4007000f0071004040821002d900060040e03012035032103c6d03d8102d43c54203010750101c0d40c03080d181104c0d40d43d19001d00c00c00905076011340402c140c030000320b01810684000303610b00b01c0d06011100c581076440c0c2c155009441c16800b0808420303140d202c200c0000201b2108081480400318602d00781010030300ea00400c40003007480250441c00c6500004600c41070581c480182816944403520704955640d4a1500da0360340c0705140c5009103480817050003000030441c1903024001210001d81660003603032080d2190741a1b4142d0396601040704030045010711582c015103000103602c98104611 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 864080026 1250 864078776 864078799
    0x412081e1303140a1106070f150608210703030e011d06040c051804030f090b0c01021201050301061a0313020306070903120905011d2d15040e13060605060a0e0f 70
    0x164a41620400c01e07107401b0303010015802c000c1010f0707046481292a000031a101c0c01c00d550f000c0140152106208014441c40354050502c1c0742024070341d0080c1c8020094000900c0c203201c3d81e509502130943c56140c800c41d5542c03420290103404071142c0722100100080c01816480c5407602d44240d505071541c20190107024042458524041d502e08016001078240c20b012040045a91088030f000901d90451042440c003c500505141015005400c45510040d003580c01680c031903060600701c1d2241c0c0b040c94118800400300740345424030780d0000c40c0c0040030100301c0140c441550700440d02e080c10581e105400030740c6010041041c41140030292440c00010701e0000400351130040020440c1e82c030540c920300713482c5841c0903072003860b0760312201410b4107409132a010381407144102403454280f112440d00c178003500d1000181a608811a03046406840311910340100f240c4072000c201010090a13142280e55a90710000420b0b940d035640054040341c0041c0d9070346003103102c1850520400300600703640f41d4050700ca00509e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 864081276 1250 864080026 864080033
    0x609041403130f09020f3a1d0c010906050f040f1508010e1902030a0f1406010f02060103150509030d020708130803120601053403140412081e1303140a 66
    0x1180d51400784940700d101f42d1003064080a0640e841002150b0482007120216050324415410254044e48041510b4041d4005400f4950b110341c104807045001550264080c0543c40c014805041d419400d82009414a6180d2544001883d0181c000120415010036001000307640500355a0151249070301515450400c805d000c589001e005201a44081c0c0120001b10140801e80c080d6950040c5040c05000c0d20441404d0700c0302e96042626000d001616048101d0002400080c203c2e0480e6848a01024032170841c81d2000000c2a024000e0500782c00200b2608104031410b0018200040c09241100d541345880c510810303150308194010300040d001400060350180c0015181d0760300c8002801d003d9650a1146401c0d01e01d12100080b07007600c040c1030701140b0701e00321080354002c2501d4401d450700f032600c01004d0440c4807940182e10501801c1c4950120070070001c0d00d108041c0920030744138505e018110042c1440b0416039008040e440464800000741002406400b50307080c0051042c4a000d424a000d1585 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 864082526 1250 864081276 864081307
    0x501060915084c050105010c0309090b010c08040303020d0e0a051c11060f040812310905011202040f0c0e040b0303070203010204060f020615090609041403130f0902 72
    0xf10715440700c090306049980b0f030a02028202c003c0260b846007200508051002c0f940d400f500c07031015141180e01d0f0000115843d40541e0740451820381644810b03036258640f00102d0701078501c2005d4541000106442440007810041c05007002c2c3d8420f0300901800002208014400004280d21510801910b081000140c460190621816000b102d01040c40519410070600b602501c022681c1c0100d0000740f520120b01d07410018005a5146d801a039168208241201401d400354847c1c0399951050003007084e41c000c4100722101c154200020880e076100c1e6451484004071942603007c481ea040c824400c0304214506403081c2020b008106600300070023801d85400400c01c10050018070701481e40c40341e14103000c0d40d04000791203290780d000b0000e40d504c9441e12402003020066034808009031042e5004900011075809404941ca10060400500c1e43d44400403c100003070040e00c25a0818901801c1081428091005004911099800380801803900d150705400250f03541c000e00407248103110100c1f02d41c0307020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 864083776 1250 864082526 864082543
    0x703030c03081305160e0f042f1003090b0901050103050c01180f06021609090b0a05130b010807060f110c010e0604180b0901060309030e06130e0103050106091508 71
    0x180340201c142d60f1440f00d4002c4a6800d400003403e01c0c070a0020300b1200c03030300031446502900d2992a03000b00311b45030204c01e055810001e8a004118144d000e4400440c4d0504400c0c010f40580c2d010f1250301c4c003113060303400709050400103d40b0000007074454a410051203100290550001d603004020802d961558403590788400700540000d04100040f1100e039485800400c0309800b514a0340c0c144100d00c6d688140107503596402c088003214580344800c0002e181c0c4130a200b042d486540225605900780c2c2e4814402e401054000c003001150b01c0714400e08400308400d83c460364064410140180485c60400f600584410507120070b507000c1140700c400380b2440c0c80010514081122007820002c61000302a8002980c0f030140d80c000701c8120b80031071500d085090560b00700c42880c100665094181d82d0301c6120880c1030310305440c0040c010502c030071151031840c1050402040e81191481584603003548410b050f011050080c0e100b560a691542d00c24020720520f8807880a42d03403840d06070303600300d145460003041d01e07000074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 864085026 1250 864083776 864083783
    0x9150915070e12010f0b040506150d0903050403080c100515460501031d03090f04020d1404110a0302180705040b030103140f030307120b030a05030313140703030c 71
    0x2030201c814801d440d60290b203d40d015a440c000d000c080031401c2c2800003060140810340c462410013000c5045414180c000705c034032042d00c40460f0328095043c0ba01c04003401060308100c0410604100001c0840c407884090b280c182e40000141c0710180034103500f10140c0e10f000e444a01408940c4a65107055a60500ba0035620100c1031301039240302e1001c18800615840855500201849680d281e0480002c82014139055a030241c8041068202c5a2a0310300c0c104c00741c251107480c9a104101590083c900b28000e07a04070300d0010009860100d2084016080e1103103032940f00c91454000052000308007090610b4440320b101078550421081c515000200e210580b03040d455031101b00d9002040300355204504903000307131900500c81581ca5940e803621207690496031883c42c000d806402042c44160201000b2207000c0c01c1d0030780d40d00381c00245411200000f4030700058010f515120f01a1a41c00080d0180042d6105100c030748581c1902c0b40e21814030350360b004410006403200f80c002e20070510000e40c100d801183d05580 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 864086276 1250 864085026 864085037
    0x20a05060c03130215090405180d02120f03190c020a170304110d0c080a030503040201030c090501051b01090c0b19020723030a0c1e080a020d080901050d050915091507 73
    0x5d0b4402c11055074411003c005410a0a003020010306c2c503104d06400b400114400c0440e0381c4030440d5a0100d0311508030101e00400454104058800486201c02030750700540003204000007181e00390f00100c2100c1c1c6002181d0007607040300d85080c06001d840c100c100701c42e80080c0c0403c1d145242560354100170604e040c000074803172918002d52609028905107418058100c1c074080312010081414060032a0300f00306e03402c03030000303050500f0041c9080c451803620045400c1a1141d50814034140d0b0800783c0400c030640d488042d5075031207240c2400302d100740080a0040604480107642c03400701500718039401a407a01c10100395441078400700181505600c845c074444100c024840c0e00c806a03d00083e04003014004060000b0841005c0400c84c01c050140c0c2a20715055015008142d1b40d55410180c2ca945a10f14044d521240312240a0042210600204100300c070514045151903040c030f950780122481540c00c51365542c020484102c07080f0307a4030030058101d284c5800030036601540c20860442000014441c808201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 864087526 1250 864086276 864086299
    0x1009030215030c07050f030d0e012901030905010609060914090d030203190c0305190c051e16030e031006180c1b03030b180606040902130510020a05060c031302 70
    0x140f14100f0348008a40c06000d0f5954148082006a07590b004000c50880c0140340c00c12801003c481440f928a00781348241c800c0e2a0800000e541250821404821505241d00d820b080d02c00101e0a02c2000702034220100001000f50512004800319454925510317511f0800d0402e008900c01c0000f00d600e0150314030310f07015075680c0d5a0b1411403450b031035040c00300e40401d0820800d0116280c154109520882c2c03c0210b40e00d52145580403107054960583e41003000c1001009140e11000e00021010308002d50803030720502e40007800010290000c040c1e081034000480381800c1002c240350130f00c4421442c01c03410f00c06000e038a0401103464015550f10140140c910317520050500d40900528900d51b190040712075503c20f034402824041e014106828405200e0045090030041681c2c00141280c02034401400550030310f82440900c6c8000c1d03002c8006409056241500000c081d0f4031031800711003080b07042d406000001c0c0c66150807490101d000d00f802d0b00344141441003080450014810101803074048445103500d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 864088776 1250 864087526 864087541
    0x160212160f14100f15050409050316080301030b280b010e1003020d05060913031d0a12050c0d050d030f02070215040806010b16141501090506100903021503 68
    0x30100c190006259852102c0c2545101a01082d0521280600d41e001c0c04140c0203148403004865140050080c841200e8030300b4416800c0a901800407144504205c91070406240a509250103081400300d034400740c00801482004200710109801c1000e80c0350f071440e021041d071a5452050010841c64400554a0003a40f520760301c00c030f00f4004200c1000c1c005450704001e681006010758820511031812900703003400701b07141d424180710203845204890443c0d000d46400d5501121035403624050a01d040b0745840c2c1c1811140e5668000400808035000c10b404d4203415440c1c160b081c0a40f22580728400d920354040350011803000301e20101c05805e5440c0005002801002d003000034020800d0103508048802d200d0184914450020000c0d50021001c03103d10360ba1340c50b100500c52144034105800c58408001000000c0c8a0b085506024490701d02528860325003d60741041c07940b03090b400461540d4541092003405d042000301d10602101a203030007103400307041d5004224001d41001c165425820000000360744c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 864090026 1250 864088776 864088793
    0x51302060921010b0f01050301030b010603150803040b190309170d060f090c0e03061e0a060b18041107260c0d050307031d100c0201150e16021216 64
    0x3064070b040d4840740101c0c035954425000b040140c000c280550101100002c643d0300038801d8078100c90380543c214200343e09202c822800303002c8101c0012044104000f010450306030a0001d0009400c5d00d07558107442d4259200903e8080f5011034120701071610307008031701c4042580b66550280541003a0001603950301d081d6030035401171180e9400003010800c071590205502295402040c0c4040d156610081510008010151030b0070741070705c3e40c1c01c150202913008100030b402050300503031161f0700000004a050fa02c2c80a283e0740e038010400e01c410559500407040307051900e8402c80b426158070110450074030002740d81c3c650003441042000400f8000c801c01e0b0398480d0b4600402c40340000d02c11015240304484d100c502802c66041542e80d680803a0605a11864076040f08840250900c1164020003c0c6441000400003e0868804410855413285a00c00402d00c41e2014500188520911042d41c0d01d8111100d5120754100e400c0c18003107410484c164044206400103880350f41203085102030140c02c062078500103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 864091276 1250 864090026 864090049
    0x60c0908010e0309030607020c010206071b1a06030105091b0603090a14160608040f39180c0203030402121603060f051b0a030f02070c0e01060f02010513020609 70
    0x80300c1d030030000d18407040840070001d458084016801c660590b19542410703615070400100c950f00683c08940001e180c1840780054803d003100850384030a8803009504c074080c070010514802c050a5032103c0521400781024401c41d5071146010703029051140103525228507a03a0750941c0f440c407503030002c40450010f810074023580705010b81c05003e0381400301485003ca074862001310100b80340d0341003c0900040c2240030b844a58499031b030005490045256654808034030f104018140c052880e89294420494080c100c070748010a98202c0482c111940b62000700500039200140c90480f1506102e04400d070b00f034001040d01e40040d030403200b4044d80007050040c545880c0c804d8001e405101110700002061203d10340c0f00240b000b40e1075200b131005a440c400d00304580400c6d81c00c4000c480741c04000595141c0e202e40d0280004140d00c170800f6190809a03155184040b4058102002c81c0c00c110004000094100c2c00410002c0f0b801d00080c011443c0078203d40300034040524010b4050b000000e01c1101d83e0340c3c3c1d6084403c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 864092526 1250 864091276 864091289
    0xf0d03091505010e0601084c06110c0f0d0b04081608040302011d180a1508421312090f0602010e0616050408060420040b0607060c09 58
    0x2e036940e000c1201d480710090f00c81502046580703001c50320183d110743c048129036882861074200b200324074084c1100d1006112035a0307442d54540c7c20803580e100c0302c820008000c1210760b66020221544014050070000c200800a2007140914488101604d82000560140342c1142d090049a80c1d80e0600c601c517840340781031007c0b84030203001e03140341000140e50161066a0003030340c8074140130090480300206800c0211b40b0f9a40001101e44a10074011000c804c076a0102c558600442e8140041c3c40885552256401c070364410780049242c21000c024402d400000c945004d03458404d5040c100800c22084045c400820030800e02001c0024585000c05209407502ca5100804200040c0b0f04c5900516032403aa016940c580f03880e08000041031071050107031884098206001d003406445001c0688100001c030301d20b29052000c28800010118400d01440c0d2040c1d008102816503134402c038000710b00104e017843d02f8510071441c6c040002c5494546800b0b5a01c038a5002c400020303282d4800131b00b80d403504070560046 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 864093776 1250 864092526 864092531
    0x30703080f070c171009020f0307241e0c030c1502030714031e060a0f031b12031b0303060905070207180905061603020d0c050702010f020f0d030915 65
    0x1070300c0500c0d006005000d00d07030081c461a2440c80d03e44201041c0d551031402d01008580c0092071280000300c4030303480840792610080c010f480c14000080441e0800020342d01603181444a000d2100e80c0803103443c044184800305242480ba83d6800180c10045c0e0000640c07940e0802480c0c0d0351280c101401080d03120305076900038209103120708003001d212011354401c94040d00000c2000503480004020354050324060f48020150b0100788240d4107a440e4986070007401d040e401005408009200e00c910042c040c091401081111a1079020304010b03034000d0459408608038200d01d81c0d00c100440d9008580c11300d5040200c00103c0350303c030141070441c05041203801402c030103850030302070011880d0001400d80899264005600074103400d94000d900b1259590380c00790403504080f00141488100c03c08440340c040b9a802c0050038410b003a4001d0040f24200e04120001c600000f9080065603000841c44d064010369100401155101305d08141e1034031241c40044041c1522032014900b00b00c540306401520348140c0700b04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 864095026 1250 864093776 864093787
    0x241101140a021b120f090f120304030b0c0a020a080a031d010b040b06030408040302060f070c0905010321120203062404091410060815040c0804060609062303070308 72
    0x12000940c0142c82c000c9000740c0100d007a402000c00400d09044134409020100c0c10710600305010b40c42580000080d40d8840c0d4821001d8845540300c00c04055801e00103001141c0b201d003986070a0343c001c030300584041d50842041c4070702c9851aa0000782d4100c030076402a00c103601c07080003100a4001d407030010034107040340740d040c080240b600505601c003010889080f2424440c0c00891410302082d13110070744020340752100c10001803002d401d001004003014000220503070700e00700b950386414081c8080340d08000c02c050b840303100420074401c40c418450750780c03036410b821840b54000319040035001140036601e6424154020002400c1965500031307030045403c01035079030785500b4046020004039074041c3c000d0340d00c694940002c00c1401c05000c5529807052420918540c1200e05010b800e40c0c0c0e20350b0040c29010720032107960b01601035480341e02a220b0b0000ca40d8031016564289407400d2025181c15811000449103420403c0088030500290030181214603211000f400c001071002ca420181650005002180001032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 864096276 1250 864095026 864095041
    0xc0c0616050d080a06050105160f051e03040e0105040b0f0f03210c01050709060c0f110619110318210303160207050405012d03150c0924110114 63
    0x1c4610405400384c0400510741c580005403041c4c0074059240c85031074220903202c2d00050010380c00c512a10300074030071074890851203011040c000c0341c1003588a4550300041020811800d00000142c094403003107405008268200002c5541d8240b44c005041c0b003010300d00d551075032a84040c0148130190318205403406444c400c050610a0a52120740014015031078600040c160500c9851003500b50b443c560b82d0300c0c40076402501d83d03070264480c408080e00d4005012540341950b98070b4000800301140042e402c07211101500710701500d01d070380d048010740c0660402c1080c4040c0044201c0918204031084425080c680400e0291040060150b0b031030700c10317a100020034060b480d2440a81014518150780c216103403e07444000380410749800703111301c0d250380201148035088018038005101010b1009856115070030794a40314034411403c10b510707511700d0b03e0f03442d0f2040b103176550300c211f4407405403800d035520541c521280000740030800c0d64035001804109040d40004903010b0290440701d04c0008480f51171050741030901 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 864097526 1250 864096276 864096287
    0x203031e043801170a080f0d1b080a060f0603110913092307120201050c0105070801050109090509060103081308060906160e01080105041503080706060512030c0c0616050d 75
    0x2c2c403401aa0080350001500b5003481081600b4141d511010b00114031160341c2d4101130750441c1380300050381d603002e00c288110010940b041040303120000c100807903c1d045181c400340034040d0180c16110254100541405088602d00724801111000c1c03500060034103503403034140c486024076141c1035030143c00754131144804400c542002d101c403030107040840158880d150000002c014502d44c01070f11134014441c10005c03200f40d496080c00450040c1000b6140c2050601c0c0d00382100d41c121b5514002c224540d00501c8256401280070b0003034450a1010811414519101e03991a03005100c000c01c46400020303058041040e0000020041c400601241c8803070508414598446c0c2c411112070803085d04020056040d00d00c1f80c2051a1a40e40c1038480381966402c1205120290007020b21903210391919800c0000050840c4004000130343c025840003410604004c00c201c00761041e00b144410742c0e842403112101a002c003080810904501f2a5120799448080c1c00c040c0c8961103c1901508900890301c803024400e400a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 864098776 1250 864097526 864097613
    0x19060501080106050915090c0c1606031d0c15040f09060602011811010f050c101d0303010e070c2915040e07030f0804090603050304030605070203031e04 67
    0x1c0009000141c1c4400600001c00d1084072900003aa402c140e50304001c0c01e00148040e00700603a43c020601c3c02c04058501850076804101448501003008020009160706104a88580e040303658204901e5002180c04c90b541c1d00c0c00d1100600c9280505440318071041c010f0200c400a12031607041400076981c4410300e82c000e0695100702e402550a2a40c42c1450307291a02c0780ca0100c5502802042034000b0312001181d0340102c900701c0b4014400108031404108804012400362420004408603050403401c9148810f000000d03d0b20903254401d100511001d4060490710b548518249800c0e030308403c460520300794903144881c00641c901b102c41c014000103c07004010341e00c104a510a100351a40c03480007030008442c103161340e1010f240c0200400333000059604090108507805103004505064884404804459040e401100d80e0b07480000c0403c100303d01c42c0103255100a031b0340003840c01c5152040c44c00e02e0700425211503e00040c081d00004042044001070381c0d190105d840401070100e40354006108648030709 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 864100026 1250 864098776 864098789
    0x2090a030f0c0b030c0a050313020604120309050604030b16020109060204121b0b0405010c05070e070206010f1a0301140103090b10170f0a030302090a15030f050708071d0319060501 79
    0x4a04040340403000700e030489006081040c4058982041010300b11462342010b8603144000420300030120140e078403000a40040c00890201d4074007403c103480c018003d100c0a1b0f10003802020144000c0010500c0d00c0c2c1039942c002d1070206100c24200303400d24101d005004141005044c1032000c54046043c1591454003021103120752040c00c40303240b451440f150541030b80e00c2387c64502201004144165485074400131f07100c1d0301c0b603002c84150b942c55201c201c0e002202283d141e001a80054010092460122422070040c40c1102c00f064442c0da200c12884428130050180d035200c0801c0440c203041b03c1c1d00c680d2140320b046820080415150071300b012800c2080701c0c03a1041c00c1144800034500d4148a2020410106a48000e0000d080a203000c1c1e034150083e40024400a41c0641025070014100a903440211300100007a5800544028190141c0e021143c028007514100058082013000c116040160a64a0480a050704c140510030a0000785004460340c444040e180d5103150800c104105074008505854030b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 864101276 1250 864100026 864100043
    0x81b100522180209100e060405060c01051b12010312120f0c020d0e280807030f051014040201081503120408010e0d140c0c0904030509040b030613110402090a030f 71
    0x411074004180e000b80d113a05030b403001c00004560200780c0108002e17201c0585c0503000394181540c500000340a500b00c8480a100d5075180d008000c1e4144102903940540c000c0122454100510180c480c03c20441c1408000d01000c1d412512002031409100ca03100c034507947c8031003401030914000d0624003403d810009803002d48924a0001c00310350090708282178411018182c0e004c01d20001c0c1390b1807105c0c0c030b840d5142d1070b1051414402151507038040c400d0b040a18050088908043c46c6841c146140021041700e110040303290050800000d134886055941258091800503000e0b140d45ca070840000e035440d0005581071040d403041c0010381610002400460710098020004841d201c0d0400352140c24441200340007901081c0c02c0c190400e24400904014a0050201e13a46984c810700401c0c400d042c2601c040d8042400841c031142c2703601e041d0203800654102540505501c2c1411401780001f90040b4000901c0008104140303881915150305036030010400401e010b102a0b0350f400c1540e90018050015900d400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 864102526 1250 864101276 864101309
    0xe150604060b0a080604060308031003111c0807020102010e071403011b0f120b1801080d0c020f010302210f0711030f0f0a022505010207081b100522 65
    0x352a01c0392804603461450000d1600e8000c800880700c0340b000918130356100e5661007003c0003190001002c2c44c45032815410700d554240c01c41c1021611840d0414866101b0200b000d004810040700d086c050b4112a400fa5007180c4912440c401030b805459090341c0f18415108020b030005180d040a0070083d0200f41c10340082201103156296920b40a280c06a42c801140d0414130003030381f2501c1020455242d1703951070340001d0b50542c02c000081d95940c5404440c1d803e00072020050100403411700080381d243c46503042100126510341c1c00b0881c40306410180358103040c2c0c08030328011140d07800f00102580c1a45000d2051040c038129030324108000090303940f940003411004111440c10000411518039140e0300407214140700001d0490361041e07014407003c0e000c60050301d0101380c242d0546401c00c91030075904c0311008011414800028580070f01075000308225408421030034007522440e40981168541a280e201800d21f0464054469204c5d40701203a840c0d14542d500c02400244224500c03060318200305a1aa00f00e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 864103776 1250 864102526 864102529
    0xb0904050c1912021014030106030c1704020901051302070f12032007021917010603030e0a051c0c0527060a0806190e030f0d0b010503010f0603020c010f0e1506 70
    0x301d03024069410f01c01290b20b104005403602510044080000345080031040324212400001a0401e9000704042501c03031181445007a00718100011485400c00801c15601d8141c0002d4001007046c030a1501805c00030b201600b1145494040360749071900481203a91841561802503a4400d544680b00006454007503014150044400610304051007030343c50030306210a030f030208042c44002d02c040260006060000180340c189000c1049154050300c0e0002940503d581400740210540e50b180500c2545512020301a682c0c58104038003405800c20903403c0100f410b03203085903c501c0c10350082540101c0c014031070480f1107107801105002c441c0411110066449a80c1132114241203030080101c40d8100b03100080d02300700410054074100bc9000c1c2d002c078060802e54a42030440d80090103a0003000c60010b82e400c49000b05000e05a030505e400e1078a00d16640c500104501d0029840c0501c5081540018000750028425004050b0103a000c8000300711000d8404840c40d503d01c04a41080042003003d800910755 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 864105026 1250 864103776 864103819
    0xf0e01050d0302120c03160302030705101116020414040b0103050d0c080901050c01090804080708070f0b0a080a140c071a220302070305010e0102030f0a090c0e0a0b0904050c 76
    0x490b50305800409201d120062070b50b425801c00180d030281440709200400002011300a0903000324080d401460b43c52486062041c200764002040d08203aa00308480d141e0b142c401802100c0206450b002030580c03082c1188002009064404242180c2d002c0b503a0503c0180001c001000d4101d81c41385003151001d01035030506a4010341d0585024049600c24480342907294001d0009003000380704d0320000900c0c1c40d1243e036010703440d4105400400286c5c1c40100c003403120400820481c4058601c58005542c0340d40303446442d103041e10402c0303888000c010300315021501840c003170780042580c0701c244010ba448610b0301100301e0500340c22810b01640d1300e01c10350811502480c441c410301805450420071021031414103040980c0d40301404101181184141000040070600070710032030780c0c0381210341e001580d607040034040700050100180040c00c1e0b0381d02d000302010000d40c03461000c1044030308016022142e42c1e0740703100003001826488481500648041d00b00401c10001150780c005c0400100d5020301c0039072483c060000b2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 864106276 1250 864105026 864105049
    0x50312092107030e0d020d061a01020f030316021c0c0c050105090f060a050f0304080a030b33040503010c03060602070617041707080703080f0c030403170c0c03040f0e0105 75
    0x101203080220b00003080c86201001c07181d6102405c0c000796203950794082424000c5000c426200203680b01c0c600d03500280b004980004096003403004010710006011082d80302d00c80036240000116922038000f030074034002e000802070b101500240c001041a03040000e4035505c224601214500e40035840410558060400e507441c1e9440500304200c6851140b0038820f8590190610b0003c0c02f0040c450b0004000246000b548518440c030485612500700c1c1d41c0c0542902d0382941c090f840ba6040c5400300c296a20f40b4100c14021520340260a050480b10750090b102c01d1042c0d4010383d800d135003045034100e65240c0540000044506075070807600815a9103038101d440b200c85100c0d11136802110310204003c00c11401ca4511640c03400c1d408030780390120300c0d13580383c0484e071013107102300c0c0405c540108000c0d903196801c18443d4030038005200c0c0b0341345103810f03500180b04002044803007155039010404558030b40107000995103080210812259200e07158481100744c0001c622900c09003200c1c1800100742414030040d01032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 864107526 1250 864106276 864106333
    0x3020a020613030207050312070b09030405130b0a03080c030304141b190b030910050906160c1502040902091306060e1003090c0e010e060301060806060d0f05031209 72
    0x700c151a040c0a4100c03544004a0940440c81100340100b603e603001d01210460410a400d220b41d1003800e4507064100c0300005103241030300c1e0014081003200b5103662021000e01c0d8140b9500040300c03007200b000250451100d42001d02800004100c03030800d84000801580141d008007064428444a07461156070f44541d02480f4501c00c1140a85032102e040c1b44209080042c0d00c1c04603051065299101d84140750404c480f00d00c259840307100300049103102071040301d420100150181c113091501400384544000780007002d2040081071074014041c4559071000e40380704030a000c41507641c1c03540c2d10000c0c4041d401005a40d4422000000261050b8280e84522001c88aa41e110030882c8050720040006181c4000c03060f1041c15125598140083d03000c21480000c3d210445000009505050340340744400d10042a00e03000f617142c0764091006600015040d0390000c1c0489061403a0041031408064110311000b000b0203e12010a4040c003018800c4143c621400b500320469000101024454001416400c56075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 864108776 1250 864107526 864107533
    0x1504060f1e1a0415030210020106030b010e13151a030c090a020906070618110d201309120e010801060509010309140619051302031e0a050a03080f0703020a02 69
    0x285420340040d0030841c40e0398001d1001150010a840200b002e5500340e41d070481c0c0b0840f03903d134240b08624018000401000c002d1000700a000d007965110b01c03803140b0602440c81c44010708000100b401c0000086121001d520000c8800740207000418000940300300c80214914414800e405002c2d81070000304c401858000400c84402501d8520960000794820000c050704600100000310206025000c1c034081c544400c0494454041203041500300c2500b07031000248140c0d10440d18401040034140c1c12924070039100c0c809015901c410300090901d0240c2c1000090441c1001305e18801d00450a00e82681c4180a8417091042c41d220401182e2050090241402050b030501440b070301c5510039884050740e03034407138020210217000e05650ba9140c080d08036542d06140090038898080152140203064100c0401c1c1044c0c6e240c501e950340025214560100c140140301018814a12000000c111040d031680e04203066a40040c10350800400000049a08407100c40b420404220000e10134401c4801040c1e059002c3c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 864110026 1250 864108776 864108821
    0x32c0c0409020f0319060f02040b09090910091a010504151202010203040b041401020f1f0b0d080301030b01170601060c0308100e0108010b0f030706080c07060e1504060f 74
    0x100001070200580998019070341c55144074194408212006004000000002001c952454110180c442e080c3d01c400310f2030b0040c0820010320000c10140d507542841200c06405039a10200741925012010803206201810100c01c0814000c1a1411440d800c044200c0c60456a0f00c0c4c1c1d040c481130f41d00c640c9400c0c1040c0b00b0101e080055210300344c1d8206074580b051060700d05d0241d848158801030741182e008600c189408120b03c5000b50703010003080c001c89103040301628102407820040d02e82081142103010a1075180d40340542907503602114400c50540c080c0001d9143c0d6124100503203041c10034000c0c800c00310a000c01d2082e483e4400243ca50488841359101c40c45010540c1d021161a8005441c04042c0d10a040e0040b43c1000c070054400c2c040c1c0115000064800c408000f04411810340152003400f0390002d020500c050760344441441e9000321408415951038103c1c1c900503006110800c00005036005454501b003045080070360340c9010700e010723a006200001c1c06c41444402c541084220000f0f000d4000c14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 864111276 1250 864110026 864110029
    0xe04052a0f071b26030a0509040f0e2404050606100c02030105010816050d080901180f0e0a050a020c0d030f09060e0303040b0108030a02070b0f0712032c0c 68
    0x106200d090803207016042503041d686a59004804003038880101c00b006009100b02c1c0d0154240c1180f0f04030301400100141c0039500000d4503407040700b44c0700042100004108801c0c0d103994000c001d40b402ca1640c10004d4071082d0017136544805007001440c4440002640d015901919013900f90300a0340c01c980a01203e4660304100007141c03002500c00c00038000e02c0c492540247c0c0d070a12400b8000e150420281811000034100e0b84000200b07a000300b44030748510144a03010400c0365060f40d04c01042030924840803540c1c13503201e1003200050345c010b501c2251541000b0503490411480f40340079400703003c001c1c441d5884034400e120990290540001240e03010700355400c0e200740700381c0085129440c0a1310000c0d02030201c0e2140025508243c1c203e11031688000188820000302600081c01020180095030401600600083d1a8502d42c070680c0700e400c074007103004c0400a18030707002c9845495002e43e40c10a80e0440b184050040c14200308515560404a07021034011003500b084d24941c402d1540103001445501c20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 864112526 1250 864111276 864111361
    0x20a090e072114040c0e0105151603230c0606100e1905101e0201091e0203160602010902150c070e0901020d090b180106030305040302040507140a0e0405 67
    0x28080d00b00d44801070708002ca000b82860314000c0e805040011111403d11220003221403040e403180b070013400000c40a4600704501000d458502107078854041e105a902e0030b08840d44500e082c0c101440c901c800f0000d001c5688010010040d5140100c00c0d0342c802d036030305400c200046a8041c45070011482c41c030100d014900c1d250102040419a4034032100c04513440e50049501505d0703c0c4c00040108841e600400d07401042c035000021110b142d40700034000700e040c699400c885044591400c0c8140207a0780d084104540d07043c4008130401050184a6180c0d40c2d5880d0f000340a00707001030080c3d000f00c100460050044151404a61003422944001c040451400c0d00c1448880401401300c0d905550030f1000e40312105c018080c030940e080c00341d00c42c5002800d0090f2603404a6801480c014070a07032505008000182c3c000c001d49040f02d8040340e00080a9990410a4903014290180344041c2d410000340b0050785034000d580d110100c4c0c01900d0400007a5a030f1100207004122030303041d844043c1c0b4243c502844205000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 864113776 1250 864112526 864112577
    0x601120b120d050c06010e01120f0f0501021219141b040302030303010b090117130305090f090f01090e0102030c09040b01090b040b09090c0306010e06090a0b0d020a090e07 75
    0x281021200c01d880d0400941030070080000500000c100048403c0303400c104128080c054000da02059a03a03502d04440000f01d8000a00004c1408440c4203403801841001140240c2c025001070007959506400d0f05100c1116800b00d03084000011640c06100c4092024890361612410723814500d00d0a860b1141c0b862032000964403501c014000c10480440181c9090000e07600a100c175002c06a03c8020050001d81070401d00071420103140000d208012050611140b00082d82d0b4150070801d9640d030f0544081920040074003070054000f5443ca081c06120a45020300c0e90403a001c2000402c100108041c66500340d2205441d08104000144842100c0b0300d4a9030007450f0403c0141407651895036100c0038016260000d6025107001d1401059000040c1004405654401c1300129414030314504080041c18800c40b9582c010301070000403c50300c1192b1520070750000a0045000010f0700d8401d24039403580030f9401066010f0010751701c24000181509944e460038002c01e0b2a85034141200d810400807040d91910 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 864115026 1250 864113776 864113779
    0x13120311041d151f0c02040f15080d0c05120912071401030c0c03020604200301090b0405150108060c0c01060f060c050715050d02070f140a060b090601120b 68
    0x4020018030202d4060a0301c8100c025400c00466030318000042d90600e07610503200c2030050f07901c0f0100d184c2142c180c03062120010010b04068032903001c54008100144110550103c0e0703035203414016140b1416a2184008468a0341d04888100c1030240c000c0b40c131081ca2800050140d48003000d18101b00c1d00700c42c0a010064005841c00c02c807600c204502c0d5140140c140d001c461841040584040c283d40d150107003540801884c240350a010010350b500030760b10b500061006e404840d10b02c5c00101c0303508100e103040c4a4800d00074020f0018580e80d08188048070f80580c0c0c00c44462080031580150950b0001c43d45d812205100d000d0002c030742d104000000305501a404170403c5550b00e04020915042500c40440500041d9644006816035440c00b5494100c154001700c103814900d1440e1010b1541c4842250b2000c10152000340e00c0300c0f41407a00700c4200c900544010b00c03031441c0302c1566280078030014102044601411007884615008010b1200b00314042d41c15500040000c20f80c6090156a90000c403180c110 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 864116276 1250 864115026 864115061
    0x2042403021305010522150f020703030e100e0301020406020114061507140c04110901020d083c040f0209070503011a03090a020a0305010606020d030b0a090b01020a06061508131203 79
    0x1070280e643d1403a521b00e400080590240c01204d0003110351001e82e0010085580c0004c1800b5421518007908268003c424507101d508182a60701c5141c0c403400800b84a404007400035502c0d01d481e008041c1c00703041a41903030142402c1e50b00c0080c11501d00140707404144544403000302d00e0031030b2035161012241400c10007035085200b049075481403174132170b442803909a003007544400d5268510a000241820542d468580c01c210030102404210060790f180401084141604049038950424104408081012030100711800c072404000078010f01d03140b080e100c24400c9440020654480c0c80650742400280101c044420781402405000035840005640103000c002c110380ba8a4090f41c00a210030400b030b00100c0700781e519030b0030070441d0540411034049009034905060290a0340709000c00c460004520510801a4545052001780d034002d01c030114400760000d5081c051980c4440002244910403038000c03001030340040020b1f1035410270003d0034940319407001c0941c003c02010b250440c054a85500803442044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 864117526 1250 864116276 864116317
    0x380a0c0c0c0b09040b03030c070620010204171c021b130507030b0a050a03050316030e03060103031e050f370c02030d0825020a06020424030213050105 66
    0x1007180021100800c0603441e410f50703410f44102440185e070100000345010703500500003007505440c080f8128003030f13604520b0001300d0142c02032810382c4e0303060041d03808440329440001c2c0415411414140d403281c90083c0030032121030400350010a4000c543c50348004005805c130200c6550440c0c0110344031520b81600400d05108a03626122070030031100190350040c0400c0e66140d955402c2d0608150b030a00034502203920b07074141c500d035480b881d40704d00c10f000c02c00528545580c4142c04042c000d40c400c1c0642c41d40581182d05560312450050301e00d1144542c14110141c54203034071030f201841441143c1412041c00c00050800701c0c074a15006002030360307903c12800365421186a46440310050180912403a09030786022101c01a070061500300140e401103001000003150400800c1d00a01d00080b00441c0390401070703005221245030482c2454842e5000401450001800160030b00300c142006d8a403d1071005100c004200c0d0700d0042d0300324446c6d0b0840042d29508000d00304581d60007000070b001c0451226050074403c0c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 864118776 1250 864117526 864117533
    0x519020307140c1201060b040308222c07090306020903010f23010b0a02120c01090206030106050309300d110c031e070506060907050c0703380a0c0c 65
    0x2000342d1402c1454039401460a00514035165951005070140d0707030000c01a490500135a8030280c49507010180054800242d90203180c8802691400200c21201041e107585d520b0700095007075000c144124040704c1e03107091b49154150111101d4140078020b5501e85048a624580c0c8072000303500a2316403a07030306544c1c0705680084103020f400743c40e110741030104103000562000c0400404500f81070304040c0c1200070901101034200c0d000251002041020002c0382d80b40c550380360a15002d000c114900079000316010000181841e04403025601034110301003a114500d01405000340c26a030039424080001c8154100881e09a0140780109100d40c0c0902c40880d911496201c0c0070340c7c641c040020b4421561000039080b030204407190020388072110000000b4501042c1c2e8491030f50b100301c050b000b0303446400907a000c0340e0018018411207400580b02019200c200e941d905081d950720518803402c03e070490b41b5240011400d04405170342e031101d0380d1070000701e01291141c90510005107a024011402e00c084c031040300010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 864120026 1250 864118776 864118793
    0x21081006111f02130f08150c04080106080109030905120d080c3c040f0e07030b030f011a150304140c0a090b180606030f0a0b1e120a030519020307 64
    0x4000410001d69585449050703d103507424594817051008607410b4007448140030125048441d0580001407040c0c2d44c444e901000041d04c5542d210350015031070301900069040c01900000f03251800ba885100c84540e80c0d1007480052841d0300050101034000e8100f203110503004628564201451001880c03c1014803401c2c640c8005006030f8001c440d030040e801ca403012100582640c0c0d01c42028884042c1401d25110110700403038a02d0260303501c4081c0400000d00d40902c00c2d030040001c0400101104c11040596080600a2084038024000310044074850604e900304620580310580404074260300d10b90711a1101880076905c00c0c0b16074841d0050351104000e0f60b460494510250151000c002900700d241020068940300c900b0304080604002c400b007003040c3e50364006903580f09040305180b40096485401220043c0041180250700c68a05150300320265807102e050b1801200075280f50171590749002996a685034401c0008002400c100182140403291600d00c10340b509050040302e00b00406561002c0c00f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 864121276 1250 864120026 864120073
    0xc0405101e08072702090d240b1f03090c1d0117010903120903090509090c0109120803070c03090305062509210c050d2108100611 57
    0x4904031031020310082d1001e000e1000100b0f100ca603290003c1a100500b480128882000c0d015a941c2c04209008141c0360200002100c540c0710b1208504028032040038603c200207040140c002c00d207815007490585c00c0c420700d40300c0c110f14401104500382c403d131001180034140180089605000402d00001c004943c03080c3c106000d90340d680e61040f0382d0b04040d40c1012499981c4070ba240c0a80c1840b04450129400150324111340c041110040340760041406e09440480f031a41c8040c0e00b1010100810100140109810340e000c602641d402c40d5442e620280880407581072a0007402280c0100085000180a01e003c2c001442c8241001010aa036944036039003402c1d400c4580d544a010b10400d54202c910340b111400008160031b0814400c46030502021480c40d0303841410078052080940301030018014003601c00c0c4014078000b0400e008808861810800b000c03412030703010360000310350101e441c15980902d900c02e2107915030011b1005554034006d1c0407250204085240b02032401400c00702c1c1d001910300c170035840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 864122526 1250 864121276 864121319
    0x312110c01141c11160b0907060c12110a120224010b0c0a080f0405040b01170703182306130b06060304030309120807020c03071d0a02040f080606040b06030601020c040510 75
    0x10040c403040d0506c4000c54200400010150b0001d00061003c2c0d42c00c000e01c0480325401c20b140000040311254142c408401c10008101a441000310300ca0400c585281546840e062a5090f118174804010320413081c5180e2007691007582d0584001400004500d40113000910005400c80312175050720b0300c862005500c1010040410340b4000340600040c00d140c021090418000e280511007008a80c000042c02d0202405007020962034070b89203c400c0200c40203400ba8190014801100e1480c4100051000c4402d403080c04090700070710001801340c0c607080e4400d08a940c0c0180c0c800a40703035500e000300042588020411804d169a820302d440201b817031004e0300c0d80c440b4016114002c00341050100607141022000309070784264022032040c0b12012056040d80d0882008511040c1c058a6100c081c5010340142c0d08540c0d002c000d801400102c030403000660314018901a5020010352024000380003082c0b00c201d5210340503902914a1140b01e0600345e1040b5404011101d2a03c082e54a40610032410394007006c1c2276 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 864123776 1250 864122526 864122557
    0x14040b0f071b150e0607060504030e190f08010c090603020703051b0c010e061305090603030c06070801061209080313030905040219030e030301060903020111070312110c01141c11 78
    0x900010919503d0100400c6842c1010341e4040c00000016440b40b017031240c024841900d401c081400c03d030080750910403403180180f41e80d411904455601460038500c1c4940c0015041d110000036041ca0b06114162850400703030b07500d00d01f03181030031400e6010790b1000c2e00840070854100036850136500c000c0388003a000342259014004075000c600004051314014030142e0f01c56a000c001300216090040c0c454011680243d404050b03d665a800080c254000c0d070314100c40d2070284400f00496290b005984905a46840d110a4800c02c02204d000c4111408800020016001040420410381c03440003100d0030603202e807614850080e1144c001c54282e070400440528481c400c03982001015416000700c060030480790008600350741c0740c400000c04c91080380c80040d041c0404612045803241c0d0030710200004e503801518000c4007030040000241403103903142880da041e0007200781102c081d40c0306010207007039800b488210505102594062480c1140c2000c503448540356101443c4101c00740c00c102a01c40c0707211106a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 864125026 1250 864123776 864123779
    0x4080405031006060e04050c0d090519080a09151403060f030703080a1b020f060c1626010905060f0702010b370b0d05060103090b090c1014040b0f071b 66
    0x5000040e42c5c21981e885a41414100b0841c09000302c16500f20740718520021034800043c0c10460b080072401c41001205020380ca00e40418000c054000b4080d141c41070b40d600d1080d90703807280340314800b505000f00381c0300107503d801e1490441d440400140d47c104000a100e8007941004c01c000a140480581c0215060070380420726103d455003106c3e814500d040e445a400203030240c1c550000e1030748071000081c1c0384142004244003c0f40c140c05c0100001001c1180c15000207182c81d4038141341196420004004424040c1600ca208181e060007400c0ca15136100d4001d01c0103480c0c2d180610b03004035000344a0011990785406030b484960310481f02621039108800d089240780102001030f04284007600c00141c00d2106580104032042c3c00000710f480f0510034540001780390b100c903c0100c0281c11400d402525186000d001e002c1981700128072035107005030031103404081c4462441c0039205549124104001c150082c00b00b00300180d130090082c07a00c10800c44c00076103440c0d040d03030380d56000395400b10000c03c000155000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 864126276 1250 864125026 864125039
    0x101e0303140f0d1a0d080c0c150a0807021009030e0307050a050603070c170304080306090f100e060a15051b150105010507050114150a0e04050a0b04080405031006 71
    0x344a0404003100340e01a140c103480d10b00c05002c1c0d1190f965400001907560b0454560003180c00c103060720002006141260307020240c20904c0850300000c08002c40c50103a48400c3d520b0b8a0408516080c0183c0d0f003951900b0210300020590f1004801006601540191040d0500071211031003207103140c5109845225080315440b003810302e40041504464011201d540d828000340e6102c40640e58131220a152002c0f5103002442d0000d014801e40c04071411038480407090004014004000d188100026a40f005056031501c100706112a016a044070f603000d03511500344100c14089200580c06280a081007040c50356070740304d1300350380304000040100060b03012485407003072142000ca2650840952004043d005100b51081b0081e107410705c074a6050100004042c41008801e4020150b018461491040f070341c6026051141031000b9120407601c01c3c0d00803580031480d4445020428001e40e00400100b402d1070295881700c1500d000a0001d641e1280140000641c3c2d41e000c125034818003d1200303002c25018035248 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 864127526 1250 864126276 864126287
    0x70903060e0d0c121b060501032a050402071a150111010e1b1809030405010e06071716050d0905120c01141602030102070f02031c02060f101e0303 64
    0x6103184450b044a00358802e41540040003103603ca4101c1c02082c0d2041c0c00f400f003503d0360f0360313103510040480341112041424407250758442d40c12640101e15101100304400ca91820f218030181c070809200501a40c24840c1c2c0c10254040d110040c841d582c1e801c1001c055003400c0001e01821940504132618280c0c1402c200c2d46d000001d00107501078a40284810310407034660340e40711100b00c900744085412070045c0c01d00c01d569511914421003080c0c8141c6000e41400d05040d9125800340c003440e070105100f4074456606040c000102da40d6190088900006c0e0010818800413641c451000003c3d00f09035803a902e4040742051211803601501600c48245240c43d002c00d0040300c01d41d051011503a50060000460181d0f00500702c0e14145c07152108082d0342d00c10300e105c05007159601c0b91000e0740540c03000c01c89600b000f04100070100a240224102d0709541d480d00c41c02c58110000d15007020041c0c100d03c002c80d581c1c0103001c04191b00486040364801030181c6500d04903600300d249440d8040c441e80c94900801c10b050700301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 864128776 1250 864127526 864127541
    0x901170f0a0c03020d08070204090c0801060602070b09060f090306010e0405010b0f010806010804050f0f0a0c08030702101d1005130f0506091908010203040503070302010b0402040e01091e020307090306 88
    0x400500071800c941d45894001c00154070029004158000c03000040041005c11950310030f038010010407174a10103042801c3c0041d000d00804500b0f40c40c4c054042041400000c04108480b030441d0902d140201142c2406410780040128036140751041c0815002940c0a120540c0a02400c0038031091030b1826003085429103900c0034501380209902c03054081c1e1640c0c803c07040c5904c40401c1c2444500d0703031654a00715203413401002000403240220140900c001ea40484c0030015580242c0c1c52402c00780d22111042e40b40d10440c0740007903009010301c0d407120840e401a00013642d03400b030004040d140101213601141429440964980000f807000a4140c2d002201c0403d44000d48800000382d4035860030304001c24032522442e1000c910807440310050f0800031140002040141c40b03c00d000390744a00700341c0b611030381c0c13504034100032809035083c500c2110030350900e4401d403021504180e9001e412030b4600b81003040101109003420b07c2100d000e020b00d440c510520b000450013080c266503134408144c99810944201ca402c0d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 864130026 1250 864128776 864128803
    0xd030b012a02010c060f090218090606091306050f01241d0d0c06051b0c010e060c0109050d0801091401030b07050307110a060507030e0a03210b090117 66
    0xc0c03100740d041c0d2810301c10210114203000501404a0001400103850210410500400e40c1c0d04020604145000c5a0820003c8078402e071004a0000140381c26400040e00403583c0c940d0035070190300054414503003540d6030b81e005176255a43c4080840942c542c001658821103482d204c82c4a41401003040304044001100100c41c0303007103c016892006800140240a0100d440e0504540b044e140e030590741e0307419541e07441540d00c0040b0000d1a42e8034400680341fa00181c52164081c4c42001800350a00b401003090f143c8000d0503075032148405100e03010402e07030b60000c4107451550b641c0d9641450000b03804008a000b0303400251a0138000e9803510700e140c002d8808a003481c0c946080c010004100007420003220903040401350501603241c4c0d880340f40445506000c50b0030b0740310510a1300c017020288103895010602911866800344100e00003441075a42e2002c003844020001030500215038460680381c030201c00c401e10308482c00301c2d6864000c40012151502a04140c3c249202051502c800110401c1314546050300b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 864131276 1250 864130026 864130037
    0x1b0d080f07051f0b0d0b07030b060412020108060307062a080a030b040b0d08270616051902100f02011e0f1410030807020f060309060709050901151209080c0d030b01 72
    0x201c41000c919190300854006151501300d00201f180c07203010b03800c2000115000b409640d00d580e5183c02c0c01c0305007040100e040c2d010600d84004500981000300c2d0302000d41e540e035180c2e160301c00d0401e50042400500c003e00f07520000144074002000920110082c10500001e903030105403840b2000c108012611005a07441c800c6070f00c0d03209440061086015a01d02c003070448040206051007a0010038026000c5001e80c0d404100002c020036662509010045400c4c01801224050b8905150101c5006004030020f5809a01c1090b484c00003885415904400b00703c2c1d10000c0754003540301d10319910703142003106290f00c0162100100d068502240c0303d96401d0010000d1500d0705d40c00c00041030340d41201c2c18080070344480c84c002810802d644401c0682681000050413681d581e00e0405046e644903e01a0f80150016420101c00074540c034096104d18161a492010500341c0d2883c500160350260100b411000d000d912640007001003130f41e04014001c3c004185002c2c0801e16403500004040b503801940c2ca50602c203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 864132526 1250 864131276 864131291
    0xa0516122c0603060a0e040f03080a0b1c0f020a06200303010509011823090d020c060906130503062d09030406300c111b0d080f07051f 59
    0x260001d041c2054500282ca0540d544d40341d0030007140c4004803d03001580052a0702050004101d084c18015800074001d5803034160b103441d80362490040d206402c151580c01580541c0c40400030300c1c0400d20242980c40744c02c082828100a90104014102d80d601101c041031074092609990045064414030300812080950304d1581001c0015031000b2040c05003a0548a02c1025208410b01c154851400105007000703514445001c1d50210f0b400c0401240c080b19035000d0b0700e108200486c00001c1031441410002c14403401c110303100d414400160807010103051274020039400050303141c03008d0003003500402e00900f001a5000207d000700c00b07151000300c09141c03c0c03001e1500f0410315103000700aa809035995443d1403c001a540c0300502d5005040d03e6107001a0b003481070302480600b5885d07002c4502d514076038407110700f810b1001c17162035141c3d4545804440c03201030f10110190325150010300714031018452130f005400c1040d00003458401d5080500112401d0b400344400d440042d0302e5440004002c60140003d00800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 864133776 1250 864132526 864132587
    0x51902041d0414011118190902371b03120f0b130b0901050f010801091512050a030e0901031211070b0703020a0213020906030c0a051612 60
    0x41d03940066401d1020340808141007146540c56400382402d1400203100101202c2100c014030350203100703040345d9188080109031081c01c2c40c01c200d40128001c006c5444c580c03440d00702e0040184d8480d0101002c8140802e51552405003555a021140190110307040000b88405030301030300c0310403000c00703d120030305061103540000303540481a0a076101c001040418200d8103c1c262001030407001d0305180e0300000c5200040e0340442154007424201c18100c1d032003c5540da80d00248486803c600091a002480070f1005004403205038010440840380c0c96240c104003a65040440a5607003084811162070b002940600c061613440403099140b0141201c005a055145a4035803103070200d24846581400344a441c0c083c44000c0521200d4010301030481d417550b943d030703062400a44400c41d40c1d44c22840341260b00440c0321406140e2090710207580018007104d00c0c0d074031203140350005500000203003401c020082007940070b04109084000035042c0b080c10840c3c1d44440c610005410074104844083c0d04100203028002c62 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 864135026 1250 864133776 864133799
    0x11a040605031f180b1603020c0d18031e051002041211030114092d0706110c0d0b0108063904090204030b100f060e0603070309050d0305190204 63
    0x103803501503c0703282c1455405440c1001914588481e502500042c00d803401c103101c01d81c1c41040c03003126824a000482e0340d10302c605034103e000e203a06204183d0303c030030b6061a046024000d101c138512001c111241c0d81d5a0703243d4501a031902204c1d512404d8104072460b45003007181c2002111118003030000d065003800e04216407940031502c0142c024242414040708028591429401180085a02d40400751a441c000304400e540d410704015000c01051241c040c1402c4201aa85040c104001c2001400040349400301c00c6030050400c10318100d0602948004214903929018100c0100340310780c110b42c1c52585440d00003030600500030000303581c548008490640200842c500d880e0b200480c01c1c031420410000c0c3c580f04003a030040e0b81041450a10000d0080240040d82e0b44203481440d580d80d06841c5d50f9100c20b0184a00300840c400d410106000400f400700925014001c1d650000d272628000a070308045489251800400c0e0710080c001c640d4070310070720201c103042c1c099107881c42640c00b0040d032074180b8011200b910b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 864136276 1250 864135026 864135043
    0x1e06110c0f0409142a150a1101181e0b0c031801020705101d030324310b060d0e030f0d1e0603050607030905030903030408011a04060503 60
    0x108601d148010a02076845602c881e0b5025044a1081c6039103c00007103459599000d4881401e00320b40c00c103002c0d02c204c4107040c5a181400130140c54603082c0716100e400f01e0f44607005007150b02c0c18050000c12500380c804091081c505801c50300303907001d15010003500740701800c2d4001c15142070803000790b001c0000200d0240301240f07800ca403649401c00d60341d640f1808560381e00550800310100c076500000c1d180080c0800043e4400c00b8a500700000c0081461514429800b07090540f00a10300d90028070000308140c41082c00b01c07081c1100c455100010b194500000342d2075080b11030412400040c19528000c00641c80c421f00f0160700da624400300711414900d0002400341c012140202c141c0d54442c20024001201402138170000f00c220018644c03211030744614407018003c3d01e25a0808a04010708003d9050f0303860140004807070b040400b8101c0c94a4100d0100c0107020480015030f000c0c801045420801e0710200024802846500000a0b1750103403c1d82e50348005000c555880d11603810b0403018031a646c2d003c00c0d0345a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 864137526 1250 864136276 864136279
    0x6050a0804020d02061317010e0102030402090408030403210509010609050705040902070206071406010806061503060d020a0b0a12060510020322080d0e28060f050c01061e06110c 78
    0x240300b800f4501c00502ea6101e0522406040710906038005042c0e8481e8543e110190500c500038031046d50b41c200f0032400c034002200c001e54881c0030350b008907021509040085411a00900c2c050307081e41c144040030b03009040505441c00135507507114100b260a000c01e11400d0040c180094040c881402d040b038000b031050280d8001c1c000c82650001e118401c540c0c0d80d8040361140f0764001d880020395640c0350300c0a40c480741c0c244100780240c000c01d0000313050340c07500b40c4841d2500b06800c550541141c55041c180b10901b041d10408036046021076401181c1e0095450140041c0c1020340c4e200c162003903c10340c40c801552100d920181c080c182501d54816025000b0080c3c41008030700201c0c4032040716032154100404c0440b80d1010140b80160f1141c0700d030309035028000b0b5420000650300c0d4250b000303402c00b13061a0300741c02905580c0c065800c3c50091041e03038440c0d11400b103840c01610300b060425003801c60a138211006035210444040242c00300801c1c440c2c400a000c40180b1403410184c110b03400120340152603001c03007460707035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 864138776 1250 864137526 864137539
    0x8090f030d0906110c130603331d011506030b010c020306070e0102032206080601052107050906031609150e0418050613030801050402090d02090702071505031006050a080402 76
    0x484c5040f1040207880303004540248040302a01384100220028806d5003c00e03584091049101000c14507c0c43c110300b103030b9880600f0400b40d9a0b1701c40000380240301e462040b180c0b038a4041a2402040002d008110a104040c080064460714007140230302200e5010352981d060002c18450203015070b50104a440e800031907401d100b16402c1e24400103c1c2144940d004c4102421080d1080c520600d0690281a0a503242501e9801003a26a0001581c06004c0c00141c01c1140c2d001e0310600c2c002c0f0010f030110359040702190818602706101d090000c4d0940d0401c484a2081790300620002c1e070340301d902841d0300d0300808580704c1c008041303940f482004002503c0c5038500c9015030b0701c7d040441d51254510310a090507640020a6039100e00b03000f00166012554040141c0000e060302002150780e180500c01c4070100310b002414400281110f500740611080000c100c4015402030a00000d507503040001817204a41c0301d907840320358a141403003803142c1c180c65540200702005024085034000d00d42103215141c000d034046807403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 864140026 1250 864138776 864138797
    0x1f121e02040e12030103050d05160f0203030f0408031e03160f1803060b0108010501020c0a0329070918050411011116080703050f0d0806121908090f030d0906 69
    0x4107001d0400000210001d1040e09201d446481c019800341d81640d100740c00f961804400c01000311040c1c0100c2001760180110034030400005800f090307125007910310180c15a8142a00e80c51281c041e50000d41c0007400710b400015425100800313840544910b4803191f4042401c41c102041e0306200b100c01d07800c0f90414000c04d0205081c155006944003400179168140c25441c0a03100d14191000d00030040314240030500100000c10b0700e60020481184401e00a0124040e00d455a00e5422000c929200a56881741003615082214605a50010301c00c81d036070f80b6404011480c1120a0300c840320303109140318000d490310042c04006011107450401540f824640114000c0326000700c00e09100081034455a42c0ea001500000d2015002c01c2d04011071703020f0302c04c0c0c40115000c00e5115440300110541c0034001804040090031034030300108000d4107603000504451707950761164980074454125800039038501c08082140010351502d10280d81500f0010b802801e907410140d17102a0000826014401c1489940101d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 864141276 1250 864140026 864140029
    0x12021305240703030f0c02073006020703080403260a091e06051605180108070c050a03030506040e032a011503080405010f090b030c0f121f121e02 64
    0x4414070611160504680ea11100d10300500104968513170000709600300700008a40c1c50010070600116010030301411280700ba00000049050314051209108990051111010131020b2010780303202c51003074580302024101420050b0203a00c403018501010f0507000064040201d401503150b81002c07080c50003090600d03c901d840c010f04243c0f81046804031101142c01c1d8140300c0b0a810442c00341e90790090302409804944001c6a052007000c11041a540c1040c201c0f1523694811102158003406503d00000d4010580d0350f142c0c100000032009400203511a014001d0b2441c0138401e00784481d03140d2008510f0320b440c10842c080300c8034000700c0034071900842d00c0304000030203000e42004c1e00c44212204507502003522480c201d8840c0e085070055900145000702c07110b50b05030268074444c069038207030001c41e81141e07513098a4010700d0f0700c554805080c1402c140030b00744240d010000054040d07005207440351024081d0406c07401d0645201d03400016240c501d0038400c0042680064410050040780814040c090083d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 864142526 1250 864141276 864141319
    0x1080c04050a061d070e010e1e03120307090603061502100b01031d0714030606280b0a11010f1e05270d08070201050606040b1308030a090612021305 65
    0x2031042602d903501c4840a18040c04011000d84217000a8481d0300302c03103840c01d00440d0001401c0d0340d0250000c12081d00b001c090703040d164101c514200d0040894800d0308000075a80711a40064982c40089000b102082c001c19406003d481e001d01080c924640c031814a040c8002d581d149440c0d03145140e80d5541a4144242c0d11a800613101408074001034448540c17038088169848070203105980f44403010200491007481c010400350b001c2c46000708807610461104001a074218040b9041d0100b82440c100b0000702040180094030700100035445515402288040d03c40c29a40841801c0c91035038074010780030b03030040d00c0e5082c4620000c40c50080042d040c0d881580142c04000a501c07a0640b82d00141060450b0910000e1582450289683e0340095508c0e541e80aa0a80d8025030b4060317400310301030000b40548074901010346404043c00c0e20105000b55521103480c11a80200100f02c00581d180740c0c18080c207600324951480724100560f0861a1240040d00400c0005141c011240300b442202c000584501d0500b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 864143776 1250 864142526 864142529
    0xc0705220519020c030a0207140a0e0a0e01060909150c1b0602040806040b0105010909020403020a050108270c10020619180602121608091c1103040e0f0c0301080c04050a06 75
    0x2c500c11940d401caa00499a940c0d04134070660801449100e0380840e035070010200904074100050100c84405040100f4420700d40b00052000d01c8003540c50300c81229142c030900401c001484041000a0459214240f469a0400080c61410b0107410080713040c1c030040c0c1c04400002c0031314042855a805440d5842e044d400b178440e5505c1003459104480a00c414084c40c8660a03040740d8098a845958560701d03032140081c0c0c0039601c00030b940403552003010880c07540103803a1594840180f01d00c00f610b00c5519200030305070502a60b6402182c7d0b020b141044041c0c1000800d100d083d48041c0028811807601d0305e24051600b1444a0b9040c5154071414006040005d51605405540d8088410b5495154488a01c400b01d101100d0159801c0901c078440b1456500840e1030a0290203440c000d403807414044c4088000c2036a6940224040000003c0c43c07101c023100900c00b60003d13007006940c000440c205110f199607080406030016618080c100010031980400041003e0f044105880c00301d1181d07104042d0a0041c601d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 864145026 1250 864143776 864143821
    0xa091505130b010207120f02010309060b0603090606100c0209040f0311151015080708090f0708030d06050a0f060f02150a0f05090c0f040905071a0c07052205 69
    0xe8a2202070900900d030003142c0102801c0c0c3c00c8a01240c0da9041d0038035200385e8200c001d0441840c0c04041e6015510903042407000d80d000e076401041071010040807e5103503104403014120740d0000310500049140690f40141e047c05240b50a008090064000071039415000e400204140e00d001d03032540401d800703049446501c4101005440c00c1d05082c07010520851400c44e00000002000074020641041c081d0b6075003c604419a120003590f500c0302030948030b114001e00046490303c20b1007104842a4000c100d9000507202040103141c4820010001d0000d031034440c0c100d5440303001807120030b00442c00010100001c0710310074544082e62000b0401c05a050001c030b20b8081d40d000c0d10900400c41c41e00c0d2070b904104964581d15904001d0790b59100c0d01551100e90510880768132001a202c6c01c500303450a80c00280580b4010016034003039665401c01e0b09840c0034800d56280441c500400c410381ca0346030a1000000500060b5000f050301d840050140450801c0d542000242d0790b61036021502c09500ba5040c1c2000b69007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 864146276 1250 864145026 864145039
    0x30a0305090a0c0e01080c15090f1201020310060e030106050303091e04050c04061701141009080102121801110702040e1e100e07050307030b040503130f0e01050f0a091505 75
    0x1124010138002c00c5090282040ba0300c5400d499100178284413400306035068294039154100300c0e181041103130f50100d128645134015403842c87d540d0009000e1000f54001c2042c0020382016a01d80b56000e0f01d03e245190816100f80d15000041216031800b008807408950101c4e03095040c3c0c0e007280f800340c8010221002142c1c01030320b0201004910b90130300008206a4040d0307150b0a1140f003007d41005101a024040c2d03003404002c11480c440c15050511034044065003a00f000d009094641003200d0032a0400814040503036201c106111506452001000d6a80c00c610000d1001c0702400311500014403c50100a004a680c0c0e00c4852106005216a41c00d291003020103210500c0c0c43e04e00c0381c1d55918003a09242445192a098680b6074500080c40012a80d0280140400320303c1c54071a0500c1c41d1004200344c070140000c10400f103008001d45008406007403001d1006842c1401d040c100f8a6a8030160080303030243d101850800d801d07986981701c12003121504140800c04a03000754445000c0400c0781e000c16003044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 864147526 1250 864146276 864146279
    0x402151c020304060e0d09051215160905010c0506040206030a060308160606140d120e13021201060306030f0f1e230a02061806070804081b0909030a0305090a0c 70
    0x4a80341c00850081e030007140188203100030304200c01d480300c80044140002c15000e4004009505140c00303403072440302c4d80c0d40c20b851900c4c100000700b941c501400c680c038404020314050340126464200a084c00601020301e0316500815003641c909a86034005803006e4410103011000906441e0580c01003406150b02120098440c2000d490310407101440360f1080300c0c0e050404102042c0032000652901543c04e00400c18884040d00b5150b400c013800300f0b80d84d000c04008050b81e40400326103a1168401a02110b1a00181d5a80001a6584141c40d040e00b01d5410142024010400708000031080400584c00c87c140400002403450701e00707400352a03070501c030202c60f0066002c201070015071900008403c02c076101c0c0c44101c0b244100c03000e48400c05050300940c0000240844031820400b8100082e4035080039180d24608000c58590031120340003688180450342c81108291000c0c0c032103010f178100c44402a1801c02103814164012901d074003481040504040d650800507a501c44100580090150040340c032400c4103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 864148776 1250 864147526 864147577
    0x301142b0b09030313061a0315010303140307050a050c010b03010518160608181603060f0b040605010905060901030b0d0812180a030c080702040e07080d0c0506040215 73
    0x4100c040301900c0e811072550005081a1010040320b1003840407481c07074112421190303241e20007010981041e41c400b8941105042d19514100a40c0d0105190011076180561440c82c00600e80180015030601c4000140706010a030b03a0804181d41c0c4c0c2c0d4a039030400e40e40f1003800b62907990044c42914900383d815801d01e03082c0b00f0072420180c5010a01e0056a040d02c1d0715500310700d10002860110b2048100246040340010006409285688001030828095a844002c08050000d007e5050780041e159581e071901d6100441d4020b105500e01d07594159402e011161409c0006026a07245100d0b26005100000b03100029a1095000c0310030319000411110170040c007030803e100c0c0d03a008103000031184041c2c580030641440e1910428008108000010090728940eaa02210700303030202d110840d1040303030900030403005036a1802404101c84000c1c0c018003049140c05003032807400f14000d00b69006c0c401d89600610124802041007540107406950109000b210000d00e01d5040c0b2540c20100e4854610310060080b4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 864150026 1250 864148776 864148849
    0xb04020609062106031501050604260f06060f01031817040b0f090117010b040909140d0305070201060b040e01030b060a120c0503060109020421050c060c1e03030705030114 75
    0x1140c080c5c1c1112404c1d0804a61440b900d0800e0140d140c1c400c03801e02c002c12444100002420454122200b0314008004d000d50152501001c0320144061340c019004014903403c2403180828440400d10f000d01103507402c1e58420003405403219002d0304074000c140c1e07448000b40001d4110340081a100c070030036a1359003030301e58003240e103030080e0040d04e002070f414045d500000c81980301e01906071078480408a181a2404548000800c1d140c90211407050501290084e0741c00180007480c5d07000f165803004140391070620802802c442458200f5101c500e000e02045c07204a6654903180e0659a02914580d1907441c0d00000130840b854551000381c107050224060820030800d150114101c94007075086505030b90b00c4000640990095005030702d0340762270780900c00600d00d415101107034207540180103480182544502240452b4408000000030341d00204100304265486201f000c1c200e80204059070550422032002400c2d4803040c894076000700408040d00040360355a08145d8400140382180011039040351512102 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 864151276 1250 864150026 864150031
    0x316030204050a150909020a0f0b0315010f023a1106240121020f0c0606040213232e0f02030a051303050607050c0d020304030b040206090621 62
    0xc0c900704008a039090025010750b00b0b07a80704030200344542c5170601003084004c0ca03050700b040c2c0e44035540303000000e21640040000c01c00340c128240c01d0b50307891a042d80d0001c054022203041d00c8c100000341c400e19a01c0395001c90300d05030a4455462203407580300340d070414015140a05210400783d0703138005001c10300141c1200c2001801c1c1125002e65800d030307490b10703284c1c0440c4030010b042c40500c2e89555400080c961044160510320300300b000e100034603022942c15050490b0000c0b0040c81d070000c0001050011a03a04101050344100215015884c0ca00360300030900a00603144141e248134085c800080b00002c80325281d0020703804c8050030304206082000701d240101030010078a10b030740082d038403120104a0721a1768540380300b201d03a030021450024000310440d016031140403514102c180748400840007400a205032402181241c1d0345940b1540540060f6003003e076200c1000c2c044d50700410082000568100c541c541c06901120b51a84681c4e800000c643d00f17119004050701c044051034469400c80b20a00300503030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 864152526 1250 864151276 864151279
    0x9060403170a090f0f060c03050c06011e050d1509081e180603060d140115080105011d1006080c09040c0c0c050301060b04091802130203010303030b0a03030c02010c1103160302 77
    0x10f2080d81ca003111002c1c0710480c007400c9a40c2d116103901380070302d0340604009581c0c68400c1c030b042032425544c84091802c140007a00880c880d2481243d05102c0c0840c5046424050032089684c45910000c581d0340c03001003159407104007600ca03223030041c0c4010700c41e28200303a401c1800503074030080030710308541440100c90b4452480341000b0b4a100d501441142002e00550b0b1040d800a0803054116025880d1041050740407250f1021540d25124250008002c4980c3e200040912100204455040c609850503480001c4102c1c0d6941001604000004071064010750440f01079007428801a03d40c650544654458174144e15001030030140a80703541c0d5880941610342c1e038042c0c540e40e4100d948035400c2600f81c9480f0700c50084503400500040c0042d10070b591000504030000c860b001c92924890b4045540556501800900340e54044010020b15415001e100b01d40700d0100e8030a8602819590007030044900c1d03950190401c17503450498030401032248808070220000030111510790308c1c000015a5150510b01089 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 864153776 1250 864152526 864152537
    0xf1602010c291003052508030f0c010e0309010203120c0702040e0d020c01080601020c190f24050f070318090219020c1f300b030c030a08090609060403170a 68
    0x1030980e40244000e000b603d600c000a8031b640a407018902103541c030350040407402c120446a000800302000c00007071042007003103c070141e00c421030401c0c030900311244030000084a4208120121060707034040100d0c0c1c05805004a52074103502e480358604898052554025002803400c01055a00440094420785505803075089a03618000080115000302043d5442400349e404220351801ca490080c840b445001c01d030010701031506a881c040705c5608800c69020565844007403c925000da403100007902c130142d20505041d460041103042c03144491144078006020400c06400e403800b502e00000d9024000d20754008190f480710a0b0082e0754524040000c1090094420103110381000c0c1445800504c0140c021501059007a011150560305440460400d44c8800048001c40c007103d0b108001c10b40e48140101c40008041d502642032501c0c02d800300c403110344242d01201e1a440042e01c19400c551051105a403600d896803211400f0030064080da0b0001001307610280c030500c1d60019001c014110034011640c03503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 864155026 1250 864153776 864153781
    0x3111309050618060f01120515150c030a05030c0d150810060b0f09030a0803071e021615021519050105060c0d0804021f0e0301110f1602010c29 63
    0x10440e41520448550003800d0350385000504c00d19141150105101043c1403403104541868040b41c2261012103110580c48414618946241030540303140050402c407070300c0140f0381443c11140c06d543e8012200284104180080003446240c07904058a01c1d1240c0c0c0741082c8034851031000040d400190034000e080c0c00c0d20811001d00e4218210780501c404840c80307006028038007408500314800a0380314190407038042c071844040c0c0c00003500d1080210703c50106541c860380a00c6000b66000d00e5a41001c9503072007150302c00c4402c032088a03042e1b2058000c030f0380203208924070f290511005904100d4074516079031400940c803042002107101e5130024402421140d504010a03a240c00c00c224813402501c164001f5079101c00d00840c015406529496000741c00101540c82280341900407425140254070720300001250100d000c05641000d010721858035032003864080c107014421603545003074000d102d1142d904025401c2543d055902a200341c4060b00d0700582410410303042d0003e02c83c0c007000840210107141a50200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 864156276 1250 864155026 864155029
    0x30b19180f060f0b0f09060d020d06230c0d05091606020106150c0807060528090b07020714210706021c09050d06091103031b0f0105060a1203031113090506 68
    0x4c40e00d01c180e00800552540d09084240b1409031300041500b40c204404204281c00b603651240e50811441c170a0710080741c1d1401790a140b03a40ba503d0340c0c00d140c0700c0d10701140501c0b49180c0c08009403119004207480c0002d5995038003641d01e190100344009410400c0c20042c001c1681395064000c0030903150a406003c0200c0065501210511850140900444814400c8800003030031a04829040f220159010452912020754070001c40c610844600768503603510942d03010011762010650b480b05050000d04009441c00c0b070180c10101340f04c510765100c3c5450f00f0b504030030701704a120300714440c031981002c94101076141d90001c0c0d03850860032032451848a00740ac06964040c424035080c01a00d0000d0024440003e0a544202c090102142e0454400c81501200c11950b1810405014416200d003803c088244c2140c60090402c1c4402d00c0b50920b6034113043c1003103100d441c0d652021044907104009030700c01d40d000381402c03001003110610380c0080e8000010448012180700070610180d641001c4100580c0c1c468a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 864157526 1250 864156276 864156281
    0x9170304260604140a08040e070e0f0307050607060e430b0a02100c0509130e0c01050c10180201120e0a0312090606120b09030301030b19180f060f 64
    0x560260360740c2c405400900018400a0301c100d1a5a150003203e440490540e81c026142d0020307000800e5002c54a010009042ea01211204c2c0c0000140c44152541703e001c00402e071180c9407402518014100003074101c2c01c01a082e84501d03102150801560803100106800103c04141861100165020081d4110f01e1a2040c5c0d81014004403030036010400518004500986400c861080d100b90300415905c80780c0052280510b007031440c41903440940d540014401c100380c0311428042d00d941d29150820340c4031502e10025400d440c80d44242049621800300300f269a1a00c40c02c008000ca1a03400c5c10308408030009065041042141300b40c9600c10385894840788030088507421202d020042d845013100c1008680a4620103d140010260100300080c2540351003040d50000d070300c1241540c1040001006001d405101281c203d080900907520703552650f2540790b220500644400e034480d559030500805244540c2c4440c140a10084550001c8483c90500c100c04c1c07200e444044c0e130400d08141e52220180d5152 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 864158776 1250 864157526 864157589
    0x914030a0f140c030a08010801150f03060b0d0f0f0303140403080f0a020d0e06090c0102240a14010801092d030c050705030a050f07060c03090b0a09170304 68
    0x40da210901c0000c0300e0811107031140c2a80c014210740c4420020222000000c0c0001c08040906403600b0059500d0038840c5400c464003a807480d52051490743c028810201c0300e89144003102d400150101d00079040100013a06004c05080040006440340c0c00001003100b8001704105050103610104400c60440c1141c0f01002c1c0d0803200100011009000510800c0440361240e8012112050050925401d80d0980049440d10010458541d00800030030440140070030bc2815955400e20144c81c640c68004c0712494880070a840d0071640e02c0c5034000007042c07034216903c95884c4100000000c01d16503515055a802401241c4040d55003080c0340303d40c801c030704650380311402140d1003e145207804036085840450304d003013440c8400c03551401014030018031a5030400040241e24041c0019280410f1405040740c9444581d9011205114040c030707071800402d4010300300104403146070503640c0e03072140e00b0399089a4044103604008054030303a841603808031900c00000b42041d580710341d04100c500c60714400d100ba104910f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 864160026 1250 864158776 864158797
    0x819061404020a0e0405100507020c13020c0304060507080706050703020a030b03060907060e060c060f01050108011502191a0103030503150d020609010c171c1a0310021c0f091403 78
    0x101c00c1e003002807a20340e0365843e501901600650701c25111f0b050000c01a508141c551500503032185803600e00920346441483c51180031418214500002c030ba56564890180313100d00b1013400710104000090284c90001c840349940d00240411007444c01120143c000e402c2070003017000003850111600341c0c40c01e00240282c000c10214006040207458018200c40d50b01c0000b00d03032500b000007031011003d01003042000038041d4000d280c60b14a1507051200041481e44164001241b041c0700340d21a10302c154010a030000a660012069600c40760306041600350300d82c910000070300c5080b42e0300000062640c448007843c002c803030b03d07030040d1295030004003002182c40052074007a501003020840e84100b9030107a4440166a88202c001040780c14069000070701c140c000d0141e060400120a02c1c2c0e18026005208651400c24402410341c0c0742d04544000c00c0c0d480000014a002d1a6400914070804c08a403501d040c00c4d42d1402c1200b8000d555040000c0b401400e150a002c41d820310152200854101000c0151f642101d070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 864161276 1250 864160026 864160039
    0xc0f040807210507031b080a0b070f0f0c0f02010c15240807050d240f0f0908030a0908090411091302040302180a0b041107030e01020c06041806081906140402 69
    0x5d44d1200d00c0c0c0f4180754085005408192080064540001d0090400c424041c580e420044d20f0290006401ca24404200e1000c00410940c0c500d1201e810080240a01e40c001e260220a08010b200603100c5103d403880180150210000070300c0b0b2074405400c100c54038003246911040482c40004054510000e03800b40c0005500020307014441030510b8520004018020f50741c05541443d0a180c41c061200101d0010755101d4480c800036180007100d0280ca40f600910711410050f20003680c880080c2400083c1c80c0d04400c41e1102841000d10499000f40c9440340c4005004206841000c500350b91154011000c06015940411482300700000910980d01107070b070042c18180074840e54410343e04441c1802041d5510182d6541c0b0100240e4907107200e00d480100c02c00c0d45c8240d0b202c801c1d05025181da034410804c0750456121500b06e0105494800c10b131340c2181c0c0c2d40c0880107164020b503c070382d0002d0015500b09407030501c60034084d05981c031045c1542d110074900a1a08104910a020343c4064901088802942028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 864162526 1250 864161276 864161279
    0x121c12090b0411092703090619030b030a020105030402010302180307080f15011202121507080103021201113406060303080703091101080c1e09010e01030509060105090c0f040807210507 81
    0x7000134041411040d244401c3d80c0c901364081c00001c400d904031040e5127000e5420781004030446c6405200345411350300214010012100c695000a00501c40288000d040607004030364601c24a0922240c0d4a440b80f00409548209484405266658443c648a82c446100c0d41c04007848600e600c2207000e044c0da21032402000746114603000e100380303840101d0305502d032445007844148a144800031021300482e02c960b03411030554590700410140840340b0b05690328691514030b04000f030380003041c2280c03031807900c64120301445d441000c0c9043d95400c0100304040200d5008031580100000359120100b56482501d81071000e48803220110121581c00d0001004e2084004180759150b01503e001c41e0f0141200108500e80b10765a040d00b00241d40709491500005d0000c0340310043c0f580c01c90030303030b903035840082c40c0c1000245071140c81c241e51820181714a6001b9030f541400300306003941d15821142404d80c88124517a45642d00c101c02e82c0d4a4040380b181c001c20280101201c00802e107a08110101c86821400406001d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 864163776 1250 864162526 864162571
    0x1f050108070614040812041d070207061119110a060819110910120b03030f18060f0c150114031c050d060e040c05121c12090b041109 58
    0x42c001c103d2101d01e50005000c0001c8104041103d0615802e404048a48451400802004030b10300e02441a2020301300800300318519130300185480072103001d860b001d05a01845400c0350304008071214920b03100c4034080303030080c244a00882c5140b0100b10940e134490341079907a0001107900800a807285034180f00c40c400942001440e541100c0844248120f16a03c1d0422480005080e031407516440c0b00462460902081c01c4503051003600d201000550245250802c03113040b0306903030310a040f01c070b0071516940380b80a1641d031941c1080e50120809854095500d00603d0251a40c0c1e00740c010b4081d04000040001040c0042030084a1101d403901600804d03150003610880c8241c00d20868032101008010b000030b50310300c1c449008038001400c91101c1c0301c0c001e0a00f403d00519507511500000d009a2144e4143c0e111032000045031900040603030826002d0302000c481c100c402540a400c0f248906040440c0c41e414010803d403418001c81c40745108514484c5001c00f0f110121004079500070030035040214200e0388 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 864165026 1250 864163776 864163787
    0x60c090102070f06081f05010c15020909010b130b0702010c0f020d08032703070309030816080d0c020c030f0304150905031209031603081c0b040501081f0501080706 72
    0x4800500544030003546442c0500100c0c0c240c0e44c001c07000110845c3c00c3c40140200b40c0a450161a21503070f24002d40c4d030400c40041c04080062500034420307040010a600142d0040e0705031058540d0081407500156550307041d14240c0d401003000200100603056000460301061000c482c20154107031075040c04d05e01d41da00d4000220343c2285060745c20099580485000030341007030086d03201d140030b408d500088141040010598040c15061949039074410003c003404a9041901c0a049940c0b04031501d03651303810f2042a5640c285004001401c99001040c2d01c464003029400c084d18591031682211b4000c084001090740d075481980d03060380e15400400041c03294000c2c142c40040e15141504040d4507103030340c490101c0d140c0f0521621011503000302041200c020303e0240309500315480c0c04640064140d0464450801900c140e100c8403030ba50705110b003261208122a0407844202c00000c4c0104060360b944c51015484441da07412113020f007100780030812386105007445028181d8036000014040d0b203003415001e803078 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 864166276 1250 864165026 864165037
    0xd030507140703120221090d09050a050310051e090706030b030607090b0d0608030d0f06050105040308030c030709030f0f020306061207050d050102091e030c01051801140c070b040f0e0108060c 84
    0x10900c81c0f0078413080c0040c0501070340901841210000300b030140323404030000b4441c00e2181c0015105998040d0200100d0750300041741d0201000f281c3c03002821b03807503440701c20701c44010079030064459480c81c0307041000c0c1758008a80c01c0200c810548043c09042c000300c04060301e5000803500d040124183e0f1209018200b200809041c501007012000901c49444d000031601c1c581142c4000e07011543c64080c5200103201c14011040108007e0034010308290840c0d0312184240070003088408000d0020002134540b0344200d0007800150b13040a14545d203011541408040c018060406a011340301c0c0b440031070864246111013950001b403c0e8060410541003104014001c031a20809a880b036409020031040c941e0351124142c64518601c038240a0610a44241800c1c0906401c0b1941031080902500c042600380c0c0c0d001c0806404e00f481e1249041c031414629440034002c14600b950b0074412941c000c1a440701901c014010341344240710000200c4d039210940c01c06070030309010703031000303a000311010542c3c210121010f0038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 864167526 1250 864166276 864166297
    0xa1101022e1109220f060e0414120307020102070501050c040b1615110417011406010806031509010f24180e0615091f260d0305071407031202 62
    0xd03d4000c0700e10008100341922220100100d0b0121031184466003d485100054010082c2c180980c0340340030000b0b0b4042c84014000f80482400703170412a147d41041c40700c449840c0702c0c600390071b4903070401e180001e000350420401125998a041c020680d01003480f020384045a90384d41580e40307072007100c00d03107920340c1d9058007800c440303040041e400c0e051000060b0080d801d4000c040e880d05602c540c5030021405040d84400c28100d4184d1508104860344c1e0700c0d403100164400b1080c01c180729036071141fa0119150030003013076240945041c683d00348018048103402070b512411110505100d8814207050308400300c0880d01c246500407565030010030020409580525480d2a8144005060904000607908000d8210b455014944402803409664078000039003680202107180e14030045c45191012110001090086185030044c0c4803d00c01400d160702100500340c1220b03402d80d8004581c1a80180251100303440510115482184a01808030080300303899a441d050f80d40c10016044030b001100003580314a0012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 864168776 1250 864167526 864167561
    0x120601090e070f0b0c0601150801030605180a05101d25031a070801140f130b18041712010905040309050301021218030f0301090509010e0a1101022e 65
    0x3e0101c0c075000c0d014010507404000c99030700c1401404081c1005c2c0140c2011900d0255038688220403544441c1d000c0c150b0741d200d040020203031101100d005400d01c034002100c0c0e9504c00ca0306444104400401c07858074440243c00d05000b0505080d021822102400440c40b207580c2c84081c01c4044011206c80c2e001c0503240301840412815181c2d1201e1440c0c8400020404200c1003a5007070002c042d03480008a401454001c212002c000f010701c1c00100b82c540000c01851107140100c1001421510340e90042c282c42c20004e104030700c1690289010b41171a0000c41c1c050720348248018a8041e4071000034102c8030220343c003258000751603080000070001031002800540170889282d0b00824251800d1004200344021248414011300e48850102c0040140c07090072a02d40d0010301c5040b01c1041d400083d2070544003440700210321a610b440b02e28bc010304481c030441c5050b10503612490280800000070700d01c0c100e0f00703909540c407a0204091050344d54140829501920b0011000703c0003465142e40044820080390009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 864170026 1250 864168776 864168779
    0x28123611060403080c0d030507020a020111120705011406010810030b1914100f053106060801080606030102161e0b10080f01060f03031407080301060e01030b120601090e07 75
    0x11507207a82094000300c540c00b000003004501c43c403040012140e1084146000d02223440d102e903001b5103810001d28000d041c00011448001200c1051101c201c61040c01c00c001900d40385581000d034042c081004400103851b0b170b42c0000c00c015511490003107100368101d246001030b145c699520141400e42c01003048800654152444c0c9407030041b8007071659007403601403907002c032814020b000f1308800360039030f00100020151078070402c800d40710840483c90084081d00001c039510ba82c0125801003003501c2181403070b164908800801d0a1307400c0080c8034140c0c1c52400898030540d44007001c2c0341c201c1c42500e4480094544101006000814905820344215003d20070028503000c0c070b41d01d995601c00280ca101c1e5821107a1401401a01d904100181540700000000d100c01071030140346580c8660f03280006010000384000004003c9207a0301120509070748690816525039440c4801081e0002506400b800a0b05121051400d850640300c0f50f40450f04c0d1030090071443c2d190504020040a09540205003030142c00030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 864171276 1250 864170026 864170029
    0x1a0901170114040305040e0601020a150c020106090f09120e0310020a050712030e0f0102040f0e04020303160c0f0909051b04090c1202010810120828123611 68
    0x101e07203010f148070740c860715104c0d4103160700600c820030010502c0381158080c440107808201c02c228100e10441da0150009500024104100d0141110307401c4800c8250074101c0c0760790624541c1d072000c5000c1d03002d002d40000c440305d501b1089440700722180d54298907030b200b060a0b03149042c90f980203008401716030074583d00e4800c0a031340e500004444460481c02182e540c6490807602d02061207480c240e601400700840c5094140b8140002c120400d01511211101c15400101151010000c8034140c0c0b4071071486000302c0d03800745031044e0b03100000d0146940301d0f02c20001c0047d1a103218040d000085a0080145c120f00241102e0015006503502d047c40d03009480c3e4642074017044c214910000644403501515100e12001e000140401c0c4001d04800c4204004d4075041020040e24002e030642c1c1c660042070f10707981d104500c0741080005620000b82140a80c4a0340429289401c02401c24003141c01c048d041c40b610350806001c00c0212114201220030480c181d4414016035149110706c24014410304110260808290 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 864172526 1250 864171276 864171311
    0xf06100614250312230c07080f030910060302060d05060a1a03091507080c0706060e0c03160f02030702011b0605070c0b06040c09120312020c01020901031a09011701 72
    0x52944802c807080da014034107160b8050101040b070031040b82d00344550030012045442e02d407907004003004113591100c0880c1081803400c0495000b00c0c0c203d03601c1d644681c000007481030164800da58081c0e55201e80120202012141d000d01f008981d0020801c40c1018100464800034000007451150710846031000490110206200401ca50440480085d201d00c1c00321255031914005040e01080f50004d08104082d030303644180c03003540c407120b955003854483d0241d2510301c014110342d40100001281c548208000114080c0145125940c150180b4100c40e0307a0f14401c2e243c0425000c480710050700b0400100015502903000b007104280d02d00c00c2800400d040342c4480d02200c0c5d0540f84a00040c800e02101c00600642500044d0003000c1210104803582c803117440075040007964820691001001c0400740c003410b004640c8104200d06401042d0340d80d61400ca6054001d50084440314086850000d00c06041540d00440754400c002c0036100714116401c0900c5541081015901c1e424190340b030340807201d056038204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 864173776 1250 864172526 864172567
    0x73c0201060306110c0a03050d090807031d040504110d15020708041a09090105040903230d060816031b1a04031509410d020f06100614 59
    0x6500000310203055140c014260b43c00039019681d00c0c182070200d00b00e4120b02081000806526003045a52400c40c1a001d101910900d00302810300c95010a800d0107050300700404a00700c0180101c001d031050000d0003000229a420ba40107002058a00380495035410100030b08126240101320340817083e4215403a29081e039003c40b004480049020030100060310001d03289940703000c0c844810504200301d4201040500e101481303254812a01c2d00b01040034180202a05001c4220250b0440024410300950040c075a012010000181d403411074006104c0c40c0100d180c1c41740000e59500455203500d10b40f50640000b0028403052264840d00b0b0303001852495a11a14080c1c9080b80003c58445186050651050002071140d034400742c104601803002a0701c04820407803040e90f994421400c07006101d50141241c2055008100020000a940f0f41040c0c0000309901007800a908844401b242c6296554840400703481d030003084d0002d01c0d001c0c08614007070100315100044c0c0111090403c216004004441040c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 864175026 1250 864173776 864173897
    0xc09040203010b250b060904060207020402070507061101020a0c020906030717071503020306030d140f0406021506010f0203032409040f05060919060e0f0f0f07080607 73
    0x181202d900c4024038012400c040010b41e55044c00310181c845400d9400f004011520a141c02400202088110b03815120480d8000d84110344400803442c181d542c0f06090302603000031480880019204520500072210701a003599184040c11081b9401c1c03129a840140c4034991600465101040c1e0700c0120031804042d00030503004111a43c9000c2841403403015054442c2c0405004004015a54500285240310743d080fa10f0092034034011013148035101e00410b018030b02030050010f80040d24682c00100c0c100000d0343c42c2020022034403680d00550b880c001e000107000244e042031000505520000c1d901d041c07200ca103000a60800740800c0c000804030001180c044500007000c8603e601403120801200364403e400c079004040085481c42c0140c4a107140c81002800b6030307220f1406580030b91042c00080c1c030300035101007200c1000010000b000d4440140c48410b54030741c1b1a4683c0050a05070000e04180507a4154030340040c00007034410040107050003c1c9004a203404403900c00000303007082c4002c18002190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 864176276 1250 864175026 864175049
    0xe03190b0403110115050f04060e090a020a050f0a0510030e07030f12080106020714030304031223031e071e09061b05030a1b0b010b07151401030b0c0904020301 70
    0xc140c600a007041520f2002011560b240154000c052403040b00703040b06032501111645d49282d4800c00140140400d6009484075a010a0030b0026400000642c0141280300320f409130289901c600034088045801103809511801da420104a00e080c861100740708008985004215810b20f0040e0702d1800c0c0c0740c0e42c01100d91802d1255140f043c00b4042c80182807030300f00d074601080706503d442c0740259500c210b0700800b01480c0c6240e4914800380c2d001c000f21801103a11a0f1542c04408401602428083c0002111085104406600d2400500041c1103c0c0b0072400c1500e41905103d51020380510b26400410000c203014082d1340703c144031707014802c900c424500a070f61105c103a84c0c14210005c20701d40901c01c40002c0140300070b1000001980c00300030380d140c0e00e101d40340050301c149140008003980070710281c000d480146450004150b40207240c0050115900a511709204006034511420480c1c12592904850102d01d10045c000121000151608482a41c611a04040740079000404aa00c20b034840d003007640 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 864177526 1250 864176276 864176281
    0x303080601051303080d0e0f010b0f0603090601032003010203191805072c04030207050906060403110f010e040f0b090f0c04090203191a240405010e03190b 68
    0x5920060a6510460070b20b410390400664203026403c4651a000050900381c01098044203a10668001140c6290000848103100c41406106000b028500d02e00c0d1f00602c80d00c04085c5403410040304490103040c90000034084d80c0c3c44c64443c14410195012644030790800c00001050f2a5001d00103035000c0c041400c580088030080d400200c0c1285c2804540d010055006c1030071101048020404030704503054064200c01e26020021000044030303500f01001d1107030044209100c04c0c1540010b0040641d0030945101000352189804c001c024042c91000400030840c94103040c40e43d041c1880340c0880054181840721404a050002509460f12140006811695820b04900c10302e00340c0076283d04090b004240030520b040600c15860188101d0103803464490300000460380040c4000e880c454201a800c42c00c210060022000408105841d10400d103d60101201c481a48403260780e80c1103450060085685480e150030015104200c062503039070b9241c0108405c4001b8541c00c0c0b043d0002c80b5210303400c9c004851 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 864178776 1250 864177526 864177533
    0x507060b060703050d320606090a0e0a0e011a04020d090605240a12140a02030a0b1806011809020d060f020c0f03030717270d0e0607020f0108060d0b04080403 69
    0x218400314041d505402d000b80e00c40d40c01b0614a080091784005c1801983d899a01d0001007040f0780304001865030031040d07100c800106484182096405800042c000b8016104c0e0040680c1c241c50000819aa50314030300c1d10707171000703900c0c2c95401418504816180410f40c10a00c2d260401150001c03500b01c00d1401c081180034090203038008082200c1c086c02c8998021302402d0120590003016400002010040144917410720b0210801007d11403950041c11211190301d140350003201d8000c107413080d0718040180810300e0340c04030010a00700c0c162000600700040c0075074021000c50291000e07580c2640c01000109144011844a02540501c04a078030b02c00f582d51215001c4040c50b05040c0804082560014000d0200356a846051001e070300d00004131f2244143c03210005038903c1c8a01d0112214400c0501d6001302e445400810590b9004110f40c540c8001080140c00b440b00134822201c000354081c0d01d088554034a50300a504c6542c01640c06040c040c030400c465030700d80e0384020054506680c0041d021a0070400c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 864180026 1250 864178776 864178781
    0x30f03133809040f09080a030207051c0c0b06030c030c06030a06050d0f020108060117161b060c090602121e04030c06050903010b0d050a0308040303110406030506090106090806070507060b060703050d 87
    0xd1042d135480c1000a84c00f80d8403081c2c040d0007003c12040805800240903030a2103020031448150617078003010814004d00d40100a003c81b150858111102c1010100140c0d240c40c5c0481c1e00f00511030080c018143e40380000003001402d0380300038118101c00b95a00401315994403440364040805100720f82a0070f00e140940009400d001c1e00034400d6040044902d0b20002c0a41714040310303504406200c481c120840c50051f415034011814203d1400e0b82c14990f18100305000d8681c0000300030b030203d43c450b40f51f05500d03200300702d88810000b1101078001d0300808c9180800c6800c00c002ca070340403400e60100760a19440ea40d07220011401ea60002000540c04136120f200340c6820310440d4629081200c10402500f643e40d01d140d2201e810701c402900780079504002805140c0603030420224001d010800ca85c0c0d6030380f5007902400810095802c4c80c020f0b2060300012601e540140c40013400d89140400410507540c42030411203540d445182d0031580552103105040003600d90901030070074184652585615848003d488404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 864181276 1250 864180026 864180041
    0x90c1502160b04080d050a0507080a05090415061d0a08072c1005061e0f070308060d030c0b04031817010e0703210c080315030f0313380904 61
    0x40e00700d8100810028440c0000740208540200d0406d00c2e25041480d900f601c15008411014240260005428154070742c04001000800e004a03020841006420030240c03624041d07000380c0340458010400c0d501224001140e1013080304000f002e4510583e1682800c508005156012000e10f00c0e070004450500c0c007484050110070740300c038030000d11645403440000c61039030003e10405001d000c0c0005c3c110758000f00c0c031054081174180705102035918404901881c4040c2c3c020303c1c00b039001400e401c000c6200c0346860701c200303144107405030b8540d2404a1700d41c48603204904080c1040b0705105020002407044c42036080f49000510f14100800500d24100302c01d1402e40c0d1002c80003941c0c6401458003403000400301048250103034052042c074003c200090100740c2c0e1091008401501c410404800c100c01d8801080499003582810b0b01070b914a98406584107a4a0144101c01e00501d50100414003003071a51020007d10000d1040c1e219186240d04405000c0645c0c01c0d1099100440c8001100146070900340038000b03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 864182526 1250 864181276 864181289
    0x70305070519030b09090c0102010b01210b0a090c03020316020a022b020315040c0e0f0402010e0f04090f0c0b13170f19060b090910090c150216 63
    0x11840c000ca0300401a1188052403a5665104070b9441d9a20748a5409201c0c1508081c0141c0010300708071030082d42c1c0c1c0c0240744029006608068068095520484546000d55501c09180008000b07514545001d4084001415000342512400148600c6540914200304400ea100142e69041c46400100410064a180c00565000e0500200141c880307e000c650f0691050415102c101c61100d02c52551401c01c4501940c1441503c90106d501101b00e00c82a01907445409503242060b0f0b1092140b171070700b20454210a86c14110000900594041c0d0034a80450070010162400ca000071070003d0308403155010191602d4403c00030b800d0403c100c010000e4080c0a50001260900400713a4101086070000d02032080c80e0b490308003030024213072420002507203200c003e40c054038080010189480064441c03a603096510703e040030b4076400305050603050907015000010141c007540440649610160000c140c4c1200e50409040300000e80e5202000038003006442c9070b01500c80c2c489801e100b50718449860b007150 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 864183776 1250 864182526 864182531
    0xc100501080637180305040905072118201008060a1e0b030106020f0d1d0405060a0902040603020403110906101103040902030a230103030206060d080403060c05120703 73
    0x1090040d4032400c0122400c030b545201840f0b012100000c0e00c01030100b07841c41d0802140c842e41134008264010020b00280c4c2d410220070030203603a600200321a00b8840d60100c03040c47c800c4c0384040c06494400d400008480d54810142e100c0390201c1d54404800c21203c1c06030304520100380180101a141400e0b541c1509102c2c3c0c50050510b051807000200385d031724907106046d42c00c9942103c50660a80c0d6051441c01000002e00094a941c4e650307101a403598401c49281c9403501500d08141c850b54000d00109901d01342080c10482c80551820611000380009012203030b05c100b401d040002c01799070074001003000c0e044030380c5d025858600c1c51030705600041030700800601c030702081c00801040b038486800d10202400d00d40b4084903032042d40d503541407d5103c0e0b900100c7d0618000001c0200700081078015a420170031102d0b11082a020740400e60305844000c1c0001001604601d0228549161500101003c90302a250311403034140c2d280d5510301205c2590b2101004600c0204100300c0f50032501c1402540400c0350700b8203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 864185026 1250 864183776 864183811
    0x2180103090b1314120c0f061b09060d0c09050a1403030a0c0314030403200303100902030910090b18030403081c0e010e0c1005090d11010201020c1005010806 69
    0x2c1a609440c01005035000600d590480c2c010301ca01c00000004a0100005950301d4107544460f90311103174068030a881031480746241d0110203d500103a07552061285049031200604020302d080525800055040c0e44020300b44078142031000c051140e001085502d84030b0b40d49440c500b0081c0070300d0458550000e03540e82441e50b400080da44010003104c40c40201403070b1000d07205c10310349070a5402c0000f1607010701c10020b0110400017010f420104c00101c010034192210800140c10103440d0760f900c411283c02c110314580d840700304a288266000303036801c11100410f5400b2200b40c0c42c075060880e06200002d03501d8507001000d10140c02e40c60010703c0c21422034280954a058110748a80d1594031a60140f44c1e19054107c41900540c107141e03000004138003604000740a034400c05804196107015540fa15031189032001102d80c461400f40b811a030340586d000d40749460001003504d4402c580c043c580e40e581d042d550200056a46120107010b841c04100c1108400581541400d02080c504940205252102d8040e0301c036 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 864186276 1250 864185026 864185033
    0x3091917061b130e0604020708031f1703070b0601020c030f01020910030c050708070c05101211042709050706050d0605010c03120e160801021b010c0f05071103100218010309 76
    0x703c18056561101090032a5150b139800708000303218458014013403a1010003881203000b114424805103002d10070040260b981c590704496200c010b0f030b02023a95981c0c0108440c000013542d44449607030200050040c0c40038800600701007400c05848400020183c4d40c0040d00148034544540103800d809458a010040c101c0c1c1c40318040d00f01c3c450040003801c151004203101d400c001000c48810003404000e40000d40c032030210700000d4039151080c0640d900d001d0034041c60005620707900d8107540407500c20b2105c0e8100741300340310400d18144600d03004420141d521400c4501c0411000c212400c028180c698660341c0e41c660040080d803c0f10100e401041c10440090000b40110b94070545450b01c0c0341207410001805110003500a00c1c007518007100d0000410b0001e80003424480640c007602085450b12403c0084c4002d071030702c19080711402591000800e080205001404c0d200d074028000942c80355840300703890390036400000c0c44c20780100c0a5034510f0350001500ce1003800041700e00010104203080074042d512881da03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 864187526 1250 864186276 864186307
    0x90f1205361e01080c030f04200a0b04061205040b0a0c0c051903180b090114120109021c06080a060213030b09070f0603141501050f031302101103091917061b 69
    0x4002804082c012040c10444190400f04150841c0d801490b2b161419510031408d4020b410510489001c600d08800200220301140119841250b12142d05840b039652050071a0050100312100d02c100580d40210000003201001024035290246812910f01c0d82d69180040c0305840e40c529602669210030b03010495401d200b420303101715039401d0030300300e07000c05541009502a0255a64941e0300b000a00000074201407564003d080034601040c60b0300200500c0040c02068070320901c51a00302d075000c81000c80101d0190350290901070403a0811004c2182c0d43d0b00e450401500a55070b00300103400400040100c4514142000f00504481c1410b015503008c0c90030482c402603005200681d0b40b5050992030010368450030031203074909406081c0541707a00b0510400004514a81e100b28003070312070109603404140c052024581c54186010085182108020500091580300d0128404241c004100803c101e4000125010812101e00007484a0303e04050351b820950238801c0b003140d50710300811201c40d1114007070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 864188776 1250 864187526 864187531
    0x5060303070c15171006020c010f0e100c050f0105010503010c03090f022101020d06080d02120d090c0f0602011a0916180504090f1205361e01080c030f 66
    0xa40fa840d40c0d803004003013502d80c140140e8a002820500d03008202101803908030640564649500b1540ea40341d40348019103962507907600220206181d03107a015168a440c40d00d00e48400414504402c40c00071a40d00e6501c1c000d40c110304c07190341d43d45460042c007180c20300348a07030000c14105103014071032524a82c03184c0c0d0151401800107405450302c01e0b1407800d00f8412014505484a5200c0210b40d954298140300004000d14016071109010303124403407819074800180915490001c0502600e09031120240f0700007090140d0b000c6038102081d10740003038101110725000c0000c0069030000701d50104480c28082c0350800c1616a584582940d5080c803904a00100d040020920329044c80c070004c540d140e600303049078030003a400b03503602506040c1c16804002c0d020490345ca50714812804075800c0c0f03034041301c00c2d641070060211903a86101c00c007218001c0b001400d900140c845195032000034012903a00041040c088a048810003000d00301c141c1302c1803c0d46d00100641d40001b0010700e007821414910480841000301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 864190026 1250 864188776 864188789
    0x503180a1206050411121b12120c120f0306091b0301060507050709180b01140d241409070807080607050703020f06010e0a050112022b06020313020405060303070c 71
    0x3c0c1e200003010045c0e98000729040710300007440743d54081041d800b035643d80c8682c422078144280c8556036424850a05420011503400d03ca00a0840100c40304d4010000d90440046003000e8410464149600c40c41c25000303000500c0d03024849a03480c54154140041800701400002c2025003d0003011009038440e0217883c103554880c0750580d544c20150500900d00f6402d40c12070400c05241004031080c003081080001c0e150351007541111a02d03070f0303908101440a0803c242c0244c000e1000346da09000140c2c1c80d07540070990344122a032002c03c1c0b8941408401221102a200e007644c01050041c010000c404204200c0100021801011500e044c0540795880300310140200f424800d02040c0d071401c0500034000c4020403142c101c100c9085d50782d9a4180b9540e00320541380d0005581c507013000031451aa41c03100c1c031600f80760090580514512107027480c0c05064a01c84d2603c6401c41c0300c242035400a00c0c140015401565060320443c0000060f004120032600c0c00ba089130720070381c010002c950010781ca10640d5021a400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 864191276 1250 864190026 864190031
    0x9041d10020a140d0902090915060d061407020a0303200d02030a0204050d060c0e120a021e0d11030c0415090b040b04050a050714040617061302070503180a1206 70
    0x400b505965144100f80100044080480d070094910743c40d5011a0b80d9034001c0710003600c59222800d15940700d84510800c3c8809110f170328000351090a03c0c9a04085282c0701d004006021560b080181c1e403a454141c400c400140c01010a0406040d07060141840141d003002d91200325048001e41141144264401501e1498001c4005800000e0b81c0d41694000c0c140030b08040d0564100c0e1519000401e803408402c0c000c11220880c131b045c18288001d009140e00003940082001c143c10340c080007060240140d401c2070b4812400c1c00e001c2c41362030f403030100c920780e42c8985104681d4005d140100342c10089030120741c80c0a10b25110384121000881500c2c02c1c1180e2200030002014035011000c2005000c01051443e042400e0400b480508080d42e40441e102e01710356a5480480d07240c08144c140c1d075216034400c3c0d40000f200c5003000228298540e2007590450300c01005c2d2a21200c2600d00c1d08148c1c1c0285c642981c050b000858000b0901400c00b0880700d084004960180321282009d120585068003100003500c81603 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 864192526 1250 864191276 864191287
    0xf040e1e070e090a02040305010e06010e1b0919170d02060117031e0409181a010530120a12110a0305061c0c09060e060f040915050c09041d1002 63
    0x44017a41140c1c0550f4000000303001000c600001c2c9580c5401c20301c680c20010319940005406200c041045814065a4195052800705d240d0100824543c0907a1900880341c42d01d400000e911038090b1249650480041c05404201c0d0790401c060b00300181644071810b4481021400300c06402c010049544805a000000202c40c01464602040e8010354100303a410500e0042d84040e04801d030b0074620804c2d48a40010010a4001d2442d602d41078000c1c820650401d2510002c1481d413541c2d40582e698242401040c1c0003a10300d4002590314254a0729403a030580200049c0703080700c1541c05480c002c403a4550701010702403a103214041900c0380c400d1020700e404041e6a02d020a080e0b40d240540d0391050300c1e06040d08500b804480c141500703a81e285200300d48001d4030b000d0001856991444e40d25110b008010208031400304144144405416211000c0702c40e00d6140260501c2d40007103108940c021115a0800782e21904410f0500c81158812641c02d914101a00c0c0403008040b4005480399200594000c00758031403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 864193776 1250 864192526 864192541
    0xb030c060a0c060f02070c050d02030c0103180f14010b01090e0105040f020d0e0c0406140d021c08030f0f1008100b0f0a0306020d060b09061e0f040e1e070e09 69
    0x150310b0058010041400e00003030304003a0076103801400c003d6010361046c0d0300413513403403080001102c0c0400c002501500100ca441040c0c1d03020303500080c40807400c0c1082d45100922a554030317408500b00c003c112426543c2e5011504840305c240b140300d034260350a00f0104400d41c18196410006181442480d1085460700400d00400001c0d805a51085070b4204040c40b4401040c44201d0300d480140848034000c1d403a01c90005583d0496280000c80702c0005410510780c503042d502031242006480c803140e0720f92485040307200000f0300170b200150712030fa8a0309000c13400c60a01e6000f00c0d64103480a04440c4910728420001d2110b14000324000348024004280080c03c0c000180c0411200109040016405860080c2c0002031000300e400820b01300c0300001080140c1034903403203090580d001e18944550001030621481d240401034040368071004006e0131280c0d00307112880c01c0b070801c075511580188180c010342ca01805625444151100400500340ca044001480d28001c010030090380101c1c200d100da140c0382c01003003c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 864195026 1250 864193776 864193787
    0x3070b0f01080f10022113050d1b17120106090e0c210a140108031c0203010308070311030403020604170d0f1b080c0f07060807020c06070b0411040501080c03010e010b030c060a 77
    0xc13171000600c80546d500e0240b010f480103030b07491202030b50140110382007032803c58800c803403240507030011000e07070303c60750f03010b521203588540c1c104188041a490421881403c100c0d0ba1840c64001d1116542d071701c2daa20b04280c00026104030281180c451a10144690905005400014094640000e600001c1c690380c01c080303500a0f042e54109a504800c00000100d900381000c030081070308201d0720f200d110015025480d00c500300c2c8424403001c3c1440c0401d00c29000020702c1403603e220030602c02000c6a003019141d4002510b240e01640c0141184499403144a00340b07002031000e030840812038205000c0c0ca43c01c0c3c035405410741c00d0605404514084013002002000180300545030b403208414112420112010707290740d6580180d00801d40451302c4000012046840000c0f6862900c13409021503081c03e11986e076445280758094412a45144880c0e00000f1685852040c41d0003000c502d4024002e00c003c140c2410b003120644041d080e040c3c0d0500312084d0268034001181d903043d44c01030712611794607444180700b01c44 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 864196276 1250 864195026 864195067
    0x14070605041b050a0503032208010608010c1704110f0103020d020d0c08060d08040618090c1e0905060315120322051807030c05090303070b0f01080f1002 67
    0x8518980028001407115021602801035558082c42002684a10030030030703180581c4c0315503903050307108022a4440c80ba45660301440300841e00840090707552110822070070b562080e000345101d40e549a680d4040154403800052440042100352080c606046d1140c451a180d40c800b4503002d02c150002c4a541640300b581114007075502c0110441d02c413030b0f0300451880684110b07080c05001400050100f0f07413910f021444041c25550040c501c40c40d05d481c260341a44c040e0700f02c500480d8884401c860008885181c0d014440765111583c0c0e840082020708402c403094130001103a00c20400003034281c244865122141265001080e94000d51000501a07002500b4107080e054890554000450300f4a41142401c44800043e20a0300c903030b2008030744500c02c0c0300c02100102c01002007070b21241c01240e9058060340c06658410010314207a072400300b040010a19541c880c0d4800c0368000e0740d800c1044001c166241010f0b000d031010320080c020400b0741e100d07900d694000602c02c40d039800741e0004409203503403218001c650307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 864197526 1250 864196276 864196283
    0x20c010c1704030803100504060b0d0c140a170a0c020703021e0d0f0501050f0402101805031c08090a050601030210110d050901170f012108040806100b030402010f1407 73
    0x2581c07140c6918021340e09400039643c0d0404c030320782603c1c045041d250500861041c0c1c1c078500d1010303042c820014508009440c0500d401414400d80c1811445017414641c02000c19403601e48500b0203940080781d055044400040240c54440c2c0340280d5981c8003580403800600301c07901122440003000030329680002504800e089e40d0b0b80310780d0307040c8441d041207080b86039200300354020f50081240da680c003468540300302c1007160000d62141090b0b401010080c0142003601501000c1d0304601c560b107856001003864102d201c205c0001c1303101000c001214507170344080f42d16071001408024040308111307135a440707689420600000f031040c00d8424600f0344030340c814401c03401243e40c400c00310f52002c1c520150140060b132201c10a640000c8031542d00c2d40720000d6800c102402010417149035403107a8a04203c0710602c80c18408000d0000b0780788240040820401005030000d021000301401c00350400c2d444500f8165684e41c44401ca04a042c020400940c1c0c0041880300403d81e1420080c40c0d4001c82c0c00c00100d84d114601008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 864198776 1250 864197526 864197573
    0xf030c10050f30090613140109050610080d09030812181005041e0c050f0105090406170609070f0b0306010309050f0a0215040806130c0e04030c05120901020c010c 71
    0xa181c50350741c140602c14004041e030802c20b144c0c4450401a481e04c900700c8448091305c803d85011700c0054581e442c0821f420f00e081d400005c07942225544c6905289003501d40d450409010030040c056407500340900741700c1180504190000078519521100207005402c02c032620781018500150038106150b130801e94500d140801d440c959903002e00860000d100580d02a941000107640800f06c040b5401c2e039001c1e17000c5d0001e4650b0b099070b01e440c04005c400c005d00100d8a040142c00d00c141000c0340c555000741d0029024451810840c0b18140001d2071500c00c0090403581e2a6104100400081d00300c1c650030700a949282c110b040c3e80340c4e02e440068000e8201ca40c4002d2003031040da030701c0645445011415981e61442111402c80d40012a00702913814001c5000d4521107801c002d01080017108a5107000d6083e5200316420041569034543c1d42c0c5031000100d809402061204591000b0003100784100ca080b118a10011800d14050f100002c1d44c036520505102e040c000c40e2402001403020a030b2500034800c2502c07004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 864200026 1250 864198776 864198817
    0xf0306070201020a0318110d030e0d0503030105151207260108010b0a080115060e040b090118150f1502070803030a021e190503130b150f030c10050f 65
    0x34000e5014030042c0b80001d140070b06c0c54029080400524541d42e810081480c41520383c007042043c4402070755821001e2050442130310209466910340310031514026030240d034907903240009000300e00308040040c2c0c01920081003040c0e01020140c0485420400320b144c8003044100c0400410280e0004505550090b000310300000340111054201c071040250940b130010000703607910300076800d0303401c2000807444011074003909000440c400e40204408580045c004102108503002040c0101c0c400e80005072281c1d1540d90f681c05d4080c0d40e010b54107000e00440c2c580d9007040c2ca04a503034840201680210070a00e102040c986d600f070361003000100c003d002c14200352540c0342403603800c40000794001e59803200c003405103d0340b00d10410000c01c2624802d140a00054044251806040303c2540c0f004181c00108034114860f240810f42d1807000b60300c5581100b00e40c988202c1c21b1410014046d8101061508c02d038441d00c0c40c2c03100303500c1e043c0d49031703d01c07855a0a01549566881100d05000c0c02201d00000c5030201b00e03241d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 864201276 1250 864200026 864200041
    0x190309150c0516081c20030904110a09060504050607060c0507050d08101e0b0a140d0b040b0d0f03030b0f0301050c0d05070f0804120314190c030c0806060304020f0306 73
    0x1c03820121460b030b000b2034a00e1807045105c5424003000c8150500410302c000044810000900003010b2030600ca242500d2900429100003400c9903d00300c440a54401d000c42c54070105504086140080c00741410080e0030503141c000050701502c42e1100062102e511202945203480c060402d4904803035001040e101060035044004040d45002c560034a01464409000690407184204800040942200c00b840e811704101d5170500300d60025405c0c008020000d081c0403038104d03511002d0041520020004180f0b42ca030141004103590910202a200c2e40743c0b213001f9000501c07008151480350b90b145c107011400c2800300780005c54040d030b000d0704240c06500b04400c001c24280d104009081d000801c080170041a11201800c1310035810000c2c04101040380080440c001c94500c074142240489185404a03041139403064405903031200740e610609104a800f900c1020311103034000c0401995991a0411030220071000c000c088000c040d00007401500d00201140c15501d4580010101103400b07000c40b07040b42400c41d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 864202526 1250 864201276 864201313
    0x1b0d0605041e050106030c02100b180405010b0112021c0c030609020403150e190803041b0e06042912010914150a050c0a030e2a03190309150c05 63
    0x10039090143d2818002107031040c0a4400d030f024040c05a4001c04003c1000c010010040a00048407580300c800d072440e051000310343c170700c205129a100d00c2c00404d0b0032400f8030000d404c0f00e107032100070001c090040c407050301c1c5072488904030f1100c00502c40c40451081000f600650041030b180e000b43c40b200340002008030074010071803050b040c40c0d60f40520800c20703150610801a01c2c0e000c8038500d4110340d00d094400d1808600324030301468115000e18050088942c0c00d001c0440c3d802180d0713000a12000d80b900400070180f906204080c5915881c2d56030a58041070060007008064810f011684242000d5485e250301071025801042c1003035104241c00940c10f54000c00c0f5980d1f1402d4030709030503114042000208491998090580103020341d21107070341001d070302940940c041d003040c1803050210301c02c1c1c9040c0500003203043d5501502121004829488042c035005050421381c003210902650541112900c0002c0e9018070510110380310750441c0520f90b03070300c03c0080352030000c4031001410f00e201d4018000384030419103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 864203776 1250 864202526 864202571
    0xa0602010b01171506030414060a0b0f01170a0e030708180909070302090c07060b0a03150e070f050f2418010807020604122106030b0903031b0d060504 66
    0xd0721000303001c80740e0180c0d0301070f0201e04442e4901950030f07204281403542085c80185400a100d00310352210031280100d010705d8440e00b1a1000e400d0b54441003411800c0c1440c07e00000242820301e01a071010212440034004600040c02480455544520409407150f060080e10301080c0d0054445513190301940c51a0078081080c08131074030403489500828114840040d0020803a507010344800e01c15a5a4070340c9038000d400100c000e4401c0e94039038007801c0580d9101401c5102542c400d918108402000084110480c0c0d000702403010280d01c2418140b20608005450004650301200c01a5528035802d02251307074242142201c080c2c260704001c007200d480d102c620141c0342481c040c1c007001c80510f003041b0044401180c01d80f42e9a000d60010004100410701a01525403030030410b0070aa40c85200840205504083c1c4ca005805030a07507420052081100c5080095003041706903004600b942481462600c0d0110929604030251000286150111106801040080030300420800618100700b010a4096600 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 864205026 1250 864203776 864203779
    0x60f090507051207030504080415030c080c0a0e0d05120c0d0e0d080a12061802070210090602030d020d060b07060902150f0f0325200705010518040b0a0602010b 70
    0x2068001010740d44940e05661581c00e030a5180489502e4820099005000280054602c61020480495407030491480c00703807800c4256400298201581e40c0c01441c220011301442601e0a04200e00840d03e81d01c118542c0c0703074600441e0002c00c1d1408070304c1c0841ca808001c4034044001400070402e00d91250003c2105048a12291a42c8000b044202c0c10409040741040c4000c03c10401130001a0070ac0d03124090005101544c184000380854a5044016806d405014245131054000803400114108080c60304040011400d0280c401418a84060340301c0c000c00007083d08055001c0f40c443c0c4940041d4118a000384821841d030b55540b0503a003001000340c0141c2c1005d03409030500c03280d41000101303035004540000d0107120129081042c0003034500d0f8554000340c0500001c3c2e9803826506008aa0816101400000b0340c0302d40303809207901a0030080c203841d500310980841d000100f04000c580d80013007c070b030409802011040100c001c003200050040c10104a140c1c1c010100c0c89003c2a13a680542c00300d21001030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 864206276 1250 864205026 864205031
    0x315020c2a04090c2312011d06070206010b07060b100801091a0a0b07060603120302040f0609080d0c020301200307030b060c19081e0307030f09121809060f09 69
    0x10500144001d032100d0300b03c01040034600300707420131440003100c03060051425020390441a034494040040c1d80c0024002040e1102e9540e5100d0803030700d10031a113400901500217405480c0f1031821001c003031b40350300051140422901000403510104601c950086e01103100c020240100d54020510041200c1d00034058078000503e01391400b61600320401c2e50b100c1041e40100100d1040703061600c04942034101d10303000ca45c4039894042c00700c0098030040c07035540003918070f580040e1510700e4680e212808100d203500c0a0144103500c1d6051103080402f08004030740c140c860801100c000000e04c0400d0040050750382400e030712a10031442850881402c4000d5010340340d503036000d0124070404000c0000910031909980825448110080543e0030804082c0000c24010074174241440316407100030a410440a82c0025030718000020042c0c1140c2512032200c54510340c450420646950381d13651543c2c40d100241754004d1000114410200c10b918200003c00b503c4205010300c00c0a07a5003040e044142228010401201d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 864207526 1250 864206276 864206353
    0x12071211070203070501110f010e0a110d0b0109150321020c01090503031902011b1205010e070507022b0602030f070c0c0b09010519050d0f0e070315020c 67
    0x21100c098a684a400402601d0304c60b2501005541070300170f442503800c8900075500400c9200d07100303204211140b40d540c0003400d00102c00380380024603403017084951441150003003592808101e003c003085041d40c00c0c07240d00040717540401104000d0001583d200600748607903255094017280708100e15142a11141d001c03124402a14070040d50280c1040c050707036415500c00c1c09802c6c03071003201d260320300300380300141c00009003403501824002c110803001f09208002c81c074a1513140c1102106482902c3c010981003c0001450510702070081403480747d0351000c0d01c0340c2d00224942500c4090050f1858a602d226800c000c00c58140d0b01e0140081e40041301d0248150400301d00082c542c03405889400c00071036015001320f0145040c41f28100107500080318040c100b04050111803244424014104035440d00d0744ca4817616004c1c60748800d800d03030348206080c2d0051b90411084021215000504100741d0340d00c00c068000c1c1014441210b1300900820560000718410700d02d89070b44d4103041e0540b45a030200c181c0000ca0155 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 864208633 1107 864207526 864207551
    0x21c0608030c1c0804030302090a090c0c0203010e0303010b070f050124090b01020106081f021e0c15161d1005130603060b03010b030c120712 62
    0x10741e0000420002c4100c0800030354428032002001c0e0180c54080c6640185001000f400050500d134020980f2030f150358880e0701e151b000d0250305808110201c88000d00910120361404140d000c1d520b84040031040f1400441200e050b0b821100e040751901c0c44c5075980c000510341200d01590395540c1d40041c0c02c01c91080e003494064034496811041015420080c05804903615540755606680c503000b003c00c2129408601610031001101d00c00e0802e0740a400c43d00c02078444c1445003500e015200d1424031416a84001804a04d01020100d0701400000840e00b81200410707610200e61010000142014500c100c0302e140003600d0300c4180410f144150008502d200705244d2041c0045880406d02c0c0000c058007484070b030018103451905010851510155403842e100c103006000c4074440000014490400d02c104449114052205070f8240c0e00d42a000103040410804800008608100020449 = true := by decide +kernel

theorem cover : BRFrame.Cov 864028776 864208633 := by
  have h0 := BRFrame.cov_init 864028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 864028776 ≤ n) (h2 : n < 864208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
