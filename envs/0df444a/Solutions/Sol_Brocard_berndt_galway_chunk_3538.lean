-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3538
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:56:59.73539+00:00
-- url     : https://prove2.me/submissions/566512c8-1054-4b0b-9c0c-9d7e18051b47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 636151079 ≤ n < 636330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 636152329 1250 636151079 636151129
    0x130f0f05091303021207060c03062705101707030210050c033f06030d02031e25080a030b0102030405150a02100204080109050c030105160c06060503030d0b 68
    0x6444211141d9445002c041e540d0000842c1407408038a000004901030501d01804150075042003c260010903260710166010b0120340d44a0780901c802560207820415000c0490059000c0c40c02141c120651244540010400c00c41e070704c25061031903884090948a13140c010840034011458a04620300c5511100d00d01241400c0001803da070760ba01c902c0302c940d8032000030103018150a640b000c007400310601c80c5510702900038107104010b22081a043c1e400038861f0080102c0c00f015944000217075030070700308062103440d103805068845801907440504a881e12a081010307091180c1b50000c8144101449154036a80e5a100080002c04035101040042e0440d0401c000c104440d9807000d4407425110b070083d00140c1c4d511050075042e4904018402400007071400030a00040070841907101e841d10324002e070150746c0c01450f010100b5003200c0e03040b07400341e90319802030001d800810710503034030b201b10284030350400078840781c6480000c3e1860b04007080141e4011b440742c07102e5002e0f0910602400ea045c00c2c1801030015 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 636153579 1250 636152329 636152339
    0x90a0209060607050703050d0302070201030e0610060318021c15060b03010b0d0906090b07020d03060b0301090509100e01020a09080c03060604050604150f031b0803030a0b06040803130f0f 82
    0x6900006415584140b1020a4034803d1002c103200500085500034101c0d40d01025500780640a900420b0090340468a0040b000040c49008190b05100b180040c802e290290700f4240305a00600340c2542603d41800c55070009001a25107801c81ca1806401203018251400700749082d507100851034030445850782c1040c0b000c0102d004098141c80c199001140380c03d03212610402410000c010310240581a0703030800700b4120500030a0000c2d140100b620360f080d00c0c4200b040a806a05807541d40c030030201c0c10001040100810a001d034462a0007040b024150751480108040d00d4041d1000f000c150100ca0758000740b4231515070380003412000240702000191800400350790000ea218107000302064050303510380c000034907a6640e5601c007001607e0080910640030f519445e511440240e0350204440f41e4022a41d0000e50302000140c0d042101e200070000c51560381d41e0340c0003801400900b040c50b6044001030102040505080c00a003004e4071100c91107800d46454111882807111a5900060040145c0341e401c0c85 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 636154829 1250 636153579 636153589
    0x1050d05070513091b03050c12060103020d03020c0a0f0618051e0a150305060301050f1033210203190203090705101d10080601030905010e12040e090a02 67
    0x1299002c862041c0f03040001074200b40a411801c00040c0071000c1c8240ca10a20060484500700b038a01400444200e0b03400750302885402e151051403418581d00c030740010001807401d8815200814805e2040d601d05510300750200e4000e1145412022410005180c1402415444051316401003a1040c0e20140315103488007044101007100054034202503074102007141c548601c5480d400600c80310a800c00782120300000240102400d0790010b01ca5401e00d8041741070303203002041503070150340915070f050101803528000c480001101c0f007030103030fa166900701b030420005a003282c0076020412a480d10a4964942d10b92090881050b081c50356000d84184140008040d940494100c5180c00703480050b0740f40c44082e840d905d0122594003280d44140602c45c003c0340c6e180c0c8411044012407000381c081c0700500c901c00070484803071100381038200080c40b6203000030a290b10a400454a81340901d00000300f92042d10016810038201101e41225440001410054442ca56801690001080740941000f803a00c2e40098 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 636156079 1250 636154829 636154843
    0x140c07060c0903051c231606140112031209050c060f04080f010903110a1703040602090301090b160908060606091503010f0f140d03031802031005040b01050d05 70
    0x40c00c02680d0755001c180c035500a280d02409160058100c4952544000580004002c0d00780100006080c0303030041c2c03440110004400406500d02002241040d50803003181c0700d10a130140e8296050740d190303070503030888a131340552090203000c48400f003012102c16424040c1141c400d901400169038a1310700c1c200041407010451848c2e1042c12100256168440c1c030740c41c1c1c1c5902a030341100071107009660100d20550030542c004405140f0039115a00c108540b81d42e40d94543c50f0261024004026100000f05811920300065600500c160302c01410310f606140441d00b11280c000d030468006202d60244030000d007410180201d03480c914500000950b05050059441d5640500068018200400c04c1c010941e41d0760821201e02b003851800302d40b81c3d0703034400240b5142c502c070b4804d07400005840c07603000c54042314001150384290381c0a80441d02d450030640d011402040301c40c3c5141034a498030021100160303028030606440d402d0401002c079486c101403c0586034501c0c1a80304600c02d001c8401d4180000da4045410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 636157329 1250 636156079 636156083
    0xa060803181c02031e0105220303110c011505030c0301090c031b03240b010815010c08040f12060b0a290412030302130e0709030f02180c040306140c07 66
    0x100003460280c0c0d000c2e09030b5001110003503150017203800c030745280d008144680101d06000d1000303026548071031400e0404c0840e079900d0075850803004481c00c0c01107402600647d010000c2d4580480c501030340c5640103400c40d88442002240103410040420452504200741a80321804900800440402da03a81c80703207000d241d200090400c9180c54a500d1601c3d6001b4040c001590009004003c16581603062000241c80500584c0e02c50306c0d000f038070031255203c0c04850303100744000600107001080003030054a030303040c44020403241440304100c0801d08824041041004107450100c111a180d20303464003a0940d20128001c0e8081c01c0711550401c8200700d0a001845084117000710005940d01740250080300740300c0c6400c20074190040c40c104008055041d401001102000290004060740759080c11242d0702c3d0aa03030f2400000c480000c180b0100301e0403124071030f00c01c0c1300a1403110840044504d0010002d400c9a0000c2e42c43c001042c01c00070700003036020700f51080c0f00c407410102c0c46241c468403000140c0603911300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 636158579 1250 636157329 636157339
    0x203071410051b04051509090906040b0f0c0a0e040f021c0501120807030f17040c05030105090c060a05093d0503040302030d020c010b0a1e0f0302030703170d060801050a06080318 78
    0x109070b086d003801c03c03a02115009042c19106d468135500c4e803556644140d400319402110032002a03101e2030385000803030103010802205840c3c139406a008032248801c0c10501c1c0d0784503a4032001ca4104103013a100404400b000b80d8640882c560381004c4480032500160b000d20101c6803030100c1140050b000108a401c581d6040c140a2a588515802100c400345828104900b072030300f520502c418040905030503001c4070411002401595241c000a9491760440c0c260140c1100c810300c03c0201050280c406000091301c007070000403c0c1c4107241501e40740d1180348405585d01e070b181851112028901c1044c481c40411032030505c50300d1800c0030390b8029039a1256200540c00c880c2c0c080760704000b54000307422030459494002c1040700c01c0c03a00c680c0c041c6400d003405a40d030007200c0c0d81c0342c9000810100103000e03442180e030020054006503145844814032400b400006060035141000101006030080c41850060920384000040e40d1402d044240102c8000341c02544041d0300520200110420b003200b001d070b1054082e52 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 636159829 1250 636158579 636158599
    0x90b03190b06043617070b07140d060b090415030f030507021203070506070e0a0803121807090e1204051f0201181b05010e030d0f0203071410051b0405 66
    0x40c40b2183d55a803100102e6040310744c0b200d014a10700c28001c1c40b001d502e0080792035800c081381c3c04d4008091442120700007000302400c6000240c41da4001d00811503c451100c004515110710709251204541320b5410000c140d00c404110000e65082034400e045e04018410080b801050542e120031480011040f4000c04109001a8007070446d00e8040b00c4070001032150b010bc3c1e8980c421442d1640c0c90f4002110b0290010b6504000440c440c940104114101c4840401030341c580b4203030b0b605075034504070000c0020f02e811000003414442a002041040004c02c0340380b000144407940c1c001380c1403d1a1000080c0d43c0c024505100030320681d503603980080140f414201034007a02d107400a4090380980128200b41010aa0441440301030101842c2a200143c910340081c1d890140c640005650140d00c2d0b90f1076617016481602208103450140007020705419560044900b00340e0959692049043c0809054001c2c5d00a2a69914030031210b00450307800600c410711106d07810500042c0700c0782e14062440341c1440b680d4409 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 636161079 1250 636159829 636159851
    0x304030210091214090112020c03070c0602070602070902041a0a12020d060e0a0632030a060911030604030e060906160507150201020909040209180601090b03190b0604 73
    0x30500740e910440711010300c4078940c181011071240a584845030f01144051050101c0142c03198101e80d28100c050311101d0054411b404d04000039001a146400756200c20442140464180c3c55036030020041c9a00604180e0f040003c000e08140542c0d10111724940180300c1400300c02411100103500f41400d0114a44500700d46800310f40ca5072801d168a81d01f184002002181070000e6045a01944c10300c242950760b51711500780110454040c1e10451405c0e041000349018100114980d900c40302c01c0020080c1494802031703001a0a2560000302210500d82c0d40251400308140d030103a665200c18201c014100f00d142c941c03005051441c003a042e841c4182000107034401c003030742c820b0203840070a0320606142d090960b051510b50354032a0030f8040d603505004240101012180305000b11ba81c142006000c20081c2e4840e6424032071014806409880501c0941c411120491000c000985c000e00c003500001c5107901c8404c05142c104060140740f002c000b80b980403060085182000450b40001040d100014149128 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 636162329 1250 636161079 636161083
    0x10806040f062003100b070507030f02030a080c011506030b0a030b0a0f0f0e0609070b090d083016050f0c01110c010b0109090212041101030e1e06070908100203040302 73
    0x8010399009030003c0c8031460b0004010001130340c0300728000424918926140c80c1440c1e03039402074250051003a0300c0404140002103039000c84021852001c2c6c2118107480c40c96072020356a0700544402482a03641c1c07082e5200096910701c118000302803600f8200300c103810203004102007211358007000d0004c004600106142c503941e540002282a4038800800c041a5021001d40180c10303071000c120348905c5944003042030502c0200701c0c2c0084440550425240c1110b000034015003000c48001604c07405824030030600304501c02002403043c0020800210005100300e02621003210001e41105400014070010304001c2d500b04086401113100d80340e0700c680b2440d40070302c91030150440e003c0c4003842d5403011900503101c50054000e40c031064026220081980d0720341020300224001d070700c0c032032486030b41000c041400701c4d015401c050b00580062402250300321a0008003445c01c00d030040074509003010010100d506813010b000640d08600c2c00c2c40d1036501c0500e05421703203542d5155486200249030303000012074201802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 636163579 1250 636162329 636162341
    0x140906150901030b061614070801060e011a0d02030f0405070902030106020a08030a0e070f060f0305100e0603280201030b040c0504051e130204090b030a0503190e06040e060117010806040f06 83
    0x2403110800e1001ca87c644070220007200c140600c0c0d075200748080410103030010300039907040c1c68908000c4549a1b2070200ca02e4001d900c62006040c1e5108104031415180c0b80a00041d44240f4443c1d400c06d18609041c0b80c10b40c90f00f02290b020304140740c4180014415164081020481590071040711501c0713840302c0c84104c00501240c01441c00030f1084100c00100e03460301111007002c8070026102c8030300002e003041003901236800854180070328200400e024059115a2005103070400c0015040b114001d80c0c15403401c1e150108417160820f90a002c0c3d80d401c08541c1c1c0340c058400000020794050107003114900020f0551300070350007802c0c81100c125051400e110404d5541c4001030300000c0a1066440da00e100302002503001e409191081414001ca204181c00c0005102040d60fa000000703501d4240c4207501440d000b44503c2c0c00344100721070300d10701c501c0b00d66030100a0805001e10741c07400001402c0060014001490b10f1200741000030000004000803031000c1180c0364400d8010303020001c142c54504c1c083d801071a0f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 636164829 1250 636163579 636163597
    0x206150406050a030318080105060a06030e030910030e0d02031608070203030f030a050406060e070914060c010e030a08070c050703111f0206041b0308040b090307030b01140906150901030b06 83
    0xf054a0000a050788207103104802a030540d16841c840d51203051507803e1354400c0b150290803905c45e550820003103100750701081005424006803070a0803900c0b00011544d9151100580000f03884440400240c0e03014041c002090000380025850301c440c9008084508048000c041d0500c100461941e0035508c040c4103c80c2000300c0100e8255907894400005401044191016110185030000110341c0711040f0306142e000e1000c0b505e5515415141c220001c94564038801120303081801171040e0b040003142405081014941c21000d1030f101c1d003020500a1a941d0010042c80c01c014030001c21001091f4081640000e40e500078261803040390502c001f0491444440540c141040c2c0e150140b5503c2daa40880c1c8180614441e40984d01801700d0001040f0494095000290400004120411050303101000400c040e00c000b80c15111529680c0d141c0b4264044241d000720780a054828010205140401d08070744c1c040000c95900b40d400408025100260003840726039030500d41c1d6101001d11590300d550075598195 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 636166079 1250 636164829 636164839
    0x20408030703120f05070522120605040b090c24120a0203070e03030901200a0b0f07020c041107021306090f06060201140106140a03060f060917060601020615040605 72
    0x690b0b10300202075949031900d4070701580c90112200d640d0003890003411300070101c5940762410000030000d028140c00c42443c03100340304508980700084c00813603140503500d081d01074900022a0b18242c248030030810402000ea4009401c00d00b0344099a644d000d000b00d01a001c1c1440c440e2051502e1611404a44150080c01240711030030420000c18100300d4008501c251b00e6030780c8101040c1b12040074141c1d83d0260307001c0300c0c0c0481d00c0d1180007015111f003510754000024841c4201c9140c0c05a9844040204009440364040d2404480070050721344c0d0100000c1c0442101074030704020101a49030b440010340511340b8000d20038074144101c4c03060f1000c0c98016101038080000c00b0080711010f01c50010003011140702d1031015509010180102003800c1d4580ca040794129180c050005102e0303480c840b0750340d02c9440301000381035540c100890009480074001004d45030940715181c5c036508080340d600c0107601c2d040b220403740c1e000c00b08018031642e000c1600c81c0c011226041c0c0680c000c201c1030014020302440d805c80c1c2e400c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 636167329 1250 636166079 636166087
    0x8030c090a17100b0105030109020c0a060507050c06073e01151e0b03010b0304080c070306140924090c0405090109020f03060103031d06281e140d02040803 68
    0x100000c60000160510b140200d4000000404110055a0161542c10b020520900040001c6051a00100305501440301035a4400c40955500c0301224400e4455100280010409174202d0300100080c82c0c0107800c034140900e204030b013004690322048503102d072000010a106241c9098030b9084403441c40d5680324000a00400010350007101d8104010301c5000301e6409000000860000c0b040001810350780030f0714525281d6800d000d51418940c2c006001150802c0f01080030102112007405828040c5209a20210718a448101c00021946002e09092055040380303409034841d5207040514000c003100246a501c0a40c0c0341a140d508140c00215102d81250902c01080140b250650290751014030850fa4510340c1860b50b402c1c1540d07000240401400706c1d41c408061a00b14001440340400990000e050b103280c14440a8030880c91181e44e4248950240a500e00c50802c035080500300011041150381c1c0c120585064000a008503140a036403410f9050000300070b100344145404a07005040040e045039a2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 636168579 1250 636167329 636167339
    0x10e04030c1a1e160c060213030f080702010e100c030309050c1305061002030903060c0d0b040e030c12180603040c081203090c01020a031413090515120114010308030c090a 75
    0x1900c10318103108400001d0080001e00d0301904107100100b05982c0795541801e605065441b40e0083d40715816260880704800c1c00080046d1100c050489501c0c4aa0b14040d100c140510000d011143c205101c18480d80591012081c120b50140b880c0c90702a0701803070082014078050038264203104a200103c3c0c0c12449606410030440c0a40d000380f4001d007000d503413100c070001d8170710004c036141e01801843c1075254010340c01040603102102c0203000303600c40d5541d000524280000001d0211203a0880701c500a800106500388030480502a0181403100d80e0706103850086903100d040e0b10421802d00b058411103000c03001c502404000d04080024103080000c454400e100c440001d61181c2003110030040600c10310040140747c2d4070210300001400e51580316041c091001c900a51110b80228000c81a03910307001e000041c100440d4092030b0301522070b001c8203120b61102c1000340200751103551300d800c0b91603040040c1c00d032030800f07041c2c0f42c181180d8000c2942074a0f516080c400020510500b00060f50204c03802d040820 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 636169829 1250 636168579 636168601
    0x200409050f0705030c092e32011e1d040e2b020d050702031c21060b071b080a0309051002010506090c0f04080a06060f0b03010e04030c1a 60
    0x109851040b07080745d241c0d0880c1010401d603410100c4036088180d4581c4040c032001d9035009455400811030403c18a215a181d0117010041484060400c400f45644007508488205500807084040c4080c85d225400b207100703030010a2086107406032001044464415040c05400144d8003058282c402041840111101d034086603032000212000440c0d00d414060b2100c8042e8003203c0450600c0c07494014003196498102e0a45007034202c0042070380c043c05551a8049880740c00340c0c0b26240f004445c0c840020814242007005500100030f4a8104224034000090142c46403002c2034400d469482a041c01140707245200008110700385600c183c4803440780080d80b00070950040106415250180c1d6100c5940042c910200d00740d480c2a6401d0b0b411a0300c210215000c5500c0748000d10131a250b07a120303685010707030b204641850724100b10b01c161261590785005010a40c00c150600e401003d01006140c155414096207448494002d000201880740c5045100d041040c0070080804c140d144500442881c41d0110940f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 636171079 1250 636169829 636169843
    0xf090203010b1807080c1b06012c01090f02160308010e06041a010807030204081002040503100902060307120f020d020a02060106020d050901051317160b0403200409050f 74
    0x24032a50030503050806904010603650f002c1103403944411070503240c00354140e40c1514083c1120044403410040d00b903180c00045050f218010304030000302915894841038a2016400700000040c5080c24803220342c0c02210101e0744c0c0c1c151504075600007446c1c209412034070028400d4206a13805000c5290303c070400e264118004030704880040c043d510300d9550341c000f044205c1d484c5840f503962081c03602400003070551003141840d5014000c0d00700149051b0301d4044103450854889a541d180c80e0700002c09000c1410184002c003100d003d40941032000c0d41c603a9002410501000704044104400c0680f0300c2078a0312260040058004204011560341007183c2e4550081e604c40003403100503105d0000002002ea10003d100004005160f4909041c600d1145c01102c07643e0186c442c43d4901c1c807003c0c070041b4500850411183c69140e40b90b005000075900c019815507003204c181e00980c840e41c014072040020818004400c419000c580c0e8000030003040300c00014008100188001c2c0c81e40c400c1c82080360800c10000307016 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 636172329 1250 636171079 636171083
    0x16030302070306150e1515030907030c0509040302120d0212040606261f02090415050108160f030b0303160305180a0510050304050a1401050708060301180818040f09 72
    0x40c040307080704d9201c00318070716100e03c0f400106448410004090300603064419030381c0d405c010041450f0072990991840103410030703210040b507500058010401c0000c0d40c83c1c1c140003040140c0302440103103400c0d00e000e03441e003009004c0301b0810f0704000366910b6084400d904455841111140302a118141410700300d008104601495060110b24005000344a801521551000070b444c002081d2160084003c200012200360002c0e48480d020310400038560340f07902910079103604456100b0546444e0000050000070060220160b440c0c8183c0c05640007984032840e04521081402c1c0420000d2510740441c0c5180f0070050008200c44240c40385070101a401001010314810101c21030403021100000c0146941080c0301e0305a1245c00e02d00450140c5000300c01560303001c0c2c091000d55541c0002501c0d03d0299040b020201111a55103204009040b40c104080359003000094000b00b03d0130745c40b0506d080070212030043c0680002070100320b55400c4000e00032004820342d03001c2d00902640c1302c000a81c0015006807042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 636173579 1250 636172329 636172331
    0xe090a0c03061b02030705120d020c100c02011b0905010810080d080417092206030c2d140d211106060d150504030909022101060801051302090316030302070306 70
    0x2c0c0039101d0f01c001705455101d500320000c0c1c8040d0800c80960f407103603030102c1d4095603203680034018801405c40500890b01d104040d2180421170000c100e01c0203003142c0000c000c003090007045040700d10200d60b0008184058400a080c50140742c1c07601c000341ca01070000c542c040c0c0341d14440e504050112a5012859901552081e0344d10302c158003440c421110580250b503c0303d900000001050744030303803110800d00440e019491b640014816101e86a68807041c0450f0000b2404605000c010502d006002c1440c50f02c4500c4c8003030851600b8102905540c699101100b803078810349203089500e09100700c0e410400100c0310020104a1107845220300036046a600c003065540074081c0400103030690510206402026071712120510302540c40d40c031031038000c00000d00242d0400c1304841020803840348510042101c0300c0b01c440d106202c1e130619141c0c20b03c00801604003d0801c0361303030401000300d52105a1ba00a8001111202684035059000820b180c08a848080310110312178001c004107058000c07407064292401240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 636174829 1250 636173579 636173621
    0x30309030e060c0d03090c05030a03050a080901020708030106052109070612060803220b0d0b030f0a0b18150c0408100e0a030f051303050f21040e090a0c0306 69
    0x820001e89024542c1e0303041458100f800c13403184261007940700181082c411400c804403d51140046890b2290f220f00440201c2c4000400351049600001ca480d400f07042c15000303529001966483e081c4900040c81504180140415180b1b0520915426000c503062400072070061031601d500b0495071032103107110380d03004109207010a04078215030780a5881511a490000c0d0718190741900d01b035410030303083ca00c5602044000d44012030b18004007002806500816200400e07800151810103083c484500c110000c2503000100d1000040c42c00540caa03402860f000c0b4440c51310811440c0345081c0001c0051380ca1411002d441000040c2c500d61000d071081e82e000038210760b41107c2e0f541403842282c56003000402c207030340400680e400003481014010154142c80c42c10301d041100c409451180c3d17034607a4004541c6030300b00d80300300101503804015159044030302000041e40c040c102422022940710b030340038403465024035100003110000c0c01c00c401c06a460340002c12404103613581c14040e00801020500300010100c040c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 636176079 1250 636174829 636174857
    0x100c02010b180718090f0c050a0903061a06031e0106020d020303010509071e0e130603110907050c030309011406011707030b190801090b0a09200f040903030903 70
    0x11141c0445008040c1c41035107080ea600403059036904005180c80108401c52102a20442111040f40020700704030401240280c0d0300344443c4161041c3c2d5491504002050020900166200c181081181e82000c00007a40101c0911030200c14444501c83d90303001000001842401403820741e0510b01d40c08240399000490741ca44108036103401800d2801c074010b920610041c0050303e041c1018503040b481c41c1c206003a02d03189001544013401c0c0c007800d000300400d904a180021908050419035106242e044081240702c2c15659901840c000c0e644006008000c90710010301e43d18000e00845040940c202e080781d44a1074402c00d640d010f03101148a911440b603200c1c0c01f086455001e460152082a10340c0400013030fa40d64140700714010000c10080c10b6000400c41d1454a00500e5500070300f014151000010401047e81d05100c80c8140c80605261030031031401c0300303204c08640c40718150780041d00c5070601c0c40540c45400000509400400071025030082c60401107008054056004562061081c1c458401000f480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 636177329 1250 636176079 636176081
    0x1b1203090f03010b040908130e07050a08100e0f1e1b0706020c150415090816031404170f030a0c0209070c08040e0f0a0e03190908060c040f0b07020307090f0209040e100c0201 76
    0xac0c0c0b50340002c90f40500a41307044600030304c200c90b4030607507240308a00c059a90303040386034681c8001d440445c40380d18002d09002c1821002c49802d09841c030b42c1004804503007400107042c40a01ca080d1454200a0000704000b01040500d4046270b4841282500306c907000c1010b0040300c11703030f03081c2a6411103041c074064000c0564040140189807040ba002071446082190b41007514401d40751500c01142004030070140031205d51440b5000e4000340542001d1181d2000015000b03501d0a54500b05070b4500780d000780140d18581d03034400040d2201c19816035600d0043c1d102c00b1026250700c580300c5001400400301140c007240d2000c480388a01c0c440d111804055985403515004582200c0050640d039003135400421001c3e8070340d042c1001c40c0e0580080c0d480c0c0500080da40343d41c0141800425500e1600c41c19000508204940b19980100081c25501d83c82c1454180d43b40d001035035402041c4580400903403601d28001c101421907066030403005c0c020b030092008500900e6640d4840529042402c5032900d4011402001441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 636178579 1250 636177329 636177331
    0x15031603020f0f030a0c0602061f0803070201181205010902091f0b18120a111c060c03090f030c02131814120a021b1203090f03010b040908130e 63
    0x340a044040300480300740000f140c1c00450654143c0301d00300c1c005000075100203240e00104083d45c00b800042c2080d41d000b6074a16949026000c2c0001492410b004031030b0040101c032542d42d0b09003040062000300740424002d041c020340c840d00781025481511001e125040d002401814421200d240b0940c0d2800700902e8084d00c0c00d2074171200313004841000c2c0900e0749040700a042072900d5085030b099060290700006c2845000b18907540054010030506c03001c2014403461200c000303030102d400c1028202d015032000082c1c80c2076200542881d0311129070240c0c0c0e0f40030b0384c80060543c2d040000c1100600d142c0c1009411802200422401586005510448115640300d80283e042d0b00303130b10340d0b0f6200c20305485501c802101c44000b562140110184d021080e0b40a400030030443c0d0a5402a200e12441e1503d0500204134118540c1e0241182c0038042d02c080b00c010007110341100d1f04891012a601ca05d002107401050b404088541103440d184110f400d002010015000c42020161001511500d41d815903480440c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 636179829 1250 636178579 636178583
    0x20a18050709081b04200702040605040b090c070615080a150209060f070c0b28050708070f0507081e0c0604060905011416060506040506100f110f0615031603 69
    0x800c0d1340310707040016031a20f6000410061006c155400b401401e64101600303880c5045442100091040443c20720f4000d070001400c0459007007101200070300200d6028a40240300041e1444002110070800205034801200780d280340e02060481d070b89035800c156803800004000e40e403481d00408140d51108041c02103644641c0060170140c1412014030321520550803480c0c1c00c4400c20840140880c2049085024201c1402c14041c600c600d4525010306ca00203015401241d02008010480440410001d07002c80d1079259200060300025000d50506604125040c0c1000720345004a540785c0000c03ca42250b003180120800c419070f0f40c001200c0b41000000e2041d80f0507480032a040c010104070710341c00b501001c04403103018107032546081c1640b40e2104000c00000001c4821561f10300901100c2d0409118035507005d00d09598100c05602c0040d0b010780201c210194103410045110076030200c006003482a680384c2d82c020300880d1114109040000710740c000c4000c889009109403466004200034942e0020100c036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 636181079 1250 636179829 636179833
    0x6020705010f110615010809030f030f040302011d010f0b010206100e0705040306021207030f0b0901271503020f0a03080f0901090b030a06090609090203030d0216020a1805070908 78
    0x140c9850019505089481c0c0c05100340500d40070010716a030028000780b0310417100d82c4400d400c5143e80c540054076601d8082c1580780030340d005201d00c0380400724100480c0e0700102c1d0141c00034000e6a4038035040703015020070181c040c45a591001405030000c0305420540100e0341d480070601c16442040300483c0c0d640d5081b04d110380b41081080003000084201480550004924a006807501c0d0712502c0d04000d076800412200000450b00e000c0041040c0e041c41080701e040b80d202024404625901e0009002400600583d000c85121500c0b400307000407040b841d81c4401145a4050095801c251200018403820b844240d00412100160442e0340c9807841c8804190b1350f11114070313030800800c2154104560040164603061042000020400f48122000340d841407013440004075001d42464484030581c1e1040e4840340300541060b80801c01690040180c911100000c400142c841415401c02204114110000b03034200d4803a603000b00310480011aa401d04c240e900d80140803544451104a0310308903144903400650f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 636182329 1250 636181079 636181093
    0x2040c0224150604181121070e0a0902070210050703170c0403020406030521040f0302010302071b18050705040e01050609130c0c1406091e01090501050703051905010602 74
    0x40c208200703070703075000310150818442c2860001c002c11a1548150041d0064601101e410000e448460248440120f40a00300a00381682500c81030480c68a8028208040d0248400602c015204031210020014000c2110010b0b0760388008c0c1d44000c1d4015403082c2e00946140795015a80e90050080f60040745d815039a80c5104201c0d144040141c900142404100e03500402001025075034900800c40518000d0010b001d400c418050700c140b4a007019200380900c8c0c6000c5c80700300000c00c16080900105d0360282405a07444102c1e1a01e46590f959180050181e20b000020200d1021070124041c0780c81d2075184d0040005440e0340341e0507a5036010f540b1402d400303c10b4100052105003080c0001d0420084003906442105071005495026500020007250002d00c0c0aa010340c24010007c42c008000c070440d81c0a07009504108540589900710441c4030b2150125a40e09d02c0541c00c401d40c082c5490b1034104000b00518100f0580060280c48103460341c00d9018100642c5201c401032920232281259450b030000c1681d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 636183579 1250 636182329 636182383
    0x90901050d060e0d03020d14040c180b130204062a02011b0c0602010e10050c1e0f04030501060f090c0c02010f05120f06090702030313022e03050402040c02 68
    0x704424400c0100c2d03000783c40f00c0c07020054420030031404000c1612900c0141e162000c030450321088a11030201001c800c641d1905000124010307605100c2556130114095181040d40482e20025180802640b034115000d045458607004055002d00156409a950040001100423501c2052090110f40907241484140c1d0940198010f46420500300e0300340d40040300401d55915403460149003036012001503511000908111070b414819841882c425400401c26070410001ca00c056000b01d0180e25500d04250502c200b81880403029030b42c0d000e005001483e55181c0302c0c50018041c11040c0f1a03824504024080403501078000d00680514a0140d540c010210700d454004480e41c0201c540c0e40c10500104110030310788035032001605481414007820810709420a82c00340580050000e140300119013043c0188940c003a07041048640481d0101c40858250400d40d0210100300e01d05d08801c140c200c0e03807405403030480340c05801040c03256008071030402c04800e100380c003a40c03141c0c0c07011001c1c010354000c01c2107044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 636184829 1250 636183579 636183589
    0xe040507060e01090f090b0d20041b0c110a050d06020a0909062111060a0806030c0907080c0a090b030a051801050c09040207110301020304030507060f0912050304050c220b040209090105 81
    0x300d0290040c107007503070b4011944a030a41051540b841520b41140d105040105003070030300441c40a0810840385102d6401ca1590007400114034000040c00440dc4418003102c941d200b00401c0060b11300104015540341051410000951040710b0040100306180d100168070f03002d504c0350f03000f12000c0703c0e4040f6040d03040d0a2030342c241241c1503030100d501c806148582c0045d070301c0c0e80c0003a103a5400e990300c88010a04000e800c1500d0000002031091041a40c1410091510b5102d05000d07040f0044402d01500d80c148420150741d64641a0885903103000c0103c20090030701107a8018a0260f400350a01502e00301c01c200c80c66003a12030842e00002c55902c03c00c11b690113428907600911440b40076250101c218400c030400030b420b80e802940d0a03070000d440440c0e04d8081c81003074400d0034144842c82c030701000305034011350b40c424421b4007c00301401400000307c0024140801070241000d0b002005208040328103800030a5078200e4007091484429910f0494080b08509007442204c0141900401100b40ca82c68881046 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 636186079 1250 636184829 636184841
    0x30a0807080c011b032004030203070510020c0414180a0c0b0708090a0e040b0c03070804061e0510090e15150d060c030618020a0e010503060a0e040507060e01090f09 72
    0x1415640c1ca07040c212000200c010819800032045d900840e00d83c50301960440d010441100c0c00c18007100803c03081006980010704402102c00030b0b42c40000d0304d40b0070390050b424480d2820400da0090b09003104203d11402c2c2e610b22510505011001c042002c620340002d59585007040402020000c0c0200c082c400c2d905007001070300c1143c0c0310344181032401403d0b501240e60312032560720200c0340000c001e052104114540c89101d512803c43c032030160551809a070010301c0c3c0540508041e010300d90b1040748082605117032403010389403500100144064188022884100d40c800d1003081422450440b10450514020440c0046491803690f04801916881604001d42c40c9117008242c0c0499040e4841d0006030040c000d2072840403854500040c2c0524003c2e00704001c400036101800078620401100100755041555180c80c0c103403e00e05581c590390344001240ba441c80079003006400c41d410800304002c0110004100040d02c616a5540040d410900e0040d01d44851398040d4881d0690010010320980501d0780c099 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 636187329 1250 636186079 636186097
    0x403110a0507080d08070f08040f0c03020613090e030412290702030310050d1e050118050a0606050f10032406170609070e09040503041d0108010605030a080708 70
    0x1840c40303414540d44440c41c09802d50302041c460342140d02910354881d00101c240c0e0344001c003800d00f4910044000c0005001440041c40180000c03281c001950602c035001c042c4002960780034011079504c86400d500d0071400c00740e038403401090904020340000f40890100a0780c0880305600100c0b525042c25a03505100803047c00110410041000e51140302d02c401820898080d00d56070b0043c50f541d0410074031030391214040340c000c180240b051245641c0042daa44100000680c6402c1e1894420020b42c03608501401e00c41101c8050500c04007100c406020f400b0502c3c021140c8904002c000c4260307204184140ea011452003075501034175580302c5101f0386000760810000410001205d50303014492105000410505821401c0051030215918011842040890381c02c00c000f121880e2030b600e810807005244014003040c0a000300b154402150030810100151400b40035003400300c0e2500f50000008541e901000d104010302ca60900c40300107020708022a90081a54011514910742a110b8030303585d2540d40241e0075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 636188579 1250 636187329 636187333
    0x3060b04021204030f08070c081206010e030102180406120206030103080c010b03070312080f0f07050904110a03050405100e060a0b010c170d0e010e2e1b11030909040311 74
    0x1440000d00c02d240d4144910300c030780c4a5170220411064000c04480004005000740260400844007140100064030700300100d200d44400d03a580c0c2d41004170355030103040608075019800841c0500c8161203071202c0110440301034404019032941d885039007000e00803a050180d0800001c00c01800840c03802001400005075110000c1404052100464a840c00319441610085040d02a074a04954400c5103103030016100c40400e003150408040c00c04600c54050004002e0060028040b00d007900e4941146260150049841e034881c0d0b120340004d00070301000c9400311103070f001c0c410b140740b0051210700c522107039000140020b0000c1e966000d9924020110008014180074102801b800090a005040c103003298408049a84555802505000783d507281d84280785240d040003c0a0128240007940c400b12003001c071a001c0c0582210404024400d140602e4500b10300d042c0115840d50100e848036407000350a0035035805140c000b007091007540340e0107041d070566441003040c4045004a071051003091540c0c0c0300801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 636189829 1250 636188579 636188587
    0x2130f0b1c1704030506070e0108060d030f0f020115170c010206090604060203180307110a0f05010e1329090c250201120c090311030606060d0e010b12030d06170703060b0402 76
    0x9030f4a103810000c0380c20031f000582c0041c0381401564404515500080182e840343c000c0c00d0559800780601404144c41c20800c2600b4580e800418800d401182c0015400f040095400351030b0a02461003104040803841c0c40e20407182002810b500c005001031080000001514440c4c80302d07521900a54400781c4007101e40070014403d80c003c50000d00042502500ca4007600300d24141d80c80038402c507284682e00181030603a00c03101c2004680d0b01304240031000c800c100c44203c4170025545441c801089800c1c0900710b1840e04001551102d08985444c04001c2400ca603800080c0e85c802800c00160b2140030030408420300140d00322150004040c00e52a0340510504185400041d01d116079030403540d1514407000018401b44042052000c0c0d5645503030382d20030a401406140ca0100e001c596107108880300c007034006507201082e00b11403100394040d03840b07054010046a0102c031009041580c0790020707502e11101c50316005000840840c1d403461183c11384c80603000fa00481e85180c8840d001069900901d681207a0200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 636191079 1250 636189829 636189833
    0x15010819150606170f0105030c040b04090c0b04030b09010501060e100e091e0c0403020f090921180a03120509031005010306020406020601171b060702130f0b1c170403 73
    0x1c0030302c2002d04125038904501214188403807074825800b6054401618480c1c0c014021501c021440030580c0c0c0080c0c03070120302d4403e5000454001e16a060000d03111622402d13021a01c060808000c0017282d0142e580c82a15440b15101ca0742262020701c0381c0e6020604034080038000c1d00340117160340c1e02e900c031504245155400351408074015000460307480700e1100d0120010b01d0303010512072883e40c000360700c15807040c1803074259400b00382c1c3e100210300d1062095400100040d0320100800081480a0307a5641d020034502805010440d150860f4005c5c955030b000700c031881c071103504101c1d200f80308076600a002d00043c44007416081d81c13107601003480c042d054002d0200c1c141414009009440c02184140d80050f521407400200a0500b4410307000030070311a10010950500041c0004c1ca600e40703da05028030202608004000340e00351040303c40c0203400440742d1580310603400069100c088031400b903410034410150004100252142d4a0740d0302d4070710903184054400850210b1030300d4192803910b009003600d070980300c0e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 636192329 1250 636191079 636191081
    0x1f03030c0218070818070e0126010c0305040b01051e091e0c07021c0f080a360b040e1824090d0813020904020105190207081501081915 59
    0x84904401240e140c84c00d20180e142068409000300c080b150151406606201c54805101418420582d106021640082ca0519910004101d403c110b0008005802005030041c0c041d0070211016640c403044040002850308299005120f40c0480d102e04035028dc2812040000115026003400c4400350350b50480d00c290b542c3c420909002d01c903003c1d86261502e1442c0304012102901c1111103800c0c140c241500703c001890100c9450100d40e208000907242e10112100316019032501e44104400000718040c07401107022031900c04021350101001000030760316190040c1c0301c1e00c900e11558009518a90010390502c1112045608040c4824180d90300d41c2c2051094131900d00f0340000c1080c41000d9031050100d40e9404114403d080b902c1814600f280e0302e05001d5041c00d14580300c502038010180c0e040060704581c410012500003138584505c0081154105030025030f500200d0007801c40f01d204980e041c030101c0454080c3c241c12540020300030040b020b0039003141074544401c024101c801103011080103905000d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 636193579 1250 636192329 636192331
    0x21f0e1e01050108030c0a061e1107050c010509061204060b030303090f010501140d03030b04090803011401020c06030408031303022103091603030806010f050408010603030305040302061f03030c0218 87
    0x400da090394910450030141800c640040e44004140c0e4010401000010300101b0402c5509401280000714512188408052000010805005107143c030200201c01520b8030f0180013054082d41c00c0380d000c1c0c90034500540300c6102d8001d202c3d610030403c0c000080000d04076420281e000b8882c81010072910f20020109141d81c105850301d00071904903c6007280840030034480c0ca401820007a001b16001849400815581e21107444042c4c02c00d40c480c1d0400b41d007034072143c0100c03e015034000d162503620340c3e44844851810504804042c01402345045810442c0340581c00d807405036070071549131451030722880f2081030310b022011000c80650265900380c82401d00f00183e2050792000310f107007083e581e24014840a0500c0c0c5504154015948114018404650311912841d4005000e08252081141d4002d00385c94500566101280395800c110020040544c1500403c1c0928841c3d02260742d00d4856010020000c640394034892000101d808041001c24810005800a680064650740301c142c800100d40b1034401e4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 636194829 1250 636193579 636193603
    0x150f0607060902100309020a0902030c090a08070815010b09101218060c1e110c0a081b0108090a0f03050906120103110a031511041502010906050f0106021f0e 69
    0xc0d41d0742d565003d50400c0314a540202181d498208483c480360340c00648c1c1305e00140500315140e07901200044425101c88201e4038461001000c050300641d64140d2a80d42d1002d50103901424052100200044400d03220118141c622884060b0704009042c0103010b101e1001c2d01030b100c108001000c2400c2c2c26045403040e00500010a001c282003950182088000d1b14081100401000080304103400c0c00484c12504c00c610302e040f480d1010505c07449403082c514040140c0a800d0b13024079403900002d01c148000403c20309110040c036401d0716100400c0c0054903a240c04440e1485150040d4940030002001401600c249a2003402d10b00d081c0540000454844d803c040c00352031032405d2520050050029035000014000c07030449944c5191810b641e910107841024040e4405c400d82c031003158a5120416600380c0b00608047d0300c81c071051a440050080c080c00c8145408c0c5c0d2154a40300101d02d10343d01c5c810000d8161035480d0010314030301d8011068000300651250025840a0766070308504203080003406030102001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 636196079 1250 636194829 636194831
    0x1090b01051c020c0d050c190c210501050c041a030a06090203130b0114030312060307030f051b0d0201170423030a141218012c100c0503150f060706 65
    0x62988030001e03117001c0d8a106203905024081c002e1158400380005c1034115004600b1848502c0c03c0286404074000b41d0640ac000c4501d1b100d551040e09040840ca0784614550145c0020710098682030b0328209240f00e50301138101e2400d10748110a034141d00b90002180c02145c1c01c2c0d0b001440f0f596940891040342c105883c4407103a480c5040c446024001400344031809802d4800301c1740851482c0800190f503e1040e40910021007024400040c5103640a109032002180c216000d054607003018908640c89108074401100d039100703da401013805091041d000c00c000d03039041e101d2403040144149110310a0000520449403040844070602c40a1700c0c14030070b0301c114140070004603280c050000005e0b0024219000e4008551028410515203280c098a50b54000310284c0e1210301034140c01e102c890162010302c040c640044210108007a540e17034003500d480c4240d42c5880540d1008199500900183d4a1103140000000e80a10124580341120340c0c042c000f1031001032540039100c5a84000c02d00541040780d0545601d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 636197329 1250 636196079 636196087
    0x30c04180501050108010915050607052812050c0f070303111009050709090819020705010e1f050309010905010501030803070e0303130e0402010e0d11150f0301090b01051c02 76
    0x1001251036410344140404009100365030414000904c03041051003080090303074481c226689480210304003100603120241c00c0070b942ea00141400781e50707064101d000b11280a45da41e18503080400e288074140c01305a01100024001074042c01c01c6500741c005115070101ea015210210790740f00c0003000480001c52185d03e03070f1480c40c544a12500d082401e15088a44024208a00103000440100306003040e5542e410b800038054502d0b00b010142030003118487c480d00c00050341410141d03500001e40380c0803240b00340d03204440c0e10911414000d01c00342094904000124940305021024040c0010319030010028000082401c0951903c5094500a90094944910000034042440d62045075109411010350041d89090501040908a01e0191044a41d20b15200d070114085a201d0400301c02041002851440d81203003e0528401141e21f0b220000d00c20552000310344400094003081d03a103451000c240c8141560304e03010f0150003601c0c0280c8454108001040208000101ca000c0038103014085840182c507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 636198579 1250 636197329 636197339
    0xd0b07030b01030221070513090f0c0c150c0513030809040c03091707020105090a0e180f0a1103010219021b0d0b0112050a0803070314010509091203041502030c04 71
    0x11540e07610652410180100301003100000b159110700c0d40d9521780401d0310200d9580307a00499190245840442c42c000581c000041e900c0c00940041aa89140340005c1040360138428003618005800c1c08014115481310031503244108036540004000c041c02d080851500c06028000300b01510309070811502080080340302d100a060a1007220b0601c151030030101305003406034850040040c12840a1400c140000403503108591240c07094485484004d0141c094080c0c0718050300900d0281110103000030001c20481840b000e80c00502164444c2d12030010f01105002501c40142c16106021210303010b64082100440700c0310f00709160102c04145501034445504000700000f0821038440e9460700c6840340740c0000020541142440d41160880c00740c58034080704920b0040c0c2090581d803c05014180040100001c0d1030701a00080c59540c1c8020703481040303a0300c8100b00040808150b03003041070365010441200204c0030400066030403d0203a82803030481035203215100240d0b401198498651500441d0401c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 636199829 1250 636198579 636198581
    0xb09040609180302150906160203070f0c03060c03060f05040905010b09040f03080c070b0609060d2a1d0408030612070305030d05070e0d0314270a0e0c1c0b0d0b0703 72
    0x1701c83c84c1d080c2070706038060a0440f02c580c1d4500c400b5004c0440f44010715040c902e42c034020070403500040e5000e034090351a26020308010130008407910083e214241041114601c00e40300c1d1240304166440f1140300d41c4010b06190901005044140c01102d46c2c0d0340c1c130192034041d03076981c600c49446a40b00e003904400b41c5010349002406103c01034440c1c10504001e014150020f124009850351002054400f4a51595400001000300406807400b03450b1b040c60600842c040056145041c82e02000d800d440c5900e95964242006145000c82c540309802c10b404010030005901f150003943c110324000c02d81c0c07165081d12601e090901000da40210755030b610004030200b1841c4140200c5610144a04000e80da410211002c9040c0e021540e100900304680c11070240c800d01031800075a010281c003a0b07103100e80c1c0404001000060102041040e2050084400004140c09202c1c0703201d11810b80c03000b0090030041102e542c0d9080034507003408140d545440b990761031301c941c4600c800d14048600401004d0404e04200c20003038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 636201079 1250 636199829 636199843
    0xf03140406060f0605070f02010c020a030602071511040515030a0605030f0c130506030d23040902040302040f0519270b040c0e0115050d0b060301080f07050414010b09040609180302 79
    0x80b00707226081c041000801d40e200d2000395a01d40a007003500200060342f00103a0120015080104810720108109040c4442e00001400000c1100010030035040209080c1400e8044d51051035030041035424162411004400a150091160340000c509282c48100283c140404190aa00d6540c41105008120300c0e00760403901458078560b40c00c20450a03c0c10200ba1200030110300102030043c0b184003088103040455104030300c100040b001300d460715103410115000c2c0d07100780700c164462424002c0f4000c901d20a481f07058040c3c40403034802c0607203100d4521a800505140400c805c0351001c07406e030081d400c0005007055809213119000318041803905160075403101001d9007018072100208401070098030000c125591804100741041a1188901c2d8011001790020458003500300d41c01100010f038455000519101c04440c803003d49000e10b40f540140022541d40845032004e25903000010402c004147e8018204100003a0000c43c00540b11813606058030890078400030341c0140e2120001c00d150341800b00c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 636202329 1250 636201079 636201089
    0xc0602150f0408030c091305091f05070905100e19090f0507090614091002060906071b030e0409050115092d020c0f060108010606030b010f0f0f03140406060f 69
    0xc107406080a8031403280c0d500004001301114040055149056500c0c040c0d05011104070800a120f070346030036507520352250501c4014841c030042000002014441c5800744501c6041580d5400c40c2d5241780030200100840c10107802d2051040f1038110410743c1d100c5400107021718081104c6030001754500b442440454000429507900c1e24035100502403020f83c88a00402100c240c0d2609281e18103665507820641d02c6006e490300e5001c4c441080a50826802086043c0316209070810703504940c5d0b44010980d0342d0400c880324072180c1c00030344d601080086d000d40c42c00700c01d04102620000c0c00d040c40f6074900b03003140c0107400708105407040742504220b0300c10503004004501040301422000d004004e286000c1c004103903010a4891900403813602c11041d0b04204030580d0b90940c40c00c9401c1965a410302500074038650160000107400c3c0126145294010f050844c0002a0f40c0d840c20340540039910119805c0c401082d1081c10146c40b4a44200c8000340800038034000e074007414000858900d4100d128921146940c06 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 636203579 1250 636202329 636202351
    0x70b040c0e1e27070305010e0607082a04090f0b100903172101090e060601111c14130e071403010b030a091709090105061314040204030c060215 63
    0x1048004200894110b4103200800d00d41107808682049500c40305a00b20f120340c4198880007040c00015081440f50a01c00000c0e158030391a00c0c542124811000c85001700016402d0380a040c10010300708101d5110790400c4145804d0136120400744003501e504641c6081000d03280e000202e0240b510b000d0520541125061480b10380b0b00c3c540e2a8852821601103902081001040140050b001c0f42400c0c0b01c001c108000040140da100d10780d18005000f02c40e070310210780c49514000b45040d40103203041e48901c20610010300082410845040e030050b000070b90744081198401f141c5207811903007406007103c0c0101c2403400d00c0b06030901060907203001c4000e00c540304000f924811b4400c030760300440449040d514041255070b030300e41e2044194406080841030040c111000103881404149441c4050035010340e046031804251b03680d400c1040494010350b600c1302041810b4440c100001d407202440311843c2d140107403015003059640c2e20782416040c426030002c40941c102691a030f0140b60f9000d1199400030700c00e05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 636204829 1250 636203579 636203611
    0xc030e0102011a120109050d26010302090402090730050a02040b0f2503030e0625030c0905060f0c070b070302070e041b090b2b06090206070b040c0e 65
    0x608000c03a00040300c40c40d401400c044040b000224401e4011b000c40540003811030381c8101c46207800505844006048140f83d801e1402ca89101303448164402d07040f00d030020300000403521a0b0f000c1010054001d40903201380183c40d16912001c0506429121005070181c00300421503c8808440c0150b0340020101c6200718810002030007000c4404e0280d80740c1ea030084289580364001c02c000c60210f03000d0b454040d48601c000c80250300c205540341e04403a0000c00040280d0300f00e40c56200e90010603052114141c0780b4108074104003403816100350301000060f00d40340b9042e02442d1f42d5202140640d0311281c0c0516201c0701c009403c04001e40d0401c042c0001300b880c900c0c06464a800c5483c000c1d1945014026040003011020204007801a00103030244643e56034030799880840d076180660b07001060b05010700303406101241a1403c24212103c600090381143e00d41e20b82c199070055030707504024400701c2c408a0784603005000a4000c51b110030801e52049214030244440c0358100044808252002003c0c00c030184982c0b1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 636206079 1250 636204829 636204851
    0x4090b1b070c030b2d0a0c020604021005090d060f0c0e09070c060213080f0a141209040504061b0507020a05090106021c0207170601050a060311030c090d120c030e010201 74
    0x4880001101c1d08040d201c00f440c2c1703d400380302c0c0112010300821190b01c414042207a20414401200038040c5c5aa81010031502d50756000580e00d86400f1500a58084094107008450b00d011310020410420000c041c02d188010503610f8804842c5a0810540000c2d603c9006a1049810501d43d003913040045036500018070701910010031603048248000c0c02c40c0c0d0040750840c02406880190f101a1003001c01b41c40c41d1200001c1000e9440d0b8150800351414440b0340c414423450fa13400300d001010161f50103401881c1c0000a002c0c040540009081102c40035550400c0d80300341c0500c000c42894440c03ea60b50300ea5a01d10a00402100c43c0141c2c01c0540f00c1c5000c1d000405c5200d400181c3c01212403d880130881c1d00c2e2805107800d07400c1882541c000c1e01c1d40c622000904054180c0850f800b0f05982d801c07500401607a495000c00c6044405a8540c02d03400300080000c5001307d54102c02810340710100178602c110100c503542d62401078084840300c4c02c1c041407204540100f0507411007224400c1104c00c0c402002504010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 636207329 1250 636206079 636206093
    0xb0d0b09040b1306090606060f1206060e0418080403210f0c06091103060c220302100507051f02030114150a1b081b0f0a08091e04090b1b07 61
    0x40c089061880300c990783e001c10801650020042c80c0d4105030b0401c0749039a520000780900121100d000009421980c01c0c6910540905c1203605032040c69660511801a41092200401180c200516034203040684000001c000c81c3c01440038521415484070300030740e00120305803000354051101050100002c550b2030340603840160b14040c160800c00110307050303c080c1480da440030402e41015800d8062030b0100700d64507104030010881d00c90187c400500c400c1a10030101c40000250200960140007040000100ea107c0c03c05070030f0bc079002d1801c0c0c513040108103590f140c0001d00f0030070141055030048010020400c0d8400900d011038002d4444d03100c1c102d0900308824461151041240a00c0071104280d001d101c2c02c00254401d19078004800c40c0e4400d00300d48a6014400c1d007840c0006188502e42134a0302d81280810819081540074a0366820490404100041207201d201c50010002c002e00180c407040d81c8a01480c11020300410004280b0b040840c0710700ca0030030300903d030081e40400c100100e000113480 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 636208579 1250 636207329 636207331
    0x309130b0409051203070f1806031112040606030303050a0209090103080a020705060c070e161403070302070203032b090b010b0c030f0403121818090c0f0b0d0b09040b 73
    0x142400000c0d155503a000003001441c0c16030000d0003900c50045030075010006038000f940500502d40304c03412000c1d400901250500c002005002500403407140402c180d80c080e0b0011611001e041c582681000c031502039040c5502000c4400f9200251919810001e042d09803140030340200c151413080d880e00302e5680c00300e0b01100301841f00034070304080010000380080c800c0c0803280c0984401480c1584e02d0081915080e9168150301030a40c805d840240820296100d503219025000300a40301c070500c01c0d001d1a030000c03042d08010032080506400300002c1005076400c0c0300801c0424094400c41d0000c0e05801100d0900b03581c0250405002071920f824040440e043e00405811101c0004000d41e035103030700340405070840c01450170034400402c01240104c10070a00200b0700c20902801d0b03a68070101c4079410400c031141e40142c411a1041003400396580410042500081e200c03900422080c40c071540d0b6200d000400108030750210700744407000300c7c0a40c00301d030950048040c400c1e421969034840b810700c0c0e00c80100f00a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 636209829 1250 636208579 636208609
    0x6060c0201140f040f180504030c080a030923010c091406031003230c19121106030c0c01060f03020603070c060608031810030603030e0f1302041401110309 68
    0x21140c1c03034281c50918110102c401e010607501d612134440743d441c3d070a80c48a0b40e041c00350962022020030071a0b105505440b402c0c5c030554042c2d403808401003658442903802d41c04407100e00c0805803035540c0c0d40c01103141c00b52400000701d8a007444050050202594a0031208100160020810f882100300304203d910400381c00c91503c100c03070303880e84d03034032003c40f8001d0100c0560720050007010307010802545184168001442d9607007140030341c1c1501d00c41c4410450214480c80c110781d040e0080e10003d0100f5011240035041c1c087c1304400303001040c0d002d14000703034164000311400030700c040c00001d458031400020300400005001d600354107001d040c110703030020b19540130007450b11041120b00c085070b00601c1501d0f0800002403801c00c05030382e90b80d074211246010f010740d403002007030240000360482c0090512078403a960481e50142d54001818020034100004840001c3c0c030180d110940c114540380320320081c4010b20040c81c24200b102443c40400e00090031051003c0d000c1039803500184403030710302d030b81380c1e600307051900d907 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 636211079 1250 636209829 636209837
    0xf030c28021f0209031204060207141804060905010504051b0607080714030f0406020c010f1e050c0c0a090507081e060f0a0b070506040201090803071a0c16050303010e0a06060c0201 79
    0x20b058448004000d0060f60009a418825801d1402c54006c2d80401081a603000b54241d54490b51200c2180047d54082d10b000c54024501c17203215901d075000143c14030780141c403030603000c0b40419560316a54292001580c6c05d540d20303000010320000c0c5154020000c26a400e0582d0550704004a0f0f456004c0d941c00b52880140a111040300031280f010301c18400c13a403480940761012600e0ba13480301002951170110100d8140818880107504003080e01981d80407035001c00319956101c011204502c00c641642002401c4c0e0183c2c49841d55000043d40c40304d5191016182d034510026072480c0240c4018030064000d00807110b0311000b004d042c14211310f80c0f130340c4a0b4005800d0f034092110b07100450220340b40c880940d100d0106c018010814404011021070150f000300c0c000d9807003c8181d45c448141c16100c0c8a1307802d004000c0003c008002c403d06482410b004e50068600740110b060004100032101050003982013114507030000401841a22840c1c841c0d150002c0c84d0001c104081410301c60064611107204c40064184 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 636212329 1250 636211079 636211123
    0xb19080c0d051b0d0c03200a0b07061104270506010e09010603200307050a0201060f1d0c0405150415052104020a180c2a030804080f030c2802 62
    0x168890700e4441a4050744000c0d045035040d600d00704000c40c8440180a4087e02059041203070251603c91400015600900007e507e0880642c1e80c13074004041600c1c0700903200f0030500c000070b50450340c44410702c0101c500b42d40c03100c1c401d40fa40c0413140c1200c100803c49414484860b050200e95100c0f14881ea0648840d0308002072040c28030540c0000c556564844420980c0001041001d03080e07008024000200c2150020701c102d41c0c42d110a200b451700180a03049030303000440f010582e8569100705507074100e4450f080040c505501d4802050070032520b0035206014171030002d41008000d443c0d004110301e00301c5614285045c1798003070314030900019000004040c8241c03e04040b4042d559080955030003070050307427540241607501070b041c00d02500c000c00f001404100c425a0617030020154091103000c440d03110740301c414510495503007580c800070f01420a13201c400d000d10441818544180056000780001134105485003070000b400081d24520300c20340c06894000302011082d076900003072000801c214441d441c00340 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 636213579 1250 636212329 636212383
    0x120509010c0e100516060227030d030b0d0210020601051914100e031510060c120f120204030b040c090b010207050f13060b0d060816090c030b19080c0d05 67
    0x30340294116178015421108054040104960046c03d04100d0000c1d140d00c12505c806070b0414940b84094400d800d50000320369034030014401e911500600d500241a210950415004a91208409401d0f0005680000c005000d0744c43c1101c0512100c1d1241d4100c96140c4e418003050407800d01e049500386002d064404e600740c3d4060b0003503804200c20750025003113500303d5880c0034070340c590380384d0036268094403400c1d501000c6810341c403820071f0300100b642182d6400c004003070941c4202c68000c81c8448800c00c1044d02c000c3e2a001e03007201e000400056002c1d00034030306141000c3c1881132040200e42d01c6003449c0e500d0048481341c1c07a60045041d00444108484801c0203008141c0813070b070410305205424010b9454100045000c80d1940c010707060300700d00140b040050903254614a9522440e4141110a0000b02c0701c1c1042074884075041b8401c1500c00345008120240403901103070b40c101c0c4004c45403501d0000d00e01e051200079804c1102c0407003014100c45812500c80240c03101c64690036040c0501c04149400c65034550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 636214829 1250 636213579 636213587
    0x1103040519171207030c030209030c1905030a030908071d0a09020f060f0d0b10141e0a0206040302330603070f0e18010c090501032307120509010c0e10 66
    0x445000e903000301550f02d245200c403003d0081c40c216003403804603240034860000c070b0b0300c24402c3d2006100054001d0012134180410003040c241420100d010f894960b45001c01d0988007480f194000303a104c0d858017220340d0b0600d64284e0030b0558a03003016016615429400c00d00c01556105150030100c0c0d03400006a0356980d00209103110040e00e410b070b4028900058010074208090000d0480070f6812a0412a89424908021483c2064002040094004030500080308a038400501d202c9500c0e18820703801080468014145800c10305400c000b6822440822082c107405005180041c3c5e0003091a014201c0788034080d1041c1821101c1c443d118001940000c2d1031038800b0031210014240b80001c0c408040d5843c8401041c0c1b071001c45000703e8a5a00e021000e1440005000c2e04003440c0082d2120300096050030700460082c01503050794103000b11b01d0400c070030010041410f010300801c000c0e43c800d0030788005070401100341d07000900700e07400c961314201c60100125803000c0400c0500b941269620204200c00600725 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 636216079 1250 636214829 636214853
    0xa050a12020a050c0118020303071e050118021f020601090f241a040b0a0e2d03151b1e0f090901050f010807080901091b06031103040519 60
    0x4400e4034400900701403400c2c0c010340904200c0030044001c0c481c000b1050360040380c000505c0002074042e401031080d0000210b10710403200500225800302500d405090b00d840f402d5501c1c14010140c2015201280c1041d4140b001c1604801140e00c40c40002210b6001c1c0d0007540c6950510440b04030079500d44a12004802c2900b1080d0024900b06641030b0380e400100b00180d868206100742c5007c14207452428852074184400d4030100c3d0044c884160a1000c01c01d802c0c2c0e03400c820500500c2d0f00280e440200c1c0710411740345510100031003e651801414071402d10078141b40c559082603c0d0b80c40000d01007000503103d1400019041e2888927010f841e102c882c0300c1700d0100b40c40003036212051011404500c180411815001501c40402c4c100ca40f10b42030f2f6600c070284002c0003030640959000030407a40000c0c07600d82c0508011500407904c0f00c0000780f0700c122515110910f84c95840304546080f4140c0341041425854018510600961080707103281d800c0c0355442540d00c80d49070085040018020419805101003030a1f07030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 636217329 1250 636216079 636216107
    0x7060e030304121103010b030715080a06030f05060405100b1f020a0c1707093c0c0302030610020601080a1203060f150305070212070602090f030a141903050a050a 71
    0x4004400e001c1c603004c0a802407280c0254020741c80c1c2580600f0318a00080d88804a800107034034140c40ba2080e2204444440005008144558075130740000006121461413072a454018005011181058034241e424811b8081c0c10011103070501500070603e0365840c1a00d0004010b030045200f080c064200280e04007180c090000e000d00c14202e500154403111140031814a0b10701d0000d0f40c1e106500d031000503013140c4040081880369500c00d08040f000c800b400e2001c00b0b40c1c0e2901d030200d940f0304d1819800c000c15110b51402030000250080117010060401c49980400400741d40060110381d810b02d00c8155480d00207000c043c041c0c0440c0d0b6480340d8024040c0d0f100300090b2041550002c10552945250700fa07404051000c200007a1805002070719140c03011510190003552469054074004090715144042d401c910075255002e400d880002c1c51980e01000303814040c610942030328038400e21a116113810407170083c90404007a040414020000395109088990b00d1115041c184e4481042c0c4e0001c4456032180198 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 636218579 1250 636217329 636217349
    0xf0309010b06270d200d0803070e0414160c1505010f031416050d050c03030403110306130f030302030a09020d060e2a0f0612040b07110303060307060e030304 69
    0x180002c0100526200a9040301030005582c0c02110b5100f805484c2030041005131030503422414030b002d2400c0302c00c000344969500070103240101a03292038040c0c85900c00d6400401003402d8400310b0b03a907410240114204d0310401010304d48907142901c407070507119806400e035004011038100c50f1001c00c44408031501c811031248030200070941e100c1000100d0f11096000688100d41c900d81c3c1c490010f0340014280d160650809034ad804a240340005014400c4000c00044130750340202d4005007182e840401c064401940600307810015a44044181030400502415042e045c00c0c6900d800320200f40c04102c0081d0703640d8107290040c3d0f281e60341000d120052581840080d8003801c48007101090114070b03001405242c1122003603800c0b840e0140c00e00c22004484059003040050b0041c84004546004501d20210300b402030507681c035010320300c1c0e0440e48580b81101c1c00c44400c0100020b010403143d0210b015913101c08074000075882c6092a500003a512001d0f4400c20b0100011400e03180c0b47e0f51014070036a0000c1240c555 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 636219829 1250 636218579 636218587
    0xa0905101809031725120203090d110a03210f1a0a06022e0209090901020406080a0504020d020d05030904090807050c06130311030102071e0312050c0f0309010b06 71
    0x199107010b4690010240c0026014007281c4140e0610500f0f5036000700150071301011145039000c40c0390021110380400b14203100803007080c041c1c04034443c001980b2559002000d00607581554801600710480c0d11040e081e103074001203c40f000250000d910050511246040c1100941e150b40018081c1060280084555080103d440040c0c03003a0303041051031500172100e00090b503442d464202da89138038085101c18420381405054014045840c04000f81361400c08000d850460504041040c818055072880710a0398001000c010a0703a0103c110345d0820389407201031006003080c1e0005800312030108400391245510b07000500400c6410401ca0342840000b070310502c0411014200148141c020100035903117405628140d655174902102119446e400880c641d4960341e0440d1906001c0c541d07000c21098056608000700c00203d10090800100400101c0750b4002c0074840340740c01844695681070784002103060000b03001c00c070300881080e41d107011054507080d501c0369141c0f5040340c0548500d9400980200c0005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 636221079 1250 636219829 636219869
    0xc1b07031a1902030915060a0f18050705040e0c0d060306060f0806090604030f0c06180f111009060f05040306020309160b0a09060c051509010219020c0a090510 70
    0xe240c8510031540742c4002502039825a50000c103a100444100d91550000c3d036582c5071002401e28110f80000018050040c16911041c08041611550708592895180f0455030300fa040c0f09c9002d2154042d0340c03032810341e041520344415108000b04c083d064030f0151101040f004000d404650044005540180341480b5580d510010b16540310428001d0889a006140018507030440008505000701e0303259603008465205070038100c0d540d512083e011228107481e00f42847c410302900712180d04403401641d065a8000303c61601804174001301d004140610f0960086144050b00000750030300310303682420100d40c104041c2070101c40c24883c40c2c0000345050310101c14801c010500160070000c00302c50b1600c0181582d110842d41c00c003400360741181c1c000207006c1c9100340328061140340c8028482d03100700c0448405403000c0e203d4020b4a1400c44a1740166980424007a0000041d0010712083c0116030002e00394114581c000300d819400980104a40c4941740c0000c107200000b4451104000e021484d050700c5992880 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 636222329 1250 636221079 636221123
    0x212031201060f39020a030c0321020a0c0506032806030606050303040b040312050c06090a050615090a0b0f0a0e04050105151c030e0d030207080d080c1b0703 69
    0xa01c104030016180401040c2c200381c1c0c10300c1e2038004101905840148813880214001e519201c410f003281c11680441d400130000b241c4c4e644102c041c61203800704013120034a1307106c001008900200c0a404550120300726001242c101c0710f080c02030b070344152039159403036445182022030305403d900744401482c194008290301082561003402036a104e01d100340005950b400800d66680a03034001d03060b800b94200400c000080d0078403094180500381c4c1c2420790800300a40c0c0954208001140d07030100c0e9401109071181001030900803198450488800d000c00c8ca25450081001b005004240202c101c0d512107496541e80e54990040344590001003601880c1c0341c89620301104040c0554045809600f0b02011501860006000300c140810151091420307076002e00c1e504400c4d0300918402d400b409074a84414026490740c5002d00e445034000d070000c11025242010b90f6250103111074403402040312580c14028100c042d40115000e08107040c44d1845032032814601c180c2484500d900091440c803603000d44900403101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 636223579 1250 636222329 636222347
    0x102250f030c06060f0b0304051006080712030e0405010b03060f061c0207060b030303040309030302151b1c062715050127090f05310303020c060411030f0106050a03021203120106 78
    0x1c101c9c00c1d2050058603102c07080a503107450281131a143c204c08001d011080c0703501007841b1118024504110455013103004074003140c4003a040441c1400e0000104102c80c142003905c110183d500f9036081d49082103841c502d8104030030b100c8020454940000f03024051100c5504006120350005081c1c95480c1003a14000d0001c0b82e00784003c501500440e0f8001138099104000300d403107001404d00040760910000c81444040d8440c141d00144290724101c01110290103204410207404112504400d49869021600c1e031010312030324100b03510742000d0519005460818070b050807914203090034a040c910381c40320403a503010002003855008001c540c0001c2e49a04030781000030011850181000941c603805034030817071119081100d40813441100700c6400600f004804500e6401e000e4039005040405402d811170901070150340c2514690ba08010180152a0604c51490841c03000c03402000172910b410b01040d140c840071711010344030329031824030002c006c04140100c45184003008051105913071903443c09440441 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 636224829 1250 636223579 636223583
    0xa020f06070c080304063b01110403020a0b03040c091112011508010e1008030c07260a08071410090c1a1602041d0102250f030c06060f0b0304 62
    0x108000101d1809070207a04502d00054100c0311142ca59a25a241c020207010072003900182603400030a91154030641c2850001c00d00007003074440b100c0e17902801c0d14500b900c403896616410503504101c10801665601d0540c0300b00c4207001c4000c2d440e0794850400c0c080d118a10342c4080000da041604511404010700001c19040c0b0781d00e20011080c4e6250880812140c10706281000860f103600014000c0005c1086400da0040da112a12160251141c030b5a82c00e581054170310310040c2c2e000300c10610064104a4a11900c0c01541c0710307090700f005c0801d410903501ca00c0440d02400c40140060408180600e4080b86e600e1400060112480001c20345c1501c00240407900c81512000024134002c80c400d10080c0040d00b080e03038009119070a002100311003a401ca03400303d808aa01540c0c0c1c03020340b480c4901c850210400040c2078000141c0740c82e01a255a81c61030148200c0c0211040c0c0d034002e01c8005500c803800303080340c260507281011080304280307030800c001c0085801c9084805452940000c54001140c01584918 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 636226079 1250 636224829 636224833
    0x3020d0c03020c0303040b180d11060702030910050d09021809060604150509060f042a05160f0309080f010207020312040f18110d0c0e09070905040b0a08030a020f 71
    0x280d0000812002c038080c1c5064080150010404540400d814000540e0040688001806030b03611071101d56240221881c0d1540114607080e4044e082c03840d041c810302da40440d660014610344040240024042c585a81244050050200e00e54490340640d5001000299006e4507002c10300a09a04400d8a01c0040328105c54034402d4500003000350400d4003c00348030707800310078000600c9414601080418103000744017a40186a4001c2e14078a6038440c0200307010008a00201e0f0202c030118000801140600001d031030070301201304500c0018882c10b010312440715401100300c0108000034030f4119100c2d01554081c055a11400709250803ca0b0706500500440d40b089044440750641c0b9803020046024a125514444086a104009005003141ca40c013040880000000f111100c140c4805900d410100414080300c0e550b43c4450300268020101c08816181100e0808880c07030040f0006100c002c8600841d40a991170b40d00c12032041d11400070704009081755109903034a0700b54000000b0365800c01581019a02c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 636227329 1250 636226079 636226091
    0x10090915150f18090206030f040309080a030203030118090f050708010b09040809100c12090609050105071203020c031c021e0c0d05090f1c030306090c0804110301021903020d 76
    0x341c01c4050454003262542204001d0940c603100040300720580d0080c1c90428644c8802000d0700596541c001148a504055145900c50405040040401c9100c2d003000025034031604181d0701203900003058904550800d6424143c2040a00b81100030b040d08980007041c0451840d00d007400c00c840403854100352000360000708074002d801c9003004882c080070f0340c0207400b0000401000416041594801006039102e0500005c4407245c3d0380ea1030709414020740200000382c00400c041c03118990061800c002001c0900c4e06074280159034942501b80c1c580610803005041d170024010500700130910555040080460280403804e25204520010394480c6142071035001101164150200300e040940b1844084040200071450708220195050760100f655554002c40d10080b01d4030070fa6070f0004440f500e01405d502c0d03d00740c01042c58060169203030364004556242c10400c6001c84107034400322a80c0d1298120101a21017a05600800d009105030b0b8654200008010700c10301040c1c0e05500102029220035004100d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 636228579 1250 636227329 636227351
    0x110c01200406120209012307051227010e030a03021f020c0303070e130c0c0506160c08091528080601140c0114010825050f0910090915 59
    0x280d0300c1540248000714082511034840311903540d0113800740d8241810107900d080300065074441d00d2600c240104031207180004802080140a00404070b1000c4182040c50500c02400301c021030170007400030804400d03200000c0a03441d0b680b0513121201007940140c00e440088000d810003c1d107600e4903048640c440844201100403062082c402c4403402000e1101a5041d5103a803082110320407441d804140c0d00080f80841c03902c0d074180c01e1140450700c085544903000b4811052030b2031810010014200d00f00810640720900c1c0705c0341c02240b0318040c10b074040b40d501e82d540c1200300040c4284945084c10614124003042c9040114002c03102c50324002d5801c900c108011003100300480d5210422500940014101441c0c0c010003441d050140c520210400008501c03c25102498000800300368024070103903000529100e03401c0304c00c6803c0310064840d210b81d0032000c0e0900003c46c0020201442d80c6010307144000008420011581030321029000f1554244460500341c10080d440301800c1d0303d0407121170300c0c0c8040b4070343c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 636229829 1250 636228579 636228641
    0x30905070e0103050304180f020d0606120603020a06030c050d0e150f1009090f0b071d0f0d02060c070e190606110a14010f09150507020a050c090406110c01 68
    0xb0490381c4c410001c514240c00c094807143c03c81340783c085040c15161101c0007410680b03101c3c0044d04070072a00f444002052072405070001c10a002000d0605022450600c050015031280d400c1c01055811030306012400c400c036460116020b1068020b01001c00b0318045a40c14810030204403000420000d008480080d00d540c0b8002c2018801560020080b40000f0020805800590022a00d560054050001e104000e80741d4825080301162200300254100500301040300d00700b205941455002d8944d42214000c07440420080440048080e114400200d84c00310300800030403100c001362032003a03aa001c05048ca0070301d0088024040b29808019804c00340003145140c8100e440c1c04103100d20000403c44132030030307803540070311030401c5082c0c0c00980d500c07540030100e541c51500800300111320415288140c0e42241c541c030b40480f0380c050122000c40d08416040c40114070f0000394000c6a81c01240c0750140c580ba980f03851030090119541044a0b400046000e0000e8081076109200340c0a00300301c030888207900850015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 636231079 1250 636229829 636229831
    0x30b07050f03070c2316080d02060f131e03140c0604120320030103060c05120705130f06050703030b12100e01020f071b0803030c040302060c010f0c030905070e 70
    0x241c82480e090000495140c41100d420a1a5004280310390000c1c40114600040710710501c14004aa4402150400140035460020000341010b40c0602004c8040d840000d48656001d407078603403800c01410209031107140c3d040502040c81e034800408104060141c120700c20b00c241e500e40139400f28000824045000303406008644084421001502c42548c9559450701d4400407050341c101090354a40071101c034040c02d8100448002910700205440791303d1031500c20265000482000200301d0284403103040301e01c00c1e0312502e401120504020351900b40d0040489000130040d480180410407800340021103507040001407021a002e50780c01c0c4880c50010342031107007c281b00500340000d80d00005411143d102d203680105551040300c80054688803008141c44001e0b082041c0a881d00401d079403420221000328050302c4000d00c20310f800b550440c40c012012940c18003c0b0b00c00a401642e001510116000082d4405010006030f00c03000c200701005000700178010045ca0500320f485105403940801c949400120207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 636232329 1250 636231079 636231097
    0x17210f06010512010b0c0f0d11160b0a12242405030c09060405031e0f010b01020a11190b030603191515030c080102030708010e04020a060e01020c040203010b04030b0705 74
    0xc0c0c3c040342d01e084a0b60006600c045402d403070f1409094020400420140a00c6d02020540e0303a030690312541c80c90846040c04040380d8141c0f501c841004c0200600c11082040c1c0f07004030400c1c1095540c00c0c0d00e5103109409851041e07120b0384030003a00004180c41110b91400b0b4026160070b00981100003540c005461602d056181d02400402c1051001401c1d0505400c0200480301000d0003490403d0b03a2800400d01c0d18000c45004488805030001c01c0014280c104042c1c1e40001c2840b009015094005002030345920190310b015080c11f401030310310462512003580a03650f0200f00d06076481c007660b440711904100c1c3c0003a950381c0d11a004110224500201020701c21541c08d0b0044403c415064540c50044d0080811425550400310b04590020114464504440041c03015100140e070340e01e40341074010000e060582003495190204400c0c040962503540d0b135001641d84034144070032545402e100507172820007442505544640004004201d1083d088041c1044278410001c40d81103407070b40413058805014a88503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 636233579 1250 636232329 636232357
    0x105010608061002101808040b0c06101203080606040803120a0c05130902070c12060221010602060f07020304080a11040509030a1407060b041410080309030a17210f060105 75
    0x4d83c0a600d05a17000e40403020a02028410301720040c0d030b91287c10b812561010904002c0071603d007410403020f000043d0700071607011650f056035050800d007440030058000b000c0c02f000940000142e040d152413003120050154201201e45803042c0c0d0221100200c4109c4000700210709003010080502e0003502a01d482d00b06504151140508102450000390000c0794140c03603e81c60f40200040c40c0070800c040a008502440026a80e58104e00317100216172001800d190b1083e014100402002d94045030203030b085550f4401481554481c0b000407865809940c000845a0041003800000c110a0003070aa17016102034409016580d50070595540ba8040c3c4103003070011840b211234445182c48041c005094940c802c0c40006510b840c86c41c0498100c6805080c00342380e1002d02001d0000c1c1203643e591043c0140592001540750903655004030b6120004076400034800074050092154058846058800520613041503910120350720300720380c01c14081030f00d03240080322480c0041183d42d4071a4003110b503803005d5500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 636234829 1250 636233579 636233593
    0x90803011e05011d131808041a04050d030807030617030a11070b0f0a0201091a040614010305030d0b0d080703051e180d060216050303010f05040218040b010c05030301080105010608061002 82
    0x1040c00380c0c2c1304c85d801c4000701c1a950b4110891081080e10b0070140c03441e000b8020141c4a40c2800c2010501c0c001c0c4001e1118541d805100401482e0b5400960071181035151401d201951100c400a801408aa80107440c81c3c245074890a444154000050143c108103a914200502c000d44484c40d01c0b901310380034490302030004001501e0f01c441818001e107191402480001081c010603103c0308000c42140ca000303208025540148000c2c00010300610803400405080345945500d103603212540c903c00c00b141c10310565150729204003d6a1348540c1c03a024203412442e41d41c4c0d81e0015140003406507109801d000005442812a03042d03503400b850960744151007145065406403410300822214014404c0301302e0346c9603020064184d100c220b9800310a42240301d440119200d50401100740403500b001d810550159105101321131408864800c40204524140c400003022801040101c03201070000c80e01070032030311001000240072141540220304846040d9550280d03a1205000c01059212000ca04401a4840300f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 636236079 1250 636234829 636234887
    0x4050a12120e0303060423011431061d0c0310090f0b01030b01030908090438030c1f030b030102040f060801031b030c1701090803011e0501 61
    0x110008061445800c02500c404001c88014040e55890076422070181c00100500402d814a03004151006008201070b1245042d41c2c01103e55084c0144180340e10154900108000c039102d0303406102607010a00c00079000846d618161040141e0f00725020821a80303044c20000700c441e00841923103400c02c906e2050400c55180c4202c0c0064a41000c0d04440098401030300005181160f41b051512071001c0785030100d9590101c10014049030744403100315040c1410201c0c440002000c0500304d802c0510116070008280501d1f100305a20b4030003004448034202c21248043c124501d03170085804180e036040b0107d60394010440c007481045505c816080c081480c08050700501c550103900b0034440d1030400f4000506080d901c8e51040c41c8050164480d00c04140300c41e00510900c00800c00d0410321003010b450300810103156a50342c01d0700f410248a440744203943d4a00310081c58a0079040324658540100b082900c0303513181d00715481404110a2452040c000c0c0030800142540a0304891980308014880b01609420304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 636237329 1250 636236079 636236093
    0x12030507080c07051c0201090902030606070807050c060a0809010b04020906070b061206130501060e04051c03090c091406030114071b0803100e01090b0901030303020a3f020304050a 79
    0x60b020803030090203480c90100c0d0f07948076038145e100012402002c0144090703840c00003408901d442d82101070300c68010810000f051301d0f444110344005610581d416036480b0340703040860400c1809507505a00100005500d510b1a40c4a440640688001070003006150f02c028208000c901c02c1440264100d04180091400b05d0302e40c0c07041903440400500104140a6004215824001d04803440e005440085090700284078092065a01a2130615000580342c1042e4031599600c650700d40008989810301990000d00601c030f0f41008200d04d6000c40303c10b40b141d0f00c990644c8081c0071007016001d003e061400009108e80717014040c91181c151005000c14507034461590032200450031120120034940c401c92008002080400198030039140e000c0e40c07404160400c17801d200401c0069000c0c0c1001410207003000c5007551003000003411254103081c01130f660704001d24240c401500d15030000340740e00800d64850266200309501c1d0310b190310281034844e07001444121a9012400160b6000d02940d0180e50144001911 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 636238579 1250 636237329 636237337
    0xf12340609122a0312090608010e040206070311010608010207120e0f24030901050610050c120d0e0f0a020307060c05151e0112020f150a0305070e0406030506101203050708 75
    0x100d07a841d03c5228462010410510354000c841c003151100181c03540952186110020700228601421075501d003000f16008114050b0010b8416000003a00c202098056000300e0b0140391260028801c0554499416000b90070a03a41a0f80c0824603d10004d58203114601240c544c0c88014100500d60303510400784122603003400c06207050340f070b24110498030404d03644010314071402940d0004100b0b071900324244648002c66240301e80a1003018001d03008400e001040c8105c40b00800e08030540c0311030101005001400120076400e02c035000315040b000d1614800324102020364000d0381107600e01987c90204481ca4420a8005801034221140803619032441c030443c1a0000390411005002c108180c5800107629402e901180416000058890450406c0011715a10480480e0662941000c0b034200062501c07800c03452004043d40c0303900080f02d075801805180d6030032001401c100300003030301c3c1d1422603600c02c401e0720311034000000c42d11b0003c9d811400c0c1c2e070030710883d65250ba1028101010b950b219002500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 636239829 1250 636238579 636238613
    0x12090d200301060b0d0c030c021009051e0a03020705030c030d0e030102090a290306010c030e1f020c01081807051504030b07050702100e0f1234060912 66
    0x30410000c50940e0303024080d80e0090148580160b80d2400e1500c80070080303800314aa070394185804c00300e440000350f40200b54007500841039440440c58280d14600705003412090700403204482c15007010310120f05800640c9481c2d291080e001c80b4121511030382007607511901220010b91685c8555460486130380b00300272003d80b982001d00054101828078000410f030340d9243e0440103100403005c2e41e1445486280c0034a0b001e03140c4280c00c851a50402d00002480c07095002c00260500074010068021501c80510300c28565542201682440c0c2505c10001e440303540800c10140002d000401150020240c4240401541c90342c0005001041c40c101c14410310348200401804451024000080410a0a04021f01c41c00480d6201c07592000075104008034409021120b000300006d00d4015860b0341c80c1c00c1c289992501d01141d045105070b05890320580b4091000d4a140e20703180b08514048110303030b146010a80040501e8085012058030303000102e40120311032003180c0404142c0768013072003c01e0065840f075440c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 636241079 1250 636239829 636239873
    0xa0c06060506030903070c06030b182d0a0b061c0b0a0308040b120112052d19030f080c0a050a0c020405040c0e0604020c03220f030b01060212090d 64
    0x1681d07800015142d42c20449920650390000680c0408010a071013160010b0200d40c01d0400034440000046015403003d0300f11001c540b107803003000c10581456216460010080b51042c010030b0440300c210420044020386001c0d64840c10800d03880054504041aa0b120741c000345151024080010510360103000e015203607907000900004003001240100c4000c2000c0c0c003402034110f940300030b805101c07200007405a00400e11058001c2030b00000901c0801c899507000c1038001c6130055594100c13007134600440324158040884c421102001007102840b071400c424103000b915044508203044a054580d54012214442031500401c0348203070903409a80a4192110a440d0569000030b45034045001c0700ca00f60303410741320340c98905400c200c0c240040058541c000000e86040d030604c803200e40c0c099900d000f4581d0312188003060b094603d1100324841a440010020940d10210032956820003490342d980a0281e01c00500a0302100c202c00050711007228400e200290840cad02100854070703003503e0720548071076081d115 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 636242329 1250 636241079 636241091
    0x110303131703010b042112080903041d0f0f0702030a080709030206070303140a0e0a032618060c0315060901020f030307030e01150803040308160b0112060f110a0c06 72
    0x20030841c80c05980a00894182d1944e0b4500f040c0701001080c45c8464800039901100e48003400180322041198800a4207040000d041d0716184403450640c0a41e80014500b03002e0200e0095035466108580350242d43c905801d660079440c3c941164441c8903040f07800c0d10160740204080c00540b8441d14502d41d000c40c840c41c2c44912251207500040319a48800c0080d00040d071203000c402c40c4c03007841e100d0580d0042e560040400011f040134007496280d903b40040a0144044040d14102c0c0d140714102a08485621060b060100c0c5045d001d030059001c0c0c40d003c45a00d85c89001d00281c264034034042242c0c0114040c0010b80519800c201c1006480c1c0c0c80b0326a058110b026203640201090390810280d40581d13081d0320040344400c1c01c42020303421200340842c010300507a0100300401c120326012045a00b6030350401d220030366581c04280b00c0041e0b070960780e40041003002e03c04000603610b2120399009e03240500c40c00c424031035070560140041c151603040c20031282e101410001601c0242c0210381c21091a0311428000c150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 636243579 1250 636242329 636242363
    0xf160f0203030315040c0e13020d1e020c1501120b06031009060b120601030c051212040609030b06031b120f010908040e0c0c0d050a05040509070e030d11030313 70
    0x21608142d07040f01070012504044013140c6003900409510450390714203812894031500000381c1e003185200c00b0248065000807202a01909038008600c040c8181248424242000301c45000a43c0304400e0070015002e10200c07294106840d039102c038101d503042d005401021032962076007421000e01402803a494400c2c01c613210300341a018003a0105850080c140001c19002c0581889a40094525400e0307454211100500000700742040705402ea6505640900021030303400b00306031420501c400e6440080502143c0018000d52007013461080c3c0340b15a5072441c0a459440625640d4880310f062040e1000501d040f42400d410304007812401200520b084844540540b8042801c64060f90403d03202904000f03800e00c0448404061a0b40104088000343c0c03400304038502c125182d49144004030b0800100144c41d901d200d22500075038005c2c1c4170052540842e0305200714064914031190407002d00a0190701c00201f0320307600645036045044550805103155640e0410601078071025a4070071142d56900d017040c140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 636244829 1250 636243579 636243583
    0x15200f0f07200109050111070e0c090303040b0c120a080703050a02090604090203040605060306040b1b1903090302011a0d03030e070e0c0a030612081c0b10020102090112020f160f0203 80
    0x200c414950342c00752032070015120005003c0d8100d0340016061040d40025520180c9001504800301c40b101001c010268840c480d403042c40e0711035444602d6240c4070208001c20500302c050000c1010000e88021258451981b83e000042e81c05103503c040007180181c0001800c06010340c205c0c0f81d008002010040c03070400c041001070001d8105410200c4026400300410040050314402d4030327040700c2e044004003418074060b0b540008407400200480e2241910011110808070404240c40c04054880c290850030300031550300800074030907080c06400560800e50b20705134a407820303d0311404280300509440b9110a0940b401e80c0a459a452004181c0c406c1410008003442d10000c0d06010300740c0d900c4000d6030b80e041010014150362240d0007080c40c2d15a6168440c0009803544201c44004100c01d0f4240c4000081c28038090003811000030464200600008442039642e040d4010700254100362142c600701d10400320540c1c00c03405401c80f000d440d98000c1018407081c00c0c81d6032017641c000b84190064402c0d411980d000c07074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 636246079 1250 636244829 636244853
    0x3090a0c080102040501030f061539110109061d06070501051e0a060602060a0506180f1e01080618030403121e02030309060c0315030a15200f0f07 64
    0x303a580413406005075071f4140070348c0e1141b034522103003408590705040e4801941200042000c060089000b41c5902d86402003042c03036000c3c008041007903002913290070400d0b80c1c0d410700c2c03504aa005880ca55030a0040d8000c911940c140c80d1700c0d80d24098040c42c104030040d810100c0c07040d000c0c0e1080051200700c001035000d0042601c5000a001070001404400c480c0c80548400500a813070038504004052001c20b9000a00e168000c002110105558455602148038505400950b80c40c1c2c922540c20003809484030301c1e1180c02142e5050a400c2d000350883e1219070400c0c42800346c00d0540d0040750218001180d101c0d0040c841010030001d491138241d03a591411108290002d0090110b070100c2c0001403a4490405441004141400503518501c0c000e4110340e1515030040c524a500d62020000c00c400409a1000b1403070302001804480604c1d143c3e0900303400302e0b80222400a05035082050a0b0ad40c20190900c50300d4030310b0740d0004681440c07801c6020308800c2c2c00c505440d6800071024007078440819a201080 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 636247329 1250 636246079 636246089
    0x7091a210706030527010e0f12030f060d02060a08090d0e0f0d08130f0603060509370204080a11031903050a05090a06030b01030506061e0f2802071a0f03090a0c 70
    0x182004018205c58100404c231900314030b072500040c2428000d07400d0b2008695102550144952103030b90750b000010015880c05d80042c1d005000403030181002a08500b11034000c401d076400310742d40110081c40440d1138000c02140c4541201e03640039690b21720704207403c107030403054031400105040800405965441c1c0714140e10654122030700d0681049a56058482c00010b03080c156040c00d80c91414080548100c80d51601c4e403542401c0102c0200c2807115071890303d078070300038a0700000c0d50f580350b0f00c070000c0d0f6681840c030328240c031100d001c0c650a07280e51a000454046001400640d040c03640c51948054800b508481c0d8100e0038001c0800050245540786071140e4090803481e20001105d0030348100041c2200d500900c11409904100b11500c21282c03a0035a030303001c080000c040540e0b95166030030a00d60a004800d002d400307802001d95200030000001843c002085001c2c0c1c00c4031020b542d100b05500d4a024100340c0415240410400c00d0000b0172050004c690060b40c0c0011507004c40c49a50b20804201c02581c40b03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 636248579 1250 636247329 636247331
    0xc030c010621321e03030f0f0a0902090c0a030b03010504051203070215040309170c01050d11040801050c04050909060c030a020d14011502010608010204031208060307091a21070603052701 82
    0x44044d02c607561101c100d032003100d054011401c62800d45401008600c2c0039180310b800f10406400100340424680017008038a038058110b040e6803c2065568025030001d040c03105c0400d061040700349103818144100307446282c010004050001d06807101c0b0041c0d500240040045000385a45040b004500d0010a40101c0c0b295503956125031030024400c1954650001d9007070150070101c0016010317a8401d040e030b0000c518a1344001800c0c100003000c42168880e980c0190f02550070a41040300c81001c1038050030865500b0740b500d030001c2d580ca0701d8140c0c80c0c1904030341d20400c41c071092000c03642010349540a4030151801c42d100042481c00f250f401000d07840309030f0104421805007200c40c2807480e42030040c01e0051a0120095081ca81940d848a442c003420309c1e800ca0812111200040d0756550030031581d801461603a6042140044030070780c07415040607000e9601c1c02001d20b211000c480521460500300642064409040101e08058085025260180c01081510302c08c4080606480143c40002045141000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 636249829 1250 636248579 636248593
    0x1509150714030715050412081f1202013218040f050403030b0a050d0204020c0102160503070c06090e18070503010e0304080c100906050306030a080c030c01062132 71
    0x41d010414503010070b04c5050322828041448009603410792400c81548040c01c0048155075240701c240407014000b84100d6038505200303000075a904198586810850003030340d500201c2d184038404015030012000301c110040c0e444611075080042d00034040d20060b016000c15191100940c00081c00307031f49006680d1940290b41d4014001019054449c10701d981c00b042c1c2c0c408500620300b00000b51400c0c001100030340511303000038480342040c20a50440d410001d0b10340312203412000909040795260030040040398000403800380465102e000d00e82c00011119070340c2c40c0380350580c0c4030030b4044050785050910405501c600003012816640a0241003e003507600f02c01991540d1404541a00e010400506240260590381560609641c07042d0781c3c90075190f090400c0b540da034a811010030702c2c00100c014041c24000d000308404071011004002082c80414250003440150346511010f412024455a0801e03100e07088204440010100d2840a5400b26101c10046914140c0c00c044580000c01c2d5924280c1604000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 636251079 1250 636249829 636249833
    0x2309010c1227020303040509090a0605070302040f06030903363c050a030f23032b0e0a031d031b060d06030b07090515091507140307 58
    0x1480e4490742602004082c010040b61104071503030311004200000502c03401148a10a648041040358020000039268043da89892201c250710b40c0b013070b841c3c01c0700ca03a402c000108240038820b000361425141018140200c091604130260002d2000890840c11300c00090400c451000e4615280029a040000d8094120111204a040c180c101d600940301c0a8005e1744c80d4241c0f0070101900c00c12504c0e1030360041521500f049038600d250180c41c0d000540c84030480c8008000c01203d50810305c80503208038261481004020041c0e02544803540942580c0d90040c081c0c2500100c501c80b250080d40c44210f040c40018000301c90381e0042c0c4600116252195009404000402d43d00c0b44034050b00300440c11005204003084d400285e1101854000110341813900721041d001c0e03503500b4007103c6000a00340000c000701582c0c0d140c100340091044407c0c00210b400e01c200010075042a5070724080903000007540505e00b15002081107030720180000da446599805110000000d11038426180e24800040000d42e01c0304614 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 636252329 1250 636251079 636251087
    0x1b03022e0608070e0117100e03090f040b09040611040e0112050d08040c0e07030e01090b010314070b071b081009060b0604030803072001180b010f060f032309010c 71
    0x56000b40c020350b00041e0204182122103640e00c0c150f40c20416018402403240c0b180c0b918094400b645900718500c3d080300820b69050001c01812500001d45030000607940420400049400c41c10030140c004008000140c00200258000302103039084030340060500307480d441c400203803000981104d1348000400c4c0c1610140b2504108095495a07586001861032415a46150000901b4413400b00090104808a00320340d000750000e000e05080c11000b0400d40c03545003000c07100b0351420b12040d284604040d040420b15030000c141d18064803102d0742103a14140d81a900d58000d456400407205140300841c001180141091101ca401c0e20151440420034001c5030400c50211044011040d00c0b0350402c01040000a82040075281c1c0480b0b507080c80502414600394411020544000000c1c2c15407900904424500c0e40010341312260b40900340d0394a0302d0785c8484800b0084030560141e400441c2d0403407a0510114801d03082041c20075041400140c86a841060f5000c04002c10b0311881c805075140c2549840c000c0d84 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 636253579 1250 636252329 636252341
    0xe1c0e030f0d1b020105090612040c1517040507150903110102071503020d0b041506080c0f0403170408030f030f0703110d0c03150306050f0a020a1b03022e 68
    0x500e0182c404a10394020241414a06110031141c010055540000303684c00740041e10711541018040f565507821042c8a80e00e107000031101101c07a40b0400e40045006c40f00b09038844500c0d80705403034110b4407121210840240e40001001258180300300c2e02e02049401002c203007150a84415107070b046d440360641ca00454a807056005543c11944000c4042109504900074200d480e0400e0400690751195030081c10050002400701c0c80d002801e02c1d90ba03402202086442408807812540d42c4072050f1a2800480300310301c161141510303244010f000c280049040c01d1001103008258052191600d0b80c0c0761446800c503001008400041c0c4404010450b000354803816a03a48401c1394501041213081c170411154150080d01420070441b5900d11048080c0e5021354000480764a1b6940703105441c90f580d260074030142604840700340c000318845000c101580c20ba0300903100c0b003c446445008151151401d6440d220030804000c0e011807141c04000c1d00c0f8082081e0031030f98800d294021000c0e901d158141e2480036549 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 636254829 1250 636253579 636253603
    0xd020d02280201090b06010c03120e1f050103020d060e15040c1401080610080606070c140102150f04020f0105210108160b0f0c1f1a060910030e1c0e03 66
    0x41013001d44e030001000080b10550110090074986c28019140c10100c80b040650903558003a1031030032484882c0c0303250005503842d40e010424140d0707819031104898002500c0d009e12009410220544282c030003d081e6030404890b0322901c80844628540b6840504c0a80130150350540380d07404103003010b11001120440c054600c40017802c1c1030050b4200a4040ba4a000c1800440c4c410001c0c8400411442e581e03c0b021101c050b42c1222507001d8803a2500d403c400d5a00d41c6000440c058802c0c0c11107182003280301d0300124031410502c18402d040f0f03030b00d0b6003d014410500074034013810000c0421281030041c0600c14150b1800340390384c030b0710784035503050a64081c23425001100078130000101c50381c104681c01005c0121425204088202034030303882c80d610410b140c90807032007000100c24001018198440d4a80c4d1101c8440d40708100300050340d140c0582404124440c030908141c101000710205103025011782c108200b4070f5800303000c0350848031240c52400c0314044044d0150b000910795a00d241c2c9189420840c10f07c1602c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 636256079 1250 636254829 636254831
    0x50a02130e06280b120d080f0a0b060a050a1b050102030601021e070911120f1f031104022802101103071b0318090903170106050f0d020d02280201 64
    0xf854602484602c141c4042140700c6854440603518001d841d160750540c03800b0158421101d00c00890301d0080c1c4840d00840d180642e21440e9000070780b4031000350150410b0208003038002460280700c80001c95440d480062003205200903000d800b45c443c0c03e0314036800516400f500006031281000b100086c03c10b403000345104410030321020441c01f036240c045089021120048030000b15040c1ea071512041a02680e01c2020101100c1010005030381c00381d401d040c0c840c46482d0903034000344c0101110076507150b505020190001d1103200014450b820640d0003003032510800003017000038500d07241081104c40381c036041c4000180c1141001c00648071450003a6101c0e0070a99880500b1742c40d0101e401000403201d0700925420b020340c1000e00e130900d8028000261300e803450103c440d122607110b403818000f4001c0c10004400048210180303640041d840e60b0454143c81150741c032180344c00c03580442c40b08241c01006a009482760f0030806541e0441161005110301e44060200060400e9189403003041018604106015a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 636257329 1250 636256079 636256111
    0x19080616030515150c0a1a0601090e0c07060218040e0d200a030e1813021c05101509021306030605031c051c05070905120106080613050a02130e06 64
    0x603a115a5680d04c0705a503031a11a4a070202c5103c400d1410720b0062010340004419100800300360603149041d4490300b020380b14007107899070f582180300300128121450700c17180406010b09800155541c00a00010401000420b0b102c091200010119542100079282582c001104000000c2d040700d200c1c1c11040d2955200340c04c1c40d6403c401981c8543c0c00d860f0080c01c002c08054042025900c000b280300c10320103c0c0e10080f0f9203181c040381d441244078040c9400e0384510901e0390203922540f80054464546a4008041c02d07520b0342a00550340a0104000c042c004000c0036517000c12208000d101806000400200d0718403018a0100007030219500364004d58065084151100ca03550585c01c09000540030f50303e0420350340c43c110f1301021009070000d032084141c54240302c00e2090480e4400c0d40349064420860b04105088034180400b82251002d00c103480d100d0304002c000401145c0360342800c031f0049018200740d0380001030355800500e0303501900c0480c03291140d0703450040d246440100700043e07111184548840c44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 636258579 1250 636257329 636257371
    0x141006090209060906070804031a012111041508101e1103070507060216030c050111130315060e0f0406060602010b010e0f030a081801170105010905190806160305 71
    0x103d0310a0301e1300341e4000c60002550000300041c030001c580055802041c941601040ca01658200352004e101d00c04265443c0c0c65090750080c089580c104615038081940140315004d0014880500410a40c1c0005c0c072014035000240c4031014419601e61715881e603400181c21082c041d004000b01b00184000f00c0d0245030445000b0003030542411690400020709003951103c0c107500c0c2150103403044007000501c0304400921401015048900c688480788500028084402401c44140da6809282040a0001a403040420100740c03060762039024030b00000c10204031107403611b82e0400c00030800c0c2ea01030074282121040100b8060207200d000054941480240b146000303180008012060895186101c0c00c014031041c1c1d0b41e690f003042a807640e5544440c3c420b440d98001d0780c48003c9035040068a6000c1070003095040d04c1c001c4060890380c10b0b2401616482481420103061000c2c24242207100c055100301c0342000310340e00504000d19485144030b0f6150704024075010900809641028001c04003d0304c2d08030701503003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 636259829 1250 636258579 636258589
    0x31b02240601051c11181c081e070f241109010503060f090f07120203012d0909050304030c090c0905040f02040b040b09040605030a0308060d0f141006090209 69
    0x1130686000c0d82e8003443c03800c2601c100402880b54081003d000e50300001c5100e5102c030a0450901c04e000111103030b804500e810102160104001d01000303040741c80070000322411035000f0701030f85500e03200c0645980c1000c203155035035520502d501d403080d500007940c10503d02c1d50070509000009a880078032001c0c4103407026200320b840140140d4008030705110000c0001801510703154210180c20b01e00510b80211400c0c00d04c05e40e040100142c410100240f84c1340c4902c044c82c00280210b07412607055400403d2080e20342c0d174042d034a0401d4a24814508002000005020202c034061500102e002e8070186590701d107540b80423000344040d075000381c10160405850004040e00a00d156040328002e440224440c000114180000d11460f000700340c40410220740800d003a821080070704000031059508008494840082655402c080380c8028000f80811000980b00e0802040c4108014810000a00034448940e140710902580b26401c892075031149008001101c1c0340d00800c4010401c0c15021480c000c12880850 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 636261079 1250 636259829 636259837
    0x20d0b1f02102007110301050105120a06020d240e06100c020f03030c030a020f0706030917070f0b0406140f0105010f230f0a030e010209060316031b0224060105 70
    0x16402035540c414400e00741407005031001c071408080e003c0359503400f062802e0110304891042d8103000e9072074003002050505098115080d09a080c5000b403d1241075aa20b44000c4d41c050090b9040d4191a0010340342c0025003444410003010b00845c0b2004010708100031518002c1d80104041d01c15807420328060401500305040420450301075030280c010300742e80c034040303880c51007014100c40507444002008074410751b02050f41c5040b0480700064640c069601c0c48114203607043d4560203080604d203106100c00a41c4d20000411015200b090034669480d415102c56000300c00413142961015155076100c00d95007000c20034150704c03048007401100c0e25410540000d1512642020980c14040c1048202620680ca0405694004880c560040d43c51075204c414850b15000311603080c000c01d05242c8182014113060003070b6a880032004d010306045507200b03015040b28103542042c020a0580d100b85008049640e102030100a03030303d0760003c1503582032100d404041c4c04807481d01c000c200c480a005218143c0c1e4407034200c0f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 636262329 1250 636261079 636261103
    0x302031e0114040f11010e0316050a083919061e0504050d05030403050f0708070b0f0702101205070e1002071d072703030f0804050c040c020a0204020d0b1f02 69
    0x91740c0e00480d044010780380349400983c001d80c036110700f41c0d4004801d04108044001e070307041a58a045500e43c0c4000c040ea642509985080c02c000303101610312064105003220320001403040d040711048510700d1010401d00a1061955a00113a01e003605021040c3c004034101c07181c0c007914910354800c05c0c2021008016001c0c1e80030792441000c0ba08401c4003845004c0003901d016603002400c0c0c4110740c0c2866140e507903600d441c2c4603074195070103107110002d502c2c500e0100360b45460062240c214940746071307a404c00c87d50f80e0101c2000030600c504c40510f14a84d8110f8454184940c189868440c1c4500c121010401d091143d81001400c562080e4400d010650000d0700b5060064094042d90b1055180d40000b90390504d4402d210010103d41700940b01490118600c3c0c09007200d00035114248080d521542c21240310204890103441d07948141284600d900f40f82d8850f00c22025207105503241031030f2a80c002000d90740b004541d21070071511802c2e0182145091203070300000348510800c016004481c240c0181d16081d103130b410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 636263579 1250 636262329 636262343
    0xc0302010315080102040b0901021e07060810080114090712030e0609150a03050601080f160c150204030311060c161101050909090a12050301050102030d150302031e0114040f 76
    0x400b414500b01601e42005407005100a41d01d6030380f0746040403600d801c040c090703500502c01c500003841034070300c040e1142e0b8258100001410080d42011003c3d515440041d00501d14880d003c100000c80e2002803081035100c0a8021845407681824850740e860f2401c40d801507012075407c0d940001c0000e80016010b901c1e17400c29241d0a440b21354880c0024111301d520000141901c500050340107600b0f6040d401184226800d0b00d0f90ba1140d100d2031f8108030500d0342111203080005a042d4519001805000c03418003d5100b00e01c241014200450b4050030390300250700480c0800d41c0040340b0110031a050040c158484e108030580c5052000c401b806038128440303c6406403444410031860310b010f9200e90110351042c10701410340307031560a00200450307079490460f400b503404103258100e1412451041d41224103c8005a0045051140000840c0000c0c0300214042c0c0c004042c0100010042c0c8090000051908450040600c120b8801c01d4150035500e009040f4207000c5125000c101c0081c40035001604a56013101c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 636264829 1250 636263579 636263591
    0x11e030b030d2a0c0e0c040611010204030f060510051521281808180f150a0e100c03020609030a02030a030221010902030601122f2101060305090a0c03020103 69
    0x10050744c1c101c06500040e001d000c10321304204013840e00100820446003031b0b5503560135504041132118200c2c02580001400707407503480b092901052040d008a90446110244810f10079600c40008018800850042544541c0851148074807140f04c5500c170111145002c0c0200e4500c2c010350304d40320004110001000f480c4802d4a207d403200700c590b1100e607101c001006a90b404800905005107950803000c0305850b44014540b0b020303054140400c40c201e01040242c4102240790070480000d0580d0441815170301040074009407031440b0342e1030000d5007804814948880941396182d00b002070401c800104401175550003003140a1400758000219901c103c010320f40140c035400b14105a9890040c4040400d41881002001207940c0029900450280000340c136007440011080341e07420180c9201c9600c41441c507104400340b20f003180c00e8001003145010f043c00424980308100c0303140d10040101c1c40a04070402d14600051180d41c1d051720566800c01c180341e00502c9285002e544025441e1814040241095150300c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 636266079 1250 636264829 636264833
    0xf0904050d0507170f0d27080306060903010f1508060405070501050d020906030a0e0d0f0512071e05040e060906130c020102040909030336030806011e030b030d2a 71
    0x207050b02e101081a184c00e56450b02004031030030301d0340c100d40e0848003c1c40c40e08800e0400881c14401c46c1c041c40100402c0d41040a58949a41c0c030a0381000f4101900602d0800101c2003642c1c083c0b02c2c4106007000c40f40001400381100b15041d050700140e4004549642c060001d02021407000900c03041207070b0302464a5a9566051180c900107406400d00854010710040103201c00104107801003c01d0303078295401c60b0013502d14140f04442071950b001c0b4203004150204488185601c0410100350720401c0f5060074810210200040071000e0030782c940c01c0e80001c4020a05206c0018070604068001c030003198041c001e41032160004504050116140051710b5991103000c9001b4000c0d01910b0041030107010400080a541c2409805003403800c5000002c480824014101c011900344122034907689002040e500007100c0d50140d8000c1c030003a00d0a418015030b1003200e03032210001030700b031a1008907a55001c65201c44202c1813510b441c82900d10314051103000d407150f50b140c0e0a44c0d0160040b800344040c0c1d22400b04458 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 636267329 1250 636266079 636266093
    0x9020304020d06050106020d02060c0f2203050304230a0b09040f0908030901140609130b0c070c032102010c02061f0305060a1b0203040b04180f0f0b0f0904050d0507 72
    0x7850b8014401410103000050781e81e00414402c131359050580a648055450b0900d5191901c1045a21411703e04244018540383e000c288030240c0078042807440012032610303516110303d103030026804200d0118501c0725281000c8a6082080100c46040d2081610346051000418260041070500c030b01450b030700c0c00d5000d600803c0c1d40094004030340040002d40e80c1c0c146807007038034003804107401c0450007244400b01054a6003080071183c0d219640c04101c0070354149803507689980700c0c240603100402002c424003008010480c1c02003c48019885404402c40b8801480f907508429000c0c07142e00410b592520101c661803d0f008510507601664100005103141048014819100c40f02d400190061250700200000103290381d2040343d0601c101104246008042031081382d480c071460140301d4000000703020401c07d40b81041101c04e00001c060720082500e82d0b01110380d50448401c280042103064903420075818a0825100c030220601043d5036844d498601522070a5a4011442181c0200500001c51005216803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 636268579 1250 636267329 636267349
    0xd11011e11090d0302010e0d1e080405070e1303030f09320102120103020108010506041206021c02070c3f02040b06070f030818100504290f090c0a0902030402 69
    0x80280000e20004413420024000c28000004014507c1040308020343c16002d83e10040c2c1c0341c0d91141ca550f0038240c140900315a1a40054402c4031584245840450158504041c03076101d104c4010407501c000003a403c00a0a03500c0b00310710f1602c5e007850030021801142522186800075210705480300144065480c2c0303075840181d40c2e030003842e003548041801c0341589140c074101d604881c000d0b070303411102d40d89900070000c030741c407662003000c040c5d00c03800c810000090340e10b030007070070500154100e07003000c2c0c202a010780002d9a01a00045800042e500740c2803000003202d04500440c1c0d038048050b03078521380b540f4003507501d11041250610350b03da100c1c0c0d4220085580b07a4001f091012005450591039140c60714003200031080241040740441c001c440026030032594005140d0441c0c246c500280300c10f901c21072410b401840c0140003916454008a107d00d400344601070004000b14074800069511714224200d4049000090601081030b00300d402d40140307030358901c4600380507690303208401070b540c0d101c0c0d10010b030035418 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 636269829 1250 636268579 636268597
    0x70224070b060a08071d0a1503050f060a05011503050912160303050105060306092d09030a140a0903020907030615050307030f0b100c0510020c0d11011e11 68
    0x4001504030204418164070902420b016641003010544948545882d40703000d01802c0c06400c0c280080c0c00390100c039910b155410002c03151001400c1448070f147c000c03c0b101c00e504142c0300c55000503030f03040c400300c420040141d010f40300f21410062035041070201c2d1000d41c090700710030702003545503008100b4544050200d2050a0069902c041c1d8904174410314103402d11903000c090703000c2407030940005094100402220300c9100003c00c000031650303e814120312840c01c03800d000c40c1848032030742c1b2103412000095101400f80900100454035128080030090240e002402000c41584081c00842419900700350f03107500b034a904843c440910b94a607441100242130680c8000c050f0002100c010b01d1a82d041310095001b0b1000d96006d00075000c040c1c11000c1919070f011600340c0c208046222a10b0315501c180d4089140612a500b9100c980d82035001107400d98003c83e258075529002541c0c42840e01d82c000d2144181c5141d4200244a1901c1e060303604000001d17844826103841703071100d81c0001030300b0b01003080700c0c01c1a0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 636271079 1250 636269829 636269899
    0xe030405030601171902060706020d180528050d0305090a0807031809050906010302040203070212032e0f09020307050d0c080106080907050d11030a0209040b07090e09030702 76
    0x5a50703101841c03400107264000c0e6900340034114902c4420f05c2645140143c9035005844180b0b02a05591440300960003501d9410500b80d841001850a000f81040c0d602d0250142000380080d070001d02d04282c01c51031a00050b202404001d286034001400400ca244144149007000126a03860704000e50074212140300080c8007c0c07001500000305034100340c0744500b00c03025140034020b007a110402d0004442060300d10740941c0c6d1100004000520b4650000c0d80d118034288103a1340304c4010308280300f100760025101010440702c41ea00d003c02c42030000001050042600c00c4011907280b5000749840c1240e8540142240560008001110580220704940d50740329141410040f4440d6010002c01004083c05903000261201d0b02007090354000041078001c0c0c420061228200d0342007540d414011b8040d00c90090b81500171698004007580c0c40c000c0341e40c4503e01900c464401450718403c010401111a001103400d0090700d004e0020040000098501455040e00e0080c0320701049803410750005181f0060480034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 636272329 1250 636271079 636271081
    0x40e060106031a060a0c121407061a040c0804060e150a0209011d0307060320040e041202030703140307121505010908010615120902030a0b09161401030e0304050306 72
    0x3141d030607444020104524444024030031070b08002c0084c0c520840038100f000030310120001c004911105c041158002c000c3c00c01b681c5036962038980e004e203500450b500b82d0f00181c0c0e0f80c140781856196686403166202e001c40d41005070344406e89001d81404400703000a058241d581c3c072000c0c0c40c1c513010802e180030358103041070040d810b00e80081c02001942c0901c02a50001c0c0702e4450000740c10100d10241040080002c001d00031325814800100c1c001e02c2004450290f682c5510131030100030002d03500400140061184403c46403600d8240412240790781000c040856108200e001b0200b03038000c06113076002084000c51a52500c2e04c0500f00d4151103c0701c40d42c5042c80c5005040304240c02c00468980403250280c0755815115a01d015150032a1007501c244680b141e812100c6010301d0344500740040803014049000030746041c030b0f5004a072500c00488000c0300d8003030140d41485142c4070100500c0e4a08052000e503030f080f080c101201411401c1e0030540d01030505444007019282c0c481d0070f00aa03400303004003608503012 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 636273579 1250 636272329 636272339
    0x60e0421110a060b032e020d0b04020a020a120507050309010807052a16140f030703080c01050f160c121116060f173d080105060103060503060a0b040e0601 68
    0x4e10000c0c180510a00c03030110b4100c807802c013210040041070040c040f14107540560005110180d48402c4e10f008145694001d03000c41a6a00c0c406071603085d070030364001c0040103810315000c01d0380d0a034101c50000f844414402080054000002c94052070340a00c0c01c0ea0003600c2d400005c0c0d0355405024858200801c40d03a41c041e20203040508e0a500c111948070031100c0c0e0740e0b004007500c800003e01c1c4c000c880c035440b80d00c0418801c0703080100d50004030f02000350480300300541d2610f03941c007950030520f440700ca5651201c003403005168032004d0240d002318581103640e4039209514400f03030150307a00c0f880041030300c41c5510030001e000c2d00035000200c01400c40c0f01907440e4042d0100c3e1070800c05103207004e00d402107540ca0803108500780c403a0300740c3c03a00b03a08003885101c0075499861244105080030480501041100c50400d0344850403101c1840b0700003402e0410ba07811505001100d801c2d22001002c40d810141740c544208076550b000959180c200d0054940040c4000c074042c003142c09400040d40c10f911501c5a07030700000d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 636274829 1250 636273579 636273581
    0x5060706090c06180314030903060a02041e18111902070305100209090f06060417010e0f010c050d0f11030103050303040b0f010e06101107061101060e0421110a06 71
    0x7100d110355050360701e0544924068540c45220030060b40c16480c1c150f01400013a04449000d5044410102103d080468000010303241c00c90840340b0f460156004a01080440680008070040202610a0709003103030600c0a1b08882c0b800c181c005a0040703440e5404000c01c82c0c000d004039007c00c00140da44408900a0400295940300c441c40b044801d4483c0b111f50a00254151080d0390311171800070305110365503c0310190740b06444405080c0580c8480c0030400014501c00680340e00031540301e4207001242c04100030745c034182800100f00714000d40340d0502d550303402010350020444500c01452030b00000c80c00d03501e83d0210b00401c1d4288400050316070020000c014824000059407185c0e124000060f020f580310b4145c014444001c0c480c8181156983c0d0204503030303282480b00c0e01d904500c03900d482001c80f203064050a1504200b540024081040c1d06900c0300980e00038010900540312070510401d0341c0c00c26175220981d60000162252000d203a01c109448094801d248031407206840d4422242400c80c5420000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 636276079 1250 636274829 636274841
    0x60f020909060a0f0b0705030906180108061002190c03020a030f0c120b0109020d0906051006020d020309060a0c1a07080604050f0f16020f16030c21031805060706 71
    0x284109000d100007180c920308000f0740303070544506070314000e5501d00c1e000b040314850300101d400711041d0006002a64032070311078001601440c681122107610140205c00050f00b68000540b4041c02410710710701094a194001032400b2000e60804212a0205407504100700032042541000758803880001000040c0310f1407014000540d40550890720785140d40c1c409680c81641d00c5c03c0000c2c0b528003440d00400860b00369901505800808a1022034164404e6032610111201210321820a6041d01c005000d410b9040113500004001c2d40010351411076038800107240e601540a00904112110030301c5000c20144800d2150081000400c010f05070030200c0e070260440104448a5015501e400001141c500060000c00d0046000086103200340d11658000381803802d034030307620a0540c42542c102131580d030800c026039080340980d890071440080c11b62500d01c0345080240c0c400c001c0a1141c40d141019051255241c422641c1d06003841502454050511240303050ba41d401a5448a4041003170400d002094200c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 636277329 1250 636276079 636276097
    0x19030507030602030702010e070303020c1c120336020d021203031302010f0504051810150512100e0a050718150e100c15090b07051e0301230d060f02 65
    0xf0311080c8c914800c01c2d6a110158400640141d11111200f049810072141c46041c0001c2c003241280c5071070700c03511041699495541c240c000030b0b903a00c00081040302142008442d00e4031100080560904c6800182c6082d01d2009d00030307100c2c0200c5045402159981116010515004410380340c41c0d103001c080319140904a001c05030301042881a64100c1a4400c400f10307002e840d4010900840005103209005c1c003030800401c21041200e91210100b100c0e440302284054203800b0b9a42d969844480400d90b200c40000906a40c03e60080c42d0018820391104580d0144d010500c52000120380c0e44d500c0007251826504040140541c111000c0450303142990303d0449003560762502c0301902d02d420042031003480e0741c3e102540e00c00200303002c00001c005144130b0006a010341c2408030106d0420065141e0040417032040c0e4800012800008090b00e00b042c0c00c428072440c88a802200504661400c51258040100c0c10300d401c03800d4071490500c1d5032039a207050014801e243c005100f004018000c1021400a5010a4071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 636278579 1250 636277329 636277331
    0x11d1305070305072409091505030f0106180e0717100c09080f0d02061503010603060c05040f080a0302060c0307020109050f0115121106030910021309110909061903050703060203070201 81
    0x40c040140c1002c00c41d000c03039641700d5480c59406d81ca0729031006c00404950307815030450072070b148000980d90790421143c0d40807442d40000090861620074100c00c100940700e116006107080044803000000c001c1a50012558410062018084110011800e0807042d1014500707032880c0c45003c2009503030102c000002d64403041c080710a0325180c0c8080356030703032412540410b0040c1d01241c0042c032100c0b02a203200503000d8000d00046081c40e00c80da80c3d030094800a11103800042d41c00718040003600c7e03149000e04010004070001d0010303c2c043c0d840c000e48490300101100860080000460300040c800d5003c141c60795040410340d00310046501809019105c10309000d94001310000f40465100d10b1394410340d6203981d100b0076070301d41c40b1241418002a5000100648902d008400c030005110505000601c0100d4020a008015600300090202280c41302c0008400702541400044c40c0d0b03456000355180c00034012225034070314042840400000d00c6054000802e2801a64800010015190040c5001d80e4040d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 636279829 1250 636278579 636278609
    0x301030b0903090904030f050c15040318080a020f210d030b03070501050301090e0c0d11100309031b080408122a03070305030c0f04150e0108011d130507030507 70
    0x81c240759a40242c00c8002d40c04038511000c40c000900440755103000c00d1250519604242d9201049420319954002c0942c02c0f55440c02000105a400602c824400c3e41c038031018403816080000c603c1d03807000481d2000340a0b13030500020014643e1006501c10100310440c148214401d0a48020703525035041800742c20210b07080c424041c4071860041820300543e0810381d03a440c15031b8030b040c0d940c01c09040002e600036140e000350f10100640c1c1d102c403d08241d500d80281113a4402c0302290003801407003450710595104040ca4520716100203980b00d4074040c4401c43c0d050a8594149140c20036030903d12545e44801c082e8440c0100390f0b50030a80500150880c0700b10540b11b805540d05100b82c54403151440248444190007c00a00c1c0000e80944081c5400801307019015081903101e1950f0b4800d0f81c0180c1000b5000022000040b072100e40c0035841d52142c00081c6814005945010f41d110481c0c010701d890303400c3c00b154103000038903010104401ea13003816410008a9422a560741042511021640114040410451 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 636281079 1250 636279829 636279841
    0x4110a02031c0e030a03050402130510081002030c03010501050a110d2102040608040209070311070c180603034104050a080a030503040b09030c0708010b010917070603020702150f0301030b 82
    0x110400f010072003030b04051403401020792000c4000f000c1c028012070b0701c6154141020714a504e18480e5601c9190030000d80d031656030901c0880391a0100000041104500410410078141412410340e41101d80a09256407100065042624032241000945026101c0d6000341455503600150300403401508000300007a0b5800384d21500181d20850044801041070300002c01c00500f41450b4030340d400b0042d4540002e4441001500801550203803105a880c15070074841445070300d458020840360796003804402c100311865942c018100b40b02601072441c05900c054007480d190958600181fa016038020301c0f1000d03c4551a004c0d61294100b406454040d007020200411100000210810840e4241d102d2501310b40e03980d50b664101c2940184040c005000034070051032400300800c20301014000d100004500e45402800050205030540e1201111484154145100c014045400415148140380148e03451a803400442c0d00c0c0c1d07030703407651001480d5000224100b00c606503502440c1030f40c1c403c2c40500c110751514 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 636282329 1250 636281079 636281081
    0xa0519080612030426150705090a0e1501080702011508010204090c02071211270901051006170c0f0d05060306181e16060c110d051b04110a02031c 64
    0x1030701884007100800b0480100009a526000d4600d05841c0125003200b102c1d010b004580e460180c7c1e007907000c58808501a0080d151500302c03030001c1c00c0d040502d00c8030b6184c01542041d20303601040c20316040c00f820308040f40030035100b90004000808040e0f50101100d42d5540054003d43c4288240b4900a140404008005101049110403500078003450f0705424243d4807500041c4801407807081e840510074440c0c400300c03616002841500041b401101481c0c0c5441440c8a003500c00c014500c0010440b00d0a0030f1000750741044a01003900d81070284281d090b41d400c181c00c201e602c13414115003030000001c210301d00b8410941d045284502d8064090724015100c0354400d039140c031a1003203d207c032500710480d4500c0d401d4206441c01240d07607240040310310804515a010303070740101c99007080f4002403003040e1440a000d0100904202c0513401d980c1e0f00190590303602d0b440d817600a640a02c3c0841141105411481c1e170360740d0029120041003440055440b10318050195490b413105400184800d50805140d240202c0c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 636283579 1250 636282329 636282337
    0xe04060c03111e07021809060105010906120b030a0203060f1803180d050c15121f031704030b181e061b0d02040b03070818070302060a051908061203 65
    0x40000a0342448420401400100e034204002110441c06000080160380d55044004108554006420035400c140721f441d400e0a2058118505100c2040820080d8561006c1c12964060156100042d8004100c002a0400e5a0110065814491b0703d0030301850203030040d2554000d00d8502041100000c00c060000c0c0c07240620501c007890002d101c6840800ca0501d40c240240b101c0c814000d8421210240000a000a180600a800441e40031409002c4a030300600b11326003085240f059411001700c8011401601c40544c0001050040200c40d19040b8060180a45002e994004480b1507240b51001203c0c0328001c00d201c1d007100d5071040ba03418400c036902420740700881040060150000d981c941c0b40c41d0030182c0e018828040111020040110202c13400c1c40a48041c1460b0703490716503039040c40c650041483d100940200403010920f880e5000310300000441104503941500d1030f0f82c50b150070715020782e150b000b0402c540e006031095412405420764803140c4544128811101d03000c1c60100d4405c002d0303490007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 636284829 1250 636283579 636283601
    0x20f07061b120f121e020304030201020d0e0c0f0409020a09090201110d08071707020706050901020a0c090c180e010918020301050a150b07030806151303240c0f12020d060e04060c03 79
    0x312550040e000c2c17040703800560b1b00501a0002600d002042450881221280442e0071416000001401807600d002100005981c20031142407025844940010744d00800500c50414002d81d5403144c10304590160701d201d014a45140700307440b444d480e2840c0140040c02d0860b94940090030600c4c145840c0a4004034450003001030780d009200160600384151004d074001c000883c103501c2403111400c002405030001601501e030016010582c01902500a01074100c14030030241010310440c8144202c146201085044810480c0702251503095421003001c2d588461300c0185d010350802c2c08100030852103800030062080039203094a080c1d03540f810700d40c29900505600400040480d030200d07019141c90420210142921610b5518003605420740c0501d4003004e9104464624100110608114450341034607150a6522014002c003045e054004004010360707a0740d0014440915015082940240d05580954040120070846281c40340c46094592800f280e040380c0303c0c0c0c20701d2010310807240729001340d040c3c1d80c2c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 636286079 1250 636284829 636284861
    0xf011d0403050706090203071502011b05030412080a09080d090b06061c0e1014070e3f0d03061a12060121021b010c020f07061b120f12 59
    0x100341d560708007902170400c0c00da07414810007001003105c41040c501c0c00f80c1d460140d0000214000c0341d400c500f500043c84010340c81480f606000b00004102c0401d4203c511113030503c1c251205507a198012070041c4503120300a01240d60104a03142c100015920a401240c064154003250740d90315000c0041c3d85c46031a42290080542560258240c0280e401c104035803d408025903000020303001805003113400010000d40b4018050781407185494102034003d40204064500c00c1c0741003c0c00d441003c02c42281085e202c0204003120240708007052981024110f840b8050a5504029030308500401814883c001c00405031640c1400107a1300849000300e88100c042c218003042d240d51404010340704001204610a402140c5203a0400590b03202e200900070807000e0b0310344128000d2040105030844038007404542c150341c45024065078103100054140120b8800f40750510032912605900b0b45154000c034801041c10501c1000c1e01ca4142d0400c1c400d50043e012650740d204600c0400061000390340866414200c86 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 636287329 1250 636286079 636286087
    0x703030f0b15090418050325080304140a060c0302030907050d02090a0b1203160308060301051504050a0209060c030901170112062304111201110306040b040603020303030f011d040305 80
    0x10700b44080e0070310550040c000120002c1d0003034001000c913114003040711190000114140d1164640407a80301401740848003800f12652030355130700300522019001400f0001100c120540070502040728020255100b10103120201034000080c010303400a48000e00b29014640020405080c4603044d0502d440d001030800c04070380c41e40802480100034000c0e104c0d810001000100038516400c00081c00c1c0014042c011481080031420300a001d68030281000340f00e03034142030911041d0159020035400c4024200da0000b89611b07038040c0b20000340b10b0400b013903400c55008110210725410100c09400306080a0325020381050219000015205d000d000e010000b00f40d00d0f0115002c10044e91100d034043d040d8003200c5407880540303141d40503c400102d600b250b0010342891110308078108206420019011003009025811400c0104851400700a00c46402180d40b145101c000d6a540d800c02d900070740e00a402d6956a003041880c5090b0b00400b40a0040714102c91601d00d004005807030905e41c401c94050341ca1a0074 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 636288579 1250 636287329 636287359
    0x110c0f09060d0f080c0d0804050c150d141005270714040305031e0415050705070b0307080a0c05030717060d0605010b0c0f0a050d050705010f09080703030f0b 69
    0x2802001810303003a0012100e9140c10000f9651031550003000d070003510794030f80394451110b005d4034180d242c1e41500c6c1000100818880002c00000d0030301421a0304944c004100724412101680078081c03181800141800c000c440487c0340c031141070550203640c44511031400c0355101c5003400004043c001028844020b40c0c039900c141da003000d00f481d0349c001620745070140c00c0540750440204a901b00e0f810039600e6410015004207040b2019240050103482000198100f07031400b48450803a1030085000303024064001844801c00c00c0c1481940050100400c8580e140d052901d0b000340040c07401c03500d800311282360070102c010302401a41568418100303a13640401c0d0b1500c4068a04020002520311034211200d60500b03070008005018545c0030701041140c83d40c484044256103071508084a03943d040e26000080d81da00852030101d210300d5405002e041843d038400e1149010740c0105040c0011002a034a0081c001c010403602c18014800c0501035642070028000340841d03001241c03166221590300040092480c52 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 636289829 1250 636288579 636288589
    0x50105090c190309061e0510050a06030218030303090a0209070215060d030216030b071b0807020405090a0f1506060305090a060c2102071a01060503040b34110c0f 71
    0x40400b0a89400310380b2140c01c0e0341c2c941c15280e14890b0000d440c425402143d06503455440380a07072000308540c0103412903183c034010803002c05135801000101034000a020503958243d0150200b440b001030708407980d80c034109003099181d030a0349908920510500300070840407440050011101d02e0310382805142500d45404010819034544000c40a50040c1c1c1b507000c180c9211244142c00840c040c000700000b9103028580141202c6080f0640c2d8039602c40c00103410013042e0f0f410192441c10b58191000035141d121802ca251400310502c100070140f0750360801001c1042540042c0d014080b034500300c2440103d8035902c098060758030490f0250740d02e82c4a040d0320301c0450004d800c074101040c01c80c104010f050441c41e10001222205661983c3c680313400049000c01c0212020724036403031946495118049505224000b04144009072011744007140c0680864080300450300c10711a8610302d81a4948816014210101d8041410f1405400300301300c0034408012110106111210307a1004000c40c0d102c1c044001044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 636291079 1250 636289829 636289867
    0x503160e070c1b08060108030c1f0e0712060f06050d020d02060f121f0303020709050408040e0a0f060608011401030207170307050d15060c06200a03090501050105090c 73
    0x1000c100c1c401070400301007500c002ca640c942c0030440c240075000f2818603004074038007201a8410702943d4030400400c0c05508010031908101300c03480750081c0c01c6030701c00600480a0070029000340b0203401160030014447c0a0b90f0392501c001d5100303480501040e40001280001c070b6106215880e04180c24200880062a22450f5010042e100415260502c0818100940150005504000c40188907428170080d440061400e81d00303c3c42001054103210309594000391507501901c1110fa5440e240c9010400b000060802c0d60080c10340c0124a248519004400401500c152981c40941a01c0e1a5010550510900304075060314020901c07280700080d100300460095000c580180c0b6444020061000b907010f041d00114040e0351280e503000c2e103803034034a2490000c892038081d600c1240200305000304a038682240c030300b40c01d960b0090000180c00b1480c90158440611441c41c442091100080c08200303645c0691003a000345014030020001aa210014803408001c1510410f0505078103110350020202034603d0a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 636292329 1250 636291079 636291091
    0x61608010509151801091508030c0319050c01020f0304140a0506160302040504091110030e190311060f01080f06060603220b13110103150b131d0405070503160e 70
    0xb402460108030703130940d03940c10a130000d900300e5448504406031014081c407030360050a4200c0242d4500506104016507910440034810802e141c12a00036002e10301500540704c1d09507000d40290b5485030f0b07200f0034510680c0111030403210908110b445400342c8c003000442c016140c4c0d01100820050303c40414252200c508000303104200743c3c08110100d80340c1c4990054070340d803a214001e059800981c20080003825190309500c5020945000316025440d5800950b0403d10590030300300404201440c24225107040c00ea6480380c880d0700c180c20031b00415483c0d2280081c101c03003200066402c0c801a1b001d5450710344030103841036540f0035800d10100f07540100c1c043c94210004070451444120703c20300c2d920010074000855500c1d02c1800c0054281c07090114072590b60030110000d01e000c0200b18248441e6050803980381c00380501b8100301003818840c848501540c2070141603282d05140181074130200d0307405540c1e01141c0413203040c0031342c01c0c00043e141000902c01d4015016401128242c3c6d041a0071745c240c0c60001804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 636293579 1250 636292329 636292339
    0x14090406080f0a051c080103030c06020c010507080403031802010905040b0303090d0302102a0f02121303051b150310170606040e06010602340806160801050915 70
    0x7480d074010001000c5500c0c03007070040c20020010341005420044500120400c9000c0d40c00408000c0d580000300704d054a0381410300d10051101424050024015251100c2096180105108000d50000034041c4181e00c03035501408400c4442121441c004034100009000c2060910144590f29054100d11070f9018090101d03400c01c4a2100012618441c44200b0b0780540c11549003040c1250302e9001c1c0040110007034403245030254501031402c030318a165458600800c0403280f40c0c05446031091182d4807031a0494a0150f850300120782100102c6001440100c0f0a44155110f04020344194901c1450500004198044002001c07041ca08660b20080205056000c408408202049241d0720100407441142c002d01d25460900c086c0403c40f0006e079840003a03a444000100070b110ba00003403009100701d000c12405030003502c1c406091582c11a10b0b68200f04080f4448020410341e000280702440f8000c200840f052075020740b90f09540f0b1074402e00a80d03422601e01c90010382459002c880310000480050300d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 636294829 1250 636293579 636293591
    0x60901060921061103130c14060d0e1e250b090d06110409141b030610020c030303090102220605120405100f021308010e0607080403090e0109021b010c140904 69
    0x80c113044207500031244095150500c20098081c014207150310b80c003500d807190106076510f03600c800140c1c640c0110000c3c0050542c8505103500c11100500039420345e0700c8203041d02100d03901c8105005403502d40e103180160302c48611603180d440840c8044a410b0480d20b120041d585401010003e1101518071f881055903801e4690041550500400d00100003c0c844003074001901240b80f624000c812401800c41074036401d1440c001814180d407081101c0c2c004e407040fa002c3e07820196506043c0c0c18884800d515540c10301001c001c1001800b0190000c0202c18040092031503004407011407110710700014003c1400280c01849490658240c5c9802c460b040b50084048a0317241c2d4101907041d060300c01466186405540102d549103500c068070005001400c441002070086024004007076a175000018407d4081100000114040c540502100c1d80501801c40c450551985c641d03a807003010703610503a0310032400c601a0303900301d004180620440741c000401e0340d2542c000d4403603980c0340151900507220240c2d006541d80 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 636296079 1250 636294829 636294851
    0x50415050c15090a060b1002121305040504050303070e15030721090501090b09010c080a0c05250203070f050108070e1c0b1b090901150e060a030506090106092106 71
    0x41c041a03c281d200400500c1c40d20301034a4280160340802c1c11450040c140d800790010030603000300b03003007686a05c03103055180c03141a584185516001c03960b200725081454042840b09100011004500c20001074681e5201020800b040c0031050000c8000090500b0052010840c4c0ca445091f86100b2003003c012480000555060502d089030300f401000c03551607665105110800102000d03d580c010101070081102c50781e00170002c1c2111100520300d8000b0b41d521034040c42018001d409031000c405110a40c0003003825084030030f5600d812520740584c820b04c18048005105038010320341c0c0c02940c0041e0364101c03060b19081802d880d000b290202040c0d0006260300c1003004903200d4951000164010800c03680035081c0800410142c0341d02078443c1000500411090b00383d510303071511240c115400d98048c4aa4403100e00c1e030448270500a0b13040e40b0780c44480020080000c0b0790640020b8003489044030301896a0b6a01d0205454800e8248604503942e04059903912a000c0c2c8003041d01c907031900075000414040d07110 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 636297329 1250 636296079 636296113
    0x6040312080a0207240c021c0e1810030507050603160c03020a12030f050a05090a080d0f020301032012060a0c120c050408060a091a1504091202010c050415050c 70
    0x892090f07178918001241005100043e405044410881b0b80081d01c021000c0402c40c61640c81e05010290038070204091481164a54000c0075880004005024007a4203190300f40c80000c11562105a640d441081c201188515061080724014019908a01507080300508196191600c0c2c1205800794060031008074042607004420021409590ba40020700e9100d140068040303484c0542100041e41c41c10301040f00301131000811015068002440d5038690407002c0c1c0100252007107076a103021050021000200304803002d43c907112032150011070403100303560000900c1003c03850006901d219a1044001c00c644900b680d0044607024428a800b40803550342c80504405d56980c1a0690009540028100721041e000c6c803540380c0214002100b8001015a51109032060100d20030946100035036102151100781440000c0e9040e0401034000e2145282d1410201d80004400a808007d5403d10110f100002e21810403141603c213844040c2000e039040c03030300498550b080b500070680b05106200642c00300c0804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 636298579 1250 636297329 636297353
    0x10902030d08070f030b1309170f1c14190b09180618060703020d2915131701090c093822180b0606040312080a0207 51
    0x202d4503007901c181811607005041c809212008003c0520304111003500da540d0400c0c0c08090b100e00b61011582070003c0c1031030403101130740e4181e641c000f400c0080d03501c12043c4140f000e00101006051280072841c00400710000780c50601100b090011203000000d084a00003601005010340f01440c000380c1d813064180810b00c5030200340ca82d05c0c0d500984030640d4040f040e041100d00c0e40040450390700c1c0500602a45016500c000151440c8281074001c80c100000d60700d103601c00242050714448440302c1d440b010651900301044620300600800a0541140d900c0b10038108075402e08000380c6900e0580c3c5d1524155004850a1113004409552922045000700f542c100b02d8401904241d40000340310001040700c001c1c0941414403204030214841d80c08485c7e842c203030a80c804002800c1c0e5545da603400655404151000c0b0000c6400086840c0040c540b10703207001d000c51265500c2c130400b00031442d601c1301c40811a05c2c0c0114400140900d0f1003111051199100e261000d4001000040c090b080640325035400c929a81 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 636299829 1250 636298579 636298603
    0x90d031b08070b070c150c180303030c020d020105310b010806090601120b0114030f07080f0613081e04030c0e06100e032e050907051504060e1201090203 67
    0x6404200e82e414000c103010400e8000707640b814080c40400c1c09039076411440b8030580b00c5034001552110380d079400d2401100b1000c0780484004140c80d21580b02c0c82c014008120b105100401442840c48410300d05005125441c05102c7c2c00b0000c891b5100d8601940d03070b0b03a10310b841011080480444465001075008207485018100c204041c0c00c072071425203041890040140d109480407400b0401c540c020511500840313041d00c3d44150040340c0488400041780c9401400c2c12101c80354840ca010000740b4850214102c016031072144255800754842c11340310941244200009080c2e010200000508180450700c1c41041d10002801c0d40d0070259292540300403941c0d6944800841002d40341045001c0c907001a0544c0021418140203989080ca607001c00c2d51903e00c010903583d90540441d000d000009550882c2c0400b4a0001041c00a031615160309500d83c08288101c60080035550a0701852102e02c1c004d0760b058520a40e1044a240d0949042200a226410454045540c0c0f8901207002d600c0900c003501c2151 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 636301079 1250 636299829 636299843
    0x180303130503090619020d02070f05060d0e06090709110310060e0307080d0c0204180c090209010e0a091401080a05120307050f1303021e0a0b030903120f0105190b090d031b 75
    0x1c00405c006803c1c0b049541140c011900911401e101580030340b0044d0050b1041a0760454440041a244500074040340e82e05044610403181048002800062004182e42d080201448050284600300069010a07242c405004076582e07400d00c2510300c40c17504041000e800a088410407075a4512031418900c600c2c00303201c001342c40e4016100075814a4050415001d90f02050142c400c0c9494990740502402402740745006a00052020251381c42080c0301042204000e001d21034182d51040720700300031f010100803101c0c0c0195103400015020404194204c0700381c1c100c3c020b0002c1c09007201d00c41506900c0281a0024000140f080c111022210806440d024004a000c007035858118010002800c1c255004140c000000c80b0f0164032a0321950090420be8488481c9103842e5115013052030f0440c004d00300713000000b444c600108030045000c2c80b2403130f040391010b456140c903448400725000803251310b500075048a46c00030010280e2034140910000c2d001130180c13511003d000c9161040c00b071440b00c5000d060701c02d9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 636302329 1250 636301079 636301117
    0xc0703140106090c08040206120907090f090c15021b0a0e0f0a0b042f090405100e13030e060a030617100b040207050a02010c080f120703051803031305030906 69
    0x4460301c84e51504840c14203181c10f15140941c0080c40a00c540c1c2084004c1c540080085030b0041010800d40002c0c01c0c030010b0a0080407003008015006101d82e00d000c1d9504480760b50005004203902c08172003443c103200d43c068500c2d440100100400b03102c0304452190800e00d11240014400d00c2121084e01814181d1084111030804141c2d41d41a50701440c80c10b44150710b4896900707070254000c0080007002c04a00460080c600301c1e1400303031510303020f0f8105580c0c00504103002c00440c00140c80440c001d07038410511185450b02c0349140e91320445107000d802008100310607a4406145030007006410415640d25010820079151700010103415100204040c1a41c08642c1400c200290360007081210581601c0031410b011007a240c082d941c041852010303050150000c004802e1007405001c4038260700c841d103a2a5a00c140c2d1a80c5980404000c98290002920704008203410b6094049001c0d071050741c60006609685840058845101111804a4040c4801c00040701c042e200c41020303200000518140c1c2c504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 636303579 1250 636302329 636302339
    0xf1f1e030914072d0f0b120c0f09120c033013050d021f0f14121b0705160302030f0d081b0702060310090b010903020303030402060c0703140106 63
    0x4141c280000342d2080d0304140014411207141103880c18a10207100300d52419040710201c1443c1c850416040003038a0000a600412000003600003000c4c0d4450300710104080d40e86908004919000b4500503003403541040005025601c0e040c40c140c00c1003104003040d9010f0441d0000060310306115282c00e40c80e483c1000d07103600200542f400310b42c00c111b4885c0005926090520070704a401c1081030141c103205161640c4080290b4480400f40484244000c0c40c0d00601082c1c10301c0035019940c0c00e1010000180b0001e8040401c004000c262040e00d000312030411255203502002c0c002c1c2d22100012419036000c06c0c801000401d40800c40c03981e03c001c00b00f07101d6541d241540181800d14020002c0c0c09815803103141604002036001c4000381e40030429221121030340c840803540e58402c4c0316000010f50f0212021050105400b800c031419403c44c0c80255040003020034035001910000d02038400a50b142e00240005001348c03e000004002c100c1090083e80c0446850343d03034440c0200c0201403959981da54079201801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 636304829 1250 636303579 636303593
    0x120c120203180c120a02040e0708030c0c0a0603060513050403030b13020c0d020c03072903010e060301060621020c03160308040302100b0a0519080102040b070506060f1f1e0309 77
    0x25143c002d4a41318086054495007594550880342c00a025a540e0207184144802c18080711024180e80010b590b81e400031920410303aa940d04491a91140d8613130300001413603c1c0a84100300c1150009041c030849a035070012020001e0400910940a0640b02c2c40c4000c82c075550f00700c0c50361031245a0341d00140c40d80d0b095912a80382c80001c0d450013040d50b202c60150788040e50006403d1003101c0540c00c14a403400d02d11007c0100c5000c0c05100c00700c404078084004644502d0a500e510303c1520b040c0c00810809590b0f26040f1030449840c060b512410014001750a02d07800c49030014024000450216443c200d0124200c1c010744464050070f60004007040306200405a040c418490a4101c0d65020700c4800c1d4024005110b2224900ca0148a411001060b04030b250400360400e0003404c004000b10b40340c5a031035202184a034024a4204c4190203204001151b6140c001c5604404d03c1003d0156600e0705d040a40c0c4207850188080075038180107000d4035202d45000010401e041c3c1c0c1d00c072950080b404c0c041a00e8011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 636306079 1250 636304829 636304843
    0x181403130905010b120a0207060204140126010605130e01031a010e0717180703030933031d0d090905060913030302031302060d0207140d120c12020318 66
    0x1054040c01c00004000d150094000e0300c14145e031800810015480d031003213100c024400d0304001400756001143c00030f0105510384808017041c0c02030704c50702c80c1c188401400344522a0341d00000d8080315078881c0107026051096014142c03552400315846925030701d402281540a00c240d00441d0740c080c00c4101d1840c41998045410b00500011850030b80d01e04003440081c05131078030780c00304040d40640c02000070360f0803110700c510002c400794100a0350a5280c403418003d0441415001d80e80c841c20b2400c100e8021401c005231840410001c1112500070108404000ca01502980141c11860801480340341036900b07091280e03419401503911841102898401c510003610802081c40f03205401ca02c04000319a58062000b0351340c3c43c1d141c600180d40780d542071500001c0446000d0040c2d00a41c010034240703c41200c5074001c1c2010390040400b104144e411281959403001001c00041c00155088455070143c84950401d000c41811030070030401270a84d20205070700302e820445980003a0824450304d040c070810140602 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 636307329 1250 636306079 636306089
    0x7060c03020d0503040305070f12030e07060c260a091d130b1f0315050a05040f060905010231060201180b180313060e0a030209040618140313 62
    0x121510064402a40302c071203480481080c06400000101014407034030841d103416502000750140340502d402d02c461940c04203203035980803074038065203000b01e550000f03032020407a0025526801c4803030481c0e070f4211549058811402101c048100010803000b03596002d040e40e030300d29684082c1041c1c600407060700f0214a103120365400341009000d124070005041195040150480d00c1000d19449070702c02d11013480b03100c003100070710500c40100c080f0801015100f04620498600c00038805600c0f1084510103c03201950018001198a2a10030004110340c010754003160007000010304017681110000500c40300041010303504988034010310104220310340d003240a44ac0e0342c0300801c00c02c1280e240b071700744e40341080034050480a90140060032901446840580600414064944840d0101c1da811941c03062801ba01000c1403800d2403541c4181050f00c44403084a40051004003503480d2511080000c0404a40e18041440f2040e0060041032034865041c82e85000300000f1561180507102e220b09644080e001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 636308579 1250 636307329 636307337
    0xc0102221a0301360f06091506110109061401030201080a0621050c04020409020903121c1a030f06090706050f0403061104120b04140f1b1809030301080706 68
    0x205801c070035074241528190fa0a1803820304040d104034046501c08507505200c408008804003040c4084c00340303a0844000078104040611030151511070a0003903d0b45907142c081c3d080c0211404010062141c40301002d02c5480b2800018074a42c1601c0d0b41c0140d0301613144a400c681402e000420031564407845550384003000044c100407050030720140591070891a0722415084911040f4041130140900c001c035041c4000400c11551141c0d83c808490103074100102043c402d0080c04507a0f02d18034600c00845080c4440e026500b02d43d0000c185074480140b410660700322278201c1303000a100503034074100a200305034609080100103500c0c1558140c2d24000315500f01104020060201000694211050b901540c5e40144013040904116003804050300880c0e20801d040c40c000e0f00072106000b43d041090380118010011102083c0c404003501da60317030504078140c940325404080951800e00e520b491680900034010312502c46c0401e541e0f4030700e030051016110132140d60000401001406000c00000d0000c20480c24 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 636309829 1250 636308579 636308609
    0x10e060904050c0907170a0e0d0918021e0c010b130905120c01110a0c031e08040204050402220b0f0306070f030203070e040c020303060310050c0a03110c010222 70
    0x184498442180300620f5001e680a14003040000d4003c443d4410310351480181c1c17481d5841c2c00001c40000d0f010b01c0728092480c0c094010a0008a44200304410644505061a03070004503c07807811002944821140958908800b01c3c113203130010408011b102e0bc50a420010a0505650007000006021011800f4401d882c0140710b50002d800850860500d03071000b401c00d5210154603800c3c90151404648103844a0400a5040b00c1c10382c111002c2210940079948403100c4030300c400e00150300e4144400408020800050002c1c0040c58950025940680701402003000000142c2040642e40c0c12003003014803540c1c50f1841c1d0301184c140f144424020b40c004070001c025906100740003800b10203070a10a103040503000400035403181d00440d241303004001c3c0a0070400010000e503000a45941003540c41604c00c0c060800da00c03002c0480c50041c00d020b4120720490524192211030250001c25404030b849112003070a012112035010284041c014103c540c5242000003050041c200700c0014641e0400c0c8a00c0b07103600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 636311079 1250 636309829 636309833
    0x2040618141e151207031704060e040902030c15120c16030f0309080d020304060e06011505250503071509050307020d050313180605120303070810030c0608010e060904 73
    0x20318885160151a800892500c903c1c54140c02c1010022145400c00b85504480d040c40301c2c0095200d0407607000d24a41da040840104a1321404d01c110721038500000d0a4a80070541e80c0b5003a84040c2815100504035a6003001c00c0c1c0100d000c0c800309030b490039040e01c404076019681103040d4110a500015412001c6e1500b130007070040b10303c80c5ca004a8064104184500481021800f23540b0184101e078010750003617144c0c0182070b5124007961040f40c040703d03a14181720030807407101d000059090580b100c5a907030158480d142e030000c8915030003c80c1c2d00d050f000321041d1190120705030b14260350780f0355006402860f1364202500380a0f0703020000503085c900c401d140c0301d4000089480802901c1c003059040320484828031040c1055455070040d040c00700c5003900140d00025004851080e40a00710041c9101809810b540320304008042d8054004051190400c10000d02140d21900d041940a1042050f05c0300164581d20340b011605040c0d046600450500c01c010b0184612400183d13610a8045030080038a28040d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 636312329 1250 636311079 636311101
    0xf050603150c040f03150e0f120a0210060f0311220c0909050f01050f010c051b010302041e051e1008070302090d0c0e01050d03200304030204061814 65
    0x1041e041d0407005034101203a400081d2804540080c20800c02d441149910780c2844c401406450403c0185c0b00c0c503040181d8074140c070225030b40206036424800b816000a262000300a11388c1704080040450060320281d21740d0b2031407882028040e10214040c91189415483c0411848024410141c4101001d00001000c40f05207505400e41070f07040d100104a42d844008140c403c2107442d0420500385060008204025607400c040c0340c1261001c850070480c1d0f080c07110054170a01100100901990400d1140311200103260034001070040062400600d4907607200f41480c609100503000032600e001f052020007892070080300202070303034403d500c0350b0300b031242c2060000e0490780300740e5840810f0041000019840c240a07a058603010040500380c0d681d9034640d440d00d96000720b414010004603011001c0041110b090804120700349a6142d10b908410701c0380354807003014161080e070495203141300420011006840b02e015610081000250081500003558264401d1391340c69000d40d0850348045081100310030031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 636313579 1250 636312329 636312343
    0x40e03091e030d14040909030c02030c0108090d05093d09050a0909020301090c080106090609050c0324041406031903021903110a0b0403020d0c23031e0406030f050603 73
    0x1d500b00401d078410700314094092030185c0e40c40f981c4841d00e001310f00c106054000f0040c0581510890640340c480780c80340c0043d00d02110540e0b800240750700c03400005400a006000408075000b0003019a03141c8e0410480d400555046181200007130500c0841101088003846040d043c7c2780c01d50704094240609010106104100611803000420303164100b503402c0d502c0a42c01a22103582103940441042d8440001038040c02072445031400c464644200066604d1003803003038038002c08100300810319585408801e0027a490307506003203240e15001d03030070301d1060381d6202d10462179501c040c0881c056440c501641014104030b01000f4903107485605c1c0f58a9000a079002c11180c06a401c3c000300c0d003400c03440034103040391640034031410410540300b40087c0e80c05000700c641c98648194881c1d8204c0340c0c1c241c880a0308403078060103c00c1c02040115488460318419081c03044485003000e23080100e9060811000d000c800c0382c094154800c1042074001000c0c048550f1502034500c1c05c41212505200d1410044046541c6080f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 636314829 1250 636313579 636313603
    0x30503040602090a03060b03070503060103020d1202190b0103111819020c16032d0308040204020918010501080a0e1005090a12170a0c08060d080405040e03091e03 71
    0x110020000d020441c00e9415a00110400f4250324107403516441c19030700420300c0c07202e510722900c110403000503a440c00081c104c0c140c950280080ea906180c95030313407080d184001c2c000b5030198000d1717034070400640d8179140c017503598a8001e400a00e01949542043e940b0f400303101400501480c059100c00000c0c1444520540d0000d41074a00e110500441401c0e202c0217000b280108000b90007210881c11500b4208000b00c01640d00810528100360706440b0030142c4051030250141e60144c0c1c800e858004280280c5980390b00c00d00140015184c21040d40014a04005202c907071006800c01c1c50052000c1d59203d007400754030000c1c0d018200102002e002e9070341d965100c01d59050100f00c0d1a2000100c0309401441002c9015501503c002c200307170142080070300500701c0f901481011001c4e104c001102e06030140545002203003075840e0030790301d500c8003404d102c41550900000d860740e590802c8001050781f0b8034428803a81075007a02c055920380d403421007040810801184907131207050f100120980156004140c540c00d1032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 636316079 1250 636314829 636314837
    0xf01030e060f040302070f0f031b0312050c01140408070c06020d1215090c050d0c030b010504031101031d0f0f070302210708060c070201020f152d0405150a0507050703 73
    0x143d590320b000c81c5000a00c2e00015180300401d00c000440d02800d04246080d80c6c41070400e483c10009004030440e1140680c40702409000c1ca42d44182500c501840c0241164400c920000c91003403031020404440f0f01c0c0070b90701190042000203428060140d03185150780941207520107000420311041c0e004020800c100c0c164007034645e40e200f10100c41100c40101000401c40b0300300a20081c60301d0303035000d455030300840100c00340c5a0500f00d03805402482803240043c104030503191982080d0564450403001c0c9006007900d81816565401d80100503076035001c0030f1441d6070520040020b0000a030703040b03060195103000c2c6c4900340d210701801d10050307582e1500d02003a400d040848400850358110054600400c61f0700c140094060300091100c3ca20304800207010b024000c1e02141c46101e8449121681d40407400802082c003c01031000c9000e1183d42e68841100e048184a040c0180a40c038811040c00c410644d000c464503805940340d81941400302c50340b15800030314243c007000607290030b802c06403482c81002070080c104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 636317329 1250 636316079 636316081
    0x90e0a06060918090f0b04050d050901140d021606240b03010603360b0c1804110f1c0501080a1707020a260708010c0c06020711060708090f01030e060f 66
    0x250859022110b490b80102e14801c50703844c141080042800c01f44e400b0b8801d40550750602950314040c4088440384e034410ba44848441c40001030380301c41e58210602e41460070760200901c04c200c050620400d8070803800f4520004414810f00c4c20303060644c42141c89460704c3c552061080200c2c6040401b44da04464050401103025100d000c0d1100c10b00340b49663b40600e0b036942081008440c0782071a26580000e10980003e2441e494440d42c8030703082d0096003200b4002d0000d002c0068418206504500002403000048034140342103070001c6407107604082c0c40c41074410318440402c107103c800d82c00341c140180f0418001e05007030255034641e90aa008400c0c00100b500000044001c21921800b8a181c000d250642404042c0d1088454100041d0710900748030000d8031070301a02282000042c450404240c100b0307121036407540d900ba90b4210203500001010340703401e2280210141152210b000400601d84070359401c2d03580c0c0790103504002d40d00d24801c402e18105403400c00595094600019095001110040080c9032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 636318579 1250 636317329 636317369
    0x21e07080703060f110301080a020a050402030603030702121207030314010906030c06030209131404140c0d24020c280b07050705070308040b09041404030903080c1606090e0a060609 79
    0x45c10b900c2080b0300103140c0000002030b1180c07010407204800c070700c01c94903442040c4c1d5800400090380010798020390b00d90030400142006180407689503001072204000d50b1070150400504406a401101007079010079114030881384e071901c642d0761850240100c00b00030001641191920300350300c0e085024141c14141e0001d01000c00d42e41c0c65085602d04907006d00113100c0e80c41d640124215840c02680d088034686d802400c16826603801150100b64a0400f5004002c0c1d24026100d40d0600711203809a180308000b0000200300d400d06a000074801c28000030014602040c01c07510444805110040e0700c0c1a020256201c2000030301c4400700260002d8492800d203880d0590760404605201e510f80c0005e008031000240041e07400c2c6190081c02c0f80303110480d001c00c11030280c0500c000e0355520484008002070a0110f003400010580e6000e044c6107080e02c01203482120700e28003603d90034507060308100041114090100100d03d0005041c5500090560042c40854a000f0014010510500070b210000726680b405d451 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 636319829 1250 636318579 636318581
    0x30a0905310b041d010b01031109011407060c08010f0602060f162c1c0b130302070305060106050318010b010f140903060c071b030f02040209040608030a021e07080703060f 75
    0x40b4200280200701d10b0b0380d040064140c1c26101c800c060f00c0c0e9402c180c000d1003698042c0c8100740108184c4851585410891401111001310f070004103040e40d002030001e54040340c554070030039503003416544925460b0350408845000e40b007001c0d030103803003154402410442151050907089410800c14580a4030700e5503450f005546605401800c115548000300602c054104202e9142224107803c0d14980d00c001e800b9094811040650700c000780444001d9400300d55449088003081e0102030003841510601600c95552030305142c03081e404100015030200910941090985804d042002004002c00500302c8038000607203000a80310700c541c00d10242118100c85101c0d444120b81e45000f00070103803049803900c5100d904580e00310320070980301a2405016502c0700d03052015130805507500003003131103d003229903800c100203075000520b100c0d08103072104800a000102040605a44441a0058103404656014108100454210079031459004002c2000300d41c80118445c403d40340c101402061000c8002c203008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 636321079 1250 636319829 636319841
    0x1b0512070608041e030801180e0601140a05090a0f0f0905150901020d020a0206220b040807050109020d03030e0624090a02040b0304031206060302030f1611010509030a090531 76
    0xa28804c05084054100b6500c01c400c24140d480d100c1d0200c5000c840b0000090448600900d42040ca61022006011480400003101c0e084080100369816190f140e902240c9062001d40da2602101e813a14070b40340740d5214a0184030385030786800342c042000f160681c403441d9807002c241000d500750b601c80c3c0c03001c80d854580a4049a00300b0310759407400d5544040144009503640c100b21a03000c3c000000c0325400e54815403d8a011161a4000d48041d07540d4660352152112a40042e40c2141c2c15036944082400507190003000c190014040e8400080e08640c0010b06414400d0003000703040440e002e00e20001001004a007443c04d040b109a9009100e075650404a000910468120740721021010080004041e40706c0d60311380c00046100c80922085070f4420703050b0182c2c00142c660303810480100c00000c541081440b05641100e0301c0d4900038140171032901540e8211402501c600c803103a0800a1480c0c212904103004400401060f141104c00c0c95250310744800b110030b00791410700c14000c05240e40400003901d4000c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 636322329 1250 636321079 636321113
    0x30305070c02120a0209100b0f0a020a02090115032003130609020901120c0602031e090f181014030a020105031807060c032705011b0f1b051207060804 66
    0x80850080481401d40d40e404d82140100e2150442200081281ca043d010110441d01d5000c002420030740c2011406465410034901c81045228003150840540e48413003080c1e000f0113003091401d1000e84240002801e40e520000d0300944210180c0460040c83c0c400303012280d00400c50309a01744941c07050310300b00340900100c07000a03600001420010480c02d10190b44108554491032540c61441c0d5559010707600c90283c0c960088854925402924403d4001c0c0024000000005d00d00032284050b0000100e546030f9802c100031a440d50702d8100070b00d02d600031800301c0141140640c101c0c0c151008400182d07966803560002410400080007240c45200c0e2040000300a5054409a806450f02c40000424980c031084040c1c000950391011201d00780c0b000b20344d20308054001590010618103003001500e40c1c40340c2c50550b12001384030000c86c034041480307042c588078210b20440c20f51801400c0710303103c41c01c040e40031f400c268810790303e0600c3c031054508000b854104541c0395081ca606903035100d04183d1110b01c250055 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 636323579 1250 636322329 636322339
    0x2070537060c0318240905010f09030909020c031b03040503120d060e160305190609090c0603060e1305070512010903031505010518121c14070807030305070c02 70
    0x560030090650070000700c0300c00c10355040000801003401c801011390741c40b401404400c411000303046455200341060300344c55807900011603440c950340d4074907003150901d442c20604160b0740d201400401da03120789175000500c0c1c0200f0650a00015141c130b6516481038800d010701c0340b5985100e040614505205803002408001c0a85d0300341c40b418298111035031301c400b50803009545494004501000d5650280d4018041108140240311003030109900501b0040e1945021121400c141806944240505000351070a11400b00d07100c00c084c60404140b800c03940149052600b040b00500c25940401368455114150300007000e180c00003410b007542040344640201f03410010501a0f1142c9a50541109892a10a42d010005039800b0110300352941c60900444d400102d041010b001c540440040001000744001c044030303091028110101d1030143c2d08051107041201c03c2c92603160498000400001010540d55064642000d0b90344840303151068003002001d02da81e401c08520402e02c07620381d0040086e40901 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 636324829 1250 636323579 636323683
    0x1401030207050111161506030c0e040f0512042303030f070f1505090f0703051c0212070b040308090d021207031b152904090201051e130603020705 64
    0x80d010100c1c1c049458186ca202064800c180300c1190030b841010102c94004404944003400c141350445902c20141c0240e03140340c0c0794004003012441c103100800c070580310181d00603643c5142080913000e0a40e15540c18018811052001c511920b020089803540828401c1c0b490350350382c0c0f0785041c115464000c6070161041020b00741030040500c3d079a01c014050760304441115281d0711490075030b90380c4582c2400020030a40085082c00e00d4030030f900441c41d00049441c0151241c00d10442c90a680b280c1042d60b00f92104002442804180340c2c0001000da04005e40c140035103444020190040d640b400c10b001d0f060029800010b01e203051510034900844089800f00c5c008001310280e040c090707a58804400500c02c1e00e8038007000c02041924046001c03020242c84408001c104049004110080180b440c003a414001300300860803c003105601c1996001d92680c1070592148840414181c00026a802990525204004040106000042c840480c040b145404541070061701c07454588405801c1c0c18003100c0c04042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 636326079 1250 636324829 636324847
    0x30803070804060f0b0f01080a0b1e12070e01031205160c080118111002030705060f070216051807020f010204060302310e0406021c050711071401030207050111 70
    0x40c01c060140b03000340801c1c80301d00c0700078042c6422070300c0d840300c9203900100703040300c0c40103a50103551541c0d8018510000094a09403c401148001d100e4024030704211020b003190440d2803911429543c1c10b000494001c00090307081640c0c420074508180006400e190131065008031051041003101d03c00d840e03290804a09a41c10710748009040c08601030240c2e00d500304442802c07003d07508040a0362068128030240e10303c0020340c0600802d40c910441c100214001003103c5000700714200041802001482081e2500d4917001c80001c0c02c05052251010100d030346180208640e41d00c400211440341080400340740c00d511000b006030314183e9411224035403940081400981d20350540d0103801d0740800480e04003100f14031003010f500241c0280d900c62010120a04040c4a01c01c5502c1f107895005224031801450f00440700c400c81d10049032201d803181680d4651040007a0aa804a140f040c840107082c0103140c51401d29207100c11105042e40351034100b60b030210382d94003408400d40200d82c1c143c0844044c155684a20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 636327329 1250 636326079 636326087
    0xb06090d1101031d030901051c0501030b04050606100518040b0907021b040b06040b0705150c1908040b0a0915020315010906020c010912030512012c101e03080307 71
    0xd41d41050110b45450a000c04411030001c015442e0120200918980b01442c4010759a5812401d80b01b0302030320f1641d420500c41840741c420103000c1c40c020311440e86545030034506a4504040104014044c521034058410709542100c01d6441941e86a20a00300001d4841c001c00e004201c5000a1035022090704184242c40d83c001c10710424a4800d68500c03600c0700601c40600041e200ca00c0d010780d411400810040050441000c0038040162240e010360b900742e40b8100f000c5420a40070784201c0c1500d2400a5005030303100440c544ca030142d003004c0c140445107141c291541a9480002040ca01c0416200e40f800420844202e00412141c1a6400115220f08040401b00c850005514a640c003181c0350400200d0a03500000700c0040201050355481506800e055410308200030804045061000a102c2d035001075592040203806050360401018100c00c0c05280c0340c80c40c01101a800f000c40e220b500c140031030f00301e081e8400ea05031414284d4000391103410451714184820641e002a009060200a001d2400d41c4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 636328579 1250 636327329 636327353
    0x1801060503060f03060606030a051f0303030f1b080c0306010e04181a090325021c05060606040f090c0513090c02071719060e030403110a0f060203030a0b06090d 70
    0x151802884000143c00341951080240e404a5009005200042860a03141c000300c0d03003e0a50001010a100704a284406075121600118042a16001403a044108034800c8141890000b000d07041c01604200001e04031080261124900d40400400280c40d6409407034541499078014004105000605041491442181c4400c4815084900c11602d10380a090b80e142d0080012001440c03919122010b9541c0c1c692500c03d0070301c0c034144400319035000740c0d03101030300007907000f0701d4083e034403044507552a20b00e080c040000c000500c05c21080c0010f00480c1d12010049059506181c0009101c43c45100140e42e075024100404014801d070400104e054401034011000e43c040c90740840e0b007030341e0f1185403419800b4404c221400b5164044000030754945158107102080702d024410000e1420148070b803450540d4000e800944175102c07c020112101d0803c451000003c0144001d01e201103410164000e4030f0b440054450041f054440c41d0404403959100203c41d100200108100c1004490745001141100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 636329829 1250 636328579 636328591
    0xa0f03050d11030a0804060605060d020d0b09010f06030b0d0b100303080714070308040f0c0602010e120901080426030f01081015170f0f07031b060e010c021801060503 73
    0x14000c00940440c040c4000d1400c0110503000741d030803c14590000c42c0c045c08010410741d0b0b429100c2d00000740e01d0300c0e200024014034500180c050323a11180189030406580c40103c0d564068900300004200c601e0420b50400b05581c600c1c5400705580d010031000407001080346101600095440040c446c01208030501202203070b200f5112580d595689100a564154280c0d08001c910001003101000080c8601401640248600d90700700085906480e603941d01c2c00290030250150f90364000760f8131b00b0801000707424050440c1d509000e29000034000024400c02019000400300d1070300e10900034264880c40b02c40350b40000103102840d00c0303180288100c0740c070103070a11034068540203071b4141060b40b183c1d5000e0803190b0031001400a0302145490500300d40352484400d4601c440c00382d4240c1046400040c880c0c41902c4881000501030182581492020a0684030307108a04451880e8100600d60b000400c1104400003420010f2400491b4004569645000307502d50848492034400450b41a40010295020359 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 636330935 1106 636329829 636329833
    0x6070303021e090316081203180f0c010314041a130b0a05040c0605070309121403030405100501050d240b150403030f08061c0606050a0f0305 62
    0x210070b01508258000700044210310707840c0800c12a0032003c0e04d1248013000c207241040721942d48000100c1c1c41100000400000c50500c98000c440e070446840c00d06403483e000d9506002e58544662441d4907010a1504034156441010700d0201171146902182c0c104c01e230301200003184074410008141100d6003031250f5294000a180c00641c60044a800c18082854145890110868405504000100003042c0a078001280d40480202c0440e0054070702917a02080381e00744200c1d041602105401d69200000c240001c10400003940e0019a03a0018200701d01c3c0d80b10010032004070b46208029091807440c0d43d0301c490404a10001d00000407100200003401e04466021400c40c14040c4be01000c003010205007041419009038402d6038408162410090703e14101d80003482e00e121003030340b030318505110340700034403c21000368404030181c0070043c40010300d16600c920480003404240002c848074 = true := by decide +kernel

theorem cover : BRFrame.Cov 636151079 636330935 := by
  have h0 := BRFrame.cov_init 636151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 636151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 636151079 ≤ n) (h2 : n < 636330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
