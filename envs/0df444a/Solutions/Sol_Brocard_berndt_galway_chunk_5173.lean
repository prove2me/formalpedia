-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5173
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:58:55.956022+00:00
-- url     : https://prove2.me/submissions/57916cd9-89ff-42c8-9e61-726af1c30c5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 930215827 ≤ n < 930395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 930217077 1250 930215827 930215837
    0x17030f070f0c170d0302160b09060106080702030703140304030e040615030b090f061c05100615030e03040b0d0605030f03070b0a05060d02060f07140c0a06030e060a09050f030a 77
    0x9902c1c1410780080480750809410b1800b03000740c00c1c44502d00004d182041d080c03203050161f190312043c074403c000d040c5904000303029000c0d2035042080022000c03078828140c031070130340300d9140b540c07500902241d0360700640c80001c000c2000f400f001551300109902850707000d8881c0c0ba00480c80d0161300081026104103030320250291080c2c0b001102065054090016000c41c2682c4a017103600d01151000f80329640a0720b030a00505020b0400025804401410034079a42c2140c2200d031802d11204500700281403a1003030060300341d2032030a03c59441e8868000c000e6041348510040d0f04180c2030400720546540a003000c400d03501c4d650728000076951001d00c004254620f10300080c0d6142c10aa0914240c86540240450300141c649801c0104564405460801d03164040c1c1d02c0d6603c81609010740e034550b1041c1c40002d424080751014501190b00d000541440c045429241d0140c0c0716503075801a415a01e49000304500b542050000504480e4580d20a44071940200111014010750b420b01904650082d100000000c2c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 930218327 1250 930217077 930217103
    0xe07030b06101d1e0d060c14121b0c0105090d0311070309090e0102071707030e0603011d040f15060501020c060708040b030a0209060d0501141509041104170a2a17030f07 74
    0x3035080100325051184108c40c051030034040032503500e1071041c000d101403c501592a0022082c40d4000103848a4501050003007049003003440810b5540e10030f802c0c108000a040c0481819100c800d44103441960b60300d03880d48001c090a01c40201e0213010040445a070641d824081040403940807040914055244031406a403084c4909000304402580791401d4001c5408100400140301c1b000c0017403071081c2510002b0304003038465240011004190f501c019003006141c1d80f000b8051325465100714100c8400740c00301d0302c040f40060b051241d103008400c4080c01030700d8148010070005502034011035103c0b010b104010310b0024044005107150304034082c10203039580c1c1c2e800140607504084c030160100000c225940300d000105003545060610070480c1c020300403a103070900c10b040d64003040166000740540703440c422002911940c11a90300d80b050300e401c0ea0500d00030048040c6403555a600400501800c0342080440741c103002154120302c4200d15000301c1c1e44010428103030940100c10161040038814102c03400c03a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 930219577 1250 930218327 930218351
    0x1b03010b03031606050708070f270801020d05011a04140f0907090e01060201090b151801090b1906080103030c140303152409130e07030b06101d1e0d06 66
    0x1510010040414841070320117000d402034000c541524100c1d12761801d0042d1001090950f40c815401d0b072081c042c0d454120310302003801c0d4410b4015004490071a207042125a80c1c8002d81615507070442800d12546408010a001c544502d01d1040c2e401140980f8a90840c1c0c0d104005c690090000c903010000100c1521040c49000c40281c411401400903100a109404a58031148015540030f04613030f21007892103500349003039243e54407001c0e180d03403401e10940308540e52001c0072406050240055441102c014400200841c0741c01e0f00c5605480c05950b41510b04e80c21031390180c40c40400d80800380d44107600c0e403810102825080004501c0b45540302591001d0241c018240110060034541d01d282241c0041c503465010071103e01030341ca10600449110400b4000200101e00900d080840504540141c0c5004414080c44141441c0220720903a60460311607107034481220550040840c41c803803246001c0345540da41c0b03001c00542c03040f5220411804030309030001c0001801025610021682c003a2540b100368a4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 930220827 1250 930219577 930219581
    0x403020d020d0f090b0c0f1f06120816050312040302010c0908240613020c160f030305030c030c16051011090604150302040b040f080705060406021b03010b03031606 72
    0x10740c82c1c6820200d04000b02100081c00400361070040101c0340308045030b5062003401c00c1010304106068042515006615032120400100c0552443d00c1e51600308000001c007004280c041d0081d581c0c1203a1450308100c06070b5038084003007080c5402070310325100c01d20407072404526041c2503a009510940000541040101020705503040300d501c04900d43e0041e00811402da0b010303942c640344818502041c00310740e0f41c45cad100088044007541303c8280e0442c4007084150600b4000074489001481c900701c0d10300b01c16510304004200c0d00c0391b400002e0003d4401d202041c2c030f48116001031500a540102c9640c10000003109114000c400020207071070540c00311403051502a201e101d025030419030100c18901e850030080104251b07205500c59003c124030b1449035218054401d03815240604010340080b645c550780e546d602804040326003d5040d60340903080000507149446001c4404440321a0050075041c0c1921110f044041c00340c4544075055529002d0292079641c1c10310060820080060414280140c64100901 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 930222077 1250 930220827 930220843
    0x607030e0d050304030b1303020c220c1e02060a110903070b072603060118050a05010e0a0b0a08090c010201050708070516330603050a082805040503061324060b030403020d02 76
    0x1019101c06111121072f5a0b15054001003160b1800c00421400321100048443ea90b141500c0800c0000c504003000c0250307408160760b40200050795091180c010440c3c908400c80c8034960b44503606a0143c1c20410056030842e006e080e50030301030a4451012684e41d881c0780b04074030304512505c1601d0800000c0015561b08001ea0b01000c0c90300c2107200100f50b0420002c50007035216405024140074454000c0800e039604c021041c400351414030b012680b100180c4070050080700c019a1400d845000349032104003130303500c144180741c447c100541d81c80c02507454118058844da40081e904140341e1701101d40407004500c1140c0c000000203450320110f0060010a034060740c001c1e2035800c0c1111140d0500c0d02c00c1000c00c50000d48512050740280700d86a4a1003005101000100310004094184220b00c4040c881c0ea5041400380088034020340c103603100c1d640d8100d080041c03400003e000510a00300c0704098803071031107202c1882280c882c2801c4000b490540f01c2c075542d4940d0b00f0031241240181e0090150044a50341400495 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 930223327 1250 930222077 930222079
    0x3080106021506030c061b030d090b13050d030c110718061a1b10051303110313090e07121118190207020a1205010c0e0607030e0d050304030b1303020c 66
    0x206181c100100065102c0a02c640a01c2c850600455080c4107e018050b40300070742034031101103a039038800445016014081e01070007602c0e200e034254009802c00b07036804801d00f8141d6000f030143c01c2c0d120808809500905800c5202c1040002140c800210b2450820811010b040300c901e121b200004520603c3c0300792101900005584041e40d1090749090401c0c8094510055026026401038031503d000030b494400c0030b1a001d0744080c100010b010440c0000405030300130f6030282c0c0e0f801404003241881940c1d20f120b505040011400010800c01c002001a44260480c2503588181c0c0c424660f2404c1c0700a0320301da108000d446480c403441140441d803506040200002082403a032a038685440c0c98045212585402806045c54000581d101195140c42c1c4400151941c40307040a18140a403e02d90700070715805201c20702045000f1024040740c60180c0070b8a440c242e169072401a81400d050500102c1c00055500316501d00c000c3c0004000101c0a01d031003441031984250700000a4003504000385440c803071002c12 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 930224577 1250 930223327 930223363
    0x5071e0209180d1d04020a0c08070b07120e0a0f0302010e010f05010f0609030f061e0c05030612010b220e0a12020c010c1109060a030816051506100809030c0a0308010602 74
    0x5102c940c0c413294104040130200e500613291010410f080d110491481e600812010001880078104512031440703a0084040303030b8601d48001099030009045440300c0028410f158018407030071000980d00481070711a07500c40d100202d0b6046000f40a00d0940d0080021f0144041d00c0b40014403550081030459230040030149402d002d80b5185441e6110b8021b411803016081075201d08100038040d0600a041e800b81c0a00c900802c506e468821009240c3e401c1982c0c0345120f28140820104868014080d022045000418044001c550452442c0b0354070401203d4500c0151a80f01040188809011140031a03000d4020210200c203d803000a060041d61210a81440f80c00e040201c0420b900c1ea0418116101c26a001d098a03264440090080a240e0b8001031070400c001070f8496803603010b2550400024401e804030b40003138502803280003003401c00700c44858000c480c01c2c40000c0994450f05682c0d41125120060700e10b0100704480d0241014078802080d0007040c2e03410010015030340d04100c110b00a444040380 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 930225827 1250 930224577 930224597
    0x6060a05040e070201110403080301170c150703180b09010801061e030906021306031a03011109010c02011e031e09050c01080c090a090605040506030d05071e0209180d 73
    0x1024120307010764010100318900d401c0020784070030300035884030306240940c002d00e9841e95502c0c40c0000e000d510901441071500748211420f44400300c0011b000d40c030000d00401c0221422883e529428460300201c4c0300b6020044c1e0401002046c0302410301d400040c0c00c4aa4809560b0501e160024000d9a4103074001c0c001c01c02d2281149803510031820b1a468042180e14020500d81141d06228001e0f01400002108054444000203001c03605035004407290355028181644400003401010300303d8402c251361400805042001048079803081d00001c082e00d2050620300c00b08140c28030300501e0803002b80240c1d0b0100e6650031400280300a01c21a0ba412401ca0000512040c052992001e4551b884142658140040c50002c121000504400e030361440002a096486c00c07a0f9840562028107414403500380685c4c40d10003c03a031982000304e040d00850718151600c81c82c01d6040d075965503002030803280d113401d10001d101c404401642c2d030b50350040c01f8454190a160345130159100c0305080040100000b4180040401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 930227077 1250 930225827 930225847
    0x1106120903071101170c07150e160b160b0c07080403060b041a0f0411041502030d0b0301020f03131a07020a0b070e0a3005030705010f0621020102011401090606080606 73
    0x3001584040c454814a4480081c3e01c0c08c0b40038035501540b0140d4a500301401100741080000d0800910900d01040003503144c0d90b095001c0651081c0c1c07070700b03904c8503180d400c0220200d1000181c03141c101c0e040c7c1c18114604440c0e600c4070b81e900d82150700112000f1751594a80442880c09003ea5544111030050100714189100c00040407080280052030065440390f20447c41c1c00319410540d40100100c4000a142808109009480381d0160803c5480107180c0342e0a840e95040c1442541c0810040f60701309465a240c0c1000000256030b0144129000c440e01108070301c2c106125081035014211640050071035601c05e00d00b800825400070300c480b04100d01c000c8049225551001e401046810301c198503103c0c0d0851420300a030300c000c6441e00c105286803030754610301003150000041024900440007001b41326005207030b200c2030b24454404c40040c40e071540588040c140d480d0341c40034070040c030500001400e440948400318641209170b0003004016528442000034541101d599075000c0c0d800c07101c0c1850104111 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 930228327 1250 930227077 930227117
    0x2b050f071d06090f030a02040510030506180606061e07030c0b070e0f06090406050d14250605090105120a06060311030423160e062107031106120903071101 68
    0x81c103c28800e240c1911400c4181d102402101c0c0015005401441503103001c02d40d9a12076000c61200b100c1c94421140003484103040d00c0804100c4281150150502e41c07200c008200c400e401003a0b1502c103030072500881d601c007150171500030103031a4440d481d01030441c6242c0c245607010b490000c0029040c007110100c4500b40e5500d16031000c82100045036515203c142c00070202d0000c04140d007019410810464100d002d02c4001c040d40c0103080030802c1211114450101c148402801d071002c0c85061701c0070000e0901c0800e0140d4083c00d070100061600505000004601e174454181c180c1d988044950345030410700c2704681c14001d40d07000707400b05030b1040c2c91401d1560300e28906070600614000200009103044501305400d0018545902030301001c080d06a48440c0e00c0c01580e581914107034481c4940260b0054261822000170490031001c001400b2001d01e551a40c3c2c41405413050955403083c010803014004402d50410b05004040c0c920085444915a2070a501103101c04903a090500001c50700015440c0509 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 930229577 1250 930228327 930228337
    0x240905041e11040308030f090f0a0b0c0f1c0902040605030a0f0b04080c030c06150904032010150801200d0b03010207140f0d090b2b050f071d06 63
    0x1ca04006082510440c0c02c05440c011500000c10009001051000c900b02e00c0c0070041c0034000c00c17000e0726154031074500041c0d078489180b40000c0c03407001038200007a28100d40402520120002da01401d1800d012954900301c11103000510102c02e50b52581c140041d07040034460a00602410350081c28001902e4542c00300d1340d030703c9110050840c0702d500f000804102100c2c0603107d00360107005c200c0303480d0761118009548882080f20000760242101e46520b4080c500441d0190099400d0b0320340b11038041260000409a80b0000324030403ca205403c0c0d802c0c01031380e00e481613000d402819074032031801e1030070020f056094540382225035a1a014403079806072069604011a9081101c0311800100881c00c00f001c00d01a01074004041d0140f2219001d215100a01281c00f09802840c942500c142c9179522405552900403400b601c0401441845a4401002c0d02500b1f140307015a003036113210016a050700018152002101c8080c44409504140070751903070410001e611030104c50b0400201d100c01080460054014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 930230827 1250 930229577 930229631
    0x31805103e0405041503050f0d120207030c051212090307031e0306050904061a01140d0e0c0405160906090e070c03030222140105040e060105070c24090504 68
    0x20a484180700480c4150480e0300500c0f0142003030022104200421122240c948000c1e90107002c4e80c0580e00c0f40b4100403c45010f20301e00c0340c95060000c500016484e00940040340100c041c003042c001ca64000c2101088000320440400c5030702591000c0010522900300720140021115034020b10400c3c0000c3d40000c10001069011899254035076803488003100608995403080c0e030010041801e00c024130001c0e0f00110741d600c200850005070b98880e100115030b001c0c507208402081d40018403041542d14040e4103c000200007000845169600e5038000504403107056a1840380004031070702006515070001d0b9480000c200340d0130004101403170807072940c14029000f03010508019141d04060b007058001d6050740e0142442c41074481a484a60000b00400091405500945803112168a22940c410012541030710307400c1d14040c4041e00e42d88019910b80e003180504072600400d80f40003040e641c101c0c6083e11180c19101021562811144c04003802a604c0c41d04050b018a04000368900c2e01000c201c2d2801030144 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 930232077 1250 930230827 930230921
    0x1103040b04081b0307020103050618040209100b0c0d1103041206020d0e0102070c0524040b03130210030605152a030903030c1f0b03060f060103180510 66
    0x2070365103400650361040000c0d0340100802c0086151011a00101900c103042c401c2c0c80030031003031b241c0c03504014064403510440d01c0003c01c0c1e8400a40107080058205400c8510303983d210482645801c04041c4641020300c0c4034a560340188030075158030f030340013100c10040000b07a00690720341410300309410b034144881100a040c040c0c0010f03a01c20720314101e9101e9810103603004000c54070b690140c80d11031030000f01441242d10074101815000c9907000f540891440300d1018074009481e143c9084142026038000400c20000000b18050250241e221200801d41c1002c0c140d400052050602081101c040d4160780008021030050001001603006a02c00c2140a450b4591042e40080c807035500d54170314411445600d415000c046010010f68200080040746091065005880110000000000c80d840000c07a641d1541c008408140910960900c007508a0410b14010909403070320303901c01e244c00784a10011140d66020400309102d1410901ca10002007540c40e1081d2840801480500c1112401d00308460700c0c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 930233327 1250 930232077 930232081
    0x140403030e0a021f03060e011d090a3002010213030209250906120e0d0f0306050d0f1416170f0f010902190b0d0209040f09120f031103040b 61
    0x5941000b00310280c1d58004c0c0b001049143d80d40340c0d000c2040040038000c01080c2050400304541c078482108505aa19840080e9428200380000301204140541820300030b00174220140041004088020780e601310080350f4040d580d130010003002c1f03036010114510f002c5910500420301c0502000c0d420404503501164590780d0b68481410a1654003410607c000c0e60b604540b2204503059008100310080303c0080c7c036107a06812a950f00c43c0161505048120f085810000e040d0642c2070007460300040103d19841c0c0069000d46481c0461a4190011001d48aaa002200a00411028000442124100f000948800480c0c184500300d600143e000f00d001c001c1104400040e800c0c1d0030003860401c8100301086071513080c16406e00e90300800c0f00c1c00c0e0503406400d00e9084415032001600c8944112a400301055240400010316a0000c0d0005503186a00a40314409101980018080e103600c8600034a8100d4070200c0b02c0c080070700260280c03400b003424503060001c2501848940015280e001f40c020050a1036a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 930234577 1250 930233327 930233351
    0x11040b07141509010b010806150a09180b0f010e0901090e010e0a0c03110109060806010305060d021f09092a050714030a0201050c0c0d12020c01110c0606010314040303 73
    0x4070010055185191240300401141c00c040c000109016221000080101c0842c20004440850088402e80d0300508071400a144248041005040c183c40502d44800d80d03a4561500301420410207965060040d100c00c1015002d2030010402000d940c0c1c00d08110400d070107000007003202c6080521078203840c19a5940d03500007001c400c2d00040980e290a0307054522000d020b10b00b8200c0c106003070105441910071441960b8055000b40c1d4003070260358041c0c43d070a000b40d84200045014203001400391360480c5012000b140140c0b01c42041056003814010031550a1000c208028282800e56100c43d0b20745041414140c9840d81c00050345503034a501c4000c1e0030300c400d41614196424071520200030b01c1d8000380505803c500c20040701070400640907500904c001d07200d02060b00c2142c0100b5210841540000440c8224140194081d880e00c040e812030150415048400d1207013180c03004903070b401801c00e000403460094002031101d035a01050174282002400700b0860610403410004100409040d6180c4c2c01c0601 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 930235827 1250 930234577 930234593
    0x15121506090e01020c070b131205160b0a031b171003140d0e0f1f200102130509090703030810030206030a0e1011030a020d060e0a061811040b07 63
    0x6032521000070b100481002c40024000e60284400c0300e454000c225020410a08079002c5a1031480b00d0300c4000551b0741864a1050084844074013181c5902c60021100005107a501d080001003501e2900c00c1c1d1101d04808003c0c0540c2e10041c000c2e904c0c0c04140c882001800d400010b044a00c1c294081c017250f035039443d00c0704110f12400c02c3c1c0014142c13009403c000c1400c0c24000134004484a42a59070b84070010a49040c000b0f880030074600250300c0002514a50030301c1902d03d031380c0c0141d40414540021440641d200c81c000d200440500040d859400280c1029075110300411680101000e5488104524102910315111459404000c0400044038041107030441c81d8090040910340041c83c01e039a82c100842d803140180146196220f1034011400c43d815100124480d60441d40c3c4c240c1001491561949005e00096004500c40070500b41c0c0ca85020a01810700001c0911520700501d0001c0c01504024940e0001c00780c9018030810035040c41c0c10309491394081000d0307038115180d20000310780b2506c01c1d14144803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 930237077 1250 930235827 930235829
    0x606120d0e011b0f051e1b1f020706020c1909110705070e010303170f0f0702150f060102070b0406122307030b0f0d020904020d02030a050f0706020115121506 69
    0x410b20a05481030701030044d19040f020095105804440b100d00b44910500e50340e24880103c40c54a4204d51401d1500030800e041481900d200104075030007041c3d444032528402100c0305075010059114140503c96160100640c11580100701c950343c1d4401220804000800c255002c2c0003a101d0701c40010711b00340c607203c00942c0d44c9142c2c09019a90140e4450b2040303d05801c0910065000031211903d10074400c8014602c01e00482c0003001c1d441040d520011507010780f1074040e2100045200b03044003003540d070f28054100f0740100020008030b2658146003000924000b0150461081d000042008026160300000000340a01c800708002c21b81c0c044481d5104804101080c00701041d00c0c2210800140765810b40c4030b0004908112015800c10341d107401880310300b5a101c00000d4001d100304000c0b030b015160801d18207601e54801421141415030a60b41d541c00c2c054000034178000c81d480800c042c0109a028091086d541c0401200841041d141c0304071000c490300c0308480a0200c0c82c406e80201003c8846401c500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 930238327 1250 930237077 930237107
    0x6100e090103050105060a300213110c010b062106040f020406031b020309030c12010902030f060703050114090705030a0e03031302040b04090f080a1707110606120d0e01 74
    0x310303680d2420114060708084924911031620380c003003c2070303c1561400440c0c0b00d54400c0c2d4100910002002101c10001c8242001e81e40060080d0026218003007a0040c070b0980e40498003910f40324038101155a01790350801c0079042c4900d401303010302c115260104090071018040c1e0b07066581503450b90310218008082000250501c40c2c00090003003281505900409554a400420710b401e1500044040740c482c0110540668540c21811004903d4070306180c05144801c60540006081c00c0c036070340000c7c90030300484140440e0380c000030100034604d0f42600c1654010801d190180201e00260310000e441d04a00501244c24000080049001e01c42c05074804016140401c1c01c0b03d03035904000141c4454008400022440f42d0305280d0302070101c5c1480c2c0501815150300c9200c04080f50340c0da948002c3d90f0b030481030088007008030f044005000b4030090500d5a0085a4544414842d140744080301814900000d01d400e00802403407928907a40000000c0300078542203075151412080c1302030310040f04c00843d40e20304d42c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 930239577 1250 930238327 930238339
    0x614010906031a07080c0f21060117010303020303270105090304090e0f0c281d01090b1516140114011e090b0604031509171206100e 58
    0x210300344065078011016680201d0a040765501408031081d0030000445800001a00700f0340403500c9848907001400c8607642c901c08007418000004064006043c1d4800f03040c40d00400c00d014016996080030721401e103602c000c00441e000e1340c19605c001e036032803001402c0412000741c02809800203000021040d400d104c0c220000303000508059224680d241c120b070048c0c200310fa00d00b558581448500003610690b0b80b4084010f003155028030010000000e4202c850700c02540b88000a064440141d100c0c200090004099102c5001e054000101003c00050b004844560b00e400410a80e5503a0795004001a6440701d00d40c2e652840c60f6282e032900e800d44030078002c106090140c090343c0c2c200010b400c842c522032143d20408581da80d072403e03034a02d5200302d480340d0744450b10005028000210b0b03580040303200e0100070389074600d403582e00d640d008960104a10b0040099a844428004100d042d100b0b1203442d20b4030240356400d008424801000d00040605003d110b810700701c01072180c05000c0c000240d03441400400c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 930240827 1250 930239577 930239579
    0xd02040305010f0603110301020a02150a06170304060311040b0909040c050d0f1a0c04061823010306050f150706090615030311060c0d1a040609060905150d0f061401 72
    0x140f074003900d4640001c0320501d01c0280c0e5260681814030030340d21140c281c6d50044c02d02560b28140c000c0c0b41a400340070080000d40303a5902240000801509040002c0540000d6a03103c1c80e0040080444608005920b041c00c0c0820040001d0781d005002d9555142c8100d800f07043c580c0702ca1904001c0d0031841d500c980d1b0445001a48141805aa0302e0510421402403541d50700c3c108660b10062951042110308500742041400207010301845504190000d80c000c00b00f0038603458032418503201c852014100d10b51200d400c080c0d400d0b040d5a150141c03800402c02500c107405800711910000f0280030383c10084424581d8089000720500002c5d8002401c0940c0016003041586101700c540d05071496180000d80200300440714100c14a170000804505c04c03240c903440c06003002222040a0003822141c200c0c9014048180340d03440003941c542c401d4900a044000c0001405031030182c0001c1502d40c010701c041d104081000017209244c0303d403050017000aa21a076004480c55081c6052401042c01c1c10b80e529030140c074000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 930242077 1250 930240827 930240851
    0x6070e09060a05091509060907170c070f150c031119020a0b15100809060c0a0c0c0b030702010e0703020f0103091e0f1401020a020a020108060a08060a14060d03090b0d0204030501 78
    0x290401c4c1c0c0080a40300b0b0001c40c0d0b1f801091100f0440c0640e41c0400140010030200460032000c51380b60382042c82c03021118508071050301c078500080103d84081e2440010301001500343d0915215090801269003002d201d44003100b544500c0718028804090409411424003e4065100f0722411051552000d0200142c1c1800400c002c04100125040c43c044d0900c081040d02c0380e8081c02c0014880c00054000f42083d640c0c80310301f550749800070300c4e056090161400507800010300800c1401e000d0000c00705001d8580c13808440090940b081881684c0c0c1030340101400b400983c4822812004018003800d01240d1643d4519244101900c6601e00010490456010b8030801944400d19002c09020701e4040c2592120b255815080b441850036080240c1d005219420044d4002c01020ba4800380080c9142c1030f0070340d141d100341d0814002b1264030510650381d011603454030b09401e902c1600f1200c1030f1501403600d070041e5005450040c46010303400c1e0b06400850b0000301281650115000782d90302100921020103020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 930243327 1250 930242077 930242101
    0xc181e1a0301031703040c1a1611040b180412111915050c16030504080f060604050c130b0d150e090c011b111c050d090806070e09060a0509 61
    0x8001210f00316144c40111003007070036001c16a409280c010b9080030216242400c1e10700e242c201305007000741a03a01401208200f200340a440900305019410a129803a40b940c200001c0b0781c81d0520350f0780304007005400c1c4407440f00710900d07090f406540b000c098403042e850300d6010b4920591041902c1c142c2d218004c1025501041c00c201d91400b6481042000c9601000050040645600312a94504910140303d250120a4109900c92049000e0304089250030340380c0541c18184050340c42d400c05103900c421305211640c180781c80341c3d0f9844442d4035401c50070f0030360700005042803000354800d42482440200703240d4502d4000c1e07445541d10080e99140d2422050342d40a180e03400100865174400c1e00d00400340701000f6035000f207003409105003050710301640913011350ba581102104811801d0360800c0c40d481000f051051541c115541c402c0c0650b004010010019a00422107a401d810812950b08507000784401c079600f00c0200c1c0c491140071509034400c1d50720400403a03481021540300d11b41c45042d40c024407460000329 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 930244577 1250 930243327 930243329
    0x6130b0a1e080a09020109091529090d03020f03120114010c150905160b070212030c1504030e0d06060801060b130603021c02040906090c181e1a0301 65
    0x6440d10100e01e4040018071150328914650503000c1405100007800d00080c50b845003070308620504020031541e403650019804c1b139002c4e0450282503054503c00f0310180d20403040000c040c10311241c0c2c40520200d00c0b02c510000d07000d0080e1140c06141e64001010801d4002c0c4500307032891520404990322210f4009500100740020300c501c1d00c80b00c3c402032292019500c91b1f00100303401500304841d050441c0726004840001c0000038002d07600340c0034181d0b00282d82d0a130115180024801900a65104c0c0c280d4010407111102079862111540d104028044402d0002f203446030b9044441c1e400440c2550391802c081d034619000b1709020380e01c040c001c061841000400c2e4012020b036004800200a03840e03c5103107050940c4202204503141440325802004424882c2d00240124010f0000720107030034110355045030607a085604074085e0f02d41c0360f0f03000b40081600d61041056000c42071409004034400b120070100d0820260051160311800c12901e1080d504040d003610300200703271813141080784007451440e045041e002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 930245827 1250 930244577 930244597
    0x5010806130207051507181514030a0b190f0509040f060e06070201060609030308042d030c1511190318061a0105041a0c01231b0301140f06130b 63
    0x700d9000c562414447c00b44041d49a0310380b069002c615003070448461403040030310015410440700c07600440519450101950107180c4111000c80e40201840c2001040341851088a156500702102040300c0300e26200150701320f41c01580d002103c3d4886082045010800c000060000c5003482c810030145c12002a21a210703c10780d500030429152240300483d9940d2046c0b2000e0001444480400d0200b01000c5807200d4241c80d0725548064074203000d441400d1400260340c19804940c111500c00240113010a030301c11512032111042003205021110500b07540289189941040c84104456a032640240d02c0300c02c280b201041141c41c61011450000c000d85500d1886034010803000e0b03404840d07540504c003610155681c01203c0c000e06014600c403c80150018185150303a5903c07410038440c0b2040c1011100700707603451000da5407c98a81212200180e488180300d0f02d030181c804100402200d410980c00c2c40a041d070455448210040880c000b03501401901c901c1703118242c0361080003800c031103600b00410030380207 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 930247077 1250 930245827 930245863
    0x712020906211b0f0702041d060115080723090d020a0f06020f2407020319030c110a0c090209011107080106170307030801060e0409060e07050f04150501080613020705 73
    0x10790103904540900613115502c441a400340071041c014074068020707240350300c000f41d0104110310110506030301c1c001e420307840b401d10581050700189002e80d12450480e486116420014440f00c800f2400040d41030821143c42080e60b8045062041e9076107900030454085c1d00104031915075500e0715204500101c2c14407602d00075110304114840c40701e001041c542d081c038649405100300c003000303e030301203140c198014813260131800100809514410000303010303a00c20307680d07503000103280300301502c0507041540181140300c00f1342c44401864002104640c6003000e031440d0480250311214848010b0b00c0c0201c040000480314016101e010480d05015880038044408610500c0c101404604000e03481e8411000080c0001e07401d403005000c1d1501507100c4030044003000d0301c0000c0e41d06041d1540380c221042c480c0340a900d50841881041a45000812500658012142008030082000c549080c0109900c6681d040c005200001400e650b01c14003118951050030000b95602d640320706c0c00e2a21900c8449012880070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 930248327 1250 930247077 930247111
    0x80d0c0203090f0102070b030a09020109090e0106030606140a0b0c0a060e03030714040305190305070f0308151813051908070201080c0f16050c0d0b060909010203071202090621 77
    0x245c0300040030b000301c541040340c9500d146c40340070b0250040d0110480c140d0600c10074007400911041309103c5c0c58202401d6000015406013035150000a96425510101c05d2406502843c159a581e81d80075200302e5102030181540c43d12103009039400c2940101c8003800c0145080c0400b404c044000c0011446803003255030700c500d00c00c19500500b095004900000d4265801100c810f66803030080c2d00b070321591501a003403080c1006900d40d00c0c0b50034162001011000a40c1d182d09014a115401c1414a5034503c01c50780d1101598112001c6440c0380d030b004041184100faa0300500c42444030074440c40011028030680c0b420120250308040c55142d20a18040b80084c5c1c1c02c200042d0040e100009444504080081103460700c070b403d4960b81d011000220381901c5c240200306c0c0d03000b4140c1e02c0040311071115206442c01405450030000300280604001c200c070b020740c1d00400070402100d511400e5190018202180140c0b00c0586a0103e41c0d2405410050a42c581d84040d80420b649848e941e07180c40381c59031004918000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 930249577 1250 930248327 930248329
    0x9070c0501060506160605061f08190e0c09010e070203071707140f10020a080403050a09180e150403171003060203010e09010f0606090b071412271c080d0c0203090f 72
    0x400b04845100f0030100c140450080c0f400c0c0318403000354000c1101c4a1040714bc00f40d1048034400c4a40a40c20b03040907074481a04c030740c0da0b401c10000c12401000500c200301814904440d010391644111100203204680200d0b50200c16010002903540c00c0d5040000810300302c1c484d50312a59250b080c3c0c2080c03403580c400e00405e11400d10300c50007102c20900095503102425240ea644c240c030302d508540030f00c0090080a100c007144000d100d480b04d05000600340408901d0300301c0500e000741460039012481510340580030070030012942001901074940040b5058009603940c0610360408081c039030300000c001e28000070000540700ca04a504900500001c0004c000c0341e00141d003108215a245e218000114a050208000c001d68000241a0941c000c00c41c11400c0d0103000105410a41e03050176110100f070f004110120b20001c0705a41400e56080700c0305e1041c4000403480015002403103100f0340420301c52300300041000c0010110a0b41c0f6001107483c018802c407800c0100281d01c90704107084043c0654080c0c444010a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 930250827 1250 930249577 930249589
    0x30605011d0612070509030115050f0406031a0403110f210a230d1b090b0a080f15041a0301050a060e24030601030602210609070c050106050616060506 66
    0x124a200602d20361070508200c01680304003030020802c03014010140500003850b14203004a0f0580c0c42c4a60440700c0c0d085c10301c0100701e075001c4801e00709806607107084e1052000810721143d40307501a41400c403281560350307a4901101c80446414403501c1c140502d00b480701d500600081c0c2c20086035100382c40380b905549451220b20083c0543c6c903c00c0001041c00c1d01c2d081d1050002ca4083c80050b54500f402ca181403042d000110954141c60a5503240301c011203078034042c80d907000311501c01600d9448080b82c5802c1e0209070003481c5c01006050040c40c150030201242e4445015106240c4c0600041e000380b00600c540c0300c42c0000c100424269502a5080c1000a240070030940b041310305441c01ca40b81e068a50700c940c48802d2a02a16620034410031344510307200d42c4150390402169000314898400941c1d034005031225800542208400494012214001d01c0b00c2582e076182c001e035000810740390042050105081050140c5125809140c001c1030016108184420f11250701c4402c41c01280203204035142c160900039 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 930252077 1250 930250827 930250877
    0xf0d03120903050f0c1b060c03030417090d0b190e0714060409060f030c060318031d0402030702010903410d1a01031a01082d0703060501 60
    0x3a1a00103505106400c0380e020499450091504034101111801000301e80c0d8442255601540c1c042146040690600c2000840c920b505aaa2070304001d1421035007952400068001880c00a090064082e4041c45405840207990f0007002c0c3c11801411341001002d82c001a40d0b4144203094001e012845a02c0034020035000c00d040c84002e0604500d4040341c0701f0700c0f00828955982c022010840025110703102d0140a0140c070214074100409895882c103035251982643c001d070145401c00c202e522140105545481e8050340606004140e6040d80d84440c00e2400980341c180d60082c03001c02404180c0740d0550140240a2003500d4003c00c3d00f22845a80300f65190181c12001c800207001e0000140200305000100c50354000700026040c41000328241080c2c4203041008212145a0304242c2150340c1e250103840c00c2c0c00c61400e015107166000c200000c00c004c0000300340e060011600c140d00c03c680704440000520010b1048a2110359040c001306c0200a02440d12410b80002c000006403001103401c0d5000741 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 930253327 1250 930252077 930252083
    0x10903080306220221070c081207020a06052d1504184b020111100207140106060206010e2a07030f1d0303120a090f110f0d 54
    0x9003141c1e0391104100f0342d1a10105402e11110032810b403165040c05500140000000454101424101020340e030038121400401c2c1c0c2c020401c840c5010008204500110b800b9601882180d04080c1c0e134148060345407444452009080d14642000c1046a86909596554608090020742d0040011000300061b07101c06580042002c081c1040b12031321842c01d50701101c0107058100d40b04405d00301d40e40710301d80c0241c0d036417002082c0303031680c0030038140c60788140c0e07243d00c00d1420301101c2d003104503110090001c03121104203c000d050160b088855668440c0801c204a041d02411000b5903882c402440c0c0451105074029a8114039800d0010200ba01400461201d050340d07800303119091107075190790500d603d0641c41c0030101d099503103180300c42c00e030300c03010900908086000e41c440001c00c2400290080c8281c0c2c3c8021503c0301c03201640c8050b0702c2039801000325201c0b14599240c21440389c4800303503040c0040800d11001040e010545800c1c00410441c41840d1529141c2100e00c11404840030080c4045200c410b01c3c01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 930254577 1250 930253327 930253343
    0x90509040c0609062303061c03020607030f05041a0702161221020d1817030a08010608060a03141203040f060e01020405150705010605210c1c0803092514010903 70
    0x84642d841907017000d554041c0008255a103104c080e451408030341c0c40740100550050300454100400300c0c1d0540515520b40c03447d400704200f28039154503910b540600c0104008840a060400314088600c01c0110365584080c95131500b4005070340d01c06030804940060f1080b203000c1e4143c602023030f407880f40802c2603424100e290094890340181482c1161480300340c0050050599007d140450300c01c1880c684510303c0841100150760f0344c02048805810400c050784070804001c0d2400402c4448d846002c809412030340d008041c100d5030408000024108600780009924204000c800c0000b070040000040440301c0c0211b00400110344501c1c00b15090344694013400e03811404004144030707004003020003007609900030400007880b50f8552000481d640030100c40520303280341581c1d0303a0b2409031081c030080452240403588801c3c078142c10000d0700c464a81f40400501440d40110000700061000d100070302c0140c01e51400030702103450080e802d0110316224028101c20844201451205502410666041e42d40000003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 930255827 1250 930254577 930254627
    0x7120212030c120d060b18041b12020d090b07091a16080903160f050f0303030103020f010c030915020102040f0501020105041a07031d010f0e03120f07090509040c060906 74
    0x82e00f0840e41c022414024965552103000820550401c0a81454045800890400c1042c60100700c04c1d1190031801c0c00846c000d1510081546402141508040035400707005038039001a8100310b4003c00050b00050101d80c044010041915130005e60441903603415007001d88034042a00b61403281780220195001c200b2512100800403444070806400265002800c40c1d000091100108013a000590300c0065441c201c54818403180c40d0000c07401c1110107007600110b01755850341e00082c2d0101a912200390602c48925000820305129005c83c1010b4600e8140d03081e410140e00800900079407051181200100448202140399841800b5803405150031600000f044d2504003401003002c4806022182417541e6024800c2c003414421080142290302c040c000107094040070507101c29103211032207a50a0740c00c200000c0c0d2000314141c0aa07a081402200d49450555500400351b40d071f00d80540100d80d01503030f2541004100a0b81ca040107040d15195610a14402c0c0e851006480c188a410141e40e8040342d8210 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 930257077 1250 930255827 930255853
    0x14010608070e0d1509060b03010c091e05120f06060103060302090f10090e0f060106020a03091202010203040e0406051608090a0b0604090221160b03040305071407120212030c 76
    0x4100808100024100004801d541d5224031325046010700700000c030b5031211005c906100451007050140c410950081c0688890303848000c0610b07010340034070104881d50301030415090303543e9108400a410702603c9400da600d81c3c00305c01030383d841840c1e5031025184600400206c0652203130041c6800c40354080c5c030307803642502ca0080b001d06128005103003562851413107400013401c44007400b40c0c0381203940050151413062501481a0b0820405800c11b500799030002240301c0000c4c0e0b02820702d07000c032000c01541450311070b4140b00403800d600c5291322541c500301c100700502c0103000460f031040c0d0042d03044501c103e0101108103070507120100d0850b03800e5116004070101c040410b4075075482e540e0101c0001d10005901d03489600003850000d601000050301c0142c1c80d4810301d61201008509a400608061250740e58948a01c911892000500090800c0004074003c01045010080c10401035400c2c41a150055201c0b0b01d15200d001c52501c0032381c4200e84034003200940c80c0d0040101c4140c2a400030290981a039804 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 930258327 1250 930257077 930257087
    0x1f050d150203060409020405010b0714070803031b09100306090b03120a0309021816081003110103095a020f01140d1409010b0d03120b1201020d1401060807 68
    0x10f08207900300d03403180302650040e40c03035100d064040c02e011061a03807120101c4c14071a88224004003803030b5055001071b0051101040c000f050343d80c403418008400c0c102d80210740146140707028035542503401142800c1050300f01038146e00070505440c0c0c2100300300300c1d6101240c01c044e500c007584044800c07460310401c51904000d100f41c01c0185514009041159001200c14002540c01340440d040041d0403e5042124900e81d8011840c0350480e0300038070101503d80c25a220a001225911041c030705040d500e40c11001003000304c041903120f02c12452a0030030f0307903500801003440b8802d0701205032050040c080380904c2c07950202030340320003040d1101105188041003642803000203403074100100c0c1407007844820211045e080c5e03c028800e2103581440804d1f1400084c1d011034070b011020700407600d20f0b41094042100c0740ca0b0510946410347c0c26280c00034455800c10703020802462a510341e260421240b0300e1035a00100150020403400e04080f50400c070302050060015042c04003070203860009082280880c08052140c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 930259577 1250 930258327 930258331
    0x6082508063307060e0a0b010e1e1305070503031206150c030a0c1106090618040b03121c050907092c010518070605090d050a05061f050d150203 63
    0x180400d450a403500d8010000d4050840545050300440020f482e401c00045001d400d1507024240024481c10300c5642c0c8001030030350305001c1c0611114002000401d150015201101c1c0d5620390baa094000b400c2075003001c680214010000d0341c1c248582c0380700003280c1c14000704440c45000b2032420340100341c60b10710820002e00e1088070004002c030424009200000c00c207000034000100c1030340f04c9400d1415103180079891500c90f4100c5500c2080c00f41b003c9942511000122409494800c45a0341040e40150005008050144560741c0500c5481c801c9012048024010402507907000d5400030700c404c44142c0036081d03843c11120360070190025503080000c070f02d09802c0b203080b011840d581404000105400020307012140007007510745030b44030340a01c0014160401120314406000c0003a000040c2001000b1300944030710f4800a00a90b01003004009001c0c1c18003810201550003810313900542040d0308070742d54464001000c00320540d0034103000141440c0c421820720025074001ca07003903416200c2d905500029080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 930260827 1250 930259577 930259609
    0x2d020c040608031e0c2401080f06010b0f0a110d02010c020c0a03020d03120207060f06050f01030b01020705221406012706050d02190801090b0409200105130608250806 73
    0x551b90070b5884241603001d81c0e0145a000c001210903540c0351100c150702c0c1685110340200b682d0070010042c4038149101c0e0441d00d110f98001a803607a5811194400c076410b03000c4a000356298020944181c40ca2503041d0003d03034440d0010b90890303010584610410000e0201440001d5104090401c0800045c1c001c4903031101c0803907007000050900007991910f0003962079949800202580e641410b100524000c0c03028107d0200c2031808001c03040020b00044d40c0c40c091800f030340b032003500c0c0341c0c0340420080b04090640140100c4084140b040550020389030744804010f8030740301d001c641c0388101d02c00c4103c03075070f0306600a42c0500f02003a080a071420718180c440c0d90180c0c5100c0440c9408100c035503441c0c6120056607080c50318941d00d1a00b103600d4130081c04112195507240e607125908210014010442203c2110304c1105e0382405655150030b094010383c0c1038411402c4007403000c00503010008080d500105500c3c440c64401003410f0500d100d02020340b0b1117042500406000c00c0604e400b050003810400001440d40030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 930262077 1250 930260827 930260833
    0x1006020c1818010c0903021503040209150d02120115050303190f141201080601050d08040504020d09150b0a1a0a18090f02040504060506192d020c040608031e0c 70
    0x101210f030a40d12101c1ca003102282d40000c0c10000c500700b851076a0340740700c0c1a100740c1d0305505103a400501c0c020030251090b5407070030a03c200c0a00325a00d040301c04003e1940144903822aa2001c1081400303800d4407601e039600d20304208000241d50070301108442c5080040d1441080c1036203900c0c03081c3c42902d01c030400c00742009503011402c0c411241c040c004181550104640c0d000c0b961500340c80a1400c03005800c20b901900c54801c1c11070029124906079400d891080300c0168491500888880c0140070b84240a800c0109000306202d244089a10401c0030050503651042c02684500d04027540009034203418240700c0c001c1043c024014070803009402120041b1341100c001c2030b9600c2c0340c45c0584441810161030076030b0001c1d04100074605032003440000c240503240f19040000007842031010100c40043c220a020f1542e61072001000c44a120661500030408032543c07907a401c40000f9926812048030b0b81c001c0307190a0010508002c00070a0380e618004c0c0645140c88910710125050813030304400c010340c0d90740c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 930263327 1250 930262077 930262111
    0x71e0e0a050f3114071406070f02041503140d020105070e040b0d080309030417150606030a020d021306030e1506150c010f02090a06090b070201050c0a05010609051006020c18 76
    0x43c00b000c04001c00f04d01406242c1c4030107111650340c508110305540441043c0d000f12111902e5900c520003617811864004d070410303100740c41500115001d03110001100c42106005200402004181c500521121070140b0445903162844d006c01d90886000741e6051000c541c410030200b940e03207401c0d0002c111050380685009206d200c0c2d652625a0303a00165410141600086070074800d81608103040440c03c0070075002020f0b0b0104150120540c0d540240c003060050a002000800740c000c1d42d01181c0d210407910b441190784600e00308500303032008001d01070f80c0002405d00f092040344030700004007501e281c500d41c071040180d038840b50208000c004515801e07169000051042d040381820038807234411280e800400140e0348883c94403c001c400303c01600000305009116000f13120501c0c060050b291910747c203017001962045882c0e091442c080e46031034001c0540d030a110001c18810b101c2d8003d5030003000f03080d24100e1045e031203007030590300c410880d018a50011360980e0400c800080710200d2940008180c007030b10040d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 930264577 1250 930263327 930263401
    0xa030b070c0b0403020102030a0e07030c031407240e010305242727060105060906070b07020714030118120c050708070816060206061002071e0e0a050f 66
    0x2d040300700da065000d80d50210400c00e17041480e010b40c03403030401540090220642941c0da9032340303000c0160002070724040c100c3c100340c0112901042604003416420600315058014546004204122200240001030080c445041594043e0041030300981d00c522224465100071400509101e1118076501c0d481644241e0803110442c000b02c1030f0801c1d80c032a030b102000c1c51900c130840501003288102ca802c0505401c11601c00340340780100c1c00c5030541c1c02c122902d80d9101314110000b4600d0140d02c402825520380d0205001c030f1a03400080c1101114000d041d0700348a0b812540c10142207400a1500c4902c031216110950000380c903c110680c04c00e11542048002001d1540f1841d2030030441c0e41042e030b070701e0b0700604007405024010016030004070354464000001c00e0030030038000e48482003c0c007098010800d003082c00501034001c2c0310080140c0b00001d40d209460407503c1180c2c50080350361007107600344803092005c18480901c0d406403038480da81c00d142d00040d0703031516285a00755082c0e0301682481408245282054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 930265827 1250 930264577 930264593
    0x2190e060f0408062d01030b040305040b121f05030a06050606041a040e0609070c0b100e0a0b0411160215120a0f050a050106140a170103061b0e0a030b070c 68
    0x1d082220700800c1e04d403030401d2401e00100c00c40c4c000c0e80342c035400c10955039000500c95103126040d6540040c0d445055181e900d015291805143c00c0310304210800b04081e6110540d50392420701c603221540c12a07c1c0b2501c030300c2c030803080002c0c54043c40c2d4040d000140e00b48045000354200d60f0300214090f00044c80c182d0750f50b00d5150345640aa0000e030301d06100003070402c082c2030603071122908200c0861311428a0300741000302800a0511490041c0001410310006a0500c2501c8031880141a07503088840c1501d040c6210710010044841307868480d0340742034a400701880140d02581c1e224210301103615160700d400e408200c5680c15080c050a1585400c000007140e2855050403c0c2c00f9403e20f00c000b06140404480301c10039038800a21094200303180200410540d80d026041801015032010300503900d40e440e403400c6840103081200601ca08a180c0c000008103c680d9004002c20940d40d90551803464a120b0102c60112104182d40e83c031a401030000e2002c03658404545030230025904045165000f01e5031150a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 930267077 1250 930265827 930265829
    0x50d020a090b070807020310051009093210090b0f060a08010f0c0905030d23040305060f040203011b0e0118050910050a061103120a09050610090b0402190e060f04 71
    0x4d8051000700f0f03401e0441c1030801c0450700c1c4107482c0c44c0500c02803408015220001480d80310b0351a40a446120000a1280d46103a50111080c41850380701d21442c00b1305045078150162200744090710403134541c003500c200d0500c42d440f40182d1010016001d901c45014002c0c4101c40079041a521002980002401d07510034031070190300402c52900400c130905114030241c2240d07440da000c94002d40020031406c0905910070b030041d4921a10345104411210403002d8410f050107176420040843c03041d481800561044507040030700c10341c404c6000340901c0031003034031302c0360b2025101c1140c01c00f01d006201c0c0b8420b00e6014280c526405103807014102a495035500008400c0442a1011200040b9288041c0304a041a01e00440a0040c40c1049011103c40030301465581c0b041318200c5510712041e5005c41d4000c0003075000600129008002c071001810120702c0303518900040d10a101c192842c0100400d200d0503d8002d442e80a023048c60107545184507000d0588040c481c0001c2c06074031602c200004034001503c007010380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 930268327 1250 930267077 930267083
    0xa02010b01030b0a050108070309030e0429100c0b060402130605090a06020d12020c0a12020d320c0c09070504060e0d0c1715160e090601050d020a090b07 67
    0x12036464416800074080b508400c0c0d6403401204921028002030341c205080a03000001c600d0b0000e00d4011310709041360858000482140d0040c10f02200e41031000110483d8481c0d00d110504810081c0b84500401462180254420000c00d442420030030204540c5549694490005070016141019403100f900c5607584c1a00040049200401c80002c41d08001038018003910480c00200920000309001820305d0916100c2d000a1540028410f008804140040d81050380c2c8214007000b2041d040d1030194644401084410000b003845041d0f820b074501c000404d00169812580601041c1c12400d442ca1541d881480c2210862107070355032420023501c800320030a22030398003545c0d000c0e1946c1c04c0c440010801458113003468810815851074902065030f800750442156004000580449598140d240c1131005c0491142120130f001c204002e42814022050142505a95543c94a007500142044209a02130b28441d0000c1e0040c40440c00400d00c660046c1b607030700803a042641c400f40d40c905000003a1b81c0804011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 930269577 1250 930268327 930268331
    0x20a030f030f030504170a02100203070801030b0f012304240815010f060c03021f060f0819060506010207051c140f0a060203101d22020d0b04170a0201 66
    0x10052603440109040401c0b401e24090129003020340b66150207040c01403101003055000901e084409000704a00f0095040e02182503480c0d1800c80b00240203000240320907901c1d51a1040012030f51920b0310000c5060f17841d04006414840074640d903480f03042010905080d017113942c8120322682205917800d914054801501c11507085400e020142d400c00c40d041001044900c8810018009005c940c40b404003514060b250030080307191941400ca01e00b02d04171580218012111283c082d406045030000c03000e462003088095041c2d036850392190744d90304404c0c15006d0a00000c19581d40011081c2c0c000a4005205104032040316403a00001402068402100b0800c848049072010070402c5e07501f80341d52070b219604040c10100300e96a0146071141c4040400814990740040000d10f410320300b941e00c030050421155001e114005c014204082c144003614010380070a0007200c1b246a440c000d4444560b801d42c0608841c1c0042001d80d507640c1d15240103403048a228a00b45d00700c941e040301320303400781140890076400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 930270827 1250 930269577 930269603
    0xd0b010314040605090d020a050705060306151314010c08030f09010f1a0301150501050313051204080102070203100b012a0506043818011104140a0b070209071407020a03 74
    0x6c2c17800b4401d0401009641110320202d01141c03001c58030034111102911016540c0d40c0d21000595464180d90401000d8800400e46040d01184148464152003040360344415000c0c0300030040d21481c6039000300404400e0100005045a1210b854031a0040f0404001051660080340c03c003068401c0c1c440d428030400342d900901040c80c0381c03d010704264800c088030f19a201a041400003040c07440020038560b6448105406c202c1009030810500300c0750010494001d85564039500707124041d51144034242c0c80f1744a8169641c074901e1052040320003d2505850b01c00301d002c00005180d440c2c1da01030300c13989040790f020351003c0e0100f1800c0c0302c15840782d80f01d0107500d01030031090600c180901c5d0602708100d51440a04100702041c903a0015401e4000700c50780420303410070007030180050160194516420030366901140010b014034072040c420308502c000b21081c04400d915581415420b014484000e5844a41c0320302060300e081c001c5445910f902e1240c02907610b44206034000c81d01d030140d16403040b0344150700c0b090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 930272077 1250 930270827 930270841
    0x1060f022b1707032003070207050d1505180633010c081819050d030e030a0215030702010b12070b1c1107031709100e3c0f030d0b010314040605 63
    0x403178443d43c40441880d8038110705141100030f5851046000f458002c0d00308811281c1400320880100c0340c280c0c90f905007405549480e16215440c1d4044c22500311142c8a00d00124414824200e15a00044519045072000c2821110b05004420301440b0715814010343c1c16592010400c41c0f00203160842140050170100304410050000d0f01d40403040f41d95007d00c941205100c141c1d144041c02d111030344c040c5011840b44d210600000d0501d007407140c0007503100c400340c0c1000320002900e40c0030310301c60170a9030000c010740102501400309440d0490b61031760068004107018890481524003030446407450b814154041084c802d0680111081c88081d0b81e0700f0710000c10b010f010180e0020b206006140c3c480798862613070070f1200d00b095880c0304030071004090544031310040c1c01e0300324201720380718154911140900c80107501e11400c0d800c03143e080840101c402e1340082c0d407503485103000507494840e001c040c00440c03038070700f074100800018642c0c0c080075030406031036010114002c00450300c3c16005034081e900004803030034011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 930273327 1250 930272077 930272111
    0x4170d0905060f150d0f060b060d020304060504150c092d09020d0507031107141f050105040c0203120c0a030605040e010e0607080903270603070801060f022b170703 72
    0x7804262241145162410002c0c1c03080c07a41041b4a540210049500c050b40800035210b4010403440320724072803001c0704120501030542c0005001d10301032001002c0904082681c0016205001c8046011401054042110b51070315000c208105500c1415102122540c02061031481415805181144d40101d010110280c6c54419135820000c43d04081211903403008511005000d0890050203042841417450b14001062043d0301c0c20311b18004003034200111101d1100024030007170150134001c030b00e070141c4041c40c1400001100c107031420440c921501c560b47d40240b02410781c480300c030030000c16803919000100394440d4003805111030111000480c4906414411500d03101c0010290010403078502c0512040c450044211888034100340c0420440320700c04079a65100d52016000c10b034110000104110f41e00783c0c4680141d06985003070307450388480c01d04024200c0c0e8a100c1e408902c03010607980740610b031010030140b80040000b01241004000084c3c00c100c100d41001c0c00700c48510110761140c10504d070003900700c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 930274577 1250 930273327 930273361
    0x60a0c1514040b1e0a0f06091814070b03180109020603010b070b10050123090a140a12030207051c0210020c12070b251203020406030c030504170d0905060f 68
    0x160321050300302a803042c80c84200c000250440030016a00e031b0791030380d0300205074001c20042d10a00c2d8040c0f0081441d24144000356000f0741040c0d0789041d0201c80c04400c800041100c0080f1441c8404050541d100d040340240c525101c82e0000065650b03c0e030f0101300603150040514001c011907940b1507100c100c1030501400c4018018030310051041c00310b01c10710032681c003c1c0d46c024140c00303589001c000d0030320003081041c0d5500c40c01c01503640c062542c1e8070000358000421618100d04400365101c02085559880e80356004801c9074000340544c101c00b0042c00703181002c04209041020302c4090a481c41160340105407251040300c021001a0050310a41a0bd800d0001000710b05070f486c90b000740106031618180710034034011080040f0703102540d03211078118105c1f1114003006e0f0036003181038580404052000a0002e5100e84520004a42002d5600c040f450081c4100c074807541e00406502510300d03190307151402c60751010000808082e43d4802510105001f000034030300c1141c02144c002610f0030300ba00d2410040140c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 930275827 1250 930274577 930274591
    0x6020a1208040b0415060b040308041401050304330c0809070803090117131403130e010509190221100902030c0d0b01051c020703030f0b060a0c1514040b 67
    0xa040c0c1484006400040f40c0c6a0084c5c02a614003911aa446141c2c0c01400d19030703101420303180004c034001c401d11008500400803202411000074a00c4e14a03001501e00e4001241d001e0500300000100c4d91820300c01d1100c8140d26841d8805103954107564000300003c03174025280c0c184c0000c814604105002d8010403000003e440f40c80010360401d484140024610450102c00c40040c02c0e0202c041200c10b250191404e42e4594400d091541c9144640211603680d00280d6401070a00411800010489415000300341030b41c00107011849595200140756026204a84008140b16030802411102c0300034000e00c2aa40e13904001c183ca00c0c0e041c18400c0c8a04815a42c1000d40d000d8410400d00031241621070454880c000380351700102d01ca03050000181c0f428042d0300140401c043c00505002000e0752264014561240700752410098203440303040000440d0100e051040d00301d0010441040840e0084880c1140c10b4407071031071112241c00c40d6103070f06d0130b842c6c8504820300c5400b42c0340305001c20013500c14451a80125 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 930277077 1250 930275827 930275837
    0x311030d05031612090b09060a0b0a0b07080a2d12050c071b0305070b0a1d010e0d020d050307030818030c06063d0e04020c071a040f06020a12 62
    0x7040001030071169603c0c1003450502000714594200304199070844c030800c80d0080280f62451915440d41c035125803085501da041903190201c80f40051600741c150a046c1c030601c1c80c00a050158030f41d190003040c1e00160043d0103211139001d0300988040100c070844070030728108901c0209040e40d05030141142c50000614041142004208184030b414081560703801c541080c244803000042509a050030006904081c00500440202042e020041b40051882e40010303501c00c045190005003218100e0b80c082030041c0005c10545414000b482d24240a008003800180b8500c8440605d48d1014a5a480740a0440204401c11304000741e41c00c1840c004001a035504024500d00803801c005203440700c4000b44424401e6515520950350f21026101d8407104000042007101c0c1102c41c040811441143c9030903800c001a10f000f03259455041ca802a0740031030720742d10b00401c0501d040059152014481d00800c1641d01c0042c4000a50070180d100458001c00741b6401a1045007101d06140403000300303281c84001481 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 930278327 1250 930277077 930277081
    0x3070503192a0206040f020d08040e1f05010507020307090f0e030d0c02160305060a0f0b100e0a0f0311091b130603110702030c1207091a09010602010501062c04060311030d0503 77
    0x10b64076006c141960703074111102c01441d080c6140c03015950045801540c8980c880c0030800000b0210301c0e6200b000000b000070700c0c10585540304011165445202d9009400d0342003040d04000b50100d941101994000b81d4101003403440c9030380d2080d807a5402481d0358540751074031512807242194050081c1034401288101940465085888080d80c1c0c40026204207040c0390b685104070b90700403840e40007411941c0f00509482520b0b1104000800c0d216024801d940300d4519214009503d260318985503084070350000078a807050280303404000388030344001d00c11011401802c14400040e0100e900070440800380012a0032900d080090003411100880781a03802114100103607800b50394009080900000b0480304034650b540a0300315981000000d52050114600382600c50b4a01c624451000c407101805440c5034100740ea9400049003610420722600000c141079039a841d550503407142c41007080c41500c0a10a0104c0b00e000003003402c85036168810b9900301052501084503113010311140d0f010480c1858014154 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 930279577 1250 930278327 930278333
    0x12020909120f1e0c120306220c08060609310603031206140a030809040e0f0d02060c07020d0308181e010f27020d140606190b03070503192a020604 64
    0x800f00c0c41501452405c0210018a66544004541c1c03591004c4d00072100f07908058142d01c1c0050310000c41d244001c03410107000103615082c94010740d654510f00a02c9a003a07055022a600300c0d0100200006c806800d44c0c0b2130322090701d80d0307038054540298800e075a0b03840c17001c2c01d20101c0c0d400c44280d50000d00c200e102c4140740001ea942e03030551103025603402c00381d8aa902e800d041c00260061043c90080034182c00b0701c0b0f401d500e001c00003181c0410040815000c0d1102c658134205001d44610034141d00075405009024a400428403410071142d00040a09090080d02030351804140f4054801c0102505101c0c1070101c1d111126080c041c4990383d07031a880c0c2c144130100301d03015541440e040403d0082503003c1e148207007000f55918105da5000554000300070b0b12030348250b902c1e010b4603100c040300c081d8041d491003840f41e01c00031180f25581007100c058400319419901c0380310040b1200d51010342007402c94078101017943d1200301c0c0c9200761607045e04840f14161100740400303220300145c07008035554010b43d0000420071000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 930280827 1250 930279577 930279583
    0x609150c06090f0303190222030b071202090907032c061005092e0e1014060307020d05180907021005011a040302040c020109170405090109020412020909120f1e0c 71
    0x5404800d2405608d505904a041d11101d036440c251441f040714509000051084139075a172030140c3d0683c0c2e107005040a003a074249040e8415181e29640041e40b50380024411440b940c401051140030210b0071048000058038a0380031160b0f009800f40c0780d0000800e0000b031000a80013803009000a90b1b81510314906404082c10040d08000c42d104040c0008600710010110300d803c0c0000740c0a0200d5200075402d18807080d800d00202030003444c42002d42c000700300d16903240450a0368801d203000e0380101001c0c50107440407100c83e00706004e207007500c0704821800400350b561000010b11414281c0c0c0141502c10035400302000b6907006a104482d4000c41c50494020251100125810b99806403400f02e0029100d90040b40102141100a0200081100340316062030f4010003c0003103500031585a034080e620760004101300d11481c4100404403506543c1240142484c11a055000030f11001f525906ca2801000c1200c0380d20902031a001d4810000b843c100b280c0000400341c0a04031104c1240f400c14401e2450656 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 930282077 1250 930280827 930280861
    0x1d010608160315050a06050c2107030e1807030c0e0a0617090a0b07053007120e0607122003040201180b0d020c25050609150c06090f0303 60
    0x10406885000d40411240f03e032121000400004d001e084002c0c0c0c2d0354600914580001610200c5401203030782d1040d100d03144d55842106080403003070316403400e0020f6030141c2c0d0452881000039048030240c0386808500c1c2403016003c0c0314004548020802d12034a143c0107010503858032600d8441c034000541400303030b1540803800c0b0003100512500303031690380c407030441d9107180882d07014006080003400c004210105503c03401408168080044c0307442e511603544542e035140c1281c12004c8195903c2c000003d00d51600c21088800f4401201e0070010b9a1905d0007100e50400340106e45081c0401e59003081e40603d080f5070302c90036000481100b150443c10010301280c01c6203100c00780003c0e040081e0481d64094200301035600000500a0f0f034040d554a5001c070b00608065005010080894000c03403687c031001c02940164204050f0460300804503c134206000c20010341c10088841c0c1e044041d80d9402802c0c520302e40c1c01040c0075000080203210501c1c00300902480c1c1195154034400a40041c4144500350b030034000480 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 930283327 1250 930282077 930282121
    0xa05100b040b0703050c0f150c0406140708090901030506180a0c060c02061303031701061d04020f0c12070b010f0317030402010c2102010b0f0a0306110f041d010608 72
    0xe40e07981da0500702150903020f0300c07803803100c40d0040441f41c5e41c0050001601c0c2c030a00090100204030307665150041e501c6405584140000b00d221f500c8802e04102724800100340c00c600c1550101e0816001c64089001350100360411203081d03103d01c05005861000142111403000918020700401d03020b961007951041e40b0341701d040306025200320414110754486040d10100000407104c151826500c0c18028500610002108404a44440007081d178a01c1401c00038503030401400c0185880e614941444025480544696025075080c440420900c50900116401c03598102c11513031200044d080c184c10103c01a449182c0303000d50b00c40200000382c0728a800100200320740042a44a985a00040e40c101300562030042a1204203001002c495900c0384031810700c2d1a09074000c01c003507105c1a05104580b1091005c0a5100231040802c0000803055004a1460070640403520304191070781c0030305056500103400c02070030300910113038600701c80c404281c6080c01005585000211401c00c0511032164040c0d8603102 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 930284577 1250 930283327 930283349
    0x20708180d080a0507110d020d120306080106060509030d020c151608030705070615080c061308010e1e1209120a1704080114071e110a0b0a05100b04 65
    0x1046aa1008106001250008a00d0b07550f5801680d00034000d52041e141203030074040c0c0510404090070b1072011203541030750180a09244003810344542c403401ea481811201015182c4c00003040c0840c080c000d803001061399071a00313038880700910300309410f20350341c800d200c411907010b15030847c500c0c4d4890968084038995803030a140e803014441c1c2d148405240e4005d024141c920000280513903281e02c040108480743c001e041c100144101d204c498a0101c000e84a15a00b03071b8020041c180c1c440c0f800030020300c481c13604c0389079100030765503504042d5003911101c803c10f19054200703d040e2008140076003500709140340f008018150181664030024032070b0240710441401400c82000c8080403c00030402104030b1500701405045a50403080c1044881d403042c000e0780320303550800e40103d040e0504081402c0c00381c00143c0707641800c1c5503941c034445111002d81f0707005d108015242c090071074150024031a0000341c1d400381e0492042841c021290800340c602c0a842890389140d000020020042b80710181c50a9520070b90103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 930285827 1250 930284577 930284617
    0x3040308180c1504030201030e01060803030c210c0a200d14070b01090608011d0a06022503180618050609040f14010302040605092505040e10061101020708 68
    0x5450540310615190300f210100d074840100f00c0e80c0300e001d801224401d030380a004a4001c3d00c0614280d481910502c54070f030340140040760050180300c01905400a07030300e08189004c20f801e010204006000d5072000d0f580880003d8000c4401e0388052214680c1c0c1d084500f41d0724010306070210941e11012032400c0810030840324501700091425804035201190024034103456561a0130090006101601c0b411f2603e606e4134000c40080070040c207010185048020251240344040e1315010b02a50100d8035890501e0304032084810300300d4480c0040308140707002c0d590341180c0b40c03421881a40212450381003001440705054218408016020300582621802e940c8940c8a2030610003040c05440b90411008125091131000c903420b101c00524241240d000329402e0021941d514284403441d202a40c01080d05030904c0952019080c07256220000650281b41481c509960f0740c503030224442c01aa041090f201070280200203071070303000002003114041d18000f1442e04500b561004907078464520f1030f41110440c445 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 930287077 1250 930285827 930285871
    0x8060606120403230d0b24040513020405060304050c010807080f041407170a0203071d011e0e0412020705010e0a060e04020903030f031608190902040e030a020f1203040308 75
    0x3c050299204031132416100c45124180e54054003100c441240a600b210000902d040041e41034001c0c0030407035980c040c1c40d040c18201800408103400032910030b620b400b00000150341d11117100452165000d41c01408040100c00001482d150700586941c0800c484003080c08410704101c03000640090f40081d443d4800822020100c3c00c5c01411752002e114000c0b80c0100d95440b0f40701003081e082d510310807020b4610306603c800e0480c0801d0ba002140b00c030303014900c000507c1003d84803100000f90080e0192820a01759580d24460399425003280c0031188940481c3c035120030742e45c04010f110040e11013424200301041114002c924851290302c18030081241c4030b89820b6958031583d0480c1d000c62070280542e65601d100c844a101141d0044d1214140003801034101d0141da4800c05115001f482c0e00320040d0404c80e4100c1500c401341c010031100766485590383d18801c160710b404000510a041c003940241003400b000072100c1d400c03c5180b07404821031020401c104000a54480c8010754000313941036810f011410507007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 930288327 1250 930287077 930287117
    0x30b090714101b0309080d0e15030108060103030c0309050918060a06050916030905070608160201020301180e0c2101270609050f010603060b15090d2405010f08060606120403 76
    0x3910031003944c0900d04007c0b20159000c5900300081d00256847c50b4503004e49000485107200900c150383d42234001d5001480000d1040c4c8500b07003401e0192400b02240b54892000039101c4000341d4607000030700b080301071040c0e0b500030502c0426844228010100000751a1501050b62510024071164000d03001415103513180d402a401980b400b90408221b401c0c151b03c5080250400000382c82c01e0180c0c25038011845042841402124141c40c2140d0780030008030403441101c400f0b800c200115032114028070503190f609444d240011a8100210300d05010b090010071426400c580d6050280400194000c01800603502119104120a540080005210704850801a0a00b141e025808010f942401800000c0c010709800448500d1011501040e04603030300c40000035103110320540c9030340100c03000d41e281020412403440090030810400c8101c034003400060b50300003100d400f6000035942c041200c0060108e80004c00040e41e000c2c0084d25468a032000f030100e104501000188001c0400150b2803020506107045 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 930289577 1250 930288327 930288329
    0xa05061911070b060f0a1202150c011517010c050f030907030209070507060c080f0f0a061d0f0c04180e01230403020c150409050a06030b090714101b0309 67
    0x40720080b51200e0142c5000c83d04210103480d039030f00ca010440b1041c1c1891510003880d1088814042560503584400d0303007070210701e0851881502a40000303101d118070904003802031a6184511a0031404507a040480020400e0701000100c40140c1c501118460820b411200f2208401d90882a041d100c1d0b0301e09544070b05d408400d410007500101840b061161003504403024000340780c4a0360080c0401103605c0802c807900b080032258103c902d8110310100b00d840d41009030864000700c8042c40400d03920b44911b0809401140300e494001648000b5041055100c1441c025503003211203000c905260900d804d504a9003680c44076224110140e69051158540009600110404602c058401c00440700200c0040c0c802c0400c41d4244c0150065081c0c034600c902d03007920800003410700d41c211035003801d090080030b44c01080c1c000e0241c48581c1e640c00010002c2011020070790710418a01c0300804c4450700304031000d000020101c07080350244100444055070150072080d014010580000f000107007031150b0808803032030b1000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 930290827 1250 930289577 930289601
    0x11130213061d1908070806070e090901090206130e010b131505040509040f41030403050703061b0f0206010501051606050c1e250312140106030c020a050619 68
    0x70300003440060f04028074210046508000a17142095691603030316441d20030454600002a03040b041c841c11038034002000c0c5801204803130001074030010f15808a5810350000325800000c1c60705420800030078800d01c00040c00b410380d2806803803c100001c156211250124051290100c0f401c504440c80e81d480351060f1002400300a01401c50b80c2480d0801a858002e200c01c20f84440b822041041c800b0441440070244001c0c0c15522010055003d6000c80042108540560400c0c04201f0000012500400c203400203135002e0341000071844000c2c552200c00d89013040181d0b061000a469040f4210f40204403a81140c400307007001907840c1254142007810104030321000300310070710345000d0055a40004025040503a80d1060013405440340580d0b15042d40244081c5185c02800780300241c6807407140f50420305200d8460308250506403120140c9805403100812501c00d42c1c05124010400c0b2907050041400300f01c2e01c0d001801e002c50882d16107036291040181607099a07000207801c484031010507445002280300d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 930292077 1250 930290827 930290839
    0xe0a0201081b2d0901090b0a11060c19170103120915020f060a0605300a0311071d131502070507050a050405010803070f0206120411130213061d 63
    0xa85504030031108007840e40b1602030510080365050f2680404200c80011005848201c003452808400c00c17550f81c0480120f00c200310006c9010384c0240c0d810820940101c5425240139145c0a81440751000d02c00f15000c42c0c42085203841580c0c181aa450f050241901c0c3c21084650685500318010f03141ca0040e64015540000361040450340c4a41c081504a203824884081d02d44035211854900107550039401820f40c809004002400440c0c020300380d807080c81c1c3e490360070980b8070300c0d05010740c60401c4042d210640c0880d19800b404042d41a00344641d002820364410a1001c0c900c1e071040c10104110018840c01b0442c1914846005111319502d150400011b0713000f0030f643d0743c140b034031f880d40c1c4650040c882c640c0108501c210100341c42c901402180e050301d120074020340c203000c066101c0241d84604958141d0f0070490170055000351007074400c00184560b020b28100c00c02c41880006010510040f1402c15002d0307841409102002680649c1c0d040c101c0300e851600719442e085100c94861464058428a8ad1140c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 930293327 1250 930292077 930292087
    0xd090309151d1e01030f0b09090609060906040309051e060d0f0605030a0f08030712060e01050907020106060e0f1306080a0302120705120f130603020309100e0a0201081b 74
    0x95840216001000381d5030100d034490b26220403c2c4910880c44a02542d00703907010311400d444551003640500d45807006001c0100d125910080411500301095408a00079009001000a4141d00700681c0790000c40010050815113016203000b0034100050060354441c203c801009a0800700c1040d281c1e403a00780051142c1d964103c40c8018000403c240f00d24444541d050100000c2c042c0340105401a2441d04180c501e40104d140c0d940f680c0b4940d1008004509006c0403903512010071030740340300e0748014010a0a80001650411040020980c4020131800c116030501e1801c1c410140d00400d001c41d182010345882d11021040302c001219800e94000041d8a14074040780040d54820010741869040d01a4003914240d0b601c0c0d88904000340700c0d1200290040c2d02c65840c05441242e13501c0102420a00144240c5c2042e003291001803c515042e400200080d4002c020303c08400028845122a1100d000080080c0d0810b1180f040d2a0040100c020b41407103e46800140d1100c072052918a00b0104001234980c2c903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 930294577 1250 930293327 930293369
    0xe09090309120307021e031e01090b0c1305150708070f110a0b0307050708071e030e0307050d151404030c06060905070c0219080307030e03060f04080d090309 69
    0x25000081c009101d85414040300700200004401c44403469000f4140c1c40c03150076590b8030303141d24850603610190540b0030312903403050415503d800141030088400010452510300d081c6103112207000740004480b0350081040c0015181040b216404441040da4260b64159000c1d00c2190b0ac0d00417520050003e460004901081107250034041d900780d840b0f111200d00c0110a0b40a0080040a90180520002d02000417491850080b801b5082451040c4003003862303c2c41c1c981e2100e10740d00000011401c030050b0500580100342c0c00c0709005c5440e4100350014441c15107024006071490900c0180038159420301c001741014203030342e0380240f6007403011946126490f041c5480c00900c0001c44040c10345200e4a400404150b921030781c040d042c000c018aa80e09100700f0035030b808009500e0302180c21401850154417002030030380380900140c50f0081c043d848000104800c5010315040200c010840d40c00f0704070345400c010001d10010107584600d1401d84000800d80a1890243c81107011a00700c2d003403610340741c145c01c001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 930295827 1250 930294577 930294583
    0x50a05031e190b04050d0e0307030f0f0c090203060406091509022104080a030e06131e0c140123040317120a0912020c010801050112020f180337030e0909 67
    0x2403417084045907590a2020004c48001207113600c5540c5c950406e04003000458402001201000d00807001c0401c8001142e1355010ba085095100300021600802004900d1916124000042c14952801e00c0039500d494213605403215030703008440c102030740804c003400b140f0317070546484c0040e0b000815103100500f45030070184426040302d09444006400e0241001d20f802021581d14010321001043d40712042003941e911111032030002c1c00546009018416401040e040d09034003008003440030b01e07400041e0110300014800340c0603009214524600464040c1c41d0702c1d40c42c04a4040b41d81203416121081800c1300c500d03040b40306400104044101004c14071040101650100c0d445605c07441e4000b140d1594500c041c1c1c0c54010071000c1d43d0100e050400104501d5001e06000d0000d05101e950062904080940c034801e01d40000c502241c00058103034031002141010044400c40130380c803042d41c81c02c1307024111043c00250240026580c01c0b1948004100c10140283d4524415403002082c2800f13a151001f40165 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 930297077 1250 930295827 930295831
    0xf06151819030c0b04030c05061c05040c050f0603100501050a0c06020a08010608061c150b04061d010e09030702150c100f0c030212060d050a02190807050a05031e190b 73
    0x802c2d00e0110f40020360344807848102d404036540656041c3c540b07071421007040078a801c0310410840714082061408000303115032069912603071207038540078070203402c103c01d201d03104035110710544c00b03081c0410500c1100e07c00310760342d84200e5a00b40b8204c0d60781c1d40c400390216402540c003030008004c030f170020454042ca01d4204c900c99050700d00d1603030760342c0e503d0361640708201c258a00d2404901e59001d0031100200410b51544444c0142100398101041d0240410084ad04449032907210b070480c07044c00e01403244425030164a090042409aa19001c5401c04500c015206c1c412000000d208a00070210082d005642c0001d4841c100e0070304044c5c407030781c00710003043c0e6018021800410213420310b40386000040d68028801d0711881d160300055520650703506014888021001502910944a401e034800f0042ea20740241c8900c01c412548122032881c90010b659152400c41d0300680e01c07424491805001c180c4000074890200300e01d0480a03002c2d14001e844c114200680c4901481d0f004001c0400c003428040303500c108034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 930298327 1250 930297077 930297083
    0x180506010e1504110a0f030e03040807030b0601020705030607050d110301230306010602030702090604021e220b0a030c0e10050c060c090a0e09010e0d03050f0f0615181903 75
    0xc0080c2c28000400c0b0032181c1d400c40d407046140b01408a004214414030000c4003008003420700040c62803020b2001883d43c0c1081c1c0c0030720000d601140c0f040c000c1112480090350014028001424143e00303010020b034940e000104101304101d40403030080320386402c54002d000f807058070001440c2e413543c42d1503850010469400e541031b50100700f1850708105060000d0f00070304880aa9001c0c504220300c0754200030302c80e00090030888c1c2c007039000e2086003499100850b01300c104090030400c1c550f450021000c2001ca042c0400c119200b607021066040040f803901030121800d0440740d02d00001c040c00d81303400543e41d40c035000314800d4110300d0620b8076205180e0000001c02d45d0b14148401c039102940e44108800061007105c40e040d800c8481d000081142540801c01c090b00005c0301e1001144800041d4501c92034141c540948400007501c0d030041c850200071018003070350002c038112800d0310240340c0400030a00820f152402c1d0841641b001545201d5101e051a0359429003e00815000c030301509110840200705840c0802d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 930299577 1250 930298327 930298351
    0x60801050f01021506040c141204140114040809010216030c0f0e0112060207170d0b18071d04151502061003050a0609020409020d050d0f020f030904180506010e 70
    0x101e400e980000f480030190a200c030b112154590ba0b0b20709000181c040d0007082400e104104400201e0350964030701030318030340755807800791800c6103428100700605403c610b00c194440e92400000c2428810b0401d1035a5026400c1400d440d91941d890004034501004c2c040a091820b24645000c0b0412281004400c1200c0322140580805515290312480c60a0b00b8440c07609a0010301b61000009695900070b808842d0103082164180865400340e90310760741c004c400314071155513a810303a885603180042c0380717004410100048d1030a5142410002e850b082001002250160300d20301004902c2d40c1d29002501100c1380d84c00100c0d03d0300d54960460381003140040300c60002d8050b078000103a42041e62409001140d401000410180007240c4501000f810010800c0e80c2041e10381d10380c500561110000c2e00d051038400c400074141c0c10400d0400405400019420000319044801e5114036004000284c401c4964201c6000408100034201815015107010009000d030042100001e035400200d00340d0b03031140c803016400c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 930300827 1250 930299577 930299599
    0x181a0c0d030509120a091a040f060801030201021b01050a2f1e0a020d0303110f04030f02040b04050c070b06030c03150a200307030e100e0f10020301030206030c0c1606080105 76
    0xd807444d90051040060024880d041e0800c800f0b2105403c10203101c541070001494603840341140800039003941c200f00007240b01c0100402c1156070401504903500c0030105215400c0e6901741c0020700502ca0302e1390200801040b01010040600700307081c440f03000c03544061900034120042c4c003076949030355198a07001c130514542000001d4040020400350708081d4014580200355107a980c0a1b401000b40a07a80074540c0000d2011107004102440180003550162015a846117203920400055403412064580624180820300c48001d01d442c003905e003402d0f8000c2c20b0b40c1d140da07580d0000c03070f1404400d182a0307a45440b42c0100107100703140008c0228001c3c11014003e03c0021501600107420240d8510b410302c400ca01040019402882540000a02c45c00f0506640d11100300d04080c00075192884480c0b08243c00814645001c0c103001c01c544508c0d00300c10b123030960444d85103800140700c50100038080c045100c00028012107603241800181d00483c600c40b07805060980f5480000c118440034001c050181c3c4680349 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 930302077 1250 930300827 930300853
    0xf0a120c08010e030a140c07030305040e09120910121a15090105030a0903020a0b0a0e010c030513020405040203071d0403030f09120e0d080c0d080601181a0c0d030509 73
    0x300303d01800d03501c006524000000c0422038041900404064000c0782c10301110340c0200003400444020343c025514035032a141081c11442210801400c00000c1c2c2d481844c114100c0c1422000341e9803104011900c100004400110640740601907102c407152452a003000c403100c00078481010183e202007500c820a1009201740340d0850781c8100c0c003600340464030600008003010501d07044070002520a10548451884555407440c7d20350040d140c110b040c949070521040d40030760034803075000404100d16040c0180c0c06e0242c2c021500c0461200044c3c0107586410004081d034604010200052141101d01c0d61075404403d280b5107074100c141d8040380042d080110140031094180903881070280c2220212409810b159419a82500704145d0745800641c00001c0742c001c50340c01c0d0050011450244040c0c00381041d003000c020501017009020905105201500480c2c801502242c0c0e016155015900702110307900d1000e0f00d81c00d00804422500d20b02c90100c0714040e090b8941c02050080103d2000c80e03070248070242c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 930303327 1250 930302077 930302081
    0x100c030c170a021309020703030b1c08042c040302010606090504090b060904060f020c070e070813060203130f08090406140f09060414011e052202090f0a120c0801 71
    0x1000a01035981d00d0100341c0300040343e802011608a0020000000c1e80d13202002c0c0260b800c40344060300480d5541c1d40700c040500b8100d000311981b81000124607014001e940e11f000041c0140c0c0110301402d1100d282001501c03903d80c0c03210042d19160080b18081d0b20741483c0080c043c0000d800780c10002101c42e80300085900f46405501c10540d8001e4960505649400522214400060003900c540c1e841e4001e00b13071100c04078801400c0d159101409002d500e410403916000030800505261708000002c3c042040003103904052860581d03000401603074a45a0300c0a10100303400c0303114060b12a1988103003103020004100010311402205031010311003250789a4412220502003071800d50800000501c01900c0e14007007598a9010390014000500c1c3d42040c0e0f015141d90009802401808018641031150516280032200041c14221800d00700c1c0e49140c00e0b0b47c02c1103094410800181038003c544244036907950501004508405092012155a5400c0c4859240d00c060400d4658202204000c10001818 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 930304577 1250 930303327 930303347
    0x10c020d05030a020703140301120b0c030717090c1807120606050405040b181003020a1715250f03060906030c030206090109090f061a0705060f070908100c030c 70
    0x1c0d11082d0842d500c4882d544040c2d0701c080300440c00c110301003900900c0900241e024501a0200c0b000011485610b440e22184010020700307101c02e00b0b10b09000700000c0c55880300b00015900b019913040c030066114440d17018601030305041583e901004901c1d4190805611500d42171207012140d4841001d0398a0000303440440e9102d018000014104120900480c10244c06c03007070542c0009004202c541a503404940050401640d1040f031660081004100398034180f00104081c20303c91071708a44d13000007111880d03a01c142d444402040303030805030006101c0c4030250801445507103c0040f40c01604400071030050014181e03180d40c0002c00c0c0390540104450f8401c2c800c2c10140da40c440c403e4a40c2c01d00b1740c0c007000b48235000210b505040000f440c50205d079541490155004c0d60f10f581d14082045410301542c07008008144d510b10101120a108074408502c002917299000b182d200c1500b40a0f0700e6210044903460100d4002120a100b04c80306000700d80c03c03e0f03004240a0030141d0b002c000c50910342c8800c43c3d100c0781d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 930305827 1250 930304577 930304603
    0x7030e010e1206161b05030d2306090406020f0307080402091b0f030606041a07020a090e0a1202120a110c06030c0a14190518120a1506030b040c08010c02 67
    0x30030b00041d03611048000e01d0710744204c1420905512550b0408010440a04d140d04840540000c100707103818407014040d40d1030700104800d460700c1c0140300c00ca405244103c018039a80c445c5502101050520403940d0454605d40d410a03145944c030300c0d0a2602518201060350700302d004040080010781d5981d092004a50800c0d0744004451800d404034082e03905a400140450303620000400000640580420414248071624040c0903200c41c1d090040010800d207a40c8400141c41c2429a4001c602d18045001c1074516800b10600003030042161080345030644100d00c0700c030b8840e000a060400d8a401c1821171868071400c400b101d03045280541402240d01007030380c01c0390101c070003440509079003800740d8880c10400c5802032145040c108540d40140f84040e148811034082100001e442d11030101c0d092070b900c21084242c0d4600003002920400580c1e525030420040d0150b9a000c0e0f8060b032620741900190300940d0001c406203064201400d224108114500c280803c941ca82070340c0b40300d9180081502050040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 930307077 1250 930305827 930305833
    0x10030b090105240c1c120b1021060e01090207060e030f0301051c0b0f0f060a0302150a03180302061f0311010e031c0f09080313032607030e010e12 64
    0x1641c4840309203150041130000c85280622501c1007a44401030350742ca019402c3c2a580c1042021801d01c1d550116400c1c081c0c1c284c0201d401d1a000018103400c000d092100c0c1d42c0089080b55a003100090b00300082c00103401c0383e0100002e5000000382c02c20142c01030640070f402048200525100391000555034415010b038003034245004e000400142c46c208500329a072101101598104051960b5004114842142d5120440382a407044c8000c603082942c00ca40d000e8015a0400285801c6400062400310b051400d2202d8000001d0b0700c20743c0c6446600712403081030a075404600d241c081450041c1d22400d040321101380500d207000e40c12050036001c0c0070450032660480364140308001d10500465021210f01421074062040030300108aa8802c0a102c1c40300030040e03551a2050140400e00420003c400e80c0f140c80701c1d81c4180219140030880d0440701e012280d0080c5080c145003107003030043d0010f00e82e1408202c0e03800000b04080c028145c121503005042c20007640d130f60111b20054410413903d94100ea5a2030302c0b0f98 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 930308327 1250 930307077 930307129
    0x70f050906120f0115030624090b011b0f06051b03160507081602030606040e0c0f04060b0f03070806120a03080603030904091103060906190207030e10030b090105 71
    0x8246200b44400c0120444140c0700303807010551540e4291540c06890034895610307000100140b102c0c80c414051904030340101401c000d0012404147c80380f41902a0b10031503a51014189480e80c004d0b5050014a8841c1501c17180c440c2c054245001c6585c0c18a0f0141d80d80703410000000d00c45c1c086804100e04888a0914940c2035840b40c0f151502c84c200c29003020000e0000401202010518200c0602080300c10f40240d030319a80f80300e105150402d0400342ca1103000760304100c3c07400b500c00c00208002c00c401d0b40a84041c0d0000b800000013078080d011030340c800c848c40d44000800340070303001c5020300540c8180342a13240c01802e0786980b030a0120320040032400602c2d90304501b440740e0009120b501c5031500188000c044904145001d40002d0446a40c1c1302c1c01c880d540561a40b600307aa040030b11400d64007041c1c81d00540300382e182c0240e4905c2400500101910000e5000403048101401180c0014440304083c0940321020000343c000760003001080f80991003203c4500001419141928074060042003510680e4019 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 930309577 1250 930308327 930308329
    0x6010506040b1602060d0516020111220b030c0d20090603040611030106020d02060a0516080403030f021206190302101404150f0f020114160509040518070f050906 71
    0xb035003001c40514012114203d4500140e42c03604c1c0508403100840c01e0000d1281007440c44004c0c400400e0841809590400d481103840b040090160340404110300a84500804007a9240d4941656500800c603410301c088144002800d01c1c1c8040c00ca07032030316014108180e4029002040c504902c0703062a505940c0104203203910740c01c0039030145070014401d11010a9015a480c111642c0c1d800907000b0900590098100707500b03050341008410342010b1403440800c41800e0840c0305038a0602202100e405004204c408141014805d91095050100720501151101c801176114128a07405075951481803d161080310411203007a800c440c110307540107203a688403480b24101600d0030010035000c1c4142c804103000008003aa1300604000190403540d4440140381c002d0302015002c1c0a8213079074801160714010030130b990790115000481e000541c1c1d080c40f074403802e40e41c0d00c1119140306105503650410b051030213100c100350b030415400008406800940314155146c40b00c0b80303850701c90b911407036030701c610300340041519 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 930310827 1250 930309577 930309599
    0x307030f0b040603080a0216151116030c05131a01080901060f09020a110a03050d050c0c0d0e0901090b0303030103080702040912121109013f05180601050604 69
    0x4001040280403407452080000142102c810b0750064a03103881c005005a412076050121040b0341e031360300790200680c41c10182001d6440c2c0050f510300b4148030550050b1480080f08101d81e403242c1c95038140620116440b8a05041140c0c0c50f88500c1e402503d0113100f000c4000224021611142907880a00021096410044503807503000f0b054810555078074180490112034241c0f500014101215002d030b99014170310001440e041c034032078040d03050ba08400704a20020354400c044480b149030003100440c1d07985608115074601d1041007291403003071003803c0c0c044412070b400046801254100b194100c010baa0b841e40100241c4080ea81d01c964181c10800c01403000558210140000c1800548002418880740d0349121086800304200c60218040203c054401d0304540129961a84800d034004c2c24901440c0010700a00c440a070407480500100392001000b102d030144041d400c014030598042d0340c19894245000900c400d440e00c42c204403400c0001ca129610001d1300754100c0d4405881ca6103031602d84040c02c80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 930312077 1250 930310827 930310841
    0x30e0a0201081503120310050d0b040b060415080c01080c040807031707141b061c1a09130302060f0106050a05030403090e0a060e0907050a14040b060705070f1208030703 74
    0x803e501000754220064404109403040100320191403582d03414062000c07850200c1c2c952140e4801c0d016002c1c2e090000d01d203503030307900d820036030292564001e40c403540c00040c05070003a5441044100c00600b40003800010005520309050000e032a590450384600c100c2040d58441c07401001c20650003d50b0810000d000e80b00d088a403444141c044504180503942c0e588916048041a03080c00d41c480f4915605503072601680b500c01800440300340d4600030401003101000540201c5101129507542400c1c100713040c0200c040c2010400080040c1c81516246600e07880090540030140c006203d52000a6202e0750303800440b9050300d829482d420f05020194500f100c0e5a407000f0012010007030300c4500041d900d404e03041d684c1d000b120041404251075050081540e16244020715100059101400800c1952105542041a114588052601e8440034004100602800200c0070b4215100146000c140500800c140080d5a03c112090b902180d039402d100d0305441c118403020385002010408208120300030f0380b02803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 930313327 1250 930312077 930312091
    0x91101110c030d0e090109061d040f0f060c090509011d07050d0507090302181501050c011104030c150c05100b0d0212060a0b060a0c0615050a0b070302070501030e0a020108 75
    0x5082000c805000c03d0800d1808140300c0d01140300d40368004d500d4680a00303402d000d810650010001c0c1c0e480e08601c05501202803c2c50070400100c00003007011711a541084141040d049030712904a5080741c074003400204440c00c4a5400143c4405000c500c1c0d00d011243c8504840001c08260701800b04903004150000d000340c110b4083c0b04042180e0305105180b8000d0134030611481d100c864001d4514018403508900b00c0c40c1000d14040c2010800107a1072034130245042c1d10000f0708e00580c5600d09440060b0043c008160764907480391000c81c0010405c0701503080b1605954240c6144042c204400a068610a41066009101d60000000b00c1805900e030b600c00482d2910081c410f941264032500440c0034860081400d100070307000601000107a071030a00501c44803c400b559158030300000d1440c01002800312860003002c903900d81c004840c01c2c0d101800c242010317100041c1540c180542e26801500183c0c014001140503000b00030000815601038414505c07400340720805400c1340801c1c4e900445103640000c02c03078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 930314577 1250 930313327 930313333
    0x20a09050a3618060209040f0221070203040f080109060b010503312001020c03070602190503040b03011806080118121e030902180606120c0f0f07110409110111 70
    0x54000d220710210101032240541c1c070061b6540744000038042582c0900407003d0981d80104801d20104007282d403981c0307101804001060f4147c4a12004034298815940180c2c036a900000e8086203114040d4003811006100c2d842c100414410380c3c00654080c0421144403201030320103d012a41c602c0d804807074942020600c1102c0300c04140503561510541c15111005120450110300b400941d40c041240c074a500108800403d40903182c0000295503121001455900040c02c2c0341c0001004400c0003628081c00242490303030380782d6031558480700140f501412160f2010382042000580d9400610a1a05d02d0500103805404004a0307102d15080a003001030510400c40812201848450201d0701c410790310301e244c0d074041145038041c0108940da071560400c0000f41c100000034070031a03a44003003c031201e140d40c100354039100703566841100f411401003484001c900200058842c0c4540030810040545600c1100e00d114030000303090921040340e8044000400e2098002e81842c2d0940c028080361026103520b40803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 930315827 1250 930314577 930314591
    0x60e0f070e0d06020408060f041109010e13110d03020c011218020d0809031006051201060503060f09120301080601030c0b0c0c01050f040b070602031e0412030504080d020a09050a36 79
    0x6c050b01d000c600b1143d8050740c444140600c001c1044503a0032046690045030301d08007035410020114a0540c010340551600c3c5d140e10003a80c10404000c058055010008002c1400c0e1182070601a49480740c02e00c0034dd00162000300c0c04944440c00380700e1034103c40e082070858020080281d081c030081c020301e16000e03a0706030340c00d0095480340d5070708001c2c00381075451845004c60314a140605001220b0912640c6a0031030b4180308040c021074400103a60b907806074101d00d005100c0d480d04102d460420b4031500308803100040000001c00c64040004845040300c1c80b82d550281c80c0c0ba40c41e401d42c00c1d2405500c0d04908590450190303d0029842407000d0704811030300344d0312a0318060b03807500303942c4e250391006d201142c0f1280c0100c01c1012000815a06045503400031820748c07580d2515546440b4551081c00c001018141e031000840c0a208140054543e0700420300421980c030b0740220405024a03203148101c80c460b05c240d400201c2e401c0d215850504000c0b030340300649000d40a038034414403a003c180c0703054664400c1e61180 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 930317077 1250 930315827 930315839
    0x3090312061e010e0d060c0e030c040606020604020603130803090309091506191103040815070201180b13440d0e0a080412060b010e090f180f01060e0f070e0d060204 72
    0x100c7c0040f104110348848d4900640c07c0d040c1410411500802c512451070004100592500421881d900c994102e03a601d540b44d03550003201060542403600030302440c00120400c81480d0001004010075101210014400c0d0b450141080310801da80b0001e07604a1024401c019090b107420f203203aa000d41c0380c1c0c241003c2c14251b851038940395402035444904680e02c140003a1440e000c5803190075401503140e1000388000c2c1d80d10782139490610b8180d00010800c54000c0d001451104180107490300299201d6801241c01000c001d09602100d40c0c0050551303204d050040f86094018540c6030b0407141c0c11003e003414148500300c0701c2072004002e04602a107840c020030401d680007445200c0240f018100701d00c1d0f0f070b00c0d0702c4c0a00e050402c11620140c1c0b1441c1841038050f40740d019a030b206a0083c0c1d001c203413550022020b80c1c7d0900703000c010413014203544510f48910416000c5600041d0000070903030309400080e030321981d110f800d607500d4648243d805202080c902c01042d1445e060100e5513070001400740c000503140c00c2c0c0da58 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 930318327 1250 930317077 930317081
    0x301030b25050f1804180b152d1e0f030604030f1b0206070303060305120a0207120312060f150512040327180c0c053003090312061e010e0d06 62
    0xf803409412030714009001b02080070261505402520a1494042031102c500104944412510040c0c036100c01845a0381c8d02c0c82c0e038401e00c1c22442013000d0007007220025a401c0d040808444008001d206804c0f40000300b0759400c0c005045071085405a549565030f0081c00c0081e04c10070b40c024040070218906110200140e1903400080007024803039907000072198503500380f081c18070460469940b00100200040384200f43e00103102c0c2c00f0340340e00d81d4480080743d4951405980e440c0c00c1c070f6084400e09080080000b26501d603850943c0840f000c03446800c4207080c00d2401150341d032192880304035002d0885808540031a100741010300300c2102032140c18086c1d44203810480e0b2510813a0b40216403d00c40c80190070402d4032540038540700f0103051304001c401c02482e40d540d962101031000b040041701c0d004000440c422203e03902c04100094011030700c17966034103005c84410303126070102000d5108900d0800202d421800c120b0310078405401540b50f00032441441100448410303008581c100d031303c403403443c24035030106402d8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 930319577 1250 930318327 930318341
    0x4021e071514010e1b09100903110607020a030f052b09050a030803070311040b0a03020712050306060403060f0b0a091b020105100b0c010e030301030b25050f1804 71
    0x140c039400c03403103401d2044104180c41d0314244030800011040010044a940092550b400240710300c0e03d80e101c250095030100c4d65001c0c49540580c80704034880d001c29002e0304580c03c1d10687e80558411004200d80e0014001c1c140f04d006c01c003e4100303076514400c0000c01c8041045110140c4941c0c252041c1a00c4840c94000c00c7c80300703000050803900452003000c2196004000000101000d0b01c4558040d480d68a4042d00c0d40001000d0800380354440e52900400c47c80e010448000d0803414426540700d90109070020025042140100c03040034215031031181450282080d40c0c41005c0041c00907280c40d065565803005041d680480d000c0950f115604040d00313680b0040d00302c0c0038003c0ba420000701e199424030b00c203c000c5481407540c1c0959140105004070f648016600c1003e45000301da000b56210483c616042c01401150b00a40783c3e0701000c000402003210200c54035000c1c0e4a0f003e066003824501805181c25080010310240c00303e03000b00b000b0001c0d0060706000d00100c40c48040340f0f002da0450240420255046 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 930320827 1250 930319577 930319583
    0xc1006061107050a05060901080a0b09090a0b060a0f0b0a0c0c151d1c02030c09070f0f02010c05040e060d0b0c0903010f2003041b0e0406111804021e07 66
    0x120208031401c16404200c0c0c40020003044039010480e0740750401041709441160460b0307041101841c0055a28810b54000b04c42e800350140c8603070514a400a203054070f51031469001c0341c81c0d003c200046a00c0d0b14103904510140d03040c104c1c034424124642030b2031b84220f610406901088c025034841e0070000c80c44a41d5200c00518a00440c48140b80800c40e0080c40340101100414a02010b00d02e0044a62108409074004140c00c0000c04503120050000a2a0079130002c48250320000d40400c02400c3c1c2d40c08102c0c003c0c00c0300d00f92104868072030000410381c01da0701c20480c3c140010710b05020412042c1c20b035104040e045000507080c02c0c50307151142c442e071400b414102d6182c4590400051441c0c12030509204004815003030360b100304030705080e18190804031505640400e51410b0080b001ca01030090300701408900000303507000c2501c01c07551003500c059602000c07603040c1e4818ac0b4100380721402001020840d15159400950040d0f2007160400f004000d41040c1c140e80c0b4100000c0001029002008004000080c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 930322077 1250 930320827 930320837
    0x70b18071e05013b090c39030c03220305060a0f1b090f0b1804020309030c1009030e010908030a032412140f060c09030309040501031101030e070b040b0c100606 70
    0x41348144481003001406902c9802010425519121090641030110140200b401041100c4664502105103814990314995020000e010b11745850300000804014031001030000c50405505020600c0c400a880003401c00c1c0c1003100041c555452a078007600d2414205a0001030ba10484101c0d0364500b008213503143c01140c9442020f100e5035212484000051000402503481d110300921303200c080d0030072103038003901694011020800c1e901090050f200e60740318041c211842160803c4448001d00034109094000c01c007907007008801544138017041d330b00380c40503040118a000c3c10703424120010481c1c0725158000c07030b0b0350000c02004c4003054400b0000429000c504202c000038142000b4502c04d01c0c2c814864107941c00201e40c0b401d894404504030340c0c01101541c4c0d2544407028000403c1c21881074012841c2c3c8185000008020004c42c1da00d0300c50385800c2a40d0400c000c1c1d41c9480ba0903581d40382c90050002400382400104042e02909006051103800b040c00c1d601da1140d030540d010107581d644e80040300494 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 930323327 1250 930322077 930322187
    0x10906080f1005100e07120f020307300e060708090307081b07090509070e01210209040c03060f0e0d0c2001020102120a02091003020f0f070503070b18071e0501 70
    0x1f52942c001d480c005016040c046146082086c2c014144454800b4054510440345030442c2050003550030b84409440b03581e400b80070030000143c9298a54a0803107000b00400e558a02148034140b000040d6480341e07a00003030b19440c05020072000ca45511010005400e00c1c482c0c0080071030304880500034a40a00307107007001800d0341420607166070303480b0704160007680c1c40c440c50100c002000c0d07c1481160880303d030192204103068866003001c0d00300e2520350300040d04503418400211141042a401041c11108000c15030703d0b01d0ba4204000c4038002481c4101134040803045401c000300c0307592040000f0458005000051034042c100d03020380e54400c030884904440b10742c00726108040e0705102104c0d070401111743c5000c6141000303c005d090050701407440c90030412034011a039081000350070170444001517040313254928103280c20000030351759180c900d41140b10b84c094040700003150a51340000c100f5071003403080c01c00142814000111132221101004045000d2040f180c0381038000a804920000f95607044009030744 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 930324577 1250 930323327 930323357
    0x1050d0b130609050d032403080c030f040e04030e1914011b0b041703070203121e09100f060308070209070309121710120f062003010906080f1005100e07 67
    0x1f0b03468081b110022140c00300803050000b1000c424201640c1d07020101d2601d44154a1843d4514091000c04524240e400a400b080541785044000c0c41039219a031035a081910400c03e2180c05c070060030300090301c0003c00394144024000f0403542c4100340010314080c413058034080c3c001c0b413100189140981c0e40c0283c010511043c0945540c44046141031054514a14109000001d540344104410504c00c3c0c0d0549c0701041d0320540714450075440c00030110011306030381801a50700e0b48809488004240c0d0600e000036051003002c1c030340103030b10031242c010052504084e900e40a00c204c0b048018005410140c0d104020000203800c40525000100603598004540e00c91151418002d140a0b04215078048105401c0100c00700206000c5141d40e0700c46a19081640c1624040d00584071710024401d5410101956000f00610710020b07504840c0698000d01243d50b441200a440d20051900b000c00e5401095903214100030a800194101c2c0c1189810321883c0e5a60300c8040041c9400c1d1070f010000350f20444008a4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 930325827 1250 930324577 930324581
    0xb150d060311061c09020f04050106120509160b0717070507090b09060a030f02120303072a12050f0405060409020711041103070f050c01050a0b1801050d0b130609050d03 74
    0x1400700c00c0da030891078a40c00c0480c9000c598106502100490344415403d8110f4580b074034600c100180261060015584649000d4001c0300c0103004cc030025441c160004106500004001c50f080365075410307100f1900e0034900a10743c681d00040c2c0039103111520380342e05122403119000400791036000d071016008807410941407100307480c0080308140c0305401030001d00c11907a984480322001c5950000703001d2740c001d000d0301c0412101c0010f00c000b4500b901000c8100100e81d81c110004a24a5000768991401030444d02413000c0d0103040a98081c1800c280002000c1509010300020541101c4800000703042036940c0000845580c810707001043c015402040d100200011124440911802180c0c00c5c40140b080b58080e03402ca000042c00746c4100980012a0b40c15580941e045500380080f40c4000c1c0214035040003000040c02d504038100d03004101440b0050000660204054141e0b40020240349500b030190700c41c200c0741d200141002680303586055a0500156042c401c82070101e00c61005050050003a00010701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 930327077 1250 930325827 930325853
    0xd1703010503210f071e0524160c08040305030403050a230604020f0a0f08030301150f0e010e0604051815180f07030603080406050408120f0d0b150d0603 67
    0x7000e03801101d502c128100580041d84c8245202100c01a100c91507070602082c11751580303d1501c0c070001e02051040c00e00a001c5045403005054202d002d810900b4448101c118043c201d5000700c200798080c2101130030030300c5144c04281403030084107400c1c242526502d8443c01e50340705038411039042d03000420741c0080220201c0110700702001d003026060305026104140f92034010040000380f1030340410184040d580d450071020005442c9050b44044901c0d105c45055030769a0085c00b0b01080c00c1c3d09840d000b1500c40c4074240c4010800d4440d9980c98003030b4003d500540d940d590000d40c41c0c0c1d00803002c1c8004206919141a285040081120406058100007001f080c654100c003583d24050740c40c450310000500b450310b044540103403141018031403035511103100300c0c01040c4541000700542000280050f4082e40a4042c00664004806540d882030030b66110240a10074403402100204050115000024696000c4616404068250142d4680c0746114080582c00030100c1002d030307503070350106109010443d21410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 930328327 1250 930327077 930327103
    0x708071a040501050a0e130905010f1a01090e062b2604060e060c010203190606090f050402030907241403150603130203030a03050a0e150c090d1703010503 68
    0x2407a150405000900a00c90b91000c00f0900c00c0500c8640040c0c5c0790002d541120f00700c1140100000d00f840d10301607002c0c2c0f04a240c001400ea0800780c2858118582000d04410080143c4030402d0a510340810802e0a400c0200b032603500c0103240d560307510400040411600c41c413595502041940c005880c20f000c0e000490419003100c0d40603034403403951406c417070021102980e400b030404148490700c42c40010214415000b040f129540080305100e190780344a1140e9612000c16041880300589440080302c1d01c0401d031003000340d4000700c242c08001d01cac1003d42c010341d04402c4500c1030346c03043c0c0d480c1c0010030083c0d4400421400c00c1181c96040d169035550060110f00704802c030340400d51850400c0c40714000c5403400c030341c0024402c0b10000080f843c401d1803104039100303a50780039094944ae1060307000c02500401040301c0450300f450074004d01002031500451050301d1310690040c10001600c074070308488082e070081000d4a42140001030440e001c6050030800c1c0c421b01082c03011542c1e407507061078103060900d980000c4503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 930329577 1250 930328327 930328379
    0xc02090a091b0605030a0e012a1103210403020109051e10060503030f090a0f030b16020d081909020a121416231801030b090a031707020c03070807 64
    0x1840301940c000105e80d08454400c4020400109408001f0300500700710103052800b4400744070f036544000140d031007001c0481d00c603180c04020a40c3c0701c21042d104c0c841c1d145038030042e501252150300d500c01300780c40581e005406440009503c1c2d55075510589032a680c040f1446c00a0223404042d074510204104d2005a008051011700c00d451a00303002c01d0b40c034054100c0b84c280c1900c0110300065192a1600064010270303a001c1e420030710a030b50b0b05040f901e09006850780d0308403844180c10f0642050000980e44c9025541741c0e114202544e0b40150704424122a9076085034117622032000c80003594030390002e00c014003034240c118660400f01e40352201c04c03030040210700100d9401901000c8018404da50355a401c8403206205807450f00c034481c210700140030943c052540c2c4920f00d1204000060300020440b416284514241001e58590080c1141e6a0600000c010001040598008045904414030b580c2020b42c0340115002034441d480043c1c02c0c55404d8108680075403106804002203400c0030501e000155212980d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 930330827 1250 930329577 930329579
    0x1050c06060d03170106110d03060506031306020c0a0b0901060609050306180705090901150501091406071401020309060405070f03030f0e22240e0f070c02090a091b 72
    0x1100d4640d60000c104520984004490b03006150140c0881d580400b412001c014881d1785030364020703104284c2e0944e506030a1080d03100f14214035029128460545000502e13142c115501c110007183d814500c06000c440550f02405040d101c0d0104100000e0858403444810030740e40340041a150860b095a0322050030454041c0d0100000c0e1400b058a81d00400d4020249136001c10b4410045e1800c1003c0d44156004103001301006006403065105100c1d0655507c0b2000020350749400454190b002c42c0209008030980d14419212071824400a003c154171540c28000b403100014040c60032a04215001080b540042c2c04020401500303201540141c004245a100a00d085032002000940460401d40c10300000c08070803440d642e05c45114064403d0416110103401a480101c1c0000d800b4403881420070b2001c880c43e02901101d901c00b150b080c0e4248104803141340d5580c9010025688000c0c1c1204180419041400b0140e1a00855140b0458602c0e0f008150030b052480c00b2000758440c00135000c100301c00c40e00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 930332077 1250 930330827 930330847
    0x130c05030103120903050d11060a0507050d09020a1208072915120a1b09060312050708040906030602040e0703090c260a1506080a081617030901050a0b0105 68
    0xe881c192500050300d1800c81e40c5020b0f00740c9100700d035904042c01d580308290706501c5c020303805000c0049040d0361800761140b64a07180380030f4094840c01c4e10560007007130307003030000100c0303c03882d81e0103508020300003030115048594522401042c407500580c20386403040006502003d00001001201002503400441c03030300c0d02c1101d001c41d01400006000c845052162400f41c104c0c03070342c0d0340a07114614004881a1140c000081c9411100810002625230350f03014007000c0040e83c45c0c024440d60040b603820415814084a044004880b00d5001c9e06044a0055003480007144500071849400007840c8103803c01a0786505201d4030a068100040c13120080504188420001071015400301d803c0b41c3d000f540e400c3c2e000d0906a910b64440c411640e0086051142e102c040050102c1480030308001ca19078001004500d8035427212a84510001c0400350445004103d03070b5080c420b04840c1c3c0d8000500170603032041c0b001d145640c0903100d03a0042d2181e03c1160344031018045505500e11407420750460900b456031602c440344c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 930333327 1250 930332077 930332087
    0xb0603040b0609060a0b03090c0a06020f0a060908040b0408070807052d01030b04090f020a060e0303070b09010b100804020f0f0a0902031b030708010e1b0409020313080a020c130c 78
    0x40c500350040390903c01150581c1c80f100722030340107094212100754580c907000440e542d4411410100510401344008000350300b0740081170410000710060701400744081207850710030140220306c4049806e4070b000c103c0041c0074800348000d003000d06030880c007900000c0d103820603981c54480c0c1c0e0f4118a01c5240d40c0081003010b08034100b01c90f4440d039804c6849070508601a00180c0003000d050386030a40050409802800b00300b050b07041905014400c0b03501090f000d4503481c6c11514540588501505a40304000c0708001c103918100c038550214244001042010721000446c90b286444103082010400420034882145044100c004004900b1b0710200c4406000f00e0010b903003401144280700c8030a41c00404120500a041510982900380e4046942da0381401000103007450407d11a0070150741508000c100c00ba90000382140700a041c074410107040605200d41c0e04000e42c0058200f24880074842c0c243d9001070341c4070001e0a000000354014044052040b4103201900050f01907039009a40f401c00030702c14068110b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 930334577 1250 930333327 930333331
    0xf0e070315060c05151e012c100f061d09060f04020f0d150302010206010806070503180312010b22050a03030c03050705030d0c1202030402180a06180b040b0603040b 72
    0x10319114643e84402c0c02c00c5804e00030078407600040900710004000455000d41e11304411020700481c0140540ea940e1140c0714090412105003c08544c42a101e840c0c10707605420280d040304c4031829842c00c6c0303980c841840100550740d80c001c8010502c01c2070842501c294080d604910014103603001c14251800c0000900003c4221106920540c0e01282011146a5910903281c14001c50300d020083d0120b03240500019040381d1001701d0041c41440004100c42d01c011070101d001e40d07065201d03103003981c41c0d80d8203200300d040001c80d640700c0301d20090010b030301c7d181c500004081c0200343c0004038999400b240d465504050003021b05283c41d4003100780702044561961440801141e40524103014180303844c0c80c08441c0f40c891200090100d1002080900c041142688500000c60094490504200d8450840e000741d00040700c010b0343c0302501405d03100074070000c4034206500c4002e40f00f000981c0b60300c031000080c24504035420001843d80d154401318282c1000c1c41480b0604408440a500b50b26065560024402c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 930335827 1250 930334577 930334589
    0x9010c12090201080f180f030403060516120504021f121d1f110f0405040501050f060703080601022508160e0c0903030d020304030203030f01091803030b0604030c0f0e070315 76
    0x452001580c0b003840e0034180106801c0c50811f0310000c8070180c070800c2d078a42142c04251041450310340841c00c0e9140104a01c00d101c856501e90303803d000141c031a820020600107000381c1e002844038507407518000c4840344040448000f0f446002e503840c2400d44120486216040c0914101c088003080030741028002040c40007100c1d42d68002e074911402e01e51010103001e101d006040c840360081080e5500c445c8a0001d04142c41094030304111503039a401c00c01001078080c4a400e03030088010010a00840d00c0f40c010388d903000d501130040310350410303034200b0000c01e40341c440d21040441ca20702c07042030058403c140000b0076168041e000d05c9614509082c0800300c1090050100460740030000381300310481d2818810340f8440c280890b0119128034150401a41300c0c0c6c07040782d445485e010400700100b0800744511441400c07030580041e540340702c0c150742e03002c0d4010f00c21440002c2e8401c0e401d10000000554044210703001e0003c00401c00c2c031107841c04003118843d03000a4100ca0905051445500b0403000741700400007120340b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 930337077 1250 930335827 930335851
    0x901110d0f090b1306050c041d0702010b060f0c07090e0304060f0c21080603010e030a140705240c18090402190e070e010509100305040212010509010c1209020108 71
    0x31600307114401403080140080004944004029100805440c01c80c40c07603000b041c00b4421a0f860b02c032440c40b036206902640d1100807680c512070b80c055070480c800550141603030000240e107689400000740940c010aa500917811800241c25001c000c0c107100150043c0100c0d070061090002a105103522400ba50152070100028801051816441540c80440450f007003005007002803018403071000800c042c04901c81c042000f16010032401d041c144160f03c81c8400d0a4083c41c148034440604580d1762840c2c0c0788000e003580c42130241074081841480a48049056007032049070304d04841034103900b00e680003840c0a006040901ca503000c50b6070036411103048080308540890b05a920340c0700041c0030b4a04601c0c0100c24420820b004030750a4105068940269110380b980d20000300903000460390340c4206503c1315041890140300c6202c8501a80080e5002407000f40145d5001442004050131a00226550340003603440302d002541c000d81140580c442e15002080920050010750006003030b08202406100b0000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 930338327 1250 930337077 930337091
    0x11010903090b0c340501091d2d0a05010e0f01180608030d0912050f07020f1302190912050c04051806090304060e0405060d032f0c040e071a0702060f0a080901050901110d 74
    0x14019014040c015001503c1300c0c40750114084034040c0e00d27a821075500701c5007880e10340041030003020030341e0481c0706a40c203131842442c50f800c0100302c009101d0b82e00300059940740c98403c0450010018800742508102d0103100040c60412420050000740c075117141c0c0c50501c0030800c0207558504004044802a035010345100c0d80c509140c0f0003041019520302d0040341d40c00d02c0850b080300d0202a81c5004244081c5030b50350140e1003603c2d4000030340741d805c1d00c1800812603440310080101c0e41c2004d03084140c0c407000c0020703604c0c48980f60440301400e1080c2120f501580e500001014070090b9040301201140101c1a5020407480c60311301c0110340384107001b02d409828030a90341c451121345607003000540c82d0030700a070048480905000d24295a500b24114150b4481e5040001c2584c0840c8002018811035480000b130111141012204100d0307075005103230681e0440c1c000c000d0500c6120203100203060b000056659002c0600d442030810342100c1000c3c0100c0816410310801d16458a0900162241c920803401d0000741c2c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 930339577 1250 930338327 930338341
    0x70c0605070c02060c1b09160806063702070b0403060510080d030b04050f07231e0c0d021f0f06090c0203090111010903090b0c340501091d 61
    0xd02c1c01c000d0001e5000700d000640c80100000401c11801c82e550f40c1c074500422030146000c020405000722800700c0300e808103101d03034004148212a8250006005402c040c0341503083d00c03105c6000c401c0306a5211001c64284140c007043c0c42c4903850038040000c1d6101501aa5060801e07060442c480c174070001e080c042d183d202084821a4040780400100802d1b0111941000d940101a0181c000c00c0041e034481e514140000d800210608225440790700c2c503540c3c404140c10401d031440003158900b20380c0581c0010074420304003480e81c805043c140c0906400d120a8848040103101480d1040d455800d600b190480020400381c44040100300300c810b400f1880c00305175070701202c070000018806944218080c6003404d07854200260088014510aa400c1e40c40c9040f80d841c18245a090f5090158003c0000e13141240421034203100d0000b610f10024150150f40651408407906414400701c074915a80103800c0c181b8041108608442d00c1c13004181c01c0c01c00d121000d1078a0715456940c00e105580b8402c9182d400000b5040d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 930340827 1250 930339577 930339587
    0x1515061c0f0b121507020f06090c0907031b0f0e0d15060506030910020708041706061f0912020d05030a0503090d080103020f01030c1112071a070c060507 67
    0x240d00003441846420309800c920540250500020038181d0914000c1e0205190501c0e400b0a2003c3d820300c0001d00fa00d0306100244070030054014a5003085000d640311140c0c04200500445020310380703d1006140c1c490030f0078204128128003400c03031824941b92422500600d24580350342203403c5000d0030201d00324000c03000159118100d05000c598015904c003100010002c00c02c5000d00c0442644201304003084d00d86051005511042c0d600c02202c5e40021201c00d0700c8102d0f60010482148220300d028101581da003e41880c1081007807400c019500842c040040c0c82c14101c0644410038010800803484034942400a4880307096805218003003104c40484e0390654664405000c042a030000c101ca903640500c0d54000c00c0b0303800503280410503004800d0041040c51150840a0680e1340040c5265020000c0c10700550080040c11852403d2000b407030030100001800388041c007200c40f01c00c40e980343d84076a207181060800003c091000307804940d0a0a00a00c15031040d14488001ea0244002079a5282c0300700a440f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 930342077 1250 930340827 930340837
    0x1804110301092406030b0415060906032102030310060c061b02030a030b0609090604020304140f03071b030b0609190203070915020604031209030516050a14151506 71
    0x18266080c01d100300100040000e9101002c01020980c818482c07031280d86900b500e540d40310283c1504038041c04240803038110319440110808052002030a41c0d40c0301100342c10b8460035481610400c5071817030b00d04dc202010900c00c8021110a10146185140c40302115840c140c1c0c0780140410000000360718401c1000d982d2024404101122145c00c18281c0018025601d50001021000003410404803c1080c284201a11800c2c60000c008019a940f801e00340f1000350001841655030030300042c00048150801d100d201c140303500b480080c0d0b5882c0740c0d5090012148204800300650f46900075401c10200300140300c91501315800302c8000030f16440d01910bc084100c121040d1482441c0300000388034016810140b22002ca405052507600841c0a40070141c2c4c85074000c80b005030120b0b5202c1c5a501718002607038072501e00e840c460b040640c201103007028098511440c400045483e68050700c0d19406001140e10002d160141e80340040c4603c08481000c80b80180016014401d0040d030641881400d82e00c18007030f51 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 930343327 1250 930342077 930342079
    0x63c0f040204120519050d0f0e0d0305030618130201052d04050a090e0a120507051203040615080d030b2106180109051f0225030e010c02180411 63
    0x5902c40d900d400d000a84800740708002c4940b1300c01d420703191490500030384a980d4400c6c0c2010140c00a001d0220064418040980d4000108901920381c0d03502c84e40c44021090220b40031761340d2603480c5d1820106221b00946200102402e51407030400700550140a0110b58410603030a20f0810340b9500c42d000400c82003030440c00c080074003130043c141d40c54004011501500898400701e030420012a17903203005d8811104a0750901009401581064001ca441d202c465040600145001407501890784c54042c1820b06c845800380386580300100348424003c15024211309914041d9855103207500d420240350b81c9120300d0407100141526060542c01541d10840901d00000c0b000d48550b1040004200300c80d1110300444115100580006614100c0201445030103003c0d6480b90007024180f40c0d118461161407498043e52030010340801c10f891602d21042211124a80a00d01ca01c2c0241040e180c040c00180106455034100184d00c86100d02507903414086d500345182c1c69060222640301d5051107540401485442 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 930344577 1250 930343327 930343331
    0x12052a09010315050f06030c12100c0c110105030105060301090504020402040306020c0d0215060a0e0912160308070314041202070806090a02120a03080420030a0b063c0f04 75
    0x10300c008050803c12109865000304440da4070381072410a15101507403443e0301035000500d4a03102e81410340e020140b14000c28200c0d0f400701c0c50254004180e40400c0c01200c0000c1d00d2401c210b040091a0300007001490090134041e06640c100008121a40014403d10303003c252204085800c1d501c0c3e5a0448004d9604190155031361075458405503a108403a016880040c868060011089500401020701130301008017109003842c076015009441040c007030004101c0b1b0181282c1c1c607e0039000301004050321400c55070310a6510301c09040140880320001c25400605003401c14400c005c141e050078055000c1c1c0d10440002c901600d080e000c82c600962500044210b2081e4801d1040740080066022005403080b01c1c084210380ba00f1303102649440c070001c0d009000c00c01d86004900041e0040c003c81205042d01d40f0024447c0c031000d00000c2c0f40102c115815150466610280007160415415605581d404072008003800c45100740030010300c140d480b4103641c901ca034580d1140500d40c0c4064511074000e000902c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 930345827 1250 930344577 930344579
    0x30a0810090c03021c0c050a030b040f0c0801031502040807181b09050316080a0201110a0b0c0703090806070e063006010306050d050c01080c0d091b12052a0901 70
    0xb900940c00354003241703080855030041e0b07400302c0b485010710540c80ca04c560b1506e080800d02c05054000e082021481c0c0d5000f40c907910344640d07803245449044504030f143e07510620030394554201045081346213051003a4035030040105002c58000061188121981780518a07511480008100002d2001040c8200110303100030000d400c0c1c0390310001c3c0d04141d130740c110256411000c100a0445481410b0300c581c560a40041d9140c80240d07019240c100c58040d030071400e46208601325074038600700c2101240c5601c03034802c0c003054640c03d065100544502821080b8000c0001d811702e404068094110720b5038151043c0000a91001030558041020709201d00032003030b00108a00300394085010842c00c4440a001a14108001407240b42c1082250310103600b01001c0e01d00c00e0b10000044908c010f0060101c00039140420001d404441a4815000d6083c000e00d51895560403168510899a44590008110300718080248002ca400400c41408401e0386401101d559a40203101b00b6a900800942c5030744500c0c0600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 930347077 1250 930345827 930345851
    0x80d0f06030c05030a0c090207050309030717280f11030f010605040f05010b071e24200a03320403022107110d08030108010b01140a02030a081009 64
    0xe0800c0e00e1080c400000d4040e1540c0905548112060b8050b0281704010342c10030515401b5070050540b41d01500540c1e181c00c0041c0c012038507280c00b5a22506200050380808981810140030000c1c1c007002c000020501d44041403200e01c1c000f81c0710900608030010010011042120040084002d40c0014060352404400141c2160091403140f003502d024a040c00078640c40590507104a50680b6140382d02c8909295584e128000300300c0a600c90303403400010403460003011408604c0a42d582d07038015a134501c070103499030310020b050f9502c4000403070805c90080381110b481c0700080156565505075160001c1c1d01c0c2860000802c24600c00901002901008150440c1301c1342240c030442c0c4614004e40131961004801400403081941d030b201400d5a0760020310516000520041041040100040200e403401009841c0c400084d402a405101d85079900c250ba0b03182540c000c2c18400601d0001c0301c2c05810240f888001030340724480c5003005810000c0744400203011385000001070001c0c040000c010402a50702c40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 930348327 1250 930347077 930347081
    0x71101110409060b0901050715020708030f180114220206030a02070308010605090109060f17090309130e06011505070c23030328090803031006030b03030a0f0804080d0f 74
    0x1c01000c6840c2d04001c408203c031160501104d40483d1706035140c510f403c405494088801d002400a645626002c200281c00300700000081d41c0075243c0c0c0d00c03800e1014102030008500e0440100300310010790f4144440d4890740c03000c103120b103a8407609644480020f442041d0400c04201d00080001394403803004800d10000c0b1507103901812145201c1d8032402d210766280d40c801e487d14007820543d1b03030001c1c40400d011700c00b02e40314042010410609060095000c044c00c0c0c1245d18016045401001c1c540c404120307447d651030302c0b080c2c42411881801082004510312001140c455105000d001c0b8406210070886035603c0c4118125007215030050410001503468034861104655921400f401014282c42d07404c1440c5004000c8034510320150010512181081c0381030152101d9a00c590400c2c0075565000140410040c40154424444040003840b203508041000d400c54410050650080c0e0041c0200082c15401626080740d5030300038104480155140d2501020302c0c440ca6040c485024144060040c01002035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 930349577 1250 930348327 930348329
    0xb03010b10260903190207030c051318050109031d090103110303092718100b0303091e03010518060f06130e060f0601020d0e13020d0c0206150a0501080604050711011104 74
    0x105940702817140c00404a03600c00c01e80c00003902c003854214040015140141104c15090070841010a0010b41000910045249544142d0f210394490304601c0405a106180e03207000380d00d1656034402c00c501003000c036005030340500004041c1e0340d0821024890f9a0304101342c0362440380050203280862070240d440e0b4051102d1b196025038525400c4045a407040a94610b074201c1c003142001003418003090040180500004d41d01c55070140810800b44c8419203500d07420120017444032540304038a691507001d050071110000e056020002d02c000c48049107241c0400d1840e0000d001c4201c8410a03110400003621500c41d600b49075800e9490b001c0c000c03860170400701d10207100e900e421144500c5961164016629a8081900300c0001041030303040b90114586565064950190000010b040140301c64000c421207500d81c8a14015078810010800c00320030fa00c1070392040300025078008414031b20f05400a000f220000d011544220f482e80001410240300d10324901401e0411002488141084454146a5402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 930350827 1250 930349577 930349597
    0x4021306090911030403050702010507032a0c0e0403090e040303140f01080d110c01030c020f0a050f12040b0703140706140601020d0801080705010e190f05040b03010b10260903 77
    0x403c040601005071843c00c0d00c1c461030305a125940b400109600440d43d42c0d1200b0411418884038901d1400c410504601c031600108424480c0c00880e101c0e4200300c80030022503030281680b07140c0c280400c0300180c0d00c03003025011540d40310404880c0e61100c0c42d069015102c1ca104032b00b00072680d1800c212140004600d00340c100e0342c80e04143c903d0203003860011144503402143c80b11705a440240e400609501c6540000d464800314415141c541e03c0312009079040405000003030300e542e0b0040c481d0070b0314050203000d8100503079040c0c880d06146c2464860444014010b540c07014007480200f0900c011240c001d103080302d03191540f2060800515010380002500b03203000b983c126005100b004c504841d0a030040c00d525050b940d00100500045180000465003c008081c40503000841640304815458490b81f4040242c468084070315820b0741050140000c58465a40700f034400d0f81040e910015584650301e980009070054038000c03069085d04035070a1000c1381045100d6650620320800c101101102002078960852 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 930352077 1250 930350827 930350831
    0x10506340c05010e060307090b0d0b0d111008130b0a270605100e1342090b0f0c0913021b010203090d0c0c0f171c0c030c02040213060909 60
    0x51350000b4801540401c640d1840400c0703140406000743e1941c1009455001b96a1402244903403d42000c603010703c071380071005ca17070010103d40c2440c1d0515160104c49405500c0d40381c403113100d103014810500c0e006100c45010b8640c407080400f2400039580e58116207010380f0800f40507244125100c1d44101c80c000f507120141c0d96186080c02061094a414407918102c40110301c0b151034545030455400f8032a8422a000c9440c00042c1441d00d8a0803080e280d039280e11065502c00024070010541500042c7c4c1500305d5607505e40745001c4075500042c0c640d0340c8094000540e000c985070395030b40c0d40004a006100d5100c0240c1d02c0b100180e14840c0d000001e4005041100540c02c81c41d140c4191800e08030b0a0380019070798008181c00c010403008060b44100b105c050b85038007030300152224603510252641d41c00115086001641e038085a6114180010400001101e0341c078090032215201700c0200070188168450000c082001e11505401903503a41d40544000c04440800388540b680c2d070300c5016041400e14480d100c0703964 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 930353327 1250 930352077 930352097
    0x120507060b09010815090c0a12050c030d0c0303150b040803040f1d160e060a030b100c020a06050c0703061a1002030903060c071a07180806010506340c0501 68
    0xb040ca8041c0a048400c00d000420081300c80302d45400100800800c0010144520420030043d0380d50b9022900041c950300c155201040002e003082c2d030900000100c402d0199008101031550b641d80040744040c45509854001185000d040386103480030300d03a0740b00602e44c0c0000714011900d00000310003082205c0f0084100ca80c0903654200b00441d5901d4500304c035604540c0c440000360060700b000a03010117900145040c0a0445e070942c0010f000341c100e01a2039001a9645107817201c1d50500740a841d5021045003018402c89581d90700058003a100340c010034003080000328582c480068100000d00180d64000c0042c01040f00d000020b0450284098000c1c0c4112040c40e40c0c0c034119400402112903200300a000382c81f142d550004180d50b0340e40001d2040b80c450a6003960907460070b142d2001c890040c00c903a501d5100308286040442031040054002e9003040c0c04c044010003466a07050101c40d526080300d0101200c0c09a400001008100c0c550104038908036511441d404204000f02042c0c20b40b002600c400c220300c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 930354577 1250 930353327 930353329
    0x31b010f09180b0a0b181c12030e0102070c120308060108100b0307110115060801080f06040f081306050a17010b070f020619080a0b040c02031b0703120507060b 70
    0x10401e0320406003030420400b0500021800b5030001030401d040600126410307a80d4030076486183d030000e80092046000300b07801c0e18440c0303071124030410300c40300c00d00a0440c5050180c88020f40d15070f0300c40d4004103040d0f0b00e8484c18401c00c000e40666a00d03941020101c0e07112556103102000328200a20118000f1384c1050005135698040d004143c022158000e651500509140d117082c05076002601a0042c0840702c0d0601c0c0400509000348010701030402813030202d140c50503074081c101c0c0c4410b030071107001c0782c101600d200800e045c00100c26511030f4000485032400c0700a070502d003815101d046c0991841580714100425140d800c4402442c800305240d0f50101213400f003500c294001d030028040c44d01c00d04403c00c155000305240501c410b41940c00100710f140b9082c08038a0a0b4402049050150049400d4500f0003030340d02010310800300c80030030580f01030010000440d80207450340701d10020140c810b080401d0980300710004121720400346074040d810002400310800c025210341c001190898405041c1601400e207 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 930355827 1250 930354577 930354587
    0x50d080310090c05160c0902040b0a090902040602030d20040608090d0c030804081b1605040b0303040305060714040801021c0f090201050405010f021009080c100b060708090f031b010f 80
    0x2049040c4d851505001e445101c101784c140903440b00351040c494a40c40465900c2d2280300403c000c25142240b55550703008028041c00a0f08a5840301d15194814002040341e103401104840c030f80300101d43e0005a0203c038500f40400b8144c0b501c02103080003008100421641d40240300c82c1d0251042c442110003100180000301c0300c82c0295080240040c81d000040b80008194002801001d014040709054050010f001246090420107a500d0b06040001082003103050a10400282020640c0031318036107030171a19110f40d5003c0c081d01a0b0300300a0013003060120100c10700140d0340548071040095694a1181c0a02105483c100c071103442c000e850f040351012150064851100c9955040e12064206442e220040d950621725191000542c01440740d152100740e82da202c2c05152501c94a072079a21031003c11000c42c5000d8606e030307041917035a01d002c420418950f5403500f40d541c056407108141c0d59503440400419584480c0e58500b40e018400c0312203070a05040c1c0040349110319102a030301c075007510240b001c0c03c840d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 930357077 1250 930355827 930355841
    0x15010e091b0d020d180506130809010c020607060c030506180108030417030f0f0909010803090102070e0604060915151107030204090201110102030703140601050f0927040b01091a1f0306050d08031009 87
    0xc1060310410121340302f5409038080d48901400102420b003030400684652050304c1603600300c503001036540c20800c0b0080c600380d41144418582d1001031170481d8103090080780c1d01e05c00c0f401001043c04541541d0b10302c4080400455040400b0a44400c1d21108250b40031402d503000544154407900b00c3c100003140f609070010a40318291416802070000901d00601d40301004c3d0041c140d45d4000d0707128040808d198130036000c2c41030f42c03801004088001030310307001c1100c41504680311000d0402000c455483c0700103400044c0d0205583d01210001402d414a10041e034080d03a841c42c001c0080d50010040100158260b405490520b03007031065a0020342d03c200045030039204010031600c02d094140500d0400c3c1c00c00100b00d481c0380c9020258030f000d040c003044641d5003241c0c003140d003140c007041d141005101e8240c440c051035000700c21909045212004000000e001e8100800511140c1c42c90b150f1600f13031840c401c0d00000001d20002d05885562800d60803c3c080551040358087c002843ca00c000285280c9140729a070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 930358327 1250 930357077 930357083
    0x105030601170316140a210503010501080412051b0105070e01180b0711030604120e1c020d150c030213140913081215010e091b0d020d18050613 63
    0x1480c05110041c100ea102ca00390005517031100c82000c0c00382c5084030400050309600e00900440c848102c101c6540c403000011203a040b0104181400100210b0b41c2020000b43c00c10391020661a0340d010700710341280c690040005900b82500000c0d0058040641035104a0041825589100051000360015158410340302c3d001041070000e010f04101388800e0902420b185482147c060301e2250309500000e141c400103a03015254440300c1c2d16883d00240c0c021101120301349054520b01e00d580d4508003030348030708000e90344043c1c0940e8580b80c98a007005004860440705200c488403c00c62001c040b20020000d410880940c00109664000031480c4201c0c001c2500100034010400c1040390780c2c0440308550707480350b403a040b6092081884060200c00101113258070502010403907040f40e44607034000601c3c00508080880c043c3d1144070605c440c81c0c40fa03880903802c141c0b40e074150a584d4440140c1220003841440c211090540ca03000d0211610285440456040c5019608566940d16143d40610328540b02940003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 930359577 1250 930358327 930358333
    0x503070c120807120e2503050d180e04020f040203040f05010606050c0f15071107150507060f09050a060c2106260705040c090e10030506090c01021b061e03010503060117 74
    0x2280a00c03506c5980500c55000c14032000403060794035518607240200060072200403d4942144045201c24a4256002800c042a41e21920705058010a1003942c800d00e4480c01540c000000400b4803041018114059074440001c00603070340d0b903000003001c035040001d41c0503190007200d000c6150400000340102e245d1040281d003c0840d02c032044c05460380c08034030302004524000d04400188040f800d6404540354051500c0795a84c42d0a280ba08100300e4090003501c403041454650340d040030420005422007050381c080000160401440b0080d01c030b04507040c500c4d803d24801c0804d0395080760742a0f04810219159000109035000080c0d0019040704901c11810106078040740c020000c500d02500080003c0d005824045050344d00c4107800c03c030301901181c08403203044000d0810030410804010050340300801c800540039842207040000e480b201c907a07180e4140165910700c4640310303641300310032110202c140d4601014154002823500b015a0402d110391446070013000000151042100700101c00180e0f0380c005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 930360827 1250 930359577 930359593
    0x170703110910030503040e010305010c0507032019200103090b0f100b030408074101021b1608070f0b131701020702090a0614010503070c120807120e 65
    0x60080400c00142410b14072401801d0020110300140000e001521108810030981d60540c103089080d41d80c0c40c1d03607140802408001c00300110b644039240c420012100c211440e8141c5412164514185141c19510b4410f00c040d820481040041030900a03030200d5406021003a60304100158107c994015000d0903140d500d000103034500f441554140c0c2d1001c0e400880b821115110b071054011604216411110320600154040c180080240e000c07051110384441401b030302c4c4901c1500c9a46403c4440300e0a040c0b0351009150501402c03c1d0166131080d07200000c61100c0842c04d800c01541c40880a0140f40d001d0100e0790081182c40c0080340000030b46188500713950a10341342c003142040c160f001c61031794194400307095008030f450300c2060560070180074803000168541d00a4010842d0100014140001c5c181c908101009543c0c1c66800e911040713002402e00d42c0e160340d601c20050740c841c8402a0014603800340d46010b00324080d0400b0381c80d80190301a07a100b02d140c6c2082244401150050300116600b030f409429 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 930362077 1250 930360827 930360829
    0xf060b03010608041a0f07080f060f0f0a21021002010c0815010c02131a04022a0a0c09060e01090209030c090619080706081e0a0506011704030917070311 67
    0x360b0f25002441000c0702d10000b13652802c4101100c0c01605d2840c0d40f801910184240c09500c030b1042a0025140c07000c1d445541443c00c0010842501034488234000d407804241004642d98078105c3c41e000f003080d00301b80f0b169a8a0035144100c0840100c408030b00c6580041ca1010400d84140314070035883e0820b8542d0301854403400c00e108240800b00e5100b83c100070100b600b07030005884075a6042c112140014021179141e00964419240d01001c00c1d4260240d48180b0244019044141a1b407000c2c074014424401141c2c480b040150600904440180000d29a2305001958503080d5101c60b00700d075a08070b00791075541d0b00c41d10220107074441c0611081d0305030304c1110700d901145001c0c3c05a035003002c03000f01080b0401d114400a0005200150712841040d0442e1400301318081d0080c50300c1d58401011405a07040c6030040c00508a42c0c200900503a00b00f554a100103052070740100b5508000c202400800c0300d503490700340707001480503c1c18000d030600885403003e4071000c80d200180071419203503c81c0b143c000391304042c8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 930363327 1250 930362077 930362087
    0x50a060518100509060114030303010e0709151809060e15010504080d03050603010b01020d0909050c1308101508030703050d090b090616051e0901030b0901180f060b030106 75
    0x24100d00801d02000e1404640000c0c10082c88419030722001e80410700780341c041c401a04100050f0306c19100290b031050790640b0707075902000b01c0e810340707480003a1912180c807241c070102c66030205a000040710a9080e40c0180b201d07a000714080c2d820b80c00c0c52010500d480e40312510b0724140d0700700b84951b101c14148200451403004c010144241007940601d080390030240c1c0e4101d01c3e49840c0c1d00c0600c2c00007103541c40d800e01ca41d80c1001e0068040200c1300f13000400018400a8000300102864420400c409981d0700102d00303038401c800c1c02c0381c8944800e01002d01425446900b861340780c00f10b21907002c082c545400e1032179041100743c04044c0b0444080402841c20030b116920190707030039408820240c03d0a035a031554070f07000a410000f401e000c6c0340303820700400b400d00c1d0a00e04502240b402642d54000c0c04014030035070105044031a0b55518120f650150143c40d00c14040058000e012000e0300b403680400e00000126014600e1003100b400c11f03030112018025800407181c180100d58040c019048060400c0006104180c014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 930364577 1250 930363327 930363331
    0x7081b101b0b270303012103020111040e0a05090f0c0118030f050106081005090607210f0c090b0f1207050403060204080c010e0f0d12090306060806060319050a0605 72
    0x20001c522a101203070781d4240c0900c0301290b88010204500010401060a016241c240340c01a24010741c510b50410400b40c04c001e6050f101ea440e0080c82c481d80d5404c05100f0342080b480903a2003400c050300c80b91a42c22000c82944102c690440c12450840001c2d8890000207203006e80d41f81d0000903003480e55184004407000c5801c00c03800215004d600700300000040c80380b01a0180305010b00c000190b411706140180303003040340f2000300803525420071041c171a10600c041016070b005042424911025004006400c9006d011989241038040c50004510003450094002103000d8a099659009881d22603406046c0ea021741c0c5019003100780240500403240704e01c41c0800da0050320700d00305580cc3c150740342e44a0082c1da00c41d4203c44640c2e001012400d030300e035801110300f00306048212022049211142c0c041240e1654514018055003924441c48220501540e106c0c405584c011400740501a1075211550792208280e40c028004d100b520300281240c024107214030041640b100103030030ba5145907202c1c080a0240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 930365827 1250 930364577 930364607
    0x1b060621030c2a030a0804121406040c15090e0a0f0b060a02030c06010e0108030d0504030509030d0e090a0c210b0607031709010c0903030503090f0f07081b10 69
    0x401c116480b1061020040f0407004246114400045940040795800b10042400c1d041c1c045c0c0e110001400c0065568020359041d0b0303032880c2e84a00426101c1c20180c02503507500c005004603005410622041c419010007640c01c1c0d45407064030b1f000d0010300074400c4507440680c1c4124070040d00c690001c50060341c8160080300c1c04982d200780c0440c00711030080001c4c0c0d865110900010159100081042d2074a00a02c0040c0c0142140c20000b1701c0d030f40c50003004540700d00c2800100e42407141e42d0f6002404060203a0103440300703220060201c40c500042140090204000e0211103480340e0444d1000070030102160180b050403427446d036140d014489004914680c80c80031000c0900180f0740f101c0700c2c050f0a44602d40949100c2c0d009640f904480b038010850b42400180242440000340d0400040c80440c1d0b40001c06041200e605241c079603079035a00d245100b81014034141c025000c034000c0103c1501d010a0001c0c2c05400c0e6400d500a4032000c0400c1d10003100d4400c40202d400b90060403044d8002201d074090481d0802d4506 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 930367077 1250 930365827 930365833
    0x7052b02030c090c0d180f0212071a09091602030a0c292502061303030e03030a020c16050a0b0a0309050618070801020403081602030f10021b060621 65
    0x201d041c0002d0440c030403c0300d0541d200c2e1302c04203400c95160024000c45242c0100d140148210020a40b20700c20484041103011380101d10310078190000e500c0400c4803400030902142414207198459040c0826130744100c1d40300744a450b441000c103801c0080c5080e00400030000f50001c1d89420b40b034120030b83d0141d131170705003c3e60300c00903144009181c04000da04205040d9152890120b03071b85840910480b401c0007561441c060228100c111095554000031030139000101c40803a0308001015103000c0b000707085d003050001500d00002c0140072180c10141c0140503080706004c1581c8805246981072080c140c3c1901c5501e40c0062041d05c2084001442c8000f030888807186d00d000300e014000f646684d85020401d445807000340301c01c0945c02c48203000034030404003c2c2c4103420003945032501e0754450802074051101680100c4020414050031580d0402c28131000ea5040d5090318020040c2e02c00d041c2c0207401c000310742720052030700008030003100c900802c4880c131400c1d0041421441c07050012100031103490091415071544 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 930368327 1250 930367077 930367093
    0xc1b0204111e030a1803080f090a020a031101030b0603150d14190506070c0309171905071805060130060803030907090e07060e040216110307052b0203 66
    0x8441c5442950842c509501c29900c2c107010680b94220b61500501e40345800201600f4000039522003074450300814034082c80c900c5a202d0000503402e040c007124000b035229031020b0740001086a129940015440709032004c001c1c4c209541c00740701e0648400c58403882c0c44104200c52080c01d00d00110700f004224040c42d00a10462401d15009281450192a01c00702080c3d0b07500c6034040180400440fa40036490349810503030807072240ea019000f03141c140200d44e0b80d46010302c4144081030007001441e402c2600081c501a0040d06806c0098440c81540660720724024030481e02607207070300c80303000d228041d5106943c0d40f200c0803400d0580c050300c43c048569585ca41c03100c8610400902e50306000d60405400ea5001450b900c0c01c6c01b00c28103242c5081944a00d0801d070a25046140300d0b080070030340004490640c1000d805141003440064005d104c0c2160164201c4840608a810b02044039080803401d0710560441c0d540700e03290410040380b40c40d103c162440300c18290048002102c0000394804d80c5502c06005c0310005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 930369577 1250 930368327 930368347
    0x5011d130c03050a0b010605090a1a0702221a0a05040921030204140a0e16140a120e01060f1707030f0f0c0905090a06020a020c0d060b040c1b020411 65
    0x2075a86a00075034059000600220038028070381c02440c0100b480d82030942c54002c00c2400b10700e15003000d00c00c0c200e0441c1303285809034100340c1c0c0310121a1b4a6900034440545403800511000742649000a41c1404520b0501d0091200541040c8010780000003000c0001e102d250030304003c003410540104071080c41030b44400030131550401d580012404955140580c440d420159828081000c8880041c85428004e0303040120003202c05106811004411a0b450310801000307056805018004051112020000c2c601801e190311014200800d000d190050000444004444d800d951082c0030b600b21038211807808001c02070914150b89450759010090710b050075929118855a40403950381522032000c250118000c01072124416409084140010803c0d400c1450806a442d80170400040c1503aa0020300d661005008000c10041c070240201000802d0f4102e1420030301402c071010030140200d0900000c801c98601a000340303101c03e040542201401c0c480d9800f00f0002c0c0000d0140c030702008400b00450381e04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 930370827 1250 930369577 930369593
    0x90c0a050c07080705030c1503010e0c0f030a1e0507140d0f060803131203020714010e10020c130c050d0c1b0c080d0801261c0207090507020105011d13 66
    0x10583c5801408131113180030207050811114080007441200240248103890b0361082c183c0381500c2c01d811401055541c1c030240007030240314003112450940008010090b0b01001c5030003410000d1a2140307911001e40380b42c40001e0079104155000400328040100d00d204091134240030f0041070302040c0011401f2003141e02168100c0700b880e0816030058000080d441c4c0c902115001c000024414020074085401190314001e40350082c070b0243c00c4000501d00d000c059540c0c4a81601690390750020210002c04880031000ba40d600c448086d410300aa4102079054400d0801d4400c5640c60b100b542c8446d03150a800c003090100405d41d44168200307100100c00800310074207900b480303d840c0070b210f0862901d00c1c07800c00101901d81010031042c41c0401503a040140704040c3d40128031007118580c006041480046005098107103400a003422500003c402a0032046503130025214048442a81d4204415128041c040b800e84900340035149a42c0140c220302c050891003500072940c000b40302c19164451403141d44c1c501302 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 930372077 1250 930370827 930370829
    0x703050c130f05120d0518040b0414070e01050a0c11040f0204120c0f050d0f0203010b040f23011208031005040f02040302090f24031504030302070b15090c0a050c07 72
    0x25110b40c4008052180d420a10079011004510710000d048503c03030810000d102d0301c6001d042900302029500510a281c54030f03001406207400080080c840f00c0c06400010303020443c110b680790001049408411450350281048540704091a50f60540c0d580c2d2507150340e0136004242280c248c21507610025080b0421440c4094406811140081c0c11403c0040c10685842c25158200341550258601c003004103583d00c0c04038026051340306022006071101400000d00600120200342d40041c2405c02d0350100c6034165103c040341c03202e0031090704407104001d030510140000c240034041d030300030341c003020741000c2810070003c0c40d4480007003018441103d07100c42c041419034000580c90501c01c0c0e00441c0074421440c02c240d21550003100c071048030040c5d15003902000c03006100402403207003002041d040b0811944040c4001d969440c503401c2ca021240c10b0519000b8000c2d40002800e4400140319004a160200082d0b10b661203200000d1035080c042d00d810107502165031003000300d4018401d0402c08605400410b0203520 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 930373327 1250 930372077 930372089
    0x2070b1e01050f51030f06010819050a0222120602160c1508070503160e010207051914060304050d0f030e0a0c1806061e0504050904050109031b02090703050c13 70
    0x24130b80d840d0241d00d0b51001002401504503000207200308500901c8180325103500c035009203401d00790354454008150300383c1c1021201590b8203040200b00300800c5899002004180340003141d0010503100000e40c41342d0b806d541c0c028201000949604d060124220f42c010342040c1030030440f13800b6101002c0e9a024000205680b060001d03440648004c002d198200c8210350344010700c0c0c10540d285141518880d1804040c89280e401440100080c4160700d910802801c80608006003600c428a0074401d02000803000b070380700c0c00c4240780e950088400d0302c0c1818029280540e0307000000f0900c00350318032825038114020503140810940d590180e400c20305000c02514041c00d0080d65492000b90414619202100844217009140d07400e0120030084c440e0b02816080c02008402091b08040c4007440c0125031901c130355408182d01c40c0341882844140407042d40050100c40c480d8445441185207203410b041c04141c4042e000c0e600c2281c0c80c0002c2c00850184e041250300191520146152800158424804904e260011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 930374577 1250 930373327 930373429
    0x51e0103060615050a0c03110f010f02040f050f03070e460b0f010302030a0b0a03050304150207060e1903060e03070201020c0f090121020402070b1e01050f 68
    0xc010340706000329640c04103505464454a817204583c00504140103e001c0201000300c681822800c05c4c0c01031041c9038412089034028041e07802aa03070b07014041c7d0020302806110303015179680014245004906406842000780103404c4031032500216000c1d10000030310290840600304010780c902030180704810142115148000c1c500c0150b13000080d242d021a1000303580107803814252803004d41e546003110b9074980e000d20300035950340e440700840c00c05031407003403000f03500222149004801c00602202420070f4504d01a000c80c2001c142c05000c0381c2e175000b80d11a00340400e50040c1c2e809054140b040704080484040c0c031411495030707a6591008200d074204140c8400681010854108560f4103000085010b1001c603a052003001400700000c0d1004010b01c203500c0840090002c6054001e203189220020b1600100704640b118400c2c00e1519400030111502150039256680403205001c03c081420b050b908060161546d0030205418084420000f050a805180e08000804500e0a460180005c01420710840e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 930375827 1250 930374577 930374579
    0xf0603250c02131a0927030d0c0c1506180f150b130b07020f0f030a050d080a05251b0206370c02041d0109050c2106040204051e01030606 60
    0x1520440104c01002501c9094200c2c180714144401040c00c42052080b20a104800d0703030354002e83c5103135100342d6061640130717414400000040c6802c00b0400c65034034015205110054004200c000803070b2054042e41c0481c161060f11207070b00c1c11150b400410030b281024000582109102225404100d0369440680e04410006030349401d91403c0b099440284000b0b1541410000160300084145008944443c0180c9200c0300401c015070381004515155030b041800d690300c219034603100901405040b900080e51900b46004607248107090300c1e90f1102c00017000c0d134032840c00c0880c05003100c3c00d0101d041e0742c0c02041d211500310350240c0c1d1540300410700d0201c842030001a06681c1010300702c00820b41e03802a82d171000c00006030401290003001d4610381c540d04450000c0c15002c80050020342d480c0711800002c2c0340d172030324070400100040000d4490320f1070400c880320440020f20701e180700c1d003c140844900086070011804100107041a07003115401011019006600c0e1074445920062000260320655006407a004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 930377077 1250 930375827 930375851
    0x190f0602250c060c0201081f030f03020a061803020a0f150204081011030c22030b19050c030601121d0a080d0c050301030b0103110d200f0603250c0213 66
    0x141180140b6641c1032a14528804d40c001074a0402d0050905020050304031001ea00443c400162002950b4895011000d107030050400959602410004441d21803a00140c812640d0181e42c190b4415a0f0550007000c241c2e040d80e48440c081c605800c42110014850071040088200342e0000e01302504401c1e00401c43c0081d4941c118050307032200420610180310800070300000300c0c5440116207920b0428400306004001642080f07050450550000e0000400d10b800e02c82d0440388041600d0400020040502070f0342c58519120459101c1503507801c0c0480d070104260440e100d20360f088001c03407201c0c07403180c440c054809100550803e08000802c8985950000d201500103601c1d104812140c0d8062030541d05660640e516201120301c10700002e00244060148551282e41da100448140c0303a10201c0c11020754040004d04444c07200e9110007170710a40c0b000c2c07140d8459040c040b003601d04c075a2265020f10055940b8031029685840089142c2c420000c0491594015031280e45d04c00e011115003100018071054160 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 930378327 1250 930377077 930377093
    0xa03050f0a0516050f0607081905030f09010b10030f15060305070912020114030603010f060f140906060301050d0201020a06501e0108060601020f190f060225 69
    0x200e114082c02c4a1800213020036210020348103900740c815201c0039039641880c2840719050003542c0c2210441c0317911445160f2451b60003c042d50080e14162002076060702ea20a115080c0c1d030444049a41080000c40d1900d441c1c8d100e80c020030b520740714820001940160383c4043c018400d4803038008401003510764090007030441e0301c00c01c5c08004000c0c9102d204204419a4002080071781d28442c42148840c0c00b02c0400e001c0d5074203502074015030b40711450811640d03503039440d100c2d5110034038810483c03103e518000200460a00130035a601c0781800030b00451840c1c3c2440104589030642000c1039045200e454030310800640b651203004454000074241c46030300e0514034170380d20822848511510140b04c0101c40d401000c242c100508185402026160751295504074590403500000030207042c14100750000000d0307400001c24a640620000c3e404d4408211401c100e181da42c13556000c40d08070b541155558540824000350f25008241e10503800940381c80d0303603000c842d0b02c401c001e15004003c03800c011521404110441e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 930379577 1250 930378327 930378343
    0x10140d0e030a0f0801061b06110a1d060711091b131410021e1c231c0b01021e0c01230405090a1b051c02120402010e0a03050f0a05 57
    0x14138140b8682d604042000303128841004040803240c000c080080104045900002c01c2800d0f0725842c141c0340c20729148014505106020011848207014050154604105044440a81c3c00071140b0b0f8507611a42d040c48614100100084080700e188076100b9109580000200000c01c00604004d810303e040032241d8102007500049644511049281d011000f0303004166082040f440b401e05502c242022000c0368240013200c1c6500e99410820400441c5650700256a41440380c020444800c0d5202400b49104c000d110700d0102d001c05108100760070070124240d8006035100c89061050768448403001042040c80c8005d50101c256903000301030b9021540d60f111400b400100b076003c0101c11b1407125a8001d0344a44598012a4012106100020440303000d64003c00300000200101c015219000b00006103d50082c00a5141c0c038070160342c01c2e100c841054029500ca09182100c2d610b2030b900d0391790041d10b0950b01c426010342c0001d1450701c00030202d54180b0641411403005005401440c5540c64510706280f00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 930380827 1250 930379577 930379607
    0xd050108010501060c020906150c1b03010c0918022104060f0b060d0c270e09030c030306130902030601091a090114092806050a050f10140d0e030a 64
    0x5000010404c0c15070008800b601d003601518080c80302d80b00c01c008586001021400208440000180c169005800141c0f80d8202481c0300240380da41446078040500781d032491038019002480100081c060711050309140c07294420380c41001442d02e92541402403070314800c1007080c00b100812004000501c0494001c02d22000c1207100c0170014035080c10700007a2a4060072840030106035486800b611620b005040800150a1030b549030340044030101507200003800280070380d4288505900108400107400000d03244035440c07450142d42159180e1081c40b14051090340c524100603160301d50900903841c00c0c03042c240a800c0b400e1004c2041360010707450203148801074200501610712240100082041c03c0c0d42048000000c64413245640ca65001d0400c41c1c1e01d90303e0300400140342485107814101003591080d804c98905071509110302d5a00c804109050b160000b0b490f1b003201c0b944039034445492062000d80040d80c00c0003142820030510608100448401607500700645c0d0001444005080e00b1442c0e20000c100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 930382077 1250 930380827 930380831
    0x21002060f0f060a092f040305071a0708070303060f0b07050a02101e0815120606010c080f0c0a0605060603040c0306021305100f09080627070b0f0d05010801 69
    0x801103a04111001c0040c64020b48008800c0802c0182c1d59203280c074001040e440409210311054100442c41104130105450408841035050005851100e02038404594110380601a401c5c6402c0038a0400e441d03002064440250400800d400241c0c18009402d00c0d600940d40000c20750709100e1100c0301c5059941040000100c00c0c840080022800a031082146905841020440314240d606590b8240c46a042903440c4258100c410300c119440141ca40c4900503842100403011904002d0045c00719040044400316040f81c000560340354010442e1107080d80c46400c5580c585503040d200d0001d150000c01c51101c060b0890030000d420300500d0b004454200000310740003443d5050a541d00d440c140b10a110040c029034010a49000010041006000500d4060f04c003c1c451844071100502070140c102c00c0c00d0200d581340b00080340e10000000e80610400c0684802181300c0f03010742501c3c4820340c4a20398800280300c0c0482c045100b10085001d40461000208a03a07200d010000e18881a900141c02202a680c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 930383327 1250 930382077 930382081
    0x1c112e080f2208071e0302060c09060d0b0a0305060106090602060a020c0705012304090e100b0a060e0402190e010f050a020703020d02040902041410081c030509190f02100206 76
    0x1041d40c2c0e205586450b10032004a00d520142c0c03400c16002d01403984050914800c0402d61012544011814107449221750300340c98241d0fa60041010300d60080000c0550401002d1209100410071544482d81e00d54005021030344541e501e82d03556240c00b100f604402d0000750480000c100003601089080d07008804540d0135410700038003481c8280d50381e40314452641005940076810000c05404460f0070042d00d42442596921070301c1d42e80040180030550000c150b1031054480040510a1600c03d80100400c0100600011440c000c02218405038100c400c950059003080f103840c07003c0c003414100c2c0d2880074941303801100a603004009040709243c500d15805000040040301c00144d400301c0c82c8416070b070b4112440d40f8445403500200c0c0050604240c000d400c01c0c0303410454540c421000700b07894461001008900c00050311052103c0d10ba8400005003031a00a002e0007448070b050103034100035403010b881001c42e84900011900f2140f02c10140c0400c1d01e009400710382100035414041c480507101040782c00144858 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 930384577 1250 930383327 930383341
    0x1507111b0d0305090d060204121a060904081b101d030703141305030d1d0a0617070320070303140f040f0204060f06110105061c112e080f 60
    0x1607200d0300007800c101c0300042c02100d60f6a9200d12084554000780115100c64558401101381c5038518800c0c1e54403405c0303220707441180c10040e40052041c18054400912600d0310b03aa0054180c200c2520726005811480309441d440900700880074204480100126600d580f038032500070b500440d90140e8129800401401011941041030896401c8558180c15511032011826460039507064002d0f541c14061085142a00b0b540800901c15982c4d0310040300d5003005400c420007018141d80d200d92008611b04500d890101c2c1c91b060f000d42c0c1c4c42152404c020444205118680e82c020491200c0c14800c0c07000420348000f450750600c20964207280910901c202810320740700a05103010014001080004140142c601b1134589400200c010a18a403120341c81c1c039211680500540784441d400030341580780c0400070354503141402000075282e01880c4602e246252580700c901d1441e00a54400d5044000300040d20651030880001152a550360401019054619000180382a0700070742215240c000400078400c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 930385827 1250 930384577 930384589
    0xa0e0606180d020619300908120f07080a0603030804260408072c010314030f12070e041406012109030e090f0709030f051507111b 57
    0x7122110011140318600c000000800800091600030b410800c0401c0044038003111184410036191540c4603030b01d81d041c0d81c801d480280d2546800c000c0c200f215034940085504940da10414540303014108440c0f42002019802503000310a4071200d500b40f40c080100072995504c0b00000b031f0401da1425080c03084c5459924000c05030b1201400160145007030600c1100003812801040721414640f00c6455100e40c0e5487c2e4039500c0b03800912a070851414100c1c0080b5440090040c03a6140d4030054040d00ac9a900b151142907800d8403925040354a817108110707901540140300e01803c442040515041010718046030010035000b2010a07150241d820700d54000c00c10a10001e455510900078038015540020340c40220428074080d99a1860131481d00e4070700303424150304c5040c07880510010b64142c0b403d81c96582c0403030841c280407203000d000036445080600008810300f00240e80b90f400741c02240d544c0c940a140c0070203419000c0da0700318045181800000001d12042c841c01e001e103503004845040c0c2d00c1046001c682 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 930387077 1250 930385827 930385837
    0x30d2106080a06050c07060e0d09320102031204050c0120071a07020909150121110d05060a0504020f010507080d0e0f070b0a08010f150f0201020d090609020a0e0606 72
    0x40f403951910001002040701d101556092900243d003440042010401c494840291084c03140002e2002c400200e0000d81440e081c2d59030100c2d0711502039050010702c029004540c0c40d00113181c11400700b0807224100110450f030761402203019901800300e80c0e03103010025221105427441d4040c80441c40130390581c40d04000c2000c05c02c458800c2d8510400c5034840c0d407800518810641d00941c07050312071082c4024480001424a03000c0009105100143d0300c0d450800c0c421400100e9482604401d050001c2c0000e0303038444d045a016001a0454803021040c2d99098104007003107841184490b6111704000551408103d204a600300a0038541e240801e20f445200300d61042c10352544049880c4c501c44403500030304200c0c40c940c1c82825019505080d443d010881000e40c0160580c4000400c41000492480344844a40e401c440c109a140f5171018260002680c2d0039410b24003000941d503090203000d0305540c00d1300414034024480c080004a448461040051815498005115503549842003028644400b07080307403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 930388327 1250 930387077 930387083
    0x9080d0e100c020915060904060603050f07020a0b04080a02100204060e03012f1308120c0d030506061614030a020c04050109021206061e0d020301050f0f01091e0302030d2106080a 78
    0x501070321081d03c0406e00510a208010b50041c0c5031400c0003030341591540c482402000da1100c04c04443d02c0301c0001700e82da0501001c002e40f0042d01400030030005075000d0014407044a01e07005640300346802c100328030126042a8000008941e10070764603000c520b001c1c17080302820086000b101649040300d03402305404034001054003128150001f2031000054109805400410341601110403c414a0000042c0c41d00462400407107445880707101c801c0c0500030301a01d13200c2d4001030704c480d0a00030795810300d001c0e0040114080ea8001c83c03911210b440000103000601030641c20ba002000030180030414401106d0b41680141180e500c10f0100e941c0702d02480341103e4110b082220002d4981581964500d05d1455641c3d44084c1c210b400625800041c0303132600910b0403240110f9203078039001d00031020322240c0c9a04252150001e08030340024052240e24001a10410010058000e44248c81f5400f0a2074a50300c10548008a0301d400e024003020b0480c64a45607a49072601c0050100c54500000300c2e50303601d44c0310801 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 930389577 1250 930388327 930388351
    0x1809010306271e03211409010204050f0409060216030207170f03030a0c17101502011b081e010807030b161e170a06050a06210b0109080d0e100c0209 65
    0x4007013418030580304e881045d40d000040380d064450383c3c81c0c818000d007199141c82080b0000600087c00e04c280601c00c1c5c42c106c030b00180046501c08145d03810000100060b044c1101c42550901545120545000d840d5481900c40d0b00103014141c2050b03452911100368a0b002045e982c400700c040c220620020003a02d4000110140205050007141410380740481c0140c000002600d0100404c0307441361110000304211510700d082100f044000b003800320b0a03070b1002a0345118405501c1888002184640c1042d540451301501c40c20403000f201e80c0d048403004080e44161134076440070301c0034000d0000b4200503603003040340032000c8000746160001c098415404039812000c115001d040310b4040e280100c2404540300c1a842aa6206140900582005109074002e40d801004407440c00301e0064061031461104290401d0f40940e03400e28449180094403041301080c1c100110384100254000081141e41e00070030107034840a0000c6504400e0000d10700380c011840b4100000e00484401584070720040036045014007110b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 930390827 1250 930389577 930389633
    0x203062b0318210311101b0c02300f0102130e0402030d030507030204051f020c010201021e0903010204051f0206060603040c06080a060506190e06031506180901030627 73
    0x405d403a181000d5a04d582207000d90034071072403030401c41d5100c6400411155510005001c00c0c0400300c8000102490007508150b190034541d00880d0030f00c03820400e155103030780c68030840498210072030b081107003a40010101c3ea4004c00c01c0c5410040c0481c1c00e60152902070801d9036a4030740703900003903903a480c85085c45082c50b6458001c9211180702e07404441c003a000140040c0c44911244408030a810381100490005000e0403500d81c00d00e61041c000c40c2c1c80c4d0b000c1900c8145604d11040c100696039800b0070b0200794159820800065551101c40c0301190060307000c0e002008907149210b010303040450040017079104903002c108000c0043c010b80b4011044d50a1407801c105165540480d1000402c80c607041964040000f04603039000c01051407032040358005075620311041102000612a0074042a01c0150400041b40415521810300c1d0029003480c0d21076031041c0e662040c0300800704100f0b80c0c007030f00240d801e180c0311603075407901203111b5140094a00105146a003120341d2034646070301d030105806003110b0542040c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 930392077 1250 930390827 930390833
    0x14011a030a0503162603091507080114130510150e0306150102010e0703140c04022104080d020d0f061d0109050735100b0307030203062b031821 63
    0x1607505071882070030505440d41d03802e000345c004260f00708803102051481a85141ca28646040c802c103030241d003175070b100c840380750742041c0110040c800c2c02c0c0340d607581040b580380c201c1c4030451613401038178081d14aa0241541c0346050034000001c210a03005440180400c2c090f003a081d075140020034560168260401e000c03500c3c0700c140101c0c090012400d0000b00c0d8401c0e01c101000b07004640070503801c01c00d90700b0f044070f804040c15402d00003640241104440d00c90100740240d030086240b208050b510520400c8258074002c141c02245040742c005000c1080c01d503540d4480224040d16510418010309082c242c0c0183c01d400080703801240c18014064403491940398400300b10b10a0186c2110100151114081003541c240003030800003100e031035000e030301d208880c3c031002ca00f46454072080c00b01618891035580d0b1541c0c2d50840107401a60014002640210400680e031420400140d00c080214155440c0c0b4550710038242030040c0045c41c00b0701d40310344100110104000d1802d008607800800e064122407440505a0b0303007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 930393327 1250 930392077 930392093
    0x2a09081c0c141032010504110f0301080a050105010509060d0f02040f0903050d05060d08040e100504090b0a05071803030806060f070b1603090305090111070314011a030a050316 77
    0xc002c501c911401204407104a00e6802c01e9001000315003000c0b1021854142d00c8440d020920000320b820b1600000501460800d500130884400c5030081d80d1b45007000e0180011815032090b48060769582201403140308101c3d0a00400c0c2c01820f08071003a01541c20400b00151540f103400400800c4018201013000864440340c1124041c0c00c01100200660146828041c100f6132112910909251070000080c841d03141c62520818400c1e040b10075a4181410030000031040700340a0100202410f2400c030010b802e5855006c1d0030741e054403407801c0c1c8403981084c88100095850142544c42070081c0320413a40b081c100d000b9503010440c0c0d05880d200c0403640f665004102c0d00c0c801d1411040d40c0e900002600c0302031090300d50034a400307507203011a840190700e40c100d404c0301206d49480d0020001070040064070043d602c15680049440f188009803000da0380c0c0c2e9910480060000c0321070003990b9440d401801400314020407000c611440c150054201c000581c0d483c552039100c1c0c0101012100c0c105880c1c0340070303c9198 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 930394577 1250 930393327 930393353
    0x504240816090b03131707030225081603030305090c100e060d050a02130816030209090c0a090b10030216060207140607020109020f010203090102070611012a09081c0c 73
    0x841c84903a00d05000d90300401003e017001058440f612404004860000b005d130482e0701d0303660540e015100c507040e045003880708000f000800c41e903402d2043c0300c08070364180d0031701c118040804030190070f04010f40f0b5441d01800381e50300104020390a4029030301e2116143c40302060300345c00004501e4100c001c0b01c10310700003035005c1c05850400595a40b80004100c000e000f9035004161061816007100102940c3d07403161a5205c2001e80496250340781100c0410050900240031600701c5c841c0c1054a50010130030002c600f481c0c00355844030301156211084104a801c01f4080c4c0200342829184c00e40ca080d0a80319440c241103034a40d401420b807a400252030090100014100000304120000d072401428050002070180015500c264802c014100981e401d070747c00041200c661400680161417070902e815800e90344200010041500c0e03548a000f048120b881c100c281e000d5010803e80e84100350120060002e0078046282c00c0845154003c40e840d094000d801c4190301558406c0d450000d44580c00c5140002d00342c008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 930395683 1106 930394577 930394589
    0x30905060304061112060f0a050105030f0c0906040f0602060109061223190c0801091703101802030403301a030706050424081609 57
    0x200055940140103c500241c0c4200f0510b4410700f90f0302010b02e00b07092040d0f203400c1241c00d252200e41b05050350f6054030342c65445824040080d00702d01c000b8025408040c1106c2c00182034803e43c070201c446024000d00a9516596202e1030061855007a008002c0540140c42c00441d1200044c41201c0807035010220284034004151074014032254410301000c0300c024400e01040c1a003001f00815a02c14240f24150940d13000141045e00350380407641c02c013201e0b0713034103090134040824a45250904501e9141c0030aa51b02d8079402442074500001d68045002140c040080601d450701a902951003140030303848030303905e8450442c045441c100e050515080e01c603d0061160030890f155900000140a408900ba00d1010b00d50700000d2601c0115404100080c000080500a91500160f6170203c114001880110884031070f5015181c0c5000510400e00c9007290707c04452414411400f04004101d = true := by decide +kernel

theorem cover : BRFrame.Cov 930215827 930395683 := by
  have h0 := BRFrame.cov_init 930215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 930215827 ≤ n) (h2 : n < 930395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
