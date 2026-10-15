-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3985
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:49.370061+00:00
-- url     : https://prove2.me/submissions/46673ee2-7266-4759-a27e-90426f69859a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 716546762 ≤ n < 716726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 716548012 1250 716546762 716546767
    0xf061b030318020d150c020705060d1e0f0606080604020702031e03160c080c1903080912010e0c01030f0b1e04020408030307030c0207091407031a030109140705040501081c05 76
    0x580d518800b46003101d0068109060700c04141040400300c0d85a07081c080c01f9075001000c10880b0b60b403030f0401c5130700d12400550081144110306034140c20119429260580081c10203000c041100c4407503201e00122012640e07410000d403100410b005c120310901001a400d50004203484811032a03a00c1000144a0b42c03100b100d15055000d5800c00c0517409160f0304075202c0b6400c04080203290010030000b8866603048624031208500f0303d036482a4181540300007042c88001085010b1266a80300c0c4208085030801d00038070895030100c00b182d031105031200e080f0340441d01d40226070502008510684190702005032140c1d1485040d0b8104c0c004803d0215903896000782c00b040080b03017603041032000d940240456280440c0c4a90f046034064103040b601e42040c90017600e17103401e8004441980c9607c030f40084080c1000a0700300c03514000345a0300400b00b40d007a6010340c240700304034041120071402c00d40c844030040103444030302c1c1e2220300300401d8800038030a200156010352040d85213030090708442c40b274103521401c0991 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 716549262 1250 716548012 716548061
    0x604150b0a021c0206090d0e06040513020310210b0a110c070f060f051213080406050d112d071a160f1e02160e010f061b0303 55
    0x44060344040100401030f0441500f0b011280740c1c040f50b689881500d80050805450b060074401c3c1c1d40d07079000c0d80010030443d03112030004842d141c001c101c8002c0e10000e040f200b445e10f010141e80e4040d500c1503800010040c614400010500b80b0044070041c80c40c0c0d8500690030700611071301e466103111000340490908903503800301c6d00914248a0001c10070020305c140686007681c5400c171103283e641103660245060024041c01b0f10304e0704e40d1003000c481300003031b4540b170380c01d4039484525030000c0345100307a04002e1081e0350004022415039003102c051300007400c2e44078060001e1074104004c0b4440e4082d201d0f1410462045544204291204010780c1c001d100c0541d8640381040a543c55980d42c8400b40201030850b8103c42c4207000da176104500741d03a6801d4000b810709144143d0020700c010984140c02610340541201c41203a114924402c0c046843c840040c650305a4010b41c4840d000c0081100a210b110780c1000c00c0310b00014032074003c01c2c5528104120301c4500015110989043d030203041c0b2030b07000511200c0c4407828034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 716550512 1250 716549262 716549279
    0x51c0605060d060807060518010c050c0d08040f0807050f010e011b0f0201122a120204080106050307051210050411031b010e01170414011407020a060507090e060415 72
    0x10500d6050741e160100b025450a1340c15814845a50040303020000c1c1080104070b844000002c074181c404c001c1c600305e40f04820300d0601e18200b5286c0240190b00c1500070340100140700d01c2001520540b0401d00482a1090742e400140d9a00d000c20b02c6516040829454000880c1d07005040207408240d040c10070001041c108040d080005440078421600d8220aa155005550780000064a10150010100180440800c00c1000c1f8109000013080d80c001050800d02c0140c031880044181c11075504065484a031640304d4540600564000c0354024400d4120014240c0b4000020702000c1c02110080c141d410181039442002d030030300400aa441e03a01c9490303005001d8408210706c01c0d152000303042c91008900680001003030780100000403410040d040110a240c103044e00325040d0061781c005070460170446003c1000c0e014099881c50700914a01c403400700550f0310740220b40e0b40d100e9841030004000542d1381020544100d601401030102c055000000610981403540c466900150541000394140d5900d500c507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 716551762 1250 716550512 716550517
    0x31623100203031b0309100b0102010f090506190504031209080405060a02060f01050301050601120f091b030611030c0a031d10090506090d0c0807060b1305070e10051c060506 76
    0x250303001a4400010000e0038441403d84070f9a483d0501e0082c0d1850030060f1b1340d1a55010403040244180355030b1814031050368000d6200020120680300180301250a9081c5140c9500c0308030303111032030203020200010700190541f088511807585900d6150300c040300d400c0050020101b03550115180d490400003c241e696543c4050304c00ca6000e94000c5c1407602d011000021040010f82c400d902076030404061100b039030380001d4003035842d0341c42c001c000a412088090900140904d04000f0b000d080c10160b661590000b1241b00d5000d03240115400e0000c1c1440174810301441c4030890301d080343d18001707000d900402d0344660442c0030011070245180b5407060b004a00a824076001b030328030b0010213035500e1021003000002d00031180c3c00f44040d0302400c132104010034050509a14031100820304000050613500f004469400340d042801d014104d03c0403e480c040020006100646081c004140c00e0a100c0c01186042c0b000c4865611740340d41c40701e0a1990a0203103114018840410a003000d0300d5080101c2c079925080003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 716553012 1250 716551762 716551789
    0x904020d0c02010c0c0305090411040b07060501050913030806010e0414010b04150e061b032704141017010f09050d0305060105041a070c05030f0109030e031623 70
    0x800240d54101d1110190071a01e002c0508000d020201c55200d022981100668050b444261404109442d2031604e070186c3d8415504141e04c1450041042003d000300da0f80b103981070300d40035036143c040c544030b4500b114191010303038000070005460800003800a51150719401d00c00a0050800700d6480d135504550344000d00d00f42c02210440102280400c030302d040980c0c1350448031566041070381000b00d00b000030480c14490300341e004186035148030110901042c200100d5840340c46024441c20300d1182040c08400ca43d401c0c00c0260720030303130800c841d22610452a8800e24018000405d01a036a18640320180320700e0403d00c3d0686e0f0443d540d81641040390003090090306c0300244a040a07004000c2000c034007400b06d0b034003d0810341c1000410705c018000d030304030901120340100380014a10b440e42c01916082241c0942d41d00415058050555125160101504401c201e00d03c203443e10045810310f04185950f0300c560a04401c010b007105203040000c074203440150010315180104000780c0304411004155034410108 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 716554262 1250 716553012 716553037
    0x20a1a04090f020c0f0c1f05040506070c031e02010e0a051e01021e0307140d080a09060f24080c2d0a180501060c03050906031e010b040303030b060c0601030314090402 73
    0x32007400491802c80c600c1e43c011f409541a641c45c00141204c000c0c0940554002d49010b000005240b005102183d24404010350b0700000441501001c0c1c10b42d510051507a40f000c81c0814050100800d09107014071a035004d5035000b0b850908860303804100349080520600101d8158090f9109200d0102820020034540044400085540e07501a28029034621030481c0000707425041002105026607000e45680c1d080740b0008000700fa4543c042c14441c00401171540300d603d145103011341c614901000c450140118410480d260320702d041d680d0079101c1d12012082c0381c450780b1048660b0448221034140c03862440d11014000a9a113540c0c108021a51034255a01700240d42c41100c61b825541034154000d49014042c039142c00c0949504546d030184c028007805504070700c5906c0100c0081d10011003d4002032100148060310318880d6583d50104449902c180416000281401854252401c101c011141d0f00028000105002ea19546040360b444100300c03000000340000308415103055903580054421901c41c0e0307 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 716555512 1250 716554262 716554273
    0x60304060e0d020a11030c031c0302041e0503010e0c24040b0301032d0b04141507050a02100203060d020d03140a0905040b030a0507090c09080a050a020a1a04090f020c0f 74
    0x40c10000a400000c145d541c0c8603911050b1401001d0310701092080714103645102d0320341e500340c4a0005801038000c540250044144407684840085941c003840300448400350020040700c452980c6540d00c404090301d89580144461034001c0f50740400300480307902c000b1007180c89030900d070716a000400701c0c0c0d00c20392007514401c82030b005260000a0480140400e69200d086d0840303100404d50754584901401130000d08070039401903076100020414081c0301541100c042510203d4030345514094440e402034100701c00144103000d01c800c5041d00603c00c490003644010708903103901e200d42e405c20403003035201c400c11000c01c00c402d80340c1e0015858174406041e00d104140c03120721f0700350300f442c050008448450f44400e11030ba00c2a080f4102051010840105551000c0004145510905400e07505840d41da48845078500c920030210050110114458014901c00c5030305030741440d0703954401c07030400807413481844600c2c40c01c00017080111140e40c04000b5031101008090300b0114680c151a04200c241a100250354004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 716556762 1250 716555512 716555533
    0x10305030d0b101d040615021f0606020c0f01050c0d03051e0c0706200a020615010804020109060f0e0a0305030c010606080c09121011180402090f060304060e0d02 71
    0x1a4080d15034802c0058440d12110303c0310300402414030500003451340010003610124015030322150400700180403800c80803494a4103982c00295a100b0185803111010600c1080890f04a00ca000315012500150b0081600d40c115404201078004800b0300c20f8140300040052003a5004103003e9440800c4654900040030303d0b00302244001044030741d1030052100070090410910521040c250341d14035400c40c100148694100c030030700001d030b400d100b40480d20300800b0941e542e44960008415200745c8110480301e00c03600c0030701c00545074050240d40c003d0215071142404d102c02803007002568004902c51800440c00c160020208000c41c08940080e14039820024124200440034095200100717401e181c0031445241c4032a07025090b00803a40e41a00c50000c919400c1c801c3c04081001d0007a5054040003042241465210b83c1e8859110070007040102c055404040c0c02854644251007001d4000380030340980308100c2080202c9540010401ca40d09980c407808000d9031407081001c00034400182c1c0084c403040702c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 716558012 1250 716556762 716556787
    0x9060608030c1212070c02030a08181804020a12050705061305031614122b0f080105010c030f020f0a03020d03060b030613092406180507082d01030503 66
    0x3503c120040d15480d08020141c18444c489140f00d600c820381d45407003000d0f0901d038400203003006094000981088808525941626a0106c50001d80c0b8022035524940150752010b501c0c0703050301220040c1d8450550902001b14846502105135820310410a903000755440b075001800a4000e41c1c1030b103c4140458100f80a01c4c1420000d00c080c40101208224059142401c840c040541541186000f909103089080000001b0012602100f501d080340e18107040300607245a102010341409980099116043c51800c1070150000034181c0324182d4400e0119040d0341c03030540364840562001c030110b00c00c1080c01c041e40d0100f07210030341403284258060920600761a00c002c0654842d40c1045003003c50420502841c5c1c0d48104600340c981d440441d010840c4034813428a001c4965804501d494607100048003117010b001960f03c150305640442c0b0000010705103000d0858115401101d10001103030550001c0382000c036114103100400c0a0000344698108051114180540e400780e004071810352001c038019401e00c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 716559262 1250 716558012 716558023
    0x102101b09170c040f1e0905210f03040f020612070207140105070210170103121707050304170912060901050a0c050d090201300506190e06030109060608030c 69
    0xc0000d0103812607030702c040030b85880b4104001001c1c8510703528030314852221402e400c00e080c00302d804880c841c10040f54148a0018003c0284221070500414200610909180c0703d00c0c0c03846100d10315854240800c2070001c2800b0361015200b034035001c2c403202074000180c0c0d403840241010041d5086020b403e05284601900c1d08134660419007125041c00301803480d45c2d9210050b164140e80407940b40c1c03031114580409407107540640114a100c0c032045030011080c4050300c08080d541501c560380d80c1300c1000460b4819229000240c0c0c40c2d0f0300054081000c5408a41000d414001d80d48400221a00c1c001d0700343c0005890b00059400d1442d5030708090b04110500c0d20030b2048940c0420002c0c800d0120b141c81c020000c2c010302c60441c0018010746d0b1501c40b03c0669105400c403200080040120007511034000880895186900d400e5020380c0382490b0005d00c003810b14a000d024041000c003040e0b481a0f050a0301c580c6400001420550199a108440b0022944600598000342040009195039a80c24800541080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 716560512 1250 716559262 716559269
    0x60a1512050708161409030706020714010f050405060d060b0c10050c0c1e030708040b04050f01030b1003020702120a0b010305060106030c02150a02070606031b120f020d020102101b09 80
    0x20f040c0402020200d4020010801502d510300360203c0c110a41c41500340340900d007603d64040c8a401c1c004902c1c0e036000103154007500c6681244d6100e00781124011280c08081c102e0801c009802070104105500307101b03000d800106280c54012960355160010400c031608100924852070744814441000c80c0a1442240d4000c03c20b516981c1c980f0783c280812503034071a580503d00c5c0742c03142e0078040829010300034806e440d00d042e4007040031035170380c1c0e038a1000e0a5241c1050003000d202d526060b0000036950f000344580c1100340c1001c2c20000c0c4681c0505001e40c020b4008007010790f04035010820b24401000184051941180700d180c11841e0795045050040c035102058001c00300345850001002c17255a000501c8641080c00d0800800e038661f00d44d5001c4020f03000e0003200808880c2404404070030842c2902c0390001007d542140400103031b548441c009840381c1e0760000079203402c05480c8120003508000850041c81c0d0300600444983d90090707402c2004403610540c00d039041101a4030860001503000700183c009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 716561762 1250 716560512 716560517
    0xd0908090f0604030b2d160f020102160303050a02071a010f05060f04030611121006110a020f0907110303090a120809060f091c0507061407050a0503060a15120507 71
    0x406095030b0750408074880c0945100840d02c0580000400e02d00b01b5421100c40003000355003620f042c14641400030352000401c1c091004a2001c1000c0c84140e44140f0941b80380e100741601031020403400b91001d40040002820000240d9000c100f0500840d40318034881002034078408482c180c85d80740c0400c03015142c0706a0462885400c003041800640700b0300805607010340760030130740000c2c0c0c441c581700300545248141e060494918030b41070100554000100312501c00ca8445881325020034441d11401074417a841c0007402540903800c045440240c5c200f00002a52009003404c1084006907604140780ca950811203150a4540c000080304040120580c0c40600c80fa0b01402c00082c0c0342403680c0025100e600003402c9072905003a082c006810140e040042c1054440010070040019180c0e8400a15980c4444415106203050596a203504188800224440e10481e40d540b41001c451942c0ac035055070020f801d50340c0c080d9156001080c900e48000c0b0081c00c03a5107907114401000c0700d0203044001d03a000208190207 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 716563012 1250 716561762 716561767
    0x3050423060423040c020102030601021c051c0b041422020a061d1c020a0b041505130305010f0c030b030c0907050a2a05070906050a050103110d0908090f06 68
    0x11607116002075030b00351100a803200142014000d020808400c0061005500c94100120500a1074066009500480083c1c4c02c3e16842c282c0a02c6e519010042210000d0000c0c100b001302c4601141c1802d940c0780501c44501340850781408004c001000d641c10b4544000400009105000030301c0c49041a00800400751805030403c00d84030340005428180510a420900a07200e9241c00e5085680040624401d0010f1041820300321180c00810000b21001040b40a03000200d0041100c3e054001610110b51394011452080b0308202c1040302c060b081146403802d59056030b0004000218203004040180007000b40000c1c0c3c041c03003000000c060b603002902d81c502035044204c5001c0c4640352019803503404015410308503591030310610220b440e040000c448690b40d070300d07641c001c0e0003c01e6035801c43d0311420300484c116903044c0d03112440002101c40c01e120301903110203a46010446035003e03420580c80c6103120702100d4280403807050048c00740c4016680c201c03000e0900143c0880c0d14a00b040410340c4800c0180c50290 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 716564262 1250 716563012 716563079
    0x912060a0c1220031f090c14030c07110a0906090f0c1b020915060309012a0801060e01140a18151205060d05030d14060906010c150204080109030504 65
    0x1003450050f0303e8076944100740000010801d400204000c0703030000c0c0302c4e00801c0c0315982e5862030300000d20484550b100060b1003d40c80761582e00b00601520301900c0e04041d142d00d098865614143c45070b100c00000b0b604a0810900068503545c103116000050588043c0420301408a03d840300840c1c0203d07442070107103d00140c614822168490b190f04299038180e40d4010181c440e9040192001c1140700e096030b01a40c00000c102030a001174101d04c1c10340c80c951244500800d110351607c00700036507094007030002901c9200100030741e078841e921810860b10107051100c3e5504890610807119848030040b42c010440e1240c4d03580200c0c01a0003884001d00c0d51010814450f14150307001421254441c00145e074a54035003000c500340356501404444c41c664000c0440f55602c0307000081101420310340c42d0003888203855500041c2103040807000c1c14881c0030169100d10407600c096030f4000245d0740820001003000c0d802c2c0000705840d076091148442c0c190081d00c03950b03202c501d000400d400398156442c0501c03407040c420a088 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 716565512 1250 716564262 716564291
    0x1b060305070903151a0d06060306050105090f0a020313140a030206100b1803030c0715080f070512040c0e070918020f0a0f020f01140105190513020912060a0c12 70
    0x9a50744c00399640c0400c680c031111035600103800e0050500c40c1d104081000d4003080103150750006040380d2081d581809160b9035001004142401203840c000743e8407400001030000900341d4002d6510280c4045c01c00c64210b29511038806500d10b02a00c4005a485168188103140c0c042110a504c840740c423002034880c030f0030148026500d000340541009118003501850b0034585e41032061301d00c10040c000440c0c0200781d449a40100819410b00c1c400c020404400200f1290070346040d0043c8a85020b80300c440c80d0880c2c81c20f00e4052481c1c0204160303880d403001c0d00c2c082009058080024003844055440c85151420001d8030344240b100256942100392040011350032030140e0200ba6140d211443c00e10b803c0d422a000401e07400c0a10301d039044031040d441e12585421110402a8190603640c003035650003040c618124400c09020000d001d2541e0045035a020b180f0010740300c1e00103101c1901e02802126a1070070304449545004000c0d10b084054039220300c1c1182c901d40d400545142406110107003030280c0f14520450 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 716566762 1250 716565512 716565533
    0x1a040b03071401090506030403031b02120f070f0203070b030601261308070c0806010906060c03020c27250219120e120115050a030b0604090c031b060305070903 70
    0x2c5480100000345000101c0e8000c111500003044003400c41c1d642c1786882d00d0014000c005412820310085002c90009131500c2c80013510515407038213400c5061a010011076074641e00c0c1c11001c400c0352142800303d403020041c0c80912080004100300c4003c56101d090500000d864028400c04010b201241c4000b01002d0b400501206600150141e403001034600745410010664410001c001d842c0343c1d8046800220031500180e0103040b12002c1204011454445004643e4140c800c030f8041d0060b441507000c201c888c034102c03510140d8104825800540300030100c0c150241c500b421107404403021075002a408084040e0349061094090600c05010b408040f14607810b514a240600941aa40700e20006402e480c02900d41d00d840e0400203180124100954140d075018001424440307070010f80444e8000b5440c00c01403004415030342e110b50501025500d290070303c001000201c400303927403402c4a04000408100041d110b0401d40c500141080d1900b414a40f000e41502e402400f4901001021401040842c040418 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 716568012 1250 716566762 716566769
    0x61508040b01060516021003024605191101111806040e0f09190503030a0e060c0f070503070c06081f0614031810090507090605030d080907030804091a040b0307 70
    0x4480d0b05c4045640710460090054107580740f0f820700310340c5084030740741910a40388242500020854508ac9601807022909500d1441c2d24004284c050003181607c0c07200040000a42c146454080085d00c90400c440782903540b000300340340f80003900207907034080e4170300410400356201340c00d481d2645030030302c0c00561400c0c1c0c3d20020b203221b03181168000801e00e504414002e4985620b650440114502407a00f00551243d2081d16014042880c05e022058000004100ca80c452081104418100f00c5134103030500d501d50009070111207502082040340c0001e00c0c041031410190071a41d07514030080c6402400c40c1e01d6501d000c4241d1f8540b0100160400041d5400b03200c081c1190102c135062901d03a25003005403030fa240000c00b0031034154011a850181c41054991020340e8481c000d004850b101c41d621070b421011602c0c14007036203804d03802c03a071b0540c20924051402903410800403001c0b1840141d80f174465400f0b9402c84e400500d6020740f109050f1200c21500407130300416840444041081c0718428002954a024520 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 716569262 1250 716568012 716568019
    0x140606040806010308070f0506072a0b01060e0103061d011701090221100e010b03150f010312050c0303070915021f0f0f02031305010510060f050904061508040b0106051602 75
    0x1608100b0003001c070b5135001f603c50f032102c100d0b4031605000c00060304030f4440a0300703039090030000b905060303415810584210402e034100900705000d90824204a03079881104040c1c03814583c0345d8070b0010340b512028070050704190b15080602e0040d4100300c40c520800c0412021501c0c1c0780c2c10b0822039800341c0d5035a580d907034102d0b510081411420703551078092400c0c100e44031381c0e060340c680c80d02c4a04403180f041900000404c110480545202000c403200e03800801c0c1056862019030928003005000080c1c0d0301d085e14a04486c1d90a0031070802d00580215417540e44216100c0c000a0f403614803c00c07003401800c2c2c00c440c1040c1203001400704c100360350081014841141083c4101c00307840c3d02040c01084a40d070300c40481344092160a542d03a10b080d0180300c01500c0300c0c503c200d4941d032901c000640b08651801c0c04c0d200b40d0300242c0c1c4110300c0555080c400c81d081d030400303800154007aa03501000a5050891030302c80c0c0d014410740e101c03038020f80703420b040003500c021050b4000e03010300604206448140344c0d41c00030b181c1001c4e07045 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 716570512 1250 716569262 716569267
    0xc0e07050d0f0f15030213020a0e04091b14130c1b02011e08060910050d060f060b0a110f060702030406110a1e060b010309021305070e090a140606040806010308 70
    0x1da0312001c0d05802c0d103c11030042c0f41c83c1c0d400c00101200d8450500752030080c0d81031590261a5a0150100d1140c031065200040d808000c00c0300a203401d03007010124a000300d600980003a010382c2c03c48040082c40e4002088a614000741e601b4604002c01d103607101101e006010000e0329880c3c50040e1060309c918960010030141c0c090703c0707404c40e80200304000421001c0c0100303240041807044080c00001c002c1d580c0c1d611560f6408002044804081c0c180e41c00d603a00642019a40d0102d0703554a80a0710f400d0340220307003c60f114440440d403003140d00f01609881201da03803001840e01c08500c0007414401d001c0c04054840d00321008014090307030004100c0d000c591183c42d101c5072259401d41d91501305001008003c141924104d41c601c0c041403a1081c3c0381001e40a07900070030400c0c03070001c01036040351030781d0740025013040e551031071400686819485940e00c03010a05103074000070140b03000100054811240f80e407605aaa001b0940b04a100081a0381e000d501a1791441c038040c00d228016a42c0caa0500c0011312400c0300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 716571762 1250 716570512 716570531
    0x6270c0a0608090106091b0e09040f020111010e010504030815030606060405060a0e0a0f0e2802030403020c0405040c080f0313140307090204141c02150a1107120c0e07050d 75
    0x2d51044c001440045801c10204004403282c10700c4d46441c4180e00c0008e04107020302d2085140640d00c00340207503032020141045850580c01511110040039032500655a02c00c10710b40d940d031082c002c040c4220b10a90b1010460301d0304456413100c811003003640c14084e40c4420304102c0b00ea1514030071036054901c2207402c9600d520450200721491500d1030309040d04105e404200050a59050711507809031a02103112806980d2aa0319a070700d00610303199a20980b0b03074808064003840c08561300a64015001b481038403280c0c01d809000c41c040c0c440544003110124500345c0100400d04d400c0c00300320504000c40028518000000400202c06841030081c030742000c00f007603040c415945d020044040108078444081d501c99a54090b02d014542044400b03034040c651403c02c074101100003100070102d01da4010021550f0b045103a11803080c5404c01803141c810b21904d03400540441e01e08011074802041c0421513420f02002e1440c0c00ea034903400503801900034080701000c0c008055000015124005804000000c0d00607e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 716573012 1250 716571762 716571781
    0x6090e13031404081c08091b010309030302072306010530010605100503010e100b0a030e01060504020c0a020f01050921120c0d02010b012c04060806270c0a0608 70
    0x41303034000c1003240304d1602a0b4800c000c440c5a02e00e81c424054445103038903618424400d07218050301004510395503180b02012442d601036440728403150f02a00e07005051252542e146002c015050615200103c0315625155180408002c03c6024000c183d40301020101d8020384800f2000d030018282e03c0c03085482640c1484007a0944c40705000b464000c00041070101e40c00405441d50303000303000c1c060b00c41860200043c10310003040c403080111072b40800c0c903e10308100184101d00070b0400005070241e65403260340002c2c05503914000b070196960810090f140f60062441042807011041401c907041c40400d01181c60160790f40400180440c0b90403054241001840c5911400c200c10001048120310001c503070800c42d080c001600b00b0622603d030300204441607154005641031544d280040704405a05503100368000070b41c5481005000000e000440c130709131901c811600f424001c81d2007008082d00c8120105042d54007411950002e05404084c1c190088000c0c081440256140110300500c85a2008200c8900c1c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 716574262 1250 716573012 716573017
    0x100c03200906070b011d150a0e09010b030106090e01061e0e04030309020402070b060909070323010603050a0f0203060a0e0a0605060609100f200309210f030406090e130314 75
    0x44e485503004c01203684603124500c0290800501508040c46c0c40005480100c41d446403808501004295003469460141c03281158000244110800d548410648405413000d028800281138021008031301c42c0000d10110742110310a901841c040c01c0b070f03482d141c110b060060141030240c40000f00039049582d9075003000e070090302c603003900290024070002d8180288903054801d40d0040d00c0880d114100c2e5110540040e42c1c40d2000d000c0030b40003450045010301d8141401a00c9802c0b203042d0400031030300c10782c0da864540c141428400192001c01c070600b0798000b1032405001090348075003803660400072005000c000e150f6501517027100501c8240c0d101c1c0420100e03680c0c081618080c00c4000e11017004d04903511385c0148420071a0486402207810121894110700101c8855850103004500841c146800c440401c4001c1d00130b95450003450301c154280c0e441e803a20034071044211402c0c48000b150f849140c01c0b0000d05032201948041c0c2002800400d0000020043d0b06042259030186002c841d10b800402400340c552 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 716575512 1250 716574262 716574277
    0x1230a0f0b1e060c06040f02040609020a0e0f030f1c0801060c0510051b071101110c0112110f0a032c0a021e031902120a02033a02100c03200906 63
    0x70b00c02c5c01e0030001040150314011142900c2a00e05100e0309540d018640182d00410b4960808900040d142591500301607105c842c4191004088404090102c28454141020504414802955106c60b86225500300459a005282c0e070302d440c051310741c141d4036030313649800445801d24425511240805e0300517064002e85405030101c2d9000b644d652400345022119044080c1e480b5010076064400300307040e1500400c8a101400c0c0c1a180c6007030b030185e2840c0400c010f1001c150102081803040c00341c440908000800303017400d030300942c07400590507a0b840303c0e0b103014841a09072100e10107a060160343c0d400c10003013101410301d0760690b12004030224042c10f1028603000da5050300d406225440101402404408108480a000303456410045c182c2080035619001140e60294040e440f801c8150040380b001caa40710300417101c4405a52840080b0b2940030441c41c41040341100580c002181c0f4020032009100360901c0a103d801c0401007130f0101809101c0445030504007000780320001c20302105079194142102c041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 716576762 1250 716575512 716575537
    0x50603010b0a0212311205071719080a0908010f06060e18220209100e180606040e010e01020a022103010812090301230a0f0b1e06 57
    0x120340e15000c0101503a000320030b00e80018851201ca1503880c440040803500d20003040701317480104a50014555420041c0e241c0c4600c4890802640003036501020310710904450720460140c041d040c0b41c240e101801d2140420120000d0f00007407465080c048440c3d03c0707001c0040e8008032a47d00d07501d034071700140c0366a526940720700410350805040280c6001190f10510030f9030966252a81070317914420921030311289080f901c1000002139808200c2400035500817004941e504640403400d00496404038201e81401da800b182107500e060000e0100c460080b00b00c0d44c3c8106540859090f0080b04044c080e55128091702003400b6a59942c0b810300307090820340013441908680700007599105013807003000f940c503480030010804603a0a4030510404c122080101c9040f00c1078407001b001645101e182a0119600543d4032540c10341da54a0f6000950890b0642e005c0c000f0340f40c250704802458400301503403c2d1141c2e1017070f00004515007030101c09503a8400082011000802c40000100602940400c01d144200304032000c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 716578012 1250 716576762 716576767
    0xd05300403020d02100911010503061908061009050f040b091002030c040f0b120f06120109051036050a05100903020d0305010503060a051906090902031b010f0f090506 73
    0x5042e00012a02031800032030742160828901003a00104030794020000a01c5014400144140e030b6204002554000000510000758040414004490080c40d0b600c071f00e00d590045400c002d44084404145d900626800e90280854030340349401e120b445400820040620042e040404d0103000c0410003822075003c46081190740c1e040c140d610380090b400c41d10a40e5207424540102140360664601511080c080900012031103440f85141c04c0c2c142400208002e0308060b2501281000d600e090041040e0907020342d003d0000303078a601440c0000d446002000034030302e076000444030440682c101300020135002408982e020041107460a2410302c003212101428500c40c2c0e225011000425a100e08002c41c030a07001c03200c2c5540340510a0b41611000d1003030f2036254010100190504a8940006900170400c560a442e0300701041854001c0301c1e03040d00030200701c650301c0b00a0f00460a042103140c2c1c10041c000c10054102c001d040c00200040c8903042498200813006420540460062604d00040c0034000e00340d94 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 716579262 1250 716578012 716578021
    0x50d0509071214010c05090109090b01021f05040611091c02031606111917180a080a0c090504020d081818090d170115051c02090907020d0530 62
    0x14810019161a900da528010a85d10518054411100030f0041070711604007691401e800708006040743d00d002410f6001d01001d03103644110342d80070b0200003409020001003505041c101072045500c54140c800c00d103941000280c41aa0703a10182c0e0341b1200c601c130800624803140e031012904040304d006191500d00400040800d41e1741d0000b44031034a5001032000c40701540c1c0c881c0c0c2c103080668a0401e0140000c4010825140641d5a0100824207080d40e00c14201d80b03290400e02195030304055a200c20130580200c5400030400c02c4e8a003100e0001c0c03082101c2401141000e030001080b42c801228000c15a040000f1442d1a0000384564901d03487c00040c031184041002e0042d0b42e000c15811203e004880c091000c115a90710b026014100440c107000c000300c00030342c2c01c0007801d421035000394210000f4003100303210340691141031686508040c0380442c00075807a07425403005c0c840c9403040a00108155000910101c101590100944004404a40e05c0c50060540b540004c981e501030228518005d000c424100f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 716580512 1250 716579262 716579273
    0x516111c051c2003062b120822021008040c0906301101050903031c0c020f030f030a1503080c010506190f09110f0313030306050405010501050d05090712 67
    0x40b40c44895800300b0145400440040070f40c07100300c41840d480818030b503840c104c0e600d1140e0741602825044501050040c00d03501c9800caa21200b02c3c6083c00030704000b0400c200c201c0c82c0e06003003110b0300608440152a003640e900040c400b000100142007001646800141803000340c10b05680108401c03401040040e8071820141229902e400c0030100c84101052104bd462400b20390704010300360840c00381e90103070a01e00300444456103c41c0c1c04941c184014040d001848240c41c8080d070204449a4000400c1d60300c1c440b01031704200c1c203c03c0118844e081407017000742e0118048110390b070180d0240380c0081d88120030701c060200c12900340c0000d40049404520781203d00c2055104c035000e4001241d0346040c1502062030400100460b0140b4840d10b64100420002c0300c103640c1041c08103101d0381003241d040c0b03555040c50101d10f80084512180ea044141256400e042c0c1500c140d8001d4002503a0a00c101d41c14040040d000b482007003505c015007130307481e0006141141e09100b0800541203844032a01c01020301d0a02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 716581762 1250 716580512 716580521
    0x803070207051c02010e1c060e120c1b01111e01020d050a0209090109050702210702090f01030611091f0e0402040b0408010e06060d08030a09020d060516111c051c 71
    0x22408241606103491b8189010304800c400b840ca2020110340305003680c2d440001624061045a03400d1142442004103401c41201915003c070340c040080222281c51020402c40c0e040c0020f1690621000c030044011013023020402580c0f00001c0c85401c5141040d042010b80203110703001d9101c141c1e41c42c01e024011b190580760014140700c0b100b264005101e036201c2d40309404403202034071074001683c0008860031460700480760302024981d00e0421541809a1900450541c120880d00f807194101c0040c018810840d1a10811004104d13070700015003850b45400124001d454600c0c40d0039070201c01903030581e4445c1d1040c00c1d9144854405801551100d903a401890250780103070160311141d5090012000501000081c21449017a000b003500f1144182d40d264003089a001a2100100701d44600035040035880b25484890b20b81d00c220750004280c640948080c50601451002c401000700940303402c00c044100141c2c05104845c10415041606000101034803103101300c18a81280aa040c0301410039840035511 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 716583012 1250 716581762 716581819
    0x90904030302181f0c020d050712150902030a030e03010f0c050307030c03050907060503251e0c050c040509010b0d05010c1803030516112d01090e04080307020705 71
    0x103a0b00041e4404010000380e401e4504c0d2101d4400802c01c410f030b2100e84181d41910409001400d2607014400f02d4803460308000c02600068804203007080c540b4200984001010494503044074200881c00440d0700203501d0321001440035041000c00d000084040d0360a501c0790b24451a0010704000e4808243c801034a5a041268240040b07407400781c564004c80d000340600c6108482d01c8016115042c2420303000d96a80c2c2014084151840d540a1525100d4146048543d400310031a21740710b000c1e100c0f14202100d452079110b00321003000030034007450002587c00505030042038401c4801007820743c3ca81001d00c2c010448240c840764000030000e40a01800070641c00b120655009a84041180c0e104a003c0280b407880c3e44030050000d00e04110382081040b07844401d03043c262103883c1001c0f4160300d000c0040c0040005c03800c01128001401e8444815010f1441303d1600c4040a00b01000c009181c1140e41070504001400070700004800400540c4080c82809688060503004111485048982c5400000380000f0310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 716584262 1250 716583012 716583037
    0x2a09040e0d170711060a09030905090a090c050d44044e02040f0510050a120318150909060603020f0706090201020c060c030901091d1b090904030302 65
    0x1010401441c894200708420031044001440705031240070f0600001c0c104043c0230b60401c140900040b8a40d038030b0304203040c082e03441c100e00410540310900344072004031100d40c000342c40380914040407000a0340c940000002d00401000c0309441c1c01042e4201d68050011041440c48028004081341c1c0071000780b000f500aa80b00e05240e035019102d1210407002e0a0703240c10456102c054510003c030050304640b200c0b0030348031020300041d0b807080c03280f40d002c01c0540c0c510540714010641c0741c0b800c001501c554201150004c200456804000c180f43c140070100003481c40101600b0029160070014000c201104140c004058030080b09404020b030600c01030282c0c10501420301c02e00d00346080004c10a11034003c0c4c07074a24520004071841c107041691440000c2440708022410341c0600500d0070007560740c80000d080000c1890000d181e0b42d13040600010020311403600000c900e0210405071442c8103042054040d4031030300c3c0345100008030b40f040310042c02c1070080a52881c0d10140840411040581c5900904180f480f0761 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 716585512 1250 716584262 716584307
    0xe1f0f0902220e01150c060507093305160b0f0f0702010b0303040504050703140709080d08040b0604020309250e0708040506040b13292a09040e0d 64
    0x2c0751451240180e500c03078110740400790340050245402000032500101c02c24240041e81c80840c4c0c1d19841520704c11503d54012507442d940400c1080c0481025900c440c1d481c40c51180d40c0e0800000040700704010780340500030820089803864203003a0950441d52041e4008403122910b140541522900b10401c4130b40740e04008001c40450002c1d80140105070164000030091424282020309101c01050005d14120406880303903002c2c002e0350061406240140fa042d40c901d0a100d040001c0c2515080c910700c200410400c54504000125090790381c0103400c200c0c00c030b601580c0ca80318400c0461400000c0200113880740d60404400c0f1100e144081c4036012504d08035030480750b5a9070900f00341d4000328200c81c06000358008200241c002002143c0300c039441904a0202c030704000c0c183d2039498a009070300d250300d000d11032210000400c5c2c42e481c0c40b801e40c0c01030f10f40e0b85c440d6014041051040c614005160f042a401c680460703e00c0b0641d030f42d50002d43c0c9400004080b5554441e0406009003028040162980240b110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 716586762 1250 716585512 716585557
    0x804050111060f0402130216050a12050a020712030e1003060e0f06030303070c030201150f080c0a2402030909090a0308061c020f0303130602030408060a02040e1f0f0902 74
    0x1c14118800c420740c200054032039440390244501c03402001c01900c486c950821044644401880616641c2d500a00080100c12094688040400c009191810034002c1c00d000701c8101c154005156015605452824400c495151405503417000024501c00d40c05100171b0000c2c2c240541c03640c419030481d1101401380300b031a112503510f41b85800c01a1031068064204000090b2024000c824402c1c4043c403e10000500940b18894000c3d180702d02d0300007194240c1e0070001006064020411030342009022140320b07089924001c3c841021701d0748101a11003048080082ca40c40a00074010b980e44050301500031042d6162808070b1740d032280552001200440d101d980440d4840c140300d0903110602c180c00254454007071080c0c080200d002c444844055061104004c290350b003001d5840d190005010381c0d001161524240b00605003418401444d68441e40d1050208110307180d820340d051904440c1d4400e0003100845030341c80031000c0d6201600429031040f03044000060a4107160300400318001c051450b248900d04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 716588012 1250 716586762 716586797
    0x251809020a08161407080702030708011109040e070605030402100e061315031104050d050133080c01020a060507032009041512170c101401080303040b012303060408040501 75
    0x5190302c0503a0078010505c490000506550300510115000504503007041c0d940d00d03c040c0c02c0d14490404030070072642c0407405402500301801011f43e080781c040c01070070071b6030706100005101d4040108040c0c42282c1c640a1210380c1c90040604516030100540010f030358001048400031441d40c40c0c4900f03c6c2c1c94a0010040e00564030034480d50490840482e0b00c10300c4d00707250404004002c4114482511155039912041e0180d54840045c1040c0100c0a11111103104e28880d0b0b500090196900c4101da0350444404103100d40e82c0400da00c443c50350700400000302ea40712042c2c00c030000c144603010800030f18500e413071180750b245c200c0010b400c004804840900000d101070200b0118420a44103c07003030809641c0c0c5150000e000442c0034050741020310710f064200080f4030041480d20084d01c40b00c084803559494020350040300f060032030340075080480095256007000d0760703120318400052080a56107860300c0030101402c1c4001005d00540e120060440d200e5080905040e40c01e50b003e4403c640c041220700c2c2c3c22008024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 716589262 1250 716588012 716588027
    0x2092d0c12010b030f0403201912140901030903091706090610030f02060708090d0605010602121815040f0e10080f070b0306010c02040c030b09251809020a0816 70
    0x3c65050020b401c680f80c5540035100940c1c14070008c20390821107806040702400400603124480b04642c00b2204196260501c0030610000c00010f0b410498003030a1086030401e820100d40300e0072420b01c2c0024200801e03007400c484114040d00011048c0c000f41c103001d0802c0e0000190240140c41c0a019600e05072244400006c40103001d1200400011848001001500e0900050040207000d41c2c012464003c41e60001607400428401c120749941d5a8001804116810840c1f24101400b031184940f0b0000c0d10b03200c3c510b00d0104030a41610611644400d08400203207541610024144105032122040c1c40b038410b50800c2600b00c1d9140750715030a185d40003450340350004a160f100c6a030307240030381001d40c14500a018203600090503181403000788804540141c4030f603c070b1101600001c1da030000d01802c03460b003003017807900c406000d0313803a2220702a0002e840d00d203107801c000501c0740c500e003098880d48480c03184071b40c1c2c450002d5200c0f5840340e20108a8440c1c0c5034100004911642801811241101c0c0c0c5000645925 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 716590512 1250 716589262 716589271
    0x71d1201021c1a04090c0b0f04030c06081902090f090a0b040b06040620010902030a110102010c0806150702030c190e0903130513182306010302092d0c12010b03 70
    0x10600759580c520b007482d174086018180200c5901c5007a6454a002c0f84066128111604604100050420a000041100c0000390245242c009403500301420080c1c03001c1c00080d030b1281c0c0a03500081084141e0f07100c13561003000f00005810b081c42454030403c21401001011541406203017403032281003035890b01c03908542c00d0300c034180c403201c01520f16100e0151840918030303180346041d035035102024050b907001c202c04200e041c4140c0c0c0402d0340b0a4107800081c00e40d03018406c84814006400c0c14844190758101900201031000e0400640f1480c1e10700000349401040d4081c1604100c1d00304503010880a005030780b0080d102d00018480c0c003a00ca4004441d600d00c10105803418070041c1690a100502e04041ca0030042c480d440c00109101e004520440440100b2041c102d440801c0d07001c03415841180a402c421344166004060000c562554002c10034030704000703000140c0101042c01d0344c8180c1b2209580041d900640b0b20a50549141c8411990401c1e40038600c2c2c80400c4180c0c400000c0c05242400440748113 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 716591762 1250 716590512 716590541
    0xc161a0903060a050403020a080715112701120912020c0618100c02130b040c0e0114031803040308030403020118051509031e09040e0d0206071d1201021c 67
    0x103c0c0e07a003140304002408054001c5045000b00406100400e0f8000c01a1840314001c850030450281d0000b0b00310101c0f200e070584010902000e00010540c0210310505051040c0f1101c0041f03040c01112004840c1521003440030300c0a545046691000c2c000410500202c0301419021100040360132020841c960094505101d401e111200390320901b400c140c8002182c408142c1060f00d9180700603800100c0501520b00c2100100303945031a0b00705145494000c8580280440c100f441c082414400002c03c4ad540400704800b0344040000415254820780c4402403801c0c2d001d900340c98175140c0ba464003107040d500c252b9050780158200089801c214615600d08444141d21130300401001d418801d890b20a0540205800581e00040c030892800c091501070b044040518014481d9890282d07a080208540c400449602d1960020840b0100c81d03800041c210740204290901202407082c60496039078107280f017420290084400041c02a20041c1500600b240110b48400c00281120780c03102281216030b850b00c0c0c03030b41 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 716593012 1250 716591762 716591773
    0x602071a070b0c3604140123030307060603140705060310150216080a0b1b0f160c0608060423071b050607020a03020f070803030103060b0301020c161a0903 68
    0x43c000c08034020a1802a2441e0480c551040c181c100c0340400110440340000e0040a1a004050f180070321030000002c1d018000c1256950501880d038000c20588400c0075020302c60700300c40b00d000f56820004d84c0c1003281d0111060242944902d40034000840c01804c0414a00c1540000305945c0b900c01c3c140d030701c151641c1c1d40c0d081e081882d00c1015103003203040a08003000e500035998010f01e032402a001c04005003030014014462413005203807004402c0c00007004c8408448280d81c5e104ea00040c400300325000084018541da850384544d174505004001003070401017403000c4940c0000740c01034020304020705c81c41b23046404006407040ca00304503040003e100010800402000c2c00900c2083c080c1140c00502021044a90200d8060b99070b03107840c0100680c0d42c0c6001d680900103000402d40d040100745140317001000545246494940b03020381c1e134001800024440781c2c62f89144c80498800b50b050f10b007013005d0309003102c505ca101d00c1e0301c480c00071425000e12400403106001118085d0180b1044401c007030720280c014103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 716594262 1250 716593012 716593021
    0x14071b0308130803160602090d140304080c030102071a10150f0306081c12091b051207080601030b0a09050607110d0309020f04050a0e120307090906060f12150602071a070b 75
    0x3c6c02940444520399024002440c6c44006c50502419040f030f190300c81004554460401703a8840c0b03001c0c1881c1800381310740e00420950b4002144000071229890440000c841c0c2c54854020078a40311005401150342c07409411444400c169020062170400081390720300300305090f2215162500c0718a68100030b0074138603110b825608902d03c1248000c1005081d42c000180080301c0380d560b0701e8400c08245039072018201d4640d050000345404c044081381528000e0081840c40d281c4821107454210510000d002d02e50250002149125960081c0300c049034090281e4100e03142ca10030280c440c0d00c0104080c200b038400d2260300c2e4002c2d4001e10030380d20081c2d00180412a0183d07154100005440024000607025031920121850344500b00030a110f1448242c40c0d15071245000702c07008109507150b0307101c000704905041081149a400401900d000c03012440d040c1c0700415105c4502010300b00380e0648080130507041c80001800c55010985c0025a0815050043c40c82c22031a0309019a001e02000501082162000b09 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 716595512 1250 716594262 716594273
    0x3020301030b0601090e0718120c09060501050324060904020a02010e060708011a09040b0901150809010501030206040308030601092102130c021905280203010b04050714071b030813080316 82
    0x444000a2300101030200380d440c0c850400200320074140464003d03a00d00348c1440026503034000e140250600b07180007401e601d0300d178000003000040c2d2070030100402a0040d0036161905c42000300c0715541000b0740300b90f6a405280000074020503130f45101c45118014280440c2c5503e00c0341c60894101c0f601c0c0700c44402d2905a0f201703a403116030311899400e64400e07601e104032001d030b480c1d14102da8000d000069524080c00140c0c04040e0451b50000c14a00190345001c00510040e9203010665040e2900a0045612036841d4001030310003c0c0d6039001542c1c1031904403078540d1004158410f20b14028402d03907078500c01d101180c1c8101c0a540001e8031540c0546c2001c0b0b5a8440306030560b0307200c01c4680c052800c484400c0080c40100c1072038100751541d15100001081a0801c3d03040c05d00494076414402d9608003d09d240c030560060001203807400035a14134100280010500109141124440000001c1580c082e540d030b240491842e800100b0a90038054556000202810b000c02910303000c0c644403170300d04004041d0380e585 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 716596762 1250 716595512 716595527
    0x1020d030e0319050c0f030c15040602072328020f01140a0305011a0c0a060209060d06080604260901080a11070312060902041a0c0114040303020301030b0601090e07 72
    0xa114140700a20203100c0c000c401c1510420000f11907190f080d41c820b1200b4aa40c00d0041003503901890b40e00070480c61710640c400090000307825602612141450300c0328681007010348a1000e000d400c40c030305000204480103445181d0882e500b0104221143c086180020050010f00d81ea0820031000044c500d050141c10804440041001305140541202100e80241d24664000340030060000381d0b0340e0b00503c80300c0b0702030b090700c040200845009401e0086c0009104e0740c5140b00c1070000d140c40d07008140325805440d500151280e04940b424140502070300c44001c6551a60102d80c2940c007901100504907010405247c1c1a098030b929001442c5021400c45c0159140c100103420685055541c41e46010361000400c09802c0d4580300341d40e8071035000c0c1c82c094000300382c0307005404c103c0f00103204000c104203030404040c00b0520f0700ea200e664541c5910429440718011320b5100c1601b210061190100410107600d0350080d0f058034880d402d071140548887d00110b81c2003111340170728907a80e125030021a034920b00030b441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 716598012 1250 716596762 716596781
    0x12071d15071a011d01050d0b130201050903010c05031e01030507030f0203030717210610110102070206040609090c050a12020d060f080d1b0c030215071e0b090c01020d03 74
    0xb594034a111005030031101000741d100b0319401c0c500b100071a041030015040640100011203d0010142c20713512090403c06018000d8440100064892000c40e4010300aa92a410009000301300761122070b01d0103082544100c1c0c07051000c11801001070010381da40340c004d40c1070760381080040c060242036544124540130912016a4944010700604002500c0c0c071800d1040944616003240d00c41d10b10120f403039028280141c400c21200c80f80c41c20090306032208210800342038054078007000f603107604102c0f0500a203d0040c0182d00503600145c04650103812560340401c80729084001c0200300d06049084030b070780c010324041800050700007031841c400403d02e80107403c80741201e590001e0f229070703603440382c00034002540c1c07040c0a260031803004c100c4a1500074200750a10f40d2001d40406400009a1311490704008a0000030300c40c00c56085500b20340b56024043d9a0465031160b1147c00000a04403424801261640b04030303000402c41c0001a5200b40c082004031004506800074408035503031100c240c024250009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 716599262 1250 716598012 716598023
    0xc0203040e0c0d111b0714060f0408101e06030308040b090c1e04060909020306360a06060524160204050406061a0309071505090612071d1507 62
    0x1050342c01070692442041070056400d070a0a036150369000d035103c80001e00301000b4a40f40c00101b8204407038101c00300c0030111030038116650341e070750360102803020a1030083d6002010306110710300a1440025041e031024800852411724129078101c82c245110a90741c1601000700005d40c0c04022900107800104016000000d0005903260031440d01c004c40c0c00482c2141c01048202100180d000c0759080620030b01d0080c1c18404024090203407540c001c0b035903a05024000400207401c0d090000040e00e881070a1110420000d02e49540354401a940740b55241c0e000001615100d02d40900041c080c64480000051080004048002c20307250102d03c5425402c0300308040c64405084140c000142c3c0d5a118042c07250b88601d6001440c04e007405500e00c0c0d00d800007040c0e048090410424819140c0c0f0000b201000c42e0764581c90420b074900e074020215554007903000350940007400440e40400c140908000360b48a5545590346010700e030001c9400c00c03003404102d1202904100302504a020740c4112900400c0f0150065 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 716600512 1250 716599262 716599267
    0x807030b09070309020406080d02120306010516030206011e26030c030a0c060e0a150e0a120201020d0b1c0308042307031a0606040e191b020609010c0203040e0c 70
    0x31004a4001c000031681e603000242c0e030383e01354001c61030030703100392009880d0070ba008001c0c20500d80c070f000e55940c83d0034031002c808140200016110ba88210100c498203504031102d4045640c1d903180181d501d04080c01603056000d15100b440720550601a040d8003140c14842d030441465020b55a2841c001c0e041d09180055400100103000c1c00c2d2001b08000c0c240d41c40717107a030f454504508609000c0c007101c65001c00b03510180c0022890b180450156050b03018280e28070040000c03d482ca040380c2c10304e040760340078000340030035000362080700f801d40c065002d080c02c4059540144022001e000c10002d000d21007515000d08030304005002c2d00407a1140000325401485000a003400c80e4100da806003849030455000383d40740e4040ca2060080000d01707000e04c5c03107012480038404901d0070b203c8000f9507280514042d0040c4030840e0000079040f07400d18181b015007103031012010040340d041120852010151098280c016200c1c01000c5102d2100500c1644c181524a41c0514209800c04480654190f0086c09111541a05 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 716601762 1250 716600512 716600531
    0x507030801270e0a03090f0b1b0705150a030f0605060d0903020c0901080313090908070f0f2a0f0305071502030d0e0304030c0501110a150207140a0b0c0a0906080703 72
    0x1a10900c411410a0f100402180c059403038001c001e400540c100442d8100d00030410084581c8034002d0760411482945450007400f140c2d6100c916201150307000c0c60344032000e4078410000362507100050036203c080341d40601140c1840d00d102c0b41665450710030380347c220b9420002d21070310003401e80c06a0041c41c0b281c8180c41c040c2d80300500180e0030310b00030780007141d1035080003600d00d40075861022024010409503400b802a100c55031940780e6240241140a070403c0300e548503000401c44940e02c070032501c4c0e500584c412400407202c440840c101491446030013080705400c1e40030500300c0c4c60700e02c030404907540700b40141a224100750081c500001520840c0c0c055200900c10f0b98601034945c0584002c0d06640c40045484038510300340480c1000407603000340d040c080004a81d2001c10800b09544856a8005010002d90050519010f00034403c501c00a418030504084191281a0104000780c0b9240a55641501c0b9100d0345611101445803a0515001c6100300b5010401c650042c4001d81c1d0084850030f0002e1010107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 716603012 1250 716601762 716601839
    0x40509040803060a1a07080f04031b030c0f03170a170106021b0603070203180a05120c03010e011404030f0c0212100606050a0e04050a060f0b03160507030801 69
    0x141903804503040c01e80070040203100e0400c2d030008002003828140340785601c00005000a00e6210302c850203401c9500000c2c480c01031402031b0b01214021a40030080b407440c510040b2441c80d00300c0b103501007222840070001000030170304590749210050303d0300040e8007050042100303804201d682c01002403000b44400d032103a00740601104041d00b8028501500030b8003490501d1481c1c2c1c150000098a0184101f0051051007140c0f41c3c0041981c041d41d00c014001b80812580c0d0b80050b6480c00268852039100e0f0000b401400301450109034050b000500340d0080c08540b40160a09080c0e4411000510560000100280100344a21141e1980407802d050001403080341d60003140400e0b4907055500d450b41d00203040c4a110140b2881800300400d8030340341481c101307070813404014803102d032401049100d9600d8001181540e00c0350342c80080244a000444040b4a40c0c42c2c1a00b2180e03001114a941010384145900c040a40102c0448280c01d071300d035440280c268286600341e14017480e20b440e085907807140c030500c1c031000700c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 716604262 1250 716603012 716603029
    0x50d0e0c18070305091b010302070c0504020a050a080108120f070c0914010303020c010206190c1b030306030b01351e0c0f0a030503120405210301140f090c0f0405 71
    0xc1c0508200d25034a401c0790083c00740d0780b025201820b160302214140e1181424111061402c10342441e0251b0341d0b070701c581041c8680d040765800240c0d00a100080d2401c51070340240042141c0c1390b05032203c2030a0781c4e0f07880c201c68032140208115228a0f001b0403403c901c400e1141c00a225540c030a410700c80540342c5a00161003187c07002010042c090050301c006105040e010010001c2e041424402061189021000b0780d070504621081c10200030b490315448004107000704483e04150407526042001d42616040040c041e025904c41a949030f0071140002c16101c1405945001d05601d00c0d8030380382640403171103006200e2008100c111205010743d00610f01c807080c40300407003c2d4414543c002488540d000b5410070501486001c1d0f80c81c40762110103010030014201009a500f004d885910131203807555141400d80c10201c41680b007490704d0900c07903c4452065441c001841c1a1013a1030780501000c40d40200b884030314480758500c0755100c40310303400041c0e0a103032050040c000500414049810240e0322030200d280308 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 716605512 1250 716604262 716604289
    0xf06050a0603140303160f03180b01140303030129040b1207030f02071e050a0b0115031505030c0904080904020d050117011401030b040309230411040501050d0e0c 71
    0x94441800b0028019120420440c01c44201e01075841c60404100c10040424800c8440d000c0c031031071551a84070a0300035071152000e0070701012885252425032402c15101c0c0401d000f0b0a480c10003a006001e2903040010a03241030314541c012292003589030034800c458400404502c4581020200000306204141c0005031a156820400d261003d00f40484080d0543c3c40030b020900d540c41c4113100003404250345100740306a40702040004000001c4a041c01030a1070449000580480d09140001070601d0084201011440c1d07959010440786540601880803014588515139066000c1304406a443c90100c65054215214459007840d05a020340814141d8006211500456507208010028070070301d901070b95040b9060070b00801c24401d480c2c0000030010700601010705043c1c400d00024080500a59914019085032070342c601181c1e60700c410981c228001c84903094021030030705440c80c603480681401e40301034a00585401e420311882e07210100052440c5ccd149a00030f842000042c0945445004826241 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 716606762 1250 716605512 716605531
    0xc0b280c02090c0306060405061809132109090b0a0807080109151104030f0f05030d0501051009260115031115030103020f0907020c1e15031506070f0605 67
    0xd414010809018002400541c00100c200104103150303a0b841304031303401d46100f11000d94071040d10310000506207000054268000350484203012140c800c0c2074486048a204101c0102000788120080c00041c0340019680c001c00d001c18018058800190014400c0a00190282424a5544d40381915000d1b035940540401d0750f640941e1814840f082c203d410682003050740034014201d541c1d100d41d00911135072001030544010395040500304a40752112802803600f14088030349580401e05140300602003031040c64810201000d9203c220350064183c0000c80d10800c0106107001040b40340300a046034140448030361ba55841c0040841490001041d901442c01013110071019045101404112000e0200c299007070281840104010390b00d00da40f42c0c9200005a0b9090384540328058241d01d01802602202d41c0071117012a44a810350300b1489803003060303008a039500788071b200d1010b07100810300c001e450445210107010a03001560070010000c041092080c4148111503815454440c2111015107001e0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 716608012 1250 716606762 716606777
    0xa1203020409060f0f0605091c210206070806040507090812090415080706030b060c0114150f01090509070c0c0f18020301050f040908190309020306090a0c0b28 70
    0x42d00c520681014142036034580c6a030380e040601c0800ca0200500c646400c0000c005070740c403455241c5090040081a140d401c1a039100e4051920311801e00c560f21002590900303210711000310902c0015258024646030f10750182540b141c40038071024107401403a840c01c0c480c244000092907402008071500140c0c582c40c04c0e68440440b082000243c1e00106510f4200e81500c0f44144114040800d031742080310b03440d042c00202d030310380b40c0081031060007501c160720880e520700340c104407a41641b0000030744914a151b120100e002e42200421843c44050b041c81d80c0010b1703c0d48814422800d00b0400140c000c0603d09082d1300071040c030760300c2140e0080c143d00a200301c200f40560410100009540896070580c0040c0d096045d076051402060a02c5c19030300c41039108903102d00340d00c018003004404031400140b003c6059208401c0c00350014018168020040380644144400119034000c0419841c9030694408141c682c5686807036102c46240d04807095400602112410050b80000c03018101c1131402e4240d140c010703 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 716609262 1250 716608012 716608019
    0x3010e0d02101a0102100510171c05041a07060e010e16050103090b1306240e090609030307120f060e18010606210f0c0e13090f0b090a12030204 63
    0x1090302c3d070b0010141d01c0d192249803414816a00401e090100c074104600008469a408800400050385070f400b0f9021081051401444c50f440410889401d84450f80e0f900c2071440886400c45a5209512941c00001c00c624140444000e03000c0003041c0da140129008103107646045540c130f085442050705068a58420f50b0b003080d0f184509101c0b403008040900301040080c4960700c0306080000001d00581e0210a404c01140420619a0142c40c60040c001209211b281100b4140b07900c0300e50600880403640b108100244800c640010102d1103481010061411500c42420545090240b40450011030391101d100c01460308961040c44020100e0480f2404681400700c0340b400074488400c0405170f03990400310305100340e5422000c0401050390541910741007910324940d2200800d417032803000b0249407c1400540c086070303100421000e90802218500e000d8080e10b0054001c50f0450100102513004440c8550045131084003141d0f030000000c41619010001d030303078444182c4561640c1c0140401d5001c81d003403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 716610512 1250 716609262 716609293
    0xf0606061b0309180f070c15113a09080d0915020c070312030212060114070c0b07030f02060415020714032205040b01050d02030406021b0304081c1d03010e0d02 70
    0x1103801c40c0842c100b4490201840e06c1d5160a4925540701c54185a01d030180c01c0501601c2700c0c100d544250b982c500713101e01d1142c1c500030202c0b494102c41c1e9004070b0407600940342c4107043c032510410395940d034042d0b20545841541c22801c00030342010403082d01e15040154010303032485428001000712486003030103882e0307250452a050801030000c1d20500105441800005001045440400e4200d0000d090001c59a10302c100001d07100c0c800c0e0f07500201500c0d90701c1c20024901c01d50801400c2d10a01c6600d80d00c08165a00300b04980d103403000c407400f501000c008000d03e6401c2e1050f40c01069901e0080701310610b4410066001d074a941e00968104074011802c0c0c440101064581c400040500b004440500605400000080c5940078441981d08080d5000001c5001c000d16581110305617507808112500000032803008644030307040f41c424a840c50003441c406411115401505100e0300005894001c4015195465036107401902c08840350036650b01d0b080e080082c4400c0281420440940c0e000307120001203030000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 716611762 1250 716610512 716610541
    0xb010305070e0105090703051512010603020307090e060a0c09030b01140906030303240604030f0b0717330a14040b03030301032d230f0606061b030918 66
    0x11880541400b0010f000c0d80e51800340c1039400c10310380d1a001c104c03a100c00903400d030035032401034600b82d20201c0c505609480310010340144007168001c41c2a245141ea548801006a0b0100300f03070b5090300d401100004400010540c014035840c07049142c040c40003600c9560b07240c419013082c0c01c83c00e03844041a25602c06450110041076010105801541c1142401a40c0e24000c11401d10300071a85840b1800c2c007260b5031a44402c1d80c008540281e038601303950501d4188000c40e141c0030398450b400074281d07418244c034590056480500a0007079864800c440320384080c40403c4030785400c26200b0900000710150780b1981d240d90b0f101000d4640500300720001d0360319000304000c850507816114001d400500c01040820340301c246100044020561800e00512206070001c01d0800d0404010302041540d5540040030034080305c503a008080303480c115440c02c1c0e20700c0d02055491004681e00303580b08400300005021039842100c15040c85051404582c00c04114400080702c00318120402c070b4000c41c1160402a04002c02d010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 716613012 1250 716611762 716611769
    0x1120c0632030919052802150304140a02032e1b0f02120301210f0812062e030b12010c140307081605220303030615091401030e0a0b01030507 62
    0x6020001d1211517507201c0d141d22046c3d0011040304140345e04031410a2060007104801b690080c0b4644040c1c81d01c1802c80100d403c05d88051703920b042d40030111040c0c0700c400124030350076070740013001401c1840e852085602d014181521001d884409900c0301140100b00e400303014195141c03042e85c013007941c1440c00c008061130300240b20300c8119030062003d140720070380860071a070540e1503014a510024104800c054048000342c04010a0004910361500c01c1c000144040c024402d6044840725140e00d0300c900700050303041c0304002c1150070708081d155900898a07014540c01402e4003410041201c071203c1c00010624100c0000610a80c0d4451143c0001c03e548000d1a28941034614a62429420a4030300202842c1d4000d1118101402111030200390901400c299400701c40e0a1281d01a0712050582c4d0b1a811a0b0b248000c0740804c0c00c0c43d40114000c6945802d045e0884007980c0c8003000c05180440360700000aa01110f00d0501d0354440300c1c1050090f06100140f103590003059404541e5145203051450210310782d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 716614262 1250 716613012 716613043
    0x4091e0507050310090c210f060906050109020a121d12070210171306060504060605090307050103020c032d19021606050702130f1503060501120c06320309 68
    0x8401a0006c0c1254034041d05a03001c2c031120841052070a405881703c41d02c01c54020300944e10102d40e020401c165904103041041c460401401666640c0d50000180e0007150000c10200e8508544038030b1641d210707413100803955a0000340702c0c1d5a620310401c0508166560300ca0032203915000440b84150b050450988003824480d2071312251514410b1714198544c44064a249420740f003001c03034041482860307040303000a018010000c1204960301c0101130003c2d8020b5040b40d000b030280040001781036020380300b642d0405c02c09602075840c2898105c0b1301851a800d11099181414400c00d40110814410020703042d50540c05d084020420700d84d0070041e245c0860392000305000c6a540100340441580001179940c25039050b84d0328500c030040a40e255010b000b404210802491400c000d00380985c0e100840301044038040d48040120b070740c03a0413004840d2400e064026000070350031002009018418640c00b038981078110080009807a03e080004104400f141c15400114000b2050281e00e00c4207008100c10b144152 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 716615512 1250 716614262 716614271
    0x705061f0e040c03052a040e0c061608211501090b0c0316120f03110301170708060f0717090d11010b0406030c060f08041104091e0507050310 62
    0x22454040203006000e11400348550502180400c503007840032002859000054510340a00841280342c0d00840007801c0a00c010b080002e50307001d0901e031240490301c1780c1400141840b6070080003032264507400940c80030901c1d9022030600001c80e941201821101621000d612503010800c19200ca5460740a0005032a1100211a803603507030b03070410307040d204842003042640e40b05d030304005004d411405034550010200d600e03a034650082001844034901110700740d480e40246541c8d2410110308640c010420b171021000200014085040175980c0350404075540421109010f480701a020f0404000340c8210402c4010241070003810380c2c000d00c107150f000940c41e514850900d4803550031940e512900b0800014000018010144204c081d0440668190060700c20300c44aa503a00d003070742940f08130f8802c0a0000d240c0401015141e4824983c0a0090b41c10140964080403040200802421194412a00095070840d0b004415a0840031140f04a004401901505251a007418240800d003400e4180040c6030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 716616762 1250 716615512 716615551
    0x10e010b03240d050c0102060109060b0711030c210105070c110f012703050d090305100c09050d0813080c0d0b090a0b0115030b06041406071511070506 66
    0x8101520750003400c0e2030b440120484a01080d0310b4a4200003602030b0409114075501e000d101c0c0000e012004410207900b114a02e03030b40c40c0244012210140034841c0c00781c030104140004102c06200004d903808005040c2c0701c524000c5400a14100031884c80c0b034400f003200004100e0040c0d0284505a88056103042000c00464603903070f4844038181081c01140719640410303141103140d1240307640d01070505250040141400c4011008500e044061204440b144220303441040700920400c6001c040f2540100240180480707980701b44d000d032040300c8041080010f8131100094a80e501e00306109520b024015080c0e0303510034001a01c001100c1c0c0c0d00200015407014000101648403000c0c407200300e5403c180c3c4414246c807207092903820113101c840050500c101040000c500030302120fa4001c00143d1780c0c1c408200058408051204501680c0310300700003500c0311b801500003810840000c011051141c425400da140600c00b00e9412181203c0708107107050300c04200320007002820418103401c86105c406091403601c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 716618012 1250 716616762 716616779
    0xf1b010b0307260c040e01020d2f0d0e070f03140a2a0509071e0212121302040e0705040c030b0303031b0c0d0e4207020415030b010e01 59
    0x40d10080c0d0340e8100100c00c50912055003440b00c00c884c1c0c88010f0040c081c052807040130b28040d400c11248080340b94909401e81c520729080d1001018401000c0302c42102d4103640500c880750765000702d2549039015440f220f0250b900f030400d12508010f0151584009090350540c14100c54008210b0030f0180c80303a20886600d00400c06511541540c041054080140c0a000c80d203c1480e0300030ba42d2203940c105040a00740980f013508004041c80c0b807030608011a0001c201507000f03da94a8a100855451140030003055091081c40c00d40709a010340c0c507081c0940d4008040d8040780803108000a10b0f001034004010030300841c60705014540081c042481c090003012144000292a40300151815076251001a66256807443c0e0700c003955481c208201c1921401c806001c401f4000d040241c8900303110f0031101c8480c0c44031074903a02c001c1c48900040d03a52540ca075061106020182c0070080c0b803c0d40314090601c4601e0050742e40c2d024030b0840c0803e80900400803407452518001c03411041c1c208566206090005102600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 716619262 1250 716618012 716618039
    0x314010b010903140f03040e0a140708040201350a0f021e070f140c0a270914031305241c0603120809061522020f1b010b0307 55
    0x3a002486608110402103050345001c1701d00b8403200b12400080386c00100c2041d146941c40c07162080210620090b0021a091054108210355801c0800d00000202d4099486201000044d11139030100a4200480000d4031103000e0264200d0091000d50381c08000c0303005c0041c00340c451072060140d03040d8200300100d00d124a0b40b03004000d110b0152070011401700284058502070500c0240c10071441400035008040180e119800c40712a41d0141011000c0004d03940c0100c07148100103400740ea02c0340a0b9000040d10000580b036007100aa500741e40409a40c0c000d101d09100811042d85c070303021151000b610705001d0100d0301103119481841c0398101ca94050001c1e00a004413042d0802c021801e40760410000c05000c01800f01d0342001c0c000c1d01c545542090b0b9280c1108029016400090481c3d100d0b40d281d42c0c081e64500d070700c443e0342900b14404607461801d0000e0759000a2001d4044200582460648004400f1641010b800d01e24110b50403128402e03820800c0c031a510191405a014014290500e0100100356 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 716620512 1250 716619262 716619269
    0x2101b050c10020403140c0d020a1e0b0307110f03070305070b0a15230f03031c020702060a030504021206070203090918060903041a0711040c021905070314010b0109 72
    0x8080041d00201280341440604040300c1c800800b192100c2e141e08240f60300c481d41c07159002d441e106540303441d2a685030a001e24481154010b00f0710b100f403410800036840740360780c41c158580d03480507000c0b010944030411000b0b9842500c0c96a1507083d0143c0001241d890100e40c00440f480390707041044000046039004040b111402d4000e0181810364441e440403034020985a80b240610b801882c40210307031141d10402441e98041e0a0b1050100d0040c00310400c40f03c00c49901900c4d03813550040000b49040c0c142002c6007803803041215801800c00038150003041c00c941c8641180705c00240c1d20350420045152034800c0004c1d00c803144000f444207142900c03029540c0d200c0d403a80700b071007880440d002440070712409018500690074001515905c0c14445111607590b0000c2c01000003d02d0080d00d03a1901e50329290648500c0c030b81100703441421000c0002407000600a041c1014118019148800c030036400d030b071604103a00d904c1080242681c51a504044442000c40e01c400d241d00d034180800003030141e070b0001b40d42098 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 716621762 1250 716620512 716620517
    0xb040b0a03020c0f06070207240f080c0d050a0c020105130c061b02130b01030605010309030c020d2609030d0c12180f2301031806111201031202101b 65
    0x2143c0715a0320b458940f21030610800c50b01d118030800c02500c0f55011a41e18200e503c680d0740b071510000d1580c007511200907130b0f0b07807128002455003808401080c81403c0d00d030f4010400c1d040c0d1500c1c21480130030030402ea902c2100c010060544a1601810b500d45c244110783d031019124184043d0f0360115664101d02c00c806214540410401200e404000da107a8083e03202001c2d4000c2c405079241d4492068103001d0f000e10b01e000c42c0841d1519500007590f502034081c10f078003244e01d13640320800c540e01c0d50308200c4400c1c0c1c1143c05070368146903803801c803414504540c5240a01c0d6551410aa1144900e80c2054600130000012034100250300e8914400106800d84980c0d41c180c240c2000700b14900c000125908120142d031042c41e0000e9800c40004620140e4000020710740414038503000b406003044015004e4a0b50b54801c55148640403400a02141069000c1c0760b011001c2c0308641c1c03500ba000020344140d09002c0e001074912000d00180001500d80401240e100e4001000303007400b1010900d00384404259244618209 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 716623012 1250 716621762 716621767
    0x304020d0b040515040605040b0f06030703170d0c0206041e150c140d0b0109050301020f1e090a0906050103050a0c0207210c0e01050a170705120f060a0509070b040b0a0302 75
    0x40100501420240c1e902c011a103034071345d2815081600c007401c4180ca0540b030040000c0d02140843e51031030141481603202400820f02c1503d5962000b60b0030468214450250f1018072210034042c05d1401200b820103803581c010f1140c0d0901d4148110000c03c20311107055022900c10842c4000740096036a4100c00005403800603109242000c15034855a41500d02d0980d61400a11500880d4299010200400087c4d036815a1142c60341c003070500b01d1103000415400104107124110554042008101c2c07016407501c542400d01c8003500104001209903003000a50301d49810090040d56454442d0b25800740e4101d5091003500c4001c04080d450b664540102d1080d11982072110400607580108100d0f1258040c0c9000d000c02d46e030700c4105954138403e0148602c201400000050400038207d00826904080c0340074090040ca00380812441031111403001d007041c000e444130729165160910130140704401c0072201017054a80401c5a0f414205030382c001c2c1c81e0200091000303120300c2c480b00e400d483c0005158180181d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 716624262 1250 716623012 716623021
    0x9081b1e12091309061a01030b0303030a091506030c24090308090613090e010e07080d0c06140a050a1107050604060216080a0e0301060e060102150711030c070513020304020d0b 77
    0x843e0745000c02c80321801c0301d080120040810010303a100042c08004554410b000941400044094a4007802c043e40d16510074004207030040c22950050304480d1041c40701000b00840c0c040141c0c140c40d4168020340e40c01c2004482000000c603000340045070103000d1401d81036032188030340002e0080000f500000d001131001140392100b6403503040c11130f03440d0a114800039001a83d036809a00180017078030701024255003400314401100c01d001460400769041c140241c0a40d09034928100d40c801908030094410303540354140e030105100300d0184980258002000404c091415444034415510f07000c00302d054844c0100300e80000304001090840d0030650180001d40c0e078010b045e800e0302c0315651218001e06240e00000d603c001582d00000281803011080c2e00130b01c82c080c1c2d103901d040e2203030004841081c05a00708014010001c41d440c0c081941c0205542400c00c0452b038440071451440c1c0000440f0012540258400e01c56440c11a030f50049c0c91015140a503c2c41c50242e011407027852001c43e0041108040c0c00118 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 716625512 1250 716624262 716624269
    0x1c060506190308070210080603100902040209090403030c0908070f12141c080105040218010f181805180a020d0503210a0c0c0b071209081b1e1209 64
    0x2801e4200800c60500d00c071680320b042c01c01c21503220400c1284102c40c0b103216501480c4c01804d8480c400e0a000300035016003654102160042c0a83c210100e03407040c1c0c01c010422140e5142044580114041e683c00140d40c030b424800a480d503035540e000340100f5070000908000302c050302c10307040c0295962000c0303070701d40342c01c051604249450b643d400d04580c80c00f8404c0350181c0d00107248140140344103159901945a6030fa442880100d1107140d18174018ac400d4006521032950040142c800398010901c1c00011030861440480d04240c02d540012408503107800703840b900e8880b54040c0b103800014441c40d201080304144202e0f592040c100354001d0040c18010603072003e2080510a8802c4046039048000c9084a10383c18103006030800c0b02d040c10070920b0680400c041c1c0b44100d2142c0c3c0701550205140c14184c441c0d00c0140c1e0301401055540e00955180c91501000030881c070090000d501024810f60031401c0c0266a4a0a01f81e50b1200481c0a100b84e86900c441d814002900c144030b00c1c800c103c0303580c1e10309514020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 716626762 1250 716625512 716625529
    0x2130c0e0307030b0f1501020c010e0f04060308093c061e0706180b0414030702030307050303040b131a070905030a150e030f0d0c09030510050f061c060506 68
    0xe0752601030301200100b48000c41004520038040c51381c4840142c1d5070480346e42d030110080a880e9005901408808660394080c0d004100005001810b030002483c51400040070f848140d00111103006000c10450700b142414144003050a100d084001c5100a0149160410501129007800d421116503010b581035140d0034100c0d684019029415030328101c20307084c06400c660011038202c81c51442c0c0340000500414043d0003000d5184d12501e4080581c40c1c580305ca0031180e284507030044e0140810050100180d40410050020900c0751001d507880c0d1405080203106000001c2460410806c0b41038a607000454590340082c551005030584951501c440c030044130b214402c1e40115415229510b2400f041c095441c1e000810310701c0705c039000e0000c007102c07039001078407030181000041c480103080c003d0040720100d80e0400801043c1902e070074034005a49441d124035107006503c100003141da0b944248205a815180c415070b000d84155101034403414840d801610710b5100b04405846982c0d9040401d0030340c0d0310300c0103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 716628012 1250 716626762 716626787
    0x30a060b150a0c05120f09040e01291f050406050703121d06180703020f04140705130603020a0e090a090206040602150108061e0712051510020a02130c 66
    0x2109600c0342c44204014000a580a0f4151124400e16044841e040080000c4501150010740c4060610142a050001910011010300101d54031041036555500740f0f0113010b42e002d03a0003200d07060443d124409009909541420034001606030030110f41c1c003281c00070700301c504450103450b0080d5113035218102210784038100c5020304c03103250500ba024010a110a050300101907141d9040e41e00e0b68450551850400b0014104540c558102260030409172a05035100c110102d0003a00204181c1408407040c3c1c640d4400319000c0021480100f015416081d90103903450141c42142070862400351520400f60404195540c014441c02c0120000360104265030403100b5266806460313240c5a030744504010791a01440f50260883d42c03040300000966040008a0b54028030700c400340207006603503084006034525001880764050103000b1906c0c40c481d1040d841210300c03c104020182084602c00710030020301c50f414039040000c5500c80815640036a4441c00c081788181d1640400140b403420030071003591400113094 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 716629262 1250 716628012 716628049
    0x1b110303040f0302041409060601050d060e0f0108120c0a140c03150717040f121814010e03010c090b16021203040519081c0c1b0503060c09030a060b 65
    0x1d000216550030070401c9043e81c0c03003200c040c0202d42c00403000c3c9000c00e40c1120040d01d41d50155000c60a1540074000070001c17a0342c41d0b02d02160454581074140502d03101660b01440e0041401c00400204106001c8802d0076060411803a14084024165a0340c4105981000c0c1c001d843c801a02e030700c0c215003040304200a410107020b9440303407220700d456840b0419045440c0c1010880418250604d40010030380948120361080040403882d0a0f51650b20600042400040c00c0c0b003102403280c400200740801e004001e00c0380c0c009484140030481e000428079200d0b80c000b140260305100c100640d9940182c01c0d070040e03511100f581502e030429100149000070703200c03c0194019012081d421003503a0044001c10a5a40c01e494240c64510354450340da110100318490035035140c0060b0500f8000c40c80284201090b07400501c1d006415034a0354071004031240d0f55a000c64403807564018200040e040c00d10000c3d500c0b6142e144100d06244002c0c0c0440e803980b28400005281d60390700e82000c1c24980d9010802e064004206 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 716630512 1250 716629262 716629267
    0xc0a050c22021b2a030d09090203130203120705010f0501140d050102130b0304020906060c060705161e11040204120b0408040e040c0608130c0e0613020c070501030f06061b110303 78
    0x280072242c0e43c6090b0302011354249a00c8581c4164240000e090440702100e1340c94074505494202c0c1d480003508040c01c0c0e014400522425140136a80402c0380780c426542000c011030340ea41d010300c0d040303084030400c0c18180409400c0c103004208a17080a559421509401c1e2001c6211107190714003d402486021009090018002e601041c00c80095000e144507904c01d80e0015420384520040101ca4024281c0119542d84205d0004102905c240301400301000140303101056141555644841d240701c40e80500c80c0c00c0d000382018000c0c17203850501899802c4050300c04515190500c4916030311000c0c0000d010305800298400f040804c120b1500301c40c001e106017040200e240c00e140c60110000f400c0c9100e000e0000300c2590100700441244550007202030352011500800c1854600c0702980520000c20495001000801001d242da65074001000d504080e04003134846107003844005001c03241441010300e001031418405121325900580c01c50040d480c4100c207403da0000516040201ea813000d00c0035034050001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 716631762 1250 716630512 716630533
    0x50703020a021204120305070614040605190603020108180f06010611070806011d0901090f0c0801061d0c0310030606090b3606030a05030c0a050c22021b 67
    0x550240c00340980590030383c0c0b041e11503d14100414000c5018030200d00c0030365071140e00000c0c0210000c0c44180e01c981d002182d00e803581031122a07200c104441c00e5940c0341c3c81d24200300b4140e5098080c044104a05207040000c0c80c196000208500401843d0300e00c2420b9034400000404410001c0f43c0700600d41200704d036101e40c1c40710002401c0c007141540f55201c520030303508003180108000c10001e040e074560301681441200c0e0b10108061002d070103800d14005558424009003c5041c0980180c3c0305805618108415807410110302c0c00c58540e0350015403400c0f44401d501c00c110110001664100c1905020180c81e6201e540d800d1080781101e0f41700030601443c145001a01050903003010809580440711101038082c4800302508480303900d9800c0040725001c0c1344017101c0c40e420381d840c6074201401a0407a04001803541e256480e540c010044106954032480050040020030808680110001c1e592428082200305040d08400301a00c10112402d0f0080395100c8240c0b150f204180010300018125004d1510 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 716633012 1250 716631762 716631767
    0x605091003020103200703030c0525050c0d02030c04050a0b19030c0e040503271c0b0610090303081f03030f03050a0b180a0b04020a08010806060a1d090a060507 70
    0x351403200301d0100382400402c03c04480a80c044c20340740e4048540c82c1d0328111296401702c0003041c52400344014420180003440740680c40d286000d1007800d141c011103416100c4c82c10300c03510381024000e03194850007030300b410200162008681d24980c2602600c01280303079166070490202030043c001403141c1151000b954a8140c03651005a117046a000c2c0d4044c80c90151101c405120b15907040703a0180040c2d00400c01c610080701389402030005040c00713030200c004042c0000c0c0091605c0d1800040c905440d44805c1c02c1405009919814503000101122241c03c4070009800280810600d41710140601c4020030004074000d80c0d440243c0c441100610001000944a240c090b001c414045040c800080c81d0000050005165101c1d030501d1120080c0f078594000b041c6540a005000000c00365041c80362560b041d10310640700e0f4000341c025201700f501c620201d503041c039211901e0134000030201031040028620820202031200203510101441c1c03052030500d55903030700768180380c03080c14900240700618080800c03100a5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 716634262 1250 716633012 716633041
    0x3030705070312060b1207140c0313090c0801050603130506160f0c2d0c03060603120311040902090d0b071d1504050904140a151404121101060509 64
    0x28030a40301c928014140030400d00c2160064015840c0d8800101700c543c2c00034101ba001a036102c989490506000c901810500840750000070f100003041d40085014660100c0c2c9240b0030b0090521701c003040100111181c40240400410710400340074083c000042440d100411a20003000d03900030040300ca0f80c1c10441028170000c0514912200050b203030841c080c6402d0311034440b05800076003000425606482590b0000b83c9030b0980031401c61000d0b030b1840c0000020306000d01050041d40107540000d0104d00c1c41c1054001c2800041400d0105454120501e21030920041a41c0944111103001070702ca5071008080b4411510904024042c0b545902c10042e59660081484a001130307080040d40c070001b42c120502108000c00d03030844250000500c420303c040c0c1889a000c903400380c0100c034a106124214827042e418000c80d140140d03541881d1003180407608540f0701550080500080c88413486182940703030b05802c102c1c00900c0300100000310043e841101d509400c903034041c040081001c016414188412040030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 716635512 1250 716634262 716634277
    0x120303242d040c0503070f030b19080f150c04030f080f070b1504020711040e19060c081e1302010909020a0e0312090d0f021809033619030503030705 65
    0x580c1080f0f14030189610030750940e40642d000e622440140c072201d600903006041013030b503140d0b0884a4102c01b02203000030003076103200600ca000701811070441c2c0492860b041002103524108030a5008041c4003c040070302c81201c080380c1c1c2117481c410952001d858056aa4132519042000046002c02c11000b07001c60205010301030b65072803950a83c4008000180002d900400c000500404603084002c081410190021080c005101013684d25008480f1481a020107001c48140e41c00f5a07920864040d00e80c2055290750800405402c0130054003148584c1c1e8080e100c01080e4004074216207007071404590140004d00c01034101c01c0819500c500c60448000c2c081402004440e1091043c0c4600001c8041034608440181401600c03150b0780c008d0030748030a1081e05240c041241c00c0040e0f100000b40030300311000c2c41d50003441ca50b0046c6589801d118203000e488040301104c600804120070600a0300a59001e1812a401d8103542c0c01d00c900300081d840c0402c0350344c640d00c05055800f000003000f8880e6401802001c82 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 716636762 1250 716635512 716635519
    0x81017010b10080c090906040b060c030a020105010b03390408010e061b1b0c030118120315050f0a050d03050a090e1006120902030706020705120303242d 67
    0x30690140e41240c107100f09407007400c00a0381c100704035a080e003400c20344141d0040b4007030800704400c80c5100206800c0c1c0e01c01034040205820105400010740d81c2030140500401210340301c5070460401810048a084041600b81c000c502140031410000e03420070681c0f006e0070403010406484596952a81d03002e4601d49040d8051405150009022450002c1107812042082071303c0c2e604004801004580d20740d07400e06503420038401c46501e000c03e40d60901038407030845099410b00d0031010191400a0140b46e505443c48241400c0102402c900d40010400b5011100d00b2944040403181c6170004c2906446140c02c05a08803581c2c054010a040d0031400070607901807540d441034900c3d40e944541805012041da15002d40108610040000ca4400c505080595202c00800a245800d07076001038505010383c0e00c280096040f0000420086c50b0100450f0042003040000e1480c601c3d2200c410002c81c801c0c41740c4c5d04a03007800340459a415444d52809440c1d805420481107524010801c910794080780740f8000c8610 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 716638012 1250 716636762 716636779
    0x4060509100908040e31030e010309030e0405060d020402070b01050a080a03022a0913142407231312020f1e03070e0907080703020907081017010b 64
    0x44481d051045180168101000604007424020a1302428070080c01c41030791644014112000c038110040381d0800250340e103401d074150f910207280c00fa052210814149051510b403881030400310380c10515100400d10300321000581a5190000901255003c400107904544082459010460140c14039410380d03808440010030913642c1c0900380c0c0e0b43c0388034540040058000c1ca00e0f02c4100c02004202030900c41c0000012840010900e0116140050442d00d8010580d00b1160000910081c24900c621500e40040508048880c03a000c01043e89a44a00a00b0b503aa6000000b41118480d0700c803295250303034980c003888090f01404400b07143c03504940850304070602001800500740c8a40c001002080364054010903071b5100318020092800404a40c2081c2c1c10089985248143d8040c0192005400c0761400c40341c0a00b44040224507140c90764004103081d0b48148028070160303851340f48440d4820013528008000d40e9440e10b50545861071607005000202c40c0c000c0c0c260f804003064001c0d4007852010f950509 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 716639262 1250 716638012 716638033
    0x3040807050a03020a0b0a021e06060108010618170a050a03080f07020102120705031b0406020d030b151c0f111207020105070914180403031509060503120c0c0904060509 74
    0x240c504010310000f54017035080d1208010301e018030300c094880281a801a60101c00c642d2000caa08804810311941c1c0c680c000000f008081c0d82c1056181d40908541d00d00701070300d15100003500c02c600d802c90054280c0311801244505c1500300130019142210b07400010703600303403241a242c05460807000791a29402100d007030000540d014030503c2940d031601c505c440400701c0b40e00c44940c1a645548060848200d4041c0a140c0d5070280c40c05100030b00060005030f00602d051443e99034010126004040c0d080c0c400c64124150419103018482501c1307aa5800e804010b1007034a0940c8000010204186400703402414000f03225101490040905441e4180314003215043d500da6008908984084034240007044807444240140da00032482c41051007800752601c807407070720b170320201074106002200c00300c0000351101e50311034040d461030710810000e215005042c014141030000183d103900659590800006011905042c184010001403000c1c0ea40038000400301e0816041c048060101201e18010fa0711039000e203803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 716640512 1250 716639262 716639269
    0xd020406080106080403200309030d120c020a02280f06021e0105062b050601180c0203030408120a060e13061b020a02091008120405091003150e1e0304080705 69
    0x45200d198591f130307081c0081c00c0c146448007c011602000e5503040c4028440e2400c152410040e0038094065621600c20940d01010718030b098070911301d400720454100258000041e11500d00c80c2d80030a203a101c070400003590a9041c60a040e00a501ca100c2113a54480f00158aa40201e01000030300140e08001128060065415080c0d40041d035031a5081180300710f01c1808409090041518600e00c980724580c0400942c55441c60401d0a070003044010040081c90f540141d1148211000a0100d0000d1030075440c21b9118070440e40190004070a000440b100041d10102c120f50124010b00381c6008014141d040074508060004c0c1a210115565440d00048e02407201d11001c4003052144564010030b0b80c40ca4a501340544010f000e030044043ca0225003020813010424800a052003000d04c0c1c25645503483d00003000901007000c0d0011145240900061021070b111012030180d040b04c41c100480d82d041d906180f00d24080c0c019041c1d090301160440000500c0780c01000600c22241769108842c4025140c0082 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 716641762 1250 716640512 716640527
    0x30a0b0a0e19180b040203010b040c030605100207060f05091309060f060504270f0f12140f030c0a1416060608010614120a050304091413080f09060405060d020406080106 74
    0x49003c03a030070f00c15a001410b161a8540d0041c0b01900101e0f00b82c80e03e40100e000ea5001c9207080c00401c1d1a104207220360b040c48045000451542d20050801525050b005409401101903400400c400096401c890303480b901c09545c10385501034010003440034ad60070542d0082640d03900d014180c074103001c0c0005851030103000d503641c2450301e182101d80a030740d00541701c10b41460030603040300c19170840d00e55240232039010140102150300441d9005840c00c3d20110003030810010644d00d01c503016017841082c02c40102801502d500009112800750f07a5145030381c1c1038510880c010f030303842092800000c07081c000402c011000f4032058030500c8107020550b1540e1404d0300361180b90003100b103420301400744100280303010204030f03248081130020b1b6100c400c45a15140d00390342c456003001d01ea294031039108007a508400c8900d103912035841c46c40e000d001602a9a01442441038080c02c412450002c03c12080e1581c0b918100c3e0010400100125070301c4080d04003040c00703074116105074408250410000a11240229074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 716643012 1250 716641762 716641781
    0x9011802030c0f01030902030712170412030e0102031c0c1119080702180406021c05041104020f12130611041206051801090c290f030a0b0a0e19 63
    0x40c0c00009540c00502c83c0b000c0d01d08410038101520b0350440005a201804800c000e00700c0703a0713003840701050a0b060848044680b210380850210b000c01c820041c86507441e078400d07405985441c10030000b40c000c1c40102c1c038500490a4205c4070b10542c006036003c00105500084600c0541c0c0c5481c2000510061145e494607a4039001501f050802242c5400007403000006000740c52000300302800c41c80d4280076221003001c045400b290030f56400128480001000c006843d0803400c0590140814a0f01e642d400000c3e51000070382a0165401050102400011105403981071300d500c51074580070324165010491072020081c0985120746400041d8070210a60000c0714140c40a801410b0b88003810b030703a00c01340142402090071100480160140c4500340f001e000c1d82103564000c00034203015900b4098000f41954107004440c18041c2d00f05000c8148169a08c251100d00e045040100d4895607032140007009000c4040007039603c460261030100d0326001044c00e090042c0a50280b01c0342d40c0c80707910743c043c1c1201e02d23000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 716644262 1250 716643012 716643019
    0xf0a052101150c050c060d0e030412060b10170a0f0903050714070e2802041e0801062d080d09030b01060c020d0b130c26030304030519090506040303050309011802 71
    0x5c1215140c0c20301c0c0e00201481c20f1a41030005500c82d08203003503400c40d00f05070030201041c102c0310325003000d000003130003a0f800c0a14100e501c000000d100420180038184480c0418000135020b0780010581c01640c2e002c0e2445545441c014408008a0724008165a000e03410031103010a452041c020141c9000550030240e41841c515000c0303e8036071480740c41c000d020329441c411098074044001d0307011190500207800146070b4001c03145841014207800503400b6807580c000d5002030b03150144c200103002c00004030302d4035070b4000300c0405046940b8040d10018500303e034104246510400d1490007070241d0000070101241d0003035507180b03050303600c803001120500300075503010b94050300d907034600700200f00d8a41d0300b543c00840c20103041c451104ca5664090513000c40b0703444504122001507007000d2980600608088028071078014628500d05a07502406c42d018030b41d400c020b0840000c0c50000302501a11412002d03220040207640c556a0300d02d03000744281e10840e46840c080d42040c1c903511512203102095815294000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 716645512 1250 716644262 716644273
    0x2010c020d0516140f010f05090f06090402070516121106180d03051e04030c14120114010510080f0a0c0c0f05100b0603010b0f0a052101150c05 63
    0x10340030403508044124081d0394601424501c100c41e0301d10003100c1c000800e2090740e0208103544640030040b08807580d08245052007138640c1c100d002039038407100b00c800c00c030030032144003a41c0314421010030150b014040c41c60340c00c940300080c80000c3c4040010244810300440705544c07c010f0302d65007401502c513041030000b444901071200340c0342e0714a0014060000035841e08070f60b807401d0726a40006006c0300c41c2c0220903030200307400082c0c2c08040d1907022035034a0500c8074003010528062850b81c0c1c0748400e81c954031035410f42414118031010310b03030354000e580b52501c0201c500901c0006002020440c0455007803040301d206024a0541400c1d0500828880b441000000004480340e41e89070403805c09800c200c0c2c80340d010040041c0a030400901140d4055080038040c80c011315a000d0040c41150440f00381090841c0301c0d000c20700040000d804800112503400800d80551925407038103210981e024022002c100c880c251a1100f500c100394000e410050481e0501442841e21600940c01500c241151410181182e00304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 716646762 1250 716645512 716645537
    0x1c0525061d0a081207110105072f0a0206090117070504090f180f1b080303160302030c04090e100509060f1807060c1505042001020712111504080102041d040201 70
    0x40352150345e01c2845030828468a0b00580446821200112120380100d544103058440440c3c03041c070a02e60706201a503141802a40a110351641c809119800910450b0001420762030b5034130514151000e118843c0202030b80341009000540950820301031004e50914000302080c690362503009002d44102c80300080c0005e1001d40d19403000301e80d454039094440400c4008003005d60590084488020034100c00611b482e030406070400119000aa040d00040500500610042c140d03c201210f040b0746810790001503a00100b1394050404480d240c05000040c584010000c00000c046920ba10070000751004100039641d00b800d442420001c10ba880715142c0c0408400c3c00070b503014480304a107440c01070201c1c5050541090115003a981e088404031420950707014804025100e4003640c0f42d000f0320900107003450764100740d6a05007004600034054500040b445600850317413100707a00226480203148151b940d89444403541800703544181715801c50042e400802e0700100403079072a0305015071b9050b940c104441e82d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 716648012 1250 716646762 716646787
    0x60a0309060b06041805011a030601120b03030f0a02010c021204120203070902030907150503040f0809190b09031b03070b0708211501021c0525061d0a08 67
    0x2240e080445046030b41d0303035101e00c03030740d403044050801805404141c030003034038072405040f086d22410780c410034206140c02c0810300c1c0c004010090f00c1c2e22120a00c0e0100b45166000c148402810360124100d415000002e1040c290f00c000a006044d10703e0540c0013408030075800e0104903a01d58055081010496051105000015042d0800e101c1940020102d48000c1d8544215500302d0b80250352025141c2d002d07900c204011810350318140042c1005081540c217500e4551250110440382d00700081003400c0005091246584401a11840300282200f0f0b60b0903d0300d50802212030351146072164401e10403024114408103910401c45801140600501300040c0f03050251100c5e07802800b800c07911114280301c480c40c5002c4118030034004841c00c0036181840d04007102e1a084003050165100d0454020506072996911070440e000c0084081d458503d030748401e84050071841011200d04100e07600c81005800d001e00a4070742002e402140e004c18484880038251400b0347c1d850208041c002d110100506c144500c450 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 716649262 1250 716648012 716648021
    0x140d03030e0123010e010509011d1305032b180809010309080c070513050601050909191d121315090e070507060b041518060b13080c030606060a03 64
    0xc20401c000318600f28049005a4038018076003a681c00500c0b500700400400840318400ca00510055031252060b504204503204040c030903120010b0f440030001c0120340c03c03c64008421100580240540c0c0d10b9030440510403036540c452110321240c041c180321050211b02c1c681c2c4181803440303850491955036415142d807542055003101e164181811396030300d940f01c0802c141c070300100b004003000ca000e0500c0c141494100001040c3e185544015a4501802c0104590b00041210002441241c0341c1800c1d0341c1d540e40542d040360300d0700c1480d1b04490604d40c4256640c002d40c485503100701c40380d10940361001c0364a07030380c0141400b40455049610544810405c00d608400032903040d001c680b40f030301c445000c0c0c4401243e000100b041d5079171000100006052002d000c2540700b20400000c084600b400709800e0054900c000d0031300c038081c03640108030b84071141440159940c4004010400c24a04c9a00c0e120406140c107941d0000c1d225094080c01442402d031850710f008078601e40320304c200070040c50410312036880c220002c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 716650512 1250 716649262 716649281
    0x20a03120e030a120b0301092102061e10051203040f0b191202090402070807021926010f0608060601120203040309120221010507120204050307052206060e0109140d0303 74
    0x126924505c104954600b0f00501c0105800f81c40307900c0c003002102c1d0a804d10151642e50020464100c50280020110b160f40100c000421201c88804191984903170200c0d02003440e444960b100000c00c400340c4424101001810859180c0b23224904140d40d11a0a82842d1080040c00d420384018603159103602802011700110480040c880103003891420700200c0c0407031380040d005030749650b0007040c40e0b01186440000c0c15000040c802d10014075601d0100040902d4102c100c019001043c01c070384194103c0c1e000d601110815020500c02d00c030060351100b40b0354a9207001e840c1c1c0c43c00185811100f140b0301e0303007500881340201e84c16610131040600c0c18002400f0445880e0041340c2c01050a4982441404c4680800701f500c4403100001845040c400703400340207041020303200306000d030050204100940d000715009040f21401c0d40c02205020340318508400080030005a411380c903180038804142554010b0390500d08900a8843c540c0954494014800101c9012890342d84480580c0e41900043d100b0341259000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 716651762 1250 716650512 716650547
    0xc0f050d02060904051314210a020a060e1213090b01050307080114010c2307090c050d0906021b01050f0c040524040803043c1403030712020a03120e030a 67
    0xd80c00d03d5900c1c01c000000111f20100250b0050824044103c01d028001010240c070302c007180e01d8040408400313900c2d0010460094041c596031030865100030001c0c0001034412811903600c60781c1d003c110000044481d10390040007850740c03402110850139400781d0210303805051541c03240380c1260301e009658086d42c06190030b00c50401c40e003c841c400000d0040c4400c3d805d00c2c0c2107040c00b196560021118181b03450019440244e6080c20b10590301c0d5030903040811030b80104803160000c2101c040310b04002c0d0203403140d000c0440101844548c645110303039040d071007107001d03c0401c03001c0652520341103100100d80c0514020a544480c040b25110107416803603000e240c0103510800540c0c200f5594800d0b00381190410742c892104001e80c40e00180506504101d00c1241c003414001112540400764140c0328100f40c940641c82804040184a80ca80c3c1d4041050f0b540003503002a18540b41400c0c6d06000352214080003040b000301e64003000500010915014680908450400640c10711052000803100300700200800180c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 716653012 1250 716651762 716651791
    0x1a0706020f0703050c0c011404030b061f080f060915040506030c0429191802071704090e010c02030a0f090806040f0201120b0109052b0c0f050d0206090405 68
    0x32020310700c8000e440d845019845491711031006a061a0403c4a022011810041c902203640701000201c0251030603250001d540032515070310f031400b18a46205040400e00c810300320030003610744180d20030724051190740300210f003d03615160b440a200c940c950507220000c007042510110780460806502055018000078200c070180042ccc01cdc045030469000c80c1440d0154410a200d61001895000d0800b1103030f5001d54654031200c0c50f80c1502e0b140f0101d0342c01403d03060000c2c01030300d010900c85501614011a007040035030003015100340b6400c6d600e40c814441c805503d82003400380200f40300c0611070341826072076076000713185800b4014004a5600d92002c3c0a00140602c802c000304020344200880c6104a2203000b1000f5022a80d00000d42840e940303c840c4101d0a0070007210360600d90b4001d07202e03421034005403100007800c40c3c800309074080e241007514845c174180d10350307020174041c0081c11003401c0c11070320700c40454050ba6403030f0401d000b80d407081e1840203500120100f00581d51070500c1d0380031942c0203501d0030b014017 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 716654262 1250 716653012 716653027
    0x3020a090b1621020f0606060d0e0708010f020d050c13090f060e090102180904110607030c08030708150f0901030f050109020604030809041d0a1403091201021b071a070602 75
    0x8004924055401c1203c1c2100c0080620607030100319088485101ca00105200d203040e6000803030520031a44a91842503c40c4d5907482c50680c20880c010160010100901141008141820081d04404802c218260070b210110b400700f04ad107011100c0d40c5440d01a440d1525041031228030140034a2039a542c5032540d42c5e00001032190308905214054450080007503500d01c2c040300f01100c24113806210a11610311141404001850b44410260b81b4105841c10340d211812400c0585000c41d0bc0d640c05059190008104810750364000e04003440f96104210701504421800c041c058a40c5007000c0c45034100318140d0060010603042c0020b0003285215400220f20040380d64040386864102d584101c078035000200c2c1200540c64640501c401818101c0103e132000310321601542c4d502c4000020240000000303e00f6a8202e00c402d1089944900003d000000c0038507c008004d03000b54440e040202c0034800c04140059001d002040100c21100d91901c00d41c022020303413242d81d030b4540c040c001c01c5072180c1c1d00704002c2c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 716655512 1250 716654262 716654273
    0x50d121b080304051005010503030a08041506030f1407140f03010e12041805160c02040f180303060905160f0c0204110702030f0a020303030a09020414010909030f03020a090b16 77
    0x640c0521414580780c803401d00385459441d184511039052101070400c030042c06503440020580b00c1211f04c61800c10801d8585007000710f03980c4801122100f405080c51000320a100f140092248003038800d040b20307409620081c808030344401590103101458425170050202e02d15120031300f040c1c040e00080001034a124088401d900d44003102d400d001c400d900106080003124501070649040c820181c400740101d1501016007442000e00004803020701c041c000c0c1e0903055480300d5001001d403d607020800c21668510b184a002c0f822860002100080d04003200031412105038001c0350b000300e010040c50040521400001c2d03a8925088a008041224216603403016039100d02403c1c06090003802c40640d6041980140f600746400b9200704a5035030321008402c2c0c01a180002140d50101c1c0e000c000180000407480010050642da10714800000441c2c0000702c0d51a00c01d60014030038900c40c0c0c841000f6205820340c16400e90207008180c030f0100300c0d0030008118140034080240541152043d0629481d030302582c52 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 716656762 1250 716655512 716655557
    0x2030c010606080115030b0d08030c070606030303021b1b060a110601060309120e10030e0c031e190b040204050a0608010e0d02010e120301170f0f160b04050d12 70
    0x640002203030307070004208915080c105d10410318002d240602120386c0c0d800c049144074142a0009001d00000400602900340300d8069518a550085081c4065981c07801c0c0200a90404500402104002c00e80e103181d07a031340024010b44401083c2c4d04031081e01c418504011450704541c1c0c007803042c4840d581031a00140310a01403140a40001c0c0c030005254007103800c1915402c05030040a00034082000b2100c44541d5511840c0c0b2040b0b0340c685800f00300300203030074030003420108215607503a058801c4c030003a08000840e1040b1150b40d96114422070702e4007070381050302000d0b0444078440540705164444c00f040150a01e070300115800351040e4000b06482c0c6e5181c0c001800c5660b0300e16201b020790407075205101d03001e5080c0074010241d80601e0003081059202c00d080d020170311045c880c0902c000c000035000c0b8200f520507c034000a01d1903810988020b000c61190054654412041060340c45915071004500d100c1e012064a0a969000d4152138050300c10769104484000d00c0055141400307445e0401000505180300c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 716658012 1250 716656762 716656769
    0xc020307090c08061503130804150e04050f130f05030909010b03070f02010b01051602181906080a0f061d0d120b030c010e280e010513110405010e0102030c0106 70
    0x8002880305000300c4000d00c1c443c00a040c3d1032060540c825084440e495200036030350003240700310310141c48103c0d030f142610741440b8551140403000b4040301d0600361107401c9004400071035810745050003d65036258201541a0702107414801210404010a0204507031030700d1407403084c0c402c100322454068117100080c03c00000340d120111b8481c00004101d040e41c1d02207010441140e007400244011036007480064001e001d1281e0504d05c9a0f03d80740e2410a65880300c0104181843c401d840840c07a06101003e544030320070207516615000d09000000911401c00240203003119000380130941c07451207a55600000d424400044490000c01180620680350140144440d10300f1070740340c0c40003443e100000701d42a65100044d00b8071907004840841da807660054010000300f2400c88100c6031040035900f000c194000c0315054610854200e002c0400c803000c40b440307004d042e04c8080314400d1074401c17211914070a6904003000c1050010041c0000c005650082054900380380741401076a05000c07206910608540301c41c0d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 716659262 1250 716658012 716658029
    0x102d15030b06040c08060a1203050d02040e22170d020909010b0a020f1c2007090b12010209150906040915090506060a0230161709030703020d030c020307 67
    0x1040c44640c0c500f611644c20300440508100e8501d281490010f00016550f1003600c5a0098642d416401c262241003200c450380040780d4215145c1d0b440d13080c1a42c291200f150380c024050b40541501c0d102c1c0d03c201c0e040d54260780d400b42e0f00e80306609002e00907103580d030082c0c070400091640034060b4050030b41d51510720074080d040000b03055444d4403601c407000b071801010f004402000d4000d04401001c1007490b00700c1b90280300d8907040121f4009444400032803661608544070341c0d80c2c0501d500c00300d1903030b519801a58810908550a038440600001c2841c00c078800d0b503413010751080d604140781041d03100800140400d850300522945c00c8c036540e0440c28065801d00910001485a51417082c0300030304581c070403a900030301e0544055060044038036010791b59250300042d1180030310307104c1300c45e02c48010354413003c25041e044400e0081c0ca0300140c10611181349031691040722041c070003d210212000b01c0109540000c580103006209852941d001c0c001c1c0003801e1941a410400040841d030056202000750000501a81 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 716660512 1250 716659262 716659283
    0xe240a090903121803080c0304020a0807030302060a0515031b0301181a07050a270b070f05070e15190306061e14060909131211102d1503 60
    0x80d41082c04803148130101c4c1d08407840341213408000c41d5000003510742c03001c4420411399882d1590b000181e1403040580c004c0303a5901c5840800b204069011540764050900c40038284080d440303107401c80c042107400102c00c0740c141c1c0c084144042480c0e80d540c030000c80b01c4006400050070411640300101041152501550103e212104a030181091102201da01a100b458008d05200040b1401070940810f454000c141100c03d05801841940c0c0800b03200c018041c01070744a50315003003880d101103d9951303420241c80c540500c040c0092a107101101040c440d214041340707000b0b034030400030402070500c2540c11081d106241d000307004000119240305440180c800d850000e0321030004040611054501d580020180806140501c06d45440e00020380c2c1000b00700300c554032030a5590214845440401c003001a2040c0d501441150466400041d0000d80c2c517016410b8400381c40141c64104251807100103547c200207007514010181040c4922050a1081d9004000c0ba403955540d030030422101c5a5002910b428600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 716661762 1250 716660512 716660537
    0x14010c05070c050f0913050c0a12140f120d0b0306041b12080301230d2006040308073305100512060105130209031b0a0e240a090903 58
    0x80b282c100307000b02021201c1254095500c2d010a81900002d4041040e229011219000b001400e001c02c0da180306010300382c0c6449903610685a50102e41090003602d88814090642c0aa0940400e0b0107401d150362034020980034150049003142a400026000f0010703035182c00c0503895540030301c401401240980c903050191a40c100e407444605026900c02d80c0c2420601c0340c1c000000b01108103580c1100c2c0011060b44100305008036003010f0060003544030741d100e03421802d40c204020304010369030200d00b03840d41c082e01244030480a1200c03910170ba00001c1c100d50418000780300051200c0900b02134900005a2f1482c0d030f103c43d011098408403403400880701d06a1103400704482190022802c00040c0011182003e6190000359a03640345c0c00e060080f40d004142200d81140c3e10b8a96404a41c90420007404036480300c00d001d102c001083e0003807030229215007070440300010728240b079000c0340707014501d8699440e485804031001c1c2a41814454000e03900482d44a03000600b2003180e00c0360a0071940a52200407c0002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 716663012 1250 716661762 716661773
    0x90209160c1a10150c08070c030b18060907051e0a080d0c05010b0a140411040b13090e0c01050d0902010e04050a0b01080901021303110604050a08030d050702151314010c0507 76
    0x16000010a101010b0780321302002e170300050001038103402c2100c00395140704600300555000065000506032812881c10b0001d04200c0d8045c0384014454841960ba95407a04078925441d5082d62003401d42c0f000940440100f0b80080542010101c400200a0309009075100316140c10085c0118000d40840c2420842c001817190a0140e0325898600321483d0300514208000c5a82c0c039090780345c010b8043c41c0d0303409804500450039011a8013804110710119103c4601c0045880400c3c160700410998030300388409560f58010000b55801ca080058464605010304280d803900203000382881641000305900c5070700e0075501c3d5481000e010380c80e0b00b040490076071000d10025000c02c00190682e803c0e680304001c0c220641c0c150f004101b0a4a9002542020544c0d40c00f00140d0b15000b00d801070360340845100d00c0041c6614001004159000701d2440074442076035040c8042c0c3c1c8560124a082c5650081c49000031540414581c0c0196500d01c20b200b118084100c180303641d42182e00d00940341012a0b00000c3c480d00788103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 716664262 1250 716663012 716663041
    0x20f0c0a031a090c06040807050f040606090b0a02030412060617072d0b0406050c070b090609040b030f15010f050910050121051e0109090209160c1a 65
    0x15280100180c0c07850341d078240d109034110301401e140150500426018a410702002d819140020700a540319a110b044443e00ca241074440c0781d2140c44074841c03101090030329000d200100e51894842041c1545084807010700e035070003581e4003c11030204104c08540748034140101c4002d030b07028450015225050042190801655a1080d60300b607000301030802c0300c00840c220b160703801420300303d400035034217601200d80386142801d0b0042442481d000c40c3c04039041d03906c6000307028441040011103002c070f9910314100f00341e84145100160410420010969a4101508012010200a01100d904000e1071700c044e414a85101084414024001d004011010000041038090402114222201d00349046000c0080c2c1c95881403034180421030841e80c1c09025602020340700a401d1140c140724030301e4102680c1d8101d50907990f0810070380b11072030004075121400d481214006903024100b000c194541e2081c25080c020240320b05000c000031410300d200010500007815250400c84582d0b07500c1070070040118150700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 716665512 1250 716664262 716664283
    0x3090b0604090f140a0f080c070f030f060c050d1b120c080f1b0c010b0a140f041e06060305010504050703090f0f03120e0a060b010914060d0b03010606020f 68
    0x86080480c5000458403072103c5640c129449101260880d1004e03900350306001030010060900750540080905002005009000c00000c0d1020b0350645500c620b4031069140685c000074000c22144900c03013000031616808640c0c2c000c2c0c035041942c2040301407100102a00c212201402019111000c110103030303a00861b03104400105007200b40909504404014600c00d4000c200c0b0b20309020b440c011400300c490340303201400030014091400d503a0725200c400c00f901030b10310180c189004d030707071a5800001d850788401c842c00e42480c0018000340802e20794008020103000090b1030101d60407062661142002000e01c241002804176880101e2036614217800c01c8120741000b0102410f0608107818180080c101a41c403408280c1e000c88138141041050800b16861906400c883c641302e80f5207801c15241c61000a9202c007050b1003528280140030000c401180ca2841c070344500b00c5400b04041303011055203000130241030240150f070400921200c00800007402c1d80c426030300c08400b50300324a200c100505030500442d10030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 716666762 1250 716665512 716665519
    0x15041d0706030c0c0b040807020411370e0406050301020c0a06140603150414010603060b03100608070510050f220b0c030d0c18032102060c040303180f0603090b06 71
    0x12401c1c460750142100c13050650042030081040001002c0100b10f83c10750f0030460300540100900c07034015050a1155000310301d950000e44000e05c887d9944480aa8800380413021000600b201180b400800d0b25800c4411100031361042d242d20001c02d0980382403028020f900041300c0140b0140d24079080c41411140300d03030714114200c01014100002504d0000b8201c0c0610349070070a4034025039590414081c03c007102c01400d140e5500304800002801055082241d44030011400e59441c0e017000a413000899015214841042d04800410031061404451201058060342003491600490800d09240d03076002c0c58200d4011138081e0601420101c180c0c0c10036000d048411071140c03501c411110496a070340100205680c95075110a03440c04502e04c103600e0500540d0032811194000d42d00c91500d80c8048203550086060940210542c2c1d8080d4400182d19002d040d00300d26031841c0c14203685007141d084811420781450310620400014070b40713400d40d651100038081a41d0001c0d54900920785002820400303080d6910 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 716668012 1250 716666762 716666771
    0x623190c11070b0703021f060e010b120601031a1f0f050a08040807030c050604050f0c0109031e05071d1005060708031f0f06081006021903050315041d070603 69
    0x410390000250241502c41e00c441103138a4030120314040740f500c41c40401425105000e00d01c0042a1052501b28200f50380c0c814103054220307a01c3d00301000003070084242c100451030701000032070502c4d4041e42c01110b24032500343c00f0900003407148000c6042c071041e80d0049084007400071340110081b644007804903a040f8461a006140050b0f124008101000242005d01210381c009180010580100c11207a80c1540c000251021450a8288292621030b00c40c03803441a401540b410441d950711400f902c105803540100c89240750004803810000c40c0112600880307007031090390f5000c10241195006134150010b80d06689025240203040580c50000507841640100c0b001e00034000062100c806483e885504940008989461804192070300e0001c2c1e8480c040c0d5000707013000400c80d60750081200d032091081503c440200b03980d51004036922044141c0b11440340503c6003c5500184c811001103401c001e040713105101102881001801716401c8610a180d0121220480c0248640070f0010381c000302103070b040410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 716669262 1250 716668012 716668037
    0x803070201020d030b0d14030307170105101b051501060e040603082b05070207050906030c060a0c0812010e0906091203130203070f0b0c1c0c0623190c 66
    0x3d43d915aa10454028075031650200e14650b02c84d0400c182404e60070000240c84107000341d14043c0c4070744c01543e42c003002642c4c03003001041421096020b9070403282c02900c140622041c1840468030110404214466114440e008802180c0100008142ca004504040d10702d075150501c040c0c40c01091b080d002c0d0045040407420008580e1038415200c2c142d014003040303502d110301c142c002c000a40c0221600c1048500d0401804222395000420f8419160152400c1c07107551102c0040507078800b1001c0c00590320001c00c00800003001d103d120a28686440f45070614100f140300c0002c000004000d0300040c4140c00e10104001c0702600420980b41c1005016016040001200c240d07200303076200c001c040852400d40040140c0454804201503001014a4800b828640d521060000c0303a99004e558065001e1140c200c0f0201100d103811041980410140c4842c580386140e0307030b0740c003001d8050407000240340c103426000a0601a0300525461040840044151140340002c0c0c3c03002c12281c001480c4020040c0c07818082 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 716670512 1250 716669262 716669267
    0x61b0822030e01110f1b0105070c05040b06070605010602011b110606011b05070b03040303061a0d0b04020705011b020d0c150906152912060d050106050d05160803070201 74
    0xc92140e41529120500700010320060394614211039a850381d51240079003007000fa02000c18010300264540107102c240703005e6030300111018090700720043c0540141000800292800703920070b01c0c0c2d2503005403100381805500c2c3c4a40c3d0455409074403020260b51070f1101c2d00c0205800fa04480280240c5040008405451020302503507020002c00c0c0d0350602c04135800503040c45215415083c02964400115008685c17a98555015600143c500714003080c1485030100d200f0300c440100e480c0c43c0100300b010905013127810041c6c20103880c1030075280f900190b080000c1e2000c03810a02034085101c80c603d44441c0c01d00c0180100a24054078903403903d0070440c0b02003a800014003029501d02041311210008500c0743c0550411800400c1188000d0600042030000011189112108028811034140e1311a00b66408201c190f400b0b0311502c06440680c9525000042480c03512845014886008200001d030841e200c4000c1540400408010b80d41a40118a21005c4410b904a61000380045201660400501d81d001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 716671762 1250 716670512 716670571
    0x51c0308060112020c0f1608060f07120e03071719050306030f010603050f060c0406052205030d030212060f0d02012307230d02120a0c061b08 62
    0x14104601000421802c2c1c2c4200480d09142c028080c0440d510b4902d400704650b41c402031200c500c0c8074090078508261003910300110f002100c85075400b84c4455521042c0d00c07402d211004003140d080c0702c801141c58009022602c2070401e88501d078801140d0350b02160810030084084681b441d43c0b03120f01004500344103120800c00402c0c000083c1845030b00d0703449e180300182c03d041d000000f582c4690b2801c4000024440006000352002c8125001e40b20207480d04480d000344c80c4110b010f1040403a0080001c8040c1138008038100c103001041005411416440e84002401c120701c4c010b1240020341c0100e103d0141c203194411680d0440d200310b41840944401101045400b01c0c4403201034180714a1480a52940c0035400c108000000100d82265840d00989403120140c0007039404010042c40d034180781c0d1014040052600d07113044d4a90010000401c0460034004c495000c032241004101c6446c007a5000a400c2e4010030b003124402d00310710b00e44500055801400300c8002405080f500558130709501800c03200303100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 716673012 1250 716671762 716671819
    0x504091d19060207080706020406110609060103030c260d140108060622020307120501120f081b01111e04060914010e0306180c030a051018020a17060105 67
    0x1c00c44682003580c1400c000078003614801a00b1076100265a504024041c0d004000359103142d00c031000e440c4510005550b84500440d00c0c104164040310060010902a0122080c110311440d0080021159180103801041c00d440460308030b0040810108a000d006014003241e00000700034981e2a9031400b0b20003a680c24014180714010112020300c2c0c0e01920b03020312200a40085402c0555403400d00702001080405910000551185404c0000c1a80300c40c6107100300700300d038014511120580300360f00c0310812640403d2059600c010015040080380a080c0038030030a60141c000d02584034602c01080c4840309090b204402040b00c800c00051103900e400405d101d0541e000c0b51400483d0030505001600d10b001e4205511364180324110401401c1e041000030f0b111040c0305101070311350001104086c540d40d8010f54000034500c0c0c205000740000c020096101c25070b001c1011010008064840e00890030500d129008036140070141c0003071796040d0348100811801002c0594442d6401100660600100ea080d0700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 716674262 1250 716673012 716673043
    0x5010e130c0b030703090c03050705010801141806042003011e0b0d0207050102210615270a0e01080318030d05040905060f04110d0b0d030203090d15020a0504091d 71
    0x10100c4c002c184258030011400d50700840c18015207450703040ca9940d83c00c0c01d01c2050b00051108001054180300440314450420b00a02500e502c20803d1080c80b14602008204c940c010f0343da485104d00c5202240424105c2030007200c0310079070307a50410707104915041e45048198030350300c406202000121071010480f00100c0c03c00780016181da032036107003640c0a441020054200d0060b0841c00c0d00098100d020b41303034003c03503045981c8901900128100d407800e000d001680c07101d16110390720b00300300c1e90b100c12005580410002d101100c040c1c0c844a02da0000407003a08190150341c030206000b00c01e441103a10f408481701084000302045200c001000f13180c0d00c980d0062604081e240c50201c1e20680340c45480064040008009200c0d10a44807500301040c0c0005640d10350a900340301c1244864102501414000c58155020707515110b11881030281c2011060b0741110614800344080d03440304000d1000d0424011180d0f202d6585a140007020000d40e0244c4103811155a1000869000c440000462107003525105 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 716675512 1250 716674262 716674267
    0xc0210021213170a030507020d0827010f050c190e090c0a050c012d0603020901150212070b060a0510021c02030d060308030906103f0605010e130c0b 65
    0x9181941039008a4100c0a00310f01e40030032540c0b0b0003070f0160003003449040c0c1e41c6d085805d084003200e41264420019259405185030424110350703000755020a82e25010340082c00840e4844c03034403500c13004640040750040509035012407609041d41660111000d015802c0ca4182c40c10361245000841c03404018003808088503000850800e40c0d40036400362042006400b000300305000e500c1c061852072031001c28443c103402e0103048500720708041a10640090342c0d0007030144101a800e02c451007206000410140c8198880c4548104281d481c00000b0a0810720a00129a843c102a0284103900d80e403900301510070071170b171104010400d0703000460f554660340e44000b80035060046541642188181c01c6544110b42c204603002c4140031000c4011400703804a00100c0c0d459503501005264a000c090081500021510b102917003444003201c2001014610b40d68407080c4522840248804c405010501b11035141e155401048024440c407556503100e8001403003450350b60103031707950340d44c0002c554000c004006001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 716676762 1250 716675512 716675551
    0x30c051512161106190c03060806060607030c02060f04030b07030c020c010c0c05060f1b060103050a030807022b200a0f051e0318031204091a0a090c02100212 69
    0x8a02d04906071960f101900c0b003505000c101d0490030820500b0800c00e2a0038181994030083c8030b80b04500860307910001615860302c8500c00c1212961140030250100f103065244170000da500c000040034100c2c00c00364030f990355501d586050351610b50b004101e0700078103203811203c4074810b40120703160080702800d1801d03008240791440e01008098503504a15040600070425206d07589050700241a11030218540e6500c08140381007559540300c0074000104940c024281c00c00000340190403240d000f208034015900c41d102030300d0001c00450040031604c4110b20300182c40c418090307000790105000300c169401d40c1800d000340c200003603600c1a10800040c10746102110500c1440001c1c84420034803043c00300300b140c030814034400c0d10703940c6e070041d0003030a48500380d01344035644500d8001560308007105100442820f107450300090100400311404004c119034490500105035954251041c0e01502e9010380010741c610700f03074400910b401d555010340e08219204000060101c1d958011045e0300403801180a03601011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 716678012 1250 716676762 716676767
    0x15020f0d0309030c0639180528090513030e0904022b0807110316050901090509033a0e0601030b1305010e0c010e0105120f10050901030c05151216 64
    0x5620018065222518101600360621ba0300d80d815100307040e035607194181241e401c415071240300c1c911907a0b50120f400207004480542c8840700140307180d420f140b1103e000b0b544458041c00d0360030442d20117018107000b8210300d08040d00201c060107001c4c4140d600315160314190f8049948100c442040f915200100d603452005001020078424040e64401c000c0b40d200c43c031918080115200800042d44640076104410b4040c00b41d1104c407004680e00104001c410380d190000c2c3c00010400908110f0103030008008120180c0e140c642c0320f49018101040044149102e40c413005100c044951588030741030708214a01c11680000507080c2d05403504049030710f9054580801140d409a1604001412035080032008100b6881c08200f09812000a889100b450b14414004540c94441c0075420151000440b01060550f04031014941d03000c5a40d54032407a0b031070b071180e00041091b02c09034030881e42d14010800510650070b00da4070101c01080d1084d02c41e400c06901880c240c611680090291310500c22804040c0850fa1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 716679262 1250 716678012 716678051
    0x1006030b0402071a0105040b010203120c07060e031317010e07092f030402040506010e030a03081914180106050105040603270605090d020615150415020f0d0309030c06 73
    0x21340c4114070001c0412980c3c070b2001c4c010700c24801c180c8600c0c540742c00304213254000700469401c004818021503c41e5101c0c0c00c01080e580161700155100c0740d49101c040000368040005103840c20b902449846000d10300180d18100745401d0301c049100b41d0500100301c150b400002040da040c0d07000e100000c54040d5280e40c0151032160704152048104040d10070021245054000441c0641e0080d60280160796424006440c2e001c07402c00c01e19010f40c008440b0070046480b03844040c0c0c10880b010311070740d804d095034101300c402c1d03c902d014260b054039080d03002e03c41c494a24035110541c00035488020b00800d171030b200004e0180d00491160300c05041d04c801c80c0444111020109115200c01303000c014418026506041c0001d00d412074003e0720078400c002c580d414450000440d940304542d8032020784680000c1c07509001c0000d0001d8000c0302a803038140004540015610100c4080c0801035004001c1680c1c1e00310818900019002c3c50814035141450250204e40d20149a00c07800c1d41140012404400c08103035104401e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 716680512 1250 716679262 716679277
    0x10c06051b0301120c080601062a0813050a080705010c03050f090d150b0405010e2e0e070206011a040608090c12071a031017100519050705031006030b0402 68
    0xa900000c0049031030607819100130300040c06103080c0c1a403980c071010421303038681d42030140401041103e1403070021071800e074907202c101c0c8003010002000140300b0b0351108215007040890540030f5130105400c0c0081d0401843c6000100003000c0203044491400300060312880c42080050100a40044d0003100100018100d94401c040908080c010b005241800340300b9203081002940e4490801440560340e1516028030b9040c2c030304441240a503600e1790314500100c82c40c40c20309080850511003604c00300744400c004800003080103000781202440d0242c0000c2c18190140c00909811081080d00d801c0b180000080da4142d60007405d080282c1e4541d616031354600302d44442000e41c4201125a9030034840404100b031000c5a9015418401c580c0710100c610f042400b0803500001403280b8032000300311014078900e00d900101d0084040c0e50303560050282c00710940f8021940c90300200e5414400058450045c890150301140078a002800c600742160081c182c282c1c94480c0d04201600c800500045d543c50341e0403141403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 716681762 1250 716680512 716680561
    0xa03090f0f032a03090b1303060603050c0f01180527250309051c0509190e06010f081f230310021204151d030720010c0605 54
    0xc101c01da2a0003800e03041c10420700c414500710105400e4589803840706031000c0e1039058443e0290142405209800b03074001a400c40d032011621180000802c0e0f081c498680550300400144c10144003001c00d0100216032918528100440450545a03420038401c00c80151401150310022501040740b000070042e4094194440068981c0144140c650710521040805804040c8030303d510f030803841d800d03400c0703682081d0060300e40c0c1c000401542c2c145031848404216081d00d4242142000d000801240160b01080c02e580e07401e1a1419003844070030380010503558041002d00c0d001110705160000107180580142c0203a95446602556041c030010341400200a441c01e0038100c400d500072494954507015007103031002d0080c0109042c2d141255454001c40708502110780041056440d10341c0e0708080031120000342e144440e51031000c80034801c00c2040010029000300300442c1c64507114101a4114030302640717040035503d00c414101c6001d0f600540d100410680000c400151a03450840301ca400c4028110341c0803e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 716683012 1250 716681762 716681783
    0x4030f08280207050102160b1e0403030c0303110306061207020c040c03060e090703050304060f020f150103031106060f040f02071a0f0c0a0c11040f060b0301080c03120a03090f 77
    0x80c0c01140c28540700d080180ba400c8441c03480d6144016600c2e8101c01105e208080a8090306002a122005c020203850000d85040c0042d00305024205016070440e4004a002540700c0042c101232652602800486840110303c10703142d400c0ca140000c01611410b8280000712049200081d8858002e0200c4040e00002810508c1889582400103009101c1d601690060110803800708600c120300040e500700307030781d4040002c61600d81040011341b400c4000d040610110f01c22401c110322507000500000c5e40242c16942c400c0313003e50442c60301a011003568911703400b095101004010b410b5440075166000c1201c16140055a4000360350306802030b00c22034001030b103080c1d120b00348952603000b0000e20521031a541c1103005140c0d1640b81c0031010710701c50a02280000380454240b04045044c8111580b0140001000050400c2a54901c1000e40d038081e80b0044425501100421078410107002e41201c02604034060618801018008034080c0500840750042690ba079451004002c030743c0c0300360b041058100c400c03c3d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 716684262 1250 716683012 716683057
    0x30a0e040b041a0301320c1612030b120601051005090a0e07030507170c0307050c0105161d09010b0702030c090c0d0b0d0f0209100902070309051e0604030f08 69
    0x102c3c0000c5812018080d601e020400f07208011020019000752040c0c5c2155640c2d0700c03490b041288202809015042c00c0b0f141041210514003c0e8034041901a101c0c10001c0a515100c40300a011140c1494803103008017812181c14440d42404035085040da1030031079401149400c80740c1c0851300d600130990003d0704060011000700d5925103640400b485203085035014030082e511100119400d8040f11703c40d840c007040c03040100320b40580140180d0f51000e60340c03030000c0c09e11141c10411801c0d510151b071a02c08075403440020130710301d40c0d01c010201c008146031074000b901480000040f400b102c6051103904040390700403035480304543d400d00038294020300c0103024000750300f4410381c41015035024292418102c2d1402c2c400038400e0804021100c1041d400010f03c1e02c04920580134862604c000510586440c0901040070071038a403030b84007503c1130501981d00d01e5111410700062103031032106500c0d5a041900c000c42d0b41302259072030310111819203900941c1520040c9951512409602400d00041c00012070681e6a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 716685512 1250 716684262 716684291
    0xd1502040b0a050c0601120b0103030e0625050c090c04120f0206030106091e03030509040f140106020c1806030c01051615090605330f0a15120608030a0e040b04 70
    0x30110348580405484141c0d0740e070482c0341c003044101f4000400c0c458800f8010804a805000c100240b01000380c4041c2c40d11044402d840d2001d041000002c08aa00844c000410f01100300061000e40c00196401000e40c00c02100050540c011032103407028044014401108229840020b41e1a407070b4042e20243d01c1303503103500f4083c201500c13038003e08484104c0c01442140d048a40c3d507020b411030390540c540c107103810400e40503c0050608508603a10a5850788060581d484642d40100c1c000c1190303501506110082e40c013040f8005600011600d2200d801a00384481564080b0b000b14283d0424200181e580804220039000f440813540058800801454004141800c507040002418845c102c00c1004e0360343d41e5002030200343c9680318141c07003180744072680c1683d940c1080b02003881040144000007075850540011020245900854861102000c1e01a2890380200344814a0308040d84180112810800041c1d520b000e050710070b40800500b40f1782c0403141d480b6a13001c80720000016105214082540111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 716686762 1250 716685512 716685517
    0x303030705040e0705070213090201110a03030b181006052110051810030213020d0609020c01050f0903070b04110d05070609061706040507110f060f13020d1502040b0a05 74
    0x3c000d0000200c0c0c0000310003510641c1103440c01a801020081021050600b0030018a80d005049040c00340d5619510100c000800051500b03d200e40d1b40032030298208014040301003947c15840628415090501c000703d0410030300b0070240d17220b07481d025803980c07200da403c404820030007284410008905420301400f62202d03100c0209507034042e107811824a80500849180070303800c41d486882e44404100030b00061400c3c4c4c0d5505001400c4000c0541483d000070034207011592990b206424040d800200d0030251802030082551140b01c20b26856841e1412000311502ca00c20040b00030f2180318208006000c2000758100c4840650016018044c011400d251159441d682da001d1b07032020a841550004a4901c980c9640310b0b04600700d40f4640c00780d15100148000340201912600074801c0b020300e44508182e00700f0a11281d00541c00c014001800e000c1010941008090700f50074038070840844603005a11814a5820b9083c0e1110072544120068040c0c44028007407508074108200c400070b04201c0841d4000301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 716688012 1250 716686762 716686769
    0x30307080301030c051f05030f0603070504021617030c161a01030f0203010e03040f0b071a132d15060b030907030c0f0323120d051602010b01021e0309030303070504 72
    0x1013040c035007031784d6046c001c09201d007660202c40029000c000194880200c0154260071010180890340c00c15102d8000406981160071b08810b10340030010340c4000e002d402500d00c1007414a1661141c91824072401e140d110744a61012a00940d0311490000300b049680080d5007101191010380380c1e41540c40349451004000c0044040c2d00c29030a146124101410100c11101129000802840a5841e2004c00c0e8441e80080c032003607030765034102c0c1002e0b000d0680c40c0c65018030403007a050040c00003042503e0040c200181e405c68845009812440b8002c605040303848083c420b9810040305a07039001860405405000d0f280c02821100310040700b885204540062903a041c0c0380314244602045071201b9405041281c01c0c800070300388a444050061700c090b440400710390750303901805c1907402c508403601804c0f1196000014107a412541c80e03003040400b001d20004405008100d100034000c038143c55000135034413903500300700d600000410310b0b071a11040420400c6031907000d009003d490b00e0b4075003d03102a059810510 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 716689262 1250 716688012 716688019
    0x71a131805090114060f01120f091208010308030c0705190303021b01050613091a010b0a1b0f08090109090e030a110f15060a0b1309060603060320030307080301030c05 73
    0x801080507420113000c1c0a048051015442c01580e4440301009811207580d0320309414800c1c0c0c401c00c1e1110741510f0041400c108400500410000034611b401c1c080012940e17240300030064020300500001e10450708585d0001a80321180c0e403260840e0502604010083300035a50801c0710100b444205a05500607005c0e90807403030301e040c80c02300c1903043c41030907642c00315402603011244c05100c5030150344550154603114003d0035003144088007640381503008042030b00b00043c140380220b000b83c1080c0d8891041500084994001d816034a482d581c1d95903040b201c1440140f01000100b024642c0340d100d0b2001e8001003031146014403034201a0002c3c55144d030301040703003800003880b08011716030100400245288900c10300c000910610484104a00322124003034174081d4450321000001800ca20480050041c81c0950702404060a00d000c03010401c544241d0b0004050500340b007410404508407400503e240c408a001248444124000281c01c51059100c0100f105030701000100512401292762425500181c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 716690512 1250 716689262 716689271
    0xf1a2101140406082d120d1a0603060103110906071103060703050115081e160f110c06030c04091805070503011a040903121d07050a08071a1318 63
    0x40082c0010390f41a4003c1c80341c03d60213a100b103000c0d81800030444030050207882100405182d11140c65040100183c13000c40e0b40c150104a00c410003091740b00c2e1301010051111303640900c4048501180950100520540c10306039103c21800e640200300d0219a810040101044d07078035040d81c506801e051080c1d0021034040d01c1000000b80c100e038040d1003114113a032820340494100c0e0343d02d00d90451700307041c00500780460781051103078444a800b1140c00e61401600c0001403440c4241028100a080c01169184201002800000d040700301c800400c61000c03503801500d2141c1d46c0d944410103040c0038402c541c00340307000501e000500d008116000c2207251305513109600365609540d0360300c20503003a00c0304400000104650b417050102280b8080d8028050f00c1d00c282003121545054070403a0084680a010380100300c2c01e60526001d41c10020f000d25005018100c6040761203d040020a6a540c0054010310030a0014000c510781314176010015510101540803030034810684540c03009803054036103664809071a040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 716691762 1250 716690512 716690549
    0x1180605060c0601050d0c05090109050910053c090a0b0c030103080405090618070e03240f0c0d1a010801060507020904030e0d02030613020109050a0f1a2101 69
    0x1c0e00407540c03400c0c441c42c01401540d003000108154214003450440d10800301d030070000380688074038420034003d141000c000286413502c0c00c1060b04000307540400300c082620f040b04100e0310308180146172015401c5211414100340d02c44688081100e41d003c540101c04200300204020b4210020344a21814404e10b4048569190202c042519001c20b00009001ca034061005004a04000c05c2c22548000300509400c201108203540c0c0c8910941961440001a00800401c1c1c4a0804000080c980e4040c42c0c0307010b00c03042e4200c0d01c85003c50741c0503000c030314541d20160129514418600c107848101c0e0380f80004100120a8100c0844105428140240031880d0341c400021078500540a0761111500940041c1003a40d07165400ca070f100b0301c071401c5507501c8075502c1244400b5031000c0109a200e544c0c101c811031090440342c0000342c020030007640001d1081c00f0300700080c40700c80d070404900700440b00c41480c2c09810f10f54681000c0001e00031001c0c0590964000440400035444c07062034903040341c01000c117001ca10b02c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 716693012 1250 716691762 716691769
    0x110301200406261b071a040c1a2d0c061501030501061224091d0102070f030815090a1a040b01051e19021b0307031119030b01180605 58
    0x40148080f19505010000d09206841c0c074048041c0740501c0701c440e04c2c2000b240e80c0c01786400c0d07034241c2d20600702d41200701300805c0007035002080c005440f010901e210040c01a80030070f00745108030328068006100007450304160007004c0d11621452210852103540b00d100c0560259582d45003180c1c100200182108100005d500a104140c144c0720340c0c1d80c03071601d91008100c0c0c81c0e011340034060074501c1e290b004031000500c2018404080000c0c05141101080e01c45800b5500e66203d40c1c50104207400343d2042052400044200c2100d01182d54541480d00c480e69408410305458643d6540c0181c2124030b11040044900b200d40c008034142c0160f1020b400c82c19014030500044681000405010541c1040003510414141241d001c8807403e20141d80d14240102c032000302c1900200d444e030000750384000c000031251180020400c4103044140d0040c0090342ca1030300c81c806410380e10f480140c05154400c04002203045000d00181c055900500199003650b5281d025040080d107103101040424034103000402d4618 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 716694262 1250 716693012 716693057
    0xf0b031e06060904150803030109060e09060105090f04080403081603030e0a020310020c0c0d05010b0a0603140f0a1d0606011407050706051b0a06060f09020304030c110301200406 78
    0x30806810b590600f2815814032005003010507000c01e00000883c1d0000b06000e040000354080c00c081c0300046682c40c581540c1d244040c00c09080d42c0c4240e00104018442900c84902265002454092510468859003480083c0c0c0c03055401c064a205e00c00a0058412581084039440d214441e40c1d040203414000c0b41c4a80c2c80d01c40c03002000b54181c21282c000d0701900060b0300581034041e04103050302c00c0410850b00054540020f203170101c400e42d448508119680c0382c1007107028010120307403c040c044c80c08180e030b1142e5602c800401a68040003000d000c11000755450f8403c0341c00e818030096038200d1908400782650780f60412640c25000070b0b00d00038000d05030a40d84041e2030f8810307808401401c009092190681703403074000c51320513405205481f01c004030140c0200007003c0c00c02c1c000c03000020900d0909108120079201c1743c03c03442c1c0e554010418040029802002c01305415007150300210185c1c82900041e01609440c928000281940c0c1400c400c08202ca4000b0001c84003651900750840e00003a0400c02e40c072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 716695512 1250 716694262 716694271
    0xa1107030b2d060f04140406060e01060c030219030c0b0f0910090209010e040f08040b0c06060604061b020f031605040b010f20070314030a18050d0303020f040f0b031e 73
    0x400b0034002042407820072001c0c41c8290039008002090140515103c5a803682c0c003128150740c81500e075a4100300c0310081c900001e0140503070f49012094201240c802035914407000020349203121500700490107040c45004450704da0742d4005040daa02e4180305500b05d041890079034108489010300c20303020808802501c10f80503100e60280c441d050301ea00c0d00d00c0041e01c00e14000d000f921140444820003002a1401e0001c201030b0003501c0500e03441d0307400b00f0641031419900030021405490700304028001d06801c061094800800609001ca140113184003240851003480070042e0544900f00e02800c660f00d24520356002e441090b54200324070f001d100011a4181260b11016002c070342c05e452400e100845071003117000f02540f000c04030350409540365030b2107001041044500c07a003600b01040c0094004e5210a55403041c1444680c4c00f001e4508100020700b6441038440004c0a0550014041c0c05032440007050f54003d21080c0352a44100382d480d484d000c403942c400c0b58116801990901801007000c0c0354404d40703004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 716696762 1250 716695512 716695591
    0x30602090f0316031410110301090b010e0904060b0409021f0224010510030207080403141029010215010806040212010e030409230108030c01061d0604020a1107030b 72
    0x242c3e403031519190407400c4652809074030343c000c0403164010980c2ca070040e8080c00309103c4485030b50790700d04000c102c105c030344005500e81004090055610300ea903610071100c0d00035400240010306a2103c07000500140000319000b500204c0d0444503100d1221080421302c088146602940d4100c44074100342000c154112031544200500c2c11b005001c0745c240340010005119079410700520b0005107844204854000354021100038088103145c40f80c1d60b0050107a0650054418014084000c4002803c1c1401c0f00b0343c3d81c4001c140603130607a503803040ea00c200070350300b408045414410341c1542c40320141d0f5180c50040300c080e4080c1000081d0710380c00c02814422064a0000b80000e942081c1c280700107031000d030940c12880c2507070344071103981140d142a0310312226009101041c000c5a4440c81c6c640601d0175100b491b800040180301003848100c1e40600340b404160310a00451300103a4445500b10b0039580880320a160b81c2c20382c81000008001c000070098a580540c10030342640d80b0301c0010081c0b440740b10243c181003041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 716698012 1250 716696762 716696803
    0x1e02010501150503190204030b0403091202031b01090302180f0c042702040302061204150b030613210c020118060c03030506030c0d050604110405060102061b1201030602090f03 77
    0x2c1d1540714001941c0c10144400503150780130703481030880c0c1c00c1c1d070025081501c095003174000303010426401c0b8900d00010f0280c0c4082c0e180f8003205800003a10b64882da168050345544120503250350f61300c47c60089000e158000c2004000d644a00110071030064100c070102c100c40d881e0004a0b500b603208030241d40c01c55039006410003110000c101c504d441c40400701080307000f540d024032020005070340c1c0f40f000e86492140604090150b140505003841941020300c5490700c00c0d03252003c00400d94602195075039024500d00401041240e041c50507203502101056404901c0d00498511019560f1043d021000300d0b0003640c0f882401742c1c4c1a00f15001004551152001282c000744105000a020b5080765130702400040035120304041020100b000d5001c42d490441d042c0d0048403c220030040704c521000059002039404203e0b81c9020b0700040d540311006813110542141c80d040071108000d40c0f00442d5401d01649050102c256500e14050020b504000200c520800c0300340d0780c00c00c2070b00f0002045003625000020151 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 716699262 1250 716698012 716698049
    0xf2d061109030607050a1b03020313061d040e0c030304081b060310090f0902060f13080d081f09090f140c0102100f060801020307080910051e07110d1e02010501 70
    0x8030640d01c098003070000d0029000e5000c145170340c5900b815107c28017039006035070b907051f40d401e299012203e0368200f0000d100c9a024000e44001034850302d12a40390083c1c0740050701c3c2c0158a85240340082102000303506200000c1c010402a40101c7c0807074881c188400c04890100a117420440280012540700c0318690303582204000641032508000b0009110081c00a4901c1c40354000c00c4040d03010441d102040c503000100300399621042c02d075600003000f61070044d040d503008210307005080180103400740c9190002c9060200743c41140c192960020308c050841000780d9030702e0307141000340d15440f1882035410700742104e11111032110118190919002c164082d11090030842103400042081404800c80d565603103201042e88002440203502410054554011901d000300105107402c501e1051901854185010720000280500d803040c40c02940c52842e02d9560b440c807904840c0d80700c079099800154030429a413052070380d07005000e400030003014420070f03800e401c0b4150701a07090311002c0c425140b030550064076a1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 716700512 1250 716699262 716699267
    0x602010506130b0f131a0402040b09150d05011d06060a140c010e06090a060b1e010302070212010f0c09060f0206040803090f0d1d0901060c0f2d061109030607 69
    0x2101031004102d2100513442c000819103a402c149980800d450b45c42100c80a2402c00c01c85960003c2c0e02207030194603040c20700920621f14000c1c2c9801900884208070099041d058a90560700c500d02d172014100800d69480c1000744018a03ca1803000c2500a20408141103003070400031a0360b8550705880e0402032540300e41004d070b03d40e803003200d1221895694141d0403046003801e202c0c1d40e0049490b04014024404c2170704050b821a080e00401501c00e50042100c02c045112983c80d440c28048e0900300181c0302c1040d0b0010424014114403440210351070204050000000e96000c5244450349031748440c002a04c0d888103584003025003414401507444140003500240b056001954403d030140d058940c40c000d074107070161401c00d032500f0f02408160321600700f88030a00c041710b40890f0100101c034400d4481d49400c2c0c014000340c0c2c08003c040d20b02c00c0103100700014007505800f80084ae207032103248600709403406040300302c01c403c00d81c8045034098109880d8020010503031054a0035500004c1c007401d466180d1300c40a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 716701762 1250 716700512 716700521
    0x14010e1011010e0114040c05180f0402010c021309150501050d170910050d1401050108043009050a08010e060c0304060b090403031a0306091209040b060c0d09060201050613 75
    0xd0340055034961001c0c210f030440a01030b60200707449082000d0001d0902c0e16103074440c80c0c2d00340c00050168294044448036103148000543c5c0000391a0b0800410380c0711400100c4442002400280d00240d402d191b05059403041d9220449040c01031140d001000880c50203001683c900313100d001da000109104400c0818003440d1903034144146500da540c038058805000c00c60002c00034491001182e40030409410004542c01210540c04c01b580000380150304000c0044d111100c0981701902c2c24030403814101105c145010384203070014030300703042c1e03014400c07030b0700008041000c41e0181500aa40101c00040c4c440d8050144508115104000d4040380d0382c0c0101d00c5105410080050b165292112180f04c071584403002901d0285020703545c04a504500b0030103103c0e001c03c0075180e00d4040d50050003000300e03160002c690b030040c695203103102603501e0301e41400040c040c0c07013101e4007140d120070009109101d00703000280c4680440c42d1500d440d0010b96683c80160308a910848085401000c8008008141d40a9070300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 716703012 1250 716701762 716701787
    0x606030c03100b060405100522030203060f07051215030c040605060706150b0a02030706060e060f13060f0f06091a0304080a0306180f1505030a060510051914010e10 72
    0x10217400c1035a901d0009400348804000200801e00005044100910f12008640c401c1d507524442e0780051f145071b000c40d689560041204c80c51145600c003140545219004840c0841901001c600817030030f1030311070007007500030785c280c200c3c4203105034800b4800506050150100311407004226904043c55900e070000900400002c0405456243c0e40215500d540c0c40003030078488109500071520f0340f185140413411140350b90403000c000711f0503004002441d0396161082d10307c01c4042c0c5031034081213808151a4007038401c0d03400c08841102444004140780382c3c140724400c00c48603079a0341c400181d0350720070b07600d000c0441258500030028010070025000c10200d100400e4100d541d494009007203641c80310076a2400c00d04070100c584a41d100c140b030f240d8020050103000c800c00c06010040011500e404000381da81c040910340180040d0702c4a0014400c82d15600d026070042c48013600790780302d144003074048005c43c80d1180120842c1d100d241c8400380c00395103d17600c500e4100e00b000c0e00603000300d000104151842242d504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 716704262 1250 716703012 716703019
    0xc01093804080d18090203091b0307271d071406090901060309060c021b01120b0316060201141014030a02060f0c010f0908070f14070312020606030c03100b 68
    0xc001182c04041103060035104240d6543d54041d106604290400725403680000c0e40da0380148144440c00c280840d24141e98035400e00e00188240c00140841c0c288202903100c0310340025070000b410004035610310410844100350804020300440100c4925003441c0500d00387c0c0140e80700c0141480740030007508442031074040090015003170202c07450024003852800d030401c01c0000d40321810365040184d1401100120711050020344511051240c2212040c0000041181004282c2c03581000041d101d40c06500300c04c038040c0940d80c0740c000500341c0000010092003490010340c44c049500d00204440908940a01800100c0c800060b00d404940e210311400100302d20b034540603c0002c2401640c9440c0281008a41102c5460311001182007050071a03040c000d002039a00c0c00e001030440001d0355001101d50803648414022050040750500f400c2520726200c00640c940b24109000c014080040758050500d00d0903403c0314440da03541c40c141501c80114180781070705944000101000e40780250000c1c0c01d00c440c042c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 716705512 1250 716704262 716704267
    0xe060a050721020d02060601050904152103080a0603051507020102121f0501020105040804030f030c0803270c0d03210213050a060c050d050d14090c010938 68
    0x281c452052450201107206001401d110b00c2609003030f0103200115010700140042c041ca4600800080d029101c0c25130b080c0e2156651b6402d2021400c0601c0c00c0101810410082c1000704002d111500d01540440c8002c0d0085080c48000409018403806040d0540741c2c004040e10072003140c0d2204c10710340e0801605400640d5000d105549084003203444544c890145032052040b40800360642c00140070841e00914116410402003102080c0d500c001c84041302d50040c42c8035009000d505084030321440102e002400810004180144034062780c3c61507031031569000c0725124120300303402e03071707603915840306690b1070b00030780c03054035403c0820f0042c0c03c0d074507010141185400d43c13002101e1582040ba4483d407503129402c0c4c03600d2024407060401c0c00d8074078060441c030f0910b58034065464403071540e5499040c80c24400c03c100050280d2030b40d0708541142030111140c507415112414480a540d4441e07a41401c16800034412480011394034641c0a100e003261001d101000c00411140025840403a0000241d49204c0004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 716706762 1250 716705512 716705527
    0x803070504150e011e02060c13030b0f0a060b0c100e07080f0102070b06010c0c0902030c13030f0510020f07030c02180c0d05070903021e040608060903070b160e060a05 73
    0x2c1e02060b5861081d01e41d03454044600082c005417440703480f0060100c24207036050a05800070b400280c2c040d0040ca0030001a40c603450a10001d524076045900001c124410000521074200f502190740c5004070645081480b41d00d45844030130500c0d0181d14103242907544031400d20700c0503801d2035000600500c0341005455036a519164441d1521541c00c1004011380c0d4002141c04c03c2c01210361541d500040246040491201d041c0c80711800308007176000f0007005660000104401192540884401c10710110b2541d541c4e50307490500c605c5807040c807001661140551002c12440401a108441403000721249507424061070b9107048500b05100750089801a1102058138807545444115920910b0703603014442ea61040f480501050f114003400791b40030700800030030070300042c2c4c0c841041c0e000d60a200801200c0c1007000b54000340142c0304691001e0414000c05003480b000034404030007091608e00501d0704084640300d90b0383c14503a11400e841c000c40080c0519107050031034030b8018000c02d11502c0c0c2d450068200800f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 716708012 1250 716706762 716706779
    0x60609020f0f0d0e030a0e010e0f0901031205090307062d09090209060706020f0a020715200c1806010e0a030b15060f040e06010e040c080109020c010204120b07030b1c0803070504 78
    0x42c606c01c40209080c07007400142c1d50303400404035040c61002e072208501100b0100101d51a44410302000700500c010035900c1d0400d91089060319683c40e8005d0440c1c2d082e0799030700400781c810b402c02108200c0c021155114580d24101c01400716881d0a8141c0c1c41e00391007880d2148a1009400101009034490b00400c035a0b00815043d00203000c008074612078441c2e80312104a000f902d42802c6511007907d92215101000b5000d170400d01041e032889105861050403240b0b880c83c03c0c1018558060b0990104040444c0c0d03200c1d84a409032a442031000381c0359002d46c0c0840310200305100c4140d00c402422a090240007d0402e03148880030720350b02c94041d007018242000d00c40ca00740c10350415007110b00004990700c10490700390707844200a40048010349d0104607215104900803d0800c8c140261071025070005400381c0300160940c102c0d001000c84510100083d4002c0c44c1c2a098088180c8981002a08010001c4200d190a010106035600c6500c0600508810380e030714881182c00061480051020520000481c40c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 716709262 1250 716708012 716708017
    0x130603061d0c030f10050a0e0f06070e0f0307120305070209161403040206030f190f060f060e030d0c020f040501090c110f071202060d020f0304060609020f0f0d0e03 72
    0xc4019001c6815080c20000c0e10b40b036500903281e407095020480c282c1a100b404103008418110484000c50180e445081840144c50091210840e07071065042d46d2124032004a54075008980543e41d0520414105040244401c070b030440d00d580c160059203040010040c01005041010b2090030018200111500000d82d080b80464161030b4004107507c0055540e94401e82c00c80c40e240422101720704505058020441c0ea0200518440c90b20b10407801080468034442400401e441c440d0307400b800010f000381e86480141c11940718048484400703c5020907003e02901c0402d512090140c01030446032003404013100c880c0810b00060b40c02948104400c401c6440710f0181a0280a0300c11340400c801c00f40c00d000802c000041c1d0190401038000e0001c10b0032030ba10200b5158103e8004481940c0380c003805e40005080ca100e2040088802440000e10044c02c8072000043e5104078002c5004011003982c8010740d205900c2412a80701000d0300820020007080c0d064409051500901c2e140051100515000c00e0301e5a0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 716710512 1250 716709262 716709281
    0x1b030a02030a03050105060f04261b030606030307050607120b060f04030201180302090c09040e0106031a09010903021905030904061e140a050411190504260c13060306 73
    0x181c10014410103019018040c0b40e00502042d54402d20b018801901000a401a80201024031a85144012508203001c40c94503001c40c6d00000d451542503c80042e0b4800c18010809074024015000000ea89240200548178025004006840c4a90f0344040c201c903030015507007034150120398403106c58205480e560702038a54035241c119410b41d1203040d800003401301058900820840345181005100586982c0b050680000710f5404460711615103100040250120b011542c0c050b602e03069000007404006039480070480c43c00f01c1441501e840380030f0345900340d034050140a005644070b00071990344595122030103072410740140256428034201a001405541d0760b035000642402041d250a110f4141001c03401005150400e252100ca00800780131404000f201c0c41442d204941d5001d10301981c0841c0d604945604803040e042030b1316403600d090060019001130103110078503180c42c1c0d0300880c03113090448181d90040700314004000c180d07501d0042003107520520703c3c1b4105031354403100004001000c40c003440311075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 716711762 1250 716710512 716710517
    0x15030b0903030106031a030d080709030b0a0f0e0f061f0b0307090501091401020a02040504030512010f0801050c031e0402061b031905130603020c010b060403060906240b1b030a 77
    0x1207500d05000142918070060881d0081903110750015141d540014092216239400d04104103295190541500d00c00380c1580302510b9207a900c0f00f0040045819402404103081040c0b00700080624540d9490355880d000b1914130701c59000402041d940710f410035a030800100c80c02d403807021a50704d07440c40c10465001130b50070740e001c16a9088180704ea5a00540e010000d8294100414240c98038080000d503126070307007100030b40140d0b90342002c9024540f0400481e0204040e0380e01035462035a40710103121031504581b041159035403038034011688950352001200c3c0101880b000420104c02c600d4890082604040d2089900050420204055413202002e00c0c80c2c510b035100156444882403140408500c08603040034003003180810207400009000c41c01c00b010350b4468900141c03600700821801780106810642913900c8080801d00004000c1e0580109428510603d0203108400a0104208903900a502622a40e00c3c041c1801d0003176501d004054001248500b001c0c114502140080d14295440721059100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 716713012 1250 716711762 716711767
    0x915250203240a11130b0d0b10080f060904020d061a1c110a080d050f2203061d06070507030c0219030b01080606060a05090102030c100617010b1315030b0903 69
    0x9210f2a4842c030a0020200701c802460444840c00084004040c0c2c001c6501c29080401e1814100040d42d2150030103e00141c05022400b071600d0020345208400ca0f50025805060b00c002211401d0024100c1c1c0120790244c000d200400c074aa540c800a060b42c09111500c00c8400c40007100309660381c0c41018000720102c0e915030000540d84c1017004c820b010702240c0502440c0c4d000c03000c0108404c00214441e4074005458900c1e00c881d09005030500501c01c41412540c3c505850445e11b640061a01c0e102040324840c940c100701070704040d5502400c05015841c11800c507084980020100f44c00f600c0100240d034444c0c40d0001c5402e1250740091010010743c0c24654600460480500401030380100c181c0c05401d42c80001d01d05840c00100189480c441e003060142080f0010826060590081043c1e40c003003462041519100820710002400601c021311400c1500c00e030b04110008551f1040c85100b8200402500d03010400207180c034440d01800c0e04c928645000d154180c0c5c00404200c42c01a00340c0908003040c00707180d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 716714262 1250 716713012 716713021
    0xa030b09042612061908070902090112091203020a09050d0501020702040b0d050d12060e070e0f04020f03180a21080a050910090618030302091525020324 67
    0x3201008000c0707401140b60304000c8151180040c2128541c85841213805683c0302a8031040042031480e40d9104015500c0b41041c0866480090303000347c01140403e0781d40c0c840f02251051444240d800014000c5c00201c4928804942c0034401c0e00100503064035401d10078500342d03403140400c1d1059904401a20141d502007005411407400c0d0103551307001182180c0000c545003644e242c0c0d9464240c4140510103001440c1021810700f46540c010a004204000203c0c3c402d14005a000d4444e1443d0043d15100b141c10b02a44a560f00e402e10a540b0f42c5014420300c542146d5480380d40000c4500100042c240e00d1041c07125420006d8036000450b49034001d082403142c40c003400001d026000950191025040314103003000c10894070400105017080032500302002c541c070255400c12600810300d58000749001d0001440840c103068040e001405800402c2c0d403485030490414945100c0340c040e204043c01d05840600440c96800d50490b00c8004040c001410789441040d0350120081c0c070342c08101032100c00c01e03100c030420 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 716715512 1250 716714262 716714303
    0xf07030e060906042408060907030b010e10030e0c060f0a050904020408010213030303051b0d0902010c140705030f0c030616020721110307031e0c0b030108070f0f1a0a030b0904 77
    0x440717024145041c010400d042000c00940c10000080590041513907c201d03640c09a0301c51726440d802c210b405042d00c0501c0303158240c01000b50440028020301c40c41000c190761400d0820b10100c5100c1c1ca00746000c00e0030805000802c94450f403141c5101d56005400344004910100288018841c80703603006903401e589469440c0c083c0a80d0b4001744960030311a2080d01d00200402d50074101d58105014020001d1014410f03c01620782c2030310800d000e8005d18024032300100191001403803500781d030022001c6a8603c15400f0b02c0320f07501e1240c1d145e5180c043e00b18031b02184d440074040c0c1503103060002a00503508010380f608803400f01f00c1c2100ca007042d1220011040503052201f0f4031480c2c00002c000390060071070f00303007540c452182c004501c2900340041a0310103000350a0001e8107200314054032a46000958950b96030000f5592a4411b00a14a0f985000b01c40002c0c3c00005407218012506140c8000e102003518210700c404940140703090000f4141c888042c22250b81c0e400309018802c0388610307503214007540300b032449 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 716716762 1250 716715512 716715569
    0x50d0516140307240309081e0c0f01230403140a0e1815090a0e0f01020d0e0d170711030c3910091a030103060b060f07030e06090604 58
    0x341c0039450103138035000602180c4c0c42d81910a0165802c000ca044000ca2409220511441152030034115400e800c09080c00d41200080c2201f0001b01c08407080080c120342010b088a10b0300c0410600d003510150940d600604901090b64024081e040040041031085448191544500d00002c000703400d003045007155141440f5061800081d1117108016444c04400c609038154007008100e2182c1d0040000582d0400c4541020050041500554442595468a45010307401c50315001046a0510548080002000400c906084460f9071240b510b4145082680d40d2040060f04041c1006054203400c421040d0800040203050b00c2c81000b000540d00040d91142014003e251410f6070f121074856a40820205043c503260908013121158100254030000759888660342d440394079401c0c4921720440d1081c545001840c12030f0b001c3d1106100150084040143c0f0317101e0384e03841064250b03060280e140440d1084046812001c0054200d504d040c0b842e0000408030f8109074000300320307003040007910708103005600070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 716718012 1250 716716762 716716769
    0x3c06011d010608131b0b0d05011a1813062c0709091e060303051801090b0703030b1519021923010f05040804170d09050d0516140307 58
    0x1444002941040401403907468040d01448484038241100b00600030071055403024105c815070541a0280d50f5020390784190441e19500404600e030400000d600d00700404400ba002d592000c0c03103460710781d140408400b908455407002d0b411120b50381045400148e68855140a000c0325900c581c4a08441e0210780c0d0640306001c6c68442800c0f00d0014130510f00d821441240c15660314031740105e0300f03072090443c81242d5400500059011070406800100780740d0041c0040c01140300c0e40300c0011003004100019280543d4034400c540400340100007110220b8401d81c000c41800e18001c003070030720302e910001c1e45400b25089859403410410703055040075071050f0108a8004000101620000820300c0c03a11a441c0b5203200c2d291907200d041c0038101a29614000390712a040a60160340c04206506090401d14426000b82c001c00030145074107403080c0c18840001405000398001c0d40d40740044241030009208043ca0314031821540b03845140d820130300c15800e075518940070348100c4c0102030301c0c0740307600041614010740ba60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 716719262 1250 716718012 716718059
    0x308070818040606020c060d020d02040f150302180411071a2d010b0318100605040b040b0d08090315041101080105060c030315011b0b04060c0e033c0601 67
    0x40040113015004500c920300028101e0f1401e07100e0344014851406480f41c0e0f03900100329880000e02040003401480104161f840003030b080c100280c50b10b1015401ca10030080c0c0c16084842000c41c0071542c0c0b4090700803074031004030b00c5100c506080b40d03a90b030303244180c80000800d218031034490300300711050004620243c071541e0100301103007403030391b00c3d01e02000c0b40d01c01800b44190ac0c0c0740c00400034181500c44081324000e010302404071043c0700d403080070100c000c008a00501e4840c50401c442c0c505149403901441a060300002c0940800221a030741c2c00c10a9441140219050701604600188218084c07541f41c0c0305138051515200f01000540006003030301d1058200030700c550310601101c140800c0c0001583c2e80b00e070b24004604105032213040103030382c80000103456108220100103140108402d0210302d50080e48114814400886000c1302030b994082c41c11841501544070303000816030741034040c503005200149484064449603001c078600c0900700002c0040a400e41c40000108440b800100c400c00c00b40c071160 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 716720512 1250 716719262 716719271
    0xa090b130b040b07090509013b06101202070804050a09020f0711010c08030108011d030901050d110f04081c08100909050c0618130e061609030807081804 67
    0x340d6401c80a11400341c005400c6000000000711103500038034800016101c001d01030182ca41e03480240c800561011109884100860381c2c0c890b41a040d000d9545d410070803000c248404564034142800700c0308002c407180104004440408051000c0588000c0c060180103040c4d00f59958200703000d00c060300d01594801d0b42818410072024807883d683d030007900d0829602c85100d0323011039512070041720501c03400310000d040c07a0000000084c0340081580000204803c1c04404c40c0360f43c4038100c051ba200e00840041c0d80c0413030804c1200851400b170541c00031500300380d0921b000c0c0c1000052040c4008a8205800c1070016038031166141d070601444141442e0704454a1600110034908640c940b4004420351150300202074a440c28035040040038080150749010150074980c40700c00190034038038a004110300c458016010070880481458072400f441c02044192401041c00d512010b044050245c812948801000000d0300702200159141c3c004141142c0200400c94440c00c0300501000d11244084100388282e150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 716721762 1250 716720512 716720551
    0x110702030c060d1407050901030b0306040b0a1e06090204052803020d1e08090f0d1a06011809140a050402031e2d0f03040e0c13030501050a090b 63
    0x1070401c030140c5003610b1058407699121005800b8210000c26088000122000c000c0b0855000300038144010090341c041c0201852081459101c4100742c0e4041d111360040000952102e0090708144581481800fa048040300080c201c0d1040720019004815800d0b0002020402441c16142900244101d03034256281400d1044107182040340a20000340180441001da5062054600c01c0c05a040c0703164462072044090740c82c4c5030a00b90b0000d40e04600c500b402301c0e4203080500700321100300b814981c0300030350201015000c0785194101d100101018100303d40189454240265000310710024080c1100100b40c0c00092002d801d08000001d00b00f0380020301d04820080540e400007200311a40417589d48803011481400c400074203050101c0070303002104801c0544034039039040b03000d5150b80120840080c2c5035050410f411542d02ca1040307102d490f141020460102e4105000c082c01407454008010134102110782d20780e542825100d044a02d020340c2a03407021030500f800640481c0503400100580d062192506 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 716723012 1250 716721762 716721769
    0x705040605071106040305010911040e0f250b04172b0e01020304051804020a080a05060103420501150c03080408043b04030927020301090f110702 64
    0x101c0c1000f40850a40300070a00f040e441e44000c4802454115000340005006414141000ca00190450b40990b20740b5a0400540740c0c0400c2c8070100b034441c52701404090111005000f00d480c440030003429400780d040000101240728100910060401001555440074920782050605104003c2c4039083d04c2554280120b00c51f11214803480f0304003500307242c0c181c4000000100e00d180985e421268000d000c1620400c00ea602d0368001c0c1e4404e9108585403480346451b01007440d00c5920100c2d0041c51540240014800500502d0007a4028420b001d481c40300c00a81450580b0241d000c0c1216001c036100c2100c070401d140380c140c003c03a03001d0b0021464103960b00000a030020004c00e410710000d010083d101d0040b80070842030800b00d90051814003032904030042c8003507c00840203400320285040075106071002c400c00ca10081400e102d141c054803095185482d00540e411459a4014140e40b06090104046401d40f6035101a50103000781d102c0000380c8250030181c200440c2c20f00d96400a071140b00388640c3d801a41d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 716724262 1250 716723012 716723017
    0x14040b0a2007030f111902030c040b0f10030e0a14010c0903050607050a020304030206040b04150e0603150f120105070e030f030f071403160309140a0915120b0f0705040605 75
    0x81d0b142c980218102640101181d500009111701e070070301c0c026010102404c80d40c22141d0225540214199007020b005c52080100b10f500210240e81c000c100003400e840c261509000380c2540c02642d00b40498811b41c2c48504504000307503010120b41c0c140b06006500f0400a0034030411a0701c001d2414084001400d544541d5a503100003402c4200300070300081c6844645100f401034a0085601909054a843d21440c1c500c0303407030b005400741d0070418400e450700d0181319100341d0174950a2803018110b43e01e03540312904112340e00c0014074240307600020340c0c409001981c0c550040005140c440d2000004803820140402460151a074044612950102008086540000c0200e5980240e40a00b10756a030b890f80c07600c492102ea031f80040c49040e010100d9130310220380c001144031508910aa07103440c2c03816103440080305108400485103070001c4050324184110b900c0c661141c805d0039800d1006514040e510401d0030140c00e4180011503014020201344401d9000e12080c43c0c2d0008058100642030500b0010024400d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 716725512 1250 716724262 716724277
    0x3150f0406180f060b0d08030a09050c090c0414060f16050c01050703021020030c0d05011203080f04030504080d0201020702090601020703050d210f0e160b090105070614040b0a20 78
    0x1c43da10005d10f000c1d0766444840d221141e07884400d96441e444c202c4c02030401000110f00270780f400d00407450401c80d6450540c9540f8450285141c281d410319040c04501e22500300c1c281960380d00401d0400c600340340e413200740000d803180329800c400700d10003480285442810841c00060311030510000388880c0c0300080d00072031034504c0320040c4080010700501102c0b00b01400340c0a00200000c45c0300010a0140c000300204c000c0c1a00c214600051000c0c0c3d0f0327a0407070030405007242c990260000c0c40140208030701805440f25541c00a0207458458145500c0da600a8204003010662101507075002500804608000c02c100e41d05c90800d00151012501d1030312120f8940742007040c1501000100c2c02614102e081103da69101e003244035004106905103800d1880003031084020340340c0c4900c50409220300c408e220720004000d80e8841d03401c26041c200d82c040113443c2c039003012404503449510b4003008000d0301c4c1d02d031042902c02e60145020303043d030341001d641d0030048860705010b4005d01c140d10025021103000160031113907003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 716726618 1106 716725512 716725523
    0x26090a061e150e0403081f140405060a0503030a050f0d0c08011809030210090606050d030201090209090312160c050609160605040f0605070203150f0406180f 69
    0x2281c50900c501007080e41100c0c00500080d1152103010b400250f24040c1f500080300c0c85841c1c2d01004210b4218107410290b00b05245107605d0b081c0115a04030380180d07200d501140c00c050100c0e403a4031840705100c05015000810418144440c401c4840f04488030308100014000d0078401480c0000a10400700004111740300b0040340065441410001c642c1030300201880c2c07a0540382500a81000c010640c0e00c10b42d40d407400145c2e900c81040e505000b501c81d500006400c0d16920401c4014480030308078000c00c0d4401c0c02058200000d502e4010f8000840103000410641243d00840d4074440324a8028458010345041c800b00040015448003041084400b1000e46074603250f0480b420b01491103821100c0c442803000304002800b4500404000740058180c48207180300c0500114100c0041d00c40044a0030303007508000900169216001000ea91041c031034900c04032903245e45840c050061400f07003a = true := by decide +kernel

theorem cover : BRFrame.Cov 716546762 716726618 := by
  have h0 := BRFrame.cov_init 716546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 716546762 ≤ n) (h2 : n < 716726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
