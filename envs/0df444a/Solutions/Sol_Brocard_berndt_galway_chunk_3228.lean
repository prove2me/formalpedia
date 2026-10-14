-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3228
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:02:48.972405+00:00
-- url     : https://prove2.me/submissions/19eb501b-13da-4d4f-bb78-f7f41cae95eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 580395683 ≤ n < 580575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 580396933 1250 580395683 580395689
    0x1a0112090201050405060d200c190b0610030e0d0e01021e070308070c030c060e09250f0905040e03040501091d0118061508090601050d0b0114040204050604031b 70
    0x40144588809500083c100d48510f01455005642c0010031900407403c035000514811a0003002968000c1d910106031182d421000e4400741500502290081804912040d42145070704400384600710303117460003000303038200d0f03210445810f241e01c807141f0410503001440301c100000303c161102c640e4098017500080c10914031311085016000540c002585a0200203030340390503a948880000c0c1d070b5111505001c00c18500c0c1d0352008001000000001c10b66682c005c3c000304804000fa28100c15549600100361304010340b12000d011403011844e0248811403046030400154145801c07c600318a80b40e4001c1025120001449206648006410400c03035902c03031400700040513424080e0300b40c002e078100307042e0b29180180b180e1450410311403078003003528200c0d610810007002035200c1c0040e2845068400f0b401200100c07071485240c0595000001d10741000c0a1005c42c8641c00185003456a003444204410201c00d0400383d40c00941c01c1c800031840307445903001040614042c031140306048a10006280c4c107502190 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 580398183 1250 580396933 580396967
    0x20f0603150a0623070219090903090b0a210b040c0809060f01180e0c0d0f0b0708060102151e0f1015090504021e0d0902181312020a05011a01 62
    0x310b00a02c000c11140c02044940401e800680c5d902c120350700000344038103031400b110060404404000941002164450f07290b5030f110343c4404494035900c4110908a0088500d8600440d403242040d50b24140c424180302d80b241c001c1c100c0020005030510200b0202d038074140750721000c01c0f030304424001005402c001190380102ea030a525141507040682c204500c0181c00020a0025120002d81d500e0741c20520601a06843c080c00e452861002d6080c10710351410b1514058401c440081c0205a01520a2989503c41d01e410b800501040040c0351905a12600040c0307024403000001100e20410703a00c10f04080e00401c00c1d400303140d4150411080010608145a00c6a5801401282c407490746940081e2240304030749003114010713100c400d06072002e2103410700c107090f1800f05030001400d06000641a40244001d0b0b000b50f82c240c0c03404600a150104480781594851145140781400c00d00150326852006014141441600d2070a4455517a050079121280440650102418850091942c7c0b000341c0d840c03840a50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 580399433 1250 580398183 580398197
    0x4080f0105060402250303020d1107150911190e130b0108060601080708180a060204062a120212160b0606074403330904020f0603150a06 60
    0x14030007103403082c5d1083c94050b4aa80c040c0d8040c02854000e90541e02e460012034014044015160307d54165603000040489081c890035040782007814461040c240d0050b4020107904060402e0700820503007035110003100034241994200400d036160f0040c4580d02591006040c04000c0c1c07402d00d030004a05c0b40580012007107510001c01c1107503aa0b48500d0f43c0e81c00c41c0032070078a1442034441c2c00c1212200359a00001f507071644102e000d408100703c0e81e50300810841d000c0f541d5581000d010760550400b0720038003030202da00030000c1e50400c102040b0b03030000807044604540100c03080f08080a130800700c1345d0429419142d01c1d5844103000710602607013405083d80480102c5440d4074042c1142d64020031070b1003080310f40a42c0000c0c080310044403800b10b61b46012004124000a01080002d616560941d004407040b0521141c44510307803011804007960210856400c0001c500710b04000014041c8442d00284142c0c3d00050455500110747c840f0f400641c002c3c9186c100d48004404c00c0300911580380b1256110004000c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 580400683 1250 580399433 580399447
    0x806060c0c0f0622080105091902041104031506081006030b040615080a05031308010504120c06110304060209040c05030702030901080408040504050f1605180d1704080f0105060402 79
    0x1001c5089506450116012480380c11114041a41402010100c44130305a50210310b43c071562207410f039402200c42c0000240000c3d61030702041603c400e08950254070000d40e034102d000043c80c05412131a00300694000740f50409503a5221a40c0800c6071054884080d9034484042c000200c062140680d00d400c2c4440030700c403080c5550f0301c0d51240300d4001c0019140681d59800554610f150340e0300e007070042079030030216140304090381401da41b2030b80f00080103409401600c00018040c2ea040c081c4038400d540000305e000c860081107000740c48883e04110b0890700305a03241044040ca686d110091800f90380500c0c001070312104941c0c2400b04a8521581003c244070b0b0a104015007680e001044a44101080ca0411200d484626021207240659000146e105040500700300900452000b6240305005d0303484030118040700142e041c1c1d0107105d06043d09a00e165482e16a04050a04440d0400c50b94070410110014507407103551401680c000d40c000100d2904040468000c46d4800d000d0749da0003001c01c8404502d082c04c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 580401933 1250 580400683 580400707
    0x5090103080f030603340e010506040308030703020c070f0810140112020607020306040b070801151d031608010501090b0a080705010f1119020109091a040506040e011b080606 76
    0x60742c1c0700341c5040400000014081d45051000c001d1910064604650141c141da43c22124002d06003007a1280c2c4800d9240054070883c416003150488a000d45058589811615007003482d9000600e000240740d000c000b1034a8080d020890940102602c40300c0d135190310f00340880f1500304000044007038002e5007003110741610400c0b441c0c1c0c100c1c1183d050303d5400740a06410301c0401ca65005411003c4d40c54000c1c0703010403090104401e1410300c1440d5913541c280190303032107882045001c43c844c02e20b000003488406200c201d0144880c00d02040c3ca030003c044845082e4121004c80680c0c0b819001618540d440b5401000010300c90f000d00e01071000203c1d50170449604081c0d0b5582d990043c1e224040c104580c0b002e068003024040c11081e2a10302115050315945020b02c500c4005941151004074005030b80e03d4400201d0210910038690840841c0415032080b0401004000c0a0301c00034102e668026642e80c60208801024442d8400404d40c054800b0102c0e004e1a001030070f8007074001e01c10b50003400100310450b0141 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 580403183 1250 580401933 580401937
    0x611030720090f16260c0909070207030f060902040e060a091103010606020c0405040f020603090a0209011202060d0e0c0607150c0306080a0303020f09150304110a060f11100507180509010308 83
    0xc3c1c0b80c41d14009803203428250005c100ca10580c203044d04151081400140c1e40e0a1000b0b20105005480c0322065031212001280e540c0840d12020300701d00070280d035030400251950800c1c14107500003840454801444400e4908141042d60300140c401d0b0b4030701c2000c04000c806280908001c00840082107800d2503e00c0c0a03403161b00200c2410320503595800010100285940c2c611031003600508081c0d10303840c00c40c02440c0e4031080d009040e84a102440300014a102d0080700302d0b9502c66020b801c0f64102000300503294003034524142100c20300e005041c0311400984400c00501300c038901503030340601107092007407150701100d81c005451401c060a22a0070710000d000010a400c804d50b01d03180050345c0c0c00c07074043c01004034007d001c020359110b189281d80c0301d00c05204102a40c003550042010460214500d010030025240c54400d0324042224192a95103040c050070201c0c69920407a0140c0b80031106510300c0c0400c5800441c1c484e400b040042c45c51480c01510a003c90b0064082034812103001d50560f1034211f030724 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 580404433 1250 580403183 580403221
    0xb0a0501050d0e030f1b0604030c08180907033303140712060623031209210105040317010303051602030109060f1a0612010611030720090f 61
    0x10210028410b200711805030320000420559070207990f180d011032480849aa880285280ba000460381900314901801082c142d00840c3d060b1140c0b80a05801d41c0c0b41c04103501300003161006c00c1c864804214854440020705842034200356000149000044182010314060b003c19402c10440104000d1a80b040810013200341ca420040d2820071040c0210200e00d80229604600120207081d81000200b1111303402c402d080e6a0b0564900390042ea0904000550440c03c40030350358940d10440c88041d50003443c80c02030401200c003a0440c56802040085001d040700301c00100300c0c0d40da5562081000741a40909004011115480c80752450351440e1401402402030804100e030f840b61107142c010441d94258058150117034480014040c20300581c141500900d08149040034100365468401d00628009085800310071300c00c2d98250582e400d152040312910300080914065101c100105004950b04050505052b124018501c254034800d009100700100040c01c3c5110300c0e04517a040c048850801607010f808 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 580405683 1250 580404433 580404437
    0x121115240a0819060c02010e0a15021e04030c0e10060e0117090609010e0313031511030c07020f04050403300c020319052a10021b07090b0a0501 63
    0x1000c5203400181c4040351580104040d1154008a015038a10640050300d0580180d50400c0000c00b010810b0342a034000202200e8650004028080000c0340046442c95102c8000801410422031200601c518929424040a1800d0101c2c00300304104009061001800200d841c1200500780585650000700040c00b990301444800ca64446c101d03445001c0321041071070007461200042c181060b415440341410360341d6108650030440108081100001150210324000b0140781d01e0390301d96110b2501341440011407900c0c0a49440c00100040c01c0a0061030080c0c0d03080f42102d5540c00d0f07510400c0114005600c405000307508100811000c00d4001002010030000a207010418000602081400d0141c00c2c50115101c1d00c0e1074248901250b00002500a401405040d82044101004103942c0c0e0702640b4082d4041d0042d014000602c1c1040c8400340f014031000030100c81d02541c00070207010903600850810484645240050780650508221500c01042400030400c400c0900b6030209030618124010310341 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 580406933 1250 580405683 580405741
    0x120c0a0815180411031b061c0b060408100b010e1518100e0112050126030c0d0507060513110d08070605010b041a0c0705100c121115 58
    0x807a4a80010307806a0501c4041800090710b002c0c030349104042201c09100d0700910805400051088810055506111004201c1401d00109843c14914080c080c1d00e02058980c4580070100a074840d0303006070000d800700e14050424640040403401c21201c0c00c21070a41003006182a0f1041038603424106280031100c1d040150b50f840d5254000e1300c085455000c101d4000115500048150358400ca1070301072aa000d076940c1c03481c07614950b11f510580f1020301840d03509145440145c0c81d501e24420103a090f50800509417030924110701582c50404c58030384540400715000090000c20098148199640800c800c00402c0703081e400750b180c6050700300c80389140601072030104520f042403208072029240001d0713006000b0b00503581c550300034034250740152090301105980d00d400130031008010701c19140d500089038000c1040500e4481000040068500f10105000c6400b030400007080803045581c1241e840358458140c50341181145c249041201c10310f000d1031303c1840b014070040c503004040f914000000440c80314 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 580408183 1250 580406933 580406971
    0x103c050601022406031504080315030715090f0b070b010911040f03060e061e06090c040e1302120c0117090f100b0a0609050f040509030405060d02120c0a08 68
    0x20f450500b01c0320320f501820039051402c0f50083c10302d1084a2150100b6010794107500349030701c00c01525200070340f402031070500c003803000410200d40b414125060610050444001640c1c480d2050700e996030240402c00000c10000b014040b00444010800003001c0a0b403100d4540b01c450748541c12181410f0003034604180c0c4442070000c05e40107079003d460181c4000305089070072a64034941170008001d9900040d5441c001c00000803c180c00c00048d4010040b1981284126a03842404015541c000100400c5d82d000d802c2c400425103503001c0c40003511a100030610706211a1040c010002c00f0f103104404280c5560201e1509460369a01818152200440703c08050b20f94594010700c0d0f08001c5000300d40c0d041032003071203003d4404c0c01c01504940001d403c191840ea075107503220305c0c0448058096019598205001c0d808200c07080c01c05500c150b1f8444403007401d4904081d11840040d18941c45081c1d440c3c40a50003042a41c940e0303e03060415504400c194244501d400c603000301c05407078400001e111036050324081c0342c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 580409433 1250 580408183 580408187
    0x20a1202010b040e01020d06141e01020a140c01020f030f16050109060e0a0309140604030f5a0807080405041e050601031e0207060b03103c050601 64
    0x100ba50040050084c00b9154034411024000e400101035001d005040003030004e100821100c1d4500c1000024050312040300000f000c1c5007a038408800c5c864110f104007442a40401c0071000c01da284070381000082c2010804030750009103040360380c80765400503810400051650300072000441d070015602e01241c176040201414030700d00505413070101030321850400d8203803580b001020591503211440b90b101c0c270f10541d45500c1079804001c80d03046c105800020801040c80403035041d080540d0b0780c0e032040b60090321500714220099400c80e4000042366803a0000c501c61241104108138203c030707049901d0540b001400034181060085458528007030070201c000501c80003800f58000840d00601000b500c24050010300f039401c400068128068841c00350314045c045420356100b4003824031102080124a0140c4c82030074803503002540140821a5480d6503084500780d5500d040c424230a61407102ea8001801600340c161040300300700030301e80254440000d05152204d4224901e4081105084000c001505036528001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 580410683 1250 580409433 580409441
    0x609060209120d1b05030f07060b130605010c2a030b0105010f0206060f0d0215040b0316020a03120522120905010807050f070311010504050f0705010905061e0f030a0501030b06010c03020a120201 85
    0x607c211910014114050110b580c00c103511410301510b013844118900a008030403103c803070090600241101030002c0120320900281ca03254640140f85804080c1c854800d0443c200c80f550084546c2a006001007000e076070081800310741c0703402f5070020f09542c2c50040d000900714100354520501c901c21100c8c442081d91a9210030424114101c0002030f665900e49401d10f149400440c3d8482ca2044000002ca500c2840450303010f155590540301d090f408042c2032403e0b809400b0042100e01540700e202c0401000745050100c0c4654103002d05054505d4003841d00005050308003640046040c055044103020625134014110f03102e05a1024482da107078407103480e044032486a2003541d50b11310f41c2001c0c10300c03007032000120b94150000920f4084900303d658070401565907007902e02c182a4070000c1070000c0b103e489002100e4990190184850601d00215000044c200380c1013545c910014a5640005100300103500c800382d03401c02c1c4c0c2400c029000365142e0f58001d580d02d005905c02028200c0b2080d9440000b030007500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 580411933 1250 580410683 580410697
    0xc10030b06030108060603061305100b01210501170705010f080c0d09081c0c0e0d050319120c0207050f060c0a080a0201021309060503030f13030609060209120d1b0503 73
    0x200d80e03d50390781c00d4403540c600003545c1d524420300400c00454200d411151243c90159405006080e6041d001001d000040251440c52414841c9640054401e500405074460050007941800101e55040015481c24cc2c041782c25400d03125070080b0401d11980e0b8200e282c26154100c1e919244d0400d80c0e0340b5800d00700318010454002c03c12814003072004100484c3d42e002e40302034900101c0320206915018044000d03295110a80d0000c030703d00000788615800c100200f11500d60156044078503009800f88203035015011140c2c600d0000d40100181c40d0300fa00369001c2e1070461207441c0b0081050301c1c1420006041c0300e00102000d48144000540c86511502c02c4c005981d6032a006100300c1e4880601d044064040c2d4080c8051210150300c0440110711800c8a1091005442000c3e00560500280d8191103c4035403108100680b50b104507000040000e00c5406124411445a034000d81c840c0742440c140708500d02215200700103a0002401103800c550b01c4100c0744d41074144c500e0000c1d10540c0b10f0030600c2c21407003098 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 580413183 1250 580411933 580411939
    0x904080a0c080f09041b14160b070513060504061b0620030a14010803040b03100b0c030913361a07080c0c0601330c0c0b0c0c10030b 58
    0x3c078503c000650356001034003110105440500ca142c1400c50344801c400750003213003500850100d44991016541480140c0803001000d0001c2117629004d84a401000c2800c03981d03080060000158501c004106480041c020256402c001d8186814540e0103410708071480c1e8540426848015500107000c16500695400d03100780580c205c98061a940b900606c0d80700322898003441c1c4c00c4c202c0ea031140300071203440c2074101c0300c00c070000e10b042600703041c503d091503400504420035041e01d00f9808101c084d0310030b00801d400740d4070301d0055690708604024051060f851840540000385031280b5140e01880c00d191840b202180312102250b0500c9030b020181204603000d03005850b06282c5c40b039180e080444074480900801d030315140c000040e0f5403801c00c50b000b813042c0200d049158200d60010407502c103001d0030010440c1d001c0400700218404880c1c510a41e9203511a001002400c4000040c0030300036030302c103200d010f04003044005150902c00c0800325620350401100e03901820801e0a8140d0f800d2080c1c2c00030b02c3c900002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 580414433 1250 580413183 580413187
    0x6011505071a040c08071a03090f06010f050901091b0c02010504090609022203050d0c06061505030a2f030a0207060924021306030510050a0602070e10050904080a0c08 73
    0x10030b0007408555012a0201c6400d45500d00208094800181d640211441010b22480d80080343d1081003c5400c050441312052240103902d29280005003d064080c00d403c505101c00185400c042020800c41a40301c602c105150140910781181d40d64426090030046e0f00340903000342101e100480700e44c0304682c03003482c1d0f1501d00b110111f2400740035001852400e0212108400b075000240b90002499060b100051490780000c603002ea241d4050a07600241c907004103c00107506a4451940014024065100c8000340b0000200714408a035840ed50040060251104040c0e0b42003101d100c0001031160714003d02d500000c00062400d0b4000e404403080c1c82da020605100c40461803408145003800741c8480024480300b00c404034114003851080c0c40b1283c0d100140100090301d0181c0c20f03001000054011044045880c1c0045026114038180c0c10040140e58003c1c0f020b40e01c4c0040c0600a040b020f0283c1203001c0340c0c3c180400656403010350684e001500207142c1c580d2042c030f844081e10008510720340140304081c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 580415683 1250 580414433 580414463
    0x1090905070e2805120f030f1b0708060720100b011d011b020d02031e120f0a031508010e031e0309070303030b0d0b0108210703020601150507 62
    0x110610b0030020040903a0b240d44400d03442c2d40030180049440f031000740c0b802500d10040140d450303c1c05d03d10000111040980c0c2c48045007524041c15640a00c544801104d8000740075040c040302640900e410f00d51440c040c00c01c10707081c025141c3d110180134116200b001848000403022141c5103203080b4a03034600a007190440c00c42e40e48024043c3c40d00000f41c1e40441c0a40305d880940700702401c510440058140c1d01d04181c6650840d000303805910483c802d82c1c1100303c48a4207c0141c5080003d82010b00b250016a500e10000d90310700ca260903d20102031180035420b01c4070648007828035050f12203031410b0f8100820f480c40034420344c000c2019154014290356090051841004101000074210003007001d0f20010500f0703442d050a0454132054a640445600518081001c43d20990280f1301900000385480103100ca6510f82c031030789540a0700700c41001e812481c030072400c400c0349040b039021500100c91142c2c00e02c5003541b4080d488502c1441038a010071044a1907080301403044003201c0505601400c80c1c4040c4034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 580416933 1250 580415683 580415687
    0x60806090a120f121e290d11040b01030902150a030c0302090d0308282702030a060506060f040803090a1e0b130b031603050601050a09030b060109090507 67
    0x203114030036649440040c2d518488180704903a1551400c035203072144504110035201003001001c4e400c3c08400d8112002c0c1d0481100c2c10320b8007521103140100d2010f59039500461000740001c40903031407114810292150a1000030744400070790750003103070100c500280a459010069004c0e1406040c001d40c00f02ca07400481e0300d010420030291070060500c1d98100b0074003405207000e07801c030310488032119844200a28001c3c00a40310790003080d4402400c102c1034094240005181c3c01000100c218880d034039440741d0034a0b041d010b1111400403400f5820980d540340c10b5460300429210360740200b0180c030a5440741c0c00905103807030780e01c00c8800c81e0300810702e1641d0392656074035260344036040340704541e20549034204001042040c050180740010b40704400407406500c0c004c034603074080d07000c2c2d205107036021000c2c0b80c00502c941202000d94440c0481c140400c0d400801c1c440018200c441c02000d00f03060000038002381d000507a1003020142030f82c0e40124035104c95181c2c030005aa240d040f65101002880c140360030803800075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 580418183 1250 580416933 580416943
    0x609060608150703060b030c21070c03121103041202010207201905030d20011a01020d0302040312050a030b040903110706020a080f090d0503070b07110c13020d06080609 74
    0x82c0d204904800380d190351078128243c4185108505d0000310038808140c6501504001b0000401040f25112401e852813542d003070b1540c822a800c8010841e50f0811800b4580c00030501c0f2154003002e4030401001d14000c175103010320301001d000948440c140007444118207000750b04803000507400ca9001032626405507010050340c0140e0700f001e4050300189001400c0016101407131000e4900040c0036050382650341c1412110580411021703e40d81c0310500c940c02d000c14007071040c1c0001220ba9181c901440c141200064904100810017200b01481080300b000440c1c0c0c0c00c910b08d080c0c4822031500341c1e82c40340400c070b0440c081c0040400140d84a440d004080040540000f1144000b8038603805a0300525950b0109070384848c034640020300307041300803c03054035080030300002442030303403c0100340c480b1700d91490701c0d40352071900906402c4603007500c90002e0003601504080d00769511480c1400415400e0401c00104c2d2648583e040542000c0d0b4010503010044012070b008803018005080440d050351402e400859920 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 580419433 1250 580418183 580418203
    0xb0304060c14120402130b0f01030b030724140414150d020d0c09060f17040f0b010b0405040b0d1a060f06160b090607020a03050c030715020d1109030a06090609060608 73
    0x10b501200105406e06406014111245000903c58000c4090174001075001d42012580d01c3c1e41400740400c081141c01d00740740c0096a201f410075035003055401d02040582000840303040e00e10100345c140300420000c5da10402c0e13401819411b44600090b8001403000d9040c5000e1002c000000c20f0001c41c1a01042c00d00741d008801605180c1e440540c050359820040c3c84a55000484a00060620b6282c008202504200c1504648902c2d102a21203005495010480707800380c0003205203502c0003404010b02d242500402e0483c000440320342d104442140d5a00d40d95100010390340b4201880d0b000020003a039a203562580d410840075141c00e544d925541030b281c0c0c00000030304040320103440c0040401c2260900140741031081c0e00f41d030010104844227450581d1643c00c00b01c01580c0038071003008188005515084100301c000248407000d0703156010b0030f0f0b0042c1900c008170f0504049450602000c50617650018070948060f0b0440c00001e050065405c0182c0030b0040b03906d014007070501b0100006060311001822100c6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 580420683 1250 580419433 580419439
    0x5150703090e0403051c200c1e0610050102061e07030605060d09020918060c16080a0815091909030e0d0506040209010e06030d032703050c12040b0304060c14120402 72
    0x12510303c900d5a000c550000502031030b07208407ea070b004032814501c0002e141e0001c0f03c0080312403441d800f01582282d40c00c00260800e80da0003000600c52591004002c1300060300b0709001a041c2d61a248521941030140700580080c03024000740450745150103035000802404003e0306841d520004901800040d000c0c5e0038040780100b05071400599180c1640707003042041e503200005081903403a814001d20080d08005540f8210101d45d011140000c0c8501f0020401480b564035600410b281410b03500c8100c00030001150f014009800412a0040d0078512400c1710204c02c40d0002141201410100c2d041610501c0c080c1c2c122a04100b044140000090500c0c4101d10840d08042941e80702c901540a280054800c07580661040d00c581d03c00038003a810400006011000c500002c08ad04032205a002c3d81640c07064001c60400140c090b11840c00b407021400e04991802c5192805281000c80e0241e840300810282001e82c6d91024110022310400c800200c0a52503c552034880300301c0102c07580300030001c1e90100c2c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 580421933 1250 580420683 580420717
    0xf061807020303070e0a03080f3a05061207091104080615190807090515030d030e120903060105060702031c0e01020706080906070c0204110708030f1005150703090e040305 75
    0x45d6524008610200780d903844800141011080a151400c50708500558012007012800c15402601c400003038002c051800d40e0220402034034801040c04551001d44828040c0d400c0101e108c807103401c0058a041210b042d00c0f000200d80e010010301180d00d01a940181d01103014520030720002641e00e041d030360b1003d40e0454116030900e40c03031521540141e00d188a120b045070030905040002804a61000b90b2003500498115600c0c0e003204002820306a040c507102c000f2a5541030f240807600020400001e902c1d00c2030030101c0ca080d030342d03600103640d5034030511401c0c1c82a4000248203045440a00803d1400c031046401c0c03403100c071400c0034068404e0511181050061007110000940c8a119041641c020061840544138a0720365810448808512140590f0440e4071010f440340c1c0542e198000f02017680c000c108803a106d042508042d030581002404415039000e48035000e006682e14590001350820407510032590755900c926003652203510f16800301d04854888000c00084c140c00070020490801d101c00303100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 580423183 1250 580421933 580421957
    0xd030309110105160605060103110403030f0f05090d06180803130314032418010b0d051008070e0a0e07030803061311091002010902040f06030203070f0305060f06180702030307 77
    0x45113401001c0c0c4190340c00f06985808808204a40e01c8a900500306140218403400700f543c040f000ca5001c0da00407400035800d0099188019489100d65200d140310703290240c0750814980006440002c120f1025025542e80d44200311480d02d144540c40700103030300a40711a1649420300e929510030030406d006801084e2031105480d00030044004591103110340301020307160881e00c64a40d18554003103924940c0c1160121501d405035049104107135000300400c2c2c4600da0349100c80002c0c0c4041d543c001c0d04103141d1412210080c4503c02c400b04030078040c1e5104003c0401d01d0303680d10340c2c540058505075442c801d1600800700b000c8240301d407a0f0021403003040d0958a400020501c0d011600841e0400c400c901d83c40340b824030010340c161174100da6405c030441c0b0034800442e134480395400040490328001b41e80711016641d41010421824140240320040c0361070a51440c4242c07079a111a40c0355480180302c0f10310b0000a0740010f017607585100404410380c030403203104040e038074060070041c0d940e0784150303504008603001203000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 580424433 1250 580423183 580423187
    0x303120c0306140f0a2c13020904060515041b11011e090816050c041407020a1203140c0712050c060a09020d050303070f091403030909041e0615060507021806030c0d0303091101 77
    0x11f41d5125501902d058411317680c50715010000c09001d010b04641140e210019030880c3d680d4002c003000c1807d450394801c40009030501c051701e61400b12041d41c0300c5904000010003040100b104064032804880700100e8281e1280c504040f19200d6041e0002401c03140c3d00318501402400074408210784801c0d42c1c104a0020079450800c10610f0460b02c140060b881980c1140024211080ca42c03030190003414040349a00c006c000c40d015400040b6030031101c0341400325131601480700c80b1162400c001d02c1d505140b85000c0656410035140c403002010040c2d4162111410b00c110344139900180c5120b6086000e50340c803820407400003050400c280b07a0500000d00300540c0400c4003905030300c80c0380619000a000703500e03140081c4140328030030a000388251440110403460701080502e40b001c60f031880d0701c1a0f41c0007070000e981802c1c441550f00550010320400509008010042e102d1050114030a40e001e00c24800759134460000138509081d002070039030410032000c5101c080540540007200340310720401c0c103800880310314001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 580425683 1250 580424433 580424461
    0x6080a05070c081b0f01180b0a0c2a02040903080f090d0512130c0b0703020d02060c0a05090f130204031a1608090a0b010303120c0306140f0a2c 63
    0x1c080c243e40c4040192036446022410080b903402c0400c015203290703103000d05a95084420340300f903605c69860400c055808000c61030200e03692100a0b04d90401440c190854010800e02c01d10f10b5a0340d4054180c1c9000943c02d80c60741002d1449a4010401d01c4003100c14907000749a0b03031041d50040c002400c542c0201f9001c13017012418029035070b60742d82c0c1d42e403e0080803410f0013054403000d880c4041c1c0046120001000c00d1041224801800700480270503510800303850001d19241c008200d80d42150092414050802c0c1c000d0b088401c914900e1901c40e844882090018100f40da04015165108094900069142c0c2154026004480c000d07030040203410f01400300310440c01e000320b9003050842060031440940b6401416420381108040b8215080d100b0642d440b042c4408003078000b900440c11004800c50017900b68090b81e40c10b6801407030180001e5141c4040319403428030400c1b40b40c0c892076640302107041039190303020000020321420030b40300100321202419081c404070641c0440e013000c00f0000000c000b400481c01c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 580426933 1250 580425683 580425707
    0x112030903150e10110f070206041e051207060f080405031b0c0a05090606040e0c04030f03031a010c050a023f010c0206011410051909060207210b090304050a06080a0507 74
    0x440b11b03d0041003245040556015400403039000400b4040814a4116013508031a03110b002e45681880f9030600041003401c0908400b00c81c155480704005200c07103540090954084140ca0500c0b0f8403a07181c40c64503d056010b09040c22440112000f49024100000900385200c11003d4805050306c948601c203011203060100c0b10720b40c0083c0108410825100d100c0700340c0e035001c0c80c243c41d40c07801c0c107403280e41d4410100211042500046d031070b90f0082c007078500840b12245104409082c02840c00740d10396a2103444407140303071002c0d20562134411465002140da034101b520b46a404000382c2015403007042c0d400700034280c02c110000750790710f82081e000741d40d4000220203041c1c401442621400100b6041040f9402d0606031300c40003080010f010042c041000070540c1408100c941c1c56400c005401c2c4600240341115643c0030f41220318040c81f46e485030ba0039240c0c44000d4581c0148041140750341d400003481c614401c80d407000340c0040b962500010401c1e80300d40c0940c014001d906042c0601d1700d985004a41042101d9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 580428183 1250 580426933 580426961
    0x50d09081306140703021504050c090403021014060306060d02190612061d011a13060537030e0a1b090c031e2412050c0d0b0112030903150e10 62
    0x110300750407da8044008254010721070b00450342081140030103d6018042600c0440c05a03010180300d40c0c0c003d149020303020092201d000060094505000060340e2000050200c6000d441507030518020354503248510034400a000d11410030300c1e562000c00070711710348520000d103504501d031100c00300e28122204014004600741c07606004140e42410400000ea03402810303640300c0c405041025459a00200034068020503c1e03460b02c40d191121644d10798100041a15a8101c3c40801c02e00e40c80683c658040341046040b0b43e1070f0000340500f464140354a0300e24603100240040c4948a08410041100841c0c042502c29004040c00040100c2e6070641c00c1d103047c4208206a0380c0d8116004d2004541984880b8882c40004a01c1c955500d081c000c030341120100e9000f81103240d002800c00340c18004200a0304000b050240c448054000082d01d41c0c1c28036000c11700a10829004040c01da8091522038521140519044200910701400c0407501c00e0041c2003030200e170b1203540a080e10211000040d40305007250070b0424 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 580429433 1250 580428183 580428193
    0x20a0315172b050c0f070f150807120207050f12091905090105040f1410050109060e060f030c0714160e07080a0c020102041a0d050609011203050d0908130614070302 72
    0x4820b050380c003030700a004040b2080c452508400703150343c0100070100c020302c42080b00016013070070041044a40074103411820103110061b010b0010319a800700440745000c1403046c00503101c501c00e180050070480f420118140501c00c0c1e4000c18907c038410740c02040015021100c00c1031880700b490031440036125034483c0c1c0ba071021416004000342c4c24aa0412512400c901d08001002103209800c0032100034180c0b4590926004c109080c016960004414009003105042420b0608031420000e109032041d02c9014800c0000400402c04150205040d1580740390f2003446040003111021070250781d045c020340080c4d903200b0b000768002110440614001c0c0140015614a00c40ea5103808021010b4003200e10b5900456608020000d82044c441003a80d5101801c0c4e0104e641c0c42d0349121a1000742ca10144c0810300c16140c1000403c194880c414110102e584c2c113050058650030185112001016007a1000d007540d8000119a004031300d13030041020980c3c0503a2a910b81000300c488241131a40504440140560300c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 580430683 1250 580429433 580429513
    0x3030806040b09040c03020108010801020f2502061b070f0506030f07090503031210060206070f0f03060306050103110a0b03160806240d2a03020a031517 67
    0x858446903521140c041c20128200318010007080c0c40031000c84040c0c55280076001c0038011580d10013920b50040c000c0900079410700b095210150503c0c4101000040620a500028103c01100030900300c1c1c0d1540080245403940039162112641000b882004a410f0145540109000c1008031881d401d071500a09801d00395622105200d0704e90401404100910040c1100092142d500300000c180b030f400e900701565814113010300d80a0200010b034014009540002c000c001b1021f03441000100d40034445c1c0740c07181d426002e01c03209900900b22504090019814000040b090200507020104000002e8620ba90503a40d40c10010115000a881d1030040110f02d21181000714031445209400c1100180000700c00350074030905050191a50047d02d5401c000030410341c402c0e040d14403401d001c2070030396181d000400051b641100d41d10225084448141130740428005070061295012142c0c29100c1110305601903283e00d01e10301d201400c0d9550304002c4c4280315035509201000c0c8514101c0e6100311011101c050a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 580431933 1250 580430683 580430687
    0x6040e0105012304090b010912030206160306050603070512090a0c0b090a080a0b090d0906200316050309040b0406140f06250201080c0a020706120e06010902040e01051203040303 78
    0x300e40740d8007454100300021a0000003d214000b080105107220001503103030554030014180c4055980145c51503c115021400441d030003041296110610f09094070200c00e40c0c0e90706900030700580d0070640d040103010042098064105005003136540c090802c0300341a940f00c00b00303999260794404008054000310700041184501500c068030200300c005007002400c54031502554034017044004203440d404101001c0c400383c08014030100b400178071286003800c003c1d410120003910b004286078012070000c000c01c0025907180e4013481036406c40015040803100461b800e0514681daa080340001c103201d0f5103800c200705518682442001c044941c0701045400140301201040400344240c14400e401a40070050b8010a602c3c9180c0c6003020f000300100400100901d000040480e1070007401a081c0800801c01c210f000c1c0c2d00000e0b40c2003200c0c0c42d4640951200d003c10813039009004121048040d5104150006c80c007500307150050416902d0791802402d690780e07650b0410800c501607a4100d415508100001d1022074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 580433183 1250 580431933 580431947
    0x170103151b0c12050c0105040602030114090c030708070c1407181e0e1504080307030c030b01120923010b0301150303092d0b09010806092205070902032406040e010501 73
    0x301c40e0030001d00306480941c201b4295442106c04036182a8004014081d811901c0c0a444040109031520700e0756140219803c54544005401901442a950b00040b00e051090100c1200b0f60b5210150341d520804030f030842031387d8640034003030303200d44241d58001411030321440d02c5103103624841c480500d02e650040d00620380050203460207500301802691509a00c82c9411803902d4000c5101d200c00698900d440b0a00504581001021404140c100030100c10f85a07444803400c2d00d02842540000303411810303880c0840e07142502c1c1a0040301c1480350209081c4004066001442000042d002406002c9042680380d50380d0352503000003030100325800c0e01400b0784000d401c502220662002d101040400004850000b04201503101c440386d003030009540b03041d40d41d01c4540a508404141c412908070308140b00c1d50862590740d11980e242103040e5045420074490200072420080031a00c9046541e824585100300200401902440000c04400320107000c41c2841400c50301100c1c1044c0c49014644d0809004450301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 580434433 1250 580433183 580433213
    0x507020f0a1407080f030c010c030b06070b0a0608011802040b030604051e01090602130302030d03140c0a021204060c02091b0a050903031201060f110106080a02060307170103151b0c 79
    0x40e104181c3c01140ca00c00805c038068550410344010b584490042042600355180e200d903600030036080c0040c0381c9480e00c801080d01d918035884011850b50303541d6054640020300741580912019820564641c140345005001c0c03c1015000355420300c00184020141661071a05490041c0340e54011020403174451100041d048201210000101c2d1002d100d440300420307600705c010590500ba0703002408004514003005000001d41c61170070140409420819a0801d54500405c034010b101d10000c0c42050091090100ca4451002215101e841d07945480c0c0c001c000c0c2c002003404038000c1c11050080395001424240c110030031101c41c60701601d04103180608a4050300404101d030341500c42801807442540c6801100c134007805c566907500344030104c1028001d066646415500c622030340350502c10700180b00c0124400c401d0540642c0c3e03281d43d0340c840920444004000411154001030683e0010003000b2132007111445848400e9001e1141e541150300400c240401c001c4000045083c0c240030b00001a0444141088 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 580435683 1250 580434433 580434473
    0xc08071101180305010203100608060a03021e060708090901060c1e0c050904060c030c0302040e160c0512040614120f0a330e0601050a0c0813080606040507020f0a 71
    0x880494096040c5122803900f040707403a650040308000c8550030031080a801050030303141c01d9680c0c0c10700f80c1c0130403018107840c04040e0041a00030100a5401c4c0200680303010050042c0042d0b40d240781c0c905100c0000c0e00032080d024802c00107034000141052054003428072298000c0744034502c010700200b00002101306c9600450f4840d080d5100040d4590b6150443e505c100c0c02094003181801003000c0050840301034500e45070a0501c144020f000c0c100c00c0d0a00300740d001c440d0381040d80031600982d03001e9030075078402d6900034442c0c80383c1044040a24200c001134012282c03107441e8003003905010000f8501500850381032264150340a000a0a07913805588c545401c90ba03896030000760f040391443d80702c0085a6401c400e80c0d00c4200d42484154982d45900c0c96000cc01c6451801c100e94184400020520b2051540d007008104051910005000c0140111190f88000e8068040b50650b1a401580c64440483d04140700c0d031700d88000210f00500126101089141d00c002500c440c2c0510b03942ca41c000c20a460301d44c10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 580436933 1250 580435683 580435697
    0x7120906140c1f0902040c110a060f110a090608150f040b0f060c160b03010e1f08010c03060302180906130f0b0405030c060c090901030303020c010e2b0c08071101 71
    0x300c0f020a211030340224407500000c5600504d60061109640240000d1000c0000f08040303c00024000324012506550050700420017805c1a03210340040c000b494003c0d4005440002d1155a46070404040030495040b511503602d00c0d500c5031740d41c03850000e400c00c0040c0c0000c541c104d514050301d0194420070080070003c00b200e0320030b011100496005c0e00115000810760340301001c03548426014540950003010f0024609186606091b2050100d15007e0400300406000100c4481c44480c102d00700006004404000c115060003103030700030040c00d00ba110590080f540d21140b40040303120030000e2441002c3c00e900030055078a0b0f5050707a04801728044403c0d04c41900301e50000300090044403096001d107015000071600d07810500c000da42020406009081c40f060304020300e1409407603a180c01030460b60541030042c0c41d0017101e4000e5024184003203d45100b40607440d0764000340c4601005502000842410122030182c00b48810340e2589545000584207203070500c1700354005140a0ba03018480030040c94004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 580438183 1250 580436933 580436953
    0x31a060f120a0c12090809041808030f1005030109050c1c050102070c090510030c03030f050c062e0501020a0f080f040909111e09090f0d0507120906140c 67
    0x501203402d8408074007031500c8039015000d8036400802c040d01360001d0300c010800f40b50144e075408003038480c16550600540d215112000003290a21003c2c0300703150040a40c0340da900e085a000c2c001d002040b1a021540203a8503008521420144a090742c5d0301d5002009010441c50343d02044403240850305400e41c180084510000010402c0c0050102184505890210107091100309025150014050314400c00c03a56070030408220108004070072641c02d41800405103c10f002c08540078031550f003d807a51480340800f8044003503001d003180784104c824400c1c10411001c00312080c40d0800c07290300ca4140140c1c0304070180070100b511280c04000325486880c403140781100400ca41c00380b5411a5000b42c5056640e4038444062020008089500c0d01d0b0845869580420300700482c4024030302241041d00501d00100020399507a420822884520b4042d0110f0308441c03400c80c0e000340594010107048a40340e0b000e140241e00c1c50b00074119041502c101c0c0d21000c1051a40d0100780c040d80c0c010340740c00c08030b41c81b0f510210 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 580439433 1250 580438183 580438207
    0x402040f030b060906041b050304021306030b06090f10090b0406052814010c08070c0e09030a0311040807120809060d0f14040203030f070303200c0607031a060f 70
    0x903001103201e03448100386464058104a00074400400803030041f0b09000003d032220360180b101100406160034071756169115030002c100e5221119000042c8507150480100900c0b5407203244500c40d0104135000d0105684460800281000641e40b612640b006100240031506264101c10032280300030b440041e00d00c1e51840010740411741e5100144018984119070310700d05070380c4909440940140c881400500800f840002d01611070050b000d0320065001c2040c01c104000000800000e004040c0c1c0000c450500004058aa80c81243d06001103403800f443c00100b80882003d4800329805003002e00016850224001541d12004c0e40c11550b0701c0080022004903500c4e00054254010038440019001681c3c4a541d411129100000c1d105624100104070050350000211052010344c00c0099440348040e18040cac2c040e001c00759000e07078450b030807c6841c0c4000e2050800751040000007021151980c035140f1055080303d007140c1c0805a0003a081000354100c1c1030100092400d0907000c01b50528041c102015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 580440683 1250 580439433 580439459
    0x8030f040b0a0b010e28060503190e070311040b03070806150f0904030c02030f070b030a1404021315172529040e070f020d030b0f3c031903020307030e040204 69
    0x8001c01040010050054a0b42911400c06840c2181c0c81e0812000c14216002692503003c1e2000a000480f214060ed015407519000580e0429002e02160901a10b03607001545030001200c0c802c1255000700d1504242c0e1030603080b600003008002d030088000c0d0319191000c4030300c1c0b0301d0000c059801d442142607901d0009010401a0010810b007a00382d520313400d01c101c400040e91520254060603200030f000303020140e03071034103040f40490615000c0024181c82c8030100841d012403960020030840d003020716100030b4000209207901c285400400e03c84000e4400f04410540c04003500a0b01c51424986940085070f031110042210042a001040c81c201a51001d60744d0050304d0440311400004c1400040407203642e01080128850700a50909010b50025100030610319110b5403103007807003811050700715640031007051060740b01315440c00b104000d041070340211810300081000905020344143d0602e203240c0d91102d0f80c1480c06590640c00346280c650182c03002c44800301c00400302c7c0e5005a003004001784148011007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 580441933 1250 580440683 580440689
    0xf0103090b3c04120f020d0f030608070e010906050d150c0507020a080d020f010b100c021c0c08060601091d060a050a06020a11090105151608030f040b0a0b010e28 71
    0x1a0180c0c03d2600d4038106a003410102c030014180241429003c2e00e107600440d50300c220306080d10349013001401054040340a01310702c0c0c0c8041c281c4c1c0114180403801c000d00d030700070368181c40803c0f8050021079602e20501145000070304024091000584160424080d550070481e0b422070350340b5240341003d10070340018881c14415401000340768021440002c180350180010303a965400c0c0c00c000c100b503884100204012001c0b17420101d0411010303080503821941da04100111507000080700d03030300100b107600e001455140c0501607030300d99204400005007103610422154050311104031704903407140018144e5001c1e40d14040d120fa64442118200400e241e10f984007000300401c141d134010651441242400c42e4054020b800c800d0091080340700501c03c5403140140404101c040e40d010703ea4070004d00405c1c1d035515018940c01050088004217008001c40000e04150055000d55140d00d0710383c81d80305c00d1134126044e0002c210f01007245034601034068540342c0f552620600007288910881060440c1910049000d90 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 580443183 1250 580441933 580442041
    0x110a1e080c0313021518030a120509062a10050603070501032a210e033720010902010806090a09140d030b0108090304030602091f0804020f0103090b 65
    0x10071146c00148094107001854541034001d08800c1010b5240c202c40e10007030014078800e20800003640d0482e074490340d0894516844030920f8080d01540342441c0e401e9054103404140440c41100b0010101c00c01610540740a050010300422001d86040e0040d0003800c1c0d031102010713034596a100d01d0f40103251b0303a84070120700c010320340c1d124031200400700c015034511040b8401c001001c0e0304d09501a02c1050001084a030094058104001c034944c1c0110b40b02d00b01d5450a4469510340c804020302d02041790450407864030034560b44014810f07415601015422205908030190000702a00c001c6000382c1001c22a548d00308000c80350205510400e0703190100c02d49450100a2a9039002c00f4840d0406035162003507803100701c0c003464000358070300303201700360664900072404054013240d40003c08825036503e290b00e81081d40ca2005000300b03441c0c1c1ca13100c054284c0c03104540980c010611078842c5039080d031280c4140c50304182d00180074100f50726030b18069842c091114100100b810703401090310b0603058140c04003441e0343c4012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 580444433 1250 580443183 580443187
    0x101d0f1801050a1d01030b0916030f05060f07020316080c0a0b09010608070521011e05040501060e06060406051606060b0408010606020109030503010302040509070306110a1e080c03130215 82
    0x128042c014841c410740e0024600d281000718000107800c2c04609681100e07080045901e540d100c03008060b08001d100c1c1003c64449c020081d000080040d1b00075001420f60007613082c0c90160744c44104103800b015040705e06400580081203505552110901c44580c02801000704509120513800c410b0f140038811a4151115541c00041040e018024081e01c006045040c02514160380360402092480d8180300550701c024a8000d07548103484400d40c81440030364000da02070304842c0380140100004140a80b000e0716654201800030030384580c9103400e1070040c440500340519242c90040b007107600e41c0004e0b440041e0f110400d240000844d41500920015140c5038101f03039501d40c0f80448140c2140c1c100ea016109590500d0410400b084d00103065a0459406a4000c00c05075150f2b2203690a1500300d400c005c2105291684d410a4030a510015001034841c90310f429110f20f07040c0031344141c2d10010b4440d45002542d410001201c02032404c0256401004901c1100e884401a1b03001682d042c42c29410140c0070440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 580445683 1250 580444433 580444439
    0x6090a020a080a08040b16020301050708150109050325120812130b010b211f0605091e12010216020f0415030201083111101d0f1801 58
    0x58070400c8020007504000b08015021540d03290002c2c01903218500b00803001140e2114100841a05600440d40c010001c20061034002c2024000200569100c0201c000f4981115503550044880c80240d40c8003c1c0142400303007142d410065050641c015a4840d2001b2240005400082c640000c4050b4402c452407900d511340c00000356402a001406411034403010502140411501c58016041d61540c60802d6666610203681c0e07032000c0700c4440750100102c01c100400609000c08490050b80400e0b800060f2034280e034400f0111080c1c01101d035000e5000c01d0b20554501034152140307100b44110340140c00f1136040704500d018180ac80c0c00c11142c0d07290f400c4910030080210302e06812202d4140030b00b100c00f0440480c43c1c00400d55400f206000080c148505800030a1420711011207000300e0003010989822007d44109500380288010346040b6000600c60385000050300d04152003a50302c0c0016030310900c0c02e1080351821621071003c44241504261100410307100b549031140d4081c20740074503017030500305945 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 580446933 1250 580445683 580445689
    0x1403030402010f02120f0f19120b030d020309040507140a09031a0c0702011112040f0302040b22110d0c030b12240415020301081506010305040f2306090a02 68
    0x20f41840480308540154089144002c54681030301c0c020f052000d00303d51140b120640d0f0340715510981440c41c107210f040c0b50304d940100358449010034040c041c08409102e900c283c0c500340350742e5540707021400c000b42e0014850410141060352009900c00624a0113200c03000d191840c145a581c88030381d40400045d02100144140300c041f17044624204401c08120302a8a0840e0086002d401200720003410007010410703941911604002d0000074041e500132082d551903455018140c440303a01e00c0201e01660504400d180310703140c41102d02c10541d80c0d203200c0300342e5404001d041c0703c014540c0d0707418007810103024848400c0c0c14041707100720041c170132441d1400602203010400f00802d400c030124074030159038000303804043d241c2100c01c600c1c1850400303406120b2064a50b80b8041c61068558244184814808000040d041c200015142448100c00e22220101d4403240011026a0000c8801401c0c3e40001d414120000300c1c0c0c94408084d00c0c80050517020655491456907003040420f0350091110341c0305129580c00e500d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 580448183 1250 580446933 580446947
    0x308070c060807081305070b030907081b0a03330c1728180803060109140f0603040305090409200d1a04020105040f0605130801090c0b0c030403140303040201 69
    0x100c007a0070202e0003440c0c07076040103042d038074001c21120145422400f0041001030400105c0701030402c55100c04d0f101c1c5807802c4010b84d94500c40c442c0c0c0c026803040d07800d80c0705650940c0061642018019103402065802d6032240080d40b11082000061041c14a003002c4d840180c0385039094100c9140b610101300d200203103600500302100040c81c51011a1910180a034107001d0200d421302841c0c02030914900d010403100c20b000200f03204064003010380100d014420400200e80025440342d442602c0b1100c86540f550407215481c180c80443d035802810403d040b12a500d8102c01642d40a0310a28109185c4002d52022030240c40c107540c0e00722507500420790040300d0000c45c06223580d0608400d0340d800c0010340480d00e89108403a41c8002d07420755420b80801003820343e44100c00300c4c0c01521015008250f81030b03035501d0041059020381125061070b85000800300b070010042c00380030407840d084501710740400c0c14200032480c0e0b0b50010341e50070150f200803c000400a440320410504c81c1c5203120241d612403a00d400090104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 580449433 1250 580448183 580448189
    0x50307031e03050702060a0506010905030a05100c0c050c0418200103062c09070509090d030510030f02191505030a0c0305071b03050f0d020a030c0201020c070911070b010308070c 78
    0x414108410406440c1e170006009601c901c03e054003164684400e030058552800c584c000c9505801001e820100f48403001441c40803030030000808108885c0001030844195220520042003074120701a0041c0610f0680c200d81c2201310144142065281980d850300e900030b0f4118001d04c00e600d55094071009940e0148144401000c0d02c215030f100c010440800301c0200c45046a070700310800e080002254035640c0800041d40540381c098003003034041c140b0741c040566070354030348010320002400e0600151944c00c5015121080b02d42c44000c190b83c030b091503070800c03414900c1c199001101801c1c0c950000b403181d0b0000c1004201482c9911000c0e540d04041d4114002d135200c0083e10b100f0b00d4101130901c81100d5100c982491342c1c8008145030b41400c1c20340e01d82180d8a106c0d40001c1a056400884c0f41c43c1c0d5020103500078007402f441501d04201c84807034000c080e800d030302075040c03e18100c3e0004a010422140640c01050140207030341045490113015035581d90003030300e080e00161840e00001c00e0030001c02a1000f42c01003e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 580450683 1250 580449433 580449437
    0x1a1b04141212251e1403040f03140a08040b0c10061a0c24060102060a14160201020d0f14010e010f2309012c06061801020703050307031e 60
    0x140124598116003280300e03206410000369a0000401c0b4040f0030028401079266002607003405012100e000140d40b400400b4080c1c860842c03802404201280c0001100c04940031070503004003da1039511881c0c0001e407100701a5105002c0c80580000180c200f10007440580581c000a0751509805001c0714074049010031403821a40c9490818081520001c0c1003102141d10510096500c3c91545120340c1841c111004984942208080d040078084020310400e118000a03822034825036034217030019007940c1c0344208050303051155501040f0540d009640303c1c501e440d800d000140c41d0195a900303240495114200c2c0d100290390f40d04860044001c5070742d00c80e0052064001110595040880305091100248517000440c0003a0103100f20041c1c2d00d1700c60603510744004061007290341e034890340c8583e202101d0001e074040d0720700060314044006852504070301441014000030f08240881038445400c4040c0b042442c150b201d403410000000d8030070401001c1e051700c6551501c0f440744a036035a515640c00f03d1412181 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 580451933 1250 580450683 580450693
    0x307110604020607020d03021203090c0103050a0203132a030501050603071d010501050d06030b0420030d02072607090e0c0f1c0204020c010903020604140a1a1b041412 73
    0x40581c3d00d02c016070384803e804845ca0701d6140c0d000d242c01e924204c105d003410380c825000401040b0098801180300818000300f03032030600142d035880512508034441210000611151802103001042c6801842003c00c800030360f100c8151100300d6040103040219900031516a91114104001400c007404039100404070040c0f10ba003100ba0b000f0b052520440f0500445040060220705030380301280300d170001001103400c201c03000e110f42003505000750008840c225030400c625520031a0a6079040c0000c2c030f2990410b065010345483d5041046011020b4649107034101c042058500c40211020301f409020000c0c00034090014016980d002d40600301200d400070b1074031484804000d507030152510513000010564500612040300c0c0240b0004000340110502c00c0820741c0b07480510001c054000542da40581e00441c403c440700e14001018a80d100c000d0000242000e100f8140c0c9070030107601795507840e0440984802900d0b0441400e942c3d101c160030a40c8110f101e50308512060445081461600e0075054100300602 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 580453183 1250 580451933 580451941
    0x80f04020303092808121c06090f05041205030c070b04110616030210060e0604180503041d01050406030807080304030e1e10081006051c060902120c070b070c030c020907030203071106 80
    0x49024011074001f541c4024095401007108a4107031702c81005000154020400c40740c40c0703408100201012241150005002a40904c98034001d170300343c0f80300b180d000b0320840c039002d05035541c403507412400360044600800103019442035588081c080d0500c01c20000506ca50030326107041c005d1810081009001803180741641c10301428101d02c25207548200e06450202d180e201103003e01d1180341032458090400e000200c0d01040580c0110344a84450f001d078500d421040e42c80d80100300c101c81c42444001c02c05001040b081c030016100350003440e40280a0b0600100898070100441d50203884182007010090400c1e842610b2450046808215002d0500c0c1c402d08604c1c1a00d108600c040860054905101001c5490b5194883c241c400d00f00d1040f000c4004d000300b95542101c00080d4100107081c0c889103101000161030001f2610a8503c0d840e003000c012540c688404a0568001c043c2007402d80c00c014040d02d0950244c3c594a030518000d0480f035400598914102c0c60003401655121008001d43d00480180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 580454433 1250 580453183 580453213
    0x1905040c091d150106020d09080607080711070b0706050a05060312030a060f1203020111070c0e100e13050609010b13020c0312010603060302030c04020a080f04020303092808 76
    0x80025510200c1c0001814040d4080d4804150385844070070b45640b04110a82c5080c03a04041c0e00c90481e00d00703400f02c6030304020300b0f90151460b40c1c00e8020348415602101c000742d01540f0490659810000e03500b003101841e11602001e5040030001d40004005003070000d482c0003004000e22a683c0d001000440404c140d04001c4000780e190001c0900c01091514003001184a109003a4080c8000344041c0c050000d000c0d54a080407d151a03040301c055015510b44038909111406010071100e05e40d51010000c829142851880b40f1052030107864441c8000b1400e902003210740e0341c0701a035401205043e460000c4101e9601d40140382080c010984441c42e41002e013808010340301c110300c0d15018418141d004d0780710400300d010300d07296000c4d8030f0058019100302c8000180c0a078259000c10144d9000354256000012130800307101c164401d5400403000070700d00302c4c0050314400d061354200350414801000d90b8a0030268800249605070880c0701e490001e480010192120349030140380d64001c119103000b502596505400d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 580455683 1250 580454433 580454453
    0x306061206130e070f0b040b030117010f06080a0b0903090a0b071b0312020114060a030210030b030303151e060f030a060e0a0204030311071809051e0105190504 70
    0x4000310005421012070300075074030401001212009600704118001d582d210580e9a441c0324800c004050358400350229000c11400107e4055030644140541303103900c0e0103e40000b2a142e94480300700c5568500e440f003180351a600030300c001084e8444c0144001c0c442d80c208501ca0b611701405e010569441006880785585404020008541650744215120015410401a16010901e018510300c020f80313404000c000c00c800c151a103c14041d0f0082120a00c00b1118540d01101030381c0b070130f6015481803001c10044c5001900e000007413103949008a400010000401d181da00255042c980091031402103040e141018012100c00024414801440084150109150b0f1065a001a40500001000070113410ba55005030004040e0350150241c203150001070080290807074041100099210200320803921030000b2748034295400341b000c1c40d0682035003180d11002814110f00c01c682e60301868410b49084520302c000080e0480c0e40f46c00120300e918244504200040f20845041e840e603190000b40300c01705400c452 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 580456933 1250 580455683 580455697
    0xd0e03061f0308030a060602060708100b160605070f030b0603010308071e080a0203031e040c0e090f030f09011b0305121003020904050d0e0f011d0f060a0320030606 72
    0x381181608052070801110381c007264102500001000082c031420070051b40c0310004480081d801d543c020749440c142224859010745500c181012401d41c24064100d00000411180f0103155110f2035220880d621202942c0c4100ca080c0003041c201c8012182c1581c060041000c0ca9908507003161466041d40c1d9640140c0c080e41c02e0180c454000341d0302030f80440000507038040325a504403161329101c10b81010025900d920844002c1c420201023104042c868007031448043c0200d038441050032516050000c10078118400402e5060030f4490455013010b407004c2400182901d694001403d59a507440200140460042c401500c0a0f12078103040e100201b030b8004252010142540c0e00721116440e01c0c2c82c020072400190b00041d5010094405010410000113034000207508e00b40c440c016000c4041003044035000d02d12501501082d1190b16001800e18107a00311030030200000d0500b0703968006080410341d640c010541040110365224030714015040140c0d540205088000303010f91031490200041445801056 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 580458183 1250 580456933 580456951
    0x51b0a0c120515090c0a0b03150901060c0b1f06020f060c121605120109020904051501020a08130308040e0411040915020c010f021314030d022503170c0d0e0306 70
    0x12000c142c50344c109215241c3c0001c0010720050090f5114000d80f103040d401543c0030000031031440804002418242c1010313048a0641c3c0b40e0402401c3e507074640312012503000300003101c2c0500b412001c8032002d003101440f1001d410140d00400c44280700c02d074074034076050010741b102440210a102c001c0a0000c1e0035070099101140b80c4549440038114071041e01d044c042c00e005940030000f400700200c0c1d070202e981e000c0d106003003003100c082c02a500c9065400e00c0c202000340c0f40c80d0042c1c00c44090100414020346c01030a415041850307580c80c0b907980b900ca007801500940c00140452403894180000e000c40d903402c0810360744003201c3c100068800c607910b0313010840031a03503030b050340c50340100304803203415000c0d400100c944004070425950f501c0803180407a000801406007140800c3d480704200c142d824001203005880d4582c4e0000d005c12501802044100f610441c02820616503000020000415405660b0890f071000034070b5944400900d4039a5042944001c0310004100c070014500c0040e5174005000381d0071000503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 580459433 1250 580458183 580458223
    0x2030c011b050303010e2505030619082d07050f040905100603030203041802030c04030609020a1206062c0a0b040b0d080712091d07051b0a0c1205 64
    0x810381d41c601d030058201c000d07042d400040000282d104c0509045842200742c2142c0351006a4008582c00c00c1c00c0e80501d01c400007410500c00100c43d420541d412044d56052a90030640740b50713032040f07203514140d00785083d1450070100b51080b8003030119006211100c0c3c021a006803080754185408181c4404a46001c1ca01c1151510041c0040c0b007401d0106096000305403e091050035140e04010b03590340c0c42413140a41600091500b8047c0008501c2a01d0045022000b8945172070310b036440e545c0241240110aa9200582c1080000e501103a85048292180724182c0844c119280020300d07044100a103000c0041c4100b40f4103012441d082100d04c0c19403290b400c40c000034560b500c4101040040001400c0140c000c80340144103400d0000b0b4a01a011070ad20560340295400504c600031600103080d44181d4180d000303060550400303d00711440c0c05e640b00d20249840c1d03052503084510714600518603540c45505812850720fa60510521141b02d030090305014441850340d11050b0703103e82d40c0700d080703001545449440c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 580460683 1250 580459433 580459457
    0x1e031b081207110d021f0e060105060d0e1506030607051801080714040b07050106050604050a030b0403120609020310081204051e030d0210050115080a0b0111010f1e05010302030c01 79
    0x401400002400103411540141d44104c4080d6441e01d40d194511010314140c48800c04448141c01000912440e00c3e01901440c0d00c4c08040c40200c5c1c0005080950098075240388000550040003100050400b081120340e040c10603400385410014090030003410490100000c00728000c28241c4c0240765003083c038100c4895625030504a403004264106d00810704400100022100e10000191100c039005030003c000740382e0307a8000c03c201c1d0f05c118821a500585011401c1011034155038005130301602074180203002c0702c000455202120120380006407601d034040144036440c903a40c440c52004c2e1890400812201203004dc13103002c0ba00461044612845103544e03050324001230a00c0c0d1844402c00901250029586100042e40b52014100c0a02a60f46413100010b1115141c0041c00e480009a0303e070390301076480c0e001c6100d000c0c0803200d4449062026031a40b469680b10248624010100010000a400190004039080e000340d0060701800b102e08001c01800940c1c1d01040001c4040303000d0a1240001030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 580461933 1250 580460683 580460687
    0x10b090d1b090f0b09090c060f160f14070f1a0c010c0207211a06060c16090b0d02060a1b0b010303031a010302121906031e031b081207 59
    0x4801c820342045505a8100000c0c6034980b50005030344143e4609090081041c18000d22558510440f103100c019402030303d40001c5420010000d05001160001c0d0601c2c1480104030400b11855541c011145010f08906001c1407049010707100d0011105480075040b2035141a524165500890107190416491618020300248681d01140c0044000e04000c2c4004c0b05150b00c06516042203100c1c4550078808054002c21340f01540d405809000d5018501d00000e812101310060450801407000303400c04c108201c0088020410444480400c03c00c249861220741850341ca0003c0c1d80c074100313400c4d001d4051381d12647c0059072034030140c60800c0c82c945001503c25103282c06440007003181103005031007000b0500c00403080c150b00d41c12600b4210031245603c9901d1740d010004500328420800d842d40c40c081100c0210300d45129180d800c0e450010700c00320100c7c0d120f40b01d880e11601025540000c58515410200702d0040540010406088118806800c000328130603444918551184180c80c0852851b84030005803039078 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 580463183 1250 580461933 580461953
    0x801062f030d05040803150907051801030b060c1612110d0c180b0a05090c090409150213050f0616120c0c030b04031d030c060306060c06071d0306010b090d 68
    0x2d04100081c00f042c189070901001c0350f4402d60710031040300a8041c0135000d6050003406140500c02650f05d5500d88045100340c041c50001c15440329041544070301180190399280c002030854141e041025003d0303044c0318040c40a0071003103075020500b215aa503c5080224002d004403010381d0505036032981c1c80b803c1a03d020909100b00350000e001c80e0049c0082c1480741840c60303220700102d410179103113a400c0985032410040d4201040310100300c1000100449201428a41c12982c01d9601ca10300842c4184d48940b94034041ea040320b0303000c002c001140002007250b4030b801c0d4034000c044c880503142c141c034100304c50051410a00c500040644601d0381e4960210300d8621681010149540103034002007420b490f85407064441206035022b80000e504203226640c258808120310117100002002807010441c9403051040540004200544c00381c0180410782c4440410f2110912550141e6203114242e612070803400c80c0402a134503450300950100780103000141813001142c420000c00c50348400004000c1ca0061514 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 580464433 1250 580463183 580463197
    0x70206032a0c0721080a02100f02070236070c0c0303030204180501050a180e0106030f0c080d1407020d050a08090114030408040603180615060801062f03 67
    0x2611941d98541c0c2100703800340260800b6204202540c01150b0345075101d83d0741d40304401100c0e003188910300e40500050134200042c0980082d50040d1002c124a03400103108581420420035040d80e00002c0d14021458407075100d09200d030034004148200c1074051007826284800000c400c0100b00c0c02004141040d01070406180420b5121580c0114140c032458020045e41191048581c2580170003011b91889500c0c1c0030b103905032540a000e418032903113000409000f060189940700140c80da1864154003580c1c0a0280402450041c400310900200500e00112031500b03070740c041d02941e0000c80380011181d90040c3c0002242210680340341e02d4030428000602800e42a1100030880e201d202c00d110100b10000016000440090b00c405804400651403404248403c4070018a070090400050100303a0190b44265508440d03200c542001491650340c41d011200c1e0050030300a0608907010401405030300107071b41030240070949000000c071903a00315458040c01c0b40f0283c840b0000032580e42c1819520040081d105e44e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 580465683 1250 580464433 580464481
    0xd080f0c160b0109150e09250914220c0608060f040f0c140a1e031b080a0c050c190203240115030c05030106030e01060f03080909070e010507020603 65
    0xe203580da404258010505c00008451002600e080002c41d0b0741621240b600c1810103030090194401424908584440d01c284000580380e14440d003c981311940c7c0c492220b0141c40002464000d0030000340758513202112041906070525481110400074509480083c1103982c9410040c8070b5460b0500051000701202200d650001e142c170318080f031810300c65041501c5448490b103415003200c0c03050b0155403042c0f2407482e200000c40e4483c040340040071003c88c10040c00d441c151600090380703082210011000d468000410300043d003550140984d0000e548100b046000c81130501920f003080000d00c00742c4400440c645000000040c5506005540301808801d24550b16040020048403103100240d48070a001c0c0190303010703004e501140d81c18032406485642041806600d47e80c3c1983e02c1d0080072409440382100c1100c5554a6980010310750504441c482d026504ca0074049480380d81001c14041450802807031441000642548001c19903040001c2791611074061715213a03078a17a101c42c441e62404000c1c546c0702c68 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 580466933 1250 580465683 580465703
    0x240c010908030705130506030c0f0309010908040b0406090b12070e01020a02030d090e100e06100905150403020f0a15031d0d21290d0c0e01080d080f0c16 67
    0x30710f82d640f001c01007100e4120140844c880940341e5050124a000880c2c504111902c10004111804010006144c0c02800c44001040308480345ea216801034000d644401d00c1c1c51070101c0d00b40810341c2c128034800c01403c038075403e0a042442c0040c1222607401d0241c2081d007403203040400403406034801d0000d000115000703000c4412444500c0002052008a40705102440c152000410403006900f03440300101d0308218a000d801c0c0e00c0702000c00c015042400c40380c400340500b2060020b03841d26444014046014407404064543c1e00e140140042e0741a0741003098412549080140280d14849100700000b048520b400644a4540801a1903404002e0700c2851079101e002400230900341c0c0201c000d4450b2040009410b07100d6081c0f450704061b5000443c0c42207480603080a800c807240042c02d489000702c0e0008200b00448840ca40310b480a0320b8494203ca2440241c202c018001924100096421099603240182031031400d00e06104e0408030140c0707021120007000541c9c1015000a410030200c0740d401650342c2e9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 580468183 1250 580466933 580466941
    0xc09062701060e040912110a0b0403080708010918082d0904110c15040c1503241d1308030a0504020118030506130c12061a240c01090803 60
    0x50303041400d124100010310315440b56105401c0c240030710003181d68009148451501410401d940401145500c8400d034032450701d03c1d1005c58250f0700b80301d0141e0b0090300c4001d06d5080c03413000206400c0c1c050f085201e045040046540515809905210781c0c0b58000401c0303629608458002021071041c0302000109002040c40d00c001070215100419180380226001c20005c0e8246019010601034190f556502d600525074000480d540804101c0d803003441a03400101482c4c64401c010b2509405000780da0000ba035400b40080341e096001035090040381140b101c00c0c0c1243c50722044036100701c4980c1e01445800001004a0031a210030390100c01c401da0b01c142059101e103072809400300180380032582031380010000d91740240b24141140d1300710180c9421002030401596150844074032102108000c465412070303803200040d054134115038079010611801d00482c401da101c070740c000ca00b244042d18803445801e2804020050500e200c090448500b0f0501c5800c0d2502d1007118032034010014190f015214040c000100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 580469433 1250 580468183 580468249
    0x606090a06020c0306071814030a0b0a09110a1809080d020304030221190f120c020703020301230612030c030a260705030606070c030507080f0d0f020c0906 68
    0x8011410070913012261581d8500408550180304002c1009402c01145001d00980000d0103411035104400342c00c03103003e881d00b5600c00d00f054800300d80d00e40a080c0e0340e44001382041042c844180915100700e0300c900e03429051600440311442805012800b840d81c400104080050450940301031180311b6408640301d107070a0501039143c2c15194507c1c55420040703422500081e00c8901511040200c0000d1040c0d95005c601c4142e5a82c6c8030241000c0902944000c980451203150180800114003079028000c82031451051509550b058081480b0380300401900c001700203108150198031003001c8038503003010800e101c6528110b100d20b10b4407090302d000014084501c2900240d140200081d19054500a210610101040890f00340c0b1503c1c00540c080002c1030b21031801001421502e03004d801c04c0c0900c141c1c4c9a848929007543c03039200d01180c1d001082d80c1042c0f10780601c10b600350080c841c1010585131401c0790009448140e4114550b10075182d84012983d01d44a5101000c45002e6031401c09600b00144444 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 580470683 1250 580469433 580469443
    0x405090102090109080a080405040c0e1203210108122a010204030c050d0b0403030b060c010518010e24040606050d060f0b0105070f020d0204020c160323030a03050606090a0602 77
    0x4143e02240880800003901171002415810071900001c43c0c0b0300700740c1401d0401000e480503018100800c62100c003010344903554459050506040d900043d5951440c1040c0040c002484082d000c024504400c0100203105010818900341c40b84038609a0303031172000d0141c0c035000380c4d00724034100030500d07006100e4403a00c041503000b0001c0d2030040320741000140d0f030380c410442d000f607003d20001c1c0544807900c00b1a000a0080d0400e0b07401500041110f4145890710700b4080c01c4030400c0b24807190620141d00341e144800380a1107420f200d40159009400b20007001c00f0303444041070464540e0b051110340c640000d401c1c00347c1381d4452000781070010803427600d0b00e0240c140711700603000150b0310b007540724a04440001c80798003450840e91031562029180f07900a130305408004d020007030b55000f40d030055000c200d40c6241d080140482c02c1790403070f014840e040980c1941807020201410304913400084c00d07000c0d41284111400800c0c2c43c0c14100d245404900340d07403440c010400c1405032060961304040b0301038002c103505da00030030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 580471933 1250 580470683 580470697
    0x90506010507200f0d08160215070302070e01050d0c1503060e040803060a061b06020c10050408030a06091a0f180702010c0201110a09030803040309050a1508060d2f0405090102 77
    0x70341d940307036070313440100b000034501c40d4110040c1003103410040500d5007180440901586400102115650104101201d00583c4030705800c030016001785105000c0d2891002c0ca4a0141c40c0039503406034213107410340d41c915600ca02c5004440d45520011404041c052103900901c002d80204286468242013a1508031155002076920611500c45802c000c42c80d51301c0381e078002d92240b00c42c1c001c102e014140f9407100310081d03010b41105400f07030240390704114021a050189030300a44c85002d05aa0f03a1070f081e100201190b0039504698101828001c8450380281450315101640341c04940271004000138400203080c2d58040f110716141403100c107040010003501940055110600d80c1c009111042c580181c045080c4500041103010890707180b000e001086010b805142d0144c82400e0400301d03540c0703610000703030400d030603600200303c50180121198400e41c1c801140c035003040d410340c0c1d000c22083c40c0c1d903a2032034100c10580101c000364802c80e482400c644c2c510110a114204003034001c01880c18444020b5007c2d50080c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 580473183 1250 580471933 580471939
    0x10e03160c05300d0f0e0d0c0608010612050c0f03180109110102010605040506061b07080a050c1503060916021002120f010f0e0406020f0702180702120408030409050601050720 77
    0x460381810201c1c0411414010101551750354034112089005890481c05c0c500103a400a601413500c10014080d51540c1d40a00300a0712071074000e61520400509034500a5954a0452706040c00e105403070400e50182c41d451050101442d40320745d03480000340364045002804030803d40c2440c00c1a000c0c4240107158441d007081c20f030300a00c0038648400a00081e10019904070f03410500801c0503940c8440c00482207d407c2c4101400d07124510b541d4a00d4516000302450143c840341c01070407140c3d103245040340d6140302850810704014203500e0040001a10210002c043ca0301c4030541c40320050480c0d1080c440070840b42c04151046444190520b0800b0054000329583c02d12001c1d60700000c16a010403041000480720301c00c1c5400c1042c1c6d40c650b00c04001e5005a020700c0100a810f0000c5d90041e82c2d5140a2103030a8078243c0c001c809864035203002454280c0c86d014800a01c50100401e00060030f0100c12a4166580c190010841da1900b00c01210759204031440645102116034040c00d40301203251f40034a41900c11 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 580474433 1250 580473183 580473259
    0x2010e0414070305100b1c0e0604030807120605131a040204170d0c050604151e0203070806060406050901110705040e0a12032a09170c01020f010e03160c05 68
    0x10725883c01741c2c00c580d008a684c2d0000c140301c0103050086a101d0070302000103110340898040c03072801029140140c00d40e0101d01080d8500100000c441c0e10415861801c025110240f003c90720f060301280040100b43c0140d411980c95010343d40d4003610320740c03e4071501c01c0082c20455545a807500c001c80420004004860680100c2200f80c821901c10070340401000d0300712010b0021501d5565030a40d41c08007515802542ea80ca40741403d0468201ca21544048100804050303504d140140307005000003001070040c0e2007040700307000900100350b0100544c2c2c01500f081c24414a40409402e00d0347c0380129036442140c1c0301d0b0030440040c59500340800c2d0241c1c104d10840103514050680700099003503031008001e11000c159844501805e020f80240c85040060032070400c1c03803c2e00d0700c40701c0400ca002100646456194401c45800e216540e04100c4041034a04c040300030041e506014240e29124070032a00000c001d03050703001c040801d000604000d107000300f000810360290960003c0c0c4035864402002080310ac00c101c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 580475683 1250 580474433 580474441
    0x22101021e12070c0c0801050411030f060910020726041811092704031116030c03082b0912051804020d09080d0e070f030b0601080402010e0414070305 66
    0xa44810b842440c0761501c4400c1d03403980d482d00c080707482000c9210140d5802d414080000b590950a20410f80144c1c040c030001211480c03664145031901c40c095a03a0800f40e403040040002c540800b00d84e00c00d8141d203201d00560b562000303041103c0c28072104540010985120000c3d10b600c000100010001ca81c420214141c0100020410f14100c07000c481d6007100a400c1040001000e2074480700407800594004030030311681c03842d40d000c01d400030b004440413004070391040c00b02004201c3c00c05c403016480515202c464407a50841e654401803080300d1000030403040d404039100101102d07804440e868280c8445441ca00c0340c0e0b8406081000c0d01411806441c001c041c062012401880f03401101c8040700501d543c0080c070b40b480d4040c0802540310140207200650713118801400202e01340020b140400c1000300105400000e820340604110341907100603400641c00758200002814a030707074a5030102d801d0038490312070b03607460005803000d024000004d0740c85860080070800c03801e8400c44003405490966010011070795 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 580476933 1250 580475683 580475737
    0x8010e03040f05060702010c062906040503120d1d07030605060d050a0f06060f0e160305040201120e0c101805030c011202160203070602030714030a0c0f02210102 71
    0x108074028080740c002162800d103e6428408018580c551061404401c9802c040d1a60401c6451504441c03e01030640c003101c00417051043d0484030741030405c40c0d0309460985041c000942c1d03080e00390720b042491080800c0300b541224040c3d000e02c941030999901ca4504401e020205507da184a001c05c6645918100206900703080c009042001c1c2944980240203141190f2250400122a44d070111110341d00d0b0200130440c058580d0882d0028840581600d1280c24401c0781a900350003400d0001007010314000422000d030380d0101c0340b403000c14400480040c201014458035410a4100001d40e134001250044074051198402c00c0d001441c00d10140341c0d0407968940d8105501d480b40b4010090001d80c08080088640030150b004041c072030310742011080b0011155000c81d080201a9100201603000400c000c0c041c080c80f244000c6030304c007107000a145000c07003071f60b00900070420f4180c0180c00d00b08501550811910380c0c0c00c48040c500384206ca042c0d0111342141546011b50f00040f0004000102e856205203a58 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 580478183 1250 580476933 580476937
    0x210050f0412050d06090c0201020d0b090c0304020603071b11270711010216050604021503040f080f130e16030510050d05030d02160c1e0302011805180108010e03 71
    0x2a92142e018000305031004800c4650750802400d00300e81e2540ca0000141ca92654400c000261015400242c2c580f008070349104226002280c0380f90142a00400f0402035185107000c0307a03070196046481607120346840e01c0841d9501010089c140c20781d4440414541446101010560385410480d0382121081d018046001e25190000f49040c0c1c00d051400443d8400d402030000c100504400c0b4001800d0040460011610101e89101540d1710b402c00703000d010660038120703c009901c2e0a41c13800c03d40b0f5820103540781080f84100010241c40514041142c80000100c02d04a440d4000704c440040303880790b103030091049060300907502d281c603811060024582c0c0c24000c0c0541c0380308000390320581d0501850102070104207004c0d03060071185800300308000160984548040c000217844a54807000c8140c251402e41e0142107503801c99414040003001d18400549141143c5040c0c0b0340c28a404542070040b4908800c0d40c031007980059078040109445480d410000340711030b50480d079014009100010641c6c049644034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 580479433 1250 580478183 580478191
    0x3030501051f0c030f140d09030e01020d0f0e0a0504050405010c02010b041e0e0c09010602010b0307090b0303030a15080a052409061501180e10060906020c040e0c0d030210050f 77
    0x490004002e210109005040141c041035040c1490f03503500381c440c17a440c455684141850455a681c42300c40d84185648a03041d03803028042030006006003a0070350350140413011700007104803c05c030142565401503120800070302c00818014001f440307241005d1600601900e82102001c1c010342c640585011a07150a0041080c102c002403101c42c03580e0400b0200d00040d024031048400548034401710094681c58202800d4020020b41d400007030440803400405080112690202c01480d0420b61041410307540031080300c0d04003138107010005503500400030301c11501c149503001c01035502901c1d20748018094089124071107a841c010b01c0a803002c880c1d50f2103200c48001030300c145817144e00c13074000102e1159000c115801200814180401d0740000c13100030600c0280c0b6900308141d01c0e9080b10500809d10015022407000d4049410328000990500700002c2d80c400002e0001791086844c1d0401c11901c1d60144019900540042c042001503002801c1c080d42c2e031901500341d01000b51416002400303100f1005081070003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 580480683 1250 580479433 580479437
    0xc0a14031e0a1112040204020415080709080a021503070e03070b1210120807030516030905090f0403021c110604030314010b09031002072f030d231e03010303030501051f 74
    0x10300c0541340300c06059a60003002241c02c194200000704490211503141c1a03040301035501c00c009407a184c0c1c0018000d40150b0300111007540543c05103001a44c404010200d0f1101c04a02291a80e80e003590031506040e044145035018091400d003c03826000010040a0340443d030f00291455803103207404402209507501c51092a60004642540050364131002008150700901c3c0260503c0303404100c4841010302404100d001c04d40303005d4100403509040c40025845020123004002c03e15058500ac0c1d104e0344c10142d560084102d1042625116024145680740f03044c8150458041780340601d000740080c54001d0012880200070b900018403248100201c40d1982400b40240080c007031078440c101c010f5000310300200e03844800e10071070740c02e2154402140e4201d00204101c3c0c800b1800d5000c181400c007000a2105004c000b91130f03440003400c2c02100e507444a03d40350341d41180c2e91107800e0341e4020101c140a018402d1481070000001080c0340d4150003843c142c400c01c540802c030911420b900084644941c40903500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 580481933 1250 580480683 580480687
    0x5030702040b0d06060b1b030a0f0e03070308070b0a05060a030512160b1005100e1c05010603081209010605060301150810050d1b08150c0a14031e0a11 66
    0x1070a00780c1001d0920350020b040d01000c0b080c0782d540c41090356107a4101421101740420700780c10400800040003101d851000c00f07503103042c0e0b6210000f01480140981311003409000752800c02035850400002004540003114661075500c1e62400c4281d060090b9584401c00c0e00b440046407282c6400b0b03c400c130440790300c81c0007824210369804016040341c01c14000c2100a4040300c00990200e80c1c2207440034445d4410b52010000b07d42403604102c11000704041c610304004248854500c151595042c024100d1a0306cce00b00f0070004c40519020b400752040e900000c000c2d10010544a03a104c4405c80765501500c00305009020050300c40050042e40c0c0400d00c982d021b00d80113480b0900040d809010080d80281c452440d4000311500c0d040800c5240c0515a41115641415007100850041d416142009440003001908010914a52008012602410010380391a0019401045074000c165188000c61080e0b811500c071729010702e0114800203a03014010200c0c040c83c3c0003a00040141c400c1c112101e9890f00c2c100c1c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 580483183 1250 580481933 580481947
    0x60c05120f0a0b12030c01050c030c090d020409060e07061b1e020d0506012303010903090e090a1205040905100503070b25230a1203090201020c2d09040503 68
    0x108208101400001e516a60f44007202d00c56121030050400c105200401185d40380d4907903404c80c2c00c40b6401040c04001d41014024002c07500603c8003100c0401d01c084580607031002d01d500000f0020303d541d1000409040c070f041c003010f180440220f8070b40d040300d101e41c460203440403000e0040b5490080214000380315007881005120768003600b8002503106400503150780041c1791241e90f0741e89030080a82200c021484404c0c07100148600c082c0ba84a1350745020303002401039030144d0390082c100d400c15000300103019840400103103544400304011441c036908010a03013901c0c042c05074090402c1c2d01c00d002c0c2150441c18000000c6039004841600d104803540a0018003489180050460544d044540c128001d0909201031110749184803000e039000d00c0c0640c02c101d42d54100c01666268820781c0140452403038112909200c0441d01c010210750860005040101d010301841c40100c2c00c08803010001e41d40400d91403404480c3c4400c4501c206a03540d040d181000d00f0b0703a0981e04005070034000300d50061003940700300208 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 580484433 1250 580483183 580483201
    0xb190509030423040f0e0d05041d061f0306090c080402090c03101e050102010b030d0203040911090306041b120b011208040f030f060606050901120b12030d0207060c0512 74
    0x1003d9105899400d0303640421444000900f543c0c51a0307100c61402e62102c0140314610001e101410341e02040307003012071804d072404808450380000010f9507645190800c0000d406a200d001007031244c802c9045400c0d0040881780e6000e40144114003d80d08910314001025103001d0103040014012900200f18400594030027180b004a640300806100100c0410100001d074082442c0d2820740d007101e030303004000006003400002400c450640100c0c500c40d03881703892007804035238011040b1000d0f603840c00d41c0031402081c54a43c00c0e0403841111030303081d01441110200b0060006c108110102c01c201c1c07540500509940d074402c1c80420315215409045c01b0740301c000401c120000749100001f200d1050200c181007903658040518480356591041e90003a0b43e60198108002640c030580c07019000d2800c1950800c041000000c0440d524082d003500076a680d901c0d00130346941c412102c5407410840804881d0b07100b919200c40000303504172513011128142010b18a130703170850180c401c1c0c03501c020240742030100d80e0f6a0038600d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 580485683 1250 580484433 580484459
    0x3040506061537020705030d080c0d0c02010605062a0705030705010e19170708210a030b10110f03091518060a050301031e030e060702060d0203040b1905090304 70
    0x42c9070001d01203150920f4280c0c0c0b030038402d940040702035005040031a00e480141401d04c8084940718007041012402c0200004181040c1c0700ea01d10b5442d0002000c07a80c00d24140e00402c8184c203c03950012012401e0560034010f118485014a4032109a81c10340c40082205239071420503004031903258206883c24400c079446030068110006008003c3c1c103200e960100c603091800b500d46c00207140c0341e4140d00011842002000040001d1003d540149848807005940780d408028a90400024080005841075203503c80d4211600341d000040c00302c41e48004214001d01129201c03030046009000d440721403254101c0100c141d40d6600c1010b000c11080c01a41c001018560344020074481404484241e00580c584441000c1c20080281e501d5070b656035410340c1000c840708807400c4503400760302044920b0b02002036448810014604d03401c0d261551100300f1440000c1c1c40340111550401d00920100030801400007200780b40340103042100140745004481002601520011140204141c1c030400081000d1052819 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 580486933 1250 580485683 580485727
    0xb25080d0207030e090c04030b090c090105010809010f050a0c0e0301060f060c050a0503120a0501170c0933040b06040e19061e0302040b0109051e011b08030405060615 73
    0x180200c11604c4110004203400815141c0480b4600046014000c11640c10001a0001c0c008801096011010000110b61007814003550b81048204400324501d642c094201a03030340b2880f440300f803003145041c8543c84024281c4d90fa110000402d0007680b00090309041c030030603090717950b04401c6126a90902c84207842000c136111046429101e000b002001046041c0060440d940343c1d900c86030ba03582001a030030015600180c02c80d00c4100035483c4146181305000070344160395002a50044525138503540c00c503024540100940c2081d4041d95480c05403188501120424268120340401c0300301404402d0040034060b90195035140c90000740070400c1300382c200c00c0390080040803c0c408285607460b004590116683c0d6004034105d801d410b80140210b191500031800000b00a182c807014140c0b41030b002413048108030390070154031092a600c035405648a035054000c0440404000036060110b450010784130ba004070b900b0b42d1300740a44130100e40719251440400d000009e40002490030a03482101c22990011110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 580488183 1250 580486933 580486937
    0x207050f19051009020d02370b0d0c2006010f08070b030a0f0216060209040501140d030503060a05030613030f020d140901020c1c0b0109020a1b030c0b010b25080d020703 74
    0x6d41c41c880181d40d0084138005050020f02805010709010000945880b041c07002400714a440890610400e281d00381541c4060039605008611601801000e41c3c180718880000e070510280045400a2050000f070064101c40148040b0200a5607590b0313000d0322614170303014511841c00c0400215000c019607030092080d0440c0640c00502c0d2030300c400c11199031454128400c440f100d03004514250f0390701c0d140c4505801003a07105149031001100c0700000e04081c0503804000c042c440048041452911003071000c0020b01307809001c4a44134100030b021405100b40c007003400c45c009048507408140c4184082a0120f0b01c5140780c03112030403c548504100010b81042e17080c60304610400c4009900f940e81c04508480c5681040c3c6405054a1117040c0180060380c160080c0820314010804c0b0702c20580e03c40110303c01c0e0740c04d1b100440030118081c581100d103515800d002405100b0b500d03002151b0f01d00010020086004035011100b92600032544030010b1440e0120040d118201c148007560900720190010015a4424 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 580489433 1250 580488183 580488199
    0x30b0c0c010f0b031009030e010302160c0909051605010203042d180606090506090904050f060702150115080f07030204080f10060506040803030604020703050d0207050f1905100902 79
    0xe0a20142140c1c2c9124041c002c860721031454000c0c5080c03d0000384440c1c0382d50902800f0030748041d03d010707100d98182000740b4100742d40001c0907520321041c0c800c0c07203823074551000740300f040680da6640c040c015043e810004e407250700520401110100e11511140129141a0042d40c109860b1560607400012105070160070803503c0091454640c12090344100a801c40782d400d407179030902d410306500031074919402410500900000500c4640e0b10700040c2c1e80e1400d011590031000303aa462811030305080004a405003c6c2c401c3c4418020f80b580c01290b2003120b15140f44082d0126a603503802119800c07640011030003c1025000450600451658060b80c0b00c00c01e4100035240c5507132400c0c150b140c013040e1000e0100c0c5410003c1d83d01c148124a0043c0002098203c3e00103003480d0400f0039081c0c4921001e00218881c07540051808201070291050b5001704440d030404545541d020f04200b5150007a4000d04000c41c003840319031100d8068400c44800003036030801c00800316101120907400c01004402801d9a0040074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 580490683 1250 580489433 580489447
    0xc160b030910090c1e03051b010c150e07030803011d060d0b090f1f05010504020f0a08060d0204020c010b041b0c0623090f0d030c0c030e0d0206040b04050306090313030b0c 75
    0x20341860001e403801d1801201c1034074a0740c14104c1c01c014050201c110811110302358400260381c040c648a00b215000b82c480c05100c4070301d0400c8001006400a401c3d841d0113042800402d01c60f100001c0c5041383d18107590b816460501c521190903001089500c0303580200300c514001c01007868034034803c1e84210321004842d0f1041602508603d80499100c0d0a0300ba04c4645c40008001821800307060f005010544040d41030500c1100903412900400480c0c508000c5080d0003d0510f6980007407184c010340d0041d2086690b540e102101c20301a00c0780820742070142c0d0074030056194940003840c0d4000002d00725a6551100a01da07507031072000c1c120906900d401c500710195480009100615824004d980c41001000f006200e2034009007404035070340e90360302030503e4050755081c2140c0010310281c11036407600c0c0455001040d03000064000c0207922010f500840f010401268000c82d5000810a070340b0210700322002c9980b80c07000e5070b030340f4410f0070781203042e210105004000082102410580200c0c2440c241820046 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 580491933 1250 580490683 580490699
    0x8070c1103030c030c1c0c1b050d151b141e0a090620031c1e02090307090b0a060c1e11150310060e03030903030c160b030910090c 57
    0x11111111001381c20000303000d01a91340801440c103045140c2185040c41200c0c4100c06000a1029a005000d41c03a081303119980b80d041c002314460207004002c000d5012100d10b401c01140c18130140748034502080ca07107008001c642280269200c0100d0441d0744111b0440d091a044940617041890420500246070b01c1c140c4402c0084000380c448400c3c00d40d654841d4a142c0140100740702e01c0310300d4207040d00364010200a483e00e008012a000c1400d58030300610303460f040b40380f190010019980c140b40e0200c002c0562003101079194000b000074560490480e840316840b42112011905440c00143e8007081c0b40004010446c0182d0398041c512780100c00c451884494481301403d1000741000c215410b200308400e0a0031440c0284101c941800c400804500707620308084d21000015160160005018608805030121364041007116100784e0087d00780c9444840c0f80112a940d001d1034004110f28606601011038040740c07540983e44114078810041c0380201c151380c01c010040c04c1202c010769220000c094049200c1d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 580493183 1250 580491933 580491937
    0xe031501031a071d011808030307030c0e040b0112231906090207080304061d030a090801060603020a1d0d020409030f080f011409130605010b07031403060108070c110303 74
    0x141c05440c901490203010b0010b018619001410401800200381c42c58483c2e41079800810005403080c00c200081c65030228005d85208020740c407407881d07880004100b08003540d0640040b071503244545c4460001c0f0f50440708103c03e0300c0d5000090b40c0040c2c8d0480c8116148403a6402440e141d042c10b400134031107944101d0314403d01c45800c40e0103261001c00f5501686140485110b9040241090407086080c0b104a035500e201610000d48054051912400d50717074801b003640b019821201c40b03140100c990f580d22015000d0444141ca00c2a003129510f4100c0c0003411038001d00884011200d183d0300e400404407080042e21003940030703405d001c0d0441040345404006854911503420303141d0084e1980c90600d0b402c40002025940010038100d2542070798401041941d0401e101302c001d80d002201c406a01d036541d410803440000006802502c81c5042100014654866000805c0c4880c069a1202d00100d80e0880400043c801918540d002800c07920020341e216210380490342c01148144000320310b0f5101100020702d07603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 580494433 1250 580493183 580493189
    0x703081b13030b0601020c06070602071103190605060a050a0e07050c1207110d02030d031107080301030303050f0a050106091a0c0a0308010f0905041a070c0515041419030e031501 78
    0xd15103402082c0103000300e0485403580b041d4244014111000280041415406039543c001c0c5100d802183d800c08002e040481810b501d40054111480c2002c005c81c2d054070408416015601245803c000c110182010040700c020740781e002e072048120614120503ca4805d000038080800c0003000e100790428a17030103000d5008845119800b072031315840103003031441e000c0b00881c200501c110030003203d010040c1c41c00304680d80400e10f203003030004280410150055280c07103103100043c174119001002008041e05980941d021304251524030403280d81b802d2917242220028081e4402140450604100f001035624203400b0744401c6114160400f6038400e011403800341840e004a011440001c0140b081180100d21030004052041d0700740514107080d2540c007422140d048401161050250000c3c8280703000e0800c100c1030b9944081102d00320203c10040c1405c00f81e09441c200c900c202d03580001802480c2c000303103120300301c0909100d858194032156401e0750301c000d0b404003560705806030707001004a5a40e90740e511402 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 580495683 1250 580494433 580494457
    0xf1e030108011d0f150703060f0e040311122b1b1404030312090f0c060f020d260702281703091005090a0b071205011a0703081b 56
    0x6003074400f03000c521115211034a030900700c1d44440c0703c20b08180f00c0040c1c101d030030040d25440c605c61510765000c2207014201c81c1c1c01140040c0c410007000140111079175a882d10550213a60303200d1404010740034841d215050082e02d0b811b9400113000444c06088200300c48a940c0b24a010002c4e0b00c0c03034844060b41e00355450318401020344021203007010b01050304a61608030909445000d5403515095503406083e401c11110b141c031503c0d6803018510b041040c401c001045c1c8a030000c405040240e0303110001424401c503418544014016070000e8128640100070400c83d81e2405683c185046503070001451100c04010322000c210701c550100346160b40741405401c540c1e40c4503000030030444070003420188045040301514540004040081101130400403d69141d0080b140d48042000d0b1684c08c461490407205010161040c66550241b018032500f03c604070743c5800c600d0406202da40e030f80ea40f1070540ba00407500e002e9680d4004001340e00010b4401e9811950003244203400301c5560074003000c0d00c06550404606148 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 580496933 1250 580495683 580495691
    0x903080c0312070f1403010f0605091c0c0305010f1404080913180c050904032003041d011d0103051207060905150117010203070207170f060403052502060f1e03010801 73
    0x40e84d98841102202c0d28210040a80b545d40740690701080e00c00d143c4144010800d01203101049507071034500c00021801ea2030401080e4a080e818100c5400d074461000311429803914491112628441c01014007a503001c65040103141d07155240c02c86280d10007000245e200f80307400501e1440c00d08501c248079141c0000a14103240e40329602c0d045078524241d0300000d209410110400001a900c10b80a244078041510004101c1102e030b41110311b103000d02d80005227030a540c504001000c1d40001c108504a84c1c00e4600e8526075200c842428008490a0001410907040408008094000f030001403c40030f00c40c050002d008807036529014103200700f001e080100c02790000010000c1c03114000e401501c0010b540700840c514201110042c0d40c0c0d8490f07200301096644410103482d401c020500409a0352801001901c961385803610740140355a01c0051840058061400303c80300a03102c05040110a5902400403442d000e00c9130000c41094114180e2500884000b880803c40f2000c0d60340503600074140c05002003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 580498183 1250 580496933 580496957
    0x140103060e1b1f05070819121b0509010c061a10090609060f0306080f2d0a06020c16090c020c1e190902070f050613030903080c031207 59
    0x5820020400280a808045150142e806a440f551580c900d0301c44010b2440b4000c160321020b441e64010504090f100c0100454841c01494071007a1035401440c580da40c600d010325400300e0410444008444017240114482c913440c41450240c0018070b1030040c141840c0d0700500c00b50f40c03200c3c2a2148041c2c41c1c00541c80740d04802a083c10300c400d40700341d0751800c3d0030640400c1b07050800041070382a440c42428204165200041d0304140207034490800b0381600c406441e21025102040da03504c43e904405640d40c0121084001c44680c041e454900c0b11b4402d22028201e1001c850f2140e402a411176408400a40240401c1612504e860650380f0010002c0341d6010403812031440002c1d08202c040052280620908410a0345031080144411a0114204d80410f0481c4071402400300c80001504100502440025007c05010301e0a02003001c061144048908907580d0503241000c0642400d002404030710810b0b414000140d40c0d10291043c4d205c0d0404882c2083d441486e82c0c0710540d802e48021001c120171000003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 580499433 1250 580498183 580498211
    0x20109020a090b06030f0a11031f090e0d0302030901020d050103030f090509130609031224150507032723040b01021b0312031609270c020114010306 65
    0x10004080c4a08100f001c1075070340d00030509521000344400340440b0500000b8880100c10350007220101600710039581c0ba450414044041c810000d01c8404c2d8070184003100080d912418001c42845c0d0030000058400c8122084003507002c1e400240c98500d5554090160744042880e51003a075000390700a603107082c8142e1490700050070f80c22481e000180580c1d04001000583c4803040d60152080d9800305000036081c5182c1400c0340c1c01c10040380c1c0c0d0340807a8100407a55461181d80c4040c00240c4920111b04c19500c0c0d51089241c41290304001c107030022990502107400420b000c0c6148041a26450010000c002105400d20502c0310140c1c102908810400d200c4440c3e10320b40c503e400c1d004820654040009c6101d40d00043c0d0b80c0c00000d48081c01d000c44000c002000c41c0c1b000d00408600c40c464100e030584a0038100c1140100142902e85c100c0061707910000003482200d03e200c060f40c40c00c4020504e0512241e011f0440001e00260f881a00c19507480c1d02c03010301a135018106039802035005d0040040c620b500f403500c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 580500683 1250 580499433 580499449
    0x703170a090b0c0a0f080705010903020c030f07080c0d0807120306061101020c060a1d0a141603080a03090809032a061213230c03010c08040b042004090302010902 71
    0xb0324078406002c940509600090750152640d040380301d500c16030030705107041c1d2914441c3d00300041855003042412010180c0008142e003070710400b101900d0580016020096882280c1d114441c49548500f180085900304400b606c1495400b9041c1035203481c0c10354071484403c40240c45004006079403001e0800c85140d0081200e0b036071200c10002589401c2c000c088030356441c0c6003c2d00052044c0e5644003504101e850303220703030010300c08845802d0f01c0000e03400c8e007000b5804402c60b1010220324000c680c108100b504c0341c0309070b07042580c1c0c2c8900c0b030504003011000110018602000704584041e0304002d50041a0350030412352100f1040006c0c82044c4007504d9000249600300d480d501c0c1d00520342480b49110303261080e2605c540c046e91680c14645c100c82542000403100c5524040000580141605100b0052000c0b0741004e82c80c8050380217100648410300101c6103114102c40140c05c50001d03001050006100d52900d4655510917094611406902d0300020f04803580520101c0c0540e544242d10000c40c100009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 580501933 1250 580500683 580500689
    0x1b0f020709060e0a05100f0b09130524010917101d0c0411070807030801090b01050403080909040203011e0204061803020a0506070314040b0705010e0d0905040902030703170a09 77
    0x1800a145041c08818003c2e102500c43c0400c181c903080000c0300d07024000080700040c42d02c19010007c5e9555030a504c6242d80c081e002140c0501e014080d8441c40c4029402014080c911400d9030750804038048545040b0801c2404000d410041303001c2c1d00041100c07184105c941c0c2501c006000c0d0072042c0110256004030f03944980b000241d1003a080342c1407498800440c0360240740d0340c00e40d004a02101420f45662080c031a91f003000303010700408504030050581c03003207640713060307590591080000140300801076030103002c2c61000508281041040a02c0381c00d0440b03100790498405000400d01e500c01442c0900b021001e81c0b04190040d42c08101080100d500103580186805250019050f60381035030003080041101e030107440d010b030400049a03c2094810400c8800751400c01c40180d4170386440380300c0282c080d072004106568960804800000c00400031071400b01c4c5148507103d10315210b1910302417101420400c50166418000c0312800001308055003601c0c40004040c0b20f46a0756280d00c1c90000d029071130590 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 580503183 1250 580501933 580501949
    0x180803240925030b0306070e0a080d020d110303100302040b13050702030c0d030504080405190803040609060306050418060b0607050a080703031409031c022203060507110601030212011b0f0207 84
    0xe0450360f6075840201b221a0040c03d80d180541c8800c0d1024085070f2007000341c0d8440e040038030403001c10310509039000c40c8058005c4100c0d030301c0300b0002d503004842940e01d0200783e41c1f68040480b4900101b0061409601c4501d421101801a026111082c00c030501103403001c8825901680000840b201310340c1c42404810398030104c07410308100d82d007041d84540245000b0f9024240c09921910324041850904440d0b51000300040320449549a484110081c55281c0790b10130300780840d0401c000800c8514140c01110000c1d2040000c400d500021500d400c800f800c0c0f1422021303001072042181c0004203d06000c21154140940c4589503035004038580141110403044101c0c1c40e41c00c1c02c8043c80154000030041b154076900c000912001001542c0080c0001d1045c5917214900c044400001200000313107502110881c1d003e007034102310307907070321000d0940d48182c0000d240d03800c0e50400d00040c80146480c50503114003529070b000009a4510b8011070307a100c4040700c450032020490b81d10754800c101350b04002242c00b4094035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 580504433 1250 580503183 580503191
    0x8070b0114150906030709080703050c0108010e07020a060c092102090609010612020306150a1d03010c120e03160507030b01060c0f021c0203060c04080118080324092503 74
    0x103484a00d514000d02011500c00c21001010400c6c95208000b00d6002d06902c1098a491603902c0c6007603903507002c8a800f0180414003050000136501c40752030120b407003000f1a0b0046c080c00c83c840c0d0b807000b000341403e50348841840620340d004603984212a80c110750351110003042d5440070545004201c04008014041889503a031300005015003540806038205108420602580701e860f038030b00141c03400d4507850080901c4440404d0f500021648102c50400c622907201170310300709810410506003610680d0485070301041404c1003600c075050450340503641d50083c10003501e04103000d503d0125000b11010b1402d5a00341c1c4508000e00038080c1e8143d10500402482c1013242c01c420b800e5071945400c040e190340107440f0f000b507150f0080350605154a11040c455004082d25418680100390300c0d41c98000d800b0340000c070340ca043c40412140550314284485240c20110060465460b0038162240000507040c4190f4548100c0d03003401c886c0c0781d44031018008d4001440003407441c000400b98050940e11320150000b00740c20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 580505683 1250 580504433 580504459
    0x40302030703080907030206071112070b451002070509040807060b130f0e030702030303040b060102101407122c010e030c06061504030308070507030c08070b0114 71
    0x30441d1902030b8907007007580069076483c1c069428140141c1c0f0194011000080c04404c0241c8a8250060564202c0d440c0c612509040000da690319070600681d032041c201041001c110755028407c001c50090f5503c00b01142115100d200c04582d041a160349104500c0180b03024120315102159464240e480c3c4010710700c140c542400180e4032079004e070003d0300c08200000c0020a1044135004070010f942c0142000c001300080c2c6150100802e90448003002c010b00e030460b55040203001000301c59900d41c00400640c2161916244e12507840c9001d40014150301c00d08101c903010005500036030300050340300101c17a959480c16050162130016010104122145890311158001c0100611140d6180e00400a4881c092500388201c0c0100012440c4000b03611001c101100304c1040021151710030a41a64880504500745030200501e01850100034049030101e400900260703c10800350040e41d000e407400b180d0b444110348442c038556210803001c0d00c01c00d0004005201d59008025806c58525041d54185c07001c2c44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 580506933 1250 580505683 580505687
    0xc010f0905480a09021201051309170d1508010905100e1c230d0b010c02060d150509070206090c1f0c02040213240c0b130f06021c060e0403 61
    0x7101034841080724001214500d80c58407600d01c3c100203000c5080c2d007150b0703484c1c50300c20010084c4824820240710b40c2a0b0b40c0c00500c4136500780600b11080764080c1301e8019203070034262300d03914a800c0b0003e0765840c01d81e20082e00c2034442c01c1031040c00080540f20000110581c20f801c0440c01d06441b10b0102c1026410034101d03403008680000e528407111240d0b0158a204440904122003044501e40783c880941100e40068014030841d02c02085904c041c100200210301900d001510110189400a94071190503c02d882c0461803d41192805040000800412589420002c2e212803c19908000143d20000400580110420485103a440c0458002c245040000141d034140300018040c1c10402001041d03035011916160144d508c0320840c0c0070484095521009034480c40307481018102c014030300a070500108a4000d9215400302c2e07401100c045034541d10400e90000b001c080d62030444060001d4071640020807018405001000300c4502552203c0c0745e41d54196080e5000c980203284014129014400000c0d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 580508183 1250 580506933 580507033
    0x6050915041a090a2f04030f03210504030809060103080a050c1617120f0703301e060f1412060103060b1f0909020c010f0905 55
    0x104200c80114032048081801c402c1501c80c0d6036601d4024040606100074035141da00802d010640d280d826410504810991380b001100d0785100c1092100f007000180003050141014581a500a0420b020304d10040d05404452038100d002010010b507640080c80308055200100541080e513100c010013942d419a1214523175446141e4140040c4076000550040e010000d1012041000881e0600c89a09a49a06c9078890f0168a5550700c1c8a0144901101e0305109074030603641c51440180d032803030401036640c0e07003610400c0c801c1030b1400e00b0210100440d42c2d2905150098900310401917000b08120202102e0f14203a6620042207010890406400380b001c015084031420444036881c4005070501403030008034840745c0c0800114080303401220700100501c48a42c100d040071010688040c5030b0400380c81480c04240e071480040c40000340c2c0b10b0b8010065040c158001e4505c00c1c546400014074140a801240b04a07800341c50308690300d4221140959a982d0071058405000140490900e414082000342031160 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 580509433 1250 580508183 580508221
    0x106031a040e072106140c0711041116061d06040204110403050604050705130204051f110f06041707121b0605250e030a02130209061c060509 62
    0x1655070707031425070b1850380c10001c401c000d01c1e1003120018180007107a001482c401d03440006030340581c14160004c40740d6500d45440d503c03c160001c00c16043c00c078640c1c0c0307090061003161817056019881e51510000303950030a00030480d0700300c101003007146100d880c42d0040075554500c1a20258485444840301c0d00000441ca05611580c102c4000459608800807a24a03005917080941144150340800041140014820081d141d00311829140d4140f408501e1080c0e1003603001e504e0f0800c91492000c10310170300c00524030b4008489410000035003102c484c40c0c00c2c640741b0015005a6154042000d100500c000d01008001d42d40c00380d0006894140e40c0c1d00c59405140f0740001c1141040204520b04014a000b5582e4681aa40c0705006201c0d50074010025110b10100528020000106014010102d8083e80103103828810140241100c49030740d03020816010800860084000d030200061105070b5116030003410301080b44ca203403007180c000780100c050840b01c071390b00214012078851050082200040170b180c801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 580510683 1250 580509433 580509439
    0x10c02061b030703050c01050f0601120e012d050f1e0a0e06040303050f0f101503091704031b0503030d0c020a020d0507051005030f06060906070b040f0b0106031a 71
    0x5200070456010040840168140805000c0442d4440070554010020805150420000d00003a00d4000801c80d00030415507205004c21072410a25a80640d103800c2503a2034041c0500015014030340340041865003560b203609a002d0b010004501c5100a071511401ea080354801c9080784c018544560f80c202d84070050900e16060805000005114600d203400000c1c074002690299480c030f040601c2c01074054070082d078120452403007240000e940b4a1450401510403100c210802000c9450b0460303040904502c0f13410082019118041c803004619030f5101b41400044c2000c15036600c1e07145003480d04582106240d04d115441c901e9404021030766000040e1009406003150004408a200300e003030307181c1184080025007244a0700c2d83d903030612001060751b004039001910340501c0300c0c00401c0122034038407040380c40c00b007406607a0021445504109000e04202c24003e03080903c6c008a50716522034035101254211180f0860100003000c014401d160342d401810309040a10140820360003400005902820040c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 580511933 1250 580510683 580510687
    0x12060902130e1009020c1018020306041101020c0a0312091d040b0601030902040c080412030e0735030c011805061819080306030705030705090403030509120a02010c09060806010c0206 80
    0x1505030070f810010801051074000841d50340c0c02c142e40741d41d15030740c2c3d504400c1042860032071810b8200d01c842000700b0404c1d80c01006001903540302d64401403c00080001d1504500c43c42c2104001074413035001c69000f541c014000d01e241e80f95014070092808460350020004250408101c503071049801c05a203070000d62140969045079202c1c0012001401c107258040d500a050103004104590020038443c003881c0210480c01d0060503030390381501558841030002500b9800004d00704407507007540010f481c017030b0756085980320034119441d403142010352800520075064100060300c20011009108414103520034014a13a82c0c080503858041e250711001b490801c2c6400d0004231840025410f1040010310b234001c1c4003041d0660a60301b000740340b54104680c034500a00ca9a43d0229032468001400012940010910b80090351582c0e012405404054a004400d10401c041400b0004050000d0b21a01e03c0b55400010034000322007000b8401102d960040d0709200081c001d0201a0f68090403903441c040c0c05035070483e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 580513183 1250 580511933 580511941
    0xd030209030c0406121119030807060f0212013308062206030204060e1314031905120f061c080702030d03050f010b03090d0c020d021012060902130e 65
    0x19003064801142c0341d60040c6444000304480d107111450001007400f4840000b00c00343c5413000e04c120041071191040308194042070810001c0d0f804001440901e20841d00418038868407060700f0241e82190103031190342c0c04a00c0040c040902e1450b821101e01c0e07018009a100c1e1240b0030382d01151000e20b103008004100d0040f0019020361911030700009419114950103440514242c0e01c80002d0000b40002c900c0f1354180400051140b950300407040c0a1032012106c400240280c1c1d903001040000b0b80c10194090009001613a010700319401d649a010542d500c941c2d550301032000b003621900c84010b1002070308801c10424001c1e141c903107106403c9403414030721042c4000740c400c3c184424140074101c0001e40c980b11f10510746005540c0750308518050800000c51154907600c1e44034020190000b103492200070b502c11403040e41030522030002e50361042e00181681207801900c0e00483d007142c003800b00340000f007094841042e608841e10310036180206542c120850601e400c1c2c203022504000e10380300343c0d100050300e90b000c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 580514433 1250 580513183 580513189
    0x80d080726091c08060f0a032d0b0108010b0f0108040c05060a05040803130503010c08130206092b0302070602010903020a02090403050c160302040b100e1915090e090d020d030209 78
    0x990f01c2c1c0b0036090078501c0c5904a512008160039400c48a41c0e0113150382580c07800076424032004400540e984001c0b07404400920f0322414001700080c0002c040070340c2c810200940400c1c580c9908034064041840081400703900c850500c40045941d01903070f070400c08603408000103d440e16261006803181243d2980e55490400c00444d800c0c05035401960040c000041e5201c082e01300a601c00040b10010b400138006600481030070340785100101c502c5200c00301a0000d80e0014034151000706500c1e00c0041c0b40c5116000350200100c80d6400d151180140c3c98600036900060607010090b6600030000c520013401400c4103507800a445c2c40103858001d000c0c00030203001c6001c050040050714070303000710f5000721902c4d0b1244031b81070864820300d0310090380998903084c010041400c00504115192400e600c3e1421050003210900045120b071041c05401d00503410000700d00f80d0740041c507001499682380d491100300d60034201b00320325840000c4c0400070190311901e0310034401c03500415040d60070080c908005844900070404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 580515683 1250 580514433 580514443
    0x210203030304110619110706030207030f08040804090204090203060405010b0a0f0e1309081e04050109052e120f021e1303120306031b0812090301090804080d08072609 73
    0x441d203000240900301034400340c0c8641114a102011011507191f036036114001d50032031050f520050006246200b074144d01c50f0056403200d410900c01c2803024609652420200120b0300180c000c00400380d000010311215152900426015000d0210407a00d00011940040c3c030041e0100c0d0b5000c20301c0702406800f040b030b56401810118100303d0380c1040c003500a080c0341c42d010315440345007441c890b44034000d0124081403d00064405031241a110382d0342c4242440200b080e111840c140aa54400307000f400c01e00c1c1c50303034a0804e01d0505801911008030402000c1d41c4d5806490342c43c2c08c802103451040c095841802c44a041c0b04233034200750b82c00c0f1641c1d8100070410300c00c2420340d5040034000c050300ba800100826850303071080084034010001d0340c001c0e55864014800c0314880c3d1241c290242c1c8188104248804008000c103100500240002001c410b1640c40000c1e0b034029601c900c410b6005412a400a02e400920540c1e0181161a0060f41d072200000070b0a404440310041c41014641c5100181c2c5505007002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 580516933 1250 580515683 580515697
    0xb150405190f0e010510080708040b180115060e0114070f0c0308030c070c05010f02060a0507090503010f060501020c19120303060306052403070b032e0e012102030303041106 76
    0x51081042c0c0c1c84080300724261000384282030160400e080341040141c89054940d0196295603240181034580d0f44418903201c03070103481206550301482b45241184400d22642c0241d88ca1a25180d210619000018040d4880b03000c50b141030140508441050b589100111a2100c2d030020003080c00c2c1125081c0344040c3c900907080100003401c0001800040c03108800a0020745200d00707032002c09a6140c400444891504007200009640020081845240c15403c181da00040f28a40424116079901c002425641441c0800a11955800c4280700a50741031207080c0d06036405480f941c006900511420203004494030800c021a44005511420140710760852001150000e0041c480703804c0c040134520f00031901d41c60b0700c8502c0d0f041d20f155000a04001c00c10302c04688400034014150303919801050310f145015136001490940c003005444c9a40f18840c3d0132400703440174002000140d8140051212030342084090300302c8200c540d418a000580d0000b04580d4131503030090600040c0d02d88000400c0150080b02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 580518183 1250 580516933 580516949
    0x510050a0621020408030714030c0114091006060c1101020a08120f01050a150804050111070822030804031b0f12061406030601120f060f0509010b15040519 68
    0x103240029015440445944820001d80000d540290748a181504a108920403c1030f02e41042c8101c0f0040341c1e20701e0400303400103410010780b4030b0720f007007000d5190840d00c000380d40341d40031000d0b08184101a5002c00001c0103020b580c42003000007504100780a042c1d40310f2044001c01510044201c50050b0b4400d000c500c04460b8404149600c4060f1505142c101100488101c0655020310000180518141c1c901c5001c54140d50700c0681101403449045801003030051041c4c506640f120140e85104102d04001d241040c000d02c20940c58030300d149803030000c0c01c5c40301d039000610000e00e640c280041084081220200c070340c840000034084150040603d08148150721110b0303200c46404d0001001c0390034030a0008100d1241d14100702c004000903c100c5c5140050f915540c05900c4200107000da000784044c542c0d9410300804e8582000308913507883c0001d8604c20448000510f49030400c0c4151500240120360b80c0a80840300d4026101c00e0000300c01440c0100d2140911568001601d070111f01409132003200030708414 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 580519433 1250 580518183 580518199
    0xc0a030912090501110d05160c03150b0a0909080412061b0e040e061512030705031305010e03060f0a051f0b071a040f0b1e04050a0312060b0409051005 66
    0x1901d40500301c0c60091044502144005603001504900400c0c2056445d11684446007020340e092407020840b20504800c95035204c0000e030200c04140140e0000d80024a00d000204042e0b2a8501b8401c2250083c2c2c400c074400780c2082d11801c00581c41c102aa001c0c4d500303075145401c04613241d04001004d4a03641200c035030b880c007a03500006202980441800050041507a09100d40716461004030b568801c00c1320800e0300d4503454003600200e0300c2c00c0ca100195004103001103030b04124070f03901c03440c0c216401424110882030b0211400c0025513003203066681090f8084000c0c00303442c50480145c43c0800b10041184003c5590b0340c00051500301001c442181d0414a804e1140043e500c03402c0211030355210000c1a81e48207110189810b006110340308051180da8030844c0c4030341542e203903034503406c2c0041c010306040301d940e0003581c03200b130701184245040e84a94021402880d1001d0070b418050451f0520210301c2001074100401485030012102c1190b04454205400240d203035a106044017100c000c503000140d00c41c4403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 580520683 1250 580519433 580519463
    0x4141203010902030a0b1807180b19020313170105130506040605060103240e01050402090a09020d0b1f1e02030a1d12030a030509010204031709221d0f060c0a0309 71
    0x66040c80382c8c07207003005441d0480d01c0e9140d1007540c8402c6100b849000c2403204100441d190903111240607403644882d034012242420549a0076008540c1030b90080c136030031f040700401c0640d0408240503a9401c00b85d1161540010442da84411f611051300400c058031864507800410041e0340300741c2c000d0302101510301d5400d01c418079806020401008500c110325842208100108840c0341620031640c440c40e00401c40c00c038142c41e00400002a40042c401e26600d030341e1395400c41c80e0685440109140030380d81260f054060303840744c65000e0000c0e016140c182c1c072142100143c1e80f0445800008a84405030706082680414071b4051030714a54400c0c1e11001c0c1e0304a51150f201c2000138800202400030750141e5241403200b80e86040303c0c24200d01552002400007000150700f070300a0300b0141c00415013030201520038080402c401213903410708074001c005202d00d5170ba42c07e01c0f01a48041701c8042c1034609043c00140540c4041c06c9602552200d01918500b001040002e0700b0740e80724081d5000e03030300da03541c05050704080c0380d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 580521933 1250 580520683 580520719
    0xc0e07020307110306010b161a070f081006140f0403080708090a0e04021f051b0606100801050306010b0307020f060718060507120503101a0304141203010902030a0b 72
    0x24100480d00022000143c1c2514034010540c1e43c181c800000c2c02c0c0d4100318280c400c41500320007000b4159a48115481e1451005030301c20011481041036480f201e000648162004050210040900f40051600300c42480030650142603442c116034203410090300c0d24549803280c012480b80c0d6100920500d80010502e00b0007640d01d015021000c001c4039000c94095446120b0365101c2c0c01190000c1d030144016032581d08d00310b14200c1e07004c0c80d0f216501d0224286050303c030311500d032850780d0121011564481003c001c9030745010052040c131140d0515001d582945820082a502c0c40c060107070003501c0c0404070014200314800c0000346501603c1c42e013103440c0ba0624040150415040482c049100d0112000100d242400341c01111907099000102518049954204884a400140c04035100d40045000020f05004504064000c00300641e44980d49041c680b80025501c9054200701c002e6030481c0081d0f01e4074520b220f0950b030459403195000740e83c0ea62588040b40007000640c0c486030340f0201400b824180c200d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 580523183 1250 580521933 580521937
    0x80102070f06050c0406080705030709080607120f02070f0f020102030f030c040e0c09030a1b120c0504050919030806130e010f1a100c1412030901060608160305040c0e070203 76
    0x34000c25041200d80c84030584d4804a2145000d2003020401030360201700c00e18030420003194400502d141185038240c5850606080100698411f000160400c4c1012070300e106d184104050302c200e01d0f0003140f4204159858101c81c009a00001c0d01041510050601f964000d00448403007802104030943d5031720301000180c0c03054006004c1c19005e40d0204000803541e50030242280d500581c014010710310300a890340d50140310980c084251303909030b403036580000740400047c0c89100007501c180e1070b020504e4100001d000444070000c0c4800d1590b4860f0304001a0204072900d5852500c3c2c052506800c1581e841c0c000c81c212220441007480d220f0315004a00319500010740c440c8000c0c200580041c0502503001014080d509059000b0980c0050340d99540c41c0d49901400c21a08102c0c0b02e050410402400d070055941812038a44080301201c00000801c00350840c00e100e40d101412403800c003d0010708009003404500750002c0055000e1696600c00f240c20700c10b0742174440c1e00400c081c0d030011049151020009442e9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 580524433 1250 580523183 580523213
    0x60305030a090e0c030406051305010c020c01031802010801061209080a0c05100504152301090c0824100203190201020414040908070204051e040503120f090d05090a08010207 76
    0x50241802046404162444900800c50703070513400d0841c0c58503180c0500420003e48501c0d00e100384400700d440002c0082c010218070701d0080c0c02410380c0382c00440c00581903038800f041c40310590505d992601c0050fa0000d02840c1550300d1860b11003404054511403200030312089402410002c4041140a42030390f0102c061082c6602c07840c1950140601000c1040c01e450b02036400424070391010203401032170b1205074050307074102c2c0448610b491707450340071644800300315002c0e01706000480c1c0781d4440e01072071034122030100e0b0003003d6125040c2510260b0580070b203036400c000300c00c0c0b80708020118250060b144200155040c1510025040030703a000422000381c001c1d4400c0c401d88a0790240c404814400303161a200700d07254036070004801071070a0304550802005101c01005030720003030000c444160681e40da013003010b4440c6101c4d00007947d54a050039030f8103c051b0700060102a003807100008000400702d011a0f6960700303501d51300b0107944521403140092021416900866500c0d8070100b0340c1e10603c110702182c0307400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 580525683 1250 580524433 580524437
    0x201021e0a1101020604110f0a050913060b010503041104050621071a07030203040b0904110307020d0216060f0e01050d0c052a07030b1905070201020c070e011224060305030a 76
    0x142c1401c001c010390710b0f4a800c4a004d03108101c3e41017030610700e041040d01e07039100f40c800034120700ca001d49500005010781401d8030540900308552104004105140c4584017042d24242081070451402e03503a110700b010301c2101154083d9496102040484c1c9441803078000d464100c01000c544a0009a0078544e5000d407445488a1516908100002c0d407660908845403503400d580603625013414441c4068060340803514907034000e5a5542c05480c0e081c0e415002d14056041c80e8041e0075007009480000340f602508060b5034101900401c01000306503040007800c4410010303810010745480e0a0700c0103845502a107500900450706280f581c0600715401801401c0c00044981031054003070300040141007611985004043e2a48500d10038400300700c40080c00c940c40105007400000130842e00c0f044000380d034003d4075480d01507134022a031002120740521070390020b40521000c4810640c90b058240ca541c00c0070440c050102c1700c0201003180645800069205102040001805180c1e50f07441d000c0d649a110036004c0c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 580526933 1250 580525683 580525703
    0x19020d110307023327030a080f01120b060d020a1508010909031704050a080a05030403120c2c120d02070b0301080c130b0907050306190302090408070201021e0a 70
    0x141801840035120013041481804860990401003248801c41024020040c074001c2c551000b6203601d20314a61118020340e0501654540c0ba00340405020b0711406018203800c19101d1005112030200c4040c5040c640760845455001502c0e01c0c00840c000803000c6402075088400c0300e4002c03c12107854080c002001c62160303240143c580e0f031400c4038401c650050600800042022400d90f8208421040c003581050040003030b16102c0c1d0311a80d507507160707038040c001ca04003081c800300811090603000142202507142411040c13081140340c5c00018030031040701006403e444c1480e40700180707000d840007911a070310700302404020361901103044c07590707490300e9084440700144104800072030103400600c01d484c1200e128400400300d40032108200407500e809200021a02541e403142c40780301c0c0c6e0340c44034602d029500c151076442e49c0e0f05002c000c1c00640b1b00b802c100440304982281c420001a145e4240e00d0345c1c442c2d000b520b469150402440104d00740110340000780004540d01e040140c080c50b0225034081524841c0840034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 580528183 1250 580526933 580526953
    0x507020f010b030606010e120615040c0309030206011e08060907032a060c060e0d08010302030111070b13020a0b07060209100e0f040911030f030c010b0409080319020d11030702 77
    0x81c240c0d07044025a6800d900081d0219003d940115a80d1130303040d0004111000004002c801c0d42d00e441d40444000300701420310405203500f03040522801815020901d000e00010b00c2c5500c0107542c0700e07010700c1481061341000d5103030035176a803c23040c0d050090000c0e041514501d080281c2e10581e20b00c0d1500041c0e4444583e518090134454800704a0244010424900629986042c400f0707101c1c5401018180c40c401c0d2191030990040c130040c0841044c0308840e4840c0c0110703505500500d82110ba806c180034405c00c00c200000004a41404520b40c0c3c4142c91010100c900308251020960044050f4840410b408003c10004208422a00a0102d85006655149205000304c0c0102c80070042054640d4011220780c603000c8050810750802005d89014060700d18400000501007860103074a0000700650342c0002c83c3c010f000203030a018552103804129828007103d03880d41c448824501c0050038031440c1c12002d005c1400c1080b415010345011042985041101c0481100e40c845e075540219000c00050186440794 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 580529433 1250 580528183 580528213
    0x31501030605060604030f0303020906090607050f0d031a0402160f0807140604020a03030302071a01170708031e1b0102070b0105030c041406010c0c030c030f12030204120602220306050702 82
    0x244040f283c124a00c208150103503181270f0000d50001c004076810441c10000c0100d59210080203140e05486803004103508092a0440d03414903030f95070f000108050410804c142d01c104240e409284400c401c0780c0059446084403100e03142c00f580f00400070801c07007001c51514284020b09010b410040e02810130316032911410f420344e03510b5460840d1700941c007504c0741500b131000c02e20a80c06019502d11034822510b26500003900060001000d0740405400703105402c1c00102400140f0031200103212250065003410320050a91100340d1300309403003103181d00340400c51140c4800100090743c1da544c01c0c00000c541d01d06903420b086080041c05d000d01c1e8020f00c2901e10310031540c2881e00c2500310010302810f00d02c0954a40c03200444020444480a9914040c0d0340030120110324480070810003184920344c2c5180c03003401403401d00182400c00f0501720526105000c01c2002000d81c949407030205500410050340c40717900b030560b01c180703080001c3e44003103140303000c40c0200c1040100da02c8580101d05035022035015180316950 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 580530683 1250 580529433 580529437
    0x40e0c040e1b0307030b04091b14040608070311130f020a0f080f0408161a0907060206040b060607031119020306060a030f02060309030f030a090c0509090a0308070302090315010306050606 82
    0xb10b205001d041000400b640e00c43c0d400b00c2d0068000420204002071f040c1c8a2451010a0301450340702d030f008c6484d080220030020b251003100d011080ea428800395203443c000e03036201d140d0b9100160041050b0100c031051a074584400c05048410150100721200900b2010802500a515290041608000c0329402640144102031040d900850f6502c09580d8940d0381207220703009080c2450b021071084039142c000541c030021043d00a14070000110903894405200c615015a543c05881950001014000407415900c0660341c0410305840d0156034031203900d402c9a02101c9960f044103107001b03c500340300d0980e481800b030380f102d03034021030131600191aa0b90030003401c5816440010054804803605800500f4044017955100a020381540c3c100100020101e9040c0c0c401c9400c501300c10b5941c1e102801700029642098050701c030554460030645401c18815645260746003016003881070010005404a00c65011603040340c1c409015201c0c0b12110210340300b00f4810a01040300e440c1c0c00c11000451761708003181 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 580531933 1250 580530683 580530721
    0x90b060909100b0312040902030f010b091c03090f12031710050f15040303050403051006150309060b1f0306090902100c150519140c031605040e0c040e 66
    0x1002d041c0c01e440c1d040842004103089a5019054000d00d0108071480480c4c00240006201c807201c0907a07645452461040c2c1410143c00c646580c47d001c1c847d031103494440d401e001d034124802c1d14181c2003d44460405803541d24443e03002c10080750030741c038020420049080d602c4003201c0c42500c402c503080c1030343d0100000782041103440e40c0301342c0f07181c2d0780030849840e16415040c41d11001808145810800c00d0308100e00d6030241e0400e901041001808100304001040016100591281c04126040c1084920311079080f010900c2e10401d40c0310907201040c0065a0f0000580329030007400e800402403801c66481d4250000403421010910f455400110004640500480e0342d0b40102100b1910200003415a04040800c0080c4d0380e040f0042c40d4920f032200c0c603105150055150448240d521048076421340b05464039207084130000d44600e001d01081442c4002030300c2d0898170380c0591460305400ca08044806006590224842c0c10580c0c040c0085813146c10003c006545101b07180e5070050740c44400c038452107101c1c46 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 580533183 1250 580531933 580531951
    0xe090105010f14070507060c031b0201050f0318010603050c03010606020f060f10180204150302090a030b0901091704050306060d1502090423010e0703060e1503030f0d090b0609 77
    0x581e00030b28684284480c600c544000c01c440d5040440c16100e81d45400095002900446d10b40c0034803005264211091141c0111516604003480444d17600003010340c050228000c40c2c4071004408694081005401000b500c001c84000704a000d40d20700700b5503903842d40c1890190080d441c207500460000d00c0403e91261500c2810014640740d11400c400d0301010b00004c0804440d040b5070b40300840c1401a5204200721182d44940c0941c07602c0c00c0140c80381c3c00303517000105c0d0410300d881001400000d807034005040c01100c0d001307519109282d803001295405880501802400303801d0030103038a45c408a102c1c014005a40c1c00713030122402c1e5900c8000340003034040d00034001341c0b044800d500601d288841d55001482c1041d809040410001c0b5004407462030000c102a080f140540107000603c4284080c03e002c42c1d0111441c85e09120452622924030304011014116160f1814404107030103258030200102e80c00c100012081c19a910440d0740c2d5040108440c62045480001c6500455060700d040401e02d0f00a0b140d038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 580534433 1250 580533183 580533197
    0x9130212010626010902030f07030c0f0e160e1c0606060203071a04170c030d051b0a050304020303040e09100b03060f220b100806060a0609050118240e09010501 70
    0x500f1040c4040301c0c04812a005664071070a014005071401d00000e0b04036001440109072540c07c40c03800d03499564094101c0790540d034042c00b017080303a0646410300740d0b04501026080400d80304044400c4500b4140201c0c0e00740c0080390002c2c61100d0188141d000d062141c00742508001854940b14220b0304c0c0c1c803c00d00c02a101e841e414502c50305440d003c0b111141c1140c481c0040c1c40c0444007000c10869650491030400c601c681020401d0202205540a00e039403015068210344c80340f10421080700301a0140d4070742e030b40400c0350110000301192401c00487c0e02421115200c814140b4005ca109070303440302c500340c00315581410710740c4045241c140000c80b07601481c0c0070107500340559903e4410459204000e9141280c0c00800103503180491100030625025040c4410f80041c880d0921012900c1c5c2503007e40000e02a4440400c200a815800ba0111040d0b0380709203000c0d114041c298050403c010810342180740c031010a044410140e5085001c0170164884644840c03400c5141a03041207118002403003442c6c0803d0034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 580535683 1250 580534433 580534469
    0x7050409051e010b04061403060a050c040603020f0c0609031c0209060306092208091507081e0c100c270504051305031801110304081b040902091302120106 68
    0x5104003156400071540c000500d000e032200c0010262003c1fa070218081c4400c0c125a5509400c0612409603c031105500c00c0c4854140b0050024880c400ca00c1510205540030030442180c00140088a490605032400c031142400c001031171540fa50700a0710802c0f440d60701328484168005650007903a03042000241b00e10304558414042c0300e22000004c0c03186507480013502042c0002600726407000e2501d4090801305071a03181120034800c062070300920310702c0038000a024440008208004a41c180001ea5a03000d007c00080f04c040f0a4078010762080e21640d0086c0c4034a01d003400015444120481320790fa45550115039001c00701c0c0500c00e065016081981109081440b10f41495040310390401041088c40e41650a20b407034042c00e5412203061200180d044041c1c6603040d6a00841c043c1c9011007940203149007c0c5080c00d060b90b1084100502c1e103c199125a089030640c2d40c5034020650140c020b070601c1c140d4a400c2c40303400d4086c008940304074895030012400803140881481100181e9035003868409170060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 580536933 1250 580535683 580535713
    0x108070807090f0e060708041205040e0a0903140a02030a09091806090203211801080c22031203020306040c050414150d060608012d0b2107020304080705040905 70
    0x4030b40e07010040f0480d180c0c0350303203007840b201048810f1040f0030f1956291401e0400749040b004a15400036101d0402400307010900a00e402e009215030081086c600c0003580b05a189000c0d50741c000302d5400844031017004507007950910303004402440c0540d070b0740d5681003001d91100004800c5402900d01d01d50076100c0b014002c400901150300c032146840c001001c4a609861100a6041a406d090b0310440c0301040441c280840901500c80b00c0e0301c0d880709003003580c04c034680300c0440007050180c05442c80406420308200c1c2c11130444401040c0c0519000b5403031402ca0b0385005c402401039401a02c04e5402285442e070b011030180d21403410b40d025034107403100c03202e1030382c1c041030401080b01449800c00e048082c00300400d600f107031700714400c1e44020a0141c43e14442903242a422400e4a02600080b10285441712a0107110321020100d2105a40c0d50606054850320043c5928280e0000840b8110409103c1020310110540010142040707501c075800303c071040d42d110400e1000750b075a41040107005500402003550082 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 580538183 1250 580536933 580536941
    0xd180312030e0f120403060b03010614060a05041d010602060f07020d0e13140105010216140111010b090a1e021c0209030a080a08070e040515010e03160b12010807080709 74
    0x2a0084080301d02e01c04142c0303005410203940300c0404d803003200c0004080082100a029141c20703a80100c008008692420711403100400d800a006803103442c00092040c0824051000d0f500984500780084003075100c50001621002420f00904c1c0151154100180d010443c2c0a01c1521410b1294090140300d840b040703040e602070107200342181d400000140021800c07038031441041e8a0b0003043c40503c1403545440006400c0c01c120110b03542c14a0701c4284140001d40520382000e051130400c0c0392012028050210003401042d00382c4078950700521042c144000c1307140c2c41d0080728003240603040ca4158220194074076812407041c48003d06804550b0001e101850009901905205030050309441c52402d060f941c2400a41c043c007c540c000c04e00320760078410740950080c0c801030a10340a40d4100102d0501c030300c034020b80c21090300e29a4100400554000741ea61001d0000a1008a42010b8a55095280c02087d01c46d83c11800e030003e03111080000014040b94006001030440b0600e40103040c2d501e04004074503000e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 580539433 1250 580538183 580538201
    0x33003020a0c080c0a0b1305070e07030207080d0e07051206010e130203100e0601121a07230309160518061f020d0e040506130f090605090d18031203 65
    0x1100300755a0802c0072034030000041140d810000c015080020051824503805038024002e45a080607680800d00007a20028400703054481c509440501c96940c0c540480c040c1c03080b918005c1220314042013140c001186904040e54074500e000070b44140e2034030340d01404044000c6d4281440307164050360040141900c007459003030b00b01d1949000307200c1001003500070900e00700101c8440501c8076960b140e80c4107000c00034410303e03015202080c15000c3e8001ca680728550645000340d001141c0a01c1400400d100b140031300c0a0740d10444d442e001003411070042085c13100c202e40044032401d00502030202c404031b07000032200e0500c040d110000c0030071110b19808078030003040c10710007000f00350040c88140c4102e44541d03464ec48891500d0840d03009014880c5540c1c8014040c046400318640903d05000502c0019610b40700f2214250003007010000302030301c2a002003c05407418a0300503001c0361603d410f0203540c41001c10105a90402d6840f100d40511030011142c20501c042d10000e01683c50b000d005141e024843d03000507140d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 580540683 1250 580539433 580539437
    0x150f0e01180b09040b180a0b0603010b04030b0921310b0a050c16051206040c1205010204051302090a171509250914130201050903120a050301033003020a 67
    0x10459801003002061b520320360458a595410070000d004c0094081c0300c40d034410a403001819549000c0f041001400384d800002c2802800f0300c0043d034194420042d15180c2d803504000400c07860b070f030700200d00030740c0e171280f00b001114221300034189107203e40d07080c0c2880c002c03514401d060000c1c80c540750504070560441100d040801c07508010b00b22280340100041410b100d103940b02c0745801c17442c1008002000a0070a0038510340e80043c401c10002c06c50480005003240d0003103407801400540c03890030500a21545d081154000d40c0007000e01c000700107507030150442100544010115a4036070a03091000040780010001c0c552003804030400c6468680341d80354000c45000102d1f02c00401640592125641c4804030301c07107200f41c054003040350304400d0041140c00340943c080d100240c144421100c403607248007800603043c80b00001d1802e401e40c8040011454010040c10b4603500c44000420043c0554001e100507107103024000041e1000a00f401c1400c030701a035144014901c1c0e04d00f00403080e0060340100481e030341 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 580541933 1250 580540683 580540691
    0x91a070906110d14120f0f091b1507080708030f01060908030403030e0411120a0b0105160b1803030a05011a04080307030e03030d020406030f0516050301120c150f0e01180b0904 77
    0x4440b01507001d17214040c0c51450041002c41c0303002c04803450003600c010203070400c1d40d0020112000d10194080d00c0d444035101035404804032084a12a00524443d80e2401040c04500165000c20700050402841c003658030000c210200e641d98000c2102c1108490041c190150401c00003000001e020b0240c030007500c480540301081507058400b004d030113500b10024100d011a036100411020712000d204540008009081031818404540742d000303420a802d40000b80201c03952400724a000d5950200ca890a11400c0101c0b036503442d00c0c102e07a401501080c803800e9001d04007800e03000481c0c0c250341e00303480c140c0d00d49074011428030443d2345080b82c61003071540c103643d0035010421090a080b1040d00060014043c181c030003150040c52041d2040c12541d000300001d210f00d5407404d058806950280c202c1341103540365414210a070300c50703042409001100ea4041d003a8030448840b030304039560f0001c1c036914410302c1031386030384103044030400054400c0300d1f41c0b0074445225110005c040c052500000d0282c40b1403000a00002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 580543183 1250 580541933 580541947
    0x30307030209130f02070303060501180b0306040219020a12020a03081504090b0123060403050703081803060412030e0c100f110607032a02060a0f091a070906110d14 72
    0x2030803240f030301340d80d10001900010340c03000307043d0180070b401c004000130718090321400340a51603804090514081ca401230400000420815980d640603106002401c44407010540540500070b90b03070b0322640701c0403180c05008509081c189400820b40e01d01003501131b2640e01c2c09540304070341c440300300b030079084806d0707200e50740d080d129001ca42950790b0540600910030320351000c00c82001c001d408014100c11b40600c584804c00084c000900301191800440750310032400360b2610806103150b800a000c150081340c0512680b070130001400f200546035102d220054908000d20034001440c1e40d01e030300140708080c0d04040503a40a4044510071a240c3d01c0b00741182c90b16078110040c6a40700d41c1003c03002c0d500c0d003000945505040d00101da0610307100001200c8a4040d021a011100000e511198001c1ca4a8091541c81074200c1d124145900110710300d59000307002c52591b1252211200b541442501d4a400141045d000441d00c45e020f00284103862000c04004c0400b500043d008450100c0c0003240c10003c80c40c184409 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 580544433 1250 580543183 580543219
    0x50a110a2001110f0a0605040201090b0d020301050f0f0120100f020309150708010b0334020115030c1703040f082b0e0d140d090305011a03030307030209 67
    0xc8500c0182103000c1e18100026000050140300c103071031648a2900110182ca008030703c001951000340381c0c000c2c00803074542d549000580f5041002d0740042c04a4a00090031140803009500942c16928119040c10680382c01da400d211401c041060164003280c1081d16003a6070050b0000200002d401003c101d440c00000002c0c4101507600034440b0295164000c418031039084000e0200442060702c00500ca1594501110010000213042c49000101003001011580b00031035520f040c00e803584508980246255100c02c00180983c020900c1d80055103844c9203503d0720280c1840380000c890300281011002403e0250000c0d508180c00701c020300510040000180b2403410700b142c0b000508003000640308107041d0b400446903c0c54824810400310a18140c0c041303c45030010400340102c0c40c15600050301c4042450700c400b44100380b41c048001e41c4203400b00040003e50140405003034a2240b0700034410303502c85d40c20a555500c0c42819150b41500140b001400707551003070703001d00b1500100034103400594240c4880 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 580545683 1250 580544433 580544453
    0xd0f110408060103110102210304060f0504030c061a010c02040e01140405071508061e031f1a0d020d15061a04090e0f030d0f09060f02070203060a050601050a110a 71
    0x81401d141d006035004005101010703140300d0701640280007405600710b02d1071818140808225110a1408001c40401e0610015a011903010f421492042040707050908002e010b03101100c0085841d9424082d060359004481168080342140c181c40b010b0403003c20b80d007008090301c01008010150340da03403d201030b030340000741c40c44a0065000e04040d24006041c0403509081e0b642415160042c01100310a1080130388401b40b03010400030400540d403440d1500302001a04043c2c00c00b0303001401c800d40740a4080c1528082d400401c030381c04040b51a582c004c40150900c5020f003000342000c1d507c40380c11031800e004503003665004500904c510000107466626010348200b404040400c00700c02010129003803040320418424025080c48000c0103142000c00401800ea5a00c510f564030080240c8403000212150080c1e048502e500d84d2002c1c00380032448403102202c001790041c0c1c200f0b07403207403240101051011540b84a5a802a00103a4a02d8a4444180402e5541e0080d40d0407156041c07240b030100401040e03003840 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 580546933 1250 580545683 580545689
    0x105060f190512090115030803090313090507020d020a0203070b1e070503190c0507051002120301290a0e0607080708130806070e03031b0c1012060e04080d0f1104 71
    0x22080c1d02e8054203003d28020341801440700800782e1605214044948014015404803070b4800c10903540e80d5521a0500d04500135035001c1c130425000f080c1c011419030b17280c2d00800d200303108070780c02c0721441d0000042c120394505001c0c4020350160040e0340309002c0e146a003401046c9180810b40c119a03c814508c56541d05988500016074160300041130800741c0c074103481c400d06010300d210b01e890032180131251141511003032140300721072041819507454031701c05009001c2d40c14200c4100780c5040e00da69443d0203a10000c003662a10003080e955800b604201c2120031016280c2c0c900310f035614881c1d03020003d4113011856000c20400d0f103180e4014407038900060355800051640454000d1261801c07031510701403031301d031410151009040c40300050300b41c111510300006494040c40414542c00000386020115800c25502046060708502c003112203e1220b904460101c1c501d50b95000300300f12059441c54807940300c0e14190f5004003100e03810050340801ea031680c0c02100048051000005100481d800f00d989180d01542c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 580548183 1250 580546933 580546937
    0x9050c04080706230301060225120f0b01090513080c1515090a1806020904060f12050706050901090306020a030b04050a0c1202090906011d0a090e1011030105060f19 72
    0x403038940c02c2d0b507112400c0805440c01c4c0d150382034115418140e010b920341c0000e400e070f000c0c40d00d0703081e09407480040141c100c2e000601c082d00101d8104581800e0200d1071700001071040e2000003a003230002030900c85034800c0034400d0812005191441e6420799840c0036641c44020340b54038510801c3c4400c0352007520002c0403802141c8508107040141a04c8052010400009200984171483e01d4049900c865481807040d1160b0740c00880141e55004090000f80107007600d400c105010b20002e0008981a00200b200000e05401038040359040c40d6603140446003442114449400208003171810000202980c024000581c1103040108090320010301290444004492203c0c1c030a48841c6200c0180d80c2100c3d6218054600314419807078150160041214501c01410550420a07410300c40c0c0039a40c00100d041d0039454000346003401c683d5852484030007400d05502030090301d014074500359540e104a4030035014041c0c0c00e90786260440c0e180104000130754200d01d50b42015080d040007000701003125640b5a8008600d03035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 580549433 1250 580548183 580548197
    0x30f0212060f190b0f160f0213060602191112030a09140906240f040501140306030a060b010e15210103080706090f05030304051c05040b0409050c04080706 68
    0x66410090b2401042404034025020514000301e410001d1441c0b40130741d181ca9480c245d5640d542c003d001240c0c46602c400c0080c4c00030b444420010400072030640ca030f9560084800300741d055480c0c5020b904a940c54030400000d039011120004205412090710101c01c5c3c0144080380e00c110300c9401107200030303040700d4078a1482e40000690101c0c8a400c4039000c409070000240e007064083c4a003020500000c406050507114104440304401148540d01d90303040030901030521030340c0b5070186401d2180f868105015aa001c1505201101c550211001c02c1e01d124400080080c000104140c44841c0180510005d4a040014240050840e40c940070042070740031900d034118960303400740c0c09075441100005580f900c851441907070040011a5806040c1d8641a811500014410555180c0740811035007440006001d408040208014020003280c0005000c07000d400c1c07841403c4030000c0072251807084c0c2c0200d00256006000078000e044507a8045c66112821031007451620751108040c502d0104158050000525a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 580550683 1250 580549433 580549441
    0x31202070632090d0f260306181b040f03060e030a021e03040f09051614070b060d051501290315010c060c030f0e071212030f0212 57
    0x40098031544a0304003584810448840c0007010700701d0010842054200c010100b80f44000d070380c0e11003550848540c4015080042602c42c50032060360648004216043e6507400c0c1020b40345220101140c0c840c84005001c1008225100003003000c41d5005031035108180d082a040a200259810050010300040c1d811210541c0c80c43c0f5101040e508610605409508180304456415400141c114080d07640e0302d01e0b41e031618018820301880c0d401990b01c021800d404040c0001184001c41c0d1180740a00c00c1c8a514075400100c41109803002c0c40310300c603480c0d001c280800c00e01001c102c887d28800e41020f0000c1c0a044402e1485c5c907054a07241c051030721004024090801002044c211000c980b04400070b018800448100c1c681c00c0c0c1003140801003c03921014880b142c1c401c40c0340c0c46414060ba403203510080c00c004602c05404020010162040070788017007441d0030f6031810308440018207181210600e40380201c9200071a03650b501038015025070941495100c030000c1020f64443e0024040c080e11100c900006494 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 580551933 1250 580550683 580550687
    0x90109051015120b07050a050d06090207060e061009091118100e06031209040e011e1805030d0b0316080d1418060c0a021c02090f010f030201030f060312020706 70
    0x10a03544070001492240d050f510001c1c100c4107450307600558605181e501c076920380c0020b40d036a109802181c0c2d5218505180880c1942c4c00b513010b04440703800340404002801161a02e0395079900151400c0c10750000c0300404209821042d08409101c2e0b10840fa03060130070301958085804000f01e02c1d451859a02a54108241e102d54800c2c0d02004085d90f401030562030400c480802d80300c3c1c02c502d41e50000607400040c03c4946485a8003c4080805020020004103211165102000d40d581194034001c60a280601c4403010500d22004030803a0401d014500d0101d041d80c0400041004191268060203100c80180078003034900144002840c00401500b13024803518402801c3c5207014000c0820041c06000e4054031030805003001810500550388a640c0d50400380300b4900d80031890400961060583c07000c038900003e540c0344485218400e42e91414642c603044400350801009000781500c004a4100400256119800c10b441c8003204140000e0101d469482c0c01030031212500c004c10140e0300590040007955 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 580553183 1250 580551933 580551971
    0x212061005031b0a03060b031614091f2001050405010c08161809020c1f0902090f0c270108060f0f130609060e1005040204050a0e0901090510 62
    0x4085450280d1461600e10310350f5503c034148114000748400f000c2148003803d4001e52110300070b0503041c5140d544904e08401e09450004030310311020001481c601075a40898001c100f51440035400908105100c03032150a003404100c0d401055100300b09411118400b4101d52401820810241d00c00100c1c003841e1a040c043d0030740ba03610070701008000c8094100041c15521000d15030055050780741080c0350820110320324039500c105030807000445200168030404601d001400d50400b030409050541d2082c40411110101d5920000194029019000084888401460b000d42c805070800c172250903d180000840341c520040040215046000c5100300c08a603000b03103507143d21400407100404c1c8001603002081e804441d803084a4003446181c91500c0c0e001c0c06079003094010b0194000200700181d0b03a40506501c072071003a030300701c610f0100139400401c0b0740c00c15000301c9041c1d40c0007501100c030040c07801404031030000005203501d00d155030701e20504000500912842c407507003600c400042483d900e5100000204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 580554433 1250 580553183 580553209
    0x4060207050d0c050f010c050f0d030612080a0513031707031704020604091a060a090501080a060320180708071215060804020a092a03050730021206 65
    0x1400e0240c01000000f102407030542c09844080c1e072900075408500c00181d807540d500d9503004065001d514038000c1c00701d500203214400b000c000c0d134060000542c1c44105030b01004040c000540440010080149001d008200910700e2244c03030b210340314005542e615110000c04032030380c060b03140303c0000800c81e05041d032200070b03409141d0140234030011508040c0d002948a1141e446800c151644820300825500c21203940e0442c8183c2c00382940d07603200c101c4039008084040700d01a09001c00e50b07420203d040040644129401d8030b46c0a803240342480b5164511118000d80300040c90b601004245283e45082000155207010391401d44521449081c0404050b0041170038100201c0b807903103420b581e000050b001b070240100301c07042818141c0458940d4004039020740305070340214a40b94103000516211426a68030418001c110b04c003100e100b00d040348021810340320181c5a0000199180d0141004441e401c0043d401c0740824614500b102d016841014050360041410a05115041d004000050400c00760b4507601e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 580555683 1250 580554433 580554439
    0x15090c0b1612051c02090103050f040507050904140d0207050a0b0a0206010312050c061008190b0601120219050c1009021507061d030c0c030f0703020121020c030406020705 75
    0x20007040200a01c020703030000201074901480d00c002481124002c204640044002c103031054440d110801e07060000e58400c3c1105400203241c2800a01d040c450040c0c058040c5a1105c050f181c028603103010072004035405030082e260341d80700002c0031020070020003001100904a0f00a030118030f140c401009134200841e07102800141042200308540c81c1e0104009065923449030703510215141441c1c1c01c42c0c443c001d2050300c1c00765110301410310a11000403100c480840341e03a4022283c5414020040421181d82d0303202c0240784115031008100a58000c1010020359003009000508183d034030881c080344403a4402e4000c000c58400500720302d11400501c01c10100304041007003407010f80f0150b800b0840740d04107180d00c403443c41c0c804107548003040045c1d0008559000c4100003401c0c0c100086101c203071a544803002142d046e1081c070700036000900f030206d48500d00c401500043e1039143e10319001916094008500040015042d01c0090a003054500c0600844d4919900841d101c50901d20040c3c07a003001340d08000d00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 580556933 1250 580555683 580555687
    0x1409180a140f060307030b0c090a1e0f0f0510210c1e0e0607030909110a11060108060c0d0615170c0903060402130e06040b061512070302090d15090c0b 66
    0x83e50314005603080c1100c0e80044000416a9030144601d510f0103000d411940c000145240040c100b01c0c550000d01c014a0640c050750b840303580e11840d6a40301401882001c0114032080e504010300e00c0c01144808030101203040841e80301291201c2c400c4108111000102100d0b5544041c100081d03020040c0c5d6202d03c090034200440040c42203002d03010881c5800d540744103510000318401018402c030401402000c03d80c100b40002d001480050fa101d4002009203400182c0d100c183c0c100e2072400055540c1210350701c601504c03c0707881e40200b0060580c8410312040c2c90030340303e03d000138960620a21030301c844800c55651548004541d211550003160203007010480482c240000c1455035000301d03c042d00154101e83d41c409034840900000d018040c400180011070055208120510085052080c4211070403140240d6000901d22400b02c0c6014807003031001389188050014546074081c6d8020400341d8030080c1082c4410102d07070b031600d460b042c000c0744049040e52a114524108880d40220002070800315111034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 580558183 1250 580556933 580556941
    0x609060203070c0e041b060807030e010b091b04030206040b070209090a05061f090c0e012604080c030702060304031e03060302011211130909020f0d031409180a140f 72
    0x3c0050340303e4080ca2400c81c4034480070030100400c05040b60000408010280c40c1107a8507040038140c18411100c11010034140941c40041d02818071489403d401c0003400b01c1e610fa11008440588178213210265038000d1001c00000c0056590300380a44008e0070100003540e990b2610b841445070414006d460001c0c15071004020100041c2d001c05c950360700504125080101030018024200e00e074505902c658030343c5151500071400550b108100e800002d0003030300c450303075130b01000002c0719800d4909071070250040450001003000648000b004080401c20b030811282080040c0c1c001500c1030b0300c1078408502098440d40f00001616404c0090300318124035080400c40300d403440d00007904030304d140081400b003240c0e2064240054410a810b84042c88400c1d0381504c002919504044010004294241c1c481c05440301280601d10300442c0082070154195140c1c0103000c0380c00c8004019801042d0400d5000e1a48203050110340d8459100300d01c01c07515202e000c1101040005848a1414050304405103200650204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 580559433 1250 580558183 580558193
    0x6060c0d030c09051203270924130509060c03220804090212010f050301020913180b270105161101021c14060d0b130512030c0403030f0e031f0b1801060906020307 71
    0x4150b024010303151000381d090810200b0400c4070072703818160354090f580090007404003c0170707405188124008400c403411038481c1302200034180400c6421203c50901450914619880032042406080c41454020f080640f00c2c1d480c4000e0382c03c0384824460b100588001005248070313034140e0f000180411340c003c61422540d000811505101c1500340c1178565140c1802c030910a102000c18904650442c01054003418006000e41c03000941080d900c0d030306498868005010b16040c41014010084a8000825804225002c0d07840340200d0606a001c2d540c00e105100310303105e88454080341e0201d11240003a100d1074a43e003848424802500250003030001d0031107580002e0441d00c106030429649400b880d24040b082c90150302e8400c000001e0015002c02000740406d042d4050041c100750391094680c0b5140d50700001044a00c4082c0356a0781d58103500950040396074150226203d000c2182250001c1403741000c00031070026054000d82c0420041240f0041000c240d05c0300b2000094120361000d14600000c42d291 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 580560683 1250 580559433 580559449
    0x1306030b0d030305070c02030105090c0414130f032601091a0922150507030b030f060c030a0b0d0309090c05040f0e07020a050d020606010806060c0d030c0905120327 72
    0x1010f26603100b001c01c1650f4000d1101420081e80140248260303e080743c0303825101c01180101c2da01031410100500b40c03514171540c100344120500d5401c6040c10700d041e1511841901c0c0c6171000c1d81417160300c0c0300d0020690845044959554450480d44246500d01105202107a0440f2107090001a05403a0364200d969582c0c2050703000401001c07040c40c180010805040c3c0c1d28111a030042c02809078140f80c0c3d03000c0d00d85800c150700c1002d09490807c4031903c2d01050648800748402c01c640c1e19080100000c402540c400060358003d0310303d650000700018030102040c42d40c82e040f0000d40100343c035080300b00b05189840c02114200006454600c0c1440d181801100300003015004081145544100090780c543c4204580b01500340c00008a407003500c0320550180d240d81040c1c5007030f80043e1000000039800d09000c0110750100071304c1c2008040e01c05a03400308400901c0051050010818448000681d603a100c0803503004500808010f10f0361600703440030b940702c1284551101043c0754000c420a05040d070318010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 580561933 1250 580560683 580560709
    0x3030d0b18160c0206040f060c020901050916030f020d180203060a060b16021323010503190201080735130302071211040204091a0f060d0b030a080a051306030b 70
    0x40243d04041107100140031806107030040c000c00d0310192030000c0c100d0750008201101a0080d20340440903600c907818130420000440c3d0b0b110515941206d00e900f414481e600021602280b604014241161a607400c000d0303420740c1400355101d00742080c60606510f81444920703004038160504114aa103800c021b1030302401401042d00c002c10b040300424083d915000800043c90f0f28a071010081882c020450340c54410b1440e4443c0d6180c0800c00000c02c5a04001413030440c00728810003a1104000c0a03130045404000c01004213080060318910010480c860441e0200f0441c0d000380d249100c1e04003100360502804005001d015030041c0e90607042d001c65004030345001a03031120304031051101442d04020782c101026038000354005100240004200708903603c010445c18810880c480318031074203002c002e0313800c0c02c81100c2a4811420041111850b0442c4d012500307012029054a00c1d042854a48844540020a0005c0801e000140036001c065503222a40c02074921410100031120503100400c11b0148a54 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 580563183 1250 580561933 580561937
    0x1a090c070501061e031707030801090902122d0c06032a0c030703172707120c030c0602031c0b040209060a0e10050906090607030c0203030d0b1816 64
    0x150440c28400d00b90802000f82c00909405a05010000711080544049100999084800b641c04400f640112402c40340043c0c0c2540d80d090b590703420910250300400e000c0e10100d9200c0d0030b50010314000c0c0014080d02c00d004001c2014003811643c05401c00c4100210344001e9062070f004078180b10071036980c0b10141d0750040614142103141722018600e1300d40c101901821103150708000301d15400c116a00000400e55603201e070b035a400040e1131801c440c203285102a1000c1c801002020300c0b540c900c458061070141c2c030500000071074040d03607a1090704440401882030181c1d000d00400702c080c405d004050704000e00411052004500d80314012907103030720403106c3e0041d4425940c2c0702c0c80c44003c2980d403901500c945071801848280e4035080100040c220045e006030481c040d54260099546990148060741c05c0311402030090b91411020908101c41c40c5d00402c021800d04c8410104000584c9041000d440480021007000506103119010080c54580c3c0d46000c40562205404000e81083d0100300790b1200882d074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 580564433 1250 580563183 580563187
    0x904110a0510081f08070f0501120c120f0f0c050d140f0a090c0f0e090706090f030f0510050c21150d030908030c0d032003010608100302030604080405041a090c 70
    0x600101e41013081358000e102c144180c12000c5042181100044d08a6000341c0340c013208000c9a80c9002c090b40d000d0007042c0b000c92940d000c00c0b00c1000030790b084244090f0304000006101200d00c1851030450381c4c034111090007c1c0c0003082814016034584100840503440c00c03620001440c003500b147d801d80c0c0d002044080d03200c0d107800c83c00040084000c0d418019055202050403a80e4603038142e241c0c4c014088070340010a116100e00062910b002c0c070350190980320b440c0814241e941c1175845000002d00200c000300d402c0d119020301a8250314207445201d019050700148950344004180070300c1c1c210892161000040342c901001c1c4070219140c441003800014060b545481484220305090b654806241d110350454080003802d883c2940003c28200c0ba02c0d40c040e141081000c00b8103000d40e00c03d000103419041800e00402c010311140d0f008005841d4080107803490000c071107403280d001c207080240a413411541040041001c0c072085c60a4003581a9086402d0244d00c82e400207603001915910340545200220400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 580565683 1250 580564433 580564471
    0x1a030d0c081c090203010513330204061e180e06010215090631080f0708121b1c050903070218150a060801140a03020904110a051008 58
    0x90101520000c40020700060718800c00000340c1c0c0080d00748030008074417951801e000505000b076280300d019419030f0081030110621710fa040416052034072600280c1d000100810b01205204441e000030070282003a0307907507021005207011035401505415180c4d0000c3c480c610072400f001552004007030003124000c1e8455034154680d80c00603410110f00407000701c070381c040800400281500000e22140288110030b100c0c081840c850402c14846001004580580034401c050769000c100410042c0035003803601c000c80c41c50305000da80d816510358007010842c69296862820402d078803000443c031101d040d100402085c5440300380c8003450b550f10800545154429910800b0030208013007007040e00e86003503010b0081c907005048010f812036038440c01c4070b4410340c5c1c12203e009000c0e07505201d058402140c080c3e071038090a40c3d09080702d00c2c4082100b010229000014a4000009030f0b645041141c050b80c00307003100070001c01c0c551080c4554918940c11490007000b0313070f80d8131029495100c0d000703907800071003481b85486200e5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 580566933 1250 580565683 580565693
    0x22080f2b0e180f010b070b0408030405070b0c010623011b050c330708070b1b0a0807030606090513020d0e0715030c090e01030b1e070c05011a030d0c 65
    0x90640314103410550300e820080446404152581c007503c1c01008442a0340e80e070f002c003c0218840c0c80350007424404010081000610b000340607540051003002a1203030b20341c8503100b4501a8001d01807030703160f60303440e19400c01ca01c1c60392004580d4071710000f01c0703000820341281c000600011100441c44a032000312080480900c80140068030b1032880c000c0c03d914114512902400d08118441d040190000781000140c1880121008403420990f01c0403216003010290303190500d04850040040344400603000e0722191030811903000346500b1010383c840800500b000c1d8001021034205410100c14092803800620290752442e40703c060703c0806c484056034900c1c84c41403890103040e0744000700e5518480c80801054000d04091081107040a82c0d808110b41120b50104503420095485a543e03a5900c400c01400414803109c802075021010954210f4181c1241c1180029072004031803c0001400c070005440400c18203005031030050803640b440d021000503880000707440d4a0b480d02c05c801031010040c51082000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 580568183 1250 580566933 580566947
    0x10e1023040f0507170c0f100915110d110d02070b0f1c0231030804050f0f030f0f0706110712150c051b0303070903060b040222080f2b 59
    0x1041e1080c5020348009517255096898052424591003801040c40810941c1490010011f840700942d8803075401e41d1500d95400d1040b90b9800c0303001c04009440c084e01c81c1c025010050440300345015a55503520309a62007581d0f04090303e1584090840d0842981080305503121030951311800b141e15100c81d0340d9011280b00072034406240703140b0f05925001141d4542c1804030380030100a01a002d9a512000750725a24496640c1e10f05030000418401d0240801e00ca5800e1841103006075407400b400c201503036080e03040042d2a080542d41c5042c42030f440788000c440c280b642840002c0003006642012909401600915a1100d0150140340181d074043c11141c8280721001c0350354030034207000c41410801298460001040d40c0e0005136004900202ea81c1c0c018090a80081240d125540039585c9000c0c0345d0842e0f843e03070064003400803056800307502032000c5001c00b4501e125100070880610241c5040b81e01e4034200b1800e00803000000481a0442110314030b821030070242410744190080d48178041d090084105680e20 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 580569433 1250 580568183 580568189
    0x41b0e03010b030f0f06062409040b0405040b191107142508072c0a0209031b0301240608061f030e010f0c020703170c010e1023040f0507 60
    0x511407001a4507100c0c801240703d003131001002c004d4901c551f42d83d60921042d40042c42d00e6002e003040700524104070803242000340948100c010808035191030110001001d9500c160703001d031003091080081c00544400a4064005080c10a40c241305511901080300325900500001609142c01c0a050380c2d20701100744102184101d001342d9241c00e1006201110108150901401d04248199540422401140482c441c00d0194000050001403100d540b80201e103038018000035020354081c07000005956081c4081c0311005012500101441c590000701801d4806002141d40d801041011031141c18011b00030241c152a09401e05928540340d1001040700300040343e0100300d440c24080143c0c3d5540e98141c215100c2c0c41d060f9002880300440701000081140e10204805016031f1001c64100005003611140c5408140040500c13410180c04100503400d481c401b4000c00301c103820008000c8404803192081d03500000d43e866600c0344960b1030584808002d100a80040c0c0405810600c807400c11508110304006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 580570683 1250 580569433 580569439
    0x1140f042417040c0620011a03010501050a0506091c080301150f1409040903034a1e0307021203041d0603030a0c0c03060203011d06041b0e03010b 64
    0x80032030100d51040050901e810454009034981000d004100420b04403507010310b07040719040008610304041680d0000104400d0022610b4030f1110b821101c1080c49501032000071070402981c841c00180c201801c40d0f4050b00550b00c0340b542c50a0a00a540703d510664908031001d80340e0f800c0030900d00712011502e144621000b80f64403000400821a01c000085088001d49684c481d145c42c0d007058030060321000c0528070004180387e4140440f2500b0700e460340000398154020f0030000f0340b40d001d181d810b990755940b0b103141e10b017200420041c15201b040000c031088020700d002c3e4040400145002d044e95266604016034801c0c00c070400c1070703c81076074505200710781a2960041100d1f506200a26400c4e880c3d400622030f140c2c02210607408600444012022144190001400b45107010a80e00701520807024101040d5440e44000b040800069800c0c4001c40c007a02001d0034007084000c50a9400d41680402401c984c051810500e1100c80c0089035001d00b0b810003040d04080c01d403c603224022a00406681c255158 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 580571933 1250 580570683 580570709
    0x12009031513060507050702011205150a030813120b0a0c050d020a030b09090d020a08030406020c060a060f0b0c0303040f0204021c0b04051b191806030b03010501050306010501140f04 80
    0x80709908180c00c2c40b01c2c00d20900c01030100d070741d0300001501d0303034015450064085080d0010b04805084c06900040c0d2040400c00d10818074142c032008070b6243e100f140c1007242c041c10000307001d1545050008081006290003a080251250395035500b076403540001d00741ca0400c946803440124032a0141d42500c3d045070040f00e04644501004030003d001d061071a04d001c3c02282d400c008904c022101050802c0d03106900d400519980815542d030700300c0c0340d000800503504681d0900080c4030201042c0074540c05080c880e403000c12510b0070b01454116181107135020900030541004111207000300403060382c0e4011f82020350200303200c1d50f90010902030f1181400c03814900302c0909a200c01c071400d95200030040041a03908000300d980e0f003a41800d0070030000706005c114080a020584040000b41d12038003400e6542e28003108010481c0503d0301000c65260403510100340c641c4c5050000d81001d1150500500085009284c80d502d00130000e80401215814840000e0380014504411113041e411200240884040c1c40d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 580573183 1250 580571933 580571941
    0x150b0409060f1e020301150c111002060f0705120c0307030e06190f0209010e100e030613061a1005070303200408070b030118090f050d03020a020d020120090315 70
    0x400200483c11500780c0d45001002c004182100b01d200b45c81c141c0f60080341d035880004c0c4c84c032401d807800340c07504100b103600035008942c1c1012522212007018a50105400030115405c02800c0c0f200d01900c0184080b0030050140005001c000c080350060b508510903500c3d55a0720346409008801a00e508a4081b070144500300a04c0440d12400d0761504241c6040d8804000f040d0520b4041c10503845023414040c002044195a1501807a14220001c60690203007008204130800802080c1001c004031000039204040402410510400740100c0485a8240c1c00d603042c0c442c203400c001614000b000490740b0070484007141420806001e0307800207200d24000c0c3c1543c00e0105141e10348264a512500441206009018000a01e48000c1c1c003541d050b501c00d145000580c107981d4101c500206014003090b65820a03c043e64400b04e842844500ca01c000166005640c580c049035000e4544100c844811085a240541620342100503e014203a0340600b103007030b26510403030100028a03000c0320b40c040e0308118802600340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 580574433 1250 580573183 580573211
    0x7050a1b0f030e0f03070f1518080d110a0506011502031e04141c0201030b132903070303120c210c120c05070b0c0412030903020f0d150b040906 63
    0x10070080a8201c83d6000c50001c6001403585582c214424a00307541c0c0c10301f60a10100c00a031a90008408040c44c00420001189125041002c01644500314940004e0b041c0c250041d448140c1030070a0600c01c00400c280c0c1099960030340d44400c14407800221003528503108003407501c00c0c41281d07034507192407c02000700c400c00c02054502c4e50051190a000c2000c00b00200300c03900740703400f4400786a41e40712060a0005125001034000e000c444110b15880b08a6080c0380c07000b0300c030301d11581400c504046103d120119200d1104140c000107aa0b1451003a8001903003000001c1d031000098413078a05068020822210605042d40c0141d8501451884540b40042c03004130948550711039003070440140d031180300403202c00480c00100e450f0150030000140d01044808042203120940940048201c185e0034a801c0e41d50030002603800d4112812000148065070810a61410340680b4021140031114100c1020040e601e03c000c27805030b84020080740380c50350080041565154008502d041d0009014004003d400e455 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 580575539 1106 580574433 580574447
    0x1e0908041517010b1c181502071205070302070f0e0411030a2012010b0906090405010e101425030906060906030503040e010801020307050a1b0f03 64
    0x200b40d6141001c16054001c06070141c082e5294000713007180661034610881440c80160400c0400200c103851b15108000c001d60281e01100350091400003040030340140040034040310803503008105041d4001e001801518400d0b42034401d904d0b1503c3c1240d0106585000318010400454002000140294242100c1c500000d0454132120070790341d11540c02d000e811402a0790701e071009819044c41d04112202c0400034084074001d011994004000c920702c003400500b07052041100310049001c0c41020350005105400f203d0941d800c03c90841e200e94054a2401c240115100d5204009441800f0009074170204a0140080581c3d5942e07100040f8045d100c0140d080d212030b5500c00000441206611403080154419005181c503149409000d0b86d00b19416844411140d004104101c07000c4e42c8a003c0f1415081c0c4c50804c7c00084012624180c0ca00310051001084401003105000926802045c = true := by decide +kernel

theorem cover : BRFrame.Cov 580395683 580575539 := by
  have h0 := BRFrame.cov_init 580395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 580395683 ≤ n) (h2 : n < 580575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
