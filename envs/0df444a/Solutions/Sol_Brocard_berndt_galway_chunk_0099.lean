-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0099
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:50:27.589037+00:00
-- url     : https://prove2.me/submissions/ef09da7b-c470-4342-869d-59ac9c5c9777

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 17625905 ≤ n < 17805761 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 17627155 1250 17625905 17625953
    0x30b0307091e1413080307020106081609060e0108070308030a230601020601050303070507030b100503070306050a110408100b060c010f0614010203071205030a02070803130c0801020910030f06120f 86
    0xc41e0800351903c1d5404e400801100d0041300051540717000317500240090052206407660b03612010481514407009026041529260130008a811180003000764140e548441c0100b10700c43c11500d954419401c02441c00c0d051540301c841d21908983d46400e403c200b81d048400d144541d081117000a414428140c00c075070b02940c000e02002010480c001240f03004c4a03045070000c0200d84604260b81c00011581c0c00c416010f209000c4000104040780d4000351113201e41c98000c1004820a200550061059100d241c0c1140d01c00a0300c203449489981c071080c00c5410003001e00380752883d000307a054251000c1c05214200c0c81e03035910042203945c05806400b48500400d1014500e071020903500c000204190014007000c11002000051101e00540d040b40e407000e4001e103420341c403480c041c1c040410211407010111600b03415400c00047d002c00500a540d48440c00030320b80d004034210795404500400c40c9881c1c1c54041900c4030070000f010090103604002203801003040014003265800d1481040c05802005041021 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 17628405 1250 17627155 17627161
    0x71509050f130504050a05010507080c0d020d0b0a090605031902031f09020931031e030204050603150109080304060503040303090f060525030605060a030b0307091e14 73
    0x150000105080d5441254485100481000030455804015289001141c80c200521040c41000565040c3d041d1249000380301550368020101c0d440c040a454014207030100b8444050415000e8001d0000102210310000e41448500001031082d01958426034040d5500c40c1e060041c0c0c2030a10070880d103901290f030050000c01299000c00e56440b011440c580c0b00000442481845403a550080402590000e149050310b0804032080100c0001000b03800341c0410381410a020b40c08080f850000c80744e40c26403114000343c00c5030458410812181c0550000305503003000040351540d81c44001c1c5018a00c0c07680f0300411100d4a00007d0040c20441c0c10100701544244010030425034000d04031303a4090740c14503004ca041101454030752541402c40c0c000400f000d041c1710401c04031040d040b500c4000500c09802d41c0100c0701600009030215a254000e103600310104220516030140650440d0700c540390050112007540d5913903582001143c0d4002e04041c40d00504441c0700d22803010b00d00444034018000c90303030181141 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 17629655 1250 17628405 17628407
    0xe06041101050309030412050304050a051009030b0603070509010306060501030e1207032f0109120e0f090c0408030a03020a0207050405061c0203030c0f060901060e0403081317040311030715 83
    0xc0d040301806041000000004000d21003d000383d0340180003034000c41c40721740c2c2d40d1f20300a078590b045070054502400f808400002c41d0306e001c3c0403c034040d010a8451001d5103041d40c071342c1031603020003c145507094428003c0026882d19035140340c0780210701446e0300248043c280b0307000400b039480e0204e410b481c47c0c3c0294072400030107809400b150030385a8507003007c2101c1113200ca803520145c0c0c03031440492a1900e4418035288078034410740005c650b007072080119042140000741e0913500461461245038100b02280380000035414961120703a0002c0f240682c140c20700303640342c1c6c2c0f0900c5d5134030590760040043d4001c50405400d9404105480c060f080460702486603181000c0400e9400b003c40308035155020f850701903e006e5407004d200b101d03030b502d25610a17903080f00160042c4130340da820151400360840d8039040000410405d17481c0303041d0040da85a61a994a61103030000c100c00054080c0b0156038103002003a98600c40340d0040000c0000b1849600100c045400c01002c160904665034800210210181042901c0f5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 17630905 1250 17629655 17629673
    0x1170309031c0c0204020a051206060c030d0207022b030206060406180207060b090108010902090115020a0210170103030804050d0809030906070606260f03120f04020111060a050a0e0604 81
    0x80d1040110402e55440324500403140c2c1e804500c00a0b40041c400110540340640c070000610800301001c800070041d0710b4810607c810b51207501c1c3c0300b003440d410034400c00d40740d844070381c004001300d500040600131030b0740b02e140d134441d841c170507800f0102e50a58945130548100f64042c0801d40d0311901c101d600300240743c43d088080540320b6100c6465001035600142c0d1004018403030340703c080344803005403498146607107030400180280680442644920780c544000500000344012110b420341d041d1b13018202c0d0a00d543d0910000003a03048401c410b2000009040b0b0f2030366403602c2418020740c000ea60701041e5041c11304006061490700010300d070420900b0340800015034000400c0360344915017903a40c5580e5401e5400d12000802440e0009074824030805101821070748000c95421140d4201c0c82070360f800e210003800716a40c074031a1034501b030100c8404100162140b581d031210643d1040c01818070000801c8006180c90511404440e88400c6a80c1c840a214505180c0d1140180382d07031000c0d00912040c1815102c24640c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 17632155 1250 17630905 17630923
    0xc020103050603030714010522020604060507030c0503030405010203040303051501080408090a08120301090b0102030c06070315080a0f03021b0904080304140601140103050609040305070f02150f030117030903 91
    0x14107440c0c00215140e03403010004c441000e40c0045205030781c001c1d50030310207000e41400d450407a13041150400b6090812036030003a4269403a4000c1c4000d280500c0d1400a4925410254060381440707003092170304011403000d1005512561048000682da49068500901100e0015140400000b070180c82905a40d80054810b40c001e80c0020700680c4600b6020b0000d12030040303e401001c100d02440720050145101c80020b907060343d0110406019412a0b90012641c90042d8881d190981d4820004108424041d034481c00a0041359083d1442158588150b40e280c03011301e0100f02d40d28013540744c0c12814981c0c180000c510100c2d604180009041c00c400c0064000c0e8130280019114080002c08030b0308204c1040c0606000c81b40401c1550100d683d01c40d0030265000311903070020701207410807000400350324105954a115a40c10340764981041140e4440c09800d4015840c102e03000000760b18040c00310366440e4098441c2d010185142541c80d030420500e00314680c12100081c011f40c0c0244815241940c0116410407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 17633405 1250 17632155 17632157
    0x10503060601030905030d09050c03060f0705031b090604060c0204050117070501030e0c0a03030504090507050910030f090b0c090307090603030e01080a09080a0314070c1709041113051f0c0201 84
    0x4d5a400c1c0c0f4200030703040d4803030310700901e4005e850f00401c5d034100140860f40c1c4a00d10421000d07138080e1341e0361000c00d03001407000300e51420004104000184555020129841010900008050601101c800410503c1d4032907003092001c10281c1c0170000c02c600d030502540e070142440040090342c03c81d031260740c10358400407400360505040c0c9440c2003800b154420010200303420700080025161030307624203000e40164440d00454500b036040c2000998101d010340300b1100d00307010141140c03104145c0100128014009d2023142d004203a250032507840030a2038020f000c0e0103804451710a940e07030400c49040510308142680040c1c00241482000c00c0130a4004440040d0b100081c08c0010072961200c0030b800c010309101070300a00075040410840704e405c0e4503a1040342c01c4401c0c02c200c0300441d12114010394500141e058014038405051600c50407800382c02c0042c100a4078042c10106074000032826580075a0007801034400c150404500c100650718110306810308001005a030141685041100140b000400d9400a8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 17634655 1250 17633405 17633411
    0xa0603020102072601060605030910020a02070314010e0f03040f06020c060409021608040612060801180314120103060902010e011412061309031d060f07060c090b0d050105090c0301050306060103 85
    0x81e21801130b207a00201071010700c000304011034840e00c001e0a19081030301e1620951140c5561841c5112f1a4801c4985520450300240a19481e65891140220f01072600554554135400e52840c4103404100304012811100090360700c40b800e00303520502d074a1155100d40110751011414460a4072201c048400341d90341c140c405030381c40c5190906d803141d00602c00001404400001000501c4a50003c520810364180c43c3d07051012965a480b0113007614140b45014912601c2010b0740700c00240102c540c03030b005d0030310410141d00f00b40502074960b174091401d034000d0f40c626442d03034440f034210343e0b218140300407400342400c220250043d000303009800c0703000319907a4921180d031308030104126a40d82c0c00c80c036407000480c0d034080c08440d40901d80201904411660440d4421001c4030b10310181c60f2400c169181c140070350502c5420407880e5141d66002c0c01080340000d003400060000410f019001c1c2c0014407540c400f0203400708843d450311040c00006c002c01004141c502c0c0d010700051000350340204416800070402d20b808 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 17635905 1250 17634655 17634689
    0x40b0a0504050d0503030a050c040b09010309050106081209120f0604030c020102071211090a020a020307060216080301060206090f0607090e041b14030f0303060f0d031704080405090a060302010207 86
    0x50318503115503042a40e100900704003a60030494004025803144034100c0062010362541084280305004901402c1c6035280280026000365100350f018040d094001e4001040072a559016139081c0204075a20303000d40c00e0002414025401d05122904a100c04030ac01800e41000c6110700d02c3d00d40c04003800060070081c1030042c01055a20800016018244070035104000401c14501510985040c003c058001d0042c1e0300066094100780c0300707803014074010b03801451030808550340f988002d501a1641d84650204104904e01103003240b00130314080c100c560020903041c140070f14402d20b8400181c00051302d95001104002480d640300400070308a0380848622103164607149044c80c941d05002158180700c0b849600c0000e026606841c0888030410182e0984400c2d00310020031640780d10084038015000414058044064102100361750b110b24004d02c4e00c80f04141040b204031134540400e480668038070704017003414025441c0807142c0c141c1203080800100301241c80c580c00070751207800d2032080400003100c41c652 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 17637155 1250 17635905 17635907
    0x6090315110a0503040303140114060f120408030f0916030201110c040c0302090a062307021804080306040b010f2c060f03040c0f03050307170d020309010504020f0a0b040b0a 76
    0x100641140c50030071065110200031600038880e4008440507030000782020001e5805191111415042c1c1d00f620705400081c40408090210340d510020b03007203400308070070441d04071181c031403800c0340340180e100300b0a031076413800c000f88000c4e903d00010f00320780f507c6d03009a030000c5041202e0707141300ca040700e87c282840780c015544540041c0c14a1043c0c0d50f41904141024156403050381d155004140d081800c560350840350340c84182c102c81101840300c80800e1501c540f06049001d400c10b03805000000d02c01071024140c0b4480c0c88650800400a03107003111803507004418003a00e49410b01030749030311744000e02c1d0480d9178882e0740c10002c0c070203035584008409400c24800310010011424000320000341025200703d60704c4410140c004182d5000315026260100701890104000c00c003400d00108403500040114189010b031744a55110801d00012280c403150100040e0420b00038600255101d188504000a018506801480310b1806c0d40240140304007164038040c4088001030098a0550300200009620754181000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 17638405 1250 17637155 17637161
    0x40b0a12020d0e100e0c030601030206131509090f0209030a060902010905030a0507090501050303090a0603050601050405040e030a09060305070c231501060e010c031704110402130515030106090315 86
    0x2480a0140381803145110304643e00080c40030290451110400c040c0301c00100c42616280c0160fa6564140c0140b4010805480c01c01c2c0900f00c00c564400c0041a0b0b0b50780d42c0c8910302020041340041c030128415517410020718606118103203981880300c40c19442e1807200380000c2d40340d81181100030480d9540f03865480a59105116080151102a04503001d907030b41c1d414841d030340341c4192140414950400300003181d10b0030b020007982c0700303040050802504541001010b0300603000060981d410004280000500c0795258010800e1144400004c1c0d50f413803614440041c00340c82182c02245c10315041c8802d000140d03912540e020401c603000313840c0070011b42c0181301d2600c0103299822403010911600b510300d010b01041d409428101c901a4490401d24640b5000544e20a06400800340c0802d25503120411b1054200c0c80155009100f0f080110b800000a4000750498110a40c5042c518092510510080c01c003a96604410f1520403802130941d85000b800810464050000070020061075140740850403440e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 17639655 1250 17638405 17638417
    0x30b09010e0f0a05100b0901050d050f16030501150303050f0703030204080d0207050315010303021515040903080907050105040302090604020a050708030a0b100c030207060315050909150903040b0a1202 88
    0x107000c0e07400e03441031102040e07901c04400f9002e482c90700400e04100c1c2c0c90346152203240144007000d01700d8410760f880c0c182000726010402105603030b00c0c007031040c120740340c80818442c5030f940030380308960144441e040d0b0800c14211a0101004c40780419000f6081c004070b500308090b16181e0140d0b0300d0095640b03020b440d0450190007030fa03001c000c2610404403211589500410998103540080c1d0860320170415408403d007101d2000c0c80007401503000000c884011140c003005c8241d110110441318074000b911075000c034080715400c040540001700840241b041c800000d12824000f488240303402c50801d404c540000c1d54100020780a02d00c91903000070131600e400c0c040c1096070185500320362041d40303e02c6d003540e0a00242c11116030a6110302c40d0f20b070081000038001c80c48159100c0d05030740101489802d000c8150000c09150001e140000551100014507544092100344143c0181014203103186140c2000584203401510303c10780d58005010034420040468296503a054091404400000c0b074403044100900c505 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 17640905 1250 17639655 17639681
    0x207051207051801051503011a090a0509090604060c091a07060b060304060c02010f090f0b090304080f01020d05090d0c0303050c0d06030308091002090f0909030f030f01080705010504050a030b0901 86
    0x16420310600f0721032200015040314030581d1661031000c4500b0300320713195100c00d015540c02c0c1c9201c0481c040041d125080a8000050050030b50260191110f00090761040d044071100106d40c00f400800081060380d0041c85010380480c1440c0c901da5040042c4008102404012220150300104183c82400f216400500e240c0c03e0217410b072607030f0f41401e0502002600c44a00c80704007560a116100039100964403030010803c0c0c200300241c01e51340d1030340e550320324289015200108610041c840860303114005d002908030746541c0f80005984240d400e00c07103000d4410050401e4669080b0143d0040031a80288010040d203070306140005941d80d921041300854000c91001c080c22502d080c102008054020420302d01a14540c021901c284208800e22400da2041038049500602c100c05000715a0506a5800c2e402c00c04034025282051040b90342200c50750021182007000c3c0c2003100040196000c184810700c040d000030704c0e050b850701b81400d000c59030303a100324400288011100400100503070401c1d44098100154 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 17642155 1250 17640905 17640919
    0x5010305030d0c0512040206030613020f0403020108061f1803060f020c10050411010e0114070506180a05071202040b040501080d03060e01050307060e120706020a03030c03050601020705120705 84
    0x40341041681d0350414041c1d408014034046244210381d00810130f0b9401c5003d00d040714085603840360309014140d00003400540d08100e4a04a04d00c96000c903001800c003094a014100351902c1c5140001004400042c10b50f03809090850b0419a036150381c40c03840c40401c0303170070f003007450305402f80c0c407a040032100705503001900c0c4920700003035000200c6158008100381b80c16001103c07400103c200c1c00104030b882c2035400601d1800d80501061880d4010a904200d84005040c8056003510120000c581680708403011242608904104180e501080e0402191600c0c210000d01c5202d45e10b41c0c0b03180c0c2e900114003a01c3c960400c40e0018508550f00d030b4200b0408080c01900c01d02995035034826640e42c404900800b0f0011070305001c40880c4010303905601e107040702c0c4010010141249407480955203607030141040c46d0490701c2c071814000700800c100040c400a060340e50042200c1481d506004044072100403004040504000601155a0740081d001c0280d400407902d03003201e8614052580d14060741c80c0d00554100d80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 17643405 1250 17642155 17642159
    0x2e0e1e01060f05120c2812050f0a0c030609080910030f0c030209010804020d0201030204120b0610050c0604030e1324050402040303020303043c020112110f030c04090501 74
    0x14041d00118216000c00c04114030b1039450340f080222208204074910500d602443d001d00310752804451130492100364101b803000c050051003200d14209565005852014a010300140800004000c1003454445041c042c100104007555074889842e694800039051030703100d21200c0248000b80c4225031211000a040e40d003080208980a00030300800114a25070314035150400b1041c6010303000700d45a0181c1691030400701e80e070304d03801c000b40c00c075280c2d00a0381015402c0c840859000e040520f00c1140c81d00030300c0ea060340791810300b08100c502e6013180f80d031404101c2c061081a842900002d0703400d4216500d803c00020601d010030100c0c0002e025141852006410001c0007030b00d0000302c000015041042c1c03030340d0303601164484040c801a44603c0c030004005900810006000c01c014109a0090801e076800780782c3d00d41c0d0842155812040e02441d601010079080125001319a0400040507058070942d00c14400301500b40d18020f000c0c06103404048266000100103060308213001d0480c0e000d00340b020760403c0107503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 17644655 1250 17643405 17643463
    0x203091203130606051c060e0102070206040303050409060506040308070803090c0310060503150127021306120e010501030210050a0203130e01080d05040f12030509040c030e2e0e 78
    0xb00990b054800a291850110302800c02c80b80c0464444405002440071003940c6d40c44600030300440c1045940b5550074001c4d00c0040e074950004000039806556000e0719181420301c080d084401c00d621041c45444100030070400203440000b40c0d42c269412842244d22a69a4458a0704010a0040c859454021000b415030303c02d250b9031001050701c00c2501200d04455a0000b4821064401c3c001c40218048900640c10a050030780080c43c50200001400b41c103005c0b580704148203d28180d001b0601064130016241040300040c400c0d6000403c100000744455491034000c10390440c200e40c450420440005a01044240200204c890009401405401e0f1a9890102584d0041700b0300500700c06000312140103110030301c62000d0701d0540c1ca50f00f40200c200c48c40d02c1d100c02e4460004441c2101482824811044036035901e01c5000f20b161010b8901040b8980c0c03016800742441d00100c0c034241c07009002490380051005940ca650102c400484002079002c00e41704039549000b4840c141842e0300064002649800c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 17645905 1250 17644655 17644681
    0x606030c080705030c0a0504050702070f080d080c090f10050f03040606030b0906040c0506092209060e0a0803180a050607020c01090e0c030402040504060b060406050c06011a07060203091203 83
    0x15901441a00c1e04a0f0700c500c20103403204842c0764196880303a136604040c0080d1030300c1d0348440c0d0080c0c55401100c01c030075034601e0640b01d4072007940d02c11610703174008030100a4040d4100e2000c992201c3d140b61614685548640040c1d4004220b500c3c5900134040103900203000344c081d2044400102d20441026140c0ca007078688040980683c0c0000c135140c1400d00089004000c00203002401290710103c1c40080340d041105002250b0803074034420781c2c401c1074142d007040714540c400a980101074040300c0104183c00c40b82002c606840c540000039031a54400d01c03d40d03000c1040482030365007020060002120412403d0201840c1002c0404041c0c400c2c0520000e1003e40c1d0340014028040340002c1e22101503481e51124404003042044407420a03c25007080090018a000d90045500c60710940c000078104400401082080e0010307000701020940000303004c00942002c1203000d0041020000045a0349800c8003225501c0c01450300040586401002194006809008559060401c070211580740d02d05019482d013b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 17647155 1250 17645905 17645909
    0x7080606040c0810090e03070804060201050906091c05130803042c0103030f08090703050607091805090703120e04020304060f0c0201050f070c0c050303120711060106091a070606030c 80
    0x710310314081160a0311402060110301c40d2140e1084c6107041031030808040003030422120f01400d54041042030100042d414005040902241d41c00000e071450490301003407030b05402405d0718038a0707408502e524120f1844140c1d03403003900344103180c0b85444034891895210320054641000d900c40c0800b03e00410400544038034403092456035001c6001e120b0720003014103c000400e000280000b0006083c00c036944d8000d0344181c0d00660150101c0b6002940c030340380c082c00d0203402d0741d42500003420240304002c0203001c0880820039144000e0200202e06100d40c18a0b9154941d1200600521009021198960048000c150641000f80007550f032840c00d03180c03100003401c01024240f14640303041c441d4a0400d105200d0148115518500180503442e42c0106654450750700c0000c0700d10a40342c10020074161020300c045c1c20701040400c000e01c510704100d480a0030a080c40042c103201603002c4001000f03401d60144c50001203400c10410720400121a14414049108036640074100714100140001084400705014003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 17648405 1250 17647155 17647159
    0x2070b0325030204060504120819081501050c07060813050d080103060c02030304020d020405090f0f0102030708010e090a0623090a0303111c0209030a050d0c020108010e091c050c07080606 82
    0x1c1c004040450507012030040780541400502c050001740a01000501e00921080c0a08000f81c217005100104450041103105a407000420740c10a00c2450100e00e00e0000c0600b90900f8154180070003d030700d09a41d0219403180c902003280c0038001c00c549200c01c1c0002d60601d9040b90035130303a8091038030350040c005841c02e100850784a8075144007140001d10110650340200c0c0d00800032125100e0035000c02c0082c20307018000d0711031070041480d080d00e40041000140c20010141c000940c40349080380c03020b80705190581c840c03080f100004042007c591008500c1c03000c400d9102c0800289500d040745126071a10004c4201c1c0301861100041c0914190001a09044d4911a81c0c05001d200e981031300300c210701d000795141060f003038100f051149010b884c6a000f03440c1c10341000d000c84103079601c20b459291130102c02c4401c1c0c0700400c8901c01c8403015940d016002c0c502429003100103201a00f0310340f000e00c2d03035440355030050032050102a42c0d11240621980031518103c500d40200c5d030400ba00c600340d103902c4070820b84041e4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 17649655 1250 17648405 17648461
    0x6010f0b090607143003040308060f040b1c0c120209070c05150c07050f030408030702010311120c0d0f05070e0d0c050a09020c19050c010c0609060f0903030b01170a0c02070b03 77
    0x100703404111700e045a105950660b00c1840300d48076001032041d00505074407415841900d41c2d020f140140ca40c0081d450a001c0b07080d61024400e0f801d4204003030804502c3d0880f480740d403c05000100540c641c40507903500001c051400c480f540d60740e0f0808074148014507074840b1000b070070682445030b03010b0a10058101c0138019426542d00c5000c14110720798910452051001079017080c4032400140d030003079201503e54681030079168a020f00302000180c1c2102304403080b00b42c2e200b01080a04041500c1d10541010352031702c0508022900b400300c07002d0f04898010900c00d201e0309050315420104400404420010000500a444140c1c1c8613400712019400180c1c82200318401c540c2d4582c041d510502410781e01d070340c202000e821150200c1c001110034070480c4000366409500c810804001031403034454581c2d59081d11b403001840003018030f001020b071010907031082d0400c103282171690108400171184a170011130802c0001030304005600f00b60b0a00c1e1281e885500900804000c000300c0d02c110803258074a032501e1050701c2c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 17650905 1250 17649655 17649733
    0x150303050f180a061106070315060507020d12030509100e0304090203090a020a03200406030b0414160902040302120c01090e06010908060405061b1201091a19060206010f0b09060714 79
    0x710100c0701c00b00300c84820521909d404001c0d20780541d0050203030318009070a503294072410b612918181c40d1441c0405000a50310b40400c40802d01c140042030740030f0450030301884120003540155569028501420b80710340c1d4000040780a400e010040c1d01c00d400c2d40502458501540ca040003030300480c980360000d0300d40e503004207004458030b05072007801c06a0341e00c40035000d89034403039454042e822608224000200d2142c803041c1040d881100c54040000c01144c800503940d24258410300054082da01485051a07000311800440b5070380000e00007066850b460a5400300d40d07620001251480382503400130150740030780b2050000340400450718600c501c0c0b8040c0c502600c00402030300c0a10900c00d04c6052903410080c00018000310486070130240c540130702c004070342424000000006218500603500103c608020501c200711054052207400e005008c09880f808a444c5000a80c159600c51003a125204003c00113410b400c018003041101c00c49100f4001310385021600564940c04005043d01c02a0018185182 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 17652155 1250 17650905 17650907
    0x40c080105124b0d0212040b070f0204180c030b0c090102030a0e0103060f1511060106020304060e040609020705030a08010b0304020f041d0d0f03150303050f180a06110607 75
    0xb41c1ca440d6041c0007940d4605003000c40c038a207450240030076408040785420842589032072040440f40303030390070800c0190070764075030750540130340341001480e9641c61006081c0020044010190300303a0304800d03080841c0340154002480020001c0c901c28001a050100580c80722043c003607045204810f981c45968001d4180c3c65161800002d070207042d58050069000300712503c0c4151049408030307801c03036040c14040b46541d219444600403040c41e801903d07150950301d8845183c25031140100c0800c90071480031b0003581d418003030025200c3c85140500e00a020180b10301540e162200d40c007220042111000442d15071a080c50995242c1e40043c0700300e000903080d0300022508034040000c403030045030b00130301080315905410140809041500c0041ea8030005d5060381540405041c44031385901d00107541e940301c03121206140070342212000b02643e1190703007529409100003078005c41254001031640b401c0c00d48850100b010b0703075885540402030b0f0703411803480900010030a401c01002c0c072018050809544d01079441c0c42c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 17653405 1250 17652155 17652163
    0x1b0501110f03041e08030409020702030606090405060a110f0f04050a06020601050918031608030601090e040803040602030c0f0f030703050109050405060402130207020405130b07020f030306130209040c08010512 92
    0x201c00303207150070811080004612206285a030b038182c06102000f01940d03100c0680c19a040399118180880c3c0010b401c000318a418003c41d0740c004070844605009041030384030303588d958070000c0100c085c9550720b82c0100e00005800c010b5400c0c034400d491032182c0d1505c4452828440b0b400920595000300361000c070129405001040c06070507203001800f802c1c60755480b4100070050010351030200c043c60008012810281c1004504070044034000c9070070b25941d080c00d45c00100401c3d80c5074446501e180540c1d0500000440000449410617009a0b01581303a888540d500c1c1c25a12810109442d402c100140b403042c84071640024521984498404114682c0c1c7e410318581644e00c1140c000f041900280005001440e10422003116400e942d8170060400d5260b5000c070701114010b9400b02d10703130800d1b00d98210400141070b10582d8041b08600c041e11402e04085030407540c1c0e00001d001c00d4070920b0301010201015070a9416200c842e50b00030003d10800320310101c00342c00e4000c28050127000f004694035103900014001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 17654655 1250 17653405 17653423
    0x6010308090301111603050703090b120f01051002060a150e0103051c03020910140f0c0304080d0c02010207210609140601090606090506090d0f0b0a0b0103090b01120204091b050111 79
    0xa40d241403062aa46d0444180c1d110080403800d05c000d45d280416510400303000b90101d01103c0402c8807940c1441441003910300300c141e02c02c1c0d118103100315400e03111a50100e50305800064007034000c03401d120400041c040c0c00c24250000c4041400d07410000050201c0001e140044203240c83c41c9050003072290508405910900c401580c12001c00c1d140340c0c0701079129100f0a06402c10000580d8140f01c0200040021503120b2400840c0590002c0f9003403040c90014001c042401d01241085290880c4650020313440e103d461090440800d0200c8207526a00740d415401450986e00c0442000100c032036182c480484020041c282c01c03c1d120b59030010414900d01d110b0700e000c3d074a00f521862025032030002042203641c031450401c0d41003441a0171031030000301494141300410741b140000d2029071500d03c0c1358000300c0da90301a14904050400303251a02040b50f80001d641034a10351051640415440c0c0003090261030300c7c040c01022081e81c802041c0700481c100b81030106a0b0300c26a61540000200036118ad0b540f0031107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 17655905 1250 17654655 17654677
    0x1052d040c030f03030b0301020309010e01180c0e0c09030102070c03060b01090b191b0308040201020607030902090703020a02030c06041101141305040207031209050102030628030b13050601030809030111 89
    0x22a07014004501503a070440200b03482403030041106a8084080b9080e41c200b42d40d0b034540341e0344800004500c00c00c02e000f10242d1180c078a00d07405242c645511451101d0380544141031342c3c5000c94010504031282c0340201c0b022224064000e56943c0c0003031070441d41c40300d81c520055904624000d807500d01c40d072203103805c0c50407a04501103e5080030103a0000d5000c60394a00340001c207001d050344d03080801c00c070740000b026900d9020351181c6080d072800e0b0001a0174843c005000f90b0400d81b6002c002c600507542d59105540020140c0360058403071a0f2610160f00c0c500c82c41e81c40210610400b0100410061000030054000c20300703a9a0340c40a152000441036240108084290313001111001800030f81410b6002e440d45902902d441c280c0e00580200810407103126030320994003650000200070231410049600001c0380f640c41d400c82a4050741c800c00f018140100c1c00018040044140801d03c03194100d60451a02a0400291615540c1d24600040d503680080185c03806942805c0f40383d204c02941740c0c144ca8080c061 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 17657155 1250 17655905 17655923
    0xf010e030a0201030b0f030a2102030a0c15060506030906070f0201290609060a0f180602150705090a0605030910020a0c030c17040e04020f040c020a110d020301052d04 73
    0x5507801075002d005171010720741d04040c1660303151860740e8003040610804c03800390a6140c1442075401c480c0405100301d404c00001c1d50301c1041684591503201c1e09a020480d0084c0403443c3c0010f10400e07850103819076501c150b910440210038404080808901c1500401c1107803264007201ea0b200c1c00990070b035250003040a0000020040742e4400c0d00c254034002d10a14401000c0600c4c09000c50000b56043d009400c6c5000081c00c1c000042e00c0540e080000c54a240d000100728140c03040c50310000a5035003015001100303400c0c1000b400710720001d02501c00d84e444494000d00890800744c0710b600003082c680040342d407a90f0b14842ca681899407440d580c403c0b520258034940d22601010090344040e40d9009060404480c481000d425040400035030101810250010b0003040810b800c2c18010003034840c0900f0442840345140c040040d007416000102c070381120b13a203d41c081801144090000e007200c0d4110030080e42650901c8200700c5001d010f042401c00031600492550500b10582c100d2244c2174004403001000368003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 17658405 1250 17657155 17657173
    0x1060e0105210309031203040605060603040b0103152a0206011e06081f0e060316080303060d02031c0305060111030a080403030513170c0d08060907110a060203010b04050f010e03 78
    0xc2e4a08440740382c0050700c0200c92030480a2004039192425038100704d01040d4020040c0000c00800b03002d007640104007111550b0035030900d9101d41060180c10b12004054103001d50780c05c1c0798110680c100440c030361b0145001804640c2411902001c1401881000005001d410000b24404035004450580305030b07075000704240746040801c203468822002d01303072621030031006442800c0c0d402854001c4000e01040a04102d0508141c000d0510f040020403900001d040383d00d4050040041c000141c0c1d602c203e0803100d0b05d10302a928004641480b4000c4000d1170110003036443c41c052650181c00070f601509082e601e061611142080c03503074484c0101072040f000501804085008644250001e9420007203842507816580a540d0b12500b0b0300d15110080c400c030300c2c00070917284464030003840498900116404d1205003480c0080010b402c03181c004000809020031507080c3e213000c038001c200b1025400d502450440d44c80d6162159004260814800d107441034108519a9041c0d501c60000e50b1001c002c041c0051010341 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 17659655 1250 17658405 17658439
    0x31501090f0b160b09010218040209010f0f090509040b06010917060103080a0525060b03010c17040302010905160807120b04030c020f0406030f110102060702030d15090c050a0201060e0105 82
    0xa4000f4181050140501a034800444c040410b8140201e485000040e990086108450440403007603690381e20640c414480c080c4a40d8201444000040300d0f803405500103500b1920640b4080715030303044507400030505401c00080105c04a2003901891003601c924482d150384d85008003030805a02171010468009000400c0000d140b02d0250000101d18100305091580b201ca048988102d0024444001c0c1c4004212201740b048074443c10701031941c191b000740104181d4003406401c20421240a20064400034002030506100b0f44c07043c416280d00c001a10105840000a10804c2085010f109107600a001d4001041800152001445a0b00004c05203140d510341c1c600b40d400c110150416a0883c05510101181c2e58036445040e01462103110040d55084441c280b88400c40902c01000c0d055501c1201403001440e000410307910981420304012603c0c456042c1003612400e1180c0c85501c110341020b070b40148140d001809000c800340c41d07a008201c0d296440200c81c0c1d80040a205080d0041c030510010715040c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 17660905 1250 17659655 17659657
    0xc030f03060506070f060c08060f01050c0a0605010f080d0206010311060901020109080412140303010e040b070909050106090510080705041a07050601060806030f010903080606090d02120102031501090f0b 89
    0x608454100050400d503964003159956000b80c0c81102e8a943c2d855070301c42000b00c1c51244d802000c00e58a40420036107044400b041c010f60300c1003900340c1032010208541080c400c0030401c0607009a44581c0074001540d4075003140d40c6a06081c0a0000d440c0100380441005602c0018440e04032a0810010b030030700d4881c00d00b4002c5070b030f00c4501d01c94119500e501440f00400d00c9080244018810a07103000c6120303071642001c03540c0e03c48210100c50540c10400040202c002d5010b002c0ba00315410680d8802c9946070001d050350401203550020b500d550500000240e196000311850003243d900343e8840b0100e40180390102c440d80004c94101010407400d2100b80407000038020019561101c98603a145001140d80741c00b480c1c50404d92001002501d114104840380c24248050041d401100000780304580e01560081d02241000741014010807001c140941103554203c01031604139000303410884462442d41f8098047c0d40202c550b0f170009089401d00090701c0d48111252030458200001c40700751582010118111 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 17662155 1250 17660905 17660927
    0x31b0206090907020606010f090806070f170a0501091112160302070606080d020c06120103020d080702090a0902190b0403080706060b03070c0605150906090c0c0a0f140c010c03 77
    0x40c010310410300750742c40e080c0070940035550f02d40081540b840e0010004040340501540c0c0c03010041214030812104400042c2d080e00720b8001d04209109904101040310380342000c801001c009030b440402d0040d100c0e5190f001506880d8149030070b00c00c40b0031a00c1b91400a11502c0241d02c3c1c902d0040000440810f024070000d8170a0318a45809032905056403610000d1fa40d03607400507005900b02c4c8030200c08441d01009503505054041e00c03c01e0a021210085650030141480081d000d1203240c00f1150420400ac1c0031103540c0e13507004020f1070301c41c104420220014070b40a03508070700545607801080942a5900391160031034500c40c031010314160466a8104007500014001c41d161500c07000d0210741d018411018502c61a19580c1c0c0046101d00c0b410b028040d144c000e8840c0c0d10b00b6622102c201025291842d5040e408038050707034185105d1315406104011807084801c000c0d1076002da200c080080015540c03000703000c4c034094a011010b01000418a07a1594080a0a94041001701c0305202c00031340510002c81c8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 17663405 1250 17662155 17662159
    0x30b030f01020d0b09070809070603020702030102041a0d0e1617010b040c080f070302090a050d03020a08041202030601090b061b07050910060813030e01030207060f0f0e07090207031b02 81
    0x1445109041200e030980c0c2101c07141c1c0c030009840b003903401c0260a16150407030b4442c005240010300c60401c0101141c0794001c9000d01410141c0001c0d540c3c7c00e5440940407203008200030180c0d80140c3c00546120496a006050031000c0241806946180203c0004035000100144440e0302001d920f8039440d000c00400703807110710240755201e18085905580c3d038440d441000c1d0154403060200d1902c03503084400c220000740300805051040c04500001d885984000058a4041d54620000c142c01d04040e40f62a205600041000400290204954500c2c041c0d44900368400d404540e84c590700c4407400c000703851444070f1700c81d04440144034404030740036060038802c280301401d000d0b18203494498010940c02c2e071040714140741501e44e80c8020403020742e12250316a0701803100d02150442000071b580c01800f2007424092581015000304038142031018592168005203004030040102040b03800ca02d4010708107003014100d02c2d010345600000c90840600072140c1213541591780c18491900e9298a002c0685880402d907 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 17664655 1250 17663405 17663413
    0xd0506011404090c090608060901061a0c011b1806030203010311150706061e15090b0322051e1603061a03060a0501030c06020a1a0a1b09030201020709051501030b03 72
    0x400401c104d68580c5000d050801d101190490600d4541413500c140940503a41301da25000d41002841c0a12150081c0c1c0b13030650340c4c030030394624103050050f014190406d0301320f01c05400714410905007038201044010304540c074180c0d01c400726904c4100780c04a00090bc0040d107500e50010b900f138100e240182400740801c400c03c1c009030800c0042d44a840464216400101010488010300d0b410752142c507507450010030505144c2d207004206000018005540b52203880c1e0030b40008008186019068043c0c0782c841900521454103104090403c0c581d0345580d6181604004c1c140c000141d442100881c1602c0b40b05982c44a2a086600d1581c40070010008031740e04010355004084030250603a020f00c1501d00a440003503000c01c05505500f00b49460b21081d920640540d401403a1348000180d0744e048403c10301391451200003031503481d0b40c000d030060007a01e11034941030b15106a02030794140c3c2056030074007a02d000382d00b01e0b42c68544504030801103507800d682c0c1600b0034507410100e00281d071080c0c00a0002c0c15000d0156 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 17665905 1250 17664655 17664671
    0x130c09051803040306020307030501091a010e060c0a030206040b010e060a1403030f120417191b080406050403050c03010522110406081b040b06070b0907030209071d0d0506011404 78
    0x210b42142c100350800c841054002061150b400da060003510301400c44860f08004008911307424a04e20444030356101c0c14015502040c220716a03900d410303900c8412101c025a0150b01d00343c9002501c44108840c121031803080e01001164600d000c0e000342e8030a20014110544d92400c103110001c11082c610107080c1d15101c01c010484a4480d078102818180040c5100c0b03804c0b42c1054640400c40e80b16060419030304020500000c1c2099a00300e410b81d205c403881e8105400460082d07410541c8062019101030803a801c00500000d0a03507001c0010030840c0d024505569009022400b00350070303034130251500510741100070007152440218a012220051050f45000c2800110b0720100303013614007541c0404010b0b08140150341c2d10b0041800c4102303101a08484c204065040310b0300044803400b403200c002c0d05140090000074000d110410101e4051600203018511b50b140448005059814101e140242c2740318180258030241441010040321a45c86030181c8116800e021102c40080b0313040c404560310644880350 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 17667155 1250 17665905 17665951
    0x60507050a0c0b0a02010f0b1e0301060305030f0325080402040e101b030e010204050a12020114030f010501030e06060306070311040b04030f0203010b1507030302030703020c060708010806130c0905 86
    0x1c164003c1c4054103c0036140c5844c000060f003120a0004c03c074802034200480138005a9074400301601c032040c60b00c4106c81c8074082002090040c401c40c5c1004003144800107035035040c4180d25016520907560741c0410102c1d92513140c9200c8504503007400c0745c07000c01c101e800801d0046c41c2c1a003101c181440340320211070f4045200b00c0140180d40c441942444204201e01e4000c00c0680e05000750b24028030782c20000d44c41d00d403414000c540500e140f40700d6200b84480b41400320703085a03c6245180040d51540c1d0b9565140d00309500c04401c3e84a0070b205030381c0807074a480d0b0b141600e0751011501d2840b850300140078050f42d648803c8244c0107010380c0c6841d0001c80d0000c04c408680c2442140c068405180518001d1000081c0d51041c1402c449845408500c030b5803030100903190302845c0c0011205c46a505142c09a100d46489405602a02440c00c140d000f07401801304010300c0f030340d1042c6003604807505002266100e0310780d002e001d0342003114190040c1400c20000800d0040302d6460700071540084803800110605807000403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 17668405 1250 17667155 17667173
    0xa14091e040309030c08010204080303040809030f030a05131203050d050603120a0908010c0c080d020a030906050108100606050c0c2209030809010608160302130b040e071a0304020109060507050a 85
    0x41c1c11800b103070802c20180184075003071507280e0103800b0590003186000d0401041c9a603e00005000610b0141c0014011240b030b00c080c440da5140010101c212600ca01c00e0348000b9000d0b0704680c40f0507446d4a0201000503d42000211185002d505900e51500d88a03030440ea0901900c002000c00c1e03010321030000b050031000c0e0541c00070040a1180d65075000803c2c2488285420758000d0000c2204100c501d075a600d0100b00400d080320b20700c600300386005035150002c5400b50050006400f0180c05036103400000680c0c140d001c00c1c00c0144080b0940104101c6403100d0058a4038003498802854680c0990320700b070150b080603000312041c1c4c05010f013511266000c034200c290545030f20341c4c0100e00096a09043c8850001c09003e4036001c3c0c0038081c0a05144035100180c1012640184070184c440d80a4100b02c0840004640c002c3c0d800d0031001d0402c0c0409015030b00b030715550f54480d100d2840d0101407034a00c6944182141d050f02d0003564140c0d03c0c80f610a191400841d0190003141007900c2c00d02480e510140001e035544 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 17669655 1250 17668405 17668411
    0x10f0503061f020a020f03010506090105010c050705060a0906020c100504050d05011d0a050706050403030f1b0203010f1509050c0304080304032d0e1e0103021803071409060a14091e 79
    0x98020b1000716880d1046c0882c1c0741d10308a28078000da04050500c8600e41c1d900c0c400c82e055510a280801d280c94840c00d005142c012554030450300130000242054031a0780c080403040a981c0907808035003400900009000218044040c24000200705020a008600d04900d640205030700413400410401b01c204100c140b21161440c0c896929407051440004000040c0a0a00104510f0500b00d00740352441e10081d00c80c40c0c5c45a1408100000030701d81c00750b400601072044241d26000383c020031102c04148a03040c0245011016080c840c50401c03000100380c0e801c0c2c01058800c41018224500f10344450b65080201d4002800c00c90034860059020886498005410b00381e000c11a140700c00003191401001d07020700a045402406541c0510044030810b1100808400c420310038030340180da4a0448200726015003c901c5c00b10703410f00803010006010f61404010451102044412001b10b4860504201311450288241000d055040032031a21618010082c5c1c0d0380507124403030300b0f44d8006407003148680c018811 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 17670905 1250 17669655 17669657
    0x61513091b080108060703020a0306080312010f050d020619020304030206070506060f060304210504050411030f01080a0f0b0403030902040504060203090d030b1e0a1a0a02100209010f0503061f 84
    0x1500510303440281d4008524940c0001d05040b249541880001521844c0051000d0107044d000500403051030b00c03d5100301e0003440f2407807d603170310760000b4035099103403000c04c1c4240001031b1200c03000404c4030b141040803860354660091106180519200169891200400419042d40418800040542c4454000300b610900c03c0300540b44070320700381042081c803100100c2c2c01c60040d10107204200010741135146030203415065110f40c50b90340d50001e501b00c0c3c180c40380303411250f0040d0825407010f003000039070790166001e2113140c840280180e882d000c1a0756105503c0c4801340ca5a14540d11410200344141e0032190054020b16001c42c2d6200650042019580305417000c0b20304550010401044007001e20100d40503030000d18003404000b040c54001401007031101d680300c0b6801403c0091014540d83c0500d0f0400504d104c40c110401e0038007840e01c0d0399068000072900d0001d4060f200115480a285101311054003405850740e03100c0700d6980d4011200c0b0307000244240d030081034404414240c8828058001003032001d0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 17672155 1250 17670905 17670911
    0x507080f03070506070905010917010605130c081602120d0e0d0807180b0a0509030309040c0306030c0b030f16020a0b04110406120209040f0317010308030a060e090606151309 76
    0x6140383c00c92078500c2c001c03c88010003401013000e0007039aa0042c03114084a0305004600185480541040d004207155440380b5032145080080c5d64140700d10f50400c1c0760f03030b81054580304100d55540c074004407104c010300055401608040c201e0740d200d0180344058882c004c0036050010b1500c03031440c485440c10103074410060100303003028100042540d01c420120003008060518020f9245131011620746070040c0d0b408241881800f18412015850030030649865a0b0018814000c00c3c0403404090001c0c0300ca03020a0b20841101280483c5032900b4404a80c00b945000380d07150410307903884c50200d600d01041181a0118040c07c81d00d0008501c40f80755050056019010384141d100205040104890701c95020a10300034055071554003594805010540c801c0d01f100c2e81045518045c54202c2e0021410a00708a50b040c1e5500044280800d844c0594030805520000f0445582c8405002c140200304981100c5036034454000100b541c204508401d0b01d0043c403101040c24000040b03841e400500d1a034002c1308420b59 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 17673405 1250 17672155 17672167
    0x3060103021b121c020c070306110702060403110907020a08030a2a090e0105040b030304050d080f07030c020108060a05030c0d05100f050a0609050105010c030804080405040207060c0807090b12040507080f03 90
    0xe1104d55190002440743d000c51400b2055142c1d41d49662880c84007800340c1e0b0750f030022081402e0490b012128950b17401400f0030790ba1910713407520885c2c0d084507016450140310881b00040305030380002030811029400041d000e05641d144c11513007010b4440c0c0282026801ca025040c0185da00c4120b25034404c42030b0546998206a042c0322900c0d20030003051f88483d200c0c508002c156032880e10044225400d4610031381c0c0d925050961418900104d11a40001d603c22040014680060551201030000081c0c0b007681d880846484900400c160441240611903060300150740e20406803800b02034245502e0f101c4d0f410303604640b0000c08504125101000200501b81d1103d003046402415885040041e020000302040594103000000740b40c4502250f0050074803171404045000d11010505503001810010019940c6500f43d161003009410a40c0e00400401c4040c001b2034155070140c0c2d105401e0781d02c42c003d0281020300302d42c03402981d488040e000351002d009080323000c1080c040501221303602180301c0f402035039511 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 17674655 1250 17673405 17673427
    0x504090f12020c012a020a060203030a1103010e01123908010c02031c0e0a1101032901030b0a09050f090f010605060a11030d140901060902070803060103021b12 70
    0x100650340c1070841d0000601c40c080c0e40e800c01034202000f0044204084c0d50000c001c02141070703200507000694001c001030400a4080d90010080d4401c01001505118202286405100c140001c2c000c00e488840f9810040c02640004462103135024041c0141e14101c64620f480801200003126244505c5803000301881c0b401d4581800c43d20083c000c900c020041903903078000080d203901882d21602d5090300e500280e1a0f28000300e4102c100d1083c400c4090b1001e0a04038500704804078020403000740420b050010130905441e40014064110308001d910700e5039000d80800450007003ca00800310341c060440c04001c19072001d81c1c411303280300e41c2c1125a100032508008181c00d00e401d07948102018540c2c10164240119207507038050301d050300d12328103080100c980c1c003999150440c051540c03908406e51800090810b9226000b00c0d10f400740c030741e40000b0420309860700e89040071ba2181d18406406074000b0001301c2c489512071745c01418040c400018080f6a4422082c0050034a8400300e910034004c64081000d00c1e0395 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 17675905 1250 17674655 17674673
    0xe0409050717030f030103021908070b04060305090f0c040f1d0307140708070b0310082a010314060603060301020708031e0703091e0302120417010501090c09030b0603070504090f 78
    0x10203401d100a50800d4807012401003117220501000380202180e050110103000c0c40c0303e032500600405815150300a8940680b07241c00d40091042100003814980424007403100850380706030740d900641c098850318186906100140c580501400092640d032407468504000d00401c4101514404002d540e81d03120600b00301034004a070144548d5075400038402040031920004020341203580e440ca11a44035a544521801402081d9110000074090003202d0022058010103103ca90148124444201c00700d03040114103d03002640c00622100307002002c2001840c0c030102460b8000c10040000d0b2400c0d810b035130745010316041a00c1c03100b1250b00700710ba0f58a58541e041c41803030340880c103441d041002200c030751a107042103240110103d012010100420090501c01d0007207280701008185410381e01d84d80c440b10030600c1100c010040d803540d440c101c00811840032500400c1152611542c0e0700030481e003540c0ba0111080d40251070140d00d0b109003000019151201c0c051042c01d2400b0700d0105c040c50219090103055 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 17677155 1250 17675905 17675939
    0x408030f180406210201050702040f0c0908030a050406030e030705070807030b091203040809010c02040c0c051006050121060f030308150a0e0c070201030e07080102040f09110409020a0e04090507 85
    0x201d50f0501c1818880d40c4401400340e11a4040b008a0600411050006a80c58868070342c01a4109080603010b22400c495500801943c00f0590b0312041d01c1a95007850540720301404000400040d4100010414148260040555102c000080d80d207403c1c01030fa9600c0c6406400e41c0550b5640e04403140410510807450103496102501802070105039040c0d00061a186c0310060004004031404030700c14903183d101e083c080d490140d001c0c208109450140b00084c06610800345e04881c14451865800200302075400303001c003250810307140c1c24108840900154070601440030408000340d81c443d0b0024101200303010000c0114000c2e01c90100c00d0074900b803d04040007480d01d02c580901d1141100300440101c41c411694064400c62455482d900d044c401280a032564441101840c07244410204203c0010350080003140c0064680b5001d40e0b43e6448150140c40050300c01d001c40e91011b0204001d080181d800600503c1460f107003901041d1800d0300080d044808404041c0c0380e42d844401c0901c03100c0c480d82c070030000e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 17678405 1250 17677155 17677159
    0x60c0d020f070f05130b03010501080c1309021507081e0301060f05070b0601030e010609020f03060102010e070b030f041e050c1212030103080702010207030b070503070216060f0806060408030f18 85
    0x440b00f410302e110303900115503d10806010344d07034040800340300050645c0642269600140244034559458003000d603a8000102514400d02c00900c241440030128454440b902d940504516041015014852002d4002c0842695408001c1180f4260b4a6181c0958a00750150000050b200d50501c040100405841003141c0c062050401c03402000ca44d004013115400202441d0201d0328103d230035509030150040d684001052800410320383c00341c1c900d80c4042c2d40f00c1c0394280e00811220200400f550b940b0701551180701d550701001c00c0401c1034030190513005079020740100c4050510805000d0340603000c01c8030303210588d0203030810700c0031000701d1801c42000103030101c80c1c00080c41031104c109110741c1c141c8010301c402070402c07071700003000e600b113900078030501c07000355000b080402007840d114001a180303900803540740d0014011600060382c00c003510300521003950311640d14590040c4c0102ca0544208074003400340c940c003440510001a022008000800081e80041c407500d8a4812038050740d02d5490400081074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 17679655 1250 17678405 17678413
    0x60e0604030803060d08090301060801060513060b04030b0426030a0c030614010509040f0204030308090601060f080a0e250e01080c0d080307140d090203060a0b0a090b010e060c0d020f 80
    0x1003103960b016642c0142007110100d4907076490307244ca064180b1814034455055420031754002960141984128100d46050705e102c800000204241e5007201d4550042016060043c0414400b14101180da1584507104904034004140c1c2d07080240601c1000000820b4501000801c2000c04d0010b07008075507200d042818140302060030b040d41d09107240c0d41d804000c5e041010124117001107a541c1c4d04500305240440d0000c43d6103d860b414001c21104c0110b8204806201c1d410001450500c03c00001441c601907540302e4031b0039200c181c6203c0207442030001781c00c1c191044850101c4a01c0141101d48615030130000304803045490a105d003030003020142c0c00001c46400010034036000b40c0760864500035a60740030313401554030b9a60020a803107001d001c0c200703420030143c0400c0601d44120b071940800b0300345000702d04880465641c6078040f0140c071290f001098020601d25001c025100640d00413420307403d4141050414002800c02044154001a0701500c0c146d02049a500d1100d8051090511403090f0314003030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 17680905 1250 17679655 17679659
    0xf02060906011502010207170712020c1c02060705060c0904060503120706151205010f05090604110603060d0503030f0103020f0105070309151103070c0501030c090e01050607060213030606060e0604 86
    0x280d500c030501441450192501ca07000c10071158800e40c12180d0540d0302c103002c44020140d003400010a0b40100c01c0845180080a5044224034000240d01c405a0001092003140c02c030414040d0341c1c08160517000702c0e0440801d0009600040050103264480c1e00140544c944901c030a10403c8255000b0380c1c021b500031703080000d1201d40012000104d034001703a00701e400810568441c014000c83384984da4000011141c03407071450010000190444091443c0c440c03800d0180d51680040d00f901e0f1142903c000300313000d181c1e807003040031418004c02440d0b0081004001138a41071150f1141400c6a00495103c06209000b5006000314604a9080c40c030004082c07a00c1400e0500311340d07000e440b580c114050300390440c52948400f400035104280034000c0000203010b40f034840c541c03443e043d14441590700480d0b0110b400c00301c072002070b28400e083c1e0104035501100310030b40b139900e003a0502c1031507409004180d820b15001c22910f10350341581c03101c00004600c95000001c02c2403520b40000d0051008016142c440e41d010041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 17682155 1250 17680905 17680921
    0x504051e0114030703020f061207020609100203090a030e0a0f03060905010501090608030f13030f14010c0806180405031204050a0b0604090803180a020406081e010207030203071709041104060f0206 86
    0x805021760f94181c0748080c80700c6004001078001d0155003130002619030385c8400c2141040e80424881d001e00485421600d032506007025000a0b80821212016240c1c0407180c2e00300841d01c5602d032110701e400c0140c480c0741100e45941510500c400d080c0c0050741c200b0348903d00743c01080300c00d20640c6c0c0101045d80081140c0da0818001c644c4a114240c80c1010464001c64610074124a8030842402581d00c0070a0b640403101c50b06d8881509001c0b40341d014859460000e41c0851540207050301403082c10010101440383c00c0d000c6040003981c001800070380e030612040c0030b0b03081480001d2442034003880c002c070300400e04040b080c5007031885c88000034800c502a9040103441c60020703c816065030380001c0240085250501c0c280c409500c0d0401960010354040e0070001d000410000118005175821410250310170040c8404c29024281d01c1124001001130b80708000e44004030f081c0705c1101201e1101204030b0351070b1007011000682900d401280003d181c01d4005001c000341c130380207078000d551116180040c1480d8a0903000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 17683405 1250 17682155 17682163
    0x201140a0f110d08010b1b0a030e030c040b0a27020a02031902030a0804140a0203010c050306040e030903120c0712030305010603050a0905152205060106090509010e0601030f060504051e011403 84
    0x12603d000d03044042058401c0707030f0b1101204c3e07c1d5400d41101302d44100038030f400c00410440c01100214041c1c01400348d03030f81c10350904d8052030740e0300d04025010f203c0d800d141400c0c080c03441900c044404040103600c3c5503500d007034420f0f00042112604690045440c0c3c00740d6941d41c005401e00e0003030601994020050580540e800c11410350b401500261071602c40d0483c00841130500040c144025072651a04001c41c1d102d681140265000710380598040004103a0464284d40d00e10030b0850413503041e0b10010045688060100082014994100c1911401c0d680c2c1c000d42040c5681403501100803d0726900103218243d454440c20364070400f100001d000105054440d1510740c0e9189050b1410711801c0c2c0c1c00a4802c00a003400c01c0c0924500500c1d0980c00b201d0b0b42401610b030710081c011280002c00225000a5900d421292a0305031107c11040514688400c401500104007480046009a8a4410000702031b80c462180030b11600d0000004103199841c000c003c1c680050503040f000c4591140b01c4024503d850001d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 17684655 1250 17683405 17683409
    0x10806090d030c0509180a0506031911010201110a080a0506010804080909060105040f090f050601050901020d030e07050a03030e0102010c02030c070b0d02040503030a120509060402010c0f0201140a0f110d0801 91
    0xc140080d01c820030300b0f021500d5100308a403203900241d41c010300340c0441c901c500c000c070320920030380701304001603120002016214522614400035041ca801e6498001c203046032245e0003810014000041c4615442042d01003507081041c103440498244010018400c0c001e00600364052003d281c503540c81c2c41c0541e11540c150090540d968014280d0b0350000d03650f640100d0480340540348000321000d403c1e9403800c403140a442d05030800c14605091101140b403d50040c000c0e030f9140c110580140a0280d1149400c60080c011075881036268803800320002a13a031103c032102c8010b0b42c025030351075a600c05400000390030340d020300c651001150320401c6520080f0002007031580690307156522655a400304501020080d01444c0c01042c3e050100040c07050b40e203500907941501051080500780142d43d2500d1008da10307036000311000b0f408502081901d000190003542e1703007c01284141081c5000645104d5400c019070040d070840ca0201d00700030228400c094111020070011084032004003090326078050000c003429818 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 17685905 1250 17684655 17684657
    0xb06030f0a0609020414030c0a0509130501060504050a05060103150303080106051b070902070308070c050a11040219110c0618010807020a0503070b040309090207030c080c030c07080312010806090d 86
    0x640c010914610071a00100000c1920140964607140c490040014884c20f8240303c40c032074441c4003c104014140a4800400ca0310020411000c680d11042801c031844d0060b8030803240c1e550b071400301090b965a02d200b0180a90003605001509142140014040368550b070045400031501900800000790f0105616041d00c0e518039185032904400700305c42c0050401820000389a002e08080480d40c80d0300d5034040d0a403940a6640e10179a41c40c1c0540c00d5038624a8000003034440c0d000702d9800c3c0041581600c10704404103014000504c3d209071141750351b04260004aa01000400d1803c4840385144100801c92220200301e58591410481c4450080000030010540c0e052009480008607a04c2c024044040c60700e8104060b00d41c0c6010740d25160440300e0b0100c800320081a02010042811281d603c255800d0541c55201d807030f80040d603a1900ca8a60b00146000d01240c8005c0014400d6404248505802007139108011502d40e00c84407040409110160009a001d074040e10420030b00e084002080c14802ca0702d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 17687155 1250 17685905 17685931
    0xe040b0f030c132c06060604030c0302152701030e030a0c0b1503070b090102070f031a06220e10150324050c0901090602011503061104030501050103050607020d02010b0603 75
    0x10b05046001800210084080003000a00000e130944a01e8203414200f0042a05858142d0f6610b401c10001c0e000790300014008a0201c00e09000606003206c1c02151041041000d504144100b680d10191600e50600d451008860040c1e24096581501507251240d00b280c025500b42050080c0c020401c0e0003c20001e02a11200004a1080c08004186c83d43d1450050113451140c0e403075500300d40035030341b10b8801c1d9801480382400018103007058241950aaa0380481903540c23014802d42c00ea8405c00c0c010348400c2d40709480c5410300c0c4003549015208900c00d406008081616032005030303e10300340f44400e0b4140f0b00c3c4a0506c0c0107009000e5103492000142c03640560701c00501c481c0c1150340c0c0c2040710f02d44218a9441d10309070900401507100d501901c0400c2d000d0b40e440d400c2d191600012800d032005401d0414908458a10900000c1c0c560b0300490f903107940860010f4103003603490b120030303094420a038415500d5800c07403010b1028603981800000c0700441680020f001e50300d10500400e11500c4000d00d41d50f400c02d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 17688405 1250 17687155 17687179
    0x1e050906070204020d051303180308070809040b0301020408010905010b0f180a090501020a080103050c120706030209031906021b0c0a03030806010c050604030e0a0608090601030303090c0e070e040b0f030c 89
    0x19903681940e40001c00031030304021b40d107840c02c0700903d0002e0186098022903d840140102d2110f40d00818040e84d03403002095043c19410381c2e41090701d402140c41554002d4840c68210071580703091003c0e2009100540010070b010701c4d03a092460071101b0209120380076078224285840142c440c1c01c0c41210074404000a0085951050400402801c00c00401082075000240a4240c25809800326060305e0040d82559040464403040100005000d0401c42d031b19001040c0400c4102c2c004c0d0701804000d8400380036182c200080c0000354085500e02c2d201240c2507540415600098595811411101e40c11300c0c004003841c005210004523a959141710060400c26640700298181c0d200c1c444501c0b030568040d089500e24246072801074039402e482e101c12409081b105400042d03540c4180e02507401199000701421003a425618110058050980182c8004011100014041c01d805880520429a55581c24041c1c90700004200541c0d0399159003d2040c0c100403008111642c01290142000204032200c0600c06 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 17689655 1250 17688405 17688409
    0xe12090105040906030503070c05010f0f080601050d02030405070e101a030c070b040303062103090312180602160e01031104150b0d0e0c0a0305030409090305040902031302011e0509060702 82
    0x88215005031103c9410550000200400000905000d42c03142503014503468884004489018403c0104000684d0f4007441150305401000c0264000c1c4c4180340c41c1d442d2200c01c814400c140e13441a00e00301d5055005080c01c0180900c00c40a403600f20b0782c008040b1308070070324003010302d1203101143d402e1101c81800000420078a1307801c6030843c3d03941c650010300c00d280b500d03060901400500152203030555040c00500c001ea40c009102c0001190a5416200e4642d003c2c00c5413550f00c0c190040440c2107040c44001001c4441d600402c001907401440958001c18071107641043e100c5450074158450070782c1e8076a503c018000507022164031031102d00240c400003851000e588038403029005903800406600400074134012055040c2d0441c00301ba03071a003030894841001040c140310180740c0510002e00950000c0c481800215102c0d0402c00e60036010745009401d142e200d06402c0304991050300e070311f0034030381e803181042c1c04658014986070150390021000d44054840c0010190085c42201e01441c819400014244115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 17690905 1250 17689655 17689657
    0xd1503060f0c0206101809050c0301090b16020718050402010c08040b180a03021c050705180103030305070201050c0301060309020a15080405060901051506090d0f080406030e010e12090105 82
    0x640c0c00c48400d01c029000203032114018038466818400501440c40010340c504031420086048035202a0300d22a20200e265140f00245a000d40c00c548a0081898569140d6802d020b440416030003565640d4403420900950100f080f44140d251007550005c00d401c200d215082e0011140450b0418400b1890340d9a9100480f050641c140d0000c081c150b0119020401d01c0c021000b5014540c0050420080d550b40d80c020405540e066200c020f45c00f4000103240701ca0012040b80e00e440840c03281c412603c2d12521030380001c483e1108091419074580100b4010024590325000309500890540000c01c43c40c14035600303107180c51005005410a040d1105a0340f000c43d03c81d080c0d41c81c020b010060303c0483c000c140150040001c0001d0b00c041d1010321813103000c110814810b204150241d044800d510a031540e070310341030003100c1e049050207542c80400c0b940494042600c08512101651064100d0b940d5141005170103000c9400300c0915082c941e15021011816000019050070000400314865407980e07021070048032a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 17692155 1250 17690905 17690909
    0x80f040305120403020f070602030f09060a050409020c01050402011b020904120c080c100b030607080a050c0c030c010b0111010b090105040905071a040305010b090601051b070b0a110111030603030d15 87
    0x70050b19a4108000e25a010911100401146084e1104250ba0b0381c8126524021500d03521407555040110020a1034484010040780200307042940c1072540d12020041203803c5a01e80d007481ea51600200720466038080074020170884106550070b0445172a8001c1036200c0c0000b4030003025501d2007180c2000c0305004420380810f46520525585ea40c900c4000c440c1c1d240c40c200119898850300701b4401401d1440c000ca54075115001c2951821540d648000003100030340409091800c03030200030003149034011014001001c070f20091000105500a00d003000501c058040842e080e6603925010411150750b48112460741100c204490202d200440c50910340d092100c964862800040c212110a810743c2124010380120b9000344020044c1c20150303030070720410a804403801c1d03001402c00c201d000c40c45540d29000035030b030540f0320381107546998441c00e135001c05520001801e00481c0b41c0c13540100a0900900032000d00542c0c5142090075800d2001c0070950328040c00645288468495032201e060701e60441c0d061340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 17693405 1250 17692155 17692177
    0x504060f0204060306080d0906050a03020904090c06020d0e1c030305090118031707030b1f0c02032409030403020d0305030406090203100c030e0a02010509060a0509060c060105031507080f040305 85
    0x581c82d0355580c8060020101c9120350521406001407000d0480d028624400c111503031511080d2504030009c0c1c1c21002540018402c6038040c0c0c2e91383c00710707020607031802c80d0300003a01042c0c0042109500001010301310050800d04a441036204a48080403000e0310364a10618640c035040105482d111008814007501d10032080c6090038055480d11f006055010140c02030841080c0c0c13643c6080e860311a02101a03482d50741015400c02083e847d00071191034110075822a05c8000c0c60422407590b0180e000030f082c10780c0120070100000211218154103800c2c00d00f0690401102402145058559400300d1115035402e2006030a1280100004080c000c4039003046034226030050940ba4000035171415031005000c4810800e000a20b010f000900d06880003a0080107103805031105800c3c0384504003005a280e05c06418207003080340605c074808007511400301800e10140b40d00f015083c2581000305040c600741c0014500c11411a4401c2441002500141c1064000e0000b00070304003582e07120b040c00d40d01449481e400301c1d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 17694655 1250 17693405 17693407
    0xd05030304030f0f03150b03040311060c090a140f0105071a0405100506120c040507050f0f0703020f0307030801030f020a080f010608010c0504080601150c020a03050f0c061c0504060f02 81
    0x4101036002c4410f02c0b0011203a03c0320304a03640c66030811011100c003910b911041c50494281400001e445601441d0700510900c4d000b161150500c036900e06040040c0c55128102c00d0105110b1500d2405401c00740260204095002a240c005e00c001030144c00820600e41c1403180000303a040034005940d142d0404400d450201d41090b00b86480c02c29620808440000d4600e40f42001281c501d00d88182c0070034403051038400901a0340080d1013000001c10004c0c1c19075007401000c00c0005010440c0038050609504180906502c4800904010381070120740c074840c41850300b04000345030009400c026200d054030b410075103d055000716440800d1119500d508132042a10030503010341140321054001006a40d01c550007845051018901600d4a00030750203040c030300b0f4000c0c00060050201070801283d14640601d03000c5c150f88840e80106885156981080e0b032103801074203210500310010460b00c09904010743d60b59261054040c820360781000c184091112281e240e40110382488260342000024a03039404e011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 17695905 1250 17694655 17694661
    0xc0510020a0302040302061603170f06190914010f080606011d04060302040501120c06030605030a030528050304060b01050301060509040b0301061e030506090102090904020909030c070b0c06060a180b0d050303 91
    0x2076515888c1e007011000074060a003500032248224001a00a182008110105485034010803034510001e000406c080c44c40c0c50800a0484141d000d2151506200d500718046941042440280441035400400091740110288041c99a1051200d81e05034400825031103000c602e0340010b00981859400070f03600900307240001c550aa24020346100e400c2c8116078040c1140c2c1e0300c0e14140c1c140e800798440c49134190005040940400c0c0a00000c04003100d0743e0007905071020038004c4051014050a480c00d0001c1c00200800041158500c0f40042941090801e18155850460004c00610070b4030b1103280601d80711150400715840942100c0090a00102d200071406c440701708180c1404600d00c01650b04c2c1c0308020205008000600c04c0307802c0d03140060141441903440e9001c0c051110300203890f80102d03200030468130b00380d24404c1c03140c0e101a185442d60306680d0110911524608074004d0b2400c0d201f02d40062003000361110142c8000c26141c042c940101d94442d0110000310040120513019000380000010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 17697155 1250 17695905 17695927
    0x120a0605030f0705010801090b0310020f0307091a07080c010e0601090b032806020705070305031c05060f09070f05040f03080d050106080906010308030402040f09050c030705010c0510020a030204030206 88
    0x4001900d80940440e046080e0a2080e1a510103551080714046030715031005010a1000d07411010b5485006030440e103540c01101d03642800ca9110b440c48540d02140403003400742c1c00b580308062000a05000c10250b500b03e07121078100c40c051161520003030044400262250300300400390403191540700f1410135200301d907a4854500000e003981400b2144a1700924403604820b149440300d5604021560150b0350030b013400c030791f100740003588103c0050301d107441481c1c000800640d08200400e448900303044050452258183c4000558001610306031090382d540c80707482e41c26114141c005600001914000780816403901094400340301e143c000881d0f907184104003008cc0920b0304d004101c021035400c400c020507070b039034001128202c80507901e1065542041d8010008101d054020f160007074001040051498482c140c50021601040c44c00c84807030304458500882840d05001741c4008250a00702850405010394a8907204e0102c5050240c3ea40d5000c500101101d100b035058502959001c1c108559400c02c0c264 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 17698405 1250 17697155 17697161
    0xe0904050a0302010e07060c150b10031506030c080403080a0605060d060e10080a0b0702160e070306170706030e100603030206150f090402040504060902030d05120606030f1803120a 79
    0x21040c1c003d9801c24103d40103505000036004200c40d8182c1d902108800c0c10394800000400c1c4207210303032200f1f480c0c4080c0c0c1c0d807030341d0b8482d802641c0e0003864400090b0348444030501c1000c0310082e40108103152400403c1c00c1c003035402a0906a1042e89460400d04554803c4900d000410142e0400d540010002c60855250703615030744040d040d00c188050082c080c0d0f4600c081042402c0c80c5009044c015000400c601000600240d40d06030080c400d80155003030f5000b05c040c060346410841c1c0c4005030211202e02031051140d0148070f420007038680c82c0040d64400f80c0b201c0a4954800c51031040504069642c0c2d000c0012020601c40000710601911060208a969041c002e541e50f90641300c104503004102e503891018039225141e2044408098011f5919039a290204401020f00034419900076450398100d000580e4103003e00082c2488070744030241c5486070402c6041061030014145800354a0030400d111107403000e5298168070052407940010040180941242103025082c0e41024844400c001d03c001807034550 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 17699655 1250 17698405 17698423
    0x180d06020313060518120f0f03070504031b05010828110703080106050712030c02030c0a0507060e040504020607020f13061d06180f070507020315060901080303040c060503070e090405 80
    0x1940078006915024802020300000c440140340b664032001c0403c0030b004009018010500201f194142015021143c0c1809076208490550009174002024010020505d2339082514001e8480740f124030306103400600190710203850b450b400002e124840b214906081020058105241d50070b1100f0410526441c000d42c101c1c00d03003180810300b514000b0a2081c41002074900407500b028010308400d0049005600070241800c0020840c0001c1000c900d050702e040292680503071003180200001441c101004200800c41c008091142c0c0c10001404003617a5240c05584100d07404442c00758940780070300c0015406810320840900898108000041e10345c488080e0b48524001c03920030b0300c0380c42c0d1b00e004c10404102d60303070006400d10380c600c0404100415500e0b81116404905410aa4501030894001070314006c0003260170013007040580200085410402101401001c000c801542503041580d9400c800c1081e9000301000c000d40400020051031244c04040d4950070702420740031803418a810034039200c440700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 17700905 1250 17699655 17699663
    0x5070902040f0b07030507030c110d030207030312110d0e01150801020408100902060307141605030405030c01090b04030f02010c02040c0c0605060603061e03010e010203090d1e05180d06020313 84
    0x314002525010003000c8418080d8546d448914214556809071010740b071040095404484149005245840e1941818275150203900205200e91071843d0003000b105070505604059030920501c0844000d9080503240a031000a80c081b80b0256a07044440c0108141c966243d0b110180000024810f10198010000c1d03960030029124074240c4552903105880320368200035041002000000c2c01c4038450780880203510b040c02e01003468010004810a0311000880040d41c1d15080010100285d203401c00000703030b5107542030808001561502541c85550b01480c071002e810399540e50121021a80300301ea45000242d4002e0041040312072411006150700030a1300e08841d101d1800c1d0200f0002c0c500201a40c0c45510000d0402c1001c42603401490114112107000540564a560040112071420f001462040300808001c06900400044c01845101e400211342c18007071b10054550a02540807044400001050300c8000124040e000445d0205600d090003601451000c4103101c080c1643c2e46104407410b0203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 17702155 1250 17700905 17700929
    0xd0303201c0e060c0301090903030615090509010e06060f1b0307060501080d03090203070612090f0b04210f0f11010603050610080303010e0708060d05010606020c0109090209010c0314070507090204 86
    0xb19048031030760740c0f8098650105800c1d040c00100b0190710a03402996015200c0d00c0c02252a07591010b145001514289402c0007041c0d98160a200605090030000c3c014203a405440d0b08604011000c00d4035032003810704641144100150130115152440041c400b00031205c1c0803039950b4421070400074010301c0280035443c1940074012103024110300c64020f00c01803e800a01900405140034820b8802280c4440c001c0e01c8161580403080216161810403200c046c003444045007249440c0c0380c1a044585410450703104120540084c50001f42d0140350041060b1183c02d181c5c01c0c00c0c0040310709686115042c0b014000541c2840700c04030401802207091801484191000d5032503540f91000161603000034011141800381d20b01c0086d440324031030004907800c144007030b00300180714810fa20342c1420740c1e0031a007004015a2105c10003c8495074040c00350ba00524640b0011400d248480000910300055079401030100f01045a4107010742058604540071168048111451150349503004406508240300d0f140f01500 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 17703405 1250 17702155 17702171
    0x3080711030901140a090302090a02030403030b01050304031706120105100807050f010e0d03050c0a0309080d03060815100801150504060e01030f0f0c05060408030d1a0d0303201c 78
    0x840007065581c2c02905844e018038001d010415806640c1120b040c2c00104018072034000056119150503501171071102da00582d607450142006800c2da03003042c10441c100314040040202103503100c4801c8401e010140100f9403140c507020b0028a8400340000e0100182d4a0302e024800c080300b403141640111400181500c041031f90701e40c00c100007109190115408500410100803291030080640c0032110f01c2070070701e2400c2081c004e11840c9840e21340300c0e0403000700f03a90f42c10900071100100a101700d41c1107685804d103c007608050100392502160808020800006001b09076040802d64040c00031304403860003041041d441c1e004a4003004624410180124176004cac0c04241c2659808030740e03050f40d40010300318100041303030350b100007000540043c01d48002d10840ca011a6580d141c500500c01005407070011500d0f021410030310740849003144695500602400045034540c1c55500e4081d0403541c05080015600d03513007140501259181d5a01d40e01c2c0c40100144000c4400c24100c2d03c41c14924542c081000101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 17704655 1250 17703405 17703437
    0x102070509010f0306051003140a030e04110909070e040513030e0603100b07060609060303080109051f06030c02190c0602150903030c0a050c0601030b0a110f030708070207080703030807 81
    0x70001c2c01a10b0b11106400018804142c1d03e82200e03402c20136002d0010012680c9440d50120a9200501d00700306030040021f0300c00b03156024070b05428040044600f000aa0840e160b401c4003881111012800707440000b00155400d8000c1e070303008041180162051009162a207007205c034a0b07003404411004030782c4c0c106000405060800540384103c00010b041402c49050100c0600c294003d2042156819100d43c00407480c1420760041100444c80307502c62800c01c0d4140036a0300d050361001481100c80480043d101c8440070407401e000d00c01c940380da040003d10400b90402c101c0c00e00303500b070041410074510300310440100152008460120341c183e909542c15403041c0f0f505640e001c1800d0b81c040c03126602c28000301321640a541d0040ca030840b43d40c24850724003512104800c0c20500264003d66007614010304110001515005450b00900302503c00c904e420010442c0b030b6580e02001e403030a003c0124020020300564000c00c109409003034030f6401c64100e141d0320301d07005045900855001001841d41107621060b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 17705905 1250 17704655 17704669
    0xf120903060103061107080d05010e0105030a0b0a05060a090614120303010e04030806120d0c110103020a021002070219090e070501030902030c010804060f0f090b0108031c020705120309030901020705 87
    0x5008010302030035059207140c450102034841e100c01a03801c40020840d080002d40c4030030007010700f0301a140d004519903140222000401c030050b03100318065004400f40c6000078104013200d65000712580d100203030640725032001c100034507465003007828400d14106011801c5031690900d5400f05004a50301080310a40801c45a20790000b8400d18088100510100307000a01031104290f00405c090f01448000890201c41c5180c41a100050400300e2400d80110003440f25032014000101007e00b401d40c40d04150b080004d6072980ba072459002060390100b00c400465882d40451921040f40040300b1110b591500b0904004040c1003442c071744188103821000503154004d0041c51152a00200908001d40440c0010346074118014002c03109165a0710700c2c0d9150802901c80d1960303180c4181c0e4005168082131030291041041030300254201d9000340700528589903418400052500e00b402c000d604d0762582d01d0071174504000000101c04155002c030401480c1d04000014041e506426821100615690818800c2e6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 17707155 1250 17705905 17705917
    0xd02070c1a0708070302010f02031501090f06020c09060301090602120f060a0311040b0a08060c0403020103060e0108031b03090a0303050904050f010311100e061204030801090525030f0501080f12 85
    0x10300c10302c68030700400e0715032002d802c0c0030380a4000440d010381c0025a072007c81c3c2c000c03030f8203085190441110060315603014004002411410420b641480e0a18001950340c0c00c400555505ca821004002000d030384080d0090441181e21020070340d203e800300c2e0040c030525102158100014004040020031b1846d08040941c102ca4001e6a800f8040f111401404090960305204030707000a001180014110001c22890707201e0001c403d40715480320306501c001016280190702010690126a006100740400070086910a0264400820704031b9201d42c0110704500803086c0780c95104100203400024940c02800038880324008580400a580e2440075600035804207000103056000d54212008207418411440d161480240c20240035a2600d44c0000d09282d204031003480003164120203100030076401403d410b003d005180000c1c0058580b402e4228800317211042c2c084408919101d8050b54140a644044c0400c140641d09114540e118841c01d86e0f14120f034043c664052090f0003910f80814030103030035599 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 17708405 1250 17707155 17707199
    0x501110718020325080108010f05010f060c03090305100209041b020703020f0609040617010b121228090602061b090f0102070b0a0804120813030807090503030d02070c 73
    0x704200d00a4016802900010130b40032603e000042c5a001414084824054241096551785600c4d81010450307070030741da40601c0303408900c0d040c0170051002640b0200c0120039110b8500d400d0004d500d0505044a040183c2d41c0060070f580240c2901c410515030700d4000344022101550184210804000e4640c1d800180e00c55100058000600078001480d1402c0511111580142a00e0401c140f03640041c08465031075010f00c6080c0084441041010403c0c0920b421030b400c125041c490480c902920542c0b02c050140468400c3d810004648a03207440450000000300e90718601c484800b40c140c1c00180c07801441340036aa025114120008031044c03454400c13080c40001d400c80c4139050403401c00038060300402c003e000506600403070202041115641010702000401650341800b50700b014108005132241a681c0c3c2c00030840141c04004c00c80006040d01e510b1540d0601d841c900f140e441080c2114810095000f26601d4017001a440c45421865005072601900903030404041591341c1c1e040000b481c0350200411 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 17709655 1250 17708405 17708429
    0x90b07051b040b1302030a14010501050301060c0206040306090f05070807050f060d020706020a09031104050112141509150604020c0a030c03050f07200f0f040908040e070905011107 79
    0x2101d002904125441005800403856100c070100089000103005000780990350b0110070000081c88038000c2d1011075019105406030340d418003000070640e11050041c5018441c00001e00421521440d00b210300454211004011032200c600e0f040c288118080340585491040c03040c003150b080380100309407080b15401080704408c501c041d800d20005822220006015560a1002c04003007405170004029452003691500310751402c5260209405800e001a2400f070751a100040c403004480042080750b10b034000c0c142a0505420700d140516003a0711030a0f141c42c0794a080e080c00700b484130010f013500c02e0380441c168580c40c030f80c2d5103c180300c00c078080c044252301550b106105d0103010a0003105040100780c000c1c44c20903c0c0186074401e110a690281308100d8070080605000b481c401d06820110136840c0089920145160580001a86412503144901d00c00e541c0d40e2222000c01c440f42c01140c00034280d030302c1840c1844c60b10b0080940440b07210f20449020940003080d1a0100d880450040f042c1c6010030825 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 17710905 1250 17709655 17709673
    0x3051c0206011a04030501020c07080d0906090b0706021603030203091b06030106050715020412020906032b090e04063c0507030f020c0a020310090206030f090102120108010b01090b0705 81
    0x18800e9220700002e40c0c000c0d0b000401005c00807130002e00080c010084c8500080254500d04100180703401c20846a500c01c00c0032416041c055180d0201c240011150381e55061074540d10142400e5000317109024501c0041c00714419a04209501900a1441042c042040d91801c0c521461001d06041c0e04030108e660080342000107000c0280108043d0030841d004102c046c40d10030410309110220f90080d00306100d24480c0c40e00d16011803400c0c1c40c007564001021b07000f91176400d800010645050b544050a500c0300b003407084c1c810b001188612003e1000b0300c00c40101306001d040c0b904004004249050415149142c1040140b006626820451201c075810211003070100035200d245e580140000340601c0101515000540341540e05030010b0f204000110011b40300709181071041503e020741981d4010b04003420801c4400160b070303500041c5d913400090151924850b030f0725000302600910030410070a09900c801d1780041610b100562001c1c007000000e80303e00b50382d29111481c1405e02d004015000305564030000c02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 17712155 1250 17710905 17710919
    0x302070e070201060f030b01050a0f05010c030e01020f0d080f220f02010c02060f0a08010e011203030e0a140a05120f0d0b18070f030501050409050d080712020f030103051c020601 78
    0x509079028419100000d429500c4050035001459030b41d00c1606c41c6910180148a20300c0c0c400c005000525161914018441c80c2c9000600350481068000e424002800c0380010280d0090020b00d4408038150182d4105140c80d0102a04000c03064456494010702e00000458a19281000114000ca084031104141c000e566840c212100449000c83c1002040d00d00e800058613040054082c103030381030100945604582d40c0043c04140305920000307000c6110001000101056220752220700e0b0036160201c1d02207210300042d0314040c0441c0d0010001000c080c1d40c1c00300400082621090700b880f600541d01000219003100c0e100b8024141d040c0849a010058064100c4844e4000c20441d80090718100c0294400c40d0300c01c2805408031941d10101c1e9034031036800c0801c1d0b4548500b501500d01214108034480c220f0700c07816982c2030039a8000301440000c0d00411000c600400400c500160450403d554810000d00d8600b150740080c0b004031030703d1054144200300e04504560003a8440101c5d8003c00c002d0b842d2502c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 17713405 1250 17712155 17712179
    0x106050304170d0609022d0a05070c05060a02030705060703060e01210b04030201021b2d0a0c03050a020405011413020901030e2d0604080d02030601030618050403030e0307030207 78
    0x9014080b00004101d0000000380e14001d580050050708001a218282ca85118500c040c041e070710043c1ca49000b00c0c02842408607103040d11240304c914609641c5880d010b00d880c0645040b190845940300348042003420038694000700900300310b44207105550036031304c459005800307940d0340f40500c0200600950050105074005401ca800c03c03041c80340d500d4018981034589090801040c0c50980041c0d4000900c035171310b142003106c142d04c0100c0c070304001c1401403a803544500c5650802c803e07104200ca640e40c2d11840303003207040008280081d000340740302603140d9a074a04581c1e185c45e44807080380620300b480d00021b42e5490401d07200d0000740014000d034080184881d50341000f98041580c40d0b041c55503030f6049560f411810006003010101001c441100c1c2c4180c4480d0130340341145003801c84050380c00107080200003901700c2d05980f4035000c0c18002586940b41c03071005130b0203013216030005032120400440030128030400380c110320302941c0261010040c0c090b0910005403640f02c2c842024025911000c010011108049 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 17714655 1250 17713405 17713433
    0x30e070e1506190314010f0302010518030f06070801031104020301060e040e10060308030604050109090804150e0405071707020304050d0b1003020406080706020d030207030f080405070305010507021e060106050304 93
    0x2c1c0114030f000140504002e0b0840c0400b0b09100295481020000344007440b0002c0740544a030914011200e8951390000703095102d44511401d041080200c4801ca03070b2004c01591038591850400e90345103182000005111810900c0700b50350b4003200d00c4e40780556040c40e100301d80c180c8440e80d40b00c6040508031420300014114141c0d41c042240b10301290180030300070030310801e00654840c00050766241050000c00040d1141a080034070080c0c50418158001004801203c007120b00070500251807495160040d80e455500461143d041800d000030406020750000502900c8002029102029140c03400c0c100d03903d00940c0a43c0d42c01c452020503940c04502c002044650000e484078844c00c200b81c0f20b078041029118264000c0c1c226611103001405485c4e018054110340354854034046051501548000f04800d09030480003061210b810081002c0c8042800241c000d550000024441400e001030029179480030100e016070020a4414007110014000c25800e040f84e280355612415611591200d0b03103d0b001030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 17715905 1250 17714655 17714659
    0x201050a0e101706040c09030b0a0209060a031b0206071d0f031002070314160b060d0609033506011b0b01230d0203070b090321030601030e070e15 64
    0x1616052205a41d5100c2c0d10751445500d5880c110842e20b02031440400440103000e06214030700306007003e0100c50b4030040860480341c1100c0c0c41d035205d840e407110010082c070544410542109001480b4400c40342c140d007110300b00c178070584410198428000c40803601c480d02504c0c181d00042c00b242c48841c1c03640030048040c540c618010041c4038030250300c0700040c1c601030402922040558000c01d42000340358115100742c1c50006904503491800d1101e003410422004000001000b03401510082442a150a403040c44060303031081c420001c1210506000d04103d00301c00d030511600301c91200c0e81500803584041d10807600301c0c514100801e0340712000151000c84a1414105044241565400100f0b4a03d18420300070403070321200d580c8d45006014540741450860064501514079003046c0801601c00003000e0040740e00910100e1740328440e1000181c20034290300c0040c2c12800501043d07128070b81c0e04500441c081d9401743c0b410025110b03114029515020329100e185418102c04000800100091402402403000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 17717155 1250 17715905 17715917
    0x90102061906050a0f0e0108060103120c0317041a0c09060403020418020916030b040908070f06110a0201050906090106150e04060f08010e010b0301061a0c030408030406020f0105060415030201050a 86
    0x102c10104c1e54101c0580d2061502c007550b213408100068400700c0541c05004540041c0038290b045403034680c4486021566901008020b103203c100b4988129403a000610100d415207001303040c18203258038005030141d40b0885d1200982f01003102504240c00301c2e8086d16001c1d120604081c0341d6002c000040100084e00711a2030003619101c00142d4480040d140300e0581328000388030320074140320014100c1c0c981d2004607000d10703e80b6110901007440003082d160ba455000c00c6100000e510313454050040c02001121502c1140042405c0e03200d66019045544200e1402c41101c5156580c2001135081c0e502c2d0f48540c0181c803405409040d6803a200f80c40c05140c00300040d0021940c10f50f5085050180c04040e40210016551264001c4030181c0a000d4408040001c40081c0b104504080c24910131041441d03400c02c1e000c500048115001c0c0b018002d450040c5a0b00064a8513181d69440194940080343d1900c480c2d9460000003600c1e80c80c09100c1c02c0c4441400c0328021480c9403c6500542d00d070780c0078032591001d01c96 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 17718405 1250 17717155 17717159
    0x3040302060c060f09030403200411040f0501022812170a0506091e0a02070303060512151006020c010c140706020309010f051e0703050403120305040215090102061906 73
    0x101d020081072214a1070000309801e14000c220040c8541018001c0c0f01d298104001c2003011803407000800c1c0628140c10101d07040d2581900000e4010038401c000584405408140001c4040c42d00c401081200c2cac0a03001d0301c90501114401105040c0911039041c040ca04010000010039100c9850000e03110340741c1450141050501c05240303540b5402c0701d680340ca440e250303401c100c5203003840e80348550403868a0304c03d04807061081502d8044410010044030010b6400b08401042c0761107504080b00501700034014000c104410034042d80c9821401108084403540310022609423001720321401c003110b0541c1d000e804000741e114011035a9440402096904240d990020030031004103001c864010056070300291380d610201d034009000480045003a07002d125003880514000f419642000e102601490a00d070341d121740e43e01d020784141c0184d41000d450b5401c060f1000300f405030076500040c0154001c40340c520b5009540c04401545208404000740183c01500104064a030010800b0785078544514001c42d03c0c43d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 17719655 1250 17718405 17718409
    0x6080c070b1003060606020606010e0405060609040203010f290f0306040b060d06150c0f0b07030e1207020109090b010e130605030a0602090a15080708040302030d061202010201050709050d0602070503040302 90
    0x100660b029400324894220070002c000701d92141400410590001d4040c502d841c1340042c10400400c0740c0301e800750b9160000030baa1941d408d01120140b4000910454030382d40c440101c90403040507400380102e8404030490f0310115101d03501c0d00c40e2502d00004907251400d4130070f1103408142d4001a00c0e468026442d103003c8002a0346800c058103c040420030300007510703480c225030031505501902d80700090020740620100880c9181c8524142705400400c0c04480da252a0b01c01c0f4001e1000d0b04080180340594841545d0394180c00c8000d141d024000d0760f61815164460325402c00311303201c1903207840c082035940d1440f07901400c00400c015407018102034000b5082c0c0d62076001c40d00340308481d00105d41d800c2d0b00080c020034600d400030880019042c0104521640c0410300405400490080c200c80e050140303c0b000282014403c10489800d45051070040c0285507a13500240315030070804000b01d015500702000a04054842e0790030078102e0f507000301071211460668460340000c0d40000020795a900040001101503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 17720905 1250 17719655 17719673
    0x1110705030d0b01050f0f03040201030b01030e030901030518070e04030807090b0a0c050a0203160504050f07020606010c15061205010507030e0606150405030a0b04020306010602060402030a0204020309010e0a140d0e0a06080c07 99
    0xc02107207c420381e0340e02e0248001011103520640d80e40c1070510b4122410101e000c0001514a6000c080c240080c1507116208800c040f51030160001c0d4061161300004103c0405524529000e2840303500c9a441c552030f19030302510b03d00070300c0c0910048824140700066a0718851a02c00004034026025250755000300d07000720307043c40303603c4400c00c04c80308144c903041190341014480c144d03020421000d40070440c20300c0440251100809800141045904005c2c07c040c0001d8400d0504200d842c2031341082070310759810440d460701a070b0764401d9405520340000120200c5c06070060410140985c400f4100c0b039a40c0204010140e946001305030010102804046102c0e11300f00030069603a40114142c0802e80f03001d20425117002c1c01600038804541000d8103100040c2c034005030054115504540142e201d59074400414010100c0f0707941102c0501c1500300210134084113034180060500080e0548055501e20603080c1e1380804040074190b00400c0400701081000c3c03054004507000307088221410710380340c1103071100841 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 17722155 1250 17720905 17720917
    0x303070f120501060201061403120304020105091507060506010f170c0d020d0204080c1f020c01050906120a0e07060905010801150314040515010e06012010020a030207020301110705030d0b01050f 85
    0x942c1d5a60070601600348c5d9041d202c42d080c00c048008015860451a2100712400041e1009041c00000f04108403165110740b448014084070070003507501c541e403509003400a0300c0c05070764003404101082a000c61075031041413101420400c0d2070000000d5150102010000d42c000041ca4110715800d00080a10440d507000a000400c503c1d001080c90104100400250444140460692440045012104580101d95142000b030b003400d105403100100c1c404182248111068061011f014400304601ca20702c1d98004000c3c600e038102226121519030205550781c10f1140922408144180c4c01000716420325150b03070340719650340e1038003240c59107158203145480070059908980a80000e41301c1c207448082c0082c03940c0101100081c0e02c07001e040c858000380800702c40b000c02400c011410404030b00d14442c200030b072a100e84400002107603601d0100e40014000c2d0404103080b8400d50034139125803242080c1c942a50005a080f8010703524100f00886548000e02072800d08a042c82000c0c4400390001c0309500103090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 17723405 1250 17722155 17722157
    0x90b0603160f0e0a090b180f0705070c030b0405011a040203060307030f06020412080318010501050d0f0302010b030d05040515040303080c03150d03080702062a0703020a02060c0c0307090e0303070f12050106 90
    0x1c002d0304540800c610000c2d107620447c8410f0858080082c1a44a201c1e095041542401c0450303440b0550b080001c070102c41070308090002c014010511003080f50550040107216650f04100481a084d4010441a4030064404640c190b0142c5824000701d60a045889500b074482c0303100500d45070f80e5400b020070301640403e09130740d01d9401000300f0400c64000382508404000540c020017940d810000020303802c0c101c0000150541442a1440d010103000b540b00c90800c4a000341200c0401d0f045100060203a0704c02e0042c0da0040e03c0c000d070400b40b16510b08056405695140d25080709135543d210541143e40c000030103560312001c500003c03612a4642c4860410850f000703503a840000e04c3c2061020340350aa0251043c0500f2004404c9442c0100c003c02488440c82100500183e0b81d000908080b031805111440c0030390321507000103546040240c0091724901c0c131754080d020364241c1341d542c0610f8401c503400110343c0701083d00100002400f1910aa44109151041c2c2c100706041070304001d00710003110000d030401c00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 17724655 1250 17723405 17723411
    0x2106040b07110114041e05010e0f0d020a050c0108040f080c06040c060c0b0f0c0d05010b0d1503030905100306031a01030b0603070320030111070c090b0603160f0e0a09 73
    0x1100c1d0310741c41070b01020801c06101c003e11099000810010904c40e0050000e040300c001e840c0c0900c4d80c2c141c90050400f441d074100b002805900c080c40e64050311002c82001034905442505502040140040b0340500300c160003002501a148540c80103440343c2da40103200b204c84040840b00d02c0c0004020b1806001004a201c0040c065403805141c010305640c05034204005012050a141000428038901d00342e202c90b4041c03041205460761a14140c00d0300882501c20308460806c8004900c011408000d418001c2001c031040c0b00c1601003001da01840b001034000540041c0801d4010b1001d8100b0181d244004801c524000480310b50f29240c20003804149271803403800d00301c071000420a2100e80d02c11582c00110483c09488000e1075551998402c100a6103040d98209142140d0001e0356801c1d80315262014130b220211340d07142e03407e103047e403003c0c9018044d40b030038a031400d800c10040c3d003040f20540e07110340000400c0c0001c164025105440030080d0411060810200c803100c466a5104d1000080080028080c08 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 17725905 1250 17724655 17724661
    0x405030a08031e09030904111b030705060c0c211201030f050111340b0702060f0a09021008091e160e040f030f020f0a0c1806050109052106040b 63
    0x420040c0300f80910030302c24407004003e01c00b803030b10302104942401004460000d820402800014010300403c0211b862001d01651a400e04550120080202c2c2d4407680645805660b0740303080711851b00800b030b0001c410398003542101c076070070340c2800303071041c190700c8080200781410100181d0100a60f826001164050000c1c0b130b0100411100340206400d8800000d101401c0200c0350074900101d4030352004c683c01c0d8180700c0181304ca840288540c03201304540c01c081003401c10300e0000800f9665041c2135908800400303500c0300160034842c0921030705851581c01429035a111150f44011107010310702611403841c2c1c1c06031181e040c0c0400c4449210640d01c00c8584040c1000048018140000700e0300c9900c0050041510303420040000d8007503140c9511503a150401c000d00c00d40c01e00c012444c0c00c071860181c00f128801c0040c0b0b00c080c0840c00800c4411900040300040d6042880c20303d61080d142e0b24490315000c2044050140300301c2c41c1c81c02c0e10301c5019030301c1c881442c01034000441c00e1b803904005031015103080d5460418 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 17727155 1250 17725905 17725921
    0x30302010b0d11010c020a030506010303020f060f0106050d09081902070501030c0305040b0c0c03070512070b0603030702011d12030d020403021503090a02010309060b04050906060102062404050c0405030a0803 91
    0x98454480d804964032501d040c0c0d81c3d00c075001203d440503803290401c07400300010011555802d8508001e950070600325400f030360312031401a58401610f0a03d441ca44180000140c80d10340800000341603c429541c0c80e41024090440c030400b405000408035003d0380103020081613000101c60400c0c0680150780100160703031500001500301d46230140d04c1020181400100000700d50341c2c0b161150408059401c0d507a494840c603e116040d07005090340203040d4012920030003481601074010b040014007600f10fa0f0400e80703441003099940e106da294000e0104d00d8080c910384501c49081c484985400780985a030403400d001c641c1160450740080d81e032110b650350101c0c0038020f509003004480d80b04030281d80858a5030030104c200c45d503611010200241095100c200d6030081000503006900300c4480030300180814100410710355228002101c4440c0140703e10400241e0012840300d101054180310b4280018400f0400306101c0540300041011400c0e80b0f04120009041d10100009c0c6810390065560b5a16400c094030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 17728405 1250 17727155 17727161
    0x100501060311030c13050d060207050c04050403080f040303060f08031c060305151e0114010201050702010507050901030e031e0d0605010c0b0109090201120507030207060b03060f01120c03060f0603030201 89
    0x314808041c60610002c2c0c6208001080760f41111841840c252109003200011081c420035410031904070824441180401c00e20f0b401415100d4400c605840044080000348000c0b81c030102c034080c1c00540c1400104500303400246055400500a180100f4003036118220413003805110f81c025525988005013402080008804c55502da0005110511840c0d00c0c540b2411750b9081d081d4812502d440d28600802c0c4406c410440f8250301c003907030030307840d09080d030f910201048a440c8040c4a540594203241c00950698410b10881d44201c01503260386045c5990980110010b1461000003550f1b48004c2046010500c18500e02c645256440c400340380d40d5076440000c0c0420303180c0316848941031056204042d0001000c00e0b00f0b59054509109000405900c50b000495540d00c1e07403690400c10303d01e080c00b4003070400c0e0306400401d80d56005010910502ca0907400741540c841046070607444101c4038000500141c7c1010342d8a000550082580301110394494480c2c404880e40208402c011aa07034030000c008168083c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 17729655 1250 17728405 17728409
    0x201020f0705010801060f030e0a08070308060306010b040b09010c020415030201021605090406020c0a020a0f06020d09030f030e12030c060601110a050d03021303140604020a12120807050405040509100501 89
    0x8081c1c5149480d02c40040c0c0480c0f0180504020310800d9094211001d1181e80082076040070001140c2040c0c13a142059002c40c3c0c070072030064000403441000280c1500300021103e040714503558034a4039003481d05800e210160492900c031070420030503070340c240c001d03079507900401e10300034040c41410b4101451480007928108403e20510940022400100420355a600306543e1107600306001682da103107401101401c2908182d8003c0d031003100e02d6004a0403c04020380082654615021669206178801094541341c0f81d510005200d0007002c80c2c0c050000f4030500c0b0b03060b10745c0d00151013040c2e80c0320800c07111815034022040c00480ba44c00441001740d0756900c48a0040c854200b64080e10348151240c1f80d040d1605000204030060580010311050500044400000295003051400d20551081103a444e00e0b140141d81c21b81c0304102400c00400c000407800b2000c029554840082e0f15041c020341c506441100c03004184070300b4484203101c0005c0c10b0700c403030241e24440c1028502400607030716644072900c02c440d01a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 17730905 1250 17729655 17729683
    0x1060e1015020312060411070302100c05070f080708070c03060209010e1002060a09030e03030d0f06080c0901060c08040b16050f011503020f060f0a09030317060a06050304050c031207020102 83
    0x24820100c1540100c11a1503001c144001c02d8210361721107012801a04403c400c502800400040e200149903001c24100c1041160745010300207081d5040c0125824042d9010140550f00c0079203072311000030000c50050a00503c41e9880e1410488103031500c1070328030300c80ea00c1030b03c00341e0300050840807941e8041400808101c0480b403601d40e0030210040290b07a03074001040228411754446180d424140620454841420000c04507a6039501404060020340307800350f040e03e40c3c03504189003c54803a10108040f8003401025000c0e0300568030304101152406407106081e5481e110800c000720700c55014400800d580f00524146000c4019107250103450071910307405445842e45003132103045800c504041c2400c1145e404171303000d03443c46002e000040c40030b1041034040340030f10400290440d4036070f0f0011b04445c2124000d4a44920f80303400f80081f0041c04004407030103640a4050300c4107120460080000d036400c01c3c0540201e92075518100c0c0401d1410200c1c2c2281041d10300301180c4402103607810030041901c0d07411 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 17732155 1250 17730905 17730929
    0x302150106090f0b09030c091008070b0301050105071b0306020406031b0806060f0901050c010c02060103170a050a0f03090210051b0106120201030506121b1302160204020a02010204030501060e10 85
    0x2400105662010b0140505042440001a40c205e280d0303007003000c044240c4004000c8603030b90501040026804a10b03229041c4030f070040080000310035003007109903412110103031140ad1505d0380a83d034040080c5165100c1080202c00540d010011903507520140020b002c2540300090006481180000301140004a030000c00886108121443d100d140903036511240914140761500759910050f00c2c6806920400207171381d03180103c103c100703503800265103048a0240100c0c0404030150342049090748036400c0707140b0100c0d204104902045209621034502d001091a00044130995540010070f8455140300b00c0f400560045500224a51594241d204600e202c2c40200400c51402c48040150400004041c3c1410390328000684680c031140c00300290044c40c07a007500e040c01100841400c0d816642c0c0700060160307114070642c0c1034a4103036208403014940b04013a5616104010707820800070394080360400003195000d010010004100340945400b400c810030348000149020f40b9000c0c200641607108500200c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 17733405 1250 17732155 17732159
    0xb010819030f030f0f0617060c040501081005030318040609060f14010c0b0c030109050601030504030c0f06021323010302070803010918081204030207090b03030f180d030215010609 79
    0x3040001020040d549400d0508107040031140a41c020034040340201446418003d0042180724a54001030039240350410040400e01d1503820266503160445502c4040ca00400c0140059030040c40e2096000f070b00d0a0368100d000d6100c0e070201c0e0075030b00103007600e000d8071801080350b03516407809008100c0a8451400c0030400c0c1482c240c42e100500d1624824440e00d030352142c4510045901c00c408020201d07800c84401d100c24106085da0071065402482000c1040d440d00000c0349866200313001c5c0320702561b01940c9049141001c0d84a042442608140c120740403903007003140703c1034207a2820602c002020152039217100ea0038803081c41d001450b5515640750402d03104115140000d2010025070b03054840594002901c000809c0c5c1e0710401c1d00c400c80020b080b048022403401c0c0030000e40100107204520907070036101d544e940d45550b00c003035503e10416a40d140d00240030b4040301c50542005020541c4a0040d1014400300030b002040040c018041c00b5001604070076400c40004140301c1540340141621329044035014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 17734655 1250 17733405 17733433
    0x190305010b0c1e030405060f040f06030203060901170a0b0703090308090703051207030203040b0304080a200303070302070201030216050c01090b0c0601030f020303120a0b0a061d060903160603090b0108 88
    0x20720b4419128103802c44843d00c0c0003020500b0825034020780b83c0900303684d50703940d04420210200d42151050103500e07120002e0200b5458030034003c0d41d00030300c00130709424401e9080c280c5507580c00260b44c01c280341c544600c468010114424102c0a030081b10541c600080220760340c1801002141d0003003000303a0b250700c900d5080000a000207010894845010700140e01d034140c92030228194402c0381c1c01400c1c218400705c148401e114004c402449410312648482165284880849010300012040300708281c00900015103502d000303800804070540f0500d0014500481d50ba1350603000801c803501540ca6920840728a0480d58021984401a0241361440c80c04c0000302c0c0c0300c00703a4814050000405141c4028510800c41d00c040099414502c0000200c3e2981c2c0350400f500402003040c10080f920555404400040c29030003061140201811429a1210702050308280482c0e035114414807a054820400307040c04e9804a82c1c0002c000d44000d0303801003012a000c2c00d00c2031a645041e00100342c19040280c2c130000d00707 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 17735905 1250 17734655 17734663
    0xf0c040e0a140106140409020d0605060a080f0f01050705030f2a0a08091e03040b0702120d030c0f030b090601120e01090f060e060c0304110301090602190305010b0c 72
    0x10040844000c9031010048964506128009074014294400090040611a0190080350655100c1d205030070002202ea01001300b66907040f84003030b41003442c0c504480003081e05600f02c035070300070f90190007131100310340d03818206140c600c01080c1109960040041c11180030000e0043c86d4001400e45445811350070074207800084124003410100d40e07490b0103d840490140e000b012200d00042003071000751213a045113009096004112040d000900541c41c8810759895034030030980f550000200158180350038181c0580c01680806801d030fa104441240300b40708400d00b0000501008415a0041403180241802503c0400c054103c14181810010b0200242c1c0f02c5000b401d90000c2c0c24a0625600c0350760303c0119000344180d0600751001c5d42020541c4051161015080e2103041c4200c0042000780c8003520503130f407540800d0720402c0e8000340070408600864280c0000b10036511005000043c11a01c9640d60000c82c0d00240d01c004484e58015074040b003454140c4030340d40c01001c09403030441c6000d107404805521 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 17737155 1250 17735905 17735923
    0x50906010507240f0203010306090201080108161202040b04090302070f050405190903030e16030b09030309120c0c19050f0108010506090112090c0303020a0b01080111040506030702100501090b0a080f 87
    0x1680400c4012000d01c0742c0c0c940c01052116134081421562940c503403c00901a0403584000d0380400c2829000081c400030005028100840003a400d00c0b40328140382d060b10722607698000503030340aa2614240491542c1303030300c210101d1038401e07002050502c0c90400c90410b41a8268401882646044204600018060040e040074400c0010014a0114929050380100862002c101c0244501380c600301c205034010142c2c01c16240a581c4c255044d658000c912a52888101c400000ca500070b000d2101010490340050516944844107652140c561600841d031000e628428915885000d02020070603804e2122410034596820b10b4a04051f60500002c00c4451050f0703030f811810000707100e5900a100307036264881054140c2c04095030700e0031a03032418000d40c0c1c1c9003900c4081d41d00400324030001884410500c43d03550000c060301403040c2818a044100202031f040105214194010041140da90340c0a0b17101d0700c0c0c0038207001d907000681d11403440c0a02c8a000305a80040b452544181c100c0c0c446e840c07001500020b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 17738405 1250 17737155 17737193
    0x70302060c090105130f050f12070317040e0f07091202010e01080604020705010e060702060907081f021b010e010c030b011413030b0405010b030606010806060a0f020102090316050906010507 83
    0x103601c05030100101c549125955451700030600d45400030400c80c3c00c03003102c60200c0380120342148204001c0e0b8200403c9a10100390089217502c150010000a004c3d83d207555865855128400e052980d03858520b82003200848000c0401c0e64501b040010351500801303080c0127030880c0320001c2d800300031550010300b4095220381a241031010007000186140e40341e07011150031a038020000d1000034002c0c44050303600c20040e6141000b5003d030600044512a001940100b1201c4110040040c2c1c20711a180002c0020200c144200141d000c0003407250b0301c0750000d0007120ba80c0700784000241d0a2580790030b107821904d0206004007003504140491500b42c1c2d210250605408175000103942c2c071142d503d031604a004603988010301008420b0104818007006601101c2c8449050301a45d641c1d43c1c42c0f000458080c2000c0300e030258030170780c140003503460b42c1d04c18072941c40b45202e0350000510301155000040e00d01107445003004a2841c0e008801e02050810300c49880d0446000e08005040c4540d650701d514141c1913800c601e40d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 17739655 1250 17738405 17738407
    0x60c051e060f09100e0129010c03030504020a03060c02061902040b04091e090305040801060f0e040f030201091410060504020901020c060304080d290f0102070510020f0d0905100203070302060c 84
    0x4070340721418042012808030b04c2e003040007039040494200e030281c500400d52401d40300c112182d83c41d03076242000c910300003290165234040000000d0340c4c06030018a0f001d042a6044014554080300040d031030301c00d4080d9140d082d0010705051420404c2c0800c081c00b03090b0f040c4510f60040c0010071040700d22101766816144204000b091003140b0120501c05102c4100001440718140358080b000e05030040010815683c0c250002c0c4501c94545500b042310700404d1140d031003842c1d450000180418000148501003610910020925010760b447d80040302180c0c0348a07440030340202c04204c2c00170100e0300c548002080152010740c2001907e80001c0c0d210740319403020b0741c0140750020020f01000020230486400403020316041207813100100e0010b458008006018220390309400c1e24101c41c0c079040421200b41c0c5416401800fa4a00340300500c108088250314038815441207180c1ca8036001c0c4280941d0395100301c2a03948000712883c00f03082120507119007000d4415500100700b8070000c02e5000c10600d900c4428404e0007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 17740905 1250 17739655 17739661
    0x305100b031b010c0803070f0f020307080a141b0313170a030f1215030309050405040f02042007060b03010b010c0803010b090109081b0907050c030409180c060c051e060f 74
    0x161114100f41d500142085030010400447c5e68204c03041d168032008594440b144062450410780c0d03030744500100038003906018000c40d509240314200c00a4070541d0104011f0034002084c0030754181403441840c842e40c0342c00115001901001e5001110010b100310036203155016603401d00543c460302c0e4000d0107020042440c00d4081d05501038405141d560507540c030104403083d640c08440c9210101404100c002445034640081c4919042c0141401a50007903000c2c3c5d1000d5060303003044003c00c02c0564600310210316140c46080000844040c0900c140070300c10105280c8035200800d0300319514800c0032810700800b4200c400c08581410f0a40c5e0540e07a404818559881e40ca800680d025032080e441040e803440360b40003001003070b03041035040002d201c41581c0c0c03000a619445405d946e540100928552141e0041c8001c02465226801050f0100c03d0b03000c07921a00c00c00c540b03440d548480107800080100c0c00b080710076001c0000c00c0014420740c1481d000c802421030051102d10b6265280680038465078080c141c08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 17742155 1250 17740905 17740907
    0x90f020415080402040f020306061801121104090501120f06020702030c0a08030c0c010f020c01120b04050408071703190b0f030102040f05010801090606081902040e0406060305100b031b01 82
    0x12100640310240442070020402100245030000840d0700b00e00941c1000c0c84561006101d000780d81c00707414000d00700c03420180c01ca680442d80301250a201ca041104c1e00341c45806000c402d1141841c901380440341d07550303075508010000080e01e006074060440710034004078a0003c200a4802212070f20703406a070140e80c810071800000d00e850744110791039501c041c000000095000000006100c690703a0802035030f00d8015a41c005641c8021903007030000140e040709200803241c1d03219400344555a281072000060768641030000c101110360884080b01c120300001881d0045c0201c0102c02800e85003401e400c186149044205a032590100da150009025214070384c1c59032507a944080d1680c08800903008545550762007146400c4800710344a0a03010440f02c0001040e0641103000303410a641c182d0b261041941c558240364070380304c0808a0000b403402da0921000c68500980c65409004038050314021400904600b0464104041c0102e000c0c90580342c020000c5058501066503060360010035040507011700d071400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 17743405 1250 17742155 17742157
    0x3020d050102070c09050402030c0301060e18151f0e100b0304210503060f06090312090102030d0606120f09020a0509060f0306130308100b0d0504020d05010c030b0f1801090f02 77
    0x202c000c1c8214201341c3c0100c0e0450313003a8005442507000300c049a00b10403140d0145400c031400c0380a407a088440700000544990134850101d0300421480ac11114048082030719280c81e440182c1e003842000c0803500c52290510503500071003001c0c1024461510742e50070420007200d560300c9644203414245801000050a0100340f00b13080622680309501401603504080c00100070303600803100740d4401c1b00c101d81070340c400d81411070070343c1d141c41805001007401c103599900c1180941c0103944080d0461000704803181c0c0940190055400400503a01c1c0c0a010510501c210401c1d102d1220b88541c08604e09140e042c00350b9500c11445045480641e0340740300544400010800ca542022595501885240c045c0017840c43c102e1407207500c0600035611400303191903080103030032011064407a6801e000320a0012500b00d450036404582c115100500d282040000c658605094132910100031020076540d101d40c2142c0d0511140720908448110340d41c1d900f0f01c120007030091150006005901e2242e0307440703110100206150b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 17744655 1250 17743405 17743417
    0x315060608071b170307090305010e030f160204060807060302040311010f1205270c0301060501050703080103030f18030b100801020f0d021b0304030b0405010c020102190806030a0b0702010603060b03150103020d050102 95
    0x11003c00e640b4034208a011f00315400a00c0111895840c020780c0445512012083d62400302e8407070252854a089032004203000d030744030712050f42c1c8243e444000107500c0b002040250000c000031348003d40c9981c55800c00c580c04010b1998410f041c0071003000e110703540d0350b4170200d5080c00103032804000442c2c1d10b582c00914110f45c2d0b84101c07640c1e002010a00071030707805800a01001030140440003032140c50740303500044a090155070320080200e4846401400081d003d82d024040310030aa1518940c4c2c86009420f0f202c40c415258004c0d54214498010700c00f1484691f1059400341515900035844c140c120516650316104421030840c041d40e01082030710201206142040d08800080c0480351500d480381000210010141c42c100e40542ca415070310400c850040c02698482d08500024800c0309141c0c0300c003950744d590010052039150041c9100d03e400510f64503c02070180e50664000500c00341540340c100100d48104ac0d04910a60241c40080c0503182c022049034152981500c0c8600c1c0b5507071074582240640550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 17745905 1250 17744655 17744693
    0xa090905070c06060f0303050f0d0e01090c0e070e061e040503070b0a18030c060c05030702040c1107081c140c06090102090913050a06050c0c0105010315060608071b 72
    0x49401d00803507a40c403001ea400594003480041102617a00c01414402200510000700440e1080c410240c661500d48041c00c20441c0054000c41c48180201940c0e01b19910020111007031034003c501800b07884102d07250150b220b415400c0000c0304c000b10000080c564060703c40c0c8900f00d0110310b20f14507400180380341944e0003041d01030f08482d1101c1d1500ba51075000d8200e100a400001c1c0e480088401208003500207030122030b0000040f502d95400d1030f03001c0b500112041c206648900c410080d0800588035071140b8400c0380c110350b594210000b000f03400c0c07504020481d0301c120b080e039000100541a440c0c0107009604191040e0410090036000240c000c9524021038160707114901804c000c0003d2084190005c06500d03504503034000556961940090120300f41c80409003d5502c900c900c180000c080e85d20031500311800c6200300341818500401d00d03080d14001d800c22a85020315450b04070241c905400341001a04076402c10f200c0c68a8038072001441a03108a000b614584000881813041c0b1080c2d51580ca07050401c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 17747155 1250 17745905 17745911
    0xa12020a051609150b04050402030a021b0606010207060f0e091f03050106150912030c0602090a030c0302030c010e010807050a121a0111010b060702010c02040605030f0a030f0201110f0a0909 83
    0x2c00c40324035445001e030384a00c22000742403034480d4210210315802182500c00c5110800c2c00c2904080901000b504020291000d4560030010342d00e0328010050000c2c00d0000c910024411490200002802c05145070321010070b1003886041800150b401c000350040041094441941c1d503036460000c492078440644003100500110007000c030078080190814820f6501c000405914444a01c0045640d0940c0f481988810700c1b02415a0f80040d00c510359207034146019400143c10b00d0b41100014038014801c1d030048a4508030b8050400c114101441f1245c12440c09007071a550410911001804020700180040100840007500e254110f018031034012030b800204104100443c03210048018800181d681e0380d01203070000641e2010310805000300e480707204021b00381504001c2280c0c0159030030040321504990007a02c03840f01003444d8500f045681b056000b000005c003003a00c107038100585084a00c602ca4411a410604c0c41e56040101c40110b81e95211301191a0781d0720091040104c4001c09660412688681 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 17748405 1250 17747155 17747173
    0x60e0307060c1805150307050a021204120201031d0c01050703050f030a0e101b031d0105040c061b020a0b0a05120709061403060a140a0f06120b10020a12020a05 70
    0x40c1c020103075643c002c140f010950320661584100001d0048403074500f060f038401000000c200d0b521401c090111480b0b04d00444001803d03000d42803290760400e4228408100ba81e140c20000e56a040c02210b0b403034101e40310120811a4110342184c1c440650059150500000090765002c0610510441b0064030a081e2490b4070303800c00010040240c003a184041e80d4a00c504c4100c2c0c0c16807103581c031404c2110f030920850310690072815401078015004420b418502038800071010304103600c0038091107110340c1c818002c035003940e13080c26409045070340c12504241c02c105e40180d6480040c0c807041840415504110422501c984000720201c0399441214280da5541e020b840900c00301907049400d4138145d41c007a840d1a414036003100404080c40c0000c07a00c041d03210702241800c000e060132090442010000240c0382200382030302d4000b96040c03400d09901060004407190f440c481084038503c504c1c544000c044a0b00f032042000c40070300135130390910000003518010f165884d41c45100e00800c040403d04d1750107019156111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 17749655 1250 17748405 17748407
    0x71205010207151a0f0d02090c09150a09060309110301090c06080c070f0b0a023106030204030323190201050a05070207050105040303182d05060301050607060e0307060c 74
    0x241040008032004940303d80d1524a200c40c40c003841640103e03000002c521403070b5020030032061300700e21540365802c401c45042560250700c800d0041807140302c1c1c90122640c0c07000e2030030610a0361181807a082070114402c0c02a04004e580c01540842111980e140225510205090080e8554601c04c1016415071030105900200306104030035408882a640304c43c2c006540d403103005006842051401890950381f12030b400300056054180303a4010001d000c005040502000e0a0820a00920001d015422000405004044120200740302402d0a07240c21744c1441d24580c0c0c05444004101c42c8440300d0030340403465070b585014150a44544140d00c18440c2001071900501078000c007000e40351140303582d050000081c800d82c0009014402c0b5801039490310314152643d242181c610a0140c40020418140500010b080404140c000188203031480805204e89511001c03100c55030703403a84090701800c001d10040005590740c60585100c0d0f6000030300032551407400013080c0e0840c490a070b401011b0f589482c004003141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 17750905 1250 17749655 17749657
    0x3010609140f07050c0c120309030115080d02010903080604020d0b04020315040b040603020306040b0903070b010e01182a02030904050a0905190209150d0c0b03070f050708090603040201020712050102 87
    0x1544146188110b140c60f0488125040d01c210300a041440d40f141a003609070b818000790480b1959100c1d030541c1e0402c40c071680020b0940b120201c0454884c44214802e00604005000c04900d010b00e500003003003c0b49266074090482c220080c42c482c419540441c1d00690f0000540003e02e42d400000c01c11562071403c1150440c900401c40c2c030580c012803415071a040f16090621030f00003601e40050040c8042e503955543c2881e000001002158640001d00201d00040c0114407400d002c0c007994120f900e0301c1c0d070425542d54104800340100e00d41c4075042c8030051908810700349041c0c1581c40c0032844030300f60420010042c1d1452240b4160250080e141c1002c201c0d518943c0d9111908071031080d41600d02c03040204082604e6207844500c081c3d44100d9140c0850310300b00050a403114099005800140440e05070340342c0b440d00f0f000321781c00341242140001c10800801e070320101c86090342e11107040080c2842c96a46800b0b0b210700581e020240280000000700c2c09580c000c2012800400740064010b030402d0003407078a50b0107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 17752155 1250 17750905 17750911
    0x318060e030d0b0406030503070b0c04090603030e09090303060d15020f03010e150603150f0d020d03080f07020f0c040509120301030318140f090403110f060f010f0f0e060301060914 79
    0x1071189440003c050310314150048400722074018004509044103a00d40f04860392000d400044004000c010002d200b0055000e58402140641c440c164169030543c248075032500f00810800c0d540c1c008008001542e075400300c0c200c06c940c2d007202d4404407202c840301000c03000348070300300711034984003004000007802c175040c001207510035440c07564090300e11602003050001c0d0b404283c03440e10808885088004c903508100041c9800010028030b1850400f0442d0082042e6950800041d0002881c1d0000c100001c5525421660000c2d443e10003420130604400c40075440c0d450460baa41d00c21512000440c4100c0000c100c1c60050a1401e10b645540396580e00c0c01505100440d06021000715480e403000039120314120100c500c1c45405000c090008001c5030400140207001441107040c080044190ba810728001c04c0b44c02d030995010402024107081100054160450582c00f03100c01007020303101446200396135401541202c41d00001810a5201c50001a02502e01a00110b5205140104d55056034140c84c84c01e40c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 17753405 1250 17752155 17752177
    0xd080627090f06040b07080a06031205070c05060a0203040b030c040302040c0c060c02030f03220602030709090b030a0206070f03111f05070806030d0c08040e0a0504050706031a010318060e03 83
    0xa9260300c4460000e0b1a89401c1381d01800fa5613800d40090702d00380c0600000f0358010402c4900251868032581c0302d01c0960050307400e5600165010420710200030080040d0005800202c580a052900c07410009540348900d020b9030380ca20700040003040703030120200e0540b00559401030040c0201550101c0c000c10350340307071004203036245410110030400150000c01100e0355000d1504031103113540d4806078400105003503082a440700f00344c645d559a02050b203600c0514000d400903039540086502d4440c5d9541500c104c0c800703061103500541000310041e80c1748405c41e0b4025034001000c0301400d1080c141600e488941080060f814081c40301c071500801702c03500c4100300840001c0d90800894a0704a01158654400c80d503851f059404241600401c42c0510000040300c1e01c1248018502501d445001d400c2e043d0582d4825101c607125028041000700900c2008003810030b0b4174041101c02424000300020f1100036612038141542e4010f6100d0b00c0416040503070075580c22030030502c0018460840250780780d2207100c40c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 17754655 1250 17753405 17753413
    0x140706020120030609070507030c1211010b01020105100603050c04030b0903090414060306010b0c100e0106050f01021f0203060111011406030d02070803040306020906090d0501020702210d08062709 86
    0x92962034006083c2c9008400181c01200e2a81e0b80c0d41c0182d803164002c80e02075007405504988880059499017090950280c2030f07036038011448010800a0a4038080c2c0001410341e4184020029081c2200255808070380360340c42e003c21035071291450071000b80300b40e410240c013a407542c40801030141000402003080603c1a5802c100324140490002c04030003080d0703003160b03060304920010020020107074003402d190782110080e00c2520158640c0b1038101c0f11400900c80c1c05035169042003042e0b06c0c4c00e25040d2458042800a04200040c251510200240f081080143c03141e010001c182141d1244c0503810700a001803008010011508010f098801d104030f03142e038031a101e5981035044452000c10b008007264000030045040178119a901c1c0065008000d00070341090f01400905031aa8a0000d210780c8180158001680c030300281c010b00c244a921140728000800c00203000c10130340d20002400100300c0d4800c0c03801008903111040000c02c0d55455519903003442c001a481c41e03581000004925016000380c008036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 17755905 1250 17754655 17754701
    0x4030b06060301060e01030507020106050d0b0117010b03030d1a060706020c1c0c080904230106120203060109150311031006080a2f0c010207030e030105060a18091407060201 76
    0x1072184000d00400c00041d4010000c000c5c40d50080c0c02280c1c0044a5000120314103840d0800303c1c0c0c14107085c420645d8122280b000411040090482c28620141000020f04c075902c151000f00b5502e100e00c0b0100700c2555941c0f14182947c840b055140140750100500c015664003160404070040c4d0843e0100610b0780c050700388030714403028030a03404003210103440d150040116210340301d20b000c039041410802c1e002612210b803940341c1c0d001941842c0c0b882061041101c1d032541000b200a00920b0540400b80000744100300b40281d91703070403060340011910718442514403482452000c0f0041e1048000000c1a11000300070301c044410300d51400c070300b80c403096a02c0310702c00e50b02c0c44100425603030050707aa60110b0a03c00610f81c40940d0001029903c0030b46501d58070b261601d40b00c201822680b0404041d0001141051001854079080c01025000002216400c800c03900b4060700c1e06d0025a00030340000b420741c0c3d89000404010041c2c00c88917400468405a891103a03441e07001034060f140000714602800e841d4005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 17757155 1250 17755905 17755909
    0x6091506050f0a06020705040905010b040f020a1101050106020c0d110a0b0910020c0904020d14030307030b1203090307092c06010503150108030d02070f080d090308010603060e0c0f0708040b04030b06 87
    0x103050215140d0340d001b4070030b99240c1000d1000401e2450300c180c880d0354a41030a8401501d4a01450a07400076603039005a544c003c1e194010031a080036000c10003942d06040040103910390024050406410480d0910724288061034103855420f02e001107250050581440040c0c0580c1c1034018182c40101607444120348810014100c0e229401c182c1741c9503000001002150141c10042401d0303080b640300701040c0540001c0309200c90700c0c6030811101100003030348070745940141d070a21090314020004544001e6007800000400207440745103501a810105aa454440481600502c1d07a450428501c081e144e0708204601e10b0300780c0b40d81003405814003034030607401e1240780b040d01884002c1c103d4018501442c00c0070300e100c41c2c00000e5440300c502030302d0304201d815000012031000c40c001c1c0010310510100180010745450080c05c1180144e020074281407401e001080705107000740d2081d9001c490105903d5480c40c0d0030701b015005005900c4090311a03040800c01041a2740c8542c0100141d900030300308020142d9590007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 17758405 1250 17757155 17757169
    0x109080d1b03050702130b03011a062d0406030608010606080702070909020109170604021201050c040e10030c03260405010921050f031804050f010506030406091506050f 74
    0x41820009011511600c1241a10307001078810901c40d25240d0302d07003550740d000907283c1c901c08060603041c69603480030380b65249024403509003500340c00c28141c0b41c800da41e540000c40d02d0042e01380c403070f4440d4008100c600208884c841c0060844520b0680107403030315215200100201560f0280d905658a00600440c40b603001d030012921440640e40205070b410305090816010708444101281031140d0400041403900004030080009a500741c018100c1d443c050041121956007040400d00e1031b4501014010b81c05040000c40d0b00780c0318840605416600d13000725141c5003003105d510140c40074448107008402c129124030b0040024500b2107014287c0c000720b0421540d14070461040501191910304204202000004010000d095081c40c41454211586032242031101d0120b208086800005030a28128580c07048440c05020a481c108500d01d000c0d1042c80b00150180a4280710360004000107007000126004207110302e0784141a031441c1010001c0440207030025004980c030502c1c8c00d28681c4940d00f4000d0b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 17759655 1250 17758405 17758423
    0xc090f010305120a0302040b041508130b0a09020609040203090304150203030903040303030f090f030e03070b040e010b03130f03170105010201020c06010e070306120c05090105030f0c0118080d0e010908 88
    0x40a88503418004031030910301c4d80403c0d00b00d402d154082c00001020704003030010304014108509241e10340031140000400d6068002c0041031242d206110480c0072504424106074841c05070341c00010007010b18000141507001d071041d070039800703070000040066810000c00544100d07100b05440101104007503500b1303030703c03400200c0d5007040d40d5000b44001c101191080d04610300c040c80078040000c3c0c280107600e031624070391441001600841d104160380d010604007002080b000345413804030f1504003414007640201c541418840c00198980110124045480e00100b01e8240344d440f1000607503114a505d0090b241d140c030701070025003444000713000203100d5006008032080b5400a80103041507a013445030501254001519100400d684e4910218020f40f00b9501031941c10301070703034a40a5087c908010042c06000503000305000360000f5050b540b040900040c102c040d41c000f4246040c0403990000310341000c40540e8041c44a92007400c1c0414452038101d00f0760072100e1800c1c4c0e940d40360103488001d666a941e10744 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 17760905 1250 17759655 17759663
    0xa1b0801020412290403030c0c0b040507140a0b07020907031d01050f0109050c070b0405120c010b03010515090a090f2001030b01020f07060c0c080607050408010b010804030e040b0a08010e0c090f0103 87
    0x40c6001078002880f0364010072299195003030480201509d51640f0442c45000c42d421030f030980c032800e014400d00b02102c40c001d00c1c10f80b0845a01100700d08020204020b401032500017800f40c01c4020101d0880c03402034104501004d184071484c44181c1c0070320b800601070302c026510341212244070705c00070400511600034036124082101c90385181c0342282da180c103100c40004005840e50301072aa803909030340c011680100a80500c1b0000440c0d00c1d803011040508481001c0c01f0600c1c40c242444079241552a115100d43d400132150700001080300081c02c0015500c1e074050401003241001442055510540c10a01c0c0c054000c01e0340c080100d03182c07180043e45c0d1b40107071243e01011680100c0040040b070344503040d00b401ca036218401c88600e080d941c801d00b918095050f070714440880d1010800384a061424418240303808000d00e8003800506050720098485080e0400a03809503072100c0c580c80b100e44400d4081d800600169000304070584545841d0747c5c0360f28a2490781032107020b00d100845d400d00c1b040701d10203060303c0d04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 17762155 1250 17760905 17760983
    0x1c0e030309060f0a020c04020a050c010e060405060708070c020301020406081e0c0d0c0c02130c1e0801090e0313090b011209020603010e0405160803090a060f020a1b0801020412 77
    0x6007040300f4800d8100310ba1890440c80b60b006c10744040d031180c0c005040b000c0859114540c95559a040031800e44a032a05010f18a41c8103208001c0862000a00c040e04040326040070000c9071640002259a031102e00700c0a50150300008001031520361009619100341c4c01c1c004440d03841000106c001040841c183c0e601d080694003403005200c1201a64003c080d0721790241010003041c00701e5404146400d541c030204954495480458001007504a41510f0501040b00c034400e4401803c00009440008180504510a59181c0c1180d204003801c104440300e040042c111441d05aa984004001411004c0044c034000350b9101c0040c110b0800c64000d20f00000c0d8000c1c002400c603802c01403140c3c5140f600500035203c5206551003060748003526000c520190031104041c0d5503e075040000d00c8004c3c1c206034005002c1048043d844105242e001c1145c80b00306a0160001c05000d83c1d00d0031803060841a9040340000c1c0d440058002908408004072050383c074455105500c1c54000c1074002c0c15030700300c100100940905 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 17763405 1250 17762155 17762167
    0x305090c030d03020d0603020901030c14060c06150d1505090705010302040308030610050f03090a030215150d05100c05041403030418050c07080a0f02060610051204050705031c0e03030906 82
    0x1010790003905d28000c003c07000140d02662a00051074108081c0e105550100d45094240304101c4240c40366801d00900751071003450a0011145103949810040c0386c0c0c04081e104003203614903590307180200d018071178100d100d0050816030451800c0c02400d040c0c8882881d4032076a1000070ba44d5000b4001ea8084941000710f4505598842e41408005020100d9400800008100100c44038100f28055402294120001d26035070303010b880c0203445c00307000030700181446980408003c00800f00e6002561035400c155110554003e5a10b00303640340c042810741030096941003402181c0c0c000d6000c17010304111120101c034030340c0d105884c4040c035450b442240a00c245548402c034045001c01c1c2c054000940000c8420212407900b60980c90b0701d03216800440318100061074845940c280103504020740c81c0c02c10310444000d030080310050000b61039845508506d540f503040c010001000d01c44103210038801000080d041d1030086800040e03000b00040050641008110f0034940704000c1d04001058440b003483c05051549094 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 17764655 1250 17763405 17763407
    0xa0b0111030d11070804060c15060e060d02010e1315050d03020309090c040e0403030f0f0c08011203020a050f03030610030e030706021803012a020102070206160f05030301080307030305090c030d 85
    0x28000303c0341c20040f070304204a400003400c40006000514155807811200c6540307103410907010040b1000e81964500340102801060030814455801c100200c0391104102c03021700c01a00d51278100c2003142d6200c64041c0607840c0411740380d08100f0511803090302804100d038030740040002c1130000c1e010213001070303100b0b11a01036281040c0310415000100c030b000d460f040650300c1a5120070348001700d400714002526070300900d440e0810741c0507180e40c11044803020301c43d043c644100148403807414451103424507c0d010200302490700a10920702c000d81c0050135641e0144d040c842c825500e50094070f00c60300030b0162251104081f88070784100e06403840f8020165140a01c01c0d1540806500100b200000340040170080740ea8596007403281310b244101c80140d03482c2c2d03549030100010b031a10000c00d000040d640100180750050341d40300e04540006243e403003016425026800d10106200d030304070005040340710000c00854900f000001814809100340c2c0d003400142d43e4208181c2d01c406d414210a0303050742c811819042d4607 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 17765905 1250 17764655 17764661
    0x10060602031201030b10080303100f121709040209040504050106080f0d0e010806010302190804060f06030b01051302040503030c06060a21031416080711030a020616080d020f030a0b0111030d 83
    0x620361424000300c1e141c031416114115442607e00006003d4901d0341005140c3c100140400148113341c1084604501a01c1e07144140c6200d420410788401c2c0000c45070b030969a6541074070055280513200b08002d107000d1030154003c01590040690394030031500810324402e00014034141d00000e07540c0c2c104280e82d0704030041d600008094200d82c1403540a100d440001c0c003000200c11010001d50f40e92a41c2070815080c01021100c08091031011641806000d201003180031303070703800d04685040d907001000d030200700d09a100030702503500802c1c1d0500002407860a0341400241c80e5004d600100c4c0e124414507900d000a181040048400c440054980340c07094000ca4081c1176802c1c840701c0c007220304914011080003c40030707803465010f007100c6811001c103416090100ca080e4900c00b00d4019401001881825000560b1f45d015204000a29403114900041000103070030a071684c1c3d1034107150543d22082010340080309900200e4070052468a0031002540640c4110075a00d80c01070780300301451a103e100004032010b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 17767155 1250 17765905 17765911
    0x31b03130204020a020c0901050114090904050717060a0b03150411010908013306020723040f050a0b03061603020918040c06080a0b01090b07020117010810060602031201030b 76
    0x303141489140d4501584580c00200810002a8081c0c080c94a252080002102040c0c0240381000465115541e084217681c0c101c4480c41411154a061903442d4503101d442d00d0410b4000740c00841c07003010700f21540c1c2070000350315001d815403843c14000f410081044c55556100f2907050070b07051340a0008100030614001e41d04030442c0c818545100c190b51034a04540c00d42d6042e41000d08010562103480c02441c07040d04e8121360460f12014400803d41c54800002d6a8008900480b41d801180c007122801400f00da00010101000140090081c5031003944048002c00c5c00300c0d40c1035501424003e0340c461610b004150140304852009144114100d000c00880c001d4001d00c40140c0c0151541d0300403101c40c000940080d01c00ca00c1441c001d540d95003004001094048003030f0080d594035082101700a16aa00a04507106652200da0441c0e11403a1030b00049802d85041d04402c05091540700020036508070100702d8903040f00c1060414000389550b031000700e0f82c81c4120341c0482010311500005000060700041e085030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 17768405 1250 17767155 17767171
    0x90408030408070b01060f0f09050d1e060c020a030e01020d27030605040506040c06080903041509090e07050114040e060603060a0314030304030216050603040b0c0d09030206040204060b031b03 84
    0x200b000783c2070303854004041c8280c00c40700100d0480001014141d03401020301076118003620303003d01c9181c41c01d40402c00c001040000142824068403105074804d46800c83c0e11b0074180c0240082c05141e03c0341401944454440350250b00080b50007400700c203036500004d210358000c10b45983d40c18400d42000a0030074510310716100507511603410300d000808107640780141d90240d405000500030700c0c10030786404201d01c201a0b0140d0b0a00100c40104100083d0120a40c2c00319500380380d508035034442e1000c08680c100e01030741000304000d03c0c0c05a04c00c040c0d140062480c041e9a4207803110f05416030821a18501402644103130010f4125402c0052032a080c50000340d070b00030340040c0190610702d4403991390701890440c00401c000b00744c7c404410081456810480f0f510202840c2112102050518010840300d00c0000d02c05021929800e01040e6035000400c11150b9461050b03408025030140703441c0003034440c001503406a100303508000e000300b06101c603401120701540754000070055200081c41010144c4c1c100800c602 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 17769655 1250 17768405 17768407
    0x130c1209031107030506010f12080307030f0b0901030305090118180b03030f03010611120306090c07020d05030a03020403050606032e021e0702010807020604030206010504180f12140702090408030408 87
    0x14040e0b41e0401c00740015500c500c015080e0340d0b0500b039401d218003000d644085103080e262030444010036042e10807240c0200700d83c54041a011540e04000c0050040f9030f002d5500705005000020130300da03020000c1c058031030099940000903800b0400307200191205008100b4222442d100c42e2440700b540c1d40c40102605409400d50341808490340764503d45410036032013000803a0a589021240c44000d001c100c0c1402d1160340401e06500b05480401c1015400420740103650b5000500035081d5030720040f8a846e51580072048a035500c03918a0020041c0d04180700448a511072072012403042d240205408600c168000703005e40c010800c03900488504a046604440503560070450600808242e20b091907000c10407920a580d6140144001030290400400b40801c54100030305220000e6800b14600781114012200400d94444240d40000d5411000500500d002c5035855002c04212a40e07001c1420151603440301003c0ba0f01403850300505128011000307611a44400008000480100255822500907040c0d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 17770905 1250 17769655 17769677
    0xb0c0a0908060108160b0301030305030105121e0c12010b0d030507031107090b010809010b09010b0a0e0315090c0a0803041e0803070b040203010b01140301030204020d020708070f02130c120903 84
    0x101d401c1540c02e0300241100e03041404900d0054021044503001413079410306451941d8503588005042d80418025648074001c03006503019030000801081c40507071410044141844c1051111030b44d98000f07400c040380182c040c21292510401c040c811304204a80c041d02c5050200c429a4048805500041084050080d0380150741d00a050400400e405820f042000081d10484070b400500f50313045c01007010381c083e030520b07502000e2038890711070190449003464403480c0c039035030342c4441981e9182014914503050b100d0266140355440f140500c103030143c1d00a00c207440400c501c0c0410300c84110301502a184141c0d2041208011110b03880026445600c0c1039501400e101e6182c031b01c0d0a00b5548680c00544007c540d04007800158507003803090500340207090a15025043c030b00070174954540814400a486240d0101d419404c0400075012500750710383c0018115540c0c070240c50310940f00d8044d0181a80119202d81407428203a105200f00c1d411403d4a4030b5461210300001d0320390020f058000c2d403c6040060002007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 17772155 1250 17770905 17770919
    0x81602070e01060c0302010f06150c02041808070b0108010902010215060d1a0f09010506010f0e03010906020325050a090302040c0210020d0b0102010f020412080d0b1503070f09030b0c0a09 82
    0xc0035028002030340e5445034040a45c10000d0a503180552101e0355185050010805821140c802c3c20342001181400e005400050000800800c95035548520340b00c045c4c0300e908108180d58009101c824820b006814040c1d81b40c0008900700d0b400f002d40203001d81c2c02907040d0020103184111050740301c6002058000100141c5e9a0502440403101c520005641514140140b983c00c1401840d400f00c40d6000800151600000080c05901521a001e0502588070707051091905c007900680921604054155a0384c10046681d082582005940003607107504a203e00098600c90f80484440048940d18000400e00396004c03c0010310038543c202d000e44c03080e02030b28041010140045e00b21040070340d5001840126650029003552559407503030030700c1441004140240240c1069034643d01c5d420024003034503a40038003034004c02040b814011681c00440056001a9600c070900114854002980c44c00f421281c81041034854410300c1c00007c00416902c0f002a80c00b107054805820006213034030380240d4107580d40701 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 17773405 1250 17772155 17772179
    0x7080a110102010e0607050409020703020106120c050901090203040b061e09070e01030c05071208090f030403050a020a1d010611010b190503160b1206060d15030311010c08160207 78
    0x441100c0494081101014079038082c49000700c1c50b500030000d04514030340090001c06520590044800c0554081000c03024075100354480e101411300f240c90344070388101c41c1c108205128011312485100d48070140001c0f40e001d05a0081d01e00841d40150f00b40c0e483c0d15072000300316084206014407641180180c01050b0340d9951a8107150040c16640c8607415400c0c481000101510034060b040400c0c02401c0244c080000c42228910801c400945401e81032911000c65642c2801600c62010341c00d8440801d012050280102c3d025015a1089503080120360b503403030fa1400c21100144452518861000c010400d05d03010f03810203040c000010300005004210000000c4219603001c071544462110f03c3d509200b141010231041c94021034180342103002d20b180c01014040e5100d2a4240000b0b03101d6480418055242e81068034204800000c0c00d100012a694404401282c0e0f88401e1340010311010207400c0d040c0061159280b42c0140e030b514000280d880c5004250401550284041180300c0c02900141d0500619 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 17774655 1250 17773405 17773423
    0x703110114060405060103020403030c0609020d0b012301080712110d0204080304030203070b0306030a032102030f0609010b0a0e2101020f1c020301050906010e150f0714120901050304050708 83
    0x88914002030502c4818001240d43c0244242d05141c8100014004203421240c90b8824a81c4020f012640b040070344003045180c000702100911a001520001c00e084411809170240d4549250282c010320034020011142c02d10300f941c000340440c1500740c0315514121503030004030035207080c44c20070351410284071000f900320381c0158000040c1b40c10101e014400c6107418000c40b0000c0081001e030a0440c01d000d00000c0d01c4150851006041c00794004903181c913580420450320320f554001c0c4046480e40780c00d890700ba0f2290300480700c41d413203040d0000012462480580030384806c080242d461202c40e417818024000c51501c200e02542511040c0d407209031010314240014026000320029160f00c5039040c541407014000711407100160180140018020790300da04d41407c0e8040024a0f0040f651145000031034180c007140c1c0c81c0c50503404000502142c0305800c0c2e80051280d948910782e40010101c0e100300160311044401c0d0300341400c0034204520f804035840740001d990030034001c1007503034001966071306401e14200383e00e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 17775905 1250 17774655 17774681
    0x20603090f1b12010203010b0f030702070306050406090308060307030b07030b0d1205070b01140603060103050604090614011712040b030402010908030a0804020a09020c0601031205041703040503071706010b07031101 94
    0x305640b110350341840d110710300580030725400950035035040100301e50190140c1c220f1102c90000c0070000404c910700c01c0145000a6400c036100f00001d0419003440409070407090700a40c0480c9002011030410b0a0024040c0c088070703000580210503445400088028100c400e54080d401640220801c0c04143c032400300c00c50b0403072140c0b121607440c20f079460300c0e4a5580d01648505810070380050700d40820b40b201c008480c1d000c802440c00003007955440c40020020a41000003402d01854180640408c17906800302e0f03410380d40e600e0650240f900802031015a40e095810b0910101c0409000030019040d8080c040c6801c40e2050612041c200d44443c025441c41c0c101c6040580000c0110b024401581808403000015040ca428158034103107031fa101c1a552a0410706c001003400101140d4036102e281301b03401b51805001c0c16810b1010f003440710803400e81e030303604580500351203801000710000f0141110382048104081d04406018103a00c0c00345a0003294000103001c2d41440251005001a10801e100300702d82c000f0302c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 17777155 1250 17775905 17775943
    0x81201030507050a0b04031b03140c03100b06041202030c120c09181c030605060d020301080c01050903070b070203120301060305040606050109050d02040b04020d051801051f03020603090f 82
    0x356003461032038010294495406a010b21106003d40101c8000f11000e40790801c1c8000c1b00c923211405110f040355884d501c090b2800303280c41c844a1500b01c01040010b49030004a003103c0c0d0180a0107801c0048035946c40c031959001c0d004200400c158001c000031954403d00080070b40b0152174554000c10710351654070380030200136046803107588010700e040e103c29600031082e1900000c0ca040340d1146155a6044040801b04401c80d01c444025000c6c0709402c03910141001070700d200d41304d081f4500302034040d40007801034084034015200e01c3c3e03165500c9001a183c07402c4008006051442c6461600040703a07028100070381c2c06002d03d002484100c840c5c580118001e011030358002a0701d03e82418201c00300e9903590441d43c1044510401000310b0782d034640360008a10b8044500040f040364190008000340f15503034840c18500d00b41020003c40408540e28014030b1036100009100680d9a4260012030280300c6041106a90000605001600300840030f141d00c00407030421074004206440d007852400030200882008050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 17778405 1250 17777155 17777159
    0x703050d050705040b030f1005030111070201030605090408041503020c030412021c03050a0f03020c01090c0f0905061e06070b0411041104080304050d05030d050106080f13020117060d081201 83
    0x401071081e181e006882e072901d5400c2c141400c59603040f070710000e40b114030101810030100750f40080c0c040c60300000301002030003000304002c8020141001c0e044950240c0c0030900d840c80004442c240300110500c5558030840d51440c1504083e0720240c011844660706c0b0070103901340940c0302400d40410041c400390ac07054004c1c0c10014854410090322407181142c9401c102088840e440002c0d4101003911070081c0c4504100ba2400c03c4890214000c1c00f030984913010540c2400b80e04028412040850016907200a5061340d2094803a01441c042e1081954101d8000304000c1d070450745244075014090381d242008050b1840e0164949961200030800d81b010785000010525030010761505205054140e044d4490b8036007864034000e4940d449002720303c0342c5400340c0d4881181d1010400280704480b4100c0950804102075612500c00a2944004071445109584410301044010f80200000c412442c2d059607540b0214540050780685030001500090300701200142c038000103140140a03044003103c12140302c4040d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 17779655 1250 17778405 17778427
    0x80304050618010207120305060f13020309070807030308040305070c0302030a05010501090c030e06010b0c1c050301091107020f131527090302070905100b0f120c030105010c0f0204020708070305 85
    0x144002e0741c05030180c1c030401c840c00004401024241c0c450b800e41c100080c9580d15603021901040c9034152480d8000d0714609020031032842503024500410020040b25011a2101d038650750729002d501010300854409400a400a88294024450140310f1072440e188581d59502191070f080c06924112940c0c1d44071801800741105074420880d2403070031840c00b800703401038091016846400600541d102e4000028501a81600c10080d545500686019505a485050300300600d160404e0203901903c6083c03a5007540c00021240070703035a0b402d0f0001c4c1222603d603900d01c10800382c1200d1714401c461071504d46c80c0418851444140300c0c070003804880104a02c0c4099011000b00ca44800404501003618114000e0042580003460710140c1c0d004007000110750b00e40e146c4148040b10b25600400d5055400540b640300410158040c04002c481c03204003d10782e0701c5803240b41040c3e0000340110750000da1482008008036494684150302c40c1e001600040c82c240035520303000b203294404c04040e004107400194000d5a1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 17780905 1250 17779655 17779681
    0x6060507051005061c0206160b0103030e09010b12040c08030301080a030305010b0c1e03070c12060e060903030619120602120705250201031d01060f0501020304031203020f070803040506 81
    0x45540000401442c40c0141c0005e10a907010924180500d40c3c1c940c0410854403180112074680045d401411465142442d0182c024082404100c0009a0800c080c0c001410050005816036003125140c9042c080c100c43e1002c00c40000500030765551158900c002124813051000f18040c2000c00c0c00380400342c25a04000e025030b40103a20141c03030940d08008050500801042c01d92440c0706480311118503a801c414024130354014103102400c07a2401610020b5108096099500d0039881908180551490f103040d06840e01741c1118255201d0304100006501071030b2201b05a507054041655a0302c505032109204e0180b5072a81c80c04842d03541d070003c1c440c0b102481d1281c0e072540c0310742c4918009103012400607802c040140c02217000c0e102d001a003807054007160b010b03410030a0511840170b4001400034001e12418042c0001d40318138541c1315000030001c00c00d54404411181a40d401c544403030350054500008400941c4000b900d5140040144000c0340040c50000056009034000c5000300742a0602d03140b42d01c05d13 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 17782155 1250 17780905 17780923
    0xa0605070801091104080304050d0305190e040c08160f120f050402030114040816020607020306090a060605040605030c0603090114070f021506090a0c1101020d0614150d020c07090606050705 83
    0x38141c4c0510042044501c0001242c05903241030b99032a484400c5450252000e002740100b404039060840300011100b43d01c0401030100c00340844060028410041d029141c0399010355102d1254070030038a8403800c481c01f5001054449403146408800b803900e2031245000c07a001048541032141d1540142300039850309005007141400085202c40a904080c0c2c0c803041c0f03d2041a02020b101541312510300c095684e82d0054070085034010b001c1d01e503d80350050310944c4800c1102000c403032151401074045a141054464441510300160060500d60248010064190001001b4106035901c45540b0b100284484407030354001c1101344c03104e8030040103400000c0d060200101c0f200d44800c0001d02000401d1780c03100e40306500880c1b440d40001e07100702800307000c8808410b070701804085036000103015102181c09500003c2290803019682100f0120041006040b01e8150b40c0f8801192090040c04040e4803e50b004200310351090040390701c01a545c90061060b0342d040da00040105002043d1003050000a01038508 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 17783405 1250 17782155 17782181
    0x109200306010e13170d0209120102031018180803010f0603021303030e0117010b0c061003050a02090a2003090d0c020307090b03030d090602030603070e040209011401020a060507080109 81
    0x1d5030400500701d9411000038844802404c2c2c0541500601c600c00c400b80d88001c1c07584000940d60716141c4030700e0020b944040143c41c00f802206140740318005043c400d13640501030f10007484942c0c0d4079000042003c0c007412081a4015030f030b107007540e00c00d00c03118080c04000c0358442d00360b540e240d600d011209080c5980d1540030310140344c01000801d6824014034014015241d041c1884483d5418801c012102001003010451000c08009d001240400101010f082c0180e209400c50b40503035103801440307074030701072500c8010b0560f841034011030018a000350003158001d00c02180040c01000d11040e44604018610864003802c400006025801d1801e110080c84955a03041c56100c1c42500e0b404643e480c185881603404a5075126056441541d06108451090310340318000d101101190030150000c0d44161522442403140707280c000341944076428040c1c4030300d40041035421583c0c03074a8032109108841118250442c050284040300060303041c80703100e00402d0b50340d40e14080e40d0704080024085806203401c4c19 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 17784655 1250 17783405 17783413
    0x3030402030606010c0311060106020715020109021e12010c05030703060503010905060615090402031503070806010f120809030307050c0901061110020a03020f07030e040f0e0307060509030c01092003 87
    0x400981c4000881e1a000b8000b0300e40b2110030320b42030404580c0b100c84d0403907000b854042c1c00000151030b540090300206403001c801d0042084600f03000268202c4844010003034202c050240314045a60180d5a41585070030090110300c0180030789a1b15900311241002d0801c0462004070034420029494031806024000940c002c00c03006600c4d89a29903111001044c031803091a100303141c8007928401c40161205c8500160096480381480f002404078040041e14441c000e118404e400a401040010310504076104814406c050b141000e40f424512028040c0c1691121001c010500b401e890410060148500807406001b14005c000d0400414210603440142000102c40307200204550104020f02c9800001d500160381c0c80000304103a019001e64007060384050350108030302e8107041d00849103914142c80ac680400503500020802c03008c842e0441030740c010660080c480140010f949600540c1c101440e10112828801c1c1c0410700d41c25200c1d220001c0708d03401f00c20244c15400101c6d940d002c02548604070041c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 17785905 1250 17784655 17784661
    0x9090305030402041a0307080303040b0a02030601080103080c01110304150c0306150503090a020a061d0301020a090e0a0f02040b0703090e04030509011407080a110c010306030b16180e040210020303 86
    0x50403804050310207485075558080c280c01410080b000481c40d0600517050350100c40c0d5800c2801d403203402c100c4050b2107801c68200000e01d0dc40c4903200305e078442c0d801615090016425a01c40702143e8000745801c0200390340e101841004160940c0146100e9032040404071070702c146d2010300c41e06459071003400700c1c00d0500f800000d006040d882c81c51082c2021300c03860030589a81d90080780501d0001c0000010350400d0803000007090060348801620402000c102032401100c9030300342450300301e104803015200010794007a0305005a4400b50520fa801c48960a00400d42011401c01038003242c0c07250380408209440002d00317004045d08009840c0003007540c00442991807070940ca01800303910a44c2e40c028100300f0203107074400c420760350760055032480c9030401c00c902e803100d080b40c101038400c45022055030542d20640400446035031103406610142c0743d011582110b80d48882d102c01d46030461070a03102e1306000c1d4102104001c00c0494403010020107a40e21040c0b038a050900500c0310000e80e042a070703000c40d0010010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 17787155 1250 17785905 17785907
    0x22080c01050c03090c120c0103020706140c0c070e070819020c011d0c06040302131812030204060e100903030305060a0302130207110105040e0c070f021206150a0806011502070f12030801090903 84
    0x1e40804000a027009a0f44030041c0c41c11000401001c1c030903680c100381c0388042c0004800941d0240400c2e20324181220b182540710210f6000b1503d045801900281003000026500c1c2d0840d054070603541d4240c0030260411811001c1142034508802e2983ca00c4141118114060802085003042c000815521f442c40d0030308540208624140e52a18405000d4680c0e928241581d61100e06155164010040d42c103080d9110000074043d500c240700714800074001841c04d10862501030b001c4100c03c0000e403107074030b401441c2d07540982c00781000804480c0c0c040c200880020140c3c03a419142c1001084804006030380e1034181c034040e03d618040c0c85109040203c1071000340b007403224510002c0c2d0409106100ca0742c64044c0c40c40c195003541c1940c6070094001070045048418410005010b5000704207c03074020360421004401c0c0000000203114000d6a41d001d50010050f1441c0b111001004104a105841c4001e4075114040c901403050781c0440d003212504c1c02c2010078113500c054018050811080113021103107254030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 17788405 1250 17787155 17787163
    0x4050c0f09100504030b011e05040608030306010e03070b0c10051602150c04090216020a06020c030a0b18070303020709050603010606050307030203061f02070602011422080c01050c03090c12 83
    0x704481c0101111010b081c0703140d004400350340040d9403100700341601c1d42c1c403485100c219480346046044106149100884d0601e8a405035009603540303c0000e43c150780d200001120b046159941c00c0e5050b00558402242868102c401407100c078041400900241e070312020301c0012a80000c1c82d40190070784c0c40e40303c0070250f940850300500d40c040100d04400c031610342c05d040549074820769100102d502c1c800a41c0b06920548205401c0e40d15000311045448150348050986c0c5941c003250300981d01d074000e0141280010b06041c14a504542100080d054036080d60182c0c40c540300716508150056801000c0802c41c18585021350307640103105034028040b480c940b1401400d1800058008420705801200180790750f122003c4040300c1034140c42c0282c89170050710001039190340c201c0c0541310055082201d1450410012480e587c000e12020180540391383e54000d044441d2000406c084981c0e0b641081a00b203c108240100d03409030043d2004503680c0e081100e10f851070110f208800500981c1300c07071160140e580c0c01207 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 17789655 1250 17788405 17788417
    0x3020916021603030203030c0a050c0709090203060a0b06040b070501090f030c0203060c07020d08030c07020d0305030702070609030206070b0915160807020109030206010504050601030e01020301080102040311061305060703110d0e04050c0f 104
    0x4423801c0c1c641040410603281c0f80074100b901c02d5984580c01000074003c6a030341210f01e813207009500740c41203038071590a10000d981076280d003250003d400700030410440401d0001404c00c54021384c00041c410200d079540003019980c0100940000b45080c3c41079040d45010302003540c100c900200d0291406602c4c0c3e0100e041e601c00c050700503144110200c0014000b2801310200c61469900411410310100c1b80e107000b4003da0401e9580700014801c8880c00306465009114080c244ea0300202102c1c100f9616030b0b50200c00b004000c104042500031181c1c9078581a40d085841d43c003602d140d500c0850a1030074400d00619064004020740304581c1843c500170007080e0080b03042415998181c401080e02c2da1034600613809400340f140d0a00c1c0e950301c000000503020b60103501078010307284900c0915556291000402c22240034404e60880d180c1500401048a480d003100280202807090405440041240e40c02ca0304043d4103801943c042100100300c60814a06441001e45c0900010252070030550808a00c80c40c070f010709 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 17790905 1250 17789655 17789671
    0xf020d03050402180f0103050706020a0201121a0607050f06070c02010804020405041b06050409050105040c080a0b0d060906050601120606020a030507080408010c090602010f050411010e0a0302091602160303020303 93
    0x60404101035440d41e4843d2400e0204c024090402428180c15224a0710024803040d5243d00410707001041c160b10200d0007501683e0140d44040071081c7c00032515000307100780111144111107500321103407a45c90b01005010060302560242c090040c210181300c1c203241d8020503540400c41c00b610505c006070f07040740005401640582c1e000506646a1401030000080009881c544030410701e000980d40b6070010042054400702c040c10f1040f40da0f500e003400140c0d00d4030700c0300a010036040d81c006400e148540d4400342140030000c00410041c002d544843c0f085541556047d00c0864681080040e40e50300245040458846038208001303003441e00000030340703400c0c000070002d081041c001981414000300e0401e5401601e001d42c000c101000c2641405032001180c1e00c2880059400c152280380c00b100b0702c0c402c2a108035080307001c40036160025801101c211170509102c941c4410b0062000c005616959105403050311661600890186200c3c0041c1c40e101c40480d1600d401c0311540402d100003a404820399401c4909 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 17792155 1250 17790905 17790911
    0xe01060512130813060905060301030f0b09070f031110081b0d0f140f07020102030106020705010e120109030302040f1a040b070f0b09030702010f020d0206071803020303130302040c0f020d03 83
    0x90301c9140202c00782426000740c03c1d54408a03100d44019031544202003100c0c240e8560102c1203648100b4840340e8002484007500359102d4510040c0481c1c0ca1a40c029400910070040c0d46142d0b0715103000c2c011492450304180c44a00018101c0f5440d800c00302407074410300509040072402890454551040f5004040368000c0662000c100405503003000e40144000c9119000306001c899101030061029440480d11f85108c11340490215101030b0043c4201d034180d402c980c1c0034040d860305042c010348610a00c10300c89a0011010082d0000b1311a0a2081640e103510035500540d40b5450700750b007000d044249800c060766001d1004040403044015130100d9085901044207142c80d4010390130105034035001602c01400c0040c01d40c0821810150100090690034400d0702c409081c0302c0081d008176a10780c0c03007920600140e070024003c02ca55078003821f980c0511042c000c1e020300f01c0b2516075000c05c0c219000f411078031481c40c803550400e000710301d014040e00c4849400c51506101c1c52034041d4000b550f0340b611003645801d040d5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 17793405 1250 17792155 17792161
    0x3010b0f010e030c09010801090302060105060f0306100c080d05100501020c0d02130e070f0513020301050f1519020601150c0209010314010b0a0303200f030708030a0b0405010b040602070e01060512 86
    0x2028810000d81071380c000d1880a8035a55000c0c61400390800c20000c40050189400208582c54a48165a65840c4030100700d82155030b02020301460348038100e081e200380051003c0510008294034010045610b95400101d16810710300c2c01001705882640207181927421030740b400601601d400d00794450240d0110740b40344200003070300e80704d900418000302c20306c0c22405005000705070604c29104100460b03200b0303201d9a00425603040318800700d000c00e00641c0c1d8002e00581d81c1c04d10510740403c200243d602c038019040d1401c82c101750721b44205441e861010340035800440c01000840f01c802d40c680c40c101c803941061b40c0040c1641d0300003041d100e81400010090b24131410034200000d1700350300c294240d250151904a2154407428003400b8640407a40c6040e0b2907e2540400c2041007004c228542c3c4040a07600031801c01e409943d480030150001400341854030b43c1c43c800c1e411181d407140601d500807ca0382150300e41e1a420404000d041210030740143d40c0c90100c8800410601c2e40c00700c2144d0141c108091a04060b403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 17794655 1250 17793405 17793409
    0x1008150c040302030307140c041406061e0301090c090503030307050412050c0306040605060f0a050f010507050c0411030403020f010b010c03050702040207021917060c070326040804090b03010b0f010e 87
    0x8020764102a4051201140020800c64152525010143c0c2002200c045c0e0804c0d604200564035110419145105210081400d80c209000a4038904554604180070302031070441040d1950000d030b000c00e00c02c40d160764184107090b0f00300390321401400081c0d002c0c51a614000708040c05911843c41036a0360041804030407070501105020b414801480182612268182428408081c1400350741e900c0c451030481c20f158001c0d2a2207803215003202d40260404054402d500c0040d250781d00804006d440b81d0144a0004110b0340e120721510101410447d42c2a813030f402c0c1401e0080c50110f0001c04170740560b25014501e4001e03230704a400303500ca031a414038107143e54003107510104001e07004001000750840b407204200154100713061180016111000700121400c48030a140503030f03640c000c0c0c5d0b80715083e90f410003c410100b84503280b03404104214004101126038170030300071580c4002c1250240c4119501280030700c0f810404e400b82244141c4110024410801490001064070358440b10050600c80b00e41c692405503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 17795905 1250 17794655 17794657
    0x40f0206040b0d0209040c031a0103020d0204030206070b04030f050a0c02060723010507030b030a02130e030702030d0804051608060604051503010c0302070507050604120f020103090609080a02061008150c 89
    0x6000b00307041c065160422014444081d402c4205071030b200d2820590112149442481154407000c034180740000107159000040d0002e510403000c2d040815002c120101c056122a00204003480c40b03000020054030341824001d0568030b44003039603401c101007004460a901ea10548036030710300e60100c900e66551042460182c00c007034850b440302e1540080282d859100210107511041c800c03a801d440a00c03036481d1050405407100c1924400a51103191900d0030903555a40340d024840010001d02141d2515010780c000038584500c64034417000248a6900300030401c8410320041803582c489043c07012201d4149150f0f036888400040a15000f141d4a0000400080050103070b25030029000d4000c01645c102014028060f41c080c0c038084c2d503039220300e810005072810108125821940003c90320f10304e23450142e4420152480f050420390400d45c1b949210300100e04a44650109103104134076203540c90548040207803d1010080100c00c142005c502c04018607480131503440d032078400808a1042aa40d034407440016 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 17797155 1250 17795905 17795909
    0x20c0c040e01090203120c070b0304020d0606080703030e04020703090302040c0210051e010f0e0c070501090c060302091c0506070e040617161403122a03030601030b01050f03040f020604 81
    0x481820301c0d980c501c0d684810340c80704200310b009800380c031603001c0c0c4010107482e41d21681c02c258100da8826501000b044400c00c014542203440184018114a10f0780c54960a940b0b451704860070f0346d00406010001c00da0060f01e4004400700a0b078042d41007241c00e440242010700c10f4440640103c3d203c58605d2242d40c424812117501c25070000c030030480c0381002000400303014544544d01c428a07400f40300114480f080c40100e08202c6205800d550308907511001034008a17007104004072099900d61465000203109803520f80003911065030300580b0744001c001041052484011f0300c860400110305407101003840841c400b50701544074144200300760001404140142001c1d4401b2541c400c107103512880c1c4e44404100301010710b13102380041042035100c00e0503030301180b00c142490394990b010101c4030701d0050040d0082c1c02c240c440444013300d80059442d080300181030400195085800000c100a81581c25101d402c480100a10300f281c104084c442003c2d4543c400504050240e000b491001d600310344e119822500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 17798405 1250 17797155 17797159
    0x10c02090a0c0e091015020312010618120b0406020c0f030409020304050105010e090c0d030e100c0201020f19150e0a06050402010e061911010f09140705090c030a020c0c 74
    0x40c840c03400340004002041c00c0d184041c00908034940c0150340386842c0c00034500550101500b8130016160998084003641104220001d50005015012050a4007a18103000349501c3c1c540d1082100f00b104011f44c002c0d480c2e04401d400c8600c800103640410030000182d0313401a800200107a5440004401c507240220480c041c0c1c20f5440000303000704e07045200b5000756010306c0c81100248074076604c641c01c2002118048035003042503480310b44800628508055100d159a019013030408c21401c100e40031aa0305480d03948003102040e504034800341156410011a0a0000c00402a1030b008070311010303c107840080c481c00903144a155002c800300000da558080c104070a2034a080f10000f01c140d151010140070200c40613030110b01c1c0c010146c0c002e41000821200c15505010503d4180c03c0281c90940d050543c41c540a00c0341c1d981e800c10150b01000c030740320704c0c0004c5000790301c414151009a0610b80c80c00010780c0003035010303464480522290311900c0301520307008556100003684400f4451211890503141c5c411241d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 17799655 1250 17798405 17798419
    0x80a111603060b0f030622031803120915050a030f06151d010e010c030c031403090703110411040501140f040e010305190507140a1502030301080706031a0906010c02 72
    0x7041001543c040410810190341c8010030301c903034104168445034100c0b1070346100354514864580112010003407814440c800e00f0110140788074442c00094109980d0402c031003070302034004d0b42d1440c0740c3c100e090140100002240030720080b40302c1c2402010381c0512042001419107440b100a400591600510090015100d40c541001242c4030001d003207000300514100c0c46560300111501035403042050312503034441a10382c4218001296070813160490301c404190100003451000307081c4130450b00021401440c484004000850030740c2000c50303009200c01c0c1d10798840d038075156900b51440c0c8200b00741c8049400034200303000c0c2110356882140d801d205140e00e000d106480003c0c00f1450129149030141a00e0007803046401c00e00c03840721801150a04080081c0817580420b1040011842001002820102c080d1000d41c02035540e15104070380c6e106c40704400000d17800c04801030021752010881c0c5c3c8000c18082c41c060064001800e02400203104200115000d018008001640760b4003a40e098440d003a4060800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 17800905 1250 17799655 17799659
    0x30c010e010603020a0807030c030b04110405010b19030501031109041b0635011802120a0501031421030604020f0705010b0f01030e030405100e03030c06011a0403080a1116 75
    0x941d00034030160001301c1c0301700e02802d4041030b4400000351380c0c0c00faa6407200d6078440d100c0c19600d80c520000402042107a41c03000380000c0d0316513604c8074001c190003000661030480d21582074802a820300c00720441c294040500e00740040022401000c8035000080040c3c0710310009803114204040d03040600d40880c5101106274400080069000c00c899003207810b42030302841000c041e040301c14482912164101e0101c100c00c1c00602000c0e07000481c0c1682e20092080c01441c000c030783d0300031a01c402c03c00c0710514001561341c801003092000e041003103181d0201c0c4002600c1e21038403000c45010b58010801200f0703403c0b140817001844e25260755045032000ca116966098807110f1629001e4080c107000103030140502002c1c1c050303882c654080e018001c005001e00d006035013868286000d0142107200c414084041143c440755102c0315840c20f000074000803000001800361913051695400d00e00e0703003140342003502a4040208101050780807040d81c408808915140e1241554400c2e22803418020312090783c0804611400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 17802155 1250 17800905 17800931
    0x90312050405010305151e0102030d090f0c06030509030a05090a030209040f060c020303060303040e04170712030b0303070c050405090c1002010b040501080a0308012904090b090a1a0d05030c01 84
    0x1d44100e500990301032202e565108040a500e98011484582016001054034014602010241c40e15041031040b42d040043c415054425540f00c031000303a810a00d085803000501c0351584104000d0081c03424288141d040c80701009940307101d518500420028081940d000c03668607800911b000b180c00801614072030500381000615401c0c502c000700d8031030b4503040f400c085450000c81602c0c4600c0c4004d024604003807400950b070540d86030082003102d5406200410031001e600b03c10141244601900c40440440c1e60100060201c0d038042d0711151181e4820b1085000045003a52620255a01a41d0203d17680c0c80703000c2c1c101e00e060400d42445a104441a0560136000d50541c001690403c00301c0c2c0034012a681c0760b900507161001ca100290000e490900140442800000a0004140000301c2910000400300d12a0b0543e000341d0040ca00054640c400384c0c4043c9440c1b14183e410810010080101000322060081c00c010070b0911203012f0300c40030300043d040c41800c2c010f640440c0c0da00b00090000080c0964 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 17803405 1250 17802155 17802157
    0x3091603060507080f04020109170f06011202031018022e020102030a0c080405060a020a0507060c26060d150b0a03120906020607080c0d0605100c15020a02060103110109031205 77
    0x18101d001a14881c009005e20b0410f420007801103406854070345520b410421200804190240e5001c510701c9039003001e5009041c00c102aa000380216611813010001a1042505143c400358242c500e5074284070700d221010384144016507030180c2c101c1e800888005981681042031000f8051124940100e441600007142c042d0000d5114038603c05003002624030445056803141c106071009003241e0700800c00540d208003280d00404001419007803044c200b41c2a03941c0c40003030310002e0360141c2c0007a225002c110b001c8a240c517240882101d20141e90703403291074090302007140e0342c841800c00b07425001c0c4c00e07401000003160369008c100d144002900001c800b40d04da050441c0c035200095603010008456010000e0030501c046001e07400340d80a84c3c2d50441c20f4850824a0815400c0044207030207581d41c1d030a0010f02651000d00e400c000100e9510307103900050741742c00d02120000b000e011002005004100c1803021030b60218409040d42d42c004204580b070808003004030f4248425420052856011108080c1c5960b0000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 17804655 1250 17803405 17803411
    0xd0204020a080a0605040212040209090106080f0106150302030c16020609180103020907031404030e0f09010e0f07030204060c0b0a0e0307030801030b090d20120d06031502120c030916030605 83
    0x41e010b0104c0d0765201e05200c01c078820910300d17405160000b0301040040c80c100c81010780014031580081800c50300d42d403902d0705040703200740f00680e01da42d42c01040086d042416070040e1800d90304c1c203046056142040c02418036109400130035048429103445141150b60b054107503000048080c1c480208e115134104840000202800180d104010310f9001960041c428081c0b50b0144243c20911050ba460769a800e031600390003007201550200e50083c1090541d299207500398000e01556102d5103281c2840300e08195074080141c003410415004000901c440d41c0c01544040d481c03688000c0b82c0170280e840810f0100100300c07092a00c5180c3c080003411109140c1c2c041c0115051303d010f0380c1c000469440c0c0c401c1d46540d8000851000d404501c034403014500726802d68a20300c101c66069001ea40c500200c2010310308080e40401001010540e8440007032090040c00d600305e514088013410304500d0801000c2c9441151100208400084c040010004008100a20044007441c9606401c0e1405648034505440506021 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 17805761 1106 17804655 17804671
    0x4020d0213090f0312050f0c04060e010201020903070b0a080a0212130809091f0b131202030304030c0308030103170304030903060218030a050304060306080f060601030b0d0204020a08 80
    0x1058645410703922a680e035102e0b802c171a010800403200c0180009280e00aa681000444140b03a4200c0741030701c40500380004c80e40c0009004034064400c02c1003035901405280c0002460794160800340c410101340303884a03c4940d40307054a5104a0164450321900607152001240e2480c20781d0640503591402000018900380140b0082500d850b03007074640f519115003c030040d10700d1416001c3e49401a1103d400094941090b0312a00b809450840c0107221469040700b9901c0c0c02c554082044400456102d2640c420066803800e000034a50024030041d500082146150700c505004881180c0c0300741e6050b100ea0b5541400d58952400a4103d81000d1a00440f012900c0310903030760410200710200e100388003c43d55035052400c003d0a441d0309610691240d40440c240c00d03a61100491071542c490000e10b00000c000b441903000520311703000040c0107900039100044d0b00d1107da522101441c810414 = true := by decide +kernel

theorem cover : BRFrame.Cov 17625905 17805761 := by
  have h0 := BRFrame.cov_init 17625905
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17625905 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 17625905 ≤ n) (h2 : n < 17805761) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
