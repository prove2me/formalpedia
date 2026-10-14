-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3423
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:37:13.141776+00:00
-- url     : https://prove2.me/submissions/022b6622-ddb2-4e0a-b5d4-fc341cf4c5d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 615467625 ≤ n < 615647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 615468875 1250 615467625 615467647
    0x17070e130f020c0309012a0b0402060405121c020d0206042d060204030210030b010518120109060b090105030c0102060403051c0906091502130b030c1315080a0924060b 73
    0x900b40b001c802c0e2202ca002e8903503407441100480001f64401040d4180044c141c002400c4140c0c403680050000780010300b400d488400080700e0030300348480700420390b10848591458070a9003d80d00712685070303400540844560f41b00040c6d201c00008100501e80400300c155521385810342800c41c2000000100c0f04c80c01142c003494144000e5205010136481050080750404010344680606c185506c8180d480380d04010400c0904820820b54070b10050380929145041200b41900344a0200741e18080c25011900f03d0b80d6401f440258841038000c14000d4100c04450004c60740c000440da60825403502e8180d544001c01807a140c920216813074010009805c0c50700e01018070a4030f070000d140303890150b42d030000b1034400c03c180c1e84103d2048ea814800d100000071810810304541101543d0720420300d9126514109907a80c0307804c0803480700e0f008000c0e101c440005140b04294005415a07001d100d80f03404101e101c2040e2039202c01c2120050140d0000044801e0303503c4400c4d0385400040c018900e10f6041c540361640c000c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 615470125 1250 615468875 615468877
    0x3090204063b011203051b030a05131a0f03090a120305011401020f100c0c060527030f090d0201050c0d110111041202060a110d020c0117070e130f020c03 67
    0x3805003102c1e82050007030b00c201c4030320305200f8100d4148407030b0340000f242c0310754041e00e05810101070700c0c141c0d8204805002d0502ca007480240b0220340c1c5030b030b24565500c0c012096140c4a4029400c81c4407150f0001d0805000100c00300126424245006034003074403a41d441c0d04943c40d0034038401008140034600303905450000d4068016505030340700c5107400142503429500484c1d5400030030101003280d071300100800d80d20382c03081d80c080300c0c62070007601d425940c1c0d040360303118102501ca060320041d082070f007020380c1e0345a550004402e0100484500300034514224000203803600034004d25400d20f20842b080c0e01d100086a0254080700e48a016070702c140c600b04500781c64064041000061440c2c455420701c03403510b4512028004175015502034500080c04040250213200b4141c01801c106010f000703c8800310051003001708098a041d04003940102141182840010208456507031400e054800702411700842c0c0740c0140e01c1521054041e40d40181004c00c800142c40540b0041080009851000424040080b8080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 615471375 1250 615470125 615470189
    0x9021b0d1205070c03080f07021002070807030906080103151a0306181c051e160b10060305160c03020c0d06050f0f01030510020a050909010b03070e030601060c030309020406 76
    0x4040240d035031881c0f0140c4880c2441d0748002c002505050019080140691240f90000d030944111000c0301c010195901c1207034000c82d8142e40100010402c0010150310141c000081d00141c501850154034503500e07035180e0703080c120301040701e40c0c1c442811043c2c1c0c2441c00d0000e002e24000030215000d0303080140b115481c441d144006100e06008614107601904c8040070b401c0c0d1071880e40d656161078420360304485171103d5844201007079507600400800e4a0101062940c15440b030150450b034400c0c0c03e00100000720001c559001c0c50a00d41003208010340201c00f60100c01070011a820221190303c0c1c1c03460102e00301449030400b02d40c0081c8124403801489040d074803007403041c6c00d5540c1415041d19104004c4074141000d120090940e07008036a0302e5030369800c80d00078003001c006a081c2107080081d000e0000d035490209800c0304144481c04001c02901560040440c1002e03030307080d0050901941070050051507401821006400d15454082c09021501c4c0d42d4005401401080c400b0829855544410b1403080181 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 615472625 1250 615471375 615471407
    0x327081f09020627030714090912072001081308070c030b09030c010f111611060d050610030c0f140c01020301060201020703110c0d030f03150b03060307140a09021b0d 73
    0x3144e81c07607030034140010304100740c548030141c02200c18842010072078a984010441d40f101e0040304040c1c1031001c442409800103a01c64612070a0301c243e84043c5852412507144150304000744035007403200003c0740302e0700d02c43c3c11500300080b40d80d81c0c00207040c00ca0200c0c1c803a500040c00d040d194000c000d0090b5000c4051702d50030350324400a020f40c84100405109813044079052180c81c0c4401c000318029107804040784030034035200340c200c01400320001001800c15000750404188054850081007480c0c9840c442c1c8880b200901d060400140c0d9441400400041480480d03c040c002114440d140c60f00156003552003178817241c4000e654035a141c4500a02139004034004038081381c0d801c0c2e0000ea1108011811030b90b0498050501c401103041c6450480e030229082041806255031001c0080246407110b00407030140142080a41c0c5e241402d0050520f040720031307880402c041441016202160342c0d01d45580040300c107440f00242e100d0700b0101042c107000030785900b8840548200c140398403005400c02407441a600c0c103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 615473875 1250 615472625 615472687
    0xb0d0b01020102072a08010f0504020103052a0a0e19032d030302071106030a0b01231206220614040c052a0a0327081f090206 55
    0x196401a0b00342e018030800140390840c840b0080c0b0442e208460080b020580010080300080d5803810401e00312060191900d0f0341d95221020401503503018081c0301d03001840154031505200904400007d00440b450602c44600d400260840220b88120040e0411b400000c000404807003d070b4040f80560445403004880c04101034034410001ca020310000750364002c4520b0350080c06200c640c0d0440c000d601200040342c14802e40140900d0030b032100d2000c0d6102d541008000030fa040d2680001424810760b0a85940203e842c038140e030030f80c401e040c4060ba002591601c02c54030060311802e0000d01e001c0c00c0c4100e070b1644005041211800c2280c40c1d0817500440c0c86050000c448100d9000920003515100c01c0c08a022031000c00507000080b000d4200003030301c41c4180003260b1085070203190752810420180000c7d000140050303050040c0c3c0f0a885070b80b40a130b0100b132040940b11454007102c071703071030b0513086400704840e04c50000e14541040c12074110340d490700c2d8024100c507030303501605200d04d00c00c80c00d11441e03540c1c501d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 615475125 1250 615473875 615473891
    0x2040b12061f06052b0204141503060a060c0f0501020f19020d0507020d030314071d06030f06130e0618010b03060103030815030102070f0b16020625030b09010b0d 71
    0x604076002c20706686196881030b1905240c100c0c118052614019000506500c3c44540b40702005a0300c0988003801c0d0602c264101700c80403004010401a40078900350342d1940c208248001e540d910f000300401c030780c02c1d13081400c060310003030402d03039080300d85e02c00c007d07005500014882d09011181001800700340c042c00000551001001401c9961303c1d902a02c0901240c0200440409464070540f25031001d8420b107400702c0c0e8012605021201148183c0e40c2101060040d019540c0401c916030b10104195000e48142d802c40c54990301403c1c61040280c11603000305e002e03049202c5ca11603d500909440042c040427940d80381818585680c189152184508155203008003940d80f0349004991203040765015610a850340e00d800c00c8030243c18001d2001a54999800c101050000300810f80141e2954000c10980c1c0203450600c01042c80101010020303411900260b0400001040300407a00c0c98039050344a42400507030122205034010f04c85100ca03180c0c84040c00e400020b010b00c90000501c0515028102407051030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 615476375 1250 615475125 615475171
    0x4020306010e0108100203131a24090604020901140a080708010611070911070609060501090e03040308040b0f1b070501031104260316030c020307050a060c030c02040b1206 75
    0xc2c030038010002d540d000085002c060244c01d4000d1751b044522030001c8050309840c2e03a200840e030070641103451001c03483d0200300008840d1910250152074004144294100e1009000840c51701000709400d114070b5020554a01d2640b241c2c0c24000110100c0c21216998000c1140c0500054011204240040e400e00300105d41306104001031441110b601004bc10010708003042c900180c40c83c0d000a44030b000c424400000072034500d00070850824000c3d42c0002e131650410110005654032004482d03d1780d801040100700245102c01107604071241682960340b5400d542c42c5104062150740301404086410300304010000101068175411100243c0b0b0800c504d0340c0d07004442d07000340030f94494005483e1000c08104903805044039494001e0a4a002b901d16181200c0c4114100e040101000e50024859480309021400c08101c0c46010705021204006454948100288041c2580c4001401c20429100c00b004540380d0b9000824640d02c01000c00c11604240640c0350350720750702150610b0080900000c000040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 615477625 1250 615476375 615476399
    0x102070c0324021204060902190e010e01140a270515010f02061b210c04090f060509040f06060e01060c0201090e0606192309040e0c01120e030f0a0302030402030601 72
    0x40c1c01301029910342e03102d403101c00c010240c0c03000c281d8010445012141711540c0a2811002603c0700d5203044c4095410b0084001204005820030543c405007004078000702c0d40c0b402c4441049414480004070030440d4a0518030282810181e41c550060510003400b09016802805613501c030002e0342c50907403a20000e44126a81c100030368950b482d001190f010144c1000c0c0010050081c03140c8613a000200158814540b60700c00012190f804001c00b01140500a48009000704507000c10500030620000381406d00040d02080c014100a0040d01c1d00c4074008104060b6800030070051411041c0702c0b4240d83d6527800500b5171450001e00f02c0c00615420780c00705000020340e108038003600300940707124104402a40d20040000301a1015404d2040d45c2400c40508034421300e00f403600c01c00b01c0040903200d1300c44e50184020340b1750b80806c0c8201c2c1d800080340d944d00b5903406556140d401e0200c21000c035048418440c090700794803e06400010514002032000000c0d40c00d90001c500a81c801d404544d1030383c0e6034070090091 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 615478875 1250 615477625 615477637
    0x30b0c3f0412200304090603020907140d020a0e090406050615070b0c1308010c170702010e1b0406050a030c050a050108040305030c1305100c0605062403090102070c032402 75
    0x101c00000155160700b41d10808601940c0000500e00101000c640d2100520f9a00503034858207480d51500313424400c6040601c0356940090301380c108038002841c044c840c00c00e14014051003168455010410b11018ce124111a030035a03040681072190303906140c188000074003021228507000d80070300c0714250242880314080b039030510342020001d0142c1e00d8210000c207041e4041009101148420310002c51402e8ac28031030030f6040d100c541c88445e031480d6503030350000c00c4003001000c80e000e692400444040103d80820112615817008004219084031000001d0061103160050758000440040101c1005206001a402d5481c03c41e01e04012a6840300115800601100e005001460901c040b804d00020031000d005d868020075420001c040d12a000f2032801d24110b10038030f00040401c0600400c3c00030600c02c3d5a0003034001d944084078003000c0b002940501081c40e007510a0700a00100182403d0001c1d4107441807607600200541d07600b56241024040c03108290008410080224140341c5510114802c41e50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 615480125 1250 615478875 615478883
    0x50d0e0f040f05091e030f0d0b0a1d060609010206070e12030a020a050f0a081204061d0a03030b030115172b120515090406110c210c0601030b0c3f04 65
    0x440d04600d607d210415070007540003a48429111044042a81d4600710302002521403622200101c01c1c8801c2c40260f03445000e0320305800383c1410008025140d03070201d102c075400300890900ca00344100d01e00108190f10740080388540103000102da02c0c02e0f0749a010a01080450050301150030301c181d00d141c45a1142c0365100000d007920820001c0d401e4000c0760480c0035521a00400c00081e80c203130424100d4102c01c400c5200c7c016280c110591100c2099050310807000422001c1d0b00801403030402803120724000c0f18902030310ba080c1c0d2000380c03012605801004140243c603000c20440d8440e40e00c2c1c10030b00d460f10607001c10100120304c1002c0c034400c00a15904c038091199402074500c2e4610203840c030900036908405131099480c551501c00d4505034010007030042000d44100c0e801000b4001e1510780303a03000701d00b482014803034030ba0303003040300108003a400144181034980020003000c01c1d4454038281d480a2040c0004000401314140100800d6910300500514086c0d00781c1e00400e84040c6440c3c030384203424046030020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 615481375 1250 615480125 615480127
    0xf0303071b060204030f080406030e010b0a050415091107260d09261308011103270d03021801050c07060f0c0c090501091107050d0e0f040f05091e03 65
    0x2445050844079266224080c03480145001c1d100d0726601003000c03115509030340b2580300007420000140d051080034000180341d8000c2100c0c0c42e203403001455500240c401c0c4d510454680080940503150615941d0040424841c2000322507003401401c0000e07000600181d03210075030015a48414412540408078464240245514200491144c0c1000305141a415100d86030b14143e0070b244854034480c4c094025140c540301c50340f40c07407450b0090b08000c2c220f0340180a95906141024071043e045000b80ea4001c00030072403500a0718802455105e21656090310b846940c8580d40950701e500350180e004201d0114280b109c039002d13224050042d0b405204055075094541e0280108024081c410840000201482e1601500d104082d403035a480c3c4250b070390400b808441d610401003100f03c00511840015881c5041410300b440300c0e80d119591511400d074031680c00d0207000000143c80b507032051080c40d5030500003001000303c0340c000c0407d4001464101c2d0540d0b404e200349401030001031203590402c1c400049803c021 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 615482625 1250 615481375 615481397
    0x4060903020126091b01020106140d060209060f03060a0e0402220f0603050114100b030c070501090f080304061103010b0720210c0109030816050a02030105090f0f030307 74
    0x1140e40c100e1401c05284919901d079000d600f80c030381c3c2d00079090046507480d00800e021401400c02c800460343d100310460542e07140a504018200c0740a600480051382121200102252410100082e100c1c903407059601000010354100640601c0c00550300410060300c05a03801a107986048038004010b0750007943c8010307510004640034080250025004034203020100b05d48541c02c66040590314541c00481d00303a51680402c44202e5080c21a0a43c00260030403801450307803410600c00d2603031001400580d8440e00c0051410300303200094000106959004592519003002814295034a82040d981142d4071821300d0031009a04044a0589040e80d003e4801a41f81618590381d54540c0e035061003088450340904003e212182e507404020b40c03014070349450241034104031a00c3c02d90030520b00c40c1c3c1003810322440403c1400072804090a6556561100c491641d8900d02810325078500001d0442c000d50541c240750810144c1e80b40032480c600444140307811036011032940030025859010889002e070004c0c107804d075a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 615483875 1250 615482625 615482627
    0x1201060e0910150e040c050405031b06040506070507051903060e0a0b150f03100917030103080d1814030a0905043c06081e1504020919050f040b0c040609030201 70
    0x1100c004062030303040138a0b2100c2010080b80a45880c0c0000c800402e201103001c00540c102407100710354160105454440e00640c42d400a02c86000d54000e1a0180001007080d50800008014640152500030074810b000301001b02c5141000c0c84074042250040c2c24034000b1230411000080d4455402c0d0302c6514112a5038131010062100803401120a0340010210f080380110380f0280040300070a174541d81d01240c1079040b818000801000c05111040c1c500e010801000454684403d450a1420014000c80c802008030701e51645c20031000d10141403080310b11800341580c68000002e083c400641d17200e80c10150b658038104401c403010310301608071580d0586e0f6103900c04503a600c03030400d00c064a45a492082c207684c04980040714525001008554018288030040c20003c0110958120f408ca0050465801c41c002406002e540580028010004840400e0b00c050981d41800c00e0124641c10410075440c14503500c00046000740c9003035506071100f9022800d2910303410211020b8407104d0f2542c503c6245140c1c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 615485125 1250 615483875 615483899
    0x102010b090703020c0703081b0c011d06031b13090506030c0d17070515011d01030302150a06091503060b0904230312010801090201020f030a021e01020f1201060e0910 73
    0x1054603c107002e05440400008d401002400d88034aa0002841d00c0000610381c2c48c2c03829411000c041d052141c40080c1c1c1b4107280c21051022100341050307494036102e4540d4002a24000d03000814103102107408901c02070100742204c400800c030b075882e180601c4980c403030409042d11340d180801c1d15900000c6140c203010214848500ca05044200302800301c1c50f20506840b42814030385984600c481e203480c1a0010810303030910803520031600580b09072490055146030b902a43c3d46005104c0300341d04c4088200014601d1445030b014500400c0d5040c000e210412410420980602490208071002031810400c2280c13401c02801261249610002c800000307400b2503031b40c0b03902c1c042c1c032124074440d48410440b0044c400c8010f090f2600802650001245250740b520019082400307110b0884003d034000e1200345021070340001c0c4141c14682508503c00d40c0c826035181e031800380c4950b4a80d2029030100084845070b04c8440e2590034125a4560741d204403450040c0c0070048846016181001c84850155007404a250700c04 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 615486375 1250 615485125 615485137
    0xf1905010b1b070e010f030605010f0b071202011b030608160f030305070804030c0b0c0606010c110111030412051c021c0f0e0a090e0c0603040b01030b04021801080109020406050102010b09070302 85
    0x200c45080d84d884480056404c000d811800800307a80d10001c00800185006442c007400d012402000000e041c9a03948000380900388000d408080422607014099000f03500001400c540081c00c2e4a0440c6005409006810b50b442000039600c5144a09506400d884030000c054030140040f4402c035901e50345040302c60781c220100c01d46100e241040004001160104980014044900364549852401605d18180a002002d807818400340c1401030000400409043ca20b050090a018000f050724003502c07451030046402040c02c0128528010042c400c0c0061030580001c4402c006541c1a005904201d80312040d56040c00b0030381c40e10303841d60001c02c0c2c000c0d11002035800b034600d06145002126400290304070000e6001003200c030341c0c510fa00c0540b05000e206101850b00d065848c6c6245040a90703031000d8143c01440301601205040001c90304560b1480102500c4404ac0d1403010710700d5031114400d0b402022a00c80c00ca220703e00d030020000c2d09500601803202c0c444401440ca03441580e80f40ea00754041c2d032142e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 615487625 1250 615486375 615486427
    0xf0708010605060a230412060b10080a15120f0b010f2405091305070206060d05070e06031203040309050a1d1b0c030a02070306060e010308161a0f1905010b 68
    0x10b45c42c2d031680701c0080000e84020301c0500d0044629990320b0070f0260888400c4240d06014110340071101e8001070300812180c2c4c200c16481c20008288810980e0881c2640071070b085441c50f804000c1c8108103204420f40c0800c411030050b4008441642d0304c5000c070301c200c1c189120354144146505c3d40301e808425030b4001640040301a0806501d042c803111300150340740c2d01c445240c84482c0d40e51000d000300c0650400140b903004100f61109a171304011506c640760388030310504c1008104aa030400145141d2814001200081003503040241c5a003400c1c5005084444140642c9000340904180006c44640201d114250340030000c80d080890340300c4d000300000304880901300c0d94603120108848034042108000406a18403151b014085103070035854503005607040c8ac0d100c1e018120040006002041351032048441510310045000c0000c10350b458014040e40c107082402d40840c0803001040014160000c0300e03481200780b42c110200210702500c4130000c8440c20b024420b0701d490207001c104590004001d0501e01c01c078038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 615488875 1250 615487625 615487667
    0x31c08040807170325030608070902030a0204050a030b0f0a020712080405070503121e07030912030e062109071412010f020a0306080706031a01121d0f0708010605060a 73
    0x1043c62001c100760300a031040b50320640e441060711000c107145031040014503110314007400990316205407543e48036854040c0460480e400404100300e10b0b603ea040341c0040202078518440d0302d90380c1c101001e452004903101005101c0b900c0c006440008a4400c8840c1983d000014820007010306504681c003a400030003c0751030388240c86c00030601e59030030040189507080d041c2c80580d4803400c2c0c40200c03040450401c1d40c1c0c006003000380308120010790803a00901c103031070300322040740b10010306130030101d40700300b0500206500140c0004c0c041e525558100008005941e011075815510786801404540d6103209206140c0001072006598106140c000900c00001440c3c6001060403204038031810308a80c0640c490f0000b00b0303569081000720000910101d40180340c0e030304041014090011600a00a070b18036030b010304011a00203001a400d02550041300440300c0301078074050460b2940f41050f039805400c4d4000d0500d2081000006540d00d0500954060702c90152851742055143c100170f0b15031240c1549020b1f000c0907 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 615490125 1250 615488875 615488903
    0xa090903140715110a0e0102070f170a0f05101812050306030a0605091c08070e06090103020706180b0c0f0d05070201230709060801060203090f01021c03020306031c08040807 76
    0x5060060740320f2000c242d00c01507070383c980315003020748551b120124050564000704001c00149564004900454904000c0d801512800c041d0650500c8480c140042c8850904001d000500800003040f0311081c2860500f00040c2d50014400702c1840c1c0003d41c010a00c0c4180c041010fa40c510401c0a1a0060000b0b42180e54400d05952590146c82c1c0c02c84100a03a0703484000c0000326201c41c01011400e1042d107040600a40c200b42c0c4006280c20092240d450181000280c07003029a407280d4100d1b505aa0402f0342000020f0402240c3c9914240b0008140c521a1489001c508500c61100403111020310704051149007400c4128000040c0100806000035956039120795041104001401d020380f0345481079028103807408000142c41da800e1034001c481006030020043c0201500001165180e03e005c07a030390b06031000382d040101d1804858078070825040d038090099001a40c0c054025500551084003514200003012400e440c0c200250004040047c405d2008203000c40c01c1c0d84001c1c507000340942d42c3c0e0b1321526 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 615491375 1250 615490125 615490163
    0x40207021f231914070f0f080a110d050903030403020d080909040c03061a0a030b09160602030a0e030c0108040b041b060f17270106150207050a0909031407 68
    0x21030800c1840c82c0040c0051000da20b03110010001e46a10041e0070300241c0101e54440349000c41c0a40341c0014260b040101640701805541a0f2544105a205224950302c840040004140e64924520401540714501030092524003a20a0303440e6404040c3c011418545590200200800b002c5c9050f90b070127030104030600c450f841d0030398502d100340c1c001e5036007c0045181d40f800c01c04503105071030f9100e42001c03501c120980594031806034900f181d40008070842207444a010090606110400706110010003d0002070360303a8011029000303840c010b0702d403081e0304c00481090540342c10204803114000b60740840046c000421b185072050b040b038020920504800c0b010f0804005546140d00038401044616800100040c1d01512800e146030740405d0a080c10304142d2007087c0c1d98800d06110203d01d803482c03254282c80b01801d5000e4402840140da60051443d900f007006500c0b280035015050240d00d10744408100c8030703d580201c003034299250782c80c465403840361000e82c0095001280c0440d00700c0c420f0400700310b0340 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 615492625 1250 615491375 615491417
    0x11b1d0a0f09050f071d10030b0d030f0905010302030405062701090c0302130b210c09010b070b010b120c1c05070909051023030f0a081305040207021f 66
    0xd82100c0c80700142c94140350030244c0d20b82c2c0d070051410301046261014200c0888141c080000d6121b415980d5030010800ea800a07000340c03000d1150540c00c00c4c814103003402070592011108104901c151142c106164a401c0110268401120050200e9202102140400346420301c1c800980c003030030360b18100701009140070f1420b5070204001a99814030356036040c415858004061000c182e24458200411803000c030100340085110420b201c0744207040304295515040900c00b605103960004c282c003c00b0347e142c0d580e0000d00d07042003d003a20760301c2d01d4400109020190208a1303107008851440310b001135882c3d4030000e560358025103a2401e030300c00300060740888001074005c444c040c400707648408030241c2c10030040700b04481c40144a440005008581004041e50001400100031003410205212140c2c10004c289006840d88410402c0d11450002c1824400644041c3c2010b40d00d6000015076a49e584003040300340d00031824081d51088528140300701010b203002c14103801100c1c40c01c4c013502c903058a1100c11a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 615493875 1250 615492625 615492629
    0x40b1003020a0e060913110108071116030b060108010302030a0b0405010912020102070311030a090302010806040e1e070806102310030b09060604030803010308030a180311011b1d0a0f 80
    0x1140440b105200042c5404154035038860b8480e03c4076651280f954950b00c0c7c030b480c10300d59414140305495010442c070b40c0c4614500e0140c0c0000e002201c00001002801c00401c142034401502e049003c0707004150a50301c07403035100303048030f1f0010003c0c21601d1054032104840203000d081100c466684030000304c0010305041e010603107580d81d600010784581047c05c02400d480c0c1480e40801e5160020818080d8481d0011034100a1b2502881c02d40c8030341d5610004a40146120041c2c0105440385203481c507451090003490404040299058501450303030fa00089688240645581c199a03603450304c103006100340886100b11684e0b81d2a0600c0d41c2420034404078804040560000d00029158a4008003505008401a81110307081ea019071402d491f50300c0d000c01500041c00b001344414000800300b5010010354100004c0c4002800456540d41d10516004d0000c0c006024440030950030403c0450007411494031480e450b00c2552281021900c2c91481161072008451800307502c01403180002c14521585505100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 615495125 1250 615493875 615493889
    0x30f0216171c06050306060a0f0b0c010f0911150906030f09010b18072d3204090e0f10020d0e06010f03110d11060307050f0d0f0e0312040b1003020a 65
    0x2070f81810f02081c03609000340100054010001040c0402c40b440d08000440c0c00c54100004850701d64002144490140c0140c4035041d020764107080300d14040c04103c40700b90748c10450031a610401d500000d0000480360141409450740b000702400018003009404d40181d500c1030b408070000644c911071070300040d109841c80070301c800c142a141c2c040000080e042250707110340000e515200e426074400708207980b5411880340f00407000c2004944407a500725407090004080c031030b01142d900d240f28911b2034502c42c0e2504030b841010310060030007040510409001c520501107058240207031007080791502669010303601c000200d520365941d50030400c4001400340f01d901d0192454040500e00c07a8a1401c00715000b8942c003000a1240090300c0102c0001494820f40d4140e00c402512540d449070f841017419503090185d5100a0300c030110000b2006139050035a4043c9080d0501407500304001201030441698034013030f0012400411128a0206001c540d1f2180941d50000b20944102c510303945a50104502c81d2040d40445 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 615496375 1250 615495125 615495131
    0x8060106091802030a0207022e170c0901110f010203060102010b061c11090402040e06130506060a120b0d0f03020d0504061d0f040e1b060708030c0d0e010c0c03030f0216171c 76
    0x790310000c0403c81d84901d1b42a515203010036603c101c882b12201c0382c010b813065010050014081c0e12590080e01d21000a01001060b200d154034411561400f07540222022030055103005031044141c5016003d4403080010fa00d8038204290110390610700401c50300380762120387c51051003803981d1035030f660004001800c0041e558156505042e4140a017200310b0a10014099062108010709516441d0a480c81d914651900c892005145501d02c802070034400022a00402902e04807014003844419140e0090712a0b0301700d58000c0385e4200200c8090055005000001e41c5e10000292244101080c00003810402001c800010700e42500180c11560b104542030026089034075000034502407140f9007503001c582682d65500e0004503139030380340003031000a140d80d00d00000800c50f0b0b580048961b00c280d0061a5040c0200a44580c03250080c080449144045000a0900c07003561005850381c000c1c1c074010459480c1706586c0000c02c0d0b42d180c0702d103041c4c50501101404144610392290100ca01800d0f10000100000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 615497625 1250 615496375 615496429
    0x1b06020604150b1518150403020d08070c030512040806070f02030306060715052508130201032d0501082509050c0f030103110f0405040218130804090608060106091802030a020702 78
    0xc0304c00c5039111000340402c0d91047c04104007584a0713000c008121907001e0b02c41c40d0f130303640c40789442141c004a40d04090000e102d10030082841c0c0d000c1c04020404d881c0144101c600c2541c9202d011125502d01c1e1501400580092000c01d10908042014203c0c0794400d81d03002401540351445013040b0399044603285500d84401e41403000c001c40100d03410740c10042900d004640d41c5401848100084031803030000f810983d840105241c50103011005401240ca03003801100c0185200c0295000b60400f80101000350141400c4040310644540c0b22062540400c0410100180f5000d500d900601c4000e0003d480d000041042101c0d414400c070046028500c80c443c0000400503a101780300c481e0700540241c9015515100c14040944d80d21001c50f42c2107020101c1c4559140d90340000441c0b200c0e41c0050050244c94082000724103c0041c0e00040260340d241ca0032603406a03070740c0e0811030f04103034107100d0b01c440c102401c0241080b10380380d9001198000010311000d450030f41654003240c0034401c44928041d0b4441c0700d402e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 615498875 1250 615497625 615497629
    0x50f03040f0501110c1509060304050616030905120a020304150c0501060e01050d0f080c030a030e01200d0b011b1202061f051e030a1b06020604150b1518 67
    0x1891000e041c0c00c0c81d002c4e14004803001c140399502100104644500c144505420782d140c4000c0807101424030241425449041c14585250382d0038060f80c403540c01d014124564041e40384a4411003030b03259040303801414180300391030100d41d05501a2400d0b40c214041044081610f8078120104294104140d54050385890345050260840e0f1540e0041d182e040280801007205daa1400380440c003842d0446900d81c480e4600b0700e0403c200e40714003082d00c409800045401c440443c1c06900c10055040c01130028032a0240040350881866156070440119140030700282c14202c0c41a0702100038082c0c181400d0702c00840d000b44c2d0070384111100c00c00720762803070000f40002c60542e41413200f9038103c20401179403014600d4013000101104110700500b40181d450800c10015040e0041080c0b1340a031000d400e45000d201c0f5420030a800241114441c0100f03a1401c2c1c0c0029601d00c00a0194407607600030a920740e900138124070610140400c44a1590b110032040c80300c4115005013002840d1218003207070301c140e116880c101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 615500125 1250 615498875 615498899
    0x81e0112060f0516030c030b03010f0204080f010203060306041511030109020a1101050405070b0a090e0903070c153c120b03070b0703230403060519090201140c0a050f0304 75
    0x4840b8525800e007001e2221344103845055408015071810045410300340710104030002c20503459095415030a20038038500103d0b959004006480d030032030580b44264118034420303081c3d100503510a50194000300000e80420020300e000642d000d5646004203682215010000d02c0c2d400a0b004403000c1ca9000600c2d402d1076030800c4c04554025000700c000e00c441e1505490b21925800f491290716800c1000049840c4400c0c8214605000340081c0c0c010540f041c204034000c29680e81018404488805e9001000b01d060103000d40ca0000070b0041da91203410700c034048030040210a5400750002d14981ca039000550703c001880d0201001c2c006140d94181084030210311103000da800c1202d072503000380c0040006000c0e268003082203c100e150142480200d07855030f44000b165180d004000c0c1c103100100414040100301c040e4105501558400001008030b880002c5400100e03a01403a00a004c10400501d6400040c0c07040d020f44042e94200c2d0a490100b5a00e03201c2a08107281261104543e4000040500c80014140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 615501375 1250 615500125 615500141
    0x305251a070203090a08070501180e1501030e190501240e07051603080f0f01050609040915020406210e1f090c140109051906081e011206 60
    0x10822004041151640a032009400d840000d1488030800010969030007001141c180c0072028000303141003541e5009840e03d03242036024090000d8407490800c0304c035030a0303451001e0580d4103e41c03403804140c68039051141303001c184c581620b040c03640360958541440410710500786c0000d82e03600c21044500291410608564007804200c0061401803100c0344040070500c0030200350342c2420040e1045480b034000c203880324090412111001e043c40000c1408042d40018401d000b400350305944c401d130343c807003450740e0400e01003d024640c0c0040d07041c0850303503581c60300741c1010102130300070400c0482e0f0050800b00354082c0d078072070340201000c90402142080103506092030004a48a032071410020596400021134031204058000380c100b41080c040e01e5004403296100d05c2e080369210041280710303941d03508200c0403841c1906815001c030300298000103950a00556030240901720240c81d05943d41414015598800064003001e616403040c403205420800360b6071500d01800e0410b0084e0b0b5815400d140610599403a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 615502625 1250 615501375 615501427
    0xc06090806181203251e050c16080d021515010c020409080c150a0b102601151e02030301060c03050405030d170a1506051c1a0411030c0706020705030d02070305 70
    0x180301d14540d400d9107400c100c4486c02441c80d009644441e0002c14600c0c2042c00c1407034944545440d50b000aa08500050103158a209a02039403401000d0304071080016000b10ba5030510200002039081c6150f12510200c0b080741c0c40100001400b46841d128023715030400b80503100164080841c0395445000198004c0d40001040e0707043c0000752624001c02e4071a03d901d00954180250411340803200300000780c04244083c0700c0f1f030aa0740d480d82d6814400ba01c0d40f40016410000ca8030001000d40316540c0300c00754201e000013540045103103903c0d00c3d40c01c49525004050580c1008014000451966400c1c004846040c046507500c140c44804806110859000a4030000351240341646032041a2400c880d90011a0642c0c1409500e6640302050481c2030810080c400110038900b1101c1010710308410755440426500750790411800c1a4000784644910040d2490b161502080c0001c00000f1a030703400a02c01188100300b500e003000c400c0e104500990f0410746044000c00c00c01301d102c940c1c0968850b41d0314480804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 615503875 1250 615502625 615502637
    0xd05100503072c060d0b070e04050106261003050102040b040618080d08180f06040510110f090f060c0c270a090606080a0c030c0609080618120325 64
    0x800c001c0d0001900c0420f9407142500010700090750f45c0e440020f0010003e800090718805881d110000400c1030b04d2001550b4402c514101c0080f0305180f00702c80103500d8402d00101c40024000810140000080050290542786006000480010400c1c0080c000078502c0701c00d2162220305025001e400c0101c490b4040b50b05038483e0310100a030000001c1d5404084090342855040b40d1101d000742c0400700d8481c1e8003140c06124040c640c0143c10340c0002e14502c03440c020003d66011070f0000398084181d619050b9000080c1300300340700c0b000542040c60024210000c0081c80c800fa40c401100120314260003628081109800c10b400b4009941400390300607011280e004aa480300440281c00608521310142442104603999040c0e041004501d07481203014101590440700800c0c2305141200b010140b41c08200c4003c000100c3c00601e09001e41182c106980d8200003601a0703503141043d8106c18111b522040885108401ca4507410007441e40c0114010005020783e88020408920708100d4408030842c002d08110b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 615505125 1250 615503875 615503909
    0x90c01020d02030703110c09040506061806010f0806031e0610050612010b070606180204170a05191b0f031407080615030c04050703021216050901050f0d0510050307 72
    0x2d808802c0341c12003a4981482ca2003400c2c40b41c4050320741510b40c61803940244c13650060009001e00054224420070f0125035884582d00080c08240c0081e009903540d40c08210a514142c0b8440d00480d010395101002034216803109c0069840d038601c0e04121042e4505030b8000c40203200d6880c0c0207828900c0034000540d202c510705000101c2a21685405100720804d90074089002002c00207103421580080030440014811001c400b0400c600070f610911078110b400081c000c440380d2070100481c00d05400d03600100030703000c03030300f040206c3d2229020f001d6011201c40400007410312800000e001010080c2c4100800010100d065143c4500000d44510f0308012903800540c040007030790000100e20390301202140c0700b0206040349201003860700304c04046a40d449402c01c2c0c100050706500d640036055184242001c00c40d10346580241140400d425024180060b0b8100301104880d4021000ad040d5800c55100351032410310010381c400b048441c181d0f5941d40c3c2c1d9900804c20840c5240c104483c0c0c01500007000382c465110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 615506375 1250 615505125 615505127
    0x1a06030f0405061308031501030b0a08010605100804050303130812070c03080a0911150705010207291b0a11010c021e0c06031603110a1817060a05100f0b03090c01020d 73
    0xc000103108005582500e18034221f40d174031940020303030502405451880700a4850800c1c0d800b0b0810381c041c2c6400f588905001c0c07a01d01c1d00c00d145c6d0500072a0400040c1d0310b9512000c038061402c4070010303815190080104403a48003000d00d4040e4a104d0003c503964074940c00c44600d00144150303000f80188056504020380800442d083d90084901450103c2d000d100710b00c10a82d5003d0b8034000c00c0300103801540b01046002c11b00484030140c46260911410381501c0c1d40e0321122603a01002c046da051240603482e00d110020030025a07004101d4403109090400c0f0320b2070b0b015541801d540c0c0c403250300801a0054034010240207131600100100445003400341660380d0542d0003103803850000810004101003001c00554000f4060f911007001004103000f010355884140c50302a116201444100041d802a910006104100310039502d0314201194040c059589800140002801002d0f14005000c95080400a0000345140c000c4004000c41125582ca170f00d0264101401d00300c442049906541090201c121a1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 615507625 1250 615506375 615506377
    0x60510090e031207090801090c241b02040209102d1706060d0608031c0c0504030201210e0c0306011a1204080c030d0207060c030b0609041a06030f0405061308 69
    0x108020315400303c0c1c11342d81c458040713805480a0b4004400d40d46005c0117641807220500e4481c007900c0c060a0b41196076005500c00d4102e00700d40c19038850019004108100c8100e20345502030b13401c640014000340c11301d42040d001450021450b041040400c0f00c81544282c19460720400300b1402e0f0f00012a64120032030054090329201c42d00501081464407240000c0f1035a035001c06a40b0240103103c0c00304505038580054664941c0408140c1c0d00b42c82c40301850308940740d0300340900d11241143d5a00d03542890314550056034842f200c61420812025100c0b04241e400c6554460170300c41c0500d840080400003017100916081102c1a08500180300080800c034120702080c40c02c650080c20229101e41c004d64070f60428155a0240d00448807480c08001603020ba00c0300242c02800d507030350180704104032800003042e060f03049511904400303800c4601884440310078986680300d918010391301038101d010308083c00002085c81d441102c4068142c181d03002403100f07000c01000780740c1c1d0103003030584406a102c0e42c2e916000c860b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 615508875 1250 615507625 615507637
    0x50405060c0c0a1211120a02070506030702100903050406090518040807030224010501031a0a140102070803041d010e01231c030801031e030c020f0a0b07060510090e03 73
    0x18401d0006007101c20002c08020444a4030341111032042c070190340c500010300b00c019040304940944100c00f500407030311143d50105d90403010710b50024014079181c20184015904000c3c02e0100b540503862050707040c40030381d008400c0036500c40d550340c42e50b0b54100031001d05202c4040d00110f0164a60303440328000e003c21a0729203a042604051a03540383d80032464100d2402c1d444c0720021011004821400303440c440a004000e060341d009072400e006040325140100d645d491011140381d400516240e0030002200800f00c020410181071068810f1151904001c80c95944103502c4004503030030080080c0d01c020146440c45016100c40140700005501d4021102203001c0108102400254038211400441d070b40c2a410184180c8010381e00030000c40b00d424003402c40e04091106039102006040c0d59407207c0011144a1303c641d0385a15405a004d20940074010b2001d003e406041e04030184880c04581521341d2009080041d10980001ca600e191500c41140542015884a01068106103451200c580c0100a95507 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 615510125 1250 615508875 615508891
    0xf03071e0506070809010c170619030212280308161211071403030106121104170d030b040c050714010f09080408010b090103080f070c03021002010e0c09010602030f0307030b10030603060f05040506 86
    0x2b549040d0b40e00000d81c3c5032600d80c0000d501100780c142d100d0f0f9404d008035203100207111405420821120070b2820301c400d030307219090060002c1e00c50390004095a4400c4030031005191f1500e0110411208510380504807004240540940c48000c00c01d60b0401c104898140c1061b00e0083c0554115403510601902801000d11898035441d1503884104100c2941c0c0140c0c2c0050008248003d048030f540540145c40e0450181801c000a0400005c0203442c02c06000f00b950002180c0e4840d40781240544841d08680d044c000300c200c0d2075403240403000c1121540d0281e152411701880c4125030f2285842c40e07440c00c5803404140795004a061200400100341940d0589007500d8820016a40d00d15092034000d50110040d000254402c004010095880380d056006c2c0c804c10200c0011903440038192000c000349000240300b280010b900030414010040303032140207150400841d0601044d001004000602190b42c120f05640000e50b0f00d000c20001d00c51103005821202544084c2040107050545800c0d45512005042803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 615511375 1250 615510125 615510139
    0x30906050705160603021c0b28080f0303090d0306060905130e07030c080106050103110a111f2009150a1704060203060a06020f03071e0506070809010c1706 68
    0x40d041c0301090280c51001c02c3e03100040280b85813038440240080d00840e041c0d80c10b4074024405607001c03001c14460400f10100c0200325a0f0040305580211219611091842d404a440305000107a0f4000c1000040307003428000d0080d544030300c0c207c0502850981810b00c04802c041c03c1000c2040f101350040f4103a0241c0702c0c1138a5144898078810038a501170308440050040c40c1c4a0202e0000c18400d228025509840900f0001d010b925514401102034a1aa1403918070740041080f403001d01c2400703000c0019902c0750315070550b02400301c01d009184412a10f0592089030613107a0ba41c41034080d40c10905d0503040c0c24600c000d031742041c6508001c80c00185405004044a00c0d0020700c50010ba8028500e852002840804090580c603062404502940040d03c005002d80301585000c10300341d0010030503159000100c8002c0d0b082c20800c0d2551003200b501c03107031007140441510058002080b001d0042511903215034440c618541410aa0302d0300b11103801d0308000030082040304290b24401e1420f07501e85c005108503021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 615512625 1250 615511375 615511387
    0x30406031424150c06070f05120a050a1407110606121519020f0d050903040e0411150304200603060d03030510050414040302060a1509091b0f031103030703090605 71
    0x411160f0550154501000b84081820f080789500058000e105150071340e02c210b03a464508505a94a0044454850501c0003102c000b907a08030b0154022540326000110101c1c4215441c40d11140d14001650407000288509010f407101e980108085a04100c081e01c02c003910710705400ca01a240c1c1d0210300c80000c812102d00101d2510040010300246411001004641c1c4201c116001c081551181500741155800e040009442c03d0020040c2d40444502e50020358103540d6647d519020150039100043e4442c0c601c4c06000026040c96010b51300c9503110b1840c0c030401c0981070301c0b03a8400301c0070041c080b48030b04020030400129444004c28642c40d1581420046911303200e0f40b50340041001103400c0550024642030020715840c901c0c80c003080c0110f01940950310503032980142d20098880d540d041c0808620061410403509883d6480f10101d94010650691403250480c100c004060a0343c5c40400001c0052209000703005c03a080f018144d28070100c0003545015802c2e94003400c429030900c11502806808079134 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 615513875 1250 615512625 615512629
    0x3080406120b15030627070e030f010e0c010f0306080706080405011a010e0f040b1c030f0503010303050a0c03270f080102090d02010e03151e060117040602130314030406031424 77
    0x103003d0070b602000c0b105c2c0d5041e180800005223002421541248a44100e901d00560340c10f061142400c014681d60140102d021004019070b100d080c107480000130075503200c8000414090031320040300513000c60750300c41206080a080c0399007525490b00407000c0c803200c90300c050070075a03070004414001140d00f42e13809038103241d586c40040c0080002c0c6001175004802c10001c0e2400b5441c5209010045101e5141d0000d100032100c004c03070341170100f4013008000c50b07130410802580703d0044050010301482403520190894440745812042505040342c042e1074030411506201c61002521901e0107446000d000718208120000069210b00115201a0500160000e0b0801d25201485284940060701d5041e407641d0410310120f4141c0000040340000743d0040c1c40100e02d1562181341184950380414040b104144c50340c2e11650002d52005000c543c0c0103121300320000000f014485081746600340034004c0c5884514015020301034605100f0100d00c90f900540400800d2580728004809044d8130700541d55101c804140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 615515125 1250 615513875 615513919
    0x90c08040209130b01140907090803030403120209190302010f1d2106090601030b01150f031a0d0c03050c0f100e010c020402040e25021e010603080406120b150306 71
    0x4000d884c080703544c00003080380d090301070b8100104141130302c406c034007551450380440d8016031a008001151300b003000484d0209104d0f003920720400c503503840010314019000d40000c070b101403002107921074640c6010040080d0342e0402200c641400c02ca061508007070319072015515065480c40d220134840e150f44c03648100211002c5e11045051000c1004031201c0d4149001007656810342440101c43d504815000411400320700305400760004003d0325115104201c80b102a4058000000919501150704840a50741e42d110000100124000e402101507a42541085030a0a00a1102602446510b14403031250340b59a0b111905400701031401040d881d0191004a07048900744401a60040c00402c001c00c00c00043c0040324020b001320002c148041c504c0d00741e0551051149040c540c00758201b4907100070460030210240d00c0740840706000050361502c076542c0030a640c11076008000050145078070b0340305043c205c0c460300042c2c410464103070030440d01d480c200b07078420310000305440e020340400764110444074882e070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 615516375 1250 615515125 615515161
    0xf03060e0708250503010605060d0c17070f031a0303090111120d1e0c0e1005040b040b04050a1409070e040b040501230a031109040305071406040c090c08040209 70
    0x803c0d203860500c0c100f0001c41840180f2070680c03a040418a00055030b1605200301011a0f10182a090070801d03d40c800303000034090414080c051095002c08415040807486000f4881c010a40740c0e00721100646a000f812a00031184103d180c0850001040da5558000143c2d101c00b80240b0300500c0341690f142d000c4d401c14100c91449890341002061b01d004580c604d8006002a04048003242e03102200d40d03500001b81d411160080e40413036031181c0103142d1810a081001e441c400e0306c0c1022440c00d40e50380900452607200c1c1e4001191200c02040502451a0821f4008020721813544100c9100460300000b2340d462030050a0001406030b801340724031040d207441c0c210780f03d1410300800030049580e58041e44000c44e00000071890169048034445480791a00c1a00c01c401d0b2030308841e00061b040326204c18050b50410190098051107801e03c000d00002d01641c500c1c540302c018501c050941e41c1070174038001410003441e402c10340030642001041ca25590303008000580c416011144d0b508162512a0040c4c1000300038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 615517625 1250 615516375 615516389
    0x3020d1b0e0a1406041e0f020403020607080307140309070603270c06090b180d020301180501091115030601181a121b1c06150206060909070f03060e07 66
    0x62003044100015a40001e82c01c22058810f030140e070351440104011141284250420302d490385650007088001a4020380f030500300c0000051600303459070001000c58001c084100c400031400420030550741c0d40a485c80384040012030030315055013003c040240e11004180651010943c0e111200341c480300302c2c80e07030440b0107003a541000c45584540d405d0085111076240140d030003140c15100002240300907441100d10030140240e400310440980000c004420300001000d99140d034903900c020858129888076492218407441c000210140c07140f41c170010060700610058402c5440b0043d4100c0e0358139000440368000d800346081300380c00b41131500419608126800940541030044191800540d040700109240450604030700c14950303401c00d80c05000803040a44c1040500f00f0311140003903c002203040c0880198800010441c180c40b4289840341e020343c08030306801603200d01e06226160034081001a00404440b011b00811410f0410390103407070383e1901c030042c43d640e66103054602e480d2007400342d10003820718 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 615518875 1250 615517625 615517649
    0x11b02030a0c0303020a0311190f0f020415030b0618060d0c0e010816050a0f03350a08090a0b0c0702041b0201090c0e1501050304050a02030d0503090708010603020d1b 73
    0xf6402d000b5601c202c0c4c0e11040b00882c05070040c03403c1604000400044088108c41c02207402c102c5a40e64030354107034496104403440d010105032100140d03650301810402d8541c045400841e030f440d40c00c29901100020304882e0282a003000b90008642c256401c40360711a1b000d5138446600da0203442c160310480f52a5010300c007101c1c0003000120b0546008509000031034500c1071010710140c3c580d4100310100b0401d2203690850b141c800350420028000c42c07501600b07044114050302400024102c40c150500000403407045202002030741c0c40d8032507000366105820100071401000012001e540d94036208002410700130a0f1100861103d00b15912a040321200c0401800d410500032680c44011340030b442011350030ad940326070030000803c00c203000c83e0f151071082c200101408508852600151140d920182043d10603014044101016072810031007920343c1007003540c0d03c0760340b850807818445c00d0044640041600b030341482030403c090394541c0500400281c000709601d03084403071440031800200e00307a071110190303042c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 615520125 1250 615518875 615518879
    0x305030f0c120a020c0f120a0f05040b0403080706050106081e060f0a0e0115050f090d03030b0402070b01060e04020f0f1b06040b0a0501060e010804150209031209130605011b02030a0c 80
    0xa180e0003805c1804a21021a4001076100b410140c41d4010b1009405911806100d02c0c42602e2041024a021841c0c81c181245401c0c0c03100c2c24031002d80e06c96041903452403000241c0c1010032034248609801408280350661060070208900382c464250316180024100d01e01c004a00590303509903501c81c030000024164440541c0da0354100c0e80382c01c0240f140c02c4030488441c51000c0d000340203d0031117402c04085408189800310703800403c07080148140040c0d042543e6101d00b40115160b5200078040140542c01d0205d040d803401030028682c04000740d030240610700501c400c0c2003552a0354150f8600f13242d03048003240c0365a007042480011841444030600a44900d4082c04103208582003004d004100c1d2140c203110710b80c0c075000250740c000d0a058001c2d0025100200080c08201030075100039148080d841e01600e0060b856001a00d0601c813510f03040451107000841039014a4004823107040e603680c4000600283d4603200010340741700e02146178091140120040c9104564003803100e1200b070b0743d01c08000400340f5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 615521375 1250 615520125 615520141
    0xa06140d081e2b061a0703180f0303020319110c0904020f15040305010b0613051903050303010f080c03010b0622080a080a030b01110607032a0f0206070504030305030f0c12 75
    0x644461010303c0b100c0c40d140004c600780240c02c0384041542c80580701245400c41c0b660301110f95030312840c51011190320a200c081103011402c00307504021030103a0f0085403074210f001d0901c000c05611481080901c042058081906580030511340380c00e6800300d1703e04100d41d41e00e001051207a65100c9910317502c030043d4000007004280301070240060f83d0054000700070308004407040c07000714410040d5400084102c10410066860b04417000e8008a1401c1e06440d03446075660f40d580e107107410a130003031101c200c91410184a2207400b005059001c5904400a0005034210f030086805403181101000b84081c3c5100f20072100403100503510014102c14042b1400042907040c031500355001120058002400d00028108a41c40351030020092900080681a03a849401094000b400042d1039243d40c0174002d2680381c0041d0302400501c545210649910340940c0007514001e0410780c004000e002401804d1109001207135020054940c00388001407070310456210284035003194003031041c000d01c103403070004e0401c0601 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 615522625 1250 615521375 615521437
    0x4150e031e0310140d080a0c020a06030c020d0c0b0a0e0a150c030b2409030c0d080c1c1e03060308180f010e030a0605070c08030a06140d081e 62
    0x3400ca900f26050b40340d4441c81051850400c132404107034080d2400540001081406c0000d20201c1c9803800d100300707040045e50108160394100d40c40352011a9481e00014240c45d018020306503c45100d1a0039003052150756030b200e2080030007928031000d0704c0d9200142ca14202c170030052401c045d9007002003006045101802070000d0810301d850080068203101c064609410a20b0215104000d103101440c0c001e4801d00c4294017540000d040350341d251140303100c2503109803900050b0110b10b038010803140e5915881240101e1410682c9044400102407101f1485004d036130010150b480240745c40361001082d403014000302c018203042e400190040000050b1018000f2024a0b41e094082050320681c881141c1d003c015034022500329641501341c2c210b00b504100280c01340d070007150b0081281c1003040240c01c190f22403943e07a410032290600307182c2c1c0e520814009000001503142030301e00c0c1242c01c42103420203030341c1e18a00c0d40280f40644502c10402001001244024000e58100f000417003285000104107104003414 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 615523875 1250 615522625 615522631
    0xa0b030304270b0609060a12060b0d060302120a0b04080901050d0608031801051c02030402030708190302010b030a030504030b04170a031d0601060918020d020304060209090f04150e031e03 82
    0x1261920088400310704120040d1a80c1d00001841b050501144403420349164507620b03601413821f83d80b124041080650b80014007038684002000044850440c4140203005032011031080c4550f002d4100e401c006100c04d003483d9801544100d07696251420580144c4490103407110352800d250078103401003201303000003003d8148403025103190728101c5082001500d85201d65041c1061002d0a50b00180d41180c09030025604941f0183c122850716640307070180c0d0700b00b203204850f0130400030f107041c0c0300014182c0c240516140d50300210050b0540000307603a4050510b00c5184801060605100c0000d424000c000400340462494400400c5d40c030044144000c0040c4512249041100102d445040044034000750003410303078040c1d45508031520308000c0c1c5200c00914406d0300c1c075042c41c0c00300f01c20003106100d400654080c3c2c0c89400050b0300c5010100c200300e440d0360028034518003515100100404034481800d04207152004120014180c0c01169005040d4841c1005035102c041c24041d0026921400400540c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 615525125 1250 615523875 615523949
    0x3080402030d09080606060a090909060c080a0212072615120c0603041e080a03061401051e181c0b090d0f08070c2109080111030a0b030304 61
    0x2c8106240d4109445904160044290541c48040000e440341070450044c03010071417600384800c0315030703039007000318190f0381d11080840d80c054881c0501c1e4482500303e40c0464016941010540c2032012030081c1c0c4213943e0300201400c0402082401420400e025100400041d4680740c880040c140b0b0681541004d9201d6411147d0007810460000354906001003402d00903014000c080d10300d1a25039459142206000d031006030702c0c110a080310034000a102e44020f14003038440d03031408140c0a282c80b26051a410100450905020040220310b041c60004060003481102c6030b81890f485030700d6000440342e07540a03210f426410041000c0303400080b4404141101c421072082c01c1071600c540d40c0c0d1011030b803903040c2844064042010b10307121080c2d0038001c3d00060350022803860440d40c1d41c4a141c40e0301c18280c481c14906016503841c01000310071140e0000b181d0010b4843e0400070300189250885418552100801c1002150741c0d400013944c0c1a0f80a0080f00d008041445042c1e9211403500510140071005611001c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 615526375 1250 615525125 615525133
    0x304030807021204030b06100302120702070906050901030f14010209060a03090506060d030f0f051c0e10020f07060f1b0815010903080409020a0c0606080106030c0f0e06060703110a0308040203 84
    0x4652100386008135003c2da503012845885540322042030262034000802d4036410706400307100c0466046a024446481105140c3c0102240d9250059800071150640c02080c020f803c0d2200500119903480081c0d01c1540d40070801c1c8140000071030f00640280a0022659841782c000103031000b0055050300b020403e60b01030030980e402c42d110f410030091040e07048440100418002d44900996034011584c2d000011140e0918515200840900c049050902203038640320507a100d0850001c1c0c1c03c00c00c00c805140c800f90000310b00d081d450005031092405241707002002c0c280c41d030040080d021880c1d0842d6400b4004100c040503402007444c1c000d41503030340481e03d40d41c0c0c03030079a219003c0585d845012164212078012411903d03143c1040c00c2c00029504c040310040074411113540b80e2000906078400c4200078010300d00001000b83c00c42c503080c40e141c64250310014100342690400d20a020f0280e451036004007088032440e644030101c0c43c06650072080359443e00c0540c02054104400d054129100030301c203074070031000c1d2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 615527625 1250 615526375 615526393
    0x20f091005090a1802120f011d0d3204030b0403030b150918060d022e390b010f030209010603020a021e0f03030103081b0f10150506030403080702 64
    0x4030048408294011001110708051138000d81081d400d40800a64903030184c40c40f20f841c1c0c0d01034509442c04001038110401c11121607100c080418001001800d80074038100d5031503000440207402c0c11480e20303056117004011400384114100303050212401943c1c0b04400e40d08a15060070090018188030344880e00031001d1503200780302c01880c4822a0480e11005100ca1080c0c07600c035005450300074000b08803075008a0702d22403540150b85c89c031030300b0301c00c5050a0342082d207194004404140d51240c11080070090017103d64064a01c3d20300c6030f02100c07500b00d120164406007106100c2032445c06481d030001411035002000049110003020b0031444c1600d00941d00070740d05903030340c0c10214101d105103250440180c0200700510a007407080018120003c0c144021207000004014850341198000c0c4d2046644050015003103d001118100d03038900d6401c101c001c2c200c9103c5412065446001c1d107040b51009035a41c81c48801c81901c88003144024080103028145c507807400c0c0c503018081440c1030701c0000141c8504410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 615528875 1250 615527625 615527641
    0x60c090120031312050607050d0e030313150b09040b0c0f0a0509031902010e0d0302011b080906010e070801140a03061103091506030304050d060f230a0c1704020f09100509 75
    0x1504c0f1560000062020b0750302c144040b40c00340c000051004030307a07848150302643c04400300060b60141c41e0450f07820700140034624110010300304c21105601103c4c141102c09285546084201c0d0340103401000c81c51390703550380000e941e906201b815031800042d01c000c1101030f005d55025000e00950f0700d09a0442d0000120340c03045104c0d4141020740280041c4480b68803141c80c2c1481103c000e030f0103129000110701b003030b40303099000c1101c0080c3c4c904c0c2000403180010450304500030041d050040000111410003824004801404030105000340a40c00440001c50152501c46800e01002181c000f881004125195100b50784d0b242d2054910003c140301e000040c4c00d2521800008500944000b00254640b924240901a0640b041c10040c0c6a0a5540081d0ba0313111200c1d000340b10b00010300080c0300300c00d00880240e1040c4020040d15240c50f0710700d8252000b40c00794120006400701070b02e80c00c61004c15561413000a0364081d6400c04950000300b000f050000003010030200c1c4007954022a40e01100741d0b10304203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 615530125 1250 615528875 615528899
    0x513050f072105010b15120c04031a13020604030b090f01060b0a0e010306170d1106040f0b0c09100f0e1c0305030c0d020406020601060e040b03060c0901200313 70
    0x207000106040c851150101182240252104a115100101748140510005a0f0f10031007808150703e05440003a0409007900b0310224980e00003441019182810b045440b0060107040c0d040801c2d0784030fa103803008038000010701886089510b07402050581c0d901c0e120320306185003000940d0041441e100b00e080416086006006074001d030707400848082e0800203e48002c860441e8251555414166610750210710346541444101000c1c440c9801040307030b0441100f0090040001000c8481181c01a600b840002040f1300c1c0b10800d6640c00959450b815180c00d0200f07210761150220075503205207601d108242072074010142881d0402551285800e02054005001c43d628019000d1031800d0001c2080f030000a00a03000741d5001110241410b08049180c04001c080760311540012015038000b02c0108540d6a000c0c601d000c50400a031014459800454042a82c500c0050b054541321400450b408415034414400c1240d40500401d0340c0030500300c0b240c0019200d600106082e00310040100020403615000b41d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 615531375 1250 615530125 615530129
    0x5070e0102060a05271b060a0804080d021b0a03201f18050106084c062304050702030a0f051c051503010510060e030c040513050f07 58
    0x1e0090100c6a840000007001004010004107502d9030698a240b280e0048601040309010320300d005220b2250110203980c01c00d84043c240504c20402040880c5078554408850b541056020054030b46841042c42d803440a8050b81051485507040c20f40d1040c50003c000075403c60080c0a0f84031603562160140b98442d560b02c0c0c0310b4045006900c8807044282c00402003240350025800c50b0000210568002502003c1c81000641919243c0d165842840110414040c0000604a00403045aa0703080c000440c08000600b0505508451000c0220001e010b1404641150408800001c02c800c50321031001c900982558840003003501074007002d540080c1003922580d402102c0e190015424215900f10480342e0021003a400c2d0108081800b514201d419582c004d00081202d503203000c1114a0f1510140d812001c28940740c038420381c1060180140420800904400d455071440c0080d4503842100210f403400c1d1900f510700390018904000c000b4080d440101d1412030a11403426140c090600702c0721117940b0000c40c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 615532625 1250 615531375 615531377
    0x905150a060306120b060d0f08031f12031101090204151815171002070b0a0f09020f060711030706020a02100f08161e0801290d091401020304051005070e01 68
    0x48181100859200e0311780940c030810040801161241e01c0d914070310b190f020a5001c4130b00703500c080284000d07580c040e006044c06103010911215100d1900b85502030212031914082d00348a0151310700100c150080d0810149243c02500c20b02106400381d50b44081c2c480980b068510070005c080c1e6604e40d07120700c0c0c010072450980c0c9500c0d2100440c100403880001c1200c1e0110031410b441166100c40305c8103418009052858042ea000c2840c602e04100c3da00c0c00d0300e1192402c829114035044062005a840c40c1b40c400802a003541c0300794441c42030b0302e040540e6103903100c5403a60500c90250000b60b50b560008940281c61310a8410348241c02d010700085e07501c000a1690303030340800c448900207007101c0d00d6095014900c19884c5014221800742009628001c883c600d184000140c0e480018802420390318840c500c5220b118402428103a40c0310f035810380e28090f18a403450000c1d103410444080c06034000e2003d603001c424400856030b03400c0070305e4900d580d041041d03100210755081c5000139078910701455158080d4601 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 615533875 1250 615532625 615532649
    0x1510030216080a1b0602190f020a0803060105040b0c0c012d0302031312030c180308030a0f1509050109062418090e06060405160507030c05070905150a060306 69
    0x20b99264505904800354100810001c105550302007141c0c24501c4404d24007070751005903994110284000c04c04074000500e41480300da89204401d0560000350b02c1801a000580035489480e20b0004807014072544d4880084110042071148a034080070070504640e0000340c0341c1e01c06d282c0038484c0344c21240750024002c0030504014071024254034020b8008551041d10300014180d034003129035640c80303c0e007050042000001d540c0c0b54400700032030b00030794400c070141c24101800803088e1a564403003800d484000c048074003141d2034112a056a0700107812000f0105160000d0104841c0c0325518240181424403403110103500b018000108200343e41c0c0b0b00760505c400840c400050b07044a050695400700c0c610406003090501f564000b030384840b10303c10030401288cc18040e10540c04c0640400c0260390020f0003000911040c8600b001c0c10b15000b104941c412540743c1020040302501c7e040150400200e5403000d60114203103410080d41c242078540081a1000494031000c1064032011f0440c101c95407070098201e0782c01c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 615535125 1250 615533875 615533917
    0xa063201020c150313060603050a1a060f010c0f0f051f27020f040632030d0c0501091203060611010905060606090a05040219110120030c1215100302 65
    0x300800950340711001c00343d180070780401d56546c0811141d0942c0705a6a0760410308030041007001c4600c0000e0310090000e210002030510100081801110341d000c9414004d1a0106a08100d00030225551030782d0480940c0c0d180c1003481c02e02c1606d0704407000c2e01c1035030070701c1c414000300220040f40b0035040b00103110420745487c00141d014003a188000e003003050340d005010301d2038400f0643e40c900809010341a040c000c0400f41ea1103c015501d9802440c10441c241140c1c42c0c14404562000610140240110b00d0070b440c1c4155241841e81c0101030062005c1e00200142d6908a001609078000c003003261540e80d00c44541c151801901800c8419401c0001d2041c0c201c3c5000c0f440c41d1500301c010303100c3e00301e0060041013110f94810001d03049900c00d60442040c66501650b2001c01ca030020300301d55402c26803c0c000d21100e2400340c8814000801c05020540d41080031001c242c0d112102d0042c1ca20f80c9111490556050420300482c0b805202d02a4020748140b00d2207403d165010303c28004e441603107500c9480000144 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 615536375 1250 615535125 615535159
    0xf0114090d0c0c180207120e01020d03020708030a0203180d0e0901121709010e0d050123040b1617100e09010c020601051c05102c060604050a063201020c 67
    0x4601c400513219010307001d12620000c01d10010340d0080c040000c0d12010071000100d00060700303040701030503104d09241c0705000b280080b44000045035841000e4140040e503d0741e607990482c2c003a4040402c00c0e49688540f07a502c2d1011500b04900c940001000c070b800580903030342c0e21a100200501900001d140120701030b1952041c0080c0805415508414100200381101c00e0300032800c22031036001d05030f80700d81d19512400c104507030036444003107860600c54100c04285070030303103131100829405010000601d00c240d454091242c803600500d01c2c100070008940c50075060050100340100100d01811800d1080b01e0b000c16030005052207210360b14103983c1c0180145078600001c006c054012440ea60910170040032406000913000e01c14545000712400d000160b409650150310b6454903400107424a560342f600b9590603400c40051600c3e403010b002c58003c11280d40d001ca0040c040e00d686d5200c04800311078a407002c51403030740c55114403112581014040031602d4540004a9680381100c011540214440320940740b52 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 615537625 1250 615536375 615536399
    0x90b0a09020a200f15061c12082203030504051b010f080901020c030a0c1202031c09060f0e030c012316030204080d0e040506090411040e0f0114090d0c0c 67
    0x1c02c3c40659002c03030415100c0506005941c80c1a01290a001041100d036240c01145102d13120342111900200d94145d5031801030350100395440c8000d1100700340024120302105a0840004030358619207031041241850094040c0c5801c5c0d50403101400f070b41d40c802c1030400368085841da12985c16540c001e0f002640400076181100083c0841c01595003c00510040d09030800080c003441d651a615040c2114050520000300c80c1030715294000c40d0001c10148890000f41100d00c034580c4504003000070064101d1070030400510800d800c25011b40e04200b20a01c1001300030000d000000c40510007449818001350f0741d04c1d2100201c0c0785100e810240940030410a0a0941060f9016091420300600d855100d020140c5494030600c0300000040c0d09212600c81e500b818092103400250a4608080f9810642d8460803403409405c9800d000d0303542c0d10303d0010700c0d4004000c0b8143c8030040340c00030041c0c200c01c10240d440c1c0c10411a403064082c401d20a0303008055100c0c1e80c0b14200c0e0b9802900e9203101a040000845507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 615538875 1250 615537625 615537677
    0x71101171506160606080f12030405060115020f010509070f0b041203031d160f0608150112060f0b1917041101090b190f020304031a0403030213090b0a09020a 69
    0x2204050003d1140003036503038841d0b00041c118000003005521541c0803030a2034880f0700030140354158014000d00000500000c3c4a6066a00310036800c81e62840e048000c81ca0109508440c91080d03091a0500484600100d801d80c203032440000e009a1a03606c0c0c1855450300d2003907200d003202c104903090b82080440e00c00c2d03001d18510f10248000d46101e254107210107281c21001240c00c2000100d880c010403114a403008040001c0203075042641c180d141100400441007040400c050510840e00c40069000325664011809081d4124183e0000750329004424016006007140481c40100100d44000090280042d90f05004040542c0c005680e40e903a10402e0141e0860907503810b1046200c03000c01c1b1134040f10058031a141e41c42130381c5180e00b85e00f002c006099009442000c01590420081400810a0810140c003010001c2805103115206c03031038120b009118400510b00200760310752010588030790780d40060301c0c110001c840965002e44c9170600c2c01d04a128130611900400c5940a118126101f4080c1150b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 615540125 1250 615538875 615538897
    0xa0e010e070917030a0e090906071110060b030103060b040b10050906070c1403060a060605040b0f040819120e06030a09060615030b03011505210a020402071101171506 73
    0x10410795259043d0103034020111040a46030000b04001c00400e0b8014580102c0340f07401c5500070b055003481020726403a40380181c00042048880284612003c4003044410f44102c403007002080001e980f2501000903400030301040b40c02600308905003100340f41a0007905007a2000515040402070055416500d0790b0012205940003042400001c011401c10115000188024007143c2004541c4104050030300100400309000c076440c04000f80246544007090f2070994110500c0c556a8000c051000f4030140141e5000c00e07d1803003400305443c0841c80c00070604021610500d1020300400601600707440501050b0001c03600818240006540b00b40300307402130640140100ca00041854940104482c0c0309000301c903240100352121004080b6003401d00c2a02c45c0302106821144501e401d005c00a03010100c94164510078a1070640c021807180e8060044c0240f16038010001c40d43c070002403400001c012461082513003c58403e103000c16940401400c0580b0460244111000c00b602c01420007120350001d1481b43c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 615541375 1250 615540125 615540137
    0xf2808030a0903081608070c0c030b0916080609030306060a031e0b0a170d051b06040312050115020a150f0f050a0b0d030e0f06161407050a0e010e07 65
    0x4011495400040d0700034000100301140140c001d06003e401e07090068210501c800d1100c46503061194000f10854002e00286440c03080d100745d0b410180790b0303070109810107094840380c40c0903c5000b450008035800c00c030a004034148403da80c0e4001241d00e61104413020b640035001000004d4107444c2a40c01007980700202d042c000340e0034540103500318040018201e000e40c403964400203000a40b070b04518500040072110211800d44c984458100c3c0c035072000e500c0d101d00b4014040790f4505680210260060040341090480d01645072034100100a64590103490480c54601360002c0f0300703424035184180305940560003d04640740f60383c0c1c400d001c0512800503000e01555410032400e13280c0c0c050040f04405040c1041c042843c0c2042c1038806d0845100c0440c1c1d81c030840304c80300d540300065004100740040c00000c64082000f0b1100c2000b04e08184603c0c09031044130040c6003512000c2016a11001042102c400304445035a51202c05110121105006000d10009a840108020024400740f15071008142c6020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 615542625 1250 615541375 615541453
    0x12130c15111b0f0d0c1206021207020a121706090c2710020703170f0904110a0908060702210d020a0207090f18150e06090c120f 56
    0x106052084182d04003036215807420951a90b071411a2100e11188801c403100e00e0302101607652890020380b948a40b100002c000e0702c004083c81419815610300340140d0104507018903103440300070740761416008112a855559038040c00340911405560306250356544001c261a00c03860104240500018840154010200180d281104e41d844082c5c3c40d070340b04110307843c2400400f00200106640421803610455000c00b1040010a00e05504107809645030030400e60b88804881500c0214032494410341d412500b04080514a2040350004144515a0350754030594952660161502c4441c1590480b00580c030640000b10b16001c04c0200b01d03441070788a66072a1600703480d0041e98013642c024840c00d01c05608406000c00103818240218039452928081c00c000009005140c21404007c11102802c8144c0342d1103d034a1103125648811036200c10401214014034044041e1956a16048100c0f4001c041310054941510400142e07803000b98078010181080e2074003820100c00340000a08005401858000c0f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 615543875 1250 615542625 615542657
    0xf0406090c0e130c0503061504030b1815060918070509010f0819050d0819113001060c0c03060c03060e13030207180603061112130c15 59
    0xe50780562819445503101440241c04104a604a80102c1240303035041c6998080b0080d40002246d5202e40b003242e004024101814605126003d5500000c1446100c2c0d0113000e841d600c0c0e00c1c40c01e6206410b0740210ba0f13030540c0740d0110032040c8009464a641001e02000480c24800030f01c8041d840d080c01c000201c41591340d844e000651105001e0b405146c03441c070180030a12403032800307020005406035500118200c42203aa07403059503800103181ca83c81004084004654480084403c102d01e110701e85206100d0050341090400d140c0d8441e55000c1c0d04c0c44440e42c8206038104442c00300941e00c0c0e030040d51115940e0f00e0074805440c5880b81d130004850f650501000440080d2140c41a0001c88030300740d8000446905101c02804000009000703d0074402410354138000080d070000b100c2c41605e240b581e49000b14562441c110b4007074561500000c2c4200e060440b1007851240708006800c001c0402c015984242c0c50700071f051a0f0781300d0040800380010b590100300b0300c801e03070303110b51043c0b0114458642950030001600e8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 615545125 1250 615543875 615543881
    0x62c13170307030c14071b0e1f0609051309050f0d02070501080c03061e010e21010b04050112030f02190f120801150e1203040b03040605090d0903020f040609 69
    0x381510809408001d02c0002c0d40e0502c1402e2942080341003401c2c130b02c2200c1d101d03614a80100b81004011031303c06441c164401014070444002004006030044150405132681c0b03115491244010070528203100c1c00050b5a4410110303041221000b6001001003d030000b950f80260000810680b050700c18000c0380350545804100b18001003869034058506141010700040803080302138002103281c0b20900a110035640c1e002d90340e00c4141044022031a03103501020060700c2034400400d140750b2110b00f0400740d0320344502c00c11000741d643c2040e50003000b400c0301000c1007104840d800c2c0501d1510100400310880060f000d60300d100b256842c01e00403942c2c0021074864089946007140005c403003041c0c1401e1010100000b01e02c10003480d05240c107003040d0325030422000628070781803000d10204000795401d1200b40c58640307031942c8042c10480c0702580d980f02d448403802c0c2c000d503005440840d043da02c0c140004819600c003095234114200d45503228107078035103190204000f100c04201204e510943e41c110000b10200944 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 615546375 1250 615545125 615545153
    0x181b0f0903070b1201060206010b09092502100b0901060e09130b04080403020102010b03010507020c010f050702032e090f0204020901200705040b0d0507170304090f0f062c13 76
    0x1d10701695800c156280c0303164004d01a8440c0081d54890401406428104016103090b00d0050312861103940e141c0c8905005d1403094090b40a012800641e0411900c0e80030078024104000d103001485450610414040c0c041000d1042100060001d421507501303181c04001c01b074000300c51040038488d00c4802c0e02c8114082105880484000c08006002c204558080c0140c02d046013084000308118030b89090082e480300e01c2c80940c581006114000d41e0902e43c00740f42a5204250054100c4120004200c68046520750304040c0c4035955540c54000420040d0702c2c082c0d800c12075440780100300f0b5400103a0902c0043c1d0002107a1a041c0081d41405944030840c20040860605c007540090004519100500048900d10800c0c54014405a22010003086001a18404a81244c6100d0364044170060016085004503084001d00c0e40c1000c032001d1004509801c450001515004200f0810380e4442c20301d5445c244239440140b0200405e03151400c012449102107500c071340c10305200505884c0550701c006141d0018 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 615547625 1250 615546375 615546389
    0xb010e031c05031801151d04020f040c21090507050307030c150509040c031e0212040f170408060105010905010527190605071b0501050304060506062502181b0f090307 73
    0x1184c410400da210f540001200c2140c90014401c7c2c0e401c154000c0b5400120444105002c0e503120912051032900ca0220302951040305a42c485070100c40c21941005000004000e071100d1050010220b005e14003c0b480c281181d40c0100d0001502d450a814100e1000064961b54240202401303a5225901c030307070080f80404411a0340c00201361406108240b2514140d0380e501003458414001c00d4000c000d4409401c1c2c1164228400880e010410b15013a560b80028141400d5140d001060001f00e5002c00110141030b00c40907250b4502c03958880004444500078a2811603040000510549449030810300c42c00b26980080c14407040030856000d80a40149580d1125000520008020b801c0c40700c104c40303e51110592468120901346407600080003400040c201030043c0780c1d03500106031940e8581d4101d0ba040d03200208003902412001e200644029204001640a07044001210411145118019229a8182e03101c0e0144440005e08504141c0107600001a038036000c12420007207540c1040860010801 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 615548875 1250 615547625 615547661
    0x36090906040614010f03170717030412020606090a05070c0512090102100b01080c0307090e0103150c17010b0a0c05030318210403060207150c030b010e031c05031801 72
    0x12500c0c00004860003c1c048400307500c40c20005000d20121001e01008983d000b10151400d006d00d1343e085c1149101c1d6400040c4440c10803602e980d500c9440d60051403003503020300c60003090841918426a16003108490700d070b52214404000414258603a0701164010125280c044a83e03801561514504034501019640c0d0240204030071000e507a04118140c0b00c03101710300b03080c000440c440c0c00180071700e24090914013500002100080c91140304821000061035842100001c559485c1000d000c10010404540c42c030b5820040301081d418041c400c0050408000560300d83c00307a1170001c0c5d0034a40d4000300800810030420103c0c0c4030120708100043c40c052001400070348900e1351145050347c50040c5902b4054100140f18840715a0301c5220402d950407243c01040c05030740c41405251480034510854000d507801d525088039049100d0b031544c8410b02040080e00c07041c4515904508040da44e40022405140c01d0000b001c060543c14451009580c00c020b07240748500c107a001e007680ac1401c3d6411003004110582d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 615550125 1250 615548875 615548881
    0x101b08280e1908060f07180306050712090f03050c0f030426061504020904020904051018020711100219050f0114010602100902030705060f0301050a06020336090906 72
    0x34004800c25510110b42d0103500d5a0703440c0464468485000030000c201c44210702e07000441c128001c03031244850841c03402e02c0120b4543c592130001d004003400e0b22010700162188a49070451040e174441c50b0070b0140c01c905084229152a036013100c15501400e02c0041e00c0c000e5a1851002207010000341005e098071400c82c0c0b050744500a1400c2100b4904110b1034200c1e0b01400a02c101d190b04001000032541341a1001b590b24041321021601a1041c03410560f0403901d4030007000411070700081d041081d100e20f504161021220f007603080e82a405100701c040c200b6640d552030b0354111b20340440c200504078010f005450194200400006022046d070006903803c0d00b150041c05140c0c042032041c500d80400408822500354100b64000755200c030708603005c40f440356641d0881000d55404111500003000c000782020f82d184088202d610f003e030030a1082c0d60207100c0c07625004c14111700100646220524464031403802d002c55204880485162645a041481104510f1782c416155a040584038450f00300003418142 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 615551375 1250 615550125 615550129
    0x501030209070e1e1c03080f090c0a06050d0f06030302031905071a04050a050601080706030b0a062c060706022a070b13080d030b101b08280e 62
    0x480020003200401c84030551090399135807442003426280c4e19500f0007074207481004000c64695103042816650102881041d0301c20154400842c910034001c20420155640781e10756400e0340d4549800c00280e005000c3c040500002c0d1054001d0510300d80031003008181a60021010012169150170503401a040010821008525810111502c06192a00d1071400440b40c440e00c00401280d010603020102240c045000d0000170000604c01d66003003029078020b075a503040000d5841c076241c80303000e0119003440400049490a09400011110035460700080b02e240c0c00030a000e03c0c40d81540d007800340003011800c1d43c5c07070f500c8240280045a100301d000694540717000030005e00d0b2408246072040204a00c808050302c821011030058215081001aa40c81c0d69105c0ca03445c046001540104000d0320462141b594a20707450303003050a201000b61203030790f0401500402145e510000d9660300e004a0300d450244400504d00344001c11340180b03281075110038842034032080788926412070b40c600001071205108182078 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 615552625 1250 615551375 615551389
    0x60f0b031b030114040c0c050124061701050405040c03050604030810080c130c0c02040926030c0f0f1c0e010e190f021206010b040306050c2508040b0c0105010302 71
    0x50031204965500b10b42c50400b0414900c001c4000d6240107075281c41c507000c0c249014101c0941d0152303000009000000700c2c01420301000030b008803529440070415600140141c002c003d0f458909110070382003c85a07090034144009024041c00803507103411100c80000200ea401d10005004d50700c25030f9a6902410a908c0d01e4556402c5900b145955801c01310000070349507595007000d45041e03464403000c1050007200700203a85941c0b0007600650014181040c1a08212552071444084094440c2d54100454036110303000300d0380011200c00e005194100030050b41408804054003110059070710881c40d000760031103ca40c486d240d0f00814600582c854108450404080c0034481d40060540b0040c400329400c9801500c0e580301210703000d0b150f1140c0082480a40d105e2940c40c0010324150320450b01c665030b44000c040290746c014881a81d0075803408000c10710102806044480321042003106418003103100a04001c00308900c102150066420400047c00030903c6000d40303500c1d5201c0c00001850361441c0103204030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 615553875 1250 615552625 615552661
    0x50a05040e0303150f0d06060503151b160c06020d120c0e010806040b150d0b09040c0e0a06080706020a05010b0303130e07090806042a0503060a0c03060f0b03 69
    0x1046003032031004010a01d000050f25404242040d400140e6080b40e00450206480040c80681160701c81200106000c0b894200d030040710419011641c82148486860940341010755810084171905050b025469034282e0103000208440310f1511107101c0c00e9915180a03802586c44031001d40c110301650000140c00c542c803001d03801c01201040c00516400f400003024882c020090701c0c1409180c101154552721180d000c212000006000c5915840501812010581190034008002c0e03061505031026428946c041600845c0d004180c404101d090030010080d480700108030008103503603900e0000307440c501045640014581500586503100113800c0c190b0035174450081c0180641d00400c0b881d0302c40180080c506080b00d410141d602030544402c0000c481400300340e40101c410b403141600788030500c1000c5881d08111b5038400c401e8131864100c0440e20310380c4000d51203070b10341c15044207000618024042d04040e030040035903e00000da0341c0d10b580c88031103910001d42108030300a00100810428450b503841c641c42c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 615555125 1250 615553875 615553879
    0x20c041802030d090b0901110102040b0a181706040326010f08100204150309030c0f031713050c060c1e01061a07050c0d0c05090f0919080315010c1203020301050a05 72
    0x203200f0704003a05c0c501ca611503030302814104401c4281c0380741014021b505481c0507100078117009541d00307031500c0010900d4251000c20b1005c6510780000107101c1d08990f641000d5842040003500241c2e031036880580d405a410154404001000901010080b901d8858280a032201a0521080c9818007034400d207030800d00c50003404e18603c104014044140154a101105403084c0340110f03a1041c0b502d0222803589009000a02a108000051081540042d00c144c40041c1d2090201b25070b0344c1c0c0010781522410481c8028290350400b5101c4501d80c1080070040421801a10880d40609511a4001001c800b410205c58840e5941c6900740402d4580d20752809100301d043e06a42e0a00ba82078560540b184054507051f4401c400030800f80040105803e1208000c00c00244840c0b00c900e05250111341407101120103020a028444130b00769500405034501d4202071300911003508603542c041c8c8100c10b244421a64505015168a404e0f00003807a8581075180c0030155a00562654585000d0064001d46508094 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 615556375 1250 615555125 615555137
    0x1b0f0f0a020d1b03050304090203070e09010b0d0902030c0a0e1f0302010f0f020717160602160e040204140c070b07020303060105030f062803020114070b010510020c041802030d 77
    0x2405a902d150b0900352064100546000f03070300b00d441c0e401d420303540c040d80300401d540008100000c48003034a0f40550712407120303034444c0d00348000d0500401155100034080c106d0481e40c203020451251075164000c80003144003900312081c02d011000050711803030b0940d020300030401c10b040c00c1065100f0611490350003101c0c0c81291002e418215400640341e100dd2011172030400149400f07044015108000b20802056000121103020360103203861601c800e880e40110a01e1611100700240c5240f0000c0c6007030078241010315110216040420482504402030400d81e4000e0300d84203045050316a8201050141c03080c071103074581c1d900103850603500c42e240007480a800d5400500c2000380366608041241c1e80b05414500520481d554100080e0448080b944803483d02c80c0790100010b1400704140d41c000a4038000d0701c0700903141c524907002e0314451041400081c50b01105d800104114200100079400780c0007a80180c0d070003044418081011684601002007a01e4079030004241981002c1c01880d6600da4149040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 615557625 1250 615556375 615556393
    0x30406050a050325110d11030f0705070504060e0f01060503060f040903031503060606140c0a080c120705030a08010506090306040b07112a0607050c1003021b0f0f 71
    0xd040c600450504034148400040081c02101419090500716090036000d600815143d0130020310f0680c4051441d1680d1069001c0249800d010b69105511500280011031030180c440d12002c2a45e04480000c443c075118412000c00c46541e03500550002d8040200b40c907030304d0324040b50721600460040e4071500a0010070014000c464480711010a40703ea01500c020821a599150480044c1507080126600c2440c4c1440401040b0594020500300c640c0d5a84e00e03044540810340e21643d901c6000340301b5205600048000d4002492003020300120200e1100361011207265030141c240c5984048000c4a850300005920400503422840050160600782e8055044c40c00ca50082036075610040c0015020f1340a44000903d9944201409a9805111002d903035026005910203003c0000300d10403010032080d11825148107061840a882d0840d401100170074580d1000b02c03e10010f802864404800c26808001c1202c84540c00d1100e0a0300321490b000901c00300303803515241800d140744d42e8203501003a0040540c2c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 615558875 1250 615557625 615557627
    0x1b0904152315070b04080409020304150b041a10051c090b010b040303120e01110d05010306051e0115020115180507110c01140909010806040b060a0e130c0506040803071103030406 78
    0x350f0703085a81c000030110a540ba907040c00c0f0f005002d16403010305058000010801040302500361642c0c0d144400109102d480749601c200f006030b5001d028090440020b490010307001b480c00407426000c4000070b080840ca41620782d0050f042882c03058444540d002e80300d0818104100c0040c0a650051400182d45030500b07013107a50007001c1c1c1443c0c006846600d80c4844594402070f2003980804c80160303451642c9540c030b000c1400560080c1000340705c00d403100c9140900250384805010844010300e203c00080d170070140e08080c4559001c08280080004540d603d441004c24184400e4030078010300904103120045c2c1100901550580d035009180004120b40d40c210450700070400038240100c2142400c1452542098a110211038010007141c560b00007900c40c00080d1307003c0b0114201d4001e034042c0203500003036603a04080c0111482148a2203945010800028103907141c14080315414078410b900342c09005940701c00142950700b06030418806a00001441030801c030640c02000e5aa81058003d10305251030070074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 615560125 1250 615558875 615558877
    0xa090807150315080303150306100302031c020708030d1b0f14070201121d0709050402030307030c02030c130209210d03050c0403061e0b091b0904152315 67
    0x8584141601c03803800500c1c03060032010070400b4002d04c01c12652a850540c80184424500000143c028020b86000ca00d03541002c0d02c0403000d882c0c020b0001d040c41129200f451581d84c0f45151840214003a80001003210f42c4184010140c049280720089081c0094a6040310b0581c10404901c003800301d003034003400c503660708040064140707407602560b15161222400180da01103443d114564500b45040111040c02d112010540404000c070800c54085c2c2d5103d01c40c0c074049407401e941c0030354558001d004090000b88142d408029aa1015003650101510200840e078106403c03450410f0304ea0300803e12101505282028106206001c4411224440782c110610b444180c808494070801da2280001144481d500741150015a4440000c01c40d002a0082c1a980781c04010940d0f040702e4100345d240305140c070700400702500501800d04c041d0480c14020710740021980c045000c0300c0c1c1042d25410315020403e9480b544a000f80010701920409039100001076030f48142d410303442171180b03000c5c881c10b03580307411800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 615561375 1250 615560125 615560159
    0x20d020d030e070e0412030e030a09030206031b0a02012a200c120a1502090612040213061706070c0c14010c02040c02010f0b060c100b0a12080a090807 66
    0x3040019200201e400c2d003030b081144a40000307405550078000d00c401c1020001149180701c00d59501000720031900f50307220351244a05480000040c000600a1002d407034000015500301441d0341580c1117008191f0481122600008101c40150f55100718150a404015600c0c8a1948035104884000740b04030300f003d01310304241036130003a988a041d030705600030b005c1c10415504030300401407150350b04494a07050a644d560441008440361080038404602c4d080301c60007624a0700c138004012a04040c6421a01400c50400030310580e80081d401c80f44440c42e21a42c41400040d1051002c0f15491818100b01c6615181c00503000704204008280041d020550202075401039490065401d03c0c00c003100001220310f2480303030320003030340c454500b010411a607501540160080b044070b000600030700c000da40c00c0021500550381c1520391a00031181c0041d084009038080c02c03c501e4020003072071100340c4400340c2e1a9113412b025400c0700d0240001030b07514440d5400c034917000004c0c03000100410303100e410301501d4041c1030003075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 615562625 1250 615561375 615561377
    0x302091f05121e0109050f06190203040305090105031005091501090b0f090907020c0604090506100905011b06020706050103080903100c0c02060a110d030f140903070314040807081b01020d020d 84
    0x650640341c084030f020b402c80041c4941041c1204c0c14074980780b51450300c1e038000b030f10143c40d52000c1c0161996018180e00135607101c0ca8040d01c403142021501001590310760300080501a1082103c40046132555543c4420382c010007240d0040c60703802e8012030000d0042c150300e400003e007010f002d0050f00801c00403441102d010070010f80b0203010396112214181c1c904040910425800a000714021415240c0c55000c20300c940403c454040c5040003014050b50046000d0003901d000480c411481c0000702240c00300300000d1b910641005203403600640700e0a04841c42070f041121380500c0010303014003500c1d0030000c42210001c2620100f001e400c040201805064502400900075640440c6a45200c1c2c00713031013001031103c03440050710142e01013a00000c1c005c02ca40c1c190001e8035484d11095000b46d03000f610703003144240d0024004600d019805d80b41503032091255040681100000c2002260140c81802084001d00d400c0c0003c114011110540c103001c801816100c0e03045521034801810407950018040345400b0171 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 615563875 1250 615562625 615562663
    0x609140412140d1512020306010e180a08030601090f0e130206090405130b070309030206060d060603120c0b010905190903090510081b130303030b0301060302091f0512 73
    0x3094000d444200c0800085000c0326400700d0070010f4022990000443c801c004082c0800654641000e0004e152003000007a4150f80200014030112000c04610768200c00e14203c0811220300c1004414541003001c0400c480500740802030106950300407424102411a41c80103903102c81c24140301e0b84141400034542c0c0c074080d0400001000350f4a80608560300b84a01600502092402880c94049400000300c01c0b141d41c1110000102143c3c4a40704000742d15500d45d0180c070003500d501c3d0801404544030041a50300079500c0c00c0020000ea401c47d41c02014400a03140c020502117181001c2095540503802801c101c1e00b41001c010101d4181c0b90030f40a2021350307800008400707002c1d013411101d246558201380c1d00040180b400c03e0b111504200314034411070b110003c4000400e4501818112406820540d40c0746498403401407000074025044040c9914026000180e0180c0c2c076000100700c0d400980e1078110307214a040352410141d00d00394668001d400141c80c0600400d01e885080390b40d4034050000c403600445 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 615565125 1250 615563875 615563903
    0x6140d0812041e060b01020c0402160b100509040b07030f020a080a0203070c08030106091707061b171c0b01030506030c1504030c031a0f2203021509010b010306091404 73
    0x403610741c0300200f030454096450000c0c405841c00d0340050035035040c424054400e00c406d41c019850503008941000341c0d4441c0c061840001070b600d441c3c1e800c60181c02c485071070481c0700012800307884660415200398050345406000e401d1605d8042e01311020b00f144080c070540100001c0c0c6440385c1000c101900100c114a0060303880c0d64200b0121034644042000411212000cc000680c0340c0d402401d11083e1003040c509140001049500356554004520504c400301d0701c0403880300c4841c0049030a103044240070304681c3c980d0854400c560001c55205080442c0040e101481c00584948244105042d200003801d0411142c188031000950300c451521881d4820000b00d2140381c001c1c0711a0060702c004580c00075040391240e40720b1921a040400b50074041c41000f44107000904501040c0030764a00031003503a0301d00d1846110200d00d02690030240302c4241c00b51b1103155840d00141010344005841240d22000000342c0e02d248100040590301c40e80c6c880b03441c0504142c581c1d10200070300341d40c180d0071a0784080b912085403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 615566375 1250 615565125 615565133
    0x1412040b0c0c0f01020d0605041e02090312042c0405060a0507030204030b0408030402180c07030c140f060108062a28080a11071101120e070906140d081204 68
    0x44116000300b1a030740030b0404080b41464054001c1e2211903a42c120034403100791140c0c113000494510b4001d00c040c1c0d5030122900540e1440b942e0060005031005010703200200900d1451f032660b940103500ca03c102143c210f1181c2642d6a04400040c12031203007081c031843c1402c1c0b03178540e155211000303813844002c143d44d48003003083e00f07001c1d604442c01141d0200c0ba00c0114a01030502d041d20ba0000c40b0142c0c0142400c549070780e85010344400b55807065900e03544150a00c00341d918122800080311a08a0b1803207150300b44a52030440402401c40407000060003455550304046c0e001d410804050f112070b000484580d0341c0ca2104c8240598a5132881c4108001904c4107201c004159543c040a007581c050801501102e2006c20303440980a4443d40b1a44001d001041c0b00311064034551107089800b502e03c0700c603170344034581961045c41c424440b40118100840c20354050280300b8103090481d03002c6000c6030307a03a00041000a181c24400740740a101107880c00c048140d9a00c0c0c0c03211a1046403580107411aa0708c001600300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 615567625 1250 615566375 615566377
    0x160e010e041409010501080d090e07210903110727090b090604050c010f05180d0503030a090c0e09211309020d0b032a030a0501050702030403031412040b0c 68
    0x209001003003808146403080c40c6010b98602510a02c074554200390001c280c0420008101c01e0140c255a40c41c40500e141511020b41110060000300401010000e00305202c0e480c0003041c0000c100b08640001c82012031310b07000d04600c20b032480155117500401001c002c40c0c5a0300d42e00e04501a600e001d9031040c041c000c5040b000414034008000c00b0b8501503420f1041c410340004107280705501c65800c60742203000c284015a035608a080711900001c400b04111583d80500020306400c2000c00340c48510012115030340d4601f580c000b1950001c0281da90380740442404483c10b20b050041408200c2c05c1203d0a00d000030b141c03240d941e101620700fa90400b120106481001104a6040f11588005000040d0b158080e03800607601c05000c400b582810140716140900d00032a0100a100a6030740c0714103c480c0301d12000d041c0111601005905020b1000c40f0700202d00203000b142d1080b541540515a01c600317501c0c005d0001615802e03045a501c1082c040300030b400b801c8112036a00182c20010310019503450080741c482c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 615568875 1250 615567625 615567647
    0x6050703020c0d050d0801060309120e1201140a1103060d0f05070915050103110a0e0f010c150209030d02070303050708070c03020607052d1009020411180405070305160e01 75
    0x4030a210f50209101021900d802d05005950306c00107980da99900c12000d541201d400a0840c20210804103021400b4095028800c10017070880c64a8940401d40c0500310388201c41c1c0f91980c05802c07010840e01d00d4a034429807851184044c0881d095040040110340382c5004280000c043c0001d913010441440f50400103040285504441402501c400781c4010319082c8a9105440c0407a05001103a142c06400e10155a21407440b41e40e09800810310f1010461034651485444d070510081080407004908464000700100000c20009661400500c00f03151400303025410800071034024035814400680e00000321071045400c40103ca40325005407d0030b400048269000030751006001074a503041060200b01386c00c881c15841111400b801001420320403480c10254600d4058000c12041020307040b160740000812400a00001880b07000031101d040680d0041e00004440150000c00300711906e0107010f5241c0c40300484c41d050180d0b081c5649601c1c0e10603030203440301c01071018080f220203040c0d01c501742140c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 615570125 1250 615568875 615568879
    0x1050702010b120a112e0e0a0e040f03091e1a0a0503011e0b0c100c0e0303090103020309030f0307110f1f0209030c150c011103060a03080c2103060301141006050703020c 74
    0x140146c06003001041c041401400c003040c040604c0600a142801d40c080881c1ea460303c00058582d01c0341e8440303011100c20030b8114184214918089495491a40f00d0030758252801001c0802c6410400210080c02d0148820300c04514100801010140d020707050724115110700780c0f10005009598107251007822141c100341c00529002c5900c034014100000c141441b8115490304101c01303214148105d80044141c4c0115406500c200b04c0d088055101342d00441c0d005200c0c1055908049030201410440e038800d48141d0000b0300c01b06424030743c460b820300031009003901100c002d01024a000d886245540c0008405041c100d034089008000c1d13031000d00800c0507404008108000300164030409020580250080414940c6002d100101151070740c1304076401004010b001401d118030316941c604445e4006281620140a50300f071880c1240c070500e1038040e49000904015440349003081c241800c480030603d0404c0d816000300c0078801007a40204000f815104d43d4a840da0b690a0241410ba00c4e00ca6600012a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 615571375 1250 615570125 615570169
    0x108180102030c09011d1c0302010f060e07080c1c020f07060603061d0606030309060318070b0a080c03061806061b011d060c09040c09030203060901050702010b120a11 73
    0x401050f2192000702000d11090321070505c82940308074010000091074a4840c0c00804001d104144070201d0792142031103034401d20020911801d90304010090341d00e2075005a0000c2071240c2403010981e0040131131a84407150480a90501200c040d80704a444401c200625580c2c0d40000c0e507010009200f002c4485403a00100280b202d1340c0d1700d00d0a44001c2c60b200c8807511000510340c548459245010a801d8060b401c010001c505140e00c0000700226540054070301101e28040217031a0183c14014401d18004090f20750101e926080c000c10003502c44000200841c80c80c41c410000c110a9a4502c0318042c034042c1407560410b000ea079400045030072480344181c2e404061132007000f03051b08a030054010002c188804856803810a848101c0c0980d10071040d00d00340c11645e0180300720000341c20540e00c480000d100c0f626000031820b5807030700800c1c00d2820581c1c000f422a5118001c000b031a903024054048054002c0d110603820310000d8000c00d8452104030001045019000d08a00c425a00d00b60007004c410300c054000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 615572625 1250 615571375 615571381
    0xa0b0402130509071a070206090402091c03020309011b050d03090305160c080f0307020105160c120f02010905031c120626071406070b1e010f08070909050c010818010203 74
    0x400c1c0da1340302a01c5548180116022a0181440c4210903a206103038003078032050415503114200006904a601019080081c2048541c0e048242000790200b65002e50060751ba02c02100c00010001d20107540b45d111500100103003500040c0300090791040d00262490001080c104604c4c1c00c0301c4900ca01200c140f0010260706c061000c0c020240c2c0c1c0f920803070302c43c00d044544a0300c002a5403626809003000c040c0c00b150040c4204c040d40e8589220500a40d4030404840b00c0f01e80d201d40605c000305134043c40c261000c0411981940841d40c10442d40c001806c03040340202410211948126081d401110081c0b080104440885143d600207030083c0e00500350300c1c034108a01d02600c0000b81c684010740e0600ba4014401e00c0000035181d04800d001031415000940440e00e0074000703441d45040414050056007110540c40a0180009401c8002c940070b002c114610f80c06241c6042c1c3d54a2a007081a0060701c0c00b5840d24600d0000282c0005012440c42000c0c00c1403180b47c2e99050040e091b1413a450300d030b2034281d4000410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 615573875 1250 615572625 615572641
    0xc090911040b280e10060203091915030608100515064608010b04060f020c2107060203250203070801020a030c120e300c0c01030b0d03020a0b04021305 66
    0x25210940d102005444d00b595210f44a0011110f02031141da80582c104105a03011801e00f007100000c40c40040707401300c418075542d24854110030325000f07540d00000c1c3d03903030420b20181d0400d0001d074520804a940a002c41d041071100c1c060b101401c41c8110380314140019030031072035448440c001c0d44058000b40c01c1e2603c04184030008114801303903000d445100c10130038042c0113106c0d0082030214140ca00e1800094106802d0402c141e5024210350045c4007544120030845031030b60340e071082010b10300d40f041c0440554109201c1140b8070308140b9421050664006100d07078041c00744541c045055960f0030300301081c03904405002280c01c000d01900310303020035400050b00f005c1613901504030940ca0302c0d4682d180350110b40c1031045a0708540d0031004048154016840c03070741c1140c400e041c607030303681c080764081a01800c1b126051050144c3e000b01c0090320181c10001d26032041d90303010b11030000000000c1c0c070205400c1002da40d0007500e80d2442c600042a91224001040c10354a880380402c07002100501d0070426405c4c8000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 615575125 1250 615573875 615573949
    0x20615131806180c0308030406140a06081c0c1b0503030a020307050601050d0b0406050615040306050109060509040b0a180f031106060307150e040b1c0c090911040b 72
    0x40266800c0f81403980c85a034803014000c0b41001c01d81c004c11580c1c800e40c01c0d03658450143e807001e401950f071561541e5540b01d00503c04139216000b061509070014040740390100980c140100044000c503800030000315444881d4220398450281c0307600402c0a0038146110522080806543c0c0005d50075200200d10b10210a40000007807100038080c008488071681d0f16010404a0000c00301d00401c0c001a0700301040c005845a0012508628000c0c02c0b10456901c00e1504000c58100707501c2601c4c0d090722040104615a02d51003800003420040d11100c00529083e203030304652900c0545200c020b00d41d20390481046c3c050305141c002c0015440701064a2070561400c0c0140b640c020308048011314003030313100401c045150021b050000ca40d0710f0300a100560745424010b65852070340044583d00b15840b020798041c1d039641c81c0311072030008980891507501100c141c00d041c1040103440d04884140d07450201301d24041840034a801c40d10110454002ca113540109010070441904001c1d11840c3d095920880400380c2000d01e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 615576375 1250 615575125 615575171
    0x108190203071508310b040f0b070302040e010e060120030708040e0a0b04091121070b042606010905041a0a05071d0d020105130806010927020102061513 67
    0x201030009200000c5c880c08449070002d07110400103c41060441c0003400c1802c40b69030090050308000c001e8007080d107400e10341c07940481c0d44c02c0010340d0004060000500c83c107403e50242555644410301c80ca840d90000e8203105803a0343e1109003440c06400141c4a04080003200c40256204040541b03982d13852a0900c044081500d180d039150741040621a214189031098550725900071100c5d00c0d40f00c400c0000d00000e00c0e4101d0720300e08524000005c3c1402d540c01002594020040000794650b00c0c4d01d030000481440c03811143c10341901c440110348210900c80019841e0558242810006084d00d0b28540715610204021442d06299100010001002c4c0c1c0c5030302c41361140966450790344600141a411081e03c40b100c1e040780c4d40c8418400044d80c0954031603000350810111a02c00c0c441c0b8076440710901850048244e211181c001e80300c07850701b002c10507036510020740070b9008200f40d400100d160b80080e4031030400814172425200380d0600072145644010500d007420516807420803001580c0d07228045504518 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 615577625 1250 615576375 615576391
    0x11061c020c010f0c0827010207080c0a060507050a021b04020d14090105070e03061803090915010207050103020a02301201050a0e04150207020613060e15030108190203071508 76
    0x42d03000d0504c60254410307030320804070020100034004024102c1c00c01c3e20189510401c0a6500348000c6000588800c01418524907070740c001e00c00c000d02d51500b201a00c10051100c1d007000002d1040802e070640018482e20080d0124609691690901010500a000d5501e030300c0440c1d0b0500d4803540e1514503080b82c0d28001c241a04c000e100c5a5105002903c1c1d101d560704460360980d02800000790078850440074584c0b900a8681501c0c5006013001c0050103400c01500c030302410000032070300005590703010840100104800e003810340c00c0c11182d1001130b450303070a0140385140508010490000710044c6c5402003c0f1044181449601c81142810040e02d4400900485000d0012a81c0203d160640c0c000701920541d0b00403041c489218503d40c9000103500700104c101d03000401030240000192042950501512071541c4240800d50304000700070b000c8400a6010108003c10001801a40d8000c1500b074610b0340c0d000400341c543c80443c80445e140502c59804060001c106014030700000c1d607c025031500403061 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 615578875 1250 615577625 615577631
    0x5220b1c120e040c090512010f092415031214031006031107021f0306030c0603050f070e0a0b090d0506070201020301081b010e090c130e061c11061c020c010f 69
    0xe80b0910049412240800000c0f40c130030f004c10049494281041803290080d2000400c0c00340381e01c0718200650701c8a90044500700380d01500c104210802c40c41042400c01c1c80e007414801c2030f4040868201501041c080901405d0703501061000481c0200c0b1414450300000c0e81880ea03915000343c6140110196014041c0003c0c10103c507907040c0d600a0003501d05003500201140c101c41c0f030748032441d803450300a012080d060644814000010910121600c0c00400f03075a01d0226062801c1c0050284411b8000e1444003480b000b50700030003584d1100504082560a40480c0f036640e000f407000081c40c090b001e400b0003803040c071540c1300304100243e042d00654100c50b00b07081218150031a18030101c07101d400001c1001e0020310300101d504580d143c4002c0f219003158405d1a0301c0e10f444001c2e150100d01c03a0144d0009400c00310010207101e0b060070148145030b0340311000402010a80e04c2c5030340b008081e14943e0701c1c0364455417011a808104031010b4000c2203d02203036100841d614180340703241902034a080b81803100c0141c9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 615580125 1250 615578875 615578897
    0x18060c030e1c031d0a030201020307140c0d0e0f04060329070f08040c05030a052521030e09011712120a090804090c0e030705220b1c12 59
    0x300020707144901c007070001c030b400145050034002200180140b040344001200e0050340d0f4143c42030140f1040d151140a58005a03680c5090100030f008a50800400c2c201f100c1c0c1003140914601c004510700d44401b0706403401280d4401144005030000403841419940285009400000c02078044031040050103210040d4400e54140862488210011121070000c10000b1030b80320011881a0102503200b0700c50603144c043d09482d0300110785402d01c540c0c4100c030a42c0c460401400001110340382900341a41141101c400541801e0807030034084070340a500d0400b5801d6020703450070140a40621040007030060070a14040d0303980c401060a121850075a41c8003401003000e468031260b80b4908a881280d200306039200740342c0324241440c005256000d4207070b42d010b1040c4401310b240171a03405180b102600642d0b03504981d0038090201424200168880303031040e42c0a19108401200020942e503a044401d0790001e200324070103021543c050701610005d8440180504411b04210084003854109682c903900c030354a883c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 615581375 1250 615580125 615580151
    0xf060f0807031104050f0f0601051b060a051f06030f0f0e0a032c0111070902031501021501080606010804150203010303050a0e041419060f090608060c03100504020c0118060c03 77
    0x1842601d03411301e540460800a024045c0a031f030310780d811800600d0441d15011190011814540190214061a40080062250f8040b040c083c41da0480d541c43e902d9401d50203075080c031b000b00041381e218080c18035840340b601c00144001980800110300054005002400520801c20703210ba1480e05c1c00c0307000c5541e1444091040820b18010400c020500109842c9080d44000544050050311014501d9220f01000483d100c91640007950240600c06806c01c51031952600282c148180d00300c0d041010281540100040300c00062001d400c95028249441e035610703507041403007502c08800224020280004000420158008000d02c015005907555071000001182000207650200c124440e144240101042000c140181e0130111089c0f40c100010705039075541100161446160320503010950b513000200114107061004642c0124000f48175442c500c0c1c0300741c0b4510440b0050051500032940800d040003052002d600c01c4900c810860310500749a280d0703142a50160141281040020703080540b94102c2c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 615582625 1250 615581375 615581381
    0x18100c03060305120f0a11010e01060303081602160504050912031f0518010501050306010207080609030a080f1b1804050a09051002040303140a03060b030c0c010606050f0d0f060f0807031104 83
    0x30541c6005c28601811100304407020124840048425540d6082100c0d0426091141e840218880d8840c01500d180c441490040300c0000c16903041950000e9000140341c0409000540c20341c0e108540008013502c40400075032a00b5206100440c2d00b07800003040c0600e8000c907030176511248a1400c20400c41d284c0311402c3c05100180c400c28039044100240050100798014005147c1c85081807044a40199440c61020b181c4401a1004c4030036030400601c04207000d902211041c0c0c031070091440407690b410504030303164800121076090020814089601288242c03d8040c240c03031703e04020400c1c4100e04040030248000d20811004585074441d140745000380d0388090094900301e0f6055102d21044035401c089070200760340038040c1c00040607500d40d00860105100c001850203104484249074545403000d01c500c0c01c45503903411010a004c0d0a00c44c809140e20780d10101c0380242c0410102040c4104c0e1916010050129500030f0210580c1080d4080f8155000058290882c0c0c040c8441200c82142481031000f2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 615583875 1250 615582625 615582637
    0x30b0708010e0105150304030c02061c0218010516080717040605030a0e07050f041121093a09080d03020903060c070b010b070302030c011103060108060a0602030318100c0306030512 79
    0x4812000c6c000a40424003e420500c100c50000e0000c6261040c03686000080003400340d1250b0059031b0109000d500e60002d00e01d0992042005c2c20080c0c5070140705003150a2240781100e009004420020f40703c0d00b00440c0420306485104d201c406c658469441c0c0c04080c2040e00211855070b01d01e4a0301c0d111400000c00020b440b0200c94001d004010ac00c10244144000b401420929403500c803420017030000c038008011a045840c10030f02c0e001d00d1050501c003858038240302143c2c02c040c10400d580318142480c1502240d011802d41d102c03015441c0d00068480b42600c64ad11598014003040c004c9000d4116180d805400801e51290b00310190340356503448410a40140c0100303035020b08a94410001400040b032200e008100c624080e0040702d040c060304401540c252000480310f484095004000d005055810501e07550700440211200030300d481c1030041c000c0d070f09d000051500628600307007650700c200c0d91380611002d03200340c1c190102800380751181c800241c09081c42c0c0c8402c1752140700c5c03248144150718864040d101 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 615585125 1250 615583875 615583909
    0x80115080c0a0c03051209070f080d0e1c050109080a1202030c0a0309030c05031606050105040209010804060c0309020d08130f0305070504020708040b070c141c0f0804030b0708010e0105 81
    0x2040400c0403004a9081100c104110240b003400c0050a520000c0c01c2001c031f01c5003003200014000c09003801c2e1a0324204116511804607648101003848009812210a1200740fa00303841c40600140c4034804004803e1922502030015403070441020280070300e000c020401072030540c41d418400080020883d04a200841c0c6840360040b041c4000c001c0244290042006940a0701d45501310185a4031401c2c110313880701458458590401100d01d0402502d8040c083c010001183c046040c8946980040d010900081000700055076465070880b144d400b030381c0400c048640150210031880e500d450511000c0e03100100c040555a0710f5000042c00f1707109030200340e00f9680d004000e8070840385001c1c2844080d4100d820b00722920031084c08003252400703995018010843c002e070304240e402c40c85d02103071042e00102521524090340e1555494a2952000800d0701001c5600490b007401c20303901814200301c14041c039000101100d413203a047c0318005034420107190684400300000d40303c0743d80e01e88c10800341c0700011201e08 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 615586375 1250 615585125 615585127
    0xf06070c05090a140a020705070605070b0402010e03071805060906090702030a11012904050a0527070312090e010819080a0c0c0602100b09010f030807080f0a080115080c 74
    0x20000341040e0b1001c41e0001e01001c0d0119040d070031156068070390310b02128082d104a5000c6009001e200302044490020025400c0c141e00e445210b49808581c1c5000034006814000c84009804054030f0400013900200401598a08089956404400901401c0c0c900c98440c010580108000b0b140c071000d964000c00d0107400540c038000e503064040e121003680031a0444155a01c03001d8a20b01412101c11000c0f01c0c840318070140a036010b801c1004110341c009054108064038207420844511000d80010400030f5031020105002c00e1700d01d012078641040fa03000100b54122480760b0040f1240c0048014007a13404114400c8010f03a25100b281d591b5113120035440000d41e48030300024000c500381d10300401d0075090f18503140303040d1b05554444801a40ca83e60284006a03c003071200c00314400d0b00e1183d0305a9003021140d180e41075141510341200030701c0d14000940b42182c006020402c002e185070454102d1411043c0940d00c2d0902a04058201d000c00d01c11241031780003450401030440e00c95141140300d2900b0061503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 615587625 1250 615586375 615586379
    0x605091509011203050408150105010f210f0207050a1410020901020d0807030b0909030a1b0f06020c0312010305030a0809010212041e0606080f010b060415031e0c020c0f06070c 77
    0x2030030f9010a500083d01401403c000104000c003090101e1a131400c00040c00140a51520000605800140000c04104103244019005e960240100d510b42d40208074130100c1d0004a016000c4020310464000400611404059030100440da01d805042e07001844142c2d204614500724980170b80c482c41d503400e40140c1000008646260054070700382d401070003900d400200741c01101c0c00324045d00400c1d10303030042540c8042040c41a01c1c2d4002d01c0c00d20420381c001a004c1c907418403a501c04480301e00840d0014030091300030401380d101030020030580703030100c03451600800d0030350b507900741262603a11401c1c120b800a0f15000000d84650414000c5486c0403a11402c16200360ba00c0c1d0300d5501c04412720003131100400983c06c035000e021500700c0c090000500381c60009032000f0746524844608482900c40f2550242409100c200001d1922488010b2804003500b400300d20440c0b07040c0100a4080c620400201040ca0080006815580007a010194103019580d0364911000b04080102034024031000414141d28a182 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 615588875 1250 615587625 615587639
    0x1201030209040f050604151a01210e0a120e0402030403170601050405030318090601020c21210703080a0501050d030c1a130b010f1802090f1201060509150901 69
    0x400e0750281c01030701c10042c1c00364140d945904204050b071b020355140300b00a00b105854000c521032070491000160074180442c0007040044d0100114003180200c01c003190141c054000c1013038000085d00c07010441070f102260000d10f00b40701282c0524580b04000307400e8683d43d40c01d9041034400c4030b0055415860f61007121700d40c909030702c0c040c0c04001c00445c10042c1c1403000080c551000c10203011b044d0040c004003011142840c00744080d00d00c000342458119481803001502c01d40b21184124190a12420b0b00c0c0200d880c00d4140c645403c034400c03a80c050444207600c01a07a5042e81c2e0700a042e0702e52081d80d8403034107525005150000d80d10203004544d40201103410f0340002901807806500302c18414079141080d4a01c3c540d032482d200004680d4405c0e113940c01251001003001c1c025001c2e0150440543e243d0201e4106014006142104c001080c0e40c20b500098504643e40c0340c0301c040d80c26003002090b213040d00031103d42681c084c111500c503403405046410041035842c1d030501d04802c0b102d14054003903075aa07841e0401c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 615590125 1250 615588875 615588889
    0x7022e0213050307060905030c040506150304061e091104151e030b010803040f0618031101020f0f0c190e0a0506010c0b090303011502061e1009020d050a06060512010302 74
    0x1400c1c0030350200950000940f600c09008500081c00d6070340711980b003d49003001b070508095451101c90310441c41c00c010400c040d5500b4412445100f940101583c481d079492a1820041102441c0d10031040c030500d904a4816070b20350809c0004610401c1d40c1d00c40c4080c1402401300307a90300044c001030462964401400b8000e01c43c00400b0000c0710b46c40c0308450103580c075215490a00c0c020b812881c6150030000d01445040254800703500101407625008065aa10162002ca10031b11030000401c1103912541c01d0659a10070407840c50390110a0301030ba00c41400102504c2d42c3d8250000c80617004071071102d40c582600c60303084688012503c0d2a800c1682c1c0751384148044005110041000b8184245140d20002044100007624401c0584800071580c80d410800d4200030b0841e01d944404c21035220301d0810028120220104050840313546040029032200800ca50414001e900f0040d01c4502c049090926811160049801007114043c104a032a03103541003160700f84071390003d00c560600014010001402c10038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 615591375 1250 615590125 615590137
    0x8090a021e0405160801080313120206071e020406080312010b09010201021303030c0c1a070b180a0501090b010b03101202030a06050108060f0604020307090b1602120607022e02 77
    0x8001c0841d07456000001070450308142e41044c680c01e4030760005100b0a4200368010b015200380c40080d420082c07018204452030500e4015116194005001d400864550340c060700e0003664014520444d459081506120403800c104082c0d10483c1031400c0014034030340110840d8080d48412240e14056802c1600c0b001c0d440c0d004000c0c2c1d40c11591300b084200352899244902d01c014500c00e0307692080c180303c1d1341486107210007a9045501140c04070392100154460901c01c4a8030154040d00050144e6a1182c0b40c089811050700c0005050081c480550200070041d44100082c61043c0e000030b00d1640c940840c1042400300700c3e0004042c9517288014002c41002c0d154600100d07200504440003c010350380d603d010760304207034450a5158000e0050101d04c0300402c010740c0d441341c8142d07011411807a0413040144804114812030324101070014081035040381e41d0608036291900540721800a42d800880039036103840498846005001d11803241c1215402d100100d410881042244041c0400c2440d41c0c0d4002d40c003003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 615592625 1250 615591375 615591409
    0x20c010e030a0503190206010f0b04051e120f0106080c091b09191403010e12090109090e150f1311030f01060902030108071e030f081b0307021008090a02 67
    0x740b059400204100010300c154824150200e0148a1007803020f8a8440c0c180c10a504201000c0c0040c00f00180490981e41100c100700e62641000740c2c020102c41700e01803031a482c990403035810078a00c0120000011640035402079980204007d0f0303551680300703032540018150340360f22001600110b484a410904180102c40c50111080d10340344040700014848085100300002800d502d5030104403034100302d0016281040250000d110042071202ca40d5103a02c5403141b28051060003280b4641d40e80d06c920181d0015201140d07040203060f103ea540203a450f41410381d60070007070740341d07800040c2080c040070009400b902000c00489950a25903985210315044850710705e41601c40c03942198003900c824003900c2c005142400c00141d40c0d505003240d01e802c251464005c0d8585141c0840420107060b107940022085941050600c00244028680598103124901078070ac05c002d980044001c050300c002c4018840700307200304c03900036200e401a2401e448001040703440e455190402d03400701d4003500b09180d100c04000c2c85 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 615593875 1250 615592625 615592633
    0x1b010614062b050703111603110a02121015080a0b06060d050f012105120a09080307032708031801030219090503120903060411180c090306010f06020c010e03 69
    0x21405241c82c440711440780c0b00c0d1043c2c49078103102c000d43c0c041c418050040e0042824600d01900015441100210500700401704815641900c0c00c500e003d200e495101135000b4401c480c00040c00e45a00e603652005144140c940d407500c030030381640b110b044070840c1c1102ca00c00e0140002c0700e2140c440c00c0c245c4800a00321030300000200401074510b003640c13207000e12034050900f08401c15410701c800442d002101100e04441074800c1c403105000f14400281d449a020210341d000e43d40d44c4030303801007265041e540707905c1640a48804038035030040541101d211300008409248212400d40304038090340c0e044043d449600910f400400c2090f03540100d0300c2040041d40018140540781440520b84060354a4159821794001a140a4140315900e020301040c1c000c90703040314086061038171700c1c13001984031a4003130300c0140f004800400d000190b4540d25140c51080400501450311440d182c003280c00107900c0301c04070901c02d0059030008a203004e107000c2d41505680303295005015441c940c0300156035503046050f8060b0700d441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 615595125 1250 615593875 615593917
    0x409091b300618060f02030c040e2203050a0f09230d0209070c051005060102070612110301090606030e0714040e0c06040b37080a0e060a021b01061406 66
    0x8540030350202c000d143c500200ba44509800c0c07050481d802d5454042c000c43c010400d01c9a207060150507a01903e6941d41052a20b07192041680011510031105116021112080b1014150490044c0c03030000540d807a9042000380d801d50849024a00d8000c450502858055215040d51420000c400c259005001075010700380540000796070788011a2010006841c005061080080c2445a490b854600c0c540a020310304008002030b4641c4a240110340c00c00104801e034000c00ca0311b541100d9a100300c1d0040c650f540e0351310b449a440241805000c0d91000c24241401c1921081000800300102c0d100400003083c000614001c20018060710100183d0520a0049042440e80e420000b0700003441d5421100d030f079031a0945820003d80244410400340a0745040780461802c41c40c02e07000d0f42000507840d0000042c0d840c0819580103002504603529944259030400400c11400d60080403040703401d05c0800c41c0100460603940c01d2703482c280941c2e0060314081030010510300701400070341500e810484541d61080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 615596375 1250 615595125 615595133
    0x6080a021c2a03050f01030305030714030a270c1401050d060b070311030f030601052a06010905010b09031002090a05060d05040611071110020c03030409091b30 70
    0x48944081081c401111075004a00d80312a41c2c25540030905402c06101d00e1400c44100010b01405200c00b5081c48000400285040c0c0301c0e2010b08140310008421903164200844040b0040620703406c006980884094000c0c881d801181e400d00d2020742c45051041c0382c0e81803048407100d4040300000181409014001ca400e074241e18040c0c0809803003841200741c1c6680c00f80c1001010a1903003001c00e4082d4000b08040c84100301400101c0394400d00c213013000f075618003804840d01d8110101005028030442090849506105e01081c25812110348001c10700ca0f030798034ac0380015118400d003504a98140d001c00c1d40417490b081260050a04104010800d00841c3d03075a401050700c43d03100b24004000d56688100304010883e2074418541d10b42081582c0604015841d075406100d03c90081742144228060640000d07168402c0140015000380a010760b0340715545c074400c1c24060701c4034040c212498100540b142460540b1862808121034030180d080080707552103480d14210581210030328042d1038103040d2150110b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 615597625 1250 615596375 615596381
    0xd0b0603150f010509120102130909200613080a06050702030a0219020d1b170d120e0c13090c080c010c0b0a0e01091406130c1701060e1015050406080a021c 68
    0x7810f07500008d41c6da080c0110203580d10100f503410856219180c04125804220700b2040c103464401340640d042140942c500014086020300c409064000f142d0a4012404400204540340076038814003083c441c030f0311400401e03a01c81c00b0381403124005030300107003c842d0442c0768070401180d481c1c0090042541100184c60300c5005c10500480171000c1c0780003880802c1140070030094180d0150040d00034200300440f101004004001c0851000700c11070321541910742e084403e1141080014004044885000b00c0a61103006802c4840064500003d00c0000044402d004642142c603030505030b64554503c205541c40b40c184901c060500ca80e0300380c1d10880102000000d2052401c803d0054030281048810341c00443d25095004202c61031005540c1209400100d0139000300060361002d01180b8400030342c8151031030041c07103140c0c000356070a42010103004e0084220226a000e81d844908015030703c0035191801d0707429211b544110710005a58900007400100c150340980328a0b03d180e9110b089480305440b840044e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 615598875 1250 615597625 615597649
    0x60b16030c1202010c080106030c0504060305041e03020106170316030c030219080409050c1c02210406090c0506120f0a0b030d11010605030a030c02090703150b0d0b0603150f010509 79
    0x9031703540b9029000010780080f002c40c01008949010300c85081c00405c01400d2f8002d910415040c03588170b001103020040d508600c00011380350300021041a030444d00f070080c0a441280314180e9800388501300078410860203c01c0302d90100d03180c1003c0c41c00e0641560201c555006140f416030850040c182400c000e24902d000703500603203021b0f2081580312070506104408480e0058581901071004120800405580380b801040751039a0030700060700c65034a203c02c01100520208215060740f110020042003200c140d100b01d010340d0185641100c801e80712010302c6181d10400210081c20106000002c2d202c0e0001d52520780e01200e192400b250500c01100820720700340c03440a064000c80d4403148044c0ad026001d10640000f00012002840880b030140c17030207001c031024458042c3c020003a910016020301d00030381101c48900c0d401301c200000390f5600d200c16540c98000707000ca96501400e01002c1c01807072038a40c0a1780d000d04a00c203d03803100e50441c5401c000351040c0403200740b81408014416005c4540d0b0b0030100c209 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 615600125 1250 615598875 615598877
    0x1b0a03030b0414061f050d240b030c0708130902030f090c01082a1b03040305070905040206120703200a0207050a0602030a08090a021e010e04060b16030c12 68
    0xc28410715400c010507501c801000188121103481002019603d40140c80040c10300d411032481c030303060180d000702d070716228107070380d20002c0d80c1010745000848820081d036040c40d02d000c1e01468280303610b03419003818620042e502c150340c1100c180040000f00e5a1900200510782040c404212096912141b40060760011514540d101c601e100802c03c02a00501a11001c03400c00d01e459100340c6000c0e031501c0442c00c11040744440c03040c02c0300074001c9504451401c42c0c00d481464021201500720030000716aa03540640400c5a0314050040009000d60160042074010b59006001604019403006109040300e001800b400c10140c644113908011950800c496501741c407850034040e5141c0d0300c00b401901d0700c0311541c0864080d4034806405c100c115404801c0d10003110b61303407400b0030817919200442803803c1205a00a51b009040c0000303c0d405c02030541c08008080c1007a01c075155154001c07410032048031482e105000310304100700500e04140d00c0707000c0c0542d86180702c2d081a900e02c41940d142c11810084420721302c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 615601375 1250 615600125 615600131
    0x1c0e0703060b09090703020907050a0509150307180b180d12080a0605010503010e0606030702070305060a0c08070309030903080c190804050319030210151502150709060c02061b0a0303 80
    0x2810b11501c180e03031058130100109104c520f940d010941500d0001c101c0000c12202003001b492079840f4070100c82c400c1c4002000314440340c0b0303000c909401590003502c8072000f081f20021840d040c940f600b51003c0859480c3c0400c5810504103407042011450750791495584a80ca01d400e0300c0c0002d9007022803000075080b658481010b40742c1040c50400310740b92a0002c50510400340010001e049010104550001c01602d645449480f00700d4180e01d05100f03600010000e000b007104000018545602c610b0500003981e6800003980c5482c0c2c420f400f25400c03164040c0020b05848028000b01d800d0310001c1188040e400e00b00c60320030384019404450040214411038440c00700090030021450200200b0365500c0000d2008a844651130758007030343e1928040b45500da801d888207400c01040c003024406200130310801201d0460780b26005e034003d403500525900210950498000309140034810840309050b54a03a84403880c3c241000d80030031403249c00014004242840c80400c1690710f010500003100c2e001e00c0381e00d001c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 615602625 1250 615601375 615601391
    0x901060501030c11100b150c03031f0803070201080405071e050414010509010e060d02100f1d0312161a01030b06061e0307112d070b1c0e070306 63
    0x10155060008200d00700101c10b04246000140480c8617611075121034400030f101c004945c00710311f244240d561000342a04010981c01c8200c84003000031446146515280010980e15044d00303840040607010f042410b0b0300a000320030042d409000f01c51380103401282100c0c01560703682c1e0700300711100c894a5004a5152803520030032490400e40100c0e41030341c3c10b90b16030882d190704020104564010512850403102010004100c1d95102d1250650788030350040e101500c00c2012641c003030400c9902628a03400200b8190040e03802000c01e1142c40340700c010040281100f0785440c02c0e84103c030b41012899040d2004c21041d00400500403040300d0554050800090440d0342c9503040014580e03200030300d40d42c0910010840348254100c42c04140e0720000492103c81d03200d4888240803504c5c1300261000115511501404103c0324a125982d49000e04040c42014409940810b103243c54072050711401c02c009105000349a0308001c14201038010104800000403110140040c043c50506154401d0340c81a40c0c030090 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 615603875 1250 615602625 615602627
    0xa050403033204170c01020c13020904020a0801050907080408090105090f090f0f01170706080a0914100b03030903030d0903120f0b12150703021812070e0919030c0c030503030901060501 81
    0x40801610044000d0442d001080340081d44071102c14008e40d09c60074910a9480401405034107a88409601070811503d40700c142201424030350003805580c2c45404d41c1800070740310920450006104a0b0300c000c600742402121030043d103080d001024282da04c03001d662441d40154442c40c012074030440905403602c00d541040c07106041e000704103030003030121060110b41c84200d65100003090001c81d0020b2400050903902d003541503004085401008181d188404000c1c00700030000207041c86d05660302d520401480000d10101507407442124030b0160140c01c184500d49490350390360b0295850500a080a41101c621031401c08101d0713030bd1040c00041196a0019170101e400c007d03050940303003851040142201311952407503d00507000103101c0002c00d03400240322541c4060b064407801302244042d14003901d68102d03115998641c10140120681d4640c40c00018290500001c1c121900380344014103c50035071002d450844103003a08081c240e8038460004000000540200025480350300c202d00000364103070034100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 615605125 1250 615603875 615603899
    0x609060c0c0f020105030a0e06160e060a1205070c050f032101032112090b0603010f050c0414010e0d120e030706090b030a0902060a230a050403033204 66
    0x490310042081280005000a00014807041d000b502404d00944955404443c1e030003400609281c5200f501812050080d18200e0864a01d00d1131015221261303902c030300b03209014503070242c001c00d28001a80001d6000701440e80ba40080d07041600e0780b61269540c002d90311074910307046000c00951459800004c015407007070003040b910b078082030301c101010b03d0304d51568403013110080380300511f4005540c48040b50312500303000704000700768404aa0750a002e00200c80c00c10041591301122618041e509000307003101d58110a204082c4a40840c924090515040000748443e08900000181c180101c807188480183d80341421280c14500c16440740800e0b580c00b2900170030700d800c0c0c800707030a0003588000710a00100741c1000c3c4d40015075440c0c0309026244e546840b411301c0a042020700294000c9400140804420b501004401000c1d449006540740c50003107084280062280e032030040d0003c3c005100a100181c0b01d20ac0c0008006141085c100d2481d02040107080c00c601001c0489584110004080140c114524 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 615606375 1250 615605125 615605141
    0x7051c020a0804020103021b2406150f16021815040902010e012307050d08090318010507020d0c0f14011e050309150106031d030316080a06080a060906 66
    0x42000e506059840794080c140c84800341c0001d05164000c40c07401010092030760350351003458070075084800c104040020b2291080444074002d00c403042c01400209039003031035008800b50300c00c281005403900c000210001280d80086485a44403240c482e011070141c0d541601618600350450384502d03c3e0b040988054060800c00460303507001d5414400140003513038001c00b46141c5104203003440e4aa5900c41168000b03c00a015503101c00c40c6e2003c240030003031100000c3c0052240030252943e20041d143d1000c820359030301500000c540d0203a0584200451781d44102c01900e03c503031001d00004210711096a40f040031000341e4204c001c0c9030090000401c075035980d0b8038412000880030f0800021500000400070121060304a40c0340601c40e00201003138219a0800072914041c9403000001c0c11942c6580000300503015003008010701d41500900001103150100482e0701440071548005051110100c00355042e4a00a10248101e555403200042c0e1690900c0000a41740c413480300050002c10360715061049039006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 615607625 1250 615606375 615606427
    0xe100f15050301150308090d050111040f0608010308030403030c090b160204060603060311090601180603203a0c17090f03120c0403060e0f07080d0504050123030705 72
    0x2084e801d403181c005082812050300c1c1c01128203a5503660240101c1c00026402c5001007a0b0743c41d103091070309107040580191003902c898103004418039070790f41004c0301c042c0020700014100240400102d00043d0003544074000d211060b00304001c40540d0703149a0401030700846080301d00740c00300420000440c5460300c5000e0113802c0505040045d0750031074441120348162080118001e820001c08940540c2c000d66641e1344442c035184010107a59103601008014140c600c80f4802c8051041e005608140070f01402c1d03074100c101029070301642c42c040e08540401240b001c1148400c0f128445110448002c0300e00981119110070b4982c000380072001d804950b96510b000f89002441d030400c1481f0003c1d0390011040b50520035101c50004034903101d0543e13080003407160394001400140f4144160610000c080f41040c01004a04191380301940d41c1c0280a4842400c0044500020b000704070a02507503009000c41c8100d8510318403680042c480b240c0180f22160710980d00300c00030941c0440c0c210700599a0b8482401c0c1e041c54 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 615608875 1250 615607625 615607631
    0xc0109140f0312040507050d12030c030b06090d1a181207170f09040c031d0705090115020106090f020c070f08060103030302030405031c020c1506060304060e100f15050301 75
    0x184440d071a00c0703004001140c2c14800741d04012506015080080c10054903000700807201c0c61549240240c50340403406115000b1908044400440c94082d1182c00b04a800240100b42b42c4405042004541d5140e00340444e82c050100120402d220080000715108801c4a104244450070f421800c074600b01c0307460b8115032610300800680700002d81480540e298802d21048140d228510000803032200d0003070b0b06e22541c210749484d01800788594107410014041c14100c0c441c400d50904a41029101c00c01c0d030003000d0308080420010800b00c075040d0982001f0880b50320001031043e482e086103006031840d10001c1200e464020036091f03400e00302845071800070110356101a042c40e01c1d0159454032400d05110280c14507a0110020b020b1100610440e001210305040011640340038044140003500304003160851403240c0400c01012042e0740032000d00a940c01071203182175a5480e50750301c029001441c003084107402400340c4005000c51902900d15100e00b030600c0802c1003090311b2074001200f4216030100c1d1081e81 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 615610125 1250 615608875 615608893
    0x1902030307140c0d0f140a0804020405150f0f01020c0a12020f06030f1303031d010522030203390a05160506160203010e19210f03020711060c010914 65
    0xc0d0029a240608409017009842125283c0d07050715160b40603031011104000010301c00702c00c994400c040c64031480c0f00310b60070042525800001450b650114400b940c00950003103071348501d4581060748a0a4460500c1256210607450340401d061a280d03502194a41c041340e0004011450704440d1200c031542e00745c8200e03003549000040f000c8060005001c14814400e100340003001d040c0300b03400c0b100b03800814480c5000d441152000c11030017481d003100c0c0000c98000701d8680000d03600410924160098041c0d005606015004a4a100c41006030200300900030412202e15104030310b180501440c01c070050702410329030340b05040c100c1c10300005c00822942a42528402e000e513a49040645401e2002c0b241981070346156480400c5c014044503020041c075206d000d0b021128100800215103400c1d11801e0310042800750032035610080602c90308071102051100341d0550b0784078404e901804015005d00ca1500c818182c01e80800c00a43c4075105280140e5104c203814001d10803648444401408800001c1540307603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 615611375 1250 615610125 615610147
    0xf0b0714010b0d0b09031611030f0304140f04020d0c0206041101020105060a031407091d070e01050f06030a1503140d1d10120203070f0909060f0e0408190203030714 72
    0x301d0800f0010024004c0c040418a130007010001d81d85440e03030410404000c10a0340c10f2194101d00d0308a0410711034480d0b00494200c800300070081e10100c0310032212107842100d047d802c106030788003c0c2c00780a40180d030034000409a40c0950292802d84002e0b90050082400c1506180c2d8135407a0011000303055a0400c1e05120b500c0d00c2c1c15261100320780d000303900c2c0c0c07403041040c01109042c187d060f404038540c1070420440f11004012540800e0010107650121040380780d503a0101a00800c01b480354039404040c003080210107081400081d50700002800300024022100c008034a44c0c5c1325540c000f56507007800500520043e80701045005000a00d40c100401001d9031081d071302d4021214403007442d004012241e0070080c6203005000e11401136500090540d1640391840c0010044140766200c074001071080d0200091100d541d10948040d59148c1c540c44004508200e81c00703108440c090021a03044404206410301185a0007110501030040d40c003856a0b411711800041100b0320708018241c4002080280941e40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 615612625 1250 615611375 615611389
    0xc120c050408060106180b0c1c020607120e06012907060501050f09090d03020912120705010c0f09060507080c010c0e040b03010c0c1407050613060201050123190f0b0714010b 76
    0xb0784412100a07178a401c5d41e0700075803c1035050b131380740c00b0401001c00c9d00208440d00414440d10401169644000e000180c0841c80c00303442c24408040410b0b08880e00500100a9110440311034034a1110241c0c24079112822460150344507410a036021340e5075100600440c170b491006c0619226007101c0205403402c14020a544034010310b0b00f40300505500040241040e12880341000340d102d40102907401303840030312078422204d41c00311408032025440c207000c8407820303405007003040c070750042c0d0340e03240e40a0500b02841a5441d40c803050382034408542c18000105440d0007406114110355607540d400361b440b0134850501043c2c03440c40a02e24070a9051416031803c40380d100c540300b500550000010202c80b07030b180580901f405003d4120b6600140006507001400345104002e10440e401b030380c02000b050fa621a01d031141612141820b441f60a40c881050802d49408203201040b510001020860583c1d1480c03c8032640000b41d0000c10301d214045181014081d01c003143c1c0310344008a000901004507090002464 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 615613875 1250 615612625 615612629
    0x4060b09040522060b040e0d080c0c070e01140301060503190206091c0b04030806040b010c0221030d090501140c2205090a02071101020c03030d0c120c05040806010618 73
    0x655a82d0001520b80300f0300810320b8204000c149201401d00349903040500c060009410300b01d016030306002c0080d0903600001210355080740da660316498280c80700074010020313078003c0d9151040352090103c00310796411f5414003680203160400e14000e030b001201050601b5a2282c3d84201d10a8120401d02d002c02c4503140f0b10b101e0700310780c1150035070740d02c40c1c8a0740095003da0405445407006503243c224442004503500d141c40c0241d0007901c890031b02d03a503240b08000035544007008140c00184c182034594014240300b5810060300f6844404070f40c3c040124010913140d80c10040d05100c240c2d89440039441802803c0c03150205024003400010813074039084840c04101c1c41203004c0d15200c018084800c0320725803c28182c14010340310040c44031005081c1800120080c0d00040016179801c0031510400e80c040d0b000159003c45030300c000e0080c509041420382290020164545034406102c850407044540220724811060b1607142a00d0303a0380c5581c100070400d850400c2c149c028200744012400758540a0226900c5001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 615615125 1250 615613875 615613879
    0x30504140a030b040506040b090a0f0303090510050f0115090807173a080f150f09010e040c1707050907090b0c060a0509280515090606090604060b09 65
    0x403098444008244890655400640010320510a0004000020403994080d41c01181d1510712611188100c50702c607409540c00030034035001e40b001c0b0f0780000e00035045250351314000e00a0710b0300a9450111801680c104482c000582e10b0a2401400141400815012070181c6803411910076410966203030b81d035400074001c0348038881d01e203a03032204201f90812540c903a00c910380e280058a000305888012200c002070000b01180c41d071542580e2040d078490b502c610f104903c01c04800000d6140c540030040d0200390301c66110303000100100c01d45495121a50143d000300780c1000001c20a240c181042d01d90841c0981024001100c010090700c0e000900207210001e481003110a148141c552910545a951310b56210340111140469004645000481c0741d0b07110340000c04091000d940c3c3c403624507840b03800d108619041d0298899001d2140c2c103524285003000b0b4400c50444100150080a009150000f1905810141d000c207040007550b08041c0000d9401c050150340c180659810071440070858056081014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 615616375 1250 615615125 615615149
    0x10080d05070b0f0c1b210307080403030902310513020306010312090504050c120c03010b1602061209030406110d1d01030f1e060f14060c01020c0123070903030504 71
    0x14151098860844880305640d545c45110420480e600756100d000c550504078440c10f40da000c081c11407040302c00701e034401e844503540d0440613074840c0d400b0740042c019044140c0c1c0200d000c0140c00940300c81402201542d900d480d00320000742c8560b440300000d44100038170008962500241c03601c010303180060f00740c0c103582c1c1c4032050b5481c03080140740c11210706000e5402280d0103410718040c4004100b10301c0c020143d105d90b001481540b5a10100302c5c2440e44001c5c855401c2e0322104101d00e070b02c40300003178541c4c0804034402042c25190a007142c000003071601c001e81e041300305904002030411242e50000301c2004200c0c0910003601114487d8080900901000d000a050306600244400d00380d0713100ba8807210729050100400c024051024401c11014428252180707405032401c40c004ca40038024070404011200900902e0031004000000c0c02107030f4100c10481d0b03019640900c8040d8000d4800c0c000c030130148411506c4003004024040541e910390034040e001006100940c83c0a00101780e21108440984122446c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 615617625 1250 615616375 615616381
    0x304030c060902033c1f0204120605090d03050106021e1e06010807080f100c020a30030c08011e090203360a06110c010510080d05070b0f 60
    0x201c0501042c0d10b000350305020f190396520f6800001e40c181502d05000d000d5108681e0007814110b138200b2540940d0485a0b40a0310041c440024900e42410301044510b20241c1415a20b141d400ca0741a20301000710b40107601d8408001d050001009009508411850280455454010043e46400c04200c00034080c0322003030f03900d1442c10010841c8045145030142d00c08051040074045580b104402c1c0140c22143c01583c10003d0360550000f1955103003070041000d09113500e080c038003040081600458007802d41c011040341802203030000085031a06c403090480710741c8442a080b204070b04024101c04190500d442c122a1109050340560942c0c159409403140083c0040c03000a0302c50f00514aa0107811214000002c00198021941050254541c680d40764082203500d00343d401c1d40321403000c0e800c19166128903414008121142c0107109240e600c0d0161500d0107003000d030000c0c255102119907500d0710040003001c00c03031345000700007241d03110006180107420495250740340008100084c16150700e5041c00004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 615618875 1250 615617625 615617633
    0x120307150c1107290415210e03030a022104060b18221104020a050d0608030408030a050a1407060c08070e0604090b12071706060d030e100c0b090c150705030304030c 72
    0x855020b02040103062020090181e4000e05100c7e0601c000c0c2141b20710300b900700d1030540c0035000b00200101424091400c50f520120000e00a40045103042e420f80364103048203500142c1c4d20a4217000c0ea00070800818400030340d10510a06922400c100c0c1c0101c440030f0100b14030403000c1d44051182010750b40d03811150032100c1c14404441c095450416501920002e104004903401c2801000908030280081c40181d41d41c8100b0b64807405588101c0c4090b0f0000c1103550350203482080100000c00f81800c200c130707070000d0b0310f040074030b0740d03005580e0480380d0564401404440c00d801450141c0c7c030074114913140c81624911404039a0b1400349100315254607494040a0364641e541c2021031200700c200da0102c5580310360354400500500c044000303584060048001151640c1401c112103a8229013548600040d02c03504014401685030300e1400008110720b0303104c003070002030800840d903028280c103500500c1c104860b201004800e40c032020180c00c0042c82040803000044020055039403058043c10b00e02000161420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 615620125 1250 615618875 615618877
    0xe16030f0c180207061103010503120703140304061e0c021b060919031a0f011a07120f020706030902030a0f140313090e03090f120307150c110729 64
    0xc0d1078048034400c0c1c42c25624441e4080c0480d540900c50600a4143c5070b140612244404e005a903055044061031505000c0510001c041c0c15100749000700c295440d540101c8800c1c0c1098034101ca42c0c944840035400c50741d44001503d84030356000e0004004055489c50301035030314410030031885992024030200001c10b5450000b80c034614070000e48401d5000c3c0d04a00b81c1010408240001c503641c1e42c5802c0741c0c0c600781601558991140c155494441102d0342405101000c07122054100c070565481086008001600c2a85450f000030302c6455040c019080040e001c4d0030030310300b508400b040605d011500310142c7d03400554640255040f01c80700e1404400c9041460120340c0032500210f2074480002d40440c0b54041c07034065812104101401c00c540c00010400315102e10803001019440002d1424840d414038100b00c5020400c0407050442c0d1070105280c6d03e401048030a0456010340d03a66a026044550b030300319801d8140117029002915885003001c402a586921a1170800d800b40d048031425240c0c402414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 615621375 1250 615620125 615620129
    0xd02040e071e0503010507080c03060628080a180305030a0b0609030307140c040605030607030c030b2112270103090605090d110105061c050a020a0f090e16030f0c 71
    0x1e42c41400e001180560111602a6446024003e40ca4030b00001d0020b071042034024010441c0081c11451034580c4820010300b41c10142d40042d2690720803020309030428841c4c10410310540300ea1640c2d40507141c445104411280309450340303a4840c05c1155000b0000343e211007100c0e4003603410f9000141800000002c180b150281510b001c0c0c044c800028000c0500070243e1070801040c10360000c403103000502c8800e0006840042c40340c260558040030205070841c1c00b0b504a1140000a0f14000402c0c0701c429001824103071004c5142e508180d141060361207854000e010400340747c44003080040c0340c0100800f013032340701c203d00041082c000c001040121000b0f0b807082c6c0203665041c0c3c10a03400d21403410714080d41e40e03d51100d0b46080c00400d01d0700451000d054010f01420344540401842e001d203c900e41034440618015002084486015801346200140d843c41c2061014143c295021160340d402c0103c9141126804071920f20594084044c0c88240359282d0940001d0340e901c81080342e414501c62800d0004802c290b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 615622625 1250 615621375 615621389
    0xf0720011d1b030c0a2d0f0303080f04030504051905090f060405060a18150504020d0b1011280b01060305060a1733010b1809060d02040e07 61
    0x3040e5036988660000340200180c103800702400841600b03404060341e81d005203ca4680120a1400420030442e6004144030b0b14441d02107020180300c00b1751244401c80364075800041e040c01c0804c206100740342d440407015502c08504400c00c900d60829882c050002c0c0194410284a03011070192143d642d480326001d00c0040c1405047e8021505100b00403c0c10440100c0d03d0b2805286800700040d51803034088021811900c40042d011180080b64804501601101016000701c00c01a4400201501c1e1780c0300901c4901003040c000504c412034542040400c0c900c903000c0c20200b225400304001d01c444045030b512414030381403818800065031114070340041c0840c0d0a014040d60001c20001501c02d8058201e60b1042a040f5201d40c140350320b07003082403281135055464000d143c0c0704210003804000b4001403021281d5803c0000d240302c8443c5c041c0d02e04c070030100b60030800d07408002040300500001101c5070386480c20f10854030056140350400c0460741201034031501074811500d50840c0602400d090160401030401c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 615623875 1250 615622625 615622661
    0x70b01030f030915080a05060913061a032a010c080306090712150501140f030f07020a050303040f1e020105270307030f02030601090203190906060b041205060f072001 73
    0x150100183c0100006c030341100315142868009140741c584014030a21802caaa0001096501151206002001c4620303c02100000202c030203012990100300300b20740003da47e810803600600014038880c184403800440350522a41d0141040050403d40c2981c0d4000c8082d10803510700d039a16401203c1204a00a002c0b020303d150020100c0d240c0c102940c00c80070f4400c280c0b250114883c100e0102a202e11034042811011134013440403c5240d100702c82d40c03603001002441180c0d0410030f6512183d040d0f504c03c1e601114490081c1444008100c20894091403410706145a0300a80f0504e80029149100d04010b0b110b2525505064080c0701d00c141803507841651001d021905281c1e05c038030f1300035456980107130240c0c030134407900c07000051055080c000c480c801c04100744000300c10820810010084e000100040300d2180d1034078004600c0b509600702034001000481e003803801e01e420a00b0040d00f0600c001d4903014144048504215026401c2a030000c400c1d10441205188100f0b03102880d4014410f1036410100c03041c07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 615625125 1250 615623875 615623909
    0x1b081005121506010e030a0b0c1207020616020c0105040e0402041413060506090405120d021e180a0b090d1e08031830090307030c0f0803070b01030f0309 67
    0x60300040003000d60000c0380c0380b034116450740340064641c02000d100550f410341c0000c01700f100041c0100034681d00b020311100d040b0300f801944040040d10341011904040160b0000080100c1c3c0041071200c039288400c0340c005032000d920458002403681c800c40c007806140824040c0407034119192507000d0513a4204100c183d2645003403075a61742d032194044990a44451b420440480d0043c40d0016002c0c2c0110b600a000f800074643d0292141c0d01d98004081040d82d0650130b2200d080c10302801c600400707003010805591b0703030382d42403c02d85400445201403a03103000e042c209800340300340380118003100c44060044441074800b8005103060f0403000065032040032f0308410303040d06004004c280005940126001d00040c04d89041d22081c4660341c2800f0500c08240b00314071007424171900000030004403c10f001300301c1d151800c029800031030b141000946c000c80d1030103108401005001c100c0510b0b840075142c07450107549403d2240d21012034034041804050000300080d2900c004041c0070b00e1480d801040550706508900e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 615626375 1250 615625125 615625159
    0x9050114131b0305370818010e030a020123030405012003150103050a1104080607200c04091109040b04210206060f0621090105070e01050d0c090f08010501080f011b081005 75
    0x21f04505062505242c5090303000d20b8940c001d290000c0186005130080800b054190011104410044602480c41d08407035810102101c44c0c0b0011271040380114000314171030502d41400c40501101c100025020701c018030520032610183c09100755403003001d2a0216054480c4921900102810038850040e5100010000303400303400811180d00c036040d50340b203a00c4080480103511145c1044904030750385035004880310b0580c5e480d003580442d0000d800740d0740e08100da885400100c3c05643d8140d030140c0382038540f04104001c21440300449140300425107186180f602c2d00b8040a55107800c06441c003403080400420444440e1201002d0301c4400c01d40442220a0b940c07800d9110001d01002d641c844415402c01c000102401c0c01180c404608123810f0b503c1c2c03460301e103064140d40010444026080104107460900040405d102841030b0064104daa0001544d035142003a19850912628507800709a414040f80ea0507940241c440312030309141900307013201259038504003c1214041340d0407181c0d0041c00c030422900d0034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 615627625 1250 615626375 615626377
    0xf13060e0f07140a050607020904031b06111209010204080c1c0512030405010b04061a0d0605040f0221010b0a080405031c09111e0409050114131b03053708 68
    0x8075405450140303030a80c035217003800280d105081002e900b1070002d034017080000f07108a20202d200012140c084100d081e2998940d0b0030303a6803e00061096140c040380081c4545400380185811483c1d901c002c40c03400785400d040949900a03100f5140c032a44403094030b10b0b4000205520503084c1980b180c140c0710041c001d600c0320001034009580607140345d0f00e00141c22007d03040c5031003040d054030340c1a400c0402c122809914900c140d40f01e06c240241803500c60000003066280c5000c0d00c007a10310321501c003584510314070040843c002034100c0325100325a00745004111002c2a84c0807582d03140703c14a04251560b482e41000e030314500c10490f95400e00c201c4140c414072114025800144624444d82646140c80d0200c0200000d980120039600e507103001d0641c6e010000e03e403640c800d05031940300d44008645d4001113450015140310803101011180e240240c001c0810181c0c01c0c40305050b4048100d5054003e0854079410b07642c070b0810f09070350444110b441100c100408802e108160150590441c182d0401c070500d0a4289 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 615628875 1250 615627625 615627659
    0x50307060c12050f010905061804030201021e0405090f040305041a0301090501080102090306010b090406080111210405060a0b010c080a0306140301091e170f040501080f13060e0f07 79
    0x1159010080003070b80860003554000c1030441150a4903034209500203006040103021150301518903140c075081001b0340c4030050310a502030780005840e241d11140d80d000a040d40003011140c03580c00c00003403005070707100c9104581001c0c07000b00d4035103d55118582500c16100b00d40010320100780d040003000f400b69880d00154103882c0700314070030320a503640c814126080c4e015222102c5d40c950040b100500092250601602e20202d0060001c584140c0e03500c02c440c00c491040741110390204000070703201c03460803a0107188420000204012080d0345007548416803250f002a0a000d00e081c0c43e0003004640c2ea101e450b52008441e00014102d030756641c4084081e00414051240c1c210005110241c201d042c0340610406e545c0540000201c516800709195403030603c0001c2d00d08840350121000301d90110581c010103041d28183d00403800d65a6804e060014091600003132054100901101c100044c00c0801c0410101c00369000201060359101040c045060010700e02c58040b4600c600f050000c5c1ca02400800b4400b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 615630125 1250 615628875 615628877
    0x20a0b0414010305042013020c03210f040809060f0d051806070f211e11030106050d0203070c05190b060603040c03030815100f020c0d1518050307060c 66
    0x41442075000103600f540d1044030050011624502038026011104114015610009040906582c0000510710490704144160501c0e0b0340045050b0911a4402c1d454010010201007503000c0b5240800c138102206200400c014480140451111410b8851000351a0400c0f01056182c0e00c0c0e4840251000c0100300444480501820072148403034001e4010030500d0140f4801e03640c220b08d031030303007050159240c02414882444a5107409004414060036118210242e426042c00f10a07200d07403c2517070740c1521140c800d0760225100800041102030f80060803a651000134400160705e95681001c151100c0d0213503240508140101e41c509800055001c64008040e84925150900b9882d07450620003a8041102e006192001680f004e00c0401d0040075050f41c0221030541004220500001182c1c0b8240c2001c0b079640441c0c4032542c10030b1082d030188940f0702d4900c3c0540d00d001d0940441d88906000707070740c040ca12260059540840307004082c0080c0007492200d402100320380da00e180910340000140300d148901c3c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 615631375 1250 615630125 615630149
    0x90204030f1a0c030c0f13030515090d050405120c3a23210310060e100810090908041403030a02070626150a080d0507080a030207020a0b04 61
    0x110400d046440b072034010014082868110307511000d08060650000640c4030707455805003c01214021884000c3c00071f10311178000707080310b8120903103903040c0c019020f00451269080368400c500400d5004e0151421264110750606c2039441c800c0c0c00c0e030b04100804d40c0b42c0f9003022440c040e14a138413202c944885800c60360002c805041c880811590802c01850740306c010001d107a9450030380000140201602c00b54a80e00c000d8405110141a81071444204403040048000740030040000719a0f9076100035000309010700f0880100624280050102030098900c1014005520081a0811011036801d0f000d4442030004000c982c0683c00c0a00310794009118201d58008550407046007030170044161892841c03140c005103181400c243c2c0641d200007651b01c4101c0900810b030780b058039400e40120360030b0060268801400d408103641c410b101c0280e245400c660010f50050414004955022003242d0955400c031307070f89644a080c41407048005c0d200350b41010b54450030b6540301040189007000244229207910301c5076 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 615632625 1250 615631375 615631403
    0x90906150406181a2d041506020a0c0603050405030702040e0c0307140405060406032d06020703030506010f050c2e0603051501090504390906030c0509040b0c0d0204090204030f 77
    0x4070b05d05d05403181c24221404030300f10201c00c81c2d000181c2111a440200045810300c03040e982032403110171540c444401a0b005104920901c10307001c001501034051458244100c0c83d00d07446640c1d40e8803601d40300a004554034042910b40d2a0280040819400002d040d51095580d4622808100c000350144070302c41d919180104100380703085c0c411102246d5001c2e2210300c1200780300311140754200c04401c846003080300121310304000030114401031030b40d503109031400922403c1c000b0006101e80002d00846051000c2001189186800001c1ea040040c0c3c2108400307a15800040340c40c102041c41440801c0c8560500501008003d40401d504c030040603ca8110174490b07a9401410054800685000c2e1040d81004004164494030045000513050f41000032a8510f002d544400d0b4100d0b013542c414040f05036210414410400031079149001403008860f102d02d0341c2001d8486a80301007000d0022191350100051000b0480e805405076002040000c000315201d540d2404c116450300064401200d0f020010040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 615633875 1250 615632625 615632629
    0x907020a20010804150b061b010c02280c180203011a1306050a0c0f060c03140609010618080f030315120a02010e0a0e040507030201020c090906150406181a 68
    0x200c1c6101005943c0c03800c50381c13299114041600307048000b5640c0251141d048501a840700402889010454000101c035040f6407000d40c0e084442c8081c1103021074000c03004219100100030180403075609070a0311248240e408c4d16003182c3c0300304c180d4440d051481c41c07481c00d43d0420046038081c3d41200d900f00d01e00d00509001d100d80d04001e00c5981ca640c0c420903023808050105ca413080000c4c000803030460410b441d2444180d240c1707402d00540f09030300301c501c20740740c40c14019240d9040c001e15a01c0024052180c01c6801c04600003088404140603803010000f03680c0006044400c0340303d091004040b8441510410140490f44544030307803080310601e80750307007401212540a081c481301c03000c40b0304c0180028100744002c503401100c40b980c01320f004c207074882648100851018660002a030186200300d006010680c038520019003030020240701d5511032009401004030040010410b01c0c1e10032540b43c600c1c411301e40c840000070020941030f0040030380002041c0ca18504400c1d00d0388001100b06848031400c483c6088801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 615635125 1250 615633875 615633923
    0x20304050f0706080c0d0e06131202070620010b06031518012d15020a05060703090c03030c02031f05040b010503061915081f06050910030305070302010b0907020a 71
    0x3c07a00c00064451320004245001d8100a48202c0300c0c11075001c21500344086425280c000241e0799043c400c0400c0100c2e8042000340121003020300902d001620480d4681580607042c0000e00700b000c070103c41d1411049000000a5006214000c801061326480b410650b1895410760788840c007a5020f1204211425a0f0340e200e060143d0403207010500b40a00c009403402c1040d4849840c00c4034212084c0010004106440d292000007070b0003246a005142d0307c11642045441d001018268005140c5040c0c10140410a1038000c0b030141c94142c10052101c00051006c41d1620042c009403d8100a07207000e05400e4040c9900107070f000d0343c010b45260303002c2d07626001050388811040d0b50f1302d620340e45403004020880649400450040040000d200100c42e42c4580b13650500c20b00580c1c18230415540d0700880701c0c4a029104e020081c040a0310594458944802c030341c019142070340005010701ca070120360403007054401d4202c803121103005060804681030000000e960b881404400f2280e0ba010b001000d0002e4030300003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 615636375 1250 615635125 615635129
    0x30b030712150e0a080d0e12040b1305040614010809070b071202060708160e0303040b0c0322050102030702010e04180c050418020d030507172805120a0f0e060109020304050f07 77
    0x14103641c50b1010701b01d600001441d4009400c0c0f264011007042410002c00440507100a08840b070b2460307940d50304004c0c800230070050360300030354855071400505008281e42206152b00d026401e08103034601e80c83d105a51460510180c0c44043d2a00b0000381c158208105185408a070800076000c44e0116281e40c4400d855918048034207130040301071100e400341c4661040320841c190080240980b4034254035088000e2a40d030000c00541d1321a40300003585454501d80581a503079403036190f450450140d0400f00003e48a01c50448064108640149070a42c5980c0d20303030010a18140740c01600410b14614941410003d900b40304092140c0d192991072802c400d06c1c1c042d00d80006a00a265641c1d4007220343d0107880d95000341109540d022209107400480b10002001040d00c00d11080e6250061340801442114016040e101031081000610410818090a10000740c01000d590b8010a44020f02000b50000700f26080c02e441051085100024107201e4070360003140030f2805481a6030841c0186215166518524 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 615637625 1250 615636375 615636383
    0x8071101050a080448051c330e010b010e060f0f090901060801032117090c060a09030c141003020c0c040c082a0a030b030712150e0a 58
    0x1400000700015a2a2101c00722801ca2480382e40845105c00701c20603000c800b4181034213003031205104149012089140035001090200c90780c0310907a05504450380c20484501b030080c40b5006903407040442c24110f6000711032403008945150f10034540304001e94050491b1081c131038055482d01c4030101055109072400c50040f0300140c0854138080f44a00641ca07103030700107412008096000c0c0301c003400ba5038444045034001d24140da50004d6550550610543e8121031000c04603103500e02d2295a6101c0b030b0485401401003810080654072650703990a10b90400c00303141c4119034030142c0012001000750300006583d081d070f40156045401c441e102c0030140d9801500d502d0b2942e01c60b84403a000b90f9418400e8005003500c0341c1c04d505a0700010513400c0498141c4401d5003810380801c0151040010300c02d115400d18284107042c145080105e43c0c030f52000c4040d0300c9440b451000305505c0e101d5140042e1020007110009044445a000c103954050904004c04c1215811403543e01f0304107544000384a0b0f0014074004002c0d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 615638875 1250 615637625 615637637
    0xb04030b04020f0a080a03090806040309050d0507030819120b1f12060315050702150601120603080f0a02070b0408070e06031e030307170417071e08071101050a 70
    0x440d1101425410010700481e0b0002c9200040307401c588829072440002e00f010700007081d50032841e18001e4841c1d0410b0b08841c2c80c6501c01400c01001ca9070050982003125019528064804c0c00d0f406c0c40790500486400141c100c44000a1700004640002d07802c01e039100350759a544206155032502007080c0c80c1c03208030440c0d01203ca00885a80b000342e160070721104c81210f050442c101c810102d002d40a4948560060300c00250340b0190031500004c5000e6650b11404a101425803003501c1d040d90820420003030070383c0341045070005c2c480c10b44101070ba1041015641050b4615190415118641e200381c0c0b2162258006001c0d03200d00240c00a0f030102643c05803090700c00941105030900e403100f240040010155541880b880308101d40f60950040c0c000000c2d0b81c80c10140d13503a80390200000c0c01c1d510140140802d200544420040454005640e1100d400c1c90f821b40c1c80e0361140c1da4204070109040343d0600041d41082c2210071810046001c1c01440428412081524001c0624006440600480d00c881c404541 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 615640125 1250 615638875 615638879
    0x120c0705032a01050d0c08070f0309020d030509030a0602031302010908070b030109150e04050a2001020c04090602070b0910060906050105031503010f0f020903010510241b05250b04 79
    0x901442c0e85810010302d421070902c40000413000c10317030b00c56550900110301000c0a10164650090280807590290f040034001007209502003580b1300003982003d01004800b050a07103540c0d40c2403041300c0c80c50350801070a5440e414103d0304240e0201528004a01056000d200014051000304000084075410141641180c3c6045042c1004e000d0800d450243c070b4046110120b503a408203a51503004501400040600254901e450b08110907001d91240c02c9100e00d04403029941e81c00680b845002c881a1400f2841d604a45041c1c00a03000b50348000340203034038650801110800001c1e0b80504110513040622085a40fa405501140c040b80101e03400150104002103800902c00900b0b13102d84c5008c0d000141c0c6011100c010412924440c031070340d44c107a0b0002200000f5140c00d014042e000040380840094051a001c3e411121903241d0610300210780508000114450080100c8a10959442e10a240d200d07c03519166448030f21860001c540b2541c505507502d070904049007190300b540c1ca600a12443c0074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 615641375 1250 615640125 615640183
    0x30b03030d050919060c0806010519030207020d02090405100c05180d1b0b091212040303120e102703020607031e020406020a02090c0313080912120c070503 68
    0x200700284843d866100c0d2400301d003940400c00e41140310481c001d0030005002c12070f401e0010000c24002d026039040140134040c4101010b803800d841a0b0149044c140180e641500340b000c01c01003a585030b00a03501095040808c0309100012030071001d0141c2c0030f00300b0000714a4114003a11680544015158182c075240b940e86001c0c01c001e404800300d180101842540034110f0311444000510b02c0c0c00c41c0c0903154000c1400b800c6810143d10500c203148078000644004032039048d002d0068001e520014013044606150020080380f543c1c481a6107444143c10b035622450041110b001500240c0c0c1c03d0250201000c02080d140447c40041c035100c1a072503070107040036407a191000c0703028082e4180b4850b141200c007402e80c8070325566840248000c04a60300900291507480c010440c20207001000315204043c1081081991000d52400d098003d40c0210100c0c0c44410b040082010500091402840f81c814210a10341c00386000c80542094011785003200e01840e02c0d0010b040d00c0e4030b8410280f100e2142520090304500c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 615642625 1250 615641375 615641381
    0x20d171027060303030b011407210c080c0102090f0306040510020a091e05010f142505030d140907050102062208031008060a0e0a02010c230f010c030b03030d 69
    0x1001c24001c400365001e002016420840b0100da1003200400c4c0c2d900000032440d41c0143c0d0804130350f00511807090a04100d03031901c42643c110382c11107086801e142c0b40486130560046404940058001320030a840348400d0f407a150003907001c03c000314403c0d4569094000c507440d000903668030a590050241c8035256091075032001940000e4003003c213010040c07401091541c44800c041d40d4403500e5040d045400c41c5004005403a440030351503080200080d0f8102d481d07502c0ea40500300c43c0e41030328105c0c100b0115854202c1007400b0008080c0024038900001561050007440c903000380074030035020b0103031107420f403580c01700240d030380d04248a01d602580085000828542110700081101d104e9080c1220084072140d0702c1074580d600481e0a00b0240c0c240000034800c1000c1080b010741d018641005c10090540e621086581e1f402e85000300a04002e4181040b00410032000c42c44030340400c1c2540000010121303503140326101c1c60316404a4906620307080301c4010042c4640526641202d000e40598500444ad02000001e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 615643875 1250 615642625 615642659
    0x10030b0a09020a030603020f0a0602060c0a050d0c080a0c0e010903021c0b04030503040516050a180f1a090912030105060c0312040b040204050f010b180307080706020d1710 75
    0x1200d1080030002803000303040c0c0000c10a4421a43d8001191802c620420940702ea20b04c0500b0f00400c0c20210a001081d000200c19421503146803c4503121010b228040710184600ca180d40e01060030400d0304001d1380e1704100d074140106c199002c1070141081040c02200c650f4040c04441d80000c10300141000581008100c0f84d84142e540700c10529080b40507203401030040002d13a0308a0001703000004110a1000520040c1c00c444c14506540580d40d01c6c100c0010340d000c00c9401005003030000c240c1410348120580e4480e103000e160f012400c1c054550690203e095400507054070a0007181020300068200d240801c20358508421000d105042d03034204018050950041c00d5203450342e1008000c646044184000e840e849107106031080012480c0910502c41a20030190100e016902103000500000c02650305441418501801707a0504000c00d000180c030b0a400c560118101d8001c012022036483c0e4040780010f03100b03196440d0300107142c2203e035111500301011104c540301c010001c401441207460719400c03094 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 615645125 1250 615643875 615643879
    0x3010501030c051608360f0105091f02010f150b0c0a0f1b0e04050c010f090b030f1806040809040902131a0108060f1f170406060806060402040510030b 66
    0x41000f01020644c4540ca80000050b00c050b940801c48512022110034560042d00c01c0b021050100c102d0b031441e1104004d100c1502903c00e00001c007560701c56910413020745a0711140140180548020b18100507418001152100010b508210360011840c1880c094060206144441004064500501c2154507046441601264000c80000070041040c0b0003076402c0d20360081c2000000200c1e80a003802c401a042d51083c0c51558252041001052000c00c42880d050021700b800c008412495000f00c807246a00d03080034400c1040030081c002d80c4080d0b40003061048000203250010700021080860355450122342c010300402c020000130030740b403c0540040411910140011142d0212213041070b040c0c54000d082e00d82d44c400210801c18182da4803510303041c0c0018042e50007150140e81800401c440d15641e054012415100c940c0380c55491303105010310403900341c2125004909040510f00300000d0181403244005070300c01c0102080f068600b81c4210f4088075030041640c40d54540380702c0e00341c000d441e07134002c2d2035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 615646375 1250 615645125 615645127
    0x12032004120b09161815080303190e07080303151c0f1104020408010902100e061b0a020d0f05010605090112031b171201090506061b0f010c110606030105090303010501030c05 76
    0x185200c844014101c25001c0300e809130700c1078205004403220040d01d103210340c4201d45d042001c084080701710303900468500d0024002204ad404800054000030070035002c07034031406c00b000509040200c0510b0169a001c401c00e42020221000c03c0710403200d00200d81442482010840006144540700c3c92036284100120010b00c10f2840002d0202d03005540141c01c0ca0751140f108404618152003680f0096446080c40310720f1551540c0400c110b0b01070100101c03d80d074034541000c07031508803c0095100c4a0740c014940e07641d00d02a450604001c008100b4111015070901c034000c5400e103441c2080d10305960b03040015000b4114142c03000c0300c9001250981c408a546801d82d84404580d048044006903945000c28564130f554a00e07040b221603105034803c1c07155502d00004c1c081c083d511001101d05c411420380d242c0744403110b0b4009803400c0c560705802e0a4290761030310391600c12042e002085201440003560036148669124401c1c1821788404907030000d0150010001440b080d0b0003580210700f102445d140071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 615647482 1107 615646375 615646393
    0x3140114011203090801091a070c0803061e09040503030106020d0221030603031b010f0c021506011b05030c0c0f010f17040f12032004120b09 62
    0x1030040d4000d46110030b60038140705190240c094403d120003088410080d280007500700078148040302d04104a180001c2c940780c000c460b4602c0d002d030050700301861641c4031800c1000038107200805131943e894809090310340b0303142e40004510a40c400c0d00110395035418003130040e141c0710750f02403650115484403076200c2c0300d44905442006581d0100120503200c0c1c543d00c00107400d40c02558480b10080159100007014114150011440300b900c080080040340002d54003281c43e0781181d110001700748409804154654400e5868642050044049206601c3d650740c99608540c0449020501544a251030a103549412001c0108001090034218180e9070348400181601c41e038640f0110340c5221940001b02807100780f50403600e9044d840310445800031314032880075009042e003000307240210054480b04900c142585045500f50741c402d09010401e1000d0f03503100d40205a00801c0501d132401244a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 615467625 615647482 := by
  have h0 := BRFrame.cov_init 615467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 615467625 ≤ n) (h2 : n < 615647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
