-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0775
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:42:34.589285+00:00
-- url     : https://prove2.me/submissions/23a1b614-b9a4-4a95-833c-296b8a02203e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 139208633 ≤ n < 139388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 139209883 1250 139208633 139208651
    0x7090b030c0a0303030c09120308011a0d05010306061802131401050c010e071502010e120310030507030f060b01140d0f020910021b01020307020109090c21020901020606180a0519 78
    0x140c3c02c080c905049641d01e4000c010346501c865020508c51283c05800940c44a006221303642200c001c110315039180302d000c0c3c0d04004000301000141c4109070400c5804544901c4200301e1041031400322900221950410b6080c0b40d100b488540031b22a0611510345540b03990f00344c0400303590003a01101c0c240604100280b1100001500303469851181e48100e00c1c220250001d08000148103101e580340114980020340540d55041c40c1c5080d441c0c2002e8248450106503210005c00250704204240040d4481d0701d584101d80b4170340c01c0550803030700020415414010008040c180400d4007034101d9030300d08c0220b500080c01c0d825218103070000f4018052840c0d000f001c80e0905880060f0009508120000008440380700e034000d2400480e1030b40904000240801e41d100000e00000145402c10f111410480c5806408158680b005580701c1e103401041c3e0505584c005140d00d0a035038180003203039001d0f8040e80c14a14002403d02e2107280c5141c018444030700c8540e1080420002c0d100208104000d12a00341d09008200e9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 139211133 1250 139209883 139209887
    0x90603132307030308070c11041505060a0917010501062a0b0c1218070b0903030c070f0e0c0a140903011e060801060510020705011103070813090b01020c0307090b030c0a0303 76
    0x3d000c250b0100d10700c080003d141c02d12074030b41c0408542e07014880081028031001844040c02d445840c0029020074020046000e0b01c6220140162001342e0b540e49905918003c0d00b6042c8440c01241026035904000050000c19040702d000844c00f81c900a40b0b1003414201c40e080030504609010007030985031030000344518010002d005d40400724038035074002981e49038070003a42080401103220b419140c00145e001c12003401c0c1c04025010000c0003809603490412407414290401c55103030410000421143c000340b10102d85188615404284861040c0c070740202141d001d040c0001d0312407154901c440005a505c082d0300e00f17411170003d02160641050646036581e54600160009008108056280080015641c50040061924580d454001e00343e01410071004544002c030111030315a040c8010071000001604400051200c141c002142001990400b0304007030580f11080d68041c1190310459800391207940c0070480d88111045008000754800300315000c03038148001e988455600074500d1400206040e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 139212383 1250 139211133 139211143
    0x307030b0108070c03022d0d0809070605030f01030f0f15050603010c020703020904023309010f1706060322080903010c05040b0a050a0306080d0e090c0906031323 71
    0x180302600e0705a500d558603d02100c644011000c0034005a001e2103400054225000700c4c00c103252244403020304402441070425103440c1c113612400300003400c0700b0104039034688180602009003c061030f08518500303060803440341246042c08041c2640b1040c00c40041003114844100500981c0302005c3e070360922001c40c91500410382168518020b50802c0ba40c0313680244080b842e40256540140342ca80320351150f03024041140c070800d0800c80340c1950300301d01e031003020900440001c07258110000c180e521b06043c000180410f80c0d01021720140584070100d88100c407039942c1c1140d03100005488007500d076910241c201c04c030084a065510b003070040f0001c6003000c1c40f55180003461a02c1084c1d000f4003540b60700e4901202c05208603c6505d00c04d50081c480c1030340321885040117011000d01e51802140c4a504d079500b0b41d0810098103001c4001c1881480c0f5604a4100500d1141e80b145840102c03600380041c00c00441c0c03c0d880010301e442020200049038008010f00c1500100d691000c04005482041c04078420990355 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 139213633 1250 139212383 139212401
    0x90c05010e0f06070f02010315080a02030111180f060d02040b040807080c060a03050403210c020705150403061806050c0309060c31030605070f1805031c0311030703 72
    0x908040c0540340581044600b04640c40c1001e00001e182030403a480700d01294428010880c101a112650f520121031998000c5000d0482107001d0a117003503192040508480c6921030740044102c06010386441d210200c5060318050400782c0e05003814030341e080000303445841a00004100203101013800726210341032001400c20340701401d00300c54003a5240c104d000e030303501140c448450780000e0800c8007142051003a000706400511070304103849400a900c0c01c001103441c00806810031799540d901c103881071a50400600006120550792220f40c1d01d14290000c02511580c003014184a4036042001c15a6190381e404151031070700320781c0400c03481c1891040c082c911b600a4a41034840e100b03150128131100c089404407070b40c42844415002da6810100184180381c01c1c1d0404201007041c1818001001c142c4901600744139a01c00d5940c0c035204496103002502489555640c80c0703012114603010300c1b040c4c0340004d406c100c180d44401341c50724811844004902034120b084c5a4042040040b09208400d83c068003e01c0d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 139214883 1250 139213633 139213637
    0x91003080f1b01050105030c0d05010908030a05071205041e0c0b04080a1202030405060418020d140601090602030301120602030903040801020f0403150506130c1103070b090f1f0b010e04090c0501 85
    0x80c030503401c40e2260981d04203021b0940d00d50071442000400385042007e09440d14864400441c032006c0588070485560030032a1030794401c45d150410050804da00520012102d1300081040007141090f0b110980554415150059020065901402480001c11800e00281034554903160358075203450019485404d498011201d400820351464521030011099074147d0300003171712443c182440c05100d000c01411003209020110b03400c005c031052102060290030040f403511000043c01e4145100010321804107503201c1c20464000f41f0044c0594010091030203040c41d0015400350316a11380d0b4102904502c0703658464a065880001c105454120120140007105c2c0201c0200c14034208294400095505c111a01c0b03074001c1c103117100c90f078a0711020743c0008501c920b00d140c1111522400d50340b0030f107154070921080d9a0042600c0070440100e404010804050828401600e040812004c07001048201d40040c0303030140b40c40749a410901d0344280d183e036075000001001409600f8250030000d030142141c3c0580e0380 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 139216133 1250 139214883 139214917
    0x408090907020f030703030b041b030504020306060307030b0f150a03030c0501050c0a0c02011110060f0f08030702030a0308070c02040212070e10020c06090d0206040f080d02070e06091003080f 84
    0x72080c00410b0050b10324524034003031407810303d050780c6c00c50050407030902103588555150100e100d8420955015030910340ca80d1000101400d040c01050b00d000001400e440c4282e0042009000241501c010650483c1c4074105108440e1030388400c80205540040405400c030740039000001c107065202441c0d60301c8038066402000b00313031651220241e00c0d21a440324200428507440c0e03142c2c019441810341d00c14110007201601d4200d5003d611040503281c071540501e40c003102e24481440040320780c0383c6001c01020b20341e00540c0b4040d0345174003081d180d481103140a4140145900003800702c0d0700441c210700030154014411581c0302c1401e01110a503140c05c2d9041c0002503540003902100e803c002c8411040382109800500242c03c103403040051039030080c0350144e08041841348801c0140c980c2e20240c03004e0540d03c0300848906040090b094540342200d04044215882200200611103800c0740013034200c642655000380b1391b40c1e22010406508007075880240401000515007000c0a00c07040580104039900d41814 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 139217383 1250 139216133 139216141
    0x30d1806031802010c0501060e0a0608010506330415080a15030308011710020d0207031205010b0711030c030a2109080c09040f0b010305010624080c03150904080909 72
    0xc1c12142103000380e1602a82440c0840050343c0207041480d004ca210f20008a020780d212141c030301d03400d0025550042541e48070201408035600a0151592055007552900040111580c1c00d42c0e44046c2201c42640e2188041d042c60594040d00d4121030103021410a00c42408051400080c811601140c2104041e45813034080d52490725840152800c0702d07010b40e160505030f402c4c4400030790840c0304034407840c0442c0b06242e400405c0356603d0015111648003280300607182e5629007000380c00306250ba000781540b0b0b45408010300007000041c0a9550907500000000c1c01003011801103483d01001e1441c01d685403150044030002c22200c203071104a0300c2d00305c1201c1000c01810100c2030314200454000c07020607400c00d050800e1541010120302e98000c0c000c0802100340402070312919014502070f0001c0d40e29035111b0400780444481c4560014001400304e201001d4401811001801d01e50064261a01c00b040000403414200945100016440d001400c6018504240c81d0848a60f40181503250181820100003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 139218633 1250 139217383 139217387
    0x100b07030f03020a090e0c040e0708040512070204090f0605070908010e0a0f29011e120b0403050d020c010b0301050a0e0a080d0609060602010207020a1a04061805030d1806 75
    0x149610a600d9250507200400ca1001500a9000f10b5400350402a80c00000198100c2c500742e154081c8055984081e501c81c2045034400c4c0c01c100003810b83c0140400d200600000510014585040800381e1003c1c5481e4001840010060011400e000d0142d491584181082c00304d03691100b4061040d0391164036417180e039040c0080c26245008440016078110303c0038000414030103403103040898030a44440c075040f490100d40904002000c680c0c500c0c028240c0006100b802c0c0c0c4144c0c80541c114018007892542da14007030100080c00c01a00005121140c014086000c050062054480b0b020020205549a6020700c600c2c0e07000b8121028410302c01d608040101e241c0c00507902c00c03044103002480243c107054001e91500c410ba40c1c0003900b0f9210043ea01c1f5000140c0300120302c9901c01415683c1c1c009a40c0340e545004100403046035400c0441c03001c9031826001c0110030064100e904580007800c090071084038002d4806c4406842e07901040c2c2500440311501d2189a002a91800c2c20420960102110380c80301e40c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 139219883 1250 139218633 139218637
    0xb160320150a0605010e0910030b0702030301090c0207031709040f29120312070507060f05011d0106120b0102100207032309010503060609030c040c020c01020d110a060c09030605040308100b 83
    0x240303400300e004041b000761203040a80c40d039680200c1c14880c1503c25581c981e50b643c0544003c407070420058102100602000c0c11a0082d803000c0c64a42c401444c569003180c40341d21080502445103602e0180004120100c4d40303c2e50400c1b0400a5140303400c0151007413003000c0080c0a40120403200d10002c0d14010f83d003192400c2c00c0b0301da10101000c0b00079130a240741120010400c0030090042c4040c814180102c80004109004110301480f001304041030b2549403014462070805000207030305003c52450f0040c0038041d070026190814214585000c51080440d0300141d040c4403000c820780e440540002600300038540c000c040c000364800751000c0c50041000707000741c1c0c4a4a00402c022540003075800c00100d01d4510700b24000e0140844001c0907280e050703038010002030480709101114400340c1c01c880361840c940e60301032280751561503071400c010111050500e05191103001071000200700359901d81104030b1451088480c46c0103507902c0b420402c11801e06040241c50b80302d0841d4800006900c001b07021421501d1401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 139221133 1250 139219883 139219889
    0x3050706021e0d08060105042115020702010c030f0e03070e070801051912080903060a0605011404030c1703070b0f0a15030f0f060e121209070b160320150a06 69
    0x2c00b800012103400000c90b220b060103401d043c1013040a20002c00c68492980f0828010010303032502400030091454602d03204214405103c00e00d0744107020101c0035076000100c0305130f0f41c0d81c0f6280a03c0d103026412026124070040900da02e80600c12503c020480c9400c3d10192409480f9586840c8150382ea10740070400d404544a40c0c805004c11000c1c001c015540300a004402643c0c42840c40508041030840401c1c0390002c1180c0200f4801d8590908010a5030011890f00e51078000032201841c050031511061a00c1c84a0b10606103820340540c1d848000c41c07010710607600c1c00c691141c22b06050342040f1501002140041d03c181c18203929009400b440501140f0f007040460380d1003401840301c000542c90b403500038988004d0958a49448801c001c0301050180045503010781310f00b1003240c844e1804600036150318001491140982d1041c90b0520401004001b034940481c03c01d003042014041a14044440d03201200c00081106c10311002428010004200c4605000b0503900e00101680c80070510000d076110342c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 139222383 1250 139221133 139221193
    0xa03020c0a080a021f0302091e010e010815130f091a07050307121d060903070317070c0210090911030103050609060f0604091106030708040b011409220203070305070602 74
    0x70390b01205c5100010702c00c1048980d07402c0040c02d2664120220f44441c806001c0d02130b54240545010400d5078220359124130440080c80c0142035860710701c400b0a03a02195086c2c861080c60f0001c0c0c00182f00206402000300c0d48010790b03061055030464030f03080d2004a4401d0321500c05450f8400061115071041013982d208107400d96503c0c070b0060101c040300c002000402400c910320702500345100c407040c0040003072074003506603e00290750b00e03545420700070141e500329a84940240e03010ba0510481560055448482680445010182100684e02500c1c0d1181a0744440c83d907504140702c6a10550701c060155040304c0c0100c9c280c0d52907940340b45020381c0350700c42200c2d0140000c2e0900082461410b15a200540c1c0500c103046506540014100240a03a0000c80d209800103983c401003000700000c0d84482070052100e542c0f0051000c43c000002030910400070001c292a4554011640041c4240701d240050b894002e401e90701c1d007a40360b007402c1d5125100c0d806a00c0161084414031026100903042d808a090307114 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 139223633 1250 139222383 139222399
    0x601081501060806300f0106080a0206090d060903030b04050c0705060103110102070306050a050403020f060108031e0d020a030b041d0a0f210509030d030203061c020307080a03020c0a080a02 83
    0x180582c0c034650041d04030f41d04808004401c021503514080c1701220004143c800001c2281003030205031410502c40340300c0350700e64104501009044400240b288049604440d403e0310760410300085000b65003e89005402241458000024507800d50b028540c504015141407200e60340d115080300c1b00f441603d0b030080c460b40c8014010000f08410840800400700144190361001d0f03a0ba469180a9503070969511480984e5a401d0004140e01004055080038a40340940300da03602d40302c12162030740a025810f42c102a04a6101200c0010540c121001d040c10383c2011925129007000c01401000044845400b851400d20500c004034a1f1101d440442c115500c0105502c10655885041c5d6182c607020803150b000d2801862024072020901100d0116110717aa15900c1e5403282c020149040c05181c0743c441458030410a0000359150450440c50101d8448442036180310148040713464501903030f00005290141341c00440c03c056000c1112007200c0c504481035030000b03841746130751a10b4211400000354401d882e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 139224883 1250 139223633 139223639
    0x312030f0b06071b09050714030402151c0b220e0a020301090b07170c07060e070b0406030b030705030304052b080a08190516050705101d0601081501 65
    0x800d03001000005402800400d0354545007020840507040b42c4801c4442c01c4255500c2c1c1d040c60744d00072002e0014121040306000b00e0034440030140801c0d101d0243d285070b0f2000000050199102c40c4500c004100e81802d195039a6000c1c0c440e4048000d0b00f504500000300d05001100885150915030070018011200c4070a008841507500c1c0001854013600001103801488079144c09030340d0070b1141044c058000c0074580c110b490501c50040c00500e03c0c401155181820390b0901000c91030000680c1c050711b9000c840018004610b4606c28a00b00c503503030002e45242c01c000307030228074154140c01c0840b181c1001d904684d521034842003015124040d40c01141d030000c0b0b10700d1a6185d0151514240e0852400518040307001e980c2540310006150700241e40000400c0400042c007480110400c0100c9024034101c404003e1410127440c014213000e0900e01d510108080401d0030000d0180600190003403010140040001c50013008080091030002a0020003d005005c00040c0201002ca22a00040c0f1500e100e1842c40c0e003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 139226133 1250 139224883 139224887
    0x618030c12030e040f0905060c25031e09091808030a020f040b072001020d020c01081806090a0218010303080a090314030a0603051c08010e0601020c031b0f04060312 72
    0x10001d01c0a40c1089481207a40f8420340f507920604034281800c03000464018500d042252409002402c140d0741c040702000600041e40780341a0250001190741c51000d0002c4090808540039480240c100c140201c0c3c000842c0b0f1010342060488003180d14401c4244903050054800e149403414240c00a0407001c800c100003120741c0c0d100c0e4020b15610203001515030421b6110301125070150480e450481d040f4016008101c04c0c4160b2003828803400000744014503007142c082d040251500143c04600d03060003400004551541c10380703074104004003c40003c4034101e00e0000212a9035919034901a800b900180c00c400c1e072080950011141629015200d6607441d88560803254000d09981307205a040081151441410400440045010741c420030000b0034081d0450610324280b8100d014284401c0702c20340c101c4c1c5292504440303807e04403603600184041e10b582d6440145e080c08040e40b445a0b05005032441e54505a80c01100c000c5803100030f03901c00b001e1024000c18001221380e5400050454030791181400030841c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 139227383 1250 139226133 139226159
    0x1213090c0201090f050d12020f0909073c090803030c0706090206030c0309070501020c010e04050603010e06070c0302060106031503080306010c0b10031e1a04030e0a030b010618030c 79
    0x5031510000620340566254080320805404080703865810000040e04c4043d40547c2520000c1d40201045282c03034800c1800e5025449400242801041070800140c00c0321701408103604000e405810b40e000f10b0b500300c4103000400050789000c10b400c038294200180c0c0c4510490269003981d0f0030800039480c0d40c03551580700b40550403001046584030f0302c2e10804070068960b1b9000d90f000d04803c0c43c0540d102e0402c1e040b52803d00c0604d4004074110350101507184e2031681d101406115a0000b40c45c000307070039203542c408280903145009034100d40380715220034030506a602840c1d021010380030f41d090741c6580e40c0b80d403400c42c02d9500c0d4805030108080341120520220b00048011a04207105041100c620807217503840c54454601100d04840d043c2c070009040060048000d03a8282400d00c5040254900155a9820b601c07845d01090480f03802c80300e400002c041601810b0f0005420070010041d070764050390b80c507101c4600c4500b4026000018220102211481403021801003030326440503c2601c164200341d2a10308403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 139228633 1250 139227383 139227401
    0x20a0b09030f1603120509031c1d0312010f050312180306090d02010c081b16060203190c080601020a12180f08011104030b04020628080108121309 64
    0x5000800c2956240b0390504014054500781c102e1400408400307007805032400807401e17401246103003440100b00c07500e1004400c13662240010844030b0203007844100b03078a008010b0340601d00d030540b00e040c1d03c02c15651000400760082604c0c210b80c0400f0f581c5c82d2032104410125506c1101c0d0182e10005801e100c400380c44029000c50400001c190741201d41500002e0314000040d40c00c080641c01140c0840c1c0350343e80c280075480990340305003070503441410950718100310030400c900d542010715408500c582114100344505003e407504100259201d0804560300d044d400390300075115000502c3c00b0a01880c40d03025422107031140303405801a01d000c140d20744030060b50b141c40001308420000001c018810344061070410f40b02800c588045c8551442c10300c480c2608680a140c1611a808414407080001400304000507900c280d042d6281d42e00da44910b0f019801e64540e0295004580d010401580d028507480b01456040720400c0080b00c5001c100f01440b00e0342071242543e40f064461081c3c8041c0207421340c0303820001300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 139229883 1250 139228633 139228651
    0x902091c1707110d0b190c141803070b0c0105010909030507060b011b080715020913020f0421050607050f2b050f0f01060509060d150305010203090a050609030a020a0b 73
    0x1070f20382c2e80c00004038000701c0c1070307800c542c000741160a200800060074421081c030000300d24100062000a040a0031a00e4106098503d000e00065211b4030042c000510b44224580a4211a18a52925034508043d0062034503150558038100002a81c0e5406000c1c1590503505a01d419290540329120240a04081c4000605001011071605919400d8820242049009424054030740100340390407a107404890760300c1002c1600500c00703000300f41da4051399807640c41000000180d8440000c0d103209101d0149910070070103040c80e404038018201904d14400c61442c0715038140d5400d0b640742c450680c0c01d4052490050300e115000e010001c00c9140135000420604002c0300d00d4140c0c45501c81c0c0500030f8501c03c40703200010318104410b01601c54903204010b40946014201542001211004580940580e41c0d11769a49502c40f84004c0d94071141800c03a101464200c030080d075991a0054041d07a07900034443c4100c40300d10880e80001c0c0814008401d560a040b81a409401070303025139100c80c241100c0c00340c40c0b400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 139231133 1250 139229883 139229903
    0x41208040f170a090e0105010e131104090204241b110904050c030607170a05061c030e0118080c0f120a03020105100602010e0c1002010212010902091c1707 68
    0x804185040c4070441481d900d54801e0390b0780c40f0030b4a0300602494450340711018581c80c40c00140301aa81040c00402680c600751500b00d00050401c500202070300f030141110340c4401c00002d010a0b01c91140d0000c0040e01c480c0700782410420b10a00c48100034107150410b510000300314800c0320010403034401c10003509a0080c000c41c2c4002a4030710020341c1c1f01105941c00c445a5004494a035118103007800641e13803100440c1020008008a1103507041c4000740200942c01c0a0740c0c48000a040340c0c0c9044009010242502031500401d41524000c0c0a102203403001901080c520305685805e4403200d4801819141c0e40c401500046550a00380620f07021220310180e4080a0b100c0d000c001c0807410024040040d010342d00102e01801c06541e0b1022900003174014208690400c0700c0424629400140004000d40586600d22480054007040740280140d0145159511189000140300700094028101942003200c9124010b80101da4031207045050000c024a280048000010300302900305c00b41400b82e0140480c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 139232383 1250 139231133 139231163
    0xb01140d03031d060f04110108040503090d14030c0a0b010902090f0904050c151809060303070b1005060a02060901060b0a1d010915080f0603070812030606190c0303110304120804 78
    0x43c01c04a08682c0d409151691740d00b0402030000074205041e1300b01080c20250300504140e00c030103841e44103100c103c1d409a084003100d1400c0000880c16491003035900000e0f1703500c40d40c04140c0c4588440343c000c0140c600000070030020071080058800c50390320f41e00c01000d0941c113135010340500c04008801442669280a100303240700c0380e900c070751342004000c0688849599582a24000c0d20001c2d9110361819801131404204001c032580313000044419041d00a070007092169110051180d0a049582005422180c085540304500b80c0001e00345014006440c000e010880d182c41d0740800500910500c9400102c0c28800050307983c0c1c180d01e1140d092881071406240c000d880e40c1403103801d0f000c500710031000522030404101b03030703400d008441a0b04204102e02512185180c420119170350183c00b880c2080503440000815102ea0702d000c216641c0e00d0b1101e1482320650a081005000030340b100300705401090a0882076a03000190340100c070321030ba5100b045c0034000e40408e00226642d41000b0030444129841001b40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 139233633 1250 139232383 139232441
    0x3020d0501020d2d020f0723030a09060201060b120106080a06030c0b0a020139031e0e070801050f07121404120e0303071211280b01140d0303 62
    0x14818001e078000300c2540014101d40c059044c3d03402038481d00041403040c00411403450300442202c8502c0d80115a90095443c00003200d098408042d032035040c00d05c000500284219002a90303841100c101e030b0020414241c1c1c86608200612600d04940e0724400e400006124007405003050340d4200350003c000084c0203860f541c510415440f03540141c48038003004140c06c013040350b09029110140e8130000404503103e404074041c2d545807900301e404400d14001c55480c3e401d11780c4650300080a600500164120071150354124000804000c0405c0c9400e010320800402d440c00d0501030540599044500140b82d40d8070380c1009c0301d00c00103010b40c2c00450342c1c035100166820005007a44130f0203180030f408000300990000784040d001c4058455401d00980080c41200e0205246041c03000c03c00d81e241c1095408612003010550408001c010b8040e84038429134003040e241d2407403140c03110b0f24500c69104400141d0321505941c0e8511720300c08100341c2c41440c0403d00400288203400c4040400d0711301e07001480200899003a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 139234883 1250 139233633 139233641
    0x6110a02280e0103060e0309010207051c02040219170f0402040903200c090601020a08041a04050a0f080c01052d13090f0b010c02010206070e06070f060b030f01060f03020d0501020d 79
    0x2e84201c0b88408014424420103124600b5008002401076190100400010391542224801e042c0f24803403031200803070001c2401c642c0c000e605600910841d074400309130b440114601c1d40662200005400b26014a42c50704107110407900804035018041c1d8640e0340d60703007004040d00603400100c08005001c9059000b00c1459600068010700d210050002c205402d014000d101400405060441d0300c640e07501d10228030801c4c22102910f540c540c2c0d42c0c010141c4500c48001920950340042e03000309481e80c0010310385003060085001d84005400b980c9405800340011146401900d5440d003455040c06400200303218a1a01d900b80c1c40030b40304500e82000c61110280c2115282c6503c003420b03040c0c0302d40c0070014404ac03602c6844071046090906130050012900006d6650b4402001c450520402e80756a03000c545d210304c2603a040c95449075088040012502d0708401400500d40014000d10401071120541d0106001d85000d540115620001151540e020801020030000302075400d03550812032001016000c1c05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 139236133 1250 139234883 139234889
    0x50a03030c120302071e11010206060604030615080715030b01080c0319140a0b0a05060408030405010f020a0b0703230c0a030b0105120f0402030607030e1009051005071806110a0228 79
    0x103ca046c483d815401c00c80f0111b10305c1a801c9045400c1a01003001c1070742c0d030303000b41c4007540d40100300082c1c2d03d80d10074600308000c8029081604548998007000442000c0000d403007400c15034030707076081c04058458001034441c60307000e454490404105100003406180b9422500b460004030000208003030450784842c11054400703880a81030319031145c0b0106400c2c281403000b02c00515054400910f450315005440340c590083d80502c038104007851100d4081c042c401c00185a02c2600552007602600380000041c006128103110159010720b0041d819403828000c00501e031040302c0d5411041d280c20b00100c0c0440007401c1c500340850501400b4028080c0600d0036496032032082c0da031100c400d16a81000c1c0109442c041004080000701420988680308011001c12100901120100c022407003544030b140290a00d50701d101a01c4084d841c0404100c025540300c0296055403010020318a03c01d81c03904411103170000c110440ca03040d0380c04050101c0060406201100e08000c44600407554400080410b55000f4144c1e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 139237383 1250 139236133 139236173
    0x1707090e03340516080a02061207020a060e01060e0601050702030c061605100f050c0310060509120105070f0f020a0804140a0e07020102090102012d0504110402041806050a03030c12030207 82
    0x2a81d0031244c050803d054000b41407990000c200e0b211082d400602c0c0d5228201480d200f50014001140645000f00003510889900503c14801614816066402003c082c85042d0030240c9480111700c0701d5000c0c0c4101c030702c0d054018010b00001d420910620405038840c4603403008545444124802080e01880114069980141c010400e484818847c5003968009814449040410420b001c064104800050110f070550304200c4d03121030b00580000d0792000607406048140d404d190801c507000f50320000f031048002036a140c890120310001c0b412039650303501c80c00041981800b0401840003107094012040440e8004010400880e29441c2a098508003a104000542e4001c5130505080d83c086c040c408900ba0b0303002c1e00c810010405440900c40041c88030039005565510300101c1e0601564a080103c7c2920292065584555810300c01d000b680c162074000d11041e00d030440200d480d180c407079044c80850ba01955091b002140e107441d05c90742d48076080700310414541d0030024072002560941140100c46000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 139238633 1250 139237383 139237393
    0x1a070b19020f070203060c090604030f0302030d020a08101e0902030c09030a051005130b041e1e031106090607110a0501090b0405010b0a1a130b041707090e033405 71
    0x784107052500b42c020701741100e42403051146488d541c84d0340003540c00300c4e81c00120601d48420b007414241e042d88911844024075500010b1010300c4a9008000a0b005001c810409152580d480c00550301e2a58680b11440040035865000c1061000d140c01440c2c00900011010b8070f00a640d8002034500145401c00301c3d650340041d030900c060385c1118031030650303c0704610420100b82e18160340c904000d03c0300100300802c0b660700e007513201e0700c10400c3c445000c5c0000d42c80400c0c160040e400c2c071040e90340c0000100301140000d004d500b024040c0e050210b040c500442882c0020300507a201e030b420550b078180a005c1042d003184038100f0ba00300410310900500b5081801180032541504182c10500d007542c2d25105c03143d01549804100708182d01d510070402044000c0e0718041510358040288404450b0200d9000715416100031501195808a0903044048407811404684500d5606e01c003601c02c1e0f45503480030070800e41051021645c1c41e42c09004842900c025110002c000c1610322110700d04082c0c10340c6007540c450b400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 139239883 1250 139238633 139238647
    0x42003010e010e090a0b2217032712070525140429060d0e010c080615070b1009050a0603060b010212030112050c030a110102071a070b19020f 62
    0x5222001500440903a010b0309083c2a1511039808500c400b4001c641c7c1d032030142110782c101c0001c51129000044d44905010341c1d800382040d054030b280d01b00b55140842c00b02c11103521520800b282400f00d0038035146c4030144c0149049100101101d4200b04402d5070103002e0320326803035000f0080154150b028800c42512801060170000d0b852568180f00040c0c41c011450802074103001c0c0d46100c90400c0e44e41023007408054028201012417028002c0703180d940f4046052200c544030701601904152807031901e559501181d5640d000800c50300050401c0c0c10400003000300069000300d003000c007900350312821807802c2c100d14580d03d40103d011694100c3780e00304c8903940c0d0703441482002624094000d060000b40b00900c1294626000c5400e02c0c40f0601c910106030a00c141e40a04200d800e04c58401205e00060941d47c1070022800c018980700004032003213006004022000c14110307a0391529008010110381c80c541444c2c0309954615080b80007902e00c6150b25180000004550124002026000d14550141d03855500e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 139241133 1250 139239883 139239899
    0x5060a021e03090d02060106050406020c040506030f15040b090601150305060d020d03020604020307060306050f12011808120901020322060e0708030a08010b0f1204170d0207050d080606030105042003010e01 90
    0x123070095010018100000c1240320703400210030901c03a000700d07000502d03074841c1e03030000c2d00e000c0340619000d00e00d0180d80b000b40f003120000b0241c648114007030408049203954940c40035032100360900901500500c10003140e03072003512a40c4036690100001d490003005680580004400c4002600d04400603804079040108509084c01030500408031400e0a201040c01c000001e0091000c0070b0040b40904800350415640074425045810014001941680d4000080c02c104480d03030b002c4030f0740781014040f030b034081441d054051007128461409070005146c0741400c1c40c56a11002d80d440026200303561246521170340064148200e4004040960040d9640c143c603c601405551059100260300001400900d0880201d80212004c01e1600d0138241001d60302ca06e040c204800342c9020203400d000780461040944c85c0140d008001490141d03040b43c5400e11104022165030b078003210364035040b8105000400c44c2c2d0030a5045441c440c0d001d01e03402a0101820f06080030290001d0740302440810030b110041224407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 139242383 1250 139241133 139241143
    0x90b0112060e210a09090c030606090806040f031101020c060f09010e0c030a03030915020301030302031c1a1e040f0c0e09040c0e06011b030918020705060a021e03090d02 74
    0xc0c14140142c41c02900c03581403c01142c04000b04101168400610700030715031311500e1424094941110f04201c690741244004005008030700483e800f2441c42040498104000100a1b103e140e0050f1505541e050651b01140c03204003141042c1d60540d0207004051600c0c0d4180040c0e803080b504518000041c0c80d10480d000d0a60b80c82c808429000d801200003081175444c0410504643d035094140400c4801c80c41c44c2150301000d069548502d401d2000c00080101076021008142481800058490028490160008032500115095206081c0310907280c201c0c24100342c0600b018841c501019103140e41c2d030010a041d505141c01c54104543c0c0d4900c1e005000340c11002d9640ca8220541d450318191a25980d8000b50000d14040c0107560361081001484580c400e4070f101d0034001004e0084c20f805062841e0260401120340940440000b0350703061140542c100b131003034804554210008200c95210129900025803022084000b46505603803080154200800154000d1455038003e007040c8182c200000c0c108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 139243633 1250 139242383 139242401
    0x2120a110a08061314060c0c060708070e010311091309060509150403030207021f020102070b010e0c0a12020403060524040212070809070e150103060b040518040303090b011206 77
    0x1d10450842446916000078a440c1d0001070808643c4103000c0f80d0525080400c3d500140107814400d010800a990302e1010140034075901034001ca5010b52103000041d00c0b004011207a400000e0620741d0141000e40c8681c01224070003a1802c20507181035240b40124040020340e241c0d03040c59580710490482044820b1162950000052003d03016182441c0c504110005010380041d04140c0c011078000195030361000554080c66002c0700004881021240c064040c0d080340707900395000b912501c00040c1d082d840380c0240d48252005078000b841c0c588440c0d010f4a400c0451442c1c101425400d102c0400000c2981c03281030b000d80b044410001c2d00d4a12211400500f4040111440c0103038014050b0140d48010580c4c03040c3c02c90200d080c42d460341d42d1014003140c0307403c1783c42c1c0c064107101c85540140a0943d10680c03c07400c6500702a41d040c07020540390307645000107102d0307840340c0740c1c00505e400340030502d010700c4424032034006119290200714102152180d810005003a0010003100e840030145004200080c400c006032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 139244883 1250 139243633 139243639
    0xe010207031b0f0311031c05070f030b060307051b06010f031218090507020102090d06020301150903020303071e05120918150f0102100609090b0618130305040302120a11 74
    0x100b45259108503484890a00c0141807144407107405900ca070050042d620545402c1c140311400c20281d40c0e855004d85802c0e04e208000c60326500b46211924803d0041d00d80b54000909810300e140c5810700704680d00d92083e00308881104a05001c1031796600300740702041c020403000404007040c6085040c007803c00411482c00a0034001c241e0314030114440e06000740000c54126010014440c0e46008050340039110740004294000c899102260802c81c2da5409103043e1852800c1c43c840b000140340c0d05464101171400083e516a1050054100250302c81100340403a110404002c0950b18584c1d0b03903189041604030075200030000100380100c1a0a005041d603403546018403203103c03581010010500e0300d0511080c030a00035aa810000c00719a4000c0203244001f0308400303410014142c0d1150194001c0040ca801103408444040104529103001844c1142401403589400490b4660303104401034500009012000d020040c0f01c00000359641003070f29900ca042c0040944404030b0b0510345501200704001c81544 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 139246133 1250 139244883 139244927
    0xc02031306051e030a05041101020a02011403090f030418110712030e0106050d080304060606020a151e0c0f1206061413270b010c030e01081008010e01020703 69
    0x600d259000448804480881c100980d4850445940301d000c80404040d88030a03010000512040e500250300c428800c074000c00741e440404420100480e1203156202000c1d000901070b40a400241c2030050042d500312a500c030858030100713480070b8414119080b684c01030fa01030700c0c850009440711303400e4001e0000c1a80c3c4044028545202d650b180c0e10036000c40c215100401d999155030f0a10308000b54031600207080010050403500503145490440c40d0700c210381c21510703542048000541b103400021000c40c0d0a50000300007900c4480f00389d0440c0180100048201034001d1044401e40c0c11440d8802c608180e20700e0b5480c124210880301e8060401541d1441801c0f010f032034080d04100072030f8080400383c02016482c00056a801c40e40c03e80e070905002c5900b005004040300041102c4c40c64981409249448001200380300f8040d10038015200480ca40a02802145550108103060b600c070b00c420f82e6100020444200303515031280d1841e4216062403050414981d070000d40041415005000310810108140c0441 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 139247383 1250 139246133 139246147
    0xb030a05060418060c03060f0f06030b0303040506040b0c070306020703051b06010602100b0d150c180803090616152304051009141204090506030a050c120f01091103010c0203 76
    0xc408600c0050f0040c00441d61030681080040c460f4200780c000f010111442d01c84942c580e241c107481c0040512452000c2458510300000508011042d02c044800060085040030314020030f55140340d10010008119009a03c00070000a1844c80a01503d6010365203190b01c5007000c490403a80c4110702228a12658003000040184590001c1d01001d030034080c0720086510468180480d0414000020040c08201350400f801c0c000aa141d007c2c0307140b8800d6903100f21941d5180922950303007594501404881e40c00070403014415060250003000741e44c1d0b0440320311880c0f541c2601c0703d1982c140001960449140c0318100120b1014061002512a200d154114181402c140d40d076955283e0780c4d15119080c60751aa20384006205803284015984401072040e81e100f403042e0401c1b00e9541d032141c041c524086181c103010550a0a000881440c110391002c01481181c2c1108100700c0c9407a41240801400e00c0307100c5c00301090b55000c1c001c0e000114802d071180000c0c0782c00d002c00c040c2510030000022007194400e110b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 139248633 1250 139247383 139247411
    0x3090c01030209030f0703050109050c06070f0b0c09060c0606040507030b0306040209090f030309010209010f09050f09042108060405160c030e04020706021b0d050a020304051c020a0b030a050604 85
    0x2214a04024240140e940d41c010011a080a0580c59482040c1c041e1003400414000190004500715100b02c05803002c00c00c284040000d1400307040c03800343c07022440f4031050300040c014011503500300d002c1c811400d00301001040082d42c3ca6010740c02012042c0c00801c01c0c40054100350144070b0b000042c0c0c9c1801c0c080c1d082010082603840d100100702a101d407031080042084400203025a20000d1180c034281c03580c0e8901650114042e43c421428240082d1088203060070301c2d40f148180b04141e900040158041e01400310801c41c0e40c00c4094403d884d50000c04403000e68201d11080d10406e010280c1d100c500e21340c40c00c2c904200440300000e041c80d00400300124035502c52a80f100a551505615040c201611002c800200c1e009010300d0302d0040004d032001800c601802c002607921208200a1002c442840a203110101c40c540201800300015a05c107100c107201c1c9140c07070300380c85000d4103003010f070303a448002d0303540015660903544d50040150745400810702c4524402c501a4a1340309000707981c1444404030000d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 139249883 1250 139248633 139248643
    0x411040c030216060b0604080624030c060414150a020a020102210406081f120203250b090103020904060b0424090608040f02040501030302030903071d01120203070b13050a0b0309 78
    0x4000d100031794400410182d030366031100307540c090403541003101e02c6440c0a11040f982e07000004000050340307024038440051490b0018110321215000b815440c01c041c035200407172800c0d601c1c42c0340b201e500c140401c10071462100c1200241400c46620703401003800c141540000ba003000038071508400f800300384413004500102d11a084504a46440c41c18441c5585c64844844c210200c41c0000c88181c14141e400103242001c542841104500071000e0b074000085402401c030403104141c40c0490b41d071034084800c00803030203c02d024086402c41070501510f061031190004080350300c02e030000199950041018841030303494850380900d40407200440b41040d01407002c0601110381c0e6106040070802d8240000782000709400b202c0500170780c090410300865860741f901a40701c0d046809094002c0c41a80e200045200c0007880c03c8603120340d03c41c0c0a5040d40d0a10038558040115148207903050b104401e13000074078000050040554503044201d03203200d142007034100440b9082d640e1054400c10f0090092001079140820 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 139251133 1250 139249883 139249927
    0xa150e0d02060a0c080114190b030103062a090521070b0a35070306051002060103021f0c11010504170303061c02030303060d05010f140906010509040308040303051504050411040c0302 80
    0x5500b81c0c1710708d00342011140c0506507000541c3e08000407000204000d41500074dd000900108103038032180e0400343e004040036a0600e074941c0000c8507208100802c0c02d0040744c024040750031812214402240902661814419512a6600850005803020856808000100c40c141c5600415054440401c1145042c138800318a0344420402d40c07020601050083e40400002e02021300142604003000390042d450f14000d1205030b02034886004241074080450040c601d048909455482d412034031901d4a03581c06c100140b4403414003608000224501007502a480c0851422030011540c03440c0840602540f000000c121300c1e0016410f0000f03d0040e40c0101c00e89a10502c203a600e051120140c2c10000d0150a2104205410501d0210f034043c9000c89601d00c24861400141100c84c2c0d640d0f624244081c41408030390103000110440046400a4425008503070080403682020100150280020b0308448058804917440d01c1c0a8018100a0505014504000280d401c0850824051030726000014001305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 139252383 1250 139251133 139251139
    0x17090a021e03031306020303041203020f0d09050c031912080f0f09010b0a06020a06051b09010f03090c260105010807060e040e010c170109050402030a150e0d02060a0c080114 76
    0x4411001c20344040050300d030001c5515181807070b603c0d41e0700d0004e51a40d1094800741c070001a098800b5001038020b0080700c00e9001c084600314902601030050200030810508211814002d403103031461596001c109880810160072520154140305e03260144078000c0741d945600911000c0780811184692110640b0391081002f95155840d603140701407c0c0c01011100320715a8130004140020400d607900203190113007184941c40400254071030f998180c80411040c0303170f0200d030803108100c80c50b1554800e2062400094043c2400f068200703403580c94046016031904550195191902d5100c00b80710782e50199400481c105008002e954140081140c41c2e40c15801820f0070300c42040304a5036151580d82c4410400d0b112200200502007030f000d0000c3c0340304a0780c2d0040290302540304c00440c003045580700d800d005543c001d0081020719410b9950041d02c40049020410745a56610043c81110003170280f010450002d40c050417a900d4801500c03001c070703a01d044400701004000030040c487c00b02e1241408148404c12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 139253633 1250 139252383 139252429
    0x1050403021e03010906020921030306040c050408010609020a030f02030f011e030c0f082a0103050406020702130f18030c020411130801060302100c0b0f15030d17090a02 74
    0xc0c042d1251540c070203650b26010740c40c00d5058014040707140d019203059101103031701126004840740c4120071080103d241c030105410400100b989464540d06c00b221050081c204070b818181c1d0340c03601600311011940f01a840c45d070001020341d2101d9241c8030b00e0403403425142c011815810001c50300d036511141401540c041c1e414040d030080b0000c1d07221705020000c0d64004d10000c622525003180152035042e03481002000d111311f01c4040c02d40d1400004810135104581d40c0000745000c100011805400c01030030540c2d0041e82044407070003507100d6a021100942c2214030225281092440f4502180c1038108920780b61300365020b0403000a6803094a941d026501150701044400d03a05000301e941d4414406900300c81207a2010004d000c010640111089a000311101c145000d00410161140d0785003c000420000c407001c006601040f481c80803a0301320704d40310107038408001d140000c81e03d04401680c030080411295406001342c3c5c2c0c8442160340d440f1650b034010b0020000c0c160f000c03405124036502d504141a4031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 139254883 1250 139253633 139253659
    0x506011d1e040e16080f06070f1b0b0f0f0106021203061f080103060e0c0a090c030902040c170c181e1c060e0f120913020c010e0613020105040302 64
    0xc0103000141c0c031500820400c050b400c11058156100c0000c1c00c0e0030100e00010034000740b10600407170900b0090340d000b4050300059844100c21501000b0080e8154207001c000f06400315800c1180c01c1c0058a03034400e0402014600304200030400c032010040c00c00941d03c204000601c00ca69001c1410800b800c640b40300b00b9141c1c3c03140c00004000030404448a0080f0b290620141106039001d04228100ca01804041100c0c55003c04203a49407145e01481581128981c0000c100940050303205480001c07051a0008045411703500003002d4900410590300014105000715842e240b51030002a003145d042401145401040085059108140842e040c850b0210040e003800b50f03907200c0c240030300034000104141d6100010716280c5414002a400582e803042c90709180350710004002601c9084403101800800130a8001c2d403d5076000e40c070034100d50b908070164655000383d1202c1d50001e4804540b0300800402c00c024090402c0d85024401420103400282c000440b07130260741c00c20212416650190f41026130300d40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 139256133 1250 139254883 139254919
    0x30b030c150a051c02031f0e190207170310120f02010c02031f09110d0c17010609090507090507140405090705120a05041b2304110c100506011d 63
    0x32111100c04c1d0031840c0000981c0441d5550040d40300f660805000d00204402d06074103420207025000714540d103814200481c655031031300100c0580c124200e000241c85c0c1400c5583d20003400103060380e96180108040705015140c1840107000307000d0030300c1e10308807503a402d40c0e40c0700c00814004c0e0050182c1403010755003442096480600c4003005108948240182248c80e81d041c540041000d020151140c00780b48090a0f41f600d082ca9644181e1600301c10207401e214141141c40743c107640d0364600c5100da5940c6500c002034812260284002d1580144041c00865190540302010384038000c0602d010000300c8080c48a200720304006440959105079031040d0140c1e45d1369820f85041c81505060b56040841c04204951803402e508502e100b5031041400356052100004185a0544c1c1c5004000c0075007504068101e1748883c034aa1070030241d800400c0410710107489a140400d079803000c80345c0784c09600310305a00796549100780280b41d00b240c0c00707283c040711203101c440d41021040d0f41d00e11920701c110700e003210b24050b0003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 139257383 1250 139256133 139256137
    0xb0112030509040b01090302030706180906050f04050a0f1401031202011103010b07061413020307090203010b070305090a210302070b07030507030309020d0c0b072109032d06020a030b030c150a05 85
    0x26501400f22000c86840b2440034cc000600440c5603008034080650116501d4401e002d084210380001c0c110050036240c0c401080040c180c000d081c1d950701c81c0d43d00c80c91180b240d2140554640c03032008099504c682d50450a0000105103840c15007419a81012000d403601c0360140201e85c11034900c0c0b0b0130551211a03624146018000400c20350840c1e40d2041c052040580c0a03580a00405d88220225034845e56120040d0042e03000c04d01c03801c00a0703c1e06010050200740641e000b840f04071002005013140680321440a00c5000c600c19a90040d54405070f805010107804006143c003a240a440d150300340302c0070b1b5a0040692003a200b0040403d916010420215111105d850500c00d038009014400541c0307442051602d5000b40b00161211a0800301c0e403200080203011500041480b40d544000e01425600c519030084c0317900c07014050600038045480300e6051016070714030b00701d031041e80050b903502d01c8000000c058810001580b40720b50808a088991555403030088840ca070036240004c0c0d101d00d801001907600d8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 139258633 1250 139257383 139257389
    0x3070e181203070504081b090703090203010207050a03020d020607020c06040302060a11071e05090f01050402070c030501020f0901030614010f1103160f0501061d24040f05040b0112030509040b0109 86
    0x5210200600100c44d070000060015540340342d04840c2080e000b01541c01a2190412400d80c10580300da010820845c230940008003014000307000945804c0595558a05e060080e401c25130058100d1416041c0041c2c0c14000650084d00300e1008010101c00e120024080e40324510000384a007900080d841500707402100c000c2d01032100a0260b51130300e50345a0300c03581e820388c202440c80b58010030b20a0104040c44e040180318060300c0b13003c000016903800c00090200951100000303075a100c811000000c00614240000c0c0b603012902c4d2522615011850300140580e820368019010b21801c1c6500c440c0c0d0351340e111104018250013841c11500d4018582d100c00d0562243c0007801c41c0c5003808282c08010300030324040d0301100c20302c282c0c02001815502d43c1c041d4503000341c01c0c1c0c2864552600c940070405050100300000344544000c0124103040114000081c12140a15001190140c40e00100b01c1800f8800e446240148a9030039012880302e9503903402040340c403610780e02034411550f5464085050f4403510111006e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 139259883 1250 139258633 139258663
    0x1509060b090f06041b0219030e0a030c0503060109020301030818150409051501080108070306022a0c040f0c051e1303080d0507020a03050a0807182303070e18 69
    0x9581807800e8100702c071040884031140200d0600c5034050740e0100107022036841144540c090700510031180d4802d40d1905046105904200c141c04800000c1d5590000250045128011040c840e074070300820b044c281441640030390080c91040c401000070074110001c4a440c00c0c0b0541076680d0b990a5000010500f200c100700f403e84103480420046010550343c0c0c001c50180d030302c1900c41400c200c144001104c0d592002d016080d056042040e0400015016401400c0c040c9840c0da101980f45e84c02000074040943c2214000d5000e900024084207207041c40c1c441c40d015803030166805e00040c610800007906500ca004480d020481703030002011001d0340c5640c1900c2c0390441c0803550305030040d6282404070042e0491715040c0c1c0002d14000c0844d004500015172000a0b9a154981c0c40c10202205d00036540f60400901d003d06001c081142c10640004000b9021f000c1c04407804100c1e40d01040003c40b100c00308421207600c0c00703036002d01d0050110311421142d4944c0044507010070321100501c14942801d14143c5c07094005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 139261133 1250 139259883 139259899
    0x1b0203120f09010306090b0a050d03050903010c0c141203011802120f0405070806040507171908040f0504020f070b04170301030506010e06010f140f2107031104031509060b 75
    0x1c81d0444020301e8140c40907a0140302e059100c5280718110b130800c0622961248650808100a05081d80d041e200c0501030708160f81400305c02c101003801d44030300315213007030015407c40d4050301040f006041d072511010681005181800c1d1003000480305c2d10040c0101d041d0f28551030303803801803401950101e403011244292004100c1c20501c203800c01d000b4082d202115103018640d0b0100d1940c000049603403050f0742290040000919200c003c0740c030a80640d4080c0c04502a0850189008014101c0c0c4a00e030740c4181c001b6540d540c6046c881150701596a0000e40c440c500401035250320f1801c16040d02d01464111b09500303807a4880f498500303c84a003105840400c888040000000c0c004080341107812550784a03208059a607420f00111624118543c0d440301140d005803042140c0c0c070b02440074240f2035080f04d0551349040c09202c5540ba18204808051301e21050440c01c126000780d06003d445030840c0c0700324a642c00c0074115940d4901824a5801a10700e4603641d001c01028051141c01c00c1e810881e002d05030344 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 139262383 1250 139261133 139261147
    0x403080909070c08071b03020607031107050a120602090a360e03070308071107031b0503010606050d0207031206030311010b01020d0905010c14060f01060909020a1b020312 75
    0x626040300015600ca4032104000a030600d006205882030b06030710a01302403402e00d2a654100750511a14680c4801c1001c0300c00c00700051302ca55000702941d0f402a1610711140c500c2d000c1d5140b0f0880d03030350801c41c0103e9081500300a0700001d030b2035040003142d01c0326015132509c0b03c00020801c174001c40d5000c0c00c500c2c4007110340031880700d841030000c8a54010000400c84095140c0880c842606c00201d10b02e8540d91042011802003446000307400d42210b03451400c4204928810500f81c607040d50394000fa900e0301d154100d5000220000d5117500014034064009229642c90000050010302031401004034154000030f400c1c0c109441514540c1a0382d9240300100182d03516800c00070001008a0340403d1075618044030f0310304ca0b40c00001c2030150004644d031104d01e03242c1000c0044a05150f4820226150801c441074028100c1e410f01140b0702c506d0b8064807490321585000030083c60030703480341c2c45100e0f1507104001704010581e00c05401d45000034040009000c41a03a4400f19142800004401c0c280640c042102 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 139263633 1250 139262383 139262393
    0x603050907170a03111c0504060210020301060c020d050708010e070518010305070312030902041406090f27010f1b0207060507050c01050a0219060f0b040501080309011809090804180c0f03020d0f020403 88
    0xd4009c3d00c40e03550890715401c40303020040f000c0740b100b80102e1005c100d90071301a00042c6010103200a4161044c000d9411559595002c00d09690f4050181c880c280c003c0c11041c0030b642000b000b013a841401c50031100301c01d54519100c140c0c48900745d00014014000140c409002c06019400004c025903000e001044460303e000f0302c1010b008802d0390b00d6031154400c0c1010909249003c1d01450150072080e1a5801d0b00201ca22a0300c2d1300c0c9002244c070702465403036001e0304403200103a100e0f1031101d60112203010225a41124000c0c00c1c200d00303401c90001d002090002d14085100001c0c440c10004007802c209968034420b2400303034645601d07070703904281031002c501680c41009070540111007910105541031081442c0d402c2000180d650902034080e19500c1406203040c10744c86010300080c444880b103010286241c441c840c00003914680442910b004a00140030820701064548202c0c8400c0000404c006044109070010300410401ca01182007540100b036841d550b03c2d0551002e01c840400078003c56603903540b8501 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 139264883 1250 139263633 139263637
    0xc09030c12030306080c01200106050901090c0801061d04090c0503030c07090c020f0a1e02030307080a0e06070f0b0403050c070602070503280602070c0506040603050907170a03111c05 80
    0x10440001e400c251000174410000500f40390281816160912041b0307810007548000c2014204001c1250340b14030703000504c1d8540c050518060409d4840100c0c07013540d42070002d0142401130740200b04100b0040b24800c1d460032001405510f0003411100403480b50900d04080c042060b1030b42085a00d4040040d510f01e1400d400102a001c0768100c0006004a01c85e1b00c0d000d0361240742100320380b940307504000d401e20005200701d02c003100800c03811405c126240d03179660040b0349140c0140504903009240020241c405581081960b12002c0048445c1c1c1e1600301280e454010700302c19510b00a03c045000c5011400300b50244041d02c81c41c000c2c079821505070540c0c0700c4000750741e08601e00c20304d8000c3c0640f02010442613001040c1c42c1c44c4110300c00024070039120700e6841000070340c000207090b1101041a1f001041545c1e0b480c00800c01480142d8000c9a01d0605440700d9040041503030141081c4c40d203004c041d11aa64002ca400c6000359003600704041a10302c0e15038403604180c200400e00f0300341050083c410021640102c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 139266133 1250 139264883 139264919
    0x513020d0b010e03151803130e150a0b07050f01150f1508131703040812150306071b0b0103080714070f030809121006080d020a080307030c09030c 64
    0x102402400c807080015601c021800786841e03015000a00c0d03144180510903521600642860350700c02c00186c080e05500d045411070030141000a912403c2008502011700485402c20441e40300b51840d240180001041c80c005c0e803049600d04880487d88805010050052540c11080c0306e0007400104600c4800b00003a0603140101c0403407030388001c0041225410b44004214103000c0d0340f201a083d40b5162402a8134601007182243c2c0d050380c00344001848501311700a1401760344140440342e107962a10700036118010000f0000c182070242c81940d0401580d000400e5070b0404014200787e030309031038000700e90344640446040c003512030803090000004100095000701202030280b08644920001d5a40302511045a842152200d944004062011621060090100d0720313008080001d41500c4102c0340e400c211081480c1c1800c079580d1403003003001c0c110622140e0307905e11013403000d0300e07929125540d02601c902002c0e12030300800d56200c0c1b5050100f8028140b19000e56001542e800d1400e580d52025061084401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 139267383 1250 139266133 139266157
    0x3070f02220b1507050a03030e0715120f0c020703060b040605030f1e0706020a020108061219020f10051213080c011a010c080a030c090f0f05030111130306020310051302 74
    0x80c0144403c0060106454605a0200c080d16500405460480262402c0104050140074022000890503030601002d003400566880343c03c50222100e800408451040309060b0180d410300c05d085042c0d55001c60140c1c02e0702d500080014503e100314000c940100000c0c3c0016406102e200ca542503604000075014107800d030b50b440000b08400d0f00c20a1540c49680900c81e0385d01603809154044010f40c050481a80d010001605450348201c1c0140c6403868060303c4498410448840c140303107825818041d49070850395000340e8008022a46240000340a44501800c0c0e28120100e100844e9400c8003018202a825810a00c3e180c0c49110107500396000305440b11300d9040b80800c183e9a45000d50151041c00c1010740c10441040c180840302d01d0690280482e19192810005007903400300703c01900d8020b0310068030008450313102c00d070708110516003100c898400211168070b0034070518481d013552611502c25654070071805038a135102c124070341c030001100780c00080c3d114451891203c4444800c1c1e016060b000c03101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 139268633 1250 139267383 139267399
    0xf0e07060302071e111c02122a030307050105011e050a1404020703170106020f060903030f04030c06140c0d0f09080a0c0c030b01060207030c08070803070f02220b 71
    0x28003003603040340300c0c511008058548002a0316502408000c0c15544503028194803180d00f1440d00c0094000c1b10710100403c041c100c5110307040305504040c06445e0340100544010840c0c294008199890302c0d05840e29417084060482044001c0e850501c01e413040f107903104c00240803039610303281c00901050b1050060805410f03000c0c4005540d10304810031000312005098002080d21180c021721000c0d42c4412025014401825000c040001600751030b103001b004645d0144c00500404280141004006007421016a10034014082d02810b26900c007a086681170508940d040684c0c078020340a0440c101c1c001c071030701441d00104000303000c005000b0950404008410031684040c2c202ca481110720844010b462840184003104110f40106962400035000d103005880305030380d03951217450b100d009810000060300504c10400170000c11400b175001409614001d000010300f010100c0e0354070300a1290280050588a372840c017913454580729440c03840c10340b80441002c0e06510110402400844400d01e01405034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 139269883 1250 139268633 139268639
    0x3070515011e03122d050405030f0304261203010e010510080702060a0f06030b0901020702091003030e01050f09031c090602070308090d110d030807030c05040501170a0b040f0e07 78
    0x49a02d90b00c041c0c0c1d5001408419079a03801c01c0840311038140b0501c2c1c400b1111303545000c190f00e01914680141000450303450994032400c1c030080c54140f10300f0500303880c0503600c2800140400f200082d600c00040c40c800707402150703400b03032108002e2a0000e1010f110314010300006c004a02c5a0202440c175060310030503126032416405803082194607460032610270b030042e00300c3d01c04141e41000640028201c0c459001c00480c6007a1a03032204441c1801c2562240801d070b500091000444c284441015441401003000b095402d01d1514040c10700d03040d00c04013504104001450140030f89d00d000c26240c1003007002d0100d8401680d200265001c1210f060011400b2804038240043c1e06440051580190307540080be80303040c141400280550034035601c500711a01c0c0200500f10000341c44001c1900e040e44c4c000d64074050981000ca8002d411100e00040000c01c05c1000c0006001a1360420490032881030380b110303080c1d0140d688172400340c02040c1c032103c8203500909007003015400100d42e4003d18460481c00c41035a41940e5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 139271133 1250 139269883 139269929
    0x10806010f050d09020103060f0e0a0b090403020a0303090501060e04080c1b0f0625030914010e011d150f07050c040504031b03030b0415080d031401050f01020307051501 74
    0x81e410030740000880070003600b20041c1081d04481c08043c0f060502007a440d446404281480343d031900120a914880310801c03a50100a0040c5403185209580310000350030252002500c8041500015007415180c1100c50b04210003588004028031881801d404281840e20f40b10210b540319103c51081403041c1a5001043c0784003090100e8000e00060165025071855000d002d0150403905819030310410a0a0f5511b00910302d61402c3c6903180720b0303900d550b140390402c8501500c5829201710380d410044c1c845040c1780240d0304001600c066460a0250842c81c50030000000c90f56040701e01c0040c80201c0128000f42d1420515020b80340c5c4c0da01c12400d0b51200e41881c010f200882d18201d80c0a80011019a0008180001c106008a00501a207408101c180c0504041000d690300030950f036049598600c810001c511080c015135251030190b01e8181311034110424000c124100601484c1c0c49906900e01590b8168020400c4424460b4004192078030b1800030307100008119004d11a1809503070b11301000346600c032 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 139272383 1250 139271133 139271147
    0x5031b31050901050d0305070602040e061201020403022b050714040c0c080909040503041e321003022101030b0606030c07120905030a050a02040f1806020a200c01080601 74
    0x1d54040e2000d0501c0e860b241c00c0003c41c0381d00820690612008001c03460208105000500180c0b5100707120210f80d04180c6d052003142c1020503070035100c99105000a0005a0300c504c8101400407800c02100b5001400d008444441003402d800108a032140b0f00b400182c8212504040080e031a040f00c01f000411400300c4250340017060104001c1c0054804c1244c01d50b6441e01c250904d0304540200100c07400c3c2034603001001210b60882d45a18001019400c0800080041d1000c001c0040f202803011181144015280f0108403805400d042c410400d0201510480344aa815504011900ca0381c1c82c0220490655206103203c00f80800d4840d108650009900d42c01c040040b640910901e5030300c6450000207496090001d0504c8410300e0401c15940c1001030646d40030020381096074029070207406d80400354810801265501040100c210381011078035602e80e15440091741b515900003138050794426982070300700d445242c03070440c100140308028141c0c50007020000717001e00da078074081c1c1b60444d454441d0401941c401c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 139273633 1250 139272383 139272389
    0xa08180a0c051212031303110a080d1b08070309081309060905070903020303071b17010507020d030b0307140a09050910050f060a17070306050a0b011202180105031b31 73
    0x4907904102088050386e00717400380030b0361600903e080f03210404031042442c00d003140288207840000d004034445610340c4451240c4e0000200292002d402c4014403030020f0001c02005204505250f5500d51000510810001300c0300c2c1d00110b20701101055441d0369094000b40001c0c05442c1c015458100001c0f50540100756401c2030301d40003030003141802c01981e45c0d40c507500500c8200c100324441d00c401c0080d6142c0209000015200c0840000c02d0601c1d20f04030082c50504d842800780201828002c5240c280c1d100880e9030000d44001202c3c0342180b61565000c108000d007a031303121103d0709203084c08100e0581004115103440300788000d000d2059032a4120403000300c42c001d44015910295880f010410f880901c2d400c420400312a0f0255081980d42e44c440c0780442d101100c02c080c843d0b48801d40c0101030343c0e0041240005a411000840c140309509500c2403034000c00000d207606000c000404601d041030a07201050910014071240c0761341e41d0740d00180541040e20a40141e03131002c01c2c04141c1200c2440c5548031025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 139274883 1250 139273633 139273663
    0x303090506070206040e1302040204140f03010b01091e12060e0607080402010503010509061c0b010906050d081b070b130906061d0112091e02030c0a06050a08180a0c0512 74
    0x2030900f404003c1b421038101504918500e800014480c006803564000381006040d2140d040708900d045e00f061198103035403000024800e925207024400180c0c0c02031030800545580030070700001176043c10100300030400d203900105144411500340b041008000d810140f41c1800c1c400541d0b03e00d48800b40140c414240c1518000e022680600041c44103013851400709a104500a09180e84c04000042c0030000710000903043d508109540014000c0131382a00812000301402d540800e10200c207038807441a940194520b041203c4e15025400008010400298015010004000d6034800140180a01d843d00f0392141580d61400c026001030035901543c000107050404007203000380d83c0c20402c01112168240e41c07080007807030b07524140720006c140c0081045110f0325600642c03048100385401058a401340a2040c24482c890480c000e2282560107000e660140301c0340d09001d080c03a154000c03080c030f1549541a43c184240b08440030401480b07080612141111401ea030503048040900402a44951050980c558 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 139276133 1250 139274883 139274887
    0x180702030a05130315050a050105012c0f0913062904050a1d070e01050603160c0206040306050c180109060507200405010f03050d09030309031101030609020c070303090506070206 78
    0x10406024800406182011140f0030b00ca49407284d0714048005107901010517003640e40c804000e1880a18494180034060909207105030740003a004040f01c0414502d5401c2480d450040101e00540f10310320000043e03240100540ca007460003040316240d450b0102030545a05040c1807025000d40f599182092400700582200444011440d050002400c000342c5044030041d0340748558000e417016101010181c0491038050802c0300e10b803904070140c001041c0c102d20f01c103510801c01d20240b86c4100c210080862000d0504c81c0211103180001881401958405007860341000c08000103020210010202c19101c1c11038120090a143c1c011074000d450b40c0100c5011510802050003c5090140002c01c03600c4928800b00c521a21030b000b08058a0081e0700100d06544504401d00030488148040012400c403031034640700781072544d01c0040480c1140e100180502c10440030300681070340b01e0303048031019060300345080d55140c07201090b13140d07206050300c000e400084c01140c000c100751038560102c2c2e50460700240018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 139277383 1250 139276133 139276147
    0xa090206040b1305031603030206011d040f110913021e0a060e0415030b06130b060f1b0d32030a020903031b0a0213020705060103030305060103090b010305060618070203 74
    0x464543c488810703541108a1002d002425584c00c0060b414116001c140f0001d040d803039482d0280c034080060f00410042c1d104a90050b24001c1c03009811580650449035143c0ba00586080952020310007240e1079400400e9282002684445465108503580c425100e44034803c000441d0a569a840c00e8000707940708016200400840b4482c0ca0012800403004000064a80f9010590300c10309075503602c03c80c0e000c8002c4e020410640751240b484c0821507a05030050004094840000d45244182c60201d00c500802044421030f8181d640103071200240c01b4000c90740d250408142c05044440c2c0344003a0320a00c4001203d0804c0c1c0c0c0d00c40f0a125810b54101903016040d502c43c03070382807000307074105403411505840188840384541110666150b8110355503c06094030480c42e005104986000da04a1001c01c1e004002100000f01c0004e44c1c00d0440f81c041c640020140c072580c00480107461414400b03056004004008400c1c44800311b40f143c050103084608010b00c900403c0d00902c0f85808641c26009604203002e12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 139278633 1250 139277383 139277399
    0xd0614040e0a1202190c08010606110c040504060f051f0603020c100902120304060e0307050d02010e09070e0411190206070c080703140414040605030708071a0d05070c03080a09020604 80
    0xf80d6202c80d41d40140d409140851201118001c174a04065444008041e41040920000c2c49000003a02161810200317080e0080b500903512080d012415000d5680c0b240018217106680d4400020100000028000c0341000c0790a40380420b601a095828034444030030004007140130b4800c690006455902520381601001000380090464800c00d9800c200f42c01e4860f0f40c0e9010600c0103201411460710381100c840e20403003d06250000b02c1c1c0001c2d0207003403042252000740c0e8000100000d000c100702c031208801c0d07845e44400c4480c21414101c080d045420a0b446400030307811180504403524a9a03820960140c0814080780d40d20002d0300d80c9030201e506404020007003110301c5d0040c08072601030305002c42c000080c0090004103611960000e44900c0308000f94900718900340c00703120b0040204800402c04581052901038488505104040520400c503c40b84c2001c04000c059410540414408200d43d103070108000e00100d400074400c8001031180c6000440310982441100c2155401401031402c0505141c04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 139279883 1250 139278633 139278653
    0x6050604061d1003050105180105012111131109010e0d0c12030e0303300c0415020109140a02120d05030a0506060c0a0c060f080609070c0213020d0614040e0a 69
    0x190706441140301004400b082d070900a2901a08440c8e460103648142c4580311821150706810190301500c1040c0183c00b0b44250060f103944e442e420030201d90302c0030004400248094003144020184906220f201582203030000c026203a244000c0c1ca0701c184000b0704108010400c2034800004001840d0303034209101c40c4240681800740c0038841c0c101250080c00700e0001914580184120b0216201e02a100c9004501d900030000307010f0f01d40304900d003e941080500426a8060790280f03001c00c0010044400039503200f5002422036903040040070b8009542007070104c0d11070858000a0f40070304441448203a900c0c00010310460510900e944190840e1200820030002d00350140c2030a5001ca02030000c070100080910100950310702c103a01c0c218000745080c60103007410340603210b80c0c01030141d07040c00c0044a0300c0703c0340142e501100500c1c12080030b1006100292020640d00c0140e41c172588045551120356015902450581d0503404284003c0d02d00c1c2c10412054448003105c082c0e051f00141d400030002000c2280d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 139281133 1250 139279883 139279891
    0x121c0b060d020c0a1401090b0708060a0911030f010501020304030b01061821030206070908070e04061508010608120415120f020d150e0105060f030702120c01020706050604061d 77
    0xc41454a098103100c00241c2e00460343d42e01c250b0308500c4a0310708200c942405040b6550a12000b8402d422080d00c65444e00040208840f00f1302c42c284000545c80c6c0d032054040000391280b01c0e0200801e006e82102a81c0383e4000700d030a141400d02c000000304072580008299000c8940c0a42080f42c142c1c03e001048a01880e0032440b441000f8a030130f000b00f28260b08200c1450b071505a00c0c80c2e03600e00701060500a152000141000e828803200300d000744034150f8003048644c190740300c400c488000390302e46281250007800100c603000503070410094081207040301908440101e480d1441107840e14215070140b00c0c0b03107200ea80310f008d0072039140e10300601d1210300508d821b081030300b0100c034005942580322003032130140d900258071000029941d64102d00445007040c25040504001c1e04006c5840d81040f020403158405e656108482607004000984098820014408100b000500c2162500c101c03140850103034018507400c4440509140014070f0604040c4148070460701100c400b216030b800049039040e08410050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 139282383 1250 139281133 139281139
    0xb09060403061811060313020f12031201140612010905090f01020a0c2312161a04141c2001020f0c0d0813080a0e0918121c0b 55
    0x1120000c085070b854414204501d2000d000d01d60074030b400307141c4101c22035080308103d8403445080c002e1024059041d1075941441d641600c0354001d007a00140028080d00400343c50903810b03c400550b500003620b1100c581812501400c0603e001e848a000400402d030007030720444500400d08000410000040d60080c0790000c0c0000c2c02d49070400566004642607a102d5004640404c120003a101c0420000c1c030b940d1088046202c50725651880141c0c462078031140000044006800c011655880c4201c0c1c107154020b8950f40001e41401e28203010660300c2030200c007203405440621200103012822034005c603050740100c011200800e050004072506892510302c1960700310314083c000c00740405040003440100781030080441c3c01511002010141894011000404010805018248908600d00b02d80c03889480390300c0292103841301c1e40404122500d9488000040d03000c4d60420602c0048a224880c1d000ca203551081a10740fa20880d11190403c0c0c440d40c000f0340c548048056542080c000a94002503400c1d40007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 139283633 1250 139282383 139282387
    0x1c0c02040c050d09050105060f1e010507031106040302011d0a030f050318151503030a0813021302030f07030e0d02030405040e01020909012403050f0402040f0f090503090405011d010b0906 82
    0x750f03000301c00c035042207030110b81c00da540d44203102245c034245d803850251007002c030b400c0c034415016144030394061601d1142c9181881408a601401c0600400950781c08041c15011901c240c0b4060400a01801d00220a83c2c5109406541c0140448001c60541c0c0c076103826445e0512000425501283e03d6400201309d1400036149071032580c418502400402e901c071300420740e884441d0816680451100e00902e1145200341c1c0100411f91109070056141540a0308120010056001a001140540e80000742c5e0340402c5200104000031030f003648009a00070100740d50308201040382d9007101c40e074841866002c1009680240001c01031880c0c6900a000b00d010504005400c10942c0008103040c0002038020400306a4a44a02c03150180800b41c5440c2810f0309207000c0c000c0341000104402d0280010304068012504c83e030b02c071280343d540c94200108501981c0c004002808082c00c0441c0c40e900202c8101d0300c542d050a00000c0c0900c0d0728404403044000d850009880d070703481e0070403800d515401102200c0e081101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 139284883 1250 139283633 139283647
    0x80d08250305100b04030b190b18040309050a14040b0307030c03030c03020111120a0e0c0306070528050306060304290403030e01060b040b0a020106091503051c0c02040c05 75
    0x540040040c50105076100490079040040084181e10150f070003440742c04405100800c0824090300585410440c260580e0020080103040312001e8200302c01c40d242c00c001d800406c488001c0107040d803588500e010b50b603091201521348040084603075051051203103d94240f003081c4136514190f84842031190b4010304a0b00b02907600e80e200c03074000e02d240e482940495200454202810340a0090380c1071520600e100604d4040d182d14141c144402c060a01d03400e0580e10b07014004822420025403070900030040403988940390a0100400607070028540c0c84c0440d0f88080000410207058030100b1400d0b0494590509503541c00040c0700c0c01f504000c1050390800600341320b4111130140003485400c0d02d000480420034915103402c025050b9142c44d00252400d038981142000788624020075202a280d80410307030369840070390080480c0501601c0c0c0104240b5403a01130300d00024a441004482180e03c910b0079120306215580000c1c4813080740350b90080c0444e8200c0e00314801490b0070ba000e003103140302c5800c00c2414019 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 139286133 1250 139284883 139284931
    0x5091c020d050c010807020c01080103120c0b0130020310050c120a0b01030e0c031c021204080304050405010b03070801090b1804030201050603070b0a0c080306030307020607060606090906080d08 85
    0x341e1220165100d0b0401c3c0401e50503540d014410550161460009110708043c004c0020040300c0c0c140702c054550665003002011543c4203002007044283c000e061525103584a10700c4001000344200a048200c0780e03031646070441400c1c030214000c0103070010058101c00c0342d2070170840c015100c010091403c1c00c00c204030740c20380b05000900c40c1d40240d102800000c0c2c980740d0f800005d02222081811107500342e0140904c10450340d40000c04c44645016080440c0300702e05141e509030b151800403030441c081081c0101d40401c060314000301400490310100c6090085076a1541e1840030792000340c840800180600005202504540d081044c1601c4060b0111020a101c10030345041418180d8088006035140c1040c03008900d000c01410016001d811009841c08044440141c0329840d40d880041020380040000b40d01541c062080c0c42105030007500d020782c3c42c40d040c0350041c0108080c0c0180340100d1408407010580452511030a8141c2d1401c000410401c000410107413540c580040c4000e83c025440c04243c13004003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 139287383 1250 139286133 139286149
    0xc05031c0503010e130803100e010906050d060b01030b031f0507030203010f090e16091508030c1f090f0f060c080606090d0f06020d020915030408041a0d02030f060102010c0f05091c02 80
    0x141a104908060314100271092528500607809400c130981408014805d039030361806450111580800c0020b038950380d44c2c3c01a409840c4503250360340e041c060003400701c51100d4030260503003682c09800000c001039070300c00100b5130490000b8003401d00350401401060103503405a03400000280c11100807611403840c0361054a0201c90540c0058140075190000c0005600c04050640702901c00c02001e1802e00400705190340c0e130381c0c2071740c02c80420300708500100c0c00c06241d4641c02004000d8005107101c4032150141030101c440040f901d8209d95041c948078075420040d2082e940103000d828000c24480c41d084800c020080c1c480d20000c01603c441c100c803c2c1581c002140e0348001d001c041414407015841740102e5081120481c590142c00312417204c10010400040c408404690582d0100c1c003221000a203850300700b0b05513004100030804200d00c00018002c0c00c10081019501c40c80099000344801300301201c0440d0103014010306280403580c180401000e81c68218410010190007000c140c110342d083e07400140f060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 139288633 1250 139287383 139287391
    0x102101406010f2d0f0807020c010507080d0e0321010609120302030904050a060f051c1220010207231b010c060f0504021011030306010305130602070c05031c0503010e130803 76
    0x5084c150080c150035a0803900b950109880d608042c0c08a02e0500d502035101c3c082640c005040040000d5000104581c140a640360940c03002d03010801c6550880c945650303036200c502d03070356803030080c0001c14020201c030f0f0f901d4a410390b0400e0703480b80d600c40d103400743d130418681c41064100d080d404240500300043d111445030b54400e600c1c00801107103103413400e9110300158400741c1005002e401c2807001c81201109105420108651040881000c203050f80d40c2101c008581c210609000c00c458110410382600c150007412007d40944465440c800c01302d480100c041d81108840400354104000c03c940f8412904801402044c0605040c056811282c0e01c6404031503404003c0080207590301e0900c070a504268080ca03000400ca410000a4540e04e8400300e90742e40402002541011349030000034410b201407000c500e04a0b50700210964850a152400c0144c46040d80071300c5009216050740400c0c842e51a04400740d03410040d0f02d0f198030f50390815030454041200242854410340e80000c0d0f00000132080b100071441 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 139289883 1250 139288633 139288697
    0xd0c08010906140d110d0c0b0904050f160c050c0307080615191206021204050102090907020303060a12020a0e100609140603010b09120d0e0102101406010f 68
    0x103981005403000407500190015150403100c5801102c2540b078242c0014950380d0480f6905521640e00c9002980040801c5401800780700c805000151400110f40684640318080f5400e101c181d0300c69110301c50300c001c1111004020700d00e0780c4078a03418a015840509805001d07070290303140301c8400008039103008055400f00741207510030020045a461300c541c14803844541142c107024040c901d24101e0380120224007071254240f0302c0000342d10030007d03d60b04480420b0101540d850301342c505410051300075000708940d54020351203400042c9041e4404403c482c0701ea000100420032540c24400c840c0310800031a00106d8000405000c0412150751145195202c1c200701308031141d0311810500000c000078010781c800c04000c201103c1801440d92408203580c15241c0c5800e800d5180d5032041f0020780707000030550114055028041e21400c640d540140002d2400d002a02140c1005940fa2903000854140e6070030b020568500c28042a15580f180c8440d001203621403800c9011011076120900c0034503540004161 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 139291133 1250 139289883 139289897
    0x10b0a120209060a050d020909030d050a02120709030803011701020c0f0616140d0c020c040c020c0301060f030203062d010806060a05060a0e090613110a030e0607021002030a020d0c 79
    0x8600e030a4524983c4020240d40842c00f09140c00080f0311751b1210740302c2c0248074005510000314112000c000341c5000d0048100c05200314241000480000d62014035a4090440303a4000200213a002d200400100d0354002c02003441d42c3c3c41d14280311103d060001c00700c0a1550200141c0c84011420030500710001664005800c0310305020703440340c040042c0c8900d4201405040d01032040140c94000590300741c1207031801e003c92002d021503812800e0601d2100541d078800d03e0712460302d072a941c0c0040c00013001c0e00300380d0007008204d45034541300d4040c25451000950690050001580300d00700540c0c20b8030121454120072981080100d48100b08200036000f2582030340c02035081043ca49485c0c1a0607000300000c0c1c40080ca0806481d000501924003048034600030181040450541d40720900b60301c20074404d009040200d184c004025180302c0c0d0113207000c880000d09001e0031604810780400c010f0b01440040c1c00409a5021480c2508040d400c024400ca000f10fa003488504031041450141d44144005d5030360f419 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 139292383 1250 139291133 139291169
    0x3110604031b090615021f090b0423010207051207061508010b042a0e060f0406020105060f03011803030f0f09060f050a200f071b08010e0105040c05040b03010b0a 71
    0x100844001c1e900c2004841400e0510442d02600487c0700c0082c980320402d007aa0b80381e291045603000d80300c0100002e0019040c01c042100340001640e815840c0021001040d0800315460f0820b402e0340640d0b500a40b66401140d0b141e075003048038500900c221441038401080c0001c1464600590170055804400b00340d444180214551405219800c48081010005c005290500300c41c25a501000c52003c0240064074210740681d64400d801c0d14003008404100755525a103e6400034040d007016200140075907042c440004203850f0600a4605d40c003040d011210740b010300d50301c00310003070038940c41c0f0368590036030f00c0c5048000e6001a000d14025a03000d00c001081152030a1101c1c822030b000107000300c1c0d20750b180003080050107400311418210303c41d59003030b41610741074540d070111003c2c40380c100024040491400031010b00e4190101c020111003541008005400d80e4403541400d03a44100c0f001000c04a0381c800602103844c0c0340d03125220785034016000052a03004071000c00e034080b109411051028024003021 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 139293633 1250 139292383 139292399
    0x70602072601061502070503010c1b0303200d140601020607050f0d060b040323030405040c0216080718090803060108071209060f060b0906090f03030d2307081003110604031b 76
    0xb00001f41003c0c0c0081007601e822080c02800d40b41e034110310f800225004518501810f1080d00101c0b021100a20300100d002c2c801d84c20358500303601643c8141d00160610b10340d241d9000c41c8200051086606802411b1107940303040007140c4690105007001601c480c00e0100302001c0382d4a104060140520700c20159440e4210309040c40c00e080d440c04000415500b0b080c916000071404000e0743c045031000d80e4003190702c20400c1c03c00d03814281881110380c90007019070f80002d02701c5030024401007104c5500c45500d10a4014044200a0350320000002d0301c00e02e400c001050840d44a00441070f849002c52510f4800000410142825120551811b4a0103500c4aa4203060580705100702e400920282e2026450282c1060220b8110300420201c18410584542e4142041d01d00340201d65660b1030164040101c0e0065502c1d140c040c0f00078070968401c442c448000101c03500d0107a105075008000528080e1102403542d40c44007142075040081c181c00810501002000175500c91031040e52013400001c3d004014200f80341 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 139294883 1250 139293633 139293643
    0x51e0106080103061404050a031103120406020310050334241209030207120309080304030b22030c260408030903010e01050121020a030f0305090a08070602072601061502 74
    0x703a00d031740840905000001340c00007190192540c0c14186041c9060300304c00c5040c01e60040d9003030380e236180350028200410030000b540154031840c510303032484290b16200d005255441d400b01140d1a074035904802c4005601d02e000400f21698071a203280d0324040b540303503c240100d072941d040c401c4409174241f24000400d0b0b60089003880d44110a182e00304107111044e10020350f00c1c035061195903440801421020245441010071034081c148104c203d9940d00c2d40e901d400d042d0040116080c01c0c0000c0910303c01c41c0702c003000b2100e050b0100d82580d5680d01c820801e0311000f050418021440d43c2c84811510f20b03511400c0c414000c1c10080180703401650702d400e0880c09240c291504d080d020744144e45000d0051045d00d902c07110310490307010b031400505040506440810102c101e55000a08844a0318002a04055009005000c041d10642e031403881d0750743c4c651324a41c1d5245240501c80c00358121880a122200c014104030501c1e49820201d030100f080b4801c4000d0031164107400400a2041c002c121225494040103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 139296133 1250 139294883 139294901
    0x81602090f09031209070b13080606090c12090a021e030c0406080d05030916090203010311030a0c0b090d0b040c030b100b09150903070906051008041104051e010608010306 75
    0xa030000514100d07905030f88a100d260290f800400c1c402c00898021102084480302030100d0f80c59a541d15a032104400302303081e0051144090600c10440001c00d40d06145c01080d001d00f101c1c1b210182403420408042ea840710006001c400b4902c503c4141e400035a0714070740e49e0300c400140340d651710000286640c02d06041403500d410301400b46041c8207080003c00c0000950160121003440c0081d01ea4441c00ba0080c2041001801d514140005540118424803035a0043d8105e0740b00c0c0783c0c1c030b104e440c02103018140c03159a10708001d0f24818040e0410414101860014501e41c0310082205401200760381c0d40841e080d800340c5007641d100100c0784041c13040080800500d80c0101c5d2010380914094507040308540240314200d0803501a1035140322000540d14404251a18002d008007230b01c0180391240340c09001008940f04413031050007003200550015009011a5000329084120045440120700511000d020040c0c0303d11540024417a030f401c4610410400c65000c3e011560710803025503d075082001c05d07505010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 139297383 1250 139296133 139296151
    0x408030702011404020618060c010516090602160501051606050c0703021e190303060305101e0207020f040207020f030303090d1d0906011206080d0504030501060f051c05030708160209 80
    0x241804050b0340c1381004e0720810098542d002c0d984108400200da2300e07000c1c11440d04169800d1005014803400580c00079017007001203a0b039013140d203a61100e040b40da80080070512a200780c203000043c084c03541300e00b0040064022289105100d038820703070f5498044031021210f612221034045080300401d9070510490981c0d6000e2402e4400311080e02c5d0000c0e455601c8420101d03004c00ea0790843c0820580260403600c000d58006003550f0010100710902005032001540b1310448201c411048101000380f4130070707101c0b801d801420000d0741140540500c8002e501c030b240b00f80c1c0d20081c201060409a0342c100011841401068007a080320042d6200190105802802e03541c03840101ca540000141c85034141036a10130801d19011001c80c00f0510054002d0443e44c0184049000742c3c0c0c990038078507400500074000c07244260000c000640d070701c01100c101003029002e40d9500404144654040200c03103001c0c04501c900441c10f60f031901c100c90ba00c0b130500394881c800d10290709000e205040194030300061319a90054082d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 139298633 1250 139297383 139297421
    0xf03031006080f0f04021f0305041a010807270204060c150218060a03150b0405090a0624030204050604030605041e05060a180c030624030309060f021005040803070201 73
    0x4143c468500c114000c190300c032201030b104005000d5640350305612a1400405940c101d80b01c86107a0010302a0000301c4007500c00484420030502c081d540e01d8003580c12141c1d40c4002c2c24002e8201449101e001e50366468079404079541d144070708515060381c8020300c01080c82c0e803140d00041d08940381115140c142c092440d1049441448604003100c200884001d02134000c075610385d600d500d00c1400764010050035080c1e611400b510400071404010400040050390300844514805503155681b100544a45009405103001c20800d14025a49500b203043d18050301030070094103144c2c0783d50208100307070411b900954400342c446090205101000083c00041c00700f10b00b200e05403c56945600b503441001030840810140c2c2e400c2d202807000c1d00604050503039607200c0035082526940c2d00b070140260800e0500d0541404c030042145401802000081c3c0850350b0503150082082d1501c001030729081d805001c2c07102903008060003548070041e184501489280b02d51410350312800c22000090071a125450304050400d40f0f = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 139299883 1250 139298633 139298641
    0xc0f0c0906100507150b0111010621020102031b0109120314040209060406050901030f020a050a080703060c0509030a0309080606030313090203180a03050301090b0901060512180f0303100608 83
    0x80311055503200005407a04403005160400c1140c003440780403409807400408030308031441e50105030018019203000741e80d02010448142c40d40f0b030072121244150151100c204105502241d0309a500030100e50050066038140071840304844224285110301c2c0341180d40d240d9529007000a0703030459a1154a0071314003003205059070302d48100d01140180019204110a000181d41d543d140e1300070030060203000d071403500c055940e4a0082c0c01000d80403003c80c410f02c1401800714850400602860896460000071b043c4207165070ad80c1c00c020440b842c80e0508018040080b4003a40d01c0400c5032401c010f101e590f4010301c041c500b618080c100440034011912a400820208600f0800c010011081d00c100e0600180c0d0b0b9215983d1150000d10951404e40c00e174042e01800009068200c00918101c03003001d00188404007545040140056090058001040091104002c01e00703900400ea50b000c0300805840300400c802005040c03404040c82c0350020154000820030103802155070b0f0f1500208202c0c1410343d41424 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 139301133 1250 139299883 139299889
    0xd050708030712060909080904050a020c060c070f020d03020f0106060302090a0528031a0105090106080a0b040b1c14030a050717071a0f06031b040903021509030c0f0c 73
    0x31020b04400104004051200c0c504240341d4410402040381250030410040b032890040b00ca81c100c00b072060b108a150100060304003c0e1802203400940034032001d003c1540e00e002e4081c8040e003006201745c5042c1a070050042c01030701d441445003031040c040d8000300540c10030541900e00b560b4007034025004060041c820445a83c40741e00c200000d686085855a2554600b0f10051120510b20001c41a103601140000018412030003025100640718507441e04651381c0b14400c3c06074009081c0700c1c210001d03c043d0005182085150307c080c9844c180144081244505400013a46270403010341c180900312845050b400803c0002202010040803030300186090440002018101d030080c040c1c00360200c285840c0d40807042402c3c40440c0c102a920440c80c800fa00074440d012640d6200844941c40303544000c80c00f20b0135919000842c03030201001c00800d00394050307260051002800020b0000c8056119020208543d0702c03400d000640f01d110390300002c0d6216000c2548141c9000d0105010b000035401c11600b0320b030562 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 139302383 1250 139301133 139301137
    0x30a0c03110a0f06050702151201030201021911060714070e3103030e2e0b0d020a090c021905010c0206010e0129041d101403060f04020d020603010e07020d050708 71
    0x2d0307210704007140c4440042c000701e843c0c0c8ca17001010002d24007000694004a41c01c24450740d069a0007079084880022585080d083d544140c04401380440c0190f400408080c5004801441503502c180b151420b58844040d1591901240f1307004421070318020001c108920030310802c10b1007980c0c3c800324a58019a200c02c1113445403440746402a0405845108041d200d280030090b5001007818200a80d241510640000c40e848880c0000a0001d505000d0703803032038a15103a018103041d80e80040070400345520317021080c4c00802200850340294003c040201050914030880d07084190b0080c0d0000c02c041001c0000241400c4058212541d00b41044006000c446545101850030000000c0c0c918618075110001e01031a00851b40529166a0240405030344001c0306072080c0d0086911710b01c1a200e00d0b40320000c105da400c18840b035261b050751050380084e41c240c2d10001066045800a0722a2000c0500c0e500850301d150b00982224584821040c144800641c1c100a420788114681c5403207401c102e05542d07401114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 139303633 1250 139302383 139302389
    0x3080a1205091203130c0e0c0a020106090e03160302100207030905030709020f12090703080307030c020105060306090a02011805180103120e0f0f0a0506030a1d03040e040f11030a0c03110a0f 83
    0x18901c1d04045c4081142c1e03881614007421b440710416000f03182c800000c42c4c05071300148540006500700000000d44450070f01032a60707400341040143d41001c00542c07105201c44a010703019800c602c80c145560103840c0f824402041030070300940e0740048140c104001d041c94454690710420049104000007039000103500207607540b217002c209031042c2070f450f000c90f19480c1403201e0b040605102030000900c0601030305039004e080c054806030001c0c40340385d40302e4040544030f100c110f0300e03020b05800030381e0314200641c8166004440c0708440c640410001f601c1d400441c501c1160284040341203030302c50005009111700040d014840c0c3d2010326000c0e0b0448014004584013158030350507240280c0c48c10050310700075038481d244140a010050401500d9280004010340502000b541e4107801414403201c880c001803010003190251203006890810035102c41d0340c0c1c440c07001c0b50300d00e0640d0b014500e140081480e680520130b017581d450103154821480c0d411424000c00c2040c0b1151118440c80400b0700c208611641104c002c021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 139304883 1250 139303633 139303651
    0x60b040302180c0c07090e0d1d10020106080111121b040902070204021605160b07050607110319050a140c0d080c13030b01140901030507090b04020403080a1205091203 73
    0x2c20384481000e440c150061004440042c0252100411030504030f030b12242e605001d55045031190300921000f41c440b980c1c241c1c42c03803480e0a02a0104001c81c1841406034150511510000030301d9941c8000c50f42c00c40319590f0307800708103a90004001c5801f806d03000402d42c10600f9034804400c3c01400b07211203021485648141d50b1a560040307035040c155a1941e056030f8120384030041107100040d6074034040b46c59001c020586084408113002c00710b44c2e41448810740310a10392110081207241c461000550b844800c0c4148003000e84000c01021f1000441c0c00c4151480d000e00d42c132041c2e04d4540c81440030342190180c0d01c00780d0005106110668181400041c0c40d0a441283c0c2812071241c0c40b5015604010300c1240400807960100340070000820443e000320364101c40c00040e00303044171202c410411001c004207101c09096680041001c1c4820a55503015218480005200510b45983d079692034007950066045d08021400d0040c9202c8102d0050048603131202a000180c42030340390280a030b40d4640009000044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 139306133 1250 139304883 139304929
    0x11409060420060a0e1507030806040e1606080103110d0f060504020109051503190c080a0b180403050306030d110703151107080a180608040201080405010618060801060b040302 77
    0x180c01c0c481904006980b5070250002d40d48030140c001c040c100840c00b464144c00b8100c0c00c0b9116400711101429642c0300707685540d031310701c0544400c0201302c060041c014140c07840e03005201000d08a0f03c0c01980c80d100506071603c03400600c0d80740d4100040c983d50101521400340b28501e0801c000140511001c01d105580138030300040c2034880b400100c42c0c0004540062f5004541d0080c0420300c0c000300c02c080e41c400ea804407914080000d001050348165106210454041189400841c074035600c1c0f50004500d5001c058400100008405001d00008401359005d80c01300b02c000040c80400d04050000307511400b000d04001540b501c69034481507507441240320140140b07803c03141c120035440d115002032546003a0709148540b41d500606003220705a0000c1030550216070846001c001071915042e4030021105070b0344070390480c0e9580703400540d407200b00100112015540c0305004624200041e00c003080d1030981d900700140c4c1c2410202014215401c5030095609500244410401603a6800c8060501164819810 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 139307383 1250 139306133 139306163
    0x1c03090c050d0c08100204090b0a030201200a1505040605060f030304061d040207032c090403080402030109050706090602070519060f121107060b0f0a0b030c040801110a020114090604 80
    0x2620340e07811604007010790300407036045e542c08170180c2e0050000c3d141da00004100300d220450410080701c0365444000c0c04030740440c1d80d1000c0c60015030344500038801000c09545007965a40e42d0724418030000241c05c020f0681c2d800a000a00889214265109a042e11900503001c0f003500043ea980c01944604820044bc59440010008491a90040012005d8815512030b10240341c040c22201940c840e00b50f0f800c410103040c4010041c840c03440b4220710000b5100c072580d80c41760b44044405400007002070343c00d5903c032403004001600c108441c20040105079255801c9600340303100242403002c15400f01e44241084060352502c00802c0000404550365800e041a5221890f801900c42410078142c0300405d504d00003501c010404641d004110f910702c204410480d43c854034040020900c2100d4400e900018141e400784124618040115089001d000c94207007000c0d41e0b00e0680d802d49620034034000400300b010034142c0c001074090051801e040d05188400d5800c0c501054580c1d590780307000f00042c01411440d148a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 139308633 1250 139307383 139307393
    0x1c06020a020a05030d0e0d080705070206070c050618100509010503010509180303010303030f0b01050f03040f08040503071202133c0608030702120f210f0403051c03090c050d 76
    0x241c0c82155201d0f041c1c81c0c50b0301110203013000502a0280d4014280a4220a09442485528810702c201c505844403801d090f525000e00c40d8980010408a41c401d039801c00106040c0e543c00d000c2d241d08081000100d01c045040070034006040405920b2400b4443c00703000c81c044903070b00201681d05654080d42d400c00305a403101034820000c07500101044540c04000300100030b00da4103410410305c50500903818020080d0340f200440380c51240300003013034410b8820310201d4005161440d64651560007134032800d0070552204002400c2c005d007613101c0d81d01c0d14035590021007142804681e07150240c440c1a010042682840022440d1403110404041600304400b00d036504070038a01c0d040c81c14842c1c10601000866260b8040c80e030b80380d0150205030300c1088201140c44020500040240160601c04c01500070031900902c000c0441096001e540300749c3c9401e2109014042d0f0a0000e00019070003840240140f1402175000e0f90102e006862040c2054107050b85200802c0401c4081c01c211035003902d008160550500f80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 139309883 1250 139308633 139308643
    0x906060504091a0105030a0b0c2a0709060911030106050c01150303111e0d0f0e040c020105330d080706062d0f141c0602181c06020a02 59
    0x1264454505a008000e000c0f040800c8a116680c540000e000c3e03980701c0080507602d40c0702e45001407012440d000000c640c82112000b40c0a0729040e68004032084a41c2e0480142058110800d01c4050b03014580030801c201e8a030088100800764407900b04004500040120110b02c01406108180080000ca046291000b540810114a03100142c5204161a490300030008070200500603a64031071044185041d0f90002c1e021094492a800144810329020000382d90041d40414000c0c01c0c000c40480c0b42d20192140c0c01140d0303100e00141d0002810307280c100014412141b0089a505140c3c1201811081c1d0601c401028060079208036400346d000702c103d2800210900c180c04004203858200440065070742c1c0e0792203500c1080111401090220b038a10448102402403600c50a81d070810502001c100b1150603080d0000044400341959082c075000082c2c3c45e488211080c001c890f1941d00003450340d21302d2004032000d86000350840744400030045444001207a4904035002418484d800030300c081d80d150003081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 139311133 1250 139309883 139309889
    0x20a0803010305060609090c1e030c0402030108030c010617030406180302100c030e01260601020f0d02070801110c0604170c070815090a05060a020703121118060405010909090606 78
    0x1046994035a100d1400320b07201c0d00b0a44e4000e009141c008042001c0c0d80001c140d00d022800d0241000310303103404441c010024021140e4200341c01d40145000e0444644442c002540a0400d2030010360359501140d011508440c400e50149607440b91141013038018000c04001c59045130342c0c0e8a818592012000b1042100c00c025074002503000c0645201d0340011900003200c1c001660082d11204610064240103641251030200d00190440b0b5280720703007421420484640790070407010700c100d07034041400b05221841c00310340c5446400036a118100802c81d013807003405035100560450030750700d007811900d080007661032602420050140000d07240d1410000b0022007600c02145040c41210802a41ca2880305d0703d900c100180c0104206400c000207554210004942d0085603209005000540d101c600032070081d04003e50440403c42581c01080090455024001c02c07001c0c0c1e02c00e8959100f060f413010f110340070000d04525000d10030500013089207a8101104808592400e80c0101c0c400425240c094000d00c0a50 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 139312383 1250 139311133 139311143
    0x50409022503030b09010e0c1e091c0b0a02070b01090509010b100f14070b0613060503060f06030d030606051602010302040e07081e310c0305031905040b0a050a020a 72
    0x881e60400d159041d004402c03404001d43e050400307a42c803410741e821031020448640480c0710b0b0800a1a50000401e80010700d400d00405c1c00d0b034101180b0030006070f03881000a40843d0b104003403200303500c1440003c040050b044107413541c0861414103181e035103148002d414414070802c2d0f60f4450000b10b8990003900401c0005400030005410041400310160004000300c0e81c0340001554980c0180421005904650001e60890000c1c02c66039075403410030549556003520741c1401e9490b00000180d58504100003801031004420b0210545096010705143c106e0301c00e804030800d41411020802c0702c0e0400211048819000c58102d441c1e035103800141c02a03c200c1c1e000b10502003486040280055100b60000c0c080c2e000c42e412a01c81c02054030303e40c1c40c1d448003600c900c14090241c065413504d200e000344c03030410445044c0c1c001c01d8242ca5192140c4645044660080c0e03903d0b0000520000059603402450154004605220f401c103803c054500c01140254119001800000103641880500030084101401d5000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 139313633 1250 139312383 139312447
    0x4031a0702060901051e04081e040f09020705030702061b07060203030402010e0306071d180f0907080303070e010e041d0d020601060201060311040e16120b070c1a0402060d02220b0403020105040902 86
    0x41c0034007027151f030062207840c2440900000120300d1038150b0084400468100000314240003240c1c08010302a440350407507003280c000800001d0429501840340d036004bca11a0040e640ba4901030002510504030740c18060301c40d4201d80104050940c016860a0901d1345a05c48414800c800c1c00219a20805500010955281650400c0481d000c50880c4900c41c940500070f48484640c2e80018559038001542c2c42e00116514012065455100d80f05000ca07040000300007144039004050316074450000408416400d800c002201c00c42150104001d80c0105607900c02000041d15544070135904018961115214980b2801200c103030001c00c1201490303e0b409100c00d01c008550b00e025120b50a445c103102142c040780d40d0707800556010702403400c034507003035800185e6040703050b00c0ea240c0e9452030440240102da001c04144444c012240c010b00c003a00750784111044040001c944003050f0a040042c030341c000c00c0c496100300070510050364000141d03000c4480000d03000d1b88a441c3c40003403e1030f2100d15107241681c5441 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 139314883 1250 139313633 139313677
    0x50f070f031814070503120307080402010513080d0e031609020c0f010c050409060b04050109050d020411030c070203010b0306130807060b0d06020406030e2803030204031a0702060901051e0408 84
    0x12035510603882c1c031002e07004c640c007141d80d91060503291980c0b60b03c20070483e0020b00020b80c0f0030b401440f019501a205141040c5011801e043c01c40030345000d83c0041a050340061022000c0e140c01c1000215650401c50040140e0405050300c42c0295070f1030b000341c20700541c000c1400515440100300a04820300c144000340015a110f0b403008249802611840c41c1d56402e009000490503003050458083e218103a50380c907280d500700b80170702402030889582240c021b41c0d036003c1c0f62a07000b00395014600032000c1c02c2c070342541c40245004260030b41d0091030816200350030080038040101c614044520000790300080654441d05c20b81021030080000d4003425411800c465014802c000541d4000e005440c940d84003041199031241a80d5a9403040310154032260a0804250a034175000e020541d000c94400c0c9009443c4c0b82d02e03580c83c540240e407000302c41601ca5000d4810700080a405100507540a06100006c01440c075042060b080d4040c00001c5414460600f2000700d814004028125015181059100301034418 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 139316133 1250 139314883 139314893
    0x6070b01080114100e07050a1809060815010e0403030e0a0605091023070315050618120d080c03070e1c020306090307080d0f0905071401030b0103050f070f0318 70
    0x6540d050392803c1100d40000d210b08801d5002082562501c900002c41c2d40da80c40c20980341a4004205c4030140012814640010109141c140010f01001003020458504e4801c9203840c0540400b02d80410500c09801440907404181113140d0164246c50b01050350054280454203000084101525507424441048180d800018800c5040c0d9010001080340c0039802c69480c60000ea4054200c000c004454045070509129800c050210351002e1010402e903aa108001211076103d4440301b1402d10926504a50741e00d0840550043c2c12490000760000d1031320000c2c01420420002e1480d4030b5110040081000244551000c0001200c060002d40c1800e0540210390b0000f003c00f142203109200c0c03200002e4440101005076044942c0c056030a508041d001e07a00c40c4082c0a040c00441d03041c83e6201c03044400301e1810840000108841519401d00d00e0707842000500b40c0d280424000e0625080c10280520f180d000c11010703500a01d603142c030000010340c0b858102c015005916011400e4119203011000703001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 139317383 1250 139316133 139316141
    0xb0f0d0605030a0501060f09090209070f031b0e040e191401021201031a250c0f02090f0708090703030903020f0f040e07050f1005040618050a03030e030c012a0206070b010801 76
    0x2ea941c687c04489150740342c0c0960180c0342e1050700207411281d16070104803801c0c041c11400d0800c980710708003c140403058409142103030151036034030400181010b0600d459400c05201e540798036107102e009080103403900f02d03020000500c002d00003407001083d030104c00e00d001401c2d03040d14514404188510303119696400c2c201000400940703002018005000480d0500c0401c04080c0203c2d242085103403900c0c0d401c0642912807540400054400b003402d2200311740181e440040c020300c07621051518840504042e10010171109004200d030401e0750000c0e0091020039000f024003130031254100c8000720040100f201080c45101b031244070540090602c00200e00c03482e80070580c001929415525a0400c0341c25000300280c910000d42a000480c0c0104000c3c0310892085001c030507400846014045002c0e0b480c804200624500d40c025000a50b1041100c41145824410210700781400d181191401d03050600b90860107900881c001526854180044219100d21054410b400e420040251030b569440300418007030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 139318633 1250 139317383 139317389
    0xa090602040e0103141506010513030f050f1009030206040204050403030e0609070612060308030112020121050709140109090b0a0b0f0304030807050f0a0f05091207030b0603070b0f0d0605030a050106 87
    0x11118500d5000441000060030265940718121040b1b03a5444030001551303d076010590400916030130700004000b080c00d00d440a607603d4818402810302100d080700050030407440311001420281081034034404030b64006940350308981c0440f0002442d403560300c0d0640080c410003a00d0481405a01c081040c2001d0100e1000100c48550b04ea64401301060a60142183c0d064003004080c40b8050005200b084442c0d00003120300c41c818104032512051128541426541950105540681720030070060059445200c1800404d6440d070710b142192400400030701000018003401c000d490b580d403008020b65a60030040c0d002008440020395580600b6902c200307450340202c2d010390215581c0340216500902c41c0c0e04845d82201c1c4640260704005030310004a0710350074409444000c000c010700044c00c1994524000c03c42d0000c05100410a051552400003040340006110500c65004884100203030340380101200d441141702c0081d0b0f550f94840c001440300800b1550045900752103100103010401030154801415 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 139319883 1250 139318633 139318643
    0x302181c05100e07170111030a1a010306030203030a2f06011e0807060f0504030206030118050a020315120307140d03050a020403030921120c0308060604030203070e0a090602040e0103 80
    0x54008a000040b05032403442070031900552100741c0801600c1a540002c020240107180040b40c0d18601580200d11a08207079446462560307541d5050007803034070440d50031107100801c1c2001e1005604c0c580010f80c8901400c030710001800881e80040041c000420000c8600800301c0d035881c000d515030156107039030f903060034020025401e000c80c00da2030020444003401c008482c03c00c1d0040c014542402d01c1144c10303032203104e80c1005201e07045c84040010307a5840040c5002e4554982048030714945a0050400c1d1607024201480c814810401e02c91550403c50042c01380c0c41c01507580d0003000074800d1440d4614410050007a00d0b840120140307012011000ca410400c2030040e40d4280130301e0b02c8403200d81c01203210301e02c0020045445a0fa007004114070714850a529150f0410420b9030f1101d8070380340c8065115003803080d900090104109030f020550400c0c0600e402c1201a40c113641806d0440d0b01080d540d60f1503014603804910840c1c001103801c1c0c40c40c3c2043e20400da00a60035901c0d1a910b8022280b807400038001224 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 139321133 1250 139319883 139319893
    0x3010c0c0c080609030a0c0602090603041a1b03061c06090602070506090309010f030506030309151e090d02040b120d0903110306070905041d01060b030109110703050405010302181c05 80
    0x1440000c0011a0f60040d00d0050203940740c1401d0140136584950040012500b00d40c00303200e0103403103960300e4000c0c501c1940101c41414501c040310700c9500200400510b82c1c203182e45221126005884020b0550313a028209650b5028105a050480602051900e4004101d941400b80c82020411302c1d4000c3c5c04a144514211102c07500e540720a04c0d100c2c0a038040c0e150000d25001811003c0034820b8002a400a2028064070b142c1940e000c04543c81307554051200e04187d20005201151950800b42d00b04244108104203041c5811580041d0040a400b1400f911454460440305580e55480e4a80c4101119a00c100c0d0718810030302c04c2c017426100c0544410350b61900940c180c4013050901185a92041900c0e50f5506806814a802c020081c00502000d0101080e00c04150506400921840c070103000c100c03464945942c03402c0c002c101510440506900a940f05115a50010760010162026035000f400d01585643e101c0051980d044000203034036a001d13481980440128000d11101604240201c1c29030b070b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 139322383 1250 139321133 139321139
    0xc0d060e010b0d02030417070c06091a0d05070201023a0b01021e031e031005060a09061d0a09140906061c02040f020a05030114010309020603040305031503010c0c0c 72
    0x4425110034810316040c2c601c20450b0040000c80c43c0d004640c0140b042c0000003c84000f000ca502080c0c00100c8200d88034040c0704004c1c00801d40108c0d00c0401482d4400e43c4203503410b007500901c01c0300c2c003800ca40d846420b03490740d0100700403d000f0b4054400c00031076500e105440100883e840d0006000d40005162060595500c80508414500401030f007030406030000d052441c04401c8420542e05000c22a0800303010912240305503c0e50750f002071040102c40f40300540c0700d052400705400e0402c1c05078030144c441d440030001174501d1504905140220713280c41c2013403015590050702110300c40805860483d4060200c44004c16502d4441e80b22100070240100045001e40d01c049030b09981700b40c141c407115448810040780e4461110402200e000d9244003038000300d05800366190f034006a03003203011640081500400180100340f04a03c034142070040c00d29040c4811041c98020400502c4007600c00b9081140010000d49150204480e100b0040d1015008001c0c0c0022410000c0200d03c01d1201210302508e50b034000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 139323633 1250 139322383 139322399
    0x30908060c0304020d1110030621051e0c06040603020304060c0c02030309040e0f060a1407090b04061407050d05180906060a081f06090512010507020703020f0102070305060c0d06 78
    0x4038400c151079031901c0c0c0b443e02c0310303000c12400c40c81003807088400c000f20a10080d03003a1100b40c0ca410000c07080e62404940b00e4188002d4102c1a0100d02d42c00da40211320700309060200e000000c07101c0c00510b01d8065000020301400d501e40c00c05004812450304440c0001d000249107500d540110702c00c0d40201010061000c503840101c03030041503210041e5041c2c1c0144400e24807480e00b60310446011120f00704030b0711115440107007182007080031500f02540d01d82e90202ca1541008000880c1ea012486180c5001c009040c8081010b5074007031400b500041140e00700040c52103a01c41c030100c40b5056003003800c0740c030030700b400d00001030a0368018015860040c0c0044e011401c641001c1540900590f0700500d450304100c41c080d403c48503d07200030b00808065190040c100460315144400d41c0117040c0c40e81e070350749001b400d04081c0f1006008a00f20b142080c0e1505007000303074203036000c1084010307a9030403540344245c01c05260040349800710382c2c0c002a115000b42c5040c0031659240f10024000890600020300079640d4420003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 139324883 1250 139323633 139323643
    0x15010608061e060a091212080106020619050709122d020306040803060d120306061407051c180b03061203091302030a11071b2312030f0a0c030908 64
    0x2a070300040c889585a055540f030301d80040d00d00311140d40740440c8610313551010003085c0707241620300351800032540c05c070340708100d6010740341601510b498002003c181c02c0407074500400c1c40e1a81d808001c01075481d03020402d0140b155001c140180401481c0152500316418602140200e242400c42056400f034100500c011407520210b00032600100941880e581c0c0d51100d82c0329900007081940c1c001d40e11008800001c1d80f0b00e07042c0c043c640440e500041c2c070a0030702101401100041092801003081841000300042002842001055034642e0300000e048004000b40c3d50020511902c1501440078030001c10100809009984211000c580d043c407112440c102c29904c81c4907440455811405c0360300040c4c2c0350340e0a6001190844464440010076004c841c001c1441c0381c104110413182c058003400340780083c000b045041c2002d03019418082e1058000e40c01c03141c0104241c007107501d00075181c0c442000a00032091040c3c2d90a4032521300d0299440b001c048004080040c0c0070f004038040b40c1c00d1003000c55400c1c00003031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 139326133 1250 139324883 139324909
    0x4181b2609120c0c060712030c0801031110031103010909020a0f0f290a05031503061504090c08150103031e0912060b0a0e09120903060403030506030703051501060806 73
    0x58112000c50b1900d20070341c1d030300103240e0710f8040c072403a007407a40c2c252200c0f401009460301070110048240f01e0903500030306441c000702601c810044044e005101040c000064690f00c40411101d806040488400a0b009090401c44140101c2d0020000085501c0550001d0380d03854030840b0a01c1030309488a00e014004482801020041207052800b40404100c800c2885440b887c2e083c141840f580e079003030705d1840e00c0d80555503540c00110040309100450b2501c126180c8110401c44c05400145810b0662003421942e8144d06032007a51520300700000e110100d41d000000d01030000640e00c03036010003144442000801e100480000b03401d4007060546128be8201e0b048020500ea5031494001c1c40c0c0540c60040b4901100e003a10301d1507940d606484150b452210300b10040c4100b822200e058a031581c0c103142005805007002a2040c810800d07a00c0507a40070880e00e51255060030001507544400004c03d1030107850fa080141140304004203d449a915240001e0403610169519545035a840381402494400c0c62 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 139327383 1250 139326133 139326151
    0xd030f02070b13140f070509010b07050c060307050405041d250308130915060f0509010504170304030f060e070603140604200f09090109050c04181b26 66
    0x64040b032107501c0c05043c035440e1203002d00424000b10800318031440c10445482000c15030b6a2100c8010801404e0140301c0c0d0340180b13424240181000c0350b0751509600c031186120706a205000000006e403030640a4000c0d02d0141c40e02a20070444140d1a101c400d20030302940c001e003005403003991180c0400710503490b040c500e204c2e11a0030091f8058915596950301d82c0059280003050740400a020903040401d1242e1441e5402c0c074880c6c18050f61805a010f000f02c003039a41000200441040410001d0760008121011520102d55200021040780390041c294010f980000304851003980641c0300b0703c440d50304405c05090910b4140d0b0900c41d500c7d00300303030212406101680c00416401c000124607107032a5002e03070903285a00c501c0044030000505000810360040c0040d41583c8004600e040301c60900355002070152840c0c0b54200054100440c0d10215400b5901c0f0b050f46501040c0010200e106664202c41083c184205030b11070f40084c03040001e000104401b40064162031060b90b0300764145125036205000714440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 139328633 1250 139327383 139327403
    0x31804060f06030c120905242802130605070c0806010e010905040302010e06100e0c09030712080708070b0411010c080904020c01140a15060815010815040e0d030f0207 73
    0x402c160080c0400c51303400810700422a5038940c8803040c50003a907003414442c1c8068510422960081200079400005503c1403c00000400405000c6605140c1003080c08060000c8010a1604224084c0c40340710f15041c0c500c0b0b24010005155034109002d405131503c203a1038400c4054030b41030361940c0e80c0000d208844c100c00d84800108094640f070b901003504203010344000b042040030560381c54640b42058443d103424042d07911040002c0a81100c42541004070507040303034075040c40100040d5555481c1d0140c8403040c00340c05500001c1020900c112224158059a07140d01d60754541050300d50301004986c240d81c22650015409607647c032402c42050a0b583c80981641021016820f000003500060540380d501c3d07584132914264811800c038107500c01c0302c2001e8041081e00c4c0c11180c5030304c004644d0340300c00c040c4a09101407000041c04545440c503000400e01c0e14021075501c10744e80b01c66040d494444150058076044550f0064940450138035001200303078074280202141940c1034400c80c4a140400390601000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 139329883 1250 139328633 139328639
    0x9050c01030203150306010608090d080103020a060807110106060309031103090904060f0b090a09020a080a0b0f070e0405070c0b0112030509060703090e09010f0c090e1603020d0e031804060f 83
    0x950107913800155a42e04281005508000300386440000c1c0c0080e004521004100402d14500300182c108a0040b4a44034455514603808603402c500c071070003080700384210500080c0c0501d125002c240b42801d4180001e2200d42d95500014000740254a0b05600282e40a8482c2e8038102e0000111241800081c05150351a0f032151604001400001104248242c41e500003030400d56a128403540a0701c0c07030880008642d50745104120811401d940030030400e41040500f030000c21002c1c2d09165014101d101c1e005001d681c2c820041300c203a641d581d080d83e8414900740c24480c1c03250340000c00020180c46154443c980d0f980710209682d02031548540200040c504000406084c100480502805840380c18000f5105440c2c940c0941c00680844005009a40d02c00c004d804c04503e5000d502d072400010300703080342d0031414459242c0c03510700b00401108140d22491401250741c4d209078100e030381803418460100010316444100584071352081c42002e00460040c0c09080070ba203401e100744800c41e03c8016140b03021740c1c9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 139331133 1250 139329883 139329887
    0x11a04061d03010e0d210603020109140324070f090b04030305160b0c190305010509220209190501050f03030702280e06090f04020a05220e010501050306070309050c01 73
    0x2208100da09552200f1304111410f2080048000a500359110740c2094007081451880c2c10402002e00420542010410000350b6000020710b81a43c0c01012071051002007840400e04e00040304180e400300f10780100d621101408010400ca0080d03510b591890580942104100c0c0c0300e60050040c1215000100001c100003400350008000300344103448048407000e501d4071000100cac4002c03034440d1541480090301207114503082c0743d01e5848000c1030400308007950501d804201d0b209030080000010100710110860400309002503e1007555000b050484a45490409001c84515045950b03240d1410310001240a02c1c0c0940281c021000103001507040c90100d4003048070a00e4401c201c54401010204070454400810055402920b5000d00d0284103040c40c40600400c868001c1c18209964142010b010050b5182081c803000c8880840f605008101041003800f14210040344400806140906030420284103420150490743e04400350345607030f0703154001a01034520640d001000742d007241c0001c0080e58 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 139332383 1250 139331133 139331177
    0x305060a0b0d140c0a170108070302040509030d0e010c09090501050303030c070804151d031501090203090705030f010c030b030d2307060207030e0310090512071118011a0406 76
    0xc05128004550f0418030403169490400558000c00031880c00281c0d0301500e070300000c41442078010304202221940c074120400381c440c1c103a4003000748103546940208000c05002c1042d03075607400d14003904100d40c0101200041c000e002c0c81030480b001c1940c050001074428094425141201e40c0900958550b503034401c40a103560b0f02400b0129042c90081c04045011007a00c244045140ca5036114800001e04000002d603407032403100700c424840d601034034500c4031012100c50b80d10b045402c81d040240c1c881c0c880184060400e4a580c00407a003610030880f6030800c2c4c20054001c0807072445c01c2d88040180340c4d069020f02d6258044c1c0302c48040410741c207024821031854004034603803558074020001c6043c8001c0e030741c901c0305076444aa0150001810021500c00d0782c902489a81d980b01c0c0c8a001c10404103410f40d40300d0b91144082d4003030300b81d2010045040400d00170003610388020254000c2c02c41c028034520b0410124038400a0040d800e40803240c0c00c0000700641d203142100e058070981d2311520540f0702c66880c3d02c0074074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 139333633 1250 139332383 139332397
    0x150311101e05161a0c091c050304050310020409060b0c280803190501090204060905090a2705010c0302090f0405070c050105010b090f03070302010e24030a0b010806010305060a0b 78
    0x2204000a281103420f101c844a0903500c10305409122440481c807000103000d001d0001c0898110400840c4c2d00d6985040440c1c050b4140164682d41c460214100f441c02c602407540182d405008200c0d102211108540c010403da41e5040400c10502d03880d51070a1201c1e0042d5541d008107580003401000d851086020341000003047c0c1c10203d10300b08a50356600703890341c00030754158140030640e01c2654660a002d00a090248c981d2140440c181890080000c1c16a0420300ca03aa004805000c040341203100a9045400c1c640d074103850a0b174080c080d51a024000c0b4803c15000c7d9055442c01c018011518800d00031200c3c888802003c0304c0102d134031001000010140540001d043c0302c03c0000000c000750081c05500c0c02011085815501c80d0405000e000c500c09000c500f51f4887e801c500e03814001030380c000724402004c0105507540c043c64401c080c010807000120307010400081001104010b07041449402848040743d00780c1e108401071311501d0056080e1441524929800710305d80b0014880b2121440140030a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 139334883 1250 139333633 139333637
    0x20d050705030d02210906040c0b0c010b0d050c01021203010506071101030912020d200a1403040909150b1c11210d1b03020d0e01090801150311101e 65
    0x1a210b05543c03101c040740d0001d01c1400750500340100b1500d40d80400d00d10a540402c201c4003400f55443c02d03a6602e17824410b18001c03c002404007162003075101800750f11032255400301508411300c0c1c07403040c18155641d40c40783d10f805006100348201c05c10201c0d000c00070b5904855028102506100c421b40e1641042c1140141083c1011b6490601d0b6010540f100b82ca0a283e4105402421000d03668600c01070400d480d4045215600070300044100b141d800010701004015003002d03042c034091502004d00e9045100326408003000c582800038007410b100c00f01400704200150031302c0801c19a140101840181118401c1c030003949c01e4101c08120101b44c02041c026000c103001855156904120303249007281030311041c0c40d0165584101d100500c05c640008543d02403d90500b00941c048a90b5030740256030f001e40f442103d080292509a4180710303401a0456000380c850613000b40f142514010001840704641e01c0159550b4a800032240ca880c2000c1003800c03000b41c4190388208055101c8a03511300c0c122200c0b8101d2003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 139336133 1250 139334883 139334887
    0xe0c0307150e010311072010050a0c0818130e010c090b0a03050402032a030708060c0304031d040c051305060f0a08271b0102011a09100905190e03040501020d05070503 73
    0x40003411f0920386400c2c4000b0f604408075420620400c0c0216581c42080507000e22904121040495801090510799160f000e06019524500ca00706100d900c050308400035003080407000d030420032440507001742403407000340802000021002d001c03c0fa0340e81c1d40d501c560a8a088104244418070744203400c20b5a1280c0090121642605144480700001048a00d40c00e42c0d06407640e480c00141c5000c0c131a010081041c00700506c200d0030902d200c0d0010f48005000101400f030000c034803800d03030002c4070220404010002c00030000c0700a040400382c803a50141c408054080c80c281004503403481c1200c150b8100b80e03071844040d81041c00404054a40003070142400c480591020340d00c943c03000c50104402c066101d844060003041c0e0281079124040d480402d0040d05590401c028052001045140b0201002040f82ca40e2a262135400682c09107042e00d80000b4006410001000030608944401381d80405030418100900d18071001c1164480c022405404d0058000c03400d68010103204901911340d035401001668 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 139337383 1250 139336133 139336147
    0x8130b0106032004090603030908241005041401080d0c03050406050d020403050f250305120a11060f060a05091b090604090f0b120109020102060a0513060e0c0307150e010311 76
    0x4030b0f098006078042410162620300510405034801c00d03110042105c45c008284810502200390200e0911840082e0039904000c006000c0b000b08070b110400400340074000300405105c00c208803015075000d01a04060f44905070396440168402c0790100d60680c4c040d624a03081034248441229070341d2000c0c045200c095024007020000c110180324905a014900e030041c840401c00030305a000d00c1403d000b07503042c202c50100c0c080001c210081490150701d006a010030fa603c020000090360790110949405810b8410a1304100e4141d5051a0046c020081144c40a0030f10381e03500200011107808031428034400020703640c43d49070900b003800a000305ca41300610403810192125016011682150540f5008503100d042c44011800c00c1c980c4044000c0c141f9009005c01440c3e5000070b592400068200c00030f0594802c0017410741004000e24811003540004144414103d1403031039a0384841d6195120311901525900142c01c440e810480201f61b0155102c010741e10075410015001401c014050401403035003003043e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 139338633 1250 139337383 139337441
    0x90a0f09020a030c050406050a080709120b09010b0f030703110d0503070b0708160c0f03050c0f0309090f10031e170705010b060408030d0b0303040e010e040308130b010603 75
    0x480581240c8400507262694844001c040c0c41c0c1e40030340d4100b4480704000034090782e640081100c01c00001424160316a03101c00800300e0300303100d050b40104160000e40030100104400c408566014020340e038020b10051865030200000142c519014640c10340c01035604000181d901041c0d1006070b02c000305683c40141540e00da150440d4082402143c1180c0300004121020381c01c403211641280480f8000031890410641c060000000c1c01400f8041c00d03131420390003003014070413003c840e00e10104a065505101c0320074000c0c1d80d02c2d005080b0b042d1107615540f0000b40081c90a4070054800d00c07100300459035042c40d60310340300b800308100300010285108000f00c14002c00c41c0c80c1c82d81d1840009045040f41d5550792404c045003101c0b01850a90b200d00710821017003044040000903a19804401072000034010070301d0700024a10301c141c0e07001c44981e110f2078000084038005041c095100300d000b5105d00c12640e0741c01100b11402003403484000c000c0414600180f201e14441e80c0700b1042c0002130303600b6842a003510350b18 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 139339883 1250 139338633 139338659
    0x409051c2a080415170108030708070b100f0f03111819090602040f060f0807020606130f09050604020a090209060a080903070203061005190b0a05090117040c030c06081b090a 76
    0x810045681c54480401e803002c007010179801005070402440c00c144030365980000b54814502c010f017004c04408082581d1000c03010180000f08122a011030303085aa4801c150072464851106032028a000c245600103030030a041c0c031040d055805804406540e0b21070103000c070704c0481c51406034500d641d250006c0300010110300c01880a42884d801140000749030800084c9802c694001460401c004c407004d000505070005001c0d03030045070844003d0442600038128000500c0c5681d0340c08a12030030000c0d40381c103000e00070075014080c2d4001c0e5000c0c0c03059038039604000103030f03c41d0281254000c18200940032081d4413035a10f0b182c0088846044c2c902d400015000686080c1083e990441444400c2d0010890317407808850107003e4010b0b0700ca00e4036860b80340400740c0c0e409000390303500c0740c1c103002c1c0000d48101d69030b1042c140d0000895451401012505050901c40020f8000d400202c80390f2403004070200b4814052842d076403191450303c140e18007060807144c00010613080f94001d07607006030b0b001801080d2000502c1d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 139341133 1250 139339883 139339919
    0x309300c0304050a060c05070303030c050705010908041707080606041e090b1510080105060706060e01060908070e040f0f050c0301060303180905011d04110409051c2a0804 75
    0x107644450034070702008010025503005006002c99245603200107030002c501d1030301300ca403d414001100540564190b41521031050001c045518298040c0104610900500280d40f20f0496034403504402e904850b54441e00c5006c0c11078564805000a40645025080b11880d41d07050a021003a036248102c0c280309481c2140d5044130003040d0a410011020199000c402030f2242c11030700c00418091000b80908044010302070b0358040ca03400210b0400780301403a0804801030040710240600f541e581d0000615005090049000b02d000d9807c000510300303610380c1480d0160b600800300100d2040c166448011300c0c10615000c9440303004251803140c0991702881211300860217500d4019001140c005510742203500364110403001840d20005201110256010403c550448040c1d04103603140c906140d044915103490b4540d10605180f418810000085400700c10300440360a581e000007511001501d4290182000014030482669000390390007100e80c012864500800d441c900d0a074039110040b5034070046070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 139342383 1250 139341133 139341157
    0x70507140c130902101b0b04050f0712050d0212120402030c041e0b0307080a03050a12060b0a2d050702010905040f090c0b1804020a1b05010516020102030930 69
    0x1030120010f40c00d05400c43c0646640a1806506d420000a01c4008200c2c1c5402c001c2d03c403004c0c12001500b0410b04000c89410f00303250340e0803284c006030740e25442102c0c6941940d04484600607401041681800003030007403906420b036850642040b0b95111454031101c3c00034000d07a4103110303104440640d42c440d40318609030040b0940000450b41c560386001400c4d1480b8050550203540200010049003402050705a0820307032519100e9561000143d040b1600c2610000c1d00390b0042c40c1010009410340c0e040f0050180f0501a00c506046d040107208000d1038400030503080580d025140700404056106d180108811ba1050600c0081e031a01ca07030101c0e085814510040008603030b207513014424041a803451400510b91280c5403417a04414020dc10b1602c42c20b60032150181e0b0300810941c14690086080c0714080000810600d111080350030302a000c3c00e01945c0f480c101484503003250040c58410b0088a03c5000110b008000c41000d900d030b45005144030403840c0260500c5c200f0030426101000307005000d054609 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 139343633 1250 139342383 139342391
    0x150e0a060e0a051f181d0a0506030102030f040212070f0b090a0f0305030f13080d12050a060321021504030201140601081510140c03041d070507140c13 66
    0x85014012800d44030340045200d1400c0100d100c02508510301104003058445c90142c962482a40251004070110f0700003071564503100e00c032400e801e41100001031090f06100d0081c0300076140c5200b418200d01c070548096040c550030a0000d000341c20058070141920301c814048903d201c1c0d884d0240c0718207441d0303900140003e03880005c62290519242e000750000d4807403803c80303504e124616030700d0550780d22401e0b50a500004001c01c601229858540b15000288003000a47d01710380c201c4000144038003000303818107520910b04404503070b4600c7c080c031905003a070754407205030400404400f0751030b1904400500c4000843c4100300080b20014100241580204c0c82078001140f80001d0042040b064403000348994100b1020008100d2851f2044510f261010400d0b2528440300c030000000b11451045c90307803101d0140f4030001c1c00c5007081e440040100120741a002c002a50007000d039400039000c2c1d5058135514001070041c010078000c2000180200140c04040c411110303142549004203505202220035000d016580b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 139344883 1250 139343633 139343657
    0x9100f05090f010204061d06072909030a170604020706060303050c0607031814010b0415050a0e070206040201080703090b040c06030e0105010302030d12090c03050609101401150e0a06 80
    0x410441c030b6046940b80740c000d6003030500f01000102460941e18540d0307030866000c2c440401030b8994400300c0740600d40000707207c1030320b109510081581c5c400e40d044c418030800392034000541c04100401910720181c1c190b502c058400440365420241d04102030100d6900c607608001c1a40086c24910884c402140709440341e40e1a20380c044405410008000d20700301c00d05003082d0303000321480d1000540d442020751040b1207c5510400c3c9414600400c00c40740340c15001032805010281200340b0614040450700120380014145468103406050400152101400340e030002000c03500540c061441641c0c46004c901e00043d00b800e1030745451100319003e45040c2c40700040008103110310f0f40e0602500b1310003441c08c0000d000652455001c40e03130301d2040d0200c49041040c074038141c0c502d042485d085a8a09a00004401c0350396881b4146161a00c03010ba441400d1841071114001140307806010304c265010f001c20140c0141c3e840c10540300c01704100410240c0401c82c00e452540640d586009a0501511040d81c6e18070030301d10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 139346133 1250 139344883 139344901
    0x9070302130608120a052713140103030c1e080d180f0303020a050f0315010e030610140111010e0a03080c0f0301090b0406030503040902030406110301030b0403030509100f05 76
    0x1800303210707aa6115051a00c1845002000500150001801c1050a503540030034207046840d03000301c803a50000700070708040952240e01841180d220188040b1040c0c060041c4195940040300c4018030990041d4403910b004001003030280601800c001d0107000d01d00344040d50318100c00f984419a80d4212030204000c2540d0365803003809c0c4101180d1240540844044000707540340d10881e14a0700e10010704044d00000c0003004d41c2c0c0726030203442c0c0000c40d584074952a0300300003442070301010300124428001120f2403154400c900d0300082c101d01075141c441c07144a4030381c100050b80001030345019025050195114002351914130074424988200b1200002d0809407046140c0101604005403200d2480c0009100070310460054600300c3e030440b0008e2000041d6002c0750008607000d400280d2000e4524040030400040001180d0015841113100d0b01d002c001080c0c40190001e09c600003800040c3c00c10300007900181c0081c0c06540a250040c010104550740c28500c40352460545400e071402d801615125002e00820b21 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 139347383 1250 139346133 139346149
    0x20d06020d11070f0f14010e210406050a1b020603041103010f060510080405010902030601150e010c030c02010c0c05040f0c02070e090322030206030f0708071404060e0406080609070302 81
    0x7800640b406103000710940f159100501100750250003051880d120f001000005440321100d01e120710000d0118580a603203540d1221b00594200d42c118040404905125492104031415141540c680f00d05051156004441e0310510b0081c0c4c3c009004840f0045004d82d64140c059071086100308014401d0b0700000081c103094600403c0d031481501c4c10a5018070a81c0d5492440440040207898440302c540d40c0c40c18010301421507080040d4040c051030f4004200c0304041e80102c480c2200d00d848101c2c40900d800300444040c40c91102c040d000546181c044070041d80b0034200f07101d08078064a00284c000752281c00003030841d602030384102d904599455010b110300360184001402800c0c885d4140708103190941c282d540364810003c03100a0648004c1882100d40318a0b84244090368014015684034070f00890552601101510040041407811001645132071007000d42d40b00d00d01da00c40d00a0308040ca0040b0666800e410304404a6005881c0c80b4049031500301000711611510f42c12000701082461801440046 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 139348633 1250 139347383 139347401
    0x11190201051501210c0201230402010f0309060b040e0102040609140609040b1804051e061e1b0f03041101180b0d09120906200c0d0201020a020d06020d 66
    0x259050108004071420036105040e01ea203402c1c00c24600d004071081c1034a030b110018141d000070061902e1042207840354158419210820750801c20a003505d0030100c45e80b000007085400a0000d02c950745e551020a00c0382e000640743e18483e44020130b00a03080c0f00028180c4100c03409102d421703035000c0b40030406198849036000c0140b107045903806000400d240800c040b44100041140503980380c480111164a81d41c50a4050388121400742e411400c02d4a01592501c44502c3d5400c0e0915490120030202c102c0401c0351401062041c41404140d1001c212980112000514542003003070b41c84004a09082e407503005003400d0b280e400f081e82c1c0d2850507240890088102c00a42410880c50f1100d80c0d02e4500911070202c243c81c4101c241d00c4c0c4503034519919002502c0000802810300c69054980d580240d005040401500c0484d1148400c004004540d0400c009040e0386c0410543c1c0451001e51081c02c0c05013071514954010700c16203147d5803c43e00480c1850502c1c00045410b00d500007110342d80341d85c8511800c406 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 139349883 1250 139348633 139348637
    0xd02060f0c090f04090c1206060515030702190507051c0506010902160609020301150e0406060902090315040804050a080d1103040e070807170a0c030f0c0f050703020708011119 77
    0xc002808001c20100036400c2a40f502542e510000d04c000d2082c04003401004103000742050302440110714203074015004511a0700d000e40b11700c045985408401c1010f991003010030b58000c0502515420b0140d00e000c03ea8013007502c80b4010f88401044c81d803145500e18505580708008600c0300c0a192601600d8034405038000704200d88107011200e00f0328a4080b0500c1513903006000030503104a0740c0002401040300a0322014102c000c5540000c9080343c1d580d0382442580100c1c402c0100d1076540710040c00f40e105448500307a254000e150b00488044e16004a290041c2c00350381100c4c2070603110000300b1301e08074480e0042c907480e81c4050074002140b98491480142c40010304091410540341c61401d46031804040d1090082c00605030000d07220500c40ca1003201404c050040d44051343c244101003400410b2901b00100c0003c0c10158801c00b15442c03401403614500320b541e030341008041d0740d40085a080e080075400f00c00f103001d0b40500103403042d024003685140c00d00210300782e07913030744184091080700c0c825502060003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 139351133 1250 139349883 139349887
    0xc0e09090625091511060702060c09151c05090706020705180703021306090501030b011d01030e1905011401051905010f0c0803010f06091205060a09140d02060f0c 71
    0x10740244100399400e00416001c2030031030100030b4a003007610381d250a82c0202001641060310250683d5001c0d206000010100c000d881c0c0a48540800304d1321004211078205441c034080001d071105003404585095003005000f289820003510034605034015540c4182c0313000b90b13600d4200784400d0740014000c41c0018640c0e4001004820714220202d035200001440f07800d075a007403020000b10150300a40499610321a48450140d6107500c41001408607441c40c020640001d1a20f03d80c81c0b007070350150001c18000a074120601507001c480c2e40044004c1c01c00f41e8180c031001d00441ba04a02e0342c0c28144242d40000b4850300003c42c0b0b030400c40d0b12b22030000c0c4050b40030b40c3c400d02c100b500b00c0c5010b40120003008142e42d02031810f520002880401aa1264089240100300100c00400011794820200c2001d0039a9210382c1c8940000e5500e42c260015440c2c01c200240494128901040c05d0340c00c690301c030601180c481c120061000000d016090700b001d0b200c80d40e95015030490401c0151140111103416402148011074038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 139352383 1250 139351133 139351141
    0x140d0b040201081003020d03030f0f06060e090903070f0f02040f02070201082a07050c0405010f030c0902031e0703090201080901050112030804020d12020f010b10140702040b040c0e090906 82
    0x6444500180010341404003080101e02e00c3c1e4080d20500002d1500940070402c09040e40c0740041c01050ba41c0c070042c000c1c91602c03141c81c05481d014002d5000326141c5685402c2c010400b14100580b039800980380a1680c8003c10070f80000a09136103c04140500640d03004d60080154010b20080d101e14940500801e07104010400060ba080300400760030615140c210010100d00e40c8840a80c442000c00d040b503481e4012401c04100311001802848441065406101d682d90320200e003c4c94054a001c0180004040070003404280b0340d542c090350b440406405050407807850b0111180710032000b070321440c000030380b282c50b0b041c00d65810080340c0390480d0f402802000755600d044800e2100c4040c070b101c01000c02c040b0f600031605640d1404560070986030000c0444041400c6414041d546140d020b070000c80c154244107680180b0b260519079040750400340c0d20362000322080b80700c22485641c40000708a9016548030504442511540300c0c08803400d0b0360381c8681d6008031001c01040584000201004a00e0740000100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 139353633 1250 139352383 139352393
    0x5070b0705160f0f0516030203071d04080d110d06050102010b1203040b090d020604060c120302030403170403051e0306120a0c0510052502041406090408090103020f13140d 75
    0x204040350b000054442c0b0003070f1502d030803044c40b110514040d00c603210311508a10300c8901015004101c0748210105e03a0100e03551040056041c0c0c542c2084034000c1e900c200000c000c125103000400383c1500301000041c1c1e658034280f10580c1500302600c408440f0765200001e10107540c0900c40c002c81c000044a00503005052030508658038811400713000991100802c1c51a210b407101042c9884995000340f60302d4071181c80d00b2009082c0940c07118150360060303d1208005042b1302901c00c8a010f603070103a88804040c06121080d402c0490058030481c2041006c109101d244255410482140040302c2d03600d6035207041442c200007540001d5130f90750700d640e0081404500024024140c15044582c290795034622140301041c1540c00f03000d5500520400b40d80c66090562948003003020401444c070842d801c10440c014403140c094010700c21600160088070305004a800726a498025010144d014540589400304415191b00d198100e0034030362100c001040d00030721139a0301400c00c0a4048000341d84050044060703480d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 139354883 1250 139353633 139353667
    0x8100b0915040b0105040b0304150507050a020601050120011a1201020928050d0b010303120203010501021e160608040c060203030603100209060d2a080108070306021309050705070b0705 81
    0x300700c0c03289645040c41ca01a074002c0d0240d5005003130300c010142d10781c0b0707080c1011940744e040080c940000500e030000081086008500792035030b44185900401484c2c0c00c010055502d003450140507150765000c00980d0262480900420b03c044c058490324903d1803460b44184a15811030303c8250b12140d005205c4140145c840135030002d0040d021140103084540c0b0035441504103042c4d900030a41100c04841c055052003203150786941221701c02c0c4e480564400309200d1345004c9010a024442c0142c20418040024607030030310f03030640e51301c82c0d030b009681c130456400001e1101502075510000108200c00d04110522103c03022240c02894203001451440c40d02800082d00c4044401c80c0300d41042d800716400c1c1039a29020300303850b140c0814410400c8104920340030034024081022034449001c00604485c8241072103890742d14102c07140c2c80000c1815608503a03400780a90007103e4483d60406640d80c0c0011105202d00505001c0d0481741c07070360b41d074502e040d041265032010020300b0071082c8401004051501070486007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 139356133 1250 139354883 139354921
    0xe0309010c111311040e100302060901050307030e0708150903070506070c03170709090b030c030d03090501090c060503040c150509061b07030305031512030702010e0d08030108100b09 80
    0x1010900e090b59802c006580c950f03440c1c031034003030151820b03d0409a92a41c00000d00c141d4810080400a030f569000c5000e89103411404025002a007d000c00340065000b1800703190010040e040105011203803c1000d403500d4400e5002c91410b40c40011b024820f4030801012036040680c0202451a0482d1030f1501c1d0380e19a00544400c0410200644803c14540304900f42103824841240003407441c20300309001021480c00d4000c600c031080c580140c580312807034001240c180c842c10240141041110f9000250010a140c29098030301c0e540340d681320030009950442140180070a500e13260380302d0a090612001a04c0b09410031001817600c030250350300c00c0303030428207846400701c040785d130305a80c0e81761f4112001c40b40044250140b01403003460800320400d600b002c060b40c411540c140b11054208100020070080c4413110f030074030105030810003401016500c684084011414081e00c62442036a00b95110400b940c07007644508101d820001201c441064580210326501c079040781d26031445d01f4040c2803151a00140b00d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 139357383 1250 139356133 139356143
    0x403020d150f0203161706010807090b03040b01080607021603150608061501020c04060620030714010b0f012a0c0b0d0e0f0106180e070e0a0f0e0309010c 67
    0x4020352080002850510410380c2550409014007800100000040c0d042a03400940c00c0700c100d0311152040d4411401030240c400612048a8151100310040d100550041e06000401110f0b01e404903079810414015401540b04803203080f0341e03600d0808136904100c0702030f180004540000800c295003190802c0303400c0a8079040400320540300c00c00141c0c4170041c40664044242d42c02140200f241c64a5500003055a41a00b030302900c80c500f110108200858020340140303004200400e420301102d01101798960340d14000003085030300d40f40a0b83c9501d403009406c091141d8060b134444035a01001d08249c0000e074284102030800c442c90728101500c0c159140e440141082c10044201c0c90f0030180020a401000140300300fa07141d50340c07200c2d00b400007005440d0402c4192030512884c203030300804040511802c02218105040d05018003042d40510000c1d2088100906880c812080c012030035010b25140e26000d40d081315000103080080300365401c140c0d81d5006008005400500c40d9400a9801403001700c00c507130b800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 139358633 1250 139357383 139357399
    0xb0f010f09020c0114070810050406080d03021b060c0d060b0304020a050d02010306091b0818070b07080f131d0103020306160201150b121302010c0803060303070f05030a23040302 78
    0x2560a00411082c080308600c604d05d54180039000d6003080203d806811800b540c807200300e40700d00911064800910604000784c0c010401810741d50700c00e602a04800034440c400350b584003504501c0501d0804156000725a55000094100582005200b400002c062030041c5900f1072510f50001484c491a80c1b003001c4c0607944d5017442504581c80781d032041c4082c0a88400c1084003041d00c0c00c132a2600703458202260040754002011a10b8290170681c001100d650380c0f0020420320b4104032408066402c02681100c0e6140c040c02084141c081d2603026000380750340c41d2845540e8030318020a91183c075000e035808045c084001c4006002584000c110190b10207070b945a40801c002d25084101e005007018100720f91490074080f004600d231003464001b0185003803180742e1030045450318007040300707010000c900003400f0134020070380440060510400307164800c3d8020152405c100c0b20343c03905980d00c4002101140c06400018486e10036a0b000045411000029031105410000300c8000011a2040e4000030f03205000c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 139359883 1250 139358633 139358647
    0x31821020d11100201020d0b060403050c0f01051306030221070e04020306030304180b010206010503060f0103021005120405010e011107030e0f0a0302100c0b130203030304030f11030a0c0b0f010f0902 87
    0x24610b482c03120028052600501c4041d00c000d000b500028070740c0548a0509000d01004c0c5000d13000c0d60183da4001000d000341d1030080041010241d00900418184401446406a2105034140500041440c0d490250350b901d8200c0010407070707041c4513401c0300b100c0d610700b800c1c0a01150b0046110f0f00001003940d005076030f5184c65002a155000b1a4004000080c071081800050b000a811400e040d0900f82c00310341c1c850b43c07110201074072810226042e811500c00a401000580703007045200c1d0002a0600704149041320b49002591001400c81c0e080d20729a444800100741d0351024410004461039000b00c041c280103280d540242231541824405226603a00c18284c046aa03540c0034510086030b00602c40e1007403001c07810b000360030901d4003441581d402c254200010300008510008490340c5034020051881d40e59195802c0d5144086030801c141001003011108095500800080a040d5281e807100c1404524500d050320181e0b1000749100310480200004000240b40e0401107015500160405600c40314 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 139361133 1250 139359883 139359893
    0x504110a140d0f0f060806091b0a03020a0b0a180501050a200a0b15010302030408070303180203032a0304050a0308070516030c091b080703110702030109031821020d 72
    0x50300c0a00c042e951800a081c555200c680d4404640324126000034815140e48444c510388400c0e0440f01c00c0d05581082502c1c011803411000c894103c01d0004001000301c1d80c80380c0118442001d01d030045440d000d0b00080005241d6003203843c00d01141000d9005550700e41c100000200036001d00a00e0a00344041504d03500068036a0000345030001e14450704461010f01581000c55846000341d410301c069280000002906521900807284115000408103103071002e035540071801442c1d400c4440790f000c0b0701a850080180cbd02400200741c10b20090a1102e440c04403206100e10143c44060701e070540d94420041040746445510409003243d4100317800c1074032007280e0f003030860a041440c502c01c200180c0c150400700400115101900a940e04a101001703490f200307201e500b25040c5081c0c21800443d040074000345800c0e100742c01801c11009803032a00781c02d240c0a136000c682560700381c15085005c168100344840003d200205120000c1019040b908100701c848084512580310003c0c000e40075004183c05c0f1740a002d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 139362383 1250 139361133 139361137
    0x50904092a1202031b061209030309010b0f0918120403081315080c1c14070e0a24050f0a1101060b1806180a0e010602070504110a14 58
    0x15401a1a4050400d5503003901c1080792210008034410024100000c200c09035440030340b1040660280007000030a1040c1103680382c401c900c650743c59005508025000c122900c0100881c003038140c220086450342040c1c0b210320700313654031590345602038428420b2041c003d035200928207800510b4007003810803d03042c1403501e50920800e0710400300403010010b800004c01207400700034094411715000c000c00780c9440d00078103100311140500301800110800c0110301d060741c0080041c9840003103080c1d02030906008460040c155100005d42d00c035811034100070001010b4104201d031520b1030b0116401e08001e0b0400d44034210403c59105600c4803110440030b4003424501070310881c0d041d410016003c1e0346800c0409401424a1400803660341c05500f010400108a8450810345607841104111092044081c1c2d0a00500d60841e000d00d08408100c882e0200349070710742043c04406841d030194038a00c05d6060001c080c3c9080990b6020300d01440c0707032514504207040300c02d0569407170f05001c0c034000701c440c04014a888068 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 139363633 1250 139362383 139362401
    0x604030f02010e100507020306070e1e13090b012103140304050c0a121401050601050d0209150705062a04090c020705130606020f0c010507080d150902030402030c10090501050904 78
    0x59141130a165100d90060043c16000d482103044800941d00d541d4100d031080c4e000d40c1002c2e00144442c043c8150a104031130b2002803c40d0180c4056032403030030700702001d00f503500c250380a4802030724441c0140b0140890b42201c5184482441c0400c4140185640c01849091900c00e004024a8044045800c22605111514a080000305580755440d110221f42c80041e544000440d50041070f074803140400a03043c09000d1007582e050716550f06019440e00032070082c4d8000c41c6500d80c8a00701810340e040d0f036001d01001d80101d6001c0c10080c0260300e01004010a440c1c01c0e807002180643d003140100144804410454040c0c800d80c0c0804078103030604000c140d1a0504507004035a2044c8000180b01c00c0c4642903024104840043e42200c00c080100040251288000d003080c070b0000da0200142c001059000c802090b0103500c1c8007000486110301150809a44450380015241540000034403083d33180411030b04a00d0741e4102c985842c40ba40c00c0344003034030b0ba04442c031039281401b6020a41c0b210781e030380f150702400310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 139364883 1250 139363633 139363639
    0x10303020c090a0b06030103080306040e0106030b0c070501140a020a17040f02040e030c011b020735100207051005070e101d0a15080f09060a020315030319030506040b0604030f02010e 80
    0x200c0d612440c02740701c03541040711403600032481d00400ea60141d205002d00b20440c0c1e0418400700050f00c42540794006540a10300030764456489121400e46007241d02c4103180300b034102d48001601c5080916004004c1480c052032003400c0d240500501020a1011421095055044070002240c0d000200e005056006682c0c2031045d40d40303448004000c2c242c1c46a1488040340503a0700f520b0015440d50925a02d40d81441e400800d04001000304440b991907103440303403e0800b040002c81e81400d800700c031030000760382c03050b0300c11540780d040807060310400802401010b0708484107007480a40440204007248a20385c2c0014820104091604030812096060680e40901007020f007458042c140c07a0258283d100680d20090400116a04c0028100140d508405d6000345400c002411032520352134981c2c0c019410240600602105001c0441180d507000c000501003040f90a8000300e03d2060301d2005011100700030412801035040038444545030b079403901102c0030b895121981c51080c1c6101c2c001214880c0d101c00005070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 139366133 1250 139364883 139364887
    0x3040b090a0b16020405060d03080a0c0207080f0106080616020a0201080402060d0906020415050a0203070303150b0a0e032b0c140303071d030d09051324080f06010303020c090a0b06 79
    0x2090f800c09410400001d009030b40034445034440d0400d0001c6c075101010b0141c00691440c0c04180c408000740c1014030300c0d540a1049985003a1191945414041801a00c1020303a640d2981080b40640074031510b80c0c45050000c940c05400100c00019444001643c0024104141c0000107011540d0b04002d0b00c0001240b0a002c100d6401c0c90715221000350302030b025018114080c062040041c5100b0411a01c0c0b07440c4541c061810407210780e6083d070240c03241c02022280001c807001c0204641c4008009000002c0300b40c0e48181e00140403c2c00e15003028a140d101c4403007942088032502410700301103a0800754101303501d0102d49039016410000c0c0120014181442c06000000502c0904c582c02504124105100315501da010101c0740d08160303a640817a10103001080c0306c01420400b91407c0c003a80c01c449601e105020076188246a030200c2041b510300c5a500e0420040d15040c03200701d00802c22206800100c0005010950550310040c0d034500085080381e103c0c92030100060301e004010307040100c4d80d420190000d0307 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 139367383 1250 139366133 139366147
    0x412021e150a0510030b07020f01090f0b090c0102120d0609020a0201050402010216080d030e010209040504031125091503062f12010501110c0306090607080f0903040b090a0b 76
    0x7501d8810301c0080844640207035000c254810101e00c91140030701c40d103d041c004118515034511098000081018042d0700641c00c01c100307100020f0190f00240c510441000c80319005074a05103a0441e0054100c1095502c0179007022403998001424140000080841d29103991a107045032025000075041100040e001080b284401501504540c2c0214400d809641c10143c00b6a0642c4010159225100741980440b1600d038515000340c0c4008420300301c42c00050f2415200340041400d41d00103450444c0010301e4841c0d905010306041c000d5001080044000b415100f221502903450201c25000d2146030340d0303039014001c48202c0c0c02ea440b038001f50790001c1c05101c84004a240e443d0700d400c0c890001c44401264147c0d08610b05c410344119055820810340c0104140d080800454818003112024001c0344924640c1c0845607030100111480b880003903004001500e05000020181f400181000111407204030522528500c04000d032402d6414501b00e054640c541100010714821607a031010140c1a0001864 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 139368633 1250 139367383 139367443
    0x13090c0b071e26040308030906010509060d02091b09120106090614060313020103020903070b0403140607020a1203020403080c06070f0221030402030c030f0307060b0a0608041202 78
    0x350990360b00485141d5100303207002c89181c1c040546820000c00c1c160040300c0021805034000c40e910002c4244441090606480c0d0780c0385030b05a030050300c1c2a0701c00d5210000400c1140703031030802d10703500c04e0b026180380342442d1859001c12846100030380740f0903110026004086007107503018280d070841040100311160401900701264024070342809071000e218100701c2c1c0032421080304180c103100030f100580700c0303851640d81c4200b4440400303000350300703d041680130401e100540e0303000c20003400581041e0140943d61451071500004221110700c524100390060303010411055004074a1028864001d91000d034030070342c07070b4000300c000b8031a6070401002002d02041c06031614000054142c440c0116885415000c00048416a42d92007520f00300003c41059000c0c2e1100105803030041c541042c400340480f000d484e9103400003401c040f9450301d144595480450b000c414000d460154901c2d624094903803046035418400020100c100040019020405220762060602d00c20481d440c1240c9116007101c51801d000c0c010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 139369883 1250 139368633 139368637
    0x21608072a080d170a05060d080f0904051806010e071107091e06080618030c030d02090a14010507020d080c060f06040c020102190f020f060a02030402041802030c13090c0b 75
    0x1d8070b9464818402c1521032140601980e9100502a000c1d13000c850b96049442d2000d0b0000810242d00310100000c00000190100040c101814651100d2a21418482d09200c00c80f400246201540c404060710b5981412002c50164117403422142e10414a40e64944240c0e003449070040041342a110301000000c988207036912034800341d20020078001e090322010b15814195a610b00408880ea0050070118040ca035000c041442c030b80c000e084c241d0341000412026103095420040010554a800145140740c034a0540510302c00b40400d00244007000f404500004c0c518001c41e00000e000c0c4ca04020888103201c046001d41d441258400111a00b80c90003243c0600f07810b1085d10180e00660078408111b404034010300070b6844200c1600100d00141554040441c0c103141011518020740c0513030308150900c890180300a0384079610222002d641c0f400c2502c14402262011600c440301c0c81200e2145000699001c100344081d07d034100d4505c0103100907040d2180043c0110f502c020031111081d84005050200800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 139371133 1250 139369883 139369889
    0x13121808100b03030c2d030408010b010806061207030203100909060f0507022b09080607022103011503090501110c01090506060a03021023040305100609021608072a 72
    0x2001c1c0b101002110501d662070041403072403020703900815003000e0b645110001c040811044007413500e50403030080d1803060443d403094205100d41c0c0d46400030130303c19581081072550450420741d83c05190000d41c1d0060510044040c00020406800101281d0003040d0071310780c500940740b49081040340242a2400b20000c0c803140c81c0030b212031070529000500203800810030050308140903101d0f503120744041c0c80e4907503807044440c803a01c1407055500002c00c440750100002442400e094000380000c0c0b60307480510b18802c44040c2c40d100f00c24170800c01407090550030f00f2000503141c140d0070301142e002ea41d0325002d4050308501052407038220020619064400054104080103800340054615945a2005104040513140400380d08150003076055001544a06001c5011603005902c045403028031000000380c035072103640191110746c031000d6800d045403407030305c210801070078214002c5284c8108101101e201024650010b455408003103802410702282074440428445603c041001e030001e1440007041d8104540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 139372383 1250 139371133 139371163
    0xa0806060f010504080a06050408070615030c080615010318062f0301030305070f08130e1602010e0d0507030c0507090203101403030304021309020904061b030513121808 74
    0x700a85515402001200d080d20f52000180c04080d2940d1103040151101600440d10070000300300450120f012445040c8040c44500e856014061031401c000050408541059102c2e42001040c06444a80314480c4e020740c0000382000306400300c20b032003800c815140442001e8035550500015192280700c0c0c085203039040703041d840c00f00c200c90070000307a10300c10b07002c2404000d001c80c03001c00464020540031b401104c0b00c036208103526490700e12424181018454580d01c903040862804003030010107250f2840042c1d4400c840d1000700003d120010120342c0d68a0b048c06102d0500c039000940f40c0030302d80f080c28910700c1c154010b0221500c0541d500c61035030003540102c1d021540f0444004021540302244013100c0000b10009000303604607203817502008040111042d04c135103000c2c4d0381c240340001612290780e564803030317801044001204040081e600c00401001042c42c020985004200060304201241900c005500100400c81780c0d50b0210080c5c501401000d194542c41c40440b40000c1d02c0c03074002a0394980502e0070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 139373633 1250 139372383 139372399
    0x7030b07020d171302060d1407030b0603100b0903011d0309010e060c0303060103050c0c100b0108010909031715030304120c0f140909071205010b04140417180a080606 73
    0xb2007421140c00340c001958040d01d844880124030125110048a00d20714002040d040c1b810b0070001d2402d0459001d10580440703c06000c0402480e9a01485000440e20040d11654554a005c0c1c40c149100300c0c8501441104040204801c4000d44007507000c0e100d40800001d61403418900f03045c007180d494000303c8465000500c0007408200e03904040d820344845c070210740c008500355102d040042d409858000c107c9811040c3c180001c01d050501044030211034190040300080e01ca00c40780004082d484140c0210003814103241803880040d5000d49003410340a92400128003684070a440d40c031240800343e00d4a81c1c14071010801040c04040701c220f03804a14401c4844e000340c0c50b9200c841c0c4810b2030a03441860b5464009162071081400d14809142e841100002500d410f50703100d801d111030703c070389000b400d581310782d90380d04800305a090070300c99100d02c501d06d81c481580900c1e10381c4d05c41140310304c4618680c021407804101582019040e840f40091040001c02d18002241c58004080d540d010071286244182c0130 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 139374883 1250 139373633 139373653
    0x1d091014061c120507031e050703030617070b03060301141f081b04090213020d02090301060902041406071403040b0d140403200c060706051b090a0e06030a0507030b0702 74
    0xb407010111503141d002c8460103902071816415101c030b401c80130040e0b090240c51754103503100c030707030002d1180302ca80c421030301c915440f0b01d01814010102c8920b60001c40c0008450240d030b444c400310000b0300c0c03000c80e0070708120303541d50b940c41c00c002c02d025218039800702c130307240f00e050007800354006117881c00c0303005081c910300d6a0070411b64921420f0f954021010070315090340c5140560410130f040c08c2e08440002070001d00f0544503003100412880032607002441406e00c10b540401c40d02410b1a003801140000c0c4001d00055085c0b50800138449441481d44544505c2a04005841070810808100c8140300f0314200c070540e83c807030340d4590031821198042501c00300c0f1185400b280388407041e040400103000f2900f51303481030000c60b40c60729403419038410060072a8a80c81078800d03c2d0066035890004142d00e520984001c50282441b50010018101c04080340310f450105020758042600c0f20f0940404503000f0760300100c5142c8800340130034100030381c500014015000303001c6c0104c140000d2500c11401080d156080340c1c00202 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 139376133 1250 139374883 139374919
    0x6070b0412080a06140907031b0f090603090515040f050601060518030f07091505030601300f08070c05060723070305071823040501151d09101406 64
    0x402070085c9482c03000132010310000c41c24031061656000c1c605e41000124000122450080154910300103400114012400886c46500802000045c9240d0a042c0b1440b08150307600360711442141c0b01c4490482c0500e001906210000140c4030000d0f0308002580c00071358460800400c0c5500c00905a17014440d08030a214460500017510100c0101c02c80c0030780306050404060300080c06180e0002d00081c49440390102e47c0c1d90f010300841b4000d002e01101680070a207840207080304020603055050b5044402a002030119848100340d15402c2d5111694540c0c449540c940f101035a44180c1142c1e80160021842c0010800c650300c0460110800e0700824200d010000185590b92540d4040144181c1110108212920209801c89801001c003100454419059130107904c541d1003894641004035645400d2005002c030a101d500d00d981540800554079a080c41d080140803080c000d00ca4500980c2240000c0c0500d40511903122041c0055005005a01e0040131080c14840300780d403070310b108180c00031450043ca0307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 139377383 1250 139376133 139376141
    0x30302150c07120c330c020709060605091206070507082511090903160303090507030b24060a0905063402120a0c050d0f020405010608091009030206011406070b0412080a 74
    0x10b000d44071802c45074035482c20a480500ba1b080140d105511907144003050060290003035101400041d5603207500d500d110000c202e2101d404001d400e0090300000c0074086c0b1194894101d44c16a43c0040000b0f566000f200040c42c0c2c03803940304c0f880b0389812004040da481040306a440000094074201d804170281d81342d4410b0503403280702e0440c03d5014402403001d8080064001d800c68070007207020740192035a10b07a8a460b8000b00340301c11901003d0204c1407680e91040103c1c0d00d0b402074050b1000740d94107810000181c1015003150f1450040610590001c10385110b9600e0312003001d0510042040c12645460b5100d010400308850098100c0c071605e292922680400c41c00240c1d0310f1502c3e000f01403150281c0c9000140142032101010035500011025403920268869000e5940208015a03401c11245000e0308a0784c2806140340b01201d80505000e510000710380e0008200b4103464040303081140354005200010801c1c8580d6100a0040521404003c144107240704d09000600075602d814140d60f42c1d0b068050300716 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 139378633 1250 139377383 139377443
    0x30f043302101e05070804020307090605090403200f07080d031808160803040c050103050f040203060a0c0c0f060b0a12382707030302150c07120c 64
    0x41c2d10502c1c1411002031540c00c0500c4455810711890003c800d101214010380d0340407176990000c151075000340b00c01c50500304a410000c0441c82400c00c660b0781000c0001e00d102c07401030001380c1040307041558542041c04000d020080801001c0c11203013500010111700703840754601d100b462114042d18191102240c0207019144105207000c05461840a103540e074041d49401044c41c860182c2c2c4041061000124144000c5000d507004d04c00f4140360071718041c001020ba41004140c40780c8120084c040c8030060b00d00003195600041d55a00c00b003071150030240100c0311800314140c05060072040c0c3d40c0c110203104d0660f20072140e003041500c41091045e143c50000f40c0203651000014200c0d045903d80c2c0c502e0111407a51001c15039920007401d00050a10400c0001c540300503142a0103041e0420300418181c071201c640600c18048681c0900b045514580300a921100141068400c040400000403c500c6c1c0ba0401c0703070f20103a8441240c1c206d604000300f0051039041c5098046864901c8400c030440d2500100501180e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 139379883 1250 139378633 139378637
    0x90a020c060103060207060b030718050a02122a0d05090105010509010501050f0310180b040617031e04091d06010603020f0a0f140c010b011205010501140c030f0433 72
    0x39640781d44d41e00802940b2404068403034660b00d212542142c7c0d0140002c0004060765110f60401416140c2030408490f005400b0604441c4100042c01048041d8010031741e000400b61103510025510360400801c6001c05209400b01e4040000d040b043d0715002d5001c14064420000200040c1c1e0701c450520248000078040d4a01203002030054132840b400320b00041d42d00640300c00c4882202c9903a03003000048040c0651103540803d84070700a444035400c00307200e0407000300801002c2d0000c2009503811140c4901c6007440b645c2000c01d0f1214400d0602150030100d5000340a6070008000c803420300d400510084080c0c404a83d4240118000094014400d000380c0341e50a6088640b68a0950140c0c03068408000c0c89030039006001c4c0450310081c20741043c402a101c055007610010902e81d40a400042030700666004243c89a442c1400501c0280d910600380c00c0d5844800d02c101c1d64a00002007654a5401842d615242c061800100031450030318090b2421401c0c1c0b03908803001c452000c0300645414801d400d287d5400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 139381133 1250 139379883 139379893
    0x1060f03061409040210050c0106060c02040e0d120b0303040b0f044e0f0b1f1802071509110a06051806030a110705011406030607080601120e010c0905090a020c 70
    0x5440e0088610024003101c1c2031051901c14010901401e591155002c40041f5190007401c0cc10341c1030500910044188180c040c012982500c50086c0c0500c880b02400320381c0ca9a12550103086880400c22034001d44071201005441e070020403401c20b41071f80700b40101100000c03600c51200100745069038400f403a001c034501500f070780304503a0300e980c40c4800b048003001e03e005407100401000c948982081241c0c00d00668802c8060301d849146000c50303246801c848050200251800c0181000048079002503020700c100c09a95031105040080024440c403084441031442c010080003041903000030070300c01c91000d48521072802e40c2c9540aa405c0c3c014942002d41c0e00e00281c01450652401d100255072041d2208000610030300015280301986e04005422100c5a56580d00c0030341454103c00c0c510f91000049000344000e00d00080c0c01002541c0180c106030501042125001c801c0c2c0c41600302171705140c49003000b0030420846510007006a043c1d03202700ca020703d81007404195114640e00032985104003d4008003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 139382383 1250 139381133 139381141
    0x519150b1603031e050103061d0a02090403020102071707050c0411030f040201050c0f01020c01050603030a0f0f030902060307030b040515010f0e030703050304060801090605091003081e0301060f03061409 89
    0x45a00901c20422420555681c41c000314608150400f8400b08014001c001065030651901a0440f03aa20800202410080d185000e0500d40001c03641d82c586c2c0e05850180c1c46071541d25003039019008107440142100080d0306455400256034003e003083e907000f075040360301b41040030080c00f044883e071740440424150108005019801b60343d0038150054412700d007181c9442e480c680714500300303100c3c0705031002c50b0303500043c200351710340380034080c007508500110095490700c02c1e0350201500591281a0a00902100250248040c0d009074001200c96401801450b41c924003a08020010040818868030541c42c040104480442c03950008051140c182c42d140c0c900640c082040d039244980844081d07151140c144007000250092000e0001821242c98034030055040188440940f54240c001d14001d62300c0c030040041d0400e820650b0301c1240e400c00f800c04e68031800744459881599060b403410180d448000b00002e074256000b588120240d055507000c00803036458610f80380b030020f50030440b16881400c1c00041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 139383633 1250 139382383 139382407
    0x901030209060d0602130915060819020904140f070314010b07020409020d031809090c0e0c070b040302100f0204081216060908131410120905010519150b 67
    0x21a400410041c208510703c1155603580042c2da00c031424a030031602003044100302424450252258094401138916021030420300001c00c14000146045400ca84280d0401c600740f0b4580e048511201c07001e0800d1054104130081d04802401c241c0700044010070f0385002800541c86445141020341c1503a1701603c480c0d203000800503994112030303802d82c4c0c015601c2c00c0b0400103a4030b100e103800c01140b0035103c00d20482e44440080020300035640c4404802811310220000145002010409a0b202e0700710341d072903648402c44048064050b0400042c0410f074620306020602da0001274403c0405241c81040c001290100301120030f0317004d070f07104142d5107500c2099503402d11b2142c00081c02c40c881c03003402c2c00418060f25807201c0041e55180041651501d10000e50035556200194049024115484010a402001b0408100045122001002080b492520200321001d00340c000d03458050f0000c000b8032150030210f081034666a802d000c0d0f000310794500f280400c0300b0281c7c0345280c81120481200c9070305000d022001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 139384883 1250 139383633 139383649
    0x10e03030d050a06330804140d030b0a050a0b04030204051302030a06050601021204031e02221b02060f01090e0a0c0801050f011a1c0e030a020f0c01080609010302 71
    0x41258540000c1c0000c4545840d94418184210089000803a20b24607200132040782e42c00c592100100c80648000ba08400c0000c6003e038504107010b458964800d59440c1005000510212503d101030700682c4921003200b0350540010203411011620885d0017503541080025603806403141c500c1100e4284030400c058076096000a134071106410840c404908a42c0c0024203195040404527441d5130344409000995904108641d4884406201c1034070306410b6444528032450029401c60301c035403c000c0020115120380d60107400811018641c100c4840e0450103803c0503080050404210850191742d07100d04600c002450b50050b04a2420040c03d40d00f007424800142045580c00c41d51486403510840004940000410042c5030880c00052282805810710794840c170180d110800c5101401c11800041000a003140d0080640c0c02c50a400c10981000050241900a541901d540000715082c400c003a0080780e203d558985403c103980e401c0c0c1e621001074071104c0040d82e1098019809000510040c10110380d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 139386133 1250 139384883 139384907
    0x309060a050609131b0308160605010f050a0b0c01090501020a021b09071e0c050a030c06050603010e0303070f17010b0403030908030a050304060b01050c070f0807080a050606040b010c051501061209030e01 89
    0x82c0c1541e15901c1f0344900c08550310080d41c0c02c1210030715584010038401a4820341d40034100c922140d46407145413100003003030145103008048070004002070403c603854003503100300c040d540d0010080d034541032080d6010b5225454051b080901060100d4070782d0441c500301c0b10b120b04c1000315440750a010441c020005c42c512403000c0005080c0000d00c0d05150100d0020170071a000e180c403981e01c1c0d03c40202da620700b01059601c007a010340e0003a814110512040032010060304c1d80654549460200031802c5407040790b000280400302100d040a0500220f000742005000348162406a160340001b07a0340c46c1d103003c1d030302c0c8250356034000050828408600080e642d504009810a0145006410306c07003e18412420300006501191011021010070409901c06004210003001c07131b5000b03445040b5440c0c40d03803500d90034000d010920482d52140100388581c004c00030701d5203441c0c006084450000c0000310f4102040d50a00845011440c54800d07500c0203203440c0240012030398103a94a04000c07981500644650140314 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 139387383 1250 139386133 139386173
    0x110312282a18030503030105210a030503070306050603041104111305060d11030f01061e0203040302091e13060b0a03030e0d0c05030a0501060513020a0819060504020309060a05060913 80
    0x103100d0710540c100302c0d480201450190010315565403420701007000c4003010080d991806c118808001c1c40301100491090307015034060605503525500e41004400030b2602c2d8100d540d01c00c07401300070b00c0240300c00561898020b2805403030400c03041c030410701c09801900444e240441c400340c0300ea409015500b0010064030f650894a0350124107400c0810607182d030358100701c1e41ca00d043e0198100400805a0000110000d444025035400c24482d0301c070b41c000e482c0d10550101a0080000a000c69243e03020a2088821260b5500b0f841d4498144940c0d1040c1c010200300341a81c00c942032100400c1149071054a0304e0449a0644031303090030944001c03e000100341e80c050f00b5581c0403052a4001569102882001c98852180e800010024102005c00005040001d46070032181d00c140102d61020b504251f0f9283c00102c031100064030220360312824009010913412544c1c000e4008400d1014500c80064654054801c000c41400141d564034107010b0000c800304d44015586a00b0413031b020114003406205002234500c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 139388489 1106 139387383 139387397
    0x3020c06040f0b07020a050406030f200a050409110301050106050a03060e070f140c151503011b030c021504081b01090210110312282a 59
    0x10b80580c1e203d2200000303800d400d6648144400d001040020400d0006540320f1030003001d046011007080b90041104810204d10410040c0b0129491030050526450796241600b000041c1c9041c280a581005009070021040e803001c0c001d60340a04a281c1780c0654558086000608458540d03014481480c0d4172014440349076485480000c180103585002d045c905844079090b0a0740c41502c24031a100c2c414000d800740c0c131003081c3c01071a00c10800001c0c40d0503004420014982a10018945108001d0100d4002400309000e6400910b0388022032045130b100c02850344801a04040c142c038151041c520101c0ca5107001c081034010100c0780e1000c0e0340240328944095010683c60040c0501c103006004035808a8000c13031404006032501030000480014840c01d00c2c0d05401400f000100c15807003441100d11951840c002a4004d280d0448510514207403000000c450120780710182004007000c00c10b84c = true := by decide +kernel

theorem cover : BRFrame.Cov 139208633 139388489 := by
  have h0 := BRFrame.cov_init 139208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 139208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 139208633 ≤ n) (h2 : n < 139388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
