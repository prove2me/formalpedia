-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3230
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:02:51.213881+00:00
-- url     : https://prove2.me/submissions/f5526907-93e8-4fce-bab0-459ac99336f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 580755395 ≤ n < 580935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 580756645 1250 580755395 580755433
    0x60f090d080c0a0905090c0c0f060103031e0c02040504030f0f0e0102070b03090a02120304051e060a03050a0e240130020f0a1d0f011503050405010b09040c030302 71
    0x8003050118490307102203030b066219503001d801c05a06900d000907120341c945000c03802c11081903414a0649201141a00c00244140030ba4856402810000c00c1590300d107440041654641d0260790211400803514552424820250f8981d4660050b0090009003028074004201c803050000391070015000f46520652079200340880e00801030142d0080540b24200b148003981e540c000b0b03003010202e22462020b2030050300d40c0c01a910031146100d01941c4c41d18901014006418000308081010602c100101644ca90303980060b42c00c810690300d4000b030315668850108004110400101504e84165200400349042022103250750f0030307203010715039580c4e40e8a0034844940503c41d043c240c41741001036140d5800c804a0300c4640c94003400200484005003524010941c40b00654001c01001c211069210100450810b5041d03001039800700c04490b20761402e0040070705000c0f10180c0074205900c0d04040b0b814880250001c0d034000c1401030454210342028a0728498110492100302c015000c0c00800c1464140c00340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 580757895 1250 580756645 580756663
    0x807330f020414040b03161d0708040309211e0201120506060a0810090227010908030d0c03060b0a030e1c090b0d0e0d0201061a03060d0303020f07080705060f09 70
    0x20090450320580f0007004081c0410210007500343c4a80c00000300441c11224003400204a030322884008141046e6a0340c0004070001c0180381408488000c0c00b0020b5400039003501103511442504240000d8854110001100c21001a01b05200c00d07070100d07402400da410100b0414400d890f1085140340c00e035410000ea0300201e69541c0d200c0800d0001004881c09440c10380e5011140c40030154103035803102c0b501001c0741c01051907440b402c028000c0d0520b0103208a4052005030f00c003428800c5009d440c11001507541d00c90295001c0040f17444501d642801406504640090032148030b03021740341c841d03042d0010001c001000098006100f03400c0000c1040c10200040c0302040301da503072085185801e0020448480c0c1c041a1800c20303541c0e43d00c0d00b005d003e69042c80400015601c070703400403c02a1500c801200e101c0107050b1880c2c403080d410800c3c000165100f40c203100761f40f1352609001d40c135081210313010815405602d4001d0b10b10f0302c00207150300800c600421068420624030018000301d481d41110305075200c4440c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 580759145 1250 580757895 580757909
    0xc240617011e1d01090803160e030a060c09030203031b06010f12030e120316030206011d18031201031a010905010b0703120e071410050307020a0807330f0204 69
    0x1041c803441107104640010383c0c80d10040360000941c03207811034040d0850386010780540d800c03a004024421011214100d52070703111154603108050b000d1203000a9281d951040c0010701c2ca44d5641482c2c15190301a105c07010082d5002006d69845803405031540e0070056800d00742c038549005d107200201d0501d90422107101942e0030313808054800200759030140e40030001c01e031240e035022042d6078407150105010802010841d44141800700d500210f850064a00401a001070314030000c100845c0c03901e4000040c1c116803040c400c410b10740c40c250003041c00350304510610720198072080140e00040180003c1a03004860240c140d055a5116070b0707108000002c46401380154001e03503404100540103c0e104030780c3c840e0401000030001070b1402c20040018905035450713100d490841042610420540b8055030302088840c2c0c1814501e15502d02810700035101c00f192100104201703000b040100074000c2e0060300c41c0c400001d52207900714049050b0491918940102040400582003208070700202ca81d41c001c3d6401c03a108 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 580760395 1250 580759145 580759181
    0x302012c030a0503061c11010f0203160209100905040b070224010504090201110105070f020f0f0705060d020c07060806030d0c0b0a0209060906030109020a090609030803070c24061701 80
    0x240142c00c983c254006800c09500100a100701513200000410901d48030313104296680d141203040d4000343c00921050010700079500184040c00d144411081022102c5604550740c0c0c1843e503c025070003d9542268001314107040c5028200b200304460780740b015016400c40d408072103040b150200444800c2c0c205050042c0d070010b8240041089003065040010854070505000340b001c014005990708480742101c1c0c860024040c0071504900c580c06220030460381c1c2d881006400c8810343d10301c0c5036544440301c0c841c090003640c000840d0309c00300c1019815a8941140c810541d00b225075684402010414291080c0d4405e00500d0308120f043c5000f08010f943e1240d010700e51380e01c01d0f0b0f502e9145000941155014a4019008001d0340740f43d5566580114040c000c07400300107031200313084500101001d01980002c410711034a04000e101040c0c41d8400d4035031101c0c05140400780c042c41c40c90a56561f04440e504007403d01e018541c2d80c07162091641024040e6071200025004030b90b2880000380c26a292004180005070b2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 580761645 1250 580760395 580760407
    0xe071d100b03070203190302040914010b03010608091609060e09060403080c0a0219050706082a030c04051002060916050a031403070803040b0f071d10030b0a030302012c03 75
    0x4007000c003a42c0e000c6041e0040c2ca003080910845081503103008080e00703001076400102404040c0c150300c0350045500205500700141e60401003403241c1448180180f00034841e504001441d2090100000310004040302c400003015541c03500400007400030303801b40c55080c842910014801729000126588210b82699840c181030b100c00c00364000720343c405460341c070850081030368031941c000760007603190500c1d4403820081c54145e1030010014454000640f400c0d81500b4152460072960070303103076040d441020124008039540d48a10764022618031032940021b400c00c58100a01c89580d4001c940988a8a2154162011410742c03a04c00c910004180c0902503000c0c40111040c804541c0c600341c00c550807034521084134a070602544075080f041e0030442d400c68506002c0d900b00010100d801c40966040f0840c0c0c1000f0061a0648080b03058506180d210740f40030307807008100c4282880c031a800013070250b8070241240f1459910f03420000c0c060415146a0b10341e2400b03540c80e684903d607109040801e0078000e2000f640c2020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 580762895 1250 580761645 580761659
    0x106170417090303040b0301090507030606171e090a0201080907290d1b09090b0a0e090109020901060c0c0e04170318010c030605011205040c17010f0e071d10 69
    0xa03403801d4261881d0300140200881a102000100090010304808a449604d4441c0c11000e40304001c14410806003041d808010b519007242910106500c804041d444a80e2141e1085942c0b04001d2060030203216610240300d1810000300300f20740258000ea039400040e0f6601e50502c0d50f100020b206481d8480301c40c2e0402280f201112881c022168020180c507441d107000c100c81c400989441481c40c10b55440311102002e045074108900000408600d80c050048502510001e4041c2c2e00030b100d003055010070b06c1c0000b00f28100030741c00a0041ca07801041c10001707584650b001403030700d40c4a0000300c48050b1802c2e4045210090300074118815940154070250440d0509808840d50b0005000400c1c2c051902c3d820850207202802082c0b0748403034940d000101d10346400001030123500c503200c021a8007846d10040c0400b040c1e030448403406482021840d030441e40010b8801500403c020410101403c0c6043c0301201f65a4012942c042201c410012407594000c0b21004128106000c1d240071040c03446d4048104209 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 580764145 1250 580762895 580762913
    0x215010806181207300f0c032003031e2716080c1003140c1309060f051512070305100305160f0902090d0f0204150305060f01061704 58
    0x10b040e002e060360700e0003d001c20212001e030841401140e000750031020074484075040380503a060b000b0030340701c100b480b100c00140701400448061000340104640d45031400c0506015000715852030315a0a03002071850400c0f55070384c0d281d03042590036001c40140c01d0100d0908080d104006401a42c2070b682044500083c1c0f0141141d0714680301c501e01641c001c540c0c4164420040703002c6c150003054040d010301040b40c80ca01c1040fa6140e0002c04450a141c50f0800c40c0c1828080d011a240d8020b0349243c003a03981d003401c02d44003164400f40750300c520185c038140000854070f4114000740c00101c0d40e09960041e4801d406c030315900114040c01001e01d08441520340000c0605100350450780d08406100e001032090340d1a9100c05051a1924480c50f0981020280c2044205640201c0b18020030b103080c42103041225132000110800d0710700b10060001410140c0c088290760b610750292450348070306a01c441c0c1090f0b80c0e00d0a40d480c1d120486542e40604030b070500001d07040d4043ea00704800e40d102e084208609650310303030700c4040f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 580765395 1250 580764145 580764181
    0x90803210a15060207151d01111f0f0e0d0c033b030d18030201030e0c10020703120309080f161203060f1208032a070807030215010806 59
    0x907407104000126a02c0c00041c100143c21264060001a400c10076001c4507081000f441500b0043e03076625803000e0240c0340c14210701107142480d01500503c0603480580c500300760440328064000c40d094135000280001c1e4440040240003260078002814070108454640315000d1011001c00d11221500d000240b28945410003184003520441d40d41e5811500010481c2c00c0001e03280c40d0301260650b01d001883c0c10044100c0312682494822880c98000b000758001d180f50b4403000341890b440703042c3d81010910501c5540f8003254080d1058628070005103001f943d9600e01d00c4103407100c689461918869902c00c0c00389195050700902d08a14210f0000240c0840d6400340d89868800d800c0da40c12800011000d0001c001244080d68000c20ba05090000d03001d00801582d203c0c2d130144884c2e5003030200080c2c24405403580003400d41e082c40f0180c41c915040d0340301001e20340c03081d4000a20000d0010308101c80c040250542600a03421102031084010010302d8056003800341c1044e03a884040024001034a89012000e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 580766645 1250 580765395 580765411
    0x12060123390a05070506091507150c0c0209010b2506150b07020111010b100c050a0203010c080f0121020f01170c03060a0503060609070c0f08070303020d05060415031709060309010501090e120304020411070b070f09080321 96
    0x5514041c04020b9104f03804181c120607807680c0300003600c0082d5a40464003110031084003001300700010400c00010600c02d014450318046c8a00354a440042c4002440348141458018009119a6141e8000102035000c22102e50070903040b02d00020941d0740d96540045214026041c0038000500d43e0b8081241c14250010170318104070801e071549102c118001c1c041401038000c659182e17200d0520b40204910858641c100c0c6002c0ea00460400025941e45003886401c0319607420310084108843c203009122010035580070b0310100b000a1020105641540144540e003100c440402c0b442d2150b40c104000da4401c00d0340b40c140c050540e042400070491340510100408982c0485a2624900d0000716005400c2140c001085035176400041103201a103005406040c00d0460140071802071a600d05800c601000e48040c2c05241da403150181900d8090045505880c1c000080826500e40742c07e00030901d81d010580600001c3d002140041c100800009030313400c0010041c104c4c090030b910703550035001201e00100085 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 580767895 1250 580766645 580766651
    0xb03120a09211b21080301090504080405100e040612021003050a0e0109140d020304051c020d020612060123390a05070506091507150c0c0209010b2506 66
    0xd000640c202206209024a40701c580f03c0585002c07400840342c0701c2c03050b20381c9116942c8081100040c42c10001c40307042d101c0080c00010142c0365030820710a140100e4200c2c0740c2100b00c189580c100180c00003412040c2400440d000d20040c0c0c0c86000b0005420040c100017504041c10200c59000c007030180c0c00640d4007a510820006a200d01302c000e0354256804200c0c10358210051002003a0000410300c9000c0b000c002500045250915000100f440c0c561030051005203200c000784050219696a80008204d07500204080e4558019141481c1c0c4160b043d40c959000c0f82403208000d08141c034414400e000044120742142c20030759a446040011402076244501c1686205080c445000b91038100c1000c1700040001000407401d141303410352410186401503481050f0034048100d040d9103602c51403004a400d0384600381c50740310924203810300d0400141040c40c007500301460804203d40c484504030702d9038021100701a181c0d1f80c450108906100c0c0540d07108420315001d0b00305200003111500b01d400130f4410b541c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 580769145 1250 580767895 580767959
    0xc0e0108090109170406030617030405011d031204081c1d040902060d0914120d180f14010b1914121204060e03030a020a061a130b03120a09 61
    0x104100d40310304c0e01a044a00d20100d4140092030f072503c00d2002401d01c00d0176249a040f0b540f60a1552401548605410441d8000c85002140f00c440310001c07107450301a040741c140480000110300c0c141c0107805407640a12501c50244007040c0304031025040c00c0136948a424a600303140507203429450b623841d51150001d844418000050f182c800003040c115640c00070004041e141850081800984289142e0480c1e001d10744003014040e40c00119006c040e0411400035591408444006043d504d404001d0310308100d400a14082c40101420311450a0241e4000c0003c02034503810004078695144800360348000c004406d0201c4000d1685120030110000c00300714486440c010b0080c07510010f030410702d58540001c0b404005194101c4a4110112000c4000c0c600705490240d00075900c6540017809458140c035584161007982c000f42d0b20a01d200310140030803c0d1100c250b049440945a034144182c000d1103401d00d1301c0140e005000545000c4042580c0d0ba681c8185440f100500091490740c4141c0d19002c6c2181d5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 580770395 1250 580769145 580769153
    0x80606030a14090c010e0d03050a0507150e0a0c0602030f1c09080c0109030912150518010e0606090a05011d0a0b0d0f030e09090304060c1704081506040c0e0108090109 73
    0x190b1441801d145008110003166034000400e58400c401800b4000c280c0400c800000903000310680e5a108181d00e44070342c0b2001c80c1d040100d1071020320b8648200440c40c02c4103004100e040441c1c4c0c0924035000d078107603444c40d6a40311070403a40d9104408907041d8010040c020f07117000e6151120341e000ea5000c590030209040500752a148843c0e0f10665803000b81d0782d03403010344404141c0c0180611005103000e01e08030500a82684a80101124000c4100840c1344d85000141d0918809210101080744080080103410700c0d00c4e04040da2818103645451140a0078000240b13010824000d0382d040c0d400821022042d40c8125060108140b00035008010071603c6080c00340c19502e5030081008400e01880344800c0a9416080c0500143c0c001011275000303011200400c5200e1400004032011203000e45460f02c2008603505000c010202e01660540440000003400500403000103030240300031120903041440d60b00c40c0d404002c121520340c03480700d005c03552054110201e580141d4255510040205c00491034452035a1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 580771645 1250 580770395 580770431
    0x40506040b040f090204051e0d080301090e0717030a1812060f0506090906070c050f01110c0d0e09040206030a0e010606050d1103240a0308030a09110f01080606030a 72
    0x106038285180482c04111426001080304020b109000045281c603003001c0214203039803c02e082c1408600703002d00c10b400b419211509007901b116080400c00380c80b541c407620458080d14080b0b0003115248107010001c2640002500f600d5480388602004500c1d06035003a005851842c29201404401d000e01e400000b048080c603c0c08026407840740600180c600d02021883d0211840607100383d0180507040100504d1401c0080c2103900319125051250717469000c2c1c600b0914040c48080011515420704010749503902444000e0a180c0d0b4282c03095070150f11481a049070a012124003040d801170a40b07000c00c025080980045400001294020038a030380c0e8241c2140c01d55081c0e900080025000080031144d038607140c45201014004806060300d9410864990100d105140052640003011007000c10625078a0f00110b00c011540440c4198a07460030740c1d001340040c0142078050702c11160f461418102d40c07824600c03506a84505840d289071307588030b00040c052990001030403404550340c0c440003004c2c2184162 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 580772895 1250 580771645 580771649
    0x1502071205010f060602030901210908210f090703110a120f0506010506340f050a030905180a0e010b1509190303020d0302071a0c0702040515010c0f060204050604 71
    0x750012501c2480001000100c03001c50703000c401150000c0c4000c40c0c0503a4001c5c80030038001c40c03c41d95802800c00d0307140e00500509400c01c00901d00380c0005481c0c054100c080d40c28071508001000b00041c0c0e550b03103001c1007911070800c80f101c95054021460520000700079030703040e20501c030018020483c0306459070600c5480e6402c40308180c0b10b030009548184200001006a41d0140400b41c50071800c0511302a0500000b0340e101600b0040192101c1c20750000010662186c90019004141252001d0107070074415141c149081e41a00058201c13030011500d414010a4580301e0b45450303200754030315a910441080145000c54440c51203540b121074600071036690500d60500d402c1c160801075034454060342003000113103540a507128050505102000841c2d00031410301405283c90401580d1601d0a1030a01200f1201381400c424210301401400700101c215006449404c1c803e4808001d60385540074209a440b04440f441c030700088094a2800010b1901113490148520072030300542401d844200082c0150025 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 580774145 1250 580772895 580772903
    0x40f02120303180c010f120929010602010b0607060b0111010f0b011101090201020607050a050910080411040b1c02061e0a09060e060304082209020c1e060115020712 72
    0x3005200421502503460081840e003e40105528030500001912554242c110b00c02845410360440c032098410781c0206008551041601501901c00c2c404050001c01003041201c0000014001054180c0148280d00444400608260816401740d8503800a0070111001c1c50400ca80244e0580009009000f418034035800007401280c00115440010115900554803402c981c0c1040b81900241c0d80200b60f450300000b1074501a0b6807440640d9082c1d406102d0a244503030011141b901550826611504560107944256440f40d24203014004201c1515030404116601c01c14610b000c807982e2480e4076070000e1180c4058406810204078107111451030740c0c00308103500b05260020390400b0880d030010808026140900701010421811408560b00e8000100700512103400016076000c141e000c03d841520b0b120361800010f03485921000054042d40005241d00360301c4c4200041203080f606040b00704007071412042c0c001d110a030701e0a07869154840c2252421020342c007541c80040380051000100045442c06 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 580775395 1250 580774145 580774147
    0xc050a0303050618010308221505070303050c07020f010327050601051f050301050105072325031703070309020306150936010e100b03240f040f021203 66
    0x302c1c0522500c803075800f2018104c40c0350b1000510001e0321150075192441282c4e424201d03100f00712281c0136400149074000c030a17442c0700f0805d0b40e0503480c4d2201c02454110320a40c0c9c03d0100303482d07000021040e070203811002540700b0468001009d180d442070f400303140d07016070a00c54464101d11824001ca50081040000e50782c540000b001484075003403c410f0281d02ca860f80394140c84150702c8250081c444d000602480e0704204000840c842480515403071041145100031a10b6102c04003900b00903500c0c80c085005c00d113002003540440140d0748410104804580d04940140101f00412000c1000769000402a005140d82c404820002d62000c216051246241d090200900120f14040100d60000104504000d841861600c0d0a21a0003049494400b40d888056546a0b4000050502500740281112054860001500074050325904044a4400190250b80c42c4001c80302c1c1680c0503e02903040c0d800c6081700b000210b990030480310010b544c043d014809808240d212907002038500c1583c80c0c101401c07030780 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 580776645 1250 580775395 580775401
    0xf02090601091221110d0e1f0f020105090d02100207060f02070c1802090d030f232101030f0312020d020f03090f0615040c0e0a1d0a05010e0114010c050a030305 70
    0x15801c0083c5240c42c04c50a150b903240c10000115991064606544820415900c282000507100c25000700002050401503d240350603111009104d1000d0520410056003058085100682c011441b00781c81c68071030303015000d04e14408100c0c801a501c00c850848000b03903a040402c074015101e101030a0308030311880ca60310441389421940b461040000c640c1c0c1d50420710400200c012030f5a40010605401d81c9818190006004500140c03900c85600700c840610820021070f01e003011403040002c00b541c0c14103034045103410f01c100003208210b00742404014402c2c1048641d044c0407a0040c051311102c00341d04540907185c80c01134200700050780c0010308030b140d0300c1c02c020050062110041c0400c0c00d4604c1d0300340040c006841c1840341b180c0c2ca484810030040c05070755202c0b80d01010350311549070a00d06070406030229460903941d000180140601c0e013580f101c0b205401d00483c030f1005150140904844c00e40650040356403e0469000c0001207038035000c0c2c10700144402d03860003e07009210003800c0d54002c0d01e0025142c6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 580777895 1250 580776645 580776683
    0x5130f03050a031206050901050d1a0106030b0a06170a090f080a0807120b130c020709060806070f0f080a0f0219030e0d0504061d04110c0601031109040f020906010912 73
    0x20808652090120741045c1c07003405552039000f031050460380205d41021440c5041d0034040304106101160010311044840040303001e07500350300442440c02e41510000714041d5514821620001c02070008d210006098001c645a10100c2d000401d0241c041c244a0b15403413010313a1414515071004014101007541d5404000d201900084c28031044090b0f40300500104001c0800280c030094a03851030214607a0314140d65074040d208214540c05001d110304c04000194813106180c0d6948400c0300d80700000b49217803e054440900c10340303003404150481d4482008c5030700d88544800180c8201c4c03200481265080c4405221003050950000c11000c4507240041c0c14403140010b00c1c24102015024024010100020040c8640c44025190480c081101507000d04003403000080180c100e0808003c1e03401c8000ca4040340c00d041c081442c82c1241e10513146908640018000d00203946021a009000c001746141e5803009410180b640d2075002d0014544607003441d80716603050504801d005401e882c45124514045000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 580779145 1250 580777895 580777907
    0x50301060906060203220f082b09030b0c070c0e042a06080613090b181f05040317010902210c03011a0403060c0e0306100803040605130f03050a03 64
    0x1c0e002503202444501e092400103503603440b03031140e02040405445044441c1412083e9150041c0100103500c08030790361b0340c90901c2c1c0e07180c21100d440001e1009023580344044181004c000c41d101e090780d0b15000c1080c1d2075600c2d109040e00000305035009180b006c010401c005000e8101035009009504644040713414581021784080d182e0011401040c840c072000c20124201d5001c5110032202c161a040c1d4455440d02c01182542070b00c00000e40c60181889654810840d084950303a10401c1d043c0c0e810300c08280c40b064035560b9489080d8080b880880b51640110f16150b003900900c2d03200b4001c2c101007001690800001010b400c09038442c003902c03980400d0210906600085c401c0d10070700c40200c040300340d00341080c0140041c4818402c84c0130f80307d12140f5900568240301d00f030300c0096400c58410005d980381580c02601c000b03031143c3c03100d00c207000b0300d00011407150300501420309481000c0300650034142007110954880e4000840440502d174040b000003511030150240401540c070400241440f1680c601c0c0107410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 580780395 1250 580779145 580779149
    0x4030f021605040207020609030303010308091203040b0d0b031c020726060c090d06021204060b01050a0210020306011b1a09030c0c01051c020d0c1409060301030f11130605030106 78
    0x464002411500051101140c007400362041100c00699480051002030420b124141101c7d8040c04084000010700c9403a074040c006013942515000c0b0561000090300b610792045002d1000141d06c2408802c0007100c19078801c00034003402a084494070300c0800400f03201c404020b001403006901c560701c02e2025800040180f501200c140b01043c4000618548542d1120700080000100c0300d008161020302e59211a00c41c01c1e40e0750080b204554030384501250902040c400c40d01035036441c1c00c01c4010b81c43c0d544100200ca000c0311941e8044c000e41103000030312101030350000e8403a50401c1800020045a502e2940100790010b100e00a4440d101c080d0480d940e0050364011b0201045400500c0006824180031464001d042001d1038101e80e20340250f58019203a10444130442445407002c100042c4200a030750108806030001c0d1640b90041401085402c0346101d81068550409418801000007031507204440200b01e1060a0961204030720710007040340e415001c50b50303900564079500104501d043c28400c50300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 580781645 1250 580780395 580780397
    0xa20041e0c020c0306060d03031b030c03060605040b030a051005031b0f0108041a0406020d06031a060303040b0702060319180605090604080711010324031a13142404030f 74
    0x14541143c580041c0d01e84400800d00b03030082c0391481c041c0f0b00b05031085d409010441c00c4051a022442407003a0700400400c1d08440c0e01c3c0101c0d03e8100e01007400c031300075002e540444076010300742c0c0d20b55a1843c1e85403020b083c0151100e00c0b490301060020495907030a020041c420815201e40d0b10644013003204110540c8041d0759000d0501c0380500c18400840d054460010200154281d5004241c5540c0b134914001c0c0306084481388414544680441048003422801211100404e8100e015032614401c243c0c43e44524030800014080c1005000c5c011b00303104016503403004031040c0240045128644040980f401e03c90300021402030380481e04208103c5100360381d0007080e088000c0c4228941551562028420a200580140a10395409005a109070800c1c03100c1b0707024040c00680075400c00400a038030030711804103c1d042c116690801c2c0011049024443c8207403110145801e48800e03585503020540440c0c442000d0030f00617004280c55400718820803041c1081000c0d118401c921305810020004000401240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 580782895 1250 580781645 580781653
    0x2010905150301150c05011e0c020601141012060b0c0f01060302030c010e1f030f0c14040e1b0304050703150504320f10061203020a20041e0c02 63
    0x1200420900c4181c07815203107048410107400900d04c50644006220410003040b56013420f29110b000c0c001038000080e03e0003c000b040c0118941c0d00402d0703880301824060400c1080c1084020f00d002d19012044a0450703084e0705203500404030190f24542628196040340c801d0310b000040f9140050410002e007000008030034002c0090313034110340c0000c1d16880503a160b94100040890500c1407a592058010400300c1c00010098102c450702038003902a14808000300001c40c54910a400d5440c02842141403001c07241e04802e20b4182000c884200e800c40c0680310707805d99200303d44090044203400000310700840c0910024a8802e2841c41e08080c00c2d0b2400c01030000d16030520091000164036265000b078500c018202c0400011201c0e12018904588102040580e01ca0401c000000700d4011400468981c8420303010701086840d0302440300113480300217000300140d001c5640c070070104040505a8411030489d0380c01d40c00305c110000008040d50b624009141d00c1d803050220403000045907200d6502a141c5a001070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 580784145 1250 580782895 580782919
    0x112518061a13050f0a05030a0303050601020105061206010b03250c02040b1804060f0b181e061e01050405100e0102060a0b031009080909011e0e0415020a0e03030c030702010905 77
    0x21940c89500c1e22459024034131490030400181c1e20b81c00a10040c0c90003804580c88000300e030800074003411003501d1081c05540307444007280c01c0f41000b186404039058a8001410b540c0d03e0316000f01c41980c402090000c11703680c0525603404e2140300001c00200525180d8810310340c0e5045004100490f1a041c00380380c4110b841c2c1c000c03088002810080a071b030150b088500040c0300311110b00180050261248200da0243e03020481075824800d200d14103010720640c86100200c88941044070858800944206502111440c481070b0341100c907030600d413050711040c0740540c146170b9501c02040302601e82854003001b040c02d1102c04007048d60b0400a580d80b00002c07400a000e440c1d980000310703403100203412004524644640101003440006401ca03074a20b200980702c5a4a0760f9580c8104242500b04d148501c80c0e800302500004600c400e2101079030248d50085a102e12540c1103c807400c000b0b5110741d510340b041c01520b0b1070b948000e60301800074003058414a0042e582da88201d00c00103050080641201d4403506894100d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 580785395 1250 580784145 580784167
    0x7020604201302130504111209010b18040c0e0a020304110312160204021303050f100c021e0a061a1c050c090c070609051c112518061a 59
    0x210804042d240c001a070352001303c075030b6606010382504540e400c20700303145031307201e410400ca0024070b4401c200702d181d1a1180c1303032050440c0c207a8020b40c0903264040f015850200c01d81c1656542c6980203803081404902040d5202080184200122010031030310380e0100401c82405851015001500c900300c01030a500b000303003616010603008011484a11030f078669650003c41d11542e044945403803480d03038100d48890382ca01e080f5a9505083d5010112401640d0741c03020b0182a5004000358211940c0280000c81102d8095100240b86030b1a0100c151094078880c8000ca1503600c0f4070031440d082d130003400b00e850b1944014801d0350a540d0324100d000ca1200e00d800e401060ac04902c1c2c60204200320384a21868640c1002d075607030380c0180030b000b07271080c0d1600056900304400000c25440400c00590045240fa624100658113417404054800312a0448403144051880740d0b41c05020b0307021100c9640340b03502d40304c5503a6040e040400c006d00203407a564140a014500c0c000d8003640c5000a01c845207443c5c1040f0a007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 580786645 1250 580785395 580785409
    0xd050613110a270614130f080f28032c090112030903110a05030f010e0606010311090103111b1e070b041401050714060403080a051303050c0705090702060420 69
    0x20410003004030341d640c011400580301d42100d25190301300ca1b82d143d200d922481c26041c040d07072512422084c0d2181c585008007040d40420641c10798148811000c003403808030700111300e880c01610030031010010340c00c1e6003499000d0014403d1115104802c40d8070f1480303005400780010660306810042d500411801d0490010364800040810b480d40700d0080300c1c1400030007001c124501c0c0340d030700001d80c14010032000540003001544800c0c0000c2070842114456110b48005504a513007400700404003110401c00d04041d94040d811400022544010107803604c54a161b4841610003801900c0c06070b41c0241c90410780441d0000c00c07681c4048160f2025010302442d1050f912483c0c8124441e11110b010a40d80101ea941c0c019010b4841e0399400020f101a903090000344251203120480b42280840d07800e00105124a00c03d01c03d50344034480d61180310b04405010384085e10250440034000340a8030681c180842e0710344400070424081c401c603400038032081c01d00f0f14224000140c4412042c0c62040003c1e04000e1969980c0b13 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 580787895 1250 580786645 580786649
    0x60606030b1509030715210204050a05100c02060c1023181207080901020115060203040605071e030237140f0601060f0912080d050613110a27 62
    0x2010090f5283e42a00119061480e6175100f480140c061011072100030b40c010140c0d8840144409140e5490382e503100b02c4d04100c0c095030003016000201c0300800d005074100864008850303840740c00d19081701403541c7c0c00501c0c940d01c07040b1b070600319402084921241c20f00a008042d01000d2a11122181402e88010350600c001c0003810f204024080000d140502e107418056620804c1442681503650703101401d080006034001544a1700540c43c11401c03440d00c1d00b405569005862140d8042c2d4901458894216401d170080041036403209002c120494680c204003440300d4a1501c00d0300074140d113180101d2034400c884000310940c1031100028503481c100700411050490815441082d0300005000c222102e4601451400182114801d1b000086a0f00303802550006180000d41d070b40180c3d140d114180e44500380480c0000a000c1c1c6400e000841550a080d0401a071200780a010050303850404201d21007503580200c111189100700160074134100742c0c014a803070113060640300c1c00d850141c491490415004054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 580789145 1250 580787895 580787929
    0x806040f0b06010504030609050c09010501050a093b0f0106080c04270507020109050d030606051801170403050301031b0b0313050f01060e01172116021309060606030b 73
    0x140e00050b04036030003030044e9809181c000d003081001104900d0b00e240d0710710707207440524403c56a441c00021a0741c820b1088581081d5039070703940c00e020f600d4458443c9401c40743e0409080d5420820040300c1902c0c9003200002d00d841070640340e024483c141403850800d140010780100c410042048100400d00e10100115400c940207400402d0000c58004040c482c0b0000d05441c1d406124244010f0000e65541501b14652840c00f40d0190380d1070b00000c0e0801e40449400d03202c2c05001c04c03c00c0c054181091120740c0b09480040c01814849131102c2d080030048048503089400700c0c04580040014020300c0b40311158140345034000300e02c5005d01410f2580c1c1401a01000f058803027815903103c990701c1004020b0210740d0b8000d08101c001d0080030b0b1540e50002d00030009000f10034250521000028400800040380496031569141503c080b035505030b0104003981c04115024450b088500caa1001030320703501841c00c4022080c15000a83c0c400303078942141500c2190740f00c1004c16043c911814455a5106044903210443c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 580790395 1250 580789145 580789163
    0x60f290315180a0b19030b060f090c0c06010f12080d150602070501030e0d0903023a03120b01050433020d080a0e0601030201260a02090a0806040f 64
    0x291030490110701c882014560b0810219889a0510604040418060000d0780b40911039441c3d442d082c041c180000d44000c0c00c82c0001c4010805c04900711146464003d1801b400d283c0000d003145c000715000710030030f48010041ca0000103404094240030311026014081c929218148d0a103424524810b04042d140060440800003074045c90480481d40b2042207030b40e1a40125a0681e52941c02a440d500c0e03074410a40481e040c07800e003007014400418010255403041e00c4240d1b446046409100301c090006800c2c0c080c05500d0178000c0c0b4844040c0300201261007800890080c10212460020106a0019034031406642000c981810350780c2c00000352001d6529009503105059a800001038034001020110b0001001011405040e80e6001ca94400d2200860701c0d09609500c0307124440b012604c0d070041020b0160801e8005000540c407030081200800081e074649070340300e458020307240380c0d140301a04c20b60341d8943e0024901066040001000000704a82000b600d42450030380c4402140706c401403401010f0060b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 580791645 1250 580790395 580790401
    0x1090b07021513080d1509050109060b2a030706050109060f05010f090e0705071a07081812091f0c0308010602150a020a1403010f1d0606090d24060f2903 67
    0x251079202d0061010515400406c0340d547d01d600d00d009080c28007400d1141424100045801e00e00c99040310308201c801504150100c00b01c1040b0a49003003244580310341d90004010710000b2544034080d1501130510200c000480780d1030484122a207003507a5000b60f050002200a007100ca40d04041258110b58002d4400b00280c0d8400303008070b41c0740c402c09800500c0d00c11071080300300040070164009489a409505d0308201502c0d010300f56520250b004540c41542c1d0f1210b58000c06d114011005043d12030070142030000901203000c00e6007a010031745000c200006001d05e0192060591164590780101040d0014018890340d90800840c030000051071990182d4000176082001d520a4414040d240c490790202a22075031034030030028120f209845800180c0907029084501003040b0b50f00c0c140900801090b03c1d00c0d06880806011508029480980d080890a0610040c18258009a121080100348000745440c1054103580d44c1e101d154004074400d50056191012508000c1d40354040c1d5545111010b03180d507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 580792895 1250 580791645 580791667
    0x501061d0f1c03090503060112080403030f0507020409150506040605030a080f1908100e06061b1608010c1121030a0b04020d06060e040c09051203070501090b0702151308 74
    0x1e002c4000781d60981880d1101c0420300d60b20596040a40d842201990556645e50180801504003000d024044000c03c00041000a0007209070310000511030030418140562600001e00b241d4010005564502e11010305504401c13051048941c00318007180e007009401d0405006c0f80d80c910340760710010121f1800203040d9050000d0f03c8103a809041691340307880c0c12030340c1ea100c00038540c04050301c144032003000b401e40c00715029030000451031151402404882c180810741445903110400403800300420700481c0719001c2246000e0161a0240c01d4080020039907200d01070000704500c03086078042074160040e4005590508003001403002402d03080461036103c6d150451080d00800c42052443e91042c80090700e030000401d1504628100d03540d40d190f180c90684684140004e880c0d400d00e003100050741900080c0028070303090502031441c0c00d16404503400c140c00ca9030340500b1144906c20650740d81721200108100a0342c108505000b41203425032030056414a61003e4540d244010001072001c070000c50140040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 580794145 1250 580792895 580792909
    0x5072606040207080d0501030c0503060a0603080f22030507050a080a0209040303050c0c0d121b0c0318030507090e120712080411180414010e10090c0506030f01090501061d0f 76
    0x420300f41719040059596902e081e9540c0d070311501c2154000d004020001e03122000700d02c106401c5a4100300002d00c1d150071010703140381030f9100c4075540b401441c6584c1e103459018280a40d4002462141c00289800c40c2000c04100f083c1c0c0e0140c1c4001d24550208042d0300042c0c560140c26504554181000700c0c150b00c40340600f014034013400c00710f2030076445000340d00c02102d81d02c03445141941c80718400c2003142c0e414400c58850450301a500002c04108010080f10000740308102e224065414298070301d1007641c481e074406040002560101c00c11903101c90b810742039000140500c440007101c1481c11403401e411a0780d00c18420b0342262818050010120000d014040c07c00c188440e0312900a151034901c2070401804880b03442c0984041d10741c40e1300a002c18020350014494111400c0000000b000b17902ea01500032005407049060403104408007080004d034688600c0c0266018040c1c0400c01d00da6503051071411021100705a1040c4d0070819105103418194200d480211109101a501101a00011070108082d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 580795395 1250 580794145 580794157
    0x91b0e0411040b1804050c040632042306040509011418071e030b131109030f0a170f0d051302031917040b04150c0c06030507260604020708 61
    0x41848001134450101403c152160780c0000c1c111800c101c01d032645107001c40306000318050f01c408034048130041e443d031035944186102a02a51001c00080580180f02070740183c110f0f61008011000300c85003a009007040d6040202d903900c0c180c40310f509052070080003d4001ca418400c80f450301080c8150000540c482d08106400040c50401c41b80d494181684010001e110384002c08080605158440048511074010030000c11b60041140e8038105040403904000c0214007014192007004100103481d58070140f03c81062211854090718040040d801c00c0d0340c80090a40b005401d603201040410301d0007a10070142c4403140034400c000102660f0b58003081c11302c00315801000e9810701c244800c51134451301c2283d003030001c0340c41840018582410f40d01c1c0c0005500441c01410b1440303138180402e1203169256a4007041010141c03904040035405529220343c4100190080c42c0042c0c0c1703c0c03041144007600110301c605a40c1c0d03804400455040c444550525241010306802e200f05c1e00040c4000a100301141030b070380 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 580796645 1250 580795395 580795409
    0x101d0d14160f0f02010315050a0b0a020a050a081b0601050a18020d110c0d08090d030213030b0408040f2309060411040b07020901050105070803060906120a0b01091b0e041104 76
    0xda030421a09000400d51843c8600304d00090609105241c1d6800502480048880140100c980e15060a40741c07203146e0013139a540b0085200303680e00c0c1c80216200b0003501c440c071801412900d90300c10b0840c1c950708040c2031016903aa0b0700ea1010004000b1502c40c201c0c03510032940c42d50a159566250410b200b00a441191507072000d0b42d0030b02d2601505082400c0050520655a408442c2c0211140001391104c0000b141c0303240c043c0e08680ca0a8a80ca4000e80042400c0e0072407107100c401c01a22503450f82042d06040d0740903a03100303802103001d0001820144107080a0040b841e4031450221525042e110f458942c3c800b6a8065210400401c00540300c41e08114440c080d14041d26442d03588a11013606581c02c000b8040e41304003040000000c49500900450f100e050b000910a403440e91a40244420340901514164110001006030440980d00f405905d0071184a211414881d5160110040070351f10800c58210002d01840c1180c55000d40100e003001c418202980c000c9038440301c4440c51001d5010b0ba40c40382c0c0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 580797895 1250 580796645 580796663
    0x503220222060501110c09010e0901020f070809130605130e010b060a020313060c0b010306090f061406090127151d0a060b030c030621101d0d1416 64
    0x24400c80054010909540d4203036921005c58041105042c1e0b1000c0d05010a03030000c00001c01030011034041e5940641c00781a020026241c80c0481d110a009640303c01c03000c0d00c5898011441d0f603958507215104030b00c0003900ca02d040c0945d50910f000a0780520a60340f100725001d5a8505403040202e0a40000214440040109807070b64010f60000c0c0d1a580400d421030f0001011034404100540121030358405540c00540005403a0f0a40d60751000815580c802691071000005460002603158041c03814403c1c00304059000364101502800702c1c07010180c0025943c1346810460103042d06e041103c03080d000a13201b0b4003042c07042c078605030048002c0e4a900010301d110031414000d4a204140340d0000d0160307681190400089640e5804c810040c00240d0784000030480c100007142051400140b03d045019007441408401c4000c2e208083c54000040ca00b4a08213880340300031b00b0200f2450700c40c41e1001100310060300c04d010702100d000b0211000504221101c100205041c2c418000040921007a1a07121400c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 580799145 1250 580797895 580797949
    0x1d01080304061e12061202150c06060607030519110114090303130f050613030807020601050102030706020a031e05090705040b1f02070905090c09010503010b0904110d05010213140105032202 83
    0x4000d259503c44140c0c0940703140230b240b03444816604101c44844000c4805000941c0702d207010088140d21089080d41000f81c00d0000043c0502d50680455164620f40c4816607515050b11440d03003035841c555402518507107107008104886c0c0c4080110b075400b1004042d5248610703498a40051400d40880000d003240c4030b19400c0040c191000201031001c1c3c1e0007500e5000c05aa5100e4040365038900c00d024450040e0002d00101b400035049401174508400d4070304000c280f2296a0b12496034113101c01c0901c482a503102d40c2403008180b81400700c0340141000392001c1c055240107e0115001e2100c0702c1000c0c02c90301d82c05a03140e00051090100b0809044c5418061080b4141030708241d680e045641c8806200f040d00138000140703490144524180c1e08005401034070556215111940241104180e942d00030000410000000c4d00a00c0204028207450810190311400c003d0740503402001038124505020b003c0082c040c0c8031329100f0000c101d00c1700d80c6440115280305440826841612184115021480d000308 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 580800395 1250 580799145 580799159
    0x171303140c03071202060706060b07050d031112010b03100e0a060e01060c0f12030e01020a171008070905060d29091b0d050a0803011d01080304061e1206 67
    0x1284050512504642900264508168540f070300ba205803195071001c030b945480142019005481c2c3c603401001c00250481e80d42d02410b10030751200f08101d43c5900b03e0760860360282e40510908202c1c0c2a00c6080c2410b00350f0300388501c50b10071418080c9090511000c0000b542454188100304003610607217010f8100c03420107236980400b401a40c09038944041e414400404c003c1e100b041e000d240345400c0320030088000d003c0d1f15080e51014000089404154407040c070744003216404d0000300300c5c08205a65002454060501d005481000a400c0070200214000108a040400a07010003600c024941c00520394481c01c0008000c11008540145041c4001114030f0f42c0d0107917405052407003090b62112800c0d039582c864840d919501c4605102031903401c0710418010764140740940d46400c1b8825402c45103841e0702c544604029030426401003008581400140c103401100d40980fa004040340f40040d4140303418a0005003400c2c0c21140c07120011001036285045451184032860301c080c016050410032f050700c0e669 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 580801645 1250 580800395 580800413
    0x203030a09140907140a110618010513050705120309040513030f0c03020319090e090f0708070806010302060901031503030302091503011d091015140108040f171303 72
    0x109071200303862414860ba40c141090310711144142841c1d901c4403954807440c813042c80903811042010040080352140c40000c0c1c030702084013034010848040424040b00070782aa16003980d000409107103080c111261808001000001d001b002d0f681c0803640400762940700ca0135149940540117040350300c50304000c24003141030096010107490340e009540d5036100c03100548041d6003000150707000400503441040361045905c40e0700b005800341c00642c50884402d41e0350b0302c87c44d2050801541c045800360031401d01c0031b000250130010003004100d602e015040140c9003064840e19100144006406a075000031a0800c0c0d038442d500c1602521010700c0504a02612401e000300250080015a400b030b00d40980e1f0101c948054605680c12140601c10b885219400b100701c41d204524060102001c5105120344043c5110f40303800f980c0c04518944003440f6200d42361041503055100b000e030f00c0606211405c41072002040c240c0c802100e074541c021403903c800c4c04ca122800d4405100340502420044121030010080000100d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 580802895 1250 580801645 580801649
    0x240417151f0602010b0121090b1f15080c0f090d0b011a0f1b15010801140703061401230c06011a04050918150403020c0108180718090203030a09 63
    0x40a90070040c0e403690420713402c942c40004042c0c04106201c82c007540d8031401c6922080300307901d0b0700408140280e0f296100d40340f0071420b480c1180300c61240e40325007000f001040c1c00302d0020030800000d2191000c0e501d00240440d00007411a600520000441c0510990550102d6910050141124403207207840c0c2001c504486080c003c0c40401002c0e14210100c40031781c001038604a0b03d681c0784203450701c4000482c042680c0040c40e91803c090080551101080382003068250080c200c000000c01c0021f06660800f082c20401003c01081c03506c0d00340e0600400303103111283c14551000782040000d4943c0c20f1007010380406050414050032a0000d40b0304000c0d0404036906041f11142c2032101c250030309590341e0b00c4e5140142d01a0a8000c41c400002514000108000300d075409400320070b40d035103450507d160fa094890100c4040e00543c2c01ba64580446582c0b189650303911510f0515200400500105440d450707560310f11414034841c041d030404410781d80c0d031540450201c590080c00c9035a201d038000b20281000d4094 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 580804145 1250 580802895 580802941
    0x50109050114070207090e0705041503030f050f0405010e030a0b07050a08090a050a02100c0f14060f1015053a090b040b13120e24041715 60
    0x12040b16000e0358014800749000310700c6a009031810505000030140103001c4076030240702a02c14001c00140c103480318808ca804018140e0101c800310360541c00e010303143d0f042c402c580300100441041030062010568003541d0580d0801d280c911108980c1d84001303882c210800001401c50052141800100740d085801008802c0701626100d40555603d591143c4a24542c00040c0054005407100e50051914215130100e0410a04201c114241a61500e50101845c40400c440d441d8040c890f00084400030050340e54400b1413121034645a10708019103103010011407081d035100409a8000b0400c0300c0c091001c1c1d03804c03e500d40344021003594400001c2002083d902c002e030013640c0c4c20880d03e04003564003401410744994102c0c440c5103c0d0f4130b80355910120110014034a180700d42e40c001110b400107070012041c0e0641e50301596100e50f00f4411400300400e040300a001038001c0f40c002000c0542d201076581c1541c04a992800021030010314540d0f58a09182d0020081c00b01404480200141903000040949001c0c0607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 580805395 1250 580804145 580804151
    0xa0b031506120303090d03051009060602010609050f13030503060411160b01050306041208070903061a090a09030c06050a02041d0103051501060c061e0204030b01090b09190203040309120501090501 86
    0x101d160b506480c1d101c01d586981c921740007510b0485500c0d029800058210710009000d0304502c0d903912a400c222225a000003006035145d41c81041940018055560022070b01c2846841d1800c0105078aa0031282400300142404002300010310181c2e070720342c0100056108100401d5490003201c1c0c0c28004c00007184800c4034140e40701e000104142c18001041d030322559105080078058600c102d0b040d41c1c09440113091100308200c07004048001406d50146c400c003850b01060360400d541188040002e591801040706200c145403e11150100b035106078402003084e0400d03c0041d903a115030344007001a10594001c2c0308146840c1072011000d40903190814100c90140303056812a82200d0303d10700340c00e0f000380325410006a644a250011a4040d80001c484002500340085800990301c4c061080c0e0b0084e50056a84540440041051804500540b1001d1004803000b2280d0b15000c0030b0b02d10302000c0403222111050307010002804040c0582001030150144441e00c540004243c5070940c041e0040540481e600d500b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 580806645 1250 580805395 580805419
    0x405220c0302070309061d04090b07020c0f060d020f040503060103050a050f07060e0108072307030e040204031a04080903010204180b0306060f2206080a1703040f0b0a0b031506 77
    0x4440c1c800d9031107039545950f07911265440c1c2001102d0403074072207ca003003910204c1a00c94803242c0d541e10032541581d01c1954006001c2c074041c2ca010342031582103581c03030340643c0008040b0343c82030355803030112100001100e0b03006172680300d003071202d070503d0050b6000f46030944144000402800400602120081d20a20440f512420000755060320348a89115502c049004198440d40a601501d00a98041c215103840c110440d149101c840b004e0301403a0003001c45482c0003400d84141523200c201e40844910a1f90158500307451a550800150390030308040d000b503100ca00200e4100520002140c182d88001402075485644458969440707a903503291507aa05071402c43e4074149410007068003403140c4001000e80b15003504413000c4c00a800c5001c142841170402c4d220b00700b0000c07007031441280c010706020782c010f0a0b58485450080104800c10350006900b850038804c101c00180003c40c094001940844440c102e034072062849000783c41409038040d414000e0304180c0e0f9020440c0d20a05104103400c9a2041c402c503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 580807895 1250 580806645 580806647
    0xc06010503120909060f060d06140a080114060d02030708010903020105060405150f120106051e190b0a0311073309020d1b0506030a0e010c1103120c0405220c 69
    0xb03c15000d84070b03013050080700010030a203048109107403085000780a03240b900b1548422003049036210b0304120a00c10420035046446d05002401c4005082000003c001c079020200c0c02c1a00f15100501a611030490205088219142449010002e0141c0c1000f0700480c001c03880c001c2d003e403004440c0c25020303030314180000d04e60008013050b40006241c06000c02e03041076241810b015080c07810202000c40c640d2901e00000300f68840c200d24001c414403410503022501010301c20400f854814503680e07000c80400c1e41042c0b00e2000c0c220110392492003a41000542d07204113101c100718034012014054000c5200080427941c02e10440f610810f1001202c42c900081014041042c003100c00e1440060b4002c0d08007440900082c801d440c0e880309103034410410101803170303940d000610941d0084442d12010707030b00c0f1545041c04c0d0703500f401800000075050601c1c000f481210310300e01b81d59000d4640c1d10b40c412089103000c10043ba0a0034225005003030041c210180400d01c0311489001861061424041c0e01e2078550301c01105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 580809145 1250 580807895 580807897
    0x30a020c011b020f0109050607060f0b121203040c09110c1c0207030305031b0c100c02010507050a0c14060106050406111204050909010b09130201110705030706030216080c0601050312 80
    0x885800b2191984480480e003e0100450603400074905121000e0b0700804c0340c1c0d94a84c043c0103264440d2001184041c0c101007000c09541c6a41142c500a105c000714060031198041382c00941c0186170400580c4070f41d5a4202a03401305440d9020045441c40c140c50040c0c5011494010b1440559880445101c1d4080c4000d007041c8000300c01040e40160400c1c0701c00e00020344200002e5810a81205440c2d035507001c203030440380e115440400000880e80c487c0b88140c0400c4000e02400c02640600d0008000a03d48000c01414511691148008021014000c5801c0154414403685d000f2091811034007250307184c0c0406440c99004e80503440200d1100180c10a400d5000200c045400c330303803480e055085c07925144c1402a80240548082c2855480b0307043d05031540c80e07680c0030601c03071002c200061b16110028000076211401121448090703821425050045440000381c0c04216241850010b9561203400c0101100904041000f4074a190014400c428608000b4005043c0c3e042282a14100918110000c110b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 580810395 1250 580809145 580809167
    0xa0e160303020601051c050d2001090201080712090b162c06130b0d0902040c021b01080a180803070311190f0c020909010903030507030908090409020d02030f030a020c01 74
    0x1640000010301c800d003801d040c041b5a03241403041d07140c42880169240d6081032003070701030600040c5e00b950440300181c1e00c03485c0c02002d9601d460001c00248501d900000c2c1707002d8000348180148a02590031240003141030703028000040d0030418500705814130004854001c090949a000051001c6c0903a68500882e500f18010340b21480d0107108181c1075072800d00c0302c943c22043e2040c44c10307a8a0500025299660070060140ca44001c20000d4031320803a1042000715480d10b000ca104650280c0050000714041108100405500b42804a403690351145160094041085100708640441215504001400c0c0140d400f43c111b0740ca09108615213281d50716824042c00900754442101c8020798552140150340d40c14a00149140282c920441034010400080080c0d800b40003030783d514600d00c024568035228240e00404549400c0c0140755907030311014583c1c0282e40c2c403203100702e42e01c1001108542d5502c03030b071141d00303540641030b02d02140210402d9905c81d008001a40058001d9008840c05980310310402c1c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 580811645 1250 580810395 580810397
    0x609150108040b06040207050d03020d110319050612011805070501170112030203090907020a111e041109040510091b05030a020319060b04210b040b070c02090a0e160303 74
    0x407560796141c42c0d0705180070f009064513070400e90030084c8002207001070080140c582800d480150f03075008400881b100f00c503c109408119400244180809038a5480c40000c0c031002c045001700c1d03281c5034403000074411741c6030614a207590342c6441600728174400491400000a0302175410303182400c1d504c00c01559a2000840d500705407000031401840300841a032010344142c4c2c041d1045a05080700400030400e80c01c07065419070050703800030010b103003007003262150302e010b0402c1510285400075842d243c003118582e00c0010140304a48410a95030660780d4038058400448000707000744013a081600d01701c545444140162088181042c0c803a0040c212070301c941d551080d071183c0d034a6107556075080401c03000350000780c150001c031149074040c0329840010b0b0140402030007201c032200355154540700e1607201c1d81d40080e80581c0020990700081c00130481d10038010341d0054100089200ca6a151001110000d154200c02035005075201c2c20711182e54031703940c841901940c1c0282210424290100e28070030100c40345c48010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 580812895 1250 580811645 580811657
    0x2e050702070902041409010510020319020c040c121a010905130e0d030e06090c1005030612060408040f0e130605040317040605100b120721090b1005060703050f031806090606091501 79
    0x561001d039143380c418800060b1041c0c50f1100144400541a1007124034480001030246080211440e03d52042541044078000e02c043c51114401c000b030103550f068480c070340c46a00300d12601818125980c005c2c0c120ba82900083d51104810b5203000707001000c0c0b01e403042106104850000d80740500025800c0100c000c001d11060040403099000c903850f500080c01d81c1e4100c281d548036107a404508004107802103201c0c1d43c1d281c0d02c95051800b18081c0f0000ca0b03002c1c00c0228100418404049101c4400321000760704107501140a0b52903040c140d6002461a030f06580340030240c8100030500060b0707403109018100344001103d881e44d407601c940015006407081c0403245069400401c0c000f40c040e0141c00820f12041da034408441d50440c2c203030ba080303400103207050f6104140003040182481e803c0182c0c0001e0a42201d1050800c2d4898400904a0048400c0c203d2020340020200c0c07503203110481210a605006000c440d910f03c0d111300e4440d11544242e5000c0c3c018004440850700c80e941d01040e050703d5900617524070b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 580814145 1250 580812895 580812907
    0xb181804020f0604030609061e06050105030109020f04170c010305130b060d02030f01020d02130522020307030605060f07030e04050118111b0604052e0507020709020414090105100203 80
    0x50704403030300c500383d8041420840000041e005001701405c03980a40c400241c4c010900d2104151111101003140420385008001d00a507a0410152419201501001a2140002200a01103104170380107850b0400240c0c1c89402c0f684000a17420083c10800e980c24003482d00c90404507000c3c01c0c192907004192139403460000340142409007982840500060454013051040110b090032a489014080e01c201d07000140c06c0310340c00c1c400088000808041d5545018141c8404403d00490843d40141d800c0d29000400304a40c103100360071010107030100401c525690401202c0d03400c60303a44003030801c4012580c1044021054134040c440c69040781c20142c1c2160740000d031b40705000020120f11400d82e45501d4240014410340304800d903000c503412220301c02486035040509211b441c0103000c9280303c40010000c41c2d03408074280c5408403540c240341d590b0b502042c561aa00026414003400303805c0068400d101042c005000c0100f0510709004441c142c030b03501c0d02c2c5d9803a0300521001900142d840b0f40564420008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 580815395 1250 580814145 580814149
    0x120901090303030e010609020a0e040506060301150c0317070f02011503020f040e10110909011a07030f05190e1302040503250b070b0402041a01140a0512010b18180402 73
    0x2030311134800024000104d05441c0c802c030310f0403600640e04110000b6079905a00700241070078491150003450445070182550b16140004c0c40749602102000e0400000034002401c25000c5d18500c0741101c3c64460700e00d4180307030074503004088007820740980e00150b003010f00c80101e8120380b168040980360040c102010a5a000050101501d44013010b03170442c1c8650f000c0c000020761640300e0070b0a040748552103d5039927210002001568001a0003011880ba00302200c1100944202c007100c1046516003802d2100e102070324429100c901403140011b4142c5554401c0d078089951000c0d6020b5506c004a0704c00744ca04623140d00c41c904901950088542544c40008080300e24020312140c0c6000b242c007410341644180c0c407280d1483d03640d08074000841c0c4d46d881c0b81003030004514003805211889a2100310960490304401c000a100d1507105952140c1040c000440b456081e111704115164510144481507132540d50f903038240c5041d80403015a5800800044500606103848508030700081140c102401070703610340b038003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 580816645 1250 580815395 580815401
    0xb030a03031e0207050d0e03070e041506050301020d06090c0512150607020319050d0314040f2102070e060909031c1803320f09240a0212090109030303 66
    0x5811a80800b50121001c1000e000804c1c8084c41403010b0000d01d0540d10018101e1100b5500d031611981148409012404940b1861a07005412006440c18014651408001841c4a42140780c065000086520095007250410300440e11061000c001c000d402800c00c8440380508011000e0307501100340410840f030120058419000350007410b01d490f22505d40e0002e803070f1005900107801c040e81c1a0208500b40031007403200280b4203000341401d1001c41d00c0e60044012000700144011301d40005034040005100c4041503107d01c055a09020f481c441d00a641f02954403926071050104001c0e00c0c40c0002d0704e50030b20700031042c02245030500550608001c1407c01011203e0510b000b000180d88000c0710140404080031400000e0003500d4110b58680400301c00c4c604a001c82c060f00040880c40c01209039408003140880d004500740c1071416480c0c861640008520455034202022500d64401d42035990b808140020b00600c01a0b4007102c5100c0b00c0c4041c200c08502690fa000703804a1341c50345080001c07a000b60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 580817895 1250 580816645 580816661
    0x7030309020a2304051e071106060108010303090512120418060b2d0903071401080a3b06070e01080f06030a0b130b070207170106030c120f050601030818040b030a0303 73
    0x4901540880b0001c030148586c03841103805000003407011110398030042043c401c0e150000028607014081d90b0646c2c8010744001b006100d418090040c1c0340204170300d600305002c82c14503041903210465030ba0307607a5110302000f2100c010308092250302d88100001e40000c3c01080704e0021101250040c01e45e42c419075603960314404443c0394103103142c0400480405580901109000d0800112500740b090220300004180e40e000801e40c1c0c10741854220703075004250032094607256010003a6440350744a850700c91205c030900b54040c02c28030340e40b0401c4140035205812030600d00315140c007079aa01e040d070350303540c5600c0b180e13060f00340d03221074164210b6003846004c910258546540072500040c214400003469548070350400c800c483d01070058100b200207008001d225500c1007071581045009012040c115241c20501d0700c2d1621584040c1e203403100e2442c0801002c810640803980e0000140d480d00d45c2d43e814518860fa0050000d08a88084604000b4892505109445c00d03024090020b0000340c0c0c495a007076004003210 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 580819145 1250 580817895 580817911
    0x50f010b09011e050d0501080328090506041d130f0f020105120a050405190b060402070606080a06050a0513120e12011a1005030601211107030309020a230405 69
    0x6000c510f807080384452540e011003a60383d00e0380e40d203000d10004403080700d1060b04550b909800801c0b1490481c512200c4a001c601c005188040c3c440e0a602c00c10350b41d800b010350180350042004140006c1d001c07842140781d11613141500366204940e88040b11604060580c61004124031001600c0c800815101e40c4902c148601c1810305c64580403032a038500003500c004503003034004243c0701c1d000c00003046821f10405092030440d96180703040301c145560740140407070f000300220f00172a8040b07102002d210164000b02c0003880702d0819128448243e00f489809823204440c00e4003d141441c0210f104450501044941e02d60030525412982a02940864400140000a591201e04800017412264080c40740002c003012030482ca50781c04000e00f081c08107500c2c10040b01010702000381f04200b056604410b507410200300b610040d000e0312140b00c5080e8000d1804803042244440089103641c1010382540c060500b0394004c441c02c40c0219a2100c406440c0243e41e1500c01d21034074a188041c0c09800c0c1600300c0d80e00040351b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 580820395 1250 580819145 580819157
    0xc0e07140408030d0e03160201030902031203010b040906050a051c24060305060c070c03020d03260103060b090402130e030403020d1b0f060c0308091903091404050f010b0901 76
    0x104903120464000b600400c07003c0d040080c0b6100a54114460801e00c6143c20b4090341c180851030404480d010f05440010b4145501e44cad541c01c7c110740c4c040c07015100c20882902c1d001d0300c03961120b072100ea1070f80140c02510b840c580350400210b09840c002024008480c2c1c0181400c1c00c000660f01000c054441c0d01108440c80c51040e41c13031902d03801c02640300d607801c0f0500f1400001d62a103035080052403c880500100041641041400c003c02c0008001c641075070303015900c00458100c14070b400ca0710b280c4405030b08611104100a0f1030701c601210940d4504903401004140700d010f00b0107040115422003614000d6118005140c00c00d50700c036860300010700d0581124252030800e03569401050074081075020848440c414080d5110b6207031040da80c0c100250060a903801c0403641080c0c4050001901d00c1c801600740202c44000981004042000044a100445001d000f2021519001c1c04010b168010201c03040c104510040c5182003511a5070300c5030401d6609525180d2030035a0400b613070390002c4440c504100c2c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 580821645 1250 580820395 580820417
    0xa14030405030d2d02032d0703081e0405070518100504050c071a010f121a13141f020a0801030f0c05061206090f07050712030e0703032a0c0e07 63
    0x1c07089040c4c100d070300d0560065556400c0442c0b10406601020358807813410210600c0c508108002042500d210b268036040c13060841d01c3c0c1040080e02c06d1303c40707125900041d40850420081203c08038494080b00d41c15540c40b11106120700c00310480c0b0004452103c071500701500700300300c4c8e807920303400094100354043c000926107003140d02c902403030210900030440c10f40b4a01c00100000302c1150001c400500c4180a081451041e40daa0b130300700348134842c2e5070a20b02d00300f480c08210010001d40303c940501b50300c00300e00c00c0205280c4403007503140d01803401c4042c0800c01c51940d1807019182c50013240c00d040010380d540b80e1184c0c00d543d210901550750b002c043c0d91505100c680803500c0e4450400805500259051740b00040c40e0100410038218001841250800c40c000140541c15170040140e0b001c544e8401940f41c162400c0c2e1608030010a49030861a51521515100006064109000d07440c1090316950040100c0d0303100184640703061460000501e08480e9240401400c0d40010100c0e40200b11858114400c01d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 580822895 1250 580821645 580821707
    0xe03030c0609190b040602090402040509041203050f0603210c0303100305010b030c0901050405061207060e040e0a03090b0c0712120e0102070f170f010e0a14030405030d 74
    0x14000c41044025a4008000d204140c2020406030000030043c400368242e1103090b594000032480c0c042c0005041580101c1d0200f000d9a59405403009014003901c3c1100528140c204512501464a40000403901d0705010482560b42c0700c01d40342c03260001a0040c800c20080000e0400c540980c44945103140c0400e10444d0001d24041c03005500640d100240c200d0801c0c11400e1080c2107640300c4541603c070b58810701410606440355016541143d800300c0c1c0020702c47d0340364000700d4484429483c4803241c81c0200c1401150312070b0040104011182d0039501000a0401058010398039094004080d000c10300184003080404644070082107448001e038152010241e03600f0090020524a81c1c0c12511b58004490301034010340c0c011960b05820750244000c1641600d0000729054190007401540c0300f0301c0521500d4050030204001c0e078145a03c020008128402a0140454544191a208031943c200241c02c41c4c0030780a0000694040d118018040e0620248078003003640d1400b001a082d5032005c1d040401e2503041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 580824145 1250 580822895 580822897
    0xb1813020a02060915010612020a030e0f0d14030f04060207051009080915030709091a0604090e160e0f0402040b030a2a12060b030307020904050a03080a050702030315010e0303 77
    0x8040c2c0003031855080c0b4070314080c10050180c800440c0b450304a00104400c41d8440d00c030100d0803105210042c1d070f07100c0c1c0b0035044000d08610286000588520b10300559900c00000e2010300e20400e41e41d40000c0e04510311038854a80c4010b50b00c910104081901203808244181e008145c2c0d2449001258040403840d400c28040d110318000c25218101d0104078005c0350f0509203114500c1840320781086d495071070080c0b030180080c000d6000d4042c03640c1e9075031542c154166000c841c025030348200820480d1299582c200704005024840600c2100b401100790014080c85192060400d6a204200c074041c030341e48108000d24070440003002607901507221042c10301c00381c609200302080c20380582040341c201402103c1406001340160029007042c0c503110000c2200301d1159074000e40c0c00707a01030804075540950700d000910310701070158007a6209189100388002c00c000011002441d6109441c2c540782540d613a6415000c6440c219600005a0001c000140e02560812104c50034101c2c141401c0748402240d0700424a5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 580825395 1250 580824145 580824157
    0x903050601030602040602010b0a0e0403320c010b0406120602030c04150e0a0602070b04060c06020d0c021b010e1e030111031005011b02181b0a0507030314010b181302 73
    0x72240e0004c3c0501006d41c0c20b0117080e0500c0025503018210529044200c0c510f070000800207420003050015000a0031441a041240b106188901500400c5402d1881040383e219806406c0c80e50f10341801641c041c2800d01458003151580b02d641281106161100c60103980000d1442006ca201044049109a00d100c1120000c084958032428038a042c001400480c081d00c4d08400103552000d0810000020500201c605440d0705107001c0c00c2c11591860250b01038020540d0300c24000e400c084011120700e0340003807210032000007610508210745900c80152a04805000007039007046011300c00002844030703a0000e00b070300000a8000a02d0b05040812224140c2003503882c91000d18100208025540e401008809401c1c2090611034941c2804d50001d60740003202200000320b1120000044c1c408966242d804460021100201d99107840000000f00907522500b400c5021902e0900c280c60f070806c980c0801070588601c0041030f45000050042003482207188501d043d030115030b00d08048030f224628009804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 580826645 1250 580825395 580825403
    0xd081308131d0603030a0c0305090306091c210e0a0506070e1305150108040218070302070b011e090e100e070e060d0c26031309230f07090305060103 65
    0x20700c0a0400030780c100c103030300d107441035520541e01281444816900402210024002c038100074082c0e61031880c05179518041e010180c1d92500940c400c000c0a1140801c10180503003405048c4c03503001c950405c0a845030460080404410b10310140e40c1004086070b036010100d0807404004442810300349a4540b490620304942c8000020f07031039403030a5164101980604501d85100d80144154500040302924424084020604114540000c00d05545601c4082084243e102c401420503242c5408040c010790b006042c200c1d0030091a000010301c411860360003002e91052003800c0d442d000d25140003400074100b01151706120740500002034404c05450310030710b0b0459141c10050f21306d540ca0250544070984004107101d02444036540b04000045401180f0400d54030b039904145100400003c1c01321251004a03150881c03031000090107104c0340403600d1040104c80030100244a03001c101c0750050b800401101042d4148009940460240403820900135400300303151401c0c888641c1d4a480b22441d000c0c081c0c1c800e030b03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 580827895 1250 580826645 580826677
    0x21042102010902030d0504061209061b050901180e06040e070f18050a0207020904141005130c0503030c100b0d1b0806060414010302010f12020a020c0f0306090d081308 73
    0x4003141010310004204c40c917141004c3c1d0034146003441c081d01076103e20040c400025681c600c00c03400c0040a03071003c400441c0c01c280c80f800039803c1311001b0b08250302024000d4003017000c400d4242102d503031041070b81041e0b1307010384440702254031003109000240012000c80f512601a14002140c0b0201c810184d000400c8507045101d6843d10940c69201250070290070701c842e59004018101c050f0b15074010254105a2000850f880c5118410a050400140c084800d06542c01e0606000c004540c1070402e42c40a8000c8418080d8270342c0e134034201543c80c400c00320740300025081513181c16442141e507800f2060341d200c060804014807800b603503081503854000408042030311245030203100001c410425180e0142c4191810021a140c00d201183c0c1540140300c003d0401011410f191301d118070404044181000290701591200381421020b51140c0622342482c2c0200c61002c82c00805260000b4886c0c040c466410250100d8201150201c0315400c0c020b00142c0c0440703101c462040001c9442005128480800b0b18007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 580829145 1250 580827895 580827911
    0x902074809050a050c090118051804060b030105010620070512010204080706210507020a060e01061502060c030f04050f03040e1b0a0206010e0601170903030703112104210201 76
    0x901c0440d82c01030215140585050100300d0140304a0048504e0724009080560040c1064150009038112580090b900301c214502c0300d015010403440303039034040c9100380300512001281d18185030032200309200743c000103104c40f08014409120302c0101d01c031020b40743c01034805142d1a00c012807100c20f464030551318660740c00601041070100610145c2c01500f018640301d0241181625400b4511404000a80002d990344001c82c4506000700040031801d80d0000c1d0034032030380c019400030b68001e24103441100100703803a481c10742070707610b1011803203611950341e594141d401c6444201c41c40c04400c0c0018002c403210300c00c1c0d986d50b04109500304040c200804050600310745d00e00c2d2103001c00245041c450a98550140140041d042860f004034243d81520103400d0b5030b100550f50b2000488488580b0701c18080c20341ea62400b4014900e0000c0011803003640e403a1018070a80d28151100501d46c82883d8983c50705480c514040405030b040c0740743d01e54010703020320282d00f503c408000103800e40b030f81a54001c90160b9511481 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 580830395 1250 580829145 580829159
    0x40b180f0106110c0108180f0f0f030a0c060e0106031506150806010f0e151303020a06090b04180f1802090c04180509030c06010303020a03080109020748 67
    0xa080c0034000c1c501c3d250b03034070520200c02c2030303075070002140903505008074440081e60403c042034281500c82c079402c00f2916070100d0040c0d11a04d40d1107800282d102e0780542c80d4070b1241a10000200d46001e00039a807420048202911070030010300c03200b41c882c80316540f59403000001c2000799a40345c80901c400100010503629008481e02c24030108d00700401404515001c002442ea004460300e02c0d440c0c43c03814182c0317400e000703900020190116a00746d180348180100314240302d144c02580041c180c80c400d4603051170050311070000b40c0c2c040703039544649083c08c0e85c2000103001d1609091000c40b2108d02d0312101041001203002044141c44004020b401c40f685034a149130305519151050503001144107111500c0c1a080013104d480d0641c480404080841c0c031000401c0036404208100d0340d1000308081622025612454000e403943c2c13801134141d001071000030000c118208680300315021150300c030078228540c04820440e03089111003e004030b080c4039410441e0280c0303e100c0b03108500340c8102c0403000011550403d00c13 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 580831645 1250 580830395 580830421
    0x306091407120f0807260a02100608120d021c021c05060306070311040b0a020c12010b010e040b1305091c0206161b06060b0a0f02030a020c0f040b18 65
    0x444a502d00c1065000d0901080000300c0b00e01003aa0803103000c1e681c844403030078605982c450307001204411404890344c0b84548280035000d03207420740c4140d0035140c003520055040e00644407140191359070740e001a2a04052424a64010610203000349030140c10400c96410015441c10038541c19440c0c2da0f00051a0780340281a004485819010484100400d08000022030380d20007005100b034003810382d1094801030890900055034000d10880044035074503142c18000a44605502e10720034003075040307000100301e0082d0601a4001c040c0c01039403004a040075480800000c2e0003d20040c5420828000c074198540707074940601403040d24144010035041c0603020082c00700c801e03041201d00031074100b6800c0c00f9814441c0c0d02d800c041503440e490001d0910501622506800024000042405142050002d0070201001c003070140c1d6501511204048017030b60b08140e132280700d0b18414200603004a515a00300d80740c041c0c22844400409040000d800d24080e02060018500b105003603d0801604204420085011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 580832895 1250 580831645 580831649
    0x204080718020304030e0906061b0703110a0317090105040305101e02070b011202030102220303020c0a24031112010314010b06041502010b102c0a0303180306091407 72
    0x881c00c510354600381c1c8004200d0000030101c144070329401808604c96958180c15100d040b10b0030324400707500c091540f400c1903403072555200c1100c21036a450307020740b554a040c80300401120f030042144110b003a100c1c00f54580641c85085182d05100040c040070002c100d040000c3d8201401e21030740000d840e40b08900ea250602840b203014062a4010400d082c001840401014111212147c00302c690505600c0000c0c060300810500e8203041c10481d8119100704140d42e5408101d0b07000344c003a01c1004c2680c0050020300314950040600422900c0c5294911550107414107030403e41524000a51640070384117000c07180d010000382d0b00719245000040c030500250304800d404804181c8020001c10040b0b0010031070314002c0b0310801c4540f580301c040c3c0c4841103000b9001400140ca0041007010014410580900030051044443c1912500c0c0038030810007004800d01c1c200110001444401c49500d541e0301210301400e1040445000004541e000000500c2c078010200340c00e1089503800c400700740c0e41c140d03d80341c0b0800c0d07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 580834145 1250 580832895 580832939
    0x14010b04050a0603050a0b060310030309060c02090f18060a0c090506040807031221060e0610080c1b070b0702280b0705030c0d050a03060e010e060904031202040807 72
    0x810082000c2d5035000c850004a51043c1000f04441d6103c1c0702080050041c8802c554220500104000c1a5a0030a40c42c400b035901c80d07190b90300140c0c1c68101c1101e81c000c0113a0003c1d0095031070000300303094004c40b81e42c0700d90084c0882503400c042000c8180840c2050002e5440c11036042c3c40c0c0c407440103c4d907006408c40d400742c4000d4400d182401e1401c4034607641e8080521014101d1032520840800031441600281c105860030f001028290740b01c04c184000601c01407048181c8402d03501d010841520300040d4020001455694190050315100790f0500107a00c040c10203000041c0d0000c005080d04800d01401c0001d140703680c0e905481d00010700500518620007440440ca03c505c08540c1020490100300002c03d4031080c201d840d03103e40043c48c06c03915500c580c210540291003408056511994810001d0130640002da8092000ca070ba1a0501c0d070040d00c00b80510302a502880001903458181211002c3d44280649030a20b4041102c1c101d20089a000b50800f00c07980c1c204c600280003406042c1c250380d1607961a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 580835395 1250 580834145 580834147
    0x4090c050c0703110102160f0509070503040203060403051803010905060702070e0906161103030f010f080c010e10050424090b091c02010e0406090f0b04060501051801020114010914010b 81
    0x1000c461540780c0b072035400b00034005600200c1c004001e901c04c1000300980e508450522001c81d4655403a070a0381e41da0381c81034522800c5100c2c00940c0c158400c4095070301603503003d40101016103c0d983c00780c44039002401203948200e41d001185450355006d00400b0507040c040c90180000d0704013584020708080071904451203210450b014049136043c0060b0b801d60105418030401d04007031000d10204d421804010340403a4520000c402c0c0702914501440950498a00c540f0400a0a655098180d111500c02c035031940410000e822a0340d550400d1a080e000022032490010f2800d92a00541b44036007064010800300164503c03402c00d207090b005214031002e02006c9060074100020040054510702e500c41001c81c0c0200012030103400c40e4040c8440341d0180d10010401d000301c6403a6503c990042000031040c100e112305160a40c1000d0420784500b000340c40060791203500c2e0009038030f1548101800f42108904641d42c82502d684210080e05105010b4044150b01107965031100900060242041e0000c1c0310200d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 580836645 1250 580835395 580835407
    0x4030f05011409071715071d15070605040c030501020c0f190b130c03210215070905010c0c090f0506040f0e07062f0f060a0501050a030809040207050d0504090c05 71
    0x18000440380121860761000c2101022185c0c140c40c00c040c1c080c403441c1340d10701910082c8040c11b5005880c20425085480c4141103000002c401c0004030102c07429030070100368081085002140e40ca811042c1d0290080c8003022140d580c17591180d08a81c00850901c40c140c0206103000d036468000d201e08440300e1110403c81030600d5590300d5003582903001612040300340c03605030240800c0104020b61074009580003100e04020289400031402c0302042c42d01c0c4c03c0d0050140100d0380c01c80120302f400711fa025080c00d41c0e450403164144001541c4001580380c2c190384090300180005011003040c0100c1c2d5052844200224950800318140400ea038400741480c202d041c1090020040c0400000c0d4000c1200e10740e1500780c120b10f180100c1c003642c100d009000d100440320803420318507807528001031840d0041c140c0001c95402d40d07214190102220340a024480d0700c0820720b40104080b6030b4000c00f07044c00680050005140c00c60f160790311071500ca001c414000c0854030202c0c0800c0041c00c1e13882008480500790a140d80351070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 580837895 1250 580836645 580836661
    0xb18010f05040f0b030706110706050f030f1801050403030f0b03010b0d0201030c0509190501020d2a03090b0a1d0312090424120b010b210402060d0204030f050114 71
    0x400c060103118010b540e200038107400802103422999040c00c02030282e6422680300d500040c0f1441c0c41034624450380c4107665000660030b215030101d81100484480351400e50301e60241c265440c50f00946007004120100000e200c00440038810706005602c00d84001030101003009000e81640c00b8104030504c40e134903044900e04035450758500b07020110360910703000600c100004802d448a004081c18603400c0507101401400085002c00c1001c01c3da02e09030221090340701805001c480c010300540060303520610180d2103241c51400c0400060341244603080800d601502c0c0c001e2103010340c0040c1c8030380001800f001d82d0040c0c00c0750890300d41c401044c0c003a0302509012020350005226803242d040210702a070741d0340785114040100014409049140229a080900c0c0e507003500740c800c040c0d03968060303c02c0000c41000260101c014030441e02461011144560500581d141d031003016040140142e8011504110390002c01026100a0000c0c6100305c25003d1802c81c54100070f42122000c080c03047c07403482c6500510070380c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 580839145 1250 580837895 580837919
    0x18060a06082508030403200d1707020420030a0c0e030c0906040605060403050a030909051506031009110a09140a1205151501030c02060f220206040305010b1801 70
    0xc280c40580d502150502ea64801030300d40310f600144590001040110410140c05407004400b00b41c026842a174019503820000405141c800c010320505140119a60022511000c0d0042c24001000090b904030a4100b10002003031041c903620001600004001c0d0030701c0d952180090b4111986041d815031a007850110740d03100c0e00300030131501c2040760b41d0008100d0f50b200d421180180001400c140d455950300d150407907603840c49210480124400940c0414180c5092281911460005081c032803110311001c1480b1140c0e1000e0841074031040b5540c0b01050250950090380000650184529a42d003400ba000620b004180e0f001000d038550802c1103881c10356038405802050355144880000815007d261086c900f0041d0150752007009021070070040c0d1a0402c801010003c5402e803010b1100200010040707840c1d80c021180700c030b11a00540045280480c50058100d2444840e2500249040c01a000681240c000741c0c01107074240c2d11900b90400a05080c1d41c164008052f28076015120b5040a88407004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 580840395 1250 580839145 580839163
    0x905060f091f0204090f0203010e130b010513140411011715120f0111030a0f0c0f0e0316080706030c05160204050c040306140702070605131a040e18060a0608 69
    0x140c0e541c0000d1641407400a681228001c081d420020806903074001c06840184d000ad1140303040407102600000c05240c02c6541d40300c1c100780d000305206003170b80c2001304010498840101307034000195100c043c4c01301c2e4024000c500c3e028900030156a08088440c0000405001c86461036207503151140d014405012124495420105000c9440324510003c500340345240c00307075100084c0115801c141900c040142403200a5000391614002400103005024081064079022a40038002550420625480500ca42503c00d11140010156035207040b405503004003000007178010000e66017201c0300c00c1140c5078040c820f032851420641001070030b00058200040350160011006405661181c000a8040444904032070240d45d00400400580b00d030b55800c00b03103546088558102502c40d01c100400c0440c06542a2000d007e0440c02c1e603418141000c1e240030408802c03001102c100941130001048104408440350301c03914040400c14480d00700310510628050700a40740c0000c243c6001000c2c015601c0100343c03220 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 580841645 1250 580840395 580840423
    0x301051e06120a08030112120e01050901032c01050f0709051c15020307020f0f010621080d020f0d0b420d0e10050622020c030d0905060f09 61
    0x2100b0780108800900301541c001d401018040c000001054100c00310135038035030b02c41c000c0402c80a05d014000b002c0d212007040c1360300c007808201c060003055565882504841c07103010034809403080c600300b080344030782d038241c10008171240301d035161420007a0f0440305d8000765074003c00c0341c6415805c4914150208805081d0304e1b407190702c2c41560040c0201407080d84e00328001800c040500c21903481c83c1000c402910b580c0303a01c522003c1070080c400d803161441d07014080c40c015680d44c03810380081a0b29090018440525040e8200e0b14243c00b480b00b40418607c500c0603110200c0603c000f04d03541d05100590700112807d540031a8411070741c00301e420350340b040300003082c2d801c45081d828851200c445441c15020030b00c0d0f01ca0703008041c0800020f114103502d2070581240740808112402c9541c200c801d402c5190a861044585a4000c2102d010300c101e4107a000e401c0c004110300a01c00145031001207040982154407518040c1c0c6400e8451040d0301c07c01c0005c000d8a0380c4010422103681d040e0601c039079041e072900c0c08100100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 580842895 1250 580841645 580841659
    0x91a0a120212210301030b07020606060405060912100b10050f0304060504020319080406020d050408030901081f0905100506090916050906030a05060f0102070e011806080f0c0301051e06 81
    0x2460b0308100030400030b14080901070f9440301a20440c1201550007400119281100840401c440c540002150780c010f07407004000c41c4c240b9041400340045038101c0360354a603000c90007503c0c0d51045442132040800d4503001c2800400c98200d24810311045042802406042100400c508601468800c05583e00a40d001c0c4c404103070381e16680002480c0000000e00070104c080c582d0484000c01000d2170003801114010f4003a03601014618400743d50901035445070030309640040044464541c07260305000d520115088048415910b41320343c045081d4403542000d0f00140e954401e00091501e4000840002c0c802150800c4c501040f00c000702e00d0f050005000600c05095102130160480d0180c015518a0100070300306607281c1c54071040ca20003400302500c8090040322455103400c1e540d440810300100f911451000d00000d030346010041c0414040c2d103080b402409559407808034414a0a1001076071002040008040e5868071504041c2106d001800040030706d900110149090540703d156075600610817642c032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 580844145 1250 580842895 580842919
    0x50403090b0a0c031b0602120403020705010f0915110f0a030e0a140409030302190c061b080c0c01020f07030203090306010e090c010e0d1b0612060f140f0901091a0a1202 74
    0x1c4101700c1940d9200405081c00496a034540f91480e19409105034000d03030031144801e81d0340f0700545d000060907600710001980404240000011202e0314440c220b4149058020501550200d6080c245040c400000c0764109400b600300b410b81c41084070181d200c085588808051030700d8010b60030305600b45060343c082e9880f0580031080c18080e90580c3c41448001000d5400c0c003203022002413025030440c80c2220482d140070700342140c2c100707914403448807840c65031600d032625152402d0b4081c2e07a4200b50f040c40703280d40d020018882240490030140c000f041c8a0b40081d0386800d180d0f0308044c20010140c11121110140c00100104510b001411070540c00d003c0c20529114a042c0700810f22150031403101030101c400d24044007415a500d960a00b080b42c003103941e400c03080d10940f00c001c2c00743c070401c0c440c420050b00f07507030414040000d000012034a0000d00a000d101c212000c400401c8038040d00340d00a134041c2e03907030312a40d0803180499801e07040f0f43e0310216001c0f00c400d07090130203030000c0c00c40c5010003038051240e005007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 580845395 1250 580844145 580844177
    0x605130c090806130b0108060105030c060c0c031f0c0c020f01050a020a0602041e08150411010e030d0206060a0f0b0a050919081c08270109080c01050403090b0a0c03 72
    0x344101511040c0300b0b0f1100c82c034040e005403190a0842070f00715044104e14000203400000800e000d4103940e80100500201e040940401c03101d90045880c8214900402801e080980c2c1d08222607070105142d5482c0e04446580c0c044a44110b5103e403080c0340a0008540d18000107036a42e4400700c0500b002420003c0e1191f05814080780307082e544000042103076100240104044040c52076001503168201c1c83d4582c100c0c3c88400d82c0f0340b1411403a5070640c810390045d0200300040c426100c0f0b40f99180e011302d00b103101350034800d00084c608a0410480d50150b0840c0c0e060000368200005180050800410b0000026142201c488054850300d040502000000300e55a00191784a0240101c587e0100071039007038040d00c0e03111450300c82082440311020301240c0910340440600038544588110f419030740b60280780858201000c65034070b41c45e241084555039801401e000600324000b80403030232201400041c0618003444e01a08500c031a40106d07540b000140107804c1000d9004602200039541407400d40841c2841580c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 580846645 1250 580845395 580845407
    0x11030604020d1b0e0a0f060f03170906070618260f0f070c1d0a14041202120403110a06110d0e0414191104080c150705012d0605130c 58
    0x2c00704024803024080445c040b504421001e120303454041200c0d83d41c4020300401050382d448001c0c41c080341003081c142c07584240000360030710395400b5003c41d280c0940741c0d8805040f00c519030f08101101005004400038404c40000c0c00c81d01c0140c004401c00d0072001010ba03e074580c042e000141e00b08dd07030001204681000c1a0066806450b4001c080403003007034981d600c1d96005e00f101c04c41d0201500010340003c0002003180200e14004078204a85035480e111a1541d01c8814400c500c802c003984540740c1c00028910050006200940c01003206661071440103041100300100e07075000c1801c01c01c2c4a02c3d0000000804030304c440420120303007443d031180c00180c004034020705030061803445041180010000351040204025640001c2810100f103002c4640701002d8041c05140115001780d4400440c0100505049800c030f0315200401c50107600f0007905070344003425200c1c4980300381a00412030401600d030a201d40103125034084270306000c2c0009803c10004c640106881c43d0f40f58001500c4070640070403280104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 580847895 1250 580846645 580846649
    0x118031e052a0a0b09060108010506010c030c0323040f06140a022d0a03050c0d0f02070506180d1a0f010e0c0306130e010c020f071202040b120f060411030604020d1b 72
    0x203000b200c682d20302041703596243c500900ca0a1090750906000414035813143e00a4070005a05807250440e680441d10100c0d00000d40c2d0401c410001154851080c03025002e80180005001d440d20030540c950170440300400707036503114141d803119400c1480f50301c08285e0003041c00007002040d8100301203811a0300d00d60b440c80c50407183c00240d1381d00519400c6010f042c0d004000b007258082071002c0f0350640c5400c401c101e40382c6a080601c840140c100c62410f1105240420040c0090202d1019080340241c0400010742440c481032800c640c80075110701195628440c41031007a500c540303140213203013256241c0710544000000040041c01c0030000080081c655559540c0f0b0401c220042c03203420024480c195003424000c00712203070014050b00c00d1189142d80c1480000307601c0256000710540a0800d4629400d00000c0c001c404901c6a20411100e03000c0c02c20042000302d03c09611342d1070001c1901d41007904141840c034001d00c030345034003e800c01010031016032034150509002a034000d40083d82c8082598a6007501c152075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 580849145 1250 580847895 580847903
    0x9090f06020a0e100e01080c0f090613060305010b030115080a1404052b14090102011d0709110702010806130e160e01080313030f02030118031e052a0a 66
    0x20900d1018103a002022003c880303000d540a480482c846101038400200304010b460000304038100045110a0340d42c05801918840070300641080c10134400140180c011000d41d114011281e0810051a907050050500600c034010003246154100189414401c00c4d8800c51070500044d03001152800c000795000c80750842ca860055422800d05142090f118040383c244202d600c03804424041511490040f04081100182c585041c0096208a0000290044110b146c19551b8882d07804401c0b80c40311a510030101404406040e0050800001c00b0071182403029484413140b0a0140c0710050760070207001d9800a0084074072801c843d40c1d0f000f6900103400103c504da2024081c50004076000c00c085107090003521031440310544181c1e02e900e41d50b60340340200480d48007003080310700e070070004162194021000c25001500201e84451614680c0441408924003180001d008101c070555086641d00d00b0204410305280c802c0c50104405610307032018500d0070b11900142d40b064141103018804004c00c03001c0c2940 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 580850395 1250 580849145 580849147
    0xb03060303091e101404090e0a0b01080f1902090604020310150f02060a0b09131505190b04060302030d120209040609020a12050105010827060c2104020a09090f0602 72
    0x3050301d2101070906011114001c132004110034500d42c1c02800700150000380c9401140c1007030700d060071000140a080400144500407102e4440104904540c824060490b01009110195080c1d0b4104d1a0004d4a0031041c140c0d410130082d200140c0d0b50203030007a00880c00b03c0c1c0250702d1f501c441030401104085c40d8800343c280c140e001fa82d40f1129070809043c00515016400742c5401360748048050090301c910809a540c0050b104002440c030400c0525450f0905001d0303200c1c103000284c2c060f02d1208441c0103498005c42d10310b18410101c04d9045500503481e114400360b40510680303107154086555510070000c201c0502003400c1d41c4d44c0c403010031541507801200c002401480520350350841600254011310040340001c600c0c0520001915560242d40c0c102c41041c1c0d04c05502d80d4401c06002da42070300c6641a442d5100d0b81150b40c07041044104942c50050301c800340303000c1c0c1d61010289403a010600e0310301103000c5003003080c00b0480560340340130145040320f80d15840400e1051040c506501401c40f00e4400800440c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 580851645 1250 580850395 580850419
    0xb0c07060503220c080d0306080303130f08070b101e15050903010911040b030307080a26090f07080d0923030d0c0b010504022704060b0d20040303090b0306030309 71
    0x24003103004422903040e10705482c4c1d41002d00004070188da0700c0d4001c8440561040003c1107209110302e291051060148691102210003a03940505c0356000500070351741407040300c00b0b1000240c6003009410003030200b686201d03540c100c004811034580e00107114040b03115007415074403d82d0b030313014400300c0d80010300c014002c00510126182c401c10140070203d05c0d40c01186070a001000d01d090000869590300d81000a41d800e0568a0304115480c1220162941042002d4882141426040021640a0300c18403001d0030b15000c48547c5c01e0b1504050340e1106c09075500021203a0000d5401200420958500c0c0800d002008071525100c4841f80308052056058072071104000c90055101030980d603405c0c443c6030f60072160390b81e803c01c10040c5c5c0104002e1082c440a40a0702480c007074000080d050004d20080d0000c201c05503205c4070740e8890b42001200d01d20341a250304140412803080e0016025503040100b4240c14141103860082c540c8601f8040e003102c0d10400400b040361981c1c2041610842a0001c000704000c0e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 580852895 1250 580851645 580851653
    0x7020c061b010c110312060a15110d030203060f1314101a041a030a140a02070309120507061d060301090c0201380f040e030403020102070b0c0706050322 67
    0x900d4100072185103501c1c000b0054962442000c01c1c1d4602000d120045040c0340200c2e41c06214104003a100c258001b1480600181c0300c10524120310000086442c0c034486000000c5c0d82d141403001400c116020188100100701d5142d80700030310744a59040c01e4401844c1ca05062000c0310050075150700030b42002c000c440400400f04451143d02041d00e0075104100c4c0c0f0300e04540c034081e5903030180707015440c444000074180c44000381942020319403045065102181c0c14508801c0e49510050030740303446800a80025050041c5070f0003100e050300408a07810f52580b454041d031a41c1d500c2e101d650042c081009400000c0c00e5100105d07118913030f1404002004240e41c0d5035119130480003410403140900c0554285020744900301c1e00320440c6003400416640c240c1c0c030048140e0704014071556098680c0e80c401c4603014005c200b5140c0717114035182d454800c401565a6800c600000e40b8001c0554041103030640100b208485840d000b059240440b000340c00c02c40d4881d12054120303214107000003c550001940420303601c0500c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 580854145 1250 580852895 580852927
    0x1401030e071e0e010605030f1906060203030106170c0403060b2d04050106030c0e120109050604060203060a0806091903110a0b0a0513020a23130c030f1b0807020c06 72
    0x10181c0390100340b4001d50340f001070f240e22810921034240411300900005a4400c0380e049000d03031003c2549901400302000810000441d561500700e10010b82c80480180320325a0010407401c80c5001e0f42442e1034003032070300c0b1100e1031462080f80002043c464481103245400c1c2ca40c46c000c2c0030074100104a0300a000c2083e03003080c003039200b8204131901c1107040400002c1c0b620300920910403035145941d00c1c1c079442c0040c0e60a00583d000c01000d480c255650381c00303841c0f0120324103000d200c1c001c1d44252000340e0f0b070342894410840f80210f16001000c50b60820b0050105050740000c81c41c5407404060100741c003002084c00d047d510007040d0011190140034481c04c00040040071203030180701e034500d040f01b0820368460500704c1c005114040c0b80290002502d282c1800300c0d02d42c000240c0c2e203078841003010030b10f0b04407a4030106030040b00292460940e02c1d1141980080c040c0c01d40100c412441c0c07001801c00010180c900800c128030340c02e03014107043c44040070214404910911a8400c034041c0a46020b5507481040150481 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 580855395 1250 580854145 580854179
    0x1e0501020307031512030e1f09080d05040509070e0a0b0c01090302061506040b0c12070c1802090f04051005120c09090c1f0c05100e061f1401030e07 65
    0x1a1a0642d40c0c289910f0421801e0b0076280c1c003080705071178502103940030b580f8030003950100342d4401c1050f18943d00c01305202105d02c07888a41d56a8095115241c039083c140341c400b92584240034002d0900061007540c40300c40040d40d02c001280b401c06206900030010981620383ca8012140c00d80c0002503100d4040c005400180e109840f942c201e44180c3d55000b100c00c8814011150503601c071908000c03c114147c079074005841c5c004155000d8803540c4281001c400301c0350f0b00c4103004680341c8404010401c490f842c0d0080107013050810729815450640aa0700040900d00c040070704c2485a6038800c04103007074000c88081c580c00b42c00c01030005185011309001d071940c2c1c2c400d6807004510035050040042c081080104101c1090f282c081c00e80d403501d51f00b845403602882c1000c003008003044940008280440c10412025410440c14032000495800e409411410450000e20b0300000500e29035201c1c10a0307850b010403004860500d0000c051012400004030080e207110701d081d042c03a10407900f01103a121804907210031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 580856645 1250 580855395 580855397
    0x60d0606081038060c1005070807020d0201020c060103080f0c01050705040906050a051507050a12180b19180b1c1419112209050603010e191e0501020307 67
    0x1420070003200c1c0300d944107240c55408443c4030345024000700702c5007880030162643c520f01c80c0540303801018160300107003154411100303c80000c0e00b990074080d0458043c40740c3c08a09800c4e10003580307001003250209640e0324062000800d203d03000202c0b84508650340c001d6420141e4220000e004600f41210024040e070800c1c000e9003811443c0460006492030301c0540a0308070b0340050150700d805c0c681d428400130103800c40d620940302c0c0d0152660690010b50380c20204691200c042d120b2684802c0501d0500034a400d00383c00440308580208001000220184520790800c0700364602a02a03604040d159003004000e03a014856500b004161448000c0325486031400c0314540e0300c0204031100303c4080b288104401034844240f044600c0100800107076040d000300d0082d80c43c4110441c900705039040300ca08900d00c1c03031100a1240006001c144080c2400d03001d10754205c3c0f02240207100ea03003129a40c258454420130854a81020840640010022420301c1c8480740102c1c2d8035510807003881400c005021794001c5403540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 580857895 1250 580856645 580856681
    0x1020d06031e020906280303050c0c04050c070b1819060509060c030a020f0403080c030702030c0102030c1e240405101406061e041e0906030b060d06060810 68
    0x200e1007020700c40030b15030001c2050341561585420300c42e80441c00c40c002c803071455107107040100410342180d5540c0214032030b130f0340c1c0340c1d4850318010081e003026404940c80f80300354142001d0040000d66002a41c084d543c00c005002d5503030700c90502840304403c24015886490060741801800b045880c4040b0b0710300d0380501e20600c40e560340d1080700390300c0f0340c030442d50307010000c8040c00410711803d4035034003421400300340f003940760b10b000e440c0c0c7c49584a07500800c6074010700d035100090400840c2011303c15600010030070700040d421b00510300135558485403c0000c2d0132524034008894074a0f120100501c90002620034240c40749511030002d42540c2c00c5046906442a204068003049241103a1240540b03005001102d140c03282c07204030401003c3e901070754000142405400071402c400305a07070024001000003c01c5149000409001504103080741d9003e200554a032980420100c1c3c0060302280d40007200302c881e0180e01c101842d004000301800e80001c40e0718032411080d0480d0700c4142e4000c0007800c480702d50318 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 580859145 1250 580857895 580857923
    0xf23010803090603070c03020307060908071b0503061f0f03030c23070b07060207021809010c110a03030905100204092c070911040504090609113102070501020d0603 72
    0x541d41d00ca02c0d40c84541040041000900480c0700f407410a204a209205692034144191918401c0da022184144c7d04920000b6212003001101000300121000381008030829601d08000030351940d500800a24581280c5181c1d41b8021040c50b40031009004405001669151603003001440745140d0103003111000791942c0c1c4000c3d058001030300c2001c900a0007004100d03650410b90060784035080110129491902404a5030050380c80e0090f84031b480c0304240010045181c80c03c0c003103081d2801e40d0840028444480c135001d618840110780b611860360941004116100c151800da031404a094109c032100610100e40450741146940090340c0303e1605510f02907426008800c0e0042e8110b102030030003410703032107600200800011380c0c0102070240444240315013015030fa00c0c003103400d0350900c8008441083c2c0d0f540c024800c2240c1410301768884107054441c0c845011241811024441c001201007404070404003200110807074507011201e4031a0301070300954035000e40b064282d0103400d0601040303036240005020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 580860395 1250 580859145 580859159
    0x4090510051b070f03110d121139030c160e0c0d05061212090a09090203060106030e010213060806010206090d0e090a0e010e030a0e030c090a0209040f2301 68
    0xd00011a02503242c6440c0002d80e903030304c14032141300103800c4092100030b01e24004928024070102c19600d400f5100c81010f00b001001200843d20100d07001d900c500c0c0c090040c4440c0030012401d001c0c158200f104c41009541071003221040c81094400446113510000550040100000c070350f9580200c4c0e0080c034640c02a40702c6840340fa12080c1100c0184844505021000480140c0e811003a00558040c00f000c420590410156040010422900f2526240040c88401034142151028000d240340d075020018640640d0000c1e88841c0c0611442c01019203480f9101031500e0298122906500051013654169680300009882c456040320340310301501405001441100c00400c0b0a84c0040990f920184030701ca43d81e0070820302e008050800410326680b907569000704542441f1f45801500c031580150384840103644001c00303240301c55044038042c2d00210076185040c0c540703d02c425000340025001588a9082c04003190007440b414440b4021a070901d050805500c0501d540b0910f00e04500d48615150b80c3c940342 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 580861645 1250 580860395 580860421
    0x2120106080706091d130f031e05070311060402011e0201020919030224040915030605150909010903020a0b041e030503090f0a12081807060810050405090a02040b0a050409051005 78
    0x1201003810500c400700c6d400140c10340803035600d400d22906041407803a0191520400070b6124082040104600040000030f05411214400c843c020410043c10b4510307180d13000900c001c826a050240d0034980e40819958503000f134041e44c252003806010107a1504000301070407a01c07261480180c0c0102f4130703407404048008441c0540b48a001c600101c0c50b107031600c1c10b88600300400d0001c9076039080d0002e5400100001e40103014540c043c0041214008060601c8005c12000c0000a01003071001e80c988540c031000280c020407038101c01900f00c140381880d030750340c0d0904194001107a80d042c428101020b0070481010742103409980548024405c8030202611141c0c1c1a940311260034000d41280c0407401c1c10400c0c98480c580065000c0d02c0035140b1481904150221031911000390401000b142d950030400240d070300c03001c84482c010001220700380101c2c140803110a40f200d04454010f4050750312a019100c40340c5a40e4002d0700240302c013410400c1184250306103192200307495214801c0b82d6045c10080303024911540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 580862895 1250 580861645 580861651
    0xc0103060905060d110307180203090f151b071506031203020903030304061a0307030f051006061e020f0a20090708070c0c090c0c1403130302120106080706091d 70
    0x15080382c13400c20b00d44d1209110400c0300155507515206405000c904030701561646808000400e60150320b03400c011400c1424142d90b002180c0144d0f000c000380349100354903038400c9070b0000d60307078005c80d4404078084d4078010140c450f12901411803001c4440c40c450403071003a40900100ca0161100c02d6010006401c00c078180d10030841c9090303041d8010300128000ca0071319800840041082c8441100c0070100c1c00200b41007010561040e02d1000d5441c2c404c40c2402800d000c0c1d0507600d6203813402000418180032010300304000d0190104654000c00e90800c60313490007003186a10300d484200440304840080e140100424814950044a0b1412a6044400350820030180390145086440b1203215507203400c0304807003000c0007400a44445001e0303100010383d1000c0d8492181c4445460351024103401c901d041a1100c1d414546807141154800c2003412817540400303030440282c80d41211102c1d4150320410b50140942116040350190340540c01c0c0c0001c5403078203d6401821152050f04100c141104410300d111144822 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 580864145 1250 580862895 580862899
    0x603170c06061f0e03070504051906050121050702070302090c04080709020f03040f030311160317012301120e030301170a150f09050607110115051f0219050c010306090506 75
    0x51803c8081d842c000c40c58140145409400c60798646c1d81d0b4000901681c10540740c6900c810703166410070140404034000d020140a0a003842c4410f001ca900c0c000b00c81000d0650815102640c4034046050180b0900c55a8000c603001001c10185040000018400c0d80c403074402d0006d00d1184440000700541c0500030b582c440044081d001d4110398950b122040d0301010030004504250352401240e100b60400c001400784c621142032103030783d44942441c001c0d000150700d00001985103280b1004100112403200f180c0c84241c0082602800300d1060700040e100c820741030070a840c0d40ca00702114552650400000f81d8100c80c985034040e40329622600099481c1e00080340003404080803190310030004c50090f08070003240125400c0001e641511a2101d9007407800c142c0b8507070300149907051000f81500003409400d404100702c41200c0341d89232508000604030381d01d00740c82c4803d0748603030030100740e41d01e0080c0958404c810900b0850519200750b440c04035200e082d625440340c013081c0b802e01d0203d50f2000d00d1007514490500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 580865395 1250 580864145 580864189
    0x25051c0f060e0103080a141306050306041103060f0f0d060e0a111f05070201050702041a040510060206060d08041d0108060a0b2d10080105030d020f0d120603170c0606 73
    0x3200c541101ca25407484403071100d111080006048280c0d100080788c00401060742c030280c0724140700d01000189e801000314240018400c1c41030012a40e96081d0403500c1d594110b916185d0701400d003000c9954408841d07005401c0510703080e0048000c580108100c04071074032810814507421044001c00c2103c006440c4210342c1c80d0740d07001190f40e40b94040c4004180e00c1d0b0050503c5402c21595500103030603103520300b4007240840441618a005c0341818010960000c1111581e00c20807410000000d41c4c0d5040101290700ca40702040c101010f00880300111000352150303035180b5000d4901c01c4898031401d5000c0c8560b01c02c0e0f10816001035050038107442403142d4603400525000c000241e030840342c106102408000b030350364803901d0850318090380c0341d0090000c0700070300741c0711000b556140c04109810602600070b0700c03040d034020000d2050311841c08a031800b40744902c0e0901c800741100c0f00340d642008000c103810050041d01020502415104001e002c0c1c04011115400c44800307646000900202c40e0ba60050a100d85072 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 580866645 1250 580865395 580865407
    0xf0418031b0b19050108030c1b04020409180b0915070c030207170a020102010b0303070b01031e020a1706090114180316111201020325051c0f060e010308 67
    0x1200e0624452890186850180210700e5070b103500c2d0001c0810b540d01c581407424004078a40844190084500600300680510305180c240d117140c6450700f040002080768000311103100241c1c0d0345c460741554050513130804100621226800300007030514883d2019200c00c1498400600c0003140000d80710480614500340305065142c2403002d640c58200070340700303c096004070700001c981881030081011100400703000402180646000290848002e00c50301d50182d04100060b5010443c020503150450741e0101081c0501070a504e0030321540101400b000b907118120020019080450895801c0440c4115040d55860340f290914a42203d141c01c05c900c14000e030001c0015410785441c103005001070512000c2d6450240402c2d1780d10400e02001d001292040c0d50211003580ca810520754081604200c10001c51070340c02d0100d803141511000f81c1e050144903041302501c803451489001642d406940340655040900c1c032440405002c0d0031f680f1108880369103031000003e000d204845d02c040c101e07904032401c10302d419 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 580867895 1250 580866645 580866647
    0x714060909090a05060a15050d0503030c091503041a0f09071505130e01080d05030114061309020315040507090e040b041410090c0b030c0d0f1107050c0f041803 70
    0x60040410318a805545042d402188003481180d03c184500c410000380020011f25014440c48660040341c0030f103007000b2901001038000400c0780c0d042020b07100855241c03030310b00c00010100580f80740700d03200708034000c02070000b004000c803001010f06d00300c40340711901940d0740703100202240000c4a1039001584102e1042290f0b02200c004050541d1291905902d4010407a080c5107409200c0d60042d4074032034003100104007044050200302c1443c1014541a803542d40b500c5446e104000c00504594403c80b00024008029590130b000f540040490040542d00c0e4900703244500700000d001e050860080e070a282c0060a000e1080450a054441c1e2310503107002a150f640b200342ca084c0000b4000c6482d00c40d80000142800390070010250194400394005c40c483310700303282000342099164400800c50000f1700c280410310002106542c0542c007680e00c002141f200d0781001c0000381c108000c0c0c0e0310384550000340741c1c028041d0215001e070400d81c0a89403500c41149003000d1004440055846010030809490428002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 580869145 1250 580867895 580867909
    0x5150702040903053a0902014407030c2309130203130c150905060a030609060609060305060303030103030c0803090a062a0804080307140715090507140609 68
    0x900e001c0d2401328142813190312400d0150b805043d1102d03040003151415400c1c07205080f00b03903a1401c100c1405000c081c4103940064101c5040d504581c8121080070049080079000801001c1181c1c448021032202819454401c10103800580d0354000086c180100d581c002c1e0302a00e09103100702541c8003040b0740b034042c3d514a5003c039080030100c50f0b84030785103401d0020380d420203002850040c40c02c0111310008113200d10708400400103680c488039108071003500f1201c006130001900f5085030350035101e40340e9803503071043d0441c020324554000b1a003051030729101248803540280c188041e201d1a84042055481f01403c141d9070340024800140001d050901e81d200150b480005503401003000c00440301080341580e92802552006184060350303100750150701203100441c5084400c04920740c10014078030304041c2c82e08400d61000900450902a400100075808511a070803262400d03080020341054050900040d00030340b01d202421754640c407c50b035012440e280074004032040908020211841c3c034031041700b4030440c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 580870395 1250 580869145 580869161
    0xa030e1204080c190302060a050702190b0a09091407051b010f091109070806040506030703050f071502030301080a0f0809040905010603030f0f02031611030708160515070204 76
    0x1860169014045100300900040c0015144280203484656504424040140c82080c0c01280c442c40c0b44000700090780314801110300c0180f180c5005561400c40d400031a0b601c041070400c14151404007000000c0e0400c07004c0c041c01161800355109040300d55101c2a50065810854866461440303100100340e5560040e0000d10280e0140e102e58007440c001292071908450144c1c88660700251107030072513010092480204c165032a011690700003142812400107184000042449008666550100700d21b41c2e420465540155031010407202c0c0c194a400840d5200d00c40c03489141c07403000c1c21140704071002e4004001d0b40e043c0c030505e4008113070041443e140d80104241450f005c0c3d0300d0b03071020400000b050b00d69000d0141518000d00000c41d400c3c0c550701d401003049020303100320000c01070f41d10344a064043c0e02000320303100060841d0785074600580b5810302c404400281c810166040c0303d411310014002d407001c2421083d5860400329000c15a40c1c610500c1001e51f04d0000600c1061020001e00d401481c0c00c0d440019 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 580871645 1250 580870395 580870421
    0x80601140d0c081006051503270d030b0a050f012c1c15110d091103240f010506030106050c100c0509031002090906090a090602181309080a03 62
    0x40c0c0c07050b91600312540c900343c1c20208558004418070203228200f8000c41d03004205c03d030384c18410210080c400d40418000540b00c01400040c59151107244190511001081ca064009591030603000701d2004e402040106503580c0640100780d000241c910f800000202c1050040c0c6400300003c2c0c0e005d09070300106142205199060b2041400d03c40103844042d0142441d039115031080c4189c3c04903040203403904242c250300c41055403e244c035001019000038180c83c4000900c02020640e80c50502c1c2814141600205042c0c1520070410040300265514030206118a0010b1401e0382a0325490400805c0074000d0040c240c011100b0001040110b1091004012150302601910b01d00c250300c81801c0f00390f03034203412103000060010070880180c1c03805003c1c1c01c02003010308200b10f1038000e40d00701086660f90020a114404c065000024040d403105400c150a40340c0d02c1441199150244802418400d80c0f0741c100314041c1104400348181710b85648592040e2580007101c050030b00c41c8801c1c007200038146542e2045 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 580872895 1250 580871645 580871659
    0x60501051e16030c03271712070b0618060607021002160602010f112721010c1b0f0b0c090301020f0405030c012a02120a12020d0908060114 61
    0x41510302c050315038400b000c0c2c4039546030a039844660030020001c03008001e580403244203034241c1d0000c048240d40783c1012a0300b1601012901041044c1e05400d00321026403851741d0f6480010036001b0031030b44102c818481c03581210f68402c5079100074514102e0550480d0313001d8100300c040240b41c4c0585821809610700c100b180c41103c480d0300784120415410401e550102d40580c0d1248210051b05085003d25803084d1031000780507082080d00c90252000104c0c4410300c6481102c0d180070302c0711645440d0b000c00850b00b5050704000d0380520012768136000380810000800020b802210803030340403a542d180107109540003000c02070705100343d81303030b40d500d018015054003a402800c0041c2c00d45e5407420b001400d0410b41075490103841d01d240c00c0500d4200b010444582d41080a450402c3c800c0741d891f000f1480e422801d200c40e00003803422906c0440c201c600d10800901c81881241a1803041029640e40b0f585420015426542002030540c02a100e144107405907005503001030005020500c1882800000d40c90020480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 580874145 1250 580872895 580872907
    0x705040b060913091103160e0a150609050316031a060a050411070b060904080d0b2407030e0603010b0a080c0f03130302070b0f09131d0c0103050901060501051e 70
    0x98200c54100d012181000d0311810800e007170000d229825011440198068085035802c100c0281c2084c1c030f180180340340000c3d4000400c1c802d1034180c2c4080b13040301928228140150311240b01800307601c1035101d014428070031000c1a144405500210350104e950000581042c0031100140b004000340045c20603800200700400043e640da03807401031080c66a0a92651650f41c940d80c14503107014032009107050700a8010000f0300001681c05001c51310412000180095042040e00c002440c0a200d091240c081d035801c2c0204002a0f0000001000e001d8800e07120384170603052503400d005540c0024452000b44420900103202954050025594040c0b9001c4140349002080c0036035114541040e5400c8104210310076418040540411151010300384031440c0504140400306000d0300c521945004500445079078099002c440b0300d582142071031a115800d4054500101102c09a866106546060000e401c22012459460040c0b15410980780183e550b1460024803c070140c038425503502280c207001c001000300c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 580875395 1250 580874145 580874149
    0x15120c1728031e09140307031112122701030c0f0e0a09050f0103050f06040506070c0212060702030306030712050604020f15040308030117011a1009090501080c0a060507050705040b0609 81
    0x10703040481c2160322035811131400e0110162840b0400404c150003a0310010050010503004d0402d500d0040e030032112844241c50310081603043c0b88140c10024903500011460340d110038103841c80d003c0c041040d04000007403240c852004506480130600780402081e07a4200a0070540c1c405c4100075030b035000290980136401c1d034401648040f0381c0100d500440c1700040b08014070070004c040c001082542000401400e49003020b80701c180d107550000d0324480078040c0003d40d040c00c5440c0c44400c02c0c00340002c1415520b0700e01c0e19207400303522503000325a000e00c079020304071000c100145804101a09141c120000b0503040c0e81d56800d01c18011450780d4401e9212101c25265102175941c8001040610b220368036540d04c070f516005c900c440c480c1c0425040312950b4140880560a4409509002c0100d14103e0f00d26861078010001030341ca00c2c2d0075420105050b4101000480e00010000358010301d07600c20341d08c03480741654a5400321203d0103800d6000300141c0242c101000940741c076400024a0110050000c2c0c504024100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 580876645 1250 580875395 580875437
    0x2701030b0d0c15022a10020d090b13030803180f0f070b0306010315060c03021203060607120e100903211706040f020304030819020f070615120c172803 66
    0x1407117003040d42c03c501d80c80310b600b4000401162141e060000f03100b040c6101c0d0307010740381d00024050342c201c822011034003690000c2c8100c810b40045801180c0c0941e01c1c100306c00b60700e08001550b4629041132158070f4035103400050002c0c210300d80c0e850303d0303028240301818aa801c210076480680121304041c0ca800310b0f02c490402c40c500c4040141569141c0d4200450640390203800e01d0119a80c000d40c103001841000140d0f103a98003100c104991165182c0c00442050a080c0c0d01c0c24010108190011822226003a140390080c0b50841903038021074060340240c0c000c01c1001d0003009840e0075a80041c0301c00134080c1d140c0c01450b60045e04040d0041c404158112001d841e60203e0300200c80c00e8001a842c9018007aa10203000c50603205d10307907045015444c120420142c20054418410000c15150780c940f40b40b414400354402c4072011f44002001e81d000749403079082014981c482401443c00381010142499501c6600081c106c240900107024020070800381e820b40c07003000f0314401003070301405411008110300804e808 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 580877895 1250 580876645 580876693
    0xe120d050315040506060904181e030e09161b0605071716020309060d0e0a0501050106120e0606010e010201020706050a150914040f05032701030b0d0c1502 68
    0x580c5968407803400b003031404203071840100c80501440c5807070700f40850f9841e488212150b228094801040da000d0002c03101100d0510b114019000550303000200b0344140030365a08800050081d070f1120200070100041009165040e03414081003882c0d140359401c0c0b24091030b01c059440041400c0010200c11644a14007607a01c100c0c0c04c0000140844a1600d0755030005900542004040e1080c450f05035008201a5072031141c1d400c0140309100100302c420400700e8030780184500781c0d11801603408080765890228080d080030b01812001c1030041c4812020000280f140341c040041c508010a4181c0310000159407603200f0260705030465400700904000304906018490040a007a103000030354031054803207001c00c071406d5003004460a00700b009000c1d00f502041440c039081500440001c101480d986401403451007081c1e940003680e400d5103020b11103a45044100420041e0a8805110b001030200802040072891007008141100940c011f014210080c3d4004d4201503160046420440c1c5012060240038048 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 580879145 1250 580877895 580877897
    0x408010906050f0f04030c03140702030f0601030203010b15040302130b0603160908030c060c16150203010e01091e0504020f0a080703021f0801090c030f0c050d27030e120d 75
    0x200203002071610311449483d4464113103820111581015500140f0b80f4041807409001c010f5050025001408135600304d40b034081d80201111154100d901035151640c03000d01c001e03842540b07012074803c480e01303285604061f10080e842040c1e1a19045038204003a5004c0701550000d202e03a90f2481b0303e070039103a240c01075026025501d00798411901480380140145800d42203004550801c2c4000c407602e0f4000641d280d0032000800105480d40e24502034001c03101c450105c068455125581600e0011040b540150f041e5445241c0104960703032500501c40c1640c10604008040c105440d82d042249151540441d4000d48002c1c42c0b00d68000b0b81000141d15540c0c1d076000780c0103640110380c00700308501d042645d600c0301c02d100c020381c9408c038074285901230600241403041919031511980d0300200d1502c658000b24000700040810070112101540040a03500b007504074101c43c41c0340101080007004456520383c0e264003240240686030500f40c1c1c044807081828059540c00880074004452007107802d0040000301d06032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 580880395 1250 580879145 580879151
    0x30602120402031018030c0f0b01030311060702070501080a05060d05060106090815090c2e090602010b09010302030705040e07090e0c090f0402130e0c0a0b130b040e0411060408010906 80
    0xa004250a0601008104584a10384551703e840040c912010400443e09400d00c2c034641445800e05410285d0292401000c2c101071a0022003019088203065400f5801c50702160300b1a65880c03c00c1e61349241030f010b0702e400700c0e201a0026044c008142c11072944403c014003013201c000c60543d02d0301e103881001c1e00104045620440f06100c510410040454000d41c0c0245442550074282c0005841d802d40d9242d650007007004d503e58a60704176107400c80b502c100d950f418020180c3c6000e0000180042140d0050740d00650822030500450329012407420b0603260010702400c2e1451401d01040018210880f8104042c000c51500280b020424426000345200d118060510312186400304400b1002c01008610f22440c81c0c0180b0025840e14449000c8002c0e84500005040b60007540302c0386425032805c803c5600503c2000c01280301144000070b03004800c0d52083e4036052949920307004006001c1d03030195114001901000501141d100c0412006c0e520001d07040341c3c0341a0315024a1820b490348642c065902c107072 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 580881645 1250 580880395 580880401
    0x1e03010905010e0c011404230114070b0f0115140313050a0503090a0b03010b03010b030c1b0708010e0d0210090c031502070209010504020703081f05060d1a191a0403060212 75
    0x10b000300c04184826a504001880c040c10580300e40443c8e00c811040d925003420621203290f003a400b501c07803c00764040c42d8907203a8951f407407440e0411050004a60715600407200900000705040008500210003100c2d444a00c444000140100715070b0b0001000d03110501080300504021079800d1160002603800340b005165910300714018002c414040754800c04990744200010042c5442c1036003034a05480700d8100e0720350b89031500044610b0601030701d0443c0e10120400310210200d1480040e540c001c5032207100c001c2c0151085e55240710f8441c2041180040981c02c00c03900700d2101d01c0c0f1980071030104d511800c003103540d40d5125100c0d06003a00005e04800c941550000d190425860a22511401008100e0301585005030b196002080b4503c090032580e9105802846140e4485840010070042c20001e0700454541c60300300f000d50064010f001115000302840d250076046810140b200354880c00406c540743c06280e26000450000c1c2501041e0009a9070041c84088006405400140304e40741c040c1200d051981 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 580882895 1250 580881645 580881647
    0x6010f0f02240a1a060d24081e0105160c020a0e090a260a080402031e10050604060b03070807090e01030f151e0207060e060709081b1e03010905010e0c01 67
    0x7040d11820b08003428006144013a581d0ba40c02c11100319061840010940c420070024502e10340d00c2074003d02c01801a04080070609a038001035003180e00c10f240030103102c50308040c40650300300c41302a5420f40a5182c070841c0401e295016403220200148040c1c0014101a030b1142c07003800c40001501d45006540140c0902802d012900000303c008822141800c25000540c42c41c1403d40d2054048450a0081031000034013035590500081031601d802190300583c1030b660a81141d00c0300300c80390721489010f00d00780115585081a1003030009840c1c80314151861034803114020307102020010070202c00c120640c0c4c2d0200c0c4071b82c41909000d008602c83c1743d08600030000d51400c03650409800d660501c03040e240c40141c44601c0301038803900566804140005070744000d503042410240c00001900c150502c11502031222182d8050001812030345400700b900c0460f0381c4a010070440074003022400703a000080c01002d0b03540100d06c02495050b664001e00000e0924400c0d41c980b400d6075400321403500f40c0e400105c1070120343c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 580884145 1250 580882895 580882901
    0x1106100305070602060f061e04050a0203060111060c0414120a0507030614280e070311090708090a1209051f0207090b180618010e0405120306010f0f02240a 68
    0x40c3c00e95001600442c600000c928040c00e1005019902c1107081c002c84140ca200c0e080c0d0300c903004002c00741042c406450120b515501940c8103039001d42c0003450412040441c40b0300410283d0044403e50040d6260516006407030b028140c2a800040e80045c0c4000004441d0710304200c0294018810700240400601c1c500705042104c00b20360484400008080412409420590618051840806120481c3e14006d00d07018010580e582d203501c00c40c41445008400e03c03401701c03441032040b0002c0383c42409942e181c036000c9668407408d07110304113558840080500044e003801000303a9040240d14000480b9659400041c001180f0072034401d0405950304019001d06506001d81c1c0081e01c4900f005004c00100721002c80d100c1420244400c0c2c5501495001c60b0142d5203142414109100310b203000702c0c0a503101d106500d05604203450031075562040440141c5d0350b8000d081681c1c45402c050f11030622098004c001900d41c500c0c9041c0000850152000080108418450b07404441482240d034540074940a4031382411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 580885395 1250 580884145 580884149
    0x5010615030506010e010c06021c0608070f0819050a08040b07050f0d020a0b0a06121b080a170c0c0303030907050a2115150e0613060e16110610030507 66
    0x401d400d000412500340d8118031030100d060020b1a00c4600045141000c90003030280c0107820000140304203405101f42c909400c00c10a03a0100c0c4291100e00c0d69540d0741c158244054031684407190081e5490448410007440702484103801a0241e8001150507170b43c080c8164000e40051101c2803000ca400c80c207100040210055403ea000c005090440140030302175071391817104000800350304c84100001c641c0300064011000500c541c400c0003914002c1c42c940130a07034000600c0101c4d200c00c02d031080042c0c85070300001c1010f03016400091908509003c92164031841d4000800c2e400a0700c05d81e0a0788210340c0b010002075200b08084030103031040e5401c190030882c40302d195611003140c041c1c0d51a08859150030041d100c45142d0360202c40e45000c26403903091803004c0c1515601240e00c568161000080300340e00e89180c9442960700b140c0e4000a0900a200d1008030f5601e03010f040a04e0762401c5c00210504034001040ba2165114108510346440c1481100d140001c1281c0007101e0f80600322080081000070442c2d140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 580886645 1250 580885395 580885397
    0xf0703030b0d03091203111209091b09041d1e010b040204030510020a0c0b07050304031202180609030304091a1215220501021305011b020d0f080f0705010615 69
    0x3120310a65100240484c0032030003049002c0b442d12600d101018002c14090240400080a443e80c0c420000d50f03409403908031030500c4e40213800500c005030140d075413002d9002000ca8126001c9051540e8802030000034070b81000b035600da40d0f0b2a2801e5003d03c5904020743c124050f021400300d07251007883c0c15500d003034038541490b0038082c500500c01800000c40101da031000d04150081c006840c0c05c1d01d048201e40520030040007405501c00c2d00c00788a0030560010003184500d01903140d2048010802807180b01b203101d04036111513100b91940c0101c101e864010010280180000c0449040c141c58020030b401300c0e6500031441c060300c0b040c58454065401c000358030700281c1100102a2242c4071810791216462940244840801d44408550750005000150cd0201094000e4000c545a10900103000203201041c01205c2c0414080200700b0058a02d000c40c0d510740c1940688469181c1500744d40f81080e840c0c40d01c508a50030003052100980d0050418040e10000340240e001140c82d5103410441c6854a82c4506070308 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 580887895 1250 580886645 580886659
    0x62a0d05060f01110c040207051c080f0f04030c0201111c050405090702070e010e0a1e020928061803080a08040b0c12070c02030f0d09050f03011b0f050c030f0703030b 73
    0x70f60b8901040c000c0c5c00c0c40d42958003503600c400c14034084d42007400e10580c10190f444848424040c0070341c0840b1040c0305800d1502450510740301da40c41040151b008441c0200040c4000080c08015441030503200c02050340d41e000c40b018140280c10403550f0328802c001c25000074801107000c01491425201c0d854120302c03240040c140c0741d0f082124802a198050050800300d000810208101d001b450b40300240d06c1140c18400b468845041204001951081c080148110035007007401d4403003100c003190824202035800715812014074284040c1c0f80c0ba101d11840d44690210120f00101184007800109016560f95490742c842c0e107002c0c0750003041d030b00e40500b9065640f20244844501c050303840d0505600700c116070501ca001240ea1f071001915040d02021004c805000706a050000560088081000da0344210b80d1550b6048640c400c2c54200d0b20380b08030340f940c1e076004510a00f602d14052183c40540c00f1581c031b0628513091403000c2c002c2c82c40d401080640780c2c18000045003014103500d8424620440001c0343c4030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 580889145 1250 580887895 580887917
    0x103020a3f0e0a030c0507090501120203010b0103050c0307180b040e18030408070302131805010b130209130c0c05070e0a0c0302091014090301050f0406140405062a0d05060f01 77
    0x11990f0f81c08800c200405011004032601c051103020041d000082845440030b0000d03684982842e0710b50b0203031410490196080455000c210b6000340201c5200c1d84503c00c40c60700315921502c00b00c84844146042c0c07221010405004507200010000900181040007041d94107070801d842c41403d00403818510014540040c0400c1c4200303c0c001c24180b080f6501240d400d4201d4450040000003400b180c15a05000a07940682208005c019041300424110803945a000c10078225481400e03407144001d40e50384042c0c007007600191000c2c0c1c2c0c1d1000780174810501d020a40024103695240ca06056504410071481c03083c010032502145500235446a195245400d604146070300300840c40026941d00900e00788403900c4100b04944294400b9605128401002842241400718058000e540141c80c16104941403103811a40c54900042d040d003d254000f00400d066036460301b03d03045400e4004840c09010307550383c100d8624468dd01001d40140b6000c0c0d0b00000389401c064040100030416030481c94107000d006403031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 580890395 1250 580889145 580889171
    0x813170c1504050d05210a0b100f080133030e01200a031d01020a181a07030c08120106021c080106090e0417030f04030914090103020103020a3f 63
    0x60103004c0c246400c00640b120b02070060505181d00c1035070401456483e03c1c081007207112403900045076100f01510301c0c042d1207100c1401141c10a20340100b40001c241924010003210208442600504c00c0d0000100d0100d07880c2c0e59041c0d8034492201d0101700007503c45030740880034002803007032092120b1a5912090042a64442d050300341c0992000001490390301e80700c40411900444400c000a03174401c0c021581c40c500308a0103071054108440c0b5089694400002080e070200d003e1034a200c256000820906241050b0b074100e54a02d9030710800c132403070281446100ca84212021a003170107441560080c001e42e00c040150b030362840c80410548000c00006200402c011b07504041d51000340c9001241141007655103040c841c00200d00c045034942c942ca800410071501c00a0b403140d050251f4420307542d404a00390f6031400c0001001c0c042034895030203080d0100410056000707600a000080350340c28041c4040240400118904c7d0702c1082c4103083d420000c403816152a81c0d80308d07900490440280c04c0000500e0508 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 580891645 1250 580890395 580890403
    0xb0c0c060a1808031e09030d0e0c0619030b130204090506010c2f0d031707020f1203182a06270a08030c16080a0b04030813170c150405 59
    0x80c003a0104100002080d09610200385e1060303184109510142503061020485603280d00000041c0111840e000884119400200354060703680801840f0300d05100c50307a21b40582e843c0e84e42146909040c1d4540d01400651595022550081c5900c40010f071128604510300d41a07440c000c05150401180da1000c4001404c9140380c07001518040c1d4507581820a00407000205814050440b07602408502941080580c414140c940c540c1e10100040c005440c1c41d03034281e98650a07580c0c1c0c159240c0185d000842c2c201c90700300186a204a55080c0d00300040c107140f01d003030705240d013003000703820038400700a544c50810598558a00040205981c25441d0055020844903e41400e5040c6030440c9103082070b401e030756500c2c4c8040d000a0b04030384e010740b0b59981385501410f641710440f2400c40b0300202c0c110030011300241701050308803590780c1014444846542e00c1d0380407266107000801d54074840e0207548a400100324172603614100503000000d203070780e0784004240b41890a03c001c260032079134840250801001881c007007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 580892895 1250 580891645 580891691
    0xc030306060f0c1103012703090807030c0e0a02040b12100b0403020607060f0209032e0c0503060f010207090204080604140601180c1b1211010507050913090b0c0c060a 73
    0x4c2d00c0401c0341c048020020380074010160140004030108800f180c0c8070b40d81910842c0740d03140b09807200c190710340d130b40c154050700c1d0f40c01d07484087e1a949020004120006000c4085036000c201e21000601d85a1903403560101da070080c41d000d800648403202000000d00c4c40e030f00608040c1c20342402140c1000c0c03071540041c0e501d10842c18002c0c101a11500007400419054051b980010750080646a2030440031608031029208038400102c2c20300d0310409520045c0c0c5920980c4165002950751070301c1c5075245402d000c201c090001c90799045104d0305100251081c1588082e001520ba0300000d0700450420b0b081404100d14101040046900b100004102103d0b40b90b1428062422100c80400d407001e10030740a031001c8001200d03c050b0f0564060503e020820b580500175010000c0e600c0342d17090003207107002c51030807210100d858070b02081c400c20004100c0d1900300110710811882c0311021406120554840e031500900b80c1b19114801000708280d203d00300709000301070340418021005c0219050709030b07a202500f5682 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 580894145 1250 580892895 580892903
    0xe070504110412051603080319050c040510210e0c030c01090302090408070b01090e1014130609050706081b07030801061d0a0b03061305040c091e05070c030306060f0c 73
    0x1d02e4039070040040138400344980288900e002c0304600d9603804c21034071035802121803035401e1800100c06245118544070302c40c080c03d0100310f0981441c0c14375044c00b820710a40040c14050105803003a0340407140702d00050742c0030345e1005076020942100b0300304202d10f0f22840500c0c0c107110750060b10b40604540d80c0f040442003201c0d01125028015121410702d269644601d0310040c140d40795a2001084080c0e00c1d40102c070341400407a0440d039036546004410000c480c040404d00c4010030140b0701148614078040aa8485140a00700000e00106955075151803c4280c2e40010040343c4094204030102034101c05d514000d950380c00303009107450036590b00180390400c14005d0705c052003031403c0c130409140001440c04841c042c024084103040303500d99080c6c010640080700d480e40700c0c0b071182030400c151043e140149405964040e04900600b401d2035504c0c00075098203943c80050803e2500c03420f4040115000b9507006041c0c6444d404845000d500b802410384000303822020034001d000e05108c2c1030aa1050100d00540d802c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 580895395 1250 580894145 580894169
    0x3030f030a111b2404170c0c0d0b01050a05240a0e120a1106040e0a091a1f090b060703121e0b040509070b070803040c12060e0705041104 60
    0x4001c103902c0d40a1641180520400900c60400304000040c050020a07460400000c1c60100c03d10381e0303032a81e10b048400800031202031001c00d64540301c1201600740758805005a42c0140141c0c00419101c8503103880654020a00e080108440e003407014841001e058142d89019911440044c1c6051034020302c13241142034140003407503102c0c040c400d20011a09940091145600b0340104001c1035480310201000d0b45c21440a040b0300c80d1074600b680481d82111800d0800f034005683e0f11041000030000d43c17a060f03424020600e0305e521080c800810f250b00c44e443c1a1100c102546004034240d000d240241c200483c66803070090071410031342d182c0303007618841540361910441d042c02c072564040c0a425000402606901c8085000c6203101c0c07540c20040a1860564003041340f5034038600700542c0c0e40503601c0f036494116801c0018602191612000b164002c1c015140a9129981c03030f003c900e940303402010709650f51641e4400214081405208010091800300d5007800410000100d1500b203101714810400c2d0828 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 580896645 1250 580895395 580895411
    0x20f011704030e15040e0f0c040812030c0f0c1f050106092606010f03050c0f100c08070b0f0a0f1413053a03021813090f0c05040b03030f030a 62
    0x154451885652280d41d241c0b0684861b03031001075a410320001c1d00c4000903003244c0d0000418150804d401e550488000e803009115411014040014584c8007901c0d02103014010041a82d840c1c0d11100103001d442561001000700c0c91072107401000c0c43c82100440d200c42828280104000381e8040c0440041d502444203003815020182c06030883c040030224505d159028040c00004c5190030a244d00381201d02403426600050800000c20000400ca91a01d42e0302ca00f9644013403021907c29000b10941e50f200e03522542c40c2190944070342240c0c41c2c1c00c80d02d4250040500e410041400703414041c1100590314a081489221920240b010000c50000c00c106085200e00d0b030014140311082181425541c2612050318104a1a038204814003507600451840413220401c03075085188a442260210280b0f00c0c3d5080d910008507040202c000030202d8034814090b00c810303c11700400c002000a080052044070403088181c038090a120650302c01c400714034030980043c010364040e0300c410b408695014030000c00001d2401c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 580897895 1250 580896645 580896649
    0x702010f1817010219030e0f060f0a090c231e010c02040b040b0405010308030106030507080702060a0f0e1f1503020d06021e0a0c051c0f11190609020f011704030e 71
    0x1004401c8519084104450942443c0c0d400d50701602400a441c1f003910141001ca9503100e5035124280c41485103188144002081106a9809080d5191040400d901d070581d880300301319590f41070301282080c0928440c40308400d80c54060803c0801e92518040c0c032041c1c40d00640040e10344010014040c0c000ca444030804143d907500c1e6031100b141c4240c000c00420043d40c4a040c00d00141d002401010086450080464403c1e401114000c1c4656403d500130401580c405106030040d02c0c951782c404003003a032181603400000c04213010002c0c1051b4807985100890701d4040300b420580383c5465040140300a0750b1710030310150301c0310340d01c54107001c0d0002c030302599429410007038480b610000c1d000d6060407d404980f241c4102d42c0300c8080f0a02c0d038010000c403850042c8144c01190701c203004402210108250740d4402038214080c0464040f0a04100c0c00c2d107944529100859140300c0100328111340342075946000da4110b10300000b007107260040c02e01e00f0594402070300e003407043d0041d009000074081c041c0e00304800b9919 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 580899145 1250 580897895 580897897
    0x403080d3c111c11310b1603030b0f0114070219081b0103050f0118150603020c010e01050c070b0a0b060f04080d020a05061f050a0305030702010f18170102 68
    0x103104061480e03965044000340d40401c80d9841c3c0764103a01600301041070f40015048001c3c0c0f103e00c850789180c901092082a45005c4240620001d8441350441c2d5500045900c541005401b900901030708414504080c1c4c50700030111418095814411840402c40440700d036840800000d80d021046001585c60b40e0b94000150312007004c480c00c070019028003c0200300001f000c101c481d0300740c8400301455121841d0070700640994104943c8442c91000c1c10f0010000040441c0c0d600c0781f01360450344c0001d000302034022000d40066240e0040c0340860380015403112400824450340109006c2000200030a0504540c6c0300c140d481144809410150368501080a001c9a980644087c002c000c090a584029015240c145a00213114a034640d020743d90180340f00b14000701e030030b01580e6481800742580b9a1801001044142b0100354102d4070384000f5404101516402d050001441c0110021511003505200042104182c01032070000c1022080d000248100058a400261034400381000c490f41d010384840780c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 580900395 1250 580899145 580899161
    0x14180f03010f0b0114030702060c030c130b0a0207060e0a090b03030c0601240e0f01050a140c03030a0b120309090c12041b080a05072102060403080d3c 66
    0x4194079051000780c0b00781850740100e0034803c0a88607115029502454400c00380012200c21000d600310200103080408a0030045038880402c4021504280c2201801c1d0091903050300150744020700003a012608a804101c0f030802440300e40342c04103c1c1d03001980814801e5180c0c0c82420f0845032189070a503040e641c00d00c10b17100088a09011a4902e41e0b40e04500c0c0722013a10903030750034070301a415110403038440c0c8603051080755840c016002e84c0120140714011220765111500d50002c1001c0740703e0708a52417500000422001024500541d1a800c3c444003200c00c40710b42c60590352081080d4041e0101c205008030945400d004100c1c5c00d04800d60300c0007100b00a41c411240c1402e0585a641d00308000c0101003201c80942d00381a50392440c070142c032410455621003141001800c3c039486858100400c401e0030b0050080c41100002519158071240e001c9845c5030050381045681c2d200205500d04040581e20030b20803501460f11600101c0b840405003107070408440005008080100d2a1324121100c0076081240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 580901645 1250 580900395 580900399
    0x80304170a18060e0306191803030f0f14070f0509100c050106050a0b09090c0f16050c100c11041d01090209060a0f0b03040f0204180b0714180f 63
    0x5070761860700c0710040c0040c46034611003140000920300441d82c9071040c0c1010300c41d020302400910b80c54845050305200394038008024a41142c4486500a00b4440c0d9049103a50710b101c2d49000c944400304014003000d4442d000e5120b0003503840c040d500c500200003d440b00e500030880341421042a0b10703000d400c89081c466200d4803900010001207003408550722403020030545010720004c124054441040088440c454820306030070700c40911100c1042d1800c1c454032500000d8040403140350170100490103000f9041f0788a205404440318403010305114051143d03141390001183d501e080b00603c100c020b4500b406643e1b010340740100c400c00c400c6035620795070700c00421004000009401005001169406400504ca04038040d0110002040c800d0400742022400d482d64008460710450810780d111a10780c00c000e10030358003041581088000341c2c9944c400d074024081183c2103000c1c64092401c00c0c418150010307040701d081040140c1e50400128108040c0c41c07603800402019000580240b000844910b02c42040c0ca03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 580902895 1250 580901645 580901647
    0x70f020705030d050913150b0f091008010f0b120c070f020909030408010e0c030d0f09170c0a080a02030d030c0e0a08060f1605030103030c030c120905090a061208030417 74
    0x44001307401c007020300744d200c2c0101e40f0900d50a24a010b414140e40c070800300410704c59201407040c00075000050152110040044056003402da48500242e080401070500d070000c200c030640140074040c040640c482c09400080040d6140010704040b92154800003008903108040c041480350801491282090100d0380051464010342004004c1a841e9445449003030040d601e00680f030401c007500417410324980700c1c005000d0b1801589181c0240c95458008845004115940e0703000f1903013200b41403183d210359a00c84001c0040c04104414000b198105400854240d8411004140182da000581900700d200a00c0d0105094881c01400d5820343c4080c00da06038846458000810218400511184103048402010f021610340c08840580f51b010f211014001035010401440805d0240e901704074500d10a140090708900300d61114100c8080200c46000000c01c41c0c4c03010040d900d011460341b50050390019081000a00d40000302c0d003244035a040c010109000480068184000034803250800600420742c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 580904145 1250 580902895 580902913
    0x120f0212070917030d111207030603030f030b091503010605060c0609071202031b01050d020711030c0f0f120307020d0506010e07050301030b2212050901080f040506070f02070503 78
    0x300400000c200d400a000401c2d620001411010912030500102d003000091032428803071840c4900605240020003480c154204111201d41010881c102d20482c2c850390700003180c9047d07107801800e01982c809004c04050038211705410a6440c40c43c80ea4004804180c0349500ca040c0c030380864094030456000541c046404181d030403240c1804242e03180320303601003029140700a840d00004040d0310020300d006134050380030580e43ca0b0320784000244074590180506080d4100b000c5d2882a10680c0c0c441c041c100e0b000c14149011080500b020401b8044040c0102c601101c80e1803210089003c1082e80c8405174481e20081001c50b903090740c180121032003542c0107400f00d0312829941c1030841d5500300a1140d040c105c0380c401d0004041c54070500503a03040c0d80d80030640c0101500e07a50034141e040750070152028000301c8540e80c1e13640020741c40180030340030400b96100d1544403d0110005403504c40001c28403045080000c040200090010810981c4407039582040d00da0096030001c1285440034035081786815100e80014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 580905395 1250 580904145 580904167
    0x50604090902180c040f090204080325020904030f020c092a13170f06061c081303030e130e0c19170106090b0607111203120a0911060a0f120f02 63
    0x500940c0c0d0046d41c4030820f5a07507a410308080b4401d40c0700d0b03c451038005100c140300c0700082c19444e136400703482c16052076a548441d400060304484290380440209403c5014421200c5d0184040102e00b0400c60305d600d054130700030300000e0740340882c5840d40c8580c1140c41d5400c1c010001c020151a014152030000a10307064803004000e05015081040707040b80e12481078a400107000001d0045d01c561001341c0a80c0c00302080c3c55106803155400003040312645400c0c0301101c0d01d1030180034003a00940c000d950b495100c500da00284066944141c6000b141d40741426003080d110800007a50071058502a10388200e0803810144400f080c0625410681e80305800032404024428150440c10a55800400420008010350704001081c460108020076041c03010b00003040a25000d0024a40309141c20242c901d070100c2044880b00010085420050b145c2e603444020f030078000f015070741e0400008284c820780c1ca0105800400340000007003828078400c100c016107650385c1481c01c030342120443d000e04041c00e640f10040e0381c04c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 580906645 1250 580905395 580905397
    0x30408010203090c030f0a030504260a030c02090c0a0203220b040b0a02070506121b090414181f020307180305030a1101050705040504020c0a050d1806020304050604090902180c 77
    0x2801070304c80d1248101c1c0c1100181b010410082c10351381070b142c081c5414981310407a050413544144543c40003518203c000300d0040e052000c614154801d588034013400110748100000d5070b4000d00f00e40e007507101c24030107541090340010849100c1d082204882915070082030b0711078a501501d030400f1148000224001849401c910701802c00101580c0a030ba002940f60814010740340603150101da040d820503800f0940c1c01c004050390303001c41058201050f10341101c0202040640b482810503071034407403e080410005221004102c140650580081c00d0071541c0c00074400d000c10006900840b01a03800400700b048507000d5056151103003520340481d8025a84d03404e00f80e40341d030490081c0d0808540364104a040c120780c10300c0b54030700c2403285846040c00c15040505200094009060718802c5103d0280200045002003004a8591226981e01d2003c035860406000302010036a02000941d40107010901040c2c0d1031100392000c1ea07080320720005480c6d580703000094031f408480c00d40781601c2070703004180304280d902d901c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 580907895 1250 580906645 580906663
    0x61b02040917040602010605060306010c020607050109080f04050418030c0210020f06040b09160308040b1c06080304061202070506061528021912030905032728061103040801020309 79
    0xe002040034643d240142712040c0300480c0c9c5940002c1d40c161000b001481c0442c042c1902502803800061a41e22a584082d000d6002c44d9a0b61800040405c1c100110310f0a8050707088100030300c20b01c03101c8100c8999006040300280c542c1c020320405203000000b10441c400c00081e0306032401a0212046800c060414130b900c00804d580c01c1c4000d0143c200341c0000e40c050074904030100e9500c1561246020328041001016401c0201340c44143e000030740814910b40c0b0709010b4100a0000c45014580e101e240000207007111168824012215005000390400714401150f031a030f0102c1c0c255807031444e0311b02611100340f03680308020300e0003040d0300b06151455540c070607000c000000d02003a808440c444014048030032501c2d00021070040c4292462514055814400e40015499522400807070b0309020104a001408900c008580c0900054000b10f00e0341c50300d0a5040c1024041881c211442d6031031111104104100c03503802610140036070201d00d5010302008100300c070014a4000021900c0341030500000e92108480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 580909145 1250 580907895 580907897
    0xa021c05043003180302130204081501030f0308060d0204180c050109420e0f0402031303030507050c0d090302090f010506040911130e0f010f061b020409170406 70
    0x2140050100e1051051102001c0038002c070741180e00c2c100d9503044403048100701c44141c0e2211421070020043c1c5500070b100c0000035106070096180e81c00d015030309150030064404000c03150180c1d0010004130303004180c2460050307050316011516a0b0780c00c0c0800c1540e080e242c1c00030f412a10b00b1a40600c2c05c14034000071030b2030510400040c140c0c103640314011942d603904c5001d0b62804943d00764200c00d00c540d02c100c07000b1134125485c2e0b02d000b0341d041c0394402d024101541102d4201042200790342e03810300d1800c1c0700700c1c040b0380c10200d804504508004900320501110090001e00303050b034500103d4000390083d030603111020b0182c2e00f1101c00c0d00d43d8107002030540d42d00d0302c01207028801d18004541440c504000c0c0314160348000d0a510708007031405600c0b1000d03046942584080385c600300100515038900c04c50250140c1407001519440341004180c1c0002c40e0b00503030001c3da007a446444203000c11607203c140b078401c2c07851410207180340f0302143c0000b03001001c050b0401813540b81180912a100020f4001a104071170340c07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 580910395 1250 580909145 580909169
    0x4062307060555020c0312250c020406050901090b0108090307020904081b070b0901020d031b1d030601080f0f0105010602030a2001110405330a021c0504 67
    0x11000321041d044200d4000c4203143e0440c3d070304441e01d8200941036500949034603415070310f040464404801c100d034020020308070550070020700c1c07811641d5100c2c89940c2200d4041012400e20340d1400032000302441c0e56542000308481c58030703060b00b55a11034000c83c010746801041000c1e15650746007484000c02400a102c2c0c0400d1a410004001020110580b200290013070070038803d41e9196510b40c2c40c1c0d45e1041400d0103048004514910680508000d80030260030a00d841558a2441c81d0000e841c1001c480e003800105400c1c080311520380003081c0c8100003810b11604016844160010620780c1110079039044c0c580500c00c0c6000002da10200180d20540c4035894001e42d160102d500c4041b500361f030024010900980e0080210181003440f0720090b8080044101032401e5000d074228065096a1004401c074230000b402040c00e00c190300c3c1900b050810101403441c401401c0c080136801e440f941340c00141d082880e00020030b288095a000f405400701121156481160361a003440006d005600240545540c90003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 580911645 1250 580910395 580910431
    0xe0d02060105151608090d12081b130902030702100e060a0506180705070804081c0315080a17040f060507060f02070308041b120c080c15040623070605 66
    0x12460202c500710701210054020300c004d03944030080d8550081880c2d5800c8071944070403030302165101c10345040c0d000c103a44d10b400c0c86052501e003008200c5038800306139458060070041484c803c6250214a001c6803003042025840c4d68441105909080288280249442c10445011034080f008200c1c0c504ca170103041001c0201c2c0d1074008c10301040c0b0805a544800e03000c151000b0540c898062405001c1c4188908513442ca0140c65880807410201000c40300c20b80c83d03810050444005803d4013444d02d00885401e0403042c243e00c1d040045a40e440e000c1d4000d015001e000350601080000b082c200d801400d04959400c10b0540d440303e00400b250720988040e20303581e2503c00c540e10b8074100c45c001c448000741c050341c0d10800b40e200c94440d880c400b00b501c1d0301d00107920b011010006225400480e4040003030300842c124605549480c40607414a408081c2c0303240310701520300981000c2c1035001e0980f010745003203141c10825000764440c1a09031035180011065000b80114502d401c0240b50380100344658880d840c4143c0100e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 580912895 1250 580911645 580911679
    0x91e16090c0503041b090e0303041a074515021b0616060606030e010b0405060a06050a090b040350011b03060302190503070902090102010e0d02060105 66
    0x2003000810800080041011501103030070300c50b4100068545c9280745260b03030741d46d0b01c2a9046400d03034004200b0980000c0200000d120620f420780030300f09101010003d40346401c800040200c054101404580506200c0035036105207802064200460f015409071400400040d8886422030284562048665a5000d07400d402d031000c50b400340e1140307049220503030035412441008980d0700002d00800c200e4259031010300104885000d2000142681d4038005152600c856019089d03881c484111070049040000b80f0505071140406d00781110814901541c484e401d80320105e410300900e92151004920128000c014041880d182e00d00035030340303118818020b00407010045104000d0340d8041d1410001c52640751007030076420f015805403c041a000140034419100c101c040640070200540c00284d8400080c0110304201340d20040a030100d5580c125060700d00781c0040e59400e5680100050203402080f01842d0783d000750030016800c0803401c00c1d6558400291402540d64500b40311705413040c240f1034842c884c3c1c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 580914145 1250 580912895 580912901
    0x10305100908120921090f0409120e120105091c0e0a06271728120c022d12030d09030903080f04060906030b09040b091e1609 55
    0x255032040b0254240059003403d0100068024840300303aa0050910403180d180c028081003108809108020f42c4503041e41c020b1103100700a05082c0c0e03003d1440c03c8d9108000c20300080d26403030035154902e0000010840c840104080a40f02c0500c10030301d609250a004a2002c003040480310081108118017140400410490382c41400300402e503040760700caa0090110703074401c0655207880140c0c41984101540c010006000345000c0740d02c503411404c1c2c03190300b80d11419400e104c400c8480000481d0700c0c07650402c1d0000c90511051092005080c086c8003072032080524050340c02d60000d507030002c203100c041070f49003d03060509002002a9519040c02441c0d401e17010f140c07801c0781d07441c0b07122510001e6003071039060003000c0018860b404040e024001420000000120034000501e00c0da0590007000c1d44480c54000040c00c0c0d241035400080505051001828194580340b4111358883d800114403000340c0c540748105800c01d04113014020410b1440d44091403802e900007070601e542d1903500c0200720304640d145688021 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 580915395 1250 580914145 580914161
    0xf0306190320120d110c031f020c0a020907050304020405100612051009060b12100e04020618040c030624020703080d0b04090c0504200d0216050f0601030510 69
    0x80711295422071003900b2401500c5080040a0000c0780107210032041e00785025104c064600020381d0096034028214801e02c07a50342c54000540c0140141d1284c44c2d4140d0094031281e020301f580c964080b030a00d00d125001c0101d044805c0d000740c01840c0604001d50010b055a10131a01030340210b060901003003c2502402d6140e04a600d1a40e1f121030707042010340004007404000c0d00032401500720340004038520319648207500061a501003500d58542410203400340f1903130018010410140300d24800c0010065000310075601c590f04541095807181500c45408003004400009a042072404161208440d05540f283e0192142062000c2c018408485000c44440c214121003005820505c01000000c50a402810440000c4000441c001c1c1020011a0448040b804140c070301c028540c02c10016030809108541008030b9540c1c0c42851000010600012881141507039603042c0d40c00100d00c480c452810304141131655204003a28410542c2041090392110300780010b640d6030007000070303882c401e00303e500c15994 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 580916645 1250 580915395 580915403
    0x3220305031509090619091b03021008071e0c0b07030e01200706150b07030215060603040c06080a1e020702100203121f05060a030c02070510050f1e0f03061903 70
    0x4407540c8080304640e2030000b11b034460300415101c0509400141014030003e048031000d5101c2c00545241d80100104074a07645100ca05000000c403c1c41040359201140d44940c41e20b0300da001051142e41003040310300d140320034409004508034400703000c48954590000f84810040300001d01001d00a1201c004400c0b150580008081000704040b000060440e0070180c819400ca030082c1078840c2d07540480780c40b1740d408124101c0040e0012100510040784940c95190010340a4a0320303401c520f0a961529003404060103000140458a800511088802c2e041a82241d118401042e0b1909000013040b01035002031200b240704200301111001c40ca0310020580740001030070701c80300030244c0700c1c1c03203408121000b00303c2ca003040d000004401107030741d0711000002c0c064a40141e8000481d60a032480080c10302c080c0f500114131801a8412144801341d0200940c0c1e41102d864900c0390303640170f900070401e64a100700000300039a8000030440042421000c8059403003802c054950803600104070700d01d405102c665010041c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 580917895 1250 580916645 580916653
    0x20d02070b031902040f0b090108180613060605030307050f010609050415090f020907051902030331020a0305031801090509010b18061303021809030a050322030503150909 75
    0x62110340c0007940c042d00f5100c142d5070051030941c032025010001d5206070400107402da8002108040395a201e07061a500082c0202c0881001d0210000540c450002030600010740380c1103503c0d441407007a00d90243c0000c10009007107d07520003c52805588a00c001620455194605180040c2541c441c0c02424413907540310b190285407510b5090385800401e0042015119844103480500042e00c0d80c981060007030007035850741c0b81c032110320700c100d0311080090380400c904541050007805003110403105101c8000c080241200d40404644442c0900075440c0c3c5d0b8061342c400131b80400081407210100051855484d49006101a403401c0001562016024850203400000000040101f46801400303402071525100101d049c44440134001412500806c20b50320340102182020811840d06114004519002040c0410300b4940480304640f24055140b449051002c0040099891081840d02d112100e005c3c041c06000380c1a607080c0244950412180805041d08a0009013518600001264840c450500c028 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 580919145 1250 580917895 580917901
    0x48080105010f020109050a03080402040f060503122101030c03031107060c06020f1c0522020d0609080c0706030204052b020f010c2411040303020705150d140403020d02070b03 76
    0x112800010b8141e4442155622562070000075400d000420005001e41c1c0e0304c070001d081500400c000c80f240303000700842c00b610b0858108a951008a0400e42240f000050f49454120031f4036021200140207152110111080001004000e2540280d40940c0c3c002d903101c1843d44050549203664500a000d42c20214840c005988001082e540041c180705d11806100c80c1031441170403100d58132800c4045c580c0c4050b5243c10802108140000e4501c1001d05620446400b00640f900818100264208060141d0782ca4160120502c80000100c0303807007a81c08401c40d01c0c15a502c07840200290041c2c0200c1c2c2c800d40c2c180b26109171148911403890340d003140443e440303545003060350f08003d10390348547c0f52241401141c15161000c900c0b000303000458440c2c03e1050900e00500051100d04485490020142c5034106020500101c0d9000030390000f511010340e941402105051340038803450103104c1014409508001c01c140c00409040e80850185100342c0807600c08800d840000d036180e40c2da502038007601d04014000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 580920395 1250 580919145 580919147
    0xb030f0c041d010c0e03240f07020a08130e0606030103081c110d020408010f02120103030c02040b091f09061406071703130b010f1a030a4808010501 65
    0x2c01e551002503602200034507030400c1a098259842e4486240200781c100c03035142d009003010701680c101180003100b024000915003100013101440900300749640300404000a42d510b00030860481c9094104c08600d0316450000c44d0b400f64000503001d603002a0032a80003250341400c081c0142c0341030303030740c484005824842d10f120f20303d0040c9103883c2281022600d908588500c2c0026500616801600180240e640d9040840d01401d540e0f01c00b0000d06c08d28410422105202d40044a007810b42c0c0c1e0600d42200030841c03500000d00540714016400c0d074040c00c803a0038407036440351500180354000380540c202803d59a69100ae4802c0712030910805002900c040d52058032464038000400c1032a102d5400c0c003240c0c0c084042e010300d1503042100c080c104c107144002000107100580c6140c40c0108951410307041c1250814510014446400041100c021404004036600f0030068022031700000d225a40c10b030581030134500360440f000340c00c1120070324400c071400c04550040c1c0041c18000d90344242d496240f42a440c1c040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 580921645 1250 580920395 580920401
    0x20f010c0c051002030406020f030a05070b1306020415110c030303070c030917030c100e0c041d011a01030e1b010516060c05071401090b0c0d1512060b030f0c04 70
    0x582150071419500011802e0342d581014040c21484590046840d203040c19800b82c50455138800c1b20400358814040426240d600400316211640d0203030340d40d48a500c80c02c10b0044864604000148160f00104000c00e2820740c155507034220505907650f04a101216020403911881004001c07501600708000042240e4000c608000c4824843c1c03900700300c016034503042c20300f206801c40e032000041c1e0000981c80180c600104210602120380c00401c000920004007140e03900c039440c200d207500464a40c1c09094003503170407000500e43d004810009200c2500003003004c2d00001c100e000c3c00350110380f411000e1008804001070303055401303005142940001000e20b0041d25581c002c80f44020180d0140c0140b00c0010f98140034808030200580c480903199501890300b00e03424a107106510606a15001c0403401003171100c500320b608102014482c46d5581141490003001c1e084018640b05036025850300000c000d56410880c070070590052508114a07102e1404154880070742101001c0710381c0c440583e120881ca490340c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 580922895 1250 580921645 580921667
    0x3041203050f071715030a050a03142805190f0f210b0f030708010507080f2403011d0a02130902150f070c0b030403020607081006030e0c04060e01080f0109020f01 71
    0x60032004001700c4000646050f44484040f21075030000b2040c0020581c00000d013402c807802a1880c1420419480c0106251034040307501202c1c50342c204c040c4240d11340d01820844000e8100003415421b00000c0c40c1000d01054800090040043c450002030540c040c8207500d10740c101189064500d0805201031100c50240a41c80b070400d0344044510401411640c04020b902c0040c034610002003041d241180c0c0203070000b0360080ca2a000005031b003007008101c0041c8405080600768005680c942e520003180400d0040207040301c83c00c40100b03262040049030000141c89010035101303c0b038148004540b4001182554014040203401800810402c5407008900010f49050086030071818142a01c82d01c1e2001040782641c0800340c030600010902081c03503818001d40b5401441070401c04501d04041040441c050b500c1d100e00410103030781d824003d0301803000340800001c598006005000b455103540d000c904610313081c803030440588680c102d507451101040c0240064150005d01400035012800f0064034600203607 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 580924145 1250 580922895 580922911
    0xb04031a060102010b0d06112809080c0a0e090c0a080304050f1f081e0a020405040f0b1e0604030b010e18010c0504270c1e08011206020f0c010203041203050f0717 71
    0x203000c052703d458524000c001075094410410310441070901000b40c20001702e90400c0344141c0004184000030f49610f1849802c0303500c014080344890303680c0700c5100d04041c2d10540035940310764118000540401d0002c00340007a14030072a803004e2424807120030041c0003100c0480581103182c003203044601040c000d8944a9100e0441c44181d244e80c98501c80413175003090b08031081d0041d25400302d0103210b1401c25101e200c5054440400421100e6400000101c0700c40b041011000c0008102d00010015107661058800455120481d000c0650b1034480d1282415012104080d12588ca5410700400c2c0605008804020580f601c5403842c003424a116003250741200090b8034030381c10744014450807200092058203100101076a030701c42941401c0400c0c1d0000100740c1c80b000c4c01c0042503001449030800203203012412903031101c00141d0f00d603000881c000490060a001206652000c030800c410310041581d007280500b4156010043d581c0d486104c14403041041e00c00030006012201c100c00000602060b0a4010001e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 580925395 1250 580924145 580924147
    0x6011503110d062306070f0209150a0e18160b28020105040c080f0c040513020d0c032108310303060504110f0a08060a0b04031a060102010b0d0611 64
    0x2000d005a41500c44941c010080450709000440205007500c403043d132070301030881d6403911b4032207240c03500660803140000c040e02c102c1000c000b25008400c07014070f0307241041000e0042850349686841e0a141d40204445c0e48031002c2042a182400031404502844103940c601c44840415041a0000a098024000d00601d880300f00403000c22240344602e541140422550020489150501c0c2ca04000301240d882040c0617802401d4058038000081078400d10230106070340014a40d510700310107000c4a001d581e030294012960202c1c010502c02400355003401d5a01030034031601100c92000003044120411200000014080800718283c4581400c0c800c0340d5010701130f4208a80200d0321b0380740d15003d10380c9078200c0100761342d24820050740c1054003139011034006010096051407120346800d4070034407881d03c9820410500c1c100280e056034600c1260005490581d01c0c061300c42c1e40b246000b400d01c800011701c5040c0040703064000740441d803050050382c1c003000000e00002400441c554511010340070610140f002990 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 580926645 1250 580925395 580925407
    0x1c0503040e04050c0a0b0c10110f071214070b010b0307180902040609170c0d08041d06031603020a0612020f07030905090108031303021c02151b0601150311 68
    0x214124450049002e10f0160100445450811456000d03943c4408011079042c003203e11054008101c51910300c18403100820b1015500c541d040651240c0c03519407031100408a14042807103031748440040792145544400c0012100080079a90f0b501501c2d03801002100040018044d0420b0000a913402501509000228440108621410791859007041c00c00550108040210302d44c0024207030300400c8118882805a001d046141d901c4401034840e542c00b450043c10044100b00780072044030010894440e20f10007100a200c000c0d02100419075525100303101d4054001c1608030286003003c102d90307006004111007460000c080d03d0b01e20a40c40d4010407154280006181c10b011080100052482540c3c2c0300e100c1c41c2000100103404406030440f1040e6481803105038000c060445c1d07a001925011601c03100e450310103103a06c10164901d030030029040311800c4020300c400d03203c042c0030b044441d840303a00580c18009201c00302c1e65262002d01c01d4002c10b000265400a0351f40c0030f07900110a03548046141880c0c05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 580927895 1250 580926645 580926659
    0x309060c0c030a0624080c0d03120903020604031d0102060708090a06060e01060305010611120d110d05060f011d190503030a0c03090e042f0d06020c010b0f1c050304 72
    0x195035034141c40064841c4142241602042d440005c0c21640495409080b030406806603501d03a4880255800303804042184414980114400d410040c10024140113000d9103141c001e44401d0155012008182544030b1155907201c001012041c0d03010690040c880755544c09400c0310807650140211900e4002d0004540103c0c545000e02c84c0948010350701010b5039450050018210340050740444100102d00150600c94040400e4503031014881d800c1b60b030341315003400102c0c8000b001107505450812000142c9000c2130041c5800c0300c0c0c49043e0840750044140030450045d24604111000c82d41c0300a1207a8140f01240f40c020b8841c10350040d041c1641d1515074494011914503400b144808012074120b04010081603405860000a06520310604030503040c16a28242132503000b40601c40d03901498407440c0d100a2043c25007070303c2ca090013080d40e1031100090030f14100035841203000c03a265500b040180d0045051111068220702c00c040e00400d00e11121094240414190b000220350501080000080f04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 580929145 1250 580927895 580927903
    0x302041a03040506060d0b1612050a0f0c020706020d11010f020406110f1c050c160b130f050d1205191d0d02090a02130503010906021207050306030309060c0c03 70
    0x10038015500c5560340d04080c03c02070301d0b000006111714420039040701907800050024401640000d40d91800040184502406072855440c019092070704078500000c01c0b081040075080a00482c80c420380c100100703081010b049840c0c40450290101681c0881200c010345407051010341900070118000042a030b0314500d510003680d0241d404000018003108012136464014080c154840929000911010f11100d518140c800c50108020003404801300308003055200034403041c10040401c0b0800d0f461703552a02c451002580062450310801d01002038007091203405102c480050386c80c014046c2481e910180d449c404400500c0e910380c0304009091220307001c5100c09810401c891007068481312000c0700c44507440707580c4591002c20a84107203a141040009030300c81240464005901d1100540d507081c40109803105081c0960189030158071b0f10802c5c0051080c3d1754080e010380c1070f480f00a0343c00d84d100c0780702c01c9815010070b40305140d160300b08105401052078400010105412060308cc0c450080c3c0c403100007410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 580930395 1250 580929145 580929179
    0xd03050909100e09010204051e0303090424090e120c07030f03080f090a17030604090b0c0304030206060901030c06030b0a0e0a060f050319020f06270406051f0f030204 73
    0x6182d8044806010250312003a41c60760001607500214100751510000588007400680c01c000c07441c22034603410406807010300072110280005030084c0050303901d40b5040c446520000b00d07642d405c21a00c510200303c003103090040081024441c80105103400d0845401c213400d80c481492650648138a140000c00102c024200441d59402511350b0101c0e403600604070004224010b00c0c212a641000b801400010206191481d140e04401d256070f03100d1380d9a10118004100500c4041c000b0114002084105000d200055100320301c40d03801d03a4250b440c1c0c081800514002804000c111000b03441d001d00c0040d1081d40002c1c082080100012920355952079181d443c00400d540d1412000e458803030501401e0600c2c84000b00610058004040700c034403001148605202f1040d000b8418580380358002c0c200d54610094500c00400094034151055030031550f0140341d50f019185074061070031300000141914202ca07a40c00c484070329601c100d042d490000b80413245d204508020205255003840702042400385903d102c60 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 580931645 1250 580930395 580930411
    0xf080412020a0b090c15160f05100207080d0606031e050415020d0f0606180b0c010221070305071e110f010204141e030a0210031413030807080903090d03050909 70
    0x12145e101c400501c000c136414040d0741c8030140d60400108140d0024205000161500926610f07407901580c90010309084694030381c492142c0c0041402802d00c106d4800810811540c49410440c1d15a1200c0039011390300504a90140f4420a02d02c50325140c01d00d400295000c1d10402d071045d28642502031900c22071f000004e86221640d40d402c564090914284520707405490b6504001c7c806081c2d25042905400e003078016030524140200328560014000d405940d859400c501d4001e442c000402070030800031108403900d00000f4108800304030b050340100c444800c119070700c1007200400440b6840580304032a005030040403e106810603d01c4241c400e20143c000342000c042c6040800300780f0410000020b180b03c0903031b8000042914000f40d15030700060100502507060741c1e600c004011440c400d8004050079403000c92018041e2041204e1706580c00c1340900c49030b00c2512900886e444030b00f4101ea5641085401076011ba001f008101c82c0f502d442d244070310030940f09140851400043e840400c441c0a41034580746 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 580932895 1250 580931645 580931653
    0x603090c090732030a0b0303040317031603050c0f0304020d0b070201050a0b040618150f0f05090903070c06030509100f05070f0f09030803070e030a050604020f010f080412020a0b09 79
    0x40d1880a01c021508400600780900d40c80083e4200c0268110f0b00c40504031000d05681e03174094903c82c1e2401d000b5a002503410411442d262803428007120710641c804c40b1009101ca000d2942d030382e60036020f44580340c00f40b00209041400e15001103016400d591000e44113903881714004030341100140001c2c10462041c291680045200d090201c01c200985800074046e81c4580d06040c81480b030307001d0300e80009444182c00440032804080c4a01c00c112071280d10b410807116100c440c0804503201110900344011904240c43c00c6170291344d04001c1a0b200e0103000c10042941001e0b180400402d44250030280e0013945c140140e6401140d100400002c4840c411040803800392124100460b06800002e9504c951190703040480d510281c1120082908220b40001050340c0da0100105007c2440b941d103a000c07150700a0121040c144050829a544210444040340b29520444106401d54400c0c5d01d00d143d41d400c1502e80d00c400d1380326540c03001d20a038801c008020441c450b68000401150080712282c3c001c000c41c4000d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 580934145 1250 580932895 580932917
    0x6031a151c08031e130b06040903090806090307030e060421030509060c0705100e0306040b09010605120c031e030a21151e060e10020106180204050a1d04020603090c0907 74
    0x460043c000082c4032020a042c0f485c241c00128440f1607240381e200702c0854000484102c00e103000c2c0d9000c801500104024450041040301880000000708003450198440150122219040018521a9001c0c910400c02507409480c84605a09842c0e0040c600c43c2c02c2c400e0611001d400414415003003080b0b0240598000703a0200800e013003021444100c4822844c040018201e180c0219035100c2002d4001022200382400241800000394480000380c000200103e1480008410349591640706200403440382c00b40585050307581b680d00645000300c5400601460030500012000d80d04034003d1039415907800d810315041910441c9070f104840100d0108180380400d1801c2408120010408080204da52a10200140141a0010703494244440c040341d502c000c0603000c000480c09020a03502000c140440210301c9074100c2e00c90780143c011b42e2070035100402400e946d0007100030404100115168580b815402283c0517040c040c00a5a00c0043c80b070854403942425408504000c8d400c5803100d0001d01c2a03000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 580935251 1106 580934145 580934191
    0xb1f0e270f120415030c09060c03090504060b030915040503030f06120d0305011a09060f0f16050705120f2e0f06031a151c0803 56
    0xc2e0b5421079034040c2981c00303940140c041c03115070340e980c541c07035460451092040041c5000356594040280f0300c0c22038143e60200341c49009604000080301c020a0b15251402207400400e88034a5640e07070f0340380c00381c02c0324105051413000040b141c4004050101040e800001c2c0ea40100b8920041480d42e10b0301b00c0081d000000c0ca4018030501c0c0501038041d10219007582c00399040b5a10034012485c20000c21041030f545201d00707100154844000e0181141807928003010b00b00741ca100d014183c3c41d012226140225104400c0c0046a079a445074000380110f08001d86044040c000210003441c64898000406448a10303001e840c0e01800c5141480166070082d96004420107100705c07074200b01c420702c00003441000d000c0500081e82c070784103030b402c00484401c0000c14541c8070b501c6000402041080000400c070710701e44003880c444182e1620703424200205c0d00003001540100420394511b0001e43d01c02b14 = true := by decide +kernel

theorem cover : BRFrame.Cov 580755395 580935251 := by
  have h0 := BRFrame.cov_init 580755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 580755395 ≤ n) (h2 : n < 580935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
