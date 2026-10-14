-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3204
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:58:31.403455+00:00
-- url     : https://prove2.me/submissions/890ce17f-450a-4bdc-880c-2195e22c0c87

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 576079136 ≤ n < 576258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 576080386 1250 576079136 576079177
    0x4050d080613020d0f06030b042a061107092c012007030c0803091b0a0e010315060b0406080109140c031305010b041a0a2c0603010207060908 62
    0x540d110601034030a40d0307201251501644101d00e2030307800b404101070003a0f000300d000e0058035030300700c1200e845070025a40141c10030100400c0c403000ca5100400344801c19445201d40140b5074031400d001495008010400820000480c02414104031b140c01078040c05004200c400c5220801c00560951882071032030140a03070078844032802e018464044240149541c40d114440820440410ba5000400890900941900760070110300c8080c080c5118aa800e801450842038009051030136080345410107100b91501380382481101c001881480c11070764481d9400b004c0303000381c908402c05481f10340c10048141c500031800148003584107944504030b0340507503c2004414540c128405030f0349030456691070640c40800100720b034404009092400e1074050000047c961034880700003015503c0e070000021140e40c0304010030794203250412505005100d0000941c0d0803c131146802c0d80c0d0800940c0c082401492800b001401a0b1401c0d0101e9460701d5101c0700801c04085517280c0318010381c102020030781c0c1c0c81003007400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 576081636 1250 576080386 576080413
    0x18010f08070b2503170f011406071a0403110a030903110d0f0b1902040b07050105180c0f060910021f06080c1309080c0a051009030f080c210405 63
    0x441e01d0f0344407011200c1d03d028140c500d0003110b0912803d000c4040080e68814a6520108688a039018080c2d400354038100e9450704100c00302401003801598402c0400308260000642003201d018082e24000c2e801200b81c0e5652f04080d00c443c0c00d0064144468040c281d83d40e410107503c214130806492150b02c01140b81d0714008103200440e0075060b402030904940050342d10119845004c02d5030710010055a51902d00f41c04003045051380c00c140d02040b4a10404149501040310a0085030350046514018407038803501c410041d40d640103a00c0c01a805280100300100139505c594046800e2058080c04022002d1800c000007551414003820292055008176200c01c0641c0c2140944422500f218005000400c004010000082d007003000107542030750390301c400780c0004030039001614502d040100075000745526420442c1c180000c3d4210702c0d421f00d24068420b800250000510401d805281c60601c42d03940c0d070800d1089180c415480003041224580742078000b100584417445200700c0c4074005507210100340c5c80 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 576082886 1250 576081636 576081659
    0x10605070b1b0313150207050102091e0a09020702010309060c0804061d0703060f091b0f0504060b0a030e0f0106090b0312040f06050a1b030306170a0c09020918010f0807 74
    0x2556105400d0b400c00114510004400b142001c29025284944159040e10b01c20000c90740310704800c80380759402003080303000f40ca0802001000194005410b4440700041700000b405800d10303000b00c46405901040e1071042d6442503008116241d80f0040800c1310a020220203800c0500450b41240c000b81040c01e008081d100804000021203d4100100031060445c0c0d50782e80640a510728008015030b55001c50000b0030342d40c1c4080074100c07283c24080c0c3c0d0610305041b07608003003101d51f401250299081201c20031001e640e10701103c100006a240001e18000420803150420b6030000c1c07044507079801d060b404501c0c0c80b040e5102504c244402c030100d450030800540700c10501e018512410869962500c01000014020f000600b8581d0390742c175280c2e0340b0405102096805c02c05040c02a00081c1d0f90300024040c00c4104030b540c1100c0c1d54503000525006243c1d540fa00351001240c090392000640100d81d605450f203e41d800214290b00e420760b000c00355a100c0e04207400440c0903204d5920a8442d40c41c0010340c049148 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 576084136 1250 576082886 576082921
    0xf15020703050606120a120329030c060d0915050105310507050c0a03050306210a08160807062a08040222020d051605040e010e1b03010605070b 63
    0x40b0241140e9920a002c00101c0100090fa00c1d007940142c038011400070f6456412900114155100020300103100351500c0c40c1032024110305101e6043c4012401702e555000245030300c40c040d007115825a070340c2c0a83c00e44000750031005001801c040582010000181035504024140c9078144c4a00d0034204048200e0300c111950510081c0794012034030b00d00c25010416401c05130f80001c460411611f010503c043d03c0746050418030003500051404010300090f880d041003140e04605807921503184840d4207503081611090300e104002c142d003a0020b20104115991039001c0c25141d08815056121041802c00c200602100110003000c080804040d4218450099004802c11590781d03443c0108d5466909015842203801d00d02c090300a06540c003260703c410039000038440542400004620741c10007080702c64000032070440c6070050002c00c3c072043c004c0e00340b107100c1d250458100030060500303a00c0b8180160035400000d03000e603c91140000000c941d0941160003003a4451045c04100010350b07980d00030308500341a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 576085386 1250 576084136 576084143
    0xa0f0b04020f070f0f0b161805061909080d0e0f01082203050d0e250b1210050604081e01020414101101150513050c0418020403020a0f15020703 63
    0x180300d014046402c00d5400460700344203424403c005001c0e62111b0041c41022a180d211100000140d0082c640e030080c801c1010260300c0320825038007070a100003c0d480c1e01580f850964071010100001120510034107003c03005000c2c100640303643c0c4940380401440c584001100c0d60103600c142d01c3c1c0c1042c651140c40c40c5485101402308900781038500410800313a4250040c0c05030100001030041781d0100ca070318400c00e0303039540c5000000d0800e01c0b5955000d048030f04d81322981d00c1201281241c204600d11084d42240d007181d649250000d8165a02440c024060b1501d4000640100b070104020603985400920b000000c0617150b00b0122948000508030701740e120318007c2e16850020100c040040b410008400380c42210541072a02020520414140c2142d00c010800300304411428010003090525120030f0007002c0d8004024009031400c5100e0500510441c45140c495803130803170010484010940c1603034080c2d41d00500f05000c0568680140e07500b6441c038055030070034000340701c00101003e00014041049950 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 576086636 1250 576085386 576085417
    0x30a0213080a030e0603040606033008070e1002030f0301030501050f130c0b0730030b01050909060d020a0915031a0f01050103020d020705071d010602060702060a0906140a0f0b0402 79
    0x401c14140029071b000500222009911070501000151100c001019100d00c2032200d200305d0002100c0425600008442481c03e00c0010802d105038194040340201050301d0994040569000c100c108034a14440c0c0d410b82c22101d203010001001300007041d009140030304403a9103e8181c0f502d9401c403101141d11540401800c1d03408510003004400c2039800504521030291000c0c111042070a815003800080750682c100d01080031803107020b801034162158581002d028038010341000c0300303007010030b03601c60300a0240b40c800c59600503900110f58446507807102406401c4418440d0b81041041001c44100a020403a60a25203540001c45aa4210880c43c031030480030303145820b96440d100040d0000d500c056030700300c41c0f02d0f000c0041201160041000c000181100c84007034005034181081c1001d14030301038224201315040071050103010381c1e001a849411421030440000e190000c0c0c90040010300001d50030240c590b81001c01c2207000d4019911494525a034681c080c090007520a00b00004c0380303e140c50390b000404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 576087886 1250 576086636 576086657
    0x90e0d020303072d0905010f03091a180a05060114010f081302120d091d040515070203040302041a0a06020601121b08120705010b0a051e0a0b030a0213080a03 69
    0x82c400c1c040b913100c2a4a0b55241400c414060a141015140000c41c020210b0302a000402c100c0d644140200c803040024074041003032402c0c0f0740e9030f0100c0d140c00040c4c0c990b01c2c00c64080840d4010203122070f41e0900c80380010840f00c140e10030385482d540b101e20134403a2814031035002010394115405013041c0040426159600c000711340d1415050364125200600598109440b029130003000c950401117084c8480b10ba442c1e022525180114030348044c01044c3c1c01c5519002d0820070f000001c0c0c40040d03d102c03c40b240058506855031150012071650141d030f40060340c000c0c10851708a540840078248a0b1041d1010703030ba14014a41c440c50182c0c0da0396000e00c0340c200c803900100c88e5840419030f2000b0050080040444a6503907590b1011707560703c2c18003511001e1584050015200b000c020007441100030812054030b200100c1c0c0c0c907000000302d02102200c0e180c00001c60441c07404045903100c16451002c1c1441d8a009910381c14041e070500000c2d00401c180e007164080055011130100c2001824907441070341a130b00c1c181102c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 576089136 1250 576087886 576087901
    0xf0c0d050405070b0318010e0c0607030f050f040b0408060907030302070612060e010e100f03020d0602160b0411010e030a02060417030d02070602070c151d03031c020301090e0d020303 80
    0x40c94020415101c030301030301801041d2080c0e040c1c0107501880f8018000f20710b045403c3c1010f8212450807080b00300a5015051103203250f220642503c51503600740c108601c14481c000d50a0300c1e64890b0440c02f00303501100150109520315540003500541d1524412500a0340e642c40c1c4440e07803440c07540005000b6a02c20001040260309c00c40d05000c580f204040c0100723095560364141d2a80450a800801007a40e80504001042c030081c1c000d20300034169100c820a00c2071a54010074003a8203441c601a01c003540000b00f070180145850342c4ac481c104d91040b45000a071400381080d1900c5482a00b03a54002104941c0080d01d901c0c00051314004103800800440c80d091401100800750740094820720a180814450200c0c1d044a130710141c259107005290143e9500924a400502c0510360b80100c1040b02c0460080d5080540c442c1c050099410740045d0030700c807401c0ea480080d1540c043d00003011040740346032542c2d485403000c54000d103040b40e0316030300c00740a03a03444686000d8660f0240740c0d00400692041c000103624 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 576090386 1250 576089136 576089141
    0x130504110904051003121806080709150206040201180e0606032d0103030f0813170d0c17010602030a050304060b010c1220011104050114040b1c050f0c0d 67
    0x1403054008000d49400c601c00c0101d0709840003103e5001c03204084840800038480000c072006219002803811070300c040490f0b0700d45044a10b1502a9008000b0000005103140d070141140741c3c0980b8283e551070f1101c42d6255002507650303c085070224009078482c8001d002d098020b010304401d803200d60400400341d640342400e101c00d03608028505540101042401e07400c400c076400700c800740c0310500c0039100362643c190301703002c2e200e60a6008004200200070342040340400c03141445040c1c4507408640c000306c3ea005000410f0039802818505100d00b40f81c0510003c1041d0040e05460100f5045124050541c0e600c400580c0c0320300510030044045041000000e0000c0c030745030300010690605040c145407050b02625071612640d075105240002c25012002d0800728000c52550301c2c5c401148074001d0000c002d00c0440c1080303d001e0703480380e141400150a0110b92221095090300c1c080d02034072582607219032005444aa4000020301e940c0002d44c82c00300424803020f105088548203000512442d4130b04030912400000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 576091636 1250 576090386 576090401
    0xb0606071b030302010b030601030c0e060316060f030b040b2b06050106030504020906041e0903051c020405090112170c0312040602031e040f080a0903050a0b1b130504 73
    0x511000401400002071050030708020042560810440c030319007540350107400c5401c200d030401d1080c0c0c00301004200066036100800103451040c045540b540e198000403030b2400840d0702d41d504417011440d4011074495840241000d032500a9501070006112a0051000f210b40c01e044441d0030216120b9040c1c40c50156411840c1140403250990134000c2d11510380f2000c407030003030300000d0000c0c0d00c510a00c01985820404150001000c90781001840d40008081001c004441c540c40185030720b910040c414540500281c41681c5070540d0b50340100d00c1c00c01c0d900802907002d4010548103426000020031615050380840403d140e02040100b0b242c00000090b98154201051a0030544030030000d02100d580102d141d14096403040d2805610303810451203100c00050000c00d041794101a440401000c20700714104a80d00941046410b59102c80380f10307081368410035a41003d406885202d40c5007040041907034005205074545a24810019a0070302840d0b42e41c49003280d40c8540e080218028445403405d07034400310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 576092886 1250 576091636 576091639
    0x103110405040f080c0106060e060310060f020f061e0f070903150b0415051c030507021212070b0a050705090f3705030708060c031303120e011a0a0f030b06 68
    0x40c5034000c0e65603150140d8005c1030f130a61355035190301c3e040003d00d030001d4403080d0403d4201c0f1000c0c194985048000012151032280718100b02d07540d0404942c20b0b0090110704000c2507500f05890007840e2480c03030201c2036000407800303180e065248400a88203c61058806000d800c095544d0f1031024516204d04644c41000d0480329411562026802c3c49981c95219501a280d4062020803c0c68a0101005038106030114007400d180b20426898000961000071603a555504452103000780209403035003032804020159041140000040b00b005001e40035040a2040040c42d50a10aa03500c038135003217605000307030b00310641c00c030a5180c00c0240c00d150031008000c10011800c840c981203203a0900d0340040c094550749040d9941d40203101440141010310a68010b031903814000c000c582845440851140310042503d221440034800e00010107100380e212400c40b90050b01c0a100c1200041e510700d000b000740c69207489080700c1440301118681400341c982801c41c0d0b0100381018040d07142d5103c00c00329580041555 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 576094136 1250 576092886 576092903
    0x501090e0a06150206060f1c080f0f030403021608150c0309010b031c0207092307030b033c100e010608030d020712110307020d030e181509010311040504 67
    0x421000080100400384800b51350040c2600c0c14800140007070381100c610124043d141c501c0b490602c01400541d0741c0041980072444a65800802c1140850790186080301c1107403030400014041407640c009107442851000c480d411700200d94400650f540c40703030a021a000ca41c015240003428815498000d16440741c00d0714004161400c9000000381010800c0c8421000726011026001000b68100200b501501a43d0750401028080504130002ca940341089080d403084103400180745c0c2480ba1300054080d08014003280d070b226038500a40e6486000f61051062040c89072940c40c114200d28200c003800400500010f080d03122092540075019004540000c4229925140c0001d8006000c0000b02094140544016141c41840c0760403400301986100403010480101f001c001402e002008642a1590454000305031221a107807e0b11009000c1c0009503002940e143d000702e080088049a80c80b0b0000e160380c00340e5801c000010000c41100a000141050310b401c0101c0b0b5580c03d05611194109010708000b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 576095386 1250 576094136 576094139
    0x90a02070f021f031d0a060e0307050d090e0603031c0b15070812090304080309041518050708091204090b15031005041503031b06020903010e070503060705040501090e0a06 75
    0x80b8086000c0c0824110110305001d1002031004d40c14407032144032001c06000541050f241440e116964907040d40050103072950351246c800b482d542081200e616aa205080d116001500714003d0903d1300d180c401c105801080d400010041d10b40402141d00c0c508050030103401511401c504031006101812070641c1015080e040c41000c0d02442c400340000b184595422030340c1c0c808006e00c1c8015003c000d0050003c650041c0000c0c480c4810100646174171642c240d800080c400d0b80220700c80d8404100d03a00c951403118882c50010700540b41078015501c5400b0a48481e1003a80765000084d03950806541d454201c40c90031320050000e4041900680440075000307000d424075a50000700d0182c1135206941412140b0304120b4100443d0829024204403c03803281069060180f85403400b070440c8120300c45c90324420760307100b50300810860345505072180502c001e0000c105414000b0440d076691680c500030144248504000120010b01c10b0042310181c0d0b0307060707480b984200e02d001c4840c403021300c02410f980040c40e2240c0d070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 576096636 1250 576095386 576095389
    0x6080717090c040f020306030708010608030a14040f081b0f0a14040207021c0b07050909070f030f020d06030614090d0503070210090308040b13121b121808010605090a02070f02 77
    0x140c5004c00340382000050741c0e410b01d074040514040142c2d00005269041c02400c00c090100802924040511400e142c1c0600c41c0b010041405481240c0200c0546c0c1c2d5074520118141100203510f51008108207015980c00c085101004800c0140b0890554860540c900910212038540c030084410b82d400340c00941441c049600003005c0720794500400000c82400d00e00710046c03200070103180b0b40101603801c03c10305e44050440402c0b841c0c41c0081001c001c0c094800070170203074503100780d121041c1c0c03510b184004c5480f004002c451802501c0c403840161507650614171082c0d40c50128141c1640101c00e00d2000740344185004106481c40d80004214006600480711354400d05a11406141d203034502c2661480d40c40d20b01440d002d484501c028005a5190b100c0c4401000040c808030864135002d807035400d25000130440148910381120300d030740307009000c03c0c5403a40c00c44045403c0032400c550482000c890f070100c940c40b418010b00300c035138230300c5241d40c000c1711200401c034105180d50041c6401d500076041d5a903007105940 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 576097886 1250 576096636 576096641
    0xa0e030111030f191109061b0d030e1612022b060c03110a0801091a0d050d090b0c0d0c020406031e0201110106080a142506020706080717090c04 63
    0x58501c04481d862000f04001c080241c1c400445040f9044c0040118810100e2484280e00174408410b00850b000501d0180c60f8040e2071040f040660510304075448914418030040107020711002e03030f810505c01e0b4a415450100344200780e405588202d0060515410f00d902000501c010046240e030010088002c41c0700600b0060b40c4030400c0c03501a100c0860440120240101202c1138068455200107062150300d82c020346c000c0b829811602d44440110340c0e030040b40414103d42c0c500221040e40002855102c100304003001c0b0710710402c1d40040d2100d01c1b4244e540d01d1003040300c0c45400e00b40e50280d004a08155201030041e641480484e002030000110380f034490342c44800c040c000b00704e0340c030308005101500c030f0456a0145004141500c410000e0281602d0051040d47c0c0e000e0f00d1400412200a50125032030b0740d03800704084600c10002090000800300b5021010f8584030382e501a00e4018001d06001007850380c041d04000c0d01517042591015001a111142c01403c90800b41052800d8014021580c610b13981c0c50 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 576099136 1250 576097886 576097891
    0x6020a03110d0c02070e0118112a0f1204031218080309311e060e040b0a020a0f0302090102010f0609060f090c05090907020c03060c0903210a0e03011103 67
    0x855001a6607202d200f0003918141003a482800382a081d400103020404035500300f986c1c030a41d42680070030706d604450321484140c024104049105072070602e07071006110784810440038428854007a9140341f0744c8440c999032600b0300c461220000d03800c100010800201ca1443d0071940d60818600010f500b140b4034162224100070f43c1c042000c60b8808070748486186001024034801b4140a2004510180e400d0321003a030501c0a40b0329419403554a04445090740b4084c4000b6083c02c51201e03040049503101d41c11109100d8040d0350030750351980e1032000100103000c503100f00c910100c1c0c15260341c440707401c108c1d1044010394840e03030311141155200c44806110801d01d01030305010305495074010a40604000908029021581c010380c2c106040006d401c2c083d6400204464403003000b038440b0b01540c0d40d031103816840e0160744050903805d03100d141c0420040e102048068141408210151b07140d0181900c400341c4148030040425400c103500300f242c82042402800030b0f031010240500003182610b00b500003d03603150000c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 576100386 1250 576099136 576099157
    0x1c081602090a061401030902030706110705040f05240a15110f010606030b010302040509010308070f350c0d1b08030c0c0f0703110f0a05040207050d021603020d06020a0311 75
    0x4070380f014001a0403065030b24103a42c0c0c0c203180400c00303112150000b99440348c452081c00140710a000381029405d10a01180d405040007400500c01c2d80c8081c41200000c110444010b01000428940c5074807100950880c003101d890010443d40c040f50401018400010a0322104000d1040e1300f040401d02602c180182503002504070000074502e86003a0020f016580e2009800781018030401080c4601c0e0307a88100b003419650014070351515040390b450000440c650f4100b0152a0040207070500091160030810701c4030415002e5088101c0c2600ea12000f45680980d814400c95a042039044403e55481071900040d104840800b1a40080c0b0a8481100e250b0055039a800d01100010364294111000c00c542050385403c1070007050220701d10740310f600313142d0080805a44035455408081006688000d445400303080300620840d940c0302d851500c20f0341c64031015603840250103881c4d040112040d018401d84202c03900503040307100b031094543e560304c003d42c81540b01c6814107584105241050300c4580207400d0b101003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 576101636 1250 576100386 576100391
    0x40302012901020703060e0c0d08030a06060503040506310b0405160e01290a02060717151203040314060906010e011202120f1b040b1c081602090a 64
    0xc070032040c00e498409404070607400380095094501e980c00190380c402c80c2d40100c0001590800f00310b81c2c078181303c0c250b07050582c030680c10348108050250901c010750103424800410006950740e80da0a40d460301040300c01810341d4203d90000340c0701d8880c20450380d680c1c40c801ea001c0c1c4800d405084100ca02089001004c0c0e4442800c07004010403c1b208100c0091072050100b4003409181c5005031110b00c1c058140900403c1c42c0090200340c1c0528420500050b0b44030861b040e0503256400c03c58001c0d0703943c100702c840f1000100c800c070207a0110110041890301032008080e181000f50500c0080c0b03c0c001d00c040610300440d100400001005c5103907501290700780e0001c0400f40401e800e24104c95850500180c1000d804810322000404c01c0082040e280d508a40d41aa028060740c05050303a000d003029007800003007445001e03021810550340300038241c2540c1c85504850070400c81a960f001d11540002810601c0c5840300d019604101040c0c0141c05095420001c0c01010f8000381c0710382c04540105816941c1400e140d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 576102886 1250 576101636 576101651
    0x50615040b040911070c06111504060b041815020a09050a031202100c0903021203070b01091b14030c030c21220209041209260d09060503270604030201 66
    0x441c0c001d082907036130a60354140c10440c5644850050b18143d00c604024006d6074130340c52960450a104000766003800301d100540d10700c1c00c3c0c1800710103002d800c03807020f10130343c07801841c14040104041340c4901d01c0d40140e0002c00c138810340862403000390b001d202d5440500c02d000f01c0001d400d0703407442109030185100704010381d50415403980180c45c0c40b101951a031241400d100c010307880c00f0340c440d011904480d0100c0d4101002c55002e00c10500b144500c42c0d029040c94103040001c2941d003001c2d0041d10030b82d5501c030055111001da1203003c0300c030000b21108800c0209001c1002c512070003c0716004c0c58000e01700b514040c0c40d00440c0c0d003200003507600c0708100060b0300c41a501041591404490000720710442da0100f0307240c160f8154009119020010b000418a1610340c0604082c00c0c41580b0358005400d41c1c0804d410042c01c01f2410781181a45813110522501c034104403115910311a00580f1304aa2890b210682141c61f1803448107203040c44d898a07c1e180400954040a07100000c01050780114003a40000135500c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 576104136 1250 576102886 576102899
    0x602041503060b0f07030507111002010515040204080c040e250e0604090807150e120408061b030a0902010516060b0306010608070e090604150303050a0e03070612050615040b04 77
    0x310b007541d02031901020240305240c00324224404403400c0540c98900075546500524000020428600d0307030a0700841c6101d01d40505980542c0954020381e003080710a95030381403600c00c2006030321482c0104441c0b03401000d00c4400c2403c294201d040c00d8400d201c01d88220f56013910803498000401c9a080d85000390028040242074200b0f05030710341080707050b82e0602401c80c0c40e0702c80740b505201d1000020241801080350a01280580c0d00030268044807801382e5841c40004a442c41042d0007501903012540038290224003d111075401c078aa088100410312800c40e0350b032001a030300070113000d0816030602400300301005100140051880c0d0043c89640006042e17603100d01450700c1c01c04143c10000900c808002404200794211000082c80345007210910742c01c0d03681c00086006031190354030002d01d44000c45000300030541c100d009444d901005581d41111140d81030105942c0380442e01c10000490248000380e100c821050300003642c040405052890100389849100020b980541e0028408140224050048 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 576105386 1250 576104136 576104141
    0x1209031b1216030e1507060f050f0f1905010605030717011a090411070f020306070306030309121109040302100f09020f09092509140f040b0709030602041503 69
    0x110300010000d01906005100340c002500c2841c1890340007201501ca0b08003014420b0a04c8004c0d2800070b031480f600f0010130550350b086074100076807c44206051800302c3c03900d040c640c0700b428072030080f0074080117854849072030031001500043e01100209400103410800c8215034002c040c000c040c19600ca42d624a032200780101110390900d40c1401011800004004c0c0140481c62074400003c1c420f07484e81e8034010800054010800322603017001143c000715010060100c0707a0b040f014a64002e40544d4856550b150003207044483c1070100070003141059005200d1408a01890304044e4401c01902034000c2e1108002600c00c070046404800607030044030455202f01d8140501c280280c3c3e07501013401440041e41c0040c0b49030000705040c600480c0c2d40c03030010316800400c0140d0108100c410003480d0400e006070b282821406414040d01c00341c42c0c140a0041c0201d000900c10f54840c9003a400e418125454a03600c025010001402180030010400b50101c0403607074500c000e00080c0025640c4541c2000800342c00343c207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 576106636 1250 576105386 576105427
    0x30f2a0b01050130020903070f030b010f180b010c060e0604020a15050f0a050403021c0507050603070e37031b150507080f0301090c0306080d05120c120903 68
    0x1002a10741d0b03c4c1801c0b0481106500c00c0c1079843c040300014081d480f505200074050000e1040c0c5c98810134400107201002c060489055074010360081c0c00b00d85e2102034042c4c80c00303110701c15407400200000e40060011349550190f00c0c1c07070a05240034980e406040d00c80009507406107141c0c140e01c2c0c00450505c401c600d48171401000509122041ca44010a4003070050810302032001403040b41078000410410b020b100d0000c41307003d0355005000f11f50b84004a81c20100c6505c0c070941c1141c040c41043e5021901d071802c2e100f035900c92401c1d96212407400c6100c0c4280304140403400c0c0c40a0800d1405250800e491310341b28005060030b81e442c80c802c20351501d14103014221000740605203000e84510340042c02445100301c113521407080c903814111350780c0340b491034200d40f05d100d0200d0f2030440840100011035211000e4220602c882d180707aa00740192900c44a86d80c0d10303181c1c002e0664003c01c008100850700200d04075002c0364000c800102c4a8108104100600b100800456500400390800555402130b441130480e16030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 576107886 1250 576106636 576106639
    0x50106020d2c0f03100e10230105040b0d17070b06040509190804090c090503060708060a090e0f011104170304050a0311030319021b040509030403030f2a0b0105 70
    0x180c462160481c007001440400b03207550003500d02c19540041500c040001d12800c040081042101d911603045041c3c462030b4009080040c1c90400d4080d03040f11401781c1c00c6207482814403000000702c2c0d280004010080c0b1480c061903801c505038103814030204010740e001160201e811400b481e0f54021900d010301c0503c40080038248950b10b0001441182100050301044010003808200d0318107440d81001141e03800b60b0350108a046041c038801e15070300d6500c04a51001c9034402d8007202c0c0207841d1010300751000c260840b80650010001c8a0030010000c0a0f0040c08100505c0408e403040c00e91003002403420f640d14883d1100942c14009000c201070803803031000c4444008900003a504241c14a000500b0360343c641e12020300031261025040d80c5035507040c022102030900a9140ca45410751240d80613440d0f0000600740d2000070880d03000c2050351f003040c0c0031b018850305507800503510b0b00781165400da60800b00350480f41c0030080c9200c03e00c92550200664045081000c0c10310140a600710705c0c041c85489016000075 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 576109136 1250 576107886 576107927
    0x3060b1207030c120c09050109081506060d02090402130f0f060f0807140703030e010515010527120c0f040209030c0d03120f0509250612020d050106020d 67
    0x4031040d442040803160004224074022940840e8598200c492a03101156820218a8203002e03550719a0400c085004441007a00d4482c812950380d42c2c0e898031038940c480c80c030360003c20b080f00098207850107030010a41035074864401401c0c02d140001280c102e8005241c03801c801d0707003070170810700c2998100d4074880014507181d0b12041e0b80604007000184000c0140542c0001d00680001042003903008444207011059022280c0791185503a003001030180c20707c1c2e440550554070702000f00e69007034001c0c0021551030030180c41b6036181c041c0711010390141d41e200f40e5152403400c50708851040240c0d40c003103655034850108401400e0700c0303d80500f00302d0b0528140603106c0c821441040030308120746002c40c0c2c0d10741c00c000444038503540741200d06040c0e54100800c1c841031001480d000302d039034030004d166100c217000380402d400700c0321070703a9030000910b07610300c800308511a40c644900c004015213441541c1440c51546ca4001c003504141e003040084c0251030080e0003500168103c0c0c559070300c1069100c001000e4481210095 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 576110386 1250 576109136 576109147
    0x40b04090b0a17070e040203070302180403090602070614030a060f060c060c050406080a020901170c07050f070308030c03090c04090606030302010b09150d0206070f06050f1305120d150305060703060b 87
    0x3841d5104013510681d0800502d441c005405d43d941405840c0c0119000340403480e0209011010584c81402150b0441c0404d00d140c0f00480c92a01c0059502c00380c038501d0300c4040d020009d60306099100e0304010a420300305070711840701141034012030b0901030040855072151200c00c0c0301e901c2c207803080e606d50102d07440802c4000e210401070faa51046000b070300400030b002c0c0107a80c0d1440300c1c0104e403101301454800c450041a6401c0c0703e411716001c0010403949010b9010740d040004803a240a490b0503240c0320241804c0f0050000c036801040520045421805440c1190b2100c064040800d080e80c0e6100000d03580300f07948120030010f041d028010100310076030880d80c1070a01d1620600300350b070101d0201c0c603450103218901d08402c11920760b02c08940b441600051010741c02d0281e482c020002c0d020803500309070709a08680121b000c1d648094a070082d4a507001024100e0b00d681d078410600303103030001c48462480c02d40311500451445501914072029500a1000d0101885c00a4018064505941c09501484400c101c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 576111636 1250 576110386 576110429
    0x70c090203060f060a270f05010c201c0515060103020306101103040302150c0708060f0103110a12060c0207082b050c1204090b010809150c040b04090b0a 67
    0x155421180f01c100c45aa840d45d06041003100c10a61000311009a00e02e1900c1c8501d044c4040305081c01210500990180d145803200e0044801021248004180c03c94003000d158004000080010307441402030802d603503c11640b10014441d45d24440705a500390818141e10035058010150a80c0c020003c0c03e003586913040000100c1d1314081c858081c10100004017000042d40350f0240115001190020600c070040c1034503140f2a1069401480c44100c2441404030000c0d131910b0110f0100d200344d0b80201d604803241e04e1901c440f040703c45a4030707400303502c0400210042001144400280e100794002e00700010250800c50020380b90035410380101440d5441019440c1c6c4105d00300141031114403151621b055103460300380c0191560301610f00b14041e030b8003a08669400000300100a172003142c079038140c1400240300c42001075809843c2542c0000c1c542c1c000441111a81d070741c04459075040340b00d1014140c0341c296a0040b80040d90005d40040c0009612840d5000c40f0340340c890705002c00f5005020786800e0300020540c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 576112886 1250 576111636 576111649
    0xf03100209190e06150f040902041415040b031003060c08090706110706050d0e030a08040501141909170a0f02060c181011120703170c0f09040b030a08070c09020306 72
    0x1002030b4400c8507000003c4441009031415a0400725001d0106c948403030329519140040c0d0040e000700c165207984140508604d1030402803100c0700784107502406180606002c00b000540e4030042058500050007a40000064241d00c05e040882182c3d42e01c0c1101d5082c111000c60800c20300d0307407100081107a41010140c0b03400000c6410760850f0b1641c00d0455540020f10140340140c2a051107000060201081c1000c4a0303421106543c441c1d4441c030b008220303c95080e02028500c0c8400d580d0005c15020440310013440b410740345c1c400c0007a50702855015030820b410002513805030748020056000200b181d8207a046407601000314507048400c403000c15082602800620781c0d8010000e00082c89194103ca20344012405400d5140c02041c40300161200c8514440f890621036001d440304400050381440c0c1020000e6034000744601a01140b98113a15011500c800f0b00345c55000703044c583d03902981d0395110f404256001c00101d424140300388007850302d501d4181040800c1c25400c0e400219094010000c008046d66000d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 576114136 1250 576112886 576112891
    0xc0203031305011503120f051801080a18061b1121041802190c020109090c0513030b0601031b08040b270705040c02070311040504020f03100209190e 65
    0x6081c0001c07180060a140e40546540d44407400307240440d41e004018411b071002d08002003401d50b220060070440c030308412140b5104035107101010040d08201006558880c180d020b402440a903004120704008054290550241400c00c4500c01c1e07a0711618403c03240c2940c04a41903e450b810b00e51040c204400841c0c3e141c0350080a80d00c91030113000a212226030701101502c000d009280c000d003000c40300311000a402076204c55444001c0784000b446001d002031141c65a800707819410f03903684030340c1d40c50254400c010b01800c940d16000e00c1400e0061041ca5661042d0400046000e149144070742d081aa0002d411100301841c018102c007440c1841040080e004000705402541c08180d10009070342e007035100481c3c05088451010084541e0711902003074540000c002017580c00032102080301051442050340c0d0b441c45480000c19000d540c00110740c8a1915030f01442d03100303002800404024a03103000107030030010034246410303000b035011a03424880e0500b010034800f000d000078804d510060600000b6569441c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 576115386 1250 576114136 576114151
    0x801050409020406170f3a05041d1524070816050a020a0f0f290a09060e060906070b06210f060a02040b0a050c07080304090e010f0c020303 61
    0x2140d652000b1911180d2121006009072403040100082400006495041c541c00080440c8a40740401000000c0b0441890700c00021a003041c0241c070300300000e402c1d0600c19101003010710200b400000b9160b00f540420701103850a55200c43c80a03c0c044ca200b402020326102894050031500c440c840f0140210101e8202000300525840e03229101071a00800d180710b2003581000603454610b4100030080e0015462010501c01c0340d00d403034926291741c0120344409141c40354444501044604021a81e1b1000781080f0007002c21000c808c8a100000e0042c0c0781d2382c8210350101c0041c0d00f81c08100191a8022007010f015841164000c0c5400c0c210800034a5500130600050256610000801d038542d4442c503101201b040019401a09000745405064071000c0300a500d040310301520000814041c11842120140e43c01d4600003400c0c10300c035041c115000d0700625120a064403c1601c04154a2410809000248140040494114a0b402102d400c0d0384442d03041d0902c40c0e00f82241529140d4020065a41c010324 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 576116636 1250 576115386 576115391
    0x106020a1b050406030c05040509010c050d1808030702060609130c27050906090c010816050f0408070905060406051c0818040f020c010c090b04180e010c0f03060603020a08010504 78
    0x81103079820300000ca6001e6a44945004400000c01003940c4819045400c1158100040d41c0e50141c0c480c26203502044503800610108142c803000d0b646a17116650100c40e03040c00c244182e1881d035945a003988203a42d0302015900c03090030014549820264650300100740c00301c0c1ca0507501c0070341d80c4ca041444640030f000c600040c40c006082e0311a0141c1c0b404080111000818840390514002c070a86501090701d03101c141d8025400210851f5015080c03890044145281000403400103000441d1282c03c02828080d07401010400080c035400c0810808021b811580380004c1c20b410320380304110849115078040e50054541c071f414009a0130340590100211a0010356144d5500c0541443d19074862801981c203034082d01c0c14041001958455001d0f203290a0100001c00c5110b0100100b130702d48141c6e0780301c1d1400484c42004240180b021240040101006145003c070340c40204008a50a4818088600e03001800d207040328a030a6925005580050115081c11031a013840340500070305401c81405214011074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 576117886 1250 576116636 576116663
    0x70c030308060409060906090b010902131a090603090708062d0903090d06050402040f0b0d030f020102091005070b01060e0a030204020c0c030111030a290d0525060908060106020a 78
    0xf1140c2d0400c19286600000c02c104012203450814000d0101ca41c06440550048001203420609842107030030900c8d00c40c0c2c070000c141d40303440b080094140304801c800b1441d0000b400042025224403015500901e850301c0901041d50402007003a01e0568014090794981c0c07440000703000a140c046c841240000e0250981800301d594040c444d83c510301c1100c401c950411120b01c4002c042c4101c40e84424002d92080780c060102d1419050244141c45088121030341c4585000000340019000e440960100782103400003500b440712080000c0c145090040c05440820310000b014010056001001030240590b802c2111051804070080f5000c0003507404000d0040b507000803000c0c1400741c2004842030108000f0024810003201d814285015001550313052003d50801e8a0785402504280c650361031504051f000e032082c041090704201da0410211015038041c000c8031a2001400c0a070078864180203100c0d2220310308540b9041c0010802c040d81c1d40300024603044500140b083ca80c0c04144810b0b001e801104460505 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 576119136 1250 576117886 576117889
    0x4080f01380d0b0a02090f0a0e0112030903020a0306021c05100b1b061305120702030303070c08090a2402010902090a0c05040806161202090a0e070c06051e0606070c03030806 76
    0x2042c14680c0907281d0b000c95010020f8001440e0020401003070300341c03140d0880d44041810300c400064140100201d0303200c00c200512280b030400030000b404078007034648980d42c0c0d5620340216808002c541c2065030314070703000180680d442c051006103505003a01c03100c04022510705405940b9201602d8001d424481800040040b0f1146503610270038502d104400542e00303203060844d00c16021182e40c00049656015690401c0b6008188405032110507802401035440c40d51649821035510003242c500b1501c01381e040c00004429150020700078090084c28241d034003915a20780b82c2e00c1e0b410030652540300031681450802c3c130050310f90300c180c240c11840510010503125074284c81503501e070146410600ca94441d046c2084a0900168654507004d880354131101c1618603040d0149040e03200301d4030000e42005204008104510070a18a40c1d4420f98600e046e29a10155660b03540c29500701341d810300d80c8003d60062180760611000e42039500001c00311402c62400f180d41d039a4406011182c40007405024205001a001d03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 576120386 1250 576119136 576119149
    0xf030c0b063109060e0606090709061e050408100515060a0903020906030a0b253e031204020901060e0102060a0504031803080309010b0105091c021504080f0138 70
    0x101c5500c160144174403198201e0b055600d80d411919940b1908000012032981030143c0d00041c213950750713036032303a010340881040c01310307800d01c0b03040f50540304000d001c200000b4011801d12020b942072600707050120f49828240e00d000c03a410030861013188a40c900b00140d19006402111960483c3d6040c0c805503043e95540b40003c6c00c0c40101900503000c0c0c08039904001e00641c09401074013403c00042e01e0020003200925044a0110858a950f80590031000c040880c0c41c20800d25114400c1d1164201030600710384411003800c43c6c20201d0702408086120341072000310303d041c4420710301415031490240007041c000c0c0c0001390340300800b03001400b501355500f020500f03151141560000d0031041d072507501c00180e92072400d1001035200f01c03200c2c0c0b40c07940b83c980402d150350b22410444220110040c5010750002c240b07d0000c020000c090412a8840e0310f81040e0301c4000480e901400040c04140c001c0c0600742c000d0f2585909641c0c511404450304400420302c1c01c880070f907400c0b1816520b106802400030040704d000c0401c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 576121636 1250 576120386 576120401
    0x5060a0306111905030112110d050102130303030609020918090102090a062a02062a06161b1a0606090d150e03070c0e060d0f030c0b0631 60
    0x3001c2c00c2040242c640c1d030080e070041008041c002000c0c50703907040204048400780028050000d074003079240c0d070310004202e012202094090000f05210400c0b1050380c0d4460032030f400000200da00f200007641c104141034051007604000e010109003585852031a81c00030340107402244524844401d00c00201d90080310035410382e03042d5840030704504070040d00c0f10000b51030b81880007204038268500b1021070241c0e10b1004142034120b40d018188500b403003218181515100c03004642e100d0100d48040648042007010040c241c003030501c0301c1808807980015603000380000c43d101e100c04018810301e040e840008407012901001070320a40080d41c43d0b52504000101917104e104ca007c3d03842002d03000d00105000813601d0b4000c140103c40c1d020007410744410019500c9009059000e03000e0040d50b54200512642c402c02540c0c001001812510220010360300d00100c030307001e9401580040c4400c2c050340e0421501e01c0102d900940c04a600085080c5850044c03680c666020030802000b0461404095039003031755800c0440c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 576122886 1250 576121636 576121643
    0xc0812090106090f090c0b09031014090708030310050d1416380c010e030c070f05120d0f022e05010617070e061b0d14040b090405060a03 60
    0x50003410040503a5019040c42e000c0e20800c9460032081662090b81d030b02c0b54140666011002001061a1114185040c1c020300004c4d0740600610105e9818403100d0310800da50482c6072150340045040108800f8070304000e5070000004c0764010010b1260840d0351000150460b030084401003000800d501e0a06a428420341920f485031103050f40c000783e640101c0c3c8000c410b80300145589001100c0c000e4000c1c00c8202c04a9a1801c00c3c0c00f40007070340f516920340f40e000f1b1410140076000455074184442d0913500c0c550082c1140052034100301c200740011600d00000400400302140c0100700306900003000d0380c4032881c5450035000d1112006179000d04a0007444044650040f19071380c030400101100b01c0110603032140d10002d00c0c0d10300d406e001180c681e02035000c80e240b8070b03e40000103000383e1380c0030420b9980a02c45a592030f4088414001d60f400b903040c1c1c2e40e40501417481c0c031020740151401d410000d0b1603140d01540480810b502444140982022403090300c10844003280c5c00b041c10303203804001c529866565040030307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 576124136 1250 576122886 576122917
    0x8010e060607140318090601050f030901060312050304051c0e310905010f06060c08030c042718081914040801020301081510060309021c06150b0301030506070c08 71
    0x10020940104c05460314400e41107074040c2d000314110800040f0ba01c225542404100f0621400c050043c05801030b641c031101c10000024035545a80303940044480c40c18181c000103400004000c01c0060500070201e0110507041c2c202c6c010503440002a1181c010310342c20501448c0320080c0d600e8181d0481c01c1620281d00c080d03110844045410303002c078018010303204050b01c4540c2428140d03a100341a510401c0300300d40e81c1d55070364559921141d441c401e860340b014200740e4034200c0610010484001010303140b44030442d006103ea0300f01080941c4501901c80036070a062107845580b02180c0421390f19022a20b19004101244203a080a1001a0b40c407003c0e01c064200c80300c80102e40070450400540c0118161600641150391001c400d1082c4500498100c945d110b52955400040044500a400000c0315502c010a2001c0410301201c1400301d0907001c0509407180d603164510f2140c9405505900b1b80a0100c1503807244c074660440e15800e50307403000a81001e040014074051030041c4400c080580d003000080c6800d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 576125386 1250 576124136 576124163
    0x2030108100f143d03020d030212390a03051615020a0e030706020a0f0606120f02040606020a031d0a0320130903020a11060904063308010e060607 64
    0xc40c8404c24101c1c07401442c140c082c0c0da0030030580c107a0610300255141041a12400d050a40e03090008a042540086040d0300c511052a1005000030001e821400655030300c00100e05c0b842551626000b10341203803000002807018a1440c03a01b40420f54500301ca1b0103046c00c1d40e5503424541111081c8031410390207014210858104592108141c00130404050181e0b940d4001500c031004041c0c842c10f4a20a41c00540e1100810600281103000040c41c01400b5180004446684ea1403031440d011440000b00c40c6009128202011890a44aa5030142c111803000b010012035903074014103403560f41848034244c0c5840d250700f41c0040e41c5201c91240515881454001c410300480f001a040e80c1d0907046440c41041d1100c503069604030244a0041200e0b0581d009001000071070700c80c00c62070b000c1240c045c1e4020504109900683e02c0d64021000284074040d44a04800041c010581d4116101d1035a240b00c0d414560302c0080c2150310504040c1901c00040e01c8400b113031207280024000d885440001444500d180c0f10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 576126636 1250 576125386 576125401
    0xc0406030609020310050f0403120f050106110105011a0f13081c0815062a0f0a0c0902031501050c03070203061e130825050105091f02030108100f14 65
    0xa511480c825001c40351700e4a40a1811002d458084503d4200d61080d00001800300744074144441d580e428001002441499049032001603601c02d810200228030241200200010700340f003001d0040c42c0ca091003440050007401aa0725901c03840c02001100070300401d82c113840200c0382071424002c1103040c044039102590f2105000c103a103100452500070038903950005006680d4030384035800207000244201d14040c40c41003044540004850b42302021020340192040000080041d24940d1819000600341c4481d1460828690116600a11886801130003807006007602c0b0041114156402d0170300e25100d05115960518500400c80080e6040c4103080504c2400ba42c2e6102c030205003000400101115510225004060340520b04000d1400c4410440381c0040022007a043c0422004001e0045500c4020384605003074807030941d11101282c02580d28000005220406103a05881c0020b00390b003951b2401c584c064903a860307001818052511404c0c00120f054207179000b81001e40d4038803042d1200e03081c07200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 576127886 1250 576126636 576126641
    0x6050d09020609042a080105031009030c051002030901200f1c1e0f050405061b07140d0318030210020325080a0e0106050a031b0e09240403020a020f030c04060306 71
    0x1c0c016074114017001540c8518400c1c00d285058541c09001811003070410700c1c907100200060901682044503501c02c8900190060100f90041e028000c40940c603410411412402c41e011100d184c05042003ca0100d021514980c003a11090446541e005132112415210058106034030528443c2980c078003605480c4001c42464000c0c40814030300d408204013607104001c0d03c00c030350040d01c0c0500154031010028850342e40c40c406940d0030a04803c400b07801c100303143e40c60280388410080c80000790b401010015008650602c540d00044002500b80562040304c0d40b406519007194103021100d8680000014458407c402c64414184c00c102e14601514042100000c084a000381ca11002550811149442c1541705000d00c005444009104070005840c598400c0785030991001c041c4c40c0103c0190f030008011103290341a40c41680c1c8607002c5c0914450070380e503000481a02d0000301200e0491003041c00b000c650b0005926110540c1507440701c0041c1742c05030001c1e25007200ba9001c15446400d058001c01000200d8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 576129136 1250 576127886 576127931
    0x1c021905030a05031309052403010b190e071e08060409140102030f06060301080d0e130509070f0602210313021002011d06070c03050703050c01150e09060106050d0902060904 76
    0x128085d190310f6450b441103c0648400f69003400c64170740900c1075210364241c4544103035801030005000040d11103807030000c00d524061003c4e041c41031030000c0908100c42480308001c02da12140e00d1402c0c3c4404c4c1000040c241c52601e20b43c0e400030401c08482e0000d512030701c1d2540118011608140c420200030300102c511742c084e41c8101d80d00c80240d0f0003c8045602400c014094a041e2603550000d888941c07407698044480b41070b1001c103240e00803070805000194200d00c3c45418081c803e520040e00b070203402c01840080301301460344200c0171540440c05071600302d21600d0000704c400c00110003071a900e4807036400c1241081c00c8808082d50090140d074082d40d101c2e405500114081e0701e29030b08003011100c82200142c13114400c940f0800429080f16404002900c07407030080c8800c03480703424401e0800c050034a845003151300900c220030721100015401d200d00d4600d20013031640610020f000b01310a41c10404014114001c41c010101c007503440318800001c41d0346183c1500c0c120400584104100455001d18a03500782d400c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 576130386 1250 576129136 576129157
    0xf0b12150c0a0c0516170601031511090a03050c21030301050f03030c251a040b0310030618030e0306131b0b030c0d0b010507080a0c080712020c0f1c021905030a0503 72
    0x200c406c00701200b002140250480342c100013481100e1014000b0800648801d00d60400105401c1001d510f0640d2a03464401c042c1d4002c000411884000c1c905100040140d10a1195110f42500c40340c11009000000c0300d05458041d1190103d5a0031000403d145009050302c000180c0103001801410703240300901c00741a08001548446019aa80c40c807818201000340c00b80310004082000b8001002c4003402107806c49960040700d01200c2d41d81d111041110091440e00c80380007900c0d01c1d02c0051541c801180c0c4e905003412000350075542400408482c156808080003446911080f20000340400034030802c2d401411080084d958a00d407000d00da4086070710101d41185100e19140100110b548100c0c25681c44c154446001c0c1d140444181c400c1d210014540c0c01100c1e58002000100c2c0003e030684001400340d14150000d108008070402080010000e03d5542409100d42c0364090b403c80e0003034240280d200d0f8041d01c0780291301c800343c0031030f0203005125080b8541610500c040350f01000400001014210320 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 576131636 1250 576130386 576130409
    0x3080d09020a062c1903050a030e0616060f0209060c01050910060303090e090705061c0608160308130302040603050a031202040509280f0b12150c0a0c0516 68
    0x320b8280c240e55444c016841a40300e500000c1062031544030b4880d805245500003011445140e04080c80c20000740c80c03941049842d03401c00380b184410190003201c403140d0002e00310780c1136080c001c1121843c0166118608060149500e440c4000802b20031a4100c0d813150b280980225980c41d5668102406850184d03445505442034a50310020b409140c442c074030a5940c50342c0c400703081364500060300903004806004240c40e0300030a44000b56941d140c5005040719088100d020101d0108a05500d013110b0740c035400182980c1040d0030100c43d80d4940000d081c141c982c00004907840c0c0c2031700700700584241c8040e00000d421074076200000c0148180044c01c2c0f0306041c0302e0b942c2d040d50040c40c444420264000c0384207981c3c0014442d00070403006407048828030311012149141c415480d03801c19024060303c1000542070041070303842c0e0f41807c3c00d081465900c421034090100800941c0c0c1351131408101860001c01d410705035100407a00785401803007682c10352803c50300441140c20204d4024400d40700b00980380700303c200510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 576132886 1250 576131636 576131639
    0xf05010e040507021504051504121b05250302090903040e10060c0b06010c0b07120b0a15050c16150905030c031e070b0d0606020f061005060d0603080d09020a 69
    0x6050b01405200e00035941c050000c0026981c0404002040644129204e0041021a1603d0324041d008540f0950144141c2e000b039000c01d01d40600000c2202120014140081d010600840c1002510f61005082c000441000c40c2c0c51102100d568080c0f030b08001c2d07006810505000c00110000080c0c8241c0d00198605441500c03030f034107160004c0b1014450710010991031402000850013900300745501440c1810308000300c40303117503858024241d8122801404501e01028000007030140b4403482c0314140c0180c850500890800c007c4a500d50000381c41c0400300100042c03505410903007803058014241c0600c81c40032950b0b40300c4036504603181800c12100300003040240c0c0096a0b140c0000c4108902402030060000302c18428111002a4120070a80c1c7e038911800000140c1071002600810882c407180030006200c505001c002401c0c240c00c4500100c0c240d00003000c0c00b00001c9203029460071207208503601c0350350b40e060080c850301801540d407015021a101084c1d090f980c0906411040110740308403290314426 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 576134136 1250 576132886 576132889
    0x200d060618060f0f05010509040207060f0c0906020109080f0a02010b1e13020315191205070f0e010506190311220503030a021002131a0c1603021c03180f05010e 70
    0x3004a8484c01540c0c1d4039a0700c0400042d40140c00400c1d2480c0f010704003524080481d00c41c1c1041d80c0105503140f42c07940e610514a102554014500c401409c558402845424480d803111089800b8400d00409451030000c0c0c401e076698000d600100034000c0241c604e40c0c004106a0a00d014280311104071406414410303143e185d02000e03131007200c1c851510044140303100c041d0760302400140d5101d4498030503528030100c0040740300340c080f854810800d4031600c02040d102d03060242c1101c1142041d4060006c0300b4040f40144060350750041554400722800c0740c001c62007550b5030011000b40543c844031041600c000038429902100c0e01d0f48200580714146007024106641c0c000381a138901c142c45903071005030072584031000e8403002034000340081d100e21100c0e02c00c00c40c0c5401400f131a1000e03801c51044035010024403011954824801c2d03020515800b1b400d6030700c092550300490070342881d59121000d41c1010802c001c3c105806017007407000036180001907202d02d94032031424050702d02ca0780c0101400300381310300c0111015 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 576135386 1250 576134136 576134159
    0x60807050906030f0604060f15020f01151503020f030a09061b02071202190602060f0a150506071b060e031203041e140105070e120604200d06061806 65
    0x4070070016220074034543d1110010185030b0006043c1c01e510585039100040c103001c40c61140400f4040c141180020b40703085444c06481c00c580c40c6a03a90259040072404070800895045500c200c45182c10170344010001c02074101c00a10810b0700d40782045d0317008818032110b2105607000003282c0b0300c904002c0002d16404003140152002c12051900145c0c0181400c3c40b01004d40303011075840d03600c040e140b002c0b403000c06461813640003065082400142d102c1001c110800c19030610054006018040400c6109582d0010410b0a4001e01815020f0000042d0860400c00e008807200740f043c1000c68412006d42d06d4400007401c5040e500c61543c400d103d50340c40001881a6407003120701036603100c640010100b0a60700d207205800b050300010b07215601c05d001e4820000d5030a0007180e1040380c041c1c0d41e85000c440c805040004c11a003014035001c0c9507002608120000d0111010801a44080409031510f101c4203030010b1080c0d05142801040d442c100140007940000010a030444038a004a0500c422615101000725 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 576136636 1250 576135386 576135397
    0xb0112150510230c03090405040b1e240d02041505090a060b09040902180a02040801110304030c02040b030f030c03070507090b1507030e04090f050105070f0c110a1e06080705 76
    0x580a18074500a0382c0c226400000d03c006180b4100f620304065040300042d0440d04101d4054600450040812401c2c180d0031201803410511a00f041c4064201012078100d20390f03083302c06442221100c44049515915050300700b510650081c010312030201000c1c0610b1410741140b03e114050020705000c21400001303800341c1c0382550b041603503150400041a04000181000030000d80e0010f032104101500c201101d901517124005412025a90302d180c010b8190864512b050303131001c0030106000340000aa4441c040030641601101c021031444140c89c002410400d107000060114880042c2142c4180c50100c0580340d0700c0d002c0c20a4035203490b5100401401d48006101c586e070310216000810742c8140102000e00045800391038482d407103890080202d4203c07010900180ca1215044141c601002024080c140d03201441e4a400d1b2074105001201500c2d8200c152802402c40c0c800340389850168484414000081c1400c2114600400190340c403181118914040d282c0010340b12400501080d005404840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 576137886 1250 576136636 576136667
    0x1209060b0f030c15070204060e010e07140901050406030506040e030a0e030c03060601050a36030b070c1e1a1f1202030303041104150801020a0f0804080d0b0112150510 73
    0x20140c090a0713080e05000d9002c6172089900582d42c007404244072001594440c0a062001340064407808e0512014046423410f020743c114184003004401c4103640c2c40800e5030102c4d40d06003000f04190f1079030800100907240c6111540030303a1201083c1c048410703034084d083d00c1c04914203074182c4102c3c540d00005e00d52582c0044503124041002040310210552107452039200c50300d0307100716071180d43c07802e44940100049041c08150010003c01018024860390b07407211038002c051030521101c0100b0a9440c6054074503c0140c00039120b00403117804042c484105040340c150310320406d6445042c504088513215040d07801c0c1401c206c500811101044441510700480400c5400500450440d5200c0d903854003541c001c2c015064106803900080c601d000d81002d034080180452000250700d0325410f85000381a200020b42c06010001c4880a11021919100855411a03800340d404201c0519000c0107880300c7c41265114110300d880c280c1035204041c5058030a80580b5001c44811188800519049039850790440045 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 576139136 1250 576137886 576137899
    0x60b0310061808060403120e010b011d0a090f0f050615191e0c033b0609120f1002070b0f04031101150807080a05030a050a1209060b0f030c 61
    0xd00086000d2000c002d04200340205500203551141000f0f03060070800d84045001c90b900f54518240120180100811050000020050a03c055000138078030768000204545804103a24854640c4e01c4010506018100021080c4140d46000907854010718411003401141480c000102d20580742059080c0d6280703445d141c4490600d50001a0f0080e0208a510704100340586507914401007203644070040c1a40d090740e2502a0080803608010f00358062901c89125002030788201380d4091034040c10507002510088103c010f5030b84022002c9000c510909000c0b070b600064801e2001a500800a43e032a10b1510780f03c15100071410191000d816401020f030014054145480090907502d6182400f81d480341c000e103058040f0001c014110b80c21181c403203042c540100d00e1000144070409081150400500300c0d08000c0c01c28900c6074607480e44900411480343e040120014003141c840e03200b458004041c0302c0700d45040280c0b52191500e003005040320b602d8140039074510040d080007490041900c07204801d024144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 576140386 1250 576139136 576139139
    0x50409080715060e070806120d021011090307080a11010206040b04080711280b030702030f0a090b2b050f01090908070602070c0503060a0204032609031b0103060b0310 73
    0x44410966000314915800d43d600c540002d03400c500400c690740208803035280c031212824000c050200380000c581c250050b40c0e0001c0c411004099000661002c082440e0300000396159010b017084141d80b10b28400140c0c54841e00801090304840407484504e6544183c80d9141c0c40c0f095100103a031945012540541f91090890026020807694001001400e1199404919250f440070006a518030080c0380d0904000e0b42d040c84405c0f00402c0130105000e448080007103030a41c034102c100294f583c03240e0360240194103404611900e40302c0c010321181d0050150b44024640360f10b5103024001d500410810242c0c800c482d0b680440c101c15105200d010f006401c80d4262030b00356800d210141c03000d01216070007200e00303620400035007011034500d2000e490303603074411481c06a51b0b92074107042600c1c180001d00095005c910400c400c01c00542c0c000400d00c0c140c40501000a42d50910004a80c40c5000f000311558140c028005001c075100c005040315030035a10240c0301007140a4843d03a40102e9030008a4076080400c062100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 576141636 1250 576140386 576140393
    0x1204170607080720060a02041502190201230705030d050c0c0c090921030423060708060a09020a081009060b0304110d0c181407020a030c0302010e0d0c06060504090807 73
    0x441d0102c040490a0301c1c0100c21071304106454141c2c111040a007a5501050078400407000984074030f5604014801807880007100416001842c125102c002d041c440f0a4604101e800301c0d0285d2030f400c01103c1b0521075280c07080c0f4202152207602075502c07414a18904400612143c220405691a1429210040c44448159020301c1070142c809012000c5500c5039000c41615403030070b500080c11540302d100300d01e901da0030585810003c0d0340307030811a100e44403e008c20142034080c0000b112a848900d0746010034454640d000400c0c0105135a820030120745000065540740c1a401140003405001860041c210141d40c9100071000c845032800742082440041020a020501e0501486480d12000b841e604852001303540c4d020459035541e1010320b080c1d0440c0c09aa0a00c001c52003004e011a09414101c070440c84c6c0305000a484400f07441000341030007245030812050500c00d40c0000300d04c088030320071108034401e9404d01800d0514411000c0b5441400d040c0c01003081c0c1010b003c1d25200070b074011185030400031070744e6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 576142886 1250 576141636 576141647
    0xe03030a0915230a020307080a0b150a180e070f0e2709010f0204180911090108070305240c03090109020306010902370c0309030512041706070807 64
    0x144141c0c0d4201640c003000118409a00c03400d03050740f0502400d507003103185a002010208000400754514248140200480150071880389035101c54241c900142c10030000d000500710401b01c030312610304100c0c0450402d403d01e40007481c160404010310031264900340c4e5034695980c048400c0b49d0352800180c0f44103105440900856412100c038400900344020100300c1c61440300700090408e4503141c480301c80010302c25414001e00c1800e94810592005525050900f40307041007014060760419103441e5606100028008500c0d1400000c000041c02c903015940e40301e4045039030f111513000c142c0d00c90054102030700c0d25584005490121000800340c402c0c440c1d07030b01001d19030144c0000703246100325520750000d000180d40500c0254081c01104c6001600c8403030554680e07000c8400d070038150040d101e02d030580701c00070820881c1107001c9005900d0504100802d620701102e1142e41580004c219108560036655904542c3c405001540c464955803890420035640e4030b6501d200c1510760201082105011808152041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 576144136 1250 576142886 576142901
    0x309120703021512010b0f041a1209010203060102010f02212a030f180a12090806010f0303030c021b0f01030608030c16050102010b180406060503030703120506040e03030a 75
    0x51050350801a600d4002c41c1000b0410310702c00198810024035100650b040e45402800342405d5031595042035001c07505050343d80b02d14000d50b980321141c58582c21003d1040001c0740e02900b0245040d201c14102240914081d400a58126007d9400d11300b00b242000214800c0c0d032000344440403517200c09a942140c40e4406030002d050004000480302201601618024400702c4111004905554074030b0a070196030507414014140e800c1920341900c3e43c204a203000101e401040c0e0f0000d14018052078001c8040c1c07180d0343c030395000709038a000b000700001d00e42e0b00c104d190004032802518180411113103c10b00b03c0c2c407141022514003500c0064081284203003440720010400e00d4043c140066100d4940007118515000400c40c00403c1d4083c0003212800780c4d0201002c001070000780001c0c0144400b850015103c00300c000380030410b10390b0034030009041c000d0941015000704400b40640b540c40c1b42c1820b005191025031200e81c04058100004a0010309061040103680010f0a01450031915000e4801c80034040300d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 576145386 1250 576144136 576144169
    0x1014060d05030f070f06061a0a0305100503100f11090924090a0903320d020d06030b041407120b0414010501080a051c1e02030d0203070324080309 64
    0x18080c41c804500b2440040c5190342c06884030610f208818a04102580c0b101d8000038122840803404411701c2103c0d900340e8038402d600c2d040102cbe56945d654901c15041c045079101940c54442c0540420384e000d10755020001003c4a03072001d0205100049482c00c841c840c1040c010340041504000603103901c0c205030740382c03a01c204800c0b0343e44030142074600103210b5000a030b03044c0c07038980d98a5000204160700b100d60010b03040d054071a038a2080074002c1502120420341c6001c02c1e09600c1c0042e843e40c149010f81c0c129400c80c09102001c02c000c0d1307201c0c20980c000031022602101d0455651510ba070003880009150801c07200100480700005c25281d4422102c0b0201900446150416040c2194920b00a0094030b0180413000d00074128040c59091443c03070300401100c0344260851850b0b40310300490b84a504a0070300300150034501076461140300120300d54030074018544c01685c4003205004000d503150b049022142c120062003045550a00800c0719009518450450182c0c8108040020b0b03082c80c401c40030000d05c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 576146636 1250 576145386 576145393
    0xe070203070f110d0b06040e0f0303011a09030303151513180b130e100b21030c0d080601090b032a0405090c03040309240309080c0a03030c021014060d05 67
    0x2a0b0f20b004c14100703035500300100c444100640400c0341c2c03804c0920440002104850081c0f801008034600780740c0320f20040c0100e644c500b1840d02260781c2c190306c410840e10511006401c499030b03031400f422141c00528075200094424050351601c1561084014240c03014004000c615540461428803011164124600e43c242050342b100120601030381d810108220301c42d503451000c1401d0000c0c00a003400c055513401c1c644051450b04100800035184c107100a64981e0310aa98201c4444041100a00c5c42c05a188030406911642c0740302140d6951045030a03002d038600ba210000701584a180c0c1c00303610700080f181d503508507107440390b22080304c83e505114039046c1071074a01d024500754a0307401040c004c1c1000c5442440d00c020000910003010340c0700398074200138810b4120200344061121903998124038981c6140041580b501c41403400d00846108444109011344110782c1c5501880c540640942040c0c8003103400350080844502c0c03090411b004440c2c101070034001c960015a5050100250300c0303d000e2081d5036510 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 576147886 1250 576146636 576146663
    0x307050a12020705070602070906081b18090c0906010306061d04180c0302180106021c050d0c0e03010e06090c130b03070b03180307030c120e03190b010e070203070f 72
    0x20703102d10051200500074009041c0003814544068940342c60341e031120340315918181003000726610201d03000c00603d6613001105441407400c3e0006540d5158410041d01c100522001c0c041c101100140704c210583c0e0903110f4042541d51a001903044505500c602c2c80415002d000035000d0700c0c0b4007002100ca07200000c000255a1414134003046074190301e4441142c6180034001c0c02e00075403034014541c054100b0720090340c0784158141340000351a150f00c55030340102498295540c124240c040d800782c07498000d50440801c001804140c0080069400c00c0310309002c1d5103450758600d1002d0000c41d680744078200180041115034451000d105c012541d66085100d5940d4840c41001c0950341440448c000702010031000341c82e824025407142910420130740d00e003195402049000b0009810040301072140b0b4005c040358059030701d84c84042e201400540c0381c0641c9030181003001040000001200500c4600401e2013440503a202c000e11040b4034000e6400c203026920a000a20004449925210f4640d10a401849106 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 576149136 1250 576147886 576147917
    0x1b0c030a2a03110a0c06021005090a0c060f0302040302040f050712093f031d06010e060f061b1f06120209090f0303160e0103150b030604020714030c0606090403050307050a 75
    0x2840d00786c00c03910058100b00c580e040c07114011b0107a50b0304401e00002600070700328180c0e144c9a00f4901440355030240310600085c0402d00e0f000380e04ad00c0041d50003410921a0032400060030f0000e010881c0c0000201d215900001c3c00440c01d4868001e4a0b68000032446240710003404090140c807004034200304214544a1609034030098049807010b0700d030291000310301065009028000c000204000e03440b00d45c1701c14010403000840800490f042035080e9107004010846501080d0184a0048807040b6821462130040d0103800000c1d5000d070501501c2d00120014041c054094155a400c1c841d500d00154944810005407614101c0b42d508000710400310781e008455150300c0b50841d007003180d03400448006110700740e010b150804400d40387d01c2d00c02d10f410444c03080d54060000c282c1c03005004001c580ba8010001410b651100d42c100c0d903440703410400c2010502d40e01e003010781d9240c1c020080c050341401040080b584078203243d101d90380a958152921410359807107000840d404c2d0000b003240d1081001c140c0c4040601c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 576150386 1250 576149136 576149153
    0x120e010e011d0a03080a05100e100303031d030d0f1b1e050405100c030e060d0516051e030411060d09050c030d020a02091b0c030a2a03110a 61
    0x1034103800c90001c0341040e0180c641c48a0503548005000241d00031070311210020303074480c03809540003900c10400155500c910740544000302443d00203041104555052041b1000d415007800e049030300c281e8050041480d1400600d508175001119038155070b006000c0054803540342d070440860340d01c4403a00040e030300c03048400210003a841c0f01c0c4400089017070401c4014111030405041c052121560402518140c40c00c00452820a9001c00c2c1c0d208100c070301c00e1a0000c0521401d030071240c841005002076110b51600682400400041c0c96524641401c41c29a020260040050359518880b0320052011207040076614941c0d9071004104440001024a805280ea560b441c06402004000c100c00101d02c2d8052030554504841e07034401038413a5202041018501d40d0020700149800d0b81600e40540a40707903e000148402150407001c1000d035004100101d0302c0310b0020190580703415503500c0c0025080e6000303219189441d01c600c5941000451507600e07021038003c1c040820551100c0044548142d22602c2d290340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 576151636 1250 576150386 576150401
    0xa1211030a030504080607050901090608060102013c18140a060f0e0c090103020306130309090501140102070905010f170a021f090807080a12120e0a0b07030e0a03120e01 74
    0xc1800444e0600642c4010400e8540c00a41401d1140c500840d800001e400500c081c070a000030000203a0004546901c00c4d04140c2e00751620b20410140700110720702c424002c00780b045000c00108803c104444030810369020380f070f101035100c0b034070003c00341c8054594103928135174181c04039518414950100001091449000203008022000254880c503020190b4202103642d11454840d0200c0801480507030b40125005411040c0c40d42d6091880300c6a01d000d0351721010940c401418180f03410000190414072900120810400740d00f81c80350720392210043e60403103000703002d014003030010220b0900c002300b0200d61300c40d0b013400300c0012600c0381c0c07200b64005414400606150030300d9030b40c000e8002801e281c1013000040a001520040c2c901c050900c144581d980d6818078001d01480e04500320a010540110400c48031808820400d0103040d03107000303c450396032981d203a003141d13116000740004400324440d2166001004440016003403c0300d1549040707802400007480400301ca41da8425108481c04248119039 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 576152886 1250 576151636 576151643
    0xf1e03010801292b0609050705032104180b040f0b0301050c0c15070e130c0806090405030a120b0d0b090105010b0c0d0810090903030e07050f0a1211030a 67
    0x1c80030961500071000100f0070114048110242c84403503403544e10a0f500415800c40a509002040b000c42000391601c112150054181d80c03402d03084100380240881c4050039282d040e41101c00b40101c0100c04540480410401d000010081c4420b11403020307001c006070801d0309240008a04113420b10001811100c484810480081e510710210443d03040a0048607071062078160b8090504070300003440ae0b1685080e9003030304409151000014685402844891481c0502030004541c019900d01d50710010b200507a031540c00b00301c48800080d41032074413005051160754440003450900c207100c1010364003015421b10b002400c03a2240d211905c50b44a0005c1d5995413405164100210b007001c520315801c40d101a000b195101d40c0411440340b95110002d628009850580341407015a510712840c020440c1d0390f604444400350400c15034000b8035901d90480c015240643c02600c0e04e039940c035802c0004d0800000c01c0e00713400000003142007080f658906627030642d5500a038032440306501e00d0300010341064135281d0300f203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 576154136 1250 576152886 576152891
    0x40b060105042d06020106050f0f061b06150d0f0f03030e011b110109230a060f090308180619020c0a0c0303090605090a05130b10030b1507080f1e03010801 68
    0x80c0c00b03814500f40c0300030042940b80001c0100c14100030124100b01e0030004914042c05103c52800c0054490404940b0b210020342c0d201201a5032a18160b03443c2d0314250741c500b40101c11480d0700c90300f0b841c02800f00c018696000384078428140807559a2000c6040e50a0183c09041e6200050742403040c082c00f48001d458006884c0e00e1041103035107006004048106c1161001d80e1400001400084030001808604c100300840030b403440d515420224076103a5814030060509051068065080c0c0d8070b90050340c0068404d40718006181e0382e8a113408038020040c10a8a80780d030006022402140420a8201251941d03172005460803520a40d851701c1d0040c0d0440880c0c40c0c105030881001415801852071001e0500c901d031403032400c0704450024078600700350300402d03115074002b5850b16158543c50f440100e141001408011041c2e8060402038001c000700070390fa074044c8003803400565800c005071044459075607108900a06000f0000082d03086600610340030360384000e81145003040402090003860082c01000c002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 576155386 1250 576154136 576154199
    0x306111e09010f020615060c07120b0a2a030209030109020d150c0503091b18040506060301180506131106131410020d031e020f0301090e03070b040b06010504 69
    0x50882120f80982400c540005040c0503e001a0f08032450070120102d501c0c0f0749821504d0141c5040860071f5009642c42545052030703008100585007441c5c441c01d00000c1c20010f0039901c580244000c8680000040c9641c0d50f040702103503090095014040b80ea40240001802c0702a0754041036840b13125200c00c2d181010000c0e403080c09441c80e0300481101c001c1c140780143c21810501c50580d600c0011500500818001030540c007055101ca03480c003680e201030480503880e40c0c1028140652121000e40d912802542070003602c0000c02c0071064442080780d4818000c00f40c0d44e4a4003448070004406440844402000c0c1003580075540c5e5203c0038100c0e0b8002c1d015000b061515040c080032040007080a2280140c60041031403c01070f0300807601e8203819159050200350702c0203040e00c41c1c88a407050100282401e1000c500b0b16035a49111004e1410f0750031203a0200300000b4060919541c80c065504000c040085180010317000800404c4d100f60040c5040c10102e08040d16610b544400b10000c1e4000b00c503106c8050b24 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 576156636 1250 576155386 576155389
    0x403030509030c04060b0a050706150308091503061e060702040203070801060e0f0105120703061e08060105060c0c060f070b04060b101d121e250e010306111e09 70
    0x9a40f0307040008030303001c00c4850f161a28072012405030300c11403000d2200c00b10700e080500241c2c0d004000d01180c0b101c40c2340c95a50300c030b14180354945c0215038040d0044d5454403201010484c88000c580c000d920003807104041c58404071079600011003505a040d0005000d114000040c2c0b00d60010718000e84040d00d40030303000d40c1803141c024285005180303807510900340c5007040310550360040111303040321005c40c3e0200d00c1a52a1282900904221703400203800010107182d140004080f10b107541c080c1c88030f2005503101a41c0c4c401c10084140a0001c207465250402c44010700f2078079202c801046600184a1502d0030720316203403030f010700f414801c48050700e1060b00c40380f28020b64034150900310b40e00400f0b801c00c50441c84090b55400b803c041603520541c01801d001541c00e052034020000140c1007210000d0114030a800780804139283c5030401c03504401c01c60044200110109540301900c240c60781c0708200101b80e86076403101409011070040c0f41c1034243c0100007529041101500000e1103550a00003503a40308181d90 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 576157886 1250 576156636 576156643
    0x7030305031b120a0926031005090105030706030924060311010206070206070e01050d091101030606050f09090406021c06080d2303100803040909030207120b0601081b040303050903 79
    0x340c60141d802c2080041091500d4a0f264240c1c1094804000041c2200f0070f261614480c1c40a08448206820704203201c0d90801803400114030403030801062800c4030b65a41c0038012080c0080c001c66a060304039500c280000b91283d405203254a0080b0803004455003000c04203400c0c01da0200311210300302d0f101d0b0020310074008180c803c40b1030441d0a01c01081180750600009480d00b4014242400300b10310b070203c0c400300d68491800e966a20001c2e00702081482264038080c1c1002000b98640340c042424a0740000f403d500503800d4400794101071000500d0510418100300c1c00c048010400c99401c0d07401d01404d103d0031130644034404580203005001940c2d5042400039440d1600078010a020005841d280d03410b02c41ca40c900d4141050284d110950301e81c0c403040400b544941640c1c02041c603034800460006015616a00508241d43c0242c00303840d180c1d0b0715081d441d1201039291701d0241074022a107004c1030940d4800c10b4003c1d80914103540188000300f003415004020743c0554020390001d04003190380c84840c036040c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 576159136 1250 576157886 576157921
    0x1522150f09120b091f0203063d050d060b0903060105040501080a080903030c03030f0711060417031b030a020a0801080106030b0606070c050a030f061a030303011a0c0703030503 77
    0x5090962003036261005900880b94102c0004280c1d400380c0340441d51310481000304114410403250800d400c1e0f08040e500e00d0083d08101e6046200e130311400f015010a0340d203e1900c0306030b03440b080380c039000310301030f140c82420740c124901884403c20030200300f00801404944075950160900002c042d13510002c5008041c42c000c0107070401889285488010400880c002030b104c1a920740c424549521501d5110000303043d070240071300c2c00c680e0340000410003a44c01000001c40f0300c00c1070503481d580600d071244105155186000c45000740341440030100d0f21300188004000d143c0c026a80c0240740c03a00e41101a110600f40c01c1694154191a004207039010103e4000d001607024001c040c00801440d4a59104c807038459001410b15402014001103038001d100d00c01000001034503000d4140786005a4925090213000312106003552040c2c0341030034800c0d140e20860010199440c00400940c25642011003880044541c04244c0c0c8004404204c0902140b03400d0004000a50003a159642c80f0300e050040ba800300e000320b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 576160386 1250 576159136 576159167
    0xc0e180f2e090f06050f09060606070b0c13060201020a2607080613021204021206071403060307090e16060513060806120105160e040605152215 63
    0x1c14503414051800a180144620800550050040c02a070040c0010000e40c0d0016114070300400c9800184116030300140e00a041285140942d503a45070080764032050159032166004808004100c0461041b8035861341051060105030700c0d190b550b901d0441c5402e003690120000d07035004644440312603001720300318064420074251850002d00c2c0c1c905403004810010b022105000c00c0d1404034503681c81c2c00141e500c0702004204110f43e15115800c0c03e5040d8241140c0491040a0600c68640c03007100c04603185005144680b40ca101c090a102244202c9400c011320042e00351150701400550f850f01d500858013816a058003500c804200200344440300c9486801080034000e0030806e030001c2c1c0d00108840d00c1250214030b001c80083d200d039070000d510440c1d1128a82125801d0505003c020711440c855429506c01c2c985503110381c6d10030b035400e20055810381e11032294809450b45480c60400d0300d2034003d1040c02c2c840c0599079944201030345a01862405604510081c03114060081d410581103030f00c1342d410980 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 576161636 1250 576160386 576160393
    0xe0907050f180a0203150a0303171b030609310c0e0c0f130506030115120e0712060b100804050d0806090a02161e06060e010803160c0e180f 61
    0xca10140d0b20680c07402a00551641d0f074000002402408070888103a0a120b004060b6031031544d0701d0400802030000703003c0c2044164a19404249441300c81c17172030a005a40415203c1e4107680d900c5003005070100c1c0003410148003640480b13082009404541d01000d00500903089aa040340d1581841c00001e41280c008404a50700c91003844801603082c0103480d1055200c514060b5540a01200603000411907401213030008004000816000342d904007800380381c10581e484c010701c40300c1e848090040d56000711000c1c10302c0e0410744040c030541f03c1c0032005c1c5180c2c3c1c0c01034902145071020800843da103d20600700340310008000e9014801007090610003074403030044a19140e40d4a0504200042c02c07014080c014860150340066000c104030081d101c1030b01c2c0160003c180c0c404002402401d051408503240c001c66082d0b161400c0070440c0210140e02a0503030381240c3c0118107042c0030125006280c0d081600c00d0314a0040c003e00000d02c48013a9020a1298440d114000720031925101d10500e03010010b60041c41036003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 576162886 1250 576161636 576161659
    0x21b0105040807140a080f0a0201150e0118020408030310051305070e10120501090615080f0402120a0507080309090702010c2705030105040f02030f070b04050d03090e0907050f 77
    0x1114001503440c900d81086400250700c0d41d00c10003170700d0149800001803004501007040391310444284060401610795030000c2c82180304550000c00ac00b1040c1c001c00d5500311342603005001001c0d110b4224020140c0084006183c1038444840903d03540088031b4964030001103450501017420b22500400040003a060184203d0818a501170081a44520000d0291814800c081c5020340300f00d59003e1891051682003001d9610341c84804042c00ba14011264044c0001d61300910040c400c002191042c24542c2490000c2e03101c5034200440c112032049610024442c1303a0008020034014040480105203610045550b590b60a05114504000500120641e4074101606112541003d228248083d00519185081018901130000041c458100b6905503107014200401c009140090b071001c0c034000c4003201c2034000c03058001780da80c000398007403c46c20801c140010800d81c1408811a40d203203202e4103011000649440081404644c111280510f41d40b000000b00712138104a810287c408005591891a14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 576164136 1250 576162886 576162893
    0x313020a120515010e2d070f02071508010b030601020304030c142407140f0111030a060b0a0912060f050f180304230a0f1e12110402070c18021b010504 66
    0x1000000c1c8008840a881b03001203120510407241c5200121600e034440900b41450880180004e00241854003d840f40304008a42915085002c4015004030355524117181e0a01e0904056a000545860b0641c8020702001c40003400c00b0714004060021200843c4102c6011002c0020900c440307000001403594034070410121100d10021240301c580c129852312151403403440c680b440d00c0c51683c61a1142d520b4a10007207198400040114003480c0b003e40c05004041c0c40d204642100e12910507241c01207a42c0500c200011510181501c0445028040000e0184104030408081d01c034220341ca4118141c40b042003041a8604220011040c200d81e00110f00780790070a00c1342240b841c29200d00340755408000c926812550345400011002e4148501d0031100b0a80d0745040c0e00c0c000103240044420203115400103c0d42500c0e454004410310b0304001c0c42680368002d48140402903222030760543e0b21815000022800700e403031000d142c0c0710315500c010040ea40c000c2d41c000f46100b001c80400c00200341e4103005c20f10022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 576165386 1250 576164136 576164159
    0xc0a0201060b28210b190e011203090819021e10030f0e070b07020a0812030403030c0201021e04090b0d11100c050d02030d11031009020313020a12051501 67
    0x402942c00c0c9160483e1403516400d448500054a81c181a00e004107400300500800f44c02845010800f91407048568041d030400042d0020a4042c1101214a0500400075007440b00312205003640a030034100040c81d00e86050038100b030201d5003d0b00c0102140112102142404042030000162041c0380342c02d0840300c40005825402c40e0954141016180c0e03a4410852410754050002c510410b8219039900350340f0301c0c03030482580111006a200d03488191000a04420201e01d06014420000d034032442e40e03031190390940041c144816800110740d030074051010205010315060360038030301c2d07d40c09507166850303c100441510101141c1038000c401c180c0c0e8100003c1c1100546082040007101c0c2c20310303111481c2c1000c48104080c0303403014180307200b401e09000c8000e4010000381900a0901003c0c00141011520251180710680300040700703010044040007510000d41c05075400c0300325410550040381d006d800141e101035940c0c01c5151000022800c020070407a00b0400c03111a8010900744042d65854080100350 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 576166636 1250 576165386 576165427
    0x504150b03032101091103070801090f060e0702070305010c02010b0607020f061c091101090b090108040302010e0d11061012080a0302040f0905270a030c1a0c0a0201060b 74
    0x49440d11021040659582070003600c003111004500310100070758003841c100841c5420f104a0400918004801240304010780482e072091f100d0751102c08980c1d2030000b040000b0803005407000401980c0c2c040c0850030400e0000b00f2802008194014100d80741107040040c21145528905400e41e0326100001c2c0043c0c44030000e46900320780481c0d900c540c070000e96010408510554140c2e80801102602c00c000c00c020661245884501680c541c0c0301c070040081c01076400003a1401340b40341c6034605004210142d03210f80541e43e4054131a1002042240c80c0110307851900701111201004210030b4250f484441d1001c001199104181603400c0300c8142c60099280e10221240c0e1001c3d102d903070001101c100082c080e0701118001c104106c1400b281c16980c1600100909003a20100d000d4026000314a10400c401c0c02003040e125502000703810449640c0c0da0a440c41318500d50704441001130b100301c052824542c0c4c0ca5040c4210030344480c0e16030720001d544009084a40310740008056039410701c0189900c000510340c1d000f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 576167886 1250 576166636 576166673
    0x3090c01050304060207080307020304090f06050a0e1810090303050a050705070f0c080604110f09150d050f03070803162c130c09090b0402120406050402010c14070f05040504 76
    0x541d40d49460504001a1080312001f03009560000140140c0700d0740040281304640d9107050400c108c0e5005003205060b540c0c00d109095000781071203824409403016103c0b80760800252148200c0883c0009a00f50801881603485c0e014107079a1000102810381601406500164000c010892480c09540c09415030281c0c80010748140703501891170b0108581e40c00310501905400f802c0303070301e689098600891460701c03c018070307401384041240d06850750911050381802440c002001c0200f1a90784c4051090722096034100b91910312400001c105c03190414401410303c90701600c145956450001c59402c0d08800d6080f09101b00800684658407070f0b030882e0b4030362080581c4106d84200c035900722070008400c048a0f100b080d44951500700d110601c0c5800c1900401140c42800c41489008611800c200c2207005014021203040714010001d40000d40c5a406650b20610504245c40f0122890b01c0700030f070306400c4d4882d40c0071652040c0c40c2808046e098200c107a00501c412103041c4014a02a5900e80c143c500c0260104c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 576169136 1250 576167886 576167897
    0x81b031303150621120c0c030b0a0608151b131211010f141e03090d03060f08461109091c02030415120c02190b0a1407030c021203090c01 60
    0x140c41c50362140c40d044031b98075040b800303c100107612400c240050403030036145820164640072000480300c0340070800b07100d0450070b4203242d0032079551a007a0011800d4000b8029503485020010305240c5054401c818003d04101c0c0728180003080d1070300e4440f076003804605006040c8192003145c01e58070f941c800310702610000e01c0990a40c5646d100c54a43c11300807411118154420000301c00c10001050003c4d14101031900e40e9014044155074042401d03990449009a03405a00542d84001004448440d6001c282c1110390448a1681c40c500c162080c2114a02c020603d44010301c02d000b0520090519150070080c1c03c44402d2500d05002504aa440c160030301d40c10030180c0403000820342c0d44e00a0051707400810f1140745079000c0c00011b080046c1020212100c4410320707840d1507070200755a4070024403205e003070510144140103409952100d8480c500010041031115454451401d80c00403d5198140209000d4030080382034084420042d003403016007003080066080c01d00070808400400991414400380030b081c039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 576170386 1250 576169136 576169163
    0x5151315060302120a02041d07030215040905190b15030a090501200a0306152f0307060b010e010c0b01050d06090804030f0213020304081b031303150621 67
    0x60a01601e40c603400603501005071504420f11103c0403950041c158400ca03010001c00c00710b59003403140c015008111048a41c0008001d0006040070001555030004560040c0d083c9a55100403000350350080f02c2225242b503140c400d031901206030f40604103607007508403880c4205031010000300140d0302004051403952600c440e02e01050100039031080d044c412214040100c8450015210691a4080840700001034a49000062210128400d400c0b91500980c2c42d01042d6180f40500f514000c100012845c08146450b40c070307060b140f07040005003441792203840d022401510030b01c00941041c024000d058144240100103000003035103071001030f0541c8c01c1220300c201d00c0c1005040c4140202030b240401400707160000340220078064104252160704e07208690350701910039841503041c16030200350f9005061040074032058a00e010803041104001c0984002c0301e0800700072402c0d40d0758001c0399070300644110011345402141ea448502900c4003400142070b00c1480d50b080344601ca840d580c2c0307903440908182070321f800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 576171636 1250 576170386 576170423
    0x804020d020f0d0b100b090f010c020a0f15030501080102210702160e010f1e12021201051e0a0905150601050f0d1415010e0f120118051513 61
    0x82c2200c0b140d20240003070990105628018030440fa007990450000e912840d4009900a200d0084509510024240c0201040d81e900191744801c4e0041c42281c0c0001c803a00b02003402c2400030103c0c0e000b41a9401d40c1c40800420000c0581102d03070613000105580d004001e040d98451140304034070602c11280004401d940c0e180c8808a003840f0100082c0000e502c140c1200007040a800d4078500e05079881e0784c00e00300d4070740d50354045540604845e485c1046000300b20f80081044040a48617409940c0c005404428201e02c51240c660071503400b1203c44070804001c000181201c1c5500c188580e015111703090400200500b9107070240c0e21802c184140510407002c0000501c0c903442042a02e0006180100007500e4980000401c00603082c485450001e01d400800020f506040400d8480b00504040e1101c4106011200c01d00002c09106200590012418a0b120008000074441d0000484042610b0b001000d041d140c15402c1600511642c40158140010b02090200c0b590300240c40c0f0380c0c001986401220741c0d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 576172886 1250 576171636 576171649
    0x80103051c02010f110c0d08070c0813030b040f1b29040b07030c060b1509040e011b020703050c03060408090d0309050901090606080f040c05100c06112205010804020d02 74
    0x4c0d1002e040713080402c50142180c06002806050200360151082044500303000c8907002c2080703455070009164207203500003145020000303229000c01d080300455010b403603848042031040c0540c2c0c102c0e14600d0414201c4180001040907044904000703108000480c40e040e6148071603d2030a400e081c501e00386450b03403d9a0341c03040e0200c400404403407042d20b48606083c00e000e8000d07124080300b6611141401074142c11441c1c5844014241038205141908152000c4240001050703090010107456503105038180b03008809440e085081002e65000b00701d40790847c42c00034208a4105d16460190b400302c401e010006210b0025100504419903010000c494241812100400c4550143e038110040c41e0020860040c2078001c072050b650785484d0384680d519181d40c8110710a408807000740c9a00e4007030006209a00d4141b800d02880c98907440c0042e80320071700362200d10881e0700a02c4500350704d20002685240d0342900b8240458000880e07411000f0903031800001030f00a810040c03000340705800b18803401e0119503640 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 576174136 1250 576172886 576172901
    0x3140d0e040c270e1b19051608091002061006031104030f0308160e03070e101e030308131a0a09141e0c06072010020a02040c080103051c0201 62
    0x49181d40039819484810803c11842401515100e090000016008100d01d514045d250b1075840c0900c2d01c2d120300740030381001700341c000380f00309041100402190041c07100d120420b210b541e001c0c8801603950100c490400c4664900c041c1c440042d504000c0400c04041c4450401004903a078605000c1108010310100c0d40c0c01c0d205603003004144000a1401d0740a0660003c0c0c50381c410f641b01c50030960902c920071800d0f2001390449002a41c03540c8848810301c03005610020300794012040c0c04129820980b52481c04d41449070012541d600c002c1260000c0003815440601c441c1c0040e0100130340e1070310780e503a9125007a52006d901c0d080200000c400020415a956030f900c03440c02c242d044134010f100c0005071129192160ba108111407071294419001c1401508003007904031041000806192510178039503903414819880d0340042c4000c2c019a0040c01c0681c4400c001004001c0301070340076000c0e26807c1d1041004943e505519602082a05c80042c800140000b41050f980015002d884143d0000440100e0240905 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 576175386 1250 576174136 576174167
    0x201081602011d030304050706170424090303020c010c05120103030c0312021b060105190603090c0b030f1e070f0c050c0a06090501030614030304050d0804080d0903140d0e040c 77
    0x440c0b50020f080100800070390701841c0b02e80c040c2d41200c2c0c2e82c0c9030100d940b4441d950104001c0062a408140000d200710b03800349012801c4214801a41c608100680466506500035004603070009071b4203041200038400e0245242080c06e10303d040880340c240d00700500c14140001000e101000210000303040c003d60306004a024840010355507400074092808003444801c50361002441110004507092030100c1d04420411000445400da051074a6011000740c000c1120a0ba003003501404044ac7d01c4440c2c2d801144203c0240609200c0750410810007282180e40e20010030040019205101040e0f9000da06005108028500000307101840d0400a0a103819000311940c03280d1500c01c00244c0c2a0001940421114242c80400c03016945a079034400e1030000300c40080c0c1c076401c108000d001514010380d4019074140110703444d07814a9203403c021864180040c8010000c280386920400400091007101e800440d0820003030000c05100e0750018181c9840980360794401c41e00d0326801c20043c2e10480960a51041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 576176636 1250 576175386 576175421
    0x140d031403010f090b04052e0305070305030405100905062a0d0206060111010e060c0a050f0f04140d0302060a0509010b060f1317100f0f0e0106050103051003020108160201 75
    0x2d655035840060f8075248154890a420440035054030f203400d106035441507294040c44003109045409104007010307140c500560041c88500d0220100d00100045e901652141009642e60340c10f00c0300700245d114542c420074042016015052006403030702420345101020050f08030000c03500303004141c3c0b150306140d2280b0001e8443d240070a52076a42c00905940a107101fa2a416071402141c80707290309031200e08042800715403003500854103010b5004010b0604600500e0030a0034414a00003108182d4045000400480808201400504e600c80c0135050364a0781110b00d03a01c002602d6502a4407510010040c180155507030000403042c160a40080b00d50400042c5070650354213105210f005150401a0760303900c8410080b1000c140310903c0030140c00c1c041000f1004040e405410514280540429100d5659458942d242c84541d00c18074080d080031801500d001180c00c60914000508076032008282d613459100080040000d41d80201c00e982d001700c000c000c00e403101c454400040e4050302940201020912 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 576177886 1250 576176636 576176639
    0x405030f0c01091202180405150901050106080604020a0f080c0c010c09180621050c04050f1608130215190503181209040506030f1e07090501140d03140301 68
    0x10404107074501e8012090f00e608858580b80d4203100040d640e612030003500250002c00142c0c8880141c80240c2c1d0007840b5408540c101403070040340c2c68515100f0f540b50f4120383e4641006110312070b0450318450b0f110b6001d031011400d02c4a0304400400c3c001480c09034070148040900407802c0324003481c04561003417030010000d02640c840c0c080c004001d400180300341203100c00c0c120314020700c9c215940550b2048030b9060500074042000c2c40c024500b40019a0021203041c82180c11484280c2c6139805418405c981180c041c10b03c0340ba1040045414520000c00c3e001080061410441c8a52492041d010f129805032180200c00c202e1060042480c03103600c4100c1c405003a2084400f035160f078000001c1d48590003c07224803400c1c0c214040481e540d0f540003981c156122105010014841c1040d50143d948642c0050803100e58400d0340281303030f0034190400c5606103001103104400003140c004110030001090350b9001041907616001d82c1040c5489001c249502c00c82c0d000381c815080c5841404034040303840804003440e9a95 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 576179136 1250 576177886 576177913
    0xc06020f191b0812121f181407080403020c0a05100c02210102030106021603112704030302180906090703150e090a020909011e0b04090f08090306161211040503 70
    0x60300000c21101245e4044000101d910030401d1100150f4404810081c1c081d504196000c2454102c2d590300001c46036461600c1c0303e80d00b0050b44014004e01d60307511094401d040c035040081c2000014a41c5074002c10344108100041d8680380d1725003080c000b040c5440303d1060f2051000405907286813200b04039111040c0003d0200c1407065006504a8a840d000c41c0c5280c0b00e0740303654500c1c07101c42c0e11025080c285c07035000030080c81c1460000102015440c41c0003219a015203180c0140c2e5100680d010340010b40d002c1640042e5041242581182c103100300e0b064041450000001091410001c2c01401099160000311104c2044244410003404202c5001c503406c0c50304020099403035000c00420703031140782c0c0c84010407110b120603c41d0304880d4803241d00c04c4001c04091007440c0045c0400c076041070b400c1541c55400720041480c00b40341d84c2070300307100d81041d030b40c0c80701c40c0b6003014038000024099a03040c1c03000042c0c9038016a0441c0c109201051071601c0071403062840240b00c0380030301855001d42c1c0c144c0070795840141c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 576180386 1250 576179136 576179173
    0x31401050922140d140406050d060305030c0a060b0d15020901090e0403020d030623010c11060708180102030901170402042712030b030c150409090c06020f191b08 71
    0x70300c603807801c40c4c40c3e20144c04022650b519000248103140784041200b40403041c4504001c0890018034280031405036900d0381c0b514030b5584050000d4580390017884460f4108180c42c01203203d181b00490f107061310034000b9211402280341d00f405c41c1c605243e0014100c2b085074055070310100240401c45981d000d91500d411302944480c0203840f0040041c2c608040403883c1c8009a07002c1500c4840152074040b40c101103001516803109a050640c0d4040c8000c58482e9135681d003800904401e4422242503460302c40e00c911142e0511032900c17582d41590018042145141d070300000181503d01f070030225103030b00e8950f03001160041c0002101c00c3c4000041c102c1d415080111109440c083c180b041c0201101503000201c104c04441b0400c41084d8540c019070001404c9141059400348900c61a17514280380958a070a5442191140303e03084480e1800039a00b000925018405100205402d101411072840390340c8002301d0442d8403a000401d0701c040661040740000c04c115064000d4062802203450b5810002440e521 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 576181636 1250 576180386 576180413
    0x6040902030a030f0e01050406140d1d0c120a0506060d080f070f1401060303090501121e0c0909090f02060c03090301050a0b030d0c0b0c2b06030201030606031401050922 74
    0x1c509170b04a1244154810400c0710100c403096a07981c00c0350a41059201150740c454256080c000792a203852080e05c10f060120444920041d40003000d0681000003030080001c0c6c4a42610165080b041d2040c01203680801c039240d00c000100d8005206600700c1c81d00550500400054802c1c1d0000805c24034100302c801200c0301c1070305001d01d0304450140d00d1021801e09035500c030f010050005848442c108001e50107403003880a61024442e002c00c21f500180548202c0702a0702c0d81014103a51140f00c02c0084580110101000d40b04e80c52051041d002580c6a5001d85050650001d000702c0001981000c0d990062060384e80c071010003402408182411031b0305102a200c03107802d05100303029201000c22100e005030500b12030668460f41100392595903022810f210b80100c642000c0003020601203c40340c3c1e02404d401600140c000b140007503060300b54000103044640940140090528080f2841c0c00350380d00070700d251304507031045074440c41382c0e5625541c01103900c83c0c8000202e02c002c020651103080016064030141d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 576182886 1250 576181636 576181667
    0xf010219030e0c13020a0c1e0219060e060901030b03160314010c12150302031f15120605370515060a0e010e120c0f0303130501050306040902030a03 65
    0x403800d028003c2e200c021081c0c04a60100719100040300c000c0d002c0d0090998460142400c4219101e291070b8502414001e00054880014558004086180c00304a80313040540051406601a051103005811140f008134100c1c4039203004074000840340e200e80c0001002d900d02500740c90101c0c45200810400940764001100c2c4850b1001d000380302c45505200381d2809030540e548440400010300300708401400140e81d8911038014403040070004d80c900308080e500c800801d120b80500480000c034040304560100b4012028248040c5d800c01500d00c10020318441a03400c00b40c00a01a2508103c00d580340503d050001c485174246500d00d014600a40103010040702401014412983c401050800c002c0080c03190302c0d031065003400100c1034544106202942698181402e609a11500c00024101d450030b02142c1d89a5112104006590400e050215000c5106400842c145801024214130100e105e01031681084030100c001401960307a6000003034056009800c0c0c2e28207000c6414001e0070100300c64800f5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 576184136 1250 576182886 576182891
    0x8010b1002030f0d0e030409051e09071a030a060e070504080c0f09010e04062405011803020a1502010f14090d0903020a0905070c150501050a0801050108070e090f01021903 75
    0x3280035400072040b2800e103614903680c9032412210703106420042003000c1c10f510940c4010b00c0041229000352069601030040001c4141c828840004c1102d940c100042a0440a40080c0e0042045e080207091200e228102814202c1c0c89a61f02d00b02640101070540c4801480d00300141407000c042d4210005000f82c824810a54000d806400d0910600ca0440032090303400442480c010031050603500c0d019600207100d0000403a0b8034488141c0701030002c4169003404081118240e040100750b0f00410481003021210a00404151035134001039250f107450b126100c8020040e5812404d140c3c0700b9401400c650418900802190507a40ca04201200381143c880481d031283c01114160a80255001d10840786c0c0103100709807060801c0054405032001414003402d00028100d600001075101074000754118203a2070000d90f03581361004102c2012170952040311580d15010050181c000007044a00513945c08076403061554036054425440c08155132500902d5510110324004155509105d4850b80015a6001d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 576185386 1250 576184136 576184159
    0x813022e02010b0307050d0206070821130f1511030108060708070504030f02150f0d05220206250f0803150a080c090402010e0a060c050d0306080a0b1f08010b 69
    0x9900725801c9040144c2d140d030040340200040e141850401780d01c9440035060710300b441015a14021603800551355007211004a40007070780c03001130340401242d100c62941840342092200762070781d40c6803101e5400007030b0980c00d003c10f881e010680d0540200c1c40c0c40340701e61201540c0350f9440181d03d445000684a100000392004c0106410f18810760645041d260000080c0c20b03500c503546d0070020340000d001d000708070554082c0080d018881c0000060003441c0b0354a8004180c6282c000c0094010300810314008800082c84101030380961a200103440c5003440d1000c0c0002c65958142e41101c1d95012618002d20303c0c500050b400040001c00005503000b956511650740e0656200c0c010080c44080c1d900400f421a8804481e003403051030801719881e000b90060600380b01ca000c0030b0f400b15a02c25041d410000205e0403810380c038001c0000800c0701c02000c0d41c0d640303020028641003820080d120210303004040c05104094020035405803401003415450410240140780c103582e43d030780e890301070040206c0c614410100c41300c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 576186636 1250 576185386 576185479
    0x50f01050105011b0c0f08030903010506010311070f0602041a0d050705030402100509010e1f0909060b030601200a1a0a05040c180908030903131a0a081302 68
    0x242416100144c441041030400301d101440080c1ea426010344403248407041c0081c000880140d2500034120708006160780300e00c10790500d800d40381c01805c0c0c00d04152034030450300030b012402c1c1c0645402d26407104514818800504101002c0c0c0255007146c0413181040075620714596045005050116501409119070380d00c1d8441901c09000468002e03400689c0c00c10b407031103d184501c0041c54420014103200800044070408a002624411401003920180c882401d4101760800041c1000b0304035004240300c030038100307610005240409080141400720412129108802c1c001072002c0c400035080032110442a1030802c80e1003545000d841c00825002c1d0310200d0080b250901a8520850f0001e4210300e1913890003860300c0f800c1d000040c01d42d0801e43d8440002002403100310096001e00780070801507440d01c5a09080000d0483c159004203040020078150368103114801e41558110201c5080140140d664a01c0040c0403601824000394400c0350900510092034140b8298a03004011a081c2e00da041c44501c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 576187886 1250 576186636 576186641
    0x41a040506070305070501151e0503210313080304060b0a05040e0601290301030c140604210f050a140d0c05070b03180304141306030b040b06060c19050f01 68
    0x50319400c00703010090400820700401c000c0140501c154000150340b400c01d50b00504074801500071042000481125a24210007080040050311044018044000004848043e00814a180105c11a40100000e1150340b1070b02c103001c44a07072300940d900e9074a241c07900d000001800c00e484014400c20002201082500f441d2180c0940000101300504407a400c190f408440c5250802891806282c5000307100c2c1c5200002c4095400cd51190440007070080c18080308088502c9000d40c043d000d10014072040022050350941e060001030b8032841103480403801c1c2000303c03500300c0e80d10003c1c1003842404220070402c51080207080040101106848004003082c0701103d401c50b04180c00740a9a000b050305201401c0035100440e04070001203a09002c01c0f05010000d411604241d10081921886d00140129401c05148680d04c01c24600410408282541da4000041d140500080c200c55403100006034951200400c4800340c81c10303441207641911440c0ca5010107500780c860100c900340900b541c0b00300d540c030050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 576189136 1250 576187886 576187889
    0x90c0306061205100b0c0a0c08030c0a06020306040207060606050d0507030b0609120c1f26070c0f06111305030a0317070201090204061401020d0206010e070c02030c15041a04 76
    0x55441100340c0b07141e1019140900b50103482141860740c1c41100040840707000c0020801140c00002a2030a44050f01f0300c09400070482c6d00441040c1c108009490007800d0102c0c4900e03209501140043e104e2303c0c0e0a021030000e000702784004094a01e0008040f8200d50408050301000d0100350041c41140d403405012070954a03480c030803642007407041c05503804a29200360445080d01c01d503404c8407900901d1000203081802c82107407000317811401031181c018460f070001c44140e00140e01c2401447c11060b07003000d01c0c03406000030900307001c200b61510100c0800512409441105801c00c0d0144191000d1450455070303a813005030111001c4400c1100010346080108040340d066070076031101080100c00302a04400c000c00249480c045568403001080180c0d1070340316640103444030b2010701801044440001e8500240440320000b0755105400422084500c0050345510085a01e0000c161811520100b0302d4580c0041c141a402402c9044520189800d1005441110100150354915000c080e80303881052240b17 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 576190386 1250 576189136 576189149
    0x71128140a1110030902091003050d050f1b0a051204060201060906210201050409060b07021305040b18030408011b021c08040f020d0501090302012906030402040e0c0303030103030207090c0306 84
    0x2074840b46141030411095007041c03904011070400030544c0010307005a81252881911106660203000340300041061810b0610a400d0075840d080142c1c2042c1d40c14090380c070745612500c0c2000104100058144100f560701d6500c80300302c85800c1242151044243c00c2401108010340c80d081000074126901e00881044504604007203214035007040b0043e0010f40d524000740d0602504000c0024540c000c0d10030040141614030700c0c2c644900c13141c410004080c5144400004035401c14080c403011075044218503030461041048210b281808502e01e0b41140550f50056202c0d500e80307010700c1d02d50b0704540c0c01c504561905500f5582d185400714004c4202484074070050f0000b036116070000340000c4070f0252000400b0300040070032403802c02d00d0350380c28259403480100b200149d4407082034040500080c8286d038400c1c001c82960141200d010004a40c0d035000c010b201902c40d6480396581a0790f8442405104c40307a01c030180076139a80c1c1d038503428081d680300d02620903010f10910704407441110178428820042520b11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 576191636 1250 576190386 576190403
    0x40b030c03091c0201060812121305010f020c07030b07030e060109020d0908040b0a090f0503121303021825050406052107032301060503071128140a 65
    0x503180d80c000c00d150002400e0307800c60311400340c44103540d68403580642070321a5140e001041071070414241e0343c140318038846c1c8840c0c1c0040600c0044464121807800c150311108607030300079030380304c1c8141405030141401840b2403a5040c8005111103c4d804045940c0c0252030244044540540f42c0c900e04030212140e40100e0800c4e5008100140000310481c0c00420210340b0255010034640596243c0d4909644503900070f04903024005001c190740364100709041e0080072a2030302c508400d45060003090326003505140415036202d0004210030341000703d40e500307405584c01901e4402441008502d01d050a0340a80d02e0003030418910740e00880b0240f021080d40302641140d6103040c10301d494498107035026040f0708000c21980c100015051202141d80c002144209440d5130045a03485002500c00d41d042c0519444130a096503541c010303c0100d4000b401c9a0f0444101d11b0031030032460521445900b03284580c0c00350f0b4030000d07a000780911025219008507212a01030b4462001203842011041c0d81d40207461002000d010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 576192886 1250 576191636 576191641
    0x506030c0703080c0f0a030c080601030b1c0206160b06090c16110123040515040b2b1803080f0603060610030b06040f03030311040e040206130305010c0201060515040b03 74
    0x240f0800c0007a801181c0c0e858200d05158030007644d6072490b0414410700000903558140000789561004480b6001402820108503000100c400700e003003c0b501ca0414044c0310200c41010342151140350842c1d52040003008103211880282c500900500c10a40b031052080c0c1401c0e002c50480000e15049643c80708408458104e0320307806a4408400c120400845418084107405e0080000030003d086007591185204182e592401e00040010038003442c50486034082c0c09100a11001c070b81c5004a810b4000c3c01c880004161046006041c1c0303540c20740d5027620040d424981c608462181c10804051040e119403604803859a031300407903000b00c0c841101e415074150b20a601190700c5040c4260300b04050600ba2a011070a1035520001c0b40703031540315070f01c440c441c1d905515042042c10303410711501c6603119400785650303e0549042c1e82d11b00180006080030348101400a1000c480b295460f0024006607070010007809004d5514001900900b4035104242c080c0c141c150300c02d403030201000100d80940d5020300d001c43c11034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 576194136 1250 576192886 576192893
    0x51908011d030301050120031216090f14220b0406150519020c280905091f020706061215020405030307140111270a0b040603050406110c0f070506030c07 67
    0x80c04440c100d187e0b020941e011509182d503080c0014420301c111741e42100e11504001c4213458009a5900840d010040380800501018110403182000c440319803c05001c09181d01c0001480c00144116440c0a0f00c0144022642c03411075401c0f1034900d9504a82c104052581d860424190101c084c11190000d44200503902c141820f4091454100060740704880310030280e44d0205042220142c2c80118403079150640400703440c90181300e44003606c4d03941c00c24400b078240b804035181d58036103801140e0b196076504440308891002c00c1c1d05984405402020601505544452000e00c0d0f506100046d07806e004051200d0303603255801d000300c80840f100900103502d0643d598494001554807031050240d19501c4226542140b00007030301070076074400744921000165000010207a44401d0f000f0350302e4041c4c05880020041004410141e804850f030b41d09001c03801d580c480c80e008000b807030030103520407001e0700c04207080c4480ba800103004032138060160102c4c0c0409440740204080c1d400300319500000786800f000b01c2d4000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 576195386 1250 576194136 576194147
    0x1506120201080c161707020301050604151214071502010b0a050a090f02090409080903060a09030903140f0d030c0207050306040b0a020f040b030408090906090402090c030c04051908011d0303010501 86
    0x70096804c0440707100195a50716035905010010001c40c0849012861106618080c8640341d0050000c0324100880c0f4480c94280c60000454460198424281403012040c441041c01c4c004500840b10701342c1b10115192021442858080360b8071b1801503103441601405418a01080419500c0040411210502e01074425000c7e2520091b102c050700d400703024607800c3d903c541c000c41c225035101d80502500c86c4c800000b41032500c00014030703c000351801c02c0d0660011a800501190550b90410b0031000c00400d80d84001d860b0030440c40a4507024810919284e04e815855800341c0640744540e820b80e81c245643e8810940d0301d1005890140c85d805001c004204201003a41c001c0100142d0075900d2428155901d59401c0150001c6405469080e00080c0c003100c14503105000c2a0700150848010044d82440d4022500041e802032420003c4900000070503c450204010380d4014000182402451021201c107017801c4482441003104542c00c1011494030f00d1a035080480c0e0080c6490011402c507841c2400443e01e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 576196636 1250 576195386 576195397
    0x40302060a0e030403062f1213020604051c0b010b09060d0f09152703080a0b010905060d020d0c0206010b0d0207080d2a0e0d060b030f0a1506120201080c 67
    0x42c3d1204203c0040040d000703000b640344145442600c403003c11589149100c0030650007082c2a040340c070030040440c51f00c1840c0941900b1074078000d01d066038482c0f03510205070680303c0c0b5000355078420300140c03090180003104501543d16034421031422107a66038540b61103100e401150304449d4060414400c451114049078040360300d1494602c40031801000d070351114035241d1405207403032450350344a19400028142600d041010b0440c0742203414094001902e0081c2074460181281911984918901c01d140e131142c020500039000060815548501c0c00450714000e501048002092504105200d203d40c1c0c004100c0c0c0c0d040342d4102480502d0b00344002640c000a5000c0102100e2505003030100d108840054410180b40c0c080c00341080d0ba42c100d112489104120320464100c003000306005200741103032244401044800ea00000206210400c80c0000703003000c1070243c0901d284c1c402e0105680501443c9041c90010007032140041010903203641c11160940c10105029011868220100c1d03240b1104200030302 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 576197886 1250 576196636 576196661
    0x21e030a140c0c12090105090f04060b2208060405070b0d0f020406050c19031e050c03031303090e010305030f03180a080409240611030c030a0804030f08040302060a 72
    0x2410301c1402034a01440c0009a07610070301c010300400d03040751058040080c055009200300c1043d0521072a100020505e06c10706495a02600b18031002ea281030301c6035089240503003d0503120310b80f209201b0a540c0d801c602051070f50700000e0303401d000c0000c80d19408900107005581100c0074060031814401030b030f1610b03406150002d140b107076940140c241c01c485600c0a0f001408040e41c2d172a035189040121035150440a804044040c2d81c940166800280c00c2680c00424000e002c0c01c040301003001420a9546000741c4032030701c0c03907404000100100d041d40e5660003502c030762003a01c510181544400000f00484400d0000805c00d61007045044015541400070b15840100d0704180d00a2039000040c1c1401d04a40c0d10048441240100c6e082c07101e003245000c1e10511210850a400c480d0200c00418280c0020700c0c400c0909003d21348900e1041c0960a10880d001604000c04403070b913540d8103201c01458040d00700d80940000d808072900424180c401c10030a80110342690040c0a00c3d140c032108040104031071241d90 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 576199136 1250 576197886 576197891
    0x100f021905180d21110a0803060a0e070e011808070f15020d050d0203060d0f060f0f11090f06040b03040c030204050a090f02211002121807060f03090209010b180103021e030a 76
    0x2c01c1d21720410099200e207203d580000e4403410f00b84207215041003107402280e02e00c1000c0c0e0401466550184069210501c2440c0c00340300011050200d4412000d02d400405044c001d5103c0814410072800c03031101120451012070708121442c0c44102d885643d00e9602c0b00000d5030030072519558000c550065500590010429100400581d07500d031900c001c412001c1312881d40f680300c004e662400c2c62040b00010403010406204170f90f904007014003070384101c103a0703244103903d5108104007a484110954014043d0006413a0b540d0400d410903000e03540c030510049124a081c440000c14589081c003d222000d940310320524030300c030000e81c00c2061241904411040308070441039562440ea40030816244828440d840050361500311030b00540b01540014014810340040004041140e81e00142107021500c03640742c901d100388070401c03081b030107040900c4010f03500480e103200109480c070081d00104014030854584c1061103012800550581c020540600420084911000781070181c0c0c800841d888640030303000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 576200386 1250 576199136 576199157
    0x1403030405130e0f06011401140409051305281101030b220b0307060906050c03130609180506030d050d180c050a06030e100f021905180d21 61
    0x2c5406020740d00112440329445480507101c0c00c506018400c2c400e92034070054002d542c10a039a02c41a440488071040c100180e003440c20b0035049094080d9400350031000c07804d0000d0b00b0302a641d01e202c401c84c1042501c3c2c07400380072400c1c143c402e0708500410442101d24155129100c05895140c807000207078180a040c19110b50540d1710a6480b0322961841d0054200070001d00003031013181e0001c980306208002d010b548080010300c4880c1e04281c07840212046072034260350782e01650320864194010f03c0c000c00030f41e0303040100210f081e581005414068a0155084032051992400003004be140291100e9816401c0442441c3c1014411070041245000001c0c0224441160706031116419810790000c0c0e0711000d00502c141f000d850030408000c000d14492605102c510106804c42c0d80396001c0d0449110815504c4001211448203a01074602d6480c01c80c1100000041068000e0016448101c29000707044c410002c420b40c43c9404040340300ea0940086d21800c0020951700a241107803c04044401444200240d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 576201636 1250 576200386 576200389
    0xa140d050114010f050a0b16051509070e090d0c0209090a0b01120b090a150c1b051b0105040b0d050406020408060907060f03052208040906080a02281403030405 70
    0x10701005400d501e00040700c0b07985081c0e85901305903007a0b00303ea4445d24410508115107010142550440c9a58840361035039440c1d01d01d0454174143d91000500c4020b40180b0401c0352260022559200301d0311403914482042d80c03072031900c40c1c4030400c84000b070000c88d8085d24000c0240c103003070003070f164400b18003005c4403202c1203c2d4507603406105090b445403c510040304020342c100901d82e0a00c5411030304030402482800c401e42d541c1d04501d10120402040c2c5543d1f14a4402400e10900d50081c0a240c102c071800080051420180d4030351030b048407002c408080740c1c511040319500c05d204980443c1c3c00682c2050918140b001c0040c003908010f0016103407980c09000214000c1e500780005401808940300500c41d20f460600c0c09840d91040952840605240c9010005c64800c0312450410b03c000e801e80101d011800c92410801c10300440d080000ca0600c1d001c40425170100010340203400f00e00854004c149500220b501003480700c0d1000c07003880c1140b02c40701c007007110404c00020091394800040a507810940c4410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 576202886 1250 576201636 576201641
    0xa0e01020d020d0b0901030f0b0402010e04020c0f0115060c14010b1002030406081b0403080702010c0b0a0b120109050c0607170720030703020f0f0102010207170c07090501050a140d0501 81
    0x1c148400066002031154a0104144540107510301c1c169080c001d41e40c91358132143e805104001e03028000429060015003168850301c00384c51081e0b0010011500d0744000d49000d541d801104054403903541c030b072007003650010701c0c0030070000101c0b00550307a0440b015560b03035074a80070321504c280d980500e0340d05c4422000c070980c1c4c0c040b850500000d80b0303402141c449281c581c00408600300504601ca100d04220281101c0c803168904680a581e0080c0800303503200400d1004994074103c4c0030000d040300c1c0c94202404000b504680010b45220012150780500016491400b0308131250f440c0014102d9005803040c07096424400c0190605d079004610390b5000c0101c00170001840c1d408035000b02c33001e4401520064000c424002d41c00d221201c1500101200b508640c04981c2c0741c10b000b41001e102e403141920110583e8400d40481b4249503101e8000d1101c0f15140c1344061042d00422895501030094000204e141c200381c1c4240c80c102d406c001d0081d141c03540752000c1780e80c0310b00052501070b4000320030b8482040480c0c7c090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 576204136 1250 576202886 576202897
    0x6030c0f18040f120f0905010c0510110a0e010e03060610020a0b09160605090f130603170a0807170708040309080313061b080904020c010603051c030501050a030f0b0a0e0102 76
    0x20b221000040c0c0c1c640c0b030800700c0340268100030713024803207188607102032031381c2c4200316a059a03001c0c00c00095041e01401d02c0c51510b86900d50200006081002c81000c252064001d400340c03e0b43c03a01d40d400003420640064410141c0828019055407240000940c1440c24a082d0340c0180070b1401914004040da0312803902d0120100c400803c2076000c0a0102d8480c02c0c0c0342203800040c5500e182081c1030905400000c1c80d18001c0320229032143e060803095a100c0c01050340150b0045601002244800f4100e5100c980560400144103002c24001800103c0c0f01d40290413000c0804000109510303680c0d00c030202550005005007082c4c00b04841c003000420150700c1000104001071242400c0084940b41071002004000c4030105010550001706d20b01d00015074610645100b000122400350f03e80724120b440da40102090f920113486803041b0040c1d030281c14666400f88201e58030a07030b018070880c1e0b00d48043c45100d00c414031008008001035409980461003074550039030880701180005c40d412098100300c50a98100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 576205386 1250 576204136 576204143
    0x7060b0607120e010807090e0f091606180501030605060301030303020703050f071113151202040e0321160806040c0903060e0d12110405060f04050a1202041406030c0f1804 75
    0x110b03d0b081000d9a00010300650052852400031000744c2884600d001c0c40342c025203950401056100402c040e04002e21043c5e21001c40d50107224800c03941c95100500d00e0340d00038500680b4001e166804212540700340903c0f07040ea00046c1c10b603132450b440e40c0d80442c0294801c01c019420450140050000c01c1710170801040c030140583c03000e40b2525038a500308000355003a452206d481500d000c01e50725042c0010091349080310b0030600094000901d0307002080203811004010700440c000000c8213104210154040d8154440554244c00c07565140c0c1c15210700c280d80108070001098020300022181c1c64142c00981c0c0c1507000f413403d081016601d60314001074842040340107240b5045001c2208405500c000e20b5100c1c02a0f000c02801205540301d01e80000348194050702d4041c007000104c89100c00b2074032044400809010f400b0580f0b15594880380b00d88003d800344102d00c950708001c1c480300c1c0400c550040900a610040281076003071100000c020005608644007500301da06420005001c3d022002a035109070700 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 576206636 1250 576205386 576205397
    0xb130c1a0d1a0f090405100b01020f07030515130b27010e060a0e061b030c0c0f0607030605041514030c09160f091a07061404030c021e010507060b060712 67
    0x408010412160030f0360b483e480c040c0581c4001c2202241000699954158011000048061642c00101d0901d0125082c01c00320348102032000041080000d640300114a103103d103604152901032281038550304c192800382c20301040740c0108190381100d1900031014000590784c00d00c0300132040d24807400e4400710702c0400c102c0d421040030005145814061290b1926548003c0d000780d1501c0855036103054000705041508030b00110004010760144070880b074500d6000d904940b00000203816880c2e0300c600403220740c80004d06284000aa0b8109400f401286160705000220801d0904401c1d0455105040c802a0300d0f1150075860085911200141030107003146408442c0303184400c0b04040d00055184130074404100c4404c4007000305042c401040b40352211800307030141d0f40e540c1da0709100001d8125102c8404442d85800280400c050f00003102e200458400d0b0b9601d2051842e104a1142c81d540214103a40852001c01100e400103040d0750044201c050001e02180c00c1803000d456a100140000c1c4203c00842e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 576207886 1250 576206636 576206681
    0x5070318050a0b0601170a020a0c0b04050d090e07050306010f020106091104031a0106080a0b010207170c09010801020309102720042304141006030b130c1a0d 69
    0x7010000f800e911035000c2c00e1802da2141c2c641c0c4100baa10000500075003104d5030118492410611a10f8100400e60f00525490454202030070310b5030b26881d80580130004916401000902c41c410ba000075441a0081d0311100e081da92010010b4450385800c0e80c2103400c6550300c240228800c030452080040c2034421280b290385135402c40c07510b1500c04111440398661014200c0c01002055800100154020442e83c4081040414000181e140c2025a0861088208049103100c0d03018400100040e00141c119882c03403090b42d03a164402d080341700950303103c1240d4111810030710a80300642c12107000d9074290b004190a403c001a503d654000c2c9400080b140070001012100d031810b4240610b007080c90085804001c1d2002c0c0c203200c500e03a0880d4810042d1100e0320200020140804a0110841210b01005803060a039407541d01c0002032209002c126680e241c8440421042d035000b6141e12a40c6a12600b60110b0754144402c0f44024603055220b02c42c0c40c90104412154030301140a410303044d4030102c10101d40e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 576209136 1250 576207886 576207893
    0xb0a120f3903170d0608060703140609060f06070510060b0c071406031810060b03060a060c1101111612021e0109090c120212150303070803070305070318050a 69
    0x851151059811014410014030106000b01c6003c3c1c6804a14a81c00c1c0c0e0b80c400c1ea131981400f8000b140c0c86800b690090b0710412240e56007580000c602c0302c987d40180a9141d4074030007005043c0c00d0640e003440d0003482c1a110314469041050003002000c0c02641119000e64201050b507040e0365090f04220032540700400c050b06507075010440d0034083c14000d20007488001096000c514980801010100360078081901c066400c401440102c051104a00040c03140507110302e03400b002ca60003550100d004050040c0700003101407080c0344010065a000c62040c07207180705000110740741021080141d060b0701813075505031003206001d00f03d00020b0014543c00c0086181da80100504d0800c410068800b111a050802100d40ea201541c80c0958065040002e01c024809100b240e0150b41d2001c1c0c4107199200054001e0b441d107050f00c0b61446007801040110161424070145502e07800b807030600501005040c8045141d0074001d40201c1c1d800460740c680015400c039001c1242c010603562180035600303500316148540c1031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 576210386 1250 576209136 576209213
    0xc0e03100606230a0e180a090212010204030809040e030408150f250f02030915070c080307030f0c050a020a0909050706051e0705070302040e0f100b0a120f 68
    0x1049115050200395240c465580d030f030144a000304110800001c06520401036884105041c51804c0100ca450298900403074454024070491009a01c2010f1900c1c0001d884c0105008031415640c0c02007000707042c100c1c0320080c48054050b091084c412408140004101d900041003001584100c0013114809070130301c6072003c3c0ba5400c001c1d0406a000701041400407010b004012100c032030801c146072545113007010f080c08070b017103000e421400c80c0d000c03a135121288400d1904402802080e4011a00c24a0700c95031640b03015504d00c03d0000040108004900520180e4042d950070b51110b409a0191410105a54001120101903030080d00b8025541d070880f46c14030508100311400b81105007040d601d015480d00c880721942030f92001000c0c0c003d000044800800a06221200c01964040c10a1040c0c1c1281c0c60390644588107441c410185100740c9003901d0030f0b4041801010404c036805403100003607034200b802c1c2d8a14101003000c20343e00241410a8840052481c0048160b451080700301c0c5032441c2000c4019614 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 576211636 1250 576210386 576210407
    0xf14030f04060f030c270e090a0507090608060402011407060219110703150903020c030313060206090105072003120a051e011a0306150f070605280c0e03100606 70
    0x80505c1c3c0b46110050f82d4019403508480166042d034209a00150307103116208500c01c0d00030402e400200800d100300c50500082110001c0d11a00070383d16a2a00ca802110480d80d00f48204407c0d035101c1c401040141d4040d06901e091240c01d590410716040c00d075159082668850b1070ba4030701c2e002d803107001100050340c40021440d070403950801034030800303281d62101000340c000600030841c125a07601195081500801c130050b2909000340a03a6220242d00c8405c1c61031100a110f1440136003c2d070000503002c814103101d01445159591145601d40050542124000c1c0804e11600000d100c01c0010011a200c140d00d603030302c1401071078000325803454001c805401c1c0301004100d03060b610800344011710441104030b50354003c0d80100004207840380c2c1e4080025102d1012805900e0a1140c0040ca0200c2c4a442100520f0b11501401050109403602d0f0710020f1481040703841c1510100501002d01041006030300301200ca210945000d005442410713001234205404a00070ba8075083c0e40700e00070000b49070008000103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 576212886 1250 576211636 576211667
    0x903070201260106032c03030603010e0f0a030f050708070b010f05030106030308150409080c0102070515011d0c091305190e0a120903080c01021e160f14030f0406 71
    0x164181480120b0081040042c000e0400340f6072a01038003100100100002404907481d0f101400843c0d1100f811207450750f1003078030041c2c025401d10ad80e00e107070b8004c005045103030050314100602c14940350303480403103444081102110030024100408004610510040d140b00307070140040b26500e501d045200a043c80040c1c0c131041c007a905160040011035000040340f91b21591515580d030040d00e28000240040c504060700030050000800d82d0007884005501901d070483c0300f6000c5414282d038003085e1540c115002d105448180194061040000300c900c89642e4001c8000255141040e40c041300044100c03d4081d0501031a903a07820412002c00c003958900700a04000020070007000c0001d51a864a89041c42005070401c0403541c0d0312403103140f00e0b00d03000c002181c1000c8043e85552403158454080d520002c0805c084070841603602d0000102e001c21590501d2080c0ca400c1084006681ca05001d2201c0510554210f2128662421041303003d100401e05540e20100503540d0b181403440241469220b2111003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 576214136 1250 576212886 576212927
    0x406060905060703030902033d14011211040501090906050c16080304080f130302100f2111041203080a0501050a090b0607121d040e0c060309070e0903070201 69
    0x400c03950300e4071811030740b111390107190201e00c00c00300740086841d00a040c0040d03484000d01ca2540c4410400400b00ea80c010050346000c400d09071b4005007404203a400907401c540c40300b6030301c1004100301142800b0b461247c82c81212011860781c0e52500240440c1d000f64040358009844880850800200c0c0c030075254420701c5484002c3c1040d24040309903c2d82c01c1003031402005031f540003022030b003445401001e0328105c02c80001b0700f50f82c501d9412030710000d00a143c84200d004480d001803c880c164014198120619000e0360781854a01d001e400c58100c100d102240b07100038550719101001080e81030b00082003d01504040c0c00c0d800e03007040c580100204801000300340f0503490800140300c95529100c40c0411100c821402040c400b02d1000011654031a03450020060401c803032a00465541090341202814003180606c22041040d009000a56401a640050300d400200205407149030100107190441d10341000ca90040c1d4039002e100002450903941c5810b07503071003c00c46030115070703003c09103525124401d81031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 576215386 1250 576214136 576214139
    0x109050d12050f01260a080d061d0609073c1d13060504140a1a031e1c0203040810020703050307030906110f030f0a090b07050a09150e04060609 63
    0x1081c415203018000c44021074a54440c0ca002010064205d41c000c03800c5d0403d0710159440c0340780440c190340c0208120055a410038200181d0141240410407501c80f140c8803402003540d64008209034100e00400d0001841a10381c0c132103401c2c0507001c0200111404000050724840d00400624294607206c0882400f0044108150b002c00780303030300390b000445003000e680c40442d141003800b004016140580110f50000d1424080302c07041d4600045160141c41030800400516520ba08600000c0001c0e00e100b40d0140d0003c00c028240741c0c420301c246603c0c020b1980a079482c1946602c1c54074200006c2141090059002190500c40c100060126000e0300c08204811490300740c2596001c0c102d03000042c100c01c1815500c0790b460041c400e498002d0b1042d841000000c0307980702c40200040085400070f5401c1d94540c200080020580c01c651300c203907070080382c000440c4c14442e41e42005c120b0726640000c1c0c07240f081100031407001030b8050300c2c0c0703011050350001c5848604541142030140400c9a4180e44050200840402c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 576216636 1250 576215386 576215401
    0x6030706050d0203070e09091507080c09090c1207271211030703060e0f151005100c0c06110c19060c0206040503160609090c02060106050306120109050d1205 69
    0x4035841c20b07110740005612661484400d6503885907009a03980c2000c0100c0401090301070114070404518110103190043d6200c50404541080e0102c4403084035807130801c1616510b1404800d090b901020011450745031080d42da880320000d0406440c0390f404240c0710340c03000244e03c3d403540e0700356801265461400400d5140c400e0400c40100c00d80005031034008014526030f441c2e1800e12160303014642110f0148000321010701801d698991030b9503100014010307042078000e080030494045000740802d00003010325a0800f410484980c40784111030081c0040b01c21410300141c25100342c4d000900b040d40390928101c025645042c204000454070b903110303c48511107440480c02c41c80700300301503078207600d0201c41c010094400b1804a202d15007002e0b03070522915003203a803640301d041400c81c15900381d0b035030f03011580742e8440c8000d081c1c824014040016801c00b00050040034850b501a541c040d000811a554800d40b14031402d00b16120321a06883ca44c024034070001d80c5a4014005460103031104104000601e091034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 576217886 1250 576216636 576216647
    0x90f0f0c061110020c0109020a030302100b0102160b0903070e01091d15040b1509041b050303130501030903050918010510050a0206190914030414060405090a2c0c040506030706 77
    0x1103c400001d40c04640544c184600b540010441c0da4050202d00072940c9071300303020350b841d036441425450543c07c104500712654408642420080648a040c51a2504001107176603540c200000780c5804d88100840020900301204c030309402040c2c413031000110001c1242000300b9541c1031241c034000540c0216200403400c009611010b070f2040e0401500080343c3c03034050144010208911030950b0201c80320040c04140710394007044100040407041540f241c660303100103254070f9004201d0755611842c2d00410811565000c1e07001000b840c1e1080c50300b18075203008140002d8100b0480207a60010320311000050002d4208000c109120050340e09025080815020b002956210000d00103042046510b03140c6980d4141078005440792030b403141c41d103031290010f0554076650350480d116070002d814000c12100c0d43d03800c044048805035900682100019030340c501d00000a4280803480c00020100d451110b180350b00d1040388203040088150113402d0b640080c10400003640c40c0500704a00c2a000848100b01c1c458110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 576219136 1250 576217886 576217903
    0xb0f07020f040f0c0513080f061923041703161d0a1e0b04060f0e0a080f01020403060f02030c091507020913230601050d0501090f0f0c0611 61
    0x4550030005601400041006050002461083c0300d08060351440f416420202410140408103600345c1300c10303550400e06540d0030007000180c00d40e030050301c0441c01e2500300c4240d0000c05019007201161340502d4405003110703e0800d512000119042105000400c54801002484541c01025181c1141000110510303000b903218000018004031411041032564008101624080c1c004c00e644441d90361008180c0c01c04241010b40340c1c041481c0d101c0447d0070b020400036142601c1c07980d620411303180303d90b075415507100c800e09944640c001e050003000540300b0020407190008600c20301c00580c4a0349107240080c00e42d501122002c82c5940103100700001c005200080c0e403202042119800042d0290580f00466403103002406500070305040200b20201c0301004044054030320a030502c00c04d200c0903000b400f610301940080b480e12900036400400c1189084029040c4190140300001090803003031b620b20f400f843c030410040790401444071801090084c0b10312030800815040c1440340c2500784003000d10382c503800603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 576220386 1250 576219136 576219139
    0x3030f0509010201060f03051c0206070504210615150c02060307050319090308072a020f0a080615030705120a031206090c030b0901090b0d0204020703170106050408070b0f0702 77
    0x301d18040c20760300c00d412041c01024016480c2122a840b070402c6900d0b4007c003042d1003211034802c80b0076600644001085032148070030f81d171028201410b0034004a403402075010542e10200e2400d0318032022501074401c44140d8031500c21707a0750165203070145c0380107c1400c03100c80000b4030131810564405031b1100320449620401c9840c00b980d407507850946a800c0d92850748510007039189407031405403c060b00961014040c1c06a40c862800c0e111030151400204145103245002c044d25010701c000044c14070f03e81d01000078070014480e1003002c2d101c10b581c0e0714103002100e85150000d000f6414010500341400100082d0000342d0308260210030016115603211214407000b42004031410040400500304c0e0700100103800040c0050001001c903903001006048030200ca5032140100c0000018604002c0c881c031149090301519481d60b41c0b0090302040001e4018601c1581445082000681004603042400303010b05500d4480c2505c940c00c0002c081c1ca4481650004480d85100304500c0f085240c0200641300425130 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 576221636 1250 576220386 576220397
    0x824070c030c150e0f0d02150103081204050c030d211b080901090c030f0308010503030307021f090c060f08010801050105220b090123090138070803071803030f 70
    0x15110280c5004013282d0220540368012021000b50042e4045618035484003603500300d6a802d01895101401c0410a00c0010103001c3c080290a885031540c1c103207190701501031019200c036190084042420302c45403980103000152840021940320400e01019044401105d808000d5801440b91900d403205100e10101c0c00e0018100000d5a00038094001d00c0c07249078807019403c0b00980d44c0c070b494804552a610304402065441c0000f169504001003070383c0c414262580148040300e45642c092400b0785010a260b042c5645461102d00031400c64100640105285d6807504408995030340014100f00040e000a07a8036410903004104076607034402c4c07140c080e40944000103605034129102400030320304405000d800611320400080d1003c0b14040c0c00400000f40510400890910001c0002d0300200340240502500141c540e414003a103034010901c801c0b0703035020074501c10540e140700d07040c15034100220803243d03144000100314403254844e0558203c15001510070a145081d654083c0c0f1950307040350800104423 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 576222886 1250 576221636 576221663
    0x90907081003021807110c011e0e040905030702011101092117010e19020903070b1317100f09021f09240318030806190824070c030c 58
    0x20180507550006660040400c02c5880f0f040c2d00c01d12a100c421542540401d0ba00c004119080901045110f11460146d603040e403051884c8103060390f142c60105100342008100701c18020240c44501c20785a08070f0040000316158841403000512200c7c84120442c0182d0500b0700440014003803140c2843c4080b001c0710026a03189121004076451044010360b04014101d10000064400350b01300c0c0c03203002e1411018120b0719000c48404100a0b0300c540308010741c040d8404c1600300002030951024114140b80d103042141843c0d034480320040c15a16004801059030402d07442c015203484e8502c05c0c2060720140320428000303c00d064000820080c007104a0080001c8098510320005103c3c001c2c0801404c140541100305145919407840c2c034603441c203d1403001c0ba141110242245112a240c0708440d80c3c19a903111030b40c2d544805000c40e1009980d02c2c80c0103c001d078500070400000030300c5511017100015800301c00b5280d100d06844011031024040d08180034140d880a4040b0f503000d1505140f05400404500465 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 576224136 1250 576222886 576222901
    0x5070e07050909070e0108060a26031c05070e090f04022b050309130608060703020c0c04020703120515060906031f030c030c050306011d040f14010212010b09090708 72
    0x140304500085a010001c03d0410101940103205020300799401e9179605d007141d40d48801e0112241d103600a00f00707400b403401c07051581212103401d00203010905605990800c10b00315540f4850f440d8101d450700c03541e9110301c1003021041c1c0c0641803014240d01203401082a0525046480284c44080c101034000c00c3d41c503c4504c88000c500781d19106909405e2089101e964a40c10b00ea62a0b0b00040c080c1440b500144840403c1200c00f0301602c070070354807004040e00740c54031549010340003580080e00f0304100b400b4003200f00c01d0179611031002c0c0c20450301a4442001080c0c0f803c1c86031040f180000c00c04401408040031a81d420b0b180c2006540703500c50190744096403512008140b5181c2d08142499103a0040c044202008001c0029102c1044a10405000d04600c0c2c0b103004140e1140c00c240a50003041d50424034060010580302c2e03c664100b0f000e036500010300055919038060f006107103504508540c0d000034001c40214004c00300310740100455040141070250100001d120310344080e0052040103940004205072 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 576225386 1250 576224136 576224147
    0x3060b040b0907020109050f03030106210e12040501030b090103080307050d060302090405010b091b0304060c030e070807052416030203160b16020604030c120306080f06010905100305070e07 83
    0xa401460981d00f4a04404000d02030030312542c080743c1740d02502c103241005580010a4a05807411500c2c0c880710300c1d0b540318802001a202c422040038035500d030307020131486400510502d81d5040c00600b40740e03600c905000014041da0f20f2042228000c0a2038001000071441c4001a0ba0304451a4036103a0b03950703091450f08102904207070300044d50058440c000d10003040415800001c06e407a00391180e0805a4503800e0020f919032040c03d610200300e108100003000608a50311842e0052200d080c0014100c100c012030615080f081d40040e15281e106900c240040d107041001281030300d03005d5400d480301c0c3e40d03c0d103400b0105e0300405e190074a401802d5120300d41094000d0099408415000c05d003070000344040d0901c0c0c6140c140a9425081107a1a0346070040c41910103e0702c0c6104d81d030540c4821100d80c400d6560f07000004000900f403010150f03134a07001315170000d003401000d4441c1040001040b455050a170f1441c01c80e90042c0c01d155a4514000003000081c0000c241181241c4610341a8000c9565a210030341700e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 576226636 1250 576225386 576225401
    0x91512051305191e0c14011704110103200412020409082b0b010c15110f04080f0c01170a2c060c1c050402060c030c030325080103060b04 60
    0x14010080310310450b583c004002c10f2001e0003120001d5543d03c510000210020f51080090820f50b4105170a020710590b0420401d0320100c10701d096402449014924400c4c0380086d9801c0395602c549844030840340da4036014a80f0603009024158183d00a0412121054480c0b0710400f40c00400303480784401955516400358a0040d08908450340e100384a0a190316840d0120031b804200038482106414030a006100d546600c0c0d070103131180c680409080d2206035a180b400c1180a5210352200031980707501c41110040e242c0360588407071a60701d032424400d5144c20280408070f401081d40c0b2480b0426016079004c540c5403080d64011441c1e142c00c2e1520202403018240c0350b2880b4220500d070b80d5801801101c030070415026020401c0950b00d0545428101c454940f0a89007441344040d9042c03c1c00aa82e021507001d20741080c40200301c80d203048541d5000a065030010394860100307800110400542d440303c850302c40800b0251030014000c1c1040702001030404d40040c003010b4002c680e10007142aa41d100e40c2e11154 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 576227886 1250 576226636 576226643
    0x5160f0e01120e1207050f0303010f030308041401111305090606040302060307020c100915080103030504050f0112110c0f0f03030a0218130204050a0501050702030a0b1b04030f030915120513 83
    0x82110000380001541940500d00840e09803084c85140d2100b01c030040189e03070607900224861030903503203952011a0f103540003030000d071800d084502c0420300780d541c01d02c00c7c507a0032400c000c29180c9688030040b41c1c0c00b642c0d02650289005650340307000c121940d5684012542640c2d4115141a226141c84104a141c140810401900002001c003020000c075000401482250410001c5500400d00300b40111840d000c03e00c03009000c04e80600051185181403051048150010b1400c0180e2443d1788003d03505a4001100c1c06424a50000302c6207807040f400e0084803d411184c030b000300410203845840903076030302c0011f102e80e40d41d903070110301c41d0100c1004041c07010300f46000a0424102d5040c00110900030352080c80303014407400b468000003400c0e500a009840301240c0060292100c803009845010324900d0040c40c0407548450b0140b04912958a80041c03c051806050500b0110360107140141503101e9581004e1035200ca000d0310035100c3c5500613248032800400c40b40208546d140c861408060445410009 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 576229136 1250 576227886 576227893
    0x2703091f020f0f030417010e06010911090a1206050c030408180f060a020601080c03010b0d060203040201090e041a070302160f0c08030703170a090203071a130905160f0e01120e 77
    0x50340303c0b450010290050720700d00d6450003040004900304078200c41c1120310b00d8070580c000c80010000048075500c120807042c15814128540840d2200144460301c45030400681640100c228a0a000507403080c00d070b1081c044400c2c28518205500d424000d4040c25803d80c560006000c0030281c10740b181d000060f030300107000e44204c0c1c40f0042810302944035242401000010b101e00983c3c11454601401038903840e003005461701c58400c000b5140c0401070f61004101341d0511969040000e2203a881c408110721540c042c1c5e016200b00101380c01c0100049402070901c00415006101075010711041030820916654040302d540c0e600e40032880c181080000580c040c003c280808500c3e002855040001040c0a071400104900749648040d829402c4401c00000650154440c0c04140260032240e9542c003a011185410340d418149484a003000a41076074005040c0d0688400c1840303181c0c407566016441d460607508103440300301c1034440d00424444458100b1410096803000c2c4030840c08180d40495861490001070307 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 576230386 1250 576229136 576229153
    0x1b0b0403061a041a0d06020919030b07180504020304030201060e18070f03050706210603031e030902060904110702030a0c06090605040e070305040510052703091f020f 73
    0x8503000b804070b101041c200c501186051035240c60306205011070284440c0c11060702d0742c55032080c010080c3c02c41e070084421a508004c403000350b94038900c1d0855000a003001c080c5049055203840444c0100260040040c405450507803095403102c1c50121060307a509440050312556603041c12409422580d100c501c40d4103c400c1884006405014211240c0d8203400c201c0300c12039a2070f2840c1054010310300c406042a04041004d1184900c109546001ca02c840100d28803255484400e1404072500d5070f004501091800d0046107940c2080d807a04c803a00d15260508018001031900480c429105000100e4030640d079561905031701c1c891240544000d44d402078110354542c1501d28048440b11158007480c0c000c50b001e01c0c40000d04034800c1048034195180b02040300c40c3c0d61181d2074107401801c0c000e0400c42e07040c0160078090400003d03034072900b446401c00b080e100d1b400000c1e03441c40284480c40c880740d102030760700200f2510185855082c1090300f030b0024290840c1881440303e00c100c1c140a68101b00c00243e0103440036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 576231636 1250 576230386 576230393
    0xc0f020a0e16080c0d0209240a1b2102011d07030b0c072f04020a0305061504060219030e0d0305090906010309231015090b0604050d1b0b0403 62
    0x11402e20900704120000118911401e09a81c070000480b4220000401040b08003d984920f03000791590300c80140000703500d103400c2c9490300300308043c0014801d0704801c042020074000d644013500e10500094400c0b12202c251164a51203c90450b9203141d00090b601c000e00304440610075400800e001d9020311111850000e140000e94580d44240702c151014010100840c481891400031240540d901070034416204605216800e0710b0384180b5080000225140c00d100260386540c001803400b0021030b9400580c9140603000c110341003440c0f035291554040284400e1144680000d266007002c90059000441a000f514045416030500e03040c09400038a050f49070000c058210b030140c80d100408881d10702c0c0303aa076018011422203501510241541c08800312100744190081411445840900c05880109584450070004ea40d454202c102c61450401d0b810084154035102d13440b41e1000441e000792615140200149d01d2402414016040003005144c1c000000d00c6084080001c1680c40c071160f45544e81c81c00d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 576232886 1250 576231636 576231659
    0x1c0c0b04031b06020106180b0307031e06060e07050d0e07261002030c03040b0702101802030c0306091507091e05040e06010e180c0306010806040507081c0c0f020a 71
    0x1c0d0141c0d03000181c0d90b000c101c140c01070040a00341c0b40000c0c400301040d80780440d80000303041c080303801c5905400b81620202c042000800e044409078000f5065001c564203d242010440e01c2c107034007941444110909102500c0c0d03010044400d44003c640c00411014001400c8506100340c6500c00440d0034168002032141c440034041008903007410310706583c50103400f09503c0059200885500e44002400c10000b8000748003184c2c020740001940c03046903410030703015200508841240c015140e040051900b11021494100040191804240c01401e184e08203000d038941e54803042c020360460400c00000050702103100d440c6103001000d43c40880071080030f190204000d490124003d040c000c5040c07805030409104001080c80c125405008110b050350303030b0090301403202c40c0059a502c100b40103000303505440ba83e0070440c0e1400790104c84040e10030390401e450320798a0301010368040e100300c0d001201414a2403890b00d428441155030341c11f2880080c2c00350f01d48410b8200744503000a5007e2980d0001003515031190 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 576234136 1250 576232886 576232913
    0xd260a15091b1209061a031e0705041d070b090f01030b0f040b06071506060807020601030f320a030216030b06130b030601090203071206051c0c0b0403 66
    0x1480c42085854101901c103841440d03098020040d030b1800400300c1184512651444a10700d44000038018805036a03200c01d82c0e181d2444141a4021503050186504e070600c038a070041140c0c6c205090585000704003162711007000b03100e03040c4516a599070a0b03903130407100304034012000070510a0b0747c4101d40740c51003031601d40c00c42240309001e0411136001e4003031540070b4403d6401d0120001e065000840c01c2004020240c20790043c0140c00c52000e02c0070300001100d00400c00f03080f040c880d5000c5459414581c0042114600070107440855001c2401000410664070b4825888c80c0c0080030700440c1061b84280941241c00e207020038680000880000214034004540540f07004d21907801e4a500803030207101102201904d000142c0407200e01004505035141c951410510f4071118100842c1d200032400c002401c0032402d07800a0b2441f0b40000810107650383c000ca64800d1020940c0782000030508140106802424040784178919220400d941c005005551680d00c0c0184501c0155a5540352240392103050400301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 576235386 1250 576234136 576234161
    0xb0c190f03022107140102210906070905060403060f0216120206400602070c0e01050a0e010902031005150a03110c06240301090b04050f010b01020d260a 67
    0x1002250301c52221142d08803030080f40c81c002c0d900d0505080d52104000d1000001401490750760030081c004401c0c882c821005c19032090100c3d40441817134159021410054018440b40820902031828001c0765079220564040e81c0e004074000466041d540c02140085c070030301e4005c0e541c50300b1001c0c10000b0003404140000c8101d100d0380c00d48001e5169103a6042d03024010003841c1d84411035101012960613004044521070071034403528540c01c00100c0d12080c04a034400502a0342c0b0512251080c40281d0404444500505040d121204000d00e0545035a8401c0300602a050701c8030340010101e40c600c04078080c034130302400d0300415118946800614118241d48034038007a4012a0a00009000740d0b04a002079805000215000d0300d065911421800c60088440c48a64416806260a1989600c0901c1180780d841d02c518113100c503034101420b0103890040a00c1071010140c0c1090707080031039a680483e1001c0c01500905240c0000762003008125408000000301c0e0144001500401c50502ca45400182c0305540 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 576236636 1250 576235386 576235393
    0x30a05090d0807081810060608070f0203041202090402040f060b190903020f10120c0206150627040204080303130606080f0309010f0306120507050a140a0b0c190f0302 73
    0x96000040c2c2da903039000c9a40101051000000540c004044c11078070480c084c82100ba18610b41c01503034104110751a540114002a03203010802c62529002030040092400b140011030819207000c80d001e20384080d800000b402980c01c040820210345598202400e50926040c0a201c015100c0c01a840c881e040409007101e007416442003022058083c444040580380c02800e00050b01c4600d4003071004800000020f60100308001c28030b10488070315031103008044003c0e54080d00b1241400c02c80c905215070341006c818440d02081050416640c0c120740003c3c080e15107041c2041980f88a200058001c5c040d6520411171804000b081200c8070700b440b42c0c0c240090348200410050b445c0c60b5400a6170b1003104440040702d541c400c002030f030555805500070b0b075052130340e910b40410f0075610f40c0482c1030f68003c0355504075119800440c0c14013403480c0c020300c0e09010304034041050714161032042c000b0785c08245c10300c07039000c3c0001b00248808542c1410b022044034003030480bd0b00308160b8424903101d100030300d400d50103800501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 576237886 1250 576236636 576236653
    0x41521050603060a1401050904050a02090a09031e050a1101020d0c0c0212010603020a12021c050327060403060902060f0301030803011d01120305030a0b090115030b060702031203040303020f030a0509 87
    0x794a445006845c3c1d40c4005200542e03801d05043c41040c0d03a000d0006d803030034450b00e02260b005940ea1134943c2d10945401d100802c0356042440c0107050410081407415191074542d04088000d40d2110589001e10418501000400c1801c02402e00a2041c613505280c91030074000000509601310059100c402d10070303070380c02410f181240d40c0302c4e080315070501000358441e1400d030081140c0440f01500302d481c140020090b1580c5c0f00300d00c43c10b0701600f00741b4070b045455400100303e010030301c05070801c3c0268140024071031080f590b1809000885612481c08000e245640d503a800c00255110711085c2e4140b411250046662940c40381000101d541091080700c00c4400104030a544000c1c048601174100c82c140c40d00450903200554041d603541e0401401401c83c29607402c0b19207595621041228000c1c03c40042d00c4140f010b40c00802010b50740192a0070340030308070810400b03005807000a0440309040e4103610345600c9448502c0d0440c040c1c80784401003075011b0b002000b448060f95460340118000c4101e03100702d51440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 576239136 1250 576237886 576237901
    0x31e39030a090512030f0412110a06080f0603010506010912080c03120610030216110f031e0c09040c0302010c170d02040501030609051b0a0c0602130303200304152105060306 76
    0x80c1b05039001c0002080302400700f0091000c0078510201441c1c41380391001d010480e08804a02c401c0d49641c404000100c1c0d280521582541040d2446d4100e0ac080e4004d101a00d4944000b8105d000c09128891a100c9808412420301180200f5038500c01040b5040e05e41d00c0d5034007552094008070a45215129120310b0089135040790203031084814414026011059602458492581d0b00048144050b0080c4d040420030440d540d0a1080744044070b031040d644074252a03080303440c624040d40070034103a004401820900000c21648111041200e074240390030b02c280b035250b2500d50150210b1040c3c050140c0c80125085034001204c0c0c01800035514281d130300f04221b6a8860710302d4151780d4196400012001039001440155002000400400003e07040107180b031041507403828101e9120280410104003900d105004155100a6014006c140036814002159103201007076140d100b03c0c421903100306c046010a81d4401d0180700c2d0000312840c8603100a901c449081042406050101e070018407178051100041c0e0036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 576240386 1250 576239136 576239143
    0x320106020a0506060d110603040506190213090e0f1506040f0506010815010306050303130e060108012709020901060203130501050a02030406110a14031e39030a090512 73
    0x8140d0080c00a20154803800217114088400400a440c4050310007042c1c10a42c44510095020350310580040c9242d1920340c40015214080d4525404641d004000c1d007401c0f000ea0241030025222206400112290700f02c6d00d8501d0040c4403448082d89019881c5044102c0d1240110309210760010b6070180b04081c2000310740c00845608070b503403e02056150003c21803607a0300c1c4a03100c00c248018140024aa5250f500103131035038014000040e80000ca00c0401d00264901d4503407150020800c1c00c22031010750500394581e01203500f5043e6060405081602c0814000c03c41d04882c00c00b40d00540440300c9075031a100000e4aa50042d94108110010740c1400216944101e040b40e2110135550b0207142098207003441210600381100c00041c0c54030829216001090b941d41012b80d8480d081c2c0015545e4546900407910407084940244c0302081c0144030801003201b9120b01c0c0303444030103a1441440503d02d2061110030035018101c807c000c4e44404103080344010742040400d015500300301c40864034002450081a80c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 576241636 1250 576240386 576240403
    0x70e09040c15090e01170c0d1115070b0408090301051806010603110c0f031b0d120e011b020c04141006031d0d020601051e03061932010602 61
    0x10001d840000300030301c2e4039030009840e05100914195a081e030351098144d1039030301c00b80c01281e0094401030204110010401617100300709004e0760baa4a81241c1a00c4146070200310078095400380d4480c1d8905114001301d00c044403030b8294090300e0140342e4240b50a025045030062180d1600075882d02012480011480403124603800d220300090469070b007086400c030301030a9000f02405032114140b00c01c1250a100780000040d041802004640710601111400840d1140c00e14010158016401d04408154010300301d0004500c615404241400c0a081c21401440080300c074002c4924500c5e510540c4507408610410749007011074040c03000718010b6103035682721442614a0050001c0d2100100314490203034000540090b184e105d100c44c43e5407071030861410300500c10074140042e000707a4014400751921056096480c2100c01301c9121010b005400301c0d644600143c16050110200034844950034495081f4152800900d2000c80d20801050310030450143d25138180d15221480c280081140e0344006031420 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 576242886 1250 576241636 576241643
    0x60405130c05040234050d11060c071703070903150b03191b0f0e07050711220f1401080a030917030f03150306010902130515040f0608070e0904 63
    0x6a4040c0382c281008000e40c407100e2499401a81c0c60344044100440c651081c000912011000b82c18000e149051400c2200310b080c20014000400451400d01600058003640610036401040e0303240c03554100b07101c05036005249509548000400c11034050350020021048a01c02c80b445080030007545030050548282608064042d406078101e214411601c0d64940e0040b400f6145042181c030710120f00101601194000d0855900c031f01b04104a418100c0c503400b0350040d1580727401401c144203655a20a038101001c1f00901c40c3d04644000c400340c1e4240103502c1440b20401104102c00000c0c030301180b020746520307038900c00c500507028000602900701251190032103034036544500345030f81000d0311000c40d0882440301141902c0284040c02034805180000c600460080603020303c420b0b07403401003515000050708488d484900612400c18621900c03070104042c0c420441d6880070300001d9085444290103140d002d01c51107400c942000900300d40104000740a1021951002c040c1140749090000c207020565005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 576244136 1250 576242886 576242903
    0xf192f09010509011b02032b0c08040510110d120e1506090a0207020d1104150506030c1606092609060703030908191d030106031505040f051506040513 66
    0x2015071041e004001030050817a440030100b00a5004030f03140c05113102c0e42000d158000100900090300ca2050300d1180a118038145407202d0140e030b658106c1e0f0040d8400c45000f81d20310321800b000a400b441401014100a104075105c03201000c000a0240311180045142c0d00e2810704a400c107500041000c1c03e20f000c8803041102c582c0c5600c01408441000201334944a40d03090240d100165220030070b05d52200d003d0210554088603900802c01142e0449094009400254100b004140c580380240c80d4005010446651140141e00d40c01c2912814020000e040c145000f113640c04015008451269003140e000d044040407002e490b442643d1312850010941c0a14140609000203120f908080d440c0d510800e105400c9c0342c4000c0c0b1080042d45000700030004071f41c1c1481a41f1006510f20020208040120300074000a0300d552030f4030500a0100c403904064944a600080c2441000610112110341c0b0204544011643c00c0885600c03000580d20148554100b4011880d0205078080c5403840301c1d000300ca00e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 576245386 1250 576244136 576244147
    0x603070513080109030e090106020102030f0a0b190305070617190504060209090a091205090609040b19080c01080a090b071215060206040506070302120f192f090105 72
    0x362000d070451070603003440098500011418641c28014840801d21940b240701c01100e804082190b0350300b058002e1021a0310500c02c05c12020441c103004d40e0000c41144000411400d9038010402112a21218503214483e00e41d00004220380014031808607100341e6107001d00700c2107000b82041d0071042a90b21320741c00b1164008400b8403c0a0b50702242e0014881c850052815084502042010608a80d0004690b50795a100700c1882440e4091480e020407900c2c1c2545403111840000700c09004885400d4002d0351f58215185503500c408002a02a0642c402d880000996500407590341d01c0200c101e0b0760000d41308102140c4254960701032800255400490050203681d2241c084441801ca4800ca000d40c90b2030b80e10102d045400c1075113501c064005035014212920341401d11038a41703007019124030f081604c100841d055a4049900098011840702c0c0004440c0e00d40c9072040c0c0d08081c0e44102804058034001c00100280900f60b20103201008182d0b200784501800c14881586004200c02d660200703204000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 576246636 1250 576245386 576245401
    0x60824091b270406050405010b1c0b03060414070b120415150f050a0b0c0a0206030a0e060f042a09020705010f050403022416030b01020a050111090a090b0603 69
    0xd502158400440c810304003400c1003082d51060001c1c84070030884201180300140c050074680241c001034002601d0511540d403400018512602c01c2e0204100b094041d03a9020040c502d01e034101c1c00b0182c00040858a5600b41410165000461303400b481e141032092050010b8423040100c2641c058006241c0030403181d6a641c0c959a8140b40d080859001c903d40c2d8000c4100f01d840041c600c0705c058494202144042c0b401e10050001c51407641d00020310135070040c00001141140041c15090a540c16902d1301c0c0c03030b0340720851510040d101c81100600c0300e019601c1040784010100d29071070300c9180202c1c5854209007845032400b9140035400114025808800001d21844403143c0040c0710081c4114000035603120b0000000342203400a450403001a08a0712402004c8151110081e00e2540011240d00c1e290070074440b800600901c090940c001e01d03407540040740b22a8000c2c8402c400c401d8101d0001d0220501c42039034600540d114120309407150700c0081c004600600300e84501d4880b900d0190801c7d00d035803140d10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 576247886 1250 576246636 576246661
    0x70309021305070e0a03080301060f020703080a0c03091212030c081905060109030503030a05070e1813030c080304050a0b0a0c0e090402270601170906240a06082409 72
    0xd00070028054890001c08080d05c4803682c2000840c09410425140e50402c44020003884001e5035910071507110020078000305038407000f1601e0b82800c60609888000c1140b070140c0c0d215050394048030901a0014190b01400b0081210454000b042d076820444040748400c1500d0150003035801c000203460715000801d025001da48425044041410f0548610341d80c1d03070781e203442c540c030031100c08960320346410a21408940107840c2035003a420482d110b11864000c2c180b140e648110041202c031421209a4070031050500541030303c00c015802000680d80c1c0c5c134180c1881a43c90001c41b034100c0380b00f1030000014105400e10711401c120442c0076943c540f0820400d00c1000344407d005042070741d0016400460b0702c0520081d0302d0b1a14040508c0d01c103c44c00780303042000542892081c805080c4007249000401c00c803400007064241c8d0080c204802419102c4200082c207500b0038a1600b40c58202464800108517960440c0f1210301c40c0e84500003070b0394600709000d04000b01007802080390350414400c1020442003240e16 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 576249136 1250 576247886 576247891
    0xb0a1b050c060a03020d0608150a02031003080a03021e040f0501050705030d0501150f0305221704142e080a020c0105071e09062a06021b06070309021305 67
    0x40c011140032550110004145500c98110000070a03800186518500064040d280041ca128001b500500d112507540740c1c3c00b05401070207806101e0b1b00000040b0081118000d0201440c2c00040036519070701301c0700001d0300940c007010221b0800181c1e03008a2103074000d20001c55040e22043c44950021a20b006d0040d10103801000e404c440c103000a1052520251b00e501c500c5000303100307885c0e007400b010010a2000d44034002c821103200405040400b003040c1880c4203118185200644282822103002e00e08040307148005010580070840300000340080c11000c117000306a2275400403100c000c0d08080a10004c03050000d00643c0d50007a0343d1030140951024003600d102540072403044000751420045089060840e90101c54550100d0031403d410034200c2126041115601c2250504803501c03401c08c10040c1140045181041080030351030400b030302071000c0711440301140b07603c0401951500c40e240d00100ca00c101044041046203e20700004181c5d078440c1c0680322a4940140c00c0c0d0090400080041002d003000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 576250386 1250 576249136 576249143
    0x302070204060b0d0207200603011401050c0a1401270f0c0e0112030807030209150a020f072318010303080a0912170117070e04060e070303090e010b0a1b 67
    0x11480c0000e00c3c416400000c04003980709402c010303545c414074030700742c5440c0f88800e42445841c3c480342c105000c02c1d04c801007181c2c155180b0090034a00310b244840120703405c0c820103281174114021841c81d1001c1040030141d944003000107030028001600d6001d010300c0740160b00981020b0303600352070f20098007007980980030030000c90241a80d84416501da10400310300c00d000ba481030340780142e601c1301c18051562110b141d0b904071006203001d5141c00349000000707040007108040d5516001000543e102d4090080140388000c03805881903480c11503992981d000c4002c9000681c070300c207502c1e149007420302d0302e0107140c0c004420540c0d0f440c41269908545046910510042c43e04840641d6900d1402c081525080d807498942007a50381c000d203480070607080d50281c20741a0b00c403101e4198000c004181e5044040b60040507100304e06ca02c000241d4441c1003030710141c01505410b10890240c1c034004420f169011400c0003d6500c1503482c0891a43d927203543c03145a10801510b50006440035600c0e50f6400d4840d560221010301 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 576251636 1250 576250386 576250391
    0x12030604020f041415040803030610030e1e16030503160501140c0913020a1413090e0d020111040e190605100c020406140d03180b040306090b0906070e010302070204 72
    0x142c0d0052690962041e0045807251200d101000c43c03c0c41d05045481800c004800701a080070716000c00241d580c04003030700e0b80c0e11948074111100300030351095100c040080352650494074804c0c0c4d01c1c00030500c0001d402a03c80074034021003500400c103045200b8010202c0764400d000b54a04040781c0c000c0c01c03002203001e07400c1340c01c3e5407070b00d1162001030490f0448038002c0e4110303601a66030340b071204100210350354101c40c4440107500500c0105a62070300411a0b050a0950350609903907800ca0616a4440c0c1515402034022940b90241088010100281e0070f01c041c0340680080101030480019540c09001d00e1040d4524052a580001e80c0c0541c0281c7c09a050040340e803004c139105e625040021a00a020034410000490342000f540c01d51509008280040c038100741c42000e41c0c801c1a0220f00301d403c1e4514060148040411000070752007020401600034030740062310340d899540302d00c7c0c044041c200341c4034169060141c01c4040b5980310720220390540100841d480d030550503000c0700f0054004c2c0d007009005991065 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 576252886 1250 576251636 576251647
    0x20d030203040803041427070e0609060a05220510300c0906080405033106030911031b090c0d0608150c0406080105060d18030903050f0a051203060402 66
    0x2101000500054071b007545203003185441003003d015000c503501c51080c1201844c100301e2207800030386e501e80b50340200280c1303015240c648004011902910900c4102a0000000104c0c5440550300c9005007030448811803d0741c810010200400005042c80e0282540c020002201c019540b40505101e0701c8000c0f01900c901010080c480b031110410070b0010020703011a131590001480154041c02000c050039890030400d10b1424152a5156280509142c0140514454002c03880300140c0030314240b81010041324524626881e8003004010b8405000700b100c0b441c6502e0300d1381005107008284040d6a204088120442c00786500c00c010303660300080e0600f9000340080010b0203454501e4080c00003c1c0511100403d03070015007401c81c05000380010800384c5c50072814032007400850742c4442c0a134116201111500d03120100051590010490340d035099007100d243e06000780416800440c14411203002d1400d0f5208080c00000c8645c41c0d52015074003c10503004104518503510b0024013840e04403234040c0005003009d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 576254136 1250 576252886 576252899
    0x140a03051909060504020111030403050c06071403190e12030a0315120b0916051c0302120403060905210d050411090103150b04090201090501211104140d020a03020d03020304 76
    0x1980141d006483d06500e0b40c0401082d560008890100c40c00301000540c80c1616503180c4070b4868044892152040314005541c10510403c01441c0669258400a0b40d594103130344c50070240c00d032910300d80740f0700032030340e510829129454840e440012100f5114007a6191000144085000306000c261005410070202000300d101c680141d500307224903108401782491410040e207007a1402c1601105205442274090051000e910760040c100004580710050aa0984842c0b80c26414680322000c0c0c24010b600104001091280c2e0b6000614a20b000c0e0303003520292404ca030020340c90000780ea040072140309801c20009581c01c80d0741d48010b601501410200025126110000b01901d00a0b481030311034018075502006040107611036182501d80c1182e04100340e80c010350002c0c16100c031500c00c10b4140000280d82240340c1c42d10010781d6010010641c800c03c070520304075051030203580140c01b035080c2204d026040c1102504041002d00d01c510b0300100014030182c6142d00704003041007003480c1101103010600000488 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 576255386 1250 576254136 576254141
    0x9060301090c030e013b07061202040801050c1908010602070b0705070b1b0d030507020c12010f1b0e030c06121009020703020c01030b030a0c06050a140c06060a06140a030519 76
    0x401c00380303014000030b008401c07030021400180c6e00642d034060b0112040091091200050000c21501e4604040762010f8a07400700c0700086c004c80d4007070043ca500700001c01038802c1e0001d0082a030380079840d420911408080c00110b8541c0d1007401400b0244e40030440c184404140c5e84007501c2d40c244981c00b21001e10303889a00000703568101020b01e6459009001c03191601c0c0c0c07401e100d8220745441a2404006d02d141c007a030001d40d50b100100966002d1581c403c0201740302403003900301e01440030005c9424880900040015844144a0300c80c200002c0c4088680d54030341d140100701c444040c500200b600382040307031040088540da03801a084040240c40f00000040580c41c50020f48905402f036005804400c407150000360968030804113036071103034100702036610000d203410000000703592407450169200c1c0341090040d51000300742015601c4054000c900d50f80b024800003582c5200381001d840c0512100d945803401c0e1043d030049031200d0f003c25418008080054400c0e40f0103580100c05503400e10040d42d402c00e02008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 576256636 1250 576255386 576255401
    0x150f0303041a0a0314090a06020304031704261303140c22060e1312140c060a0b010c033e01020d05060909071e090c0801060306080309060301090c030e01 67
    0xc0c2c61101141030906641c0600c684c00302c40d26117050540f102d00c1d120140380d8541480010003881180d0120224042c5071082c82807404892807901103c0450800342041c0d00607001080c02151800c01420300c040356059898151303032914000180d00340740e050840d5981540a510754850041510400d584080c80707948903040b400c0b40c645544800b110810300312184505031586074000c105807000c0f0400340142102ea090440c4a01500014080e510b00c1d880d000449882d05412401080010086264210f240010070a103004402031070081000c10010b50040d40c201d1450007000e00881d0140d4840c04000c000b40003070200d600c603412810100d001d00412900882030440344a94500c1e1760114007031150f98460300c02c03a83c00500450300e40c1c3c00340c41c08601031075a9509500502c00300c4607244192000e0300206400b040007611001c0024803042c5003444000b01501800d2007240700090400b50000350100d4044200c500031107003e00403614580c24940d00b00b014040003065a0b0405940d00300d00c2d110014281709410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 576257886 1250 576256636 576256679
    0x40f0c0e01171c1b05102301050f01050c03091f0f18050d0206070b040503090108011e03110f040603060f0f110703030e030f0d0501180203150f030304 66
    0x1d506000e0011039580c00403518400580c41000103480011034524040600005880c14540440fa064202c0f0011400714000a0042c0b041d481c000c60004d0054110004140c80e82d6a4212581d40146406814400a104194201c040301d0403491255125100402090780c0c29000c40c1e140029500200748a1440c203464251903c1a41d480440c2ca90351049101421030340500c0d14486100102c16000003840c45441424440e16007440c2d54011500c425080d9803209421049512072881d1504000d07441e03502c00104940054103400010501c108102500c0302c40d0078801e141800d0041c20341c0c1e901d40100d19500a1285d0114010780c0c156861380d150301030320380514420b4401040c901c1002c0200030950b82e040885000b200d0400310030003030408640c0240c820b020b42528000c120541882d49075821482400d10300000f075100011010001341140d080b640c103c1d20281c0f01100340341c104581010403400107440c2c0c821104151262040e1030300c0d0148840c40390050040549241030368580c14100d000c8000040396 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 576258992 1106 576257886 576257909
    0x30c12032d110f0417281110090807060309031202091801140109120503070201110f030a12050c131206090b041103101a09040f0c 57
    0xc0404102154100d50f14903401840b065154864059a5440b4045031030090b0344010028500c0302154440c0c02c624aa003c11020804002d8140a4103a4907948070542207040d81e076917030303d20700c0c00501c090316440d20062800a0300f90800038aa80308105041c903146035800803a4122186902e003010b00900160744003007040c00144043d1000e01d5030014801d140c400459000511000b100303410809032030b51220140e40760b1500322811b21485009200b50020300c941c4c030055003e001240315100c90501604e0071006142000e0f45190440d010030343c0010701c910394014484e1058421103070040310708081c03281380a05d00d403000a807038500d500c685001c24428056460920015620828116500800008a500345810001201d114006083e4803034040c4004981c02c215803440303000e180c03c8081c016224221010000c0000c003180080c010344102400c49000ca0015900d860300d000a0b28580084 = true := by decide +kernel

theorem cover : BRFrame.Cov 576079136 576258992 := by
  have h0 := BRFrame.cov_init 576079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 576079136 ≤ n) (h2 : n < 576258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
