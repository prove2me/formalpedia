-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2294
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:16:40.307569+00:00
-- url     : https://prove2.me/submissions/77461280-aebc-4c7c-9510-49152a88a8d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 412410071 ≤ n < 412589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 412411321 1250 412410071 412410077
    0x11010b01030504020a140a1703030402011d0f0108090c0a17070b040e0c0c0f01090c030b07020327010e0307080d020607110a06020304080d020c0f070b070314030901021b0607120606020a02010c03 85
    0x343d03550941c03e0302102100e50852329a00040200425035800c41c404600342011a444070f003862009000003400c21600111440c100589840040c690741c404003c3c10b000040028140c952140e514581000003418054211940340941c010014030000b042050b00d041d03407044003985040340d84a040107001070304040d051a41600c1103d0400200c06d100f88a0504030b00c1c0901040c240c05421400c0c0030613102005000001194010440241d01c10440c000034007521121001e040c1200ba207910040b40c1020300c001805a00d0f0080000004103004001a40c1000041030707025101c0716500d007107080e80d0408000740c81d41840d4005a410b0b400044507980115030045c49038943c41e0829401d100d40d401240c0280091442681c4071104881d4280c00800c8144014070f021440540703042107a913001011406000b022048c0a0008404526400b00a4051740c0c81038000b615074000088843c0c041c0780d41c0d01c0c01541c1d0203000c42c04070801c0d07107482c0c0c9130b9001d2941a520f058004218000c1c00747e004440d1502220001d07420 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 412412571 1250 412411321 412411339
    0x2070807020a09090c0501090302010807030b0a0f090e2b03050a021218070b0f0405040b0d050321151008040303111602120307030917011b11010b01030504020a14 71
    0x1030b659203001e48042d218006001070032403c01e00d801805025690030481c11300440d441c0410060f81e120580641c03103403040c40c0209140120f2008198540300300d07001070155050b0b0f0b100114901019500c81c00310722a40c0011191540f0340e007214070b031080380c140c140c0d00740e4800c14807180e105050080c0c0041d03400c0490301200502d04940103540203a05c210650348000000c11136072466040c581c040003e02d000c0d14456249915280a00c1d03041211803249102c0d180c0225100e168400307440c1d607843d0040c4040d68200d001d881c0e07210380414084200581c140201000700c601c01303001c41c01d489886c110580156002806038040300e4001c0f0400d641c0c40600420840406845482d88101814010041c0014501608601030610154410040103818522007042c040c2c2c07090000d43d0200740e201100008549500301030300b5130402c052001e2809808070542c00344216400908841e24030b50b00c0f1040c3c60340304001e00020080c3e4030715000114240e510503034019500040f2039806001015110003814100b080017400307189 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 412413821 1250 412412571 412412573
    0x602031909090c090821030a0c020f0a0525050310020904330b0708040e04051002122d01090c0512010305061005030a031205040c09090c030203011d0a0602070807 71
    0x359000390903640f0020300b038960304000d40c1c8400c010000c500352100201c4410701c020408450705501008046141c40394951101c011828000d01076404108415019034420407003500300303580d81d54081050001090318401112401008095004058440081c007400d0151007140c06003010350000392200f940107a807101503c0390640c611080728051101c904281039800074145003055207442c6030f440310701d1901d010091240082c50000440c0d058551504000c0201c0c3c480e4100300d0b00c0c201d1092600b1300158070000307000ca84040c6546040b4441c24103048021261014108102c00c0c0d280c0700c150b9000080030640040c0a054040d8019510b49541071501c0c03410468429500b0b2920f903804e91080e036098001c1010b100000e0011160703c1d02611059000300500c02c1c4a0345c001302501d40109607285e4140e929004203082000018488004060349101888441414105000c1c150110700c412803280d840c1213101848203588a28044600b036504014202c0d0220303d07196000658407880003100c6140040007644 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 412415071 1250 412413821 412413839
    0x60509040309060e0d08070b0a11030906091b0d0201081b070b091912030203150d1a241908060907060e030106050607030302070501090b090109020f0a0602031909 71
    0x19100d14000d5442240403490400c0161111083c2113105003c1c2c1200700d01c20002c10b8004080350446540140054026036940382401c0c020b22000c001d080b041040041440301c02e4400083c2c003802060a00142c030115080026200403004135149010b40210100c10850059801181c4165014822808142c0304c009082244103040d4440c56040b144089a5818410820030802c000c031503024050302c081c04801d000b03454400e03502e020444100105a00000060240891600b100105100141500500e8901c40c03524921907000500041c88600440b800503070380c0c52030030010300c05003120200102c19003c00c140a001c0c8600380012005001c1c004001c002400a608000e003a200751000000b038203000b420544000c00e8240c80c00c407120311a070304000c400d1000e80d80300d10403221495414240140d5810040c43d26502401c52070304040d0059a0a404000080300107400c40316031188210b0300c640c0e1444109040043d204c030b2901442c80181c0c02031003810340201c510190f8130500880390800e5000c0a80d151190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 412416321 1250 412415071 412415089
    0x12130c0905160905100c1b030501061d0f190924060f0b040f06200f010c1b0b070c0f05060405100609050f150d1506052103070303020d0605 61
    0x4407000550000084042c0341d0702a60500c0035220480310340c4045030402c00000c00c2c0d0003800f000500410f0300d50b21455108000c4480c131b40019a40176000340f00c00ca550f04164028603c807040d890a40c0c0c4908000101d010780480711007803084500000380b00102040c00701c254000d0040700c008446040343c80c0500340c0c0d582c6280c903007403010440c20b8001040141c2409401044183c99500c00981c0c10003c0c0400d003d00c800b81c18181080c3c41d00b03450000c6410425004102c013244c0d000011645d140140480c00103690810340004c502c08070035031aaa000000200348000b00c0344051200130300200d4005010415041c410401d501c4000e0090b101c45103908101d4480078105282610116039035405400001400d00341401518014900001d0402c11032900a8403038022038001040d0f0907407405030a010007419610400682c03102d0341c00c00c40e01750340251880510002041c0901655104401041e0640801c4a404051130300e000c09060240d03042c00c5403a9010340103900400d00c1d020406807078820104407900c8065503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 412417571 1250 412416321 412416331
    0x1c05060a18020912010605040606021906390f0c0309090507090314030d05060a1202130e030a02071a0a02030f070c0306050702010506010f03050606070209180708030406030e010212130c0905 83
    0x550500e487c00b08401c441040d031080065400c004106201450141c1c464101290404008211224800c030b1450301c00907001c07480e034100300750182c00c00f4010350011000441031070681c0311076101c0c0406034419250700080c94001400101480c500340b1286516410598200700c140c00e103007442e80d03260340e034900c0c2086020100008a500100e19248003101c4c030f005050300580c4c140c529604041c10611460004000044060f004e201c0302c031022082040142c0c032282c10030060000703507a195208080002d4644220344074141c107651066150310040c06002c0c0c1100e44107146034008501e889039130783c40c0403150f410103a1b00f036031b000d41003043c008085591400f6140c03180c44c41d9030000880d8070305940050304e80c001d42104a02014074280410103d030b10307072a0881c0c28458040342c003800305075211102d1625680b400e24402c1020700401400003031040340007000d00252481a10700340075443e41a400f0508034003c03001d0300a0040303d039a000c1540918402c81040019025400d140e107141d44a038030040c250342d029030b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 412418821 1250 412417571 412417573
    0xe16110708071205010b04110a0518040c0c14030c0706181203050304290a0207140106030f020a27090203012310060815060c071205031c05060a18020912 67
    0xf00c0b04100202032103507480c1c1940444003003041d44210b00303e040507809000c0ca103a0500038002120000301c10407051054440318020000c0c0b0a188071100c009141c0c600003003086039031072040340d2801042c0001101340d80035500010b0040c24060319006085803500c4100540354000c1703000d50030204010341e044407010025402515443c1d9681414985001c004480030391042010a406202e01c05403040c0e044034640011000e07101507100c917002e080569910380407003082d908a40c80c2c10740000c2007100300e543c20b002c000d000700c07120310308182c0c2c1d01d8030080100c05060200303010200e10034503c0001b24aa5120700039040c00900001000c00c410300106a502c0300340220809954504020800c0000075000b008000e010649008141030078240200441244c2020f40350b8442c03e40841c9007040400304200300320042c13841054000400c00941000c07034482d4040800080f04000c0500d182c0540d41a902543e4020b040140071017100398a885000c1c500301c035a818085003074540030040d50103d6074074050500c2080820700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 412420071 1250 412418821 412418849
    0x6090f0c07060c05032226160f1e050d3515060705121e1b1501080303070c060605030f0102090301050105010c02150f0424090e1611070807 61
    0x5611a00b58240009044805040032006c00c80000c00d54400000b4030b554481d0340c01e03910030f14400b00c20010b003c1c0f08005004003001c071054001780b06c003a0b040054a5406010042800c0e96a1440d65a881117090401f0304aa484414120300180c4a066200560020400604c2d4680c40c00c4042a14404400c0400d030034040500090000c407444401311030840c01c004848040c54008691b5880d500c0d40c485083d9200807400101d200001e5012000c0a00e00004c0b88086c22a5202c0f07c020341054450909168019188070310101c0e4407240005240b0701c0c1c180d0356084025400d6698140c002c884458014004071941600c5040008241d1020041e030020140110009a2581c010f00203041c21203005a2046040008088181004d42c540720300e00008604900081c683e602c1269088100910403a1b01010b0046030815100301041c62003034035003614440c1030b81c4101a0503654030100305601810355040014920481058408038012904521032402e01c5040e60820717541d80301c040d420480c540e4090400c0035004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 412421321 1250 412420071 412420081
    0x3040807020913150e100221042004060501051903151d0a11031902040b0412060c030912200601170f0a030e12151807080606090f0c07060c0503 63
    0x1092900500341810b200400241c0d440c400d03c103644545551b030f582480c950005945030b1003040d40e119040c5400b940c80709040309043c40d00d0006540d00810b03800146100501d0080c01c0356180900501045400503900d032070500c0d1030f5482c8202c0b60381144403980240741d84c40074424001b8000c1000c44005260b01402c00c130a05003501a020391072100100380c0300340946884030940b0070034218000d480d00010001c00303039843c01683d00c000380d00a11440c0c0025200010104000030850314600701d2060b114030581b000d00c1510301c1d841c016004e035039800500801c4009084603c1c0002889044d07480c108030440c0400003a01400b2100c010704065082c0c004007080340320001d1000600401f001240c00a5500c0c00c01070070709241e81c1c1ca0042461100010750341c400c1e00000149444050104a904a020143e000b00c114a0400311002020051a550b05901d507000310000080e01e19804a8040d11903180541005002e0ba03601c0103251010900810030310700c00405202c41d40c04118948618000b0b082140c880b207681c2e00740 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 412422571 1250 412421321 412421333
    0x3060b011101050a1a0303040806070530041e030801030305030c0f044502070c0e09070602010513020a03080a1e02060108151e0c09041a04060e1b03040807020913 71
    0x2680c40100c0c041c7c0c0c0200800c1181800006480d548000c040c90300c42d4407540f00015400220421070291014130460404a01096000c0d00c2154082c5100b083c048040c035010303c5440840c0c0041080240229806800402c0428000c40007550302c452002c0d19540f074004417512084954000b41c200d10341c500c02195506200261210f214401e00c0c1000c5452301d1000040300720035004080035040c2d142807a4001c0303000410001c1e001c1030314001e015000380070b034070380d2602c1981984e4a000700e2085000560810000c00e8580c00010110220b054015201d0b02405081d519201e41d0b82c0d00001006003000200c1d07603900408000d41c80b1000b09018180e000d070800c0e5140c0114545040340b01e900c5030305207a0000f0180108400d070400717180f0304412109444491940c0b00761a0980074052a002d83d50014200424104040700ca04890243e070402110204122511070010354907800085510030f0801c00b0032014054003031160805503500902c52504940f4140301075000c0741d030090341a518064040b41039a900010400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 412423821 1250 412422571 412422611
    0x5010f090609020a08070f27050f100e06031e070b070c14010822030306030503040b0a03060e01120f06020904020409022505030301140d0204050915010f0b0403060b011101050a 77
    0x1c0005d0080c1051420070100e50302c82d483ca071103200c600090310310300251180440100c89117915941e050410803894045071030302e903076442250f00380314800994070082072181101f030a0781d000d01c80150041020407100d4030785406c285c0080742c000c19180304480001aa10000c000103105c8240315100340d01c221071401e203003941080d00403e0340310305100d8914200201d550406540d2001d150100b18a440c0203004c1c1d060980052140d600041c0007404001070124031500010001d016000c403a40e4100b04040d0358441c00c40404c1d10078003884800d407a1104048011070060102c1300d0240b80580001483d2000c0c0c100000c00b264001d6024a019a4000c10003140031102d05203c03038070341205042e82c4020f041c11a43e455440b0b104c140107070b8100e050900ea1084450316041d4140e6002d0f82e010300f040110b41040c10840383d440004140301d2141c0d101d41c500100f8080f03885d881c100201d032940124a41400d0441d65044050000c5408803410030803100d030301e8407004400340501d0b03019840c660400640f4210070006501121 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 412425071 1250 412423821 412423829
    0x50c070902040311010c1b0b0c0c040509060705072d030f0e0904141504060203010806070c0818010302070623010b1303020f01030e0706020105010501090609061b05010f090609020a 79
    0xe44184002c10100300b00d4420300040c94001d10307261040d4000c5180000040310304069210501c80b10340d40c0817401c1d080c01d10040c1074184076107045a81148183c01000b098820465070b20065401120105020b84d0081000e440e4261182a2110101140b1184556010000070010405840c0344c0d40394414160410314952500314146032454592600c0004100b031003030082c2c030050080885004142d009078013480584015101c40305401c100d41000c2c10680041d402c2070003512070b140155008030304268040c1e6200c01c031180d07000c8441401c02d601e40441e0300c8a41500c140c0c1e42c0c1859003c200307100c002021403144004440c00b100c0c04c801d0030080058a440785d0f4070305030014420702d14100300800003041101c040704c049941c101c50115200d4400c4004130050b00703420102842901c6003010104400d901034210701d060710340a81c1c03020944d644d031302c0040b106107511344643c00c046a122101c0030325680c0c00000e0398481500982c00411490b507034105040459049140513602903650710b01c800214584082c10384010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 412426321 1250 412425071 412425089
    0x601061404081f110406030f1116030305070311030906070f0f020703140114010b0301060305160c060b1f050405010206011508131a010b07030e030a0b0c0a090f06050c07 74
    0x10034201074125a0703e40721440034080c000c01d549108808082180c2141d50364040040140b61a2942c03440050080c07c0c1da191005151400c02001c1c2107040c00040594070040c40e0f540088001a400351420f80082001030000350805449034001c98200c02d410000f5030007001003800070725161801060040a42d01c90000207010840100755089600342c1c0050031801756078200640680d41324800e0080342c0106021740200701e03865001c200001340c0e0458000614101c61a5480600c150ba4a80c600c241d00701d0700b400580c8010030f605109881c0424055400243c16000c083c100072441481444080035829094861a000400002d001c1c0520359042c4885401098034481c5d20358402d24044010380b8007070004082d007002402903d02242803050b2659018840d8007001d15100c01d40d41c4400070f2600d1544400d07801e03404030b1004058804035090000d01e00f81c50710307084086182d5035182d0700841d045651040ca0480100964804085100c07650641c40100800181e2500c0b940d420182c6601814108594014951 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 412427571 1250 412426321 412426327
    0x14040509011104060f180b070b09030405090f180111030907080c1003020313120e04380d0203101401150909021605100c03270f051504030206010614 65
    0x650b10704001501c081d5442030510801d114410030044070803044030020300401040c00d0100181360400c0c0d2000340110b50003402e6914065640c030892650300d1280f403050301d400641a20000709074419407402d80f900440c420402e00201c1c444080c6103401d4071115198003504440000134020110f000b0400d01008200c084c02411000145500160080c07050144d04005e01d0b4000000403503456101084026483d80700e0920210000c0c0101e004020400e0f010f0a0750207181b500031810002d00d0011079041c001c102c403c0d10700c101600410846640b541c01c0d80d1400c0d800c115442c16910060350b040c01040312881868400150290000c150041b00c000103038081c502e60f400714110310300c3d40f0342e02c8003004040d0340b0000d5000d65620070081c44030b04070507441d0b40080c0c418003c00040c4107451509800881ca8204a0b55052200084014000c480180c00740c40325081503481c0d20303996001508410141540f1030045003911a40709440e800b180c0c4107002258110010b03005080103002d07240d0401c4096540303101c808a040c1c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 412428821 1250 412427571 412427591
    0x6151c03080406020a111e011503050c01140409110702040b0d1e0f0c030302030307030509010c2106080a051507020c0f010e0307180209030106050607030507140312011404050901 78
    0x1040d03a40103070003d0203a81e00064000c0005004000405003600e00308226106803039401c80b40c1900c0ca040b894007aa065007495a100c01242c1044072800a43c1d80040140039030140300070055070744141c01a20b206060324244000580b509140c4110780e21540003195159a50384c20b0310402c400c8404600c0610311030791000e42100041181140c42c64400302e0000c480c1c280c0c02401d0300707100446024081005000c8100c1c4d0b0030100c101640030000c0e50182034a51070502064440c0c002088c00d850941c050340780000c040707406c003d4560040140007606500b01e1107000800e0754444000074105000203100351780a501004103426400c000300203041d440445803016000e8241d0a40014510101101070181009002002050030f681c4c207000200c01420007450469400300150009800b9400c0220700f28441c1d4031304440022142400700403110f05035071603520745290050703581c0c495003050040b5042c0d124030710090000030a600a80030b6070b28042c0041c40d00340c540240684c01000240c41d802066240c250b410710490903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 412430071 1250 412428821 412428827
    0x50108070617151c0618020102010c0915050d1104060c1209050d06020c0316110f030102070506060d260403020a0b0c120a12090b0421080c0a1106151c03 67
    0x1105001110f2410b0022101c40c41c13500313180308050014121524008041c68140280c1e0b5240e002e192003a00240101c88005001382d41a040324410040e400380140500c1018034458070040001e048103000000d40345a4410740c4401d00d0300250000070206e01e4001114041c008098425100e0484914181c018541490045010803c803000010901900411204150103080c4152084244103081086da88401814881420981040d145005900440110b0703042c0c101802154076081d00a80140002c0d29a0414801c0c002076615041d1001d8140d441c1e20810b041b000c1040004c000d0344c41e4000c580700c83c1540104100789026910a0f159a071080040b91503015000c6581e41141d08100004d548903000030109598000d092581240064030300403180041045808540b13010301e001d4948540e84c2061a117520361403030b60040095012859200c005518844168010201040503141c00f4a450040b550224a0a9000d40b0744001002c1c03040e4990712181007462801c0d40410703030400030544503882a00c006d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 412431321 1250 412430071 412430101
    0xe010b070f110607150b01031b082d161e02060f04030e04060e16032a030207060c08180706050a050306040e0f16060e060301051e04050108070617 64
    0x502c400408035a526550f540c800c00e0342e14007600300c0d030103440c4107410300c0185004005480e5030700c2c0460300d80914011120440c08405c0c1c0c03802030b40c1c0c459494079150008117903500078180c69a00d12150002c100c0003007034800400303040d010343e440d12800c0711a00b8030356402903c8029003107401000040d4443c1c100311850790001d6019002141840f508040d87c07150b08046517078440c11300310b80e6006400c210b40001c0c03010b01d0503480c92040001051201d90754903400c804070709035800c410860100f440d1400c420080f10644800d075822280c00e500707005151192684e01e00041d142c1c6445040c1c0031501007401c01401080c100c88150080000f003006c4c0c4140c60914802410901402ea085c50402002000040744c1e80c40320307802042c0496030ba070110741c411804000794543e1a402036100020f004c0072000d0009140e03004513892048040010b24590841e1308202c14002100011a0703071101da013104080340243d58640b0f20516000c1c050401c041e00c0d51505281000e0701c6414441407114094429a0802050850351010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 412432571 1250 412431321 412431323
    0xb07021201020f0a27031101030e01020f04080c040b090f0a09020409120809060118090503070f1101120e0a02040207050a0b040503131e05120307080301060801140306070806090907030507030803010e010b070f 91
    0x46007c06486040c0104d00506020101030001d6100080309200b0001c194003400485000c90100c60040000d1340c103001c1aa4020445141c004114401140d91042c01e01d4655a009010b1000014060590b400180a5414406080e56000b40342d52011040e55031010866038401d0b10360b0000d00555241c0701050301054070030f01d000205680e440c1d442d80100003040c81200c0055420820314000007840b420040750103001c411001e4040341c92144040c00300c410078024424400c01601c050440300c0440e40a010295100003000c5803140945e1a04200240003c0c4005004501440c002c0d512010309541110f060301c0240c009d011034004400b1450804001400709200b42c5209454140c01598500b440900d9401b58600003000400c001c07001045103580300b260389040b149254603082c0040700680a040d10381200340c1d844400a40c4010008415041c01e0340310a802600346402c4030003c82c0e403629018140340c415003044401c2100000104040c0103103e544901408840510138580000c1d582e803040e040c50800b41c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 412433821 1250 412432571 412432583
    0x80a0209061c110109051e10050f12070e100203070209040204020712090503010506010504050f21030a110d0503220c0f0806061f08071103040504050106120c0203030c040b07021201020f0a2703 84
    0x210105120384100c09441c64492b0300e554040d110740c0440720084069008441c540300149210035002801d113051384a0911404c41d540203989070924503000e114181d10010402d80c3c001c0d800b0001d450000341192101c0c0c030500019607441e03889a04160400d400e50f100a41140d04010082c0801e00c469038412044000d442402c030f80c0351082c1500304a1000e1040b4601d00a2816800007280c0700c046240c110129544561036801a5200380212200c00d03202e5010694101070300d0702e00b40500c1452104803011020b40c150103040ea441d201e654401c1180c004005640200c2000e40100d000c0c07200b242401c1e4501c0514a601501e0f00034600302e84a401000034100500c0c1c00200a5048503036007240d00184100c4000e860080c1c8203000325038503540041c10762104003104000c09807820001d202c502c0d1021040c0c0e80070303000d8117490502c2d042c80c7c01e019540d240c00c076400c16070b031020b0701e0220000c1810003480248884640d00d60300b99103d000116000d01030896000c111640c03125400c00c081c007400b0000c02e0b14000d4a034401c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 412435071 1250 412433821 412433839
    0x40f0b1306080c1c150602062d15030a020a06031401080a03050f03130b04030c15050c09041e05180f0708100509160803040f050a080a0209061c110109051e 68
    0x70100e00094a40050a0008045c03200400b00d82039a0108143c6c1c401e401808030090000d0301c04030900041004415401c01c0c4d0303810394005c10a0400400f0b4409040c80d4018200e880004090300000c0203403c481d80400d001c0b0b9030320440c1c0e010701c0e003440154a0050204030060400101030b502d029109116088050b0a00b40c400000521207050700701350701c200d158100714240890f1407e80f4000e0414280b650050321488285424100071200600070644243c1c5020080c0d8102501002800045c1c2503c54610503003079050400c40f4024096031159a11130414070f40725002d15400d51032030600b446040881c100301604050007d000d400000505d07401620440d40c80003035a90b8802c001c203410b011810500351403004242c400040e441c000007000e4010350746071204943c041591030003041003d4a10b07200d000040e4201807540400351411000ca1588283c3c040c104841c00f043e107241540b04900010303805c035902030140e44070401e075507440ac0c00c040140005071413225140500410609052000c981418031560090b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 412436321 1250 412435071 412435117
    0x306010c0201021f0f0b220914010908030708060603100302010f0c0615031a0c0a0509220b091e0402121c030c14180d170f041703070b01170102040f0b1306080c 70
    0x4520300c9d4240c18805008100c28469840c21300c80c1544250340110000300501c011422618141c0200c9004550400c0101e00761840d40c1c2c01541d050100c40d0520080c001c2160300c02c4041103260007100410034040d0b6022901394150f00d00040000c050b10101c00c03e1a01d40801c10111041c058100d424401560401c40c0c0c07100003100014510f400e001c021034900e5124140c0282ca0138580e83c00c120301108084840f091b0f1955082507074610f05019281c45900084880081000340c1000300c2040004c08494043d110321701e907001a81c1403c600f901c810100020382d50309035940990783c0904420038034011440da139494140b059050026001000b00f4062185e43d4964410f030801c11000180c28610803242020758442252103010005500140301d080012001c00c0080340324500c0c00b004407001c03587d1140f52032003140d00309006051091700361070710004a0b40d4200404501900650325403401040641d04840d6134442c00d00080e02a0f140d1580301d0000d104402060180340d05410064403e40034010b00028000070308 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 412437571 1250 412436321 412436333
    0xe0c0d0504020f040905010b1f090303030902030c0405131403031621110c1b03030f220f03030e1009140105040f12050d020a02060306010c0201021f0f0b2209 69
    0xf42d035000b942c0c06890a6580f0013040300c103400c500080c8808403034480e14807100800d445001c0e19401110400110010310600000c0c1c000d40c0140c141c03078009812100d00590140200341100c03010303034440b5100c0c40c481c00e134070701082075000400405095480c086d60444c14074243d1000b12414140401007408000700044820000ba9540104505081c1c242404181080d82112030030f5801610300c140e0390b000c1c17121300011031110005106000c600190007546042d40e0180b1200081e00706d16180c40d56203c0c000c0d01450400c0a5205139409040d9030715081c0065461450042c14003000c0c1148140111262085231390301542000301d02088840400c12100418243c50040791244103903007019000040c801c4000c284d440540c0300c030181d030503c40c0c0304988102404400a80c3d5940135050001d5002100f00006402944512644880184180120341e000048100119a0b203080309a00113443d90b9215040c030b11440e51401480b08603001603400e484810701d480b9002a0304040481c00d19070041d1984000030403c44 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 412438821 1250 412437571 412437589
    0xc030c0d060f140909101104080303010602100c031a060a230406030507020a0c150e0301050901092a0e060f0607030c030906050306060306012102120405070e0c0d050402 74
    0x40e50401089803500280c040104450003061882d518203c0e80d11000e00b040d03150103000e204088000c0c00440d00400d106006001d0396254052006000d00000404000400146018107001e030050f01c4c24000c0007055200b10f42007100404105801d255107a40a03c2040361030424800e010740301650340d070200e88420f864148074419581c92001e514000080d15240d15005481902d0b890f1380c2c180401d8441030402c90fa5400c0280001d007803001a000c00308002c0b1b80301700000c95245a50300b0715610300002200000d003110700031590050665100e130130144c02c004082c0202d10f05108107043c03458130300020018400d10000c06029020702c440390280442c480c1c0c2c0c0c0d4024144941d2200800c000c0c0d85040501e00100b096070790039000c401064a87e54040b0792140603005480c800c65001c3d10b400d0459a80000450301200184940c0c04502c1400402c80944089400240a20420021101c800e030a10303240c40d82c40c0c01d8080c0c0c007d094a1804000f4851f4808900c800c03140c244040c0500030845840d03500004034144 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 412440071 1250 412438821 412438837
    0x108040302190c1707270612061d0303070e1201110a090f08030f071220011d01050c0919080d080601020f010608030f160204020f1c02070302060c030c 66
    0x15a18280020014103000f50f400b41d0307500a41c118401071440c0440c0342c0e0740480340260160000034a4001c1074210480803150300010001c9004140640c0e6182d0000d000e000c00c030340a03503096840b402c40e844c1940b601800814213a400100442c51403401e06c00060210380710142c1b20b4412110a42d15401d000c80940000b10389841814010b66110b40007900038014078514400c40348405c900450001d4482030120a59800480c0c8941c010714007503041e40e0b401e10300308203203456038203006101004404110803040c010f18440441c80000441203d60060f22072601300e40c00b4120202da0400b010403018002c0c59003540c0000301c0586244920100c0b10845920b100d1aa4001d1900d0384600038125541c4e42d84a40710501540e420303001d030790345805207182650986e4068024000a98001c0140d1004110728500078a03840c0c030240d807a007004c182c15900050503a40318241c106030f2070b00c000c40c0344c00000c107a0440c1c08900f82d194102c21032401c19207560113905c544005100300030702c880200004040140d0003080f02c40e88 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 412441321 1250 412440071 412440103
    0x10e030406050c070602070b120405030c060a270f02040b06120903041a07030801031e140a0c0e010f05040c1403040c0f0b1c05040c050d030201050f1b07020108040302 73
    0x15921108010b115401c504440000c0e8859040300160170b900219220007550030320355000b480d041896004580c0c03018080c00c06c8a4910007000743c0e00a440d420701c11107004084c0307000c012032410b103180c046c882105903284120fa03010299114074400190b01540d40c400300365068401140d11201076002034942d00a4008246580c88450100004c13414080014016a00d01c00840e80042c40070303502c144c00303d00551038000c020803580001400810056090800c40308040a02d1401680d050341d101d07214600303075042d10704807944440b19540810080480b1035024202e803800e4100c46600d81003400a401d0b865208590103a9078408203008064428000c02036203803032903c0c41540d80d04103071a1680c0c100a20b481099440641d20801160744203100c000c13103000b5100c0020328290555401b01c400700411018000311071a90090000107010f40720200341c4030255010b6000000c0c680342a0340908498417008000400a504c034594600c0a100c1c40780503146842d4080c60141340d17070b9595180c01d82c500340d80070301401c0e00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 412442571 1250 412441321 412441327
    0x5130b030a080a2a0803040b091905060f0114061219060803091e0105040302040b0a05040e030c01050106030c1b0303110c0a140102040602250b0d020301080d0903021c05010e03 77
    0x1200350010342c0709500381c0c403a070f20100d81c1d549480091300e5052940728004240c0b40f02000840c0100345a10480c40d040b41550041e50440d84040003500031a60841c00c08a409030049410412529621040c050050080b0350201903114015000102d09104881c0303550500541000803c00d0414901c00040c4802c8186600b04210307900c505256581c0d800041103540302d2010120030b59403401700851540140d85041e10303800e0402d800c650030000540060b1101c2ca803c08140034001030303255034500603481c04030301c1e20024550700c1c504c1da1365403400d440c016042001490f0920007150343c40790b4003e0031034500c2e181c1c50b200030100d00443c3c642140a46100d064000240348040788506003654049401514184650207200c0c1225a20a8031400d030b00a501c64a009a00051900b0703030711240182c0c041203074104020311184d0003522503810445507080740780403d099560200040c00208400c10a03156504101c0c101030f1000391441e4009185848000002d50031012011081d0702041001d420186048045ca000daa407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 412443821 1250 412442571 412442587
    0x117010612110909012901050c0d050306010f050306031c020c0a0b090307061b0609020d140a02012c0111030d1113050901060f140409050f06040c050405130b030a08 72
    0x38141d12501c00344100489404503054040512558070083d40d0f078210080081c2400c6d1403c101c00f45820f0903e410b0000c10004c2020b0290184043d84104101e07031122038590600c80c00040910f0b521085a01c00e1000c20028001541e40000b4140c02d0b6050584c42c01d47c1c1442091004c900b881403800c09150410180301c03010407921051800743c18501c0d81a1304070360500e590340c13004540140322a030300186200c1d5845032040105110341c1040a0460014002007200c030502c0d55035113007618070303000140c5090300308c2e4003288110f6070b1002640007114030150070404038038800f0103d94901c1280c000e426042c0700f5405d032040b1440c901030058030880c000d000310400c2800e04203540707210180c1c40034801145081c1d080801041170320740001c03640d0581d5403030b60380c42e40d01400301070b400d50b06c8440b07581c45035059080903c40080c40c10198024540f08036100e180d582024107011040c4400e031643c03542c82009000041c8418403481c1ca0b070f40704c1c0001003000c0361008541888620042030230302000841c0078101c0840020016 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 412445071 1250 412443821 412443833
    0x11106191505010e0d0c0e010e040606091a0d0c170c0a0b04060801090207060204030204020c100e1b0d02040608010c081e0402060d0509011506030902010e090601080117010612 77
    0x10610500c40c0c0c040c080c229058001c0c180c10140c80c0945070200da94804510004e0a110100c641101c3c811b00c0901741d011703168900d046030600242e1103914681901030401c01040b0103401204000c01c50b10400f8031001c00c5210341505100c1403281c0003809060304030100350600c501d80c40d03404020a50b000039140400480d03410103881e51486e003103d9001d2900070360000398090038101180e04580040d610b020440e405c1c04483c80c0a0350010505860f02c5409010203c00350391244010301c20a51040000c2104c01e040c10034800950b4040304000c16290846040c1c0300d02010500c48107111520704607001c810022040c070029008058541040500b9841d161508840e82e030004103040c002c1c1c8412130071410340f085075002c01941150864009410041c180111000c495654006940041c00900081409892081b440c0890200c5912100000b82c83d581c01c0c40039540c0080c0d82200880c415610120305e0b01e041e00c0080d004400c1031155070341c0c00c81502483c5151010a50110014195018482c03407540b000d400e1074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 412446321 1250 412445071 412445101
    0x7081801090e0a140912030c0f040914011e1511190605100e091203040305072f0405011a07080c010e030415180302101119110105041a0306011106 64
    0xe8902604c1c0303002003440e1020000d8405030b10080c00440501d540e8688500003910f8200144a845640c010710020800349018024a04050600c0700e410300650314100050311042211004413410050303426091001c1000b40e044501e405140e402c180806910417507072240b5002c078004154104030700c080c1c81001000301540042c1d005103c010f082c0000d07a6140c2d00d86a002d02401e90302c9100a5015151400b0303000c45035805183d119000e41813150034000181c450001307a161b00140d080c07110040755810030100c00e030981040c001c0701c0181da04008640c140040e21132206031f131f04090b10014402045c088204410801110b0050085100030310070202c7e03003e0300075980e41040c0500e40d58096950084036456100c3c00d41d100c1545d07800000361880030326540038021102d03100510b05080002c9030b00036043c0002c0c2080011000c4002c04e02d81400844507003061400d5007440503c080c1000342c104810000ba044001c1c003240d40c0308549151558a840b101c00581e080c103840050351200b80910f40400c441090f004200d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 412447571 1250 412446321 412446341
    0xc040f0f0e060c190c02060c010608070b0c0a151506030f0f0c0c021012020406120b0604030b041502090901030318050418031211130305100207081801090e0a 69
    0x8240044018808200e84070380b070454203003000d2001402802c1040a4501c0004221410750a0001819225030041880d07580088070346801607454401c00c1210740c500304207110050030180400c41c144a0320700003c0392201401d40010700000800070100810711400d911000e000b0180781d8541420641c1c845001e0b002d071202c0c200a598092901d2081d02040c0014010282056500d50303660110440ca6070070000c0151060b0400c8040141c444ca1500c0c14201130310007840542043c0d1600950241084450000e030340d450b064441c061040ac1c001007000405441c2d0b0300c2d1f04154840c010640030074a09583d600240a9440c030341760300c21443c10000081c143c1241c0c194840c003d0a911894000361540c00b4041581d00403840203205112500f4a440441e201d1040c814055551840c04503201d9121480000b250b04084520840210848420000c102c070030081d81d81e004034150019403c007865a11a5242c60080780182c8030b8186101500c5d40483c1e118901c260007800c02e200d98480d40c5d040000401c4010542558 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 412448821 1250 412447571 412447601
    0xa09060e1f3506041a04020310080f030703050a0f0c290a0603030807050c2b2d031e0f0501080d0e102d020a0b06011d010305090c040f 59
    0x1030800501d03500118400c10301e42c48508001090f192030041c40004c1030812440860010320041000d030a540d9030000354091b01008980c1030030103042c0000c15092070191814942c15910400c03002c0c0010b600034064800101a5040c50020785102440586684510340401071000000401805460300c000312034100008081c504000c40da6645480703e0102c841c1808054040f40142d80000c454900c900018150f55a60b030003070380c200c00b41c0040860404c41e0b102c2001582c980385c9004501d08990302203004896a5810f11070412801d0750144021007501000301c98500700340e2101c041542c2a45180000010b6110f0000c042000c80703494425140202002c0c042c01407540902c07112540001e1064840d00f003620b00040003c891000404c0050382c41030044200c40540c5000412115203d002603c000030034001942c014208000c5980b815203264a001032046061140000480055044443c424076480400703090004183e1a000202032030501e0340940e40d0740c800e080c0781001044a00d290400c0407945d104030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 412450071 1250 412448821 412448867
    0x1b1014040f091527150e0c0904110a081f0b0c0a0302010b030d0203220305030403030806011218060c03020c03070309051003050c030c07020d150518030a09060e1f 71
    0x5410018840c03400c00d26a109841c025103032400d0740c13003139602030112021110b60440d5419074412030044c0c19401242c1da600e0340040071400d0030050405008003124001464031282c034002040c0000740040704090714441c0c2d8400042d80c5103c1903d07000c068100a032426200880d21202c0340424030780d898800748005c034015420000102110b0500154034451039005401842c282844204881401e0310010f080a01c030481414000001c2201032000f080076502070b641b034007003501d04680054160440c04011800a41ca840f2042a01030141c5400301031231a804030000c1401d2085900840c041e00802d00d680046010000300542095000090202210021344c0c17040c3d0380700790150058080b100e0884040f0086001000050b201e0100c00c00181022803001f0030442c101c04040e102c00d07521420317030008450b150b6030b15001d003c01200486012100044a10000c502d0000b403c400140340c0880c0d0300c01d1000307200f4482c0010381503540c0c042034028601005080400308400d002e800805804240940c005081c50348 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 412451321 1250 412450071 412450079
    0xc050102070f0509060f061306230307030209010c0c150305090609070b0c120a0302041e060e01030209010e0d0605040311061e07020c04060905091b1014040f0915 71
    0x1003031071001c95040002c0d10340b8052034402031102c0c00b8801002e560380a04142418492a5500c07005400c521207003140700718040d0b060007806070201c1450280c03120142080c00d00040c11001c14401c82e42e100342d50745000358441001d800107031400d44070284020702e00d0300503241c04110b107030228582d030943c21119a001d2125031560040c1c182c03036450030f076458555600081c07028051b10138294014108200c81d0001c8a14403c0d450262000b00e070440c5072200002078000a08109031040482c1190b002d40e5617084040750b1514000c006030a000030348598a040c9500801c0c0c204580e070049a128030007140203094000c152070711f46040030082800b19411004142c120550007000c1400240b2207100b4082000000c80a080c070412641e0103a000424203c1140b20311a440c80c600c0d10343e40035030001062840c1000c02e4904000900073f04043d0025030709152030782440d84a4a13180d0700d1240400141d001400c011a0240c0182d40d1a074144c407903900003189c141ca4000000030305100a078000d01220102e0120142d0168075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 412452571 1250 412451321 412451323
    0x20609041103071701052b0525051801050f24070201110d12091401151404020f16050a0803090a0218060d17190203030412080f011502030f070506040c050102 69
    0xc01e000301038001c21fa009510203001c0e804640c4600703441c0a100c140d100c1a03d15500c2c03a250800341e0010b1a41c40d12904082c4003a0445c0c141290041d00d001c071203001d1209540d848840c9a64414810300c0c1c81900310220740810f0380c640510180c41410303a40440035906000706074019039640081c404a00007400101818106080428038074141d80c02d5998041d0404190328812000e8000744109580d1190b0070020819604824490b805c8007102c0c40c04030040e001d20701104002030100c18a5100d000d640104003014079a11004103c0350000200540c83c154480c0b5401e105113407400400d40202102c000009004600000041c000407031b910032104810104040680348a00e4001034551070b4004080b1101c3c0400517070401400105540c0502c04541000040c92022003410030b80441e24026070400403c0c84140b04001002000d541041d040006450420203188420001d05210305038600e2810b185000e0340394030a00440e101d01c40300d0841d4940750149428121342b2603009a4080b02c0a06071036000240c0741d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 412453821 1250 412452571 412452617
    0x6030b0a0b01170603190b0402031204060507170904060e09010e15190b21010608010e1e03070f111810170705040903021606050f04050d02060904110307 67
    0x200c10383d2031610004840000385107510000c1c0000d60706004812030180410a486118070f2990301030814410a828240103040c24130044400c0c4031200c080401040c03012907009003c40346103aa0102000d480c000c48000e140456005445031250b2003030604034001080c510f00c0b04441e0145000d60002c204e01d21107268220760700e0035071640040c040c210030303c0011015038412800fa10160000000450016446800a004890003c0301c540461010310942007007a102482900c0150540c03100800c50b0851410302c445d03842c0c805810034003041d4600030803000c40c0701042c0300350b88082d54480b4143c1c480c484249070040d0703104007008500740907056000d907071064100203520817809058140c0c0707510849402c0ca807814804240141110040b441818000501038030b551045042150095001d070680141e64001c01e80340c410940d00a104010741800b058400647c0359040742e0886070f084800000340c1d480e0f40301081560040070159640a850b2101141d04520f48000440c450346a40c1c1e0358901e094441046103503085 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 412455071 1250 412453821 412453841
    0x6030905060703110d0e0d030608072d080624041e0f02120f01030308070f051207030e15041e11060d021306030606090e070f23070606030b0a 62
    0x16000c600801c0c2c28a0280c1e0105626601d1140541e240a43e688020010b0740c8a9015050840e4403d0715082c007441e41c5482a00b01030541803003d01049490080396010689002c05075211511803034a0f004040102280103900410326282562040d2902d180400110f6210a10b41407801c1b1904034078100782d00d4940f00c1c180d01c40d00c14905a0044042d03030f01c07204004011084030003c4040d0f00300024800b40300c510031801d12403141c981c4050840d604511300100364607000f031700c56000e12210b1180c5180b4107400030161200e81030712203c0810f150f43c0354502240a40450f1051403810300a000700d03c505024148101446140954a10311201c039601c4003684e4885040c000c081c02c10001391500724441e141c0840200b00c080c0b02c200e005404c088040e120007082d151154400c20100741d8071941001069000311100008285400c1c0f4600e040c50001d00140620310603044c0d440800070010910341d04100c0c84080c0720060242002e40341e840d01132510b4a50300504460005030352903611400000e000004d28051307040e0700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 412456321 1250 412455071 412455073
    0x4020405010927030219080306042a080406110403030f0e03120f0d020403020a0f1d0c0a110a14030a120c23041e060e090103022107080f1606030905 65
    0x40340b42c40c500c5a83d4800e800c821011400303070482004226810260031780c455800b41d40040d80d02c2c01d049007040300321082a0103e050030219507004001c50305103540081c607081110f0400318200d80e030b0307483e0400003800c0c110040503010002084c0403081c190f02001c43c50010490703480b00707656000304004050f50f500c0e2982410700440350030011000c640d60400e01900500700420000b5083c55165400108520443d8101a038101e004040c00c00c40a0f10f00d40c1c4501140c02d14440081613414000b00001c0c0d0382c0302e503200381e005101034a000d2400c5101c2c200110311805070030002741a280646c1c80c080a03140d510101421000131500c46d01201c0f0101a071145c02c001d40e40700d40300c89900c00039000090407003104403d8003c48501d401d0100048c1011a0325124890789642420382c20f400341000d01c05084035000c00c022a0048004000605c0140c881713a444c000071000c29100840c40c0c0d0384002041d80f4112403508580741500819289000c039150000b042d4410b600e0f4000d50481907902c45a00310116040fa490141c19 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 412457571 1250 412456321 412456361
    0x150e0910050a172d070b040e04061107150203090d020616080702160605032409040204271a1b0f0901030e010213030308090c031c0309051203040204050109 68
    0x885884056940d0459860580c0c0d4080c21041880c03403185010461000003000341c400c41c9130002c0d0188042e50240c140030104a05042c14000060b51246000300001d102d1944c803140808001c41302030a4800d0f503607000707180041300d00c1080c00341e40180d001520102842d20980941540060000c6803103840b03000e006425101d9810100c0007260b2402c000340400055024100c0c070306202d120614660b90140c01d468644560360304080c086071488024003420b000c002d86113000305481581e00ca00c0000d4019030100c03000306c1e01403074000310544082d00700c031040203249950103000c03003c124858403104e101192004111500d80c1d5a10003241801e0030081c078410040c3e00821424030651012000b8042282043c540003174683c032038103070f07690890b0b00282d0001d0700c0c0c48601000300209948001040c0d170015011025002d40003013640481c1d90f41001480028807103d8000031284c0b09031095000c442c0389034100c000c60b0f8004014a4040e0780c20381c400c2e034081e400ba50a10001203184903d038060704460980c400c0540c1c2c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 412458821 1250 412457571 412457579
    0x1b08030a0516030917070e060909150901021b07081905060103030807090b1b0f0d02030409051e010f060e060a09060513030602030a020405030c0409020a0b0c0304150e0910050a 77
    0x1418141c402d0110148100040c011440c0e00325580c12001204c43d134401030001c50300b445965240070354002c03c0c80e07100b000c1301c4040100e0700da40404d00700c05c0c1c00b40b00c0019004644503000254064003a4259006840045802c03d42c5460030004c2d40710222807151058038040b01c1034504120301141e001d0310281c001e500601c01080024800c030420766102c1c0c20b174501141c0f026241d46003849960301910ba0380032030310040d04000c25644d80510841d0402c00c0300070700a2801401002001e512400385104102c2c0310303690f401c0042c40c0550081d59080c900f5208421095481d83c4407043d18130398150a0141c4000988c0034031144116042c104e00720340c100041034803074401c01c61030410120303404d6001d04903204e40d1840040d000400a2454005503006000703032080580c4848c200300a2525055015103094411070030400c403070000d601c0d44821007050302c03180f04209035556014401f45240d445035a0203800b20290740001051415881914036559480444081150b034540d01460309000d0420b004440e80a041800d0802c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 412460071 1250 412458821 412458847
    0x50a05060d021905091f020601140411040603060f12050312070215012d1406031305060702070603060905040203060621061f0e09060601050a0302040306091b08030a05 73
    0x401c84800c1c14402501d0300d100455001c1ca00c81c000700200001c6400403406159501d8150207014042602c10340c0112071000d43c2c0700003540c0d07180601ca100010440c01e041411103440b176401030391800150141e010390312951070a008004003501c0c400c2c0144400006000301c0c10b000000301c4201c00e03e8203c0011800c122020b244851301e110054851425841114100c92500c0c2d00c0c4003120b4000d04040000d03642030350100c03883d100c003031058804100349031070381101c18043c6403034600041c00020301c1550700301d0304e03655407150110f0540012a0085d081d0710130102001341b00d42d400120f00c801c1d036010303517000c0c44801c0d0740e010140d059890580300254986c000300b0000780607040c04104101500d0b501d10200400c0c5a0079241581080400d0300d103048594a800c151701812954202080d004000b03801d40c1d200d1614002e0360440e1104005030040d410000009245851580310f601524065a0081c400b04030a4000d460200e20a0340000080b45403c0c0700a00005072002010003562030208040d10740e949400d10007500300f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 412461321 1250 412460071 412460077
    0x5010c050c151c0c110a0308011703070f06060503010b0a030f030e06090d14060f04030c03081306050903090315070525080f0307030f060b0d050a0609051311030106050a0506 76
    0x68960320a040c441c200b00d20440095401d0b01e9014254005104c0016160017444001c18440780192540100100000658000000f604403140840114141c40602d55401d04511511401800c580024031454041c090b4640c0403a003107a41c2107000300b1008442030705210040c14144400b4040140d00c401c1c0300d020900400107102042d00c01002c4600e000c12440010309866001c0314152203104541d4004c05203900c00700a650b0308200751500800da140740a40e0001c0444020180007020030907407202085803401c458507000a420b920801c2070040d490083c0c20240c2c0d03074000f001024468403d40c41220035485090005074007400b442c0c2d4070700c0c0c6000e0102d04a03184420494080281d80c51d0200d100c00c010a1000019000c511608540f2a0340ea0418200080035a203d240303d00070607614041c0704200c031003c201c0407680311a042043c0803c40b40d4440c410340d001080c181c0c1c071040b08181410100104c0603200900340c480e4138072521600411450540a0608a03852800b440c0d400c506039075018446440c0103806 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 412462571 1250 412461321 412461349
    0x121d01080c0706020a0e060c0106050418020603040f051204060305041a010b090d02030309031902150325030f0c05040501120209030a03030b030a0f03081e04020d060c0c080f0a02010605010c050c 85
    0x106c12840202c180210300d403584041429103440c0d649010034000391400380030764629070b610b90031080031074151600000e00d1884007600084c09240080100d42c10032038140b02d0000c03038507002c01040d900c4943d00c24002d0f000d444200c804541c2641c0c00c003440a0100304000010341030700c0105a0b004c4c01c0a500009010f40c0304031182c401e0b42e2510041c0181852590100720a4883d003400402e165a03440c1c05206203d10f1820041c0032804003030043c020072100d80160020f40c00c40101c4406070098032242904190002d001c0c0356070b0400707942d0a142d586810300c1d40000013482212030a80c1c40c640030074070007026031040303004091f90294103801030008803002ca846071700104c00083c802403d90341460510b50b40c12400521201048004c15103c604107c0707410507400380c10a2141c010a03a6403d586030550010740e4810b12001e0007041503903030f03003021003e0034810001810303040d5000280c607a07500544409510350f42c1001ea601001982000b2022913154840e10010003841e5101c0d009244c40c8100c901000020044885 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 412463821 1250 412462571 412462577
    0x23030109050121380a0606020705030f06070f03021606050610090302010207150201020f041401500f0d0501090c021c031103070309140d0e0d050307121d01080c0706020a 74
    0x71060755200320366540c5010f00c1110b0000100d1b18508040623080982ea944414840e4005000241840c103001c25001d51103402072070701400a02400905800038040d0b41d00504079100e680040604200e0140e11a6008903011103510615855a14045411000600000340147c11441040004000944540211450500015042114041d00c8194582060707211000440031006d00220035600080f0b910513010300e040800c010070007004440200010780c045280c0c03002d20056540c1e07203c0c102c0c0c1420f44010b801ea001c4131607558a080300070b101140d080000301c800c04c2842d0600006160000384600c040c040a690060080c2d80f855407800b01e00040c030080c1d500240b64890300030700074440c4141d0096210b4102038400082490040c1030480304109007075042c122070b030700c80c403000c08000e07800c02d60100200c00d048544e00811506407502e0b50450060440c02071042c4528044222680d03089220305030385d8003c0c0c203c02e0181c1d11170100112664101a03c8440050008028980c041000c680040080c82c8442c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 412465071 1250 412463821 412463903
    0x190e03030c060f10050a060e061b0609010b0a050306040c15030b0d03050d0509060114060d091704170304030803070c02010e0a08011a010206041223030109050121 71
    0x240c105400c1034400c5030300b03140e1040c0001c2084104a5807111030b9005c0e04099032010141e81c10070300042d0240b103000340782e01c4c0301e0103000c074076050791040d14040130481c000e86400f0303111242048891240640000c060003440f0701d84061020440382000202d0501c55a0000501e0440740c1c5800101c005070803d00780c643c4201038960b01140919114200c2040d0000e01c26a5460b0381d03603100c0181c02c03044480107002258a078000400401c600c1001040120702c2c05011220701c0c0d86c03002001b0b0300000a150150b001030200d214400703214803494503800600101c442c0d06e10302d03120307078100d4070092500c2c0e101700d00004154680604c085411648030b0781740c80d5105ea1041c1080d0421942c8400000c464410a0380301c01c01a039150b40030055940d01922050300751510a00041c090b904056031418050000588004204a030290b1600641104807500855070036058101a560703507110300722007020700000d0049c0c4030340004400307178031981d40d0300606030b484a0764201791354880058481011200c500e22040920000c88400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 412466321 1250 412465071 412465087
    0x180c05101808030a0815030a1202010e16030201140c0706260f241f020106150504031101050f120903040b1315050903060103080c19030c0302060a02190e0303 69
    0x103901141c0160080c94003c0d9152610440018110f45008040c000740c42c203007000303072140c907200005c0f1078115590144013801d290a0580c070803030041095a6a0001c140300b0024412500c1c0170716100c1e0b0301900e000b0381e209044001170100d514180e20a81c1c50001d800c0d48801400c011039485501410030b5010f101c2003a400c001544022800c200100f81c800a95100041e8148041e01c02d44110052000166041c00c440485820300000c0c1c0c91441d00d051102c60f00000c82c90302c1d1041c1d00c00e601c5000902958001da080c14546048000c01c280c0040c00b003110501a06988a483c0c1d41c0500142e403480040c0024182c81d081007800c0755890383c1e40152005103940300521010a543e000500603100c20448100441562481e1004147e4212060040310741840710420411444c0e4901007590b90540c0e400c00c0303072107503511504894285402d04141081e030a08000f4851082015031158000c440300c4e000350b080b00c0d019100e03124404124800c0c00500d00c0d1803605449160300c0b13a401001c0300b9960364001802c1d64100525 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 412467571 1250 412466321 412466357
    0xc06081b0a020c040f060602030a05160b13030f03060e0103021002010603061a0f0907050702010810050a060909150b180109090f0519051003023c04180c0510 69
    0x3010720400050380041410602608103441003081036500c140040c88150300c1c201c8003a48070311804c0c40b500b00b0000c00140d689007844282103c5940e1540c41040d1b00000d01c2c0040b2040f040b19242c03a4214001403440ca03194a07a05c1c0700b8050803003035500500c8041c002c0d92855080000040040c0701d1101555211180080820898031988003203610711104c2460280603d020016000900c3da020781c0709a0350f101c10310210950010a803852141d0a0804664507250340742440c152003c141e00003607100c00440c20104009610070502d40895180c51401e01c0f5a0080115501c007456080c000c1c03007044403027809540d40c22440b500e49040c0b200c00605020043e19120385001051350b40e07010191500303d0b00d42e000c0c40311640d203c010306d9901a039801c4040140d030404902149003510b582c88068400c072521442d07241a00070701c0b10120748441c0c00301c800c1903c1ba007507040300346e81c07000030091054802c3d85042e42d00400e03c041916640c048a9001c541d13880d030107085c6000c101d80418003400c030000308101000700c4001455 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 412468821 1250 412467571 412467577
    0x170106180209011d180906070210020c0a08031008060103060209040e0a0314031f08011a03070e0105040911180a05011a03010902131205060609070507050604020409020f100c050606010c0c06081b 85
    0x1b01400c05007074a0b00c5c1000c070107403405001100241c009171040110038900d03040412070b000126404185581d90351142e0100c09000307016900518058002c03100004108000d0307030b000708a614015a001d00121141c604800d888000c104c0015010a5141003650b07015220f660041d98800001c0400080066814021482c810780e960040d6291369590604840c0c101e02802464240070700c114001d002d41c500303112500083c3c54041c424540034a44456040c01000007200100300c0c1500080c080c02c10054003800840581c08080d24400c0c803c40c500000800c69446184d0300b8000c0c0c05084541030300c0c59203401c01110003035220420700c00795458000700c0070400d62040c0020416142c0124000c00c8a401c0440400280f0640039001c0e03001d0000400000300043c201040090384181c048030f00256084130344c00401d0b0529401ca81a9500034007040d100b100e03683e0041c19524200d40078400f100c1c8580d480301c00555060400b988040c0c0b8080403180c08024881c425201550301243c294504440808003a1170282160 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 412470071 1250 412468821 412468831
    0x6160b19060b04050a08070b0a0c03030f110904150617130b090d08092e110d02040608090a0f0209070207080a030f1101060b030c070309170106180209011d18 69
    0x2e080090b08020030301c1e118040002500700600681030b1180307032031101c2c40d66200c0c031f8052009210120054006050080d486803080504025041c801d100c040c0142c140598440b11409100fa89000301e007825660381480d80d0802c1c0c076565203802c61040c41500003882c182c0001403c0c3c0780b120766150b403400c000400240545000310781010062814000707180018001100040009404d1f9004c42140d110f2110941062101580c00c445803161102c50300460a004e88049461212a50703000900e040785001143d0081c800c840c00c5035644030380c0b0b4440300d006a032502e8107040c1c081e110811a5110748090b142141c2e0850f00070003240101d80304a42d40f02006030070140e0500058010840c0540c2ca0003100390041640c0400032002c1c0020000e490505000132254040500034820084e404515182014015140b44000d4044c05420b500c4100540b42001c0c00f82100b0f01402c0d20348401060f10400240e482e00030b0700e8041d5016141c407110f0205141502070540710211740c00398001c074080031790303c0f01e00407800c1240c1c055 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 412471321 1250 412470071 412470089
    0xc2b050109021002060c1c0b0907090504150513110d0e06010311030a0c0605030c09030703050303090d09030c090f090605090706020d050c03091924030b06160b1906 72
    0x34002900402c0b0480c04100d400f041550480030800c1003000c107100c2200d080d156106040350500510281c0071005003121003105400c240701d030b170901100503080282c00c401c6501c00c81d400c0c030102d0703040c1c40d100c4001c9500e4856103030801d8618030040e110400e0b80e00906134540e0406ca61506020950900509640001112940ca60001d100600900501d410b0305030310a0340503401000302c180d050341d405c80811a10b2055004124010000c5103809004a00300e81e40e2940003400c0b02e0034191a804c3c4035440c0e40c010b81d1100b00d14442c80004805040c018a2482e0859410200b440103403842d0081440c054a480141c0041b00c41d40d98911600103103c51003454000c0203100c00030103101c1d0406402901d8a01e03080a12010303c101031040110769080001180e0000e0b200762140708001c1c1400b24403203441e8029030011826007070b1507600344000c41070b40045111014000e65082c04495888424411103104098107001001480780714034010401a0b9400c60700807100d404620190100740d051002103030504d400c41468 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 412472571 1250 412471321 412471331
    0x20903071701060603021603030b0a0815220503040b0702010903060f09021503060d02041d01021908010b07120518060a020304030203060916050907030e0d08190507020c2b0501 77
    0x1c4142446008098001030508500e092010714107600c00c5016a9801000c258607070500c5006034030340c80030f820001c3c080e0030200d42e070040345283c0170041c500080380c01165041e208101c6c645a01d44000d414542150410055031034541060f554076019400214240c1c1408030407800000080c590384108150304418100004141c0040d104100f1807503e0f045a5540001d4148180002652007040c0132800b1581124000342e044452800302412051114450241d5403010507414070380e9209a1664005844940d00c6090507a203801e51414207009e4800d0103446011034850341320040340078000510102152031400c2800c0c80c409800a0050f510486110300140c002060410841c2020410b0a0300044558080c00c0144652400c0d6404a9000d1044511074008080441c1c0c181d03020b540103818120711903050f02c0003024194005001e4035400d943e00e0344403240c62000f400003d50603108041c042c0c0b00941c0a094410600000c0080458840851348a4201c03003201a1304881c0c0707000c07c0381824600c14000811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 412473821 1250 412472571 412472609
    0x80d0b030a0305090102060f06090c0703030609020a181508160210090c0f05040207050a02040b1305040b0402090105010f081f08031606060b07080d0f0f051503100b0f04090602090307 80
    0x3040c007c1c060011501c0c041100c0c10b06c03c1c00c2d6501c80103240d125843d0100d540e01c43c0c0c50313804c0c103c010700b05a030f02084403a440010901d44050b0701210111074191403100d18000070341d841c03e6903001185a032040c0d000117242080420200044504021400310710340c8100c1d00100840210041100c468050131214020164030070040480d2491000d801000115006c605120258480f552100c0050740020701c070380d540d403803845c2d89a07541c4040300d00d0254008400304102e140030700c4c288508400507182a44145409000000c40c3c0d8070030000c0440e081c4203503440c044280c4400e5644d001011030384003075003403041400001049000080003e40402020341004410009603800c102d4211401c580100f45000803c02c800e0700840d00e07000807190074900003600025071440420980300202a13040f400d400d007a0414091280c040061981c10000304002c40540b03080d0046402400b0481d94004d40043d04141c25816216040c075055000c1c049aa01890000d4500f03084400020705004441d000703503042c83c2803500045 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 412475071 1250 412473821 412473823
    0x14100501060e040c021b19080106081e2505060a020102090913021f090320010807021606050903010f0606020f0c06030f010b03060f0301050c210c07080d0b030a0305090102 75
    0x10803542d03003500d0800c40216071002c025280d10020f00c811900c2038040c078040c01c454172a00c08000040401c03603000e1541fa6100c0030001c1c040c2a083c41054090320503842290786180d44401443e060740e05d4440200036803d0040c0f91042003150384596414210030300308000415032100001030111401d00c0e800140d4814403070041240007040500525500d0030700c281020010384900214004a120a050902c61000380000440c3d00000980008200341040580030358050416034404c1c00c40c603000d8075180000e583d40d60080b80d8607034554031280c0b03200c24030910822005015500031320b60701402400200d502c9500603d1a000d0b100c40f644501300591004480e4070a201080c42244160041103030000d1641c10100e0348150001410b01440c0740751100080440c03c0340da07849032010100b040240080c4030914082e0130240f550b4001c060682c1030300158240300940c07801c502c12003e02c1303240b04501003800c1001c40d0319402c40f5500480400708001e5501c111000895604214101840d0300c1b0707640c1d503681d811040c4002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 412476321 1250 412475071 412475087
    0x4021b011104030507270f0c080604110d090305070804060206071101050423030702030706210e1b061b030702010306140312221226161410050106 64
    0x45800c070003060000340001140032864004482288200e00903c010070b00917000507404044a01464038903001100c280820113420102c00c000703145d00c410b5880c3d1b0b01c0406200c265003504520f010801010800d0503080b42480d0300c42100c0328064903155050000c607a540501c142d115410440250f07100c2c0007044003259200d4102c0c007035a08004028232040c102a0f07110104008110450121001003510350813441034100181c80b902a001012038009aa4410000e810861841d015036802d603410102c1c80903808213070142101d02400c03600208117044040f0301100441100410b45a48060b007001811000e5107c00000c1080f0000d06018560303400840c03001404503a42507210511518404004295596022130014842e08014a005a980d42d41c4512186070038000e041024a9060010011070080300800300c02803004e105240d0381d201030365a50304034000d200c102e40851040300d90030845d0000d18802411f4845525100f003020001d5880a442c40500b0141003540c101c4c070280c3d43e0801000455440182 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 412477571 1250 412476321 412476341
    0x14120309060108010c18120f051f0e0705030606041d0a200109031a1f080a060e0a02060a05091302220510051e09030d051c061d06010e04021b01 63
    0x1000c440c5030001400c0300d0140902d80300744034021f41c40030100001d0214600201c2c00302c55210040d40c810b060a40390088426400e4428038502c9450b080131f0004a120014081094a00040003454255142c034100006401404030311002e41c40710308115030b0804000c00c803c481051081d140c42c070845000c102c405401c60082c0c01c00604001d80d03d0010000b1864610780407100910035014800250b840f028001d5240548103500d0008441c491000540386d41cbc00302d901e4180a105480900880001c4d002c4696201a02d020196025074200040412076014800a1010f0341000d8021035202900c100c2d104201e8200c1000e100605000c20400a1001c408004610141008803a56201304490001c010128021181c00d88010014444181544c054120a5a510000041c11602402c1a04600400541080842400d030702c2d12110754241e000b19a00070002034809a00d5006a14000c4071502030000c1d40203000981030210400302e814164607240000c1c0551000d01090180d14400030f890f4500311045518 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 412478821 1250 412477571 412477577
    0x8090601122607030224040b180a080d090c080706020309221503020405060a0e010909060603020433050d12030e0d032f07030503100e10090c081314120309060108010c 73
    0x1041000142315262020b42100306074803003418034020000701500d8070f01d8031200580005030110f905a11380c4e0650b085615814031a00550b091560f440a0007a990301e454010600540c1060200014900704001b0312886402d05808101100c481582080100c0380035101c50000d1103040071090056043c24042c42d5001001640c81c1800b172841c1c043c1c2d46405501c103008050300c0c01d4031081d0305014001c0d00d82000c0081c5d50000c0080111015500c5900308074022224403140d00d405c15001d094404407503249243c12601e015118241c2038881c1e0760b41d12a00032030701c0207240c14140d559090340e28a4030204034454518080d514006100c041965044590150b055942200c6907804c4100c0200149258255806180d15003131460701c9840782d03420b00000303205903040350710021091803c01140541380301c8203030100c442100d010011005070321812146501e00711111300b02c01440c500c00000003040c1a400681c518003030410355440c50703070409511b420f0f507100b174420301150381c405801030022308400c4c8a030080c480c0d4981 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 412480071 1250 412478821 412478893
    0x706030b0118181a130b01030204030b0c0306030c0d0506010605090409050f0a0203011505010504030f080702060c0d030507082818141027050309040c030903080906011226070302 78
    0x400083c00c49100c056038504117640342e03114900c40e0303402601178030b0203144d1050645000f45081451031030a0b400440341d443c4079120304404550300d42401408400e01ea504400078200c00e030f08154080e51140e000100443c3c00c40d07541d0395080c000c03600c24800c10400c410504050700c0010b030940101425515405d8030104101c100070320802681e82c004044034202c982c4420380d0428a00a41007000c0a4000c81e200607420002c0054004002c140224440b803148403280c80c10812529a541c003110381788801c81c0c0c510880d03095407446c0c1c0c50400100c0c8428040005068000c60060303d000480114414409003c44aa184042061044a1003404414004007078580100160a1101c6190003800000c14854030546112804801400018030480b484540d000d0400e100403000050b0007801480c0161080c0c0005203507001080a0354000b0075180e04840380c880705400c1d01d14460f2500d0540450035003103000607419030716450805990080c040c0141c04d019070060303e00c540041100142c0c8039030702d12903803a05504070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 412481321 1250 412480071 412480121
    0x10b03010f18090804151d0a06050702030705100509011d0321040f03080409140c09210a030206070f0c0f0f061d070501030e030c0706030b011818 64
    0x110744000884454403003403204800302c02c40c0200200100b04000e0b201c283d001601154811528840c2c020084040d070701c42140b41c55910a0310003441e68030000b84c0d030104c07100404126451060000e040820300040c1503d401c00daa420000b844003403041c0c00d030004a803010071070340029a08048901251030651b12551002e507480300019403260785200480a8901c500e5458500640c03002003a174018140c9071919038003503600c074241250140c025116400701c0a0801d50504003030120080c001d0b0180090740d4845003819807101c104294010008800002d004540e5105800c12004000f40d00115001350080c00032410120401001110b8045e01c00042c02440000c9030001080340080c640740c10380002c3d10151140d900d1a00e2005170180001c4612180c2c1004541544444081044000c45100340c80400c02c910204035034548a0060401d40409600680c20030004c041c0039030440c000103d4140340a030082c8030b44080c0c18800d0001078001c000100a900c0580a0313042d0716200b08042e101d008130030510134001c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 412482571 1250 412481321 412481339
    0x503010e0a02030a0b19060603060302150918090c04020d0203040606061805010309030905120f0f07050904150b060307080a05010f08102007050609060609010f0905060d2009010b0301 80
    0x8003103002005c3d01c441400107914880030244041b100050440c1c1401815550754008025103510301040e88201d51802d8004a0f84060000712000f0311406480c411600317500d402000301910740180069a42d015901c1050391541d640d1004280c0a035100b031006840b402c190400b10f08603861a0040414040a00b590a45104038164080c0448009280100d410b441d586012900c000301030b400789801c4030040521a40c40318000c1034100d100c2c2c0c0e403038046035210460852200d540c1c01242c4111a00710b011a40800c003c281c0a101100d8154820300d004900103610401083d00f5500440d800000036018406201c1000c03010b000b03980c014040c3c0502540e076281060f00e8541c845000c0d040300d40200d95100b42c4000d5401084c000c0000840d6860004d43e01c900e0517044c034544401c412525200030340152000103100f0301c1c1a00c0d056044e82d1041440c84403030307400c0070310503801800c01070f05840c6d015410369541c100041c4042a0b000b0144080074250600c054040240600040180c102784400b4205000501c05110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 412483821 1250 412482571 412482583
    0x603221106040e041b03080d0f0b310507121109030619060e010302060f07030e03120a080906010803040b0336010b04090201020316170301170f010c050702061804150503010e0a0203 79
    0x164000000e120401d01e087e441c01004400d000752f810418207402c1408011801e2a0810751128400f41441076851141703400c1d044850846030240841c02c1c05105040f003203401e40c80031b101000d808240d60710780380c081030000703252030000c0f541c10607803a010200d07017080c1811600400b401000030004480240d415540014140d0240001c0c480320700c0c401252103418148515100352050501500b035072400fa0343e000303a40c4a1540104c1c60f4801080c0c2c141702154210400042d01030480758814061400c080c1803210102140d13201401c0c40c0350241d0034452a8074030184500d1021801354040400007090000052818207403100d401445108514240280300940d03004011a500110b03030389100090424145040142440d810040d0110ba06000c00046500084071101c4a07605c210001180c843c0c420071a80789003a190860404000260140015401401d02c10090810142caa80e81040a40301d4240404c00310781c0b00412030008629508010480e6080078841c0000551141003e040310442c03980100703075520 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 412485071 1250 412483821 412483837
    0x1030227070e0303070c030308091902090c1e0c010b0907020c0f1021051812040902030c09040f050613020c151e0103050a0c050603221106040e041b0308 67
    0x1100c800700b40255582801100c1020344c0c00400c0100554407810b004001c0340c030490f440c0204d441103d0294010345825110340004a80c020101c054550b0b91002088880d008640c1030400003880031810302e03280402001800d404001507000103615103414040001103503001d021101550402000c001e082d0b100c1c2c1c42c0c000404a4281c5842d90300d41c41d01e00b4100c40c0e0201004844400c0d5035051800c01241d522608018011081401940349008040c0e0956444500001032004c0041080008000c040f119401542e0304c5083c2c2e0381c5281c2404011004942522078031525001c2c565912000c219440c0740c030b4180c00418481d00f6400310300b08140480700e0f40d40c3e8036064440151484400740040c040d100d012843d40d00760000c0c14000c2c400395a50b45000f82d600d02034100119503041c1e04100200305410b240d0306491042443c200c8458082d110143d40d402400c16104090b035a10206c0c91100c0050386a0000800060905801160451030281004200c0705145141c515407004051070400108001c00e098481d49 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 412486321 1250 412485071 412485077
    0x20906040b09030c0d032c2107270b0306070f1215171c090e0a060302150301090b0108241f0f080c090303030f1003150501080d0906200102120a050103022707 69
    0x20081088298270f80300c070550102d1840e00294500020b60342c2c001d201603100140300d5200b409045503d0082544500341128080000340c4818008442c2c2803007844d0461100080c2c0740001200c4100703805202041816421180c81da00e103068001c0e4142004001c02c01003440c00b00c191f250815299440109070950b20301c0b4902c0c50400520101e00e814245038000c100442d4000c08486002d403000724009056003092080c840c409192014050355035003e0400948118007040900010795000d103030740b41d80f1601610920780c0241950401c864220f8007038103012212080f640b1107001411404200a094460050103060311203810721040c1c0c101e440010070340303800041e1140a50600c0c3d036000c043c0889244241c2c800303005030308001c0c00f1000202140d170050b030580c1c083d5810342d0070001c00300c2400d54a0f042540715200000308180c00c104501e0304420503064511808200261802c10360601d40803502c501550301d411515524401002145041600450a2a400c00426921003031410f4400004074008101e0828 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 412487571 1250 412486321 412486369
    0x209070e19180e1515011b0201050306060a021c08090c060f030114130213150e0d150b0d0c05121612060b09041a0a020906040b09030c0d032c 62
    0x4818810700a0004d4148800c20403441407803c469107001c0005401c03030072408640a2101c500e182e0132031260300340300703030b601a107405142d51585001d001d099800300c031203101140104d94000d03800c51150840180c08002558520159042c482e03046410702c08000c016a00c44c2c40104482d00c5184030381d8041da0304540400f04070740f099003c0f090120303c00b02e455940c0c0e81000ba2000424000e0401030900d154145da2002a4246070700d09008401c0e02e0240400c5981c0b5400f41003020507038009000c0002d09256005030b42e0010035211001c41c04201440008401100d40d080b2192041c40351b0301344200320584c07604544e802061030b810501403078104250240610700602e01841164000c0c0203458101c45501080a0b003446160724003424050380c0300ca0f80519403a00c0a426102007000000e15009a5900c1d44005009510f4a0302e024605138031584070344c182c10b416010340b00744180365940700074a21800074000d442d9180201a001710100303030000c0504402203010101c007000840c40d01c824010f00b50071b6101e0180c0d010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 412488821 1250 412487571 412487591
    0xf060c02061b030304030801030c050f0102210409062c040b07081b04031a15150d0b12031b010c0804021306150c150c020c090a06030209070e1918 64
    0x44003107148441480b140b0000003804101940f25100f20b040300d001d080c1094409449408100c9080c003050a03541c0107901c0300c003210340803940000d07480400c01c00d41424280f03032503680c1920310107490b4590301046082c40c2001d104842008003082c42c0890108268502082e40b0f03107980c0d20000b0074005450902004020800103002011411110040c0c040c554001c036107451303480c5003001d4101ca103174900308080507030344010805900c94034140c81d803c200c00400d202d000b0708018075000700c5500000810030700036880344000552070701d890a011103408231b040003565444070101c004c1d1012400041d86d01302030780e02d4180b03580020f81d80a26040d8200c0e40c1250b400c0040090303010000042c01103074001006880d24540100105a00000f035402d90f03500c189002c185000340d510300e580495a13004030b43c0c07000d6017011401e40980e1400400c00c550200e41c00000141041c0c0341d8004c034a07406421038041c4081005401c050340545003910f0910b52142021886000060615482c84040e81241d416030f240b1584810030a8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 412490071 1250 412488821 412488847
    0x120302010b04050a05181f0209150a030902031902030c041d0105071d0301060b03060603060a090e100609050403020d0f111501031b0b04030f020d1a100f060c0206 71
    0x20404580280305206500308403584c44000c21055410300400841010041001071021401080020021051034403c0d01000170b020081c0d403001e0311007540424040382c11140140c946000d04131001140d034001807070381c64907c107246c5010442052102e450b4083c0d41480c0040e030780024590054a8142c4011410041400034960818039407500c175802942040204a4450746c4001c40c00191a00e85041045105500050500700c41180c000d40c1c4600c42e0030000200a03007842c100a40c0c000d0005840e05119513510900e01c81224221005800281c0200c0880d40c0815407a000d0f01010f0041a002040141000d64005e5583d612001141d0103000b182c0501201040c0100b14022403800100e054840c0b030f100b9101c109400751000d00007101d240305814600d0381d04050080488080c1c41e41e00b241140b81c503085444030700c50b011042c2c0d0100c0e8003d59024254000403900d005061f03046500e80005045410413040920300889142c000d001821030005040040a91100e042d11030346070191b400c1941c07036a02062403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 412491321 1250 412490071 412490081
    0xa0c060519030c2a020301050703090206070605060117090102220b0d090602040f0b1e0c06070e03030f0d0911030102031605090303041203110606014b11010b0d0c12030201 75
    0x343e80d85482c10484c0c139190522402c88512020f01c03c4008006a550b000c0003981101c40c90640039400103428826100003070020360100750880c20504255003400c0c1009070b10700c000701040301c2c01003da03500071540360014209000d04107200c0d6000b0343c0060400b401c0c004640201e020f04005040f40d152200c140e0070a028aa5040302e01902040140545054640701c5058880e44105600941072400940b8514407540d44802da030025961080601015190a08215004501416401c0e0300d4002006801c00d2549960020107039650180c1c808143c4000c10704001e12000000f080c0d05000c0e034010001c10990316a88461aa80140340c0c1c2401500e40c4c00c40c0300445e20754041d0350411080d0042102e00c4100340f5030800b80f43c0105611180031228039584400046800317a201548501110400c05040305018807049c0b0290b401501d0407640f00d02c1084403200b9620101c440114410200e84800b499040141c8280600b252041099825900c4410181c0c2c0e00000e0b5100d9204d04034140d030200d0600402c05100703400c0307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 412492571 1250 412491321 412491347
    0x90e062a1b0609070e0f070f2d09061d06030f09030d090c060f0f091a090405091f0902150a0203070b0106080105190b25080301031505061002100b0118080a0c060519030c 74
    0x501a289580c03c2400383c0f99076603d0161a0108800d002c144911110785901000cce20480a003d43c0e0468441c50608110040d014002c00e06c58042030142a100c4032447c814040b059001c0c0c40c1d0114039518008000e000e04145240c0b110410020380400c1700c81e1500256660200d81039841c48125061281000864502519105a40c420308060a11440800004401068410444a185c02c944103841d0369400c590384030500039040700815800607070310440140a00122415801540c2c030704200c13070b5a6030801a030f00760803110200d00c4040040c4050705040701005103140c1022401d902c1d00d4141030540882e40541c00d0010704520780075020b40041e281d102c9080d42c0c2554880a11a00e0796100d1520050900186071503010903480c10001403403a1525003003005c1c0da1145500940441c61120400c000036009200c5031030305100360158491140007080c3e6003403005040900207404404980d107021200302510f50300203030400200303015034465103002c07071a0555079244d036060003c4c1304046044280c40e03100d46500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 412493821 1250 412492571 412492637
    0x1031101110a0c06030b012a0c090c2f1509010608070e06010315120f21051c0504150207110604090e062a1b0609070e0f070f 55
    0x26102d01000900f40607602a03880c10749080c415522400c004442091a0318451502030141c0c032102c100d5818049203c562042c0205c0c00d5001040d05d0340d030038406840b40c4030701078030001d07409003816124119140c407480348001019001031010201140390a030744603495041425036101842c042141410254000300c000d11156041d03030751860b56071041c2042114122521030100b8100000d85181040080625003501d03001c40140603085040c1d103a034001d101000d80100c4920090b200d24020018400f40700d10a8900d0580d00c081c1e0702c41e100b14547c2a415503460342c0e0440c0d90309041c1400006009681c2180991701103150040c1ca40009003040005e20038840d2050b50488400100800d001820382c104a641c1c0703100748201d5925459955001c1481c01448010824a00c0001d0007001000922001808103009240d894000d1410026644c1d0626109644420599001b400300300300c01032205c60038a500c40b2004448034828a8070320006450a990001c40004001e2039504080c5032440341040e000400d80082 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 412495071 1250 412493821 412493833
    0x90a08030c211f180f09140709140106020309090c0d062d14010e03010b100c140303040b0412110a06052e0b0708041701020a11010209090103110111 65
    0x600444a12802610340452103076140c1c4000359001020300d0310904960500f8510340741e2042e034004c10402020401d40381c16804e9103500b07440b0041400c90308503051800140340607001e164609000314013119611468008850350003401042a682c011007542c581c0002074400f1621595002d655070098070401341e0000c030072468610041000800c006030304c03401c2c40c4001c000030082d0741d030400f140138100114400d020031307181c0000101802c0d500c03c2959082d06030300500007040004025000034046c20b100d248400010307140101c601d084c02226107203514558465401340d40340d810651505400a800184040d0007601d02114076644144520240110218464207a544107905847c000026003000ea40495400104294511a054000041c8022007403400e0020b82c10728074241003225603411205c1c0546982074203000019003c3d094802c1003a1810700c0c4c900050760f0f00c001090180410040d48a4080703140e10506c00c03c10710341c8511441034156608801e11070b90700f014550048405144c0a24904164003641b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 412496321 1250 412495071 412495117
    0x15030b0103060501030b090a231005010b0c07061706310510301b080a05060a0203130f02041b05090405010e04021f09120f0302070e090a08030c 63
    0x20360095050b07030310a1461131b0300da44403001d40c19598404410050b040c3d031a0118403041c0c010704840b402a500404500b40c4259a42549086040311400d1303001c04200310000071007009400d01803107040b000d0405420103050500c0d5400d280c3d5207016008182a008404c580b074180038500c4c0300311102410f100310442c40c41180e170541504901402050302d034011048001003010800300c2000d019100c00c050354402100403c0d01c1d035a40001d00000c1c5800030780303140820015030170541039500383c2c520141098900801d03d410081c2350061070800028180b003d010304c18408d1050300d80c1790264821002d900700405903410401c9000180050901d6080049030b40c0192118160a5401202409490b041110200000d0385c0e90034000d00ca031502102c1c002e5110545000c1144211150103121104007003d00d050600b4540360500540c0043c4200e200340c9020f115001d80d5810580c0c100100c030080c0215030307016403560501c004183d03030321408030318014601900400000c15098408007680c2c0c1e200d54a50307803036042c0303209 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 412497571 1250 412496321 412496333
    0x510051b0406020309040528091b031a07021504030c0c23150415051e0f1224010e06120c0c07140f010311070f050618070e010915030b0103 61
    0x70180300d8040e508060004800c0040c04952803181c07403130481203013480711204000200030240c000040b9401034094412b54026484039005001030352048144220200105401088180c1e00402100c215031042405041e4032401ca224030350002e03818206100810101c1c0b60aa00c40d5105401a000401c0f010001e18086c100e040341d1030312401015640c0b8a0b03043c1e80a031a41d001423043e80160344111150784003400c03e280c4161b000380020070499080280448682000160560018a1100074140041a05e41d038007480c1c9002250050035040711240c603e80ca411021420fa4441a800340c184000303020446040e844100c21142c081100b0350302d0032036a1400c910348000540000e0071500141c40713030b0300d00440c1c1c01d40306080d440c1078180020705910082c0c54600044014040c60011000085010f00c040000202c0c00300c0000c4403107128402800291821541e15020088071401070761035507101030420840604010300444c1540e100d56404a20980380114000d10040b07503510060001807004000418014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 412498821 1250 412497571 412497577
    0x20f010f0c1406100602010608070522020a02030d0c0804020a0b0d0e07080f010e0604031b08120f01060f0c02012001020f040f0303090b09061207020c1306080c0402070510051b04060203 81
    0x9036280c240c0c410030b40c07104c0040f1f08031101406140110f6205640074800d615001b880c40c410415016800c0307100c424980c0b501d100740e8009660000c05680b0119500c03405c5511405409203a20003854a81040d1415400003510705215110f100b001040028070304644c0c61740c3d40c00511038465410112440c544d903501000b0341d55000c1ca90740c05030f11352801d02400840240402e00901071501a80c506100c08407102c000503500ca00b0140441d040c000411070f5004116050a03d184502e0403164028240d61622038043d0604482045800810509901c41390050307803c90399252400c4940c01180030040010115207009105441030140110720208000407002c1c1c03800706c00c1042d40d2083e075624504982c1d800b1244094010445110f40c400c4080c00420704000e404000c07103134458408d20480b00820040d00c08076100300904e41c26003110580b501414004034800300724a145525060300e0451800b10f850302e920b51144000d4410389002c81d01c0754041400c500f030010a80104800d0804811343c2d4660b0b80c034002e50360303038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 412500071 1250 412498821 412498831
    0x3040209100f0303050f09040501060503150603090a080915030408070c0b0f0d0507020a0606091a030c030a0209040314030a1b09150c0303020c030a09061803020f010f0c1406 76
    0x3000c00000102000c45030400340045800807691510090b0a569003a00c0c1034210442c06074200006200100013a51140a298020200c98071103950b0b81c24200e40f500035144810039003a008a40810901c481880006042640d00d0b8000d1030b6039072a00819000203c4030400000c00300b071a0000481848203100401c3d000301013142c071a410100307080c0d0780d9503c00102f0740a804480300b0002c030107000c090300103121608500e0744100a44182c40004d101e60340c450301103840c241c01c5001c1865442200700100440c3c01e003040b00303242e0110000d1084885000c00a0356880c000702000b8090b071580008901014010280d00002d01241e00050f0f8403440c040c0340540050180070300b401c00c00c50307100703847c0e0310f80e24060008002660340d14003d4091003000c100c400d0301c0d0030200140490406508002c0c18601000510103008c00140641d60800300e2841c00c480204208900b50420070361106000701040141d803400030411200e04c080c00c040c554180b6141d415281012212000b401d82012003207894515040460194805c07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 412501321 1250 412500071 412500079
    0xd05030d1409070f03030503090f1002090f06040b030a090305041823190c0e060d0501082a010c1106160c0f08060c0c0c1914100f1808070b030402 64
    0x1540e8a0307040310f82c0c40325544103c0c1078a009101c01800801c1c4030f04000e59101031008211400c5c034583c00001407a06681c4101d0458055003c41d080c00103141070a00b441c41710f041210101d09150a0403030b2690305100c0a0400d200d8143d0b5030409404140c010415100101007015580c8480c3d480190424040c00189116000c40c045000c500b102501011960a000e06080d50700411f9440c00340c1940b43c010306808050fa014402c5110071120b031503a0704070080504a884460100d50740d45456a100d2030442d603000ca2002c140440211030a01403100c0c0110040e81000346131040850601d41003041504814001090b00701400103910b00c440117500b0b88940d0f0203445040010703622552200104003441842c05002c8441d04103a000c11145c0e0341c507030003404400609809482420b00c6400024001c1022032854800b101c0410904000c607200742d4503841c64090065403040d102c4c215140300140707070200a084143c14400c0a40c80050122002110700c0301400c0303c1c0c1c040701c82d801c0d2200c46054641d0000c813000c9100f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 412502571 1250 412501321 412501361
    0x108010f0e1e0106050a03050f0c0f0d0602160213021908072304080706020f010e0312060409030c0813230904120c050712060b04060b180d05030d 64
    0x1041407003021a0764001c203000d0008100646030309141640000c01c46201c80d901c1d07000100d01540c0750304450000794803d2000700309841c0100483c1381020901301582d4070440400280c0840e50b180e00c1b80782030901b81e202c0300060b07840c0c1ca403120700340d5000e0202c040a50001c240150854000c1900ea0007071000c002400841100e0b103c0b403120407901d41c80b045680030300203105458032641d424850072007070001c20350001d0002e0038a9143c00b429460400d46a01400c0180e0002694107201c140c2842042d81d007800010181d4505003190b400481c40500c00303000c65005076507520b82e6201b07061003120302c0010a58040b0038695030b44124403510300078424600800c0103110880b0420061500c80300401b50300180098001040d035561504c8203810304c3c1c42c030681c200c1480b146080140011b5410701c20301c0d000d411004070224210f8141d0420101b228001000540102c0c82d046003480f01d6441401074540c450900046414072004401c081a0003103c80c003001002c600c17000ca01e64408210a401a0036008880d81107444 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 412503821 1250 412502571 412502591
    0x20703170403090b090301020c16050a08070303080411190303120b010e03070e22060507260c090117010b03010608090a111017070c122f07030c06030203010801 70
    0xc404056400902003000b4800c00c1003030f2505100a0200300e40014001410000104049820301e5120010150740382c80e05201032105141110740040038041140003840001e00796600901082c1010303001510f000c5c001202040169200685041e0400201d0790840055942e85805460f845066103840c034214102540101d4552003801c5403958030a0080090280518180f41707510444c00140c4403686041c4804400007074651403a401c2c0140074854100000c507480c10a00c010044000781040098400000d04915910190080650f0f048030000540e10343c0d6098a40040e100c1d05244050b41c000300f641c83d00005040d0803114003444c101c0d01070742c0f900c100c2e87c2d4400440984400328440700420300c48100c1c02c41c1880307040c0850494407045881c100083c000c80c001c0032603802c4c01717002c546100c0003541614040e03040005034500c4141e4070341c03e03060280c2c4d60303010b1800340024090710304842c4044442d018120861800e081008200464100c8003000046846100090103944240201039056084c503107401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 412505071 1250 412503821 412503857
    0x7141f0608120409050903040b0309060103173a090c090c02010b01091e05060714010f0506010219050106030638010905040510091b0801050a12032a06020703 69
    0xb184000c400101c05151078240b804800041001030a5022a03105c20f0001207400e42c0c11030011030103032228000030110303903245d0325104403010014131195485100501c2154503160701030b58a40091035100503000b0030010540800303052640f51702c2c0d1001d690350074003a40d181407160000d408015a443e20354144070f1101035100a90030f035054501000e00003143c04108202c0c0341800302c800c0c2200c2400899180d0125560030024a49401103181541c1809101c0700000507040240301d00010130207110000e020704d150020000c0d4845986800f042e02c0700ca01521080100002175101001131503100500f00aa8001c1f4120340f282c40304e001c0000c07003801040d040500c024047d84807a0120500c81603480107031040c02c1c10b003408060a405020750546201420011134021400d0150301003610540c0020070440090070030040080720180d002034002c1000707039020701590203035070241910703160103040486203c4a0401001425402100310b0400440705c03030350500400416030014800d450096aa90f0395003002d104081d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 412506321 1250 412505071 412505083
    0x14060d0201080f070302040f15081506030c1809070807181a1b06070e0414040b061c0b04080a110102030906041e020301110405120319030207141f0608 66
    0x20740032800d8000080c000d04400c2880d40e030703c1483d615016081a50701c0c03e40341b9029003d5041451b000c40d091001c0d030340d0b40782c2c40010130394440441d4201c0d0840ca152580401c803c3d00c405400e0542e42c0c28006540c0203446039030801074401c48070281001d0307001c1c41c044c0070060414a040d500000000c40c01342811a121110f120130405440008900c06440d91081b02c0d2410660b11421040200c199250344003049003a090100d288140600d445001e01100c5840820080b16000860381c20340c9403890041c800400d0594881d640c1c03040c0c040d119031400781000c11041d026102d0196004264421200410003000342c0f590203800181c400d5103804091030490b000795070030707400102d60a240b141d000c00009004108030460356002000710b0740302c02801c00c0440c0c02083c03d44851341064a101000000c0030880360400b0705030400d07001d1440000c0c50400544c00761448520b03120614900403d90045156418401c41c000125248000041265a40c90300810f500c1a103290005203096400c8c50311130006420700000c600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 412507571 1250 412506321 412506323
    0xd080123040513020607030905120706050f0703030b0a03050106090c111b01051908190e060406020903030f1602010216060c0213060909080711010306261c0314060d 72
    0x3008a011508106001c01014014881085201c80218080c0507031900c100800d00c6d24020381c1c504040c14180b00911046030030301d882034405580300050402c203095010007034a40030090101200c1d43d41400c0d007421000f0344402071815610150b001800010004158021011950144014001d4003201c0343c0c2aa8103010250250300c140e007040d03400c02c000011243d41840304035414100103042c08880010300f24017040203514280804d1400c0d0600100d040d805404040d02c0c5540907052160f4000c6040b81c1d5101c0b40c0c040e100170542600407454a00c26581801a2641c0d8551102201d40b40e41003014940b4850190711800d03070140c001d60017944120390025400806940c10f945072002c24148a5003802003000030b40c510040b030107030364040108155000d4014234498900981545807030f076656043c0090010740c01501e044c14503203001010481c884449910b0b0750f4480e0301f070354440c1d6800d00c1c1000403410003010011511600518a089100300c0d40c15900c00849440000302c540300c1590b410040c000c82c5112548 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 412508821 1250 412507571 412507619
    0x3040f0b360607032a03021c0215150409232107020d020301150509160906030f020903101a010215040b04050f0313150203030613020d021b0d0801 64
    0x81689242c2000d10040038100e10034070b442040041c8600c03110303002c3c01e228810418010440e484200070305604003d8881d1050711880701c03c0380042e14600103542e0341e0100c5100070085400a00041c03925020510034040724034041d0041c09420440c1ca03068002c0350036003000740200c03140c14204980030070001420302c81503041c24114002c5080c8849080b50310382c10104007242d00030310103900107005031801e00940000380701c192244c503200ca0804040109840000303005070710300c0107003502000305143d103d9084011505282800902800300c0c0311503001a10410101541601c03038581c2400c0f2501080d484007061420000f0204042d001035001240c80301030f140e8105c40000e0005010401141e4100025074200c2e100b8821102c1c00460b1030101c0341181c00c0400d460303104440d400300412208256030701c2c2d1159507842c1d1014500c4c610380800021014214030070b40c0107500794046481c011001c816030407038036000919521003642d0001d025445030743c3d4503c3d104d42c1700002c0b5440000210502203803841e160a000e125 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 412510071 1250 412508821 412508917
    0x6050301150c020f0f0a030204022d12070509130e210403050303060f04090f030f02010605010e06070b0a021303110a0f06090e090a0611070209090304180e03040f0b 72
    0x720800903145c604081055005040d10300020050341d40c4d200518000c4900c2030b611030380301564080c59000100700b410700a050382c01008500062507120140e1a84050b141c101030b512004118007141c08070590b040c1c0d01021901d0424200d0001d240040d07920b0441c440c848044110159410044500d0f02a91000400951051000c140c8514219105550b1040c018100094450b40380c3c994406410001101f07802140c1c008281c0f151130ba60a00a14015180a0034000341815982c00405c60511070440701800d00786880c000b146150040e0340407144031624854010780f2150f164149840883e190029051055001240005480e00085441d00403152551152818149041e25905041200800c52000c80c050b9080150000d4410b220b100070007040080c0541d12680107105000800702c0140c000d5145510038001001000c1084004203e0b58419001c040348900d4031604140c95801160041001e41c107025402050000107000070704529001c0c84140b0740100c5c100c0884c00e41c01d51b00300310340c1c0301e01003250 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 412511321 1250 412510071 412510099
    0xf090111090402030c0f040605070b10030b040609030314090c040515010e060708090607290925030b01090516110304170a06051006020d03021801081e0106050301150c02 74
    0x160f4007465001041307100c0c091402503003810302040f5502c55007001000c0b0394003003400c00c10702000301da201d0790005d00003015060781030458840011402c4010700081406480e5018442054802c1d00a840b0050134010317003600381d060080c400c580319142c3c0e5500364000da192400140700b44a10300c603080c0d40c9200c10385880d80c10034030820038003a1035400502c0a5500b243c0810002110740c80703483c0205101406005080b12a580c4101402905030015000e8407030070000340305101c4803c801041825081600c21048805046e50300d5441c12001801c2d840a40448503400000802e202190800e92140c02c14610207540362100603016204807091010200c002d40c001e10051001814580090600032810b50845903104515911350041c0e88007251080d14941c900301d010040d15404200021a0550504003075040007040e8024085180101e42e28504101444001c40c0303500b48002c02d04045500b4030100b0002c82d607114040074009030300030720038488052003046001c40b0003481141c80b002800da0043c0040003d00741 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 412512571 1250 412511321 412511329
    0xb0604181d030405460b030c0415030213060e0406030b01081c0903080904050403030605040c0c05010b0a050915150313020a0b030c181c06060503060703021c0e010212010306050f09011109 82
    0x498445c03150341e5100794202241002829019603c170303c2013110000e90751410070030207287c0b40540c1d0b103d81080c180140800702c00d0881d1100444c0a840080c5000200c61185a0004014002650015124020034000454004d00210b04629120b0005955281d45000100c0031142d80d00d0501c400b034815102840030420310318264012540050207881d000c1a01511040000c048421300c006030800f1030300754054882000001c0c002d0780c0e039000741210078201031454400800d154510040c00c0000c1c01c40d00658080b0581d644494031054402071000c0e298407481c01350095841c0000550701a445410359460000700401c1020880b4411725104050074106402a880c0840c0070f1412601681d1003e03800c2043d5190740e82000d00749861502407000410760528003014141400340142c1800c04242c010009108074080320b110318240003900220000e42c078907103101220300a0140346918101d45003403070000818003915420150080070f00c0c40c66088251548407020303003200c0091041e105440300c180f110051602e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 412513821 1250 412512571 412512679
    0x90a170601060f0c12110d03060b0a030f14040c0f05060a05070602180619090902160305030a09150e0d0e0913030e030706210b0604181d030405 63
    0x100e5040c04049041303141c0d0b034040100394070701101d00095080403820b002c000082044181c2c010305800c0410803141403030304404c05885809030010074951100043ca41c1280c141d44402000c854180c50144942858600f90040c01e181c0d105120741c04006c4400402c003842c0c100100c0382e142c0130584806140a13415510300c4083c2d08840740310344102c445015040700a8039030000030840f4603071031078509610706051003024010702d449420030f172111441031020040f84603e80c007921500c1074143c10301ca9240d5031400e07a418040d165610f03008140d4080940c4286c4940104d8021103c03500c0300100b43c40d481480f100084982c08988004164043c0242e8040341024044102c0c00c80d440b4003d19018890091000220f441d0084e0355024000180c04070805030070140d00c1c020060107111046409114201b900300002c2c0d058042c500449064040c4241d556009504690000032200b20b04503503620590800c0d0842c58803a00603200d0700d8019a04180c861384062000148241c6845049150040007060303916242842c403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 412515071 1250 412513821 412513847
    0xe0d0809010b0901171009020d06050c041503020406081e010e06130e030403050c1507080901120c02010b030c120a120c02210c060a0203181c08090a17060106 69
    0x1540e00e800502e40d503125912031030f001e49802040410503413a460b08a5180800030001c090350039141c0f0811000581c0c0d4090b81109098001c9070109241d25482640041407085501c50107103840801c40400d10f1346d402d03030040d000700c0311140c8407a04140d660031041c40c4090240c1c540820303002e041d07100500041e1440d80400381c1003140a0305280380031441c40391802c12125203096588070f03a80049400c2003000810060301002050980b06010030070b91081d04100c26015a01000b01600b501040313072070310785c0d214a180d644440302c8044280280d04407404007a000b800c0d2002c02e58020300801c1c0d5843c4c0d1600788441c0c1c00d8071440e4a000107001960503515030501e00070054080b40c0c2004188405040075940ea419040d4211a010340325045922849402a1178913000b040101d0140d034007031152140240d00403043d26804010231030180d681e240ca600015801c80c203403000d0264107555600780c4070103100b17141e00940b085030b60549a107001ca42d00d0700e5401c00d6400d40c840c0800f00359070200c00144006c0b4410000481d5203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 412516321 1250 412515071 412515073
    0x40503100e0f12130f0501140d14010b03040308010e1302130b210f06060d0318050405070906080a1109010c15020a0f17011a0c03120916090e0d0809 65
    0x401d20b18005181048152000c0c200da5038000715030704142601c3e20260b4070092403d072141c0d800c0b041c07400380081d00c102d10300b0780f4500c8082400300300c04001040d5500090110010001c6200107980c59240d0b002543d00141c8081e40050980c10010806080301c00b490f40c0214102100300d405c0e00c10030703401c220405a4502800c102d40d516240c5000d00e41c0c844072904039030f180c2c00d004086050f15120790214602f0006040089503948400305006594840400e8809201c3d0180ba00031000300748490810f0755a400c42e88000c1d0003500e000204481d56900c40c404400307480d6a03030390341481d548031840003070142e555444e580d40c04081c080006415035805510b80b071280ca0303c00d1595a0a015a41400100b2604a181a040455849104000030715800400d59014016614040180d541003107102d112a010900030820000e200150050881030100240c032818115a19100d1180c0340111095071201003007400c06070411024040415254014050b0340c405000030802441c101036088011611840c005d8000a00c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 412517571 1250 412516321 412516333
    0x90c0d0f1a010212160b220503090f090402130e0703050307030801050405011d070809150a0b0316150f0e1206060f04020a0e040b0103061203090f0605040503100e 71
    0x228041034020710701c00c00036005000c1c0d84020064006820302a0040280392041d608000070b620f611301700d001c20300001d90812003000041c1c0e50a0131072102c0103408400b542c1c800a00000080811200200519035448261341c0d02114920803400e11401c008280c0340254000c078091101c842002440c3e2188c40800f50b14403c0f1070309142e40707440b13582c25036005600c140c00060039400140500e0034140100c900500003444009a800d1541e030b04c060154501800300c40c10804660f021900c1403104115407440460813885082c6581403030204140108111508503000c1d018100350410090004043c12084480c583e848114189804800303c840d04851070062060100c840d100c08100e0300c40320302c2c0300300b01e000c03040090019003001d00030017406100c91081c09108500411100040d16400071101d440e20606560100c0c280b000000140e0140a00d9000322420306501c2120b01c0c18143c1c00300c081c4084440080b94905260340340e0004a4480c450b5001d0940c15030b014401c105281e0b0300e190b210f1a0443d60010540340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 412518821 1250 412517571 412517591
    0x5040b0a0b1b24040606170309010c151416030207030f030c05041502060708060a0602100b0f040c05030106030e060105010801030308180709020406200a081606050a0f050a0b090c0d 79
    0x41d005101d520501e6501d2110f0200000c003c00d5116045c0608482d5214003190302d40000166968032500030744904001c070000a4a00b0042c1d1038844559480319080309001e101d084c0c81e200110098201d8690800030300303100c40c202545002e0b100720781e0300380d0f0580d48101c101d01d4800703c01d40c040d1480c89940f90401908000c001a02990540d400c542c524065010304103905281000a2402c5030103480c5502c20019000d007040030940008407042001c43c41103000c07441e2190000002da807260407181494000382032112004030b00780d011000314162105900c041100c429500c01c0d15503514404d00500e070104540c01c8c014004a0f0042d024203612441106021040c1000229600d082c50003070760161041e55000b00e030502021340c1100c1140b2105558150b1101d151017403403102a070f078014024000e00142400184035001c00c18041041c0c0d01c554002c5c41c10b00050410758031340300c000c245000d941c0c5101032600001c00d0034480140a03000500e0001000b42c1069110141081d034641d1081117180c580c55682e1380c03008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 412520071 1250 412518821 412518853
    0x20301060b25030e1e03011a0105041707080708030304050d030908090d11040608010618020f031501021204060503071103030403020c01110f060c1306050f0403030c020a05130605040b0a0b1b 83
    0x54400301c000d4075610804800348149400e64010f12040854a074060041e5050749e45d0150540c6e0440703402c841e072070100038000c007a0241454415000440180965100400c140c400040114000c910070000c5911584000b0412421590790b160000c102e05000c0101071340c2071422690030002103007c0d0000da0b10503072404002074112810341e8041140c80c1d455850402c400020103400c0e2084c402038800540c64913404200389651482700608100c0d0814541900b02c12503442000000580c0e03050744000ba50311612107401501d0745d04202c8458001400311300c1010719010010069a01903035154001700100c0c0c0c42031006460000880c58141440d215415040005103030800c41c45001d200e1080505a5800c05c0c050001c0740c9242540041052102c20405518a407005000b182c1c126501031810b0000e41c10181300103410070301c2c40d17442039510002081410413044074590101d4220b030f60031942000810069000e0080b134001c688074a03101e01303500340700c0f8a02070310030003444103452600380c4140c4035100310000a030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 412521321 1250 412520071 412520089
    0x20604120614091b240304030801051003020c0303070e12030d0b0f1f050a0306090c022d0d120906060605120f1b1c0612020301060b25030e 61
    0x780c4106403655034048106680c030660a40150000020b01101514203082003200314000800b10302803403000480c900c6100070b040381130b00c1014034980542d40c1ca0401d414014112142030054600c00c0107000c43c2c0100b854041c1c404c580545407091b0207141143e4030f2140a90307100302582d0b105a0000d04e1003415400c011014002800800745403040082c817010800305019841c5c120a6007a8042c0800c0f41c1d40940c80080c0b814881030b0100c481c80c0442c1e89020b480d60403805440e01d540106a13080c14141291010390700480c2c0c0c0d500c00030744c1032281c1854070703a00e44516500b11032503c15207145400c00181c0380f618500c11040315480c101c0e00c0d2004a00c4100ca580c50008903919540144000b810204002d0003100201c070080c0e4010200c03500c940b00d6402d00703d692104e01140039000300c04062000079011074107150300e03215640d070340b6000e00200502d5a8414491910300064007040303100c0c2d440c2607808605001a00e00781c46450811200780b807584942181000d542a00308001a000e025175449080801c0d5680101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 412522571 1250 412521321 412521323
    0x306062f1213180501081c0309020a140f19050103020702040b0a06030c090b030106020705090a0f060602030309011416030b1302130f0b071203052205030315030d120902060412 77
    0x600021626002d011114032910207500007103141444010810078000140030707807030b030b10104010301f04038a0540803d600800340e403540250802d412b240c0006800303c4c800485088039070b0a8844031485c111103020401184007110190303c100c281090180065446940684034991018000241d0f12003201c2c000307064022181d0150b00080c0d00c0e6149000e0361548480300000030147d003040d090555040c030b00c0194440d60035002d02402061060001105080c00343c224004080e01000d00f004400c3d20740348025180d5004548112036503003450300c01160110b0350302001c1c0c4a40c07607503403000200e0080c50034101e01510721002c0e5158400d41d20407109070031700994070040003002e0104240300c2c038103490310031014510b4501d6071058001c85018401c48002c9000b07114821128503051070000f403d036591001881080105212044510450444420401c07034000021030094124101060178045104200350351240d8013a001c1d07001602d2080d148482c010701c1d8002992981c4002c103a141850b8540b0b030030b103034080480c0e00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 412523821 1250 412522571 412522597
    0xf060d0f0506160908060c0d020904020d060602120c1917040b040609050f06030a050a1d150603010e0a290a020711010e061e07061107030306062f12 65
    0x24803101d43d82c1c0c80910b090b841d8981c200359110500c0c2c01149622404018418420300c140040c5030800810030303504640d007500c4018821502c0e4000104450002c1040d4008c4002611030074081400e60344200b0151601400b00c08002d105024690105044c19078062104494601c105c400b192280300d44000900081c1040740e80443e01c8a24100e4010701850442c0e000a014810b4a101c101a03a02c07401c00303c03548101c02c0100482c0c580c0305c09a040b4000c003246403011444c042101010002c100c40840d1190380c07100078501c07650791520303640201422965610a00300c090341c4013099030f00015200f0502141004413491501840d1000c00c0f41c0e41807001c0003140c0340300c1d0709640080c2410400c080307801c200007940001e291080030110028041200e510580640daa030143e802c00c0792201c2032849000b02c642440e0300c24000e00010310103405180140e004a503080f408a400c000010400912400300c08071546408080c8402c044203030401c01c4084508058510b501d4003c0c03015209105003d1030050440ca18800c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 412525071 1250 412523821 412523833
    0x1a0d02070f0b1501030606090608040219090906050c0903030901120b0a0303080106030e010b0303030606130f030803040209070c0201050d05060102190507090c0e0f040225060506040609050601080f060d0f05 90
    0x728426588680030016050500d411b0701442041e42c426002c8060381c015040c03124541d260350001a01080c20003500000040c164030010a4685032074010039030451080b001805a52629010074400d40151050550907500a001007072441d80704488050400b90101d10000e2107910f0342000c144000080c0c0c1090340450500d0004020555161240c00e800d10160f40003009018014000640c1343c0c400603048a00c5000b0210b40800c2c45044005110014102a14640f41c0e85942c1e05d0300204980040307500b607203d91413440008403090b0082202650300f6505030b584501d4543c520311144010b00016041d1030451141d25262810003019020720103001e0700910040054925081d0ba0206940c0300740d03001c40400103400c0d000d400ac1e8071030904a48482030202e8000d0307200ea00e41c4142e0940718400c800009071198040043c00b0170300c25035074007180c0500301c103a90602101ba200c00d0028181c5000b982d105000900101c00034040307001803442e039034112038020002d2400c1e1149445410107011800702c03e840c690801 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 412526321 1250 412525071 412525081
    0x914010501120212040b0901020c0f072c01030803100806070206090d0e060f0706110f0414040207150b15070b06040506010819020307020a080c060604151a0d02070f0b 73
    0xc0a0040c074402d01c210542c40d200f210003104142510140000302081c1c207003408240012801e40544101000701001c03149030342e40c03d400c8141c1d10100741c400d001e07074807161900b4085000d112071000d500080ca158a101d14a07444e5035a00001c0364002005142650b1006001007a11807082c4050b80c001c010031360080c10b10381451181d00c4d0610346640b4100c02480f04000100106031140005e5445400d80600c1803900c03840b0f00d0516030301600d564840711002050010b00c460750304035410f0141068814080e40c5440003254082400304030310800c800640818081c03160700030706401d503400c140b02c24000a00011a800d170740500310807840d002044121402c0c40340201300080e03400c19106035644035100b480d2000e0786082580d8103044103a000e001e43c0100b1a00000001c22890080040c981380961041d200342c0e60f24540c0d01d41d43c0e1030703580c0ad560b094032450610808480b41d41c0c00004d00025182d03071720482c1040c002910070324903e503440f000501c01040d40901025004c00c02c201e0f9441d51080c01800b84980034a08 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 412527571 1250 412526321 412526327
    0x9020f090a090605101d030601080a0311010c080408070c050604060302091c1a071e08040b070201050702031c061802041d0f04030c02010509090a020d0605031f0c090914010501 77
    0x1290440c1084901d442c000300701d0385d03645225501e402e030854144803c1c001540c4e01428021181c8a882641520400b800014480400518070690314000d5607031420601501c4a91402e0743c441003070800009001801280c08101d4820003854a940300c0d180c18000c1c03e54403004500745801543c1b0070301c086540811000110b040c05074020000b9000b081a6014040950b070311a034080515542c8901d00e001d10800080342c1c280035081070280d8070490b0130712800840000100900083c0100c600312203c0c0e14040106401038014000d031800340b01150040c43c02e04c0d444100c01c10a460002018404254441c40005134000720b078828100806000039000d41d6803800d002c40580042006a00b0784445090700041003141c0302d20070003c0703401c01e6152501c0341c440d443e03d0004030344a00a40610305c0c1d100c01c0d16018404020080c0e4028210110040014002540d950081540b6420940c41820280b0007103040b015520f121a80701003504121400c0100106032241003042c00c480b4098903c16003001c5140040c4034541e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 412528821 1250 412527571 412527589
    0x1218070e0f090328171902340303060501020a05060106050a05040f170d08040b0a021c1503050105070c260403050f010504020a092304110d0f020f04060621020409020f09 74
    0x2c1020b00310b54042c100912400d21191b071074070f0f1105d000c55000c01d03806144c104e00c44030140000400e940c400300700440d4074501a01c00d0b50001089000c68501500041d403540040742c20001c032070300071000e010340c1c1c3e1074107805988170f60040ba91034042140800c07011486407200d80a0744003605011020884528401d0881480c0c5406400700400303202c045020040004d0383c0c080c03600d40c410700300000946c8a605c99030000e0004441d40b400710f41c0c1141000440c80104c4000f1362480220f0380520000d101ca501c50341c0d400d039a4107101d0100074001c0021810014a00d4a0050401071501c0da0255003e10309070740c0303407a02410f01c11400c1340f90f91180d4413002480254a440c03407400001e05101c08040140c6111000e83d907150320801036207050032a04210005080c0b1810110100c0340800240c0094001b080340d207054200740302041c4049104948041105046060034801d0f00c0c145c0d50140c8800e24129042681c0c050340380704090002d095243c007000049003042c0c90740080c0002c46000c4440e680c44484213402c1201000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 412530071 1250 412528821 412528847
    0x60b0417030903071a04030b2401080610050702030c0607050703060c05090a14030111031602010612020120031606020405010f020c0f010e0a0503031218070e0f090328 73
    0x1c0e00c02d111a039816500400d07680b040701c822504140ea0600c071007816055a001c0e607480544444c3e0320b03c00700301704a100b2152241801d01000706414140b0320600040d1142c0300242c40e10b0b07400c41d162220300d04100f8082d10080c071000d03000808540040918030002590307680710032808c441715000040e007001001f031140680c10701d1a00307604005041c5000507001c200c0130b03641e9106041d8001292504640c01d500d003036102c0c021014462035055a45d00c3c002007407084116a1601c0c0c84015032034081b000581c10a410200c11025605950f1f42203503113989103406c41051403540301e00c048e5000401180921601e1000c031340318040d21030a03001d038071546807000140441c001103039508203540044402d003103d540c1e242800d92020b01c0900b4a443c03082c4921010071f14191168100d260580710016908071001c2103055124400c00c48440c12001d1801c054008a03114041031003074145115250002c21030080140c907a180e44168108200c80c1402000301c940c0d5180d00c10600c42c0e0b6060002180c500050030390101620401c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 412531321 1250 412530071 412530073
    0x30109082502010e21060a0c090806061806031203070216060819020a0302041d010f05010c120c140303150306060102030a020c040b0102010b060d0506040f060303081612060b0417 78
    0x1c00c01a0000780c011000280d40c0c9100d507885038480840f005004983d1360107445c0002c2141c0d01da15100700b0340d0303000307185100720500440e00720745c80081c00c0e20700001c003e40309410242100042000c2140d01811055015046949c94041c109441d9428160000138501c108443d0f4028803403850018109000c40c0842d4001604100c1024100070710522400714243c14034400050060360713040010703011030084c011a0400c01e611050407980511054461920300d0503980355041850355540c0c5c0300010344280c0c2130b814004014070400ca91851041d4050b01c0440c1c21503002e004a1401c00050803040c80c11640121030411300c0141280484c05581020420a80c0c022003c2c0011498840e990401a56a00061030710500c45d0b6101c80348513000740d10030740140b420388d44e0143c034054603094440c0f900c2d0054001211001c1c0954640101410710010b02c1c0103020480b505512900074584402030b044804d00c0300050020f0500c41c1d000070f002c0e480c4085100741e000820400660070f0b2120b0401034881c5028044030360118003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 412532571 1250 412531321 412531387
    0x1003060504060b0a0e0f0f0a0b030108070f1a0309010207020402073203160f02040501060503090f03040311090402220618020403030807120e0d05092403070e03010b03010908 76
    0xc0c26810800401c5803840440d440131444184c40c0010b07d800c1c1310754401541200c04424001041d98000c005107042c5d40703140054590300c58450100008070b840724072070340b00403120b414990307143c405010004580220320800003500e00700d000c0e004101682e10417001168000383c1c00314080c503650515207003c04a0341011034001140d41f9690074959480c01010781000040501c41c8088040200703110b0040c030040c3d40a8418090340da91008050320503001110341c183c0501030000003042500000c0210307411743e5401004e60f6400040c100a0102400009204a0300018a56100c80c160401c4203d208201c0c0c020340d10101e00c0f03900f40010000e5035482c202203818624014801032000a82040c4101c1d801240d80c680400182032006e0040c1c0548140700c0c14441c05d0040c1651003101d20362000c0103200c610800e46078800e4030442d90300044801c0400403101070392036905201080a0a200b01120b1495120050007c1118200040001e007122205641280d04000014800040202e040010001164007031407941c1d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 412533821 1250 412532571 412532587
    0x106050604170703021002070f0b0403021e0102030714070f0e040213020703021204080c10020d021f0207150b04061706040b060a1d040203120a0504090b0307051003060504060b 77
    0x1014000c900a400b11000710800201002c001081684000c1d50014000411800d035510043d4954240703016035081c07004000b00129036515980104c2e000c0b80d9026044002d02104403007043c4480705103200c0d0904500041007007101041c40220f5034640e50b5250009425070134500192210640c00d50380c4800700d0310b8405400c100140ea181400b0a800201c81000540d544126150403414101701c504104030000001c074002c14031203000500d0500352841903500201480320400280c4e41c60b580300d186d0000690048a41c2134807104501603035802c441c4464400360602400b0313a24402c402c2c106448003d10143d4415581da83c41c50107010b144001c02440c0383c544100103e6141050300c03034400800241c9401c000348042425901d41141a100814041c54205a001e080c9050191542c1c1d0548040e8803d1050341d900e2003040903030f00200d6400e8403845d215186028640b2003150003900845002035450b010311200000c06440346501144503000b1540d00284035420078041000f112215001404144400c0c84540 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 412535071 1250 412533821 412533829
    0x1a150103060f0902030402031e0a06270f0c150e030607050408151f03030206060f0a050d0215041d180106030209012106020c030a02011803080609040314031303030c02010605 76
    0x4103541007000090703980d542d6400403a203804031101189c3c050490000b00729014800100b0180329147c481d1105100da103003041d10803040c06108400311032115000902a000280c208008401258440c0d00701d0614540e0320460305400190300d102a201180114904400700c0c0b409000c0d0310f600c12500e0500781c8c00c19081140c0169642503a120064144000401044040940c2403044002005045007084c0c500e48925000351500015103440340100702c000051001ca10309061000b0581e6805040182000d4aa03002c1003802c1703004103070f101022101000003113071083e61095640e00708103004c03900a0590600c14403002007480450500e04259240036403d00040e40e401031014110760031010400c14105410040781c40c0c00c3c0c410f6030018056480018201000340c0080060300a0740c000d0380080200790b03440340d010807802a120344001c0018903000000740c007a103028a8030641240c0a480e00c0301145240380407000c1568401d4815030005c04d0040380d184101507260142001249107880240201c0703141c6004a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 412536321 1250 412535071 412535099
    0x2090a0e16050c0712060603051b0915180901050f0c0427020c010e060717040809010507050709090c2c150f06120a0606020a0f03080a06031a15010306 66
    0x14000b00000012000c1e0305039400c20080000d0f101c0113001003211035080c94020000c2c4440e2004455a0080181c016046040200d000c1d02001002d41603040507910300842c80708042c1401034480d03016030019141000048140d110034070509800d0700024140c2001132141c0d0b0342c0301000300194500c840c00c200a202540e0120054850b191405415000c0094007100c41c0300a40189104140f00e5841c0491401d41d4180c0080e426000e0341c5c0c942c44552915004003003c10084404550242c450801002020103651181004241d0b560044058410f01c45d120040035050350f00c40e43c1e043d608404200c8052180c030030403660b003c10b49026000c2c54001c05003108803156040d40001c100c00c08080094809020980311018405408100200025503851000000c0000305070103a0b1080c208528003034000c14000e000040886400f50000700012070424255070440d0005001003e4a00341c0d501e452002001072001545510a640404030801e020b290160007815032104070550300f4100760502c1b0041200e031441c003590b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 412537571 1250 412536321 412536361
    0x10801150c021c0602072105040807030210141306030f06060c0f022b0507050609060706020c07030c0b07030e0a0b0a0311090a03150501050d02090604091a0a02090a0e 73
    0x501c1001c42c62041d115150220140060300c540c5c000170302c2004101c801a0b070300c184011030f4040c0c5031035084034a00440d058001e83c0541009544a0700f820300c09494080c040520101d500e24040d5131000280c4030021103070704800b59000801c15040024003085405020b001b400f4203940004101c3c040c985030000304800004200030b481e5007406a8594103540315179695040120800000b01307202554003443e140d1081801c0c2081e551030141c560701140600e0440111010614014103c6050010075200c800003903100d00d00c10040351241c80c900000003443c0300f01800c0108030341100d00f81c5506d02070030042c003a44042c280c0340f44039150300b0006100560022090b28001600e17841d00007843c00840801c12800d210f446012640411030302d50000411969610340104280c222a0034001640d88005120320a882028002d5005034850009901400c00d640400d01d582c1c003400c840144d011110450010180c1c0c01e49180c68007603000a020419400c0c400c540c8001020f100100340d86038a81581c202000c400d060322 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 412538821 1250 412537571 412537579
    0x9160f082a010e010c060204080a020a0806041a13050d03020d051308191b111305010e01180902040c050d0e030f0304020913050706121407121e02030f06010801150c02 73
    0x70b8040d8559200d81d0941072170b83d61085003151758030b845c0d103201681e410100e07600320b2181c906140701040e402c0b004910307180500c1d030105d40900600c801680230b22494000030f20088400c0c010310f1407180811800c120052032400f440d100140d550540078001360903540020640c0290301080400385002410f440216842c1001d0030300c61191003000b0b41d2045681c002150000c0209514215002040c0309890700b07505005001194200e1203000103a00030002d5031400d200b594001c5200740300400000b020540d02d041013018a1000241001e110350008080b144031010b001c0008102041592000c141b40c0700b85007000e400440203600f803030010030b104503251000800080c020070361600450390803103408500140e000e51020a691090351a52001000820050070a0381a10704202190310b001da1071404840c064025a0f0302d0301c2c40d9803203040045001e40300c004554805c3c1c3c2080100b880b5849080d10166005448075400d405150038110001003070b60030107800004503240c044c0704103451690001811102c4a60560b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 412540071 1250 412538821 412538837
    0x9150506121b04030f0812061017070314090a1202070509180c0d14060f01060503070309080f0d0f06060311030406050c04050d0f1a0c040e09160f082a01 67
    0xc2d281000d1400340b540010800320000c1c081a003040304103000340c03190251048203420741c0d035580c03420042c0380c40c49503245d9404103ea441c001d00200b0400c000c55680702c0b03001e05000c80c3c0c140c0d070051070709440720045404140329003158440c0e81c20002c0d080c45560003100188020800e180c00d10300040d1f0001c80240040305242222800b88010600034882c0d5940118000c100c1d140184840c00c041032965a801c00c84001c0d80140e00004500807291019a41039039501d0380c400742543d03941e0b40f080c1c004280a090540302c50105004500d4070454810003072400410002c408038003100101c501600ba69900e81141d000d060900001c3c15035030010906607a8072540201020800791500651008144215001590004080782001050110030380c50b8404803441005007d02468412001c01264201511100301d0f0400400040161082c107410b00d0360000c00c440143c50190503c0511400c501036a684200e400245014003081a0542445040c2007041c21940c0c1440c4a8051996143e0b00b542a80b10385050140e42 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 412541321 1250 412540071 412540111
    0x4090f06081203071202120a090201090302150714010c080c07030903150207050606030c100e1c0c0f09050c0901031e090620091e190915050612 63
    0x3500148010074042007542d08454004000d041254001c81c0c8100100d58158100740820300c840c402c07209091010f1940e40025207a100c01d00010b044441410790400c0712950021000d0ba0b14201026101ca0300c1d0084c09a450200e8034094219071041040c40303081d64504410016103c0c0c011144981c000d01c1c603001c0a54841081c501a03400030b10710f81000c1d100d802c040c0009040045958018038115000700102c030300303d81c2c9040405680b4602c0080903a00300b600300805900e81d9008401500302014000d1090300e81d00c0d145901c07403040103d19501569040d68413002000141e040d41b20300e502038400c5039020f01c4949407105c1084a640301c0ea494282c1090798500c2c3c4002e10b600b02c9004800485054a014003c0116074104040500f566804048071210383d5450a6011079a040465404100103000c0c04480024156402500000c4884064215a030203154903408071250305040c02422142000080c0b4664044d00f059800b041d94000c0350003050104650703a082c04080300348130360001a502070b8810b038280c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 412542571 1250 412541321 412541351
    0xc05070303180e0106030506130902210a1e02180103080316030e0d180605090a03080f0c0a14011505013905010e0607030605060d020304021504060807110102040b0409 73
    0xa944180c2c112402e41002203805d60f41501303c0d9001350400c50b401c40480900003198000c4568600c0300a61010252841c044445e00402000c89903000d104c00f501c452030602d403507480150620344918405000158401e8003145000520703440007583c0d50103d00025810341e985c40404fc40060f202c90030140c1807520308421140300307401c1031045211540c15144522010380e006440104219609640310341540d2000c50304074420002d0f5400c00c80700074540c0003500c0c915103071885c580d0b00c80c0d050f000035040700f006651200707001000640d40041c0f1504000c0f100c1c80728600303c00d0854194448401c3d0b01c00d0000001c22040e81d01460b911081c40c0b5080041c0d00c4000407078081180c0710400101c040c14511000c41c4042031000c190f20042c618503d180070b51f481a074403124110101c0b4554007956501240030300404501e410784bc0d010b10741c464406881d8407811401116524099002a0710040008212030104000c1da42d1082c4c40d00141040d1b0303002542810700f00310040300640124050303007a049a03100c1c0d0016000d01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 412543821 1250 412542571 412542617
    0x1051b010b100206100b03090c01050c012706110301030f030e0316121a01060921080d0501050f030c0a1a0d0f140117060703090219180c0c05070303 65
    0x2802803415480d00b0201401a40b1342d501191030380e10041d5030a07400950104050f040328440c00454005c2c060004d298001900c250b00180d41c030850700c0d0b60300c000c40c1d0003501140c040001d50b0003040ca201e440c40d9030a858000103503125a004546a500180300410004d00d0345a0040002940341c1070442c007801103031012a00d091108051007045404241000070300800780088204224020240913115664200070642c0340c0e0000e10441000440c54441000034034145088101d0303407400e5151001441d00b9607110303c00180c020f000006111991080104144e181440d00041d0411040c1c01034800364040000080d0b5503500c5205841035140030213800100c031003040007100c1e56400c1c5918204907500000480000800c0e91000203d03143d01490004190300310021aa0342c83c20250400900c0c2690380c14504502800358100103e030004060078242c070f42105110b8584c03010342844400340440e5241c031903201c0300b039695860100e4103002e80c41e1114000704002040c0c10056035094105040690101149602050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 412545071 1250 412543821 412543841
    0x15090f05060a0b01090602060f0705210405070f0503011404170903011803030b091003030f0c02270106030e03040306111204050a0201080a021c0b01110f03070606080c01051b01 77
    0x4041d040420101c819290b00141c110b0500383d030760001c441d4179560107990758142a100c00c003180c042040018001ca200d10000c1c8030080c507404010749085882104400203003815641103032190490340e42403151003c034250940080a04030000d011108007010110306050006c0c001602451480b1952080f1080e000111031050a014000b04030f05245030307081e508a000d88260450009041649036452460001c20841c010078840840d00040e03461031360161541034010344804c05025908600710b0243e56a00b0715034001120605040380c80100340d01502e0f0300e420b4160411014946003401002c1d01d101e0010950b41030f80d5108400140e03aa50de400143d1081c02110180442a4508000c0104212011410b2042180300780c0741d0500c0d40e202c141250060b4020b00c1c562a07040c400760614070740034008070780059050b1041818004203041c0703003a00d10341c02e20455101200d2a548005205820800030344520401490920701404007030132080b0000b4039601c03c00c1e0072140d481c03c0d280030021040c482075004401c0c1d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 412546321 1250 412545071 412545073
    0x21203030103331d0a0b011a09011409041d06090705011b0b0939030616081504020f0c0615030312181c020114070912050708100b12030715090f05 64
    0x181c1110314088107000c4007401409030b03648c40300b8040c031004542d031400e5805102d4140c4640030b24282000354002c25030015481c00d9405502c8040b09900e001044040458a643c2000a8003c525210a040d8a80007031503000c0750401403400b035514900c013a0070303081c180901d9101c0143d004549488454601d89030322a094007807201c94201c0803107815038186501804c0192681e82b400d50140c01e1004242e240c5008031620815080d84290350110365226880860307204a101c1d984440e104c06d9400804c080340c111040c01d60110300e0029003003d03d0342c401c019080e488920140a075802e9549007000c00d40702d00684200308154540400401c0645c0c1200740d5805454100400b00c079509100060490183c0711100c069802651920b400505011050b801ea50310403006612400009440c100c800114034903910401c0e64140030b48600843c07114010311050304603041c031180c0031814041c248200096138009020000c05e41d4020407084001604856401c142107851410008440c07403281000c68030004550802022 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 412547571 1250 412546321 412546333
    0x32e06020102040510021f050402121006050418151104150806130e0d0e01021f0510060206070f030b15071203060504060b04050603090a021203030103331d 68
    0x195035815400f510071a8000ca500303111a480681c01680c4541e600300c01200d0071190000d0451030002c00d6000107410601c0941445917081165040318104007000c0030000c2410b8442c1010412881c041c024003003e601d04850f000e43d0164580e41e0720300d8900c01d0702c2c9940314882d21035520103030380b00048003902d008208070200e40a8000c3e46a0004001000071108076100f003101000b60880b40300c1b540700f5510380c850240014130784102180c0b030036140b040310f2030034250461240340a00082d264076556807101301540f40388041460300f00045036821b04200c0750411002c41d07001ea001c0150711513215110154413801e030300b00098004440b6010614a10800c50021409040021700408004203084407218010507541c00300441a186c40400050f07492910501c49001c40500c0203112901d4214019900a14010211903d0985030750124070910302c0c00202001641000c8010001d01068900c00a04980802500070900a14014864441140381260036001d80e46601c00c010200c21603400d402e6402c952801c55107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 412548821 1250 412547571 412547579
    0x141f030c0e07021b032e0e010905010b0d05030a030c0c0c0e0702011a0f220e06010303110d0912020120011a0604030c0513020f0307030902120f03032e 66
    0x109061081c0d8248006114000e024031002e422055a01c02c4400e00401600c04009000c2e1044040700841982450b040880786041013400042d10035005004e14440010903a50027908145003140c550050701401001c20f601040000f40010040b25107050860500142c900d100a0b02210a040c4035070b4020501045458080707030702403000700943c1c40303081c207039000f031201442103201c0c01a9040c07e0901c19070064061607000c9040c0c41c1005140c8941802c0c84101251b0314002080d20095609600300f85d046600504018800d01d40d0000034034000c0d440d1000103000381d01036040d0080018035544240150303000044840011a8451540c0f0060b100001c0561010142c01e00000b0303000b000c4080c6080c141c0d00c02d240250b1000d04040c0300b540c0c00c407904010f02100309031421007489003440e411031075000495401c12084140d682907001840c00703030510b0380e0000f44020440c41844001222155184895880990070f8800c221000080321f5100b042c145000b401e0144401c641040350040014095010b1200c2074045 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 412550071 1250 412548821 412548839
    0xe19080313030501150602070b091309082110170c130b190f0b03090f070806040b060306240301061d0610050301080606100c0f03110709141f030c 64
    0x21054900803802008810045c90080341c13a000c4900ca400e0150300030030810001c5c04026800750188082c05001c2002003071182d14040c0c00c03039280b0841281e2054011800000b005000003940010328010740c0381d9600f0b27090002401c04030006a02c150f80440c443c0c0b0742030013070510b4144414980000c024143c18610b1414401c0c180150560034031881c082c4002e0544c280700358244420242c11545041d0080352450f0034490034240c1940002c04021483c0715600049004140401c2030b80d005040c880c020b0400360510746068851014042c4c0b0041c840d602000c14028a280c4e1b10022603514810392003611410b18070b010109001d0aa9507120100c3c1c11020312121800702d48182c206440f8100842c0d004542103038010b010780d1540402e0151584a602c1940000c0c4542401c441f056002d40385402c2140308107545640e9289074283d0f1803c01ca0000360320600300314491000b04212405130907660f80034054021644410704204000400c0b00207000c0c502d19020b0300001801e58020051904480c400488544401c560307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 412551321 1250 412550071 412550107
    0x71b0507030209090a08040e10030203070b04060207060915030506041d0f100c170604140703021801091d180a031106012102090a1b02010c11060105010e190803 70
    0x341c3c0950500320010b8080e03100841d002e01442e0b0302c043c40d13508150401c5400203e0305401004503a5600d2110070110243c0d50401109009110000c0410740e100e041c4000203080850a40c0040e00340701c201002405000707145241c500da541020320300011030740d5640e4005406021107841c0c485220283c0d0402d105c42c020007180c034000340c1d1401001c40d40c0260030745810340700300c9184015000c00a401ca40c0c00c601e454105c0340f401034103c000204003041c480398162101c411554152040701c04254001240400d8400e003081d548501780d400d081c005515403822641c1400b4400b00316a181d8000b1345c3d0000510754000010095070141003280c210b0328a00b10350b180c050040310255240c44407030300c11800001141007210540c031f141c000c01280d9012944000d982441102032000d410706092503101d1100942d5040351080c5065490320685c00803075400b6030070740054502c01c9400e8140c04244c02410060115136002503108514020994000444851540c034802584c42c10350000c0300140400681e401c803945014600c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 412552571 1250 412551321 412551323
    0x180e01050f0603030702012001050a05061c03120207080705031603120b01020705010c1a1f06140a140d2406021902040e120d061a0304050c09071b050703 67
    0xc0149807508404603141d15412141c05900d680100314010041d44100050b00045c0200c80800120112030145a03017910802c8440c05185592901000303020b240003100045060b41031a074400c01d030515500c0c000c021414001d4510341003078000840d041003000420071140116006001e5079100c42e069594044054a800d0055002480e2a00b01d07080500f0284150444d401c01600202a003510304001541c00300c050160544400070082e440c031401ca00d032500014410f03485901c1e22001040d17689c3c640050f41c0c003a504014108080001c240034107030008c004942c8511100c0c14448038104034401d19290900ca0700d210012180c3c28071642010105480101c5000c0c1c00088100140e115180e148c104d1313035800c000c1c00c00002500b401c0d00010160505a100107000e040e10300540d107450882c2c141e004a1070b0700030420fa000482c3c1d90002008480c3c11080d41102c541c41c1c94900d0392039030410740c48840d40e07080aa48c0051098040388049503409006181480c124140c0c5030503d0902c00c00342c2442034803607405100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 412553821 1250 412552571 412552573
    0x90609070527040c031a16030911060c0313060c06110c0615060d020c0309030c040c020a030f18060302220f030b04050709050408180d020a0303030b0406180e 69
    0x22840d403030110300c0e0240d0000d162100004240d52400c0e51542610b0140c001c1e40e4080c007905000c804206120380c210300001441d91810a94104041c0c841610407180c0b200c035080515240c40c040c0024840d850307280c0900b0044824036221010307409124150700c038640380105012a01c220000e840d60300000981a064014001004114489800480385201d00e09412489400880001d00c84c0b40009000c90b9074002d02500f403500b40040c8031920000c9a200600d080303a513520101d034000807440c04200b20609020162804d02c0152030141c0080c0d42c1d026200d07401070a10007400119a0751f01d218840045401c4a00c1400718950350380c44202070b0080d8400c80c800510880c68880c0701d001000405032070350490f0b140d444c0540540740303541c0f1580030103000a4001c55107802002000180c14606009103401903000301d100c00d039a01c243c4941040d008c1d0000c003920f0b00800f0807428440c0503a0326074000100b12034041c1030126030704070b03504006801051140c224101c0c0c1c03803000000f00401c026640c018415003080308 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 412555071 1250 412553821 412553833
    0xf01060215040809041505040c030f1a030a020105030c070f080405041b02061302031603111002010504020d0b130506100602150c04061413150f180603050603030909090609 75
    0x2190078008080480e000307004a8010007006225041030350201d80409610b4200481041c1c840d40000c09681e102400321002944031013178581c2c1900c0c688a1351404402160603c1c0e2078080e07141c0070030b8444d01c02c0b0710060b045c000c000c40041d4682c40e800c000c031707030110398808920b00f500e0804d4074186160b0b80160040502613841e1408514034100902410311490950360018841c9a030b52503180c0920b13080032042241c00d40900402011001203003071090340910b1048429a24201002c02070003c4000700c2d410007403c686c102014400542c81e03881c0720451079038000b40721650907a40c0700c04a04600100900040c0148076220801c4030403c05c6407161015615941d0a40b071425a40e401000500141980c1680d48403004000c1003015500400589100400342e0054605192959240901d2214654030000310040e00d2030501030800c2c0d01210418011815007840180043c0b03550582d480c0a086015400a00d5911404164195020425506403210080c2004c0c00c0d468156440b41d00c0314015110121941708134 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 412556321 1250 412555071 412555093
    0x305060105040830180913050303090705040e0a03140711130b040e0d05030c28031a01031a130b030f1c0203070f0b0604110c061005010302090a0911120f010602 70
    0x2070001c0300c490302c0c00e507102c0f20340042840d000c104021001809544404547d4904080010b0082c00a1449140c4c4075020b0000d5034a4441032006540c40680805881d8021401c080c000076004800e410a4000c1e6085050321410b0724903280d2124407480400e5a40540303d2a445030000c0e0050b04011445039041d1420b2040e8160501c50320303a038100d1411004041807050000407080350418002d0440c0d05211500609c0042055140d481206079148150700000e482d002e40701d4458002c060034003070303d00007882c0c100a034008001d2007001a030941303c0c0b0035201c1d29801c42d05400341c2060f40c001c50050031009090b6100c00002d506015518040e941c82119840702c4074010039025030011041e5030845800c59500c03070045400707039500302d146a03004041c0c0e61b006a54407600e8420f0349003400a4140880800c0040080c0d00b400d2a82c141c40355280ea204504260041200040c580c4074011071b00e040322414000807400d01c07808031101c81603000b00340e294410000940c00f001030359180c0918040c101c0b032198090310050b801d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 412557571 1250 412556321 412556413
    0x303060b04060c0f08070c031b08030a140a020a061d0606120d180f0f09050a0c050d0b0609060c0a020a1a0a0f2c01110a050a0303050601050408 63
    0x664420500421030511948003c2201ca0b07000e04e070303282d100d4030229241c02c90a541c0c10284026540080e00c43c141d282c0b1400103210034012262000e45103c8008506011010b80e00500861200003000085800072801d0307001980200702c1540d000d41e1009042c00003900d4400040c00c01c3c124070342c0c28445441984040b50150503c008d41c00f04810140003c1c01c0c0e4841b20701015104c900030220071221210f1411800606901c54100300300150140d0f844080c280c9251400940c240c07400546a03040302854842c21140d1550094200c0e1200c0c4180038010940c1d05844000403814040c1400301c94008900141c2c0d100c006201040d412082031003220100c5400d901caa1110040c0701d000c907800a02030208101400c800c2c3d000b00c0c001c0d0490400381c5011030014509500c0740f07040c42810901d00d00419003010b41c0034075940c0c021422540007112103000313014822840d00c442c2c1d82c6606114003d070906650784046038641e48100708890141c4540c00441d802c42c0d0034000344181c00c0d140640317140c141c1e5100601c40c0c48030702c032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 412558821 1250 412557571 412557577
    0x30604060e0c07020d050a080d14160c02012f010b03010c0507080706150302040e010f050903270a0803041217270103180b041506060512151c0303060b 66
    0xc0b41120300300343c4980e080c029075004101d070980b181c2c42100440c10004190700010164a0745461012030041460201e004640c1c0016004031107800205810250b000d0784030783e1840300241c0900c1d0190f000c00e145d00e014440e42c1d00c54002e0300c048125084031910300040540203c0c2080e0000d40080050010640c011903e600480070003e0480c1c008200c0c40c000b25500d80c020340030f11744d0a42d00d10b445483ea260300003011509410050866a51619407005140310180304003076118031703580f002c1d610741003600c9007403180303116407003042504140c003c20b030002281c03681e624500c09002444c0841c3d070f850391600c441c0b03150681d110300111140c654082041c200e40c04140161480d55443d00000d031002c00091190f82e0710581b03141d9000341015600d03000c981c0c102500c0d401080180e4051002000242098101650041007808105a089040820410003582d00c401111016804906805201c0d107503200710040e003a61003908213038005160580d8011380101054113031800b500c252004c00809035100d900c003600340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 412560071 1250 412558821 412558831
    0x100f12050d0e1c1b0603050402040b150909040f050609160b0708120901272901150c020406060f110c01080601180308070c1805090604080a0201021e030604060e 70
    0x744540710358000d107281215142d8046104421060084428031000d420704c5406500500000b52100c0502c825410303d482226800b000a035025045110712070f40035481c40c8030361440240207076440d10000b000e00a0303034101c16008640c000180d1390941442c410341607071401d031525508001005803c00091100c2c00394125204d003544041d0090510f80c840340344d11011000240080620b5490341411400c201c010100c500200380c12003400c800d01e8002d0304086e104001251039885580c240420305466031f10f180082581150074014081c040c01809910864202c400c2d180003e4000342090004200b082c0c2000800c100d61007580e6440e1503103201c00907001ea4402c0c0c000403c0340441c240302e01050f02d5500c10301c002d90151422005940f070341940c90361403168941c4144415501581c07031141c14444a0540c6140071204405000140b10504042d80030517150400900001c02840e4000b031403002c618002c1d015921400034424240ca0212001a010300565200301e91184c4142c3c1341c2040403607400c81c0c120280d070041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 412561321 1250 412560071 412560079
    0x120601051309060209120d030c0206190506060d0507030506010e03160306051003050708060103020301200d020714101d0102070816021c11040609060803030609100f12050d0e 76
    0x1030074030051507000705150102962074035001c000c081c00d952201044400071900503001000440300b032010040884460028050464000c84103100e9011a042c40318085104180000516600c071200010414400d842d003e0300c20909201c03c201c0318507055800340c1d11500c0280c0354045801124000c15866850421001c020b40c10400000d0000c43c06550120740d1050518120004080d1a03494881c03520708142e028800039030100005204606080c010302c080b8281c965044c043e91405034050480b0340c0070702e840c91a90707240c1c08500f81083c080824000288148850306940207510500f0041002d09510b00320070301c3c4051238450790a103004052080750020741c0c0200441c2e0034505922135100c000d800c8220b090380d03c03503004400e011180510781c0100c40c0e5035200b500225842c50200d0107000030390703500c1d070302408540313140c1703081004015000700c11250712901c04c0303c408a039540c40c0200391810480542000041d088a82004900c03000600d04401c1c00d075002e0811202e110340018011034250382103000460700 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 412562571 1250 412561321 412561339
    0x4090b1c0b0907051206100e010602070311060912010f0e0606010903060e0309030f1c0504051f091e090b190e091c030c0318020a050d080d02041412060105 68
    0x4200081c80242d000090758090310400d580d5500007580300c400740c00c900040c680003207091282d245402e221a00040440ca80092040e43c54890040e46401251101034055000d9540f981000c0c1d49500c111004c0b050300901c070340c034044103010380b443c002d00d403074102071509900d040c3d05c017041d8040016074980b10f014160f403104005030455840d04050040348240c16145e11090040c942507079018010420070240050081c022079800201d082084a000040c1c4000d11008100c20b0001b9190645a012002071400c9511905050888221107052003507000303031055102c4502200c07601800a8854045400c0490248001007512040007250080c0440056a02000c0f80c3d041083e842c0d032035045541b00c1d4110055a950303511451517010414602e100c850b00082d03840144408075070309485855002039225115504519103980030a0440303e0304d000e400e118000496242d010046110100d8aa0070280c180c19902c1d60b6641c0307204024240091740c6c01e8429102c09a020407007800008040d8101d40004040c054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 412563821 1250 412562571 412562573
    0x1b1204050f01020f010207050606030d0e131805010c030b04060608010b0403060b01021204030605180a2d0206040e100e0c09060703090305011b02011b080a020a02031e04090b1c 77
    0x11206400c0ca5214190b0050710b0620134503000a01c09890a41c1c00340c0003a2040d480d04070201801d01050521110038084048422001612040031340b002104808100154900d00c60301d40311017804d1a008010515801d02e41c4c1508403075810b800041080ca000d890130b100250f111401039034041000d000721140c840080c003040000c0f4901d41c00c44a161201030042c0ca000021020300003050794095001500e2094032681848138000084240d61420164840900488580c03540c1e05800e0100701c400282030b4400c003a2140010420300110000e22550041c1032555031031b51103003403440180089601007603104000d8000100c101a0402e40d900c2140390040052401c915901040841d0300042c4c016010131000300c40100009100748909800d60304030502d00101d5240008009003502c10440741d00d01c02c4115041d5103544190044031080d04407104020160b01c0d02c9207600308078658040c20031460009159140c401140d184964000d006480c1807200034045046a8001d020070002081503490f00182c6d40a9804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 412565071 1250 412563821 412563829
    0x6050d0f0215070b100501020706030b03030d05040201020c040617070503160b1c0204030f02130240060c060f02070c030204180c0b0a021b06030711030d05010b1b120405 74
    0x645140c100d140b025040548070788a138040c0200071552401c041c000858107000350368040003a0801403010b07180034480358a00c0c0b070109403a0300400d24035400b00758448000c9400c5a0080c8140c10100a004d8410001c030341d43c1d00311254660054030029007090294840c00b007014140841c0343c1e403007901c5a10303105040c03502c1d240d035a0b60503601111141c90380001c070f60646002c401e0745000400c01503000c0c08006021044500400c2101c0003e014004205881003001d2a18a8105207403911009002103880d40412211071201c040001003880460a01007a04c1c03001c13a1540c0c20804001465006800821500c00c041541008034464010040c1006040040410062030541c000301e40c1940c00c4440400e1000741552040300480042c0c1006034000404118088203550401640c2e1400b1440f0014090b6511010041201c034840500588100b0600c441d14050f011030400481d64682c101c08010001507030b4801421031a1303048040c1110140c1c400501c8400e5142002070803161001242d03240381d103814540801c01c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 412566321 1250 412565071 412565089
    0x80d02070e0a0e010911010810080c0103020c0309090a1d0625020c0a18200901030b0307030f0b010e071110020904180f060e060f0a020d0e03071506050d0f02 69
    0x3681c2c01601e40310501c90401007800340701ca08600c520049901e1031020000076141c070000810782d81c503c07680e80204010f4245c2c00280326205110a0031f00582c0d03000d091503ca8110b10400c0c0781c05820010034801d001e1507260541c00070424080d10100c2c4640302000f604c0391600c801d01036413540261045d81c441028000c01840106449001c6030040324561007079080031551200403030b0f10082c0c80030040c20486411a5044c082c3d805101d4804403040a0850031894554850154a04040c109a03503195000c00545040018001468100015170380f00442444d05580600c1c00b401070f450b0038030300c88010607109400f510030070f40e100c0c007550042c2550400c01140d880094100317142e8190f005031a50010403112841031200305000d401030b07000404105660418109940e01c02c034910006270300100c01c01801901500c1125045000f4400c0507942e1006440c81101078481580040103d01001501c13400b00044440b0261082010300b0703040c44416070301e0080101c4d91a40ca08082c14105a110340344c401882d2100030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 412567571 1250 412566321 412566331
    0x308010e0c0706050403030b0109081f0c05280e1206160216090905070605090a0603050408040504020c0c101d0d05192a120b190203090106050406080d02070e 69
    0x7190305020458403210140ca0080d1030a074040381e41d480700f402d40307944c1c0161200c0c041c0c000d000c01071103500303032209000d04401e03c12481ca041182d5a806c3da40c41e140c3c0b04100311040700e80d02d5950904000d200f0f080541d40078080d2100400441d0134000141204e0502020b401c082c000c91001501d00369890340d032100303401c2a0050210045019485001d404003800da20000b02070082202c000070694007034a4104c3c03a05455400c91010300c003040c00b03919260707914419000151091445c3c00709031900e032881c1c02c540501854109036809400828120100c40000886d4000c1440c2151907803494105900143c490341d8807041c0700480c032045805107902a0404024248605100340129180e40d50b01c2c3d500d001c2c0710142800119110b400240003101011001c1080200750040e943c0da1000d0705140c003d03030500d0350050f480d0081c0070030031400000c1c9071159072020b08807980c5102c040075552407034440413450003480980103040c480c529050020824080000701ca242111450b002088054184462208680704c001d02d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 412568821 1250 412567571 412567591
    0x20c0a0e0109020315100f120203090c130e06010e0f18030d0c0504150503011e05010f12020d09080301170133080d0804060606021603030516020418030e0303070308010e 74
    0x14a840311a100c81b140c2a4482c090b0780e1380e1681111480900070082022015900700040c011700c2445030002c8003160301c078087d00085900458650320044068007814182400e041075000e50000000c4043d480100da5210b042d80d55580659a51440c0600c40c070b00c12015501e085550080c886a40c84040552110050300d01d541007150910750748080d008040e07e20600703900300090010004101c2031542441ca1000407c9151544400d203084c00300007410401d840f04200204450030100c5a000c103a141d04859101da003211092140b4609030501c0c0607140d0081c8a502c0800c1d68501100702030710310610071031140603a00f942e201c07400d5002c0842200310180484c816000a404210001604c0b02c0400160f886402ca80d00d410b411440c00c0e040c0f040c02c940030795000c9010364001211b5121403103488142c0400f41ea500d41407017a2102411302034205004a0f00000035001850004e040e200601084443c4e035440d4400d40d1101000d20300001815102d02817400010046007821340140700a065044460341d100903074403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 412570071 1250 412568821 412568851
    0xc14011202040306020712020604033e0a02100e010210050405011805100b040506060a0c060e070605040305010b0f0d14030712050309430b1306020c0a0e01090203 71
    0x640e15401c0340c0c420360080b503c5581c0003803094200300c040003944581c0380f400d0001d04103a2400f07860141200c00c5810328201151843e1a5003000d096511810780c900100d0403441d5460341040d11032081e03960340038250030b038440d01e0f200c07441c23918041c07203107001203641c28040e03020705042c00000c02d0071000b518000d481140c15548030718264040480c0d035a404a6624000c0e00145199020f07192207000b10740ca04c0d50346030b0045003490f04100540c1c891004940d6442100e1807c41000d8503103041080081036400150490760107603003000113003d03074048060401e4034004c00080005445040800c03900da0b440d4401e2540000300c07450314602055180c8000c00c4503401540c02c0d81d186c03080c2ea68503440c55168040c84200420004018004221000c01aa8024aa000304054051000690b04004400706a100c0313826420041d10300c10709103000058848010514002c05945901012501000b8a1014090000103110303040c40316500b850510b10180c00c480c00000c1c0c07541da03a400c00881001035400100145185500c907 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 412571321 1250 412570071 412570097
    0x1b0607050d021005160804020108042105070b0a061a0c030d02030f0114030604020121090813151b0308060315040507051008040804210c0303030b010e0103090c1401 72
    0x380040030340d1050300d9001d0480c0300310f820a000201e03100603000b08100c00341d00c448035008a130400034458010780c0900303181b00195510303e040c1d64a401641e04902444402405030320040d50851b01400d5100c0c0700b09400c68055450107800400c0300c1d820b2240c1c5180ca22426141449041450002c1c541001c0a1098a1406038240e896105992007a1002251035042c080100140903202c92241f0446508501900c1d0030304107038000900c4405024210369070880042603c5070585515404001890b90006409880c2e0907041034031010045c20303218030914268a4001414554032030300400b1400111010020214440368030212240d5000401007509449419040c24229220440d05442584500000c1c8034030b0f4184014882c04071101d40c07c0341d0a0140c00424040054503403801d0314255610035009000d40003040040c0c07860041551000740c0340511108010040c194190040e000c40f9038207803100d5100700d80303280045040354000300d000340c2000c42c0400309000041d0094100040300b801403500c10300071401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 412572571 1250 412571321 412571323
    0x2030604141c050405130510030615030f0f050607020607050d09031205130501150f090b06160501020702090606032404020d020a03020903060c03040215070f0f03031a03030c1b060705 80
    0x404010b25000c03550124040181e40b03407510046003071003071400f800e003c2410891224403580245000c028207686d00e1780c81a41414500b0f001d110001c68124034640d10b24000e508064460340d412080076110b501484001580190000450750b00903072551380e03802e291010810b07080d00100b110800440400000309440c02240f0624001d070303401207008803e520300600c0f0740d1820ba401c41d00c005c86510b810810f00082000f85d072030700b12104003c555051501088807141c000000b480c601c6100c0c8050507001c09407010b90140702c41540500394070780c404c0d40c3c41e200c1525441c0401495000458101d40b02c0780703c250103915445000d8841e1075000e407001d08094100550301d04850141d800c4a100b060020760b02142c026a149010000d50390025942c48669107542001e802040980101000030f4104000019084040000509040074115009002861103000e5440c0003000f034424600c0c08400c401c9600071044491402000700c5031707640260310041410041e1b42100b4110310079a80251a8050428050384002ca50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 412573821 1250 412572571 412572613
    0x151e09070b031e0f0a06060f0219020a0e040f05071d070507050f03040b0c010501090e0c10020304050d0809010e0301290d0209160914030303010303032703050a021203040203060414 79
    0x1c041c4c156820107107010a020801c44185601c00b2042100c40e500d03280b812600800c0c81102100c041035040804c000d1030010504031603040d4400f09a2014541c2004148441d050041c0708032031041054444640c0e5400700307102c40e04009010207118800180100b1022401040146840c602c1401a200d80d9143c05000270b045030083d130b01243ea41c980c00140d00c8440c007400e00c1402d0151402000c10071410b010000c040d940c03400046900d50040310b03200c00c2d10080380e0080054800034600200403440e200300514001050b90005600e880c0450f030b0111400210b80703418000c22001d44030b40ca241c0705032075200141000c0d0701d0400d264029002100f900303601015840c1c40d444944246240302d0040c510120010005140c11111341c00680030000c480306411392980c000c8103c4c2c1c1125014a404212801e020400c40f6502c5405064020424084185101015042405003580044070740994101d0500301802815034803045030b00940c103403c4400001e002a480e00e4001c1d910a981000f250104941201c4018801c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 412575071 1250 412573821 412573831
    0xc0f0210020609010e0109050709022209020415030504021315050909010504110a080312060a09090614061507060c0302090d03090e0c0a0e130b03151e09070b031e 71
    0x82c004608000450f0424051501c095008000030040d6020355150a510390041e8042c00041903000221015055201e8010000660b9034005140005030303601791400003503000d4410950b40d2110b0b0100110182d01034403515100c4c6030090314807004a07107030b8007410000b00f095003c00c40c89401910400704c0c0c00e803140b02e0303050703c10101107000242d142001d080042849400700800780c0f00c4c00f1401d6081c00404404070955505007900c2c0740403482030310354100080c181c0350386030049a0003030300d08100282405440d0308a145500440c950804030f0b5207034107084c49800e413000b82c0c0b1071044100421044c07002070126448400d07030030980c3c5401403d00001000184a0b94040300007900056062201030182c40d04040030342c1e0708041e440380c043c1c0c605881100003600312a2100c43d5030744101d00d00003582400b000c15410401520034000c1c295800380c191015648040f44041d0b450b442c02e424400714481c1070b000000100d13406072402c4001403d030281b91952502481e840201415107a02d00304001c030003042203030381465000d5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 412576321 1250 412575071 412575073
    0x40924090b0c0301050d08090102070b0304060921021203090c0a03150c030c08160e0a0f0609050d030e060d0608070311030c010f200a05030f1b010213060c0f021002 72
    0x182050800c028201d8000d0b10400d075442042004212550701c05c0c1d1400310a41d4409441038481d4020300050b800c20f0b04680c003122420b01d00008100c108513281e8860408548607001000c03400c00c2e01c003411a0751031100d221a00260344500c00503554043d040e0065a070042491040f214240541004103c3d0b80c86039500887d040c0c02001444140c1c80e07414060b00380c01201600c2e081161500c1c0f0b034001416603002a200c40c54032880b10000034403e03845026150b407094405403d1003090740c2e481407400c0712040b031807280c00c000583c0100c0c0420680b81c01846401c81c070790580d580c11000003696003085101c0c0c4c0036006c10401da03a0395520000b542c003c10f00000c801540036001009120304007034207041c00d095182d6001d46c100480d00050400154002c0c00480882c2c40070f0001c1145101d101c94058500358003c01c002c0d00511001c103210861034200d00040203190100c6840e0010010170f0141c0d0b500784d00450f134201c41201c4a618041c0940c40c49030500321768043c05441d00c0500303004660040740341c194000c0400300c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 412577571 1250 412576321 412576331
    0x901030e0118051513020604030f021c1103070503071208030c160302030316110d0f360b07031727060105040501150503060f060c060106080a0c0807020606040924 71
    0x581314200002c140d002074640141c43c070300d60195001075541d11a0f40001000300c0c5a045a0a09649500302c2250a180b0200a60385002980d410710b03403408151131104501c04d01c00d10602041c01d003404606481142d002c108000031240440e50ba103111a0401410f40445880c00d001c0c0c2c69254040d041f01c81c0f1098000d401655603818018106c61504c10751700890020321094038000f2071501c0c000280c40600c0212494008209079901d0000c1380c40e0303080c18032050491710001b04c00015000103480110030b102c4000400700d007890381c1c034100a1041c0c010400c0c0900441c140e03201103206110081d100e10351201031041c810707000c0000c0000d60084074030031802a01c02680300c1d100510613403e007841203902414412824511804840000600c54440103021034015542d00c070319400346455040c00e039440400c5e004103507101580c69440041c40b5150466166a0290806030160449030080c0710541c002c4c10b1a502400207070359042c05000240c40c20384001c40b010342d000810000203010070203011005105200021503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 412578821 1250 412577571 412577593
    0xf0d050a1205030f101809150212060a05010201111602180a020c01052206110409020406110105100609050120030f0414190302090408040305100905010c03050c0901030e011805 77
    0xa1030900080507241781441c03001e024000c141c00994881220624000046105a003a1034003034087e40e0b90300c01d00640c072400400c10030311020091040920928080c0ea080e0a00c594550049007a20a55220b600c0c1c007140401c81c85202614600d40d24040ca40043c06580c04410b038200a081d5201080b00c0d030303c0c5c0550780400e04400c0c404007070040301c1c2c02003082030526030700d0741040c00e01c0146100c4c1c0c9000142066600c0c8401f01d0900280d5058500400040500310348851b591400540451044c44c414841546408005503a140c5c08040f02c5007503e01a80e5248080c40c14040103491001080c00d600f40501c80c0480c100c00b0a2204200601c2c40046410f40b154a035840c0140104081e041000321600c80c00b850390003003c40c0030103414444101d079012242c130b4010ba202e90601d0070003403003280c001030124007411401e100c01012171b030001550a48a10004c001c2840304100071401c0b140240c070304215241003000000c0b11076209400c08101041c1c080000a544152244165000110880100c449070000c00380e400d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 412580071 1250 412578821 412578841
    0x4260f1b1b060a0f02190b09150c030c0d1b0e0a050406080d030203100f0f0303080a0e1b03010e070e06090121060207080f0304030e100504050f0d050a120503 69
    0x4600c110407084101100415071001850b80e0080e01541c40c20000040c001010710382c070030032981603040c1001071400900502810815910107080b1038100d414031030070441d00801085020917500c2801c0000c2c0075410b50b1291001d03000c3e690b0000101c054555200c6d500d00380c41001c004c1c041181092203440f00c0141d030190406000b2100b08590052740b069140504c2006414000300c0d6840461026140041c1d0303035650b510840441c0e421130f4004428038200d20358080741d0358192004980550740070f5101c80c003856841e00c0b2010161462000ea03840d0a0300b06840360b1000245c0c0030714114010348014004600240007400b41e0385819602e50042d2560801c034414002c003420b0846403907024200b0f0002c5030002c4a0f11316004507900e40c0f010720080000ea8002040c000348071850059602d0901d0081510343d990409040081040300d100050a104405d0f4844142074540900d080310121384010f000c103800741f50580200004d1500c05042a502409180c8491000444000b20b1480d00c079819220780303440341400a486 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 412581321 1250 412580071 412580083
    0x302090114122205061f0f0602030c1603020d0201080a1e021e0405030714010c0b131a060f010320040806040308090a03120507030b091006140304260f1b 67
    0x141c100c3c01070b6110004040f640102c2e1941c0d000c0c4800306014064892030b0004240c002c001e610880303030314a0407400860741130b038040010000c081e8200103c0c0d40c0340607500103e614904031403200a500031441c0110200650007412456405003a0300b10000703004020101c40c0301c1700c00303c6c403006040a607400228400e01440c1d201044440d00308009245040505120201390340745400d008501800800c0c41d400d4555030700c00c160f03103410076a00408809540c24101003034003218210202c1160205d00d0801111030b42c40001c0307101d91007148000c0014508042010040d402000783c4242c02c2490216401964642041c1c000100700a08900000349514030f001c2c20018080380000e4169103054018190610200e0343c02030800b4000f036801d1800052549030008150010301c400e6224641114003001041848554070000104482d010b48070210040300c000009004c61104a4000300305011254405894100908260481a42464041d843c20201d0309400c18a60007404d034001d20f880801d00e030307101602d50038442 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 412582571 1250 412581321 412581361
    0x40c0905010215010e0117010f02040303030b030f0a081801030902031605090a020708040e2214120405060f160804090b040b01050c1b22020705161401030209011412 72
    0x9103070480c0d4100241e0341701c190410302c18507460030740311040d1640c42d45080d80300f00b14000100380110741d2641d4900c4c0c0034018201c6079409a220b8014100f8044d500a4045000b804c40d80d03001c0401ca00d0014480028031b8440d0005420604050f0747c0d482d0080161001c102d090b1a000481e8100c0514a01c0c00c410803105403c020002040e081c018000400010b40b140140c909584240180d52400d5950780d074042c0d0712081203006640c400c001d804564040c06491501e40040b0441002501d07031101f0b404211241c9841248111a007001041142d102421601009406d140e03421480c01055945107454a03c00e9030881d401c5421800d030351381d0010074249464459040031140a0230074a0424148a105030340fa0784070f100d418141c50501d406d00403581e41d5140707603050000b180520040f07400b105110401c0025042101c044650703210341c0032002c0c001070035124a03c0c11118481e501d01880803141c001140607412030342006060041244040b1038041e94a8082c2c04449070025203d0075a01d04403c60310003901c03540e50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 412583821 1250 412582571 412582603
    0x806100602030418110d150819020307031e080a030b1c110103050612070b0d0501051206011e050d03020f060c0313060b03030708030f040308060906010c1b05040c09050102 75
    0x400c000100c5007041482c81e19008400000707070f1000c2c0c41102925407040c21080c1b259030346403001840411900c0300595040c0d6490070110340c060f4803900049160107801203006507040e44030721000c20000f0620f000102c40000d04400c0665070010325640c1e00100d0700305440b000c01190f00c402160710141003611940c0341004601c40c40d070502282585500c4032200001008504250f200c00010320503403200c041117011107c820040b00c101c0395903100301111607001440da20161900b04400000c4500c0c0004c04540112014405025280d107003d10101d511000b920b9000c8008050000000307865480b04000c40c601406a0090a812038401e40000d00f0508000e104810095080c0103000c410350310030b07612400107a402140099506000c2d00042d10314022210020840040042041040c030302d2410380d1401a40b180d15840e000c1c0d200d190411034130460454215001681e501c0700d18010840798281120007544a0b1100c0d03524640341c0f0301040903202a0040300000c02d41140041003e560704001074410500036907 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 412585071 1250 412583821 412583827
    0x1020a03080703090302070b130306110a08010e09100c08190507020304051e0d0f1203020a021005180709020a11120f0705030f03100302090c0702010e1c0c080610060203 74
    0xd58094200380001d02420201039036495030318200b45c0208000303405420301d21034807611040c075103009442424107070004a80301400c00e0101802440888103680c42074481d9150624981c1c01c10003e20a065001070580e21a446000b440501000e0307207100700c02c40c140303103aa00d403020303881e119685840c03c09241c000180580e103040200241340794080261030540d5800c4a050ba40c2070802e0910340f0710354035403080c040d80c0410f40034004010422802d405100c154458114a401c12890040950803400f80100541c05078101d01c14240c00030300c0a43c8150b512010a1f1031210f040110702d1480b900e450300540000620302d600081043d8803981026020303110145034070003400d03a03034801d05401001c1d0098036600381c00074102044038000c0280a0041e0b072090340c00c100d6460303100c4c030f40030401606100752071001340d00450701000822540c8004000300d640c00b54041e1503500c2202d10075403d00144105000c4c040618417407480503100020400b03016403000b000d0385070040c41a4107004107180c1c5c1040c00c80c0e0102096500130 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 412586321 1250 412585071 412585073
    0xc0c0905180613080a03110310060f0801080607030f140a14011a04290d0f060e0114120c120f12090d0b091903020f1b0607020402090d141b01020a 64
    0x200d03044000c80f90303010951070749072003112005401600a0700040340882201100704a14000342605640c102c0f4015601e984c0260070f24401034400d00c01c00c3c000d08009802120001c0e12090281e0011945002d41010000301241030003503001c0320a2083d240440c6d1103446003000e4451181da140040e0140040c01d0305030004420f4a0101406849644501040d44841405450307d000c031003a50303d41c0c1c0c88010820a90384203a280b0300c29000b404034080020f50319181500104070b1540340364886041e6031248688010144101b020484080090071840c002c511030300d500200c2e01c0e241d030041074040d80030481c01484e000c0007215029040001100610051040a000c108004d95801c41e02c612100d4010000305c4060711041d1308542015122010f09101000e02100e00c0200b641c0083d02807500d031440c4080d19054a0402101101322048038500ca41c0b040040c1700200151400f94004c00141c000144210401d904070342e6400c4074000110500c16084d0050703025950b500a140400000590091002d0607504860b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 412587571 1250 412586321 412586341
    0x603290603030a0e0607020301151d0c07021c02100c0b0109020702090403260403110f0705060904020d0906050903040609060e132c011d030f0a0806010c0c09051806 72
    0x1880f078080f402c001c0d002032000c215807201030459040c0c40e0041d009000424a0302c03900210440c0c94480c888031911b1000c6002000076103000721500816030410072071b250101d66000c010844050740881009090701617504001a6660300600c0d01044168a40e00c1e007068017810002103900d8164000000c0e00d00403c00c41c40181d8507500300c00c1c0d105a0508010883e5103030408044000b50071554041c954090b48001e100501d03801c0102c0f80d4091340c04d403048030321a40030074200607120b004a101e01504510103025484140c54903801030700d05d502c0203460005403131405071100390603100150780241d241d4000160610480f9800120300b8050070303a60900102c0090614045008044030f13506001c4003507170b00d501c0c50b0090745031a401c510300ca0299180c0c5d49040580d0520441c000c040c2d00c4080c13210100d81940010900001009032a04c2c0c032941c40146003030088076601603421400c014000d40c104030368105003000003a5240010b801805208074001924901091030740d0082d812807544200700c3d8400801c0100d0381e10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 412588821 1250 412587571 412587577
    0x13090509160305060f0c0c010c031401082b020c0303072108070e04020d06030206030f070810030f150e1c020601090b060306041e090521031b0c10060329060303 70
    0x2102d0175044102d90f15104070311110301a40028130029424882545041a8550880950107000522a840c0ca076650b610103540c5109503034075603c0c03801103131451446c0b5614040c118811200341e401170300d1540f641e40001908640c001241110114482a0310740b0600001000311403540e5181d0814107010b0420010150100810780c1c00a8810342d00018980109040c42d0070001c000c40d070242c003494a0b400c03c10240c01251100700c5d0104005040040061140d2403500d29800440e82c010540b0754104681d91910080d1101d26008000d1603615003c5890a20350100314280c9680082070501490301d175090002820041e0690250034a18204154030b0319642d00c0e40116604980119400580030b0b1400048499050040e40c82c0c548180c6040c804100f8408003280514040c0c660500c80c0d850a8030700e400c01070740c0c2d00007661082c2c603003003400c0345665000000000402e20350410500320f41005c0c4000e0401015900190421100f1040d40110000e10f01d407039040100300c0d2000c01c13000400f54540080480e540380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 412589928 1107 412588821 412588831
    0x7081f050c180607170d0c0806011407170703051314360c041d07091703070813060810060e0607031107082a090c030901021309050916030506 62
    0x5074850400c8034400d10050b121103015072f1011940c02d05c42d400c0040110b0b1103072810b5900000c00071070f50b0054004140720350398003903555911411426006000364005283e42d00d1205003421180d566210340101038031000c0044d24a40b045040910041100e629a00340c41d5400000f0700c0300c6520325500420542d4024801101c10610020203c1a40242207800d00c0015034101b0301403100e110ba507078a0802402c0c40f01d003103d0504189071191a1550b105414485880200c0e40e8208005500071905542c482104042c440d45180f034444013908a20400e0041c0784aa840020340d0380800d401513181c210195544002c40300700c291942d12032030391000f8805881341c4581100c1b85901113000780400031082c40c68080c00840d03d41c0c441c1c48840305260006001200c1e195001d0160000000400900100400c540000820f03e03042c4801031074189034001810008120121405002040e070001e0015001 = true := by decide +kernel

theorem cover : BRFrame.Cov 412410071 412589928 := by
  have h0 := BRFrame.cov_init 412410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 412410071 ≤ n) (h2 : n < 412589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
