-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4599
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:08:09.173664+00:00
-- url     : https://prove2.me/submissions/345dc307-2213-45f4-b79a-a5971b6f491c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 826978417 ≤ n < 827158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 826979667 1250 826978417 826978421
    0x14060a0b03100e16140a0206010501050a020c040f050907060c05030f0702120d020109030306050a140409171605060106031a0409020303040902210a142a0406081801150315 75
    0xba1a902c4003c40203482c290398243d507107155640901c40010b52180808403801211001d8079000e82003900900745980c213110045030942c00c548030b100111322401c00d481c0c441d0b8503140b02d8158100e08a03000450a442d0103184c5030710300481b5610030000c02c0250401000403600100c2980c01e444408074145a98640318000144092280c4001d03406d98050707800500c48450f01548010941480b03614240b0209994008200394428184500c40304c1c08038080100c0440e14166004c2c03125140318002c0b0800e00b02440c4580c50150704800c00c00788480050024a00501c1420040c8500500746840c0a02c6014090782c60350070004114030380c01e800f442c4c070741c00228219035060003960003070b0002100864031440d40840003408800b05240035442c01404c94085181c5c040e05010310010360034407180c1e045c00f60b21020808a0100ca5940000d0070f00034001c0e4a5482c01500c0c0d10041c002010550740d005441d007001d01080500d040200000b03501c6a141005e0440e0081545000000312a0440381c50300752402c1a144101c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 826980917 1250 826979667 826979669
    0x105090c0f13060c030809070b0d050a0e03040b0a080c0f16030e09070302040603052214010204050619031d1f1119020d110c090408070210020c0414060a0b0310 70
    0x10080706595000f10f16107074400400d8266501a42e03601e241030710750824050b00c444aa00070f4120481e81040101e0180e20750b50031050304071500d0540000d240041088290450300680c015208801000809524a5902088054102402110407450309005003c0b4103050300c6880205000a59001e140c042813500440120b0b0903048007426440061400e0071004000b50300c103000e2013001c24503040105202130420000d807004502210f00060014041c3d0702c5a181c0b88540340388880e420342d000c110100b45500e50310041e20f01d030000418110309104001e880074061700c286c240b030011850443d01e003500c0c146a0000d011100c112140714100b00004009000d40d02034556104041c200345000281246158111071000c0b01c000034035402d80c4c000c1c48110302c0031900c948213103420300400e600c01c02c100d900c2841c02a0040790010320501d0005c0c03410340b650740414410080e408440e80581c0000007103a80d24180350080c58162004c3c4a42ca008034a0030000041410304c580c00344614800c004000515241403141c1260 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 826982167 1250 826980917 826980937
    0x3190902011e05030907080304210c170304030c060519050d2d20030a180506040b0108120a02030f030a06030c0e1b270429030c01080105090c0f 63
    0x41d010b00d05410001c2c05076402622a920b90744904030000552040120648094aa20181000c08031411201c404105880203605417681d0050030030000e40010450248484071100001942c3c03a0391030740c01c04400050080d8888010300508100c0ea4440d03450903460080e50f41090708045441340c01000f5040010078540da11403110a1001224102c43d40c01041d840c5c01c03208400307805120305108104c4e806503806503240c099030031041c00d02c0420042107164104a1070810398203902c144860f941e45aa40c42d009050f2026100340b4000e00c01803092060a02c061442500c0b0718501034600b000c181c40c000d69a00c95007070121030200c0e0101c08204080c02580040c001903801034004007440381c40b03031101c45200b00c06841500c0004008003a510403201c068042c2c6464031210701d1110080c00403151982d816007500e00503c0e501c00e42d10b02805d00100c95002e141010213000480c3c0c42c80400350b0100780351801c240401d0f1035051141640041010f40c2e0307003160095100844041c0541c46858400503104070340501d840c20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 826983417 1250 826982167 826982207
    0x20916050d11131a04180b060a0f0215010f03081c020a082a0f070213051f080111091c05011a01180e180c1509090c0319090201 56
    0x6028200b90001c003420809400d1060301d80e0b41559002e0042241e00c490f961865940000e01082054200740e00c120085060b5104000c15003c81400010b0310035480340c0000008102000c091200c2254104404c000c0344030156072642c500c0d410062525409c41c414403000300200c00c0090f906621841e150500c004440581505648982d0020400380170b00c842100d00607100032880910340d21480407400101e5110b120010aa841c00c0211004040135074000d540aa0f0003142202031512001214401e480c0f241080c5915203e601341032401c011504400d55120310807030381c106001c107403802054a045482c8c0820844a13103404400c82009200d00650f0307003001410b29482c0003140ca0343c6049400551502c44000d1f614095541d020440102d8050214018031440c0324042c0002040c81602078889200c0d00003480884038900300c0340700080c94002401210004004010032344010908004018540180d0000300391811450000e2000c200e4464090818203c19180d14801040d03901401e04020071603100308030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 826984667 1250 826983417 826983431
    0x340311040b04150c020a05010c1e140f24040309080d0203041401030c02060f100e01140f03071401050306131802030709020c0309040b03030c030304031e0309020916050d 74
    0x103041d2608a4494160040c040508651059109844400c04644e00404902c1800d007070400440708540d0300082240c02c46c0885113512842e04a91418540d03a9210f56010b02050109030030f1035003003140d8000d0382101503106010780000c401c51088a00c4200e0b58200414661703559a060031541b94110790310804060103038190003070740f41d507000c0024001e8503601c0c0c00c0700f210f04021100450840c4c60144100006030400c901081042d44001d40e441d40000d81c0140403103015440c0d0403841038222007a4803002004200800c0000f0508014610b15403910b402c8004e0301c04e10745000141c5108c0f00d04056164100030b00000094210740d030324141032002d00540c0714100184500885030742022002c16809034402d206101000484031060300031610f403010400e01070b604004440040c00701510b000e91b08260706002c01e2058006280c010006180729900070f50350190111640d14074002810903042d07050041500303080070385007d43c5032110b00d40e070040030031000c101e03440c0100c05003181e00e40a0300005101d96800c101c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 826985917 1250 826984667 826984679
    0xc08130b0f0a080609090a06110405060a090e0c090a12170d05100504021c0504140604080a080604060605070305090f09151509010c080c0106030507170634031104 71
    0x81c000c2d140560b21480f21075120141048101501103034015025440388903414009111a000f16007400300544605007016102e50000e500d5800400c000350014502040421800070b000910302e0700241010a158608180e49012618220960140076100c880c2c1030803c904019499404c044500500d481c42c0b5110241000346401401d007d039040743c0c640c14800004943d6140c5403089489a0000200d0103070040c0c44400c0040c007a0000501c10380e4600105210401c10100c2807108900c40c900c1031010540c0c80c038007020040c21042d030190205015618000b02881020341103000c4690154050828644800e164800603511840403501d9a8001c1030382c009121244040410200b2000b0049607130700c0c03c111906001000e64040d41000a001480e41d02d807403c04112860000c202c2c20314030200100d4000c0e10381c0c985510345403450380082d090940b0700b80b280300000001c4c4841034002d4040c410281d0b50b14640c016954800400140003600d282070760314000b00d6071307011741e015008201c0d00c1165140c0780eaa80740 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 826987167 1250 826985917 826985947
    0x3050f1213051b090105270901060f0603060b070b041b06050904111e0a09080f060a1d060411061c09110a030803071d0613051309030c08130b 62
    0x104044800d40305601010798054000c0b40c0d961030101001d0420342c2076a10340001c0104440c900b051042d890701106110710071f1f040c880518913104e410150b00106400345481c0c8014401c1c42558014410136146c00d00500070800304200315440c041d00704c92114015126401d000b40c240d40c1c00350106541078507a04000807440d03001005000203840485d01004099040d0048030a98424402071400140340c1e480421798840c070f00006005914a50f241940c030076a101d0341480c1c905400010107095035070005d010410000424096810b02c5001c113003440e80142c81000b20596152000b03040100321010045401d10ba03901d400c400c0e07c40e10528036412089035a800035003c401421980c10503940a0303c614015055400c00f40c4045040341e9121038101d18580c0c4d4181c0c101d07080b400c0c07445010010b6042e11482c0d5095a113081c05420000141d030040000d0505d400200042405520304046000b8100010840420b0b04103010030415500512080d03503a4000800244802c1c850b500f094a44610128011545081c54 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 826988417 1250 826987167 826987201
    0x1c0b011a041829010306090207080d020a030e0610030c0609080606040c1413030b010e011a0a03090c0602060901060e101e030605010e04060b010305010e040f06090c060201020706050c07050a03050f12 87
    0x3a00c2c02c000490301c640c8510168842d45202038646a2b007006602d03000b03c00780c4d00904e41c6095034900001d401a802c2c16044c2044001c3e100020070481660051040c8040f04041d103008150a080c0605031504c2c01105036200c19000700141c2c8600d6440451144050150b1000d000380c3d11040140750340c500341e203d10300300007240d10300085d22a51680710001c1503000125048a0507906100a6600b20380250b182c12102584450f031420101034560581c240080c02042070710019203440e8001d06030902d41854041d08641d4a5800b0304c0c9012004014031545d4600c903041441520107030210000e1100308480401d2180241c1d03440104150310700310000039203400d00c1c01e035140520320880050000b0354190004405482080c0039030305a110001e400700b0f002445480080c0c0c075081c030858010460041e1905c51781c5900405d68451000342c0d400159940801c1313210321845a101c0c5466050314104100d5898059444d00184401428404c1c00103400c001b4030384a400392413840742d0740a506c001c01d1402c1d141004002003c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 826989667 1250 826988417 826988419
    0xc0206130e0c070506310b0a1503030e0f06071a100b03040210031e0e0309010e0901120b0c0c070312110c0904060513021c0b011a041829 60
    0x503140100e04908022000c80f00700a4102e8018070302500c8040c6881180420454546208002070700b500f01410200755050b8030140c001c40e000f00e664030704140c0b840c05407140303480303c00a400c81c1d030f100c10b00000390411811017039000300f86d4051610814038404101e00c1d200e9040c0141080c0c150f03400f803100c2c1c225840300f828030601e440b0300d5509800340c0e108411542c0d400280c5009501502ea105100c2030b140c40307503012030b0424032404401c8074407070050032545080b951444030505a54100280c16603c55800c5918441c6104045c0c51a5010b0b41c0341260202d81c03095100d400a24800800c0b0103d1841300d840403e4400e018030a2050302c2d5081e589290a0749840c00d0204d510780410b200103c040c0d0741c4100440e440d508140c024084210035a1590303900f800814000f4080a108030314401c0010160712403280d0300c00e03c40d101c22468102c0a0b55401c1010f40100168808031124401c41e6030900c076490750105907070864a030014040a06503184270311030b01509a400080d50590f40c80400900a1003450039500c0342100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 826990917 1250 826989667 826989689
    0x60a0e0a090816211d0a1203020604020f0a0612050711070803030a1419200f09120604050a11031c020a031d0f0d02040609050c0d0b01020313050d030c020613 69
    0x34a0310b00058031100003218500c0410074150091700f03000e80c4451402028003006103008845600c0d541c008403001c0c5c0c441425070041e40040304000441c10100f1000005103811601ca281360792600c08020551003c000800c0e2550b51a031000c5840da50040e0035110a600020086d521100c1c1c865608550703940044400301036483c00e00298084c1d221540d41c8503409560024100d0301016030102c1600c1c090311201c516607807494090081341100300c0f490070241c0b2003030b128820502e0340e4510080802c84031800f40b814400310340d08040103200c0001e4000441412181e480040c07203030000c0e2078000082c10300380349816541c170381c0c207555020440c0300e80c0c0450005580e0f03120381c90b42e0840d02a94004020031401100315030340c10180c0d081050066103021903020b00c0191005101140c1e985d22441c00c541960b5055580514480340400c0a40c0000c50701c1c001d2b4448600300784021428048040d425040094180c85182e002d10064510107007031501c514201c0c032109401400c4a0303070380c41c2c9042030a036101078180320b2075000c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 826992167 1250 826990917 826990943
    0x1a042904020f0324040b011407020a0e150310020f0702010c1a0c2502012309031902130b010507080702040b190614030c0f0a0210090b01061205060a0e0a090816 70
    0x5c070782889450017000040e551407488a846070076501141d40200c0017640e01c00060320000a13003904808480b40314446c461071040100212006052410800c40401c00d80240140400d0101030f207604151028241c091920030076100d541d0506500d1300c04802c80710300f59081c1e10420040f000a403035005011014060300d02c0114040c03c112484020815208004e0000b40711b10034410103c00541c4858149085a0740c04525041c2c407000000c0c60043c00d403050752410902e00c0003a03815031400c01405101020306290900c00d2040e4240000e080e4030650400400605011038044255280da6101a80002c0040c0c0a805c0c55501e4614200c0340020510a240004403040c00c20415100401c043e43e01a1043c1500913041c0000084402802d40100700503408610600b45000102c011030b026092009000c0e51841e4020b50500350002c01d601f40044280680038100401d110b120b44035556410100d8030b1030001c00e0f207540c0350b40380e080d40602540c410180507040080b4100300710200c1c0392002c10a50344103029031b810364 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 826993417 1250 826992167 826992169
    0x20c0105101202090609070e040e0c04060b1219020403200f0307211b0f08061005060d0c0e04240e0c0a0807211a042904020f0324 57
    0x38000902c00250826144004540141800500c054000300d03181080c0003c4c21140001c141110080c10341914150301080a40080b810300b4858036000d0701d00c4044030352909500070b05100d0480740140001ea4454084c3c843c4a6211220b681610040c2d03500003608070340e02da442d07150011261600c00d0f070315114041c02c56410942d0310b00002c5038801c45e07d034040b480900c00840c41400505103031981d4155117003030002e034041400d900c1010140c0c0c00f500355202d00d0724519003404142843c1caa401800d03800504c00c600c900748016070f200010b0380d14000d5440d10229091031045000c46880006006107a001030401c1e8501808880c1841809148030b108594480384690354643c10035004402d4840402081c010841c554905104001d0300360b0010403030400e0564a6440660500c0340c80c0002c00c10015180d90340408000780c02076052240c00600102d406000b2032520401303101c030494601c41d244904a180e07461151180e259501514590200300003126240d20300610039591103900705407071541c1c01d50008000f10036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 826994667 1250 826993417 826993439
    0x1b030a0c170c01180b0c010b040207080c0f07030b0103060e010e1b1807080112050f030a0305090105060a0614090a0815060102060f0f1909052d06190c0c06020c010510 73
    0x4003210f0841c1009886241400f1030b42e0a83c00388214180341e5480360508c0d820380d10395000502007144520b007500d955120006801e81012300b620035580850b00005420404106115030060549400032400035102101c8243c80d0700611440c000c1028a0280a19200100d4000180198010026200c42d50503488045400d445444100c4070500805c0d05c0c00014400150402880c6020310301c158100c800d0780d1101384400340384d504004c09440c0029112802c00002c94020b0141c80e0700b01800703071464010142403180c040d29101c203044201040c2c90003c608119184e41d14203c2c1c00050100c0401d0751003803490f812104400400c2116181d0241c854040492266072010f1502841040300000d00700190703d44240706001ca81c52140a06003032a1580f10140c003080091101440c18140f521610b04800881044548581885140400e058220008200c11840b403510100006e8604050004801a000303000343c490043c0210081c050360707c041407103144420154811070042015201000300655540722001c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 826995917 1250 826994667 826994687
    0x6020304062007031b0b1210140d060203071701030c0303030c08010b0a08060105040b030a1d0d09050f0102030705060a150f05010c060903110d08060906040606021b030a0c170c01 78
    0x82c190f000301000c102250101040c0d45119034105018007189aa601d01c080e941d03080b000203051281041c00911007004215a2140c00804503000301c100002c600100050314180001c1024022a400000080d0041d104002d0300c80e0195440d025403d16503101d06121901003042d010890229292500306001c2c140503070700840c100c070040c01089141c02c0c010242120500d001620303d5043c400d0030312010030141c217094003562241c89a02e1001400070394144805002c1d0400c001c0c043d2854000c40c1e0440e003019403200700c14066400a40343c030f5808860200040b0710718491128060954091038080c0b004800864212850008080d840041c00b26220482000ea5100500c121804146546003480020b001a081514018040d0802c40444c1c951501d4250900410706c035584c002900080c1041940e00d082c1210f2500150260ba04000a904103c00070307549503880c14500200c84440e40c01903189503410000025087e0340405003651040d51042d05071000790000140b00868090340039031060075445000b2a207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 826997167 1250 826995917 826995977
    0x190e25050a2d050304020910050d0f0c0b0a110d0e010e0405090307060203070906021b0607060c0c0611070c0f0806130609210f080c03130203010b03010507080f0a0902031b04150602030406 82
    0x2cac080d65590f030203885d201d8084125954a24150000303040441680500000c17002034540d65142021020000e041031032200000301800303060301440610341d80c020640c0b0065030007a02c0028542e150f4001c030a166000d0444c008280314000420418826400300c044000c4980a408481c1846000b12903001d04154481c1c0240c4c000b031082c008007000c515960440d128040c924105010502160385840094500d90040d940700c0c0f081c002150820404490801801095182000b100243c1400c2981d602c0d04800740c00e14000d402034401e044144141ca900043ca05684a44a00886085480d405c0c51480c1d0410b402c0001c80c142c02c4200d0400d42c0140e0f03806101c0d01035030301040d2559544500c0803044000101c0180c0e0076640c2d4079540b146070748003441040e00131700254860700500e01c0d19162100100c0c0000f00104c2c003060900ca480401a1000500d140b0f001d081d0300048602d44000b4400f02d0000d051813950300603001d261b4540010103030f4002c0000c20540d001551040300c0500c007117441d450071741c1a50300a9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 826998417 1250 826997167 826997179
    0xe040b0703020730120203090304031118010306060317070f060c1403360c0108040f0203030d0b0418110906190e25050a2d05030402091005 61
    0x9490354480d60040203054402d002020074400c1040c0c00007180d49104254110310300080e076030441400c1e00452449a070005109081d40f4610301301e08015102c0c01a0302c0000c05d4401e4600b00070f030940d610707015008640c5020000b802c1c0c1e03640e0b4906255005d000305100603201712614a46070701d41d4031101c0e01100ea08036000504a203041d03e4696528000303210040414040100c001d580c013081c80b1000c1e0003140a5811490540300c0c12002c034800300103031040120340815400c0c204040d04041c90010411818114090800c100e40f666035091070150080b916100175030502002070030440591081e8058103130400309580c10090041d107071020b11846000e048000e441520312242e64106407901c2c3d49041e41c0404050040c41078080403506075000070300103400545e4150402020040b042c06160020900c04001400800d205003400070090a18492a0420820014690909002039040110104c00c821010000200071100c1d004002c00507002660228440c0300000b000c01c3c8541105000740060324802030030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 826999667 1250 826998417 826998421
    0x51503010b270402280206070807050f1c0f0b1c08030c0909040b0117070b040504150503030d020a17091c0c06050403080f090115050402090a0504020a050903070e040b 73
    0xc0110a441c2d16a40164450010042d280c0e151118009043c10b070706000c0061080031194040309540e401c07551000c000310740c805001c102c01c481c2e021204641280a034201940c0d100c0e5a071040850a01c039416496981d1408150791041c141000c0c1d00a030005203907142c00b000039400210030010340c07014500030508a411680421008210444000c0d900301400c510303001e190903400b81c0800d503510403c440c10703105c00740c2000c01040440a00c0e010f500420180d500606041410b0003074005d000d009034040c5030f004030340e070700911118850894401e9029000c01800c0b00d8480030045038000c042c0d030189550b60002084d034400c0d50703800c1002000c0c0c40c1c00707105c0040281800321803a551148125140c07251180410001c1040382c00072650341e208180c003d40c0280c4c2c0d00301291030104005440c84a0180a20f48035030301d07040d90b000f03020b9280104207041c1d80e0215005039441801100003610904103410884e482840042c0c0c07010f0881d0480c008024003281907050f01c91680d903415180b0b807140d1003254040c02c42c481400c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 827000917 1250 826999667 826999687
    0x8100509071710030c051306050d050a0510050601172205010b010f140a03051b18210604120c060f020a0f140708090a030803131407120b0403030e06040804051503010b 73
    0x1442c07c0b40542c5d0400003000e40d81c0d180010b21411040c1400d4641740c011042240521206002d10089600b806400b4001c5080c000300080540c1010411400b60400d5000824080c0c40744080400100381c121444284004403810002e0090828140d1140030030445129200350701d000c0d03868806040304049840d070a052071000154003414000f0300491908052308071200c441154000500548050008100d81ca54921010700c01e0500110f000f030386046500220040b208070001500c43d40c00340c2d00c59a081c0213400440c406403810004140f000b0041402d001a803843c4120302e5029040318840d59440d485000101d040c240c42c0c40040d0818605d844508108140c081560540102100840501010b1500782d0366100c030051074001f41d41020403c21002422001e100058044030740204d001b80c040d00303005240010302c0403048402d1400625600c8001300260525010f580700440b0312003030302c054a15a01d0f040c60500c40640c09405940d11810104140c1440c018030f10b019603060702e00ca054018a8070003205 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 827002167 1250 827000917 827000929
    0x9070303080f070e060412051e06061005090a0303020105060f060a080f13060504050a03080c040513110c0708030703110705010806131b0302070606050f060a08100509071710030c05 79
    0x60926081c0004d240e03c1c0812501c0c1c0c00018002410450200c004c0060a8a003403800d201100c10b444669101406c185520b1b0031004c5016504041e00322003201c0b000d80003000c140c509002d418605980070920040000c189501900110710a1000712080708070009000c003089881d0003200030301000034500f480041d140507104899035800010b41050052400745554400058980032941210701307410100a400425030003024860b04002e03c0c11080d41407604010108143d181c1c0e2f80e000b00070040c4c482c10300e10324403a06030b0202e510700700b07649066540390398843e0800e81da0707903100803002c600044040340b0400900c00045110342c02d0302c00c140d50f45141500c81070100092422000c20103920241d03181103105000045000e000f1110910b500e015840d15040e08200048400d0396000c18010000c20121212994030701d41112094055410150110744501242850300c0429800854124075a403082c020040e40040d40b03624213829101e04a521940c4130f02d4410322100c120b1000802c6540b40c86000c0c001c40c5000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 827003417 1250 827002167 827002171
    0x5250e070e090c04150c0809100c05060907031505100e040201021f060614091804080705030406120b030d2309270f070804170909041a09070303080f 65
    0x614008070001107640014036512000d03250042020740001d0100196880106100d00e9402141000f0500e001c80340c85583d2540b14000351a8072484554401c080041d0295884802594210080f12075516282c940550340300748600060f01e0a9051403c2080e840401d0b0140906c1202062449080c59240c20034050070144003400c00c9041d80161041e80324010215082044090903400d800310380d651400802401c4040401303042c10b0301c400100038100040d110540806a40000612026030590b500c0c14441e206000d0814000c049000000700003c004d9804445187e030008044001c00044001204250f503c0d444a0b054002003103801d1607460500000f5000c65a403402610091440c150b41a00040c0607441c0e010309400d02c1070b001ca0403075188007940410456110880d078040c00c02a0500d0074000d00f2880e0004c100800412850380104000c058010685090b01005040c003c501d00f054901000c0304920060100c07111891680010741307400e0001407203421031b50542c595003115110101044c0d01c01c400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 827004667 1250 827003417 827003431
    0x150112110103020d050703050712061a180a031b09050f040f0213141008070b1b070b0a12050901050c1204170c1c0306051e01030b190305250e 62
    0x3c00d00008451458902509111340d00c160b0300001d482c6803184000c2c2c400360620601200c0c0b1882c206050180c0c880b01400030020850101c6071907100c4441954070394854034050345454022501c0c420010801000d4440461001a00c260304c2589a49a03101001200c004840340c0132031400d03010210740400e03440d145160105001074804c10080c0003080c500d5041c1c416006900130081c03500400c04c0381c1c00c0b400c244200042d0000e8809811018038100843e5564081d82c040011403044a410074403001c602042000c00600048220b40c0d1143c000c900007601500002103074840c084c3c18039001036500e00040c4141c61050921808850601d040545a00c610840c000d20403070b01100541c001f01080d1700900003410804201c50014405010018100000406503402d0501850705018061040c4e544034503003400010a01c0000d0402c041030040105c0c0030300703152444039401076400d44218030804c111010704c0003500c1c000d04c11602510b140c1c608a058107501e91080d184821003a1109002e1040100c21403500320314 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 827005917 1250 827004667 827004671
    0xa09060c060b030f1b03030a0c0305030a020d060f05120604050714030a05071205100606020c0d081614010b0f06030105060a0908010c26131b2303150112110103 70
    0x1c04000407910308010500f113448158400e091112038842d071040d9965407541c007500903600b001071964010b010084104d40c002c080c0035001c40017800a48080e07054078010410000b061042c6543c4459034078000c0c0d2140161b502030345610300b0100f00c070500002d04a024076071000040c48202d00c0d000220b00f031525410903580e0715005006001e00400c2c0100000409008080e0143c02841200d103800c524040803503080040c11801c01004008580e0007240c0340d0182c0714141c0b24ac0300c0b41101850070034018440c080c3c1180e941c4000c10340d03031428014007545400105144000812640010108101070000b154030116880b20082005001c40c1c1005805440d0070890b504100308400d4035125107600752455000300074001041700003846240d200c404140e030100c401010500b80b05003000030a4848030f410703458015044402035501c007181203040309182d50040125903001c2d10005d08411100c504522850400c520030301c24400c00045201b59010424100c9103054090080c43c07000c4c4d07840c402c0c103500e070455250601d5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 827007167 1250 827005917 827005931
    0x150303072a061d0105090f0301050109050a150b0d0b0103091406090d03060b0304080c03162906061206010207050d0c0f0603050603100b0102160306020c0f01051620010606050315060a09060c06 84
    0x23132401d000b840d0280035411000f06840c9402c5042c401115182d0000c03d858004102d42000303081036040c11105d0480581c9004a10410381c040164040c04189500802d02020a003034410402d00c04941c140c02103c0090036201d0040e007404045098403014051050b5810f0301700041000542000e0080c001320400c1e00130f490030300202c1540e02c42c14952104007681c82c0c80322640c1488184074040300305c4c0d0709141782c01142d09050500601081e924043c815401c0141c110034070110b96942e008100d440014a00188880ba001c1210b18120300019104d2050256281d001040484d40c6ca00a0140e00d110b008054020180882000c04890207007640780042d074154090090721051f0041b178501d030380c405140542c030050782d00d00c0d030088007030703d44030030f41424115691402c82030061071808100b6074041e00c00302d85400510010210144004241d0f000e0301c0d01525071030310034005062030f0888091842103a45c5068030900000344402e11050344640d4611070700281d45ca0308140076280c011003103540c0c242d001f540001514 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 827008417 1250 827007167 827007169
    0x10b120106051521090f10060e07031517010209010915020c010c030311030c120f010609140f03060906011e0b1b0109060c09080c0a0e150303072a061d0105090f 70
    0x40c84c0107a8510241d0341040d200c2515040042210504000307032000100500c5150100d9400c140601411001c105502c524050301c03180101811140507040313600710b80e071090b440d620f00309000703502c407048007400304140c01c4000030000140d001c4540720100540241c81c0d02424203004452001300000100c080c10b03039401e590f262001911003c2d611941b0130384092543c2d41404020500d074210010700d07001c80c04805000510500380d000c400c1d80100c0351800000314041921700001898240c07090340c85c3c0d4040c820f07802013108400d40003554604070b625040e002c03c4030750b050600c028002a200d008554807140c041007445d40540d02550001d00c03880302400001a0304640d9a90301065030b43c1200080e000945081c0c00f40100c041c00e204540c2449000c43d04a001c043c50048109005030000b030100894038801c0c10909151b403018012030ba440c0343e018441d42c1d007609090101e00b422210012441c001c81003d1031002c0741041c010800621400b8844140f07c0020101800444144d4440f00d2125000800e2404c5102e003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 827009667 1250 827008417 827008477
    0x70512040b0604110306130c020f01240803040311060d0e0f010504050f0712020405070207030f060203090c060c0312100b0705010b09061009061b080309010b1201060515 74
    0x1803886810488510b0800318200010342e0010320040071882c00800500880750303210690000f4602c000c1e2000724034009800016402e080030826504001d501740078130040e099020080390000044180c41c01800561162036007540da001d1400018010889055038415a2030241d01802d00c540aa42002c00c00784600d170741c107a060141040000ba003d0b9100c00500081043c02e001d034a0b800b031000030080040c0e0f460844c00008480160401a026503554008108224802c0c02032002071600020800e01c20140303451300b02e00039801202c480845001d5160600713514030b420070885641041000095061442d40005003580d100d000d456100700310307110000040c05402031400760004e54052030000403000328550601c410482c0c000e10b9140315103d03ca84001d082034100e4801419500036207050701c0746524800c8240c0001d0249031010300120f8011081001c100f1054002c201c900c030f0156002992681c400071041d00780ea4460048a41c0030a803200008200080304010340401000000d040034003c18030085611 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 827010917 1250 827009667 827009671
    0x1082b030209150f0d0605040c09060c0c170d03060f030c0e06040f1e0b0a080706120b06040b04140a0b042102060d150b0a0e130f11090406080c0d0308070512 69
    0x111350001704090368800820302c00c480c01028151014020742c0300100b80186400c01c6805100c00703120f800e000c0d06c0c0c01e200c1d880a00c0000ba011400c2a424618500d80e1360980c4c0c1e103020300001e40083d0400c40c01180c608403a00301e14048a0380000c0111105082c00014083e000f0010040c6400603034401c0c035032001c0b85076030080942100805000314118000c07007881200f0754420700c42c00350280e210172800b0031041c0c80009410040b501140740101c8804c80011582002d8034501240e5548500c0209001c1040c040301e600920868445012103044125a9001c0c052000030794070071518078510500040151031007040c2d1070b20014508181c1704a100030170380d00140ca0b40c1c00c00710389103801e42c0e9280f028041e1880c21190050180c4440300c41c25081c441c0c50f04000300440e40c86030845d0301270303100a9500b1101c841180c00444800420520900400b03260780360000301c94119210303003485982800400942084040f440000d031070002b92403419864207684050300d83c0c403c05005a41017000030008460078401c150350542c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 827012167 1250 827010917 827010937
    0xb040f050a02220e040201111c0503160804050a02060c0304030605100503120c030a0f120c0201140703090b040215072f06030105011b0303020408070b0301082b03020915 74
    0x10380f555202c3e00c1112400110034180104001e910344240a100300551010b40e01550901c0d0603c402d1000e020f0450500b182c1020041c140c0c0c0000220f0780c20b007034200300614443c2440c00255104001a807508031005201600d02905607009405943e0150a202008100c0340011108503898150349a172420115003003181c040302c040d0702c1e48809120915050040304400000550503038113003000380701c04540701e2180c69250303011b0050048440b200640100c0c01b03c81c6896030040704000c1007461483c0130f806042095183c900d400700380000241505e000348204804590010304042d9203580396424480d5103050725286181c0c12100b40b01690000303e42e201c1281c402c00c044190b007140307580e0f0841301c90400540710801c41d02c0741c5c0741440140100c0e64442c0f0041d08210009070040403161150809400a2040760032011560284040206450506100031412121031404480412403039200009079408500b56102d2506c203803101c1060a2403081d00940b500da1002084148405030030800e0706880d0f400360070340e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 827013417 1250 827012167 827012171
    0x102040515130f031a1911030406050601020303161b0c06090f0f0b16061e0b180c2a0a150e0106080c04090c17160b1603030b040f050a 59
    0x448120b110714000000404040d44100b800a0542d0780b40c40c0303070100a940c00003c5c201c001c00000c90b100c4c0c3c1483d07100846440c00070b04210940e41046c00d41001d0f8000c41d03007620401d0408000c1000ca500c000102ea00c50342600c0c850014020784c00340c08513040005603210b403105660391501c0c00041b4600130480d10040c086c036250020714910348540001c00004550241c003101d00c0b004010410507940104a0300701d4003a0400c0741400808500e00079000b805807e8200c0c01450303031440b1a40b800400350f40600380149007161180c7e054408089069006042140c140309162070601038560b4081061003136254000b483c02801c508038500001091422f90b2030b51080d01c00d80f0b942844e590444605100b014118507640c40240486804c008580e5a582c441916160249075100c01c2801401012040c4101030240d8000e1075564400401d406540c81c070904807502809840c0c844d0019160004101719091403807040c500a04e4141d06480640003030103c44c1481d90081d494400202e0011500d10515105005003000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 827014667 1250 827013417 827013427
    0xd02030304150b0d0f0501020d060b09040b041a1210230a0212012105030304060203041a040f0305070201050d0c110c0f130b0604080304030311060f1303110102040515 73
    0x8801c40e2000c1c8000000100d502c3d040c415002034840c5003960700f00c560800e182140201e043c2c50306900a10400340c0402c5454607200e0041400c0c09d50310005e01420f0801c94040c40316074011000c00085501e6825901001a40701e0030120090501980e024107041c82c082c140c5941350a00020b0380180c608901c0e9880341711180580700d000000c5c02a60050b0070503400300c1c085081026090a203440c2c1841801007107000c00c0c8940c0c0c00b0056030400300400206070360010070fa0340c40e42402e20f8050080d40050380c046448840e241401c9806c01050b803003940c810791300082c000c580d182c441c5e01c040d0380a601210703059041000400501c10580c92501442d00d5a826540e54081b000300041310250034107880c07840c40703803003240d4500000b080c503522804034041e8080b0900000584c1b043d8480040d40d10f2089600004030b40c040844d002040c550408a50328003040c102c41924201e80d191100000c00842c11601511000111140c010100780705000c2c0310007a00755500010301e419181d8001079200c003258180c100401d100065 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 827015917 1250 827014667 827014673
    0x904020f1c0303090314070506041b09020c0105061305040210050319020412020f0103150506030a09061b03060e0115050313201201020a020c061602101d09042409050d02030304 77
    0x255080c031606c6400141d00348140c583c0e41940b101400342002d0701c5403101e1800380005024609800740100303c1e024085564004045200c1e02809007120700364481c09820020041d40e15460140c203100d20340c0101802c400c1c00508109a406400c0034020708407400c104128420b1594180c4001c001401d180d85a020505070703031b40f040000b42e0303140d22a0a81014141151707070f0001d804418520080d40d0044641c41e40740c2d0750b1043c25000826100c80003804141c10001041c985c92110780102d281c0300001d0382c0900001d510b8091800c402102031044d0b075120100c100100e808180b00783e0145402005200607640b58008c90340fa07100d06441003d1540503545001c011801943c40c250307070000300d41200100294100540c0b00c1019460344011011b00b4020b00c000941d50b0f00040c01011645c040130b030b0040040744580f904000c0241090010011003691816082c1d040580b85040c1000301d2056034010040f03840c00c0780340e0b1080800c03043d54031100f0754002e44031084200083c5091001205c1c1803465401180c60342b510741 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 827017167 1250 827015917 827015927
    0xc021309060e0c01120c0c0b0408040f0b09060904020f19050c0c120703020907020a050601060f1209020a1701021303050d090e09070306021c0507020c03010c020c0904020f1c03030903 80
    0x200e2141c415889184410303204d0340c004034491800181342c007000520b00e440355020b541484840c00000c18908400c03040000700301818001d041170b1f50180c1810031000743c4412148059120320402c0782c0c1d00180034000070006140c1500140b43d8180c0e105690b505150800b56214443c8601041d07000c0401c030003003803031220020304000301310f84d03113508071542c002d0b610301d5045c41611002039001c040d00036480c450004072424000c20900c1245036000e0b08542466030b42d00c9009000b400c00c0791440c00001c640711001001d0b1625130185490b9142c0060403402c80b14034242c00c484054a01d0f0103000107554007403000740c1028030b0030741d4910002c2d409035021f400b40c101c0480c0010000807a60b04031001c0d8503400814040c1c80c007000107940702a42d038400700059450010300caa540b20500014104e540c071030b0900080040242d0b0100e251040c00c0401d80080c01111024001681ca50240e29038581d0460b0207200018050b00d0840c504120a0802070700e1451444082c8140301101080b0110540200b61184040e604141e408 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 827018417 1250 827017167 827017181
    0x220309051e0f131b0903050601150503070809070503031c0b06040308070f0510180303361104150f240c02030f1903200d050a0c02130906 60
    0x882000140d60304400003880d0b2480c1c0718055004005080c0100d48210b4107501c251090303000c06400407105801d043e402448180c1c1401704031100d014500002845c00864800609200150b03101c0d1030a542e07448008070f5180300020460011841440030025068906000511905a000b0040c007440100b0810341000e031000d0030b8485005010400080000ca1070305002d98440030303403200560500b41141e040c614600f4160800e941ca1040c94100180c031a04e16004a01c1d2160303202c5e031014481103442c401e4151500910070130b1044a8880c0844228043e080340381c122003107c2c0b0900c400c203403000c46000400d0449480390b4216441c0201c00c002071050048041e0007100614412082844003144100300324031030b21034036030f401c410b10040303a001c4021543c2c02d10110000851072811a03154030740d0036030b860034a2a081601600490300c00c0743c1040c00c8400600000b440d400105c0c00401610b0080882154194011014039041040c1c1e00c2100006a40d0450403c4521242e000081107403252404d000c4100c0c0c4603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 827019667 1250 827018417 827018449
    0x90e0c12130c03170d020d0903030507020a0201081f0b030106051b0c0303070b0604090b091f050f010b0705120310050a12350304080a02060610020a0b22030905 70
    0x2400e4444400a40b0026550055940c000030f024990b1201c48801c46480c0a42c07550748441900100b150210340c4002e5025108142c001d580c207025a8407418020b985500a0311b8020340010752080c001040c1e00707001c171040f100300011640b000400560364a24040301e600280c10a0001400004601c48070080310744441c000100514050560b00035440002079413481103010040540559a0019003150f0320307035101c002c03a140c0201010009291040c006a00c6000c0007010030401e011b0072456259a410b14401c00d032145014800340901c0d642032a4604240340c0040d1303000c48a034450880000d04070102d80002d940030700d01d005151142c880c20001008504509600041141c50b04287d02a002c01c3c0d0481107184400860340294000d414030400507800c807164051104d04c0703503e0002c140310401446000034404000c040c2d007650b402d0340314803080200904200622400503889008030502140e0f21622407500841c40d0054a1903050081801d10283c0c5800802a00841c8a21004103c2d40c18042086511829 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 827020917 1250 827019667 827019691
    0x36020a12020f0a08060a05100509100603180c1a090a0312030614030d0c08040f060c060e0c0310020d0914240118020d020706110705010c08041e03090e0c12 68
    0x414400c4c4a969400001c00040c0d420781c44002003001000c4031a6844041c16014003015414500f52940c518030f60200c1c40f800000900d002ca04a4605100b500e070011030075842003542c0c0f0254585100740600c0c40d41031a02d03d20800042256910740d65640040d04020f5201c0c05442d83e030381c0407800026044074280d40c802c0c04030b50003020f02008180c0e008038030b02042c4055030400b000140804d0414442c1c0c0d0045410003410750030300f0080032a0250300141e900c514640304080c20b1140c0c1d600c84034020744034201a40443e4150b840006820706c1903d468003e4403420144100025070502d140d29204100049101003104c2508040002d40c00b51144e000644004054050b01040c207526004a54007219280420307083c060741e02161403a0b0a440a030110782c16550003000074030204900c1000680d4550042c00304444540c1317044040044203000c5c400ca584103d4010301c6602100580115203000061036417011002c0020580000c901010521499400307920306509598071000c85802c214010700001c1c08501c1c0e040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 827022167 1250 827020917 827020919
    0x51f0201050a060e04081308100902030f0a0203210c0307030509010e04090201050a0f050c01061d011202060405120f10020c0c012f0f0f0c040b0436020a12020f0a 71
    0x40c000e10031305900185e1080180d139850050070f20303905441903540c00c1900e250040782c40c1150400c83d40d8202d00080c900890a0b503140301c2100d081c42d561145030100083d01600000c000c86003030f8a030305070803c002007411b5481c5441c0024009090b401c50340018000c0b800b182c1c020a0031003465034400c04c66440c0038400e5070200b2240440e0f0300080d140303000c0c113103100c2c00304100c07041031201c10382c842c40549040707940e01c1c0000d00110341c842282e00e50036082d1881c1d06000071882d100000b00310380f40310400c0000d41c3d0003600c510715190401090000c507035285045101c1a00c19074813103c400200c2003000c80360650b41000700580710480c0c80b00c594140a00d0b0001c540c104114801c0058242518070000c00640e45410115901d401001c0c44081c1044000c1c104c0072a18010001924140d4001258002d4444000c660030048a02c00d042084100c5010400c440444050780480707614941c2c8000b000e5131015045010760151400c65170004250f504160040745480910201c11021814540c8409000d100c0c101c0d40a843c603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 827023417 1250 827022167 827022179
    0x30521031504020307090e0f041a07080a11210108010c030204260111070803010311040e03070204050603030d0905100f0c02062404020d020316020f1510051f0201050a06 74
    0x1902501081d0351046034000301050100d4028601305006107605064400185854400070910800c101c80554080804000045507003582500307161107544a03494a00703ca03101d41c20b0400080a86d02a51050070f1403c1100308059410364211304c1851984030101601c5606200d00d050075a444001c8540500d40107000c00d104404840b0b010348084030316101c10030a0005000031580c05019a90f810180000d0b0000f2803c09008242000718166401011040d203070380f403c1e01c280003c560020542c0c08803500b00380320020062030300b6004a90004001030031a410701540d030a0000071242101c60031101a400000304951080590107000e0402c0c04282042160164010010303448410050071803a43c1c0101800c034000000503996000c0701e11030054011502d41c002152040020f510641b00480c40c90030005901e01079034400a000402c0c04000b0015141809210000201400000c0c0604c02c604188440102d196141c0d0658020b0b4080e421401c0101000c10a6002e400c490380034225160540c00c082e014056 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 827024667 1250 827023417 827023441
    0x1801110306061c111c0b091303080406060f0609060207140f0910090c030603050c03060c1c020f0d0c26070503040f0f23210a120603052103 61
    0x8107003600c05080f900c035401e000038004020001158881c0d240100b0b04c0e0321072000b40d00c84016080e1004070304101d070000348410005199001c80d61410561080310400d03000901c2480780c5a0007503c1200042815504c80c8902c0703613428840c1d00a4030024016407010801140c0c10441040182545043e0035945006d00b8041042100e02d000424012864040820f0941418140781c070028030100301d0800c05070122110081c050000c510041e9000d100d0b45402003194607010032194060440342e0401494a8a00c65403000405c0c40ca080b0300d100c1a40c248021082c5001980c01005140b102c00c1c80004d0b20031204001400070090030340307030f000400341d10840f0074840c081801c0c60a4204085042c82c0381c0300d0f980c500c2c10900905004000030300840c074154003841004201c0c001454030b610710103480c0380c40704440380d00755a94100078038a11078000440a0700c51042c00780c01d0300078000e080d00c91811014201048420005446055104a07003035030000c2120140791840000000e204500b00050920b5402c2c1030482e112 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 827025917 1250 827024667 827024677
    0x11070e2406090d15061e08030c06040b1e040b07030606020304060e0103020d02040b070f020a0503010c020316031701080c101b060b0109090e06040b0703050103033203180111030606 79
    0x101030001c80b41034805004001c0e094007106081e40e0302c117001007512906103c4010425044880d0117044040001c100c0c2800401614802c1180900038101c5944030340706c00c10040c030080c1c04a0125043c22903401c3d46003403240c4115200310b0281c2440c406904140c0e80c02400c030b4401e0f501030b03011500248020301043c0d030b110511210002c02443c0140c1c032008400c000e00020720136544060800100014940704000b50a880740041c640202c9023032459070390322024182652000b6910200503002089220308040b03000f00809070325030107403401c540100b42c00c0341142203411303083e00280b449500c6003469181919081d00071010f1000c0910b005003241c1e5030703900750640090000500612071600c44c5000c29071640b05103001c40c001c0c49803460500010502e14440c68807841c09540c2a100b214450001805490280c01114126585961590f411400700288a403400072040781a00198465450341d1744607200d6400914021180c8011414074140b200c03010301e02b1230302c000c180307000d0402003402000103070750703d02060754 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 827027167 1250 827025917 827025919
    0x3140c1507060213050d11030d08010b040e090a122309370b090109050402090609212a04090308150103090f0804030b010b1905090111070e240609 64
    0x140c0c50329001103980e07034104131341d07001103401004116181c0c081c450079240c204152902901036602c580412902121601000d0142504070b140801c02000040d0340000381c60382c820b00c0a42929401a140ea49101e51950b10071070b07820008904150740d1540a1000ca0118460a6461032691900d010b40022804140514070101810785074501550040711078038581400264400550018940e1500d07100500342d041102c21500081100601003a0381c10300e0310031aa56000018449402d22600b9420004160210968141c0c40110038944120420040100b100110080c20314070304464208080d01c04900ea070303040d4603407083d0300700756003400440d401103003458000f085c10080310010a045030050300901034110b0024591189014214107000303030000540150380c800c91300d9100d03076666074040c42010f000e0400006403a02c005004103412600075001042c803104181407040c030340e41070301f040c440c241003043c1c0c03124001c0402c0c83c041040e20030322040300c4840982500c9160060700d091340d0209610340220280a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 827028417 1250 827027167 827027171
    0xa020403020306220b071d0a03051203070c080c010b100f080f06030a21020c030a1703060d02180f0601111c02012a140903061b09040603140c150706 65
    0x200f01070200183c54070280c55004090174800d82030445d0014085e6505050341c00520211042504180c0b602207500800c681d0080018040b18098400d41062a400078150105002e0381c820940001054800607003014028400000740682ea02001e0004110104000400b00940328500869440d007040d1165084100019074005a94404002c2032074046980c0380503151090310141e100901d920303440c401c030404169600341c032180700c00c0005055503034000d04030041c040100049640300303000c07000c4040c2d5440340d00200a140b8500064011404510254001600c940c0c4950204401c040e000c601c0190041828a09800103455040b0f50b0350300d807030701c164034a0b01c4a203101400c4030807240b01b500100011f81115003003a04040e42005d0001c6203940c42c01c00c5501145259292540c482145010350305074000c0035016000c5581c441c00210300f03020004200240d4200c0c103211039821a20781d4491000a50302c15841445805642e809407854056004901407142d0900d40449031028401e0381910741855102e400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 827029667 1250 827028417 827028451
    0x30c050a12082a010905071e06050f09040f0905010203060108012702030a0e06090f0f0106031a07110318010e0d050a0b09030408061e070e100c03020a1a040b0a020403020306 76
    0x350f8000700ca5583c910442e5030800c070a06043c4a00800c3e14011602c0a40d11104c142491120003001a5002e11521010407030501481040d60b210700014850b0030401000020100b0002142d18200e0b18081026959070b0350100401c101c650b040b0318440d0140220381501c003d0651014012003607510b03840d40c595401070300440412a200e11641021100b8182e041c16220585007440f01299101c50240c4580c1c45803048018101c42034a0612520703007540d0704102c0d103400b41410540c0e0703401d1070388018140c8000c000710b00c00311010f51707102400900750440c002207204001410701e00004007061001201203110700e86031306e1a040000c1d0001080506a680401405040e9680448450442c043c0350b000700d030355004a40c2001414041101603a0740701ea0341c040d00603101c1d220f180b0200c034641761404010350040c50882c682c15010b030082d91f880600320302c13a1049174036013441640c4400da241924111040301c14589420f02003041841c250540c0c0c0320640310001c40c01e0501e1500000c2c0c0e0703468098510a000b41ca6840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 827030917 1250 827029667 827029717
    0x10c18050609031002070807021e0906150c0a111504080a30030c031d06040212030f040b04050301320c040b030702280f200901030c050a1208 62
    0x444d1920880b002d8508540740c44560a00c80410380c030a80040303104a8510094442140300c110250a0011002e0a00030480d43c807541403102100d01c0414280100b50705006005240702c041151500561007403445084041800052044120b2505002c1046000034070040c400607100088543d015a0030001d020030740412081c858200311a0500090703120007034442181c0a82d034140e0000024211305540c104030881260400d8540c50310a114603000507080031003c203000d4030b000c610102d901502207007030320310700302da00c00c6001d40540c000d522000000501050401c82e500c1c0a02c0340c1a05007415450284245c403255480410110f43c05024241fa400742801142c101c0b10b01c4410340c0c0280070301450300355480c108071802a640e28541200810107151000c2a544412141c0d0301c03c205503503014208241181c00e0341d40b85220503604042d40410343d02e80c1200701c19a95281035505000718001c0020000c04c130b04101c1131080e0001c071500603204800c00c0c100c64500043d118030444508145c0440401c455921003c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 827032167 1250 827030917 827030923
    0x8030c120d1b1701090b0603060f06090d05071a0309061609030b0901291003020309012307121413020d0203030d0221041703070e061209010c1805060903 67
    0x221000031200641242c940340c2540140070060701410403c00c005641ea80c0e1030244c1c084e114003000082d040074003403000c10760504080345920705003000200250b0030318a1020200d07074600d01d086401d6450394050703007081003100300c041e940440c904103d248261440c031b07100c0f140c01d80d1508041d1210030b80c1708a00310185810381c400c034000ca020307503032100d4070300c000d81000703291240a060100c119014480c0d80780ca15001e0681c0008240901c804027900300c41007000b030301ca02074009400040c103c010554840c0a180e400303008040080103c01540031008100b401d200c0340c0181540034150b86c1800c424030701382240c2c1000d4005020703240c2c020314169038404e00308024400300b08030354002da400a4140c400400d0341080760602e50007900303440402c80c003c084101c400380b9501e1002c000c1503030064210343c021224482d000340c03040e0095500c00308504080401c1401040441d00e564404554050382492690511800200071300401c2c449800782c2c50008000c4e40301c0e10403904a5034061198900c184000207031a90135032018 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 827033417 1250 827032167 827032181
    0x1e0f0f0918020c0606041a1e04060608090d02010c08011701140108031905030c03010b090604170a060c0827150903130501230d0e030d06030201030608030c120d 70
    0x110010240c038108148250180d006a03e0380c2000d4010040024494105407041c03003000910000d68440001040062050084840401040e0742d61130f00352081464a5a0090000400b00342c5e81e61180e6143c410300e02070a100b021a028011641401b290407019584407082c1c80c1991070304580f007022400e42560090040106960003544211048000511184040040c0411251a100e42c840f210308030741007265507120881c1c001c50170140500c01484491601800703040c080394094400c030304c0d0580f9a00700c412747c0d50f80b02d0501c6619522500241d0100681c3d0700402c04078240c2d0741488229030400c640c0004800704003607001144400b000c0340107204003c0030442840c0800075014403000c0e604002000d02e0b2294041a04c01d5a4944103c000003690b5100c4c403c031261031400045181e0001a41c0001342d0b800d41e2040c40c441000f42d444105409e105502030000308818074514000150b032914601c005426191187c3c44aa5182c005102c6c1001c1c091300460820400044014144c0daa1038055400d08010706030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 827034667 1250 827033417 827033429
    0x120c0b03190905070f06020f150406020c0703050303070e060702011d0a0521061f15020a021c02090a021c09020a0f0f180b0d02090a1113061e0f0f09 65
    0x2441c010b0000d10201040700b02c1075816400e4041d03c45503c5a1041c2d0b500d080c80c000c1c4401d29030100d000c440311a8620000d440e0000e00c2400094034013001d2010440c034205244d00147e500b84c10000c1030240b01c5403c52400100345000380c070b010b403c00c3c04da071300064820070072168240a088e410300050160703a40e954030540083c1034010290b00700c0000c03081c10140d001c0c8880304061014482c50011680f0010342c2404442d9048540c94051003041c1861541d88402032803480c1c42c015441104003040050362014402020960b00d600280c02c441500d004000000700007506102099104009407070300c0d07903248000d4040b01d21400c4808110f0308414030208424840a034842d56290100c46400302e4080ca017600c2400855815440e80290290800901d00031144498001780c0c0c0229244214030050805103c41c9900200c100c00001c0c03118010342c121a502d6103c100d01e130094082980c001d003c89070304102d241d82020301e00010018080e00c0100050325880040011100784488002040c0d08103204440040160070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 827035917 1250 827034667 827034671
    0x10c120f0e1306030b091507052107110d2c0609090403030b090f060303120405010b090412020f06190b03031c1b0e0907050a0207090911010801120c0b0319 68
    0x4241182c03000105a81d00044444900e0400400c00b4400d00003a000741020380c01456410303e40702c030041501c0c198031884440d09507032a803030b100545103801404028410300f0f0f41e03100c1e0030010003610300d968100043c02d0268401c1c0400e254010020005483e48410403a100c00364821080d0802c50000701103009010460b035100041e44100810550b064001c40070301002a00c80164948594103014503002085a0031501350380140b00e0110a04030020b0f05641140c00f45000050781020000492034069049070160340060240c400460920b81c1001350700c5011003000054091414455038210140200ca0204181c29444e13200e0a20aa80c090048514484220909114a180c4110300d00060240c02c804400780030341080700015a140a810381c80c800510040009441d0394641c101031300c0395080103c5080c1188110103020408406911808642601940860402c111288001007180760f050708001c02a841031742c8118000380e0343d0392508055032902e24019807296103010343c00640e9a042980410b48038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 827037167 1250 827035917 827035939
    0x1051b0708030a092412062115021215030309030a0c080d0914330310080f0a060f020702060403150c021b09040813060815010c120f0e 59
    0x165000008203098a0203459040245558a1103009110609400701354150f8030111790b20b903280d1282884110300b0441580000c0c1c02c0c0d44070350704100710f0b2000e09941200943e00004040a101001081001a44400e6003c0d03141c403541801d8880200000b030215000c4080754003011403030f507500f80240c501001d800f404035268420070b400d0480c820000d52049113800c0c013843d240c4610302c0c0e01c20b140705401e6070b1180390a42e40c3c0010303030401d012191b65800743c82d60381040940b4a1403c1007480c0c151418500c24000760180c1c480c2442e4003d80c41000d0306030b0200c441c0e9804410380c425070070070100d1042038264018900252114510040c000a8420294001d6201030b0001d8040100808280c54101c01480305504018205001005999481c14400344010615180c410301d050f0f8500b0249a992051180d0304941c10015002d03038100560034247c101d40c0114070004200107500140c001d907541c00850074a000081c50180b5200c1d410013800041c0000c00708012009079001e424080d5240c400d000c030002d00405200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 827038417 1250 827037167 827037179
    0x1b02030f0114010f080d1b060b04020a0e0a05091b0a1202030703091a04020a05041508010c0503071e0f03110c0d0302030105181012020d06090c0509060103020703090501051b07 77
    0x2d400d0190420701100e030400400d039242e000400c000c541d005600ca1401c0240c18841300000141d681c13508580703282d26441c40d902c7d01d0702e49002800340192142c407003000c151414010000301c900d03075801882c000c845217010400d001150700400f91004e40710180d01c03541c1d46107025044407c160000355501000b0f00000a120665500d5801040c0540c007400c0c1424400c02d40004902d0000010380e00a507004842c04024040c40c5010fa2213040845a200382000c00299184030b0303182503401100311000403880c0441003005094109600c0c810100503401e40c0c07908030038000d4000e8525a0315003400d108041c0e403030180c100010b4035501200d407080140821108849840400100039500900915000e205032070a10050101c3ca040e44a002e4070424820303400d02402d0690b506916190024166805000c80c40130790013040f51780c0301d14151140036018004c070150602050024140c03004d008a41014070404c80d00b4007280e4008035403025100300340303000750f41c0f1140614040c8162400580c0f5003098002c4a80010710703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 827039667 1250 827038417 827038451
    0x3020a0c0b030f0702030910030c0c020a0e0a1107080d02090d0212010e0712021c03140c0601090605090f061207080d18170d030c0c140615040203071b02030f01 70
    0x12941d0f8034568410942d8840e482241ca80c002c03069499003110021103070f036051500a801c080e241a18500d461200052740da0005000010035900c500f8642425070140310200c4d400f03004000700410b000d90140c0c54140310382d032014558414581107814090b8080f400c0007042c0c1d91500095440c0e50000d26440d400c900300d1600e10700800c400d90405400740320f846c00008512724002031100741a0340040c83c029401800d800810b0360407881b0b003030403820029190f080703008128424000e8582c2000c440002c040a41c1480d40010440d03da50b08000c1c89002c02104004468586040c5d2a41c0140191080d801040b00654080d00e8507280f0303002410640520032070f11000320350101c209121007030914440e0501c2c80c0e90740f0865040c01c9c03c441040900b07802400000b00d00314002e800c0188481d005203031000c0c0f5440d5980310f9620403003151850380b800d50410b0080c400c2421241d5401d0800540c101d800b1840d50903c2d043c00361049241c901d442405400700041a001e640d03091010800f0024888000d105907107800030b072411 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 827040917 1250 827039667 827039671
    0x40b090115020601090e120d1104060504140409150906110d0207021801150f0905060d0e01051f060c240b1f14280f12110f0703020a0c0b03 61
    0x1441044000104070002c0c0c02140000440600075191140080507e440c0e030754802d078910f030015601c81c0d01c12050380b848180200300900f1607a80d010707292800e00070500e540c0078081c910248100c0c10320940002082c00410360310441d650816001621403018074012018159814805401240103e441100b5200c950014100c0354070031680e8008100129061040b014400c1c083c0012421507035442ca1015801029060001419800c08a0f40d040d0f0b05c0e030000b0300c0c0d030b800700781583e0245840d13102c809803540007409a190002c0000300144480c120110240c4a100324500c03d1b28208104d00d1056000d1000103800301c500305907450105400010300302a90400381200d041d40b60300503003003c084800800c0184c0c00c010540300e42c1d0790342c6284071b184203000c00c03905070446d84c2c0580780c0c0317041c0c40d09400b100c00b07003079039500401d0340076031148640140042000381903c04c01e00301c25060386007003210b40419192000704444522000314051a201c40130f5041c00c07842d2100c1c10200404c0c0d01c01c140d0340856800180c05c00b1318 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 827042167 1250 827040917 827040959
    0xa03240515071509031b030f0311031312200c1f08011202010e030d030b0301050a0618020d02160501020306030115140d44030106080a0b040b0901 64
    0x800d259038100c1210034490040301a01002c10400e06016400f825040b03001c505020b40781015010038001403100c0324405002045002c1445214008445c1d40c0600880d100380b0910121507080d45000b8481c54140070140070010803007a031254100c54a140202c50001e1401140b000031020008180c0045507a80c0500b2a0700f4403401c5088d500e03101084401c200d810b040380b0707103948442d480c3e4a461418260921059030483c188645178050302c43c030780c404010f0110fa4031015600403d1191a6006140c00c440014010710380035170030030b003090146600314079116884001e40c1300010303a20f000e1a01e54000a004105031000300396602d01d40002442015005140030b540200e00801c042e0101c101d60348291210303485200c40c0818000290060791401c56a54001c40d4001d50380d101c02840346100700c1009860b000602920386250f0154170704220b5000e00000c00c041e11800e8010f00e1541404000340948500609001289032104454480b580310350300590606003000d080c07580303d540c682642c00303040c2d500314580c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 827043417 1250 827042167 827042179
    0x6170f0c0d021f02010603020d1a090c0d0312020c010e0601091401150f2a030206010905070504170a05031305040b0901030c050f190305070e0c0309120a032405 70
    0x48051811044414085a0050121910805418014400f89090282d0b8030030355603901c0c00007002d0b0f107d03c00702400e402d10440130105c0340c080410390002a81c5002d07100c158207a010004044442c1c1b190001d0300b000d2505401c0c41901d80c8468080388011744207140700481a03501700312240e00d01202c005503070f9051320488a412710075029442c00c55251a0024460941c18030403944c80041d11a0040d9401d4400e0aa42d15042c0010050700c484801c042081e94040045808412501e9003410b505100c114090140c6010074882800c221b41c00030442d0040c1e000d2a030a0303602807030b00b040b6422802c0042c40c4140c0d82c00b00940e622858051061003040d0150701c00c8901070350401044012a00d032001d040c40c140c0e03500440d0780e600c0d81e08000900156009480040d50000030404030200f4a465080b041001144070350011325019003458036288400700b025080302c00740b0701c00b0b100f4045115400300d100d0f40b80b0b0203814a00e5032142d00e800000c5019040d0071100c4102c4401426240b12036404607242c0d1f00c241d480c25100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 827044667 1250 827043417 827043433
    0x12091b03050a0311030702010c20040501030b1012020904031404031202030310050d020919020f03010f03060c231c0f0507030c050f220b0f21010308070b0a06170f 71
    0x4d9151207102d00034009000904008480700041c2c02004110803498007408075501d440083c4010904544003078005440c1083c00004015049440101140c00707444860105e2a04d00a40d07400705100301c0b006040281403103141c00d01005103402440503100219002060180b00315140140a9220303802550140301d020360350680407903141040c500b280000303940640254519074440b0844200403068103004a9130325002c00a2000805015000d076018003900052582d81d00c4c51880c00008982d15450160207210f03c04148d48000307130b036000c0035205004140354041e03518052800ba4000c0070210042d40c01840c0c0ca040340d05405803a907a400b243c440c1142d034034100b110310344080084d940b074002c0d20b0308119840c03020005040f00c281c1c401800d50141e82d09452410701035454003611645a0420401409843c0e000310f054504455142d24103058070060b0750f500c080d154155100e28901d4816a81c024250b00c00b6807012903142c81099000324024580441d42d0051210086101074540c07070840703658000b5200e54a4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 827045917 1250 827044667 827044697
    0xf0705010b090105011d06041203090503010531020117010603051611030a0302090609090f0a06301a0106120f0b010507020111100903030209030f070612091b03050a03 73
    0x180b81c161030050b15105a850a1800302d00c4107911141c09503a08600148000911081c00303410a0542c14800d888003107101c1d00f05001d143c00c460f4020001c0c1c41590074004001100c0300d41030380c0b001c814102000b00301c030301031594001a920030342030b03164007104101845c2c00060300d01e60541c009401114401c00e030710403550491004464882c00c0c41100038454004110860081d4025402000614030240c003180c1880ba0240c00030301d00400c101c83c4450205840420001c8034041031280364060a08040d04013003000211814120220105600f5072000600052030307010f005280c2076514403550fa030f2904840310341e102d030707801031202180418105449007440300301d081450203400341c201c000c1c1040c1d4600341050805c0c0c00445200e80c03151002e24407401a440d000809040300c1c0a031003150350090b24050b90781caa818080c07601d481d04001d4940c400d5000a0b509021160340041c070307074552320301c14a400b05089005041c412041c01045515515201e1030300c000004100010451540c8103020b0784843c1d000c590346038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 827047167 1250 827045917 827045929
    0x50c030a0302061311040c030b2403060904110415060e04050f040305070804030b1f1502060105040b0a0503100f06170a0b070e03030304030c06050a11031305030f0f0705010b 76
    0x1010040250300030500203000d821340d00e408110040c0c011410050821241e80110b0112006a00c040000a840300485e0205003400c00f00b40040aa2140030140c51241d041d0b014400b50001a0245d4481c04103c1c3c041400c3c8214403802948514005100704101510000e145400c90a40d114800c040b0b6010030b500d0041e45464401c480c42003088a420400695895030304640651115108803814070040c003010010500482c0c000380f03d004002180c001c007100469040b40802c2140d0700460500d400c01691400302940071590904680c400d540100e540c1d0748a10000e204080175400c102d415110301114241d18044e07603002111340780b8461100300041a2101c000d00051902d0703200c861200e50045499400060a00250a40c801028940700c130076001c00c03500080c00c50b4820740f0141c0020b0180c400f4403040c01000d10466800002045d410030070095200c5608000d800001c2c60320518016940d02d04003445800c0c000c95803440002116555103000d071032111001504452410384996280c10340c4c004190602d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 827048417 1250 827047167 827047183
    0x140105010c08030a090317130b060901150c11060c01240602120a1224090507021f0905120309010f0513081e0c070e09071d070306050d0807050c03 64
    0x902c40030718660707403801400003030244d5030300031001c105900c0c00342000c414120105034004c0c00385802c1c1d080c0b4040340d81024420454060100391045689a0042000c5496003c2150485907103041039981c00e002810600c44110201100720341002c0000384562100d40103502020300b0004031010451000d51009a100d401c0d01c0301d0080b4005a0b20082c075105803d0032000c040c00304d410241c6070540c0142c0030982c0304401c0e142c142034bd00002c500700c00401280c104617140d421000c0e1807603c104101a02d00300c18000e40c0d80b00c41c0300809400240103089003507802419000000b04603040022951010341c0c8100c01d00056004a503092040d510f000c10042d1070740341c0e0b030003180d004164402401c02c8590290300c40c031443d1703404920021540380611030003444204002026100840001000e0a8068a01542d010302d0307550080601080782c120f03030740c240000400210f40541582c40006100e000d981c2e5000c0c103800511454100c941d000700c919100b0000c1000b1000140f07100b82c49031b810355654002d0710302490f81ea4000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 827049667 1250 827048417 827048423
    0x30b031e0c040501140607021302071b080607031b050708040b0301080a0c060c0c1802120a0c020d02011e050403020f011a12060708010e0603011413060608030720010309050d0201140105010c 83
    0x300300403000352034900b0032702c0d845500e000801440e201d255a80e0a2202003242e4a000c07507116030080030400d145091150590040d5103040910005071055500b4000701e000b8190b440c280000820400280a42e400c151005400c01d05e01240d038950311110301c1607a45032102e5080341c484c03034440c0011510501c80c048054210764890703182c1140c2402d140000c46032400790240480340a500380b10401a441520a009001d10404440090454280c50000f4100015051074605581c101401e100c404179440c0d5003540b54507040c9800040315115072400300c0c10440b4185180d41d4035800c0400e1089452507255402c0d40b20001200c00b80701003c1042505034440008076440e00105d45103000400041d038964500ea81d102100038000a1510304240c420310500c2801d950b1a9281085031480c0b200300015031060802a1411100442c2810316603914036400c200c050f8481500300000307003405201640250440c0d80c9241d13000c4290340000c108044000e0007000c0001540f8400c860400000560f940a2a03070744401c590 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 827050917 1250 827049667 827049679
    0x327030b060a1e0b070311030304030806010801050d080403080d060e07080105130e0c04091e110a050108040215090d02060d0c030b040501081015031b0303031109060307030b031e0c04050114 83
    0x126061040c4c01c2500000380a4052107070b0001e0309542a0000e100840c45a41b00ea11440707580d041c00000140201416003002c0c0c042d02003007030dc50002c41c0009040e1012642d002c0c0c41c3c1661584501d07001c0000d032071203621610000e204401031040d0341e5007161120341070b1042510800d0409002464440940b101079952040607008404191868201600510103ea01441c103081360030040314054494102c0c0c508080c6d0381c40d44070090180013490091604d0b0004c0100b440c060b00d04d03080940025808502e4011601d0b003256000540ca02581c036940451103400c1d40050040380c5a098040c1d148024062a203421000a40360440d61103642c500361040b54181c0e04140300070201c003560300f544100200202441800b86103040000000003600001702e410b000c0e8554008060820b01d50f02d40075040d5003a52170124aa02030038031070400380781c9500c41680d500038424940481d602e0706200110b810040041c3c0b0100301c85010000d40b100300a400907004c4402d0105071000c11190382c0c0e40c02e502c9000c01c45442d005510032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 827052167 1250 827050917 827050919
    0x5090601030b010e04020a080d0c1407060503280504030c0201021615050f040f0314060c09010c02092d01080c090f04080a051c060e0105120a0327030b060a1e 69
    0x880b40c44c003240e401071000d010050b44a4031420028684080280c0780c00000d04428101000c019502c5041d00003981020010300303266080c03800c00741240c040201011800c581c9a6491010350410070100c1d0022a0b12190410003810b013814010310305040b194082c5d025119038821000c1119040d242041101d2191403040c0d00078841107001c5a13190b20840101b03400e0030303040c0004142010182c0d030420086100d21000a1000b030440c0b6124204140140314000119041c083d880150360091980f040e1700d50f0441c0c8031080c0e607807008503094510011441c0240c10302090452007425081c4400c03854141c801981c11140a00c60a46c1000440c80702191445400c060341004940020003400140c42c1da1000c5041031828400c103261403500703d0380742c19000013582d511801c1c20010701024101e00c0740548002d8528040301040211100c0e500c0e401d6040050030030102d401d8070f0f420403c2c00d5044100c000b558242408125030784e41050071003036806550301032280c19040b00005540007a12030244502d00c0e9600755140d41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 827053417 1250 827052167 827052179
    0x1e0606031b0406030516060216081c0504030524060a051503061f09062a0f11040207210206070210050603030d110d0606050903072102120a050105090601030b01 70
    0x1841c092103425049921400003200280d42440100d40a09456001001c1185044c2c80285007035003070249581440007154007400400300204050442c140030007904406200900e0080310103101c0d6034030180c000d001d116100e041100c04107030000081c00c017840040c01035481d02c00030421090564800d50350f0041c0d0707903245040f002c0d81200155034410701c0140400c005400320a2841140502240290b00150850a091000316000301420f10550001460900442c1040905100651740150068890860000c00c80700b004015524009000000782040d912141e15150202c011901c561041c0c0f003899859003248202071002542500c10003a80e8002e01090001c4410b98008040285c06283c060004001c95076003118940991032081d0002c10346d06954003241c40c1c0900494050380c0103142040001c003c061010b03580041c2d0310b01550045003054680a100103110100e0b0103581200075000300c401d04400d820102c0114a1300c4809000d23400903c026520140810303211070303003400000c1042e81188014010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 827054667 1250 827053417 827053453
    0xb0c0604020f0f013603031106091b1212040602010b0411030f040b0c070b0412030e1609020c0c030d0c0215070b15040f06141201090b0109020906040f081e060603 71
    0x181e000b17500348464a01390309540b81c1c0041404d03003060f0041840b4040e00d0700601001c1048591004003000946500c00d01d81c0d000250304092007030364500c20031141d00c003030820b0030081c00340e02c1c1d502d1612800723a03558545c1c50b0b00c040e000e800e4014805200354a00f14608100b40c120303208891164840c3d110401090791991740d030883e141005468041c8015040c07102070001b419070f603541400786000380c3c11044946000c2c4c4004050340c1e0100a1600c00750440080440010209412401a43c0c21400d0168840c5206140d65181c41c00650740b861b4144a80c40710807044507040145814054021356409034a520100d095100910504100900385a1105c0002d105081402c40d40c0456400060000c1008002c1d200e80000b501d1458012622110503901310911505d40102c0d10064038a0006c001d001d01520754480e503250040510800018640015003082282d1300c0008450280c44010301c81030005440d28a42359880c4c00a91012010105500901c0c1c0c2800002800612442c00240246403941101d1001e42c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 827055917 1250 827054667 827054717
    0x10e100c1b03031e0501140901150c02092d090d050a0c03031a131b03090320030f030708070f090503060a0b0a0b0c1c0e1e01090b0c0604020f0f01 64
    0x88600c1144084d59100900350003094000c02c0c2000c101c9003400d041d0341c101300d0000d00c180d2220550480300300c0c105000640180d80301e8501d54040f108071034180d582c081408441d001a189000030364000e582202b00341c00c00d40c2d4152740a207803e082180c0d0041c41e0210250340a02c28135034188041180c26440100003842900050414442d03080100d0041c4c410501140c062045100c400194585403040b52003d020560040b101c004007615080c0301c2c0042a4501038140f540d001c40d010590311031501424803589040040301c405120fa61000d6591386401c01c4001d1040c070701620b103000080c1ca02e2000240d407500c40c890700016940c004026290725150480c21200500b03032000e4154210324440b400040c443e0a04002d0064025054040c100e2000038114084800600440c1c40d028090000a010f1030b81c0c94441e2001c13044414110f01c102c0c000072400c01a1201c103602e52211f821700760000f071108489200416114069032080d104001c14480440070020411104145940000c40c60003007005038a4180320b40d81 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 827057167 1250 827055917 827055941
    0xc020a09090501150602031b01020406090905040804030b1602060705120712060305030409020909010b12070804030e1e180f0610050708040902030403081003020303040303050c010e010e100c1b0303 86
    0xba03180d4038140084d070312504075402140940c10100e9245200920140b03440ca154050300c5c0218509030400c0e0000e01a0003c174000d4035012130765040001c08008010741210040c1d42c03c10f811000c070303242044000d409041540504801801400003041006008405807903040034807652007182903903848411a14488071000c40100b25440d24400070228406200410107000909009655820301c0310900444070b20603407023a10702090410a169285d40411801174100110349055162525a4101100c8900906c240c166001d05140b8029142c0002054811307000720b019528110010308800c00082406d8040f204241c1542c00000083d41c1464030b01d88031500000c2e94140682094000c0c0c641e014139030481c6d0000e208640d4008244014990030000d043d91114891501181d914110750229480e4000e9110040c103102c0081043c580000c000e400040c000440f04008000c01054981c250307079240c8070054085900752820316000000c612030078506006554004030103081d540150b500310020442c5400d18 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 827058417 1250 827057167 827057171
    0x1403030708090f21010606081308070f0c0b0405010305010e0f1f0e04150516050d1505060a0c201c0f0507080708010f050f15040209030f060a05070c020a09090501 71
    0x441041d99070003020100c000c454001820390744e201c20303401608450880e00900f040c0600c0d5401c0100d00c0100b181b4a40d022680b20b69580d4403a0243d00d49540d0f0700d1409a8010311652001c04080b524940202c0a0400c0326401d0342c2c02d1000342d90782c84540a10450036200c000e0320035071440000c0c100d0741422042045038031104055400965488664225600c800d403811102e14030b9421032507000031481c0c007540381c0081120b0071030340c1c2c080741d4004050070500c6099403040650f0384400c05012b111404c40c0000c00102000707401c40d55180d846200044c000e440020040741c11099103100b183c3c040c0000803182680c102d001d095960f03c1c4071040d1085400700c9940c50100d410031038851050000036810702c03925000300000c0008044940c02c01036000d007510300301c85045a64900d401c00704660f0030400c4824941000341d004200c24030310700c6000460041e200b0905542d81620500c800051010800101240304d080c000200700f1183d10340000844c1d14031091400654000440c50f8180145030b0170341c1c001c0c0a00b82c407613000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 827059667 1250 827058417 827058439
    0x2508121008010903080a06060206190b04020904180201140301302307050d031d03101b03140f04080309191208160503161103070b0907140303070809 65
    0x188900390f64442904400142001d000d1041c0c012440c050800a801140043e0280c0d2520044042c85070070390207101031002d80c80e00c0d014602919543d044408000005e4000c0c0103d5411984004044150300401c170f0008410202104600d01c00c03030b060300e050390481903a411680c1c181c070030090f8441c000320761446900d12550041c000010261f0b80051501e4081e0b0b480520144054500c903424030340c499010a0103844205962400658402640714240c041880e40081d40340b01c04002c00d107040342d21881102c41c030b460000341602c44000c0300758098803ea90ba540c140142c800700003200c4078122013a40c0c00809044404045800a0a41c002460380a850441122102071010000700c03504281804266113600d42c0101d00c0848640c49288585d014039011040203002c040e080740200304d480003c004808103c45101c1c103d0481c1d215001d145804c0e05040c040300d88a0005081001c0c80300b801b51195400d0340314000000586800c03480311107180d004010091400d001054070703108176603405010025809808581 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 827060917 1250 827059667 827059679
    0x50f09040f061509140307051e1914010302040b07030f050705060a0203040b1812030a020717090a05030f06040b13150504050705120c240a030225081210 67
    0x412080107001e004045414410360703e10290001101da086484a4071542c00250401d44000800d04220f40c0c0070348804030284142003440050284403065a079000e4044c0c02c0c1d0b01d110740c0b99490240e05940107481c902803010320000040d01207105d14130950003441004d004003030209000700d4a018044409040c003921309500c0e6030b14503052003001c4484000e840d40c0402404180708295600c3c40e84150000c00146001c0000c0c2c3c0482d594060b10100e1081046000000405c156001c0e0195503d0740d900009105038168101c407034100680100003014003500f403207440090329260000f002c401c1c0e0174481d409001c0c0c980f00da499030041031200421120b0440c11500180300001d040614004c020b00316610f000940d4240303458603a0074862540d00c890b224060248030100d94001c08581c5d000200c07030480c2c2d80b001100884c10010380844141d00c00c51405030001c12240402c40d059001840101030301c03403100640344401109210101c044140c0605102e10a10141e2040071220071b0700c40d00081c103585117509c0f1030340d100c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 827062167 1250 827060917 827060921
    0x905100f06030912090b1815070b0925090e010b100e0109090c1b0c0e010305032110030623010f05030f0c030d080a27050c040606050f09040f 62
    0x35114000095669485805000c400e1a03142c00d801d841d07150195039a85809505407842c003903403806410b60b04140031642031070341e2803108015451223101c4000d82ca03400b00b4108140030705011030302e00246014164910548101900d420a0481601d1001d0891607040205090041c0100f07001002290360700d2003d16032550703c00c542c540305245190707107030016009503074001450781c2c0944e40140070703180c14000c410144d170750400756900c47c3e2141e40d013080000940b941410041c49036554407c51201880000202c2404000310084c190701400d000000c50408041070b0701c103001081114500058040e9400a05c00140183c1041c4800c001060114810045104a13a0020071003039101c2a07580100f0002044942400d000007241c00110794047c20343c021146001c80c0d1203400081740a802c10001c04000344244c0070743c0c0e000a101070ba101400314120b104001d80080701c1112035509549920840d034511b02107241c135003c1d910595000350740301800c261040407041d11680140a182c3c2c1d20549500c1c8c0c04070440654 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 827063417 1250 827062167 827062169
    0xc03180806160e0a140d060f05040b01061d092205010507050406120b090a090f0611071a25020f010e0c0429090a0222090b0d05070905100f 61
    0x15a10228204100070070280103c0c408400b1036009401c0c03203030100220a4082031004c0d2003e020354132400c00f42d00700d00c0d11a0003801d0b092200d40d0381c1c626210501c01030140d8001d0541c1600d0990320b0318440c8003280400300382c82c003403001400ba41c040c0000c0d002410f030307c249441c01c01a4024281e036110541c105036803031a003519012140000042c0340880d00300142d0398003081c0c400301001140410081c440e01c103c0400d4004c000180754048098640e1118000c019804185030021500a1810440c2002902c11040264040d903400d40b000744040f00c001c6c4000040e80302c030768041c8a0110300c100003012000307501c0c14090317040b44081c025806100300141014078280910760103201c04c28040c08018111070104070031250412071030020307031030220b44082e070201040880c0d075078564048545d980756030b42e1085004087d10480d100d81d00010005e40303240c641c00300c81c50175070310540e07004000c2401b1200c261002d02014401407040a08682c1c040302c01081061003e5006a80240f6448070240c41d0b5510350200c0c107001280b03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 827064667 1250 827063417 827063431
    0x4030c360906110c0a0201020c01052502060705030706090b06040522081306050408060a1103011701060308120a0605040506030d030b030a02060f07060c03151715010f0f150c03180806 80
    0x20300c02240c115a410301001e649c0140034281103041528603880c900360880601071407043c43c003402c032404040d907440d08140c4d00600e47c4101107996407100c5c0d04d050409000e206d035046032120780140208038607183ca401003134464451003801c800c04014103002c00e00d03030004d011410317136090700300b0407240d4001c4a290801e41c01178101070700d46a60321880c200142c2d141210040000c00c0f003918082080c1c130300841e414100d81c11100d440f07100400408600104500502c0641e00c002c0c80c001e030000f40c03143c18113030150303045101300204003040109070760783d40c00d0006031a402c031502507058101c0b041341080b80b0f019034444100c00d440a411100c08000c6a40851060340c401c2d130703408084070710206800c0100181801040c3d0760310594502440f5000400d041104000003601030f06c607024016090104d1121400c00c011a2164a40c1520a01c2c039603417441d03403050050b02030050014009003d0001b00340a66001c504110315441580d59840758602501d044450300400b0040031202c0106c124005000350040001ca409494 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 827065917 1250 827064667 827064673
    0x1f021c0c02030a1b2111012a0309030906031e05280908030a02070303180c050a090204030809220905010b010801053a020604030c360906110c 62
    0x40428060015108000310f040c4005142d10144000f41030940644503005242252240b000100c440031b5420040c2c500380280c1d103620340300680c80d0140e1030001e4900c0070440c540094600404090040b0b0075219602e0003c0c0c045903520000b0890303c1d03c25403022200b034040122016040c2003501d400401c1d602d003030b54498050183c8102c0d8002c80c146050000040340c1840404100c0c034036490ba1182d109020041c040c01c0c80ea940895203a09060098000d98681d60302c4125080000f000c41c40c10034030882003070007024018880000003155150103031080700e0583c1d800c1270041781409071a07804c210002600c2c3c0789501191107021b000ca12692000c0c0078070424035100d8000483d45401c0c83c170004000c844141d009520845040795a11814001a0041c100c1000c036490441500e029004440e00105101c820007504181d00007800010b0180c14541d100c2500d036002c0441340c5d10803000d481d090b08071407036540d8649650504110b14000c025aa0b11040d0118403903000803403030b0f1155000041d5903800031403620032550 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 827067167 1250 827065917 827065927
    0x1f08010c091d070818150406060602031c0b03190807061104150c030320120912040b0a0c02060706020d0b03061005120309030a081b1f021c0c0203 64
    0x258100100c0405050b011042c1d11150000d1035520401150280000052115100214040745c8004400b030a002129200b2524058410000d540c50040d080b54261200c91900101043d61480441101e8030004143e0080c6481c01c1301c0000c070f0004002d1411055030511070210160303108940440c1c50103910380501d60f132585074100d5040140035100785205044071541d0400c030902544503103080c0841551407501d810b80e128400c0380f40541c020071902340b881d0f6480702d000030700d0f101e444201c4006183c5400000b021460740d407103400d0644da60b40b44528910040030b90501c0103002c043c08036000b8024110301407501191403000d43e004150164807000c01a00da40e41c00041c00d81c070b40308050041500941c0f0a50052100b4076003440050b86406450207003e110305048241181d00d51000c00680d03015080040c1520980086032400045550140011162900200e6105201d0100c0800e03040c0742d501220604101141030b07500f8002c000e6000818500361101c1a030702c0c04007444034501c41c9045218043d001950350b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 827068417 1250 827067167 827067191
    0x60c0708160608041220060c0d060e060607171210030b06090c1603050403060f0509060108070308120702100f02041d1003021011060702071409090d081f0801 69
    0x240000d80c0244060050710f00c18080003843c881c0c0050a000407514051183e03100500800000091003d5171200360710030788090000203400d140c001d0658441803901005007035591502807000d05411600380b0390140051000c00301103034070100c4a451840725100310074074140301d4480c42a405081607940440c8444d402c0c40900400640001c40360308a00c007100d1041007803609504904142c4150801d40c141c0c642d0069005003014081c4c1c064401540d440302040c4032070b10b442c1c2d1148000308401c44a1900c940301c1c6100016400001203491400e80f40c00c546000d180007041c16940c60301c10b001900b004111b02c182c159203100c540107841002440082e00101598582c5040d80070007101080c00406100c152100c002d01c402121441c07081401c895040d20400350150780d0503000d0321020913107010841e05c4c3c000c100030800200e5001c14483d0a4540e011401d4100090000500c00d00001c203e403110040e50190010b8803a072400ba0050551050160341d2020f1704522941000ea54006580d00059660b9192000c2e4100307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 827069667 1250 827068417 827068453
    0x60c0f15191e0b31050112050c06031e040b091b0102070e090a0b0906040203060c1206042c07170c01080f0a1404050a02010e012c060c0708 61
    0x6012803030a01ca0101c81041d50766250300d54000c010a080e503110303215041500d80c2486088004a0f001c2600f0340829280c5020b080b132121002d02c90100ca00d408000b190000a4041d840c0c06a6044002046014450f1082c00040d40c409031100c0c40120320108048112402c0b03403045807040e4071440112107070341001003401c3c1c42c040400d040c0344c6d01551403601c0f461060b6030000e825001c41e10724120204080d242d01d0349141c1403801007034015040400c078100b0850b040000145440c00780340709501700d4201c2e42e40c250b44d00e105402540e101504202c054000b1629a141540112165002c0080307540c47e800300702d0b03802c0c4a00e800d100802c036103e60850310040141c1451403510f82920641f40707001d1b150045941c1d0001780126001060062000c0c50640403ca14145c140c0c0324071183d11401c6c101c4c00365424a82031841d603480120340100d000440090625030294495a81401c210b0105c2c0407004484030014004240a2030074056a500070100f4418558502d4003000890300030a50803001d040c039480c04104041ca = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 827070917 1250 827069667 827069701
    0x603150307080106051003050a06050d0f110f060304080d06091a03120903031e0c030a0306210506060f1305010303032013090216050a03030b041d070302060c0f15 71
    0x9041c0d15213a0100041d0315168a4500e0011030b900c0c000804e40d646d40e0051004000580003141c1010040c0c0054080042e1404035480840c05444030f80490703480081000b61807803444a0098118400b4808140050350400250041580b683c41c08079116445132800000c5410104500b03210364031250141c5000d0a0502065190700c14400c600c81c542a01e40c0046513491042c013584180540180300c0303a084030710440003503440144c840d1056944c0c030100b00301d0040c0900358501400403809032aa03048000c2c03030030f0000c50f00e401d5030744140540300965620003000b8000c1031411145070026010200c200080301c261240501079482510300003000100e10002d1403200e429406180c0c0d25020030086c00590b1a4002c03809001c9a10206c070140c1c1c1c600b401c8807203c52028480704020310911420b84d040d410541c041d000040102c500b52420081c3d030040d0017140700c070b41032400c0801d901030700320102c00c0c405418a00000d01d0925192400ca440b103140e1030502070301d0308882c1c191580d4409265000d12400e950081c0d2146 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 827072167 1250 827070917 827070929
    0x90f03031b020604170a090b040603050a0608060613050c1b07060e0108071b0201261603110711010c0506010906080c0603010312122403050706090b030703020c010b0603150307 77
    0x85245044c0e40d0320040b08803175181d1455560000309141100d184108a03d8016049400c1c1c03c584480d6140302c046c02030081545c00020311814004046241c0d280010107030304c100001445840a02c20034040d01c001084043d000e03a214004c00c00c0f000c15401503000ca0510440110700c010402c0510380f420041042142c0c2070542d040008580503c0580303170380401e07041c092621014041c601c0c91345034401a100b1004000320050300648284c040c0809043c06540c40d0f120b407911a20314100103c906070100c0440392200c4410042c10000d0148402107420b48012088032901030402c030031415820348459181481c00d03480400f0040e16040207010905d02403110341152030042d1382d0316046504540e00c00b00c41640d410a401c0c00c1000c42aa07640700e461080e004440038124285400d18484003d841c90301500009000a88040c0f04039100001c3c0f0034030402c044000c45442076107807419611b4490f000ca02135400003400743c001c1d40d21811070121f5507888400030341c080c1c10781444000e003024002040c50b0600030158405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 827073417 1250 827072167 827072173
    0x12180b04030b0112030909021c090b0403030c1806030209041d030310050d02100e150c0a0b010f0b0912010b0312121506030109090501020d090813080f07060f03090f03031b02 76
    0x1d500007a0308010091b01b030307514407203025031100b0200b92252080c0c01c0c48800b0440709401d00100d00d0074041407586c920701982c0030b66014008a02104d03401c2c0c030380304410001c0c42c0407803400c803204010251280d40680741c944001000070070f1202c080c0319580b000f8242c000b201d81031600000b0a009c0c01c84400720003c40100800c1d42c050389202c85540000301d0710100c45c2015400c1c820264200752043d5582e0f10030445811141d102e00e61165000c0300d203181e4807004081d0840d0040c0c2150000701b048075203d84186d04580380811400d02c2e0070341c0c1d00705221034121200710040c425900c48222200070b5600744124100410001e640648458001c404000c1c09040948a4407400102c252250030030740725071040303038196203643c400801c82c000755103803036802481090503601c80c6a00d064055020810040014401741c00c0984c05130b4801610307410a075449500368000f50388036601410301009154040c0c0301d024030174000b60800081400d06600d48800041c413142c07013140041d544690705401242c40b50310b03041c039400030b074401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 827074667 1250 827073417 827073449
    0xa031b0e07090f09020a170903041419031101050712120501060e0d0303020319060f06030507180e04021f111207030c15021303050a0312051312180b04030b01 69
    0x8104843c0d02c4501903410810b070001103401e03c050140c4d03030702115210700000c0304070030f450000011502c940081c000c0c50648603549090040520b0050b10604041000a8000690528580d00d00c4a010b02c1811140d0600c5001c1c0f0000700130500c0341004600c940210380b200600004514401811140140c020405004060b0360092158507504c51442d49951305050040ea2900d845503203000041c00b04442c600f000381801c070049058042194040c040360281c0e00c05010a482e56001501c1c859540c44101e028860104002c101d41e80340400c186030000c0c0050144802000c030b03104031246494005006102103644500c0c9000080c00c1027042e002c03000706060319141004060740d001098010407400142001000f0018110341c080e055044170488800300d02d2030140b003551307441c0641d01c0711100d89042d03011070880400301e0558500c901402d48903001d490303458540c404440c0c0c1e81c0400744c2e00c4950240100b0070352000c154600c3d030000003c0b9018240c40c00b2941c5d00c851940c9081c22448205030000c102c401c0b21500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 827075917 1250 827074667 827074679
    0x13090c0807050a0e190306091109040f110d0f03021b0303040f1e1502210307080f0a060f122604120f0c0e152d0a031b0e0709 55
    0x191a14509585801041c110060001807901c007510417102c4100c050000c40042041229841042c1d00b500c02c07a0192103020100c0c0412280030000c55003e41501c142810300300009200768414486420300902039a0381d4120b80d01c0320349446260079012005079000c1d000401c008481080c4580303d4403000c0b80118981400c0406403100c1503910f20a501519a6600b00d04d50380c84082400d4078064010f090304080c90345074001009590f5105c07820b0710b0350b014814a0741c0c0343d01001984112440748159448002558079900766011a4500051072254055950000440c5030098802440010002c0d0001002544a01d0503c0d103058a003488d210384100c1d91614801c5003891386c02081d1801c880070f00d02080c0c0c80d05a9800e0500010b4622f00001307010035002d980104500d00003503a40c0e4003440d81703a010600004110345c203124011844038180386080d02100c1c0038107100c0040e414400b504950182441d40800d6aa603150801d80e0031103a0080a00910307041c040c0410840f0b810f0351548511540381c140080c0e46004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 827077167 1250 827075917 827075927
    0x6131416090603020906371211120d05090d0f02030105040819020a0203060f0c0409020a020d0e010c0b01140d080d020a1b031e09080d11010b01171504090813090c0807 73
    0x3002c40c0010445200540c0741b03101381f50a4042c000d00e02540d50004030755240c43c00d6520303a4507503403d2a1082c1c00303070b8400000c0c409001881550010350754035014584509c210811880480e00350088070200c10070001d04c0010384080c020b46004d9031280c40c0e951345074150a00640ea211212000c00c0c402c540c802c1c440c01007d680c000404a8109100748824010743d181c980b10b86455115a80004600500002d00b0194450f4001a40246645c0702e80e0754115410b052401115408110b5074003034114421a80180521441880500354845000708203074640b19032540d401105801c07030820407040580c0820701d9a07005030001140c170b01c2084541040701d41d00c060303541c02030716481c0c070305aa992031a080d4102843d40d2074041c4005402808019045810000c00c25900503c914401e0340d450b0700c29424800c00e00700b5940521a115826842100c0b01070050781c488117250210401220000e500c03a1304c1b0001d0001258540c0300504180c1403007140070300141e0502c040c18090321350081c5c401040108a20810a10030b80c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 827078417 1250 827077167 827077219
    0xe0102130f051c0b0601051603080910020301032f04091104060503010c020d052101150210020f1804180f1103030313030c0c08030313050f06131416090603020906 71
    0x10a13441180c540720340300102c2c0c540c003d50602c8a080d40300c2c00e24140a150700950440c3c0b2540e94403048034a01510030580c0c1c1d050303000070300c802404000742e403600544d00c49201b00d0103020110001012000300c01d9100c00501500d92182c010741e04412000d03803082c00c606150080344050403041d07000340a01070008000a541d1903040b07021104000d4080380e01141e24922030039800310310b81086090890307543c5602d0141c0f103000b0200300c2c18015110340307a054254aa120300036241c1e081b50300f20016040a540840030351441e4010b102171503000c1e50311040d885040340340e0311f4000990350240300014100400783c98039450307000900d812a48260b1040c001c0141c544a80c140240d080d17580b504c1c01c030140c00064a404c9094126942000d440d500010040080c0701410700c00100f14103001ea8106c03008140d800c0c0340951103c8040e52001c1b40e01d6200e400382c1004c1040d503130641070062065021514408211203141414420780e800461545441d00707410801e502c5d020041c1500550208c85014403030f02111601d1850b0020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 827079667 1250 827078417 827078423
    0x210e01050a1a09040318171603120509010c12030e0d0c05060a09060f091209050109030803010506030720100606020d1e02010b12060a1407021f0e0102130f051c 70
    0x1030320b00040d04140c0308168404c2c0440d100840d004c011070719074000c1814219003002007a1f540c410210083e01032491000081c0441e500041d15404000720b11008031030342d90003a0440760502c04040b16120000b0b038031202038024503a055400040307040c2d41c220b0b05810201c03070310b0500007000074001c440c4000c01da000c110940c00c01003207240005c8001c0b451a21074040c02000b1700105079185060102070500280c6006400340c60080d6543c402c41c00e8980c8015075400102e800301070b10210701400144039504040f001550055090304116024030b10742c2240540e0f01c080644090410b80011851850f19182c5002d0b00014000a0020b4510203980c1d1384000d08c503520300103040d09102d00c440e41c11041c00b4000e5026540a18028201010460078100c0140c0d85280540d0f00c0300b54903142c200d10300005203003000140d0003159245c2c058083e0b000c2202d044400e2803602a29080e502d0340e10319a211801d00240700404c100c010301006518018502407002a00d580d884c1c0c4014043c0c7c0000c039500172140c0c8214024158564 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 827080917 1250 827079667 827079679
    0x6140304060f090506190c170c090d030c0b0a110316051603090e090316060f11070b0907080f031e0f030f010314011b030c210e01050a1a 60
    0x180c0d90601001800388038034820070007032406015006024001c20b950303200300d001300901d0003036a00307003040b41044500300a040310019140348909400401060f01d500d401580c2496451300b050700e86400144016a9102c0403004a03200100704c80820030400c0c40c0c01d5100043c00000c002c4101d0780901981c542c030000300401101940c0390b118040d56801001600c0205001449902803640700c0e00c0e0103051513107180190448282040001180950004112501820700005000103003c1d545e035180081c01e1002d85480101e81c4075075104488041c1c01015140980c004c902c185c80505208006505140580e0090391481d00300c841700d0762880000008491241140e90340300341082c0c0103031001e904a4020000049610300001041c01015035280c2c91132030589028403980c60880f0310b240b051f0790890750203a0700030a000c0410600030300400d019a201e800460341c1801c200c00d03202181410140c01489050300310160707aa0f41c0440d6144800309101d940e07409243d2040c20012406c10030098180356109441c803e01c561 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 827082167 1250 827080917 827080921
    0x10e331314011107060f0902010f1809110a0e031c0c03021f060e09030a17042102100c050306031b01020307150504031d0f10020102091201050f01050307061403 70
    0x411104180c1e046a10144020080b480c10210b00d41490380c42410f007982c010b1b00b456401c100b50301003803040310032095058482d110700e40f074503040544005c1c15071050311860317404107030340095500c03168040c04000c0c4059001880d91030040c0c540c0600082350013102507002364012510b1001c2013203603204610280301c640c1000901e14005250807481d0078072140300092001e141c0c003074018403000d581d04644199102d0030510109a03441e80c1140341da178054072008000107031004058441080005080350381090184a0700c0300d00d14450000100146008280321005071300c0f0a0748010b5607141c5100d000000c90461408a00c4c44c00c0040001e50744280074a460240880700705402d000f280e00800884200952201011005524104401004100440301980865255040140c044200d074131080b8030008000d00040100c60b80740144400100000f1014040d99800c000050441e9030b442c4409110040900000c01c80b441e00281c1c0141c500d0b4180e02c02da0003584400702c00d00409421000d4079480501c5c2e242c46545076 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 827083417 1250 827082167 827082173
    0x8031e0f0925120b01151407030c3932030f06011502010b010504060507240207080c070b030f01090504051009260903030d1805010e3313 60
    0x1501042d807000d5203103030f00a0f101d40d0401c101c00311028104c4102c49001c99400180030400e58550303032200c401d03a42c5807604100c0351002a00440e0b18600f440d001f401c200160302030802034074410740b90300d4401d240388820360310440801c05662804c2c200904055208150020840a2400440301d002400896401c00261824181d03880400404003407010503801c560382542c1d1075501801d00440b0900840041d400d00c090300c031a950243c021101100c0da690b880a161500da500c0315950007500b00e0020060b2801c81060181001090000d0100240604a1030341d660103140380d000e2400300598402c0104100a0003000151100302034070a0465040910100f40c0741e5403031501a0414004013600071a1034944506075090084400c1c41034126241c010304907001c0c0c20120780c50a2503000c0e5403155035144d4000c0090741641540c2c0e40000740b51201e06040201020959030300c9509507070144841c1000c03030f0b20414140d424060504800344494040300c032215000540e15900844a060040c068143c0d8681c4032425810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 827084667 1250 827083417 827083483
    0x26040b0702120717011a0f040e010b030f0106230d260d0509010e062505090a0603050712090807030503090309100e0a050103110901110a08031e0f09 65
    0x1c0c2c0900181900c0314140c0300c5800c60030880d03000c0c1951070b50350b2910240004544003118105010f11004006d2900014a5410040a40300f4216540b4a035500d441d841e8040e038400304541590500381e0070002c9400307030402c102d203000303003281c4d11070100c000d00c400c0442c2c0c0c02e0ba22a40b080744035680d0004d4602d004251250720805550707600250300d840c00c040c002802403a0480c25403000c6d000d03110a1000f4001400c1440c4c4950b135a103800c1d80e0361090b5808500740c0c0c40c400b107202d003141a40400340f0308219082c00c0c024000511600724541c030000c04030380c9800070001721650041c0c441c052002e4074081000b2030026529a50302c0790003842e200030706112001001c076206203030410035240e0800008050800100b040075000b8155036001e0b511900490f0b914401040544c0640141105090950411030904540300011264110728903030307004290140c0035180c000715031980e0055114250361042400708414500c4d5081e25068001d001a82c10345090042c050030900108a01c1c5040c180303072000f071500c1040c00120945e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 827085917 1250 827084667 827084689
    0xa0b03071208030415020705060a0e07050901090e060108060421090302040e0c030601080c0d4106071403160504050a060e15160b0c190302030426040b0702 68
    0x1411040301c60300c10304001c030b5a00210300c104d216480c10042d195003036000609030b025902c0e00030950382261002400102c1c10368032109158903201c2c1115183c40d59400840d4115100ba080082e1081d200d030b030080d01e8503508000e03460042500c50001c210500d800c0d1210040d00d41c440704072889a42d1904008412540b095203503202840d0010b000300802c5c0344a00942d5540c000462070036000340103040001030342040c0858181c20b010f5001d0700c203054103c400e5032055800c850103003020301c1e41140ca00c00f02c03039600e40c4140c140c2841203200c21362060642c1c000041502c6c0000040240040041c90615020565080d4060782d0f00702c035050180d55110800844191034501941d00a95001900c40100186071030740b00408400214058a1050140d03200c030a03da0000d1040c4882c4002000743c60b4186070001d0400800380358007050f008030f1a400c04642c03458446070203000002c61400241c022040c0f106203c40c01d080d070032070141400071140000c14030248840a6004510034201a5030000c120314056494142c8689 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 827087167 1250 827085917 827085929
    0x30a030e010617010914190204090203030c0a14011a06040e101a0d0f020711010f2c030d0207030b190605030f06100803090a09090f06110a1103040e0a0b0307 69
    0x2110103c900302d011402803028200544800922460f11140f81c04041041c0380c40a400308000e030507081e100d8007804090480350b4400ca80521040040840300401880020400c6102d40030700711444000c451002d0175a2072200506241c00300903080e07180039555600850b02212622240e9003141c2e81e0f2545d0202c88042d50380d000034110780e0b03101c456405908401000301a047c4030341c0c1d81001103041c2071741c0301d400700d000e0b0b10001001d02e407030354610610540c05000c2440d07080080e840c00e00314030600c1038502001c00910814885d0840498002050707a4078061141a44c082440d03c014401c40745035481e54803080b00042e1445044007104004110a071382c0c25081100540b40140484070b8905120750030303650b00d0504585541c0340603c1e4442c04129014084112001d440c00140170b820080d0800a40800403c074840c1c085401041184407880081e2184c0694401290043e001d20b031100710f4480b01409801001c0d00c00b40c015007082205025681d29a5140741d0400140031001800603030b08401300e803600e54160005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 827088417 1250 827087167 827087189
    0x306090102180d2105031902040b160c0b0c06010303080c09030c1c05061f120809130209180a0e071d0408220311010306050102031e090a1212020a020102030a030e0106 73
    0x4c04401c642100055001d8554901a2a08046144181c4040b4000e41c010b500301e4017810040ca110380c43c014401c5032481c90181c10348442c40c594502d4003004035844008801c0c0d56800c42001007041c07680140e119079024000b030b035020f0720b01500d074400a900c40303400071581481902604202c60000c00e61007003400c0e00a034010121202810701d042107101c070b071031007504040301416884030100d0070301744441070744581035480b2000b141031922003010005481c001e141080348140c0c0c28006e61400da03407026101c1c1c1d0540305032200054282480e0b06d1b580291034a481090a180e03014000410444070148010b0b1503215180c61400502d0700c8900e000d60b1300e0311484441c0114246c1c040c52400d129108003901c123040740d1107030740b407401c00314201c0005405840c0c1c14414039016030014041188c10f00c215a040030000c400000d05075107400280c03400100743c40c0c1e03141c0195002c144491030f2201001899032045104100340d00007070051072650781c0000d640340b24140c540400c0640b03030f030201e11003641c0c02d41111028000c407400e8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 827089667 1250 827088417 827088473
    0x30c0a050f1c021f021303060203162a080f0408150a0603150b0a051c0c081507051c0c110d03060524121003020306090102180d 56
    0x110550750701c401190303500c09004003260400910005080704000780310030b0300503041c03210708400c61074034009050300403140e00e81e001c22401156648940e810000340d449050b005890341420205801700034101c481d11002c0c4000540c801c001c56826003001c0503102c0680c41c080f280c1c0d03449440c0030703455030280305802001000082004034050001103502494840035000300e150b10703600c240d100403d680d07003444041c2c003c8002011194000c606500301c10401c500103002c13480c044d681c0e4004900c5011a50f02c1444402e02c50031018030070000610001001400d40d4002445080121204181102c00190001050140c0000c0d0400080d600600f520b0704444c02080c100302007040d203000502607108403009001d40e405a030b00000d1215020344185416220b010304a01030744007407403403225520020086010061072003844001204011048400d105054444080643ca85184103151800901621583c10303a401444403150a09407c014981c0d000d07411075191906079160300702000402c50206021142c5641119 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 827090917 1250 827089667 827089673
    0x8031b01090b09010b030d0329121b0a14090109021b011404170c0604020906010903080d23130f0c030b0708060901050d020603011e1503061a0304030e0d05030c0a 71
    0x21040c05c440700254103441c00d403956140200d04444400043c42c20310070464480300c02c011066031042c6403040014004840d400b441e526881e240035104041c09000d004000c40840090900e11005001000070079801d5290114042c001699074005000b1010305642c04900002009408440c1034030101d014070003040001d145240c11200060102d50586601120240d110b403525803560455906102c0040075201c04d0711241d0030440d29840180001d410040e000740044082a5660f000b400240072103900004d0082841108082260744410004003132012030007081000794008400701485039202e044058940c1d482d203081800d03030806800c0075184030b04440c100440190000200c5020f1001190031620366a607441c20060319000f0710f40020f42011303013840104144c1600e004201c4404e14900001b506140d00c0d90400a2100980b4200348002911101f040103a805211241c41484820651180c5141f5040e01c0181c05141c3c601e03840c0740180c503000301c03050504c0b0b8240309859522000c40140e0b880d03140542 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 827092167 1250 827090917 827090921
    0x20708070c14010804110f01020f1e060f010812030c1903020901090b04120206030a0b030123090d05040b0a020c030102042904061407050c0a03030c1b08031b01090b0901 74
    0x101450b4681a480c0504122540c040c00d0f80511a903070044e003015141d003a03030060000440d01502010705500c688125452402c0041c0059804e20643c01034540c105444900036901d000c9015007602600c941260042c01a0304010460820a40049000319666107450842e00124460741400840c100e204030702030402140c2c0b54009089100090344e62620817a200c5070401800c0c0305900c40c450341c1e82e02d201140d10040c00e09001955100c96425400180826044040303070035100912200c14030f42c1d5004032401c1030021059142c1e41c014904030024404882c208402401a02c114014234200100115203017903102c1c401c00905c02001005002952240d40c0d403001045070904203040e038043c01d054506601c005044010940742100d00550301c148664015103030756101c0754400351040d5441d0165074280c41c07054868441070001144241e0f0350000145950410a00c07420800300021a0801c0300f8104120f071007c00000ea0320002001130310701268126000030917005240e50a4010310f10900ca03820024446419 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 827093417 1250 827092167 827092169
    0x51516060f0c020f07092c07030209070f08060127230d0c03020d0c080114070801060c03021e0c130b0114121302060c060406060f0f0f0315020708070c 66
    0x111070502140e101c2c0c0a040c0d803a0324000f03149040c40da01941e410045000281c02511030b100c650300350340f5841c2a140c0d03680e0b40348141c095001c90299002940170400c50030301c24126075003c900c5280020781103078100001440541c0292182e0704200c5016500c54248041c0503646408010700480d8544075a40d404c95440c044404107403140d89881c2c81c910000080c00c0c268419400c83d944070104694640c00d6500b0060b00803042c14040d95030032500500490034910901c01c054500ca8241140c002501e40840010b190350b5058000008010b0b091101400207900041d518070343c01e070316141801c40c2d0203403845458503100002444950008900c20100c040960b01d81c400f018000f42a0b8070070a1040e5040842d110902c12015481c0b00c0912507000115080303080069001d52600c020009451f00c11080703e4189842c40c1030710155052603580c03008200c80d407541c41240008001e000c0d540c211041c60604080d14071003103403002404540e44005290500341059040301e07100c86c0d00545013a11a429820003000441d01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 827094667 1250 827093417 827093441
    0x4030e220c08060d03020312040515090303040605150d0b061f090e07230901020102040e070819050601020d0503040f0209010e180610031401060521011a0a05151606 72
    0x1860340030800b2800d00400d00300c0401e170580c005619180b44034200d40e098a00c000c00a5500e40114203403002c8009980f00024060f00c40e410055031079041c00e04040d02207500c003078004c4c4000c0c42c140802c01e071591900c02400f030846070030006000321682e602020504003d2052002041018504141c01019030440c650409440d000004940641d039242402c6d503104200150350364801d0344444400c0e407407070091401003a403600188005410196286001c21001e8400d84840307000c240c0c905c0c10402c1165164480b000c160f101c0c2e600600090038400000707500d82031140e4510040250020000e01800300704003e900e4803a80c0a44103581030741e9a40b201123102c1909130f8200130326510003e42c02407403007800600903008100d04203821100030718664030340382d01189961500045540b070303510002e030301e40d1200400e031070074042c850030702c03070b4103407a51404c1c9084524010300351800e401410400704082e191403120310141c40040d04c2980461002e00c2408116000d10801c50054001c21121941048141e401008081038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 827095917 1250 827094667 827094677
    0x15041b030f140f10150c03030b010201090b012309040318060206040c090f0f05090c03150f0103020402070206070b130b01080a0b0a0b04090609080408070611030304030e220c 76
    0x81800c600103960a42c80d540880840c03150104000ca0009a0300640026481c1e203d4001140e80342c900080343d09a21032a0030100f44900b80311010305415009600b00000d09100800400c4801c5da6501e10854041c021041e8041c45c1e5400345e5040740c0e881642c0c11800e2001007841440703280c540340041020210302030045000034500c1000840c0c6000040c00d40c003882d404220b8500b01030809140170010b101c0711030240042d0f5241d0b0307005c100d80c0043d8480e0a0160081001074203030645c012091505d44140740c0f88185101c0003100400106540c50300c002415a94102c50159540802d4000600345024200d4080c010000300130070302c5011075540c040703194480d00c5a41181000e030707640d040c8591101c00c4140c016119040310000541a0405580300c113803200d00081c400a01c00b410b83c3c64810443d83c46540131141550000750a111005040024400401144c901228426207090400e502e902014100a05110300031102c42c110742c2d540b00e6114035480d454007400e44420402d02d04400603000740300180300824 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 827097167 1250 827095917 827095931
    0x6040e010633050f030402060909070216080727110406050c0c0604140909010608070b0d0f0902030d0c0201050909091b060c210903060c191b06020315041b03 69
    0x2481e000c040420003035032281410114480713a480f8003030b40000e0080342c0c030060400c9040c400d0b5a4510055001c0c41c46035001340680a0360420850300c11005d900035100ca0341c01100f04200070640034414040c60031800308415552003940c0511000350031340300d0700c00300102c2c00480d0214031039a00034003400d00040300e00107c6203518011004e01802d07200340d001c3d40d15000041c189050f024240225070300e802880041c000519166035410903410318219800449041e880000c820303d031144540110000206414010084060150300003507a0f00d00c2c00d4829002d21814400d8481568051025560764610140016500d403804010f4551111107008007250300b080142e0b00e505180c1003003015600b0240c1d40d0780041c0f02e03911180d003103c80e04c113101808c201c0d03810740200101009506e0a10034203004040e49448251203000c100180000000c130341c00c80f9020450a010340d200080030441500d95865000300703006136a511162803441c0c41c808923225060b0841c0c205041d400d410141800c502507035000a82d000c101407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 827098417 1250 827097167 827097239
    0x130501050313021c02041b0210060e0105090c0409020325140f090a1815120201080a0c0e040e0309040b041a22060602011b110607050306040e0106 64
    0x54001554110b100300e98040d80100182080d80c0030060000e41d0004000303920a00d640020184c0313408182040103607645000f05540c83e42c0400403012400b6070030009001c110f0800b6840e5050302d0051051610032141030010441684607441120040c0c400540207540d40d187c074841050002c550900e80d40758005006000004562042404111198444002529140e00701181030b034550445503003941d0066018100241001c0c038641038210444c51042c010611054411011040640581c800e180401d01d10441c2c500503030303009c08110b60114106078009148003060408490201a1660460300203180c10042d0800d510000040d00d0755400403142031000c1113101043c801507407a4400b003040320070b1301c3c0e289440c0c0720718260f000211706c801d000c0342c0c81c1c840d0408002e490717045d0b4109900c1580981d40d50340d4050751000c1c109070041c165403c0c80c1410b944000e94590881d5a07400e00a01d58410020007002007212596981c02c044074071a0206e0082c00481e07101d42281c039140158104d01030325007002445074048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 827099667 1250 827098417 827098427
    0x302010f0518010f020c062206020613230f010e0f0d091401020114010f060206010b091f020715050d230411040f02030703090b150d0201051303120203130501 69
    0x15540c0c00c2d41c1424041c5040c0070054910841148115065004000c0c960b035064881401030103180181c100f5441d00c0000140c0100b580620a40103103046400c00b008001307181c50b124060300007069002052004150300d2241401c000941d641500800340500180e40c0301807030f81504a9010340c2d010340b06075100140400105a550788c841070403040032620411041140001c030b03004c4c40d0704888060002045c00340d0021680d201062098004030350f41301440360140020750341080407502605a0402241c50300078944001021203d56480704516111544c0051031407510070b21110006011005408c0d4050580e1800500039420440b80760080307a00d03080010743d02902c0d88400c4401401c2e015403000e0903031501d85403000c024010359030807504a5211440d400015241b803004501c41c00d100d80d000130704a603070743c600b06c0d0755450040c00701507003039482d010410825986e6500380e00741c01c1c0e03090800a40d52034900309410262050355001070702c44103400c3c0c2810030302e940100c01080d4015500f80c2032000c880d200d00040d41c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 827100917 1250 827099667 827099677
    0x1809210915090608180601031a071b0f0c0e0702030d11030601081812160312110f0d0b1c03080f040b070f050705060c04090e07050303030619030b0c040302010f05 71
    0x400a540d10b1010803019001e070102039041115602c000740105906150646060401e0b0b00845000442c07080580440d106281819040301e02c03890030303d124004c0c00c0c100f1384007542c070746402801c151404002001000801c114502c010190140a081245400308000c0c0d201e8200307204881486082684011319601941d0440748a04130503190030b08142c40340403801c0340b00c4410311109462445580600f907001400c2038090500b0300c040071400061100103103401401c80100c403500b00401030500da40a1001d0070303104140ca02d03103d90000ba8580b030350f00300b842c40406469903528054105101e48191103000b9000181364040c507001c2d880c1d0034219110b16071240aa408102d5010380340030a0030740410003e5100d811618000d0340286451810b1851584540c1c0c2409000c1d9905142c00308005820400000c179409031900002c096030103003031043d1a10010980342e00c0010300c1c0a1107400c0e2507004001d500380841ca500c01039908007001243c2c91070403441545607a8003901090340400d8405014010f000d2048040750 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 827102167 1250 827100917 827100959
    0x81b07060e1c0b070807141c0e010207050709330302030f060f01060c020604170601090c020f0601032a0b07051501061d0301020f0c0307060c050702030718092109 71
    0xd441a1344606040b00c12000142440042004844c04184849240400340420154044941c41c07200c2c070031031007035040300d071000781079243e5074014010b4501092002c20f00b0401c481d41e5200c04150b003091302070700e002802000c007030054821031003400c1198000051046a410b4034400e8044414811110898036501c034812200810782c2da24000040c1b142c0b80c4285814264540701418460600d61286407896003500204d8512000e40d002d0b1004110724040c500604c0c04020260014115007000282d0207900c6000500001d8120000304010107008040440103400184c40040c413003000d00e841c0c2d02201465070042d40140d42500c502003000010319082c51202d4100e901030348035160b00b0b8003441a00d114101180c01190360656091002041640840d40180318004403c000b660f61007e662608400315001c0c4088038040002c00c1c4150b6006840002c1c0802c10f0710751010102400440708803900700585140c0e00000d14907070044800c180e4500203101582003522503900c0d801d260907210050a0542000c00100c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 827103417 1250 827102167 827102183
    0x80706050d0b060f04031104020d0c02010902101b03050903160f0816050a150309050d0e030f030c031c0608011128020d05090a08070806010305120313081b07060e1c 72
    0x100001034458207c4d20981c40301620150070b0103001400380049a1061080c800584d46800e690000c40ca0400400d00c041c20381070230150784842c401c1003c02040e2011b500001c052180005846940e030368204200d4545035030603000300700019110306650b03018076468032032000f1511607030541c03450a540840d218019114041c00d9514107030314109103842c0240103600c100781070581d6608020080350051010840150058981e8480d519400052510b001808900c005858009000343c903541360021044400c0c03641c00d00c401c0c01041c0804141c10740140441d510032042c075882d04241c2c15000807410080d00410304010203290030421800325041c01d484d0720906080040e00100041401d0f070f40190054403010030301074112046c035500c80001c1c900e002c456400c800d800d9030044004000f000b8042007480072030581e41d0040e0381107061014407020f41c2a003140d0020811003011036500c000080828000504000e428212030110b950380d94054215060302c0a61409140031491500c401107400d0107500e842580a400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 827104667 1250 827103417 827103419
    0x150903190c0816150f02041a13151b03020607081303090509100f03050102030105030f240c0d1a03010b0109080c040b061309020a180825080706050d0b060f04 69
    0x3840c8100d518808085610240101326120180b16030300c502c80e4205800c81c401603445003400e421040380d0510081019004c1410800c4804801081c10700404039402086a0010000324100941d401d4209601f42e55140100d041e0001c10f05038001110386c040c3d1020381360141252640010303001e08140480c00500032501c4840c0c100001c3c20101610743e0b1042461109a03000341e1140c0b0408021900c1d0303403082c0c45a0b0740100042c0107920b0140110405066100d000340110b000d01c1c51544082c00082c03882043d02071a650001d400c4101c91421689072418041041001100c1e906118044000d0081503074029032801c103501a0950190902006a900c044000c0c08a5000042004050f00360b1000d00c076084242030100040e9003109040c0f2402412900c14003588551a540340200381201d8ae4419281400282100300b040400c04034010034804001148481240c00c459226010511103030b01c05941e520680400060761540000540341041d041402401000303e490b00700001d90103411044e40d090501080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 827105917 1250 827104667 827104687
    0x50c03060108040b0606090402041205010515100c051905010c0212030702073f060e070f03020105160c14041118130e070306020309061303080c0c150903190c08 70
    0x1000340c0c0c04107009101500c7d007911100440e00784d801c00c1c1e01c603140041e014111001080000e00a0543c089034001010307980740060380010b899003480755003410a000c60b65440409004003408088003030342da090700c07200403e1514580a8001c069480c00c6d0780060007411900c02c00b0340b41e404222409148039900801100e400c281d10fa09042043c0090b1201d09416611050000b4114040015001c2c413519042c152035100c0b41080025128030202c4501290041c0000f448249400e190303690580c0e80a1170403d441d41e4020807960100c80000d80d028180c000800e20019160340e4803820031030a0001928244100c2c00150860783c002e0190482d202440c40198030541128204080300345031740801181c0104118803007889250400280d03070020349400c0e40000c2080b4044008200c0b49403c007000d1107101c0410815914003c0032280c019000e502940000290802402c7d0108000b909010940e006810035082072100d260b580e91100f03088118030350790620107000c1280280440090300d900b00b07410901e0150862 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 827107167 1250 827105917 827105933
    0x150109050f030307062307020d0f0f050903060a1b0206010f0308070201020709020c071a1603110f241b0f0706060b072a0f05040b04111804050c0306010804 68
    0x19400e4141c4404d104240c00305480e402100d0540d403010384210345c0030100c942d20544203a0006d02c010f0655008111030020030754070220302c40d21040146000d400008020204483c0d13481741a1050b6418171600742030101c1e280c09503009400722424914101d0354188a40c0d020784c2c5400017449818044103a40c80c040001c00da40034000c00d140c91051050b26402c503120741030003040380c00051400046910803041446a16040340041c23221700380d002d44a5052141c18900c40c95800e2178004020104585262484200c040c00c020a0b144030b01c96105441500030340958184018058201c25032201e5104804070700342d100d82e05000f1000240e2140014903124105900420036402407004880d226a80c0000180c20380203d00649030341442403045140d10750b9440c2c80c00c502503009040300708441590120400c03010070212540070860303100340c401081d079200030b00020b0024045803038a4181000c1c00980c2002100c800300403a030b150001190704100c6610740641100c041e000440f002800b00d565400807402103081c00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 827108417 1250 827107167 827107189
    0x6060f030a14010908030901150611030a0c0c0b070302010f1103041e0c0e0108100531061404080310081b06220828050312130209040f0b15010905 64
    0x702c2c00800c83c504140d907a942c5541c01101c0040c01a559104c01a0801383e95030555001040d461500c0c5110080030440c441e1203111307940e440828004401c41c83e500304840c0c168181d00800142030002d072189190704000e0701078003101445070b0304a85030012060844c1200003c2d00d015540003c400f07002e44d540700340303000c8190002c55000c1d03c101038031180004182004406c60f034040e2110308042c000158110410f041070b540d02030200552040c503440d81e46168501181030422024420b040e00e0b0f14101103080600040c11b04007040303ca4204000204001d01409c400214000d44400b0f584112040da200300c40c43d01d5402b858400400c28921080c40b9801d4030b0100d014102c2100d0107a10041c0300542b0703088c0000081e8066001c1c10aa0300480400048101040034142418440c440d188200c03850954501e5182c1c0b040014401c000740118000c01d008a564000d023680d09603001d406d11406013010308004040c0001100c3c229a9101920006100708440c51803600d0800b1041e15000001410702c810402c6100d01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 827109667 1250 827108417 827108453
    0x9050d030905030703030c02010206130308060f0d08120108160311090c090a0e0a0b031203060103021b0d050909060103140c0c10091211030c060705161b060206060f030a 74
    0x2c16290b078140702d00c90065101c2e4860031a00703e918400a82400b02c003c01748140303e90b41c081b2000100c2c0e00080310691041c821582e2540c2000d0900004100b04015030000c1c040d40c8021441e1002403001001c4c0c14182e45400e804c65454060761034401220303081070301004221030310b50817440c0d080d403c2030b605040c3c02c812011081c50030118550080340c41205560301039440503001d4418002c007050f8612400d21005003e42c042c2041d00d12a00c281d043c1c5d4800540001d0400d075001456882c03a00c451108452402c1c03480041e070703100308030b01c100007421a00111042449031407040c000c00d41540c0a40314001d09007680b180c1a81e416920203c0c0c21007960406191302e6a507028442681c146407c41740308070501c1c90300c41c0040c1c02c3c0d8841070f85801080090421030812242e8020414581404400529140e1103002c5251050b03070340041644c580221882d44000501500c42908040740e600f800c08081000d641a50317080302c0780350340d40d10200811460b2030784186415030845811980406c0495030580e0401503 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 827110917 1250 827109667 827109677
    0xd0e01030609090c0f091107020f120f030a2c0d02010908030a050315010806060322020a0312031119030e03120f090f0c0105310902040f080d09050d03 66
    0x96034a02c03040030b4944440741194030310400e2400b030114110ba212050050800480104100d0184102c485500d00c112440039108661051721048243c0c0e0303a80c02c010720040100701361102d440b150140b080d900d40145803000c0101c7e0348404400030980e406d49040040d070503d4400f0144032509a070a02034020141d040c240e0410280460214a01e00100024162042541c4e9415641c0c40d003500310040c0e0413001c28002d410481070b48144100b41d640c0b4810390350030a00c81a40ca11101c24412071071504100c2c5c0440081d00581d40320340c000244070ba1030a500c003040565450034003d00034880410003503032007155400b04134882642c018100d40d502c00e502c2142c111200e002241d01c0c10650070004504494101d5800c000700f03110404005c1141070510100d21041007000061034403d1450002030040d0050802d80301d480c00c00303544260100e42041212403134034a00f810359402d40b15100e6502201945c0300d03000d070500b180c44a030000a0201400100108044000d03079820000c42c0c04c010421500380c1403a14241e040107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 827112167 1250 827110917 827110919
    0xc0f0312090c141201140f0a1e0207061a030d050a1b0813060c08041809020904080c01060b04050307140604080712030e06030f0105040518061f0f080d0e010306 70
    0x11405110000a400e00f0740045080c0b51003d0200010880012480c0d042a414001524400d03040015080e4000d865041060219070b1105041401040342c99248407280c0a2405500c00303142041c0e00600850780503120500964042c1c0409004402d220003110303802d0342c00b07080c20703180591142014042401c520300c1c2604024170001d8405480d0070105809030303014100014540c07900100d0900c0000246180d09010000744c980d500d034036005000304d2003044102035138119520f05a42d120341c0510203943e4001c0c01100542014188078400e50061201c05616602e42080458030382906010740d402c41c0c0e001002000305c0e03414228160040d503102c100d10760300804107110119104d941884140e0240c004c0c160284a1268682401890b60390652070050003400e08000384286140007034034060664a080c4c501058a48803008569400e02c81950400ca6a0050300244001c02441d044442d4803a82180c1682418075110070110f0540e00c80ca110358042648800c0d911050a402180011500601411f00080b0781d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 827113417 1250 827112167 827112173
    0xb0612010b0f161103060702070b040b0702060409090606030215121518040b0702152205030d02130312080f0f0903040e09010b12010605030a1709042a0c0f031209 71
    0x2c003c050f02295110030703103c03050046080400c803060b84031003940700074072050b80b9019440071940710f00c0c040c13400803400014841d02907484650403180280520042042544034074104600240500d010482c4114541c020601b6191000c074190f92403a04c0c44920119551540414032112103980a084c41d000b07030011100502010010103102d104d14054600c54619103402000281004084410307598948030305000e0201c401d02c0542c062440480c41510440104003900b030a614500581c200c8441143c000200d1a2138155417002c0b00d011280305280c00001104403032000c1d280380d401210403400349801c450000d001c810600c0c142d141c0000d12072041d6460243c582540c0e071110380b011522074110380c0d1241c3c0040c0e02402c104044120605102c4000c001860502000030b445e00d880d0000907058040c0d082028602101c04000c440c0180030040c010404201440e400702d50a401f0724014018601c82070841ca1600e42c011f5028002999111918800f44000c41c0d80076220444000500b604050360b84240d2000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 827114667 1250 827113417 827113447
    0x9090606081509060a06031e0c0807140f0604141c081b0c120d110c1008091605030d05030c070b0a15300302030c0303010f090b0612010b0f 61
    0xc10100030310a03003610b03e8400d101c60700e41440980015000c0b85030910810206048011004542058603c900600e05a80c02c0080a1045035000340b01540100440022402c0754400640d5520380305440350f00c2d000e00f00d0010000e541c012071107120001e25a10701500d02a103019600c500d0340060407050200b44400c0c5807140002c40c0c0042c006240c00070000c070030b50607030078804011125681d0021502402044490524a0b0315140f14400780028002140004100380c030062113224201c1703002030690040080c1042d0010440c0c081a81d910712580210355140d540304141404890603250007500420710701d07804100880320350340010481310b582081404520300107903501400e45d0180d0b0a4000c00320715404000e801d00742c075404c181c0c0440c940444940050005410780b018a03000458100c690b16191903090a041e411032160544915a5020000c0041012040d80400e44255601c0140c208800d815902c103010b07162241d40c401141c24100e00f00104800c10000c0004c220a1440c80c00b070701e049c008610042c0c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 827115917 1250 827114667 827114683
    0x20d022202030118202505070608010816030b190f050a0b2d03030f130618060219030e03010603032312010b21010801020711040507090909060608 64
    0xa82036400100402200c03035550f040b4150840010020048681825454020018100f4400182010100300d10388503222161203883d80b40c444100e00c0601400130b10b800381c0c548855001c2d07400421101070000c2a28075002036407a424910001a6440160840e00d07840c101d0130004150b40560b0004034017180c2400c030640a91141e417001010b02060508003050000d041c5d034041c41d00240100e40c0314840d1403004c0003400b9608410b08514225440d50a180d20200341544244c9401e01440c40e8001071f07549031903040c80390210403103038580d50740c000c41c040c001e6441c4000e1b00c03140701d1040160300c0000c900c070f030320401c850a85c03401030f100b4282810101d4241b80481e0035102e250340241d011504524020740019005208860720140d840c03942440c1c146500c9220308002018003608450303060108003042404198000111262055401080b1075030703603404064040d5200b44008c03101b42070340c6d0800d060300d41130502540e40525069101c0303040d43c40c1040c00090060060380e5080d103100b0345980700020051130170b2103005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 827117167 1250 827115917 827115979
    0x100605131104050a09090605280e012c0705090105100315170a0201020601050604210812040c0816180b0102010b18010f0e010312030911100801090e1207020d02 70
    0x3051074009030602d1008c6820080500f1260340d13035480f4007503521a06a0044500303030141c1900042c80901c48842038010000c1110440071808288078030700c0049004c0140701005202d00045445d056182d1041c40f0408500b8841c4d150002c050702001042d2502a4014400c00d0021a0009026030b50720000d0401031f4118012000c0306030004920034080d03513418051140500000e651451800e40361510b11560030f070341c074496003101d01b02449986040081c0801118908a052040d40d201d50a00d428945108900f600c40c810b0a440f0309000003810031141d10350700048a84c120a501500c0c10701c5148000a40079207400c240c115542c41380d00880c20f80c3d90404004c070b00881000e90304800d60400c0101801c0c0c41c11034100c1132284941d4030042002074446601000b050b40d01e0f1401044240e12803415014424103880540d500c0144204180492a4081004c41c12107104110500040d00000503154407800c0000704100c40040c10001e003409402c241060000c1e040c070140100f20289018011507035030343d4180c000d40d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 827118417 1250 827117167 827117171
    0x306010c0f080c010c0c0203070b032d010e070c2303040503060c19090e160c06020d05040314180d0c080f03030709090e101a03031803100605131104050a09 68
    0xc0864000902c50a54900031074245403c0300308954001942d903203662b1050503c42040040024083c50106901c40d282c450340300e0402001c0143da60795501124024000d070191103141c00002250a4810040317069920b800c132802c80501d407190264403501101d20244448144010080056261401c0000c10711400c2040f2002d034451906600e02c51164040d40c20000800003c0c84041c400072600201aa40260038001ca036140001c2c0d4450540342010800c02c058001803010070704010748003664100c544211711035500c440e08211410000c0f060b60191030300e00c4039048040c1c50f103a01107041040003c0f00c2580a203020380a2985c1d0745084501d414880c240b18840c5400100611916580110100c2c000e44103032a0180000308070600001d6681400080405850382c844098200003c2e40b400c05044d140f0025083d20794411000c4050a5246e04180d0414028401c0101c60881d0346a24400ea105554009142c0c6c0082101c0c2c801e154098a202202500881020007001403256195400d4000070500380c800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 827119667 1250 827118417 827118427
    0x80a06181a0d051014040b0c090a0f0623040803071401020c03071a1311010e0a0e010605070b06091b0d021908090f010e06010b0d0b090403170c0913020306010c0f08 72
    0x2d0780c080e41c001645d840d031000303007031340c01e000010382c981080c03950110300001c6854850038101d00281c000307800355010031008a085040894216442401040c2d005400301d00301c4031030045000c0102a40c0710b00d10641c03030346410a2008000190000c0e483ca480e052440c0005030415101412140c1581d012105c1180c03480c50300c60744090310000050300640e021042d00307084003a426203519494008181a429141045858140681d41da03480351041000761030790001da00d2042d0386802d03000d021036011001c2683c9a00c0040c00007256483c3c030007805885103106d8124046155584c1034022000e4002e030103035084894080c803144072204212410300c1d00041c42940d440c0c0031030422440303050801240e0250303048680d0405806510302c031070001e040e42c1191440300d401a42c2c0c2c0d13410a03002005181c801503a603441001c1209000a2503401010b40e490701c20450505801d41e00c55202d942c1a510a040c07882d9005550148102c0c0c07905082e031b01a40d4014410f04003a8a00107003555001c6403689455401c6550030b0300459 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 827120917 1250 827119667 827119693
    0x4060515090108070302031006032408010506030c19090522060209150703020a030f02010e16031403070c0315110316030605040603020f1207050604090903080a06181a0d05 75
    0xa40203130008510306045140d41018004a00442da40380140014540c03501c1c0d84115810700d0f45101c0c1c0c003c440550040c900c8607105d54056019207415541c040c0f007440350075102c00075403814449008450020300b401584042c40c28a10314007a1130002c0c00342d6540b00d040e050b148080c03c1d14181e500401c1d407080c1401607544001c50100003c9811509100b80c842c4010300030900040d400003102c00b60340c1d405040c40d400c0c8245001c0224094400140c1260445c0148440e03070102c035000d1140a81900e100e0b004120b401c1c640d04080035030b00d01420501078810f19200303c0400c042070102c070400c0c502044010010690030f4403007141c42c0c1264010703103001d0079100c8a80c0e500000250b061080b078010f0302003220140311451540d00015032001962001c2482050341406440341c00508200c0f20f80103060140c5450303203440d03850502d14020031024030181c01040e2400d0000e0319104d440d1288005440e10041c29482e80480025580000e0007100000f1203030001c18074061307010b0742c0d402c0000074040b4450401491403610b024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 827122167 1250 827120917 827120927
    0x4060b0a033837030c05060316110a17030402040b09060105071b080601081f02030c0304060f0e1204030c0e010e040213110d020c1920040605150901 65
    0x8005070585062210304030102c040481d40398034400200c81810100240d40c400c1c0d80007094801e800042100703110318800032801a00c400320112802101c001d0461681c40c0d081c4a41c503c0200c030aa0911410140b0f074100c0b45000da0001c0f4200c08605049a580d500b01d5135038150394241c00031510005400c040708000440c60180102c80428100b41c030040f11504102d800038050b401404002803295494241c200000b08600c06090000d01c6060100d9403a565a80030031520f0344500f9200d140c4e522150346031485101301c50b0088a00820102a00a24695450b29003200801000c502c0030b4089482d00003405610408010880e0f141820b48000c513529440c500d0000c00410040c0e008940c1c903507101004000541183c0411070740940c0507103020b1a8006c0032075940004011040c110040d03098046158440000154003614013050201d084418482d403c2130045492003a9010040c48040410b20340151030905004240c58010042c20103d078564035075000801d44080310070418182c000c0401c85030410342e888 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 827123417 1250 827122167 827122211
    0x40807122109050c04020912010903030903081609060806031518070503070803120606070f0809010e0108271029220b01090306092a0b120604060b0a03 66
    0x400e01005158001da82e0651a22040113110744940e1380800c60541984500184410105c00b0600804c06805146800780040408800039000036400c1400681001600c00606c651807850b0b0311540e03c61498440300329244ca4004200c150140511814090341280708103442e409262302d402003003504002c6030505807901845070700191003075106003010800030b030010049404401155003444015598140800c0740c511034090007d1003105c01c004040288070030040a010014030903a038041101342c07080e0044501c0c10050f108020340180302044100c110b5111121407002240c45010384950134101c8800d00103c0d503c104088031400326081040a60460002070042803080446680001c030707280701c100001c10300d0030040c5080705503070700e61503500d160b0b000b8043c04008543c13204040c4a4030900b45055681c10b00140405200c0c5080c1d60b02c580d895880e110201406d5071010800c2d0f50804010f0310034809078440150080b50419034414000c521008440010200c0c010140c0700440e0f540500d02c403451114a034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 827124667 1250 827123417 827123477
    0x16030506062706060c060a061e050907030b040b0a03030e090702030c1009111c0b01080105010503100b040b03070602060709060206070c060209032b090509040309050904080712 77
    0x9020030b224084104001004268140380a2040c107980d07003008940d0b20f00c540f02d6600b91a102d000d080100c00d04994000304107407200e08070f2103000c10824447d01604a1030714001c0c15400340f100c2c400940f07032511030b45c040c0e40340c0e50006002040c0d06c150b00e008168500165007050340001c00c007489001c103609200c80c4568002c01d03d8801540b03040303000d0712450788501ba01c82e11b030102282c45042610900010500c400c00c25100200900d0f000d03102c1c421140024020007508a50a11420000040c0340b18180300300da04a5102170050020384245034a0300d07005081180845500503520103201e5900c0e1010040c180140015800800c0c26007000302d400b8041d58010340c00f0740115400a410019950351201900103000c0d4041e0026032a4032208001071300700711540125201002c45c00f040120000c07100144c01d0542d02c05611800748441d190820b021350024111006008100314403c104000c1c10003080040d4000d010b0405607041501a83d11101c01048032183c00c0001544c91100070360103030441041c032102a007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 827125917 1250 827124667 827124679
    0x11011104031713030816030215100519120b060a12030207090504060b030619060807140603070507080d0204030309120b18030433090e24031603050606 66
    0x46541e0b03030b01019a440b004080072840c070115000041d03001940c00d03540550b07808400309444a5980800003004e00c004942030f00188a010a0041c0d80e41110b44035900509420800b40c0009003010309010212030301661020203500001e1000400318482d500c1c542010344501c16110003400c00d0020001c00740850303004401d868207112104400290002a8581115100080412240e6a40c2007c500400c956100c140e0580140c0007082840c2c00101c1d0340341e105103a146010028141c60b050f02660700c21703190140f1900d031442c40504581e2482c140c4003940d0300045134a80350789400380550f1081095040000311500d46500445d00340201b40e00044100f019280300603c04411100d540c0b1683c03500303040a07180408080b2201c02100c4801c0301401220702508500d04100003c0b1000d0a021980c160070580701211040b040c030900458910330b50809049402c51715402600f80ca4141080c1514400c1c01c404d502c00581e90050006291410711004480700f444000c2e81d51020300c6c60a04a0038200014982d600c220 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 827127167 1250 827125917 827125919
    0x6051006090513020712020601031b0f090b0d020d06020408211803011b08150a060c03031512121e051b07051809010f090f02092511011104 61
    0x5a0040041c0700716001124681c60300322280440c10003d11500e03002030001c4514940300042c041e00018182e040341c0c40380040050720407044c0e18188200c4581d009105040b92010f03410006030742e0a40002d0791fa4000101280c1440795290700185140b9061442281c0740c0390046010040d41d0000d002e08c0d900b2002c036041c008aa100c0041e003a0f11a032141d681441208a44540008010b40b002d40c401e00f070324000c008104502c244210380250803900e04846d400840b00c180803480c006e5042c00c1c1055000c40c2d410303807188a004001641e055016020f40075035800140b05d0301000041c1980800c070040422401000540e081483c0300350010290111705801800403a801840e1650841c1d0040464031031803000e405015960104202842c207080c0d09030700440e84041c0c00c000041d81207060040c514060340d80c101c000c0100749a224082001c0d50300240b409441c0740c1c6800f51a4001d81004a40a507101c1c0f52544009144520003c41100603c0c10300301410000b203198002000e031410920680702410092681a030401d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 827128417 1250 827127167 827127179
    0x1503020105120405011b12050105030a1e0302011512020f0103140a09030c05030c06070801120b070f0c12090f0b1e07290f06010f0f081807080703060510 67
    0x107125007441070695042020000c3e003402420f51200580f54014441241d80107405e410090084140103648038009242000004a40c070300021000d000d1640a0752076201e2005c4901501c100c440c0c00c440c1a010342d52240c9a0011290409c1e502e00c0c050010fa21411660480500620400245609089040c94a0300070100c6400c0704521102c0e0340603501d80d40c041661103003407034219010000703110028418800403403141442100420060300c40d0041e5500c5204c00e80c2d03202214400c03814024400341600a40b0310209039120f104503128040c002690801403031145440c0c5c0d40d888280406040b520010303000b0f203000c1c00703a001d034402101e004200c2c0802c00e40c00c0a004564035612103010340d413085074081e07002034000200b210340b092030052031b10079400c45090040d0307100d4076421036103007159480501086117000030304940c05910910032341d00443d603c1d0480400c6100707058030002e40c003a10300b209200b182000f5203980030082000c140948958805802c0041c03551030400141e540251000020040481c018019 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 827129667 1250 827128417 827128427
    0x120611090d020f190e220b0f04060b1315061404052403250c05030d1d010903020f0f030910080705040905010801021206031902060c100204170115030201 67
    0x446901166011040441c0000041e0361011039401044684c1d148000080d00c4d101d0a5901c6200d651700300180707646100c4000c4d0b56010070120b030000070003a07410180854401d480c601422988284609070000d160500080011000d07440c107046215116201d20020300b442c20340174100002040b103030814111a0410480c200f1041c0030f58050207002d10511b07040403520380381d0071344418000e50351000c0c1300342c1d6814903038560380042c10180c100c0200e0080b03211041c0174961007400d56500c03990700f00c0b018605043d5064094800ba10b1001d204c01c0c0142c03103860051075075080031711a11440c64401d030010b19081703c0e0b120b00c450034124954030090070340c0c0040c00300180d561030f46881c881401c9010320f0300c7c110f1030307070b0300c00054425000d035400280600d40703020000700b108d07041540205104844c119145209070f40d030204166440416401003100601800055001400c03e48058035604074864181c41c008d90204080204a03046a4000d031100c41c1c42d5480c1995a220a10404c03468403a00520413820604540010341 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 827130917 1250 827129667 827129689
    0x41b090e0106171f020904020a02030d15050f060307020c040e0a0b060d0c060f0c0c0b090112060333020a02070e13052127011d0d12020a060612061109 66
    0x3030031380300c01011050f01292035411940a000028011510b40000300c500950b607801c004041c401091074a112740084113054848002164030050000c503e071101c1205000d0150070141042056105190242a066449000b00d07604240c0840081111440e42d0405046c40e42c0040c0c8501d00034004290355a000c0782002d04c10305c09403501420527000c9845021011103c0c400742000240014003202404120200d105005214004090382c401c0d0110004421920481d0207601c00100007090002c603008000003003c1000202c1d01056403c4118188040000d800b40d031300001c2d0b03650050308504401c0c0142941621090342215218441203804002c60307407542d590f414007909598000642030404050312020404580c08503500d4100803440020200d48500d05240e0301c4d400e5400320302d05202c00740d0341c54003c50483e02c0c050401064080010501c3d121650541c1c82d10011070118080c64601e54041850740c015032000385404c40762a6481e2155017042d00455407007201009080c60100309007000759072101140a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 827132167 1250 827130917 827130943
    0x90f03050a02280b01050915102601030203010e0a080d090206090d110a06111b120a030c110603151513121704030c0e041b090e010617 59
    0x955210407441c01a45414041010380603542c180b4000712100c0c0002c2c0e5101a0080e100344034030443c50340c81b00c04102134804221918030140f030a6010305096850301d50f5210070020350714180380c40041101c07401a000609034512000341400d031034004104500b401d108a08011868902520100c00c2582c1c609a070b5208440144059030307201d9000009555804044400c40c0d8402402c1d480d004049181c15030008180610651240d90b580c580010190700610403041c0520300345014050354024803440c3c070110036550000e5900030524060384a41030303100b0450032001c1340c047d403039881e010000c0380340c2021180750191141e4003c080030700601c10b207400000c1540b0a030210407140c002604100c082e0040f020b00072260b03c0f04494051000c001048100c08000b540b12500449000c3d1500e41811000940c0b0310441c03100030601d0701c104400b00a84002c80300800d03081031048403138685030036000d00c8001c5a0030f0070f03401145507940d5900080c0c124a90034401c03074008084005110410085194119403106039481201c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 827133417 1250 827132167 827132177
    0x60301050f04121202031e011a0f0c01150803130b040302060906031e16080108072d030807030305060f0405060105040b0f070f0302030c120906091011070e19090f03 72
    0x4883c2d025846210300c0901e00101103444c0c2c648640c0c41000041a003c034500300300820300006c01c016071214003440341d20700c20a044504e0a20a1240c01c000c2c1d13400011103141c1c9540e02d009041001c00c0c01d04a02c0700400a8070002c60b2605118010603601d4041580b00a0260790b0030842040161901c0d0284d480805080329000d880b59034428845005e40380e065081641d560351203003044190820a00403146181c01d80d170358041580c2c2c85161081e030f135822600a60054072180080c101d030310195500c040c2c2c2c6802141120310300c029030300da441403042d070802502280800e44400c2001000d0a1245941c1264002140e00b4081801e00c2070001c4d00c5032045015010800c0c01c0050383d880b004801001701d61601da07008891101c4c02e01103007030094494214180200150046680141002540700e00342d90300300000901c0c170b500c1c090428042000307030801c8100e10405e200b4032a1002040302c10030b0140720b0046c2207070700e0071004501e4800070200c00a44040304001c050340c5401200320104d185500441500c80c0d0505207 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 827134667 1250 827133417 827133443
    0xc031e0e06031e04080c24040b1e0106091701140f06040e070308040905060d03080106082511010b03030403030c060e070b0c0f060a1e200f070506060301050f04 70
    0x74200d14a01031125103c0f006150804d000c104003072107008040c0a9400c00030341e80440110002a1041006080031842c00303444000842c010404034843e20b134100740710403d1040090b8010007039000c043c200364044000f04401c05410055195802c01044840030071100030051a000341030f8440800c400a0300010030f68004400150598907035510000e2081640703022240c0d090766a20346500103a100e40128880030382032201080c2c0b03505002d8461040c071649a1a100d415a007018022508603400a0070354451100e00302500d800d5004c0b13100c0d68030214006540d2140c0a03101c0004c418252251340c04c0c40741c000c2e40100001c0003c81e60201140440d40d610860100f002e800b0191401c2c50003803d900505080d900002d194a038581c0002404d03c10b41d40300c10292402a035824035248125418a04d44441c400c40c080451f0b81074228550020841c0d64644140c50400342c60800c8000041d00b0014100d221990000b0302c950034400d0030001507074003241c102e00078031180c540380403200c51460740a4002086503440002e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 827135917 1250 827134667 827134681
    0x24011410120b04060b07150b101209210f080705041a0d02030f0a06050d0809010806180702103b0307050316060b10020316050a0209070c031e0e0603 65
    0x40c82542c00a01c103000d15604c4c1c0821614a80c407559049403044070015020b03660010074002c0034001d21000f010305103200d10080c42510004058140030207945da5a803400400259504100002044122100540328040560180a03080003209000520140d6400c020206901c041194180c070072445103855450100c505418541c0207992100021034000300c20400c0241c0c0f600012031240c0c020309014411642e441d810f0140c21042040060540e0304100103402d015401021020b0700018098000200d00c0401359451204010680d035a00040c0c03c0000200540032290003400d5a4170200301c0075072101c40640701101c0c0101c1c2c60301500c0070349440d00d10700844403410900540e40419085015030f136503401201c503581c0c0f401100220403614180380c103100c100741d4107241d000d450b80139802d03800861504084a00511000c6841e81044500780b040d440b02400680f508401180201c0064840003075948a51034003910f140d000040d05920008045034120070b0561290f405403000e2015940e49a403515100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 827137167 1250 827135917 827135921
    0x903101505040c140c060601180501021209010c0b040b06030c19061103071b061b020f0f04150803070606060804030e0d1401020307020a381005032401141012 69
    0x981c8130105440130a01544c101c0011841c1031207040248e88440c990600d100fa1240342c6a243c3c0600c50050740718480d210003403907046000300080501410504440d140b1581c0344180001c0440741254004900e070240703c07543c20f0402c02900074060403100c43c800046081e5028003902a1481042c00b0803103060100340b04c4140a0045500c10f0703400c0810305140c907241c0036031505422030b6442114001410304031035040900d03885000303100d01c95004010340b040001c054204490a0240d0112550060703403070424801020a01000d100200641c902458941039030741002401c8480c66404502407161402c104030000c0e9100c5807460f41a08102c03030a91213078596003000c3c0021741d200e509202c499071001060028450700041ca624096204161703444140d60301b81c05801100c0f50054103c0190700c5801d0704591411b40016046a0241100981d14070780d56807440083c0c034104260680003040c0c040d0301c45941c0b040c007041c250030340541900c0311240307001d68110340403a014101445003081004141c400c83c840c00480c507 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 827138417 1250 827137167 827137187
    0xa0204050c12151026090c04060303030605120a05070b07050309041107060509010b0607080721050304140a03052208060702010c080604050403050a051608030c0903101505040c 77
    0x44031100020f443c04804200b103507540f1004a500c1640c94243c0c05060502c41c800e080030112951142c000d60440c00c0107441151a4050101c1c521801840c010b41b0098680e031042400442c00f0f030f50040740041c681801c1c411004a079088200240c0c02c90329030381000c5940011941c0449807042d44540d9607135401d0810900318090302c0c84175940f190401c030140010400c0c00d40a4005180903c004000301e441d10700c0714600300c42909805d550001f2080c041500800e0701500a415403c0c011035101101c0d0f00310352582c8281c010307450401d00220720084203020078446066400c100c5c00402100418101181d074502415034042c034000c440ea222004181041da9840c00990b180c001d111440881c0c586081684001e07000e010f00135501c030000340c18200083c03924502805113078015501501c8a070301e07106030720000f194642e20000d030600300c0c0000f10741c09500140d092002544941460300310300352248551b004260600c032007072000310029400c100071040019801c079080d400310754040b240083c0d95214803e01361004298 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 827139667 1250 827138417 827138437
    0x38160204140a0c032702040e0304090603170a02120c0319030f0c0206010b160c12030f03050f040b010e0a090807290106020703111c0c0602010c030b030a0204050c 71
    0x1064070620112210030541405040d0300c01c4140065003203941e0403402c95400c401200c001c030356030314002d003200c0600c000300616490014001040c41c001c003030b150a145a20551141c940c0030742c3d880c0104280001e50007840d802460000c2c405107000d8107140000c2d039801d03211948030200040000c014000760003c104981c0f09111040721171022011192019006090040c15001c06509000d08012418800320701d00d0305a40064400f18202040038111040c0282441c4080351604158500419005103803032540481500c01e41d81c49440310b454074401426940c000c1c05200f0f0341c0c00241c0030b12001420020f600c50541d41402000401583d030801d689014066100010b000c9000c001404400c1c8480e51b0561114481c4509205460403543d01a25011030402d10450f801a04140303c280300040748880c6801c5c0d40d03c8010700c0c3d10380b11100c2c0690141c8503804100d040300c90f2070503040304001d01a0203001e038420300d04150500700b00850740310002c20b4032001c281030024400c0d95968002105080711038180c45607019 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 827140917 1250 827139667 827139671
    0x7080406120b180718060801090b01020102040e0c1908090309280605120601050a0516020102010b1003020a090f0b0909042310050105030a021f1101051038160204 71
    0xa9070164084a04001c0e00e941d00000d40112a10061821701100082118440d50340c00d0b900360301c0c2040110003408031120700d5045540030000005e259017000f0046001d03040c66070000d669440f0904854160048511030041486842c00c10401c3e03000c0007000741c500c0f03040181c4150009564400c5e50100760301e10b4284401e6030720104d02c0017150559000010706106038502d171030050a071303c0320030041d103003406450814000150304101000611005c0031100b509284103000100e092100d40c80029622a240c070b00f2500025804100211030070340c48009403009080c0e51440e000c6060600105036007034810711781d441c2e010351a8440440d0810404070300780d0840700013401c120b0b40d80d21a903944803912a042c00300b01a012600305800450940380c0820308035045680201005000102e40c0a28120042d544512005001e9030301c00c1c01000200030b014030f070b1154940002c1004468140406200a001504400501c0e40c0340c00c4d403903044c4a110f8500744c140701d00041030065110446420000141906c1150094100b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 827142167 1250 827140917 827140939
    0xb03042321070f050f0127020d17120a020307021b3a110108010b030f0417090d0302010609060e06091f180207150509101e051501020d020307080406120b 67
    0x460190300107c103191140c9400d15203940803d24010401061110107036100110090f020006180f0724507030303c0e403804660440d60500e5001521403140030000c41d03118009030b400004105040c5e41c10b00c0072006445030076003054035507180940821001100801c1e50040d005d403800107403203c02507442c0c518034004411540003103190f82e0751820300f54507080100c0460204010350300200382d80c0c02480c240c912540c0d41b13503107000090351561511060309202d00108818000104081540d41d1614003240c400140a500042901803400448038100c0303a55034030406988070440c060100c3c0780c0d24440856004850a034044070720303000c08940030302c0304456544644484001030910050448454000c1c120040c043d904c0c01e1011030b0381c2e61300c040a0328011200310000380c2040c0d1687c004800c0e1343c0e1100c130301d101214075a092008100300001088483c16601c20040d010480b90302030241da0b040095041141140c03014500b083e0b4256640c0d0068016030017400c0902104000b8491803101c10381c04800c00354002445e00c41c0704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 827143417 1250 827142167 827142193
    0xf0f0612060c0403123609050f01080c010e030c04021b03030a1b080402063a0207060b040e03030f0601020c10030c030506190315060b03042321070f05 66
    0x81d4000e2004485408010080a1409000c0c01414220080d080180c886d41d03001314200d048648038228a100325034800388070220f80c4920340c0c4120361180d00d0b1030b80109495410225214905000c2e80109810400c0711800740c400b42d1400315030000d00000560f400340e2591000a140b40f08001c600c6443c080a01c0040100044c210860f0004078100d00701940c0e89440d103c0b52078040314400740c11200607421240c100310340c5206580b41c8208171a10500c881d072504a29564103110300c02442451102d440c0140c0100745002070001d948544810318000b10b0702009410182c031071640d181e000080140b8000141140003a4159009101500350034800030b0000c12740c02a402c0000d401000400ca6100c0008c0c5004005161810a01d44050007800d00706803845c441c46c51590b644660300261542216503a44807000040c1c098411009980940c1c8240000c4100c40b10750060481c006011140c0bc0c1180e5102040a03480b1031030114440511200c41c40c000c0d0740d80d9030141420a0303840b2034100010304500c1040c034a00b00c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 827144667 1250 827143417 827143441
    0xc21040b1605010e06190c090b07170c01090618020901032d0b071b08030c0c0c0d060501031707020a03030e01030e15070f11030a08070215091b0303030f0f061206 71
    0xc00c40c0881c0d0006c40404122080c40c0444070b4000c07542c00030503544c0b00d0a02c000b02c400e9000e004a1440b07050140d0810000203401d86058121540c0041143e44a88002c400c01155024900e5615414038070300342e415411f0b03000161100070611001c0c00c6041042d80c21044030325641806c00f422000460050084038061914045d03141003218940c0000751820041c2204083c0c1c82c0300d0385490303504481c002c0c0c15900e94001000e0075070b22244090202d0b10840744141819141c8032007000b607450051000145d40c0d855410440d0047e581c10341f1070300030305100b0002000107940c1c110750740d82038039018a08104002c1034080142c1c000c0c14a1004c19080d441032074842c494141500704100c0c8640115520758180841440d0103561100e95004000c500c0e4000303006004c1c102d03100d00d41c09988000e0070300c126405543c2c91203880351005010703600b041c034580051000703440340c0030340a2079044080c41c19001545189403124440141c01d801038010441401600e0103d030095a03400081034540481c441030380c801c0c1c1081510b0000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 827145917 1250 827144667 827144671
    0x102030712060512100b0d050f2107030903030509041416030b1504030b041b0b090405100503060a0b01050f1c0e0309090721060b0c21040b1605010e06 66
    0x1e000782401800704040c10070340c096a01004c0c02400038035100619800c07841c054662813103410780000003003507a107011510400580c20741e00030900141000c055854291503800c07100007007150405008000d50b8000a0b404111001140d40500e000b6440d81044070001e80903203100305500d9088052041071206100d02480b602c0d00284031a1401c10148a600c8140030340c060022080340c60030352041c0300410100c0c9048140c1544903109049540001d0b04540911040c00410b40044580800c00300c0d0380f003040d0500b44a00c9030018440c40d0400050340c9401c1c0000e658240040c000c09000b0f44a80750049280d0207041514038551946c043e9544070401d60681035040c560f59005100500d040003034a009608000c401c54140380e001a01460703450b6a8010147c030030b142c0190707506103800001d10801644010900c20180a0081202199600c080c4120750a18111214640d0451902d0721200d541990018504880440b2848090117440e100f159010b14407034044907001501035402c2004006882c5404101c4074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 827147167 1250 827145917 827145947
    0xa082b0b040f0c1d0f0409050f0705030304050627150901090e370552050c030a02030301030308090d0c060e0c1e10022d0a0501020307 59
    0x440c82d48048201c0a4503018000c120220f03000d4841c000320140320708801c1c0301090010708015503003112800070400b142e000c04400da429800c007000d11000c40d6001d1000318010701e01240103504041c00d200c0003417118440e240310041c0344447c0d91943c08403250085c0d40d40c1c002c00740082c1003103814102000d9401d265402010401c2c00103004400220f00300e0408941c43d4060901072551aa1505400045034008400030345601c810140d003084819010b407103805401c3c41254254580c09a11004a40b100c50b8a5951001c14003100e11102d41d000500111420b50680d4a8411002d00c0301c0f12391034130050300c0b1842103c150400f203010004103012400e80010042d0b040364400d6503090a0b50755200d6115403501011502000019003e140083c0410403d4100d19401100c1c4030a586004142c10001035801c0080c0741c10000c1e000c501c0901c061a0f150070b13000484240141c5c000780c5013a441d8003000d658041840119081400e02d10404c60307203801d004001190103198040021941c9080c21440500400e1014001c1d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 827148417 1250 827147167 827147171
    0x28020f0316060e061c0509030d060b07060f020c0c01032d06050a1725080d0903110d0317040305040b04090911010f020d120e1005090d02060601020a082b0b04 69
    0x701a8509288003205c019484442e5410b0080c0e2100b00302d0005480043d0800e040d5100c28000c0200c82045481a40c00808414250a954450601e01803040da1603040282ca402c0d0700c14032a4004640010540e0303c0903c2e001d1030b000074a492003220031420103005000d400301d021956001c92811118507840681981e90465500600701d03a200610b1480d402c4108144501360440390090452031440390500160420200c001104907854181c2180b0306405c0b281c4100000e00c50310001c1007400329609009202e00f000361001c80b6002e02588000d03001110003008900c0007944400040c1c1410b1140003a0390152200349251035a4550380c0e5001406010148420346641c80c1c49414044598081c0c51041310204041d00505218509403600703a940c480c0525600c480300c1d807594148200b188040c0314a10003244411000246401e25001070f51030829215550020742d80040240191683c000420201d841e600803105980c9032810100c1070881c040a131091800308104c00211a41c02c4160307001141c02010070703101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 827149667 1250 827148417 827148437
    0x303041503141f09020a0e1e010909050c0708070f0b07020d170f0601050c1615030f02070809100203120c0c2b0f020a02030d05031828020f031606 64
    0x40a6400d90060341c80040c0c00c01003032030402100100350054041e40e001b81c00c084010144440208402003c0342440101024006044090701d43e000b03604039028194510042000317140800225005114408010300032030400300da0101042016034000c0700c3d065024241c0c19950900382800b80d901c0c4050416003011035070309000760800700e5051481d14460b4508040514154840c00e005641581c032060302c002c13441c010b0076070a500c03900340218580024801d841503654a95100400101240d102030b04030b501d1140104002c2012a08103420b9880740c14089640d00d030080038a500c02da25622a400758034507103200100802080c0090400070745119076a10050f1102c0601c03203504186c601c0c00c4400b0707282090421040300e11070244076441c00b543d800709134011240211004c3c0c00103450030380301541100016200008000305020500c0c00e00a08190501c0149421400c041e0000800e0110600302651403162103c45019541d0b54990b580d070420010341510000c0c825214502d000008a02400f0081090303890 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 827150917 1250 827149667 827149681
    0x150106050c07051c0f230f1c09080604030c1a040203070605030703090c0806150303070803040204051b0c16050d170c1f02071b061706030304150314 65
    0x2007110304035405480501099030518003004a04c0d2294034014100b09200e5807480000350154540d180001d0103140d510200842241c54120100c90140340382074160850b1300d13006550701d00010410690613200407450415407c154040311030426942c0000210321640080c40141504014000201400340c041800351000000e8002000c00094030025050b03401a0010821103200c5c2c3c01550b00b2441d00d00e030200b9207140c10346829001d140725410001d0150414420f10646443c0054000c12000c0107901641c244007841c0c46420320f90000820180c010707a298000140340c0a80c030454041c21012520030751f5108d0840c44a003030b954065030081039040c2d40c0b10340c4000c5a170b490a14050645076034416081030035001c0c980300011440e08045000b0a01e4451900c0280304122810203080e40d10104a0005841d00c80608020008100d4a4912400421500c0003402641c2c2d03c00b2500c00000080d500090300c5840d004081b910318403c6a010700e03101642c04402c00060303541504680028242500c0e104856183c440d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 827152167 1250 827150917 827150927
    0x100b03010e121815030403030504080c0a0614010f080304090513021302070b06030f0d030921120c0f09060f020f0105010609050a2c1e011d0a060503101503080c150106 73
    0x3010444130707403000d20000b00081c1c46600003980c81031099100d40c0c02c1c0075a0803040341c46d000d804d0404649032500c0d07a120b20407418401d10f0741401406034098103100949032180a0f0b84038811405081c10064443c0d0000d820800380b0f0710082030346075004d810100400d550310f0482e0000c4d04032000403150031141c400071503120300d000110340900c009120060090414640c4007074008084404089810003240303100f000d1a10680320403541030904a49486610310505200b48040395032030f0a11b0b000f0b02649818202d80d942d4008409402e03070700f1900b0000080c004a6a060303103085010002203900398281000841c0c16a800703c0e0040403070b20242c031001b494a803148015621108030700c3c440700749032103201d0084550600c0b82158070307000740019946c10a090340a83c040300320581309800074144d020701801154100c001901000703a000d150381c0c10400c61a4100070010f51510290f4001d0035200c0d4807800c4992041c1c5954981c02e0003182e10001c55030b82d90380859401501d814090640e801c00180c40700000440034020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 827153417 1250 827152167 827152189
    0x702210d1e031e09020a080a0803090f0105040c2c0903040f060207180b0d05060f060109150c021504090513030f05030415020304110d14010513020102100b03010e1218 73
    0x75030920500a800c4803102c02013200d100140e0748a00110400120100107218a0a4084c0a50912607030381c03030400c0120786003811040b40b255181e0301d48010480800d140d40c400401307690014480030b000b00515003d0158815501c100c1d110551115414000c40b61310020082040340d2100003102c00495030740c0c1050b40ca9400c14403480702c400880d8080d50002905550080e0703400030000b00b66858104550b00c50a203040000c4600b80e0644200d071061280301e6800c01202002895459500083c40c05000d82c010003076941c1840013802050074444c070900d40c00c04001500c0241c00d01c988108034a20300004412450121003c054011400c01d0441c42c200c2e921a8044030312494014080702c0b1824000c41c01840291b10040c0280e41507c4d001c2411503156803503e000a034220700070cc6c26400080701048045003140c401502c0300074030b0f011010100c00180d80109095124850382c00c000101d10400f440400d002d4000404509294010001054500880103010300b140d15001c256246c051400c641c1885005c00c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 827154667 1250 827153417 827153441
    0x8180909010912030e120c3f03011401120f09110a090c39080903011118190f03080304030e151204030c1403210c0702210d1e03 56
    0x112901e64298440c00000810501301d1303203802c07a500403034140e403102602d08050064100ca000e050311304900c54142304c00c1d921201508011024a035516007203000400a41000840381408030361950324600d520603a008017540c01c10000240140c211074a00700c8807008049a4880c4203d0b00040d000c00c84103003a00c900b400070882a220305000d506003400045c0c089000165412151204404150070640e1101002102e10f11031100280c8940542080500f91a41607000044818081c0144416581c400032481c1c100704081d030300300030800c051401d80115a01d4035000380b03110004c400000000c000c9208003c42c0710b54000d81d41d071b0740001c482e0010403802880400392540b082d4002e000c040101040c0b01071017030700984241030103046049641d543c03c42e610841d04100300540c0000c0b130601813a006000740101c1030707900cc43c125540e03440c01c10600c00703041c055031201a005100d2410000c000103014441000740e924242c08642042c240e221004129807401080324000664001c5820003160280c010441c42d0b0403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 827155917 1250 827154667 827154673
    0x1b04030605040359131e02040303030b0f01080c0c030403060911030609010510051002101a10140403110a1d010302040c0c0c27090c2c0408180909010912030e 69
    0x280a0042280d108585e0079001204c0341c2e20801c4104448001c107804514565041015032a1480c50034041c085442c941d01740d078098142c80d1840d4600e80c3e406241103510154584103a5181c00e802c0114624602a0340c10042074213103090844c0051003800c202d80710302054120129041c1e0717500c841c03007982607030800c1d2062604801200c1050000e468407010780723458401c5900c100c0e8103014a6086084c141e40824202080001c0002600000c50802003111039601c03041d400c1040504030134200c85292403080b44030182c549003000812a88964400e9143c0000380821408003040c0e501b0b500810701d0741c000a1004074869849c001c80700f00050300400341c00b40401d8003c16110b610525255a248440c0880381c10503012040070a00b1108003421846211402401800720001075410003004901d6403210300e04070709956611042d4030207130450780021a84e0196114902a80302d0311829402c1990b0b0400f00107035580a0100c0040115507101544111905401501000c140e003c8100040d000c031825020f0000c1030750 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 827157167 1250 827155917 827156087
    0x11205120901030207051f0c09050306060d0602090310051009061d28060e0603060907060507060b0607060c020106050f06070303200a090e1b040306050403 68
    0xd59020203001c030007030181000b51070203503e5600c09091145424030b2601c0000b503907c02644036207903446055000380c960700300003440c2030511000a40c0c50301d000b441c5501c0348800d1403c02c4200b203100d4040d46c0c1c2e1342c00041c0480c1e0a1892080c602005414201d07407203500c014409100060070b46082c041c11007100c4025190407a000500e030700f15280c00100400c00c45080c500400c840d0384004030680140806040c0c0380001600c203081c0301c902c00c10500d024064510a91200060080080e008180d50088824904003903588500501c2d0010140103100c1146070b0000e00800d40c5414407540d90410200f448596008001040c4c840c000c000000802510242d0007000502050000034002c0e44000386261135441d80c1c4c00c1310407840e01c0310030b442d610042d0324400060380ea007001c20001c50083d40300764200d01c0503180c414581c520300004860301c2c0190700c4090715194685022405040c0521042d0344240d03030812807200c0e25040008160130301101d060b84150151460b4401c0c980703210792014404400c007002220b0550f09 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 827158273 1106 827157167 827157193
    0x18060e01051303080f120f010303021905070f0308301504090203011a09070c03120c1e030e07090207020306070507140d0801030308060402030f0f0a140a0501030b011205 74
    0x415031f01006100094010032001c035004161070b091400c6e5031241c2011494200d05a11448248243c02004800e01108800500d0b650541000311003c24451402c01500444803c40105010b103000000ca82c0c158500d1030021004c120040c404035640c1019000682151924040c0d1042040782c05903014082c01c260178140c0c0d11200e981003a202a0409450281200a80300000ca12a0f80e807501e004119501036019200c0c2e00181002c548001206080c1c050000c05001e541d049041c0b16106000902a44c540201c64030164081c3c060002030310b9296050f00e0981203040c0c00c44554010b8407000360010300401804410700010750324940c440d495800d007d450f0303580280c0bc0e5409240100200109588444404d075001540b0b268503500075690030807144000c0501c0c2c20681c01b600c001100380f107040c0c0c003250003da045c0e0b400b42c6050f1405990720840c039008040d161400400c030741c001203004810 = true := by decide +kernel

theorem cover : BRFrame.Cov 826978417 827158273 := by
  have h0 := BRFrame.cov_init 826978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 826978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 826978417 ≤ n) (h2 : n < 827158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
