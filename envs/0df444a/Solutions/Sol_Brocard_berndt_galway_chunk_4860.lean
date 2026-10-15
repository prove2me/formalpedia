-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4860
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:58:18.458985+00:00
-- url     : https://prove2.me/submissions/be765ea4-ed51-4dff-bbca-b693a6e4bea1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 873920863 ≤ n < 874100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 873922113 1250 873920863 873920891
    0xb03010f0b04030f08090a080105070207301203390e0f190b040e010821090907120519060603110d05040f0605041b050607151814060901 60
    0x320120b82e0010401d03880444c071a5103080d62940540d40c09540000240c0021400700400e1040500a030341c1a001060001e01d440a0056080402d481e000e42c0e5465089440a14400b40403e140c4419400f41850300c850340784490540040401490765400d40c406408240c000720300507245003180c00b170407040000e0908208241110104010010a078004074140d0011110b0304000c046003208030080b0741003503000c0d5202c0c038001446070400c1c3c2c04149503840e040c00411003c08148140d404e100c02c1420305056912100745004124071420305082e0098441c2c00c0095505032141c0540d50707200240c10000d10090600d2607218400490f9000b0840c886441e1100004a003400b902c00e1110300014121980d00700364840f030a03440113040c01841601c95264010b00d50000522510401d4410780c443c01042c0c0000c6000000720454280580155020305010445200030031604030300100900c6c10b1410114180041b01c180001c0706003c40c00c000c2100c0e03441c4925072501540403a1444c4500e040e40000c0084103104465 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 873923363 1250 873922113 873922117
    0xe0103140f0706030b130207080712080717190509010c0816120f021603020106030c120206031b040801060b090f0108011a070813140112020408070b03060301060b040b03010f0b 77
    0x200c14107940c803281d01040700501a4100d01190840140034001e00074001803d00160f905c803440803112200e00080c071303400b001a01c00ba003d52000c0305243c440e00b1480c082d003010f0300030103504400c0103110248500007211444101c901c80d0b10007a884505002d20700b0303c8910239000c1e020482c200c8001c44e5204000072072003c01c070600b5001d144c1080d612404404a05080c40d03004110010703502c02e09035000c02540448092420600e40803030320035400003e586207113082c10032402d07020340c10466099180f565440056035510007529004000a0700d1100c1c44401403028410a00c600d81c003905681d400c2810001e50001407002a040802c400e550641c4810000001180c0e960002d00030f007203d840b202c2070b00366562004000580b03400c900c030b80081454a41c441e0700c80310b4800b0541e80200410000d1758a204400c3d41d11030026105641c21460030350a141c01c1007a901d0300c0390554052002090030100c00070759103a409400c404000d00c2030402d419a240d490f220745000e658003d000b200840e4008401c006240e000c0c20701 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 873924613 1250 873923363 873923383
    0x204031a0a140c0d02180a0b04080609030a0507030323162a030f0c060204090606201c02030f0c0622020303090607060b040c050a180e041101020f070e010314 69
    0x8245011070045003100250010006c0c04050500341350074035055215104902c010700451001907440300c0c5006102c91070014000c0804015400a105040c1415044000d0b01c01050b0300d4100411003003009190340101500e49522040ca99081c4c000b4468903070741c014002d8138589407036558415440030150308040c0c801c010364071600280c0d0510003c0d802203485510940340340b0b01c1c03501d004401c1c0e2580e5220142a0380150700030072555030b40c55004111054011540c09000103852400d070b51201046140b25455401c01890860845051848446030b54402d200b2a10f204c15580c506c10f480b8002c41d18246d070f40d610220f0711442104e0039104c0c07480740303c10410049468664010001c5160511500074407059402c620340c00c07505640c80b42a80c03074181d5503501440040540d40d43d241c940b28401e14400624100c041e440310641e03024500d0003884488a0166055445138204051f00101461000102e00c2e22410301d10a25883c01a400e0105901c4881e0142d28104d0b40149101410340e5072200d00580c81d007031094 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 873925863 1250 873924613 873924631
    0x9010e1501080105370303050d0605010e130b12060f070f022b030e010e010e0124050409051501030b0603070b120610090f03030305180312010b09040204031a0a14 71
    0xa1482c3c20701140c1c0c0300003120113000d0080046003913011820726150400e1b50000c5022400200b0729601d02906407280324003d180904c1c0070002c001600000c20310740d00c8008500203065441d604600715540f0341c4c1c90f4596119001c40111411440c00107045c02c1c0e0130406868000024107070020f14000e0760710004078111820752104288468000107043c0040b500c83c46400302c2d0134191030701d442d040d06000a12400c8220000140003042e0810890f10540c04c54282d07010810b14503840840761080340b0b06140846007a02c00c00d07600016104c400d8240b2078540003c80081041e40340c0e120000cc000c11914000050040030160100c6855941350302648030300d405106c1d40c80500c0352030a4005410b6103000c0310410442b23002c50810340c900307680f030305a46018640b4a420540c08282c4440900481d18000172606a90052a00c040d40c100003450160502c02a010f124038540140b0209000c1420780e61035040710b0085500c0091b03c460a540d12190011300c00040701e00b010451b25122043e224207210b03130a45481000c0e24 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 873927113 1250 873925863 873925879
    0x30f0b010b0a05030f04030e061c0b0303030c0702012a0f0606050102120723010c050a022a01120b060a0908010b0901060e01141309090c06090f210209010e1501080105 73
    0x4203040c42d88814006c100742e00b0422280c185055584640000b0031100da0301520031001110348040f41d1082e10140e000180c004e81c000c03c01c1100155491b0107454940da424604603414000c503059040081c0d94039a001030032120000403a204000320b2491240d030b180e20a20302448256910801a0380f2171499003c0d100354030f8030800c4100002106c21091010039116604011a11039440e501c035802c40e416050b040020030800039001058580400040c43c14801010310184d80f900328003201155020791260a50510010218545000045400458009101800050311000524002071201031244165a100d51900c12207042a040103101181a20382d1074480d4150b5010003001165490340e1400d080c03862070b605000c04954410144802c100410300d0744008030760f2000905084102c10b00d242c0c860130600054030010000f002c3c001024a080391072903680d004148180948000400d04020002540f1501003c0007107850009102020b0040c600b08112541e5140454011b4450303a10a001d00340d0301c5042 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 873928363 1250 873927113 873927121
    0xa02010c060c1e0503071409060f1b010908070204060e090a0b061305040b100b07120c1a0a0510050402090a0e040305210402091b0a0e0301020c07030f0b010b0a0503 72
    0x8150001d4a860b4201c1c030f00b010107200015402c4100b000720802e001c0000d0b000000b441591076000b20051600482407031400d00d403440080001d94184210940000001c4010407007000c80d0494002c0784565900702d4000b4086c040301c507c0c0c140b4480c0d00c100e108a11407487d00b030340420002c010000d2144101441ca004114000f21515030b0755000100900302e590119a0300c04009800c03005002d010b005500c140c0c00e01444c1d08001d65504030215454103d5106488140b00340408208410303130480c03800d101414000142c10449c1030807603041200f0b941403103404d840001070110b01d241d540d1055100d01103400302004516140d030700b00026442031404c0700d540481c0101c020b0206112800e6056086807181c10040d1910400c00b2007a045007425003849000850340108110650405400a580c000c10750450b4400040648881c080507006000f2504204550005013582c151425811a030150803290f00f00c40345142e81c0e00c0c0010a041c2c0c0301c5800c1751640d01c0440000742a45030754080d980840c442c1d45034103046940d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 873929613 1250 873928363 873928373
    0x9150c1109150d0503090f090601020709150b030c0c0d050a0903080904020d0606020304031a101809050102180406120f080c01020405040f02030f10030c151e050c0601080a02010c 78
    0x20060402c000021200188807038035690407400c5090755106001943e1920110003c10104001e104102801134207000204041d90780e0116250055075942100010b8010003003031621088511a00518042c440c00004d001d121a0320001a0800c4410441240e444440d0800300301c0e042cbc0640882c40c0d02040c840a014800182800084c02038110702500050420780550014000e4804540c4500056080002c051040c01811100c40104c1e030004a020051030820140d071640000580c801e955000080740c400c0c0940b004103420002c01c1681100080d500da009100e003004a000503c8843c9200d50310300000000e41c035090044040000d900141e684103003000d20348030144103601c00c03d07022405540c204000300d900d944500c56647c0d0900d02e1031005880e8a000c80c0400ca4142000c3c0c010446c5140703d074000c01c0000c0c5503807010410f451074014440c0584c40040c0090f180402704034081540d40090111414041c0c0c0d009c00a00503480341e0f00c044601e1640da8420f1251201c007c0d10029000501307420001d0080f0b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 873930863 1250 873929613 873929629
    0xc061023030d050d020c0d0c020306330f0a170c01170708040c1802090a080613080901052b06060f09090228080402091501050313051c09150c11 63
    0x21004c1005458040c02c514102d00b080328603851030340490840724240055040070421180d00240c0b0f014074080009603504101400701c12060200c145450643c1002c907191644d1669014249000e04054001030f00d81c1500e0503001464141c0b003e0601c00e545003000607610640c894600200004000314140e1a445422107400200810a58545503506070003d0600c50342203c1001e1360401503c0181c071000c00404000748030000381c1c8041890340c81481442007154003240c00c1c1050507801004180e440c5281001643c45020f002c0c452421813a06c0c00b038440d842007000b004401d000d140b4035010407449071602c40a03200118030785034441c0024000c10046c803405026500030f2030803040040204003410b511071071290b040c0024030003010010f00c0c100b0903c002c41c1084619a5080a0005007205a45102200080503800300816203001d0364540d41100007805001e02071040035011301d40d1042585940828050989940d610441204080700c0320442d6001e03100308520a9056070000d145400c4001100030000300c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 873932113 1250 873930863 873930877
    0x15030f030905030604120815030c0906120f0f24011518170c0907051c15030b190612020d140106120b0c030601080105150c061023030d05 60
    0x407012904020905a0342081040c1c0f24920401d0520308020113100000c00b0704401806001117131b00707400e800484542e40441c00c2680000180e035101426640d080010704000c0144500064500800440c481c4092000c00c00b11110056107080f981200b520506464080460302c15440f06e0384204001030000103038032011049204400d00c0e010425048110002c0b445004c1c941c4420b505510b01c2c441d42c0e041d1207040c808000000340c1100c041281c4e244c25800940b5074032038003802c2003c1096000c210314805440b40d11041d600f4541031f403456400c5e5100e01e8690040c540030b65281800481341c4101e030603481e580c4d014060540751180848a2010f08030760a0040003000c000e4126800045641c400e01007500910907080148041280d80d10300040c90f0401d400c0500000c0c145512030301d410010422666044130303656046501c251404000b01d0b460034809032140c0540c1c000c3c252280920400c2c0b2034401c2044500d0401d83d0700307041c0c0b4601d4003521171550450758001c2d1200143c06400030054400380d20301400280c904 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 873933363 1250 873932113 873932117
    0x711060f25022d0103090302031812070e010302130221042603271c0507080708120108060f040b07090e04080d110301030507030204021c090b061315030f03 68
    0x44105540020400c903840200b04881400101c18801e000100e0079501800b81000c0c00c01b017080610743c0c0c500940381e2140b601000c1014941089801854441041c0a030b00c6009403410780b90b14a0319850240b0304c51300c007032100342c0c410112100c007199400d05510850358192013a080b007000c018403800c071030041403000600c180e85e0610901400f04100d0525000b10442c0c040004c1455036130f00e03000c050300450803007032080001c0b03c40851000c20195a00060408400b68000c6a6407001d1100c10380212441d1155040042420304082110340030043e081f006000c0305550026801d08580e222441d06940b040221200228014a4070205001c10000042950002c250307140403001e903500c420b000b40300e102041c1c070215805600000d880c24540001d1059a0032242500704035071135549140c0310182c0d201010b00010340301c0c0d130b030000d0b80e804074407480803611402c5400e140041c0121142400d04540c13001d070407540705005201d08030300d02d0201c0903d0f2141010b0003d0696280284034150f4503520708414034100e0840c2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 873934613 1250 873933363 873933427
    0x6160605070309060e01060302040e0109051504080417032107020307030e040b03030a0c1109040210300b030c06160b0603070909050709180f12020109020a0b0711060f 73
    0xf01207000c5010300703262281e904002081c002d207144180404c680441c00100805d0749800000c0e00010310110700c02c178056410910003150f58a4500741a0443d101715800124014403070303c01d040c0041800304c09062480c4100d484a9003100f00d1070300c2c000c00c441080300c034600140c00802035100003a00465504c400860050000103034540481c000c02d10b55484907032210049142c07003000c1c03410095211100f5812420a4031082031a050503404640f4611603401ca00e014400c54000301c140c090742c5c01c403600d8410842a1a50301000003a00380c17803001172149440ca1806405503451810241c28014100c551011055804445030801034171415030303001000c0c0405906008051000440d040c450040c0a080e03400781d00504400b502d00303015181200c803903603104144403011400c0107022a8889040c4030050f508200c1002e040c0e240c4039802c1f40140804100294407010040000c10050070310000f805640d4071a00c0c084045060390810411721b070060b40b008510500c03040281211340038510940d44109401c80c00411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 873935863 1250 873934613 873934631
    0x50d03090b0613110c1e01090203030a0507060f0606080f07020610050f12070303050301050a171e0a0b100807060905030c0f010507080d0213060f0903060e0a020a0b0c0606061606050703 81
    0x81c0207038881c40c10b0241652100b21088074100355014506c05500d1404000c00041000c0d42c0440d071a805155010782c00d200340803481c00c05004c180d0700070340c10010300c451040003000c0e210712000d00b104400ba940f1120081000340003600c0c1d00d000081d1980910000b00790840c80d10b01e0038040003080194845d41c180c01001480100c41200300420134030000d188070b61a015100d606200502c482543c02d913119a0520103011114a83c2036800304603403441035000401592170205003a006407419000e60b50050421192000300840200c40308180c50659564505480d032096441c07200f100c41c1d0700780f8005d09034107410400068415240680510b00301c0d01040c14003a040c903245071039440750364000490140d94180c0005940107600c503004164070180c400c1c1c0c10b018510950844006000d409940030081141c0d80c1c840c6d410242d05010000c040d00307258010310000340151603103840b240a8011a00010710740c0300d40c101041c51840d110382900e855102e015002000d014154a4a40c0a804007401440078140e43c0c26aa07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 873937113 1250 873935863 873935891
    0x30a2306060f2817010b032710051005010207031502250f0201030f114e130818060d0e01050930030a150f03050d03090b0613 55
    0x190343c0c803908403160340a122078040140152510034200d44001d03d440d0014040ca8032200d0649400005a1400c107110080e0b0500345031132010844590801031140300603041c00869150807a0344102222081d840304a50f49000581c1d607038520b400000c0460b44c0c4043c90b8102d00780760f40d01801c000ca58507203100a1038020000404001c002e503000580760030004440c040d0039541c260148800780300341d566040110711500750510005010700d00d203903c80da400882000c4400141440c501004140130707050030381300d502e0340d000d0b00350407010b04002200264010700001c0d0032845003140c02d413076064004a0061401e034080c103110100f0100340c26841c0e8000f00c00d20072403081d20224404c80410702e400d03000004141c100a000c0d00e01d80b0544800d0351801c1c284c1d02d4281d1405075502103010420480540f4040e84035158a01240c0103041c00395002c0d0100343c01100c0005601d014504400100c134064010354900203080c407411002d407102c041001e402c6a052001080312400c203105c5144203400c82c20800980c0110703810306 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 873938363 1250 873937113 873937147
    0xb09040e0c090702060708010602070f06110a0203101a2713051c0e04050603120f07020904060c08090309010c022115090c030106050a030605100803030c030a2306060f 73
    0x3c0b40c001a4010800c1000b015003007240c160240c040780c001814210b02e000b01d2070b17580c06502d00910b8100000c0c0854034228400801c000d449180c0d004081e1101c0300b01403101c00e00240403840181001d01c50761241202c481c20b00120400c0180c00304c140161281001c40c502e241c141101034480c0d9101008154900b02103202441610071303105403501000358403400340c0d4004001144050005100d80c2c502801e004440d80c0000b400150039252244940e01c828600550500f10301a10f00c000c0c0d00f0002e0102001701304801d5034448540340d410b60300d030300f0481c2d110300183d1662400781c000000c5c00300e90035080c18070240c45c00d81c5000c04484e4280d000701d444008040320941c10424100d5190083d00c810f00c0612040c0b10301400701c49c800100c150000c10007580751600084520a052001908043c0e0b240c020840720086424400064080081140da07241001114008240d1048412080c000c1c03518890102d00d04503022010400d141e5900c1c01ca0f684e840e0a41000780ea42c0c0446940d86680d40c080008000400b0aa00b03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 873939613 1250 873938363 873938371
    0xd091805090f0d082509030b09030d0207120807021212190e011a0f0105030f070e0d0305090a09020408150901021908061201140a02030c040302120a06150b09040e0c09 73
    0x501c0c4400d608040d01000c2c91720746103c001ca52003402c00310580095a0348404a80104d81d00f21203160500d03280d078030446045100c1c1e40e19044120740001485020f110000300d00d42c07462030840da9582440c1e60f49090890300c44188094401081c20100801c41e002ca42080c10f142e0407c00740f00f0f20202c4c1c111003c0c00981103030bd81c030b240301600b42d44807040c4d0310308103807214000800910241c0f041c030400b880d030000007010361200814000455000304041001284201d41165060b5005403204404144500700508690403c07035060703109145040d0007003030040c0e0074004e46007210148002000141c2d26140c4520101a0040082855641c01c1c0022006500c14042a030050901500c401f211030a00c0700c00d210f1001102c1c6200c0704240c0c1803d81110000030324105d446c1d408041102d0050b182d84606540300c12500c220b078400395208810b5000701341c0006010800301003941c407030b01041000c489162401c001306015482541030240c02800305040c54180f81d04000b007030181000a88000c0d001c048005001c0c11415030b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 873940863 1250 873939613 873939617
    0xc0703150b10120b0901120b37050a061a09012d0305090f0c100215073b15090402040e010509130b0106110312090d020d091805090f0d 59
    0x10605100e6004a44207104e1040800c0d114041c541d0b04180000d40f08807840307d0000d0888032004005007800000720781104030612042e078410750364200f0211710076424030788500803504c4902d8000032640010240c4900e00444c4c45000102511030440d1020203080c1d00881d1844d0305011a124001c002540c034104040700c0900b0207440c0d0218482c401000600311a00101201002d502c6030741c2824800600151180400000301c1e1003041080c031600c4120300740520745100c01d42504014080c4100c040c0c200c54400c04040d00102541e80c01a181c45091102c042011141c590607030900140d100360741459050040c1500c1c14001280c82d01283c1c001050491f0700645c000c1681560301001031020346007008203250440007458400f00221116112a000c0359418418030050005000c003510039500d0510590300e003804410158070003483c1c001c0704079440f642900c1313030240103004240521959034003400402c825100010031a9032200c0090081800a1002800c0000c541c03050080002d06000d0801280318070351890b03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 873942113 1250 873940863 873940877
    0xb04200307231c111210060e060d021e040e1f0507050712080613051018020c030d020a030b091501081602030a082e030b0c0c0703150b10 60
    0x803090950100036005489031044255071080310091031440c92410209030000048940700426100040003035105481c2c82c0502c1c0603e00e10003c106c0380c0b40c1d0058048500d020720a90542e0380e440b0800c2010041128001d52002c0c00040d030050410701c9c1c1c1e4202c2800ea03c042c1000400d6a42440d01502d058032200702d100100d4001c590869018200b4002c1d03503003142d03403030900340d04040c082d54071402c1c1c0120028440041114802c00a116955012146002100c107040700f04000e00300f41b52184510714490007040c8240e6400002068041018401c650610714904d0280d8100004c2030650000303540200c444004068a5002442403982ca120000c0c0c000c0500814000682e40c200d80090b0400d00000c0c10f002e800e1034085a0f8008168003c41150018545458940c503035903552000c203603925458000854001c4c80e2960340e02c441030010071416007603c1c01294118007a0303803124480a914812031010103416046014100009191400e20500d1340e00349410204030303406800e01140e0140d42005401d0009805 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 873943363 1250 873942113 873942149
    0xe070b030108150705072a030f120509030a0303231006080a0204030b130303060e150108090307020a030b182b030507140706060302091e07020a0b04200307 68
    0x3040110f022601c00296021441e440d100304007902a003d8000d0241190315441d09a502d41c441341c845054606482c0d0750302620841c0c407400c0c072901e08104548211041c2d00309840300c106030341c017130320690700c40c0c070b03802001000d0060302d5982c03ca0180903058500803408090203100312240300141c007698810800100000456454a00010b09000002c0c0a009105204010174800320300015003481d403242180c10031700064071036890110300420942c0d010f840001c03428001d004138005071110b040005d010980c1c0d05481c075141ca0f40c8441e20391090702002580070112503801c01c002602c94250303550058130710140d901ba014030000d005050040080701d4048455110b0751000f16445580031540000485203420002460149005400c0340c2c4d540004e611000300c08030f111410044190480d0380034641c0904400641d0a03c42e107003284001d00c0030b6201400490303503000120410b100040650140350000d10103a40c9441c3c54850f4907a0300c005c00d000401100078070600707070b9042c1c4040018200134a021002c0d40d003002c0c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 873944613 1250 873943363 873943379
    0xc01020d050a0b01080c0313080c030c010906020306011724030f03040303030b01080901050f0613021c0b1c0c090b131406030616081b0909040b1006170f0a0e070b0301 73
    0x1c0d00070180710401b00c0c14400e220809036100d00c500b00955000c030039103a641007400c1c2e01c0e52950290045000156003464924001c00801d50059070040f0340a0320f810761141c080b42c21040d110711081b01c20210f07800560b01d80d640d8600d19400200c01803c1c0140a880104403042a4282541c1c03240c0c109401280d11081c0000c1296030001060303611802c043c000300180c0c1003400c3d001e481410084c00283c42500e040d8a00403102e555641100c5805500800350044403415500c40800751032400d0344140319450900107010200300000e00d16004980c400f102d20302c042e040c00703003000c028052260302c0c0e90040c0403441883c40400e40f5200c3e1120321401164041c0c1d0340e10b0f10307404251500100a15200701a40270701051051113800426490300b10910211040321f0b4241c103003c010741400380341c1e00107502420103070902051100382101180109400c100c44e6514a8541da01501d80c8011400c1d0b403400c0d50038600004101c45001e00000303400c00107030a40804d00b00000e54110307241c0601a001860030301d0001004000e411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 873945863 1250 873944613 873944627
    0x1b15090a0f180e03090d080d0e070f0f030302030403150b060301080109120302040617090f1c0912020d03031e050c0c0c0405010503070b0309160303170a050f0c0c01020d050a0b01 78
    0x141581c14103201d4014501c2000e91a4017a4021083c0125030b040111010001520265a03000e85840c0341000501303551305910350350300c00b58400d4100780405001c011442c0701d083d400400c2038039010740080d490076183d40c1c0c41d841e160300c100344042a115928a00001290b039104e00850090000e0400486c4000c06800d1106810122400c090285441007108001d999001910f51003290101c0301c040382c0c00d6480c0300046062080c421260340d1180039042c0300303511003901c504095001c00450b603a480b110341c2e11800c0b54066840a600c010b5403000042d00030310300091094000164008207113101498554114064100f92401036074030407a000c0001c9400302442c8420402000a8031040354140f00035490030703002ca0340f101914011607141110010000d114588100002d84504014440340c5500683d00d0400600b4001c0e00544101001c41107004036500040a00946015101641c0e800501c0d4549841e4409030f5031241c41c0101ca503540900100d044000c45200d00c3c0c1c460707061424082154034041c40010080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 873947113 1250 873945863 873945899
    0x6030c0e120d0e130606080103140a03231b060a0f0204030c12030215090c0405180616090e04060e010b03060f1302010c020d050a11031b15090a0f 64
    0x1605403141c40c90600100000d100030420000d00300700000c9440382021803100d442c250120031109080940c0040c410394400b032440d040b24010300008514080190603c0d48941160314017034000b078026540d150015840706c22080101103141041e901e494018a00c050007188200d0f04805a50001401c114164031280078400c0150300b4030303000718685402d698503205112039500504581c1801d02000c1c1c401c041c02006041301d00000d51484034554034161907110742d81c1002e0500140128100404129044103103400d05141c00307140009041c0b00d45d1011400b1510064143c45402080288640000d8207a443c02950b40220702400c808500c407282115201d0960712131103a11800382c0e01c0302c401c121031611b143c0d0f030264004130481d500d02140c0d0f1003800102d90007000d01c0c0300a94840f42d000703424410088000f98100e103103032080303141c1040604200c040580f6109004845541c0001c2c0c00302288092404040504203404112044c074140401000410348a00c01a00201c0d02c5204070802845210003601c0b0000078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 873948363 1250 873947113 873947119
    0x703113a0902091b0f070c0302041b020d08040309090f0608070e060901030602070f0204060e07031b0e0409050106090c230f090603040c03060e03090909030a051b010209040606030c0e 80
    0x700301c0c203940820b01e44880100f440c4511520346060240c0d0504c400205c480d000c00c20852161121003909044034903501c030f880220300c141c1c034003d02680658500032689510b2000798010344008410b1a10555000c0002401201081603101c00444c002a551082c46114000000000758081c00d04000b0380c500661a000b145500c0c240400300319a60761403c241c581500d84c00300004d41c481502d03207405108801482d400961003410520042070212a4401c038600c1240c213690248440b0741e1482d0052507841c411010f400000d220340e10560118106504007181440c81103000280090303840180c1c0003145d00c40450140059032000440e081018010ba10b0a600d240c031800552520f280b0b81043c090a10445400300d000390008070000701803280c01a02d0b400110b13004074042c090300d00801103c035107a0380440121403085441501085081038004280e900980c00381d00c80d1442d180040c41076a14505005003403103044e6400b00846400c0c5d880724000e410007000b40d52004150180100d20160018010101143c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 873949613 1250 873948363 873948371
    0x6030617070f0b0a020c040204030b0a14010806060d050a0f0b0f070f0903060f150b19020a080304020427030302040f08061e0903040515040e16080703113a 68
    0xc82c91294000c03000856070b4548000d07a0b01c0041c400c2c02c0c4c0c2032502c0e141c0f0f4135901c24400300b00001486040380b110362162044c04400c0100e0f0012000c40d019280081c0107826041c3d20a07000034506042c5a0368141c6002e0140c0120340e038003411943c442009030b8238203074100c070040060b10500c40c01d00b590600c0707a90498030301e00f0892080200703000000e00c10302080c400604500d843e803162034403200c007550280d00d000741050341005140e600d821114800d5070007405401c2001102e01c0a046070644045002008103502c4660540b440e19140c08100c003400303c000c0c800100b0b00881c0e00340c240320101145d06c1c04400744a0f40f80561218070f0160340c1d800400c802da0121000b504104100b0520341401080201c08203409108507080b03888442481d4070f1409941c00558118a0407d095094651000041c0c02210048400b017107003030307940c081e500b02401000c0c02c00e2004596050301003402c1c24040c4c0c00035110760405140076401e101c145441c4c11009640f0121583d085a0140800381d240c15051f1018509907204110901c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 873950863 1250 873949613 873949619
    0xd18210c0c0906032f01120207230f0a080d02030912120708100b0715061503020d0605040c14030613110c010c0207150809010b031c02190b2a040603061707 68
    0x3030009202c0da172421304000380c048920508041c1ca43c143d401898102035450342c120002c2198613601071011810305002d100741032107441849000101c84c410503510844035800c001c070b0ae080c048084d41003d030100c6294081d5442c078882540d22840030700719003000420304c014a070400d820090045a80a0702c804a00c0c0b0f103a000502c00040d10a003202e6409a0008003800e40c4006184101c0040105820075040c941003184042030702980340d00904203010560508000043d0703164200012a40c480081d400031400880011052800307113400346a1142010300680c04c000c80c66041070003120048074041d440c0e00b0000c01c010b840c03540d00744034221047c0d40b54002004158104078070050400d01070364402040040150003c0c2810f4030a400c140c03480036000d001c03105194000c8542e80d1004aa0409140c0180b00e96003040d580c226142d503c000109070031440c070300c0280e118080e03400485041100f054000c0460054000b614400c11002803000301025940040c10b0303828a4810b000341e01605580081c6170707000c28414 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 873952113 1250 873950863 873950933
    0xf200901150e0909070501021b031c021203010906030b181b0f0d03020d08090c18040201170a050712050c0417120d020d18210c0c090603 60
    0x1541034908521040002032207078081140c200b2806508240c02c10701500511034a0703940001c044040e10030907001e8a92990040d074200c1b106101000e500c640c50781c454032a050440b41c0f4a0005103406039980b06480c00f2412466170074000d0340c420313404400e0003599458100b05000d80340c240170ba0084200d035441101051140445540d42444603954031401c240d15403a41c00b1543c0d01400d040810501400c46070102d886403c02944a1400c3e03000ca0303002c1030400c000100d101c200030407038450a000c000e0881742d070080c0b131210080000c10000c00c100e051110350040c02c240e801c0b981c24114030582c03e03200042018030745120010850310500b24003521850510003404030400a0708207903010f80ea50311040c8510400b1a020baa03140c249118001a0f031100005802e9601000640013095100d200c034000b800b00300c141a40c1070b032008940d4034010b4075264000440d00058940a407588102c40120f10b031200510009480e00c403008007640d0b0114910366903901d0104100403070000c4040180110307440c013202c50503548801c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 873953363 1250 873952113 873952129
    0x51903171003081c0504050a05150702100f02040806090c0a1a1c090807060b0a0b03061011030d060b030108010b0406030f0b2805060a050a18020f0409090f20 69
    0xc020103000010130040c0c880c0702030303200140304043c0412050040d0b041504045850315030941d4146c505004500300000205d154040060042d51503500800e025101104648001d01c6200b08210342b4079020000040d50050130001d4500030440e50300503000c03800740c0c0c1d420404849125441440c050116039012002c042c0e80c030040c4c80d5401420b4441c22011880d02000c0d0008101a94008103801c0b80070800130240407241c0e00c640242d460558a83c1da50075114924982e06010444420303a0200181c00700c0040d8a03c04d40a40e020200c03040b007264200000c2204650941c0c840c0d82000b0600742010004000e06e40e024061141c1000083d40e04008003400c40d00c90305407060080c40090441d01c0c250020529401400c40140c0c81e82000c0d1440d0002584072420b00c1d406401c0949089100c3c40c60104045668900404100101c48005400c1d03450000002e0285c07000c0d411100060340451070500c00041c0c40c4005000b05000b40384104c049981c500726900c0d0082048080580b428480540c40c100e400c0551180c0c15 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 873954613 1250 873953363 873953369
    0x170703320712020d020d05070b0d0e120702060d2d0f060b040510050f360618010c080a09080d0906020601030b04110301060927050a0206160519031710 66
    0xa2440c84c441da0500100700d500d90070309030042403445805000605c10070550054035500002102c00d101081050705e08035503d90000d00c0010302c9000401c012030051a184000341845024140c003c0380c501e00301030b007540d140d400100f5100d420204180c0d19000900513480740b03543c0c2003200b0100300b008a0801550380c4c4180150f020715401351480003040c2c15041d024030b003030b2584410628a03040d40d4680c200d8101410120010a01c8420320f07803120300c00d2140008031004000031030054800e43c186100d58690150010000c11018148158042c2010215075080d00403d03407224507445040c0d240b460038102d18948981c4403a2481088068035080c40070075400b01e0080d044075000200e64049895170b0400000d6034030501351180d455840c01c0f01c006040070f00c9070004a4410001014081c40070005400d0402029010100408035000000568010b140c4400640b195603029075401107a02d0042c0d0f640c0c0d1610980b000098500d41110040c0010180c2c090400e00516a0450f80001c483c2400c8120400410300d80c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 873955863 1250 873954613 873954619
    0x50405100c021203040f21080a0b0a080f06100608070c150209040207030f021204030807230615030601050a062309060d02071106070c17070332071202 66
    0x1103000707034869208104904002c240c83c1c0c03906a590401e45404840450b0400040700c02e901c0c40c924011043c4500052060000780e1074403001041d0391843c4100d801003001c40c40f17155000700c601d50701042420b010042070200f41c00d01c000400d83c0e410400c107500e00640032640701e901000b84030760800c0011075000c2c408030200c0d42c1c02641c001000403001e4100e0b003e405a41b01843e0414404180c22042c0b40d408400501c00312401d4090304c094000c0d1001c00c0040d44141d010140003043c0c2002010006008400481c40d030a551503030440000e0010310300e050034000240c512a04510714400d01845914050084500501049858818044c5448000f41c0003043c0d641070340840038480360000610084480c22591040c1004006a0fa610200c4c04070000a402c198070030340701c0c1210b201c00c60201c2d0604500301c5115a40101c00c0c0702e50b40d071401514081c1c0400d20004520140109440040044c9400d510080200790f40b9603024440c3d110041c0c950a83d952400d041039896000038420000d6901c440d40c0154420703015 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 873957113 1250 873955863 873955871
    0x1b030616051803011d060703060501080105060f07020a0f0f170a020f090912030c040f09061a03070c05060109020a0e1806010e0406150801080f010e0709050411120303100905040510 79
    0xb800020b0060180a00d03116030f80300c45040c41204504041b45881c8030300d500da2000c001350364a40b030044416000034000c003600400e0400c2107071088070b00c10001d815058401448182e410780c0300e80c691200e56140d030f8400406410400414010006d0a2400f980000d0121008103074041d00c580000e000030507000c000c0e138007a003644401319150303000074010321081c1c2a03400d05059980c20700c2404201c080e4007912402c080384800a0f0086410344150090300e04443c1051003048100e109405e03148420351000d03282c0000e001044122200217141130012500030202d00d00010b80391a00484081c03d5a11040c8450740300d0624401108041007640d40125040f40080c60a4450458070783e0109009002c680c210000450509201c1d00c5800c0d8403804880c1642e50800544444040d0000d81600341c1e0420410840d003600b1180c402e2002403d1680017541c424096200c03030156500c1035000c40c041000d031a5038804140c00020800c08800c0040411000600e0030081c00c002520306902e40c140c680000b401d044580b241c403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 873958363 1250 873957113 873957157
    0x80c0a02010f090b0109060b0c0303010b0a05040f0b040312030203310b0108010e0d051305040f060b07121e051c060f060203040f090b01020309040b01111b03061605 72
    0xc00d51101800c0c0d9071941d420802d260044c01d1003070b00302109102d84162582481e102091060081c000d60750030b00c40320720003141144d00345480340c44150041d019140411406010004440c0910b5080380000c0002c121099616803c6003044900c3c2c42d0b0b08884241403500410078003009441c4049040100d44410360241d407210b506244043ea1800c50b100094440302602c0004102c0100c19030005003240105c2040311445110400b00b504e0358010303003914000c00241c1d0101040981015000342d089030051a400081c0d041d2100b407034100b65007007244241e529444403119800d000b80c0140300b1584070a803816540380c003507042c90300003440351050a28612442ca110103512003801115000701c0301400341c85100203902522190004e5580d0010f100c0e403031720030080302c60006070300d0710a102d4400e2400f4180e02031450460000180405400d0b021840ad0410035413000c2c29040100c248402a09900442c1d0301d41c03164000d0200f094580703100a02651440300781707044444000d5401c901116440a03200305950303800c4103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 873959613 1250 873958363 873958367
    0x141f0b071e051f1a0f0a060c020118080c0a05011b0809061b0a050c0405160c1b09021308010501120b0406021611041a10120b10020a020111010903080c0a 67
    0x455460703261103180030b501c03581c0d0a00341c843e040038501c244050070452a10303042c40100145101c0204201b5041a08840148031803845441001c84050043c10300b9a800e00e00301043c0e01003460301d80d100b03a5890f00803404a0140d4a0030000c2500100024a403400c000200c0702c0c183d10200011001c014054400001d86040d9502c81e141512280302601c0c0110b4207181c1440c08007916200b0707000085485028221400c000f0745441e100b198020001c9103e003140c0c40300d0070389007135030300007900441074550918003115281d500300f403012034001403c403038080581c85600140c1407490b10100c0d9040030401d070341400010710034030305051031500f8181d420082080590319141070420080c460390581180314004030104c0400e12860043c294072130903007a50104131a01d42030052041d044104405140e01c20483d00c00600046e00c1070f03640c041044111840041d68400d0030000507010b204844040d0f0168100c40c4143c015582c01c22844902042e03c0390082c00007800c55940109038000040059501c0500480d0b5004914 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 873960863 1250 873959613 873959623
    0x2030d0c0507210f0302070e010e01030b0601050306011101052d0c160305040801151404091110180f0f0806310206030a09020a0b0901021f141f0b071e05 67
    0x340c3c000421300c20f000403c0c10025100e88550180782501e0f5507280c000225540c0c0c0711001412282c0204403524036442e8080110740c194000f809603070411005450445141400b880342a021f800300381300818002e0651a40c0d20f40c0620000d10703956007500300d0b400b00035000b8803050442d462641410040b10f2010031a1800755454007440d000041550b00e01041000000d04042011013511441b0620b0500c3c103801004100640309459002441c5090b098560900c504203c1940041041b1a0625025a40c001c00107540e00300c51591100c00d131020900b80c200040721110040102030070a51000d41441d240c00401c4c040e81c190456620401200b41cbc00c0d07010f01a00880d00354402d010750040066907203081440c030f4200a030168600984c400e4502c01c00024140c25180207d6820b03080607000f403c0880c50a03e51801300800c05e101e00c0160944852000d41850403480d1918401c0c4028003101c0502c5640000c090718014140e0030074000c0351002c10640740840c16203111000c1c05850681800b10380801807a00900f41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 873962113 1250 873960863 873960929
    0xa03170717070302030a2715020f0c070302040b0102010203130b04210804110105040f03080d060905040f03030606140328051005011701030308040f05030705061302030d0c0507 77
    0x3507069005004030254940c004500803a07110000340200041c00c0035083d0300b0f09441c04103248296280302904001905200d4240c0c241c0c410450050802e1118000151650b1262000781596008040d0038001c601c0c0c18403c41071a42d50a100031811031528504983d00050464000360003400c0c90000181004100380c42d400038450410f009400700c03030307500030082d00804041d541203e031304007008034110b002e5106501b078804848100c4ac01c10201c07407440d00e9001c072690110340516615502d0f40c20214046242d4042c10340198401d0210b00f0060240d400d0080c1140c11340d8121100300120314503080040d5180c5d9041e05c3d0440e0300c400700c80c1c0050002a00181ca240c0407880243c003524105010461503940c0728045034201e0b0402c0c5c0f03d00d44001003040550382010303070074000103010800e61400310300418240c0c003540003564819011245801125120f107844e05004448010003c002d1300f050108608042c4174503007449034241070491085070343e5507070b9035160f50090040c16405408280b0f1034880200c0c40e00c02d1850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 873963363 1250 873962113 873962147
    0x904020409060303080604090b01050d1e2f0901050f01020f0f100e1914030403080327011a01030209030123040303140c0f032706010f05030a031707 65
    0x246075079507807058019144521040e000b1501030400034010f0704003405850b06056000403000c5990382000104200c0c0d107044030701580d5117030564190b141020181c404c400f40c840d02504444a980c00c8040b444074041004802107001d03404011052000307600c9a500072419030f07100b142d031f41440c040c0782070040303142000080400c0c2140c480d42c403200f02c0e52000481c58402802c1e0002050059144031850183d880015a948841840c049c0601c28041001c0858854400d500002503e18240d80d9482d5803000b41c1085d142d01064450507a90344460360034004400003d0082907000f80718952418070140949890400c08a05050700003a0210099030203501001100e403c20402c00c00c041a010314503c0e913603004890840c0030038035042800e01d850803e444418400e5100c0c181c500c0c5400580b001c02203c0d07810161500710041d620144140b800114a000f00c0752007004140103040e690300d41000c00700d140c480356000340e000e1b81280d416000801d91040d501000b000c102035002c07000383c995078402c60710266054180d0030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 873964613 1250 873963363 873963367
    0xe1009050115080615061b010c02100e0303041b050a0b030a061706010909031e020a05010606050a05090411120405030705060106020c13050601021e010b27040f08090402 74
    0x14055012854040c0108000c200a0030102c10780035104445005012807640820005092141100003442103117001400103030400b1610700f0f13981e0325604941080529651a1003104030f04a0341007080d0742503451640001e000750714008065a841c0c0c4005003015100e114035600e400e6601f0002d40b203001c0105000703801c842d2029a0341c40038000303907007090303600c1b80a842c103010000503a185004090030010f92402d001d014a6481c000f8010018030303400fa0100d003401610840070405d05004c400e907105100e05074000e000071100c6880c240b4210340540e040034007400002d010207102a50300006648042c4019070300096030f0f41580c000318030f6a01450441c1810341641c81c01704020800080040c0c0043c9214070b0458050740d80301c00040c1d03100c0e0022a08aa0480d001c44040300940b1072581005801003018010b9a190014049500f092041c2d110400401d81e07450300c1c2404481e0400b0301020304030080c80311403240700d00b1080858030107412014001600300c000303d4a0800a00c44130300d084422820000304215 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 873965863 1250 873964613 873964633
    0xe131101030e2a040b060309070b0705010902100f020f070b0406110f03040308130b03010b0a0c0f02030f03221409060a1707051f080f0c070609140607092301030e 71
    0x82d90360058011030f5004034202915000c80341080c1c2e040c2d0780034070403a4014200b0141407400006150704000829907840d0f403129148e40c0980c40da000105035465056035032140c442030540029141101c0407050b0034060b4003e400400c004034085068500b5180b8900e001035180440c4550245004000d400040442c00009000001c200d401d0006220583c1800364400d03040ea901c60954a150009101d42e9841100c10008440c003588202c0c070805090744182d06403a20030640381c0110f031034444022800c160540c400140042298a140440310070041c035101c000d5203503070a281c19102c6944540b8042c501405405000c10300541d6401c1e207441c0a4128003100b8421919040d124580d940c01c103214050085460340c94245c1010041c02c0032000024150300c5a040e99164030007120702d140001041401c2d5444c05024140000c0e209025042c0014046c0d1421007110200031200f5003803601c0a40100240100424200030441c011070540b05078920000642d41e19515080040c0c4c06410b86200c0e401190082420700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 873967113 1250 873965863 873965923
    0x203120306030f2506090f26032101143006040819050f070f082b050f011802090a030c06030c12051302090402031002040303090e131101030e 62
    0x211001010245206805d54900b01901c2c00f600038007410100341c50301d030350501c981d00f142e94100100f074500c0a051041c404034190042e0442d00411143c0440c502c040701d540a6843c00e00120034003500ba0705107165250051324001566071901c0998011017607101c0801c020000d10a680004160454a81030347c0c894640743c0f0300342810350300140b41c00b10681d520105103400103210300b090300c91042d004a415071404000f500c0c2d0045040240d8800c031101da108001c502080d003030080c01c3c4050001000841e0040743e661505090a580c4000d0400007075140400041005c17200912402c138941104050040e500c000d064040b881d000d0b907942003d0b10740101c1c01070001e44290f01d0791200304c0c505081d545555074885140c0744541940e0050744c41411100e101c15000001d407030040d4045400501c01811140c1442c0701050403000d0385c000b44e00036030206020f0300d4100900750500b003201e98030460362a808500e1500d03903a11029010300c0d1541d40c0d4100341c0e8070042442d40c0700007008071103200000c0d0b0a8440d01c210042d03980c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 873968363 1250 873967113 873967153
    0x1406120405030c070f05010906031a040213080601090c2c0604030b071808120c0c0d12080a020c0312150409060c020c010302090f04050c070b0106091a03040203120306030f 75
    0x2c40480344251840018245d0a25080d4001d03120141d4a0b4907400e0328201c800ca0280041c0c012403201d001603d003040c452079850707100504482d1482c0907110701c413030314201ca01406c2400580c0440c01c0305041c910b0b640d0000394003103020004840b614440b0750000d01d5064020b95102e0ba403161198000c58001004400d01030700380c209070310400f1580c2c0e0307455000f0300003000003201c0c90080c41210300700c0c0e00c4203e0011400c1c000501a040d1388203132100b120780d1894a8000540104c00c20398058a000b941403016807075043c0d0144a45502a0002c0015490518001110340d5648104608001441c0300c44000c03032170300c00d4218882c5114401c018028000c442c01801c010700105401e1502c040944182c47d070340900d03940207000b5905010f00040c22859035403215024800502401003001d040d22400300610320002e00b540000034040c2c80c1c00c0d52100c4100e03040c414892143d10030441d00b12103c0c0d805000304030050790000343c0b034400b0f030b840c0540040d107039265000031a20301200c1c894031101f18028486009424218121 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 873969613 1250 873968363 873968377
    0x60612060e0d020a080309030d18110907140a1e0801090510050d06021b0f1b120a0f1e05010e100c080708100f060f09050415140612040503 61
    0x40204015100c580c54942c0c2e542d0103607490350141e04440d1414000c1030400001d036600171022410f4070701d8030b03c2c2d00c44140110b4150304402044d5001c100350101c01c1c4000c1d1030340c4142200c1c0030703141c110b06402c0c124005800c029200f03105103800c0c3c01c00958559458420100c450f00c1142c01502020070303080c4200702500750402406a41051450500001c140c0b00079070200004070703640582400700e109000c0e01c41d070002c1e50141c1341c8106e01c45040c1050360b00680d41008007070103012103a00075040e04420448070321008445048824418200702a204c01c42d030701c021a030245401d0f84644045805000c0b4a000d0035994a03000304d203000e11900b90854001d0001c10b4000e0f401081c0b241e81502c3c1d030f80700b0b200524002c95004d10b080380c0000b03440c100011040307401003050300d400403001c0080c0d0380041d5446c0112110380c455034101e40002852001904000c07500035803500c2c05000111020300c0a1030000c41c503242843e401d4412501c0d910b1020b0310031803c9458440403242d59207200620603c5910f480c0c00c069960b81c0c0903034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 873970863 1250 873969613 873969623
    0x130605120604020315270f18060402060f0901091e0e061c260711030c0301090512130801020a03140a06051f052b0f0209060322060612 59
    0xe40018a070345803c2c401c880c4280c407074118000340e840011052202421072010000003215030480c50042a0740c00c10807040c4641c00381c1c80385503514500100300c4141000c00c0d1000106550052050000683c0d82d0810341d60509492101651a07440d8440100d565204551200c082190310b5613005681c04020070041c0709403002c1088460f0f094464009200325682c9880700c0508166500c01c01500081c0007100d1008030070502a0301c420120b00f0701c0041d62030396201d400d00f103a4490040c1100c50442c1024805012911401c40003004240102d4582d42d0b242c801040001d04800030003e035100c0c4c4420001d48210207410204002c640780c07007025070003800801e010448121403009034000100d2512280c054001070303400242c014514000d641c003103c103440c440d0160007000d000051140c00c01040d0805110041d8080e08102d0fa80c10764a424002d0040350b1a54186158044c010800d1070410b495003000c83c1d8108030103107075410615041d103442040d68400154014500e5040490020707450040407440583c0d54028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 873972113 1250 873970863 873970897
    0xc12051c0306050f03151f4406010905070201020c070b0d11071a07050c2d0106031e020d021206060a150c0f11030109080403050f0705060d11130605 65
    0x44d8040660361602140c10480820a070702c0000e160203640d441c42030703a40c144c181c040c1d076405841781c1c801d0602c81c44401c00314030b044140c441c2c0504c40d60088480c240710a84940340645d41990b100c2d203401e84451050142810310b13a104d002046041d03200b503049074421a202c1c3e0582e5807260b1071f810020803da021010203e569400c0c4500080048086000c0355481c5a02c81000003820032011000007103102c0003420041031240030701c0349184c02901030005070004900b40c2415048031b240c11640075400105a00300705c7c03c681c58558240300080004072120010804155031035461540752000400b10305545030300a400207601c21720546c15032130006056000740d804031074548003203840d6486481c0200031510150005a66855010045082c0003040d58849001c2c2c0d40d4280d01c0c1540c040420f0a4a01d03890080b591003000240410510001340051030f486044a0080d02c2c1107498000021807034010244058400b981d50003500c084441d0480446640101d806480110035940350741c0074019070408550400d02d4250 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 873973363 1250 873972113 873972139
    0x1008070612060611030a0c03020a0f080a1709031602120307080408190c2601020c03040e16091806090c050d0c09030b07030b030309040608060601020f0a0c12051c030605 74
    0xa010b100031300d100c50f0f0005608068032070a0444485070001070503002d40c0110709460780865000910300b48114002c1401681e90b900c4c002c0d00038030b0200714054692040c5045411312143c41c901004841c40a00c0c03001c40303007211f9499400001c0c5c081c004c0d001103a04911001600c40304004205019000301d034900340030380340142d8800203d022444601c210042c11000d1442c000d10400280381c034600f816441400101d28440c3c907905c0300508a80c40030800c519181e00106041080e4000c001300306038044039a20402084c10211000903100c96114092003104d02e0f494881c3d80340f045110781c4031070010400100c007400387d103120040140080e400860701d0402541001401d8003a03030700900359103003120b511070044909692008404c8008214000c000f0742d050200304a00241d95036203008640c0903150b100094189420400006842d103081c0004c8a9143c4c0c00111540c030126141d10359010843d080754502c40c004084a2408500b410650250a849400700346804004142d040e031050041d21002d07101031000e001e17 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 873974613 1250 873973363 873973367
    0xa1508031228060608090c1f08040f0b040f0201080901050f010b090102031b01060f120c05090c0c0d020604030212040b090409031707170c0c03030f10080706120606 72
    0x101d404890110112084003042d40c20308451026842c914000d207803814040c2001441c1c00070396410b90b002000080d004001e00c4201c0b035051042e032000310001c9a00540c1348902c0707840710a08203400c5840300d06024943d40081d090007004400c4c0500640d20041e598001c4c03a107860400c620240c4890240d001a40340400030309410340502c43c03e4080e9618070800d1003943e28069111085510000c907040c1180410310a12400d000b0f041c4000705a00c1c491000400c01c503040001b140072004087c1d21170480107150324826400720358800744c4002900c03801ea03203c040c541d45604046240b44114054003145200350054881807650215009000d544260b007944c0c0e1410501f88001141e000314021110149000c002c0c01d01585001e5102c1381074a486400c021200c1c0c040107050350241003040b01c4241c04285020561450001e1032083e140e030010404211030304202d40382d209245e607400020b01041010030310601181c010b50101c10f22030010301e40780e801c9501868540400504030065503034070615507800d0100100e4064 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 873975863 1250 873974613 873974617
    0xa03060f0c0302070b0402040b1302041404110405010f030b060418091a011a0705120c032113060b040f0e010209090a05060d0f06180f0210020d0503160e090a150803 72
    0x2d85c0213400448584c889400301720080511000f0240c1c0020400801c0c00740c000540003601c001d228444205114004010500041d00d0402d050b07458000e4041109000c0c1380e13004480081d0010b084d1400140e60031035a00420303817034400c1e42c018525501c800d5a444150401d82d41050528074410003070f000d040031080140d00740860080c0924101c44030881818518100d80c0c50281c50101e001e2000c0b1170111511890720046030348400460f5245410001e980320002d409150703545036070b02c00c840254259107801140030948003a0b4540081840740ca07903014815568031900080c0c0c03c900003020401a600c00804194001e52040020764095003c070780020b0307500301c80b0b489003510a05010f00740040d040d00e503640340401424070010440b0041d40e280004070070138a10340051886d5510030b80350ba40b4000c4080c010002402c100800c0c0c2d40c00c40d8003135400d0000003607000e0103136500000c00d03200764040e60101410a03500d000d0070705420758001490604100302484541c101e4040308802942d880300701074540c0c000944038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 873977113 1250 873975863 873975877
    0x10091a09070b0a051902160b071505071115061206061309080d0c0c02011d011d0d02061303110d0f0206180607050105072a0605060f0a03060f0c0302 65
    0x3a0300300303100400511488000070041d0740420315100d40351800c00c41032001c1c425211001030700180c0c071189a4003070103010700c2e0b540c4000e094114909800e220304ca580b0a03130200f00403000b81c2c03c19a101d00110304035900500e1121000390702e0100b680e2100151804081816030300f140c0780307440ba40c0104510a5001c0011500c180030f808040d02507000b4100381e080400282c40318100440e010301c0c00b042801d20b420410721656001e8181c90f612071600c03c44500005181030301401ca04000a045c0c403c40e0100c41c1c1e04050303045d001c03c0d4001601c0ba040ca841d800080d0100603074031006500040002044004007581d5001881030b00e00c20008004055084400d000d8030302c10741d80006000320403200044015151010250207014525001c100c040400840811200e070400c2008503100d80d119000d2004030350b000f5884101e007525840c91103042d0208000b070215400c2140e800034003010750f40c8000c601340751551648069406c0024201c9684035641c0d2515100800305403c1000c0654945005003a10724400d00031507140c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 873978363 1250 873977113 873977131
    0xc05030406090c05060c01060312050a020d11030f120108012f0306030313080d1d01020d050f09030d0c060b15090f010c0615140604050307032310091a 66
    0x15540ca503034030180149240103040e80c2d9501d4540d00020302d50740741780080c400304850740c1c0080303002c5e86946444650f02c2e07130b40004001417210034405070142e580c1c00214210949100d01d4820a4a141d2200040c294071170302c12580070030180019220300140072024454100c2d4170f540d00030003150044407a0300c107290b404403401800c041e00803030480e0006611080a140c10180040035a03180510181000e1665105a0300003031080d0050210340411540142074114840c18400511240c036201100007525440358440c82d909200c4041103883d520600001500c1c1c000b1005030440d03121009a04e40130b046081c00080031540f040c1426545d00d0301d410540b00c2c06400c2c0061107006418018020704000e02408245822130400880e0038024000c03520b1405031044203080709a1210401d81071210b0340180c604d1141c1c03c10b004440c100400c01003910005003000469412950300203007841d01c001c044019400e41c08000c181d91060b03104c1442c0c40c100743c0d406540490310442c1981c980ba180c00003044942102240c202c44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 873979613 1250 873978363 873978367
    0x30e030f07151e080604140106050f0f041a0c06010b1602040e010f0c0504051e0906120a0b01030c1d060d02010302030c0f0f03090d0203030408071112011b02010b040c05 74
    0xc085044140ba4000d01682400c19042d0101c02048094040c034a041100300060407010500c01d05042510031140c10700400183e80906604010f0042c0c4036104605220381304400000d0000950480307001903a014042ea40c84103c2e1100045000c42d003036410003e074100b03188c0205c1c00000340034504141102c600780c02c0b0017804415581d840d000c02c4003c4c41682c0041240355250502410380074000d00c2081c00b60300303a5072901034940c4e081c5014003041c9000c80052130316007000442043c0b1960b4801d0001644400111203803155401c1c141c072000e044c108a03843c02405400c2d0750340040704000d0051141c03004c2c0d4007180da41b14050f000122403207031020f209480c000d4000c0742c6000048003551094008541c40540c998456251102250b144100c5510bc1d190816000c10302200f4082200001d1001170780080d4070344021800c504240d01c400c1e65512400d0703401840501c8000980d000340d25000845805449682c1c0204aa400d00b401501124001d181001005510b8068142c0d02c0c0d260a00c40c4071201c00090b03803464 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 873980863 1250 873979613 873979619
    0x302090406020705030d0f0c0e03250f15080a09080a140c0a0f0204050c03061c03120203090102091f12050c0d0c0203040e0c031603090f050f0703030e030f07 69
    0x22508050419140603400b0840d00740410307002c00040c510520481000103070b0390001d85400301120f400204420400c030203001c06046650b00026104010040d05403e4031340b91000000d070b03c0110070b15500010500e0384001b00017545000c1e80300c3c08803d140039034445803090b5464003120012142525801040070310280000d51203984140300240c07030702201c00c0b01c072498007104030421032600044c0942104c0b0741e0280c00c022011800c0501a80c0c0c1c000d024081028210708004000820784d082c000140802010b52480c0c03182810320640986d4100c01510000710368904000302c0e0b16020b54000d40303a50740a11091045403500d0035000324048000960713640c444040c0300c0d000d08450003030b103005040c0801c03400b418402c02c900141c091003401c452494940042d0ba956191111b02240014001c2081e840c0280a004121103001a4094029403100314940002c03c1001031801e003000b510b5031480030307029210301c3c000c88020f8240001e0800a5a0098807001c03c0d42c140401011355420b100d102d426240e421081e030030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 873982113 1250 873980863 873980869
    0xe0f01060c14010e060117010608010e030405100c061a120a0803180c09010f150503010602100e150c04090f0b1003090302070b0d0f0c03020711150706090f0b0618010302 74
    0x860b8094a540082030754050800d14525040080e000008841141c60f0b045442e02000d101d490000c105010003800b2a1310281d44480e00c0b4001c0313100f400d0040750b1481c62103400520070010700704141e5000c1c408120001642c40d61100d166264800d980c000d01c0c4c80c444010019030001441c9945c554065102c03881e5a4441c0412507203030502402c1141d06204a00c00703110309507034a20107180a0605801c201c113400b45444110048031950403041c60521804200600034194049103403002c0c481c10a20118400703401e00301ca2840d050341c2540e10281890080103100d059850800103004441c2511801e100042c802001c2c03004441881c440380e40e001480c121480103480c0650405851903009005441140d039403072401541590160015004c0380c0e03560400600041c0440c800d1403058030203454114101002e6607520180b0035620b003a4030784503c039002c03000100c610b00c10080f210300c80d62295050068240314504000311403180042110900800720014180d41004952150311640c0c0030f070b8040c02a441d68080c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 873983363 1250 873982113 873982133
    0x20f0f04110f07050601050a060f03090c081b0f031501030b04020f152d0a11071d0108070e04020a0b090402071e2f011d04060f0e0f01060c 61
    0x2000e4215071107030800899210990080d0220300e9002c0401aa10001890224100320301604090b00c036694400081c4801e03548a45000210f24050500180d100f1407400c00b01040f044962000c0d80034401c64002c00280801c4850a0985c064151070b00b00080440c0030801d600d03003039a82203011030303040c201004001064140d40309039003050001e00030603103140c046004545010040034031500003400010300003484010105880b0540c04c010043c643c40484843d104601622401c00030b58200041c803000301c0c0b5108018030030780300200100e8101c0c0d0f0356603011500c1d0400b814800d00c0f6040b5180180340000030240041c004141c441c9900030302c0000414280880500e1079048201d0290f00240e003406000001511146c0d0a0f4445549801084d030034100e902e403440040400c0b42000509005299600a010000c41c4070b10b5080c4809091401c11210401203001e40c1e0b410a2809540c050300341200082c2c0da0070324a118105445401525504d2982c81c00180c483d060320a101d03110001d020040c01802085034070ba0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 873984613 1250 873983363 873983389
    0x319020f1f021e031801090b0f07020c03030c01142a07051f054807230d020102132321010c02072102190801020306011209020f 56
    0x3100500f820180e440b88010020440310803c0100c10000610614048501c03004804a503070320024841c07914161380fa4801940040c06c980c1004240b503010620b542d00034004503008803c0034003180d484035446103240703004c0d01604035001c0b4283c0d03565021603040840300e141c203100d41200c0762036880c0300410301183e1811076109010a490754018680c010301e42d459001358003114045140c00200e01410540e0308500181e6001e1071000c450031040c038660705604940c2c4000b5980d803014007611141c6520780043e0500c1071081210050100d40d181500c0c0300900e90106080103100e240f8400c17181c1040c07104205030700700c0c030030f449031000704d15101001003001b0ad00880469041c0040c0807103c0c00608090004141402030203110300041d4a02041c1010042809104030401d0920718401890b80502d81603404003085880903a001c2e0700d9008078244c1066498104800303003107a03000030f1003210311655403101d18000e41095844600058842994a0302720900c0c0c001c028032076400409401206880404200c06007429030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 873985863 1250 873984613 873984673
    0x303050a050d060f0911130b03060103200703030e0607080a05060127031101170f090a080703091a040b1602011803080306121612110406080319020f 65
    0x4035070208048280115001000100051440c1500b0300000c1c0c01580e00c800346c5402c155405004c000c06e210b4004202104549050700c010355281c4071000100c02400d804515580303200d501030b81c03441d80400c0e040024911203010780c1c1d00b0481d002c41c4980141c0ca6001c1500d2500014607413602142c91074401c0d038083e0360410014144032794079103502020b844002901414201c8100c4002c0c1c1d041040c003a2607000d0105240c024a000d50502c664010b03010b4040c400503109030300300c034140c100040100f0000c020950380d4540010071180c40c0c02c01854010107000e118083c0b00c6880103002c3d100c0c10143c24060594044d103c407241c0740740c20704107107010f40c2d5905108203070160304003c2041c2210b41c4a04980002130043d600036580e40350369282076418881619081940c0900d40c4e40601c8480c1100031030300b90f441c0184d1311802845401551241441d80c035203103003c1e40c525401850050300064030f160000090400d07850600e5010075654000c0010303a11007038503501034009034103c4982c00355029602020380700040804 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 873987113 1250 873985863 873985867
    0x3030f091509110f01050706180215030103030e031b011b0b010f050316050306010e1015110d1722060609020301080708070303020718090f0b1609030c0303050a05 71
    0x1d03100c2291912601201c1e03001203503210048010710201e0710300000c1c510025107410100420b2040000c00905c00c1d1080a403515680b02d00030a4410064600e41405540041110002101c01004500396902c2032000310040340201d00b110400d400c0105401e00810310802032259490002001900c0c102d0540c500282c0c0205194071000004003000b0038075001e000500c00700c01590341050289450604640c8404c2007140820000b000241e900107089410340b0301600ca03a00d410f0721145184c01800e14070381c011005c42000d020200c4103840e07200352001485240c08040302c10859885800f41c3d00000b00f150b4100c0ea02c2000f100041e03404907104074010304080c4149150340d02c031660b42c90b6030b821610316400400100f60008010800e4003810882000901700101c040d08403940b8641e07010f940c81c40c15100d17015142c038180c8032104400005900408455420181010101941d0304d41810b403400c04566004d020700180020703980b0188a06511781c1034903030104948058905540782500c841d04551266802c102007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 873988363 1250 873987113 873987131
    0x1031e08120a02041d04050303010311031c2307050706050a0e040e070e0c040b030720060f01061e020c060304020d0c15080f13030f180b1801050a0c03030f 68
    0x441e01e81d4621030100180700688580c14010b100651403082c440d4507001c01e03c0304050002040c4003004582c11242d10080c0c0d51020040c810110342401c201c44801c284031128418444000d58000c2301b5910321009000e04486011200c45a6006c40e01420001070b2507a4800201400141c2c081c0d002400c044416003881c45040c800d100018007520b904080904e00364000ea582000040e0b407001203070760441c411240240c105824204458400c1c000242584104a02c02080b01580200301000c2c0c0d406080240c10b03251139180c280700e40c01e050f0344288540c5000a60210340b42c8200281d2184401055280da40a8082170420f1020800315410203001aa445808005030200150b040181d800003482c2c0c2196000070301d486204041c0c00d42c02c2c011f2100c812a003c0350104007844070b003080c801203035650509111440c4040190100c03802c1e403280100780c240582101c00420030001e610003030702d80350240c0d15103d8109110b81c40111420b005450402001c954840b40e2100000d0098100043c5142d1081e00000c0d2694 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 873989613 1250 873988363 873988387
    0x1a04050c040f021c0e060c070519080403060f0e121920060717061c150f0e0c030705030a02030309060c03132d0e07050a030f1b0801090501031e08 64
    0xd90421302c68099540000e244009424058203502600701d0700164204005138032465100c4600304516240d40d00c030096454200030220060b40c01079030300201c0400800036050b4503840100081008903090f840b85244280034a00d41c901140d204800c050087c1254018800342076451442d41d20070b04a05488401c0f0400700d0100c1088004e104844503983d900c072241d08580d117050f004501610280c00b5441c80714156001400340c4072101640369000d001000c01d039888000410042c0326a10f000c08145081c50000301300e913007002820081c1e6110403001e6902d0940d40b4000c0581c1ca200341100250160014011171400c0d192500285c000c0721404401d072803a200320405c3c51500b441d05034004c41c0702c88030b00030a070744042140c80c10360a0718000481c541030512402c1140d072880c0101e0042c078450802c0300c00190115001d1103908920300003031000c01d040c421811010030100c01c44804d80900780c0040c2000000080410b007501441d812203800c601d050241034403000c1821164004500162040b4504100440c0342074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 873990863 1250 873989613 873989647
    0x15030b03030a020d140c07150c14061005190b090a080115090501050306040b04080a3e0610031b1d01080601050604140f0103090c09091a04050c040f02 66
    0x303140f58054860003030f50b0407010b03002030011562010001001c1c003403002081400101407050303d210901821200810184c215404aa865001402c0300c1080545290590000420764003078084001801b074501d40710780c00e000b40344101d605840d803c481081805c12011000c040102001b82c40500a8a0402e807a0b0b41c02500795010a184c0c81c1c44507114010401295030284901c6000d800101d000c0c00c03050030951070700c00351000090320140c46c410000850b001c0485c0510f03404840504205040c000c10040a00c2c054081c0744400d0520480000c036201e000e00b13074080491000e1088001003680200d950a5843d140001d4a10b102c14400d8504040d80c080b8425140c212041280c07a04400301011540c14528010305105069008500422080c8420721400c02010310410b402c0c4020b540420612904000407805410040707400b8290040506000c5a10300d1560882c01d005402421144e401c1052007a15001c48101114080c006407c0300749800800e2070a5004000303103507525800075080264107030505440f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 873992113 1250 873990863 873990877
    0x150405030304081c03090f060b040615020a0605071821080f1b03090609191511070807050604030b0702010b1f090e04080418021c020a032415030b0303 66
    0x1e0380b02190301d1480442081089001c95aa440c06102498051fa070302d50951581c00360081c1f8450311030700040c81c00d4070b8561021004040e44903d42d40030106010020707450710b0b1401000d41c0e0792170034140002c28503401005080104611816120840c40c83d000303940f81002150841004101141e0f800440401d03c000050000303007100c4602c43d039036100c6049100e50201d6401c24a00780030b410520074100140d6610041c1c500601040d61000b02c000d40e05403410b60000180d0f04114000d0f18002062241280c0c80798001c174603030701c00320210b030a03181c2c070b0b15005a030b2040f051285a502c41010001400080c2030f003400660004003500010030011030031000699040b5418001c600780013041d0b820303a1065a4820309010040909008040c4c160626480d80389151250f800350500300c581000f01481d001c03600f907040368841d4990b8035460385010b84902040011758009280b00000070b0820108400d10000d00200c04520603040c442406801d107020302860810b0042e07181c0800b4151303640c210407aa03403418801000c42e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 873993363 1250 873992113 873992129
    0x7031d10120908191205150d0f05010507090e01232808160914060d020a18050a0501060e01171b03130c06020604080a140904150302030f011a150405030304 68
    0x30f50440d184008114404100c01c42e81e406040c46d0034000340c1a0038030070059071000300340c82000c01806a03081608910103500c100400a40c40c0108001c0c0309580a214642901c00130162844580d82e9400401c00e00d2051015000224207554900600e1b842c081c40002c40d80464501d0a200c4c501034500c103110400c02d030f035109078001d401480d1180c06554542d0446c0005d13100e0f0601c10071a01d222898090115040180828010103040c1840419542c518060b40000c1c449200ca03070340c40101d00c00b05d0714060801074030310b629040c0c24503002085003800380d02c1c1d407600c2c1041030b990042d00d40c80c0c0701d5210510500161100000080e031121a01d000e10382d0400641c072076001003d2202c1e542c0c06a291400d400360f40f603031004046402c1101440700080e292412580140303d41c3c90f0013100e0035070844589845126441d01d055001d86011900b0f5482000b42c0350400c200c03030085003600d045402c9408114203851a90702d60011b0b0800c00c0303c50700c000c0c1c6002d4180354032107580075140381c0c2095181c0c4d02180c595800358100c414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 873994613 1250 873993363 873993397
    0x50d06060303020c03010e1f110309010f0605010c0f0b0a1e020c07050a030827121507030501060c140709090f1110050d021c020d0207031d10120908 65
    0x2082c550100564500380c03005030003c00ca0164420582a160b6401501c000b403801821003400c641c02c100b075044640540d20b030700c0d1003960341c0c10030840803402891400700d94480141010000501c03980614001c1c1c050641101249000e00c8080e960b074100d40000411280503955140c24900c0c01c5001100d4041c5109004200142d9a0701002c00e00ca191903003a520191055000701014000500c07141c00782c50305104111000545000f47e01003100740010b9552610f50883c1000040e8600718500080b40c400ac81308500a0500f02e80320341074114140d038401d00aa202040e00c4131400d20004038001d02d501d900c400c8171001d0301e200075110300c1c4031000c1c4c0381900300680d001c2c1c288440c010144030088103a44040a0100c1e500741010170704031005842030044601000c102903001c10080c043d28500d0810104104180c0c034119a144000751178000290000c240a400148580c41d110010a00d000704038803041d140100403038054044610101d0b2108140c9000107040e9032142d5205000032404030103002446540e000101d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 873995863 1250 873994613 873994619
    0x5070b1309090201050a0809030904110a11010e0c061606060905220f0f062c0c010503060f09060a0e0a02180f0a0303032007061b1806050310050d0606 66
    0x8621109a820503801c541c0360030340c500b0043c0c1c1c01100f01c0303070700990505100f88030b40d0b21103640500b140507200780075412900b040c111041265045004044444040d00c0f15070b103a0f118400c01c1801c0791505004441c4552000303401c98403916005000e00a0030134002400c4064040031741d6040c0a840d4282d0040a05a46680510040d100110312490341d40c800d04040c010a5502c0f030300d0f84200100d035410080c05002c400308115040c4820b58208000c035810720074001010207201d0940d400070b51180c51402d0464000e0a03501c2c401d81d03219008481c01644d0040c00c040c1205202c1c1c040004158001e8102e540c007c0c41060300203200002e04050901c100c40c040750041c0c6454004001c0c040241c82202818412840001c440240d651501c0020341629054600040c10841d502412507481e0408002c1c1080080b0101e25034041101980029004407a01000f8805031141c5090959416425092600c0701410001052104610031005558014200015200c0755503558021512680b01c2d030384240c80382a1200d07800c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 873997113 1250 873995863 873995887
    0xf050103060c1706091b03070c0b090c060f0f0c120408010612020d060b130908030a0e060c0403030f02241b0310270606110f030307050f0a030905070b 66
    0x10524149150521241e00444141c82c090b20718002004d00e44220038050100302d00307040203254015a124030300081da50301c0c201584040c140d4801104200c034201641000905410340c0824407894011002c1e008038201364610980303240e0f54000d08414004000103000c0c03c1103d850400810500c020945841952141083e64031400e40d400b0760000c7e6517011410308410010b8440c2c1920080c210313001400001c035000c140c000680b9024028020b004080e040031015024880354600440c010041c1c0d1004224004d1030f5462280c86d02001c07205414060310601080010900448040006048500c1505c080741c030480102c03442c090628074046080f103914001c00040d04246407013a0a45100c10403464214502409072041e030154500070b0005000c170b901c030301c50041c00c00c1c07403411504810540c0062000580b41c500042c15420f400031401c60768031a66481d42c850800c0402224000c51081d03841d1b0746081c0008080040c60383c0103010940400d9030344c24052020400030301c010700180c2030a0f109540d682c00d00b03500d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 873998363 1250 873997113 873997121
    0x515010905070f080604090609061d100e0c010c0c080303190e061b0c01090618050615181f1e0f0e06010e180f0106120b010f18090f05010306 62
    0x500140240d00e4045480f943c0c02031500395005000b00d40208440440386040800340c0042030004045a00700500f1409103000201c5075101b4541074000c0303501d903418600703040059490140030b80e8159007001480c48041e51041c1601d0102d14020f881d011412540c40c810145940d0084401440c044101c0b01d055a9104190080700c1c910100100102014200324801002d24911481422142000000e950b01c0d003040a41200c000180c00c40d000f0001e4410340c4c3d04225040e00d203100c0c03c40781070244000180100c01081c61003110904050303c189503c0041c0341103a070407000050056450f10904400320000e818524141c54042c080310b440039914034406145584041032160003030291aa03812000340200c00798030f1040750b8041000d11340603442d010304801091005d84040341c00b250070b0959404014920852804050407a034581d51562032030344600c0025400c8a2502c9507940c002802c4150040e5070b14031440c0c507040e88510308400e034045655a48600821180c001000038400c0b40c40c0e500400c20b20000d441 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 873999613 1250 873998363 873998371
    0x6020d0605040b0a0501031a03060103050309151602090c0409050907170d1202090d140d1d030c2b05070314070803041a070b0703090b01090209030304120f0515010905 73
    0x2d4140714071141100010030141c801d000342410165607031059111000703041d00e41340d150b80e000340c00d5603201d503140e080c4280c8940c44582140d0080c80186c801800c040081011114514280542e02040c840c2c2c0d942001540440608104041d103800d20020801c00078074441c1c00d001c2d070203004c0240745440c640898154401c0c02c00c0740c124000c0e00048045144150010352a14a01a14902c01030b0343d94005400289450401400a00312078950400c07000842400070f2000e8160040b9120318030301003000754121585180500203503400da0071000b0550018184206005000035142c51099008503400300c00c183e0390079050b40d0665181d44118002c10910000000c00b803040003044028005140c2020801a5244210300c100131072414120b690040d1030181000741c03148240e014601d544903043c01c08004004c0d1503030010039120f02010f81e000140d811183d108035081101d000e03003d141000d10b4259045080d070450781041c0c0d110003801802030001032091001c9440c05822074001e0409506100c1c08000701d81c0014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 874000863 1250 873999613 873999619
    0x1030204050105071103070f031a06030318041808030c070b0109111b03040f140906120c0103090c080303090d020f211b060a0e190f0803060a0b030406020d0605 70
    0x18095a40d000f011542400d8203c00000c94141a2802091404c2030f582e00c0651903408440021003000305070103c0c0c182030780e070000d081082030321000d04142e1680b04800b48115031400c80e1130540c0907414141c000c45090b081d4404003401906840c0c640b0721071a8402c45003003d800d400002c8500402440f02502c0340901a003001c100241c18a0000015070340c41804150362900412411150083c00c04104690260110b015040c031441d503900d694444c0f1075040d241441c4100f0401000030340c0d50070418101105081d03d10300815481c0014030042d4000c088684041c0e8021108500100da1500104000d60044818030f000740005000e041c00241800751240d4a80d0240e00300001080401d02c20180442d01e24450580301603070741c840461080c44020070081101150f00801d010040c060415a1001080e102e000040ea88118060340766682c00c201185401021013014018040102c0e56210185610070009491245c0107601e80f007581426420840f0101c407529000180300181d10392a00031600105419 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 874002113 1250 874000863 874000867
    0x170a06050307060311040b0304170d09060608060601140c0c031e060f1003150e010f1a03031201090506012007052b02090402010e0d03320a110304091d010b010302 71
    0x17101c0f07040385202c1d07882001003600303000c0041010703c0615401c02030180c41e4110810341d101140514130014241180e41603130748601e000f00014500030080f9126100304016920303950007076400c138840c2d159508000703200321079485440384140c420b440801505403003200044070f03940035080b55401307140341400c014203201300d45030a101031040a002040038041501d9110b80e20140720710400c1c0d524070061011486406007503081001c80444240c0d154803c4080c003e80000d04604040d8001c2803668a109074180780200c41708040041056212a510445c2c00400c145000c803484103210305030414480e21290f059503140c0080004216615000e10341c8840010308803003101a10304801d4001d801c0821020029001d1035011000608580c031902c062184c4140080c00c0300d11010301406e0003810341c0700e05104c00c004c0c44101c2845075040c090f42100701c194003040044451504c1150541126200c03054001b0051500c024400070510b0915030281e41c5a803c2c0c01c80e032407008003030311a140c1829220041c000034181881 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 874003363 1250 874002113 874002131
    0x1509030f0409050a0207080f0903070e090312040809101d01020703030c0b0403030e010608030715020301030c0519030803010b0a031521080d020307051207140a030c170a060503070603 80
    0x10810784003180c04101000900e035848040e850b01a1040c2e030310041445400040c1000071200410180072041c60a4080380e049603242c0104807207158082e01c0b248039640c41402110070713841e510582158054440d189250524425002003107a24002c3c641403030209600080701411840960300b542c1550400344000c1080034555200940000740000700a0500801ca000140500d03029802020860728040020044180d80b6241c0c3c1d510780d00000011941d681200301d00440108490094905980e01702c400103000c40c0c50318080000404004840340300c007824010001020654400c00386000741001c086040c0d603171944400c02801ca60441c0d0310081e131000c80d1f02c070900c090b4032215580101240d108003466800c40c40d43c100550b15005200c000f21185000000b0808140d0b8008003401210741840c10201d000d84030160251202d510600103501d00f543c2c18094101924030941000031882c03264203001d012a10314146c0d51001311021104010a0f5440d000208540d0a0400600000301401d140800100311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 874004613 1250 874003363 874003387
    0x909060b030607081306020f1303060e010b0906100c1506030b070e0402180f180a06030c1d060603070e03010e2b0e10051c0e01050c07022d0a0305150903 67
    0x10305111701406155000c20000780705203245080341e200624000c2c4e40d00400e035580c5050805801c10140000b599401c0810801d540e080111a050240800810107049503d420008640d800f4010805662944481c011000c031140e0704c0c869030001d140690480003640c54210070140c100b2800000c081c1c0200d20420031a041030211820120400408441d0110342668100000b800f010444d0302030035049002c0810b10901d402c00354001c10840744a886d114000315520841403003072203600b148208140301ca00d000140146080c2d001154801030f5800d0034080840b140700440d085a44402495801ea0701072410700311100030b001040001d142c150308002c44440c020250040208080140c42c83c040c83e400c4102c4480c03c3d000b01d040d03d8505464058000030100390103140c002904640c8041c2c0c0565180c41c0200c0e442000600440e0300ca141c010b0811503884070313850283c2d03c1d481c40407100104c0050703444003d000c1965500c4031a81c002c5000c1c1c0300030320f100c1c200d044600250786005060141c0070707842040380b814001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 874005863 1250 874004613 874004641
    0xd0b011d04051005060112021810020c0d06180b0a1d0c0307050111100c12060801050c040311030106081b010e09011a03180a0c1e030215130909060b03060708 69
    0x7010f004004256a2980740043e01d800c02c400c0c42c21080540003003090001ea4140015005540004444800f017058a1a8043e40c41b2041d891020f9001a07141002c030700440e40c1600300e205c95a0882104c08804800e03a22150f0302044c05895602c600c41e02e440b001d0481c040c0c9900035001c411018409400340d20146000030755610303068401c01e0705010040042410030f12041c0f00070303000d40841540c10b01c0360a190b07490040c0146811040d110000740f4103079020036421814411280b0442401000916003411038544103099201400b2441c4d2640d01c03403802080220b03081c003514601c0c810386a80d05013010888400540106080c2a141d80100c10405c0100508000b1503004451031030500340c0c4c61782d84e441c1d400902c881003810b0304600c4424440d02d401307002001803940a600403a00407101a038001044c40c205000141e41c1444040c0d400ba10503a8551000f00e0031000030844080f030290304440c02c69582c440320b0f0944a0b1458166000c2d6640c0d0b42e03107900c07402d003031084a600c00c02d5031400c0c603914581400a01030750 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 874007113 1250 874005863 874005883
    0x9041a0c04080a082a0717100603060c12050f010e060d0f0503130905150114121302010305070305190b03101103040204060807150e01090e09070f050102121806090d0b011d0405 77
    0x4010b6003501413140d41fa040c8040801158089421310086da03d0b4103112001c0c02c0c4091007031001810301049480ba040d828480c070380c011089007248140507480c024100c88080006408a54030003440b142e018005000b00510911072449030002e580c54050801440c0030503802c540c8900ca07803138145020080219092601c070341c1030041c24201948401e907a508000c0590007105111080a000c00d02409195900c3d400c5044a46100f41d805100d1580e4801044043d28825660515541015040b221201d080b68100d0212b5802c0034040340c21a0914036064402d56a07845901191f0b41c40000600003075083c140906805813011800030320744580b5201c050844690f100300c1c1001002550b00d400c0c1e200e0380c070807803e81004010b250080180c1e41400f00190351110414440c1c00e01100540c000081c3e03950010412240007000740d002e50b402c0c11a01d90000107040d41b2044000d610410400c00217415545031105410605c0c0165a19619581841c0c180384a54800945400441803100c0c04c0100207076000410001c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 874008363 1250 874007113 874007129
    0x903062e06120c0507230c2b080c0709061a0c0307030309060b0d032f0a022b14070f051302160b090c030c09041a0c04080a082a07 57
    0x1c6032110071400c461500610400420791164405209060386c01240b1000c142014030045d12061b007108000c01c00c00f00a000b44130b40340b2804402e40f50303175180b48040140743c0380e5004250301c074031305000c0408860502c2410f8109d1000250f0742c080c01c5c4041f0b001e4803240c04514805a11062400704174102c1e860703682c0035000c40141019107886a400030480583c21171410701c10003500c04e23070741152075240c0601034000c811004400714000400e00048000283d40f507c88034000007014004503640350b02880705141510407200ca00044180c542401029101d55545041d07000d411a20681a000ea04032410035640303900018489060a0040c022562a150a14a03010f01c1000046e500d90204594042c80301d4807500103009a880c1c0004c00405040214103400307140e2048003611f43d0b14a07941c0030480449130503500a880e5000441c898817444208124294110344001605800d00b5078440341589840403400040b204100007261200040602c0fa80030600c035182071111082c032099030034031281e0f600c890744200c0352 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 874009613 1250 874008363 874008371
    0xf090613060603021503070806030615010f03020909010b07290114011e1d060708030a050718030f06050c070f060515180709060c03020c090c0903062e0612 68
    0x81009881d030300c04802968040d015001c510141c01708a9000d4204403581380215113041e000880038a404039500b03200f05441254904890b003408011a0f20040c8000710006050b03081006800c1580c81d0b4140b640205035465965690740741c0c40c5014020040e4442040340900051a04401001c04212019054403100b00d04507040d001d111004940010611080c540000c4498500c41041940020750025004551a44400116040303040c40182c1c801d4110141040e2001d0001c10341e44e102c40e4000c85d40011285c9021071003e0301240c68540420b480303500454000619124003010401140681a0300c685400e51060800009443e241400009258001d00307442d40c40d00003859a0b014a620402d1300d90014004030b82e646140035888043c2e207410749815020400001d00001c1035846005c5040074550305601806181c2c1501e4244214143c010b000d82c2c090a00500c01001c446c0c40420400348140500114455000c04038101800a401c0301a640c0008120816040c8001600101001c1c2d00d1034845900203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 874010863 1250 874009613 874009651
    0xb1e040e07081b0c0d200604021e09070c02030c010804020f19080708074401060905040f030e0303040602030a050904020906070c090c0306050d02010f12051303080f0906 74
    0xf09400f168000d0001c0c01090208140da09484000384505115800d9203456130000100607080c0c031400040c00503000e441d0700550005005081029100d0102d40f501d03030008611203516030001c1d4805c5011a00500003c011529040561504101c484c80e07805003820312503424181b50300461140c41920349098003514507a0b01d400e5400041c00c1c007a4000f440400e050b2800d050300c1d031007181d46400040c42403500e4144003010f201420b80700e28248401a204400c200720130240ca48210b801d030805802c403c030342a9581c40400094000d007a0050500c518419140d001ca034240d02d01c4c014208414615441d40079038400d010030711599400004403031801541c0d0400c561510503140015000c0d201d140307034840e0040e00220303802d820800480c0d01001a80c03030320f003014080505103d004504403a450b208403548044400004000355000e2940c0340e640c0c1440d0301e800c50b0382210107035030601903d4007920107102a084207040300051683c40850182c01440406c445000d600300120816030791180a0500c01c5020440e640d89 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 874012113 1250 874010863 874010881
    0x10b04050a0b1803010606050a020640291b0f0c070314010603031b032015041518080d2c06060f010e030619020409060b1e040e0708 58
    0x450f180c180100240442034039824010324607003104074a0000361040c2004110140d0b800b000c5103041812243da170007074405541e58001144108030441c106120180c00c0100003046078032216240c0d645407682890035560424156a03c207903c0205044901d42c1007000705000050702c0401c8036002280d9544150b2074017900d803081814080d15170700007001031824021070300700d000064101390100c03806a01c5030141310100400c1c0040c62080480000e00203007003d000000c0700030243c03089000d10344205084603d903110004024045c1401a241900c144103034010400d10340030b441c02418580020342c000c18900100d25654080305002e0216000c07400394603030f00f588100d000b0102d01c0d42990703852005040046520b0622032522640150f66890190000e5034403103c603540246401401244050001d0803150358623960740c0b035044800c1c60417500c03042c0c0800000414107150300030740000e089861141980c81c441c0340120f45050079400390011603400c0c14001003201504018450350f02604504241354295190420 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 874013363 1250 874012113 874012147
    0xd30050a020d1202210a1506020c0d030311070c140f0d0210170403090905011d041203150e1005010e1509010507020604140a06050c101d0106060f08010b04050a0b 71
    0x5a150701c039045284216414414112960081020100c07c0001215014000f14810304501030032002d680000007403500c031304100204401840c003900d0001031140a2517000350040e800503006456415010805001840c40c807080580280350850b100c11035020002c011803010156514040d00c035100c48958000d4550142c0340e05401032860081c0c00b040c40c5820b24024103056014050b10a840d0301d45800800e620015031441c100e108044500f1420700d548a50f0707101840010b0106200401d502d0b94501c0d2135422010a40b0343c0500780d480ba4060b42e40c07408003024610307035117283c0c0003604100803d8070701070340d903102c900008102c251600d00d11650b500c00e00005036402c0c414140c00039004000010001000400800343d4444100c04072170741c00c0f905075035000c01c440030700420405010682110b090544401c80c81d85c041c94152800c04000001000032607034050845544c1d5200d000803c8041d0315001c9403a0b802848540509103007082a8107281c2040e01142c1c0410160258091700c0d82c0010b07428081042d5501c2c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 874014613 1250 874013363 874013377
    0x1062f0109080a0c0b2d060a05090a061d0103031e021216020103140709150908100204051f020309150909010f050102010f0203040f0803060d30050a020d1202 69
    0x410a030f5a040c010400402038403040500365440c240130400f107584080c454042c4004500485110b0080601c0740c0000007101c0006008154044040c1d0030014145c0ca40c4240e051050301503480000350300e4900b400e851141394030380d81c0071021144824010b00000b9004103118550071034480560b400ca4450020903490211110341d0315081d883c020a00c03403035041c5039a00e0710b40418402c0c0e80500c10207000c22105803500b0010303208000481c03510704090050b003064a02442c04039880b4640044103580d50070740da0341041c504001180096400060030f0196062204c400d07150f5603415200008500c0784004020345034015022054030035884440105020810381084d00c104110041c000c0140d541d690030780ca9441400d62040324059402c000010144080e18030960b481680c0140242c41e50316400c0c0d42d4181d943d800100156400301428040c01c0106405071489100b500215004140c5402203941309440c414006020342c08000f0104003008540c1c1c0e01084829100c0b8460030310810078190742001c4006805941 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 874015863 1250 874014613 874014623
    0x2112010b070303140f0f09012003040c050d0314030612011a030d05071e08120403030606120509030a0e0f04020a0207050a05030102070b15130903080f01062f0109 71
    0x8984045104010401c0c140b081c0c07800c010340701c00300c000030f0381356201201e0500806456200260000260b01c90807640448214000203040726561001003181e00c41c9981610001c0000c020001001a0071807017401505040b16480e05a090079a801800d80413041040d13810b81002002060150321844200401100400024002c08078410580b441c1003890084241c400d00c0350010300560140070750203d4031080c1d0045c0c226130340a10300b50303202c0c0c2009031820021501110308102802c0d100b0003104a980c0545e02c079580c0030819500d418801824465a4540003a00f140f804081c0410700030000221050204642010081c1c1d90354080080c0740b01c200040d0700d581181c0000790941c80d42d90302045002c20750394100d40f51044591510113041c01c0b405401002000c05c0310410109407003503c03c201c490f5120400034501814150003c0f40c0100b80d40c800301040340400c0340c200030702514611021415001d440d00385450710201c00010144c01c03119420703000891102c0c02e42c280c2c00300c801d00e080d0001c03c0015000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 874017113 1250 874015863 874015897
    0xc2c04060e2a0306010f052101080f101404020f0a05060a020304181a1e06070c030302010b0f1c0c0e010608040c081207060f020c01050c1908040521 65
    0x2000c5a01000402d03180c80b031a1111442401c03900800c1e29070030740f801004103a441c18a450b610820564841e80800d8101440c103000c19044c0f040040b51a17a61800380001101a0510f030703009001141c0713040c40010350b0741c40090a005041c41c4d40e00b02050030590154044907030400da0820400070070034005071a0003240d0441d0700000c900c04a650004004c00480340015202d80b28062209107000c21204082e0904018107001d040c4610145440003001080c255541810030f140c541d520002403041c0d06c002012a0a41500d2000300145602842400703040701082d91039944548409002842d288009030a00380c0e1340c555210844140040518513001405c0005490340711544c41d010041d00e2000d085400703d40b603c020080100e0480320114142040d2505034a505052100990320320000e04000c007085248190700b4050f1050355102400368034024180c42c942c6540c1d405141010440c60380020049a0074440101d0501c00040c1000940c0000c0c6403030b003c24100c054003880030720101c6d442804801c440b1103502c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 874018363 1250 874017113 874017121
    0xa031d0304050a0e09060a02030702190605040b010501081b0307050c15090d050a050405100309060f14090a080405041a030f0601060f1e0c05240105040c2c04060e 71
    0x30050003501c4088600240b800c0c2c1d2141420b031071240c2120f00119540061000c20440c0950ba000f558100d038090050316a040c0d500510301460500c1520159801510ba00c103020500200002c4240500800e1030400b005107880c0c1009025141d043d41004580c1000100251038184520150303021000258281c402c41038180030030519040040c1c0320030003140102c200e01d0141c40d026104807070300307483d075615441d007854600000c00458242441c8a601415100c0c050900003800911450a6404550f00d00107071032600100d45c036014400040c00488a0703406030140f90040380f0400300351400c4030300c00c44000c6400205026422055440c60007125094814010040146000415000d050303030800e17a103103500e55031002d01c1194400320410b404c04031070b84104502e030340180c442c0e1803905e079a0740120102d914450610781c992028034103480d0140c240b5a601030042c041c070314082c091088103510616000000c0c1000a1202c006c140c0140d50f500030f0310403411035170b180640f40c40c2c128500a180c0c0c0c11034901c40d458 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 874019613 1250 874018363 874018421
    0x306170a0f0615090209130207050d030b270a0e0c0d110d0507030c0311040902011b02040621110d0b01210f0305120f04030e010c110a060215090a0b0c0a03 68
    0x10140700309108140047c6420780da246035100791142290080e00406041160003000d80040c1026404030b42c01440d0140b0151004c0c03c0070440c50400d400801786d0b03098a00d407440301da000b151084c000c025900c1d080b10001d14007a40c0c91080c1b54100c550441c1c070740e0001e0007459000592400030130758014100e000701030f400020300c85070381c1d01501124001c0307283d44d80d000707118010401204d00740d4800a010940a030078041d0780c02890034038000080d20107400040e505440b47d04400c0e502e41140030314100705a00d5484101006020395203041401c0701900d054041041c02c3d5540f21008505002e0082c01d1b0362100c6090764402582000d014034603400081c0410301c204141002040340d803003058540350100d903c038003090800b0561080144a5038040e41c804e560310b009a0011150545003c5003601d04403880030550f926542d800d00b8100c01850550020160309a403280303920265007000b801c1c007482c1e800440804011500b848030031507020074041da102d030340d408100d1030540061061004074078070071164a0b00450108 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 874020863 1250 874019613 874019617
    0x3030f073f090f1502160b19020f07030b0105120715050a140a05070b010b0c070e150405130201081e070507020a09051005031b0d0b1e040b01060306170a0f06150902 72
    0x110313140c0d00f42d4215062008206d01218154400c0d0b118402c010040380012a0552800b140020300500c1503401c1e4040e4100d0300340c50310750250010f840858440004021078605055820710b0b0b09451000740010614107030381111424802030380c007001d0010004000c50480d204840c41310900d0241a0000d485482c0004004c0c4540c10150040b034034900881e0011940c2040356060341c50084d03050004115140c1000094090054040c02e00740100c117100404044e0307a950b07401160711076030000d00429041880d50000502d071107005001c100481400200c4201504026200f1076030104450620580d01d11461001c21060f035140c0d800b0311402881d10050184940103e9000c40840b107044088a500e1950343c0c2404e040041d1801c000391380305400c42001000a41010b51311984241a15a8070b80c4400c20400891408101168115201100d407001400b2158151140c0000f810340b040b150400f08502c600100d13625a0f200da00940400d200b40e00c402d041082c903410004030700010700e4100c110180d441204902035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 874022113 1250 874020863 874020899
    0x7080406110105070504030b04030f0302132c1015020715210b0d0303050408070506160908060c030402090a06170c1e0a0308070f0203030f073f090f 65
    0x6500f098085110503200300180e5040c0c03070300300320710220b203480b00e5030183ca200405142c644240340d000c0c8801180350380c29070141001041020501d10713032041c118102d58a01d85c1d16080f0b20596082c0c820600c44070604144007038054039581ca604106100c000301060f0301d800c1f2141e00c1060700004021402d11403a5101410341e02800000c9080d01c907903810041d419094810340200745401800328820400801c0c8079811161308a4040e201e420301d04140398440c0f50070444111601100f404600481c8581c00380d1119017003005001c0640601514140b481c0c000300b0074840604003900c02c0003000c001c10b0903800c6643c04a0002c014407003e990101d010152555110500381c1c8200d48113011101071005a02008640c000c59403800601c905042415559000781c81d412201e0b0a403140601c1c21110001a1400c000030605080c44402440d04e80ca5913241c0303003130322089041000001e48032030800b00041401a2146120010300c140c21190200004101110300d24900d9000461215205400088183c0c1c0daa20342290 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 874023363 1250 874022113 874022147
    0x80d1407020d0f030e2b02040b090a140a05040c0501080c0909010807060f210c020a0501090f020a050d0f02010f111606020d090b040501030902181602011802031e0307080406 76
    0x100b011740380200400c0d500e06c41010710b126000c8044580e080c1030721034540c81d691032009200207810680e00020560105040340e10201140da100c0354012201d4052142550241c0c003024240418035203a0303100d02003440c652059a05000d04007010a281c5610303d02034444010000d040c0e0800c2d9a9103100350381c0c1d64800e0b84a440b01113040440c0701000e241c460415005042840030034242e0f0705101041d004010101c43caa042d04500607948440c00140c000c1c0103900321700d4041c400100c1000c4260040003030079891640b101d481000c650302100700081c800355004050070b809081c402c0b08541c450f80c09440e08409842d0440f81f40c0201408118404d68800c88141555101e50071500b84800301041503c804465009403441400c09220400c1558482c0e041b05242e14070260061000a90861100010003416541080d030740e01101000280c00381e09120700216846031207182c9002c000aa000710340c0b030b03209600e50489001c55080682842040400840b0310169100c0d0149a03a1561071100425000c02d070105614 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 874024613 1250 874023363 874023377
    0x2040b040f051b0723070815010305120412060e030c07030b15191503020f0406031a0910120f020d0b1f0302150903071814010906080d1407020d0f03 65
    0x140000f82100b42c815150b44501d200380c2e2841440040350b10341021802e1a03e16201d011000f24407030a086c0309880700280d01e42548400b0b54114a001410030a0440707202248040910040108401c0084040c1c075841e000200007581b0422101345078114854104a24100d01c0b600000100300f10203075480c0ca2203403082c01240041140c804003000840d082c580c100c1944111084000e0041c1c40024007080d144800c9400c00501d01114080803c1140d082540031074042540c8451109030b48000c190500b4010000b01c5440c5103903d02428401c0251045000c0c0c0015010000d40080030814044c2c0120092a0024061070503002146040d8620650480d900d699420501050a6003e54600b0101c0140c90b801028048030103015011607070305400010034141d01d44101607001481c5451250006843c0c115103e000c185000c0c8106007126101041c2d00001d0043c0c50700c003040283c410003246004035072400d454440c04081c070104009003030380203a40b0040d5201c040950144100f2000040c034466181c4642c441d20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 874025863 1250 874024613 874024651
    0x20d20090c040605040303180e07110124151704080714060f0f0403170108011a091e062101060e1f030201110f0703080c120703170402040b040f05 64
    0xc1141c05a407050801041c1c01703100c2030001a019000510380c03a05855020103e40b9621540680c032540140c1d07542012848014003050380010030301500391004048103044030700c440080340301103810300c1070701c5136088041410155240584c070610900b000d06810006c85000c0e81098107241025034840754007280c6a02401c00c0e0b05450f52000b00d10303140b05054481001c03255035030700100000e2025000300200c0812801442c0901205401c4900e54064100c04c1c00005540d80f12041d80c01070012821280d9100b082c81104020224403070a840501849480e142c1c40d03020380b02d503c040340d130042e5070b90000711950200403921600e0000550284084401c44101d278003041c0c46e282b0318817071044458003520b03101c00500d840034400f5500a4040803101e203d403800711060b5a000c1c20340700c1e0820345141c20445003184005801030203204200824186803104082c0c15203030461a540141180e6240640b0741c0f0043c80950020b819940da561042c21300c0680504103000085c9101d4810008020843d2400310310140c101c224 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 874027113 1250 874025863 874025881
    0x1d1e150c16240c0c050915011b0b130809030601030f020a0609181d1b101107030b070c06060602010c020115140f061909030b010602060c0a0804020d2009 67
    0x39080000001c40000309049041c100700c80740003e60206503004034002500180c03a4549000061007030300d00404100e0007610030f0b0001880c0380c007881001310b01d2151040b103500104841300aa65004010440d141c8010f4140b4900440c580c001c4104299060190380e00000c14881c0c4c00d0443c404082c42110181215a00c81205a4214100e40101030141442d03841d00c1c0c01c8145c0c181d104a10041c0c80504800510012240d01454030011001034500303a4101c200c811241e041c61961481c9001c0b060400c8411b0058002c456036841126100c00791002000d600800d6506009400107141d590300108c00b4001980c03945000f0703002e0405081d00030010343c42c0c09080c8100c141b102c10024169500d40f5004000c8102080070484100700a01d40d4907404101004102c2d407600e00e81c06400c0b220106901c401050601d141012002c0c818160f02450964000004020150011000b21841c90030141040101034480d400843c0d8080301160700213103441c0030802d6165171a0007000d41141018401c130f0b444c3e082c9546500c8070b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 874028363 1250 874027113 874027139
    0x30901110406050d1a09011202030f060108030a050a0e0303030c0304150903051603051c06051509100f121113120b01060f0516121d1e150c16 62
    0x144a00065003841691103130303456074000503454070581c0c0b00b00410f1000c900000309042003c0c1e00211540300e81c0000d980450a090008403210002480980306541c035120b682500c0340710f142032441c02c200001403a644142d014440484180c1c002804403622458603140b132a04550043d1015110080c29685090242c84c450041c00c0340154965542c60403d200c082c00d040d140200080d04400b441428040c49001500e51340c1000c940c1c0303180c4a13000c03a045181c4000d1082060341e0000456628a0230443c406c02500c403884c071203000b11141d14206100501d12002103503410825900544458240f042951580300d44030042c104000c1ea120902c504cc50744c8900144031040741000051880ba90b940c0104030250240440d200104201d00b481442c02c04078603080792843c404030b0342c11200c1c460000100b81082c1c1d4070042d044042801c20400055202401002407a0240c28210344482a0028441c0c4405515000141e141c080d588c240016114084116015100c500300030740804c03846210080010728000c0900 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 874029613 1250 874028363 874028369
    0xa15090b060907201e010204170622080d05100f060905010815041b05130603090807022e0e030d0819090201261f06090b180409080309011104 62
    0x135055030f00d50103010740020001c5004604000750040d103c0ca0001c40d850f0303025981d140c410300303070005a603a810841c107a100c46d120204004016402001000741c3c03218100f08078211204140c1144040c4502031610380000d1107000380c1c64510500742014030120f0f074660a200000d51b0fa03c041840106038035140201c2d00e40d007040c031030725002501150104e100d940d0840300085d02c41002900104e040303554485405005140d010106000403030005d55902c10200400d0840040c5c001840c1c00e11115105132126800ca000380c80003e4800ea0134014640d80c4000c044851800f000c40002500034026040d0f0009410301c403c4030742d103500034010500c507070000d00d00c18190ba0380f043d6007151340d41c0c1c00941007a065000922143d03100b28140b11606402c242e400c12a0000d84000000e400246a91460300c0c240003180c449052079015800d01c0c4100040c004550044015020f803410b046585446084126040716403442d52240765401c2031802c1c1d10041400f5000000b5449000403900a00100549160385541481584 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 874030863 1250 874029613 874029617
    0x60e100e030d0509010e0307080a03050a0c090312031e0c030b040b06040e070207030501050109050916060e060a05130303080402100f1b02032d1b060f09030a15090b060907 75
    0x1c0284103142c40b5520070b42d040540a000014060728001640f49075070302c668000c0c0e40e0680040340c0c20022583c94011030b6400040c103e42400309007480c0c1c00240110401e400f00420170001011207000c41446139100d02040e1004051202c10800b101001d64010304440d81420700290412800d405241800e001c3c69100c10702c041d15a07407401c2c0c40c00c1d03110f141c3c40d00050192400c5008045001020a0090292074046c0c048424002984d041c60803035949489603030218403081c1215020204001604201e4040490340103030340069403940300d0300b0103c0d101d1003107850700c9150b052070f0500801070581c08481548100c2c401d43c0c142d0300c880d02001e826540c0d03034080816280060800784406140f2030084d00c0f840f00030703413010301111445072640c14941c061640d080910509100701e1102c1d03c94000d02041540f82c0d03080c6070798245440b1207441c0003080142c440e05008003108007000400303902c241c074200083e01e001604904100d100a44003540395001c0c1941500581b0500ca01d5000704030103240080c1c0035801a440d81d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 874032113 1250 874030863 874030867
    0x1060f090621230d020309040e0c03060103120905030106030605100b18010c030509040525050a020c0910180c0305010e071d0f0a0b04172e0f09060e100e03 68
    0x2603581c0e08528a101c0b80000e40d40e8418042c02c60804020003208130004400d4010310b840701400c505200840c3c0004141100030303401382c0030030011070303c0100f00d59054130b80000c00c180d07112040b01026282085070ba480729416618208000007032010651119018400010104c20140d0392030031080c116010f9207200003d06074041030804c080b90700a06011120510034188141031402400c0050200d520444041002c000b40c800c9481f00705588030051514102d00e41810343c103052203440001c0d50b440311075015a0192940501156240014061000082110065800d203001880c103c174406080742480103000f00382807200214000c0d044612141c03040100da900c0c000024890401080410341c50031007560400e68025208880f512900c09000241108140f803554aa103021001c2406460740000315081783c000501642e400a101d020409c020700110040c080c8400300c0850000080c00b03c0d0025060b59803400036240c0804c00c81c0c0c1c1082d0024890398007a80c100000c0b41000b9002c0d43c0010b045c003e525001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 874033363 1250 874032113 874032179
    0xf010504090c020709060323010203090c0405190c02030a180308032a1b0618060f0a0e010f0b031504050d0516080a1715031905030c01060f0906 63
    0x40c540c002d0185500c1881103481d4541e0f26a103580450303210f034005441c215500a126101c0070100e50030111381c01282d80c021482c0d0700e02520681d84174074008281c14800c0b5115000b0469465800d805204403a1181e4020440c240282c00081c0d96907002c512118041040c52440c40025806c0402010880c2d4000e40d1543c99681d56210b49002014842141e0b030101240315403000c1880e403850045d111000504005120900e15203d50900d40030006001ea4030380155148601503001002c1402504840120390709540c9848010444000d000c80107007810156107040040000001150081d148000c0309030240d030902002c0f40b5142d0f291000c02c50b00601181e00c04803220302001c0c403400060004a841c8000443c2a5103190360f2800d0715417241c2c940c1d00003e40088086100801c10b940380c10f801c914244140c01c41903007480c0200b80c54403451400180844c0086041006010062044900480c0604000c21003a42c84502050030682d65000725503006144c0740022030720000440001403000320003154001e46600d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 874034613 1250 874033363 874033379
    0x15050706181b0b0a1b051e0c0d0213110f031003020916081801060e010807060e03060f060f1c0f140102041212030608030d0b04051006320a020303150f010504 69
    0x45241200c2e1008170100010320085241800300e25100001e40340305011116401c004035151164402c01d0710300c110b025800040050b580e400c02e00c290090494000300b034640c00c83c1100c11150086260600000d13800000308100c03c0c8089841030b06a9100300c80d043c19980340c03205812070260800d007500001c10728600100c0d890301c200007141d00f41c000e4000d00100b0b00e103890300c403182203480080c0c0c407042c0c46a0021a06000d400d03001041501c015506400405041c0b800084440c0e44200240c1041c3c010180d0355051041d5807182850032070a42070b44114440a2200745c40c2024250368508029922038904c10b0b05001d0740301c0107008031800c4030707204e5032110703400625034440c07030943d1044120240616a50700b40004207180e060024000d003040903080011801d01040620003940c0009010030426601c41009200e4150000001e5080c04480e8618144264444149030f445030719071000e44a0520010443c072000d16400401140320b28042c0c981c05010035600428000450f400079083d50224400740310510480fa = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 874035863 1250 874034613 874034627
    0x615030a02040506130f050603010c0c02012a0f05030a1814060d06150c1101030204030201050f030a0e010e0f07090905030f0d110706092a15050706181b0b0a 69
    0x1580060003245501752440b09201103602075481003050700e440f642008043c3c542071080d00c10074141400c120308056000e41c002894241c10180741d450201c41c00c55540800d6680350004c1240c25845840380e41e180d481420036656036045103100c9400980d14030300c400201ca48010100f000c684000210510b070f41d00c1c0c1030821400ba0001502c8288040d03558100080b000d42401425000041a4413101c12405186c100542d0070041c0c09612070516004000410060f6805070031107a070010180c0c00d2940f04c1d160041448050030008084c0481076003444040e4044050209090641c807503c0000c44008540c1c1300c400a099500d0200d0280c201d410901038012108016001004007070b01c0c0c0d000000c2c1e03071520100e80e00e003560810701c0241c0e83c080d601c00e4450b00300601d88500d10841c240802c107a40e064880d0103e10403032050a4011050903000d41540507410901030802d441c242d0364004420312034210410403041e64400d180e030040d07902c8246070b51100c0b104103950341c810081d44c0e10b40c4643ca00c1c00c002c0c2401640d0310707 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 874037113 1250 874035863 874035871
    0x1409060a0c2003100f0902180609010e0f010605030c132612040b0f070c0305101a0a140a030f0f020a0501090803030f070915030903180605041401090513020403050615030a020405 78
    0xd0b645030010100140e4508c1b50a80070030078500d640c0001800c1103000d000036000b0580101032510280002d0000c0c0c0380741c1000d410304440440c608582d03255980307020090300740540d42c507080f004040c4503000f05d801c0201e003092611000303040401036154502c003114244c1e24807000d02d8640d110302c1e01300001e00c411415000100b04004441e21142d1034a84c4941e27179030814010941c0b050380d0b20742040154540546460007135080460280d022910314512140004650450074800e11440c100507806100d115180c040d0707410300840d04002c402c6002e1800e03080500d110242280b00f02e01c221480080401d207980980312440035250043c0045056a8032500c58400580000c4e0865042c0102d0b04000582c2d03121035404803440342c100c0d40e4003242c142c3c001d1a0150078a00540490301d000300c104402400b0459018059508030342e4400e040311145014200180c908041c00e1308201c0e001801c4443d000c4150703c02c4d800901c06c4074807ca0885269a6500c480799190035101844a6403540100f00d2000152405400003500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 874038363 1250 874037113 874037141
    0xe01021207060b0d3309020f091b0a020604061103011203080c090918060709050105220e131104020304021c050c041d0105010b191409060a0c200310 65
    0x41c0b00c480d2520111100041c01030b4400c0c54544088003024402178480d1008644007000034001803403a0344c0090200c00305450740c0da01030500117001171200b949558580801c00800034000c0c1da21400c56000a40701c841c1114241e81150911a40d02c5d80044070702d040344c0c126020200600482d00e0036503400c4a8001003c0c0200022500900c410001075a80c694640e015031841081c40c5005440002100c0c1040d0004020500740030200c0310421060341c0210446100c00d5940d042c0d07a007070385e80000001c016603c04d03401120815250904100481841501241300140581884418864841d04103c145e20044500075000581145260850300300312900c01c40244c4220181d80c060800c440200301240c43d4181c14030384002021030382030035404080c0705187c05021031118840c40e000700c146805003140d11800c1040204107c041084803181d000c6015a581642c008042d01da40d4070310020014034050214105882601c102c049100b0401180c2c40a004018005405860300303142141381080280400003603900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 874039613 1250 874038363 874038379
    0x1b030901020904020d060e1b03130606091406030f010501060f3b0f01020c091f031e14062701320702030c100c111c0e01021207060b 58
    0x182c1551203001401c00243d10010008541d031801030032000071800981640020090303203a9100310400711100703c1c4e50011001c00b000c45e1358229440c1031001811994030078501c1c60b14102c5d41003c1303034070381504850041c00120129440607860015a5088660038865200070500356440c100080f0301803a60346185130015800d401800703515103441440c0c0382c020440c092804241110700f16051410b1110b4620f9200c082c80180020000a00800c480b00e4018042c0c4000e03801c8030740c0a41103080e00300030510155520904c04c003d04040701301b84110088045d2412a404031000b0102004200001149441280c00425480d503402d03490100c5a0005400d5008103a207540ba0400d0309004010f88010340b02c0d60003244281da03419800c0c6254040c00b10307800b4000c0700443d0410030800c4110340e00052030407002e841d15040042d007040802c9007a82c003030704d0040b016203090060703128075403002200481c08140d1050a2700c1c0c20148010002c01240c07100080011561850340511000f008140c080d0f0004500b01c0c8040e062031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 874040863 1250 874039613 874039627
    0x60c0a0f060e060f010305070b1608030414030706050f06040b1809010f1d0706050403030c06020c0c100804060b031f0e100908130504090c141504080f070e1b03090102 73
    0x50401008444c2103414080600041040003030421501e40140b0183c2c0c0325030300f40307030215034104201c4a0200002d40007001c044041002d010b45c1c20303140c0035242c02c0a021296600c0c00c502d0240e020b00012207248807240700d010f00241c40c1c0d00b02800381080740b220080500d0323180c01d1808850a00401d0140dc1d00e0400d43d82e81c43c482d80442d10510032044201c100c400c4586103030307040d00c9510b072901401b50440380412030700b8002040000d411500c0180d800354003450141e21f89002c400e0413403405060303443c0141c3c000c01d8003076403414550700300480a00803030240070305101000156042c1641e441c405810f40b15007c45da0b08044142035215446401c04800b154259482504048981016600035171b2041d1040200002d0300c01505090040200c001c3c9020748003488002b1707294a4280d1203c000b031150055450044000401ca5685d03084031030004254208101c1d2200d845507400c0f550b41d1008807010800d40f1030050003062910b400342c5414031036280d400400c1045002c0c1c00000ca0a80c002810449081d9001c0c0540 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 874042113 1250 874040863 874040891
    0x106050405090a020405160203070807030e09010611011802030c0f0a170d111c03051f0312020c0609090703110403050607080a0b100806061804090602040311060c0a0f06 74
    0x5a4010300d8084014000700f69107004110864002070892000b580340030b4920764105401000303484c2e070b050b0801551900c0340c125050940d201079501e280c441d4000611170002c2415900010f100010070b100400811040c55444240010030052440207541544400401d070340340e142210003d41364210241001e64880e036a080d084140c07940c2014602c085800941061001c598001c1c8440d00000e8000001c040340c400f0610540114400b880000d000c140e15440000c0d1150000c4010151002d260301e11440c0c0c00303a4a0410352420300f4113020480041c0140d420b201600c1c6001700c150b524a50700140b901190351a40c0030140d00801041201c1484100c0c1480000041242841110301c9852540c46a190390714140c607070107080f9212160312034480ea42407030132a95401c2c0d00c0701d86e0660040c01034403101d42e0303480481d400f00b4050042c4010310741c2c400e0400405400304245500a003003240c1c0b20b20203034080c1d010080200200f41c0a08980e42060f640020078440c0030400306400340c144070703000b0b04000556840031051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 874043363 1250 874042113 874042121
    0x130513091509020306130f060504060608030c0f1207020109050f0a05060316092c270115050114030f04031701060f18080c130f150e01050a12031101060504 68
    0x1944401c41e0345510000c1036050502c1a075520a50400c11490710f001360381c3c5c0b6807118800e810380151810781c1d9900010100925030380800b0282c2103060490b91222801555550317075100044024005014482c600c1e840d151860041d281e89541c140c440180c171034200014840042c2442035020382c42010f04a002a00352504030045020384041e080d02040d14a520300090800065a48540e90210000002c04a0310041e8900d5103111401403481070141c1c4c9814a40000040c1c00c90b0781d02d4020b0380e00050115155005510484103964440c00210301d4503599401524910703091542c07030f4203096082000400200c0148045076215100713081840c004103806540300b91140707090704808046409400c00840304c6801c070440c1d20801c000c00c015a440541020011511046900000c6001e80c11140b4584501002074015080304401002c2c00c01c05c4c20150315120001608511558a960003054008030f542d040200714002503807240801040070410b1a50300b141c5076036491004070308655886401151654490003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 874044613 1250 874043363 874043393
    0x1021f020f280f170a060e010f0e09030a0230040f06030b0411041e080d0f09120b01050906010e0301090302010516020c0a03110d0c0e01090c020313051309 68
    0x124550610a041440281180844101c40c2c10f0041c80c0d0b40320164244c0c0400e000703000284012240406441c1c001c4200040d01503074100c0c00d15081079200100f208411404039404440d8000550603060322400803d5440f485041142801a003042910f2168035070041c402c44241c600c442000f40e400325041070580b00542058008045000f11280100031031907043c010740b4000c2e40115010800d8a03100521213250f48154440d9035a4613010800d9080300c0c407280446140200080c00566080324014040200120b09441202001c035802c0340c80030507090341d040c0044d940315038411541c5081e41d090030108048028000e0101c0d0410500c04900a41030b1828000d00030070611a400208860901028410b10401c4c04c0401008640c444411024141d540c08519011030360081b11810403141c2d045d0109056540445016100030491000000d0741741e16150241d040303903a0686c0c1041041d01e000e804070780360b1180c0242c541580b807120300d00f44110b10302901c2c0486050440000003031080501e50302c17140751201000f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 874045863 1250 874044613 874044637
    0x360b0a020f030313021002012306011202030a0b180403121109040c030606020c1203121806071e080f0a0b040f18020a0504110d0507200a06060e0601021f020f 69
    0x20f0020446c1046481d040080d01640002d00406114040c030a4528045000040070000701c8404614507901400c4c00c0311502c10284401d55480c64505400c5002e4041260301c40d002e840300c04005807424a0005501e809a5030507030f43e0b51441c04140300220f02070940782480a0950100f0007030801595120b00c81ca24030000d1649022031120b10f0100040d062440d07e428082c0030344001086420144404411502c00c52170440314884a5110f0205000c441c5444c840540b0452044006001901d6080300e0800e41c03941003070780c607031401001c1542e00710342c1042e0075036100c2c01c6100e5500c0451101ca00701d80000c0c203640f8019000081195010100d542942c003c00b1300002c55040c20b80802e0158104804180003a020a83d400e102c00c625600301c040851095860515005039a603020814651040d40b00751950001c0011303803680b90400100351500d49055a504035801450542d0008215504002e50b6108041c16000303440a070104400021040b03041c1001c030301465a081000e1100511b441c1c0c080c000d80300701c0b1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 874047113 1250 874045863 874045891
    0x1110406080f060402040501020c0405091207051f09030c03030902010e030304060923060715060b031006030509060906070e03010f0608010b19080c130f0507360b0a020f0303 76
    0x75045480e20b601c00680668002c90040000380620390300000c14083c96034080c2ea00050360303a50070721114108003a0380d40611700140d00099442c14844000740c0243c545142d4205481c501901404507812a0300b015030090201d24074105600101e40a41d00c40481180181450005e025007540040e0544d84242c00240100d14010b406100c1c840b104040089880440e00c1c880e080e115101001520034040d1100040c0b8010f103407105042a19015004800105080d00010351a800d010294083d030140601804002918003000201c074008001a243d0241c4000c40191005482c2c0440480f0008441d05501da015900c403440e090a10300300d4410740004201420000484003000403c120b1100d2901c00034001c6001601014032400e00c0100e100442c040b01120460b104505213600d642c0078003140110001c82c14a0802045003941d0821000141d081d83c03030070b01507404561200940300084400f040407826894107007042c02803940b01402000b1103699401202d0f0183d1310302c0c2a0b00d01c0d646c000c071880d601c82014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 874048363 1250 874047113 874047121
    0x4060e10200913021e0a03060608060d0c06030c050f04030b04050d020a0c05093409080d05160501090c14010212120a11091806030d0503070518030111040608 69
    0x200003003004000000700003542c50000da07a400550300024900d81c002400e41e00007000c10004141411007103142942240040d1103030003a01c0041d00522a501c02d00380410306950003d102d6150596802c05142c1d07000302c2c0c200740c03281030020480c010700c29504c0000901004010580039004480701a1000354880d20320450145000d291045c01c0140103003403d0306540c05071182e500010109013409058950541e1003042a03500c2c00c2000c8560010090348032210400c8450341000c41d00a03680d045441036845d111030300c0c03042d982e5180664810b02c214003140003c01c280b00c140030781400e00400044040c022000420700185c1900d0700769024140d0f40c403441189079010010354142d41c05102114110303604034112820283c1031840001c03d50001408005550344e940e0b40d6a01c000a1402520110207001d0540000014400c9102e01c1c0744200b03881d510710a22441c40a50300d001d100320110307807007100641d5545d41000c4202a113012078040284039150325540390b501e501da29404a4025000030000f40e5992000303410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 874049613 1250 874048363 874048391
    0xb0705040f0e04062a18050d080a030c020c030a030302030a021b0304061103041a070f150c120e1906200d05060901030b010519090f0b013504060e10 65
    0x426030311384108904c0e0b81088405410b0074400345c40c1220005081603840c0f18101142e45007103815a400c2a0b9000c80c140319100141310201b805854440782030784041200c0c1e90300450590b80c40c0007882c0403d0781a4400440240028800d4000d1500319445001c058101041c000000030314101036500c0303582c240e1022a00300401944001d20305d00c40700301d41c400303103103400e0501d0b40c51078a21044200c4403840201c001034010400a0381c1d0a5800b03001d40184007118410340080c82e00300a000302c10f10600c002030680c481d07031904401c07a118142880d54140d0080c41c9950340c4000040100d860740b68156074581d5102201040d001d0311281e01010b201c0c1a4564555800f4454444421500050011402085010014800180310044250554008541d111f04200303c0c40c004607041c5c11190030039400c0600f42b44641d40101d030a174110010404007602c0303003807200001c03201c0110308850042c4004c051000b554688014429030000780743c0c0040c00b5030000708400d45e600b140c0381c0c900400b110750a501c00707a5440052440032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 874050863 1250 874049613 874049621
    0x151701021c111b030d0f0b10021506121f0c080f091513050708060a200d0207020105070210090509070c051f140408130906120b0705040f0e0406 63
    0x900c1161081009000030420002c1a0040725515084080c05500350004008200155042c080c1445820b10080040805000c05058140d02c5203008034080364880260740d00102d80e000c01d00e00002500385259848034100008180484404805801456210710307800d003007441c4410000501040100b03024000d400300034141800140800300d101429014000011008600c0d4110541c0c4104055260b46610021042e41803204400900600c00c1c040000380e41d03580403549074402d001f001c404002d201900381003a040c0c1c0541c411040217103141000060700700c2d0072070382c05400b6007401072621509200c982da020a419841c180c03100c10100d004035104004914180c0495a485806403030000200341469903031503074600d003410050010b401140e000380618001030f442001c854100d08071525140c20282403a25543d480103400c50440320800201140d20601c9000700030407565412200c4017000c04684a0184688001c1c1504080000800000030700c0e0119114260152000500c50b0429051900d031040c101c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 874052113 1250 874050863 874050907
    0xd020a03050c130c0f0c03200604050105130b0c0f041805040c06030e03180609031c08090c010906030f0f050109020c012906031506070602220f0915170102 68
    0xf0342d040149588061303034020224500700050781402600202c8034542900da001082101e0024100c0307152649000d52400500940214042d000070003507915000c48000b078080301d80340040e000c540308102059a501000e0000c000400900b6503041c01c094481032810400400209801910b80e2204240070a1081d0840d180d030080c48070b801d080004a03212011a500c5e4001c02d0b10314404141800307924401a01d8500846120100050603a40d010203c91644003a12010420010000300d8040005008100005821031200c0050f16036600c41880e1010843c0600142c83c0c0006e03013076850712000c1d000b031031146c000c1502038000c1d12000741c0c54202d814031300d03421a460b01d49103402c00c0d040c040c19500040f8072940d00450b000d01c203544c2c65582e0780d64041100d104805110703d15401c11000203a00c020b1004940c064161040c2c880c480328644a00c01c0c8403454405054050820480840841000520143d9002c0c1e01072922a901c50300310b0310369035446406410041030001c100c82c1d40009100810001c560384100803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 874053363 1250 874052113 874052149
    0x2040606031b231c0c02070f090506090a090609050a0b0702011112070e01141c06080d1d031e28030c02220906090606080a0b04060b0d020a03050c 64
    0x60803c4460300c0080e6070500000d2580d1280002007000b034280c0030380a240b01c12200d01d1424004c454032000000d54801c0301d031150010324007040704049100080c0b8021640501c2c0000c090340c4041e181c200c442801400030301d0702260b06a41e19007402c00041c0b414000c1d42c6c1c400340500090002407624441c003a080d50811030dc8641c505008000c081c400d440281c40f480d4000400b40340041641c03401000581d00f00741c000d00042441880810f86c041c0c40074440710041e4840300e05540034070060740d0f60740c6107a503185429244200030038940d4200c042007903c460821545440002c089031a20030740d000c070254840e003888c0c403c1542c503005540d0380e100300140500854603807864407000c0c460784601910010000c9a032405c0007440360b404144c000190101210740d0800508030501c08010701d000b00d2901000601481c0c90456145041450009040b440415075070020f6403c000e640d00207030341d1941c443c0003c1c10404415a40b1420755800c540c09a140c1d0300c00079019600c01c00080c418041818100f0903801c800c00d490f011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 874054613 1250 874053363 874053377
    0x106030323040e10150504050d0204050402031f0e010510180c02011401080307050d03060b1b010e0a030909060b040f030803130203030c010f1104030809010c05010902040606031b 78
    0x10398885404030300581c0c0420302038000c200050340d0901a1003254060b040120300755050000c1d928001c5804001c40e0390248007100c09040d62403054429000c0c1d44140303988a030300c18403154054146504066485440141a64180c0b54020071030050014404404c0f14010b40c3d41d01c0c80981e0303190921400344c000c5034403085002d85624042c115203a0040081542c8030a0b80c850090022603070007500710401c1607400d0740c6400c119603140c01032540e40f07400c000415203480c8100c0340d40502d024028410203054810720500c00d450a4130020840103d075140d440200c5c21996649003000403524140004021244659680710307400e40b50007090310580340075400c0750703e45a90401041054038074400b250011283d0000f1019102d996040c15800c4c894a54500a5014000001c051800f4a0194020801069420790401c0f012101056a1b040c5025a000c010041d000030003003240c2d10f40c000c4003800c460f0b6124400200703040140d640458155556940240040303521030404071450040d42d8040798100b203181c41d01e41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 874055863 1250 874054613 874054619
    0xd0206070f060f05250e0a06050703050f04091e0e030a030c0e09040b09011404110d050304091a100203120a050c0f0f0a02010e070f03240c0f110106 65
    0x1a09500c19880000d11000c59200524200691030300250843c2e4140f0104100916048040c80c0d0380e10f0b40b8480710302c0c403a03103003183c0d0100d43c034007480100001030030240803083e4003400c1100503500355001c01404d5061000500c00d40460740f05040040011f03110780000410701c101282e81c1d600302c2c441c40640c0314088a080402401c0701240c000305441d50294546008107040581d60f200345c651640401215800c0f0141e4002c00090100744103919025808142c001c001c2d80002e48078414002030180c83c0100407541c54500d0000720700d8100c031b04580040c052800c1d28030b0a03945402110850344080100803100541c229115181d01d0030203000b80c000081400514640000c6081d940e04805c0001c01ca9003070b01d41c0d1640402c03010941c40c0705890040c2007e1310825941d450095002d140c940102500740300560070030740d252240e810040b621800703c540c4a03601055460a5654140c0c0d0a5028250b01c1d0900a80155440c000300315400380b540040100e40f98010803241d0300030000d1280c1c401501c1203c0b10380c1050810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 874057113 1250 874055863 874055869
    0xc04050a0e010b09091302030f0d0e010c05031c022205031b01080a0905010209041109100519121104140a09020903070623041509080d1b050f01020f0403110d02 70
    0x3200e0113070088604442c2d503503c000d094012148102d6000e034040c40b0f82004200000d43c00505500704481545071003034556914001194900d4000030010304640040c4101c0c102c0c481c038500d50440407000030a000d42424030f44100c1042078007040c001001160940f080411040c03d0038003402c4401110300c404c5603004a100000a05100800f030803a49400741d8451031442400300c294191303400380710010b0040c04903001021641c0556040b00302458464800544003c444500480032a103000c0c1703011400e00020184890f046d941c00030b14946031078860340c807030703210042818903503004001074503e43c45820080e00d070102c01e02070f0303281d4140c00c00c81c06148108003c040a503000642c0108559691410d6920b0922002000d8078a03500400c004280c840d0102c0d002c20011039907125031100714081c0d51881202e66403640416a10062040d00380045070391842c610b2600e14660058038080781c050001c07a801100c8010010382203901010001419442c086824070801c0a00d000e1319004040c201c40341d60f0f03c45016000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 874058363 1250 874057113 874057117
    0x50d060806360d0509090f0103030804020d03091a0309010f290a05060d0504021309030509010e0d0507080105150307030b0a15030609060204090507181701020c060c04050a0e010b 78
    0x1040c00c204003041642c01d068441c50810402e451041400d0b1040c00f180100d020b0040d4005400765881030f040d41c40002c8800d040340003c2412a600756807001035039242d42e02030101643c8040b00071303810043c03115400700d1010107000c0381d8241c0108424805582e440c115140c80c0c21117501d845491000707401d0001c3c0821103001848049482050703a88096420040030300061152141c580c031040d00090045080c100d010300c25800b061044d03000b9590344e40d0900200e0300703000480721580002008240f06215203032055101f10450803a040707019011382c10300c0105880340da1610031554054130a50f9118401c01880041504100204100030b400074890301d425075039100700c1d50400402d5980c0c420f0780ca4050b8540d2025280e0704100858114404218010712401c044c0081d5100b4003441072440d0800740816100b602c20300c0714210800c2d40c03081c0e0444080c00d2a41070019042000410030156409000364042800280089402904400c0303e16650314a00400c0c401404807903800740d00b194154100420a0740500c8003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 874059613 1250 874058363 874058401
    0x60f11010b240c011b020607051c0c030e06150a0501051317120a0804020a0506030405030313020f0a06031a120304090506061303080d0b0f1804061407050d060806 71
    0x112060700090300c500c00710040e0068030246069503007440c0c5d408070344945845810105945913801d4402e25a1003580a64692146010360900c481004e01a030030040400d502c81a403640d810b140c04a0086a0001614503240081e92011464000391280081d5403900c1e0f2103240003400203092003800c025038429000140005803042d4a255501d91081c00e189032420b0203903003401d0002451840d21038804850041140c4002c0310100d0144030405400301d11490460300b5207106550203002146540c0c0d030b11030140b0411035401000c07608034100381c0241e0b149a507040c07200405001d032907500095041610688600313007014280424002e100745070403080245404001c0b82c0907104602400300e1607848035000b040705072184284003c0c064004490110411510000520840012001c180402c12201040010f40d0308030310401d03548401c45c0021032000081ba086810391003800b034507002840c55030b41010503040c000e0403140800010000107021314076010720700ca0179000d00702c5480205600d1411560180e030b0814910 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 874060863 1250 874059613 874059649
    0x3030c030903230d1b0b06030a050a0b0702060703060b04051909020d0c022a150c011e0e120a14040312080718030203060615220f0501020133080106060f11010b 70
    0x1b100048564030f0401441111613408030880b2020b0490342030008032014180c89020050103002c0200c0e8001d8880c2c02a081507403148091549440d142104000706180149800781e60140c03910000140c140d0944050800350180710b8010642c00d1506c4802810103503490b15100600d8a510f910710001201d2165520321140242c0300c00781026510b854185407809424030392441e40d07003428000511031792007500f44109030500400500100a00c0c4020540310151540c0b0303255144810700c403040e808e610a00560201601c580b620628003a16900c98100301012580c040c0007003541001401907165100480303c01c3c00440c550a200350b141964006a215580581154030803010800c000310307544400c0d01100c283c1010f1007010a60300c501028150580700c01807244036a82076900600144950040c0180c1d04605004042c000c0046086407441e100e0319400030040790513030b409120114080300e0034400d10010349501d4a81d0341d03004d400312900a0480a014860810f16414810807079543e4840d0043d020040c906a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 874062113 1250 874060863 874060883
    0x30605180a0b1f03091e120e0f0d110f09040c050f010e040504060506010e03010207050304090917120411180f0a0f061412010b0a03030c030903230d1b 66
    0x1400000d843d500b01040140001e4500030601800e003900b5a012582240c0300c0c0600044800c440120b2110040c41705c2c80c0500407150f600b00314941c1d944211268503101800034065039801d206200410f03041c282141c4211034469040861170301c9841d01114440c4000320843d40c0440c0d27440e150741c840c14a615503200e16405902c40d075119003401c0e8015030103015400e9002d01308004602d000e0074418094541a1019408079040382d00d0514181010b000710303580290407900071860310345001103000080001030425113454440051502c0d0b0744050703500600c3c2001005040e0700d42820581048054901e01e0710b01c0324850005488152440503642c40d030541c0c000800102101c2170768031600d16038054000d002140000504d006000f05411882c001c07205106c0c2801d80e1004481926092420308992186c0611a0310100011080002130310031096000c02031f100380792405001c0e540340d0362841d03c0001141d40c580ea00f030b0f034844135200c0c0c0302080110001e11032a40c03401078101d80c1101c1000c60820307900107001c0d10319602 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 874063363 1250 874062113 874062131
    0x200307060f020a0212011e0510060c02030319111204050d3207170313030b0403020f101b020c0a0911040503060c030601080a0e030a03050403030b030601090606030605180a 75
    0x2804503150080e0058170201c066842c1c444418020709070302e40c000c40101041d911141c400794503842030500c01c1854221321070300c83d401c01200342e85004140104aa06100420001466150301c0c45c44602c4018252224180c280c6c00c014650b08140000745400c0640700c084c08204015034a8198042042d030700704035211150008410300300c5d1a803038000e500741a1203503c03c141707480135100002c0e04c00c1141e006144840c00d011203202d01c1f94032803040c0301e04c006c402401d204081c0007144207030b40425007040c401e004803000a01c030216624100144c0300750800d40255602c014495650700c0411065011183d40f0242c11800d014000051200c1c0060040414407940c542d031080c42034084100326800741c1070007000c555030703483d241210400c5640b0448071603000a01100125100c030900b4000c0c92401458a0041c5007004c0111b08124001c0030020403c4d000c05481c0d810304101034905201741e90281031000c1000c01c03082d05044020302920984c1c1c0c40180504181c102e030a555104183d1016009a9034a4000c18944d507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 874064613 1250 874063363 874063367
    0xa050703092a050405060a060311120f180d090b030717091e0604030503010306022104050c030d020c131107051203040b012102010e0319050703200307060f 68
    0x6a0340750014000711156030b04803004282d41900e494404564940d200709107440d0014003003510b03400e480c140d40100e0980b20501001d80241c101120b0308202d03410050030013101031004501140207465656000e444901404810340900000410842a0310028079040c0e010071401032603003400340705501e40400c001c800315054610a139160013207080301071240c0070b45081061003188c030b80140c400c05c41580140c18090401114004c11706170710aa415803250350450780303140c5490010b03501503000d400c10402c0c0e86400c07400301000501c07841d0107140294001d00040100a0505161441e81444541503501c0325542e41c50698545000c040d0b001c80b0f484c0d0106010050310f0825002c0e00403050700130024020240104019800c0c50040e610030703802040403408590780c0cac160284801190034400440500041e040c40c001d94040c100e488220503000e001c98601c03600740142c02c1da540380317004d40448803500603600070024420380f40060514504441c8030041a56080000039513a40d5031446036030b080c030400451000c80a4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 874065863 1250 874064613 874064621
    0x4080702010806420c101805100216060504060f050c190c06020c0106060c03030b06120402060309070f0b181206070809010f020a0f0210060501050904200a05030f01080c0303030a050703 81
    0x140e948080f050f00e50800240c0d90f0745a40c103400c86d032240a0324204281c101140d115600030002504040038100c0d0b2400c412581d800303580440d488181410103000300c400020154820703144114098040051a05152108101582c0002e040007584200030302a40c00700e0000c00000400c5000b860500c80d0701d040642c5050b0b0081e01030005040c103254a0304900144c81900524000e0b031103032186d507041113250341e6101000042d0003800c1031513882c41002000a001400c00d000103581000f9807070202d0740001e0b500c8182e107881b03030300a0b004414880c601098414010015500d155100c0000301c03001203204071100c03040303a82c5840007000d41c070070000c802011928205080d4410062401c010b50190350b500c195210140440710310000b52001440790001450505102e07214200c103507041652424a0a40050104805408100d1000d01e0324501c64540b480452007081c010046044207031546c548902e0100804c0303c0780d00301684080703604d8010f00d1144a040d94040200ca5000c28846400125501c51000440c018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 874067113 1250 874065863 874065979
    0x51309050115081606052a1c0f0306050306090a1e050109030f120b0a0329012603030933070801080c032a041404080702010806 56
    0x1100b040c049001e00c004155011981400c8510180882d03131040100c07001e12810182900400c036000c9005a81544003c0c920b2951914004443d1101001810b802c904515a20483c1c04105070104800300036826001c0c41004100032405041c407450148000c94842c041c1c03030801041d181030240383d50548011580c02080b0250000003c00c0114101d00d0003402042145407240c01140b000d12003240310640310302498260f40d01c080d00d1a901c0c0e910315a503100908240ca0750480708000f009041100c0310a500d020316008107250700003c2e01007441d0141c1d04114019000965225400400070070040d0540010041a9004040781300c5900b4401d00a0304031031400c22010540c42800100148603401da44803820a061301c0500e0155443d0082c02000c040c1e0f21180d481d49003900f071740c003051007a518081400560a00c03c401034008201094044c9658400301c01c11107080f540200c2c037141c2c07c070555902001d542e070320000543e6030fa542c074a080c0782c025400714400c000049850b500c449a0308070842040c00740350b00c1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 874068363 1250 874067113 874067141
    0x20a15090305120a08060904050d1103040918111002030403150609021902061815041104052502030412120908010e07081207020a0b0f0c120a02160513090501 69
    0x3d0b00211240a440d8091544000001c1d900307070100b4080d2500030542402941d0110060001449030042940c100b22071945d0000640024000064944036034004d2280003018042c1c0c1c1150350103546000c05645001141060084005000c076800300e41c0c00008132801d41c1d070011440005200c081058002400d84c541000940500200d142085684111801c010060968080c1c54140da60040110050310001c02941d023154045842c11000e07624403810181c2150203182c0380901c40c014200840c0c117440341554683e0350110048560420f00f51002510302e04c0600300d101941c501441d080142254210240d0090248000c06034983c066a0151120708014240708000348080900558005d0701e40490b03103d003001e0790098a860490310808a1b04640001d0350043c041010700d400d00c00040c1c8e264111510000342d5040421000354081c0e4200252070134034034080d0700143e40710808030b002401c05c59110840c07810044078410a000c02d9440c1030400d80c03000d4400b080000c41c00c01c83d00707049000d40000c144c8211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 874069613 1250 874068363 874068373
    0x316230a08010914060102030a0513050a0e040c080706020c040b0609130608100204150c02030a05030c070620100b0a030c2408040b0121080c100b0409020a15090305 72
    0x400030342022001d4100c2d10ba90f0010403081c0c6003440f803901ca441d13046800a005810801c203001c061405070f4042c20500703c001d421070380c0c400e494101081c403400c0d06070031010054170300c44100400c00a803900d0001c05000140701916000f8a040c0e4080e566900c101a05031085480b40005800750310340c0790645480c41c0d0010080003810281c608018010701c13540c000c43c582c07400303061000200071040d4001c07030f022070303075000000200d40c00c940408645406148000300e0380360160b1480c02c00421820805410480034690141c20660314060010313081d51030311105410b074183c2580e0035a0000e03030081142d0340d020340d0544011440d04101070009024503100d40008224001c1f4203000724428060084001d646400c2c4503103882c54456020082e03c00c0001160700506e100714075001400813408080304c071020117850941e040041403143e86d0300d40031a044100e003e50180e10400503c02d1046250051444400c82503d007008a11815000304880f15158003641e01c484c20076001542202d4401d02922004540181c2907603 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 874070863 1250 874069613 874069627
    0xe0106140705031902100b060904050411132901120c03060b0a020106080706050301031e050a02090c09182e0b0a020706030b1503040f140717060c031623 67
    0x300c50361015a00c050b005101c3d420545042006600c12a95100387c000c02c0c841c00c042c1d03800c0800020b4140104201c41d042c0c018890344c0c901e91985c42c840044021501004241001a0706c803048284208080e004d1402c441e00030031034643d0f6085200f0060714000d0707100104905110341400e901811841e406141b449070300045050340c00f98198441c2e000d0303480c01e000717030742c445680c41c58101d50600080c00080c01c11102098bc019004101401c03241103988071701b040d0358481d285600020119402240d69149209000941070350503d007040e200454080020003480e032070b0500554010200011091032660340d00343c00001c0c0300f026070300c407842d50040070400500c035035400030740c00001d407140c2c06c0788035400209040c01c1461125190014804070511503e0701003e003503a43c0c50f2504100414246070039942e00306103400300c01c00b4040a0181c08041c1940301c00c0c0c2109401c00125143c949100107202501168060013480202c22700301d00104074000042c50071140e161900084440305502069114481400000e441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 874072113 1250 874070863 874070887
    0x81807051e0411040b0912011503060b0906120c040f0e2b030c141602090a0e0d1e0c020310091a06010302070308010902031305120705160e010614070503 67
    0x1d0310304407506840038418400c01590040c80340c0114000c2400d42c000c00e0100302c01c141008850040c0d01d4050100108002c800c04444820075074141e0401da1f000344c1c031a60240c0316814070002c43c1c1d8000d042a107510600901408805490780c1ca41030040d807003540c48042c14a096159074002c004410007840030f540050f0116410f0031380000c03074001a240c0807000f1805a080c2c050080c41030b800800e41e50384644028102406403030f40341d988200101141c640c22101c5230b0001d601c03941609849043c80d480300040c0184800070f840d00d00401401c40c00c3c20444100003034942c0418843d110030b00c01d14141021040300c025032001904003032042080481d03440c64050044103000ca590300c0098110300c003114198180d1203810046060780319081d0040c021070300d1040100103d440361b6002310346c02400341400580c05140780d40c0d001d05140f09021580c0b20020003003081400d002060041050b80c1c2664004420024039000e1048504801441200288102c0e44500582149428201c03880c4d95031000550381d59420300300030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 874073363 1250 874072113 874072159
    0x30603010905061f0515070213020c1b190f0b0304020a0b0d06051e09180f070803130e130809010509120d180f17030405030d050417060708180705 64
    0x3c80ca41c21200320b0310019940c1484880c403071b084081c0304495442c00d1103136000d0020b8114114030548030316600b0031101911180902c03070030400000d9800c10f02e1542200e00704000040000304405201f8000d400c0e010000c0d40c881e50f091604603682c42070340c180c0b6545c4900028425031500d5001c251440d03c0002c8000c03146c48a42d00500070f441d0100c40c03800c00406c801c5041100c5000d070030002900000385a011031620741024007501b041d202254101c400d52100318034124105070080d4002407140d480400e046800c10100070050001d80204c207902c00907413400c0110420003150802e80901072400000c0c82c00c54903445402254440580a46415191600c08000e15560b8036000034400c002a000c114032500306003103140060440350322204691400d0308008104803403060801c0351264900c020030001826403000d02c00e1601c8520741c0d03155591154988000c0c0c043c202207070803030b20704140c1080341084096601701d031815400418440d451034403034014261041c684034054110035413100c1c91580000f985200050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 874074613 1250 874073363 874073401
    0x40906090b040309090f05161b140f070e04020609010c080708030c0406030e0a0503190e120610080102040b03012c04060e1605030c090709090e01090201200a0803060301090506 77
    0x1401b0400c4441900c20360003200c100303031a0004007041010040d629548290b0031a1030007603881e081d8240c465696542ca0001c150b1240d014102c03600300c00d102c00503040381400b0b120020202d10050084a00e0700303a000a142d8850007002c80d06010001411001f03010f650400d68400d540e112041541d281804402520144c00c5446100002418000710070014140450880c07802e584c018002c0d41049030b01c00f62508443d8104103035000304130841c0103100880c0d4130100c595095003200f01c09059542851710b42e00700c1103070030340d0400401130780108000c121a188041c1141e045600c0107040c601c0075454007080a950922650209410f2842e40080c8000e110f02c0d07a02c131464140b20881150640340302003407185a01d0341d0303e20655905400040384607a00d424a440d4407a403080c8289840000e907520346403090126000d90551250b160354505882045581043d05071001044820f8089980504c2590051760342046c8603000b0007a201c00300128987d51030035003203034409d184d100f0250785031803502607032070680d1100c405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 874075863 1250 874074613 874074629
    0x16230411041e1a0d111e0915070b0406050c0c07030803220b0f07030e0613030c0b010603050f0604060b03070e030f0a1a0c04030203030318070e01290414040906090b040309 75
    0x30f0000b40c0a20054000c581e0030b86441000030100b1030f0741d06c80794881c0380c101c0e45c1c0382d58020400e54045214091114014441a4030276401250319041c00d0030200100c800040820f904000308010405055400180e4841100e03840403c0a0b903940d908283c40828903a91903a5225800200459204000716440024420424515503070590340c0e400000b102990f02da80031049964001300042080800090344d0150080d00a0034103062001c80ca82d50502d5600e02640f0480000e95501c1c10711810f824171803007042c0c0019003224284040d84c01c041c40c07845540303c058a40c0e000d00540421000710307601d0a00c030550720f0980c83c5050f1013802019003020822210000701ca18280c210b190000340c04c0d8501c000035034007030740d402a00450856841a0029a0300c0f10032414240c03051080b0000001e0310b40c03410a003c0d018203400d82801c1c6c0001c00c1c0c411003e42001e052040004e1105043c4024004d01c00c030505034071000e0204032404500243e450400c5c0700240904a0042c040190300740c00c0000781500710001d40201c075040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 874077113 1250 874075863 874075871
    0x11070609140601061205060a0308210a050c1b1203010f0603050108030c0304151202040f0509060d0b150d0c0b030603210409090516230411041e1a0d 65
    0x1c008503448420901401303010400d1001d0344038803004554811548414050b180c2e46c034040d220349034100340ba0000d040c401d00b60700c0c00d13031610340d01c100081201030341020000c0c2c0c06204504050b01022520b0017502d20305604864121410820004108140115109540112a600d5854019850040c1c80f0f501605010030f0800c0000210703000300004803642800a1070107182050b0420003c88802140c41d8441ca0800200c5030302c07052501ea041c402080148010024414071a00c0d080a101c0d6501c0b005000a200e011624881e02c045003444580c20740c006951201440c60814010020740c1c1703c046940082c26080a60300c0200c0e40e190000001c600480c4120100c0300e8004130513000c451807000c1045460303201c2c1801d20041200c000d0a810102e00180704034291102480703410400c0407600c04a902c0b01800d0300f1110404074140f100c0c1c0181a00d403480540e818400b0038581c00f1062414491071240740d450349102c1200c00b045203243c004100c06081c0d41091950803c0c401203442003d07404c00c0c0440b010507498 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 874078363 1250 874077113 874077143
    0xb04050d09060806060732030a20060c0d09060e062a16031101091124041a0c070602070312050406020a060c02030408031b0d0c021e030111070609 64
    0x40500c84d105920080846161202c1ea640d40d61804601d402c0d51a0f846591010000240d000b2655182644c1442c400943e22403038400300051061002da40c011599042c05080605029408106564050340301c4d11181d58503050658444c00030300c094400034101919244804c80b0110b8040740d038a020f01d0001441034001c54003c282c1c0c00c202121820104080e02c000c10009400242644e01081d2103800782c00d083c4126030a01d503016094442421040b030341d5026100da164610b00e05049810030880100b00006404442585200c0c410310450290030100e1b012031444546001140b4205c540c0c1c241c00c10291031099544290103981ca541501040360500c03902c4410501d014840d50540b0100c50140d401025001c1c2140c58000080503200f841c0011800104004650124100000d0400440c2c0d1051045180041d030303502c5013800f0b429441b400070080726002c00070140e62410981007040484131140300803c3d0000c4000307030041181411529140d80d004c580e8605000042c0e0143c02000d008440540c04250 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 874079613 1250 874078363 874078367
    0x606030b1b03010618090e010506100509100c020d140a030e010309021f121104031407030308013006020c010b0405092e06080705011220160b04050d0906 67
    0xc1101c440400701080c03004202084c81601020b40310b01440800f13000050300c03155000180c0d0f401503d1222503070b440708280800390170f201c3c08a00c0340c16050700e0800e043c021f070b040004500e0802c800109042240303100d0900c0943d5100005003211a6204120b46041c42000101c0e5468084054090340450186480d06030554000d0203440740036039004060000000528900300040340c981c0c0041010403410041c50340554103144981540d0510150b1a00d03211841d514000d0540e5911880c80c12540d0040c04c02000000d422060103819280c0d513150603582106101c29810304100c40703407803103c910200d1070240300901c20300d54002e00b0641c90078002808401e2100d0288015540300b035035203c1146d840b40100d1401701940b503007540b440004902a000080c0c84040d801000d5600307d0b04a9055500308001c10440c66030400a0090480c5002e201840340010b13a404003030030032002000e0b1a074000400507504100511501c0040d01c083c4e80018411540c2c10107003031003641d0700754510050303010520404000c28218 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 874080863 1250 874079613 874079641
    0x5070909060b030403030c17090c0a051914150720030c1f020f0a0b160f02031e0c01020d06050a0803070209180c1203120a02160f110d0606030b 63
    0x803916100b0a1854540340ea04030010401058030b04100031240e20300f01071082100d4407190080d1076020040c180710281c00c04002901d43c06611440c410700c0c03da900ca14860b06105003603003c44100c00c119500881100f8082004562007201992040f90300141000800c000f10401d442c0d03c510140070311001440440c03d03d070f954050100c00c140c1c01030074000c08007d2540d4501c00703200074106510680d44281c1e10410340d2481c201881c001140c0240c41c50080242501c130700410031610040720710700040742005000e006901c911a400d81243e8480039000241c8041041100301d41c07081001e08002c6695080c8038003540700800c00c5006440c89010707080c0340040d210304000280c0d50300b580c00a003c040c5a40b1000e500c07204240c4100072078880c81c001c2000110207580e510300200d0b82000000f01940e510010301004454035200141303030003003007881032002c1050702070310400c0694000e03442101c4141002c2242004038581c48ac2c09a00c2d80c2c03200d201e20b458020003240360480001c8134800c0f82d1172000c64440c00031300504d2f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 874082113 1250 874080863 874080869
    0x31b0312011d040f060b040c0507050c040207031421070c020f060f040501080a0603050105010e041b03080307050c10060f03110f010509130209100c030e0111030d0e07180507090906 79
    0x480c0c0b001003400304e041003101c4044144951000140141c8500200d4160b0341d0502540380814800305001d81400001d00254440fa10203e40440c5030480540c2c0203031400d0a038160031400d01e2000b0070102c1084009407441c80d582d41c42044a03503a0707850034280041041407040012800346603103200090881c200403040d0741000c0341d40c403200c50a0505110044586800003000841165102c140001c0440d01c284603035406040060414146850310703041411142041014101e070751840d003201000452100c1e41501e4000c80e0074a483ca45d20542001420b05d042c2640440d4003560f0318144002421039142610001102d00c14994014440010400c000740d880341e950309580420700801600b4040c1ca0541c0d0b0b4800c400d8140c5000608114907280401c140380d400c661540b022403041d9a40009240e00008803003039001091a00580d02100b409200c0d807640140251030301120b484070f0003c0012041801540c01400b000030302c1080241da00318840d03014290540300f10780820241480407845821602403034080d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 874083363 1250 874082113 874082159
    0x7141309110402070609120203120c04030c0902030603150708270d03181b05090606070201020c10020f2d1207080a030b18010302030d0302070b01050405040302031b031201 75
    0xa4105000c00c0c04060344c08100e007264050f9982050000040341031002c2000140183d000b951140710103010000703a070402a100c10520401070008000003038030303a000314040c0c517000000540c481c2c81c4e44011074981014007076540c400794418406c00481c03a84c0f05501c584070710921180711400da8850304206c11a0701c0c1c07103000444d00350005140301604501030707048984140348009541c80840c00c5034851400c440134541e88090035048198003003180c1e142c105625a00844110b640341c6c80c00303420340e0010359138048164a2078090f10a00ba0040090b900a204c0701180b814080b00361083c0584070329042d99a041498555085200500d20840b150600081e6079074454500c960464070f0040b481d1540c0500f5005101c0ca4001c050303c40494035860b85810b01d00c4403408081010a45165041d0b104150034062840c50040800d48180300800c08215520401030442c1c0c030580c0e00180b0758985040803420340c401c1200d14131a40c10683c0720034850f02800130050469802c0014050042d9882d8454400c48280b4079299a00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 874084613 1250 874083363 874083383
    0x605130b0f041521093f120c030621080f040b070213140f040c210614060f1302040803030c041a07020d030f23040302151603120e07141309 61
    0x7400711034000f5030b40200d442d40c0301b140100c8210600b0f41961808958030340000440d107075000c1200b0119030068404051403400d060240504104400d82c420800114580d1002c408504c81028410020115018080c0f518121030744c80e9220503141d299a408010200d000340341c0301e16441c01c04442d5100759010186658036030116134031603101c9030202d800041c10035170300102200d00c00603444400c00440300980ca4001e8142640004c070b0308250046230403800035a4480c00c269070411500e55101c42681d00300d280308030b03140c0903481ca1001540009001d590840c8609100002c144001c81c401c000182084400145044141844104007940940500e540094104c10f05d60314041c0003d024440030000c0181d14903089500e078041030724070201c0622080208000f040005024019802d00c031000304905514116240c1c50180e42d505a548940e0f0030140141c00c02448101010704001e035a00a2907508200c002114649525400c03440d011025240c4aa40f03d16207140504211b10342c60300440c21500c0c0c114445107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 874085863 1250 874084613 874084643
    0xc090207080403022106011409070305060609010f0903020603042a03030c0b04020f03060412111f050417040e0604061508060f0a03060e03040e010605130b0f04152109 73
    0x360318034690850b00805150810385c0000c860381003200038002c05e80d000301d044216162070148058400064240400c040c2460104072281c1c40f25421150a40c4c000e00c0d06030825241c0b00011901d07420a504001d5000c04004113010602026030003040c0241c07189401d4140000341b908907420003d40511000303011451146414010510640080364000e00181c110200e118078400000e00389113003101d04442c1c0f000301401c022800c5034804e40c00e20200042c20010522040107801c405203494044105440194071900000e00b00310a100400801013881284981c03200c2d2240004d440c0200700320f4006024520308080080c0c1d0f1403001181c0703d003d498075181c40300140c40c0c0400f8442e07110078003103040d41c00910384000000094810b2140791071064440b0041c2d13880e54101f0316416407044060f4011010460300784051004901a84070400803540403203034141d034404003001140940c0c0200da12075404003503141c026192076500440300082c41c0d08082c6644052901d21208201254001c94020b0081c004002e840c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 874087113 1250 874085863 874085869
    0x30b040204021603020607110a02060306060310050604060f0e04110304110f131a03060108060a050901091a0a0c030612030302030a0207050303180705042003042105070c09020708040302 81
    0x550040c0c005400580342c501c250400c200d0364084224100e00580c40802000b00d600d512001405001403002d01410401d0f10540025405000190403148030f100d001000c6050b419006208200921001c4d03c0241c031582e489a010700f0110006103a4408545e1a0300b50041d1842c10b88920552900b00030841411516140c660010002002684c01e81040035118240c81c3c5503a0540c03003001c481035031880070030b8048080c0c07581d060b6034043c00e100324025841003005108400010403d107030312200c00d0000090f10359404a07924003400c8100030250890705040300d0300c040f4404002000b441044800d41c10303c614009038030300320101c444030712802144403030492071200002c0c0b02c0d4005580041c42c900025090805944a460540d801580d41e4401e1110750014502203140611194000348004c03502040b10700030010010543d140906c803950902140040040c01308020482004070780700341031000061414481d0b802400903440a902900c00b00741c0d01d2000140450341c3c4c02241c01c010741c0100442c0c1020710310707030034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 874088363 1250 874087113 874087133
    0x403050a0201060b040b040801060b07030f1b021c05150c090d050c040f02040e0c123d050411130603090c03080d0203040209130c14010210110a1b0c03 66
    0x108400710354903039100044001143e80a80080e0580300300559465181c400c2c92409c40700541e10449004070300703100800100e0f401400d1104da44c461130420030f071220403506141c0c0385005000c9000b544003070001040103c1444c60010302560340d100e4821144960307900420a002c109040b0b41046000100304052142d44c200000c00d8090144540125083e100c00b10000a040c3d0300703d0002da0700c0d0f0684c0828108020b40000f042240c008071f081c44513a01c0c0c4040c04212581504005000a10101b45139810307080080401451008800262444080580f10081c1d2480c0780e43d002d10546105a00301413002c450140c0400844483c4e958a010381d025180c5043e01c298003030100d202e81504c8076003202100002081d41c001c01444c1600d66a02c00680d03904d020310411042e204007414004881c001a0b011a0029140c5880d40041e1a0100ba03110764803013850340100d1601942402c00d200e15420f00d5150317011200d5503000380891101c0b0b5199141c0e941c4100703e4007030b91480300c0c0002401400c40703d10300700049000264 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 874089613 1250 874088363 874088377
    0x4141b040c03060909050c0f061804090809060703020106060f020d080f0603120c0c03070b090924040f05010810020f12041b08030715021e0906070611190e09040305 72
    0x2e010801a80c0c40b0190340403a60b42000544403904401c1d1000010700d019903060b1440c02003120218248608900390794103a1042c9201d850080fa500c000600500c56450705807460f10b1402000c8980e95a035900e0001d000c1c250b5845074001056041d459103108a0010469419a0b20349540d43d0620790b5652154440103440a000b1039014010030b00f0380b070142c1400000505198010500501c0340094000601d0700d40b202c00d41c814010030b00244000300c05907580c1c00686030020984404002c441914120b40002003c1d020f195aa1040c40c00c0c2c402c06d414030050700060b04a9440209039130614850105101c140c2c40740c40110f100000c0f00f00401c800031701f424021a81c01900a140ca904500d20380d100481c07c0140a4000d02982c2e800070031400100b241241140100010209081d401c1416803444520f800c108030340700100701c50020407452019201c440681b1206904401c0511030f136540c111100842d036100016141c140100060174145207400390844081d540b0008e0300074a91039450f51002c41d65070304051 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 874090863 1250 874089613 874089617
    0x1030f1803020307050c0306040c3c031110051e07020a180b011d0d0825030813022202070b0c04050307120c03140a0501050405010504141b040c 63
    0x1003803900180034951140680c26101c0c0e0029959903109080880ca440b540c00d03003440c820703401201000000f5046c0320168049410041c0c0d400c001c2201c114141d005440102068030b0710000c41000442c409514075040c008032405a5498501c05034400140521100c1010703618010610400c003c80080f50301d202c0040c41554881562410014240c0c0001c1d01403940380d010380901c02e2a8180d0480700302061040c0540420242464940b0120386980340552400038504180304100401c81e01041c000303000e08440312a01e242030680b01040001500d0020b2524141d001d0300050040c0c0001398400c40d0031015050b81d43e4000b04950340c031110306003a0751141d102082461758542d40a10009002840d8001114001e2000600d01501c03907007800140351070403100382d102e041803014101020340824080c80800c416260030403225280e900043d01258608a121403006006620740030800083c01010342c04140102c0c85150a140e030942c2e80c11110f03585039420306100004a15242c81c0009900d07003648807281c210341038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 874092113 1250 874090863 874090871
    0x1e090320010203061c0f06090b060a05030604020a0312021615170405061306090206030901090302060a2a02010902030601180605101706120d0c0543090c170a020406050901030f 77
    0x3039a940080e0781d00c8c40022150225124284032492400351025005098180c000308040d00d0117800050341c2c50040d12002c0c0407950400f80b0b02401d24402c1c800900c0049015080b6031074030f9a9000c1c01002080003039401000665003546141c0307185141c9458a0290340c001005140c142c0f9410302554042c00c0b0356600310b403403540d1001d1880c0140c440c04041c512600c0f582c0c3c000520b4049a08011381483c00041000340c1d8245002c07120200c1c072108000701144045407140c10402d80c000c3d140c00341e005086020003c0d5242c4905030000130441e031485010549034150f20b5083c130040c0d03991030500950504602e800b4000c1030305440c0042c42d50040102c070301d500101c0180750310444900c840d03106040c01425234410f00000e0003014044140102041300c90a1021185c00e000d1050040605804401c007030b005a5070000e42017141014100400d1002560242031489010403010981102c05092804030014011500d00d600b00001d20750000c0d8800e480484010740c80740c07450802a5001113005056107034070042c5007644e03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 874093363 1250 874092113 874092143
    0x7080a12050103140c011b06240e01180b0f060a0918240609060f1404170c0d03080a150b0d0c091e091e090320010203061c 54
    0x14034007955009501400c03014840b600b00c1c1800b0380c100700fa099010781c184605601841058a106a405440ca41c0c20100001c0e40d0340e1404101200a000c441103600502e404401c0400e0300800600014121910034900300d800c5501c4a0000e0195114001c01c1640302180d05590342186c00c2080040c00199281d02d001c0d072003e81c0790301008000c1251040701900080e07039042d030100403012444581003a10024117005159914040307004120901d00d019000c03c0150516a458a081c01210000e80c03060060440c3d5495a8442410a0b000d00f0b19400d4041944100301880903507003400f003040c807585900350303480310b10740e40e11280741c00c3c051f22100d04020750441108100240c100100c20142600c2105e40c0c001080300310803000c004103039000e1504400d50706918410f02d5070403840d0740300c0707030a0444082c41c0000c0f0b0240d0b031440d1200d0724140361000c072119150800301044100765108826402d07414440326055000d0003001b103200e081703010840d626a040700d8800700b0224400d0380188011a0244501805604854 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 874094613 1250 874093363 874093397
    0x30708070c151b05130306020c190b070801051f0f0c0213050105012c01030b270402030106061b020d050a0210050910080903120603010621060c0c0807080a 68
    0x581400c2c0d500d0b2460b940c4010b5070101c1030803000111804050301e4100e081070018050302c2d0890300a8032001300380d90f07400522640704000c14403596101c20728a13101c03030441c104c2a06001c00030050880d0b128000030803440000c1340915002800032203050803001d4035041c40300b41c41d4054503948654031314075040c041d042040e0380049e83c074424000501c2c2c0d2049000b203425450040050034581001c56012445507041284401c00400e080c44604028406d10300442c0c1c5080303070301c0442c0250717521504a01740b00b040100f4941e080714454003000c1c0102e100758000c1100641c0c0300e01c211030f2a010300c500203d000100a0190000d440c0084810031154082c10944581e130803913030700040c540a4040d20501c00300d900070074213138040c1c90010241e50b0083c00c6810406524540500b640380c40344120000141030100a40c0440c05a0300c0940c001405409181c00002d180ca960f025001d40031480b500c0d080f10070030f042c008208541441018001c914035441403115041411554503d0308540000d81181c0801290b04040c9034080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 874095863 1250 874094613 874094633
    0x20f04091e1412182205062106161b1b08011d0d0c0c0512010e0f1510050f0d1401090c14031216140604060c170408030708070c 56
    0x4640b00e143e55941311004034035600c0e403400110805200348032070074a0ba59007094807001030001003540c0100040c95030f10600010000c404500201d9620201e14442200c80c480c0001c442e8069030156441e000e80040c0c0f410111907150303860605688081c0307031448181c0080c05a61341001070102d0300d4040700c0107544400010b801c46140c01607100c04441d903200000c3c3c4440d4180484003084015180c034405c40c607102d0303d540d00e0303442e1288529802001d855841d0045850298015012184c440044d00d014003048110156944090101c5a1440040da80824600310050f42c22104031780000d0300070420003194208110745601d0410f0140e81d45c82011000c103003454000e12640034402d103d06aa0802603003841e11900c00d1200d40420070f80030303901a4260300c6828550000f6070b4900390007040700c01c8c110610303464800c103844000d0784503408500c113850901c03080004542040185411550b20403900c1041c0548c00c3da800441942c024014200800109041c184220803480c0c1c459440d0401c20b6240310b450380c914000c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 874097113 1250 874095863 874095883
    0x70204111204020111070e010e060103090b090102041815060507151103101401120f0603020a0308041e030b0f060d0807120801050f031c1b060504020f04091e14 70
    0x8a01c00c4800c010466170060200c10b00030700d101000f01122410040c5c0c0e40d622a906000d00c502d07910150300000d80a0307103c0d4008003a855032040c0780035507a0820b5000b860113508039004040b144803800540c1161502d0303c0c420841c1c0000e12076031181045240002c140e6241c0e1015205a4070784600c950680d94481180c05208140310703101075220703500d01d82500386651190711900140d07200b0480602e09003181e84c0c0a2408010312544500008280705126002002406250700c0250040006403000040c80fa21001074400c9402d4001e4480000300c070b0318004616a0340341d010003020308190b40e000c00e0307009150001180d07100001030aa00f801002c15125440e2541040d18120307070360b141c060300c100d19031980090524018142030f100c0300c48030303055100000e0b1102d104521100954001480401245118495211001601c0c011203070050324241009405003101f00c409900a1081440205480c1024410102070340e402542b140e05411800240c510981c0340d208095402090783c0703c14201034007040c0009208 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 874098363 1250 874097113 874097137
    0x90901081c0507050a1b090f0905070e160513091406010e1f0804110a03140f0a0c0b1b160812070c06050a02030c0a060906051b0d0207020411 62
    0x540140520358070118240740801d502080400d002e007400042000070380e8024994003540281074580b665070318881e031110951080e8500707400d140b400c4002851319403080403c98003980903240e286071155100354444005403101400705035804041450f0034443c60282400c2c8055820b4440c1446d541c40c84071080c0c4d40310310940c140c000403820509c95036607045002e01960940c19212810081d561458803e881c0030200310310801c0c071085400207801c000712041e05003403804005262100650312414421a042d40d45d246410b45c2d03100c1c00c00100031080001070040081a032000d607641c482402e0802d00d01e6a03402c00410800d070010030307041210b00d204040c0400b144195a034404a10050720b8010740518044800c012645040020058140400c0a00c44614165000d5080403a5100300c1158103d241d0b21a40703000506c5805242401c1040000c50340084e4100c50142d2014001a1202458041000030701c04500d406401d04000f0381d51405101d401500159000603c0000d00b0714001007039034070540c055400300311 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 874099613 1250 874098363 874098373
    0x905030d030605011e0e040e010f1113080f0606010c03020a050a0803060a050d0b0402060a140408150115171e0c0d0e0307080a031d010c020c0f030f03070b070509090108 74
    0x11095034461304e04a91030002c0400b102d1111005d440180064400000190040341c80daa038500c000882500502c10030700c07443c4800c001d542d0400e0f000c410749030042d102a9040000b1044002088034000500001c000c1e002c1d00604a907458607401941c0c5c2049020044055015096003113010403406c1c044002d656004861455a0780313440010403500400a802c00c5208280480d9880c0100b500501c80c0c9a00507416110b180d951554414103888207100b17441c0002403140b00080100719014045400c82d51080e0200e89080c4990301e90341d0604019100d090381c1000038044006c85050010110a62900305084c07442c1042c4019456100c080c02d81c40031078402110403000100d4012408261080d000c582203500003842c248005565001c0e080c0c4101e042200806446000c00142c8000508000c18200c0c00e02c1d00800a88031072040294551050401041c450080001184001d083c0801d54910380e0a014d0b01a5290110701d030707120701c54504060300c8013041080a2051196944440012340c1c040c05c13091000304 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 874100719 1106 874099613 874099619
    0x1b0e01050f0316080a05061005010c1b230a08060403080a0203060307181a090115110a0606060206240a030f11030106061106060907050f0a0905030d0306 67
    0x1803901d400f03500041c0e05030002829180841c8584d040d2241030f070395048000444c0300541301b441e020550103940f00000035107640500c1d14015040c1d462816442d1038400c80061454128202c64964240c1d581007055880c0203000e0000500c031450040684c1c2c5042c0e40c0c014803050000d06440d41160700032010500d46e950a0004c00c014284071024000144042031a18003e40a005d280110358550040100c8090a24001030b034181c42c84000c48000d074220000007203415826030050000180240c0320342400040c60350140400410080e402010301d0704150350b40e1122101c151901224500c45140317883c101e61100e100c45401c41e600a99600c41c0b00c141410300b2405852400705076a410752070300001190f05034000b004060b807500701e00201c920316620710040c04084401911780070041002445480c0c042607a60700146441c400d54903050301070b29603610100b494080c00400507408a92100e40c14 = true := by decide +kernel

theorem cover : BRFrame.Cov 873920863 874100719 := by
  have h0 := BRFrame.cov_init 873920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 873920863 ≤ n) (h2 : n < 874100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
