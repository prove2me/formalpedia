-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2966
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:16:16.681347+00:00
-- url     : https://prove2.me/submissions/a83c7dce-e838-45b7-9432-6bf7f8bfb938

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 533273381 ≤ n < 533453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 533274631 1250 533273381 533273393
    0x1210020f1c0207020f01080c07060f020405091b071e120f08060604050901170f0d0e03070504020702100e060915070203150405030403260c030909160e090c09030118 72
    0x580615001d070001c60900085500041524a4074546203040100800100d140800840100c50b070b50360f445041000845082d0798900040e410a114a81c4100c2c203000c0007841d0300d1401110040707a00da0180c505481c0038041e54406025610010101241240381445800042e6041030311143c0005680c0320200c00d05000c101c010721a0340700074566405000144801c0140b070300ca241049040d101d0000c0c03141d4100175907103a16803402e808031103d00c219108614104960b19040704082c5040c2405909a8224a0300e842c10310003a842442c0d0000d401c00c40301072022244510403000b03800300640040480e45086e68100000352030b00041500ca55082400254038001c41c44e0401448464411207a1010340f10310b002e4891544a0040d0b01c006060320b4104010040740c1400440b0202c0083c00001c8403688601d82c03404d40990b2a008403034074078001e400001c00b05100c42e1100e556071003040810f60f40c0c055a401c80c0000c1c00b100d500054516603000c5824070460fa25a90f088c0503240100c29660324039a0441c0c0c5030300b410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 533275881 1250 533274631 533274667
    0x406050c010b040b03030702130e060106081815071d040e0102180f0604050d030507050a0f0212060628080607051306050304020306070c14070b0a2304051210020f 71
    0x441c803d0b0702c0c24000c803165450200c1a2a0440c2d0119107403010700340310450303a0001d0000c07008400e6460049400216002c1e030071034042d40c081c0d80e2008410f6003a03000d512183c0d68800c2c220140c54901c0314410001600180b08035410740d54226048040022030081102040940f0006040c1004594002c0740403540d0341c120405000b01d65000300d9450f12240481c81c0421214407075401014020f92842d0842001d05019408075080305ea404811580602c0c60b40c1040303c902d000e0314504910802d5003200c2e0b00300410340011464021031000341810320002da080c1c1c0c0b00c00e020701c0201c8074011840d01d901c4001510ad4003032041d2807050069451311a581c5a40410211500c4525009070301404424014400941c5000908507400100c9080101000b42c3d903080010030700f6882d4000151038411624045001280400900165a003513160183c415a41062a1095050030005181e0080c1c090008108070711b07000c04001d0010a058003130383c4405112080144c180c0c3e2000920703c0d040b0340c00051760031040c2110488 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 533277131 1250 533275881 533275901
    0xc04151803030905030d020313060e2d01030b030102070c0621060902030105040e0a111c0506130501050601091a031f0f03023d050d15150813080c030706020406050c01 73
    0x910728140309e603a00152008154007500c003c0241c844d00103449130b01e1304144070400e1941030f0713100c040d0f82d40c0c0d071071401d2101c842000c1c006002074108618040241014003e50b11142d60100580040504040088440d0340c403000c80900e0b040d143c04810003150049100e404050704002c0300140ea20760408041c003040d1924090300c0d208591204041601081c0741528060702c2d2081202d60a003c0d204144450900744e90031007000c1c01e540180c0d0140450f9400d00c240740480070344140020f0202e80e40380d80056806215078800e2000c0c0071411080490300c2040d4200a40e4032010001c1d1a00d14400c02030621041303034042d5003140c3c0400c0c0500340c091055107411600f400380f0780826071411481a10301d8032040e8034000103030854141d04040d44088140d09010b4010f4ae203414450076010400030710a071034001003001c0740d0300c55200c2e22007201d0380d420b01862055541c0c41c4100c005550010100c4500d60354115180e00c001852500b80c0410300480300001d40342d00040000340025500c1c0d41e2a40500d400f0306007107802d6518 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 533278381 1250 533277131 533277133
    0xb0406030b0103021005040b162409110402030106020d1206080115090f0506100c020406051309140d02120c01090218092a01050d140a09050708060c04151803030905030d02 75
    0x40104840701c80d1000f00c1da5034140ca04039609150049c3d2610501d00c0c1203020143d0040c000c291081d441a905e6a0f01a00d13580313005011100e0300d10540c1c420700c0201c0c0b00a010700b50042c1c0007640300d502c0b0700c1c2c02481c80c82c4c039118035140c00003036003607450064170300f190003481e00f05812540fa084108452405400b44c10070b00c409160081089040080c0001c0001000310305420034098403a03005400e641e0f40e0389c0007600400d8040c10944480d0001c0019100515199004496141201e0a07110010000286024990b0740340d0b0010300c60501d02084040d4103402c05800c001d055034a90311f10310010f80760107030303402030540c0301140c00c0c24cc5050080c2e059082203850202d039000c0c00b41a40d0101e800400c002c5c0c942001c2802070074270958818014100308060148201800e044501e00e8041c000021119405100018064000e40d00e01603107510600da1103180540341110703440b4041c401802a410741c814082c2050403641030501980080e50106c1045070b07145d90041d004500c1640040100e410140902d1a200c0c103244 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 533279631 1250 533278381 533278387
    0x90607080f0403031d0715090302100507050f010f0203160e01020d050a090b1b0c180a0f02040320011b02060f0d02090307030c0f0504020403020d060f0b0406030b0103021005 76
    0x580188a2200201030418200e20342010606040c000d501c0800c2d12050344c92941d0f80c0009403180c95036128564441c2e0301144035510700d12148284100700540582c2c1d030043c80740340041202c071030480f0700d5001254281c541d801240000c0c403130b6410920580402c10030900d0b000d601c074135180400304c00e4610040c00c40b20511040e0f001c2500ca580c0c1c00320b29504005c00300d040140d22440a90340c1104c44007415001011034100000f2050b1095500f42c1c1515807241c00301007100c003030840c0b0405101c28810503c01d1882c5030050340c004200400306542080241007107017600141416900d44170003042501c4480c02c51416010801c0004c1d003941e001c0e00007601c0000320700040306005c0a0703034080b54052050f0a269126500301180190260f461501100d01c031110050481d44040d0300d0b070510341e0f4124040d101b02d4140403041900011581041d000355022290018015104001c454890350080d210341112551042d41e2000ba851482e902c91042c407002d14014071100c1511341c114814031142c0303802c20403000f007401414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 533280881 1250 533279631 533279641
    0x31701060c14010b0312030f1005030a06020f0f0a0302070203011a0f01050706150806090606010c080a21050c0a1403040b0105011805040908031906060f0f050409150602060906 77
    0x4418038000c10355201c00504030361950b040705140184074141c0c031903a00d4005e48044800d504408400b43d405103528550304001600d030750740003d6040d42d582c861540c150300b007240102c0110f82e0542c0580191f10312020340b1480c0c51031000740d61040b42e00603901800881c6d4041610300650809101c0c5c0d00708a140c89501c403800b9204a030025001d01d440840b0241005000144141004141e80185c8420303881c12018510094850610b1a10b90004a40b04603880c880d41c00001c06940c4602003800c80940c20001e1545405003845c0d0442e503991600c007424011040490481c44604907901c99184264090303040300b0b8451010a1004025580c200c2052088841c02e20621012550360b1540302d04591013400d200b04961005801d60300310580301c2c1c3c062030b17020b441c0c01c0d0801d0a108000d0015886120b030140d001c910764007051600c00c00c9810900032140011901d4810008140c0200c3c0340380000009070911038141070350f461707480c02940e003002540305d00d08451150422085804200b210b820041000c0a40498644 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 533282131 1250 533280881 533280887
    0x501121a0c16050c031c080a0c05030601051b101506020109020f0d0507090203040b040c05030a170d060306060b0d060b030c03070e04021603020703050715090b070203010204050603010f0303170106 86
    0x907040d00070400c0c1e40264110380400200b00041e881e01c48010703058031086e1036900300d810503a982103514580420035150014084488510980c0580c0a003a140c1d03604503200c08004607110b8108201d109522806490700c140c6084040107030300300c001894280403518001d126210003110301164007900941e81441c81260041c1c0c2d40204140c0c001c2d00c00d480c10a0b45d548142425450040542d0080d40201d1000051106008020200c00e104a001c2c54604543d1641c81e001d043e0740d8110107501030071010340d06564516130300c4048001d04440348100d401169843e229142d020031108076901c05908480c001031064504036490141c5001040303200030082c103602e09541c00c0001f13840024880c40c00c0003030100c2202d20590300c0d507040c0c521702c3c1107803070306491a9251442c0280d5907002d180000d0312948a202c100042c00c0c5c3c5000d0115007a940103669800606242410f141c0d0a80c0207070743d0483e410754003404045a5515902c010714001c00b030038010503003840d16604020300303014014480004091004d50043c010690 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 533283381 1250 533282131 533282137
    0x161406040513020f07290108100b150d1b1803060906090c0b0c010e0f15040f051f05070c0308010b030615040b090103110901080c0f0705010501121a0c 66
    0x806031011000b034004009501c00912542403004030302c4501194450034002c5011142202041c0c0c104017200401040040d00c100c46001d1080c40004e5002030ba0b0250100a290000c1c000c2200240007410202d18040c416140c6401040c00d0280e007540d00d4421650030011004140700c2e8904e10706144202000b0362503124000d2072180005065141c4504404003000b02036030140c10516000400700542c5a1901030748201e07a440a040d1311030075801c04540d6503a240002c1058000b20782c800d030041220181140004001d01030090007601e507403448901038004644207010003000c2d4009a80703480009000c000a6174110f501c0a040c000c1044000d8401c0030000390043c5030b45040d030b5401000789403a907898900103032108080c0340e4030110103080450005003800e4100050045840300762010700015045117000b602d203000d41c040407030014001501046200301407600a1640c0b106041e01c152800c0c2d4280c41d41400d4038400ea200d2051401d054003405c0901c11001c0c80b40d0a403c0c4008800450380c1410b00800007180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 533284631 1250 533283381 533283389
    0xf180b0117030c100b0907020c1e2403040b1501120b040912050307170c04050904050307200a09090c0501112503170301152f16140604 59
    0x1202500c0312101d0800800a072420018114112041c20740c5030b13100d020140c800031a5132401202d003a800304161a001241c030842820001e007003a03110694401d00303120381d0540401c945800c5800c080007600190418650803404a0042c4900d643d00e05061601200600e0300034003441c90030701c1a00c54010181c5c0d000e15410b010b82442000030880d0030240c00060018964010020010901c07402840304d95130704503024510852540c0c6a08448010350000103891500454940000e0482044240820728003503400c5500980940100e0b820032949654000072200b008400c441c4280c54010750281501d803002c281005001c4a4805004615040e566203205d0a05802440d05014512518038203441e4204a2041c01030203480302022003a2255400308185482400142c0e1301034501e60403940040c0010017106d040b40c032180400c00402c41c150408480310058101e02c080000c0d4807454003a03201c8018030301c0c50702503221180a80720088074002d07010070310041c660150752018241d01a65980f80c0c1d0b0401610304070707 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 533285881 1250 533284631 533284649
    0x8030105032e020d06080a0f060f0207050c0402032211130e1b01110d030203160e0607030c2102030c0f0f0c0f042703030c170a0b03150a0f180b01 64
    0x941321180c40d0400350650f5040901039100c1c000c1800180030003003007007003941070050404102d50320b880714040b0245e10500c140a8441da208031800c503203901f0694001c42c0e121040c40b0b25000f100e00510081003e20004103015036885101c142601c3c5107141040c001601682c014070208450303c00d031079103151141f035007260000c00b20300e07075240c018030990044407115900008402a039640e10320b207903000f034000d41091f104090f01072540072034130303040c50f001d401500e0b03401200038885418040c00b40d40c00c42c0c00350304980302110241d4040300032086130202c66005120703003d2240c002e03503100c4500d10042468070044480c100302c582d11600d0000301000010441a00260080c1e0784201c4040000340410003030045c48400d100381134400228072551f42c2041c04500c2c05184a650140b26107544040d0132942c0c502140ca510451a07107500100ba01e2110300c0d031203846540070180569103a00300318a092030424004640c6000e8807501c800c4031010584103441030541303002d8940c41881c0340880360344503400e55102c14050b2901c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 533287131 1250 533285881 533285887
    0xc021e010213140a0b13030c1517090102190503040b061e0f120304030302070e0f0103031d01020c0307030b0601030e06010e0112050a0609290f0402190f0308030105032e02 75
    0x41c5495540f0a50045c1031040c504a5552150f4040c440c1865024841034901400910740424020540601141c019500c0c1e0345a90a60b407010307102c480043d8000d0981405ca6600f00b103076001781301000c60f00c6507640b0901d80b1001e03100c0c5404e00303002d03098a8005108030b10654001d40c0d402588445000a5910240d0684403c2c01c8446244d01086003503001e50b410481a10010800008040c1e0005d47c020580d081d11400030419102c81c68030461602c403c1c00014042180241144060080c0d8107403030f03560280510407584400039540200342002c03c5a04250344085240301040155605405003050b43e410801c0144080e6140405240c901181070180000740344207404407600307109040002809a60b0001c0c4108644da425141112280a82c0c1345400b00400713001013040c540b01400100d25200340101522089560340c1d60b0708200f52010000c00e07421100c4803640c0d021039240781901080000d14840d407102c0341d80e541020101860500c2040c08071429540701810701d600003842142c0c1e0035500030b280b00c001d03031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 533288381 1250 533287131 533287169
    0x5190302030601140414180705070209070507080703030c030606020a0816020a0e0f0a1d0c0f040e03160212070b1c090f03020a0b0108160b071103010c021e010213 71
    0x14130f9031803c030000c801c900300880c004c43c0b04141404250640303003089501c2001d040c200b01140035400811980c81010a1040c0f00040141c200501c0142c1d00c0351003490880e2420805a940d0b0301d69410100f0140c0000f5502d44400309059003600c40d0b400030f041640010211400179030b44003001032207580b00b81500000001040811511144204d0000d0000454505601e280c148490195101d007101c6540040c0e05106070190100d103412140c0030300c90351800280041041c1502400015214000d816810a07030f211006c5481442c107102411020b80354074186509400d4600420080512044180301c168000d0401040360488440c119510080c90001d0b40b281017540803540700061510900181a401c400d620f2102010b81c0441d10b0b030741e0140300d070010b0074150362500c18140d595066840300c9802c0500d501414841d1a14000117011018842c14080e079080c6640b902090940f02e002e41d652016a100d215444021803ca4961000840a4400843c102804407580308201c404600c900c1d040c40020b00d030025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 533289631 1250 533288381 533288387
    0x50a0b1602040615091a04050603041419030806030706080f0702010902090a0c0818060a020d0f060602150c0a0903020d080c060709051512041e0c030501020703090605190302030601 79
    0x1a256074009104002d221381d03528200e00700321080c5280b00b0000c0c40660700070a50f4060114900503001040d80300a042900308402c3c043c0c1c40e0700203070055650141e0740d400c103032404104020b50240c9205100036007043c08100d02d80544104400f4151610982200a0a2054560005210794040d41d920074242d140d032101c9409900501d030403403011b90000c04003010011112860742101e031642440d6a20091103980e01e10840b8400700c0c2c9684c800c00660000d20101d403600c4141e40150180000c3c217000000c0303840a00e6040b4003103030400e600860150f00400b4850660304001c00b480c55001d1120303454580781c0301c41100c00a00102c85404003e1107800004002c00c180a1100203440c110420030048845508003040041c204812500c02c051244000c0d04407804a15410030a407504401010010711050722995255010180c4868191070742401c203e20200c042120940c03d00700450103040010f9841c0d401e410014001103560300715005102e0100f0000c1d0b80015041031211840340240781c0180c8039102e2800403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 533290881 1250 533289631 533289667
    0x110c06062211090907020a030206040209060406090f0c0806120d0503131505180f03070b040503190521040b0402040c03020f0c01021b151f09050a0c0305010b0301050a0b 74
    0x540c1054030b00b4030321500e100d410340001e0440030070840391110307150780d8140103e80e15882c0d002d0060058118402003001804d124604a42140008001086060b141c4c881c84e01203403410100c041c416a11100b01e4070440d500580c08a030020000c1d20b0f000508403071030500355039400e84134000201b040710000c001004125000909496240c0c0205041090711624500300080c09003580d081c112004200ea9030400e1480008001c816100c1d0307070024509000d960344a060308000018420381e040d0000b0071002282075080511003103801180d489058807503215210400d00d245100c030a0706c101e41400e10503c0007098a40d52130742d0b880740c2c0c101c9002c03500750705204c0102d0103401a200742030b40301c80b8003058031b4845d448103401400301036a42050060781c42803565609a503a4100341c00b24980d9402d40000715603400421424059455454036411018640ea01e000303604036602101c0510b012503544105001c01ca515000301e500521241b46020304650610000541c069418030981514140025140c0c64503085d400032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 533292131 1250 533290881 533290939
    0xf080a0e040603051c030c02070e0408090901031a0906041505061f11010e0c010e060a020c0d0807061401030b060d0618050604382e0801110c0606 64
    0x3404559621310785659120920025561074030f940404c07208807240b11b441410149002c5034020041180791143d101e020910182007510b00000800c80c00981c0d44a4440043c002c501c80c0c02c064000b001c40d02c01c2517840356400b0b48484101e0b004201480b001c101031200304003442601410008807611640d00040c401e06500751700141a82d0841440c4203110b810459460b0040f007500024043d1650152205e91120003000c2c105000ca0b480d15101c60030740c2000740243c00303010303424011100705e400d4080016103803d41c0b1400494562900003540c0c1c0070044a40201486415100201c01095055a80385520100c2c010980350248002414110074004039801544010750178652075500d05241d0309085071110401c4405590030060003007411a5a45505050f80040005401c9516400c0c00000310904241d03001d0500707031821036161036030480c07014440c2903900c6030000303c040c05010f140b41860f51825030300e01c15000c00c141c071000e1010b41071100000c80c5160b0301c400704a41002446d505200400004016424 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 533293381 1250 533292131 533292139
    0x90a0e0309220e0c0102010b03160b07080408070b091003050610081005040504150501080601080309090a020c01150302040c0309020f060f040e0708010e0c031e07050c01180c06030501030f080a0e 85
    0x7108158443c000c01c903c4003002d820b0f0300034426480c501c1c0901d031303485607261603107130030b03803d4005013002402085005400464424502107141c541e07078600e0946404000d42010004901c0003a510055180424062400c0700990406000b54a0590001410020703401c1800c02840345180004520206004c044006044010020005400c00d0708200640d04403000740304400a21b86000131919090018015048850020003940b60032404400e0080b9140003905044056400b4042d20318841401c0c011003850010251aa0040515500402c016101e90700d049009051400d0702d200e001d82c940c50112a219038094072001d55400720000c20350001e01c10355200f4415000c4c0b0400b0701c00000c1d40800326178100c900030700380c2100d02d84500e0450131082c801641c0b50b501e1401c40c0e209035906807011080c00380d40003505060250030b0a900f00c00040c00e4940ba42c444541c1d48030a60700300c004000040c001d2102600c0c90b4a004c010035030465880c5040a01c41c0e050103008400d003c0f0f042002144504084d844c0503074064 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 533294631 1250 533293381 533293391
    0x90f03031b0105011e180b0a050d030e130c050f1606050705030114030c10230a030c1d010f05160c030804030203100504021c030207081506090a0e030922 67
    0x140801d030081c102030007241c4003250110800c006000e0745240400c181e42000e180803201c3c2d80f44d603802e00001d1071440d01c1990084040c00300094240e840e28901940c03a03000381c4411201c040c9000820075516010b60900410902d0890300503d81640002a620001e5050401c0ae03626035909000154a030035244004000604040c00c0000403640b042c06503048136000a0309800c2d154451040540307a4230300c0c03401d007a00000d03290350b0072014522032a81140742607452528201c41c0390081c2c000c1a070a40c81800b00c90046038861500d60340311548041d190340c038600310b0441400f0843c00c8000080c080442250ba078010400003141e8840e007042c2080d0703680300495021a07941e0007240e99142418294100317100a0f8442d00270089410041c946d5402064032451b030051103840300d140e01c400354828410400d01c0690461084001c00314421200b00300030700c140680e84104440528140e0208041504020301110001341443c00d000c6542400005031006d00000721030960b0a062000d42c5d070501080298108a01c40e4180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 533295881 1250 533294631 533294677
    0x5060114030a051605120c10120207060504051c0219061125030305010b0a0905040e01060504110c0c010207060f030f0f09031101150e0103020607030c1a0601081308090f0303 76
    0x4e90100c0c1e000392204008402408021501d0301c6084442c0c0381c00c03e501455003810144542c00d2110390b002c654000504140c81e68685908491081764215031680c86100203c0c046451111000b290080350b20040c410105903080031444480315540050445449140e031070715440f9500d00769440c6241a00d019001d0b45040040702e1500c0030707400c1040d0042803030a00041442c10554044a001c0f0400c1c5c2c031002c14031490081448020401d030f4070014080c1d5030b41e84012039940d07194091040410742c0c288205480d00040a05241800d422401260540d40714030010480d40e5000703801c10314004840d042c000340c42141e140d41c0304040d161188524100614002c03901c0209900480701146170aa004002c00040c034030001e034084841c000d402903007000081007004000625184001340812882480c042c22240e00641d111039080340389907038032001580d00d841040500e5900035000e0b940b002c240444d003c03040d0625194000c0c40c5c810f82c00518010700c000015100075071410402c5502600060400459082c00c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 533297131 1250 533295881 533295913
    0x309051215010603050906180c0d140d0306080a150912020a15062108040b0705030703030b18041101200c040e0d210b1c030f030905060114030a05 64
    0x8071100004540524100101d4014803c3c031410707100b40b8412000306001d40346d80300028441c480281440c51b26101d028000c0c90b103030320381c038040ca02624441d0241e074840901c01c0381d0003402c007009210000109460400c0420402500285151a1980020141c0420340880c00707003401400811101030300030f1a1031110200788070350009000383d14034003c07840d503030100d8404010402555038501c29055480707031204e4a42c0b8031052003101c00070041d100d0788916240955801030244590080c01043c0d40b6600301149002c00d1541502884030700074811201d01020b40c0404852460103800500090404568072500b03043c6079020b180d2503000c0c10590f490100c80c2802c0010781c0c80c4d48030042c410f801d000c2c5041420603c0e10200c00205110503004030340701d50031300800403181200e0708641242c00c0c517001915000758441e103441d840380900411111171034009040302142006090500100814020135281942c0c40000c00c02c04902903056421114160100b200340200007840c00c20211006411809004843c1f008110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 533298381 1250 533297131 533297143
    0x60501060807180b19050904060314060c0f0f210a0506240328060801060906120f030f03091a01140102070b09010503190c03091b06120903090512 64
    0x30701c2c1e54440c290200d0754010450981c0140c0300d030442c100e200b840785154002001984008100e201c1c0f500e142020361000c0080d00b81e803101c0d40f06403102c0c00700001c600c40c015020b101c10b580c480000d084251524420a00403451440346800841e2800c0c80840c1d01004c44a40403c0c0304201c400103002c044030741c1000001d0000400b015564544110701a000c02d2036045c41c04c283c03505244076080d00c068250f0380c0e0080603280030300c2c4001d01c0c05660201d9410075050403640341f088001070301405000080c17440c1068007220440307074507401080f1038500d07506803c000241509072113148070303030305280c814413000341c03050290050706203048001c101e02e003282c40c0000c03041f00c50401d19040f43c000c0024841390759882c0c0700581c4c41c0c00703a60296400342d1104005031040341d40034030700950700815403025075108250142c4c00e4808840005600c0703400a9140c0300c5001c240840c020f4608a0b481c0c001d510340016500e440c0000d40b203a4006400c142030b40352581540f00501d03000740080e01c003c00d00034289152031110400040d807150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 533299631 1250 533298381 533298391
    0x8120d09052e09050318150a0201051e13060b1507050c03070911030106030b011b1212021303030e040608010501030c1707060e06030414030f0a090503030304020a050108130605010608 80
    0x241c61455144800c241c40e0143d12540c681000256140010420313070701d07000c59030341545c00750030000801580f403442c1c05d907500070030034031840d83c0c000078090501031221000f84001c1c2040700c04007540302050090706603002c00d103503180581c4060000742001020011411200940c60030900520703010841f4420f004001c0b07800d2040348002c400383d520342601c031003002c0c04072036182e0b0130284079020500c0140003860203980482d07845601410501c1d05068400211000a9002c4d90308640321001c000f0030140d82d6800003001e055038401c0c1c010960615001e4140b2a00380c0c0710620014003004918140405503459550011000c2d10249c8000d015548e128144030140701c03424415203234808220124541d820401060342010b68900740e540452580c569000c010b03071034101410039a1803281c40c40c0d40d040003020400c000d0102d20208265aa01c0c0c2c3c2600b60040c010000c00c0e072203039000760000c004010059907010140c409078ae41c00d0030400c1d4241c44c7d0b80f50b016030f00c1d0142440244104e290000124000da04425040d10035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 533300881 1250 533299631 533299693
    0x4050c10181a0316021011091825030b0d0305120c03090a02040b011206060201061805040b0703270b041502160212012409060b0408120d0905 62
    0x5554442034456800100d100c1a00664024000b142c4c0c2c4001004600340c2e00c654510440b480c002e030b034603034500c122610030303203a408850b100213034100603810581f1000c40c00400002401815240c070019050001159511000c3c1c1c40118102c420500c9009a00004800d10040d116052051103072a0140c419030101c00105841d42c00100042c5c9000c840800b224401d50001000c0c1c40c60280307640c00c0c00090540200b420b0705105048400e10000030f0688249001080c140d400400e4207441c1207039180c0202c04ac0c001d07032000c19040804002c0861004601c00d07801c54054a40060b40d0701c04a035004400000800c40c07150035414000c231845c14401c1d4810602c1c0203c0c099618406075421143c940b404a2040f11218005890403443c800050315100c4090305075286c0c1040041440d040f044440b4441c0c2d040c64411200c4001e0301d40742440703082e844d4421000540050052149003c1c04c140c039190750b48204012648416100141b00403d0140a402901035141d201c011100030b00c010a9180d00d6100c0c00c0580c1d0341c48 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 533302131 1250 533300881 533300927
    0x2103072102040f0b0c070303050f280e0609010504030228080705040c09150c15060902030103060506010314150303040e0a0209100207050f040f1515090501030507080a0504050c10 78
    0x100c4d13000c42085400242440005125440c038503502680d43ea04644900111118140015446041c441148111101480841048000c4070031005818144090301d0079004603400d0000c41c071581d0308001103500f0342e070701240c410400070b400000795005520300803400031269908260021344441d0000d07a40c4242d410403142800225001c0d001201c0344081481660301e6410407031482d040580c080c0042d9002e603401060750140c281c4083c81c08200380e56480c0e0101001540c00001041880480d01c1032a070000001d01e4148504109440c0d030400d02c06000d0148100c45103071415801c0c5d41c1d42e04008481c01003130441c440c04000e250000300e14009401400040c0e000303240c0c1001c1440110b20221b608400d44100034030b404443c002c003009000c010300c0020507461040380e5903501d10442078295000b850090130400045204040314010003801180c00342d00160605090074180000c5580042c000369004402440001e06943d4030300741540761400c6900100e03040b81030390383d0405400703500c0581c1e1070317801601c0da540c242 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 533303381 1250 533302131 533302139
    0x4050c18040c0503030f1803010e07082a030d110c10031406040e2e050c090a0807051804061503031814092206020d02030f092103072102040f 62
    0x80c0341c2c420511442c80c0001c01f040204025044903441b0715a1881c0500001401581483e01d0740c036008094101d00380d82d91145085000c2d084070300c0b003210030031454616000080080000401e03518049403036890305001c00303450300340c20045003082051511040100803d126442114018004011101c1c0e006c4404043c100041d41310308281c080c0038103910b034680007001c02c0140c03405821016900b00303510078403801c09501c82c0000c00501c1d00400d800344d00c600842a9955907008c040121440496000d00b43d2030300881d03000c2003155224019810340102c481e032040e180380e94901e00351000b044040040100c11508040100a040d403280d428825809050604075005440c1c0c41f40308411803103000d04540c003861200000310241c4250341301c0c208030415041c0c800c500401568440c4141c4c2c10603091035200c5907000c0208094440c6106030660420000e00141101455201210b0100181892007400200001002c40c40d003610802a5007074130020121441c42d046042e8020760301a40c0507100b904d040c2400f0680c045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 533304631 1250 533303381 533303383
    0xd0504060515040c0c03030c0207050a03080c06100b18060702090f060423040f0c0f0603091707050c150f0c0a050f0c1008100e090c0103050702060114040504050c18040c0503 76
    0x200032045504c8105d00011141d0b01200070b00720703d00c01001180035130b40e000039a5440740120790700514890305029841c0c0e0f03003c41d4540d28110004203e021340c51f03440c61040080d8070f01d55045070003180d5540c141c006110351203000f06001744650f42000307421040610800103403a40610070705000740c0084600340f10500300b5481d000e602502d0704420000000300384022500103481140039a4605102e0300c400501e440d6207200491440c41740d940450046500d41030303040200900c1c510b422a110748c402214034103001442d26800d0b075504d04c140519001d40524040300390490440410740e501c8041c401a683d80d10072010300310648485140000702c0391840b600f41e103a41818800710b450241c16202500c0004603040141d021a4081c1c805000c140d1a101520b8010070f80e01001d0760342034810201407000340041d4aa1000040884a0040c060f10844d08144014051002c000e00b52a40c0785d102280d0110b9251500d0405a00f0203040c041020f5200c890340f9651a14000f10584151045005060919405944200f41 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 533305881 1250 533304631 533304641
    0x250c060e0609130b1921150e0c0405011d0603010218010503040602070609030c050d03110307050a0e0301060e0103051b0112051f0b0d0e0321060102030d050406051504 73
    0x80c0703038440c6060042c0d00c03050510402c161150080e0342004074541c001c260210749031400b144603100c0481c501100c01c0c0f05d0380320040720070303186d2040e16460320030907941649a8000200c100c1d403001201c030380c071880c071b0b00e0b00000204008084000018000c0005584d920107030705541070f15240c140540c04070440002d100307203411b01c05e03102e0305000c00041d01169000400112060b602c0100121a9187d00b800310101042d400c3c03040d4000030340302c0e0f200e014408696041003032803d41000d401104160034940c07415501e90709413060307c0c0c004001c0d062064a8841c07002d4180c8841e800d562540340c15601e0610000b41034101a4030850480c0d010f082510040342a40c0007110203041c2041c1c40780d01041c0c0c3c0d2081507100a11b20781c4000e601c03807125403641000d1000003000d40c040070100e5000c04000e50020a207401c4d070154610071218240382070401546002c11203090003005804101040c40c691801a00240081c1d0080c402c859403011400c01c2040146020314150005040c265000d50301140764882c848100d040c240300d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 533307131 1250 533305881 533305907
    0x3051306140108011a130216080304081c02070f150e01022a03131a0912100b0406030f0204050403030204080d0c030e180a09050c10120b06070b01060e0402250c06 71
    0x1018624491b01003490296016010145035078515031401d8000c5818400503501651240c4c40113079560b8213000001c07041e4002c1e01141a22680b040001a000896000030001002d030b001640c00800803449500320020080190200b6042d4000a00420307220b9040c02d00582c2c2202c0c9921084070007445440300c60b030303d016a0802e0344c400c00c0e25080038010010b48419001caa0f80800340400e260410210200f6021b4018007101d0001c0c1c3c0c003901c01ca0a06941d2401a98040e0b802900c00300945031035511503d5458101c850064001d60b500c001242c2494440c1c0c0480e00504000c60460305201446171006214803070040047e800640c0d0400100741601e8166074424680302d209a00320141d80310090740d00001c0c01c414408580f9881601008185074907003942d04481b0032102d403101d00f0740d07000201064040d100c0c070000151141324104288000541e800314402d040d0750047c42c0060f1036000160115000344503181c21181001115210f44814014003102c102000388100d0840c05001d80c0d446040e16540c400100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 533308381 1250 533307131 533307139
    0x60810080f120306040f0c020c010e031c18030605040302070f0f0e0c0a02100c09180b0d080c011401230a0305030f070206070b180f0d02060703051306140108011a 71
    0x2041902d00032071801a540000c1e000b00001121026101034404039610782844501503041000d0103c13240d81c10082001e400c03101a00500404105807000902504181e11100184040a00c5045004140039440809158000320411950405081c017035030322003061055070318060300308802080c1c6c000038100b010100c415003680368800da1911452400725400801c0190214410039440100c074a00c14060700d218280f407a229441d42d03a0400301c601c08100c4c4903820b4440c00a080100090380c0751180b4114543c602d80000003180c440c0104048180540700c0403d142071600d43d20000841d54000c61600c0510703c0d203004444e0400c0038030f040705202c0301c480301d40320241c8190401c2c082a1501d03107900008141c0184014060b40c0340211170358680802201c1560942101040f000d00c40840c0c0c84100856480c5501c0c4000400000030201002507448000030407100c00c144d2108040399449904401d4080403a5210f441031058800010fa4401101001d104003081c42d8203040740000200040403001c100020007034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 533309631 1250 533308381 533308393
    0x20d110703031d030c0703081b2b02070f05040506130501090b01080610080601050309030903060c0a26060f0d0f110114070c15110a05010902150913050408090a060810080f 75
    0x51981305003508003078031036254a200b1070020f094149c404c2c010260140000c0c00d0130b080720440000c40241241c8504070090039035100c1941885010412a40d107412070703c0440e4045526070707030800450181201e4040c032010a030f040a0011860307411b42d0f00710a0741c0c40c100703030780e0041281d94907006c1094401144078480041a400c001045055108030000c5038050000b1040328a0440080042450700340f086070342681180b801308003024150f43c0005004120144040c0055024155075106030310180c0c044c1009205450740c035003034100c0c3d481708600d00442c0d9030814840003602c80181090705c10103601c1c3c00b07440e0001d100f00d81701500407060380302510a00d64003c5c0e91041014207000c001c03130248840000300c400307001d209001c0e06100001004580c0310244100001b0a0241c0c02e441400400c040542c40003620384000d1003d804d46444244410701188480c5002280325181e038207200c0c555103d542c01c0c45405c41445034000c18180d80115440d806049900145044a560341d07150640b1040c120200a075940c000c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 533310881 1250 533309631 533309633
    0x11130203040b130c080a0305030109140f1302041e050f061e040902040e030412051006030317270c090f090304060c0507050d12081f09020d110703031d030c0703 70
    0x1420203403900c2407184008040c4c003a210701c041032078041840d60440005c1c100000501c20308a06018400207220501004001030424903002c4010030b03001045100180500090342040d50345a8120030407441205502240017400958000098002151a1800c4444800c0451070a0800c0f440d06550303074800e40c00f0f00e8a614044400c10010342180803080e680103486820342030140c40d040c0300400051070001010b0040d1032151410f903003421062914503c031140b074820204046a0000a110035183c03546041c140070741c2c0c1f03580c1101030b041211030306401c610352226407003042d2010003c2c0e07903240c01c1805c03110000d03d43d45e05c1402d41d005480031a1042d98540041c0070401110b4000c49c010310201e4071400580b07072115204c00c007140c084200c4003030546420b400c11100b901030681150031140c024080f1141142c0c81c10071340e0000c20180d0002d210304c0340d800380e00048496a100c481d60200340c00038003c0e030401c0d41c0e0709014240140030b00445000400851640c851100c0c4000c4004200d03681ca8a981014160891035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 533312131 1250 533310881 533310901
    0x3150c0f0e01050a030e0705060c0606120f0601060f02030d090309080f1902040c14030906010e0c07051c021608030c15090d0e010c120825020709151211130203040b 72
    0x41b000711001030303c00c4107800704081d59181c0182030303210f260300000c10300d80c504041080303202c003050f00c604c000c142c010135440c5070074800c0410f55506458250030311960409580c6000ca00e98030500303600d8441c0c0d40ca42604503003016400b854138800ca030200d100f00d81c44101072010840d258003c0250700c05201103076106d02c00050401b5000305000341100d04110045507004018541310790f10032070b4005a140c01010046c410f2211903004590056000d180090a190182c0d036402e6480040c0c41054100d00000312550781540c1c82006040d000101e100690109030344e441481750f80e45d42094000524900545a544060350000c5a01074031920b07170f980040500d4400e0346c0e002c2e100310032030181c0141004169649000403030004200b011010110303580e00308062400003807428110480030700304014100c003000340e41c121f035a001038800b0684d0301482000a4120000d04a90030610745540f18068409082d16414140403161004400314201a0350280311a070290170008100c0c40101c40080001c420b8001142c61004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 533313381 1250 533312131 533312141
    0xb1c03020a020d03030b0306010605120406090c050607061a030606031b04110403050a05060f310b0f070e040903090b03100521160807060f0903150c0f0e01050a03 71
    0x20190040e00d04840142d0042410061a5142500829281e070124203060504020040c011710b42071801500f0700d00a20040c000c4408040d0000d05a203464613011803d010440b0300b807078002d0000500b02a610a003516180000e000141000011254140c440c4811401c01081c094440d5030010050000b0046d40e400d0800030580000619800650b1501c86241c0f2903c410018405980640003d18108859242140c0f8054009100c052039041c11702c01c1c4680035140088480c04140c000900d11000783c5047c0c16140500382880010f4504520141032210298100c0712103070107019150351701c845099215081c0019216040801800036218a20400910b05140080c6820007084016041c05c6aa01d1000824400c1d690700d0050307641d904090447d0900400301b1400d071096214104002c80c06240400c3ca075280c214911545081c0102c2e43d600d902458441d81726107000d1980074032480b0321000c903541100000e041d40e00c5500040741030007010030741281c0540328660600038165901d914128030613404030058a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 533314631 1250 533313381 533313383
    0xf0d03091806050406061e0e010905060a050f03040b04020a1403030706020c1006031b050d05031e0d0c170a02130612061205030706230a0213230102060a0b1c 69
    0x1540d688400f281980da00c0c01020024049a6030381e1000c50400140004100e0b60020618203002aa0240004503600243c403502200c40894180c5e84440103894140d400d0720481c258005100c4001040004003c000799240380254000e840900c0120745030002043e4510104421a50540c418401000014420740042c5043c26444007a100ca20a500366520195400c58000f150000b413451502000b03074600180600c01080c0848050b82c400c3c04a032146503c900c18440b06441020544e001d108101f20540222000e04000d020f040084521048004002c07411001d5001690051200400d15441640c02682c60020075501544109850840306960000d4041c42203140140c641c9070008606103070114100b0b0710780c0a040559510350007481c015049550145540c40254a003070014280300340c11084469200b5003580006176a0398100d20600003501281e8051418a504214011202c10b003120000d0000e0a081e000c0b992184c0f100303418007003039810200740070b41c00800001c59100700c010031203035600640d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 533315881 1250 533314631 533314679
    0xb030f060408031005190e100506040b0903030f0403050106080d030911010f02070b04170c030d05070f020103140403030b041a031b0a1502031c0b0105041e0b180f0d0309 74
    0x816035400105080600e146c40807540071400d450b04201500d1012046580301c8458550402d64a05010010b1454000d900a05284c0003000c9054281a2400c02c121b4401c8101d01800903140c1d90799142903400307040305008525542c090018481c041e07900a02404406a6111814036039a600000c01100c0403903145c001c0208500ca00d8000180c5501250010005003900586e440c502c894070b6198107280c8200004958040c1e480b102408000395440426100d880f580300c0000d042ca22240c0c001200509840345622041c042c0c1002844101a010380c0f1400e1000780564040c814104880c11070b00c04800c031144480e07015040018032400b8103200780d081000c11940103110071051601c0f0740982016001c80030810b009039000144602803001d008404500414099405101054081000900a006611407132100003944a1100000c408400c041006844010003190300c40120700303002028030084e6080b00d4015251711800c4010343c20720b06038411205400da214003c506141031103031060003182c10000700395 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 533317131 1250 533315881 533315911
    0x60d06020a031e060311240d02091003060302010e041416030e0106140114030c0904020705010b090910060f0e0402091e0702030a0305091b060c01060302060d0e010b030f06040803 78
    0x1c0070154142c14140b2015950f00040c1682980341208485000c0d8001500c01c8003001200120300c1401c0740c1e202c14807441d11041540b50783c00c0c2a40c4001900840c40c1283d400700241030120001a459070099048034001d83e14840390700c2006040c0000c50b0780b1042c0c404080c0d661640002c12174805002c0d60403580c4407a290018865240c00203460849070f180d044180d24000542e4810595079124035130f034185c4030138910340f030385035042103400c9a41c68410b0001243c042c1d9004a200700520000b940300d03120040020b01026640e14110300d10f00e480e044a901c010002901d01880420440c4584040409036000c4040913842c03503c80d5002c1140410005090b00308a4480550807008240c83d1503403e4040c50042c3c004688901e84204040c081d520000c0540c40b07160b01203854003d1300c1c00400070010b0a2201594001d80d100303181e01e042800750000340c0010750404000290101440300550115201944600080044240200406441e0202c109814038268407400102c0c000c541c4a800840e0891400d21003982 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 533318381 1250 533317131 533317151
    0x3060a0b040b0d240e0c040302030d08100f0803030604151a0910050c0a02101101060b091206040b0403050f04050406081609060f1205010f0e0d0e0603060d06020a03 72
    0x249078800e400591001c04041a18280885103008a980d16202c0c150b01e0001483d5200450584169920803040d5440000020070b0300d460340c44e01210051a00038090301c0360401101c0780a01109001c3c3c0308100c04560f02e140018034680c100c1314060076211204061440c544403141080064480c503108800d0306010b66200040180316040302c1d9a115008140c0c84c0d4480d0440010441c1d181050684a4240f1004101c80d2202d510b000c9003c001059040300d00d0340f50140d003281c003140c20307801600e05500c8035841d0100105410300c10078060a506101112040b089403442000e468403220180c500070700303013003541000c82c0020303004001600f0410388041806062603a100e0014003580c9655000301e6454200b150004910702c1018130041c09000d04d18028440c0902d04034540300e200c000352040c0f099400382540d0381000c00400703420100d0501c0c4288000c2c0710061521000d140c64031400840c600c0420701c0c00d1a081c3c92401d151080e6845040c0c000c1c400c21560358961904006548400444000c15640f00b042078 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 533319631 1250 533318381 533318399
    0x10b040b0f0903010c0c1203061a071a1806130b012310032f0414030106150806010f0806010807110120090f0f060702060703020a0807050312161403060a 67
    0x140500c001c2d46c80c942c20f200282014000110710107420390030103050860038071a01809030b2000c00c0c420b001d401559a42c01d841d080008540c0c04075200c19040c1c29500c1c0600c1020101c00c100c0c00c041100d04000c2e0380301c80d240c0301c03a240300c11a0801e40c01031101d0110340c01082140003103202c0600d080da4201b0340e06030f400106800903540c1180402c000000c41c2d07440f240481140b24540703072099012207030460010005407404041c0e41e02c1c000c911500c84c2801e0f03007203c00b5980b0b45007904040024540903007040e01000703038003001900d01c0000f114120b00113400c00402c500f02e03500c1080c1982c080d00d13040e16192015107842c20101e03042d0142117110380c0315641f28405035100200c00c040716210024045850750f15071403540104400c1c1d4090b0803803030784694502030301d0000d00e5071103034100c8600d02d5040361984d0340d80420380b5042e0705014180d038018100071404114241404030200040c10f0803001d040031071b566591101041c1c16642009041e0500041c02e2640b4601112000710086801480040003c1840c80d83c9040007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 533320881 1250 533319631 533319641
    0x9090f06130c0f09080a211205040c050103151d1315050603071d010e0603070503030a111507050a120f110c16030b0c1804090b040515010b040b0f090301 67
    0x200d00003924120f181d140340e503401004000a400340b02d014003544180c54035002e22100418414110341d400c02c1d034a0b5081180564200065010401c00500c03c921f4142450940c02c500b80c460640445d0030808404030094144215405580300c0e03428040031f914991400b034080040080662094400794038016012450700019003090070740e41500880e040c50164103040c2454803a600c0284182080080c5100d1840c0113040241910405d6040e248143ea500c80001d142600c5580010b41600000510004290340114064501c07c140c0742211b0380001082041e80301032030200c0d1400000351060000342031861041e8400d19070380c0c48130040800d00360115560308045412640e00c0c900c2030f282c00603455810650520a81215010004001454901c1d64603044113100b001000c1049504000031140e1030480c0f11501202d050501a10401045030f0510302420b5040b000e0743c040d103403032081d040040c0000e419500a20305070fa00359404203050601c0c24034000e60315000702c028000c003940240180c000c0354400b4450 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 533322131 1250 533320881 533320901
    0x70204141009060f270c0f11030a0c06020a0903120e130c0206011208070b010b0702120c1c02010c02032416090312020a0b01090606020c01020309090f0613 68
    0x1030003a2410505010300704151568800441d503810102d003001100c01c44103420048581c0c4a28400201c1490031700d038068130200f2071800000510788140b1028043c0d0003214910b844105440326a600d840040380a6030380e00400c0d01c2d000002d04013401c00400510b403a0068550307508141020380701c2948994504000044080c04240003510b44485040c0030b05c0c0408809080c260040803c000c0400d03400380081d12400c0c14003c140c0c0d141842034140c0c00700030780c00e82282c41f10381c0c00001404565071690100782166101c0072090b48a4000740c40d450350b0b82000456405030301c0c24000c040d001c0030780d1102c1d035100c104444040180d040c42a0341c0d030f082001d83c9082c0102c118400351002e04140c600024021042545d8018100c202c0041e01589082e40403501b0000910a1b07980020804c40c0c4012100c80c12890006001c03001000c440104000250384840d90300801e059494a400392060803030790800481c0d032802108407090f4080741e1600812440c4141180301a04801c020781801e00141c1d034002014240c640c2030b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 533323381 1250 533322131 533322161
    0x302070501090308150a051503070504090204060509040b061204031b0f050c180f0105011815020c0a061809050604020f1801021b0102250810020304170408030d020c03070204 76
    0x410504110441704c3c4400c0041c11200707001c5042c10600881e00800700d240e00c2031400c0c80000046100c0e18016001e40740100a0242c040d0740d910b0315404000c241d5000014068082e608000001c10749142c01c0c02980c194040b1542f06841e641e54585084a0556040b40018543c400010b00400868506054202154000c20051900d001c80c8404c0c00079412200c840b50440042c01c0c1c0c10b011400601e03460240c11a0001d182464654040841081588000c0da100c1c002d90800c502030229084d0300820000744154080300c0c5089050398600d015210501000903440320461a03110501c026509580410381109021740018100300125108510317941c061103034040310b00546545c40480d50703410402010060002d84d0f58585c98012070002079030340c07420405071300c12413021100070b80903442c52403114000400701402161480c00c40b0108002c029803058a00f500d450200380f9203a008031240c2e00032101110885c0005621701a07a039085040250000440000140004c028910240e41c2e40d005200d04401400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 533324631 1250 533323381 533323397
    0x62007110f19080a0b010923090c0915010f020303060f04020705010f0203071707020d0f032409090605090136060203041a060906030c04114f0302010507020103020705010903 76
    0x200b045c6241c0da00503406041d04500786610204424038940020390b4480d944003200410361107218000c0e003411344100b0741c1c9030071000350702c03c002081c290440901d030681400c0e00c440c925502070b00c0c022600c81c802143c80a41003a00c40c4044001c5041030307401001e10b135004000009105103046051021782e40f06403075130720010b130807003021600f03081405030b43c1741c2c0262a60000b0301c0080c6144c1c00250918bc101d04500041c580c1d902280031610103403081031400041c1340c58034000d5050721800c0301d42c01016002c0d01654801c4c84c00000500e081014407850041050301d10f18144c54840030030f164070210228043d4a240c1c4030088603003a00240c05400a10700032440b0f42c0184400401c13541c176030380c01403100410446c480c50f6400705002003500c003c1103111900e00203071004990744d0b000d45a4110b0600c00e0a2079880c4080b40c1000c5000d05c2c04085d9400c0c0300b221107840401c2240c1d500010807010034450600081d11107250307c00d040005600a80040c5155403047c10054104029601c94608482a4080584c0450b00034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 533325881 1250 533324631 533324633
    0x1a0108060115050c0606010302030c09130c1211070803040c0906080102071e02090f1008060c07060b090c04090c12020c070e070306080a08091903062007110f19080a 72
    0x90314075440400038644a81045451884282d1710400548403d0601d54000041541c040104040300c484440107030180703080644000c1808014402c0708000d01c00620901c10840301d503500c900400d0a00500d82e03511a0509526403903450803940054411191030707e100f540007400441314050343e40102051320006803100340320f00b440302d41019500c0b6655520300a00392044010307a190811240c205107000100180d40d6902c0102c501d00ca0300c241c029401600c00d580810014078920790052401500c1406c00344144131403001404840c0c80151440100588140011300c190600c075400241c21050600d0012003000c2d026000d80101d030b00c421494903841d04070102c140400181220326a0700446140740030082c1ca854011001d40b1900208401404c011002400c0503260f55035001d26501003030352107619901d050756490321400034803501c2085100c2c0c4000d49040c0130b90071a24030a5803100c642080c50302c00305907090003c10048806900019a11020601c006001602c2088040c40074041c07007030040041d0005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 533327131 1250 533325881 533325899
    0x303040e1303020111091309031b060501090605180c09150c150609070c02040e03090415080c0117040f0c151809060807031e060507051b06060a060c1a01080601 70
    0x710b1441c3d80a17604200409030b10703919915540742c81040e0070300001581d1a80c2d4078089400d40c1c03980d424a8140007410850300188441c1f40e2003a8101c510800041001f5a6a0010b100d8156551002c01340c50300e00316000601d1100c000d10040004001c004d010411034000800146e50035008030b8901e01032039100c20182090712030380640280e08910100c40301c0845150200004000740117000c0d00a0080d601c41c1d03116079aa11003003090350306614008005002504c544814280303007449030b21903d2203a10450008245d61350033260010b0780c005600303944440d55034440d1285403d9480c040700c00c60b01400400c00001e007801d48e40a4040b1302c000107030b031703403810000c0c040010203c4060513403c407800c030904e014000c015402c00041c0010403079621151503481081d00c1400c0c0352540d0703104540035100f07500b45001c001005902400034243d21a00c5048a0850040305100300d1752410100d400e650031200411003844241c0c0a216181c0c1c50ba8460307044050212003046500041c86401e900c01d09071603001d28010b10141c14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 533328381 1250 533327131 533327141
    0x70204050709030206030612010e070b0a08070305010e04200d0809010201200a080606070501020a03020d0609200309010e100903020607020604111c02060316030b0a1805060303040e13030201 83
    0x41c10314000d920a8255000256031740b002800191040c58000319528104400f07402201c5180112b41c1907500d4540e07204c0c1c150942d6408801141e0004292800043c0741031b000b881554143c030381481c0c1d4010a5a1240c1c1c6d41103510004640314100900351100c0080c041eaa4101e00b40c00b540d10404415440f07140c90800a825a00005c0d0091416202400c031510141a08000e807900c040346031410310429110040170644500c1862400340045d400014840c0e443c0c0d800d0780040807041c01075403003000b005a4070f1070400c0032a545c143c01c4102e41038040c10603d41c00c24260018540020204000003034103480c182140d03180c4051301c0029090141c031b8546410500d5010711140c0d6001036180054041c0b46132a42e0342c0208540054542d900c500c40450302a041010104005070400e42c0c050151a6a42001d415010003041d001d00c1010010b400c0418800c3c0741d062022500781124229011485001d43e41502603011308401000a44c041c0703c1800006221146000300318090600703540b0304002c0300454280242540c1d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 533329631 1250 533328381 533328391
    0x4091a0306070e010c0206130e09010204260c120304170c0306010824070e150310090209010504050d020d0c0b071104090209010e070212030c0406170103170705010b03030f07020405 79
    0x700c0100043c00703482c0d8008114805040d812600665117501101001c170140521340c0011221014100400003d00d10540c003c0c004d551110014503030742604203080c40741c0c64480c2c2a03180601e400c800181011030a207040e0408450940a060302d00b0551610610300700d059800c422000329512456003070700703141400d202c25405021204081d0184807001e052220701c100810072015203240c0c0d810001102c103031081d840711072041d0008000c403c41e03420501d005082a04141c90800c03e100d50f48500144200007882200c11805041c0c5030982854078140c01c00c02c807048010700c140d8204080311003540c0000c1c1800da10728003428103168032640341c26281c20a0558a035070080a01e0246203400250005640d40c140c03444d0440c0d07500040e10160f40d9641e00100e08140321001010742c03850011080c00440c41c0c0d400f01800544050342c1d5108070800541c0c06a1031751100038031024000180c0032442c40b4441441e14000e2518a002e41c001044402c640d4000c01d242d41d104120b107613031404011031901c046241c9402115000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 533330881 1250 533329631 533329637
    0x20d14061003030e0d03140f0f070c0305010b0904031e050f0408150f061302090d050d091712030a0504080c060420180604020d0b041812020f0d0e010504091a030607 72
    0x40392560050000c666216510700c020b100462610030b038440308800c45000c550080d09c0c1e180c554019142050000c0694007045441e5420304c20400032a05005140300d1250b034040d07541183c45245a000300100e85101800301c001c001040114030030003125180100020040c440c01042c1d0100c1308844091030741009021a1095402001404119a103075504a02c280201000060b03a410085e000202001c0114000038002d01924006000c2c06400c011084110b4441500c0e0840350242c0c50b003015102e032490011400c003c4414070109440c1001a80b080e076006100b9841c442c40d103800890020701c0c0c51005c4508848518201401c180ea6645038071644c45071142c2a1645207201c07083e41566406c10324010089030041e540070650440910715500004040040508200400d400800749135103513461104094401251a0451000d614400100e4190552103580a0040186d28420444080241d03000f60b0381005800d0001140f440c0e1248a1210303009504101c0360003031403140c0700780343c10540000d280d0760074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 533332131 1250 533330881 533330899
    0xb12040507050d081c0f0e07050405010617041707050f16060f0c060c0e0d030305010302040b06091f051c0f0b06040501090b030406020f04031b14010507020d14061003030e 75
    0x5180805445124a85c070003010103030700001d41814000c3c810419501801410002030740820300c40810035000f50b50040c2c0d800d015980c0c0319a8142d405140351030f040c8440903070800c0020080384580142d004c0c0d0500111041d8034056031a02d49501e441c02624a00d42180c100c6400c0900365401040524020481800d0520302101d040d00060b000b0182d00001074005138a0305801c0c450311f8403418942c03841c920020982c14484000c1e0800400a01c403d01049000b1458200c44d14800d20700320b01030b00c2c1c0042005140c0d80c5102c485035180403603404046240e10031300030103004d40d261000e5000303000e08010311441e100240409880d4a481300350307000300c2043c0380a4a000c002c01c0c022a40d025a1800c1601e022448079a6251a189410402032003040e1000c601b8403c082804801c00200c0803e0354100d4102004507414182c0702c0740c0c9040d04920059005020541c100003400c01428400c01e15a02d190007402c2101c0400e0744c40400c1c0c0d0800030304490392031003002030303140c01c0c81055041041102122000c0c0c0c1c03000c603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 533333381 1250 533332131 533332133
    0xd18050109090203190e150a14220602040909150501030b0705130f060e1203040b0901260c0d110405033403031e0302070b0f100b12040507050d 63
    0x5601c8060146102c8a03400000041c0c5141040e030106240e83c00c0c1070f10810000b5020402a80c42d02c1c3da106d180451440c098006c106100b44500910103254042c070350200307040e240c5400b4030510103a150840d1035005640741d0042c0118203688050401007100d0707000031071014401d180514962035074050460f86a4030704801840402da01d42c03e840d80c002d078681800b55032549244c46400e0300110380d5211240c99004c141004c6021a2722003682b40800409440740126001d1000c1031075100d004600500f8011141448003c1e899071040142904030440001c100402504840e0302c1c40300540c040300c0000c00300d03000040380e0f80b89482610a04a5640c06524054201420600000d4407003645000c401d24281c800c445196040d840145440c4031048801180c1101940da49005061030300f0480000c0392110900801c1c003040350080c000c580080390701c528001d6641c1c1d100c1083c072000340000342c100102c0c1040d0b244007040c0c15104030000c00c1065080149182549424a800d07850442140c00444c028511203003618 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 533334631 1250 533333381 533333387
    0x403020705040c02030904110a0305010f120f0212101d0f070b1b0d0305060319020105070201110f0102040b1306031401030303020307050d0518210d0203190203090d180501 75
    0x40c0c195401154003040515048034100d180d4040c2c8148585c1c0103140c4071400581200660051016000701d840c181b003140ea0715400c803800040e43d0310845008501180b01c1d42c001880703030020200c0040c8001c021014980c00100000c3ca00b500034598a00d03150740e00d584c01814441c1c023000041c440b0b410345008040d240307801071189450320458410080c0c00350300405c7d070113803010030005021108172803441100d4070041c2104005001d0081651540d0190080800740c141580c00e0108019031240c040c0c4032f1034078007003040c0d0044450020408290b02d0070b0042018000700048280010300080c090b508855844a5a003207171440203030141c1e03106005040ca01182c1003c58003040c540305044a4242c00c005032640d071b8410094505101e01d01d5102040c51030442000301d0744600780d04249254144208541d80c546061203140c10070000210782034408013003030140d008034480b183c00456120074100424020039098200b028140d80041d90409045d0700028404ca1419a01c0105802c007c0444645d124800d4078000c000b03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 533335881 1250 533334631 533334643
    0xd1a040b090907180e03131d240103060306020c070303030b0a060207170a1b06030c020d050913020f0706051609050f01080a2c0d1e08100f031a0a05040302 68
    0x440603600342245111220b07061a8003010034481c209085d42c1c0c0c1c0785600c207a1f03852501d00e180944903512081c1d5030509002a00364650302c0c8682e1504814103d150f03141d0300c03924180d12000041384d04264441402000042060000d00b0010031020018800d007405e515001e002c1c1c6c1d024801c154001c00c60820104078880e0300186446c01c45440c42001c0c01842c030540b425508043c0d02c8480074054000841c2d0348000c0c00515841768040358155681007000e0b414030581280c840803001541c5000802c18800b42109181580c141d0848400101d80103180c25002440d44186801600064546507910000c204894440c200b000d400c04c1080c0c500658841d05150000b21200d500310700b218100102400040c200f040d659100c7d1901200800d007402c00310b2695062503006078203020384803c0d20700980603200f02140c040d010410b60212141c00001c02c545007400304aa9518004046614070030506c0b1740081c1500384000640055405480035041044400d9512140544003500c06406640350408001c042940402d030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 533337131 1250 533335881 533335889
    0x300606031209090f1017061b090a05060f04030b010f050a080d02070303080c0c030d0b0a061103040320061c0c090b0318070801020a030e1908030a110d1a040b090907 72
    0x11507080c0307880e031445d00c401002c029007006100c401c1d506000641d604000828910034075224003400a0581c2090a02006010b039a0b902c03500443c01820910162401c1360152200010010001d42425682c1e1240b02c141d4030301fa8480840f01100042c11b00c441d0401d2000a00030b050384030010010000c01800007035584505102c05800c1000042c081401c40c0c00340411100f031f00b60318508480c0c503050101e1001000b0060301c02d66a204140c03034071000034068003c2c0495907000d5030040142d0300b030034a1034886164150102050554001554120356010fa90300809810113001d001d0350303100c11346480c03100e01c02241c3c4110100824400001820424041c0300c2040342d61045011441c0408040700340d00c05803030242150446421940046100c3c0e95440c1c0c15800301128415103000ca031172000045000c025640038a102c054110041000001d481c4c0b00e494001c01e8074605215004c0c0d192120282030002140c824130068000c408107450410001c0c41c050140345603141d001c8030250300605010554903542c4000d842 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 533338381 1250 533337131 533337151
    0x2e030e07140402070209011e05041830080f0108160b070303110f07051c0f1d0303030f04060e070b090d030c06060f0e1602030930060603120909 63
    0x1c00d045007a111901507402c0c856010702010b402e540c642c80c20b08900d0459200e074211080880c0c0000455180ca03020302543c130030f888c4150b480003404903290340d807109984041600700421640c1004996141424030259042510703034907a00d460518507480250840306a010030b4055000418003101034003900c104034110b408134401c56540703c005103015005042c0030403640c100c1400200d151401480414020613069210394182c0e01086001c120107400c242c0507a01140000da8140c031003031001405140301c0401e02c03046001c20700b08180444c000030300e941c1c030440340790390704641100500081204501500140b070a1010290900605081900c0014010f8950851144800d00008414940507001490300680c001805004490311940c0f07802ca0b908442c4240520381c4000c1000500305007a03d084941007003100d070301551420740001c0c10031003074a40c01144400768000c1c103c9950082d1101d000f6100e030244041c806011245020810142440c0b0051580c0ca200301c41007040d0f003410399416480c03a6200140403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 533339631 1250 533338381 533338409
    0x141003031403250906120e10020c16150905090403020a0204020a090513020a0905030d121d03031f0b1615060803070b10050a0503030304110402092e030e07 68
    0xe10f03401c644840c3d60b1010002e503944000001120b40c041c050f1001c0e920180c40c2d5035481c0e0030480a110440c1c21000aa5101760040c2c404500c00792242c2d002045004071042c2100c80d8070365101e042c2d105010341a03010b00d0000c00308000c1503551542020501006040464190481c0c0c03a0a45010391907043c83d0b48003d100d00d80c0040c1801c0c403030303005a000038050007018100c0720b10703d054152104000c0d80144000b001003514007000148510700004c41403030448143e91000d00a4101749107141c040c0402d0241c0d4100083c21040000f800c480c204065803148255040400407080000e5840d034041c00130703411141e165441008400303280c040560a0b032090b80d41c130050868440c05412400c1008010755000400c0502000505405005200c1c4038940503000c0e0101c2a4022075a0f00200071244115104154045d0810700c0001c001c41c9501c0b408208800006c3d02c05440e1443d8900099089200342c5081c903181290342040030200140c01c501c0c0040c400403230404109010304058820b0742c079421440780300070340a080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 533340881 1250 533339631 533339641
    0x6040605090111071a09030f030c0a0f0203010b0409030305150301181407080a030c050f1906020307030b120106030c150503061210090809030d09140d0201030915141003031403 77
    0x40002c1c1c0e0041600c0394040701201840038842000d03034846c120040c403e21500710045617500c004411030f2000580b010080c5070f00800c50351215200207541d042607030306542e91891029551218010f06040b648070f070b0b0b00003d043c40d200c0603685250450b104142d000b03038501041d244145400428207968150051035003107210058958903840d0170015000480c081c024500d84004240d04884822800d5100b542940c018076039816030940d4030f00500b00002404c00d00d049100d008100c59500854008005180116510400c903020032042508a0b0314206160355542c010410700c034001c107051018008002000c60b90340c0000344001c003180006032403980f00b8480000b015001d5030040114070000b500d0b40e841404166114107005003150400701c9058040d001d0b46261910041c4a65403c00680707414400f0004002d2019007803001d01c00388100c04906142ea94441000861520055030210b0068600b003c60060581940b0409424014100b8443e091010703400380700003504040c2154a03129020b01a5442c0d0b0383d9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 533342131 1250 533340881 533340883
    0x604140f01121439010f1422140f13230a020d0e0606030d030519110c071d0a050613090303050912070b0a0506010e060a03050609010506040605090111 66
    0xc40543c0341644d2244101102110b000b40c0c0c2820907240c070203443e10703c98000b0304101d90303031100060f8580d5000640441082042074000c2c045544110075103101d141c10484041400002e906558488580c0386010240c10450005024200200c181d0140c5041e15045a04804541d130540340c6850320403903d80b03900020350414500d860040c3c01008424105805042500b00c4000a5210406403001f4904110030b100908078001006402480e02030020460781c02180c008074000d1401800480003140178045c07070701c00048c041c0151500d9101e8244516590846603030464501a0258841c0c0802d0320025503601c0c000e80c0c800b0b40e4035030002c41d8100110f243c1d50ba40b00001c01560f040d0605071009442c0001c040245030340741d84414880d148160490f11601048107098140d0b003d0300500a10883d01000010b44003101c60700001c1d08114181054a0902800d100061480c0c015007805400240e0b40c00801c501c0c0d10b0403011960041c03400b035901e40e152504051004006229003a1194180070801c403100c584404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 533343381 1250 533342131 533342153
    0xa0212011104030b0a051803090f150408070915150804111c02030d0e0d03110708121c02040608130f05100212090106080618031c050604140f0112 64
    0x180e107110090351603440e403500c4070101509079070045810345030800141c60410000000c456940410000b5401c011003c0100690101101a003642155407285420044050b40d4041c0000d80038000180036a03606040b9002d00b295425201003407046c00d0140c04015005100303120790a000050301c0c00091075039441c140b056680036030584d0240c0100802c0b01c2c1c00c0d03680c40c0715210811210f208030150b61481c828400101c6489503a10543c1c0d03031010499120f000020b0180304204510003c14066508141d80c414105041818008480d0442100012001d641d242c60560013030803000e403044d08604160030584020b0007440005c052099294070896034509020342e0b0350f6024401ca52007011985115944061071010b500040c1010070640755120101c0d4a404040c003540056501403001440701d682c0f0075041c0e80d501d0b82d0200b1b450880d40401c1024421031782036100304928199007100080343d1030810009000807200c0a400320402038a550052144201c10880f003e811140398038a140000b890506254101c11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 533344631 1250 533343381 533343401
    0x10f27020619050f07030c030305162007031b03350f09040e0304061b080702040c141612030c02070b09040b040204080109170406050a0513050306250f020a021201 71
    0x101c00070805401b00340c3d1020910700c0c254405c0d60140000d0b00e403103401402c80440b030114403000c030745a13443c1d61114106420b145610111104210395a0b580d0f262900400228104072507020701c00340b98003d0080c48900b401060103115400044c00d0304510400300c0350176002003804e00c0c2c0c81940700000c06c010030000000c261101d00800a008111141c0d541d0340003541e943c032522412001c542e2411400f48400c10040060f000250020800391600040ea42004024044100307510b06001c0d1142100c25003424182c00713849119508440f504404219060000c03854480d00e50a00800d403c00a14103a005d9000c40c60b041243e9503201941d860b1035a0600080c043e101c0c40d000c2d03d0f0001e101140000b0990380c1500a07420361801a41d4103155034181d40c400004912603400b9060114404214224105220b00c00404450007621200038181d500c2e04000b070b040c00c109482d4408101580c1d0610f04801c51454183d40301d110403401d010140c0340c28044080c3d194041960042c0c811b002c03008010b50500400c1d008510300b8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 533345881 1250 533344631 533344657
    0xa05030a15082514060405100c15020901120506010c1407180501050405010902121b120a0507021225020303120903030711061905090c03010f2702061905 67
    0x43c1c540203511203842040f00312010755030078000c0800559021001d83d114180040a80150300d410b007040e06221031109541042410011401290404180391000003804000310205c0580d80d00550b4000415545003400101c008626010030320505a801100700400c00d540500b01072011084800103a003070502c0f0b0303170181000724441e980c1c2c040e00c1c0c40140d12250580c1c004441c1004140d8880440c90103d010b1203003822080310030345000c40c41c0140400e80c480c01441a0192075460304000c80814a1015010f607203500c0705540320700034000c42a03010304c490f017840d40304182e01a04000840720700709441000144844103d52820a24009545050013101d81010780085a45494100740c640c85540754803ca82650009081c01c2c0440b14140c40819403900070122911201204004040d43c68010720340070f8a010118030414040e91440d48007130090b065240080303100040d0019500c3d40310310003507044400c0c0d0f07040000108400c1006948110649462180f030a00f0300c031034484125000d880e00d11408540c40030b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 533347131 1250 533345881 533345893
    0x605011a0724050921040605070b13050102070807030f1701050d0206120403090f1215020a1b080301170601080a030804020d06090f0218060904060b0303092d060a05030a1508 76
    0x3e80b43c000030701e240c00e4110f0040400c0d1941d048029150181c0a47e0140304c000030010003580010610005103e900075840c0da10400c056a4183c0c3c0309422039008000032210040302041c2c1000b450342008481c0703000825070400d600041300b02d8500145140050241c10b115190483d0a001551220404d64250f290341482c0000030341001e0802500e00c05884c401d002041333241c28404a100740581415498040e0320180b40759801c0f0062111801070f401c02103020003007007803940c0b025001d001c140a0701820342e801031004a659505000c3d41d40c900e450001e2803400c2c00c0d4494001001130000000e041e00d0a41c2e01854081a903842c3c0e440090591481c09102500c043c2c2005c81d500140801d200644803424030890b41d03550700320f51140d22141210801c030b449940c00518000041c0226880c0c0c2c00400d12120001c0940349854100b8000070540305080c1c112651f14540010550705608444004a00500080301d0040c01e240c41500010f180303200081c03107003000940724807001d1808403000ca9068013400c146d20a0700e070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 533348381 1250 533347131 533347141
    0x13051f080a050c031605010c0212010c03050114030a15180209011d10080c0108190609020301170102040f0306020d02040b0c0606010f08011d0c040f0605070605011a072405 75
    0x1644407007401040c1c2d01c900406104203854070380001c2e00320303400b110429040c00700e03460300300107495840e0504800e81e00300c0d40940c0f141203001001c1c4a0b20f03601d61425100040d6035414903204c40560020102424000d500103104500030804c464190206c0c103005600202e01c44115010900f489620220003e400142c090008143e0040c424041125031100c5c0c2d0751246c0a540d60382e0200c4040c66076101c0c58a5a80000440c403c95500c82c4160940c81190301510311040c54500c0c0d140c60896070f00e40e01c50001a0b90200c0103000c107903075001140c01c11920041c020350421707041c01100b0160b1f4000d8030009000b684c0c00501844c0c5420380d50107441c020540151501c0c3c803901a070802c030f5110710b0100c5096000468004900f2081401a204035058070100000400a100e0001045c69003c001406607010b00d00e080c0700c0040c07041341a00d004d8001c0d00082e641e484c4c070383c0c01c01d1500105440701a044020b50000703040c1e0800d01c0c1951382c815248816000501034032100c3c60701141d0381c81c200d0300e1407900050a05041c1000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 533349631 1250 533348381 533348383
    0x20a20030717010c08012105120d060e06062107090f030602090909010501150311040f0f031a0603030a0309060902132c0c0f03150f040c05030c13051f08 67
    0x58002d41500020b00400c604a8030899031034030240206400c0304c1d14001c2c11081ca03811840c4c0d10380502e11601c03c84240d0725038004000703116000801c04c852526207805081c001c81c40f03019102a00103d040d9205824403991844600c2b2143c4c10044e90244103031200001030980d031141c00072800404002250410894480c2881c6000e94003090701240200c28520101e8500710b01441054121103191420f40440800385204402038011000e000c080714a0500012440c42032000754140103201441a042e00a450b600d421b000d21580107080c20714072880c0350100000f83d2408011070300242000c4c64002813110140c6840d200a003c1c10b06d01075000045114081e848040c0b07640460302c000b941e00700c05043d110b4400d24510715120706000c8c000d40c036045034030b40c200c40f414079181a80411360020113035108000054110f440e0808211807481c400c000480502041c080e03041400000f4000c150060f0010401010103c1e240e221042e100101680da03820000d01081c0703400d81c01130102e050703400410709500e0b80c0d51b501d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 533350881 1250 533349631 533349659
    0x3120c030315120706080604091b05010225050f0406230f040b030703170c0307030f170403170907090e0309091003021c03020309090f041a07020a200307 67
    0x8503200b8080303400026114642461040310b250491001040c600e4184101150030319006004160403a03250f80c4840e00013809a88003031500b0030504583d6010510300700c002846d02c09c20280980d407986c0826003144100c0c003503074034038010749105a0340b03020b83c4406080401d0081840740d1042070b0b14510101c084242030340103031145081c07200131103500c03809103e0002040304507402c051035a545a809004104005800c0000d00d0340c011411049583c188003811410508541c00582d003140020b0b2200200300b66641c120744102107080b162080c017a1140b60507036001c1c124030900d0021150400c3c10130001290080200401005044030381d4080c4000032407108a00d80e650131400d0034a1207100400000380c0d00d4501c44c502c1b48210384c4c000308030781481110319543d4607400740460401d03801c5000402c66851251a0041c01c2d0380900200300720000d40349007a0420780c3d0071100c40d1203080340541c400b00c24020095800a8401c60300350f04a1000c20081c2001100c005007448031003c41c6070103004500d800a0352000b10912 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 533352131 1250 533350881 533350891
    0x60d0507110f280819200109200d060e030903011409120c0a020904030c02040e0a08031504090b0103050747070605010f060f020c0603010603050603120c0303 69
    0x1120100c415400455032683d03a0150f8550b07410400c150b12600c602c2070007002c41505802130070414038155003680039101408080070301e1008144d2824010351803079641180c0c51094a9000002c0060400d80d940b050360001d242c40c048038910681d42411802640c03106151424603a0181c0200904250740250725120740040520754480d51a00b00c440003440300e96a51030b84504440409403608604041424a454000c411000c82c248030302d40c40c100050f02e031850014011402515101202c00360303841003005940e402c9501c40290b0300044207103400581c50a090b02d8010440101003200d002c540404500106a0080064400e0303104034000014040301050100a40340b412040c0902d80700410740c540301162031208125600300000e00840c1003060a1510040d005030003000c404c2c07500c40c1e243c440d40140c03107081c1c0142c041d01c00c40c4442003010b503802c0101111407100c1400900100081d0708001102c80c0014420f24041c19141e500003451035609028400c0303241000d5012036101c40d411408240d503604202c1e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 533353381 1250 533352131 533352133
    0x307050c0f011a1905010c030203040e09061501020c0112110c0a060e0601080f0304051512071805041503060908071406040b01170d1101110f07050705010804080f0702060d050711 78
    0x800003c904001018540085032180d1404c10300c1e26180c011140c1c1001c2d5602035085010500021455007181e041c194040c86000c40200442e0406c02960040c0c240d1000d00f40d81591b0100200c0461640c00101c1002c20341200c40c00080ca0682d440f640e03071030900c01c00c2c84003041030142e94615010441320383d0180341a2003110b01100c6250380c0340c9410b0340d540e40d0250004c1d00c0b240c1c003c2c0700400242c9002c0c08001031900307040070504c2c02c00007407010900b2541e0050b100071020034072202c20000043d041842c0e2070000c043c1220140f004102c0a2050b030340d03014035400301a10142e103908041007800290350454100540c030165001e81c030380e91070000580791541070f90105c0c0c07284d146000000b5034000c09048003280d001c00368050488038920b0203054940542040400d1980e540341c42080c0c03400414100a0400e145065078402e0b507440301e900c0c02a09100c00c070f402542c18008002c0a00000c20342701c5003074335521000100301507522031103070001030340d03034012400b180c0c800c282040100104181c0c82459a000c44020f48 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 533354631 1250 533353381 533353421
    0x51009020408031c09020603281e0c0e010906030207050703020d03050d180201080705090f061902011808070f03141303051e2a040203041b060f0f03020307050c0f01 72
    0x24018030179148100e1020b90303c0031007400800c2d02c544034003c0c00d0b201c4108242e80f001d0a01000c01440e015181c080a20304e14001c803042c101d020541d59805000701501880c0f81840d034081d43c000003c1d0003074030240909003c1503400310b03410013042010059400a107400522079842d4000d0340c0b500400551141405142d058105540015042605007a4906c260390503101c940b8296202001194260412030005034131040640180e0103e4803454010075003540c500040b080c44010180c2c0103801d5070340d903200c8d4103104000a0486408618070f1001d035002e050b4010b01c2c0d900460444c3c1000c450108280c0d20103600c0c0c4500044200e0310840310003502049a20490a0b02d030440c460101c400d50713055281da0301240ba50443c0001086200c6560406110b02c00d40c40350034080700c1540c40100781282c1040368229030030201070010b00010503401d04508000d194500e003103541050314500003013003411201d286106041d008400f11b001e00d4040d0042e42c2104800104982080320b241c105603010304030189010601d03000f05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 533355881 1250 533354631 533354677
    0x51602210403300801080a0201050705030909040b0a060e04150509151501030b0906010914121c021516030c121a010e19210813030c0906140405100902040803 69
    0x54007103a41200c06113805480f800e161a0010b664580c4458bc0c12100d9000402c4003d00513034980034441d0056000e0355801034030f403500325104000c90b83c05401202840c015102004001903c0c0040ca1101c584441d40c04983e41d120b05041610380403003c04a01c220201c0f078001c102c0c6600240320401360410090340c0510211003500140070881d4020341e221400190148410301842c00001781c0396101a40c0640703009800d00307000205070b08016020341c200c401c11210074401c880c0650b04211441607003086011411160804440c1e6000e86011024100241b540f900501c03c52280500340a5801060403013040c44070200d181008070404c0003040000e030114066510741802402d104600401d40d00101d452414600e040402c031980080042d00f500441d004080705420006a4030070180c402c2e12180c0302511546819803425195040e41500903104180c81c01c0000c02c9100306488080c02040d40a0b503002820341c948503041d80d0a070229801c124000d6000147c00142050300000601510703407940d0042c1000925 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 533357131 1250 533355881 533355887
    0x60106030507050304020f0126011a04050d03030911131e0204050a030212031b060106090803120a090309030503040807060e03070e010b1b0d0f0305160221040330 71
    0x8181d0b480400a04103100280043c03e101110443c010814109600c04458801000b80300341c0720310722000007521848004000540c858041d410381c41e064403004504007030400002c10038440c00407101a040540715200705050003000544104107890203840301c40711400600d42c003000703080c00c43d51740008000500201010f1808501c01d4809880740140941d140303038503540800c01d04094080c40c000d02070208202803411212021301c480700310000100500b420350316104010b011002c0341d9002002580082000c203800c0703080214100d5100d030001000241c10b03811410b0841e01e40b4407a800c010840c2c400041e0114001c00c0010f003500445030a07a81e80004603a940090544800c0c2030304c07070085490340210052100d01035880250868131040408646408421108249012240050070b00403030904440c0303d81c100d903d40191580032026a142d040401c65503e002542c401c51002c04503000002e111100c0140303542c0318200d0f002903400007042107810034000c0c0908030700044454400400e007075800001c0c03201e40c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 533358381 1250 533357131 533357141
    0x71137030302060703020c1609090b0a0c05040308030717070e031204050d1112010218040c0305060a050f0d0c0312020706020a0302060a0c12020d090c0506120c0a09151106010603 78
    0xd450b034040c005a49461006401a400c050701d21b110500036142c03107130605c0b840f102c10940100020500440e101d01c882c10b12822549000e0000582c046c10300c10114141601b00c412141143d074400c0009650390756214003207560344e00984c800e03000c00d1003d60500031a1640b0070007524402400300c05a84982c404010300700380d9482a8844d1a420084500c0c440b8007148081d100c1c110201009000707080e42d2080b0141c0e081c01c90b80244201c01c07850003c1c0c100041641828031480c40749030b0140c1808c2026013446400514200104c1c46041c0c0700f013020442c92411610783c0410280f1443c1d20819501e07506450f0b107400e03901111140340c1d01005204040d000520a032000034402ca440350140c02400d00340c1c440004401c00b8264803c6a403081c040b510070303a406400f010b88010181c601300000c0020700030505140182e160201d541c841441603000b0700800c40055410f001d400d41002540350413607941c05985a06540881880e400400d030303501c1000c40e05454503000258241c400c1c01c02410350b24241c1e00c881042c1c0480d8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 533359631 1250 533358381 533358383
    0x140c0a060510061d21060f1f1409091e031e09011b0816050610090c0f050711150a030510150e1318021305010303020c0607113703 57
    0xc80c2a4106088a0418040c0b88012400c1711260f242d01d08059105145440c8054035081444001e0204003e20301c220720301c03444500d800070660f112410b40340074500c0d0411410280080d10030100200455205c0604101094094400c0c0c24442034200c0c0781c4800a4503a005040d4000f500c2d0654100100c5030752015044520b03951050315030b100001c0000c04505400001d4032000c458408041000c0100400391641040c9000e209800a058a02e82071000d0003142c4901c0c0e114050322400c10180483c1c442d00034046145c0e00c406460b00e079465500600780701250740c00d8a5201500089450000c071045c0c200c01000300104191500c062029032100e03803140e04c400020744509120b8280410314500b00c24171030185d02c28640001044100c200c1040d0622908a03107103484100c0d00c9135070b25180d100841c2817992100c079804090352401c221035890b46d140a5102e408808800e841014001080c1e8101b18944928450aa8015043c50040c0030b0710f84590009481d25404039484425a1300200060000f00955905407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 533360881 1250 533359631 533359667
    0xb03161a030c0f0f0423030c01110d030b01030b120105041218061d12010507020c030708150402030f011104030303060e040f0818120304060f020f0d140c0a06051006 72
    0x108000002c3c0320495000000149035560081100045100e00408013400b45214062441003104440341050319240544103c141484040c001c07003c05d4a501103500c41950744107043c00714800e00e815004078020002506080d03880303502e030303060012091415442180301e2803094042248400030070000307a80c048040494418844608082402034178810351302c0703000441821346090701c4000c1180c00641e44ca95090780c00800d40c0c0d503400410244c241d0400440440420035400381c202c0345e090510260310b03003004820151108825201040071500c0c20000e1a0080c015100208400d40450016511a90086c031050b00068140302005c22444a1208007034041e5074071084804c1c075038580e41e490107140d40005046082d025800c0c040c9010030b48461380c20071042000d100145580b00c5c10207501801d524002210b00381103501111002e0003044002402c0900e10505050402036040e09080b220401d12404010045500400811001300145600b20a0194940490303c40101f900d03113008960701440050030302c03c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 533362131 1250 533360881 533360887
    0xc1b06020708122a1317030c030307030b03073003050c01060f0509101d0a020d1d010f02090114160215030a05070207030b0606030a0b03161a030c 64
    0x211950300400c01144280512810b081e860303038060104035000c076000b141040e500b0401a5100f5010030f400040c94034280c051505012500140c00b8542d175940c002c145099480c904030f00040300080003650f800b01d00348001c580e81d81c9441080103010701101da483c03034040e201383c440104045d10180c910b20810300d48448403402ea03100208049480702c090010030b0741071100c2085006241d010070300881303000d01400d8252500e420b00c0c010901420700d00c0100021007800c07880006006508141c1e03c0340640da120300c00f0300324498640b0854440240b00d1841051601e038503196607007050f850702029080401c070044008000000c4c5102104059104111941c1d000600b25020454040d652002602e030f6411103030000d00c0d060031258049030b04800680c501c0301c54240040100070480780c850240343d60010b941d1025241540c40c41e42c0e2001ca80001030a140c0c4603403030200010b8080c200d01c0c0d224504010000b0110340c0500d07148091741500d0700c104e01803003e075400100d81184d41c038044a03049900412400102c0f500d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 533363381 1250 533362131 533362133
    0x3060c1d060a0c030e0d05030d0e0c0f06040512010e010507110f061510120e01090c0f0f06080603031204032012071403040f0303030f1b0e120a05060c030a0c1b 70
    0x281e01710101c6000e540104496404c001160007000a001c0e00ea004080000d10142200034940c80c0c2000305111b28410518400d20714002e031140020340c0c0c1103810980750046101b4454403d1800b41880c1c4001e0f05181d880c000c2081002d6074869130b01420501c0b41c0b01034408841c41c000400d619120204c0700300180c48011110711800d03013001e00328882080200e10342444040007134030b001c0003900d20301c800c2948140c2d1648125014090070050007401860f1000740317202682d01e484071000f1648140c0c400d6009000102c0c0c001941605e080c02151036035404444150854a09854003604406c1402400d140c04008071503003d980c6180004d12604c0b941c001280542007604594405050b18030084055285010900000401c0301c1c00100203005544a920045801a606d022900442d446a00030074542646425400c40064006a091b000d011003030350041040c1302c4403c03d0390703d04248400002d000348900030030050348a61540c0514022001224107100103032503070300d08580d00c0e217400590100050000100c04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 533364631 1250 533363381 533363387
    0x20703021012060306020406030c1e03110702030d0207090b18040b070201021210030303271515060c0b071106010608040c170a02030d050310031b03060c1d060a0c03 72
    0x100c40a5145024110701a42030500000d0f41d84650003112080d801140034003a643c3c25008200b4448001d10f8042d441c43d90b00d0104810645003c2411824035541e2104084101c3d50030040b40c45890700034040b10141102003400a6450615220740c0e0402071810240c0011440c1449004403440304000405045031104d40f01c4c00c420545c041c0515040d59420408441c1134110b1204039841000c4840c01218000d195007000750503a000d031030240460059000d6248950040d118034680302c00c1d000072004801052041e070b0840240302c203030000d420080d10003000048166000c80e4801c10144102034400315515507030300941d180314401080d450385400c500300621900d48942c02071075025020316100c0d9082d41e0754000300d11404d80015110681900450000410340c2002c0101109480552a10b07074030390300d0100300f180d03001d01e0b4034080140b40b00360540b081d40349850709000b00c9000d036400800801c11552210005006000404684002074070741d4100c4041c01d1401405440041c0c1d515150500c01500c150340403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 533365881 1250 533364631 533364649
    0x1903240b09031510030b06090408030a021614010b0a08160527011203110714040911130b0306010e010605030a0504031b050105010f08060c0a05090a17030a0f050a02070302 75
    0x1c9a01881000082c085440c6034000507405131101c0b003821403209080d824409990035000782440d01480500092200040d11001100d0b4000c0076000010b882c3c80c3c0d000070603100304403d001702408110b144110850404019800340c1c041d02011508241c800e80e540500d40d4555600c1003129800c3c0351040d90030040c5050201503101e003c42d05180c241010036066100702040c903000c4e00180d1800240c69038103003c1503040003840003803d24003001010090324140304070b0300c401e400141880c0190346a902000c10072000144850300010000c0074510082e5000c0c0009005085040b000c600c2403041000004e507001c524403006059401d00e0362124a1543c0d084e0106014140c05403085040100d0001c4030b1404031442d21001e05040e04c150008176071035151110b210840c00094002600642104013400500000741c1c0483e1b1a040711030034056158001c0da0001028615140d2010382c02e524100c036002600a8040000c01c00d03111983c039a0380111462100c2164680914a51800942d01c514002d10240c03402c2081 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 533367131 1250 533365881 533365897
    0x105040c0c08040303030b040f0e0a030e2209060b10080a11070b070f02010501080d1215080304060921030804020f040f02070b011409160815061903240b 67
    0x10160140074650755144460740700d40e2080d00040d907203181940c0c09181502917815029100f110070700071075a0382c61046403551200c2c032005051107400c3d08100815180c0451801201c522004a070148403031483d0060050014028200d80f03031480d03c0c0240e002c40c07030600c04d031381e001010664950034242c1d500c040480082000003c09e00c41e0724001e002040c0011045180c403481242c166441000340d40e4046c1d030190a44406802c4900d96410920402e601964840103400c0412041c0c0d0010404408000510350000e149030040b081b1400002000b094141e00321101600300e41700308150710300c03036660413100540c40c0311a900300400003155030000c0f4000d841c1c60202a20040d60080c000202c00038101400800c90348007880480312140703104010040c40d1001080e4a60710300040e03405209a291000c070340d04500b0040784146050020a0001c9040c110000715130701c01c0728001903c00c559500002600c038a022618a80e1100001d00b882101114410010001070355402c0e4103a8500c02c80c0e047c0340c032a09094121106d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 533368381 1250 533367131 533367137
    0x30a120e070e16051e031e0106020a0c051e040207060906051017070b0901050c0c1e0f102708070f03060b030111090609010e040203010e010e090a020d140a14101a090105040c 76
    0x44100e807c07494a41d00240246881c3c2c0007040200c0291401440004040c1c0c0304034420400321004039120b20b00c280c181a005d8200b150700513619080c070301d080030050007510b9029140d5803030802044080070314014003001380c1c0d00040b820404c80300b0500c00f484c2e40ba582030040410340c29007442000f010354003e0003d8010303248407805840c01c04800c0c401085d1022908a41d000040c2c1c1ca80e102c4025500b8641034041440c0c80c2035a00e40b801c0701c4411340150810301549424140801202c030405d01c0d5915260a0344042c050203401d40d480c090303840e10813455040440c00301f680c06520b00220310807140f60502ca80040d40e01035424003810300801c0c20411030070f90001c0040c141800503c91030020540d07220b00c011400ba00400d00003040300d50602d9013800300007000030036900382540b2141829016a0700c442005201551180502c2d4401450070301d041e04202004000a10700402044d00414140010600c080712034038030101044140d411800b4074074010030071000030303411591810060080b0300781600030010300000c9003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 533369631 1250 533368381 533368411
    0xf030306010c0b07030f0c121d0303040f080c010615030e0a05060106031a22150303050301030213230402120a082205060c010b0f0105030603030a120e070e16051e03 72
    0x2d406e0944207041300c1c0350002070b2454851f14003a059482814040c64240300a50342c1402850020390b40c1384070180014000310780c1644410100b00c01c000842d10004d9070700c0000e005040d5110b180b91000000c1024000200742044406ea04050002950b1700f4a10782100090107140d1070b00c00281c00030300b100b900c6100d05280098480802d0f40710020402041524180f903001010b000d15001022941550103561009100560400c04070307902c81d09607030541e50125044160b0034030441c1e102c8010300301d03680c01210401c050818617140714810f0041911640c001d54240b8101c0031070b0807600303403581e103801401004040103005110b6201a80c1c0284603070501381b100700024440d1541c0010740c06410540100c01d40360b4550583d80c42c0790074049a400d11940003820114154100340000945901440c9116030421242d2a0001c000e8901c40d00311880c1c0249042c03d58490780c0d2034031100c40c0510422a003240c0c2c0d05800400d221410740c030032022500e6440c01501c1c0100e0780044003201c501e1580c4054070400c2004248 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 533370881 1250 533369631 533369651
    0x4231515040903180b0306090103111f0c05010c0e180603070b0408071823060d06061e05030d1707120c030204061d01120c0516060e0f030306010c0b0703 67
    0x5445442182806512007420429002c0c464044d2950b40b90401d001c801ca0905c2408650f490b02d9040c0b03070560b64441d041144d440a020301003070000b484c03810741d44501c056000300c580d2500e8020f0072750045140942d0086c42a051281030540f1107004508125030000f00000300d0310305183c8101e143d55048030303004090b60105030f6200702c050902e410030340109030300d81c0125004001c90001041d0300114010300c44400e102c00c02001082c2d242c0b501d12641e038443c0f003441881c00030700990f0712404c2c10300700168031080802c441c2da1a40d10800c1c10706581c3c03860454004594402107594170f80054120303014081c503a80c2c62020080c108042000c044007a00b01d805010748107400c0d5158440030b000701181c0a840340d5006803510308d09440100080f112600e003507058001120784002c541d80c04124008441d08038032000c14a101c0158040304d0b14801d02400e020452104030b40b039400c001880d0090030030200c1c8582155600b6110590468a81c131054441c41d010521124a040c000380385504201d9000701e0b1824005800290 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 533372131 1250 533370881 533370889
    0x5060c18040c030203090f06040f0201052107020c18040f02100c06090f06060e090706110f070326040e070e1302030f0103031418060c210304231515 65
    0x380076070b140407035004420003a60010030070180700180c40c550001c4c505828503803141c00041000c00030280c1004400511407800d01459031140c1c51102c10600380c50194a810180207450384515665140310742c035024071598501504a0100d0b00072504031441105607522603003042b8401035441e021a051056034105640820011300c18260040c0c01942e002c00241070034074028048403000e4001003809200c0e00140080d0a80c000303902c4081d121103003058102d120f200d55a051603c45130380342c02103031440b4091001c403c000c20250f00c0e040401200c4008040807410782c20320103c80c00b43d409921501d50440c4001031400e48940d91030b11309070801a00d00c4410f124041102d0080c1d030b0040b02c8624000f400c10004004159020417619286500e100740d85082104c8005902400050104018030515000c1521503a824003800580440c20030902c0c0d0200508096008100d942c00441c0c0a46030445009000180d4880c401921000011013401810802c00410015103440e400a41081040019062284c03581d4031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 533373381 1250 533372131 533372141
    0x100501092612030a0f06030305031303090528060201020301290403060905010b010824221d010605030a11040c0c060203070203070b063109080414130905060c1804 71
    0x140000c0b2030b0b07a0345000e4491200b60381c0d0305d0f1044070110703142c10001c0021a6001c01540d40081c4501c141e0b181000441c101240c130300209411080d40003d0f811078210030100551000044503002d00f0681200d10f070340302016401c1b40000d214001180701c1d040c0c1d10f2008120383c00d4141310b4010300c0c10003c0d07090175100c1e01e41030704070307862650202c840b603546d5a028080c6680007503607103a00c0706070703242d200400042441102c281c2031f52000e16940141107240f50b103a82003d40e180040725034101d0003030030004201c24940c03424103004203a183c0e6405502e07080c030202e0070f4240829507049294102e04107841c00c000c1001884000c0290504100801034042c00400018038640000c5000d0b803841c2c0d00550711401d40b81041480d00b0000381c411072280001c1100341c00011400b40a4611404403000c460144c0d4070400aa20064000d4040c0204150f400090102d110f65142d60b12450600003511001d0b034450201600c0300444141c80e01c040c00300e41c002e10009840040700780090042d60500035090040310a008003050540e8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 533374631 1250 533373381 533373403
    0x1230103110d1703101e140d020103090f060212070203090306071b120f02010c0512070c1712150618040c050c06010b0904050c13050f04020912060403081005010926 72
    0x7000c010072446c040481d0010714500080c10301d00340d4518142d030030103542020040040c0142e1083c101034081d0780c01303070788203840058001200c0c803155a29840c0c840c0c025880780c0741d40141c00e4030f44001302d0304407817002094850519014000700b1240d1542041a1604407150741411a00050110500002510103100713403026511501c03185c40c0028041030103401d460b0103840503420401c040c08410002c901c4410708130340114040c20100002000b606008000d001528060030001d100000c42041c080560344170b081c070604010507103604084075603003080001d00c10032591032052200c0c240d95103010310301503000100c02941810410300d4071040381d50190078003009a2100200001c0031440242605044c0a41a84140403200952400b004032802010034065401142e002d0000d9a0036540d039600d5541c11100c140c2802054403000310208039540350b84682c225000c40016101c2c0c40411209040c456404003900e0741615241389090400b00d1080d0f0b1880a059407210386500c00409009810003406070b06480 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 533375881 1250 533374631 533374651
    0x1213150306151b0803060d0c0e061c03020d0827010e01050c090604090b01030f1b0e060408071e0b1308010c170f041a0901230103110d1703 61
    0x4034a4409024804106500c1d0b04041c4000101090071542c0e0000710300ea01203501c0740e81c00c0e0312522100c000c14000c18410200501c091b40110003c1a0b488550140c0b07807060504540c0c04c101c03081c142d0300c004091101000e004015030300c6170079411181c03401420001d034020104c035400480c3d1a041c0304840303d60368506404482a0b551440d6000c0050030a02441da80311b42600300c0039240284010101c2e00302c2c400da1080512855803840000081d138400d820004451344000018000030b0170308141209055a18a60080410560840700313410f4100001a034044403200c40141609500d0030f1040348191240380034000001400607004110035038041c02401d1790f40407040810b482c45090034401d60844100e001004144001c04120107108035240800680c46000e45c0340711111a11a460940400b0b086e01c90312507090360900c1d0401c2004901540603d080181c500b1020300cbd04040d00c904036406940a002c040c002d1901c9a442071028240030607507442c402d1040300704404c004054900c40c015500280c0d110000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 533377131 1250 533375881 533375891
    0x70e030105190b06041d191a0f090114010c021c1b0e0919050a0501090602031e040c06050304051501080303060405010b090d060b01030923070e0103030212131503 71
    0x282c11441000e84442042d10500e2405040034034189914180c4614100c0c1940000002510110031110003c02d40ca0151001d001101240b4250058540341c13111560295100005902c890300d4801340442c100c0740d85442c040c1d880c451407001143c60007070242d41a600031007046002c491603403012000240042c0201450504201ea0110180c4881e03245e51209000c85803075414020701c914003003050704100340b18044102d64400c543c030f0554101829050080c0c099460001240240f1101c3c0e0001c500ca00e00c100c0c0340f059084000001c070512460203480113030010002c00401e110b400c5c0650011508680620100da604007014903c0303105040c001d8008420640010041c4107803810540182c501500110100504003543c7da0b010840013020a8000341c202a290311004030300313034040e6110396a8030340c102005100750702e0b10f201c0c80c524115000030580b4061280400008011000b50585130581e0751540c0509941c0c50780491150044c0c2120410340100c0c011030000003004060110349246000c1130b41ca020039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 533378381 1250 533377131 533377171
    0x9030a141018050c040c0e030d090806100605041e0b0a030b031501030f0221030a0504180509191106030a0b0a0e0c0403030503150303040b040306050c09010e09070e030105 75
    0x2590000e0251003949900a00d081000902c04104a07003425804c1c0c03000241b941000704111510303101075201c9a0180509492444115842440c400503208803004586da00d0310740300c103044554000b500c00c00001071014403081c41400f02480e18403803d200347c5881c400c3c01944031442600154003488514002c01d54842490791942824803410713048003440d000e00c008540c5036850380350250040c130344000e104d8082c1c600120820303c1c802c1c0480034920302d48000c03243c0302d80e070701a00a003450388540594558070859800c85d011401981c000e0038403400c0d40d1030103881d8100d0011820031020816a00894002441c420340c902e581d19424051803255481505c0800d08203048014050b84001a07041240350740c01d44000c1100b080c490108560480c0d5051820075501d030b4440d0901c20502e0031052002d035050000080001c1d8005040e800741058a016100410544c0c96200c1d0419043c407500180e0740c00300d219800324180b1803400090059204009041240d0b02e0500703103001900311502203840301003041c0c501100d80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 533379631 1250 533378381 533378413
    0xd0801030506131110020a0501150e060a1a0a02120a050d1514010e0a0909050a030f0302120c0901030f050a150504090503030a0c140304030503010608070203031b09030a14 75
    0x180d04141640030403c0ca940d240d40344c40e204406459040760140c505420720b0075055108000405005401400030045449413017048130482605201d01c0d0740f05c2581c1c10110341d45140501c40881260841c481049484190051481c0142c2010340000150f0185001580c10019840000c0215a9191f5a4035a40351a40401041111000d00c000e41c030000182c0300c14415069854000c1141000900f00208144030000005503203003401d4100071200c6080c1a010400c1000000e02001154441c4c0c0390f207041d14500707040440803402024180041648040045405112500014040c0b40f4061601081120b07821800c1000d446055482102a6640302800f1829031380c14949040900343c00c41d4240036804454840554900000d030640b001956244010b656182c0282c2d03040c07400405071a007442c2c50340303050305001e80340303410920a41c03011821450001382070500c0401224400d0300300c240c010307062500c8403018203400d0b04070040e081c2c0c1610441c4014004100030100c84078150342c8910042016541c0c8407018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 533380881 1250 533379631 533379643
    0x30b0105090a09050c04050c0c010603140607020312011202010c061e0b1008040b0a0603050a0b04030806090c031803040f0b0c0c0306040206160203011b03150f080a03080c0c0d08010305 81
    0x46000e9503c0c1c403882000042c13002c600c3c0458114101c0b4081180c3c0c841c00010181072180c04202041036203441c03000070412104c0c04100d04950901025140c1d1607807030700b1090780c80f8810b107807032501d9a2319245d0050040086280f04903012034010b26054003a8140391703951030201e4500203280740c911b01d1041855400c00030365025110018000392015100202c0c1140058150400980020038000d07078000001c1d01c200060744910000c5070444211090b04045052501560714165400e400203007000d000070f0502e0821100450040b141264a585150f69245500c5035070080043d503044603001c104000502c460300c11039420094400852481e03580c080d101d00780c03890462002005800b85d004541000003503520070080e6980d46503080c4903004000d000b840024014034075402034946104103c203412074120341c95800004234815800c1c00800d92a1034100c404034621f0603111b1040300d40d01288000001134814002e8642002d840d02c19241800c070202e426a0a000e002c3c4241c00009101400400030302400b0000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 533382131 1250 533380881 533380891
    0x5070602010608031206030307051203191104060302130f0803120f0708070c03050d110316170c090f0306090d120209030709093905030111160c0f030b010509 69
    0x2000b01a10b03000700c0341c1d00e1380035000100104140110004407161000e104451061364814144ca01c013081307280700304190340c0003a0390342d619071000c3c120845009032440c800d03024181c00c0500c1d142d04091500a04401030340c4001b004241080300303560000b980d500c8107044d090180910401664580701d241c40c04040044c40100544e0300c0898210a001115030000f01e00d5802210034a0a2841c642540c20295104d101c0d14080090700c0c0c3c903080104440070704030400346000705a07081c0703002c0010050500807208060010709038010b591120b000b0450380001c07040100103405019103000d003944505400a818900d045070000c9041c0c2210b100700c0e02640e8020003201440040705011400e0000050100f40e444241e0b0080c0102c0b070742e0703c0c00940d0510040d8501030b00c0001c1d202c0c0c0401d5290a01d0400320004081a1f03055805a0101307160104041c90107004011600300a00b072a10b06014000314500080c00309000141d8200703141c0c1c540840c6d0070700941f8281c40034502920701185107500d02010701080040c0182 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 533383381 1250 533382131 533382133
    0x20f0d0f15111206062a031b0c0a0608100308040e0a06050108010f06031d1f1a280b03040f0c060503010b07260409060513090c15020307061805070602 66
    0x4032040d622503051200d16000001520010349a981000740020541b0700c2e4140c0f850300c00144207080e446050008000c042448446c00311391640340290032800c5e40c40395648803003907119039144018401d02e031107039011503230000031300a000204640c1c0e074881c5285035200d500817031a0030200d8400c10036034600900070840240804c2c81d044074550325040414010384e85034001c82c001c040e02e03010841b12201000e01c5004080503124140c1c1c1e140510000c04011542c1d4001c440000310341808038030f40702d41d4540340e03950b4040c0d070000d001500301c800e0320b0042c8001d4130300e00c0d00b5880d03c60200401c00f044945056025510403407203031030240078400b05400d121640e04a29401041007210400042c04201e466600381d56540354085443c05440008400d985200403081013400002c400c046000540c903041c40c1c201900319403017940d03604221a5149060400e5450440c009000c2c006035040400081050a408203405102441609d05002c515903940050700e4010319400440d058000e8980103001e01408010020f04045c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 533384631 1250 533383381 533383387
    0xa020a05030607170613060e060901090c090911040b07030c0611071101050a020114070512090601030f02060307020307020a0f06030f0c1b02030a02090711060903090d020f0d0f1511 79
    0x400c1c020204034081a88169130b08444000c503901d81c0b00e41856506444110109204854480400d044030701011207469100701000c400008034402c00c2e02c00d191041c1c00f02da07500320060342009a4800544040109500414820400082c1e6102d40201620b400340c460b9440a008007018241201900c48450305407000301c0003080502c0026008640c013040c0f40400f0308025440d20900f81c03090f80101841030f42041c0c0d180001d0104a1000d81c0400185030800c00c410214109460310036641e9501c0c40309000040c05010012622005498008055644100584100d03440d24610b64003040c0b242065600c0303400102903103641400710036094041d5a04280d12030800304041c0b061844000d281014442800c015000e0b000444825520b050150801e8280c0207042d16402d0b05042c100201100e000c2c280c0062540101408180000e0b0007101711a1887d0006001340f80c60010341e0200604007880a204076071224002804100250021030b480c40c00038000c030148020280010500710a68005040c100d83c00c0f5410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 533385881 1250 533384631 533384641
    0x11010606020c010c081216030c0309080d09081c14090d1d010311030c03010303081609091503060e01050f01050a031e03030b190501020c1203030a09050c0d050a020a050306 75
    0x10b52200002007481c00b0890305032a800d24440382c0c4140500782810417846403c200030f2403012001e102050703070075503001c00c00010200c20440c11200010001490380c00100802c0361f042c2501d401102e002805030104500d449881c00380c1c84200c500503443c0c182855200d8156200c416250140154800e0704034010b8240260034040c01420030204010002c464544111114040d074442d81c060001681c07072030000c40e80d900b4405400c10407501700344001c600081244000400002e8421080403480d80c198492000141c10555100701a040300303500d411131000c480d40000082202c5000769900600d80c00000202400e0030301803140742610580180340110320140302040040d00c0d048a01c0d00715502c2d80709203d05d10036030307140c110060300a6001450b80204485c402aa80d0885a000803080301e800341c003156500c234500340900030b2480c2c036203000c2c8641e5001400000e140c4115500701d0080e651081042d00e1100c00050f0011b004078143c56401d5500341d0002d0590011404c02a070701e0001b0b0042100140301ca4985 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 533387131 1250 533385881 533385883
    0x3151b0903030306011d040603030305010807050f060706051e0717010e09030f0702061b161e03060c0909020c030c010501090212070f12020409050f0a05012412020f0a1101060602 78
    0x40a040d160400415521061074620403070305006c42030b50300400500580f603880c1401809010f086c094160b040c081c11000251502e000d0644519454000d010503083c10301b030b501d540000b001c000304030303840b510a680080c04240c56510303140780c46054140c40d402c0d0118020954039072810070507040940c2c00707024102031060340d0a002094034803501c1740039509a0740315858800308007140950548035041c54415090b06012042c040303042c2d03801c03000710700e901031109544022540c0203c1c0f10b2038075170343c122843c0b034014801b103612a00844841c47c0307613060601c895030361303154004e08aa00400051800d6003002c104407007410028040c050042200140030f6092402c48096101d412a024100809000a6250a2800b203018190303440980101503000c540701d0b9500e641440c06084101e0f00d02a50352042800611a030304148107840c107075064803506462041c11910142c0600c40c044d41d0810521405540e200485200750005006481040700000d840746d40d450b00151102d60a4002902c490341080d00a005e8141c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 533388381 1250 533387131 533387137
    0xf030501180c1e170703140103061802031203060118051003150b071101080f10030312110d0e06100b0d0203060103020c10051b0a1707020c03151b090303 67
    0x45400c1d030004040303080c1501554401c862450340d6100058403e01c901c9155086074068484074161100c0b018580c3e9001001c0742102d45502104c0500f00d2024014004100c2c641d1102c0c0301c41600c000c0c010054180c6400181c0341059480700318400000020030003406580c070448101010391544400e060a03810000012500300841441e041055591030030103540030000d40c1030600400802e9001650341f441c0d4244070161a20869060740454048030214602d0451042850300c11001038210344072035401e41e42e0854030184c84070b40700303102d031600c401c203094032409003c1c000c04100602076000102c81c015040070f24100400240511000448038100300003104000044a03d40c0c001107400580c0e950b22200160000e01408254074064031418500700644a0a684024062801e45125000d0300150308062140d0388110803411000615a55400001c3d0b519000005d40141c0380e40103580d81e2590710b0300400e292003c1e40d00000100340000707040c4506030b4074149044070b03843c241d1020240780081d11004240d980c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 533389631 1250 533388381 533388419
    0xf050f190c0509131107080408070609081005090c060c0a110f060a080603071a0306280b0723030a0f08010302091305250305120403050604030c050f07090c0f030501 72
    0x713204d24811150300e0a4a5002c41e204840d9500d246480320454109131110f500b040c0aa1941c1c0c0c071a4200c04030b10703035020301d070a00e007100d400c02c0050903104003440241e0040c000c0070740390032064400e0b00b030282001d9031440301a08411400034011316900c913107814808541002d065555005181b2292410f05a0321440100c500e40700450900300105d441d00c80c04289010000e0744086001d011480f882d400c1e0001341c0d00118059041282c49101400360034000914031518864013071001c011b6644100301201d5500003520b05e407802a03080078400c0110140303203a0600c0402084208a42001910000803504a403e81c6038103020f40c40c02d21230542c15540460001c0c1f0001d40072408210380b080c0080100582000151811041803402440001032030088040502603070208440d60f0150848120544a801e030075039003200e81201c020141903c031a2000d803003e90500314140c13214004c0c0c1009000040040140c14000c103c03030203000a050340c41440c000c001c00d040000c00404c06003442e00410200c109030000d10449 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 533390881 1250 533389631 533389639
    0x1608010b041413200405070903030f0e013603050304060f03090206040918151505240a0c05010c0c0b0105041404030f021009050c0a0f0b1c0f050f190c0509 68
    0x100380d4100c0100d0701415100c0071945c03050030241002a04c0740e01190308401c403440f0791114007143e40c2d18201a102c05500d04e65140c00210400303596030300c00000703a5003080644540041c11507125817500040707030808400c0d00240d9055000107410410142d00110b5040107140c18170b8104680d03da00c1c0d000684500c680c0c40b9030382c00319031100804c00045060900115403103070710205a1012044080001d0050420003803c404c3d2258950030008490401030521103440a088a610320b5041e070b5421041c6030341c1c0060034210b0030001ca01c1c0454000441c00d10a034500c20001d9201d581002c404d500d0003000000050700401d020350300b4006452500c400c5120041e4005174103082c1605520003241040380f900c810313080424042404c1000c4070b03041c868081080000200155151280d0b1622807050300102c004c2d07841403480380001000750351410340014030b02190b5006071100103c1c0203880f00c100b0605540c400d60340f01c112007141000b44403001140f914082c503040ca2588050001003c0250007504074010010b1481c01 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 533392131 1250 533390881 533390903
    0xb070602070c0b21092805031207030b0906041a0904021c061a0405060d080a1e120b030c1c320106081c030e1608010b041413 55
    0x200b02c290840d03840980300c0180341c0c41d244c000706150384100c055018882e0300040d000d00d011a194000100c6ca1410320101c0f4404503e0140807407204810307010100d8002d884900050014407420010215506e00502c000c0c0e81c0411002d0510003088070a1f040a815503100394500b10012000f014810340840ea04030048520140c1591540085000c11240c0181c01c10000070200c2040100070303903a03008040b0354102842081507401c0c0d0714248800c441060314110351060f8021181c81c0010259401000e46500b01d2511403030260b145010b0045104900fa4800c0110310140ca00e03981c0c5425a209000300b94008070f0040824503244000710b07290b07080807021000c5400702e00c1c04400c248090300315120342c006c000b0400841d440844040e8031390021210745a005840d4280480019404400564403606c404001c61b0189540721400003500180740c2c00340c1d001c0090292502c1210b0203865494440e006000d000004078840c240301f0108801c0340c0c6503007078000c0d4590421040c80303201429492019211503020800e500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 533393381 1250 533392131 533392133
    0x109060806010c060609090501050c0436060303031a010206011a07060605030610050901090b1026190c03060e010504090f05060106120b031506010305070e03031b160b07060207 77
    0x10780e0500e11000505018200100040d00074039544c401601f16010700020440380e114110440001d100d00c1c0308080c08012001c91180712810307001804640040c5500070094449103405180c0700b500c400341e00c10f402081e035426100c40910480850079510000c00d20182400e58108038528000c4512010149020030000c11910100240c950142029100041c11940f180c81c094840000740b020b64001c05e40650b070404000902007020380203140c0d64500041510b5821101c88508541050b819500945040701c00c05c0e2280d0143d00b0503541c2400307006401140e180f00070100740381030700380e03a00140020205441c0480402448200c9050303107040d160100ea0100e50364400303040c6441010011707000985640105000000d1554100003100c10302802600c060110846050400d0b0301c0d9282d1800014000c40020300240c542d42c0710341c0c8019844109030420020f4840b1020200e451900301c880b180d440c000c0f20903082c80e80c00c1c204005c140d469440780981d2130420b0703051010000382400380d4680104084e8010a00c13070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 533394631 1250 533393381 533393387
    0x130b1603110703080c1c0c0f17090d0302010605010e06090a030b0406021201060806040c03020405032d030a05120108010903091a09040509031c0510120807020303032a09010906080601 80
    0x9401141c02070a13103a100c84206960341d4171108000e4016680300f46100781600c1e454040d0441c1650360b030f048203900d401003045846004400440300349200554108005502146e44d4000600c0711050007a4000a84541803100240005aa0100c03081c450101888105226504e003408101601c0d48040d10340450385851400501900400c0c2e07814403410800c000101702c50342d110721040e20400c0110340c2403112602411040d0300300d115500405405030844400c001c503541c0c2d14040960400c0f0a20140c40e40c8a03e103280550440d008018100005080001d41081e0b443c2010092805003014400810490b05540c0d000740c03400680d48503600b0742c4c0b01f00b44030050b4004910b20548001d2500580280040e1500d810025129840600c00c1510890b00382c200703190303841d00c41c030506200c0c00d08482c2c081d01050400c40e8101c000c50312201d0441c1d001c41c0400c120801614107001450040440e07425050100c5000c7c60580c520540347c00d590041040e091146d04610303a40624403400f203921504100c116031315480012 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 533395881 1250 533394631 533394643
    0x9151e120d08100e0609060f0411040e160540260309011b0503040608040b220209092e0e061b09010221130b160311 51
    0x500e60188050110494100020941e0307000011155114030099940c002d5160455015000e0000601d44010000e007250510b0403c2d590403140c014844001e07550305a0001c4c0545129540451190801141c01c03c8045800c880b490b81119642222401682905400a045000b90817050581641d0300031005078204120308a41407080c078100101140243c00040f08030b00003054843e102103840801c02c404c00112014010080611154001d1840d01198000440d0b640b44260f80708031002000310b440f04c1c0002c81c00c1008000030005525100481c1c039041c10002d0180308001d0408140d03044014444480c410411108004c00d54129a0a03e1986419414500d01811004807480750110000c008d204484055013100b9074141002c1c0502642c400105419203e0b281944c021554507006813100000084020240080110601c105c5054088401c03100301d05404180704480c03140000500152038011100300000a0148654003600d804d4401e5401c1114200714003003e0204100701402c500000c0c014084 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 533397131 1250 533395881 533395939
    0xc1d06210108060711011a010f020f100903021203040309031502090402070f051c0516030216031a07050304020f044107020609061501031d06070e0915 66
    0x10080d215a100d440039036540000b43d034450301183e1040001c1c8807020050103103062500d0035452200b0000300d000015a441c1c84072184004c154015040402c240184c00c21002c0c0c00b40b1302540002c154a000b604010f41400100300b542d0141100810400c000700b60410b074440116940301c0c215100002103d0400720080c000c030201c4503405800002c88030280006a80fa0f400300034083c2098a10001b4010002c1d41d0301c205040102c030101d00c0c14400903ca40c40c4220724200c00c40e000340140c4904011850000707485856030381046403038990894805150041205440b5402507180c2003441c43c48c107154000416071070a840c0352510035501c1e0f06098444641c415030040700003c405c10b81d00c3c4540d0071588070301c1d4002c1a140742d129903210b04500061019100003100c50050180b83c015000c5500d6400c1810740785040840c40714149911a044d40141d020000543c8152031a190080c0926041036000280360b01202c0307400d40e114000c8542130000441c6402c0c0d03100850482201c80488051012222540010046071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 533398381 1250 533397131 533397187
    0xc04020403060209090105030102130509040f0611030405070b0a080c07020f030607030b03010f09030f050c07120b070f020c0f0103150e090304061b0c0e0910060306060503010c1d06 79
    0x1000002c20040da0050420303400300300c84036402680c03102c013032501301e0280300c0000040c2c1c001c0c040100000d08002000a8110f8010030807032050300120f807a400305a4a1002d803a0505c28000010082800000e100a070041d19440005900d80008503500030b03c6448040c0c008030141100041582c00c55446c96442c4481d0034019080d1641490812000380081044000540c080c0d400d00a00c0d2140603030030300c41c043e05070398140c882110064000c681204c00340c1082074610080e20a8110215132114588034a0620912904070002545000440203040ba81c444d2114130540d0b000c0d417419407140d42da2004821007911300b07180000d0742e19501280000e401e600b640c05007680540078001e000c13603400048002c00c181c3e00151900d41c2410750b486c140e6541d8a02460001e0300d40c03185040d0074400e0188021180b41c203c001c0000326552445030404002c11038415130320483d0325640d51002000f09043c280154018400c0e1421f0403030300d02044951141c1c03004403060702d081c41040c00180700d04116009007220700c0c1c6415200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 533399631 1250 533398381 533398387
    0x2070303120e2e09051b06040305010e28020d122001090c0602030f0f030411090708070905030d12020903011e020d0b0a1413181b08030406021903020c0402 68
    0x85400f446198180108600318030f10761146181c2c0303201c9018460030603174018010456400300c03488003d200f82003884003691082080200001051003402a00e00501c54000588403a13021580b05c0501c0e240f903180442c030b820303034580048005640c80f50b514441035030700700764070a00030355545408070386d428910b10010103c20407022050342c05400550007107420501c61004e17803c440d0346507241642c0c0c9000d030f11400d2092200c200034a4088250030006550081c2c8200c080004a080340c07000251802d600726a90300c005246e05041090581c1e1201601c0c00802096010300007000a0540080600030800c0040b600b05400081c4400542c800b5071100c640490303a2000055824030310046d01c4082e40c4004920585182403541e81141440c00c8a004006c40e402c81d00311030280340c0504144010425003034500946681c5c0c0d019858070b200308030b2600100c0c1c0303403049410350200c11a0700c09001e0300348040d070003404490f4014403051008603000140e1030307045240740401003680c1e500d914040745800c510030010758110f4004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 533400881 1250 533399631 533399653
    0x11b080d05060a1703030f101206020c01020403020a0b090907050901020327122a0a0509040309030b090f1005040809152701110d050a050d061a1e070302070303120e 72
    0x10003c5e501602148200b0482510745201c0088e90b081c40f801164808106141f9940014100754010080020454005400c20755a50001415030400d68480121240000395041c007501d400c0e0007842c3d015540f802c2160510940c00c0000b540da0051407946000000604100009020311424070301c9808001001141c4040034110042d40300c6000c0d080496141080035142003113804000612603e000d00034002d001443e1a0008001c074101003d80154244506040040040ba411401c583d02c038940010040040e4a00c0c04003092a00c1d5240c981c030f04125142c0300502000984140c00c0f502184400c44000c0450a40f03100340c114544201280c0540c28203822030341141034600d419018503070040076200c005da401004180b4545071064007a11400165041100c01c00c8580141d014060000140c0c030000344054452040e8483e0840702d5100541c2c803500410044421103805c903c3d0a2592520807030281446001d0360060354504a03404001e051001c40a03030f404406085034000da070b66109110884128071b0304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 533402131 1250 533400881 533400883
    0xf03020c0c04051519051f050c0111090a0b04030c05040905030c0a0506100819080f090a0306090203010c050c0c0d0f1b05030d090303120e0a0c080606011b080d05060a17 74
    0x1181c0d420f58000c000541e1710070302030308180300d04804964004d0441400c01d0648501040c0c0b00c0ca100c07843e11306000083c03200c07150800013407041d041480051b100f041ea50320005010080321001d20340c080c0008840030001072002403210a03a6100f190420364003c07440210350b01e800c0e402c5010b1461441d0052240303201550a1100000f0380d18040c85a10001c100500e845101d010380780c1d070020f4003040780b2a80988641000850102c0100a8030030600a00c0341042074110006940c1d500c0c07030b4010b90346103032100130541c00c0d443d080c89502e03c1c101c41810060b10740640000210380313411102066a105291000694083c8103800444c1d200080c2d001a80c02d0030700b0400d42400351002e07000d002c0d01c2e01130700c100002540b9190290b1900b00569816459207900340c0361508101c030141038580f4001d2914042c110716103001815042441007e8070b16480503017502d14010b00010010044c0d9141d603220342a001540801054101044540b850a40c1801041e5a0387d1800890581d030351913400950181c545000303100d0385401c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 533403381 1250 533402131 533402161
    0x17040b1c050609040506150f22060503030901020a15022511011d09060d050a0515060a0f1806081e011a15030a110f09010f020d0f03020c0c0405 63
    0xc0d1803030100015118001440390380c507404c5a000300b440d4440030200d50480c8002c1802c40011000030401011240c80b8400700d10b4030681d007564031080e60320f4080881e5503010540192809040c0c2030740117500740740c070307880000313589000a450140105109000c81d1040342c800740c04403849d811406401040c140300d03040003602007044c0c0001c140d80c005c515901c1600558403603c00703446404110300e440c44c9a139000c64100301c5100e00c0503184c1d561180c0305001045c005481800089242130040f409080c40c540da1954841071003900a042501c905601903060000e10809408ca0b0300b6600012460700142c540e0001040003030451790480320080c8500420081c24a03411440542c0c080d41b104000d108042020001d1a484034a50590036403103060b2003080e01418070038102450b4000c11001021400308141c448000541d400000300c44000a40018450031558128280307a8220708288020705050782080c03070051051040d0f030240010180c0014a625103401e0812241c074816000400400440c245a41403044060f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 533404631 1250 533403381 533403427
    0x40b030c07050c01030501140f0d0f06021e030f2205102906030103030503041b080a02010f081b1305040e0d0314070e010521130212010605010c17040b 66
    0x11045180035280f951090050310b040707940101d6034a4103942079204000c1c0302c0c18070301c00490300480803600303c2011441c1c1c44103101d42107005d00001640c460a04940f28080443c5410301071800e80c003042400120900003150701c0c1d0103d2280040299104225000a854040014081d00511440c0001014602c10f6405809104031168407491b441d48080c2c0c02ea030403580007507010390340500107100401c01719000380010f543c0240300700d400b001c2610301c40c030180715411038070b0300210241d50001c0079480c219608200302e8550320b2800d0400c0034003841d00c0007035052624010407454080e42004940044c8a030190f100081c0035007801007041c050f4018070ba0b081560303060901d16001c006828850b600108162090401e8007850140d540c01e09140e50300c4006450f02d40c0038410b2000e2100b04140580024079042d000c5602500403a0744115100529004004100c07041100c0000c00340d1600c001001980e8109041c2203e4a62205108090344500a640e564a010b140d00852580030700068002d0400d00100c100c0f800b032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 533405881 1250 533404631 533404633
    0x190c0222050702070503161802041a0307020d05030f0703090305161103100603030813020f0616030f260c0408010608060703140601211d010207020f040c02061b040b030c0705 76
    0x110340d14000c16a8461440003150140ca4410380123128021800e48418031041000c0c201515240d540d000c150201c41005005c0030140c000401880030140c1d06101441040500d171a000e411802c0c02944106000000b402030814140e81e480c081d01010300401c10364805e0346048013805a0002c2030300f4207420f110704211542e44a4001e100d60354900162074490101a66055500c0664030380d1910301c7c1091b0078003044010f13684042c0036006428181d43e05002404c55914054409a2402c214500540340300c102506090612056503c5003c841030303d100410131503400d5900c032042a03280c079082c05510b88950b802600165081180c040341503903000840d0b45c01804a40e608008854411101d5006c60740144c420600180d0324454080c4220101019504110a807401c0021041280c841d20303070a1400303490383c0d42c03c942d4000c110441549000c0f0100301c1680820f85060000b00201c4c00e00a464613002007000102040001003035680c001102d064401401e007a102c80e07907490038410310904c030300e41107881c0c00c40c0c003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 533407131 1250 533405881 533405893
    0x13051606020c030703050d0503100503010906020904230606092806090b120601030e0f010903120e0303010311060f07060606121113090b041112100b190c0222050702 72
    0x401c3c100001c1c031404a03504a005010b039240081803c854660014000320440e601d60740010842e0360b02071086001161103201e0060f60340c172616041c0400e4400304210510382c402418020480c40603c4003600d64800000c0303546941d540c41c0d9a000801c1c04c002d00700300301c00c0801c8842a190654800d032000e201a0b820320348400d0380850342c902e0130704520f10440760340c100c0e451020008203050394000d420a80807020120241e89a140511041e0b80c00c50310858415000986640540507104000c2e1041d620b00582400c0514a10742c10354a40a020854100ca81400346400042c1580d20039402d800780e80c460782e88031805008807962200003d00c809800039504294500d0101c403040002550800c46003402214881d001290b071602510383c00502c100010715400c15243c0340090700074800b6100030151200100c0754001e481c100700c0380c3c1440c000e00c10b0b080800d800c04100424901811601148500010070f882c0014000400c2c0c03011810060141c000f502c4010201c68254040c0c25244e04040d20680d045d600320380c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 533408381 1250 533407131 533407153
    0xc24110702041b0203091903080c010501060e040e030301050904020a0b04080a1e02100806041508010e07060f080c0304060f02040801050402130c050d02280c1203051504051305160602 80
    0x140003503c81c00c1c1c40700540c0c8204902c2c006400c21551901c3c0c1e01c8050388080c1000b5540e500c0780c950719071250500e4040350b555517006202c40760f004010071007114401d4608115480b09807040c16a42d10040c09000c0c03140c425000008c04650b11981140d000d0016101501d44841e5100e40c201c0d0350704030988048480f03011001d5416402d007800d08041c03252640041c403021b038809210071309980c0404d02601142c0c01a480709000c0c03100458103141d11000305041000011140c02d259001403d10040381c120741e0400091b50300d040d40e515448968107030052490044030766641c40714944100100400701c102c0070124004140050b400006505c0f50748164000c2d0345124035294032540b541d045800764030802010660034004085401c0c100d40c081d1017400c1c205031000c80100211101c0903821404a600840003400416818080000c2c40702021030005031410140f05a0a0041e00d5200381c5003504d90745402140d075040004e102c48030017010300f02c2644c2c010081e290a03201062000756000810301941016200d1551411 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 533409631 1250 533408381 533408411
    0x30305070c0b0601121103070e12070305070e0a0e06010b0901111c11100509030307120203060d02010c060902041505030712080904050618010f0603050f070c2411070204 74
    0x146050b0761240010a4941c0c4481c019501040400140c12038140e55042c00c0e1400b1203124011070180643d0b03110099481200c504202102c00c408085010b150800c210410016100003200800c1c1c403200d000d600d501c1d0790381d0445100109605500c0800c544075850000444180c000b0040800010030790b1143c004c0c22142512642d56818940c90802d802c0250111080d0709100c1c00352080020324420640727640b4400c50641070103139030050342d030721803d40c1000061003d0703241c10541c01c1c2134900d0903040c154158600040080c0003812420006410700082c0110402080316550103a80e0782d0782c1c018000c21075a1845143d03002c16031340720b01072103000c0c0c401c1710804600d48644204c1e044401d9801804d4610f4042c0c04c105120142002078000c5410004120900550307601c600062406000d04501786290706182003002025078102801c0100c0314881c1b40203012846178050741e500c42654104079000c054600c402007080f52801d900100640c0b040c5445201c100107481d0400818650f4000c4030180302c03090190040f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 533410881 1250 533409631 533409647
    0x5010204090c11210d0e03030405030c0105060d0f03050306060c061312170c0c0f07061d010305010e0f09030d1817041d070c0204090807060e0c0310021e0a080403030507 74
    0x100803d0544c3c4405200184844c401091414078602001c00c59076100410140741d0f800c15182154203404c04540d18036098000d20620307900c480c086070130403000080c5448500c40382d1036980f0082d041043c0000042c8050306c0312000c46184044a070120380d42c92502002c0000303440703154001107440c84400c0200a10480c07080e04001d680003d14100c22000e900c80c044102119400003c0c450001d004440400b0038484003440000000c205d65156003800588080704150510300d900d5041b41898904001408012030900340b441d401110b404e0745403050f48540800904d54040d410030741110504207030b0490825180e84048500c41c0d4407450f0030850450707008500c3c0038140a9805250701d07240d26284406001d80d500c0300c41c140c0103072040c02e102140b8021034000c1002d0394200700c004c1c0e6540100044080400c2035510031680c00720200d1014000d45588030000a4641c60441c5a460402d5004510a05140d42e0000c111010701c001d4920366a03141050300b805440440c04460aa001c07038600307400500603a0141ca21 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 533412131 1250 533410881 533410903
    0x10504030e0402192114100f031a0907030605160210110703051305060307031e0501080309010e0a0f090c11060105060702060c0a06112a060f060d05010204090c11 71
    0x1144c0c41100c106000c403a00404030000c104020f400035455005010317584034a144020032000d0381400303498001d4520342003000c2984440d80540105100b040840c94a2074117014203401178010354165200d54121524020320750300060a0303d0710308402e001081007000c02a0000500c160269044e100491280000710307032669000d950000d004004120001c2c2c803a00041680e40243d1040c1d83c645c0e520b40020500642040b103440e000700742c1d00c518508010008a841c1120501d1a101c20b1140d0740c10109030356101c0c010020f40d00d040c4684081c1e55541c0c1d95442c1020303805481d52503010b40146276031784003100103000a4040398011580301001e501e4001c0d0082000780c140c0f0b0700a042680703041c1d80d55003405141d50000c501180d03a4010b0b14a078400282d000e01644411a514410305520303440d68099108584c403460441d24000d05084040501c14100030403136560050b00380c004440c040c2d95140106c2e01c00768000000030300e1540300046c08100b141150380901c0240c5207aa030782c0d200f40401c00c0c07031071552809407200c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 533413381 1250 533412131 533412157
    0xf050309060f09070f15030612020a0e0a06090f050a0e1903051b01050703150506040509060d0203011e14010e27010b120312061c06020304030c14010504030e0402 71
    0x90400c000718030603d400c50035000440314000c0d40d4004905490b82c10303402211266040301e000c0301e41113a0601800024003040c1d0484110741c030141e030001d000604180309160008001c80009240d8075440c0c0d0048000f001401410301010302c80010140043c002140c0781d0450380d00e00008256004400114603280b03040c0c00c2e600c1c030803200d181d0320143c03a80d4001043c04006d80000304031a0600500a0044d03c3c01990b6588020581c00c10180d13a4445800446c2c10485c01820284010071040e0303100804590009400d4900e041e8140341c1d8004a40500310214098400d05d054100c0c80d1410300982c0e002c0d0300c45408440343c2940396600c598011007424403d54042d0f80d40a0780e403a0790f8001e80c41c06000552180c03440000011204601302c0880d1550546200950362078202040249240c0d0102d24400d906c01000c82e040301c40c040c1c1c0d030300c901c0480c04003c400240980ea030110014040601500d4050f86d940d410254180d841030250024070701034281118110000b80200b4040030050801c1d009844021122403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 533414631 1250 533413381 533413393
    0x130201080c0906070c0e0a0c05030720010603081b07080304120204150f0902041d0c04120302210c01140f0a1e11040e1806040b15120304060f050309 65
    0x10381003400342d000808220303400b6004010b00e0000881701d658041c014400c02904d40710703618003800a007081f500024840b0f02800f13010030800403807030350044400744250003890111600f05184520140188480c0d000280300c40c000058140203441140004100e410401c4100c41e1340c00c1d154010607480303000c0c0d03124102c0001d072403a0f50107005181c203400c403502c42001c1d6070420700015560100b5501034030f1285d200c0369555900040901401d0484501c0040040f1085a59001e40c10020103484c054401c40c03003246009500350b9a081c08040c0f0034010681c001001081c015000b645010250405500098410001e5880d0025040e400f0070003036803a40c400d0407038468450081d0307603841c174840c06090328618003e8482c840c800b51225001a82c401c640603042c915400507207807402c103010080e41d514094080c03802020035680100c110a00001c016500560060302111140c0354188003403402030b8407080859019000c201a4081f4000020140c400c50300e603070344d802c401048500303011340701d47c4004d0320104170a421203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 533415881 1250 533414631 533414641
    0x10603110405060d0c0b0a030e19030c0c09050a140610122007140f120315010504091d0105071b14030c15340f020f01090302100513020108 61
    0x80d0b0312250f440400544030400300c060070340d106015a41039801242c0c0d1003002182100e0302583c0b52080d4410820b13200700409080c41050a204802c546802004040102c9070440c00100030308980f5420040400b0207040c061030070002003d10280846051a118900d036210014604d80f034000c04a0341c00c000a61203201480c1810030f51a170280030020310350660060070b04510307141e0054520017030000b01e004480780041507100c0d0030381031700341041c0d1098010103500c00707040702001501500440740c021055906206a00c0e4840c0010b03541030145034032800241b4584000081c14100c80c90701c001c40085d0001c002c000640e0384800c04e40751800304845000c524100c0350100c03000190f44000700e0805032142d80c2142d062414031501e0364604039488182810f1440884140603e1502d40e03804220304034880c0b4030040755900881c00f00300d052008849442c0c00c0010801c06c0a81c0740f4000d0008001c00c0b00207400901011f125410b000e940c0d8030010700038184491508001a00030404646a50341c00d5605949000c3c00b5265 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 533417131 1250 533415881 533415889
    0xb030a0b01020106050d060e070605040e0f100b0c010e10021602060c030d06300218041b091d031207080703021c060311030105041e060207060e0102070c060201060311 73
    0xa51030910741559682c200110300303603940c2090801310511543d008142c0c810907240e100d00b400d890364030101c18001c0600c41802965a0701128542c071090502038030880c2e82c1e6000f88900c0c100010f40c06018480000285a04004810340180e00c0451013a000c8840710001d0400150880c0309030498800015009407000c001031030620014540d1050010481c1d06142c20400544115001940855034644800f0303150b2000042d921305407a0350129a400c403255001e460780100d628500407000b48001040303800d0008041154880c0a00030364002081011001901c4602c0d0100030050704480503d4171100009155018034000111014920704e0350305030071152240881582d60f018040c210005040d002e02000e2580041010000e42d00e10b0203032404245186941400400d43c5042d441c0a4000d07410401007001140d00304020300e04004e0300304a410700e003210900301080207010341103005000300e00348461440d813140150054082140912488501c0366694031042c0d08031103940c030004040710300700e41c00a909450 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 533418381 1250 533417131 533417141
    0x4050d0303111b101404080a05070b0c090f2707020a050f0d090b031303050f13030b06100c030e0613031202010c110109080405120f0a05150a060b030a 66
    0x3200e42004240c9100e03440b045107540d08a01c0604503481284100306040740c40401201c100c0101805080140e4000d183c0729505a1400030400740c03042c04001a889003240c8240101c4032125000401c0c018542004041041203a000710000c522500030314032240110b160102c2d046a5513004402111003000405030307410318000c00101100c003580112403280c03001c1001480012501034034000645a04c04400102130a8803031950401ea100b007200380100604459041d66000d00075415040083c2c641c006da80380c91006100c0c4801c035444106215600004100d0002e849501440381101c400c41d000001d110200d81c2ca800c010342c003400044480b844a0404e08000000340280c41e400350b0544c1039603807030740c54202c1c00b40c0c1c000c205040140e5650b40b1411003d907005052401100e08000203100c00115500c540c1c11a0003180100c51251078040000686220100203900b0003990242c15201d032503c1501304540c07110a242250b4041000200c000f03a4540280d02c07941c0c040e207545842d502e085031200ca1001c40102 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 533419631 1250 533418381 533418383
    0x909041410061d15060708190906050d1a04090506061c08040e040503070f08120c0c030405090a0f0e061501020114040809030109080d0f06090b060405060c0316080909070804020604050d 81
    0x140381e6104c0c04189446907001418503034090400e8960310240c8442511241d4a180700e0807081040d1034605101543c1e00c6404c4800c42c1c00d1001c0d01040101030005001d81a10b80e0b0940c030b070b82c0245045520410407034049105807050404660080b59440380740c00152200414610042c1110802c01051040e200a094003030b401500402c1142d08082030795444582040c0740000c1079600e6403010509950420907484069803040e240c00d40795007450044004250b0321700641c01418440c00e04540050114a01c81d886000500d0502c041808001a2050290b84400051300d2241d9131840718030010945500500603009850b80048407400c0581d520f40f1581c2c05034110b0b1175004d0303141d501c0300c50081c013150050024040540f1042d40000301c880041401c00100c440301d5105d42001c0d03041074036004541c2d880c03c2c255000c0b2034040e1212030355801000981e0b0305522401b144480d0320b01d41549540144254007001c1c040f004000da54050864a481200742c0340d000007203d000b98000e004110510140c00c000480103c2c907 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 533420881 1250 533419631 533419651
    0x201181115070f140f070806010b180301060902040e010f180c20070f1d0112140303010603090b0a02070c030602090102070503150402100f0806040b060909041410061d 73
    0x4016503100c081d4580000000d407201140c4016044d2030150500c100040d010a900091400c0c83c0b030403400540301d010501c111f2a9001000c00d50050740b1001183d90480340100400810125440c1c1e60503000030b41003800343c00c0014422b4000459003024488046060302c0810340c00d0a1000d28040080300034040c110a20400c1052a074541942c146805000006882d8140003030a5085c0c00c0c41181550007000b43d1221380344241c43c22085102c040908040c0c2e064401164104280e0141c4d810311101086150004007803504c0000000140c4a6160b4080d615a81c4641070000803038131016002000d0303020b6240045c20810b9850020800185c090307008059054041c01030740d00c00c9540d280040e0814a001440c80511030707500080000f103240a801e40508600d450a01c0c0c01589183c07840100b9141c4028407050050b82e0b143c0346c0002d907035110411f44045000090640f80329103040d161040e81c854400494400510640908802071010f5004203010768808544502d0502c0c59903a00c121044805481c900c06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 533422131 1250 533420881 533420887
    0x10030b040c0323010f2325121104030b0a1e09030e10020303040b010e040f060c210203090c012304031a0604060509071d0307150201181115 61
    0x30700303486002c0640b0403500c3c40101008440000c103500f9103459068440300640782412040000c003841d400d8070030701c050700e0520f84590f0740c3c3d4040501c12000e4003982810b902c032031f00d02841865a40903d440c4001c0800e58424001e000b00c0404400b250300840c00010210380032000020241001940291309504654003540b50354402050700c5002c90345030481c03c0e00020a024808010b60030202002402c403038803480114954502512041413506040c000e082c00c407141880802c0601c42100b001543c0e594010908100744c0c0080b010180c0240c140d00d11400c500301d00d4841681c0f011a0900c00da0b8802c18022000c4e10b884001407004503802c601c0466940c0b81c1d110300d04c2c030080c005c104650180000c0c51144c0340002c880400103e18011004d8003c0203c0e00c81e40c200102405141c071240e091540042103800c00b50b0b5031610315179132291200d045007126901441003d00001c1c2c3d10068601d1085050f103560000c2040000c0844480382c0e14400300c0b405003455640c0200f80800d07086c070320200d000041c40c03002c05500b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 533423381 1250 533422131 533422133
    0xc080c190e0a0b060c0c0114040e0601050a0e0a0608181209060c0f1b12060601020c06210721140105150d06031b080c0d0204020307090503070b03011d10030b040c03 72
    0x1130307504070301c44e000c0c107652103151000c00d01e503040740503d1140c2c07442d0400541454503000e84150500401001c0d41d0400001150b00500b9502a022102d0000001401102c0e0b0750f803908001850000d013141c0b210350410540481391076040c0046a4003c507020500c0782d10345000342a01c00c0c0a169800048254898410000700f130030015414082042c00e0560404110600c251040400491840414094480ea08003c0c203000319aa00003410f0171810405030746403a05d9050070303442c3d110303003560345482c1c0f00540c84c2003404c00c8142e980c40f050001d4410f12a55003940d6802c80c1c51941c20840d00c4c003c06c49649442010010700c510f10740800304503030300044400300300d142c0011001c0c0b0714141c1d21030341c2c42280c03010b00070b1401104038141e091301f840c06050f050005020103070300700001440700600144082e008030b40c000007040185201d81d00403c00b402002e800c8402095561502220941c403d01c2008c0079441c20413240710400c10031b9521a40683c0708107420101043c08c40c1ca81c400310f05405842141e0703030281d4401c004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 533424631 1250 533423381 533423389
    0x210708010609020d050606040b09010e040b040515040513231204080102040f050103050628170a050d110d0f0e040c0c060b01052a0102090405040c080c190e0a0b 70
    0x100c00741c10040400f5864265282d0441d054034406442c2600c0b0341c805102c10b019181e1410296100410700b480c0240641e1007407000301c1c0041c20710101d201c0c0c0003820035003001001c44104984104200c0d050340c040010713669070084001c5207006801d008182019000b9102003c030a02039150200c5522101610424075045010301c1080c0e000e0741c001c1880ea5004a81008402c00174075918006080a080c103114a00d084000a81d180c516100c1d05000070002d45410002440c1910a800c00741403400c071070f04080d050104ca9650750302c8001000316110b10070512400709407842074490840c82260180245508402c13003c060ba51100040c109804014002c0301d00e18403a0303a1409030001030003142e180e039090400e1900b0103005540d018010301d81031100400640185d20a0440e580c912001d07000c810904402c1c2c0b6032078060180c482d10602941c040e003004240000c1c813a003003019a04959070385003115060544802404122552401050300740d1003003040420090341100d418a5100c01011000203c41c69050001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 533425881 1250 533424631 533424641
    0x70218040323040605090d05010b03070b0d1b0f0804030c0203120903010c090513270c050a06020a03080f181f0b0d080d111308160506030621070801 65
    0x1900000ca080c80d405802c080340c080c08040c01e14401041900d010708000002e80303644900307190745005041d049151001d00c0429400800c40103c02415191003540c0c07a400c4524541013a91040313480e0b4a0009128038000c2d418804551081207612016811003281100396035100f0010000e405100b80c0c41d91482c0141e6041c09907418416101000e2601c5591190900d404c6440c0b40710000c0501611210130b124664a0003114515010550000700d0312000ca40c0c0300c1e04404a0300c1e264030792400d100c80e182e0b03010806001c05410598200384c1d44070003000d42d03a0b00c1c22a035a82d990391001d40455080804240703010508010389902c80d5820f51407441d40d07a81c5440e00c03454081c0c040c89142d0040d500403100e2416007902d014400508030211204044a00c80e600c0d4501c0c0307489444080c590a944d15282d1140300f010174002e80c2d0b0b85a450065011030160340f841501d8490041e8844001510844407000c151894281d007a6805410083d150003d10101002e4880e88a011210400c16511680100148a040900030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 533427131 1250 533425881 533425883
    0x423010e0a0b06070b0f0c070506010b0a020c0a060e190b0c0109050613150e190f03080c07150905030d020c03041e03020907050306041104030b040b100b0f07021804 72
    0x300d4945401c10344001101c4582e441075200305020801400418404015542c100c2401e90405400792590000240300748902c0e2002070a50140c0400001c4a20f0058040c00954920b0740a44800d0900c00c1c1c01c22114182030302459001c1400c2c0308014503a13041946041c48031110080c5134540310740c4c40d241d82030015009502611040ea440e20f0480c01088003d02c2480d81208007602401e407240751641d59808240981d40550300d00b290345000c40304c5018402c00030b90b01c811000f00742085d440190341c100b010604070550401d4020803036030030201c2c840e10005000c5032034064100315070107a07001d40d0800a102511b041c5c1c006642a1005001e01649200781d44010180d41c50705138001c0d030366581351140c3e03400c00391141d1b42c0c003000e03c0c810001d042001d42c4658a215a0007000c1d8507225980380d50314400900200403040418007030703a2012070040704200684076460b002e180200e50440040c3e854210542c0d20894900071008251800e018010841c1c020101806000d88004c000c0d0200d0143c400c400c1d2920b01040360 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 533428381 1250 533427131 533427149
    0x12110d1b080c030a031b0c0204020c0c19080105100b070f0606031209030204050a0e061801060b0706060305010b030105160f0309080d060302130c2328020d050c0705042301 75
    0x790084c01d1a4061140d001d2040c50120804054035240c040039205698500010780540d4001500c0f8846081c2401280705054000b0852010016000a00d011203003607409405038540c03800010401a60503c0903000c200c542c0c1091252a0410716a10740c603802818403021101581c541d50302000160307070b01c203803641401000d60b030f00c0d80094554010030040d0b440292003c0382c0c2514052001190041c04190709600421002d1401c0200000c4a1440d0041c115580044d030381c0306011075010700304883c61300078004503401140241f2480e6200340c101801c1b0392060340c04c3c1880700c09030350b148840c0724001e20072107007442d41c0c07802e00203403011b900d440d0f03800c281d4001e410741e8000c181c0e141020300862801159448810038034400070040744058003400362958500005541f1489442d00040c8100f0240b0400c440c0c40d100394002d101d200d800340b01c1803020660138491046000d4003603560200d09040c0701d081a80d000701e034020000c0980d1890402800010005065000064400604804070381104030100d43e00030541e8003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 533429631 1250 533428381 533428387
    0x3050c010f0c0216140d030c14070306090b0f07020c0111010609020d0b090108031e0d1b0206040506150603040b0709050607080304020f01110c040e1e070312110d1b080c03 75
    0x952108245103e4100c07243e5070301c0d091700b80125601c44003800f007899a4941048407803000740c1d00344000540040b02c6a001c1c80d120380305003c41081015040003220a11a06003003070542c07203410700e10200350801c64001c801a4002c0c1728440c050341c40b6401107619410340c1400015225240c106140c1643e0010308000e141a450705014901800c0801c404c0c2e0040681e200654180034912800c00c0c4030040c031700d07222000ba20000c103408250002c0c9600c030f806505404c403030a42c083c0c2c4081074080d484180444055500380a2100042d80d6011a8103502240d81030060001d4515135665035448421103018102c401004003600c00451140c650340010500680585174050f01ca1030a40f04000d5034943c0c1c991203178100481c8a2594101780c01c0014400c65281049901041139801c80170842e2500f034610a02216168803111144045840800e1a100b507034007610500546040d0700400b640e40951340c686a2000c3da011040440300944203203258179056142c056400e46845541c1c5480751560044158606950400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 533430881 1250 533429631 533429653
    0x60b10050c0f0c0607030c0201020715080f01060912060f090c0b0315060a0c06020a0201200903070e070e220504080315042f07020a080f060a1803050c010f0c02 70
    0x40206445482202d00240b80c00041407001c42c20034011024001c0c144600b2200c05811a8000d0000c00301402004182c1450514005402030601d40252621000300000c000042022031085500c01c003a1100b5649421020560703664102c028a29842e040c00d80d079a8400c1c0c5070340083c4590301c0d00c00042907a81143c0f07032281000c8004001045002c0100e0b8403d103010408020308036004018840440d030005001620f81110b01c00580c00345c00003581c0401c442040b0300e003407000410040094608400150708031107020391a1340031050088000d0740d80c040455400c1070340c84598078000008611000c81c0d50040c041c4441404000000d5810950f01104d12203004070422000302d0a035529208c0c506003c84084c400c14042010b12080c150394400c2182c10703562070400142103203180d80c0446005560152015004540e508c80710350b19035128000a400c075000d840b003ca205031009008140302c3d80726807000c04c51041e0031550265400e6008000316103595484083c1700d00b009003244100740b0120f006070081e080090031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 533432131 1250 533430881 533430883
    0x905070806271f150807150c200109090e0105010e060d0b04030e030703021c0b1b090105030a0e030307020a0213060b031303030207150f050105090708040f060b10050c 73
    0x1400c14000c0d0035400b01a0501ea103000114001440c20000d510307000c90b9601814540039103070000003410a64030a180c0082d0480001440700221030155070000300980103258112a400f08402c40503144d400702c0d6039084804e10a06005490034074050502030040e5036101203660942d06040e00702030031079540b400108419040b500e81d003030340840100c810340040345a581c0c424222140140000d000c001c014408541d40e510200002000b450300140b11500d0452070a20b11a003002070048110380f660300b0100401c5524503503c2800d48000321503643c45040401290045403242c100a100200d115140c200c0c41242c00020300086000e41842c1e40078080c0041c181c0140941c08070002e08a40b04d00345071107c00c008070501001900d40102d00c40c4c542e10030709041401c00714007a01800402030304a030006e004110040c0303070660000c48442c144590601c1719a036941c040081c6190112103039030101e100200020300180401c9450b10030710384105000a000d07444e040104d0340e00044042d6400214500040c1050390441c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 533433381 1250 533432131 533432161
    0xb1201060507030c2a080a2312090102010b0411120f100915150525020607081c06060c44070510091406010b0f0c010905070806 56
    0x2034203042451030440c00d99001004c400401d40c01810400384071140c1c5041004202d150744d502c81512620ba0700881d00c400180d500c0e1003603041c0403107440c0030047c0d6480350300030400340450074940c0010103000039508001e4140300d02e500003403c1a045568030341ca0441c095481d4400c007200c200300004d209480b541c1d41c210481500c1d80c01b80500180d40c1e0540208842e100b807c0944c1d005650041401003060314030728100c40d040c4c8909401404240d02104058011254810301403c4171195249803121950310480d49180145441d080103500507408004010106107000c0043c5600311070f601406050319402d50382102240c2454004100060185054405000d864100c43c6061004401d4800780d4200115031984400b0485504610006404003410740c03140020007a1446c2640103c1615000000004041c0003814060021140c0300c42c5100c40600c1c0d940d000034001d041e0b0300056095443d05083c03000004164004c5003c4a04175901c91710070500090080c86900e0041480400808043c1415a1008140300d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 533434631 1250 533433381 533433389
    0x712090e150102250b0c10021216080106120506060c01090b0108071707060e0102030c031603110307030f0e0d020a0906050909030309030a05070c05030a0b180f06010513090c0b1201 79
    0x42c0701321000303111005400584508540c0c0f2110850343d9020001c01c80b5040844035000950140d10200c0d001c0c1e00c100400321494456000e52040204440b2002c2c41581e000900707018040c005640d00c1c4004140f030708258042034210708010f185030704201000100701d0a490300080300700d59021901004001184007049400d020302524100308041150030041165a103d807880380b07104014112003042e429034000c0c0100c804901c216829280d0750b140c03201382c4500c401000c0c1000c07000110b103001060704504010013541c8200e503050f035620709405100401212003032055000c45c2e62103001d140000c0010390300c11100c400104580c5801040b0203180008024440c1e10040a807103041c3c01c10010030144072404400c0342d80b807000300e0030200d0b113402407410701c1184801e42e41c002d580c0500c608200c050500540c1100a0b119455220003a041da803c0c2c40c038655160180c075140c041003a0300a0b401404035281420041d101c8040501c0006205c51054448a038104020740c04400301000010b184449015003810343d5000d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 533435881 1250 533434631 533434663
    0x6090b0103110f03130b090607080c0c030909191a0406090e030418020403020405090a0b060f0d0b04060e0303100807080c0d0b0415020f0c07050a0b0712090e150102 72
    0x60000d101e0701801d100e00802440328000000002d42880139800c62602451b8200c880d01806103000050f107543d0b00030a590701c1f4042210900010383c154900c400303c0e1b9080040c3c0001d10b061403d844184104074074003a04424041900c2d007038900300310945106002d60030300c840f1110043c0c1203030f900c1440119880d5822064480341003510700504450000100d504460f000d500201c2c02e0081285a8402030249400003580182450700b840944080002d003203070124000c8450585503102c2d40108501041003100705500300c400c514808000c40c40c00465598451301924000c00c3e04080c440c0b0f900d056502c1221020810300b041a01841360b45410080d100141030814010141e01d803d80380020900c4030756a00080500c2302c040300240400908800c05034042c80840c02c255200c040c5641d4940b40c40d00807001c0400342d031040350400034240c9444103005084486c8400514908041a100c080f00d003e040c0c102d101c2800b4041d400090080261306416208103220072000000704a2100024104050340451040d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 533437131 1250 533435881 533435891
    0x207051905010e060a02030a051c0f09020f0a030236040c0e0f040c0b0306131505190e0a11070f03020c01090e161101060803070f05010b06070f20100306090b0103 71
    0xb03106d8000088070a43c0929080c0580c84806000e12040c0c54415441c42800b400d09080000b0038001054128501c9240b003290600b080d030b003070401840240100b602c0082d43c44280050800803c2000d807140e0880d8402c8540181030316040c0c8882c603008500207075000c5411542d002410010f00005411054002c00404500380b101d0505480b0901968264001c440005000101094840c1c0d00c00d404014811a20305040c408480c03044940c100300c490a1140f08d015110039103446150801d4060320b07409030b0340b00c107020018607241d00074040700624010341d890030003940801c100808a179001c2d089100d414403941c01401440d00100005107022060f134848200b1001e07075414461032026580b0845442500c900e0008980c0c03c41c0600030b4050000c81c0c1c0024005e000020b01070040c00800c995201d1708502810092080001060520005105010000d00200d000282c104006682c030841218100d084030100e489011420000615400c0344140050100c0e42c0c51208204051240c004c41038407880900301009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 533438381 1250 533437131 533437147
    0x40b0a170708040b330306010605070209010e15180702010b10020a35030105040b120d050d1103010b0c0622030804080c0d11150709030b06010207051905010e06 70
    0x20003964003030001071448034021300244003400008000c440042c010380840c980d8480071454215400c0402408034064064a000860394034000d000f140c400c258090304030b940c540c0c601100b68111800c05425010790407480c00310701d41690307200241d8102076a1404100006c2d8240b40201908454601d4000d0740517043c101035030030705603401040d501040d03900f0100310b40250031000c01d11380d424a81840326041c5c61403c10b05030300c00d655414001d0340c1603800907501003060341c1c034060400c024403030600000030096001008007100c140c800d002800f503203071110401041d020501984c0172125042600f107900d100c00003003086004814100000c3d600f00b94000708440e601d814085100810710302d03034070340a01480508804101003198442c11110880340380c405a94841790307040c03c010003d440b085041d07003051180d00100d00280c0f480e104154060f141136124003007654610340c1c8980202000812013810b5014010780000c1e503843e2031220304410041d101e404840c44d81402e00150030500f00c440ca940c0110401d0000032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 533439631 1250 533438381 533438387
    0xd170309010c180b0703031506020f0c031617070302041826090607020a09111b0606030721020405070810060504052803120c06050106030515040b030106030602040b0a1707 75
    0x3c826a100c41d406255584045d041c207401400c11410300d40f101e0754446000140040d40861461080501c000603109060a141c0c100755441c0700124125084c03016039141001584c0c070b000c2445800791a00c5d02074501e115602c0e0001011224a40c1c107020301245117842d24010881048007000b00d103004400c0c4000410180041c0701601c0c000c014086002d03c81c0040c4810540d510b4181010051010304030a00c00030446281100c500c0e0030954101c4550a80c09810701a42d10001c581944113440180040c000e140c50002e48428100120324060004200c1140400258481d0b0043c00d00c2031286480d08603081c1448104516526000d030710250030000c00f440306000c181c0d641204c100c2e04c071801100a4001e200c00d1141c0796404181544010b11040c078120400c0145a045131014581c0350060004101907a44d6102c1034056900c03c4440210711800350300700d5843d42c5095400b40344a01409000000c00d16129603501c4100d03801a0480b003a5903501180d4015410307445424210000720380140f100050a0455003d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 533440881 1250 533439631 533439677
    0x90602010c0e090c071e210c0f021f0905030d210b03010e0304030302010b0108010e01060f081005150405040606031107080304170307030b0405070f021b0d170309010c 73
    0x3a00c5a0f008001040310300c80050180d4403101e030440f180404005d010400590f20303002c0800101e07080c103441e101140e910142600c0c40e44410070140c482c0d411070107150346c1e0341900910900c8220382c44007404903605501024034540d180a04025180c070035400f4240002c05181c45203501c11030040055840380103a020002c07040d00c0d070708441c0221000c03488001c5540040c0c0900319030110380011344804140002071581c15040320405000a032250803907641c23288101102000c090040ea4007140c460965000050712900310300317621005070507011540945820026401c208258070400740c0f900c01040c280014909880b0703000c014143ca0804120302c0c0444c0c035880c1810f0080352400f401240c00400082d041c00140e140c1c0100300d0b18164040307581e80c503210201a0042c08a1003c0501807442c210000d8031032805404c1074041c40d403640e0014480725144080c44140e07081003990355504104c030a4440f000045540f08500d10041609c540280c50340303021031103d800c403540c0241c034004100007600202502c0c7c4103e005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 533442131 1250 533440881 533440907
    0xf07050103020f040902220911030f1f0609030201020105090609070303140408010606120f0b061911060c0703080919060507030b0d0c050411180909210307090602010c 73
    0x30243c1c0b034001c914941e440501996000a5242d40000b031f1204401c1c1c000c0030b10040482c10400f90414142d12a01c4180464288902d481c001010030404100c9021074468441e5204580115200840c80c20030742d03100365507000c1d070b21080101c0c0750041c080c001c41d0b0702030003907660209540005045500c1c2c481540c03503450071140b0001d000e0000c1210740e945494101c004a5014000f1000240a255a9100d0042c103407511090030040007803801200701550400b03805600302c03102000380784a04040390700140c40d0010680d01c0c01141444100702c0b9000c031600081c0f0449104220100c0030545620903030038081c0502400502500c480d4110008000030566010440c0c2c4070250407020024090fa1080415001480b14080e03996004228400400070011031518078400d8070420380c0d040c0300c500510070030092280950890141007200ca00e800e40740c1420710300b00d4268450000b20441781116005280d81c0001a0012a00c550140c000400c100d01660040300d04001001d06200070041400d822000920b00c140c2c6a00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 533443381 1250 533442131 533442137
    0xc1b0e1905040f1b03060509060a0e0d0806060d0b0301090f0309061106010902070809041a0411160b06010c150c03060506040602060a0b041b090e011403070e0604090807230f070501 79
    0x120100e0740791340c200c85400516405001013000e4106000807541d0b40f602142c0c02c0445504048100c005038402040e01c101d0080b00382c482c094a5110300742001222340120401c605a035940f134000f04080d980901514527864018000b84045a00d03e041c01014000c42e6007102c824052800e100e000e0030400051681c2c11119000c07001612402c4c01c2ca8580e51031301c11100c40c598802e080400754954441c00b0f5545400c2c0800c111030800410b03140c0c3d02041094001c00b000314036a04000900500451508010994481e03814074154030220181d699900488003174010351541c0396a41c3c055004001d400d03218000c0901000c50f016410549000e00003552100000c001218446c2c80f1410540980c4480d00088402e1200d00080000300b00117101c000e26948040c40340e1605604031074000201820b486803c041c04041c090042c1481c542080d0b204442d0040240419400599500410001c15400c50103420907520030030717094001c0346410b075000c0780740d9000462140342074112114008c40110006816030844800b82 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 533444631 1250 533443381 533443403
    0x30b0103031407020a0b0909160903031b02041401031e020616060b0604080d2a0201080c04030c0b041d07080601030902150c1c09080606010c1b0e1905040f 68
    0x2080d0000749020f2100f009400c8002e6070004101044400003030a50780c5002d0300c9039031050b610280420a40f0310000c4401c8003264182805002007403103422050031010941e0148410358195501003000c8440c0307580710503001900503005200704141d40d07000d80d03048610380101c841d00c80110340004076a0300c00c0d02c10125511900050300300c104903507074120b00c429001c000c284a4846039118240c83d210b88019500e8800100d50140c0002407290783c058240c0759100350800f191092031203078019145814054400100d4138014400040010040c46e486405080310f40764090312a8036200b202c0c56440e00040b4007021034120300040007150365110008961017142480c0100300b100060011682e400d003a41c10b40d10303030b00e40000392681c43c0000001c2c0c52260191030040505211031928011640a4400d010301a0385070010b01c00308034070350700c101d0315038007407901030502c10a50307182c001e01f50301c04518941e01010401e07010108101c0c29500c9000e103040c400d411210180701f54502a503444031170030140c0030001c100f80c402c0c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 533445881 1250 533444631 533444657
    0x1b020c010818100e160806100302060f0c01020f0d0c0f081b0405030a051612080a030506040f021605010605040603020303091228050c0604150305040212070909020f0a030b010303 78
    0x412940c002003448a40800115840049658940340ea02410704640f40c45c0d4140090003000010f9000d214401c4407400e803034054215801c21003143d10098402a900c44140544010302c8001e00c0104002460411210b9031004a41c1da039405031840c815022003488804a0001c1c51903070405020b5601c41035443c4441d032002614520289103000c0c4d40c00294144c40341103501c0042280019805140c1580b9032a9503002d255140d01d12030744150070100003031039003100f030200313164075802900110381000c0004c101044001c0d040614600300c1c0c10107445030180e2083c1e80d04107014003900b03110f00400b800056034248145811500440d542c0d1150b240d140b40600c071500e800d0242c0080a2014441c01030b10900d6043e440c04980a0103005510350900030ba5060240300c00b240200d03d406412607048600c5000d807000610303980e00040d00200401402603800411843c1910a40c07402845202c0107048100323000210f03410705005001d02e101e00d80040c24084d122148050010409581d0900c0c1102c2d454035002d080320b825 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 533447131 1250 533445881 533445883
    0x2010309021f030221130809010c1416050109080c09040606260d0305040c060c05070e091006090b0d02090c1c02030a05090a0c05011101090b01091b020c010818 70
    0x800003501521030342d200d0700030511a816001080d44004a052480d60082c1c10a441007100b20181c44100008011031108000500c003840038000310003050500b0704000c0465102c00c0390031049407014448c9504040b50408188078142c1d05070001e05420318100d00014200110250780303071003440030b45120302030f0080010200107076a04514060600b281c4504400e9020460300056050840c0b50301030742d4000c180751103040038803078821035100e0b40c0c221101501c00c0cad10341407080d030300030424080c152a240100080407501c8000d8561480c082c0000130024404282c1444d061802ca91058104100c04c0381840f00c24049642c0d094180e507030b00c0d030f0100c440006a0711500c49046076482014203030b100701c0c0a5510001302e01c110944c00307140300c1c12a512003071250740c0d1540e25480c1c8441c84510300900485110000b84800e510405001481d83c49070380000a64050544406400795401da0040340c40c640c4400e80087c0408804c2da40402c4000c00340014a110410000064080b0320300400c0407101381300a00107842e030b40c88 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 533448381 1250 533447131 533447149
    0x11011a1c1e050309120a0201081801020712121d0a0b0702030d060807090b180c0d0221010503070b07031d0d0605040f0209010f0810180b0727120201030902 68
    0x3440740ca400e14018031500d0321649030341122a000707100e0501100080c069410101d42c2c8164243e050392011096920162031220b0f502541406100c0756600b44002e0700050080d4410716200c90080d10349107682c2030311aa00340d0680b02041c4903417078101d4854259403100c10f4000b4281850300d5001004090302d0b1394100c012842c50140030380e2260703070600704400047d01080c04968401620b15601c0d051101040003001d00a2034142d00000715608819007001440880d40d04029240d01824940090301e05602d40c00c0134080603500c16113049000c09148010040c070310301080321000410541c0c0709141815819280982405154000e481250740740030f05554007a0f80d14001c4001441d4400070400660402d4101080801e0f06044100d018080f0900049000d510320b46004044a030300100518294005402c0c24028101c40030176000301c201044400c400040700929918402c50281c1d980c1da002440c0e42c252226101d828520140354030074100d00900c060641803135003400311a0203003004a129500340c400300b82a00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 533449631 1250 533448381 533448413
    0x40c020c060d050f0f040302030901140d0e010506040501060e0904031b0807060e070602011506030b06090d031e08060913020d051009140106080a1415040311011a1c 72
    0x8000140002d0004a0b40d000034080c840103c04904160b640070b4000502200699000e4090390040c00754110a47c4aa01800b02d0004c2c0442d94a081c440c580c0c19041c10349910100c101c110ba5100c0082180d281407501c0ba150050481d45400034841c4030234000709800500c0900054100059080c1054002c44e042107404001540034030a165240c08505101004102a411590a81c018040001501481405284422181071145403c0d0300e1504070180d000b40280003860342c0100c024000c040e04c0360703511540620154001d0300c5450308642001c24207600c15030020303a09024031980070140304407525036400c046e9000300714081c082d03242c070b003d4000110709100b0304200800c00d12441600b500544101d421000c1c0e0319101c0c10803074150005245699003666558060001a82d00c94007400d004540c0810000d0008200901614103e18086841205014080f1401c1d0302007a40040154401e0609100b000504550100e002807820804000919102d80526905061f120309120b11414002c1402e090074402d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 533450881 1250 533449631 533449639
    0x30c07110603152103270607060e2b0e01020a051e0f01060e0f071803060606110a030207060807180e0103030807020f06070309141506120d0e040c020c 66
    0xf0b01d085600310111894500e4614010140d64012112078021040365442c00403d400c0614100140b003202082c40ea207504440140c1300c11100d02d04c200170344480c401401020f010314400f04000710103030a01460000c683c4809255003422026040d041480c0c410031844403000b51501d00d81034400d801c0100d01e491000308000d040ca00542c01c040001605000d1412106591001526034491003640300900301c2d441882014108131002c000555081047c40c002a03002c0030505190003002c080c0404511409000c0c1c208a407203070b958020600a40750084005143d0000315030092070824034640c0c000307448009621174101804028408a400396011750b20701c46010310f031005000d40d0303030f9071b581d00d401c0e5049020700c0b00703801149207603010410244c400305480722084082030041c0030b0760701c51140850080c851010190340c82d03440c2d4201d690f600203051140c4c40100203801460110340c1080e0003048092003144402c5806030348000ca03201c10a40c1c0000c00030303072501d00854000940707034031406040e4188040917619680c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 533452131 1250 533450881 533450887
    0x30c040513050703051807050409020303130603020903010506100c0210031107240204030b07050309150705030405011506140c0c0904150b010f0c020603090f06160809070b030c071106 80
    0x8180d0990b481248600000e540501079604c600c400b40344516000420f1100c1c580101c3c10502032418260040b0703940901c05800c492034001c5281e250000e009054101d900000d0f00094540417501d824011603410600884e0b80184280c0648400307803020485180c000d024081e1041480100c3d4001e0b03100801c03803a41d044050b0354500f030302d10f00300000001c0c03002d04c543c08064900b00302c00e1100c00340c03081d2000d44c2d900202c2001c40b0f86491905407165000240f1f5141c0303601c10280040418000d030050300e40503011540705c5030745034180361420a0954500c50560522414030000c100300250f40001c0c00708041c0600e9142940e102c44c0c0801c0c160031320380c02108540d0041900820b10040040f10091442c00d458031450030800b02080700011071700d0450890040c00010f66121002006d481c0403002981c002c00300c5000c44a40c100c00804260030500106c2c1d640703054180281101c000f894100e615264440c036442d015100090400040c0d10b02c80c0406889034030200e0340468814204448910350f041d4060000b40000d803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 533453237 1106 533452131 533452159
    0x2300603030f220f03050c01030e030d0e01022809081903050c100614030f0c060a05070804031b050a050108040b0609280c030b0118030602030c0405 65
    0x401c00e070700000308a8456241915400608040b020800c4c41031030350412504118003443c030581450b0034141e901000344408021201000302c0c4100c00151600a44061030090195072032046c80d0400410480c83c103c284401c400e1510001030f03440303d00e4984c491042c3ca0f00e4801d18078680540c02e40c0c4141d484002806880079042000d65078080380c028600c00d1020744240c0d91280d0003040200004040031029081c01d1250400700740000005120580115000ca056031040b0f0303804d40704000001caa004200710348442101e005540080350300520100e210340803288074482c1e04c11b05208662040300020b5650003006098440c1c0d4000c0022003003560340d80140501504020100ca00500042c181c0200c3c1801d00515949101965500045d00304142d540140c1142c800d2076510b41400180040f08120454510021302640e034000c0000d61240ca07107203000c802c1800303030360881540168a659021f03 = true := by decide +kernel

theorem cover : BRFrame.Cov 533273381 533453237 := by
  have h0 := BRFrame.cov_init 533273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 533273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 533273381 ≤ n) (h2 : n < 533453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
