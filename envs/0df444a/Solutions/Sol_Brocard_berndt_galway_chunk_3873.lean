-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3873
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:55:53.15618+00:00
-- url     : https://prove2.me/submissions/6af43a75-bca6-4f81-9a66-25f1662ef235

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 696402877 ≤ n < 696582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 696404127 1250 696402877 696402899
    0x1311040f1b020a0b0a20040b040f050f101808120309070603060e070e06090402160213050c0901030213030b0c0c0105070201050106200106030606141203160b1906 71
    0x14500d45072414000d4409000786000141090040360000681ca425031355079112030002d010803a1864155541c0600140d040052010152003e030080340380054440341000452041004a540200d00ca010551402c030080e854050840d404240b50707142442d240100c1081c801c1c00030301030394800c1c0054850402005014a107241c0954010f1f5200300c00c1d51f014558480d03040301510301a0040580c02c003c1030020524080c05256440c444203005003240b806c0020703240c0040c00300e070402242c140039030005400d981c0451800409103504154980c000b00118100089039041381c1c002e010b5aa07061650000f092009074030180e4001d001950301c40c038a03c0851030420281e4000350000e500c2c5413969806c08004c00c0400d80103005141c1030300c5048e034a10744000c2402d040b000101c2408485540030355641c00020001c43d03030342d0080d038000e80014254021503080300801d03c0b140040c0706040ca0702640060007940e14030713590ba500811481c0d400c055901c1c20350f10380310b010919400c0002d002c141028600403000845400300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 696405377 1250 696404127 696404141
    0x2070506060303042103090f0906080d11060c07150207080705060f07021207060216050706090618050906210105150303070b0103080d0b030709050108070b121311040f 73
    0x600668025407103040902d56a401a0700906496a0b51100c544104004602c08503905a00903c0d00c6c2d0352543d660f01001304424140c2e00a5000d085d241e482c140100201040041d00c000000e16100b074920030001486501e4402c00390480c180d82d20300194070014490a40d410404d1708030fa15404558900a17071030308a8150388100b50441e0743d402360000090540701c0c42c00f0101d01c500712640203003480325a2a20350002507804118125405582480b204454100080f548083e1310b10400c0144009414000d01421000b6642e010f10208403800411034200142400698100c560640316106981c4940c800903101c2d4880b4841040328a44200084104040540041c0d003e1403046408400f040c0e01c4c0c2c1b05258403480340b49006880406510010000036035904010920035039160030001d40084020002410456540c0c03100c2c44060704c400040c45030401c1441013a00800301015424603040560104110420005003000e100b80300501c50b400c280102d441c0044154800200301f04042e280355806031004202d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 696406627 1250 696405377 696405383
    0x2040803031b04080c0d08040e090a03140c030f0a020a17070b0a06030302030315042d060e0702071208071514070f09050f0609041509150b0d051305100207 68
    0x10040440c6002c0910200c43c00c0d02c01c01000303400140040428843c454640300c00c11070352220204000a00d44c00000441070151907001e000e08440029420014894000314030340351440c0e80c1c10031042c191103c000080361f00c6014540b456507103800d01c0403030683c100741100202030000100000e8046080760003d0082040342c0c411080718070b15803112882d00040f90300038040200564000c00c04103441d00101540c00711207607130050000c140a0691590104100500c0e0201002d80980340c10801038a4200e0240d04090007060b10a10180e141003d8001c1d41d80340248510003078020341043c0c1030203002d0000c048801d8960080550a040d00072103860a00410710000780840403045800410560b5204506e00055455180c0d104045142042c0401415194800404c0d43c4140e0030030082405403990b001c0d080300000f031081c00f454070ba45028030005c165100c9015901184004020501c00c01e4004e40581e2031056502c0030014182c0e5984400d1602500340900150040c0f0440d07083d0009110250010700000d48 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 696407877 1250 696406627 696406651
    0x60906030609050415020c0703140a031704052a0a120b090106050105031503010f0507090302090702150708070201091a0108010b010908030a03051e01060314091b0f0409060204080303 80
    0x380d82c8035803100310f03401aa002400c001003514002d840514580107401c4404114058644103962a13645d05030140d800828071846404c080c2c00c18081c1038101a0706604060035040c2561189403075a900c0d40c40700680103c414100c0c04840e19240140810340c2c1c01c002c0385401402221440e9165113181500c10b80c80201161150500400244060310602031442281c0040e1101c1c0c0c06c5444000a10580810100c11aa015961400c0c03000d16002e181c011039000b191240c40f03a01c603003403c41c0144111800002e049105541c0100c1c1281003003030b00748068940c48030f0740f8948041c1c82d441d110003c0b4007400300000054440100102c002c890b44450161882c100d488880003080528a41401921101d2903403007180d265400a204508910780680c1145038400302c00313894102c884540c508040415142030700310034002540c030190110b40b0b458007200766410210800043ca140c0c0b9002c25500e90a004903c40039003e0b84090f4000115600c0d503401c04030388076034000e205546490321802c0c0c8603600d8104480c410f803110307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 696409127 1250 696407877 696407879
    0x30409110316030b0d170708030426040b0d09030903051c020601090b0303090904020f0a0308090a060804020f040b0a05030106081b0619031107060903031d0303070e0123040609060306 80
    0x940644201c580d0010301602e17004551180b40c1741c0c0c4225404a2182140300704041000340000b03402d841c005c41c8039a00c1a45500c5015460814803100c12800144903104a0020001807080140701e40a882d03440c9500007001c580000300c3d150072030380340071240d00080144c45080032084200c00c130303141002929071180d4200c8140740c2c1c1c2c81e14400c042ea8100005036030107030002c20404a81d0b0031b0020040fa44903001901d0131503102008400318580c0005503000340c9046101059118075031405900080091583e443c222210f82410380001d44002540004144600d40d01da240c0001900d40305000002050010020000f071a5142c0c3c149403a00d014845410401c00c00d18404110392400e032095895150701c0d01c0b170a0344007811100703054008141c0410218a02074042c4a0341d400623132240184c032900c522944c1c010660450414400c880180d0815031110365070024000c00080c1544030071a0045e29000f46041d41d03050403403208000080711340c010400014200000c0100c2c0007a0000c0b5010100c48250360100005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 696410377 1250 696409127 696409171
    0xc0304050a06260c070206180d08070506060105130b0304030c1e03231e0c01021902370303090c03060b12070609060e060904061806080c03031b0304091103 68
    0x1300d4181c07000103001d024040c0581891800f4002c04c00042d000d0901418140b000145400c00074601142c814000140c440100302e000d215076a0041001e0900f07a0501c014a00c42041010b2140603404003204080005414144a0340310b00301c085400c00901d607a22020054400c0303108405000c1038011602c004001c80d007000c500100c02e50740d03175103001049017000b103501c4001c0c0014900076000707007120505101c1042411400c0c03000f02900e076101100c0700c90b4107036a22000303801c04005e0115101c100c0d44114011f004c0020010802e0014500036900500610040c602030300105a640005040c20390001004800c201c0345521000c2220030456010341101c2d4850301503a0b03210a20300601d8006010010200302440c021184107050002c000e01841c103054408010400b01c2d41c05038880c0e01c04150854101d20001444d10402c07010b059104c0244c02241d4000300442d0740d80c0305034403403190051105104071800d15018001e8802600036030b941400701010703500950700250400c1d103a840d4042d0144804d0304203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 696411627 1250 696410377 696410447
    0x1021323060412080a181e050409030e0402092701050906032a0f130f050603070303270e01030b150f0906010e0a08010c0519080c03010b0c0304050a06 66
    0x480e6240c000d4000c40704542d6490080c1a00184904024410080460410301d61046003510160847d98024180500244e240646000c000e0340568080c0e440e010020000c00c0c2d0165420303580c1348080e6030140e51100c81401046020b01b80403401d44007010708009401079614240107042c101c03402207480c402c090715917004141c1c8841c04010549100040b0600c02040e0121901c51038200749402011400c05501706004900d0307940c2c081d1110b0350606d40c0c458000000080c0d500c0f90540200703044d0010410541180e4000d4207459041c001c0b48540320fa580343c10007001703402c1c481c003c000e4840600201802d595070f1800241015041d41c0300c403101641049002803609010b458141035120040902866407207400056a000002543c851f030049001b80e808242100c09000b820302080d0541d544030350750303640c50314844078209242001c8003c21002405000e8900000780540c0d0542c0d41d0752580654400981c00320601d503201329071255802520001d400102140c200402c0c042c6101c00600003540818042036500e9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 696412877 1250 696411627 696411629
    0x1113080717031c0f0f0e0303090f0c1e0a120305212203020c03030a09030b370902030607270803160201020316050304051203030106080711010213230604 67
    0x1054842e03c80643e9903600072500b02425044003c0710006103045042a403100f0f40e4440c5643c0c040c10f510000600c5080041007000c00f16032500c00010302003007000c8800141e4199042c44900300c600c010800856110740e04c600c400300080100c0307551440f001c482440e005c2c2c441d8109004142d00a95504c020f603440e01111240356101e80c1c1d41006d1180c0e40304d164000490410410b102c140d045201d0f441402d030f030f00d883c100020414030100e901c0304070b211441e6241c5250441401444402941455800c880031040300e40383c00b0002c21501242d22030071280c05c21511000b0000040040d41c10700c24042403214050300580409092021001d440172601e0603580b102c40f03d5000e0384242c090b50b5004010182c00709941080c4280304900c144141e80c034108103a21040d07114240074105135a81c0e040010200010714120032b2078042407070314001071400c45d0305d00400035291920040058050000b50940418112006c0d0b04031141526840714415000703480c0e0040310010341821421003d4a440c0704800c1c03c06240c882c1c20f0364 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 696414127 1250 696412877 696412897
    0xd110d050906160812010b0309070602010b09130318140114070203070e0a0b03011b030b0d0335071101060807050d2a08100605090603060406111308071703 68
    0x1d864071222181c601030030000c40d5015600705400317110103d440340b880f0007401d00800c101c00c1c200d9140c2c10842d480e83e0400a0310341c010000e41e8034041e01d181c203a07114180915070088640200a464007250f05080c1c5030540496004441c110784030340c0101e0303901d00307150789246110310030780c0c41c0d000b4041036649466891096500c080e501d640080010415024146400383d0321002d01c1c100800c6441321080882d0a40341041815032003d540900800003907507040c456000240e400f01e5004821225946010b002240070540d880c4180303550703040d56030541c020312148103032502c034440450035a4501400004c0a03142200c04140955003410800150b40e4030014800040e1200288102c1200c00070b941d8a040400300110400705410350481007141410540c40d24400810003c400741280c440341e00c1c1034500300d0741c484d04514426002c330741c24410b140c0c4001403a030368441d622210001d078202c000310030302110b4042c6503450300b610305940b480030640400200e8800120b0b408010f00e0250040c107100c4540d1607025814003d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 696415377 1250 696414127 696414139
    0x60e030a0b0601180806060301050c280c08040e041101090803091207031e060e060114060924070c17120f0d05010902190201110307051b0d110d0509 65
    0x400d0101d051000305a412a20504040750443d6444c2015150600103600c100c860350003850801c411801c0a00559070320007411200d241ca480d50350900c804a24007000c0c1e84145158426201000c15802803c0c88100150800890354651350f03a0741c40c046600d01c088400711030315030865480c4103440d4000c02124040e5104203016606041d1500c05200950490134880c020611401d030002020404010910407845210503504900082c6410410165070a0a8410546038000001008140038500400010340e0003100c01941d02e08410000681212a200d110300600104c01324490a01411360018980349104a60546109946020840108260b900c01c0103094011041001d0180342110007000000c1094240505144810001c101200c42c01d0300400c4d80d20750f001401d40c02420700500110713030700c140070b20091003400c106501580c054080503004800303100000c1004d414002520383d920075000001d5084400701210a00000e10364075006510103c3c80c004c1e1032440180324402c10448101c11000391403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 696416627 1250 696415377 696415393
    0xc0e15090f03070e1608070c11010c060212090f2b1404090e010c17060a1a0f0c0109020405011d0f07031113030302010c02071202092d07020106060e03 66
    0x5010000702041c440d154140030703044011071030941d0245200d004e807140c84560b610f400d08025001d08032010281541e4184110007440c1d4000507091102000422020310307084003150b06914000c07000e40107490040400c01d07101c808000b24501c00180c40810f01e070034002220480c00345c0b0380100c1084c07040b403a00d490079841c4003c07012003951300410171907003d00013a0f501c05180c00c0e84c500c4010100c1d0464401201180d440309040c0d04000c0d8802c440390080c9a5581a000690805c40001000700c0b01501c6001004030000740040e990002e107a040c1c1c2c2c0030160000346184d480388003582c2a4002c045000b4120303ca50702c0d0000201d0741403542000c108004628000d1100580c07541d100201c04400300400312820940c8030315511031000c030b41602405514145c001c00400719400d40c82c0103400d4501c00800181107520885040050200a481080388241c055410b160700303807554407000c01d203882444840633103644445070038482d284d00d1003440c1d8403904596000f0450107465410071101d1000b007401c41c507819442514 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 696417877 1250 696416627 696416629
    0x11101b0605040201020a080c0609060109060e0a0b030c0a0f18090c14030a060e0d03110307090504021e13031e1a130c060f030608191202031c0c0e1509 66
    0x1000c0e5402c40d00500480ea1860740940d1092101c0e8000c80c0d8031040c0780c00078020300528450800140340500070405007800300a050140a03e1540802480f43d607a050300d9101095071030b1820701196240080c09418201c01d6500c1e2009102c031080c0511a8043d940f801d40500510591184600140e1507404000300007020300c0d02c403423091102c0110015603403500580e54000c000078800c3c8551000d001680d009018110450b40d0058101c4d0b078100034840c5110307820070420074010303070005128094a0040b81c3c01a110400004440c001d01499030399082102400110a80031940350b004210449114041c000f4181c0400306001103040003402c801012100700d040d891018041c5000e00ca944a680c1000f00e07480b6842a4840c45100c0c0142d610000104071112a00c0c0ca2042c0e05004090142610100174085190340110052548001c80d8003d4044d154000901c00254424000c403850700034000501e10700c04a0616000b8010702d0100d540d0408208111040d07181ea040050010050010314003450b414110060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 696419127 1250 696417877 696417881
    0x6130503120703020c1b1903260f0310031b03030e0108251e020f0304150207080106090b130c0e061e0c06010e060d0c06031e020711101b06 61
    0xc0c1011003815001e101170101c0013010000100c100040c141e608000c0442c001c2803250000d00742d50720084d1450100002c2c4085199012602461103c851038280c0c60340a040360090700740554800031020320000414003820400880c040c90a403401100194801a003154010088000510004010500e1036064404640c0644105a8802d20854400e8001d501c0c1c903151900341502180c090b40415071103440c1110304e80c200c183c140820340c0c07180010990b100302c5500c02a03413400b40d80300d020411442e070340303292540a2081c4203960040800f00000e0003450340310840b920150200c42e042c18001e0128592040400704503000315004000c00d500c3e1801046448401d0042030b80c03080f840b20080044007401e0300203404604000707044080502003d0407095040c1405000201d4001d40803522904800c040c020211320f01904240031a040f6050008542c0c41c180c42c0302007000e0202c3c0da1f031210103101144803001c1c8110044111901401101c1850703e80300c104200f600c011090304140c080c425408468074000070074a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 696420377 1250 696419127 696419131
    0x30f061506090d0219210203070306180c061e0306120311120708191e05070309050a03141501270b0603100e06030c0d120e0604170613050312 62
    0x9410218404500e80201741c903410b12400d000d80f400089002041105009800c20300d0900d01448001c581211540000307079a08a01e000140650341c1da1445003003000c103811700e08555542c1c0311340618212a950f003009440d1250043c3c8044d11001f4541c011000c0c54460721030302040e902c00003043d80c0024890f40b030454040700410b052266a00c15420906618200311024015491180220710364440c9100c682c540305514083c5c40300180003280c24840015911b02d2064041c2108500d82607450b50218182100c0c07940c1107910058002124a8010051060f5000f0302e10115100b030044684452401c49c5801c0c0720030091060144040011b5401040d2aa40917034007441e04040c40d2011a00c0d00041000621550003038507001445050003030304000301e0340a040513640c40103048000d403940c50707041d8002c10044a40844000d00c031144281c00e0b00d41450140555281c189006802207403143d4070358066010b00d481c4984816020320441c80041c1301d80c0d8810308001400b03039002000d141890b80100c00c0032650400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 696421627 1250 696420377 696420379
    0x41101090b0414010e0a030803010e130c12051c02030a0c0804050301050907080d0503101202180a0c1b150534030b01030b0306061e0904050c030f06150609 68
    0x3a031880080c2041d440300140018011401c00010b001c040c5100140040d03112194071405002903200400108041d4025281107500e0510a441980e48a88110748608240c04000389100c0e0409400300d07448090a4034014480d101d0070231201008000741ca203032034501203584000010f074010072008020901c40ea07000e010151094110070b0400f511200020300351007080ba002c416580c8100000c1150000800000320b022889080052071410000180c495401d014085d000740ea007030f15442c8008540b20304040500000500e1300c910040d00b4840e401c8800f03000240000c1c000920810056100000d59010300011746510021924a0880641000014040082c0340442d908050110180400401203100b00400100d00c03100b200084261005812900907490050400d40b40805810058600003405900803000725001c1140c590090504030000f4003005a60342c01007601810b0004010300024034001a140c100c0c10b9805681e041d108855440408131420030341c01350101001255130915500402400d10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 696422877 1250 696421627 696421637
    0x210020102070b0f090115060516080c012306100e0d02011407050a3309060b1306051003050c0d05060a0e010303020c090604020a020a060b060403120807020606030a0b041101 76
    0x5281c0d00c0703180610070202c0e00c0c05192080b90b0704100f0303405d2080c8908010b40e04817a800d00c15290408070300070958004c40040c10300c08510a280a4180400f400c1550f030341c004203400a100b064a2104400340405600002c203038481d4000703020485500c1c20b41c01052015900d03035681c40165210100708001d02055580c180c2c140134802221488540c0c040c00103240c468084c1c0010002c40e440c500c1c1c10280310345210f12159035440020322071071a11b000c0701001414803040f4500864440c0d0b090800400030602c84040c150f022200c0204169002c441d50003000482c2c0c401c4801800d800401101507060f100200c4500110800802c00c2480e194001d500884e0840b10290403000320030345401754000c10603420380040d0096400800c842c60103182c24200f5942c0004151000d41c1045113580c0027a58030f805d0214024565516119030422130303100d17101640c00558105401240ca4600381101030026401580e1000050103108000ba1841c240058652945076019081e03d94a51715a25000003a240e901196070400c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 696424127 1250 696422877 696422887
    0xf0e151303060641120c03030c10060b030403091a0c0303240118140420090a17030706020904140406060512010e19050f071d060405060a030210020102 66
    0x114184948009080c000368003104038148820702401c6000060030340208100c00700e04a00b003a80340c101c031310100040196035880003010703071820140c2802d0800c510a80c00d44030120303690010810000342940c0c410b00c494420000d068503001c3e13a1010744130480300030740421402501005a008681044030025418490f01410500442030b03131405c40d8070695000001c00440d40380c01031815485d40c80c0700d80c95042420a01c105100e6603e4074410f500081c4a0303d1102921201d22140c1030301c594100c101c02d5282e400841088905a64000080c1d130455030700c140c0242d01900d80890008814412460306120740d0300107609007000303a902c0c83c02951106110350341054480d01409a94410004000c0c002c0d41b040d200072176003e041100340f108545069601c181c490703061420070f010188000c500c4e64480c0c04600040100d05107507040075440e010659094640354070900c400000c004144100080040d1454280b01031141c540e04100010341d2000d85a5951201500701c04100502d0700200c0038202d04010700025080c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 696425377 1250 696424127 696424133
    0x14030403060f0518030c0a021908150f09120f0f0417010603061803051b030405030f060f010906050f130b030106030b0412051303110d0b160f0e151303 66
    0x7a0b11540c07120107902d42c640e401d000000303600581050450f00090011801c0005044503039589183c051000307802031000d1a00f031180407003c005124007074603200c0100e03020321f04162404aa1040200c50440c455018840840d8020901140e60030625464000e26400d00060500107501940b142e11140000002040000380c08000049040b10624001c00001006451401c02c001542c45241e0003407000d410039010768000a0700f01e400e0b603030303230002950002d4a1148007098040c554482c0c0d401c41e070303030501c02d01a055041031400a502032080d02c0400e2441110b0342e8a86401c41903c4c0c1c00c5c000d160703000048a00201d02d5051514141e9a00548a5404185070030020042402c680b81d0ba0020340308800314800700300c14003642545401400405140141c03401000d54802c2c0303008a00707400f000704410560040c46506696500b05203001f5604607003803002d1820528941031800b0040001140441c040c4100d6070702030780c05564180701c1c80c1c0000d000e42d0044408031303401c10040d600500180e9242d0481180c04008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 696426627 1250 696425377 696425381
    0xa0e07050d0609050c031204090e010626010b010e0d060b040b100e0114030402030601030b07050705010c080f1b0d0b04231b0301080c0405191e1505030a1403040306 72
    0x566000b4100040d1608013030800904000000701d00700e00030740c0903e610b0700da14601c4100300c8044034411107002641900d007052480c00760000d6809108030300348180565180302a41c6140c00d003c83d40d03150082204002c00c400548a81d0250352200d03a105005e4080340001c502150410440c64800800000c0e041381c0000003e04400b407145124000291030280700e031455608103100480138030380099481d0440c6010380c0029503480050000900c91107102021038000b90160094610b1151301000038040225003800081024204903000d05014031000045060801141440303111401c100b4a540d1404080015000c06000703120513194204c2d071b481904641e2040c2c000c5030b840400502c0612505241009a4a40c0350804500081c0f0f440e10800c1004200c101000601e00036140e402303907004079060795194281d0352180c5440844192040c14121001184209d603414035040e050038040c1003000c030103007584280c09001c0e42c5c080c0e5a0550b1000351500080703101c5020345040445d40ba42107907c2c01d0b4481d030311102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 696427877 1250 696426627 696426649
    0x1518101116020415151407080d0905071d0f01061d04050c0c2410080a030c082104031e091a0c1006180504080901120e030c0a0b0702010e060a0e0705 65
    0x80a003203110001980146e00102e0440c490300e12100302d5042c440036495849440c802c0c0181100020754035445d50b000c00c14244040b03402008a20040300c1d80e4400400454095007080307400c06600303d110400416031500403194615140110b01070801600d04041c14400144005440c910070f00100b031103800000c1408100111030b1305502c90004c201c0c0b90f0141711700b01c200c1c08060140401810b940a042c05052400110042c805030945424003102071541801c036668400d0344051801c60406000000d6a2540c04444600862082e80c8400240007403170004030021602140040009101000400545c4025030400d10510307181c0c00a0717480c08855001e25407402032021513201d041e9803100340c100074503222500500c88100d1030240602c2189440c0d0390b403021a1144240c26414400401c0c403242c1011041c1c0d100c4c84041c04c0003000c0302d40e00d420010440daa40c00000e403044644c1034071007000480a07031060044031000d1200400422040d1102c5411801400300c8500752070092003082d000280c66659068660 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 696429127 1250 696427877 696427889
    0x206130b1627080105070804030c0b0c04120809010207140a050919021b24070804030903020a0b070b0c040b030c07050f0616020609010507020d0509031518101116020415 74
    0x5500300d03240003800e44c00d54000900780c000307108a0108010100750007125140c140c1342c0c071806415580d6124603200a0301e01454000040721b0580e01911350400803010000c00c0880003d03000c58010741d903a0080c0080061a200c800c54001c400800c0400c13241c00c00c001390513041408a124003204642e80804101240c21450050f0400c00c00e000345040900e0381481110138851045425002d41004110b811a04600c05461441040b05000001c2d05041c402ca00120240d80c6c01031070004d80301c0e5585241c0d445600008002d9614013010400b06d010841c405c0211012110000a001d0031551000d40025081d041120705844d58092800340c51585401848400d202d81c00403a2010380426825170000d103445c0d001400303419142e24000a12000c56000600b0b01c40301c102c03919010340c0c1d03901e1b200046030070140c100c211444070019803404d021006c441000c6418410f446a41100d4600a00503407103002d881d4041803a00d40c2020412401c040d0245200c0400601d90000d003000c194400d0340c4c2103c080300c081e00d503c94 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 696430377 1250 696429127 696429197
    0xf010e01140711010f020c091311030f1c170109090c03051f110a140a02010f0f0606020f03120403030203041103061501030f2307090519060206130b16 66
    0x182440c0e60304800545c001899501c021701c05480498081200c0e800003820390500e0126407003070303141001144011150414800b0b016a2440d8001100e0181d40c2c00f060b510041160f10f21440440001348034051514044400d4002d900c83c036481c000d050710041010000070745040605180100116404001c0d140d05049003092030340480103108806000c07036030b202890700b1003540104030350189544e20544403851401d0b218801c96851040304803d81c01040c1280c03c43d0003d034103010602c2c0104900764400e03001c4910345c1c1c00362000b85840c0c4075683e8880c07140c050f40b4403000345d0200c041400300b4400d50165512510a5000107051a50030001924050b0101d0b004c80c00ca0b07075242605209942c2c54005c1344400d0401c03c0b403d000111418200c4007154120401c481502804600010b40c4284100d46003801068007030085040042c040c246410580e60b00d0140702c000d84624030200e14029820407403016125003201a50f1519102c8004c0c070709036084a003414008000340070402480001d10404c850b1198203103d104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 696431627 1250 696430377 696430403
    0x30c0a3506010815210f0a050c01090608130602070228051014070609021903061506050d0e011103100801050907031110020106031505011e050f010e011407 68
    0x14003044124020602810001d100c810f0010300034140103003044c030000481d40c003903d40605041c504000100540300e41e215102e01c4400002c206404280b0b481020300a80980300789803004001951040d0b010711130340e000290401c0000e100d40030602d076480e03000317403082c2c40141c03501c00740b60002400c4400c0324000800d4074103002030140700c020408600398003c00b0160b40714a288103503008081c00c9038048003200b2852003400a00c2600304017240d80300001a0f41d0040c1a0307880c00001000d045150703425800100e69041c50030510005402c01c51520108450711507035140c0c03400d51080380250240c062503881d109151340b100d15242d5066a030354041d40c414034070346880d844064505004682503940241204040303400541c800d0000c42c4000c1e032178030f0a0160958242c2c01800c1e20000c02c900412059102819505580540d106032001300e400881c12201c0c109485a00541c00030f094200d200ca542c402d03640e01100c0b05d8000a065401041c540b050b54105040000071401e02c01074190b143c1d80800c204495a42c41c80c52 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 696432877 1250 696431627 696431717
    0xc0804080a031e02160501140d050c03070f0c020f1c0c06050d060504182d0b0610020607020a02091b0c0a0507061d0d06090503070303060608070e06030c0a 68
    0xf019a41000f040d20081c0780041c25114007400840680c090340b0704000003440300041e07110411003222941e4080940400ca240b0300801d5103a0f403a0815030300c46001401408031400c04074411542101d01ca90001c0c0403103a180001010410b02d0b000c0c2004494100041d503415001142c803000703a440051103035496050b522910010114200c0d1115000300d48210710f040030210030410721401ca040d80650140c1d0300c4280481d0007107005201c100d069100256000d371a015102080340c0e108150340290703810360b0780c0c4501c4105600c0990f1174410484a140050b485020100007500e06040040d8111100c10b0700d0a1201d220182950a01e42c40030600c0140d950183c206901000002c00c52400103100c07614060003201080c0030455541035008007000d2041d0901012102800140c2e80800328660b4080c0407039603a0030700c0f0315000d4041c000c644901c0700451091400500900d020700300c01101007100034040313407840e6a140d9036269550092144070081005561105841c00d080c2e01c04040e0307004002450b82c5c3c40140d102 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 696434127 1250 696432877 696432917
    0x2040c0804050c010302120a05040501060e0718170604110a08070609080706050c1207150203041a060102030405010516110a0323030a0c030c051006092307050405010c0804080a03 78
    0x80c81c004d04061040085210b1203480c1100290002103400010805d034859003040350162110b42c220a1901c0542c1091100f616040380c8000c03c141104142e004940f1340d22051110555a0068407141c590880c00001340080d030b00303049000080340000d164860260f101c048a9250014a400140218902940500003194200309140c01070156190035440c148000300308507210b882aa211074820203001c00c982c0e040289400f007080414410b0707003013152249018104101121400d44101c1c6078601d441c4046101c1c0e51001c01203030196801070315424544910181118040c00711034a042d1100c0c0a08080403400b66500c0700100011400703801042c038071a4120b82c26503441002c03804003c04c40e034010448031601603003141c81007c9440d018140614906060305000e41080114138401c00d5542c58443e01042030102a40300007611890b04c190b0207600c81140455078010501030303130f5150106606100402c0075611809035040868450107240b400c1941d42d90a41e441e090800c181100440c41c4041d0030010b0750181e0f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 696435377 1250 696434127 696434143
    0x60905040e01060815090703080a050901030c2a02180721060518090f060709060e0402031b030402180c0a080f1312030905070e0a0c0503010b0301061b02040c080405 72
    0x600000c101c030f103103042003050341c800c40c1a082089070b03c945800030341140400d20490004640151090b0b5949140400090143c4d21410328140400d150080c07a040d581d1241c20380017202000c08400d4448150b03c201c3e4003540748810740c02241c0c001903c5450325501c486001c2d015001e4001e54480310880b0120310b42c0581c070348200c80d424620407841d000c4c0070021980d41004492646045103c84825a00d030940c0c11404d001c0d2120590700b051061100b0f0111403a8401110784c11a82180e4600c01c40451900801081e407109440e140c1c98000c140c1c01c01030755445858020f54005100034a8441035000705800c0d00d0307075039000301d445910300d003004150702d07014035080f1400355801004845000d1503032504070045c01c00ca0b1502c1401a0855801300c690640d041d000703511402c202e540010480e8803007562961641c0e00c103082101c281c0940d60070086c84520540c01401540d05a85042e05441d00f10b0307007400d0040324410302a2001602a00070b00c1401c002580f82d9214440c100c1005680c0c02d0500d1806007404c2e441c110b11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 696436627 1250 696435377 696435401
    0x6020d0b060f19030e0a14160f050f0604120b0402031c0f08101a1c020903031c020f03090a2303070f0f14031305180423030406090504 59
    0x100902c024480058080ba80150212070340141c00848041080300104200f689107803045c451104101d0502a0303003003941c0d49010328842101c1503211140d0741e0708100100c0d0320810306a2410741c0c5040c003151600c8603041da0980e40203820356040942c0c9014404154255081c240c90300400ca40601081d410107114040782c800504001c10560381e50900c00420741240e440c0108104403d82000c0f440c101e00e41c0c074400c4c1c02880c800750049110300009420550701d03404501c21a020040e8410b440502045134000c0d00e0000303200134080c500708540d030b4441e029448008001166a55420002084850f14000c081d41c010131450700140f8959005207040629802181c02c2044c00da0b10a142680400d080003040340c50455205c510b4801c03222152400262281040c0c00060495600390700c1c148c0b20394000405084000030384109070150707a943c7c2091002d600710700011800f03032503916800500481c601c3d00310000b54451444415924440312000e09046401c00d80004002174881d8204000d140381500030018120340c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 696437877 1250 696436627 696436639
    0x1002030403120b0f030d0215090f0c090a0f02030a140a06180b010c0209040501201e0a020c03070b090a06051c090206160b0103231e011806020d0b 64
    0x10140c0700980020b00101c0392200d81500c0d14030000080c2c50380300003600030000107401c030b5000401c118000380d201e5036918611003c0b03144650002d1055100080d2003200d20300b5100280501c40d07041c0082c0071f24044000e00000d1801c1d16102000d00d42c450a1004500c113000c3c007400050140610b5004a085a01c080c0c40002d8590508138140310b920902030b6074045104e8042400103900c405000140d0f42c01c420701d10040e5025090004120070300c203040d08030000d5a04406e40d0b1114061030004070b0f805500941c1031030000c0c0c05a003008602800314210091a00c0c00440c0100c178400300c50100000d24160060b004201610004100200a400e000e029200603000e075051035810542103541c07000c04008071040e55443d0300c5e1901216002d540b81c04e0202d8241c0301802d00b8050b030051550034401a140e20a12085498152017801c1c0000e821061000c0a02e081d00c0401628843c88441d1103820080b00c2c00107644019540d41c940c41028100d5240c195106078481c0d10b001d0f0712901860741c484111030400130801e015078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 696439127 1250 696437877 696437881
    0x203130b010b090424180b0306010f050a06110a1104110a2708280b010b0c1e0616051b07150f0f030510030b09100c09050f0114190f02100203 62
    0x6517a0700b0700a40c3c040e0620b500c440d825481600002c0d00d1400b01c3c19805002d41e8002040728480c5184c0300301a5003084c0c035802d5900d40d0342e210440c1e503280020011545134120881e80c40000d540703840300345040e0600401c0860780b84030010b890710362030f031054000c04041a05404d2103000640004402072204502c40902c0420390719110110b5124603101003135000d10705c01d00107030462100200d01102d4081da04000322040c0c0d580c480c1a0380d441030b800038030070156a00c151a4145110f07042610103030801c0c0c46000150200c1d441f408811a1000290510041481018046000300101004507010944849002404958a800ca40b881c1e20f00440c070301c15082110710382d900c030192508407840200040a82c42c2c00609651f0324a010300e42d000d050740008040d00c02c1c0c4030510140500008040f00500385507407040011910040c3c040e10031a24511a094115042c01692100c541c018290b42d4252458042a540780c120300003440d1200c8010b840108010588903004110203550400440d10b20841041d41140b0794 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 696440377 1250 696439127 696439181
    0x705011b060207080c010204030825030c021915030603110307030305030420040c03020d0c0c24020f03010f0e09151617010923010b0a030203130b010b0904 68
    0x1a03a140e40601a2500002c0510810840030b00b15203607980d06034001c5440d07a49a1170582616030019040f108510b40c1c2c0c48c060192110721140401c102c0c1d6054860710b02c0034890742d0a0003502514644a05001d02d1406c0000504080c0c0d1415a09200b040342c1d00051401c0c2035180199404c0b48040c0d1003802030b0300103102400003d800c8001c0300d40054105400b0705110100042c100050420065600d810608008058160036016006409081869007043c0310005000a00311480005064050a200d000d4990380c40a802d0180c220700031017101c0c010252814105400030883d41d44203901200440c0152801005243c141801d207540041080c03003d881907203540344c03012030341ca140540301c0000302e424000c00000460085100a5200e01596440102076035a0702802d4014660303071001c4c00a80100300b6104855030742d0031100c03070b06840d003000d2501d04026000000720003c1d003005002d216061160614500422450a4054001c20511010555034011a02400f00751440074a1443c1c03040103c100c1f2400c2e13 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 696441627 1250 696440377 696440417
    0x420e010504020f04090f080f0a090e0709060e01050d090b1b0c0d18051002010e0f1504080a0905120a0203010f05071e030609021303060606020f0304090e0102090a1403070501 76
    0x148004481c0424005c11394289010130500d1407400030181c503070008030502c50030000400342c000785009484010181d80e4400c10644a076200301d0340a40010140c44003484414040c1706140a81001031400c54104513030500342408940701c10b032094a44031414400c020280340d40d44c888000c1d40005000003410000c42d0526107079900c0400004105000341d1100190105420b4480f0000030200180349640740156000c0103030081089005200040c00740ca8101401040c0000b81068420100d10158440d607880c2e8a8428840e000015504108141203000066030b13542e1300c01a40c00e00000c400681040255803040608440c8000b05210001d0308003410066040e8200e80c505104030903200c00305c0d0141d81e4400c0214010040c5030060551680701040964040d11187c41500950748580d4041028944031001642c0d600501454208180e01c00c1000340400d1000303802c14100070f07100c07000160612408000040350302800346c0010070204015075203100c580c5410805440201800c1c00c000000d946205150f8903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 696442877 1250 696441627 696441649
    0x70905181504090308060f0604050a09021303080f030f130c03080a0e030d030e0f0102030c03130303060e0a051e0114010f120c21060501020a420e01050402 68
    0x4030212518005040c4007000e054480c0240c200070000c10401c1e01a1601410078281030760160b02542c1420101c0e2002d040180441c2c042d182e00401d1800a21303c0c000b401e401030340c0309007164001910750841c000000740301ca5000e40090a09c80ca00582c030ba00c2c00c2a490011160010251010b030200a01e100703000c994511400303410b41e038014144aa840c00781c882e05940f05031007444050380501c54980300b02001a407540c00f801040680c1000e40d1f40d19484849680c1c281d0005981e03a40d00c54100300040b840108511030100400c1d882401d02060b035940d02c0c0041050201e003181c1d120040c5465200300984510080c91144071224090311041032941070007420306090361401904e505001d1026680740c0700c103000f418005092000380e03000b03000d15a85d901d4000c00c440c01c400d201da0361180c522881440072030020b000d51800c2c0ca01c103900a04103040340c0e498000105000054580341001044603070040b11f00712100002402e40503240701502c0400050300c0d02d0440c0d50722084039215914100600006036a8246910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 696444127 1250 696442877 696442909
    0x617010f0302090c36010206040c0e1b07050304061103160206030a020708041401030b0d05190f05060a09030f0903020105030609090712050105091e03030708071103071406070905 78
    0x54503640b1028010002e00c20440b0072003440e880c510428280510175003010b000c0c0103028926690060000d030040ea40e0b084240c1e0000c0000e8401c440074807050741c6002909038040003650060100000e602e03807505d069805020143d401d900300141c144101500411061405c001c080003c41c90006895424050b14041b100000e104820001c00314a0443c0d01d80c05803a20b003a000054a681c465403144060150305030a80c0860200742045c42c015410b1500d40c0804c80c1085c1c0200280408280020810f0034410740d15004440e9034130180405808207000300324080c4190070318100040d40d40f82504002d00b030301c540862002e04101c5c880c4400e00050746d205080e02d40003007054500c81d28a4552801850034211560001410707841440c100209000054003c24020b544160540351542030a401c41d9002c4420b80300d500440342d0081002c900118440d50800b54031010500d0028003084481c40355909503031184405461060080718030220b04401440016040362203800c00356012445d00740840d0040c4082d030840d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 696445377 1250 696444127 696444139
    0x90b0411040c110d0f111203010f09050402030304030623090a03090e070e04090c0801020c1614090121060510170d080c0703030209030a291b0706090203070b040617010f0302 76
    0x11003017641c042d2040c07204c07144a000903101c004105500321106030708244140c4080c03034440d40e00014104900c3c1f045074010754014010f14505419a00d030f5002600b80300442c002058040d5000904842c00e611596000e0900301d400750072045102d00300100740741d070340d60010610320103041c0502288a81003040c0c68118801500c0106440304181040303001d0810940c03003040782d94000183c0100609020450082500300b038100da42005d0380b100c1211400080408803ea00030441b100140310502d50900080712010b02e8901400d0810079580d50481641c81c04d941d590356000b0390030b109200030342424500740806407440004050306440d841005001810182001e031803000d00241c51000c4c90304c01d40407585004006021111004501c2c6004502c681550040c108060780d0000064025210306511600900601c0003921806684201c901d080c3d03840310340308503003040d074950983c00142c4043c4200c00c0148259008180c40750f26000000c0c018840c4404035244000e030543c014804c6080802800c42070303035019550 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 696446627 1250 696445377 696445397
    0x3110102014a0d0203041e0621200d0f0e060114030a08030c09150712180f0e0f06100507080a050c0307150b042d090b0411040c110d 58
    0x501c0640110801a40b0f00400c01140c010f00c0d0004000c0048810200301741c805400e051000003100180743c090b60340042c0040d500424500c12100e04039a141d01860400244e45540c801025038010030210707402c00d0541d0208105041c0030180c42140c1e0f24a0740c1100038841122a00e00c201c1e120401409514590400480130114a40b030821a40c401180d00402c0355540341465091071095070080c2480c1807103030808060b90041c95102905607036600b50710070810000d400c19041706544418078260407507002000b0103000202c512244803140001d12840d40c07980141d0620340c440b0428800c0003811207001e01b031804180b5800d160300804031200c041c0c021500c42d40340d4041242c03c6503d80701c0e9024408052002140d4482882120480c0794002c2c00c0480003000306a11040600003514403040301c10310700020707101100d1200762150307042c0c110017503001c00000380c909603998a903100e80c40d06071800e03111481580104100f074201031040c0c5102e4255800d101d040c602c00104860f03030fa01404a150801c00140200e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 696447877 1250 696446627 696446741
    0x30b0a230403031e0504020f060f1204060b1c0c0b04080a03080402042a02101a01050c01022a07050405010b090d1a0a0e190804031403130311010201 65
    0x3100c54502110700d0b20880e0480890030076031014200a80d42684201c1e103c011002c0c02785420412109a519040c9990b030a2501083d00c152080c03400903c1030701d00c1034584400700300301ea69400b00701c0d50310405200d41c000765100c0c41c1401d9822421580007035030307000e40410040c06007800001b5000c49823a0f0524040308245e0341d900c08100940074549030a503401390320107410000c4001d1060448040c041c01d5003287c00c84034100c903103502640c1d010120003041c940b41030b0611780ca0f07504c900300400741039241200152602c00030300031504075a043c00070340c015407624000451044101c144080e0004144c2105d0600255051000c0c7c00081d101d4040400e102c1d060103a0342e60b007080010040c0750982042d01014502ca842c01d0321080d0041d221001c61021130f8003883c61311000715015120341d0308256400441140c00c1038299501d0400c064a12902000c9600c402e0102e581d01e450108018006144130b120384507a85800807001a0035502c04204003a1a040c4000c0ea078541c00ca0f02910110169101c03603600d21007441012 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 696449127 1250 696447877 696447881
    0x80613020d09030c020102011a0f0607030c08040e010f0b120703020d1d030a0f09030b0703090302190f060605090f040b10091802010e010503070804080f22030b0a23040303 75
    0x1c00c01d00c40c40e6003040105001d02d81c20100c1c001465000317070000d0010010015011035040110080c056002200b5038400c115030420b2809012158403908265890741604e40f149059130b00180e11012100501b10010301440511034829001000a89045410300006401c03070345030468002c0110040640c040740145507061250071a90514031520b54541380801c4d00d00805072660710141010340806c1c08000380d420014440c450545c220780d04600c1000181d100e040080300502241d03032080c0c0843c40b45007500980041800c0c068440030b44580718090b14111103203040300c207440d07032640414403590400c0e08200c080001e0159141d4030039800810040c0310b5851042e440b1115100313030858600c40d0320381800e022120f00e10003c4288040e000742c80c0d0103003482040c8011151480100c0707200700011410030218001490b240007600c540541b80c1c0301c1c60300340341e5056800a4607081d00d889421034650522001c00c00e014003c02c0707a43c1c0000c00d01c00305010b107880c104c0c0d90701000340d1104185180c20702010001002d1520036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 696450377 1250 696449127 696449137
    0x8060f0a0518011e061e0903050609030304030f11060a0c0302040b220504050c160302012a0305100f0e100b040b030709120b01090b0d05100c09090b0108061302 70
    0x91284090006030b12010100703040c24003818440000a0602c1e5418418000840088402c240e6a150448100004e40310341d20000c14500740611042c1c80c80840003500901c1800d108200c010300454aa03d4642401800f109012410744140000c0030300051000304040f50340c0e03070b000c0820a0081006d80003070f07204800070f00c40d50f48460010351000c21111f001600c0e8240e43c1c03200c618070300f8800c0ca080d070300c1d070781044229a0b040d00c04d54952603007081801ca032103482c0700341403501034040d000000d0500c19401281c03c0103546001011a040d0100c0d0720054055098417a280d0030100040d41405078a00b0b0000c080310304002c034003a90340152030440c00201021620801c41c0080c100d544815620f49a40d0f11031642c0d503420580d084030201d2001d900104141c8400700d0000070403500a2240d80c0c03c1d074a0704066100030000180d642c0d80082c149150305e00814002c1040f0708a44090050005145112482c000e10822261300000c50490030107000c42c1c01031703900c8180390b03403c004100c0c1da0022900400c15200020301c07417 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 696451627 1250 696450377 696450379
    0x5091f0803031801321b0d0f0510030314070816050705011e08060d0203030705010e030409111314011209060f2f0c25080c1008060f0a05 60
    0x802c01c070041c501007083d00043c0c0e140340c0c003c2c0034910144445032440766920700d03079441c00c1c0b002803600b40728180c0084c54650024000f16055444141074821002c09900c1074691035005501da480c2626220b10510500c1da220483d0310749100740c0d60035984d0003401e695501041d00c9401c4c6010417020207010890302200c4041700b40901d80d0080d0212071070724075150005d500c5901e01003041d80c0c000c552004242c03142e40500a2032030307840d081255100c00401020587c484010303a010302c024072407040040c00034032030800000f41500007580c61314a40541141a11035030074903141c0030709051205001086450128806951401e440107012801c0180129440d1300141000001607007884550000c2c41503652000c500c84075558002e00200c000844200010004c2c00d6084107071442c29130900c80c54010040140040000d500180c400107032480340c1d8161180d1149400c4180d508401c50308103e1000c0420041411240c161402030785403030900005800031800403d5035019400030300ca100301c0c2d41d917040614409020 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 696452877 1250 696451627 696451633
    0x1141e0f12070305012306010513031a061507021806190b120c0901050d0908040b0c1c0e130504020609040c211514061902030a0e0a05091f08 62
    0x9181d419a00d0040c0d100545941d444e24030b0480524580d110070300601100f840c0e00c0f0340703583c48001c011941580a641c1e21601081e206c44044000780c3c001d04010001c101c2040c0342c0c841030078008100125003110b002019003180041000400507100d102c50765044000c0c0c2c002c00e400030303981c4401040211541e00380400020342445004510004500040c05101c0d245510344043c540d41d91801700f40c148255010305022031000e100d4290081d401d40c004144040c4140102c50420741c0c2c0c4c0d2040c418503040502d04a4450300300c1c0c2424404101903c030f64001034001480e00a003600545000720380c03224000d078046241c0c2510340c0d00080c10354a4078421078000ca03101400401840e0a040c00041c2440b42c102d203204001c0b0780c0010f804901ca20240910303d003100100305800c402130b19042000c1c62014a203c81135070031500c117000b001440900130b18103052242840c0c01456a8540581d0300400d642a440c285c2ca2141184110601003034a86070b002d6640801c0d0b41e210a003802400081e4903010119035403040d440c3d48 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 696454127 1250 696452877 696452899
    0x80a0602030613110c0d0306030812040c0905100311030102090d12110a141506010807050a0e060703081006051c2c01060515070b161106090d0801141e0f 67
    0x300d034130000e22404c0c1075941039400c4500d194004070280c4145200c0134182407818003032190041400c0d40e0f0143c00c1441603c01180f8035545007204020b03035000311000712006605400401c28001021066140c20500310000c5181c100140001140c00030441c0340a0101c240300041188060301402030100d840100400304c44c46070f071481c076010111040c1803905280a004241c104492200c0110125026250586404415a07a403200407592500301540c0350b0704004c54070360301c895140c40c1c040c01400018041d0b43c5403096440c10002c148030308503080c0e0211040000800c00d41d04980c0305410344503442400d5907004030710080c1c1d0526550240c4810480d02c0c4401086204410815030b0550001085443c01d6a10030203450811004408074020348101600b04004a40080d04040520f0800d00200041e07003811400b218102145c603103070501c00c03540c242041d48034a21079140030b604039480c0c60043c216a0b9030401d01d0428540422040b59408030036880380340c0d031000e00e18025a503001c90003042c4003000d01400d00c0a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 696455377 1250 696454127 696454151
    0x90213030c120c08150703051b1201080105010e0408070b191d0105071b0209091204081b060403030e150d020c01020d0e0d1b05010906110a18080a0602030613 69
    0x42c40000c400c4950018042c1c0015200314042460350744402030300304c408404c2d99241c00039006801d0080c0340e2034801000700340c15003140255401508080031a102d0300341003503060800181c00c40d401a048a685009440c1c104000130350781400301c0d40c082e50720844002c41a01d0701502c20b21202c409a00c44a40344d402d04000a080340040c07001035031407500c0580284400d407074484c3c00b0341d143c0550b60034081080c1541980c190240c201110003036002003011044908203481c0d519000115041a00f0a0724550401c04052081c5104964150b0602404480c4140742c985166070150901c172040644070301890064040140c010701e100b041c0c51030451111030640d680e040350f450880c000e5110075050302000e407500c0c105960198001a0148140d00191200d44d004440c11004542540c3c890300211a0b40d0b480b540132100041e03c5004140070b104001480c107854a02c0e024024000003901050b5a8180846c88001c110000d000180000100d03013000740142d690300c4103000b003101c810000c140310900b40d0a1000034921 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 696456627 1250 696455377 696455399
    0x70c0906090209010e060a09090902060904240e01060801060f09240210060b030612030d0204240c03020c0f04020903160e010b03070e120a0f050313140901090213030c 73
    0x151103000d99941040021178420011140214059140001c1007284180840b161076801101d1040c001040507007400c2354140000c00340ca080369071850002da101d100804c50951109090303005411403840015040d0b0402400a22810051017144100041e02c4131056007980162860310260250001e400d030b80c01c1c06108a003401d110452210f400600c0307004800d546140c800d2113400706841c003544809295450f20020458190040d00710070790640400c10198622543c01c2c0700610040c498507220100d441e8134180040c2c03515200d0161202844000070800300043d44c080b40350008144100c034109201c8948c00e020034024003034901059011b00c08d0003041440b4201a4000c10101c4a11080300012603032201d000d942c46020075900303000810490342e0803203003c2c5072644c11448401050021100b07011599292100700412902059076160800110b50a5040145c000500a0a02d0700380802c1c0e8083d03c040860590703081446018040e95010078540104030794100310700011500202d6800c401170300c0b0440c3c902 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 696457877 1250 696456627 696456637
    0x130912021606050408190821060405060102010507020705150706091a091204030303200a0806090a0605090408220e060a050111060f06060f040321080f010605070c09060902 75
    0x10000070380000020765600c01e10854098454a10180400d007500008084030b034201c00408031807049092000c40c0e414071107140201c0300c5a000c0062001603082c080180800c5410280c401c2d811641420104508590001100021184260b5000f05c10100001b0a04028003816a00420150a001d280c000340504c041c050340c1c20b0401200800c140b40c91703006a042d6185840c0200d0049500140030800200f0301075442030000f800084045480c0000c41c0102d4107050340035488500206160700d0a0101d6428451401d5070b10800c0b440c401c0004a04000000b0310320500104010410f501c0090a10b0344e9040a5008030140300c502c3e50060021f035100c05100708154400c4499900654120350b001980350702c291160030b0881280f102410f00340d100c0018076500c054004000a4200304104400c5000340051001000114040c070030104a43c1c02d17814080181c3c0b061070300840304000e041c80a02a800c21400b02650444020f401c1240da910003c2c41d001c040e0480c5030740040b075818640840000c003401704ae00200 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 696459127 1250 696457877 696457903
    0xa120b0105030105340c060603080d0f020c03070b13080a0c0b060301110405010c020307050603072d1b060e06010b0301051816030c0c120e0a2313091202 67
    0x20013140d50758081c900d9283d60760a03c5c1304141c6514444c0070024040c1d01c070420070b403820b0361034801d40100729612007505a880c01c0d0300c12980c1c4c0070001000f4658100904c940010001f0348407041d4036240031151150366900444101803c0004800c0204620b80300c072a40c4d001307800394000803a64880300c15010107810380940301000e452120901c4000f034601e00e030600c500709612180c103148a0074142000f00444444051840c101d0309403040101c00320f060794542c0b02651240c0496620769000c101c0d490204803414041c02046800010b400e001070798007681080300489501501c40f102800030209042100142600c42c00391421070007000e00106440004600841c10f0744c50654100040005e569811080700404440c240107000b10800d0100c5e000b4481c3d08254140e000c1c074503044226001507201d014183c0f224040c200b001c509610780104d654203003914402d0040810b80e52500b403500340d00e402c60026140095181d0701c110323001d034099800c581c1030f41d03c6560b0040e088450b0154403880c049029503110b900503101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 696460377 1250 696459127 696459131
    0x30b0a0212130c14031f0b100c050a06050c040e15100c2d0611180922080418050612011119050903030c03041404090b0f04020a120b01050301 62
    0xd12001c03030b072680c102d1885511401e50603119140241c0211800c0d0341c03401c0b90f40d05000e20303180d06c0180c5030500c0310024952600c040014111a01c2c4003080b01d1000d808450405108040c9140f1000c140c0c0859807852464000c4808a10750750341c4000b800451190381c0000071862581c1d010301420403030100446a03076003030658851886444c8050161207184000800034840c00120200c244201c081d254502600044180c0d40304011619555400680307180668041d205900451040c0c4040c041a90380c3d00c03008000d440700c503010b003001510401c0459055a9440360351891980712800c200c0180110707030081c0800c04400c00c1a442c1030080e000601025900f142c418200c840c81c5020285061051030300c0004200b508616214041003c20366402103098800305012090200035415203080c0000d1080c1c0f1102400743d0341e194104405032003802c561899541c061854140390038001440414103980061030490b000d44d1a1742d55100052094940da04203041c070b545089c44000400c0600c40410303050360001c03070003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 696461627 1250 696460377 696460381
    0xf0d050912070b0604090206090a031a10180504110406030305030a0e010b03031602041508070305060a02120c09130c050408150606161e0c0321050405010e0307030b0a0212 75
    0x41c07015024108003c1d002e4403e101c08600186429032054a80b284007403c02800e0400740030010300101066402030311000c240c808407000d40c5044003012503020070305080c4581c00c5410f00c001c00e1800c0496941e4803902c1555100401d0501c001d648446070350050090041c031100d5220700e40200b8a4100390380070f0888604004030501002410301032450700080140041d400e00e01c5c100b00b900c00501c00031034180d0300156101080702010f4074040c8030a0160107648001d01c04c16182d450901d2401c0d000900030f520300340c4103002c0080d404008004158005100c2c200440d11000e4600010700200c0c6a50f584445442c6000d1300c4641c0c50ba081009003084811103401d841180003000700c018024502112420b0307118200b040480243d201503051410b149003d203445002d20030f600510080b1010b81d103403068503215044a410400c2020004030451645440100c0c010a031080001c013414038019801050305000000001c10200d450400085d4001d48c0c0020300504036003440640c5034002d42c008641c5040303541003440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 696462877 1250 696461627 696461653
    0x70518100203270306100303020d05090a030803040302030c0607110d0509100c0f0b04150606110d030203090f100b030c0d0f240c120615120b0103020f0d0509 69
    0x1120300319050007600914034003002054100502c0721041003601c26410707807850b1410a5207040018902c22440c03c1054010103056003400380c03130002c01030f0900d0304004042000610f141c407404071040c2280d80c800704035922a1964501030b0308600926502c14003e202d0b620801c80e040d0350001503100d5210b089429642d08a1590404907014403039000c4854211681201134041c1c82d221310390201c0554018985082103031000d036a6400d031207000b92000d40310a200000c0702d0300c080a0604c14080200345c07a08122900140c40101a5100c100040250b400e00d6030200006807001c1c403c1c062002209400f100307075a480320171507010340000c0121600141c003a105401951045042020300a400640c0107011281800300e01c0d900c4451180f035a01e00200c0340000810704c040c0780c0c2e66038001d01204403807648551219110705124a800c07a09181d009481c2d108002c5062080150803908414001030a0300011902070340c0c480c0103a0207885030690868003203900181c12281007002c0d0344003501414001040d940c1194600d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 696464127 1250 696462877 696462889
    0x70c020901120804290403050c0103050a0e060610031506120e01050105060706110915091305190e0111040816050f1e0d08030a090314192105070518 65
    0x15001007a00504200601140300001507010b0b482500b01168690001c003c3d520050a41147d4021503141e41302078400340103582c060080079440f011000007007180800c0108800d6460a0203001c03903010b03101421044545601c82d42018184e800810240e403c259901c0070001c000f140212003d04040c0e01d05002d0b0100b665041c0240341c12903100418050411610b0384403a00208101501c14007005410040c0901c2d6071500100850341e140441411510f52522000344201d80c80e80c1088016014609020040c020110900440e47c1d5600c14400041507401c0b440703d18010002a0050355100c100810300040c0c29800141200e001524080707641d4000e56280c052152500141502c59030100d119007480c14041c0e014510381c000700d4002080918110340c05c0d120491641d009491005100780c8030140402032641044010785181303041c1000a14000d0f04140301c2e14624007a0402400300300c03007412803941040840440b0481200100700170040f0f814203580c0580240d10011034008400b0300d00d801c14189103040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 696465377 1250 696464127 696464159
    0xc030703020d08030c071b0302130605060430050c010f0809070501080c1303050120040b040506090303041701020915070c0e10030507081b0a12020402070807060203070c020901 77
    0x90500c00b0902c503641e0742c6006a81009100102945083c009000820103810803406611050895a401c890450060090030040485000651401c0ca98208515211034040784e0407203480110f8490808071a00451580c4074801d40101d6041214000070700a121006c00e40740c0c91100c00342c852294140195006540248080300c0c20b046c1c582024030108103950060403ca0f43c0302403010681403500d0b41e4803010701d0705960182c0084d14580e5484092144a6a414031140381d01100000c0550600d85032505500342d83c401c900a0300c2c001d00c0d022640380380c03544042082c0c402810440d6807800508815060544c002d40025103042d201303d180c0703450f003159050b8040488032240d820800800b0b0403400c3c1130182d400c44d0f202800c60784401c0c0b0802c100101007803080c44071101800d40100a089001500140c11044040d03204103d441303984201820040541000003060005d0390513034001d41c8524040c20031180c140078141c4090581d038000010045880d0344481c0006c1090b200311a2405180d1301d58000400c11000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 696466627 1250 696465377 696465379
    0x60312070809210a030206180a06090809091504060f0806060f12160914010b0711060403200109140a0905090703061409070603021603260c04080c03070302 68
    0x20810020011615210081c9a014070103060002e41d400d0742100d10b85a0161040801d0481d042103070150f04043c1e051080e107070043e429941d890050018203180580b10302038030100802095542903070038200702e0100156008040002c01904440c5070283c2003940034a4542c0c03440d407250349040c07000324292306800c1e1410152002240101000d030f4402060110a040e10031900d980121100080d0f45074071001c2040021450306c1001c0119000c2ca4428880c0c1a50001e01c46100e806003031200610030000588140c0c2d21054100c80949160300350703000450740074801d80d007018203000e006070b984c0360901e4511031460441010a80c1c5901400f99180c070544101e404100050360700030581c040820840c40340f40c0106401c9150030085d1201142d0301da6501040300d6040780c02000d05040042001f103c440284182c00041045040540c604a442c0c4158502040e4210000342070000801c51588248515810201048a11603d04005003402c144140943c0c200d4420b8040c03610409098013560b04020800400702c030341c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 696467877 1250 696466627 696466663
    0x31704080414040e030406053006090406060806160f02070f1404060e0901150f0602120a0c02120102030105031e070b070f080a0e09131101050a0203040504020c0709050603 75
    0x41000307420b2030b4081a81811541c002d4944008065542007030000b88010040d60312483d0786c45900c00301c85a85801c01c40d03c0341d0400d403940c110041b5426034240916034003620444240103156510714003980180f00313541003103540d4401c41e0100107611000100c110000c403055103404015070403110b0220303650300c0240200451554944070802000030070303516081840303000800204d01030380c80301901140e03c1c1003210920605c1e91074101040e0100d90121040c0060700f00c031400210310504000d0081e60740c000e00c62016603020400161002081e104416100c4601e81c024071342ca00d040102c01c5258041d400c2802140c2c440d0041250100a88946030024558a1640800750030b1040c60800943c00d01e410104068982c3c484e81d0030a680025403071802480302603426121124100d2207003041c015101c4000302810051491070f01c1c1c41c004078030380300c0d03098000c5d080c00d103080780e0f0700d00c00c080089043d806181d0049070805c0c00800c56400100e400b2500c801603812080f002c000c141d440d8401c0564600c0b00d45600b80c4980 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 696469127 1250 696467877 696467879
    0x603240b10030c11031c060e280b090a0f061202010903020d0201140712030c0507030206061009090e030d0b040b01120209060913090b153610030317040804 68
    0x940290042e000c03103d5070b402c2158001c13038a03620f46420341d40145034a05424030a4460705841881c10f10426020f001c0c04c454002d120b107055114040c803128a42c144d00156100c9a201600c0c00304641c00003c80071201401e03010a9061441001e40581240f03081041c0103824041d011405104dc031601200103501651807200f071074030b03540034460407112108050b41082581c4100f4503010b41e0000043c0350f15441124503805200344440d000b4202c50300c0202c0241040010015100420341c0010740c9a04024111043d003010b4150000680d0496411350102948504042c0c400507001808000740c0401d00f01e880c42407007440707414003c000c115081203c1442c003003942d00d00c8041e1180d4456010307003200b40e4060040d1345008640c400003102480741e4002840c000c0e45501c6000c3c01c01078440c04180c1c200c442001d860b40107050040008040d840c00f1b225026100d101075242c1c45101c20350030040c00303410420b980c0d41089820021a151842e10f031a0005401203011285507080076485000b0541c82590000403ea0410f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 696470377 1250 696469127 696469159
    0xe040905070503070321020601060e060c15100f14100f0221031f0302130c02010f06030c060206011509090b1810050f09100e0c0705010603240b 63
    0x4084a140503101031103540004520380c0c40800520001c0c1d405000303606d601800300c407000c00712002d06e4180982190091401004a55044a8280d8000ea011a0583d8507801c81050203440d003610180f6518a607500c0e041448610f03004035090100782d640001021000549503842c5168400e0f403900348680140c40441c00c0c0078913500c10f488400e03411444c1d2042c0c41650402e40c010009014040000c2022003000105011071b018920951084005807404408052899600060580c3e01d5604a400e0001d40380c44035103503194401c1d44141550840e0900802c400c50712400c10303065000c4a40103041c058401c80001096219071029400c1c5080f01c50780d58000c0070740c14015440c0c041c0c01001c0c0e4654000c80080c0900082820340e200440c4a40780e6064800b0500b0f1610042004500e40562018001e419400a0082d1454080d400d20142e401e00301310300980e03840d81521400f0314815030401904035440d0040100420907401d1022448100542d11003025420f03201d804030441e40c480c00c00a42c401e10034001c00c081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 696471627 1250 696470377 696470381
    0x612030807020708060709170105191a06030112121103030402012a060b03010f0213030b04140601080a0204110a022d0d03090219050102250306060e0702011406010e04 73
    0x70103403462050701d588540e18909146491415600017002c61400c04c418001e1050781c0a0300744201c01440700a0180b8140115084045201c46140c41001511101287d50040c3c1644080d480341d20050406a900d41e99070f101c02070407583c1c21404442413000301e00c02400f090303c139010003c2c590f105500550300d1274845500640c2c242c1042c0c17070205c0703200d2001490f00e021100160aa42c5d1194050b04020904400780c100301402c480c0080110b00b90310703105000c0c40c06142c003004007100999a2003039416049031510f00b410728070155400704400d0703144600c0c400840c050001080f00c1101d14802d84050050b0844400807100c0c500030031000100582c803107050020380510705034428075890702015a01c411003156000c1c90742003030490550703540440e403203036850811402c0c140c040305070b60712015000304a21810000000d4568200c1000c0c0303148011441d4056010948034100f22004640c0060208041a40c40000c8203c2001c101e46010141d440c0081540b5011150b0b1030386481000d0503076460110488550130040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 696472877 1250 696471627 696471631
    0x20a0b0f1018050f0c0301060207031412040f060206010b090f0904020d12020c150307080c0f090a270911061606090809120106080a060b1324080106120308 68
    0x20304007210400c0001da6464401c0c00c0248100c00706004500341c40c0480e110512000c0203441176004030004c100400009901040f0b100170380750b20440031003811100f42401460109410b001d1101207900080010f000d0000101d40700480b9002d400f91110340ea65561403031118001d0b00025900442c501038990707064070700b4080082d407082c030040420607401d140d17444d03650781100c1408003c0007583c40725005892614018803401c4011201541c801d10794a40044014200c12001d840416a440042200090f65006c2c17002c0d200300c44405020030401950380c5074100041f22502e40100c01900001034246010440c50180c100e900782c000088404a910340800d114081e030003c100241c2c0790000302d007400000703440b6024252110780105039585c0c855800c041005030860103161003841d103a00d00b207400c010310000464003411a43d0404400a41400400c1c0491100c00c100700544010358031340b20f400c00c80c010b2003040f041e4070303a800e16090301d503401c2c0c5521a8900302d405a014218000905001c004002446401c400c0c0e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 696474127 1250 696472877 696472891
    0x305010b09010503190e3a140c0a0503040509090c0d02060d0603151407050c0a0f03090b1303050f0106051509240c0c04050c161b03051606020a0b0f 65
    0x3003102545440d50f40888400815660b0b003900400c14500c0400c7e00c10144204044114042540f0000c144100099541e052040e01c01400560340c94400070040c0c580644105014003070079207191514034581192294480c0c000c5500c45c510b0040458410381c00020784002691020302001c480444640070000d283d000070300d00001d00c54452202200107605038032281091a05a2030100341400500c12141200d44002c0020080042c184100c1c8100040000c02c01c410f05d402141c0c2c3c01070240759040c100d039049a40e03000051910300000303820002036035821030101240e001d6029a070303003100c441150f21f00b81e0b030b00ca2041c154054452109503035414130090051800440003040d528004500c1120b0f9020034840046070080035802250381d85401c45c081c482d240510500311003c00540c0b03032580108900c1d005030208030400250350354000d01081518003103941d1900c4489042c440d00d0740c0c1c900d80190742d1440c04e8a07034079141007481000036209000080218072241d00c014000851f0f0340710520500c1c01c81c0c0c014024 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 696475377 1250 696474127 696474151
    0x18060a0b19090905011820040212040506180d09050111010603020301050708100902040f03030e040b09090c13050609070f0207030b0109050a0b01090303020c062a011b0305010b09010503 81
    0x711020030154000710052038140c101044010041c1001d03400c46418101d94401d0b4902c002c240d40015440b2210010400424008a40c5044070000481c00070300840040c01c0e03140401c04103010620030001145403041542400340311082038004c0065445000640302240414031010092082d58068031101d41c04000800000600940da600082d007514415107148000c1103c000a10102001440300c7d140944071004080d80b1702460103a4103480000340d0712010b030400204180e02d4850307035a02d0300b10500081c0e0040501c3c074182005000ca94403803582000f010b101e2049862010151005405807501c01c000051640180e940c03081025240100300c100908114010300c113020000481c513a150b14040c0c07429200000f2249440880b200481e4105603080f41881503ca0081001990016407c000d0040039528540c540070601d442c0c0240d000c1018070542c81804d90703900600e40001c15409900c058050304101640c031100300b01c0c00e030110760081c000d0121081c000c100b0352001354003940017143c202801c0148 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 696476627 1250 696475377 696475399
    0xd1e031d03040e091207081608071a0a0b010305060a12030504091503020114090306010303030216020904080a0314010b12070e190e07021906180b071718060a0b 70
    0x11150442d0301c603411200342d01c09140140541c2100400c0b80ca0000f401d044103884c50f10005469508060080c500700c1051400c11121f584100840001659200d40e4080c2404809804007000244d003c00101c41a02d1050300e058207110301d0758401d000c0d41d40030f60406044a102103003000c5240c40308916590040e000d0040030080001c444402c0d2058500c0105114a420350140c25480010b0108141507141c10300c5510074000802a41d03008a2258110b07031781403d0040c0d6032171070100030141c50180d103030001c0e50000143c400c0000b423001400042603030b021a60340810101e5031662040340ca4480a0281a09007201406181c400910706038469810a03001d050446844085030001070250107008070701d80b8000303140036042041c904010040d50b0094582d001428240b048070380c1d182c158410310000034003415162800013a8615940d8801a0019040b070465006c0e0b203040480980f40103411030881d0860400000090428001300d110325004d001c421025011036284c0c000100003519560b6070702075108100d204 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 696477877 1250 696476627 696476681
    0x507300b0d0804060801060e040509030919080109050304170303130f0204020436020c030738043309050f031b010509010203060d17041206020c0d1e03 66
    0x302600040265554540f100d40c10001c5c010000c034084132115009e1401d110038008224804011303101c0b007050a580f211024800a84881c11280c1c2603031080640d9442c0c40500014408003000410030384027240b00600b6a070742e4000d0010340d00c0c030040382d01c245128030890b4078000099502040d101101c1c00200003506240c0c503141d5402201c1e00039a035061004980000403408100c02c1c070345040203490440c100710709051070548000c2d00e80c03007031440c0100075022045030607100c01e030f20b1030a40a05583e42403803035014840c034007440255002c05450589070361406008840e4021010001d112030002009285020102d100d0784140c0608501a01120107018420007070200d0401080a0b02d04c1c1c00b40c41031408a05982c5030700590864602900d00c08150b401002008850386aa40c505605140c0c007403068114029141d0120f541800f803a045450f107409942141c10500c0081d0700604039140a14054a20a520b5800107442e00708094000d58070034240e8002c0c0021860283e88082c0d40345113127601d6400741182d00f103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 696479127 1250 696477877 696477893
    0x80c191503020307080603071406090402040e0109060f0803070c050405130b0901051816050607080f03040309150f080109150e09160b0307020a120c05100507300b0d 72
    0x41040340000c0c0d01008101c00b00c1d0307214410700e801c06001c1c1c000d040940e091800d00643c051001006900880300040c0111039a20340341d049400074900e0340c03c0ca0107156102d1380e40c14041c040d54440c0f20b80b01c440101c00402c4091001c800c4902c26544150841c54081c9080103200203454020000741c2d1469244c07070f0301c01c0850015603c1d54403410751030000141d51300c4e1005000001305958070802c2e610b6848071201c0c820070321645014000783ca00448040380c442000d440d10441d5403141c4138000c40e8603900030081c03008140d0858080015242c903d00300a9544040003003c072601284039850b800040c010800421492001d540b00403500f1f000315200304121602d414415607690802d503408a840d61104034510b015240c6282160f0280c000301520030310b941080c520096071800b21080241920000d48202e01005001e0084034100e680e2110a03180039000940d20301000300411103159000c5070140e01c07615100c2c84004441001c94580a801e90f00300c0803590310101c002c22042452a8101e40c58009400104d0014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 696480377 1250 696479127 696479159
    0xf141009030b090c0a08010c05030c0309010b0d03080105101719060506270306040201120e010b0d05030730050c011404120e0315010504090c030210051201050a080c19 73
    0x180c001303143e42c00343c910500c40140c2495101c980c2991500c010020140e0f030202c1241d070000c06c8000100e80700d441e404a03050044c501d40c2151a44542c00e40229010036401c03a030268100c86003141d0162175400e0f507401c240d84084204d000380c0b6142d00d4000000310801c44580072050804120140001c1180e202c0d0045044c0e907104552100484d040440500f07455941031808806491095000c0c050b24101580043c04a4850504200c0c1e510f442d0f24043d400ca103000d6000c103070150700080c02d10412140743c0c2461a00d952200c00199105a80504462081c882041e02c00c51820f0341b605e001c204274001000129200e400869026405540b6004900310811201800d9800749002e4500079840c03000c40d0f507010b80340c5e0094084840c007981005565410712481410020b0460b0812340e40821002410318050740704409d1030b00000e601005c2c1c03004141ea01c80d805800340082c140d0301e100f400c041d640ca4608102d0400240c0c858420140e21070346a5041c1400c203141311200c3c2c0e03a580b107609281c46890302c010010320101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 696481627 1250 696480377 696480391
    0x9030c0b070908420415020f03010e04120305160c0c090e070503060a0507050f070201050909151002060405060c13080d0203071712161407050d090f141009030b 70
    0xf44206010009141e050f104c0d000c150110764840391581e048403828901ca40240003801081c48400c09194011b100d40407600303018056070780c19a4030b40e15031071103410000041d1019111060410b07040904c45000c0d100d802c1c05002c0140250b0002100140100c50b000e958050440e01c01c4103503400010101218098404a10002005000020f0422040c10703c0d14000910072010142414140240c41c0d40001c06c40c1c40c0203290a0400d95903003d68001070740c4502c1024034081d041103a1304100001c1c840010401030110071b00f03c80508041c040b1400c103c8e1344807019540a806908681d02241080c2d0701c080c010903084028056110080f542d800d8040d042c01c00e90804900543c000262000812440c800d84c0c0c00203800100d182400d1132200301d0b050110040c0200702358420504a1004070000740101491103090707218020566580b00c4518046840e04e541e00140700c0440d01149003c140256088410700a482c6040c10340c000c46100c0e1410000c0540c01290726100380480a603000c800b00c2c0e080002a03200d985 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 696482877 1250 696481627 696481663
    0x11042007020405090318010e01170a0504020f010207060e0d050a020603010e0103050105070f0e0922050109111f03510f06030203060a1e090c020109030c0b070908 71
    0x801e005000545800a0044125030400c0000500e0b5900300d40c00c140082e102072907c0042440d10320010383d480e21600a80c240414500401c201e2000b0080e0805480345109913203d1440c4a01d80c0d0059a4441c0d450069401180c041900c20096080c94840041014041d10403201101c0c10354001c40c029620a8000000c03c0c0071000062051000074003405410100500d041001c0400005009080c10891032145108500540c0071408110140c880480e071401000c5054242d1201071410301d0080c0701d00c0c3e0045030031580d0700c43c4c409214909007100c0e2580040328007001c8450b0800d5030b070440007062610003070048038160100c54901d0004c3c40080d000380403884210f040c070072107009013b004908030804e015114a01c600704d0512140c102e04030300c1c0e021581541005a103903114100090100c9000350407a85e000743c0581c09141c070201c1c0301c12003a021195501d00c01c2000441080e012030a03240110320107804100fa04064000180400d1242d9601440914028122a4880001605002c280d0813040c40c144 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 696484127 1250 696482877 696482887
    0x81306050f040b010816120507150f09050a05180414030a08060f0f031c031b080402010807110a020105030a150602010b10170a18291e04110420 63
    0x202243c40490f01401c117103001404a40044903000d0544411405000c001c0140801d16008019040200c40e014200810703010206030078850740249984401036030351000030303489030000580303040c480d103208251100600100d0004000e116081c080b00001f4004a840305c4500340703a01d20014092000d40348002040e42d81e8400703800c1a41c100100d10891b102400d12902c1b608a44000990f00094424842980d84400003c0c0b1070340048203400901e89100c1e200001116070780302e441e5140d4410440361055200f43c84501d600c0e00c82c103030101e03000440b059001055522142d044005503005130040c40d84203141a4020070200c078010000720042d0741a03072000c000b5030f4440500c2d000f5803400b403c020a40410030710302904607401170040d490030b00321b011b803d400c10169070740501904e050700400c82e03100c201d800031001140400008018171850141d101c1d441c8010000c4130100307503c50740101c03010701d04079141481d100e01a103440e180c2105200340a01241d522540c0d6200c0f58480c50340c0756524a01102e00b00224036168 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 696485377 1250 696484127 696484133
    0x9040f0209030a1119120c0e0c04181d06061507030210050c040b041d10050f1509040f02120702210702030109060f020d0f1803081306050f04 62
    0x164104000000226005101c0c0c1016074800064401600f900029040d0024810f000464a0710580c840d000d43c28104103900441c00c15800082c80f5001d621401a04007003699034118452004e405a07030b06000c0043c104070400c06402998050301c140f8485101c0065031075405c2d43c0b885024000c1f03011041050304420100621072a02880e0b0291511004280d145804200d990082d00c03000e00d0240c0c004e2450795a00400c2c500d410820507900074092030440940d40742c4c5c0781c0340201d00c030112410040c81c0b43c49490001541c068812070076602110009402d120380f080d144810040f0b030300511240700b0a1000188000e4034550385a0040d1004000c1000005940d0204c5280e48002d14600030110010356104036aa001c010f00c1f0251488001d0f10010001e985682c03503071001034090b1080c2c11028013031a05008030364100c402c46900420560106110030083c2c0289029003030b0a403540700c1a40300f081c20058958002081c060504198056070b10485280c11040743e81e1910200c43c0103031250301500d04050200410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 696486627 1250 696485377 696485381
    0x50a0b040623030106051302032205030d0606021207060c0e130207052b081b070b07180e010b16080304050303041b0f0b180d1b0f0f03030c03090b0409020904 69
    0x41601c05400038400035080501048505000b8107d40350341c10760000000e204d502c41c0c210324100c03442e07114600c01c4080f280750030403640d26005103030034000c600d2602c4000030741c1034000034081109481c4044c3d09410500c10b41c8480c001040380300c6200c000d00148400c410b0440d42d60030040c026501c0c102e0380050b181c2d581810203d04d4080000b40d0189a84061548902107180700f14154038094100d20f0304110555400e50301075070b0441e0455442c5a0548041000d00800140c00d1f15035104070f03a15a22542c03107a2509411200c014580d02c60034003a20603020052010029190040c000406e5070b81400c0c0b8843d40d06d03640c840c0142e100700c03400d98542d0800700900c8204083c4260780f402c40700300700030025a40303403c2030050201c41c2c81600c1130441503070300083c040c0e2410107010b030740d07140a0380c00600c203100296050034016244c8040d001c51581040595001142145180d5080c000b65040c900039101c125056540582d8050907101081c2d040c020041800240030400f04010406408240005600c0300064024441 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 696487877 1250 696486627 696486689
    0x120c1615020c0a030503070b060d140120360306090706022103010b090d0506090105090f0d0e240a03061d01060c0308150402040605030f01150c06050a0b0406 69
    0x8030032600843c1c00c00214030000f007541d52403904000c0c410655124000001c598105050000384051034140000c0001034066000c3c1040701d01c031020a0203031665601c058002c0d4803445440e1441d5115030007500c040700c001e62031b181a20580d5070204401003681440000c2c1340410403201000075500810b8240401503040c010300c03800703110710400c0c2109120040b4103510240014090080042004100800c0f6640c2e00c10a443c4599000401d0f03485a0801803aa640038107003c07592629548a1a8040c001c604800103c800d8180c003550b503004000c1d000082044140303003918503c88960000c1e4100c000c2000c80c500c0c000e205642e00780d03d00103811071603d010307000c001155440026410346050010440c0540101ca1090001e61500e0001c005a5450070b44000700c3c41c1b841400c90304030b44042400b0034074170340220043d4060040d000c0c0058141ea0b882e80309517000c5401100040008503a54801400603805400050704004060b40200b40a000180440c0031075001d540200d0583c00300300501405404501078200e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 696489127 1250 696487877 696487879
    0x3071b0f030b010915050607050102031b09030c010c15022a0312010b03040c0f18110406020705100c0b07080a05070201050f060d020103090f0b1602070305120c1615020c 74
    0x856003031468075480103102d01407142059040e12044001810341500107100040d001c024000f944403541814014000d4008070b50884a0300c040c000401c218001a009541c10281c0040007060342140c20307801103c114110316821605100c950b040d005103405980041d101c404080401c007254402c40c82a881c004480014104029400c1001100100300348001105e0540341003050315079880e241c0d854450700c0c01c0070a0740300703c16441c51a1004a03050740c007044041d4202072170035010b10140e00d100440c0b4510303216502c07405015900620041055042c810642e001c540b425040c1040c88540b1074481e046200703070840728640082c0b003e00070005500d400d03101d0241c00c40404d20080010b49019001441500000742c6400d21401c3d8015665045a100350480000182c1c082d51746070b840c0c415032515a45120050701c0301c1c00f0903c40341c589001c900388001500411641c10a008000841002041d185194802600c900c09400744001d02102074046000000051503200b4015403090801e08009013419080d00100b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 696490377 1250 696489127 696489149
    0xd05010e22050601060e0d020315010801060f050a06030c0c0501151a070b01060e12121b0f030d020706060321020c0418151503060b13092a0803071b 65
    0x301d00071440c00a00d5a054038079500300405030035000c2001848a01340300364021341c10310500c0c0d02c03e03c0c449402c448190403615150001c2c80030580710f15520008403510300413039801c0b810101c010440c003072003a08020442841420000841c041c0f030b4840d10300b9181c0e00801007001c944010810820300329010402c1c0301c110a144070085c10510380303070348503c400700703062081c401081005010b49560fa80c554003c20409003a81013202c103080100c112034139140c2c101d404200c0c4074086175610f04000001c041038501180481101452070600c03003440c00380094010700d0701a60350650781e03040800000d45901c2010b40c4150003e0610032002c4403904001c0c036208200400c0c5016a0401200009241034100199403091780886d4140340320131502c10203401000a50960389400188050000502c1015408100c251038269205619070300c219203103105a85541600401d00c0f03003800300350940e20b1428815a015103400810409446a039910610300c0c582001c02c041d80d0000d81c00b002210815a90640d61740184004440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 696491627 1250 696490377 696490441
    0x51506040e12030105091302210f03131a130e072606090114030d0c0f0209010f17211608030106110c0d02030307150b09040f0302010c090305030904020f0d05010e 71
    0x4658000001d041202d000300f411071856075279010501c0742406800e0800222510b800ca04481c0c007885010b18412070103e180065240000d01004100f12403c1248a00c40229a10324110b000a102d0400a04420411640f551805a0405101d845c40c07015000ca401202c86828604c041210f074880680c0310707070700800c0c00c01c061011503100891424a19541d070b042861408107503040245181c026084000c0d0711030a440004210140002820800d54520320303140302030010306400741541d61102100011880c0d0190360307000f600541c3c03180240320038080d1014003d81980581d8407010f054000fa040440030400071504080615410030640112240c100c0d90b81842012640102e80c4911a0000107404003c101c032000030441d6184d04a0102060050003408040c0b8160806070316180500e28120015403c0803c2941d615209943d5101600d07001ba000e50310b48034150080100030f50001000c000c00303420030b20009071f005803288500c43c000c010380440075180d4581100e400718035004c81a0700120700210b50308 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 696492877 1250 696491627 696491629
    0x501021009120309060f0c0921021e0111070e010501030f06150503060d1203050406061d0624071407050303070309050d080708070507030201020f0a051506040e12030105091302 77
    0x801d004060080c1d00300011385080a00b40340d0003600d603d002103d102802c15440c20281036200854000f103400c8508034602c610801803416540e80e480e240040e510001d9000c0301164001c1e494180845401d050502000c205000c40c4117034200104c9034800102e002c0784000400c031558150081400c05820003e04111050034494002207881e048000101000300210006815486201502c9011608260701c10305112040c1070003400340004079802c64406003401030011794028000000300c0440000058990140d8a0000b030000d20344448010404c4414800c400f1040301c0c80f18070042002d03078005d811201140b07600000f440c0c80c180169120380e0003640f0810032000070030360100e0f148040e510210707501d81e000703039440c20004e07a17a0188c0000501310b6480007800c1c80410200041d50f50803207200303030240e80d00001005800354484444840180482d001442c203201200c0b40180c003142e102000420010381c101451440920b040c0c102d0b0f880481100c0300200510040c03070900c02007507001221940d001e41e600344640c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 696494127 1250 696492877 696492893
    0x4180c0513061a090f030a0503040302040b0d05060708091c02030304021e0108040f0c1a0309012f03091c17060405071b050a060e1605040c2f03040f0501021009 70
    0x200c0d00b1000f001d80031030101096a0b500340301004031080103044a51240305818429202d0f402132208074400d9250860b000f105d410b009a030410b103640c1100c080d017040d40c0c0d601425910401c004000100601504040d1310b0f40e8a9141948900810103070300a40d05d80c9000e1040c8200400c200b5625085c3e1030f6101c141180d05c2e0780c041c40d42036105a00c60140c143c0c041c4c543c58a40c0311449140c110344155100e242510444c5100c0001440c402ca4241c1c0081c00050030fa044403000c00f181c10508001807601040e03c480b000b0b0048402181c2111808040b16a0000300481e11200c030320910034514000350700c8140d200d1424034101c0d100c54010400b12400c102ea400c09071000341101040e96200c6540312003003c0a1001c4c4407040c0701d42c02c0442c0c0c20000502c0041c5124500c0c94030365014a0320324946031480c24000c62241040d115148540e103581d00c5400e03035904d08248806c8446041d0b00b42c4e10003068402003e203164903007400500002d00300e4600b03c0c242d5504080000e41050b4070b100b10070103400d19000d801c0001c55080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 696495377 1250 696494127 696494159
    0xa0f1403030c0c100201020f040e071d06032202060a03090b1b0a140c06070203190305101e080a0303090b1821040f12061112041104180c051306 63
    0x101d80d813010f80c010129040e406401400340b80701d02c2100110f000607050900c1b086003880380000c2d82e1006500241c00d2203421412200200441e0064801d0002902d0034500e04480d03a07400b42d50044400704294640d00046056105000010009488405403404c0010003081303903800201c4040c04c01074010480d144a40320740030f04e070032140070400900c001700d8101c4840400c482c03417a041e02d010f840300b0b850710050295403948140d01808018a03500304040006202e881103600400e40f540f00015503d2900c1141c1c0010000c44120380b003c0785d0007140004401d03504002d840d1003584261070109110805040035485401c0c020400d02e18850000c8500c1880040070070003402c4500b08010000408901081c8802d95018981000c1c1c0c0e110714012000c5094284542d22000c03440c407410060005076003c40349000306000b9980d0102031a80300f400070030f0020701e02c0c2c1074448001c000030300006051201c07543c600a40e007100d50003e4800001c85e88040c070080c10030000c031110039a80380340d00f4004e140c0343c0340c2017401000403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 696496627 1250 696495377 696495379
    0x30308061c061401030209070201110d0f0209030a11090a0903050703030504390f030201021b0312071b050301151a13030c17070608060904030306050a0f1403030c0c 72
    0x11481c010704100e03101d803000d0900303079000103007086160b940d907078030303e800950030b000980c41000d0000000d1600c0384140201c00303091003102079080c144a20025440c014280000b40030800940900005c280b9441c1000200c0140f4081c4004c1e107c000c2030003081c0706401d03401038000d4a10030b00304078003840030030f400104070303081e00e40d051500007600c3e541c0b81042c2074000f410201541e4030700c44902035160800f0302824800c00c19410740c80032400d955602c2140c100301006a00c4028056000211420b05001030420329400303821010781900d00d80c184600f0303800960360051008850001ea110701070494640310004520180030709074005c201c8154030740c3c5070390f030440703480e01c14080b1034a03000a031400568000d4040d01c03c1719001c82c0103050304585914090441c052940078407146001c600c6000c403803583c000503091048071100d4881080c03603102c08051100c0014010b00a509050b10761000154036115006280001e004001c0c036886a1800d007083d0f08211400300b510544a548140090061900301160719154408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 696497877 1250 696496627 696496639
    0xc0b070c0e06120106150e030106050a030209041401060605040602060f01060e0609030a0803040f0b090d1e0e1302040f0b1c09031106070f080c0a02060708060d20040e0703030806 78
    0x703151000034a80f480031003050341c40c550816a00084510b039801a00b200c04800d0f4481f00c4400800c07006044c00c899562040384d500c001e12150400150038140c41c0150010b010300c601718192481140b00b43d003074801030f500a000041002504014556044c0804c03904101e955404000c21f5241203401450061101c40340d5100e40310024021905540030040003451a5200a5907900c910b0503050005182d029118203076101d50311a03000030f400d00404554154a140309481d1300505581c103982a40c03440c0200c6502005000040c000802d260751001030800c848140807401594940c2400b8252030042ca0940c4490703a00401400601c0c80700354078000e60f20003000500d20000e4000c1840c20220384e50110303260b070316240340614824400016800750920243e0b0010317450704e10003034a0348400c2d03e40c94490300000d0001a0000c60204031424130540c49903800500081689200c440b842d02d4210003251030f0700c2902d840e401007180c4140582001e003d210000c10818020740504c0c1d1550b2030141c01c00e0f10090465109603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 696499127 1250 696497877 696497881
    0x201030615080a1a0d080903010606141204060905030d09150e0304031106040b030108010c080601050a080a0c120c090807050f03060f10090c020d0e040615050705010608190c0b070c0e 80
    0x5034506401401020005e0003006606894103203415554080480e0324020350034544081815405104140085141c8445a03845e142000003031000010010f04220341450321154040c0100d00b040029003809404800d000580c2c846601e80507500d07004048110090701e060944450f8214804400e49007140c1c0c100c0b450a81054a84000070f0280c400c1d42c020826141d0007100103c1c032001d055120b2a1450000d44401109480300e0006581030b000b01c10600c80060f1000b40012041c0050350099200e07000d0500b0510081c05403d005002030314404a0312500060b50b00c1c03020081032008101003001001c040d02c400c6803031650603020a443c0c0314000c0201d1000f1450101250104410510203001030280800c10004c1c2d4081c188000d488084c0119480700040c81c9403804075491801d071081c0000c40300014014101d01c20303101000d5405400400042d00c41e035603a00800610b903181448901060440000c0e2000c4000080c5840d0091850941010501190503c0344c0d10028204480b40030981c0c0d00310b408011a0703 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 696500377 1250 696499127 696499151
    0x15020c060a06180f02090901080a030e0319060b01090312050909060a0e070809120d140f06130e0a0819110a0c0612150b0d11030c04140a081501030201030615080a 71
    0x20f80720706e4561940010380407000041070340010803442ca1503442039990f002c0e00300e909020159140d101c541c1a140c980b00818420340040d0b138503807280202341818140300803ea5945e0301d038081004001d5000801141d000150b545151421144095020070100c0d240440d403402c0c01016400c07030200800010500c1b2a0101241007104100000300c2e20880403400265228101a0801e01030911285a803022040b80d2020130f904c078862080103803042001600305060320b0f00c40e000302c0020f445907d035100c04d14007039a2400008565008010048042d544542a6050040c0100100803404200c01c41001350400b0b1003440c006a151606002100d01c80c0c50f1800000d801010407034001d11510445840d81442c01d400010744241e10300103403446140c01e1000f0400d858110b90a0b2404d440100c0e40806801c40802080c0510319448003a0b030440c140241103005440d887c0d85000c0c0ca00200c401050440f4250313040100119a030600504000d8228604407507028415400301400c1d103400585004034040e100c046a142c1c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 696501627 1250 696500377 696500381
    0xb0312030f09190303060f050904020d02060a051c0605181306110d050a0b0306060a120f06020f16060b062502060c070b1e0708070605090a15020c060a06180f 69
    0xc81c40e4603d0340c40000c602500d005401441580715810b50020140c0c00081d00b8600004070900c99500034240001c0f4008a0382009502e50005030048140b05051002209818000d029400d0184444000250305070034a8100104485140c464241c280c00c000b003080500c03004911104105644000041350358840300e24001094064a80408000303132900003000b49280e0300e46c004041321072040e0182c0b80e2607100c10007800505c0021340a41d00f4017040340c90b0f91000050202440c0348046004070710050400b401c005151030954820050000132802034900a018042588075030010500101c680b01e150003c0040711503094a00c030001004140103405944040d5200c400c00c41300c0c09415003082e0340b2059142c2c41604103981000c14000420007000f1144404031854400316404140c010040350b04100315a5201400b501005000110b03074010845c0b01000141e240046400a402d020344c00368442004d8141149015001801000014185281002030b100401c03441c0481c520314020105485081c2020500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 696502877 1250 696501627 696501643
    0x1305130b0a020904050405010f0c0908030a1107080f0604030e010309020d110f13060e0105060c19030c0b0f0106031a06090f040b0312041503050907052718010b0312030f09 75
    0x1340140c241401c010030004107500c0b420071038980041c100450700c42c1708400c80f0056240d001e1541d00350b004101040140d40204c5017110148501800c031440d00317844412482c1044c204006030441070b8131140900081503040310031020103240a00e0100000840d6170000303402c0c0084104041c00200c0b000702c84944c0c2d0340302c07040c1c0e00d11010000f62a0341c0703030401d03c10b2101009002c10320650200141c0c650001c5020714203802101d40030314404004226400409100ca0000710b82c004040f4280543c507100ba100044131150901d1280c02071000c15030566140280c040d080c0c41c114566000c2801041030100515900d26041d500021010750b40d4201e140903040220740181040030115501d4440d42070f03170100c610f4043d001001a1000010784034480c1d108800b06405480003030b218005660071007107041c002410321114a0001d66500d0754048400751580c103008401c1901500c004401c03003d46490020842024014103426210542c0100101c04440c010402d0501002e4207025020244401180c026601000488 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 696504127 1250 696502877 696502879
    0x5070c021c0f08030610020105150111101a0114130e06150408251226031023090c090a0302061206090f04030203030f0a060f060e1305130b0a0209 64
    0x225090550800f4070580d0021102a0720800c05014102103281c0b06000da603000781d070008102d640d00c2482d1001035540103070340c41da500301902c2000e6195800e0700e29801043c2e02ca503011000c20150301c00309000100600060f4150104201003003001c00300c02c080035083c4e041281d00c6e80d40c601c48541c8810002814036622440d200030075100c08900806c1103680030a024140813480703009014000d25904030300e48145040d116018200034800e400c0d001080751941c54004030b10420702c0651a000140103c54480c5d0000d562008440c040d4a40074041ca501d1041207d0b038807440340c40e40740f0002c0340c00800500d6000e001000302c03081d02400300f103a250319150040c6803c040c0da801051591039010381b021803454071004403000751081c601e14021940750b84110400030b01903501603001d98510740d1107200064800b5406810f48031007035540d480000343c81c56190740c0b29018141c503644036003140828a0801541c5038043d001600c0e42482c0505101342c400c00e0700007002ea01d42e441803040c0f040e5510f0a071000c0082c05119045 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 696505377 1250 696504127 696504143
    0xe03100213050a0501030e0d0f02120403030e01080c180f0609060307050a1704020a260601060207030c230d031101020d02040305011a060a1b14030a110105070c021c 72
    0x16a403000c140c4412002a60b505030f9010032000d0303480d00110151800203584421715040f42c051910320b241700c0d40c250f252035100e900485000041d43e6844403240d5200340e02c01c2e0006648a80108015a880380c0c425030068040c40c205070401c03080302d000000c504100c2c06070902c181c4c42030046c000381d910f8072014ac503142800100402c1d181e1420000181c000d0340107032258000160140d0070302d8007916100800380d006580181c03940d10250300300f8020840d0300032641d030241007240c1c018210082c40030b410407086018100980c0546980d91451500102004803034200003150307044141910007408a034130700340d500c00b030007181c4016000c038a50030b0030748503200225440d159550000400c0c21030348071507070018011a0302c14070081089c07481c20040c1d035610010704240d07c0c3d0300c400204030800c14540b0480307504030f0480b0500543c05550b034042c0e075440e0301103070b550080e100716820110315883c0040d0000d4055802c00a400c009018a00d015000100f103021521002440b452500080c402601000c2c0d4045801d15400020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 696506627 1250 696505377 696505387
    0xb030f0a031e2f0f0f0304030b13020a0b0c0f03090319030c0b0c0304030915120f06050621180d050f220905010501050405090a0506060c0307140c1c030e031002 70
    0x102d20074004a510030b00d0402e01c500081249007000009040a0749401c0c0d030b006e1810203045a0b241503100c0c1c4090503003100074014241c1a000740c0e99002c0b0302c2d001000400012a0780f0b240d40c400460905450f407084d110503410a028003043c640340800c0d0a02020f50f988809400000d0707500c2d0982d00209032800140202c180c40003004040c2d9110170045015a000c0d4580045180d9218224105071074480541000242c1039400c1840c2180f994001c041e100860f101d020a205880700702041e02078008e540203450038128280c407030240b15903107440260000d0924044002c04000c00c1c40c019500d00000602d035041040000c1d0100c1401d202d04240e403004900540c5500101440141b259003040700c0e40546030307445d403521000085540c0901c00b00c50841c1c0c8041c007580b41590b544200540140070060005800100420a44e01cbc00c4800780018040c1034450080f82d2100408680c14a00d400c880070011030240c200240c3c4280b0340c105030401d4084982c4e0514203041d91100c1c1d03801290810403a07c844c00c030b0050002c64 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 696507877 1250 696506627 696506687
    0x12120103110d290609010b190e0d0609060f050f19021b03130602070510030213030b010605071e031706030a0c060203210411090c090a090b030f0a031e 66
    0x254181c01048880f400c40060300c81c00e00f00000d01038207104010000404000700504451081d00c0610618032508042c5d0000c6501310100e003003090b956000301d4825544200003070030000307103200e10038404401100401c4185404104561031401c05054034a086402c070b45031024051168046031180024040d600552403001c07069542c0c0c940044505009000007842c000c40d07564800100e101c03ca4800a21507180e6200d28101603000754889415202e521650350004404180c0c601d403024000d00066803020b41d60301c140d003840000030840c3c51510071242400d48074440440c6c0e111301d40e00e42d0084003503600400c03910b4090001e850070102200003031160000140015516401001900380d401e130480c0000f007128181311540d405158100c400414400090244c2c1800b42401908254002c0d2031510940c9440fa0840001c0e1260a69600c50800031707449800303101190500b80045061026080700500741c9480c01e507005851000c501d40b0b401f42105001d000f0074111881040c804007007080c4030301d014800040c154 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 696509127 1250 696507877 696507923
    0x1801020f03090c0321092e0f020c0109091112010303030b120c030a03030507110a0f06061e1a09130f0b0109030f08030a090816030212120103110d 64
    0x40e988030080c0030b214101e00e450305011600ca145101840d03120714649a14400c10031040e000111890303040208000c00e150b8041e10700c0000f05406007102140d20680011f540010070039502400614219004040360b0032559030404c1045040d0380d00040040b5000300d042410b03103c58001c455900e015143c2030700c00003040c1901540007400858080e10800b0000b100c540c206951089291690f03501036010700280c00110b4400d0780281e81216852502c50801c0c0c84e06462140f800702c08240564a044041c2c01c070300104401e42c4100070060900724080b8003045001e14000c088011288a104001c44c0c07104044604aa24602164410b0308000e004260010b9401807032030080c0090144002454600790b040c8400d98090608141101d5120f00b20000c030020703980c1d8811140d0809000d01d1241c075190355140c000281d010300903142c0413004140c180503048036401e000b4a80361401c0e400001c102d03010402510341010b00100301d41501d0300400001da00386510130208014031682d000250980e181c1d21001c1658940748 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 696510377 1250 696509127 696509131
    0x406020f03041a1303090b03070201060e0114011211090d11030a06060306060b03273d02031b0310170607031a010914150d0204170a05070e1801020f03 66
    0x83d1951041c2941c0d0340000d002c41160109010f408121070800821000e40f0700700041d584002d040c40045003a981c0da003100c0c2d91a0b032084c0c12040c2c80700106082038400d540c0c040324104d0300300343d007001c04e000303e00d54100c0400c00c0384510f0480f1405038510300804000e00145003819088144090112444220381d414054010451804100e510501381400016250348907402e6a000e00103034404108404202c8a40c06d142986505130030704907010751141c03000d00c41050141c4480050081c0e607150020308500c0f142a003640b102510782c5151a1051061082c3d030380250a004e42d22420707480707646682c0d8440c2403ea10010704980d209406449503001c81e00b08080020036150700600341c9440034401103091210181c3e1140c10742181c1030018032441c4040242842c1004031414481000d41750641c4560301110b40442507000c10752413411903030002020000d1070103009850f2040071091010700841c034030302d548090301d88007184501c421507030403500443d08103085047c030b070340e65120004021591381607a0140840a5042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 696511627 1250 696510377 696510413
    0x1515040b1312030912050708191104090b0619050418020108070305010b030406020904020d11250503040e0627040c060c0f020907020a060e1c09080705090406020f0304 73
    0xa9103000841102c0b10050814465160720364003200e50800860300c042c411441e20940e050b00c50003034000ba0f14a003c0c014000c3c21a4090382181914815003050138500f074001040e9401140741a014402141109006a404c030320101d440c00401409954154010340c0550001c075445454121242c44600f40c48103441c80d814800c5e00c0e45c1101d9580c454054003140da0901c165041d00b0b0b801c100080c00192280d0061102c02c01c002c00044c00c100d001c101c2e00f42141c0380004661544280020842e020034070a907a4040c0c140d0300ca00c980706451510341d0b2200d84a014070320802807082248800700b0380c65650b40000c1180aa0009500020300614030f94000c1c1e180400c0d01e06407042c032010a0b0200e8040e00c00c224040c001500500d803070485803026801d10150000060428003180140c40000c0f00165090140040880090000301006040a8442010307140092000c07024400800010000b007200440c401d030480f98100c230440402d0341c550400d000603208584580b8112a000800c02040102682001880d800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 696512877 1250 696511627 696511657
    0x90406150201230412050d051005150c030f07030201060305030d140703020406051902071205061005030105060108160e270106090b0d05040c0902070c09231515040b 72
    0x41000030f03034110040030700d5140000002d0000028042252114902d8501e189894541c3c54810901d07150800c50f1000e032494217994400702000c10407840c0060101000c4290214030034984188021042d81e00e104203840f40803441030101e04542854001c1d84650001c50b0040252507440b2011140c8800510031003010400d43c00c11400807a45041c0f2034420b0b103041c0d4040362103091030810341c51540403141d5407281c5d039801144502480450904201c2491030b0f152441107009112500f420300800071004142d4120703e0182e03241c8010072240d070780e1114160703402240c084076507682036004810440d520600b01321042d0300300801710001625400303644894035203242002075503101c0e640c80d02406c4070100d0041c810004404402e1202003a40001680302c0d1b80c12520809220000c4d50f603076548182a078000350030689901d40c9042c001c00c01c1003054080c1a9444005804822403003e0000342421003510140001141302501c40007248191103280301c0050821201c1c4903039840390740d00d06440e0400e521689040c10740d20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 696514127 1250 696512877 696512891
    0x40609110c07090b0f01030510090e101107020a150903081908100b1e0913051e16050c16030b0601020f150f09160801060617070c030f05090406150201 66
    0x48518800d01c80c00031001001741c04050680740c011006000040d0030100342090f0041e00040220b1144600c444610f030b00c1020f80301c11a020100e02081391500304807000c8007641001908016034524690070f060302e06e0680680040c04100000712100310040d00020074514001403640d020406400580c00b5011080e1f542d6020f9035200110b00c07141c072910b80b0540740d00040c2440318842240280c1c40421410101c1c0d066241480110400104120f00c000524422680e640043c01503000020b038102e10400e030300c6000d45c400f5050003141c2c20744140d41100d2000801502090703c581500091000e140c14801e03420b83c00240544034100603810060584031903000d44540341034028014004642c0c40c0c285007282e00e11440e00d0355103034045052584018038001c03080c00dc0202d003400c0303011215424009081681c00000d0a6401d002d4081c201194900c2c1342038540c5500410040d266500c8000c062186a0624200ca02c8103a03403001501c20340038658816134041d050641c0460b881d40310040403901450b1030f60007032040e1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 696515377 1250 696514127 696514139
    0x151903090b0c07050d03181a18071a030a020d09060c0f110c0f030304080f07080c06040503030913060902072d0308070503060102031c15081603060506040609110c07 72
    0x82c4245030000b4181c1c0c01800c05e08010f180260b00600d10034a0040d4088411461981c901c4140c070309500401d0f8140e4011001d001e02d8840302ea41481204c001e40740181400b03801e1180000018a02c1c07000030302c0c40c030000000160121580e4050725075075031020505020600e03140c504140a0a030040c0b00d000040c80008194581c10b00c100c5403440cac13081d03e440191266091080901c807003440c104c0d070400d4051001300000540c2410403c141d511a40c65500905051402e2088807414940c5240c031080c840c020078001809141e9000c41101c070b10780011500340c0811080c0b8180100504001c2d03000c40003051011410405210801e440c03051034032007560900400c940d00c29800c1403c00e407404030260014000310009480075000718025038100c0e00500445e070070302039a450034406600000400104071038440c4d48220f604900d08911802400300c1c880501000e5580c1441d00c2d40c0300c3c406120152100d030b224404208a80c8440d4014005080143c1c014080c400125105030079650045044441500c5001400140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 696516627 1250 696515377 696515401
    0x603050c011e09030f1118010f14211f0b1302040308191215050f0a0b030c0906042301080c070507030f060e150a0c020f0c151903090b 59
    0x700b00380545075032559030b0854980200c1e600c03ca26086800030302074284107035542c0c1e408001c3c00c1040d0484120000560600f01d101204800700d030702c40781611440f0342c1c2144180d03031600e20100890038200750b62001c074000c1c80c0c8820715206410010100c10403100070002003c001c2500300300701c1182e0584903007003690444c100c43c004a1103280310250079a0424030008010480100d9403000320341040c5403240c54020400d00704002c03100c0c00c034282c14a96a010104000d5800e107440031038a0f035041110305030346251400c51803812600c4001e1003440f184600103100d24456032210182e40181500c805016689810740400f070256003981a24580030400513000541c02e40101d0082351075075980710740a80400d81c556903d02400c445e8100044880984401c000c1011680c100084032108524031003000c00f50900204990880e980b0306000b00442d040401207003001900001c4400000384141c8441c3c41d0032004030841c021600840e41101203e09142080101c4075615412100520f40105081d0409803209016042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 696517877 1250 696516627 696516677
    0x1c0c0f1a0a050a0c06051f06050a0c060c020a0c080c0405010b0a0903080d09020d0b0a0f180b07090b0c031305060307121e0606081008120319020d0603050c01 69
    0x10039640e0030001540d010380b046024000504440c145a04146035a40d50b041c20790708212903500404511000140340c01000401c01e5000340381c1405c10500c4e10120540c01445e419188102904084d100c03203c0d03d8409200308038a09102d41c001040c0750340750b41c503540789e0303620344021240e0548500c0c181000841c00c143c50030300710b40b80c82d4030940b242038203589035031754904542d0002140080c02c0307661800013001680b640d00071503900d00d1242003542c5152520300c0c0c1c41c40c01c8510384025046040c2c41c2410403100104040240c2e01d04580240c1c04030116690410100c0d102d0b06950000101c0030780100c0c0313a542e0300c1f000202a0060b82c042e440c19080030342d103d07003d01140b030004807102c03c001001c112a40601212036070041001002c0040c00004031a0480c0c40902500c5807036201d0000900020108450440310401480103044032601800c0503481217030407500c140c00041d1558141c2100c2140182c2445601e81c11644503501c1d4160600841d070f030b6401c0164840c44583c3e5034a02040d00c059038031101c0c0b040e04980030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 696519127 1250 696517877 696517919
    0x91503061905011e1b06050702010c0815060c01181a011e05190506040f05010305130f0206030c0c1c080f060603130f0c0e0612010c020d0503061c0c0f 66
    0x40184908040b286041c148060a0501030201000c455080d002c9204041107451b4010000843c8500300154001d0843e250480031004101c40b140502c003442c885460061940c1d682207402c0b50300c8404020005004200d4a04003010b1000e9001e1360300d0401c070010032402010010880c1ca103c03540c1c0e0702c6035007043c0316141e00540c4442903a0b03c0400d0000340b41081135200d0030564810700350365041e00c4801148080d0b000d03030000400811500410402e40d0703072601a840d40002883d045d01c944410581c1d41c002c0c2c409800b00000e01c5031001000060281054000360f443c0c0900d184102c400c4040007000080c0d007001400c00e010001408840001e86000310a6226401010094062032031a03454a210302c00da01110601224188204841c0d1004244d4140714040942a14443c2c20782504100041168101d41550135444990422080f05802500420211225501802c156580b56907241c0001c0400d180b038170048001c50000f41d2024180016410504141c2c1c0f5032014003030b1000d4907001c13041c02000b003c0e8151 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 696520377 1250 696519127 696519137
    0xe090601090c0f0f020c030604060f0b0a0509040204090f0602030703061404090506060112200a030c021c0c08091c03030b0301061a07031808010c020129040903020309150306190501 79
    0xd82c903c03882035903203c0000c24a441612681c10748000002d01300701c0240e500392007a58448403116202c880034400c1e41d0170010200c588c1c03c1c410340f801002c40c1440d000288080d00c2075945004100c02d00c86460003862000303034043c60441d0740b4504450041c3c000c0c5030900500c0940050322401d99a98103251042c10505038000c0010400c5503105401100c00140342c041c61541152a4640c581640d040c0c03220410407141c0c2c1c0329044e611207000d4000141150a50700d40f80d800c66106065080a501109600f0710300b000340307840d0031085052241061801c5124074000d0b245c01074031a030107008503400100305034502e2511036134044c410ba1700300308105826034106000300c0c1080303e810300b448185006010700070a5440d10906108103a24065076108801921a51200d031261f5190f4100c400c00580c2840740c14101091400072000c0d2803a080c0400e150780e2803035102c05010b60baa0313440150615008100b82c50a19800421742031616a101d000d03200c564109580c45405100942c1c20424154003016102d0142d42c81a568 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 696521627 1250 696520377 696520397
    0x1c0809120f0d1e06090501080f06070f111c030f05010506040503100203061305010b0c010e1504080903010605030106060512060409030c0f03090803070602031e04151a0405010e090601090c 82
    0x2c01000340b2400700690f4802d014189141e10034102405800010085403500144035850720940c14101454810b00280716004803007045440e9412440640c40c03041d0502d480c155000720000c0240c0782410301c01e010000820740346510050306a0613040b410001c08041014009666641c06020990295020740e66140d0000c0201220011031503010f1980080020300703142c000c5020007240811580280c20411b0401000a460340b1840f00900560001240d0b10004041c04000c56022a101a40c040c10040215400103411041b81c0c0e0b017504090040e150081c003c00c0410380d01d1101420355802503480f031003901d850030002200c51a140c414050b03807540640b582440800c040c3c0d81c110594444040880c02e100d24040301080569007000501f550764420040141c0d6824203030000d2040e010a5a1140c03000b00d003102c104000188603600448a0800f140c1000c9007401e201400301d00490740041c2801e03000b51a040001900400c203003292401458004103990702070741c942d903a8a040e5050884020081012512 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 696522877 1250 696521627 696521647
    0x3460e0d020a050a060804050f0f07180e010c030615020307021503060d0c0b0a080f040c0603020d0e011104060e0316140f12010504031416080306031c0809120f 70
    0x641050039407000b03000e81d803255100e100003441088950401c0f000281c850b410041004010040b66030309052100c000c080d180e40c081c0b05ca540d0b5603c3c40c01042d54003001c022003000d40310700b5600a82c521a0041c0001c0c00201282e42d001001407a080c45500c07001200c82c0c0c0503541e014004400c0751300098001d0000746a11401600a0000c0d074001303000307d904110002213010100e02200500c0e001740c602d50060655a2003c040d0003401040040c01c2c00c900e6400941c10300000411140052089070310710b00300541c0700c9803425030340002042104120010346d42010403800300c0840140c002d00c2528003988581c00101202414503070f50b160042c0c1d0500e02c003003445100340140c0024202c0818468001040c200448c040d10010a0315081d900c01075609aa440385c05010405401c60018000c5812222640d4100041011100f4140b0400341c4041c044040c00804691580c60034003104e03054990707502c1c81c42e040800c00d40c0002c080c0c0800f02c50311466400bc0d159040b4034a40c202085410a0b080340e1855410042800 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 696524127 1250 696522877 696522889
    0xb090f09070e100311220b03090604110411030a0f0204080712060e1539120705090f0d14032b050105101d0901082d0303160203460e 58
    0x702d00001c09008a0706c0009800c0384020065210307008d0580030380a18141442c0c9101c40040381f8030220b100e5400c0000460511803428180da500605480004c10140508440340c0001e11035a0070510301405040e00c00305128450540188405120380300422000c0d9280702519220f0510740c5508580856610101d118111b0070700351520840f8258416620326103076420500340c80420241c8100d034030320000c01c6000c00d90070300300013451b400354441c106540342c00d02c248006042e040b108203141c0e12a4516146050604c00b541d404044098110340c02c80f6501c0b9202140324410181000c3d6404200710080310015103c0b240e17028180c101d40001d0704185c04280717204000d5400300e41c0036040e00e920802c01014036031365a5032048810300810343c01000c1c0c01c50054659055030680001807054442003500b40700101c845200204590740400c0a00380020710040d42035040341903100b0324003148414070611003101d1000a032990b925149480840002c0c040300600c0d070a405d0440d10761101000406d203615003811540c100b00e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 696525377 1250 696524127 696524167
    0x30307050c27070f020f0c0a1710050f0603060901060608010513140a0b0414060d0b071b06050a050906070f05090418080a0f180b090f09070e100311 65
    0x50340c40686290007003501d14402ca4030031a1100c0002c0c1d121007410380d41d15014070070100c40c40445c01c058404444503030b01182211040d44110141030700e451341d14000031003091000d00302c210300c600750600c0542004408241210004e0702c02c83d10a00840005c103d1802051049204680c1d180c3ca408034240c0c039143c00c00c04104041511031250319107442c00203880c0320500c00c0c3e60f480f402071908002004c0809100b40303c00c4403407800b21210451011014404180d03504044189007070380c4001050030644c0c58030310480710100c480300383c2c3d040030b50154115010040642c0049101d4035221804211b2595aa50036a94070313601980c0c41e902203200305202c40d14040c4548024401c1ea800a031021501401d80d680903031141420400a4444c104042101101c9590104001e00d2a40c6280780c911101d00302c00d4500c810f0b01c111840f54924084000450500b1900c481001180e000300060000700c00346044030020300302c4412a84044d102d442403036140304040d4042e208401a1074610648a0b061000c02e0007105400117034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 696526627 1250 696525377 696525409
    0x40f060302030c1917181e01110a0507050c15070f020f03030c061b040f0b03070309060e0c090109050c0a08090304090207050d0e011407080318010c030c0e030307050c 73
    0x1c01151240c10000200b1030703007600880c0d44060b00342248020214103c180036140724442104400e000c10b80d241d00040c800b0800c03044079952000100f100501900400312166a12711150010405071415604103020304100c90181064030b01500c0031204000c010700105600e05451402803013404042242600c16120b01803010b0100100320f20740e140000c1c50368101240034502a80700c4010448280041ca441104213900c079200e15003082e00700300f1040031000ca18010109503200c0440020a8648242c020008250f00070200300007010407403910340d84a440d0f0403040b40c094001d00d00001030b01c150038418a07208030b803602c40301800c042c440c010803218504c020b40806240e20041c880030402c0c2e2204d00c000c065642c0300d08003e102d1004140d40c0589044400d01e88681440b040e03a094816801040d402c43d848160300c81e9003240d403980d030301c03200c0070503102945200c0360258130340805020090742541c040c1040810580b9030303001d002c1e00f01c400c0503500e00c11002e0040c140c0d0440343c0355825074180210803001da045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 696527877 1250 696526627 696526651
    0x3011202131806150e130503090925080c0d0911030f060609090307021e1212130f031104050601020312071d010804051209010c1712060303040f06030203 67
    0x50150701810550b4400c551241c00e01041108040402c83c1c14400d0a8079081d190400da1a040e1030408100c29190340107280d01042600070300258104501841103480a40c0d004001c83c0a41c10040340500b011100100002c07586500c10301070780356081c041e1000503c40c9200419862428441c400c51a0260601140031500f2410500416190740d0f0140b00798101c0219000003070046141c44020402e4024018080504581041140b0400350311010326100d40d070b011950b003001d140b045000115420754055a0209080c0c0607488000c2d040b462001c2c003c10000110702c0e0b41807030141e00c0d0052142c03064500c0c800182a008210f64550090400d900f00301e0303001405005403810311410790f10180d442c000403204000001c07440321004d01318003e000c0070790b050a1820718041d5401d2070a42d841540c0d03042c000000d0041043c0125808000380c0c45890402034055002003218a0500d19800101e03c903000b94205680034036150000410703d050001c00d450844034030304200074102e803030300c40180c1c000e51000d05802d40c622 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 696529127 1250 696527877 696527899
    0x809070b0906090d060902030105130b040204090c0b0304061b0e03150c250b01150f0c05070b070b2202090106052a0f0607050a0906121d0615030606010503011202 71
    0x1544d01c1560516850140602251421151040500f1240024000e17402c1e1103842d041f403400719070765002c000e40c0150b054034000b40319011401d114010400c1944044502d01d4000100410810380d90031034403540c030707580034803084403e003403c004d6803054183d001da1505640f00d083e00e01d4003002d0051004da004070108060a140203c812105819620045450303000003078041500310030002d00c1d1003510700400200058007041c03500500300414030004203200c0d03001c000c990711055040c4081840404010310b524175a51381d0b9103101e0300e803210312100102c0c1d41aa459030f1605548240364812a52030748400c3d401003403a00c40741e0a0480c251250b400c8254500104051000c60780d00242c048400d212900080c80000c0c44001180c20313000d460400002e08040c2041024055901310030b0304a00103009803060350130030282884007030b02d4900041480d031a0311207807000d0554080002d0980806c04901404515401910150b0ba02061681e200b40950309180018002c000400c00140400e0110080a00c01007000501c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 696530377 1250 696529127 696529129
    0x50105030a08030a141f1a0d2d0b0103110f27030102070807021315060f170403090305190b010b030406090501060b040f1220190e01150809070b090609 66
    0x4a5006c03036007550b103085a0480300e0081c0e80039107100310080285e103100300c01000600480380200e02420048040182c1c039510302c18642c0b0182e80d2102403901804000e5003030b49020101c410090100a2011400300f4540200c0349194001d500440d070021070070701030b064074001c5210328410aa0360349106c44854880444101801a82c007030004152803030040f00c0003a00c943d1107004022240c10203020228503145005404082050085002d10880f0b20341c0c20000c20501c840242601c034141e450700708440f0054244200300405800c002c090341600d015904884901c60a09500d40e01c982110701c000d00f0181e0080010010440d401f0b004603402846502d000c0b4201080b036681d1030a42d06590090314940c440810b06000c49004202c1d00f00c000c0a400c0342c140c0a10000344c60b00600111558640801c1010b03c06245074180c44018940072280f80d83c0400440c900d40d1082c503d03000640a0190b1141071080203a941e071791b40d20030072009016111880141052a00d403080c1c0c42540d0340200309103900703d001482040c042d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 696531627 1250 696530377 696530411
    0x91d0c030403230319060801020a090317091804030e12151008011a030607020c09130c120609060c0302180d05010f02040e15100507110402070b040609050d03050105030a08030a 77
    0x25158542054000c1c404800017141540e1442c3c004118580c81404611402c3c0e07449101c0500b1030750030040071050b580754028281c0c0c0900c40d800c4030980010500d01da240b0400344030b0082601c5140203940c0c4003828404042000750010304146054601c1e4054a071304285144061102a0080b200c144103103049aa103183c8a800d45810a803c0000c65003000c03001c1d989410240400c42d17002003584051b00da0f200030100007540ca10b001070450039505500390b6480c4100404012000041c1c500449103981400031498030a02521080400720350540c1011402c0c0e44c254028000e40d410040e5203255500301240d00740c02c0c0710303556843c40d20a541e03a40d210076070881204e80c03500c01800609400e4031b1034403032850441c00c029500801138019501070950b00c0c050000180c0e20009503000b00b54002c85076840e2001131300010f0701a0140c0c85020b4003900c0d1f90024802001842c2c2c0c8602d2410b0b210310140c07000500c00e000d080e0203c40c000d2040a401d90450940e00001030700810045a12550800e800619504400b5150f18 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 696532877 1250 696531627 696531631
    0x30e0a1d010915050d150608060c0d2403210e06070209191a120312010e090a060f0b011205010321030f050103050a02090c09031018060903091d0c0304032303 69
    0x19141d20b0311306c010070481c000b0340100300203029510002c0806062180c82451540b14105140b110169201c1c030a500030903a2828000d08529010522440c07140c5900340107843c60b440c251803071541701d401c41d031150296008004858000b0300042009080102c60b40a21095000040000b000c07901b0208801300e05200901c96225000748540a03004004403020902400f10700708203040c207050703205101008103641d00303904c81415100900004a081c0d11000c1d8103902c0e0030803d08000309510300300007081402020640c00140391040903611501c4904801d14650202c5800b8003014102d002e4116660311420014921103558550710b00c2c0000b50502031346158800c8179000e03003040340c03103801442c3c00c1401e40c6803082c10310b500b001c41a80b17441c1c0b8280d10400002da0300c03c0c000003419041610b0300c802c910303011401c002c1000d400d0b0b040f842c1485000c41900c0c009201034154010721121020901411001c03414001e4520720520724003105900d107803142c1e10305584c00455801c0882185001c125a0590010300700050740c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 696534127 1250 696532877 696532883
    0x10f03021e1302210603030702010f0903140c041d060103063204170a090e1008010c090f08030703022a2107060e01080a27030e0a1d010915050d 63
    0x513152504d0307500a10600c0340342c41508501200c20f00c1409407650780802201d0626174242000c4290b0241d03407005540744130256101800c20170011040c2038600102080c40c0c54407000866040040190242d03c0032000e100c1c801c00040142d10000c01400005d2003a40200c0002903021158810244c1c0c640e1091000100041d0200c1d119200409100410100c410b43e0125072115034445030502c03402d614020101580c610500920920400214074682845200c990141a044009000000c0540070180c40301c3c0043c410203420b4584400d000520000c0403080d1241690302d41c0c09004400e2070b041480c4120010507444c0344900200601074911030f5146868190001410500e6412404100000038108101e640c800014050b000301c207207210f40ea0228000e603102c603241600281c80040300d49c40001481400e9030800030200040a0740c401d0540082c411500c8540031904001000d444810031030000840e50030070740c0701c1000b02c40107100d107820542000c51300035000c056450300555650001402e00d41000026 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 696535377 1250 696534127 696534131
    0x3080417160c1a071a15130905070609060e300d120c09050d030306031704081b010f0f050f0403060b120c0609010e150d0203010e0906010f03021e13 65
    0x42050b42c50300c1c600c0120100d0f0762540d031401d01d00c0340e4031001c54140178000c07120f032400044000500b401d882d407010f0031034070361001e05145044034010080200a03d0b007400103072110704c84c0c4200011082d02c2421400b0903207a01c3d90b20b45041c00c00c90824400d030742982200021001040d402d01400c48004400c03e080500a00002050a441c0d00310000d0070a6852698549140341405100c0b5403142d00301240d04210360003510405014001410300320010400b03900010a924800320500107440e00e500060403c0e12807600607914000c0c10203820010000200a9031307808500b0701846035080b6400742000c1020140d803410030900d4000c0d03903103001c0c3c403c8d401900308944681d03030f905400c0c1050511580d902c4030103021000804000c5403110000c0e241d801640c00070707410007804120f44262a01d80c0d40d40c030b15148201c090465141c0c1d08505d203070806500240540c2140040c62000500c501c0400107101b4101c580c50052500b21134110317001c0c8005814082a03c04407009402c100c40c0f4070351111072480d00c40740d03008800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 696536627 1250 696535377 696535379
    0x30a05010e0a1104030206030c22090b01110c190e07050703110a020108010509220506160c080409150806040c060810030b0115020a1205030a140403080417160c 70
    0x242160441d020342400440c900d88100c08240c0d1030b20700200c400303803078048607066180c3e0b840c25440d510610819506540441051182802070503d203003000080d191701c0c8009002c2c9072502001160030042a541900c000d50201a0100d49070800119403a415500302484880c007036181c1c00c01c800b002d81e00340d42940c0004d400080030014564071813483c1c0c002c2c09000e00a0034038011a50002420180103001d0b5a01c208080f0010811080d05485040312051054844c031446040c1c074180300d0b4032044201c810fa5001110003100940d458881c00d214107159500c16130440c00e180c180524000102000002d00e508044030480c0422104400c10503c4d120b01d12480c50a04c074207050010003046030304060b000e105400b0b000c98090000801490a03241550301a24206aa02c0a140400c0b031820310724190280140100c0d50440c100c140e40400107500c100c0030350100b40040c1d0000a20340760041b02c00c4070f0140c0020110000304000810040c201025082c04d415024100b6203c1b907240103401c100114100d442c8042040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 696537877 1250 696536627 696536639
    0x170a0809070504050c031501200a06050121110609121c02160303140405060a090807270209010903080d090506010812040308072a05090f04051b01110102030a0501 71
    0x1c00100980820780c0c0500a609010305a170420b0700024240751a084400050b103022a4030558512005403a8100c4840130418903004241d100c10100c0030a9417014248800407603c0c007004048a88070158090080400110307d031030344260410350309901a485401004800407075620500c0e47e41010801d40080c103950040d20302c6003103190f05043c03900001e542200140b00c50507003056070f40e10304481d01070824200c4c01114031700303081c294460b50b00125800310022610250b41c1394044444001d0301c07406803c5990450303d4040801800c40c107003040a200d0000001100340070142d54014007000601030415142568899881c1a040c0d041502004103050799070300b1190511404001e5140140078100161540043d0030005070124491408041c00048002590004004183c50110b1880580070174940300481805c900d910550028450a8880d0703180801059500d4082d80481e0302481c0d203c03008011010001c59226501070f40c07404103606000c00d5182c24158080d080c002540300d500c400f03100207141c1d0b040c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 696539127 1250 696537877 696537883
    0x17010f05070e0d06090b0a0e0f06010308070327080102090f04060305031912020a090303030b0f0f040f0b27010821130909060b0f15040b07170a0809 65
    0x112110150600c0d05004200750000000c41c82031038203590580d481601030a010019002803031004244040d51010401482c0c150740c4403030b82d003a910101f5611011030b00c03a03000b40c0d2182c003800040e00c03142d8108040d1000074019811840130aa540001c08090002c008503184600480c0c4d0201c040c41c1d40004426a607498012049080c107841202c0802c03549040d034035516601e008518451610703615801c111400316004e0915404c80301501c1400b5942c850741c1010040c007814552008501103403d00b041c150031031500b40004000e000e4068003a0f001c0303014074400c05c0007038801c44000824443d0395001841550308c4c1c002041d10010141d1040803003580100c15041d04003441680403d02981040151411030303213400e054030100c4540c01c81c0d00c81c5c030388118003001a40d0140d0ba91040c0c560030305c0d18080b803080240341e8111102d1100105c03010410300003440e0500c0008943c489005080013420001400317041d203028040d10f2002d0048400407041452035014408640c000b102d5200810420070411130940010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 696540377 1250 696539127 696539141
    0x105040b06011b0b0609042123091e130f09020906011412040c0f0801090501150f2114060a051b0d05130c06030204060224040305070c030c1701 63
    0x2103049114602c44e4990320304001014141510902c8020301080c02d0000300204100703d003003244a5410802c4910710080c0410000d5002140d10395000c944c0051580c4511050301c1c542c40d000b070180402e850701c00d07121200340b6003040146948803004407400340c5010480c0c0314000c2090b105110025800000380104910140e00406490402c4030810044a03107003941c105488540b13510450000c040d4946141c40d1490403141d4000c4125128900c82c00590940150400b44440c2d0107034000304440001041054403003c0580150f0007030060220007000750f49040d1041c0c0c409404403000c44401c00d03104e075641001a03d40e1100488841d400b8009102900c0c0d080d00c10305401201040485481100c102058a124018252916121692100055240316007044800b01e283c2c0e0101000c2d80c41912600050020341081c003134440180304d140740c000300f46502d220041034141c0046900200e281e13915541268998012007040b90b00100620700000021000103c080c054103800712084406260fa9072114211040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 696541627 1250 696540377 696540407
    0x3090a1502030702030403081602060d050a0b0103140613020c01020a0302040e0915040b15040c050406030b0f3d02070e1311100c05191a0106020304050108180105040b0601 75
    0x20410503c94160303000000c0318101d81e402100a61201800306c00300e08030742d48500e00a50080070000e410994082581d0000d481100a100c3c100103054501c0c0045040340c00c4c8588038003030b10440c41d000c40c1052410703002091160b000c000015140030800415603099070081c400c2c0c0e801207138000c1070034050107010384640ca9000b8507500c02410086205180d900720403034054800351820040001007054500b0490200300390a070094400d100200d03030070704010455407291151b1000a4600301d07000c0c00c546818075854595190007007845220701d159a110a186024106807040480400008a810b01c524001c450808410640140045524220880b12490402040f800051042254450000d01042c101400c0c00c101980c041800c00802c40b82074485010706000a04075100c1c2c54441221144864800309607a4480c4400b00f1580c070744403c1c0010071300f00a00030400503800600007440345504c240b100c81c0c2e001504c1526100031456580700a4210360701610117542d1b000c9102d04111840d604041440210b5103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 696542877 1250 696541627 696541631
    0xf030215090d05132705010f03150506030712061b0e062b060e180a021804020f0d060506121b0105130305120d052208070609060203090a15 61
    0x40c0401990351140a050400428020041000e10640200104c101d02606240e4008411544041180c0c01c0800d03680c1000544241082c002091240401281a08982d80024040d84e000a000d48100140c0f000400458140c8203d02002404a00c07440503880400d004020005a90740c500200c90030700440303105c2c4403040c45560140d034611505c581c0100d94407582c038070100c4400c4565004044054444401407000850b041c8840840c0310501c04140078096100028406031681644158680320b0103001d9010394030036103035600d401d41001440700099000c0d1004003070845030b58000c00011020b020740f600984046a03510100209814050251700281400c41c0c001c0204419072651100c140e0074207101c043c1000404218400c0003203403108440041d5030301c078090301e800f40b40464a00149401810b070040d50b6a00306008140f5055001c00a40c425044140003a10308a0180e10784e020704e58041a0126656582c900744800861040c1c80918082d0300e045014105614550078202a0190f4030383c401800c3c44c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 696544127 1250 696542877 696542881
    0x140c030703060f030c06050c070e0108010c02060105030d20010209040f0c020c031c030f1b0c1a0405030406031109091512030f03010504090213050a0f05180a02012106030f030215 78
    0x344040c00e101084403400c1c40c00c950b0310f0070311b00c2300380742444050b603c801541e604040c0081003c030819008003441c25140d60886209a0381c43d410190340384107120140010400b40920703002c14050418920001d540903a00251500d00044081001c80d81200807100640e0342d500b520002d0f0743c2d030610031101d42d110204d00070035a6404402c00c43e04000d151440f40424940d660031074405500315900f2800061221282c4001c00c0c08000c0005010040104000c54801d0403c0c003c05022060101e6076502854125008605180c00c100701900200b81186107900d94400600c2082c2c002d0343c50b0891035100b034085038070003150b46071600280455a400c0e0345500045070400d014071245021110306a0381140c8045070085500701d44e50010990603a01d42d6001000c05041401b080b603881c0307044e0000d140103401d02008000c990f9030001c03426036001c840340700300400e50804076041c400340d0303c5600362607001043c0200c0c001a030b140d10345290080b502164003c83d0141d5420003003100b450f4040c48440309903000c08400c00c0440c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 696545377 1250 696544127 696544133
    0x30c14030f06061c0c0b0406110303103f11060a23190e0a121a1909050c130c14070501090803011202031c020c0112140c030703060f03 59
    0x1c0c5070010320340c50054808144c410700b244040000b4201e11900300000e82c882a86506102441e81d10601840010455401102990020000459200311018541d002c180c030b04003d80c140c5c0c40301118149104069089182c510b4105003014101c1c175480802194609040c018a0407089800c1559800d5216200c00c2c020744540c00d0304010707213803c108043d2003500c4801c0701e00c1a008000303000c0d4441003a541c1c3c801000d070781051600981846810b0400711070010203140d82c1c0c407401e410b81c0c0001c3d1008018445a541d010302449500002c59042040940208203081c0b18003940d01c100c80701001c050b502d55001288411a034104881e4060391480240f00c00c0c00008040c40001d041c502d00201c41d5018508005410f000748031003940700705c526541c0001c4070356482d6950850120b10300c1d5148401d0b84a0301844c060b1254480350313541000036005aa0300507040421800006440c203140048810308460703150a584040c4618500f403051040418083c00d40d01d074140700728010120340c00d50f0820018800d2800040c004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 696546627 1250 696545377 696545383
    0x30105070f0c080c330f040c0603050711030a021b0609090c0a0c0c030b090d09060801060509010e181b0a02060a0b06130f081011040909031107030c14030f 68
    0x6615041256203a4802549180f40d160452900640c06842c2408848410801ca01c02c007617a036410000381281c019440720010050380c1103069034002c000702454441000b03403d01a41100d5030248480c20810040c0c060030380d40034210391140b00b070940180c214031403800b0190010840e10f90004d0003030b070f6054203204e01400400c9400741e002c0c00c2001c00113804241001043d1054041d00d124030b81c0040707510602952458038550890054030100750900441c2c0e52203001d82c1c8105074200485009540e241e5241e440d0800c1501d4036441824410b041140e003401854298071094295290701a603600d49418514040c1114840124100c0228981d0002009080007107503000614a4101080b5a000545010340070300045661003805800000c0341900440041c0e0b000d02150900101c1c1d440b10140d9400b640c600b203000d8121456030440744c0d245d0100f8841070010302e002d035100015842c82800c0c884600500260200c0c9858410343c03048542e005054424082e0388560a05e0000440d419402400031882e12208941c0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 696547877 1250 696546627 696546647
    0x1a121932010c12091e171603030501090209031b060d0615090506071a0a0905060403030507030f0b1c0c0315050105240a1404171e07030f150b1509030105070f 69
    0x480c003050b5404000070712001c03806c0c140d24519041d03a031595030f09491500e0480020143c07415001300e40350000020f8480904c1c007c64000c010000c0280103445003440499240032600c420064202000f4002c1480ca0b0803544280c00c080e12075200ca00c10590440c0000420255407038204074001d48060095000245000001c071241c000d0b4050b40d00c10f2070b41d0b01c00b82c10004140000c800341062003250f0a0106058060f88002e0060700150b43c18080c01b00307608501802d0710710344401c0d01d40050700120b012445501d444000344010344039601008143c4c0da65100c1d1000c5261030002c01c1c0f011640c410040cc00c925140103041c6c0800c902c02208081b10541c00a103c20f94020000d90785c05200004998520030b042203000c440103440c0c10002603850300d8810740380d965129000c1c203040700d8048074000c410900282c00140c0714101e9034405580c2c410401265248a0301c0b0b4a62460f882e0103640f6000851103569500d4041c41401028008642d20b4202140415081d180094003440c18406040d2000b2030281d88211280 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 696549127 1250 696547877 696547913
    0x51f0203040b0a1b0f0201030506120c010c0515250305040b01051003090c08030706110304081c060306050f0a050a1a060c101a121932010c1209 63
    0x43d84942c0451029104e240c540607210803014083c03900c45040201d0268220141c0307000703a03400c00c91580c40000f030110050f8000030140d02030340000e070b00204e00d610a9445102c07461141096036003001c01d17031070200300407801580d050218066081d01c604e0a401003682202001d0394606d17051040341025240c9503d2181d045c01080d001d100210003800d43d050107900f1241e1955405824034003001d1383c0d290810380740d40000b041204d100e42030505005198070200d043c2d900541d048144a494615907d0395110403002038400300c003c4580303504000000c1425481014450009003600080d68900061100c0c02c445006080c00c0d50341c1c1c5840541030090900c2c01c41d80e07030789250a171406a581e00d00c201480340b410046011800e541420104c12030302c0d0340512400c507000040d0503141c3c0400001c60f054025100c0381003000364074185903070440c0c03c40032070210604498401403001d00e10503500703888100803007a00d4505158000c9a910b60111241c47c0754031101030310610708004401c000382c40140d80c90040780320500c0f101c070b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 696550377 1250 696549127 696549149
    0x6062c040f02180a02130812032212020102030130021309080c030903070506160618120e19030302031b0f0d0e1e130507050d15051f020304 61
    0x1c403046484041d11681c001a4403101400c240c9403a44a01c0d0203548040030300c01010060100c0011030440004142d16508400d042403400c1d99034031714030100381003c2100700e120301d542ca850408000c241001d0100c10a10f00c50780c00542e032581004206203413a2451055155074046000300c1202c0f5030301c020a501810342d8100c40155801502c0e06a01c4050086c40c40007414401700002c8001c0000e1000004094014094041d034440319981c1c010820603009522580341d00c0041d4021040008890350300007011040c04000e4403c00190f55100d80443c2040b6107407000104558000b6403466240103843c03458401c411101e6441886e045541c020340302c0c003070f0354038000300c10a642c801038000340028858180490754003c00c27902d800a250700028503464003400014003c100d6a031401c2c2d1152440c141c21440404080d181039480006c3c80020b40040c02c0062100e42084030502081218038081e0103200884a41c1c0000703103e46070708010410031602404065144d410b0402000f4901d865004000d840881d8030705401d03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 696551627 1250 696550377 696550403
    0x402041d16050d0309060c05150c07021e0607030c02040b1903031e0804030c02151c050f0f060d060b0607030915090f170a02090406062c04 61
    0x10501400c648010030004000405002020303080001d96100c030041c0710504021055510342c14020b400c03180400140000e02889014481c2c40c2c00b4107541e10382d45208600b1104100e2032622030b400d1441c0d090b01c0100040000003440300c198076208180351031300d03540940d124074400c242c40c0000310301c0d100e4050001c0c03e11250210a01c299942c5a0003c0c11071301f8013030b003070160707c4104449004100c2a1400201c01086100c0c001460130758000e0000c410500081d1604002c5032034544065038200706c060f0080342d00410034490403c010518501030290450002007500c111024182d009003a00d130014240c803440081c0f01c01300540d9000080031941c0019064070010903003039403820600301038200c056485401510019070101019442090401118500b0401040841c9112003c80c2da07070140384122000300c03000369824001052992001c41c01d09008508039a0304107032950100d09915001c41303060b01c0a0769121010020a0026402601116214440c0c0c3c0b13000404105014890030303000d840908410387c0d6030f403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 696552877 1250 696551627 696551629
    0x90b0103020405040f091a06241b060610110a0b090a05010216062a032301080f060705040e0103170c030d050402030f070308030f060d1202010212010b03090a0b0402 72
    0x704590161a0140050041032100034000c4082c0c5001c1d18100c1d081d10041901501702900e444103070f40101e6005081c81420154151018650030f040f10b20b02c01d80500400c00104a210713540c0304108040000e01c041c1416160000c10800002481021103040c4000305031311850384038000c038a4031080382e0b000382c0c0b40b50f2540b20b0584082c035040d501c10004040750310010b03000141100d03081c1058105c42c8100401c0c01592084210300e00031550700f10704030a4a08054010450f1a406a045111001d5481410000c100b000011411030f085003030380302c141160400c002c02c83c1d03106003d101c0140d001d17a035810070f5032034946040d642030110742052001424018060f4400c50006c80c0440413540180d9400080700d8640c904a003405004001c259022032003846600c01c030f01c45001002c90b507002200d0300320942c1d50841c0c3e0342248026406500a200d41c1d40100c0c80d0044c000007940300600400005519800161200e90840408412840603005600c0d19a418810082e0180000603101105a8813440d19101929148 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 696554127 1250 696552877 696552881
    0x3010504020f19050d0f0204061d0310150920040303050901050d0504200a272004080706030b0d02010c020102101a0a0b0c15090f0106060314090d050301090b0103 71
    0x201a10f00d03000000c241181c05568802c001c4d14100141d141c0170040122070041510882c0302c2c030310420300031400d0720200c14240c0c2460112012003200c00740170342d038288514000140440c0c00c0015a40381040e15503070103002d175a2a0340b14500140032209260500b0030440910303070751540541d1000900700701d40040e041141ea44140240d0303003142c110440c2440142018a40390358112a500892010716503807502526a520f890700c40d1404a40c180c51071162808060410b10511111a0342c0d030b0701c9440d442d0b01d90451013050b0a15031480c1d2054444030f07280c541f400d1038089420415558007640405040c50100e240c0340d40c6e102c2c070041d05150309082540c100322180c401030741045400c00254a009241500320040d40ca030f88010456803800032680c81c03000780c2d124413040402d8080d05401201a41c0a02004008030313045117801a04a82c401040302d03d450544a80c55080d52003d4000d00002500c988062920715650b0414682203120075001c4e007002000100010911f000510803040c1c000d0700c0b01c20a4405d64029 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 696555377 1250 696554127 696554137
    0x90c03171201060f020c040b090c0c0304053606030c3d090909171b030f19050a120b1912051533030f070806060105070803010504020f 59
    0x903800c201d200350b82d01c05000e42854052001c0d180580164110046507107414425510311a00050008002d03440b580120102600000d501c81c070144000c11001ca055640c0708000c21141d09803502c2801081071041102076480310409a5403e54034101707091140d259808114010004070540702800b41440b807481800088612080a0010301c001d0003450100c0c0700c101164541702840c90b240c064050b0b5079141d80d503007201c1005102038442c080307021440b5810155079009001d5680303d0402d83d580044c400000760708551050340c005440f214001013820038107450702d03000301c1c03c800d042c142107044c0710000301d000e05040b080040b4501003660303d18456115581d6065038406c11502c02440a522079100c0c0303041c24910041680a030744911401941d21854504042c0040c46543e9a1440c04543c00e81c03400c900b0024582e20441c0141c81c07211140140f400e0b1010842014408101d5000b040c1c902e18121029007403800282c480e5041210030000217021940401c102d80c1154000c2c1c60041c2c1d00c3e88010f803184154003071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 696556627 1250 696555377 696555397
    0x4120e1f020c03071712090103020403021503011a041805070201200304060b0a051003020a02010906020d051602010e0c01110a061b110313050405040212030f071104090c0317 76
    0x2003810100c262580014440d40705442036085035501c503102c07032101710b400780c41c01444501603000003030440d19031100102800640358103040150500381c03240d00250f29001481100c1041c464040010480260b012402e42d0128041815072450b150514551141d59418090401c0c2c01903250000314804510035030000f400620101c0400040b5940c00d007194090780c1c000d503002e46400d41041c04660062605100e00404c0b03401c002c000c0120744a051000380c001c0d4012560400a42d5a81d000f801c0c0801d5490005143c0c549694200140618046441c0410300701c500b00340e0411a854091109803015001030310080040c800d00b4505180c8040c81402c900c4c0880c0d1003001410301e410302d8111115040724000c0c00007985440d440c0c251010850000540d40e90085941c0a400740070303454003c2206043c55403040ea007203400a00f900541909a5044500d141d001038500980c112000030503070700b031180b200400c036032302c04040303c003030110154540310120401481d0101400102e01d070091201c924207400121804880 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 696557877 1250 696556627 696556669
    0x40909051f020a0206061507022101060f050103050a0501210f060c020105061521130f03081009050603030a0e13230f0403091e050d05030409060e04120e 67
    0x3031200c0e4028043c0d0050844400507110f280e010810510b03101086217049901240c00b2418005d40360200149104400104d90103a4001803400559090170b0244a02a0110004003001c1c2481c2c800010101c40001b0b040e40340030b40c9001f0061020001c0f0080c5040c030040300c031007600d030707604a030f400c00c01c00e030410b006401080c2a242c00e40d901e44164064010512881cac0880c0c00700000c040c104080d100510a8010103a0360302c45000c8010703407403100040c03580d8018100d500c02070310300300a42d66040c00c0910a02c10580100705a4805c215258110007144006060303a00410f000600341940440c1c0d50340103804400f401c1c011a40c505400a486103da60304107400c1e280d0f0188140840521207091000f0003030181d03a0102041030010307040801c80c46905001c0c1e6410303501c98841c1e81c6003500040400000c0e140203c02d014040c000025540c3c1d07502c0e04070018600402c0990382c1d940c81c00c182a402c680c0709a1003000e22040450801c408a0400000340c91192001c0c1441550b5010610004517004052020311a90310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 696559127 1250 696557877 696557923
    0xa05012010050f0709120f03090302090a09050717120d0213030b040501110c21040503010c09080f0a03050f0319050115080906060307030305160602271504090905 71
    0x403856048180070310351140c43c04001d40c0302c01c442110307280414011800c1b0301c0c145e15080e100013800c0780c4c40440c043d40a40340100d1040e8030f95002416140c019926094119100d044032410300000380302c018004c00d5168408108981900d42403621541c94465007844032801040c0340400035110b404494011000444441c0711a07101c0c076106201c1c6000742e4051f56039620b80341c28003140c2d0019504480c036000581d0000d142500c00f540c00e01c3d0700c0100722614880400300502000420341c83c01d019150403040b05860b861045c601707240300d540c135056110507a0000b6502140343d92001c2a00b00f130459217509101d121655070fa0b9200381c026500038038884080201185840c00010305420591072000b1043c20503561702205403120038020343d5999040d80c10307561541240804000013402407009201000e07007000f05a40360b00d90703911039070200e030040e813005a07211268070050001d800300c50015001ca0201111499500141c085420010703000707a01038180d645585885800902000308030507981c504684031101d46c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 696560377 1250 696559127 696559153
    0x90301020304081b2b032d14040b1902040503070f23030607050d0f02040303020a030f03020406020c01030b0102031201090b0a0806010305100221090d1202090a050120 73
    0x641d000300010740d00c3c0d00041640c1c5940602c0400c4125001c04800c044000480085c1c0750007002c81c80d0040100241995507102200c050150f894940040d00800d02e206083c207600c1207410181c84240180f80b411101c580c081100041c0061011a000b00d29451200c0c00c1c000c0317581240d4024412500002c1e41482001000039099107a01394400944a01d0201000c10400c00d500b0060000d0f08502c416a060304400c000600c1144180c001d0441142d41d110f010503080e03651640401281d005400650060704141e0f04001032680180c5034611401d040e140031450a1f01d4004001d45030300021070050304260f02e0303000e6401168420400e40c0e0302c0d10440c01071100c030707969502203007801441449841400b41242c20400212660041f40d01812260007a0241640e0408100702c08000e46c0206003280110070204105024490103051035842511120010060100b4201c1e0245c541c5c0d25500c000442d041c010040c0c400e0513200c00304400b04489080c02d2103e800424058050034031040d00c0440031070782c81480071803491 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 696561627 1250 696560377 696560393
    0x60316030b150301051009020a0516050102040503070602150103061d01050a0b0306060102340e15010305330621240604120c0509070314070306050f090a02090301020304 74
    0x1011000c500759010103000b0103050a0320030131669810150402d0000b00182000780e00140408d000614140d40340c4a4211010000c1d10400d0b102520181e40c042820301ca035007020015213000c2c200c140000d02408030303521690303038074240705000c001c01c6252691017010030100e080044aa1458000c40203000ca4680104440700030420f80c00030600ca4810380c1c0200e0a02d500100d45603e052000c245411310780a040a4070000f031256025619010b89050040040c45441410340340f0300403d00050800f14203000c0b180010242d0b500901080182d089030303200342c1d0701d8080180f84951200468010603001e4a0308074006174184c000d848810001000c0d44010415070312190603110301c11640c0d08a82c840c925051840071318250168005070f90440400c1109100456548404900f00c81c440c44054445a85542c0410a000c00075920040420780703d04404080e88182400d0a0380040945810080a441e201c0060b10000041d400c2a026040c02d00110f1444400c6170100c58404401500075542c0c0d090030700d44040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 696562877 1250 696561627 696561631
    0x30912020d02070b0c031210171006090203060a140d1e0203060a02040b0a201c110a030e06070309121b06030e120a1106041401060f150503060316030b 66
    0x4018060703044040703a0800003409030b0381150340d454011400d1039007e00d02c0c20b4109402410603492920715010014807074030600c502c45c60322807400000d046044410140d10050300c510b500300c41d021500600410041e5215407413080700f250b107442080c07102d8604031004038050040750000500071080e100d4581022031409141c0b007803003030310a60407a2a02e56071078803810200d00550182612200c000c00248605902c83c219604020743c41000520388021401c00052400b581d4001809055081100319811241c200203a000d200348120082d00220031240d070010319a45030802924807402001c10000c060510a03081d040103001404140d018540490070a02900740c174807a18007420000d00c01002c40e15920078001d040c80600410001c101c8552088188403d41e002100f41808110004206106600c41040018095400340034940c5401e2912021142941c00310307045000032499503c0c04001c07600c0c80c0d40c11419050324600d00141c913601d8980001c0d04012a10041805400454402009100d01200c0304e234 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 696564127 1250 696562877 696562903
    0xe0102030912070803010302040b061308010606081509270f010e0c06041217190e01030b06090f0d0f0b0705030702060a180605071808150109180609020103091202 71
    0x40d85812640040d00500d00c81c005008113007003010b00040005041c107400a210f2104014001c608040080511032001811688030b114039030f45031001000104d8002c040f6a4100400c80300b80508096118003044e52548040c3c10400040e14a60f010b61070b05106ca00e40e2a07412401000b0303200212801d80c8143c0c041c00c100100741c110b9004920701d01083c1d16001084a045851003206d4540040f240c2d1260180912641099480c0e0341040000b407075403007004c180307080040d801911009240948078000400311180c1203142c0c4d0103030104204008031540c409442c010600c3c421901480700000624050a05079000c2500401c07007206c0005124445070480090f512800b055401c58015a468070f02000a6410100390402e1000c103e42c3c4180114006410895000646007440c242e03e1004504010240b92726620013034854010600e85d83c80010510b402034014044403405100340084010441d0030405041c4000f8141c2d940c0b850785104590198100c90400b0790000b01025070282000d801070340f16141141e0b07032 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 696565377 1250 696564127 696564133
    0xa1b02210f030c0102210f07080a1503030305040c050603010b121b0403050601170105010b0904020c151006080a050f0c2d1207020a0302062a190f020c031207080d0e01020309 76
    0x41c40b801d50501c0c00141c40ba0101f00030400085e101e103a01925007030405000c0444294a5a140c5905140b00c1c01c10380b0700651123a60001514074240c00c2a11810515410080c411101040100902d400c98401d442d9450200002c076400354880d07141960017071690216007070b80c0c040041000402c0c400041200c904848034681c081d03404000f80340009080b50424083c003010440306100c0369446080c60741c00303810403d00d24000c0300c0805052810201050400701e03400104520400740900800d544100da00b50021400e60003446642030909a0015050008103200c020407004900c00401804c500c0e4404801c96007010000b4041d04468116074640c2e00014034550009030400102e00514400100b41624a4040e8003400d071a448001070352034419040c1c2c8200a200c40420b01c84e04501e22a40300034903110105e504050311a8913106d41c050603003014240084259005035511312003a48000c034404540c101c031080708a9650150b440d124165028404900616928000310b6249030001503005500a00340300c011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 696566627 1250 696565377 696565417
    0x2a0d0501051e16120b01050702040501090c110309030c011107090509030d0c020613110a0504020408030a090f0605041e080a0f1106070807060509070b030c0a1b02210f030c0102 77
    0x200040c420f09002050700002c58400c0c00c8400c029040e40b01c0c0c2c0048505141880c40c10001c0e400290555900307808c00c45440340d5400c0100c00440d085540009407000301009142060400400641c442c00305290140c18440202e26101c554001840307080041d00c10040100003508015070f200b5940c0c1c22034020340082c03900e4020031008c0c090002901600c9041c40e40150210a0b20326610f926135880c80703140f1150451f681490120f40c2c0c0d500e90000e04090661440290b840300700111008041e002c1650001c4a4420515014054603038050200c4080c1e440402c0e24074a072066400b11038495141c20b83c001f004500540b2210070800070001542d82040d405012407501c01c0e5808410400f0034401d200d0001c1c51603a0400588002a0050300301540c040e404d1001c1d10361542d56103001e91a10340c0f00b280c1d5161a1240001c0c03e2003a80e4015000844002c400002541685c83c1c1e98049400340d1111141401507c0840240001400040242040034103003801544e44400c40494040d010b07400040302840700ca000e400c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 696567877 1250 696566627 696566641
    0x1005041109010c140322120803180a14031b190f110a17010f09022d060a110715140c07050901030b04030e032a0d0501051e 54
    0xa00110000200115441c20440c940155842c40302840200c4500c42030f001d460316014020b00140c8514040003c07052001e014007400c11220b405547c206604018100603008003090112054a9100305d110742c4038404468100c40d45440c000301404001d05000180c1c0c4070348461300c0084080c010660070103101007041080c2c0242903071691041500d41180c440c40d000301b0b1012521261201244030f001c0d50700c1e000482243d01c00b140c500c0e1400c2d00500c0108007901c5004038140d10922812111000008003003100c881250f001070110f2a052900107a900c3ea0b0b080166054403100c451486045070081c105130f81d4044072080030305004014066480070f4001e00710f000035544118078405c41101c606035604605000700003400300d00782e00000d5648609105100002c51941c41d14040103000e5030242041c1402440e1034600100000541d074400350103908400c51044000666280e61010b00c40ca016800b6030500d050300c003042c0034684880000d4099030038082400b0740c100381500545500e03a40100401120340d0340382d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 696569127 1250 696567877 696567881
    0x1b120a0209031902100509180f091b030c0402180a260a0f12050f04260a170307210f0509070308040e0c04150305070206060f1806041503050105100504 66
    0x400040d401080c02c00000a1040c400e1b0014809170070f0090604055070b141d0101250300c602d0880b1420400c024007020721645000401c070240c2d61a0604072040500341074503020a403100c214808160003290041409005000d80d442844404400501038140325a5664030414101031407030306015500c0e800030103000142e40c01084140d80355800c080c05880c03045055480b40546040e445040d403c100c814450042404400801000100320f81d10340000c0030000398a0301c0f0448035084d00000b10742c2e0710103403560b0005a645a40307038007171000d0700d001c440d2240e82c0c0f50380649003401514030440c540c24001c0c141c070441c42e52550280c03201c40c55024040107180d845803041d07543d0b4038641c080a80707540402d100070461038191500b080d0f070003245000440e052613510481130400d00782c03214111000c17a888800300308030309604000385940030100b101c0d065020104a000301d046000b0021880c518180000001002519150001c50002079000113a1071096501d0511030b008000940b1241e07502c41340c0040000e0030f46054 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 696570377 1250 696569127 696569173
    0x405041a030f061b0f070209060102072117042d05100c05010e030a02100b040917120606090f010c020a030c0f091a0108010e180d020f07050301020705061b120a020903 73
    0x5c00d1003440c0241c00e40030460754020040c0482d0452281500114040c841c0c91540802d0074040f500d204800c614601d8500507040e01c00401942c1c91509202c1002213040f102100300e52506a07100004032a015a8002c072400520350704a01d40100952503090061940040c0c8103513945c0c0070324001c1042d0038450682944910032001644c005030700440000b440441d060b4000180050002c0c000515040d00d695840f1001d04601e007281000103000c24031440740d90030840e0151340040201c80c46890861558005089184a032a1590402001414070b030115107402100f80c0c0a0354018400c00c0509564400301d02044805002d4400d18608010499603004581c03103000ca9403640584901c201a07081134100b02c04003400500fa082925801c8859211203d010b0051a0386070030b556007e02411455640403501d4000307a0380c4094020780c810080384021900201d134541e00504090044601a1901d10030764060b4041e8120440d1441034081c14410800d078640d0080ca0403500c1074050328403c0c10f00c008030ba00706000b6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 696571627 1250 696570377 696570397
    0x20c041802131407030903080a06030503031305031209030403021008010b030414010f0509011d0604020d110a0b0f07020f040203100b09220b12060403050405041a030f061b 75
    0x4035158040062801c034030341c1440007100d0000080d512035900403002d9180015034039040401d507500000380c103165004d0703a401d6000710108014440e41f440d40d80c0e001d0762440020300ca05082d0150300154810040c060080300c0c460440008240143e06010280350703101e900c00d1004038418402a400500c4d646e02440d607440c102c0e4031580304581503650701d0b207403c441404d002550002d01d5607640014003016202e845421301524500f00001190140c840f103c1c040200f0002d00940c007644400c00308001030b40c0d0041c0f1040346507400001c0c1454480940081025220b441e00000c0300c0078400700d90b4941c00d1001c40c026040c0e850003220005090170740c0d003080c0412848182c8030700c0a15150407006200c802c0f0040020601d1810252007040308844801541c903161200424131010180c5565800541380740c104040fa0240007840064032b00c2c0d051650b0041c0051007148104e80c05940c0f45d2143c0c41c40225001c0807028011700160075560400744902c80140c894208448041d408000e003d228801030384800191170050030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 696572877 1250 696571627 696571661
    0x110f0609060711060714070809090a0f1d030f18150a020712330603050703142d0715020303061032130b1b0a020108040305030a060905070f020c04 64
    0x6c140920080c141d40220404e40d121401000114203035190030301b2803841800600c000240c2c030b00100c2d0310740c8142c8170b103a900741e5241d010340400c2c1d00e502000407044844a6100709181e0341d49012001112003c88084407203242d01484c0503040550307809000d001044441800d45c00d071002651904046808041d4082c400790186000110000f402661420311405442010150700f070700740d000c003c0010a544454004907503e4020308010420050b803290800e10740080d4501404071107500c00d40408551000740d84815210b84411400402d0000501800d809441d00221035100644807100c0617680703902c16201140220f28045c2200c2d110752244000c0720314883c034030505280c0c000511014581c0018502098110b0145c10031100c0c103200742d8403004900070300c83e98030841d4607818100b4501c1c078403c2107030303aa01006400c006e484100503a44030200a5010303a2505200f501d0388c841d9401000101019008400d200349440d00b44038401d900001c1d10000d413941d550031075800c154560140300507a03650181c4102104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 696574127 1250 696572877 696572897
    0x80a080307030509010e030408071406090f0603040c08010f0b011b0201023417211c18060501150216060507051009030c030305061906110f06090607110607 68
    0x207442900f0280e0440d540100100b0903104600402c0e0955220340c1c8030440690001c0c0c4c04000b450405501c0155100040b40e040742407062440105001009481c0300318814500040010100881e07141d441e005007084800802100e1080040c52005006082038580410050440803140070203a07000e840045030b041e8050041c004042c580d1107002d20242180300100d1003005850b000515242c90142c008010303a1142c110f02052003240305051650040040016080303c0005881030450401128095120028002d014000d07400c80040106207003403440c08041a0908818240556600010b060364500004891640507904059aa518030100e41140c0d0803450f4008100b0715000310042c02d8154069016030f01d5100307103494880d08450764013400b01c000c102c0514011013856810700c65a644042c0545020300f1500003030740141e003c085284a030008000c181c2130b40105440303042c480d1400d008603c000700c40d0030341070040e032a54503408116494000140740040c0d0796240c54000407100d0061b50750740c4840f138404c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 696575377 1250 696574127 696574141
    0xf0b010504050901180308092e150311060d020d050f01060912030c020d021c1a13050a121e020105160504031703090a0b160e0f011202071b0e04030306080a0803 70
    0x2410000d0000546009001a000d4a04c41e274003035001d01c011440d9880d4691030f100305104004c441028004001605090302e062000902020540c030580c441200ca20b40c513261140740c8980603208061041741c1780c13402c00d424000404e19104080c1e050721101d460b80b080043d1640c0394044810801207002e8006001140d8081c05400c256a00d8408280040c103a2000782c9604d5103051444004450300712030305e4840380070003680b003540d421405400090003030210403628a0707901c800395100843c0c2c2e4043e095541101c01c10b0740640c0101c0400da413500124414003110b5441110182c000c2904440b80804884014440842540301d04110b07020f032039000c0c014603000b0120003506443d50b000248240c005100d10384052020601d802c43d818401c4002210304039150b207070840d0092550304810318141c0100c036840c400c0c011503030304043c9115640b83c440c42c00607110062400c00c142c40400e100c1c10340d41c205042c200042440c20a801c8490b10440c0240c4041c00380c0d03644c0e400309581e58095650040c105031014004120b071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 696576627 1250 696575377 696575387
    0xa0b0f040e0a0e03070f060e060402060301031203090501060b040311151912050a1a030d080a09031403040323030606070f0224130b0301121e0f0b0105040509011803 72
    0x4008403100003003400035800f071149540d025050660300b0301540c2e4211020801280120040300d01100054181414268082143c80c0411b0000404003000717000c0300307404507100343c2c031480f11243c100c0020b0090582c1c030260007586511a001c19110100b80c801030b0803032030130300b010303140c800810103038840e486c101c0c0050f0b181c1885e107417002c014010451110b503c03004500380340c013800703000b0780c03294400240d01c40c600344203401c030740d41c1d65800a0702a030060141580f023140c000c6e54070742e8040c440314000f09040c4100e103030071110b800603031a030304401000c04000e120078140d000c0080300f0142030400e40500b01000e4598509201e0004580140e441001000300c640041c81c1e00005040d035030f101034882d810340060801d410118181400b4000f440700404101640c0380089005002c00501000c0030082c44c6505280ea5503100c5800000050041101103444a00c0723440b40b51700324421150801c002910b29010341c9848a09900203100707503881141044c0c0420241e450600c90320400b51a8a50034001c000580d82c0e09440c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 696577877 1250 696576627 696576631
    0x60607020402090d06110307260a180f0b0a0506121f061d06090c040509010b1b0715031401060c03140f0c060f18070303051804020403110a0b0f040e 65
    0x280100c80311303000c2000141c00d0700800038000188022140c0707074036120303800901900c030440c4150307000c1c0c1003d40f00d58410f560011909800c82075960f40440d50160168190070700c2c03002140000c0c405406440d115051101e0003ca050007060384034014001038a40c40c04203c030b103054000500c441a00702c4050020342d002c4484c010210000300020108090307a03941c40c7c541803503051007241c5885a94441c00c000b40d5280c40036645a101c3c2400312040c0c241403c0c0808108203050500540c0720304a030001e0319640740d02c1c1103a0140d03101b00144c4100c648094444a0091803c4280500c03640070904282c003c010f22100c1d01002070603502203994103015224251001c503010718110301d10503456038041101ca100c041c10f11004100020240009107520304042e0503040705818010118408100c410080300840b80e00440c0500440b501450010386030b00c0c128082101601d0a4000503500910024000040104a0140c5681040104c903101e003001d07a0358a51404920a070141c80e00181c104100c14041140200100380d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 696579127 1250 696577877 696577879
    0xa0b07030e0a020a08010f0f050c0d0e0a06060305070e1014240f040f0504150b0a0306081605040c090e1803070210091509050f10020f070308031e06060702040209 71
    0x10b148004682c01190581c40c09800060303059446600b8180051000d0040c000442120101048175140901c1d144485008000c180c0c04055140c03c500d10700c00e01f080044d8151942c0046003002a43d54a1400c95a02c0e46d00c0d2107000c1c41e5110150010f07420680c075030490400c0300d0143c6c40340c6030200300b10b00c2082020544c482c580300c0543c0e1000324040e655401003025220800740340c0d0071190380c1c42c140069841004101e911540c441c5060003800c145040c0d85c181d8500441b0000c6801c00d4490b5039629096010300030301d802c03842e054400c40700b007140039410f1030141c1021600d05460070418800da6510449100075603028208400030070038003007080d81c1c7e901c510302c45018150ba41035a051000c160300081306220001d14001c0010406a000d000c41100c0341c07520504102e1500705115014908004205220010710801c0d214000510f19800c0319402442640c0c42c4460600a5460f010f17202e14000b00300790000c1d280c000c031010081a507104201560f1b64000e0060100400031801c005155082002950185a4071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 696580377 1250 696579127 696579133
    0x10c05030c060406021b01150915080f0c091e0f09030d0f06080f0303090a0809120604030c0302070807060207091a0907050d20070b0a060b0705060402030f0a0b07030e 73
    0x41005141c0500a40340124402c2402507942c00c0e84c5005121100b46401200b500d9902d450101e00c60000d0030030a0f20103e031003224000c66040c02900002c0d151542a51200145001d101c1d004480e4040128412001d1002114105880d8403140f03c014241d0001d40102c4d0044240c00002c2400d600744807034100d0f44100104110b0f45040019808041942e05102d14a42c06544403201480701c50b505001c02103400e50103500950071441e102041b690f41d0703901002e004e041c401c0d001600482580300c0c40500d907030590b4140304450407810b05140040181102c80b00540c01070045c9180400c41000100700001107610a030700a0200a092841e41c1d0000c1040b07a04040c0042c0e940b1810002075200c1c0d0f40a14031038040c41c0c8803181c5a10395420303e4400d8800e40740c04080d608030f841290410082d40c860035a1041c3c0d4005000d03030b1450340c400900200901040e04075540c1c207040801c00b1400c00c500000d0040c401c62007034050701c0c16500300c02e071459924800d04000a02121222000070b1103107100384d1004102c3c40b440f00071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 696581627 1250 696580377 696580387
    0x318040e070e150603090709090813080607350a180b070f02071211010c06150906050915100921060c0e10030929070801140a05010c0503 60
    0x9000d2030000c49900c8011981d00b0503041007042c0340c82050200002100782c81d0b4502c0e5180221809840c4c024900905482c555105004030a02550b40142c400d40600c84070a002c40507151190940c6d40d51080b41c42c140000e07118255183c168054640c40c848184940c0303079101c0314480c030034556605500010503021001d1758038007400d4002d02030030b8500450326004488410003070906200040070b00c066401c0080c19580070303100400c0500c1d044410420019004940c1d05900e4843c4c0f170040780c030701c0b00800d070241010f0708103140144003075542c04c422812210200b0080050503a200148001c0000844155003000b2445000c41c5c010304207490010710f0003000c2d18040b10800d8550703041488002030b502e41c094402143d81014001c115080c802c2c440c400801d81040c0140414020000b0810380c400300310801059112104081040140e00f00440d80f0307210f40903489040a880b0721194100d0b0720807201c6600050510000184170940c8000303601440d8000f81141440d181400c005441d0701041c28801c0f51b69210402c0b03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 696582733 1106 696581627 696581651
    0x30801050622080f0f0f03070611130311100309050703060c03111b0601060f0c0206071a0406062d030b070201061502030a080f09031804 60
    0x7070316699940c400c41d18040c50700400b0741501c86524400e48041031400780801c0c0806035400e80000c50b40101107840d2101c2c1c6c0c508040c1110100e81c0c1081001e00f0204249030031203030601400c1000d040c03030100c02c1000340c4140310300c5a20956500303071311a00c412494031f003510030f1115022a030301d000e0180c2c1d120385e100c072501c41a884c84011701c0c3c1503440302c034645024001c2d0000864640c240345025101c40d15001c0c1000c4281403810041441c0c0254400490242d0127041d1030701c00d0061710f0b5501c01c1d898050b6424403030107901185094815104480c120700d40c2c0b600c0d0811a03441a4031409002c5401440c0c012000e200400440710101600c2d240815640186140c900c0d140449801c030200b80381c1600c07000e405900610294010080e0b101c1500c282d003080c0358000000300200406a0340d03006140c1d0b80c052010f40030150039100c01c141c913081002090081c2d0318113003009a01400040c0700145110480c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 696402877 696582733 := by
  have h0 := BRFrame.cov_init 696402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 696402877 ≤ n) (h2 : n < 696582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
