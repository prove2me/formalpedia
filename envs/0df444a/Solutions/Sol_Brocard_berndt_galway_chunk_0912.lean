-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0912
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:54:29.623952+00:00
-- url     : https://prove2.me/submissions/2cce4f92-32cf-4ffe-b946-74b93b25f93b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 163848920 ≤ n < 164028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 163850170 1250 163848920 163848929
    0x7150807020619200f0a02010c020d08130807060203092107080403080f0c0d0206012606130201110a0b0411010801230d0b04050a0c0902040503120d06030b070c0507 72
    0x602c01440c040401c1c071030074000d0301e01e00321400c2d41e034010780c414010b0300c205880e00704001140c1580d81d030035543c410003a060340548001c0c0c0041d460204840003051000c80c0308080c8030003660318902d03207484010741d4000703070703400d4080031280d11104009120014111b4005107210307440301030182038030b1b0201660000c906058007806046046081108100007100601a074007602e030092049502c4d00644050307980e01d03100d154912101c5118103144844000e60000c0e40a043c2d44902c200311580d2500020303007001c03040041c0310031986604510300154000041040c030f1520b4038014580301852407180261681400d000c1d0b4415144840e01c01c00f0001030003001111910b2925080c6400300b42507241145610003941d0b41340c650450708a0050119406a55103414038412a401c1001c001142c03e09180c555540c0c40c2c0782070115401e48113010f00045d480018420348084030381c050302610f07049078034148024680c2e000d120b121520941d141008400f280e80d0107441c0f44a24a00d807611541d0b13010720b0030f01034508440d5034803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 163851420 1250 163850170 163850173
    0x50c130506041511010e070e18010207030e041a09270a0203071205030c010c0302042606060d170301060306031506080a0803130b10050a05010e030307020f060403050715080702 77
    0x810000c03070f200410380d030030011400c0c41c0100451389001c044502606454030404401d2003040b0300030074210518078900c0e0091640c2000e08d000045010350781c900b42c0c014880c02078041504003003000c0755814076400080549400095403175007044c00d0310008101703480a8444c4000c003042e00c0810108203110a080384460080100100b401ea044da900280c0d841956002e843c4403003e400c0f5441080150400070b0b520031085042c024032a25069000080081d00503102c0d4400040d0000445485003400e80d02c1042c034002e01c2c1c8003408040e5940c1d41401800406001e041700c42818403c141d016050a071b001440c040c20440d036020071220324500340b24a00c00044003155004606e84070302084105000943e01035082c1d80654880e0700c07a510b540e517818000030040c001828090007042045000c40003448442c0039204200d6500b2301040d01d6100444440300d480f45807036010f07403040140c0b00241c54803510001140b007000740341500d0f0588943c1d585040800035800501d00f0140341041c0c01c0c5158019146507446a198070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 163852670 1250 163851420 163851427
    0xa1b0905011b080304120909020703050a08070c0c061110090b101a041203050702030615030709291c080d060504051e0c090a030308010f090506011e02030904050c130506 74
    0x11101251444080d10007402d1030f40300a00c0b080c1b40780c003801980e1b00408035403804640301c003554100a00903a1040d001e03400010030103000540d07054007400000b040260090860481c3c2402c007a010740e40c40700000341c92071042c480c4c0c01203034000245500079580703011700c01c0824044a090010f80000c4039106600724074200308078080004100d00c2d01c141903408841a001c00c0c900b80d00c04608040c1c49500c51440c0294140c01000d0070040307480c95081c00c9221890054080b98030117503951442030202c0318091400003108144081d25030840032072205a90025900400729005001c1110101c03100041c00e12085600041c0880d4810b40d0844034800e100041ca01503600307002e00e24014802c0035080d8452180c0d002c02802170804034400188041c00e560080c90081d085960841d20381c100074041c04001d01c681b0030084040700c2e0200b0600f00b94080c0c24040c01040c3c4542814007040402030200d050341c2501c0b00d0840c402484500b400ba42c4901505d4003c50218200c146ea9000000c1400120f502036041140180001c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 163853920 1250 163852670 163852673
    0x1206091716030c03031104090504051e030d0e070e040302070e1f03020904030c0c061205090c10080414011503120f0503130203070305060903120a050606030106080a1b0905011b 77
    0x5041d0145070303403602e826110300c8581c1c41c040c3c0042c00e081c00085840c4101040129148040341d003e240154004d0044425a500c80301c5040051250140b84103035640040c88284140a01c2e604120007050410041d20407a40d12000c1382c03c010441250190010307440711100308081c3e5501d8400c980c1203043c91021042c09142150201c101c40c00c50b100081c083c20140340002c050500c15010402515030000203141c00c07a640b090010510080d4004255040703280030003041c11504005910074580c54060240141c000c1c001d103064401c5900144140c0d00e0121083c150041c401c000e00c18412200501c2c88601405800c60800072401100031a010702880142d8815841041c0c1060580343c0c4442c1038050b4062001e002d00c003003418a500390780000d040d4415117003030040100f40070000c2d0410b92609820308038241c0e00d001c140c2c0d0075120709884140e0840400c1005004291041007055400910018003090600c0c0c941000101072829202c80c1c40018141c2a06001943c1d00070a180444480c5802001464166 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 163855170 1250 163853920 163853947
    0x2031903171015020a0203070806070e09090604020d42020c06060f010509031c0e0306010f05010c030507020d14010c0e0f06090f030318030705041e0504030912060917 73
    0x2ea000300c2d078240340c840300702120107842003001d00e810590240686241a03910000b1f1640c03104141d070b000b00890045140403041c0e082010502d441003036030900030030041e00d480d02400340300203102c9416182c09405d0b4001d80082007a0003144a0000b00c0070801c4150740c40401e2010035200f0030150f0511003e8010007440341300040000e032003600201d084034070700f40901c018401a10b0fa40b10303a02107030b501401402550045000801c00802c005406a1030300000c0600f49002c1544840007401039503682403000c68240615407041c0c0621161030301c6402c007186041260340000c1d104040d00031044500801c0b00301d1188148200b0700070400c44215504102e88104609400991500c0ea45130290380500c0c400300d841e01d1140e8641c00c4441d03241401030181c0750359206100c50f01001f00e0715404800e0183c0307d003d0002403282800d01c01d04e00300c01a4150901d083c103000011080250001074010303810040c3c140d00110b040c04210030700c101c640d8820040018035202074604120840980240e030080013030180a5626074213103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 163856420 1250 163855170 163855201
    0x2010e040b03071518060507080307030b1c08070312050907140303040b0408031e03060d080d0b0a060201140a0c0905131413020102010513020f060702010c0203190317 73
    0x1100e000c2059040745010030720709400c41d44505040612021180885608000c0c039421a0742440f007401003c81e1038203010740e8648a581801031080004100180301684203612150b12100c0049c80e1204103200c41e0862452001c10600c241c070100b00003d991020560000715444542c078511805100c60300c1c1240440303817102014130a0008200300c00d98604010b6a0500c04c0f50050320780c0d940e44e01e488030746521090380d50b500401c18060700c40c0202081d03403c4510550f400d9070310840000f40003000003059540c03006015085540c001e81c010383c5884000419980e01e0f020600075000710742c0002050801440c0d2008d07a108003a00303a10216140c10b03050f2010541c0f10303242c0c5041d81c00940362070354003161014000e4002c001101c2d102c031502d000c1e0342c1440301041402005101442c000d0740280070300c0d180d0340c00c082010b0a0648c4000c0d03000309103124050b414141000608a0b0380e00504282e56081e0198011a0a15041c00040c102a0408407500c00805412140c80d101c5030000c00e0401c04035103040b4040201341c0e05c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 163857670 1250 163856420 163856447
    0xa1e0605030c010e10140714011d030c030a03020c0c03010c120b0913030c1509080d0c050327120304110a0b120402090a090503070c030b0a020c07090c050403140705040b04090201 78
    0x6222040341425401c0004031604140c3c008850408c2c0022000114000c001c86001041c1c401601060b4a40800000040d10203604141010354a42500040c0550096228640442c030324010b1075030741002c035a42846015545150358a507404945000e0b0000e504036000440a40d05ca001408280040f480f10039030640d20941c0d01d824102001e4000d800c00c0c002e0901c8400d2291081e5080100c003504002802001c2c00c206540c0520510010308045821341700c500084a032550490600020754040c0750210118031244519403099035212251f4110590b0070740d000720381c02c1c0c4480824098914a50820111180080404000c0b090070f1a81c8020302040c95040030740045c6c82049004042140584103521480d0b015501100b1699141c1d0310785005062035a03503101c1901c1020341c100020f440041e0f01d00854603021140130241509909000c4800000d100510b040d004115050101000103101c14a1894403003000c000200405842c00f81007006455141e804140601e003000540c10041c0d07002444101201c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 163858920 1250 163857670 163857677
    0x6060108100b040e3102031006051c03030f020c1605010507020105031f0b03040b070905030f0706140d0c020a050c15031306091509020108010b0717030a1e0605030c010e10 75
    0x39245c409641d03c2400d000b130343e00100c001d1000e2900c0300c070000100700e10f6580e0b4800c1e0700384c42d03d50f5a814603a208407610340c4906070f040046540303951940306050080501c0d00344242000100c0d591351b555000200d030445c418010b4150b108070403151880d01c1c0c086440700140424070b0030501d443c01c0e0b039000034164003001d002086144800074030810745804602c604400751207030100003526480c2c10300302a40292410748402000c101000c80200d841e08000c039520280c08a401e00820141c0d19001d411039051048200c6810460824403811011800d140075a540081181d03000b040c030401242003d9041c907034903804030340c030070390003041000816806001600d0740400c00d0707400d5020f8a040c50030010042e00c1c402e13030018002d601c2e0040141c0c3c0d0744107507071000d11700a000f070343e455105a80710003104950384580803000d000c1041c540000d01050300f06a0086522404160000c1442d2100c0014141c803400000d00d1101e0558491b4414011420200503906090009182c07020721400c1c54404265201c080300c6090040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 163860170 1250 163858920 163858949
    0x20d090c0905071b030e03010f0204090506030105040804050d02030c041103090607050c071503020d0606050309070e010e040f0311031c05060f010f080705070c081c020a0b01060810090e06060108100b04 88
    0x1c2c5402884c6c41100380718003030020700003040d403003035518029486405003030225454100030801d1070a0500c14035104940c801e030340380d00c1c09040408000a491901d20200d03414440c188134150240c0742d6001c0d8084c113210185040707490b030500c455140c1c1880e1005002d0401c02c9414001002e9001c40081c010040b00c409242408581c1249074046000e84640c009040603103051100020340c82d640a002144160008010358124980790b40b07407111480402c3c0305101880c98144d0110b00801d1515040c0b180262190800f08485841101c0c05401e41e001340c44102c050b0007820266820408040c0542e03680030b24110307403d4031140c5615002030310394440100041d0410901c0c000080c880744c0110111b504198000200e4240c40d075480d4080b43d034135200c0da8818902c02034001c45840041b4000640c250955520103800089a801d00404413464103005000341c3c500386254000040b0385c034292080081026454001e048a0310f030400c0003429000003c1d0800544030034040007000145c1c220350588068800c890001c006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 163861420 1250 163860170 163860173
    0x1508091b0d060e0d020c030c0105040306020f0c060106030c09062a11060f09030c0901120b0604110a0c02010f0807170612070b030a0f0603020d0201050d0f020d090c0905071b 76
    0x1114040c98074002c10b818030740030580d58982c0e030008020700011400d80c21218564420014075442e0400c8054003408604188801e1000641c69006004111070514503a82058444a40036191400a03803005000c01d0341c0300040c5900319070002582010341154141000c20385014207104441c2059540080360307401540003900104039085507030100e140c0c00100000e40750003801403041c0b003560000518034420711840107500c143d81400e0084034101e906c3d0100402c4103902c503440314045054014041c0e03512130b40d6211802e40115403c00603000d400e0320340c1d0310159804242d10000d000900407992060601103100c0811540380c0c0e10006100c0709003101d004620743d64544501103110401403c02200d8907004404012645942510195109440000040c0407018802e81c3e0b2004591080c00041e40008680d00f2150143d40200002e01c00340130031200025510029200ba04101e1700306003030380080c503034480c0c0b241400c2c8164031220001600007500100280c3c104203202400e40544410f00c040d160044000010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 163862670 1250 163861420 163861429
    0x804030309060e1501080d080105130603080304030c11010801052d0604150813050c0402031306060b09150f03130c17100e030a0c06050c0702030312011508091b 70
    0x40466214500788060341000c3d5000e81c54007000303540d00129001143c00082d0804000402004055403902c03070140d540d003490144070710f219409942016954071124001700048008000b148207174040d545a0b880302c0918640b41c1107208800c046c407810040203000601c06503581c0900d0303010104034401010491706001c00c0101070356401c02d034010351100d8042800200c0320700011008400842d15a0358260a40e107442c0904480102c04001a1031a807040da594a02d5040640c0203541066207100b4140c2c1c0c080d0980d5401082c0c07189600521202c1601090508040c07c01c2c010405400355030300145404d1030f2900942d081103002c01424401518890b045450a002448100d41c014084410180901c81201c0480725a500560300b0010003091504000011008000c1f040c1d880200d4580ea80b0440140700b40c8070b100c0034003c060800b4448800800140f00144d808100401241c0680c0342403070950740c5020b100c4811141c20754003850a10165070100030740e140f0049008a0b860a4000807a640c0900450216 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 163863920 1250 163862670 163862681
    0x6110610180e010f02030711190f0804080604060b041109010c0807020402070b0a0504050c01090303021e101a0f040506060f07150501080105090c0a0b1c090503030106091a0304030f08040303 83
    0x30b025520702107068881040f9034000714443c0750191105804140c120080550340c1007120552030300003480302426000151401600d0115034042c51000c3d06081e220f82a690078104241e9040b2803640c0c1d0350100c03c842d414140182c424601d503014009003400720140003c6c00081c0c07465001810303198001003441c110b54641c1c3c151158980c000e440e0103024501058550002c000c15176080d1024400c01c402c4014941c0308a040000707507a8103038050070f950f00003411604c126070034003020f143d103a001d0030440a0010941e0311030101c2e84800b1059407110781c0c040c0020b100b84c1442c0e010506002e28207050800000380c880004490304d00468030281a6600241c0c2000884026140c0d042905281810000200b0100542206014510341d60548480e00c0c00a410442c1044543c8200204081c05010140c2c801403030722010303140c4203515000415803d007540c1e50181158002d07080180401d003506800d010444006184e5505001c42d04d03140d41c6113042c16100644005a0071035181d04100c48100080c04141c4260001d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 163865170 1250 163863920 163863941
    0x1e0e0a08120403062007030804030c08030702100506090c0f03040804030f0c0501020105060d0c0519030602070b10060509010207090504110306040b06030d0c0c0b09061902070611061018 81
    0x361070100404500760107099006200030749843e800c1000300300201d201d40c82c0701d102903228801032a00e4040650703030a6072031050051040c0c040c00420307013654011569130002140705c0c034016806461000691103691080700d02c064003090040084030200f020b519100c104075804030240100450312070f51280b8001e02e580c41580c00042030013845645000421001190400681e90260001d002c00c1c2e407102d041c008102080400504041d140d50407c1002d03050075080c01005008800d000c1074102c0d229190041641e00c00181100c1c00805101080984031400c80440e02808480c03a0161800b1600c1d00001e540d55081c2c000c1c0e10360f295459011904005041e50030741c02244001d4159405440c00382000d201155084a03803a01a00a002407a00414825108404a03560100c5e4040015041648000d039540000c00090340103442040440582410460000c20316200756005141c4d01e8100308000748189854150a8404e03030100d404d102c07907800426081001e079080d2407501c007880e0300c0c103a00d1140a040c40400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 163866420 1250 163865170 163865173
    0x51803040308120708040f02120a051b040605030d080c030604060315090210140f0f0c030301121b240203040506040e01030209090307080a05090303190c0309061e0e0a08 74
    0x103000040141c03400103810414514516042d01e07a4a14400303807440c00701140c0003001c0c962042100001440d05114611403905141c084621440480ea556481c001d40d0366240c1139185003501d140100c500e03240c081c00024240641c05080140081480602810009030170f0307140c21a00400083e485488039440b00c001940c00010001001850007628001010160300c00d0380100313103500c0b51500090149000062000d8003100d80ca01c3d080100802e10080d0b006107502106c0c0f00b0040014400c0d40b0340c10000b0b18080c107000401d100c0d040202c0d00d0000b0314001002002d02c0356660591040104000d05a540700140840040303540d03d210000d40102d080d031050b278000a40c86280854086820265a4190ba0507603100b600c0041146e200c0c241115940d006500009000010400c40c101400e4802c4010340814a40542124285002c0c0e5644107031810340380a0b801d000500305000c2c4003d0660001040008000c0c0f42808002103201c903107412a800d07940031500050001801c000724058403840e000c200240107050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 163867670 1250 163866420 163866427
    0x230d0303182108010b0a0905011101060b340818010e03070b0a0210060509130807020402040e06090709030c052701060e0111010b060d110702030109051f06050d020103051803 76
    0xc0b50640c40c808001c00344000070320040008074159000e40200e0381011103589501c8250b42c075000045988a04452107100207541350080011005024800b070400011000e06454900821303607239851540b85140002c07506030a0300304013000410154000c58140c822070110f0101800307922001610745028038a02c0c1d54052046440010303107040c031070000c0c01310b000b5581d080d100406c885a041c0e400784e941c94005c140e4040513500100300340c0d6081d15a5001d080d0320540c034031410045030790005401ca0f009079020054600c8410304201c1030f8500007250f0382c0d0112035401c15042040c203644a12405044600401c0e004404070f030010402010100020444004060304c4150315686aa1005103c0b000340b207072150204107d1040d0300341c5001c0c1801900d140f0b41c2d0241000381031486a070f0308080035001d1041030215605d0200f1450000d0786081c06050f840501070740041002003140c1d580d21404108220031072011038130b413200a01c0140d8446c010034243c1a0240303408585502c6055603001d0342401005861014030000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 163868920 1250 163867670 163867703
    0x90b070306060e060903032b0903050304111210050c0702120c2713080405031005060f03120f0a09050307060f02012d1505031006230d030318 62
    0x640118040e68100c3d5214148084101c050001c18090300f40b0295040e001405440740042042d00d090320400340d011a2070044440c0244d8020444d40f8003042a000100700000700024071401c0f44075501515000c0d2601c4d0b21269408641a07219440d05841d0070029454101058021080c070f41501d024a40062040045280d0401110b6890918140850103011500b40441001c00e013411503c3d441608900c0e160482d44d03444901d000329040381c207411a00501d0901c00407134951410001510780444e0044009210b0402108112004030a854018460380c040d203202c8680006420640d2844601c551011340c456502e03aa0603100c81e01e050304441d82510484400007045a480443e80200c0300c601c0d00200450700d0041c01c0c1540000400d05030528160b229510380c03486c0b07034196010100402c00120711510030b54549000038140521500002201c40e00c450341484140c01c0100b14031614a2070100a45c80e03007071041c012403580490110040e09240c0c0d20019240c4515090101c40c1100382d10403008040d02d000d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 163870170 1250 163868920 163868927
    0x801120b090102040b180f040b0d120512040305030a1508070302010503060d0501111209010b01090302090a0e010c03090201140a0f050304050703060606080901050f0c190302040906030f030f02060705030a0906090b07 94
    0x8100c1c2140307e40102c21041480e8102441140c590b500c01800200701007000343c5860107003044800c80c40040010070414000c00759005203005000e140f081c3d82c0c80e50b41c0e0600300b1501080d02c000100010184d1030350142008440b500040c1601207075428207001c2e440e40c2e14000080d400d0180c42d8070217045d650900301c50b43d541d500c002004050b01a450243c0c003d140c3c540449150885a034441c4450100e8124082032000d45028480a81e1000c0480c0011406c13242c0a94a18251004058050046030302c88088108660f0031000c1011840d424014076400d05110f4400103181c55003121002c024410b0000204003405418483c0e1406141c0180050055941c7c82800802109e401ca81c40100340d460440440c030039400c03807015a030050788142d0005d4200045029012502100c01c40400c042c540d08000c0000c042416014030801103018040c1c00c0032039641420b001d8041d030300442042d0300b1900320038108440a600101525044900f44800007190f5090389480402410041c1024152040140c20001e02903030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 163871420 1250 163870170 163870207
    0x703030206070504080c040f020702031005070e04090c05060a0504031a0f060405040312020c0c03060405070915080d03090816110a0605120f07031b03050f070801120b090102040b 78
    0x8203508a0710503946200d011100fa01843c040d48034650060781111215241c02e800104581c00e1420005140407210350000e0f2501c5040c462017007506490301d08100c0590307000324041c04000c0060301c05216560180d1b9401001d00300c1806014410140490f49003442c03031080c41510007450b0300050500b01c01c09440c50140700310308122004280c0c101c00800144060130b241c002c0501842d4075032211000c0d500003174034050181d000340d03050882c2c0e4450281e40004980c0c040041601450085c000383c0041030401c9403e00503294051a2184285c00e1403604000c109400201c803461003a844c500029021050b107001c032002d2056100750807000300680301100602140326517048180071700711004882e40e03540d003600380c03460301070b40c0004c0c4074cc640c544000406800c4403064466000307440740341c00500560240510580c29401035103400000c2d03503c0c420026401c44680300c81c0d802500c0b6050081c8298036000002000200010005080d07800031404288000400d40507900a072810903441c540f10150211168040179 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 163872670 1250 163871420 163871423
    0x50d090f141c0509061c150914060102030c0a030e130c080a0c08010b0d0e0f010908070b0105030c06031f0819060501090c05040b0304030e03060a060602160501120e120c0703 76
    0x3000054160185001d07000325490110081c180070f00b00ba103400003c00701c01407503803800034403147c80d00e45800290151040c002e0243c00b040c000010480b0b1441c400580325000204002d0540d0700c2044001d08410700082c0c0405190792600d021046101c0141c04502009201255000c425090001241c95180c000c0400d521643e000c480c100b29040c580d24048070000c0082c0314000c0c0030071b820400303c250a203103030b0002045600c41c0401c459046c44420103184c04c40b1000382c401e446048020507000700708104906040d004007812001400400f44a6000420904c00901400105100e036555509006106000709006000c20b04c152030301010400280105840f40d120101c80e40b507d04000803038900140d10841e02c10492941e0703454103007801c2980b418151352000e4000c1e01400010400800c41e07036020003099200d0440c0d10b1011441c03d00c0c0a001920700060003151000e801e140c50b1042c4641c1e6409034854500f03140303084000c20000d449100190038024081c0480000c8180015040c2c8803140001d144400c0701e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 163873920 1250 163872670 163872703
    0x5040e210d090b150103050114012a0515010909020102070612090f0b01080d0908120901090312031a0f030c04050a0e03030109060f08030408030a030515060313050d0e01050d090f14 79
    0x13640e20f0011011070f2400d01a10076204402040c00e20254402d00c1a00400380c0340314405011000004408002040d00c0f12086072140d20800d05da540b1000c400120500400c180b01d0f052100580c03aa0002c2e484049900600c0e0070800840c1810081e1031440d0000004690441000283c6001c1070520399900712003401154103900c9202c904045861003400c480c012581c810300038001d607200005940105500150095041010301d903c04030104a01440e981d503800441e88000500202030812451a0340103103800c0c501c68120004140c1040e100402d90b40103403001210700096694420290700700802c07942056240074070002c030011420103070940c0079000351420405059401c1e42d851001c0c130f6076842640941036684d0414015451118002e802c020b030081400c1034486c0c2444084808200c25420071580d000007042c0d039119000c1441410700c0f06500c00281c1d4a0314650034451040007a029110b0044008043c50307803a10042c0600281071482e088007544103141001200c11008403580d260404552407401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 163875170 1250 163873920 163873951
    0x90b0904140a1a01180e0604020408060a0b0102190302150604020c0f030904050907050d062a0c0c0602030a05072d080c010507050403021005131707090605040e210d090b 74
    0x960003400c140e417599007150384c0c141718281401c461240c03181002c5d12a0345c1064082c40007103040c00080c06194407500c5114000103035800c200e000285007166004a03015000340300e0140c5004203034046400d01607215940ca401c41961650b4011030000d00c105100500e25025484031444440004801051402001c036030a01c003a4640f0703000503880e400180b00c0c0551000342d40c21150005074407900540a8030f80e01e81c01c0043e440303a10f400004902010030358494002402140c200301000080c00818014003114030003981007004400d005409071181c00350140c0001c4c00c001ca0000000b42289000b9102004004000440e00d2546032152a6400c03040403c1c0007135080000246809114506035000c0380c1d0002c1c900401c07458000000c0c3d503140e000c2181c08103034824001c40441d4038140b0421511600901800400039186400720f035208031465038000900c62400c000360f040340d4020005103440d03013600702d8580c035860115807000784d50117209107284043da007402c0c1010402440700d1074a0440c8603074021000902e5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 163876420 1250 163875170 163875221
    0xf110106080a020d0503040f030c1d09030a03021b07090504150507021b030f061f09090503040915030c03080a09060f121a061b0f0a03090b0904140a 65
    0xd880140c0034811641d440b02107030001500e801c1480c18151801182620b2405440f14a240e00006003a0000d85000c061910108035003030301c1d000030446050107803203100b126040c00314800e81c403881540070074000c242c1c001c01d0031614a030382c80e908a0a0041d0200c211852075582c9c900d07800c0601012942540c031424803102a03101000c490103018841c0f0283da02038060f00c40741070806030854480400d020b4046c4650410700030350b00420003120b0300421701030381904003c40c40c0c03034044c1030340fa90380da0483c02030a4101000240040c1000050324151110800301160006091303401103c1c10744668800341c124a2a068004107005600d4002c1c0191a100d50300c1070000da840710001d48a001344100c01c0340015000c80c81400103414283d005000e01c11502e01c1059990b05c0042c00a00581c2208400c007060a20380040940d10400c20050f4041c9000340d640506000ccda881d4502a01030b1005120b03c4407250360002c0e60515640d5154040320400340d03061042c008070700340207008000800008151000e07501d048020001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 163877670 1250 163876420 163876423
    0x501080c030f070504020d09060218030f010c0c060903030b0a030c090b09070516020f03031201080106080c0d030503191d010501063e0105090a170304080f0a020c03030a0f11 76
    0x800c2e0507080d0080c080c162800003844000d50144040340210b230b41e5002e15900043c0e03c0c3c001031035060b22800e400b4464031605010181802d9000c0d00d107142a0b8580010b401a190701700710003d541c550041800500d060140c1015400b07484000c81250f4026000c0d5004001c028807640c641081e644200c80421102c801c003803c1c000202803e640e4880400c006210901182021606840c02d00348040e01d90242225100301282c990740101a050040c0b0240000611401800344660f400a02c441402005014408000300e8280b00c111100541006400400141404010081d461200d0385c003034420020f283c03180c084c05881845400c2581c010354201000011384c1781c4600c0704034026001c50040c100b07100141c0010110442070800320360306050b1600105e21884002840f50074814030b0b0b4000604002801490440449036035962000c0321040140180004500c0d15130590325851070000140d40e48425401c82640782c803d4000070241d2503c40002d10091542d404160013900302e400f0349400c0c89861501c1c40d081e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 163878920 1250 163877670 163877683
    0x20a05070614030114030f12040e22030f14030406060905100f210206070501020307090e040f120e0a08010209040b0d15110706060801020711010305070c081c0509010501080c03 77
    0x10740d10003401c3c8010b000305040d0440e0340c03180b000010200c484070301004410b1801c3c0001d512054180c1a408202085840c19200a266004401340e0001ca40e6088401c0080070070002c1003c0a01042500c5035480784640c0203504d140d140241f6186400c0d200c0c0f40c64906039015010074029102040d06160105501521010603c0c0980d01c0022034882e6007130a1240700c081e107045103899080e8a1405035621409620785200a240e000e000700c0015940b0701e0101c001811900c1c1603800b092800340a00d0810001c9200f1aa0805030968040f0805008040c00c91341101e044500d03010869001c804c0000008405105500504000c00161400e0010305c14502c100400c4504200300039040b00c265000c0c0e08020a8540c1c40550512404500a801d060140c1c4900c800c5075070341d81040d4200ea40c0010550140820900403403500402441c081c0010b10384110020214100c00c44010001007001c10f0122640302e8111b000c50404031200003c000d83e242c0003c500f406090700307124165103805112001d01640c103000c01d40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 163880170 1250 163878920 163878947
    0x12040c0510020d1d06030103080409050c120c071502030f040c060513090213080d0801060206220311121201051c1208060f040501030312060e061806040209030a03020a050706 76
    0x2d800192900c4505030b03101042c40540c0d20035804c103084130010640e03404016501860040e09084e84450404006400321480600304860140b424004c403848000d641e03240c0380d0f1100c1d5604503a82c440c4510310300040740b40542035911410754004030811095503240360a80380319034003401c100341c0c4403903035901d060350280f1800341400c03c41c102c0c0311014042403115030010710001d00d80303030404405203a80700441c5003403804104c007040009024000420a20343c0c108001d40e0000c034180300b0490192144403000707501d17000c0400018140041042d070040c90000c14001503000ba004049240c0e69007003c01642c002c0703d54240181c80c800d0003c42079914081c00e1203007d401d00558442a0f1621803641c0b0803003601d0300350700141300a902c004d00c508030204503103440c05a240254401e842d401448580d6001500c16200b0740d0300300440222901c400c014260740c9040180075486444c0002d4000f584510340414040d208915015805200d10007100003017550016840e0029800b61040d582200d841e0a821182c00030407581 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 163881420 1250 163880170 163880173
    0x203010f020412060905070b04031b06020c0f0f04090c0906080f0f0309240703030e0d11061f0f0803040e0a0209010c140f100c1d1305060d0812040c051002 68
    0x3d48005285980712200090240b0111980b9940d554030100043d4866041264003521024800400c603111410410103020240040c0044c130480d50b002c2001000110441441a540c2c8000b030030640e200c9a100404203504134242c2c4074059111060300029040c14421b165491054800d000b407148404244041082042000346151104800800800c0c85508000d07103215107080f0703804603581c0e42c240e0041030303810310985000c40c146d800c040d0600e00b03280200d4150410b024218100c1180110041101544000b60a040b9080a401c1e05205480d45070150041c0200e20300c81c5070045540350f4008050b108a5615001c107402a03500c0c2110b1201f41e0180d0b41e501070118149410f0300c40059103100d1800152088003041385c0000c50ba032100e50f8030f00007000c1e07440440340c3d982e44401d2000c154040c0008010705060206a01c80740c500b03002089900003820f030749080e00c580c0e90001c14111b42d00c1001e0501c20540118842d521030840b554112150042079a08827244482c0b08400030b1641400c682c04403003400d8540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 163882670 1250 163881420 163881449
    0x518060f0304171c06051005030412050a14040b0c0c1504091a030d0842041104060509041808072d05030301090c210221130203010f0204 60
    0x69072242d0a00c48480120680f180600440704c69030403800780024201c40300070001c18064541828800b6207000120220100641041084082140391042c00d0b0030310f074a40b81c04e90f40c0d2040c101088815000400800400300000180040c000c0710740006481d182d407014041c1c0d00a120302c5001c000111103461103c00b45110140000c2001c0406540100302e003003039025800a0ba028024002410000042c0c1c0c0f031808500d08030240030344070000000c840783c00001c201424205403074a0340c403641007084c0080545034282c0d6a440105043e280d5401ca982c03424800f0243c56212034840030050f0161f0800303030750355005602d001030a200820b080c8132a0080c20b60041c6070140b900c030007a214101500e10140594802c00107500c40c40d442101d80381840e15445000b1009180c407941004101c60590f0302800d942410004034450481c2041082c1403ca50781c0b4860903001a52032501d01c1114691111b42c0d0540071001b81e41030100b11500344507016451145208030005c0001015411b0003604034000c50161b1ba0200b01c4d1130 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 163883920 1250 163882670 163882673
    0x303040b130302330f0405100c05091c02150a02010509190b060a0f1404050606072d12030c1e200703060c0f091a030f150904030518060f0304 62
    0xa0000503000d001c1c1c1a003244003102498105000101752600c1c24a40c9040b0100070600c4420f002c03040d00c50b4913469003880745007566403004205024174000741e4480d426041450241403113214404509035030290003909680140e11207040c0541041e907914001d54242000641c000102186a03505801ca041509400d18420744034168020402412175420074051040419031b6081040c05a005060084003481590b016405110a5800103000380c2e026400a01241e000100407580c0c14003074030707004a030b969501c00400c250384c807200003a540003620451500d101c43c01c00c44e078180c2101d0034a0100352504c2c82520304800301440c10400111000000420b03200708030368150060003ca00e6008150011210190707100d4640c00b08032603c030342001c800715040c1840c40c080d0300e03084044000180301d0320a001860034000d0200b0443e0384801441050b85940080001d050021402103851030008090710301041c80c589494007070000c1d84000002d4020b403824078070301c500524010089400e4045200003070790554455 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 163885170 1250 163883920 163883953
    0xf010b0a0305070c020a031115030112060905120304050a02091f0603021e190e0d1109060406080f070f170a0204020904060b0706150f0303020a12140703020303040b130302 75
    0x50158403c2103004121540960340d86c0c000840518011084209122143c3c001c00000b582d0104031002c4407101480100880020460543c2c0b401e50840c0022544018501d8003605126400c80040600380011003800305101000403084e0000c2d2090383c5000031500da00d0014101024a282030a00903070820390284000340c03081d00500b002c0300d41c5401400c02507109480d00d00341500011040841e00b41c000010030680303a030041c0c0e03001c103006007030b83c07400c0581205882c1c180c0800f008c0070b0068012592003010410549869020308010034020091b140050364039081d650703c9040511a00c081c02c9007503c40411081d241a8030102c081c0c1405008100c25031b895428030020390405d1020035842176851200003030350440c01d4010612907204a0b0009201200e110803c140c0168a400c030006500c0c00c0340c018800a600055002c9a454020644680d00042010304507402440d039400300401d554046610400c0580020246014030f110382040001e41e5613400030401400010007000c0c00580c00b8001c01040500d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 163886420 1250 163885170 163885181
    0xf1409060d05070b28180614130e0a05250c050109080a05040f2405070203070512030705190302070303080703020d050403110105100315020a020102040302040c05120f010b0a03 77
    0xc103000390303442942c4c0c03034000300d0341600304a0100d00144083c804144035918681c40720801c40c11076062041a948039407458a070140304c42d0042d0024002440a8024101c1c0e0310030a40e1100d0240410050040c1e4884000e81c60751034040c0c03407200c0d0990915011521045500141200b0140103010480881281c51011180e1803880d00f03040c2c626558803590440402c410b0300051040e041140c4075940c0d07652074003803850b04c40740d0280e201e40c4030f03400c03401880100c0c61035075404120784d04403a01d0311640306c54490000900f8207a243d4402076100a04100e11040d40343d0200207003007108c0c000c400342c800c195a11210442c00310900c000050050304510001c3c00000d0082c42e100303802100c2c9280060034440509120b008891040c0d03816008241405100c241072007003409050741c055100701246085524641c0c8040c6001911081ca021481e00442d11100d0f181c803d40c10350340103540040041c408040c0c82d0b4030240ca40da0005a255641084040008095001d11481d4a04840398007008070b00d0020504411001001d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 163887670 1250 163886420 163886423
    0x603031e170705070f0506070f1103040b030c0706230711010204081509030d05091005070e010c0204020c0f010f061e0605091c12031e090203100b040209090906010f1409060d 76
    0x200c00140c0f0001240080007c144242c4640c0c4403012103c40592000d08074400c01e0040b00b5450b4070030402401100030000544c0d070826850146e543d2584020f00c0c1c04805814044001e001a91071030610b01113205107126078038064242520b45101c024440f840e11703400c0c2d01c01d41c0110000b590050042c84e8242c850181d115a202203018290381c01c10069071030b13100617030b0f40580d404069030b401503082e120049054800d0a40000860408042c030010b044000b07010781c1c1c1f00c02c0c00a40b28503804500c400d0099014060038904602c0b25000700306455041c88284000c028500074110014407030542d000e00c250074802d441c0155000c5442e010b04005154041003d020344803010000500f850b00c031010f001071311f1a80405801d5503d0f48003c507100c44810f8054151501c81400d601c00f550408031080c000da04c02080c01084002ca0034000329030010308802081c003a02c20b90a0180e0411400810080032110104105059030010003140514940d1046030255003503a00070030551004000020603000d160840c00218001d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 163888920 1250 163887670 163887683
    0x70b04020a03120305190207030804170d06180f0203013c030302010f050603190204051b0307050a0e09010302060d0218060307020c240403140708010603031e17070507 73
    0x190712a5942400945001c11901c0481d403500e040c809010f1000300c800c006e8a0008200710b09100035a2001030581d1800740010307104031440c202040301c0311402030448905040c00501446070300c3e80d5402c0d00140c0c0141500819041d4031b012041c4800318054001c03a4125110010140100714400d00120482824903050200084c07446035580300e90600c0720407a60085000340c000082034810003042e9401d0b41c0004041030311a4011100700d4801c04001d0104ca00b40980640d000511580e441c000744039144c00581800f98403e20110030400c1290f8001d008010044003659450b045d02041c00070701c0440e11083c08025800101840541c424041c590701504001005038140c40c4042541d001003401070744156002c00060300302016104807800d01100f0003414820144002e0101401072010221030700403070100a20502050a0700c0c50440f0041000c01d0141c8801402041096943d14001c2c4c0b045c00c001d02185c12910003c0304c003884140c0144244500c0c0803848207103412030350f203203c0211030704d5108020480e4003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 163890170 1250 163888920 163888939
    0x70302030d080f130510111209030a09090204150e03030702090709090b27100e07090303110105090c010e04060915060201050f07020a0f1104090606090b15070b0402 72
    0x169504010840380340c803103070312190a142058100c00c450070200812800e90a00382d2401100017410014030207030440214031000440c03071406003104034035100c0c00d0060701c5003c05140a102660070b000c0002c00150f00141c99041810b5510401041030b405030388a131542c4440c546441c58a094003e4951b417007001c0000b02035031700d05960365000503148c030b4003540c043c0006890b1700010300120308103200b80b11043c81d00303c40c0c841c040041614a59194092103c0f41018a4041000304e03140c0c03a07180d80600d01800d9240300c281030318901848010030815803440282c0005200b006105c0003160188600b5005d485004081c0c06a1091700c1c00644240c113090398030f10340081e510580090a4135251141d50402410300010030b14943c07034a140242903070300140401200340e10780c4040c0300c0703410340000c0e112540c950f00c4840204040d00c1d908181c03d02d0411010b0040d000b900b0700e009e0100b08011a8080015508100c07001c000780c000d04818481c2800b1003000340101c0701004c01502010601501400c1d9002c1e1000382801003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 163891420 1250 163890170 163890173
    0x105091302031503251421030a09062d11010e010603051203060612102105151612111201030317040b07110109020306091e0a050c01110703 61
    0x49900440d0303c0c8150031407120707944919240500a03d09085040454881c030825000b5a05418132424412942c2101526a880f1301c1a2035001410302c4580076005030f50091090318403001d803030340e0065500c840010752100d4041107080c001d2501194200c810380422200c10325107041c1501030442c65014505003c20a11201c1015000b4000d0717101b28995030001084251551070b0a0340740001c400d001c040001030601c1002420b444075000d90b4801d80750740242401a464061451820440680201c507149a5010102550b103d03070301030560425204904850350b90440114454148409545050500d45464007038401c1c6841103458004680340b81000182e8004520f075103d915502001c1160303c0000980010014542c00100103c03446150b904003220a2921345e440c080c03030344001130640092011000d038001c0360072001d41c030155281d5800b40072180b0302d00340307031020342c2e591030f4001d6600b84103015013100403100b0100400c1000c40c0942c05070003030140c100040019504100c5c2408908040c2c445c0260000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 163892670 1250 163891420 163891459
    0x3010f18090506010609060207080c2404180204080c01081902070c18060e0a02070f0605040503130305100605180103022707050a08090109020a09020306010306051206092a010509 78
    0x18001d005d45d46031001e046260600c081d003400a90740c00b1b454035812040c61a42c0d5502c60b41007428a41c0c62a4511600d51014003181a9a60040b80c0007204900003050000e01c901c091030f4000e10540f0407070803c6460145c0b00340e00442d130381e20b412512440010550540303600107401035009000b00a1160428410441d1101e0306201d2140c2c1c0d04030141d1000b0b85448041003000c6030740d518183c0040e024542545001c525442d003c510701e0820354000c01c01039840d40010107100d018001d568031840d171041070a88240d0b83c0e0070300664980d850496840038516210000400d49000b144687d0426000c003e0764100f03038a160200041801414107141d0070b4034003807900c0c41000c14034121440c850b004507110291101d0b503015000b0200000100480c11a0b0b24045000d03000d0392b1040802003c80301010800340e92699003000480c050840d96018513000b0308490001403800314040303a1988a05400c0007155000044800141c01c0c0d0f607020382440c502c4801c4011264003a500c2800244a842c00c090303ca00c02501ea002c8080 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 163893920 1250 163892670 163892683
    0x109151a18070f110a1b08030d0b030601060905150307020111070501090302060c0909041401060b0c0a120516060207020102010216060506010e0406060e0f030f030f030708060603010f180905 83
    0x210404072100304106500360020542819000c4629001c0010418075120aa8841c070015010308422072030407040030300c82ca011161b00050070b03404013a652140500d5000c100a0220010080d110340241d02c004503103144a40e454804a50700203094200f090312030b4a00101e140c1c0003810150465403100f98001c070420001000b0070b500307031051000050ba04000d0900070700b13214000d005005422010030940100e691141012500140c10011000c1d075040e400307107003e00602c61548a81903000d0082444484400c01040720313030031180202030900b003104150100321028031a1590101003082d40328140fa0200d90141c0c0a0204648180001450b00e600c955020140c02da2850048803415264404c0050b90b5910070084280800280d07014070101d800d251028082c0003402d90304070b00842004500b4102640c00700f0400f05c441c2c0c03072242540d0303030f401d081045c0401c3d41e4400c41d050404100c002c0c2c04a41c081c10700c07104590403505005000e410860500400c174070b504c3c1181001e240c6081d211014a40450701c1800708 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 163895170 1250 163893920 163893949
    0x2070f0c0b0d050c0301031208180f07170d170916090f0b0103090201081b090907030c180302131d06071d0102030c0a0f0c0306050a09060b030109151a 66
    0x1010b495508100005003070b60001402e480d8142414001003000400b00030320007400050600f03000c86035544807801640500340300c00c50441c0c01c0c850382c3c90300511140e0120f000029104001e0481000400300d10055980741138030038085001540399000c66911005804001d504610aa0141d5991032428000996a01c00e260001c08401d540e0b2502c04240740840c0c030864200171002c0c00e0034482c4005940010b00a060020440c505c1105e18603000c0d4141d0340d0380c000700d40040a004040c2e40850908000c01001408001e51460104800c3c2e044511145ca58008660841e0b500410081100618506140c05007000d502c2c03070130072107130320829144824505000041c442c0400b541c4442e4084030381156010301a08910a0606542041010000e160400f1850601040d00160a5604641c00b45000420401103500103030025185c1020301c08158000c6d004200392034041d0704284004828907040600b241c49100d8020b0680381680448104080b040e0070800c20139170304904810840b60060089001d50025408 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 163896420 1250 163895170 163895189
    0x8070b0406090602061b0309010e06040b010e0c07080304110a0302060a02060613021c0225140c040e0c09100f0308130906060c0b0604090c0305030c0601080c060a0302070f0c 76
    0x342485001d6002610b00010300300791008010302e06100300e0307914090081480c2046943c80c00800208010307406d4000c880e403060380740100c13907051601e0300f085a4514028021401840162404150303214108016150341d150801c00c02403460311550b86014103c41c5074020103400a85150000025a031040068451004a600903044a18140d01000b240041108080c00e80750f105000b04888103c0c81c6400004840c1c40c1c140050b40c810b072100c086159026102c00da200340b00b0200d8021030800083c1040c9113400008101190410240c2030700300720540340b91b203854059560184562a0080c60508101030f08510400e2031000180d07185c9400c1710282071140c005441190001071122600d142c050408002013007240800c011403800e01c58020207603251600090a00308158006c074a0b45d0360303070341d02000c240ca90000c503a0425640e80d00d0031030740344c1c1c06c50500810305002e401c000054a00004c14903540d83c0d000180039910b030141c8400d06400035045404203a41e001d454550407000a19240e2898015010460 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 163897670 1250 163896420 163896427
    0x60c0a031808030a0e0f0307021207210501050a020f070308181c0e0607020607020d1506170d020d090b0d0e03130305120c030304080702030a0f03050d0f0e032208070b 73
    0x44010180c1700d107104200e00d242e000c0409401c40000c0401664581c590440b9007147c05449000042c2c904807590b0090801c2d0803203041c02c000d0400040094003502d6105200030b03c0107654490042d0200e005221114000400411410300002c0c803c52009910a814071513030000504003456451410b014800c0002c180414120040e01084d0082c084030141c0303004490740e034a00845640031400501550100174014407280a02e5020000212103c085c02d9500e040200b00782a500c101c00c80518100302d0f0254494050514100b01051021919415040403500c91111b00c3d40b44c5054a00c8a600211400540035540d16050300003031070900003040071040c4480e17170030f850301d0850030000e050019410303045254602c104039038411f00c0700100681c0e604c6a000f07000691203040c3c82c00405d0508040400082c1040240240d034410950058080c082d541500da404000010401240c08116050300703c10155940c4240490303c8002c120b0544222404445040003121130f40c1c0d80412460f00c089500610002e01012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 163898920 1250 163897670 163897681
    0x60b030f060f10051f0e030f0a0f0204062c060303090301050a0c090b280c080c061902090306130206040302090702070305010c140a0c050c060a110d0908060c0a03180803 74
    0x4003c0d40d40a40000c07680200c0c0604082c09146002c8640042041030010084041413166010311040b45541c40e488140c80300700e4aa4030700880f00c0e51250004900c16481c1010115070b03a10700d000d040c8031195080403211101610600d00c0c01c44510001c1c1142d0381480f00b00007080d1280c80c20b000d8103000e100700d900d010440101d40c42d00a800511160000d100314030b000d00c00b0300305030741c00c9032407500403100250b07050002446109005c03a003143c04441e002e44440b4001039003000b02100003403210320540c5c0800742c020403800c506045206070301c01c107010f569060380503a0110310201405c5d079108141a10050103189040e55942c04100030f0402100c0800140e002410708105002e420b008079502407040f8584071030504000034940300103009000d009410403c1107035500d81044401c002c42c4420400c000c00761070300c40e00050002026030902d0504ea55050180c08405060180190409800e850b402000f1b00107a0345c0304a0160341b036400900e080d4007090340b107540500114001d000020703409801124159030301c0c50034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 163900170 1250 163898920 163898941
    0x3060a05030d120e10140a060503030a020a03050906090d12031b090b13030c0f0512030c0a08070507030b010306020309010b01020705010e01050c030d06080307200607060b030f060f 79
    0x440d80414000e070862044180c02552080843c0e480d0f102d42d07040003880300c02180c4010b180c01344000d9042010741c0303401c41ea00a16103401d03040502c40da5000500703001c00b946401c01e0540b41c4c06201e04420144e44224001c00000703010703074050103044801428281c00c1248040004501241064040d01d0400144100221856160240b0046100001d03480c0002d200c0254000741003c440740b050201d0514041800c0c141d886142c0b032040000c5411800552080d03848007001e504140d5203100d8544203041880c151901c81c0b0020040d6118801d001c00a00140c1a0310740320302203d80d004007011540e60003200e002100180a101c4190b0113180540801a280d10b44828403608541d062800e450655104141c01c000980c0e1008440c120a0001c0c41c141c0e8035000c0d00c81000d4614007451101000d0a03082c02004105448000042e103c030038042c00400c2d8624006a031800181e40d54042a10f4111004002510114100e034000003250301c0f028003100e5a004420086a00f0688141c8185550790b69600601c0b03815a031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 163901420 1250 163900170 163900189
    0x1218051e19081602040e010f0c260109020a020a060c03060303030f15031e140d08010e01080a11062a010c1407120201090c0f0e070e030c040906020f07080306 69
    0xc40408458103003881d2264912802084a145078001c03d24039120115102c0307401140030444144024040240080c0300c42e03001c0c003020ba40300c90002d58140c3c0c003100759000c11008aa40003400c5001d8003056424420203501070342c0402d02e0302d4198801d8031500c4000600c24811800f0001040d1740c000340c001c0c114940101034806c031401060b4002e00301240d142c04807405000040031642d000e8405c112a10031111541c0c01d12201c98000b801400a0500d0110100004120f640d40203440c0d68881e90280c1c2c8903502d11400f8602800380c030350745034001e08050340060b402d20010010800c1c0281744a0a110f40440090b5422410301030110a10400142c2c00448000c24000c05404000500340704847d03810070020b540160181d0180034010281c01600303c01c03107178000e52000da0642d030005035901c2041c0c2c0f1050401c040b894103110f4000e000c150071000481d607901c504030000300244014060328800805008220180405032070544041d0b03800c1241341d21025404004107081c82c0320b509425213038608881002005030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 163902670 1250 163901420 163901443
    0x40302060a021006050409030e0f0112151d040b0c070501020f030108100b12030702061606020f0c1006150c0302010f180c0509010303080118060806070c060b010207061218051e 77
    0x1f0b007001c0d91140040d403c41d450000b62a415100c4d9001400018012203410301e00d800d01c042541d14001c26075140d42e02c12022032080c0c542981c540d000084885442d415440e1003180d0142405603014081107801c4000d000a00c856405440090f09082e29921550400e600a9000e5000340c1c0c03000701040d000503814020805601e00480721400c0350040c1d0a140c584900c200703100280f0a650005007154014811341060079015000f0100719150000034030a0000c541c02041000d1741c0c0d1240440c005680341075402800c041d92400c400407d12a0920441543c404070380c3c9800300c00395500c9955080d00d03501c02e032082516840000e0172800508000b8280015042d2140d000700d070080c095040148003281d04415050304448004d5540c15405020410460042009801c4442a0700a403001d00c403505500c034911002c218050b880030418480d0340001a6568072041c8510000700ba1003403000c8444041c1e40c5e000a15400c03000b50300c2d14001c16141e640383d00b030000a611741c821018070f0080c2d0082c000c508105041c001d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 163903920 1250 163902670 163902679
    0x40b0603060c0901030e010f020310050a0b07080a030b0103240f06080603062802030a0b1f0f050d0923070b070c030807020f1206011502150a050408040302060a02100605 74
    0x14186108451490f1180c945a903041c10b44a034400704c002002540604042c41d0784400843d2039062a03408000d912106102d01445202d184a001c14a01076217022580310660009400c1d1508000c880240e000e01032412203181070554620b03502c0e49503400c2d2500038100c01d0816422520160502c10000d90300307034040d081070782000001c01c10131013a92030019509800c4030381d08070210300c0c02003a0307001c03283c101c0d10f4468844500741c0040706004202205070811000640100da00c049012175803408040e201c0d103140c0c820300000b1100c0300c040c01014007a0300140026992008007181580c1147c41740c1070409940c203000e43d50300d0890035103040034000c1400480068910b1600e8103242c0640b030780750101200e100f4000030f8100340300042c0040c110b40d0340c5403200022941c0907200c0c1070a1810300c503065407070b05424814031303c0b1034807038180c400c0750f007407000ca2070018407140505c6021441d103614094130014040201300300c6051078200400301c0545d540340050410100e003a4018981d8400740b01d8940d06503a050382c0b00e103024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 163905170 1250 163903920 163903933
    0x905011d0c220608030c210309030a0c0203101a0405100f1a13080a03080906130f020a082a0f0d03050c0a0c06120b060301120b0c090a0e040b0603 64
    0x715030b50110010000e2003040640c5004030070000b020801041203511107102484009110382c00c00b6408110203510302c45102d00b100b610000c144440d8151300c4112400c0c04160401c009413810507004d01d46496210380040c4c21a06107100c8120800102c0d5040307100c10818000100c100a2586041e004099002c1c06800907032000e5450645050450801c1d402900e00344440e2900e01b68000080340c003555500c4204500c810308041d940c060302a164100d80344160005a44c140026000440001e8528020440135044813a0000c10f41c88140340d041c12a0022680401c1070100001e4a03e0204051001c060000007854603055005808030360020794a004c4500640007890505040e541e0690480503980d01400c06a5880c41e0805000b420400340d15001001142c0d400400300310541e101004c2c103040008507604100c034000000070005c01340400d2040a00c0410103081c01c80019442c0400c0503002504844881e080049940024003101e01e550880030601249101300005d00103524201d5800c2003099000d0314a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 163906420 1250 163905170 163905193
    0x30b0903070c050d05010b180f0a0b03070b13180203160e010203090103180b010b04092906070206070b0415050f09070e060a05030a0b070315060e040b0105040503010905011d 76
    0x2c500c2014440c80f84180004103903401800800c0d00701c40e4503040300908401d511480c208a84c09040c0c0251081216180e003c0000341c6480500e202c1c0c070040010080051030418905001c6001036030206001c0c000c07035121a580040c03044849412403514078038030400582c032807800e8203101000042c02050079013000410105080981d030007000f02c0740800820f280100d00c60980703030000da0100e44084002444414944000a50b00300e080c000782040d9140c09006018106003040c141c1042a003440701c240e60007041040f1006030b807030710070300410059102a280504100243d02c0e4082050b108031400d46481d07010f2525852203203140d22801303900100c0d0111000e5941003040c0d900e540e4046070300071001003085000115801d952403d101c0001070600508031038000c0300310301d40f00039640e80030344030030340800c0c24290502c0201200b0391a0000b51031295544040da104200c040001412113001c104d07042c8a010000450603803000c1c0140120325000d90000300b4403000520303500c50700102020803134180750012815140e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 163907670 1250 163906420 163906433
    0x51b0111070b0d0b0130060b0a0e011e0801150e090a02040f06050418090302030c1e0d021515150d05041a060a0509060f0d030f0221030105010f1808010204030b090307 73
    0x101b210000d40040b9408150401204000b0031464014412044010a00c0031102c0da210085103c40b080a030f803000c000c9180c000301780b1512a007a2600384003080e4034000500001c1c6c50b0107000c41c070b03491140c684001c040c0031000c0450b4400e90159410040070b41c0000d07044c00f00300d01403003042c4010070b6141361031450300d032410010405400c0c0c030100e0200309645406080c01414408c000340c0300a55400703001d8807400d5441050000598610780040c000d503001d00710301c415407980049032642207002c4260300c0d03803103a990390808400d8240f80c07007400796442001c1e4451400b40e03ca214014103248071600c0d10008440c10036007041031040310000e605903080b48904c0c0401c841c1e515101c11100885000350b0301c03080942c40c1d010024911600c803820550b0080d980390304140606501180d013460400c1d00d602516a6440780b02ea810600e9426200c0c0f00755058010001044154494000d413180c003521071170401c44031500d80600c458411810303803014941c6da402180510500a2080d14550880c03050f10040d0302e48982580c0350b2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 163908920 1250 163907670 163907717
    0xa020d090509040807020112020a03090203100b090c03090a12050703110a030e04020901020106030f06140901090c03020d0206070209010e010f14090f040201110105040f03110109051b0111070b0d0b01 87
    0x3850304c00c0128451085900138a030124140d107001c8002d54443c0303480f510040c0280440030003030b4401c0c41848944c2c140b508840c4949106008094183d40f02d030340d40c44011030100e91000d089850107100300640302d801700d907401c200103085103171640e42e0540c1c2e600a420002c00440c0c030034801d0f8045070004001c80c030009400503490844e0610540f000340e10740c000c0b440181d00400e040d03400600403107010070700001000341580c4103012036180d045440c812a201c100b06582214800d445c01403c0c1044108180054680a10140f40c01c038030083c01d81385002001e5002c81c1c0995001c0e8095100d100c207030001802951100241540900891106040c61551001c000785002e40c010b81401c40c001c1204c0013190a5910030600c103400309034100004e000d141854546000c403401c0c0d500050b00000d4012200071040c80b018050440020380040040168070020440d06440c100794912150601080d81c0c03004c00e03000310a07c61440206501890031752248482c0a4030340590704048041c80c10000d001002035004400a000d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 163910170 1250 163908920 163908923
    0x7030314161d0a090c02150705030c130302100206010e090f1f06080a0b060901060806030a1211010e0703050c0405041a130605010801150b0306011710120302030a020d09050904 77
    0x40300c489075102041c440d1002240320701504480c52a8012800c80c40a800c0b8102e0f044155081f80d5803c40540c07000540c2c100f068070114005001000032440c501c11050160039031160b06082d4941072580ca900080f15811030610310409600a40d0040101c88007160781c065000c2075440c094400034003405031007506d50b05e00f0a10b18508481100c0800c07540101544030002030000b03c1c086074020030b003a04107515030180850360380d88915040c1c1d0010071841d1059212034060381c00900201107880c45683c039a0a4a594034864034200074140d010705800000074059103a0317564484000d0021a811410030314209800c40c00160301850038841032200203200805002d15660f000c0c2c850641c980c44115250115482400005c0c00385802c0100124148a040d40b01000c415065a0b040f00105d0f6903481d0301a090000301c1d14140403600d402c1d2130050003040300b107020b40d02c0301848641074013068803002120032a41d070030841500164400b20f404a01d054040007132001d401c1142c140039502a02d000c00180003458006e00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 163911420 1250 163910170 163910177
    0x402030901090203030f0706060603061a070201021513030e0f0d020d080d02070b0708090106080c0d0614010303090303111515031c120609060e0a020714030703050703031416 76
    0xe04a100039407203035030426401429240c0c2c81034031a40803102c83e003200300142e40c00c601c0c01d480010380c240248200c004580280e00407075001d00e882d4005001682010005a05501491380a01e000c101c920906920070050311440f40102011810f004200401c0030010a0241000140a040c50354405c01c8c080c2480f03604580d000112121441d0407041401120341100e55540080b803402c042041c44800e02e07208414959a00da81599616881805e882091054410a8000b88a0151181031001001c001c40e0f004400115014070f0054004011070004d1380154009000800f05200b0164803c2e190740d180103403140185500a14181c42d05040b10014024945640700c412030400c03a0784041c0500300f60140021102900d1058a2201821048009030140a0b00e4580040030925100e0742c402c0380c064030305032140078100c0c2d500e0aa43c1c03402580100c506590702c000d60080f403114080100008e001951180c0d41360307501d07009146005000c0c0c41005003580d1710f28114004004405a1069444a0400c882d2a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 163912670 1250 163911420 163911427
    0x30f0803091504120e06070b0109020f070c1e0b070506070804030314070c1e0b0f060607020a0b07030e06030405030d0906150605030f070f020d18180b04050705090f0402 74
    0x1a4a80d00c0c000c000015000200040b20402090103060303018681500c5040c1c55010b03200f4004820400c0c20f00c80d40100070400c040e02d90060102a00e01d601409009840480c0d032882c01c54113444901c1085615407140c5130107400f142d22a40d01c108100c81c45002441c0390ba400a08003a52966069140e900092100701084203940001341898840d421481c050342034102c000c02d02d418181301c0101044c1c9144800d84e00288605800e81c242201c442c0c6c220f150f2600008001a652202410400450f20141801d680309405020b9000035036240d010090003480000071441c2c2d1440c0c42e00d4040c0010110342c01e0345129084c2071040001090002c803c8407404507002000003147e0490346481c0f002444110f5410307107001002e00300070844e07542080003076008e0028a04034081d19074500904590094804100c8e20040c2c201d03200c0058054049d68040424002418071071005c10b071101d000f5982a0428800c2607107140c0c6410040546041901c5407940004c1d96241451a141d410b8001c80c4403031080e480958000c0b0b5000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 163913920 1250 163912670 163912681
    0xc080a1e020102160e040303060b0309190821010e060a050121110a02070608090a020f01081008030a030507110c0102030406110708010e0f10150b0a0201181203060b04030f0803 77
    0xf88a808010764021100d0380d54185c4403809200302d0001190200c000c240f400401148464401d000d0b2440307075810000078640c686045405c202c00c1e80d4441c104403441d50b02440401106450411b00511012408007248215850540701c603002e55005040c29000304040c010602050740c0c44040c01c10a171040c4288480070442c0c84061100034194007040c4403040c5c00100355480c94540c08038180b030480f680c6544100b2a030301c403049101d0301c50141d20700c0250700c14186940c07070030a54060589194003546400a0f80507556581c04518150b511090000300001e6562042106a54111440c29070680c058401003151203503100001c2e5891145c0e00981061000b00b4048035020709007040f9000103841001e0086c001505196042c95441c0d0404d4070130910b1340200210308151880a00c81d20f0742c244110031090400303030314105068a01d60f000340c140108554036000d40c1c1c281a0307034103034180600ca0b11801380f56000c0e054608005040704c03241e0300300082c8600c1c108420404a075050300340b03486640d04482016580c2d01c40307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 163915170 1250 163913920 163913923
    0x80a0b01050d1a04063002030f0a030207030b09010c1418120a060605030609060f070e09070e04050a0c0e040c05120106030203090606060301050d03030b040b0312070c080a1e020102 79
    0x2208900001c25091504034045861010f24110303c0200c00c1d03a052011640b586c1000040300d500c214400441c04680c0c039005d000741940344001e01d03014006804e42e140d5032442d1244a0410041803019009a80190b0303040040208000c5025840f0400000030010b0007640c101c0140500c6d40302c00c1040300c00d600810080290348115510069600c401461000b005980b1001c103925421340d14010b8640c0c80c504200014582804a400ea103c0c400c014040c051955031143d0b00c20003114003030601d404100b030780611a001d039243c0501040c000c0d001c42c0c8a8200c801c824108110035100000d240113809800c2001102d699508a8410061384004481c080307810090b0b55400c0721140101d9500c0000c0e1001a170000442c076030194000c6001e0310b0704805039848c03999442d0034010326100a1092a80090721083c0030404203101b0307800041076450080c4049000030103030002a25180320307901000044440040d0f0b000030000121042c00c020319840f0050f00e901d00440d143c1c0012150342d2841183c0500000e1209800c5a10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 163916420 1250 163915170 163915177
    0x3020708030c0c1905010801030f150903080405010e01060f032303130609091103130c090203090c0405130803071d0d06020702010f140910030e060a020a020d0e01080a0b0105 76
    0x1010450342c03900c5a4209080d5142441a5407600410010501c200f4100c078011000701501c0c01030715040030503444e580d1621600814400b055681500882c10040c060410340140b0046c1070207941d8100040c2001d007865402c40d41e107560700050682c50814101302c480582c1032103a044a42001441c0160402e010743c030603c0651251480b0b5083c04002140301d90b600c40082c0f810161fa03001c0d60303201e1070151510083c1003201c12005d607031160801c09000082d030032008000d401c81000d02c035080c6500c10540d14103100043e600f0503030380800240c0003041800b010741098402c183c4d00088070003200ca2000d100d500c982c80d580c440940103004000c0c601c0e1b00e81e8103c0d030040d4070700110170001410381581c0403950b0400760001e4010b010b00f203000031080c001c2a0001445240c6100c960402480401d103000220000c2028400805611005050b20b4a0201160600a01416100d03004c0440b01513590714078004001d04000e910079161040c4000c030134084096990001c0969445910b00d0000a5214600c0c80143c2e40e500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 163917670 1250 163916420 163916429
    0xc19060e041e1409011104090e0c03070e071101090c0303110712030f17090d1209080409240b0306090703091217060f010c06091a04080c0d0305070206060904030207 72
    0xc001103880449241d50380d202c50b4410079900400301d007613290300380c0342030903107034035840c002e04d01c035000d10092091b9175559105010428444088500301000540800d00b840a5a4403910780701c4000c102b0405180d401c4221200e41000e4007008114250282d0b44104000c11180809810040240300004805d0380030800e40003d000522040070340e90000d882c00510020710030307800100084282c1c003826076801d0300c1e103c11401600d20b403000c0c0205144c821022505c200030020000380c46926503c0c00b10124461038000c1c005400030700004506c00500480c650164800e03605c0c00030310502000d17010809006a14243c0360001000c960403400740d110010201d024004a101c081c000d20030345c0c140d6841232608000d08542c0040c2880920429944110400c0402c0c0c001180c070b42d02040c040458003001a816074411034540d8841c0c4005003010b61701c60300e03240103180225000c40310780c0342c0040c04481c0160100412a01c12403a03260034401d0b498018002900d5002c0501058064040407011508140c001c3c8401e00242 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 163918920 1250 163917670 163917701
    0xd060e010902040305100218011404170f1204030c12060f0501120b07090b042c090f0f010b1c110603190e0a0819051909030201020c19060e04 62
    0x1561150750003802940144011107680c894540c1c1003091005a009071094052501e001c114800414001990403e0820b0341801c4072400c00c0002051020f81d502c0d44150100100000b04829012070385038529010700040026900c7c1d400303220170000200320000140550354805448510602e00b46000c4001d0a110002d0840355800e1000209a1007114140207a100f8050105c03181284c480340303404d031403001180c060b090031010100710900101e1804125140d5001d0810481e0b60340d0740e00e9035212881904190b484960303e4000f0209088151020040000c403400144001c01c124040e01c800102403d1400081510b1041405902414414501862800410082d01e001e81d285810084c1c2900001c02d12003800120f4a00002e807810082c6c0001d41ca03050561007141e1034074145000400ca0f035441c401134042410401c00300020f480d45030035080c00140f0b02c1703100d0301d842018500398400a410f102c05801c0341030180500e115540816003507400f600084070309a08001d5075030665a40420054540d42243c40801c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 163920170 1250 163918920 163918949
    0x20c03010204060c2001020d140c01090c180507020601030201120e1b0315090316170d0c03060902180103050703060320030106121101030c050d0f0c0e06090a03080d06 73
    0x40f9400c032030352580141c4600b500d07089111100c180040c403040c0280c9203900582c0040340b451440341c00b90781c210340511038042d4100c1c201400c0508403800c2d11081d101c21600064903280c10012025081202040140d01e460140312601d898100203545550511001c0d04001e00704c04000881039090388445c0f8503070b01d00015a07040988503102c12810121103146a4060711800c0300421850000e20301c03013070060100c0c601079032810b0158000846010344080040d111600121a100320000d01803000309010206410041203042c4209805001c40d01706074003502e02580100080088059010100c658084c000d0031b00180c5070b15001822001882c003504002d200c2011001c00c8984060307541c0e149040380d501100280314a82d2907401c00c0154a0350700700014000c400310130302d40318158041d030002007889065280c05030821030340e22050000d580d0041e10024003035940c1e149841c0e84649c481c103032480000042d10194a480c2e080c401003080c62409100280c03240d9030114200120707201c6a081200140300d9003006011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 163921420 1250 163920170 163920179
    0xe01050907050316031502180901030f0302070509071b0c0506041e08070b0412211d01080712150b040b031603060b0f03070210230a060305061303020c03010204 70
    0x10303929003a0050b280301e40f29104000c4c103114102c840010079240d2004030006848200074009000e50800c46c064040c07002141d13400c00060b01c80c10f41d140d0007035002d0550b0050402c441d003000303401c0415a42046018100b07400030040b101d034221220040d2004001d005031810016810049103413400c0780c0025a00050014002681c3c4003816011884081891492000c40f60384d800819546d0304580324560001c40288400c0000800c80007a41d041076003d40180a648046091072082c4081c030f840c4540702160102441010840780d50103040c88911003820915982d0030309400c00f0f448051840b41c007004454072104001c041c940c800100ea40100005080141c96a4441c000c0d100250021214980428550090303a0020742c40b90207000304503804210003a10308200491010804e501c018200e0056216250207001c2240a40c07140f03540f05d600082c0c01101c11900305464171100c490107000c2d14250360a2030400d0000c610007250300b03a0400700c800394a00207010985410b071700b0035440c08012981035102050014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 163922670 1250 163921420 163921423
    0x5070c0503012c0105070806100e060406050d050a0e10090c17060108060c0702100f020c1e010f020f030d0c14030106020706080604020a1d0411070f021914010806040e010509 76
    0x940d980d50100c1c50f5107074481c140c4120b088440440c0c510340003450100104045041507040c5030a00e9000380762000d0080c082a0100315182d01c036500c80f42c0000c1d80014801e0035030f1007a01c43e698100340058014440300340030141c3c4903910506000d01e00012039a607d07a400c10400d25608007402440744441c5d40050107151000705071240424490900365014100009450b00b03e008111080c1c150f000301002c42811400f03400b118150071a40860082d48581a41c48030580d64800240a28020400240000080c04000142006d0a20250b801554001c14500d035440101105685181c002c5810014074417410390821200501304450030302007120004000b1032042d9020030b05c10180c0b138207a281c00009480e840d0500080784100c0a48000240903240c00c14413044000c6620000c2c0c0c48010004a080c0c1c2d00030440c0d001e55071102c4001c40d01001d10070080300860410074280d12140c03008101d5502c8a40c0307030000c411a41240d04016034100500a80000d44980e0350345e001c444107410032002008140350031118503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 163923920 1250 163922670 163922711
    0x406050603070806100b0a030b0603040606080d1d090a0209060a08070305010f0b0703083c010f0b0d180605070c0201170c25020603130c0e070e0105070c050301 70
    0xc0c0d0080c0180000031441c4040002d4090017485038068080005207861951741da290480b500d038104258552641444903566075019500450048400103616031501d44110304e0b0071601e680304c1007400350482e04400d880d94103801262410038140d610000d1951184225402846010b0704a94090300103c2c80d41d8007641e2120344548601071030b88081240f6600ca040034a00e10403240306041d078000301005004006480b8918064101044010180520f040b0544940c09185903054051504c0c40c000301c2843c040c00340c02c1010380100218a104030741d150818270494030310300ca58400d64031181d1700c2e0048001d0308903130741d5a0206e049820180400c858189050300600401d14000c081c3d001544c01d400c25210b804101f03c03001d0080c00c18a580c0d92034001c2c3c0001120f10248000c1440d03102c840c0319100240941c40303c00065120b42100041d13000b00110500c0c1c0084242c00c6504070302400c607028003c1214203500019031051403030382403c14a072102d80303d07d080e114404250700141d8140d400c180d6070a2150040c003094 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 163925170 1250 163923920 163923931
    0x102070c0905150609010f090f1203090b0903070506160204091101080f0f0a0e03161a090d020307061812020c0f04150b030402060706110403140a0c030b1e040605 71
    0x1804030f07403661074401c0c064500c0c84a88940c000e01c1000418901d40c050452047c00300090305025100d183d55840d10440e102003580010140e41010520350201036000c2200c401821400d40014103001e181c1c0f01007503990015009190140e00b0000b003100b503450b0419412a0803640c02002405260040c0c038098480c034546103010f80c041603c15021452101e10746000c940704030507001c4001d0460742d80c410000d001c0c00c8070844e1401c03540400c012000701440940054801309004107210200c2003c0c140c010005103200520f060704940000107203c0c00680d002c422600c1c09a00b0a00200b80b00315190750070348151002000081c2130890010610b428590041000c00c8107000032102d400304000760b80140410740c3d142c3e201245121122400501a8101c200003558001d0300181003141414401c0d07541208680c00180030352002c004c046020010041c000041044014801c40070f01000082d0f55030380c518024050000401e042c26010000723242d40c0c00d2032506c1003100440a10380350303203007081d081407401040107a41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 163926420 1250 163925170 163925189
    0x606020d0f03020702180a020c160501080601050708030712020c010e01060915051c17121504090b070c030201150603060512030901050d02030703090b0f06010f0e010504090b03010e0102070c 83
    0x3010500780d000f8801e4030242900a0b000442c1d007429032004040c809002042071480039030a1000c04039240c000c220103403072054140b044113405400d200001d00480d900a1680d0f0402004020150015040d041980d0700010306051030394130381c80982c0281c0040d010704120042c00798a8050b406207a4101500b10f0411640140d40400035400880004810358a941c021150414030b004e0700d100400804503840380565002d2403d83d545060b004142104507071020708a00e1001c060f440c1400900d00b000120790010310f500301c034100241c080c9561007010200b00140f02900344950b02e915002454002c0d00419045210b81d401e0341c204035103801000c1d0041039a40685801551907603004951000000212900303048143c40f0641040441e440100196200030640001c240d1070360604000140546502400303a042608514042e240840005094480c208024000c004c400343d203114203a40c11404445c20342d40c0015002c11000200e0000c203006d454060b014008662000030610140542210048141e999000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 163927670 1250 163926420 163926437
    0x606061c2a0c150b0a030b0a0f11190219060e0f010e030c1b0105030610030209030706080712060608150301110d02071a010608010e060f04051f0906031101080702100606020d 76
    0x2803c00b112061184550051700c040000d001007005101e005600006141010501100c011002401d417144801403402403030011500c0301142c1440c4000100d03280c1c5900c010170a691000b01500c0503155464006004280d0303862840101880c1404031180c1d1021640003406400c50314008207661f40e2240c84040c01394080e6031200c1d00301104106410f0070710031050352a14155113418041183c246400e014080a1560811152816031418031940340200440d403180d58030340c5044800075100140711344001a849281000c240001703034101524680107111081082d9007040c01e107000c280101b0300301b0501c8020359808113500c0c00700c00060700240201c600c10307942e009005940e4110004107110a01644020072820001400540708100b05990302c443c0081042035070f8540f00021500700c1e0016118001842604903400b1000e403451403040004100c00384c4100802461a19505001c2303241e403020078100805240481c42d200c0c800c02482826403104d02c400c005095603440041d41d102441c000f04004100300c0e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 163928920 1250 163927670 163927703
    0xf0a0c15080903180d051902010e010302070f030503190204030c03110111210d0207150e030702010816050403021801060f0504150e0a1503020405030606061c2a0c 71
    0x1d845440c02103100c14021414054003101c295440503a010003503030004117001c0c0071070103e0b01c200004032500001c0d041007003400e4000d000040010440c00d240c1810706004200b103c0000b8585c1d80000e0f03090750180b404580380c0e1038096107021100d1100709010442400480c000c02805172400885003168420251040c002c1100001900e40c2101c642c12050301c0e410445480c00122030303082021101c41804a505840d0038140b18019040340c1240c00309032003200c202a150007101e41144110108500c200d0015810061079600003072401030020044200c0e007007410100503240e40600e041e44c01442c2d0051140069000040320a4044407003485420005000520499141d034060411201600d01c4a02c42c445845550502501c40b40b5006500c00e401c440704e00c0c40010041c032904400107540b075031550301580c3c2d60b2a00301014545080a4a03580c85400c0401c24200c1c070700c3c04150401804107500703201090a00044c00c42e11406174440400380711030754080e96200903850f4095080c05816104905008101c0c544 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 163930170 1250 163928920 163928927
    0xb090c030109021305130803011d09011a0103240b0d05060603070f1803060c02071e050102030a08090a05031207110703050601050415050301020a09030309140a090507020f0a0c15 78
    0x3a0b00301a4110098581e208004c13103113030b0003081e88005080c02e80b01411009503507002e01c0303a009902c003041880b0f04051a150340380d001c05106800681c0000240202124201c6041a031403c050105040c1595003800c550112501e0341e107c0003452080c903140380c6081e0354a034102d00c0c542c03080c241c03681c0c4245448002200c0c0d2800364180c03402000305a854600d001404c041c2903a80303c480c242c1208140440d1000000000c000d03010307030440d14059030b014140281c541405907030500030b40d8164140728820306400b40266603000040c3d400b104128500005c8948070002c5c1181400445840501540000201b000d136991a0310281d44c0a40d0881d40c8410340c015640301d0382903c44101e400010032030380242004000f43e18168004c10078141d80d5601c2481119a5507001030b007264020709485011a046000401c10305802401c00e42c000c0c0000849140c1c61000400025141d84850040c5520b095481010640503442000f0105080b06004216a009421410024038509c500e105090300d031084200c3d0078000622 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 163931420 1250 163930170 163930181
    0x2100c02101e03020c0c04050103050c01090501030e030a14120a02031e04170a1710030c0b0301060c15021204030e0a080304140d0201020a08030103080a0f03050c1210050d0b090c0301 80
    0xc2a1100311558201210b044000e0f5002842c03000d5a8030030103800350302d541c3d51071150034001c1d442800101a20380d0500005001030000d5805941130506d41460410010340c00b000b25088c58990740b0380318420400040700410107000e410a4000c240043c6010010120b000382e00844c0a020082c2c00c15058820341070410f03003445012a8003d20001c10022902c00800c0100c0203440c8048140c1042d01450302081c0a0580d0303140201d45002407031400791010400c0c401c0800340940509102c0c0500b44c503560611401610450010390010000f0784c3c000134284440982da41a15440006a0403520780760425080007032001260307a40003845101c0140c4005168800002101c00300d403c0310250514445c2010200a0036648441c2c0a9056000c0d41c00a00001a8404004c50285118002c0540c64032042d1000810342800c1008207000e0500e007609024405810320300b519200c09002d24961501d40d01c642520348004400e41c0141d811810b401c48920820042401c03440c850b403a2134048400ca10035000c2018241d52 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 163932670 1250 163931420 163931447
    0x6040606020d0f03060803210703150308033d0503030307020c060702060409140708060a0f0306050712020c01020c0c060301060813060e15090c0108190209010c02100c0210 75
    0x900000301810181e0003001c1003030548005040001d24603942d04006d03030540d400304000b075007407040302d104580340d040007104c0d0503410807100c0c5420003000046001001c011846800003134120400440015a60f000c00d11080540d603000402545040f5640c8684030f280c3c449400c85020340b01c00b080c03030228003401e00105403446440c06900800354002c00038180080d40d40000740c01c0c4c0c2c01c2841003001140d0342c103076030003130b502004018078000c50a840c1c0f05500038060200a000070307120b201c0b008000c010300b1082c240100103582d0048800030312510745400c10385426150b10705002402d40049181400f100040d03019040d114010403e59118060380c204102451000740184c8011a031a1800300e0407500065030301c10b440700c1c03042c0c0000400f8a1b030600c07194600140c0c4800031300e10b01c0001e010480550310030300030350201c04402e092130344a03400d00480c0ca160704130342c0d074880c06041540804e01401581c8140c5812100507005441c0da201d2107041c0000601c540400e650a9024a104281c80c40c0e03401d106c2e44681d940c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 163933920 1250 163932670 163932673
    0x40903020c0d020d02040501270501060e130e01110903101e0b1512060f01111c20010e0105130c0302040c030603060f0905010e0309060909040311030a030e060604060602 74
    0x2010703100801a2218107038400b0b0340c01007014180500141c070b0300d01c80d10b0f001c2d04445404000301e1052905d001200000e0f89011002c50b400c1c00b00411805402c5003c0c01c12001044420004050511072914000c2039200c03e6206150700348204400040c0b000001881201c00503429156440171804540d401d90303500184801c5107004555040c4004c070403a600080b01650010420041c2d0200261815840d41007009410030503040d1400b44a0146404200383e1840c40081c00c00740600803803410100d848000c1c0b0309085031030583d0300b0424a8158401c2c4802c2903528610f080b0302d0b0795070405800d075074001c28001020800640c40c11001c90100c460200c5090b42c102e500c245078884180c2194240300c080c101d203070050410705d40c4809003c000110701303008003103030007000013400215512182005400c0d5044000c400c20302e900b0402101c2c1071912800c0c02c6030801c0c0710680380450701307880d94030b07085034460707680d281c851440e000100781201000e515810044040a8400840301070351520070401084406a20407607016 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 163935170 1250 163933920 163933933
    0x90609020f01111e150702030307030c030903050919050a060302070c05180106051c02070305090a09151205030c01020c03041a031312030b15090415050d030c061b0c0302060604090302 80
    0x850000d5100800d480c441c40040c0c4492801c170841504103400169210300c05a003000c4204000f00740c0c18400c8040107051842e041c050000f0385e88000d0b05c2e40c8940b0300c1403801403101038203010005a000b034554008040c00350950743c3c5181e0700d0340c0c010000d40058604558040700081c00003500e26009215480c428542103c41003030b44d02c0c1c51401c0e90b15a00000c64108505e500340c1054080185034806042041c2c080d48580790741d020f40e401041050f10081d0404401075142089400038801d4510f40d0304296101c014284640380b020b030512030300d14081d030302c010f90080d8000a1120002000030014000301c548046031102007800c1c505190040b404100c50003c2c50781a0300780c0ca040417807007852b03080000d0f105034200095109110030114020560740307404a0345078880042c3c014a0780c24079208043d020424901c03454443c504000004070030000c1583c0103402c02c505044e0303810a10066034800d82010543c40c0d0115412520b4142c05040d030380d4070820075400342c004c0500194a80c00c0c01c0c01070070042541640036014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 163936420 1250 163935170 163935193
    0xa1502150618011205070503072d0609090c03020412030e1201020a0206070c02010e0a03060203070215060a030807020612150108010602060609070f050c0307150525140d090609020f0111 81
    0x44c803041c2070a440c00d2103442c43c0000c960f10180709200160003010308420100080b80140440760b82640d564a412018284080048603032103111001aa1a203400220702808120b204074041c2c05160011051642c84072050800c2603000300101d00c1961042d1482d4002d4078117413240300c0c05c0340544030148000d0b8112100042c80c40707100e02c3c40710088a1050400b003501c240c43d1004a941c8124542044900c80d50010500803207030b404101c43d921440c41174021041c64a0400f000c40d4102e641444002c0c02114013281503011981d8a6040e10b03000350705200602c2c4070381f034048011011240a154011701103140b10001040d414800b1420754030581d005091106507494a08048950300114610742c2e003002000c0c041c0d00c015510500052003414003850f10303826818045107520040742c10192080703007580b210340d00c00314094602d2a6110194040740c10046d100c8245289030440d01e2042d1802e00c012285040510b504100f0140d2018212600996011400070502d000550305030070307100b000c3c150aa008188021 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 163937670 1250 163936420 163936439
    0x30414090612060a1509090503040302040f110c0106150c020918010605060c030c0610030b390d0606081017010902040e06070e0109031a060a150215061801 68
    0x15003060010b0b04010040c00009040c60070310100341c801c800300a40f2204a001114a250b080300c02070085c1280c1005411314030750300c0941d01e100f5440028003690315903030320341e407040090b038005208000f204543c40d50b81d6002d051424002d00a034064988114207000d90318007124440c0c4001a495a4064002015901c0da408640c0205009040742c0c40d8a46d00c0d83c00104080c1c0b00c5101900c007040c10040115200c80700780140b14105040200311000d0210881e0041000c1400702a640750408465000c6004000300b005200d040507071012034401d125092a5814180d040c5440d0080004400050040200e5034440c0d1040f210420140c656020403d1000c409200010410074100e1121a06100002c1c81d0707042c5501003025100e04030402442608400108004540c1108840030541000d2904428880c10759507a90210000700c2d05541e020708903080025555290481c416004d0030150310162007108450b90025920b58880b443d0f080e11682c0750021500c1801e1425000031040c1c1c1c1c00e40c11341156820008041d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 163938920 1250 163937670 163937689
    0xa060803040f03060e070b0d02120105040c021231060e0316141306030f170f04090e031605161a030403140f040b040905060904050a030806032103070f02030414 70
    0x5c2c4807a010b01d15000a5101c000d000030458054182405030b2215000c05030f11020000c140e110340c0c0179030b007044001030b90705074003044110300840ba00f20255241c40143c1100c0c018203085040005548141c64441d1b41000354190800d421100b007595030301c000750340040038075480d01e40606950340101c0c402c01d810301c07203070300d284c0103840841502401a580701012441c824041d20803641c426250104039440400610181500d400707102d0f1b04901100d1b14000d845600304d00944100d110b04e04442e0303a41c01c0801c030307602414412250349509070f1a8000301d42d203650401c0ca40301d00c040d0242d1000c111401d0000107403912030f0715907502000400540744d815079403180c40a484004400c00804149030003003002c150007240044c0030307002a012110109846030705166108003124805450680b141445a0410000030000209004071561600d000c150710388800b03000c0f0385410f00910b0280c03528145505002d0198140303d018620131f9100d6515a11000c61303c20b03050341c49118601500e408401c1c4860302d55098109070004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 163940170 1250 163938920 163938941
    0x21201050111100f0f021605060708130f0309050603091b0316031401060803040f03020405010905040b060103110d02070311121905030907050a0306140606090f0d1a0108060a060803040f0306 83
    0x724aa07500c80030454100c1c2d10060307c004207202800666820312000b0808036a004080341000740103802c00d0341c42c080810810301e40c01041c070303600c966500040500c5200600028400602500d4603828500201c0752107a000701c41142c2d00d5002c2800183c1d861400180c641080020301031000c054a08546902034884042c1050755001e640718000015000c00400060004003400180100018110700c1000305462060340040e101d542050280030110f03e204540d25000442401c3c00500301100c0c0210001c07034054101d13480f520a00c04584041455001603050001c0842a002c0c1c03866a1174402c0010320750700a041001c458101e10010040900e4003440046410418070412070703280d40e90340d2000980200710b13a00115804e6807109218500c0381d00305001076410610403140141000300e9030010622210680f900c1911400442c1084011b0002c1100b00b9800c01e241105048802d41c0c5400d00c80350b40d01415220518442c2c41c10400040041000c001e44082c0e0310324400482d0900e145840380409021307021503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 163941420 1250 163940170 163940201
    0xf05030a060b07260f0405010e0d0209090a06050606030705090d0f0b04060204080c040b130c03060302030609030301050118030308070c030225060e040506030c042a0302120105011110 80
    0x50100b03840036104060030f035591181c0224070200041c1060100c03411340900700c030182c07004240401d11001d5407020035541605c0084c40e00d004485110000245000410310010350400a201c0a01120000100d5002d001d00d002d0981488161201c1061003805d11003182c10300300243c0c003405003104503d040380d80844441c0c000c00f0780d40412401c41e19082e2200304140c0b022104242d0004003001209814442406040710860b0200246486000850b059041c403110714403040e80c1c0c86807100c191500a038002c00185401404844903071402d03242280c1e4076803082c0103050110b5010049004150060501c0e5019254955192011a00e80207410303110003d001e00700b102580510805c0b40442c00d083c600140b0b440f414080d0000c04d80303280100140588071038103007040c003640c1004100440c54138001010021403006a03000505220420020881c0001d4000f18907040802d12a180c8a11355268010341403481c0c00c00e41200c1c15981c0c403401902c03500403d400c0112507401403e08040d84182d0385d40030080303500107a130 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 163942670 1250 163941420 163941431
    0xc0212090a21120e01080c070c0611120d051b070809102a02130e0303010b070c050a060e0f040e0c09060303130303020708071d01150302070b1905160f05030a 69
    0x3c1c0d5010031400c242104500291030351080298035a803041e015500502000e107a1403a00000e5242c45002c029280150000c0c0500c000352280d0301c5070308000c04a0343c81428015162111032004803480600b034141c1e143d0030080034208260201e05a0041162405a0b102c807140c1d107070507220340610200f0900011007a05001d0201c044001013070402c0b150b84103480b40031982c2c1c0a070744101d1040041350346800f00400149031038108101180d04c00001180d05403082c0d080c042c1d46801c00d83c80c04000c00c40203504100e0304050f05410004409402440152214004541581c5d10510550a000844070190f4003001e40f075002250b0100c0b28200351a0154101d007024086e03e10781580a41c000e420800103a0003200140d00c04007040084890a1180c40040c215010080d810148001e075001e20583c0180125024032140719403c0e005d85000c1e90488080a50002881c006450450001d8400d8040a02c4201c4c085082c02d00003200942c0326a801c00d01120551103111218014000403a00c03600300802141c030040c3d490 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 163943920 1250 163942670 163942673
    0x7120b0a09060b0c06151309080919140105070213020307090902031005091509010e0c1323040902130f0207050105040f0212060132040903030c0212090a21 68
    0x1d004003000760024903429603813007007a103808918083c00140040c8002e0703500713032045103180e544c60510980c0400d400130219580240381007800544c407031003d0066200901ca010000c0c4940c18214007411110694007940c0c089a2410040d2035a20400500961140c01142c04103240b1403107501030742c0c120300b051921075400c5803181c4d00d2404036841541d60460501680070200300c40d160515600d980a00383c1c00b54255003100c0c510102c0c44070581030080c0740340800500c000030800305044c020343d200d0303100c902090001955030796030031817010300e400b0302c40b040c0e8600c4080c00350740030704040c003072400407550207800044e188140245190041602a07001c100300d607000c0110340b002c40c200b406480d01850081c03002500014241c41044294091009594110740044004100a02c0700314042a121031a551a55604000c00710084911000030111168424945001c443c18964913601c81d800c0100c61b6000c49070841d6601034001070501400f94110b510100c800350600141c0007082e00d1103105000c042aa84090351503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 163945170 1250 163943920 163943939
    0x1905211e010e010b063406020301060306050a0b0a0f0806030c040e010203070306120f02060906070b1503070b0c072d03080903070f0612240306050a0501050907120b0a 73
    0x1440c14084503034407070050405440d4288103008541c14116045403038485c054030540000c01a07030f46d110515240380006401c0080040c442403c0c101c1c2c4c01103003150781e50303182c4401a004003142d0003502c0c000c0c02e5411020035030480800440c0c0e031103c2c45441340d00d80715404482c00c40e600300d070081210790107002d020844902c84c1c0ba580185100c00a4200002d03881e032a00b0f035401400c8500d80e90205004e121442a03d0011806444e080e0300341035010303074405a984404402240362442000340080905840c0002c010318102710781c5820075141422030a0300c52469494103046c2c0307280151115030001727400001040040400b042044805503114540c819600451520991400015540160398440c0000b415030000c1c501846010084c025030880303e8503960410400900d2580c17041c2108035015583c2a00801922104051107003a11240c1c0d0703035000c103d459203096809013005488404102d07003000004104d81c0340004902c0e03ca1481640c0d0034030105200050780d00074040c24201d81da00000d8100c80030400014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 163946420 1250 163945170 163945213
    0xa120b011101060b281205040807021002010b090a1b0c02030703060608030307111209010305090717151e040206031e1509060a03020a05210d0c02190521 67
    0x2e0413600305450f070125208006511804400400c9049601c0c56483c86483d04040f585501e2076035440c1c0000e1a986e01c2c641403480b07100b40e04000c0d50201d0701d10420b0002650542008080030b00c144c0b40c40c0201e1300d855549105944048503c046a54030115410f428a4822900c400906000508440c8126602d449460881e4550b4210116507000041003140842e0024404e1844501c210020701c011200d0304c010b15594010f02844c9410151144040780b420141040041d02a020914011100c5410a171140355a200d0f0041d00c84002510a0005484144c400c0c0203900d1701c03030041c040a0302d10f0f5500c0e404c00c425588000e1100200e0b014541c030800b004d0382807000032403140890b030143d0b20740e00c007603c0300300026150014102031088030502014801a2903800012088030000d480c030150200d802014210308252114070310a1900c03d07084c001c00441c0c0c0c080e00d00c0c0c2c0000d0007030b2424100380910b80507018280c40a802101d82195203001c50303146e5880640d5075000340700c25480070350750102c006840d510b50000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 163947670 1250 163946420 163946429
    0x10e01140d0504021f0206060d020d060f02030a06080a080412020a4407060e0102030927090601062a1208090d0315050f0612100e010b0a120b01110106 66
    0x29990340820085003001009845006005c410f00d041c0303084003c5000303586e000020050b03030180750984101c0c411500c40e100c0d001c02e180d0307000e841070016142c1061032000131b4204980c400a8181045030000b08501c02007055004903800403456840c0500304181c806002038080030480e0407941c000f100045444416055412042c02e01100340701140c01400c102401032880c01e080074001c0c180641800845c0f50028040027243c0c00d50038a8080382ea002401030381540030312107480b0307041451042c80700d103501c00140080c4803405c500c3c1d006409a8807a1851a0740d241d40900031800410b0030303d500703020f01603007040017508541c036044041400000c8643c4c0e41301d072441c1106030501c041030859043c4a10b10b402800300c0301500500345004c00202440c54100400f1102038403d0301c4c0107920b0240601c0140c6c07030740c000f1540480302c100c111440714180300303603865074141d058412800703850740031800442c44c1407820048410700b80d060755424218090500c0620028521302c908079041c400007600c0c800e0309500a018400092 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 163948920 1250 163947670 163947697
    0x60103080a090e040b190b2110021206040606030b0d0602090604121202070602060c090d05120406020d030506040506090621060a0f1802010f05180303131809080306010e0114 76
    0x40c144244142c0f0b101801c6c52240c01c0460400700c4902d503a460f0700c0612929a000c031100740817500b11070402a810482100c0a4005541c00054038002c1466000012070040310309131030404c8102d0b83c1e80411070403682d600321040c2e40300707104800c80340102d4102d802406071013070010021441c1c1540d82034660101400a202102c10070b10302040301e607000d07405001610084c140e50015012a28107a010000248a05e01c101e84c82103041c00c1d14001400806c000540d01403200e0120f2580e220307101c0401030b40e02c0e521207008000190805001951a04090080303a008440c013070904100f0391243c400b0003200f5490b84511050942c81c404442d80750f00004c20440f401540e00d490001203d0300201d21040070f5940c03880c85010010001800040140d89c84400d848000500740ba0650310f40c0018081030301c04074010640c0075494071010030454900c00c082614802115800aaa0750706960800244015030301ca59002420030b05050000890550103114031024400d014503020303183d0b0340701702c00d400a00c0d0810301c00460f12 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 163950170 1250 163948920 163948943
    0x40810060303031503080a050a09050a060503012303060a11190e041104120308042108010905090607020a02100905090f01030b0906090d0309150c1d0a03020102060103080a090e04 78
    0x749034151142140c4900c08480246030b00f170450300c0d001064400d1210792420400b0000301e2000b01c500c40e02010380030b0b200040c51402d0f502e6072000000d0480e0000e0040e071003441c0148002648181030301100c01500100900a0200c9030394268070200280745442100180201c04c011180e00c2d0040c2c500892039845180e1102041010b12205000032100041c41d00d8802c0a0204010f0001c1e0140e81202030b0300c80c0c0d0500d00300140d0364032450000c01c08150f660b0b258081001d4843e4200145802c4a50a8140c0c1d4038843c00300310395519040f886030381384000e9883d00c0240c1c001869030405820003901e008612502811f180e129150fa0b080030900010046402c1241c2000c010014002c20440c041d00321f41114004004140700d040c411946602c1d140d400365403500f81030f43da810309410003040311241c50f0075013150342e0100010f445147c00944400d005490701039400c080b1240310100c82c41c00c08444070a403501a4002e107943e81c203564401945070b010070241030600c030702040b002410f003440003540c80c0f1403480380c0c007415a07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 163951420 1250 163950170 163950173
    0x307110f1c02010606020c06030604060b041211011d0118050319060608030708030f0702010603060c030b0f03061b0306040b0a0308070507091e230a09020112020307050a0c06020408100603 82
    0x19a601030a01c0e03604690409030100130300390340010442d20301d0b07404070307034080c1d0341d45452000078020555680484450381002c42d0005036451818007141e1518040d090030541005044c004480306510300b400411010006c20700d0b941c5d2548135480c2403e64410340c0c0d40110005403a00000303440c0005210a2089110348001103104100082c01003100078030701c9900460502c04159143c0341c1c180001419080041500000260002d100b504480019500729008100041100700300801802d14041e5181c01003807d490400914140019600c1c071448500304542e188101481c0350180396030001e03000075441501c900608096a0b20030049030f0003184900d001c41c3d501e240d0341c6041400c14515600811000e450580080c07007422041d0b43c11150ad072000207001403140c200512031016681c0403400d0f4881d00050b1010042500b03401d81c008400349000741c0362000b500d00f90010920a070b00c0101d52031800074001703126030780d1141d020321200d250081c4940c4016003010b0315218500e107400c41c0c51240400c480d88603c401c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 163952670 1250 163951420 163951453
    0x21030210020c0303041b0306150e061e04020705011b0206090d03020315150d0912120203220309080303040b0f0a020901020601140103020c06090d021219050307110f 72
    0x10580800d00c40540c1840050710103a43c590100510140001b011500325600901001010f0809190b201004103d444007071071450100c00154001e10001c00741c88004141d11303140c060100b41e044000b00703a01582426014041c0710180d00004821180780d0b403039003000c4094844050b50701440c00410b0780203065600e07064540520b04900390001400741841001801f460003c951040400c000040d079a480106422141d031000c688104081a203200b40307844144801c00c100060030481e038500c580d5528544901300718000b0200d100550340c1d400303404402129a401c1c851500340944405000f07090107150640e40340841c03170656004a80846103140880100310302500403012064000c032840c0310031070400100c400040e599072010300410f42843d04009000001d40c3c402d40403034000028210a0b100e0508000d01c04c255138081c21080c107000750203219a0820040020020313540b400e08110114014004200019241e40e80050164030400210f014165507242e01089009107140050004084654000c2800b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 163953920 1250 163952670 163952683
    0x60406060807080406150509040c05010806010212120603010b030a060b0301050c0705100b030c04060603091e1212021605060f0106020d0909240806070e0a050105030403110106210302 80
    0x100c080c070040c00144400140e2044106030702c0760384a9000194003c0e446801c0034000710907800582d01c034900a0401c4100507400709443c040b2039080e200ca0744a510780200582c1c0320300a0441111804006024240901108081954002501400010b0400940c5003c2424002a070509440c41ca48504802005090900c10568808510380c07000b03080818030303078400341c48101d510300c80000c0710384444076240c079035a00340040150403d000380200005990f0782c06c05070190541e18000e0355103221082008914051034400304c001c403a031080d01040385e404803020585003007486080c034040c8241c1c24415800080030013099510b58030300a074000d040c68503182c0307109000030005070054008c540181d00c2e001502c0d908482e203441900c40100000c00c4642810701d12640801c801400e45003191482e0000241100e400300c3c1c014000c80d0302d03030358200004641105100000a01b071042500182d401c0000a0100b4441d2014000400c0c0d204008a01a0390300c2c035044401c101c540880710186e18007041c2da50308068040100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 163955170 1250 163953920 163953929
    0xd150207061821081915060f030605150703050304050c0d0b010e070f020606010c0203120a030204060f02030403030e040b061605010b10031a100203120108010204031101050903120c070e010e060406 86
    0x43c030741c140500740004103000005404c0f8030155101c28007040c20b4440b140c020008219820203980c4d06140e44040041400030003040c00004246007802c04540b60130405070000c00c1c02d0190310342901d0101d15613011a10380d407000303200342c5040c0510282d030620390f99094100400b0900860401c00b655044c0303c008620100b000d003a82003030141110072103ca00f40c0102d03031164018002d0170311400302c000701e0000c2414555035110034854401c00144010348150140d000d4401e40d03a0554556140c50348050040c0d13624410341c0406404a4440740c030402c05450716420285410700e02074181802c082c101406450030424120084030b060351a10094901c609140c406a581c070001361400340480322115120108404448418501454483d034641400c90b00030401c9585803550078114800725a0741d90101d9000750801c2c00203c992080b1080b548090f076105005403985100010040c0c00d150003601e0181c2140e62144001505070302404c240090004078060016008003103e002010003480e02908100c201c038503a400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 163956420 1250 163955170 163955213
    0x30414030a0201141305041517030403030816050f0a030b030c01030b0d0f021c05060108120304031d010207090212180d020d08060406050d050c12030301050d1502070618 74
    0x225040541e0340041d103c0c004c11004c1e80890780d540f450041e151030384040f0380c001759002800d06821420081e1303c210120304840c841c085e292a0b03503501103403041d20b81c0300f00c0c0302c00740010b40004040f8100002c500301c50600707860142404d502d44844080c5509454000b54200808240d07610900034080c1003e01010031410003d20b010400081c407a0001002c10609001c09403e84194404030130454880511901421407020240d46904481d41b030b105a40b03607001d029001850203620800c07910440c0100503240195896120708840c0c0a07000802e0140c41c3e0106900e50440c4a044000520110f06100a044944190602929615003143c40a440d0940004666200d0b4044c0085030742c09640464031440d220740074508101d16448100010b4050510b0340c02c00c40d4401442d0340c10380100310001035500d071600c0c1c0035101110090341114509850b0301003449116008280f008052000440e46102d01421803010f40d80142440001d850321812500f002c40980c82d005004914401403040d940341c5095490341156 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 163957670 1250 163956420 163956433
    0x1e0c070b010506040f120206090a0f08070605090112150f06030c02010e0304030507060c0606270b0d170703050d020d1d03030c07080c010e0a05011505090c090d030215040503041403 79
    0x91094000405c1d81328186200d41540061400c55035411b08446076000018610702c81c06456150700c0f003240303c443c4a010241d00c1400d600040c00d500690036100300c1c0c9416150350403c240082c14000150091849400812108142c0420511141005100074007000c0d0303070000768000d140b4406401c4403d505401c4407680d009010410000d0000070301001581d80b6482c05041c00080fa182010161031544c100e00e40050314000100000200303628100318040302070400303100d074030724400c11300403c01030b2000c001e044602501d140f6990543d880f0004c2c160030b40300b0310700246440c0c0052000e004980120024100143d1140401002107002c50017094040078072001641c55410281c0301030000c2d110300740004000c40008100b54952103004c1d803103055040303071140c242e604100c100d2503d180200280d19005032442590200407a2030700303080e0450b41c410031404d0324081c03400792001c080043d8201e030320400324114802c0e0a01c14080d40041b869407401a4410300007961181c0c140703900902d202094003c02400f85c0e03c102c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 163958920 1250 163957670 163957679
    0x21050a0314010b040b090105070503070615050108060f04021c0203010f030308240d080c06040b040b0108030c1009050a12050703121109040f0209061b010c020a0215031e0c070b01050604 81
    0x108580440360841c00c1d0954400c80d000c0141c54034003441002502d40cbc040882d40c003041c0000b0f50050f80e2200b0a000ca41d00c4443d07100d9005542c840c8040c1c41e5242c015102520950a40c20683d00030036100e4400d00104041c0b032404040d103000e81e0f009810402d94108a88010403c1540201b0036542000c060840041c1101000307202241e001c0030040003500c13070700c00300306103605110403101180e00800b4140140c03840c919103030506011080341683d00301c030900d00d5400001044100801a1152404444082c5c8501c0790700707202d400041c2c0780149054900b40a90304480e00095a80c242c0768207a15056101d4949800070703428082d0214201c44c07030b039180301410001e44031a41c7d80070800710340e20440c0031100000e0f8558404010002805150350071a0030030030000c2c0d210081c101c110380d025440100800248100e803200442245c495031425002504210320110348002141804061940803004e080990640e20303c50172440c8041038241c0e020310250000041002c00d106010304040d01401050350b44500c1d01c1e240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 163960170 1250 163958920 163958939
    0xf140405071205070c0c0e09060703180303020315120604030318020f011107080d1119170706020c030711040f0504080406030207060608070305070e0a09030905090421050a031401 78
    0x4680590000707542d0f00300141103280114481d03840c403174200d58038003981c5450f400d02e91b034920020b480c803088a00c901000255084d00c40e00401c4c07104820843c501e8015611513070260b020350400781030364a400c41c99481d15151629400d0118996803403880c010000d034100350501400300e40c0d080c0803001351074245405180150700d0b074410341d200c899420b00c2c00c825413040000e000c40c00c008403608900b440d4000d815000d40307001d920002010200200c0401c3d81e81c041010504100d50440f0004024412501c559807030034a0030311000a040c1032406850f01524040c0c5d03240406003194021030f0304540b90394159032020780350b0a00d8400d46120014101c1c040000342416200c400450003940b1480c0d08141c0c0004100e02080a2600700c030000745a0303401101c128545a01d0021b865824a006174102288000006490a2054040c908540381c2580b5121416400d00003445040c0c2c0004005549060b4144080d0440c80c2030010517100c21400d955850780c072403503884002030523034000d5049883d00360f100d1001804100007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 163961420 1250 163960170 163960187
    0xb0d080418090c0303120902030609010606020d05041505070804080604050a0c141f18030c06030e030a05090f01140a0905030105011413020c01090f05030d060b0a1b03030609060f14040507 82
    0x101820300307408016030f0301180c0011f090130000c02501741c040c003c248942014150802020f5988540a50346140420171085a40c2e0141c0e200d9240c1700d42d0441d0192a00c18050700c010124140100c240074030b01900e50126514003241a038040b40e9076407000b80d50300c080c09000f00da05005401c10103801c40040c521040024003040000342061000760000c03460000b954014440f010302c110484040400c80d0b41da0f420310001c04000c51040c500424200f40709070100c514084203d643d01001c98075554106084042407240803c00b215205040c8400d078a0040c03801d0b050b0f6000f4210140440d40c0d0327000020b00384020705080d982c060340030b01407072000e01044290540e215505a00140a50389006031a080c0c0c1003c0c00c0e015003060f4a02510400a003014001070040100080c03004040c01302d024410540d903a45030140b03c1c071802c0181070010783c1c0030400c401412003014081440502a1402003801502ea440342c2003141c905503c0500380c504159002c05c01202030500c04004820225800c105a01d800c1001424000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 163962670 1250 163961420 163961423
    0x9060504141905130906050702030a080f06130f05060f150d05090a080703021b090c0306041a060d0213050a0b1c06031505011e061d040b0d080418090c03 67
    0x14604041c1c007211030035040b000d00401c00140b400181064811500008020031481a1002414240041c407100c1c0004110b960010882d0380c0c03c0100e56501c0c40900d401180502026800410140450140e646074080c24402540d034200029840c2410010401e1510800000343c0c0200039074070104a118003580c0036502d103031002c1c0c000450756a4615680609021100f98011310380180441c0c080145a0300041074001350105a106903d9264400308112004c03108a0300855002410400100c1c5401c003900300000344c42424000141c0c0d0365059000900765000082821021680440d003803521841544000008240948038003ca01c0c1c10046021564419140d009038404e14600701c802c0403008650060000f2b580200340e05d031844100b00d20355405004284981d1200c100c20b400712240690300140580111420358640c2e00c649039402071541d180c80703640c0d81c40540c090340d2140b511349992508003186080c0d40c0329400341650340d42000900041641900984d035030300c41c5403080e00341c00900c40903468020303207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 163963920 1250 163962670 163962679
    0xf0103030503071103190203070b09070b0301030837140310050103021c0525020d021b01090e0c0304210909020f09040f0902040501050411040302040c02030f040f05010906050414 78
    0x30300c86244c1c01ca1461040c1c2d00c080d100680500300c00942c03142d0100190481c223114015400d51501caa19402e076a03001d0b0381c02481020035041004000160a4500030044207003070048c5803c0210810f00000089244009100c1007441d803448400b00d029404649200c21244c41d03039400341035041100d80b0321502107040c01220306050b030018450083c401440300e07144da10b2010000a00c100d2410303d002c291908480c2c403144110111001400340b410780041038001c882d4040b0f0b801040408009080095101e0700d440703a80d414007403100b03400f2488601801c1d40d10700c58400320301007a550f4101458184c00c0101d04000c510a802c194120f901d44480d4454809422070318600000750711080f0075071204c00d461040c0400103601902e41210101302c240203802c00300403180201c41c00c000580e40c52003840165040811a1001007504002c02e1006240550018080b40c00500c102da08200301c03c581c015041d4071070380102c189051449400c000365a40654080017410040c41d242d424070f80340900c1c512407600ca003548140308 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 163965170 1250 163963920 163963937
    0x302040f0e0405010228090b0f090d170a021b010801060206070305090114090f06011a091306080a080c0d0c0221010f020a091d040c05060c0c030106090506090f010303050307 76
    0x500c40250183c07000c910000240e031b00000e480041420100e1040604000411031a200c009034094215080d540c45d03408207205c00d442d05140c0c908200400c216204201ca0721940703903d0f03490040d021200600881c14094006111000c0c0e07100b841540c68070f00914030740c1005500801404a0341d404510b10b50880e802c0d0401081540343e182d41c0c00d014107060b0703134992044100c3c0b07007c000c0d50319000100141c14200803801e0300c016989410a25a03241d06000350400c07040010407031003509003030081000102040310480064181c1d03d0f010030500380078411100350b0324510040f0309a582d003541400005906455070401d50310284190303010540c00c40c0c100003902101002e10640002d20300c420b402c11089154081401c650780c070347c144000342c00e952440c00b42d21600325411060840c0b1101c5008250700460304101001011841d1004019442c2c4c0441e40002441c0a041d03a07d503c05c1d00d007402840064048841d0104640c80c0c08000d001c11701800402c10600d615072a00100003107138210003100d03000181e80ca4550b01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 163966420 1250 163965170 163965173
    0x609061805060a210209041208090f120a03060b0301090203160905030c061809070206150103062913080d030f090b07110309180a2004140a0503060a05090606010302040f0e04 76
    0x911855204c40a900b0419000401c010050303400300c80c0c4810740d05500c0d442c45584a41b02c2143c0d865100360450344142d404600300391400109140030302814905843e0105081707444240182c1a80c000b82d0011900940101c284903822404904000d1481c0b42841c1c09500c491034500001ea6440c2c100303080c11b015003000500c203101000d81e12959034220301c001d0900d228a05121200035543c0704100d40040d4466100b02c003442d0590b2003801460201c904802a1807019109035140001c1403085194040840e0002c0191311946000303407181d42d0040c2180805401000000500507003039031404020441428544006040043d1008442070b4204030315140554500384c00c1d0500607e18455040d5a42d8490181c15000340e41d035440b1114184150402c000500c8016400300034414440c00032640551420001d000a1004443c29034001500040040442c0b26440c2c0e80e9000c00d003083c2007a01d00d8030215440d0010454041c03c10441c80c0e81043c02841c045240070b11341004498111014041d4042d030314040d101140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 163967670 1250 163966420 163966469
    0xf03120209090f0402032103010312180f030203060a020304030519020f100902040e0703020901140301020d06180c05190806060c0303011d0708010e010905040609060609061805060a 79
    0x140510005016207455003002d41d0f0103060f808040b80c003203102e03206900b04c0c10800319000c0b0703001092010324000241582d0031940da51040d111407041210421240d0303c040c448e94403040d00038500400c0403003080780c45142180181810000001c00c10007034280108240000030f9440340403564012a403004d09000030002d02c0e001c070b05040c12503e0484e49482000c03a9400b1180c5558060403440b44216800c10052003010101c986545031031101941c480310410040218100e040c1c0540042000100010310340301000c4100c400302c50046d0044d81c981441e100d84655400407030b204244c2d01050074203003607050444922151400d40d904480d88020070116801041ca191110010b49090761900c000780d0352a0341e150300c0000d017611040803a1000581d06040410b036514000c1f41d41c00e041e100d0f01c45c11941d5a03820450004003a007006441100c502d9551820440480c0007441490050100c1d201c010030b034036243c546d60410960140721000c01c01c1d40741c40240310050b40d42c5510740302203030707001c160603910b1040b02e05521 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 163968920 1250 163967670 163967677
    0x402120a05010c09090e120702100c12050304030215040809061c0603080c060c1303060b120a060509010b030309030601060c0c090c09030311060912090a09020c0a0302190f031202 78
    0x10495030070845031029881d002083d500c01d9405904040180d06c0e40e1701c0c051640c440803011a039110307140810480000d42454060350f003d03d06d0078184903080d24540d50741c80d94a00f0340d9072403035000101c010050000309981030284180c0b030440040c00301060b05090b22111120300c10900121320800d00010b40001e51402d01c21a03215903140c954080024940d04d0a00c1c0ca500d902001603202c5074041e41d8001000c017003590050b245040580400800100e0a40ea240801451200042c1c0d40c4814400c42054031041b0406c03150141e5441400d02141b0f504000c0c16690a490080c804648203030000d00910b01c298800040c1e00381101d4480c07809060601381401c14000340e45168006581d09410a62403002d8280c001c61104205c83c801c2e0b982c5180180400911900c0344810785090580d80c014961903144001a0805042c01e0b020080088920a545240c50002c0303a1211f540e07503030f2780d4100070201c4061580500000d00904207041c1440b51403002c1c0d41c1c50b0008110380e10002020b003c0c0f10044c0c400c444a059069 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 163970170 1250 163968920 163968923
    0x612060e040501141b04090507031b0315120314030a11120702070506040b07020f210f1c0f081003020405070e120d020c0402030903090a0b030708010e0606030402120a 73
    0x40ca40c0d14245814030314081c00041c00008540c5400601081d0b820740c0f011000800e5450100800f410503081200503130160401030f00325410140c1740c0060742a107104035861800020055100010180611014500f0240702a1310184d0100d08040562010a0b00035104000104141d00410b40d255a498a50001080c010420040c402e002007842820120707040c85442c0102107940845039041e5a031002c1262034490b0f80a01d201b21042402041d0050070502c41c540d00108004100b500d0340700c44a4000c818070002084c244d40c0341e6001141114000406010000049040003141125000006000360242c03081465403070030040040001403c00d12030580f40c0c0007450b4001e00c02d01050614180080008128005103441100d0002c03400441c0a8001802c140c01003540d00585000d4150104200088d08014103445c2540010011258980d0f110304044001c1c003800110301751a42400e034001041080c058000380078412a50b000e000305561070700d041d0b9910540c111000795042107000210f60a009401a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 163971420 1250 163970170 163970189
    0xf0507021c050706110a0c03080a02010b120d120212070807050d06180c0c0b061c0203070611160e0c071b090204050102010e030405060414061606050411010206060901061206 76
    0x8081e0704002c004a5600c0071103540c1e555401240700901c02c071a071541d6086000401d82010344004000248049000e0440e500c060b0000181f820418408541000f98030000c0c0c0d1111f0300080e01d40100950040c10088030a03240c2c1c0c03400c5041942d80d00040c0160703400582402e0621920b8400180b0061085003210074841d560482400355642c2d9645150070b8805c4075042c00885800c1014000406104030b91184285400a841c00803d40f20078060290018124500303010140c46a0503e5026803030030407010008003802d503903400c050b000c0d40203034504004c8080c0030700c2e00c08440c040040120a082c0c48405030414030404c13405565a510f450503860341d1140d40c6060410b5200404001000d242d1903000d00202c98081e0001e100c40e00e0001c034850384030f1083c0d000d6940e00000034441880032090100b0595100c0030050445440d010f11000c0b03d8103207592210b01151500c0d2190708200401a0030040800711403000e0004201c581400400a07188010500480701008050b0404050700c224540250008155001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 163972670 1250 163971420 163971469
    0x60b030a050f01060515090112020f04081603030806011107140d020d03091715010b090102012405010e09060603040327080601090608030c19060609060b07050709020306010f050702 79
    0x10750082c041c0c0a1352042d1032050f83d9100c607401d210310750a000c0300c11106059540804080710852448003c3d0040100500000d10a01c004a5441000c009200c2c004407180e90002d281481c62800a01200004020a04110300d1410f42007050b0400148a03007034500101207481240507283c0855204240070a000e540242250101010705401c15045016209039043c0540d2841c540c14207656140806010706891110110041140b41c00138405814000014400400c1143c1340040703114581c007400c072500c82c002015034400c10103581c0241c40d01442000503180115185404d8000076403500006001500b40114000c100b03401d0944940c0340900e81c00714680461401d0341b205042c0c0d40e148001d00802d0b010b2440d01002060000c400010368400c1802e034001403d4025208031100c1c1070b801480e9044481c1a11007001140000c0140501005445603913040d0b5280d001d5401c20624080840d031001d03100ba841041030051a9074010b0045200600341d00341142d0f20101c9101140c01e200703280444400c2d440a64 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 163973920 1250 163972670 163972693
    0x50604020f16050609191103030f0406080906060d1205030a09050313090e01021608130b1209010b01030c0909090f020a0905160e01050405010309050c03011a0109080118060b030a05 79
    0x102030b42240c1d004208840e0075688a0b0042c1d0380d10115840016540d400410308040028032900b600102c040d8003a003076070305000c0b41003c118001d401079003194010480400030040b646001304611540b1410403219040c02c60019101c0721801081c1c010000e041100020009240500c1508040c0000c1c1d1320204513981ca441c16021111148483d001c3c180e4013078205450345403e8803050080c0c65101149503002c1c50509e02c80da603401c9056110f01d07102600300d20b41c0c45d400511006114080c007c48615002d40740d80510346060514211603401100038149031400040398a51076110134038030140d5140c2c0da00052100c605040c880040b80001000a52140100001061031001030300320700d01a0a000b00540e245521003201a20b03808080d00850740021400c1c4000c20456100381c00c5100002d00a206a540580d40000400d09640141810340d030300fa08090550055940e11840000090910b1802000303401d007984040c1c03070f6040000002500c00e039140e110000d0250350500030042410b90220440d00380300700340c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 163975170 1250 163973920 163973947
    0x7030213090203090d1d09190e012a0807050901020102070f06090b010f030314030402120a11150a020a300e040b120c12010b1914190603050604020f 65
    0x72104e90ba041c2c010000440300481c01141c03c0144e02a19440a403090441c0c1c0b028800d10380c0700204801d030881c529822200d0980018071513040f10b03c40c07060000c41c585128050380c8030203041400c00b1300012925500040941903001c4d1000e500540107260880d910390300c080040380603001d121000344c40842000a90340811145078040e400c002d03c04e00688115aa0f1903c804034140841e10014010901c1490141007e4810000466025100601410030300003140f4000d0300e4410b00603800c440500d0a120602c3c0c0341c2c584071101c0d030200c0721a2120140741020342c840c002d40798001e2100c01059100d0744640c416041181070396014150440c0c0c140c4000c0d60101140040400d05013010080c004c0b4900342004007a07040c9419928414401d5a00500c00c42038180309001d50b20040410b860025540c9800b03c0445948403001da01c001500070320003110301c60504640c1e10405950030310140c82110340e01ca030400c088903a080c0d004100c600c1303402c000400d81d0706c44003c03d0181c8511100792007107110001e0160500302e03070f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 163976420 1250 163975170 163975177
    0x1080628080f0c0307030807150908040801140903090d080702030f01020a200106030b01170a320f0a020d1407060512060f0105030123100c0506090a030c0b070302130902 74
    0x860b60849414001d200103050302c41507280000b1384036410400c050000714000c203a0b041c1c0019a40c030400110318480d600e905490350800e0300301c00d02c96511a8220420320101e0807109030040d1881c4041c0d460081c030030001458614280d60000c18900c0040340a405550f0107201c05108031a5000080d551404102d4005004001c4100c01c0245111010960901d0100502c00c4c00306983c0e101034003e485074200b190b01164103684180306071482c412000c0c104000340303000342001040312403001954138003c1051640a02000c2d19200304c0415400b0203c4401707001000995141c80e990103951049510105007800c00b03c210705940c92030f405101c0c401c2d00107180e60f030107070080591003203006080d82c66031140010044000c20342134070b103400244144018404050b021000c10440c20041c2004d56044003100040755a4601100c240d8004c20702512010003840000d010450340000c09170041e203000052981d002d48a03406a00d0080c10184080d000501800e01036030440e92031001211540ca90140d44203400c0003e5130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 163977670 1250 163976420 163976443
    0x6090603090c100f021b131521050c100504030c0303080a05071706010e0a0306090c170607020303040305030a060e16110d02030f031012060902030c0904020108062808 73
    0x140003850183d00750744507007543d00300d0b110030303a015101021a0342015040308180c4035485074401101202e0f00d00716826445807141c0d4444501c6084411450006030110300039025082c81594104c0412203800200301003900405008215401d01540301c014100b00d51600071038200a2003070715800c1010052580001140344030310070400c014010ba90f280c400c1101c10114001080c402041c000c00803c2c11783d03000300b1019400e000090081401c0550305d8450380180c4465400139100070140c035900340130380c101c41d015103c03110300120000c020904052000075030f6488010b102408014010002c03601c0840c481c0c00c520018040c800481c80d2030f003088024581c40181241948010500e00156003040007000320352040d00c610160080c501f40180c41002010356440142844060080c0e044041103440701c1ea040e0009280c0103003800a20104140706041c641900d20707180510603040b040412006070b0b44084513030762140302551f280340440e100c0b0300754413103980169840c510751103000d0801007841c08000603500c0611 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 163978920 1250 163977670 163977679
    0xa05040e1e13020f0f220b1207050a0b0702150c01020a031a01020a26030106050d05010905191d19020f060c0a0b0c0403021306090c09080c0d0206090603090c 69
    0xb81c5550b02c42d6050a54041c000a40100d21200b800c2114501030341c40c80068030b0050104000c055040c0d1390110381c0e01c0c0c000e03202d010b8180d44009441440c10000740c01c0014240c80c4009080103070a110020300981000e21490000100000b6010119121201c51800a04075010b070341e80c80b03542c9902054041c0d0001d64040000915148100c000200d402c09001c0f070004041c0c010f003241c0706c1151a100360fa9a410607499090350403c406044000408400a42c005c0c0015910340d600e98106a0030003003030710010380c0b0011845040c1002d1119108170f07aa101009040d101c000000c3e050381c40c1015008400340e5004c0351409008099031080e00350612100002218822141c0850100110302000343e24084c4081c405403070b502c4060310400103103170b03001820b8100102c80c440c01e08060b52640080c04000e14803250100c182c0d10303501c0820091055008501c00c2e040c0c0c1d410100c102d5030070300301d0311030759001a100440d11072500144100d0640d00d171081262003050026140d5a600c1c5000084660b564010f50074040c003d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 163980170 1250 163978920 163978981
    0x30915111f0f0903080a0c020f060f0103020306070e06030721090b0a0e03030103050309010f090b04180c050304050a0308070e04090f021002030c070621020705010b010f14030c0a05040e 81
    0xd5a1251040f8001c1d29410b0320b81030103d80728100c0a0000308001480b99066210f071a12040c03040104000311481000c418110031182e605500c10b250502e80007800300303405e1286540040b0710507520760066a50110491800e0807062020709101c222444105540140715031403d442101440200078a480c4601c2c0005000c0c00503400f4011140c1e544d100910020b005500280300800156100360351000e5110b401c4e24000305100c0e04c030842102d10b54025841360070b440a8020003509401c4181c061402d03113071480e0400504500c0c050b1100d680b030701c0a01c04014108038400002400183c02190240588280540200101002482e0201c16024481c2e8280d1080d40301d22054007030248004120b881c5c050841c0050419649401020745101102e03410003001c1400709031840c020a80740380b01600801d4080c00022402e1500000050300c52501700d0050303810000c07000f00007000c1c46115006c5907008030400c0300c800c0c1c0d6403071074290031100f5000d26088076901c15000d605020141820350414000500108102042c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 163981420 1250 163980170 163980191
    0x702011707080109151412120309010b03010c0306050102030306010f03020d060f0807050a030317040507030210120c0e01050a0e0409080715050f0f011202041d0d0206090307030915111f 81
    0x483e50744596031b003204c100c11480030281015000c40d045000d5030300032140e02e60b0214025206940046a060255a42d00d0488403076514003402006c0d41180c01e0b0400704819400e080000307440307100c010003083c18804610000c40040d0310980c111801c402c6144405c100d02a204c50360340035801031034030a0306400e2140340404039075842e01103614000c8991645a001c1003003040886000000340c0208151780c02c0c001c0101c00005600ca0b0825841a1079090b44d0300c070090f0046100c100c040340d00051389181002100c850b41111a600001190030360a12404d00301c0c4212034802c0000c1c050044000010561280800c02e4001c01a80c503900c0200f2481c0c2c404144801c0ea5202080a40000101c1e04100c44030f081d60300400940d900c0030010071500c0d001800200c1c00d09070301d2070f8403659000c07402c2048040c0d82c003490f505504541e06005464100740070002842c6040d10b140c030014140d840318040d80c0d042200c10400c0c04012402a80e50401108600341a00c81c43c00c11102810b103030803000c440651000382011010f80707 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 163982670 1250 163981420 163981451
    0x20a0812040303110309100c0506090c1c17070b22080a0c050102090a03120f18050103110c0123091f0216080c0706021c090b0702011707080109 63
    0x103400c54a052041c00d10b032441d2411144004641d04100f1107000400c41050135849880d88110358840c0c81e251401000740501e0058a025401170140c009030304924256080e42e514075030302d481e1642c7c41990030f0000072100e040440b00201e194020140b107140c0003c00c00e080083c2034101c50b1040264a800342c07008000c402a881da080e180c22030040140707000b00900103646014404680180f40150001400c041c0000d020549265003604260b07010f03100000b1002e404c503070100d44050f02c11158035001c003940180190000a00d5020300525040c507496902c1c050300201c0e1401903983c01079503c0000c0c00b055102c8522141d100303490141d944600c60340340002400b00c1000240b1780f42c05031103041c40407104040b03510b4444000d4000550040381040c50340810408141c034080507100000202c80a4503c4915020000e0320b4600c20105511000940640e00c800c0d654020304814200e0700d45881440e6503601c41e10048601c4040c030144520b070a0103142c18441c0701c50740260341d681a9110b010082014a001a5680c0d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 163983920 1250 163982670 163982683
    0x7090b03010b10090b0a090803070507080c060702131a03120703030506010f020604060c0e030f0304090c090b0301030303020f090405010e0702060c04081b0a0801051e150607110307030c12020a08 85
    0x50f010910207201080311041c0c800090040211903d071001171603860300f209604640c01190190740641c050801482400d609000b1455541021680c079032602155030302040c1c1012102c44107000c40d5507110391100034540c000c07a0100c045c8400500b981e960408050601c0415080790005600291038480000c0342c5500602c0712192600322074004002c240e0392940d40340090702070ba04102c010480c20f0742c86a00709407400c104503400c032141400610748450400c6000c20445001c1040c0c8400c1240c20300c0100181c00c154811071341529050701c2c001d030361640e01d41c2200c10b0603c28110f0b2175801525000c000241c08820780d070b119025040d69402e03101551540007000d2101d004502919010341c010031094606030070720304102e510160020b8020104603554203c02030840e00308070307190a01410003018190f95010b551494650050301c100c41b11801008040100f0494060107100402c1c0e80d1100482c2501c65400b041554011a8840c0780e8447d0b554075444c01025003014204100d005a01481c0080780f403031004102e1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 163985170 1250 163983920 163983949
    0x8041203020403030804200a0b07051b0f190f090b040c020c090601030c09090203040c050102101802010503040206070b01140310060e040b0c071208011502011503080c0c0307090b03010b 81
    0x403d17002c1d841b07544942031110108210009130306003c114900c05034440060450040500e0340069441c0c5400b030400604041d80a261107601c0d905002554010396035400024940e000b050b03c14945042c503411080640b80310540103003a40703a566001c0024110040c1d003010000708400d403010300640c0c0600c001aa41d820703800500301d034880b82d40c1000a03105e501c680e10241c01c00002d890281d4840b561030808108a910035070f801c0c1e441c244070301c0c000c0c440355804101007201542e140303104000040004003030300344801d4481740c000e04001001000c0380c155236400060390551600201a0307042540e507030060240031040d078400c603030003401101001106440c052041030100d590a03221521295141e80e511245e5140040c112800b250080c0300f03500c041380016206e1014003180b0b17190589194140aa00a00358401c031840b00216814102103a141d010402221401c03243d00015082e11403041c20010341c00c2c2042244a160540302d4000b0000d0080b03880d40000210900c10380080000c074044030244040128460103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 163986420 1250 163985170 163985177
    0x90b040b0901180906091b050303030f0103150209190501030609020c03040315140a0608060a1b030507120e010510151409130c050306090907231207060804120302040303 74
    0x400c1103403210b0b001184824140c5000144c80c9241d641c07000200e0b02108001e0728601060034032801c040e40034000130405028220010340c00c511b01500d2501c0c4d47c8405000007040c3c0d1500e10600d1000d40d0540c3c06032607140d04000c0014658580c160107800011250b482140d002070f05001c400940e91030180300711000d0501c460055840c00741151624130b01d04881d2404071010381e503141400b403103044040c61000e000e14144000803c0340e07440c0000c05c5103040b2001e801c6008180c909032003c140d000c0c10360030341e240c031242905020495a41e0035034180e8681500c11801102207081c00c009001c5604103502032442001d24402d032011107903c807584400000307421005140801c04030407940c40b04031310380009042580c0d002002180400070200034101550360741a40b80d00441c01c04410b010340e41c64400c0215074001c211100a10342e40e403608101e032804aa0780c0e033320100000084040d101064481c14080090310721004211803140d035035400c0081c43e0b4601103c00383e4000b80480c2e1620443ea200c1c2c004c96007143d41560303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 163987670 1250 163986420 163986439
    0x1150f06020309061e031305010501051503011e0515041e0e010e0a020702060424230a18140a080a020607030e04090b27070308030f0c1e04090b040b 65
    0x3c0a001c50341e804540d44072118182c224044464040c2d240086104d1841508020039000c02450714078203490041c0c110ba40300740d0712041007111109000081c1d0741119003400a404c0c0d40c01501c801c081c000c60503600074a400181c06020b26844d00c22000050003122541118482005902103010240064600912600749800d000420004424061060700903406030001480c183d100d0340000d000f40d200e50b08c418001c6040c200103500e84c83c0754000d1442540b9207810034a1500744504511300e080c0010f601564103440c80810103d5665100e203220a154a40c0c10103000c82c001e840303011180c0c0401c0202c0701c403845004000300c040340980000c25240301c103039405030149090601e99502551141d158494050700103030703240303060008510016101c0c0e004404140302600c004001500d80d001d8044c4189103420594048042000010041000c070713588035110300c254194640b0340740114001e9209021190406031807900403040f000d900700c0010001c4441c61807040054014036402e006c251064804202d602078180d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 163988920 1250 163987670 163987687
    0x807080901050d02040305010b1503160809240114220908071b090f0c09050603070201240e010608010e13030207080102121006030e100e1c0201150f060203 68
    0x580180205500c141002c50809000072031280407078015500c140d0b141d80d104e100c600c00c2410b281c107041d0101842c407110540307503181179903034018101d645038582c5081001104c0016800039080c0542070150f1441b0000c00c0010f8000c2d29444901c0500307005060030301a5038600e0321a540b0300300c0b9900110000c0069070f400980d455002d0400104202c1300207980300707001002100e00184803900c044008013083d0045071592410000c0c06c20484200440c0391813054a826004035807150031408a000320b601c02c031072090341c0366280c02d807ca002d040543c0007440840030f881c801c820030310b002ca8818004c3d40c90b003000d04859a0f903501d4080350442070a1041e404200010b5010540c3c43c041d40904001e00c501a004541a80e55110010341c2260f100d201c2c1c1d2120f445d01c030000d11400e4110540c069009020f1481c0c00e05c405101c0201e06a143d40e2050244018030b50781c1c4205c041501c40a1110507001d800b0584980c20b040b0020030040d001e8214400041450220450049840c000480d040410b0b100c15900641c14141c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 163990170 1250 163988920 163988933
    0x1030902031510031505090105060f0f0f040b041b120b0d2603070309050f060405060708090a020a060507060b010903050706030e01021207020a050f06150618100305010602190807 78
    0x2400b60050050410f5021002c02e440142548014540040000d01e51034401c68145c00c648020b010385218080301c14001e07010703568010b03440e01105401c40d07030f201442801c41c1c00280201850034010741c2050030281b80301c00c00c01480105825030806601e9140701042c8000a81c8102c80500c500396a0148880900d50041408440d03110780c40e01e106580a00c0884184002400503002194071500282e00c808580017080000d015103040005090000c05541c1800d07550940c80c1c1d480207007043c040010f080f0000c1c6801d04200f0024209035009420a4122611604005c0c04c0d5031000310301351707200c3c0c0c10400420803951084181008594004c0003915549080400450240c804245032140ac0c1d9003c3c4180010111083e8a15002d0714184d002011100c126242860511b40101003059103a00039404019009041e000e40c040c403540100c80742c0c0c0e42c1d29401c01201207152020a4002d801c04402c1130510300454060b882641170316502d408a0701400c1c0030030100210443d5403071009012101c14003481001468 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 163991420 1250 163990170 163990213
    0x3030309020607140105010f0909082d191d01081506040e0c0c251e0308070b0103020f060f0d051308030a14010906050609151b010501090b0103090203 66
    0x8000c010078900100741e11481a104903201131a00b40340d40d918010803000c40d04441040040c0a02142070000e80450b44482003d4007410420000507400c401d44d0b03020324031640792030520f01491002c2e12900d540741035815070b0000e4601400d850118010030007000082040c405810303400d0f03505070750307001481d50f4000044041051000026810010a1001095005440c0c1d0031a1142c000583c01350344440c0318200580c50f0500082248090316041071500d042c0d08441820101660004d00311111144d40ca08000340c800c9216a0018015460200703a83c4c042040d5120120b048034021134a80c0d001022a001300070041c400e04004003848035040080c5c0702d4110b01900704a80c0300e800000c00400a07009516400a154002c80e2428191541d0f808401c60106940e0900c601410050400708205420240810720621400300036a20804014008204404506044070821101c0b5081d81c01044010026a03000e80310038058816a1420405940d030654071911070080100d070000e0050800502c070b9002107600d80c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 163992670 1250 163991420 163991423
    0xb0a090f0510030f231f030c03080901050f0a05031902030705040e09030c0106061e020109020f0d2a0e13020a17030409021b0c030606010207060302090a090903020109020310020f030103030309 84
    0x9032503040442c0800072081d07280440000111741101030f0324004c1c400c03000010b105081501c0880e100c2105102003010701001ca0f0a503039101060f10b590b551400016200d0b4024030602c08151840003400d11503ea82c007102460140201044007045610000280d005a01040380d58600055003403004010442c00c0708400c0387c214091109032031401c1000c0b83c040b82034803003507008440800c9191290400800c0380300000c1d88001803610007002101003a600140c0d01460028110f8861709a40d6018810300c41e0400c00c1c00c10034008052035000a03100540c0896201c0500d2060704244209c100000700700030b184045040041ea4010904500f6506000f024110380d0040350700284a44002d120215a14485100420f810b01c48090300c9942d04201c20303000342c50030202c01c4810340290010f0091007101d076000a158800c0d1112801c0c09a2200000c2d40426039005403544800441c600b001c01007820301d0340660154081e98025020b030350140e1490340da41002c2c3e03c6a0b0308500a034030010001000482e11070740c003082109 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 163993920 1250 163992670 163992701
    0xb0d290114190f0e01030308010f05060306010c050c0409050c12010203010e0c0a02030f16200d060203091920010c0f02060708070605040b09011d070306090305040503070b0a090f051003 81
    0x2d40f9064900c0004100c2c0c0c002240d604603450060051541201c0c1e168010186010a03240340360906010640c60300010780280d060221040600301000010302101e441000d020784100988503150400e107a03a1041d42d15424013031089da4199000f02d08060017101d061311920007620700d0544403200ca5010f07550200c5201c0c000c60100344210508803c0c0303c00101b1308214562240384401d50141450034800354110042c03d00c0042c1943c6240b500c0c0c484110a800d2aa00424016100d03660381d41e20504041d03005181e01010248100404100308200744002545032440c40c031070984440c55001990000b40e8a4006445055442d0703103000140ba2680042000c1031003440401e081115079a40d00c0d050310f80903501111221014410405a60000d11803145070100da80c102c0782d4800c46111849071500303014000a0a520b0b12003e0700d006140c0648202c800912002d0f04031001c495480202d0800750304048440c400080b0b034090700141d4102950480d1094800c020114004481444800c0c0d005224145100d100c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 163995170 1250 163993920 163993969
    0xf020a02150904061703070c0b0a08070804050c04060305010203180105041e0606050a06020d080901061802090a0509090a03021b0109090c030b040c02031e0c0303040b0405010b0d290114 81
    0x84181c0000c002685c0b10701d10021a11209280341201a440d8982c01292180100703200d414015a401096a6040100c42c2000e0456072500c0c288a03041254072850141c016091110000c1040750541c02144070b005c0211180500c80d03500c040380341c21707241c040d02d0191906501e081120400b9160f03600c01020705108030310002d0840c0c0d80350f0214842c1581c9502110241e001014024109a000350081e5809906800200121414901007d620307041000102941c598041450718141d1907a0b030929018040c01421990580b8040e07401954405640c0001c40050103142007005071440021002046990140c41395513040d8100000d0b40000d00109480e00d04154403580d803844642c46900c185070908031203901941d550307441a1807a4103000311110642070050340c1000030007110351000c004c1d2500b01d82d024035150340e5500c80d4103140f070240000311603455211107030300c219604020648120740d01c0304020003900e2443c05c00441c08070742184000d1103000781d0000e01448000c02c51500020049003509801d030340100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 163996420 1250 163995170 163995179
    0x3170c0d081f180902040f111b0a030f030504020f13060602120304120f02070e0c0706230402041113030510200703050a030906090605070f020a0215090406 68
    0x80d0481000c090404101140d0510a00c034409a03035048030840755181d0000d40d10301d0300c42c00700c448440d9280d0303a440e1603685000d82001c65886811001342041c0c20b007428419a12180c0750f109565003c41d24003180007a5241070b0300f82841000c1a1120811307050340b58124071081d60343d010b030007511000704101c0e0701401f0001c5036142030b90f95620038140c03070520f0030001904a003484400380c505841061101da107118140100800a01480500f200d0342800c0e01c1c1400d8400761001040c2e1420316a9004029207004503420007079803084000c0681380c901e00458041c0310340001d41c1294034090900d201008444c40407080041e0141c00d19400080920140803805490480015101821700000307400031291600204601a0090310300d02034481c1c01000101c4010007600c0284e00c0b040a0f00c1450402000d20034049030718252180603034003224600e6007000003440f0380c6840c0c3c5081401010704841c0400070aa040d940e11800510004810f00b20b19400b45c0602d0a101c006001d010907a000840c5199000b61518004074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 163997670 1250 163996420 163996423
    0x604031b0206120610020f03041a0405091e0a1a1909090614180a0605070c06110703090605030108070902090301111b0c15040501050d0906020a0e0a150903170c 70
    0x5140c0301d4030f446a0310182045000c110791030905a4a1801315072092100d020010320100444040f40c1c04000b10368855070880d8040d05040c061540310a0380402194100300714a0340305018042d01e04900c0d002e41c0740940e200f0110500700c5180d06403603802844075280b010f02c5d9080038000b145803046014214900301c0ea0b5a200001905d05a0030111001c81d101e040d02845440480103958010a10b6500e0840f0040110103840c0d07a00600e040150540d611440850b0940703000d240148251600040300340f042080307000340c01c2e801d90300c046401c9002810840c07001840d644338006036816250303c3d00250180c42d1810201034003a400041207658155641c0d500d54003c105501c0c010708001d4803003100ea107400c1d07126013401800c168450380010300034101c00800032980385c1c2d03040848041c2c4500b401d0007501e81415040907001050501002800107100040c0310400c142c0128101030840011128500c00076164003100d42c01c4100005003602044d01001d0500c000b03000d1134100c04400d5140401c0b581000034804140307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 163998920 1250 163997670 163997677
    0xf0501060e0f0f010c0318030f14100606050d0b0406121b080d020a0b090a0606030302011e091131050a0e0c090c0c0a06020301080c0a050a06020604031b0206 69
    0x300410304056001c02207040200c000540440110381d0f00841859040002e005283c81d0307a001020841c03603500d000d116207201240e1101458000302d088030f20b000d5074500309009800012070644c10f40700fa00001024000c1030300559003640c0d100c0d41d80c1e608041780805a400581101410158041d8032100007003981407509011004050082600784c030205800995000115501d4000c0b40c0c441c0c103d204214091a000249524030a502545c244900d82c2c94140f11414000c003001e000340400d0810500000313040e4150000810301d0104012082142d1006044100300c5000000c000c211600307035400800030307151116400030441c4104400c10f540042200340320a0251889880d0141180e483c02400141045c07441484030300311181005180385810100040c0a8541c0140600c10a88001850b01880d800c140403a40d02640d0240c400d40d02c030750b1107000c2d41c0d40354010341c4001400740b92010701c00110741ca01110141d0441c2d100b60054000e50f00e03140c404461019410030340b10f269032065410000181c079944002c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 164000170 1250 163998920 163998929
    0x204050d060b150301060905061c051306060506071502092107030b0109020708070210030e070f0302030f120307080c090d050d031104050303090910030209090a0308071805060a030f0501 81
    0x10030a0b18002000540c0b41c02c980411400c4009200602ca01d94115501d41d0680b030702118115155400c2101d949003121a482010070014105410b000c1e521404004540d4210301c03c4c04140f18860300c40080c46003d005480340600380068818810101e0f04a46c0d009040209015020040c01282400c0d2108407000503d60b00f003496010150410a0000d83c070106405000b8882055207040600d4445034964080c0c1107019102c3d00040c404020100c0c06503102c048465102401c0d504041e65440444444d60b40911050b4001e0043c50803001c41400007080027200c05501411060130750700c90740707012659035000034a0140750f90403c103d140002e684601031007500510176801811039070a00d10008007503070b4102044150084d0700780300900196070f0200a44103900011b070f074100f110303a581c51654041c8541d40d81c4003a4220030042c05104103008046030702d5080c00e000c0e482d029540d403a810411640b69138040315a00c000b9100e1071062100741b40442c0108050304651078082100c004402d40b0000b2a0401c1c3d11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 164001420 1250 164000170 164000183
    0x50706080103060b03070501120513150903120533030105160e0a06080a0c05040306050a020403030f0203180607060f050a0213060513030b060a0b18040b30010204050d 73
    0x1041004141e01508000784411740c00b038443c0c50302d80710029040310780c81001c0c00a12620760300055441882c199009c0802a0011a0203440c50004440d01c0c000305100a010740010344918211f41046049000c0c0074090748288400c3c1c403060b880e41e40901c8950902040f04c0940343c40044000e9050342c1d0900400340200d80403030010090000b10100900a0954030a215000d0700884a04020141d003083c00c1e160f1000d80c650010509000030740302242e00d44550340004003001d10705020701200740f5032039000e4001e0303910035111403400040c00513090b6920300074100507001c400f200b40000ca09031f081c0440500321140c8110804038070303c000c030354402d01074400071a10309032940c5e804200240500203800441c0014452410402d01c0d045860010400c10580e500014080140e002c0104d90305860740c03010f080c010300e0901307603254440071001c0824800064071b220350361081e41420034000c071500d48500c280072080030166846108061100e00e64801c60780010704001b45560901000856480b19036068914034821007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 164002670 1250 164001420 164001437
    0xc0e0a050f01060e0a06080a0608030c010615180603110702090403030b0a0f1406030c070c03080d050a0b06090f010323040203010e28080f070f12141204050109050706 73
    0x1d00c48100c048140d02c00000c004020a41d1841500d80c0d0251005841d1185403d54170390761440c03668070140485500011861200140000c03225006600a005a40082880018415031484100c860448800b0381035440a4540e00030440c0502030380c800080c22200d040b00030304000e80303600003a40000f01100c0c260701280d1a0310164000c1d1515446d40c00290a2860455403c03d00f40310198510320341c0c69031f0060081c6400000708480c280200b09464050340d2000106442680700d290207500ca41115407550620303801c100c0070030b9418105004418071071710301800c1f280c00d2030010303020440c0d05100400e0240c181036031440b2032000c1c102207041984807041e5088030341c281d600703051040c107007165034510860105400ac03031580c0700700c290f203448242c6110840c084540d8581d4a241410f0a840c810714034080c00c0c0380c40000d064410407070705120404106000704010203210801c0101a20340b14000c815110001e007003005803002c102c0a1101e4160814000c200014800d1080d5590910b002d01a80180001c01c4921 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 164003920 1250 164002670 164002681
    0x4140d0503070c03030b032d0610150309030e04050a0c080f060312030718060f03180b0117030c030f12100602030405060c0f0105041113090f06090c0e0a05 68
    0x8019294851040345801491803908100091098041ea94010304158407901d444009035001c2280c4100040f8400300c50b800c0fa680040940181100140c4812040c0968800601a000b43c002d61204030760503013410b505868081c00c0120020215824202c0c240a00280b4162080c5c031240308441c825140c482000400300d03c99000a41100d0004228059407440c0400308021510007003052344451030070301d038120703140c0e00c940030241e40b110210000c0703a070400c001e00f0002500940c003000703080c038004141d2000c00c10102411191032000203c00405400920524010820140c1a494005032002d20205503420910700032246410340d4007000e61081c02c0c640c00b00310b0f000700002c0388140c0c0b500140036100c00c40c80b0030f18104010307403071703004900c945031281c44085a8102c0303410051000d20a6454040000c1001c1d14091030801300d01120301c40c0c840d0280201c1c0303030707140d044410707501c9004d517040c0d08014000d00a2030703103507110720240a0350b03030088820440d10400000c08445841a003801400003120118607032410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 164005170 1250 164003920 164003923
    0x303091222060918020306060405210d0903031403090d0503070509030a11120d1b02040e010c0c17040501020307111507150b0a240e0a080102040e06060408100203040c0302090414 78
    0x4003400c1c810205d1040061041d03a6450200b00c4081782c030141c49007000d00e8600c011141c05140400300c41440d60240d9905108020740c0800084156403180e260090400d40e41c090b00d90450100f200c18108660229003210080c50050001d035601103041d2034540d103000341e000c01103410220980b00440304510003809001c543e261a443c0c29204550744401810600e68641008000384d240441381e055200f00c480700407040d91a150015084800b50000a1200341000d00008015004180b0240c407416031401150501050070022142260350581c010f41c107001c42500c440821395004150140d00c1340c03108a9164040300c003d006803c0c240d004100c103082c1244902c00c00e100750752001507800e200e180b0104043c0301442c0a100300804000b95060004544400f201040d1503007501407012540c07041c1c101000044d81501500100169000b1004d0b002c01600c5441c00c1c070645010b036004c0c03a00780360410140000002d9141e4081c562190061081e41f0f03680d5666004103581ca88290340a60b4031005840114015640 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 164006420 1250 164005170 164005199
    0x1a0d0303021209010b030d0e0607080a1d040c0f1b0b0c071a010506072a12020307050a03050d080903040b040b0c061003110607030e09130b0903030912220609 69
    0x280070000303005e182492030010342c50f032003511840c0060000c00080c456690f125041a100ca1a41c0041c00a0351070f00c40440250409a4100b102c03001100596102010b608060181c1c40441c1e80076100c290602044201c140ea080308524801a201440c0f040d13000081440344140f20700401154400725a144464113040f22054550b082080d1703c5030a80d00104107689810007154446a0403a03038a00066002c40301c003070b0580f164010b02d011024003e203000f0030b000e0505c0007103051052007101203032499981c0318284410094a0320000c3c0454010301c2085182c68090640641c0c000b041000b0341c2e2400b5141d2502c2ca42c41d42090b081240004404910780010300000c000644d00409180303a00c240380740c6036076500c03060700742d00c400d5035401480d0119440c000c05002d2642c4560584000300029080d2510300482d0741030760100392042d545000f003000422074102021080ba40242070940c09811048804185001158044109010009091504908580d4280342d0350800b40c440c5541c2c503030ba11781c6046100c0c1c0c14001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 164007670 1250 164006420 164006431
    0x100e120703170f010b0f0a0e09090610080a2012010c170109021c0f020f040b03040b010b040e0708250f09090b1e0616080c070608090303040201031a0d03030212 70
    0xc41c3e120041c400211311809980e0700107403040c0255a603008542c4100c408410075240c950300044003205002e107070040482d52910580400040c5520340d0759030034446544170030343c1e9000781001c503100301907001340c82d421250807040b0740c0c01031b0903912004000b440903400c68281040c200c000800c201c244041c09811003404500411080300b042d0300f0040800610032107002c01c42c801c080402da40390492045101e054042d64603528010b010540c0ba60f984403a5500c17250b004031070840700101010b001040c0d12003c0000d4174295500841c050165035542d001c242d42c02034000d002c0d4401c01c401e20622b40f4000c080307106101c001c10115610a00210340705440580342201c031350041070503a4140400001c50b500c030f8013203110121100d1024520003a6404001c24200e1140407240c008070368040b182a41848002070007004286201401c0f180015039881084079040ea064400010541040020801662003900b1019540426121034083d280100c2c0000c3c40c0300e45601c0081300800d4000c19240103d0006800495008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 164008920 1250 164007670 164007691
    0x6090d0e01021f060f060503010f09140c13050607150b040506030c13060e040807030f030501061409010e10090f241b050307030e0f040e100e12070317 66
    0x100085001035203e0400c400c0700e100b1581d60000c60165040c0c0354100c07000801040c0342c3d13002c446403115802861644240512203104104200000300c1240c94443c072030a420444d8010199138031104040c2d00756070f000c1a100140a180e045c4041142e070f1305d150060040d5882240c650b007041e5140e0308505e06840b42c841d006c610031454038040103030548010511002c000411100304404103402c1400704000c1805420000c5040202c00401c41040503e81c0241030140c000d40343c0c44084070861034100c1c2a035030240a41d800080708401c89030207103c0c000016040d80441410506468034009010640c43e60692000d4000241030744070070400c038441c510454014086d58141030750310070740d8605124079402c4c2010b8030313000304240b2036080c2c000ba08404c4480c45905604c41e040d81c2e99902c050900034090101070060b0340c4544140444441207180a00c1070412a40384031015015001c501c801c90002420450075070290b41c010319004804c5142003000900c10184039845103ca80503441450007802e00008052480c01c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 164010170 1250 164008920 164008937
    0xd05090109120c081603080402150c070b0d090b28111b1204030305120f100b1602090408130b070302030409050c07060207060507080c0901170601090302090906090d 72
    0x8102d80901080c1c0742d0125040c580710724200d0b4074080107107125600c51600c4948028400030101503000304540d0080b402100c0d1120300f814919004040d80c410036101c410f11b940b043e81e0802c040b01000303000d032000462601c0c0001e445d4001c0d03207819600e40300031501c00814001d401115881289007000324503010844110800c07050020040c203451781c1c450400d240561022905000030030b40810031141007804004040e690b21181d6900d0041c00e103422001c50b030303900901c5c0b030300024146405106060303105074034000641050510f0840742400d160f22840d100d104e0b6400039805240940c44104042d030007144618966640c0755442e160300218805582c001c1c0c00e00e10004c0099001082d80003040c0ca0540b081070b03000140360345610350202a04d108004009001038000318100f81400140d601407803180b200e5803111080e039910950110028864a2070060103d8080100d079806c001d6180c2446511200604060004d10f8aa40010701c0004040720012107690001041101104d030601c45014521006d04180d2071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 164011420 1250 164010170 164010173
    0x90b0a05060306040b0d060c02071410080403090b130806090a02011413090903030c020d050301260c031204211703130209090f06010b040f15020a02060406050d05090109 74
    0x200521481014822500800401c00e41c0d6510781c0103a10700c00004115410319540c3d85480b40c05810010707264000350080d0040011483d1040401100124000f401080e996001c80c1c8140c42c0403502410603010404040f82c041402c80e4003e004001e080a0303030007401b000501e082034543c070702800248480c00c150000361070540140d802448101001da0031415542d1500e89001d0603c0e22001c8591118903000d08002c0e004c014190147c0c000000c04201e07078282c0380c0a8500810039103162100f0700c00d11881c00b03807103100d0888460125001d0940d40b968003054620000d110b50020b40b0b402110751164054640018040024560b00c1403031038454903110348160080c0c2e03419125460b0102d00c43c5401405854000001600d0188290504040c1a070007059a10b082c2054002d0300d03034400380c03c601282c1c1403003001c002040c050f07500c0054404503049074070304103107860a100181a1110804c050070f0150b00c42c50001c000181d58030000303000948001e50300c49403100e5011b01b91805445015265195507450b201d403010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 164012670 1250 164011420 164011429
    0xf160906050d02121f0209090f0402060f0d0e2d01060b040e070e1207090612050a060c020f0601031b0b0c060103110d060212010602011103070e0d02061209070609090b 73
    0x15054045400340c2d401054040054204510105c030000d07000550452180005810b9028220031141940c10b00103a64582c0c4060709014815600039502c01b00c28041c41c00080c1c0719100030f101524507240c002c58401c05100380c0c0762800c0090442940640744104e0085404a4510300108040340f0000090010b0f51030f01d031380440244142c0c0101d42d0b0741002c3d8000510348500a140c1c010b4004005000400b443d0485482c5586851080c05621145410960001442c1c1544d0780d200f600250040003410f0190340554458008010603403441040d806500f034080103220050027114000e500030340726180c4007020440545142c2c90240c01c05044800144056001e4560000782203040d030398480c0c28511a2100380c4001111114011001840c8500000b00c0840400d0005035143c1222082e400078441c0805982c000da24a0008032212000162041810503103842c00f4051b40c58014005002a03107000c500520000c0d0202007224a5919a44124010880395601c502c1050081c03000c0c100030052401e1100000d13 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 164013920 1250 164012670 164012689
    0x90b04060e0c090f0c130b0c0709050709030b06040c02070e0405031e03042411070503090901140d080306010c0b01030605090606030f0d030506120601081b150702060d0605030f16090605 81
    0x11717021250041884141301620480f084041c0c805c0b030318505d442c1c2402c00082542e8100c180a00c1c0841418507020410782406a03000c0d03408d8a91000b0040040c4e40c40c01d09000081c03c1140d8800c046219401d400140700120203101402580110040c50355120a105100070355114078a284801c40410820440451030030304280c8407822200e03810b01003001c54500701c9009890010000c41d00c0c1d0100244480801800100070200381d1401daa18107410381c1d881c0082e00010340c03c980801d40000c03030b404a480001e41d0140c02103a00400504000f5007000460316540300a9800341c1049450035580c04c18401100c030f00300505548820205d0040003940010f1a80315120f4000340ba5407001d068481340410125a80c059584004c00004070480c1d40641c0c0d52160300da6a00322001c99003034400b04980ca40021030a00411008194071003551592800000d6800c0c005564810b450300c20300640d0340d20000c540799509010381e00c2c200e1034034001020160300c158144d8411506a070700000303100f881c14408200507100c0001c80c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 164015170 1250 164013920 164013931
    0x203010f09060803040612051b0c0102070501180206040605030a0225201c0c050303120105090c0a050405010e1206010620060103050c09040312020301080105101203090302060d090b04060e0c090f 85
    0xc10b0a0b115219030601281c000e941c01d5041c002d0100d80b118900d22b05501400406003d00001c3c0a4400640c05002a58aa042001c0d400ca00100720a029080c0100000e40e04448070440041c94001202d2408903c10340c460b0300c0c0201c24843c010300303400307000414002510750348000021605540381c504c0095820f102002d507604510701d880040d8001e000420781e580e4000e100240981383e59401c04003448403070700024000e0620500307010300800c0318600c07a4820b440c5801029180c8a103001d040c44010340d0302400710140e15501c1118082522100c41041c84280d001b04003544032402c065a20031000c1100c402c1982d19510594042401000031810002c1c60b031000e490140c400c0e55468840d070030304444040c01c145860400c40d00000000420560560050748a80d03140c0e4061108251542c140401c21505042d018000900d40e01d03040c405443d050008003250712840800082e40040350b514004003030011602901c450f5602d000c0c500c100c000500ca8a0089841110a04200d00d0151300e078051701c6001504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 164016420 1250 164015170 164015207
    0x1050907090606081e340207060908060118060503010c030506040c110a0b04031e0804110a0e07080705090406030b0a060b040303081506120c1e09010c0609150203010f090608030406 79
    0x8078800c0064410b0528515003881d500c08002e040d5100380d0901c0c0c046c01060400103119203100068828030a05016040e103800c4409007507aa480c000f4080080000600300c42c006c0e60741e483d03000030300d69000d20559007654407030b413000b05091406404000441c8e10107042c000500601d003c03000758028001c113604401503808079a150594481d800d0440d100c203044c16811080c1c4009440010181d9008003d80b8415446901840c0c00b440b1000284000e420a074410b0540100070100806c1141340900041c03517204110b031810358245070b5580001030a8480d80e61044d1030340030f0080140844022a030141401400800181c6494030b0725540d8010100f5000900440e1104d004074181c0c04540d490701c08548100041411401480c06e12400c2c030040f5031301030b00140c4400c000d98060a0100b1480708242d49100c2816102d0110b03810040e100d250180c02c2000c42207030241c0b40040000a550f8444c40598081d201151982d24a181405e40001c00c035007464004507120f0303005000800c0071641c4014101050b840008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 164017670 1250 164016420 164016481
    0x1a06130905010f092616021216091a0402040605041a04030b01090e060f04020a060c020604031406010611031317150c0c0c1801050d0507080105090709060608 69
    0x805034014800c58400850300741c1044001c800b40260140f0070102d500300c4020402c080101000142114403916100f8000c0181c0f5011a5000d450887c0c00c051112301070700305542c0e040100b00030211002e84282c100c0c0310b0195883c0100b4260040418038a10240016070341140b8090074800702900314011413182100d4145025a40d4981401c4203041d5002164001c0400e2002d5840d0000751000d4200001985541d10691000441002220031603030301468014048850143c10700304205d401d88032184d4242d0f0811010400000042e10040e031034050200c60a000e800711b54101500103043c20320030721941c0b083d40e10502c501040c5480c8001350004a0740000c242000859100040c0d81c149000e81d04070000c14031740c1300704000038041d03910001c001126000042e100b0030a4180200715070000c40500d62400754501c440144a10309020442c10310b11070180084a40c5580da82511509441044444003038030b4104500401a09620f401000050111410801c106181813400e4944450072040f20110046540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 164018920 1250 164017670 164017673
    0x30114030309060322051f0f0207210e06130e01051f12110705070303080604020f0d050915010f0603110306060304260d1407020102040b0d020c0c18041a061309 70
    0x1070f9400c52084e81c01b406485040a819650682ca10301e08042040c0480c10705455031200d8502c7c6c822201d250b980445501e0303201c2d03200d1403a40001000981110107018540c0e5042c80c40c0d039201405000388603e0b004048840b2410b21449402c500411f9003d1400f034841c04010f010300d80c140095100e2400c07007510f0001c520050164120000d020900295100d4140003d00f0380e0038420089542c0c0166130003078464108540b80c03001030004911420859100a200c00e001d1054080056005660041400c2c8100c030614200004c400010300000ea0107896400c044150410180750540611009001c00421072800c51074000045605440000c0c00103205045442039801c0c0304032840208005141002c00f0507480d1419410726134020845a404282e0110f035217000900542c0c1305000300d0f420f8800c2c514074a8284415081080301940004441c1e0201d4014010686590f4950b0481070390a511100c1580c511030515040860303031401e89900f13498901d0034910030840c254568215160594030b00b5800003c03084a00e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 164020170 1250 164018920 164018971
    0x1208070212060606031807090f0f0501051912141203090105070c0209010b03040510110a1202040303050720030307060911030109030206072304270527210301140303090603 75
    0x648e08542c14851419860510100c826071203e5401c00918008000c241d807100208140408100704500744017407000d0341403240182c06440741149910172280340c4485546481c1031810300480d100e01100348040407042101d8809c0901074541c01c2441707410f0030800d107403c070b4012540c041c0d014060700641200000124007007010410408064001c444402c0040d501600d0003640642e215840080009000441c3da446002c0d2602c01c03a002c59616444451410143d40d41d070b800f02d03818411820080303583e5010b0320030031610240002c00c0001c5c484c8e000080d111503e0b15020b001c0000c05c0b00c406010385e14240b43c84001a0300020217a400a10a0800015800c601c035a812002803c4540c1c1d42c40c4010b01048c00101c02c02c0340440035042144d00d81d060128003100c41d07040e6045400454190100c0c0208034030b0041c000c600001c41100002c01c22043d074a854500288800030b00020501c014030a00b40000100500e50701000c070000f03070318402c802452614481100040540c00090700484002100480c24031216a1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 164021420 1250 164020170 164020183
    0x9151401120c08060a05030601150f02030705060a090228030b0c0c070f060306080f1209010c02091312050408100b03011b050c10020406120c050412080702120606060318 74
    0x41007424030101c808020010020001a03424034018421280041801c0c07030086030107030503245185001014600390ba0011a46001e1030001030081d400300b00151000307d9424001a4428002c0c1c02c004103500350309105000702015500c0c03000b42044030360041410820600c9281c00d0449400540d1001d241d20b610040500502c00c06018017041d00c40c0590028045c814501080c04070f6205440803c01140d0701c510305038480c116038800c0f104642040c0c0700020b03040c1c01e03440078003c403c0b4103150845003061682e000c00c1400c201900d072a003440142e0321048003002078a803841525000c85240840c1440d24001d29540d96100c06030303441c24000e450348031002c2141c80940c007101103c8203440d166480c1890341103024025900002c113901c400c0c081c1c41c4ea0701c8808607080c001c4500b00c0e078044d500d4440e65141c08000c8401010b82c0c101800811400f000300140350410310740c4410005001c0d01403e5651502441000b29080b40b00c45e410006800840400c801641d8103029aa4030448880700041030004255009080c03c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 164022670 1250 164021420 164021447
    0xe0a1d0703020f1206090903030402030717162301031109041109040513060b0a03080702040c031121060f090f070905061b0d080f150307030609030e010909151401 71
    0x7500810130010021131203035554021241071b20016130b640c40e07060780d42e42c99200844000e50035078002002009000b40490384040c0c503016002c141c44403083c0100c240150320b8050790080d041c030115540001048041405140c08000c0309007400c0007241100c1d255246180030365400326105a03030350030300000301d124144106d91120754010020410703032610000d4101064075403841a00d105183c451b00013940d0038084a400c0c04d80e500901d0703103802d01040fa07003080040c0c030210b0701c180209a1140040d22841c64820007405208200c000c096071240c01c4003c442d01c4400b0010825403058002d00c0c004041e9403a803461b13aa0300040003c0c01d40b9441d80d501c10094442d40065804190840b90008480b5042c58108024180c070640c0b17441030302c101202d12002211900b40075035840c000302540c20081801c98410381194500c0c0480981a9081e80e0340c2c0ea2030302000c070360406106a000c00d01083c1c844c0199070b80f00040c8400380421a0007000001c040302c04035003d85003d4060904019500d856082d9968000ca00341d40d2440d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 164023920 1250 164022670 164022697
    0xf02131502300c03120118110d05041515050315010b1e12070905090903190f090e0103050109051c14090d080c0708010c0e031504030507170a0e0a1d070302 68
    0x101e0f0f05d200d11945070002446103c60311020718680161858080c024880e0140ca20304180d82000c1d80101014001d220142c003ca03408020f100d900c8003d04140d00500802e2540b41c03118031003440ca00000e050910020b580d40126210b881001486107260800130b50340c4400c030405049034525880c485d00d031001c0c811011904090030001c001c0109003130f441b1140d02e0070307504180d5024546840e4002560750f28010725030506a84020100601c0b4410322400b404c442c0e080700e074900300c50010f513110003481203020203800a8a183c0d441d404074400303100040041415064909042c2030182c031034100002c040c01440780e601040e20100050396245503688400c126075268004c0d450b2503449642c00942542c0350100c0c03242041130750030001540c032480d0241e5003110f40c0c0070000c5c0c0902000307000722a0444590800600c00c800b808424017448011072803440641151400c88001d150750f90300c003220080c24007000b100025110711203c00c400d010300041581c0364100e80400680d030090a44407044d041d0b010380250310300d09212 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 164025170 1250 164023920 164023927
    0x105060103090507150507081801120207020f01030b0609220e0a020d030320042909010e04050402030f030c0303010e06060a0c0b0601021c0e090618190f02131502300c03 74
    0x2811405400c2c0126270100341c98030040c40c03003800c2085050303016200d400380d0b01c0a4017403051801c5502a812401000c0c80042c01036182c80610300000f60080043d030301480c4468a419001c070754164251044648a20403680180025850740c4e0004e5610a480d8000070100b41e22605a09104c1400c0c40c03180701801d401600f1103440e00d0f00c500c81c56151401194412040710701800c1e05010f213500010491b0280c810603511a4001c164001c01c0c00050840a4001c0b6014410054008040f403824405014440550720245640b07526055890049a402038079440c4101070411082c0034403504070765100400c6512800c140c0e50b640e18040143d050140350203090002091181d000c401caa64481d08003400300c4421601c10506842d00428041e402844005180c1c0340020100454580350603140c000009600710a004a1610000711754001070b60024001d507240e100c200c1d41d06100c4041820981503d91403580700401d00303032040c1058108154500390078501e8060042c0d12200c2e43c1460f03501107440c21404842101d64 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 164026420 1250 164025170 164025187
    0xb0f0c0a050109030c03031a030c1005070206040902120109020412030c140d09150c0507122303030a0c1b030806061b0f06010605040608070f030204030b0403090305010506010309050715050708 84
    0x5c1007544400460000346805001039003001d1409440442c84005002006080800c109200c05889416146000e1000510001005030341c0c40c0010000783c4800d000160320342005c0c000b0700b41000c2042e0020648980117000c144051113002031000b4a240d007500e014a404242c905040702001c3d00403030007240c00d01400c2c04000d0700c0d41d008480c86040310114040c84551201c00d02044079400314144c4024155005500c0410080360f1030300c1190303011401009030003034111a541940742040c111881d140241d0300007108100c840c0c0810b104802420001703062034071992030442961134420001b01c0004040c842850040760303407511000d0944080030703254910880da070280c4c08840d560356031588e00b4400c000c2c8206000498480c0c415001e6404a440076221000a900c4034034042c0c89038016900c0d90b038201a428400000803c603194034450045002351500c2003141e0541c1461400c0d5500100014181401c18a01100240340010700760b00300c0e507144212035180045040c0c1100e241c0f190400c09030460401042420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 164027670 1250 164026420 164026427
    0x170a030b010206010f180e010e0604060905061612050c1605010b10051c0b0102210c101a060711030604240510050409020f1201020a090e010b0f0c0a05010903 69
    0x80440400b60200c400c2d513a0380302c1409241030f000e4014a6898465240300b10a0f6002030781101c460040420300115003409040480c0703203004002c807820b49800b41c0381c106d10360038440180f18181c1c100603100005c0b401c1821040c400380081d0300343d0384c0c08012242d0b10f100281d88005c408003555040010540b442c0340e60712003800d040d03018000d444962071086e02511401c00c1c00745e005204481824083e5040200307a20300b040c0c0701100401074000c80c0350550240345c2443c461454229420880c003c5200b203681c0c2c407507800c0e40080d803808600007a680c800c3c03860580301400990220110700316415044410070354038101032401c103041d44888030340281c151240310144020020080b00052041004a42d00044009008018410358000fa640c40031245c070440b1007440942895000101031900161190092240c01c0001c03901030b128601811181d03950206000c46aa94811400760090101a102c06029410901c030200e42c0c0c8100c01c2d24103000480000d030031141010500c000a18250880300800c842456800c014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 164028776 1106 164027670 164027681
    0x80609090c0d0b070e01030c02122a0102071e02090703050403020a1406070e0a0e0f100801140609060d03020c010503060303070b180f0d020a030507170a03 68
    0x200055202c600c41d103a002d038450030f100c100750310344460018102078061103118101410074500745489a80000c411240c5e901c0700480503541c0c0c0783c02e00701c2450b1142d600f90241c00081104174042254a040d030162518900584440c501050348100e50726944050369802540003900300080360020b4481d5011540c000d1284c01118500c40a5440320120140c801c90300308440e074001d0040101c4070341d0101050400d418181d4502071071b41c0c14440c1050030900c0060400542121140001e103503440310802540050900e1402002407035100001c1c01c5010104440044c02000700d4800700e80e007400d2012101002030303010390181c03900e816000f00450340d65001a180c207074140300a00c152004900c284500ca0702607562004601d42e860481c0c10700c2e605254000444071925001000c150384101d8020035440c0c0e032507616240040d40c2d244d40c3e24120480019920200d52a10b8022441040c0141c155220 = true := by decide +kernel

theorem cover : BRFrame.Cov 163848920 164028776 := by
  have h0 := BRFrame.cov_init 163848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 163848920 ≤ n) (h2 : n < 164028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
