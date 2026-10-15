-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4009
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:18:56.232711+00:00
-- url     : https://prove2.me/submissions/2ab1e5bb-09da-4105-9ed4-135ef82e7278

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 720863309 ≤ n < 721043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 720864559 1250 720863309 720863321
    0x18060405040c050a060522061b2a15020a0f0605100b0309150108190609021504080a0308010b030609011202010908240901110403150e1218012c0103 65
    0xf80d001c0c1e040107001605d00c0d4400c0040001d821201820041e209040d0b4011341c07030b5283c034000c601c0420103644000b98aa0700d016021b8081c240510710788101c2800000540c01808840400c40c110010240b0307040c06610a04590188400110302c020401410952111a90000b0b0300c0360003072425884001040c80721948035210307030292a24000541e80c90034142d061582e44d040c056103d943c1450b103400001403550001c105c00004003058640d0580c030b40c05950b55800240320050b8101c1c1e000248c1805010010940e030068409800c04000428510400d810080c143c004141d000748814007040040241c0c5848010030b07213044402c620480c1c15140c05510050300c1c0d01883d5041042d4502c00c103400300e140c1884c10001c81c880c24220342c81c4941325849004080d4242c52002e042010030500802007000051000394152071442c07260100092400c0c6c0005000e41000c0602211412a84020490181341c200084141c8003c0d002401c09500c0010409100401c1c01d45107201f1101402096000d484141d00a811403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 720865809 1250 720864559 720864569
    0x8060718030b0c0309010c030903020c1207090c020703020102250b1c2c1c0f09090e03040f1706011502010e010f0501150c1a0601140a02100b18060405040c 68
    0x200b4520318052140d03409503041124004160340c01e11001c080106d0091051002d00f607051780c0070f8010080040188503480d212202c100c1407d100f0140c0021304000c440c45080400401030340540718071442c6000081c40d05807143c41c00aa280d4214040a213000d0541030580e0480b4a18070303046454aa080550707035800c2052880030110740d420002c0f400007a8481850743c21503c1800650200c5480c0d15128560740d8180091540042d000c40c03200003803440d8000d1031669680141803600100c41e5445060400a44103201c40c001015807011038144400d5016205280140280c030b0000280c681d1402440d03565204180704101e281c614008460545038400c1d0400440e1440c0d100003802a202c148401c030004000c03d00c42c4104c0070b040c0c07485180059110720190340702e564100b00d5030341b0300002c500348041d95020045c050320705100200e07154403200790212002d003403150020b030050612580310054003c1581d003202c0480e403080400240c1300100d542103059803500702c08252800151030f55585003600d40110340b5000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 720867059 1250 720865809 720865823
    0xc1d1003060509040c05030609070b12061f0f0305010e0919260301030c05031207030f1b0302101a031011070b0f07020c0a060e060d11180a050303040806071803 70
    0xc000174040481860340071142e0990444520f0758503801c80580b1a1118010030107842d0b0100481210040391800c9150400d50040080300c8914011003644a01817102000c1c0011030528200502160b416224850041207650341c41d0203d0314041440a4840c503410082a040c003918150b150280503180829002101140b110703018040f2005403610b21a8000344002c440b180610580442e840c14080f590000e0758030114512030a00d10580d409960342c4855440500070014141c40c510340403240c3da020b40302082d010b50050711080705034a04403c00d507400d00e6980c03108288041e041c200c06440000d4090501c41c9010b000050081e228960362010707204003100901610074180511071514503000000d80036000c0b0342c003241d40c0204954207006c100c1105201e40f9002c10050ba00d0760038030307080650043c0680c0c0c01c404400034070000d00440e410f803a9040380114901500082801c1c80c83d46c03c141c000d020241c102140218286480d109607159644002445c0e50704015500c02006461144120048040d41e40300e09 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 720868309 1250 720867059 720867061
    0x12030e0105070e0405091501211205070203012a03020a050c0d0906092c040609020406090501051201090b07140403171201050f030601050f031e060a0c1d1003060509 72
    0x42c004000b0710600000501c15450500404c404180010b1042034002441440450580c43c0c0000f403402134594002c401d501020312550040003400a04090401c01c1c42c58441d10b0710340e0441e00516007100d4103042c0490031050703110801d07903a4a07d41c65401035001024500544d6580e01c07840c00712020f0127a00702071140c9220344181c0c1048180c00168040580705103640e0040c29903a10040da000e000303100b50383c1c245600c01e8440c0561441c0303e50a0b2a0b23900c13902450000c00d545005601060440302c1650040702525600e60040c0000d10303200301c00f41c81020b00d00000b4404003405848503102d881d4050700c0310051001441074003400860000c2901c0003140c1240d2141442e5511070380a080701e44c0044581d0065141440c00441c0e946441034200c88142006030040006a0030042404002e5800248080e031602c10072508107079580c060000901c3c11241c000140085040807450b0070b00740d61480007904280080700d21b48040000c030316040781013542001c9039000314a00c0d407a41c0c264003e1803180c10a58020754018 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 720869559 1250 720868309 720868321
    0x100f0305010c02060705040b0d05070c020d050a060b01050a02070915170c0a0f2312030a090510090e0c0703050714032a030f0306121c030e0604030c12030e0105 70
    0x2d03001c1001d0b82ca01c0c1d0283c0d121540e40190440d038130311440c001c0b02c520820a000102e100c2071079a000da40c0c04941b40c00d0801044555400248042095201c2224903038040081841005a503000e40241c4c09428240b1500301103482d00081c1d00c80b0b405004545e406a42d1f000700f5890079140388800b0008000000b0300305000c0d200841e0058441e019420030901614101800044201c1110710480444020384c042410502c3d116072051400c040414026a20688101965056140a000902c8962030750344a100c045894113080c00074550440c00e0000038040131100c00c11120117502102c550200b25001140e568003150314050300c01d4020301c40082c080c04080580d0381002d560001c0100f00c2c0c0810010600d04c0b0000c503da05d0221558070082c502030541090240f911410301800196411060003008040003040603401c9901d07085941071500d00c0400d000500c1148940c00d03108075100d160152024100d1450141c034080d05c0700c05603444c0107103c1390320b1500003200360340b199020003503140c3c540000b889582010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 720870809 1250 720869559 720869561
    0x40c0207030507081507030f0908190323010312030e030a0801062c01030e0a06150501170c1803030d06030503030619080a02010c050f03070308150409030c0209100f030501 75
    0x41d0004881030311481c680460b03c1c00c800100c080c0d006059240f280019620040304a014198200000b10240d440d078410400107002d1001030600c0c500a055060b0f0000000c003001800c0c3c80c10780c0ca003020f46181407094074010303a045010f00c07415039805c1201030300c091200c40d03800c038020180b0b0043c01156000c0401c4c0460910307403000d4014100c0e545030b650030340c03001150000f8503070006030316401c91288103000d15208200d50184d0800da0442411400f55240100551910003c0e2104030303110384540b100c0170784180401d41e0441c0720f10302c844072900c0b0941118981020700040900c119000d01c5854556466844c1c000d940410888031110034002041c440787e5a40d1a00e5507991b00280e0b490b40c860f6018018440400d105c086030b050440300007900070f1040e10520703001500d511403d100180d4450064075120750740c8010070401001e0080c403c3d511558079151a0152128040030100c0c0381c0d1141c0c2c10100c042007c00e03400104070350310700e404489550305038030340180884082000fa440803001c4800808004144541 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 720872059 1250 720870809 720870823
    0x629040e040c05011713022103041509060c17030a11070c06020d0e01021e010213080c0418240b040e030702090604060e040f0503040e090f0f0705012c040c02 69
    0x1083e00c035090302285c01c0c140210a40c00403142d04828006000320003015141c440d143d1062070310100e18428018144041842c1180c0c41303504200e0001c0701840c0f0302c1201c958406030003401003810f8a01203600d1071941da2000d0000f074014488640103d400b0010510304400b5078040700080c500d00c039286555401c140f03056416204140700701d201501034920481100e5010709141103104c00b0580c0900b11400c4d8011170090720060400c2c0452541d075080c00039903c140f8850600e1009861410001c3c0b01c0c1d5080344040005561110340301c5002d0800f40724008000441d510001d403015549040c161000310042d408010041080c030b08036560050800062421031300000c40140f500c603000307a4141540d5581c5109210983d04c040c031030740e150400c88100007000300b688042c86281107032082c0c080d070345400d54881d040403c20030305503000019038028014410000c40c1c100004001d0003c001e000e00442442c040020704010001050240200e0b0b85444c0091018480ea0b030004c01440e00810401a010f21080c0c02951409 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 720873309 1250 720872059 720872069
    0xa0b03070315181118040f0f0603030206010807080102041a09030a02190303030f02090108011a12041212150b09151b060f1504020c010b090106050d0f0629040e040c 72
    0x201d806840d03403500800c01c007291100c5e84001244003083d0615806c1c03000605c0d040001d4442203030f49000c8842a04000d001d02c030001c5002e039000b400254106070006060403a1a0b00070103441c1e10400c010044a141c02c54241100400b0108458980d84a18007007030400c41c8a850003580b000d0561521001c10303141c0c190041c1541e01039641080301800c8071074280120320401c9101760208030020010088400e041003242188030441c084242400812201c9410020050720216041e15507802c4040c1e02c20742c4030321001180c80c10f0724810b00081d070b62345603c20045000c6001d84520114005204c0c6540e440c2c800861107040d1070480d54550311607940e8034581d8100c210090700015400f80c140480e400e440d0031880180100070302000203640c0c800078000c10000b0b510107603681030203540f05c40319400b0380c0d03803000c042d076008103400d48840d82d0320000b900c2e02400300c850b40c1c0140841140780c04002d0081c04940c5203151340c1244262040c040c41481188030036054000c03640111040c500c0c10b0100800c02c00c0b80800c0720b003151 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 720874559 1250 720873309 720873311
    0x1020a0e04140a2307090e0c070f0b06030111031302010f0206071b020a210c060c052a0603010f051516060515060703030e0f03090a0b0307031518 64
    0x2829020400c400d69200809600c240404a00070460f10710050340308415200c4084c400c601443c080b4200340c404440c00311840c00200d01d007840f08120b00703c40c82400542c05201c0715225403030720005590b0341c401c0140982c030103016203841600103015030300d00358041c44074064500c0304107032285004001050b40d580c40b12012400102400b003d01c2019000080c014028510b0707441c0c441040f10b2044003805405000081030b42d004005c0032000400d0000410503980d041107641e20342644d21500d080c22140c0000b41c0c0e00520400944c0c0f04244040384e00032440754423390f10800e08070390140711140d1041c5201002103d05074822030000000030440c6900003501e0458070251401d4241a502a4003d00280107072400d0114080c0b0301c640c0070002030060b03413040707a03c80d800280010307500381d21070f010802c0d58100c0501200800c0d0ba4250f9504911000c008161002d0b2100000b18604450070010500e100400d210b0380040d0b40000c0302003031007640a6041100710f50212a460801c440e40c5644440c1446044d840c0703c8441 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 720875809 1250 720874559 720874577
    0xc030706061409071704032d090803090303040302011b020a1d071812020d1e0c0909120f1e0518010f1b080702040603080702010f080907030201031805070801020a 71
    0x10b00300303218800d110784c603903846401070030725020300160768641c0051084003004074103c14201440540e4580c194040d50300c6203070505224004c01d020b04802610b402c4612281c1c0288000c603041e94002040301c0540c1d9087c0382c050302c1440d80956504030110301c104001e52103958080045902901e1251440808030110707032258103a25444002e80b1038185001407020211042c00c400c6c054005a0420200c0f00c510242172005d5210741030b12004e01c107030800c101002c0d40c00181040c43e4140401c00c1d41c40e81c00340c954081d013017003c1c90f180d82d201c0c0031845002680005110101003040350740360044181c1c411503d104d2071041b41c0001600f20041550340f05500f8810b48541c0003503121019441041c104408141c41c0d21103481c020f2042c90041280c241061040f64492070400c8008016103807070051030001c42c0b1450310542c5810345440054102666180306904001e10201004109030300040c03035a081f02c0d0203090001d101d0a52040e0704403041d8a80401510510031103000041c9440154000d0410000f603540341c0c508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 720877059 1250 720875809 720875849
    0x40e01170d0503060d0809010224011802160f151b030e060702101d011d06090a0309090513060203041401061e0e10080f0d02060a050f070c080c03070606 67
    0x2c0c0d80802d882031504018003032021400580308000038a618041401250308000d500241a804200512030a50413030501c04c0040000c02c0c1000140341911080540c00d505000c0c1156103402455400b2070301820001440c0a140180052802503170140c3c0d954aa080c0714030100d803461072142c81070016070540028600302c0c40ca81d203043c003c15202e01440f8954041d200b922203489410300a044c1e10701d14060921403008044013901024031550111043d06a091040540841d0495040c101e0040080e011600213083c0000081da002d06564181e070128080024030352035079403460040e0349a40c0c100518035440001404180150030718013450a1740140c0c001d00c04151079080d14604804030600400480001b081d0602c0400b4030751740c015034010505000030030a15511710403d481c7c1b0301d40020030500c1d5046034204481342235040c000554003110442082c003040c141061883d90005004050350100b00c030140c916810001110200e0381c00200740c108680c2c0355211410400c000f040544603008001d101504803403c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 720878309 1250 720877059 720877067
    0x1401020414092a040824010609080a1401060b070605190204080c06070611071506090b01050406110a080309011a04050907060f020a060912020c0f03030a0e06040e01170d 74
    0x48111032205546540b41c0c419404002c8149500f00007050a82d41070202007224003081218030022400d6071510390307032598801d440d48500e040c10b03002102081130300344042c40f81181c001080300c202e540c414951100780d108001020300401035904003082c50200091044140800c0d50840381c0104408555821001610412034007284200c0c07203240d00035041007035020307254a8001e0240c00c1c00f0703000d00004546e44000701e110402030f5001440032610303424648540344c1550054031039030015142c2c403003040020348040d00028015000f00c2c82850708104442504400a02e414400d80724260b5201e09065100e061074008240a41b1780194403403010000860b08860f140b03410f001f141e004843e0203018154040c2001800c03600742250815003070561065070000030004619114405050340111140905017080c100024200102a05141c0c8a1401c00d0ba1503621903401100301d0310304000c542080e0054030300c00b03004200700d4016640404c404014803000025913694000c1c20940901000301a07921114030103e06413 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 720879559 1250 720878309 720878311
    0xa02190804050f0607081914010b0c1c050d0e0f0a030e1005040308030103020d0323030f0106080907092d09020307051503061c02120c010f0c1509030903140102041409 73
    0x717400102c40d800444d000f04041e803442003010103a500c004c00c03480660311542d07180d401d080c0c0c40010b41000000307206402400a000c20354000001d0154100304a00c0c10900a1003401121501c4603c0b5554140304503407801d00300000f004a40c607010545042898034100681214400c031804e80c0200360840608600b140f16000b140d0a40354000c0556085908580078403181854241d41103081c45007000c0710903541c88946042000f00d1762130414560340d0340707081036140640340c9040c1d1165041c0000d0354240814140081508020341d460036900082c0c00818900f9007242c60610601c0142c5050f10b04034100305402c135a0440d0317008034001d0f0200c55410b07944005101d42452011012442441d042c00850700d10324101480c2ca19488048440740102ca610790001000b00c1d44140d6011196400001200c080d542c004540080d00c11040c140300d40a01851b4071b1b40744500c1140000c41e07400d42d58804c840c000705401900000c0183d5000741c03084034680e0010201600075440350049498018200c6806006403070500a11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 720880809 1250 720879559 720879571
    0x10f032408010c051e0a03060807120501110a1205151005030f0f100308070c052e2c0307080a05152419091a09090114040305030a02190804050f06 64
    0x80c020305050300100079001810010201f50300c6090008840c03400b004400090100c40900030b40c09101840c050742102c0901e0b0704641c9411060203c0e006140c0c114424a1091a07590004078550340c6403100070b500404481259940401a0a90741e07192940c885c01030741c450603e448441c400340e25032008000c0b00b000100c07511458024144001e10010b02880082d01e5142d10a921205040d916240043d90310003010400f00c00351207403042d10b00d810f4212514104800c400c0c0e801c03c14101034150b00c82c0b0042c504148412400c0e00b80c240750744020341d2000c00014000740090b40644454a07510b01c0e0a50f219040060100b070702000140218628041040c0050104611410041e03401c1d44000c0500400607591004c070b200b00000c0f4400014406094040c131055007480a0b0700c2c0d44500c0ca01400c100c1c940401a10480d0305a00d0070340400600031002000c00d8109426042c0161a03035100c01c0b540b0041d11501c2c0708295809034075001d11400ca5088440309000e24416420344410b007d1550ac1e40e507640c0022100c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 720882059 1250 720880809 720880837
    0x2030106051803011b050a02070b180f010315120f05010c051308031c05070507020301090311160f06050f190309120809150c2814030c0702010f032408010c05 69
    0x16140304c2c002d074007e26208915006841d8403e0b9030301c1c034440c55038001200b4080100e10809040680c0d2406506010300b800090030100700840c5110405840c1040d41e015660003440d54442c0003051104860301007012030b503c00000d000400c40781000500c0c1c5e411048001d039100b00a1400869001008415103029840036440028a5000c0041803005050054011014410b0400807032016072000e009078640345009440f413064202c20a1011840c0030a402c4e001108080d0125060010049080e815000c80d5050326201d034407060a0422030034036104154010380601c22444c83c0d83c0c0041e406800071414140160181c10b0342c042400001d541754403085400c40c461303420020440d070041500100c203a410181402d5002c0c10b00d840e0505003580741c651145c0203024038445805401461707621880d02d141e2000c0da1079001d03045090079810249580142e060090601040e42c89580009120380d0049814186807040c47c204081c0e9064000c041d80c4d180d008005295003028150346402c0d0180c4101c400080c0742880c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 720883309 1250 720882059 720882101
    0x1906060f0215130b040f05060108120d270b0108060c0910030911060a030b090109060305030a1d153105130e120c010c0206040c0512100203010605180301 67
    0x404841d8042e0014009903c1034103040300000030039101c10b0f05611692241e032614640100909110b854500c0581c4409031503880003030b030a9900500c1400b0744400e44012200030464014500b48000092041c0703601703403000700c81c0307021100c1482005e8100034106c40511003a04d616407104840002c183c440c2041c40b58001d405a840005030394400d5000b01031681c0900082185c148000000a0340d0754803025002c1e0000341c94a60000e020b240c4a06064010100e07203404000c0316113160f54282d2030707000d4040c8120600c20482c01d15400c01038040c1b8070000c03411004041d4070b4240c81d40746c0000c42d10342100c0300c4080d803c50f00280c80038482c03009100c58207102d0503041729224824908401c003c41c10781c422088030001c1361541140a00900c0030031411092001c491002c03500e9440c502c1040742101c218005a034110343c850010b102c0827640351104042903a20a0380c0f248040d001c03000c802860f01c52200c5440e41c116100000001d609940000a459250001d40c1e020440407414030030035003a10060f00d07441d011507812203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 720884559 1250 720883309 720883333
    0x907030303142701241707080a0b2a030106080f0f220206070b06030f060c1c0b0a0b030105040608011406210f0309040f150311060702091906060f02 65
    0x2c0506070607488040017041c180701c400038044a1883d5002900301118001d041841140101c1c0c43d100030015402d4010802c0c0382c603000c0181c0d500c252508000e03258804070b8021034041980850352451148805801c00701e100d00614180740c45034424810000000e071840c011592403003802c09568020780394070200c03d074507845020707140d0440760b408131014100440b820a52801a260980179142050145000c10951b26025083c5410b00c41c40c0b03084032600d80c10080c01c010703004100b00c054840d1540000e0a42403a081c0d924134042c01444841e4145510101c64600042ca2950310001507044e6001901c05000e01c990b6544000d081c1d442c81c00c1149554648080001c46605080003000f81c82c44d807503038a46006001034103c0c2810810203054480c01c0383c10028400350b9900b0300b400356a050700700800c1c0030400c500607821110542c01c154080104802e1a5510340c1c001a03a4101c29100e11907001451840c03141042c05008205000c9441d505903814280840041c04500520301131101c6040d58000d840510441c4e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 720885809 1250 720884559 720884611
    0x270109211b05060103140a0f0b10051305180a050a020616080307030218090402100c0201050c100509010b0102010203063105040305070201030b040e0a060221090703030314 75
    0x12640108215400ca803021020000d07841007000769000c0c8014048650450500321044540c507840d640941d4000001d105c00103008485d05900690400b62001e400c0d2188000c2042e03107011640f020340e100d000c0c454048000c000d254019070060043c004100040c015405586855090508000e82550403182c00320015052000060941c6280a0140c000c980907070768500c001d0b500700351241e00c006540410340c112010804808943e0039641181c1c020500c0c50550700007001074444401e0541040340c120488002c6901520541d00f00f44206c8003a1130844910f840c0190040500f02c6101041d5070070b120481c80b0550040c400c81c2d025505c090000ca00c0078a016040b4402001c0c00312921042d0b0141d2032450b0114503940c03180500842c800d0340e441c0d0791114140001010f170340a03140854803551426503400042e4000003400c0c40c0d0603600039400b607121048034007070341403060341c400050020301d44200401606040104160064074803d4500308413082860403402c6500c1e10485000746502069829900e42e4115 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 720887059 1250 720885809 720885863
    0x307120809210d080106031407030f090b090a02011701030b180c270a0b0109090c0306030218090f011b0c02220e0d0806090402090618270109 62
    0x10180001801c11042d0042d00301c0300c0c88084008405800c48402640741a5202581c64018800b40c07409114114994114a401c0e0002a0074403003855550207035000c4840c0f00340c20a0b68a01d400c81100102403031703d0f104c0c0c00d07101c00848000300c1c000381300c0c81140400d98202c0003440d4103232500403106004581d540e50b103a040703c0f1803a0000002510944005114580d9068040d08080c3c0407800c08074131700c07400c21524400e4208003602010f003060912900402d5a64001c2d003090444401c40c001058103408900c0540c028512508082d410403042070101da200c034603641055015001c040100d40c040054180090700325020002d4004040049003a503c01d002c0c4035541d8078520a000600b5421121700040300c0004c0c81d0641400483c495071103448800800c4806c0c0300044c41071210b810418420f1130300b54001190b6600042c80240320340101d001103a01170310b80c0c1031403c0940324081c442040d64180003107050b039000f090b100c80090010110003081c001c1c07807040c01802145a40181d0b801074101401ca111031603009 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 720888309 1250 720887059 720887077
    0x62a020102070e01030c150c02090408130812071703070c020f1807030b150a02070306050c070b0a0509010516051902030c011107110402071a070203090d1202010b03071208 75
    0x407600b60045010750354800d40d58000e612404514004034504110b80c008501c480740104240005952028003689a00e0074003984281e10004095072904160014141c07400190020002072260010b6800e0000080004150362030182c01400703583d80c80502500c245100c02c44040340040c22510356400142404040400e2840006009500040324170b514503800c0720f000ca420310300281c0c6030b105010141c181030800c0214a03a84981d118940b01a81002a50312121b5202c000e084690310740001e0040442e4006031120594800003150301401c0400200f0082c01d0281c403941c04a520300400701d00060300500e55589035583d144c0722076081281000c080e04581260f59a982c00b50f00007000300c481052020b10503901111a1441143d861b12680d003001c02c56101404804d9001c3c0d4030400580000c940c0e031040b101d00b188034000b00c981041e40d400f10b0807401c6000d0307110066000100740c2000c4041218080c16002110b080741d00030044000720340201580c40400d07202e50301401056200781e4000c200c1d91401030207880 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 720889559 1250 720888309 720888313
    0x21612030b04090f030e060406020d05070602071403030a050105060403020d020603070309020312070614060102120706060503030a090e0709031e0201031d0a17092d130b01020106062a020102 83
    0xc20100701050a070340310b181c01210101c003104001000c164000c1121503000005898071401e0600340303940030350358200d1016200309126000c1044400c005060f01240d03040f640c0801110401500c102c00d00c0e41e40c1c0c00941d8a1205181454000f01c1c060800c101550700701da400030101e02c03100751a03800f030085d103500140c014810544c403505a43e0258804200b02c11003241c404200c1940d900b524100030b0126074040c0c41c60300c0c086c0946424030460303a03030000f10900e1141c190841140e441306e0340c2c0303012001410194031480d0940004184d4014603508100d80d80100d82d46a81300c040780780d54440045030f40c01300307030300000300703070000c0c0310011210100e40c44481c001261041c100000c0c0c0781c0c1480800030444d8800f07901e04200350700c0764070711504222074076000300310b15120040702c24100480380000032035054111151a000d0b50640c0030030740551080c0111850f1102000c0c0403850b40300c244a018a0103444422a058095230928500090092084c000300d503400d6039a2503004184e013031109100c0c000b0000c0190590440c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 720890809 1250 720889559 720889571
    0x907050c0a06022d1803030301030c030b0606252015030a020c0708030702100206090a0615091d19021305070201060b030705130b0703211107060b030601050402161203 73
    0x107038046110035180b0008540244c0c5c44014800c0100c0c07200320403000c8680241c10900040001481205c90031701075942c4a108140d180c3da50b503000c0344071070003504000c803890303c0c00c1da0513290340c0704001c402c01c1080f40c0142c06840c1701e10001207030280c42c2400f1504882e00701540c0c690943e400c1d42d000001e190099000f40c0c015240c112940301091400007150031644594100140c0c0208602c0e04415825041880e400501618582184450b464006c10341001c0c189989175400100403a0895480b4009090030030720800c8a41d040340745064005100c1d0107503069500c11042c8501c041c00410003001401030b8014050b000d50994000d81c174000d804007030f1104e4155034a400001c00c080c5202d00140d48a41003694a0f19100c1209050685014031258013079034142d5070800103000420b0380320034611540f0600f0548034003159400815200140b210002948000001080000c201b01c00764102603c5a0400c030201c0e20b040c2d80304c00400c4200d20440c00130340da20b10030404444000a000038810803e00b00542000241 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 720892059 1250 720890809 720890857
    0x50907060801030b0f042112050117060a021809090c01030c1407021c020d03180b09011707110f010e010506060a0e010c080d050117150c0405120a08040806060907050c0a0602 76
    0x7c038004154081020030990340c03040c8403111552280ca401484800c108190a00c03c034043c198803000c010300000115500000c08904192040f94180c40d8103801034014090744c80c09510040d126040000c5450000782071005050100c1e1182c3d500a41c0011011203035803404005901700b100e407a00e98082d032030100580a054802694540c00544103007406500d03280802750040b401c000002d034480d00450220301040c450f082c22a41d01030030080d5462080c1e100018a9101c0f40707826242ca030704000c8050098440e0403810020307200306400110507804000003d0146803a1030042140c140140e0802d08006500802c00780754070b41c4a8480d202403540503525181c036104801e16a42c040d110700f6001701200c40a02c4002a020103c00c01482c40d0201d42c1301c0b895000d1381498118454640315900c140ca22442e0343e162520280017042c020342074800d5000103001d56969407446d9540c1c03030b10002c80380d5510540229000075042405042100e22407003c49018103802086a43c44000a403c10880710780038803031151134021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 720893309 1250 720892059 720892103
    0x6080f1f050d1b080a23030d09140105010b0a0314010b0d092f0f0906091810090c170d050415030618050a0f0902030604020d08090d06050907060801030b0f04 69
    0x4080e00c41303c0007400fa840790f42d003400040c41e880c200d0714070f820b01c041140c1440b440d000801601c490f02140300c8046049006e90401034407440f1301e4020140c8039403a0200018a081d2484000e0203040007907182400b2010200c86c50801c0c04100748210a42c44500300120a00503d240d40180b02140c841d410980e900c21840311070000e4042400700c01802d44607000030301c4100f17240c40c0900f031540d404c00b00c801003207601d0207102041c080344001d0404c680584500385000b583d1001403000d03400310082980d04004160960a0614081d07401d846040d841030b90220114104640214000d0740d40305080c0c450b1407419240031041512400c0800d81d1004260351248081040c81c2144054107540b00c5014002c5001d08003d080c1c04200c2e41c1030704083c0001c0d850a20f09000684000c105aa03003d03804841e041e29002c4107040150f242d00c1703500c4001d9400441034490f03900b085560350115024131a07240454440c25240c0d00181c3d5400020301018216407205400504560f00c00f50042e0ba00600c00d03c02000300e5810818400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 720894559 1250 720893309 720893363
    0xa20040e041e20150307020a20030a06020315030307080a05030a090c08060a1a030c0913060e060114090408071103100507030b0f0a0f0b160c06080f1f050d 68
    0x814812541d0000c03c52880c0280840201c2600d44244500c2c50400906c00f0356504240840108420000d2500901c2da000d4490000e0b00313910050f0940d00c80341300902e0588025801107480c0c01c4c51250a607d1003005081c0042a0b0300e04a9000b4001840d000c0e01107001e40350b079080180745042c055280c03e401c80c005203006d2004401028403500501c00c0b0300702500040152444044900040b4401f0700d803500e0740c2c0d50b00080d11140954107507448019903e817049080624001030002528041c201080b0400c039580004a01d412604070448140c04040702c0d4080000c40d00f410340380034207110410b12103500400d0740c10880c550f81440c000c044504000c8100880c0c015110121a26000700790390300f10020550601c603c03402c614035401c59495441c0381c100a0280d644c840305018103030004c980400c800c02d1844243c22040340e0103801c1145d05045603030701e100080010381c04803401138210300c01c1000f280e0380c02d0581501540680b01894111603076401d0805000f00b1450420041e945490450507101d82428214201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 720895809 1250 720894559 720894593
    0x705062403031801020d08040b0c0a05040803070807051b01121802121b06070c090c05070510020306010f051801030527011a010810060c1a0a20040e041e 67
    0x10f000104104000641881190362082007804001d9003080000741300c140c542c0b07a00000300503041e501d987c6000412107150090790080d0041d844000b03064414414100b0107810040d10440032110785080c2e05124030701c43e03913082d40800d000c590005402e001c1050300ea0050f1484400c0d01045281031009500080e1500540021461494110728001c600034a15480040707508501a500503140103420f9440b0702d001016849440d0b02e00d5540c0072007500b114400d608407118690000c048503120030401d41c075200258800c0d038455000c10244441c070800c0d1030155060f55890b00b511210503050111001c010340152030300400701c681c82c9800514803030340c007505260b00f04180c4000303500004010324401040a2042080d44540341444543c2081203500e190b1080601e090718503030301e480b060341006890700c01c0c1c40c80a107280e0050200412020031087c0042503200369070b015031140034241003c039041c981c0d45c07461145002c1c0b200101a001c0014011600301d0f000c007481da44d104081c0c4144800c0c0754884041640d105452 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 720897059 1250 720895809 720895837
    0x414040507060525240605100518090402030c062808060607060f1d070f080604020918030f04030525150c14011401060315260a0c2603070506240303 65
    0x801d00c4a400c0040e23103041d0351881c5003001031414211010500a1109604240340301d8400d000000742151014040055a44070242125403245a52400d480c0801980d50314115a0070000d15100002403094109602640e009072080c0e1502242e521244e01404c92100107068075522207030416540c1507201d002c5c0071445515800b8103035031400d0145070800c03079045a020307100ca81c0c01203081c44090f82e51200101d8028030303000745011a41d04000040383c15805001155090404049030010500501080c44201c0035000030320106035690140304509189001d02440702040c0041e44a041c110340075405066599000d44056400c0600c0d01c6092130039200c0798148402c11006080040045540500034114507e480320040c458040c1055812492041c800001d04060070304d2040d10340d9912014031070703845e1301508403003c500ac183d03c52030424505007414039503151400030b82020302851174001c002e44002c158050040d00d181d85071010099200f10040d403212640c1c10307403000d0928099504000034503c005059103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 720898309 1250 720897059 720897071
    0x2403030a02070e0a09020603130f12050322080a181a0c061e190906090b15041b0e0a0b0d0b0f030c030705060a0e041404050706052524 59
    0xf040c4942864054281c0e00214100062100141d81f501d041e65840350b0b020b48408100d820364244411800f40980c00070b8001d401401e072130b4503141d0344800114072586100741d0550b520810480d5052034401c9018020b0004a07040c491401041c1c85244d030003000c428404a401c502c42c0d21400206450901d0542100040100055807524004180501603100e5074404003844402d41c1444401c00503c0000c02c10400d0380340d0412641d0030311002d94420502940c12043c200208500e600e4800382801c41030720804402606141001c20301d2a181c0070728220f190054103004034902c01e140e001e880700c40440c01a25400351410320003040e80403041015140402c040311020941010f0700b0148406551995151406504a52010300c01a00c00140d10030803201c0664080c0d5803172480400c11078a14804211087c0d01c00d0508001c16490f20000e442c50f4015070140b000d8400007a610007060b24903114000c400d011030340803071884001805c102074205102c1030040d01e02900036420035400d4140d04040b18020400d06950362 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 720899559 1250 720898309 720898319
    0x22a13050103030305090607020a060b18040501090b06040902031c05090d030203090a0506160b042109051c050a03051c290603010602030d0e010219050721082403030a0207 75
    0x1000341c0e1b4014503c1400303481d59090841009458015075803000d4552034890307051862039110340101d08248070810000c02d0307003800d0520b006800703003030051360075650b1554070004200345141c103204280d070b495402002400c4100718050701c40c1c08003148000c0c1d00d0510030309100352502512242d4450004501c01e901841d80c0e51140c81c204280c0f008240c00c91130045101740032403032030084103801c0000e43e1500426444045e660b04d00d0304045031640d0f85600f001450401c09401d0403560014815020303510100c41c4010002080760914584012814025059500c01138004000c80d00860041c03403025441070321000c1441040035140140c40d564292045030707082e486022001c12450342000da0b214002150860b1455250075070084d03032405141c807039142c0c0031f81c1d0710600c0c0c145100940c12200092200081102d03100c4108401410f26008002c041e5006d48021182180280100c048030b401c5d02c0c069294003070281c96007201e044506900300c440100012448205002c3d80e030307041000c2c3c46030800982c01845010300f44 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 720900809 1250 720899559 720899561
    0x914030c15040c290c0c04140907150e1f020609010e101a0406060306051903030503070807021614181b0a021002070c0f1203022a130501030303 63
    0x15203100c491070500c80207220000d407140500c0001c03501c11665510304652201d000c079aa58042e40b11252100b03e001440e80c3d100e40b00480c0c91003500d00111000c000f600b45803444000d100703c003180c246400750002c3c2803e01800d244c001c8421460009841c010080c20315a80104900b40030078100c4200c110741700c070380310148640d04000c490340c0190040e000340904003c00202d640d640c1000e0580e00c4482d0340342e25202d80e420a140d1148c0501100080c414040e1541e2f50380e002d0001c104034001c65014400074420f00c001d481050171008112a816a555484e603a1000001c0b10081000361220086010311342e80c4e40166074506050001800c044881c603100021400108648241d1001030055403046140400c41440245603802c18803207040042241d58a0030400c00701d08158865110308070031480030620b001032110740d101660503500900314040e02d594a0f407005407500000c0f080c0003401039111030038a020903002d9081a170240598038804401140308400051a003905c41d1051035400b0760380c0e10040091583c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 720902059 1250 720900809 720900823
    0x90210143006030c03061b2208011b090509040c080d0801080c0a060c120203040e070915210b030c0a06031a0d050a0b2a0c0f12070f0203010914030c 65
    0x442c003c000c0a607004d004130b5210000100440340310b004984510301c122a140080703030704000b003403800340c40d014810318800c0030310050350300800300e0640c40c0812810890442c141c031402000388503110340d1400d91900e070400802c1e602c01001107480140042001444140c10001016107448079182c0b01a0740d0f0401e80441e1910840d2683c040c0728030120784080116507001141c10f1051a044001122201d6910406074070358401d503030141003207076020810400c0c05923110104100f950076a5000c03102c2544041c004070340d407606050359a2050428111510301c289400d0740302d085640400f9095516a5030100d0000e40302044c80d500c29004240c64448258481c40081032080540c3e10031203103000c020f449600d03001e0384e0b02e001d143c00030055550100803a04000c415595500901071100d0700c007583d1804020351199a4000f0011100a846640c486482208000c1b60f04030004075401140e9061100e0340e1035401c0050b40c6100184d81655a0381d10280108441c4020b20b00b2486803140150f030b0b03c03004612943d1904003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 720903309 1250 720902059 720902071
    0xa02130f2004050f06190f090602240601020a05010c170906010f050105030a0f09030e01030507020d080703091713170118031218060509010605040902101430 69
    0x103400815640105000d80781920070a071307040509882940c0100e4001d100703092419140d02072844051005d9035004140030105280ba55800040569a15003aa5105c2c11001450042044800c44041320069404c05903440101407041b56941c1c000c4d40c60350350842d400c10007548000388900c441202c0c5044403c034410b0300415640000c0c03000d5850010ba1a0b210900350194904000c1c00001041044030b6a401504161b048080104250f03201842c000d030030300c42c040032402d0100307040c00000f51080e4008508102611358644540c03900d80d070b400004030014000001c040710042005800480c081d1032351009005802c0c1e001c040480394034100551148108120540e080d52613042c1a0302c0481c9480940000803110340c175040078003501810700c01060103000e1128558800112900d032401c180481904401d01031802e8500030445a0340303610074072059401c03c03100030390010030945071022028851115142d020000d0080c5070b080c02d44c2001d01410100780000440c22010005038440b080840c200440ad030440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 720904559 1250 720903309 720903341
    0x6070609030801050f03160902070305040807080714120d05130906090203100f03170313060513020a0f0807120c0e0903070c30140a050a050714130b030a02130f 70
    0x101c600c1c40b07036181c01d42c480c02303102d28040d00400c4070340c00c060048054030301400400741511496915007100d26a00d072001e1007a0700840800703440c05101424042c0922903061341c4040030344901c032a05002919658400c0e0b090943c0c0c5507800d40006041c0d045071060b0406410a1803016130f42c3d042c8101d182000510320381100d040c424404c0070030000a50040040d1a2111041c041c3c01d860350745e4110b0011040f0b10f030300c501400140c03e020401000180c21200f20320903502c00c5542ca80143d17180c0742c6604007100c01740103900069000b1907041c0b01a11501c4001d003603040c1b0812550640e9911405901007a020a480800f21340d800410740508004211140801070614100c603401d66041e40e166800400c01c040c0136010040c8005402d0b0018814122800b407140f104820407201300200320324001d50340d00c010071803d81d110700645401141014031104080c201400080c49910000182d00501d0000c0001d01141e41d07152041441e01001a154182c0100400010410000e500c0070803840c0740c81a070341c038520265000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 720905809 1250 720904559 720904573
    0x40606170604050c18130c03090b01080601150e030a1b030b0c0910050928090b03071d1e0103030302040303020c0406061b060b0402070503130605090a03020f06070609030801050f03 79
    0x4140c00c03070039191001000c10491240c0000c10b1701048031040c549001180712410204c0080c00142c0641202c01814820441c07092980c1e61903140c60f469090a0251046611061079101e405921542d808140110020140c40f240c02d820398a0090a0701020403000794076084140410500151122031940015041c0300d0a00d04101800080d0705140209900d500b80800820314407142e0301c4020401d045110700300107212280002c240314031001111032107412042c50420f08103040c00d0a010078010110b80c04286000910100d05120f10320040000b02075550280c2101c1d0228428000103814500850103030301d005980c1c41c190b050090070f005040c0d102c64003450405004005090f88809240324180c103000c940c5204440780e142c0b9001a0800c210325950250000c60a901404800f00081407111601017025070101d0383c0b00c10a540301e0288a003260b5000080c49070030005030078044144488010001d1416103801c81607034400d001c40d04d2504042c1d00007603072480140b140c0d0511812640c80100b04500070b1a40e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 720907059 1250 720905809 720905821
    0x2030403030e01081e09060610030908030103080702120105011214010c0c03031d16090b0901030b040b040804050607050a0309052d150406020a02040605120c0f030c04060617060405 79
    0x800610302e80c10060440d0000360010350510089040c9220400203000b10b0804080190b980e001c15900548a40c0912038100c0f4030074020b200e010002a44101054250380c69901c03041c0c0140c000b194160303040305031811111240744013842064080c101140040800074000d050a4400898a500c122031603071500102c0d011150304410106c0c2c1303680c0d06d071401180b8810340b0401919044040031307058629100b103254051b1101c00d0704520342c007a1041c15100300100903402082240b40302c400c0c400a801c01e000c241c041000702e450b104100368407500074804203161a549001254040d8425132043d141500403203a8001010b43c00b5000b1001404115004914818103441c00d4a9aa1105080c0b0340c3c0d5510058802c40c0340d450319170601d460701000702951616076a4641c4041d48a10900f201281704518005011420b07207000180301c1021610341c001400003001540c18080300307800c00c60b0219818441c070342114a00d6a00c2d80104406080c0707a9480b58100d6054040016819101400280c421800c100c10040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 720908309 1250 720907059 720907067
    0x204150906180e15221109160507060207020d080a0305040b060420090a080319030f020708040b090d06050a2f072009010e1603090302030901030c09051c030206070203040303 76
    0x103010942c2071200c22030300c07854000315501d01040b4032441000b17190081c00052000f1194001000e00041d1145541907031160754001200002e401c045010030402d201e44004200c0c1c6601501282d0310192040c100000903488a41c19500300c0e296181c002901c03601000b0410580320b640380d800401c207840a100c0e00d03045203d240180380d03011000c542034030400b251102c1940d480c6100310004101d05000e81c2e903980c0d11515502040481da41828000c2802c0030340580d18220581308482032203401c0354485c0c0c00d003820300740c500c2e095078004405d035503100c0c01540000e00841d449200341401100228000200c003400b6090030b6882d212000c0700482d001c903103110000b021002d450300715440290f212402c0c0c2c1c002a8201404505408401509600b005a180012500c0c00a80801c4c0307002d200602c02160510004400840a0b02c000d4140200140c205020148a0354029045509075104500741840b040341c0b12008038040131022600800544014401041071507010b0261540041e00c9101031841c007800c0d038034098 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 720909559 1250 720908309 720908323
    0x3050613051b2d0a031109091209060a1808160b13030b090a081207031b0909050603070512060708010515030103080703200c0907030c0210090204150906180e 69
    0x12400140381c851843c0c2502c0c82d003928201d003070000c0900244c00c0d1a070510b40c5801c02e0000c1054065036030000810001c00300024401a000e0851003028540083c1200b0b00003907030050401a005c2c05400c0c0d0b03003100e040d10003100c1e1310003909440006158541114409030711030b184960140c0100c0343c0c00c210540a1094205590064a8001c200c0418a44410510074038050b161200908003d202184032640d040c0f04282c0180924020b903010b105a44801c1420203404100541580c00300f01c01060402c1001141c2c0c00913640a4001010fa40840b03607203002103202001c0700404418160031a004005007a900300f40008d0140006a802c001c104001100ca41240d12042c00003800641d0040f03100303810588a94030102c07002d00320101c0c0c8034500b0802e2080940c0d031385070107290601c1801a000000c55031442841001a40d1589038000e020794103003151468010022100213a0f006901ca03040c0c410700050500614006049961000460750715112000c250038181c100d440c0925410200501340e4403900040c0c0d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 720910809 1250 720909559 720909589
    0x30105091c140d180203030a090306060b0a020d120e0708060a0c02030304020a060c0f081b0d0305060a0e090f01020f04060f0c020f130b130f050c0406080106050c030403050613051b 79
    0x190344c211803c0d4105001c03409078000354507200003d0074090f2194041007080c100e0740729110510a05440300440c035000d008540c40c0c0c0d001039000441100c1c072144622041d40802007502030018a00c810250402d0a14006801840d01a4008004d2200c4071010748a5000c00003c031303102460540c28198001004010540724640070000d0b625503120521a0040300007406c0c41d404a042607882d60802c45200d0182824250008180100030000c441140a400350b00d100341c0008020018907410140100708503080904041100d03c154035403000d101d40244000c080503a00076420b40e4440d46008070003807442c1c1d1880d4610742000071a520020041e202e200d6100140041111030a58800213419100010b000f1203800c0303548003040c414890651081030303220300d022842d42c2806005540e07580a140219101d10b210356000510300200412402d1f1188028240e02c41210042c0c3c1d1034550f980e1105460f007107090315400c1340c140314a0454010041e00700094a18402004411100394400b0b00005019140507d01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 720912059 1250 720910809 720910811
    0x6030c0d03180b030414060a11030a1104090e03070209180304060f11011d070f0312081e01030b0f1609180b090c09010801080a08030c07020609030105091c140d 70
    0x208441c0030034404070384002e44901d6044540303030705c4d05060513040904111301d03040450281c80c4c0468100166809481c0501908412007491a158122200c0080c80b102d94100820350040c4000714120f40c2500a0400c0c0206001c01075840760b89600400400f48805404061940c6002c56071071865400813050741d085590a041001d40340010480664851000300f0841c80c5551030010042e030010300c041c50741064641444110798090381c9841c11201200c0486c00080c204000c10004506494418641180d2041303090358081c1402d10441e1500d045078900380c0007140c410014004004040000c915010341c0034180d060070031103007070503054003030502c40783c60156801d10742203852911506001c640000b50b1100001d807132122a40b9205d548038031145c001000c46030006000000002c1d0341200091205a03440d00101f105141da110404005a02d5000c1c0204030307003100b03040c41420015542885030703605c612032800c050f100042c0010181500d2040d90104501803040c0c3c15040d04c250854041514030842ca0104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 720913309 1250 720912059 720912077
    0x2061e04060902031006030b13020f092806062a060911150c011a031b011b0b061504120b0612070b0a0e0301020a080a020310052706030c0d03 62
    0x41a4025182da298042e4061003040c03e20b070501e100c01d03800001124020610b00410f0741f100244820103030101940179610007480b99244802d46022412a03421603204291710a0200555404139401c0082c1150240010b5490b2400c201494014010361a1052800364040b0b040c215024080196020280042c00f019a0f90070940f0030030400410b0841c0001c001810366540780303080038000700c49e0340c010301108000d5400e00c40303110401d980305a03803542d60b0800103019160f0700503243c51790900ba81c00010030604001400000034845810380f585080c589019100410725407900009106c02a240c0313504296030900b0411082242e42c07080b030011081c29900684101c0c0e2501c407040060075000d000c1c004060b0501500000242401091000304185015520354103080300c0b0b03141c00c06080b03001d0300950402058400001030301d2244164025503000d880401781c0b540700c6844601069000c28070042d4406036140c420304c2e44181d00c518001c155840071003180105040c100c0038021541e40303081c0341002024013000003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 720914559 1250 720913309 720913313
    0x60b060702220902060c012301060f27030f03030c0e030318030f060124081504090302011d07090b040911010c05030c0111031b13060f090302030304090f0b0102061e04 73
    0x6040103c815800804a036103520303008000d00d00030401c20342082250141d45640c030104c66020011941256001d0f1985081040003000a8a11000040600f0b0007200130701200c4540100050400c00650302031448281c032581a80b030083d0460304402000004d010b00002d0440c4141c1d000801c941920101c0c2c55040c00d0340142c2d401017440c0003c100340d516494000e15001044504c0303094068408040c0c82800c24101c0007011100790f0303030326200b50b54500100d0651245001241019003005550768820310000906984026032400d8131a5031101455140e0405442000884881c1c01120603500080310104081c20580e50b4003880d10340b4110301705050220500c10366043c40230902c296110441d035640240502c000b4035030310f08459032044a40c90071002e10580c3c0300e407003480900c0584091034200d4843c1c1501d0303801c20405641038401c49214208120303101c540400141c80074406440140a20500800e81001e01d04560f000e5540300350751241113500c60800c10129503080c0c042c00e0f2441da81d500c04031026403070728 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 720915809 1250 720914559 720914561
    0x120d030b1309051506010f0e010309111806030d020d08010e130804080d0206070f08070c060608070801090501200a030b04020717030907170c010503220f060b06070222 73
    0x40d072000400c1c14074003540c0702d0500c035001c100003051206a8050f4201545e4410040d00e440c000c49850400040520043c5015540298802031500d402440b0b082000b010760000184010f00e408144003003940d40009100103400d0800c41c0e43e042c0c1d001800171b0301203443c010400804100051040d20f03031441c07040022840321529520030310312154101d540159107680b00d680066980820300c2c03d4400512802002810b05449036003c3c82c06195183e80340c0410f5108d04604444962171080199151965603d000500d04010007600340240f00100020680903c141009406c4a01c6040d201d000340340d58180b00f0a440c4036400407909110181d040000d803482c24400070800034000c41e0402040700310341101da400c092441c4170195100b400300e1801c842100e6114000140d41000f01c1c1c0045030b60360310405c01da8030250700038405140e02c41140520b2000628a181d4456911900160b0580c0e00302c04000040d02441128014142d2494017034564502e0055039a0124129000101208040101004601080040e1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 720917059 1250 720915809 720915829
    0xf020c220b0a080708031e0909011203140c0d121b080a020f0703080105090604060308040b0c010b04150503061f05100c02091f320d050d02031305120d030b 68
    0x8070004c03035075400d48030b0608a583c0c4e400801c0004500b034a003107040620303140301b40844100000203400d04040f6443c00042a400140180045052261102c220b0303500c2c00c4520040c001c504440d500030505048000c4003d03060005110201c4280d42c10700021240039103483d8419101040249000540d550707030f010401c4000e000342c1207205000400001d01006150b4031031a01411b1790801c40b50030039203880f5082000100d0b50700b44001002c464003840100003050b5008054203c43e40c40e2000858544415000030302100d00c9401c980e060000c00c1801804141410043c3d6130b400604c20248544103240302107031200e030841d05d20030a44125040700d4600c90385886411600c00084d070141007100b190130a03000109944011066014015564090005800d4070700300c81c86a21003000fa07030038450030b076405444903a082c01490040b42c200a0100484001920810209a00c024241d0255480781c4c0f02ca19080c0c2050955800244030720503010034a0019074010414420380d104a0400040540c0180701260002072 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 720918309 1250 720917059 720917069
    0x60f02120a05030f01080a020f0f06041701050103060b0109030321020d020c0c150a0e0618130902040c031109100e130f0f02030c12190504030f020c220b0a 68
    0xe004074140441d150010003560207001c00c0f204141040c0e8071411100d0380d58940c55000780d40300142a82c14178040c249a41c240b82c203a20060030b0710b0305d8140c441c1c0100f05500c1c51701d020440b2aa54503001002806a00e22803183c03000024078200c09918590b480041201d03885800380e0301210a0007441c8d00016035594116003c40160303034015900c882140c102192501504c02503180909404003500174001856411100003d6454550040e60b01d15501804581d0f003051801040054000e25066000c1c0da82007801001c5861170300d004200f001062051001346d0b2424142c40c4241800c2511040c400c41c40c2c1c40503981d200005450011070898004030459110446c001d105402440f0418460508803d40c0c1040c048078007034010500c030340307080c105d0701208901c4103c44c2400a24414010454154406640340d50040d0000758400302900245000300c0480340151001c9012401000c00c1e2842540c0601a503803403c002100d40d80f8900001c80041c0210b4800e54840072031507a51079207240701d10741e10b4480c2c4001800e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 720919559 1250 720918309 720918343
    0x40b0a020a0507061a030d0201270206070f080d0e0304030b0f1f0b130b090d1203020d050c0301031e020f060c160306090507121e02031e03090103060801090507060f02 73
    0x5c0c0312000001c002e9040902240c0a805019480b5030007038014000e0140042d0040401410908807400d501e0400c89015000c81c0d22034403c022860200b6811300d2001c4606015a00f01c60752809124a10411503070032014048141d0414071080010405e070b112610361000340c0c0c0c0c1c0001843d40c2c4100f00315400d00000ca094407030901c0c0115010078460481d0019281c0300403a450b1040140c1d454441e10456400358401c0310303500107500300c17595000904945041045810a08026040c43d903c07a00c19400d491003160110401c0d00040010828800c07800740b080b041292008981d80c2d281c9540e00801c12207040c100c4058010400004c001800c081c1c20042000c0c40100c00e200040354544078170b40b4001802c1c500e0000d0381c40e0321a003c00400c0700b60340380f080c028095611000200c64800040f4900803503442c4210207980c58014401c00208054800d003884450a9880b030140d0707035600c824000903003241d5013500400c9445e03261800400008200241101c1a100302e41400e150352207580008074a00f08003170007030416072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 720920809 1250 720919559 720919571
    0x6060f0806041d0601060e090f06010c2f04060611060a02031f080c270118060e0a0c14160f020a0b0a0207030c0512100c050c01140108060f040b0a020a050706 69
    0xd40c3c8007203140b6040c3c0b1066503514924a0419042028071401aa10550100c2d14900031500e558000c04aa900080c480c2c9d8440d001c0c101c11020110a1105400350915010103a585540891903d4841d03000039080340c1c1070030341c0240710340d0118a554200c010076030340c019a400800320700c82c3d1000c1c050031409183c1340a2465031040c1ca0700e034600c0e280d02d00e484032540940f02d800d1221300501409445602c00c8820400758844581c43c1041b41d040710920320710901e0720580d0b220808240888100a41e41c82840307402d001080340700c86880b004001e40303801e1485143c08142440029810030351091b00d0908607402c28040044a809800000d0440030594840c1d665414006025021550042400300c212402520000d60305039444c0107004072802802c448c0920354121524400017030300c0c140d105100c282120703d000b504058203451824211031902000318980500ca4004000d0034004000e00c41c2c1c003180c110040c0340340e070400350384011203a03c02030040811650007044107083c032031103003040c1c0b4015130300000d06010f2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 720922059 1250 720920809 720920861
    0x30408030a03020d2f03040f06052503020337021c060503030304020625051f1d0a080d0f0603080d0513121409030102040e100906060f080604 62
    0xb90b1251401403103135030402d01e001c00744040c658210006a042401807407001ca100f000009405d5000520844d4100382c1c002004010440da8402c8a11a0a18001c10090240705030a00c00b02c010700100c40c0b0301090700400810820b1000c410114140ba1a0900017802c1848443c0d41c10526449140d011030a851021074175520202d001c880103012071841c0441005165168010b0680740d05c421240030350000000c20401502c07980190f00d44020910301501c82850303401564a4a040c042c0ca98250402c15422201e4020b00340b61500c10b07011520403040380034408140c440400e40d1510023150026098550104071004041c0890f0850300480c801105c00300806070b282d1414400c250040e8482d1071003a4a445c001604405550a00112494010300103261380051a0802c460101c020230951400600030311407104140c83c24000b40010b801070011740007a62401601d818503031640b40e413001c80b42c00d0500c0d9080005c0e03078020411aa0503201031400500940d58078001c500903010700703445804182070786e205402d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 720923309 1250 720922059 720922061
    0x9022104212d14040303081810091101030e070f0b0f0c0604050307030e01020a030903060506030109020d121e05031515070f0c0f0506160314070302210403050c1002030408030a03 78
    0xa40402c29141d818a0809081d0103031070764025408000d000c140304401098440c00b080110751000301c5601e00b1246001004075480c815680b1040f4100d601d080d1100c4110481d48e0035008144450000000410401785015049100b01e80588a16540e82d9000180c800050269404032502905860102d0701c0506240c942140d81354410303c803ea0028a513040510065813010566071500c0ba0540e07280c28205040d912803078001d140142c801c0368990358410354400103031200c01c2031011007401290105070201440170054511035030303030120070020f94100040810042e088805c3d079820980001c11600782d4034000f0040b41003075a0060381340740021408a941401c11060001001d0360a100d1088015259039900c413024000c00e190140c6a400881881140841c85600044140c0c9900038a020501750241807884140c55100c8603040e0016040100034500d05c484401c44401043c1041d0041c501e854610741b078481c0c64500c502030261180700010b00703041c41079101701b060740c3c007a14003d0f003602d51b43d00d101c2c50301138 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 720924559 1250 720923309 720923387
    0x3010e4903241806230307080109060b0405060603010e070e03190f12020102160602031308031303020c030613020f131b08010503190206030406150902210421 69
    0x8009929408141802110b6004140c201d0f281d1800b1040c920014081703a0a00100c003061441d09403041c950b0000b1320710401d00829030600d001d0140080c40a40903414481903e800500a9002c2c40c0104010869000800400c5a01989900e44840b1150b03030040068204840705000414070340705040b065061140c4030a412200078030403031440490118444060f8281d0180c403000d022214502a811800300341d4580003594881d41c2680f8481811842d039803801d4071500241c4944c5044500c03166020205501000120000d1000701e00501c0c15180003003000d0340950020754000e0084d41642c40140d125143c19842c18100341042c03800344003901c0309481090405840719808000200d00c48000120750501040c94101003900802d0101108099000c1c05025403000d4401c403085941c1d80e03540c00100315132403000300c0a40b0401d003015a49a0004c145d1100505250200c0f10800004030705000c0001d0f40c241c034082d040d2103203a600155850701844143d5002204201189610b02442c110044a090207031880c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 720925809 1250 720924559 720924569
    0x105070f082704050405060601050f1e1e040545062b2d03050316211805061f0b0406051c0b03010e490324 47
    0xc1841c15100b60304000544a0503100a4141d410080c046811544a04010724610424140d50b0303242038584590742c02001c00300d400140421401140b10300300a04528240203441c28101c4c042c031b04227818680014030b034030030f00740c004c0c4000303103522883c500080040e190300d1468040c014030031010389602c05804204800708451003845104047d0b04009200c18030806041ca0780200d15032001d07906042daa40350075405403160007854164101c0200801300d03261941074441c20340f0a948580e2a8204003d80704809500c10141506200c0310511000c0940c00000c0030070009000303000e011900b00304031400c17040e031401c82c0c000182c400e0080400b0020040a54094000c1d05181c2c03e1500105660301c0032060f55600a9000c0d060000e0301c1045110103100c550303441079501c5c080320b14001a01254520000742142e103619450055500007403140c0a0013801200c5101e0030641006400c104444a214103809502110349d059200f00b4078054400b104a1082d805180c4020a0040b107030403696459041ca03d5140c440e101d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 720927059 1250 720925809 720925867
    0xc030e040c0804140721030c0b0106020703110d030c0b040804090e15010602010e150c12010905070807020d020d230708270d03051c05010605040315060308090105070f08 74
    0x100d001016030000701790b4203ca4980c0d448181101070002c1c00c40d101000300e00300390100903055040c2d5020820806040b402402d281d0018500645146084000740c0b02a40e00c091140c400844600003194011807040e41c1190300014000440c0c0e034500d40b01c1c0e881e000d160058091689070418090095000259030008400d80c10104030b000c3c1e9a42c5e10403400c0c0d0f0b8400081d04860b07001801d85020309215004003940204c4a080d42600381401300742858802d4409900c048440c07030301c44081c4010141c000300c486400c03464500c06801380266001c000307960f505400b4054410011640100c1080901098101c0d050100e00301040e0b80d144c145041502a41d00209003000300e42002014030003014903903603514202c1d0500a0181c600d07005894074207440326081002a90820941014140107090852040502901003501d0711900c0d14154184074200110110100002519007901032001c2502242170703440c290024600140e4501c0301d807621140d002c034030500082c1407980104503051400001d10307840c0410030404007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 720928309 1250 720927059 720927083
    0xa02010e120a0e030a020a0b13050301050a0c0e030c2803080a030204030302100b0904060911030a03030608100e060a150e0702100515180a02070203060c03010801150b04060c030e040c0804 82
    0x4201a280d401708034000f54040030200003000392281200140c02070343c1d8000d007005041551040401e0940b00c04540c01c0310031554130240c0318542c64200750406c80c2a1402d80c002c25081d0080408203400c0d4642c44104603080585c00501640c02820300200c2c0c01542c2d010102c203449400125014020390000e0100f1005230080c103a1b2070654100b50300c548020b090000303015003083d485503241c0710000c0c140c00d48140c0b400b03102c4100480d01c4c1c0c1c60400c003003d0443e02c603070703000560702e46040181414003d078088881001ca01f004d01c07503100201d00207102504054070b4800003800141c281c1d085004008158001001c944080040014841d004101c05035440140300c01441140d03a079140c515400c0700800102da502c805005507400c0c40041c0801d015504c03010b9400e005182c10450340000345015002c803405003c0e00000001400074100030b01501d41e90f540d403900b0404400b814221840d02c82d0182d400b4800401403081c00703810a042c4108100080180c01510800158040d8240184954011038007a178015440d95 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 720929559 1250 720928309 720928337
    0xa05010e0f0a150f09060e060405100209030604060b0315010e07090f0803160201030b03030c010209040b0102010b01020703080310090e010b040c0503010602070608130606080d0807020c090406020a02010e120a 91
    0xc0b9004440940c04407501c125a21084250002000c0e2152080041c5699848080001d0120701c0303071102c4d8208801c02050075251030316046207014803400c1d00050b01070042c8200f10b465180014056002039200c43c0100b103a00b034510100c2e182c603041d149034011068032040000b40910755848207901520840c3e403480d6500740c0340c061841101c5020301c42c0b0300980d40104030060a801c0c080d5098240caa00c1494049010b05803d00000d145400c9a002c0985903507000510f07124a14103032040c911020380a0003b0b0103d004c1d5000041e4441880c0d00c805460588000001100d50344003500d103501800680900f00503110440c0c00b8035000300030035415103004502e440303040c0d81031078010815a4101e0b4140e600900d41d260070020200e50600003c1c01030101c1d403040701034410001c1c00c640034540c0a081980c0044c2440307801d000d801800c03c0d00c00350030081990004c50f1110016110300b10040e9015420a0740035948581000d17049006048019807161036009004400c90024039041c02810080202e60b9020301c942070744 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 720930809 1250 720929559 720929563
    0x306031014420a080f030d050f010e01170a080403030c02010e030a0803180a02101701090501030809090c0d110d2703211802040f02070506190e0a05010e0f 68
    0x1040c2d2290445441009180000c1d81d1802a940080d8000c0c000340103595950003a0b0f0701d00100d0a00010154102050402030203801e44903160340100c40e0001c000d1594502503500e01c240741e0601a00307100781c0b02181c458207010340030860503801c164022505603450340d5038140201a42d00048040b40064503a0101c08100e1900040440420340c2044a0328078680707444400d001856410202c100307841c0110403660003d81e85400034884171462035111ba030806000c2e1100030541030302c16048901124036007001440800ea0420a4a400c450251900403140e103071010240198084c40f00c0c0081214280061511094048805015000210002480041404009410b21496805080c0706000c00c401e07001c1c0200340305142c07200714082d4900d1465841d00c4010000341c00d580c802c03400078082e031241e4030400d4211b040c0b512071203a2540c0756400444c208107169483c0c9441e03540c06480190b000c2c48049404610303c2040e403001500e96548402c441d02c0c441c02d80362540c007030161030820580d140034020a07000360201c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 720932059 1250 720930809 720930871
    0x708100234081227100c0c0f080315030f030406051810020a11031911150c0708150f150f030f0c0a0602150a0203071803061b050f040b0306031014 64
    0x12401404c141407045007494002c24100c81048101711f1a00d1215020175406804215283d0060440507924500140d00f9005070380c0c500c4856002c1d520480074101600c40110664050f00c489181850ba03620304100c032419200c0700c040c07001c1e43c040c0000100b0f001264002070080c000c28400d00c0070506039004030b001c240d2281840b41c0c111240b441c0d94503a03007000604682d0111800e800080c8142c4140039580c42d9072040e03410060b81129998090082807101000070881001d04c502d595901c1c00c1d09103000c2c0300540106102401400b0700317281a10000802c1d641e10312880c800b03a08082c04951640c1e0100700426a01c0030990081c42c0114550000802c08920126480320200190164240c003a140e41210f98002c1d40014050010080034200b406903070044510f0b945c1c0110b0240790003040300c42c0261015000714a05180308414002c1c108419a1010064002d0300c0c101c9050703580550b20795032002c0200e814003001c844044559494803400c44801c00d210128680668404d190640a100f1089c3e140c02440403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 720933309 1250 720932059 720932131
    0x1802010f14090105210103050a0c1e0915080d02010f061a0f07050709052e050a121b030305070c1703160201031d07081002340812 57
    0x6040011a15550050f1300400c074881c018101c20f030008000790007043c80c04100782c000b281c42da00a0300d0804180851a10390340c01805242400600c51100c265060503540b4407841000c03409515240f20140c803c1248860b8002020003406640303408042d420000e0091284280605109141200124440940508440c05004004225803800c42106502141c079000300804440c0c0c2d1140310782c0811100501d0044902031100a0f090f000c0c040c8504101031101114122800c1c00d600c1e07907010801540d6201c0711800f04413445d0218036440ca03411414075017844010001c00c640c44c2c1c130b4a10f80c00410198010700409102d805480241c2c0c0d0701d43c4075924014100000303102860383c0d034028070910081d4416241c0a5007018414100050055102150181611041d01c0c80006035000700c0c0003040140b005220b0410384030300000341145032030a04070000b20f084500c101031400600800f48003c0d10818401b00c40c40c0b00903001010a500e42204c0e118041c1d440c0d00881d070303c560406030139141000102c81c8100b031650240c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 720934559 1250 720933309 720933347
    0x7060c05070302091815071b030c0212070e090a03090501110a02010518030f060f0109061d1b0d0c18240207120c080114100902090607061802010f 64
    0x340b03940c00700a0b050070701504084d200c080e05860551081c8081024003c070811224543c982d80c07600120252621603d44406100009103030044000280d1048244040c2e03a4101e8050102188459600f031800016400040241143c0001c0c401d1041000981d504074921036038803108115156030044502c0c1c10400d0560b41b0652240d01c0b0a4010340c01040031301028482c0c4030641403034003c42000030746400941801004c168020302c00748644c0310740c50400140500044d070740600806145c1203c0d42034414a0300c05035203180e0058804124602e45c101140b0b01c4103201d660580c3c2d104c4541204600080440c03802e401c020038180744c8030200b84059012003404851a045103640000c3c003e1280d5032441d072140c01c2c60011070103092804510000c11181105965018644005030341f810121154212003401940b0408071b40c0d1403082001d59186072a52000b981c031081c2015031692804000700d0241c7c0500c0720700900240c00c060302d0381c001030729035220b8200d028003d82c2e0704200150422015640075040084e490360b41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 720935809 1250 720934559 720934573
    0x120614190e0a0c0509040615080a020c030f0d0b0301111309110412020a0506130f091103060d030c051c0e0d02060906130302120c03063603070b01150207060c05 70
    0x3420ba520104101c089801c2c102c0c50590300400080880380c007074100d00c2129a82c2310072004201d50005280c2ea00c003060410451410417503203030003550303800396a00300c4a804070005108252007019801c54158488050700038000003a0341c0c08080c0307194006081071000c4005880380001c14440f00d0045802101513071544502d41418051455240b07520800c0a9030452102c03200003403940c079541e00801001e1420703090006507600300032038032000c4240b41c1d1241031200e06020490102094242c00ca0317400041c01c440391a00c000c2030303280607121401e400034042d110740518002c9912100180805882407100369a4500c51104214104114007410600c040e400c00b0302802290002c0c00d046004100e88007a02200c221040d0340c940c0042c4d0402000c3c11006204d07040720500700c032642030410047c1d400000e50b105c0c03025801004010540d403060710100031200f4040103003411110610a1049840003600110519025031310341000c2c0c00a41d85040c49000184501d000024815100300c00c0b40040380d500c40c010b4520 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 720937059 1250 720935809 720935821
    0x81006060f09030209010506070204141008010606023403080a02150718030b0703180503070c0e0c030402150c010212010812040e190621050c01030b0d060507120614190e 74
    0x56904000c2040360801d94940520150703070008051280704021400b000803370707181860099401c0d02c1d4541c1c490030955000002c520b184400d0300103422070f541c0006582240a9542c003064900302501540050070030000090500c6071954049245910b19202c0c400384412620f440100b01c540c00700303060201e16070442590050000ce9031840c05107030004a40c1c0b07000f2421202412403d43c13406080c01d0100e07056480041c00b042088819100c1e40c2c0107009582e040310591134020000d60071844001c1c0000d210700b2182108004141006003500d42840b01c100085481d00001d20b890035004600380500c9000344604200c1e04c0340340b21039800321410796074000c0682c40a6219032a058020480da851803803044d0b0b444007008140a140f121034003020320303801d051640d41e40c40a42000350603c4a0009024101414411901043d490750b00003440240d03400360b4005400d51380d98108407083d50030b42d19001440c03401c00200044440b8440d81140d422308003102d480c081034003900440c0e01e60010034030600001159540000c0c6c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 720938309 1250 720937059 720937069
    0x305010510020a123c0503090d03090c030b0a0203190501060c0206091c080301030b060a031a040318080102071104090f140304090f0501060e0a0605190504081006060f090302090105 79
    0x40b5504050801a13100c0c0c00c24441140003c034940440205c0c409105450703008a41074018580c00c3c00c00c2804c01e5851410114943c580b1000e82c4e100038800d054440c0d10090421039648404401503801820b00803450520f1880040030754010740d003014840100251040d04119103110301070403585580c40b14110402c0a500740012600145002c6030302041c040c8001c41b0100e80c00d800301c241c0f1031150b0381603a506d60642c41d0500e0480b01c040c1c051402400c6c039641c1031000071060395a2a18801c101609646903a460345800c61344102d101070820095414140002804001500949002c0d48103c401020f2441120140021039080c80d4014190440f007a0030782020504116500e002c48080c08280d80c0342c0741d02c811034581aa0320440300700f40c009640744010454140e020380f03020905032007203031210709007460044010301c10300500e502030b0780480c43d102c04040864041e0007107030002c0c00c0312815201d4802c4900840002031038184900000b02e0400314044c4200c0348150800d10940754001c01164599080138140301c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 720939559 1250 720938309 720938333
    0x1f0c02120306210708011e110a1d0a0b09010207090b06030609060123093f030d0e03041a0708032d090a0302070603020f03010510170403090302010305010510020a 71
    0x402c0d0400d40004000f118442400070101a00c04100041000c007581c180d204292050032078000303011407400107401c0d065a2000e0454002007404e28118490340505d05100d18500d9582d8502c1c1da00c4551580f0004000ca643c034003a14907284244c0aa4900558a03000744003903801880d00c3d161300000400000310245441d005464001c0c0381898102c2d64142d000950741842001d0281d4a5100c0c9001b03e03942c0301c28548ae0320b60300c1038851540380c40d0941d0407000341d08203035100d4892100c150123b0301150880451004200f503542c02030b000c1c1010b02c0b0f44441244101d8032036010340101500c3d01882030031300e4010b0700301034111100c040e030050500c0d180d507403070010340a2502211101d211a110091200b006644034113003206010f500040c0162000c40d69902e00607103002601e0384400d003850b0052185c4100c690040b070559045405c181e940802c11402175004030740031508840c8003030765011041f0920003030641c00301419050303a04c00e0b00d00b08a141d0700c0e5030400001c8154503281c00016030180c0303900c10000c0e82c1c10f0100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 720940809 1250 720939559 720939589
    0x40e040f1113021206120a0624060809060603030702150904090c0905240a03030825050309010c090b0d1a0307062601060206130c081f0c02120306 64
    0x541c140380d40024000600c10402c0404498012810086445800e00c00c183c020104032800c19102c4070040c1d080342c03251400344003e89603036a1880b0424050008504074000032030018000511a9101d10f005442c5000683d103074070b410303c00c110004090b810300000300c0d40100d40086c0f0088100845900b6065242e000381c4000750461b4403024440c0000e01050072510107002642008545880c0140e4101c003022440b6a4001001c0300b002c2c0350041030b1f1111044a000c0d1398241c54003101d1559600c1250a0511524020002c580f0005603851500f580c0030010750300603400c640080c480812060001c440c0c013402c5001d559010344d4100512045803c265009032490301108140b0805030080b43c0c000390508880f03034005c3c0d0125589100c00781002043c02030303981c0449200500150b003541000c6000f551440001c0080348040880001c00d010300100101180007020350720708484143c9030064010040c00e02c0c0c1c190707414036203041c520554215400407809990551204900c40c2c1540d486004004000c0418500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 720942059 1250 720940809 720940823
    0x30e010609063803070c02100201111603031b020109021f14090f0a0f090f0615030506013b030a03020d1d0904050d090b0a0e0415080f060105040c020102040e040f 71
    0x200d040f840440000c2c51054080f51601d5105981e14010f000811410554010031a4500203c904142981c1001d80f4949c0080414280d042c41030340c5015801800e0301246203c0b44203003c10314440f2203505400c0040040c2c8290f40550400c2124000000810071550441c40440e6031134103092048990b0002410b0a002c0003401c03d80b5000d0040302050707040d0580c0d0440306108174400010b0200020a0165800c1900355200c1080f1131854090900301c84412036103240c040640f03801c0402e156a00c50344040d02400104103d2151244030368a43c4224150ba40714108202411012005614075003c10aa1000c135099000340c40e900f015a041160311030035a0018400700440d20783c43e012642c448504251007540300710300806200401100241c0303070781c04661203d0700303144003040b034a419075030b2045041141c054250b6000ca0301100500b8080c4102c03041e070304500d0103441600000d81c1003c07400076825040310410344e401c010b031103c88030b022801d1707200e40e00450a00030b010700c1c045030020301042c100480382405642 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 720943309 1250 720942059 720942149
    0x30f0c031b030406090b0c130e040201031428051e040c09090c170102040501050a1803150c0e09010f03170c03030709031203180b090a12030e01060906 66
    0x7000c99820640e000e032103041e6541500c0003000b540082e01a0401044503c050410048860110890f4424000c01c600f61581001140031a40a50001114142c0459040055151030007000c4802c005940d0040c081c140c7c00e070400f082c05134035031242900810120070b0503003030000a03e0124a132500080c3c404c941c4515203d80001c2d4400341c2e44104030300a40b140e950004160f00d411500140e00300c8210348030350b0903481084100f00c5aa00b00e01154030080180c14150000c9800d0540c01500c0c54140c0d001500d100c0004200c07201411040e0302c108a44d4510340c0b0b4206880d03e004c42400644a0240214090b0003800e507004e00209011303081140300717800b40d4080503150008040c00c06c0d0541d00b00341c03800404160b0340c0100b40104403120000c0d0001140d02d02d400c10440400403404909604001c40c080c11007070f8940003044407010140944e903540c52704210045542c4800c01d400600030019403ca8414551a1a0780800e0300215401050304541d0311420250010b40c2c0d0308004044092000603581c03644000c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 720944559 1250 720943309 720943351
    0x206011d16120c0f11060108210d1401090c030504020f060702040f0c0f12020f0409050606070605090304050f04050105060f2101030803011a0a020a060f0e01060b040f0b030f0c03 78
    0x10094032100c1e40f2541e203e910204103000302510541c0c118209101c02d4104d83e00500120900040c000081d071040700e000d2a880030b000c0001a150711580c0603414420b4101141c20000703502d42901b09040f220032640800c010b0020b802c0407400c444054400035804440c490310341010b440c280000d007a40a00003000040c030550b1036152081118000340d114008139655030006080160884031002100011a00961911140b95800d001c0e038170903801040e004659a50205110342c81d10420b843c143e0b58410000c1101d800e0480f12607540b41c115218840c400d0801455070300d010f0a041c042e10b4101d6101400a42c2400c121264440307184d0000507140542d8040c00c40784445030b8200f420024020340c02482d11a5895040807003500030072980741c0006510b540c0400421801941c0018213101d40703074102c100003603002b031b04403003020103403808400d111125820800041080440700e00200200c2e007032001e41845c0d29590b907422020070301088801041c89201000042d80084540005513800100c0102c0b140030003000c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 720945809 1250 720944559 720944561
    0x30a060b180a0501030b061f140708071a09010c050d05180a140d0f020d180b0d02031f060527060a020a031d0f04091a04120206011d1612 60
    0x2c0394101000c684400041051143e00001250008001d403122480310b042020b51a40345008031440c5010014100941c4c210519a2000e540d200741d0b20900d1141d4841c15418009030ba01782c00e01000e0000c6d035898011401c842414414450212100d8070b03441c0c184032080c003004000786402481c0c0090071071399404120020100b03005143c401c81c4a054806052511005800c0c80c0c110800303081418042c1d103030501c481c5640c000404c20540c1d5007500c8c0041464518240d900c8a201c0e503507020320143c1e00c002c250b04903200995005540709400c03803100307003100c0e80c005140103011001901c00d41c03002c1003080040701545030708004001001704010f034010100e07800c404007003505a4800c0600310f00513004541d9120030560f120b1090340e01419060304440201044c000015140140401002d224959034210041004280d60102c2d2452800310b5105425103400c1c105020009a130b1041000140a0340c0000700d0044003894100d400518076854140c40c59503488025610010f200310b0711028803c80f81c0324401002c2003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 720947059 1250 720945809 720945811
    0xf0207050d08070305010608040c210623060d0b130c0305030a050417072403090611030402010f140f0f09030a060b0f0d050606100921031706030a060b18 67
    0x1c99a2180e14519100380020100c84040e04807904000041080c8000b05203038003408001c1e2018101e8042a5803655002216052211100102120309000303815600600c58400a00011150040403002c3c0e69088200004806002c1d0020050304c54040411100c0a60011140c2d416118a4011050b0780c1ca0ba1130303040c910f80003240f4030300c005100041d092080c0c216200c102401024020300404e02d083c2046c0ca101e10715243c0340101460000e9041550807501c0c0f0a801c40a0800c0d088002000404040d840c030700da00794003c032016800b0903009004141424801c82c00440ca1148020249041541600d031061003907100c40c2e10300050103030130722591203941d4003400b9030740e00340344682c230009400e4055405001d403405041d00040d100d032058108410200c0d00105103c0d42c031400c101d4820741e1500c40d1400541e0300b608150800104156003c0400030811160080c50703034114000d4444d250000306146040301d07503041c1220030300d80641100010b000020701540120440840007041500c1020010381c148480e410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 720948309 1250 720947059 720947083
    0x3261213030c0510050601030609021207050a0302070f060605010e121c050d0e01050910060f030f0816060b0f310204121a0f0105010c08030402030309040f0504060617100f020705 78
    0x250710006d01066607014410f0380d00520b04000c080d400c1054620400000b104014521410301c040040d8081d80d00344240e0440d000694414440d055094203420700340c2c01061b07a40140c1e40840e00c4401980c4451400c4440740b2506851840100040203e0881d004010081c1505210a010b01070000340701e030107558040c0c244004840400000c013407070507286091800da1145118601507181000038000040c203100b4000c1a030342c20082c06660701103103150074030051054901d030340c80c00e22104045000300f19058001040c048412a4030b103103d406c200303081020600c13180030302000c3d00300518014001300c898240c003540101e0119500600b000d580e10514803d2180030541118420202c101d98020241c0100115400000301a40b50509605150018200f0000d003403010b401140044006011554200201c2d00c0404002d80305202d16800d400001c40a4541945c04960181c1401da0108040030500703650340c00c048401c0e0080a80722000c5004a004000c100c02d640c00c619004c0003404c2c040b640c100721084c0e44e01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 720949559 1250 720948309 720948311
    0x1050d020412050c0108010609050f0f030109050a171303030e0f030d05070b010e01080d122306030c011403060415050303030c0309070b070203070504050702031303261213030c0510 79
    0x42c0c4145030190512010303560f80c60500c82d880740140600c55000c03169505680301a03c070a094604400d00003078042180790061503166080091035810406e001c216800300e94030131505242d05144d25001000c3d640602c1c0d203680403141d0b084000300040784c420f88001c1300762031014013106110000b00c03020030b0030010720310703002c0002c620001011801c014140f00070703900410980209004079410700d9000c98503144c044078403004001000200b01b24402c000d5022049903401c03484011024900039440e038040800440b02d1901c44e0144129003642035018141c0c0d4040002c3c0d224456146030381c2c2d041044010b08405000503855000c101010075252401c20043d030003220084d0b5940d88918081001e42c0c504400358001c01c1900c0821f2100c3c01c01610001038005c1a01e404603030104256580c40c80c100d25600512400c40e400d40407007040001841030445400309400a44464000302d0070a0024100c1c041c800e0300240d00c9203941403400174815113880c14a0f2040d4074424a41806240e40ca84c0307170f0a140040200d03c41003c9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 720950809 1250 720949559 720949589
    0x1b0f0f0c061204230106080d09061e111e0c0406050d111005092e0509150309010204051504080105150d1106090604030c140109121101050d0204 63
    0x68001088100c440c0380e8101d038150300d0301c4441104070b501d040c8080c000824880d030304140f401040d00203a01c01c2e10080104402006600e9650401d55030b00c280d60007411002c6507034400081000f078401c0c1903004c04078061007a0039240100304401211243c040c100d910542c0d002c1c6001d103015010000c18032810901c00d2000515140d60b80c18208011a030b0701e07510081c407404809141c503000600411a0b549048400c60344c1d0000c1e250445000e42c0d848c86150070880d40203500708a4040321020b0b00381e200100e03800a4200400045d0f0398001500c8a106529100c1d2740211042025512560b00b40021944007400d00f00140c100f5a445000c20050344000480322440742007c075080c0700c071400904c00c1d0340d0b11410503c2e540c80340051403400b14640070940000500490780c50111035644e91a00021500d002c0c81c0a0041540c6658074144030703c0b076150b5406090180404020503034150741c86001030030f065880d15554401e40402e00c0ea240807000c3c583c0c12025060003001d2000b039803c100984050300082074041c00a07604 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 720952059 1250 720950809 720950833
    0x80106121e0507090e030d05090303090f0303010614070501180b16030203070e0603150306010605040303181406070f0f0b0402010806030a03080718080105011e06030912051b0f 77
    0x6040000e000c0020049076075031041c011070400074420f82100d4040e81c0004a00c614401c400303056200c0d078001620343c1420303d424408031200c00401076100d81030000980d583c2203110000c840e260f01c001e00c17034440094880d8450542d42684000102030b5140300d503000262928090b194000301b000b545400b6902990a4010400788000c0c200281c0020302c11890300714954900944050440102c4018440c0910408070010b80901e5501540c54070400009040380d03065079450710020103e9026010403000903685502400c0c4802c00008900c058400707030145c0500031541003040c80455081440f0507680c2c40034420031400070030965003a11401c0c1d0300800600580d440c15000160005202500080c00b980c000b10030303180400d52080c0c0207600100585001585c9011103640c4190210240e00144030552901c0c00008503288400031820700380e00010000442c8541c1e4080c01e8013255020034024000c02607441e0b00d40c51851146004044401e81c0c500a50000003180e105146032030032a0f4003901150f0f00100400d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 720953309 1250 720952059 720952073
    0x2071e12020118170c062409042105120703020702040b030c090a0f0e19020109050a0b030406200c0f07050d0c090207080903151023010f020708010612 66
    0x384000380024400c90709000030141d40c010b6452800340543e2494000c4201c101011011070340b41c0c014803030031605c203820001c9188021401524a02d2280d0781c0002c0a94102d08080071070f184540d030890000a4001201d96090701091005d42c00642007000c10070400100010489400b0300903881035034010384640c11481807000f00c0305000c1d1000c1c0309a202c1000824030382d0340c10803c1c0384d000c65548004100c0c00300750001c210150880100178901c50042946a030f014441c0e40010010183c002da0b80c29103460365800a0100b0810a0300520110803000c00000700403841c51f4011030a0b0080c2e0840c140455074a0800c15501c94006000a12190300041e1a142c41c06208008880280c80f084500e101d5068050b52a07207500c003040e00c628140f02d034011a210050181160556000c0a00a419120f500303c1e2060007030f40441c1d04450040d800580b0007008102d034000348510640542426040d41c1c554268500103403803160103244e405045102c0e0440c08294904207014050060003840900b8951060a141c080f17 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 720954559 1250 720953309 720953333
    0xc030c030219120210031b0302031608040f060207030c0f051c030b0a03110a0e0906181f0b0d080408010608010e1507081519090e010b01200102071e 65
    0x52152000703100038810101820b90031412960704440c02059001c5074135040c1c1c041c1241001c40740c00407105030001b10047e501a0000c510444008860002810480b84182d0390b80713905a44c040c1c90000103403200000642540e004200f9540641000030558089607500e404038604010221400e42180021005448601254241050316828144003464440000c5140346103a44030142c608000320f601c0c583e036601d0352486240a444c1d030106c800b0b124a0486d055550301d0f4801e840d0844c1c4440c8442c0080300541002c078034485914008014034400b40e0040c500b4030060b02d102000c00390300c880402e50f0440002c88060003000100003190010030024509250305007114502c0c0f1815940ea08440d00d1007103840f682c0140e155016009040c0602203850364095403071340c0302100780d1070394100d031855411100314490060701100310741a5410074000c8a603888801c03400d0351010100c941c04140c0700041c000f1b01407950021004000c111400044c00c10758951a01142c1d0f00320042125403541c0348007204001e01110300088 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 720955809 1250 720954559 720954589
    0x206070f030e0d021f140f04052d060a110a060507090b030609010b0c120d141e06061b0715230307080402040902060d05071d09010b13030c030c0302 65
    0xa6120f240d5035000300320000b18000200060405540c0141d1710103004040000c401078003a06a41d80f9034180c00031025982e030040c01418412284c1e45011030394410360750700c0b2100ca10440c20304030381098003075024841c1580041e5003440c14800e80882d021500d0008104140300d00e8000e00000c2a941800d11014204d0055038208400c3d0500c200208a11611450045811152003031049603a800e808050fa80c20102019500d40d98444001201c0422004682001907005070084850550340c81e142c00d4070804001e054a000c1e020b03401040041c00d1403900c3e0014081500c1207c1d28154400d001c1039903241050f120b5002010b200400c6100c0a00459000342094034a1444200c4a24030310700c4008036480d140401404601004101c1000508544441d000400c903e5805010301d500e801513402004090501152400c0004482c01c40342800c065840540384103040003c1e2104c0c1d0300e0b03401d14000c414241e00200c545401d01c680c031200040010fa80e520401c3c000c5004404203d801401e501c10092141881485c2d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 720957059 1250 720955809 720955819
    0x403080f092a2205010f0902280905060c060108010c0f0c0f05030d0207080c100218090a020c0a05070e06030102091e010201060b0406090f0504090317040804030206070f030e 76
    0xa100402c0e01860030400700d4040c0c072146001034840c0000f8112aa034120074405900803480d03100901801904a44d0503200c240d0341618405071240d0b1004c089000d0f641349480595106088420040c0c0b082e80100000300740c52030440c01081d00c03030b80071903899409824030075016480040100041b80081c410380c0c1c011070003403502000c00001000010480244210060400346881c410b0208000c0c00700100d90001c90312000a640b50384260130700c6083c0750040310380413880707009900d600d00c6103074082e20890785000002004aa5040800310502030900e03c01400703004415820040c041d2851410480c5104140c0708000420b452402d04010415002016003c00c1c040e80c0140311016107a84e03903260740d0951151429102d480d890321200100d015203c1507001a41d0f08038009004980142c1c04400d181c1541e90320700300d00e14019551014013003224031221002e40000c0010000e0030780303602c603121400c0d0424003904426003007580fa9000104140e0000d00210b560840060302c51042507003103e62640c8801d0120340d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 720958309 1250 720957059 720957073
    0x9161803031707020f19030f090b180102010603080d0e1506030309010f030902300703050c01050310231305131127010303031b210b090403080f09 64
    0x81e0180103021800801c000345410032000404a40c42040b0502c1c600d180070086408021440341158100e00b02c00005a0005156607828000180034018040c00c4841f03400d10140361640c00e004401e003641c0702e460075504554179068000086051000034001002c1e0300c0340000703070404012002d9850020b004000e205404900c2041180702d0368040107407043e5480a080440344502800404c400800041c1002036000c06a00c006169900903521101050050346c1c0380440d08801c01c00e4203a941d80d4440c80000c1c1a43d00540304554903500c40c5015507003028250240d044165120000b00000b051a001030703040c0502104205201307454803040000c02d00350340380c00c1001242401085506409007020025000000340085002d0644441c0780003546d0f04241c0200610354003980c1ca03505180e28080c841500041e00b440070324408201c403418491a403030300c20785680c1d4030900c0080502d0301a00704134103203d40c0c007a1b950081d44082e0b01c8800d000d511071403103a0b0340c03414a440c4c400c24a440800010303100f24041d502c40a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 720959559 1250 720958309 720958313
    0x908031326030a030b010c021801030204060b0c0a111809010f060b1206010815041103090c04181b170c031002040b0d0b031e1b031606081509161803 65
    0x40b089480c860014680070030085d034500d0040c0d40c03001748410000e412004102d150030a0500c03a80c90705050300e1003110240301c0c09948450b1442c02c1d024520003510709070052810400010350390285410108006044101c080e106055142038401040764640d842d40d4444019441e072400f1403041d0f030064503007540202d007003004280f80e0620700400107203042e060040319000b05101c1d1005440ca43c009910041c000d110341803030310109032029001903e483c40188290740c1944281d10340360149990251209a2000e00004940c95602c41c0c0d0001031810310701d2141c00640481c0c030010718039001040412103401001010702c3c5d1001c0c140742c04d48401c004044a071040c031003400540e100741d00f240c000450510002c100002c2080029013401f8200a0a4203401103019802081400209401c1600265818203038510901a802d0507102c0004900c45d084c0810740210500446010700c403156000a046090518a40d01c24008940070480954405088018102209032103580c02020300400e1643d13500101c2010f0301c6c507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 720960809 1250 720959559 720959563
    0x714030c0406030e0f011118040203160c0f08130e240622080d11030a09050904082703071403030a0e1306030609141c030c0908031326 59
    0x280a12002c05807180000300344214200b02172035980051030001c0004201000040c00341d0f62000707c00d403100100e68800e0584501d01407094900c2010180d20710102851411402c803000110b00408840341d00c01c40c409000452101c4c400b610b00c00d001a84c3d10559241800080040054020111036082003a0408a144000d9002c014901c40c4000d0303400719280e482a9002211502000d00d488480b40154a4002050b02c000a40d980526100da21841a420a0018815201d22641080328007069240b07030708025505006800f294454050030741d00341045410581300c21402240342140d500080e40090049442c0303000d10201d0001d0003001c00780c503e05002480805e407a40108003d80c0700f485103d880440701500c540c200340e28a200046000c118503500c0b841d10034000e10506c4415141545062400d0a00c1280011610400018035101c860700c0c1c9044a0200e02800c000c011401c10030000083c0081c2c11402000a44200c0c1c0440005d40925070030141c5541100301c1d20465044501c0b1000140302d5403201c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 720962059 1250 720960809 720960817
    0x1030b030f211e0d0c09080a110112090606080d0f090521030301080307060c03090201120e2d060907050901030b07021204120b090304060504050d020d060c080714030c 73
    0x1e200b050040300c500040c2c00e41c0c154003d950301590200800b0051065010600c40101250501010300300001d003003451003100c07a2031160181007095401842100b0110310342c00d03605015440149030805d59000d07081150001d44941c1903046a00903107402c3c003440f0017103003801400ca48000741e20b40320b4013501d14080c1c000c00c80380c981d05c50b441c094030580100c01e003459002d81c0203e51841141c401c5075036075650b402c0529075030360040340280d803038602e81210020700c18400e0160065440c2c050f5143c03c4400d110898420042c0f0031545022602c1c45401c4100540c4107a200141041000c942001e40003801d880fd007440c185040106a0710060700090824006641c4140d20075054a030043c0e003040e41c6035620402030740342400a041c0d01200b620301140000d00d241c80c980c5504441f5101d0160000243c80302101d03503950307010710b0183d5008103500340014800d505103c0c200300f910030300050105810030000c0e203c18048440f203101100000e08090100000c1c1508042200208082403400500d1850300b12080411801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 720963309 1250 720962059 720962083
    0x1f060224091513020a08060403090801200307030b090a0207060b0f0607120201020405031603020118060f0509031006030c050a0e01060c0213150602061801110703080c040f030c0501030b030f 83
    0x80d00402040b803c42050440320307403541d4090044080c80f62a0244c00b503031008215021030000e000384a0100700070304103000f580304400e18241b46c0c20001041c5443c074441c0c4e800052010081660780c65070b4030102d503103003092140610390080006039078000c1810b10306e0039540044170141c054980d0500211154030f6043c101d82c60ba03600010841c15640ca91182240640700c1d6500241e0316118007203109a04100800d9881e04491007601d4180c841c9e081151441c1102015110b40c0c40420300346540310340310600403401042981d100906688080c3e008030b5150080f124203800560354000b000c1c00070702184c140001c400c4c001d00501c03240c802c96980740c010010421a005c5900038040c00200c070840f040c64409404c06034004610085003441a40c49600080d5a90000c0b41c0c840c10561403c00c80b01507403a01842154107182c0c0801032a440c1581c50744080d0740582000e000c2d206010800c020010b9020811000000a1849180a01032003850007000405803421906494480d130040c0c01140c80c00c2100282d01e5944071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 720964559 1250 720963309 720963343
    0x12010509070c06090b0717060a0515130e1e010305060a0f0e0109060b09100608130302120a020706140313020f0f1c0c08060c0f031f06022409 62
    0x250341c0c824101c030081000700d03004041d181003454035800c000c4000c0d44241300f0b010607520008500004400b5085025003030b104981c00100e4003006200300d040c00b0400308110703140e6800d01450865804a0961080b402d0352002c441c03440c8850900ca0300d034803203084003503400d08450544070940d411901ca00340c84420140c1183c001558404003211141e4082e0000e03050440c60313900821480d075840c109440a44680c07001d0078421a610000990b030b559000b044101980c0d1503998010f92580e510f8800e4884803503d20301541580304624004c000d140e507070702c020601c00c555540a4600185000e4000d0452103006140907146401401088140c56003010740c5051180c04072223a00c4254009404038441c1841d01d9505900400340c01444d020120f4040006854184140c8030800b8695460000e19102d4001341c1d101280d02404000303295940c6c410300013654205c0424055813000b6850b880707226812314065402000135030030200c3c034244031401c02140d0741c00d444050304000c000c0b454414440e41d00e030008825008030301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 720965809 1250 720964559 720964561
    0x5060f04050319211e020c0a02090a020405040c120f06051005090d080a03090203190816110a030c092901050c071e1503110313050a0b181212010509 65
    0x10b24403502414808140399100104e803044404d0401014094001501e54803440880005819065600c01c403007080900602030300302100c40d0b900300403a081003c0e06221000b502884049042d0361180708803100c03d40c140e2a01c2000f500c6039178030700701a1080043c040303007454a000020049503d401c010515013050610f0626510600c0d040041d03440c00300b065015004420118460710866055440343c3c020b140200e0480d1071442e0040c14482241c3c00389240240403520511142c2c20b1407489849481802d8807076210102d40039103540101e00010840c7c0d000744c0e440d25141204000c0300aa41c1321f000804058010f0b004d14170000003036916034030900030f0503460400c8000140820210014011440a02007402644480398007091000c40001c030030340070300e21011000c402042101070091085d000c0300380c9100c80346410340d6207000d00c0030b605642c2d03424143e40b60301032061800000390701c8c40886481140c200c44410002041039420914280c10b660100f101e1040c100854102040d041601e0384c110b0740101e4113a88a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 720967059 1250 720965809 720965857
    0x1050304031107180b19030b04021503070e0907020d080c0f040911090102010606051312170c0d080c040305060c0a020a050d05070209100b0a12021309060305060f040503 74
    0x400c42022803001c0503000e4100c01081c440c0e00d4090b4a41c0584c07402000b03000c03a901c01800c201da800781480451071400d00303c110400006641e9038117075a00500052110303100348168405a0100d030310032542d1500046800d10400b100345003a0340c0705600304c205440140100d803805100a8125600908207018410300404c05140f43d00d02d15007250040c03d41d6041c284000d000d04854060b2907000401203c0c00342d400d00c400070902c24459070035104070076102107407150b51a01d050603a00911310144000e9610b071031403104a000c41404900105030041c3e11100800103200000c4008220b060090101c1640050411003007020a900044081d0010341e02e03201d0f02e0fa0f0340c02000050781b40030b5103400000d00c207004442d0b9403003003030350040040c05450340290b92020700b41c1d5800c0140d0407480104c0c040d01e295000c0130320682c0501442800c0c0d803003001000400040ca4100b8a240c44003c01c2c00640c041700b081c0e07031904006e00c01c01006110743c3e504180c0c0b14030001040d007840c1c0d56054a900600e2011811003209041e4405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 720968309 1250 720967059 720967067
    0x80a12090b0628060e0a0905072102041a03181c031802030624060405010f050c01150807240c1205130902040e07020c06090415031a090f0106140105030403 68
    0x1560f40b4060048100c5141d035001c000d8410306800307500c3d500c00c140344000060344900c1e5000c0c451081060f981c802400d1201c4110074041024407403504d01c0c10320342c01d00010440700c060078100d05261600c203d205403645080c0301255840c0c0c00d5804011031540100903064180d4409110101d40030100d4140410504000e0034141205480031001941c54481c01d41400300000d801c440c4100444c1c0f090041551911008052012501c0745110317883c0000d40202c80d60b040e25100e0805410200070f05070000c207848007141c0c00e4482000c1182c100c0a078981010204000c100e80110100c0c80020081040c0d80303030342c09590300250000030a50006802145040c40841c001e45c410000c40751040444200010701c19280d00e10b8034000d4205018904c00301c0c0301000424820745c00004c0800b41e5000c01041549003500b16802c2c8000b0340484010210021203240d00400007039840c0c07041a84c1c10303810420300c40d21890001065417401048604007611a4034081c0c05122081c6a241d141c10b4009081c289035a60341c032580ba04032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 720969559 1250 720968309 720968359
    0x91d16060507112e080403050a03020f13080f0c010309150b06040b03041a090c0a060311070c0e040203280209071e02071e18051b0304080a12090b06 65
    0x3940c40807a604d2220b0319803950043c01040070254a5500e000d0361840101654008402e40d40600811418080d9107410307842030700105482114142054103200d081141e04600800e00e40048019411210323070981045810051441c258400f464284002056500d460744846041c080c11607415481d0320041e8090b89030681204c001f0080098441d917245450704261303a8100c00117481500500000d40800c00320800010043d810b01c2d8010140c0c1d050614000f01600101000040c034061800d051158101042050b2015002000d0b4103c0340201031600703204040c140004050000e001c01e0038103000000703d080c0000c40482c4680e05540300d52464881c1c100c2580d29917811700d05541a505240c0c04c9100302940480c0074000c0714412400a10302100c1c410f400b902518543c0122500505410100301c3d00511540261790082103003444580140342a080c00029584111010f540c001000107501010941c046250018000c42c20820400080141e803000003494028242c644564840510640c4040402c0002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 720970809 1250 720969559 720969593
    0x120f0210150512070b0a08060a090605060d0f1d0106080105090f0d0e010507150b090a0c020307020d1b1d09010218040506040b130903200a02090a09080301091d16060507 74
    0x6c0c0c5802030241c0050a07400c00720780480c058400510005078810580c0114403d0724001440395040c448564101c0004082a58076091807a03150034890701017504e034812010910643d1000071441d24200b904090940e50068050807081c0c1c0161080720f0a00008109078400c80b0307180c900302c281c041800700100c3d032902801300007074070340d00e0340c10a44004600543e01101c503404003a1460704103507503019011011071381c14452000c0560070802108006252880785071a90ba445084400841c07040400d0009042c0381d1a0040d03420300c0f950006011102c0b00b840c244a61080b4850000c1d4540804070020b5400c3c8040c0354003040c00b603a01d81001c2083c03039903141c01100c00e80c0d0000d0301207820198a0003695000e07017440841074020038000321642952100b0041d4500c00c10f0440790003044910030310303402e11905510091800c0c070f0756581c031501580004e041d0f0300218001c003400319010401655004040032500c214038004000d503801500d80c440c26035841d00300d80c400c9481d141401c9032142c1d418200b400500c642c1001c0303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 720972059 1250 720970809 720970829
    0x15060b030a061d01051c03020a06020307080615040b04032012010b041415090726040c0801090b06190b04030506150a0b09040207080403120f021015051207 68
    0x200042208030307a1002c0c00700c0d0300380c03100081082c0e40c981601000c901d0070b004464008910710104840500e400c120884054031910440d5030105558803a44100e820569201d000104010b0912640d80f030300c4410982c1d0614000c614614081c170301240540d543c862031000900c550100c0307480c520000003440b241e00c4c580308060300c4190f902903650702141c001c228089280c0d21851420081300030407540512910701c0390398207521680030300028004000d005000241500d0401c070036200562400034450004171051a40390b400d80d8401d060616000c05030103030350f820480460380342c5155400400d00c031095498115800740c130318000310040324100c03002100180c2c000d00400d040000e400410082c000400340c0c803d200340030322001e043d1401001c1244040d2948076030540c50b01d0500a020b1145400c1d4000c04400344103000c09450565240c1c0e56101210300303090441e0100d400913000c04001c1d41c040c001c2c840c8034003c25108100c1d0051350744100c0540b0750680103007402044100e442200744076041180c0c102601407481 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 720973309 1250 720972059 720972061
    0xb0409080703090306050a021602060310030f0506010815040b07030c050c0706050c120c1b0f090a0b010f0e01090308222c070804240f0b0a050d020d15060b03 69
    0xc001d051400148001c440651134030f1b001401c820716502c240d4014841c1000d030000203e00d55020031029800140c00003101d00c81c4801d0000001d00c1c5030b954260700c01e01c600042e080540c907209043d4100100115109208041642000300180d01c16480552044032800d000500e961a5141200c10f4011141c08181910502a001c5001034021015010a0508d07204940c5030300510b01482c0d51900641404040550260004100540500100022049000e001544c1385854100014605d810980c5c1d03414041e6914860a201960300800c0c1b0520401eaa00f0a00d185000880000740400c02c18800030704102000704003864178000d11710910105542402403910800d8680314200f13412511200b4200316140e40780d00106202c5024500240b00708610343f100d201329513954503280070100b40e0a50290003040312020180a06405220390320107a4100b900000c2c1000610041c415880c1c000d0300000d00c950009580d05005903141008180031960208545a031041011601c2d8090040344d0004010000040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 720974559 1250 720973309 720973313
    0x307030603060b190e07030908070f03120e2d030705011425030e0c03060a0623060a14070b13020411131a0c0a110301110a120b04090807 60
    0x508030400781d90242d441040503940303800800c0008452800c115110300044142040084000c0c151142d20078280d09002c210404d8030b0755100441d42c002d410486c0d01700d000c0c0f03c12030103042d031003100c0c40e10b8424210400c00c4800016a00b06984110891141480c400036240113101003048044170740d43c9555503c1100e49034034803444c0060282c8800243c110724021079100084010000300c9812001200b203900700340400e00031900031409410716003000c02da0b5209075080c013080b94070100100b5200703051107280090060300340000315151052041000f000103110108010840d03031907404440b8102201c1c00c01d886104007140110406001748a00a442000180100603124440300910b01c60f09108613410051540845a4086140118404807c1458020005120b01a2480184e14000b0510303840302c1d05002150300c44600c2c00c0c4502c0d03000c40e048070030f20012180c0783c1001d00540281da0500154281041c0642c0801451555948104c2c04080e44684408000e915542e00011499400400c0142c0e41c40c030714 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 720975809 1250 720974559 720974561
    0xc0204020c0c0f150901030b150307081b0a05040509040606030c030506060301050c04380d0207020f0409120c1b0602030702120d0e1302040b040f0303080c030712020c01060b030703 79
    0x42c504501600c2c0c20400b90340c1c14507040800c0400403980c594100e0512405038011001010b03100016078011083c05a5100c10341070140265206c1c8900d580c0d1010340d40780000d407100e191003901c0e01012202030284013060341543c2110a6900b5544161000c14460340c407418858050401940050b0400c20070b01804010300130b01140c07862003000d09030300921003031b11103440390b402520079885081009440d9110200d040415122910380100419940c80c443c2c0c1d0030340388940c445a00130481c842c00c81c3c0d80000c011003142056030b044404100200d03002c1017011116200c0030390100400f81c2d19810071004900c1c100411004180e244803110250110802c010f40701c01c0c0203966a4444407050348128250600c0241507840054100040805035135203180e0dc90141c0140030400c4443c80c4580100b98080c4000301c1c00ca100c00700680010f24400d07105401c03442c07139802c001d0301500340580300c8000160b0400c00c001010303400507290701e0082e0700e52100582e554514080c1e540100610340000d03541c8003000007400700c0c0542c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 720977059 1250 720975809 720975823
    0x20c01060906150f09180b01140a03091b060504170f031602040513051216050d08010321020a11041b050405040b01110a02041812050a0806030109210c0204020c 70
    0x1a603102eaa402c03138428481a030782100a0704c140a0041c40810380640c0300500e603000418811410304110854050840fa103401c1d0342c000706c9400f000aa035550b650f1003845000007510068031000610501c40c2800d0560042c0741e449140144d2030b4048041240d841d4020081001040000702a000d80f92074448400c010000c1c1c072201c2505030310542c100b1022914202049407801480b682c860001c00100c40c58407000c04a6400410708000c0348104c424035035010403c107000d09210180c45554800ba60360443c41e01d12900094041c10790710304a0380120003a24507400090b101409508100810403010700304000802900300c8140c018400c010f60704c60159419003160140c02500c10494051001c1112000115090600c89640d00202d520410290006d42405c4c1d124604020740c1c2001d240314080e41c0e88071902d441d034101400400040303000540c0f401c40c07076100c90041e41011080f0028881d01810b40c0b6245000001d01c00d0040e084101340702c1015116028200c1040d04c5503003e80155290001101e0307060311520 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 720978309 1250 720977059 720977099
    0x503130f0e070512070311040810090302160806043e0f030c03030702040213052115010b0316030e0a03090801180f0803060102010b0d0b071701080a06020c01060906 72
    0xc1001d000c0342085000780d09aa040600110300300308580d440041c100c025199411890402d05820000800c0c3c0303d2050090160590220310041406111490000d182400102c80e0001940b5007038400c2c000d112012400d25005a0410320030707010500d00514144100c0c1c10804015a001503044d4400002140031000c16044401195450f28181c030b030b4000c0c1030319609401d085961640003007059600600d001d6018000040f40c0310022000c4e00d07140c6003c94070803449085403a21080c0e1035016507084080421442920108503504268194034289070240c980c000600004000e040d6800401c80c1d4501c40d921a07a13078a0131042c112040c0d60031904002d4107554050084511650038080740401020708400d843c0720080d03001c0000358034030095440d6050a40c1014210b01d04554a90a0800c02d03a40c600410700e900500035a800080703410f00c450301806d05031703a11540e500c2480e0b4010041003040808035120030541e400c00320150351040201c52090041c80e40d5000000c1c15450940b0114000049001214000e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 720979559 1250 720978309 720978329
    0x6020f12091617030a0818010c0909111303060203040f0c0f050108100602061f05090c09090717060409061d0a0c0f081e1e030c010b011e03090503130f 66
    0x1070b183c10700b034031521604108141007580308202182c0c01511071020558001c001c40b8900c0c8442d110450307200e003035424006080300003560440061000a0091103802350301c1c40b400c01c48a04d00f80407006960181c9483d4400034200d00d60100028050000048080c4025503214645081050301d45424200072101c5001d420700140d8004009400c030391181445005841d01c03078004207801e83d140c905445654a28021040059a14141c00249501e6101c501406400006a282c1d2942805800d2080c601c9000704cc0c18204000034200341284000d1100e00c0350005810784e0f02046486040c104100a021804d10240d810320300c0d560034000862003c03502d4130b0003600c1040d045046642e10030500302051906d010b001429040f440e2426200a882251310443c2903850302541d1101030007030703a00c5407000a1908103d989410018074030703111007030070720804124100034281002d05040c50644200030f20480e8558000b8141c2da0120768060010402c2610141c0181d90b502c000038588440842d540c10600f84901c2483d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 720980809 1250 720979559 720979603
    0x90b04051005060c100c020604030311120103020f031e03030609011512092a0e1e01090b0102030415030902010216030f030e0f041505150f0706020f1209 67
    0xa141901980e80562942a5420a0242000d04010407035100030380305074080c810080f00c07075106200390140c002c80c0800c50b00941490301d0309003000360507145031849001d44008104a0f80b04d080055224490640b5010385100c205009540082464050720811440c403080c3c074101103c060405c0040114820340c420345104450343d9031080764610b000b0211001d007011500b6607520581400c1a58070400000d80504d20703032940381040101200c404c40444050407501e010b15135082c000702e0381140c0c0c6250010711a45064240c0803108440b0f005d100c4040c0600c3c0c408a0315039110001ca0fa108105035009032203040b003154100150b0400286c001c0000510482c05402258074207104809403007002c2080700e8000d00d07220b0707803640c1554080f03458400d0344500b69406400c849036942d064840e4440e01d03000e0810510619111407c000811100380d460502c03042e030400007001000a100d40740002c0d240419840700000da141d64a84000d442d0500910300d260103c85c0c41c41041110f43c2da0b0000d2000d000401441489000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 720982059 1250 720980809 720980831
    0x1208071103010501050303070609030c06050118150821120f0103060b0a03030f1b08030a020d050a0509070501050a050d0228171f050315070f0203070b0109090213140109 74
    0xa0f01c500f403003499456041800740102203071098215070082c40c82490008481c203155500d03a030842e0b00a8000f0507258001da41c102c0314040447c031602060310300c400400380f41c182c644440b9541da81040c900300303202183d508242942c42d1a201c0241c0d81c0104101843e850f1780e142000d1032600b9a0404d204c00d441c01810500842800e0814800580517640c265561902a40a0300c105440b18510b44040c01400c14040d41030101240c642005140100010703000035039512203031050b9500b902c0c2c0103440e48004514040174450b900100243d81002c403030003800e11075162000084181c8844c0911078407034204600008980c10300315103500441007440780c03088020089140c4580201e80c40172600b656001c0510b000d50100e00c54008410380e491a00d105001501c13410f0b40c0325000700381052085060030180704081024405450340200381c88240d8400c17880218103082d403940714801c54100611a13000c42559514100c0250745500c060b080510400310340c10b12a0a2000e0b48459024800744a00c203040c500d0f1054141d0b03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 720983309 1250 720982059 720982061
    0x7120509031b0f0105030910092103110901080405031209031905072004020705010e010606080903120705090d0206070f050c0f0607060528050105010f03140708040804120807110301 79
    0x4400160102d4070f92401d0800544959201800d0542244510044440718200364001d08183c40e2141d69500c5004d150854200040ca034604040701c103246c00d0009000c0042160b00030348a000d41d0900e4110b1041d180c030f0408500b07501c00c0c0b00d9403540c119814003c001c002107000006118000c0102c403c0c0d001c0d01d424140440d82d0340034521000b40200c40c0440b074460690050302448903902c034010f00041c601720701e036076849003142c0c168403104616075103c03c02082003a4122514a60100561019510308500c0b450040e40e2650018440d0090110100300314080e5161409031100381d0ba4050102c9903100000d041021915a41c0442141c051140700902202420301c0138101d050040054035040c10a0743c1c0b0fa4900b805000000c20b85500d9102088580482a03206904800164080c01c4001081c0d41020001841b24810201040c1850b040c040080310100401c4950360f4864518074020300c10303464a01d8541078510a51344030006007030070031940c2c0c4281b024440080c41114411075010b0600440d0b0800d041c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 720984559 1250 720983309 720983353
    0x928060f080f1506130e0115020604030c0b041b0b0d0b030d0f08150436020616030e13020903071a03060d0c12030806041802090112080712050903 64
    0x307141c0b2805035003c18202c000340104042200401001e4604242c03d105c0300c2413244101e07a21031411040342400421107542d414107504003451092024100c00e01d805e46000c2c08100501030300414200c1c101c030004c0c040c0b00e40b50001a41075402601010104c41d038070004415150044004401e0240c585119052285400152801c90907550b44480365075401000c02611000802003403665200082d0070a444182d850b17104e0070a10384164000c40e4a0342402074902c220128244010800d000741c649902e001690762042620795454100085014005151a048403843c801940441c1c0000948440b0381c030489081e0040d04065200b5011100a581c2d655001c5035031030700d1465540c89038001000824928101010180780560088500000740b5580313190700c140c41c001d190740c20713000030b103451081c001503161034010b05403481d410280d881c500004a030000390b01542c041c401e05011800c1c00c01c4420800030100240c410036500084d00d101c0010703041740090840d500180c64103201c0c1c01290040700d449031440300c0301 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 720985809 1250 720984559 720984571
    0x71a0c0712170705130b0301120b01060906080f0603010b0301090506011703040308070809011404060c0303110c1f091406090705030a0b0703150e092116080928060f08 73
    0x91280c1e01e41000a4039558060b11140c640d85408005c04110183d03178200450017080b0b4500000c0d0288540d0030104034410301031700301e80701b00b14601000308521944800c0640c1c0000c3c1500440080e522000c00181c01071002980903501035013448130350410f0140100d6101e0403950030321201c0c2401402c40410380d48900c42c0b4080142008000d008100208166001500c0d60351018107103590301150405018155030400c1c1e21502c00200b1201441003050385c14020108000b0001c2546414601c030200351707940795421045152080503804c04c1029140e0084e4100c1286260006080b0000c40301c4003080b69200c41045131070b40e1302440740e21030010300b502b000288003c00642120080480307440d4000b04a0246c43c0c80040da26805c0d45880d40072a044014103000741c0984541c200401680d04c030b8031080c410b8007200d1054598054018000001001c1c60001c2d014001c0307500119040d6120303594000240d1072a0b900f0318000841122100c4451516207450350340b8195401522a0040c1c6280503000f15804402140d02c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 720987059 1250 720985809 720985847
    0x90d230c1002060f090c09010b03160e0105070210030f020c150f0601080a0e032703010b1f12020f03010f1a040f0501080405010e030315010909050105060906071a0c0712 74
    0x14409449404c0c04640019403481030b148100c41501c00901c03034110a811031104000300106010044580114604144039182003414202401c0c0c80041e03c14000c16002074010f200449101a40038071030b5002d9152400c1c1071004540b1612403104039640c52903040125000703075503d400031034031940c02e400c03555100320416504c4107126a10502404080e0010030f02100304c5102c02d00014000300140248600d14442104400041c01111400c04d8207444100f92494090208001c601a06c85150202c280c40c3c443c140c00c0c00b00c4442c1042c00010001d200700170006010623404000414156020007425007200d103902e0740001200360390040003009105070f109800301110001d20401c5954001c038a81644107010b000001540c4803100c60b51030855004484024201141d508c01c84c0607986c120003039a02502001e0010800381d81441c01290051240c11807007441a903000c149c5000308900d80c0080600500034149034082030405111100c1c0300d4100d13034011500c1c8101c8182401c1260b2083d100d002c945036840351 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 720988309 1250 720987059 720987061
    0xa0203210112120e10030c080f060312180a0603060305060109060803043b060a0b130b2203060204170a0b0106050a03022502030d02030c12090d230c100206 68
    0x1a43c0140b0034000c0c40480140039012410303103141da0369104504a80a2103880110324618840c2c002041214024504c11150700e01d0000e0000540b000240d003060b80b1445042e555542c1c0c040260858500d8012419650040f14440c01198155044d0414011070740304104941669803141455010f80e41c0314096100107034414002009101303020b40480020311000c0c1d0b982200200e5400104055400005002a1441e200e0062080e5070606800c884024103080c0211814181040402e1001810b070740b00e030034640f810225034481039039907000c1d480700315240c14070003108041d9491800b4400f940041c80740406e00a6940700d60030f405140810342c0e040482e80304441108981c204402507450350030510f05c0904040d401d20905a07150012141c03980d401030b8441e8100c0b80b0025901c1014a403c00520055045400c01e02503810380000002e118146c84c100710580c0d036141d56214004c20301103010001e01130240b0000000c450441918040071002c0014a4415034005000c01014410242c0f4070600e5100160700c060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 720989559 1250 720988309 720988313
    0x37090f03110f040f050f01050f010302090f09180717060a0605010f08180a0503120c0a0207060c03050d05010605032a0d05100806071106010e010b0409150801020a0203210112 76
    0x1203162001400601c001031000c0e00501c91300c2240d008880499034003800600501c81460407003c940281c0c1c0c0d0900c2c0c150710303208440c0e02066045003400c107070034001c519040110f01c030880c004401800110f0608125080199140312045110320300403286c6206024801c042440403425001c0c40c0159001030b10f400745402d240004c00c486d41c0070002c083d1900c9401c101904c00c86d8440600000022902030401503454145c0c1005281000c07c01420910550004002801a89030045240760860f01e4908240d03d4600d19810305407040d100d258010842c240c90100082115a0480e000d14060032214021800c0c3c1181a04128007c807009451001202414001200c400845411055000804540d5200c0d481da07690540c92030490280d0b00b90022131740c21030305290201d10800280c0c0c0107001c811a400d00a5241c1024400103118500034002d9071610741107619001c0c6024881c9600910161008542d03400e08000000e48a40207030520482909400d004c2981e007101c003080c021b041e22110a100305a0808603 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 720990809 1250 720989559 720989569
    0x20301240617070e03210702031005060f06030a090f03030e0c0a06020c040b0d080a020d1d010804120c02030d0e28090c0903050d0e18160537090f0311 66
    0x30b8021130794540319002030803515091218810008007a130b142a00c1d2a40502c0c030416081402100c840e03a209898a000c010a540e80c1300030102c0d01d002e098625581e60f4441624080c00b03421103a01c0030b0410f041101c00e403420036034180d000b042070103040d00076550820004000c1104244084c032503000140d00620160f6224942548944010380c4005c1400c0c4955000359903007600c58000500c1c520158000d0904418056000740c1c02140803100c280b0011484905100083d140c000f0291001d05003848000e21180c90600411100b8103040d0010101d90005046683c004e000a02d0158564040c0428110002c0c000c030a41076050107041c00d0a01030309101d810400500c00406402c2c41c10000c0100e0140000b012a200f84600400c540c020f583d0440b070050040c090241064490040018000303e2004100c2820305092090b00b8021082c42c0c059907850008000c0ca01d480c01009c42545d000c00720b14951b40c840300b144c41d500311100da0315403600e4495554030b0100c0031907000d9500c0003521044040c0e100800500d42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 720992059 1250 720990809 720990827
    0x70e10080c04080106140306090706020304441c020703020f031c0801091b0203070f0c081207020306070c120c080d02040314100606090e1302030124061707 68
    0x8540c0031420950b507040d83e0380c25078007a80d00c640c0c40014100a000c486060a10070036500116400061070810300e002c00c0299680710301d11130564140c10721118458050300c11031844a058480d031601914880040070083d1074000405040714061203280c480c60068180c90104041c00855034024042a518540030b00c20100403c05003e0360500070311000c1240c00418981c25800d00750343d542c03036100542c1021000d40495132154802414031a20002641c001030380002202c4500d5804410a200d03182a8500a500202b40341c0ac072a103207006520680000b26418405803607494005c0b0203c59050b01c822609846600b841d403030103030652240740030b00c2020a0145045400103445407000501d4043e001100c20200c2e04582c000715038404010315680c00124040103100d82001c00c0c61410000701c5d141010140c00d05480e442081c1c0d110050704d00040c10f0030010501000c1c4950054001d02400085880d9032a5840325030b2107602c4151000c0801241a5100b506885501c5000085000c4e054440306800c1d01c8a41d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 720993309 1250 720992059 720992071
    0xb030a150b04020328052514040803070309141005070804051801090e0f0c130603060f200a020c0f1f050406020c010203030408122e0e070e1008 63
    0x611000c01c030145444902c011441917451109010a5031800700411a0000c0b426118201803414803085c8005524100b000521103035200c80100c403840c035103030000e65100034121075030460b8502c0818006000c2c680800140242403007a0344038504503407140e017a88005c0c9000214660010301d06200e484581c1c2c0908002c1c070b00140031f40380c03031801c141d940d00005d55000c00300100024a00d00c46c1d0300400c480352240c080d00f118980e1007030191200c41d6400600c2a074507816082107910071100e41c1301080300660f00e07910410280d600840d050120072140e0308944080c020100b00c5900e60100a03a4001a075141c0340c1c00d44091102c581c0c0a40050741c3e002c420800b078500d02d0007000d603010325119103a00270b41e00c0103036862420003810303142c19403903074608180642000c1481070a02e0554008000700000948690b0440c0c45c00e0b502c82c00c8405540c0c030307640c4001c54411441d4010500c6900800c9080c400114101c605504460840303242554036585c2c001c04942854850840d03640150240d011782640e076000e0a4a90350040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 720994559 1250 720993309 720993311
    0x308030c0f0f09040f18240f0203041a07090504021e0309010b090601030b0303030115030e0708070e01050a0e040b0c0f0d020c060601050f030705090418030302090a06030b030a15 78
    0x820710a516081d58080410b030300d042d01c40060f0081c1c01c2e0a09009440561002d038004010351606044d07074900d2101c1c0c1c100000c0946490b9500300103c0011030b61996134881991703200304020303524002d100d0000c0d841620280e070140100401c04915849050342c1c241300310350070fa503881c1c5500d00d04028080a500213981c20484003140d96290403220304003030090740c81620740e02d0000c941002c07244140440150041e1a942c1014100100045aa140041221f04444a60307003424101e054242d42280100303480070144000d4000c456000614010000e01a42502c00781d4441141c0799a890081000d00f10b110720644241000c4940014003103842001c0b0642e200750200f0b081c0d841c02000e14404030503540728880244801d0703400f0810105e4101e04000465201070203082161030034960441000103400700901ca1030400000040c04600c13030b169038100000c40c0c0750040018034107038000d1401401940000700c00c00d0140346801c8000a2580c0301c2e003c1c03d150b110b0080c001e05050929520f5000490000219410100d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 720995809 1250 720994559 720994567
    0x60c05070506120a2a0e0f040c1205090c0904060218130e07080c1c0501060308211003081602190311010809060f01062d0f0212130308030c 61
    0x198440c04003e0400c095002400c00161030240b0400044032920802c011040001340307401444d04240c0070100ca94600700d41020394003031504000050754a6421080e542d006801c00c0b0700014003980015105e000306502d00000d01c02c1303035580409a42d480050b1b4411a51003000c420110303011071120fa001b481961750303142d5407000d800c41b0741010174100c60380c1d00c42d800d800554030700d8200c3d02d0942c284404e002034009440580b0301c0d80480c100092a03244800d40c03460101051104c0031042190940c01803004690200480761106030440380c802c10404010002828045c0b40d80004140c1d04203403582101f526030089040381070442c00740c2c4040c19850400710890300f015205450000d03d2000017954001548a08044000c6a074903c000505a000c05401841c0b1680001c043c040c2c2d07a034444c0c146505585052070141884c1c03422000f1300303800606904003841c1752502d03d400203040b1603000341400d605050b82c1c0c00b00c80249003000498010b900c28041c9204510504181c1400001c000e1030003150032044006909044c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 720997059 1250 720995809 720995819
    0x7020601060c21082a2b050a091118270613020a050a1a070f06140a200304120e03150610090e06040b03011e06140a03050304060c0507 59
    0xc001d034464510004208820200070b03c1034010f0005241d01c1c0c03110940c0e03140c5d4240b071501c099024001d99a41081d00c1802d0343c00c1d601c001620300070000860f9003a9030184600d0415040b40b2004060440d02a42e1220315000241803d0070501111402101c0035400b00c071280d41d406c0e115803840c94101c0a000000c0c01c003240c0c084480c043c1008240e01502450101c00078180041c410000650003a9100501901020170100700050640c010420459440b5049640e5019030b8600100a00c0305204000d00151038017100130403908a50a85501c01d0000310010000c404400746034600c2e14182400481000c0003c10000b000a00d80742d017001b00b03503c050300340b58441c400ca04000034245801d041d450194242042c08000b5585821450b66401203a2070a0040c8814101a1040e0951900030400741c002d41d1513500e40e20075910b095028a00ca4100319400001c142040f00044002d40741d02e2190103560051400410518070305031820400300c0754070000852500382391450640d100841d146017a50140611600056 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 720998309 1250 720997059 720997103
    0xb0115021519111b06010e0a090606030c14090108120a050c0c1507030f0c080f220f03020a05030f0705120a06050a02041e03050d050d0605060c061e07020601060c 71
    0x203c03100200b000140c0790900c0c5813220380e44809140503054158400001000050040d80504e0380000c400310340030608202508200000e8050350b48010501c00c12a000094061003079044500b881d10210f80d150703011b0340d030f80b0f180d10f644003454003001400201c02c02c00c07044500d001d6030040c40c034107103003806645240c0030703c1e000244e94000049540c0d040d1480005c1394400c25a1105640901004500b0207a074000340c80d0300c40040300e0140c1a89201d2490b0001031003003070b08a46114201204014044d01030410341c81d07000c1600039168610080f07004040100317001c41c05150208003600c2c0405160000c024036850001007203142c03001102c0d0000e0301d011703581d1500b0108040d4014544070b0301c0b07103000c0580e6079480d21414850252440602140000c0450301c01d00c000b420200e90b40c10300c095035160039610380201142e000001c00c40d42c0d0055610036170000c4e0011001c0300115104c0c0c450000c6000748500c2a05450706202c00400481e108001030b000000144a218041c04404040900035251a181d1041c40781000b4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 720999559 1250 720998309 720998321
    0x301090e0c060309030309061e07031d0d02010608160302130c17102301140310051807020c0607080403030302030705090618030616021504020301020c06010b070b0115021519 76
    0x1545e0000810480203030300800445822100010484440c401c40445410407000d02401c003404042d150040054543c2c1d00820030070041c0c504a00b03a40b0a0345101601074001d02e0248201c8200c2c0c00f4280419402890340c02414003125000b600c07032504c0e981c805c01e1200042c100f8282e00024098025070803c6440e04408045104038428094400d5240c00c0c200c7c00403071282540040c00030303142416100c1480d44d034030100710004164400700b25610303030302d0340a221022540e06420440d0030050a50812140704042c0d4412401803405409a8594107000003d01c00381d4800c0c0c2c4009020000b081000304000b078801c1d4011548240c0030710305182408034101c00540300d984840c214120316881170b96018030368541406a00e4102003602441d92510040e45000f03904d400c1c00c00b603100c0c3c02117000000a010f545080d0110f40c0304400742c5042e10950360711110804019080300300c0c1590b004580d10008030320010144001c006658141d0010016100b40d00b86101a0102c0100200e04812000992015207400d5000f1b40f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 721000809 1250 720999559 720999571
    0x60103060b030a1e0203070905011809030311070804091506051b01090b04110f1e041d030c0d031518051506040605280f080915010e04060e0a0201050301090e0c0603 72
    0x100c90501c04c80c0105803910415030000e0480c6451b100040059815015010a420400040108141c0101d003029001442e00da600c0b52005000020340074100b008400017001555030b2880c0400c943c81d10b020026022410340d0007041e0100310108803451016003c200c0078110b64983c00c00114080031290748050f20884103a60855100c00511401d107510f2900c3c0c5c3c0700007082c40050310403905107000b80050b008a03550b01c0403e0760040da51800761442075601c0704400602c3e14142c40c200e039560030329203c1d15680c0300304441291000078540400440344060038080f0100302c48039200130080c900d5808100720010300c006000030000900c054a52220f580701d2501910060502381ca44036184c0703006111241c120100c500311541404c02d40d101e001c03c40c0d50800c0408042c2c1115180c0a0049e81e980d4909501e01001c0c0e1101c200490001f000009a0540c44101e481c40303288213003400e00502009e5801c0360b6485034100c0f0b000380480d805100601402d1320716800180207101c01c01c1110880c0c99000080342ea42c1e1303c15108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 721002059 1250 721000809 721000853
    0x20a080c0106051e0f1816020a02060a0207060215010302010c110d150b031203010b032206060e01050f060a171b03010e070e030708120f19020f1e060103060b030a 71
    0x82840c602051740404403002520301802d00d02c2500c05403550720100604000140744075983d0000d103980b0810080c8c3c6050b502402c0c003540d030801c4880203590b89072a441076500600c20400d104d4030481c020320013281242e038180c440040840840d594248603a10f421000c68105460050359408a0958488050014089003001a4000e5843c0a00d418800c87c1000004505001c2004202e030040c1e0100b02c070384c40201064122035405010848501c0b1172031110015211034141400411840f244002d000c1c100c0d40e04644c11420044080300384003140c02603072300c034002261020700e00e40c40060040b4a00d9501851655680108040b0700921020a030001e070010307011b10340325a042000041c1c0040100e414524124001c10b0800d1405500c0790303a83c006c10010341c04888021440141301688007050711800b102280032110a03c2d501c0710001c0d628000c68460846500c10200c4800281000c41c4d0780300c0e2100180c502401e0160b09640350000030303004500d074a64241c864162200046000061070380030755205901 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 721003309 1250 721002059 721002109
    0x12030a05070309082101090e030702040f0605120d09091e1a0d080d0c03021201090f0b040501030503340b0408251a0c0304031d04020a0f030e010903020a080c010605 72
    0x40c611703000380141c01c0540b9484c50200800b40c40c00000058600c5943c0c1142d021610040c60103103000900b00341d80c0f00381d40184a01154a110820124101341a01403565440042c1640c07102c400c010b6074480602d050000c6a041c54441c0005041d4121468841d5520100c075012040c0390007042d010901003c0130785020351301044c0c60258003c42d000701c1c5901d071038501e07003581484400d40c8010110a818800e9411140c0d50b40752040340c13914250090b5280c840010010070042d0395038200076807607a22641043e240c0d134220031580708c1c5400c0c400f100e400407070f032880138200219600c1ea03a03680c181600140080e81e00c800c0c01c0c01282141106811144008204211040b510943c17500e0504100c6c1c541c107014664603a42203003007004c0d00c442c4005a99201c0e0f01440c00020044840f4034012980810b0512680c10a0000445018031500100c0c040410491503030100070007120000d0700c07800c1b9102010003e00582003118280013280c2d8080182003810866800000c0541d41d440010f034488403603540502e2aa96000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 721004559 1250 721003309 721003357
    0x140d14191e270509011512021809060139050f010e0706020a03021207140a110f0a030b0c030c0c01151a0a0e060a03060b0f0903060912030a0507030908 66
    0x8609412515042d02c00100218104000202c1c00e05050090803121103081c3c2002c00c2e0381d031003461004d1007030207410411582d50b500e844619850845e4619800d00590148000c0348065104071025246400e10000e400c0c3c018001f0141c4903000c880c03400c03d51190349881d9070840042802441215072504d0048000690882508122411725030140d01410564001000c6603010a1f004203817018a00228002070b6038651061818650340d01c180b003c88a85841900340c8031003000070b40c40380c0801e810300403aa40c0c07244040070810414049814040148440c0e0321101103060042d0074000365030007004c07440045041c08404d406a50841f07070180190f420301c1e4901501008040071480d11074124160344000c0034a0101154405060725080c501c04a01940c40020411035492103a4000009401c005405a96a0006103541c0200707400001c480c8e03100c1d000b040003180e01c0c1c0b500012020009a0380c489000d00710340d145120000208030003020413040c1034482e000d03400042c049030300504c0101e955500081180d0542 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 721005809 1250 721004559 721004597
    0xf03100f02070c1505090d15020307030f0b03160b18030a030207030b10050f1519081609030308010e190501150e0a06170a110304140d14191e 62
    0xe9132050301203031040c112004045500a00b29002c00ea0292108817500341a031130840f0035000804582d52550340301005211403980d060708030480030161014240107010a01042640722103420386120084500b410382000802d55803005000040f40c280410388080300350001007820500120f80440040e0070140040c002c0000e44040280c0090729802c0c42c400c0c450518000c81c03405951156660310848030100c8005420510000f1540c8121040c1078a40380c207100110050424601582c200d0280e81d0000081541b15100300111401c60740c0550f120340090f4a005a401d80240029151500140141c024100327241d00f14011103000388442058000c9851044030300a0044059010700c500c1741c10621000c000303003940150419095921000848015181c540c40e400051525012742040b100d8007004100c2401881cac034210040707030383c7d100540c0c5410121000c103d40600420200d0403000400303200030000401503002034010814141841d40703103ca860440c0000c200ca001c00540300081c2c1095082007a2030304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 721007059 1250 721005809 721005833
    0x5131e050303160312020909070318051915090c051c06060b031e09071403030d050403090515040503032505060c042c04080a0215040c0608090316020f03100f0207 71
    0x4805c00842c2000300c050000742d50500c001c0d20810401d6264980c440700510603501e01d4181a83c0306003261101d6488144110041030020320689902000740f03002641501540a98070545a0090031502c0e01400c117410803180e00c0300f5602c0c8415003807061402200044113842114050900400400d440303181941c404929410f0368011b400d20300e072580003405002130000a0352002e860381a2601d61440e103400b00800c0c51409480318800d0140d00f04001e00c0245074000707000c20300f924019a84070b88950688940b0710a00d218510440f50160320030854142144100841103110041c0034107010340110007502e0310740c0741c0b01d030075100300200544c000f80800940003a110039001c4007025040e04140a4020b40009881e8200140050103a03400041c02d036081a20900c4a42070790180b803050003105040604003500840c4aa01504001c210b0326008290a8800002952845d4a000d4400040450141d090094800c00e004595802d8400e00a58030448002c038054000f0000841300c00503111015810300343d0744031030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 721008309 1250 721007059 721007087
    0x6150914010e1608060f040906090819080915040822050301061508151504030503090307090b061605120c0a060515131112090f070605131e0503031603 66
    0x51545250f8800b0f90402c1d0900e50026003160450301c88200c41c4c0216015140c0883c00910b8140340140e4041000180b101611aa05090199040101040500361104213064a46100c140d000b81d42024414002c01821a8014401e100450800892400030400660203c05400c020001b0020a00050500744a420000e02c0c035162500215005c482c0050603800c0702400c40e110894603c0515031040c2c55205400d0400c840c01ca20180d900c5982b070801585a40100040380d1180c0613020b4000380e0b03d81d0f58000c020461a000b01503914000005440c03038940f0510a03400c03030701030003850540313107200c40814060328003110300501602a0b03072034614105084031801031002190010310b01580c0d00071b481e030060030b201e5144420400a1080104254000c0a0003040d5540440c04024010001e040d800410148001c050301d00c1290215500d400003601c050141c0d0340c540c80c0001a100d4200407101c0c950390a030342881e0011081482c2c1c0c0d6142c0003c41e003140c0c80300c4411081b03030100410134010154040d480c245521 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 721009559 1250 721008309 721008331
    0x904120219060914060714091c0b1e0c1801030608010e0f010e0d0801030312020c01050a0204030615030b060607020f0d03050712090b0702060a0e04050901060603140c0706150914010e 80
    0x706c0c0c012000380074220114003a41a0f41004100100e054072402c03542d020f00c245e850300e40c003140c03595403400740c3c1c40c60000c44490710301d841b000c024039200300c031241c8980340140e0280340c2281c14131841c080d80c0c1401440039000070b4101034642c0400100701c103003031091344800144030000d44242c106001d2420300355460a2421211944940c4034a080d8981c8450840d054980c58a000304418541140882c0a07001c1c1e4104820654606424404500d003168000c0046900c03d00040c07040341c5402048030042d901503c00540300c6106a000510ba9203405d50050540701d200901510310b00d9080700c0483d41903c0409400c4000c220000744120520035116110411031007203281c00c010090500485590318058060000d00401d00403540c011014041c1c1202211000090010041442c1c0155a00c1c00b07003200344241c0b40800e141600c0442c50942040710f0718850303c40c41001c145803075038580c1e55030000d002800c038001d9034243e0104081500d440a01a030301100f20b590300480b443e541041c500c03140e0f0038400382c003911444c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 721010809 1250 721009559 721009561
    0x7021603021c0507030b07050403032a03080a060b07120908060c07062003090a031107060503040b07090b030c25050607080702070f0b040311040506090412021906091406 74
    0x1661002500c68490740b80000060034030210340382c031920300206030300b008200f28601e1041200301507109001e070084038060303070321039001a48560b03103040711781115030070448110284401840428007501c1e80e150021240280050019611034181400750420023040300e46080c5074540f0407190364000491005401800d01902d10f501b0121100c032801d200c0c43c0001816580c456105280c00d030714661990f000c5240d41e0052594901c0e04d02e98540d00c9400024044011030f03401c0e0860800c810000074000c0580b0a1a103400f0f1640d111a11103510401004015208020200e50701158400c2020007031405106070380e55051311850300079141c1030608082c0500690340706000603030f403000c82d100060b4a038201c44d043c20043e2041e03c440038201c3c10324015400074030001e060050000b030f4059215000704200d13802a10014600100681004103480054803280e522040030004180411814120496030550600455001c030580340801c070b900e000c90180c192051a0340300c0780407042c0840c042030b064040851201600d81 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 721012059 1250 721010809 721010813
    0xf09061a090a1a040306140f0903040807171c2a02010c030c0c080601170c190312170c0a02060a0e2a06030c0309121c0f0f1407021603 59
    0x44610038402d5541d000c040215079240701000f042203030301558000c501806030103e01c10f04006544020b0f21540e807030114440000b4410a0080300b940d007a0b03200f55014001030740c0340c95000581d8001e044080340181c020f00700900e0f031107042c10308402050a02c41d01e402a50085500123503908103d50403050510008034030f04200140e9219013072072040707a85420f1015030603405040c0b6402c07104103a085450305116220020a000003905180c15040300074000f01c8a84601140500454000c1c0728220044c0f41505001440010804407d000744400d540c50101c880e5401d0b10160f64109005490805aa5000040d1040032581c140710459101c01d20703000030300051460004850380c2d8600361103c900700c00d404c1c00100400305002e841040d050003008040b01e440c2d0500f400b1900181d801510114068410340f12340340b01405511080c1d505c035140000b4010306008139030508102426102c0041a8055501d4030300c00c4d40080c40b80f041c0200a140d02080c0140c9240002c00170b0710b0604118018100c81c000c503102080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 721013309 1250 721012059 721012069
    0x8041809050d140d1d1b030c1c2a090231090c1b0b164b0c030315050a150c0f050a020a090c270f09061a09 47
    0x149060200d0800204210800e01291740340380c4400c82031455014030010143c0b00c0c982e104000f1044d1030118203950b01d5003420010030901355014080c4502011806810501140d245c0c0103600141410840f1400f40c006c0070819a0040002074010740000307a8003107418080d480480b00c44075001d2480c2d0400d08040c07401c450810401079411700c2042040350311080d0011000d4403900d00d20956058100d00842c0798001031401951801c03048405103140354980201da01c4903441071526050403411504a454010b540c04c0c2c406064225601c1b42d03000c0c07042214000d16428004298260741e1b0412903442856204040c40c00401342d03849036070740c030010642c402010f01181e6070781e000b84000c4801d03005600300d00d40c0d2102000e03110880459806011a0301c958041d00603c0b602041e80356150b8070844100c20b0325030b142c2503043c0071154036400c01000101021503a980c05203050080005203d20020b2201001c1d6440b108419450059004191500d03210300701001804101d5101c02c50328001c00c001d2500740850540410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 721014559 1250 721013309 721013317
    0x40f0c0e061e060405061c0c0c02090a0509010914161502030a05030a14010e0a2403110f100203040e0a11090d0c1206020a0806011d060708041809050d14 67
    0x10542c0c0e401e0000b480305581d940d0080703030024680a01043d0b1280c2c40c0c0700400142030b9940d2882140d550420300c00b41c1d040b41c4a0880160720b40d0340185440700e16200c80e40e148009040041450f400ca641c2c980698020074482c4000440e040c801c03200810148001d01030b05030040151364840e040341d040140103000400d4000c070641d550a0003615200d82c581e620b0001c11009840640021103000d0400c00010500710f4400503814420000780f80c0901c500341203106941850f200c074121750030511030780d09010f000085a0000c5000300400050400e41d4a01802000a10100c880002800940d00000e41040807621075003000d0b51045444104100018001c180300da050300c0b614001c0c41c0315040c0390859401b0850070080c444042c010380c00400072940d0b820301d00940250701c80304203080401c0d02c0c01c000400035845080b091207040704111540c0c3e9442100701c144882c54200311801c0b501a0310602010420740544400b10b11000c4604001050096070750a16609101000e480742c02003000034903100000090042c122 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 721015809 1250 721014559 721014589
    0xa200301090228050c150103030804151d010e010c14041401120c080f180d05030a0207080d140705180d02010903050607030c030f1503020d030314040f0c0e06 69
    0x15a6071145500e045160103142e030b03206143c040300c45110180c8250320038003804080581c1c01c00c48440e5084900b580031009000d10008000076035540005000a04c034905106045c4103c0c200402c665058103040c100c401258020702d48943e56a01c01007a10101c240a419800c141604140d14211052031468280c1d2045001c1e031002d0031100143e0301a96480f8100244401c1c0381000104102c4840c44801004d50302c05464100d00c88155401081c1003180da081071400700410700c0018010812090f600380e0340e030b820051400305429800d00401e808a00c002c8000d00304180e056100051160300f0720032034038401c0e03000740049082000034403400d010240b141d14900c103e0b00d070850b00c0c40084d6a083c401260f440501d0740000309103001e4075040c4804c690300340e040410b401c40c3d241c505200340d88a5180c1c0400315200003d08000003200b0344000c00c054200206103c548501074640400c032001c458088403206c81c0c1c02e560442d80004000404824000380c1c40016002d01240c40e00d0030a54100a00005c080c10301d40000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 721017059 1250 721015809 721015811
    0x61e0603060a0302060307050d11030712050403031d07051206062803060212072703020f060d050124051201030206031f0b040f050306010509071809090b0a20030109 72
    0x410010303602c07014410002e560080641d6074a20b4100740040c25078000a03c500030032810040d076504820386074420f1304e205004660340c080103020f0018018000c0c0501400a03824140e4403a42e0045802a02c04036102c00030300540202000340c43d14040c84100503800e4100c1d00b090300180c0c20722407039030341e0b140c90780d08924a400d00d01240003400d4084c0203641c024941c00100080d1000030300e40c1c4400c0c0c0321003080b0b220b0641c82d21a04141c0204440e0a28020143c0c184121080f9003070070240300501e0b021041e00c1c1c0713006000c2c1000d818440c640705490704694080e0402c00326030107090464254a00b0216070400b4108551030302c1c03811f103072610b100303910800810700000b031003005d02200140320720301c0d007951a1680f801d001d00c610406641e01c03030300d60f5110b90090050249001050101192034240064228121107028140c084141d849200844103035854400d00b41d03492890510005400342c41d40981082c050180e80c5075246030402e003404000712982d0801c920341e01d2051810300642c1440c00410b0301c1c110350f170365a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 721018309 1250 721017059 721017061
    0x501050d02090919060b0f01020a0b191b020102191e1d18070e12030f0705070b0d0b1c0321090c170111030c0901032a080f061e0603 58
    0x4100c03810301024070242100344c80c001070308209000c95030b04100d400100581d1020045098000120388580c0f00e1003018080451080220302030316915240441d0700e0100410008602d40d4005401150b001841030600c01030390042809503a100b103583d01d000f5120700358280381a00380c403e1074200c40345c8a0030701001018010107d8281c8400e0000c1342e811619803000910b000d8070141000701034803600505540307041c001400a900d88000c4d0030044000a20043c07144000c1d800c181c1000c0ca010a980c0c0003020403074483c040c030040010040c494034041d200001d410f16002ca5000900e0040c03090481038a400789103140c2034004c0721130129030401c148965080081c815004051512080c040262849400050441c0c41c20341c000114604140c0700d5014106554001340001c1201440200f03a5000c25546010034140c10401200e0560081d8803102c2560365030304214140c00c2d2400d0401442c200d11817042c4003c5900300c002c01034100715141d140c07644444106d8942201e00c1c11504042d1400194000450140308000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 721019559 1250 721018309 721018321
    0x6050a03020d1b09050102030a1704080c060103050102031603060509040314090618090702012901020703120201150503070f0b130b04170c0a03110108100506041d09010501050d0209 79
    0x80c044512070b052420040c4801c0581c860074014107680d0328544800203e141070041410361000c4226103c400a17907441104d064010a00d5240e8100b000e4411940c2d000100180789111405004241c000c50140000503224500800c201125065109a100030585021420b205540c2d03844000360f0840d80514050b05803c414840981e8144100ca6000b0f9001c01e021900711207408440d40c82c000d15290a80721064036480380e1b00103a003603d403076107003c244034148031004002c002074145806080400520440300100e03a20f4942042d803d6103403c03500b0040c0d4560360300306503018840038510004c0c48141c00401b4440d142800c0c80d04c3c1661713140112500c910002624031090254054108040c20400d9442030b0f96965580b84250407202c06030400e05c090089a003148803d10706840f80c8001c80f41c112007083c00d1110000011101800b004100c01a040500c240c08501921380001420103070003180540412107914018904446e0401425125980e05240041c803040e1210b401c0d01e80800c0d810f550204980d00c8070307 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 721020809 1250 721019559 721019561
    0x1030603060f09051e0a0f0302010b1306290a0e151914120402130e1c03150f12020a0b07031d300a0804090501090b030303040c06050a03 60
    0x56001500d42810280c0e2003022010030343c01040920b10610031200601400c4090184038031181403400641e0b000743c590000410581240803034040e00c00e00c00061440002000151620700d210b035180d4541e83c0e070380e605001e055240300f44032001d01842c05c803c10680640b403107585000d11801d82c510f810031544100c81d49041d101c0ca5401e181254180c09074540380c06001d00261406000d503461080001c04604003400f42c034400c4811501140036004407007240c0d6481e17800784401d101c03500103011082551001031494000d000d004400310103c1240642d442440506402010740b82c01e0851056007403586030b8104100508003502d4021100d4a40d450715202e101400014013520403030707112a0700d9910009160741090b6120a82141400c3d0006005446070744110500168007094855240380150840b80050b20b003002d01c0312040421220011603068900c86d030b54030000303500b01d0b61007000000d40b15401800741c807905001c0c0001101040d0700550861400d5200da0050f10742520488052220005103003a4061003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 721022059 1250 721020809 721020821
    0x10801050f0109052a04031a0a0c050705121e0a0e0405070906170402010c121110090302031b010f021605010c020f030d1e05012c33030f0708070e04200103 68
    0x107c401800f20307406001851054409c4a01e030010528101800c80158000c105540703407590050000c00080e00300300384076404e60b4411754000d500319420390440c41080b040e030380040038900c00076501c0116080000d010f0000f41d5034040c149209008004805005069121100320003400c1c012248442c142c499000681e144148842c024103803516840034a40441c0c0c1102c2c1601c0e08031101d008455401c1800040003003103594040d0010010781040141e43c9078110410302894060304a10000a01d080004040e20100e91090682144582a001d54141484403c1c49900c086d800140041c094440c51203a1441d01c0384038180084088550714441051210070346800460b0280c1d44080030411540c40740c42c030012068070140750400c0d968190000402100440c0d11140c002c02282c48044182c03940f04d2511030144040b000030200b200d14080c0608410f9404114840c001007070880074042081c2448441410184c09400400058091006000c0003171440c0c05e0b6402c2690000d00c1444036558003400413405009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 721023309 1250 721022059 721022063
    0x3080a0e012c01050c0a0f02010f0f060501110f030a0c0f0609080c160501120b0d0b010b03010e09010b010c080c460203100b0612010801050f0109052a0403 68
    0x1c038140d8582d541000c440700714240c004070b5507101a100c0782e000c0341d0b0070300781c80f4211020b010001091002d122130501401a22030b440a01d80004a04071220204150403904510142281d40ba1502420005560441121a05440040003910041d003800307040c1e035034038454421444d003003061200c40803040c44440d00e01c1c50b032055070120092005040c0c50030103200d60b800a0648810902480241c03119105c00320700034200302d40040c0c503889041c0d070703541072400000c088805203107411000c00302c141700001c0c0040108034041c0c10401e44d82da450b941404289046501c0007048406240c0c03621004e08440d0707810540d400901c5a02001080c1d071071001d2020641890410700310216000a2881c0345900c02019016406c0c46040030040e9580504481c00d1861444030382100c00b030740540011003065446035460b0041801114064455450007581003200000494242c0c00303005107035500c034140681c8048441c4028010700e1180707028069414080321140695400000c0002500462008140444841026200199 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 721024559 1250 721023309 721023311
    0x714040f05061b0f030a08070c0f020f0a031707030f0216030807080922050703060e0a0e0c060409270b1602120a0c020405010f24020705060408030c010b011b03080a0e01 74
    0x380400149645d80e0803402e10800417a406a0008400f2441080400c02c065000b01c03210a8441d6140c0030321403445050b24500d0303049040c005011011480c10360100b404030307a5051540d5500d007460309004244411048031001190050500002000e819000503400d0fa90020251940d81c809440c103400c1d144122340c0c009800850105010761040c2811544403c0022150010300c50b9943d900f00440444402e80504c080c2408290046840f00322203a1180200510480482c1c090842c0180011a1600b107540554040354030761501c2080004180c0ca80c807690813800405080070030380b07941c8103a9884001480c8020f01d0300b01c007034015100e81c4200207004441100c28526a41d0b000c61400083c980c8140041c10390082c0c3c10400005440e880c08520282180c00d06d000301580d41c10042401d45c01078041e00844802c41c4914000421035030340e00c200500042c01010011603445105c1c2a1542c2540c4290710700d036041c0b00d504c3ea081c010000c4580da4500c207181d45403070001220754411020700c0061000d4924100e0075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 721025809 1250 721024559 721024573
    0x8040b0f0726060a0504110a120b0904051f1418100f0b0405160c020910030203071503150803041e0b03090a03021203190e0a0b040b0714040f05061b 65
    0x2900ca0240b10718065081542c82c81202500c440c01e100c15103002e4004240d10603004c02260031864410a00c400b200c40d24094003150340c821540000d80f002606075005d65030381d04001e0002041c144a14078615060341181800d001d90041d07901d00c01100c92005140504040f0805510001030300d003481602c8007210807841c1080500b0076104440c004003246892070340500d01d0700d800300e52880755240c25984500710540d50102070500982c2403241c2b5600280607080003401d242c1020006076000d10298000d080c1300d0725000c0c40e2002c1c91400900303a8910300c140d0340103072000c81030a102503c00882210262000b803090030610260401000c1b040c640543d110390404680881440002100480e0180c980b60080e400c64090f40c1d041240181644400c0d1011503e1044411043c0c0a00d580c43c1c00c20b01c07c541d00241070740d00c03134030584d154101e0b8203208690481c2e0112a160411031140d4010b044020981c0300c7c60755080c207250501c000e100e5202c210303000d040d12404000c62a111441ca0310180c03200b286440c50300b61001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 721027059 1250 721025809 721025867
    0x90302280801060501090b1309111605060a0501120c030b070e030307080901091a04050d150f0608010c020a02030a1502090607050601050f01050711090702160608090d08040b0f07 78
    0x3c1c1564010507002660201001510420090680d011401002c0d2804c01d01c0703240140840c0146010f8002c00641c039014040c41408081001d0052403030390203400680401d2070185445c07400c484050b006010508407040503413020512164131764081c1c03680554010b40e0754490890035030f845000c0d4000b403945807000107100000c1142c0f04003e45400c4000fa00e900250030f40710080702c1d240040502d42e903005140c051004024600d0120f401203107032809004880c507009400c0c1c1b041c0c4103403805440d90300b640796120801000b900b1030900c42c070041248a440036041c000c0480e03000907214044000c015095905032003440e051030050b031303040f101000e41c01024143c0d500311a01c0c016468544c02d206482c8513005000780440c89502940c00c0303c41013644804407880703a140c0d54007049490040034000000f18801c110444108001c2c41040070007801c51074990740300a141c80030009152110184004041102e48401d00c8000785100440d00d400184006050320160b45001c404c80d060842c030100441e100c0124409000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 721028309 1250 721027059 721027061
    0x303020a0b101a070b0702010b0102101503060f0e070605160b04050c18070206100302100302031905010801060311040c050403031d0a060e040b19090c0c02090411010807080403090302280801 83
    0x4c0c418481c0180004564541a081e422609405229409071700540e105001000103036019040015201300b51850030340d282d403100422601c00900c5201e100343e0300e400c8000a080308004000040c02075140c05840c150428182c40700c2d02c6400c59000f010768981c0f401140c1081010300905d0b0007003001614250101c007204401000e00780781900c0b541c01600840022682c0c0c0c0640802c4070b41560340144c0740200203060610101c00943c8000c05660504d5a00b86c030380403420205000306030082641c4000428958154100300760005c4212801610031441d10701d140300800d81100a603011680c242c141551510300c4011140171400c4a103400c2c642c440c002c0034011903615005001c012503a2002c0e581000780c0400780d000e000c040e002495007549071408248040014824541047c0c11000700da142c410107424140c2d000c60640c0c1001c0d0344c116201d007070140c2020000d50740403429541c0204145482211400c107600c000c1c0c00b07004c1600000c0c0c001d1880840d03a00d408140c3e20310304440c441000b40d4400583d95078016442c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 721029559 1250 721028309 721028317
    0x20c0a0609030206061306030803040f050c04060803180627130504151109151309020f07050c010c0c03061112040c06090b040f1701061208031e010303020a0b101a 71
    0x140c82a009a0007126041140381f01f03940130742e07030b020041034a1601c658498050702c074140e480031200c030701c107900101300a62603a00400740204503985c01903444031000c1803110041910074031168050310040c0700b80e0f01c1e2030028010580d000d0b105458020084007035130000c80c01550708035140c104020b080c0000d03c0200450000403818000c0303400c000f000265100f907549641840b502c035100d0360054040c0c400e180304402000040c1005c3c089501c410503103e40c2c03480380105980001a9200d4403031130120708501400070a11109010001c00d10b8007182e518000e6540781072a030217a00014208640e503641c80000c07107681200f21800f100340324145c14540d00d020b180418618a6030300503880010030714000009d0b0100000705440039030f09a0103010080a040c815000d4605107040c0703e0b5820340d900d0702400120801e507200c042071403a000d501c0e016a217150058141d044218400301400006681000400101e0307404501810300715484548080030380c132040b660081c0760069812a02d020716814007014021796940c0010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 721030809 1250 721029559 721029571
    0x1204030809060c03040206071101090f06052809290c0a02011202030618040f020a06091e0609051c12031a040e0a02010c0804150e030c030c1003020c0a0609030206 71
    0x1c0d000c0f6500c110606219000903200250030520900140f8001071b20049003625a04040c50200603242d9605290a042000399022501013031000820600c801c01a180b8002d68134034000c030050703402060903402070a4010030b2040e5400240340c6001e140340b005400100091030365001c0d030110b44421001481c103031907002c151400c80c046149030b10705142c402d4090007070f24450307030005010b207400308080c079075130034050134001c104a600146020400340103aa41803007001c00380055079140558642030001c44040014001222800b40b001c02074100301180e0702c1004841030340c805480c45c1c4031910681ca401d44e1105101300004200d00000504050310941c5680500d032a810600c3e1404000c02d43c003001e020407200950090403550b042480168095400b0b10030a070032107803262440600c1c041c2da840d05802080007040261000441e4100358180602c1d042000c02a0000100c015100282400b00002c0c408440b00d00003506140d0007090f803029180301880140c240b03a41000e001e111201d21840e0094680340700b245c00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 721032059 1250 721030809 721030813
    0x90503010c170c0f0702060316080108160911071406150d05070501030b130507020d09240e0a0e0109090303230a050a0e0a0f050d031a0f0102031204030809 68
    0x50407000c18419926410308030791103401c80901e0740f03980240c00d425500022204d00441d03130070094500161541e00c0150b04c9909070740c4095040602e0aa401000307514180d00051540e8030121230301c02a85070000c200f83c200c40c00550001082060100c5811190082880103030041046503240c0c40c9519010812610030401410303040365001411003080024104150051700c1c0c0d0303000000511895011f42e019001e0510020090b0903c2911484410240d0314229406d000507008810301ca513010343c02213040005082c07017040e800d000203800301d4845050084054a0741c00c000801e2143d0350385803240b401d140050020103514103019078482c070049001c3c20300b200003200002d141041d064844c8804d18070a00140c000b051000c885911001d600703502915024045000581c0c2d03554003081c3e02d60003040640080d0303200700c175840b40016a070704000d424510321300301030028181001408100036010510030600c00d03030220b070034000303010030355004030700d54007c03500c40c4151020345201384410706804c000c1d1340d032041c2c1844c41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 721033309 1250 721032059 721032071
    0x3090114070c0515280c080a0b0105031303050405100834030903030615020d120b0a0314010e0d02031305060708040b370306050405060f060a020102040f030309050301 73
    0x1c040700c1e601d40c07003040038025801ca001c40011132030080004540042d00b5041c4200d1402100d1444860241c4807000c0700756450b0368802c142c0000b43c02c074000d01c1d400103210340d007041104800b400180c503c1c40001c0c038041c0c1d0f008040385c40004040c000e01c03e85024000182140986985207a0050f00d82801541d1030b1000058010b42d42c900c903001c40000c02010305001004102d174404910043d8050b0110726021000d2640391100401c101000785102e00800005500410011581c00f41c00b4112441c9081c100729128100303108032031907459248100c4200d9500c0801081703882502000d09004281c0c8010b01202d50244021400609a00001a10152015002a5802c1591a001c001d01d0740300d84000140100d0085c08100160314140e0043c0c0340d00c8403055800d1400465940c2c01b0199150000d4049850b018011020b0200396414400d01010b40400c3d5400c100301c0c1002c80009928055258070300c0c0c07040d5800a904002c0900c02c2d01038400409000a504c902ca81c0c4034940600081154042d941c000c0d8a01070b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 721034559 1250 721033309 721033321
    0x60806130215030705041a0c030d020406120504020a1203030f020c01090b07080709120f0b0906010f050621090a1a06121b040b032505090c03070f08060f0603090114 72
    0x1000c40740294a184c4405103018501415090100c002d01c242c5014084107215104026a00340f0090011540034030ac01642c03a400c14102509039160102641c2400d80740104100068440c1c80c81c802c00e885042c010040d146501c0d140803401740c8900d00030302442c075001040004a252054115003455032080241e0143d41d9141041294411000c4444000140d03d42c0803c020030050350f80180003c0d070161002e42d8405d203140e00d07100e14070101560b110445500c0500100311901c6000c04003000361074102d03006803400c5d200103126002c08841c1c44a04070552120001b02c2c200d580c3c200103004030560312400b0390030f144001403c0d80320031000450304a401800c4126025800c00c001154104101030500d05444446003960b050200804200074130320381611aa00c0b00300f0329042c01d0708061555006801018010314200420300c0011100942035010100081c4188900c207900b003503441409045d41d02c0c0100f00355481c0c100084c507d41108001c0c42d0803500000a200303a03010190070600a801c40c10340304003982e440e00303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 721035809 1250 721034559 721034599
    0x2130b042301050c061f03050a0b0702010b0a03020f041d0a060515010e09360703062016050309041406010305010f08070608270a0b010b03010608010312030608061302 73
    0x4991824180d017103800001d004a00d0004a0000101d0002915426946030340c0c0b0589070801c1c100007a15001c10b10420000e04650900030401c90711010348900e200d080c917541c045006400d401c0403261040762141d1011510080c0d96a0840500c001102100c400d4404d47c01d14000410f4140c03042c03840340b841c9010b040b0081d40901b40d101c00680024007500040d64a1000c2c1c000401340201184502c007070841d980e244a8024076004440f1100c0000140c001c7c103181d4130340b003c00c0382c0040c060000505032200c038100c06840044c055078010b090314103105004052900d007a60070b40c4640c0004079400752910805103514061025184e10401c0c0a89003000180d880d24090002d10300a403007039980e16400080180009442001010f4105521040f01c1c002e111a1070120210408815044d028941c040316003542846143c0075a5401041c0304e040051440d410a14018241c51050102601c0c01e01360030086245c29200b6885100144a807500384e404a091002c1201d0210902200071391049240080903040c8100c1d07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 721037059 1250 721035809 721035817
    0x3020c0609060a0c051f0e0f070b0f031003170304030e03011a060703030603120e100306180b12010507050415030e061611030a051201090e0c0402130b04230105 70
    0x40180b03540d090089001040380d4803404160100ca840c0503624994844845a003642568501d003440c01081c10324070501d05503c1c01407600004400ea520050701001440c5043e070495034032070914040f084e601da440e02841c0c2d1034164180d1006103142c00044100c1446611200a580514425a2840c02020300181094280c0e03030000e1030b524512441c1d0207009003174948403004080b4a0300c6414041003040d41c0741c40c1e201541d60391340c0c14817000c1103031889130000c00d1909100945450307405080400509060203401d1600058031103041882558684101080e0340e1891b88403002801507000901c0a850306070310040140d00b2900c07070b03801262241201d03044114007a00400b028503280000402080c0c0e00d032241c6025018070300c100b86003070207090702ea10700140700c040c130007031041d03009039180c0e595280907058000c0c60880059104465007072a003142e0480f440e8003c5102d000310380044501584074400352a429124480a500a40c49408000b80018045c1d814504c207114440f01182c83c580000740c3c0c10015601489 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 721038309 1250 721037059 721037077
    0x2011d030a170a1401090b15130515121f050f06091e0901060f1d0f010c05010f0f060513060e040803040302070b160204051f0314030c0706080403020c06 67
    0x1810b210b40b18000e0010040b035540580d800c034002c1a016160341d030300010b1a6003030300000300c4a42c83d4051001a4100002d0542c8010310307400b5180d00c0c0c040e01480c000322800050294910912202100b003002a2040c015151624080c10324a0400c2c1018580450102d14030030351812036109180300000d8519080507031022007c400341100f0b00c0e0456281c10001c0154540c012003a030f2440251140845440d4140b050b406017000c2d440e240d20702c0c0c41e031031341c0901600f00d011503100702d40100762421625504c540340c0300b40c1c21080038203010b454442c9525025003d00050f900c24000c4d00e01d0045544030800c0c594210744200c1e1b005903407084a0300d803800c0640041e100ca90294100203030801000c00c0c0001c07a080003e55000d8043d1041d141042d4413100c12511660141207006001c0014105503400d52410f842055000400e03c18010707001b640b0078011030110940c4d880050249003404550350b007840424000c84244410b54010740c5e40c4961201c20240007964141c2d0180d0040c13042048000e030705d0038030404883c0d4000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 721039559 1250 721038309 721038317
    0x5011508090f0304180f0e070303030f0506130507030605031605040509010b09040f0f17040e06030a02010f051b150919030c020d030521150105090901060c2102011d030a 74
    0xa0900104c00d840f4000c02c2d41310841240d48071b80040d18860a031140281e900603c0000d07000c2513141d402c0c000e084d10b8584103651a80d62600b814041c0c04c1c4d03221070b24005d52090481000c81d03d544c6541c401d400a0100d540400e405000745407800c100e045420554400350b410440742007000c1e86078485550f007210040300520740c011502001040100310030681d040c007002e100b01241c8c42d0914a65490480e5034a03005101d050001000c54144181c03002285525803041096005220703031001c90b00000c2070070700d40e5180c50040c0300d00020b0300c03035080d692420043c101920640440f04403c640e0f180c4854102d404903180d455900552110329880b0303a4402c8410300068156031000142c1307003c1e801300650285695011018081c0c2081500300d503100c3c00d541e40da0b1204c1c101001400500e42151008266802115014100201085100107541d100491503040d0b0b00c0515105002e08510300d090201d00c00c911461008000b1110404203003590305420140080165000c0041c1e0856403041c4999a4050920114040303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 721040809 1250 721039559 721039567
    0x9062019082a09040c020309010903030302031b03090a111002030702040f0e1b120a08070605070e0d060524030a240606091d01030507030b070e0405011508090f03 71
    0x5500c10400650032201c00e00311800c0020040c100b000d024400301a0b42c0030540000320740109035161500c20f4845546071030003c0c2d4548032400000a188680501000342815800320200c2c540c103803400e02c03030200da4030807403c40f5540e41005a0519580c1298001c200c4040a0300c1b4210f10860078142611070002d445500118242140c0e6402c220151420038010b03410140c0c0c0740c12a0b017000d0302c104410710220090519452207104000c045c02183c140c1d0740c41a031800e9116030612400520b000045400e100d40003500041d030b9407190030080310f0341d1099036441070303120510088200902403180d001e24061a40080c00d507a418600e4440440341c518041042c640c150480903a290103c2c4000a00e50750301c1d44040c50325882c03040c507581200229400f0b88c00010005100003814009440c2041000c0c8041c940380c07104071081d61555075165a219001e0100400100000020541040c0609810400d44800900a100c15a107034a040c410b034000350000c180010310303c800820325002000c01c4500d05a892900a1490 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 721042059 1250 721040809 721040857
    0x903060a091e0807060e0105061315050303040f0e0a0507080c071a240603151002010204050a0329150f01051210050909030910030b040e01090620 64
    0x1c081e81501954070008200765482e8440c10a14880c88882c07007000959191220390502c0c0e021501d42540d010303000da151034140100b5030b60b0741d140040042d11820300401c514810251803a80d80d04161f0201e030701484040340229166210310b0f030350300540f54040c1139044290f0b50328400d1000c0d140180c510002160444000c41c1d041c407110401821514081c6492000e0f4001c401c4103d54120b10403030340c0400c440c03a001141000510740384000c14050904603080e6046061002e1000035842030410704a1107004028102d0340d03414000e405480044c0b00007484500b0306552801c1044001d613840d0311242040b4001d413425400b03001c190900e2402101100e28000c540040c03030f4103000c03002c0d01104405041c01018020b80121130b07500d07200144600907600104440c1464042403040305100075050203400d810034018044140c84241042114206500e4003051440084000c01c0007060401701190241d42401c41801c140100e68008818580c0c3c00c084c1071420704c10000090b091406182610304840b041500c00d40c0c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 721043165 1106 721042059 721042061
    0x1b0b0903100e0303010e1b0f0933180d05100506010807080411040204080f01050601080c04051e1807020d08070503040827040c090f0503030903060a 65
    0x40354041800e000d40c0c50b401305000d0340000880c100c0014a541c58080c00c1183d03855444072046507100e800102118403a808190514001c1d001c105202c81140e00c9069414081c4140b07503c000f541103ca4500031925034400e6111440384a81840340c1c0c01140e491248014150348514001c0c40c9030782100e5491000d032813001f400030f41406800000c2040858111000c0c0354015440700400c2d1203a140c070310005009004940101d8018824042468120041503000600650090300c5a0509030384134540b0807580d02c128012706400c0701c400050907041e1a80c1505402010b90002c00d02e60707442d07a0150b1903141d180303401c031540c1c40164040c0d05030309480c1d074000428a030021040d20f00b052a500d1b06071035520311881745082c030040c412143c2e000485030385041401d4071394900c8000c00604c14000c050350010f01103007060290b09030145007030b0000a003c3c50300100701d41c00100060f000d4103135540c0d140c503c84 = true := by decide +kernel

theorem cover : BRFrame.Cov 720863309 721043165 := by
  have h0 := BRFrame.cov_init 720863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 720863309 ≤ n) (h2 : n < 721043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
