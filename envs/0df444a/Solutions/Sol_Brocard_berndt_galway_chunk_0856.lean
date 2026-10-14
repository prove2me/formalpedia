-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0856
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:11:45.057287+00:00
-- url     : https://prove2.me/submissions/4045e2c3-c580-4b07-bbb4-b41d96bb5fd1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 153776978 ≤ n < 153956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 153778228 1250 153776978 153776999
    0x60f0804170a0c030810060203090603070302070b0c040f0f0b0706090213090606050f060702010c080915030a2a090b16080708030a0b030111030406090c0503010609150506090a1a04 79
    0x210b5205541e8011403403d00b41005030003041c001c0d01004520450040500115030004100c500c0c1d140c050380d0050b6269035041040703000703015180000b85801c200704180012684884050020b4440c003803224070703800c0c0e41c4c1c1c8415840c0210344d12604e10415030a0100c03101150b4964001068a030001d00340441130327512169803004450700366004982c0b5540c0c3d01e205000c541404080780103020015a841490800550006031046107440002404910300299140e4182c0300c04400c1000c020b0301100b460303102d040040300030016001c42d0007404034003c481080d03901c60340c0c20080d20358103c07801601c50141c06c13030074142070b100e4a074010040c02d040134605402010000d410b010003403c0f0907000700d00454890615141000c16109015001c40c8039a0500c28107001c550a21030480b90065400200040c0002003450109143c4c03990f9401907515501e807000c00034041c08690842550304616160305140a5254400c010f107600450700d445820160803401071284c4203106003240410069092420b003031644c1c0320070240 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 153779478 1250 153778228 153778237
    0x130803180c0904050303130503070206030a091101020a030e0d1718090f0421030e0f010b0316030837020a0308011d04061d010609061a0301060f080417 66
    0x154100e008114001246105000c046000c40382110070801c42d05140c0c440d203903680030240506884041d07954003a010000c00b00102d42d5225800780400d5100c0c6801c201520040c403494106030351f8450740454451183d0320104400e03001561580f42c038002c0d00850300512107501d0340c3c3d900403030f00c0382c519402054805040304040e21483c02c52085814111907100184980107002405030104041000140800640380d109008040e8003c0032071180e5500d0b10000c200e001d0000c86040c0004c40c0030b03450180d80d8500040d000001400790680c201c40c10710280707950402c00381c0320920000c0e1440348144a20340f040001c10503090604a460070f200440710783d1210955034841210305102c00580d0000e0187c804041d007205100d0b0042501241a000c401c0c035035401440b4010000301f0082c00e080e0364100d070021251001300d8a0000001c000c1c001c0203080e4550782c410004080b14000c4101c0c1140c1042c142c00d02100d03240440307040c1c806030307030fa1148141c400f1002030f83c80303130400341080340c05030320041001000041103c06070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 153780728 1250 153779478 153779491
    0x5070314010e030408030412060f0c0c1b060e060a032018010509010e04090606270b0405040c06030b0609060c030a090503120406080408040e011d100e040803130803 72
    0x410503103400210381d0846002c4040160780e80c00034001040b1010010041d86d04880c002000e11030780600ea890302030002c100a0300300b0301701c803440c1180301941c46030b0281c000c00720f642c80703000114406460343d0701c1d9807617140c0140301d15000500d500941c2c000504040c0d02900300d003482d50601040c070000c42038150101d0411b400307081034040404a03050310709025030504030301c01c2a07003030901c1c07072812001c00c000030b0215210a411078055a1034080c41c08c04c0008592101000300703401c0608010100740000103004061144841e207107018204550480700e85028860307a4020355000f078400c10000d18000f0300380c02500c0d10492803070388900144071904403a00d8400060146808440c050365030b039034842070b001d41b0401c05600203e0190340a103100294281c680d80c00c981c19140e241c240014150303168035040b50188a00c0c0c1020380e414800b180000303036170040e641d448c001500542c51400c00c10713542c1030000c140da680c2510070025220220004a004038030b0300c0c001940c01c8550400310010000da19101c84000350b0064644 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 153781978 1250 153780728 153780743
    0x5070303080a0c09050904141c0906020601050301141f0b12090607080103231c05041d1303030b01030219080601020708030c0622050109060b15090a0e06060403050703 73
    0x402c0500c80c014032400d07030b0850460404025480c1003002180d0340c0740740200024114240309401803074050041005617550b01820444600d15011034030002c00039280c600c1640701621840c8000708840ca018000e03101c1c0071490821f401255a203044241890728003503c0070195181e40540301084c1ca0f0070f200000d00c142c3e0040c80c95070045040c0b24000c28504640208601c04100f81400184006403056002c9041c2010406280407005001d581e1103042036681c10384e100c1d04540708181c0c8503daa420501600855041201c41880001008403441050354101d41c10a44000200d00d0040040d00a52240e412000c040c5001170a04400382c0501c503c0345030318200e842c086001303031003044000d41e41001400050640c050103907041c40721100304070303640d004064142c0390044010a4054440c255448402400980010081c8199210780c100034004080e05040c8900075a0319507466070b080c00818041b80d541c0800500400d48040ca09a058400000081c10305540a84104400404102e003044807130040d60082d0342c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 153783228 1250 153781978 153781981
    0x6090a030c0b04050a05010f021b0f0d05060f01080d020a120905060d05040501050718090e240114060c0c04110c01020706020d0b0a050d1e15020307140408030a030b06070507030308 79
    0x301306541d05c06902c50303030401c000c0e440d1080f040d560201e13240503041500711040002028400c001641c6810340d100584d00301040100c4081070200001c0d000c1e00611a0329000305060341c0712440b48d51142c1c2c2e01103905015a20500c0b1a800103103020750034880510080ca8403c2c2080d41302c000280c00b950120181420381610ba40070b1105000080c4105500038030725080132440c2d000000c0080b5400b40c410301c03d600000f541e48100700c040110604c080064404003088541d9900e8080c80c281c0c80b440e00a005d40c803143d400c0c0d07110b030703100c1810070104907680071116000524504074101d0030007004d0700c002d11020b244540248040311006400b4005002d045102e814050b0701c8050039041d050481c2c0c031b1410403c0c4208409501003009442d000c4c0101801600110514141000c1080c401c1600c4070344040146803040360804036018150f240c2c051405141241d450011a076640403a54040380101e01507020350b0b80040059901041c080d0b80081c4000d200034040d00d080107401d4032420308005080c1d0040c0e020408400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 153784478 1250 153783228 153783239
    0x90e0a020715050112061d0316110906090f0a060b18090c04050d02101b0605011404060f0501030f110f0418050f04060c050903060c04090c1b0206090a030c0b04 70
    0xa21403403000298404104542c500340c0c440652805c4200040c018540d0751100220305045482e030090020400c80c100e90b99905810f00310080c0e40400305050391028200b0300c000f1050301c0c1000455000d44001011842d8640f0fa4441c1c03d00c0c00d08004e0600d210aa944a0000850465040203000480d85409003050504038030014846541401400d0717004010b800c0106124a507100d0058400c100e0f0148c0b2001c1c031800d44c04030142c45010005845640c040250741c13524003000055040382d81030761a110300511441510000380710a03940240200041001c1c04c10041c004c65200c0d501400d01005034550100351243c00043d12000c680c00a9100b24808000050910140304540a8010034400c250820005440c140000d0002954003400c01455281c840c0c0d100481a0b204000360780e121a80103003a0751050505161f8107050b90711a20a90070b459040801c008103890041d000c45400c80d0100b04010b080404941c00c00007254889411241e0149000b08044082148015800301506142c141e417990f407420070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 153785728 1250 153784478 153784493
    0x20c01062103050304031b0602040302010314070815030a060518011d030301053006010e06030c0913031701060203040801060e060d020114160b16020106030503040b0a090e0a0207 78
    0x40d0400700000803000c50010704400d2612601a0494140c034000b80c680c0c41d20715045809018441442000c10720014200051100c4d550050007124800d803000c014101c111214004070003c202e406402003a41d0a0000e9882c9001008030007030340800800780c0d40403001c507940b20380c105c0390262030305240e0f0102c01d00a25500b000910038021030150f00b0003c0080f02c10f805d0110382c0c4d20b100502038a4003e800c1000461030061303168120039010901403100301601280081070f15607408091017884544011840491118280401c40c0c228410025004080607a681081e1030b00e07000c00c2fa90110300300000a400b1219101504149502034100e0f0340c0038540d80d6180803103150039030b411600450b0b442d0000d4030904c602030343c0d103101c0071032615030a08144e04e5011018420703260500410744071000004403402c400c1c1c104074610b020603100d5400039607040c40280b00342400302c6c225901400014100d0303200300418080045a07102074900f4030417905d0150381c020b44800f034414200e90107581035451145c011a2450820420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 153786978 1250 153785728 153785741
    0x40c0207030506070e061c11072111070605160b1329270303070306030c080105070c0f060b04110403050105070e1e040f0515030708010605060d05060d0c030303020c01 73
    0x2480d041c2035184070b030300c00580d047c4215080303a510481440c012040070b40b90703500004020000e409401d6201c80c00c0e82040500391300080003510084204440d0224805d010340c01454034840c081c00245061760503c402a19154014140c00e00000d00003000500060103022250b880f401540c00b00e203941968625001c00042030351015140e801c64140c00788607440b040c0441803607000440c0c16544808480800150380c0c4072840700740a100b280000410000f1054261b040801105d218000019405986008003404c0f910251280e80c002881e000301a0007203041c2184403510b5a0141c0000240c00100d2400103086502d165510003a0300404142041842001c0c4140b039071048060501d07440042070b90001564000304070781c0c01366100c07078825212412615143e000307080d04019214208064141400c000c0d00c030044c0031421505ca48182d00c80851030030702c18000c100442e40050100703411b040002c500400945002001d281d0000e541400180104c0c0482e8400c00040d4003035100180c0c0d60706c25a101500b510203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 153788228 1250 153786978 153786991
    0xa020f0604050303150f120d0908030702060403020d021801032003010c090506030705040305031c0c110a060504170316081006020c0402130f090f0b04050103081215040c0207030506 79
    0x55030400c800725030007001301c0e603014503d90982d00000d1001800982400381c42a00c0e25000708800003010302d018400610706450144984841024950b525080c07a40c0b403168400c001e40002d400d0204000604204142e02e00c117034401001c18816111540700e910241c5026031003a01c60000c0301000000d6201d51410580c03400c10150b0013800038200041000d040e140e00d43c45050700800c000400030310791038071850698002c4e592041c103803565000c5840505000311304c04501000c5140c40c04241041c0135001c1c0300f6444400368444050b241d1702c810b0f61140e00c000c2c038009100340e0300703480e03585404a901c12486000f14402e003100c4000062841203010028070742040109501c1d0354460504003403013425000a916150500d0441e13016070345000c0715001540d02410b55110362040e0818550210b41c0c1d11a41d0800131120086480c104401c403d00c0041000380c807406e120252042030304025800c403002c00b081e4102d41c841d402c00302e80d80d000b02052020604642c0c60441c00001a0030140341031003000401d01c1600c0c0c0040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 153789478 1250 153788228 153788233
    0x60909020d0b0402061b0604050f070303091e050a06051c0b060d020d0612030c030212040501080a0c02070e2412030306131503060207060b04090809060f0904050a020a020f 75
    0x4560200301034001c07041000e04645449000a0219a1040c0482c1c820400400905071500f803800d00ba255260002d65080b511400785614418008800140c40c1c01101e8155640c60390390713482c1c50400001e0035034a80b040131203a10405c0f400b003515100c1490900040007240e88159591b0001c16040d2050001026046841030402484007441d40d00c40c000d035407105000c0d041c0182e44409440349500180419404940181d00c3c0c0d02c1c2c420281038001802410b2180070341c00355a440c0d030103910108424891806801d0108004801107944006a0f911100d810f40312401180c0801d9100d1395811035503241280e0b03c090004000d41d10b4640b1136401291103032450300540b503054085091403211a124007000b040c882c0590081d42598144614a03001052a8801001c007411099264140000070758060303401030352001d01f400c4440324542040e11036440c4c1960452105400e21824904019990340042020b945842c004c1c058142d05980ea031040c240a02d03c821401641c42e0342021010b42483e880140c03c85254 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 153790728 1250 153789478 153789491
    0x603030207060f05041d010e15090c1b01150602010b09010b0f031003080c010b0405060f0a033f11060c04050d0309080d0801090e070503070306020f0c0a030c060609 72
    0x80d4000a405003902c107181054400c03040500c104035900d02841e8807000c50752480d040050450441c070452103040e920409409400d6940d101032003141c04000c09000d5030011030140006015812076009070090034440c3e5040c141d54440d002c0018291071045150314508613082030f0802c180d540900c2503040722003042c0c1e42490a50b01d48400b594042c09030101e003400c9003d00100080c0d40b03415202040c000740d81e2084559485100c480c60950082150000450045141c0004148180790205040140140040c07100c80350751b045039138851100c0c610700a02c1e15024441d0140001c1140c104003426030740001c180d20016180e521a10040a1007464000800640c221400380030007003100404481c180d60080d600d408112840303107801c0b105041c8076400312490380200c42b024003005621402c0d41e4101c85030a94103002c0d00b6401280240c84500c0b511419a1540c440358040000940783c6e00644540c410340940a0b09003108080704070704080350840704900064106d458402040a21301c40c9001400458a007040b48 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 153791978 1250 153790728 153790733
    0x215010f060801120503070b1e100308070f0606120f0203011d030304172502040f0507020c1c0f0302070f0806010b12090106051207291b0309040203010620010603 71
    0x10410601800071501c081981603030038070108000f1603070802da0240c4403944600d0600c200600f425270441d203100c90076030200e0204561034211544681035980045020703207031040598030403404401c00802183d10b01d464410000d4100e004081441c4400d00402010310800446c0c4100750840e030340550720f0030721102c0b0304100000c002d40000c04d403036105600801c807040400b0300d207200d10014024242c3e1448103e400b600c003021b9203003095094000c680d2090b1000d019410000004070141c500480b00280107034407500041102c5d141c04400d40381c60250000030003001ca00c50351144082078021640503000b503808404208030f040d8070174445900800b00e5001404070323541427282c00c0055110707041c1031111641c1568045581014298404801080010003100d842260808001d441d011140724400070040e800404c142014003c440c0f1a075100441d002c410b1078041e201041c003c00c0c4450000d01c4005201c14801d480341c81c1c031184000c40c06801c040d110500f202001140b084183c02c203030500010700782d051241c00c000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 153793228 1250 153791978 153791987
    0x8060d0302060106110f010203150102150412031d0307030305060901090908121504050108010b030c3a121d18010603020a050d1802180907050402030c0903010c0215010f06 75
    0x10765010b03140815400380081021840d2480e4030146d001a544000203000d0354007210f00505036075500030303021307500b0700d561100c588201603100702ca01030080100ea007450704000f4800e6200610003c403146181140720200e1034200c0c9035401c02401280840e03a10070601906191130481e50340101511001401640c14640ea0903100c5d0045001c1164480c90210206450b200300307408486400401500411540da0341d1a5454041d002e8070740014044d001d01c0116240320300b05100e460000e41003189003032400f0058800405041400d006032b5044003480c2c9514003000844400c085e0050101c15a21603500307102200ba40c04030700c09240c15451042803014140000f60010703005003030446243d4100140c4620b586102903d86e4480e0320144410796160044d44c1040b001d0022440c4234450080d540a00c2e5440d540c0070b101032190084c2c1c1c148089a001d03c804000e50702e070079001160301134a01200c1c941003086410219003074414106280c030142c3c010545044a04603041c401500401d180203424140030b00d08071003c0c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 153794478 1250 153793228 153793231
    0x1406040b070204020a0507060509060a1505220612030302040807060306080d3608060c090d080a0e13051e060d0201080411060a051b030a1403100b0d060608060d030206 73
    0x74000ca40105c2d440c592940141c00b581c90407604200140290301d0688070140c0c44d601c040b0303240300d52981b0b400b21400038000c0b6204020140d5402616048000040312405100140f090216502c10fa86072480443c809003c1c50140c0d00c0940b10740c60140c0c8903403c0400690030019142c01c4503041600d481405c00c0508000a19450310006034104940c82000e03080f242410b841c0080c3c60510100300308100c200c01540070540302d104482a18007a50440d0b1500f0207500010321960900c80c0d4080c0405c000840070512030700c01807804501c035017132061184010001003000410701d80c1c1403144031036440c003c10903400d41c01070850f001e4040da0f1245441c1842d00c5000035441e00720044000c0d04000607040068100007100c0211305154034001d00440e29000081c10090483e40035110411089800b60311404240900000f80c0342c99a4250b15901000b0305041180d080540004010080e080360503500040d0100440c4010315510440d10004620755041c5140a006071402078440742c0240991341101c40407a03030220f0902d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 153795728 1250 153794478 153794483
    0xc080a02090708100807060c111c0305030901060f06090914040819020703021c0311060708160c061103150609100305090a14060610050705061501090e101406040b07 72
    0x8410035244c240d114406038016402c00d840381d00c220000420141d80041554030f140d0b00c100d068074051603890b410701610141004d409401015180d03091400039014202655103c234840000041d000c0c1e44d0480201e0702540760f407012010400156045c05803501a00a075035a50315442c44900c1130742003966803080d80348140c06281c00182641c0d103100c6401d178424408100151f030000d0051404132241c100c00c5001e50702c080390890108002116910325070001060503071083c0125161600c00380d9404031428904100054040204000103c19400007221485415045810310302e40356124907100400c0640d4144980f0744900c1a0414426055941e0b20401c59040088880c900828542caa003131718986001007400c8014503050b03901c8014101208001031507880742900b155402014030840e00143c030b0910070b11202410a8000d4400189400030680e4449400034041c036194a1440e50354194045220b030580d0340d000c070303401152010420403520103c440c142110454031545410300d8203013091858825802c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 153796978 1250 153795728 153795737
    0x91109030a030e040204080703080d0c020a030c030c140f0d03061a0409020a05070c0b120112080304110325051201060f0927111009060c031209140303040c080a020907 73
    0xb003088544030b0740c06440042280008481000d6100d01d41400e468001418602030300d864010402a45840055031021590705600c600d02010702c1038504b03ca6502c011201641c2035445012843d03070524080200c4903c2541220180ca420501c0c40c0c0c0003010b8078010f500c00c11003440c0c80301e10400c0380c54801c1c046400300e4017880c00c01030307075103500e003405660710b004000018105040c004000125020003000a01d20030308071111544242e03885803d449c00785010180d018201a0003031001800007401001800401d400003811030700c11040b402a4070180c0c1000082e20402003005840c00c01003410401e0560b480070107001d009011035800e0411600048a00d889440344058440b61201c07a4000500d10030302041180f030500c0d05034590300f0308250300f009411601c0b4a00070940589100d44044c402c0e1243c006a030b509a60359140e600550320101c85441c0e080303150110240d52070400100103019960300c8103090304010040c5460303180904040a654000d035003d841c490f040034a2a40040c0e48020b2001e071f100d840303810b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 153798228 1250 153796978 153796997
    0xa0c02120921030c0d03060905040816050a05030a0f02070806040201230c120301181e02090f0303030103140f010501211a0f0621070510050c0610091109030a03 70
    0x402c0070354000074240740141c00002404094041c01240044103011a51414854240d80d005940102e40742107801403e818010700c09014113140c8084200e40b40e81c0200100e07a1120442d4032054250b0f441444104045441910780d40351140e0103000000003480c5170406401d540c54240c0001c0c11080681c06a80c1798048928040c0854180d2070003980c8100c241107084408038160317080c184607154020700600074444032005032800300341c80394022950321110105d09880c07050b10030038040000e508200000303035100c0003403650170b007503500c042001d18001e5010310120307001041c0600210b0308000d202525a11980d0504005100165060101d440e000c4215034900c40700501ea400c2c104484500c2c5a20417205035035031000c4c0124801e4030304000b4043c2200f218440030443c0c085c1f510005910a440c014107068020400c10051403402003850f0311801101e0524501d40030f0450319160078040308881140300c44458010a101c3c00ca11449508005038000b503c441c0341584e0900000e40c0c4852410009040260420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 153799478 1250 153798228 153798259
    0x61203031d0d02070e091903050c01061e030209071706010806010c0203030d0b0405010602030412020907090e1612020a020613080f0408010e1605090118090b040302060a0c021209 78
    0x4a0941e0701d03022581a00d010380034210b00207499149500c19440000e8a42c0f02207100c5200c00306903455802429071000700c4d44c0c2c00b9a6015500c542049080304029540d84070001000304c0800c50b50944420013502d580700c0f86040d0720410000007405441001000100111b11007428250070495401030b0003400d000707a4686e28070300101d5260054580094042c007002c610f5411034000d68120700051b02c0c1c00c48081c800e980e255001240e0fa400340703101e400048406c0400410241c1003c2c408030b5001441071800c00007207515844c003400031040c00c1d1102481031b01024003280e00668059107119000c0c11006c4294034190241100030b41d6004060985070000d42d03201202410400b40c0d004651720052a41201a101d65403807030791600a101000c110001e03405018804200c000c410346002c0c0c26150b0060843c0e680f642081d04090144410085114000343d0740d140140c085595012024400e51003540106034070b00d840300d500c80a54107041c51140c10b550100350140300c0d4203115030681d0401c0a05649000d00c228500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 153800728 1250 153799478 153799511
    0x1030602030a0b0d0b090c0609030d05090f270c030f040602030702100e07030c0e011512110708280f030e0c0a0308120915010b0f1c0501090605030106120303 69
    0x1119140e0300a10413901d08040111a00002e441050a1429941100056002e2000501c50500c003164160800d0502e24102d074015006400d20140c040d0004121000b4007000c02c0945500d201c03140d1560740d25000c224440c426069449603c402104440741c15803d0004114401c84800fa00080800703802000184449100b0000d2003d040c403000c0041c07000c1d0040b0b00720313203031640d4580c0030507500b044064401003038414948020604171100252803241500c1c15580454200c0720b0383c0200c48246844090914180c2112400f0304100d0f4040c02d621a650b0035410101402001c940c00700561007414400e03541c00e042d4020698a40002c180c0c01d001c5210002c074000c15081100d0b00240f5075000d4482c280100601a440d005822082005003140484e52514000d550b42e490080410340c1003a0300c040014809901480d01134900d082c0402c0c41641814440c00c88121810141d002d02034085545400401001c4654090b40c401054264002c00c5400d0602244580c86500c4000150030b0580b10300b204841100e81 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 153801978 1250 153800728 153800741
    0x705040e0a0c0e010f0614180307030c080606101b0305090402040b030c03090c0306012102060f120423060c09120d05090a060f1e110f0c03060a090b01030602030a 71
    0x3880d9082a0740d142d5026441c01a828012201c8a01440c480802c04500807d40300d41e0090301a40064101504205615070402403a281250076000e00d06000002900140d000030142003000050859450104140443d208020400d80104011144043c0c1282c0c11010030340c840641500d030407a5580e95007000f0130040d202e95403108016040001c1002810005c0c0e1001e140a650b4603000e48400050070b908040d40c94100b801080400ea000d290b60f02ca03211025240503204902c054903603805c0003541c1c0003c01985d04040c004c9000310843c3c00070002000301e0300c1446071400394280c200d416420404088155035417402012154802c400003102c440543d206a882c0485944910480300e04145002c40100310b5000440c000d80038552039440800c0c407600400001d14100340c940d64110b4444d0f040503598402c2056a80b00b030302440604030407402c80342000c0c020a8512405500240b80080b0703100145850600001c140c520a47e142400359400107080c0c11b8000c0c1100d4001d01c0150701da0301c842c15840e004005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 153803228 1250 153801978 153801983
    0x60f0918070b070302030c060a02120106111f1407020d020709050a02040308031e130b0c07030c0215121005010203040312020f010212060f100210090c080604140d09080705040e0a 78
    0x80129481d004c1650000050032044105404c1e0750840e25040d521609070f0248207070902958403140c2c0184401c0384201500110040003c1c200c90401450b030141c2c02080407810711003d0400d407186a036506c00350307107090260781103d11440241000b050455000752944510700610300400d0316400800e20600686e010307a00510b4000081e02d90b2820116020309090040c9800000070b00080e00019400d028407003002c1107215001911840b01e40d55107024580b01d5030041c04224144580e01d4110800758075184d11240b8440d2101c149140d50303104940315013269503402001c00ca0240c260001c10b01069a02005850440b075106010f44d4030124102c3d41613041041c10540b15200b5031000c41c1c0100e10351811306130305001e02010b0b070360319641480700403c2c0f15503803400142c0c881c09139112000e2942000c000e0342c1306400e4140a20403510744c03552582c403000e06140e800c0d2000c0e01c985004001c4099202e40c140005555140b550a000a9141c9001ca0450301d8011341d214a5100b103903680d4284001c10424002a14541d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 153804478 1250 153803228 153803249
    0x180a0e011e12020109060507020d0b2d0103020a030305030603030d0e030d11090306060f030c03060a091a010f0302092e0801050105010c08040b09030304150512060f091807 75
    0x1a107946009040441e203103480600840900030000300e82c0b60305880242c500740c06a4960071201c1c00e003c019620b540c4071070300490304094100d04040c0465000c1140c540180000e800c600e81e46941d2a01c400190380680b810020010452001000140e54442da424216945801c0c120344030350710800080c1c218000c03ea010511182090740306a030b042c1d40840100122281094100308020400c6160700701c60242d0414150154042c1c00420103d01d405d0b011540c6542000301194128116407012174140003043e40c6050f851a128139807541000000101391141074490b0401c481c040d85040940c4003640b41c0c51001901800f501c4010562491041d40114441030310315401100c1404444000c0c4249407040c460801107500c0c000012605621540d0300004890b04010002e080c0380c1010342d2280c0e00d601400c031165041c80104800211004040400100e203001d03030701c0da41d4031100c29400b084542200109020320450783e048d16038400740d48003008260040b84690684410342a83d8031001e00d40491a0410840003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 153805728 1250 153804478 153804481
    0x30608031e0f0a030e070b03040b06090c0d020a08010302040609020c0a2d0809120c10030209040209040c0c0605070507080a0305071403090313170a0f030c06111801020c06180a0e 78
    0x494041c1c2000d6640c2c1c0c5c010046a00c1e441e42c81102e594540030651300148003048078400f0600f103161082c00d0a42010b9000083d500e0074602504405c201d81c0020b00200100d01001c2c010800d600c0c0c0751103018020240b10790107502d0700580094560b11510300b01d100505038244800d83d04e2f62a06101c0d8411207041c0003d0f4202d4040b0840d04081c5a035030051050540700d04501404800d04840104078920802e0010701451042140600161f01a41105842640041e0f003400920b0b0650b5403409015851a195251403500034058103003071003078500c010854414030cd42004040b00051a00d0121403102c4018540060603446010080764200110740b0007042010780030003441007265000c0010709040c0714003088245225608c1049017001d00701c8408096442e00000f03051800300d07610310002140d0521a140c0050b201e40c46035100310403920103841d00e180085004c0384801582501c00c11260b2511403d00003065010b00d2100000d11a10581140060310841403882c10b8407500e826041c400941098881c0e050306 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 153806978 1250 153805728 153805747
    0x40f03030503160906020718020f0d240b0304020f0303070b04050102180901030b0f0403020f07080115140a270504110a0f030c29070f050607030608031e0f 68
    0x6541083d20300880055803000c1c00420107024040c1c800c11500f564004e401068a802440c0341000c00e00e81e018101c1d56002c100d0300304854440f07401400e0200c071120000850641e204210111b024410141100d901d0300000c052003107c0a20058a501607030485411401c20910740200782580100710b0028403010400050008004064018160004203000c1c0d04540013031040410280d03110038440036004141b10404180c0c00810280e44590280c0640102c420010b000035900d441d003895030b4081e285c03c0e551034014031a650f5010704070000400c07030180320750b180210300000200c03243d5281c4201c003446050208400c1440f036024050141c0c41244030010000d5103001c0c109071554a81902c03e1520416040501140315103101100c8070959801000306407a644c1041d20885186821a624610b045004140c0c0b40e240e4a07604028101d00740710b007581626102c241c0c0f401c1c42c50640054480e005040c10b2090902c001341000040e0354a6605a807441d00081d240240c00c1840c40c490f000809940d1140012801c46 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 153808228 1250 153806978 153806987
    0xa052502010b010809030901140904090506041b06140a110c060414040c02030304150f0b06040b070302161401050306060f03010f06020c04140a2406020106090b030d0c080f040f0303 79
    0x80c2c21001e0b00d030f203ca0b5545614407079450344112900c0030b022640030101550380c0c1020a000d408a624007401c00940d03507200340c850610380241101d04403401004c482c450055050a14602001007815040801c42040440301600d84e5016980c00501000811007000c2d00140081146040d003d001410540e502c030b44516011082405e04042180034070308084000304098070010441c2d100d2900602d41480080704204100e0103040c40903810703070503142c684900c041250340300030041c4002c0c81d90115140d5558030925001e428a00c2041c06800c680300202000c104241d15844240e0b02e41d142440c0441c1d40307540703040003d50280240304242447c982c000c00081000c0f01e40103401c0050f00c0898080301c0e034100c414401c010a03184a000c5c1b209030581d000700441c20a01107078010400e140c1050040c0344207500003a241c8020031001e0b501c0400141e4440d102000020042e1060a4055600b54080c10010003085005454450f01c600c0040000900182d0750501e0b01c2200c080d40c000d001c1050b403c0c604c0c160740341401031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 153809478 1250 153808228 153808241
    0x61a090a0b0301050a030803150a1401020118051c1103030705130b0a1706040b03010e0102030106090e01080d050a090902040b030703060501030e070e072d080606030c030a05250201 79
    0x24010088540301080c10070352442981d040300c0e8010300b00102541140d507030380e13030a0b08042d192807102e46003e40014041c0e45c0e42c20340300e0301030a0010444418000404c00090a550321118100705035a8900c202c00081079003c0f071901054000c00300329a0140450400071100f03503022000c4916123000100c14000c1c13480d8000f006001183e101411980c419458078401e81840c0320388800c902c0400c1000d010809114010300c1550362084d001400018640d2035140400d09407680c0184e4012180d42c00001400260341201c1e654010300483c0c0056152507042c42e0b54981e031124003084142c14040c020034074440f40c500c1511840050040c0040c19501c0740e640c2e42c80b6180d182c000b40d0701d07800468204000460507510901c903100c440c003d02002010110325100c040d09091001a042100300088550150601556956403110321400b03501c0944000108010040c151080908100d201c3c00040040c0300045019109807a000b0b055481d0002e842d03142c601d5080200400c3e60070401605d6040041c0c021510f4040d0b2009 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 153810728 1250 153809478 153809497
    0x4021903271401230a0c0512130b070903020609040207020f1008010303090b2a010f0905060907090507080403080c1b0c040f1e0b040b03070e09010e0601031101050d061a 74
    0x240b100440b64441d400c8140c402c2d1920030f4131550144000303840011540c1200c0034002d003e05040d0718103d02a080c01f0f03140d03101200c0d0840105000001342c4108102d041762030754410040e290071420a411640025110321a00d1071040c810ba4020903c442076503640c01401c400c2030801040c003030340c00744845005010788009100c154046a44810300260088904040741c4050b607904030303104000002d1280b01e2018401c4400010402d44d82c039281d440c6c1100682c4603d8620a020ba4001d0450303151280d550703032901d0842d400030603241e03042c98240200f10741c0044507250001ea15042c024400d56032105204200c0c01002c0f0340030030b00e0307000c40d201004401021440140c1f00506480c288140040e01048405942e9840343e40641c44840b00080e0302c1c41d013134560000c11080e100410210350f207012400001c0c900b140c150010351042e000d49041c000e40407400d2203140c18441d0340382c0181209615603203c1038103c0202c111424140f100005000705600c105503c8200941724545c43c004603003905205200103900181c005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 153811978 1250 153810728 153810731
    0xe190b090a020a030303050912040f030c21080a02010e0a0303050a0b0108060303030a0e100609050115080105030a030311191806050c06070e060c01020c0109020f04021903271401 78
    0x100d0030804000c140c00e0145500074202906180c65554202c00403c0010412170550048403003003c0014000e80c000c00090118502850501d81182082d8131180c03599440110581c10301c0000b10005011010044e1601c0c1e00090701c59140c400e020030580c0503223403164800c800e60040d1780c03580e01010340540c0300764050501400c041100402c0800150791940050310416416441072001850150091308a102855001010740e071101c0f00308076220081c0c0d41c00342c0000032000d844000601c41143c4449152541441d02d14000d40f0355454800465203501c800240a410180c40740100d448140350b03801120300c0111141d2aa12541d0b06c4064000c00c3c0081c40c2490040034810010000341240c0f10703109842008040d000580aa51600042070b12a00881d1407540d030480d030b0034030140c02d002200b8805005850b0300d04001040c422038900c104560340b03c1842c0407174071691051203610050300c00c610054422600720301b40002c07165503030500000c109004a56001c1000c030b40c4504c1104202500781d513034260b217090703800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 153813228 1250 153811978 153811981
    0x1403030c250803180f0307050d0807111507060c2610060302090a1707030b09070608060a030302030d0b0103022b0e03032202061c0207031404050604030f02040e190b 72
    0x410b03900ca1103100743d000929440007420806030b1600001d2020050001400c484031950f03204086072682407012010390340e404002c6000710a01000030b9203c100142e048944106c0f071a20585400c00d14010707128046d10b1180c0e40e0140440e003500a00040a0b00900804455443c6213545520040d01c031080343c07648020aa1420b0005040d8041e009403000300c44014a403601180c00c0c01c01030380d072a4102c0d854100080c851140b000010074031001c951030041c003551003d01a15414610042c0003c040689290301412a94000300042903011058514030140e200000c03420020401c0100d019008007040d150192140c0075200e40d038108080c2c2140b02d4403c1c10030b010301990404e544000e4481c0011141d80465100404540300c50074440040907130365a100409203400c010149841100d254054501c01c9103c0c1d0380010000c00b45900030302c85210112504a0451420382010040362075801140310040c21514400c1903502150303995044801b8000310142106c8000d1a504030300f508c4200170f01010340340c107681c590 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 153814478 1250 153813228 153813239
    0x5030d11090d02060c01091202030c0c0306010b0d020c21070203011401140603091204030b040308090f0c0f030f0102070507320609010507052b08101403030c25 70
    0x3600d1808400400e41c00c40c6482c15002e00050f40c0c001020b240b04c1b5582d6240640000c1e903803245070031031146254025622402c4d00d128003803070036040e4110b0621942c440001004010740071003c45600090814000d80c032800704884080c60400320541c01580d002180510074520183d440140008034001c400034024100840e00c059000d0f0001c0c011030400c4c4850b540f02c910f50341030104c02107802c01584c0007141d11200000030802d100d034109810880b405100282800107155201030700c0340c0c100406202078180e460b224031180b559541c115000038051440d04c08103120380c1d07900780710000e4915080c00082d90740d540149010743e1201141e0080d5005004880b980e508a5104170480650303900c109080900704070182020000641c01001e680c5041103020000100016011312800e591640d5001040500c0c1c03003580071204000703c1c5001c13001304000c2240c0070848140100300300302c3c7c11218003407103201038a0b0807500484c0c254420301e080d0013068440e20282000100881c0c0d00d4030a40316031490000740007034907034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 153815728 1250 153814478 153814511
    0xc090906120b0903070b0a0501170c0901090507050d3308150606091011010f020c1203060109150c11150a110304051e0f0a0501020601171005010305030d 67
    0x80c0509040d100103403028034000307074072032502c141c0069a880c2100e040c50310329aa0841200b40c1140c0880712213480700700420090f11844080d44100310280301030b051104404021600b40c140510882d42c2c125211404100d13654051411207031500b0075400141b01410001c0600a03041c141d072001d010300011080c010390003003990704040b001a02d4003100a400141c41c01c6032010014280a0038241d40010200032510b0a5174400103a8103400200d42c0703c07a41e0141a8504c040c3c01c490b855501c041c00540104560344640c40c0204800034102c0051000b03070780384e0720f440307004861403052908036021030304412200e040c0180c4c1010040c09031a10600002038121700384418000d10212000604402e0f403002e00602d25040e004601a00084843ca8200c0303040a03502c13000114420303443c0303a170150700031458160aea105041003a1460552603040d40d0b1000701c245000c0000303607140014030498960510b40e04000304948002e000002d0b510006003010300881d40c44e0300b00181c0365070003187c0220849181911020075038013030303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 153816978 1250 153815728 153815741
    0x40503070e060303030a0c030b0a0303170114030304050105031905090615010203040e01141912021201050105150a0302040302030d0504080d081b0c0705040f0b100507121209050609010c0909 83
    0x43c0143d425511240d065401810035410304000f03145d00c90092a005072500b815010095009544254035003001ca41420400d001c10782000110144e60320243c04180c80010071074089071800e1800755942e0360350300b1003170482413074090b21010124240420300501e0880000e03080c1c02100c03100d115004840c490401a6920300c42e51241c01c00c0000d00000400140c03044200c959180c61020b440704482001004425848150130b4101d03981e40f0302d04990031025418908071500d070396801d80d00208055414000000c600d8500d82c0c44a5406600c00600030f18018071940598004560150403201d0842069401822a40150049052a101d03554516021134070483c001b40c0214100814510001c00782180c03400140c0c08014003007080e1040d8040022070b901d80d80b05802074901c105000180115002d800c0200305210280b0071000c04c1814417404000c1030508000d11008030b0b8a0401440c411250034655000c0e00714440040c00c540100810411240c1064014080030078044da10b14a200740c030b69132281c084441 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 153818228 1250 153816978 153816991
    0x403021f120b010c050a080a0912020906060901090906030c030624140a0815011715010603050402040b060a03050406050106020708030706020a11030c0102120a140a0c03060504020f040503070e 84
    0x30511905405018552180c00d82c07907010700d003080d658007050311036901d00300c641c95080342d41000006d503840c500741d8800b0381e0502500301722419002210b050340004106e4031001d8901846103200141317468090707004d044564001c0c40084002d01071700d50b5a05008100b4080c501c0b06a46141c14030b003030441d000d144e1250251419000442300084503041c21401d548078801035180640100650402086180040091034640b550519480d20f0640c1402100005610401c5900c8040c1e400a40d0300d0350509500800729044da411440c2c005400d580c1e42c00017801500303003c0c110640110f00010b2604000c4c1c1e140d04900d10481c000c0341c1c1404240d030381300402c0740e41c2c1403584220003543d04141f0080d070014a264004007000c0e400303444d2014492420b82096415540801d0340a040c9a42c00284a49100c6a09410076446000d1341010011403548040000c10100000c121a50f039565a08281c000c45009500c400e001c1d00340644215100d82fa1003100740303010b0f4001d00602c0c1c401d1180d050002001c0020219040c850030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 153819478 1250 153818228 153818237
    0x20702090403030902130f05011d04120c060204050904050a1b120b09101d0f01021303060e1507030e0105060607020f060a090e040b04060e0604110111100504080403021f 74
    0x640c0c40c1c4080700148050a070407680224140b0031b502115010f802004121100c000300003449501d8842405802200310000341e03442840d150403c800704011038500000c19400d4140121400240c1c5400d500130711458004c2075000c40c40d401030009000001070355403503003841008103412000f145101514402c1483c440c0c50702c08a03d0101510000b80c20f9032005402c4600101143c0f04940d008070500280e03016010322080f4020182d03000011024204002405060910000c601d0840c03100c500074400d00c0c860001030001da8591140c032507001820424504c0c03e181d498040e02041c101203e0040107403004c6108282c80d5030a11000c0303109841c00000702d44255500401e0101031104542c10320941c0d8111358403000601c8070303640300051039100320040144210f01c02e545542a514040c070f090400c803181940407280c02d50140041200103001e86011400d10107003420028400c51032002001d2070145c1101281d4050380c241002e00c410045844040c2007a40c1c0b08461405415611081410680c0c1c0c134200c8420014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 153820728 1250 153819478 153819481
    0x605091b0706021803060c040509070806130606020c030d030b0607030813210f0c050c090c1608070606050108101802121009051605030a15180902100302070209 70
    0x82260400146031459008100d504040c6180c940c042240c02208a90003d094400f81418036440e0900150390f119040c400326505003401d107004662000001040031041c801420040381441d61030144031b0b00d0740d14000405111341500c81e0b0000b9101e48440311072038024403500a0b600c0301c0b603000b03026a141d140c10162841c2c0c1801c0046d182158190000b034170382c60300e601c00f0381c9190011503110302c095940c4510b404c2c8858a01484608010710090000c003d010800c07034042040d400091000c05c2c6c800e88210b0840e4071062584605540424031321a5005401407003084180c0401000900c3c405041601c2c000d00d402c202c101d5546005480c040d5084941c50354425401c2c03401c1c00f5280c0b5040700d400e0204a02d0000508042e0540c00e8107070301c180240c0342c04206006441c0c2c01c00170712007540501540891845000e143c90a508039000d00a800042d00c403980a944a1020032601c1c82c4810710720b001402c452102d01550386646918600829820109a00812600080b07025881c020b008440b951a400340000195 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 153821978 1250 153820728 153820741
    0x1011030d0c050c030307020d080c030421180806010801062117040302042f0406050a0305130f030804030201110403020a050d05012901020708010902030a0201140c1209010210060509 79
    0x816141d00c41e401400020b01c690003c200007003001c0e51082d640e9800a080b00d541c21036024113480c2e401032000d000d4000c10820007000a0951a498140706541c60800320050708042059071004400600803080004040b4001640840081d85a040b11040c1d4002c10826803107a100d2180742e1901400c00c0f40d24a031098410000a030004011403800e0443c80e051400c0c140c50b580050b09417440801d000d19000c1d502c1b2440090b4403220b049441b019070030f003211141780904d04000600715010304c2800c10140b5030f4920008440001d40701c030036a0301d568031400905015606260282682c00e040d1402e600641c84d0003284807041c0c10a404507400e50f03800034807240410f850701c41000101c0c030200c0d00480c0d655403914807005044508012440c9115140a200a00044038500080c40d044031a03000c065168100404075015880220f405000f44d60286000704000080c0c0214000794031480704818440d102d480100c940d03221280001d40040c1800340d00707641c54100c03004038110650791107000300c51b0300030b1341000810030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 153823228 1250 153821978 153821981
    0x906030a06211a041109331906020705060c0a020a080f060a0b0607140309040905010b03010b0102060606160822170c1011010908040801060609051e04051b03040c03021011030d 77
    0x80c070955983c144450003804800d070b24241d007035440000e40b106031900c410394064030300000d1307008c2000400800c11228a280c250000d40da0441446900d014040015102e20500405d006103859560094204d141d82a47c0d801c0700c03580d5070290218030046010f4440070505005543c040c010500308000c1c45181003000070780741c01d581402c60121010303851004101c210701548581c00340c110318900840000881d50889000d050a54a0440311141107410220404c00c0517034865007511214440c1f070b0b41b0320791044481d1030041c06030721418103455107480c0468644000f8a09044a203421340fa8002d0b0400c0d904c0c2e40c00d1006658072a01c60b0b11003a03002c0b009440d00218248100105484c10043e00004178940f09540c652240d030303a0281d00509002e94542c40c0c144406034004038800c0003800151415043c4030110814500f04c0d52125100341e100b50303111000300e00c8103014241594907400740d41c000c140d900e0415141c080303440007151004901414200406a544c6170207070810b6180800d6400c050742c40e05082ca10300c8030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 153824478 1250 153823228 153823231
    0x5060105040c0c0b0f060307080d050409090311060f01030c0b031509040c0b07141204030804060f12020d020a03050108010507020c04180f05030a090f0302060906030a06211a041109 79
    0x904214820301c3d100007081030102140d01034941c01c001020241840424941008404d4002c1c54003a031100116000381c075031150859080700c80922001840b6049440d04031402c8507c68440e072403501c5090180710031400c01c0d40f0614104d0f880303111540401a610f802c86072003070000b01d1b2403121b4000140300c521441e0400a046039481480380c0c0c0407013206074039480740000d41d41010301c0a841c1c44020720854805203504104640841070000011801d0525654030305440e48680d01a031000c000c081c0c4215520341d402090311541e032080e44a030954445922244000094104020100c0040d0512000041d20300c410f00c24107000d08280e9010f8050000280144006000040b45030340c643c0c0720151440e8080780543c0700740341c4c002c0e2240000c0d558420903004000c100081ca90003002c6050082e520810059032000b0448140e12419694140c983d95050342d002e00509407503100c0607403034489409941080c0380c841c0504004070b2040c5889500384500aa11300480441150010080341081c0c0550700c0398030740480c24a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 153825728 1250 153824478 153824501
    0xb0a170c03011a0103050109090c17010204080a030c030e0a181109060c060912120403200f070819050706050319150501080f15040b19030804051c0506010504 69
    0x3900d400340c40c640400c2c01c441d94448101480e250140300881a0740e4540541401006c55203002c1c0303d124510380f01c0700c040508902c1901402000b00000c2c40300e0010a40640700200703030324816507a42001d5810301502e00311100700110001180d065116441e031524940c04e909079107481c03010003005848110004d000307240c1b07076180c2d00d030810040c403131a00b1594580b00101015114030000d064942422032626260a4010310030300a02a0709015084038000342c520350790381c45505031030006807001a4080a9060400b1205000340078000d655012941010001d2118201c0d004c1408036030769840c00e512601c086400440000304140c211540c1041901d1003075004c1c5d600108410520303210917405c20803900485009945551041412403001c0215603000641c55910400c5c43c0c04d000d0003403400790280240b0170313804a0150312465072001120050380b5111034082d82c00c6261403c183c01c250700d900340212207400c6485200c0c031480780991448951008081c4840826070b01c10000d04050f420b02c41044094114001007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 153826978 1250 153825728 153825733
    0xa140c0c0d08040503010605100507110d0b040c030311010e030d0f150807030605180d0305090705060f0d0b041b230d0c1205220219150201060602010b0a17 68
    0x6080389035030320011100214840e10303242c0da81c0c602d000c00b4075003034846952089225040d602990400c0d00d8216044030b10300c66005d0b504803c414100c4002510082ca0302201800000150040004101961a1032010f8a01035114a42c564004050b01800c3e40d1040101d2a03542d04103014805492481da00188150515081d02040343c24001d11100c0117030042d40d202c40001c0d80808410400e200191182c1074002c004011440740107140c040e8110b90720f214070782e1041c082580d9240010100301041c401071019103030041c5211354440c00352a07601c0ca20740007018100c0079140f03040b1000d195440c0034411050307000c84110080010600d420380c1036440002000702405091290340b00285012007940003401007540b40c500c006540c00c43c09900610a407000ca140248540c60801070101e03210405042030092007005108008100d4188042a4060615000032112a000003808141c0d00d1100c0441c1031021502d2703008110440e5110340c12800c2e2211001000c2d0010b504000610501c2c16004c2c12900d1056003208 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 153828228 1250 153826978 153826993
    0xf0d0507090203100f0614070803060307150f09080a0b04510510050d030c0203060a0b030d08010312050306041e020306040f110f07151803030e01020a140c 68
    0x2100142d90046444d00b09801400340d017840505401c00406015143c0c4e4908041218000508040c8512610001400c040c6002c4000f603070660703041124602400f42482032000c041d00c11003014054180c00503400d404140d5042d8046885000081e80e040d83c140c112958a003152255143e00d00c01c0c40d0a102440d2071040c1c0c0c03010080c3c045100e01c10080411542a01205c00602c4a0721030444881e10561018840d500341018005920a195030101c1a120202d07290032180c050f916080e0b480242800000f50940948803c00a102c001c6901000b9840c02c1a400e6400b8480d1103501190180000d001c0107005900c9410110843d6200e00b000d154007400180001556810654103540e088101e5480c080d1943c0c0c000082200d5030600c0e010388051580150703420300080140c256403c1450085603454000e504010030746000340000b500340000441c40b0a642082380d1201888141c00c10b000c0d8101c01c0d40402d0501c0d80344000c90505100300c856040075a644d80600094850010380b099000040c0041203214419 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 153829478 1250 153828228 153828239
    0x60b011103070c0312180b03070e13050f1609030303110c010911030f0307030e06030402190308120f040f030807050f040905010f050402070b07050c1903020606030f0105060f0d0507 79
    0x1826807a00a403d6900880d103140f50015107182c28110a40401c10400e103802c1c1203017028000070003a581d003401036035100c2e628003a080311440007811201d030f07105281114890080410b03a00090113542d07955000d5603e582c07005c200c0d4078104d04d030b1661840042d101c0801080400d00c40d600510441c411061050700e088417012519080d03c842ca00283c0b5415103180304101645406c110030036030403071584040c42c02c000c005e0318090110300005041030b01481001001a0031541d03044502c140c005640d01001510035120300381480e5941105c00c03030f036102888030404544144001d00c0c8083c4607aa00010b070300c00c401c901d0381e41200c0070f08010348103009000c000d000541030040e07081d0203003000d0864030400140940c075042080c0e540f0b46040c2c2c400d5009910400000c0081903140c150a6030000250070a0f581d02c00c0c0c0b4180300340c60049030103094a030310048441d4001c01c041d4007086041c0200400c0f000c40f0340036014007255034201e45003940d07004d901c031043c407400411070f04084640b445c8040c00391042c0c0300f000d690345 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 153830728 1250 153829478 153829483
    0x11040207060507020d1e0f03110c010606020d0e010509060a03090303090804080c13060602121308010c03021c0e1009031b05030403020a23040e0a050703150c080f04060b0111 76
    0x7510f5500240e042402c101c40d03800c1c0c0c4020040004803104008001c3c00e9007089015002d0018585c8100405448100c0340780e5031080d0004403a0301c0315240c0001c0103030582da1200292031706403003401e42c00020a010640040c0790711400076a028038000a004900d040107814041e00185281c107002c400b0325896044060108640c0390150005100c210050202c001c040c00402a11001401c0b0100c54285099014010181c1c001481d449010b0542c003c1c030740d40e0f0420f0590603446080f07075000010b19820041c60040003545600500707000241d180b00c141c40b0018541314042030303d407695204a8036074003100549d07403400803907044210031600a0034484480042c6107000e02e103906a0000a403030b07030380c8002001c00c114107095171340710f000b4001c64040b0036007824024008025200d001006520480e00c901c464048024248030760903859a00c20300300c60308583c1d21720741000400604500d00c2405032415070358408460061800c2407080110344111049075449a880300005d140e2007000c541000144104071907418000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 153831978 1250 153830728 153830731
    0x318081009051f020a110102031e0c0d0c020102180103020909070f17040c060f08010e1f170a020307050f06120c0f030103030210180503030711100204060e040b090112110402070605 79
    0x10202c0141c1c0e00da50342c0343d01801a101046c069186680b04008100480c0d500d196510076602c41200b0005150711810f41d0a41300307000e0200031a141a2921142040381d07070f015402483c18114010358019903400c1c00c40150100d00600d44910340002e8920002410309200b8060b8107602d05450600180c011a02c0701c40310804070701210100c2e0140c0d0b143d042484500c0e04406c0f86605400589003018066040c11660710b44038030b002e40103151401d14110a10800c00f840c13074201c0f002e404907005810300414900c01c603964a4640c440c040e8043c0c00703100350102c0c03181407142140304a00b6001e00440e280a07001c5c295108081401411000c0103041482a1380406050000550085000c1e50040260031107290f42001207800c10307480c1f800110071140d03c103000a80084181e951106c12410101800360700c0f64a400c0c14a00800500c5005038070000b00895010b40188844550b0340e026282000031a50550131310038050070a003e008542c01c1180303c40c7c40098000c0000201c030b0b00c8c000e003000d410083d00750740d2002a10780 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 153833228 1250 153831978 153832033
    0xc010c02061209120f0c0c220902061207080403080601110705060f070501050c070311060709051909110c1b150c0c0a0e0a051014010e0109150203030103031808100905 73
    0x2c0002e000d115100104000e1018075012109400301c800d0b4520390090703440e090780d02d06910720b03114080307103082d5543d10007503d43312186610310700c0c0545040c01c401029114100c1d401c4002c603a1140105509510462810520b0f09228004210f00c0b41802c0c00c200c0c443c0c20200c0c442c251414200003110005400780a0240110b1b14171610790b498654030b10700942250400580c3c121190f0041d0304000141b42d100181c2405c8070b90a65407007442480b0352103006171088194000d0030690b828003c94114010f00200100603030f202400948800c925a124480c103040340b081100750740031a02c510003851300148280202044100340302292111408100807032940e007081d030b00018240040c0020410302610300c1c0241a8068110420425801c0c104031040094840710400c541c100105003009440c0c0742d01500711a80074002c41c4244802d04c40c1040e1000356254405d01040340041c5a02c1c0080200803521000523050301c200c035018104508a16501000500c1ca90740207650b2440380c101d4011a003441140d001d4810345 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 153834478 1250 153833228 153833257
    0x507050307090203091c0801030204050a0e060c090f0f0f0603070c060e0616030504031409030304030b0906040224030115030b120d020106080a110d11130b030c010c0206120912 77
    0x603041212604207410340e1a41841b00c01204000e049055000741d10505580e0304841c0000c264860301c031890014041007000c04824800e9070140003042c3e0005010b46000c0604035852020f4501e11801e02028090100d034181e004402080406a41d10f0040041c580c096802e25042415000a8031160251400010001984d40019092150071050450708111503c07490809020a081641d001003500040c940c400441c1c250120700e14038955002e00894008540214952142c3c0c24401c90f080d403100c400792003c0740320f103e003404880300500354a5420604402003816a6007540e00c2d12011410440f03002900408041d56200300c0c003095500d100003a0b4001e03007004000c01c0110b0340341d135000c2d00b101c1d01500440101d91007089200009003018603094000d84040d21840219080f0b89006200f0345d42013074820394031690b1100f58100019503640702e0301207408214100d480e10b4000d00015607840100341c0b03000c2e40048003000020f84805996089503042160f034011140480e024141124058001940900c040c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 153835728 1250 153834478 153834481
    0x20d031b0b01050117010602030a0c24050a180f060b040b0a080f010e07140f0402120c070506060a1419030b070504030c0b0301060f080705071506092301060c0507050307090203 77
    0x15603000f171719032460001c09600f00c08030394101800030b5640e0290046040130006102945c1c420401c0b22202100e041e0498a001011681074156100181400300c803948201850282c1280a001c1c18071340d1031884030313000100a0460f40c8140c4034100540a00c0c50101d030481c4d1504007004003512881901c000405c5001d014100500039140031600f51a0702007400035050f840300b00284902c84060b0205440a4012540804100e40d0307800810080e02580288800441030101042028103424009240b00340c858001c1c1c501ca50b44010801010b5000c5001c0c8070301c1151500c5c4c10400c103040441d211040480ca100310640400d9507603540300c411801c200c0f1030030009280031404008000c2c00301c4e1101c0180102100c01400c540c10700c00d0040120782242d1041040001c44408200f03e40d0250007143c820ba504a2032019035000c0d100d0200c2c0c0500028862962081c1c5480040609060005142d1b00702125083e94403001d6440e00c0c900702c41b990401c0100361402c2c01100000101990100100c00c01401c0c0360741d02603200d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 153836978 1250 153835728 153835739
    0x304050606030105220201120203091606021f23011401020706020c150703051606021b0316080a0509040f0b0a060203040e1909020613050f04090c03020d031b0b01 71
    0x2000c10107000d8034040d0781800d082c480f0074036640b40502044060b40322807a04403000c42c001220102c2c4032400d0292101d2000083c802c406402098a0420f007400c00c40e40c00c401540d90354121380c1d420f81901c88228400c0880040381901c0107607041a01258090010b1540140302d501d41c890ba2200e082e400001c95541c212013490142d40c041c031141005142c18000b415250080c24007040040031070541100405000051800c20140200299640030092074100b901102c01464140025031080304004090b40d5044000c4030b0300d03034001088481d0070b00921540302c40841580c0e5030b180b05802070310101c1c0c02e004041c041d0422948582c41860f10810007040c011400403021414080390790147e401940c21500100f00a20001c0c690080c00c0d90441e070701040280c0070b000380410143c010618288025440080040c5155100c5040c000c0c0702c4c20b64408403005d152901503036007003208442616400600c0342e81c00c1c2a0800c058070706880c1d00d43c001e0f17019040003403c00181503a5003518071b03030104080714110703840d4005205 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 153838228 1250 153836978 153836983
    0x3060a0815071d010207031104091403030601021506010203090409080c0d1d03030724060b04060503150108090c040e032110060e010504090c090f080f101103010315020f070602030405 80
    0x90030b02e9249810f0b01c400342100003501e40d945804042c0460700c072501c03508241d84481c1c0c4680c0e0b0061f00710410b40b804030200405540c90754000d81c0d10500500c2035100c0c0700c04502d8101070690003180141c004600e840e40480a00004d01048401a1441c00d014040c04100300da0601c22201d0344162a91000c600343c18290301d481702c20300181c1f41103019a00c181700400028840e4076441603840c0c4d0201e402c180c15181ea07040440a804581c004154840c0080b078000354203500030000d14010306507108204184d41d0200c004413000310701101c3d81030290380b102414400c507003032a83c82049240c1111041d00c1c0340400300c40d54420f041c00c0300c045000d00301c8994020442444825a00d81700542041d1816154081c10303440000e0042c080c034000d981c180c83e1b5031103801910318015242036000740190b0142e031a929903914140b0352501d050f10301030404d60040c01140c0f8024080ca1184519102e80031000604503425a2100c6280b47c152080005110340d0810802043e1005034001c1d000035841540302503540d08d442d00d055070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 153839478 1250 153838228 153838247
    0x3090102071b0e060105070c0320010e03210a0513030317070807090b0309010f1406041104050d03030b0604030503070b150d020d02010e040f0f05040b01060c12030203060a081507 78
    0x440d040b0a004040c000742c03801040803900b20000f4a000381e2604d900d824030f048091043d5000918454020341a854184030004101e0300c496000d0702e9a080ea089020117040d15204500301000b0f40086250411f0441031600d0b0203410300e08028900303107050140c00100d80c44011210341058000c44c84030500c61482c031142c00445136200616182950780c0c1d0508500140000c98180501200241c000c800180d462500354070160100b2180c8409010010b5050350070500640c00b541c2c00c502460511341e4031113100210b0012030702250720150241d69000c65645044005101000b5481c0d800342c020000000450310030400340190070301610301041c003400d080030030b4005084004800c0d4041da90850051016a0380c2c03800340c04820350282043c42801c0000c8001400804100c0400d03040340745032841d0002c0b0784c0c0c120b521151045100e040800010390301c4100c15520f2100d40c1c0300007803010f007188224407081c80c820340203507401a00140c900c810321500c42008a04003480c0c1581c00c09a4007607142081007240c0e2115802 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 153840728 1250 153839478 153839513
    0x50411091903210206070c030507020904060f0e01021218010b03250f05060a0e0303040b040e100909080a0e300601060e0d24110403060c080f071101110309010207 71
    0x100080d610f4604081d4503448000d082c007040c050605000b00074540a50112000b241d03006200c02c1840c90103143c80030052281101144440e440c01140c140810740510031181203050b0258052001e58800501485080d8003915801945d500c0702103504064604000e4580c03112030420009010307003070000c10420413590680c00701020900c0080200081c0c1c465030120382680440e0316105154544042c02b207455446540d00c110a2141d0000340014030080078100240105c0407a2030450200c3d54075008001500c400aa0150500b002004001c074101d020300c00001c14068003409080d048a20040c001021840304000c00520301307910f08140451000500c9a81c1c05824030342002c0799844100da0124000381c0d001103008004100e100c01c0500c5101315488420170251009005004400c814129543d4a4105100c21038846050910801d00c076805010440c0c801c6051119a14040d40d40a01c01c403044280103420745019540e5540d080f45050001c00111b04ca03014136400076070350707803010b1414040101880c50701 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 153841978 1250 153840728 153840773
    0x150507081303030518070f08010e030a0801150c06020a08060301150e010b090a051003090516050303190e03010504052805060c0a020709060909030806030f07050411091903 75
    0x4104801c8400400341c800540c00d480d0000b1255a0600d1212441200390f009869502c41c1e860002222030203004c009050301d46050003400503403140050295240540310720280411001c1c401030080003821104611141c006103400c55503021591542e404a0f4001e003074038000114480100402810240122140e00d00c203110340c100000d1406005413042403041c002d407405480005000d01032076807a0f03062040540700080049000f640c1c3c401000c0c0c018082064100ca00f40140c0350b47c0c410704003015200f08102d48000c0c000c0c624100141181a0301c3c1103000c16800d081c0b0202904410302034409115581c0f06da48181c00402050002e01403d070700301991241c25010590b144002000020404074000d81c1102c400700c010b50716003032522426810000c071504022007440c40c00e03800260035040b58201c210f5490290710360048540ba480103054a554410701103050aa0210784100118189940860b440d21091542c85040c80840000140c95402264030820f01d03100b100c0d000c0c03052010704c0f44109502d8404022 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 153843228 1250 153841978 153841981
    0x8060603060c030702120c10050912090603060a030f050705040501090c090e07020309030a03020d120207020f0f04020904060e01030b0c0903060712201c0509070b07150915050708 78
    0x1d584040c014640810100084080350341c06008003e100100c5007440c4109480e442c03e445c030075a42e8500340701500019400c0c44081482c030070700415a56105090304c03608030715140c9600d06025050384040e102607002181004000085440b4202e1509403030700c5180074281040c54081080306590701a041540b24a103007242c00540150000c5041088035241c2480e0301080e0303030389030b01641140180821103030175000d41144c0c041015408105c184400041d51203404007141014050412805a00700c000d40200403040e6800661510080d0302c0205100180b0140c6010003e10200d410744106900c4154038100d110014000c00103480c40d590340c4041308a0502e42048802c2002035520103018140c8401d00075080500c098120701034200d0319000e004180719065198822080d4400d507844415056400889900ca5800c1c0c06481d00800f8019101c1c540148080c90800b0042d01c501d5002c40c40488a86000c842c420218000c90700604003140d00030b18031260000c43c00900d03641600c3d0000c001e40f04005c01d240 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 153844478 1250 153843228 153843241
    0xc1003060f090b060c060705070605090a0f111210091505090304170f010504030e03060a0e100c0c0c0806040c0e04121d2e03050c040510050f030a150806 67
    0x100e00c004580d0160000f00b01c00d030707586000c00c00d1485020340c0b6039014094942000221354000008208107031090004001955844065036241c8000081c0102625948405280880c80c810002c2d007107508001d201e83c24202101d0f10452038400781e400340401f071580b5206035a003030100c181620700c103000040000707100c00d141c5449002e80702c2c0310343c0c0560420560550024029800200601d290b00760103071008000905080c1000340c514403640003402d10921504000500d00191802810307441480c80b4000d03c3d40c501103419190241042e62442e40c100f08144c2c1c1c0c88000300f0100783c260001020114081c0c40c0d9401d01c0e0800d540006919049061112a444240400662000c3c211525900d1501e00492501100d0301d0920080403c030120681c0215540403c07280c03d0f20700902d041e4070800c49954020106650207068007a28421981c0c41075240f0240310400460400b044140b4840c2c45a20707000c0c0c9850b014040d03400241c2c205880444826958540081078610640c00c910042c1c610321000309014507180d07 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 153845728 1250 153844478 153844499
    0x30a0503091203040b0403051c0302090d110d02060d05100b0f070813050607030809010f0c0e0607020612010b0403050c180703150504020a0c020310090203030a05030408090405090c100306 82
    0x7030707501d9014441400e8080b4039203005006a501500e81c21610a5070ba907900c3c10100da44040d410110154001d61480d80b1034117a02a02c21a812240060090032640095888244240300803814464110813002c40007001170795040d000304561007581c40c0001d400c1c1416119214604504d8000c0d54100d5810050314240c90005e0058603016a8041c03803035607460b2890f2181106002c00703503102c5034006901103940820103422241403403060b03420500810040300c1590290094030090100c0307001180c0284425851030404800070b20300c01d030001e40090f29007001c08044a40183c400d9010301e800e0000401d0034000c0102c2400f000504501c11a46900c034030302d40c0d03c2d0744240140050800c0060554542c180c080f000088035905004000040086441c0c82c03072200050004004a0b000302c4c0329004140c0441404401441401c0c3c2403500503008509013000306100f84c42c10f0340094401d840c801424004c80c0c02503629401401d210b0f00c44000036058550851040c02074090603107425406050070540e0500c650040ca = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 153846978 1250 153845728 153845737
    0x51801111b0f060d0b030c060412060b04090b04030801080f070f0b0310094502060a05090d03120e070605030c130b1206030607090e040204020c0115081b030a0503 71
    0x44450300442404050300280c822a800c400140d000301000c030702030134290a56840402c81c030b6020703815a00018409001c00c20644901c0c0901c40b043c40c084000200400d1345a885400d051401510006100300e144d1142740c072100d021202103000034405001130112071014030561018546c003030020460503007040c40400803a81140140c00e9140340100000d400c464020803c0b0740200000001045034054025941082c40340d005110f01078810458105c00c490f0100035400b4907401c000c00400090b05007958200f00a40d40700e280150304200050000c0f100c60f40d1000c844034510f601c240c440c0d42c1400c10f00141001074455040c43c8500c203400004080103800d80080840380d010801c20705455580c0743d08001c8a031072a10a400204035120081104070a040901c1e032818010311088007210780c00d60303d403e411214180e0324001c0140260145010400505003030f000342103010030210012480300c1c12206800004a0b49602c4912a1342c03056050707d810541c14082541c40031010b40140131301d000c142d21016a02e105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 153848228 1250 153846978 153847003
    0x711010305060120031305060403020904030c0c030516031208090c150f0f0d0b0306010f050d060204030206190801050a0f15020102090901080d03051e04121b0305180111 74
    0x8840d070014519070311076503802160307035014100c280c010584000407a550b500001e450300424020340c1d03030200b0540303800c2c0b082c4c0f01100d9000f03218044981d0b80e0781e000c9441c02640c41040381d58110501d00030002800c00d01040c50154803050322000820720714185540500c085206410078170140d40d00707202c3c003034001086224a011003a135480c041e611900580e400f05220700401100d4080012400c002403070a200c00811400007012411b10648900750704154852030288a01e9039149074010081110b4205100343c0d84441d8044c400c010705060340c90700840c4203030b0300c94000700ca02c5c03400341c0c54090344040e040156240907050035a49103c000e4180b60400d0ac0701030701409071741018042039166079140c0381300750120368603680054491100707560f40700c0295548500701c484920100e414400002c00220304a680c09241e41401c00c0362030441d80315619000d685081c0010301c6070401c48890118441d40d0341b0001c05950451080e40d600e55510141c0c950100c40c00e40c5000e200341004444000800d00c44800542c0041240b07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 153849478 1250 153848228 153848231
    0x1506060309023001021204120816030c020a02040204080105061503070c1b050406030b1e1003021306050306010b130b0f070803130b0112030f0306061b030e12160b07110103 75
    0x1005003c04610110000460169600004441520802030b52105010780d2056907032950390510400c05813400c0e2421240307a151700e0500805a0140c611030b4020714039080c028016920b5002aa4010909984c003603080980d59a440303400748007050800d511000c401c0f4804102281c2141822880207100b00540b90303002e800c111a1154400c0840c0200b8804c1d001040c0043c403c1040b02d550786020038000d2000c454000d1040c40c12080384514a1300364a03498419482c0f098498030603800c503801c02c2898501c1811841c00103035103110106150b2410402640a41103405c2126100d592540050030b0100c1d0382e8001d410804020300620360500e458600fa10811680441c41c00c0d141c0d070b15450900380c5070240140c0607084d00c078003c000043c280e101a428501c1c5c14041d03500c8091070320748507900707a0548140d07124860000300b4000034048420030644015460ba48280381801e000c0403010f002495114031200b00e0545508069080d29603000c4d03080c42038008041c00c1c0d14550818110784c480341900101100100d0525 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 153850728 1250 153849478 153849529
    0x906080d110c042013060f0f0c03050705010e060f15030a0209010603110f0315011d0a150e031b0a05091003120c060515040b0f0a230d150606030902 65
    0x15100340c4c0c54001c0d524100400c003922074003030099055122400740705606c082000001c100d11841d00c20f21030624104403c0d103403c000113240f076a08454540c841d20044c0c0710f95581c0d850100c102c1d0000e01090b07009600340c000c0d01c14603007407442e81d64500440f880e18052090340205d0000d0016250724404604540c80d5007000262105172107034040c0d0074450040c4105024000004006441d0020642c55150380400c0e40c84a0307000410841f1140e4024065500c5980000028006c012070700d200c010450039007110746080b84100b01450003092504170601a6851702e41c0300b90790780612a0604008040040c04100c1d1000c0780380c10f0801c100c01207640d4600010700540703007520403c85c07050300174a0b4440345a941b10000308450300d40075444c1d58224421413640c1b48200d0a041e01008903281400c1140c405510050140030030394501400c1c10b40b03c110100110210f60401c0354030000c0d582d030785201107142c0c0b40039600f0990b00d0328080010004a4002d40c011005151608c0b01c0300c1c000d40c46250542c1c1e040d40daa45040700300c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 153851978 1250 153850728 153850751
    0x5060705070b03100f030c0306060509040f0609080c0a0f1202010c09060f17010612060503060c0a0e0f180103050c0901031a10030606080d0e06032208040f0906080d110c04 75
    0xe1a03a5400640803003500a0002003080321940d500012a270280342c0801c10540c44808102e4010300607a40031b0081499841c0410114074554848006580304e0200c1038503000e07003101c4090410401c81e20580c0e041201442030801d06c502036610380030b140310340e00c020000c01e1460200035000300c14a001d6402005400300700050490b0141101649454085d90440025a074810300100400884012802c0f09810b0040000781402c4c001546c50103105a40001424103c0c003240032a42588050052580b004103801080f0003038940100010041035001020780c465811420114a40982d041145005003005401013010501ea801d9100d80300801c40403592550315980000c1e00074101d03540000c5d01176807400400142c80140040d10a00780c290710f84401c0095843c0004100b0180001c641c2c00801c06881c0d0b0112104a188100c0303248518498100d07141800c3d121180100415115002080e5840d9a0b62007485484810010300c1c0c5044090b15064941c005100d880644680080750b1142c020f580340c210140743c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 153853228 1250 153851978 153852001
    0x2040e0711150a050106030b0f1e061902030a080f0903030c0d0f1e060e011802030702030c0318040e030a0906180815060103061a03150d0f0308010f05060705070b03 72
    0x80b5800d5220140440d0424420540040034207115400102c0c6ca0181d22640a003000d43c40b424107018024500501e20785054020304d04000b40401c0705900200400684c1c48402c1801180401540b00340d00441c0c440d81c020001808888014218010304c00c0e0340004c2207850302000085a612404d461801074842d034004000002909003a401003100600704285440f00362840d922101d45c1c03c0b0780030024069240c0d0b410510034040380c00c0c040e80c500401840340041301000c10342c00454203c2c400344112440c00407480601425a082801500c2d1400d034000324640442c0703020b028100c55507020074040e600d41641c0000150034920305100f01c3c010701140241112a011629100c04024030404080d0307a03144507607007650b04500c94202e03006c2d0f000c01d1500e603011400c3e114001c2c0d40c8419000142603030789517031122000a5501e00c00314007500c1e40304100c1c21412002545426601c40964030a44800740c0742d5040210008002ca05600094054038041c0301e090003003040016040101caa400800c03598944070148a0407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 153854478 1250 153853228 153853243
    0x140c0c0a1205091008040302120f0301050d03090506040308030103050c152703030d05010e0708010305070b45100507060b060d020f12070c030c020105090d051218030102040e0711 78
    0xc2d402984c0c00990300c5003e4000044502c03852180c0c1c00c0d03401400710480955490b004141400c00c521000340014009070404051011044d4060304080d01c000360785c1c1d000140f6960094200f101c401d80040b004104201c0b04003c22450003100715124405c009021044241ca0b0007445803a1913454280351030020f412401c07094801710b003080503051340d40d610701c00795125000c2c0c1001e11030030300c2c00b69803040000c0706c280c82a91420f0580303034803801420031140350030120950798003c9045000e000440c00c107843c03c0742002d4000303010400703160b840c0c140d4840a6a86424441c0070a0031409000e20240d00000504a81c00800c988503039a01420000700940004081005c502071481a0305201c3e100040c0b04111000c4c8034080c1c03680c0a841c0c41c0c100d05650321000e085900040c5000b000b40842c2c81c442000d0015801071005c1e098859001d001990111030300d80700c103450204400740c2094040800241c4c504200d29400360020b41120a400a510301031402d075008071100b40090407002044265030384a00224414446030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 153855728 1250 153854478 153854497
    0x3050112060914070816090b03030a0c03270303030c170a200f040e091203160c1a07030f020f03011517090114060415180e0102040306140c0c0a1205 65
    0x21200b131a1140d1259076520819002c804140400d80000102d04101d4000c4101d030340000f60242d03092040c4e410041d030340340080f01070032400e01c85501700c1199100030346c2c40c8450030a40704011070803256155080c05821200180740301403c00200001041e0200709070110707140c200d0091900001d412061107a00c2202100c41e81840304030b2100000e4408200078030788013030020341d200604c040c02d0715240c1104095540702050056401d810f4103000286148a00c52a020010086401d00e0300c01d18407035544000032002410f801010300d103950014492004e6062081c107080800d0740d242145040403030103c21311280014880e42001070210b403106012203204840040385407200900150072401c240c1d240ca800303081c410703070b221016074030f000009540c514150185041d8a100b4040b9000b0290410842030f196044040303c0c1c258a545809421400340300920040000314060f001c002001d8142280c601201400a8040300c0c0d911070610074015954000f0911000c2c90342d0149808000d80320111050f180b80c010b80002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 153856978 1250 153855728 153855733
    0x70e01030606090506030d020c01080a060b070302071e0302010903060506010c0807060903080a1112060f1512071e0503130b0403031e0c02071806080706020d030c03050112060914 78
    0x10007009402110a903030000000344020398400003407541c4d494400b8403d600591011035000201d500454078150441e411810120b580c0d03441d0f42034001681e020707101c22001640095010403410701140041c0707602090921031940820328540009040310020700000d000c00ba52100400c482d680074020360120681d010943d6500d821090a03c4030041138419016004202008009048141c00d44501e8200407000c000c8942040c580d442a484a030500501040c1c0008012086040741e56800302e000100e0388070007591a5807601c6400182404d2040a440300342409040e0803650248005a8042165582c0d60324010f0740303030380d01c40052000880002c900500080d004006000515071305401c0f0b101c6404a40e003a0050406200c0f080800303c03000ca100050058100700818440e94005005900306c8090314030001c10b089072220400c9040c21490390080f40541d100c03030007030410340b905405183c010000500b001c22642d8500802d0707030001c90385070000904140d0780701c203004100a80d5820503142602e02404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 153858228 1250 153856978 153856981
    0x71401110309090c07140105010522140a0b04110a0504030b0a020d09030e031b0a050f130c1707090305060109020702060c0105071805030102090604090e101802120303090d0e0102070e 80
    0x25540269400001d06a40308002c40d0318400c1b0f910014080c0b54126040501f0809503208101011a091810039500b0b090f0283c035140d105241904041e036041c00352070451800540e2042200c204003c5070900c548107041c08d80d06002c5a0140e58200d010780e0200c90b0403400b4600d069817035051040081c45840880c5099607e440340034420305900c0011000f415409a080b201000c00d028556403002030145074943c1d101a05080600c01030510b03d401d04000c040207404105004840c0b001e580607510490951400201c4609819030784000b418116034101c6c205003440208a41183c40d0b0f141c0300d520501601d16095000101c06e0115100e03402114008100c2e00000c005e40d0504070001480307201710340f50700c0f1803a65071864042070626040c421260255002082640b44c41d1900b2184030140400c88078600b03550044600e080809109405820f0703030b21030408100b00000b4803500c104410070412039281d03041644148200b0a15410004070000c1000c564246402c44529040040b854141d035a00010a4201da403070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 153859478 1250 153858228 153858241
    0x71b0b090109060509010509071a070b090303060307060c0b130c090e071e06020a11040b0607060b040f020405030a03110102041d1b07020307031103070312020d08010807140111030909 80
    0x1804030b40c540e44034100c10301c82a140c584c011401c2c0c4000381e9804945400681e0104500300d42c00200300c0c1080100b115160600e06543c82c0d10345100b9003200c020255400c00030411450b0714040c80444050003060030703c45202101a10f80c100d85410040110460394030048016003400703036111100004144142081c004a01c0e84d80069440d0b503000d2080001114100164140306240040b0315415101258010103500026882d004a450072102016070850355950080c44142c807407000074203c0a0041c000880d68103014424002100c40d0062484d0f00240b0600c020302c81580e000c62000c1c541c0c0c0d0549010600c0ca0a075841c276a0080c85241e00614821440c00007410002c03090b1003e4a204003000c0c56054003141c206c000c0300003d441000b40080d419080a1420f000180180742c818000200c09802c60710380303545941e1158592452100000050791103800c0c8081c4c0c1c1c0e9030281300a4054001c00d0301030301100f8a4030400c2400b020004c80d03950b06000c1d40e14180c1020310b1003081031300c1c211440100f91914a081c9070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 153860728 1250 153859478 153859481
    0x603060216060e060903070803060f0a0f1514040e060415060c020a0902070305030606031308030408180a03031b0204021e0702130507020316080d050f011508010b03071b0b0901 77
    0x100c1e0448003603081c8601d020200b07001141c03e6201d034000e00003461800300e890750350140b00d0b8030003001584d0100400c1c500882545680c1703900400703094501c0c404480141401428600305030403695207402c1100500150008400744030907141250140310303252210781c0300d400c0002e01405244c22580708100490100050302e070750081241c4041402696044082c03034403500e501c4160710515030007402088040010030000e0420368001c5078025400a130410ba0b04980d6034461007240e10594003a10400c40120303191404e94004284410383c80380858500c4942c616558010380464611a00302242803586d410440c00c2d5112070b0111000382c2c0c05801002c040d44076002c510070994210300e10682c0207060690800c000c3d41020311481c2d00400e41e540095041030300218624046020204085034507440c240031380c1004400307501945000344030201700052a50b0401004102d603898001606040100038401000003010400450b034000e4550b2410b0110800150000106500d5000e0020000007d4804002480030103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 153861978 1250 153860728 153860767
    0x510090506190209210304090504030906030b19090f0603020a0f1a031509072105010515071502030603030c07080a0b1305190510060308090a0b1c050402010306030602 73
    0x14841021a02c10014120040740582c10402d6080030040c10314030f24076000c0c00e1281781340c042030108481c60030703403940009001c3d030350161001c81c0070900d80c500034000690903002c0d2075003000040d9044240350603103205080c00c02105200c1c1d60320441e0f80e20918407010ba420f0700003030040e41e006001c0d0b06885a5800100100721000d10540381e4401e600c0b440a2110481c0808607801f81080c3c0040502d4440380c0f00030000c0598000d0091014462045003154202c1c039100c5d2402d05c0c00440e01e000141643c5014188140d501d0340302000307220340c0c204010a10000741e1501c0d40c0c035250300700d01d040182c903582d42c4008245984220380c2d40c4481c6100305c40307001405940020700148024420a42c1e11410b4403401c0084112110b1600028070b01d400c11040c040c400e03100d039290f0504031809107003103a80d00301c0c1903000101240d0481c0c20a464116000034141014140080403d001b0145100b20500e00441a1203060407800142c042000594850700443e06581c800c1d000403019542220b421941c600da001c2200c0d401c03182 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 153863228 1250 153861978 153861991
    0x1a0405031b1f020a020a080c01080a150b03130209090601030c0801110a05161202150f0603061803090301020325020a050c04090f0812010314060606070204090510090506 74
    0x41e440081c111815101014115084003504201c0380840d902020b001408a061201d0110310a120440d40580e807003052400c000e2145201411400da010b800042c8003100c014074440c100c0d400c104280410b40340f00c2c010039088030b40b5014115142e84440c00c00001d448400b0001941c030414440900032400c0d4041040d40c122449503903107148582d5030300300e82803e8400b50405c03501c01c4071060002100c200d000300d0040080b44100000c03080e150260365544aa03070200d00300d44800503440250102c0616466410160700607985c1000d40f0403d103400c0c1c001139504e1500401003103d8402d0000690544801082600c800340c0c00200259280e00d81910103140f140c01003a61021215a8103030860171180c0042050100160004c3c041d0500210038014080070b0103c005003111000503a00c00c07c0c0104000d0000780c80303401601c07480103d203035255007000200c00c1082000340c03a440c0c20250902c202a991341c1c0403640010340c15200401c4100c0d590504c10f0501c4030300001c00c400c40d82406100c42c104140440c12030310510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 153864478 1250 153863228 153863233
    0x1103090604080f071d010b0f0d060e070e0103090f0314041d160503040c090203220f020307061701032910030b090c010801031e0f060603020306010e040807060b0a1a040503 75
    0x17030b0390b00c4820030b0740c14010210a02e90a54040103002450101c0010440c030500507070400c1c03401c500003c1c12411540030b544200d2040c10140c06025032190b20283c0d007100c1d4282468244015050754803513401c2888089002401d0044580101d4006003116040d540105404075603c1c0c900e900c0100450482c0f541120b4909890322164181d80203540183d040e40d01403508180203002d05810580c62000951000c0c1801c0300310004010351f00f00f48070780d5000b144642445070510300a1101c651061500e40402d0340c10100c10310058a12020304081e0b40b0030702078112500090010304414007900390038052800007590036210003440c401c00c003002000141000840f842075101d542c540e56034050854a07003545a806600069030100100040340c0c6580f4800c440d00e2070800070380d101855554405004001c07a07002112200c0d00c0d4034042040d0301c0c0c1402540d0040c90003412038222031510355a50100d5104080740100b61650321a820381541d100d0341c1c150009440b60811421070424500040342031500300788662803192 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 153865728 1250 153864478 153864493
    0x3010e0702120301030317191e0e03091503130f0f020909010509030f18091f09050705071401110d060e01120809060a0324170c010e011103090604080f 66
    0x2d02001141d04994240d0349021215800c6006200c8550340a00b407192064049080704035030030101c1c4550048110034118105004081071010b00568514180b441a00c0d00144000000c5441e0340b03c20309a2003619100280ea43e640c2c079119031085844441d00a440004e14680440400c05031100c004046e5008031000f0f881e941c1e640510070b00740e030400c0320000e070150814047e0882e80f07078071200506864141001960703180401300f404500b002004440b10240c0701c4910010040007080c410340075002c0e08400100303020502e04907002400c5489005030052a20042200301d1000480a6001038001c0a000d0380a46c0c3ea00e40c408400c00103440b10b800b8824100449000000d0080458406d01150700e90150b031080c200303443c0b181000307030b20341046000c00103140e01c2d1110046a070030aa880d041028081101180060342488440700455103441030022165004e0200c4030b005a1300000a1898a482480c0c44045207049401003401c2d030041981342e0703810220105002c100203101007401c84032049013208841d02c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 153866978 1250 153865728 153865753
    0x6151807093b011a0c030408060f0115080108030f030a0f090302060702010c03050402030601050402030709091e0605010c0b0a0c090305010504080705010b0a1211010c020310060f090e0601050402090102010e0303010e0702 96
    0xb0302c8400c1c45000c0c44225032a21140401d41d10f00081d084801d16081900c0c285551091050305204085032241910030b90f0a005000d0454146101e060400300c500c1c00600540c106204903aa038410520810302d41c0c800400000d1102aa6400c14400c6d144c078a84240640061490003070745d200825940309001d0750030301d0354401606100c0e12450344640d40040c0144102d074a80405d0100a5201801c5c000800c04000008a80e060540c091405d400c0070b0107452034031607811007020608032005500180c4c108110042240c0104010008498004020980002c0d025078440000c0d24416042d0744014415400d1001300414032101c940a42581d074050070007071009020f04c07030401c102c4c4030309030040300580189400d0441c042296001c6400f0301c0c11060500010380700e65500040e140011119030b1012842d1a070304188a0002c00b0b03500400244080941030181c400070011054985d04140111400f481d400b00e1040400e80c403d400c00f4103000d10b0f00059a6984d41c40303556007200d09030100c0761100988201c0991024 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 153868228 1250 153866978 153867089
    0x3040909150e280201080105041802031203100902030115200a0804150504150f0c0b090604030f03020c1e0102070803100e0601021c030e0703140d020615180709 70
    0x5403d43d0594400b43d807030b801c0a023080010700360702d10081240e03025002c2500060720204200301c0b83c5030f44400700c1c640300d25012464640c00701c2135801601e250703401070004001210100c1801013060380705060118420307204000702e100c0070040c0e202c001d8441c807a50b14841c01307000c2c0110090054030081c440d98013541c04014420b07034041c4100d2040e004608070340c50341080000d10807032501c4081540c40c50300b024803903242e03213504038096400c0e150308402ea04610140004c00d500305000e84030f000400d00381907007416440c003640b5881d45c0100d0002c10340022502c05208a00c0405c0d41141c0c100b5602c04020390326801c00040a90020303042d40240b803036034041c0c007011a40d1503000086440040103101c2e034134880ca43c4061422000f03071960b681190102d21030400b02000140e640704901c808041c100c0001c0c0551807038984024035294001d408030070149a505000e20141d10744030350f00a550825500016410b0712894011204008160300c0500e002e6181400e0001c000800103000d4800700031900c081c14214004000c015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 153869478 1250 153868228 153868303
    0x9060906131a0f0a03021c1a012409180e031603020c031506060405210f1b0108090303150a0b04090501180e100f020c0a0c0503120c03040909150e 64
    0xd40c0f01c4400c447c04810500a080d04515507445543c00120b08041e26058109403142030300000110a007480c407881d00f401c080d075030700c1e06408000c0c0b41c082c5882d8604080100b0150040300400300c800c1d02d9252400c1d002c00c0c10002c4900040500300045c82e01c0249080094891641c1a0104e2003406500c50b00041d8407600490030707000b0000200f130107181a207040100401d41440e08038a60108081044010110109200e444554122003004d07044103d1200c5860301c8011400322024140011403090200c07005002090342c2e84114806051100d81e14298002900300f001c03a804008000400074002c136041c656074003c00d048440540210440094622422080c0d0b01148100501984820703000994500503403c00c0700030003459100189004d041c01c0c41d1500305020410b0550f08108a14020400c03820b0820241001c42d10389500343d0300b03085441c0c0c117040d102c5c0305501c905400c1036101d030b599000b40030589200da040710303801c24800c00000c0320107800340d42c8580040d4003405503000703942050b940c0f0100c502c00d80e6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 153870728 1250 153869478 153869483
    0x4090b1518090705012a06240e040b1302120706030c080606220902040806090705030d051207091502100b01050a02071a070807050a0b06040b09060906131a0f0a03 71
    0x140801e03401c08004446c1c196803c0d1300201c55546000c006003c0881c0b01a2624409001c5e11004c0381c01400c046000744c1099100301841008281c1c1041000141c00003810240c1207607104a59060701d856a41c0144075040102c0030103540030903410082c3d840004002014012900c0f281c401b84182c20380c024007a2440c2e0400c83c1c4064010101300090b8003400c07410b00d821300e40442016450040540c07920308a2040740c0103500000642c0c0c2c40981403041080080054800500d0110b00508030b1003e039400003030003800b850a0203060780100e1004149402c0c040e06d2058094020030109a90500741c1c2d0304020741c2c4800890202070702a16042c510703403d652150b811600248901d070020415103241c000f2261481410703a096000c203003828400d41c00041c42c3c940c000c2c01e00034024002032900e84480c0c00d100d40c01503406408140308070314000d003482c03003611040c664503403100c4100c0b0002400e91702d603808243c2070300711a184103103598541001000ba110301ca04840d4036945051750003505240700c3d07000340f0100c0141404003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 153871978 1250 153870728 153870733
    0x20a11060916060c17040602010204050910030309030f03030b0910060e090403200705120a020306070516020402210f01170105012303120307091701020a08070e04090b151809 76
    0x3c0c00000c0c002c1918001c3c051103004031400605103103500703600725001604100c0050b500000c0c10001c61819919160300301950a03400f6004919603980075020340e10500c001010712094040c2d4070113050003a401a07130b4500c80601080c2841c42e207981c036000e03015681e00910002c204030045c2d480d154203004c0d890600c1a40e040d1035005444050500381e00741e240011098071054800d04c840883d15840700e034080201c080389800200150038491040600388030008046408010040c030029074148074103082c1c40c0182e0b405980050340c0d01004c1030819210450003c1401800c00303c841030100c98421054802c0c101c2e80d207040c00300c02c09a03840d804030342039807000c0c030400405880505254142402c406010700c1400d0005007128a40081c04001402030340084612078007050f5101001c21500c1c2d10070240140101d06040210315150840601034076820000c0c00400420040560511054407182d100e011001d0308400107941c1841c00300d1340340d40f070076881c05a160b016481495422907102d244014160040d11607101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 153873228 1250 153871978 153872023
    0x901090b150a0b070602070b0c030c04030222180302060106050f0304060b1210060603050a090803070f051303050a0212010b01090e0604060f090b040605011b0b0604020c01020a110609 80
    0x1038204000244845503074000d4a902c40000c0048102008111081c0324aa0160321000301c6c0c1000b81030800000c1010301882030030810400c0ca42200000c88003640e0741110611201d0490b6814481c02c003407a04a05554546000f0003025118180190107245601c41d5003110201d81c0ca802c0121014081d560086201039028004540007840613002248414006421441c00882c01c0c2405480c03c0b20303807010841d1442e03840c10b0903c009540360280c20f5000350305146c20f000010341692072a2042c84010072650030001411740c42075030607110340116501d280401d2240c40303030b045d100c2c10042e4641c040d03440200c0c402c5450300e00916244006004245400805841e40340100b45484806181244001e21565100e1b40d03800000c1001c0407101c0b03036400a00300c2c0020003d00444000c09210480719030f50007203410721007200b00840c0c2e110031a41e0446a0303c0d902989011054403080e001c90081c0c0540a0044a294000700318841d0065015601809078000701089400c40c0e00c4d202e4007151103001d1200d210800600c6102e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 153874478 1250 153873228 153873241
    0x10b01020c060f030a1b0c0308010e04020a0b0904091704050f04060f0e070212131514030601050706180f1505040f0803180a03050307032a0309050304080105010b04030204050901090b 80
    0xe0240d82e020f0350074a008503c00f24401950405484400b1600300400c7e40400780d202410350000c1c81034003402d030201240c415401c0c542c001a0021805105070400c0328030004101e40d40d500c40303412640507540c1c040c440d0202904003d400f070305e01da045405814010ba5401030303d01c00034034143c02030004580e030b030080100810341443c2c420180c405009000304103500c118022940031000c9a00203046c415000301604002504108100c984643c82035080c00c100156081002401e80f9004110b03600024242403081d500e803803a1411001610701c824900381c1c03070100024080b090200c58405001024410200e500d4000013040800d000c8910540b4060020802d4120442c000b841f02c10045800400745101d8400e180d003c5a412450203103554001c40c0003c41c040107202140d9014050442405200d40005140c161504116010b178500300c000d080401d9110301400041c881c05004580c040c051102c000d0100391f03120741d03036030715a0390043c80102d01842c50000043d020901c1032144580741c69001720a10b03020b40b10721 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 153875728 1250 153874478 153874507
    0x1141b0715031a06071e0804030f17070201090510020f030d02030f010618030b1302130902030139140f03090d1706011103090307090506040e010603030203040303030f02040b0318010b01020c06 84
    0x14841e03c10381400c4901c041001c50082c07c0a44004c510860700c4001301071880c54681266942081881d45101042c404c6c3d0005030307002046141901c2003138681d80200c581d0041300b03e01c0e00407038080c100300c9400005441c48030003600380c000714401c9014001d00c0c211a681c0781c10441c1c140c6880703840c0c1d00c180300840c00d0501c00a501c5e4581e00340c04c100002190340e01102d66400050b41200d0b5422440e008669450030341045003400e004d00815000094800b074150030b603464138000c0320203d401400354a200d0b00c0301c1341002e042c010358411504248010046d511920600c1c012080d542c000e940c20020340c444c1d01110401c00c3e12401000400000300481300d10740342c035198010355043c0d103c00c0103e2500c0c00203012440b55a01c00700141707401081042e401042604141041c00b00300c5040c0e82c416001a410300c5000e00209400008980c103d035031601e80002c1d00705078482c42c400240180d0b081004204000000e00a54581880c03030056851a004020001ca05070b4074010390340d071312500c08440c0d00044240403072040710251 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 153876978 1250 153875728 153875753
    0x40603020d0f11090406050108190b0607140a140a11060703020703080f041701020403020a1a0405030109080901021b0a12020d06090305070b01090b01141b0715031a0607 74
    0xc0e0808141a502e250100c4155526400c40392141c200100e4034800c14a854040da0005001c207003051a03c034141080035240d41003818551200c29900c44903801d041e41c40320800c40e038a40b41c0001010250080c2c41401075264260040141e17800c06030f41540600100740440d03070076a1343c1d80c0040c0032a400d07486002400803982020034250194040c60400002244904004141200c91540520ba4460410300d03d8502550f100e803001071700e03138418402480182c0742c4c1407240007a42c4400013800502c2c4125070500141c2c0c40b46411498044d404c000c800004c0081c12800b4004180c4240c094801c0060004204811181d01c08146a1720440100c01000300c404400e1107020302c13a0025050800e03658450300d440c01a5006074000300c0000c0c50020384003092007000043c99000d010f05540c18001c0c0ba548100003403400b4000080304a018000240103e14044080002030790150f0942c181c072644d0b41c0c0c1d2a20f86100e054002c81e0040400e01b011100e58984003d085e0030a10100c0c01001c560500d0866120600d40416 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 153878228 1250 153876978 153876997
    0xf0312070318060c0915050c060105010813060c020a1e05060402010f170c09040b01050403030507060b0f031507030501171207140a081806040e1303090b0a0305011d07020304060302 79
    0x500b20503031808039034603001d0040ca8200c99110481140c0c58680c02c56502410100700400b00902800001c85488010070014110b0b207007464100c0082c0c481842c2021404420280180020315101192001940200b45610400e00074041900550b003040e030803891f03034060f542c001803050704032500050040d030184881c0d03581c103485458142c400c0300f40415a10a81e00050760340046140e00480e25031054a4030b4041c140c01001d0038603195050900e1540c000c0c1c82806036103001007017540c90b150204101d0320b940c0848850400c004046401c1d1418215100c80030200a4500100085c10280045426584450104000304c90000101001e001806006180e5040a80219240c280c0c207200746c840302404126040c800383c044c2d48101d0b5201594218910305407003c4510070b0207507000788010410708248500031544034070b0095203070241d0105890700322107180b800d4112555015001c900240c04035810380c1700700e050b034060b0704405001a0080c085084c1e4031000300d90110050303004100c00c0c00618840e03009480100d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 153879478 1250 153878228 153878261
    0x20301240e03071409090102120112030203130608040309080d0507140c2701360b040203100f0b030411060a0c05071503050f070207090e10090f050f03120703 69
    0x5180000a09020b015845014006150281e05504c4d01e004540d42e038115800d06d000718a040c10360207400c01404014400c5401502014440105060090003150a40c000204c0c0752400d0540340d01000c1c141030300c10354040d40083c1401d00c1c0444c1d588000103206010016940b203140c14200f0a1b03a82c844204110f1031680900e0141c402ca1242d2a250800c0c0004260904020250b00309a40784081202d208141d1021295a100540402c45c003114805658000c203c2c001003804000d818042030f1028045280c5e48a400c03d02c000b0030017031004101c40151007035035100060301d841c0991342c03c000000b50005980c058500b01410251030b055141000080011b0f4803541014040700d48252a020f0502c85203900500300011108078492040d64113116096101c000000c00c2c40090504010007541c2e9002d034000d801d8940c7d501c440da171541031010028100810342555003440010054503141c5030314511400304a13032610807110051a000c0740482503850003030207240c0711449960b803800d00303c0180003120250399501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 153880728 1250 153879478 153879497
    0x100902060c0d0305091b010e01080405010207170903010b010c0b1815040b0a0b04090b010302010f090b03010b18060301030308040609020d02030d020f0f0708060a0e01020c03040303020109020a0902030124 89
    0x34101840b00c11002c10240d01c0004003450050011420b105c0912103205045c400d50b02c21030540da0304074900800c6148213291921840d9614948240240300e101c90140040710001026292140303248028400d040c400e070f000f840000c50340d10040d01c5000d0400070003040c2503800c60010b01c1c41e00c900d822500c1140b00c49c1084500c0070405581e07140300c541c0180c07025070300ba04001003003021280450149104901060324104120705490b10b03818180c0106000007410000c1c410880c0b10301c14401d0301c44502038036200040031740c3c95079201c0c0c41082c59840013460340c3c06a9035013864148145031000a40707048980586a0800540c0d83d40d94450003070641c48000c1340c2c0300c04004045005610100302a40b00700c0b80750340040100d045a03440d10340c607026074840e08201070341c03000806001c2d440e0003040c0740e40c00050f032034804114174408a128902a00440409204610000ca000806d02d6415008801481d0081da03550074166155a008400e911090207004040030a42c0744800c1180200e01e01845141140d1425003000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 153881978 1250 153880728 153880747
    0xc070909111002030301030b0606030103020603060103150f120b010803040602100b030304090c050c0f010c0210020c12070804140a050607081c020f0c060f04020906190f270e10090206 80
    0x30b808034500c0315001a400400140104040c07000b4442c0c0068048510508562450b8002684c0d0f1000524927410561140304210440519410410103046081180e84100e6190451030000d070302c2c0e5000c180c1d8100c06c0d840000030240e0780401100c0517141c050f40a020302d4100a100f540c09407080071045901840700b04000140280c4a02c1442103520cea5a50180d03503d02198030140380268000c0c9560701390345003100d04945c0a40000f915149110001c0c40543c403440307007241e014101807500304002e100d4000040e4400400072a40024411703516280a4a0340340b83c10035040c02112013040c09034a8000314104598404611101c002d0500310395038030349840d4941d0001c2c2c640c8060780c21440707001d4141d48000c03800300310044060058541c80290000070062510305030300018181d0b41c0141051b40030305504000501d030035549000742d6024200150110307034500e070342d4240c1c0d0054004031410231407a00b001d000031442e0f020190113400098110034008003103038402200070800034400da02040364002d2082008109 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 153883228 1250 153881978 153881989
    0xa051312020a05030f09040e0c130e12030f040507080a030f0507080c0a11030705010507080403240e0a060b0303070f080c03090312070c050a030b0f0601030e0102070b06030d050c07090911 82
    0x1000345c003d051551241002024031058400384050360201e50130242800800341c0b07603140c03540c0c00d4003140c00b0041001d01d407110804d802d1165160401c584407100104120803070440b0300310070340298400c01c119a0200c0d83c4a102c2900e6085c41003004001485010a14864501c9103001d40a0385002d82080c5240c400500e4102e880c010f40d601084840c245035811244040c5803d111400040400303080240ca081c00c42d65030046180300380d00008090104d04150203080d000c00d0001022100b1000c20704001840310743c4292a501d2000300d40c1180c0681c100061018507080100a540c2e0045d1710200e050703005c00d82d80d9500d01480c0c1042c0c4100486101c144081c0030250b408109200d03982d1500701d152a07540d0104e040000c5000042d8000f64020640d4201c1000082e8401400315806190203840080644482c0012006030a90303030201d03042c40d030000c240c060901c40c005248500480007202200e0b03900d60041001c0c0c0c0e40b4001c2c2001480c1a410a45040111000381e40054203504c0c411801604c030b03008108001039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 153884478 1250 153883228 153883237
    0x4060e041a010f0b090415181b090303050306040c0e060f030f090106120f06090f1a070807020c011d04050f0a05010906030b060103090f05030a0201020a080a051312020a0503 76
    0x1100da0a1903040c21009440c00c40c0c2076409800481030b801c090a0920301240403e02c40c1a62440c0220783e540d500f00c1c400d040b80801358021340146000e00c0c04072042200f07048080c0403100f4291800340e4000281c1159240920000ca0490707030700d500c2e800d007550b542800f044010700e8440114000d01c440f9010381040c503521540140316001d2100e1416450f420100a00b504e540801003c825440e850090140410704141d084041e10755070102d03400313200441504d03091028060340c140052451891500000821401d85000340c070360191303a0035070704d0709a840d00d40460303d0791410780340031001d40c00c000040f41d6154815500c000c600201c514141ca9043c1008001c0750468038102d0f045c00b9031440c6c000500090341d020f4004c2c10b005100301d141c14007699055841d01150300801910143c14103956018940820204515450b411900030f000d0b60340ba40070f6900041d0207548001c21480000d40f4050028030710350554841e20b0302440002090704000d80180d0b550034108400d41588505502c9160440c80015000300000c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 153885728 1250 153884478 153884483
    0xa09090b0307170a03021011090607050309040c030209011706090604091113050103020316050108070807020f07090b010210060f03060c110f01140f0f06040c03020f040305071e08030301050d0204060e04 88
    0x8000001150400a0a150103140d003441000d0a15110723100403807da078242c401240c41101c140790b4a5115180a070310314807902004541107400d24a809200f140c0550203044041803c1e02c4003607080000752252a414601196480d90148040001c43c044e81041c3d0301401130584215a1848595010701c001011040e4902c40800c01640b210014021810140007642c1079190840c001000742c1c0c02d000c0081c145100080244041010060008017158400c0103140140400070f0280da42054507487c0c00c0d4060000d511590340903108003002112290140d00c1401c0807142200800c41605045603515805010404204001c0001340d083d18800030b40c00b40210b41301c0d04059400090041c0c0401e69a80d12880c0080c400760180340508100000724200c06103070303a07121204a50002c3d003007441a070f080d0001d01901400d112644004900070003088400074000040d1136584d00c0b2484040402d00040c4060941806020a0b6800600040003c0d04108a007000032170f01c001e10114a00b030301e031080b5000240c0b089805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 153886978 1250 153885728 153885733
    0x6030c070606050108160c020a0e091005060109081f0b06190206160c02012a060204080f0a050d08100e040503070210081314010e03120108010b04020a09090b030717 72
    0x100e040005a2044000900c000c0c00d1000840c41d02c4814039895014601d890414050380c1c0c00c1003000c544d1480304413170103170003040d021820074108801019540c081d042e2488642c603240c0b81c04603109600034020f51045503060002041c01100306280480c10504146110030a20388541903040307603580b04409003144200400c0f900d51400c40c1842c3c007e10b0b043d409800d1a15420050b221054031b10760049021100603020308000310040c2d4552052101d0a031402c510000c0d564141d80884200002c54004100b15040d010494402d4003c000a4030303100d8034403607002486030788030b403031361022a5005034542c5900c045078805e840c07041a039030107104445400072141103669400014500045140104140b0140241c030300c2d08000900d804440380803400c07001280988440c849240c50440707680c094100c464008503c0e410f49443c1c4041910040c030b001000c0c0141e45403542003017014a0241050320940b121429030f41d0b2a003075540e1a0804007801000c0403800035425014002c0041200c0c1c2200c1c089250490302d0900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 153888228 1250 153886978 153886987
    0x61c0912020d050f090d020a030530090102210d020a09051e0603130f0507030507030201140a020c040f090203070e0a0f0513080a1e020303240306070e01020c06030c 72
    0x80090901605042e00c8081c0071003841310303016030010b540540700c0d005070654080314640041d00005045102d1030f0b000030142e200c1e42d880ca00c40c03060310000307103c284045e040108400720045c115000d10307070103103101590040e0300c05074210308000c10307074071000721003034030044520340b5051100c40c00c0010790788080060070218100940c10010345c02c1400004901d0904811149080b16000d000214640300150424084c2c2a41854660503c8000802c5a506c603074480c0c1120103c56591404e56114441071106034041050001c0c41200520302c1c00c2103640d0229507a015001d040101d03001c010041c1884007803580354554a0f00841c0060b03c003040000043d00c16810159864604003010380c094074624001800314038204001e01c500030307c031041115152030b40300703095540328800414100d0301102c6407000300b001007013660610742c0e4494000c0008d5010301c1d0105203803249603140989004191601c6503400d5003651050f00051401440351001045e241d01c14410742d201807000e000000c449030001c0d1120b000342c490004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 153889478 1250 153888228 153888263
    0x7110304061827053304050105030f03030a050c0705010c02010b0f1002070b0d1107060506100c0201020c010e061306030e0d030902030601030f110d150c0905030705061c09 75
    0x401440180b501190542060203003c582c0304603200c8058445a00da5250f40110704180c3c11500090032204598500c200c824035804004002c00c1c3c0c4202c0064003803460080080350500380411040ca228044900a510315125003500000400f801051080d0311a002c2c08040c00080d820301444424401650000c200301c0546010407102d4041c580c1e41342e109040502100b42040d0300030641d1812604210305640d141d0740c001201308094680c51040605201d4000346c0c5500b002625440180030b21005da440400365000301d441510002c5c150305000e809a400501904500d41c030509458880e41e02c06004a401c11600051b071800700c507200d41002003ca81c0711811034180c3e841c20401e01c0202c510760301d402d21001c54250046600d0340790601010340103840481d0100280150090041003550001d00780c11071031015814206c07050107042e00084103650904100c0c001c10340c49a06000191384004000d001c1185c0b40074100300300d5902443c6103a01134550020344013918423403031003250242c0c0d004804800b050160107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 153890728 1250 153889478 153889517
    0xc0f01050105060405130b040609020c0f0105060a030c030b0405010b060309150f011508040c150807120e060601031a041a0102072103120f0614030106050105040315050711030406 78
    0x50300320070f006000600c8200940d40c0d45004569072100381d050000b42c0141c480c004540581100d410060f0f445d07000050a00c085070002500c1c0c2100e2407003d0081006865507020440314544510000d0b001c44032504090001c1500c40300b0f050782240c1716400014134101c09901285658008a4080020303410403981400c4020349641841d03444030400e104a1050b41c18030400d0012590050b1071002041900c40c002010010800c80c0300000d08074951403268a03801c40300c801454610101e400c880001c0013003c0c0d003000301d8a5030249800440c14140a080c0399a12080110b000703001e201a0b90012070800002441c4540ba207210b6007280c2e90151040c040b842d40c05000280c602010760b448800c035004186002c43c5540b580c0c01034050415850305d02800444000f1401d0300160440e42c520046480c6002000201045c00c0382c91043d11480a60007480029682c03801500c5078051440060010015070340607a003030b42003990041e540001c07a41805010364502c000c2c0b4500d1758010b41c104001140c8280038010b11031411 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 153891978 1250 153890728 153890731
    0x30c0e01081e1f0909082505010203040501020d06060c02030c0108190905010c0305061c120507050303070305011a091804050304030803090c0a1a070b220c030b07020106061407050703080c0f0105 85
    0x14005d000d0342209903503c80c240d204d082c60402c00c14404070702e000f822050403e44003400b250018000c2d5100e00342420418000d60103000ca07000042d290030000501c4c2c41c012844c4030b000a800502131b00200030745000540b50310030001c140070001c0707420400d503060064052052850890054000150728428118040c6c100d40e0301800746c0c0d01c546920070b0a0100ca00d41402107060f00741d844806141c0c107401100081e607060240980040460201004200000e5456881301c1e0403510703519130f44402c0714103181000b92140b03e48044e00350489200b060880420319010300840d0803078888c00032645082c0d070700d440d0000c07581c0007682c1100b1aa00002d44100080c0f030714604c1c00010f00041420350511341c500340ea0707954103407041c1c1500a0126201c0d00000b0410b10f215113182d05034490203000c80390316041a1424078102c09840c001152010a000041214603205100300810317100240c0310441c000169204a00a50700070304803c980034862400e02000040d4080702801da04079840000b4601c07401c00000c501d095410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 153893228 1250 153891978 153891989
    0x80c1f0f030f110d0c080112030c0201020a0804091a150d09050c041e050a0c05030a0b0d050f150a0b01091a090604090e06130203100f0905060103050a0b07030c0e01081e1f 75
    0x40c00030042c8407001d050102391070650741c5401c0c45c1104004c1d0340f00607400d00740502409807980e03002160005850280760029078908481c100750040c103844039010040c0a8400d18541c0184010500c42115424060340c04802c07105d00442c2199240d04a80300001d045c0d030010403c5010200300c2e5042c0710890185401034607082490402706001301410703940004c125000041080da02c00c0d4880c0744c000956141e041c80e00003100e07040000d4800100c250700030160303a202070400c203803810032010002071010407140c4103003081e1040586d504117901d8070302079844562040c3c40302d040d1300038981008446082c0e039443d8014002130505d8840800d03080e40e1001d40d542040d00c01070800185200764900000144e07004203c002610f81f000c41c000032891458a0303504010400304800421500c2400f0000c01407050005110001034481d130300b6120941d580710401c4061721101408200070508000d9000065809805042c0e40151654010b225a91080850011010080d1030603800104045900c03900784d041041001d01901 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 153894478 1250 153893228 153893237
    0x717070512030a0807030906020c010c02030c16050306071107091b030b0301020903070501300207020301061509030803040317070f08011401050f090409020d0b01080c1f0f030f110d0c 80
    0x20f02c00309014108140080c921002c16640b100700c00304002c0e0590655507180000c1c0004c10203528040d0000e5580c0e800300c0384545051261295958454007212030000c203403140940541426199000c007644c0f16501c0100300c007840d000c0c0340008918a035141c8600a114020b0407085034440c4003540d000740071554030080e00fa0180e40104160311068600240282c1100c0c1c003031902d905240c030200581020400f44a00401d03420b0507100700502c01204a03005401140c2c0210020400142d1303843c0e0b116101c00800d903452010400f151030410108405c0e0001e0369106020b0f00f081c488801c0075034445046580c040b640307000843c0319180d0189500342e0080c521809000030341d88010084808100103490350081c6000e08166400004007805141c44507004060440d41c003410030784d071004083c90181c07400c50090140010760700c146061902207281205c00782e001128100c20880c1c50700e0161004942d15009440d420081c1500c906460500c10402d00c102102c000c4201d007040d0f100c00e04c1080140903110140b000b002000f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 153895728 1250 153894478 153894487
    0x901050a0e0f0a0e0111040504060b07020307090c0c0f0b0f0c0408030403080c07050312071e0807080a17100303201519050f04050c120c12071707051203 67
    0x142400e0a090b000044248280480d544030180e40020f451841c0c000c030410f5080c41034035072800000501800646008803020b03c03c5a845545150490050b0700002e58142e03c4260100158240c40e4406400c84006141041542e0201d4131101c100340720482d02140c1200c156010001844481c520164100b08405641413a00b45800c1140c4d0b503a000d2404090000940050101d1040408000300d600403e0094291440d80b50062011192604000426034440d41c00090008a00840c08406140290710407000303810101c0b181c40d81c030282e820400e40b0100f03000c013002050010100d1015114440d2038031041c9002c0481c10751900500174404480b1944541326040071424043d40c01040ca07002c1180c9640d041040e581e41c843da01001c003030b1166100354101d442c14062041114014011900c6107000e6011940310b9200e1006122410100d804032452503080039130103124524181209105003820401250390031602c94500c2c08003100f81004028050780180410080790511030100c0c6c0107988600c000c0c5080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 153896978 1250 153895728 153895739
    0x507080f060d032f0d11120307080106050702040f0f0e2103040224070c050913151e0f021e0f0703080604180c05090c041a0306060c0604030e0901050a 66
    0x1140c0201300114203600240010903282c0e421484110402803207401113500150344070300c1c09003050446070b04000071030141103201d1410003030280c2164080c000325680c10a02c0d03840c0250860b11604a02422a40184c544030350003111009030045511003d10110002102500e000c901d1b0b140948888455442c606503c4403c2c1030380c050035060b81d901c142c056550004490350101025600caa081041d911044400b04413001880350500100302034403019a1100f01980f507540120400b150108001094004600025041080300b0f400031541c206480310b03091590640c106803102959110390001400036030215079040314004000c0c04070390300d0222078141840c01e1210034080206114502002c0c007071020101c01304d0499181c607408a1050500044880c10000b070510300070b10303a80f6062042c1d034414130580020400d00d0308080c0c01c68003100c40d00740c9081c0102c02c1c01841e00d551780e00001c15066010a0034080217001d9181849a00d210340d1003a5211159414150100f18048506800c000c0c000c000303042e4107010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 153898228 1250 153896978 153896987
    0x6030b0a030b0a05060102150108030703030c090b0702040b03330a0606020a110a1203050c0601050108060303090d0f0206040305030408150609040f020d1b08071d010e0c0c010507080f060d03 83
    0x8100720386410111381990707403100503494880c0d40e41c0d09903091148600000b5001d280400074290252090b40c00b8080c0080d0510b088034000d456010b802c1e0160820810500149402c1d4005000c0500180664840c080d0001e1019400704556801e441049c0e000c60802c444030000f8911140e02c2100b60740c1c00c03c541810078138000e40e920340100b402400d0f80f200c220044450394500c1040340041c0f200d2810b481020b1800d281c010219001114801d0300b034410b12002295540c000c459a0340310b2040500114200100001088078846003503401799101071a414449026848500017080907601a100446d9124074007001280ba000301070003000b01420a52040c80196a15581030340d41041e001a6807030524401e41c00080c11803400c50034018400841d510128080b02072420036901220002c10503161181c0d542c3c50301414001c07040c4d45034004840c007000140b1051600b2402140c000c1100041036040c03106258802e801c4582c2601e145010070412001c100010818162095109800b950340c4020800d0b40e641c09030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 153899478 1250 153898228 153898231
    0x40e0d0f080c04180b0306090708030a12060509090a02190b0f03041514011508040804060503071e0201050a0623041e060906050f030d0215041e0c06030b0a030b 70
    0x7001900e0307020070101030804043d28090035402c01d12a15944042996038020174110301120b010f8000d00000884508000c514403003200c9003c005546009403000040311051044c0584c0400c4076035451f4082100d80794148004c1c4216269030003822155002d0041004c0800d00c1451500080311008003030000203c50001c0d00d44006001c0d0304180c49454914005241100300d1922105280c58026102c6070480d12001c070300d04803004410328251701c1980c1503088030041021a400340a0100c02c2100b00907040c8140d004680c403c200d86403100c4141841004506020005510a801070b91500140110340910b0b00c0746400038079130094429030000c0000004103800d220241114844d03681e4030503111141194401c8002101800e240800496480d642d041c002400d09000c0c07580034403c1e00346049018200042d0104d54020030780c00806140b05da010540c40c126200400c11070310710b10110343d0141c10581180015034410710480c100300d01d040c01d1040040803100316203021751088421080c1003020401da56041c0b07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 153900728 1250 153899478 153899507
    0xe060912160204090b06120109050307200901030b0406060b04140d110d0501090507051518030304050a030308060f030106060e060f040305191a010e2a0a030605040e0d 73
    0x5611100c00015012500070400400707500203050820240c10807442c070649501c0740100700c4055600e0259000c4150885036094001009a8401c22482c00810075091801342401a0031421544030f64011003ca00b042000380c1c01164401440b0081c082000200c1c02030070041d03c4602003207405c06d440c0004424034a213950b035000d03004802d0251520207000c4190300450003008094001c3d69240726074030341079000307103e405401e450b54000d02d4804035403031816070050078031500070621003070a02c0342c600a1038034074511429155a03d480100700c0059140c035411203510065009803108001464010140301c00ca00c4a00b01d080e100340d143c9402480101d4000d1403c80401c28142d0b402a100c11190f509132a980c429504040d00710710034006040070049004040b0a9400d00c10040005244070804241000050a0041166203424400083d25120403042c15100070741c0d80c803100340c407020034100f81c021a9034042e8426170b0010740c84002c03e12242c205402420225140c810040c01d072031082c951300074200e1648400f0f4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 153901978 1250 153900728 153900763
    0x60709060309030e03010e03210c070210030f050415050f0603060a020903070305070e0106090f050f1203160303060609050303030415020a021c02100f051b0d15180e0609 74
    0x104803e00d0320800001d040100041c0080295845a81390181d5a0300568410a821101038078080f400522803c00e03a030081601c8422581446c1b070613400c100301d890f40b65a403001010740d110380620010021340500780c0100c0c081d4dc2d000a03903800300742c10f4105441c1c004080382411901201407000540380040c070280d0080c1280e10068076644403e00090500c44a548082c15030321512002150355080172104070304031084c42e01c41c14101543c80c0c641c907444003003510071994020340184155141d82011402070094251803825607281c4a00e1803032410f00f20a40c0b02040e0300213641c41c182400143d4100b4414000381400318010b50440c901a502c00c0103285151701410441d6070042040050b5900800010031911103510000415075001035000b940c800c1c0c000e00c1d0003040f5051038041d1315826841d101d0180030f02c02c04c00300c040f54000b0ba1041404207501c15283c07107c41595541e00c00025801c1c440b95140500f81083c0016005025000b9441c1a542880440d40440d00103009000000400095101444410510 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 153903228 1250 153901978 153901991
    0x604020f030724030b0102071d0a0207200108090a1e050705100203030901060b0703170c04120506060909030c0a1104090803010b0a110613110616080d0e0607090603 72
    0x4070342403038910b92240c500402140c40034642e02052402003000400c86075020440180500f004903660341d0a4890707034400c1da0314a4000142141c401c0d2141e07a0224800b4800b6150035195500e60701552308807100244010407501c0e00310415070380a0304d0150002c2104000b0440008640c50307010301c40c96000c0c0103020260301d11040c4d104020003801844010301c0005d02190521140300c2d8060b403a54800c40b0220070759482c01501003806034551080d100080d406030b640f0b0038203051402c41000001006401d003248110107100c0081c400c0b80c9207041c04985441040605070604103041401541c2c1e10180100341c0a41041c0700200c0040c1c07000600d0621180c05c41e40c40c070f0130482084003040c01042c031000c015003107550001c0081015081c0c0e400410140d070072650749202200b5440c120750388400050b5215180070207603450b5080425004805607824000040c510b501d456030603201c000280c85d4800c02118002c0c804292161102c0b0b040c4140202d40d682c2d90301030501440e0026000b01402150701449052640d50b24 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 153904478 1250 153903228 153903259
    0x9010602071d090705210c220209040902040c03020a090e01140907120c0906020607020d0e01050904022503120203040b070c061b0504050a08070e040f1a01030602071a040203060402 79
    0x864000e010241c901101114004400741800d00e12010b109078038855981000c10340e04048c10050712528400f41c0c1d4001c030302101042400654170032140540e01c10b494031810009a5180d105451078482c90342c500599800034103c002d40301c800300d0791000c124039404c407004002200840c001521100000c94244090741e032541d50540f6105036151640c001c0303074504100058055002003100c02a102d4036001c85005a6401c03400703d0b80d07010207081d4540007e100c040b1800040d40904040c10107030070000c1c170160821002d1484071030704581c12083c150403840340300010018590440d44840c103003150400300394a07526050700c5900118401900303003410040018401000d100c080c4c1e20040e0141c101001c55030510f001070b44001c089130042d0140b103200d550b03000000100070600103082c1003250340901d0300c10040c0c1d65989800e010110315050940b0310603c5c88803254004000103d00701c0c0690320480c0c00584504040c244034800c002d2440400c03c00301c1c42c07101030101503540001d00540c4164111220045445541c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 153905728 1250 153904478 153904483
    0xf0905040215120a0b0603040201020c10090b0f0307090807080d0c02010908061005120102040302011407080705060a0603031803031d0604080d11010b04050c0706090602091003090209010602071d09 86
    0x4403440111000110740100c940540c3c152513801545424018071001030101c0820076240700a0ba0000c0c0564003089010321141840504d2801400050605220141e81c0d140c0c4082c0b15881080980d000c00b01c000100900950000c0c07058001d02035034030040910b80e00700308407680e803007540c0d0508a09012501564504581c468000d12010b015618160341403424410504074014119000f00c0d80305011a144000d02d84005200703a13000c82e0340507910301401d03c801c508200c5240d03010080545110340104078040102e07008101e1940140c00d40c2c039000a00740c4c0303075090041901d0686c0c2c4889078412603109041000c00d9008441c1000d80f1030746110401428441c2c000a2518803440c3d20034015400381d101c8050343c407504588d5500203240190000c2c401c00d0540704c100022290701b206e80c07040b544010300c140b4001c0b4140d580101502e40c4503880040c0703404118400070705c0b100249174070a40040e880d14124400c5080442d026401440759000600207682098a015405002c41c40c0c988400390003580002d40c0706008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 153906978 1250 153905728 153905749
    0x30503060f0d03050901030f0e0a020d170a0215010807180f1e1a1215040302010e12030a0c090b0406030c0905040203070302041505040503030711010c1211010c090f09050402 76
    0x518a41042c000352a014040b5004040d0803400700745445c49042c030b49207050203450140c1d5543c402a0406141c95400c2201000c07060005881211118060380d1488d16400000d00c01c40d903140d0000d10b43ea07060083c0f05858510143c00101050b08001c60800c008544101c46034402c80c46003002181801c1c0c5040e94a0090900c42803182c800795641208080f00301d10ba42c402d160919125520203201c0102405009010080e07800c500c2c081d50168500c24820245d600850b40c10501c00d200200359154030804240c0f0b00a5800f48407811103000001344016001c20740700f110625461402d14010340d5160001e8154140128850002810b840781d1503645264480c03803a82d000f0b0f2800138000c548a09001800034003d4100b80241d1003100d4403040341c0142c543c01542582c0403550000e00031490020a56100300b07046c50b00040d030606010b010340d244000503e188401412103012542d418440044280d41217007514200f650880034442c440c8410b000d20f03d451004501550103880000c1919152480800c1caa2041d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 153908228 1250 153906978 153907009
    0x9100305060d050a03030c020106140d29011d07021908031e0a0b010e031c0e04020c030c06160c020108180312040c0f09020906070b0705040503100605090f010b030403050306 76
    0x40c59134000400d6010b82c4203a40c20300059000704180d0b0f4484040c0c444100032885210f6115288000380c0700025038050056001c20741a034000942c40781c0340803c00380381b40b001fa002400848600c1424030040c0b1030002c08940d001030244024202ca88940703040b01500c041001000e031490f074000000071030208040c0d403e1204442c00301c640c0103541c50408003942c0100340040309180055003c038103540c4945070000c0d00c0d107540c401d00c12242e120310f0440c60050f02c600c1d0030395901542254003804208030511061029003007072046080900401e25214203158145201c0062250510401000d180050b0741c4c8044066030205e003840446d4940305150131018a11b0090804501412070102e0030002000070f80822441140e1214103d282000d4403021500241d024902c011030300000d00340243c0020a0a012002d41c028400d400c100c2d1a140d201c2c00840d042c40c4281b61400d40c0350740c80f48410009803c0540c0d865500101c0b80c807035900d00754101107290703215100180c0060308002c2c020001c2501c0e40e070b80305242c0c03250f0034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 153909478 1250 153908228 153908233
    0x816060e100b0307060512010b07110904030807090f1a0721090317030c09040911040513140a080306011d060a1119050304050d05030d020c150c09100305060d05 70
    0x9101c014248068005404440d020340120f20000071824000c4040e01c00d4100302039140c0041e070307090181480d081e4110360070558006c0c00c1d05550300c7d510b45985c1801d40c0668000d41d10341843d45000c1340054620107032a8000c05900403103100401041c640c07080100307500845101010358805003811f00407a0785a060308917012440f00400100700c0190008032040889100781d24407922124280850070382408215111481c55004100b44031141c6007546c840711496114154242200d21414045800c4802c104e031540d046882d14407a84c824000000c89020568041200900740b0800aa44140043c04040c1503181400b440d65004c0101e075114801403004018042d10290725290010070051180b242d030f00d01c4400b00e000d50f2a0100500b82000104005582c20400441c0f41618160502034405440c0b4019607040c0014000d400d16043c10340010088805210700a00d0301016044948407403240151034000642010001c0030ba042d20b425180d1429800c06050000d00d580e14600481c1ea44a0030200052460 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 153910728 1250 153909478 153909493
    0xc020613060c050d080112030f11070e0702010f020c2515120509160b0f040b0310050a0e22020a03080a020a0605010506040501020714030102070503040b03220816060e 73
    0x10740c402c00345180c0c40c1c0a84116040b003502c1c0c110680b100a002c0c001d075200c1c00207040643c400309010f1030032040d560700300c1e03d030190245002544031810032002d0340080c0c2840c45000c040c409034a50902038420381e49034440302140740ca45841c01c00b03a500c1075810301003845c10030284d41c06045a0005801540117114650142d141548407a400504c28081210300c902594070b00b03004204018000a04610310a10300c0d0b002501003030500f0305110058102009509000381c0800c070100f10868818050341c020351a6104641809040c50100301480401e43c00071b80030907403814208184500300d88071000000721401508000c604050000c9062182580c2026001402c00910020060780c000340c1071364014003926041000d42d803503900700420340c4070300d206807070060340040f00c00e204011114107d8041c112005000620b4059155181da045804c01c0e44002c13004800402007042d1488c0040e101d203c90081e100007040000496a2150740c00c3c02104443d00b003242c44070007850104201540903414203c00c8000306d4954 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 153911978 1250 153910728 153910739
    0x1009050c1e1c050f0706080c1204060b0307050a030302070e0714041205031303031805040e030f0d062103030e010501030f0305091504090b041407020c010804080d05010e0601020c03120a0c020613 85
    0x80e1710180c03145800140e044000100c00403143c03426202c60307100106000c0344544550300c40304043c140640031030741d26020f509400149540e0303603403540008500c41c0c0c020b0b14455140c600d10344041840200300c94240441c0040170140224101c045900740e4482150204081c41c150424a01c1d600580c0412842190030450210501d50030014000d00d44840c00842140c05031205c05000c02d480024400c5c0c8459072042c001c03400c52607aa60003402012260f880300183d207695401018a2100100c01040104400344c2d920805050340f40c06013450002c081c40c020b101e15450b42d40e485200000c400d074040c00300328010890108503039500685080b030000d400700d66512241c03118030b0b0100400c0e8240d0301520440c50711001c200d040341900509485104181c0240c00c40d04440d030010b4581302e5004000b00c4501c0420085d021001c0040e20a0307030301030000340c0560349003442d04100291a0040300300d28103110740c2c0401d240409a481d1082224111803062501224040061012410031b0140c0e280c14065800c19020201c2c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 153913228 1250 153911978 153911983
    0xa06030b010608091009051b180a02070c1a09041d01241d010e07090e071205011d07050c03040f030f020f01180b090607051009050c1e1c050f 62
    0x19034084003a9845001c0c0d05c0e0380c1c007040b00da18820043c125000103003001921000001d00c820342ca80003400c60040381d126540a04145241151580406035000c201001881a0404100d001c1c2442445540b5035415041c0c416500c1e02850922034852038540c581c1d414000101d500c0f1001d11460107009000420340502e61001220006841380c9003c2d00d807890029030700d965000c4048080c50903501e04c80e4035909002c444003031540c0040041b0184040d032103000039041d20400b4040e103d00403a50341c852a601c1411402410b46d001a40a2040e828548220910b2080035100e009d810102504059a44003020400c090550060780c0c4561080c0c43e5003107000050042c0c9040d0b00c2e0b20300d8800c032884060f00b10050010354103064214442d04c80c0c034041a0050242c000384600800c11510b000700101d040003403554600b403030401c514114401d8580c0321034a040070031200704aa0307018101c0c100e0340030380a022403180006043c1c3c0380340d0400e4402c001441d002c0484403401c2e030999113041d8110090b691150b031410765055 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 153914478 1250 153913228 153913231
    0x1207020a0b0c09010c11030111041205060c190309030e0d030201020c100509030f0306211b100c03030510030c0b03160c03120b0109080f07090b060306180a06030b010608 74
    0x140e807a9003900028401c07403030350412601c607054161104884900f25861708120b002e41c040c1825010365170f504061080a4800c0003400080011120398114031031649011420b040c000382080b044001c0502c80f070f0ac84446400420304045c102c030304d000900900d0703a00342212180194400a81c02c01041740e809000e00d607040d0000d0506c90a10300460300c8003a44d4484250407034004507185440d5410034003a240bc0350f90804010f40d0419001405841d5100c07003103020805112080500083c1035102d030202e00411142e6150002030804200e42950311501811005403011505a2000b0708140c0e5843c00180720001c81e48081d030103103822035140c1c0c5a080d11500b21500039401658043c3ca450740b41120511103500c00c0b0071100c1511780c15699060880341d00000071006e80720303c0c00c0c00da05000403120013041c0100104201850141200001c0c4001440e101c480f8089808540206005540c03c20811155496400380c0000a40c50781d5007106241d0754079034940c001401c442d04000d000054407400003070071584c4068040d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 153915728 1250 153914478 153914483
    0x210703080a0507051b010e150d1505100e06091302220503072c06031c02100606030e0a02270109091a040c0b0a03020d020d09061103040c03020f01051207020a 69
    0x301d00d428000c8056145c645400d8142600103040b45101c80d403281000e0422004c2c2208541c1000d08280c190342802c0305071141c100000d80c2541030910304115501d808030901094208908100b25014800f1b40440c525200364004240201000c1812014510320b80c7e040791100760580ca0351014540e440e8841c8200000c0700e21485109114109000c5801e5580850000161134101e10341e1070405040460001450002408203515000da050343ca0f40401700400b07202888522907010704a6102546503442c21900c56400200405184c0006038490030000a0048046a0100d800012880c500034000484928062198000c10881000050102c2c2203401c14103002c4c3c403c038100200e1640301c10078514000300488018088100d0044200001c0403980003c000a14861402624211008580700280d91245162520032650344103000305004d0b003441410003c80760f5009035440c50610f0b895a042c11103007800064452400d00c0114400c0380c1c0180212044c688011209d041a031914041c00f030b484a0404105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 153916978 1250 153915728 153915733
    0x9010e04050a051b0309030d0f060806070207080706020c03120d060f0b0a02010f0203041a06060f070803011a04030c15170c070201020606010801150c0204020c030301080715030b210703080a050705 86
    0x4008044c01c2d40113803032243c0c40300c80c010340c20035105003e400060080786d5200c5006698910020a0130ba01c18005644101e90940060884603d0308251307903c3d180160340404115003203d402e1600c1550042142110025411145078460700c0552001d8010701d502d501811303526003000c00005981c07800030064224406150020080200340010348801d030321040303800801800040b00800d00001003072000d2608910041d02c110f090205500800d50281e0200005803452030001c00100001410850800400c034804a001c6080034038550b151480d06825020350b403142407146d01400300c207920071540e03004280381d07100030312009060204002c0c1141c0e000300000e900501668000990365402201c900d03049680743c0c880d030341c031011590074111004000910201c1e40950200300c030803240281080954003911412002d054402e2800591058108076007802000b03160809220307080594400c0b4507240f0644d4203072507108085d046001030608052441d00000c0c04160041007620900da0302c800645040c900c01d804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 153918228 1250 153916978 153917011
    0x1218060103120305070c0f06021b010e0a0c080d080403120e0d030c030c03060b0a050a1b12020609011415030118050d0e0303160311030706050f06310209010e04050a05 73
    0x1222000c06c804005401c00c01c02d0301c1d840000509680c01000000c11070266150003c9202802e00e00359858090300113142c3d80800c041c12b0911071b24034580c00c01414203000401d0142c0520a0181450707000030030107401e0000c0986862062a11a001140302840b02c1043c5c8075400107005010b0018420351140000184c40c00e2142d0700c42d0f9019200b0780066a070282d84050410b15982c2c07048410740d1009403001c080106501c441c0c1078800c00c05040046241c0300b5280d83c80191710b1003800a141442c010a40035030b6a06020601520014046a0396040059080d000c2d4900702c0410209026124009101e06d528007583d1250040c4140422601d88083c01e40e0b0303942c0607080c1c03200d04040c2d99002d500d1800d50142d2070022410000703402441d200c1c42c01d0b1242c006403410a0559120041111011603034071001f15100d00802285103801500021850700305240d240d41d030848143e128020034103190f540589150b001450b4009680207550310100c50400400a020f0b81c83c210301460080c14040d201388403200f4180c507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 153919478 1250 153918228 153918241
    0x30309060804020f060a050f04080601060806031c080408040302100908010c020c06250c030302010207050607050a1b0303021306021b031c050319020d05040506060405010602031218060103120305 85
    0x1241c9010701d4004001c800b584200004010a59014002420078040c041000c18001601c10002c1c1001300130341001b41c8025850980050211400181f216120350401d41025002540320102056564094070f8120303510b948600e4200024440e60b00069030050700c40070f5003e5125444100d10702560407004c001e00589c0c1982d6030507a991030f50034600a038808003d10007c6038684546441c00e4807048105600040b00100b40c82d40300c40e40c00a500141c0040c1d40001c0c01e0003d00008014881e00040d05281092a2400340f55008040c400c41100341d500b0580b055011400f07141c40ba40549021100c00c07403608203840c0e070302c10000c0d5648000400056101c24034007402c1c441c40c40d000c920504e0b804000c0800d810070010388da00c101d840d940010205043c40c8944206882c8440052000c0c0122100c1d0200009180c03c09051042c60401c0c000c0c40144682c0c146001800361a502009540182c0c2801043c41c3c1e151721000c045011440310603002000c148903140000040c040c5015090032000c0507600c00b08600d0f02d0b040f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 153920728 1250 153919478 153919487
    0xf2b05090c1002030409050606070c0e09010513020d0305070317090d1b03020d050309100f0c170601120b060c0604232805163f140a0f060603030906 65
    0x102c6001c40584c00c1803104100611003504590383c048401040d0034981000ca6844c80701c6284e05070042e510241c888020003403400404d104494100e82d0360107c0c4c801c480740d1980010700322402c03004003c4c10802c02065000800d400f03000c010041d090126400d00c000d2401000b000e54030110f118036440002c20140039485e0b8010b10040e040100d03905a0701620610300301c4402a101c40d80041c00c5615180700d41c011011036607481d8821040c103084084008500c40401100043c00e15280f140e030744020140e0b03007044c0400c3da0782040d1342500c91414401c2c0400da0002e00b03000a070307250240800003c140d015100821040021600c0c1d599107a03030b2041200c080e0421407100705a9070368280d06203903d0740855103100194002200e0111103d03148510100d03041c641403500709440005065021070036849515050f4603040c140c1e610f95005492031f040c1081035140c0c42004002a0744410003004e0b001d08061207800400b410103109114030340b030b0814004d28203002c45141c41001012580f01c282c3c00102208004103100d80328 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 153921978 1250 153920728 153920749
    0x60608060622090504050706090b121b070605040b0403140315130f020c0c040c0302070308040b0903040312050304020103050a09151515200307080f2b05090c 69
    0x141c040c506002590350403018440e060800c512a2074040100054400c2c024043d180c462803184000d04181441d20030b0141c10040d981e00800750001c0180100d09020121510b1654400708049910520784c40171090100c01d8401c20b440645218203000405c0240503c445050307010b148030351303608070004d000c504a110303180c0000c1d11100d980c107407130301c3c212013103451b0502c421404084e5148000a13500346541e4900c0480c0e22510422041d500035540c4143c09281510070074080b19428101940380c14119907004010340f01c0140f0040104084002055401c80200241c40255500900b10100e04410034000340c0140c0044600703d0010b030400c0f000070802d072580e01443e0001c1d0380c071620407040f4070b428a070701c2c001605100c4845595003000d4900021441c86502d180006003c858840f001d00040c04003e0f010b440e0140c4d07485400b50703402000f40c0710004500004441c005155640340c6604da01000f0302c0f0748a41c40007004421515916640c02d1580c2044507030000d402001c1510840d04000802000e12228012 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 153923228 1250 153921978 153921991
    0x216050319140a050a030b0402030112030e010f050f0c0c0603090a0605010909121d031603050106090b10050c0102070209101403060603030d020c07031a01150e0d030f1b0b0a060608 79
    0x4240143c41425016801034a0b000a0320b05010580b05000e401160490700242c0c0200744030001c0c1c07584041890f03006461904031510a28012618501c000790107400c601c1590640f1184002c00580b13000140810320a092007980d0061072660b580c182180626505c0f4082001070b2400d91814000042c1e19201c4d1144101c0264042512015040c2c81e40e02511451508422882d040038403840000c002c0c0d0301801401808a40c410003849983c0c2582071035421102d90341c10036400d0510f094541c14039682c8440d10102250070f60702c3c1c52035440c11a130720340d079001e4010b00c0b00003900500342105020302c0e808460709050640b00d11b6050103d550620800701961a0000d03515240c064004200c803112200d041c8d0003e10310707195541e0890740243c0c0d50750344d642d4110f0b613882600a900c80e8034a0050001201c8504006600d83c2d0320700c1c0550300b05607a100061060b541c1708500509010301c01c048cd844c5c05001d1521441410210122002c150138141494515100101e0780d002c0c0d40e078908040440d480b030050407014003550 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 153924478 1250 153923228 153923267
    0x50d2709270803011401020a051908070c0e0a0b090f040602090f06120601110708124005100c0209040204090203160f1703030a0f0216050319 62
    0x185000403000051000a44590005030190904420403a00c8550201503034032034200c0c580e40c2c1d0300d000d0320141c81602002103941150042c0340044003051000441d4a011b41d1034840502541c034580ca844d0005106162008024800312080080c0110000448620692103c0c0f0144008103c940070082c501c5022039400d203605000502140105d4541da02810004002070944c10200701e420717000800540080030802d5881092404000080d64001011607a44204400401c000e909005880e900d48100940c01101c0c2c200108058004c50a080b102c100c1b400a801c60ba0301405681100034002510000120102080c2000b000509820304680c0030319074254070713078400598111503800c02902081c00303001a0f030b1140c1c542051902690b42800040301100400281c0240c45161070040070848540d940040b1001c2d01600001c03141142c04801c59602002c0c071039000840030074961080c4020300400e05810044190207d404e001c2090009c0249501c604901d00c07130f46602d81c241d804444a45a00702043c08c0700c2e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 153925728 1250 153924478 153924557
    0x1206070e01050304150e0f0a0c03060b0307030314090102010b0d030e09010e01050319050c04060e10080304210c0312020703030206010b0a0c0f030905090f061003141b070609050d 78
    0x4051b601203180d0701094829181004c0213400000e2400e03da800041d50806128842041042140d100e1020804800c1d0b000d410441d181d034034007812406e0054031040840400282c20362207030f8801e40c000880b842c070040494030717000c82c3c82c1801023040307201d40c4825000380307404800458140980d00c080c03030481e400140100b154000c20441031300b0219100b003040740c0c540b040e040d80b84580c0c0c0e10341c080c0c0c00c0601208002000d01d85403502c1c0c007240c07145043d480040584c004200c04e0180700c0c4403501c05603285083c0b1700b8800b558010361134418407640180d0700c0508401c6803c94010152580481d02000b242d01a03822140c0c1039803207460030300280c03203142c141e5404191088992400501c0644200345d5840c040d0420101d40c5039104007146070745d42c003141d0102c01c0c0c2d0b03000340c00c002d0a45000e511611500100e85010070040d050010442003110018004c1d007038043c07040ca200a0001302150490300f0065101c0f00501501006181041d502c00c020748e01000850100c13071900751a160505201c4d4280365103000c414242 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 153926978 1250 153925728 153925763
    0xb07091509172805030f0a08060a1706040807050c042d150302040e030f030106020114070e130b04060302040f05101d0a020a1e020a0606050406080714040b1206070e01050304 76
    0x400f0b0207030003180c10340814041c3e8058500b078540a0101c104060f1120000f40c50404100300c1d1015450b04844503404030f04140300900e0000080281d84642d0181c04103030340308200c1c140a4174080c0342840b017550041c10540d00d09405030700c10014140c2c0800e80702c440f210006401c004d80040d60004007014810f500b1644080000d460590000704400042405480c030306001483c1c110321540c03090304501c0150b9101c6501030828401180039990052480c500306510726416030001701d200a00c407041c400d0040e2070307600d0409656901d500000003140e000700b081201c041002c20240107060100d0310084110003000e4005000c0c0c802d01000c4500795a1820b1b00200e982c0e0b015a858029007010500310104407040c0380070f05400c4001c8941c04407000c205d4005210000c498507040007900e1140d0401030159050100400034190001400b000b61404050341400c03103000280032030014013088000342d074070211321000c42542c10008550b29014085070b544a50348180103c0040d01e19100558000b00050181016a102c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 153928228 1250 153926978 153927043
    0x5150a02190206040e0103030e01020d0f050703120f020d09020f0306040b040b090705210d030c02150c130b040f06021204030209040533060307080a0b0709150917 71
    0x105070344002c0c511800d0075103901030110399580c00d0300101c000c10760003c140d03451581c041281001032510780c901030700c0200382c1e8030303008126014084005060041d401144d4100c0d600c281c00c100421401c01c0d008540300c2888040c2c0c0400751182d18400e90103007240c582191407504001c60030740d1089811401034031840e20344d41c1da44540548000c202000a0044150100729039840d40c22070070514002411003409607480d18030150503e0180f085403014140340c51517100450341c0104220014840ba0800030301345617600020083e40340302d5007403c865650f008044c0458840101409481038540c0c0641030044513445140c00d0b40d9694480c01c181e081440e092104100500d0702c0d03c69160b11030320a0013658507800c14808400070110b103203603013a0750b4805c80c0c00460b00b21100ea124000d078040001c4000384001460004071585420742c842005c1c20302d59005000803034440c080c0b001c1000401040d07001b010544030100f0010407143d117030300a840401111003088640b040000480100c02040e06042c1d84814000c200303e00d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 153929478 1250 153928228 153928273
    0x8010b0d021908070e010e0a06120f06240309200f0409050304051806090a0228020a03080c0319020d09080c160f03080904052e05150a02 60
    0x149600d4003003150314401c0480880841c2e041d10ba907122007480342000c003409006640d02e5040681080b10146803201d040e034504c20313070104541c0c05041000701414190803000103408040070008646081038000180c0f5100ca0035003101d408660314001e01000800700c0110265118084081c0032083c2141c0141d602003010003400ba0603084c002c03e80c2c40d06039807501c0410250307400c031a000d550360781021508111500b1f0592030302044c45011000d00c0d82d149005000140c00c424080c0100c0290396000c1003902045141c840e43d405000d40c650903160900d0760f6035400079230301d40412500701d0000e880d80004c02d0544800909980c052004206c407800d0400d43c4006082c02174015900d500c050035121074805002c1000c01d0024110303205c2c0200504480c042520550f01c91040f268040e20407405049070030404510f1b01802d448002d10200c41c08140f503101d590a14800c11001c84504003070381c8001c001c441c503250400301080f040782c50543d50079246400001c4400300e82d02a1810810150b0800c103161003000321441450b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 153930728 1250 153929478 153929497
    0x901080c2b0b01080a1b0b1806070f06050103050106060201020f0d0203070c2f0f01020a020405060102070f031a061801030318030b0702011d030f070201030b0d12050703030515150307140a0c020a0b0a08010b 90
    0x114205141d80cbc4a9030740301400c3c1ca10544900340d5600050090110030301503803020f007040340001d518240801c4440040c51080164010341244c1c0400800c1403148160189050b041e0070140061a5030303c100d058042e6514294030b04128030400d078095442c6410b098500e0940002d05030090002c1d202d20b0307001e01000c0c1c040107044a045024081c00403912034026600b0720051801894020407040503d605028500406445984180050500381d078900d4103180381e00f81525814070741510035601d1412009850001504003c0400702450b042020381c0c0c0e815071280c0304801c02489040d40c0807041440c072940300e2254606101117035100300b0512000d0750007900504803a410181150310800f04a45510007894054498100020000074800301810b501d40034840d080381d0328103201034190140c48001035903110407080c41c480b050800f100040e951800307401c1094030039414001050b59a08000c400410b103483c19101203105c2c04500e03402103103141c40b0000340e401380c1c0c82c251600400c503401c0c0b8403400619002611f10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 153931978 1250 153930728 153930739
    0x3050f010e04030828020c060606030c0301030f1a042d050d0f0c080a030b0907080906070807170403020105091212060120030f090901080c2b0b01080a1b0b18 69
    0x15404004204201701c03440c44644480180c648442190150401401500da00c0c8262014004e1002c01030f0800308170390450354008100400d00c03842d0302d099659403109101c10303424055907000f040144a0099080c001070078034540d500000d46d4884408030045007c4c0d62002c4d00075031110341282d00860042e000d250b0224079600b0107440003e02c603912200d0a9000090510003e0f4591008040d5801e2102405030001c02c1070401c040a403034031070400c41e5101c10043c204420270480b04081032416000341c2003a9280f0f070f08800c51a01078600b40c24040d01801098403107090611451000c45084040142035800da07038610340000b030203610750038011101c2c40043c600010b02405003445a401420041000789070f03909800b08000c1d1906140710400110f40016031010002e07401605030344046548141c80c50302040040004070342d02d020403c05098400000842c020018080d580c000704031908002420070009200700d1480c0c1211820700810100174003544202c0c00311040900060718008031041400c0c0014001420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 153933228 1250 153931978 153932011
    0x601020a11040c111c0e0105031909030c0f0f020a05040207030806041a0306070801091803050901030f0b0406171207170304020301090b131b180207020409020406031203050f010e040308 81
    0x5845003040203a00300c0500e900c408260400c0c685401c0703440e084406e202400c140e130039031800444180f03a00c50316440c4082d0301c580c0d819a050405014612403c502e07a007011307407844101458505240c7c1e071010710303600307a00c680c150000004080c5402d00885400c0ca5142d40c8084640e290441448050040088203050140c0e5488148989480130050756200b0103880e585c102d001d5250a440404840c64828103a6201d400e41041c40007185d008011100d0320b20083c83d0002d100d40381c5035803041c0240398840c00350307600030b080120000da1408100c50490500020030180c0e40c20724207603000411107118000000b00343c0c15401d0840c0d003203045c20314061680240060b0000c24007060594940c1c07145601103451525446002d10004140100840440b529884201c070240400c0e00307254800010840507005074020540009039802151995000f140b0750030340c007400910245480c0e01e0200c5400722050b15920000e481c7c400050b58210001400a04030f407441200c030340c0d054489840407102640300901c0c0151401c0d5084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 153934478 1250 153933228 153933257
    0x50606071e0b1e0705030c030c03070c02041803090f0e06090a0b0301020a1d090f061009080609010506090a02040501090603020f1306050a02010e06090601050d0f080d050f0601020a11040c 82
    0x142c9142c8100907a41d1101c0340710400c01c003c10161400130348000308118080c010000d440c110041102c1c1c21400c60b54180d03031280e580c560215406110400002c2d00316040003500e014610820000320206031181d100d4000341521a0045441d5020a200e0b102d0421000404070b406402d082c11243c0d006902040007107803225175880030909907031145c88034100040803030150500c05943c040c08194a040210350707413281c90a1207031410030381e050054001340c0304000301d20a50785054000c112020081c401c00741640c0c8680b80401c002c60007088104c07171140c041c11410002405020a5208030380560340f05848178180c26041c0340c000c900035000303c5024a0303a440104110010111518030b440d0081507585d03105540c0e4569064020b0940f92040e084030300d0307035011105003c0700080c0410024195001030b900340713030308449906000103003d40404015110003800038149208141d244c0003188a6500314080e003980b9201d8100480e500da00402d00078100701a207000c026410300d1700b5000400840d016180860511030f0342e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 153935728 1250 153934478 153934493
    0x230604032a0305100b0303030720150a06090c051213080702090a09050c0102300f030c0408071512090804050411070b0601180e0403090b0c011509050606071e 69
    0x5400684180d80710050441d0141c0d2136004204e0744410550242d811804c0c4074902824210320311030420f14413601001030484030f5104001c0240b4482e0300c5401036031641001da1100000f09980d0281560190419985066490040c41101c80300c1e2a651000c80481da42c0841c07900200840701c01c1180c851b8000c1110b48056503a05031058054081040006901e102500e0154604411401040d0640d000700c3c0c142c001101e0f0300c0c0c50700c80e420038518001c020b10207061681d54100303208101102c6074144021050011708401c4502910540e0501c00c221114a622130900c0c6d160180c800790250000f9021041d500d003d0900d58012424081c42500030506050316100080e0940d101e60034440c1e1100302c00302e105028000b17000100d540000782800c100012806109a00c00310040901419501d80a9100030800b0140314101000040141c0c1d01180c3d192101c40d00707054060036406942c40d40b10455100c000c6800881131142c10f02912008184914024090f078603462450030500d10340444d000480740110224001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 153936978 1250 153935728 153935813
    0x131b03080c0102030f01140f0d05120a02070609091407050901210b040f0507020303040210020a05150103060507020d09060c031107090203061c1709030c13050123060403 74
    0x705000981c0f00d00c2d024514000340c40050380900340888003000c04035101d481d03804004400100a032085035025034282421031511550000c130318403110300060304803212940415054281c4410b5a500b2450030f984120142c00d84619121b41b00c1180042400304003da8040d034020103030701c3d0043c10003460b078840340703112581081c09990b6030307102c41074a64001154a2825128542c084490f0320820010b80c1090440203550740801040280102c0c0c2c404900e2601c01d008000707500090740d200c401c45a403840c802808404440d070078442240e00e9400c1c40040b4070b00b140040f8140300c50240c96501c640c00301c1d1030000e049070000c81191044d0140034080c50101c0540001b4070464000d4000d0560140e03581c01e1410512400301110012044840d20030840b00c40001c0e43e0625040610300f410140584a009440000742800300f0040f9270380d8040700280c0c10041d01810b5401180c101c0d850311442003d110807500112402118030901668000b03070400c400e200050074058105044007081034813050380008a42d004504807807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 153938228 1250 153936978 153936997
    0x7020618010c060603050f0f0f03030c132301120b01080c090112150f050607080921060403080a0614030309120c0a1e05041815020c010213030b0c03131b0308 69
    0x3071f00c2030b2481c0c1001c000000d0040c1a2800800000042c50480ca03242d002c080d040c0200d1400000300309040000f003000c804003038240781c11080d007030500300e000420304440b0308606540803601e1210311244030006889103603100c65041e12001800c3d6502e5050800981c417400d14a4180554030070307050303010079403807040000300340b81e01c100b240e00c00307040200c00f0890000e1684800c1c030400003007007410000f5655606030f50703078401c0a403080b01d10282d180348000181c01c58801ca14505100b032004000c10305030300640b11806115040710030000141c850b0704888006038242001c640580c01040741c203c0c1420080c5621210310030840503505846501000500962600c0e8000d1100715407210350b20707003824041c04c11907009200171602002182c0c10b82c1480c4031005080f10001d0412008000031200081407601111702c80340006000315507a1548190588598000d0300080d103410301440001a400308901c4200d90180e415660005c4450302c00d41c0c1c0d604400f0800d000450440c0480d03400000c0007541c1e0780d020300082c24 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 153939478 1250 153938228 153938233
    0x412031d0c0906030601030c0e0a06030807030305060111070f0605030c0d060602100e061603240f030605010801020c0309061b06131103120415050720031207020618010c06060305 78
    0x9101c101000a8290003814a5119400c14401000000c2c84041e40c00c084030311500a001c4e0a45e00c07961800028482070f4000707050800001002401c2644c96880144100342c00d807035100280c9004c49070142e91b07030054040d004911300038417418088580500065984503140b110303201d00d01b252904002041d90401e03030140700581d0107003800805414003405820105103170600240071529240031072103408502c242c00750090603610075100c2122020040100340080161040005156850544c010364001500c00ac4d59018940000400d2040040c003c60380250200c02c010b6050514450803c00642d001c402d607070581450013001340d01c0c19282803091510880b102e00e241e4400301c40301e0810700c401400070304815120b5049502828031302c04080e400d507000d40700070a0155034038000118051b00d1300c0c80758000140c2552040320261103000700822000035441d000364195094154104007504a6000e5040e000354804000e01c088890034000341039030440014141340244049080c1d840312012954160010b50750358 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 153940728 1250 153939478 153939493
    0x906040503010e0a0b070e0f090a0e010c0207061103040b0d0510170c120d1710080a12170f0105151606050603120a05040e09071e0306180b0412031d 65
    0xa1034100e001d510806c0e0b070802c15540840c450000f00b5041440070320b5031150b01d03e1008160001950380c0043c4280305528002c010201e03800502a503609a68442d02c0b00192520105055809020050320201d80382e05501500b801e00690840c0042d11004000c5042e02d58481d00001d1226031950b004444810b4220240c110904c4450900c45e55000d4545803101703d50051806068a95001c124481c03170881d09205116551a0310580c0c40012000d07a100758280e10807141554184800042c404200c20721948490002c51001d101140c10204c0803a01414404510401009a4100070b82615104005902200d1404c000d519254a01c41402c41c01a65110f0343c40c410044103003002c00100200d41420710010741000c00342c10000340746125074018001070348000ca0100e00d04400c00c006040181c51000d0700401000c4155868503404850351205451040c1041d0003000341540f1241510083d0b5004010760754190741e96207600310b01040c1103d2850405d944d6810400d64003034000070b200c0c0000f0300e82000c3c0160 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 153941978 1250 153940728 153940733
    0xf0d020f031311040e0a03120e150f1e01210812060a050103060503100b04110703050c01060b0306010f110a0c0b070b160c0b04080f03191a0306010504020906040503010e0a 75
    0x8405100540200c4c0b9002a183c2840c0001a403030031620740c1840d01528030421f01034a600644221a20301d050ae20658050500f03505280740814070500c0030725581415942c03020018000d6080d840a4501d00220032001071210740c02d4044444240400082000e038450001c0c4e41e204030b65802204008400b00c048018043c041c942103000000500007403030107004140c10680081d4682102c02502000d46940c0c0310303a43d800752525004409284425055075465050504018080354402000c8103c15440e1030808035400e900c0c00140c07401848103a480d100ba180c1054420754004a901c10324801d41e00c1401443e40004042401d80c030082d01d01e07018520340ba0881031800c400d80090203880c80044100c02c81640000c56841100810080e0b0041e205840a440b079042014040c81071a01c04000a07000104000e02c80c00c11340c4200703a000d40d0210f0200403000d110030f81d049491030124030207a815040000100000c1c5000d801420b5140c030300500c403c1c6400d81c0d440003c0c0c00c40c1c1070280d85044030b80100e1444000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 153943228 1250 153941978 153941993
    0x12030310050d08130e010311121902040e03030702010b0108090a0f020618130c0905060717030709090f05010e07020a030909111b06010e0705130501050a05210421050f0d020f0313 78
    0x5072850302359008501d101ca1827440e039480d0f03219072180305014034441030701c0415507a80d90080f0195940b400c003070f29524181200000d029100c1d442005004c1041c1c003004c200300b03036400641410f2180c0c2150b031903894440141c1c208100380d070045505081003141100304011696400110400382c0c031000c840000e80c4418600b0250202c100744c0c0c0500d2040d0028805180440c00d5041b9001004400302810313a0780b03540c0c80c2030541302050190000304805281400300601000c003984542d043c1d42c14005004203c1e07403410022070791040b107008020001440300c50200251034542c1c001c019551640e482060910100c08006024054102d40004040e88090300410050b9a8035041a80100c154038295240030b013107a4003440c1c5201d00d4410241004000030b030102103a0707c00e0003610540004261524401c5082e0300d00c50320029010b42c0e041e81d01d10540c1601040810a03031440c1e1901c0e40054488508040840e03441c94825081401090380d0150200607554480710108015445186100780e0f515000c001c034200300d075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 153944478 1250 153943228 153943253
    0x70b130605090309060712110601090f0f090201050a08060a080f011e0504080a050d06180b030705030102033c01080f0607020d0503040210030906110912030310050d08130e0103 77
    0x10941d0410030513180262581011a120f803508003008210424151804a54500f1007041c03003481030207008004a24610150001d060040c50600244403461109042c80216040d06030000d01044040080c20159400f4000b259880940181f004850507034405956051509400407061140d56440000003120070481e02c14104480d6000104071610342a81d0b540c1c414441e10520005111000c141060002e1040d046940505460b00b034140c804c0781b460307a648000d8041020703454820702a401d400300d1030b400c052082e00e214030340c0e825170024030014490581e580c461202c1800405c030310b0611105051000203c400e68020035030840240f550310142000142003917000391400302190060011451010f038017109403a08140c040b10490602c103030380c5006400070400310700300900c80340c109564095103042d04005450540000e440c0301c8003440e51564400c1d240d10040754100503400c41c1d04014891410281400d15409100f032041a180100c1c0c400c10764038142455014100022680005001700070422140f030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 153945728 1250 153944478 153944491
    0xa02060a0902010903030c050304080d0c02030d08071d0d02040e0f0d0c0f0b0601030b030a081e03010b070609031710050a0b0a0e1201110c0c0103060e0c031b070b130605 74
    0x208550416607000905000c13840c4000740801025003240001d1080a0007102d0040021900b03d501c00c81d860000a011050464010780c441c5c05003007145020207014030b003107501c5001c03c2c0d40d5150346a0644011094101010142140c00c1a104a01840140c45612072180c5140c03400004080c210f4580d142c0c0340c94180c18158003002c0003003844200000450444603c0807095000b028a0000e95071000120300403d80440200e40c035106440030141030290b4503006003d0350004080c0c841115103601514889403000307105070219000100311100c04034482e980503150781e512901d0104a0f014000303400c61812f05058824135540c0c6031521003013002e8a80507200d28020500d000c1100d0403c9104280640442401d002d120f0058075400c0003001340e4130080d0702443d003038985240c01c191117183e5954826541c41d181032440d170110303290002c0071480180d544142c0d803003400903400f1549155a0403e480c007420103403483e15148018244103180c00520303800222841210500707550150700c929400d002c404e40e0381c043c244 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 153946978 1250 153945728 153945731
    0x30e0106180510060c02040b011e09090b030714060a05091302030a180809041e020406020105010821070f031704050102120f010f06050702150f0712021501181d030a02060a 75
    0x200135641d00514440072107034048600055a06490005a03a4150000d03020314042e491100e16212032078014100e00141c4034445400c0041d80352440500d55100050b01451400c00e10380c1e800c000140c5028001001c19000304e1400760304100f047c001050b0100c0864404100c12500401080070540181c8110007802828a40d56040d240c0c09880302c6095100b1040303860302584d201c9601c4100c4010003810501e0094617110304560700c60f07403100300038003c14003800303416514044e8411050100d10340508040b850780c82419806d03e402e00d5030391910304410410b4000c1b000c1c090000441d006a00d170f50390a241c82680100c00242c0d80b415840d442806040004180c0d9180c01110f03070040c0304106a645600d402c0e52013030f00704565102114000512800c01501000203d1000001c8682c02c0c50040c0020f880110f101d2140282d41ca1108601070361140340c0e0001844060b541c21004010040208003600441c1d80c0380d981c0021200c103200440011042c01808041259100169100c2003541c108a07a503488284d0250 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 153948228 1250 153946978 153947011
    0x160b09010603081c09171206090c03240a0b04030b0708040503030112170a030b130207050c0d0204201308010b0d140f0601080a02130b0a030210030e01061805 69
    0xa5914207405100b0a90030940c415104201058a240e48844034044d0496014403c0511b49900000307594410b41030006050114400300300d030750a2512903a80100510500b580c11a50b9100b507041c100c004841d5402d244840b03a0000d503885807150f41041000c1d21500c0c44555503103055003800c0828400140034801001002d01c20040410408000d590644010365105044185e241c2042c035a540340031280c1944040b00001c5410f41d10350160300c0300e860403000f40c501e0b007190090202c00e00100e00900002400d16084004806c42c6880c01814a8149910080c03002441d0041c041d440c000c04511502c0701c40300324800080170182c4d480008030078802825050000d101500e40040070807480c000d65540203120b02c03001445884145401e00101c0103d0354140e08039403c0c1e69403080d13139540d03580c04d844003139011300d0b810b100c1c03a505184107000c0c020039050080c024154051841d820302901640e0b003d0500205982c901d0203078000c58082c0254402883d01c0c00b80e8418444404501c030003111406032001030765858140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 153949478 1250 153948228 153948233
    0x151c0b010c0c05100c080d0b0109050108070e040903051207031517100209060708030405030301050117060306041b0801020d0b1302070c09150f030f0c08010e071217160b09010603 78
    0x210302d42540c0d02a035864a074112002400d4410b00340d6602c004049440101d00124143c101e58031488045000b40e88010f441503450006646038501070307481c400000c040d151421018201500003210003842440c1c9145403590110480400756000d8a0201c002a180c2d41e1403020f00030702e40c580313401402100e44030b807111240720700c12a80c4c1d0340c140c0060a90065008103400c0344560b5600f09450b4104d81001490390349141078a4404d071290f000340540e80c0401c00c040341c4c0f120100a410b03c428400c20f4003030000c001c00c4d155921401a254110b04600c101f01d541d241d40807680031020300280016161040c0040380300302c0980f0411141e00402890203005038414029903021400b080c1c0a541101c0d40c0c0c101c000381d440c001c0700b0030303244100c0d1540016405c0d4100c640c00004000b90a41240300c2e041c024410403907503645400306a401d8331030350010200194421041070043e401c6440b0380383d0380d003442000c108190205904118103950840b030350034503600303221440450510203002c0c60503034010a800002c02c03040b41141d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 153950728 1250 153949478 153949493
    0xf0d0f020f0627030a050106030b0103050d080118200c0d020c03060f0f090307050105010605040905060901260a14060103031214010311030a0b0f15060c03030705030402151c0b010c 79
    0x82e01c20903802d4a11401e09a13203040c400c1c1e4800c250881e00a1004c151039003401568104203110480e0248600d50f582911603200c1c00d1014143c0f504001ca6007407445c4091001c001500c4951941c03940d01c1d035040100c3c030120b608a0024000344460700041c00b40e601e80050042d0901c000412418002e42280c0200458001c072192080d600c6410300d542045242c1b10050014598043c6030302c028019881c0100206442c0d0304400900222503c1c0201405107540b007006202682c142846a113a45050b4905c1d0103424460708600d807072024441104661351140030b030b15295800000c903090001c00c1c0e0800030041c42403540c001c004c4801d000449c3d10501c0201c80340128080ca8139030520018266540700c10368410141e40034041510007607000b40e5001d8081c107140b040400c0381c4000b616018030070050268140d00e02d040c0326041e038502086805c0514150b9a03084829580c9600043c4126072000c402580c0c1004120184098581000b54803800c0121840610000c0f0860300307072444071411f003c0c00070b6240b000601c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 153951978 1250 153950728 153950767
    0x1216090b130c020712080318150601140c0a150b03060106020a1e12020601060e030712020409061404200108091c050c011e0605010806011d0f0d0f020f06 67
    0x150300000340c0e0302c072004000c0742460300c5074024a00003400440d840c0140070418010307600407a00d54861591016404000603030b24610710341c0780348110505e000001c11541c081c0301c1d810802c4214074912442d01c8840030b2600c2c100f1a800c00120f90b051810408214025410700c0b50444081080d00202580c0d414000040e603140c2030a10f0040c440a02c0060322445000d6925400d10420350000e0304039040f100c000c00103900c0380000d0040c40c0c00641d184e41007608910f40054460206c0e906200705412409454091001078690301c0000e42e03400d42c40c1c00c03814061411124002c1d01c501d0041c0708180070400080341ea01c4581c40ea403040c040c104240c44040c809407200203d164240081818901c0c02110f0b621303403083e103040c00381c446440d16035403034504ac03c81d03a80303100c040700015034100c2403080010f00d4035400195000318043d03079000d00148290381604004160203820b8440d00b0b10003440c01c0700310510a000500b0b030000300d800490309003184484500460a203411424542e010447d18142002d04050086d0310702c900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 153953228 1250 153951978 153952009
    0x506041401090504021329011821050f0312060a0312030f0e061306060b1602130b06030109020d1a0306130314040b0c060a060f050d0305091216090b 65
    0x15103101107402c5698401d00c103481406400001d02c0542000010003c5c142101f5060015807c2821001e4855600c00c0410300c0180340700c040c071420340c1030406054861154006880313002c10b1202e1001d900128000f001399220341008000216500c40048409800515002c1d01a901500c1f03140c0d810b1000840750481c1c0c80358a109860f00003408000b41c0060005442d800146010600800f01407210510b02040940703205401500e0a000719a9076140340511441084004c0214001601004005207000400c640101c12080c0022410098000000301540e000307a100d200e000f50f002945000441d81402100c072000c907000c05030f408207450440840c0e125080241061905001040e58000301809101c803500f03481546d034502c0351255115018000707a5803210301e5120307070743c85204c0014101e0f0000340207040035941c507403640745078807841d00c4240070700108006c0e4210103021041c4140e002c01c4c1c46942a01402c00c20260040c01c980000300c4404000e480142c10000c1c100703044c42e100e8a12074603803000e007000c50003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 153954478 1250 153953228 153953231
    0x31b0d030516021002060612240402030f030301060f091e031104290a0f15081504020a030906051303090e0c0f0c030306040507050307021e0709060810050604140109 72
    0x402c020000480182d8254000c0d401100d000f5401c1003141d0000c2d401e442070b0400d9901ca40180c4a0002d1140c0d640440400c0d40305e207a6034951160341c15011041c009405c5480a02200c2d140082c00c00300a00319002600f03c5800a503900701030043c40d9602425040040060355580141e004410048040e03403440c9000180a1006243c164962620303036612140b541134042d00c0c40302c146542440ea83d14004c4c401d81d501c61054200e900d0114600a5001c40c07402250108007280c00c40248003003055070410340007400e00a001000818440c025243d50006002011466400103428461441c1010880354040c1000407400312006142001035001303001c0707005403116504400c04a42c2c0c1c4a072103030003910607101400200140490640c01d0024000051406004211014401e540d980c0700708031081d0004941c078a0040c3c0c40140300701140c1404142200d400000d403c1a0750650761207140c00010b980f8961320500f1035900141845052888038400c1640003001100c5c18402d2070811440d00b0310740ca206014111026 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 153955728 1250 153954478 153954487
    0xd0302030c22050607083007120212010b07021003020c0a170c030f070b06030312190e0d0908010f05040503070b1003020405040f03020c0337050a0c05031b0d0305 71
    0x30a105885000200310041280b03560310050314084a00f9004605850307078100f507070b0040540d6906140040d0904440010342c401183d681c0510464030b00d040e40481c030000076403c0bc20040c3c0d02d0300545a80313010706494100150348850920501c4840054118484201403050094200800e008101c84003240c0d08003180c80003006e141e034010501c512880d082c0300102d100000d040010512000c2c090844540100c00340c0049583c0c92007419144c0c07080c41824440704801d0fa00040c000c0141c0c1a40000003281098001380d03c0310320010845c0303000003103440c00300415404d8504102403502402010101c641d1450240b2040c1002c0d50740503940d00a0040c020300d80421840007030700d40c0c20340c008171800a6070002c02c2440301c3c2c10a400c0c0042515443d1000707030f00501865001d4035a030b0038000390183c1b10000c10340300000000b144906640c02400a80c80c13100c40c00006503500004100104411101a8098204000c00030300d040101440c2015400021141040300889451148e07110442e00c40da458040c10030f160368 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 153956834 1106 153955728 153955777
    0x1201060f1a0901140c03090a0602010b0307060221031803030411090a050403080103080d0609090b0105091303081f0801090302010509190209180c060c010c020d0302030c 74
    0x1084c03d1031241101d8802140c010074580302e00d20160390030405540006803400740c8a501c00c0c1c0060391100c0034140e0754034082c0008801481d60780000c001000e409004c40040d6030102103a250411004000101030203c3d054420414554040c1580c0c1c0c0da180c00e250250186200040e1140282111400520910414442c841c040c40c0c00d9140d040c4a80e20795a14010203a100320030411042c3d0701c0d030200040b0001c081c020010090721a1228080a42c181814001c0d50080103009002c070484070101e26020a41002c911600708480000003c40104007205440040c041c1d81c0c08007032036601e0100380005255041d0705c194000d000401c140e4101c0c0031210026107140003104c001039800000742d001704119800c2110100c000d0449041524454520540003c0ca141c03c0f00e442100140d442e411030085d030603410f0081420a00032400d0860550809007104100c1d8081d0b00841d003441086000c81948 = true := by decide +kernel

theorem cover : BRFrame.Cov 153776978 153956834 := by
  have h0 := BRFrame.cov_init 153776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 153776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 153776978 ≤ n) (h2 : n < 153956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
