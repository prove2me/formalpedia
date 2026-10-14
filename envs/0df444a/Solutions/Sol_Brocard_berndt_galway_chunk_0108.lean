-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0108
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:53:05.015874+00:00
-- url     : https://prove2.me/submissions/a3abb045-7de6-4827-9b35-097a886e6c36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 19244610 ≤ n < 19424466 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 19245860 1250 19244610 19244627
    0x803060328120c02010f0c110a03050303060a080c010801030b0402010903080301170d02190204090f06180302010b03010c09050111010e030a1d0402030106020303040201050315060708090906010206010f0501030c030e0708030406 99
    0x2840e0803d203410442d15000644580901100d0100303002d0004a101d080103541c102c0d4000112006210442c07503034981c00c2490b070725001103802c42e000f01000c000206026000081d49081000c0503901d2045036030844e5114000600c014000301c0c103001d0600404400245000082d502901203058100707412803002c8401031400480048079815904040f030700000005081580548145d0140c0700410340c55054580120310b00842400501480d2600410415842032010692030640c000c1c0c1c02440309855650405007200d00d0100c3e9000824807041c0104082c0d40603101000007440c0d50400000c0030040c40400034110b5001c00d0300440000e1510b44500d0541101c1611500040815901141558100b43c0301075500d12000d080a8103004001c0000340b4064100c0c031103427100c04000b800c5a61110b01a20b44001c42d50042841d151103a150480014100d5100251140c100c0d000c4081c1071240f0f524120054008102c43c0c44d24004168841884040c0041c04101840c01803040c07000466480303103042001440c542 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 19247110 1250 19245860 19245893
    0xf12040210090302010206010b220303090810050f010303030504050109020315010519030510021b0708060105040f090b011403010204051f140c070b090612100302100e0105070803060328 81
    0x1140b8102807000d42d900041680c1501c01d407400095440b50203207204201d501c0c9407070350740c607000c0981040482010f91081100013122500011038400c040c0a50500c1c085d160f0032585001e24100320001080480c4c8250000b40d0804e0140000183c1e00750307a40c001c03e080864132641d0411a405100c0100018200040c1940010b40d41c61400f4002c0360070769880799200c15040b40b02d84000c85c3c000c545400d112250615060b65011a01d086448260f62020b06a403500000d104161103145410805c44540140b806401921a07022054504607070908060b19042103c100300e81e40c2540d0300780320109a40d00d403400300308543c8510710b100f21403a80d01c009004048400c0035140c0310680d001407020b401c0387d5030001203160039580c040c021203407901d503001d002c00e41d2805070308521441480c060080c03240c064403822160b000e40303000303582030b10b103070b160109054418980c2c40c03a0090000e4410461400401c908101540d0028002001d440e400005a020708003644041c8200c001d14a21800c644000c0005d0281441e4104c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 19248360 1250 19247110 19247117
    0xf020304050a020f010c0c120309051801090f0209060a0807030204090207030e1207030b041203090605180106050906060a030905010219020d090501081303030207050709050c12011e0b0703050f12040210 88
    0x20025074440074602c0e401c0c81031108d1408000c0a090401d80195203910140038040c2c4000c2c5103101e10360301114450802c0c42600b0b00076141011036904100c041c02107400300c580151080707241840c01e0008850b0550000c1560040543c244000318211145000a04100d40240d83c0d5a1066030300310200400c00e41e9000990006074049003003000042c000b10000355019420111502c216518510141c01801510300000c001502d40410414800707600d0f5501280c10014400821056840d40103004100d4010354540768400000e0041001682c400d800021001e0b20500001d401c228030300700380000b160400c0c02c0302405604100c1500d08107980c000c0c00c0e03400030802403030312680600f07004a010501c0d01804c0b5000e020150001003120611408012003c024501d010013004145404000c82c030080d08900d951403290344205000080030680c2c1000c19006081e41c2d401719000d645801e040311007a5101d40d83c202d0500000b8050081178070604405032240e55400f841d100401e00e8240304004e40d400f0440c0268090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 19249610 1250 19248360 19248377
    0x1806150507111f1b05030301030308090d0306030b180309150406080f0105100c02040e060906060a090212010902160803070525050618070506031608010e0108150a0f020304050a020f01 80
    0x900001440f40588054909001c03110a11040903840c03130b8214080081d104d844000000410542e000350090b2040c0252400d54080031452441102030f2002840013406c2014800b010407001c1c594000400c1d0303011420130843e86884011408070b80c01da050404100c4820380c02040070051540c001110517401201c07a00c2040096050000151440340030b20f004e2020440c1c1c000403030045481c1c903030015501039001000c84000f45811024250784100c00c480c200d005c1d01c1110400a403504245c001c3d1030b6214600c0303440d81c9890703003002003150003034000700c00f01c030450580301c0032050200d008180190b00070305144d80d0711555210941400107d080305000c17141021440d4001d1200850804110150445082050030004262408003c1d1a045654010300e82c454000014844405000c804056150b4069190203105030b0b030b21591071035080002d1054424079082145c000d484c08141174000c0da03000113603040c0043c0140b5480704110481e00101c1d0101c4055006801c2501946800002c6185100003440c04164 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 19250860 1250 19249610 19249639
    0x80f0a0c09050a0e0604060912050c07030f05030f1204050c0d02060304110f04020406030506040b0103090b01090c120501120302010e01051306050a02040e0405060708010602070609180615050711 85
    0x654551440741001d00c96071140850b0002d18036400c1007514039849070444c3c1e403600301428460010401e4410071960765010211425005010b03500f40c2d50810307000700241400c03610750340b600a0651400304003214140002c1040c2c01c4170001c03c40190207011032001080c0c2c840c1c58545002d500e00000030201171300c99800c1050000c0141da880c01104c3d4403a5012071090601180754010940d418440c0315203640c414004500854001c1e4035500035413281b0802c89050040c1d002d00c20065084580d6004050111801c01e001030111100d65000340241d00b503149048815000001c5080046803420703000080242400c0000e07805145c1c1c24040c081e403c08140c07000308800e007050740134940d14641d540b038014403a90320744000411401d02076055070f0050000c40e225510514080c500151035450445281010034540000800d20500c00640242550001d848081080e170402c089405a145200c90b4040c005450b00c0e40407032240943c42d103556400c00280c50ba5a21868149010030011070303000300450241e9041c0c070780c0782c6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 19252110 1250 19250860 19250873
    0x31a01050a03080f09011206120201030b040203010e04021e030706050c1b010f030c050d0c05031902090d0206090d020d050d090e0603030a030504030903080c060f06040203131407030f0c080f0a 84
    0x11400c0d80d456805a5440c140d1800603102500e141c1500c040d51f900e000000121500707404c01110f18030b4401d0340d0400404c03940300c003044101d01081c004c0c101c010a00d4400036005042c41d10035000c0145c02030701c040d462091241d002038900500f0750011800038001162041e03a0038002c0000610208545119454000d40342d80001d15000f2079034051401c041d150025012903901a408407180c14041c0f603801e02c0341c40100c03480640503510980d441240036186c43c0160300508814400d6503030a0800404801c1080140c1d001c100b900d40115000341c0e4010590015640181c0d02c05017030101c2103104001070118001c03c1e24004d418904290300c000c40c1402c5803000c000b0681d82c08400c4130440145410001000d455508089444042a80009255000010361301d0369241c4002041c4d0b2103020400a801c4290344c4003414082a40400d4550001c1024924103110004082102c209468021300080b1a202566926040c2e8200c000c4102035502c220f0040040c000d50310300b801514034040b0100014035803002642d4414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 19253360 1250 19252110 19252117
    0x1d030705060c031b160c0e0106020a0b0606090301141f050102120307030b030303010602010e070f1d0601020c04110c060105010c0b040803060103021b011b080c04060c0f060204031a01050a0308 84
    0x2020ba0060000004d140071004007010131000000441407130b00d5841c49000c11003030400101059500700079050700007628801c070540744c606907030b041d901900d049a0180d454110300800905110752080082c4000c0703040741c40902c40d1a0740070b45c02c141401e0142c240a4141814a001d2041003c500a00002c00380b1169030000340114100c0e225011060380c96480000031801021003181c02360741400000000148140d054005001401089082d169410f960364400405ca031442e10810502d6540150703425080c8030700d4154158003100600644090706880030010307084404010b50014000d002091650b0040810014540902803c1c00c1007486184c43e51240c00c2d440d03000400c0204031f404000001985c90744a5015940058030f2407142046001c1440e841300d018080132510341204410104601c0c0c1058810224039025619100000745042e08051045030314440c0454240d8401da0850b02103c00209180300410045010301010300e0018440f40040c00c64901c1a48018442c03440704138280041801355045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 19254610 1250 19253360 19253371
    0x417090a03081303060908040f0b03011a0a0909050a06030501050f04020d0209070c0b070c031e1407051207060516020109050303060405040201020f06040506061201020403151e0207061d03070506 85
    0x2d6071035140b094149100c0f40d034550801020941003900500c2000703200c1d0060826111715060b1440e4041c0c0700d031411201400300344501500e1040c040d074002200d40d24803004204110a6150081c240d40d00d07661940305541d001d40d441d0031000c2e920101003050080c20f01c6095088402030460740b900b82030a80010b40c500b203449070040d00c02d69580c130102d60001e0003014180d0855a201d00c15080510b800d00300640305640e140d90a4021448895800300005002450581c81186171307181c070084104014400100340c0c01c0000300725018462901c901c0910310800c13018056403440740c0804559440d202c1c0c4009440d880018a0105580c1411246000600c01005413a8400d2003900c2c0003d503a5501d000407458416060640c1c8200c0c01200c00340414014081003161050344251201c5402110b0016030034201d21603844043c041144500d520040c521607078010403000da005d90640e151500011030030300e049920101741121955030394200e000081d9900408a4103600c54807001d1400e1850741c3e240c06441e003500424 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 19255860 1250 19254610 19254623
    0x405030c1912050307030807020604170a03020f2709010e0103060c0306031b06090611060a05061f020601061d061209010e030d0b0a090e1902010203041d0417090a03 72
    0x40e09a00d03900c01c00d1072100140000d0460030590802c50608949070380c400803017580050000000103290b00d0000580718080c85e070251401c004c1064100049074031742c0001c50070100b01074080004a03001816140074041801c00c082040e21240c4003040403482e585c012207000340c0502c8071400100300003070041400504480d040100410b15040240c1c08800800503600000d103030103074503a103880c040089030040100341e80d0540c860450090303c90b103040d120f4820381c1035248150380c0210000780307007000290015038000d107000c0c0c00c48a80001b004240703c80003481c80321080042e405034004101e00ca501030401c280e299141515219500946030128009120340305141d0b041034110808109084000d6114644404407032051340d8940483c0048100507220780444507100d00c101c050040360781541485128400340030100103210503000303244000920720360000b060381940400e02c000108484035104018401c00c00000e103000c2c920345464582041074a0f411030824800003031042100035140c4071306040c00c2d240c2002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 19257110 1250 19255860 19255879
    0xc0420070f02040207080703120510080a03050c01090b010303050a08060a0b040303030207020f040f02092409090403020703060f0606020f0106030308280609020306030607050c070311010309050601080c0f060405030c 94
    0x1040c06803040c0100200413100002d01c0d00c048c5a0700c246280d540c100034103414400b07074070b03038055658032807401d4001da003a16042000c4080000f0f00070b100510f42c041003900081200c050304d89800d03886210076070069002c83c40c001841d0340c144c4d034400c07510350b4400c80803101c0300041400c10043c4d038141c0c09103000060500d90300080c004c05540c0c9aa549606482c0010405c0c80800b078840412b1002e9080b81c0302c2c16000c0d2143c001c14800c02084c43d464010441c40c01d441003804c1107502410084000c00240c0f055007503014070040840400c1d0300f4055205061114200803940b030f072902900902e4401c00003255051a49003030001d000095014102c0c03601301ea0094000d000702c110560003401c4400b2003142c19041c0e41c0ca81b510000d145400e50b0003941c800c040407002d032042e40d81c0d41035050311035201d800b070301c02c080360826501400002e0410750800c91440061400044843c03a0740d5038540790032030a800283d8540d0114130321200700d1814a040c0d09484105491f21410a46860301280d950039517910154441c0300c411 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 19258360 1250 19257110 19257113
    0x1806022113030302010c0306060203031302060702010519090e0f06030703110103061806050307050a15050a0c05060703051f0e0a02070201030e030a05040501090b0408061506040503010606020c0420070f 88
    0x20007a81e818405401d0100c84a03030b41d0b403070040d0013441000e88000100f07003071181c0040c100c2d0011058910540040c058600c0c0000c050b4200140e90b070100004906019052081e140340700160941d10300140090784070341803410300b4050500c000c000001e20120803100e0200400c241500c02050501c12a03900a608540402901c030041e000b510303081d00010300000321103084ca02c03c60025040002200c1098003603442140e00d40c400e01041201c075014000b816014040102c00e1184105c3c01004000c420f46815101450242d40d50f0f400e0490a07034040f40004c1e1901d060045984003d0110b401245490894024661402542ca102ca240082c60300300200d83c0800c0c50420b69000360011039111404c4010f40c0da1f1a0f41e83c146c0a49250040c0c0078850010b403a6a0340861107048800c00c1300c0a50300400010b0955030399064440280c180e644030150341100003408000b426860900510000d0034040e006401c5540c6002c0511045410042c0c2048a420140c21212041694102101d40c00f40c2c101c45043d103441002d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 19259610 1250 19258360 19258423
    0x30f01050d151a1201050103170306030319140705060604060b0306030a020405060a0902040e07030b0604061407030309060c030204090e0c0906150708030709080d0801181a03060901020901180602 85
    0xe48000a40008004c00750041d040e0341075101a060b03a10032640317021114101030790000d55000403910540c1540c000c2160004000c0c20b42e5219148018900d001000c0b0640410b042485070002081201c00c1c3d44a0000c2c080f4516007405400003519500803883d0445c0740c101d00180d80c501d10100064000e56030f4402241050702e070b04144034090001c0200a5584940d04c620700d0a00c040120f40000c0000d140454081d90fa280130f01c11181100c07a96501c952081d5050a60034405510040c4105d0902d0b030344811880004259010f46070025660340c40040e02d952070000402d06503000403103840a01d41003241910160fa64000000350014410740e000c1000300007216034240140b00340c081c003915100000c41042546035120741c0040c1a60f07070f00f4050303800b8250300442c15a0780c0242806400142c40d007210400c1514a41c5500c004140c0303125950710002c00c03500c6804282880000d03202d05405035000160b0120650304038450f0101060048001c010852800b400203490360400003084c4205060b03000f0003241c4400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 19260860 1250 19259610 19259651
    0x3040302030f0307030f0206040b01060e030a020a0b09130e1209010215040507060e0102010c080123060403051005060d050d030513060c0809010507021501120606030c0605030f01050d15 81
    0xd025048031604800d074082c2d140d03242c01140c02200000c42e041c410f0805240301240d44c90246a010301c07181b0869080100c207039100e0703c603400b62540602ca0040b40c040541e40b8007802400404013100151382c0c0c2c4078814140503515403c03803009800c00b420b040f0088070078180022a0003990f40c0c6054800d80390581140101d051034107081d0401641e40380d14050005022002c101241112000d46514000035000001a401e039000340d20760002084a2000400c50a031103032221003064401006085030825481000404540103078009960591042000000c00d000c507208560700031030101e914014201c1c2a079101603a869204555008060b151804a45081852a20084e003954010f8052020722250080100810421110407000d5800c2101041213a4004a00c0303101e108080a480c0e40d46a007040c0c5050b205802c1200c0c2204c3c2c45680b0040000441c401c8100c8201810a41d0703120782d5682813034a42c1010080040e004244118100040c1034005405c14141c100c11840b1410041856920000740400240 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 19262110 1250 19260860 19260863
    0x2090103020f0409020d05011a030406050711070e0f090f0709090f02040c0c0201080a05010501090b0304080c061312021504240c110f0106060e2404090605040e011406060705030403 79
    0xc5002c1408030309280780c0c0e000351084c1d8850320701c00c01c40c7d41e83e00d54030615948814603000b80403160420109000c91880c2c0c005941c811700a040440d80107100c0401d080c50540f481d4003070a500700c242820f008503001c0030011580c01107180c44c0101000310411040648800d12841140c038003555079002c000402c6045102844000d40061040141ca80308482c0030700412a031440490001d48410001600701c0d54078480c0505070b61069603443d5100e4282a0b034240c8580c8081c00641c0e00380f0041c880f03002418003c2060600c21840c07900b00014070406850b005007100203024022066403c040b100d00c500400d1908000c0d8019080040341d640c0301102504050042503003000c078000d00c0d041c290016081c54100d0360400003020030320126801c01b0400b600d268200e0b4041e000b040001040c10840300c80c2e5240801e607001100e40000090400011280b180b440c1940c07090b400258043c3c0c07079a4040209181c40e208022861400c0c000900c0300540c01018524003580040ca13151190790081041c50600204105480285 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 19263360 1250 19262110 19262137
    0xf0c0f06050f0609040503040b0a030213030c0609060804051c030e1203060a0f030f0b040503270907020c010f031806051003050c030703050a02041a19080c0d020d02040209010302 78
    0x10026030402001400e0210760880240c280d500c0400c203942440d030f00d040d1155400a002d5400e140c00e2800c040c501c1e0b0701015040c000c054003030068550600410304000c005510843c0c050350110302d010006446100030b42d10420038000c0007000c11010810200f50603c01e111011000d04040e081c10300250004e03c4884046440340c420700301210341d50440a0011340c015401103406d00c00e250f58440d180800c141c110702000f001c042c950f17008240001c5403000e00c19001445401a039003000d501040005031101551780004c3e40c11a10740421a060410f0707a903c5411502600c05091840e80078030010780301025000001040560f142c11035580742c0b103042e006040f00b503070001050105003090501e20a4100e4140000c3c0d41c9805070141d104a10314001401ca0112a0320030041c1418020743c1c1c003084000c1400c05094000564903000036402c07940c0320400d0350408941d82c00600c600c1800e16044a2516400740140e6020f1303003501c869000540d4032a03203442c101070380c100c03809a524007000300100c0c00790184100c840e041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 19264610 1250 19263360 19263383
    0x30c09090c0909050901090503090625050106050f01050301060206040308040501150602030706150f031704090203070309031d030307080304060e0d110105100e15040605030303070302091905100f0c 86
    0xc655002000b0001c43e070600c803003449540c071107000843c2283c0d00c0720001040c43c1e10800440c98541003450103041e030f84c440d10003954515031129100002c582078041046135181d548840603c8180341868003074042580038030703180f4150341c1862006035454801400190030300c400d100c00101086001d4221015020955a402034500e40e100d00c060740d6900a54002c032802800d2201501070000001c4403801110350700c214130078280f40386407205001020b60030030350103a61008000110700302c0f850b0b000442c010b01540c0c2e000944d00c1c0b618180140303d0540e0308080007104a8619203145103035800030075500010b8104e0f030800c0d52500c40c4d00d448401841103c1003c1102d000d08144500c8441d00411a4132003094080700a002c03555035141e0401500201d0301840c10100414070104598040441c00584065405840020040e48900000345541c00c06c90382c10700040d400042405050500c5481204a241142408668681000009500001e85002c080c0c200010304440e0300038a4464245480380035000551980d9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 19265860 1250 19264610 19264631
    0x20d02040b0d1e0309080313060503090703020a121a1006050901030204080f06090601080303060a0b0c21090f0d05100506011e0306170a030e0105030901090209010f050906190501030c0909 82
    0x1041c543c0301d0001e401041d1a07000000f0740d602d0100848840703810121f00c40c0701d0f42e802d1a1058030383da04090401d0100d4401d421001c80180c0f9044e228501610441e141c0c00410710640c40c080303201c2840f1252034041c2c00d8030030082c0452401402846420b843c40c9041443e100c0c540007004070000d014640c0501040e00c1545290500f40c030002c10954050103102c1d042e40e005a0300d483d2155500d100664850342c0100004104005124141029048130039840c0b050b030f02040044000c2815a00c0440811040c03c2d0000544540c0c07890b0003501c0d0001400d0a4542c0104020b41e91607036070300e65101c0c46450500588400c00209030b60300c1103040f0004007001c20003070555440307000310040092a9600500303500c00341003001059a0400001d06590060f41980da40054600c1040115100d420141000d0110342d280c000b0540160344810801c0d019004240400301454036040030400301501c09000c240c01001d104c1c01e80b8241c01030390800345098503002e003400715030f56201c0503046404688941c8050f6405240003441d04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 19267110 1250 19265860 19265903
    0xf180f0a050f0f060f0a0306020a02060709080a03020a02040b0a0b0f03090c04060e16090909030210060b040b07080f160803060406053307020315160804020d02040b0d 73
    0x140a21408a82005541d464a6032180944402c3c3c070300880d80076803030001484500e030580c500c02d00ea80000e403403220420790b80c0d42d90606a800400c01078001d038100c0d1b0104031800383e02140d444000c12010f00104000001514003940f0f510890f00064055a180c210390081502c03411140c20041022050040c0d940c4150252400180c0094951074201d01800d00418600c0c9481e0140800341d40300800440803949517000c015088071149140b03a818400000400510740341d40c2c3c2f0510369040c0c008e4003c0c148030001180c24408a0b015601700c61000c40b01403209102c044034801c15a803000b0b910502c42c9584440d4808034500c0341c02081d004c92005c0d94281c62281c20428080007031030040030180c2d41400010b13200c10810420402c95162040400b00b0049104901501071000e009417a18011903945440c40395000310381804c02d4062065810303d441d10502808042e141c048441034a018a003c101500f026400a01d0807102001c5c0030744103603280c0307802c901c007035035600384000459521084d86000c0d0000d001068 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 19268360 1250 19267110 19267141
    0x31e04030308010902070305030f040f0c0f03060f050106050403030f02031c06080f0a020f0105072102030703081006051206180a1b03050c040302010804050f010203090714060a0e0f18 80
    0x440010b0180000000c0d201050300070340b18040e0385905c0303050070340d03840c0040015412401001039071520812260103020603000312041001d4662262421021421410080d040e604001007050700309203032100400c8001d41c421b01351001d890341403400240c2c881043c04100d00e1742c0903440300b02c07010012000c0c4c04501c0d4405540454101c1d40ea12081d034500c1800c4d64132003912050b44210182d002410722606c0c92803588100003c0003440e110745100803e60b88114104000102202c40200c050ba00c001010304c14960001c3d030459024006000d0440003605101d4024250b01450246500c000000004503010360f5075080b15440000140103800402d00e8201c0407030020303103003080b41d0261503024554424082c6100c2c4c01280d1050007142c20b020320b0146541c0c01140c054600900943d254001e087d003050b00704800780025405458820000c0800b9410f01c1f2402d040424000a0300f88194020421114069004a40c2009030101180e001d010403042002007950329511030240380c14280154104840205401c0700e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 19269610 1250 19268360 19268363
    0x70f030605010e09010e090f0319020c030a1e0c090203040c050a06022407030209030307030e040c05030603250f090504170705100f11030f0f06100e060309031e0403 72
    0x1400115550700040d1110364424038030319041840040140203008440b140317940c000c0411022102d14100c4046e1050554014410307000c811100381141c05440d13a4108840b504c2200c01701d0141c9811921556800c58a07840182d1505a18200000302c8041c003000e40a030034010981d203170b025940c038605490f00c115880c0d404c2c041c0740c2c031039502250003103040b03880024141000c0b10f40c1c5580311840c0801c04107921200718002c0041080507001c02c04140340da1001d2020303082151007a240e1003000240d203001c00085c0e510100380e0504200050007004410795000079003440e4044112092042e144401c80c4228811400740c000e60301710056042e000a000445a20075841240074044a010a25015190b140c079841907120242c03050340964001000e191550b440310001240d40f060000d86101d004003da0600d81003101c40c58106c0d4000c4d01007294041a0180c0c0035070106080300c92400b801e4103070720068000c1501e100703464042c510100006000c840c0c204101c41128500600d0000105c0d40078070300e260141d206000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 19270860 1250 19269610 19269617
    0x1120f03020c0d1110110a02010309050f03040b0d0c0503061005071703070c03021203010602030f1c06090204030203010e010507020304062304030b100f0503031e0d0609020306100504050f060c0a0506070f 89
    0xc00030360f400c0c4601106c0c0c0085450300003800c0c11094680045002c2c042c580016a40d9014004980d2800b41c007c00080c8001c2240060503030319098040c401f2400c840d1042f885a0600c0070130410403209644400c290619200c1034107090b9140d0445040841a043e40e0090b985100c100020078010b04580160711041d00c984264200c5d941a102c07180c0d403a01c940020302c550405a48144135074400c025520700031b448011030501400002d83c1841c200f51040d500141d1003401d64560001e024415400c0078028140b0a0180b400244050304103601c5c02540c9110318460402086a00040000b88c10090480403100c100704034140c0d510317a84c8a042c10101b20340d044d03583e41c145401881000502003202c0c000c6208540c1e00401441c28409501e07801070b160b4182c101c00b01040d1404002110441d912440340001401c841000144c807031804c0420300003d81c5800700d00c1801e10a00303100812480d0384454440c5030b248415070340c441e202c030251001c862401d0121798008040380120410030010319403047c18620010955503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 19272110 1250 19270860 19270879
    0x5060307080a0c170f0106060306050f0301020304030c06021b0a0b01060306080d050301090c050405030a050705040c03020c120702210f120f09040e1e060609010e01120f03020c0d11 79
    0x3107040d0b580d503141000502804a0032002c001e0002903d113081425003000f001c1da511880100549800c5445680050002c2943e810041c44181040c0d154010050002c0d8001c614604198a0281810115210081caa150002503040380600d003010b014550240050032103d400c03a061a10340c1034000c003406240300007407800305c1c00600d882001aa44a05410a880b5a03207076034240440c04024000300b8020b1010702604001c001216201048900c401ca0301600c082d11445042030200420764810300b13440c030101401408001e007400c2020a401641900c003011186e690301451000c6080c0500484040007005400510f4201c07040001c41c00c800303000465420f5070350344040130300c0c00c400031301032001500160034060284a101c2c0c10140c0c000f0890042e0740084a038207030485424070030314034031017280401c00390868000d010f52410302501c40303030140940d44540c003115810402c2803148566902c03000340600a002016406145c02803004501c01d000c080c2c03402e85022071034188581d40b0145401d55034014600748 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 19273360 1250 19272110 19272119
    0xa0f0e060409230717030c0709020306010e01030b0310090503030403140316080405070806010609231f030204080607030501030b0a0c02060601050901031401090504051207050309060c0309030d020105060307 90
    0x511a9520b101d500ca80480706566883c03240002070041610900c01c184a45a40030501a40c00807048451503484401150b03034003c40d0a0700c0e070402d00c40d03500c005840e60050045c045181c0e003205808240301000e01c6c000a192007070000103481c000c00c0d0110580158501903c4100344100440203507c00e034001e444a101c4589221100c041511007152801c60b10030b07071410f4218680384108503054115005000712507400f5140d4601c81c0c00c0c520280d01c92004201e04010411554a9940a40101c10340c2604407075004280d020210302c0280035a045007000c044120302e03d81044e40294191406045c081040ba5072038030345880050000c000a0006071840080c030000a40d60140d207004145040c8555800760a075501d44600540c0c07a41c00ca580014141500d4248800000502001d840d000f0900d50002080b14206030428038109940c400000c18400ca0402211002c15400022a0b1803c0d8007900d980e50746420311032455055001d03044000741e25008203182003201640c150002401008120141e07000c9969030f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 19274610 1250 19273360 19273369
    0x2041203031d0a0b1b0d0c030e070e060a1502030c0a030503010e0a020c070506030a0e0f01230103030e09040305070b0405010506010e0d1502070602070b04080a080f070e041a0a0f0e06 80
    0x1c480050042044c000003450520101c1d90350440186011501818084150500381c2914100c2c090240000ea1380c00c05180c0183c030811903240107184d1005609002c0c1445804502d000000317004a01d040c4483c200c3c03007034099100b00700300c4001c1c034880019240000001d1030020555402845814001d40d000008100020a0742c821071f03c451002c4002400118640014003006810081544201642e9000007118030502406034075403207039850000107400c0a0580e50340c40b104404ca0505122030303c0716070050002941040c0345030b002d220201d031141c9a503030704c5240c02c440070300ca801ba000300700c0c1d15040c003400100241500841c0c0207400989941512480e00010b001c41d10351000c0d405440d003c4072881c4100394860704c0e801086528041d5030003500e0600d8a482d000c03140e060544044628480000c0c1c80c0190580c0b02d0040e5420009000c848542d500302490f0040407400e106000c6441103598850882e044401c83c40300a51380c0c07a01401224045540e42c00c0404001c115100f1940c01d000c00700c0016406141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 19275860 1250 19274610 19274623
    0x606060f090f041e020310060809070e13020a060f02100213061d04150608061f0807110d05040303020c0907021203090a020a0314010c0201090b0a020d02041203031d 72
    0x11003001420110100c04001c1100c9070b502c2e400380c000c1d507101c034010001441040408100380407414056940d06000d0071803014440c569200c0404c01400c03400b4020040e5000c111441116178880c6000120348500140750000c0040e054006d600c20103620000074056000390001c41c49078019000e882030110310002c031030203900c60003401d601c104000810602c5442e0190110000700c2d071211400c081884010380c0450b0450b40350000381040c54041401c1003007041c1d80451107a40c8450280c1d0040d1a1800c1c024040355140712040002c400c0c05040740c00281400d10421760780a00801c480b044610780031642c03e01a005500070f010540050007a0403801070181002c044c190701600d0755074010126120300ca011002c09070000703800c103400d500404c61500b02582c1d0b000c4681b00654000d030f0350745414064007642103084460300329604040d6410715401e075002c100303001541e550045c0803a00240e6280074050148000341b04035007202e103a8031895040070042c941e160388000e603445061080d1000800c082200c0565541 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 19277110 1250 19275860 19275877
    0xe01020c01120e10020f03040219080307030c0515070906020c0a030503090f030f030309150a0b030c011407020a0305070602060f01150e0a050d0609020405131505130b040b0108060606 80
    0x1c0c440c010b0b16070110398550011036561452002d40e05683c00d181c0b1850180c1c1e01110f00e0068000c004010b002c194a0114212a6050300030b41c11001c50b10310300140e0355100d00819078080c041c032440f4014001840014030800040c0c002c00c5d1980030480c83d20400290640b9034502a0000520420710b511082d0300b41105d244068a4012000794105000c8408100300c0d00b1071340181d141c0500450001e846084c03401c00182d80600800390140040c1c40ca14a0190046403006110601460400511565a031000301d520003c4010030701e0f200446007418444808680304807600203400180f0040000140600420b4180903500726a00f83ca445407642c0070b601c4d8003114207010390011101d40300ca00c0304280c0e0240001088822024098801540da5a0000780c40070519070000c1e201c06885804150845c90144940c0c0d0b8031103c00758012168a026441d003622000110340300c1218160340b0004035046000103c840c00c0c400740e00c9102500390703180c140381c90300000c1001e1003404240d1041d1401b080c203502c0c01500f501c0611 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 19278360 1250 19277110 19277117
    0x604020a08061005040e010305010212150603070c020105041203020715030603021005030601020709020c1020040e040c0801060303020a060b0901030305070b071e0903050c0405151e0405070905010e01020c01 90
    0x82d01c462041242040c0c0c1e1800140a0113801c0200260b058030b41103030203000b0350180000603121400741c40e48814140300185002d51340d1381041a8160301e03a80740b200b580d0700442c140c504040350070300901c01039a051140303070401048001006000070406a00040840036200c91013801d9003c410080001c4c1c064942c0c5000080d403280c0000403031125984100082d503800032052044482540d075845070b2408036401454901040c1c1c002104011400100e40102c010745140884030380c290300042005011140a1400360365280e00540c0041740034458441c10010207440c151000300b003c240c0c1c0c0e290107940e45d503019a040301c1d15802c241d100d910324a04045154101c80e00340e1166854030110b540e4000110000414100500c41646444114001d42074101c05540c4560b469142107641182410b51a00c042c10301c50601c12800c22007080340085810380b49041000041d50b003452070110400c06000000082d2452070703005860074082100d4194032101c40c204076202a2030b9910340c5d4040800490b1291204d50340d05010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 19279610 1250 19278360 19278377
    0xb13060e12060c070809090708090f0f0304090e010b06030c03010e0c070201020703020402070807050d050c100203060d0609080d02070b0a06050405090a02010503100810050a051602100b2110050604020a 88
    0x1c40c030090002c00c94540b1495205e440c203d040000039400800c10b0780d208001803018810002842020400022540d107810000c10301247d60141d205e540740b0490003040400c5480f00710410040e48250090001c1a03402420240c0b64a0181200c0030380c0d8000b441a0340c1008110408101c2d8000d8010032615841e40690141403041c1c11902888060350090754101c60f0138404110f1903010800520010943e4145655440e0359948201c070190302d040d0700b06500e103542602c10800d0103c41d0f5151000c034079904d5800716011400c0c0ea4a41000d5040b80104142844030034000940030b400c101050003090700c2018003034410131000f9241c04c07d0000b15001180c66600ba64840b110100c055130041002c0c41e48026600780495206031a0303281181401844410182010307201c1090091900807030091a60140c60b00009a090010710340000313660740b003010460f03201c0d60341c1c848445c090b54462400000e50061b00c036045882014111540725504c00312508040012482c0c0000b04003145894003c50f00300001c1c03544c4003c00e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 19280860 1250 19279610 19279621
    0x30b150105040308091509060c060403030c05180f0303130906050a0f0501020618100e0102030405060105091303080702010b060319050603010204051509180709090b010924090b13060e1206 82
    0x10700c070340880d60000c100e038400d000e071201c0780c0e662300010407440c0849405440b060810303103005019075a2400000e41400418405800b5140e0160011038070900201d40c0f60003046980ca0200381188541e400b0002503a80400012030130305660341241044400070745603240b0440c1c2d94165440c0039941405154010780041c03000c2140c40074031080610007160f83c4801c0d11103882c807281622044400c160154080c80e500031040009000d07091011030700500040d40c0d5034000785429945036090840caa00010180007490007ca54681c0c400d5104044208005e8102a660300301000001c135404514203118030740c1410600007400c5030034180284d604689028145e007521510407480715210750014800d150b000744156080a460b80043c0b0010341c020b2240d0342364408010b0810303e01c40107440d01013400f00d0520101640c00c201401c600c1001480030340d01d02000d140b1000c44c0410031075400c0303e1079010713a00000004c58015605480d0902d91320441e40c2d10b4035008411641c100c288401300244d61740845664001500090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 19282110 1250 19280860 19280869
    0x6190c0906121d0706090f030302031c0e010504080306120d05041404020909010303030506100c03080411030a0c03060608070e040c050607051002040909030809060603060103170f04030b15010504030809 88
    0x40364001c14010070f0803502161500080d60004542030321590100c0d8007000303540d80002001010b40060781030707005a0f90035600d000e50327039100f0b00c03c04120120195085000001c025408105914a11802800741f41807909200306650803d5402e14450b00009000e078114030400206001c082c00300792a0241003a1401ea00c481c00ea501030225190019000c101548003aa43c64000d00d010350f11030303280045c071810054203208904001c1e90011051281d07442001000c46e411030500d6911551000e60328005070903160100341408020300000389542d0108502108104a41c0c02c03907010750320508202c0d506a6aa0a000415403009440c00b40803003160705800d101e1381c00d04000800b10b1500440484912021498640d0120703485640516401c96540004104140d406100c45400410782c000038a000d04086002a8860b141803000502c40c8036010004954080c40905071440d01d00101d940302d072120358908140040000407034180803214005081d10f000ca600590650301501d40080043c0e0511500c0010701 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 19283360 1250 19282110 19282127
    0x2030a0207290c0106060201060506120a021e07030e100c08070f0606050a0b090333090c03011a03010506090c070b06010509040c0e13020f0708070213090506190c0906 73
    0x240c05590700200908100b1010041c40b0303c038650700001074114608000203086a1003500000d108070380400ca00310382ca060001e1620f810610301c010050343c907600031091a14078608034500c4a2032080c00308400f018141c11141c48181201c01b40c1c0c0d0741c100c0085c41ca8046882d43c41c110001050b044052002201041202d1950404a4400d48000500d60b84400010b200144030f80e01c0480c0410b0000303007800c41c5080600092921060000c019400c0710500c4003e024038220030400f48011416820000318522410811458800300180c020044520b002d02c1000352005441c00e41340c00b039806c11000c20428101038894602c80e140d0340d03241600700b008564820401c0d25001d0400f504000381402f1030500796845220703c0c1c40c001541c1d110560403a4461040c00745102941c920214803900c1031033100080c8000800b103400d06540020040e40c0c1c0e0f030b200d2001500f421036000c0c44048403441c0c00c0350941000000103801d0b010f603002500d000c16034a5216880c0b0291f4108540380000124031400030400c2c0c0d8001e0500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 19284610 1250 19283360 19283399
    0x306060d110d02030609030304290c0a1806090801050c030c090904030903080409050117010c0f0e0d0602040e091203040507091e05040b01060306050d020906010f0c06020a051902030a0207 82
    0x2202c1c0c6030980341c0029180034001d9406440b13036040041803008018103c4803460b600c0d4140303000e00b181103540c65850000414014441d40824a001030071a00c070038480d4001d94a044402008010381d40c0c2c03213042c02070002d00303140541c210350340c40c160214207803071901c101b03132480350a41c001c202c1d140681c0c0000340841548080c0048003400296000480007840100103000a0282d0242c005030a41c9801480c80754419444400051a4909420354134266030103000c1001d4112503041600c2ca42c54404041511014560350140440d0310104e0007140584000200b13134000c5605004070341150080b07001c40c4490b403005540007400d650000d00708114440c202d07004040001c40d2403c0101e079400031811160b081c0c900c01c880440307240d800b00340103103c083d81500c2400050002a035182e090690540d011451014028003854103100c01d04405191480c402c221005226901034015901d80b100308201038240d81042418040641200346041c11880c400015110030a5059006100103480d114038108412003c5d050b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 19285860 1250 19284610 19284619
    0x10e0a031707020906010c02090f090304120f110a23040e0a0302060403020d0e01051e07080c070504270b091606081902030705030c0307090314030307030b0306060d11 73
    0x40000810509403244411401e0301940716a80e900d00e1041144101c1d00500d07881c1030005a410744000340c2c482186842d440901c14036214103a03200c2071030b4146140a613520100d940e1150144203000c1050038154040e0701845200c428040b50306541c200b00c081c02082c01090300045040661641d0011140404001401d01070000140d40040c085442c0c03e004030710a0540259020b030303051104251b410040c030130101a84c0d2502c02c01030040140020301da40b042c400c1c0c6a0128140c0d4040b800400c0555046401040e40951103aa550040340c20a0f03449010078071a1612070342c42e01038001d103800014900e11444c86c0f030039092403440944551ba40e801d00e0401519409140c41605074200c210b51070711040300050121921040703058648112480080311001000206e024014003e0100094105090b00d8101e10015050340e1070ba07480c1c81080b144100d41c0d90000d0700001c0b810209a14080000c8001e40c000d05040d80c5c1400100c52000034142d440340e0540381260480c02404842d00810284202032654183c01017 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 19287110 1250 19285860 19285879
    0x6030a080a0309230705030f03070803181c030b010c0c05041503020604090e0f0a0507030f050f01060303050a08090f0706030902040b03060403020c01021009020f090a090c090e10110306010e 83
    0x110f980c150ba01900a6400340c1340b0303150b080d46034504010400760000344001c81c0180788001014680310703128020b034803006103255804408102030007003501c3d20300b2030a541507080f241e0440b4400c070600c580e0b4414400b40c1011030f10305980c0c200694481c1c58008225038020303420404c41380c684402c1c8001040c0b03044201b51522900710001c0010380d00c1c1d0005200400d5400c07408208601501c80003400c0caa0011000303c140da00481520380001c00128896003241d0704100540090b03440742c24500e0808600c076418070211b5203020004001c158008000e083d400b440e0790756150340c541c0da00e0103080c1da8042c1f81e01415203687c4018070410000d8443e0f0008800740384040c001041e05c070700c8000800d140c41d809460860250700441c00b00c010950303040000310b403031081c0144e040c005145940c0124a282d68030b20041030040119000140c288a1643c00500d1001e62001041c0f2107903a40381840001001c141141000368002c034036a07804001c5ea070b40031301d091340441049040c0c6180c8407100151a8507100c10996a04009240d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 19288360 1250 19287110 19287113
    0x38100c021f0e041d0111070c030b0403050d020a12060509040203070b0d0b06070c0603150e0402040506040209060c06150303040f17010908030f010303090504060e070c0309081605030607050306030a080a0309 90
    0x14014444100d0a070444c102010765000035803400d403030500c60300d0503505c00300f40300c00c030080b45000e0180c3c02200d8004c001550b4540300c60908649500c1800c08417104107000103000140d01d0350015844902521100d4100b0190340c0f02e004100b49404155400380d4150b01c075040a000e43c0c20004010000d0a0500d4400a060504603020542c00e411041040d60110388800c030030000036130140102d44928907103000c1040258205590800c00c8035010340040d0066a98078001125611503074101e603e1480014101a22241401d00c0c0d036a881d03404a68045c9002c6034805420b40070308001090382c0540d0206011240780c00d0902120300740800086007a12050b40d01da94000d008038406030b000394014186020403205030347c1981006001c480e0a503100901461070031600b004250140408143c002440303251500c103c109a003400c072083c040d04d80043c2c40901642e03115040207200c1d2000002210820b4060728000d1b9114502980c02c0d0004803165501900000005da0024984800034524681740c0c2c1000102001c45 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 19289610 1250 19288360 19288369
    0x4060b0d0e0c15030a050606030c0a1b021507050c1207060c02060d020f040e09030f0307030507030f0e0c010806030a2102030708130305010b040501030c060338100c021f0e 75
    0x103404484009074000020710080c01c00c17038001d40e43c1c8039009594541c9903052811010300031340b00e0402482c0070092804641185141d140210411040e001051804d14000e00701c40b4020720307070000c001150f070740c400c000e00083c00e41001c80260592909190180c085903203062800d44001c0704000c3c01701e0b44124200100010080f8600c007502103407410544041e1603d081070303148000c90b44c0182050102e940240500c400c840144c0040301c0c3c0c030402030714000c9420b840d802400e4001d015081c140ca25031501b08880440701203000a8030b10f005071000d0741c175021aa120748080c9030b01c1e442c12000241c400c584840e404d01e42c07410b07855032881000d9070501c1200d18144a03612080d1594218040b03143c080c4003003540070001c0c01403d018045081c50100d40801155140d6514000c00c50502d21440c02415100d82c1c02501c1c07a117441b000e11b0007800407101201c2d42012202680d001c0b000080d00305904c11100038001900302071041c041c00042c541e0181804401600d07121508009000c0c1d400080c08212130f050840100d5100e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 19290860 1250 19289610 19289629
    0x180c080c0d0c0e0607051e07080601032003070b0c12030c07030302090d0b040b0103020a08010c090501030b01090f09050f010e070f0507020a1e05040e0f06060f030102130f0305070504060b0d0e0c 85
    0x3030006008840014440c03202c0c030f14410540081f00c0d0348160070a0040b14004140c190440740d01240032180c0321102c0d80a0281710f958590b030785500d4011410005001503004000309198241c0005450380f010207110400c0c034500040d121007240340d2040c4123200009000303a00509040400070209540e2200310354840030f503204202c50854030301549000420450408000220260000c80c00a00001047c0140207188641c039200f018100340c2c840080600c607034061213440003e094030030003548060b0707168050040904416100d0140000766440002520400c000c0718a00880c41d6640e464180d8400134401c560079042140701b03aa000506410004015040a1a9140d40642045101202e5141c82d08000441300700d001515810782021070030001c1081c0c04140c03a40d05c1354084803e051b10f0010794001c2402030003001c0c603064003440c1094002c6514400070885100f00c1c3d114004031103d0139101e0060209490080c40b549600b0901480102454649600131490100e112012115030882d0740300014103054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 19292110 1250 19290860 19290863
    0xc010b0d05100507030903170601180e0f06010207030302030706020904020f0a030f0e030309070b03040503040e070801030606080d1407050c060d0207020405010e040507030213020c01020301180c080c0d0c0e0607 92
    0x9008050584040d262800342980c4a54242410010031b100d0b500c2c09003900c10743c0481c1846004d00c60000401c160300817200b41d140180ca0b40070601ba400d89a1b09944a4000160796940d2641007100024003258800909041030b00d81c0756000c0c504280603503a981001c0d4000e01101580a134007806080000b0340003d000e8041e16003250740224140d4009200d000c01c40300352101642c100d400400401600c514002070105c01c541c5141080b983c0d07555a0304000d4150f0085811044003e07034044144007080e980500d0a60607203006000400045c1e5540044076a86c03215014070101007502501c0c40040710103044060050340380508103607800d00404e000000c100d0b40c0f2a9803144002940401c040c4290b0405206541c0500180400141a0b0030640ca4903584d5261030f10000f40308414165224001d1a07071901541d060a0044000f55240d50311819403c00c81c85502d01b002a10624190407440c803140708111950144600400207440c000032564800b01130641c545030202030210340d40300000e41c0c0e01c03180c0003000703240d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 19293360 1250 19292110 19292113
    0x109060203060f0f0a060e030102090607061b1e0305040f020406081b06090f040504051908030103060c051201051002070f0b03010e010e011508100510110c0105041a0c010b0d05 77
    0x286403400030440d803c82821603803801034651505103116910742e00e110400340c480c0307403c0c181d00c814038070f200107400380c0b040d044100e810400100d500c0c8100309242d04030011076102c180b010550100440070868001d010034000c107140004846c2c400075000d0180c0d002d590000e010b503036002d2068100f03401250a40c3c441d58440301e89503008081d0707040c41408911b00b145420b101140c0725860904050001892240900044d40c811503a0b0804981009070400100d02c120380400101780002c50b4034149041700c1e0b00240300c20b584007424045000e640b1307481034080303441225141d02040001d13400d00303040c008400c07400c00050065103d05c010200d05110901440401000c4407074405540390704003004441c6001060b407004024485000061145003030b0b41008400407156850141026600e100039840701038400c6d80241d80044075a15200c00c0e89601080490791100c49000300d40b440301001d00119400c0c8180d100300e00c0e92250782031026182ca81460020030400c26200c002103140344a2100007101009070145c00c0303856 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 19294610 1250 19293360 19293367
    0xb010c0b10060201050604090201020304033201060617061c030201020c100b040606020105070215100b03040605071e020a0206030406060b0427060501050906030423010b03010b030a0f03050f090301090602 89
    0x60f42400f600350300040640b0240038030190703a40040c0d9240668000108a0651451f10103aa0851005030002d241c805c2040c007040403850002c014000e00b50390040c440020503104050807a220b12243c3c09019040c054000b031164840e01c845c0400241d12010100e0855408010100307000504008051800f03031710100009043e034000d0104421600d80f903000c4d50079039040c502004502500414064550b01c0c1603640e15505513591224078100070041e4201c4000c064010080c4010300500c0d9020900c070f6140c5445494002c1440707180c2c418060501100080180d01c0408904018103084000c0d54000c0e116480120318030342c81d010845461b400c942c1108100c1c00e09641c08001e5049900900c200040000c60704110036801d0000080c114441c1d9039245010b400008085020041c1c06400c0c50702622514541c10300303045901841601802006507100d202e5030070038146450520300441d08410981e8403003002c081d04500c964041c0c0d171942101d18510496007040c80b407482991420300898825910032800141d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 19295860 1250 19294610 19294619
    0xe04062309010303050313080403170421051b0f0a03030c02011806050304110111010504031e03060e0610090803040b0703090803031e090109080c030904050702030c0703060b010c0b10 80
    0x9004418a03952040280a0040001c03c0d0820102ea4100b0354021130f031003c4100a05210382d403031003154001004030110840354150307408458081e10983d0002c550340866002c08800d19104850907040140440c0c1190100072100e11021042e03000103003010301030325443e2500000027540e00e0391f02c2e40705801103000001c0305021036900c0820103210324a150285200c0c28200f09004265000040c00181083c0030410202010b0b07003c7e02600b082560315070003d12442c03420340b80091000207060b155039031078152101800c29550090251605684074180511200c1e91040204880545280030400610460400108403460240002e0018154030100c403540c81c071130752400908c01c9109600407a8a07030402c2c0709010640c03401103045590308008511000c1e440c0c4a00030440d00404090788001d0a44800080c3c072040700c9408006000f6100e4102c0b0204078680d05c05000760f80f80c0c400c0388000300550300303c1003042c0009003443c1d021200c40303c1c040c500007018201640c0d4190b40004195103040040e10200f00410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 19297110 1250 19295860 19295909
    0x3010b070318080d0804020103020f030a1515050d0203150a08010c021603050a1b080f100e0705011b05010f020a030b090106090f06081801140405060f06061206010e0406 74
    0x1440071002c2c01e10340e445185448080c3e074a410503502c0030000c0115020201d41960f10a80680c6d50200606034825500d080120500000b02000900308030020380c65000000d12010000d238511002119440d0940350481000d55040251700040000301c0c90b8408159075903040c2c4030703042c1810192000800006000004030780c00382c68521790b030360010354440c055601400045c1021503e04a02540100306002d0400880300c4d856040b4000c0d00402c3c081d1089204031400b0303403000038460014040019003080490002c601250f01c61046010f128081100d01030f41084d103601700d40c00464058084e600000d0003903001401d02d01640c0c0b207100180d000075140c1030300b04140c2c036103980342600400307644c10045035003483d09070840d80b000400c5c45040e040c460031500103551510700080e1140401e4150000300b00d680e2a0000070341c0d2180e001c0e14140d4a0780305490000705907a80c4030542a0180000801003404c10b50000c641300008040108610304212482a1241568641d4050040a0503001000d80c3e0442a60802e01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 19298360 1250 19297110 19297127
    0x9031e0706050c04030c0b0703030e160e010905060303030412030e030d020304150614060c120403050a050d02010b01021203040326070f02060402100c050a05060106050a0e0415050f0406090203010b0703 88
    0xa140f80502000100001140044004101c4104500407600c444550a00350000c03c0036502c0c2c480070b0b004015200c2402d20f0f2004410003911100c0c0e6000c040390f42ca032219502103950840d5040d4166200300301050110700705945400d01e6510526000c18141480d061041c20741e0402c90752400940d0f000320a00c01000f4001000600700c4011003000c11189181001001c01020360442076405000001000b105950701408000301602c00b0104069036155240362072a910343e2601403e60b0b860044240480340684180a90000e05505a0080881c00d000b00108a295800a8401c40520001c04c02100140c084011400440c05242d202c0c6002d511380560007412010080700150111341062003003100580d030b170703002c0c10184115900d021102000a49000c5290240100b0040e229102d07140001691aa01c5401000ba0604a54600d0983d080f020140400d03030301c5016001450f82e210280034040c60034800c0308152010341c01000440c2c096903440850302264800e0300801581c5a002a030309081c980c00c8100c2c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 19299610 1250 19298360 19298371
    0x5010f05030c0306070513031a0402100f020c0105030717040302100c0c0201170403021e0d14070807060c2c03120405030717101415090106120509031e070605 69
    0x142c00809103010010b074903500c009101d4810b114004c40c45114100d600802d4101560b80b0005031080d020100e03071109050310307085408a01c41e200c462213800c802845071821140800c0aa0001d141c5490134000558040d040100203401301702c041c80007000b4101100103154001c500940103441c0800003070310b820007526500030220040c080d83c240d4090043c0d03840860440c04440c58400001c09403107520b01282051540b20705040000151419080c1040c1702141d84a00faa4154480883c50207500401400364020140050074007401800010049075460700b001e880320038280341c2043d25880901c008104820140300340c80b44400c0135103d01295090030841d24070f85403011a010b03400c203850000060760350881c0340650386010710140c0040151450410080c0c1000101c00024840000c41d11540c0100390700885144100d1032a0030302c1d82040d400d090719a035068402c1c59499000107815200302c803020780400b400b4610307248801c00c1a41d000800001628525401d40f000e066651030b42802c000c0140c8401404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 19300860 1250 19299610 19299613
    0x30c050408030403020d0809030a231506040507140a03060e0603060103021507050a06060e070f0305040803060f03030903010903020105010513020405010c02090a140108010c1b0b061903140105010f0503 88
    0x8203114007500003080d20102ca50440f500c552001071850100401e01951aa441c2c06220700200c100c00c103d284c032036070000c9858031702402d4034011303250460f641c4d980152090071320103c01e1680899a6404c058204581c449452b050180d94024144400d140d240d02100341400000da0764503090240c1c1421580c050780201c0114000c04082d4150780010f00a00c501c5210215103080c0043c1000070040117001041015403c9141004610fa681d14244ca07182411183c030000210b0410301e12481e18040c0c481c490240d03400003800760556540380144500ca185d501d0b04164140b0007481a00815a4240a0413602c18400d0f800032525514000030300504010300c0b0081c03a006401804148801d90b484103c17200c209404443c40e0301c9542318400b01000a281302c6120060b42c00c0e0034800400d40010540103851142c0040c0d99121640d40b5100b264044515001c000514071314091001c20028604080c00d43c070402d8406841110f0b02e40d4950f02e403920002440b820f081142d4440b0010040b0315480c0b520a0000c020a90 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 19302110 1250 19300860 19300867
    0x2010c0804020f01031508070801020910020109030815040f0e03040e07020f0d030506010e04090b04110a0308030109050912030103140c040c0f03050405030c030c16050f03060708070e04090f03030c05 87
    0x1400604400f00a46031141015581c1c4040c0c04081107015540e8003c2540200b40c1d0001522040076502035400695024094080307120341c1d5860038414464400c05c250542d9410403661640058450a42a6180c1c00355200303859003191540d001191040c4e40086118500139640c80c4d25200301c00d4034250000b0324850030354101100f841c000340e4011030044000d030803034030340010719980740720069503400c0b094100700350414601a03c6c0010003690224090103a401204c0c8048040d0705a01081224201c0f400b0081061b001480100301c401a69045149c03c1885001512825001c8400750145078000341d00a45240700e075440c0c00c040340354090006a00c3c61768140d409019512103000041c10307440c02c22142c2c03410181e54200041c14008284151151411248196995070b05500d045a5031603407142d04c0300b0349228010b9000203917458017040f0740310030301f1001d4003800c1c05980710300d010f0f41c0041004061170203200c0c1c41d003001152a07495202d22051035110340e000f070424210300d050080403601150210340c00e100041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 19303360 1250 19302110 19302113
    0x2130605011403060d0f080307080610020705060c01060e0408030f010501080f011502070504020a09050111010c0c08030a06080303010b03041104050103031b0f08030703061703030103020901090e0313031202010c0804 94
    0x2d00c2404546481d103820b296652111004148400040d40c009480071580d00c4035141002041402103000c1c100b03598401d5055240c02082001508040780e00e6405031b80608000c05c4682041009003408080040000850030350703911008204031001c0b141141d02d02c2000041183c200031f080c04042c090082881d05100f145040c03940440134502c10300904842105025a4801c181c0c030810650000c0c00f0007070403c0d515500314020140010009010705030124a612040041c550381c140f00f0603180022039583d43c1a0f541407070301c1e8440d01d513202900c0e40b1201c2d0b44503000440c0c2c0000c200011402001c0306841e103071b50f0b4030701070030702403501044100154442d0b402c0400401c042035100807400035200b0440d0141108020394035000441000950005010001c08020801c2064056001200302c60007503115400351142a11540e44134402400002c0d4040b05050040c0040303207140c4e100c40108000b4004680c5007510304070720aa054800c6a000f2580a0100e4115100440d428010340200740c20030f060241007400d01e13 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 19304610 1250 19303360 19303367
    0x90b0702060c070609080d0f020901110a23030d06030308040332030604090b01030c030c080a030f030b0406180b040e010204060503010e0403020a1406072307030309080405100503040213060501 84
    0x4090000c0c10564480507080701b84a4024111851400d01c2103040060104440404000c0c0d08600d824a0110708000c0d40c1d0603940c0e034007251941143c0e0b40400c082014044072081019480a080c103042602d05c82801840c50083c924031a002c0918000c0e1266001c62803e0300d002801d030300454205480c3d8250440380100101c00c14241030481040603038445440e580c40707102140040000d00b00107802540b07080c00010901c9101400c03681924041c0590420030340d00e410100d81e55040300500200051a88040d680641c0d2007503201c0c46407030500420101c0d080ba41d4080800340c2c0c82045241034603465507003030b03070340464035040c401c40701076200e0b090003907082074900341000c0c0c1940014403d248444840c800080c040500c00e0003c0b000c104c1d40030000a540d4200c0d140c0e44c6503219001c0b82e0708000f254004001d94a00701714000a0b03400003090f0310000d4a040150ba4046020742102d8034212200002484041030542e078140c8586000c145540e1180c1e00d03464180100844000c3c43e03041c51082e41d2901800b807016913403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 19305860 1250 19304610 19304617
    0x201050a12021e030402030c0d020907080408070c030510050a0605060d02070c0801111801020304030c0302120a060e01020a0201060b030105030c011d0301020304030e0f01090f120c080d03090b0702060c 88
    0x1801e06012030101c0400700303480040d228549611160403980c43c240f0f403074510300d64065405980280d0440f410100518180502c00359040300207540105031000080ba41e03031061a03019401885880e09a00780245691142400c00e0340d900115510b800628680c60500d44910696500541c02d183c14801c107807038000030031800d1281eaa039141c0d126400182030002d000c503400b418802003d01000805c0781039055009110705030028411550300710301098200005610000a07035060b01d42040600c1c3c0315600c0d507402c0169200c0c541d01ca9050309d01417010720001103951441510001c070011400565a1318064000030708403001600071440c00c400c24001845651800288510362103428200241100074416160308410264045181d1540c00001004100750b1300c15440c0910500a4800303010041d031070340c01514005064090000d0180b140482040340344000103040e000c05000301300340320071030351a07a001c03601303203904c03c0700c5003012a40b11a0b6100402c241451120742c08a1184050000341c01d052450801e58030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 19307110 1250 19305860 19305877
    0x3103031407080a020f130609030b010f030c050405070216090617061b070807050105010603020904060504020a020604080a0e09010f0f08030a050723250512100203040303090c080601030c06030603020105 88
    0x151302081d0104100010011110008854a02000f0744c2c1e989600c0201407010701e000407502c4c0200f0030000202001c1700920181980e41c0180214295400c10f0184002060014201d02c04c512401350001c0d940070358a5140300c0039208001000c0f424608003141c101c00303400c12045450255100c2401c0000204100c3c0382109103d02410303103e0354680c441d091180443c042c016014199510b480000203100713405500030a8010f10998084c00b440707540d030040008038000c1004040250b00701900085c00180100000c0c24541c40030304161521031440b03008134080308402d0304046825121404244040441880c0f000f00030f0500318021881c02030f2180004203c3d00030f001008003c03890407040001048102c0b070b2240c418040d45422504a913082d4100c103140003e8030f1040d4141000104c2002c101418203003044801d9006031401041804054041c420081d40700801c10f904042c0cbd141080800114600002c030014101c0c900200851350450802010507400d40d803246080c10720700801000140d1b040780a07182c100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 19308360 1250 19307110 19307131
    0x70b250224060303040b0315040c05070803040f020111010903050304020f0907020a03080910020d29010914030109060507080403170114041505060a02030d060906060504030b310303140708 82
    0xe44850003c64554001d940013290750707000104c10004070f0f1038040203000b000001250b05002019030f070b1000751241d00c1552400340c2401d00800004c7c000c110951000400e0903c10714144460b524000e40d03180c21540c2d4444220000f40700001403005514084060040300c400407a4020035504140741d029580d0082e0303640003018010240b00160740ba0f6024001c0702c0f40100400c0c4199a604c1803007401034010300b541812a40b004c2d05001043e0041107210301d00d5481c16074180c50716400c0c1030821700400400d034a600452a4150f40b074805520000c2c1081c00f031240200d00d10b8803400c030142840e18000c0d248031014070808803513105443c010420790540d2240c401c1c00d05400d840000b011107100c98400c4a461090708066044480094001501a40000108001459034400700241d41d240e036290004d40c5c030103110301d4000075802d203c18004201c855000c0ca4015050303c0700034900ea608940306c1d80c01d0400c8000009403030144456800d0505406028800030441010070050f001d103032015024000b83d00141562005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 19309610 1250 19308360 19308433
    0xb0306060d030c0b28050f01050d06020c0d0804021309030e010e030a020d12120b030304050f01050d0f09060b041404061505060f071a040c120206070b2502 68
    0x1810f00646a0040c07041c1c002d400031050f86046044c680d11202d142420b0110400184118401000d080c81814001c0d90800d0b100c0c8200d0340303410f0400103419105c80b42618000e50070032000200107010404a40040b403180c0320008146894010015080303a1010440c80b0681058440380010740d0002c941007500c2d400b400c1481924001c10b001c0380c80c0a101a9000307410055000109040c45851054102c4002960341d0f0444480907840e140b1094036042050b16030158010300003404280b030440601d80741103a041c500300e0f017804098180c00e0140e68081200e031400c0c036034658a000134000c09000300e05030341c1020b5806124a096004250741e40301c0006001a01155546842241c0c040e5000d60044c01820001d2025885140007190044203510007c1c01702c40b003140d002103201824000b000d8042c800c03900000d0580d845807400601c050307607400205080f43d1000081006000084200d4015401b500071002e050f000c8605074460303041e1042c110032850742954408140d01481c0d0a002d0050031003001e6034a41c5500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 19310860 1250 19309610 19309613
    0x90403110f060a0c0e01080f09160e07020d0f1706030f030403030206090705030106050904030c08040b030a0b0a050402031005060906040e0c030708010f030201171503010204080d030f0b0306060d 85
    0x55124240c1220030980c0120405030307200e103800240503400ba12044504011020440d40e064550680d03007010140803600443c005403030754181c1d4543c2940080000c080d03504030040c5400310400c8841030740040041c6402241400410b80e8100100c1d0013210782030420346013841c9411409404062001c0c07203031050741c221400040483d2010704c018080c00c11240c0490f5251031700c030314019441e408116215840e0784503030900002c1070318050040d241190b5014049881c1600d880e1000ca4003c641d001041e07401100c20040001d590590100862061421107070018140c1c1061007003003042c1c0c0e9298000d0b4483c500610610004140c3c040000041fa01c00325442d0b5580c00110001c80c41d140510360004580343e40c1502041035520540c001075114400c559200305080e078072426003408061590001900041945410103010300040b440c881e0080b2511030300b003030920141000682607903c0764220038055002801c40c491201d400d8066940c411180d45000d00941c103010010030b90300da400400c1d0b680f042c66030010110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 19312110 1250 19310860 19310867
    0xf12040303140106020a1406010506040303050c01060e01030b010302090702060c0406050a03090606060305040c080708030f030601031e020c0724030207022106060915090106030b030708030711010206100303080402090403 96
    0x2c6801c0001c060a101907941e800080d40300e9440d94810b40c0c003450980c1c2c3d900b2403030901240c554141c55006090034105030031510102e40d550844202030030150341c1c0394404540300c0b100c07071411030096120f6a8003c00541c1984117205a030340d00907007050f0540d4480d1040c403040081000c1960b0969030f1510b00245c0725014920120007620040e034010741014601000840c01e540e15821003031045003c2d180c8034038032607500d011030355070780c002442580c2440d0024085002000d500c00c0096400080500d40407a0000303031f81c10035424001c0039034031b540d0950746e0014040504000920041e8000c01c6280109100117007180f40071012048062035050030180e00240d40701c215a01c10000780e010050b0380b014091040300d00785070540d0743e40c0f050b18482d200d07a00b00170020790594450107100c2000d0b58094410240d50346018003c7e0042c14041264981c14007403143d011622460070005000840c2c0601e0ba080b07000600f1500290500700c0180c00c0c016910300064090010941140c0415001a81076400e80420398440c1400c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 19313360 1250 19312110 19312121
    0x801030b100f080c120708120706020705010c02010e07080a0203061305010212090d030f05040f0b070504180209150306152803050709090b0d03030f02070206190909020f12040303 78
    0x41d51042c160580104104000003500071070142e00fa12034000c140302d2507100d0356031441c4a01c240c1c400307a4000c1c0080310b045c0d402c181c0075010051281d2005414202240c0d40c090070b451801107030200503952a40c04003680c5000b041000001c0c0340003400b0780360135800d83e00030a48401d4000c0c20390131090350f8441d01c2400c02a0035411207802004400e012400c0c0d06014100944503030a08000300b00207070030881601818240c83c49580e00842d40018041c00449443c0d440074010300c0000c0c03800c800c1c13207018007002500c04404006015000c440c8031005a441034414200030624004041898041c08140100700198803207690150b0100260041c860b10f4403000c10b40c0c072a8015900404202100844a2094007240c04d500941d010315510380301c02d8021501e074401041241c196588031640003880a01d982c001c41d01942c40000341c169001405840c0580b2034003c19042d038040100000f4600d09842401034050380200309201404003d601545442c1203100c01030618003680c80f10328200b030b800134040b0b01018060fa105 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 19314610 1250 19313360 19313369
    0x5030a1a0a052b0305030907060206190903020c040501091e05040206070f050111190f020a0809040b060f04080c100c05030d0b130905030d060617010b0f0d05010305010522030801030b10 81
    0xf01d0965106140041c071030740080c1c840090030b10940340003048042c0045030851041c0d1a40c40c0429414280400d2030004d001d0381030060301036000d08001d5031080d03156802614041c041114012a0044908003001013580000c0000802c1c2c82ca41024080142e4407501100c888980040f0b580300041030508017a401840a00c11000142900040b81d0084101103420794901801c640c40c2c1030300c1c640070500300340d0301d0744c02001c00280040c8041080300709500e0a544490b042c50b0000e01520304101880e50048030f00d52058202000d143c1c010314565a15150a0130404900c1c011443d00d882d030b20a0030f03580c1c0355880c0038010031045e0041c0c503980f00802039180d40c0102003c45144010a106144e5a800d180751240d0101b013000038014100038002c110180100c2c850001c0d140c1548050f1650381c6013106ca10f0706a0003000d81031a00c1c140030045601c1301402401101e000c0d40c00741c03000044d40c0c200240190380700303100c07081c0d107006061112214401203a000f151450444c7d410800c2c4070403941c0c81c41890604814103410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 19315860 1250 19314610 19314679
    0x5030919090c0c0308090f0a080f040504150306110406140306060909040b01050102010606050c030304080306040b15040602010501060c020d02040b0102030d0212010f080a0b0c160602040605030a1a0a05 88
    0x1105503a5482a000c0e419540242c03134070525500c0d1b12801c4c0341ca451065862418903803080e001c0a0004051030000c120490400350b0b00c0d8101030302e40c2e0001d0141c4090346403500c96581c080e0ba090040c000c161090040041061080c02c1c50710340f80010142c0f00340390b45125500e92a0001c00001c034a6150300703084902d07a460003000400b15151920700194051030a00032107005610305140400e038503011784107c1d2030903038803c0011800d6507030390ba41c0d482c0d655000411250300291a224030200903220221203071525104090b102e5100d50400c40003d003129030580c4114108800c2c070f000c42000d81c031580c03051881147c065a0200d82d02c202e40313005034954401d03064a8802513100003058006400741c00149410380303141c07110051186070b40c0c4843d2981c0f4010f841001c0c040d18941000301701c8424400300188884042d142d0501c1c140c41d0385803118012a00154803c00c0820800400c0020306440c034810f101c2102514074009500c0540c60b008143d141090307010301402120707544441e200350200318001d124481810700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 19317110 1250 19315860 19315871
    0xc0f02150304061d030a0c111801030503030a0e010501140402070c05060d0606030b030f030a0c05070e0106050406120c0212130308040305010c14030906070507021f09081006030503091909 82
    0x203842001441a0024000b13004065801c0c40d03e0715a001c400c41e44c40020a0752541c060103040d44030010314035002c0c3c58036540103691070074060060041c00901c5000f140508099a03c0740361200401040e2007001c07841691903403400d4018805a003c164601c041007130b0686005031079540510340141964150b8200550213071003c116045417554507003045080d64469602880b41030b5246041c1592422000c0c420ba885400c144034490000380b040e529010010700550403a810155503035a02c02d007000d406e801c1000007171400201481610b41205407010a985420400c2000b0404c41030020b45a0285142c1d1800161002400b14051810b02160304050342c1c001d4186c1d0303519075a03407410600920031080c00c40081000c09043d44440001901a41d204451042c098426075031780c1e42080f24558803520701240c2c48083d0132040c646104a4171014884200f80d521007968072410060018a0038480c040109140d41c1003c1092001423404403c0da107000e4070545500400e611400400000181c15400c2406500c1c03505 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 19318360 1250 19317110 19317113
    0x9190b04060522061d060f01091116151119050307050403150e0111041203230d0605090c040f0b0f0c0a05010507080a09020609010f09080a05060f010e070c0f02150304 73
    0x1d43c0a414080504922801000480c94211b900e0381000c546141440d1400c0340100401002c50300300e203009601c9960b65034504520581000115154940180c900f1010100c0042020707540f4440c0014442510b0005820002c5025403100349105510503181001340100101d01d04030f02440944001e10f074403141c280500300204048900400c45003020034010340c28600c1c0c1008150a801c02c840683d00110207512640769076442c113a07084210102181a44040910380b2108255404041c020441321001c011404600c0c1c4010400d4584003d0701c121107a95003041700704940c01f08141c1000c11503031421800b0391506403102c0402035601400e20300308118001c85c0000383c100407040d8450792140101d511400101d46440c64407000b22895584d00a4212030100f007202110b600031402002c600705946000c0a0039501d0b4a81507040403400d0604403a203901c0441400728901c8038102c40c50141112500300200c515040400a00c20300901d0400703881c901c101400a81903460b1424400106040c500b0380c0c0e41d0b6030406 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 19319610 1250 19318360 19318373
    0xe0c060406020303100b030702070911070602030c090a060212040608130203030a0f02160608040f020a080f0703030323011206020c0312010503011503030909020c030d090b09190b04060522 82
    0xc459851050f0000417010800240080640380104101e42c02066828205510340c80204000b0b00140c200ea0020b0212000084840c0000e40c412005001e681c2c0d160001101480000c013041e0b00714009541244c40c03224030355003c100c151000c5465500d00a0035075218484a0010401c2881000e034042c00006000102c2c03540148141c036a1418076400c880c007843c0300541c614003081e40c0780291000913403418040340210303000e00e9035044641d00003088601320f6559103c05520f0a1550303200307012036400100040003410b4240c441c041c214414459054614020741e44411102d8105014540c0200030466a640500105506403902e07401e01000312039440a400111104681c0c0034800c9a1180d824241140202c1594090410469505448004d041410103091401035004500041d0b9548000d01c0241c04141c924001c0c501f081d405500500401d040014a07541419110000c858100f4040d03541400002c41c3c490b00e803a0b0154002c0000a52500c507904980c0c40115484d0203000501990808031040c000d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 19320860 1250 19319610 19319617
    0x30219050301050901060503010b0703030c05090d0b060102070b040e0103140a05060f060901060f0806041a060301090603140a0302031c02040302101106090705030309060c010b13050109050c0304150e0c0604060203 93
    0x3c0c112100400d681c1c0c0c82da1308070b07203d03c0b09001e54000080103010020019019801c844158115810801d08000300e40c8041001d601001c4415a0100d901c40284046942c0500498ac00342040781d90080c0780508091040303d8104062100402042c1d40034955481280284007281f240c5600170240c40450030b00268802c1491010350702240b10307014074000007488a0080454010a10a5489003c40e40e03a40c3c0c03041000405824045020601040f03130304101680e80c030001103003c0e02c15a03c000400d00c0c1903013420314029032012162081648440c40403000b00790008141c4240200820350300b6400a899903000c00030340201c1c0d00094004c903652110508054104501603880242c40c0c042303401554511340141c2e0b50f034642d0b1081c80d070542c104010740071660802c00000d0401c00c40e840004121120b01c00b022440c04203050174000001c641c0e03680140120812401825000591030041d40c0c210704003074940764403400f100d401c2801c0b001c0d905c0d00c1000c40c040301400310150404000f440d003030700c0e582e941c40040d4a035030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 19322110 1250 19320860 19320869
    0x8030309070506030603061303050c070605040906140108010311010306031709010e0618010e030f0712050d03020304020108070315030816050c030703051518010203040f02030c040605011e030219050301 88
    0xc1e441e400708150400005892062000400030691510b480c1c8440c030407002c0401042d000c0007400c01c5045003030704040142500401c126601e00743c3d41c0349040039000c2180d4103a0002000c3ca00441c13440c103030070382e0b120038100e0540b078010b4950700410340c540005078001c040c01d41c00100110000c10f81264000d0843e005059919404c0e210580e8800583c07040114070300c03500c43c030b0400012030048001d02d00d5105962680182e2402b50803180320300e1910980301c0c50051180e02c01130000107801e044400300042880701a00151913800c040d070440c03c1c01d80c0013811500b0001c001034105550740918480480e5920444001140c20116140c0e80f202111200c503d00c903161003042d034040c4200f00039901c8034180000c0c43d07400c0781d800902410b0070456540c031115002102812080540c1d8045102d005254420f20007140504d100c2d40c428921454544107060804207a241c40e40e100c0d62801c1020070488e604038079000b0400c0803a52100c00b562a401030b0680003400381c006c280b074400c0240081202d182c0e0700a0300a5050f0b8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 19323360 1250 19322110 19322113
    0xc090c030b01090e010b0c0a051023070203030a05060103020d090b060a270b0102070305070f0509070201020c100209010212070c081c0c0b0402120a0c18150506070501060f08030309 79
    0x10075034401990100380d0b5100b4040c059003240010005002c484d40a49040101d01c420b450707090305103407202450301c041c8000038014195a81c04020b60f6003515200e55050b110491002c070154071700814081d40340c1c007000b00520b801545590005440381e200390304071040d000f54031004000b1039925041107558100d0031150340b400745101050124032003010000c909020710384050b0710030f8030a2003181e000010b400d03607110003815031007401c1b808000a04280708000107020050701e80b19840f45800100b0001074070141140065900c1000038414022022458980d800700c008805650752058000403464030000010b06c60007890007248078820018201c020200711800c410840e03442c5804455118504080e08912802291400c40c100d0005110b428030b0350b600600080683c4e0b0b030b1050b43c142d1a41881c0126800710b07210a491041400b654500d25501152580c800342d04001e0400030f22143c0400380203502886101e0340c8085081c40070001e00b500700102424164401541d815034403070003a90380350001e8441c280c45 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 19324610 1250 19323360 19323371
    0x5120c0307030204020703050408030a020c03010b0906030a031809020406030e0706020102040b07031d040203070e0a0801050c04090203150406060c050d03090c050405040309051005070c050303040509220c090c03 92
    0x10005a504811a80200900140c910b5542000000c2d17110b802c00710103010b4103000c00a28100c090000e002c035103907141c01030603201070340c0001c160031130f0b108009040c41805141e003400b040b524002400c030303e0aa8942850102c00380c2032410030007958099400f0100003400000c0108150342c1c940c1080510719a04022510000d8a0303520076803c1c2d00640c095000508018002c50000c20300c0b51188480000d502009164126074100c0032030140e0788202d6010001c6140e0101102c1641094180400203000c0e610081000b4240300c9580e0003588182d03c103039440c0a40220204850340590706584a800c500104100000da55a81000e4a11012400f05941d10b0060000054546000e0700440742c0c15684115140585801c2c13504003c02800007400035400c20502c0e40c4049150b4452850040e0340d40c403a030325500d403984054038182601001c1508554025001444104015110040c0341074108042c04180c1d07480002080b4209481007007200084c1614803600310000b01e01000c1e5010200300c007400c1d0703003d119 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 19325860 1250 19324610 19324639
    0x230a090209010b0c030a0c0c0503030d09021207030b070f05121501140a0905012001091b06021b0409020d050706050d0506010201090210030506240a110f060406111207020705 76
    0x3d0780c05040041c1529410400000e18a5403242400d15003c3c0c0c492440c10b440280c80c0e03000f0905c1e640191351070340b00081d580d14501c010751406079414000145e120b030090041038155510454010005480c8900340049001807802070741c000d6043d540800079001c400d141c03030b20b0400401d42144581d00c2e40300707002c10300110b062012000c10a084034180c00c0c5030348511501900c7c040045407a0250407050f01c440c01c4650180c048030b20800c1c060360740310f82d0240e992115103181c08040301d81110342c1c80e4030040070340d4802c034080200604d00c0c0803401e151190865001404411500124009000c0980c000b88039004c0c00001181c001e8000303000c3c20017900036003010019582c41800580c201c5810200107584076024881c0901a544280c010b035070700c500054054000784400d1403200780303604030382c454008075110041840a042d5034000100c25580a1131401003000340103a94059803181d102410180c01c842d290920080311190400c03c550301c01e525580104254940f0784002910b4401c207005180c032076a02d10360304c0320 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 19327110 1250 19325860 19325879
    0x70c030b0601080106021510030b0f04150b0a030f020d05030a051206010309020f0d0c08010f0905010f021606020a0905060d0c02010b120d11010b06040609060206070503040f0303230a09020901 84
    0x70b0584d201c3ea0003c010035011b030f00c0d10841190004215800105103c0c1009c13000038494007150b406078540c40902c4407a400e10b8945404446a04c02c90180030078070b041c0c0324825903903a42c00c62008980d00800b0f0480e40c140c072800403d029410480010f40944030000f40702000c50707400001040c4c1d52080d0b44a01340c883e1a400c0044080e80d4190001075404140154100a80e01d170000d02c02c0d20241c861355030124203584d61103039682540c0003042c0c2000300e10b9590000300d061100a01aa00340e400b100b6208515154200c00b03141c951160741100038080079804105162100e01840160001d040020460f03510385003400c4070320002c4c11550f51403c0c0194200700081d806820709880fa6003203101c64401130454289014012909044d500c84040110341d03d42040c203a00781c6400c03000700064600d42d1390340d078442c9040600103460414050201ca0402c0004c00822010490306400344403555814900410141c2d011707001e0821511141710b400d070321015108180070b006009540145200f074400e41b15905260307640c04010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 19328360 1250 19327110 19327127
    0x90c0304030e03010c0e040b04060e0112020901080f120d02040f0902030105030d0c0809010e01141b0d051303200405011502150906040b06060708040305010c09090b150a0e0402070c030b0601 83
    0x85030700e01c0080b03081c914054106540407080540002b90065031406510103c1d40284d10070084132a0230000002503081010710b09025010729001000c200700d4542e0550380c0c5410090045010741804079084000d682b0b40d804903401850741c2600040701c0358444002030b000754020301c00d00740b00344103501d000c0c20000e00174044104202e411100c16401d00030080015035840200c41c1030141040b0003030794030344003034074920340a0710001056185140c202a481e41e051403801850103068824814140410003090000450000a6a80c0150280e82c45000001c9480340c00700c3d80103102d980281050300204400500c40240300d201803085e070840c0c02044608080c010700c0e86003966141d0094000300c0000d0041944c01e12140d40040c4042c25903442e00980c2e4640c24450b40041c1c000b2100c2c0d9440e800b1200e00399078003400d80307000740440107000c00c002400000011440901d10700034042894001c40e81071880c070b004004030040c60101400a550b1000f444c80c0000021050340000c80e10000c0320f40c0810070951003001c08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 19329610 1250 19328360 19328381
    0x51206010501030f02040e010b07020a05090c07030507030905030102070f03090f050f0609060705030309010f110f0d24080304030b0711030f070813090504120305100b0904020405090c0304030e0301 86
    0x2904840e400c250044000c0c003641004092007a808000001310004410807150080800c65500794681c030307c074410898544140e0b40070394070645d509010b003c01d0201a00848030155807604040303a5a0030b036407905440c0031005905c04c60385540f000c222542408444a80505698403d542d00309209803201c4c064640c0c0c5983e030140c1030b0071807a115101c0c40d0714100a002050180b20041c1598141416951414503542c400c840e920f00c00d035150001000941418015410580907a110f51070074820220038884403801807040b4842010384402070400024885810110700000821000e00b40903200c0021a0b0b881d440f5100859440c002c040004012620803400000390601da10081c0d4a8020034504d650000c0d0444101991151b50400c07035014104898540031f4000c0010440129040c60641407000b9001d054245000a140c201820017405c052001c105030150307040c4414250b03ca04040e402703c1c00038002c6401c0700760006801001e020203072101c0b4014510071403080c0e80320060352803000d00341801c0e245079404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 19330860 1250 19329610 19329613
    0x1020a020304090f020405060a09080c0405010e0c0d0e060a0c110102040302011b0312021207021504021f02100507020304050307090207020315071701090f0e010203010509070e191503060512 83
    0x28800f04000f41c100c2401c00042090150401d5214800144d0f41d41c0711440d101c1c08502e2800042148050034003101c2d8511100302c07000c03c1598902500d604803608010980c00d00440300140440c040d9076140e000094011800d000c42d10b061400523203080c02408143c0c01e5001144c1d80e4880554038080500071201a01e506966103400c0903078420606174515400c810840922540c80b104c1d4481c03500381e1000d090b41c911006024005400e0450011341040c8680c03840705800702034502000b0268070780740c40b21201009a00c00707a14405000c00c0c4203d06108100f541004403908050501901039030000113002915000c41c2980c203240c1e03980081c8000c038400e804000f90142c012107101d880030442000d800d58070203118180300384112605524000d1414098200c2e8604070b58075007203d00031911705c1c03042000c40032540000b1031840d4109000281040c030000c2c01201040794462400040d44c86041c0d007000844070803210380000a803507c1803021240c03001c10110740028074110000a079031401d5848201c00810050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 19332110 1250 19330860 19330867
    0x60f050d15020a05120105030c0d080c010204030501021b0c01090f0b0d0902040c0207030506011208040509041703070e01140f12070912030c02040b06030708010b09010306120f05010e01020a0203 85
    0x8090051030818080203403460980031802000e0401680020f182c4011160341c0c0d0759482c603890707444042034030041e04258025400f1500b050216110003180d10301d0744d50802c502644442c001c2c80078034068401c541009002c1e500100e00070080030304207244c241c4c04442000070b44a0a540010044510001620030f8409a00b400003042240520800040032030386404540411010500d4000c00c003039865002c101e0006030b100f110100b0038404148216805800344221203085105541c580034003901813409924894100e05c0c0115082007c08803807210880101c00c501c580b646840900901558100140c070303404201d0b1a8020307001e0b408804c04031110414910629801d0903490755150b44850b2004002005001042e0001308810b4042d18520304564840c1c1d64020712084039206004c00d607a82511181e020308801d000740060a60010103c6056401040c0042e41358200358004030090402c0b80e00140304520a032280000748a0b50a14954081e40114001d10103001c0000c0c0d00e40c01c0b071207045a1040144c0060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 19333360 1250 19332110 19332119
    0xb0a020a050f160c23010e03030d0203090a061b0e0405070507030818010227030309010c02060f0708040902040815040209071112040f0602160b09010503040f0f060509010e01060f 78
    0x41d8040c2104031000414520880d4840c0e481c0d01313566860390400180201c030300441c19407120f0000401c81202d5000c4c40c10321454000301010279602d01580700c038030000c19000b20004000329000c210165849400c1038003840a01440c40813803d04901686018000600030b15007031003181024066640950150b540c0c00d4600041c0361011104204003030300004c60071201c00701c0082051424000341150b4001003072884011703004600c8040c03485580c1440203022f0380080c800911540c0c0c10a40c02c0c82031507016074040703a0300c5454200d00c450500c12001c009184c2d081c00714020030038841035409402616054811901500100203450860000855000794080c0d0364200040016106850520510084100f2156200c4444805143c3c40d080354210940100b410503040103110f9041000302c0c0f405070380b850220402400e03d01c1c000d03540d00c43c0458080c14410001301181c1000072000c502d140071034000d0138040c0500c1852815001034442607076446d24640c20b00c0260340384403038184140c1c0222a0381c950031308601480c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 19334610 1250 19333360 19333387
    0x20a171e070302090904080306040608070e220606030807151406040209060c06010806060108060111070603090c090e01050f01080106081009020301091403040503010c090b1b03091c0b0a020a05 84
    0x744081c0c10580c00780100581074407101c0b070703041c00380b44038a01c1c1c552a880c00005010481358281e00075480c580c4141810003c00030741e0604a41c000008000c04010000a46600c403411b880c5450001c0c10300c1d180030340c00824070503d04080d2603510310420f15940304014a042e82070503900140c40f02660300c040758000c0b6400c0c0ca01395005014529000e46481c1c1071130750b0320030340720308040e400d038003401540c0c0084082203440c0d03900c8100150710400c24204211001a00c0c0c1c0b5565542c0550b000300d00030f0507074070105d400502410250704c1005201c01c90303003801041e81480c6024060074054403801071188820001094980b0107016180c140c4004500401c00000007248150141c1603541c1e050f44c140d540c400050340483e0001000d84503a442c580001c5d980e4a2401e01130608484c0c0c106e500300208210800d090000740404002c40381d000100c0640c06e4003c0300204c0e0810f0851107407036010b44d849442c00482c003006606a1114020044c0200d50402003655076a4914090340305006000d40000c000700b0400016041d03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 19335860 1250 19334610 19334671
    0xd03081e0403020309190906091a01141e0409020a050a1d030a081b03040b0a121401050904020a170a05070915120615060809010e01090302030405060a020c0310020a17 73
    0x307186c03070020031030782c0f030440c0c00482c0c285400c2841180d4403450055411084041c99220b001d0007271030422500f42c5c40e02001d01c0c9034080c58032500407164880e0101001030114505490103826881001c5554145481001e020303a4461581c210204000070041040f20032610081d609501c006005040059525614102c0c19803180c0c0c4407000c0d400b84510120079985040024002405401040e540d80381c1d003650014040701007007001c04000e1760600755040c0c040c0030040c20260456000340ca051485449504c005180d24145801c81064000b803c2d00c0440058000120211a68043c000b078074855903c0380d40c001d095030380341040040c0070442148100b004018900110448500980c000228050000225441801c5940c02440060705c1e030418444030142c21300c1400c0380301c180c0f04c00820020304940e070040d460b0f01540c42480d10079500030541c0c6486c1e83c001d200c405032500b4010152240762845044081c02900407401c082e00281104c03010241e10080c0c85803c0f80100e0311070000380080110b00c150040c1c3c148 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 19337110 1250 19335860 19335889
    0x180303012702130602060a0b0607060c1106070201051801050c03010b0304031710031502160b07090e010f0602010e060f060f1305100302030105060a120b0a0b0d03081e0403020309 78
    0x4207001406481d80040e2001d4a1600c001948801086140200013850050042c11403040145400103a44943d982c1d01c0841e14a40d500040c0801d030f069900d2000d50349001c0003c038080380ca0050108104900750b041d4010b600c109048130b0012141054524807500700c440c00c507044551983c0800050144000000c0510f52040c030907d08440c026000d4000358419000c280e8003050f250a441e007051080250405102c04400d8144000b1400d240da80c50030030000b40b00503403000d0680381a001c04900c40d03611580d0900040c0070400c0b556681960740300081484403030548205e50065182900103460214080b5105028907020070421046849000400c99880301445140d58818010b14400c1e003801410301600b480340c0034014181d074a403850b600600d401e4a900400c01880b9500700d1005000b07020100c454540c0c0740780c2181c190321065030fa600800008110305040705500c001d40854a20070540d01071f0b031203441103100070b498110606a103100e60705910400e450080243c2c005024254660911324840c40600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 19338360 1250 19337110 19337159
    0x1110315030705030d020d0806040903120b0a082a010c0b0106080c070b0c09030106060f0c030c020303070605090d0909110f0a0e04050a020c01060b0405090f0403030e0d03090201020618030301 84
    0xe0b0b503c800103460100c001050a015812660320f10702d80d03a4102500d142e1208040e10f00740403040391560002e0285002141704a01c203680c50880131025180c82c0d0303a190103068800102d17103040341c0716010f0002800102160722000c00340c02d60514a95442420780e41c007500e601c6004143c00b030b428440141d940c0c00006143c1000040140104808200d900c2e0106006001a03101d140d03a8546c000203140c2510003030f401030014000603c01211025a1040700520b581c0d405191040209e103c91001a00b1441000390241007a0b04007810300c0101e00020506041c170301351a850b03ea480790750307440500f015a030341d141d40a21808400d0210030003400d2218001c00c1355071050714064a02900c001c00280480f1420355041d054640c0c003213604100700c1801d1080308083c1c05401e101c5030130145090300080d503440c001050344205441580111b403c06010b600704040f6042a90309496122004d1b100050013000341403420f80c0148200b4000c6a003850f040c440d803420382484071001d5031031130f0300f01000400000543c41590269 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 19339610 1250 19338360 19338373
    0x30405010b030a060501030b07180501050903100c0201021b010507020a03030e010b09090303060a060e030c01031104030c0311130c0c1b08070f1508090705010305060402040909060b01110111031503 86
    0x81d80ea0601011a00c2449604000b4555040d0b04000c000010000c2442c418401500e000d01e242940d002e0b40d02003107940034070305030b84c0c4d614120000c43d090105118030090740d00d08148e111038280703806402508510154242201114001c440c0c040c0c20b0301d07019200840035803c00b40c2c0d8070380070a2003508a9620382030044004980080008041041000101c0c0d1401e803031740020041c00f51074a401a10240188000d25113044c00420140c0081d03198000c8001040c14543e030350030301140c0750072404181c5004541007040000c144e42e0720b0400c805803407801d08915201d400341c111841d0542015208915600e255961025a40016607490a2450040c1000c0c41c0d1040d005a0b4002040081005410050b000564115800c145803000012850103a400844140012030303041008161000426070100d0782d0034030303000c0382c0340c2ca551000c10b000740f250350041940b95003070083da030060240ea5006201142c0080ea214014074190340011400c031545072803020a00c480401c04180c0702004014030f24003420001b001d4488 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 19340860 1250 19339610 19339631
    0x50408071406010504050718051c0c08070f050a120f08040824090d050d05040303021201120209070f05090f0303040528080c010c0b0a0b2d04060e070503040501 70
    0x4201c0c21607200d1001640000014407040c00e0078080d140d003040d241d00f400f07010701080ca0440c2d0329100b028041c0b80e000380c1000408c2003810b80c046001a000c0c0350000410700d1210740b07440340e003900d4007a14000c4110b40000f81c400003a8030304100702e0900440c1d110345202c840b2541540c0d680c2040003403001e000e0300c2e000c0c400e01010541240600c10104011721140c0400310650940402c03521000c002070080e5941c0d0030815110b4802500402140e020010210001515540b0340c07600364024040c0c01f41d07074000080b1a100110381e072502c02541042450080702d500e51180d5402c4400c03140807181500010000340700740296503036810301681010300d0581c01000e480c00c041d11440882c5850542500100a1004640211203210850741d2404050034120001e8440d104a90001901d0307001c95580041031541c50b040010b107010135a034000c2d480c958000780f0f01c1d15100b940400740403200a407250380440458541d0a441098078042c0301d010121050f445044040d6a2802019034032604020010b44d0035540b548590714 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 19342110 1250 19340860 19340873
    0x4020309030a170f0f04031107060f030f2d02120c04031e020102030313030c020d080a030e0307020d06020a0c060e01020414100206010302120c0301020301080106090506030a08070605040807 83
    0x511404031080115100c908000006000b01049800940c1908003542404130038030509524039482040450014450384680c90f08541102050b1010340560190f0030001c201254006d189000005181d6818003600540300d00b004101c2d507400c0c010101001052403100b00041c18011146501e122021005080c2920004020107049003280c10868038000050140704200c42d01e0300b5420540c4413801058504101a80007035500c2c440a07154803401d180d03044100c01014490440700c0203c60b0701038010b20340300190703103001c0d40260865800d400100c2d08000304129903d1000040d603400a030001c156a030404559110040294030807502a41000312540b1040080360b21800342c1c40480c207107070000503a40c034580605e400450110881c003900c99810b801003c8103070783d0b00289081c1903076012105501d10200140c20b0318640036403581c0e05a0035500110000030980e07810760214080350810b0b01c05001641d07070341040644803100420010070484092201c4004540e4645c40b440c0e10500c5407414074076101603902e600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 19343360 1250 19342110 19342117
    0x6011e021005271b0d0c080d03090528080307090806070e010806010906080f090102091002030d0b030c0904030e0102010603060207110102100e030a05091302030f01080601050d0c0501030f06050402 86
    0x10107078805010f0b00724a641e08201296404029000303080424025003c01d903450042d4000300340315152084140c010b00031005900c000034042c0c2d4080340e03100880f0310b002034060072070100700759040e02605984180b00328a441c03928080303800c8180682e450714126941c006041d040a000c0e2400c100285230041080002002558002c403695182e4000641401000401850b8002d003900d0400145400401215420030502d235008604d0030a11043c659a00101d94028007a03844150781c800c0380c1d20032014600d074011005180900c0101c0c1c085c8501030004050665403d09491b0454100c0b04c41030002d00400d00c115030030000410b05200100d1030305e6407600c9003410783c0c01c0b03100c09440301840700071020003075a01044104a220b40c0e1102c00d1203074684140c0700c1030300e80c092003940c0424000001640000b950710040107200711411000115103e080603c2901c0320403000340108402032003204004511440c24410007440186d02820004942c0c1c140303c01100507002001e080702229480700c80106882e035842c000b4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 19344610 1250 19343360 19343371
    0xf0614040503190b0901020f04050f01020a06020a0509040b090f0c0a170c0a080619060e03010204170109020306010e1302011421150105070c030b06060f040f03031706011e021005 78
    0x203800a6000c40d0404c4184800d01600e1407510b6031040014000c0c0055010540b400c4070811a40c02000c8190800140c0c01c002c03100100800ca140300140c41c0307034020340000c0584180715080c0c80030032034000001d09200744003109a13280c0300000b4034440003031030780300c403000003070804000710728283d00309840002c80714031051310603905400301000129148010640c030400580e4082c0e021260b040040302c1a04003a5001d0f0742e03c0c0030b14003c114040443c0d049a88003501110010419512101003590624481500900001104074400d0041e0000054100032b6502d0003030245140340d02400110103075074015944003900340f440c107541003000e012004d40011a08201000c00c08003224544542c54000ba000004c0c00d800300324075040c40300c1403180c04c01150712152440184c0c3e41c4010b15116035280e040001c0c500d03000714441804120800180890011908240402100e00c03d4840403940f039040c140d00404440101c41c020700150b11065201c2121414070040c0c14561100d005403000110780071607110603a1001c031b54 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 19345860 1250 19344610 19344643
    0xe04170c0a02090f060904060218090a0c2309091005030604050f0105010602150408030604060f0306060609050402030127020f040609031401060e07030b0f0604141203040f0614040503 80
    0x20400c1907051030750f03210341d11400c413044481d405d00e0a1740001d003c91001600107002981d0102d02026114001d0b44080c5c040840245604130380d142000d43d86000e007100104081c0041c844d0b0203289041260945081845032001c5816030400312036400780705007440010141d0b0241d108401c0c0021341600d080c003000b800345000d1400340150f900721040705400e503441030380043c04540c0305490301c03111031000c1c440440d0803e500c40380c0750b07540b521080300080180010b9000a03144070505c8600100300501503121000711000e5449150b540c9a80380704000881c002482425220b03c0602070134a41100808018140320401107801824283c0c001d9441280da0001e8111034080740c040c41d414018030451100d480170076030354030000b0700c036803130500301070200d0940090070380700a05886411070055507884a402582c0400054003d544940e41c9600c0450081d604012490082610450030914100040200c030f0a40e645110052025480c094046400e07010480d81c1c0700d10800240004940303554180980c4114094800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 19347110 1250 19345860 19345873
    0x80f0a12031821110a02040b04200d060e0601200a140d030b030303070207051e04050f0109050702010e0712080915070201081503060601050a02100501090c090501020a05070e04170c 79
    0x80060381c0510b10381854400d0220141200718044800a03c2c011a681c2c1902d001c5812240b03000271901400214815109502c0383da290140d910985002421812100400c180000c42d80c5407100000840140e901a0001d85190113041c8030b042e910a0a03041c00701900d044414030991511608001d80000603504510b4000741c2c0d0314448507515015502172524100c02461660800b060040d5a0740080d105150180c0202c98044840758511541003240f924090814402c40c41c0490a01041d40360034000c4100310351801001c11103051052040d502c1041c0392900408070f00c1d081c080c000c3c44000324103000b101d2400c41040402c465403607541c058481c519400c55819114603842c800501003a90003080e5840704007000781f1051079940c00280070303074002900382483d80d0341f619490022801e004c214442c0340d11083c1040c00000304070100d940400b05103503007652010400c3d070b1113a004a0b1034420402001d01aa0703c0070074140911189800303561381142c45001000202c0e210703090700d0304d040d07041b64820400542092 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 19348360 1250 19347110 19347143
    0x20901030c03060e0604090c0308030906010e0c030f01030b060307090f02070224040603050a0207050a0f170f040b0a050c0a0b01030308011203170702010e01090f02030106080f0a120318 81
    0x1401107a071003a040781800e100ca82e00300000c104007030900800300c074402c50700c5021410501ca0803419401c00385410851090b600d2621030307035003a038803102031050303600c224102c000040604d0398600940f0300440419094070550f910396298545e00780d201404069050150142c001902100752003103500200e091803001d621840310b801048804000c03a0f0360f2208500e15007075015428000c083c00c940a94a890600040c0d50300da008000b4002c1c041c0200043c614814a1065400d228510b141840401d100300b603950b501c40e200c440803014078002c908509a0080091009101a22249000d4544440e10349440340c00c4c42e02480b0032600e4212a103800303455644284005206065101d000315000d04034540d240c215094940d54010001440c86030142d00754000d400100300300c0c40c030039041a100a8421402445443d40c1b03400c110710030150303141c0d003240b183d0f10b81040001c0d10440812004200e03031089000d010055043d0702d4071060510409801e41c2055914205001c511b481041c1e8120360b82e000315000b0322424100e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 19349610 1250 19348360 19348367
    0x80106030c06030905150405010626010b010509011b02120a0b0106090f0302060f130504020d0b090a050709181e020304060f090c060c0507030203030c06040203061e07050a120e01020901 81
    0x11034101c4010141802c2c1c407900481c00c00130340c142064004406120284d47e4904000b4010909a044801082c00080c5a101c1d00307040d00c1c80c4801c01501e82c0d0002c100b1110710500540d0644501860940420030304217003148210000e50381c920344a40003420301e240e02949407016604207603900c0811594120441e00500059502140c108090b250150a41849508540000d06a401150100b9000420011ba0407240d40800800312000b454042c106544451a141160300a1300948102c5d0b405001888001082030000e401a035001e00d086803600d02c4a142032030071100000c50705010610001e41c454600e10340e240b0032000710b013108110340c2c017005031a401c051a009040d90203850050404508186c103800104042e1803540c000c072462401e0820810318603241c0035042c0201a400a580b50002003400c404298000c24800d02c69031003202a1001e541c0c0700ca403641c040740d140211890100705c1850000d4261030041d40200003803102800c0107621016035404c4ca0041d1080c1402200140e500820b0100300740d40c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 19350860 1250 19349610 19349633
    0x110f070819080402010c0803180d03020405030c0d0b0601030207030c0510150504020316051b010609020702010315080304030f02010908060403090e0a1a1e090a0608061620011508010603 81
    0x7003502d810030841c10141c0008001c00501807000d0080c13180000880c14607914000301c081595080416a550b2414110020380250080d1140d1030090040c0250065949014400d075100c0544c0405810295115980118005d4010356402c80c1031000184462011035030800800074101c01140c0701151022907080210b00184c0e182d4880e501940c0140240814012a42141c41c05203507503280c02a11140341994900400a0105280c206946006030114900c0802c1d002001da890003030700c0500c446103003040254011b02c118890221141c0080c0814000070742003401540c1985d005160031a00c241d2103102903810314006480480124003181c004014242006032a142d20000c400f01c20000c880010248441d515103910405104d000c1c3c8034040c000b00c0240381110405010082d06401c1a850503c00c240000c00d020b024440b8644244000a8210b50424004c1071607410b0b903a40f8001001c004140c880207001007100346104654031400600d404040130000031008210100000c201140b450401104422 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 19352110 1250 19350860 19350907
    0x303090d080403020d0f020313080606040b060403051b0105041d0702010509010203060a060e040f021b0f0a0807020103020306040912050702040605030f030301060c050c06070309081005040213110f0708 88
    0x404402c1001094010450b68030440c00c600740032068111140040341144070701c1c110481705c0101e4850100d880e020000c2c4c0e0b2807244805803810403600820801304146070040d0712008042e0380c84051860310458041800c5401100306040803820540c44400103140f200c80340c0440c130b4584400c44200030742c103642400340702d8120903080021403075400c0c00c50100f15407580a000742400c1c030080c04680e00f59516194406c02920600d044115160700420003000c01d42b80100c00c944126101d07090003000c03000390102c1c8520105900031f09d01842d0074030550040d07010b501300400300c0d544a540c5080400101e101c2184190303143e003095556503a01c0d8868410041255001e8020070700a03400040207410709403000086905555160034109921122480c245140211583e8003070342240300840d940d000c06400620490a41d8075030303020b46412569904070b107811140304440103035020300b21080f5509400001d91100d00b1094407100b0751454503203100100031031076000300000c8900c940001030b02d000250901e5072940989 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 19353360 1250 19352110 19352117
    0xf03030504120e0a05120a050d02060105090a0c02031804020d060803040513050103020604090902030307050706050406030e010203090706120603020603040b04051203040503030a02090103060302121c111905010612050303090d 98
    0x1000022030513a1020b4045d403409400c0f550303042402850100510201c0076030140c1207a8103000e13003d0009480350750070300c40d150140220002281c400400c4d40141c41c12800c841d03004508103182c41502d00308040140601c2908180d00b0020111680010b001c0c004c05041000021341d0340c2d41c6070605020046080040c001382c0305203400014401a0765420841e17086542011011840c2003881c00000c1c20351041200c0101300d48a044800900130b03800c10041c0c01250040d403400c008100681034201d00342e01c030443c2c4800c201c1d04100303414860a17000d94141c040101c1030220018902d0b48990100c0c0c4198010349090303c0c0c4603e01410403042210400c000c0251001860555040d81085e583d141d0f0359001c064140490543c0200b0110200e9119902040046400500e101800750071509141d413a02c18261541012040041000607458001c0c034490403a2a1244011f200175040104802035400c400c55048415540707030480004c041c800034903010100b50184014560b242000c81c086840c0804100070601070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 19354610 1250 19353360 19353377
    0xa050d0218151809010c0801030f0b10080316050106080d12090602090d03030c02010f1104030204021b030417060f01030305040506130e16030e0a020a1802070f0303050412 75
    0x107840d00d03180500011030644084040740c0314900c0c0d0001c5091242c145941208041c0c0820034007000782040c083c090003400b0001c214041c285941210307026404d0101625604c642010310000030400903020f940a900110440181c2e5100c441c4541507510518010a0140c3d840225209010003841901e005003030a000500030421034100203803050103001010020036a980e40d0a2003409070980445001c1840281342e44000c00e200c1c50050f00410600307a14400640ca04004061030003c948030b004503540c0b5002c03085081615560800001e03500c03200000310307442915000035105034010406000680102041303500700740a0004070034070b409401048800d40a030298010404240c2101c100c40c1918010307154940e0301c82c801c90380418280c0d07607544000c842106541c03c2100000203242d441004143c6a41c0034018003401440480d90780f083c515000e03502644615080003541c286c2d13211845400c0304004054109901030712110745070b440c0040c0542c0882d40310f00c1044100410407031181442070b21410001ca2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 19355860 1250 19354610 19354613
    0x3050c0901060e0603091c0c1b05090604020705010b0a0b070323090609010e10050d060503010203160e0102070305030d0507030c03020313080901050d09050307060b030303070c0b18030c0601050a050d 87
    0x3140f00c0c500007501582c000004103e04501c107111072407640b043c11400038040280380c070008040303800007101603500c035014110300d559904000c9075203000c079a8010b1030010142c8030801080005d50101108490325075031940c408106071220a9164010040006a91b445208905010b401201d14400c0c0d031080c00300702e88249008000c102d0507284c008034281e401a071174101010050714414440f100482c0d00c03003444450303000c0059100c0014205000400028414203a44800341402d038001601d164140d1074100d619101240d00c12412000488014412120101d07543d0701c510f415940b09144881d0b0064071403040100d2032f80c142c0902c120608031460114618944900d180c1c0a4040704031300103100032000680300301d0980c0300d5810b485440c00301500c00c03c9000d00610b80540d4039840800125916402e203142c2c40b0340307450040240d85c414680c03511003080e18545542c90741e80c0780300c0c0101400d020400368065100103003010405040e50036041030040099504040801c981910203a0003144507059840c0c0346030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 19357110 1250 19355860 19355867
    0x1002030a0f05030406020f03090c031209061209031b01090317010b0a0c0302031e0702090f010b04030807150507120e06090a08030a0f09081309020708030408090d05010606030603050c090106 83
    0x40c0552580b40c0140c60303490794900300c0c01912074900e1500244401009100300f42c0030100b400541e0301411001ca42c0e210f4407507070301000540942d5541c554010018804694108080c2000703a074005041c030142c0c1d1505020040000c5079445e00403018046a41d108811010075801180f440803010440741e050710a989041070b180030520a04c42540c0c200705404000c2d82c1014020815545110803d8400e010700c0c0800050985054003c101c0c160310505000c0041100c0a45021110b8140e076140c00b0a503160a0840d101e6515952007078000300d45214050b410508038441e50710806008401a59402509180503040f8405031590703403c0c401c0132030b08004140400e007840080c030f1000241e441120552a40d607621b841c180100b0040c102c401c4200c4c1820100c1d4104500c100061010020703800c00007494603151241c032000c900424070010011071041001c503020480c2e08003d4503503032200a046445241450399254256146544a440407030746443c004d108000c0144140700c040102640c01100c4d0350326000004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 19358360 1250 19357110 19357127
    0x605030606150903070e0117010f0c08010303050f040806010f0302030d031a0f01031b08041205191103090406030b0108010f0908090118030609030f0f021b1e0405010f051002030a 78
    0x9a00003a00090801d07441c0c40520112005040b10b0544520341d60b501c1c0344614590900d0380010605519140e00c1c200d108201c2d10a03030030b50bc1c0007961106400e03030850741d003074595034010310391000760440c203020018004004000c3c00d8041e2018002c6a01d002d0300c2c1d0f206141c600442c110260081c10b0800743c2d600c05c00d1190000c091446001101c80841490702174005900408110b410308035002c1d8541c4081282075080664903015a1284102e14052038811400304d580d40100445960705030f180004800380325124000c16170501188605032440e16800340c0025086a11540c400c5601c6001900104001c040038030918441c42c40c01c00007400a000e40b40d41d02132403445041c05003818459a038400c6500000b00500041c01f07140e01080030803100c0c580c0e0802030608990701501340e0015040b816024250340c40410f25283c5c100300078001001d408043e20400c041031000b002321517182a0040148102d55556018903402444280c0404a0050400e02030041e821110b00c00c4a066501c100482503240d40d114081 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 19359610 1250 19358360 19358389
    0x1902040c0f0c0b0a140f070f020d0e040504060204050d0f03030b0f0d0f060e03030a050a0513020105030a0b010311040609090506040902091801090204091b05010206010807060c0609050303100303030605030606 91
    0x100e1642d0703951510401c1c000d000c0501c004c0d100c0a08002000200001d2101e45805040192141248c260485204a94074443d0310441000141c5030750b040e0034030781410b0b003250340c1103841000054205920f9601140c01d019901c0303020354108003200c0b0300106140e01449010701c03200303060f542c00100c4003243d00810381049820800a1a00402c541c00310280007195000b000c030320301c281c000d4951364100641890045e10302a1490f0050174542004100009001d0102d48503042c0d068550f6419035440418010050040e007041070b040c0343d00e51814068211282c001000900074540320342e00045d0070301096a040300c00c02850240a9483d250318080940d650040c00c42e4041041420a4041c0500001030340c05004900d034000e40150600c0d41080811a01c4c0e488401550502d2501080e12a600c1c1c004980e104002c4c0314500e42d07030304401c6041c800c03148a8442c1056580c0030700d80100f0f806040d50f5035a480d561044170401c00c050741d81407081c001c1680c9401010020003044006203080d040c9900020b0b244016001c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 19360860 1250 19359610 19359623
    0x1020310060c0807050607210203070f0c061b0302040602060606130506030703020d1104031505041110051902031c060305060105010e0f030601030302071509080c09181902040c0f0c 79
    0x3030800b044224811180da0170380c40360588003103007400c0d04043d0030302c20042d1032852824000c0c0a071002070481e42c42a070b840b450141c2d0f034070003000c00d2415080d00c040541210540e21143c4407401803079004e2100560401c0602140d8005035643c0c41d2074002414080046c0101d80300703440402a214501140c0605c2e03505a82d001c41e1303400d5036622040e600f64001c0c403400004004007070030300c1400b5154083e84005801107a001d00c00c4100c21712106070380795080794000c9a0003800c4801c02c141040c1d0b035003800c6801d4508004981880b0b458403166140c19105e4a07403641410005030310004075191000d000541e412490800c1c80300c107204060540e904c0c0ca0b102ca405005950401544101240103030762480580703a5005130107001d59409507180d003030003500c0e01c02601030801540303c003e2402c00040c0c440c40066007203408580c050440d60f1041001c01c64042009440c1c4103054910003486001300000f4040c10500301814081a007142d000342c030510054030280082107052041d14008940d4180c0c001d100415059803212 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 19362110 1250 19360860 19360877
    0xb0d0507030204111201090204061d0108010306020d110c0c01020d0206070c0809010302071a0a05010f0b0d021b0706030e0c06030415050402060c0a110a0e040206070305030c09100e01110102031006 86
    0xd249040e280a003034850100741748480000210189203900030b10598505554860245d0300740c241d0000c005400084e20350005440c10300402c0852400d5003c1c005100701c8400100c0c0c14020300d155140190002c24001126801c10038082d222036804000406a050060014103010300d844d0300080d00c9080c0c014030150401c2d00000b00a00f06a201e0350450f40c0040d03018041c00070000c10412246e0309208103c90140c01c031454040040b03800449903032008110384032254014a403000c0b10410390040d4200302c19412911003103800d03c0c0b810002c1440480082c108036031300098404200e0710300c5071074000e154440a01400003001400045803000c84402d00c10000030002042e0707510f07039102241091003100241011402400c0ca10410060302982e4040d000384211002c440160302c42080c480005820f40f4002e52050080101c4000280144069540110203d2341142044004004144600d0702160810300040304410300e50059a080b441c0701e0420009078008504601e00341141419501c0b0781c0c000e134070038020341c007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 19363360 1250 19362110 19362131
    0x804050a0b0702070302131a03060606180a030212060a0c05031006081905070e03010b030f21070c0306020a030f05060915030106030602040b0324010804140c091503010b0d0507030204 80
    0x700101401151b01510b8075840750700b8a21100024604a5141c0045181c0064003212628002070701500800c002003803185040c4007200b04014402c00e40a07084e8020920100020140c1e0b10410b441c006840b9660141c5518507000400d84216030050040d0b0081c0401401807014030800c50401d1000d8508605003e5141d03101e102e8034210030b0258404001089041804000303809622107c0892000d0040d0000d00020b244002015114801d20303182c8840c0f64403446043da808003019010b2150300d00d000c0c981c60710300401510b400b80c0303101840d0010341c3c03000d1f000206101419803601c10741d1131146507020304110718149000020000980070b00021030290790040f544041340d43c2940424000c0d0741c000700c115912580ea070801092074008840701044407005040c25420b46400c100c801d490170b10141d64280090341c855665005824425008003414401e000d28801385441d0001028000c0e601407049100c011030850130142503503010024980202072000d002c03400140c0008220098990440c0c0105940015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 19364610 1250 19363360 19363363
    0xe1003020702030a0627050d030b01120609091101030e060c030a020d020c0f0706090f1e080109031d0d0305040306020903030c07060c02030d090602060402040b030115060302030a05070804050a0b0702 87
    0x7480d00c0650306020f42041d0904021665101528514562540701e4882219000b10341e4000c0c076010000e845600b00c2d104a000c0780b4840d601c5441b59500504081010401c41d0b4501c80494007960488150503a880d4400c000307011031480d54580c20402441c0a00040f5022000c0c5900e6080242c010790101ca07000c004540c4c0c400890b0140d0745003044050045459516112007070b640c2d994050450400e50041900c00700c0d6041c422451f150644034005402608585000c01d41244a1b070303a0524040860445c00d008200a5028015000842d0181c2c0c4c400c889028400b244500096000d01c4e407078816401e014800d40020317000b4090702d08480c2c100c180140c59409040110f401c42c0b00d0540e00740e8282c0108a00400d240e40c1003080e924016000f501268640110f6040030b859a0049015102c0541d01910000e0014a0241c002c214402000f03800030400245150042e01424100d400c0040030035000b10821041000ba4400d4a0b0305c28840d2a09a400d4241610744039100d1100d000084e200225000000301c01500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 19365860 1250 19364610 19364617
    0x3090d03052104021005070f0f080d02030a150501050901090e06040603050a0f03020f06040f02060306010903050d0e0f0a06140304050c030604080d1b080105010c1a0a020a11010204060e100302 84
    0x29070200c4440020030400080342d541c08a030b040384104413010407903807181d03c26001c2e2991181e0000c110b0703000b002e00380c8501c2c1030203c020408a03001e050421100005840900185000c0c4440c0b9402040900e205001d0000b0001c0c15000f16041040c01e208502d40d0783ea10005810440318003d042800383d4031400080b4025181039007002d00b007445121400c03000c0000c1e40ca081c8442034000d900b03490751001c103000c090361140c40689026029003d01c0c00c0c86001340c5000002180c0240050524000540d80c03030780c070b4a00b0641240c1500703010942601c92180716040404e4641d0518004840008106007444030160443c207911040750303a000c60120000d800c000007082008011100101228050b181c14034204409502980e51075007100d040810055940c1b25040a00e05914615110104280c4c02c00d0b00455207084100b009a40c0c3c1c51140c20b00341207111903820682c0c081d8100341005a03490101c1da0000e00400180c07088014180e104000030891964000e41060112004540e0101d5208110304120041d02 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 19367110 1250 19365860 19365877
    0x23040b18012114030405100507050705100201091a061003150b070c030807051605030102030f0a0f0204030b0f0106020609030c0a08071401020d050f1005010e0f03070f0b040e0a020a0203090d0305 85
    0x1543d500611005075000000c1c100321034048400209101c5094012107060280c2c0a008210350f01940e000d06c82450074050f01c030f943c800144000105044a6101c03101403405681300340080b2805242444440e0030138071044400400e46082c107014000361404a003c1c1402d0601c0344c59208503000c0303441c004000303481003210f00564000c0e00280d00c0d0742083c10700e02d48500c800d14500c00c1c030500100700020390f4201802503d00c1000034841405440d5984286540500a09090f020303117280d00300720100001c1c0c070b42440a80100380c42860300882c0d6040640c00381c60100068000304895006211865010b940003a0442d4525403190303116440c1c09003403811140e410203005a440d2a94004600c00c2c2c080c001542c00b003071003003078a0702c0fa1000c65103c1c0c010998050303041d80200341c005151490445814240728000215410000e0f0032180e805947d140a1250070b50b854000c00a034200c0058100050070500a049410161118086141109400000e9030340c6c030681c00043e00602c0000110340a250040c1c0640b034200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 19368360 1250 19367110 19367123
    0x4030e060a08010e060d030e010309030509060a1d01030203040c03170d06080a170a020a02060306060d090b04060f060b03010501080712020301060f080108070608040b090723040b180121 81
    0x441da030394806020003000740284a09034030329500080072864203203202040385c1d4268848102040148004402903c0604029070520508118401e003c0d200c40c4004c120400455451109480030301216140315903102105a04060061040c0008110107011500850b907102d20603101c03660070b281c42c0700d400f4000c4482c401091440c100300019403010104111440f03900c505941d511740510003240030018003404c01c0480046e40800701510040c1041801580c00c203400500040c2402c0365502c1c0308042d1000e09400b20341084c105001c0c0020401d2a0203800340d0041c0c41036091054a040c04160719180c00144509030401103c5000704881c81d0107060700c081d0140700c440040d5a80c0d81c46030070103009100103e00c0b000014110000014100790081201d00689525a0f10007000b42c0311a140d03420980c50290a1448a0180740000034140c040600d0301c0c81540542d0301000140c00d07044040008a40300102950b02800000c844140c0e9814059040d078103490101c80c440e141842c3c3c01c03103108920a0003840003001d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 19369610 1250 19368360 19368367
    0x201090b0112030e01031b2a08070311060f0a0b1206010b0c10020f03070e060c031303020906030d20010e03040306050a0e0a170703030b0904060b09150d060504030e06 73
    0x182e404482901c0510303402a243c07400301e501d070800118100c0d8803000344500c918003c580c0e541c40340d5200340100000c10381a0484101c0751f0b00420a40c00b00e10380c51100480b80d00c000010140101a040240c04030041c03504405000940307800d4500c407400c007071300401c450507c0d90b4034059168680e654480200b50080ba0ba8221034066845204000043e40010f4040102d842170030042c0c403a451240c000c6035900c0c0c02c0d00710740c0f5046845140080d201858103440495000c82c080c4030260300200c0410190000300400700c7d00312105071540c0117003c61600d0141c03540b800381c5c0109142c5442d0641003584a56440b010f05800124441051090b50040843d440310103100c2c040010008140251600700300c5c040c0c0c107081c01c01c02050503101c156583d46d8030340d948000d203c180310a0300420303482d2002d0301600a031070090402003000901d00d4006030340140200c07021207455075913542032140c034181400c1a41d132101c0440003513642d1203a80c10000301009110180240080c0d1290001801c25104084046000308040c202c1505d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 19370860 1250 19369610 19369619
    0x507140d090812070515060604150305011a12060d021201061806080703020102101104090603030f1701060e04020715020309030d110f1210080f01060608100b03070f0201090b01 77
    0x180707024921480b03480744585949070500303080b034404641034a0f601030300030726003110120940c4406070401410f01d64001014440002c5103070000c00502e14003030503903400081a40c100f101d0f05048c090b001311600801041481900d5007003c0b08429243c209074215140700c501305171840021500380d4280c0c0c2c1883c180d400c1c5200062004041100380360024001d00c0144041500e50f0310700b036624204da10001e40182d100908503156801c0d5540b010160050019845151030780741d150540940e0b03402c1e4403c0300016042c440c0106425400510b9800c14a9901c9005d401c41d4542800100340b0540c0340407652003580d0000b000c10030401000f0390104215030111065403030745031221600340c60303421402d4035040705400c1c084821400075048003284e078072141d0100c80c2420650840c08283c2d01010081002d10540d016085c0407a444100b040707104480c030211000465401c2c03e16100910b400c001030103488228000304801c0c84610384110035254810781c185480342032903c0c02c80c812800b524400b04090110340100b40088ad = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 19372110 1250 19370860 19370867
    0x11040204080c090105030303040c0b03042604090f05010b04050f030708010c11100e03070b04140a05010203091501080a0305161406010510020d080601030507020f0f0106140a0303080103030507140d 86
    0x940b000310850345484140e81e190145a22440116401802001c04200900103080b55201641d0420b02810b00b60803c070b51050007101c1c081210503128225800d021604204026840c0079a801481904400703111a500d0000c6c42d110301d01030741c0240c920a03813480038030450a4800f003140100900b038020090150384420000a00900c0403010800030310b0064038201040c50b6018080c9254143e503402c011071501e10759031104104601e014000300c03040c1b4508a44150300c244208440841a0700401c001079aa092483c0a40e280401602551040c40c13085401000301d00d00215410b0b540c00c1c0c0505001d0303034030091030f01c0350801303010400d900034080384070590b05049030701c00003d07a54103813601554081c00d1440f0034481a80e0b02c54960342d11030000ac020900080c09548a074020729080b0f44030340100c415140c00000143e08100c2680d83c00304050f99521030400050b190940c0e800100b0f041903850302c56003803c54600800b035580501019060000000b47c1c1c40070054800f91804410b43e04100f954189801058001d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 19373360 1250 19372110 19372123
    0x10902030610021209040906020405041422030512100b030907140901051e011e020c040b01080f010303051602060403030e0307060503131103010f050708070906020a11010c1104020408 80
    0x1240503404800000d103403203000180c13252840c140e0300105410030184104000107401403640498005800b03110018598989024100001e4030001040701640703040c4140c2c07130f20070700c40c0f500e8125a40700711305114000c65040340482c0c2c040c0c01840000c01540da5a00b03000700c07216015500c0b41c400d0036400010890b5000300491800c0c02d48040d120f003007012412070810002c00340402e00070b86501c0400141450444d66248224102c030f2403041c100720a8400000845141030340c02c042c03117080941c1010406542e145064400c80921003406d0074141c405080c210444c0c812900140002014001c0000d2480020304503d0341112100b903004001a80d1192a0b141c010410741c84d401e03295020f03108096010502030300580c1a64030441c524003201045040d00d0f200c8402d2500701028080d01550b85888505002e405402146e10500c0543c4503810b50b4204010700a200030555030200e000c54000c8046007000a103035a400301c403055400d01e00030200d0407990904102400c2d072901400c0e8031600c009400100d1400c0410038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 19374610 1250 19373360 19373371
    0x20c071509060207060f09050d03020c0901090906050a090b0708090705030607032306011d01120501080c0913030815010e030105010801060f061e05030408040803070807060f0c0807050f0d0501090203 87
    0xd55042680e07500c4107980e00c1b16070380780140c0450007091041c0714074108a001c60b1003035802881240e051682d000040741180c030080c2c001e444a1600c400140c030612007503020706900402070b0300e020848071055807a003040b1890040c0c003100c10801010b020414215040128a000d00070040c20364600c3d040001024000b0107400311120940c80c1010030600e010002494514411381d41a1036440030003d200d4492101d950034900b1481c14001c260003582c586035a1840b03000e011300044001000318000d4403040080a401c0142a82000c2d1200550000086d0344403801c0e0ba040380141c10344054005013800140ea0f482d141f001c8180e0150b1a10740002a1003005401110481d080d003402000059181d440c200c83d01d0201c2c2e641e122610003c00340c4851218865002154007130b0103041c0543c28551a151144d0a6600400040c0d5180c45c0101340002800382a100308d944021141908100c00455580c02500c20324008040500b03224022a0207541c500481c0110703104110714a50400856850b101f01400075007007641c1303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 19375860 1250 19374610 19374613
    0xc120a050d060e060f01030f0f0203090a060e06071d010c060e210405010504031202010908040305030c070b03010e0a0e0c0d03030912140f0d15080d140f0409020c0715090602 76
    0x242600c0209181400b13182d000d80258003034001440198054507151030125146999041200311703143c01ca20185007c1e20782c00024021142e1941043c0065034212040040117400400c14070050320340041036512108407600c41c1d00e40c04680c82005071090704504801500301070400d00c00b141c11010100c3c04440a92117180d260302c0f440c1810800f84524062402000c3c0421030800060020030729a480d42a1100d94902c0085070950b00d40d44c84a9668100d0740c0102d5003030b031000c9000c40c10244184110340180c001c1c00e41c4107003198581700c448030442c07001500c80040c560360b444000c5090700b2b09002090071751a0140004034464124131300140180032540341650000007482d50018480e00c10b80d22b00004030050100581440d4a14551842c16440050120300b401d40c2c0799101945c2031a03802000000701000005400c3c064410720007c0d024a00c40e40b0f260b9070300b16041041c84217850007041501e050310319082c00103880f1200050300c28a421601d401c40d2890000000310800407903403000c00e4400382e1356150b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 19377110 1250 19375860 19375871
    0x7050319050603030f03100302030a0f0303050105090403050a0e0102010b0910060801050303030403020304030210090302030a080307020105090703051009030903060216051b09070f2709060602120304080c120a050d 93
    0xc0c614012140180c0e5050f074190802c00646061003103000195400021303030040106240d940340d0000785842c2c82c08800f21603031034501c0d86460502d0b4252113890b005100581d80490146010b0b64010003d20410218500f400b0004c150100f26034400d46c005415030301d01801403003c1e400c00c2114407074951107600c29131001540080002c56a0f00300801941c0c0030f10fa01d0b070019400c05041d5420420003004c0c04d00d00f0390401c5003543c00000942d030204098503640e401140020b03982d0400c1c03100242514030041281c0c1890b4814035007000001e000144070141c080d840701000541c61a5032030100e03003180c9181d0015295500110318400800d0380c9462601348a4410030031228041c080094908820b10b41218403540103128500140d407081c011201d6600c0e0b00417528018120603040c5007120f000c0c0002c01c0b4501c054010301c013001d1140000130f1060b200503000500042812901c400c001c080640700003400288030060100d440f4000500410040e88400d032404030b1141c6501d202c0708010300d035402ca81e601a070003e0411 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 19378360 1250 19377110 19377151
    0x60e0312040506041401020a0f06020306010905030a051c210203060429060703110a060c120204210606030203100f0510050105090f0a0512060a150524070b070503 71
    0x801c440031908050305450a0500d8104481c0340324100c800818107600030303c0382550004584402da00001e82c4540b00060322400d201000602410075504003900907030040610760082580080d40301902c00e0710781f148000c40c20600c1c1c0101d6034444003e1003c0300c2081c0d03d4110540c0604a600030354070680040c0c4007088403105040c078401d0f0060181c1c00d07040b003102c01c00840042da42401001080210300a042c054199910399080d14584074203902c0c261445681c5d250040c0c1413550001e41642c990180b941300394102811701e00c0a122950312088051284501d10208000b0400260003110045800505980e8084030780080b030b8026108044410a0061030a0005055106004010000c3d1041a900c0e41d041c800480107000f544944013110b29400000c1820014042d500c01d00d5880416012202400241c184042c02000b510102c00c0c58010f07070160b0704024001603c46142d01008480c1c9808120100d0000a4410055209105010700100880010007070502d4201000b14040c0079298a041000f4010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 19379610 1250 19378360 19378393
    0x612031d060a0909050403030902060f0309010506091504091110020304170d090b09010c1b0603050c09011704060207061404030e040e0303010b070c15021c02060103030206010501080a15060e03 84
    0xd04889901085440f00e050000d82da007a44400d80c89446814001010301d070341d0300040c2054002c0f8040350b079450740c00030400010394070a018203034009405a8601c0d410342016010326651070441c02000e07014654039500e032428049111500c0744001000380c0350210f60860f4050085d02e80e40540941c1002500d22301508070b501d81c00054182d5200016a41c2e00c2946003448500c40d080d5110048841c10400622410004101e070341036040c17481c500c513400007840a0b2a000f400340030b403031005042c4441d03204180700c8006143d80011581c0a5112000144480b9a9807882e086c0000e000e00e40c1c000c5c100c1450308000078288203401c0011801507000b0345918008108104c01c000994842000c803101d26081440104a13010020f4007910b20b051084845c034481c0c41c1c4a03040c289480300d0345d203070303840059000e503070500c030000e8440340301240d010410710143c681d540c10341d100170395120810b208440c100424a00050080c0e0825400761940d5022610380130599030fa9983c0040025105191840c4207009070840f08100e071301e0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 19380860 1250 19379610 19379617
    0xa06020601060504090e0a0203120301090c05070f02010503041a090105150405100501140c030f04170a030203090d150c020a03090b040e04080705070e01091e020901020a150612031d06 80
    0x4035990f07080c900b5040c00c94000c0901140e001402c0f641c4201d54500c40140c0d0b0510440132000f00310f80b200c170340300c3d85040300000645d18809000b000b408010003080c2d010a0000104075400f42c1c0a00340580d43c0d8036a864007096460b0300c039100301c2c0301d01110000d0080d18101900001d00540107944080f0300040100204000ca84013030701c0761800340c61001c60410155015208003400c0d40090008141880700c0f03009001d04541c00001e120240950001701804104142d00341020030000d0729005015071252a540a592445510380700c0c0d104490500f00c0e1400c200c01c0e002e5280110b041c050061003440a032400180d40d40c018907100310007041c0f21032000319580706003400361012920100c00040e441d4980d502d40ca00c5c1907201c60320a613070a0050141c0410105c40c002501c50003413001031000581800c05110f40c01c402c041500841c848540100f000800d03c2e0f03400900c55070349603040030000015000d0403802a0042400d50310500c89000b0a604c0755041c142c02c5444c40e210300c400a603920008026140800c5140d00c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 19382110 1250 19380860 19380869
    0x4080a02100b130b150a0503010810020c0307030513150e090f060f1201020d06120c09060506090111070305060109020901080a0606050f07060e0303040f02010e0109030b06040209130903020c0a06020601 88
    0x110490f402076000d80140c0003400e500030702500d03407210290314001c21040790340640f0b0b04401050000004204040003000306096103021804114204001401c0150301c1b4403540030081c0401c00041803411007640c1d0242c001000f0302002c6401113a14076500d4001d05091928604a4440c0c491a00050003800e0103d0000c3d220b8070307000b8480d0148480500410242840d00108169a598203111f80c0604545a20509020b0b0488503a01c0b0540102c62421040508640e00050017943c00c06804002685449060715020082402c000320006070800d4180d2a01050361310140c582d00c10700b0700004031440d8550060400e14002c3c0e07600c3d041944c0d9078a020301514403900c208000981c041000c1c0329409000009007041c5407140310007088031802d10b8991891604141c8040c1d40301d0a10014000456070860a035041205003070070008043da103180c4854040c2c42004103401e001c0c58001910611f15a9900c00510101e0a0080308000340252030074000c0d50380301c10103011802448010b2011400c54000200b982c101d0303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 19383360 1250 19382110 19382119
    0x90903021b1302070501150303031508010e0709020706140412140306060a05031008010e030a030e0609100f09050102040b0301050301050c070f030c020a150c05070909080409020702031504080a02100b 87
    0x35110290040000d5004c01c10580d001d560740c0c80400d9503054095900402140030355004504549100d1105c0fa159481da804850168506409812104030101d151000c40340c03180b00060302d40d81d8504040e805002d64040c2c001030800d5140070031082040c4511804505401b66545601c000348041c20b880c424030042d00c9980c0c2c46a0b05100082c061407141c3c00640d0710181049040d403440c0c0e0354800f2075083d94800d9072994081e800214120005940c035200364441c120580b001819103013801146145c44460341940b88a5164a46034012101e07030442d0080301d40554403000840d5100e541d0307810b008a41c0c20a014403840395017400d011480c0b16030f410307095541840d0000d60701e200c21b000c10b950a88181010140407071304940100e0b000692204220714101c2c12049640722221144006d00c1c02d542403040b05c3d00444006031600d84d800300130810302402e44003a61401c5000503501c010a0002038603010052003000d2804032120200000c012040b4003a140002e100e2302210030060070701d807407007003903410000210782c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 19384610 1250 19383360 19383379
    0x6020106060c020d0f0203030d0b010e0109031a07030e0316020f0301060501020d030b0a0504061d01080706020703021201060801050705040305010e0105240d0204180302060f1605030c04050406090903021b 89
    0x54500442c4c070121491107036810b50242d042503404070b41103821130300181075441e945d1602e0000303d5070040010302c00d10f4024a05490982d09503654103180142da803501c480f00040f20400107442c0c034000c2d0700c020b450b02c1c42c0d1022207498440382c001d051407105018600b00d0051040100c80601801d0502403001591816000b9002060030440100e0003010000300711944040a0800020b0584991284201910b10410450050b070809501c4034418001a8060919540848000c000c66607004c40c007002560350440d0f650305400c0c1801c8545025002c20340142840b5440c210a0154213500700d00144100d91003103000344280422a5107190032039200b201c0d01a02c41080601c55a621120a0801d60440e48c00034a0b038031148081d030b00070404035441116a07450104108d0a100b05140d01040002d07403007031171310000503101c2c071788031644000c1d80d80310012840034080d011001c82d940501c1401513502411001d04104009540c0c0c00158010700110241038016004601200040b81407004000300b1a54014011749031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 19385860 1250 19384610 19384613
    0x901050307050702090106030b0118060206070e03010902090c03090706020d080a0b0102010906050a0b1903020f0d020a0e0901091505040c0e0901060504020403050d0206070804050c010c17120a050106020106060c 92
    0x2855840141141d0420608202a200590301c0c500214041c0ca2a640d0000b081c003000400504a400d0748040103c0320400b101c0c003000300e036a0024400b5480500c916180c614403100c1e034082400b500c0a4030000350f00048150421140110400140d03104a00782c0049407402d03a0b40701410b81c1c488856551000005000a00042580e6425040824558010700c000190181c05449480441d101a100c0d00c140701d03121b6860110b40d250480e0884180800d00b28041c44943c510742c00901c3d1030240c200410300501201c13a00718150341d602e1403d00e00811008003600c0051401002d898000c0c00c8503c02220380ca480708072016041442445400d2056a11845405145040880c1d4000342e40b401042c0c1c2c0510340d22020082000d4035103001a2008520441c024800c0404058010b4200300c030040161040254501c02c000c08118001400f42030000700303013094845100c01c0e003880080c02c041d40f3340c090300b084000550108030300081509603100c3d050340801005641d0700e52200705c1c240c919610881d400101300481500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 19387110 1250 19385860 19385867
    0x103030c030908010f09050d03150e040501110403050c0102010c0f08041502040801020a0e0312070f060c0207230415081216050106080a0c050603010506030103111912020111010c050901 81
    0x911550007400c020b840e8680c0d448100b400c3d0307040c004a420400780c4a500f21010458200103805100100d41004d20480020300c034401c50390903061051142451056011400b030000030342c07028148802c0079440d25683c9843c0d0a182d80d4031002d003580c81e40150301c1e0441c0e010849200c2c400c401d02032040c50b6901c1c00070b500e40761a04864407141c5581c83c82601e5003048000307111002440100301c000f4054a8041d0850b840c0b004140c1840300e04640c05554000401c41000044d8a400b03880b022284d00000c00600e0041e02c1104a24180c0150820310501c2200050341000c802102e17035900015030110343c01d00c400418110b80d204440940d22441c541580306088a01c1d15040000c080d044010b2030300c1c00760b4400320f0360340c4400d425070720280c0c4074160a4001043c00c44c24822201c2d800006008292002403841d49080c000c1502440305105c054030b95030140d40103401558492203a0b088441412004200c2c81303440321902c03821900401c0e412404182000004a500305040c0030321740350130310181c0f6200e043c40c600e8401036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 19388360 1250 19387110 19387127
    0x50f0f01090503060112030305090105070503160c02060409020304021309080a110a0206030c070b0a05010501020a060b06071506050f03010902060304060e0f030d0c09120507051e091801150e010303 86
    0x4906004068102050b20740302044018020500008804070324900c40c02d000d400c855014103a6000c0d030741813004014500340c1200c1201d8100714003224102c421301c4a40e4040382c4042503000c0082d0312540c00240040c4909245d0061401a4001c0f1401c5202002440002c41203506007400140490014040031401c180101b210000c9100b8010648500c00b0203a400503a05500445080c0d800c1c420100d0700340140070348460380301d510290145003040345505000c0080d41c2c900080a000b025203850b440c4284054070b8150550f030105520040f00486405108040300c06007109001f1a4041c0c03540c840c81104c13030310b014010344840c190098441495612591103241c040c21288144251600c21550040000e5101f04000c0034000c5a00d900050042204200140804616444410340a0304d0a440c40041a808140d0008451049586c445542c2001180c405440b240c1c01800740d01440031800c1040c481c0c03d00301034004040c1c000008111841407600b04c8840f074101c50081450701c1c02044010720010f402519078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 19389610 1250 19388360 19388389
    0x60301020904060905041202070f050d0309210b0610080f04050114090102030105010206010506040303050a0e0a08010213030b13080a03090602070b010306150e070f0c0c0f0b120c0301050f 82
    0x252a0410715070208050310001d0707100d0401c942ea030764100400d0112111000e1091550b034400751525501d0410000c2e9a415507009451050074500c41035800c0500600c039500003811030040074100441001d980358860705900600741d420b4a508000903405203410b040d130225503a8191540c869a840b0080540e000042c01802118559a02c180b0841c000c658030340c54601c940a1074002580d0703581010002406c0c810b06a110b00d004100500003440026006419074410345911f29000c40061030307180c0054054465981b01014a520000b0340425801d04100c095050f00d000340c0104c5455210700030740301c50f0f0290074800076200110900c8100d01d218440e4015101ca43d00a40e805420201640c80d40d450f07601e402c0e442258801e41c3d48004913801400050304000400c1c64000b1015079207400703400500002c00c0480030100308540f0068120401c0b81880d008805052244080206552075498251803640007004552022130000700080c000396140f01142d0588401a00e00030100026006101122514640 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 19390860 1250 19389610 19389613
    0x20408031b03041d010807060e18250f030501290a02010605090a0504020906120304090b0105070f0804060207080c030304120204180804090b030309030604030503071106090a03140319050603 83
    0x4888074141501c4c0616200226590940d501d0703c40f445207031800c41da200c3c1052182809a400c1c0301e42c1c0d41c0041000e4645c4a500d5101e00d0703a01e0411039400842000840e1440c4440a8294140140e011801180e90160303034804215903600ca0f107429810b2164404100325118030120500d001001c1c0740b015040314071640c000450f2070354072030002544042c8100e9030711800341d42e50004c200961900b23100c090781041040d5945040303001c104130340e20b40342e2040c1c0c0210210241c88440c01601640300b2070031202e20f00c1c1c00003105041c1d981e5500e13202c0f00b207034000d02c40d40c80103100c1c801010902d00d10205041d81000313001001540780034900140c1ca50360001c0c2000599100e5030f1a40d40501e0145510000c00b10184250043c035078840c20282284110703807400a03007600960003403009240c147c80000d9078a0304a03402d0700341141c8075502c1801c00c036103060950148181c140200000d000f0342090003d14408500c1c800d44078540c0c685c41590303094400b808121840709502c5c910f4600c0310080142503014607080300f000390 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 19392110 1250 19390860 19390867
    0x10e1003020c03190e010305130c0312090b120a0b0307080304090f110d0b010f09030c0902031506070b0103030f0804110103090201030e030705100609020408030301031202010b18040b0a020408031b03 87
    0x302c403c028134040c00081341c00701d03034030400761348407582d152003403562115280b503481c540b8035102e860300005448680002045442c18050f6200741a0041d800c46008100c0314110070b81d07a0000c5082a62480425680c00f1003050801504e807080d4580403980005449100004604061030b081000d0302030b003120089540010b80e24408000c1c40080711000b460303603818540e008a843c94882c00010002c1c01c000d01d0700c10401064080500003e0040c1d40001304491340400050b03101c0d1030f92101240465100500613a0000c0300141e101c042140c03225a19040720f000382c54000e9052000001030758140d1003298014650301001e50182450360090707100442003401031400007040d4600401c0d0510b1135010070703410303269035010fa00c48540b42c05940c040c2c00c1c06010014802c0d0304051401d5030495aa0106020040c49424041182030f40e25200350301c08981030800801092070130241c40341c409407807002a101501c10000d81e90002c3d000c14018003c0b50101c441c020b0085190150b94051502001d0200100228900081 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 19393360 1250 19392110 19392127
    0xc02010807030f15030303021806090105040b070c0906030f0311030a08011205100f0204090e0c0a1a090414010504150e070f1e030b030d03110405120c030d03020c0705010e1003020c03 80
    0x280d815002d5442070311f0060346c0348881000c0030941520944a144240c0c4200448481a41d00c002503500b2507241280850326480179103044082d924154018615503842c00b0340010512445c400d616800c50b00a40741d45000b0548503c1c101d45030703c01d0f03504800100341400c0040200070481d07100144558012400d48040420b644c60250540b0010114403498a401150901802071070348588104a48800d0040c0140b49000b40801c130940d42510442440201c3c076a00c0c200c1d40d05942c1c080703031f40380d8100820400c019003c00510380c503c00d20038051503018030b00e000c0e0611080d160313040c0480b081c1d92035007545100503560600d0440300d0303521040c0e00204100750701c08036200c001078409542c00c0c0302285440104d003d2801600b80351416100c0d505d15004c0605000145070800d64500c2101d00f5503100340d0340034207200c4018600910304224800c0813900b5220740c00c84492001d0303055000d09141d501840c2600c880c5a511313001152400d1080c50402e901140708110070003018080d9004001100005e000d5a040c00083e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 19394610 1250 19393360 19393391
    0x30918021b0f0d0804020a06180801020a09090b04020903061803070203010203100302030c0a18020a170a0507030506060c030405270103080304021504060e120304180204050a060c02010807030f 84
    0x380d09004441e803021810342c607440c0c41071003407a03906040ca240c42d80c0d5901e000d800103070701100315125560501c5806600040c800c2c0220400030040c05900009554400a0b05c030024110041ca21030070840b5441c01f132003514140b4040c02141c201c048014014080ca4443c0c41510400c0e10150341494602c1c4002c101d0200182c0f800c5c0040c61007140c24040ca058021b256006160130001c0800d0703454851f0340e2044040c00719000c90040d90002210b50740c001622074005400c1078a0b0002ea202c00a06212000e80400036001c002d0707007010b0300c00c00250750284100d0b20f0342024047d20f802a4071048065801c280304c1407019003006600240801c204032942881d13070800d041c400645540a070426103544100200700010340c01c052200792581140313075645c1454245480f00007803507800e007813080c1d0b8411405450200441d441c1003080d01c0140c07505444810110360316100850007948248143c40c001c404000c00029400c2c010031640e8201901030315800d0182e5a9680101c0080410480156245a03075000501c2800c11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 19395860 1250 19394610 19394647
    0x109051203030103120305040201120e0307080325030b0a051c02060f07060b0a12080d060f08030a1d09060d05010e0303040305030601081b09060c0f01020c070303080a060303091802 79
    0x450201035542c1c2d505605181070034411441c14102454244014480140d0307010321290b0350480d02d01c0c1c0c0080c107041032500039800d40c4104000500649008030070300403061103d00c0d1082040200e0010030b12100b218640541c180c944006100d50f01c1000f0040800260074004500b03881c034007a050350741040e140142d0000e200782c0c0010100c9050311001080d100304100c910710401f0500e900445103400c1051420682015061012000030700740a000f0445520795203040e048400a40040c401d0a11401d84407001e940e500e402031409200050030030191001c04035001650284d42c000064a01581c5030350b500c007442a00c00c102081180c05650342e2024442451061003c2c5000754800c0e5580ca6490070410001418030001600307059240c61401c2e200f2195902e5401160514002030b07070322540b9000442da0803070800c408045071501f5540000748081c074914020070b03d903042c0c9109403500704141c1c40d1000c21004590081c00002c000c00c50103642803009099075044d09540c41510040036240010070440b1030b103410f4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 19397110 1250 19395860 19395889
    0x219030309020a060512040f060207020907030e0c0901030803071110020a0305040303111801112409120f0405040b0607060f0b120a020904060b01140307020a110a060e010806010905 79
    0x240c0c0c5030504821403070003c203140c0c01040c50340f50240c10001c01a1048a403854041c10041c40c17907400c40406030402c555501558009a00180183c10700c0c40c00003005030181030f0a10000c50300e03000d140ca00400ca440c0617613000d8186c0e6080f00981d41181e036480000d035004070f0f50041010052052001010503050180002d2100c4503091b40c0100d11030407d85000707000e403201610f41005a0405000ca0003075180344041e2081810f109180c180020081c8003401c40c00c0c90701d0700011450005800400c00d04180501171418010000c40f01150010001404010254002c0213803c11248d003003084200308a10342500b007158101d000500192500d84259585400c4540111003032a00640b651f0100700b10340740182e2038140f800c682c1c2e000744c20086581d40c001030001720020401000f039550380151000d181d1003280100b4000300740303140032030340d80c10504000385d600c51031050300f21090283c2d00b0541c00241001c0c5c6488049905035240e0a01c401c00c0c00c401580d4928000b0141c81c104092a14002441d90742c0c1c0003c41030300c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 19398360 1250 19397110 19397117
    0x20f010c0b040c0609051002061501090503010c09030506061f0c02151801030f050c0a05070f0c0602031209210a030b1c051c05030c16021e0102010e06040c0b0901021903 74
    0x180c646000a0401c84251b8407062051418903800711400e074002c942c85900601c41c50340b021441e40c1d0000141d03240c885603004103805600e02011004480e40040d0034505a034042c104803003180c0c0d02d080410034080401004080825030090b00e2075400c03030007065505c4101e440100900c40605001c1104180c64100400c1000400791a910140465800d0300c6081024030402101344032034a0a0903501c0940c2c41812104402c1210006040c014061100301030792640d9804051040b00a0ba1104000e65a030040051080f450f20158081041c8000001c0d90040107006101c3c0a8003802d1486003129098001507044018151a2050301550f130303444200b03c45500ba201d00c105204c50041e810040d203070207048080c490310004801e42170441a90014180e82d030120071502020340d40d0040c1001d40070210385035000290040b00c00f1025000b0300c406a00005140c40c000e0340204a04544903180d03c0d0fa807c01a42c000c0c0c008640c1820900002c10100b00800120354103004540301c10360903005000b00100c510b0f030141c001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 19399610 1250 19398360 19398383
    0xa03020c01140f0901050103030918060902030c03100e01030f020112020c0a050706020f01060e060d020111010908030f0c03040f020603070314041b0605280324061b030804020f010c0b04 81
    0x150340031800a60010a4071000300200d41c1556000351030215140107070074001c91070200700be0070b40b0303445d4005001616881038255240d040400028105400039120812100c850306030108118820302e00b440e049030f8211244040d141704503001500c0300c41c0350316032204a19030200480511042d0401001c01c409100b00b00600750340d4a85a0003e08015015140070640d0f41001000c2104002c0004040d4008004594110b04005140300513a6107102d034007449461542000382e00c00c1440300040145104d4484440d480d241e503500c0700c41c0c031012480121001064208403848000250800d600516032100c0d0a050001c2c0710b07070003041008200729040700c040380c4000220401c001e0440c2085a184010119420030b142400e5121444182d071008a0503015002407803402e00d4400f1511070381001f00038000000c89980c68403500c400180343c500060185401107000e101090030f40b1550860601c5c112a010b9841c40216282c541c20000ca00e050440d8450401c00b21346900c001080e40c21001314012445695030752003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 19400860 1250 19399610 19399621
    0x40b03030a0908010510240203120705030601090609050d0b091204031b05030111030703050c2a010b0901060e120c0405070903050c031c2708070f0515040b0a03020c0114 74
    0x25a54000c00300c52880413811b00030025044070001c9007100c050100d0118038400a4400102d01c0d60150400000b2004105810312408070340080065000300400ea80d0860f449480324400d840d00d032003d05c00d4036000355000040070041282d52010380d0b04110400c00f6a0300c1581d6000c0303554125041600191a41040d03805114404814152074100801007600284039100c0031120544c8036000c000c2c4480e047c5911140041e88040c8004200c50820b10b0380072070030310840c1c402040c0140d2400810f20416141d841c0c644002d8861502550306170403101103a540f900210f60980611a03034000d00851940380f0300c9480b030380700b000d59034038001e2074420307145642d508030041c0c61410b0840c0342550011a02c4d010350828124910b100c00b4501c048010000c441c1130001e0170101c02c602c020340b00b2072400502001030ba440d44010402100c08518030040740c864420750964191a6010030032420790113048040c00b540c0400040000303205107009040645400e0900605080c0c40301140c90a44180e119488034840341c4404005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 19402110 1250 19400860 19400863
    0x20a09050415050603040212150c07150b030c010e0f060313300305070c170301090b01050c0d0e060403060501080307020109090b010f0e0604031a060a050102030703050414040b03030a0908 82
    0x5803240c1c07070902d20141914250210300d20744000307040a8003c01094260a043c5001045961140c025014a1000c0c5203400040c818440d00100700031581c0f4400e0b6568080203502d00d005a11091400030043d100c180080c00042d5201d0900071503c07a048104110000d94135a606006140715903108011440b02d03411528204940801d06840d61020462070998890103080010111601a01d24100041e460301e42c000155490300401c50002c0a0b580400049001c2c08079100c040c6040350b515260500c02000c4550054802c0e0180b91146542548000492030700c0381d115010500d4880f00181c400351a05480e07480392410f841098001800a5100040e0501107584c0190800010a416881017154a0508000a00b10000b00d5409004c0008c0b0107215902c5541e6001103900640e4410014894802c0e89400684002c400b1900503200b94544803001445500100803258601c0c0d040d510b1a280500300b481c0e80c2e0038903000c480c50680103580c440003819242c4080008060250168407181d004902d4041002d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 19403360 1250 19402110 19402121
    0x50615180a0c0e0d05060106050d060905042102070509060402030a06080303040602130e04020105090909010f0905060f010f0b070b130609050f070609051503041502031003030e030601031713030501020a090504 91
    0x40b8003581c049013907400840e5000c500141541c40ea8034000d81d813000d1404102004d040c030360f08900d034503d16003000c0c040ac010300701510f407440c1000c1d035078940709030900040143d840c0c035902d1241c680c02080400024006180c05da000b5640943c0c000c0d800240310303888800c81440c6800460b0122182603000a0304121410340d40c000340c0040c82201006c1146180a0303000800301e0243d810601d0080c189500481e06498080d000301d00c0c2038564a00401000e41c040c01c106680320380696403a01c1c0100d03d000003284440c200d9402c0010340380704443c1113192003010340d07821900c0c1000902403009800003041007000614a801000340883c020340080c4828001547c442d403c1801503402042030003d420703010072103500da4442c0310f42a410001e102d940c6a80d5103051503d107080400030024400d910000405c1881250200c1c2d24040d280a80c0d1600c01c4505003006056444801380406082c2803256588201c1403c5604c0c01441e010114044141034542d030b0340d88081c01da801400781500491a02c1e070090040d41440d110302e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 19404610 1250 19403360 19403387
    0x405030c0f0723060706020c0a0203160311060702060703110715030c081006120c0c0b040501050702060a090b0136020301090e0304030c0302010e011e02060105010f0507050615180a0c 80
    0x1603c034003140c40c0003a940744542c0c0d00040c0f1060300440c00c940114000e10200351516009030a4803511400410550141d0076540011100c442040e102248030f41030003c2500c1146501821862070101e150b00c094940b480b05030100800ca11810102041c0c656000c1c0080007900c2154030089544c0e258183d01810020004155607544441400f04000950340f0400c41d2150b00d40c00350002400300030180301240c94180c1560041c140c0907078201804100141580003901c1650b16500791022501d810001c5025111040320160000f50020700620003804520f1a08070020100081100c0d40c00a50120100c484400c15802031011b60102c0100158a0319018540f01a08401d02461030103003982d40b12141c6540b1400040c0c1006a000780207007082c1d0052049500131041d0841c0c41c5204000081e000355144000d0240c2030000d040d1082884450340500300fa0713800b155112025014a5581c00c11004111605064032503101c1c0d404440007510245a100385401381485e90800700d401514400003510b4060401c1d00f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 19405860 1250 19404610 19404659
    0x15080604020f01080a060807030c03020306070512040204150905040c0303110c0618030109020307090509010b0103110703081909050c031608150402040b0603070201090b0109060f0e0405030c0f07 85
    0xc000060340d0b00d114040c9503039024201003849803220342d094030007004580c110308180e104412010090000307860045045030b10071401c5410700d5560107412580d0340200b0603d000e5411a01006c2001460f003038006940c003030400c90038900c80765034442c400d000350b850030340d015551040381e0f03030042c0b0a169001c1b10701e030027603801440106038908024000c81c14134810898011358040032248a882140e4081d0403007010950020122686107407179054803001440143c60451496180103000d010340e5020b40943c102d01d40141208505085c1141c506682000000300110615101200c1c840300d03d40c181c2c40340c10b080300d024500820f06100c14600780b618242c0450000c03011849040b80400c01000c0000c0c441802c5515200003048984640c40803401030500895010b81c080303000302c01c00c00d0055055000b01c420074040c4c2d0341441c451742da41c075021044503030302d001c1d001d6001800e181c240701203c080d50301c198000d44100e084a02d083d00740c1c503220f414101c0c0001101c0c81754111070003c1001d2031040c0410042c0e5992010b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 19407110 1250 19405860 19405873
    0xc030506010203070609051c170a1a010e0d080408030a08060906060702120c0d08120610020c190b0304060b030d021c0c0510140601090b070203100b0604080106091508 73
    0xb0b0b40e2800b440304021300300d42c2c0343c048200170817805119000041ea004a0000c0125403042400f420007241600c04000707101c4200005007142480f0301070805c0f006000e942100d00c0400c05001161150700d1076848980110034003005a001410710ba00500082c880c0d00f01858407032410380307401081c540300a80f2040c03181c43c12009021035559101c007118a403e6044400014501c5038810945c10003001408841d402f2480d50301450911004200030001505181146407940e034803482000714134030004e002c0600680c4410720071015410600083e01003840914416120103039510080c9604e0350081314211045a100d07100b800150804020300c403042030080c0058002e100122003800b0f8041e080741942010003009a0200b400e0101c1800b0811000ca1485014002c01000006645c00c0c40c030146c40d002d0010320356401c00185d40e025141682c101660080203041000c810b80801c102030300b880c0034403075800349081000051450302440ba0754010060310002013100007003071807003c4420956038061f1355140c0004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 19408360 1250 19407110 19407121
    0x131401030b010810090c020703150504020117070f0305060109051908010c08010b070206030406020906070b010311030a03020c12010b090103030221070201080403120605030109030203040306050c0406051602060904110d0c0305 98
    0x1149013105582000c100000c40501d640c0c0202d103031641d503134005048a121650f2000d12100250441c9214500030f88801003000c0d80c42c9152010014100c0d000c80014446041f4820464407a40142d0340042c014904139601944074000214013022101c4c03a40c4400680712420002420b0a0040068414450802009561505c8042c0c8800d11441c07800a00c034041c000006020416142d060303400850303025143e01d0712440c00e460031240300c003401c2c04240e800c244030580381c08003440e0001d40c41c4059035050340588411500c08003403040c1140032000b07484065417503820000c1141c59001513940214040e03030051008401c03030500b40d90900700700c080340c80240f07808000c40c0000d80d811804946c0c0055040c5040c14464190703c07112001001941c002c1541942044d01c05814581d002020b001034038090301c41081640c03600d200d0101ca5224501c80c0c400813400510100510080031621072507440d001500c1c0524180b09180058111030b0081c0c4101c07441100401d400d05104150303c00d04014400700d003810450f50514 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 19409610 1250 19408360 19408381
    0x602070b040e04020103020d1b03110c071a040302040e031305010203121306060e01080a021203040303080403120e010507031a0d02010503011206020c01020304050109201503070203131401030b0108 86
    0x2039004a07802e05044002007011644030358115a9080000e9004029103040a241c0100b041c0d000c4400100003070600907810044010355088602074801c0200030164185806c02f80c0344a0300d41ca510702080341ca0240000000341e20b81c0c0c000c0c8250720741c10700e01a40e0744021002000c0d80e203a5081e0012811913005101c400381150582c2240c0390815021020700d03101d4082c1e031600001078a40c07a040007607594845400020301000c0040c40c841170601c00c84141080d0000b00100c02d81c3c034012448061b00003640100840c003c6400303001c40080a81c40d5400200720031812160316800e4440561385500003d0341c9610703180d0202107000750404042c00450b18a02e103160140c000802900040c00360700541121140c5920030801c4e554111000890414001d54680c506828840c0c000c010303480303041d942d03402e8201d008420660301c45000e510000d0024680aa401084441703210103810081c40390303007584005c01c0450800501641c00c00d004000d8044e1290f03603001194001001d99a0a82c2a9814460f691040c0080003c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 19410860 1250 19409610 19409617
    0x50312030c040b030c0c070e06010210020306090609041b03120801090207030f08070203120406050601080906091203070e091003051b01050d0c050405060406050309060c0702010e010f0306150302030901060602070b 93
    0x9007030440f546a031100c0d01c0c0c40d0168031502d541000a07210b80d01c40041e20003160f170300d4144200000d8003030721000c5450b0880c0c14180c0c070044070002d50040015000941600d0b21864041c0c0042c09011010038129400710035001e2002150000d03200151008886d855066110790940d024188041c015403e03d503c5c2e41d0f01600c05510050300100344120340c00000c40c1c1318030070401e4403108118010715900c1130810341441c400901c0103503040c500141008002070b0051074001141c50003001e4103401490300d170480042c0c01e107090b0005001001003007030541502c40c80742d5a2181d024001c21000b124000d0452552410360710300440e02104d84e10382081244e074000c55a82203003d82d001d1110507240450064580035007201c030f62189801150b40114082800701c0c56075403140c007440c0704803600c0c0100c500f10b0300c88103600049070054860003400121a0384503001507510480403420b00f170ac0b03141004180c0035110310402c1042d2083c24031160000f580403003040340ca0301c02401034000411640c00504030260410440415911 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 19412110 1250 19410860 19410869
    0x705010c02031e0c0d03030b0307060f2c0603090f01050906130b0603100c0804030f0306050a1e05060a05071b0f03080a0e030a1202010b030c06040510020717010204050312030c04 78
    0x40b83e219100d02c000c60138840c404035042c000340b030050380851901d4041d00419501040c2d50091180c420045185405003160104d240c0300d81d00c50801801c0020052030300d000090905141c15210002002241d80300d41000c2d5000d0b524507400382c2102107910250130700711040101030140540c001814000007010103241c4c04001d5400140307400f4107948610220340b030101c1e0342c004005868a4076200b51141544101180d0086203e5500c80003104070800044003501d4050207070036809581d060003040001204d00c02c2e82d004690030203120103c00d60301c00000d141500300f170980e0004100001078400c1003002da045020104400003802140007424040e016107540c00d20300000300103200001b400c0885074010b402d000d0b03507208001e00301c0f00102d01d03e00d008010101040d61440240d801d103030f605022890040740c08089984050030b8203040c03618140403c840d141304280d00e801507020300c0d08040707070210800d40340c0c0400d104401e0015070340d285040103040c94090001864940c00c40c00340306200b200b000c0c0c0c40480d421075 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 19413360 1250 19412110 19412143
    0xa27050607020301090c030f0201080109020f0412020d050105010306061802030412080408120403020307120e0108070324030b25020c010f030e06090106030605010501030204080a0f06200405030705010c0203 90
    0x1c1c0d20302e202080c01080122000380c14980000c00001c10082d00d0781c40c00c0b902c03502c00c1e43c901007140d070799014600070390091644401d40c402c1c06120a100307100780855483d0006000510f1401d2950722622001e00b1201c1c01e0f0019940d01d62981d005000d061482104646050f122003c118a540340c69160201c0c0c00140c250710100b00818100030074107015207941650788000c480451401503092524020307649034048603080f83c8080c60303442040b102a010f94403198188506840306902c940e41c04d01c00320010004880307040104481c0380824442c40da1141c1c2004081c42c8030700c001c1450b1b82840070140901502008403990601184c2c2580112281d010031400c42a00d401c1c01c0010b2200e9119205501400018981207406d106a50403c036000105411020460340124010001d82e41c03118011002d80c0700794002c640c003070750000400c44001180803407514059030080c60f00048510307038108446500c40e4440c510b200040c10200781407002d13203000d000c034000510003401d1140d003805456000c6034641c5039043c1945a076 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 19414610 1250 19413360 19413367
    0x80a02090c03130804090c030b060301120f0503041a070212030306010c030302030903070602030c030f10050a0b0d14131208040201091511030a030f050c090604030b0a1503080a270506 80
    0x20030500040c10100c01d5413062090761100d0304c58004100030f0441c40091000a420b01d42004907e04081003124181c8c0c16a0b07002c40300000c01c42d15103840c0f510b9880d0048032144401c100010b00d140382a4450056000842d0f8086d6459842d0700421880106aa44140140c1c000b00f0600420b03a130061018480300b6450304001da00d9030340d03548440e0f095000e21000948070a00000c10810400c20103002036200f1007455208100549503442107142056050094039000400400c050000c0c46901001c0e061074010781c040410800303607001c5040700f801c109541600c400c1400502d1442000708100740301c5001b07400d0745840c15a034a8180c0000744080c44902c80d5503038200140381204803a600c500c511520084160084aa5810494600400424842151500c07851619010401c917200060849020386e00007411503007010700f0740e00e652003c1140a07040d6000156520a0440300501d0103088000071401140c80c50303111a04950045c1004500c034406805c101442d481c41c0c18200254075005055980580301c1c940c0303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 19415860 1250 19414610 19414621
    0x706080f070504050907033306050d020c01180302060a050c070f1b0f090e060f040b070c1208011719030305060a050909060601030b0d050714011209030801080106080a02090c03 77
    0x546100f180c000e103412100410400c2052900b58000d03c0b000d00030311700a06686181401d0040710184c0320714810903040942d510403c6042d03c10300203001da0140b18480103103800c1e07884019500b15401282001c02c3c3c0e82d0583c40700414180c041c0302c0c070f40d0320000c6503009004500d4a00c0115103035214000d4001d003056071581010301170060559103421208401e088060301c2d81d84a4007404910b42d0070f4401c201e041030030321042d0300c625803001c40c4240c041c2c151204040900c0d103807641c5513000c04600900c504100810402400e010400c0c8070b088ad07c460b1001c2c0c480881c6541007a1180202e00856410099150b000740c4a501c4034001444802c070401e0f8140c580000c03182c40390b40004060440700d0380106d0b802001c41c4144400c0407070110710640611003d8030108030980600080c010300089480c400f40842c0c01002d0b00700b00e03540c88100444511401407411a1542c018840c440d01143d07001c80381540050306c4d020051050300c909100e090050044403000303254060150307000070701c541c1c1c00034000042c65802101260 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 19417110 1250 19415860 19415867
    0x50a08040b07120f0e0f03040305030304020913020310020a0e010e010206040f03030b030703060b0432040c030212060702010606110d0513051807030b04110d021608030a0e0606030706080f07 83
    0x1c40480340480600035069845a5900078111170440080176010358070101e00f0b82c45c4000101e8040326800000703103007541d58035020411841801003071180000102182c440051394148440e80030703181040c60050700e031854144010f01c0b0301d0f005941d95041c414120807041240e030300040c50f10340c0254031040c2c403034840000703103021400f4000007002c1940510a20034007000b0007c0c80d8000303d402d144181c604000242c00d0304410111f0080300c074401d003003400190001c410700a0000c02c0c0113900c02c5c051501141c5460350f036400300304440d45c0300e00490003d420040500200c0c0f0750a016407401001039203091b07800d00c1c030000007058490a0402d084070078000300003210b80880c000500607400400000f443d81000c00c681080039204854115951000245055411089887c1c9407007413045201c01013a0030342c01c0022030381c0e00354020745c0710702c049044401c40300450000040842000f50720540d194580030905904800f403071454024080c5c80c45100b904905801d00409038000609030340954480d0790740135207807a501803d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 19418360 1250 19417110 19417127
    0x5100c02060702040b090c0c0114010b07260403030302030603060f0c19090e04060501060f050a0e010806060913060504060909020d020907090305030c070e070e100e0a080a05010b030d050a08040b07 86
    0x2079004a01b5004001403001458040e02c2504035080091001a544415404807140c3c02d01884550a00030301041010401c0c84544401801050307001c00481c0800219441894009a108600081d0000b04005503410700344a081c1d0440030a8000c2207943c01c0c0410900180e010b142426050380d44004030400c0118031810565000f024420700000060400382030003030150009004090111b400750510000c203920031030460300c0400c96a503486a034046508011903810501411720780d440441407000580681d600071142280c6280c402e000245246454140400d0701d5103540401c807580d03d05014800076883c0c0e01013103050a82c2c110f8403100d450740ca0000980380010542c001602d10711006c141568041800070352101681c242d1121820700d07540300c0d80d04a070800b07602102c141c0c2190500001800c01c2e4001c0d118680448801020a007a03292181c18051504841c544103031200d80d102d090066141c1024032802c00201c0b4146041d030301d029a480400b5200e41c2c00034000800003040740c00041c070f8640c0308201d00c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 19419610 1250 19418360 19418381
    0x3080903010f020412050c0306040507090f060806090f0d0203070803060402090402040305060c070302070b0c1509010e0d0801030606090b060a0507020105070803011d0105190504110409060f06030605100c0206070204 94
    0x2c548454417503042a03035800d8036540884040c0700e007001101461038009a031510075a07102c0001e045141c1000d4000024100d00b84204035625152a00459640c1007440030501c80e850f614024820200d07046002407800542002040c10354000308401c002040380c4400301c075440700c800d0f00c001d41c0d00c0350540b003c10001d1082ea0b10161450007102e0070700105054546c020554503002c3e9089818083e200c0c101404c0921401c0c9040e0341c40d5000200507503d00f2640c2c1c1c0c00d00d80c000c1e481c4000042c0c403c0243c0e540f0b8105824440c99000260400006004015141c81340c40d010b0803110360b042000c2012007000c40c8031442400109000e100c00403444008580c414000c481245510800007516560344051003403a4801e00c205c1d00d10b404190303000205641c00c00703641020101200881c0310318500d151209100051000340c00b1425008010400400d8204107401110020111915031040d070310318200c0010211b640f140c02103840b41b07140f8411480444d901480300400e80d601254000d69440d29132000400600500d142c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 19420860 1250 19419610 19419641
    0x3040504020f040806060a0509040303090201020c060a17090102030c121f0e06010e01031401120206070203010c080105190602150a0f0c020304080f010905060f04080408060906010911130308090301 86
    0x901c0c0e004901000d01a20481301030000b242c1c0c0d0b940300d80d020000c0310401c0e030040d507801c2032001c000200828425045901110b00600503600c4007003648001c03c81c5640303c807075038401041030341854500740502922101d07800002c0500860650810428817140d40c444e03a941c0c0d01c1d50b01c036090f01194002c001c001c100711487c41c49101c2605040e5440164800300c240071614a80451b140d10901219075020340103042465080c0c1071281c00d05d80c2031480c03003402d91000400030f030b812800500084005860910421100e84015218860a5031400080090b1302001d24401000007002c003104008143d000901c10382e04962242045d05c031a0b5400c4690030050040b01c6403181c40b5420039254025058002c00200242c1c0c1d4003100b03030b9036a0009495001d082c2ca2104400034204d91041300025980e020000c52103400511410340a0b1400382c5d0b65100030320300442954204c2040c3c10500041000f102c0500c5101419032000f91824284052140145e00c0c40c0135520001d01100b6001031083c07031075a009e500415040c2003828 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 19422110 1250 19420860 19420867
    0x309090204031a01050907120e151003050106080a030801060e12010c080901050a020f0306060304030203070c0305010606201005092a040b030a0210030e01090609050a05070f12020607050304050402 86
    0x83c50b0008154400714024040310b2440086060b0401a100b21320440c1320f9110403e000b007104034160002c1405810211090003860302c40c00740b58454103190b074001c1c0f508400d551141030960400500b11807959000001940c401c0e555400025000824541120418200b04200c403104801141400c01c4503e280d01003135203041042001c06e60407202107030146a1000081106568101d40300c3c00724401d1550f00c8881070030900c0080c201e49001402194082e1291041d00d083c80c8480d42c59180b40342054200b1100c69444410074841a940610800107802c88180b100c442c1d0686e80c801c10787c0711400224000401900d0300000340402e9010014441c03035070019500144014042114145120041001b240c0300d0350920103001d00c0e61600280e0040b000c1d4004141e12610708501d6402d07001809212000300c01365490f100180080380d124400e40d40c1c000e0040011b004268114038010381021410342015460030506c4505024078080724030071030701c6958140c44032541c0d003a03681091451030103268041540f00d0b0000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 19423360 1250 19422110 19422113
    0x103090f08070b0603030c0c04111308060901110a08010306090f080a02160b0403050304050d061113090b030106242705010212030420040e0109060b120f0712030909020403 75
    0x70009000351800b4102003181c9880300c00815031244541000d620090784000f01c071099600d07040e44a0120100000340c128506281c5035010107c4124580c403001954004d8002c01c4107248007070003004a204034503180d452919244035000760a110041c040a4070103035540e0359607401c0107d8607107406881390300a200151076003425a4001e55407002181c4009405800c0c0100103500040340c0309540c150b80e4041c024600745414942482016004501c098881c0d54491040e00492413428005200803c3d0782c40c2c4444401341000e4921040d0703042030260034000c7c3c3c505001000003402c26544001c810b07541840c0b000c0070b01101c04046855440e030141031003910640c2c1c20240c200481c0c130703404942150400e07000d40c0c3c91280c0c0304001d6100c40c041101c0150500402400f0001047c072075070f1601c03e404d01c4c002c100064500c2c20b007001c01e003110807030130f8211000c0340d86e40082d42c3c0c41d107004100d074050703c4500701c020240c1000f0100c61a03210100c1d44502942454550b1209041600a451510150111100031034507280d0f01d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 19424466 1106 19423360 19423373
    0x6070605070c080403060501050406060e0a0e09030705030c0c010906020a03050316030f0e011409070b040b03070908060702060604060b0306031e070b040e04050c040b090c03060103090f 81
    0x2480c1c600710000f109000504040c41c0160b41c0080d5540c10f220902c41198130300d801440074840414404040741d170310f001106081e00c40c404100c00d11526801c84491850003070301c40080942c000814a200103120015240c80c3c0170009a84801500e682c4080580e100d02c10380501a00040c41000011f10b03400c40d0f0212070f91509018580007a400010101c500c0c01c42d58166041c5115944600508064500c2c5104654001e14610b018100540c94210a402c0d50310592140c0c0c10000c001000040e0114040c402c020020620141510b07280c0c40e050100a403102c0049803080c0c4a28a0a000400d402801c402500e115810140003020840790a41850450b1204002400c03014411584003240024070503000d04010a10b4001c500800c1c20907150440c1000190035140e401203241c50070803501a51494a440d40150794a40c42c990b40b038036540f00490280612010107058080d003039010600f04400d = true := by decide +kernel

theorem cover : BRFrame.Cov 19244610 19424466 := by
  have h0 := BRFrame.cov_init 19244610
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19244610 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 19244610 ≤ n) (h2 : n < 19424466) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
