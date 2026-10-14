-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0590
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:37:05.411422+00:00
-- url     : https://prove2.me/submissions/f218e2c2-9ca8-492f-b0b3-2c16495176e5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 105935251 ≤ n < 106115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 105936501 1250 105935251 105935327
    0xe06030601081506040b040e01050f0603151e040f380f151309080901090608040c030b07120905010f0b0301060b03060d1410050901060b040b030a11090301020c0715 72
    0x7070252001c61008120350f52301d42034032030544da0340e803407030780301c2410096142010002c1000702000350309050150705081c11a000c1860b03140c100c1d030154440a50000c0c0c04d200a1401d140c070031542c48600303410000d050740c0310344903c0040d581c441010003015110a6560840030360b4030b207000d0303c1300c44202100c64413040d22800e0700f202100702c03854100c1191110945c00729410710810307014038042d9100582d2014607200040140d10603410a006204110050001040301c4000050540741c0c813003c189040d0726049001e0301c0c1003807121f21201e001428030038104104a0190442d10210040710000d0005095003001c060984006004030002400c003400010315a03c1c00030b5034114454007904d013044100b07000101c2d1500340711615545c0340c4001c2d00c170428000c1c807260900c105401006003181850034103042107192240792101034143d4514a03102c82400080b5031410382282c0240c0c2004008560f40c0384101c51031501d8004a2003200e0800040322801c0c01d24034081c2086201104449100c035060110741c642d80b18040e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 105937751 1250 105936501 105936521
    0x7050a05030a09020a0506040308130509100b03040309090c0c020307240516050d090e011203120209010e10031401170a080a0c0b010b03040212010b0109061d0a0e0603060108150604 79
    0x110717001d440000c10f070b1180401000076601a48207941d51340020b00080b40b00480943c0b001c0c2c0500210401c0080c0a925003014000f0349800154580e03981d115410100d42e2003c40360085020540b601002c04005908801d00405a5200340d056840040d0364030b051102d841903d6020411400801d00503940651041c00248091405403010700300340006520760300d260105d620300c2c15000c6000554240503c15080d0a02c2d8010712030030311344090309903c6607001060401d801e4000d11140c1d40210724030005a0040070a0b0760002c00150241081402041c8001c0c00360a40a0f40082c0d5810002d002241c826058410f0198084588004250300f41c0690f9a0207215030002d041a000c01c079504503850005450031b02c501d03000303140b071244080e224141030040140e5440c0421880c0345070703031401c00300c9c03d03c03030b40c00c0700e40070045490b242401440e1640c8240403042051020580e10752228003c00d01044819802c2032a40c000c0c0300030b9080390301030382c1c0304c49088d503580f440c61440d00b00c4202e43d040001c1403441d050f0451907903c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 105939001 1250 105937751 105937759
    0x703030f140103020307140d02040e0309032d0105040b0c130b0d06030b011d15040e01090602030411013009050d020a030210060b18010311180907050a05030a0902 71
    0x24101a04828007141d40c801d00070207000e0a820010425480d04100e1200038202c0703a51460001d03900386000500d55502c03c1c00c001c0c051303911200303006c1200c42c0c284142c40321000702400341e0b1594541c0b0500c24200200710b55040314030008001c1c08823200c481c1481414031655200481900d05e4440700c000d424184c22a0b405200115501000800c4035051080a00140110010045412030651404005002d0f058204001c940e0200c1807004a0040350180303103030007d10206030b461000e01d002e800724020300880ca0148c403003582802c04003000c105540c1c1c001e45c131407030141390381058040b03445004450107100300901c0c4200c000002e04050200074443d0000c141580021400510300c0c0482e40d40e681007404003012440513030000083c0c1803e064046c08546085807903224100301c2c0c1c1d414081400c1c500d0103448091034410a0130789507028a41d020b41e100d10340000f07002c210a80c850105e4208a403482100e0516180a03807056400302e8101802101514100350349500d0b04d508641d102d052175001404c010728180d82c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 105940251 1250 105939001 105939011
    0x210904020403120c1203020a02031b0106080a030e09010611030307111e030d110301050102070605030406060e01080321060f010810030b16091505030402060307230306010f0306030302060c070303 85
    0x19402c4483c615224034162241026280c2c90b0400d590340c44035520000040c10300400034501c0281d40441116002c1c120800c0c0d400803d610580c1003401172805400c46101d07442454401020b01d50400c0700d4005c0d00104441e124030702c1c0c1c0ca942080328101005440c010050340203201050005015a80750715103c5131100445440f501400d206000142021500410340c0d04001030910b92103105001d1483d49803d01045d0a285525000000795100c0d424031654040207400300c0030508000c45900712500912074101100790b44c4d615110040e41707952021560040f50f084203e0018243c0d42003000031881858002e040914034110840152521000140750b110410016000800001e5620580c20b01602c403e090744003805810b61000340007542c130350300007007210841c540207401c45a9116040301d900507070513101d46480f030301d450b0070948900084030100a92017550f070171184055503000c0c0285108071000d9948003c041c94030030003a800c03620203002c0640180c0210b400a00300100000c001d1902512901d80000c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 105941501 1250 105940251 105940253
    0x807020303040e07030b030f1213050d03030213080604020d0f05100903020102030108070501020c030a171c23060f010815030a061d1203070f050715050612210904020403 74
    0x30560380b041c0c01c5281890340d51020302c900c20b41d2500c1200700108050f0014003c10481d450410354034200383c40401000000022141d0642480d5038401004040c040c004800c03009071440d004c2c010313410a8884201c41912030074006620b4a0000e41540600d401400340c030120030b003c2d00c4080072a6200748003518588119100050f400c8054440e800f100c6011760300042c2c0b25410f000e9058204040b030340c8018110f5200001c0100b981d070f0b000c601d1950890340124081421310160395408180d005444581a00382e0540174111030200d80c0d60007090001e496031154a56840c030703c2414900401054508179088000c0d124402034550203100c01b240c00218490420343e0080d0200c001a02e02070440c84202c41039500c4001c20300f04c3c403039803040202d01c00c91694082c0c40c003004224010400e501008110340e04001c808480301c5901c3d40500119903a0741d400003041c0601e04003401501c005000162900d50043d03001880004d21311401107118209203244ca400e11607010203c00c000a403582055a80382d034029804c200c000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 105942751 1250 105941501 105941503
    0xb090f0723011e030605030d02030c061f03082d180f0f040204080109020a0806131101090306020a020d090b04051008100902070302060a0e06040b0129180411040f030f08070203 77
    0x30070301803d5900440c2c1c060030407040c9801d182c10a11007105641c0244002c61141c4404500d1075407158050100510a0905240c207084102881d070000d400c0a00020382400400700594410028200404541c1d00e600d41d0080d2540941c0319464103800b40c480503500340c941600d0040c0360041c080d417004099205c10102000010100e81c4158400c1c0c21581d135982850341103040c000300b408010402d10029285903d05140c844201e0740030400020030b04080c1a001c000039a00503203078040955008a0110b485806040c3d01a6460070081c02c6880461401c085c0080e61038810f60848007615805003c8494107401c0e2003007510303820005071006a40700701c0000c001c6082c501620160000301e0080d0b00501041c1810043c110460304080d055980c2c6801000400020940b8000d0b82c504503101854188518503022013843c600000d401c2d85c0e4181c1c0200007940c008a200e0001c01803544807000c840400204e290078003029558070a52290109c1c0c25140d25041010401c80d0881c804030b81e029401c100d01d446065800030b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 105944001 1250 105942751 105942797
    0x140c0a060c050f0d08012106111206030a051e1c031b0c050606010f0203070606141c1104050c04030609030807030e01020307080103110406050405040b090f072301 71
    0x410014094110210074080100b01041864008001414512403220802060420305008502200090900418007d070b06003120404540d00130b80100f0914071001441043c0d035020201c48001143e83c40c01103080c92602046a0440300c3c0c0c803074010014407100389003407030125107248024040f0340512028802d50320300400c12004120810399002074803101d891442010761a03184064410000603103880030009600050303549e00400d09080009820080c7c40701245507219030040184401d05240000812602c611141c41c0003940403a90b400c2030035141144245060324840014004102140c130002e4242420342c130007030708101816400d524081c0c07030b51250000d890441400720001070002e003c2004c11903140c81950001440c2800940c91400d08200003003035800c0c10300010b011002c0714540700c44c441d0b44950000703005001c0900709101c0c600d45800d0803403842500b03d42c2c951342070040003640c01c030300c3c00089200401e49070b680b4582413414020203c0d5160382ca8003404034506102d42c030b07011407151003440e203c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 105945251 1250 105944001 105944009
    0x703051807080703051c0f0302130b0c010501060f030b0102060a0b0a0803190219020105070201030c0504090e0c03010e030a08010608040201121b020c0402030c0d050901020f0a020307050606011b140c0a 88
    0x6200c0b01c4d01d0b5140041c0390007501c0544d071840d40c03801c014070040720750310401600e40805645400350302c603101031828070061101c40e408140400e01c0011810440321040d00f2140c1280c00a449456200000d60410b40542d466518401e0042c0c2141c00010444c00040d4014184031340c2c040c04105076284c80e828200e1840c1c0c03089400040c41d222000302041075a5040251030803040e250081c00c8000140c43c0d001800710b00920710000d040c5501c131240010480e1245050301d0003028042710a002d2050441c01854498040c10705081c000d50a020b4504d940c200700004981226040717543d0300e030f141d038078041c021130b003040e00504100d04008000810100c84004c40c003c8452030b09140010940c050140750007e4a403842d540c2c8214010b03801441008038644810041d9030ba00481c09801003441d50b40e5518550091043d80c26524003280c01141300140f8a5000016113440d80c4900200c52550711240700565024102d018071020000511007048002600714500000d550b16140c2102c1c20300b94000c0000d0300e48180c6801c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 105946501 1250 105945251 105945253
    0x9050303090a0b010f270b04020a09030c0b031e09011103041109130b07030207020d080c03070209011e03080a020109021f0207060305060d060b0109030b0c030a1112070305180708 78
    0x1184100340504490018010000e541220300340c241b401c41e039098003041c6061113076074000314160b01d03490300b2010760408140c0c040000c0c421551680d205201400501e4580010f5418400301400841c0c8684140112405107030920760000364140300c2c4d5441c20002100070621101952144140394001003a00091070141d03114a9030000b142103400700b44044090001d140c0364000c64031000b4600440c03904414950004120320f80580d407003046001289446605100003404280f00080100092101201601d8024400c031800703002a6030b9101020214413036a00c04492140d40080f0810016001d10024410700e0284d000100b00201c540c0c0000f0441442c0402c03000000078800c040d000020f506226460141c906410200580d003417000104140803440c0000810f0240e840744100520381c01032004c07034015a8007540d40d0f2301070300c0e114a00e440d05401c1a5400e03601903041a00c00060070442400780c80e21581e8050030b1401c0c0d5621003030110f02030000500104c240380203401001d041b4103400c1c42220003401c1840 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 105947751 1250 105946501 105946513
    0x905042609040b0303070b0610020a0203060a1d030f03010e19140103030206072d02011407020d09050a0e0f0604020c100b09070801060203220527070e0607150905030309 74
    0x40c00b0300098810101c4018440c1d001081540c0005403503401644e00540c05036152a0303d03124101050740341001140f030107540340c8601810008982c04681110b807030021404202c10807061030754001d030b941c0e010314003a448501c00e040c0014040c80f0759140c00300398019811a01290042e081c0c0c40000202c840103000070180c80c41803401442419010001079800076414900b001c0011969180442e43d041c1a0226102100e480211003040300d1003500800118000c201c40c490031400d100002035980c00c40d40d4074680108100c903000180703c0c9021394805c030440b2514512005e0603640c12601031039000c3c0050074180d02582c01e1102d03c8034080f041022031200d0a0700720000644851207420044031000081003117003000522401070248682c084207840110103401a5100080e0284040c150083c00542203243c111100400007509005c144920101d4a006072140d0109a00c4820381110000030341324030180c01c02d1080241c0b400007000c010f02c81c01c03845907840001640103410398816056510640307100d59184c0c441 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 105949001 1250 105947751 105947767
    0x5060f07051e1506060c060108070f0e07050a0e010201141003021513050d0804030f030c02011206050109060f02010f061d10080c010809010b03100c091e09050426 71
    0x400c00961078214031a9488200e402d02c03003a00d980c40c11030503c0000c41111040104030641c0303c0c0307401c1d5904180180709a410030741e151072a01b5954403091042c00050b0201103c00503100b8041440140245041d940d910b29100c3ca201c800c2d07e03035110002c2841c1c11596a100380703d203100381907410700b03000d0880c00381000b000c0c0d0301e14010000c60b103210711120035003810208a0038a0a1540e01c914000311030081c1d42c0983d0f000308a007441c1c40702c3d003d10340c005007040001040c4401016440b4100c208024402d0701e0b40112621030032510070881c3c40303c2c06080e01040950400f40103c0b8043d5000181c5207015200100701003180c080d004094a00742e42c0441d102605c22620303170f040c8601e465170469000b100d42d401d0305074842c035100080340e6842c00d1400c0981840000804604481c400703412103800740f01e000e42107810b03444084881000a01d03240841400103001d008001c10503141c20881000503120300c080c9410580e00b440c103c04010140900116042e1a03c1750313400c0302d031018108090b280810311303c46458941c055 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 105950251 1250 105949001 105949003
    0xb070e01080a0c021009051f0b060405010c0201110d050901080f04030c080306060706110c0c150d090c08030a080601030f0e100e160f05090601050301030f06091511030405010b0f0904030e01030605060f0705 90
    0x864107206c030708e0b542050704269085e19100251421500300346030081581e0001d00050340c4070368038292091001d01446280902c4140c0140007800204003e03a1940d8013aa100e581c240da21580980d4000d0001d40041d01540200b907082c0c0285410000c010615403501b00c19a5401048810207030380c1e2200e47c0700208050100d404184080d20710701c00c003650311491564035100c980205100c1d603006211120355802c20350040c0500d407402a0064038005003200c0e541c0c4804e1801804681045031040d000a013450b10000c06046140548100303c45110000c12140603080c3c400000f03408407090030b112510548072580c00342d11036140c41400800300f00c85a595050f06150502c907502c940104144d0500104000400018a204000407149604020002852051440c2c02c0802c400c44040a021a9080c0880f8803112210140114040c0b0322440007007048000c1181403124140d655000154042010300010300800d001d50003e201c100e0741450b00107403894a40303001464540007044031410f1800040381c20703420010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 105951501 1250 105950251 105950293
    0x90e010801020f0d15090c02011e0e0c060c150c0a030e12180a0905070302090a08070605090139200604150e060c03070b070e01080a0c02100905 63
    0x10020000d51508200031650320440c8113241112001e595115200c01d803100c098003007100900002c1d1014000030191420083c00380000b21100e40170b1a0812110202410b800d201e407114001c0600d0207441c82100540800c88590080058034050b40181d00b1802d030300c1c01000081e80d1040010007070b8140c40d90042c80000301114006000c0c20b459511028000d40706580c00015074400c070540960381ca804500c1040860251042c40c0e100702c51403410a014080101d4158003d0107494500781c1c3c0c41c0001580d990307145960b80a140c03150b03c01080080060360241d51169698101c0701c1841d03c3c1d208074400c40c072107032803c101c1101e096602410380d810b0072085c2007000d0016588481601ea4007080d8460640c4000a40c1911803803040c00420180c03001d122500b079000350458160804010002a280c02202e8005901c0360320a0200b190380224410000e00c50f41e02549285c080e500c4107a4800c0c0460340c03003203c0000100703413030b0f0886006d44c031413000c0000395401c640c000c60700894032460140042c0900074010002000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 105952751 1250 105951501 105951509
    0x90c020d080105010215040503071401061a0f03010911070f120e01030b010807031a0307080706260a0f02070204020a0e03010510050121021b0a030e06090d02040c140a090e01 76
    0x1101d40c0d0010002603074002080000c400821445a61945072490320b2455441112030042c0b20040030340c46000c00348419480001207a840c4003070541450340d0041100018410170081442858090005100e41c01c1ca40e4000b02449040ca00010310300001074642078844178540d00202c8004680000c0c8281d0142c1c0031035621019042828140602c18071000044c21002004101d44201540c1e031160b0f0040b581c1d501d060a90510300a02600c1c2c0b1140c940c2c5059890782d10600444000c00d180b5906c004203004a00c00c02c451580c0281684d50b80e1f030315800c5090f000f4000c0b90900d01c101c0c0b9028801d0720050307035851006084200080d02c40c1c2c1c807959180400d060a4684c01007010945100d0714204000c1641c0003001401110404001e8504c440e18800c4039100030b00924540065000100042d164070020015030002c070075010f61034045030074407440100301191049541c2103800040c50204240181001e0304108100c44a40c10100c036044079804806400d0341201040000146100104010118046004038050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 105954001 1250 105952751 105952757
    0x405010203041b0e060f031009050303090d170117010923070608060d02040b0a03170d060b0f0415020a140a0b0a0c0e0121050109050a0e01090507050f12010204090c020d 74
    0x9071408524030410f2000624180c018221411030058969080c00309480d009610b003802c000303e900d0ad0602a03681d0b0811104000705204444604200034081d203000149815031003001c020f583e0070200c08103101c014a484402c0b00d9901c403942200010310004d480a070389817400c1410302d03c0c44407a841d0945080e800b54808000d02c003000050107a907071150300009000303e405407800b0490300c000304042901c2c02c406601c0500b06044480d02070754201c8003000240390f0581c41030010310141e601c540303035a6200d110707404416041e6503040004002034002d240007040e1021180c01a03c20600300c0c0d0701c0e40c0c25010704800340c1c1a15038205914207810411034024054200c0001542040782a03101e40000d4540e00c100103501c1d05014501b441800380d105030304042d07001300c03c029500f48055603482d10520041c04003910301c1e01003103042803150f003013104051054030602500310004295883c60542407018900351821000d0300800a46480403105d0024001400242500c50000501a00c0500c0c024148401851581c00b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 105955251 1250 105954001 105954053
    0xf0f0906020c1c08070f020108010f0e07080403030b040905030405120111090603061c0b1b0a02070306020d0b041407030c05040e0118140703050702070501230a0309020603040501020304 81
    0x16140e80011400352000c0165030580c038049a03425042801e881d5010300031302441c40002d2030703010886c044800c0f0302d00c5c2e0300c00c2e00d8030103d40e608c0f4132070001c29030101e001d00903800e0404800500e00034411100703240c01c80d00a0400107418103a0b480810709035201d04109841b56440058200861b00b010b00f0b09000e00d58040008001c1402c0e07120341c4110300d111b1304000320b10800b00400480c5180d500d500c20000341808400000d20468040c0c80e052400003011a0004540d00c0402000d211a14403132040b1845401254054181c00c1d040d591840003d40141c400c200c00e480d41c80c008862580c88500c141e0944a2007070254001030700e804800202a030740300c26845d0302044014001000440110303a01903041d0f03541c031a0010744c2000d0b2450101c0c001c04015a0081110b0322800a000d0342075050740c016030013070300c941c0e00792030700b25031200019190707008401d0f83c00f1241c0c90840c00328000342106501410030701c1c4081ca00441d21404a800144076070700140c1c2d09480a960010600c41008444603002c040b5403c20030060318 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 105956501 1250 105955251 105955259
    0x90b06190b0405060d27150501030803040b0a061a12010501020a081204020301110313050c030f0d0e06070c0612050106030903080f0703090206030c040602100203060f2701060f0f09 79
    0x4002d008600c14203000340404141c603222003941e60003800c1c00d860307020a819a803e050402c1203180440300401650b680b00d820308484410680b50282906aa0700b040c4003501d191100da917000300d0098024141054140d81c0d820100310462000c1c55960700c00710503084182c65005007034070f60030078400c180d000d80d043d9400b64008a00240c0d4071000c0e1104094082141083d998443c00400c0c0076084214682442040000401c0701194541c0380c24005c81d03008104480080766031009050341e803006152022401da11545131a1456485078210303143d00303240078000324140581d6030b40d80040d4071090341120000c13031130310710604810680750b1040c1401855680b5040c017007041d00e618094100c090182000000d070b2a0319001518190094100e50b8005501400f132643e00c1c135143c1c01000c040c4e00705008040060041e83c001c003180848500a8a0090074001c001c0214082c410b020004268103a1400c0c1842445c540355039510020b95082081c000e28113910f40342041400400010510ae45081c0d840d801c0c04610031041c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 105957751 1250 105956501 105956519
    0x1609090b01230405060d0204090b010f12020c0309030307060501150206010e0f090a0507060e01030b09010305032a0307050714060a120c0c02060403050a06110c03070b041401090b0619 80
    0x684a0140b01c00c020301c0480403030507081051095800158000100290b03200e4407402d80e500400c2180c0720300d4010405901030600440780f01400411000000c0c880b060120700e440b582e50300510030301c2c040004813481c0030604404a030a42d080300c58140c6849039288010091141100800d0300c0360341d807038030181400e0b60415181c01e000e420080d202040490750180081c004290400030b518105412400700d99942d079442000610200c04419428002130070b00d140a640303424030b40441811f1f06e80c0702000d141020301810304054030640c040004180c0001e26003003603105500500041c010580036002400441c3e04100f800044c00600110700d9001d00c00c204a01e940300c0740e100164a000d6400351801003210100f800088440590740103001e540840000740001c104500000c8070401c2900c01e8100f4011b125900350313000c546005030408510581c1080000d03900280e600c14005500600c20109406444102001d01342111403600c0c084880b070803000305205040c41c1c41100c15070303507112050f1240c0c00142410008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 105959001 1250 105957751 105957767
    0x20604030c0b10080307140705121e030f04030c1a0304020607260d02030907050109060f0e1c0602030601020c03030a0f111002161101030207020f0603090111031609090b01 75
    0x2d018140901c010409401075200350500400004044035101e240706e06291110402c00c8504003902e109060303000a09041500c44200305268035405400034405502111068212070881040307540420090010305035840d00280002e1400f0340d141c030a00e2401d000c40c40301d01e00507400821a80d10424001c200c0142d40d44411a80c12942c0030f004540021102040d10b482c0070807103461010184000729405210720346683c0910301c10300310101140c40a03036480e4010743c0c031469107010724000a603e41c010b007941c10380501121020f036000900203506030b50b05014103a0015200c1381d030031115260004103000381903074104800000800120050740c0b800018134409049000480d03400307000c0c002212040003001c2c6080c0720140d003007144008103560715280a1031420704010b40c40700803500054810308440055100e442a16007066001d03020180b1000c0c2c03041000503130782004095074515034990040703a070800b28071f60240d80141901c2c00d00c0d007420002c059000c0c240400c40e800c66002e40e85030100b240d401c2c2ea807000c50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 105960251 1250 105959001 105959003
    0x14040326060f060c0c13140c0405030604170705030f0c012301090b2716030522051c18090e03030a02030403020a1406061206090d0e040902090c030105090601020604030c 74
    0x4030b0f6076600d00800407641007080b0101000e5001c03420b20a11910043d00382c1042a5000114000388550f41e96a1000c0c5103d00850095541580c00000050000b1703130102644002c121920200c0313070800c1c0150b9152403541c3e2022a169a00b11000300740480304480074028030030401ca10300c0491201d0746042d000c2141d00b040501c85e0300c0d1a40d455494900c4c1d640c0313038100d480b074100542040000140402003400005000b050394a040c04c0e68414178100102d0344284505805021000c03c2e41c22454000700d101c2d8003008000300280d4003030280041e840c0c180310883c031040ca400103081d00c6602ca10a004040c4a129003607070b030b000ca2001c90801a00c0c004007080441140d47c00b030b508031401038690f01c4070b04089240071440ca60040c070021110301c3c1903e41010001e0024414101240c414482403000b44001e91156425550404e1b07540c000d54694460901440902411a1000d000040c46442c560002401c0c2d4800f540ca032800c43c200000144060f091603045c4a07031103502800141020f08190341c0041011700341c090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 105961501 1250 105960251 105960259
    0x209030d030c03180b01030323030109051005030604050f0712020102060a0f060e04050106150f0219140d0c150606081f05090405061f0803041814040326060f 69
    0x20840c40d64080c4d8416007400800c0c1c940011600c40a20b81000510028081a404109182c00c5080c9200540b4120343c2d6072180c48006030f0079a4640800c003005080d0140688a06800011001c14943c90820540c2c0c45207025400416a1040e491121810201d107500601d04c0030180180c0140585d80000f85a44c0041780010b0018803450742160103802015641c1101107068040e50601052100540207541651b00100c13805400c0312046100381c41d6844403100f0b41c409a003044413005100c2e220551a4001d682c01415464a00390388030400c1400c0803481d01c6c80c000858142000482401002e13003211010344504078040103801e0920101818012000317000c01115281c0d2229070824058030700c402801000b000d001c54202d800c091804548503482210307107040140442031100039a103110890141210700c0a0301852806003408087d1515201540b002100703e03454600321183c2c0c11602d00441e2040703020f60742d00c1d01601178443d1000340c00142c00c00c81884040402e02800441d1b603941c00300200584040b9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 105962751 1250 105961501 105961511
    0x60405090607020322080a0f0b06010503010311121f09110a06090513180303020301060e03070509010b0903070816080d030204080c0d050f070b1e1c09241406040209030d03 75
    0xa003003690483e190404100c42c01f0720804401044200d504c0444598418000030380c0780c0d030b07500c1d0045076940801d200161000303540f0714400800d81004036004003640101002d86504181504224080e0031030240e034801e409a4134072100c014000040c002c0d03000350f0703001c5441c40101c030701d800b0009126100900031688180c8003280c2d41e50140940d07034840c0e45a641009007841562005080143c02500248a01c4000c140a0a0180d45e00e01d00803d44805690008222011603420858101c84681107800301a816125030341c07002c80e000004210480e4402c04050304039859505055910f41410058a0a08181070043c403091003d018082a05042e02d102907480f0012043c481c1011403401c3d0003000c059889000304070300401c58000720001042d40f04500e1031904860003403414412410720a46030060512101c0c0c54204000c4000c54021000c400e00a240710f10220010850400c400354007401034000045e03845200e41c1401c5214234417103510030421142141084151800302c5e03102d0300c0442105d410940d440c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 105964001 1250 105962751 105962797
    0x3041112100c0203040f0506160605060402070204050112030e0a06080403050d0207081303030f021b040b0402040302030d0203090a0501140d05041b060201020403170f040e0c04120b0604050906070203 87
    0x1001007030344003049040c06011403880c04902944a5106001d03580c00c403d8138140104180c20510116401c080c031013603002d6100803860302c604008000150025500030740030424600580d03203d00409001e4120030b8500c0e00d11a096181c05801402d051000d81d0164558200802010f40c00001082e403098240c1052556092144d044400921170030000800031a8049041e0055201e00115001500d20a8071355046041c2c206506994410302d46d18107400c03078210303001c0d0f03a940d03030620740c000c00d1150b2400b410250419440360300190800c18960403500044e0710100705440e2031300c0d2004031074004003401c0c00d1640502d250001008418800e0707a140c0180140c80b00b002c101000014000064400903540210220329241e1400a010b5405403205840b1404400e80d055000d4005504072000102c030b403142540361500d0980300c16040c400007400e0306803000040c08000382c1c80c0000d2031079075410b61080780414030310b1a1860422003140c0024283c1021039014400704461700b6000012683e0250391114043c10f042d5503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 105965251 1250 105964001 105964003
    0x3030305040f0803181002180111070b1224090106050a1106100504050f0c09190306050a0b130605061803010b0d05010e06070503061c02010531090203041112 69
    0x102c08801459032800004010390391100780072002c152400355094503541c2c807101c4880e8069020340450350202c0c1c8a01e0044001940c090100710040c8005401079480c0e0f55034440701c0e8802c07070b080398544121800401c03040140e002e203030494498904888007405c3c10800350320070200b24a140d0502403201885070000340c0b1190580a80f11440d007000300f02007100d25610f0404614400e00e5258410309009906000c0403824a10000c49044e00c00c1488001007030a0910f14010042d45240c2d88009080800003000048040342c0070340200d503c564a000c0c070201d00c0c00101818440902c41d00140ca8000a1800405114036078816049400010701c240500000d207000000103801040e41d03041c495404295a210081000750641024069050480a848166844907000d90f03451000302e40b450707402030100703c40b180d054a9168489401c3c50040c54042d09112030b40b01410f4282d00c1e00304007a4540240039100308800000000c1440c0500344d10542542581030aa888c0084040d050000c030344540b20a0310240320603c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 105966501 1250 105965251 105965273
    0x20f0102131211130c110a0b040b07090914100503010b01020c0f040b060d09020a12030804020d081b0a0b060d0209010e0414030a030506010801060c030c2a14031b0303040303030504 79
    0x1000400200c0f00e041ca50059100900040750220f000c246c030701044101880021070748440e0a1b401c020784e10516600c03683d80c4031200000401c8034051100c0e0b00d402145048481c86095101880403080e5034190912365503420310141140d2029220307078182054040b032660301103100800c044080c0d943c010809084c2000501901d641500990044408645081c684c003064101110190007521840c000948880703049a21820565001d0040707480400800d0050529000d48905280204a80c604280581c0c01207100c4401140070281c540c1d000c000c05505028541d489290020f8080f0b8500e6180c03200ca42c00318064001c140308013207600c0c40040c006410300199008111044070301d6811340e9a2060f0502c0c0203401800159840c50004101c0c1c400030070654000d4100400c02500f40e115400e10312004e0343c40b648103c9001c1240c1e120100a0a099134185000d8000c880140008004824080004205042c50005486407840040000c0c05082800740c50100c100c4040c0c9400d842c021986554508060319102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 105967751 1250 105966501 105966533
    0x405151306090f0501030503040605030709050a0b09120102180103020f04050a0f0e090d14070203011104090e010b060f040302090703240510021218030a08070c06020f01021312 77
    0x5480030451100c48400c0350310200548890140421180400c0703509034085a000b400000c00e9548100030030703c0154007600103994002e4292a01000d010340710b03404030300300c150594440c1200610109100102e4602000c01d100781c40113400085003041c510b07080302d8030001801000c0a041c5980041c0458031f0321443c02c12100502000b0308a03003102613644520481c540c80c00d2281071002140800420b0b052800400c122400424a6a6007983c49407020241900c541c441c1c07408a91565950401500c40000f100182c80100030700c200024600c00924045800e5819840b0f0f0240300324810000441c816011005072402d07650182c034010000d51310703ca000e9000340780c41d140400c2215a030300009442c00148810341c0d0151001640e41c8458042044001e0346d440401e802d00b02c0714580706224140301501a60500b00c1401c00003800c40d05040050740740da008640c40820141c0f10444550418415a5010003070040d031101d80d08000c52400012020307540502003540295a00e000d40413040000348444002a440c01c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 105969001 1250 105967751 105967759
    0x60f040b1501120509030702030f0a2402090a0b03070908010e210409020708042c061306091e11040b0f16061d070609081203060411041401080a09030e040515 69
    0x190600010b841c0c6d480d001100228031900c18540030b80c141d07010214000c00c0b40d9610441f40f11080d03100e4240e8030040a075200e2100780ba83c1e401c0c80403007090340d554010080281542120a80d69086c014801490041c40c0d8001003110780c10003030807810112000484a2a00641c1150700c075000c0042e81c41e8511a03c216031000a41900200d8400c041c06800d0008000301c6440c4a580111138400750800086281000b030040050160440066042d061005420703404403500b200020700c80740c640000c1011950701c1800c154145102125060041195100f0810000407016580e402c0519101da4402e942c0f24902c1300200c408008210303031487e007d81c244010310840d8480d10500c2110210003041000c2069240082c105d4820a0380000b8598001d551103c1079071145005400411103283c035500c0c0582c030151800b6041070351170301c400032120300c118040e0000d00390200000081c90f02c08800140040800788c220a41c81c3c1ca494010000240c00c1508449448015a004500b50fa1604002141442004500c03504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 105970251 1250 105969001 105969011
    0x6070506010f060f09081b0102010b03030a0816050f1b0a0f031d040e210409090804080607020309130c11010518010608010c0507030804110303070305040503060f040b150112 76
    0x2070070507100ea0191180f0390340d044601c80d00d10004030b900c1c40c0603203d00e5849402507841410003842111000603000e8060002264181e040c0000c240f6542c0044a0080011450028459075501400a500000e4150300e000c60408041c6c5112003643d10070081880800301c00421000b07440c0006000b494555504961b4560074060389040241c42d002c49240ca00c3c0c10301030740da000080f80c3c1c940f510580003002840d000405401c4102c500880c0003044001c801f1500d110309000020f40c0301003900501d000c1070310801c070701c940700e40c5032036a628034082c0007900b07140954001788401ca0154940361410101a445094007145445140360305494603003030382440038000c0d42400108081640e043d004160002c441030020811141c0c2c841c21a82203540d03920f40c801c0003981c104101e0012034031400800d50043e001c1c0015004140079400002c5c510380c09140c00710701256000c07908001134a0103001690b07100c00003003100701441c5480c0d40d07810b000c404020315440c0311011844040281da40702701021504200c0355002008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 105971501 1250 105970251 105970259
    0x515030a060f09020a02060603060910020d062411010b0f1003020d0903021e0a0f03050903070b120a0b0d0221010209030f060912040e0114040b100c0303060503030f07110607050601 79
    0x3c041e5004890a0300548914000f10b14035040c00107900303200d9800100904026902c21510f840a0350100c910703400e03019200c1601140b0b10091501c0d41c45a1080ea240d01001d4290015015014200b5a18800100d1b40741019240250b180c214139484150802c82d525901d156a041e4254000d0142c0013805241c14500b00d00d610402d0703000600d100f41040918004188480d46a04640d83c0d0600745a00402c4c02c00c40d0340000d4000b80c003880280c4070104004090b034044680750311003900c10340c01103401f404511158105000d07100741c040c4150f00b40c0385015134040c81c07410503e801003140420b0425810760400203071000561420001c0d81625940b80303005040e81c03c143c054488440c0e441c202501c850301280903000b18a4410707085c04040f00c084460740048089541e05c1c0816802c0c41d148007400007604170341c03103210040803641c81c4070840300c11070620b0321980312102c201d0800070101c40c401d4000c036000e0380c0100180042c0038002c00980e645da03580004e00d2201743c1d02c40008169107008403d0000e0082c071070640041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 105972751 1250 105971501 105971519
    0x80d0806040f020f0909040201020c220c0e06091e12030c0f1501150c0807031d03070501050403020f060408070305030c0d0801030c05010e01020a0b0703020d14010515030a060f 77
    0x58025103048405010344090103490008a01c2250031000034140100030f0200030341000071800d80e1150050050b40e0074800b01d10085041c40c852402204104051764110050501041c8940154500280741240510b03036840b0204480744a07100140744a180c0c404980000d050f2811002143c1210182c005d1121404060105640f9049080c2d458210b015084000c074408800251040c80014003440103540392346440480c12440110a4006040000c0c880a50300440c03d00002041228806c0d0703600240d08844804081c0010442c8588a10075041243d00300401c3c4e0744041500e003502d40440d100d56031280904002542c0748116401a12507008400c000018441e020000e004103a4008058550b82c5483d46000c8900060901009129500c809018005035110740d044240c4401c1c1801120981d449980b1242080c0d10200c7d90040002c1e0000707060720403140c2a01901021074040030400c0859410303e4001200003d103491001060704001c40025142ca41c42c3c0c000d1801861449298901503032552900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 105974001 1250 105972751 105972767
    0x40f110c0f060f040809100215040c0801050717010b0c0304050d030807020709021e0702040905160503100603051203040305040e04060507110c0306010605090102010f2c06070507150204080d 83
    0x1e122030003081d0008006800b040c02075441940d000701440e161140a00800c80300c015055841c0003184509a403000c8020350100f20301d806223000d82c0030711040900e01051182900c030010204010400460702c001ca40446c1c910460741900c00c54030829032556281c1e11400c0c6540641d5020580c800503814003101815001100c080c01880203070b081e10421511042c0350810303449180030604042c1085603091070b11a043c50301a02c0c02e14401003011480c0012900c0c1e0314940a9110318200c007040c0d14400410040c0b90030820b49071455030548003030140e9440d5449550300c5001110300804902000800101014401c0e0100c070003400841c481480c2d24101414038000900f02210303d200403a4111120041c11354002075090000b100060043c00030785c0c2030601c201c52540003560340314150b6494001143c0240803c0c068501704600c460652505403002e012180c610030040c00010100390081c0b400d200e5516848401c85900c950061840c42d81c036418034502d20028401d541c8003d1145c0030b810510724545a0040701 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 105975251 1250 105974001 105974023
    0x1c021501091d0a08090f04090212010e0106170309100e0604090204050406060e030c042705100b010503010e0c0702150d050a0b090907030609170f0309010f060e0402040f110c 76
    0x184a200e542d0200009581c1c0780c0b02c80f0090800d80003817114404600c0d28544440c00100c015002007010b03040c0c2e0b03000c50140e03c0d5a10303140d081c90f516142403c050072002d20038080180101c80e080405a2450071815031031b489850043e600a074400040e902001f0300608403850904d80242c4070300d03030390f5076288918002034004d4040d441c865420410006413452244840c90000e0305c0003000340c04071003c0d080410004120201a4682d00c200c070400b0240c2d080d881e0655008032500440141c06846041c0744414111440c02105c50b042c080240018060f04100c852529400000c20070095a10081030000407014980c060005400c1c0100281e007483d0301000d50400340c01805204818846442d4107401c00c8000070044441c00580d0380100d00400101e51503401c12007206000d407000c5000d8504205000e516507020040e41ca107010400818080703456000d21a100040c52002400c00015042540c2c1500038100508080d201c0c1c0c1e160844900003402950081e016610545012a598402c2c01402c1d51600302c0b80384 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 105976501 1250 105975251 105975281
    0x20d0212060103110d0c06030c200a0302060a05041703090a050105010f0e240105070c0902030903040e0a060303020c01120f2c0705030c2b0f11040e1c02150109 70
    0x640840e00303041c80c0000700174082d40300403420781c054285a4102c0050001e44003640802580c02c00402c1c095140342c000c100b6130351805003d498840164100a86007020240000455620344000c0001040c005940180c92001107000c0303541d40d0301d41d40221450507001260140c183c2d440c1c04000a19103040350610011102d0343d016201e0240c0d03911b48140044090303140c079401c92080c00c0380754031015842000103004c40b900c07516600e502c1c192141a030002300c2c4c00440308099154800101130100b89150342d00b040d07115035825801d05c00b1a0a5a900039107840c0740c000f03100d051100c422100014042c0c6900001c83c42031b4005400c102100030212030442c2105c5814500f4034603030141100c030101c03460100b0107000f80c0c1d101070000e211401c2c2050031300110640e031400805500403680c90216180142801849070302d40200900c0940c41d1160130a860310414034105248610714001c0344040c00e08000c51501d0035108070b400c0600307140d0000a800c3e82005489800c0f1403283c9c0c0780c8800030a5a0310b4551084c425000703003503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 105977751 1250 105976501 105976523
    0xf070c0504020703080a0b0d0f0813171b2e08150d0f030908030a020607120b1c1b0605031005010804080f0304110d030201020919051c020d0212060103 66
    0xc41444124403e180380a0005071000340041d1010078035410043c80003901a1070418094019180d0204000c0c40100131100c071100000c0620103403044064600c0a00f41e0b8048100c4698998003205ea40c1c0d81025500b001ca40401c0104420b02c0e503a9000c0b10103040020a000c01d111a000c07030425000ca03582c24501c40c0120f0b842d10046a84007179042402018400c024081d10048081030719818854150b02408400300890003002054510040c009010308020380e030000c0200382030041000c0c101410440c0e2001030949171540c86c0d011070b40c0c1c04100d01d401500206d203184800e40242003440d1703248515403048694915030b00001860b15840002075211b2031a018940c030042d074480004407420842070703d000e004404103210800c403e801e08002550400c3c0f0501c2004031403520440401c0c000618a4015001740c0d6001c82c4100603801c1c510700e01001c22401b004042e46040c1070100054600c10540420341d001e02c00300700540119184c0000d8007005503001011424544c0920360555a41d01007404211141a440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 105979001 1250 105977751 105977759
    0x60c08090706031a011202070204020a090806131a06010c06020301080a0b090111040510050403060606050d0c17011701020405030601031b080309060a0f21020409140c0d0c020709020f070c 82
    0x84c8907603030040e811a1500f4001c40c01160045546201040b100065242d00304041e0005a44034801084500390545030960f0082c54002c12504250009003c5504900340c0f2124000180c4802100080122a280c000c1d10980320100101c851110801005001038800800420f07060400949621010300c51900243c0315518540b4841c02c1e210f408880c20220780d000e1000b0702462030004204444542075107041c0341000e40d20f40b20001540c000b03078408030118178001240e03c400c00c0b1030b00480f50b01c604c03141007107070075050b800c8120118410148643c819030859180e40c484a41c0080d0100d038001c02004080701c886503120309081c1000982c00701a0007003000b144400040804001c02500c490b800002c01d842d049c08003951054620150710342140d003c11202c111030b02e0090040030b186580034045030b080180c55030309290740401140c2d80007107070b00e058a5480c010400c0e0109424100e905050081d50301040225141200741d18044254218107102c50000c9090b003a0107040d41d01502156000e550000050307035407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 105980251 1250 105979001 105979007
    0x1005030a12030c0c06021602010806030102070314160501020409020c07060c0b01050108180f0607030507020703151104050d11030105010b070b0412090810020415020609150601030603060c08090706 86
    0x2820000c1c807524820080140e424040d0b44a682082402c0c104008803244540d40c900803079000602090a0040841c179020130365030710129203544008160b0003185841a140c602424040380354224100050300000c0102d200e514001502803001d901c40000d5445640303440702a8040c0d000f0a2404500f44030700500022801c0c89011405a400c2e0000840000b81c2d003040c004660542000700003545100b100300c11a00520302c1040300716400c00d0700d54060406804c020f8002002d5601c0600040210340c4172102c01d0020940300301c0d180b6405010424009401d2002d84014407181c000c69120a510410710b1082c242800001d0210540321001140200820380e2100450b0401c6c1c080c0748d0001d814149030100060000b00380c951b46c588031081508140c920140d65000140c50480300000903400385400bca0204600046080500180c809a002234042ca251203144a95a188840c1e00300800500701004204e483e4000e5100101541c0c00400c103000410070b000000d420b02c03100f6500c4000600c103400b000180584 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 105981501 1250 105980251 105980263
    0x3030c070e061017012309010b0703080a05160309022701090f0213030204020903070504020414040b0303030c0f130f0603051e040201091710140108060c0f09120313030b100503 77
    0x13000c280025969003040c039244441d544075003880d100e50350613000c2c03890290703648048140284084003000d903540079a854000d001d40e6028128518841c10b0000b8060380c002142e1a10000c001c01c0d1600040107440745c0001200b510325010503121554800840e1180e5408015415060b959505c5040c040d40340400c807030a08078485c1d0346c0c114040810022040c40149002c0c0c00401078080e0003412200401c0c0c43e000040c049a0065001d00c1004c1c3c0042e180710031038200740c05855555a012405141186441e00c110405e9200b4482e00a0b080400080e0101302c0c2a204400300300980b070700480c605c0d040c80c0c07a8203001d0b0041400340c0c0c4861114051030550008400e4880307115101c0c0b82d041e540c10b07940c1440c1420003040d0040c0780384d030010700740078a80040c00f420b900ca00c101d90000781d401c8000306081d407600480314240400505499880102003001002c3c4160010443e01500340540c1c0c3c0d4841007249800c1c80e070450040d41096504407541c12800414000c8240c91107014001d0703c4102140c1c0c6030b54108040d5948 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 105982751 1250 105981501 105981527
    0x5070e180d0503060d0c091b05090d06020705030708040e0a0e0a0f02012003071506060f0e0907200f07060528020a0f0c0303090905010506030a0b03030c070e0610 71
    0x15105503110a030700c078030900c082d60b004403000e8044070480c0140d03a41d15990405039001011021b9076410703404581c1290b0880790307031040002d0030b080e4a80031004010818100c1d104d003001d00740341e80000f000ca00b006000c0045540c0150007010242c0c8840c0c442c4034400c1100802e4807a41040c80c01d22190080d400f50100e82a0b881c964423400d4424025a207500548103c0c2d901007418030215103040403001602d00c240014042075115603902440d5064402c0c0c2e03042100c00c16000b003c02c108000d01000c09058021030248840541204c209190303540f110022680301103551100d00388120021070301144c407900015158100b40c10103081d6030700c25485050480b040d0040b08141e07400d540c42aa0f01e507a00c0b02d10240201c0c0702d14080c0c4142d6202101c0d640311560040c0e8907110440d070160481d0810414150b00c2410359000d0099144180555450000061110f0001405030903c0581d076030017030442980c0400c125540c1c814018141c035007141c2d0714400b080b05400c044a007070340151184040e14441c1e80c40303001d80b11819 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 105984001 1250 105982751 105982753
    0x606190309050c0301090809090721090f0f030302180f0f240c0f060c1305040b0a17100b040903020a030804052a0f0111030a1206090905070e18 63
    0x6600120003030038015209468501640b40e2200c501c1e2070030700030060440d000d40b420340d0307982041c0400e0104507a8010030842c20002c1d440e80074110480c03a00c0c40d114600354040d20100b80c40c0060b041107062251101d900400b0000d000b0544030405030541c0285c05050306035503586100e00b01035418008c0009035180c80c01d604c4820741c90f80828903d4011500741c850f400e03100c2e4168555030000b07180074465008881c5200700b035200304c40050940d00704125540d80f120b400f030b40303450620140310080c1010034198020903210725141c08a842c1241c440c100201d008104044100c1380c48040c20407001d854960380c1e1600c0e0801828114030703205505243c06400c80d4a603050340104141021601d04548031400508119014080c000071070201000081c2c0022420005046a0010300302c040304000c043e02c00e002606050180d580fa121010301ca000c03041c1c034090426800c01d801001424a8048018002034010000320b520f4201580180003000405d441aa40c202101d01000d4485001040f950040d1220041301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 105985251 1250 105984001 105984037
    0x602010c09061202130b0f090a140f040e0f06070f030c02011404110109030b0c1b0613080a09050d05010c03060f0b190c0b09060906011d010504110412080406080606 72
    0x100f0f000381da004054800c08000d150714540d0f113590442d03c1d00c0d40246040c68501c4400b086240403403404c003180600a115203801d003900421070601140640e003101030381c20b2086640784001c0302c08580a01810140c8900c0c40241c641c2890600d0010305088001502d840009140c040840d44840c014407505446081c559840105544e40d640d446501d2540e408600d410840b2100c80040000c0d45200307550301407a0440c040c42c0e100c0d00d04c40c10352000310b400f0b45000c2039581d2262003401014440c030228000c03419040740035a50343d986080401d46e10149a503103d9500152113103000d005010040d485040301e20310b165018000c05039600c100750489000b81c0100c3c18250800c01c0045035080700c00f00f5803c94a0381d5410524031120450f1075440581a08985248058008604005409605001007400751032400240d0705425090303150b41c040064140a0f407402540d551a68000c0c0d100321400ba00c00a00800741e030741c44055070903d040c10302908103220703050220301000d022404910b0305200381c030390301c0d4014034204007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 105986501 1250 105985251 105985277
    0x12481106040623040305181e1002010b060a0810090506100c0501090f060b0306010e0702250e09030c0613020d0803040212010204080d021905060106360602010c0906 72
    0x7000b40030903511480c1e003c0364803282c040007140003074003207128600039110103449131200c0b0282120015903500c0d40d48103000105601401e01035114148070007100644400007a5100b04c04180e0042852a0516901c8078010032165402540085098803e813107180e07215600c0e55440070550144c407415101c083d404016501503442d001d11403014601164020800400c210b03129480304440044c01420580e0200e4503444502c06600342000f61a004040e81860b800f031a20340054000e455418820540b20119841054250241e01c0c04100030301601c26000007a001d41446120143d41e5400708200d80d071a4012a0009080340740c1035186500c4a5030064012007440d0500d6461a2555000800482c1e002050f40000d04448200f4405400030b48080e1005040c41040e9280180c50003110644501c0c0c0c0100d50501640051400b04007913045031001d08100e01032280001400ba112495101611000400708040400c10700b49509071104036030458008119004013250102c5800c9114051840403d0003900d07900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 105987751 1250 105986501 105986513
    0x105040819050910030b18060a150302041505040303020607081014040e0111030603151302150f0c0109020109060c03080105150c070b09040e0d1248110604 68
    0x34162100d181091070140040c0008465800540c4d910300041c0c0c4c2c4005440340b07402e02c0006008052500c2d11000c28914107400060055004e0f0f000e5094011440d05108009a009805903005000064070803012044142030003022508688410b80c01481085e01207020340b8061050b01c0d0003002d003002c60b4145582000031803403200910a00f0760380c0160742c40c08111260348083c407820f01c0042650280f19524101042014a0015188983e0340d842110400340035126005020301510154196951031030500454000d1650303000724840719040d0b19000410505a00065019440d441e1007620b441240c6615544103c0311609030b0080100401c04003001400075282c14408401c0340320a4002c1580351054121489003001030b554091542c00c08042044003441c81d00e402002c984450308801400e600b209110010020705c111100c0145482c0d81d00c0008142c0c00c8081d0081800c002800410403003403a0030400a1000c2001d00ca03240070010035881c00130001481600d0700070300c070100c00c0700030540c645403520b8170 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 105989001 1250 105987751 105987787
    0x305030703092910051509090c040b161a040b070309020f1201050906010602030712030b1f05030402030d090510140c0105090d1d0d0809040b031b01090801050408 71
    0xc0d203c18103500e040c03003808003a2010181c030718589600003e4540c240000d2801d01c07500c1c56004948100c40d61501c0410f417030ba15000f655440441100c9814540d00c0b6403000840034803564101204400d000102e03081165030002410090300d00c105011200d000c0aa0f4002a040078260340040030865400c01113800c26120b6000311112a000826460800b00d0320000581c04071920b50001d4908d0351148100180054140103450041109001540c901180c0356200c600c8102204404000e241c0d940103029025101d000c9171612280c0e03090f8000c0c0646211400250881d0000c40b000c0744248542e0156690062180c0c0451080300d001030304951240a10325401c2c0e9801180f81480e4600b95018002883c481d40240a4140141c4103d0090318200c004604000d10001034026806250804190f07802c4903911402c0e000136450390042c400c9034698450400003409440701313071403085d40340c4038400000d4482000d09c000d0709400c90090300c1e1611400c1c1e8a00b090380c01d83c7e104480c00391507104140032001d40000300d0662 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 105990251 1250 105989001 105989003
    0x50109140a1e05151e1b0a06020903160308030a0207060212070804021f050f030603011803030f15030c0e06010207210201030f150b09060c030301120c0b0304030503070309 75
    0x403007980c251988901c005012680c9801c52034980089401c0080b4280080f01448581c540040d051a0544c2c0311082400084e1407014410135010001d105a405950040034055299429055802a90389814000041d4000e012080c0c404d005070303400284d0b207500740c0d071980e001c50b40e01c00366807811566011070315002034100e20f009840407030f002c02030f503100c8400400e0494481d00b103e84a4150a04060043c0b086100140c4825503414006401c0d10034003e0b0040c0541e414034000c41d8003550307250f80d007501280c0501402207248018a955891120070581c140d044003040f15040171f410400b0062100265030380000741d21003c1c0002e041100288a00900d81e01c01d86e50004060044584c0d20781c2d54000365000007007030180305102d0080c03450108215a41400366100b141c10401081c00000b403420740300c00e4100d0440c8607859800c840001c001e41e0f2516a03509640f0100d1b98001501c1e220b6030b45410140e07094a011008031a40a1038800100b0b04010050035a4001e039051343d04c0c6411503840700d101364024451454 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 105991501 1250 105990251 105990259
    0x10e0712020c160305010e060105010c05030306040504020a0902030a0608010c0c0206070204091b0806010608060603010e060f01140a020106080705030304150813020409200907141809040f0308060102030405010914 93
    0x80c41180b43c200324003036030000758850702c00060020007150f4524200141038201034100204a094100454800400d6030340003841118000340c50303102c6100140c60070000b58000c0e801c1c03d0010080003841070180e8007603000c031108003000b4030450381035400c00c640e044030751031703001754402c800b03102c1640582026803145243d103200e04a210098010002d1301c5028880589c0490b20581c0103000500c02158050141038000301d05541c1c544c11035040541000c030440f4014541d034012071016504402503031003036000400c0b050070024415991034002c44001d0180c02180100051846490313000100750600000322002c541c0320311115420281ca10b00308071807500014001140146080c8103040260b5a10300c02c25641d10b11400c000d0388490040710030303403001c425a800003a22034080390040142e45504107022038000664068460f541d168070760800140808091034264100141408000800c8421100320801d98000c0d15540b495a8038080120f989100758080c1c1c500043c1000c004200c0300e45440c0b003a51403030354010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 105992751 1250 105991501 105991513
    0x210b0d080307030e16141c0507030302071409010603020d3209120306090a0e0615010e0a03031d18010b1e09030304090f2004050f03010504080307230304030f08010e0712020c 76
    0x7800700754011f1307000e020a40311034001e410108109901000500018903860100b1807a0440c000005441030340144110030600d5000100702444000b940d00c550904001803108099031400000c1d040320034001c80b41c8205444013820b02090a00c080050103003c410740c214000c1c1d1841e621201030280a42001d45559501510b40ca2810309041e0203020040c45601d800503000c01c980741342c60006002c202c090040b40d000782032441c0141b0110394030960501d0392000c1c0c6012240e02451000202d00c46000118140c5210b14450700040350380c0700705400074903001002085c0c0703100d040e40000c440710380c500c90185c8080d80355100b000200f00490080d040508032040d41d16000415418409a2418440d08a03212a1001e540090300b84403034680903040c006000340036002003000b85030555981e03180e1b00c0080d2101050001030b54003d1010a40745240f41d61100c07024020b191030b820700b45005054040405100c9001c10900310000c1040301c00862030038401c40035503850182c1544285400c0c00294401c1155031490f00a003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 105994001 1250 105992751 105992779
    0x50f01140d14060f07030911040b061b03030f0601020313030b0703020705100c0f030603020a0302060c0109020a090e06070e010c0b1012080405030111040303210b0d080307030e1614 79
    0x2498072000718820100c05491149080711300c821000c0380040841c801d0502d13009515020901109100380040c00c1620002040c20501000600d40c0c091800000d920f0703949043d6050302148080040c1d8016155952013411a40b02d01e801a41c403401401800120185612000c0010410903009c85820401c10b040040c41d03d11542c03a06420000889a000c4000d80c44008010850381d011811f40741c05c0c1c44601d42004281c1c15070380040c0c003c5125200281c443c550101cac402414a02c207600c4105820b03401443d0b01031250303980c0e442101521110100c0d041c01d0040c0c90004000a01800d00724840400580d00e2141e01459965094003003400942074540c0d00c50b0750600403906404007000051118040c410482c1c0312807808040500b0b49141c2035030040544001e100800001c0d4100d4054400580c107810111180350410003120002c003102245154425110104d590034440094004c0d805031440f1364041c4801703401c2c0e140440e50f400662042520b0b0000c00c0304204036207500030f460900428002040c0401302224 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 105995251 1250 105994001 105994013
    0x201050f03071d0a081e0c0a03050d0e15090d05160b09090c0a020d050c01150e04020306070807080a0207050a02030303070f0810050a060f02010f090b0702070801050f01140d 76
    0x2c81e400d0000c10307003a03d0103042c06070303040b0010202e031001140d2010030340707060208054550704080c1101d40700c00c40c00071301210b2034034042c0304a0403420005405545004d40d01c0c00d140d541c800a20344d04101150680d41140c1450615620f070100c046404444185441508400c5c45404000d03260700340d400703010302001421035080c1c500720380004140d40019140c0703540c4401c080040e010f1015205071a1460208000800c0d0741d008210302e0b82840780d5041c400e4403110103185107405032019440840c241100392a01140105500c0050f50260b8000c1c4d0489605943c2c1c00000e031620181502e441020034200c03400030b1120340f265001002c20f03c1c811420386540542544c080784c03541c1c0082d251741c1c0204d01d020004101c200ea02900c120707400090300c0c00143e215803808000c590500b0f80750251004000251000f1003010303000f5001344e105c148241a0800c5030071550704180400708420341d0450018050701c080050050310500a5901500700c40720350900ca0f03441e20301c03c0d4401d03190125250341c100301102d203c5408686 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 105996501 1250 105995251 105995257
    0x9020405010f0c062003160302130e04020604080105010b0310060e0108060910050901120212060103030c0f08042705010b0901051c0902060a050d0513081c020f0d0b03011d0303040803040201050f 85
    0xc1c1d00c0705500d8482c1402c04810b04101c0707c1040c01402c1500c14415100302004520241080f102040e8610070320b51a2400032a4551280d6040300701030350b00386400020609412401140b14101861030061603030303100d03c82100c5480d80d02180354001210341021562034a000b090064002402c2c1c515820400e0341ca0010405043d400d034408565507044013030440550a000c00030803a18108103000e809258116900075110081c4420b0141076104070810a408001c4044202d40240c5a01711402a661000c45615001c00a1422103015458180400001d00340001401d448035044161209410584600031000e5018140c1600c16151502c6440c0900503884500003010803181c1503941668071f28108810f00d06440e17004e00101c400011070801c46022804c1c09003a04d443c081041401c01000c68440e90f841d0181c0114503d0a0300c640c000180e80b5081c40c0550b100000d9100309038024480c404850404003401230303150030200700c15001080040c0001d481140256070291050401508001600070410b030250 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 105997751 1250 105996501 105996551
    0xf06040f1b2a05100908090a0e0a0f02040f090e0a0b1306061203080f07170106090311040e0c06130b120f0609060609041d06040309050a09020405010f0c06 68
    0x1c502c425100060100d11014521510303038140b42420340c2d5015503642d6607a0000c1c0f070710086020340ea040b00c6020030030041e0803680003400080c45440e40c0c80d01c444410380340010550300405413910300700400c0c0c0074828900a903400c903100e840d40247c2091408004401070100012850b80074002c1c0c80c245000240d440846500894030300030080030f101d00b036250140445116801501c4100680d070880700000740c0c05016207500c0450001c0545041d103800070305580c1c3e2807402d68034a4404244400208006500bc121441100c0c095242c0040d006200010300c0210742600c000c2241c1a082132400b03c866040000040c4841c1e0026641078403019501e011004150f0402d0308401011201c01043c0107000200d51a880d0300002c00301c4112101c3d0410701e001903003070303c54001141c0c0981d03100c03071448004145210880714544449810384415181514000b0f10541c140d00603940b08206003c80801d00030300d80e00c2540e0aa55042e160841000d80c0d080c0d003540c1f52004003e0450300d0075160f010400d40024404000c5c81e043e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 105999001 1250 105997751 105997757
    0x5030d0f0506031203220609020a060e032b140f03071e02010c080a05060a08060a050405070602071211040b0d1101090b090d02040b010c0f050a0c09050f06040f1b 71
    0x142000e00030181000d10031442624150710600c10300c40458016001c1541d440008006c00415100034034004020300302040c0040d5100d11680400203010790400e5812086c50340440c1030365003500982c0158500c000794040c070018412120540081018051503070086001a916036141c24240c1001814005a0084421900260781038050003610380303030b01144c60800c0606000038084041d07000002442c030b90005288078000c64960380813410b80c0c2c480300f64860140c03d010065400c00e14143d552000a40810380f000c980900ca0341c440054041e10208030001951089102947c040509468100300d024007035184981c80b942e240f05610143c0e031180600032189104501c8a0301c0160a01c00241560005602c500700390790040040184968841000810302135040f200000c040000400489102d04041c000a185d00d2691400100b4008005101a006440f8161400f045500c843c4890140e550540703080c40c441107440d000c541075140940188881060340a07001070800f841241e002a01c9505032112004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 106000251 1250 105999001 105999011
    0x303020c0604051014060139080c0d030203070206040f061d010e070504022104050c04022206020114160e0603010f170102070809010f110129010207031e05030d0f 71
    0x7403130100d004811031001d51800c41c444601e04180040c0c02c1d41401012103100c003888038101c0b81c040410b2100034002285400b00c0c0601e41d0401d240058665102c21003118091081594011469200b402103030320445031540035002d035884135541c2400c0c070101500203c072021788070054840c0300d6018038051510b1980200000c80c1e801549803003d42490700b25041107000c1c03401000010714603010f0741400d010040e03403130390002c10303c0d075803410711030300b0a0041810154480d00000c3c0003034810060fa92580c840f000c0700d9114100d0f03f582c0b080160300302c0744000c0c4500c11003441000000ca0202108240000c0b000302800c060304009505400648154000d0f085120547c000303410038014411614015003110071003100031031410100340c48410403406800e00e00ca0400c402c1e060b1a83d0384910611024110340c80304002401581094540e0324000c500c107040340342d00c46540d101c80d18200d40c400580030f412281c0100b110329140d244400780d013080030f82d100d100b51170b0342c070040101c00700c2d048280c0300b00c08150901d0302c0b0003c0c6c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 106001501 1250 106000251 106000273
    0xf0d021206040c1b0311071415040e0a05060607051204090e0a0203070b0903120408070504050703090b04152702030706090807050105030402150c0606150a021002070303020c060405 79
    0x400310203000c0074022440c225081c1c0c001a00000d65a9044110380408803000d21340e071908841124003000a00c115010f640c40003d0b01d078034181004564400212140d0036054000030f0b031030035203004a11500791030401000c0444c400450a40c0415040a4041c0081e4540000d646800345881e81154025080ba03100103010007200c80c0610a4241c00328490018107a00010750700000d80c0ca00d194003070490b21a4000511820a503000c00a0b010250806044580c076240d40300d5695441355440c3c4111030007541443c0c00105124801e01c24221481e41c4410404107a880f9a00c4008011107401c805c001500e40d83c0803070304d40391550360b03005440e0310610701c0d240d940317142d620310506090842c2030780204240247c9000a2040e41000b140b0700e0207a07102841e11540343d5689000007a003140c800581054440c0700024080580c0c00c0c00b040c40c9110303000a55605c00d80640c0562031240621881031074000581100003c86d58444aa4005244680c0240f401604101c2d2140c011030500b0020b0750300f10380503401701000380 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 106002751 1250 106001501 106001527
    0xc0d080406050601030207030e1e030a0f300c0611040f09060803030c03011a0405100f021e0c0405060d0503030f0114100c08090a35030405010219080f0d02 68
    0x10fa01200c20320f0254100b4500307540140030350603468281e511414245034290202c0c80c440d1214030503030b10020304032202d85c070403810700b01c0d4442e4050303400307440032403d81003090381c050001e02101c0c845c00414050002400c0100408440b03141000c501142e0554484140c400d01001d83e10141020b0035450802c0c4c81c0740780c0703005c4104040301c1540c1d0000d11540c206104000e07824030100107490441700746110800c0000728019020308d5a1180b608a070364021500028020302c56030100745c0b82805000c0b50219144003800d04011200010051114601580904112130b41400c1075040550041c40c0542440302c907001d942e582501b150000c485103080406290010051742040321180b0012403030a452520f0035aa5030207005004107808140030303100400008041c480b54407124803100040c400c52038040c1c140c0320040e11030b485e44019040c030501c0d0351100c1420000d00103004402c480c2100e03c160001e003010980894580501d5400070004e40b400c1e20306005400314190504020702e0048501c850050381c45420210103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 106004001 1250 106002751 106002761
    0x10213050906010806090c070b1806091501060f020a02120d0f0302030103020603011511060708150306090601060f0c0b1018050405120d15080a0201110303090a03050d020c0d080406 79
    0x1152041d021042480580d0360042a40ba8000a050b2100c8400c0d507181807030f4003140c0c411000001c205807142010403029000d0b481d801c10000305031000340d031a16102c00387c50b0340e6603200f200140d000c8200075500422030f05000b00070310501152140140e503002c1e0410b40010303503115400000c1200c6600601115010f0b903070b0000c40540760300d0944c142103043d941540c01092860005003e060714075800d4406030310a45000f02c00741d02866031110200d410030b1802017001041500152012590303441e03549003064142c40c1c04190140b05c1c060420042005070b2034650100e54880200b0083d1041c07103600200b10004c2016231244621841c144030400245920308282c1622521a0b028485540c0d4079104c14800024400703e0072840b070a40d180d070305507200d001f8400181c0c01080e0b45840b80490b003c03501000201c1e031401089205426000740ca46440b00045000e000d034907417008484aa00c59000610f8400009000f80013078820100c03214401400c000700313404a039290007110307100d21000c240700600b00000c02c8000e00403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 106005251 1250 106004001 106004009
    0x1509060303110a0309030b06010507020d060b010206130f020f0109150f02060606070b15130f09120203070b0f04080708040801020304061d0d051606050c1803060c160606080609010213 80
    0x900100f00d041e1002482d140c1540401003080800308040b801c40e0b8440c1080d1140641c000304807811407a141c0c580301c0010130300d10702d605025008800001e10881800ad40b400421904201495100c0d40941e0800c250308444c10340c0740c0c2c1070040035940850070180c0c00c5d440c140802516151114404031112010b844c11200510152040350104045c030b000a05010701150005060b00c08000000e60900018001c503130020345c001c81c800e00d054061940304004d600b080c0c50890283d41c540b42d80f2104003000301c0e20303882065400741000c00c00c3c101080c440c120350f564a82e0300074007898450b42419569502e82500e9031055110b03000c0750b0b4011060009001040c4150655960610f01120300c08441d181065103440c3c0140e08142804404a4002c0da058564041d034100c1d15030211302040145440c555000054200a800c070100070142c100c0c1074224200008c40600400c181705003241002a0521004141400700a00b00d8020707480e8000000d4641c0c0030008070740952124000941c07144021a900310006a003548 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 106006501 1250 106005251 106005253
    0xf0e0a0c0e0c070f110f1215010b04030507150302070f06050103020f031c0c030e03030a0201020a091d011202040e0f0618150a0b2202130e090c06030a150906030311 72
    0x3c8100007081c0400c071940e1a54018100b160303500b052030015403100301d102c40d00b5030003108080760805502000f0581581c1e1491040d0410307416601c03200c0d94480d42c003842c000145654450310051020b00005169903842c01e0f1540380140c034183da40d40e1940c0321408069030445441f030b150801402181b0f84584c0c40c07440440103800501ca916130706180300f09603007500c1d640f050500c50111903840905100e140418082a00601225502c03402244001c0c002d40c800201e19001841d415000314002408441d64020b00000e4800e42040d80d0811240c005180c401d084201d0f4840c1d916440342c0500b8a050160709802000710000d0b003a507290801901140300100300e01c1980d15000501d0003155268100c1c031036030300141c0045000907030030006408a224207041300000d1703142903076040701204c4d504495001481070050707a2060141c05661040345504500040d00c40c084240c100c140f04581c20301b03080d000307107a2141d041a4042410a004880b2803038211685d040340c1c4450b030320342800b4018036411a05a20074101228 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 106007751 1250 106006501 106006507
    0x61106101505070b0f010e18030301150309050a0302060604050903040f03110a0305070e06040f050603150604060504060806090c010c08040b0a090b0307020c030c01020714040f0e0a0c0e0c 82
    0x55090106000140601c0d28034541a0400c850300340c0c49101a690076542c098210325403404c105116624125003480381601d0980640300103854104d441001c5400d42400030700039425039003403020705c0c01401d100600b18020141d41d059401c002c184104040d01c5414000c0d009000345040800501c000d03124005c00e0302402d41d00412041007019100441d1a040700c0d007060a1601203580c0c003000400b00e41a690000d80544190391010032482078506a103405400119000c10400580b035454000b510011034010740c0c13603044580c60821080c600341c18941c0c0038100901c00140c254450000908850305a003111106e41e10190030008210700030040707802081d81c01d00304a000410190b6400076039100707901440b003d105010401a00340c0780541b00c16005003000304861070301d9140c50900255100c1f9540c034910b129114100e00040c4550002c244801075a4100700c900d907601d9040400c0c800603204090f801c0500316034038050071207404018004c41855a2090359064540c0745044500d6001090161810b4800d80c010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 106009001 1250 106007751 106007761
    0x20a06060308031b03010b070215120702070806010816050d14030a0309031202070c030201120603060603081207090e1308090a030b06100212030612011b051c020c0d030e030706090804061106 83
    0x7d9050b038003150303070484050500d003980b440303110480c0c0100004154203460308001e12405075000700c0d140c02900c0a450440c4d046aa0303490800342d64801c02c00651f6003143c6110360a00c0503040c44000d80700c40c0d034004c040c00108014600b5019165a0280c0b03c843c0000b81d0310310f010020181e01c000c05903d40d021740001581171500c0c0751503040a103485440000d05210725064004d043c0c2401d40c0040c3d0041d9040003041090696030300381884182d0100e842400082e403a240062a501d00501009060704c201d160304c079510307a81f810740001c0d00c038000c1c0c002554180820701002c400d50b9902c07006103010718802c80c0845450f007044401e01a6454200b0010000c1d0b4124441170501032500e081030341d9105030b0840304d041c2103400c11340c40d940c010841100ea51075074464500a404503150840024014002d55a1440b1710030401580303060128050180e0402854018450401d5200c1c0b2940120002201d1401507a140144070396809044540000b0105d43e0640007280402c031aa420517460094518101c0280c41ca916003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 106010251 1250 106009001 106009019
    0xb0d0203030f070f0b0c040612290103090b0a0603030311030f040303091a0403110706030e060402060d0e030c0124180e01110a0e10050f030115020a06060308031b0301 73
    0x184254608041501140f004207103d544440102415080b8000d05280d04002c5282d400c140d0040c05200b000c41ea0841c100b40c810381c5103100c3c01d222815401f01d01e80711340392400d1030343c000761031540f45180c1010b03201c446180105030381c011014007482010300c1c00a40300d450340c540903055800607180b41160900510421904440f148030040c2e105505180008940c016441c04a0000f11003203011410390350100200000c058108640702c01049003e4111a207180d651071044007520031140402005030003900114005007402409422414011080400c401450910803171542c0c000728420f41890303444603a0f4450442d00c0224030700700c0f442070000d00cc2f040782c00c1c10240c0400c1c45200541a410f250380b195140d03217444083d84448076100000a03515a5400040f0000b8004007404180501c60305c0e20200c0c0b078815a00580480710507100ca0b16800307065070328200240302030310f054441c100d00b980102070900b4000b500510ad01805544107030303152038485c2083c9460444001c089a81801e02800800050002c030309 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 106011501 1250 106010251 106010257
    0x1214010e0709053d0801051308030a020408120d05070e061801090e07031409061302091b0304140c01090303050d0b0105090406090c02210910050c0f030d0b0d020303 72
    0x45140003203000e844030140650310030030406409000062880030301c0010a105403c009504410310111a501c030b4444c01c172075080b40c500703582d5200c105c111240c1c424001781401d07000c1d40d400080b071940141059926980e0600f0280f550b00e8604070303d00c0014102104106500c03441e60460f5151804d560304070300310317000304c2d185114225403814010b01c083d0140c81070782e1180200c14090490300001d000b543c03d0103c0302070301904a0550389550a504d010000321201382c00940544101c01d0740b01e07403114215035a003e0041000d0080d1107251080c0c2c1c05901e028240e14200e00550145100f02d42c0b003451610b8260800303040c210300c80d06483c100300e200c0c00100081381c0e0220039920952032101001544001600050313a0758440c20041070740040c102040000d28020540c440031050155070282c41100005048614a82d082080c014101c81018004890390f801d0440001e44082c50608105140501d0300c60841d2401e00c000300910b066600004a6034a68001c0e400b07803603044030b019611102042c0d92503000980f240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 106012751 1250 106011501 106011509
    0x90607030206060111010b0d0b06240c070b070206070303020f0f030103050a03030606020c0f150d0f02070606050904080d0506060705031602030708070303091707031203020909060a050f0103090215041214010e07 92
    0x1d1a8000415901d81e103113012f03104003803c101103500d54041540e41100d1a03400c840b4440c45940146100060341d0026101100d0165500804503481c1c40b4407076406500079040aa80000d64500500806c180d010845000f103000c0c40c0500000c040980b1540f50007829135100d0b401100864210780c50811283d01c440043e0b08441c03000b1200d4031450100c00b4040c51190050440c2a181ca504100441907842c1d907076401065442c3c010341042c401551075038148140d81070180c2e0700a110078410421300c02c81c140e1952215410550040c10b1600e044000d4599a2942e0080d00f61700c0002c41042e40411b04500e0104900c0c00240300080107440740030720f561409020b880191246408110000340715148003c0b00744604409198040c4602042c0d50722410018005d40010703000700d0241c01d0040200390315151410305141180c2c001048031041140f01401100038241d81c810880c3c0008445210504514489000e00080d0401380034081c2e070b4400d103080c01d54200306030991014690b458034906140c06140403882400b03072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 106014001 1250 106012751 106012763
    0x105040f022a0c030a030903170301151107030c030b0a0e06010506091c141e060103020d020418081803010b04022d04050402030408120a0b0105031506090607030206060111010b0d 78
    0x181002803030803400e00300500483d55141c0100f2145030101a00302012405403402820001c010603100001d5411501c000e01945103003100031808412a24401c461001e0825440026981c813075990750f642112800c41c0e500100d41d5280d92800700710441d08207101d0051804116001400305500d85804180c1c20310806542e03a010300c0c01c1000c103116042c91601e0f040304255102541021561420090680b41c1019a099128814111501d004104800036207503060300e400800c4460a1705450b800c20000704039203508501c00d66a911040c2e0702042e030f01809000075074003201000300d4141c00c0200301821205a40307043d80c8074510600054000da403040d802d165030700b400b41a25102000804010180b18000d561015600c2400001000304200300c0030003424400203204e0104015803103d83d501015210201d8449000503014030001e01d4954410760102c00c0e80c407020740343c0303031270010b014003c9159984a0003064000d81d000700d0511a103541e024808030a00b00d5818000c00c94541200001048400c0c00c900180038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 106015251 1250 106014001 106014067
    0x206040b0c0102040302060a02010504021e0f061c0603050c13060b03060f0d05060c07170a020a06110d0e010501061709030403032a060507020f030705030f0307030915050105040f02 79
    0xa50740d4254101c501039500101490380b1803a0001000303018000c2201c049000d0460141800303402510b074445071005550041c1400c1d040c041c044103100c1c450300050043c555400f2441c019210360f40252040300301a40c0070308050405504001c0501a045c901311004046062402004000025030710068903003020007241d20031041410080011403030721100202400c1401410180038100007010700400381940b19807a1710000030040300c92050f890107500780c81070140c3c00091800000030f4055121007000807501381640d050054400000007102c3c3c00000000b010303035643c1c0043c8984c1da00a41394285c9203a2000d0816214600005c11540307a0086100c024244400030b20b82c0d125200320040110044120082d40450107121800c0c003d0281078180d550101502807039011001d540ca0110480ea1401c2c0c0040055142c12070141d203c150310b41c001400d0008140d03840100b1400100501070200c404403502201040e194144020403040f5640790f000d5400c098030400040102801c000201700100814298010f1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 106016501 1250 106015251 106015267
    0x15050f0c120313050601060f0e0f010908121b070609030b040c09050a02030f1f030b180703150506040605010f080403031b0201061809050c10020a0b0a0b01030e0a0206040b 75
    0x1c5441c1945946012068000c0104900c2c14001c40c50710704494051011500d5590742c1d684192070811014030000c00080e03041c1c00314001da080c1900031481c001ca041c5440c0411642d00e18000341411003900102c4026080001c00c800c2481503c00e815441038420009030407080d03d4100c014010040511004154034000000503040c807210b080118020605d680b010300c00da10b4180c864100035030007210682540d1128201103071541341c01042d00e444da0201d12a10311003041c1552502000101c1c01040c03542c030b440c440d0902c0d0200d4401032220070000c52041c15000b610014209580064840091140d805949805810001682c0c00f212545c14180d042c1000c10f4181c4680c2011402391041c010591040000c0e0b0316803200c402c0d8158810011200c2a0010070710203500b414502051f02d100100140c9960b01225011810b80b038140c41d0795a052609004644814140d0798403200c1038042141c0c1c1101e059034a280341c072060f507014051000540c0880d03000e40520f0010380e0004a490066014040d4041c0000c51103078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 106017751 1250 106016501 106016503
    0xa0b1c03030e010603240908040915090c020d021507170702032809050406051e0d1a07091d011e09090b0a0b0603040b04030302070305250c15050f0c 65
    0x21446072001e4001d1201544900f0821586030102c81e02c0e00306c0e04007548038440034480701c0c440d003e08036500c6140b0901d854540001000a4090010380038502615251b0008904c2ca95102d2261a5400341c3c0140035511003402000e410903441c031200400481ca00010080c41c2c0c1e0340403030021140a5103104500046e00c840000b00c0c5540902801c40755501d01c900d01e10360a02000c5000304c0700340c500e295075000c400c82d15002800f050b114540704150708503411018042c507614200300c241e001054094010071b4003510304c1e280c0b4041080d1200c051052444e04600340a40da80d030141e900c0c0e000d08520b68210704002c0058541e281c0e01b00c2c05205200c00c00480840a07448080d0008043e002000300e440203120a103801d040042c034138481990034000b070521f00303980207069043c11810341e4400e036000703903210400d07030b513281c030150040e6020581c101c08010023004810140140326580c90006400e8a4010b6046140c4e40740181016200b41c1046030390301129949001510b5000017212074001c0c1150300192030780341d8220301d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 106019001 1250 106017751 106017761
    0xc0118030221010f0e070b03090c2e1e0e13060905090d0c0b041e0f030512070503091b12010c0f170c0306010e0a0308030a090203060a0b1c0303 63
    0xc1d84160002070869a00d01c29150010110b02510000c00030a0181d0310200c0888403041c0032003c9940040c070703081081e001114040c503406040710301550000b02001000a03500741d040c001d182c0c05240616803082d01c0e4591200050002c0c3d1150034903d403070a400d9915000d0300d0004800850402c5038507182d0043c1d5488448400e1b003540c02002c02404413980380c80c2d01602800c1c0c02c8a4810103813081e0722034502018840e40040514a8010741c007003916413a1a141d000c402c9480090800a00c03152803c4000007034108150b000d0007038020740e91a501d89001c1c0d96100000340c0041d01480c200403040c4103105281001086803510709010349000900b03a511100404c07941100f5041d85203042d4a01480548001d4010403504003100d13a9580c2c2c03d030038040034002d0f0019107d0a8903501c201010038800100d03107500440412101040051083c104075a030b80c0c0c2d80b00c0340e9500403280f1142d50b5446561030800c505007002803d4100c40c442c003007072001003400000302e0704c08124201a4603110041503041c9050602039404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 106020251 1250 106019001 106019003
    0x60c080f0901020a061a040510050d080309010e030403061406011103040513090507030c060906020d0210050711060a020d1802130504081e03010e09011b0f02100218030c120c011803 79
    0x1052040d403008181d0840880203030302d1158019814200041c0e207409c15500d8603003c0e98001403021010010b60b403640c46080e00300902900e0390350b682e0340c2115682c6404101a1004503c10100130650050701c4181402d0707858040e2255041c00442610b6074950200401a181034600c1511200c2c2d0340700c080301c006800361004600c0a085400340312000310510001082420030b0b40c91070340f20a808a55145004c0b0f07a940d6104203481c2c01a00f00400581d203901c0b06030002c0e500002c49107404100351040c2048070381009400d0700c0801c200d60303000a6030b00401030b55020318440b07035030310f4090380e4102001600841c001d0906120391124a5949400207400c0120410940d0035980780090384a40c410401c3c5040001c6910038090781080c4440c290000e021b4020500075203d400e074155080c00180e0924a40c2070366648420f80401d0250700031307140e403402c00f1061807014240e00c403083c3d00e600c0c00e20400d020038182016082d114081c001c3c1e45400c00c00b0a0001e00088031403c10302c080c82c1659000f05c0308017074185442da46405c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 106021501 1250 106020251 106020263
    0x717010f060801050a0c08100519050402180a06050408150403140a020a030e10020a0210050d1103100b09030706050f040e01091b020c030c040e030928060c080f0901020a 74
    0x1c0040745404055110380d11650000c681004441010b0740d082e01c406504455121030310000c01e80174000c0b420031000008812407002c2d078210700c2c41e0321000014160380016025a00c40d825104140c4090310300089010001c00081c1442072034281400c002648615502807582c02d5491200003117070030507100c1c4100c0c0f41c1c4110403032481c80c0c03100301c0f07004029201c05c41000103400181c81d03070500c0440341c0340c08c4500c508207144940040c0301b840060307400d0002d011010007441007441014000c07100741000340d0081d5140c1e80f20724207140d42d03031b840d081241c12011019504040c0c0ca6420a100c3c854403a00d0008d0540156600341c01c1640d00c80c100c4004280e804e120711b401a4013500b4001000044450341030b00f0681c0c0e003040041c0f8042c07107024481012662544070464076a850b5104c1c2e0380c0d000c50307030034254000f64031203a2140c1503c0c9040300b10030100c2c900b00412103000e4030b01d030031022504000181f00311803400607020790f02e0981c89422041e00c4980d07260051032a0b0940d1500c00103504917140c3c1c000c0007491005a4800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 106022751 1250 106021501 106021511
    0x90c040b160812010801050a051603050603100c0f1103030c03011a04050d060203010303081302090c0d060306060605130f18020c1f1a010804050312040507082b02010c020717010f 78
    0x4403d54003403103030a00c9000590742c24000428401030311350150754491151900d6120440342c50318000ca01401010301000d03054003400f2020900e00d01c1c80c0c060541001019240d00c1c0d060420484000c00840e5110003403d81d541050050002c040101022207044502c9035000c000351b80c0450301410321034410390380903c0e84042c05a054400300010380c1c0185040341d020345c589482658a822101c00c04000c0040000d40c4441c4000004104581150190103056400c1e08001846500c90390b40804a4619801c0746000c0b40c0042841201000f03a2600788010380070b000782e0010740c2c51501045941c16840d500201152540106074440d041004001c4030550040b803801500e800d200d06007840000300034000b0718090800030050094515401518000d0040f60322000079032130300600303489241c002203010340226110b020313446d00001c10901c10403181070340c0d62400c00da20380c2c0d00b60340c0e0002c104442403038010710781564100381000340d8894011a9243c2195018590904002400003000d401020b41031465074016240c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 106024001 1250 106022751 106022767
    0x102070801090c18090209011a0d050c070203010c0f0f12020c151005060f0313051212060108150607030f030f06080307050c182d1306050105090c040b1608 68
    0x40305000c0441e5811065001504c0094443c041074441880e0040c0d0030482d03d00c010420424254103490081e04003641041c180040443c0141c150360040d5000f0313002d01c00108590056103400c0c451030542ca901c0d814007910702c022130310b4050300390820b5001c0e0b0340611404020400d01d412040c0c04a0b0711212400c4c003928441c03c6508410301c56030000340c2e80b090200c881c00c6004141420100101c070014040c561005c0e04542e1079126900184482c004119914018450301c204105d080e01c01500481c2e02b142190800d914150780018200d5500810000da40c0014002c0154281c0305c1380c0c01c4600294141c0b41500940d241c904d801e0b40603019078500000d036180390001c00a82924040003605000d81301e401920007010b6100d0400007050380e400c4403001540c0101c00072620380c10084d0104d072000b036004100450311b450002c9486038842012904014140f1100c0c10030000c00081c1c0c410240508000c070b503403000b103040103104242d00c1d0003607000c0c0007408000054101e0103580400310400c01940d100c00482e40d0f4501e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 106025251 1250 106024001 106024013
    0xd020d05070f0302030c220e0f04030e06040e011509050a0602031e090a06050a090b070311150115030c090807080102120907031502160b1f080a1101030b010207080109 73
    0x41107482000080101c8988100d541c482e00841e0b00455001c01640e06104043d00a00d404d5001c040607002611b0b01e44800045442c0700080c00c912614010909400901d0070382805000c1c003e02c40445403080900300024000618801240f50640d084261001c00e1400e441c1003e54018505800160b80001010b07000116941d0000c02044000c180400b09034042c0c031034549001c01c42c00346880040c0c0c00307209113005020252052015207003184c41403501c104032607603441c00810550310588080e000941c0300000c85034050703c204540546484c040b1400e41456141141d000403480c44050003e04041e210395240c02024841d04440c17006e4400d103c240d507151540d503c9514001c4d840105ca0066004c0000c000851440c808104c210440c3c4d001115000045040d0003d82c0080d403214500e4441003091005c2d0f5000b280c400d11040e4400c0712902c8020450040c0100c2400010101d23a010b40e00c95409000040009000c1e0442d40200c810700b82030104945142d500148d09101e41d58100001561a01c0505428004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 106026501 1250 106025251 106025261
    0xd0e010c170d0f06050f04090c05090601020307121d060309060406020c03070204060b030603010c020d0507020402342d02120102070f030503010e0106110303190f090302010b0301050a020403020307120201050d020d 93
    0x40c106e40c1d4401401ca10000d00054a0004401030304a040d0040200072034242125650341c402414410360345040601d5039125400240d01c141100000c3d03c402500e090700344003801280d81c07080111141400d41c5040c0c6a4960390b8207000380000c02498000ca12144024001c0082e1084540d0003002400499214490134441d41c008995452096003001e4840400300c1c0003040307000000e0140d94a40d0303e0416941c09010103903000038010a03180d0000d071800f202000002e07400c1c1c01101b90030541580480b0017401d00114000c22203014902c00d00721081e941f051b9040006c0c1c0048403507810358035000b4401d54554054024050400301400380036060008804051303012000b14103036840c1c00e901903d166200d640480780c401848a400e50213070b0080003c0390b202d03105803030000c009d00480540031070304503c0302d00a4411307a140c1010450242c0c6d11071608248502e000e014103a4040980707042181000d182d0340010741c2d1801607114244984081c0003541d01964803420803035030003109041d415541c0751500e10003100142 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 106027751 1250 106026501 106026509
    0x180902060c0f16150c0308040812040f0c14031f021204030c0b010e061305270d02100509120c03091e0906010311090126010303110d0e010c170d0f06 65
    0x410b0010040343c2d104000c91104c19108940c0d4850145a21568042d54403c07809401901c000005001c64044000302c0d9a02c1c92069100c2c01d04020285500e150072801c414580e006101c1001003868944810f40f000940c0036000010302c421a040d034000e050860000b44590300c0004800c030300b040100020315030400c3d894000c0754865880e01c403040c0e9940c820000001410b89149902c20303191881c007554101c50b500303d40d170450b82e51b4039664444040c107103c0c1110302042c0030035001c09810500310303455029010b00c541302d00c052039140e00f4402850301829154035400c4440000c4a054004620080d56510400030381d849031901030550040c1ca20500b4000c00740c4007004100701c0c454805a00000c0145d4804c0c01034902200c0d41c3c940403070425003103400540d9800318245800c1040d04c0d03040c1c0444042040340d1109070085009445198403c0420ba1015041c10b00390050700040c05138210305110f0300d0f40d1185200c62044d400c40c0445400c4030308240c49100b2072103500b155030029814000c41c040c1600142c0c0c0b04a040b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 106029001 1250 106027751 106027783
    0xe011107060c1a0403020604142a032103060603040311030705150a090c03150b03011107050d140d11070623010504060b0711030f0303040c1e180902060c0f 68
    0x180152200d83ea410000c115401001a0000b102107000103100740e480032071100c1e03548191a10004c00145807040c40c82d61610b0a0420402010307184810f05080c40840ca0f81c461010740c05000c0440c6914141c41844050b0440d406008008001003c1c035200d00508400c071a40f01080d82d40d12032144c24416910001c40603e8200031000c00c0204003554840d12403e40440c1d881841030314036501e1a243e0700f409504a004844c060350f1501c0d403c0322140e0b004c0c81001d807200b0b2510307561501c4103030718106189000303090460035052001c44000e4050a142c00c905072000e00e10450320110380b5600c1119503c00500403e140248024200400340c0d185203020a01070f45100d06240c1448041c1c8ea80b2410081030b0307074043c45101d00b50f00302002814042092080c00032095032002d01260760290750b0140084c0b45501c00c071820358000103070880500c581d204410304d032680f240c00b1903000d00082d403c3c0488286a00c4500420588a030703507030103e0b83c1c00c54603a80250f412905000742a9940c485100440986031028208800c5103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 106030251 1250 106029001 106029023
    0x1030804031a090c010e040b04060e011802040e0a0c020c0d0602030406050c130e06061b070e0a02030f13050c060c0d02060610020d0f030905030d230105100e011107060c 74
    0x316035800030b005807060b040e00c4003c200004d006401915036008a01c40036070442d4a402d0302d21426162070040b1001804044c1e50a1081c0d031400d000344000c1c240b040300d05403200b80108410070252407969021500105004c2d00040d0301c1b80c0c040410703071900301ea0f9503043e60042d0502c6070840a0014560245d44241d00408044c0f2299072491401d9815208040304c40000c1c032162348091099040407100c0c40c0c1c3c01080030303009a18200c40d5174036a0b84030042001c41d108041c1d0100b58280044103908120315048a01e80d9000c0d811400c0443c510400914000c2c0000032030004038001c0024400108a521030b030300000340000c1c0e070301c1070840201511000030956410151168a000c5a4a41048c0c8111080300390341d079000c0c19a00640590445580d00c1310740b0039408241e00c0c2c440a102013001400109815494090009148026070b210740d154100c03210690a100d03520040100482d0311101517881400c04d031490040302401c018401030b64401d030700d1108840300784100c540c0451301030b8224aa64482901502120803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 106031501 1250 106030251 106030283
    0x31e01150b090139030207210c060c0f1103030d050703020a090f050306150a1a091503090604080f0714150105030303041101050a090306050403030c031505030c0d080c060103080403 79
    0x10004068006821166484c9105591100260030224500e207101b413040c2d45800d5682c0e1000d03030010000441c00c0030b035105c0e04c3c070511003000280700c040002407007142018402d81086da00c4030200c0c2c20740180d0280850115610f00b068641e81441154908a80e03080100964208240e0050081d08002da0348404101000d60205031031071506e64000c00c40342c005000b0301c2c01d40c0e9550020a60b941d1014210350308036102900204101c59442100f11070b42c1441480c45845104060030080342490300c8164056803c000c000784041b480f000b00700564000c0d00411042d543c0c00c81180c141001c0c1c81044e4002c1c101c501404481c61850801141020100d444a190709541c0e9885604043c0c90b4441a6030052215542103000b183d00e5001f400a40074505541c2044a44a5a252981c401ba2071084400303d002035614401d42c0d400640600c54400c0010380100003900260034080801d90b00c1031101d59051103a000c3d03182003000c02444804030345000b26141e0640750700d0359480c03070b2098a40d042404100e6611042c03900340c034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 106032751 1250 106031501 106031537
    0x350105010c0206190e0306041a0106050c0a0b0402190f080601061e0809100504080910050a050405040908160305071a0f0117010e071e080606031e01150b0901 69
    0x111120b0b0000e00980c0741204500c80c8a600040401c0700005001c0c210115250903a814010280300784d0081030b076100e4070a074650f10040c40c4070050700590203000c02801156484a0b0001d903c581c107a42c440110769003910750340001603500c00031420b803100c010440342d0049600c400741e28030070b0229a03804040700d1459890b000c0c21744010700a500442c0a8141d10000402071520801c030054001d08074405880c1c903214100c5101c03080e10304c1110281d480c4ce00c0002c9500b200d00385600c940c1619030462810718100881050010070754812032040c24451178850a09800344000e0b41d007142c0c100305c190742e00070f02e103180e252501600075007180c002034400106200e010302030640e001d6a0301e4032481b4402d600c1c540c141c0c00d04400c070381c180840c806095400c1d0f60300c84d813240000e81c00f001000c0191580c0d2200da48205d01000001c458030030981c1111071190018000c3c4260b44c0ca000645a800313154820300d07a40700203412400a0300400d4900c000c0803000d04d04070070000c1e401e4031100042601c007400380da90f984130f144070400d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 106034001 1250 106032751 106032767
    0xe031305030c090c1c141003030e09040c060e0112020712021908120705091801050a0801090b01090c0c0609060902090a050907060305060a12080307020105160e0105090135010501 78
    0x200130003079007080b6100355210207100e4100010303820700b0001513401103000c81c0380c40c104007161550605a41c100c014070526402410110410301c1c11103a5451514161f650521390700c03600e00c10078041c40a40c0001800c145e024854802c10056280021502e5004c2401c0040c0407031040c071910300140c001d1841150510a003994003181c0182c202c0e10a61914511014506113202c00419950411006221a582c25a2200360403400303010103060182c060350521040109804040c1d0018a040c2e2519445a002509000065044070110000020f0114074a1001c1d00d80780d1041000600c00b0b40392108800c2004055801030f0200d600941c0c01e90115521046440100c0308143ca400c160340d44400b004000300b5110f034000a5008d04d02425008050760742d0114410308a801050072560070201000704824203609101c0c0d5584226003c002c0810ba030304012000e0007003007444546504020780001c400134a64000c10010f1131980d001d081e600740c4c0200b003211003140101d0102034034518074049000001d956204a0700 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 106035251 1250 106034001 106034011
    0xc0906060504080312070c020414060f2b020a0302090c0c01050610020c10031b0c050610031a100e012301020d091211060a020f01050121030c03030e031305030c09 71
    0x110301d40303480c10040440002000b080c060401060f50007c600507106c90040e5a0001288141201941811400c0004524a61120b07074000c0c0703403904110144000c005404400d0f40300c1c80305c603820303038000c1c60002c0342c01101507400c065000700c0d641c01485405208180200002c480401c000c021644802080102c200081004e58005a104542522540c601001280b04c04240c030300300050342d000b024903e1000410040c601e5004101131391018402c0c054140603a907403000c001c0116401c05425940c4003540c1c1950602c0c1c000d1961027000c0007510640f2400650405401c0c4283c50950315030f5951510f0581c100031480079440b001c01018140c90039400058410841c00203503d4140302c450508007201e02d10f40d032000041d20508025201650907444650040c07080c0034003039004d48546408000440d082d6041030784000c01902580b0b0103e40600c440b00b1216100c0c80d498540203036900348505044000c3c00c07500e04070048038040002d01000741d444a40c0a0340c00c541c07060702a5a410801101000b1000e98101d07a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 106036501 1250 106035251 106035253
    0x506030a020a02011e060602070906031a0415050f06030c090708010b0d060905010b1e040503060601050714010c0e18010b03010521070b0310091b05160209040c090606050408 76
    0x3040d00204a0303009009004514800003e214000e01013800755090009101c4550a586000601282d076052003d079000d0400760505100785131030f40d41caa10b80750250302c01a00c41420a80040b81c100070710031360f981903691b034052000d0040382025007006032041401d458051003446101e0601d621420314044082c800c40704c0380c07940c030816803070031030740f4140340c4c0c407104201403001e86c2d0f10b0300410b1000c52441101d019002c5110100c0e19411905840c008000c0000700d143c2040d1001d010410042e90001140e5074008400e01c0c00366210031040c9480301509040c0e802002655081107001001c042d402500c28441082c101e603140307200300f8540c156100f0200c0a00540e00d0400c002c00050001b070910008400c1c103041101c4526031000080e6600d14248804c1d0b410054828600006024180070548402d00c00b4014058081200c141034511003030500402d04a4102407140101d03400200d04c0e0880468a0390070380207004285107280c1803500010342e1030a070046995240c070b170040103e01148100c00351b45c15078980700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 106037751 1250 106036501 106036507
    0x312130f0b160f09030627081201051918020c0f0609010b0d0b040f020111030301060c0c0504022a0c040c05120a0608070603091b15030b1c02041509020708220506 71
    0x145410f40601004021001038a41070050b1f813800604950070071018a000f5043d0584540c00c0c00082c450110069110522400815648212500d9007180b036001329501d018004070503114806031440a0300030860340000c1e90003182a2810110000b251542c421903245008006607141c40381000130009032140081d0101c3c0ca00c0000900040d81c0308084d00f540e90050501c0c081348100648180d103550301c240c20903000204400750307410030010017130000c00c040e0108580c1541014003c03200002d0b2020b1803211065013040400b0414160202403081c0020008050004d00c04908003a40c0906580d100b0518010503a4445000519442851246100707852500c4040c0c0226803504000b1801780040c1c038401e48034040c0244000408403070340f12421340140324110301003270314449002001d4211030445d25403501440c14102c0070306091103180c0010840c50f504a50000b4404403014043c400c00c4060313040805064400507006003401452400703014541106c10b100000480c8079440400401036600c941c1c1c1d01b101040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 106039001 1250 106037751 106037753
    0xc01022d090111030f03070f09050108070e0f120322050301060303020307080f0409051015020706020705010c0c09091a10030503070b0901090506100609170312130f0b160f0903 77
    0x34603038004900c102241140d040c049408505c861a45c01aa801c001040700c200b03a000c240d40d003184050b0010300003420032900e140303407072034010b003440c01c0f0310107024881c504c03d04215405980f0000d40b10b103006450822213817103050b10103001b0614803880d018401540e1014400150f031303260502404044d02c4c0d040c1e02070360070000307950386100103a00007020321001580240b10100d8255110300c940c0c1c3c41041c050300340000300c0d4a8003c012405040400c908821508808800e104280e0006003000c102c40b001c2c41c0103030b0060110305007140140a80d03044003d0340390800b03012800f0b201342c0c0343c071034516a038804668418685846000079041005071000a205810502201001c92134a48200d58094540700c00440d0080c2207980d4203080c0075040751222006459488103101c4550700c45039000c00340a0b013910341c000ca068a116029500c0c001d44041c02401c0e00000009404000c0ca02d1404555550103081c0c6c21100c401031800d403101900c00c880c849400c0454031404c0c0006403260324041c2c4121501e03240d506441c0c2c15 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 106040251 1250 106039001 106039007
    0x70c0b04091a100e1305090d1b0201080610090815060109061803081b06090109050606040608030909070315030302010b01031107020904020d1103120c060c0405090109021303080c01022d0901 83
    0x2001400341c0c0c2c099106030008000d1710311030294a1041e0f440c440035064460b90040050041042c0a8506d00c48601d41039201e80140d8103c1c400c640c00c03450032107480c110100407a90441b00d012203508421001e005010742012085000044207010741000d80311a4451511800101c4000503084061900c07240300035020400709040b6001040007003880d103240d400341d100448209150420a42d80c8442070303035540d4010750900205001454216078210b40c00d201c0c2528007011560b81e0301501140d144250f80d04000b20f9081d42c003a5014454000010002072052592414068020b20300c1b555010f002c2070800d09000ca00d222010210388043d0b07402013992003951290f0302880036007603131030104460410482001075410b64040100c0013086100211043e5984042170341d4600303201024204580c5400240b10030300480c1d40b00c03031010b4151b842c060704c01601c07080b8100c44102d52400360b5001508901c3c000840c0b4042c041d0640040c51112241201450211180b0310405181c1da10b00b51304210647c4140412981584 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 106041501 1250 106040251 106040267
    0xa09020a170a0902120d030501080303090c090c130b04090608010c0f0c03020f070f081504050c01050a0e0a03080c060f0c0d0b0109050a0801050103170309070603050705070c0b04091a10 81
    0x81a03000043c08107100d5000c40e070b146003107220f5800c0c954044a042521290325018050240054030041c41c11410030b10600d55071007424070030300c91040400ea00090041d00380401501e85c03111020240e084001d0341c40307480e210310703078854002c2c06109810200041400141402a04078240955950170701a102000b000c6848442c0781a086085001c5d16008a00e14031080181e00c1c050070501d980d949040b4a00300c0701524206e5070310501000e21200c8010032000ca00c001c40c04501082c001c0c01c00550b07409005070221780170010b1a01c00d41c2d01101c00d100c04810303c01488041c241c0c8100e01011201a41c44e0200210a400c0003100c3c03803117648178100280c040058980c3c0100c160a0018182030800c940c45000081701144240c00c003400d569960b000400a01551499110000144200b02c51135805e1014807103407921080d0040714181a03da00c00308100718030440440750381c59000307a0901541502c40f4031444040d03006106403003089040a003644010b0340c4499035808084401070040300f456296450030b440d40a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 106042751 1250 106041501 106041511
    0xf0c0a020715031d060907050108160819090b04060c0c02030616030b0301020d2f0d020906040503010f05040c06020304060c06050612150402150708072a12020a09020a17 74
    0x191100004ca540e209818411070507911403c000d02840d1130460142031418010b81c0c08181001080e50501c98050440700308165100c4243c680f2041543e00c0590320083c1a203d2100c40c1e00700c51601406406000c1d090710400e00171071141030140300000d0480d0007210400c450711000b175495000742000c074400d42e08512000ca10700000341000300d080301c801c00000703003280c2240e41c038012001d0316a0f0700341c140c04644840800040d4541c4000c3d400d218440107444401d40901000e400c0e03119070000d01c040f240e03500c110a5600030800100248080d10400d40c8040203000b040d2000c85104002800100d42140040705907000e68105a075100c40900c5552074003805810050042da401c24991607a02e00510028402040e003002c501da010452030070702d4818003c21400e134000444080c0018400312000443c03450880314801d4200380d07151084900b18000094520084048491503443c809001501704640340205803240d00881d03e00320035507682d416900c141c0c170440b200180001c00642100b02c1340070217204c000d9005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 106044001 1250 106042751 106042757
    0x6030305162901051f020601060e0a0906120501050c18010305180303040308010f06031a010c0314040f08070e1e070504050303040b0d0c030e03030c0913020703080f0c0a020715 77
    0x10308607125850074003030035590b030110203214450014851401c02d003a0700c40350f901402d42051498510020300075119034040c052901080503400c031034016a52800c20303400140504030300400411b569081d0040c1e807941528000c407034550030a0006041460740b403041d51218643c820000b002e0026090044000781401414824201104c050210b22414200055841b03031f44a5118440507504000214210008907446601014207090203083c5e085413691228148043c01c0c2840248080c003071400f50f07040c0c0d0b0a454501e803946008200020618039402240c41265410400c1d110300c070351102d008104000080711000b84109001e01c20810b4070041e4652a58460365034901a401e00d921030000a0440e4800c0e07011150301c0c0390218201d04040c25920070b0103908141c0382420000034808401058890000401d00c03e800e80d40400c3d10483d42d00e40f1414400040240c120840d601c40441c07501500040094030301c010302580b00000620407007100402c403120214070f07400808016281c1840d014240c02a44030704010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 106045251 1250 106044001 106044023
    0x1d0d110106150c030801091512030e12010b01030b0303031b0702060409090f030306270209060c07030c030b0c12042306100302010e030d05041208190305060109090603030516 76
    0x41090b290452985030b03459030b980d88080034401e042c02070194106070488000740e45000f015810710b010031240ca50454028801143c040b04050030207407089a503103c8900d8021200e40080e55050506601810700684262400c1000402413800d0680c0c0703002c202e81015242440b0480c5114042c00b5401a00b8060720007410b151070325331240703455406d4a07001c59044a80c042250070003820141c0500800c8080c1241c8104038100c00010401100b000a0030503000040503030000354035100703880e001b0450702144003000413510270a98a141282c00d40019100c26105080c0880204241d4107030f000440c2c868100d060440500c50f103a1f51507400340030303e24180e105400d036030302c0041411920741807246c01d120306954400684a50310f07500014103900d003801c1c50340748280c004548005840c0e4226040d242070356811240d26032183e4007403420300e1b194440e01021000d141980c02c1e0150007139a05d03400c0503109860a0380c0c0c0e4034180d9940c80e0801c0981b0041d001c005e0120700103200c8440c10101c07486071403c2c0a8050498030038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 106046501 1250 106045251 106045259
    0xb030a020f041512020f060a02060f1b070b010906060c0201020709021326010e1c030911030a0b10060302040302151606060b0408010b09042102120a08010501031d0d110106 75
    0x2e1808000c4d0702a40c500b01d0350b90880342c250315000745c4c0c5c40240d88064584034a8500d2000c8000d450303a00007407501c914804840c011600d080b00d0908101724440b18584420364503019402c154203980740034425000e085061032408134069100740f0300c3e5600d60794103800402c2d0942c10020004080e402034410441c850550200c002411001584403600d0139843d46420180f06660b0030a440c00d450900220b082181d1010001c0c00c000c88032540300d5207113001d440c6000605405c481c54101e145e4440880103d81c50b21a41030564280201815401d004403070441c4600509a62510140c0a901552001a500c0010500844000c200ca6401800d20701e001c045c40307000a039034a0341c48004645d5503400c0700740002000326090080b414240b0504008030f00403660780034249080d03518003246024850003c041006001401804640200202c4020b4900180e00c951500441308005111550904c01c50340000c1c200000d00c516640c1070b40f6076000d200c0d01c0a020389041001010309461048202c40b104231690340ea180001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 106047751 1250 106046501 106046531
    0x4090b13060b0d030c050c030114180a060c030b27010902030a0902120c040b19031202030c030307020d0807081b09060708030405030414090108072310020f0607030b030a020f04 77
    0x4200f6200b03840744000b00000b030605501d849003042c12203004c2da140c0044800341d1800f03c001c55610104050303840c02d00c00c42e5100d0b0641828000c5d04018107182c10001002421070305500300164100090b249407040340905031101104004030558442c200d61000018407420b41c00703400a6034002800280444d0000490f80403c5c400c2860683d15202c80d004980141100d282c03174000c03501c040e030013183c0031039440240d00c00c031080040017844002e0042960b2303044042c00381e0091040d54000c00501c000d903a16031a15070400794480050803a802e00145441d000144040d0061010701c0c000c0c150301c0d1101d9800c204003080c040300c5500c84041d480d4018003c0c014540000d40303a1004510440c4610702031074840d898050703820840c5071a101035510075403a0200502c0700000004040080720100741240c41c4500c054801705207400d0414141a030031030800001001d001d600021143c01035003145c2d0071220641d1300c000084085984540400c0c0d0316404c1031207031501620341034550f1901400d0050002400c4c0d140c200600b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 106049001 1250 106047751 106047769
    0x1090806070305010311030a021302090a05090a02040305060f090607080c0f0714071703070f06020405040f0905060a1a0105030901060807080a050f0d0c23191104090b13060b 76
    0x1c00281c0c643d001402040f00140602c00142410b038000c01c0d1500140d400a1400421880c01060b40365000c0351401c860394a90342c6013002880081c0007030303000d42000c00003031000e5480b030301050760306104020110f443e02d80c47e4800d42d8400c1003d1030141203186c40351401140d9080c4060048450b0304814130400391050314410042008901c5400f160b01d0303040d00b4226042c1010342c2ca40c401c0940038a06218604500c1c4040100d41c420340d0720500c40110510a0f26000b0300034003650b004160070929002d00b12004286551004082a00800444045640c0c106c15142a01d22110036000894009095080d0a5003e20701568010a0306ca00101314107444406507441c028240d0b200e14000d034005034030350781030100600003006904000d00250043c01d841403009800c1640902e4005d001c80b040284042d2483c4041c2c2c03250008138245c1040e200030300c0c0e03034000e0188c401e07400050945041802d0780143e034151901d4410070311300d182c1c00400c40e4000e079540b000c0b41c1d040c3c0100a8041c1c0d8595100d810740c41e02590782c0030318 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 106050251 1250 106049001 106049011
    0x60f03060d02150a02010612030c03050a090f0306020703030f0501050a0b18040203250807051204051615030609020313120203070501060305060a0f0e0a0602090d0204060f140a06080406090201090806 87
    0x61140c482004d210001d007514030342c1e407080b407034040c0700613154002c20740c4102c085640e0b0ba01820701d00c1da00c212070b90044a01e14083c0e48625001d6242800100401c001500206259402030741e0070b210074000c20380c005044550a01c2129441820b010040180113146d9001e00b4840304803409181110b6050303808078042e42d101311a11030461a055a0801a941e1070b2400b0301c6000d141d40c54507820b64541008007802501c18100c50201d44680100020200311041080800d403075040c08c2800d049680c0c4000811031400b41c004294086403c01c600494402d56038400d803481490100298203101e8110303150b10491141c40c0c0061411070204100d1080800c100f401902d000318031603001844603250014000c0c0845001c00790100b5550b045c82035650355001b002800341d04440d0084001a0703948036800000d010941640c0c0020340050403c80006a206030700e1003035070100c6051420b685021503820b010400d0b251000d0150360040303600c1030040b401180899006035010b40c810305080e050a0781342d1041c50316100781140c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 106051501 1250 106050251 106050289
    0x3040c06110307030f030510080f0d02010c1b0209060105130608040203010c0804050a0b19180204112706070803090604410124080c010509060f03060d02 67
    0x8040001507401440300341903000307000c051420203000741c1e401000018280110303010036484d000402e40d8409a0b00300305004021030012171703001c20000b081c1d698986414000c80c0b0b0265103051010794416010b1044441d0f604003101d20788907400c00d00c2e401c00080b00000b0f8449810407105001d01c1150204072036040d40504480c0d00c41c19210f00d050710415007074600c1000b54108104512040c8400a800012041416039100e100045565540c18080d40100a107600840880f405d060070a80b00c80707600e9102135070090013a03405200100d4110450340706440351445c0d0500244480c143c0412200500052550840006125515107581c68072400300c02e400944100c103142d0468000c0c0803c00425021010044500b0403a054611320050300d4015902440c3c01ea0381c400c41c00f0015140070b1140298008903070f4100c00d410b030601012039244030040e04c10003030007030f15814410720004032855030291040d00d80e1404020100741c0383c10000d150200700c5420141c01150820558552080180d4448002d02c210034800d003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 106052751 1250 106051501 106051523
    0xe07090b0c071508090d030228030f0c0c030206130803070c0602040f140f030706080a090c0806040f0212011413030507050706030b1503060d021215010602100e0f07030b070201110304 80
    0x101c41e81d4140390f01410035509040c8100900d059074048510008092703a02254001410040e41c03000380c016142448148c44c40c0381c50140f0401e00c1d0f5400680c40c4407694007d900719055556100d040c420f01e45040400030b40f1010042c03000540d000d00c81c680060b40184a00009410156250291303280c10013203410040d0444050100c094480c00e02d031550495900c411002000104d180080c054200d00015042e00c11454481c5511421302808201000007003035030b0000c442e01c134030b000c0c1000e4a8006103110100d10031a004c00305c0750355030310f014050b41201d441c50810600180d144c00c2d441078011040081c085040c00802d1204001007001803100400034402c179200400d0341440d000410401549a00341641444414000d1002c941c407103486402007260b0650700d80c2580d1403041ca0503454044a080401031a01070707140045a11907010070300f807080e03019001c4144109142c1400058442c0c44a8500d2000e50b41702000403c0407070f00c059401500034016000000d4600301c50074104806520841d02981d0100c828 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 106054001 1250 106052751 106052761
    0xb190f02041410080402011d0d05030301060f0801081506011106090607090803070314070204090210050c0c0405070e091801060b0702030f06010302060d02090102030d0e0c0103060e07090b0c071508 86
    0x3102c10002042d001c65240c2caa00203550340c0582152000f910107410465009800d20014068644611303400800030542c2d160660940b0b88296603a209015910006070025040c510440c059801c15068803c094003405501101160072a040b00c0000c0099041201c80306019200200034000c0034010440480030b8032032440d04040142042e0350f581e208914640c0200004008a42e0204110034500e249954040c0c2d10080c500014001d45550340d4041e42c861002c0140c102c0d00c42d004401440c072024200c0070f036004c0340204410070003140c100300c4688000c00c1300e000f050710261030b01050245d4080e4041c0d080f901800c1c0c41405031421503d0035000003400e04400180c5005500d001c00010000712008001000741e0b41c1964013242d02070140400c81c407010b40d00032442201d2680248203941002c5c0d41b0440400c0310360030032400141e0302c004902e03010380820b141020114480c00a441500e00c1128141c8866840502d001d00e03200b1103501c2100c41307000030b00030000d0114480c581404840c41d0085242c0e202021400e003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 106055251 1250 106054001 106054019
    0x20f031806060910060c05030c0303070c0c050301090f0206030604200409050109110703200a0c09050f0103020f01120b12070602060c07020f010e0103090f050f0706080903070b190f0204 81
    0x400b40c0074034441c9006904000718001001020420b45183e072401c004d0318059032401510b98010020008068040481041401540908025901806071086403501d039520b000345401c903507040c00c0c0a002e51403980d420102605044d0f0086400500c00352000a01c100341000c0c90201000030000405641c9001808100046881c01074901410a1000800c915000788034410000d20441000400b070050005d85610003040300314150000c9a0075409840c62a0080e180480100c00c007030042c041654a1b02010420881ea6046282d05130f0398050709811481d804030005650304049501003403601d40e120b600340c034210f40b02e444000481900f143d004261103820060b01070b0408200810043d8030840034000c40025984031100d410880740e003030074801d80d103408240040b00540032012000e000b0308202c070303c0b403804c0103400a000c0c0a00620502035403091911010115003004083d60500c2881d88103201c980081420003001641046802000f041c540c1c2802e007154080c0c03035808040c480c000740d000c10308010400c1d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 106056501 1250 106055251 106055263
    0x3200304091a1c02030a0c090c031b021b0301020c0a05100507080f010b030c040801051302030709021e0306030312040309060e1507060c14040f030c05010302041a0706020f0318 77
    0x10302e00282490540d030820118a1910100c40142204041e2541940564400340015000c058100841c858656117404414028207419107040000a02c1c144030540004800d0090010100217580680b46000105010700a42800d4184042d41954200070200842004029842200b480340002c0d15440d6440d40c0d03a242181ca00074440c034184901c4c0e10811148594040909042d0750b20422681d881c3c0e00d4459100034039000d41e4012204541c640018819040c9800c02d90a2549100b182100c080d242c07a40541070990040f03a08448401e0004030400400226000c095903003c1c2020701124189105035000e110401400d907015000b10301f80d40c4050140319403102c501f03c4202c000741c4120030054602180d034016481103120190509565002e8088142d11440c0c840c0768100c11440f186440d66250410145c2200c0141b07c21613000031500b200056650084c02501d04403201450109820f030320302c1e185a4000d81c0101301c100c584680c02c000300c1c01c0281587e0055809580921081c54500420b171600c1c503d015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 106057751 1250 106056501 106056521
    0x3110a0810120210050307020102120c1207050901050405040e010933090b0c07060608120c0c0301090305040317040905010f05271803160803060108010902090906010302070320030409 80
    0x10160b54074180c00350b20f6004003003120404601d4002ea4070707540c02c5002c900a000708280300442c0003001c41408880d840c0c0802800b400c3e810b1251010300b9880d202c20568091040d6910a03004c03074000c0c0402c0003036141c00e40c098011403455400205003030166503070b82c61000d5410b20002112101c240b02080e01e410003440d1541500010b2402000f800c11107444aa2940b50000d0601c035010310000394017410490690854070003070500b4002c40d11221000114034550750001105900c03203205110707804071280360500400e002e40d505611805d291038190f4880c000206142e00c54101211002c010010301000c01d031148c64002d184000ca038403c29402c02c0c041010705202d000d60040d42015001212038800e0300341000c680c1104003c1c0b08002043c0e0010b5106095001300c148540d100042c003c0c0140a0124190046215075800d80c2c03451010303031302c800c80c12049010307050b2643e42044005002440950090b80244620f034002d081581d05080300c50b107110342c407a48403902c0035075a42000c038040006c41c6050007004903803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 106059001 1250 106057751 106057769
    0x10c2a031d06120403050306330322050106050a0509060a090b0406030f060609142e090c0207030501151a0313020604080601050112060803030f0703110a0810 69
    0x104540d40340107024400c0c040c00c1034075241d490321a089280d514401281c4140442500d071030118900b0f4240600300b90000c0358080c2c01004589401c084c0c2c020700c85440c0c07445080018101c030296200107030300c0400d9080103095007504110010724000a41c005a111019103220320004030f401c50500c4140b021440d4981c0c00a4003940c1514140041c6540d241066015140070b8800029402c1c051000500640003a90014043c042c06421010922605400c18401d5460855007841700c01145000035400840850f101180c990005880041a480b80a001250043c01081904040e43c4515030401141d01c40c000300e60241e404058100200f00c400e0203100107040020300c0c24030070780e464116003100d00030f40810005031440c0000001000000462802e15140e0f801070056520307507031108000b680c0c0c1c45081c0140d40c00b044240200303003040c1c04079006d50b03000d949240010f18210380320a400801d43d00c40c0907012009160712289074181c402c0e20000030323203c03403140740e5900d5000e81000000d02d540254550802c1c031318 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 106060251 1250 106059001 106059077
    0x30605030d0f0203091302180d021005070f1406090d08090a1104140414010608061e1e090102040e06100807050d0204030c0905010501080702210901020f010c 69
    0x440d5000709641442000d241412500c1d000b168000300d0840c4548502c4592102e0403c1c40b1071500c0300280d000d081c0110100b0a0340704250b0300b18081085440c19600003d511644081103020940d229001074000346110b1201c0c0d1804298542d1041d031031403000c250302c20b4507501c801c0412003482070070005504068201e00f001c0e085400e0169159446860031040580f0350008010045180d446950080140c003218034000300030340c01e0629040040000340300420b8243e41c205000450a403601180481c042c890702c1c0d0040300082c203d1000407840f00c4000304100c10181100c00038101003428a12510f1050452200050b0380701d0a0014500c21040c000d00340d94010109a1016200c0940103114207402000c28105181c45080d035400110285c03045400007002d41c03006003000035030008103810042c16503000741c81c2c048403541e1721030080b0395070420340740d202c4100d40003d151602080000d4004000300c0070103105482005103031503001030035a0003d0b000b0384005031902c040405d61007801e100c10780d4038005901d80c20031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 106061501 1250 106060251 106060259
    0x106080f060a030b18100207030f09060806011e0201230a0c050301050a03080912030d06091d0c010f021002030411090601050307050301090c030e0a0f021203040e0a11090a0308090a060306 82
    0x42d401801054081c1d01440050052185e1204100c801804c1000150a5503600c0c01d9160003410100e8402155011501300350700410b0550040700141d1050f18103a441c5080c40604c00e003d110b50004814803072007903550720320740ea4030b460501345007007012850700254011403810590880000c40e881d4031020000c0000a000500c4a5518080301e001101e8010000d40d48445200c0c0025503e0044450051814840055140061b00f07464020ba412609038490400080100d1202400c442403075070748100064015008042444d0300410006a04051038411550500b005101d44022a4800c0d142907520f6454044440348900d49a00550781c014001e1030040d04604200d40e0140640c0018081d601181e500c031880244424801c3e80320740810004642280d0700300300310742042c001510041c0816405900750b00905050300b180041103500300e40d10841811180c0c4e54240c50300c00285030482404a240108120242080d924560000c020b1406801e07003d640d00980c00801002c2d807880c0e0300400605080140802c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 106062751 1250 106061501 106061513
    0xb04030804020310180b100807090906110f07021020010f0506030c030a030f020307020d080a090803040614090406050301060308180306070f050c070315061809050309060705150106080f060a03 84
    0x9981160b106a84006c1a1502c00d401c2600b5003075074005903414420f198000810140c0c40c0c00c00300701d05000304010042c028034204110a03901c90541505442e0b8010072504005042580140361181424505000c00712012444c0384100c1d0400007404000d80c0d194000240100424850650441011401015026181d00100b034554608040140510500760200c40007140240105d030070480d80100f03074080a10007840d001c0f00c01d8000203070601c00180000008282ca0400000f1101641c4880c0c841060403036603410b061065900408a0f950040d88074600060a9102402958040d501c1440102c0d02d0b00e0b640203466205c80b2220324054070944c48003080c00034854100f40340715250800d91400559480710009246d00d400015407008080d4003168400d40103194490384280d0a4605040020802e200c08000300403d80d0511000902540c00802619490b458218001c01c542845802034590300030b00090545c0158a0176071110021030801c0082002c9880520300c40c07a44103070122008100e01c4d045456003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 106064001 1250 106062751 106062791
    0x30912020f060a0c0b070504030506100305101503050f010c17060f0d02040902090703051b04080616020f06040501061a070b0403030519110c01050108071a13030b04030804020310 78
    0x80d01500b0000303403414055104a07109080f054020f5a1410a400c040c0350003440c903803081c0701c01e48460040070003145903820040b40e404112038000000f483c110405080c544002d100d88190001818004000000021401c5c04a081464040340000401c0c40c84900060704881c0c86132507840c2d045540c8000c11032565529900302540c1d2106491484500f0b00e6480800c006007035000340654000bd0610030440e450340d0582109108003900004041e28070b10a440303441b5103000e40e01070b06000750008000686041018244c1e038910080501c122000d02c80c5e003c8503e81030400545041d10582d4650a041c850000000f160f15038a0171104041031404000d5100d6040d00c20005d00010105a1203e0104091168104440c8007841d01c0b0503040091051083d40440c080d8080d8103901c110303500305000000c0100c8046500411101c4146000310741000001c801c0340e103580302c1421011103c1034800c01002181e01c454105100b0b6109861b65103880c20580105440c0c0016040240c070f619040840d0148000072450349 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 106065251 1250 106064001 106064029
    0x70503220812040c0311030109020a031218091a120a0f0201030e030f030109051f0e060103020d0606050a09080303070e060d1d1b0103060302060327100903091202 71
    0x40c40c0300051040c03900c08054454081030000d4030308a40180818000603000f0f00c030440b88541b01c44011588030030103042c03d07034895203030103944200000c004002142040034192906006440c000d40a050840070320864644190007038181c050f90744a490801c0c0401c1107070729080a6040790f0103d100e4030100c412070b56941d241a001403849070315013002d50459010b0341010381c9403880b80d0203032134450044600100140c5c009119590440d810310740850b241d00241601c207440c42500ca40044a403030300f400c000d07010a80000e8030b550f0426a0821801d0003000300b030b104900142955680c0c00b961284005230080114a003034002c40e455401c1001488201034200304014a282002d445103500d440d44501040c00901c03264000300302c8802c8012005d03151003004254181c5480040c510201c0f0010040011411600e141c04001d41090003000450791030544102d9884074041204402060504040a03445c01c022500001c4030489444140400c00c2642003820070015240c54401d2901d104250340018489014403a2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 106066501 1250 106065251 106065301
    0x5040b0712031e0b011d03030307050315030105010e040b180c0d02010e04060e010f1401080105040b041b090501031a060403030309140a081903021206100c05070b030906070503 77
    0x1e4403000d041c0070380c02c0030715400d0800300848840048111940043c2c80a4580c0600003084105c00c1e07216002460700300e100a40c2c0c041d000354159070b5682401e840681c80600b00007004010004880c4466800740940d40c060210b0508000860501b031810700c040700b001070000b0070168000a00c00818102c006000c7c0e5942404540070b20340c602d280d00060f561968400c1c002c40d00301c0d0505501045240074002228100c1e0071503038441880741d540700302c07185100c072840c40f01c540007800460040102e8030f4560060800424004d0002984020914802c41c8080d0300f40d61140102c2e4103028100719540c0c252060f028254010b0749a0151181c0d48070006000e8441d50000a091660341c003c1c86041c00881460904081000c00454040065904007071005070000003204080181c12209070748103034030900070344008604800f058241610307010204600355801c035119004121071a42c0410104da070402100000303102d0032107259500d041020206081ca000242224244042001840501c103103c60316081c851140d06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 106067751 1250 106066501 106066523
    0x70314031311061303050c030708150604090602091009060815011e02030715091101030605030309042a11070501080115030921180501020105010b180d020603041407050105040b07 78
    0x100055004c0c00384110904051119107808020420f00181c1d5003100c4208804880b80681d031040d00f160780c1d410180005484060300f401040c0142003035080303204900e00c1200e01504101c030030f8002c18200c2032688201c000141d28050104501c941051034150070040b40e80400c01c2d04518038001074021104003144420404960584003405031080c41034130b40c443d0f800742000c2c0c1d50b200560441070103081002400d0303a680103901400d411030740c028450a13003180c0c0d0285c091420214044100001421002000004540b581d508030340d07494050584080c0c442450b0301c4440790000c0c01101300707103028040d8000506002000300148800c030400d11411130728818904c0c1c0407681d68245d141c810007118444000c2505023856440c0c0f100d032190848090300f801c0741030944c1c1040180d65500124281e503c00c2c400c003103040f54204604003100b040b00b0100b0303241d84406861a1181407640d40400c1140d80100c0701a602400c0c402591301c0501000c0c00200c00070b140918205013401e05210380c4482d5880b6420000782008805 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 106069001 1250 106067751 106067783
    0x100b0304150c0801030506060a0608060d1104020a0201061701020703020a0b0a0e063909010c02060f0d0501032609060304060b090c03090106090504111210020403080703140313 77
    0x49140000c640300c1c0d40140025244482c1c06000360f003080c0002c680a01495001805d541000c0741c46104880c03c40d03036420385e9038403224180019a02e1203c02524008403000848c001500e4500040c002141c003a400000d01600d040001800c940c41d00101701002d0f4010007580001c41e030f001991000e402d410003181c600c01e403940b60b0034400501c854003a54407140900000c0242164010145a00042052907407031002c40018a00c1d0f11280c10000120852000500070402070703500c00c1c2006100ca6201810072440d1259028403006503800c5074407a52a580c1e01c0e08018010410354441507400d1507001110810b404103003030441d0312140128103007070b40201d401100003007e21005812203120a2006003c3c40c45505091111041a078011503e80c81a9030801038006814000c0348143c601c1250042a10001071208108100200300c098003c01c00714410507540c012081c03c1132000340000c1d40705562199962003240313005090300c5001c918590a00c0000d00800c0300902c25241c0c076a038455400f150381405030402d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 106070251 1250 106069001 106069013
    0x3140403050f0a060b0102030c0a030503070201060e0a0501050102012307050d0b0612060f0f0a17070e090d09061704061d010e16080a02010c140a120512010608100b0304 74
    0xa96001400c503100d0501c4500040d180841c08107036060190506000c00b02443d80160f0b502c0c0720f004540480c5500c160042004070340300e040038580150b03007880003044042d40c640c2c40c104d0400041c3c2d098491240c0d601c00401c06907809100700d45400e000200654200d020201e90102540704c000c00320020b0180010381c2c0c0031424107075070008502986c010811500c41c1e035189445654400300b1202c150003201c408613010b08501d044140c80a0408008068866440c101104003400c0780b9008000045441a1640440e81664508405200f44181c030018440c40611040c001c05103669540000300307000d0501000c00d0001c809c4995950300a030050303000b03d000200031144801715102941c00c0f0526500e020300c0981c085201103541046543c004148500040d180c6000a072201c9500758002d01060380c5601e074400007204da484403030b450603018082d0b40045040343c4514036466800110140020f90005980c0250354035010aa03016181d00d180504403440c010a6615070404c2d64040c844184001000003030800c18 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 106071501 1250 106070251 106070257
    0x3070e07091206090c080a060609060f0506070f0b0106050703121109010507050a120c060b0a06081306200a0305090a0c0611120409020310080309010e010e030f01141501050c0304030314 81
    0x2901c0b0341c2e00700700c0030380c0d0f024500d48444a071f0104607445802c2c0713000014800194007d40c02603505a61f00303166024503000030850315500c42501110008005000000032400c1e1003200340c000d10781501c4483c9c2d280007900e001001f04142a18549015107440a0320404400c400c0a561900300c081c00c159a41c1d007040c0c1840303860406940d0004100100444406580a5024000c440400c3c0300c0e4101f4815072681000304440c10030307180250400102c00c140025003070213844040316003850169500041e0a5103003841280418290110600c40301c000003440540c0d5a450302c5140e510095241c017030002d0512a07554003038050418400c1e2030400002022283d0b4440c1c0070f11083e0313103880d420301d0120381c2c440c0d5910650b030194104660207031007803403000c80c001035911000c000c6444e040f2059460002d01494800155400403000c801160180316402e1041d149100034441c4980e0b518030948520740f070b403801050001e41c408641600d0340c104801400040d042110000c151010749034582040300409643e0340e00c02c10b00b40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 106072751 1250 106071501 106071503
    0x8010303140c0d180b16060207020d050609010c27050112110409090b0105060703140a110a030c050f071206020a020a08120912190804080c0f0c03070e0709120609 71
    0x2005802d48000c8103070300401e038000d0800104c00301e800c1151781c0d0284081c150042d03041c040c850707250410002000800503030050054610003081ca139200c1e20903031203c5182c10f5044420440aa540d245d04454858001c003c000f01140ca2580c00c41d44454000000c420002083c0314a03814003e2141c500041000290803107038104222a070201d4860340c0d100e800b48040c00d240c400c1a039901190030008a8503090980c03c481d050354260302c1d100c004a00b2042100040d40c40440c2440401030f1580061a10002c14401d218586009030b84e03051056034181015030505401c0c81e0346d200c959006141c10400059044107041c510ba0b0403000050301e500b0034000c01d905284103c4070082c000400001c2e51194440048030b00390180400700100c2e0184411040ac401c2148075500c009040d05807030700d00e41640f65124020050707100744500190b5040a81e03903101c5501d00000907491400a41007451803c0c89030034100040c500600b0103036400403a5041608024005900d603000d2011080d00c188055814010380390081c1e1181c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 106074001 1250 106072751 106072753
    0x6110301051c110d050313090e03041401020c04050a0b0910150c020d0503070b04061406131e061d160f0f0203090307060e09161209031b060e060c0a08010303140c 71
    0x808a890265100c0e48007203600c0340c89007c00c030000709041519100b08500c3c0340e08240158a01410300914000c01101280c40174114402ca000c500c9107501c41d805014040d1000c0080401c2c83c1071075900300040f00400502606814203d000d0400a20440c0d400f0b00d00c0282c4503042c08401070b040c1d800030a0303201201917805072051000241c60000c008260b9419442640510130030040702241400c2000501c0080d03c0f250b07804010707400400d0310440e060303105040d03c402c0c0c0d88803000242001044182942d80561100720004515070031010121080e500540d4031203880c40421140341403a03880900350390400d1000504011680c1040400b9600070000c841030b1000007012142c001d69a42c40050201304201000313030203114008003069000c12858040300d04001103482e8203048000e9100307503400a211035507040c1c0802c03841d400c62054016000300b0866036103015405c04a541e418884541c0c4c034055018000710024032080003402052903012031402d06482d4545000045809540828203072f90080c21840e0366a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 106075251 1250 106074001 106074019
    0xf040902030c040e070308071202060a0603080306120f0105010803130e06150a0512090105010314030307020d0809071703040503160b1206150d1a0d030203090d0602070b01060201060306110301051c11 87
    0x30b000409c2d5102028181075402c0790b1290381d031401c4280a0750098800148640000e00105003d89002107601090030100021a00241c048641c02ea013900c8080e84044004d40000803080e07200100030392404083e01205022040508190000c5041e8100c458cc600c4061040850061070742d91240f012690004c2c04000528410f05040801c9802421f0078841240c1c0601c00400c03841d0b51280c04010780c1c3c41407120380c015143c81d241901e010740d001c400041c04503200c0d001d209404a050003103034040b494103a072042c00845d00c5a003028241450441407050742d854103075401c041080036100c03003002c0b10a0701d030007400d009090741c0f91180424130340c5480d180d801500100c0801c2c2c0c0c0180d84207a074030441d4150b003094908104540c456040c40840d0380c2d2000080d00680040040a115041103d00c18510030b00c110001407a24249440701c51940500381c00010040c2d444260410500900f030141186400083c1030252455141500164071000c00d0441640e406021021503010f00502800002d15000e000c0c1000302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 106076501 1250 106075251 106075253
    0x201111c0209060c2e1404110a0503070909050105010909080a0507080702041b0f1b0609050a0b07020304060906030606080a050a060801050106031d0106140909030d0c0e0f040902030c040e07030807 86
    0xb4005c1d084a007600c808151031407900030320042d80900c0311515880700a240c0e0039107841e121249004c3c0c40070b4581d60800402040016641c0701040304400428000b90001510b40a91a0090a407041030340107404480c10000810041b4900300300720f94046903c0d05109035108114544039129019444000c0d43c801d1a090482c07040035020489026203520542d2091740d8035034511340946444805100b17444c4005001c001c140c00081042e4800c1000a0142c030854040309030594482d4018a801c59074040181c10205007009042d0304445194017034005c0d0b0801344507290030301d07100502c0c001d802010007802984803404110300001c19400038010300880002400340c3c1d80c582e00301401402d0500e40c0e0314102c0c080408010030b511418490036080e54140d0f070000d24650f49442c200102403402500b4036866000801061200f40032034818010f40030456100c2541a444c0c15007041059088120602d0090741882042c1c0d0042e540412203103483c070011074001a240801e5000c041c0341c181c0c2908001c001c2da8000445078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 106077751 1250 106076501 106076533
    0x1020d141b0301090c0306090513020102060906040506190b1002010c090e01150c1e0308100b1201062001090804050f0d03050409090317040b06010201111c0209060c 72
    0x2881840c180300311a28152610300c620710414000200d02003107103005100510041c15640c00004626900746408540180c49520050444505881200c15050702d0390391803085507010b200040d40800f140001e08030501d80350f03c0d02900c1c4c0e81d00901c006c1041d00203a0b403d80c0c2d81c094692000e04020f1000d000c280381070055201c080c0c000c0144007070310008504980e10000d560001803c00354141ea5016a0002030130194020665a10560020440c0d01040c0ea8001c0007507010310000d50b0340e9807402030361031980d142420b02c6140d004002c990009803030050108010051100e81c065000d046617281d20b0b00c0502000840b2128078405032450101d5040e5082000310014401008085d200b1f44404031040d0f6401030a14042004128100074000c0200b0f40c00c1c44100980d40640e4000c5810314001e06244a0320400c80d00c200314004012202159840e41d0401400020350342445803540b070800700d6036558981340e40003500480d02003059208015103600045c60700025210f000c2603807484003687d0304994810000500c84 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 106079001 1250 106077751 106077761
    0x60a03061e0311040c0512040201051b0c150708030601080402190e06132901050d09120e01020d09050904050106080f060103110604030201080a0506040b060309011d0c03070b0c0c0301020d 82
    0xc2d02c0b40f00350524a0304541c0303131511032810b0004090b1960b5190030071056802d80000c90080083e0306119003070100c110b003040c8071600c05034440c0022000d844030140210810084803a80401a030500c0c00134401d02c00080c200070b040700c0d0400c8007400c1c0301609580f80e10004103014080c030115107a50a54034000501c0c00e240e0030025024840413108200008429056181124064204501344888842c0301521840c1898010714140c1070615015140c2208900e809081d610510f0084400e8110003080c80146544140c8051160720b0901c050058402290300041c818034203405020f21030b00340c5c00003142c01c0010035803001000304002400d841910080c0e07584c1649520007448166518107000140e00042c0c58400c08440c1943d60507100c1c6038807178a41e04025401058000d18464005684601c500c0c1c1c681e4071500a140300b681c2d40700002c5101c03e680b02c8516110340507000c000c42e1035400b80d28401c049030390205010054640d000346280d20340000800c1289010090307004180c16510003d180317401c0c0700043d040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 106080251 1250 106079001 106079003
    0x309040501121a07030906060e060306060f1003020d020d0c020a170403050706031a030a050304140a0b07060b0303120906010f14011202130308040905010e090a08030402060a03061e03 80
    0x104126507a42d42c42c49507005a80400d00400c480381d0464003039000d2031076280850b007000d580d14000500410030b0740e4000803922141c0020b11801c0110040140c2440c1c1006803036400102965171100d52030140d408502d8150700000f01d0000c1c1600840d035080c03070035101e50580e00d01905410b024070002000c041d02a48400701c0d1101964a0320221103455070b80c0c03903494115400c90343c2c060003d10240d860720b9002c4008103480c01000450084210151401d03507803c1110000450241019598031071a113107070312210340c60680c0070328000d420850003080400e440304140c4000b1a0016404149078000c0c0001a0651141020522119012a05024418100040f1541130b501611a2050005d40b2a00089071000038410070314009807034541001d01444907070f006040f00f40303501c0d0340c40045075844e0743c2d40a00035007154000c05040781c0e407903004026090030340001c103410003c0303140500a1040b03641c0b00d02c11248402080a8000c4a0010382100d4040c429840040248401d121402c118100d00c5000031042559102c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 106081501 1250 106080251 106080259
    0x30a060506010c0b2505030405030301030609020d08120f0a090b060904030306150f030506010305240613062601050a03030c0c0e090d021015031704050a0f060906050702060d050402040f0e0309 84
    0x401015800d001c3c9007101c8c001c94200f8001d601f507a00e50356030340c00a0215601c0498110300e0034004030b000100b5000142c04144441d000d0290039103031001c030311401100000c081404030346c1820000d0000c50041d0030f103160031943c241c0350344100d9500e504003580503085640c00816407950060500d60059403111400c12264159503041c81640c5501d8011070030307038100b650800072454440c41710400d400d19900d0a01d10103000039001c0c6007008020400071030030442d10742c002e00103e440c1c0e10841d0000c0000000014007844040701040807941000c2c0841d41d01c1c003050000406006070010b104003401410340f402c1c0018950040303108182c0c6400300300c158039008039103c2c00004d0302c5a07013440310303106d0b06130b002c2d01c070b0a800500c181310481c500e1501c401d204001c0b103404000d14110108408a915102c00e524100078040340180b48050603d4007000030096003039544040200324051000d040180d41c0e410440c0c81110041c1c2d008161902c0354000280108450428075007510700c1c120000c211481e012001c1c24242008403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 106082751 1250 106081501 106081561
    0xf1209070603060f0e060f060307020a020321041502070b040f1d0402010509100e0d050a050607050306030a15140708090106090204080607031503080a0810050f030a060506010c0b 78
    0x1e041076080c2c4802d406821503100d1a51400e005546a885040e54070110017820320074501440804a40309034030a80e07480c40140c02c80e00d11003056080c1002100b1b0711400c00e20180320003c5855015040750f00031801031900500030119104d403058800c10541015103031030003615540c0c0c2e98940310241d010080344505000d1010026141443c1c00d00129402e20854040e16a0782c0740080ea03800f041100e51a51441ea030610040d04040c046548940c003240a040f40705000a00034000c26040681c0303000030090101041100c100304200303068401140c540c2c2010352015102d5008810841c2c801b015040121a10220741c020000304010340f54082c220368090741a4000802c40c00e0f481d002c01d00140d1007103000b241c041e80c0c00103000c283c03041d110b40e00c695902010420a072a0352500c2c0d60364184c140d8056440e000002e41d40c0828480760042c00345043c0000c2008036a404e1880900c0008291038020154000c1c001583e42c900140191b401010f251a926034030038011091843c084902c9640b141a203070140303800401d05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 106084001 1250 106082751 106082759
    0xb030604060503161517100317031003032102030a06050103060515030402120a0507060c020913050c010c11121c0201060b0d0b04060504020c030901230a1101020f120907 74
    0x4136584140d540d04210140c03100d4280020103154540c4140300c0406c000f88041d110440031751800216008220000f403401c505451410280c003c824480c058400e090010414804a41d14210f002021a036140c206507240804240f00d000022030759611000b0380a0001003081030448143d44488192802600c0030442c80f81c45600780807581418500000c0080801c101160151a180e0381031016507103074104581d941407250307441ea03003040f42503403124000c111900e07280700461420b0280709038440505140c0079800c0500361900f0352740b1005148500c2c18403450000344014407520605088410002412000600103c0e1981a03075441e00d10091812880c800c8241122140c818010b60046480c241405c50800004903a0640180014108d007a440355840400080a0b144d50001c0c09488102d000038540341d020b46c50016000013201460a501d140c04d501044828820000c103a071b5980c0d00c0340c94070b011604a00100540203110b140f8854280e928003042400750408091025442060294242c50030140d031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 106085251 1250 106084001 106084003
    0x30d020d020c01110a050313031a070804120c050f030a140310032d21030509191a180f06100311010302090d05010c0306051e0d03090905010b030604060503 68
    0x4080c0e4050016001500800c0740c42d0b00c20030740341900400e03480c1580e90180c0ca603030301c1d41e107980d00c404980e0494040d104001c0080c03012295442241a50040b20385905250240c40102114401000103000c0961001032a50003031140960510300782c2c0c000111110101c060510f2130703503034000325464000501c41d028500056401c4900782d07805011a032007000c80d05425560391041e04401c5007000d03d0b1000341c07100c180a0b0b0040d0640383e4088503010720186102a00403c0d10a011040066641c0e42414144014000300c00c1c00000c44410307902c440703040078620900324981030600c0910617000d0103070b503842031090005100045000b1900e051102c4112405280040c2c540c80e11141c08641c0301c068a00422800c001240e030600c3c03080c00e00c1405150051900341040e00040b201c0c1c880d04015034040c0e5440c060205115090f01c543d4015283c00c4400c00c3d10402d118404403284101c015040c0c4c082c51002040c0001c01d0b0080c0043c4020305100c41d030520096841300c519088540003120500d1040e801d10000240ba824 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 106086501 1250 106085251 106085263
    0x80612010b0f06030c07050105010f03030f0f0f0305220602030907120f06020703050d0203040309050112021e0903070e090c030114060d06110408011e0b09091f02090607050c030d02 79
    0x400341440c25044980020003e450f08010700030703d100403003000b0700c50004500384a150b0180c075030307007110381d0665041d0304006040b1505900d605060103c04804006500d4000003010140040d925000ca465a110805030718808094020b01e102c810b20f0100e00b00410206130061407007220410112340c107040c0d56064100c4000800c00b0060104503404050601188d070540052800d24001e040042c64808908000000c0b41d0084400745d00207003080c0c4081c4615a40080001c00207000400c0550030464140e03040c0d1a45002d00e40c5042d0620303030000e00990207480601011004000107201a40c00d89445014507440c0c60010034210310a52801107443d06600c4038084990240c2009890706e9680d4001d03540742c0d801080c8180741a12100c05c24800000c0780e040c00d0040d0058608000d0206d5000300c02006044182d433180e00e42144104e43c035004000c4101e10028000c0e00820b66461850380c10b40d030204c40700f0300070710031816100c0d000303030000035001e0611800284454208201b5021654696440301c0201e880381 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 106087751 1250 106086501 106086521
    0x1801020f03011403030909010b072f01031d03040b070b0709030f021309050607050a030b03010203010515070f0c090b1804200105040e07080702100c05030615070c0608061201 76
    0x80001c1c0700600510803203aa00c00454900541100d15080f44030300000c0300d40d00260301c00800e0b0700000840b4000c00c114149043e2520041c80c0d91080001d0440c0078001440500c4014141056a1250200c08501c3c11054006040420806807a940c54840e10380291b80c1d4091003081d5684164480030030092441204040102c0360410441d54038040340c0e074200095480311501c07220302c4944410048004c190103000031405905103442d159581d00b010f0350090700307030340c0c10540140c4280d205200401c0140c0398141c010303c3c2e04810315590b83c0d070b900103440c1002c48000c0c0d041c000341c031003c0c00d1f40700402d51600742d43c0f000381c0c13021003211138070840d00021030042d003207000c1140c1c018000804052500c1503d00380e014103c81d0750105041c824141070b2145408481c9036002c80301e60000414607014450565014001000160003c10080c8240d60701c0e1900a0034921002d89481e0203148941302da400b108000d44207075000185d0000700403031403503964074005002c10401d030307441445a258941400704104051003076580c42 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 106089001 1250 106087751 106087777
    0xc2120190e010b030c1b280206090607080d090f02040f0c0c02060d1112040c120503030103120c02130b0f010c051005070201090c03060e060f010b180f18180102 70
    0x1a820404040c6003500302420880c0c2c600801c4c04111103140d407030421b07840f141d0501700081070a0042120312414503002d036024040c011649013851000358803100c085a65800c401e6070100d5903015a40750545140c07103003818801050345026903403c100120380c100e00e80041d000b101c0a10017507040c189568201c45224034000003007409000114010308048010f004041002c000c001000c03032046e84030060551050594a0b80c000c0c2d10020001008100e451100140590035050240d8090030b940b901d50f070388010b000140211400180019080744640490818168060b085040035001500304001800740c0354443c501c901a00308031107803954402c0c1107054285402c04000d004482c4c20600500c01020302800b031504654a0700f17120302c0401d40200c410f100a40c4039103800102e902c0305076105130811001405020440c02d5100c01005858030724010b482001601e2400c004540045030001031500b11155190b980102140022116508408890310b00c240c80418103106141e00c6203100070308038881e2206400075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 106090251 1250 106089001 106089029
    0xc0e0a0513060915020d020309010608070e180a0f031d1e0402090f1507050c01030507090e190615110307030801030b070c15021c090c212019 62
    0x407518580040640074001d501c0d44d4400e00108042c0700503a400100c2c880000b940003c00e00c40311a6013441402d0081444801030700c00c0d02e003080c1c0d245910a201400d49915600c004d80301d0088d2903c2808407100450380001c850380103101c00c3c9005070540060a40c80c000c0c0032540b03840c003c0c46051135030100c40702d2641d540d41c1143c0c01302203108002c020740002446940008540c446030300c15441d042050340419004401e0161904107038a8841d02c0c0002030041d0341c0c10941484140001503400040c54015194807036410206942c0d403030244890051018081911f140c00c00c1800195850b01c0403211034004202d50b51100e0000a502c0c2503a503030b2048100007400580c042c03004001007480e81e40f0309a006040c0d45042801c020304e5891b10083c1c004c030030803200009580020404030080d02245403a030040140c030410303c45031107585c44407520018140f00e103042c629403499004c00300700303c141c524400c4280d0002d441042a540d40440c00310303055195650f180984009800070703044c00204080c42048400f8031038071100d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 106091501 1250 106090251 106090253
    0xe0405091e03161109011401120203150910090e0f1b01021606020105011d0411060f0706020301030c03052b0c060216060504060b1002070506090307050a030c0e0a0513 73
    0x251100c5000000075074002802442802031082c128120400d0040729002c10b0354a1940030031642c003c041e408802e0701c1a50080281043c1d03080a01d103c0c4c000d4000710f0040e129130b20100b0001204483c0c00b10301e0b0f444070502e400c0003210001e070765850064551080302040001c040c08011540c139203240781581604d500406107c00c0c0204030382820111408107106592004001460850700242e958000a0150b512480180510414030312013104001542c40b407110b450816440d40410b81c21f800c0200340c061107001425000481d2400100c0e440e0551101046550390707500d0401310501c0d00503000c129003d0150b91312015440507100071960441c0e400700d8960302e0000700041c09035030004241d842240c0320340c1c00b4130001190458900b070300b041040c010307003001c0f551f8a0300c0d2500d00c003150004000c0900c103010b1204904036460380000c0c0e0390103130340d0180e81c8181d441c528040043e240c120b0940c03180e6840140b420380801080780425854045804d07200c0c09000315240c8840040641d4400c85883e0b0f0200780340c0d00414 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 106092751 1250 106091501 106091533
    0x311010e0c060d09060b03070b0415032f370305040302030d05071205010305010b120129060d060b12090c0d0b06011413050315010f0509040507081c0e040509 69
    0xe5135070352049800040d281c03008004a410500303554000254200041f80402c990390b0304921075140f20009103801c000100c80642d40041140712480e6845a811001d200d207121819440100c801d510985ca01810041b601c8044500c0c0c100440c60b0303000031039041e40a00300d034424042c0c01818040d0398541c010750708102940c000100180402402c0c081041851084c0410205a41c031a03a4042d6001340004201c1c00d10640034040041c40c0c268000f80203a15007a448241720346403546440c0c141d0402c108035107015500000180311402280c8111503094506039000400300117a500620040d140c82078001d142c1c3d40c0e80e448032070711071100600554010015440792400644030f9884a980010141880031106400228549a64000c4518059545101c110074409403404000050030300d90700400e01d0560b0343c104010401c40d4174141c850140980c0c0c808021500700402400f01030094511002280e12654000c403440801d46944071440011a048900c244141e062030300a241c81010b2140c000c1c40d5202c020a0b0b14 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 106094001 1250 106092751 106092761
    0x60503062e03170901021e060114030106090c0302041806030b0117160f050a0e0903251203060911090f010e0a0812030a1d0a12110a0311010e0c060d 65
    0x1040e4441128031000c0001003c981050700c150403c008155190903151001910b44000745608070244d202c040c1e10110705c51400900300e4152442140700d001e0040542d0082409406550000c00a207418072034200c1265a2660240049035440b41340c0079290725103002c220b411160f40e40400383ca9002c04e080140300040c20041030001c04840d02080b1282420910300c14403950095400003980d07280c01f420100068580140e059001c0c0000c1100081075003040d4075000da4a1007184030489842002e24100e42d88648801074002c074107a00201841090300c24603000900030001c60290044040c03400d1510346080510006862441c50003070606000e141d00781c801520008030f40b400d01944040820f0f03010030703e401b09005030040700904004c21f40d00d90034490302c124240c640300b00d44a01c412100c1c59061132515130000389032303135400d800a80b15410215840001c42d26405030905a10301482801c9100c000c2550000540c40d280000d14000c00076600c0c09403e090f280c00c2c0301c1a640d68003100c04d0040d615900465030003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 106095251 1250 106094001 106094071
    0x80d0203040c0b031008010e1203040f02061b2a090a09060204090207030305010302121908070204270203010b09091b0f091305010e01060317180406080a030306050306 73
    0x2410440d40d5074111502c83e43c1c000c441410749280100010800f54509024a482010024029202825801c550084a4007000b80040c0c10140c48080000a44d20b40204440340184045d100d00980c524201045580c0c500340d0688040607415499200512080603104149440c00104210b07030702c1c1c80315550310300501122a0241c401075420400000d21071514401030482c00d120751404607080d03140d801086402c1011520018143c1c1040d508a00d1100351180485407242d0720804860b01c880140c00031400070120700d0b20441d1508102408a100c44421004100e8414822030092158400d01c00c2400810300c000d8605034001e0303220706460004d18807400d03485e51508034060400142c030f10f141800550000700c1600c48541d411505804042440028000c4000020340c1c01e009120340e91030750303964403100188510300c0c450090000c80c00c0d40190038891414038000400030802d1121503202c034800c035101c803c41c21040740828a0326400160508000c502944141d810752595202801340342840f6503018810f0003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 106096501 1250 106095251 106095263
    0x60426030610120e010c020109060501090501030515040311010203010e2a0405010c06020c070605130e0103120e0409020306010b091206060a03060209060f0307030f06080604051c02010b090a02070c0b0403080d020304 94
    0x79042c1502502480745006c40071250340003207050300c030b181001001c65206821003941c8504200c01400810b10000d400401e410380d007489584a41c3c0c1d94101201c450141001c0c20740300303500010002030170f491072148140c041c2e2540d00c1000704001e090705901d0340c41c2140740c204078448402840100195801042081880c0380101009403910003140342541c100f24164002801060300400c000001101c1c03c0e01e00400307002c00070381c00b500650541d19001c6041c410080310004000b0344d003922b000d090304d4581023800f21a07806400c640007541c55440070b2043d03400103078800b40038214442d0f0320b02211200013034403170003200c0107800341d40b01034190f0315401c000e980f0907105903401400800c0900503541c28800294440c000315900007070b10002900303040d001d0b2551544807564542c0b000c030503c00841c00104460302d2540d0f00300811880e4a006c03600c240c1c0580f80c4c03450305982c0904130344e0030400184120b4000703041d0380d4400e0081e81c2840d038543c0c10803200d038000ea000103000c0740e0302802108864610f9500660f000b5005003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 106097751 1250 106096501 106096511
    0x501031d010914120705070b091807020d11070509040f080f040f0513090201020606090901060f0605030f0f07141e03040f0614010515070204060806042603061012 71
    0x800c032801d440001d40c0449140426148081c1c01c1c1c1d10521212100e441d1030918245000140d40b1040d0f40c80c0700c0e5000c0e84031a000001410306483e903405c1c2c0316803a006d00301c1e03150035107038585000040d44952814510001240c1c1862201458140105540041d03500090060744141c50f9900c03100c81f610180b180c112001c40741002440783c4a60040082d000420180e001c0710075013070901d8140700384081c2d40c080000c200341c00c0c545e44500503a0040748280e4000420740c0e240c0c407503941e44000e032400341c803050b808a800030385906008183d05500c680107512980700c4841d800b40540314441c01c050710f1001224004c00280101c0c0c400c03058009110010701104891290300700038600130010288240d4815a02104c4180311001418104000744c0941c15000c1c0f040c580c1c0025035031510f40401c8646807080c1c0180013964000504504541e40c0b1341c4400b0290600714100c0340701e8506850b204c5c4054115002d0541d1401c480320120310704e0003281040741c0c8100800f40c200303464170101410035240800302c00a11200c1540754 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 106099001 1250 106097751 106097801
    0xc012d18020405100f060201140a05060102010b1009030c1a03130f02180103060507110706030e01060306060608041e020609010e03010b0310050a0c05040302030c0603040f08070c0612020a09050103 86
    0xa000f041e000d1100c0e0142501420b1416402001d61001c981c4158196414088002c0000d039800b0241544990703604e40118481c0e5800c40100e0060030040d49495000300c0d8000b8034001141e0002c600c01c280c80c0300e40e1407011001d0300c40110001e08440d0700d411441800c420400580c036480e40040402a0382c0c40751807040b02280d5254001000c122440303c2201c00d403c590001042803001c80d0150750f41022140c01c080038a007058170017803910780d030b914040d1034207054480741114031060b425444400255040942042050744460000b040a8402e59050303603881c00e5442c11080c4080280d03a5a0092640203100b10b1a060b040e50064070704688506034154595030ba14020000b5450610607800c1510300c000000071103190020140e0121101c40500b4000c001d0b0510081c030050b240003d0480708114111603040d01ea41d1240f42401c005950010014000040482c024042082402181065a65580300d45900d20901120201203004080b4900002003544004100550103a407241c03d9070340702807003100e1000d606 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 106100251 1250 106099001 106099009
    0x408030415050c030f2701020c09060316090c020d170604090f02030a03030b03070801060b040b03221a0705030601320c2a0d060e031309020c012d1802 66
    0x124080c440c64015001030b01b51205c0d40c60900300540c03540d2020000045401c0500000d541e1580741100c1800f81c43d0420114505560400070046c1204880d10080c10007610743da03a840141000010140240c420f0016003001c160280f4460391a0201502501ca9503030355000c100009840391510075a101c0040d2450300340940c8007400802c024902030f803404246900b00105140c58103819500200d500e91520304240683c800360401c0700c0888624180d01c03034a030b44480c80000014000c103641030400100701b031054010040360826040c840c03108540b8000751a540c0c01c0c0155000e00c02121154009450181c008091985003103144502d00d0103480c0d03a010040360f1307049403801580444210005980720b0320141503080b40030340221001c00784046500040e42c8050012031020021140c0c0142815100d25141104200030416203403000130a1480002c2c495503074402d030009612844585007a9428410030446101d03a900700c8040c4485403034015490880c0100e5003000415100701700c05040d1019a03122401341c0d417 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 106101501 1250 106100251 106100257
    0x250b041a0f19050a1e051210051008010f090203010608221209090b1032031819050705040f020f04080609150705070222060f0503120408030415050c03 66
    0x140340c40300d654513500c061029140c44105584075400c030815090341c40c0202d91000c02d484414203140c43c100ca2540700c00035070342d052807050307008150061030b0040000c0c4881e900001841c1252100d451091880e511054040c06a2109004170350214400c00081850080503040f0104114041002d0449a961541d035001c00350b100e4a11007000030740c0f05501071140c10140d20852031414011510044446034100d4040c240820103059504a01d1000b84050191840e4211000419542c0600d103a81d0380307896845c1038030400e84000480300038070402d5048040c2003255a141c0b0b40d82c6800034010080e240c640002c010140401c241c18584043d02408000381e0329120070081c00140207041e0160030185080f6150501c0c10006041442c0ca1010600a2000c4507411004a800880c0c040e1103c0d81e40d4003400d0744100e00a000220340c0c9551901d0050000303a005800140d42050325000c40560351100080070000b140ca0107a030103501100e82040000b04090a50060399652441c1d170781c10481e050242400125013990 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 106102751 1250 106101501 106101547
    0x402060c16060f020c010201020403050607110304030501020d09060605040b0d0b07020106170c0f06030106080a0213120c03050f0a03171312080a0609020f0a0305041103250b041a0f 79
    0x84036000f0320151960140071118454600307100171401e2603c2e541f00d80b90344920117080360050112030b0150110180050080301c01071500b00000b0340d51584406000001000140070656029103060300c040f4092a06002d44078203080000c12400c042c406a0310380080a66000e0245000c1d0f42da2108000f41181c410190040c01074102e0010b06414103a003028003414000c0e0600041c404d80082006001c859004102c1640002e840d00700142c982841444038a94428103030400d05e02c1303008000c510000c11010340b45500a0303e1056040e81c0700801d614000940e21f4000b03240042c049151415001c2215260124465100d4a465124004041e032500c46a0500c01c4140d582400141c0e0001000a0b41131140a042d001302900303c011840c0c182042c3d81c4490501418601404042d00d600219051003144a0101501e41c00181943d10700581c4174180340f180180030815030b5141d41903840015250700d4410549088401c220f41e50b0703458800300041c00003250301810513908600801c1c4005400f0098104400d2804 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 106104001 1250 106102751 106102757
    0x2130b031c020a05160608010308090604050a1e0f0803070201050d1b020f01050f01060e0d06090206030a022110060c170f18030a080d02070201030b040e0a0b07020607080402060c1606 80
    0x1154660409a080c1601d61040441703051079032000b0080d8940c8052010304594201e00d00b1a2524401c90002d00d90b440303240c0c40325901542c8404041901c81c207200380040380d4042074407400f0303070740f82d4038405071a00108a120300e03003160b0402d00088025500400003021042c0719400001b55003540c1120050201e800176082900592220920f244008001d01c95a0b40000701e40310460025031503c0c1004101d441444c82642c003a0003184014000c1200d150001d101040c2d0040c007003130f00ea140100c161030094001090108403a085495041d0003140d0100841d8000c0c2400850020150301b411000d80e950200c1c00001c685400e100707490101c03003a0708080038003c001d180080d1345075228800e094840c40d540103200700328401c3e000b80007110300060641d41194002c020403040581c0351300450005030028505080ca10b0340290501c200c075407100201003203142c06d840c840c001e166901d03158103c0803603442104448031008900103801250241c1340900242420800c024200c03480c80110000c40f01e2800100c1d402113000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 106105251 1250 106104001 106104013
    0x151806030c04020c0c130b03060906060d06020f16060b241902070b0a080708061f112812080f150402090d060c08070c05060604020c0f030708071b0302130b031c02 71
    0x47c620301440800d402402c0c68008003070718103000c1d000804210381020020003540d4005144d1500382701c0740042d240e81045040101000200d50b05141c006821081d011600c20f45001e806030035001030550b207560f4100403c40a01e802c0501410000e00020956407110b42907116010000564500311001001030f4100c41c1d5405030350307081c001409000c080014003030f1031007220020f20450b0b001c410580c018601030400c0c58084020801d121125090240c0c101540c00c01c4151203d06403442c240d03200814101501c180402e05074080192411246844180d801106082c42400492003066001a1251950130018801072410a00100080001525050854081d5101c891490015070003000b801e52102d410709050045a4a40d941c0f20340b503090082645118a60101c1c0c0d6200406081142201700000c1030700700e135030301c1c031081c10b10020540103100b0407251030001d4003001c0c445c1071005200308211780d4081c0a6080b10b0f241c0c8074a0f0303000380882c00390468141c40381c0390702c2c0390040342222140c60b6660595005014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 106106501 1250 106105251 106105271
    0x18060f0609021c0c03110c010608150603030a0c0201140c0105040605071e081807080f010b01020d1725090306110702010903080309030c0303151806030c04020c0c13 72
    0x819211203501c81e070001e61041c421107041c1ca00f440c01c0c0e0307080c4165030000051100ca6810302a8000c1c25403100804006101060100b900c000540c008002c3c0c403d2101211902c5900f24914014903004130385081e055081441b410f015140500104404648141440590710020090450701034104c40c0c55004030741c2d110b80900051040c0c42c494580c100045240403204404040544156034601544000130410032000040c070500000d0302498110441c10107403200c6a5555420a603104482d5105039199440d20030382c02e09641c0000b50740301000542d40c441341364401001994082c052801004103c0c200c1d0000302c3c000d04104002003a0072082090740340c41c08e0047c00c0d4100341c0c04031281900ca020030716104120280c09070382c01c0000001100d80c4002c1d826aa562207040031400c5014200310138035548004800e1043d80b480c140303090002e400090b28402d04201c00b40c0384036210900c0990300307550150044c40300c500850601e0b8004000400445c801c41c0e5120f100035003c241915080daa80329409959090091 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 106107751 1250 106106501 106106531
    0x207031b0f0222150e1608060d021f03060509150a03120c02030109030302130b0909040b07210c0e01050315040f09020303030c0301030309050a061416060903020c2706060903011806 79
    0x280c0c01c42001b291460441207400c0d03024080034409021030740708510700340d403840440d07403158804041d200c14046100c54074203403504064003038406030084c076105425950001d1049000c91011802004009040c6072169255403540c4004610b890016810010303581c14243c09a1000d01030707541e1261090b64016502c0d900750100c807482c54907581041d92070900401c0360559a540d60980e0613042900001c0e95500e5440300d5000787d45a504000b20b01d5a06003000014200043c410740c00700040440d1515a0a458040c0800444541c030040301c0d0209008070003840c00d2081d0525030b002080c96030a085000941c0c2400b5000245075803c121602046404004014010954040384070300003414142d0300144a103040840141040004600481126101040c3c00389044500501c0007281c130f8000e03200f080940c2140c20b00035114003201e00c04c1030083d18001d031442020303981c4042004a1058a0a00c0202c5864030400c0002d15404180303640c3d419907c404482c03850f4080d000b440450036100d0035001030411500c003c21 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 106109001 1250 106107751 106107779
    0x10306051816030207080417280204050112020904060b0f030f060a06090b01080403030507031b0503090d020303090d1b0c08030c12120a0203040203010f0f0207031b0f022215 76
    0xc4002c044c01845410700045100042e201503400490340e1500800000380000d00e4810455441007405280186034411415a086d65407079007402a035080c4540da8071503010b1900d4104003500290040a984001804240c0c0d6034054002e515000300f982000ca4400c40001e85030007107401684846d41c02c400306100082445209000007444040800d0041094040000e0442c0300d00170005014991104001a03845110358030002c000301c41614180000b20440000400b190000c40786c0700e82034031901020b04181400007080e6442103030798400900c40c1d1a6400000c585510825120340141d0404038923403400200c0b150012006803c03540001c684824044661929222010b090303454001008c0221a8009000705045940103c0c04030002d030350307074031a0320100e8010580c00c00112030b0705117040094400ca00b0103400500006003e5941e100007a002880b00201c4602114001425906002e01540050504464402c5200c0c1030101c01030303400003000e20500c207440310600d082c0c0b0f0603004550706111120039401c42d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 106110251 1250 106109001 106109041
    0x70f0e0d0302060f0705130b0a0807080105060a12090203060f100b040b0307030b131a0a0b0f0304030c03200a0b090f0618010b0a140a0503030a0c06020304020103060518 74
    0x360301100e51003a1806502c0d420007800240c0034000d030100064502d4060030072180e00401d00144400e02c217581c0c1401d08910b42120108034005116280420003980c03183c1d81e000d06984c001030510b4900345800710181d0307480344803524141a4503210b0b036540e009a0b405102c040e10500325481d581d8560f00d03004070b40c030300c0c07048040d044640b10004c2880140042103541d0152540180e05d824009410300840f00090340c01310050440310805c50070305000000d01d807010100c041c0200800e980c3c1c03100c0280c407100b013040c85000c0e15010001f141d03014000500444d206125107a501d5020782000926414041b02c1e9000038100c00c0c0034031200d54454420301d0104000c0340c4020798002d01b143c020301a101070350400c1540f04c0034050200350031605003c820700b01c2180f082d44002c0c1071100c010300030103c80344d4450750b42c0d08075407110580d41d11480900c0c4000a0a042c040103e0301c0d05121550381485082f01d69130f640f0000d4002820903070405580b0200819640c81d00b080c0d080845070000040071991404604d1360810180e0406 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 106111501 1250 106110251 106110259
    0x501050105120411011b03020c011e0c021003090206130806060409050d1202040803040816060905090f0a06030f0602120601020111090d080c07061806020615060d060905070f0e 77
    0x800c003000c042d07081058580142d0f2014041030314850010040b00c4070800703012211002c40d0039554040c20181c0000d03070601e11000070b032170300c0101d5900a0484c03400703801c2c00ca41010100d1401d80d1500014500710749415034450071424001038441158011a900303400c040740000d0740c2c020f5880240442c140400c22154001ea0849040c4500c00541d91160b0b01c0c0c40829110005002280700c9200d8038031070b160181d4000d0320a4104894031240d0380e000031a0f403005c1581e407424440081e80d0300400c2281c4907409050682c1e002424a220544451030400c140040040800384030070303510080800003500c8110740303c1505000d060050303228070024142030341101029100c2419a031400e030750030f28804c80030002c0d2034012208641000c0c4080003410800e0991248032502c1c1014081e5000100e0b80903042030018285200038030000c240280c40d10816070796a2300503919400551001d1000001030700d40000100281414a400810403030780c0c0740c9021041c1d40c070548010007ca40710351550007100754060740c00112001c08503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 106112751 1250 106111501 106111507
    0x30e0d0807020d031403150a1a0f070305040503060408071a01060905040908071a1b040b041502100609050603010e030316030203101d0f07021f0b040603061b030501050105 75
    0xa40c6045081c81805002030140c0241030014042c54000c9800128040602e844641d80b4130340780400b20403000c0c00c1600c06108079a66040441c2d101e24000d401d0158900e000d00143c540640d00760035410a4021020071020003004120125540c0c4084c00f2503806140705042180d1118220f14001ea403011a08800c0e4140c5000c2c0b2004010441d407108000040700c0050700c0020b40d481180c20142070300e1003101c002800c5400101501d1110000d501368036442800c01c0c4060704550140007070140b14a110ba0320402c0207054080c0024459800c1e4600110420146401154110380d04905400d054039840d50105584603a50000c004583c102802550340100014000d91702e14034096140400c0b11001541d50402c1540c0070001510946048820001030a1400310000401e058403004480d007143c1150391800c40600f500118007894000109049030b240c040d01030050500103048640000d00c02282c40e01c0e8040d49540c0c0000c0410418824025004004119400b080741041c80180940d601a03000a04000d420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 106114001 1250 106112751 106112753
    0x10c020601171b01050d020c01051617070e010e012601050f0402040308070f0c0e130507050405010e0f19020a0e03071e03060207020102030f030703150806130605061c050703030e0d 79
    0x201c0c034010541000b420611b40f1400076820b00d20081c041c90070340078802c1d860142400785400300804c401d001c0311650f680301c07140c40020b941406103c4c08262407800200707241d0307420031a0940c018500b541c140c19045c50503503400451110340c60080d034210900a01d403030034800d00520090404510440e00203406481c10740c6010b285d85d03268a510710642c8405066210b9038110041002540b0352440001c0c01010890261820701c400010415103131004110b41ea44914000081c2504060080504886840b412014140e50701d42411150b880700800c100300c0140603c900c4400d00526102618070303281c00d5034419200701d2411042c5450070784150042c5814414070b4046c80340c200c090800840c203995001c2000340c5c4440f624030050b031860298485100b15410080200949590301d40e04c0303500d01c0180e049000044603500c1d0398036a10b81a040d14800c1070b440782040040c010991a400c55038001002030890b80407060452940b481041140c0070031a840e0b042000100145a032000c1107481d018422644103160380c440d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 106115107 1106 106114001 106114033
    0x702060304240b060403060c1206140102070906080309010f030204090603080304020414010602060718030206121b04080325060e0c1302030c0306041508010c02060117 73
    0x32076074200e851007116020f481180790001d02031902e01802d40d10b95a018001503100c4006110080c01224a104098450500101013004400398000406000207003029440c2c2d10440c550b50506d2028040c0d0308020046032001c100034240703040c0c0c1c03803c010b800342d000e8012070303200e0a0201e00e8901c00005210440c00154070551080b038081103080725400d059851210280a808010307840500000c4496025208480040e203856590121080e52035000031051f6001104e07250b00049014280300300d650380c085440a01443c0300303a14030b007030134100555203640703008220150303501100304200901d0703e002c403480c24203800d604034200b8800e01055120b126a1500081c071010f0044c514500d00d0219004d49200b605d01881c10040c0407450341d1070390020000541845040e0000c0c1e4008180009000e41c0244a100c40c000c2140d005800c0c00d61418001d00c40000c80010001ca60350018164a41c0e00e1346 = true := by decide +kernel

theorem cover : BRFrame.Cov 105935251 106115107 := by
  have h0 := BRFrame.cov_init 105935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 105935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 105935251 ≤ n) (h2 : n < 106115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
