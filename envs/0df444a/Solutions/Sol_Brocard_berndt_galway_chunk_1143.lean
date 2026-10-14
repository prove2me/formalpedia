-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1143
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:25:55.437196+00:00
-- url     : https://prove2.me/submissions/17eecb17-7643-48ee-9ff1-9c5db409fa7a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 205395683 ≤ n < 205575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 205396933 1250 205395683 205395689
    0x102030c04090221070e0a0605190513030f0c1e050f0d03030b100908071e0302010f020c0a0b0d050a09030504060c110d06021c060e0a0c050c0d0f0f0216 67
    0x2009a51a41c040d603000e043d02000b20340400b4120441303014021001d0304007481c0b010740d003c01e507144c3e00141d030f40e000261000d02034007481d0382c2ca8415059401342490f100b24024182ca00f4500000e00c02c540c0c4984560f04085040c102c11140a00307008800c0c810849121500006403103260042520141004082060340d001030103c28099803414a0070750405000740c010721030800b80501207a50301603000a009004520130f00c1010200e008402000c98240940c2c43c4441c24240010040c21003039103554011130300d080b0308403106411800b4a032510074142d034031441d0080040488185180c2c82c0c0000044e408102c420203024014503901c1c0850742d03000250407200746d404a440600344a074207801c05003044070302032000b8172074154012030000c14081008031917405030001c0c4040e0150007000c0b8070703018400f10444516000c1ea4103007140000000d031001c1803075000341c04008451320b003c906220100b19407502d840c0b2111710900229407410354082c01c1c2940800b040109032414802010345642c600f103e2902848580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 205398183 1250 205396933 205396949
    0x203090d082706070314040203031617070303020403020405060402160b090705040f06031103070f030602160203031204170f070f02010309081207022b080709050a03080d0e0102030c04 80
    0x540050748040020000d0a40c00881003440b00700220400703040c0d601c43c0400c48413280881e282070804000100c421407100d1140e80d0290041d4540052815124004030b120700c0c1c22560300c510403100c40702080003100a0541c2d94480c0d10003680325800e510401c41507680090000303004500c1841101e802c80680007480b0919500700b000d2406c6d9450780d003100d505004003500f10b160042d050403440094600e00750b21002c1200c2c01340c004454ac1c00340400815482d8401e03407140094544140f03406001041c010b80c010500018581051005001c441c2e01190a540003644071444803211a0b0822081c0982108410452500412103d181007074a0301d0780c2e16a4041d401c400340c1400840d4540d0411a4006da000d9900d09410620164481a04c0c0414084400e0100c0360240140030711039807519038100c7c940d841c1c0ca0f850080e8030040e0494880250445400358000c20460800c00101800541c03502c90703002c0b000166020781c0382e0550340c03c015020402514455128020503078410401c00000110002c180c9098503a28 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 205399433 1250 205398183 205398197
    0x503070203031b04050315063609150403050d050907060507030c0813080304031e080d150f060306060e03031323040f06090f05040222110a0306050a08010203090d 71
    0x40708201814082e0360803170b50301841245940600c4103000611140300780340c11115801c1c00305000c1d600c0c1c010788010803028031070707190440144485004e10003031941e41700780c010080720b9621046c442020405841070f901a0082003002035a007081172014050258003070311740401050b10503d0494000d1062140c144054100152180007104002032002140e60124400d9407150f1001e4486040369165401448200d4003012400000b846228826900b0414150040200f9003040c401d803169501030b003108600c02c50071002c000380200d001420700041d1005480302741e03070025540741800c401030101c2c072910500d01e01c82c0d441482046003202103001d013141564104014450041219540300240401d840d481e070b40d0180c01d00d03028110600c0194002011114809030500010f40440c083ca002c0f6801500c000e50403100c05000c400e4501c2070007540244140580d240000c81d81143c2441500c181c000714840030000351079980410a80c548405241c000c2c0402c074008518500f080c2d440b030780d901c500702c4415506006803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 205400683 1250 205399433 205399471
    0x11010f020304051203121008100603030e1201180501020c0106080304050a09020a090815060a050d0f030305060303070516030209180303010519090c02150c07020303040308030406060503190c06050307020303 90
    0x1c240140c1e20b2500c200903031b81181b410844030000c154242c0e8000c0302c3e40743c803494291041000c02400f5082c12690141c41d000004c0e00900140896080000c2c2020341640d240c4040c00c4071000c540d140b840406010b580010b88815542d1003c6080d90066030080180c0d500a00050015032f661505103001c80f1204d00700169941c500345401d03222845103900c1f44d0f1003030003581090856580401070080c82508101c50b0142d0301d03505c0c2d10401c14404003a200107456040f00070742140c00603020364025074001070010100ca09003038481d80c40c1442c15545e4011002403160f400020011420b014841d150032041c0c1200011003103a0100103e681c07404140f19041c41418a00840c0e0b030800451403125000d0a0111030602c0300e1090814041c1d690f600503032104414030404c0002604041580341610041759008002d107140c10303d591500003490b040500190341c03060380c4a800080c1550704001d00d81031091128003c07484540d440c206105500d04c030f81d100d036041c08420420090440d0740442100d6100c0d20455140c241400303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 205401933 1250 205400683 205400719
    0xc0405040c0b030403020a0303201603030b21100b0d1712180d0302190503040602040504020304150506010203070f080a1707030b0f030309010c140a0f03030911010f02030405 76
    0x945501c40780d901d0000100740428103602281341110f06019443c00d1000948044500f43c11500821105c14809000c0c4514500070070329201cbc044942d8001e02d404070340c25034072500003440d40b851b8140c10910480e488440c401400030034000341d40480305800c2c0c01c0180100781008140320b55803003040208941380822002000c1a100c0c0161051802c24045411261a00701c1d88500c9400d49200821f21510174400c0602c501c51180c021a0240741b0480a01c941043c11410f040e1425000580700300d40840e001d21000ca044c0c1c80e03520103944180c0c01031038100612154015a4030458070f004d000300d4110740040000c5404648030121914450794045600c0c0d82c0d400211108540c00ca44140d109000e0240040074024160ba00d41c000c1c442ca440c040350315204140c1e01901b0541e8038400d51006601140d40c00640d88080341c00102ea0070820f2100c0c00039541c886c11940c1d20b0f6910b44c104607100703d01017a51911000700f8040c90b45514408480c0a00306402c02c0741107804060f5581c0198400c5078492040198031a00c500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 205403183 1250 205401933 205401953
    0x6080a0603231c0c0b16210207061515080105030316051e0d020d1115040512070b010303030501050415031e2108091612080f120a0606020106080c040504 67
    0x195803610f0031607000120980081008403020301c2510b003181c0c0c42000c25003100516200a050a0060721b03600015103408254060180040c1e11648885900b80201c2c40410a54025000c4002403902c03480106410505041410002c4000000400c0a03060060203180c9001045070000345204242e1454401c0303601d041d901d001d203909040b40943c16240e80241107041c0020700c0844900b50380d0251045280000c3c8202c0e03101403400400c450390b6015007248030840340b542001d5600b0900520640303802450003881c080c00c07648981811169002000c2c010406d150b072520440740500b40c00c4074148000c036000c440e00701029165010240c5030b100c08041a01d40d055203694048400da91048000107003c017400c0300704020040c401e500c01d010440e98000035200c95008502101600d8201003c4589203007460605018420038200440e440c01d01013004002501009000d040705203c4002d0b16180d51130600b481d14141c0e4519405a02075a0511206025440000c6103105800c05c01f40c800080d61b945505040b0504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 205404433 1250 205403183 205403203
    0x1021060906090b0106020706030c0c02120309030d0e04050606040602210d0c0809010b0d02030a03050a140c0d02100e0a0201030b3601060c020d02091f0b0406080a060323 74
    0xd9150240b40010070041000e441d0403104540c0a403100d1695800060f030984105c2500c0000040d5008800d900501c1c02c0380c4040000088034044034100031a080100e49000a900d0108010030042e80c0105002d1070b060144c0c0c3e6105500f81c5d152401c082c03a08402a55030404d00414020b20341d20405081240b0345244240c50078841d1240f41404541c0c851040501054003e5401ca200c07542044885030030350a000d11350640f6141e01a000b0700c059403054070110fa40748c01c031851020030170900341700f1040f0034040080500710f144c02110181c07069001541010385000c3c055090849003a042c04030307408d5060b03400300c0e1645000d6020700380428500c00d100000741c07201c0c1030008051900701700190b0520f000034165501f014001a9003400034016625424240c070600d0b46500025488020031100f00014140134101941102990703045202002007002201881242c41e01f018040d000301040030450650300c511025049403046408002890031500c0b41c88001807e40c100720056090201d125a10f90f01c1007140d4024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 205405683 1250 205404433 205404443
    0x1215030f0d09030501050a110403031103090405161101060e0c090102010b03030304050d14030907061d030109030e01030f05090703060b1c110f1c030305070201201210210609 76
    0x7485240d040141c51021a030000361020741ca0680060107180c0d0912540e54444180350159003480e00c1d55808681400c0d01c0c000044143c0024810701c2c08540302d60003400d006a0300259a0b42050b0110b10004142d94020105030006a040c900100460501e200310b140c0c10114541c1410750302c04008005030702600040f010a5018800002040180714012801c1001c1e0009a515a003110581c40c0301d4948501095850801c140c00510007002418081d5202c000050001548620305103100b400003403c40d8040001900480c0211000b400c45603230511410000d1142901d080050b8104440038954a60980c04000c20442d907a000d40101a980d040a40d01480380303564211410400a1514070f5007e0020000e01d8010040c03503024051920344050305c1ca90b400c840500c601401003090b1000c030003034607000e090401595a101400100e11200212045c7d01091441c4840c0d40c032103090403080208040200304070f2580448a0061111a81507200d102880107400c812000600d050700703007030009040c40400106 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 205406933 1250 205405683 205405693
    0x80604050102030f071827021603111b1020011b050304410a1104060b0f030705091e0103060509130602070c03080a021506061215030f 59
    0x4010303054000314880c071298110045242c032129419104410908090707102007034890300600c101d56070400242c03d9081d0380c0c010342542000403000403080380c1c40001c8030407401c0c802019080500d038114510f03620704404800109082078a001b00c16080c2e040f2049020b00c02c442001001c1c420501c5099804031158041500890806a180030140200701240700b40480e01c010450010a007800389046c0c901c2942c025402c0c4030841620107006805042240c928020710703607810700184941c140d03042c0f040346001e0303084010052048241040c40c0d0700246640e0651089041c52401d119400c003c2d0203440074030041c09001da0b02d1741c80c0d6442c141d400703000324880c4035008071000040e100200a614100035103000c0c2030702e04110803030321101400310006084034015890b41c0d07810b02400020344154002c1c07604902504203040d010340c0325910140f169201c0207601c00182d0081610401d68101c0001403034000b20b08488862416424a00d00110b07914001c1410645a541544000e1941c400740412a22040c1d030400b503032 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 205408183 1250 205406933 205406941
    0x18110c0d0806040b030d11060c0a1d0111070f0e01050907020c060c10050411040c1107050613050a030b010509010f080a021017010306061e0b0f09010918020d110702130c02070806 78
    0x1d00c7d150300e95410b0703e810300ca0034010a00c0700701c1c8030049880c001c87d10b650300010400084848101c080400c014981000742442085420240030301c40b01000d0418000b601d01a58a0414004465101a000343c1d21800713032402405902500025180a18901603651542b40e2105203059800c0001c00080c00c1d400500b0f1200b00800c100082c5c48002d407005044500f0058041c0c1800210388001b2110b0500009034403d41c802d004601e003032000b810804a203031824a4140d600c80001c501c00da080c41e40300300e82480c0500018007440c581603141034090040310410030b2880341b42c41101c66441c060b05a02900480040201007003540c806c600741d240900c070540c03440d5240e50f942d00d403000040a051080c13030010b01404401c460010051400d8008680164039981e06000940c5181011f5a2140d041e841c14003285032800070320844040c03050249076107d03c400689a0b00351440c500c055a90483c071045580c9010040751005a5980b0041c19246810380d00024078030001400c00d0b07143c0b20107500020f81c9840b0303001c00c00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 205409433 1250 205408183 205408187
    0x93804151e1701090308041407030816170f0904092d021002010606080f0702010e0a031101140c070b04060e1203010510080c0403110103060b0418110c0d0806040b030d 73
    0x4508440d4880b0181a40d03040e110380090072580340e0000100080d0301b00010501140007401d47e07202ca1403503042a03030005643c071b64661046070300c841c030003130000900004100e05003ea00b00c04400800b071000011494541900458200381c450500d4540c8169941c600c4042400501c05048908141e41c1041000c00c0d550002c11624103500080220700c0703147c206075000c05103481070103120103c58070ba0301d0f24079042e01c8429002d401148010b2100d02159a180c1d0a029051401c21141c0e5580b4000e44400400a5041d030303034a400c0da00c00500d0503803624116400c1c802c80c00d080500b02e501c00b58026040c1c1001d9165841e08102a1084029400b400d1240100910703c00c81100021812100c0c215000582c004070000c043d2800182160004d100100521041002c2245040581605041454002005503e4006416443d000340d081100c4801050303440d240c0a5401d4410302112491040c90203040c800c1c41401c6a64458014207807a081221aa01160b070540b070b980c11035444020000d040c0d0354480003103a40 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 205410683 1250 205409433 205409489
    0x60609091b05060a0e09060402090907120f0c0e060717041403160b1207170c0703020c01081603020d060531050411090414060109380415 60
    0x7125208900c0c5040040d1a1410000715065280345849048072811010b0401810b024005c00d001c1d001078081240c1c0c20290b865058151044445440c1d0311480003101c1c0c1b0b11004c41e14504056000d0614054601900350b41005551011040460341c0765501c03c5103103049001250041340300c1c80e0116000c1004140101d6224171000d800206808407081c1072065010801c0b1030066105500c4010720400c07450302006642c143e099031204107030400d042d54017982410016415812035642628400c0400c40008140c0d0500486500039024a825019130805002c00d4900c025050314050034550700040040e9038142c41e0300f2400c01084020039000c2c026022943d01c1490460380015484403882010407074141c0300307651086138091504041c1410703100c0d8400c800e01048101c050019162404880855011034008000903400381445040c0032a49118401ca900c100390390315240c18441140c0c0742116407299405000c0800c400310304890105148230414403402e070201c0290003000740101c48060480c829060444 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 205411933 1250 205410683 205410713
    0x102090103140f0a0902060f040603050a0e011a04050a06180605190e060609210a1b030201080c030a090210050306010f141c0216030e0a050307030c0b0706060909 71
    0x3002c1c4031603503850031941104001112400082c80d22600860240a01507202e81c15030f501c05400d5916001a10149440541059011400194540d010032060380ca0500401200101c100000d001e1501c0c80e400a070980c00301100b800b0b00a03a0303104001442c0e014941c01c41c60007013480070703040f070442000201800060a440d00403d0b014601c10004c0280aa812032805d9084500c00500803203551550000c00200e64400c08149034004005000607850008420010180c5070070080180046002403811030005201d150f110b80c12409a51410000741c1d811021907a8040c821a140c02d0b507c0e43c0c1c004600004042d2100f01940007a103000080008503000802180128001d80703410704040d4129200316001103080c100307501c4440c4103008100a0001e542035807212000603a03c0542840f120038203400f51015207800c00c3c0c00040c02c240c0c1c140400d0510941600203050140c001c0e084140c11515119054481c1d480b41e0390b22058001003013818001e2a034891001340000e08824408010b83d07060000c42100c0b00c3d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 205413183 1250 205411933 205411937
    0xd08060f04141e01060203030c0d02070b01061805030304120201080a0908070b0907052b030215090304030b1609030b07090803040e06011209020109050d03050910110d2c130c0201020901 81
    0x70640c2c01c40f01803401481812243e880d0300071132456943c00d80c1031301541c00001c10020400d400303000d036500254445003000d002c2d0a0a071b80d081010503100b1924800004c25a010900a0300200024041014030074500944a5028203080342c0c0760300c0d2620214010110074102500101011a26104215000c03a4550040c003080040b10829074840b0100050300703080c000b000022a9100d520814000900c000e01d601d004d0007030064864544d041c80d80d0f80001d000c11155004190000036050040004802c0010740040140124a481b40d58002c40940701c150340e800050041049400002c0809200e0384009000e0706030081030ba6103030b950303552a240280704140d50041c007103801040b0100611800784200c02165405031f4035036140c01c1c5003c0a0204000320b110064082040c10023001040740c807105000700c590511a6240c01001410310621800c01405041d56401c0060001807140700140300e246a0021090320807800c60315606a200140502c12420009803c1c9030800540811058065014000c002d4007a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 205414433 1250 205413183 205413211
    0xa05061e090105010e040b09031210050a06080f0a0b0a17060703050114100f200a060606051305061606090516060302070c1a040b19140306030d08060f0414 68
    0x1d5140e0b00380c0c1c900340100c8000b02401c13000180442d040c0c58030035810a0408013981d18200034100c107000114401c44501d5600354000e03800b004035003070015006005100c1c41c80e004401d4101405d6869001c4000b804605100d500d45084818079612040000010130b42c20326419202c2c0722081126884400c1110102c022a14240c00082c000c026401c014101600040c04d04442c00c00000e001c0d14200408030b191410054054440c00360811108540101062034000814125100e0702d09072042c3c0e01c1a4003e41c08100c0f00307101000c941c18030442c1c1001542c43c111106921041501c00c2c00c401c00244d2600584068140501d0800340b00303010981c0e134007064064600ca03420030b403201b80a5040c0d204241b0010310300f0810b00800c02c100800180010711180c08000500c2ca02036035880c000070a80c100c500e4400150041e40c98002c3d01c035822400500031014031464203030540c50000700098450150317910000074020000c0c00158140d8071608071440200c030090082211201c0384082d5126003004640982800c058 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 205415683 1250 205414433 205414441
    0x90905060606090f0907030b06040801141006140306010e040609050402040e1f1503050d050d05061005030703020a17240d020d0f080d0f0c031a061b0a05061e 69
    0x1080440701400e00c0944031000c07850b4804c0501000840003001d4004140e40c410072110b65554030700c000d2009102402c008104c49003550340c450a42d010161441c504544000c0080044a4000301700300a400e48410411b030b1607581d2400141c980341c494070b4905502c180b800b0300108141c5010350040b8051802070782c080002158142616a564103e844000082880010090114800754124030340d421003a43c3c8504039290780f551060b10f0100903d02e04000b055020516a440340014420950f010b001114000e100c40710800d80500340348000390010b0b0815400003418007006009800c1080940551590381e0210300e480c2d41c1000074249400001d807040070056906082500d03100142c20342143d0001c0c002d80000b002555240c2510443c00300440d00a082480444040c0b4010303c41c41c13100d440c1703585d000311366511106002070440d1040e84811f44044046140116281c4038102640c91464100c108110203441e10444070b0f00c1c01c0f4120500400e5485400204041d0310b001c0802e2400d000c0191100050b00c0d15 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 205416933 1250 205415683 205415689
    0x60816090f110f0a02010e06090304060807050306060f16170a1209050705220c170901051e09070b070602040e0f0108030324030a0f0309090c05160c0b03010909050606 73
    0x40e1011450785240042c400f0100d203c14107002020041460300000076006050108182007400448103402250004181045440d0b080072400d68481440c0c40c0c050701c2c41c0340c41c5001031038500900001c1d4807003050205550310507104210304010a1904458543c840110b140300c00c503016804030031050000fa0009960203000b803140e0240c2000c0581c0700c400f07001c18604180c10b02c00ba0306000611a0b00304103290f1402e035101c04003841400b2001405035156889039030b118502c1c40691102903c02c10940e8909000c0107401c41180d00400513100c8078842240d060b458001c400fa1a00c0e030590003204a98400003100410056598010000c0751070001d22200ca0313503904030403482142001d00c203c071003035082040003585180c1c10351000c0714180c402c402020303c1c00c05414040b84c9045400501100c01110040b4a03a00349074001038640010001e420381444030030346002d0020300a0051801e80c0721031040301d4004100700001d20f03903000003400382060b02035180d695500d503600c00b0340700b5104152001d00415000c5402e0341 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 205418183 1250 205416933 205416941
    0x9080c010e0c030c031216150501060221090906010203090a081b040606020a030e0a0b0301090b040f18030509042711030106031707021f111606080613060816090f 71
    0x30018090030400303d005007105441e607c40c010810803580c12580b082c00007940072038401d1152369030b148005003641c10300f80b010340380503481b1b00c5d031084599040600404988651003181e09289090f540c060182e22403500503032442c040c020005500200b81074003c6070070040001d1545524124143d4107280410034800e21013240e000340110401a0401606440440d001340050020201c014201c0b0015507138072000b100e9035030400c1e0010719411341c403840014154a03040c0070799031058040600403c4410640341002403400c2180c0e000405104010903411030703a541c2c65000301e1a0446038110401108a03001000e000c0c19111441217445a645200c105000d0505220750400d8a0303109070035120030800302c03150b850701d500403143c12684840c0c0c42042d00d00c02503070a4103034144144d540e1512014199010300141c103004407201da880d0292181d902c100600d560000c00960040c0c01580c0048040c420342e2110005019582c100c100c03d88594540100546c1c400c101c4603007100c030800030821801c1c1d00014000191 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 205419433 1250 205418183 205418203
    0x501050c0309030403140a150b010f030e0318040e060901150b0406230903070f1d0606030c0f0408070308040f090e060411030316080304060b0d03020303040303090609080c010e0c03 79
    0x2e64428001800040e0202e0181c40c001d00e03c01c0101ca4042c4042d03602e0f004601d00c405075410b041c0e0786070b0308807000e59600001c00d881c60040d6410300340802d851520f0210340d01d003e4110881c042003400c42d000c0103a030710b455021808440c5500169913003490131078041d80c003030070440310340c688108490782000541c0c4449105840581d400d070765a080c0c202000c60a0500d4000b01420800078616040021001c0d40d42c08001070001850640d00302d0161910303181088200074020020001400b46800400c441c5984400450fa404a0131840d40c9072200f040a0004082c2d0096800070240c51055003808400e00c6100009002224407400104a41e651104440f800f0354007985d06141060b03000601103800107058541c0483c0501001d403c80e81840001d000e030000c00070a629095401410010902091003040d00440c540c00d6001d50741c600304548107640003076680c8401440942055a0740d0360107c100b101e41d421001c65250801078044c0c0300e8800070704050080030841100c007114401c840704103226040220745001c017 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 205420683 1250 205419433 205419451
    0x3003040b04110d0b07082203020c01030c0504030302100504231f06150c06020d06091b020d0f030e0705040e010c02010b0f15070c091112071b112b0501050c03 69
    0x100385c07504402641c10b25009400780003203440b191200d0784561100a00d0802941c0030b40c0c010240c4d042e95000150803612404160780070040204014000b003600003030050709003040484006030030354030390a100f14242c1055040340480120540c4503064000700180e80741c1e05002180060b410f220403545d0300421100c00b0710802500c04008012080e042d40141c16516400340290000751425902c210400100c1c0c0f141d0300000740301030382c038007070300c0300300f503400c41030b040c80e141c040d00090cc125401306d407014245030340e0491500105500c074202d00116007414000c6400800000c1c0092010344204a03490380603100450020700198640b4070280501c3c5440b1100d40380341c42c40500398060500e141001d40307100340d201e4032007a5a944800c020000d606151841840780415038540056280e6080b50910340c0201d074003408000030401c00c8bc03a440300000303800e0300c2007010562028501200c08000310105095241003c8803a1740300029444041d82c3e071068006074a41d00b40724000801096442c40030301d400c523000c01e03114005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 205421933 1250 205420683 205420703
    0x190e0708042f1c05100c050306150d02030420030703080406030b06070c030b01180501050108011203110d03230c0318070b040b21093003040b04110d 65
    0x4180c0b01510040781c100031074080300360742203521800802d8044110000e5401c69003407402001041c0001448117440180c035200b020b01c440400e42c070b0002c081d40000341031103205404d0004503a800c0c182843c00c4800410345aa002d640b285417508007076007680141c422021700e444c541c8000c0d030b2442c0340100b5600f003660791007140341d0b0600b03081500460003821443e4006422200400004c0701007003500088400a510039001f00d41e0a6051100000d5401720380300d1103844450402005001581c1c1001003541501d044003003100e0404a181030032694042c2065888005016841d00400c0c51a07241e0070110a0084101d41c6041120300c00c0c00d10b2001a030115043c141c82c450510208074803071406032020701c0040c016400c4403011529420074580c1a03002c0c0d40a80404100010054032411070540507001007520071000d0380b203030300e8040c42c0c458440b5040717041516207614198990003c2e0119418034140280d0303800c0c4040c1c03649028508502e000310195020345114035001c940780c11910308a40341940d10303580001c00e20 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 205423183 1250 205421933 205421963
    0xa050f031c17011401020f03071a04061103071e0f02120c120307031a01111009150903020a0b0108030307051905160609020108010819080315190e070804 67
    0x76001c1c1c0c00003089420004500c006142d865880080c1502030800b03003080c580f440165200280c50140d02c407280a0064105101110200d08008030346060a681c0d64030f5a4030a40d100d00d0680000c110042204506010202c1401001341d031000c0d21406074404a00c00d8020328030f0f4800d05464418802c440100140c1c88281c56080c01044100940350f808441c20881d08c0040c41e000e0350404030b070000c40e080e0000a561303201c50b0301c440d2508500d8181e900b100f8200f8501c0a0f4021004c941c80740300d00c11550513040e8580310510108800c1544c1880c6640300008200600260b9103002501ca003989882036a6120740e800000c684e056000c0100e034012901a00c40c01c0c9480701c0308900c5040b665010683ca4107012051010055000c2000740d0740455501c14100060b00c5010b42c03002604004c81038022403150741c0408984400410014000003169070400100780d240e990792403d00d400d000c0a2818507400c010701548a20450b07004120391401d03200000e8000e000d5645042e03084424901c1141c0140000c00480400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 205424433 1250 205423183 205423213
    0x50f03031b183105040309091806050c1b0c0303031803040e0c0702040f0614210d030e061b0403020904320d0302070f0b0601050d05040c050a050f03 65
    0xa100d449025031a2602e00c0804a000948000c03050700c680d101401840820690307100d1842c0c50040014010504120382d081549000304449031300c0c001c1c200c1165558000e80d80300c5032610310303111460354008820300c0f162400c01103550603904841c2d07030410302c80e49046a05920020116a0104400c07010700114110340c0d4801c1c802403180f91441039181d950104001c041111410354014910079069038120640d00c1c409841884201c0b1101807c4454041c540001408a4103031f0508020360315000300c07007031540b08401c1c3c07841c0107481800200b02095481000307400750325940c054000035580640c0909031503d90b9500040106000f20b003040036208403804100a100500d010154541c02c03a01030310300d0b040020750070782c008002c1c400701003140041410448058413040e41e00b0868502e44807032514080d42000501c0d070301c2c101c00c405204001840581c00300c2c0003440b50392095080e15105000d40c6030071b211381d0400782030921096446028180c0542c0380014085000e0422104103c00264040c005000c1c0041200070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 205425683 1250 205424433 205424437
    0x50304080408070e0114010203032403011514030c0d0b06372405041202060705030d0204080c0901060f030b010318050f0106090b060301030308040312020304030c050f03031b 76
    0x100c9410805100100b214407040024030040c02c107018001c582941460b070303000749400211600034110340c010010003d28515801d4101c45c10040e0000d60135103424220f00003405000840500c4010700448140000c0a21019082c080c107148283d066a09024840301482221503ea040140060f2001c0d40410303141d043c81c2200c1315583d1500303641a10401141000c062548941e40c40700b03802000780080070b00c076904281c215801c0302c10b030030340356540c14810440700980580254400c00c0304070840e41e8005d60664840100703d50000e07a01c20140ca90341c07424222080d0084d00a07004103901740c42900109441c90402d00181030580300d4035102d0351101111000102d0190051818150400d0307115100c482003079403030030310746c0c2401442341e1702428000302110601400c49410741d02052080c3c0c01c1c424076221545503501100c0c1941d0b018a088104c940d15810280c804101c814404001c4a1002042006041c0e206040801040c46042602c0c20382c0301082d41d07659a40400d42e40307035094125284a50b04050303d100c2c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 205426933 1250 205425683 205425691
    0x20415121209030c03050a03020d020106080a11030a0b04031e020a080d0e120a05040303120203010311010c05010212040c051c02100c030e040507020304050a2405030c0d0e030a021009050d0503 84
    0x10700b003103800b900da40d560840c40a250303000311403aa00415085007059010711200c010f080140c8001c1080b00d10302015a031392090f0040001d40081d24040043c1c010b81c505125022215800a41c40e61140c1818a001001d03200d2001920450300402c150444919102054100d009c43c0c100e01c1103805c041c2c460000e00000d080541ca10703c0c06114071511b141d014000d460180c40022180d84a11761214550300300130b0002c44282034100010342c810001440080c211210440502c2000e103001c910603281460143d0091181304000d6500315681400c210402c601c03c41141c0650380151004d03844030f040145070142542c20b200e0000c1d48000010f140c0d0315102d1207030034600342a6020b85881c000c450414800309040304c90503101100140c00005050240b030824103404c0c030040c019843d01e0400c031260321580303000601e0840114802c004000001c0307880d610151047e9114110142d800b0046c04014079402a642d41c810920070f0050f0203120a5070652012620400b01b049401c90301400344182c80c46401c50b544d40c4001c5c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 205428183 1250 205426933 205426937
    0x60613090204090303021902061e0403050c0a0f03030e0a03140c011d0703020f0d05060703051005041506080c04050d12050f041706010504020a0512090106120f0204151212 75
    0x40c02110159640e806020a0300b40681c400580d0349464241c2c81d1212644010401e0940d413000c414041741c2640c01140c80152685030030080c070a81c65a03d400c440521821040a001d8460a071510052100001d80003c0d0740c0d202c0d840801500c06c0308200d50380ca401c075080c0041d011812280048411b01e03902c200070800c40c0003440c00022040c40440641a403240350702003102440c0d1000c1c45c00d004600340701c24185241542102d02d058020600c2d80d0b40b03561101c005080300109501c1c1e60114210302c14400c1c45c1005044000d00030700c4081c02c0d07524500b03080400c0c4d10ce008002040d802c01300b6000010741040398140d5401401c0c000c0500c0807a203d09180c01401c800c44020400100103000c506107281c0d010700050002d045803815400b8080d24030702d00d004410703081248140e2040008409568101d030442c0d00141d0100010384d816501e2b030b0a07540c010052540401002e5042041342400c20141b0482d01002600c21a81081240c2c0c54000000c0b4070f0805003c2e8503507001c4102d01e02004161880786804c0c00110b14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 205429433 1250 205428183 205428191
    0x60109050c0a030b01030e0a030306080d0206040807060b010c12020a05160f120c050a0f060207151e0903050102031018090206071518030e03011b0905060a050f2a03030603060613 78
    0x17580846140c5001d112342500002d81c2c1d01c3c014001080d0a0000c441020b189100804d4603082c191078172049845070a0300101019600d0070241c0140c1d0144260304007458000d030f81c40c040c03407820b10006501c0d00701030070040350140034032011001a500d2100c85c107416610302e54110203a130b6007404004968210840c0058501012901000681d95a03105501d0003401a210013042d1041c54668040e1903c42d0980100e4502602032a041604651042000002d08107181340e0307958101d00d42d0029035180708240c1000e030465000004205504100f13240c0300080b1280401d121b030182c1c80e015010821115601002036100c0301c1000040d01183d0311040c01c1d4004511400300003082ca4a4624035254882103020031004117050381d080c0c040c1c0f40f40c01e121b803407403201e8184c40700c2c0c00806c0c00840040054002d0b001d03c0384542c00100d00001c5040c41501611600103442d1800c44d03580e540da11080e014620b041c0c0c5044070011124040900004020094900490000e402030031a511841c04001050280c0c030703207031285140e507 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 205430683 1250 205429433 205429451
    0x230f010c02030a080109020f071e05010911010f11030304060203071b03030b102f010b060412020a0f030302031804022803060b0c07030206070203210903060109050c0a030b0103 77
    0xc0c030a055040103160000c5554211004000d45161016130040580c14814401120408001d00031540b00561112811b0b44a008541c0b03c1c078101c065009020300998030f031031410002c200d403102c0e148100180907218910681c103812002c6541c00140c8245100513001803000c1000200543c01641d0082c049040c4840308116403c61240944412481900000e0711503524210394240680b00d050b8004851801040d084070101000540c0c0f5400c1c4145c400d01140c0c21505414a1803e600c03000001200a1107595601d0340c0d0520016114008401a407040341e11040008821400701640c6003141d034180c000d5400c105c1c00c00c0119005c00c4031190295000383c0c003003054041020190324024036140d140800c01c181d602c50303440700a00729135041d0007440086608100e85914080001452004c907541140c190340d8880e99840800d041c0030030012140b0000e03035608408071009030040007400c0c144d41c044e8100c560507a6542e42000035103005a9121821090401c244040300b07100703800100d403c40042c100401c041f52 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 205431933 1250 205430683 205430713
    0x40e0a0b060a05150a18030201052b02040e150301090209041130010e011a270108030d23160c20130203010f05060c011103010b0319060323 61
    0x10308024065113040001003082540d900604100251541105aa03501a0540e070003e0710500c070705507018040ba00220260801c118540c1c2e60305d015001d1003c4c00707540310b0b0b5641d507141a101c00300390341c002841e50300034841702e901e400c0520406c40c0040d00204074540e151100c0d2101040100c822581640150003541070040c0e2071a01f640c001203644170114204031811a510340182114800d2584220710f90401d5440228041031008000c2160412155011244009100c22144804035243c0078000c1200d280005881c0c80080042c011603142d40300c081c0031004400384003200c850074038000c0c0c0010841c5203010501121000602000f80c103030a0505800319199500c5054a8420a014102099804031801c041c2d0342442035840304000c451200950555050400503580110f80e401118065500800d1882c0d03000b80c03d4011103401002d01860541e80d586882c0c14560b50750080b41c9403074000590f4081ca003d40d41c145c1c0300703405c01c4130341103000981d082030f0b00d1810300d209040c070f4414040d2501c07035003140180c409 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 205433183 1250 205431933 205431949
    0x1202070c080606030c060406140702032b11060114121501060e0108010b03060d02030a06050c0706050c07050c0405130c080c030609060906040305130e0709090b040e0a0b060a05 77
    0x180140c8800900915205040e4604880104180c1c003a8011001e000e03a20b480701c0302510107a44690030080710004a034220324180c1d0151050113980751151030304420403604c0c0c0440c2d8031122683c40c900e82c52043d50420003659020401c9240388210351240307004105400c0c0d00c0180c22007900000b40302d4448510384c1800c0a03c0e0082003200c1401c41c480c14401000300715002602900062001e00f4889a07a625190000c07016000092980c1c1c01600f01c402c1d00021581d003442000151365210104005905100c1d1807510107400403041203400500c2d202c0451075a048540035512007607400402440c8509a803c240310207000003420740321146864801042c0001c010990b850050507144008101682c00703a030416140850150458902d60081414450700303c0c80400d107282e0041e0103040055890580c103201c8540d0440e150700c00103940398a68244002503034403810280c101d40351000c040c0607800d03005041004a90107104510003950000200900083d203e43c8100e41c01400202029003503599500420624 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 205434433 1250 205433183 205433197
    0x60f0c0b09070e3103050c030f0306100c110d0212120d0507031b0c050321060f042c0c061204060e01060323070819020924060a1202 58
    0xe030040402440304802d881805540034064401c01010051040c44c8043e2110504903001346401c0c21065003070a05020300c0460381158070078012240d8540081c02414201d170800e0b00c03010702c00d603903c01d800400140714100400d07841c0d81202580f580341440e2010010356080100040b6041106100f48034400c4030b046c04440b0030200c4a161584c1d4070340d05448144111000281000241460301c0e070142c0d00e42d503450a00c00d45494860030040001e21450600d076241d40502815100500d04101c01e10790b800c5c031b04012144c0200010741c0e0710000ea60b802c404101c2514151400c1c000200c090450a41c82500e0074640f14084840c0c01e000da480c6000c3e440f0200b62070707612021522411140d08030a00c8200400d5115410207130040304000c1203668110303039810309401d1407410795441c0040b841551540e11030050140700000e12000c4112011210071319040e02101000510a91242c84030b0000100564589008035105680000b900301d074817270208040000b150020800581081102c080e541080d65492001b000c41d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 205435683 1250 205434433 205434451
    0xf0e0d030b040609140f070c0b04030e030f010c1d040b1309021f050409020307030b311b050a0210050c0702151602060306310c08090304060f0c0b 64
    0x1039144504244425030f0500d81c845a5028a000f11340700c0f800741c4007152181c00000b86400204940c40e81c003000c4076010000000139082c0140e10080c40209038100b042c001c501c00d000d4003584d80440642d40e1041c01c8406986124000c00c840c040c030441843e8407848910501c02005000280241d00080440c1d441a96000f4905545688404030400d5145c41d8424050815449881c00c203008802400103200e40918862540d0050300072010440050298001c0b80e0f8952000d40058003140c0b04a9003d803900410700242c400d5003265540e820700203a414001e1041104001d83c0da4141c600f0074100444082d4002100c1200b14068800200002c0509000f0280901000b06000362994414010001c01c4480308400302c0c003000c0704004001202550f081040c52094040f0780b000c0e113a035207440c0415051a41e0130180c2c80012003c0850700a00459a07801100605030000100b01c0950071000580307807104183c6038a00e0550081c04204640351040c1032100c1400b40300e1800080140981d40d0b000f08264094503a426 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 205436933 1250 205435683 205435691
    0xc110a080408010617070e1b070b01061202040e130f0c0e0601020d050301030f1410060e090f0c0d0b040804050d21031e0518030a090314060105060301090f0e0d03 71
    0x702c100034041d41c07015002c25046010540c000001e40d0750f940019104501c0000b84100018110200c100888507500d0303445141c241e903c0c101c0345890750700c2441c24050100892603814840701803c0071442039070142c810001030300426071a4802509003041c24080304840030b10311010410001050035607484014080e83e05610210304080002a0030031030000c1e00141041018801080845c406607011100141c21404214282440109070b43c14088600c82c01045a801d20100081c21447c00e1800b030f01c1002d62505072080d100d481072800b500c4691344e01e00b282d4812005210b80c40850404612030340c2140c0b141022900d0282d0750000b0404092006005075a09440021424011080000030b05001c00051404120010b01c0c0600090b07402c14904040e11500c0d49c407400142605e00014034189044990800c4a40302c4104060040c00150980030849103051240b0615040d0240010014180e030002000242140c0c01c119840b4000d1080649451050f138480101e00f07070015080c13201901d040d0311658042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 205438183 1250 205436933 205436939
    0x503070812010f092702030a0203060c040603060e040506071101020d050c0406030e1204150203040308030112051e0a0602090f1003290f040b010210060f030b0606030402010e040c110a0804 82
    0x120b03d04241c0d0052204c2414292885985484001d0081d1880c40044020100300e450b40003080c545200440025014410340c0d0900414802071000380c811160140d606101164030380d5800c2d040b411056500900a03400350010444850160021101c20b003c820001810804000c00c0b540a9a50a845c002c3c41003900160034031200c2d41c5409801c80200c174580c000c0032549120705440000e40701d684142901c81c01406c3c4c182c51038038401c1c0211002160084911a16561103501d5425141c440c02c4040f01d445c890040300b83c4a81c040d00c094140810800005000300900c5030710340e200658440005250312800f100150552541d803000f00a10f141d120340d500003507101e500c3c248112040100582400d0305140a410b003440c6503034070082821905029034004c12490203910050b46000141210301f030a072818070030003081410304088418101c0e40139929070f00c12030300c07488140103051006540107400155003020580c11400c080c0c01041c50701c0060301d03101d02070f9603c01c000c10b4148040d00f03038101c5445200207020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 205439433 1250 205438183 205438199
    0x6150f1207030506030a0b07050f0409060915060e011b02030604060509060a06050d020d14101b0503011206090804050415140901180e0a06020a05070b0a0203060f010507050307081201 80
    0x100d507024041d42410040c0d82031040c0000c0e903400131410001c250600910004000c03a1061003914107145020407415101c64840b8407500141150340620000079240601c07200582c040a05d05104898881d21030281014007400112240c04280b030141c0740107407044244c8401030300c00704011031181d40aa4000542400e01c503602c28100040645020015400d00c04103010590b00c07090700554207681200d000d03940039100e00d0248560410b45011400500401c805503800f1031180c2c0001400c400704613500c0502c4202540c007038402e07000c01e0091400f503100c00c640c4900054030366032140c00c0e1580143c140344d0400303590301d000030306440e0856014040e1183c90304003000000d0544103002071030074003111025002e41c149086002403440d274020420301d442e217594080d0396420040c04100c1083c2d420101c25075a0318034522014002d6403000c20308444581e43c010010b401c4480038401d40e0302800f0300a164001e403003000b1004480d07a07081031005440700d0004225440004903190014481d0030018850822650700d00618 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 205440683 1250 205439433 205439467
    0x504111f1206050102031b10090506010905010608010e0408070302010f060b0d0510050d080a0c0206070b070e01021c050c1614030613020a05010c050c09070908070803090f0906150f 79
    0x1100501d01e051400a00440c0e0300403041e2400c407019011050b5085c01e40003800d80c03401c008081c01d10480c51420450300309110380451542e040c1c400301a000d201c241d0b600c00c4100c0b03800c002441143c040c0f05240300820f000800182c01800f903107001f0302c0081040c0c0110340302d640884145600520441c0301c005000031090304140034240d03000110740d000364002803901c80400d80000c40309400034041000040ca03d08464001e003e1145d045070040c3c00075442d2840741c03820341180c550641c0c2c1400461980f050b480481e43c400110b0405c1064803040f1159072811b40101035400f0f8002d40c1c4480e141d8009e40d0211185d489001540b24000e108420995801c4c071040000e06041181c09040c0240404a003510f4001580f1038907589000c894080c81d00382a03640441c103040341450114400d0303036807142589084c00b0545a0040e00b8030150380c84030080d0b91f80940c0d288009070391791255021007500030350001442e440901d1b2030318103a41d008002600d00f441c840d4038100444443c0d0f1101c042110003400c0401e4400c1d00d4480c00700e03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 205441933 1250 205440683 205440707
    0x50f130605031f361803080109182405240303070804031719030b010206100f0e09010207020d03020709050601080919030e10030e0d02030a050d0504111f 67
    0x841100398107000480054588002c18010313040c001d01403d00c07113000c504000401d6070041400401c0f070394840342604826003540301d03800c0d40081c0c0c1210002c542c00d001440b800c841940343c4900c104840c0d41a0340e03564800440d0750740800080310900400c07809508030b80940742c81400198000c5210103034010503606083c004e0107203e40241d106024000009140300200c070241ca801c1032014500310400341032407901c1e00c6806c50208000201136072245035203425030054448021300343c003601c0700e5541c2d900c4119100710140c441d948100325030b800204000240010720540082060001515044564011543c00003880301c1c04c400680c41114108400900351041c583c000001340386c203600500b0582e40c981d50720403c99442c029903000b04500c0328105800b800c039803841250080c2a10300c0010380c4810140080501d1030401c1d03c640120741c14200c0da00e1001c41101d880c0a06038030b40d1820803000000030300082c01d00400c1290310050017207110342e2555401c202c1086560b0b00c40c103568004c010840c0001d003140c011032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 205443183 1250 205441933 205441981
    0x40201030b0303040f080319020d0801210f080306031c0c021314010f08070b03060a0303030e0a06061418090616022407030c1805062506090210021606050f13060503 72
    0x51094112181d00442f5641103400c0b000ca1a0095107040300700702e5509116400040a100320070703444030104000100654440c100032010703a000040120000d03480c40c0782d44aa000002517503d07000100502e4200703c0006000d5840c00d00041c124400c4424510180080c0c121241c0c004410804100e070280800031400034041e0f642145081d41030500101d2030320245070100a007407549a240c0010304810800680070040d4004106011495968045141c008030304540103020b01908045540101d0b040e11a890190002100400b6640d84181c2455081540010420114090303c0009290185459900080d261141d80003c80c10709144901034100d4640101b20f0040c8441181800205d480b05400c500444034203584c220303076450b0a0b05d03903c0102000308140e03180b210a892071305400e00065600c902006482660019503840c00200240e075500580a007d88420b070b81650706001c81c40c454405003804203240740d61207052040f42c0000d01d20352a00380d00010005000402007081c41039650b120a06882c2d048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 205444433 1250 205443183 205443193
    0x806090a020a060c0201051c020c01150f0506090d0b040c0905040b10141003050601200a0c05060708030a0b040e0f01090203070506070803310302060403030f02030708040201030b0303040f08031902 86
    0x2c3d03400a800c0740501072354515150042e0250440403001074040765201e0000c234008011490144c0d40a582c58046800b80c0b005980c0d0a58001c1000c2c24050210f40e240d1000400a400018041d45c8004ca03000e03006104803201c002209001940902c00d00a50780203610900c0308450074034005175076403000000d5901501d444155800e4151060301c0302c0400d807000f03420030324002c15640d030783c81c0041e9080f41c0d06103044101c1c5115803080303400e1910089981207055200741e142c03981346952001040802c0c09209030250200c0c1080000c00c002d00015031240d1041c3c04060004a02c412851052a04000c17940c0555202651202a00c008603d014080704001d010215501800c0440d00e031200421030000924402e842502d018003680309203141c00f018440d00b65030760010036881d1440d02c3c0083d111030003664214003203410982403180641580c000d49119041c15501d00529584580044018000c10010150140003c100c0031a044040d03201a00c00f400e6400011030340e4910303545558003500e0000120704115004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 205445683 1250 205444433 205444457
    0x11b08032a0909070207080d05130503060613051005040e06070818100b0d0203070f230105030403120b0310091b12230313060216060206010611070806090a020a06 71
    0x42009640d240322040e00d600c25542c0d20114140c1c41e00c0c4094009141921a46200d007050030b62210007072980001280035801cae01076a984c01e0607036510068401a40c04400c4c0b15104100b0511640503c0d40306890460110f8000c1e902c40101e000c44499110f1011260000001c0040c0bc41d006902a50403021481d400c21080d22046a281c2e10342c548023009d03540300c585401010394103a80324130050821940060136165034a40e1044c0d0707159007823090712416801a28850380c00c4000c95010211100d240f2043e15401d2a603a2295021a09040c80b410904030141c2e950544e24442e44007084a201041591040014445c08030b042030b0342032089441010082840c154020702800c00200d811241065021a1000b075104807003030b52031260303580050042400e110208a510602440c156405c04035607081d0281ea0710a0040240e00c078403072090380690307000b5901c48401002070b58800c0c008400340a01c4d84007030f03c0031682c4490041e801c141041d40c0a1a4070fa204058020551a0022103030004128174200780d081000703 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 205446933 1250 205445683 205445761
    0x11060106080118061d090601060e090c0d180c0f0f050a050904031209030e0f190608070201020c070e0a05010b0711010e12150901061a030c0702011b0803 67
    0x1414058102000c05090654052074810781180002c4c1100c55172210b0291601104000e03501402c42d080d03030461046000018a0034011003100c031400e8005485180c03c0d036110002c030f40140e44400c1000350681d03035800741560010b0751900c180e460a4401d1000100b030394a4841134808501c001d4000101003480c0100412035507481c822018102c0c0c034251f0f4061015940d5050a0b92110031881d001030f80d2504007840c034400c0560019011020907012913114170344461940500c02c0504000708051943e99a110b814417004d40108003480d84a806031001615180d22050040c3c00c1a40503845001c00c105000c050115140b032600801e80500704071020581000441e407103540e090003007074040c81d0501140082c407110a841e140385829420f4207400844001e84594000403541e0041140e165949510b82600800c100c601c0d2480e044800780f1142c0310703900710b0f00e03003064940c6107074403d032012414410995a0720100d82100381252880e035006050040e140d02c0c150310f140d142822100320191100700004c00043d8512 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 205448183 1250 205446933 205446947
    0xe0106181202030102090a0f06031404020102030a11030d090606050405011403100b0103061d0a0e16030305280810090603020607030c0507031709030c040c0e100504050409030f11060106 81
    0xc62510180c1d07406511030000c40d00a12490b540c842d0428400b22010070503404988190007255103981d0302304080032003084030018503001902c0080c0181c0081003800103040c4110343c840d47c50b031021029607160128140d002401c41d40000e208071b800d02c1d191380b81001940761500c9824014423180c988403405480e5480080e490716607841c88602560760340c0079004056442540850080c01c051601070040700041c80340b80405100441d5198481420304c2003202107840045010224440c4080e031954080c2c0c11540e05407100c0c0c1182c80803c8400400b80c0e1884079190044200c40903c10307860300c07010724604150401200090b01a004130306086e0401008100613203480040303a074a41c2e094a090f0702d1040030b0b40741040c1410100c0e8006007044000c0e8001030360326001040100446034080b41150041c20703142c41030009a48447c54140c0c04502c80e0007002c00e40d410040720a4160f940c840c40c004c1c0ca03181d140c800240440c0c1079440c0582c0010301058030200c440b904100100f0540900400a018562402100400c05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 205449433 1250 205448183 205448189
    0xc07080124050604080a1b080a0c0312140412080f04030c060f050a080a0b03010f09050102180906100c26031605090d03030b011412040b011211090402010c0212070e010618 75
    0x1400780d80c240449651210094041c000200c00d44500044034240f490242b40c0f80c0c00300b034400c424070380c0410581c28003812285c02c00c4001c41c0c01150500786801944010314131022005e407903d0600f00a5149201f400384010300c080e510a40000c848203051480062540d42c0c124070308010311004000030b040c05504541d9043e4031208841c00490344800c035402190140208d8900008034504089000040000c190040c4c160b550711810361a8000c007040e0100201c40d9000e903106c0e42c1122202d07011214991103801b8503a800c03402a00c480d100712030614003039690180c520b5240c4a50f0300303011041c4081d58003c6100c1c03d103000000c0c03600c64240501c8000051941a17507410090034595100c01e10075103a40140c0710b0f51003ca6000c01000d403038100305040452003000440c0c0440f99000c0100c00481c00300090040c500711550000400d100000111051000b2210050401c2e41400000c002c1440140c0d202c1a641d6940c2602c80c014011b1649010b0f0001c1c00400e0680000f07040c4064070154050039608420b9290407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 205450683 1250 205449433 205449443
    0x5090702060a050402061c0c021b1e040b060d020909072f1608030705150907090b0301110c01020705070609270605040c02070807090612080c07080124050604080a 71
    0x240c640e440046c009104490030413419400c01048145640c616138028070900403180c00351900c050200699140b041c51400368503500403014000c0c0304800220003507100081c00c1c0036200080c00c8080c000000d1071600022140700340e050700080c0140d55414450303081c80d000b80389800c140142e4181d035035007014080403c0d020080070700308c00118a01201000c00540d40b401d800d50400642042d11141e51a07100d40c0403601c1952a0b109025140182c1c603160104c1c80d2041003020041c0c00d18034244030078400a890501c011550641d00d90003060a10050000104164004b0100050ba50f4101d464132600b03000305a4040418081c01c0c6000304003880300d070714514480c030000000c030103400181e02c0740500040c40d20f90401c6410a192444510300d0940000c1c0070350a4803024021500702030780d036a960030309980303c0d409000c4001110940c08000034804e4009024038954202c01e907240a03846101d241c0c2183c10590310300c0d01c008003800307040c0a540e500e051010302410007a908030386400d080c00f1400b942c8034002d40c0001d04c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 205451933 1250 205450683 205450691
    0x1060804020315011e1e0b0a09080709050703140601020607030b04060f060512090d0f030903110115090605030705091302011e020a03030b030102070f0204020306030106050406030605010f05090702060a 88
    0xc00c66030305110405180e1801c02018400c2e50316514100350320080c002813000b19401500002c540c0507211003d07642c002c0303800c001c103e150509124900c10b507a00410080e1060080341d541c0400d500300c0502c8a032001d40490440021a071804110040c191036402c040c80801c10380b0401400410b907804681c00b6400300300c5040124a8600c20703030129000302040d5000304031080c0010340129100b80d0050080413080c0714100300311096180c03004255107600c5050303070440208a80211460190303010750807040c00e4178040d080140c0d01c400b109104030f00351400320b142c15000d030201c030380f05120480c21445030300c014140c203078000c02030700d030030400030a140d294003500d084400c1c25114049011a886404208041e0001d220401c0d440c03e50070700080c1d62002180c004074040380c2000d64080c01420144252402140c04c40c164818480b860707001d010007580040c11954041d521047c001c615178807540a064020751180d000000d103507141491440c0d0104031500000c0c030400e40203060010882c0d000585540083d28a04001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 205453183 1250 205451933 205451941
    0x14062d0105091008030304050307050d05040609030f2123090105030f3d06111518012d02070c0306020a03060504110a020c01020d0c06110702031207050c010306050603010608 76
    0xc01c2d240c3d5900030003aa00c80001004200036005c8050441a407046088400002c40b83d2001d4401d40103900a00c800121010410400300d480900d0703c03112940102c18882040b580b000481c82d009180f000c080020820138820450020b0480072581d81654120394041e05207521500020b0040c0300140c05088040b1400780401c00c600c03040e00c0340c6655950010410040310b2408102016070b0340000c44401c0d5280781700c0c03100003816409610803000340c01403c00501440310110031820381c09400540240d8600c14224035410300b9180c244a403420804500d420071340320340d462022000e250480f4401340c0d441c0d1070040c460080022940e08035241542e41c40107000d80c07903200e41001100241701d02c1d84829409814240c0000d00008440000d000c155503587c00d807400308254100591780d45040c4242c20000a6650400364041003869000c44820004a03000c18034059070b039000070707240c6580002c180c80c05e0480002c0c0e0f4401c101c000c00030303058081020b00b020700026103040c000a40a0105204000038016604005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 205454433 1250 205453183 205453201
    0x901030e0c030307050703060e070612020309071e050405150307030201120b0a0f090e070605090f0d0f0309060f080106050405060d02090406090609060b030610030c0c14062d010509 79
    0x121081c601400b120784800403400d0482d62a100f40c03009548803407605a90702594800030854006548994035143c2246401030305901c025800100705220314000c0d514045020013103190300c0c0e403000940c0000d030100c2909280401c821500d014000c0705641d024540d07406040c1e24082841021203409080030f03000d85960104d0080a4103c800116602030b52410020404c1903040c1480030507501d0309501004121003025803159030301c4488c000c400110344140701e004864130308440c942d0303c07203040500203059160304c41d07076440310440344820201e0108034080000e005007948064203950104051400100c154900300b4041c00c0c2c1c3c419400380b83c0c0208000a400750000641e074041307400311000900100035041da290300c643c0040c2000e0080c2d8a14034182140090120300700001e80e405000024003001e45520350f954250000d0001a90840902801c03000c240d0105a080000e46100ca800501400c3c0f149014400b500000d420310045c445c0540e280070b0301b00740b0171071030a911906465043c6c0c0d0a068a0b00d4080722 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 205455683 1250 205454433 205454443
    0xd0302030c01050903130905130209060a030b04080c0f0706080103080708041e080607021501090c1b030c06050f0c0d0c0905040c09030203121c05041505070201090b09070b0901030e 79
    0x44410725820881800101e01000004052058003006180d01190f1200c10203804e84074140e0301030b06000392240c10720002d81703404900c4541201005190103250303aa13a075190149448c007210f09403156100401c0000c0f41c0d50301440300074007001001c000b92102504021003d44003031010b02029000300c001182c01d00c01c0040c002c0403038015041c0054004243d0140c260490007107034803030141c0180c900032080401d550030b000059010040741241610f141583c20043c7d040020a0078520100400222880c2c03a000214129041c288140c040d9480c0305840e1400d041200c1564000f40030004c03808517a81c100040a0a40f1003a51082070001c6c1011510a11040040f50107510980000394030070300d000807540b0a10b030054820702c00c8030720039010360300031034104100003070385004d084103941505602c940d003489180030a0b800b141c2c0c418494914030805402d0b100b24a012117500b11100005030703550702c5802050001c00504640e00c40c1110000f00300403414032030303140444e0160382c0145041c1515158011b403420010f0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 205456933 1250 205455683 205455697
    0x3040f020a091103070f02060705180d061e11030609060d061103091608010902030c090405071a0a17270c0d060501150302070512091314071701030b04020d030203 71
    0x6100040307040c20b400c01d01e03600030344441c5e0110702d00c00b03100c859550010400e43d00c558580d40344c00e800d242d606502210040000c803007041d446269040e07110b0008005100380703c4090074100044610100000443d42201d0801d003144211100900401c02c10f90384200403e94030080913030f0800400002d44c075100e8081c1251000c521102d43c2c0c04420003000800009082d030201910702d850b40d50340c9940340300d85801ca545d041000f0350950400d505403a41030034224212504903100302d00b240d06050361041c480b0390b00c10000f4454031001400044400d03486500034020042203101c0b040d000c525003018081d10305502c9400000040d0380d1030f1200c4a2022410510034240c083c000501801c25200030b910340a001403009000e2003441072402095540b1140c420305c20345241c0c0e6803000040c03514040485445030761790041854a544028004800070045456004440858100c21a845220708042801410400c000b90302c001164080d90b0040000c03500d180c512a400580551321412013a12504049043d481006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 205458183 1250 205456933 205456949
    0xc0513020909091b0405010509010e0c0c12040f090507080a0b060403060e060126150c0715090203010f0b0d0221072c0106020d0e0a051302030f060a03050303040f020a 73
    0xe030070440f200501050702d4005180b1039154182c00100c0e50704010840e04280030300c5801150040041c001d10328503180c1c807030700941c80d04260340c18407038140d09c0280340080900100e0320240b00400c04101f90554515039a002d4158281c040c407491600c1d850040000b18020641200203481d1401d8800c4c644818007250003464009078140308140d038641466035903480a10030704919101e905400c541d12101000d0719648485000c01a1031029903180e001001400068a42c4505142c104107010004005044191251125900200b001012401014216480358000000c01402e25000e58120b941d4024054482c82c1d04441c0c003014400000c03440601c945a5240003c201d2048040121300074441c840e111541d0481d5001005180c848000c6510545000b8401c80300960700003590300030801c0c003401e02c2d5074a0640c007a050700c0c0110343c4c0d840002d07449190001c4044517554008140042d4188400440364042c109440030300c00c0034a07607a9216603d1000400140c08000c044400004550b500b404040041510fa = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 205459433 1250 205458183 205458199
    0xc0a031404050406170f07050102030307030c0e060c0f1006080709020f040e093a0f020a0c090c081f050d0606030c0b1b0d0e010c03170f180a0c05130209 67
    0x105001d0911544044500f241c911603032140c120751506c000340131003d866042e4051030454480310b905034003601041800300184170858134000e0090f250305000d02a0030303030030100600c403128400400070300f040d6036003241c45034103401c159040c071003410002180401c8403008903006a4403810006040524061600400ca5031080c84083c031082d83c1d00012074002c2ca5135070a0b0a0800241c44006c2c5030b030b0340b080c00140320306550316151107100c866024a000c1208080c0074010f0b2103401e1a076690b54902d518464203c00281652510700100c0c03154800042a4011802d442c850301c0100708211485440205200c0d40b8443d0039014003540c104000c0360000c10041d540b083c2d0901501e6100c3c00311640c03036005840c41d2426a88690700d5607104c8000041c210b001c84000e900c624600e040401c00443e85011200d4090302401404ea00300f071041c500c0c4e202d40341d00c10742600050045600f0081d5400c91712030050f0303160b1b640329401007a422010400b90b18200003100c4007250003113a1540c880e0343d403001900440d0110795000d035103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 205460683 1250 205459433 205459439
    0x2011205090601120c1208270f0402030402060706140108071a1b070305010608060601030c03090f06050a0e100e0c1f1b0203150612010603051f021e04050a09020c0a031404050406 78
    0x5800c00f408c40503000786048001e80c1c120640740421124102602540304018200e483d04034103281e4011900075002070b00e8145403840b9502d0f25800d50b000440c1143c0340c0710b80c0034010090b082d028408100548000303000c0a0803c0c3c9200003403c010700810b41c4454041442c02c4250070300c43c0c000c1114034011035014000b80401940c820140b5155801100c0d43c0780031074181020207108910034404c02c02081d501c0442c00141101319110f000041200602c0000c14640e03030006401c070084104165803c2058115010440800c451500c60a00780c3d0198098003510039001010005c14401034079060700d140314a4804010540f0a0040001031000c0303001a405004902280b804d0b1400315040c0d41c401d0000395064403140c229014824201e58142c8405401e80e00b18070051158040c00310814055842003074009030814040d42013020309051540381143c03844800003410051802e0000c6080010500d1043c00c508120324110240d460703800c921402405c0042c0f0481c85507041700d0403400e81d006070a0240c020044961 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 205461933 1250 205460683 205460693
    0x80306010e0a0801090b06011e030c140c0307020a0801020f12040c0306060303020303150a0b0405041a0414070315060c020111010f05011815080c09250c02011205090601120c12 77
    0xa0500c0094070300d009001c0007e2584d5015607000c0401c5000c041100d108842d480000b20010248116400304108204d0003052107001000b01404005000b00081c51352403500b8410016110030981c8000416401032203800395a40b035640590380d2004102c441010349945510f03040c40400d01540004228524108011050640c00405540b145407001000c1185041c6d800420814a009202d070b490240e008020030b101c14206a0028101d09904d440b03c420041d6001000809030345184000f000b00113089020402805d0b454003801c2c000da45619502d640490130104010322b041c0e019600607041c418509103d146c0c029095011683c1246004030130806941c50f6608464180080d0b00c4401c01c450800060441c01030801003050700f00c0386840700910b4600342c80da090203915000101490404c880c0d402050461420f00c00e10140101b02580d0b90b0500c441980c030000d08040300081c9040d40d100e05c1d00c1c0402c40b905100040c00350540b0900d40c84050f180d0424902812801c0b01a08012000064807001000b040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 205463183 1250 205461933 205461941
    0x60915051c2a1a030f1503030d020903030d0e060f010f030b0a050702031605060108120f03180a060e01020706050a0507021f02130e010501140c0706030c030212040c090e0c030a080306010e0a0801 85
    0x3048446110540e0f15610003441b421055042013540c190030400030061819200d034001e042820317014080c2c9044c0954080c15400b11540c851388025590807020811400c180303040f030070b28090442500d194000310709540f01c40e0001b030002080030141559031000306d00300d54001c00503103007041e4084078006800d4041c0e20b003943d10b030b180a01c6151464480d000c440306104080300c0076184005101100395046580d0f1869001c0341000f080115030751800382c01c103a440401d001c0c0c0198418824008000f503525001490705400700d92004044e00e4246180c8014007207103030303404903554524100c084034000804100103410301c024466610145000000d407100051041d50040109048070000d8903580301c540e00c2c01c20107141074441d102d8002c035580c02c907050600032a8029409200030101500d00142403880d0042403585000050b20141d41002c00c44408204034030441c06071301d42501107c400f40a9140c18200420341c0c81c98a030320000c10004000c8005940d90744502250007032824014801c0c951039540e450303c903000f4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 205464433 1250 205463183 205463191
    0x15040b09041413291302010917010b030d09050102061303050c070306050a0e010207170c07031a09070902131418010e0a0b040908040e0a060915051c2a1a03 68
    0x180000d074484c9105035400a801001e80300380c2c2c03a0285031a55207210003610184000c1040b81400917456000c2580c504081c90780080c03010f15000090700c4c114a404040c5040b0306400300e0010081807010500c130999001c038045400158149046888031350602d815111401a0048803a89100c3e8040000c21303c4082d800c801d00401c0303017100801c070341031548076003500b40e00c542000944181c484c5800e03410400040070080001403415000d4501d80c9441c0d99440a021207031030b8448400800e1001880074010b41440b9030b00090540403021482c08044030a010b0f000034031403042403080d0040303400d1440e0a44800c0340d00030300c03840aa03014100a40e101c5500f04041002610140e1802c1e140c00610001c40c10184200e2181540103682e06041600c0c1c04600c054082c4000c145480240c0c42d0440001c400c52a40140b01407880656800040c1c10b04010601900945002c42c0214482444000300c0c0400d4900011641d20030724414040403132380b04c07005140702c1c44c0a6a030010242da51400d202d4030113803001c84055805 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 205465683 1250 205464433 205464443
    0x9010e19050613121d06160c0b0304080a081b0307200a050c010509030102070b070c17031b0a030209030a03020d0323010b130e0705190e0f190308031e0615040b09041413 74
    0x250710703a00027940b240011980100300c580d0401c10110700ea80210303545684a51048440d0400419100c221a40c0d6003068a0310b0010401600c2c0442e841c2c00b60809120100c0c000200410000c1c07040e8a510381e4a4880c041c0039414000c00048138080c0d52829012581000e400102e03025083c2047c8030000c11000100d0825601c3d180140360f198132401e0700504a078000c001001041102c0c420b1510402641d9100384140001e060b42040034401d00d031014004101001d0080d0060411101d0390000903042d905040300c1030410002c50f4604e030306581c80c240300a43c15601c171124000d480c0c2c4012000c01028001a0f04160b10b401c03600300810100c10b501a00400d19a4260702100803000c007c0281625000d0001c60350310391210850405034494103040e6040324001c94941207001050760b0b01c4d100c0040d01c0d44240c0b40312170350307100c1d00150000b4007495441a54000c41c00f960010701c58860101103119a00560282580040000544111745d607125008180002555003020509040204803040e80141121b02114 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 205466933 1250 205465683 205465703
    0x10915050603030f1804090f1208090304030c140a0f0f0f0608010608070c05010b120307020a14030307060509120a03020c0606040506130509010e19050613121d0616 72
    0x41504001c801e480e0840300781180c060822000d280d0800c050720b003c0c05445c6c3c019690f070450101107102006100c0203a405000310782100c00b10039000600c4120001e0034181994000c200070000640880718040807a00385c5001c6100c501d41d40400900042d0042d030200d00c85448810b80032400031820842f50741100c125030031520300c00d590740030140c49001c2d091282e130f0042058400020720300d5004500321440248203030000520884442c2c00240350342404142e0011552000c00d800c1c0c11800c010b4284800341c001078201000580d034038400640d40b403250800040c002503c2d00c0109086901c1000140c1e041c0e100c900301a40c03915070410000300250440e051030745282c4901808207040d030801e4400c1130f0064001030164480d01c102c00c0c1ca078901800300a000404c1d02e40da81c5400c9002d42c035040c400b101000d9000242c580302580c071818003502e4040d018048500100c9180501e1002840300c13419000341000c0d0f405c0803041d42181004010072205503164a0b03401900000780303d007140211a01410b490751244108603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 205468183 1250 205466933 205466941
    0x1c170106030c090605030604090803010b1c06030803040f050304030f0b091506030304050111030d020a0305060a06030c08070f0c0203060118150b0414190311040605030d0e10020f01091505 82
    0x20140d41c0030320002d0022400701e000a01c0780b6413282000310350000e4040d1006c1003448060741c8002d00c540c0300f40d000010032000407a55940c6c2c284500403688000d40411024002e01d4116218074906100207040107112403142199441007207070500584004540110100101c0401c6042c000c001400c11585c04032680548001c0714030845007042c0306405841c02400850074503081c60010754070300307020a0b00c40c2e0103031006000401c004072a5000611900384540e5001c03426040860a100084407103810041c00d250070311000c91a00e590040700a54030107043c0c038024014500001c0c041d1081800414040d4240c010382e800400c9681800c01031f1903d19046c28010458808000941c9008a0460194003004d08040004000758544215049800c410062400300c20404049925828643c5540100c44122446c403200003a4549803082400a000507000383c00d4000401c04000d0080c91442e081511410015500d40da41038420080e034140420b85500812094510341011541400c0c00c1d500c0410003402d02c0005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 205469433 1250 205468183 205468187
    0x6030b0f04110f060f03130212062202040221090601060908060c0a020f030a020703021e0603061002120a03060f050111060103030806011e050703030506150904020c1c170106 76
    0x40344502e820181180c03102c12414100701c1100c42094403280e0000f000d003c24102c00940900540c000c00801c00d01c00c20120081c03050194030b103800d0300d09000a82143d0100520b150907802c0c1002c1020980b1024101e1681c188001002401850021101800d030f400c1140804040e40c0c0c0e400c2d00030404d80c0e0450351b583ea80d03a10101e8001140e070150700d03120b070080c0c030201d0f4108000102602019410b80141e4030a00f441c504e12a00d950401d815840060340101010810760170028034404500010a008100344030404010807040e02c0094500703805040d002d0301920a041c401c0c4200c202810800c01d001c3e548500d0444002e0151403c0d0041e09005a00c002000525602560468540038220405020168070b1074400751440140100814180300b1001184a030030000007000c451703406140d0711002e8813040607040003000c841d0010216401000920b410b0702c60054124156050640211409690b48500c4d500c611b06000001c59005481c41d420802c0d1406150400f56000e20b03107030b0002110a05a03078981d01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 205470683 1250 205469433 205469461
    0x8030a1805030c010c0501020403061b0f14070201200102040b09090105031c30090501050f060f040902040212100602101a010c020d0212031e271c030306030b 69
    0x1e499260b4000020782c0410350040d812406154060400141065602e0b1104000e0300d00341215010180c2000011100090300143d07081515a103615244044d090221004200e0348159070020f81881040c0c1034144030343c05102212401451810001d640300c40c0d0f03490740b502d1150840b00410384904024000480e1508000030710f500034400d400c60107542214007540030740754079a180d103030000c0c4883c0014449031101d50220220105407011480010030240c07504050b07007110070141c58001000036038000d000311a40e0710405442204d03000c0343e000404100070f10001d002449284050191803030424104040c5000003980001195030301d07020794108a1524803150104d0b10040349a8a0110792002400c805510458a2040d50b52001d802028120400d80015a41002008000301e1550000543d109014060744010b82940c0c140c650b181d080c0400040300704101010221284880030611040403400da490701040b121101414a14551420550034000c010301541e010503200f1803201c4000c604250a5941 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 205471933 1250 205470683 205470689
    0x609090c0309120c17180916080a0e010e0604050f0715090902070f02030f0c15040b030a050c0702060c01050604180816020118090e0f01090b010b0a1808030a18 70
    0x14101d000100d0300041c3c1c0d15410180081e03400d842d850321070170fa84d8105a001060004003039810079046403401d0041015101c0003e1035228100c1104a40e01c0e0070b50740190f051600b02c00c104902042d80503c540d0014010b10361015081c049128903802d000600401042c11490100340c42c080c0e40c0c4194075080f156440c80128002100080d4100800b08002007040d40072f80000c0348500301c0070204c08800e8001918020510400941c1504090414040c500d011541c00c3c0c1c1c05221450043d00b07284ca8101302502d140401010b01c1000d41d00c0f074000907000143d00040b14041d41d030041815850390100c2c0481c0d40200001c46030707580214500780c00b4001d21040c900c80c004032203502248140c0b80c50a100c01100c0190000b01c0c04a05005210008103241c08107045001d0242a110310000303000400d5224080c5030480f8040c414919914141101000ca90920b16a03415140400082c556810840340c0443d402e44d1140392084441e4603080d0080303002c0f00080000d00407000c0030faa40808040ca6a0840e05084440388 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 205473183 1250 205471933 205471943
    0x1051f14010203090d1a0105091b0304050109020a0b03040302010c0e0f040e01061a0c010b061201030f0807200111070605091e0303040303170c130506091201060609090c0309 76
    0x10414403851080800301210184140c90a00901070081140956020404c031000401040803070b50202c030743c0000700d00401c411115039106080907804c50000f80500d00e100c0c4c040d441c00100042c10b01400f50850503070700340d003c0d044680b41d42e40e0381e80d982015041583c0481c019420710080320326080c41540c1202601200400d990300e00c00c1c50408000040442e07108000281d5221400059880c3c00d84901072144415119038555402c5084603041c2101c40c554030051049e9010301c410300030901d90b0071f20030781540d9000d95901d10f0085030f82004000c0c0c0c0a440300c000c20f00200e5510036a9800b100010754021b5490a8031440c980c424030748411601c84009005e04d50024409100e94045071611243c042da4180030741c41c1030580701450358042402c560103078105074003041c007081c4008208081a201c1603804245803100300d040a00304030903041010380600c00c1034070865001c100302100d943e4500d01040001c0f40038000304a80d56542c000030f4aa11034503c00c19400519007140111000d020b8040d440140b43d102c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 205474433 1250 205473183 205473241
    0x3070f08030301051e04090302071a030c040e090f0303090307140a022202040305151006170624130e090102120115050f0c06040618050a020f01021c09080105 69
    0x45002e000e840e1980701741790a0080340c0175a165500340c40358400e86180c14002e074094440c035401c0ca101240e101c64015078512a0384420410040020700680c15642550310f5660701001644030418060700d0301c3c2c0e010320b0101c424000041070100d11040000204002403085a41e05401040c5604003610340b5484040a5040781000c3c1c000e0462805200302e0b8106288201070060400342c49485240c5070400e14010414000109024008040700390b51904006010b5460706845107081c200f840714130004080c100f03074040d04658100010848044c02015400f1030019111074681203501c901c41075071203140c803550441c1a54003010071b45204c010700880c0c034140d01d400e4503080c00e43d180c041e60070390070026200f00c0b000f009014000304000840c103600801c00183c1c140c00402160406003054401c6079001340700109814200e0340607400241e800b04482c5a41a01220440f2501080e2030040c2c1c02c01c810031304902041d82d22400c1894690703402c0303e400030a41d2002d0008104903500c04206102c0c000c2c0b8043c001c00d035030180d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 205475683 1250 205474433 205474439
    0x60a0903110603010b161b09051509040503040e0a060509090c010908190b060a1208271302070615060518060a080423060a1e05040209010b13030c06050903070f08030301 74
    0x30039400042141c451202480e031450039042011f08141c2c40e801294001c0d0700c490902c0440c06402d84011902c00302182c906070755007415031300d1640e00d210750b10400f00811140383c0064694400c075400100200030250850080b4584105041c0e2210442c815150204104a00100d685000050383c1500c1c1c085000656031030134000d40381c9060603040101210b0384840c2c202d40104400340802d220422062007200e030b0341e0302c41070805500808034482c03c064040c0300020652009040e0f03122180c000b811981e12a00682d203036542c0c1000340107025a90740306206143e07440f20000e1202e6104009214007400e04400d0001c0120000c1006814403c41c082c401c009070078403001c10049004640c555602e49050401034039400c003da200ba9003890300c11250308804c550358161541d030038412048a0f81121580382c1040040d0314042e80021000c01c41801806070b002c2003c5a44110161081107181c00346800610000c0a181d0b01c40e8010095404034039254028060390200068a10000300810306503038416026500b542e007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 205476933 1250 205475683 205475707
    0xe0601050f04020f07080a09051203030c030c18030d02060601020705040902030a122d0809010213090506240405010306120f060207080d0c08040501150f0306090809060a0903110603010b 81
    0x202100c19103103641304000d62030008000c100101422941d545a50890382e24010410240310300c1003040e0502c5400c10030411009000b614210781c0c2c4201c80260341c580700c2e80ca0741000a400903145030340715014451a03021801041c0c00281542c032640099084992082e1110148001c0da00c0c880d1000b9010360010f4840710014a03403000703008207010949400d141c07100d200c507481036042c021060590907509248501c1851a9403126006500c03000200080d8039101401510b0a080202803080b041d01c0c6030786002242c155918400714900c00400c0488141e40040032040041035a40188070340c501003850701130700151b8070340d644a0500c0e149412858030424080d641d11450044e6012081c12a07800808008000f0949018403c4030015561075540c04010b150603d03110b0b00711840c0b09491094040c440c0000c1064007a1000c2d80002e40f030307101002244441c802d2a0101c11030054100346603101c80c012031182491940080300d2411240110a12044007083e04c0900c803240c88280243d244c2040100034001c0094 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 205478183 1250 205476933 205476937
    0xd0c15050406053a0f0b04050c191e2c010206070f052107020f010204080a081308030c030d0f090201050a050c07030203030c1005090114040201230304080d0e0601050f0402 75
    0x3500c40d05007501c0403900702c514000100c038a11568011355a0b1703501001101c18503219038009104280d0702001107042c400c200105900406410030319070296007003d00500341c03041d8110301c651010ba9103001940040030602400403156040400600c1d020b0028180c42015060100c030054035068018004503190983c0803a2004c40700d1100e00e040c000d0400c800071404043c0c801d108541c2060300301e40051400c14010003401d01900501820700c0d68010b00042c0404000030030201ca06940c4541001c1c1d913241a85084400040c55501a1806020215540c05000004801884211403c13402003040002c010790400403501c1420000e030000e48203000800802c3c2c022001400f9074141213080f1802c3c59074030b80c0028507583c001100e00e100c0783c00032110050b0081c1c0398040c0c0c5410000d540000c5c0201c1358076483c0c4aa032a280184003a040054035000403900001c0d201019080700070b0598400d80c1d13442c04d824200c2541d0b0207984000901468010312045100f004030313455050360360091004003560703207040400000e5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 205479433 1250 205478183 205478227
    0x1c170c0304080f0903100207060c080115050a27170106080d05030a090606060302091e13050601271503050906061504050910081504050303060108070c020d0c1505040605 74
    0xc00801c104d441c44c60741d0100580d100c8140c1c0003401507902c2d4483c0c90301c0c01c01d8901d4060204103100000d00180b02c401503d5503449042c000d2460041c0c1c4a540812040354507000b40300c80d480081e0020b00000c02c101c2c0c0701020490650b1210402078080164444503582203800301d10441582e60001c24940d40494440e000030b5401c0000c118001c200380046031540401c4072030a030311001c00300b0303400100702a580c01c01c1039800f034240104c0b1170149070200c0450042603a02241184017001e06039110005155a80900040001031884e81c200402d0b081c1c02e800f81010b54101c500420b580e8030900248540b50038828000c2600c40d00f9000003800c80e5454520031300c58003d8001480c50503a05041c4800b198589558010034460480c1071011140b10780b82c0f151860600348605401c80300315000706c00300300215900008907038000d0428a03110b1619600c0f00000c4404a47d14107009502001e41c0444a081c0314120000200350307941f072012082035a0440d4810b541620462040d6008101700744500e10002074010054220 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 205480683 1250 205479433 205479457
    0x15020f0c010806130e060f010506090609060a03060f0303020a1b081f020c030c0106051c0b0c07060603020d060b01031407170c04050d03020a050c06031b0703020c031c170c030408 78
    0xb01084c0300404107889541c510000c480d4000010050103540b01c0c445a4010302e02561982d160540200201d400c91060981c443d020342c400268141e0351901c2135010360300800c2402441000c007900c9160089d20380950500175142d40d410240d00096500e4040e002c2c800b11000d410050881000c00c2184000220720b510030a020305a080c000c0401071201070004055600c4003400014407a4105401c001c8460040300e00e002d03030100f12080301000030b90200d00668001820711a51074580e5003a26161000d807444c0d4100035000f420900312102040f4058122500729482601c0070320450700c440c0b28142840c5001c503000c000280084103002001014441b46a811607049603040b8a0b2507140c101049001480300c1c0201c005a010320200020f03c1805d2198202c981e000311800c0e45542040040380c6000e200682d0005071410700081e42d03004243c000c018482c03190740080d041d42e89130110035071340540010440301e699001c90a03068002d05548a0080301510810754031490314107503101e035120091960050240169 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 205481933 1250 205480683 205480699
    0x19150e0402011815020f07031716060603060b01030f0e0309060702010504031e150204050f040e0313030b011401030e0d0302090a0803070b0a0b0d050d0f030f020309060115020f0c010806 81
    0x255015886918018099a001c5044c890794481d40080c50040030902206440d000fa50301840014000c1c3c0d035410800d40300c100f0f07180d10740c071080320700100d05800b50000600c05460b0110010030005143c002101c1c11000340c0b401c10a54174607245280a543d00030802803036a800421455074285060006442d0341030061520300c0c10580c0720341d075034580c146002040b4032860a840380301200700070442192904403050100203501703061070000414528130002101c2441a5109c280704000b8481c00c0080e01c18041c01c2c070080b404080d82d40e08002643d220300307005402c204080301c0c0383c2c1407940d400f038041c2c02c0111445400410390141000000c500030742101c450150303c549c41c4000040d13610400c00140100e503011300003070009810201504030864501e000d00601810306000302d100400c0000c04c841d5400750150070140e0540d004114110b009186840c0c118034254400300c184402c6d414001140d6050303e01200360800140210b0009070303501c102040301c80324a5481011111070551049251940080c0c001e000f0007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 205483183 1250 205481933 205481957
    0x160801180902120601140d0b0c341407030b06040504020a030f0308070e0109060f0c1106180301050606092110090b040201080711033702030319150e040201 68
    0x4010f0103c240e00455580d1080d0014848000754000c01c000408041f600c11412022075070300c030703e02040001d040041c3c8000c082404034804100c00309012556181c4001100c19003035184600b0000c1e03501d10006d440007548100400307070102c0000703000c9040d6a002195204d0703554070101000080c000c005c104070b8201e0300d01e400c0000004c080d0306c402c1000a00c680c42d00c00151811020041c40004001050b504100b1041c40410045401500e2003c0e4145d10b480c2140c01d403141410054000a844204950400e60001d49141701d0380289600d190550030440082c0425120f4200700116030046450302d641c09501c5150001d56003000048034010328403200240e03a40014480e08030070407034400e0b45051703944407461070403c0308540c0d000501c00d42c808090304010785265000d40d0555641d02400e4158134821f10500301d200044401181e0040f5020080b041d808607004580c3c00c000c2d240d07001550080441300340c240900010012a000701e585203c944640175800307034074000788003074220f17000340c026030602c20162020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 205484433 1250 205483183 205483189
    0xd0501150806100503010509090c1f090b030603070b070c0f0b090906040501060503072607020d090806090307080a030f240b03040f031413031505160801180902 70
    0x1500a008600d01510040303005000a0000203000b00b106104241880b4903180341038008050700e065070016134424090b5070f20200402d1420742e80041050380301200c45250050381110030001002c4251594621003401d940d80005800341c041503510590540010200b4000e9100041c0a0408180034000481c0c1161380c9010007441030145401c03640250000007665031440c103160780d640d6000030302178804200c1d40d894507900802500010700540c040204c0c80d05802e078233171a08400d040720791141003404402824804030180d580d018041c081b602045c8200310008090401065440c40740ba1414040d500d00106940c0d1000c40c0e501c01c218100034180d0382e540002c4020320350720441c104082e004407403e1a401c0700e41d1060500800f19030010070004030800410001401d01c920743c1c143c0c2076150402142c00702c00120b00000a003e48448014514a90302e0b0010030b01818143c10041140c03005810002071f1550f04142829a40d42e458a002241840004022103d0010721076504400844c1001810060715400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 205485683 1250 205484433 205484441
    0x3090315050103022d06030603010e032811070302130e030a020d02010e12090f040b0306090105010603150503063c0109140f0a0506040f05250504060210110d 69
    0xd181080d41c520051045050180d0003256804064801492440c505103c0c0701d00351000d803c0c1ca0f8010040800480e80a4509421210401d06401c007600d13180c1940a9034520710503000c10540300d242100d02c80c68030085029582502c0c0c80302207203001e0400e90f03003141c0034171000b001440b00c8100c00d560740b412014103890092015020403142035025001e1105000070082c01c4d517140ea190032000743c00030105400c008011100b150302c0d684047d50601038071001d100004005140e103058040e01801180200300620700c065005a0503030714107403410800e400c80868000c2803c1d01c98007803d81c140c0d1100e0041418400070701004480400304916020b5640124501d0015182000031103c01c41d441100040c070075400c0798018441c1000b52048910207030301d0000400d00c41010b002d090806c0c0c0e107985001241c5947c58680244629540144050066080590345d50000c00c42160300e0700e4505e00104600401c0c2c600c00c07402c540c122403666009220714440301c62044010980d02160100a050401844240c5602c60003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 205486933 1250 205485683 205485713
    0xf210c0309010c08010f090e0a05072903010b090105030604060503030a0306080609030313140a1a0105011106090607180509010306050711120d050a09060e0606181b07030903 76
    0x5019512410035804007401c0d90700c040080000e211081006100ba011001d24590441c2d00e4564003040141014442c0e03420282e01c903001801a0054901c00300e05101e209880d5015000310074081c2d03d1100c0c40c9049200d0030300080c0103442d0700d42c0c000c0002d05c83e80c0d0f00c540b000e907401c03200050000510503610300000303203140e0042c0081404203403200d00801a1141c00e00030680d00103007020286142d03250a0f0f034851071100501200501c641c41703d040019540108000000015600c180c3d42e031b2000d40c6164020400384000d101c1c0e2400120640e42d01c0c011100041519805100540010302c038645130a40d0a8805070080c00403500d50040e81000000d980c1d580100c3c86000b140074200c009a54107200c40001d00203018003001414a90003d480411504411012151385814948001a4940303520705c141010304016800544118100081650810004110140074080c202d8140c40103642401211181600031900c0204551201d4441c42ca0341003c0c8004201c1c10344130b07150030700e03184e5144c2d030701c00003001c003081 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 205488183 1250 205486933 205486951
    0x3030c0a110a080f0c0d0c1e1404090c0311060705010513021c050d0e0a2c15092406031608070302030c0d090201050c15040c0b07080f21 60
    0x1030910049401d1040102c030142152402030019842603100706541e888004030040e00030070303802d0164824004140303030b41c001814811140b01e15002d09441e800c501808180104140914411a0b0382d01501c3c1c24800c001c20b440d03001d000302d0005da1842e100c00700803032640607400303401080c00c012910005800784203c0b440b50030820150303d41004140180284002010814480d00a40240000110340001010388100c4240c1ca000d904e040d0011001c640d18250590051016041c5801000304041031240c250f04803900400b421141540c070244110308403000031901503001410403001c80c0101808051300007009070f640740c0000543d00e0a00c0840d059030710454040d42101107800f0076451041d4446ca000b030304120145819400c50501455140c000d20038008400319180d590a42081107900680c1074a050003000000d41d4800c004031300e0408040141201c0841d15802d41c4c0c08040703511224102030b20800da0f000340000e8105100e1039404034599010401009481034101502c076850300c255466188075407210 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 205489433 1250 205488183 205488203
    0x2070b16140a1e0212070c0f08120715090206030117010b0114040b0d060317041502060705090d050c03100c0e0a080309090a060803030703020901030f05070f1404090501120203070e06030c0f03030c0a 87
    0x20605110102c440750b0001d09c1503800001d8000030404805065403c2c103504450f20040122420203000002c201c20703c0000e40100c03002c0000a2002202c00c105882c0100000092121a6010300111401e09000f00e49244101c024001800a4820300002d805580c0c801000090350588039103c030f8004441c2d603000e03110541350004041c00407010000380c480403803244c1e0004183c981040341e005441e900500010301e001e0080d406292061040401c40070480f42c0d40542502c4a4000d00c812810180c4902481c000108014000400d4141400020141210500e10196003084444130410104800240030082c500c0c3c8c0b985400b00d80c040c4188020750095031503440c010f98078160100090103843c28401104e100519280070407036504c0c2c2204403045110342c00c0c501000d182d848042065800e02403a0409500e031481e0100201d0307845482039a003080e460088013203034080c0e42c0d0740e03040426001e000c0302c2c100e41540103030155500c03500b005d80b500d01c02400c004003903d0802040d82442c0c0d01d0300040c801c0c2540d841400d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 205490683 1250 205489433 205489439
    0x409030f0f0e03030f13060804080412110d2306130b09030c0708010203061c1203020a0c05030403050601061107150e060d0507090608090106060203180402070b16140a1e0212070c 78
    0x101b01250000300041d0030200c0880c60b041d11070f4003072400b440c800c1062400c5051381b10810040021503080c110038004004440b81800ca051070a007003e051000545107215082803000c1c0e5400029000d07200c0d44080f81600d50304140396aa2031079000c0042e010740c03500e01c4244000c541201090040b40c0140200b500016142c1c5800300070040c0c01000ca01e003032840320f40205144004200740c0c81800d07a08045030700b00982d94011f29207045031500c0410f8005440750201050100410602046113070403600e1507902c40404040e10340780c00d6101c080510a20300100c00c40103104980034003800c110412140001c1c070a608041e030f40c5c461941503600499070413001600c000024081690486ea0254001014000030401c082c241100a50740e8400ca201881c0d507021215110001c965440d0121945030b80d20400318503803800e04e10040000c0001801943c40421070f582d00511140c5001000d23220031202c0e40d80c504140c0c201c07015030086c800c655085030400314001c46944c4164210f444005010b0303d4403c41700304001d0340c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 205491933 1250 205490683 205490707
    0x708070b0a090b0403030c03031e0603060f051f090c120203070215011a0403030e0406030f030503040515060a0b0a020a0507080a05010b10020303011a0913090b060409030f0f0e03030f 80
    0x2c58010803a0000d041c081400480e070b106000703400c000d501d820700181101d01040c5986c21402c14071044810107040c4900407080042c0358003c1051041e206105000729280c0a403602d1032118030145003401c800d14903104001c51400d80d0031100540b080d500b0722440100169034504143c1c3d208892000140e8001c0d4050401e18411411460041c82a0070442800c80942c2101500038031031880090100a000076817288030f541e032548410011a84803080c503000101601d0058507030f40007218141c40e04d000e10555800d200400000941c40b42400500c1c088645003001180a031a400202228086100707091403500007544c1007100070050410307540101981e1665103881401d41e0b011001041c021f07601c0110518400343c0010036281501c584202c01d0f0070100405041e00c41070300640036240c0d40002140c041038419445680f121884c1401031a02c2051540d940c0240420f44165140041c00141c0b582c02281d03c00f07104500f07000c203c0d21b02e4034000140e09880302c0040d2568100542501107608006462600343c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 205493183 1250 205491933 205491947
    0x8091c0b10060f18140a0906060804050706110d05030a09020d030207290306240730092c010305030c070602060c0306040b040e0d03050610030e1e0708070b0a 69
    0x8100d280c0018001c60707260792014034180f54400da14842e00d40800e045c0140d0ba40c84a08000307020303ca0310030410300d981e5810081415a09a406617020b000d0858007003102031141900d07040d8200404020a40c00e0280c1030201c41c41d50000781100d04080e901c007600030051392804500340840d0300039030042c131840c2e0a0410000003030300345403a1228500d0700da000d400145c0600c0d009495004d1f0781168100442d90075241c0030b100d1100038281d031540c0c0b11030018900b010003541200141c9105141c144040c19407403c1940c07041c05400030f002210204450100c10030242c1c0c41c004000351840c030903041424091003d08080d0b80450fa00703070421100c0340c00225601c008800100310b02030003011544000d0003103007016034800e402d503c030140030329000e1034881444030210348a680003e0150004641140c8844902240c0140140ba0641e50144180350360f902101c0802d200e401481d45415644000d008030707156558045006100d0010300c084240600b032000602d400c42401204014010810516520411503000034010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 205494433 1250 205493183 205493207
    0xc1505122809151406040c11060a0519021804200a08090c01020712030e030a080307080402030f070b090d050a080f0d0e071508090c130204091103010308091c0b1006 72
    0x83c91510100c8460114a190303a20b40050040d603000601c4608074004407003903a21a1109030349407041205110540e021030384200e1188071440c1c10301c450310880d802e112041c4d1040703110011011001e4454141286407903841107085180402d0640c800b00200441c80300240c02040d1001e000c65003c0c03003000002d44080c8001d941030035091000d40760179401c1c514082d00385480d00c0d00c054100510010b06282030f8404215500b0b10079080542c0c07903220328054400502d0400e040718128080d0180602c032541c00100050100c0c281c9011681040c108032040701440b803903501c1c08109498510541c0000c0d008180b900c1c000340110001d03030612540c1c80045958100a440b02107204841d160f0246100308100741da548901d8401c3c04a07860004959124400c2082c541350042c2241e56000d5034000e05070003440f50070703401002214000c0005100946a40c1684c140d01d000c05d103c06000c140c0100480070300d91034441d1a840440c9510014031030110344545801208050403101c0c9100001401c04c284a103a80100d01c1d0807030b07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 205495683 1250 205494433 205494473
    0xc05040204080d0507080909040b011502010515060d0209090103050c0913050d050c0a020909160b0c1903050d09030e040f02190e010e1504030c1505122809 68
    0xa03040c80e1401e281da450440100f04000c101010403800d00b0424110b04850a42c00d0041c59510141007608000803460700c02c1c45a1111024041f401c006454010301419125403c441f54641040d0410000e104540d0f2000300e00c03211142d400c0000c4c800d00d80d100540b06010358002c5008081d80d0000c1c100b0300080400280904402141d112085400101c002500400c612098039001c1d40310f07007070058158a04104070350700035480000f0388100b2890100005e1559601050449607850056440c038602c0401d200710381104801d030304072270341100703c9055200d51416000d100f454210710f400c03402511707a01141d203045011000202000a00c948600d0f190141d0346101d414504110715105410724026007a4034404450340c24002104540c0b00c5580c00740d484192040c4c40602554005841411010350550050104540c50302c417101d00400c004c80f01c0d403094003c440b1640c403560701e03005803520002e1128000920507540d14405480140c21198420140c11481d0070380940425001d2841c501030818401c9140101d070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 205496933 1250 205495683 205495687
    0x606090b0a0b03040206090d0b090109050d09060804080a110607020a02010e0f03031b16030503031905060312180a062102033912070206010501140301030b060f0310090c050402 77
    0x41460b1600d41103036000399045403959568404440415410291900c01030080301316882040128101900b00c2c1c3e452512a6040e44c8039100c40c090103407400040e60203140001399600001400182c004c0c402000803000d1400d1450701c031b01e109070645281400868040006030031240c940003c658005000d005c0ea600704450004d041d0840ba00400d640f4003500c1c0741650590b840043c8074450240610140340d0b07000c0f1070f0f910f51100c25100d0030040c5c2c3d2940700741e960078001184041400b15002152041c1406404020f02034050b640c0c0798041e0703440c2030700020302c9074884103007055155425960303103110480100031b903485082d0350000303009004001c0d078130401e403240c07a0600401c1044035281c40e0011100f80f41b8a844048900800c00c0b0a01d40818401d008140480c142d001442015200c0f480e040300e803254803a60300b11a181c0c1c1e220710044a0694202440000d014020302c0148001401c04008a600c00c101806101d03014448900092400c107868684000301580c81540001780040c0712012805040c1c1990158 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 205498183 1250 205496933 205496939
    0x106050f030a05041403041e120b040206030405070f0f0305010e0705100513050d03030203040c0b04120807031b0602030a060b03040f020103021e04091d2a030313030606090b0a 77
    0x25000740700c000c01c0d14680030f035144006010003204d010f020300c034004494100e80d01c0da51070300032841084449505228100c4400c070310001d0010900000710704042d5025034400696202ca500b800011703000500221814044c0c0000890500020610a00209055032086d0f504c80e241d410240d003110304880409005400401043c021510707130481c252840f1f002407502c25a200c805401103a00e6402c66001b0940c0201302d081079105041d40350b006035000714001c9481c1211a95102c0302c0321503910031441031220140414502d00080361040001e482428003a040218229054100c400b070070059080048940560120510000c003103d442a00c3c081c1000f80d880504d5410941c9401115400c0b99100070704040d0002010b04100b882e29604e0402e8109641c6815141c6454002c1400901a203c103000c907284030481e08070500120008072454408012200001703c1c0446c070302103248412000114a81522080281202d070030940803050f40114002c4000150700d60a14034510195801c19612903c100d24807c418 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 205499433 1250 205498183 205498207
    0x30f0b0d031808010905330f0604020714010c02010e0d020c060f0f07140709062d081902040f020901051b032a0c0d020307090b15180102010501060912030305190c0c0b010605 76
    0x8281c00c9510110b60500d2581d27042c00160192003009402440200a404603801c45801500144858201600244900018208a159030311000c0300c02100680c08260f03481600e00f0100000d000d0740e1a440100380c603045001c1c05254256000038000c54040c894019180e034040c10601821015084581040c4400703407400340404482400e2400c1d0030340780c3c0315040720f80200944a400800045c0202c40c10303242100c198031a5400c0040d8000340590185060581340501320030940b003100c00800058460504100c241c4a41c11050904143c1102c0b0380d00c410080c0c8441c6071050f00d038240c1004651519080d8920301400e120b400d10048400c110f019041400086005070350100f00380b403c1d5040450005880038228000485500c900c014020301c401000a80255840720aa2035107602e520030b1b00284400c1c0d81e03501e421103100f40700e440742000080d003083d00d00c0c002074401c4e0403198010145404580c0700c2622b0360129400c66000f00c04110104900051032010040b441c503005005120500308142882e040d42a8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 205500683 1250 205499433 205499533
    0x708161b0f05040b0f09070507060c0806130902031011041403031626040306021b0a02030705040c051210081b0a0e06031f020901030f0b0d031808010905 67
    0x44500c01c0d80c49402c003140540b2240448030b17054000a084c41310364104042e02038030590003d035080e11b0050a00070001d44540c00745d90b0007801914054544849108803150301c81c01449d01c000b0407a854000e446131800c0d1400340740a00444094950b03c907581d00c40c500765868140790240301040d07000c0d03081402009040c1c001c0300300d02c1c07903440e80050803400340024480714291589115491050200804130340481842101e60182801c4c100300c00b140d00440c580d0701c0310f0039500d03034680b031000b503159000c40c00030300660801e81c000f801e2074590307400d20904200155400c50040e6200315952598088007583c00c0061034810040e4410046500b038600c00e802c1710340c6010505a01060280c103100f01d03001000301c0e402d0b48041001480c50000c0d0b4890200803521821060080d52085100e1400039042c40040341c41d243e000e209504d240d03103008010600c1d1100e165400d65501180c5c00d101c40f000c409076200021900c0c801e0140d280103074410b8005d40000c84c0c0b1089001c1c14108559480040b006211074202e0000b050108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 205501933 1250 205500683 205500689
    0x60201050c07230105130210020f0d030e01060e0112050c0105033304090c050406080f1005100803040602010f18151e0903020a0b0916090207080708161b0f 68
    0x4002c1041200c4a0703001e001003000d60710700f00415031800e010040042e039040c00030038003503100300d42c0c00c00022080401285c0d21015154100c809401071400b40c10618000c2c0d0100c50301110103000442d1050b40c0d103030b155000700002d0b441000700c5004c00c60450200304052045e064039001c05d0800070b0031030a00c000e00c0c61400708075102100100107401d84202c44100308010f82075030080c005100344107054480c07400540d0161640308090283c0d003021000711b4000d1002c90001d0080e01d241000300840c020854841014101c060316a0b024880c1884020822040a00041020340101e40000c10842100c0f68400101e405405000072128060f02c201c0300011920b00c158a00081321840114400c070100c0320170482d100c54000e01081243c0b41c9201401010740200e03c3c1c20302c0e0fa004a400c40c00035a24200c210746c46004d14001d2078102000b1800034010b001c3c49901501907540101c0c0c031141444030030b584000f402da11010140065081000c000002c01543c68001602001007101604180c0d20f010120901c102140c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 205503183 1250 205501933 205501943
    0x807090b0a020c04020f0904061a0d0f0e0616091e0b0a0324030302060c030603030a0c08090901032406240e03030d020406080f06030604151409010c0207060201050c07 73
    0x50907100c0507100b0408541c203035500038821552102002ca000009600c4031041c41d001e98208040003a440c0c0182960b000c824018034003080c5002000c0c1381a40060407445600000c071940d070340c0b500780000410400c2510680c1041200388580c0b4400340050f0035220a80c0c00702c3c0e850310740c4918841c0c41003031182c1034208039554040308a48801a48809601820100c00783e101c0300d201f004041600410300c80c074110101c80c0070380c00760740d40c644441541c5841c0e880b08599881d0550700c1000050551840740c00a402018050070b120b5080c943c0358000200d8228080c0c0c01a0b4407509025504402d0f4600c0b0b41c601c194045140b102041100e143c0030092440c5180c2601806011003000310210049005100809030580005e090303a80c1d442500c0050303002500700740152800035001d040080c0050704030140182c0070390001801840709503900e40d43c8118031004035901a81c038a031941825840040d400803194010390900c0000716144180e414020314003203565221004581c113041c1440010a041400c13181155000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 205504433 1250 205503183 205503187
    0x90501150807110d0f0306121a090304030510020a08070507030f1206030f210504030c0e0612030c010b03061006051b0c031203040b06060f0d150503070e0603010c0807090b 75
    0x2e900641e11102c1410000449025400e89622229444113004411400f540c60401c841c6495030540c5002c05061000182114041401031407145002081c03c2da0210f00081103a1815440b59102c40c2044a20f83c0c61203030850700070034000c3c6500e8001003900c1e4000c0107440c04909044050724001e2542000c030b1581020f11103d40302180110b4410341221001e942c10640702c400c2024a07103030210100c821109468000c200703410304861420701c03079421241141c0d0803200c607552031410111a0b20a881001c2e0025a100f07480c0c488055007801e09002030301d10260200000500e041c0d408003454242000102114a214090401070258503001002d6030311030300041d0fa030980c1080b910148140340c40d43c0b207442641d01d8810075086c609204103070002148514450680f00c81750703481e1842030101900590a248482e0320b0103000007040211a54801c2c4100c01103640110001503482c00403e0401e07040e60803001c43e80c0507400030050681403d000350201d4403a246400b642c1d034038103408010500402170051181d05000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 205505683 1250 205504433 205504441
    0x10c020904020a0b120f01080604080a08100906030f0209010504050603031803030408031201080111120105010c020406030803100305011a0109060804060e0732090c09120d080f010905011508 83
    0x183c911000003510140d0f40081d40d540001c2410341e610141200d02d400d1400c0b950001081c651804294180140d078400400760400d10314101c10b81c0c0d1488020400c40c1c40120032980000c068103240100c10081d40900c810703009110031401403045460051300329a00940c100410320103075450003c12143e881041b4445900e18400860000b0f08611841d0b00842c11840041040c8003d00741c00601603040b0382098000304610401ca0300c400d0810302801c00070030000e41d200001084994040c09044520910061001034540d460f86e071a810030b81c00039a4104602c08141c14284104102441000362a54441c3e0080400000901c0002c00c1d200381030144004102c40302002c64100846600300740180003100b4240d6034400e0f20f5104c2c02c480942150042c0c0c001c036040100c5c3d07074000039510300348440300741026017428410340d20b82ea0a001c065108207055900816124103096800c00140481e00601009a40e0300d04941822094003d60070380607045060ac151804004200d4409203112102851002e82090050341e0f0b5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 205506933 1250 205505683 205505689
    0xc0519021009060b0901060c020d080919030303020a09172119020d141c0c14040803030f0c0a0e0415030b3c0406020f0c1009110d02010c02090402 64
    0x800369501e5194100712241c4200002904000d0307903043c040e2810102d6a07030b600c00c01c543c050103c1d031002c0d400513036181001000c203003160b0080035140000b41081e0381440c200ea0aa044020260f401030300040d1380800c0c40710000380d00108082c02041c90502c140c4014481d00302060300d4184003580d000403482c0d80c01106007401c180340103480403020904000502c0f8000700001948130f420000c4c26a002880b0484581548048201900c10011802c1c847d0302c14010b8903503800340241101c82507841403104c00b102c400c08403000c480c01000038040841c081d5440703041460080200c04c0b0050300b000d1101e6001c4c407460404540c40300b0400059802200c0c0428001410319103104001103d40002d0304002c49842001016001e5046411400754264075114080103c100107428070401040c02c01f804509110226000c03d1880d005040030134006101c00d07180c101c0c2111601c0c900409407110701040c0d9283d190f05424056942c540702502e60060320081750500081e80020f150980c9010000d1003070b138a03070f008282592 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 205508183 1250 205506933 205506943
    0x303201f0b130c090b03040b0f0c04230316060f03050c04050d0302011d1b010e04021201080d030f1104030201051b01020a05070203070801060e011208160f11040c051902 74
    0xc00a055a880382c0d80201c00c2c040580b8040e2022000310f44009000100d820540040782e102d650008074000098544103000c1e02881400381000c0c040000510022400c0907013110145040e0481c8800f840100d040380c4140350521a4503d2460448603180f0410000030f070f0800712448800c2d03450b1170006000c2e914014210f803a401150001a003100b01c10100000b01901540448059a1810517130031603c0f40180c9020f40d129405075000c159228108099203065004d40c01d1884c8681d0000e2001d8280b0300c5840146200c1c01003640210255880244400c03403050305032240341c10310400410300340310740080690015018032031844000e04202002aa245000300c9100b000711030100613100940d0b13601c0c4180c5d0002c0094005510580c03180c0512100018072600502c42e0031b08880c03580030903140581c039120b01800ca20f2203040741621140410010000200400c50341324130814407400c00c1085800c11400c00942100c9030a8560380154a01403030702c444c154101054400c05140c0b6030200c210a40d104d64101e00385 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 205509433 1250 205508183 205508201
    0xc180321120612050c0f210a06020a020a0b0901020301080d05070303091401061a0c0a080702010c0506012403020c060118061802090432040201030e0312010303201f 72
    0x315150450104401c0b02c4901d41c80243e81c0900110340000750800100712003d01d10504440e407142401110300200085a40306882c03200c007480c01d135940316015445103026640022082c0c070040c0c12030400801005134014a041c1c00214200086017150f0400440303e40d91007003c203601060010104441003007500c241c20a92000b50700401e0b10034000c1c011a9114042c5c00203001d0910041480707814002da200750740b015505034076003050040c222220f0607140e8482d0f5500c400020383c10008020045c2d80403810400406000304259001d070184d40c0018154500416200d0100307000705401009074200210b00022000d05484294100584c0300e402e040c4420700828859102d1070349070140c10000307420407000c0d074044c10004805481c01e10120101100d144000580480b07060000303401740603403e1548011a14187c3c0c0284103040008010080d074002500d5504003030603501108006400600c06c1640c0100031030f0501040c3c0b00102d41d071101408589844201d03035280d46803d02c0c0940110f00c44d1030b0181c5c200c5062 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 205510683 1250 205509433 205509467
    0x315030510050906010504090b0f060a05150910030501120201120f0e0a020f03010513060908070206030f07231b0c060307170601020c280b0d0c180321 66
    0x10720822207188040c00e4215509202c5001d40e80002819040c240262072840380d020000303100c103540301ca9403841415005403040341c020582110208090711160010324001800c410b0702c0e501ca030041c00070006d000070700b10550820103080000400c42c1e00c140d85070000300c003682400c1008000c2002c8112000404440d141100500d007455920000c251011502c0003c9500a6031000103400106040c5401d84a050b100c070850206c0340c00808000c20000e90040310080d210b1f2a11360b01d0409190001142a0001d90712444004c0080341806002c075000829410b24038031045503d628000b1407a00b07140680101c0c0d004111980d0070880603440e00b5002e200d01011400300520650316030422030001130108070b038140d1a10507071030204040f910179030001440300d160a1000b040c03240e8901c80962100d2003500742d4024149040786901c800300d5621000c3c005020740080c5140000380280b000328001701407034002e80011515a00010041c030116805a1014001911041a190307120924520440d080e090007070180c04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 205511933 1250 205510683 205510693
    0x801151d0d03022506080f0709060c050a050307060209040b09060a15030608010905030703020607021605010302070f020a030602091302030f150a031b0e0105011e080601020304180c0807020a0803040303150305 91
    0x480700b0030000604c4141c50721641d032815259a4029074045009040d142d01011415441d420040395114440b514000c900c514103032000100540c1e100303881c640000c00c0480d0b100d50003069076005400c284c132903405072400459503528641031000100d0080000c0703003e2401180304001c01c000c0214000e4000000614580d4001c00044084d0300b80300e5180c0d04404001c900600555001c02c0c501c030710000d0000c6041c41503210600c2110f1030940198025408181c08a401701940c9402c10f000da0f444042d00801140600c5000d6695103928040041041c1803001007110507105009000f490b41048040a502681d1040225200010000050001060303544011b00310520941040c2c00328200c98034000460300c6050050f011a41c0741d50064030103451606101401c1000350707801d222280e03c01c071841030b003142041c01039074a06a200c1d5824100c021407800700030b120545070b1816003610741d884400240d000005102800c0c141c00c07da9107200c1c440c88003a01c040c0030540c80d003181e5500a018170f1440c1c0015580101118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 205513183 1250 205511933 205511983
    0x13020d12051b0c12030a0906180312021c050403050c090c09030d21050c19030e0d1e140d0203090102040b0703020607031103091f02090406060801151d0d0302 69
    0x3d03910008502603d019881802c07043d02c420800206940c2140e6844d1690b0800da42000000c41e441118220444a5850140b00020128050b0003000c01540b00d66030140884030b00d408000c18005421aa412040010801c01007011036400f00f01e4262412084560781520344030101d00641602504200c60343c1406009404810b580d005041800d10b0344000091011094a49445108072081203510340349840040000c401032442c1260582c109a4860400081e0104a10f10300b500e016850b00d00d030030200e015002c100e80c84200402070403000c030455240000703240b541035070040403d000d081c0140c0c0f4119000300218804d20421740503100134080030040907485a20a04000703690f214280c9074540403d24080e1207010120656084a100f146444020300709a684080c0c261030900002500701c258503070038040c0908070750f102d024940c000e003040d60726a002541440c0302c0c00700b10448091b000081c80710141c1e514507078201440004589903022114008400001d050581c04c0403082c8540c403c150a00c54000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 205514433 1250 205513183 205513237
    0x30803160e03010501030b01060c0201031407020c151608130b120612150c070204060f0e0915060f060702010c020405092112130f06050903090913020d1205 68
    0x5100c54886698600c0c406210000905007269803c0c000070f000c0e0b20143c030050003924054049052000e1061400054041100c0c1201d5480d103030580311100140c00c411084241d40c50150038184038144240c0126240ca000038501a6000c000340074000e1080002284005a24413048505001010300301c035125540c0110100c00020507000701c40e110310812080f040c0e841c10300c00c00034070b18040030a2020a40482c0c2c8400078407078841c2d041146d00b284d205481e40350204450340c0b0009800010500f44103c0407103420500c11550810b8520300408840031042c4080019656450b62000c00c81801034038811b6484500e400101c501c5007440d84007a420505180c10b01c4a080c6000615002003d009182002008000b90740401030303118081e40040c2d00f4080d0340202d03002000005541560328401c00c00c0300e001d00c1e4266114026254101c03a62120b03034001040116190070107000e49544440903030104100e02e03040b940024004036100801074000c8030704503a0300400c213001d0811210030585110500c514801b5003994 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 205515683 1250 205514433 205514461
    0x14031c05010513020c0a030e0a0b0409140603060403082404090c0302091b071101200706180608070807021e030702031519050603030d0e0f062d10030803 67
    0x50680500300c15143c41004502d43c0c42076074807030740c040c00240020440c1c81e141140c1c0e80b070a0070300a942c442000c603c00100e40c0c40c1c00300140001d200201000c103054001442844085400a229034002d400c80001c1100090b48649031650080011016100121120b0004038185100c490362503000b51030310080c0d030248480d8500d51012203100711801d1280340d40704018071072840031102c0090b58900c0244181c5c800540015480c5401000601d00032a890125050402c28031300341506a210301d40011206010b6942e00c82486000c2d4240f445100c0c282a1520701c004006a8001f003040040010303c1000c9103005200381310301c40d50300661070442607950840f40174103a2a94018102240301c0e01c11108184003104031700e0031407807080018481c02c0601c44200105400504002032496a140c0070801c0201c000400b140b01d0908440c800100400450b0901c1800516058000d400b1754140001280b020794040716013130f1454440c52407100010034075210801e0740c142d9106507030401040c900d00442001248041c03400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 205516933 1250 205515683 205515689
    0x1902040f0602210f0906090f0612040606090c0f0c0f0210020f0601091a221a13050c0409090302030405030a0516090c1403150d030e01030b030102120414031c0501 71
    0x40740100d0311610300c010039114483e140c40b44d0b01500082c40072494030314144c0080e0101c0c900181030b060351415200d00046265101c0d445074072400700710034203000511005124440c042c0c000410204985218081d010b8003184104517141c0c10406041442010002ca5241440b08180d0140c208502c540310f06401035204d5100318031540042c4900700000070002010f02800e08a040020b01d540c00d44880241800001d891541d062000c400c00d160180000242c0e40c031032030281042d152105021014108108441081c04184003000c040c02c000510010389203200482d800c680c1d83d607c00154a00061074181e0842c001ca1340640d0307050140e11807032018080d01140b000400d42441d48240601074039219140c04a0f50002c0310380c000150400480e0b5030f6010f21000a68115104108482161f00c107007000440c0705400c5407045001683c0078007090103650b0540104002000100e000354180f03400f400102c424444d00502c040c107101c40b10304240b4420403044c02103c00064042a900b02103a50704110907010342000c1c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 205518183 1250 205516933 205516963
    0xc03090317193501060f090e01080a0309060c020f040e01090203010f050406050601080f070305100302060705070810110f0a03090807030804050d08040521090406060804060f020a081902040f0602 85
    0x90f203403442e0700501d403e1602d410150b8141d03540d0f1070b42810401c17a000c116a0b01c41d102804041c10001c68a600700c40c05450007400010020180411740d89802801c0c690258410810b020840040200594425603601c0440e40d0a40f000602c0d80c400500b501d0150480410185d01946007462078940c4411a0b080a845180505c00c28009621850011500210b00b12810400e0302440808252410305c25004143c000c0c9840303038103804035a02c81c2c0014000b64800d500c200e030b03181e1201004111015042c05002c4d10408140d00c00c0055240d0022100010311564292903603900001900601c5180254000c0c0307505070f080380038a03803525641c0c078018020050039030341030754a2300c61503840c03001c042c1c410040584a01c5c0c0c4480908070450318801d2000760110f026803003420400e01801481c5043d00e452080358010007a59886000c45d04050030000210f4100304141da4446004000114000b50000343d8640c2107504803d0f00207040700c4000b0440300900540e0401c509089290300e001882941c00500c5000e900c07094 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 205519433 1250 205518183 205518227
    0x308040501050c0a02060411010c0b07050d060f0b09040506040f021902060c210601021f2a0801031b150305090f010c2307170406020d0c0309031719 65
    0x3107481d010050040603040d1300141d010400042c0018480403128000607410304010702180016640c84501000489100000500c0803e0114543c520340c043d0310020000202e1000116040c0304608020b4400d81c11214080d503220408607800d5103035540502a4041320420464440000d04401002c602150003204010f01c90b2401148000c2003680444105109141c05100b0964a0030410a19084018106030550043d840b44d811200410000325800c500000c40c0000d02c03444200a01d4203500c4000030300d020f0038990048004017140c100d582c85040d00e80201055500c001d40305642400600b154105190f481c40f044100301c0c11a0f0940c119500808214098404100c90790500a00305c40141d0501400620701c0040c4240215040001c202003c0c0b4229040389090090703114026519400107040074840000035041059070780c14070031900301d09500e1030309900080741600c004051411500010f005003002e032018031460b03441c00b01200c3c00e42c400700c0b482a88000e12030001410001440e280030542d0049 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 205520683 1250 205519433 205519441
    0x606030604020f0d0c05042d0e041a070e010201110705060a1104090603051501050d02032a04020c0d020c01050a0f0e0f100806040f09020307140d021203090310021603180f03030804050105 82
    0x1004c8c403000c00082d1b451040c00840e841c114214403030080281c800c0c1c07484104095410420181d20340c030680314101a0714ac40349600000c400090850304852003d52980e9407d0010f5400560046440e07508001070361400b08140d1000940d0b030b00248500c1d40242c808614040c000400c100000c154103902d501006c42014a40e0398800a00c4002c14010b0702c000d50613002400c1907942507110700b109002c5140d14900c0b021281e52181d0105040340e00c030711004240c2d9802002d030703590010f50400107181000c10030300c1c010f41040b400c440701500d1680c0c2000035009101890744954100e031518540d107003030080010520300c860041100b002c2c1440906581050040d0f08110301c903c81d409440c0902550540d014000303040f41c500d0405140c2000382a910001e030300807101d002c1800035030f985401d9232a018481b8030145643d140440101172030454042c801c4d810060050002554100a54110003440750301802c0501280b544c4041e9408038050a030020600d15900c90004400d159010f100c09100d80d10800003001180c80d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 205521933 1250 205520683 205520729
    0x915090901060e0f04050d122d0e010902010c031b0b25020d020c0d060e010507020f010b09040c0303080a0e01050a0606021b0609010c0f050d170f0606030604020f0d0c0504 75
    0x3c401c60380031b4442d520018001540d248104040d01d42c9084101000911401860444803103003000044100c03030020440354802c40048520840900c100c10f14020448a46680d0000e071401740c0e03070701d00a8240006011000c1c0c0300d10110b1080c814907580710702400198544440c0025804e0b0030180c000c0ca0750300038850b83c40c804500000d0511203044c3c00360018080301280c40c040003203004112000316222526004061100a002d000341802000356801420041540c01c420a0071612000011445103900d5801c0c003000c43d208000b00c9058136018904007aa03a0342d01514007021f407009204509c015880c000411030894002d80c08842a6400384c5d00342c074044c16103000000e8108a135221400c0e80207104001144d21903000707a1111900b54440d103c0c1e1040851aa00d80c00c0c1880b485050040c0880c0e0440d820390134150300c00107604d51024000800c000a030030400042070302804002c10190007564001445182c01142c1070030f80e00508000fa40601004162410041407038001d440340d140903200c440d081c03240e084 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 205523183 1250 205521933 205521961
    0x61c150216200604150504080a06090b0a02070c05060a0203070c03060b18150f030f07060903030e03061302150c010501330c03030c050c0a0c0f080307030e0915090901060e 75
    0x82c0d002000d0604041c10100c0400b0b009411450140600204000014290b441800701d40000c500a12000807e4082e9042c0f044404100600d9041030301e10410801700010404001e00701502e006441e400e841d8404280d007645544503501014041c0c85059100104000554001c8032800e18180c0d094002861030343c4540c5035154040e16600c01200d5000a1603409050015804c0303280200102161810240030750390701d0600c0c40b550000c00000c1e8841e1b600740141038201060f0302070190309800401c082e25040524a00e41c0c410004002d202e060340100c500000951038055a0714074a210000304001d580d41d0700f0381c0700710020300c200640701d00440040d103010183d5050307a81300b111a0381d0f4072800311028503554101c00518104a40a0501005000030f1556242c10080c1c609110b01c16030b020b014003820000b81030710b8011140d10104184c0d00812904c40040c1c0c4c05440b0141c03001e4103883d201110340f605584804514000a00705800074046c030100f03e0f000905401050840b00451041381036034955415007a000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 205524433 1250 205523183 205523243
    0x14031602120a0c020d030504030b04200a0b0d05070302361815060706060e060103061502030f090a031707060e15041212110c01060e061c150216 63
    0x200b800f40f0000e001500307008039024422071192130001e107484d44035924005014002d1328142c6020102d01100c410200003003d43c4a40c83c2000c5469805151074503c00700414030800003100c9010ba00e0b1004110f03021301a8069039408044403411a810071440c08486a1001010705121031120480c886600e03c1c2c02e04e18100c0607080c407240c01071807603959800c03c0d82030b04a00d41070070550005010458040803802a02c2540040c10301d0040c070411908244c00010181d44d883d400909001c0562000032525640002c2250100b580c000b188984505402000543c44129030f4406080704416450f0802d00c0305442c0700424040f80700c0c20b000c00080f0080003485a0710074802040101031800c0d01d01007800300c1c6400320f203616070a9241c500f2543c10703208040c1c0401580e02114400c041d54101045281c4807034428040c0c0005841401c900c20030610700940015400c408000c1d07251884c0c142c422050060140d084600c2e0181e041c00d80040d0759035807607503c4485c4580c003408410b80380d02c00e03070f964008e0000364070003854055 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 205525683 1250 205524433 205524437
    0x902070317042303090409060506030c01030c02060114150f0319060b040306050c071202070501020d030b1507031202040f0e060d050c1917030a02070f080d0e0114031602120a 76
    0x7540c0184246840ca1a43c006010140c42c40709220b103280c107035103e0040701c18440c0b0031480819036091007018941f134442c4ca84095410300d42000e905031200b0341d0000d4001d044034070700707140451903605480100706001c0d51000030100b10000054a94800d030600c07030007940600040d080d4940400402040481119058007443c030004d1420030080000c1051a084035400c4051002e40e180b800e05182d8809404002400341b44000d030300031504c1000b042d130701884982d403c01010b0605012401c002d80005410390b414042c828058131012450304145071282e94a01d5003204141c0085503101d0301d44c1000043c1340090f2280b000064400c0380040c1d05403d0600c074450b0b849a1020092501003444010400880180e00e14040030003640c007000605c55260010341000d001c80d1501455680172425002410807109800c206603070411721600f001103034000590b907030420540b407400103c82005080100c4200007540750100b041e80011051101a0300c0e1b242103070303109508039000c03184141c5441c0d16504241c0114001c0f280 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 205526933 1250 205525683 205525703
    0x10e1207080a0c0c0e09011a0a0e0c03040303060803031f090b130e030f0d020c010b09040c090c1707030b10020c0f04020f0c03070c03060e0304030c0b0d09020406090207031704 77
    0x40710501580d248a020f6205280e10141c49444901e84200b01a0440e85513600360344908189180d210390101d50000c0e1807042d90880015410000303043c641180c041c015414180000000505052003a41701c132024150300010b5941c3c1741071503021a1080003c0004000c032490a0f1480090000396900c0f40740012500030b02521000c106501c403d20041c05101003540b000d00007080080c00710582e1400038080d0a003038a030f0050b10f4075a820000d600b11030aa1144c18000d40d800c900348000b04203032072000300845001180110700581c19150441e0b1900d855a5207480c004051014082142e40680201480050688404458208208040b680c0301071140080c4c0d00708100003200142400c00c2e400412401c01034201c4036203002c42846110f4550360044200f42c501000c407010a004106460003040d5114003100020750a243c21600c805000101d5481403141031800022038464012543d0003a011458000b481089656581d400032800f85d1300c104d20881c0020007207644500302c0c2c01c040701d28038000d68024102034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 205528183 1250 205526933 205526947
    0x141015050d21170f01030209041704090c1e03060b040611070302030303010308031b040510200a0c090b01020f0a0f0c180207060507030203150906060c010509010e120708 74
    0x4007a40c01c4040c1a01c103035030030060002c01c40303074003801515100301c00c1d540d200040041d0b0314001c400c00d84043d0400c1300c680c20607001003016984200c0b001ea0003a0700007840e500030f99582d400256041c480c65000d10106410026400f5a283c3c00507004012040d1542540f101c8400d00301c0110111052402000001c4038240400e00140e403041040a00b00c5061000300ca40c000c0e141d030000303807071608240d0003220881000010010100880903560b101030601310819030802e401e00c000507800103c111282804c00c10325004180325402070030100e1002c4000302082c0c03a010016405c1150440440780504101b41c2e0404900c2549548001440da1510070780700e002c0c04c10881c3c1ca03610000350356146942551241640c400104e0019290b5048960750840280c0059940c0c0c03040c81c0a400b81c8a00502880a242c4140104913090307c21100082c04200c0c03c03101110996a8203001400c1030250381820110b80d8a84020032400354015800a04540d0800d801c07101c55501498035000280302317008000700b040c00188841 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 205529433 1250 205528183 205528189
    0x90f0c0801060f090b04080a020f09010f0b0906040323010b01021b12030f030702030d0501051503191d03030105190b120a1803021510051005071e14101505 68
    0x4643c40400510700190b80c0d580d10100c95000c1d801607041f0611903003081c1c1a000840c60110910515002e082e00e01500c03079850070110200c2807079a441202c0310b003030000070201c1940d43ea040494000e598001740c030344156480507031010440c6141c403407c00315035841d11711141d120358000100b2009000c20604510310f8030144805108038542c0350385400d40c0c80d02c000e0006aa8100062000d1446140c1c01d0303000b03580b41e01e603010751602030300c0041e80164050312803100d01c059100c0c040300442e6840300320415000c00c1030300c40d1617005004040c500c02c0351504030501c020ba01030611012000354107c8904407510502040350f98042d5052a10600c21201201d00410034540200006282d60340c1c40f815900b8005100c1c40d22450041444000900c101d0058000d5066540d1501e14070101030341001c10165111066414240450b41401da43e4078039009012003c0384400402c0001e2040e8604825100514155541240f800040c28010740008240740d00403038604008801c6039200d081011880b14990881662502e414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 205530683 1250 205529433 205529447
    0x703110115050d050a0204050405060417031314280605010e0105010203270d060501030b0702060c0a11031e09030d030203060a050907230910020a050d030b0d0b10090f0c080106 77
    0x201c4031350042110100250b96030f8860b140c400c90065002e000c0610303040c0343c42d400023258008405c9468809105020001103403c8500022642c4000c0d140308130307560058068600719152004511780f0400b12400c47c440007140c030440203503500c198814402640c0303a5527108030104090041600692062000386184e00c07118104180305044040d240586071505400715090814122003500d0490700e0f00c1c010020003200c0340302103a0001d5144098240750030030030440c03001486022400b40400440b00c1d01c0e520b54440034030459145033a10b0110008e101624411940c02c0d80010b05040d1080c01502c1b10700544902030300840e441400010703e4410784034185001c208040700058801d000308002d030121156142e001c0001d41280c114407050701500c0351101000c10016850003a021011908400044400a600000e560788917510504010865913800d501003520003d803088003509a50082d0305110418031400071503420317141c8a00c4188050702d006d41d5400103880f6502d041400081407800100819441a08 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 205531933 1250 205530683 205530709
    0x1050702060f04060806090f040c060513090905010b15030c030a0207060609020d0902211002160c030b010f0603020405031011130f1503060602070b0c030d060803070311011505 77
    0x20303051982d260202d040a42003500a200450480800d00c540c030b01c0c3c501107495001201021100043c5440d948480d1144458460102407140c00300f1034013072881c040e040040c060300c0041001c10608485040041c080c20502c0703a0240540b00401980d80c617241d00e001207a104c2c107500d03040c00d85503850303140f018402540421741c26181c182d80d94001282c183d8170303400100181d240501c03001c59984114010000d18180042c0e000c280e140c0016642c04003028049000306c8140344010005868400482c103985000107001001402c2c8080500e001c42001030480d001e905071424511101c1710b15480f420154200d00c83d90040e40e03032543c0700c4200400700242c180c00a040b0301e404401e05908041410140d404d0a90b800d03040007942c003001103006c3c003034411415800010782013103180c280042854920080d40b121040e01421001060002c0e0010140100300111200d110402b4800c02c4602d1fa1007001548a400c642000c5000400c120303606011048140110000d00019420b4844c101e8684030810140441f40b40e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 205533183 1250 205531933 205531939
    0x3060d110d061a150412110d05301c02030424020a030e0c0d03110c060a050306130b092206020c03031906030302070302090702030712020f0d05160201050702 69
    0x3070041400a10907002e0007010300614000d48108507210400c100c03006548111042102c0b0f001c3c0001c10901e82000042400f860f0090014103841030040c1c08111130a01c2311102801601c288010028005c4003a628031400c01c0c00c207440d03c00c02001400d84002144101b0703240c40c01071034400400c0740c8071400b26401590820712030508035540c840c03801c201c02c0010b540b03040994100381d40400c03d02ca5035038050281c0741900081c0e0010b01721000340c0344005a00d2402210300074041041c5151111400d0030100800020104000c0825455902c44031000b030007039100725011030080520410301c9840c10002d00408412003c01080e00d5140d940d0141d480e1410308490382d45070784c1d81202c0c0c0740b0705011030b0151004002da2802071001d1a500d1034862410319109131046c945440c52440c0c0701040020960204400041d240e0403102005c458507845012841e502032000017800707041816009401d115000a4840100300c00c14041d260f4043e80440700350703424054100c000f014020010a0341c001036100d00d0050207401d03c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 205534433 1250 205533183 205533199
    0x1d07180e0613151e09060e01030b040212010e0102040f0506090a0b0307020109020a0305070e010506040b04060c020d020303031005031c0203030c130b070c0509010b040311190812030f0c03060d11 85
    0x1d0352050b03028003c03581c494040030f8040d282615030091143da105000d071001603c10722600d81b4029400071320010510021f4240890b40020408641d2004003c01c0440b40c41030083c0325040890200c41d00030760140c8286010038000444c0000d45040c100286c40301c0040c002c0110319054600a44a1042e500c0188910115580e800403c03005a443c1c01852010310301840007050340c24140305800d42c22050680245101d0034003480104010f104100450b002e60300342c2d20302401114982d04c0440d91486995038002d40c980000302c1044000801c0c0713203c0c40212a1704074102c1c1d6284001b54842c6502130a051058001a00100005031041c03095030024042c055000c041810303100d64901c0080d21941044c2d40407108007038440300820441c0f130300c8078100b8098165604803034917043c0765540d200303041508040d200b4007840181240d10703d95031040c001c0f10001d0901000340d03902d19018002004007a40308582501d2070180d48404181b600b8010340681e4801c0d903019100d1400d400b1141c40d0040e1342c0b56001c0640790b010b070345 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 205535683 1250 205534433 205534451
    0xe03030409020304110f03190510051e0c180f150301170601231e041b02120712051b0d0c02010f030b060d0905071d07180e0613 56
    0x10410040000300400d410060300e900f41392900400000e011901280300d0303000e10000700000e69001c25080743c9405012030000f140b01440c03400b01d0511591101c0c041e003052a08080005142402c1c10303400c45a01c0a62580c0300586d02c41c141c01029021303400d220a46040d142500700e07101e04000d140c2082c640d400404003174003500340002c0640f19078800d8010207988044030840c4001840c003000064054034188860a82030682040417075a42c4030b00a512512820b04408201208920845000082e44002e001406000405000715000581845a1400621400351442002c2800005950714164061980e0444000842d022246600f003404d1403513507050380f82c08620308030500b040008007104c0c140e101d071000c05080740005402038527981c070f00301c007454281242c1815070b43e00d202c1150211b080503180095070380d15501388185400e010750403004c00000c01810860031494014400c5114100f19a00c0c01c5000500c1004080c1c6190a0b1003510180b103a010003049061800304098401c0031080440001c012079 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 205536933 1250 205535683 205535689
    0x9130f05070314070503010806041707051c1205060a062d08040c051e0603070203070c0e040605090a0b0f0a180b0105101809020a050712030b1804080304120e 69
    0x181e81c4040441e030f50719a4818551180310701e1075481546403d00d03034203640c94400565200c040c024030003820a400d40c440780081c40d1124003600d103000e070000100c03104000c0034401e49206410480c240000f069200c00b40a80408460040e90320685000d040f50791035a10348031081d214158865500d407514070180004268080e000e060030803c0000300d9403451b09900b02410007103103420080d00400d0280e40501d151000c0c45142807100180910300391081681d03650340d1817040741140144400184480843d40c400201080c1402203680501c0c02101c0c01c010940380d650405996030070a03d8010903401c02c00d400107107540354000e84a944011200300200b141e00d200d2101400c00b1004080495050352000014006800c0020540c4415261401c08940300d4103207020f001e181481c18450084126000501750000c24402e03800d403401d003079205240c00c034820300a00c03016002d4241058601d0284082c03462380d14425640225260055030010078007031558446485000c211092804180c091280c3e17600340740b210b61 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 205538183 1250 205536933 205536941
    0x409020409020d0b1e0705090d11061b010c02030408100c03061701050414191b0e09031803010c1413030b070c05010b040903140a0e03010204122609130f 67
    0x21300c6219080c0c075030701e8100b9143e40e00003464400603a000c5014020402da49030031408541e031240003221070201001c4c4514081000400c03034404036411880110303094500040c030381c803030615096407500240081c3c40c01240c02c03030b03aa008a2041031600d0388000204900c0c0101580f0131803800d401480c01280300c680f20740f4414404810208003211a039942c43c02c00c41803051100c1ca541c0e6004405010301042520394100103c4020070140107426120340c04481040210820380340c1d001080ca40c01071109524016004039226042181983d00d90840c203400300760107190622400e0340360195500c4260f144c0e00300c040300e20415000a10742c0c90084000c1d040100200c3e0006800324404c801503075600c4140c5440e131070101d096409002c9042c1c06070381004c10410010380c20148420001c0300e80050143c84030002002180c2000b104072426070154800100403070300f0321040c0000d250f00c038054092022411544030f01140648010000c540c403105090080c015907180c100e442360051101c034880400c500d40401e5200c0c0841d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 205539433 1250 205538183 205538209
    0x1006080a030225082e110f09010e090103030207150503040b0a0f0e060c0307090b0f090603070c0f03080402010908060f04080d0e1b0a0b0301060e040249020414040902040902 76
    0x280510141400340c185c150a5032440c000e445801030001d010028480c01940c000c01d510b0449805010409074003d91241410710540366000b0004403455070f40b81400307901c54031ba07070140c2000980c0300402c0c1c00c1220301410880380240e5009480a50313565801c00140010b0140e40da18280c01510388410704513508040241501950040e07441a9590400e04000b8120081c650700c10f501c032420030f001c0c1c4040a0041400d0360107890064540e1aa40d0717031502030885400100c241c0040240003050101024035500c01a250701c114800c0e00c7e0100c01c40e46410110b540e840d0203e134481002015200001c0000b541c0e2400750580e02c204240c04684000850907450500500c0d00c1890960400c00d82c05503074034548011010020607142c0310051455060820040514400094190150f90001031811440c60110841181020444500b82e600e20405014003000250340d07200301603003180503516101c2d200440c821039084425442d1b040d020740c041401400082c11b504442079a0050342c132003003540580c565250361040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 205540683 1250 205539433 205539463
    0x4030e180703060f090c0905060a1b060203010302011b02030a020112020c030406051e07020d0f1b0801021317150916060903061407050f2a1006080a03022508 69
    0x2090400d030404ea00c0380039660041201c1390500290940d01d54000c803c04059550a884040d0754080702c05041d14600460356540700c041031450b0510043c4059940a103040e00c2c801d0340c481d058843c08011151001446c0c01c8080c0d415040070441800543c000c41241015a584140250400500c10501030441e0010341c0000c021440004645e0040078070600c1443c0f00300c0b070081c454ce040840c9900407404413001400000c201149051800d81032084035241030460f2510401c0c40c41009460ba504203000c0e401c010018100c0104107100400d0b80040071510041035072002000b0180400c0f503146030712090b040a0160140c81c05506070750b4140400404001c4050300346074595010940c07841c070b032100c101e4110500344600d2000f01c00c140601d26a1000441d240961043c04807911410092140d400c48000e820480c66908040030a800c8900ca001c10303502400040c00d001084110303170302c503909a2900207100300200160046040341022040200d0301c200d20622040044803400e403583c1c02c481c41c140c403121014030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 205541933 1250 205540683 205540691
    0xb03030c0f070e160f020703150c03050a05060f04020a120c111c02030711030f330415021b060a0906050702010b01020d08061503180105010501110604030e180703 71
    0x2041c20100101c9008196056240c4103524044100310f1000c40d8200c244410044034120100649100304101e03006540c02144a01040010b1000d2000070110304e01103030701080c2808000f03903031401031748035480c41030300040c1c0f4016207110750300e0800000f035120501394024084d44003030340c2071018018072030352940780c03516101c411034244294421072404030098400c0800c0b00c1440300020781c5640c0030055901003036204024111030b1f8041030029081400098041003144100b04406005000140440885005003600036000c00303006800d8110b14001100c024210085084560324003c0c440d40c000d04022054840710820101d41c0c14119040c050181c0d1901c0c074081e1204489003d1090314130070f0940010407800200900c4501d440080d40310929070111034103100c510000500e040e100c4501c5086c0340b80242900956900d0304400a000c1004036200e48a12986824000310340f9501542d40ca0f0807404d05c50000b0016640c5560301152061801d0f5038158108400c1966440498010740c036207030064050b0f44001c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 205543183 1250 205541933 205541953
    0x10052101030f031b05121605030c061f06020601050906061201080109050105060406060c030f0201021308070f0f0b03041e0206180103050f0705070b060609060c070f090917030a0b03030c 81
    0x1884d00794403400c0380c040c0420070a0a00c00203180020815200c00e00300311241d40350514a840701070000000390000e08203010004080e0722020300400c0c100c1c07251b1042040311103c60740040c9481c801c0c1036103020366005a40800018451481c1800b90705600c504006d081320b142c407004929440b2004001e900c54500350f912003219408200082c051540d00041c01e88041261724a0860028440074060000ae02803090403110303449034038400c1d0100c7e44441030b22010400030035503c002c001d81d00c0a180c41000d200d00905200498001480407403034086440f1444c10b241181c4880d15052100000c0e40f202c2c0d41c0c11114800c1010040c0c03503141c0980841c850a4444501102460001606584c0010101c0d18840104010400010340240035200300642211034803182d80d40d024080349252080c2c2c102140d00c030102040d1074031803860014082d015500780030700c2d0451130b568401a603810340b01c00c420300809030a03a0151601142108070080e541c003011112000c40ca00c500762001c03a040d9030001d1418140d41d0440300f856 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 205544433 1250 205543183 205543187
    0x12070f110609010903060b0102070e01060e01020f071202060f0d0c080a05130203060a020a02010b060d060f0b030c12070507170d0e0a0c030f150f050a0b0f10052101030f03 75
    0x34031a5140c05840e99440c151192000070030703410f90790100070580c65440010500700c0c0d1080120f0005080082104000340d6103030800600508034481080703005200308a902c1858100c04902d800494410741085120031280e6802c10081350000d41e200c81d182d038414014040d5400860152180d00301454031084001c0c2000215102502c100030050805c403075010030804016200001d50a81c0b0401071940140c64030291501280508421244c0341e81c00304001c900c000320404641d105004444000c21110900d40c1d540031100600c0c0801c0f540303280c444000f40207540c4e03030403603e800382c07075000840d8580503180c40c2060f45d41001181154024062103000030802d0f018002c0988907512040b0b1540c4010144102c0ca5502c41a494081d80001413203005900e040d6400c0228100c202c952a200903801400083c585060b1040141802c4501c40b81c2e0303600384050f4819504040c0c000b000300427000b801d001c20908100c0816503041d4010f00f40c2090054007064480540c010180525000c0c50ac14501b11301084024100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 205545683 1250 205544433 205544453
    0xc05030610030c120509071d090d090b0306090406020c03130e070207140418021c1b0e07180b0d020705011103011508090307020603151201020408070e0912070f 70
    0x10910038507181048030400ca5420440c500d03412519240003090950f2950300080c2410707c107510104407404a15100e802400c1040c80140c0715410110072034518809442080318900c0301d078494001081000c02c003155041c01c0c41903034182e0140c0103101c058901407044407024996440f1204600003c2c50030541402401002410176401013101d10040c0015414000300301113814541e40f04512859540300560380c80d4910400c0700f02c025030010085440005114160100143c0c41c80c411140c0310b500d03848110b540b222940c500340541d00c040e50403c0140d92804000e0b144581c118800f009a50340381c5c1000030b020460b003002481207030750481016888410354031306203094805403902d18184d00014401071080c2c41800040e075203042c030545008006900c80c01b040b81c0c250300c40d9004c040d410900000411010740c0c24100241007010082d901c1400c021500c83c070300d034202c0c040c60182c1c07482c5400003102000b01d000c1c40381996402c40544006d640d2000031302e0640907034039402820100c0790815812400310500c24441e80d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 205546933 1250 205545683 205545709
    0xd02010c090605040909020307050a17060106031a0f12060c1308121c0f0f0b2404060c02011407030206010f090b010804020915031209150c0c0d080c010c050306 70
    0xd090303800074100b040280c15030249000b4a0020341c2d6031448030056550401c412001890050b201801640c0c0f110701804054a22140000040c4580300000401600c01e100f0000022002c0c40035111305c9003140100114203851038a1203510141c0e0b00070101246405108543c001c45525845030b6460740005512004030810303500409181e0402d1072111036800f0030760100c840d420040841e05180c03442d8841c03010b00400002d1201840035140c032000100c90081980036040c058800c46c0c0b4485040c0c4208051003280259890401302000280003c014403401400006d00c080e205040c500c00007a0060485011030700300349070035030040c2c0c02203004010b10664207400c440585003c43c014804141203800280c03d145014100078051076100d400241400d06000d021086000000c0035030307100d100242c4d0001450b80081c0d1220784030354900340c0ea941803205014211740320b42440c18040c121040d455400c0000e60081d802d001d9612000c04c2001030480329003072042ca41410442d444490f22400c2a0003030000d9445194 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 205548183 1250 205546933 205546937
    0x9120106050303040e0403140c16090b011d1305041b080303101401140c0706020c191202040e0607090317071a06060c01060602150a02040635090d02010c 67
    0x810510030340d02c01100b210281c540e25810582c06860b1454102c0b9240348151140c1c200e85008140c0c81d04900300494900c0041d8034020490802903200c02a1204aa00c8190160302181840310310f81c1416042c0e1560802d01c180c014210300340301c00c0540b16081502d800310341c1224000300111104038210404020074002d006001c00560440c0342040003001c060415000d26505071a01c004c08074040c0e031194050751206841c1440080d01d0304036201040d6552440b9000b00005402110b010114508010940c0701c3c16484400c600c103681403030400d070724540006070ba800780c2e04680c58801c001d02d8401d007006264003940040e86c816540720700d5030810a01c084c46121031170000d40d40401244010a8040c5078400e03013140400000104d0f038039610001200380c070442d00c003010f00f5420310344009016600810300e8040c20300d00305400c0341245c3c1d03141c0e0550300300e1241d07001e4000420b10540008444446200c06180441e09114105000240010011103450011112800c41c0c2d0300c99554285074903820f0080401546c114 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 205549433 1250 205548183 205548191
    0x1020a031d060a030906180b220210120e0c060f130308040e01060305070f0c1b0305010e030d0510050a2106320f060d030201090b0f0115050c0307020d0501150803091201 74
    0x640c3d80740c0c14008007404919840c50a4030b100284180007146409e615a80104000036030162908041d008026660354122041d182940c926041c00001c04c0d01c424450001701918980b0042e4510300307801c2c2c3c1040c0081c00c080b400212001c00003a00384402040038000620340444658905040101503543c018081c07820403501104c1003603016000080d018055a00074422582600c0f0814104446403040c1e00c007074a43e6080804c0250901804030040c0340300100c2003001c0c010355844c1840306542c2d42891141c40d400981c80c5504202c5e549102030000f045c0c4203a5801c142c0e030340d02c0d87d844150940350701d0205040388201e022001a8900c1040e90200181109901d03103c0c02403601c10a40c0c60305540042c506801409040e8026081510070340c0020700c40e82c6d2007224202d0605014018803940c4000340955010180c4030445001180d000300190780da20700440300210710305a61682400742180780750030200c60f5592a946003c95054821080901a0150400035601c46c2076103410044844000b10120841c0d07454 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 205550683 1250 205549433 205549481
    0xc05030d020f3003090307060507030605011d0a0902160606060201060501091e06080c0f070614010f14130e0303040f0204180506010e1512030d0c03060501020a031d060a030906 77
    0x2424440c00801804080195100d594445c5040d0562041400c01440305284c10100010350343c042c0e000900759002a6502501c0303103203c81c0300380200c503062000c8503403016160500b0030a07054681c00401900c007131102d0f00d5480d503502c4d42c1d03000155891030700002c0150351910303003d02c45960702c00b08170030042c10280440030400d401603401d004c0740d03a80f07030207480d04009190b000180d064012004071404003a403404000d55601440c1800c0008000c0c182c02d9905440041000052141600b08048d040c0c0d1604040f00c924000c0146c20082c170783c13040c08403001c20180c5614400b4485003040c00078600c00c50040c001d2510800c460310401c811a01e1703024151a00c4480401194040b80c400941c1d130b0f0544090aa0640c01c50f01c3c3c043c040104000c113403020351f40c8544550303c280c41001c1e002c4003600b00c0814000080c440101d0490054003501c44c036014160040e44820081c102003407040e0240c648030115240700340c0c40c000c607401c00b160300703540408560300221f82ca070440320b020800b43d40700d0300801045401052204000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 205551933 1250 205550683 205550743
    0x409050709031e020402130b0415180909021504090b010201050105120a030507140106030c08010509031602010503040219060201020a11150103080f0d090b0403031503080d090c05030d020f 82
    0x503648600406495522200c60115215581119801c0707001c50320031902160342d8a009010303527103d4020301c4800c0440120409040780070304c55001c14241c900a00c100b1060614411000821540c07a059a00205101e121341f0314a40d2040244040c01d114800401c100c0301a5002909440c010b9001e1360091250b6040c910400d5004608106850760501c1c1080c0e4030a16800c1c10500b400c0782204020895103003002c00020000340411000803035088000034004d031380e1084045c42d240d025512030412000c21040d5040300541c4100000c40c0d00a10051002c2440d008818911444080b6908a440580e44c001164106140c001a800820551703c50041c1200c0c0c9524444800c500b00600c0020030104010601e072805480d400c09803a248203001404000006060800001d81002620103a0200b41351191300d00c10103996a02e01c000342c035008403d040c50501114154001051401030a4800d061041c3c004a002da409016450703003501c1c160700400c1100c91a04105051a0040c11f404140b503040c00c101400c45030f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 205553183 1250 205551933 205551953
    0x20109061d15062110020a080403080a05010305030d0b01050d090b15060414010302030403110a15061d3108030105090705041503020d020c031b0613051c2102040905070903 75
    0x80c4c039891040f156841201e04610340603100c0751500307001d800490304c401107903440a0241c0c855401307580c9e122480e0b264100c1c030804403003080c00b0142c656001081b460401e070b801d83e00328613001401850b000345401d143c1c1404000320360004504a5581c03920b0b2062006201da402000c84003014102c1e24245072030b103405000980c0450110071030b0305064005c00001c0c01c0c58028519840204006020b5401c407101d60b03e4603502804a0590045100b0b16014020900c0305540c0000311f40c101c905820041d0035100c0286c9285412407401c3c09542c01c0d5150002d0f10030440c0c080a90181e010700c00c0801d41e85a5041504001070600010010700c20020b081c00200b00040e180c2602154444c1c0b542401a0b9400c0b481500d80040d20801e40e40b100c8500c0700003030700d034107031303d080100c4003130514085044d60b4141d1a800460340251218038005001a444140000205800300c4040c0380c000e085400c01030b80c1c000041d403078502c0e01d15545000c5103565901080c104601680d9002e02c550040d405d241046802d130075030b90307004844 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 205554433 1250 205553183 205553209
    0x22092a050409140f0106180603030e01140c0d05090909030a0206041b0b03070f0f021b01030203130506011203020706030513080d0b0406090f1503031e020109061d1506 73
    0x468480034050103000140001c01511103d48040d20b600c0c12038115070a010b4001403090448221040320b508500c05228403495080d82c0e807541e9150003d10001c80115141800398040d010b00000c00c000b000c400301c00030002d0b4036818405072686030302ca9501008100c81800d006100c419241c104005c21800309502003001503115038044070440001e4200c402624050025400900c0800b5000042c0075203103800c90003902c220303450307990341801a4181d110201d80750003403c00c072001d000204905680c0341c6c0d03000b81c02840d48070003080d590070b04081054848500e00340302a440201c0038088481400c2c28558148010001f4142d242002d00c030302e003801030001d8a0754944580207007216402054014004580360065081030b0b2000380f00b80189030f140d030040380040c80d00c800c0444078140781c4281c000112050107840411a90107071110454050715114820400c00b0780e00c60501155680c092490000325148105141040b06c00068134110341c0c2600301c90720300f0051040c0c44030700241250400c030480d5143d406407086 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 205555683 1250 205554433 205554439
    0xd0c17070209040b15030604140606150313080c03030406092006030a050705160c05040c031415030703060609060312021c050c070503060c07050c0907090509040222092a05 75
    0x3140d5a08059a085d6603051070050303410b0040b0304c10300052025038540c810910150324140ea445859010030003030f103080442c071099003a9005000043c1c01680c81c40e01615554020224585082e4030300c130300325007154011281110603d42d1810310006200c42c0c9424400d070801c0719128200000c030b582d00000c00c00d002c0103012a800303648071070020b604a40300301d00b1340c0c0c104040e20002d00c0b05104d481c9003202444d0102c0c09803500a074900b5080c88070342d078440c0c0681c24080605030f030002c0c05034031165600154242e41d905042c3e0035202e0300e000080002c490303100d848001c001d401000141030341186400001030803da0b4044007150300104001d4a520101100714020500d107081003542c030340200800781c0c200460b0f0703071200e58580a440c003044035551400004010300c600c140c0c02d80e400c08209004115a400c81528110001040c805041c0400d003000d0761001c0d04107000400b0a440442a540c1503a18481c050f45000800b03a115542070b010031141d1210078007107070b1002c010700c02c9951f12481010007001071071040030308c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 205556933 1250 205555683 205555703
    0x5010504202d130e010606140403030905090405010915020d0606030209060315040e010f2a0504120503040e040305070c05060f0d02070807080f0a0e090714090a080d0c1707020904 78
    0x29559a0f240c00b1800a1484400078042054400e030580d000b01002e126050104131221031400e0100c20910032a001d0380d51580350300451508003014407507a0400140110744540d0788054000120f00c00c801d644000d0090f8210240c3d0305d10340c5800640c160341147e807140c428180140030003d03040c0d89040a89500031200780c205d528005802000601400070300c4211145035180c00d406100c4441e040d040303100b0744e0030b4807038840703192414140307215100c081940701c0c003070000394180014405031060581c80078420780118100c07402c0a8803400b500300d46440c192011004640c5c001440740800ca011440712005101c00c17a0b6003401c100780410301d9a440d02c60720b54081e6140d903000801404001c0300005403000302e40c2121509482d003280d0740803124154403480803900450846109030b075941c03810070b48191280c3c0243d5641300d0035010002074042160402c2000943c0801040d00118154004200703e1034a543d895540f0f911402081c14416a100c40e1085405100d04082180602503294926241d030130a62000f9111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 205558183 1250 205556933 205557019
    0x3f04031101080406110307030c0e03031306050309010207020a060c120908060a0c090906090209090906040203120c0c0904120e0303040b0a0806011b06021902010506010c1e0501050420 80
    0x900401710004140c070201c0000c0b090010080d4180c1c09840900c0d180d8460140004c2c00c1402c245d60b85c0584081c0030410b540f100307001e1041030f2080000d10303003154000c00054203140042c1d0002e054100682c0200c0c0000e001c0c0000d01003402407030b00c40e104002c09070382420200b007814000c0c0b080d16200010005003a003900c55030102003d82c0300e0040000201800c2000b0060300d07446903043c8002c2c0d4003c3e15403522034008080030035041c200c045041e6029641c014010171008100c2d9101e0708160700b00c000c0c840418029400214800d48034030312040e100354400c0140507029140000301900c10520400030b1802580244414800005910200e0b1045c00b480d0800f0b01c2c240e84e03000c00481d0341840131135030604008002c42d03a2030304004903a00904544e041e24405101c0081410008a00b2181c00b22039290004104202c60300c00704c0c1c01c031440180790b080000390364221f40040d03468060070b407001a142150903004042c0304100b9000707548603140300210708943c6400f00c0800e40000c012900c02c414108904d600c5503040b18 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 205559433 1250 205558183 205558193
    0x10f050c100204090e010605010f02030706051003020607140f0111070f050f16080601050621040203030c0f100c020a02060a11010b130516030209031b033f040311010804 74
    0xc01d201c0d902141c0555035940c4070b800c1480034204182001c1003540c00d00700080303520743c058145000c1001c12507000354140340494481c00064038014195503040eaa0040b004070150b100c007070092146c0740c040c3e084041408030300b4140e00c1c0f07003c80e8480751543c10303494040441c148071040c10845d240302d03410001c10541d42041d820310509121000000c03207100d200741e4842c84001403075001e50398201d07003403201901c2c440d81c0e036502400094404d18410f1101c031251907003035508540c08240c905800a00260459040c200c02e000901d10b0101e5100031180e80d940400207031084204240a42004130303c2c40c1c4081d2103040f0465010030780310702aa150304c1c030620440008001101e42d096100c3e0380c855130020483e10311005681d5982e0010b080544000c0c010490801417030381024000c0c001c9030320042c0701400030306150300080f41034007030390700c4014010b1340c1400348081d0703421800080c50300300c164994644804040b0300301d43d40d00030a101c54003c120840281c4148000c0011800446603400907441c20f0a10102c1c50b59035143c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 205560683 1250 205559433 205559443
    0x1207050118030207090f02180103020d060e0a0209030105100e061c1e0501050f0705090d08040308191d0306060d03020a0b070e01030c031404060915050910140402010f050c 75
    0x1200074800450005003456800500c20782103402083c01001030190010f07803602a44101021140b80d200c00c1d0140f400d95501c01d41c02400c00001991000502c00d131038201000e00340310103640c5650441e40210b14402246020b1081580000c0c640b41c02d107409514001c1c0945802030018a15803241105110010106588450501c0f009500c0300c403210200c041d4809850004040c0c4d1002d42c1d1943c40c180004100707601f502d07010390040f0215140c1c0f508010110081069005014004035074101e03041c0310000024160780e02900100c2c4251040880a0b00480c0000305100c07a1640c08000c0300100040105060700c020800c1354102e60b05803806883c880e9a0f081c2a860070707203a00c02c000c20100780303401004401503110007075540200c1300344d0303040c040f0a0040c5411015603500c80c01001800320b030f1002040c000b8900e680304032181741c4144c14a4080f890001d51080c01c65100301d070b0041d81604001c00c0f84800c4280303441050b000c81c0c0001e42c4045242006d4000a206ca0800032072035040c000000b070b90801803501004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 205561933 1250 205560683 205560701
    0x61508030301031b0501020f0c09070203090604080d030b100806060a05070f060905010b1504141918110309100506130c030911010c080a0813060c03051005090912070501 74
    0xc907540d07035a50340b40c00d015401070315030540b036850b030b40344004625588081200c98220382c2070001003e00d46564420009060005011002588001c00c1000304545401002d0001050b040c130180450095454000d0142d07500c0554140c4600c0344c80c2e500d01c0403035412201e4550042000e6400a40783c008400059034213100703c1c0301c06061301c1940f007811010000b0036044814618400d8000f401001040c4e810300c81c0da0b4500030303031156805105100511402c0800041031202e208001d04c40404001b0f46040c3c023410320a642c12020960f103415030000682c030300600403562641085208185149080d4000e9a00d580004202c00881600c542c00304940f551202c501c1101c086420904104540e40c03131502500414001c00101c4509464000c40d400ca58016609058000c3e048600750789401c1e0a850212002c3c0d40040c00441029007600d11036001c45c00900c21180d001e01035480000702400c100324802c581c060740e5881648102d00648c20000d581d1804201324540c8440c0000540d294483c52034018050b09103c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 205563183 1250 205561933 205561949
    0x50702012d0f0f05180f0d0e030123070306060207150c020d0b090309010e030a1124071112280204020403020910050108090102090a06080406150b0301051305130615 72
    0x43d8011100761203d0b4062030003124845008031018049525080e01c816030444643d9003904981403c1c03440a000746a03c1c111011b00400000b007011044050304040d1446039812900100700508202c1c9990b0544100030181c021030000f000480e24000c40408043d846400c00d03410043c61090903021912110106c204203640030300d80442c01e01d0020307606641c3c0d800080440380000c082c05104070306800c0101e04d40c0c0d009074002000e28000080141442000c241841000c90355640c0c900d00c608240c4c803844080c0101c82d00c80c4440c00300f46050503040080e01d031510444410075801002098109080c0f200e01c0038084041818841c1c2007007180d0001900a0040344e0000c0e401901d1807041024450781034142c24195a400d80707403818203443d24a0150700300d001d000074603904280000e80070711255019213a0b1590241c407914011076031180d0b402e0700c07840681e00d91b40700094028004c0300600c071500e424000c0e103820410b06401080700d4a0040d03114003844801e004040c2c11141c4d00d24155030342b031a5038078040014003da0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 205564433 1250 205563183 205563191
    0x30309060a030e0a060c0216120615120317010510080109110d061e0f080d05031b0a080412050715020f090a060504061b02060306041508120d050702012d0f 68
    0x581403410180a1500c211b000501400044000310944041400e09886585010800d92051680c501000704540e09d00c40303030400441d840000300f890394100c04040d4a0b00c43c1d503407c52402065110404400f1307041c0c1140784a41405400d12400b19401001e040c11140922000b140e50031032003900003014890441d42056190614501081820421412071140011034016810003542c0d240800d4060095015014003900948030707514030305e4810406181c0204c4101071441c1d0070011560324504aa0003c800c800106210f1000c210500ca8481c030300314030742c84a60502e145403144568074040212280c1200200c400e5000c10741c04858001102640d0480502800c19000a03448036805403207a005489901c002494a01006413004445200d890360345a0150209084d1340f0342d902044060300140500c2032003d0140c540000b2502c2d010041c595500310f900654a5580303024100c29002e0703030402002c5078103581c10301c40c0b0300c0380741d2907001c1641d01030030881400425030309216442a03000e0000504820f0003d820 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 205565683 1250 205564433 205564453
    0x30b0a0b04061e08010b1b0102120103060f0c0f02151f0e0a06120305190e1c0b0907120b04050703060f0c0f020604030f0c15020301080c030706020c030309060a030e 72
    0x1c0092629103520f111840b000400d4940101c1d00d100090243c000701030f02c01e00100c2e00b410a80d580603000681036038009420110b80d03094880c85040c00740d0041d030b0260b8580c030340c04400304218880c0c001c03800034518110100c1300100d8000381d0344170340d031040301c620380e0190300002051500f4207402008003402000c40845941d41d44c02c1c0c004283e14090b910f10000b18540b101c001810788511000e412111b038180c548a041c030764220808403c55000200ca24144038900100d200603507903080c0654141c84030000707141000c110605010a100c04000c200300f00544c460303d028059034007035062148203250b100300034020740e59451a02038240060b40c0c0c0000c019505006a40d00c66104540003002e0201c1c841d610202403051007102241e0750340c400d860103408148103500c0200b03403a1040420020701802900f418043e40e0399140396204036402688040c00942101d00c034411640f030180000c40003030440b48018840222448002522441004c0205100c0c050010f17803001098000d8202c004d11183ca6004c2e29010300c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 205566933 1250 205565683 205565687
    0x618030a050703020108090f0d030203091e061603020906071410050703051503060709061b0503030903090906060f09010f0c02040504030f0f180b070302030f03040f02040c1d01030b0a0b0406 83
    0x102c6030200f01d022900d0400001c0c1000300000f0440d00305182080289039803811054298025400608540e40b94000d50b0142c1079010211310426401072000d07002885039180001c180c40030481820052000c040c0108008a200c2d41c464082e588400d42104080000e440c4104046103498020f5031400316541c2081c4c200803401e6050380c4428450500003110440386400c181c10140ca40c1300840f048800700d46d2021080c0030030761050902d840c400c007004501c6520042c25403941440d580045130202ca0544c0002241601801c001c3c1110360001c50555450342040d2107098010719a0050701d00190401c0b0101c00d8403aa4940f1414404801c3d41e0003820401c085c0c00c15080060040111400d44408203402d8408602003a2044880d40b8440c0511429074203a0b07424000c1c07200032648155026002c611040c410035032061594001140190721a84058003040c100c0d2062009640c40c5003c2d850911a0482401d1058050a11041151982440d0002d0310034210700018100e00029006101001c00102d004100a1707 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 205568183 1250 205566933 205566943
    0x150f0509310210110618030c010f0b0a060306080703030305040204090c0b0702030c0f010f050705071d09071514070c0e070203090a05030f070302130f0507090510020d05090618030a05 80
    0x1500941c0c00c0c61200c403940000b0307038040009029040d00d80d800100080ca03025101b1300f00680c21165101503030b180c1481006046d003595201e01003440315903551140120f04e40f6007842070900400b81030500344101407600c20000e444028902c80507041c103072a00d001404558942d0310610410f9804003407000c1c0c1d01d1b00c40d8002e030358582000340120302a1040f400b01d85868507040c1c45080714070724140d5a8078032801e240700c0c0c06c40703c0d6048010700f01c07000e1041c100042414403810784032070881928800c4c0e0308643c0c43d01c840b40918008055000003201141410b02c178040c0355119400c0d40d9940104454555100d440d031404082e80d01c20741d801002031500b56400d1000303860307020008041a290845100c90306644a100f010303221881440c44500315030011404000500b445601c0604805900c44001002009036050b001607a804984400c001443c00300d0034002c41c0740614462040900c14801420460f00800340980350344101c050f00c920800000ca80740f4007540649040412800018040e82c00c02412464401c1d559 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 205569433 1250 205568183 205568281
    0x306070525060906050f101401031401060c051504030f4d0705090412110607090f082a031f0506030705150304110d1202060109150f0509 60
    0x4d141800042824080c4000890780071f00c5581580c0d6a15501e8620039507a1381c200c0e40019814141c0310a0200070551a2a0341c2c58000c0110fa12402905045880c200782880108480032211941440c144000300c1d510a1032100c9803803503802c181c00700c500c44c0c0d0901c10440d800b202c005004901074030380803002e00301c0e040c407084101640315501941a4442c1203103541c5a20442c010b076500310640714000350105040741e4400c01214407a0030800041d12660960500b001404c85800340490402c1c28100031800500743c01ca4010480d02002c0d25240200003d2510400e6050b50200480c03c400c00c02a485582d05200b40390351107410310300000d1503250604020001c3d220403100b0600c280540d40f0f00007800d080003020032614124038400245540d4403a0356000040081441e02c94000d400d802020b000541110403042401c1c91540003040c8662410700f07180300355081d000e802030343c0716241c00303041003110703011540d8a06540d01102d48400c644c1d284103d005400200d141c1d58002c12060751092000140218410000307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 205570683 1250 205569433 205569443
    0x1050408010507030b13020901050d18140604120905100e22060f0b0a0221070209010e040b092817030705070b010501030624030e0f0304060305100503060705250609 72
    0x80040c813803100204030300403149154048ae00800c91440c2c9100c0c02c1e48142e0350301050340d41240701c0390b503070b40c0b500340d44046411071082d9664007110500060044010750070420416614011080e81e05044c0490210300640d08088148002030554071a666900602c3c00300c82d0480042c2c0000c1040d03440030f040c010308110312501d00d0080c4800070104101600008580c10300c4480c1e001400d141805114003216401d4981407145410340030f000c0c07080140c3d0341c0e00307030580240030025803100b81d400d06041404200b00e0203010807038030f80d00040c12401c1421240e5030440386400c0001310f49030a5803050500344000703000260852206400041005007403500038000c2c02180340950a2051560380310700054003156414001c140c0180c4809403856080c0c11f1110400343e444450b480c0104800450401c02403500740203825800c41e03a00701140c14409030398148500c0d80d10604400d42e140b0440d24000c04261030f01c1000c1c29031802c203d40080c8000487c1c00c50549e200d1182000303003a03042d9008043c1000c0d40106628641122 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 205571933 1250 205570683 205570699
    0x40f150e1905151911010908070c0e060a0509011a130f230d0f020301150f091a0d061503080a0314070201020304020f01120f02070b040204110f09090601050408010507030b 75
    0x400449800303640350180f03d584e0319038480d2801c580c280d600742640e0110040540d2200c016000045101010300300103803242400740441741c00c00110f6404100018004c901032020003808001a80e943c5000ca41140c180c8480c0c014440000c120b0380764280f1441c0034100355120030640020345003103240c2c0088100c070014000d070301c1003c00e0f000100242505201c42d0650104109160b0400b007594800e60000d500d03c014000920042c1070300a200c2c0351102ca13404041c915208000400c046851401030140c50140d0410003583c440c80c00700040c00b418400c003006400a6035811420301d28160101190029641010070107407140502c4c00010040c0c01d00c1d0704846800d880d44c10100e40624014020b81e0700807503004180c1e950070402c1c0c0004450090181d12420903542c1c44600300328000780343d440244102e50080c00ca04035146040e00510094540c80c001201300b0480c2004440d002504050640d84440780488200c40c40740c846000480d0940101e0300120300c954640801c3c4403940c1c0d0141d0101c10f042600380d403452 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 205573183 1250 205571933 205571959
    0x20f0414011205010b2409012109120c020303070602031f15030b091603050a06180b040e060105010801210b1e060603072111070803040b0c040f150e1905 67
    0x94443c620074002c03506c0c240328072203c02100d80d8540203000809018542201c80c85540741c2040142d4090021048440381c1c3c0d001a05d00717000d02e4a80000e20944142130040c4850650f5011aa0342d204440c2d0140140d6404004603d8100280c510f191480c0800c61041c41d005444420310384180303908403c1100420304c1c02d40844070500304a0301c02e03441545003881506000440b0350781039003d840000c100900f00d07680e81d034012030350000d0600c1c2041400c22460340050007450880c01d0004595922151041c03681c03051004002c140e0b8441c40382410358280000441555444000ba4002481d100c10000e04d10000a410007666085e0640c88a01c80c0e2403030301c0700325610f49404c8184503051209a41c800001011880301c988501224800d0b0912080000800602c0e004114201340c0540c100500455081d0300000c14401400b079a50041134100c00c16500c084e20700340c0740011000c02c0c10240c0c480c0d10701c841c2c940c4107840986030151032040c6900c00054151500f210710b142418440b02c03d1b5019261044910b01014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 205574433 1250 205573183 205573189
    0x20409050d0e0901050604031b090e0a05070f0b16030311161203060302090c0a021f0c1d0303070f0305070611040f21060b0303041503060609050418020f0414011205010b 74
    0x3e94102c03000070308020310b4181540c403412410710fa25408001040f40419000804203481d201f1401116005d2000d0b042890591909904003e190343c0410031240c0921001d2001580c00c00480c0d103015040b400036242450503280550107054414415104844042403010b031403102c58002d104107a10400140895004c044c20075000c850240c007001c0d404c130086d6000540034901034002421408500d0049900d662103030b02100d01e03042c6c0c03002450520325450304010814290869040a010000050b0800d001030101011907905e000e40071303018140c01d030b41d115040705140c000c10885a98940155041c09420012500d00c550350b482449103000b00f602e0036000081c0c3e01b003222815141041c8400510141846584682000d007000840c0958103001c10800050b411007030340820901c0400700e03140401d8003803400501400c00b01340d640c0030600403404c0891094a075140c91001c140e0803541210401841a901d0740802c0c01171089241c3c018145c0d011000100700300c089c040780068841c0c4500000e0007141c0008083c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 205575539 1106 205574433 205574449
    0x4240e0307030201050f04030c06020f09040c0c021203070c03060c0302040b12010806010e0402060d05070219060e1b10050a030207060603061d03180603090a020409050d0e 75
    0x1c103400c060b02801120361000c52010640c07040e141a49003d01241c9a000000b0321380c41d800140098641c02e15000d54a030810040d00c104a18403200c1c1e006401d48078540026881520117550700601e0010020880c1e0038070368000c2c1140c0300c0c20b02e0f5680388070240000198090a0580034840070030518541400752980c001c4410400d080e5515141405007844010b030003d18054441c50100009a03e07040210384810b0754820b00056140e035112001c0381054159100742e050008220f2240c400d01a1745d8001c41c400c0e90104080d90b071400003140c08114500701401045402c00c038443d1554803003e01907800b60030207180608025280c0300159540008a40d40d94100720b424640c0c2e4000450005d42c801407808c101000c200081d49800420741c181c000241045100c144501e600000044d4044402d01c104003000780c0c00740080c00f000e296450300305e444d82c001c0c14441c00040c44c48511200140382c8548 = true := by decide +kernel

theorem cover : BRFrame.Cov 205395683 205575539 := by
  have h0 := BRFrame.cov_init 205395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 205395683 ≤ n) (h2 : n < 205575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
