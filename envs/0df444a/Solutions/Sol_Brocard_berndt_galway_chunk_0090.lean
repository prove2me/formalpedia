-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0090
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:46:39.991999+00:00
-- url     : https://prove2.me/submissions/e2a8a693-6371-49f6-9dbc-222a0c8f41ab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 16007200 ≤ n < 16187057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 16008450 1250 16007200 16007209
    0x6020601170c0904031e09030f0204020306031903210b060904090203120c070906050d05070512030c03220b04060c0305030a0906021603021009020109030f031103031006020c010e 78
    0x10301503250346a900100310304240504229402c14004041c0c0b420b040c0e860141409804000802c0c83c900d201840096011800d501c140e1114003035070791100ca2440c6007500c076003d120007900000c2c0101e4140c800c040381c005d03042d00d8801122010700e109903102c8003083c0450036015441da03042e110a00c2142d00b415a001d1062b80c46106943c21340000741c900041907521400000e1034400255030007241042d000420b45150340d0013103584030940d0200001409256a19030034050261030241c40a4000d0b00310311801d0001e480c0001c04500d4054851040b2402c101802c440c190a560280700d1030a010f4000c81a0007003800d1343c0b56030260040104c0030106041070319002010b00030407208040142000400400030b0100d02041e440f400f401a0080d0b021500c425800b0407014440044910940243c884c0703164105c05101c081c010080d01c01c1d4182e4551030315920310f589a5502c0142c0040403000e0080d20014040c03601001c1001d0740c41403600350070821340246005c9021741030840001c0030741d040050707100140d41580c95 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 16009700 1250 16008450 16008463
    0x504150b0a05150310120c0503060609040201050909250302090a0602030301030302030a0806040f0908070209010e010513020705150f0f061e0607060b1207031e03020c060309150403080103050d090602 87
    0x7000c3c649503640c2e9507010a200c52503c03c513000b0140c1c00034500b80742024030030301c401c4400a84030141c0803500706032102c0d401c06c0b404c80d40c00c860003400214104106240c034200003a0060700580d40026842055000355490580c06150301c0074200007a03404142c02501e850004601c1d401001c260000e0f500d1941151002501d0f8444d260890040c4580070700460102d4846600924184161090070043c0e409030303151040c8a40e00a0200384d00c00e201a5001084002c0c00c08030b0a41210f000034591886007101d141050302030740110001b0340385801400c000388080c10304803440c5807107022030343c0300d82c9031034a000c1c0d1540d0541100a821305004030f040719020b18683d81b04182e20015440100c5286407075024a180440281110032111504105031203111121a0400121001903030f104c6ca00101e01c2c0040b40310440849501c004d0054010b0b442005002c00c142001c600554001d102d22050328080c070f006030600c0c1c1801109460441c0040d100307a004006100d000c4c000075032505002c0c900b8540301e40c64160f0003980c540e07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 16010950 1250 16009700 16009729
    0x9010f05181305060403030f0b01020d020304060311041a0307110307030206040f1103010905060a1a06030403051606050106050a080703091a071101050a020417120a0e0d060504150b0a05 81
    0x108040450703406002d0b0000550903039445001c6a08520f41460002d011b4050001e940c01403600f4101c1d881c44d958000318590050b1000303030b4000c505041c907100048000c2e013860051104560400c101c08240c2c980460080090384940c100100e98900789950010400c400f00e8044102a070020702915000a90110f8099005500000c0480310307801c2c0da0800011941d44803003869415846c00500104004020401501c524000c040410490044486822405000d038880ba60300c94800c2000130002400765010380364184200240c040350062075602d940460f0000e07000503011840c04282000b94552000201d40c1c80005840d0a104201d50b44d501c010001c44101119803007280301c5d50014800750710440b0051808581c03c0024005401c200009800a5209001d5110f01d0418500c50bc00c420341c0c001105103151081c58503413481c1c2180c50308101d802d10040c092456008000c440500d0210b82c0320f000d014002d50003900042c442d6100440f4000071115510b10103070103940c900804205a40e14001d181d910007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 16012200 1250 16010950 16010989
    0x3030e06090a0503100606020f0706140d11070303200c060a0b03030c010f0b31020901021002030408030a060e010b071b09050412030e06010509060d05010912030b09010f05 75
    0x441c00000040d020701c6998100d980c05100d040941d4035100401e40000044801680030741e5107040c1c54825498945d81c0703600510000c60700d08051620081c0d2000d00070089078018450000385a40d4407415a03200341d00030712055000035202c403850113a80348403004881803510305101d03040c501034035448841e0301d410000301610304203590340301100c0141d10107000300d620094800c4000c01025505460810091542041d014051000700c55a92401c000041a0202c44452545802c00b590f49050703005002c2d601541c0c0383c80c11070140e010404404078550015500032031003281015224035200c0201c4089130b006a0001c450886603400401020701070000325558aa004510301c1a0b141c0001c038980840d0055a1142003554a403504120601c003010445803040c0440d0394040c0300070342c2d10102d02550381801303000d01d0358002042404903d42e850603c0c0102c035028850400480c1d500e1f11503d808081d0744403c0080008640c84280781d841a140220181e4050004000c01000050034900030a55003121141c000805 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 16013450 1250 16012200 16012207
    0x60d020909010b090901020703030f110415050702060403030905040e0d0504060c06090203030304030801060807020a02030714040e010c020609010b0306010e04033f05010905040b06130b03070f030209060a03030e06 93
    0xe44800303401c02281e00c0400303408000301703040484034603000f5440340350140c0c00607242c10310113405882240900b003030100d0340d102014205810b100c1403101001d080110b400c180301d410070640005840d440040c1008601a8903600c0d0781601c7c10061209171010f403000c0901c241c104040750f01019070041c09031390179207241c3e1412644141040c83d001000302046180030758188004000c0000b01a484950342c1e041c1d0b5035a644d0140c498540c0c08081c2c2e940c00d1110720003581500080340c1070080c101d115540f540c40d100d0050010641140700c40b90b141c00c5070000101d1000503003112040126a10782402a40f110280542c0144210f41c500604242c4540020300000c007008030b011010105400c034140f0a520648045901c80f07000309400070314400c107004522002802c01e09050001400098900c03409210b990488142c030b00720399541d400c000042c00b0b8180c40e440807594810080c000303605c040040340090400c2d551614205805c50040050028005104501c1031031403080074030010b54410942449403100381d400d5601c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 16014700 1250 16013450 16013461
    0x306040809190b0a0225050f011209060504050f030a02061b0c070803030a0501090504050a12030e07030c0e0109060503030d090201030f0f1a0102061302010c050f0616110105060d0209 80
    0x500e4078203010b038107100407468004102107602100070840900d05808031442c0200c0b000c202c600004030028003456081c1031080c20021030600105035042c0300b00c140b4050b850181c08104203022550342940c2680c40e5a9114100002c000e010800c01d1001c0700307084029814980d460750020740d685001030207a2a900c00d51003240410644080642c1c201c0b0020805890b810b0307880d03d514942d250030444011550a05003400043e01d00098810b55000300e0300600900117003562510f808031115601d48003c401c1583d0303050080031096040c010a0003941c0b107110382140541c903213821481c0181060304415030742c901d0f1160130446641d0000440d60a0b000b001d0002c100030303c00c0c1c00160024101c0c0700312280500d041101d140032500b0554044000708000118000d03041c501c031001260742e21000c89100b490b240c040d40020700035600440e00111450b2041c000c54581001c0e00d8103813801c0600139510024481250b401c0e07040025000305003041c3d000404002081686480c200041000d441d8000103801848440082003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 16015950 1250 16014700 16014709
    0x50d0804050a24050f040306020318100204051912030c0f0812160918020d0608010606020f0601060c0302030f03180703030518010507020904080f0c061515090306040809 74
    0x500030301000b0401944942d5402d030542c0540c03d07041082000040c800b0014030414081c2042c1c0b04c60816824803c0d0426085507501c20017940003a10041c00d4100141103000700ea081000094a140304142015854500e040c05000144000e03a0790800c81b12502c8500707000201003600003080098152600c044100b0b11410031844206101201a0100d280055440240f242100d913403802103181c04804e122035400c00d901103c114810340540c500d0500e4580703891003582c006070050081e9a16210380018800d6940a10034219503c551084001d0381050003c010340e40014000d45004020a040851401c40c282c0d8000f0746a21840d1b4141c1c3d01400c020021400000d8000c4041141c81500011201000d450f07081c09881504010b2204071044000d054101c0300707503c640d00f81d5440a90181c008040b60300c03140e440c101550001c0e50003508410003031016031004201046034030b02518000b0303408214200300e041400559480500e4500c00700d00100b154032159140018802d0b4055004104c0980f103c81034030019 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 16017200 1250 16015950 16015957
    0x8090f060706020a1e050c060705030705041e0302010e0a150c08091002060f15060702040f110409050910050106020a0b060109050d030305150102070503070306020901200109030809010b0a050d08 85
    0x1034800b07807022540461442d045480b0300208280d4409200702081e081400b22003510030f603a45200d090f045603000ca82143e0085001d90340000c198100941003584450700004028191130031002c948041590820955800080120380d2620985003000c1d40b5041405e6400c003261b9000e9014104243d44481005110800095500e5020024110144030f15110002561040c0507600045140044404603008540030503d6202c511005800d250a001c0705808100083c5802c80f240d807181912131248413085160100200041e2000c803000003001d003004100e16150010150580c5882450000140682c0f60001807140500f276000203035048a644e004012075000c2c2c3c0d683d0140b41c000281000880416405410a510402806c490394855840d0180126500d0940c0d00c1043d4054102d00c07001e20200f40c16030002c008070340040c1000d0300c103507030151500da01041310141801c00da070750750300c3c100d108140c0d104004c0c68112444038020300a5011600005031201841c0c82103a2052a02c0c81c080803c006800003074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 16018450 1250 16017200 16017203
    0x150b0d02090a0314010e28020a09060b030405010c0203030403121808030a0c030f0908040e071107060e0103051b090d060b03060a0203010f061106070e0d02030706020f010c0503010308090f0607 84
    0x201550aa83da1921080c0004000c00718003265081c0a440c1172249400a0b041c085080d201c610b83d02e0510414210089803d20494241e800060342003010a4036510380c0100346c002c11091499540c0d0707240904105084070545140d40303046400c20020322011035813018050a0f00b403801080010030680915003258a0a5018001040000701208002c10181d4640c00300044400c0758500b4071100403240e94820459074990401008590244401c0c4211844040100c0d4014418141140340d44c0c002e5516620b00825544039400055080c9044026564035005150f000203a0060109914005a4840d0501c0c0540c2c0d4000b80540c2e20f03412800309000d81d98000c0003841902600391040790800b21b591802070341c070034064042c2e10141500006071040c40f60f401045103812030780180c0082d80300e0b02d1040b10550302a1081542c801a04825400540e0302449403070014191b42d00104981c10841c10681d0a40742c0020f592014420144010800300300c0c49000c54034410011140c5041e00030a08000400600a0440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 16019700 1250 16018450 16018459
    0x5060d051002040f0f05061801020717060106090603050709030201030b0105041a07020f0102060903030f04060603150e06070e0d06020a0c0b010b0903060a0c020a060c02071a040e0604150b0d0209 85
    0x292054906910b90090094807044090b810499403900762200d07000b1818460507401803c20041c6903003e40e5802003aa001190501c10391300030070307680c01d02035a809044181a9407250480340042000940040030703100100b1403804c1c140030a20341540081c14020300c0b1b1102074141900c40c9540c0400d0fa2165049402616807804200135004800c512a2a180c104080881c0a11500303001859150b000003400e91007001c2803c0198a95030f07031240b41d0360303402a0181c0b046813035130740741e88000c000640c12100c080c410343d804140c00100c040000003050b19114002d03010105205c26240c00c58040c1c0c494002c03100c40300f42c0100000d07a9621380702030304032886407142c1e1010300300b580c0500001c500030000300f00070220f04404500b26001916548828070481c2c4010700603c025a20280b440360009d12203403c02043c142c50f078015624510798846500a10310307001400001c1c0108009018001c141c0100b030a00d800c00c009031001c01c02c1202c04000152190b1007401a203082450119080d580e0001c550110340d0030100140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 16020950 1250 16019700 16019713
    0x20d080f0c060a0f02040e070c0c0306020c0a05060a0b0609060310050d03020a0b010902040e01031b0b1606050906040f0311030c0102070f0b0a0504080406030b0105090a0f06090605040e010905060d05 87
    0x10700700e520b4400076a00304200a09101350029540d0290082d942617450b01c20042c9040d1b00c5e040401d48550000e81d0046403040b44040d4000081180340c8041d2142d071803444e000d4160742e0214a070850078140c0080074070b44000e25007808402603450310741c29a00305020544001e0781d01e8940182121350150650701040c1d01040c09185401059404a100341d2050f2181ca00301140d070341c80c0c0440074141c1c0118003e04a4400f84000104041414041c3c1c021500c41859190f039183c903100c0e02c0c00700e4194041d0030701500f1200308074140020821076110300f690104003034024180c02c0c02c1036036400125201218000e0108610000028411407003031080300e83e1001c1d4100210f50704d0b5400d1415600080e944041916456007580004504884501409220700c0e40002d029107000d06011040d0000c240701403186040100074402506076803901440d4001230012926070311901c5184c900c00901d11071150304907204000c0d00380701c200a4001c6440e06581902c9245078041144da0350503000c20301140c40100c0c054503612508 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 16022200 1250 16020950 16020967
    0x1140406030c030503041a04060507060903030b0d08091005040803090603060a1d0a24030209130206030a0203060f010c03020c0114090603070e04050a02040605030f130f060605010e010c03020a020d080f 88
    0x1004004841f0710405004d15001c405104136264050f030b02c9928082242044404d0016485d980f0500d403240c440d04001802440403404102d8490170b4040490b0740c1c0c2da000480c2d003614a00100e84101001e0356141c034500e4942030012950701ca0042d626040d01502d404070200e0b03104d560b040401d07005000140006101039023134401804d800c0c1010b89000303103007a2801c5443c82002c41812603440310502480b09a03078034103281d84c4c00d22208071320003001481070001020648006135214401103014100c194409a10380c01e2403400c21010034860403501d414080c1e240d041c3c1000a401280540000000342070015401c9007000c0c0711000c0d840341615880c2c0c0311400004002440c0c1e0400365454040a0945040100787d4641e140f840403803141e030103004045a0103000040340210800c03280340d400720f008a42090078024940d25550946120716040380d029454400030311403542d0009c401200e0410902c2c00d0381198203541c8000e0b4907511904006401280720329032100a1203801c1040b0f0303180c3c080c2c1c10324895684555 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 16023450 1250 16022200 16022203
    0x120706060506030406050a0c1704020d23070503010b0409170703020102040302150d1407020a11030c10080f060625050c0a080d020708070b090123040e01030201200601140406030c0305 80
    0x116401417203281342c4003145503230a2086500080618020f0390a4403c1d4882c0d4082103c07800ca84d010488054032001241d0107110140c10744201e5082104004181540c1064101400d480c0f04071013240c00b170351a00002401155014480b40011080e40140e04d64682c2d41c0d003401ca0181c411a04060741102d562076044140fa5410b030300400c2d03240e400910070001600d04154901d038180041d22040300503884481c880b80030400c04101c92240b108018112400070071000b01146000070702c011004046800c40081140007403168010a07840801100c0d00d500c0c000070080d20013064010180c8550303282074a04000c90070402e08010a03800040001e0603285016624103140741da41d44c600300c2038001401141030014107004000303001c80940364650303001800d08105c1c030011901c01150354085504d07820120504d0003245003031001040a0a5400c0022100c0e6045000140c1410364440c40701501c0142d14005001194000c244030b4103581c50011560403020001c00014050b2809400142075042106000401c100c2c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 16024700 1250 16023450 16023461
    0x403020a14180f070e0d1502070507092304050a02130203061002031c1104090903020d140a0206070807051c0507020609060403020a020114120703060611010e120706060506030406 78
    0x500702e4481801c2c01c00c00d0300d2040c60250a0700c000c10300003451404112468010a00c81c034a038400500141c400c00f149440701112203410084118000340d000880798140042803103002c0c09400600d00a02452003c1d1080c03002082d86105255003c0341e00b007001c81c08000003442100b50302a0001d005c101c40c0040b03010101c00035441035551038031400d585243c107061a8000300c1030759828140200f400020302c00b0310140308081c1c0b1101402c0801d14604010200d4012000c2c0306840c803c83c0242d006020f00750328284050301040c0748800e10551aa000e001c4c42045581c00112030b035201c0c1c038600e045446030700c410307106031118003541d110798a4401050f0b42c503c9060b243c40d404288030340c809134220f0340c15444551899444c3c101c00c6d2030250050b0400c60002026500982412190308001520140750900e52101400c0c3e54034113503500741c0080d440746810098540e11079007801000000074004c000404030140070550fa04005100d032112a44081422800d0001c00d81c001401018041d090175501e00c1e0034078040c4014032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 16025950 1250 16024700 16024739
    0x5100509010501020d0503010b030402010201020c150a0c080402060a03150801021b15040f0803090a02040e010c02070611150612060108060106110d090b0d150605040504060b12040f0302030403020a 86
    0x1001034000146903100058402401009807030742031559083c41403d0600342d10040050b070566400304000c18449008102200c490342109680541c1d41c10150300c450252180c0350f84090070800b0210600001daa0340008440a2540a003000510382c81d0000c10286244450380c01b078800781d4404595410f1900725880010782c9102072800b0380701026a26080b00d0305409042d0350103800f080d880d0381c2600024007070b84015504400300a00b150014003456002805030340c620807111500313944500790100102d40400ae10382c0508610704200c1584d005c01d4404c1640d0b4101d052261003c040d94a021440903180c00306003004098008080e5022580c4400f00b03181e4404c001c4c42004002140c03c20194a41c003004207114850a036207941c0e8480300c614203922649660042400090b426542d1111101c4004100300d40300700030b150640307a0782c3e1100c1c50281000110381c403503405802090390400c5900c50f080c001103452644251302241481c0d00c0d00c01400d003289140075681000750081042d02e008a06902c11000501901 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 16027200 1250 16025950 16025959
    0x80402011e051b0604050a120e0411090906010806010e04110f0304080306010207090606050a20011514041505120312190e030a020604080d02070b010b03040308090a080a03050703020409051005 84
    0xc10710185980da8135049802629540060244000203603400d0380720501320240d481c00140c07581c0c8440005003105c1c0c51214000d080180062108801e091403001c440d070044013424236000615055001034150580c09840310300c0b5594980c003440118107c2001c0e180e0310840c010040352245032914101c1d40981c801d036013031130144c41843c400107042c01030703401034105445031603460f030f8244020b642007034900c0945070301c0c2c030000c0021424010f01401e00034412a240d4400d01029280c07240e02c3c2c50458100140c184501c40e0041d81849480d101141003124164100c50054030000110b070031079220359065009034507000402402240500c404007001d41600742c3c0c000060a82004003291000e03031a41c4d21b1040e6080403015030000000140803902600141404001d085400740c50131107a540d64034402182604602c800c80408020b22007030541c00f100080d03020000300d0045c25a00a0b6469156481c051103000b0010581c40ba8005495180701e13805940080903104800d21242c288000e48121703040b514010240103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 16028450 1250 16027200 16027237
    0x503060603060408180103020408030d050a05010605040f170c030f0a110103020304030e0d030509030307030206010905010816090207020402040509070c021008100603020d060e100e0a0903050901080402011e05 91
    0xd494042125409039a020720180e18191844c0c003481c0002c00c1060100341456401d000000348050b0510042c40354403080c0300d000401f0310f0301a03801c504884068022804014081c8402d21090b040319180700250751804011110710340005242c035140c0b8140d440300c150036024092240c03400c0140099004141803060b44222000c060240044049002c11180600002d000043c04545804e0040030f0762200f900910b001e501d000d20303c801081c81c5a00031142200168496001000003c516104143c00b51a2030009484021100a03003c11140810701420803034941c0007900408551750355044030000d01c80580a1002d600d8207100c050004516004e00f84d000e261001e1251160b544580b007024820008060311001da241801d008400a401c620003240c0b0580c1d071303080b005c1110068600042e00c24084c40070300b00e40c1d180c1005002e0110860140001e581c050070550380400081d002029107100280078a041ca00300d54583c00100d034a407220103400c552050080e03500042450780302000b000c404901c8110301c210b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 16029700 1250 16028450 16028461
    0x7030611030405010e16150c081305010905030c0108040201081f030f06050709081905030f0408010b13090f0206070515010803090f0109050a030b1807120201030c030c120c020304091401050306 84
    0x31a25030518a541c1000c4d08454103014001f42c8414181041c0d041d403907c034045803415aa01d02c3e2641c081c0d242480c0c600c141c1030003048250707404900c42010b014190041c0100f454400000703400c0c5840600300134188003c0358005040c9002c2940c4025620740e000465a146595a0400c90380ca08400801520b0960a2500151030381e1b0117868600b0071100c040c8010644440c40f507000e904650841c29040300e450004202c90540b0258050180000c3d0070700c0304c000201002aa02000b4591500211503800e00c1e042c541a0b9001c9600b1503101c0381070640550300141d032002a807030880d042120b103d1209a40910520021501c07190008c042c104408040d14000a040b10708401503a0802940c45125440000c071002440040c5403003200917004000e206520520002c1c0486290401c101340c3c00c4807540800e41c0c00710000b55039260280440c140c030281810894500d5040d07004022600349a034101035035032210032040f0002d208004480041005842c100490740a030304412055000a1250038402d20401c000b08a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 16030950 1250 16029700 16029703
    0x5010905040507030305030a0902060d0e0607080405030a030902011e0207060306080a0b0103020f1206010602060708011508060d080d11040801050a050708040b07091701020a030509030f091207030611030405010e 92
    0x140615008002414070f00d296035402c590b1503100605000c8038a850354201c80050710f910700038000c0d60039100e0021500c0700701d4640c0e062501030001c14120030002d5034001d000c003107440441107a4443d0b407185008110491240016680a640c10b03407841a0f0150100300854510b1b40490f081d001d40d0032642c0c09202e020b540300c90195482208035405441000e11038010030040c0740c000c80d64050008060a11000e400c5c148499070b0410341b090b070001d005a0040700800841c194050400e9002d48030f01c001e14030031605070100041507c18000c0900c1d0045004080c08814008460700340d4101041140c024404940004800f00c19a0018460719440f0760074800854141d09003409218400c014640d5203404980c0c898540008500c1c1c0541000140044041c01040c010000c0c3e41e160350343d040031000560f039616454002801c6480c001d0044180d50820700c805c0425200d00b80031105c070040200c410302c40c014062101c05082c03003104c0d0300040140d450050f03040008010540a50b100d1401074000300300c4483c016048a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 16032200 1250 16030950 16030961
    0x50c0d09050a051c0803091b0a030f030804050106031b1a0c0613110306011203021507020607030c02010b03030a030c02060a02070b0103080a11010504032c03030f0a0c08070b0a050109 80
    0x2990b12894203a07041c0710a041039001c41ca40e00d40901d901a1102103191941e03101c03a4000d0718a04640d802c0940051a4007562000000300703044180d030b0b00311725035243d0348940201e420107120060400c054a00400c0502009412680255404c45159130100062401c2040128910302c00c289416810602c0358001c98842400c0e0b038491820200542043e0351442a00340140048000442d4040d1215109200c103072000c10902d4041d02d444400b161404820f070030040c0c80c1c5603101311b00c29007428001003000320b01940441c2e46900000709060129542050000c00e9014000f00540b49415100c04a000100c031641a0810349400d401034083d660581c80c0c90001000b6445444009058009014010000034101100074404200344c2c4c42c0000c881400d480180e400d640b01a1020f8000400307550004500300d8020140a52603d90001130404004001000c03a8423400b4462007081c0590380869902e4521f8060580454440d6004009507034035259071030801c094840c241c03005035031070746040004140c1e000c451150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 16033450 1250 16032200 16032209
    0x1020d03050f0f040503040306020301032004020c0a02040c03020705060906070f080f01031707020d0b0402030d0e0310020a0306050907170a0b0f10090f0905040203120a050712180303050c0d09 84
    0xc060b4150b4038608543c803581e901a00131902c0d40f004100c00404244a4070182d03018622462160307049105000030404109030141c0760350320942c4100850041c0d840c000450488007541980e000c035665041e420194000c1c0104d140140c00e9000d014100708814001081072803089955845109440030303031103001c07180740d00201c480e6440d403860240188081084000442164103000101500e0400c499000c2440c280d010001225101204c8050200314075043c00591480811b80c545010224016400030346c1d9010480c2d0700070b941c5940003800f101d44510a0304550f0240001a28140c0a0304200000804090458864031400da9443e00402d030121301a01502c111141c0080c0019130100030b8804004140c2c1c141106a4140004d42c0000140c282061076035100414106400241518040c0141410190700d0504254250f004000c4084801d400c001515031540d080301010902c100400400e44940c0a024410078108810758000020140d01c00003c1880600b042c09030b801c0882d405000f900c41a41c0c0d40075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 16034700 1250 16033450 16033471
    0x506070306060206043309050111160206090301060801020a0c1202120403031808010e03091c030c080d0b04050f07020f0c060a0e0103060f0303020109020a06050304120e190e0601020d0305 82
    0x410041001d20800481b00d5104421190300380301c0716186405108014035940952079207455928051080a03c10545c0c804820300c40f0510303114420854101081c0190b074000c0c401c0308045501d003400e450940c000c00250050100031036807000792010203004180c0801c011202d250010104403205407003c1442d451b402170407600c55003814199070b01681e098050401c2c0c6014103441e03202c0050b00300700c240509520f6006440185503161003039401e01014105003080c84c2001890403814500203940032081d03555581c1c1080c1c80c0f0361145d0280315800e026210159000390704c81d0505041c4032103141d1400d07078036000d03044a030219401b0003540c1d60f040d5250400a07420070f038030030000c0c40707286001c2e4081c090340c401c1280140b400091190b150741c904000314130241c0003607006030340d500c0041c41107080c0700c003401010f440c45092550460be4590f40e0348190f2441c8022080401c0b040782c1c0c00d16280d444804507001681411a80030a0250f01ca010b8060030031001c81c1c0090044c0700d092032803040b950192280c5030045503100c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 16035950 1250 16034700 16034713
    0xd02040207020607061e060f0b030601050f0d0501061206170d181208040e010611030403080a0c0602031e0604020c0606040c05091002030a02010b0109080604020f060d061205060703060602 82
    0x10200002900400707000d90300803000b08160030005559114440da219101e107403100e80f8030300c14401e01c002c850300e60f00203543d00484000140705841554044c0d941c000b20074a4056500c603101d00301801c0c0c602031280748024560a0034004203a468000d14440ea0300d2105400c1000b44036901c00d601190109001510071541d008800c0c0001640e00c0b5040000020005401d5900400d950b14041c2c2034480c92072500369031a440c085424000308807100c280d180104400c2c941014010300350548161240b21368071000380007040014141800341d0280440c1d5402582040303045440b4682001c81e040c5d50450019449070701003070507000601d10b203414400e5403400b200d0080240000d6682c0014000100740550784041403180c02c0c45898400d556151000d04040800d502554503140c1507131001e400d40d03401180d024140300b0302c0380f001e0102810010303015620680484502c5a000a804040b4903a44551444a0321860803e0008103804040d40450981544504111115507440c0da100b02c00300c0f5118003a101c016006078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 16037200 1250 16035950 16035953
    0xb0603071e290703030e1903020a02090619090203090c1005090114041d090102070506070c0c0501140304120903021009051c0f030c03050c010207061d070303140c010f020a031e0b0d 79
    0x95112031b5002d10407904070f41042400e43c410f840010300c030103401c90050b444011003004508200c0745a40e04000182d03400e8610145280e440c0c183c1c903040e809921241d640c0440051800d80040001240400f0082c0040717102c0300310308030001e250742d0102c90850f02165481d8500f134014030b0700da001c460803a0303c401500300c0010310b410881249410040c2034042151340a02074040031400c24400540100c1190b100c0402c0d5203a0303441e021450750f5107070740041d050221090101003c02034100c102c0358065884181c041c0244030340c40303042d16060003541020b13400807521300f241484280c100303444000381c885c00c40c1c21040300246100c44403000c08564200030300d94201208400000384c0141c041802062180c10000e0418042414090072038100d00c505852668a400980a00c0014452020817000918025110403402d54070080c000078503960401980020001e07207a401c8500a50143c10328002105007559154800000240901400800c002c08041c004030030301d0500216114000d40310102401d1400201111f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 16038450 1250 16037200 16037207
    0x61b0901050a03060e0c1201060503070210050711160815160f170408040603182003030903010609020306011b03090501030b06090d03030507020c03010204120b0603071e290703 77
    0xd9402c030028035441d8400402c8041c400b802c214405e003e560502a02c4140d040403424603400181d11410502c10100300f400784107980815040098100781c2404135441d107030402c0c122a50118044280080e002d0000320104010600c2c0d0341900729a040012920140203503803031a4000c100694850345007441d012400a4128001c06c1a10b030906840d003040018140545031800940c1c8080300c007142d90500010b011f115060301403040d900440540041013030080c480b580c49100000e1214043c2c1c4109035004101c041e12360741001190540003000e0003c5c8040e40c0d86000da24040d402c150341e100d0205400184e0b4016007000b07441000b855a80540e01c0e40d10b114680700065000742800c20724030341c1011040162582c507403036400d6288020340c441e9400099903e40100000d081c500352400b001d105c0d0740100410480800c041042d054119040425040c079600c130070340000d2070050540c0c81025480f0400320103104015207004040116212090b140010040c450760400381d07016203400c014405903080c031403100400d21 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 16039700 1250 16038450 16038457
    0x1b0f0509091f09090501060603020a0806040b130c0302030603070608040b010b0d06030c0303020c2112030a0b04090b010e06040903090b0a09030501062c06010503010303110a1a010602061b090105 85
    0x14180810301d100442c2000c480c034520792030f400070342d1001e803901400340412509201c3d40d4028040ca2408604104400100804c0d1400181c1003611860301c030954018940e5500380f00441000346010304205c2400c02c0900a0040d402c11261700f8400d001e044400149036000d00c0305a4802c980c40140c0c000c2c50307030070491289415007210350a41c0c4c24690350780c1c000c0002803803580b2140155010750010182c06074840c0800460700084152403500745231000070f22001080c0050341c040c6a42100a403c1d4030381e5511800100200101c6078134940c42030400540d00e00303010707070603a859040c0d07015003483c41859502e16040c4025640c641000400180a407601000003200310741c082c100c0e422503850106d2003140c1eaa103d185c04e4600a0b0026564600d03d51150b002291120303c411503000300b40101e80c0d95624212001030514041480301030188200403004a4486900f4000b42c589240e10030610850740800401580301c1580902808000d4891400800c43c6c3c40c034491940c079900b0f0810408140743c11a04401140c1c142c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 16040950 1250 16039700 16039711
    0x30c0309010e030406030204140102010e0c010e011809060503060f04111c0b04050705040f0615050a05070b070302030f0609101806030804082d031204020f03060405011b0f050909 78
    0x550300d12464141d01003d000400041000b07a402588560428544181c1c0040c04950681568581044040d0850300030803000854242400d0040049106030700680d56000c900b10134190f4040004800300c3c47c2203ca40c009415a001034088642d81c2e40c8040600c01400c20079500075014482d48600182149007041d80c142068190b403010a004003030310f95450401e500261002c652540042c841805182064862818104a11003050007170301d2038030481180c001c04200114003001320004041007194056000c0b544100c1c0d000d200c0030010300c1c10030300c024020b41064401e40f07500c260210100e1a64501040524012a80d04140300c0c0c000303180c00303900203101c84040100019030343c54000000c04a80700c4400f42005200c141c000d800380c01e0000c840340047e95001050817a501004003040b800e0b040000040d918070b141038003103004c06904c49000280b048030506804940c188600820002004010341000f00c55848108142d03000e800321700ba082d04c061003d5442400005d00902c0851881e140c40311000f80c004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 16042200 1250 16040950 16040953
    0x905030619050417120a1503080301090507030204170714010e060a030903020c0a0608041403070305030c0c1009061a0f03030a03020d060e0c0a0906051206120f011811040b06030c0309 80
    0xd01d00400044000d1704012042c0c00c9460114040124400b84c5002d9a41545c000c0903460442505654425280340018010b0641059441d000a001140248d0498028008103a004000071590810281c0d035880c090180710b2600d24101c901c541c1c654002e00f80c2401040c40200b921b03040081c0c00c0c90840041a5400094007103124491940d01c803034030303281c40382c82c003138142552100c5c41440e00f170810b1400700c3c2c0042803490300d5a0042000f6000b199014040e283c10000c03201e0015520040c054035203203000d0131030140c2c0800c3c0345070440c000c04000c0ca03544540d801d080010540e01200104d0030400500c0b8143c2005a60140c004014010030503119034000c04da00648500b000404940b50b10100c03065400031110340e04100c0e80024041c00382508080c1010090030145001490510769040540c0d8940c0c014101500130603c21526602111043c8003100070542490020000480e143d50352090345215030005031a9003821180e00d02d810f08181c007441d0307080b00c0054429855278550b00045e0216a0008006a03050f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 16043450 1250 16042200 16042223
    0x506010f08060d0b1509010b0702010215040309150503090c0d0305041214150601170105010e09071205070509011b0807030c020604030605040803060a0e0f07050a0e030f01090309050306190504 84
    0x51103411405d000307030201813035818186014000d02201100680000c10454424894480180c3e40001c9a0707100c038100b03140303404039600c5c4d0346001d03110703000690080e03904204400600c0720b9055205018510a814803021184020304210034041c1141803010003400045081100740402100440f410201c03d00c902440070b5540b41c1c60701800e04106074401d4a551074090320051021941e408900d500b06940490200d00e004d51500002070200d00c40003095901038803240300010401801031a465000c40b039a08400c1c4114681541700400b6644000e0902d8003103502d0900c1e1403071040081140c0c0311281e51186045141911a031405e68040c4100c02c01280e00900402000c40084c400c1e01805000303c0c401c070581d6480b0f04021040148081c0e00b0740050b01c440243c0c0040041c1d030000480317407942080b00390a10580e00c0c1c7c580031080b00c0d02c01c0c01107000ba825109425482c041300d0015070080041a0282e610120380a895200700741c0c444c81c081c0c3c0c135000003a078010b003404000348103070340100c1e0000e10980d0034002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 16044700 1250 16043450 16043453
    0x3070203070f050a0e0114040507030209040c020a0203070b0a02060105120a0c0308030f0c070201050a1101060f030c03060f0e030409020c1c0804050d0906020307030e0d0c030f050c01030506010f08060d 88
    0xd0024070350020701c0d04000c0c201d03003004181081c468079405400c14200f452800c1d070505444984480804581d181305a4a035400714410740d010780d044480340c0401030014000b5480d40100a59074502d24070f0b08900a1145010004a008581007610000c80d400e5000d801c00341d10b401c04200c02400603240b85410b80c014400400d0018415030460f500440c030410856880e840c00310014040710100030b01404041c0010040300700180c0e8032208403400d800c5203080c0301034030062020705280100501e41026040071586000401403203202c000340b40482c2e11809081c000c0340030480d6801c060700d060204d0140d5a1340144420701c00c5090035005000803030244003c40e07484542c18600074a000924011010100d95104203000c00d201080c0b0203003041403410709001048620f400c0000395a1301c0b80120107070410880101c096041c0e503400141c1c015050300244000d1980d41c0301d04111046080c00039044031170340b003030b645101001d5010307000d0300344203541c140c49100a107036030400c0a0b14040c800801459004403d0702a040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 16045950 1250 16044700 16044703
    0x3030906010e07020703020a09230c07060b03150c070609080406030b0102100b06040605070206090d11100c0b0115020309030105041101090501050f040b0a110a080d060e1905070203070203 82
    0x51060980400030182545440303082c2544080150000c02150460001032016031180f0011004954542ea00042c6072202e44c1104007106a61484040f1043e28039014040c4008801010344102d0f40541c03010400e0010f240109951030220700540911400007030300041150410703401070714455018010104822035240ea90700c04560045d00300c0804607a43d248a0281940d0401c055404554030013000c12903498031000154450280c2d1080710700304000040c141c801c54890000351b0b2804d00003d0511141ea030064a406141c4142c000071060082c4a0210818070741441607a400802e6500100b40701803036408d0808210f60445c1c8054042c00b944000c2108c0c00c46074400b4420203110714080c000d28080074050500041111440d540043d0400c6024040c118140e003d0386d0440301181c9110700600e41d51000c50b4410340b000440706d105030b030745401549400c40074400e00c030740104005c05150400f00032079500c42508030000303041903c8141c10024410304004010100382c0c0003541200d00d0b13004480c148050742c0e002a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 16047200 1250 16045950 16045957
    0x30a141207051f230705090303040308090103151d060111190203010608010b0105040b0702010c050601030f0501060509010b0901030905120a170a0e0d030c030908040b0318011a12070803 81
    0x403540d60b0301c800c0c1c00c0c503003902000f4060035011041d4941070008900305520502250311a07180b1141c0ba071529408140c0680c041e4003184c60880000d01642e8445559041030a002d0b0070a4280c0d0340401e04107413103291000d08003507800050300c064040307504d480008648298018400108960b040c00440c0c2c10f425881002002400b130420300b09241021021201c1c4185400d4036503030b910024041e81400d03003a030713050380c1c01c8400d44080e9803c0d041066107070310f21400100c85000302804080c0281c0070302000407041c0100031584804241c0036600900c00384ac0c0e190103100c950b5409216801e0305680a0010004943c0309811400300c01e03001d00c088802e04146521140701940c0004114004245107050f100c0800041e1610035521021030042045101040030031a51100f102e0010078082560380c16014800c2c6000364000310b10141c121410070b458a484015604440c0c1c020b4490b403102c1d4001001212864905009420719400216028050307040c0141c02e001c842d4034820820b150b54010080042600c103400c2019 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 16048450 1250 16047200 16047203
    0x9020304080307020c060301060f08040512040807140901031713090c02010c030b0d050c12030c06040f0302010e2d01020f0703030204052806050309010905010c030203090d0905030a141207 82
    0x1c050b90307030610301d001910b80700c0107240c203901072482400104101500401d14015801040c1040c510580c0e840c41d0103810220400410002d03440049400300c2d9094002800c40255143e80c00304005403909041000043c0c10244001405232561818500c011108a8040c01141c000c198030b50f4000340c2c50b28071810990b000844200c00503950780c089124a45d516024a4a004109854009403445a0344806486503a20180140203103510309842d14014010811540701c164880c041e039410b41814030b05501c140c036255000750010341c00e00004d43c6d513071000814490702000300348180310010041540c100d41ca40d290381c00c1c0714005550a000203480f80341f0321070040c03450910030361300140e40b2070a041c10046407410040007821070002d98100410030141c42c00aa006995441c14400e484c0d40d0303644d4446015142840c1d000f0429420912110300c0141c06401440c01205c0003015103402041c4500122103072802c03031065680c075912000c14040401c0c1c55049040c00a005242070752855007092000d51881e5124000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 16049700 1250 16048450 16048463
    0x20c031b10060902030c0409021c0c050403031103030709060e030a060504080c0127060902042403030e010201020f16030315030c0311040b060703110c03100e0601290a030609020304 79
    0x1000600303000502c0b44a0292120340c03011811804c11345d03025941c81c09203016403610141c1c0024105440d20400800032202800a801400038038080c1000514641052004401050103030f60400303445180401540c1c031400982d40c900250b00c0c50102c00305d079284d00c45192140c05004200402012400728054607100b207000c1c21005a9941500c40314a0849802c03643e00842211014280c0c90455940c815000d4201d42050020a4681c05c500000e0001c0002079114041e80c194910180080c8604c10540002c5900980356210000d031100f00590030b03845240c0040303009502c200120035038050b207000000309a601915001486100000390000da1041c00d81043e906c03414030b010100200030224010704011101502d0a0081885a80c0421494011302c0c45c02018400e0803000c2c142803190800c20202c070b0b030900504840800142440000090108228820040c0915800031134200380c0d203680c082c110401000000003900140520360510b40001d4070910405468410018540303609001840c0194010f56 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 16050950 1250 16049700 16049713
    0x20a150204150914010f0c03110304090204090e07050103050106020d080c090a08070e0a02040e01030f060b0301020f0a110a0b0c0a0e150903100902090105060a030f0614090702010603080a03020c031b 87
    0x45070543d40d00b9020a07440c1c104401030f0818100ca87c3d1207110641d00690501708884005100d08502e4150b000340d4001c200c0a510104002513055140c0c3c010f0101503050109031081c0d1a12880110180c1e6401d01480c000f6074483d258a82c2c0a43c819011550310048001d0b03854245124000020004025988444008d43c0311100034020031049103d9980c02101907803086191910700070036880b5140051001030705a42d00800300cd07052040d203402030101d0807001802196509a504082c040320f40050450000040019071131030f80402e40015030911070780d0070050303462080c0d40d180c042c204a40d01c825250380401c5008201e090040d29000c41d0245108141940180c40c0c0780c00c41d060516040701041c0c0c17011018241505500940c66050b81c25042d11019151203a85e1510380800760040c18031403614914242c5011000500784502c039500e2511204103e40190f0203498040c1c1c00c034240c0c0c41034040030b40600010842080d160f0f0199004202c806c5402b0143d81c2071104480032400003c51740c41041c0000c1d004003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 16052200 1250 16050950 16050959
    0x906060b041d06010e040c02010e06071215050306060913050d030204090b09070e0105030901061a030106020c01080705031f0522050c160204090614040f02040b10020a1502041509 78
    0x1146a210303561242c914800c0180380c44800242481021229140180d55880c1c80740ba10a2007904151906042d641c1124034505000c48010050750080817104142450b0000c50405c100103450503074103d55009005104644420b020030140e200041c0420f44590795070400140050024420002804003a450040e01c46180090100c15280038150192007401c1100800400c507410211203407200c5030030310342071f0b03241d039034840381d46004040b2034000c1c054184a00d095000108030b2180194182d5186a0035165050480301c01502c41c1c00f8145d4041c00810030a000003400181411560b4880214114284403c0350b0768002203684100c03250480d11020304680d01903c140c400c5130140d04c0e044a800c2100a1810b000c8070400c004042c11100c00900c01c0d51116983c0b414450141c01440d10f6a00080303c08036a400d080c03620b44001e07002680100d004a0401185c10164500403e100350b07c031503242c0140400a0050703880c00150388807481c010040e940c3c20301020610341020b29685020182036200c12501c141007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 16053450 1250 16052200 16052219
    0x615080402030610260111040902090f0402091c02010509100203070b0c09030a03030509030712080106020d05040b070212010e030a09030203060603071511010902190303030f050912070203010906060b04 88
    0x200f82000c80c01d42ca00041182c0e07240300b0317080055481802092000441100b206a0142a0b8410920101c03000818003081d00700d00c5070b000b0321030311314205c0e40703900300001c560184426801003501c1c1c5a0b200010b5a0301694140700010003204181c0705140561500f0758882c0028813410070084801c0041e0f1012840008125420b1081900038200e030038954144030900e40026600c0c41090002010580c07035030045162401c003081594611030f8084064400b055142c03800914407982449654014456865001c015a019000311020340700101c0e0701d5071a01c04c10703409000781842070002c2c5003401e640e20400604c086c1e5003031001e01844210f40c0d4442d50000e145004040c60144c0c0a040c8034480e8202a004022141250b501c0268840d82402d110300111003e4141a005000b5820040d401c4100144590512100448600e0690b0300c6900d041040d644100b0820003200c800312800e4846900048007641d046008030f000d01041c910080011038120180c0e0ba62005a80c0c0c5980024600300020805200f02c40b071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 16054700 1250 16053450 16053463
    0x2e090209040506030718230703021309060803070807033b01050c03030402010c140102030c09040606050702090606090f0a030605220c0b07081b0c01110309060d0f061508040203 77
    0x1000c0300244100390404441c041ca90040300d1300c0298059482c1c0d0003021100c0b00000108440301030b0104410380e2320b03055501030017075480004078000050288074040340310940b40c030808065038024001035041501c03a07a5140d44940c01a1016014040d0300c240b840d01805400c110440442c0713212035148910104041c1c2c0215076400600b00c00d052110a20884400071400415240d00c84c0e024a45a030070140300d030800142c00038007490380300c0c107a50001081000800e0804001c0c00300140c195410006240d80d420308032070900840b07000079446074281000c03500701d01c0d0110141c031403103000030030024440d0115000620440c9482d4022500b4903141d10401403202d11450348102c2034800c011120340b4152141d130310400048001e001e205a0390310041101d10130b02c00100c040e5504000038100400800200d5020280c0c0e6800110440d80041d90307031028081c2504010061340c085100c0a0207640c01c14005807011000307401643c1c3c60100071a694070f0005600440c1860381810030740309486292540c1080e0040c117040c0346 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 16055950 1250 16054700 16054711
    0x140f1204030f110c091b07050d030e07060e03030a030b0310020c0a11060c10091e0b04050c04060f06110f071503060503010207030903120e042d05010e2e0902090405 72
    0x10400300c4100c100b504c4031401c1e180d01c144c006c1100e400c880c15406c40c4002a0003115400380c018840d01e9202008039405500c0900c2c9810684204c0e0701032551410100c609200120407260542c00520101c00c81d24000c0d0850401180020141d80740504088101c0040307030070802d403001980e40030b10b06080901c048048032400b0498191703042c9107855010b415269490012000c840d011540e60701c01c20301805808611446581c002c01408103c460303a40c00c0c070311000f1500f580e0582c2c0e1030040b007420301d6a6181c00e20a179412a8512040840103c2c500f99064503141d440d1100c41c00180903060319000701e60300a1041304060183e0219807034084c0c4030010700030700700d850942019002e070b0b104009020120f5000402c500490750304c110755100306030719550111401543d0111a5030000c0c24100d0411000b42400141000301e5003516424074030404500c0d07a42e041c0e8800b032160000a081c500b000c601a4509203c5502c039040728940e10108240e80c140c0b10303401c3c05425a00880c1c49503070201d802c00c0c252809000b41070b0040d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 16057200 1250 16055950 16055953
    0x60e060304080a0c05010b060415030b030a11040e03071a100b09030a020f0607020a0807080f011404020904080708030a0518150708060a0f0909020306090706140f1204030f11 76
    0x14074142d036540c0c00600c6030101900c02c2c80300c0d4010100821109400c007452008020b00141c2d00c0d103950307507410400074007500170600100c0d080a401422908001a44804107038008016001c2d104020301884020201c00c110244240410000d220108862008010300888861000c07580e611f0081140342108469400403120101d04002c4440d40d0759000956402c03951b01120120680400000050154820304900035040b407075402002a0a1002042e140e04a90405080d180411452890942203440c0410346813140c0f22035401003000341c1460082c103680688600034991905105803143d041580046400254040d07d440c104252940c01403070400228449a00030691103e40c00028000384200520050402c09081d0000d62203580d0901080c2c000e18072091030101040d00c030115000503004281e000da00900ca08000310328000c00001d5400100c0d80b86a440c240480950511104564001d024540c8180c4082c42103540700b1a440440c980143e10036201c16241c1146410044c000e615580d0700c010304c5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 16058450 1250 16057200 16057207
    0x703020111060c07060f0623010305071b0605130c0312091a0307080a060f03050102030a1104050307060e01030605270109020a0c0809030a06020304030809060112020d0f0606030219060e06 82
    0x850284000713030750016600c40004a4120b66007602d17500101403507400b50800c015141e02d119502901842c00010100c001c1c0c2e001e001d1581d4942e000c5e94003c2a0380700700703500d50f9110000038022a51590009801207143c0000e0304a200680d21241000c441c240c2090358151290101004055004010080144104004034005400e104040500760000a24100911101d040007510141066000d000548414076207000d080d5240d0412900135081110325451103843c202d00d840940d80000133540441300000c0040c00d1107800c02c00c08540c49a0094a4a070500d0344903d0082510356940b02100103403e1b1054031040444000c02003415441810392103202868810030080101c1c0b07600c40c06d0003661503046140c9941d0f8542d8080441d00e401c04002c800362282c0e10205c184800c142c3d102e1251402b07544a030084401c1a41c032080d002c21403510402b8001d5103c0761801000c400969007070303d043d203000d008000024030700740d5030b401041c802107a6846005110051041c01d1107010740010759400d03081c405503000307803d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 16059700 1250 16058450 16058461
    0xe0f0c03070f0e0303030115090512030405210d0804060b120d140d05010b040305070803180f0f0409030806011206030f060203090709021602090601020d120209060403050f070302011106 81
    0x424400078041c0700401840070069503049029030300140c21418090201c80d902d40c0d469140c608035581c0390680c3c1001034844c81002419186c4503910816244106001d9480d003843d000410034060300c2d03804424000700d03040844071070425042c02061a1a00152188103451a041c5020400c03284022100344c030607003e4034168140d004001078000742c050300c039080441c0c90a807040c4400c0214040c069110340c00314100000454032101180250084034820811030b00c000d503c1d04280741d101e000311700000c41001000c41041440d13181810002940352005441354802c4c0170000d01143c160341c1e440d9410790215219900740106560700c000b450000300d140c010100603503811540ca8404910b900c2c1b10141c007503134001c40840c0d41070400303003e0300c3d0040ca41214215501c1e1110600300681a0885200ba8410402034002501c15400410216a074070340c4d9a40d104607070f41400f000c01c0025041907013291340000e014031020000030810002c0c501d40003102c0d001420b20740d1840c03000502c00c43d83c07400c40c198590428401d00c203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 16060950 1250 16059700 16059721
    0x9091406060d021204060c0905060408030307030504060b030105090c09060406051c030216030b06100306060503070c0c08011e0b030a050a030f020a0b040f050f06011a030c0d020301030503040e0f 85
    0x250000c1080354202da070340d0a03145031040a409404403100c103008102c2e09110030482641c0c000c4401107159124854040e50728810800c0318080c52080b0741d201d4000700b000920040c801e074401940710380314010024400900c40701280c2101c0080319504211740c441214010946080724640d68007110468083c8402420140811480340710074098401103180f2083d1601054000d12420300d43c03404031200c0501d40c0e0f0781d0742005e9100c00c2d01516a20700900c40c500385035074120711901503201030715003e840e128a561074034041262058441d00003910040e85061020500407020300449464101c0c902081e0301102070302d4040c0007112840c004e0588a540300341d00c0c1c0000140041041080c40ea01414001c0302c10700158070a0341040940c07070004003511115070820042091103070114030400d0040c1c0131105544e1014030031036070301c1c0000e001781100d5480603800c59421407504001181e00c400b00b100001d05240c5884000c06c03c0e40c200381c108850079000490240184500f09041e40d5001c00800348110a0381445007088 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 16062200 1250 16060950 16060991
    0xd032a030207020604120c150804110d06110d0b0301150807060818010606030507110a0215070c05040e0102040305160b040e0a090b0a0e12040f211203020a0909 70
    0x480900d500401d0100c295592501070720001c00142e0302c6140300102510700110300300c2c0c031805003030310012104203820400c80c41903910300c0c41554000320307100c14905050104000ca0075841c0d0220750154454441c031400c0c1003054040c3c0602c01403c1404103800b00d20358105429510324180030710344103000c40410048864009010310481c2e03100d0405558035103980740a40701e0a003189141c48a5517080c50800030b00d6079819805141301c3d0a15550700d0207221002d0352003544406200748082c0d40224107270481c0c0100d004040080021512903038801419a13945ca020805841c0fa00c4014031b010303540803c00700148501400300404041c034905107001c00324204603140d2464081c1d8000c4815055480c00010720b010041d6000c41d201c1070301718140003d44d10782024508080c10300350400c801140281c48c40306101c2c0c400c640a8505540c88a295280001e00b041d05149143e140112341101200141a054000c9101e00d01c01041c4648242c2d009696040c80c1c1002505810351640001c1d566071a14891207541d021070440ba = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 16063450 1250 16062200 16062281
    0x60106120509060112030909111215010801090e0106030c080a0c15050304060209060c01020d0506040b01020109050c0609040b0a09060f060905030d0804030513080604050c030102030f011a0d0e0d03 86
    0xa00a006681407c40d6001d6240e000800030034603208143c4102c5c000d142c06810744040081c010101a0380302d140f030307614559140708076901042d940c200500822045411507103c030800b8900006000303640f07880f040c820705804c2d0702846041d04015020400d0000078650040030309100c5510304460603403808010584d110041c03010341440c3d4081b84841c0320f96908801c9508004001d8000c0d0740b640b02008030700000303010507510148030750f01c0c105042c01a0f50040c018034030000d800c000540010001c03c0d090200d0f55100c03004c15a40250344080300b01280d561005070802601a009001403400e04080d01c10480c03040d40d400000c1070002080003040a640d0025100000344803d151004840e11030745803e450900481d600400500b01c0c003200464552070002c0d10522403070040c07003190040b0641800745800c038442981c242e00188895001400300d03e0104c119a00690034074078030140b4021300f045c03004040b84e04010f0016100d0304031218100490341c2c50b014401842e4545480400e600499000110681040c100c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 16064700 1250 16063450 16063469
    0x30402031606030c020c040b01050706050a0b04051303030b0405010b040b070507050604180b0d02010e0603090a02030a0f0b07170115020c0604080604030f08090303071101020903010e0601061205090601 88
    0x5011914140507100c030201d00010760741d450946803000070307015012030500c0200603c90301d99044114900750048258000d41a19000c0c505421a250480900b40050440c000652150b030004500d80310f80c4600341c40f42403080c0404400b2165454014140c03411141514070950800d801800a181d140003258100d5411140081d65503942e0300c0c20310b081032082e03448180c0c8240f0205000480c516407055412502d88000d00801040c2c036490100040310900f0000070780050924000c40300070341071910095400c851844201c402040d00c590009152041000040340d50342590f02c0b140040080c915030664100100b401c00640105621061143c0c0b080141305040034081184104c996050091044041901014003126078541e203e0f444183d03515001d8904400003082c820021a00c07038884c2000d240a46900000b451858807424011138403544101642e8003155420840c0c4605560244603c00d902001c140191240f589466800740a040c29080400700440c02c241c01c0044e040000305415044d91704070107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 16065950 1250 16064700 16064707
    0x901020301050f1c020409050606040606020325030c0c03060b1305040b06010806040914030309060106020d0507020f15030901060501090515040909050c030a030e0406060302040e13210302090301140f0408 89
    0x1441c10103424012a0040c0d0080d207481202018444c0100e0340e05d20842c0241d80a02001d079540108030703624800d541c1e00f965030430b040c601c007020140c5034030000788101170082ca000c0e01c50041548801c60f0f081929802114129591800c803a494104407034009901110784004201c1482c050300c4010201c1c500910660401c80b86400088032903440e944044c1505801c1440ca10181640080c00c079902e40c0180d9580c1038511404000044503880011460f006d06031944e078042c11b00121b42e0a210801151030718095020300074440d45061201a08050f500c81c854040000c00c102c0c0c81c080016181d9801508181d0248226500c61030282d07200710700322011240314070303800200a0141c1c1091400e15031030082c0954980954449042890f0340000c90752510f84003140c041250307030303520780095003284141d1040410103000000054400c11501c9803128149004070032590114440428988499000014140129a0124580300c0314182403044480b610140415003245090013840d041400303500500040007506c001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 16067200 1250 16065950 16065979
    0xc02090604020c010e0f0c0d0206072d03030f0608070609030816050604030f0201050c03060a09020a0c020301020a050a09050a05030307150212040b010528060309080c06010e0106080901020301050f 86
    0xb81c0c100c0c0d01499200008022004580d12617039110031400c424200c0a03c00d0403001c80c003510f4140149180258000c0ca000c0c580f54083c1d4659104000013102c80c50300600101c5141150300103070120702c41c45440703680c00140c0c0c009400840303822141c1c660014038103580316075400d120941d0081e10100949421022013500c0f0103c080c0b80d48020308249800030305c54040d10040c13100301500704000e10b0a0110382d4002303103c00d6403800d41502e09404100c41040d403086851500704440400d0303030b00900c8401120f2821400500640c0c01007820781c1c1c0112001d20000d5400604020342642c40130030303200070b000b0403943e000c4180c2c80c1000103a83c80c014004080d101090040640d041884946d0440390707400c212880340d4407285000d06040070783d8002445000d00034540c40d03486040c18100307010b240d08440d017004d00c0c803450a410104110001d084024046800344420018900c0009040041030b0080c008690501920740c100b940083c0401d50241c10030700f043c3c0c0103000600c90f550350001c651610000a0f145114030352402d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 16068450 1250 16067200 16067209
    0xf0e0f0406030204020d05010807061d01050306030114040b090f01020304020a050f061606090212010207020907110f01060806070207060507030203031302060405061810020f0a1103120c010203040c150c020906 91
    0x550307000944c042e2000071001514900c0d600300078102e80301d041c00c3d600381369510f480580e2500c05400d501d280c3d0040143e651420784d80a040610340017440a40001600d00041845c540f03509800e5400703440560f024410080601c4003005078110a5036a80001d41c25030030550301044440c5441d0127441c1c0700302c8001c0210240d40c0c807000e0598001d10000c409141c060300e020304142d0001d0002c5c44d4142d002d1400003d68082104050003190030865000d044a07000e5510840c1c202e07a0f96001034514507840c041cad1030001002200900842003d442d0b00f41c06010705040075240640303070901561000003800028804078010030b4010055a9110b001113075205406186440000c21310720494104e036610050100301074110323000e0543c900a543d8000c0d508812883d05400c0241e0b1b650020900d0012242d00c82c0021000148880c01d191001050280c1151007014110041ea1080d420001d68501203070741c00f1081205214403010700c4401890303c20714081100c9402800100026000b21010340200004000300d98039856 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 16069700 1250 16068450 16068461
    0x2070b0d1503060c08060603040201080406090302010b06070516050109080304030b060a03020a06021b01051318020d091a10031208070c080c070e01080609150903040905010f05100f0e0f04 82
    0x908a2600d03081e540c807442d00000420303105050400240d003203000100c003418884100c81c00303250161103540c0703590754503034418025205618085007155203d103160320f4241c56900103021503074030540180148a0b09208031202c0016107034003031410407140c0703982000061408412a03050360303003200d070004d05a80d0f440c4c04a0511201d9a0009401500004001480641c003294140352004c0000320301d100865a080115001d02174210ba401c040d00c6031035010068144580d51070107014001e0200035040c222503d40e1202290340f000300968070a65128242e41d0301c032a4001005178000c003d65040609241107490700910004a207c0103400d200900c0c001c140c44038082c43d002a20700f81e2184c9182d50301d0407446140b64403a1481d205590505402d000042501ba02c04150244580c150304d004001d03000005001c1d41d04080040e00105450000f084081481c0c40302d40181400307050a02259803155160a042c40708000d489510350042040075540d6603180c0d58801d0180031400e104644020484c129007002600030701 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 16070950 1250 16069700 16069721
    0x11412010917070c0305160e060406150c0507120b0105031e070911091002030d06050312220e01090902090603010209030601060806040e010f05040302010617030901120608060f0402040b030c0102070b0d 88
    0x460b03008103060801115007c8070079034001c0c40008959403030700028801520400c4c0039201e604180485181e0440d0b205186450549000b4400c50b902c00d0f0b0b0f108000c03e08030350401402d955642c0340c01c006228500382000304a0030a0802010650046413501a89445a409014210040f81c8800700001c480c003154044c0d81c1020340052801605280702500079680340e000020981c6003034141140000d5074903001c03800d103c8a0210300394039850825181e01c205a0481d20100030f03516101d18039804543c0324803030102503003e0080c280b40050340005074010060004401844140310742e004118500d19500c01061140c11146141400c4503c4e8440c8000a0050318900300c1d480d03001c0d8130700b840d000140c041e1074020314007890180d0001c01840d621225404112118051603036510790040221545951260207501244150304400003a440c0d141e806c51802e002d4241c402c1d070a130110b5801031205500c2c013840340c0000d0301030840040010013000e0300040c0d2250501c0c030031010140400b007000319007042940c000c1204070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 16072200 1250 16070950 16070953
    0x5030d050f0d0f0c03090c0506090315060a0f090c080a0506030a02091b0a03090c06020604031b0c0504020301060e0f030f0d05030901060911040303080a020901050306061303050105011412010917070c0305 89
    0x341c519407001001851b088900b0344a0018507400000c8600b0444112980d03190040d010b071000482e00741255000c08006001a6008110307148000b54900400c2c00c03c902503d98544049070000f66208004d20015010301851146484c10050145c0c50342c0004000e40c4c1036074141c5200c400c031340d1101c11000c04402100d248c0c6140d03040c00112200301d158181d12103084bc501c15002c3c0101e107611144e04036070b215003ca50080118035060641c50108048600030802148070704a4a8603540d00d81c800314003070740c0007a072100000c9010075082d6001032601801d14110700c1d82c00e4008204541145038001da64482d19100d0500b481400808540f202400f074000801402c8001c909000c211a528820511940948030680010303800902041400515000711403100105a40b918116201d0804005c40740d07115821002d00307418804000000910f083c021a8000e100200319215180400414424440c804411070040740e41342103a404000fa020001101c00080001090f03511000c481c50110402040791b040034059 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 16073450 1250 16072200 16072211
    0xa090e040213050a09030801081504020d0f020310020c0f0a08030105010c0f050d020309130e0a030503071e030203011406030402090a05040c03061109040605010e0d021002120f04030c05030d050f0d0f 87
    0x56800c0390444280148203643c2c2c0c0300d0702da03a80e112031511100c004810000300c20f052b0000c0340241c640803884000710b901030345511004d441c650740007900c0e01d0492026140c0454002c15004101241404210540c00e4040060310a120042da14440701740300c1401030a0600c8030b10400202405241021007046c41ea020703040f91003414030310038013a5480e0010041a441511045001c030032001844c06003038a592180360052044103485d59003920681c100074001000c02062021101c034004071444582c05100807a1070040c0e50754101050a0541d100540940e40503520030000d01006898903a607841e404500c20000107517907192450030168010746039001620050404000d101100b4403d00213040e0544100d4080020650340c0005644100004803010b512220340c0c2c6501000d41080c94246841c01d0032481a1002c94499400318407040d0068002111810030200e402d20070082881051000b0b010300b00c0c001c0000091800b4020711500c1080d500010400006c00d0113011202182c02c41e6465480b602802e115 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 16074700 1250 16073450 16073461
    0x90406030b06090c040e010b09060d1401030c0801020f270303030a0203071b020306070c2a03060c08090a0f020406050604120203070501140901030203040203070312080406050106050a090e04021305 86
    0x6180c0c03801d0302c070b0740d101c0c2c0b0f0810040b4008401d58411102121405142032a0780da29040008042d17800803004640c00c14030410032903000309510320079905038003078114400c2c03820750450078110350300480d81c0c001416a81c810000000c8620100c003e48080b22044070100c540c83d810080c80c0c07050903c5100300107404d84408828004a501c0f141c019621405041e524500e201180880c6070882410000c0081d4140e0408808a00c41c01e114080030301d00a80114019545404444a0508000041d0a920000075808507007031017081058002c0d02c8048074503260200150070304142c49911a05400e40040281c000300c1c0e031110071074443d904100000e120003815551956a00c4030360004030041044100d210f8000c299001c911580034034140b00c0c2d070352007030314445007031103401d000640080d4400b40080e40d01d48150000000018035110480601c0b11950342c070100181050b1500c0c2064820681001c400c1c400c0c00d0000d00643c56006009000312510400070030f01603201c07800410410391440d81301075801820a0108036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 16075950 1250 16074700 16074713
    0x201020901050d2406020f0f0a1106090d0804080a0b0c0702011403040501090b010b0a0f03051014030a06050403030c020d09060e060307050d0c0203090109060201060b0904020a0207120309050901081903110309040603 94
    0x1406840804140c424420423039241d552565282072005000710741c00144800c184c240351001c0c00004101901802c800c50541e1140181074019510109480c0d01008000003004120348102d40c0110741c8940250421a00e40c0c0040c0511a40d40b842c0c281f1484080700060600409401020800c3d4114034508000c0d40c68100b000c42030340c04558400f021030469510014071510030710505102d1180910819401420201d0300c0e410710b00c42030140c50385445043e4001011070014454a4012482514002208144402d000c0c0c00d01c0440d59228041c804044d400700511500210300e0003450704119071541c0d40b03035982c42d030070743d0140075400c001c240c100e28041043e158107800000070a1307140d0090700d1b5105100c4d030740c00040b07013641c020380901580050107010040071814a0f03005445003e01138015100c409807508040d80100300d40c1348050f03000880c903041c100050305110a03080c0c090b10301e01006d4550000702120041607456064001820800c0c02410301364107100a1090304c0345000010414040c3e25a242003c8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 16077200 1250 16075950 16075963
    0x16080301140108090a050c04050705130803090108100e01030204020313120804020112060f0504091110030203041a04050a0308090c0d0804030605070801060c03050304050304030b040516060201020901050d240602 92
    0x16022407000008180c000100185c0000025405801045242c0441050001518001e8440820720100748840340d011070182040b2005404034800950b01e500944000501011010b402207032070310717150442132000525000540b03040d00d4068801603034a84075418855940711040c40c002d84411910f030030303000056a00c051070038040c90003603a52058500303141d84441d00b2542d643c4201407410725001000c01190406030400180320f4000c1141c422200030b49400b0400d0342c014490803000203035000040100b004588152a400c5038064004800b0620341581c50503903413140da13000642840100c0b80020740c600002c01202c0c682110280110202c84050715101c80c040d005800f045412606280000702e2441c40342e0700b6907042702c110360740d07451b00700d0324a460907100c952024100360b5a5000401003c00032400110249004a03c44c0b0020039025520b1000c001000d29a501b001c011a40100003040c4540c0c0d104050712020541341e0400599000c5c0a04000500300181d121425481100b00d0002041900803844 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 16078450 1250 16077200 16077239
    0x708100e07080405120406020a020f03010e011410060305040308010b092e0207080f0606090c0903031308010507020106030c09020d060305010518070b0a080408030a020702030a0506150d0c060516080301 88
    0x102c92000e0a40b05000000f800741f801500010791080c0308410140c070703007102d81c0d000c0c1c440050000a20b10074450039050a40b0140c074a0000c0d40c00d42801485100120801d04100070800c5240c02c0000b030034599002012444e0601c9680b04510000c904246240d8444815a40703c907007076802c21840e04500030114014400010280d00503000c1c62000182e032080220b010355544841c1d0300584081c0d601e12081040d002800b4200f490301c1d04091000380902d031001c100522040040382c501944680c40c100c070142c01d44400801c404111b90410f10108001244010343c0340980311480da01603140c01080e068100200082d9101034299030030001404403000103a0a060f450841c00b00036181e006444500041d043c0c400c03500340a0014200e00001800f18004c8030266802c01c5441401502d00807454000030314091400354140c4550b00b2820911a4000c500c0d1066000c0c01400d581d100000303200e989500c101c000c8a44595010f102e8001075801584000c000141d4500380c5c0512400c1c0c4a5842cbd00b04c0b070b24100d040044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 16079700 1250 16078450 16078453
    0x6110c040903031a12030901080c2203021201140105060a0210020d06081e060402010c020a03050d1101060609060c02101b050607030b121902130903050306040b06070b0708100e07080405 81
    0x162410301d0801980c59060031805c18019483e0007075410046408440040c8084040d03c014404101c43e0440d840301c910050f100110612441030850041040c1a881c00342140320a07803525a8407102c81540201480c1140d4044510544501c10264203a080420105c002c801e6140b0001d8038043c1612359a105106aa82a50413104c2c48140e08000000b60400c86036401440c0d800000090700540c482c0f00510b445030310107012801451798a40d2400d141013502001c3c01d0100700c6405200d41c5c040e000744920b1000b818145045041c0a2815202a2201c01c1020f00a0b0003502c1121035405124004ca030300041c50011504141c201688509100f629140c081c2c41ca00006814292100ea807450030a00f496128a80304014084900281c2c000e1201e03222007941c00c9030000031001d1030701c80940048c0b183c28a50340c02629050b68034a8984100f1044861001035507108800a0001324003280e0b01d03800046d40320900d4103001d203d5860b40542a2100d1030242d000992041c201e504001800c0c0d880139a090186100d41c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 16080950 1250 16079700 16079741
    0x7082a040f030c0501030b0a1701090f030c0203061b0405040f0b0916091413050712020c0c04050610050f0c0309060703030b2d010f0c050607090602060f0103050706110c04090303 78
    0x4501f554060048194002c003117043c18009050142004000c5400c2d503000028803000d180c0d81c001091599500603000304100303000a0b03046d4241401410341c81030400c51240c0350b800000c400315505010718000e050085a4440d0b0b121200ca2980c0e200416a042c010314655541c580130b4240070424080701c00101c002401e1010009807074128070290050284000c08402061342840f004d903006080040218040164285203200c54203843c0c80200b8500360f0480140c07814441c10410b11041d0740000e802c07036015000544c51000c6a60f8000c09440e8609100148669520303940c00c00f8915500512b05065131244d40011700c1c07410140c142d4080b1100d20b50a40d084441e05a41c99500d141d4140c90700c00d03d02854840105400241d1b00c91a86012810f8150504d010400c240342c8032070b45001000c540ca0340109074081414448183c0400020364068500e0a1003515581103640d10354941035540304080502000c001900300180c42403000c41214038001c3c0003048184250300300103000c1e251075104184110700c41c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 16082200 1250 16080950 16080959
    0xb1503090f0609030a030c0e0409030e042a030b0a0b03010b0703080a0b010207051207170f0106051005090405060120070e0702240a02040b0301030609020906040507082a040f030c 78
    0x1003906031140640700c020718248000b81000346e001d01003c000210801000e08860701880d961480340c0141d43c1d00995410000020078414032085940d15006c2251703900c1003114100c20455000c3d41021a800e5928008c00e2140d0b140c004900030b4021a080300701c440310b001c0004a2440302d440040e0039424000d99a032140c68031608110000c541030101081e0041e0400203060240313040041d19041c0010f0080101d0380c0c2030350344061b00202c0d9140b0495030340c407682006c00d6111050009000d02409400203c4da8055903040c00080a0020f2164240c00340c05031b0740b581c000688582c05403038940d00d402c1d07038078020b42d000d40c8845540d01c0d11940c2c41d000f15682c890740003000c6110f880c400910074114850700150f1142c402c504209043c80e101004100070340ca95000c10010130440d07002d201450081d88248800318a0808030f104121940400601040c0142c0c0340c0420040a0359000c80e8260300642d03030201500700d422940e0312014001c10360140c60081006e00180029400c0d0605020740200c5e4094184810115181c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 16083450 1250 16082200 16082203
    0x304020f01030606050909150607080702130b0105120603030706090803040b0f0606042106021c0b010c110603150a140a0e0403020303011e0513050601170c03010909060b1503090f 78
    0x150080b000000c1d018440d05034a030030300c01f00302da03000100765843d80200310800c0001203a950021034104e40c00507010500100b18184841c00c86158081d240c010311403071400310f0000b0030b02c2c02680130b5140c50340d4140780810399949050084840d06600185c040c81402c02ca410582e52a51054804903042c02008000070b4000c14116207141c00740400401d0349141c40d10303103e9414801e141e0740185066811401907203000140350b510040052400d0715810390840c1e00030483c0202102e81a8086a040c0030103031400340d00141c08600c0c081014041200c0c0c8949075203411058203031140c2d8809119410011078000821511900c004180e04900c080303070566800350b25015401c18120040d0390080150380140010702c05805094111000c803900120060b1210796104002110b032544000c3e003900c1165074038144041c55a001822288100802602441074100000445820700c0144944803416540d0426902046100c3e040244002d00081c21030b06180d600100013903c0d54001e8500d032181b44141e8a01d030070365000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 16084700 1250 16083450 16083461
    0x20415020f03030703020705070b03070f020d0809030a0819090c082b0807050d0f020301050a080a05100c051201080106080105100f030807021f020d180311040207020307030f0302030304020f0103 85
    0x71800095411500c4e50310081d4040e4011020480e01c9002c2d09002151000e80500514420106036441102c480014080681000c0300b0888020421008504018907054000b0803141c04120030705e00241c844d80d480c0c4107404242140b80b1400f040d01c2c20010404107024074581e160080d00c0c03586c0103580554206c0400c000c0d1055814442c4070a0940b1b66150b8250240540d00641c0d112106082551030b01c0c20106610085800300008603207100e50205c01842182000e08080024000f000c1c020509501d054a03a16600c102d0810200c030010340310219019028032960640311741180c4513018114658480c00014041d00c901d020300c5180350300e01000a854000b6082c08001281d40d1071110044107400d40d1243c202540c06000300341d030010100080f0700c00040f449a036041d80c841099014119482e4110001003241d41030310001c420382640601c050021440c42e403e05001d40c0012500142d66240601c0030900b0005180c0c00541210411014103003819004002148210720880e050002010100700543c1181c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 16085950 1250 16084700 16084723
    0x90501090504090f0f050f0d14030a1127040c050301030b0403030f02090a03060b0108090708070603020d140c0a030b03060705030406050a29040608071a0a03090b040602041502 77
    0x4041400c1088582840d51000c0302450242c800302e403040d0780ca0344501441e04030114046840398442000c0324183e0f4024084140740d84e00d50b00d0640070071413600c1c00214242c04041c004425050303072441c0f18100b1100180c11101410442e4403800340c109403c464140711582c6c1030203403c1c00307a400d000000080f6441102164141e0384d1100620140340c4035501c04500070022404100416035080010743e810b0f42d41c08051000031441500e0104851f0b4404000404c050700240100e12241c2c04a0303000d0103e8403001c03d4181c140e84032441c0042c2c403001070b100c0b141c1c041d01000e0004091004004240b29880c0515002000c14168544040c045408904149039840b40121220b6001507401e001040010700e0301c0c0c2085800c0a0b2110010907100c00c44648401c80e240340c112034540d90f25030302c404010340d820235000302c1e4003e04091010b80403241c43d100c0c03681358590341003440404011002626100380c5020b980000c02098100016022034a402d190000007035029001c0c5080481c8190246040c1503c001000c20409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 16087200 1250 16085950 16085957
    0x90504050d0c03020304030b0f010305010b030a050c0f130204030804080d0f0e040f09150b10030b031b03030d050702010b0a0b1305010509120111090a1508060108100801020a03090201030507090501 86
    0x30710500004a4030700b0200042107046000c01c22002020130b02001266014240c041c40c01402940340d450100e003103070150302d00703140a90400c0100700082900421f1051f100d06080e64000300d102d80f1100010407184015280f0003403171348049004828424440c000d4010b884580301100c40145450f50280c3d00c204038541c4d00c2d00000c0c1a0b0760380c0c48650410b40c000244071000030001141d043c0f01d960304c180710310426003004171009075101100b044514103200111043d03046130504118204040020070340321006840d040e1081000c83d810f000980d01c0410807030b00c03a07130a240000c02c480e042c4188000e0190451800d6244148240c15010601924460440b07140400c188120450703646400010b40e0340c2d400071540c56a11648254064050113000c0c0201d1118415011913595a00569020810010581d402441c1409801c0d0080c01029401022207070304101c0c242461041a030f03401e2001c2c11711740510780080c7c07165400400c240c540183c068100b1030095100362000d00003030340c8842080301c400c1e4145c4a1207000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 16088450 1250 16087200 16087213
    0x609030807030e1c0302010b240f0304020105070b010305061005010503160f0e1804150b0109090504060204050d03020f061f030201030209030a0204060b0c100c05090103020a02010b031207060609050405 88
    0x640030f002c620000c510007800784c88043d035108205210801e8108410740150b5101d080f0300318903141203c14802900000116426000d03118207281410307000e040c0c1e284580040000218055a0040095400c0154402002d8a0b03641c2c40e494446d031030342400c2e2100115101c4d58100491558000c41c1903c0c480c0f2080e618107030103500384903001c0b11420551217900082c090b121136016000c1d11401441c00100410760b01c0d43c08103050a140402c401d0f4020008074240c81c1c0b0b03041140005a070700ca040c6c04200c9401403804100340c0c03110304044000780314552103c1c2d403102c54413042100b0180c012a040e46800d41110039564590b0307907101c5404601c00030039a50155140003820610040d0b0080d4040d103921003010b0201d45441c04940e0101d01101c1d0150013403221940081401c0c103c01a04100402948a484e04144501050013201a00300d01031450a141030640203d001d804840c0300358400f004100d001000c45006010340e4031945415401024183c4e03019003802408551851540125070003175910034000d209 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 16089700 1250 16088450 16088453
    0x2010c0503070f0c060507050a08010503030405090f0c040b0a110d0905150c03070b010618080705030607030f0920010f030e0703030c0c0e010801060e06030a0f112101020409060609030807 82
    0x83c0c0c240d5404040b41440b15003202c50020039201e110305446041c1c81c3c2c841e079544120440000d00070910513842140700380c0c01040188416101e201029030004150300c262181900d800040d800d15028a40200303004e40ca011905405642d030094100d0700c900980d1090b2040c3c03200c000400c850b180a03078000d0a40244403c021a402c49007440002c2510090304400d0b80e040039200d42e50003a040900307034005000902000381c5210400b410800c41401001c0b14402085130620306804281c9461008051009056403004038103240002600b00d02a8240d002150707009284119004130750710110039425034001000d8040781c5030a180640701e880301130501c14004226152855400b21440004100b0407500080304030400500840c1c001200390107000c2440000c212142040141500c42030000e019500c243c0c03051000c1c40100d0b0440d070300c4c0d48150390020707a01308200d04444041064824030400c95041e41142c0d8848c0b80d10814194040d0040c3c420036903050044a030b88007401c43d880342850101800b1400200031140 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 16090950 1250 16089700 16089707
    0x7050703021309020d1515030c0503061305070515040302030a061a0a050a09020f04170a03021204060c12090b0f041d0f16140307021006090204080307020603060d0b0415050702010c050307 82
    0x92186e403100442d600c60884490004e1501c02c1d0300413601458428820b10161034140000b507444116240350100c4400c00d6141d05540325000c0c401c090248030510205952080c0542c211000395401604840b4400c1561070703c18000e01c04000054801e0380e00d00c507035100034548103808030700b1180010520f40c0e500c0d0401c04c6040c02035020305500c0484100804c00041c0f45002100c40e0480d03c5600e00162408908904000c2d007000413048040c40392005c204014800e41c2d400c544c184030a03c0e0420440c0d00d1240c0d494801f5602d41100d508145044400070171030b50510030190004200390f0344009801c89070b40301059800c9003a958181c0b560241c260000000420b00c03a88980203482c5a40340d442c1060700c003102c0c0c1040c6400e90703106a0354a001a04100c80b410b5403a411801010010810711608503d810f00e08840c8644a008048000340304003000030100780c5540d83c6180342c80119402c198940d1190030305145c62001000840a43c0c0821401c00e400105442d0040c0308081c52412142c0350075155544856084 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 16092200 1250 16090950 16090973
    0x406080901050a0e0a240c1205250e010c060e0c0f060f0f070501020909070f0201050609060108060120070603020913110405060304030210090623130b06060f07050703021309020d 78
    0x91302c3c04142450703540c91082c05094201d101c42d4690010b100001d660724425920018a14ad0011401240740781c2c0765018130000d581d41c0122440c06181f61071a23100101d8502c1ea1200300980894201100841400008202c00000e40030845d008040480c60800340122401031304051502c121050100d035181081c400002c01540d4400c2c1c00043c64081b0030310024848100c156940000540c400e070020300241c5e02440b440303802403400c5a0b11240b0f0300c0c10310b000820030f801c010012410007880e03004031180c1070b03500503141c180c0385591415580069140c41c8010001c2d001507599920414504540080031400c0d4030846050404051400d03151905100c18030616510181048085210302d0000b260050128410f00400901ca10310114203007602740445544004102d02008298401c08248140040c4100d00c20483c0d40d4004c6000c40255142d83c000369041c00350240180d042c40000803540100000400e08106892088a541c1c09242054890f50102e4590000c025000000c2c1d2140d103001c2580c3d4501d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 16093450 1250 16092200 16092233
    0x170f060310090503090a0905090a080c070806040503070201080c0a022802040203040b060a150516060603020a03050706030513080702040e0304090e0304140108040201020303070c020102070b0406080901050a0e0a 92
    0x858400c180200320740d0040700d01441003550301da0000703d80c1d9001d074604100c15100814100c03800303008030700f003840e03486480304200f840090190400290745401003009204010042800009842403481d090808a49a80c8820812400181c0078400104180b5006003981e612a407568010446503050607031001c224029014160f501c02d03800360f503060069940d0f000031841180b10f41c0902d402410207d06003c0c00c051640c0241024130000b01311850b866601100b991440d80001543d0107015a690400e00700910060304042e4208000e05030100500c0030000e004030490303100c1d50341040395640c1c13120102e07440c2c45522030050000c1340c104038003005890190030812030701203600140e038642559012510220341c0300d88001401a00701050401410305841400f00b0040c2081c00c10b82920b14186e40002d480f40300042800342400725250300c000c00e691007041800054280c0c48981c1c3d5035162103601c080c001c0d080440384003090350b00b0040040c420b480180150800302d045100141031840042c1c0d00c2c00e8041145420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 16094700 1250 16093450 16093453
    0x8030402010201022b060b03060612130804030503030702070f0b0a050711130608010e0105040c0b071a0f06030d0c150b040f060b07020a06030902030304060c0201020f060421170f0603 80
    0x1e005aa541c41743c4001caa80901180740b849291008402c416600d859009801c80c01c0c00344100a0907031680e0044070400d8107903400064644e40c0b500c10160749000c0e608006045000c01040100811400000660140401d40c00300c41d01070382d0356804030303200c0c6406000c0e03510207400601071038025600400241c14020300c00c400c8030b0014010034000c140d88422009100389015124001040660800e2141e0003954888600038001c0d450b007501e500e50701e1001c0f8030800540c40030004403981840b681550201c07250081500760002c42c1401107a46003c41005d84400727100340924050940ca19001d82403d42409034440c0034a0300300c80c00d0708801d100170103c0400e255040703901d444901c444d0f0703540f501c0387c040a071407402c4120b0740310b001d180184840000380e034100c00c06151416900c600907980000940c1d040780e07002d18107601904d0040c40103e04000603c0b8441e961740c0b0402040c441000382c4c40002107a40341e00e101444a0885030401c0071201e6203400000e81c0c518440e004d0110b0301144100780026440f103409030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 16095950 1250 16094700 16094707
    0xf010b04090b0102011419110c03030112050708060f041205090904020f0d0b130309050102060c0409050402011709010504110411030109050705041a1206010338060a03050628030803040201020102 85
    0x14206c0c503800300e04440c07000040004680d50381258519209101d040390851700610b04000c0300b101c22a82c0ea10043c010550300c130324650f024008105080103100301414050050341c0301824080c104491081c4250b0342140c45002190020440c1445081910945900148102001c0c0c840307800b401201c10140e050380b9002030402c050074000c5010b028441d40218245007109040a1a43c05d0040c803460131608258115001981402407103006035069030152041403000240941782c0d480140c40342d0f0441c1301d1021110f840101003002240042d07009902c5540034415848514079803804000450348480071445c070245040c40107001481190340940d41c0160300381822880c0c02d032502e10781d4a040014104517000aa400a001700751091800d829030740003d400e00341800401103800400c841d511200f0040b1035403030b400720040d03100c0e5641140310003115030001d01b140780e035040d8504006020f084d08403107050050842e584151250000305541e0010300c480e500da030603002403c0d642e80140644c0b0143c400d038110764090 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 16097200 1250 16095950 16095971
    0x30d0914030a1214100e07030b04050c090a0b03060105070803040c0b07050d0306050109050a03080d0605060c0c0a0f0311060703051201060f02060a11191b050106030b0f010b04090b010201 82
    0x300001c00c070311100c0751514001001a03100f080181d940003026419803580b11003c0c06148482640528140c80c4008040c410070754032005d08400511000380c20319400b41c103100c01c4c80b14134075040005000c0c44406031000c000480d00c81c0c840d4660380c48199507032030000b802009003401041da05009540c00a1060a210a40680d01c100d01d48040c2c2002c0c605031460b03000041c100841680511880c00104020f00300078481619050010302e803a000c910002c0e0172440300182500000920341e00c8480907000041240c0e0f2104c045080c50382e079920425609038051014214040b801240041050045a0b0705c0740304c00f41003e680009010032074106501c1181800005d000460f0402c00155040c0d01070700e040d40d00d0264401a48200030700d45070002e0300400c02185002c0c800030044848804542590200900c0f0981c0000607801c00c83d0100301d50517408400151000003801007000642001c0e0440340100200d04194940502031070760b10800f03124620880504000411500380d140e0040411000c0500000400b9020ba = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 16098450 1250 16097200 16097203
    0x9020703050309060108070303120c020c030604060f200708090a1d0f01090c0e040506030f0601080309040b01180513090b04060b01020f0d080103080c07031203051501080603030d0914 80
    0x481084000c200c000c010011414804c0209900400f80d0760000d018080c0f45407000303020740e00c0300402a410140c4881c6000310762402040420205074025080706d405241a0034044010003564442e404444c0c100b070703e03140c1176400c00c4240b0900d900301122003524101c1650740303111095002100032604048290781c0080c08001d05408080c0c5160305162600503498104e03020311640b80305801080c901e524040e0282c0081d07a10002625100105840000340c1d0303205ca0000034900b102003524a0f01a1280c1d1002084040021001c1d040d0141d007540c0c2408401c21003001076482c05184050040003d8848004014a01e0540c84140c0411600703480040c1e8410300b51603104203e1380803581660b001362a808082000c2d6410051b030480b01210a000d0440600f2041005140840c10f2102801d600f00c0400c501d040d081c0140048402941d10010b2101e4645c81c80074040d0182404651014080000081c00c1c0c4140d402032180503c10a8024003442c80d140c514042c000040c5400403064481d41d15107000d030b2800300030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 16099700 1250 16098450 16098457
    0x6060705010b03030310061b0308060f0a05030f0f010e0303090d18030f03020a030807140403060905030c0102040f140405190513050708010605040608030a0801030f060b0306010e0f090d0504090b01090902 89
    0x88110000c6a1342c203007d0b0180442c0311038100300201105003642800402d5020b940c054100e5003c89421105803035210020b0072821054201c103506005600c0c80d0004814000780f0003c1c1c1c0500003000748228144e0380c0c8100e842c5d0004995080954114614007110396105030320b207401d2030a603e04249280c40c0c60b92030b514071341c000443c021001359028400d00e005041e0030600eaa076200c59030b0301c0d101d8240c001070140d07252580241e02c401005151510000c804010042c000e40e2196a0803074001c54803643d5400201c0b00e4440d0fa442001c0d140c25414140764100d0030180199131040307080741001c00d0302d502c4000b140707002440010035500d101310708404820000784042c80240020400c800c004104141880100021038010764000150395108112179101d103900940c0c500c0c1160f400c116512039800c0c140c141800606401103485515000b0301001050340c0740144801b9018802c0000d8000c070b65a0f40c0b054043c6e444000c0e400303103004280144420840444290802e450825062400955043c2d40d0078290701642c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 16100950 1250 16099700 16099711
    0x21f0203011d011404020708040518010f0e04050303131506060306080f0c0306060f010c080301080303070f020105040b041212021201030203010b030303010614031b0a0206040302010f09080306060705010b030303 92
    0x1900000100844003407022005940d1500311498007a95140444440c20101c4080c0044e01840d0089003840c2880b03940302c00c0d50018640030b8041c00060b1003501612600702e80074045d00c8030b00201c00304d000c540c00d40d501902600c00c5920400a52039502c1c0c08640d504412000700c011584a050ba10416203820120300030000204036546022407a1414042c0090401210b0441c8040c16800302c0d0f54402c0540c1c00041e00c540204095071800388202482004032180b2003c45405441c0c001c0c0040002008030300000254840d180d603035a58079071030070507141c12401e9402c146c9024124607010030214011860301c840b021a001001d0500300c07621580d440f0749905030f801282c221800c000c401e000401c25400d0038001d03841d0074201200503624542c10480d01409044a58501040703010000c00000d0581e440e00744e44c030460100f549981c0d1f44401c04000029601e0000700d4040340154249543c25030415414000e003a00d890340511000d066903545404d0140b1600070b08000d070381ca0340d21001c00c2445518240001c50150 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 16102200 1250 16100950 16101013
    0x9060501030b01050d02150d02040b07050c010801060908100c020313080604110d03080f0705090a0b0703030605100509060702030a17030115020607080a020c071802040306110703020307030f02 84
    0x190701d0750074541039010059002e103010b201c0800600c1c0059a900e0345110b0310904031240661101889a0394a0080c0115009010701410009940c03050020004081994090076a6412960f0b0788420044800020301d11982d9007681c0044940303140a000364005071401091441100d05100100c103608607845403d43c0060101c1e0007030005d0206104000b04203c1d40f406098070418004246da40c0c00070040c03031303004040c0c0d01c040b408000842c04881c0315030208c030402207004200e4400c56032a11003440c010b502c0403c0c1140860b240c18800285414100d4480d9218451a02c5003410000303041e080c40403130703032000c00c040340c1c54010582d14400141c90301107200400704203d00080d8903513041c8032203070044264003480031040d5030083c020441090f034030501080d88400980c0003d80c0320b05120f10040e18121090b00b082c1c01d4505501420309188200303902420449018000a10890480d044c02e003a203485148405001038004101e1203000c280903540100c5048400d104036268201c2c00b0204481c000851822203183e03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 16103450 1250 16102200 16102211
    0x90b150406050337020303071101081f180204091418010603020904020f010201092102070b0705101107051f0c03380603010f0503070e04110d0606090906 67
    0x2182418424000a00030550050041108151252405507140f6510f081403201c5610070028096901c0c1481c0d803680c1c1d0207400c40c0e88070081482c21000040021000900142c0c1a8000603582a0410700001c0304040580c0c0c885441c0d030400c020034940c402c10400c01c0d8160f42d020000020080c0052003414031101407120700c82c41c9418071404088030100c0f0101e51007080d03814180c3c140301581d03880154540007641103409580b0f42c01c203840182c0c05404030703403006080400c01011920b0008602040510070442c0c0394280d8a00030b484903145040d82c003501001500640c081004441424002c0d401030703002d013070601c0e0094204141903813080c0c6040b00a01c0003402040b070200840f88410810702680c801c42c0b420741410700681c0e200070081441c0090b0b800c480c0c4e042c1c0c000c1d90410b6580100c0c2d90f00720700349041c001e04400d03900e40c3c441c2c15982151420303100b07460292169600008005a00c01c0c8054080c6078405078009900c044242001618403902400391110b81c1d950400182170311051150350b070701034815000401c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 16104700 1250 16103450 16103491
    0x10504060b040305070902032805070f09061e02010908030103050a02040501050a14010f03020d06060e1002010507021b01020c18090606040204050102030906031503060702070807060203040f051201090b 88
    0x1a280240c1c098004540180418400200049881415111110780040c0c807a40c80e030028180e110541507698108c2030b108021001d030521150007040c851501620341030002031085504aa00604510a4800150300c8900c40320f8550810075041c2507000d518400420280003544400d512a8000c2c0d200322100c1e401400a0002c40c20580211801440d0480c1c5230383e0780c1484d2800080b007540c0260020750401200700600e42c00c4078007943c142d500790042c03640100b0200d80c071114050700044032411070034842c09102c800314000d0351050044d01d00c1003d445e4003603c0c151415a15200100c07004881660650141c515000c2e242d403a203a00780c1152050f0740c1c003041010f041585542e810720340080c0c09076003c2c0c2c0c01040140310310b0340c0020407102c030810305441c416031303954800c001d591404400343c0000d0b40c9030040380e043c020807030f50010380346065a00500989014642c0c0720000d990b81d1007a48501c03808158001c20804c00742c0384c440240d08101443c14004070b1114002e5495a400d00c0c400c07101e0540d616000a0f0020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 16105950 1250 16104700 16104709
    0x804080f0d030b0a09050601090b1b010e0102090a051002150a09021008060f01050d1107030309021e010c061a15040f060206040b0105040e150a05070305130c0612021b060105 76
    0x1940007070703a003802c001d01c890040c04513815034100d0140c1c030f007220349a03c0803410340c2c0d20909440004107a0307076850a8440c2c2c402d03888640e0760540c200c0d403800316600b0007540444050341031080700e0000c40001e10240015150109000e03041040b144a00b0035406204c43c000c100502c810a028840c42107800001b0b85000d0f41c1c070412600102245001e070401c81441c04110081d228070380c01908200d0242009a10340c000c203100d080142c01030084601309aa0f0200e01d101c20982c01d50401502d2030710866004440107268007081452511055104c2d001803001300040010500581c48540d040020345a0740300c8800c0742c200030071002a001c02c4a0500d51800003000c2103040346034000070002e003416201030704031800d068440405125040c0602c0b8071450351108400e01e103600801c119000f5901811400d4010326003544130a000703010844a40d4042410900050320701e04554550108039036015210344441030500800302c0b121001c150310742c8103a66082050211186122501c0038200031380e01c000b800e456040c0010720 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 16107200 1250 16105950 16105963
    0x3050a020c01110a0b1b2b021305060c0a0f0f0317041109060d021f090603020901121109100513090b03031204020a0b070605041a04050a03030b040b090109090201020c010e100e06070804080f 83
    0x1041420301c1449211440008000d22904642c0704545140d00c034cc5a18250b1402e004a10303e006108804442103038080141d44e03881915078500903140c000d9100c040240c01140110201c80040100b02200b102d0743c00c516212801c1c035008040034103606025103850303010410f003910418000707905051400700c121030b01d54419404009086103181c00d50034421074000181c20300d6049050011825220508080049240310550b14070140040c0300000002d5000e5002c0c01c244d00082031b0411541f03510101085454880c094010300e4131010303004515000c0c0c08540142049401b034400c036400281b401e00010990712100241515078050900052107040624107a130030902900d040204080000c802c00004c1480071a607102e002d50182004503074124201c0000b0001c00900e850298070000020012640c2080359001c11304441c803e0302224800055000103507101030311841580c0c6d1103121174a40f60001d5105210b0f00d00580030240c2680d06040c4150340b8040c40360810780000e242c56112a201011204041000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 16108450 1250 16107200 16107277
    0x203030906060a080a0821070504060306050d0308040b0a0e030a02010b0319030e1014040f0801200301090b0a08010903050c1207050303041211010903050a020c01110a0b1b 75
    0xc0f03690303150848003601c0d0306811034007501c40b40c4c01280b04040340b921000c1d030454441c0f00b041c026016280921028115800500030140000d2070520040340c141055070103542c0e900d4042c3ca078203203903560344e995610748402e0040c040361803992130701000001200204050060f983e140d030004212075a8100c28985000380000c40c1e40502030807030001401007600301c1c001c0c402e02682510954408030009005859082c110100003208041c006000901102c400c6041025540d9000003480300c0f00c8a240b41d051401344800301c611000c5000c00c0104015419680f06000348038015180d00c405a07500e11105084070034102c3c080e00403070300004144030a02000c5c8260014202c0c0c40361024100f0416484540d07484c04000d00082c00545c91040c85094140910310f003102e410013020090080e80c62514000f0601e421520b00741016210710a805d008031b600604c0f0710307980521580000d0400300b402e501c80b6810315a01815000001880c078007580c5603000274100619012000003241e861420600203850003e517498004d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 16109700 1250 16108450 16108459
    0xb01030f060f09050402011b1a010602010b0a091a0301060f03020306011a270904050f06010803090d0f0204090b040c210f030f090503070906050a050303040b0301060c03050d0c020303090606 83
    0x3014003901d2182c0d06100240c4415610020f80b0b640c0b20b100680d440c645051001c00d0b00400700d40203074100400c055440d4408628078000c0035050360f850805038243ca8203040141e510070640c207420321100b0380c1a80101c841d2011009036880f4a442c1402090868545822001c402201d0074800c6c000d43c101042180e0042810010414482001e10381d071000328002c3c03070900d082c0c200d41400c0d0351040d1040c001a005455a00070b05548043c1483d2602e16038410f45181c00304200d00450000141d25803010059429550000e0002210390140b903a85031460b50101c442268426038400340080490496109103124038412400007017079500b040b081254018105d11000e09070292803440034001082a0040e440c1c0507410309141c54905040c80c41a914014039821094043c42404800221040ba07504120101c503800d5404100003a101d03024140c42e84100d00030b0b490310180420042000c14812002c0c900703880c1c041e2900c58103255206403820f040e58120044040180c0c000b100344500034509111340b40c0c00c03501c01c46 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 16110950 1250 16109700 16109711
    0x1180b1b0f03090306010e06060913020315040b01090504020705030f0a0c05060a05041e0309080f010c03051006020303010303140903010606050327190303090506180708070b0301050f030c090a0b01030f 88
    0x1000a645e90340502901e800b194060002c1819515000706440f0b590500810510000d81c100e40d152009402c11a02d804020b0007503a00d2220600b01407195507a1b030386060792070b0602c01d81400c00740000b942c00000c0442da07902c000c0004800104498028210040312603603421941c981c142440344c90440c0107070601926620700014440043e800c079241040c1c03a059a1515407041c03843e42030544402810368401a598085c00d090307640070010640c00a5140701d15501d08010035103075060a0141e40115000c2c0d000035a1040005101080c00740680700703843e0346550001442d059081e408a800e46050b580f010000c14008400d0103075100a110032251944e98200c0c80c3c2c5506c0000f4800345c0da9171a4100d08185c100c246030810042858800d4000790700e000d4002c81252030500740a070021a1a084107504102c0d10300a00c83d000c10108004a04801100d0304000d83d03e00316401c2c0341c01c00040004840b82180d25114444009420385c48003441c1d24815002203000003250382107100090165901a00701b1403c0c01d2070b00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 16112200 1250 16110950 16110967
    0x90c02060105010e0f0406180f02030402060d02090307120507030b06100207090c090f030c0f05010c03050a08070504030b0702060610050f040306050402040b06030a23040209040201180b1b0f03 84
    0x44041c11641c091905401503034084022400c442000b40c21580c01900700301c00420a84500040381da41201006420407002d0142c40398a401c0340410381c1c000794880e80400010f5070309601d0350090514804000c040e02c0764941e440d04031000c540c4042c141141e041e0003070700040003800580b50f03010b64890019034150a203800c441c000291108640d000349490f090340d40d00c1340c050492162a40b28041c20605100301ea229460f4201001d501019108865481e00391070b8001c0b40c1e82d481035030003000c00c0e541901c9140c03c040900c8420350b0003e400500050401c141071000002240c80c0b40072080c065002c5130094240b5041040501011840c0c4c5410002406010412a841500f071035007214100c94000800185640b15031002070040d10a260f1925800302d0003106001c06083d0b81d03802000181054110341c0c001c500081010162080102c0d0065804502c050000380554001c000103c1050306850724000c0464941c4030205a94200101e440030b0803940700b03041103110408100c185c0018000400030342c00e01242 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 16113450 1250 16112200 16112203
    0x81e0105061209160305010207020906030106050105070f060207120e0405060910060809030f040f090c0305040c0e0a110301060908060c03010e070f030902030105011d0f0417090d020406060c020109090c02 89
    0x826040c1e5120103262000034001c84418840d035400c80b8911220601a2039170f030305129010f500905016442080c1c0c4001040d09890305118100881300d06841e51814403481d501c07040040c0c0305c6010140d81c19502048140c0015100d41000459a2504d807a03120b2a800b0f00c000f40002c554009061900071001c40b001e002c503450001d0006021102903241019580c0d41c0c0412950460045020a4030303882c10105003c2061886164003d050300d11085042001c1350344100704070162041910081c103e007003400c109004081341c88031b0a80d070241200401040401c0340c43c6200296a001340c0c01600020322165040c8201d00c010f0141031340041c2c2ca288030b542035505180e0300011030b0301b014080c2e0050008441d6100d001c80d02a8201442d10b41e0020001c10440d0303914100400f101000c00400444030300d503a800a1101e05229000324000e940281058140c0c00d90510031210540c41070107c1a800903447c010000103075200e010b0303007002e0440f41e40c03419120146440050f100d691150011440281040380301c130480d550 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 16114700 1250 16113450 16113457
    0xc020105070819090b0a091203060315020a1709010203060307120b011205070801090809040c1d060307050d0501090221010806070e15030f04050715020705090903040e0403081e010506 80
    0x2a9445030340300c04030080f0150b400620b16800010b041714001401c00640c1081035111741c42c1c0a0045011540c0131040540440031200300d400000d00c045a82c4d0f415003000d10141c6e000d02800a602d00b4040300e031590340f81c884020340e038080324002000da40000400480d410240301d00001031540f544211403515441e654514500414043d11550b100311200748814010304129120003805800000c010b03252071800d06202a80c010f0000300d0040d81010a0343c11210711502d40752440c00c0c0f44200003a601242c0c0c2041141541c0068602d030304100083c8400020b500071882014005d000a80d40107980752805003200d140801400400c00c10381c4010001001700e6100860b00d1540a00185011854002d50343c001071711a8100309019400c83c04003008000f11802c016071049d008501500c01c0b103120300e548141c441541140c0040c400700581042e1810013180c14a11245600407000790180c90038651203042081200c24100c805900082c0d1b0f02c0c0910120708800c5141810000105040c0c200340c4d81800c010030700511 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 16115950 1250 16114700 16114711
    0x90c0301060f1404050c0f0a0c0201080601050f0d05060102031b070801050601050304020d03051e07140c0a0602031206040603050d081005040b01050405060304020d140f1b030a0f05030405061209010c0201050708 92
    0xe8a5170001141140700e003007150582c6101300030841c3c840400403001019801c6005040303000c5414070700881c3d2a580224260384032440c01000c031602c2c2001c0c0d800118007504d009004541076100c10700050131070401180d8803242e401001d4005200c411301d0b0000803429101e02400c1c160500804200344400340c3c540c948201401c41e05820400c0d580c106c2e9802d80c1e403005000121201c450179001ca48003080150005038400b9024003502180e41d82d03900b074020010044400d100d9078016070300810000c0920701521940560117030000303100140081d600c5d122682016000351001c000200c070f400c100300c01d54805103200e2000e4034064030200085800711740040d0007840795016007031240a021000030119038400f2500c0660030791150300a071103d1941d01d81d10f80d0710001e080880340503000d48510614940350000850440304001402480d03004000d44443c25880302c1c4035001d4420b404100030100312521500d00410404400e00c9401d0003d180c00c401a508440e9424040400c59061106000356554800415078101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 16117200 1250 16115950 16115959
    0x8010c09090504330f090506090c0319021c080406140405010c03120b030a140f0c0306010b070c030803010e01090605100e1201062705070f080106080a0b0603090c0301060f14 76
    0x284c82c4001c2c030b84e24400c5030961620400c1c142810049240255000350b040d940c4100211041c60301e4142d507080d1586d00c041e00032034140e8000510048981450740c010301800340040d124180140310b40d805414040c01010b402d8510043c00902006403079070000303080c80300d1015a07007218109410035000030002222148041d0070041000e052803c10b58159010154001c0c000b003c4601218180c54440c4e0014606401d0410034002e00c80b10780342111001c10402030032400200a401c00d6800c00c1c07459a800d400010080c1c0340e82d4510305021000a081100940c0644413280350000a5894462114192a52604040d00500c915220241880d4010002c81c0c000e00c805c98110031004c5180e0800790041c4900e82c012100e8009101135a120250303500c00f000540b410710340e41801156140042a9107214001029200060030388004102d44c5110300300141d04001b0390030020600b4060303200091800d42082d035204055420131720000142d40780901c903140003485005902101c1901e02645032442c80e07525030005d80103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 16118450 1250 16117200 16117253
    0x10c0f030f090b0d060519030c121103060103050a02030606040c08060907030e03040303050d060b0c07090509160311010801080d211808030a0606050f0304060c09030203060108010c09090504 83
    0x10b40a03048031005001e00580c6684c841d984d03640c1c544003605580c80781c1400341031a06102103902d8820150704050303070342041414a0302442d1514041071055202ca0a0b40c480b0b0701c2d92450b2440e50340030700a00d40294094401010f04c030100b0300415041c0807003d1300d11031080385003186045050343c0200855030301090848480100f07588914044d0080c0a90f610b00d002c1e1404001070100405411a0290200104039001000402d480b5444541070b4425149044020390056008002c0ca034002d411040d80100100141c0d0003035081349161741c1c18804590012180031182259071001541c3c0000c500780140021801030004142e40280a00a11700c0b032411141b65800b80c022170f4404030b4030f40d0000d40a80066070301924200382c0d107080c6215190020746014841034240440094039600c2001600d8048160104440c95502c880d650701c001450690494018080d2060001001d030f902841414000c1c0381000000c2074041b02408018400406908400415031801d42400042046100c401c03400014039080c2017403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 16119700 1250 16118450 16118477
    0xf061003020f1201020a02070602010e030f030606070606180b010f020106140607020a0e0903040815010303050301060503040614070f030b0301090c03061d0a0c0608090a170a050405130e060105010c0f03 88
    0x3050503071103d40c103400d903000107010026190b0019086048841c1c0b0340c020004070200e50451900c03886120f0340640c20103001e00128000b0710f0840010200b19100c0c58001030041e80e50b000c1800751049100c004003c0325a0780d800385925507000040030710050b0683c4020821181021130240c113662004142a0050310003003070f04001c5441d440c981ca000b030320f0036500740401031811031a0196680d00500900c890f034021141500e040580e0a086281629030645031503007945e0801c03004540940000f0001c1d92619114034502c0c44030044005910700581c51a941c80150b2031032500090161181407000178042d0303160038070200c003003203003c540c079419a030748040b0110b1442d001e807840000742416021100614003070168034104100b02002850103c40203038607505541d984150080392100b01560703000d8400740101080ea03140c103e02c200100041c09140c01c0c818103054640740441c1c1c030b2110b0310045006540d03860648041035031042041d42e0041c40c00b4a4900c840c81100d030740d0140d2031601003400409100c143c058650 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 16120950 1250 16119700 16119709
    0x305061f020c0306090601031e030807081003120c0c0b04030f0f0501090b01060507030215070807030f060b07030c0506010803070512091c0305031f050a03020603090c040213080f061003020f 83
    0x1451042c00030121105424207100c1c031604c46d1400e10084814a1040e602c821b41c8560810f5419401d0380c154071190b040c1d9899280980783c09a00400301900c4a00003a000300003e01e0b45040800d860840350784e084001c10f1171381f0341146244202e400107070b2aa0003d0008200060441c1104801a82c0c04640c00d4502c524924103903015101042c0300910311110300380080b030090741c408090310120303000303130300300c684800c4510f01c0301a05c00015a0b0520016680070700143d0550f0007a00a101c82169101c40005c0007540c0300318070941d136000094100c0024403440c3c440707014044108150707400b41c41000055894001c465980695503001000e0b40070b10300d82c0c045080070700c565510141c8504900407800d154a400401d1400034203561046500e0303040e400d0300301081d087e80c8400500e22019602c0160803a881d0b9400d5800300441034000600390302070703481031090504094803039001900d00e040003818000d460604041402d400c1c03040741d422940950f0702c42003c2000300201100b00d0821a901560700c054071608010228 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 16122200 1250 16120950 16120963
    0x90809090c0309010b0103020313082119060b040b0405120109020a031103010507030c0504090213090c030209130203040201050409020a0c0b0f010f05060403020603070806121204050f010305061f02 86
    0x85501900903000c001034140e4070030045209a1091008100c1e0140a10054007240429140480b1440c41c6500840020f8115402896503440c901c00c095914202c1280c4030140940883d0703020b413903c41200c000701c80b6202c0b03401540007a1a444411b14105804c003401403450307003c1c5104803803280c05c82c0c10350b061000e075007940240b0301e060b00500480c42c503540342e06041141015501845019618010010b90000e100f84940319050b0440d541c0c123482c0030700d440c001402130341009070a0304401c03848903000543c5040d039104900741405152805601c40f00c140c41003042d6207255012079a1144e0041080000503a0310500710b034203840b8110b03001a01d50304030704401c4440c200c0c0d0000040c103003205a028483c02502d0002c556041784c0412000036a040c1e00c41c420b01410740194400250002d40134004540b0060054500c01d030300c00d601400b500e404420f1440641d152451003802c900c008140000e060140d42400c40001f03c45103030030701381403045040000c0030502e01004010b908040c0514561010401d5100740000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 16123450 1250 16122200 16122217
    0xc040b06040b0d090215030f0406020a02010f0e06011a0f090114160f11040603110f010e030a030906030c111b0a0506040902090901150801031202030706050c090a0503011b030908 78
    0x40e0388070b40c0703d042108020f01d20700105038421084580c0c4403080040343d408407880b54200003c1c9904c90f0b2aa65221000394020409040640d503c03010801c2103602e0324410880224140320082c505545041c4000440c40b806203403031a0b01030020005410310410f401e00f21440124203107010140b0700400140e01000b4007880c0500c40ca56040b0320185014400c2c140c96240c0658000c0780001100310802c5c0403c400c0700d42c41e20008005420b01b0f019294186000280380042c94018100b1405201c44200003d092212039201140440c829902c24000aa071503c83c58101862034201119404c5d038041c2d41681d580002d80e001812036004940b41c1442c1d0319402882002010060000c1d5211502e510f0140040e410140c2d9441c0141c0300f01000140b495920180e60b921903400d6102c20344542d09580700d180326101660b070b9882c15407000704848800a8001c1c0b059521840b403081c012903c03200080200800507a203035210038402d038101900e007180000e1320700803030104101e00c1c1000a4205403901c2c03c00b0103801401c0c0f5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 16124700 1250 16123450 16123469
    0xb07180b0313060b010302090d030c02030106030204020a02031803060103030c141005100504050a02130e0702070302090421020c0102030f09010201090f060516030203040f060509011401031b08060103050c040b0604 93
    0xe0000c0c9100c0c40580e58145482050300740f0a0b001001300460803401400d506c143e001203141c0c240d401080c042d891452050340090000304e10a038891300410181d87c0002038550050344001030000403140d9802102c1000b68044025000e9940346460050100b40e0100c1d02400d4090301400030040950200311494030100000014481447c088480f12179025540c405c03180110f0074800040c2c8200400c0c801c884a40d5800c0c4007a001c0c617424401c488010070401440c0d003080d840342c0c20021015175034100c81c091003540300c1c215251910300d852101c034070000303e218030301000c0d54020015108075030f07004020340369803564003200345844000c000c0041380507100c1100d0140038180303001c1c40d0b00300348003e64024910688013190924102c0c007101e10104c01300e1104860141101072151401d1001520a400290708032400c1c0001060b8810070b020f1241d070301c12013a0710444484100000940504074244107880040c54080d01900c03641d03146d0703100d01c1c1c1c0701d2103a0002e89101e1355565114520a40d5060140d0b030181c582000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 16125950 1250 16124700 16124707
    0x1020601062105042102072105070803040e1009020a080606090301140108010203070311071a0402151605071205060604090c03080406050901090522051b070503070605130b07180b 78
    0x1404611710301c40c801d07425074111a80c0700380345101d400060301004551804210350b890100518044a58014561044409008940340051204002c101820141049440023011418102d25441407010030358030120700e490040c0001d000307050300320f9001a030201043d0b44460307443ca01c03100040e004201c2480c0800000711000e00100305502d05501841c41074965032020400e0a0a5203200c80d0113008290008210300200001800b89030201124250001c0c07024080202d80b100c00c411049442d0002480c2c42d075640c07040c420480c107001c0c0130404c0700000d0100504003110902c158540359142c5400a0015000703030b4640450708100030a12001b08011034114a845844540b5048001c2565001c3c1130030500041d940300012442c0c0c40d1401603078208405010007074800d0030241c106200901001421020b50150203403004c00482180d40051045501c6040503503a140d0840c68134504a52002d455800c0c0003080001400c00550110705080e04082c050900c0c3c1366150085c00c5014116019410010240d0f1012 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 16127200 1250 16125950 16125953
    0x3010b0d030c061401080a080c01060f08100606050306010e0904051009080a03060819030f090306020406050723030a0518040603060c11120301170709050c030711010b0102060106210504 81
    0x10010b8054070f48915403d012019101401400c0c4410a01400f103268010024500000307442e40001c0c240380c424100003042e100e075150700c2c960300000103a10048054107d180306442e0328290b4400c4102910f0716041150860811600003001042d642c143c5a00480c00103020a0600c0b034201300740700300081c00007401c4c08039075613a2500050a401000856011a04003900811807880100324030b944c065070b05004d01400076242d102144c1c01c0070078140b12000c1c08020000400420794034002400500480d440f00e6640c1c0c0717500d20781040c1c826011403c00201c80019104000082804030444014003c10300d016600c0340e91521010f6420320072040402d520600e070003400401c210b195000040d00d10103075201ca00b201c8502c0d910f0304c0d886441c0329100310b070241010401032004d240d07110741c041140c070051800c0f11110340c7c0f501184000c8072000d0b40c0f04050044080704010310140c1c000560100055083c001344007a00f00070700042d607030300ea045c0035290500140b20301c04907010340100d840180c00c40c0d1025040c840da0420307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 16128450 1250 16127200 16127207
    0x50613050a060801080d030902012d0f140f071502030910050105040203160305070905040f140903040803030403030906020705010504060e0c03070515070309080709060501120509060402040b03010b0d03 88
    0x100e12625000d56108240050518050710009040350140c101402c0811003108044000744000c2e0022818007003e41e0003520344541e8030801000b03012500500ba10010642180507000d1807031520503204100403c2c2c0c0ca140c90903901030030f503130f01d1040303002440340c449000e0301c1c10520300c0e102044150758242c40801008940000018240060714520404028590702d41c2d0922090340700c11920a483c02c0b8902c88584d030207901c2984499442003251418200c0251a80001802d03100a2982d54914a8580c6013903103403000d0b081d6419420030200b0005618045c0780c2011582c0341d000081000d0181640c4409000a101203a0100c58540c0e038054020049450103291000041c0380c40c0c18611038502c50001440c00034100003c6803800da80005003c040030340704401c1d0000141d0301c0010201c081089205000441d40c00c204681d03030252601d01008210603003400001446210807142800c581810032045c002c0480c00411142d030802e8040c1e0f0003050075521540800d001d42010820550400402003a04c000e2551 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 16129700 1250 16128450 16128487
    0x30901020d0609020f0306090910231e0103060e2103100603050105030712020f04020406020d270e07031b020a0b0a0b0f060706090b010609061719090305040506 70
    0x8601400c024003600c1d0702c540c0d02280a28580c03400e1900c41003003ca00706180002809074403d0034501140e2002b40342229150640c0c90010f200340c01402c3d5501d40c001d080f03140740c1c400c65001054802c401d4440ea050003011001c00c4040c400501202e54a840001c22058181b016a00d424000d109122160f01c4090212400b94400c60308981c00100e28400800d01c10320a0240504881000340109030007800d0003003032143c50505600c105c1e0b10469841000f141d9840d50b0001e0310060246402901025400d844041c1003d4a44500e040c0d580c0b40400005c103108400c0c84003a0245c85203407600c8001c0b03946204051f4000e00710400b440703039403102c0844039038a5164002000014917104900c03501c0715403203c03031100c41900d03406891207034040f008004007080360401c000074044060240c50003280302c003125111000500420b82009001a001e00c3c000d12041c0c1d04191061180c040c10043c0c1b0300340345014071400900d656661001c54904c0d448008510a2501c01d1055602914000308641d42d280c40f2900003444100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 16130950 1250 16129700 16129717
    0xf09190b07020f060402010203090402090102011806050105030f0c010207140609030a12090f050d080a1202040e010501080c0306100e0402040b12010306060503030a0807031d0d080601030e0c010c02060c030f03090102 94
    0x216104030f5802458003c200c4501544c0d040e0011801c0c045150100700103904900240d504540d0307035140581700700c401e0b078241404181c09040c00040340e50600080c103040c00c02c80c0328010b0081d4441c0070180f504c2d0342e001a1410444200345402500d880da10000501c05218a0000e594580b05000f060024401c084080340d00c00001a100c1081c2d031961480b17000c0d05a25a032203140d6028442200081c003103020f2800404201c282850301407802c0300070400440c2241c0140c0c200c2145203a140c4018001560841260342e003200d805104107055280000c00249034030040b4a48000300890410051070036140c40e01510302410707031071001300c4c1c640402c5441646000024031064038664202640088c503410044200c43c906019035a400c00f0554400c4000c2d0b0180942c0624140030100b40b000c000700600742401160a188141c0d92006e00e2800c142000509840070b100307030815590040e070050302d016038100029415556066682c15140c0007940003290031401240440082604000300300001c1d818194001c15100c0d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 16132200 1250 16130950 16130953
    0x9030f030b180c0a020a05070f0f05010801030203031b100207050a0b0a29010c080a030212090304050a0302010c020307030b0c0c07080105010506250206181509010203030f09190b0702 80
    0x101c0c1100d003005003a42480d4481031900c61501d0106180200720401000001c0d094011180e00c25a03581c0d90501d08074140d4401ca1001070b0316201400245c0d099401d110042000b403902c21610b50541e0000303a00c07442070903852007221480c01d80704109168280031009088020400854503050039080c159155050100100c861403031040004020035242d03c5204404c0200e2190b0380441d503c404404074080000c41201e50500c20006201d41c0001c803131800a04941405590160301c481403180000c00c203c0010b003040d180c0ea08203100c2449075890b08440c02d0102d1782c09180040d05c81e01180003007820906240c0002c1d19031452441005031184103000140010910f007003c603501103554030103843c2260020300802d94042c0c01009214940300d01014120480621420200e070038161a0380061004d0f8055a89104541e0000c803074551380d0302d003032001582040355403407506107800b03080340c0000d441e840020826025440c03040007180502c60100442d0b000d145158906c5026110300d401c0c406075a550444415005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 16133450 1250 16132200 16132211
    0x10e10050c090108041509081803010c020d03020913020403030906110105040f020909011b03050a0c0503010e0a110c0607050310060c0506010b0c12030109140105010c08030a09080d09030f03 83
    0x50109a00c2910300c940e003080c6016040006a200454110002900c00d6401c3c884810920078500c100c1c0c42407901c46d500c100d074295030312412031203c0d200c44100c03001c8031031080e45050000c1c10003603000702d400034100c00d10b8640140e076030015800258100781c1c0b80d901420703914408039000c02007603000ba40140903502641c8608840c40c21841c20303d0309840040394000e104540034607813880181000702c20b098020403410008203061143c5125034a5801071040600000313030b00c400500102c003000703104140001d965440d010b45558102007010034401c0c00540f0b03124495a440c84080030b4200482c007074642d100300c04000d03151142001c000003480c0340c0040c0c5099079800e000b10380005038180244030000d10f240e4080c01800c00c5a1038202c00480c0d64012401c2e200041c0200c0c0042c0c1807010a6000460203040000d40008246029080c4503541c014140c00c013505200200406c50007145290b82643da00800400e00030030304034918640b02c406806408450307083c00d401d03c0c608504058024001d15005071055808021 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 16134700 1250 16133450 16133473
    0x91d27070f1a030907150c0807030806090903070305041703090a06091802030103020d140f07030302031306050901080a020f090a0e090f01050105011d0a05030a051011190c02030c090108010e 83
    0x2c81d100c1600c1e4154641d10502c020440c2e00e045a0401e01c144115041031000341d070300f03603d0380a04e1341e002210441c00a1000c20030131403289414501d094000070400001d508120403960007521500c42e600496070f011248607143c4039440c01c200102c410604016060380880d6981d0200500383d42c08500400d01c050040c2c0c0384140c2d80900301e20a0740e040b26001080200740300302e00d0700c40706448004074011180b9030159440d50103d200c4200700c070303100451080d0300035543d032110b40d070042920004a07089201003200402a40300e180c0c0c2d00c0403030f01d078012030201e000503540d205084e0904064400c3c100460f41054004100051a4142d810900c0c8107518807019150307546580c0c10454201c070000d014440c003051041401e180700c4030f00070340c20680e00d05003d03100c50316154031200041d00e00401c106044031550f01018940550244a0143c103400715100307945a400d00d00c80c0350385559400f18a002e214100015a081c010079560100000d0134008400340940c0c00d156145d0101d01d000c2c2084000101c07052240f0351aa42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 16135950 1250 16134700 16134749
    0x8030d05011202010c061a100207080c03030405010e01080a06030501061203020c012f01020408010509010b0a0608010b0301121a070203041e031a04080c0111030403091d27070f 77
    0x40b4030030350580d510440f25a05541c0e40005010740ba00003d0200c0c40c42d80fa041c5a138441c1c6000d18801212600100403491400c1c90b00c606d0020794203074260103074100f03220800c107d981210b0303441d01482c001d0070170200d540e0f10300e4581c0c0c0007001c403680041c02641c00c2c144002100c0383c2e00d010003601240030f0f0b0b00b9640c0a00c4021b005580449440150001c1800c58000841d03a00c0000e158071070055403030740c0015203090b40e140e80c854251503081d10007000710396451125202034540a503881d0011b00c85405d06881c9503241540c2007059000c14855218a00b607a0b40d01e00b400c000c108402000c9002c1e07009244151410705100003941c0e0f030041c0c0a4081090405080202c1060851800700c01311395201000c080420562003007101d001c40094400c031141d640500200065141c28000c005076003d00400460312490176041c01494070190f0b0b4080742c640c0c00e0b1606645e0000702103846c180d0344800c00c0052540e00c2c42040f2901c28003180d400307034100700c0c0c0c0c01401808074401380c1d03c040840840c0c1c030000550b01e81c031a503560442c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 16137200 1250 16135950 16135979
    0x2010e040c02060c09030f0105012d08060f060f0d03020604060c030b0a0317160f0c05010306180c090f0602070305100b010c0605060112020705010c0807030219081005030708030d0501 80
    0x11002d80c1c05500084c083c041010003c21030745102806955030003540426850a441c420703004081e1802c0c074048012040440300003100161010b00089582840c07400080d6034441c0e03006041d5088242184000030a96203402000c4610000040c040c4404414181402900c50005032001c5880500303000001d07640c030388a4002d0721800617006214000c01d038a1036413a0040212401c0c1129900902400380c0c12030702d0700900e10002030500441030102840303043c0c501070202a91980005040c18074108040c01214445000d4400e501034117000001c203403601d1042034036800342c20750082007039400d1220b022034490b0340415450126885441180c0b4080d840b0701c420015908a4400f05001a0590040102042036a0002030308100f040c1000c41c055181d080d20b24060b680b00b4071054603103a446401c000c00036071740504100e521906030b180071401c000c03919012988448820b44540b08114501000c28040c84608003041d000b00300c02021175107002d5481319829242e4200c135000760111440e050000864010100c01c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 16138450 1250 16137200 16137221
    0x70201030f022502030f010507020703030306080303070807180f152307020904060f05040c0302120106050f04020a2006010305120406120507050717030603010f09080403020d0503070f0b0402010e04 86
    0xd0f921070380741e265400c001011240c01c240c0e41485407521102a41741d082c442c5230b02807003540e805002e4080c1141800f4040d221541d11a40e8517900c00c10800010a40c04094590855100e1030318840109040465450b046070390741003058045001e45c2c00103034103240381c2c0c7c1a08064480b0f40381c1503010311400e10b642144005500140d05250b0f001c10445c401480d080c082c1690043c071490340020650481c1343c00c0000c03100c04071784c21224040c50710b106205600d0710400c84042c444290b4003d121150508010940c0c24040e44091400783da0041031300f4400724041d892a07204000c42120208c0e040e481402c007a0b5031400c082c40b0a075214000c108880200c0074420044400b624400e03207840072552100b0345d40f0300003000c0061402040080030301c1118005400c071540e0f2002020380090302922814220101421542c240a0094a141c80c10240100045540c415a001c8a404941c10801e503803084c1092415889482002030802000c1b034060802c00c050880028000c500070b03a240406000c14400740000c072981100c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 16139700 1250 16138450 16138477
    0x90d1103040305151e070503270a020f010c020301021215010206090c0d1406100305100209180603120301030c030303050606120a090c0801020c01020409050c09011b02040209090c070201030f02 84
    0xc510380b4a00d004581c0c100a82810341c61501e17141089101041c5015522040043c1e400000d01080103413005001c680c408984c41221a00102440c0040da11b03404824028007030b1450385490442c030382c081c400c07409a854010f002556901185e21869820f000e007101c40f8010b140d5510303d80d800741d510009a81d4030441c0000010300c0082100010081c03140d845081c00c40343c1129900c45040b5000c1c0600c0000c1c004c044020800d0440e6065252141c100031003007819002503441840b010031030b5a5203100d9403412404100c81030403a46c5505001c2403c00b0002c0c07884202d03504000000001301700d010130300322007120700941e0200020f44440040207000c0c032030740c900b0208031801c0001141180f810340d882980010322801018034000d584581d09401da80000352400b400342d6000c103040001c020079008090703000303d1303016541d4a41948040040c05688040044100c1445140c009404640300c5504031941d90000170200521840c00420f800e00f16849024201d0009050074101e50400c01d003402900e82c541503146 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 16140950 1250 16139700 16139713
    0xc01200702010f080402030a02060406030504141f05150a0b0c060705071104150509100305060117030f0a02030f0d060815091b1305070804020306010f080c01050a030b09090d1103040305 81
    0x20b004a1340b040000c1c0040c2d03454040c0d4010f140059540780d0051000b0100341d10041207516040c100006c00c25034941b2115030b0368000c0c00c864070114100e54030090201061420014403038a41408545141c22240815a00001001c10104001004601411038013602e50100c0b50999034000088401c0d00501c00001c1c0300d001d4601ca0074199181540100186014040766030300841c0da1030000401d0b5901c2501c2c9003002101000f4140706101060081501600c070340302501c460210312803407503030746ca104401c5020054040072800d20f038581e100740116600400c10340610b5451b03555450341c5100420243c41024070340d1040e606010310300020594a10b204100341c4028115002080301000e20b880c802e5104258008021440501e00000a01c580d9004c0c00e042c0c1c1e110112442c06206140c603000040e00b06504481041030200605c820004440b448000c080c6000c80d01c80c1e5080f03c082e000b5090949001c0e521445004c00c01c840e001000640d1001c604030b554403100d11803444a580341d103a12450101420781e0f0000e8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 16142200 1250 16140950 16140977
    0x1080a0b0301020d1104080c060702030303070c02010903050d020102040905010e060a06031104050a0801060e011a090d0201050405030604060f050c0711062a030307180501020c0108040501110c0120070201 89
    0x26448842a5035000d800903150403070700c99080d03007200e800d003101c200c040e68041002d0010b1070040016403541101030740e8407450805a40c0000380c0c1d078003000300f4080c100181c01c0f4001046910408003000110350003070440d00304000d2101c1c007074041e412602480c0c490910700b4000081e0003a4841d5114002c0001510820285080000c02c4028061541103d5084032080000048035121501c40342d00414400d4000030740a81414a606010704c2d040c0c2c069904a44032a441d100100e80c040110740f80300104445078155001ea610050710240500c0d40125898003601c0100030a00215421070f0050b001c20b02410041a5a0388100c01c0160060080242001c00c061020480380c2c00c00302d008040c480403030b100320300c840c0b034011115880c1680c0c411044e51168102000340105907820440701c201c44880036240806107814540006d5445107503807030307050400180300c3c0403605000d13080d444482c041c203009240315903484080b030009001c1c111440f000900ca034082064500508c0b4202c0c103883c6413990595400700c000d08903 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 16143450 1250 16142200 16142221
    0x3050c0105130809090703020f07050102190206060105030c1c09050606040605090907090b0402070f05030703030f0209090604020d09140d0905030703050c060a09050901030b0106170702030301090207050c0a0e09070902090108 98
    0x42c5040241f55003001490404074000e80030740301d0741e8414800923a907a0300042e000041c41040048640c2594000d509004013aa00242a00c0d408040d07ca03103540c580c810002c030001003950041f00c1c0e04440e8a049124024048085041442400c041e02d05100b0381da59103080c0700c1401c100701c4100105811100f01840048429005890290401000582010510744500c991650010011140c030761001034034408040d0180503003003112080030011400c5c44000c00101c0c110329001480381b44a66800540c440809540750b001d40a241d4120f1004c2c210140103664403503841100500c00320100b0301800d00080d1900d400104a81039131390241c060440f003500c100c2440010740003100f481080c841c0108001c1041e8684406040c0258007680702c2c00711652424401810718000100b41d0150349101000308020039070000300700c070f0442c0c803c00300c011b98407500ca04046042551001000ea80011944070008440c00c10080c4140210b029900ba1064941d841c03055004911038506054089842c0e4000110160300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 16144700 1250 16143450 16143469
    0x402100516120201090512070f0803130611090f03060408070b060a090504200d03020a150906050108030306030607050406020715050c060702070305210405040203090304030f03050c0105130809 84
    0x103241d8032041ca000400e95030000d03540540862600140c0d9a4501c0d101806400c203d2100c15070080c1080624105142d16030f00403018144901800030200080032850460702c130300b455884150030030030801446401e400303c2d00d802d91048807100d01c98805184960280c0c079010030024040c1d82d0041c85c1c0b501c1d01c03e440d9944100c2d56802800700c0d0b444a00d0307150003e1420600c9c01400c0c40359205040f80381550740305041d02d01403070148001c006e004249040480001940000e0701c07200c0260041c0ca40001d03016407440b00005803032a01c1d4000d081e682003078000110010b001000d14051001141a540d0301e50f00c0c12411a8140a24880c3c06c00590208c6020086186003421009081d486403030018035003050500c03002e107030a0080e01c400c1c0050381701c1401002888400e00c480d03015901d80000c6201e10340d0400400015a0140d802007074440e950000116200510030000c40d0011a8010f020f04032030341e101d040280442c1c2100074050483d5003480c000412007841c000802244a07484000035080c81c0031401072100d0100c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 16145950 1250 16144700 16144717
    0x40f0204091403070b0c03040210140903010906060509070509100e01031b0c0212011509050a02071a0f0109020703140309070317070312060503031c020d050c0d0c020604021005 77
    0x30364400112000c6007440307a0640b0b03080201e0000715a100414070b004110030400502c00311000c1d8040c01848016650341d02d80c0482100345161451440740003090140c002c1c414030f03e41980c950702c0c10100208000b5660001c10417141c0c1101d5000070303030340c2e00c0f48107603018402d0a00701d9501178052240c9052483c0a81d56540d500d01d0180340000d201d49400014103a0031038800252070209a14000d40341c1107107002c0c101d0a040360100c0b8000c0c803901e01c0720b681c0c40c019041036002d1f88001d180c07140c001800500b801d5040e680c2c01c5070045407044410380d01e6000401c0601c401e07030300c01e5031000150307001049112250084581c05581581c072504032003141554014150406072003140c00303000d040c3c800000b2505c0560401d401b440c2e0b00c0d0246544400a29024000c45104213181c415a410283e04205a55010050300e140c4c030904811405c5c200716030346501e0700900c900c101c85403031b0515010078450302c0310900b00034290503e0800001c110803d25102c0581e5280022980254022002c00c007140e8a184103501034002503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 16147200 1250 16145950 16145959
    0x709030305070303090f0809030105070314070309020d080703080702061003030504030b0a0914030309010c02010e06130819090512010b090109110c010509030702040605090708070c081210030c050102010b0108040f02 94
    0x1405c1d80d4807100c003103818400176540717082c010071141c1e070a1a0038818240c1000b40342c10104113000c008206600c0e89a8000c01c04030905079118001d000f5034403650600c0b6031442c3e10a2209030380e44114078000e03000321002d0312504014840c0701e00040841c18625848015203415481300741c10289150384940340140c000340501250398866030070000241019070082d940107608005140c50b4074007150b400c1d00316a104a10341d821a81440c1c2000d500d118085a10313a0081102100c2051102030fa00f0482030911070701c240e000002001a50f50000c1c40d0f8042881c00c141c850461b40740c520026104042c070300343c8248448540d072080c02d42c80100411856a0300031500f41d02e190300300034100b10007004414211101103401d20359581002500c0300440c601071082a015001c1142c83c040300781450100144207090051078042400003001e1400d0a00061354142c034083c0d40c0000714400185031030303000780002440c284401c1b10020681c80001c15158018041c500d41c00c0710603580c1d00e00c1e56542d41c59562401d107041b030050340c11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 16148450 1250 16147200 16147211
    0xc20060f0a021c0e0f040507170702060f010e010e060d02190303030f050105060703020a030807020703060c0c020112060515070206070206030f0f0108150a05070207081606090e0709030305070303 85
    0x940408101801420000360003815820740034443c1c4510030943d803810501008100b2514041541d00c1030141e220002081c1e43c0010241d545510a407402840d03070320034906031030170b0000b04003205a001426034417468494051000c01c0e6030360740b410b86400c8001e002d852110040c40c4000382e83c1d804c044944000039400103046035034080c400300c040102d0300344c107030025000a0b86420240c4903a00329401a107004140c1500c82c02c1c50325626840c02134803208114802401c02c952f071030204a2562081101c80061600700070108480184d2000142800c051010704030701050004035030120401541c410743c0222a005081150051201903482012754403188089038405410301c00200545c44441c0518420340e515601c4071010b090801e0702045c0c0c464141e101c2d24881d8005090203080601d5440310700e4000141103408141d54850b83d105030309100450700710b01500c2c03040302c031130701c509d5aa048a41c0044442540b10040115143c4241c0e90040d001100c1c0440482d007043c4013000081c1c071620050503003601030301e0000342 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 16149700 1250 16148450 16148467
    0x50403090302091e0105120d050d060317030a0b1e130905060702010b031603170c0307050109060c03060905060d170f04060903060509010209010806061602030307080307020d0c2006 79
    0x480f004240c68550b9a00b007114100100c0182062105000d000c1c200c50b21070850190b030400c1640e0f180343c84445020090042070101d0347c1907040d04040055540003085002e40c012002210a507904100d550341c1c81c55003400d001404c43d00301240922a0040350841d100c601105000078030405000c2c400c1e80aa000b40d03541c2c41c000100c0c500303121083c01414181e0001c62040f4884e030401d4908584200170a00c280340d500e401b0800141c810580d914510540b681d6281c456101d20399050a5005d14140980a5400c0050090801c07203d540101c1d800701c101d44003040416120502c0e001254400c80d4001d8104030b085107840c0124006a80484c01710880480103490b004820300b2001182c3c006501440115007060800c3c410407046018140e4840c00c500000c5080c4003103580020f000041c050300782c0c6e01a81d0000f501210032003801403c1840e0741d0b0003504a0b6078030811464814117031303030003129600014042c0c18a0001090f110f142043c104582020140700048100c3c038280c070311000510207603030f8415401c000320351 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 16150950 1250 16149700 16149709
    0x1d10030e0a0602070b1006020d080f06060c0a050c040f1802131b1205070e01020d0c0510090b06030c060406081f0e07110d0305070203042c010f06110307080706050403090302 76
    0x2c1843d1003902074503054182110700c002d07001040d030054025904400c003a409d2207503015401c90b900900901d182c2066444000c00705156114400101d0450301408070341c4400d00000084a001403c0103440810041c080e080a05003214110a04880012381d054902c9025207050007075403211002d412000910405001c06140d41c031100c0307580a001045010246445440c030030310a00e41d0241140c10002200000000001c1d03d58039030a15850a2100e45040307242808802c1180c40c180810300318003040340050b41d0400426801d41124400e04c40e02c607440307030700406003040c5003a2811202d16444090686d1208605003841c9810035409410510620500141c81c942400c0e07101d00800301074075a105040100b520b002c2c21b1078402c1e01d05005041c01d01d014490890b81c00000c68007103c1e010744020741d04d1070080c02c3c1501002e0081201d080816041c6001181120b40d904802e0300300c5142d40c40e001e0904000c07929141d02e9000e40c6401411444040c007505c0c000c0b40d4135412080d40302d0303c28642404403d4890b030026 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 16152200 1250 16150950 16150957
    0x904090809180103030e190302130e01050109060302030c030f0a080d090f060c0216030803070f03060b0d061d0403120b0d021009090b010503090a032d020307031d10030e0a0602 77
    0xb084250011001007040c13580256201d564a81c065854018151745c40c00000402545071100902032041d18071603048244840d8058020841407a000344440d59644407032001401c42400164824080c3d080c0c03620091400042c1c00c55000c2449024001454040c0c4841c0032075000094510001610ba051140010b0040301100c90014481d0340d00007a81c61450100902e022104128021303412520340050011030742c04010303280c1c401c805184c6403003002640781d8100c01a014541c00004c6043c0c2c04100e0380c1010710300e0381200c0181c0d40082d21101d1421620316401c1e60005040d074010380400c542c0002464094010b03000b052401c0d00140038501051700740c3d4081040107102c16905800036007403081c148001c9105008800c208002485c0090035030038220103050702c1d186101001000d00c0300501c2c1000000c150302043c20001000d101040e4150310b50028081e44950044038107c1c0042c0c840020005035454500c0ba24050103005003181c900804c1d101c506a005164800c0c003854280708043c02c0000150b081c4c0000c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 16153450 1250 16152200 16152229
    0x2120109050403120e1b04090b0402040506010c02030109050705100512040809040902280605040501080604050601020c0303030408040f0909050c15040f090603050f0105060907081e090c1003110904090809 89
    0x2410001c441841b82d05482e10403e0b0294490b509000c1c001b8045182080180d401c243c040b0380004094844d0801603a4036222003600940650800b42200c00740310011503ea000c50304256144012031600c2d100032259840754100c824529107209003c5004540000c0c00342944e4800500300003541d10b46074002801c90717104102c00e0050a26500070300504000c0880e00c5000415090401500301420000041c101c0d000081215000c0d079614000a405680708120442c884240035080c0c036613a0038181013601c05a8018000c0f440b0001080c04001a9158640705824040ea0048080d20003840e20004200010f81c1c00c840380d81c8081c05c00d00c0081428143c0c0911803001f400e21107000a043c92a51900c5800e001e0001c00309407103649080e08101454450300c201d581d21882518040d000c0d551110202e012034840315210348280310801d410010381100006a600405008540303105007016562800c0f410394600040d00c80e142901400007036000c7c14070707401a0300014402d021a900741030b88280464020b200d503154 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 16154700 1250 16153450 16153453
    0x60f0405070b270a0f0303180306060303081503070302060417100c11011116080c03040b0a080601020114090304060f110f01050f0a11041505070203070801150902120109050403120e 79
    0x12a483c00d14560300d4441e02c90105441a8800500e040340340e11401d9010303c13000d802d0043c0220300707000004035200890007869008508024068484c2001403010404036901c1107242c040715405001443e000500d03c040300d078000c1085281c98280582c0f9426000c803450f81d2107092044000300f1b083c0c050280a901c0441080da541e02540321080d601d03c40c20351f046c0300242d4000300d6082010824000081c0d851050050b00808829911118039044600d9441980c0c000a8154400301d25444c842c1e40c01001c81c2e0003401309a009210008810030039006007002580c03101c0280d80700b044100125401121000108079090501c1c038001400f544860342404500510024540d54580030003810a03802c1c4000350300100035440400c0040c01082050495208a0040303054110910200c150050b224800700e9000a501a003560b03561903442e01d841d07003e0000d800d41d48414441545010801d181103200f52501000401041d03111030b480c0c407444e5002094007600c04e4003007207458a40f11000b500c1e1806041c0460b1481e00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 16155950 1250 16154700 16154737
    0x21306080a140c04090b0a0308030a0b041b020d080a0b03030304060501060810080706030b060f0c06010603061509090c020f0318030d0c0302060403030b0109090603050f01110a02060f0405070b 84
    0x70700c8044412852512440c080d40303006001c0d090742120141c40640313818400000307201c964500040c1e2031a90550005103920700010800025819580100640390001c3c1d80038003c032100450804804055080050010381c0b0a03410488158820b286064000600071000281510194040390a503402110151055a165801049115401441c5a0b07000d10100004114035040c8110707141c561078a4030840c8101500d07040003035120b94070310040714588651100b010b80d5664200d02c0294071014244900d00101e841c10f000040d018401d2048410500342581d42c0c031124600701480700b0004d00c0381c90752a000310b114880c0080d030807200c100010720040c80300400a400e081000d00816103000800c4000004000c17010245a000a4000461641081d031504000c40c0103045140100c0301d4210580c042c0700c03c5c80c1413503000001d0100204014001c00100b100906c0900b43c0c00030000b0b414841d802005006900c103400040008005c0143c1c40e8100e4420825142c43c9656139190074010307000981c0300d641070410003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 16157200 1250 16155950 16155961
    0x503070c0603051009050406060b0304150b01020303070c0f05030f1c18171b0d050418090f0b041103160e0603010e06060d02010219050109020120070b090402130608 72
    0x120054000340010b250a004a181c52941c41ca040381c001d114129449403548003290401046800c0305000e4481d04285c1c0307480f458581007040b024004002030a000520303140f0b40001039407000c0220385c030880b5603840303180b001e0243c2d5581500001080c0010350761400180000075030760502c800184080f54102010519640002454030100c82c0d1352084070a03e030f00310034901000115403500e151203040c031410340f40d0b8803264641a4004c0391542c02c8180790090240000703000e40981c0020142c403e490490200006456501e410344040b1801c1c1407028040340d02d0318034035a001414812034241d0292060808190f030780c03009800f280c03400803011421001e1b601201800d202c003003d03550540754415402c50003408100003c0a58039283c1d103024140501a02455800009590080010302920b1841c450b4091a1256900b040c1c1d00800e414501240002c407032019031181900314120714030003000040050040d26103000c4807822190301c80c01d00990403980a0003d10b100684403511203005240c1a15207076100d181c035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 16158450 1250 16157200 16157213
    0xd0f0e0d02010e0a030522030303020a021b03072c0f0402090f040b070806010c0206070c0509130b1504061e05010f020703200d0b090109050c06030606090d020604050d050307 76
    0x4000480085a240c07141c0c441640f540012040011a00340c05c00030b940e0207a00315440104441800003061001c4881400410190300d41d0061240005903401d450b40820390507440b100faa0001c1d002954143d01c195800c2c40b5022281c9003480f00c0c10f00e8049481da56180150403600704200c1100d0804418452030200015424034403d25644802c09010038207582c542961074411205000d07000c4c0e0108980300d000681181d0003400706220980e00101074984550940c43e0050400e0301a01845015500c803201107404010320740c13504c0c8100c40e440500d00d102580c448260309581c10b00b5503251f95000c1c0e110480001c02c114042086084541c196410140290a00002500c80d0342c540c46150219401844100040b540c103a0340321b01c6180c090f0b00a105c8540d03403400012240041284060143d100c0741082c45821101580000d1055109001b0340303400c485400d0408c403050004803012a00301d41d0400198269180101d03c20300e040384010012402c05840300040380c0380c100c084008859940c80066500300f0301c40e6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 16159700 1250 16158450 16158463
    0x40e01030c030201120b09040b040203030405120609010b060a080711010605180603160b0a080405250f060503070f030c03090501020f0d0501080109080f070302011b0503190c0905060703050d0f0e 85
    0x100c2e00006e0082100040100d080c04000820281c400b50461012500310b50342881120004d00e0700401610622510800064589034261070240480d8a894a0802c160401c00f05a1340071300165125480716a84954003a14148910403482c174065588520206060751941d18a05500300070440d10803d6240c40303824145040c2810400c451615000c000401912004404541048140707140811aa40300c5160171894401e00d48480d161384a20400c036405445c040300c80440c100c030084c010014800d0340c1c80c201558503100c261159030004e01c00c0d040c1005880d009400c000d5080f0a64540041c107181d0340d8849030308a0308440c1c5959000303540001c507100041018041d840c05820610000c0180c00300c40e036120406ea00c500403500c0d06407400803a815090500030340c01009a001c880a500f142c1c0804060300500c05c0c1d000322900520b1102c100d5a8a110380e056124607500c050440c0c550b190101d04100c1000715a0b00440030807000c20108006200074180c0a015100d003128007803030b000c03070104c4280410508240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 16160950 1250 16159700 16159727
    0x3040819020f19060b091302010f0305040c060804050a02090103050607020706020c06120723030610020609060c13030c150207150504030f1505040b0402090a0902060f03070302040e01030c030201 85
    0x14450840d03105030035800300f142400610341640e460030000301440e1000190195054250744070200707004101500f080c4001011105101341da404460301318012040e0111541a90060800e0002e00418041d150290700115000b41c000c5040f6641491240d0001381480000d8000712120341005090202c3c8940401103900070384100d001030200c4d28042408180d650082e0003d8100c1c203a42c64001c500e105014920031410b24050140c082542420088980740d6070340306680d83c902a00004800c0d80740303d0300c0422028058650b0501402c031945900c680c2044a4008488021900645c07285c008000b4400c0843c0e00c00a01a00c100c042c240c1008800107810b000140c0e02c0018466480c4480b03103409944401168192075000503500341d00c504a0510301c070f18840754030b10109401c0c949000c1c00140500c0d81c9205118034030842c1c1e0031800b80d403640d10760000d8400c100c8000f500241e0a01060750072902c5040510f0b48000079150041c101030791030b007140314400070a030310580f10401407403418001c1d564024000e04608 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 16162200 1250 16160950 16160953
    0x90905062d091605030a1a0a151205130b040813080708070602070305060c25060504110a050102030901030b030f0d050c0706050301050105030105040e070305160e0a0506060307120608030304081902 86
    0x50401400107081340c44000c101c000010340d901c903036500c0402500c8a05400c0400680b40c02010ba880b0341d0b4501401c4220b0240070085007040880c40582d404a0003010f2080c4949a8520344803403069a6142c00104050800c6542900030702c01d81944042da5901100181503400060202d04d00e40b100540c2082c020750019421900405405e101050300041c0d160b41080303201c0780c038603071740d000d01d01c41010608050f0700d841e003604020f1b41c059403c0c44101d4211030f0040f80114140b001c0ea11004c01001508503c606c02d107405038000340100783c042d6000341d20066080310040e05517012007590201f801e00380b030400044d240100d0303000f141402044004020340d60140999040c564071719414000040c0c9640014842c4a01c0b4a0701c031810000e841d1410300c0720381c00860340f07c0111201900120303500100c10099008040d00e00f2140c8000404081080c010540580e40c0544018515210038a0441c0c028000c000400c159075100c80d800101300c2402c20046220754041c002c6a6100d5055402003614003a12500030000c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 16163450 1250 16162200 16162231
    0x803030606070f030e100509040c0306050a0b0a140c0105040302100504020a050d0501090b01060818010204030c0302060705070b07061d0c010f050a020f100b090603030a090905062d09 80
    0x90301c60408841401e81c00003241205801c0b5890200c8042c08507015098100c44100300900d002500200a40002e06085506200a40c00700e02e00f04d00b00c65042c41465849000d10000304428000c40300240b070140c04920349280200203c01158006903c000d02030503103699994104400d15038180501e0b581e00c01d59503400d01190030300ba000101a1012801001c0c45810558007503800c201c4c0941c441c00740c160740811441c0c1550381d25400903141c000300321115001c2062250307129403540720610840d82aa64031061030004181960240882ca410215041342c5074071400e035010802648c1a030240c1001d83c450000810080d501640fa01c0590304941c2245280317038028245800c5076a085045440d14003080d00d4a00d1726040040380c100d2408121440d0f0814038010140c200b406c601c1d95400c1002ca041007503e01d40810f460725401c2c5039882c4142c940860014854506c28040068070713800554100740c006000100d41503071440d01c21000c2012111a05901c2180a0a03003d02d061084a180c0d00a000803000040d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 16164700 1250 16163450 16163461
    0x112050604020603070c050f010b01020d09030b0a021803070b0d0b12030a030908090414040501050108120f0706020f0414040b01030b1003021e0a080108010b04090c0611010914070e01080303 83
    0x36a4034000d40000e105090100015404a00c10500040c690341c202c0108d4003030801240300c090003041102030150041c06222542068103000319128812281d01c403800c0740710b6581e4001d040c0029000b49040c006203041d81c0b03460b05043c6e41c04000d0b20010300314200e40150749940d1001070101306c5203090001c0d0300a005012102d200b5070004070540e400d00c6ca0a08020502c2001894150550701c240282c241e030103468071418401248011403150701c2980300304000c100c1643c0302c00055035100280f0350344bc541210200003202d0108214005810360a100342c20160030300c421056011019003254128458520311034a00c20808c3c41c0c01d0054616100c02800c08000c080c01c17400129100c0c6407414400c0041c99000106000510485c4403260038007c410018a5103d24003094014150702c0207228110700c075802d001e40102940741500c03401d0080755100d1307814140c0c0e5152101c2503803000094400109255603950045000c2200d070380d9451990740c03038030014141d118145640001c0d85403040c1c001d460568414003c008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 16165950 1250 16164700 16164703
    0x40b010903030807090302060c01020a1107030f03052d07020f01030c0509060903280201080901110417150c0a090f0b04090905030d0f090204060b03090d08060d05010e070e011205 78
    0xc16a40c2500c2e000e5066a10a442681d0200007a40000d412050020740d580c540350040d80508042111685c9000d02003880d01d031119660321440c00040d0040714080c0b124000a40514010b00380d40c400c2c001c200d1307021244e041829070384410300c40343c503442078800280c014114503081c124218001c80900b0100500740902e28014014018400c5542c0203450004811299a4042181d19080f07540809480c00e19803841d00e42d0308840e0070b0300d0780c00c81c04109403902244c0002c00c18041c01528a03160307003901e4141442c00c840c2c1c1d0310003450030b403005043e03010700c013940c003024260700ca0071920032f07224000c40558174180040000c0803090194000e03100801c0d0180140107901e0320400703d4044035105039012840392603d04200d821841900c0702204401d14000c01e03200140c065030030851080e030003207808000803a528114480e080c401219035000c0c942000d1a8101c1c0380303000b840440d0b04174802600114100c24140c8d80c81e8215030025000003c198449075003003168070040081c850240c180c0300c0c1200300e820700c60b9842a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 16167200 1250 16165950 16165967
    0x60e0315010915050301021c05010506040e04030503070c0b07091a161203110706140705030402010e120705100306080d0c02100c03120204030807110603090a020103090809040903081005040b01 84
    0x90680e151500039440d88030b900c6600942c044d00c4018000c5568a01405400008191544d8401a0a401d00d0f00000d11482c0c9007050364100c81e25144806c00d81d40e255070713080b20705910081200060106581c0e000003c522401d03d41c41c800d01036501c45a1030f090520107010344610f040c030001007000784104100d00401c0d01010401001545c0001c05400010b060007060780540a01d5444448514010410106008084c0c224803030100300415506481d0311090750858280c4411503019022811200440d085070900e0348002000b50820800c2d51074194981d400180b600045807207010000b40c170303a881486810002e211511503a8040c0c00c1c8007800c14265400300f0000a0000b0500c010301a007006c007181132502032540010301003c2d46d0340c215512600ca14150300181c01400341500c020445a0203800e0b1410014200e038024580d0130020080712142d64011809031410703020480390780109104075038054a990003040c1c0c20034401c1d21541400d161941030058640d80c2c99200920640c00c0c0603856080343d8012191 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 16168450 1250 16167200 16167209
    0xa05060a03080702040207050d08070908060106080403080a060b0f1b010c350a1b0306060519020109080703020a0b0702031903020c0c0307091a0604030503030c0a0c0516060e031501 79
    0x40b15142e40680c00018000d0140940241c03d41c015040094480356114001a01c501180e0b02d50070b02c490388807014a0366403c000d0040d603001c1052840450b01080c000c54002e0b03801805a40c000c00e1150b01d800341c8203001c0c0c000080484a149010810101c051040b0005101440130b1200800c103581c80b520009026610a00f640da04031200e20500e040710b02a4840112a10a0b00000024a1341000c1d0100360040c143c1c030000c09061500d103c504102c15200c0e025400482d411641c0c1d06040c0580c0b190004000202030008209540d1f90b032426400003981070002d012001e020b41c02502c1c06203c5c900700a02c0444008050380c045420030050031142c1255600804c0c0211b4035490016203c400702080c00b482d051042c90301c268144954140010f20b5562034101a081003224141d200c254074410b01071002d140603502009010350030500008001124002c041c0c080f01c4d949140104402c0410346480341000b0803a00b081d054a96429018420a5000202c0c2203210380158014002c508a074161040340b64018000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 16169700 1250 16168450 16168463
    0x60603070b0306030a06060305150c0a140a020102040f0306050604060503060c0703031802030a0f140309030a0809030705060d09021c150518010f0203160e06030a05041a0a020309060a05060a03 84
    0x8103a90351410000300481750303482501002510380303d041131030b80d4400d1603c40140b0b0b100944c2c0011111800f00080e00d068075419143c05021101c0301d4003e4407150000220003007159801d00000801c1c03041c0720305480085004010020b1903042c110144400d407926074009502136400002800366241c01d20080340c0c000e40e0107103030010348d200e641c80048d01000811940650305106140031030f818480c0704d11107101600e2148298818034041c586041e5220f0280d60199507164000c0207404000c5002a0010321914400409031162143c032000001ca854010384044885141d0740c1410204608001c2e01d14007010781020741c80d03c194913466541e0140b8116003900b080000d034503500403410545000c800031129581c210001c0c842c50380c4042c2d00030000d4004480c41407142000c18003545500d8000c410b400d44c140d2020306081d14660302c140c0a8805000050030499103980c030800421403401c0d152030700901070501f207100541d0301d0410140c01454242e01815010340c00b450310b024032585aa03100347c01411280e00c002c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 16170950 1250 16169700 16169707
    0x91103010303050307030e0703060203160906020607050d05040822060801050102030301030b01120311060a022208030a0f0c050703030804030206060f130f140411010206070206040c09020702060c100c030608060603070b 95
    0x15007d81c180b440b04e500041c107150000c001d000c0c0d02c92201c03a1b0032402b0009070782c4a0902e181d44600c200e03502c0744151900408179100300241762411010b504240c0d40103000d0302d880780c501150006640010b4145c03004032014031001207014441198052821401004244001e5007103504640700c03c1640c030418440c00c0441804805081c00700340c0a0b149040003403180c0d10644046103003800c1c030840030394010020f000384416010503151143c2c169040c0c62003911981401141001600360040d0352101078180024180440c1e44004000106c0801001010350721903071b2012200c0c00c1c1440c0103441c100c006042c56100d07641d40521411a0307141d51001c00220801f10b000820f840d8403103d0340400030940c1ca06024081d8150b1010001441040d00711113203c8842a402c40741e041d911000100d0302d800041d030b0024010b09c1c580e4820001c98800b600604940e5000612080c58948160002807070440411151414240c4810b0000301060f09446410020420180902501e14180000030f84602207801900058480803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 16172200 1250 16170950 16170971
    0x82d100c0219060b190b030408160503030a1506030507021c030b0d0b060102060606030f060405040309090905061506120c07060b0607080405040b01090501020a020906040e031309110301030305030703 87
    0xb00310100400c41c2c140b820604010050030180041c00c885040036018003e88110443c1d4407080450b004100d0303029880260441c0c0380e956440d4056844010600c030158203542e440c5001c2001400214007c50a00b10001031804401407440c16903c813980c0500c0c00d1501e4501007241d076903000f04a5038005803511f00c0d1540344c3c1c614a4010350081107074034981c41c1c00c915201c1d01c000401c40715103010f0b80500b4090302124a250f80d40c60402c4224032044407100d404145034000325241d0b080c180c00544e0001d2203410080e10350313a140c4c02070204030398041d101600d41e54000f0080c404180708601c248120000182d8486161850050320704400b10fa0240540b02d001400042c000240b017440c0e44403070112030004141580e078046500303181031241c01c6400340c144114606010141c0a40c010703800c400450360184c010b41001030300e580800c0107030500213140310f4029031100c01c0000c0d002030500040c00f007000e20405001e8000c0c2050150381c203e03071001c513088907000d50400051000c650031800f0703682c0c049164a4007280000c3c40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 16173450 1250 16172200 16172203
    0xf030c050d060b130b091302090612090a0b0903210c0c01090c0305010c0813060c020c030d091a0403170c01020906030c0306010806040605090610050c07082d100c02 72
    0x101030410311a07a281480100d11440d050008150440d01c0403080114951544010546841500d006907132205090500c54200c1d0400d80103005900700c014042c0b41840150302c1107141440c801c440c085016000500bc103810880e074460381541041c0b20368021401c007000340c100880c0840e410162000380c00321040005a18203c84411501e04505a2009120036040c40c07810050215850004a03290f5003011442002c1038800c4003064410b00c035500f02d900c90400a5100c0000400031051030340c0c214000c48000c0401900c0811104501505654807561518a803035540500280421520040c7c0d030010441000400c1040d07040c003041c6920401e4240c0c2e42c2d085055901d00910034814219040200407040103503256812014600c100000c2c0c17104c403c5030350750304104021111240226580008824007050550070801d00750344035a000e500389030740b4115460362031914003d00369001040e40c0e401060701d414070102500c203d60407010044d005154060003414084d4075240e00c25101040140d9544101e82420710 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 16174700 1250 16173450 16173457
    0x6070c0803040e0106080702030c0703020d030512010b0d060b0c1b030a0f0309180e100c0314040c080f1603030e0d140607030606020a080904050901020408061509060a060f030c05 78
    0x140c8001c40c1c1e65103942e0022402a80001d101e080041001000010025400401165113004418000d000c41c18103541c200884e0030062641a401c21505011b01c8138901074881c0901e0180408014240c2c40b80c2c8019180d400740c03600c54100140d1078005220040a40d000000d14030603004c03003c020000850f0121000c240b03004495900942001d0300d03800300c0303001d0540104021056074885c030000440c0418060311841030b20380d500102a1075501100d80302c1d942e031002d5840410b82003040d2130081921400e10b0f8410b040d600302903a0a0311000c441075030401c4280004c10800003404084e00c080d00d10144016490194415035202c00343c1070103401c03d00030360301d69211980d240b030955020790311181055400ca245942e40744111445c0e00481c1c034201c80403542c01c2c0000303400415581d0002e006482d19440c1001d02015003005489010340791340034800400d00e11070921445115846141360701c05542025010441036100c00b0380181c0c01041940c009100343c40c1d01020300e1020600a04010401914050007261540b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 16175950 1250 16174700 16174709
    0x917090d15020304020a1208070b0603030f04030c08010b010804020d03110309040e010c080714090d15050c1e03010f0b03040c1a0702010210110a0f05070b010605070501050f04020f06070c 82
    0x4075100e00040c03942980c040e5018500950700500016164400481822100d16015050003414402c001c006468546034a9028070080d06690400981e02d05000c0240c01c03070b0f0012201300717143e5070302807002c0c050034460b50400c0a400d07e0b1030000da05064010170030014142c0c001034100b200340d04403401541e03410002c0324a41c884c060403c11080c008091960b0081018000c100300150202022032035081c45081d905c60a0b0032411096171a0445041c100200314580a004680309071401d102d040e604a12071248522a03141a8500d40e0b0725144c0303071605008000c90301800b030005201800141b000c1429140b90341c0580e0712992850b035a80d112820a80110402907021208180144080c0303e07900e0404805010340920071307000c6400e0f0b425800031101c2a47da11000f00d03080b08a092000c04101d61154541e26013000c040c0c14140c0c500f211b90f440b512142c0100341c0240000c20000070b62401044000d1144c1340c2e202d0b060450004050034030f81e000071041a8840c210390f20925000c20b80e03105101c0e61062a10041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 16177200 1250 16175950 16175963
    0xa180605061605060a110d090212030301080115120309030209040204020d0e0717030301030b060108040c080f060103030f0503101a0909090a0302150f04030302030c09120c03100917090d 81
    0x1040d00403410500242402c0085a00740110800f1580c40190742c001c4642d61600c2e00c800d14101913008040c1c000034802080141d0384104900003e008010707081c4001c501902442d40045040006564808410049584101c03030003a078070356600f03010075404982a02500d80c1211012865255400060b010f8000d4841142c049860040405540302e40000c009044980004955100240d0a5405903ca001c01d21000d000c5541010009205603c514205648544a8442140041e4a0383c80480ca480704012403074200354040c00052081c5500f084a085800c1580c1c6052031852821b008900d6003c030051040c0d0320034000c4e25440400d0040346009940071040d000e00803034202e00c1c000c07040c242d9a01580c4015409030280e443d44448400c50812410720420508441d10b02c0341c1c44940d400c40003540010804a68260300b17205034411030381d0b180200b6090100c45401482d100c07100030300301401c00d81c207030000e030014500c0c00c804040051700042d00c0d80c036030850049210740c54504180100e42c030065401c1005060703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 16178450 1250 16177200 16177207
    0x4030b0c032d0702010501050411030a0b12060405160902030c090d0507080f031b03070b13111005030601021e1f060302151305101403040c03120c0302011a0a18060506 73
    0x300b500c424000784524296030003800b040e42c0c1c500600045411b000c001c0040c4030070410028280111540080081c074038090003800d04641d075884c0050070000c090b00e00726039070f4000c1c050281d03422516002c1074002d000040002c6113141019503e5001d603105800f0f0480c040e80c0040243c400340300040c0300075002003181c2c0c070590380c0d5440e21011050702c0340d0010340d1591000c424481c280342244000000d844a1551140d40500d460f11a0301c030000c003140015204480030307103002143d05030940300c02c50250b04001c8551203a684a042600029040c041d1103040d180c0d400041c4984140024000104010780a0000210f07242d56540c00c5100390240403d504040d400c500c02c2d020100f065450380d00280746458040ba0045641c0743c0b11003c01c00c0360090340c49480c0015048040311181100310b0320085403c144184201c10740e0340d5a80e40ca001640300c12811200114181c40501c07414150280074105803202102020b8106002003800100c00c0301781801007600304140c14404282c0a107280d030202015010041c801c0742c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 16179700 1250 16178450 16178521
    0x105071b030602030118050c0a090e10030510090320060106050901030204080303010b0309070e0603060402043c0609060b0a050705151303030b0402030402010e060901030b041a0f010504030b0c03 85
    0xd101b1040e48440381503441c0100140040c001c2d0301c00e40d66030420395507829090360302d84000d034000808084c00990070703419003540002c0068420840c00010340f810110202d080710a07410060f01c026855108802015800b0308600ca0207a004518141507900f01d0510503118074551303004800a001c0c079084611140300000002c140409030402452050140904407204503454100746220b00400fa14800e4040d07103d10080740041c5001c0d000300e0780c070b004403456201081c00184903048680031540d9400340c3c41029046040c0381d03104075001d1880603001160040c844a0f2422044028910400074030070100b00022030300d002088414051041000007da002c0c4010b82404e500e242e5200070b9004045005c2458591003501d06d050900a4900ca550141c44100b4600e016006003c02740d40001c000d01c0c10140d0303504502240740d84070310440e14015144546590480108407e000b560310b101d0560f641030080c103001c2000000d41c03420b011980460340b5035509480b5150b074240e0850000101d0004c1d0042d400000c800742 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 16180950 1250 16179700 16179719
    0x170106030e16030c0f0503030c0c041a03010c09090501050a03170a02070e01030b0f070801050906040f0b0a090203010509100302060a0c030c02060406030f1b0203040501080606120f01090b01020c0105071b0306020301 94
    0x1400d45c0d112884924049980b801019030300d03c1200c6410000fa040a02c0c031541c10700d0325900c84024081660006a42c1d900d441d400a421030706000140d0002c42e14980082c000009144156409450291504402c807070550301c1c0d451401c804420381035202c1c0000200c00c1d5000f48240711010082950000c68005546c4900c7c118000b06011101e00803540c00080000e030034507104d03503072040c126040078014482646559041c00042e00300800210415900c075100c030701c1c440c7c4406054000800541d1030041e101c0d4100820810421005082520425072aa03800e101517a9180e00b2222300300c40750b0400540702555403605441c0d2a03000403000c1e501c01004940001c00030f0b01500715184502c0032100030055860b2903401388006c158003200040c010303842403000b401194050250700e5000000280014140f000700460002d41241c01c4034148034039400c50004000520380e902a00c48444006d0024154001c10000020914020940090070244403030380c062640c1442000808091034020100355543d6031113035800c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 16182200 1250 16180950 16180973
    0x70e0702010f0209090610020f1204090e010e060f0a06030b011d09010504080901140904050a0207050d021209040c050705060a0b03070b04030f0809060c070909020f01170106030e1603 80
    0x240d400c0000e00e085818403482204c40b40307100201100080c0e103e94041c41003203a04490008194400d001030003820810800000010f45c4185100d69031321401c0890420940d180b04007140d8190381041e14110704a400410758551100002410001c5941c0302c3c0320f070a01400d461791000d0301000e0218000300310a03400e0343d9060791607020b0141461454a0300000c036400c940d0100e41c090882c0e001400410400c2d84950f40a0405e0301040410604200b50b0000050840e8010b079240054282e0004130082040001d1020071b80000250001d8410b45444904010750380c413840c03188074800c0350b0b80c0b0741c0301c02d45a0003803095404440d000300807070b07000e85043c141c403100400d040d04e10a40310748544a000280765001108882c1070740d6122481d03a001240a0b40d07111501d400413001b80360f0250044c0895004030800304040d400400c0c0c3d489000c6800c4010b80144541821440c041d241003049444074a006507094100003411210286000240c10384804400e81c10180207a1425201c0c80305a040042445418100c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 16183450 1250 16182200 16182211
    0x50d050c130b1606050108030301050411040b070219031506031b03030210020306011103070804030c05040605031b010207180506030105090105060102060f0402010c0206190e030c06040306050612070e 87
    0x104025103903010050864007554100c40342451a0500500c01d0340000700c050a4060030b40c005000c0304480c1e03662828140c1c2c109811412080d0300102c01000549014041c04d1038031312044662a18082c10180b015015101c2e801c0041e01075142d41d21b046e01c2070340e810000d1170001c0d50012800380030b07024082c0901018200354801900e54801d0701500d0a1948040d2014604403540758000381841d03820060580041d400c014401030601000c1181c41540742c806100a1040c03600c1a10116034070380c103501c0c00c80d031159256000301c1e0150340b07408814410754038001021045800c900180010000c01440100c0c60011580c1000306c03040d401c40a194a420000e4211600891b4100d0090145548001446003280e50442d290750059001c4008949a030790003080c1103070000d006151620200c4410303004200564010205000c21034690910b04d42483c1d80000b64070309500dc00c0b0040e09072130108000190301c502640c04080c01c81c55540000c18420340c4c07403542c540f40c07140e103590584c1c0c0c1e01640c1e215040000c4408880 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 16184700 1250 16183450 16183477
    0x5070201030b03010e10090c050901060210060e130318050402040b0711040504080f030c0909040c151107060f02011e0207150513081b0f0105090c0d08090f0a0f0605 72
    0x8442d010320301801403c04e0503e078078009100340b1010030f6008001d403d950320140c80d84d8014610224050702c03074a000b0740c0603101540040060300400e01c41003044400e0f07035200101603c00f035014441700307029069000c2100c82e050300d8000240035605407000032502c3c450b402541d02c14400180003401102c0750029250032409000c3d01d00d40d0a05850600c02a034a0071240101043c0c002c00c8044668203400028641110302c2410003400c0c881d000c4042283c81509803400c0d00c03000d15102d000c02682040300b1020f001000a46481241d40c00894082c1d039a49805001304002c1c0400b103401024858800d5000503844020071a4a84003410341403101002580b01c1c0c07005642c001d96680300441140b044c1d00405001e2000f072014014110035503101c00b45560003450045604807d0440100070500301000044104d410b02000060300d81000c07903c4500d0f28000c01c540c2d5001e88140507290b004200040259803012205690380d02c58942e00d84001120311070365412455401c000d4060101e1090b03800405000007030702454 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 16185950 1250 16184700 16184711
    0x10e180a0c020c0a1e03050102071b0803071203020309010908070b0f070f020c01210911090a0b090105040b01020703080406020607020c040b10030f06080a0303140703050907150c060c0507020103 85
    0x310201d032202841030f010341d00310814050801040d800c2a0100c44c280c030091845043d095140d55896007681c3c40342c001138400000308014507800c400400e0b0a04001c0080340021071070041c00f55038100e81d002500303018206141d40400080c941e00c6c401e41003041440c1d48200e04030b41d25549454070040000050b102c810841c0300b00e41c001030b08540a40c012540d8a00250010070503c0c02107030045804d14102c034450301403600900031a51224400f40180c80740284140c0c0e004d5000ca168506008189400600e864245424001c88000301d40315480900d054540a6a0206808509100503450000f055000400c40355000400058203076012a0a0340203082541c00e172110a0000001c0005903084d040c80294040300d070548a002490003035200d080000d5241c080410302e1580c660711107040c94a2a030702540465222500e11003040080314103154401c0442c1030030802810318048003540ca060038002d1074956502454101052800348100c01c441c4c583c4030109010742c9080d140300805941040b03204901090801c0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 16187057 1107 16185950 16185971
    0x705100302071205030c09060309030717030103061506080a0b040905010e030a0207050910030807060212010906030b0f1618050d0b18010b010f0e010e180a 68
    0x140c030010307155080d0741005106203a28164910801100308100285403003d101503404035242681e82c140c0ba80d0392a0b410529601c03c0250140c00100380b215100700081c940350041d41a01d1041034244441448500311400e141c03281d00402d0007203143c240010303c40c1200350f17001e0030700c410000380040340b0f0404d80e440c0c0e030382103d0070b20b8403541803604000b0f190082c00d0b4040011900501c81620084030502c1d00d042e641822589501000704045d400107489810700c80d90380c0640e450600c4065105506503501c00301d140c018001d6120888024a002d4005074210401d8080310384911000341840c0c240007404442210300380700b2130f03880032004400c8031004500c507250246d40300c1026208000c600c3c1d042c1050109000151000b00f4861440ea05000400e07010340d80c09102410290250305011039118a40c0b00141c5102d40c810450070340020443c204428401c42d08503002c0d01400140e0810041540c01 = true := by decide +kernel

theorem cover : BRFrame.Cov 16007200 16187057 := by
  have h0 := BRFrame.cov_init 16007200
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 16007200 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 16007200 ≤ n) (h2 : n < 16187057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
